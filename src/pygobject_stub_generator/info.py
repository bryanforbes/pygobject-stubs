from __future__ import annotations

from typing import Any
from typing import cast
from typing import ClassVar
from typing import Final
from typing import Generic
from typing import get_args
from typing import get_origin
from typing import Literal
from typing import NamedTuple
from typing import Protocol
from typing import TYPE_CHECKING
from typing import TypeAlias
from typing_extensions import get_original_bases
from typing_extensions import Self

import inspect
import itertools
import re
from dataclasses import dataclass
from dataclasses import field
from dataclasses import replace
from enum import IntEnum
from enum import IntFlag
from types import GenericAlias

from gi import _gi as GI
from gi.repository import GObject

from pygobject_stub_generator.utils import fix_python_identifier
from pygobject_stub_generator.utils import get_finish_func
from pygobject_stub_generator.utils import is_ref_type
from pygobject_stub_generator.utils import MISSING
from pygobject_stub_generator.utils import MissingType

if TYPE_CHECKING:
    from collections.abc import Callable as Callable
    from collections.abc import Iterable
    from collections.abc import Iterator
    from types import BuiltinFunctionType
    from types import FunctionType
    from types import MethodDescriptorType
    from types import MethodType
    from types import ModuleType

    from gi.repository import _GIRepository3 as GIRepository

else:
    from gi.repository import GIRepository

_identifier_re: Final = re.compile(r"^[A-Za-z_]\w*$")


def _find_attributes(obj: type[Any]) -> list[str]:
    # Get all attributes resolved in this class, excluding inherited ones.
    # This includes overridden attributes that could have a different signature
    # in parent classes.
    obj_attrs = set(obj.__dict__.keys())

    # Add inherited GI attributes if we are a direct override of a GI class.
    if "__info__" not in obj.__dict__:
        for base in obj.__bases__:
            if "__info__" in base.__dict__:
                obj_attrs.update(base.__dict__.keys())

    return sorted(obj_attrs)


AttributeType: TypeAlias = Literal["class", "function", "constant"]


class _ClassAttribute(NamedTuple):
    type: Literal["class"]
    name: str
    obj: type[object]


class _FunctionAttribute(NamedTuple):
    type: Literal["function"]
    name: str
    obj: (
        FunctionType
        | BuiltinFunctionType
        | MethodDescriptorType
        | MethodType
        | Callable[..., object]
    )


class _ConstantAttribute(NamedTuple):
    type: Literal["constant"]
    name: str
    obj: object


def _iterate_attributes(
    obj: ModuleType | type[object], names: Iterable[str], /
) -> Iterator[_ClassAttribute | _FunctionAttribute | _ConstantAttribute]:
    for name in names:
        # Check if this is a valid name in python
        if not _identifier_re.match(name):
            continue

        try:
            attr_value = getattr(obj, name)
        except AttributeError:
            continue

        if inspect.isclass(attr_value):
            yield _ClassAttribute("class", name, attr_value)
        elif (
            inspect.isfunction(attr_value)
            or inspect.isbuiltin(attr_value)
            or inspect.ismethoddescriptor(attr_value)
            or inspect.ismethod(attr_value)
            or callable(attr_value)
        ):
            yield _FunctionAttribute("function", name, attr_value)
        elif (
            not name.startswith("_")
            # GDK has some busted constant names like
            # Gdk.EventType.2BUTTON_PRESS
            and not name[0].isdigit()
        ):
            yield _ConstantAttribute("constant", name, attr_value)


@dataclass(slots=True, frozen=True)
class DiscoveryContext:
    namespace: str
    repo: GIRepository.Repository


FROM_PYTHON: Final = frozenset({GI.Direction.IN, GI.Direction.INOUT})
TO_PYTHON: Final = frozenset({GI.Direction.OUT, GI.Direction.INOUT})


class _FullNameMixin(Protocol):
    name: ClassVar[str] | str

    @property
    def full_name(self) -> str:
        return f"{cast('Any', self).parent.full_name}.{self.name}"


@dataclass(slots=True)
class Argument:
    name: str
    parent: PyFunction

    info: GI.ArgInfo
    c_index: int
    from_python: bool
    to_python: bool
    required: bool
    nullable: bool


@dataclass(slots=True, frozen=True)
class Arguments:
    args: tuple[GI.ArgInfo, ...]
    can_have_defaults: bool
    hidden: frozenset[int]
    closure_targets: frozenset[int]
    last_visible_index: int
    async_callback_index: int | None
    async_cancellable_index: int | None
    async_user_data_index: int | None

    @classmethod
    def for_callable(
        cls, info: GI.CallableInfo, /, *, allow_varargs: bool = True
    ) -> Self:
        gi_args = info.get_arguments()

        hidden_indexes: set[int] = set()
        closure_indexes: set[int] = set()
        from_python_indexes: set[int] = set()
        async_callback_index: int | None = None
        async_cancellable_index: int | None = None
        async_user_data_index: int | None = None

        if (
            return_array_length_index := info.get_return_type().get_array_length_index()
        ) > -1:
            hidden_indexes.add(return_array_length_index)

        is_vfunc = isinstance(info, GI.VFuncInfo)
        is_callback = isinstance(info, GI.CallbackInfo)

        if is_callback:
            # Callback arguments that are used for closure have a closure index
            # that matches their argument index, so we can just check for that
            # instead of checking the type and direction
            for arg_index, arg in enumerate(gi_args):
                if arg.get_closure_index() == arg_index:
                    closure_indexes.add(arg_index)

                from_python_indexes.add(arg_index)

            # Apply PyGObject's user_data heuristic when no explicit closure
            # annotation is present. This mirrors the auto-detection in
            # pygi_closure_cache_new (pygi-cache.c lines 1092-1111), which
            # picks the first IN-direction void-pointer arg and treats it
            # as the user_data slot for the callback.
            if not closure_indexes:
                for arg_index, arg in enumerate(gi_args):
                    if arg.get_direction() != GI.Direction.IN:
                        continue
                    type_info = arg.get_type_info()
                    if (
                        type_info.get_tag() == GI.TypeTag.VOID
                        and type_info.is_pointer()
                    ):
                        closure_indexes.add(arg_index)
                        break
        else:
            for arg_index, arg in enumerate(gi_args):
                type_info = arg.get_type_info()
                tag = type_info.get_tag()
                is_from_python = arg.get_direction() in FROM_PYTHON

                # Hide array length args
                if (
                    tag == GI.TypeTag.ARRAY
                    and (array_length_index := type_info.get_array_length_index()) > -1
                ):
                    hidden_indexes.add(array_length_index)

                if tag == GI.TypeTag.INTERFACE:
                    iface_info = type_info.get_interface()

                    if isinstance(iface_info, GI.CallbackInfo):
                        # Hide destroy and closure args for callbacks if this
                        # isn't a vfunc
                        if (
                            not is_vfunc
                            and arg_index not in hidden_indexes
                            and arg_index not in closure_indexes
                        ):
                            if (
                                closure_index := arg.get_closure_index()
                            ) > -1 and is_from_python:
                                closure_indexes.add(closure_index)

                            if (destroy_index := arg.get_destroy_index()) > -1:
                                hidden_indexes.add(destroy_index)

                        if arg.get_scope() == GI.ScopeType.ASYNC:
                            async_callback_index = arg_index

                            if (
                                closure_index := arg.get_closure_index()
                            ) > -1 and is_from_python:
                                async_user_data_index = closure_index

                    if (
                        isinstance(iface_info, GI.ObjectInfo)
                        and f"{iface_info.get_namespace()}.{iface_info.get_name()}"
                        == "Gio.Cancellable"
                    ):
                        async_cancellable_index = arg_index

                if is_from_python:
                    from_python_indexes.add(arg_index)

        # Find the last closure argument whether it comes before or after the callback.
        last_visible_from_python = max(from_python_indexes - hidden_indexes, default=-1)

        # Treat a user_data slot as the *varargs argument iff it is the
        # trailing FROM_PYTHON arg in C-arg order (i.e. no other visible
        # FROM_PYTHON arg has a higher C-arg index). This mirrors
        # PyGObject's runtime varargs detection in the reverse loop of
        # _callable_cache_generate_args_cache_real, which picks the last
        # FROM_PYTHON arg and only treats it as varargs when it is a
        # CHILD_WITH_PYARG (i.e. a user_data slot).
        varargs_index = (
            last_visible_from_python
            if allow_varargs and last_visible_from_python in closure_indexes
            else None
        )

        return cls(
            args=gi_args,
            can_have_defaults=isinstance(info, GI.FunctionInfo),
            hidden=frozenset(hidden_indexes),
            closure_targets=frozenset(closure_indexes),
            last_visible_index=last_visible_from_python,
            async_callback_index=async_callback_index,
            async_cancellable_index=async_cancellable_index,
            async_user_data_index=async_user_data_index,
        )


@dataclass(slots=True, frozen=True)
class Param:
    name: str
    info: GI.TypeInfo | Callback
    kind: Literal["positional", "kw_only", "var_keyword", "callback"]
    has_default: bool
    default_is_none: bool
    closure_target: bool


@dataclass(slots=True, frozen=True)
class Return:
    info: GI.TypeInfo | Callback
    nullable: bool


@dataclass(slots=True, frozen=True)
class Callback:
    name: str | None
    params: tuple[Param, ...]
    returns: tuple[Return, ...]

    @classmethod
    def for_callback(cls, callback: GI.CallbackInfo, /) -> Self:
        gi_args = callback.get_arguments()
        return_type = callback.get_return_type()

        hidden_indexes: set[int] = set()
        closure_indexes: set[int] = set()
        returns: list[Return] = []
        params: list[Param] = []

        if not callback.skip_return() and (
            return_type.get_tag() != GI.TypeTag.VOID or return_type.is_pointer()
        ):
            returns.append(Return(return_type, callback.may_return_null()))

        if (return_array_length_index := return_type.get_array_length_index()) > -1:
            hidden_indexes.add(return_array_length_index)

        # Callback arguments that are used for closure have a closure index
        # that matches their argument index, so we can just check for that
        # instead of checking the type and direction
        for arg_index, arg in enumerate(gi_args):
            if arg.get_closure_index() == arg_index:
                closure_indexes.add(arg_index)

        # Apply PyGObject's user_data heuristic when no explicit closure
        # annotation is present. This mirrors the auto-detection in
        # pygi_closure_cache_new (pygi-cache.c lines 1092-1111), which
        # picks the first IN-direction void-pointer arg and treats it
        # as the user_data slot for the callback.
        if not closure_indexes:
            for arg_index, arg in enumerate(gi_args):
                if arg.get_direction() != GI.Direction.IN:
                    continue
                type_info = arg.get_type_info()
                if type_info.get_tag() == GI.TypeTag.VOID and type_info.is_pointer():
                    closure_indexes.add(arg_index)
                    break

        for arg_index, arg in enumerate(gi_args):
            if arg_index in hidden_indexes:
                continue

            nullable = arg.may_be_null()
            direction = arg.get_direction()

            if direction in FROM_PYTHON:
                params.append(
                    Param(
                        name=f"{arg.get_name()}",
                        info=arg.get_type_info(),
                        kind="callback",
                        has_default=nullable or arg.is_optional(),
                        default_is_none=nullable,
                        closure_target=arg_index in closure_indexes,
                    )
                )

            if arg.get_direction() in TO_PYTHON:
                returns.append(Return(arg.get_type_info(), arg.may_be_null()))

        return cls(
            name=callback.get_name(), params=tuple(params), returns=tuple(returns)
        )


@dataclass(slots=True, frozen=True)
class GIFunction(_FullNameMixin):
    name: str
    info: GI.FunctionInfo | GI.VFuncInfo
    parent: Module | Class | Enum
    receiver: Literal["self", "cls"] | None
    params: tuple[Param, ...]
    returns: tuple[Return, ...]
    wrapped: object | None | MissingType = MISSING

    @property
    def finish_function(self) -> GI.FunctionInfo | None:
        if isinstance(self.info, GI.FunctionInfo):
            return get_finish_func(self.info)

        return None

    @classmethod
    def for_function(
        cls,
        name: str,
        func: GI.FunctionInfo | GI.VFuncInfo,
        container: Module | Class | Enum,
        /,
    ) -> Self:
        gi_args = func.get_arguments()
        return_type = func.get_return_type()

        hidden_indexes: set[int] = set()
        closure_indexes: set[int] = set()
        from_python_indexes: set[int] = set()

        returns: list[Return] = []
        params: list[Param] = []
        receiver: Literal["self", "cls"] | None = None

        if not func.skip_return() and (
            return_type.get_tag() != GI.TypeTag.VOID or return_type.is_pointer()
        ):
            returns.append(Return(return_type, func.may_return_null()))

        if (return_array_length_index := return_type.get_array_length_index()) > -1:
            hidden_indexes.add(return_array_length_index)

        for arg_index, arg in enumerate(gi_args):
            type_info = arg.get_type_info()
            tag = type_info.get_tag()
            is_from_python = arg.get_direction() in FROM_PYTHON

            # Hide array length args
            if (
                tag == GI.TypeTag.ARRAY
                and (array_length_index := type_info.get_array_length_index()) > -1
            ):
                hidden_indexes.add(array_length_index)

            if tag == GI.TypeTag.INTERFACE:
                iface_info = type_info.get_interface()

                if isinstance(iface_info, GI.CallbackInfo):
                    # Hide destroy and closure args for callbacks if this
                    # isn't a vfunc
                    if (
                        not isinstance(func, GI.VFuncInfo)
                        and arg_index not in hidden_indexes
                        and arg_index not in closure_indexes
                    ):
                        if (
                            closure_index := arg.get_closure_index()
                        ) > -1 and is_from_python:
                            closure_indexes.add(closure_index)

                        if (destroy_index := arg.get_destroy_index()) > -1:
                            hidden_indexes.add(destroy_index)

                    if arg.get_scope() == GI.ScopeType.ASYNC:
                        async_callback_index = arg_index

                        if (
                            closure_index := arg.get_closure_index()
                        ) > -1 and is_from_python:
                            async_user_data_index = closure_index

                if (
                    isinstance(iface_info, GI.ObjectInfo)
                    and f"{iface_info.get_namespace()}.{iface_info.get_name()}"
                    == "Gio.Cancellable"
                ):
                    async_cancellable_index = arg_index

            if is_from_python:
                from_python_indexes.add(arg_index)

        for arg_index, arg in enumerate(gi_args):
            if arg_index in hidden_indexes:
                continue

            nullable = arg.may_be_null()
            direction = arg.get_direction()

            if direction in FROM_PYTHON:
                info = arg.get_type_info()
                interface_info = (
                    info.get_interface()
                    if info.get_tag() == GI.TypeTag.INTERFACE
                    else None
                )
                callback_info = (
                    interface_info
                    if isinstance(interface_info, GI.CallbackInfo)
                    else None
                )
                params.append(
                    Param(
                        name=f"{arg.get_name()}",
                        info=arg.get_type_info()
                        if callback_info is None
                        else Callback.for_callback(callback_info),
                        kind="positional",
                        has_default=nullable or arg.is_optional(),
                        default_is_none=nullable,
                        closure_target=arg_index in closure_indexes,
                    )
                )

            if arg.get_direction() in TO_PYTHON:
                returns.append(Return(arg.get_type_info(), arg.may_be_null()))

        return cls(
            name,
            func,
            container,
            receiver,
            tuple(params),
            tuple(returns),
        )


@dataclass(slots=True)
class PyFunction(_FullNameMixin):
    name: str
    func: Callable[..., object]
    parent: Module | Class | Enum
    arguments: Arguments | None

    @property
    def is_method(self) -> bool:
        return not isinstance(self.parent, Module)

    @classmethod
    def for_function(
        cls, name: str, func: Callable[..., object], container: Module | Class | Enum, /
    ) -> Self:
        return cls(
            name,
            func,
            container,
            Arguments.for_callable(func) if isinstance(func, GI.CallableInfo) else None,
        )


_strip_boolean_result_re: Final = re.compile(r"\bstrip_boolean_result\b")


def _for_function(
    name: str, func: Callable[..., object], container: Module | Class | Enum, /
) -> PyFunction | GIFunction:
    if hasattr(func, "__wrapped__") and _strip_boolean_result_re.search(str(func)):
        real_function = cast("GI.FunctionInfo", cast("Any", func).__wrapped__)
        fail_ret = inspect.getclosurevars(func).nonlocals.get("fail_ret")
        node = GIFunction.for_function(name, real_function, container)
        returns = node.returns[1:]  # Strip first return value

        return replace(node, returns=returns, wrapped=fail_ret)

    if isinstance(func, (GI.FunctionInfo, GI.VFuncInfo)):
        return GIFunction.for_function(name, func, container)

    return PyFunction.for_function(func.__name__, func, container)


@dataclass(slots=True)
class Constant(_FullNameMixin):
    name: str
    value: object
    annotation: object | None
    parent: Module | Class | Enum


@dataclass(slots=True)
class Module:
    name: str
    module: ModuleType

    annotations: dict[str, object]
    constants: dict[str, Constant]
    functions: dict[str, PyFunction | GIFunction]
    classes: dict[str, Class]
    flags: dict[str, Enum]
    enums: dict[str, Enum]
    # callbacks: dict[str, Callback]

    @property
    def full_name(self) -> str:
        return self.name

    @classmethod
    def from_module(cls, module: ModuleType, context: DiscoveryContext) -> Self:
        classes: dict[str, Class] = {}
        functions: dict[str, PyFunction | GIFunction] = {}
        flags: dict[str, Enum] = {}
        enums: dict[str, Enum] = {}
        constants: dict[str, Constant] = {}
        annotations = getattr(module, "__annotations__", {})

        instance = cls(
            context.namespace,
            module,
            annotations,
            constants,
            functions,
            classes,
            flags,
            enums,
        )

        for attribute in _iterate_attributes(module, dir(module)):
            if attribute.type == "class":
                if issubclass(attribute.obj, IntFlag):
                    flags[attribute.name] = Enum.for_enum(
                        attribute.name,
                        attribute.obj,
                        instance,
                    )
                elif issubclass(attribute.obj, IntEnum):
                    enums[attribute.name] = Enum.for_enum(
                        attribute.name,
                        attribute.obj,
                        instance,
                    )
                else:
                    classes[attribute.name] = Class.for_class(
                        attribute.name, attribute.obj, instance, context
                    )
            elif attribute.type == "function":
                functions[attribute.name] = _for_function(
                    attribute.name, attribute.obj, instance
                )
            else:
                constants[attribute.name] = Constant(
                    attribute.name,
                    attribute.obj,
                    annotations.get(attribute.name),
                    instance,
                )

        return instance


@dataclass(slots=True)
class Class(_FullNameMixin):
    name: str
    cls: type[object]
    info: GI.RegisteredTypeInfo | None
    bases: list[type[object]]
    parent: Class | Module
    annotations: dict[str, object]

    constants: dict[str, Constant]
    fields: dict[str, Field]
    methods: dict[str, PyFunction | GIFunction]
    nested_classes: dict[str, Class]

    properties: dict[str, Property]
    init: PyFunction | GObjectInit | None = field(init=False, default=None)

    ALLOWED_METHODS: ClassVar = {
        "__new__",
        "__init__",
        "__enter__",
        "__exit__",
        "__iter__",
        "__next__",
        "__getitem__",
        "__setitem__",
        "__delitem__",
        "__len__",
        "__int__",
        "__float__",
        "__bool__",
        "__contains__",
    }

    @property
    def is_ginterface(self) -> bool:
        return isinstance(self.info, GI.InterfaceInfo)

    @property
    def is_gobject(self) -> bool:
        return isinstance(self.info, GI.ObjectInfo)

    @classmethod
    def _find_repo_property(
        cls, prop_info: GI.PropertyInfo, context: DiscoveryContext, /
    ) -> GIRepository.PropertyInfo | None:
        class_info = context.repo.find_by_name(
            prop_info.get_namespace(), f"{prop_info.get_container().get_name()}"
        )
        prop_name = prop_info.get_name()

        if isinstance(
            class_info, (GIRepository.ObjectInfo, GIRepository.InterfaceInfo)
        ):
            for i in range(class_info.get_n_properties()):
                property = class_info.get_property(i)
                if property.get_name() == prop_name:
                    return property

        return None

    @classmethod
    def _iterate_properties(
        cls,
        info: GI.ObjectInfo | GI.InterfaceInfo,
        context: DiscoveryContext,
        /,
        *,
        include_interfaces: bool = False,
    ) -> Iterator[Property]:
        interface_properties: Iterable[tuple[GI.PropertyInfo, ...]] = (
            (iface.get_properties() for iface in info.get_interfaces())
            if isinstance(info, GI.ObjectInfo) and include_interfaces
            else []
        )

        yield from (
            Property.for_property(gi_prop, gir_prop)
            for gi_prop in itertools.chain(info.get_properties(), *interface_properties)
            if (gir_prop := cls._find_repo_property(gi_prop, context)) is not None
        )

    @classmethod
    def for_class(
        cls,
        cls_name: str,
        cls_: type[object],
        container: Class | Module,
        context: DiscoveryContext,
        /,
    ) -> Self:
        full_module_name = f"{cls_.__module__}.{cls_.__qualname__}"
        info: GI.RegisteredTypeInfo | None = cls_.__dict__.get("__info__")
        original_bases = list(get_original_bases(cls_))
        bases = original_bases

        # Because we're generating types for gi.repository, we have to generate stubs
        # for override classes that come from gi.repository and inherit from
        # gi.repository classes. Effectively, we want to write the stubs as if the
        # override class and repository class are one class in the MRO. What this means
        # is that the following transformations need to happen:
        # 1. For the following:
        #    gi.repository.X.One(<One repository bases>)
        #    gi.overrides.X.One(
        #        <One prefix override bases>,
        #        gi.repository.X.One,
        #        <One suffix override bases>
        #    ) -> gi.repository.X.One(
        #        <One prefix override bases>,
        #        <One repository bases>,
        #        <One override bases>
        #    )
        # 2. gi.overrides.X.Two(float) -> gi.repository.X.Two(float)
        # 3. gi.overrides.X.Three(gi.overrides.X.Four, ...) -> gi.repository.X.Three(
        #        gi.repository.X.Four, ...
        #    )
        if cls_.__module__.startswith("gi.overrides.") and any(
            base.__module__.startswith("gi.repository.") for base in bases
        ):
            bases = []
            gi_repo_full_name = full_module_name.replace(
                "gi.overrides.", "gi.repository.", 1
            )

            for base in original_bases:
                if f"{base.__module__}.{base.__qualname__}" == gi_repo_full_name:
                    bases.extend(get_original_bases(base))

                    if info is None:
                        info = base.__dict__.get("__info__")
                elif base is not object and base not in bases:
                    bases.append(base)

        if GI.GInterface in bases and not any(
            get_origin(base) is Protocol for base in bases
        ):
            # Most overrides use Generic instead of Protocol for interfaces
            index = next(
                (
                    i
                    for i, base in enumerate(bases)
                    if get_origin(base) is Generic and get_args(base)
                ),
                None,
            )
            if index is None:
                bases.append(Protocol)
            else:
                args = get_args(bases[index])
                bases[index] = GenericAlias(cast("Any", Protocol), args)

        properties: dict[str, Property] = {}
        init_properties: dict[str, Property] = {}

        if isinstance(info, (GI.ObjectInfo, GI.InterfaceInfo)):
            names: set[str] = set()

            for prop in cls._iterate_properties(info, context, include_interfaces=True):
                if (name := prop.python_name) in names:
                    continue

                names.add(name)

                if prop.readable or (prop.writable and not prop.construct_only):
                    properties[name] = prop

                if prop.writable or prop.construct or prop.construct_only:
                    init_properties[prop.python_name] = prop

            if isinstance(info, GI.ObjectInfo):
                parent = info.get_parent()
                while parent is not None:
                    for prop in cls._iterate_properties(parent, context):
                        if (name := prop.python_name) in names:
                            continue

                        names.add(name)

                        if prop.writable or prop.construct or prop.construct_only:
                            init_properties[prop.python_name] = prop

        init: Callable[..., object] | dict[str, Property] | None = None

        if issubclass(cls_, (GI.Boxed, GI.Struct, GObject.Object)):
            if issubclass(cls_, (GI.Boxed, GI.Struct)):
                # Structs and Boxed use __new__ as constructor with a dummy __init__,
                # but overrides can introduce either __new__ or __init__. The priority
                # below is:
                # 1. __new__ is the same as the "new" method from __info__
                # 2. __new__ exists on this class
                # 3. __init__ exists on this class

                if isinstance(cls_.__new__, GI.BaseInfo) and isinstance(
                    info, (GI.StructInfo, GI.UnionInfo)
                ):
                    for method_info in info.get_methods():
                        if method_info.equal(cls_.__new__):
                            init = cast("Callable[..., object]", cls_.__new__)

                if init is None:
                    if "__new__" in cls_.__dict__:
                        init = cast("Callable[..., object]", cls_.__new__)

                    elif "__init__" in cls_.__dict__:
                        init = cls_.__init__

            elif isinstance(info, GI.ObjectInfo):
                if not init_properties:
                    # Pango.Layout and Pango.FontDescription override __new__
                    if "__new__" in cls_.__dict__:
                        init = cls_.__new__
                else:
                    init = init_properties

        annotations = {
            k: v
            for k, v in getattr(cls_, "__annotations__", {}).items()
            if not k.startswith("_")
        }
        constants: dict[str, Constant] = {}
        fields: dict[str, Field] = {}
        methods: dict[str, PyFunction | GIFunction] = {}
        classes: dict[str, Class] = {}

        instance = cls(
            cls_name,
            cls_,
            info,
            bases,
            container,
            annotations,
            constants,
            fields,
            methods,
            classes,
            properties,
        )

        if isinstance(info, (GI.StructInfo, GI.ObjectInfo)):
            for field in info.get_fields():
                name = f"{field.get_name()}"
                fields[name] = Field(name, field, instance)

        for attribute in _iterate_attributes(cls_, _find_attributes(cls_)):
            if (
                attribute.name.startswith("__")
                and attribute.name not in cls.ALLOWED_METHODS
            ):
                continue

            if attribute.type == "class":
                classes[attribute.name] = Class.for_class(
                    attribute.name, attribute.obj, instance, context
                )
            elif attribute.type == "function":
                methods[attribute.name] = _for_function(
                    attribute.name,
                    attribute.obj.__func__
                    if inspect.ismethod(attribute.obj)
                    else attribute.obj,
                    instance,
                )
            elif attribute.name not in fields:
                constants[attribute.name] = Constant(
                    attribute.name,
                    attribute.obj,
                    annotations.get(attribute.name),
                    instance,
                )

        if init:
            methods.pop("__init__", None)
            methods.pop("__new__", None)

            instance.init = (
                PyFunction.for_function("__init__", init, instance)
                if callable(init)
                else GObjectInit(init_properties, instance)
            )

        return instance


@dataclass(slots=True)
class GObjectInit(_FullNameMixin):
    name: str = field(init=False, default="__init__")
    init_properties: dict[str, Property]
    parent: Class


@dataclass(slots=True)
class Field(_FullNameMixin):
    name: str
    info: GI.FieldInfo
    parent: Class


@dataclass(slots=True)
class Property:
    info: GI.PropertyInfo
    gobject_name: str
    python_name: str
    readable: bool
    writable: bool
    construct: bool
    construct_only: bool
    type_info: GI.TypeInfo
    read_nullable: bool
    write_nullable: bool

    @classmethod
    def for_property(
        cls,
        info: GI.PropertyInfo,
        gir_info: GIRepository.PropertyInfo,
        /,
    ) -> Self:
        gobject_name = f"{info.get_name()}"
        flags = info.get_flags()
        type_info = info.get_type_info()
        getter = gir_info.get_getter()
        setter = gir_info.get_setter()

        getter_nullable = bool(getter and getter.may_return_null())
        setter_nullable = bool(setter and setter.get_arg(0).may_be_null())

        is_ref = is_ref_type(type_info)

        if getter is not None:
            read_nullable = getter_nullable
        elif setter is not None:
            read_nullable = setter_nullable or is_ref
        else:
            read_nullable = is_ref

        if setter is not None:
            write_nullable = setter_nullable
        elif getter is not None:
            write_nullable = getter_nullable or is_ref
        else:
            write_nullable = is_ref

        return cls(
            info,
            gobject_name,
            fix_python_identifier(gobject_name),
            bool(flags & GObject.ParamFlags.READABLE),
            bool(flags & GObject.ParamFlags.WRITABLE),
            bool(flags & GObject.ParamFlags.CONSTRUCT),
            bool(flags & GObject.ParamFlags.CONSTRUCT_ONLY),
            type_info,
            read_nullable,
            write_nullable,
        )


@dataclass(slots=True)
class Enum(_FullNameMixin):
    name: str
    cls: type[IntEnum | IntFlag]
    info: GI.EnumInfo | None
    parent: Class | Module
    is_flags: bool
    is_gobject: bool
    members: dict[str, EnumMember]
    methods: dict[str, PyFunction]

    @classmethod
    def for_enum(
        cls,
        cls_name: str,
        cls_: type[IntFlag] | type[IntEnum],
        container: Class | Module,
        /,
    ) -> Self:
        members: dict[str, EnumMember] = {}
        methods: dict[str, PyFunction] = {}

        instance = cls(
            cls_name,
            cls_,
            None,
            container,
            issubclass(cls_, IntFlag),
            issubclass(cls_, GObject.GEnum) or issubclass(cls_, GObject.GFlags),
            members,
            methods,
        )

        for key in sorted(vars(cls_)):
            if key.startswith(("__", "_")) or key[0].isdigit():
                continue

            enum_attr = getattr(cls_, key)

            if isinstance(enum_attr, GI.FunctionInfo):
                methods[key] = PyFunction.for_function(key, enum_attr, instance)
            else:
                members[key] = EnumMember(key, enum_attr, instance)

        return instance


@dataclass(slots=True)
class EnumMember(_FullNameMixin):
    name: str
    value: object
    parent: Enum

    @property
    def names(self) -> tuple[str, ...]:
        if isinstance(self.value, GObject.GEnum):
            return (self.value.value_name, self.value.value_nick)

        if isinstance(self.value, GObject.GFlags):
            return (*self.value.value_names, *self.value.value_nicks)

        return ()
