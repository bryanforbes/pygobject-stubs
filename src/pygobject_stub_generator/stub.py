from __future__ import annotations

from typing import Any
from typing import cast
from typing import Final
from typing import get_args
from typing import get_origin
from typing import Literal
from typing import overload
from typing import Protocol
from typing import TYPE_CHECKING
from typing import TypeAlias
from typing import TypeVar
from typing_extensions import get_overloads
from typing_extensions import ParamSpec

import inspect
import re
import textwrap
from dataclasses import dataclass
from dataclasses import field
from dataclasses import InitVar
from dataclasses import replace
from enum import IntEnum
from enum import IntFlag
from functools import wraps
from types import ModuleType

import gi
import gi._gi as GI

from pygobject_stub_generator.info import Callback
from pygobject_stub_generator.info import Class
from pygobject_stub_generator.info import Constant
from pygobject_stub_generator.info import DiscoveryContext
from pygobject_stub_generator.info import Enum
from pygobject_stub_generator.info import Field
from pygobject_stub_generator.info import GIFunction
from pygobject_stub_generator.info import GObjectInit
from pygobject_stub_generator.info import Module
from pygobject_stub_generator.info import Param
from pygobject_stub_generator.info import PyFunction
from pygobject_stub_generator.info import Return

from .arguments import Arguments
from .arguments import VisibleArgument
from .class_info import ClassInfo
from .import_info import FromImportInfo
from .import_info import ImportInfo
from .type_var_info import TypeVarInfo
from .type_var_info import TypeVarTupleInfo
from .utils import fix_python_identifier
from .utils import generate_full_name
from .utils import get_finish_func
from .utils import get_return_type
from .utils import get_value
from .utils import make_nullable
from .utils import MISSING
from .utils import MissingType

gi.require_version("GIRepository", "3.0")

from gi.repository import GObject  # noqa: E402

if TYPE_CHECKING:
    from collections.abc import Callable

    from gi.repository import _GIRepository3 as GIRepository

    from .parse import Imports
    from .parse import Overrides
    from .parse import TypeVars
else:
    from gi.repository import GIRepository

_Object: TypeAlias = ModuleType | type[Any]
_FunctionMode: TypeAlias = Literal[
    "sync", "awaitable", "async_callback", "async_callback_kwargs"
]
_P = ParamSpec("_P")
_R = TypeVar("_R")

_identifier_re: Final = re.compile(r"^[A-Za-z_]\w*$")
_typing_re: Final = re.compile(r"(?:typing\.)(?P<name>\w+)\b")
_free_typing_re: Final = re.compile(r"\b(?P<name>Any|Self)\b")
_gi_repository_re: Final = re.compile(
    r"\bgi\.(?:repository|overrides)\.(?P<namespace>\w+)\.(?P<name>(?:\w+)(?:\.\w+)*)\b"
)
_import_re: Final = re.compile(
    r"\b(?P<module>(?:[A-Za-z_]\w+\.)*[A-Za-z_]\w+)\.(?P<name>[A-Za-z_]\w+)\b"
)
_type_vars_re: Final = re.compile(r"(?<!\w)[~+-](?P<name>[A-Za-z_]\w*)\b")
_strip_boolean_result_re: Final = re.compile(r"\bstrip_boolean_result\b")

_ALLOWED_FUNCTIONS: Final = {
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

_GI_IMPORT_ALIASES: Final = {
    "gi.Boxed": ("GObject", "GBoxed"),
    "gobject.GInterface": ("GObject", "GInterface"),
}

_EXCLUDED_VARARGS_CALLBACKS: Final = {
    ("GLib", "DestroyNotify"),
}

_MODULE_NORMALIZATION: Final[dict[tuple[str, str | None], str]] = {
    ("typing", "Self"): "typing_extensions",  # 3.11+
    ("typing", "TypeVar"): "typing_extensions",  # default= 3.13+, infer_variance= 3.12+
    ("typing", "Unpack"): "typing_extensions",  # 3.11+
    ("typing", "TypeVarTuple"): "typing_extensions",  # 3.11+
    ("typing", "Never"): "typing_extensions",  # 3.11+
}


def _normalize_module_name(module: str, name: str | None, /) -> str:
    return _MODULE_NORMALIZATION.get((module, name), module)


def _replace_optional(formatted: str) -> str:
    for prefix in ("typing.Optional[", "Optional["):
        while (idx := formatted.find(prefix)) != -1:
            depth = 0
            for i in range(idx + len(prefix) - 1, len(formatted)):
                if formatted[i] == "[":
                    depth += 1
                elif formatted[i] == "]":
                    depth -= 1
                    if depth == 0:
                        inner = formatted[idx + len(prefix) : i]
                        formatted = (
                            formatted[:idx] + inner + " | None" + formatted[i + 1 :]
                        )
                        break
    return formatted


def _replace_union(formatted: str) -> str:
    for prefix in ("typing.Union[", "Union["):
        while (start := formatted.find(prefix)) != -1:
            bracket_depth = 0
            for end in range(start + len(prefix) - 1, len(formatted)):
                if formatted[end] == "[":
                    bracket_depth += 1
                elif formatted[end] == "]":
                    bracket_depth -= 1
                    if bracket_depth == 0:
                        inner = formatted[start + len(prefix) : end]
                        # Split by top-level commas only
                        parts: list[str] = []
                        part_start = 0
                        nesting_depth = 0
                        for pos, char in enumerate(inner):
                            if char == "[":
                                nesting_depth += 1
                            elif char == "]":
                                nesting_depth -= 1
                            elif char == "," and nesting_depth == 0:
                                parts.append(inner[part_start:pos].strip())
                                part_start = pos + 1
                        parts.append(inner[part_start:].strip())
                        formatted = (
                            formatted[:start] + " | ".join(parts) + formatted[end + 1 :]
                        )
                        break
    return formatted


class _Named(Protocol):
    @property
    def full_name(self) -> str: ...


_F = TypeVar("_F", bound="Callable[..., str]")


def _check_override(
    func: _F,
) -> _F:
    @wraps(func)
    def wrapper(self: Stub, node: _Named, /, *args: object, **kwargs: object) -> str:
        if (override := self.check_override(node)) is not None:
            return override

        return func(self, node, *args, **kwargs)

    return cast("_F", wrapper)


@dataclass(slots=True)
class Stub:
    repo: GIRepository.Repository
    parent: _Object
    namespace: str
    overrides: Overrides
    imports: InitVar[Imports]
    typevars: InitVar[TypeVars]
    needed_imports: dict[tuple[str, str | None], FromImportInfo | ImportInfo] = field(
        init=False
    )
    needed_typevars: list[TypeVarInfo | TypeVarTupleInfo] = field(
        init=False, default_factory=list
    )
    known_namespaces: set[str] = field(init=False, default_factory=set)
    known_namespaces_prefixes: tuple[str, ...] = field(
        init=False, default_factory=tuple
    )

    def __post_init__(self, imports: Imports, typevars: TypeVars) -> None:
        self.needed_imports = {}

        for _import in imports:
            name = (
                (
                    _import.import_as or _import.name
                    if _import.module == "gi.repository"
                    else _import.name
                )
                if isinstance(_import, FromImportInfo)
                else None
            )
            module = _normalize_module_name(_import.module, name)

            self.needed_imports[(module, name)] = replace(_import, module=module)

        self.known_namespaces = {
            dependency.rsplit("-", 1)[0]
            for dependency in self.repo.get_dependencies(self.namespace)
        } | {self.namespace}
        self.known_namespaces_prefixes = tuple(
            f"{namespace}." for namespace in self.known_namespaces
        )

        self.needed_typevars = list(typevars)

        if self.namespace == "Gtk":
            self.get_import("os")

    @overload
    def check_override(self, prefix: _Named) -> str | None: ...
    @overload
    def check_override(self, prefix: str, name: str) -> str | None: ...
    def check_override(
        self, prefix: str | _Named, name: str | None = None
    ) -> str | None:
        full_name = (
            (
                prefix.full_name
                if not prefix.full_name.startswith(f"{self.namespace}.")
                else prefix.full_name[len(f"{self.namespace}.") :]
            )
            if not isinstance(prefix, str)
            else generate_full_name(prefix, cast("str", name))
        )

        if full_name in self.overrides:
            return "# override\n" + self.__fix_annotations(self.overrides[full_name])
        return None

    def __get_import(
        self, module: str, /, name: str | None = None
    ) -> FromImportInfo | ImportInfo | None:
        module = _normalize_module_name(module, name)
        return self.needed_imports.get((module, name))

    def __add_import(
        self,
        module: str,
        /,
        name: str | None = None,
        import_as: str | None = None,
    ) -> ImportInfo | FromImportInfo:
        module = _normalize_module_name(module, name)

        import_object = (
            ImportInfo(module, import_as)
            if name is None
            else FromImportInfo(module, name, import_as)
        )

        self.needed_imports[(module, name)] = import_object

        return import_object

    def get_import(self, module: str, name: str | None = None) -> str:
        if (_import := self.__get_import(module, name)) is not None:
            return _import.symbol

        if name is None:
            self.__add_import(module)
            return module

        if module == "builtins":
            return name

        symbols = [_import.symbol for _import in self.needed_imports.values()]
        import_as = name
        while import_as in symbols:
            import_as = f"_{import_as}"

        self.__add_import(module, name, None if import_as == name else import_as)
        return import_as

    @overload
    def get_namespace_member(self, info: GI.BaseInfo, /) -> str: ...
    @overload
    def get_namespace_member(self, namespace: str, name: str, /) -> str: ...

    def get_namespace_member(
        self,
        namespace: str | GI.BaseInfo,
        name: str | None = None,
        /,
    ) -> str:
        if isinstance(namespace, GI.BaseInfo):
            name = f"{namespace.get_name()}"
            namespace = namespace.get_namespace()

        if name is None:
            raise ValueError("Name must be provided when namespace is a string")

        if namespace == self.namespace:
            return name

        if namespace in ("_gi", "_gtktemplate"):
            if (_import := self.__get_import("gi", namespace)) is None:
                _import = self.__add_import("gi", namespace)
        elif namespace == "_gi_gst":
            if (_import := self.__get_import("gi.overrides", "_gi_gst")) is None:
                _import = self.__add_import("gi.overrides", "_gi_gst")
        elif namespace == "cairo":
            if (_import := self.__get_import(namespace)) is None:
                _import = self.__add_import(namespace)
        elif (_import := self.__get_import("gi.repository", namespace)) is None:
            _import = self.__add_import("gi.repository", namespace)

        return f"{_import.symbol}.{name}"

    def get_typevar(
        self,
        name: str,
        /,
        *constraints: str,
        default: str | None = None,
        bound: str | None = None,
        covariant: bool = False,
        contravariant: bool = False,
        # TODO: https://github.com/python/mypy/issues/17811
        # Since mypy doesn't support infer_variance, we'll disable this for now and
        # enable it when/if it's supported (or when 3.11 is dropped)
        # infer_variance: bool = False,
    ) -> str:
        if covariant and not contravariant:
            name = f"{name}_co"

        if contravariant and not covariant:
            name = f"{name}_contra"

        typevar = TypeVarInfo(
            name,
            default,
            constraints if constraints else None,
            bound,
            contravariant=contravariant,
            covariant=covariant,
            # infer_variance=infer_variance,
        )

        if typevar not in self.needed_typevars:
            self.needed_typevars.append(typevar)

        return name

    def get_typevar_tuple(self, name: str, /, *, default: str | None = None) -> str:
        if default is not None:
            default = self.get_unpack(default)

        typevar_tuple = TypeVarTupleInfo(name, default)

        if typevar_tuple not in self.needed_typevars:
            self.needed_typevars.append(typevar_tuple)

        return name

    def get_callback_typevar_tuple(self) -> str:
        return self.get_typevar_tuple("_DataTs", default="tuple[()]")

    def get_final(self, annotation: str | None = None) -> str:
        final_symbol = self.get_import("typing", "Final")

        if annotation is None:
            return final_symbol

        return (
            annotation
            if f"{final_symbol}[" in annotation
            else f"{final_symbol}[{annotation}]"
        )

    def get_literal(self, annotation: str, /) -> str:
        return f"{self.get_import('typing', 'Literal')}[{annotation}]"

    def get_unpack(self, annotation: str, /) -> str:
        return f"{self.get_import('typing', 'Unpack')}[{annotation}]"

    def get_unpack_data_ts(self) -> str:
        return self.get_unpack(self.get_callback_typevar_tuple())

    def get_type_alias(self, name: str, /) -> str:
        return f"{name}: {self.get_import('typing', 'TypeAlias')}"

    def get_alias(self, name: str, obj: object, /) -> str | None:
        if obj.__module__.startswith(("gi.overrides.", "gi.repository.")):
            namespace = obj.__module__.rsplit(".", 1)[1]
        elif obj.__module__ == "gobject" or obj.__module__ == "gi._gi":
            namespace = "_gi"
        elif obj.__module__ == "gi._gtktemplate":
            return self.get_namespace_member("_gtktemplate", obj.__qualname__)  # type: ignore[attr-defined]
        else:
            return None

        if namespace != self.namespace or name != obj.__qualname__:  # type: ignore[attr-defined]
            return self.get_namespace_member(namespace, obj.__qualname__)  # type: ignore[attr-defined]

        return None

    def get_property(
        self,
        name: str,
        annotations: tuple[str | None, str | None],
        /,
        *,
        indent: str = "",
    ) -> str:
        property_symbol = self.get_import("builtins", "property")
        get_annotation, set_annotation = annotations

        if get_annotation is None and set_annotation is None:
            return ""

        if get_annotation == set_annotation:
            return f"{indent}{name}: {get_annotation}"

        if get_annotation is None:
            get_annotation = self.get_import("typing", "Never")

        lines: list[str] = [
            f"@{property_symbol}",
            f"def {name}(self) -> {get_annotation}: ...",
        ]

        if set_annotation is not None:
            lines.extend(
                [
                    f"@{name}.setter",
                    f"def {name}(self, value: {set_annotation}) -> None: ...",
                ]
            )

        return textwrap.indent("\n".join(lines), indent)

    def get_class_import(self, cls: type[Any], /) -> str:
        # Things like Generic and Protocol show up in the MRO as `Generic` rather than
        # `Generic[T]`, so we need to get the original class to get the type arguments
        # to recreate them in the stubs
        origin_cls = get_origin(cls) or cls

        # TODO: track generics and properly create them in the stub
        arg_names = [arg.__name__ for arg in get_args(cls)]
        args = f"[{', '.join(arg_names)}]" if arg_names else ""

        full_name = f"{origin_cls.__module__}.{origin_cls.__qualname__}"

        ns: str | None = None
        name = ""

        if alias := _GI_IMPORT_ALIASES.get(full_name):
            ns, name = alias
        elif full_name.startswith(("gi.overrides.", "gi.repository.")):
            _, _, ns, name = full_name.split(".", 3)
        elif full_name.startswith(("gi.", "_gi.", "GI.", "_GI.", "gobject.")):
            ns, name = full_name.split(".", 1)
            ns = "_gi"
        elif full_name.startswith("cairo."):
            ns, name = full_name.split(".", 1)

        if ns is not None:
            return f"{self.get_namespace_member(ns, name)}{args}"

        module, name = full_name.rsplit(".", 1)
        return f"{self.get_import(module, name)}{args}"

    def fix_argument_name(self, name: str | None, /) -> str:
        return fix_python_identifier(name)

    def get_callable_arguments(
        self,
        info: GI.CallableInfo,
        /,
        *,
        allow_varargs: bool = True,
        mode: _FunctionMode = "sync",
    ) -> tuple[dict[str, str], list[str]]:
        arguments = Arguments.for_callable(info, allow_varargs=allow_varargs)

        if mode == "awaitable":
            arguments = arguments.as_async()
        elif mode == "async_callback_kwargs":
            arguments = arguments.as_async_callback_kwargs()

        if arguments is None:
            raise ValueError("Callable is not eligible for async transformation")

        py_args: list[VisibleArgument] = []
        return_args: list[str] = []
        required_indexes: set[int] = set()

        for arg in arguments:
            if arg.from_python and not arg.is_varargs_slot:
                py_args.append(arg)

                if arg.required:
                    required_indexes.add(arg.c_index)

                if (
                    mode in {"async_callback", "async_callback_kwargs"}
                    and arg.c_index == arguments.async_callback_index
                ):
                    py_args[-1] = replace(py_args[-1], required=True)

                    # the kwargs variant doesn't require the callback
                    if mode == "async_callback":
                        required_indexes.add(arg.c_index)

            if arg.to_python:
                return_args.append(
                    self.type_info_to_python(
                        arg.info.get_type_info(), out=True, nullable=arg.nullable
                    )
                )

        last_required = max(required_indexes, default=-1)
        args: dict[str, str] = {}

        for py_arg in py_args:
            if (
                py_arg.c_index == arguments.async_callback_index
                and isinstance(
                    iface := py_arg.info.get_type_info().get_interface(),
                    GI.CallbackInfo,
                )
                and f"{iface.get_namespace()}.{iface.get_name()}"
                == "Gio.AsyncReadyCallback"
            ):
                arg_type = self.type_info_to_python(
                    py_arg.info.get_type_info(),
                    nullable=py_arg.nullable,
                    async_callback_argument=py_arg,
                    async_callback_kwargs=(mode == "async_callback_kwargs"),
                )
            else:
                arg_type = self.type_info_to_python(
                    py_arg.info.get_type_info(),
                    nullable=py_arg.nullable,
                    varargs_callback=py_arg.is_varargs_callback,
                    closure_argument=py_arg.is_closure_target,
                )

            is_kw_only_callback = (
                mode == "async_callback_kwargs"
                and py_arg.c_index == arguments.async_callback_index
            )

            if (
                arguments.can_have_defaults
                and py_arg.c_index > last_required
                and not is_kw_only_callback
            ):
                arg_type = f"{arg_type} = {'None' if py_arg.nullable else '...'}"

            if (
                mode == "async_callback_kwargs"
                and py_arg.c_index == arguments.async_callback_index
            ):
                args["*"] = ""

            args[self.fix_argument_name(py_arg.info.get_name())] = arg_type

        if (varargs_info := arguments.varargs_info) is not None:
            args[f"*{self.fix_argument_name(varargs_info.get_name())}"] = (
                self.get_unpack_data_ts()
            )

        return_type = info.get_return_type()
        if not info.skip_return() and (
            return_type.get_tag() != GI.TypeTag.VOID or return_type.is_pointer()
        ):
            return_args = [
                self.type_info_to_python(
                    return_type, out=True, nullable=info.may_return_null()
                ),
                *return_args,
            ]

        return args, return_args

    def type_info_to_python(
        self,
        info: GI.TypeInfo | VisibleArgument,
        /,
        *,
        out: bool = False,
        nullable: bool | MissingType = MISSING,
        varargs_callback: bool | MissingType = MISSING,
        closure_argument: bool | MissingType = MISSING,
        async_callback_argument: VisibleArgument | None = None,
        async_callback_kwargs: bool | MissingType = MISSING,
    ) -> str:
        py_arg: VisibleArgument | None = None
        if isinstance(info, VisibleArgument):
            py_arg = info
            info = py_arg.info.get_type_info()

        nullable = get_value(nullable, False if py_arg is None else py_arg.nullable)
        varargs_callback = get_value(
            varargs_callback, False if py_arg is None else py_arg.is_varargs_callback
        )
        closure_argument = get_value(
            closure_argument, False if py_arg is None else py_arg.is_closure_target
        )
        async_callback_kwargs = get_value(async_callback_kwargs, False)

        tag = info.get_tag()

        py_type: str | None = None

        match tag:
            case GI.TypeTag.BOOLEAN:
                py_type = "bool"
            case (
                GI.TypeTag.INT8
                | GI.TypeTag.INT16
                | GI.TypeTag.INT32
                | GI.TypeTag.INT64
                | GI.TypeTag.UINT8
                | GI.TypeTag.UINT16
                | GI.TypeTag.UINT32
                | GI.TypeTag.UINT64
            ):
                py_type = "int"
            case GI.TypeTag.DOUBLE | GI.TypeTag.FLOAT:
                py_type = "float"
            case GI.TypeTag.UTF8 | GI.TypeTag.FILENAME | GI.TypeTag.UNICHAR:
                py_type = "str"
            case GI.TypeTag.ARRAY | GI.TypeTag.GLIST | GI.TypeTag.GSLIST:
                value_info = info.get_param_type(0)

                if TYPE_CHECKING:
                    assert value_info is not None

                value_type = self.type_info_to_python(value_info, out=out)

                if tag == GI.TypeTag.ARRAY:
                    if out:
                        # As output argument array of type uint8 are returned as bytes
                        if value_info.get_tag() == GI.TypeTag.UINT8:
                            py_type = "bytes"
                        else:
                            py_type = f"list[{value_type}]"
                    else:
                        # As input arguments array can be generated by any sequence
                        py_type = f"{self.get_import('collections.abc', 'Sequence')}[{
                            value_type
                        }]"
                else:
                    py_type = f"list[{value_type}]"

                # All return/out/inout arrays/lists get marshalled as a list, regardless
                # of nullable
                nullable = nullable and not out
            case GI.TypeTag.GHASH:
                key_info = info.get_param_type(0)
                value_info = info.get_param_type(1)

                if TYPE_CHECKING:
                    assert key_info is not None
                    assert value_info is not None

                key_type = self.type_info_to_python(key_info, out=out)
                value_type = self.type_info_to_python(value_info, out=out)
                collection_type = (
                    "dict" if out else self.get_import("collections.abc", "Mapping")
                )

                py_type = f"{collection_type}[{key_type}, {value_type}]"
            case GI.TypeTag.INTERFACE:
                interface_info = info.get_interface()

                if isinstance(interface_info, GI.CallbackInfo):
                    # TODO: enable this when PyGObject exposes CallbackInfos
                    # if (
                    #     callback_name := interface_info.get_name()
                    # ) and not interface_info.get_container():
                    #     # Reference named callbacks directly
                    #     py_type = self.get_namespace_member(
                    #         interface_info.get_namespace(), callback_name
                    #     )
                    #
                    #     if (
                    #         varargs_callback
                    #         and (
                    #             interface_info.get_namespace(),
                    #             interface_info.get_name(),
                    #         )
                    #         not in _EXCLUDED_VARARGS_CALLBACKS
                    #     ):
                    #         py_type = f"{py_type}[{self.get_unpack_data_ts()}]"
                    # else:
                    #     # Generate the `Callable[]` annotation for anonymous callbacks
                    #     (callback_args, callback_return_args) = (
                    #         self.get_callable_arguments(
                    #            interface_info, allow_varargs=varargs_callback
                    #         )
                    #     )
                    #     callback_return_type = get_return_type(callback_return_args)
                    #
                    #     py_type = f"{
                    #         self.get_import('collections.abc', 'Callable')
                    #     }[[{
                    #         ', '.join(callback_args.values())
                    #     }], {callback_return_type}]"

                    if (
                        async_callback_argument is not None
                        and f"{interface_info.get_namespace()}.{
                            interface_info.get_name()
                        }"
                        == "Gio.AsyncReadyCallback"
                    ):
                        callback_symbol = self.get_namespace_member(
                            "Gio", "_AsyncReadyCallback"
                        )
                        class_info = async_callback_argument.callable_container
                        source_type = (
                            "None"
                            if class_info is None
                            or not (
                                async_callback_argument.callable_flags
                                & (
                                    GI.FunctionInfoFlags.IS_METHOD
                                    | GI.FunctionInfoFlags.IS_CONSTRUCTOR
                                )
                            )
                            else self.get_namespace_member(class_info)
                        )

                        if isinstance(
                            async_callback_argument.callable_info, GI.VFuncInfo
                        ):
                            pointer_type = (
                                f"int | {self.get_import('typing', 'Any')} | None"
                            )
                            user_data_args = f", {pointer_type}"
                        elif async_callback_kwargs:
                            callback_symbol = self.get_namespace_member(
                                "Gio", "_AsyncReadyVarArgsCallback"
                            )
                            user_data_args = ""
                        elif async_callback_argument.is_varargs_callback:
                            callback_symbol = self.get_namespace_member(
                                "Gio", "_AsyncReadyVarArgsCallback"
                            )
                            user_data_args = f", {self.get_unpack_data_ts()}"
                        elif (
                            closure_index
                            := async_callback_argument.info.get_closure_index()
                        ) > -1:
                            user_data_arg = (
                                async_callback_argument.callable_info.get_arguments()[
                                    closure_index
                                ]
                            )
                            user_data_type = self.type_info_to_python(
                                user_data_arg.get_type_info(),
                                nullable=user_data_arg.may_be_null(),
                                closure_argument=True,
                            )
                            user_data_args = f", {user_data_type}"
                        else:
                            user_data_args = ""

                        py_type = f"{callback_symbol}[{source_type}{user_data_args}]"
                    else:
                        (callback_args, callback_return_args) = (
                            self.get_callable_arguments(
                                interface_info,
                                allow_varargs=varargs_callback,
                            )
                        )
                        callback_return_type = get_return_type(callback_return_args)

                        py_type = f"{self.get_import('collections.abc', 'Callable')}[[{
                            ', '.join(callback_args.values())
                        }], {callback_return_type}]"
                elif (
                    isinstance(interface_info, GI.EnumInfo)
                    and interface_info.get_g_type() != GObject.TYPE_NONE
                ):
                    interface_namespace = interface_info.get_namespace()
                    interface_name = f"{interface_info.get_name()}"

                    # cairo doesn't use the `_<iface>ValueType` convention
                    if not out and interface_namespace != "cairo":
                        interface_name = f"_{interface_name}ValueType"

                    py_type = self.get_namespace_member(
                        interface_namespace, interface_name
                    )
                elif interface_info is not None:
                    interface_namespace = interface_info.get_namespace()
                    interface_name = interface_info.get_name()

                    if interface_namespace == "GObject" and interface_name == "Value":
                        py_type = self.get_import("typing", "Any")

                    elif (
                        interface_namespace == "GObject" and interface_name == "Closure"
                    ):
                        py_type = f"{
                            self.get_import('collections.abc', 'Callable')
                        }[..., {self.get_import('typing', 'Any')}]"

                    elif (
                        interface_namespace == "cairo"
                        and interface_name == "Context"
                        and not out
                    ):
                        some_surface = self.get_typevar(
                            "_SomeSurface",
                            bound=f"{self.get_namespace_member('cairo', 'Surface')}",
                        )
                        py_type = f"{self.get_namespace_member('cairo', 'Context')}[{
                            some_surface
                        }]"
                    else:
                        py_type = self.get_namespace_member(
                            interface_namespace, f"{interface_name}"
                        )
            case GI.TypeTag.VOID:
                if info.is_pointer():
                    if closure_argument:
                        # Arguments passed to callbacks are specially handled by the
                        # PyGObject marshalling code, so they can be anything
                        py_type = f"{self.get_import('typing', 'Any')} | None"
                    else:
                        # Pointers can be int | CapsuleType | None, but we don't have
                        # CapsuleType until 3.13 This is what typeshed did until 3.13
                        py_type = (
                            "int"
                            if out
                            else f"int | {self.get_import('typing', 'Any')} | None"
                        )

                    # All return/out/inout pointers get marshalled as int, regardless of
                    # nullable
                    nullable = nullable and not out
                else:
                    py_type = "None"
            case GI.TypeTag.GTYPE:
                py_type = f"type[{self.get_import('typing', 'Any')}]"
            case GI.TypeTag.ERROR:
                py_type = self.get_namespace_member("GLib", "Error")

        if py_type is None:
            raise ValueError(f"Unsupported GI type tag: {tag}")

        if nullable:
            py_type = make_nullable(py_type)

        return py_type

    def __replace_typing(self, match: re.Match[str]) -> str:
        match match.group("name"):
            case ("Callable" | "Sequence" | "Iterable" | "Iterator") as name:
                symbol = self.get_import("collections.abc", name)
            case "ContextManager" as name:
                symbol = self.get_import("contextlib", f"Abstract{name}")
            case "Type" | "Tuple" | "List" | "Dict" | "Set" | "FrozenSet" as name:
                symbol = name.lower()
            case _ as name:
                symbol = self.get_import("typing", name)

        return symbol

    def __replace_free_typing(self, match: re.Match[str]) -> str:
        name = match.group("name")
        return self.get_import("typing", name)

    def __replace_import(self, match: re.Match[str]) -> str:
        module = match.group("module")
        name = match.group("name")

        if module.startswith(
            ("gi.repository.", "gi.overrides.", "_gi.", *self.known_namespaces_prefixes)
        ):
            if module.startswith(f"{self.namespace}."):
                return f"{module.split('.', 1)[1]}.{name}"
            return f"{module}.{name}"

        if module in self.known_namespaces:
            if module == self.namespace:
                return name
            return f"{module}.{name}"

        if module in {"gi", "gobject"}:
            if name == "Struct":
                return self.get_namespace_member("_gi", "Struct")
            return f"gi.repository.GObject.{name}"

        return self.get_import(module, name)

    def __replace_gi_repository(self, match: re.Match[str]) -> str:
        namespace = match.group("namespace")
        symbol = self.get_namespace_member(namespace, match.group("name"))
        return f"{symbol}"

    def __fix_annotations(self, formatted: str, /, *, fix_imports: bool = False) -> str:
        formatted = _replace_optional(formatted)
        formatted = _replace_union(formatted)
        formatted = _typing_re.sub(self.__replace_typing, formatted)
        formatted = _free_typing_re.sub(self.__replace_free_typing, formatted)
        formatted = re.sub(
            rf"\b{self.get_import('typing', 'Generator')}\[(.*?), None, None\]",
            rf"{self.get_import('collections.abc', 'Iterator')}[\1]",
            formatted,
        )
        if fix_imports:
            formatted = _import_re.sub(self.__replace_import, formatted)
        formatted = _gi_repository_re.sub(self.__replace_gi_repository, formatted)
        formatted = _type_vars_re.sub(r"\g<name>", formatted)
        return re.sub(rf"\b{self.namespace}\.", r"", formatted)

    def format_annotation(
        self, annotation: object, /, *, fix_imports: bool = False
    ) -> str:
        try:
            # This requires Python 3.14
            formatted = inspect.formatannotation(
                annotation,
                quote_annotation_strings=False,  # pyright: ignore[reportCallIssue]
            )
        except Exception:
            # This should be a good enough fallback for older Pythons
            formatted = (
                inspect.formatannotation(annotation).replace('"', "").replace("'", "")
            )

        return self.__fix_annotations(formatted, fix_imports=fix_imports)

    def format_signature(self, signature: inspect.Signature) -> str:
        try:
            # This requires Python 3.14
            formatted = signature.format(quote_annotation_strings=False)  # pyright: ignore[reportAttributeAccessIssue]
        except Exception:
            # This should be a good enough fallback for older Pythons
            formatted = str(signature).replace('"', "").replace("'", "")

        return self.__fix_annotations(formatted, fix_imports=True)

    # TODO: enable this when PyGObject exposes CallbackInfos
    # def __build_callback_type(self, callback_info: GI.CallbackInfo) -> str:
    #     name = f"{callback_info.get_name()}"
    #
    #     if override := self.check_override("", name):
    #         return override
    #
    #     # NOTE: Use `type X =` when 3.11 is dropped
    #     type_alias = self.get_import("typing", "TypeAlias")
    #     signature = callback_info.__signature__
    #
    #     callback_data_arg_name = next(
    #         (
    #             arg.get_name()
    #             for arg in callback_info.get_arguments()
    #             if arg.get_closure_index() > -1
    #         ),
    #         None,
    #     )
    #
    #     annotation = self.format_annotation(
    #         Callable[
    #             [
    #                 self.get_callback_typevar_tuple()
    #                 if param.name == callback_data_arg_name
    #                 else param.annotation
    #                 for param in signature.parameters.values()
    #             ],
    #             signature.return_annotation,
    #         ],
    #         fix_imports=True,
    #     )
    #
    #     if callback_data_arg_name is not None:
    #         unpack_symbol = self.get_import("typing", "Unpack")
    #         annotation = re.sub(
    #             r"""['"]_DataTs['"]""",
    #             self.get_unpack_data_ts(),
    #             annotation,
    #         )
    #
    #     return f"""{name}: {type_alias} = {annotation}"""
    #
    # def __build_callback_types(self) -> str:
    #     lines: list[str] = []
    #
    #     gi_repo = gi.Repository.get_default()
    #     for callback_info in gi_repo.get_infos(self.namespace):
    #         if not isinstance(callback_info, GI.CallbackInfo):
    #             continue
    #
    #         lines.append(self.__build_callback_type(callback_info))
    #
    #     return "\n".join(lines)

    def __build_function(
        self,
        name: str,
        function: GI.FunctionInfo | GI.VFuncInfo,
        in_class: type[Any] | None,
        *,
        return_signature: str | None = None,
        comment: str | None = None,
        mode: _FunctionMode = "sync",
        finish_func: GI.FunctionInfo | None = None,
    ) -> str:
        lines: list[str] = []

        is_vfunc = isinstance(function, GI.VFuncInfo)

        method: bool = False
        constructor: bool = False
        static: bool = False

        # Flags
        function_flags = function.get_flags()

        if function_flags & GI.FunctionInfoFlags.IS_CONSTRUCTOR:
            constructor = True

        if is_vfunc or (function_flags & GI.FunctionInfoFlags.IS_METHOD):
            method = True

        if in_class and not method and not constructor:
            static = True

        if mode != "sync":
            lines.append(f"@{self.get_import('typing', 'overload')}")

        # Arguments
        if mode == "awaitable":
            assert finish_func is not None
            # awaitable
            _, finish_return_args = self.get_callable_arguments(finish_func)
            args, return_args = self.get_callable_arguments(
                function, allow_varargs=False, mode=mode
            )
            return_type = f"{self.get_namespace_member('_gi', 'Async')}[{
                get_return_type(finish_return_args)
            }]"
        else:
            if mode in {"async_callback", "async_callback_kwargs"}:
                args, return_args = self.get_callable_arguments(function, mode=mode)
            else:
                args, return_args = self.get_callable_arguments(function)

            return_type = (
                return_signature if return_signature else get_return_type(return_args)
            )

        args_types = [
            name if name == "*" else f"{self.fix_argument_name(name)}: {arg}"
            for name, arg in args.items()
        ]

        if is_vfunc and args_types:
            # vfuncs are invoked by PyGObject's C marshaller with a positional tuple;
            # this means it doesn't matter what the names of the arguments are, so stubs
            # need to be positional-only
            args_types.append("/")

        # Generate string
        if constructor:
            if name == "__init__":
                # We pass the "new" constructor with the name __init__ because type
                # checkers do better with __init__ signatures, so we have to change the
                # signature a bit
                args_types.insert(0, "self")
                return_type = "None"
            else:
                lines.append("@classmethod")
                args_types.insert(0, "cls")
                # Override return value, for example Gtk.Button.new returns a Gtk.Widget
                # instead of Gtk.Button
                rt = function.get_container().get_name()
                if rt is not None and return_type != f"{rt} | None":
                    return_type = rt
        elif method:
            args_types.insert(0, "self")
        elif static:
            lines.append("@staticmethod")

        lines.append(
            f"def {name}({', '.join(str(a) for a in args_types)}) -> {return_type}: ..."
        )

        if comment:
            lines[-1] += f" # {comment}"

        return "\n".join(lines) + "\n"

    def __wrapped_strip_boolean_result(
        self,
        name: str,
        function: Callable[..., Any],
        in_class: type[Any] | None,
    ) -> str:
        real_function = cast("GI.FunctionInfo", cast("Any", function).__wrapped__)
        fail_ret = inspect.getclosurevars(function).nonlocals.get("fail_ret")

        _, return_args = self.get_callable_arguments(real_function)
        return_args = return_args[1:]  # Strip first return value

        return_signature = get_return_type(return_args)

        if fail_ret is None:
            return_signature = make_nullable(f"{return_signature}")
        else:
            if type(fail_ret) is tuple:
                if len(fail_ret) > 0:
                    return_signature = f"({return_signature} | tuple{
                        str(fail_ret).replace('(', '[').replace(')', ']')
                    })"
                else:
                    return_signature = f"({return_signature} | tuple[()])"
            else:
                return_signature = f"({return_signature} | {
                    self.get_import('typing', 'Literal')
                }[{fail_ret}])"

        return self.__build_function(
            name,
            real_function,
            in_class,
            return_signature=return_signature,
            comment="CHECK Wrapped function",
        )

    def build_function(
        self,
        name: str,
        function: Callable[..., Any],
        in_class: type[Any] | None,
        *,
        is_overload: bool = False,
    ) -> str:
        if name.startswith("_") and name not in _ALLOWED_FUNCTIONS:
            return ""

        if hasattr(function, "__wrapped__") and _strip_boolean_result_re.search(
            str(function)
        ):
            return self.__wrapped_strip_boolean_result(name, function, in_class)

        if isinstance(function, (GI.FunctionInfo, GI.VFuncInfo)):
            if in_class is None and function.get_namespace() != self.namespace:
                # Set up a constant for functions that are aliases
                return f"{name}: {self.get_final()} = {
                    self.get_namespace_member(function)
                }\n"

            if isinstance(function, GI.FunctionInfo):
                finish_func = get_finish_func(function)

                if finish_func is not None and not (
                    function.get_flags() & GI.FunctionInfoFlags.IS_CONSTRUCTOR
                ):
                    return (
                        self.__build_function(
                            name,
                            function,
                            in_class,
                            mode="awaitable",
                            finish_func=finish_func,
                        )
                        + self.__build_function(
                            name,
                            function,
                            in_class,
                            mode="async_callback",
                        )
                        + self.__build_function(
                            name,
                            function,
                            in_class,
                            mode="async_callback_kwargs",
                        )
                    )

            return self.__build_function(name, function, in_class)

        if in_class is None and (alias := self.get_alias(name, function)) is not None:
            # Set up a constant for functions that are aliases
            return f"{name}: {self.get_final()} = {alias}\n"

        signature_string: str
        missing_annotation = False

        if not is_overload and (overloads := get_overloads(function)):
            lines = [
                f"@{self.get_import('typing', 'overload')}\n{
                    self.build_function(name, overload, in_class, is_overload=True)
                }"
                for overload in overloads
            ]
            return "\n".join(lines)

        try:
            signature = inspect.signature(function)

            if name == "__init__" and signature.parameters:
                # Since we pass in __new__ with the name __init__, we need to replace
                # the `cls` parameter with `self` and set the return annotation to
                # `None`
                parameters = list(signature.parameters.values())
                parameters[0] = parameters[0].replace(
                    name="self", annotation=inspect.Parameter.empty
                )
                signature = signature.replace(
                    parameters=parameters, return_annotation=None
                )
            for param in signature.parameters.values():
                if param.name != "self" and param.annotation is inspect.Parameter.empty:
                    missing_annotation = True
            if signature.return_annotation is inspect.Signature.empty:
                missing_annotation = True

            signature_string = self.format_signature(signature)
        except Exception:
            missing_annotation = True
            if in_class:
                signature_string = "(self, *args, **kwargs)"
            else:
                signature_string = "(*args, **kwargs)"

        definition = ""
        if in_class:
            if hasattr(function, "name"):
                function_name: str = cast("Any", function).name
            else:
                function_name = function.__name__

            static_function = inspect.getattr_static(in_class, function_name, None)
            if (
                static_function
                and isinstance(static_function, staticmethod)
                and name != "__init__"
            ):
                definition += "@staticmethod\n"
        definition += f"def {name}{signature_string}:"
        docstring = (function.__doc__ or "").strip()
        if docstring:
            docstring = f'"""\n{docstring}\n"""'
            docstring = textwrap.indent(docstring, "    ")
            definition += f"\n{docstring}"
        else:
            definition += " ..."

        if missing_annotation:
            definition += "  # FIXME: Override is missing typing annotation"
        definition += "\n"

        return definition

    def __build_enum(
        self,
        name: str,
        enum_obj: type[Any],
        in_class: type[Any] | None,
        prefix_name: str,
        /,
        enum_type: Literal["enum", "flags"],
    ) -> str:
        override = self.check_override(prefix_name, name)
        if override:
            return override

        if in_class is None and (alias := self.get_alias(name, enum_obj)) is not None:
            return f"{name} = {alias}"

        full_name = generate_full_name(prefix_name, name)
        gobject_enum_base_name = "GEnum" if enum_type == "enum" else "GFlags"
        GObjectEnumBase = getattr(GObject, gobject_enum_base_name)
        int_enum_base = "IntEnum" if enum_type == "enum" else "IntFlag"

        enum_base = (
            self.get_namespace_member("GObject", gobject_enum_base_name)
            if issubclass(enum_obj, GObjectEnumBase)
            else self.get_import("enum", int_enum_base)
        )

        names: set[str] = set()
        lines: list[str] = []

        for key in sorted(vars(enum_obj)):
            if key.startswith(("__", "_")) or key[0].isdigit():
                continue

            enum_attr = getattr(enum_obj, key)

            override = self.check_override(full_name, key)
            if override:
                lines.append(override)
                continue

            if isinstance(enum_attr, GI.FunctionInfo):
                lines.append(self.build_function(key, enum_attr, enum_obj))
            elif hasattr(enum_attr, "real"):
                value = enum_attr.real
                lines.append(f"{key} = {value}")

                if isinstance(enum_attr, GObjectEnumBase):
                    names.update(
                        (enum_attr.value_name, enum_attr.value_nick)
                        if GObjectEnumBase is GObject.GEnum
                        else (*enum_attr.value_names, *enum_attr.value_nicks)
                    )
            else:
                lines.append(f"{key} = ...  # FIXME: {enum_type.title()}")

        if not lines:
            # No attributes were found
            lines = ["..."]

        cls_body = textwrap.indent("\n".join(lines), "    ")
        cls_definition = f"class {name}({enum_base}):\n{cls_body}"
        enum_value_definition = ""

        if names:
            literal_type_name = f"_{name}LiteralType"
            literal_type_symbol = self.get_type_alias(literal_type_name)
            value_type_symbol = self.get_type_alias(f"_{name}ValueType")

            names_joined = ", ".join(repr(n) for n in sorted(names))

            value_type = f"{name} | {literal_type_name}"
            if enum_type == "flags":
                value_type = f"{value_type} | tuple[{literal_type_name}, ...]"

            enum_value_definition = f"""
{literal_type_symbol} = {self.get_literal(names_joined)}
{value_type_symbol} = {value_type}"""

        return f"{cls_definition}{enum_value_definition}"

    def build_contents_and_fields(
        self,
        parent: _Object,
        children: list[str],
        in_class: type[Any] | None,
        prefix_name: str,
    ) -> tuple[str, list[GI.FieldInfo]]:
        """
        Inspect the passed module recursively and build stubs for functions,
        classes, etc.
        """
        classes: dict[str, ClassInfo] = {}
        functions: dict[str, Callable[..., Any]] = {}
        constants: dict[str, Any] = {}
        flags: dict[str, type[Any]] = {}
        enums: dict[str, type[Any]] = {}

        ret = ""

        for name in children:
            if name.startswith("__") and name not in _ALLOWED_FUNCTIONS:
                continue

            # Check if this is a valid name in python
            if not _identifier_re.match(name):
                continue

            try:
                obj = getattr(parent, name)
            except AttributeError:
                continue

            if inspect.isclass(obj):
                if issubclass(obj, IntFlag):
                    flags[name] = obj
                elif issubclass(obj, IntEnum):
                    enums[name] = obj
                else:
                    classes[name] = ClassInfo(self, obj, name, prefix_name, in_class)
            elif (
                inspect.isfunction(obj)
                or inspect.isbuiltin(obj)
                or inspect.ismethoddescriptor(obj)
            ):
                functions[name] = obj
            elif inspect.ismethod(obj):
                # bound methods
                functions[name] = obj.__func__
            elif callable(obj):
                # Fall back to a function for anything callable
                functions[name] = obj
            else:
                # Assume everything else is some manner of constant
                constants[name] = obj

        # Filter out private constants
        constants = {k: v for k, v in constants.items() if not k.startswith("_")}

        # Those are type hints overrides can have for instance attributes
        annotations = {
            k: v
            for k, v in getattr(parent, "__annotations__", {}).items()
            if not k.startswith("_") and k not in constants
        }

        # Remove fields from constants to preserve output order
        fields: list[GI.FieldInfo] = []
        if in_class:
            obj_info = getattr(in_class, "__info__", None)
            if isinstance(obj_info, (GI.StructInfo, GI.ObjectInfo)):
                for f in obj_info.get_fields():
                    field_name = f.get_name()
                    if field_name in constants:
                        del constants[field_name]
                        fields.append(f)

        # annotations
        for name in sorted(annotations):
            ret += f"{name}: {self.format_annotation(annotations[name])}\n"

        # Constants
        for name in sorted(constants):
            if name[0].isdigit():
                # GDK has some busted constant names like
                # Gdk.EventType.2BUTTON_PRESS
                continue

            override = self.check_override(prefix_name, name)
            if override:
                ret += override + "\n"
                continue

            val = constants[name]

            if str(val.__class__).startswith(("<flag", "<enum")):
                val = val.real

            annotation = getattr(parent, "__annotations__", {}).get(name)
            if annotation:
                annotation_string = self.format_annotation(annotation)
            else:
                annotation_string = val.__class__.__name__

            if (isinstance(val, str) and len(val) <= 50) or isinstance(val, bool):
                ret += f"{name}: {self.get_final()} = {val!r}\n"
            elif (
                isinstance(val, (str, float, int))
                or annotation is not None
                or not in_class
            ):
                ret += f"{name}: {self.get_final(annotation_string)}\n"
            else:
                constant_annotation = "" if in_class else f": {self.get_final()}"
                ret += f"{name}{
                    constant_annotation
                } = ...  # FIXME: Constant is missing typing annotation\n"

        if ret and functions:
            ret += "\n"

        # Functions
        if (
            in_class and issubclass(in_class, (GI.Boxed, GI.Struct, GObject.Object))
        ) or (self.check_override(prefix_name, "__init__")):
            # __new__ and __init__ are handled during class construction as __init__
            functions.pop("__new__", None)
            functions.pop("__init__", None)

        for name, func in sorted(functions.items()):
            override = self.check_override(prefix_name, name)
            if override:
                ret += override + "\n"
                continue

            ret += self.build_function(name, func, in_class)

        if ret and classes:
            ret += "\n"

        # Classes
        for _, class_info in sorted(classes.items()):
            if class_string := class_info.build():
                ret += f"{class_string}\n"

        if ret and flags:
            ret += "\n"

        # Flags
        for name, obj in sorted(flags.items()):
            ret += (
                self.__build_enum(name, obj, in_class, prefix_name, enum_type="flags")
                + "\n"
            )

        if ret and enums:
            ret += "\n"

        # Enums
        for name, obj in sorted(enums.items()):
            ret += (
                self.__build_enum(name, obj, in_class, prefix_name, enum_type="enum")
                + "\n"
            )

        return ret, fields

    def build(self) -> str:
        ret = self.build_contents_and_fields(self.parent, dir(self.parent), None, "")[0]

        extras: list[str] = []

        if self.namespace == "GObject":
            # TODO: find a better way to keep things (like protocols) that aren't in the
            # actual module but are needed for the stubs
            object_protocol = self.check_override("", "ObjectProtocol")

            if object_protocol is not None:
                extras.append(object_protocol)

        # TODO: enable this when PyGObject exposes CallbackInfos
        # This must be called before generating the imports
        # callbacks = self.__build_callback_types()

        if self.namespace == "Gio":
            async_ready_callback = self.get_type_alias("_AsyncReadyCallback")
            async_ready_var_args_callback = self.get_type_alias(
                "_AsyncReadyVarArgsCallback"
            )
            unpack_data_ts_symbol = self.get_unpack_data_ts()
            gobject_protocol_symbol = self.get_namespace_member(
                "GObject", "ObjectProtocol"
            )
            source_typevar_symbol = self.get_typevar(
                "_SourceObjectT", bound=f"{gobject_protocol_symbol} | None"
            )
            t_co_symbol = self.get_typevar(
                "_T", covariant=True, default=self.get_import("typing", "Any")
            )

            async_result_symbol = self.get_namespace_member("Gio", "AsyncResult")
            callable_symbol = self.get_import("collections.abc", "Callable")
            extras.extend(
                [
                    f"{async_ready_callback} = {callable_symbol}[[{
                        source_typevar_symbol
                    }, {async_result_symbol}, {t_co_symbol}], None]",
                    f"{async_ready_var_args_callback} = {callable_symbol}[[{
                        source_typevar_symbol
                    }, {async_result_symbol}, {unpack_data_ts_symbol}], None]",
                ]
            )

        imports = [f"{_import}" for _import in self.needed_imports.values()]
        extras_str = "\n".join(extras)

        # Only keep the typevars that are actually used in the generated stubs
        used_typevars: list[str] = []
        for typevar in self.needed_typevars:
            typevar_re = re.compile(rf"\b{typevar.name}\b")

            if (
                typevar_re.search(extras_str) is not None
                or typevar_re.search(ret) is not None
            ):
                used_typevars.append(typevar.build(self))

        return (
            "\n".join(imports)
            + "\n"
            + "\n".join(used_typevars)
            + "\n\n"
            + extras_str
            # TODO: enable this when PyGObject exposes CallbackInfos
            # + "\n\n"
            # + callbacks
            + "\n\n"
            + ret
        )

    @_check_override
    def render_constant(self, node: Constant, /) -> str:
        value = node.value
        if str(value.__class__).startswith(("<flag", "<enum")):
            value = cast("Any", value).real

        if (isinstance(value, str) and len(value) <= 50) or isinstance(value, bool):
            return f"{node.name}: {self.get_final()} = {value!r}"

        in_class = not isinstance(node.parent, Module)

        if (
            isinstance(node.value, (str, float, int))
            or node.annotation is not None
            or not in_class
        ):
            annotation_string = (
                self.format_annotation(node.annotation)
                if node.annotation is not None
                else value.__class__.__name__
            )
            return f"{node.name}: {self.get_final(annotation_string)}"

        constant_annotation = "" if in_class else f": {self.get_final()}"
        return f"{node.name}{
            constant_annotation
        } = ...  # FIXME: Constant is missing typing annotation\n"

    @_check_override
    def render_field(self, node: Field, /) -> str:
        py_type = self.render_type_info(node)
        flags = node.info.get_flags()
        if not (flags & GI.FieldInfoFlags.IS_WRITABLE):
            return self.get_property(node.name, (py_type, None))

        return f"{node.name}: {py_type}"

    @_check_override
    def render_enum(self, node: Enum, /) -> str:
        if (
            isinstance(node.parent, Module)
            and (alias := self.get_alias(node.name, node.cls)) is not None
        ):
            return f"{node.name} = {alias}"

        enum_base = (
            self.get_namespace_member("GObject", "GFlags" if node.is_flags else "GEnum")
            if node.is_gobject
            else self.get_import("enum", "IntFlag" if node.is_flags else "IntEnum")
        )

        body: list[str] = []
        names: set[str] = set()

        for key in sorted(vars(node.cls)):
            if key.startswith(("__", "_")) or key[0].isdigit():
                continue

            enum_attr = getattr(node.cls, key)

            if override := self.check_override(node.full_name, key):
                body.append(override)
                continue

            if isinstance(enum_attr, GI.FunctionInfo):
                body.append(
                    self.render_function(PyFunction.for_function(key, enum_attr, node))
                )
            elif hasattr(enum_attr, "real"):
                value = enum_attr.real
                body.append(f"{key} = {value}")

                if node.is_gobject:
                    names.update(
                        (*enum_attr.value_names, *enum_attr.value_nicks)
                        if node.is_flags
                        else (enum_attr.value_name, enum_attr.value_nick)
                    )
            else:
                body.append(
                    f"{key} = ...  # FIXME: {'Flags' if node.is_flags else 'Enum'}"
                )

        if not body:
            # No attributes were found
            body = ["..."]

        body_string = textwrap.indent("\n".join(body), "    ")
        cls_definition = f"class {node.name}({enum_base}):\n{body_string}"

        if names:
            literal_type_name = f"_{node.name}LiteralType"
            literal_type_symbol = self.get_type_alias(literal_type_name)
            value_type_symbol = self.get_type_alias(f"_{node.name}ValueType")

            names_joined = ", ".join(repr(n) for n in sorted(names))
            value_type = f"{node.name} | {literal_type_name}"

            if node.is_flags:
                value_type = f"{value_type} | tuple[{literal_type_name}, ...]"

            cls_definition = f"""{cls_definition}
{literal_type_symbol} = {self.get_literal(names_joined)}
{value_type_symbol} = {value_type}"""

        return cls_definition

    def render_props_property(
        self, node: Class, /, has_props_class: bool = False
    ) -> str:
        if override := self.check_override(node.full_name, "props"):
            return override

        if node.is_gobject and has_props_class:
            return self.get_property("props", ("Props", None))

        return ""

    def render_props_class(self, node: Class, /) -> str:
        if override := self.check_override(node.full_name, "Props"):
            return override

        if (
            not isinstance(node.info, (GI.ObjectInfo, GI.InterfaceInfo))
            or not node.properties
        ):
            return ""

        lines: list[str] = [
            prop_definition
            for name, prop_info in node.properties.items()
            if (
                prop_definition := self.get_property(
                    name,
                    (
                        self.render_type_info(
                            prop_info.type_info,
                            nullable=prop_info.read_nullable,
                            out=True,
                        )
                        if prop_info.readable
                        else None,
                        self.render_type_info(
                            prop_info.type_info,
                            nullable=prop_info.write_nullable,
                        )
                        if prop_info.writable and not prop_info.construct_only
                        else None,
                    ),
                )
            )
        ]

        props_string = "\n".join(lines) if lines else "..."
        parents_string = ""
        if isinstance(node.info, GI.ObjectInfo) and (parent := node.info.get_parent()):
            parent_name = f"{parent.get_name()}"
            parents_string = f"({
                self.get_namespace_member(parent.get_namespace(), parent_name)
            }.Props)"

        return f"""@{self.get_import("typing", "type_check_only")}
class Props{parents_string}:
{textwrap.indent(props_string, "    ")}"""

    def render_props(self, node: Class, /) -> str:
        lines: list[str] = []

        if props_class := self.render_props_class(node):
            lines.append(props_class)

        if props_property := self.render_props_property(
            node, has_props_class=bool(props_class)
        ):
            lines.append(props_property)

        return "\n".join(lines).strip()

    def render_type_info(
        self,
        node: Param | Return | Field | GI.TypeInfo,
        /,
        *,
        out: bool = False,
        nullable: bool = False,
        closure_target: bool = False,
    ) -> str:
        if isinstance(node, GI.TypeInfo):
            info = node
        elif isinstance(node, Field):
            info = node.info.get_type_info()
            out = True
        else:
            info = node.info
            out = isinstance(node, Return)
            nullable = (
                node.nullable if isinstance(node, Return) else node.default_is_none
            )
            closure_target = node.closure_target if isinstance(node, Param) else False

        if isinstance(info, Callback):
            return self.render_callback(info)

        py_type: str | None = None

        match info.get_tag():
            case GI.TypeTag.BOOLEAN:
                py_type = "bool"
            case (
                GI.TypeTag.INT8
                | GI.TypeTag.INT16
                | GI.TypeTag.INT32
                | GI.TypeTag.INT64
                | GI.TypeTag.UINT8
                | GI.TypeTag.UINT16
                | GI.TypeTag.UINT32
                | GI.TypeTag.UINT64
            ):
                py_type = "int"
            case GI.TypeTag.DOUBLE | GI.TypeTag.FLOAT:
                py_type = "float"
            case GI.TypeTag.UTF8 | GI.TypeTag.FILENAME | GI.TypeTag.UNICHAR:
                py_type = "str"
            case (GI.TypeTag.ARRAY | GI.TypeTag.GLIST | GI.TypeTag.GSLIST) as tag:
                value_info = info.get_param_type(0)

                if TYPE_CHECKING:
                    assert value_info is not None

                value_type = self.render_type_info(value_info, out=out)

                if tag == GI.TypeTag.ARRAY:
                    if out:
                        # As output argument array of type uint8 are returned as bytes
                        if value_info.get_tag() == GI.TypeTag.UINT8:
                            py_type = "bytes"
                        else:
                            py_type = f"list[{value_type}]"
                    else:
                        # As input arguments array can be generated by any sequence
                        py_type = f"{self.get_import('collections.abc', 'Sequence')}[{
                            value_type
                        }]"
                else:
                    py_type = f"list[{value_type}]"

                # All return/out/inout arrays/lists get marshalled as a list, regardless
                # of nullable
                nullable = nullable and not out
            case GI.TypeTag.GHASH:
                key_info = info.get_param_type(0)
                value_info = info.get_param_type(1)

                if TYPE_CHECKING:
                    assert key_info is not None
                    assert value_info is not None

                key_type = self.render_type_info(key_info, out=out)
                value_type = self.render_type_info(value_info, out=out)
                collection_type = (
                    "dict" if out else self.get_import("collections.abc", "Mapping")
                )

                py_type = f"{collection_type}[{key_type}, {value_type}]"
            case GI.TypeTag.INTERFACE:
                interface_info = info.get_interface()
                if isinstance(interface_info, GI.CallbackInfo):
                    py_type = self.render_callback(
                        Callback.for_callback(interface_info)
                    )
                elif (
                    isinstance(interface_info, GI.EnumInfo)
                    and interface_info.get_g_type() != GObject.TYPE_NONE
                ):
                    interface_namespace = interface_info.get_namespace()
                    interface_name = f"{interface_info.get_name()}"

                    # cairo doesn't use the `_<iface>ValueType` convention
                    if not out and interface_namespace != "cairo":
                        interface_name = f"_{interface_name}ValueType"

                    py_type = self.get_namespace_member(
                        interface_namespace, interface_name
                    )
                elif interface_info is not None:
                    interface_namespace = interface_info.get_namespace()
                    interface_name = interface_info.get_name()

                    if interface_namespace == "GObject" and interface_name == "Value":
                        py_type = self.get_import("typing", "Any")

                    elif (
                        interface_namespace == "GObject" and interface_name == "Closure"
                    ):
                        py_type = f"{
                            self.get_import('collections.abc', 'Callable')
                        }[..., {self.get_import('typing', 'Any')}]"

                    elif (
                        interface_namespace == "cairo"
                        and interface_name == "Context"
                        and not out
                    ):
                        some_surface = self.get_typevar(
                            "_SomeSurface",
                            bound=f"{self.get_namespace_member('cairo', 'Surface')}",
                        )
                        py_type = f"{self.get_namespace_member('cairo', 'Context')}[{
                            some_surface
                        }]"
                    else:
                        py_type = self.get_namespace_member(
                            interface_namespace, f"{interface_name}"
                        )
            case GI.TypeTag.VOID:
                if info.is_pointer():
                    if closure_target:
                        # Arguments passed to callbacks are specially handled by the
                        # PyGObject marshalling code, so they can be anything
                        py_type = f"{self.get_import('typing', 'Any')} | None"
                    else:
                        # Pointers can be int | CapsuleType | None, but we don't have
                        # CapsuleType until 3.13 This is what typeshed did until 3.13
                        py_type = (
                            "int"
                            if out
                            else f"int | {self.get_import('typing', 'Any')} | None"
                        )

                    # All return/out/inout pointers get marshalled as int, regardless of
                    # nullable
                    nullable = nullable and not out
                else:
                    py_type = "None"
            case GI.TypeTag.GTYPE:
                py_type = f"type[{self.get_import('typing', 'Any')}]"
            case GI.TypeTag.ERROR:
                py_type = self.get_namespace_member("GLib", "Error")

        if py_type is None:
            raise ValueError(f"Unsupported GI type tag: {info.get_tag()}")

        if nullable:
            py_type = make_nullable(py_type)

        return py_type

    def render_callback(self, node: Callback, /) -> str:
        callable_symbol = self.get_import("collections.abc", "Callable")
        param_types = [self.render_param(param) for param in node.params]
        return_types = [self.render_return(ret) for ret in node.returns]

        return f"{callable_symbol}[[{', '.join(param_types)}], {
            get_return_type(return_types)
        }]"

    def render_return(self, node: Return, /) -> str:
        type_info = (
            self.render_type_info(node)
            if isinstance(node.info, GI.TypeInfo)
            else self.render_callback(node.info)
        )

        if node.nullable:
            type_info = make_nullable(type_info)

        return type_info

    def render_param(self, node: Param, /) -> str:
        type_info = (
            self.render_type_info(node)
            if isinstance(node.info, GI.TypeInfo)
            else self.render_callback(node.info)
        )

        if node.kind == "callback":
            return type_info

        return ""

    def render_gi_function(
        self,
        node: GIFunction,
        /,
    ) -> str:
        lines: list[str] = []

        # Flags
        function_flags = node.info.get_flags()

        is_vfunc = isinstance(node.info, GI.VFuncInfo)
        constructor = bool(function_flags & GI.FunctionInfoFlags.IS_CONSTRUCTOR)
        method = is_vfunc or bool(function_flags & GI.FunctionInfoFlags.IS_METHOD)
        static = not isinstance(node.parent, Module) and not method and not constructor

        return_type = get_return_type([self.render_return(ret) for ret in node.returns])
        if node.wrapped is not MISSING:
            if node.wrapped is None:
                return_type = make_nullable(return_type)
            else:
                if type(node.wrapped) is tuple:
                    if len(node.wrapped) > 0:
                        return_type = f"({return_type} | tuple{
                            str(node.wrapped).replace('(', '[').replace(')', ']')
                        })"
                    else:
                        return_type = f"({return_type} | tuple[()])"
                else:
                    return_type = f"({return_type} | {
                        self.get_import('typing', 'Literal')
                    }[{node.wrapped}])"

        params = node.params

        param_types = [
            param.name if param.name == "*" else self.render_param(param)
            for param in params
        ]

        if constructor:
            if node.name == "__init__":
                # We pass the "new" constructor with the name __init__ because type
                # checkers do better with __init__ signatures, so we have to change the
                # signature a bit
                param_types.insert(0, "self")
                return_type = "None"
            else:
                lines.append("@classmethod")
                param_types.insert(0, "cls")
                # Override return value, for example Gtk.Button.new returns a Gtk.Widget
                # instead of Gtk.Button
                class_method_return_type = node.info.get_container().get_name()
                if (
                    class_method_return_type is not None
                    and return_type != f"{class_method_return_type} | None"
                ):
                    return_type = class_method_return_type
        elif method:
            param_types.insert(0, "self")
        elif static:
            lines.append("@staticmethod")

        lines.append(f"def {node.name}() -> None: ...")

        result = "\n".join(lines).strip()

        if node.wrapped is not MISSING:
            result = f"{result} # CHECK Wrapped function"

        return result

    def render_python_function(
        self, node: PyFunction, /, overload: Callable[..., object] | None = None
    ) -> str:
        if overload is None and (overloads := get_overloads(node.func)):
            return "\n".join(
                f"@{self.get_import('typing', 'overload')}\n{
                    self.render_python_function(node, overload=overload)
                }"
                for overload in overloads
            )

        function = node.func if overload is None else overload
        signature_string: str
        missing_annotation = False

        try:
            signature = inspect.signature(function)

            if node.name == "__init__" and signature.parameters:
                # Since we pass in __new__ with the name __init__, we need to replace
                # the `cls` parameter with `self` and set the return annotation to
                # `None`
                parameters = list(signature.parameters.values())
                parameters[0] = parameters[0].replace(
                    name="self", annotation=inspect.Parameter.empty
                )
                signature = signature.replace(
                    parameters=parameters, return_annotation=None
                )
            for param in signature.parameters.values():
                if param.name != "self" and param.annotation is inspect.Parameter.empty:
                    missing_annotation = True
            if signature.return_annotation is inspect.Signature.empty:
                missing_annotation = True

            signature_string = self.format_signature(signature)
        except Exception:
            missing_annotation = True
            signature_string = f"({
                'self, ' if isinstance(node.parent, (Class, Enum)) else ''
            }*args, **kwargs)".strip()

        function_string = f"def {node.name}{signature_string}:"
        if docstring := (function.__doc__ or "").strip():
            docstring = textwrap.indent(f'"""\n{docstring}\n"""', "    ")
            function_string = f"{function_string}\n{docstring}"
        else:
            function_string = f"{function_string} ..."

        if missing_annotation:
            function_string = (
                f"{function_string}  # FIXME: Override is missing typing annotation"
            )

        return function_string

    def render_function(self, node: PyFunction | GIFunction, /) -> str:
        if node.name.startswith("_") and node.name not in _ALLOWED_FUNCTIONS:
            return ""

        if (override := self.check_override(node)) is not None:
            return override

        if isinstance(node, GIFunction):
            if node.name == "access":
                breakpoint()

            return self.render_gi_function(node)

        return self.render_python_function(node)

        in_class = node.parent.cls if isinstance(node.parent, (Class, Enum)) else None

        if hasattr(node.func, "__wrapped__") and _strip_boolean_result_re.search(
            str(node.func)
        ):
            return self.render_wrapped_boolean_result_function(node)

        if isinstance(info := node.callable_info, (GI.FunctionInfo, GI.VFuncInfo)):
            if in_class is None and info.get_namespace() != self.namespace:
                # Set up a constant for functions that are aliases
                return f"{node.name}: {self.get_final()} = {
                    self.get_namespace_member(info)
                }\n"

            if isinstance(info, GI.FunctionInfo):
                finish_func = node.finish_function

                if finish_func is not None and not (
                    info.get_flags() & GI.FunctionInfoFlags.IS_CONSTRUCTOR
                ):
                    return ""  # TODO: build async overrides

            return self.render_gi_function(node, info)

        if (
            isinstance(node.parent, Module)
            and (alias := self.get_alias(node.name, node.func)) is not None
        ):
            # Set up a constant for functions that are aliases
            return f"{node.name}: {self.get_final()} = {alias}\n"

        return self.render_python_function(node)

    @_check_override
    def render_gobject_init(self, node: GObjectInit, /) -> str:
        if not node.init_properties:
            return ""

        args = [
            f"{name}: {
                self.type_info_to_python(prop.type_info, nullable=prop.write_nullable)
            } = ..."
            for name, prop in node.init_properties.items()
        ]

        return f"def __init__(self, *, {', '.join(args)}) -> None: ..."

    @_check_override
    def render_class_init(self, node: PyFunction | GObjectInit, /) -> str:
        if isinstance(node, GObjectInit):
            return self.render_gobject_init(node)

        return self.render_function(node)

    @_check_override
    def render_class(self, node: Class, /) -> str:
        in_class = node.parent.cls if isinstance(node.parent, Class) else None

        if not in_class and (alias := self.get_alias(node.name, node.cls)) is not None:
            # Set up a constant for classes that are aliases
            # NOTE: this should not use `Final` because doing so turns the alias into
            # a variable rather than a class
            return f"{node.name} = {alias}"

        body: list[str] = []

        # extracting docs
        docs = (
            f"{(getattr(node.cls, '__doc__', '') or '').strip()}\n\n{
                getattr(node.cls, '__gdoc__', '') or ''
            }"
        ).strip()

        if docs:
            body.append('"""\n' + docs.strip() + '\n"""')

        if node.is_gobject and (class_props := self.render_props(node)):
            body.append(class_props)

        body.extend(self.render_field(field) for field in node.fields.values())

        if node.init:
            body.append(self.render_class_init(node.init))

        for name, annotation in sorted(node.annotations.items()):
            body.append(f"{name}: {self.format_annotation(annotation)}")

        body.extend(
            self.render_constant(constant)
            for name, constant in sorted(node.constants.items())
            if not name[0].isdigit()
        )

        if body and node.methods:
            body.append("")

        body.extend(
            self.render_function(func) for _, func in sorted(node.methods.items())
        )

        if body and node.nested_classes:
            body.append("")

        body.extend(
            self.render_class(cls) for _, cls in sorted(node.nested_classes.items())
        )

        body_string = textwrap.indent("\n".join(body), "    ")
        body_string = f"\n{body_string}" if body_string else " ..."

        string_parents = ""
        if node.bases:
            bases_strings = [
                self.get_class_import(base) for base in node.bases if base is not object
            ]

            string_parents = f"({', '.join(bases_strings)})"

        return f"class {node.name}{string_parents}:{body_string}"

    def render_module(self, node: Module, /) -> str:
        parts: list[str] = []

        for name, annotation in sorted(node.annotations.items()):
            if name not in node.constants:
                parts.append(f"{name}: {self.format_annotation(annotation)}")

        parts.extend(
            self.render_constant(constant)
            for name, constant in sorted(node.constants.items())
            if not name[0].isdigit()
        )

        if parts and node.functions:
            parts.append("")

        parts.extend(
            self.render_function(func) for _, func in sorted(node.functions.items())
        )

        if parts and node.classes:
            parts.append("")

        parts.extend(self.render_class(cls) for _, cls in sorted(node.classes.items()))

        if parts and node.flags:
            parts.append("")

        parts.extend(self.render_enum(enum) for _, enum in sorted(node.flags.items()))

        if parts and node.enums:
            parts.append("")

        parts.extend(self.render_enum(enum) for _, enum in sorted(node.enums.items()))

        extras: list[str] = []

        if self.namespace == "GObject":
            # TODO: find a better way to keep things (like protocols) that aren't in the
            # actual module but are needed for the stubs
            object_protocol = self.check_override("", "ObjectProtocol")

            if object_protocol is not None:
                extras.append(object_protocol)

        if self.namespace == "Gio":
            async_ready_callback = self.get_type_alias("_AsyncReadyCallback")
            async_ready_var_args_callback = self.get_type_alias(
                "_AsyncReadyVarArgsCallback"
            )
            unpack_data_ts_symbol = self.get_unpack_data_ts()
            gobject_protocol_symbol = self.get_namespace_member(
                "GObject", "ObjectProtocol"
            )
            source_typevar_symbol = self.get_typevar(
                "_SourceObjectT", bound=f"{gobject_protocol_symbol} | None"
            )
            t_co_symbol = self.get_typevar(
                "_T", covariant=True, default=self.get_import("typing", "Any")
            )

            async_result_symbol = self.get_namespace_member("Gio", "AsyncResult")
            callable_symbol = self.get_import("collections.abc", "Callable")
            extras.extend(
                [
                    f"{async_ready_callback} = {callable_symbol}[[{
                        source_typevar_symbol
                    }, {async_result_symbol}, {t_co_symbol}], None]",
                    f"{async_ready_var_args_callback} = {callable_symbol}[[{
                        source_typevar_symbol
                    }, {async_result_symbol}, {unpack_data_ts_symbol}], None]",
                ]
            )

        imports = [f"{_import}" for _import in self.needed_imports.values()]

        imports_str = "\n".join(imports)
        extras_str = "\n".join(extras)
        parts_str = "\n".join(parts)

        # Only keep the typevars that are actually used in the generated stubs
        used_typevars: list[str] = []
        for typevar in self.needed_typevars:
            typevar_re = re.compile(rf"\b{typevar.name}\b")

            if (
                typevar_re.search(extras_str) is not None
                or typevar_re.search(parts_str) is not None
            ):
                used_typevars.append(typevar.build(self))

        used_typevars_str = "\n".join(used_typevars)

        return f"{imports_str}\n\n{used_typevars_str}\n\n{extras_str}\n\n{parts_str}\n"

    def build_from_info(self) -> str:
        module = Module.from_module(
            cast("Any", self.parent), DiscoveryContext(self.namespace, self.repo)
        )
        return self.render_module(module)
