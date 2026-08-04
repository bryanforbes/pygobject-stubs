# Stub Generator Refactor Plan

Goal: cleanly separate two layers in the stub generator.

- **Info layer (`info.py`):** Pure GI/Python discovery — walks GObject
  introspection, Python class attributes, and overrides, producing a tree of
  typed `Container`/`Buildable` nodes. No string formatting, no imports
  tracking.
- **Rendering layer (`Stub`):** Takes a node tree and renders text. Owns
  imports/typevars/overrides registry plus helpers like `get_import`,
  `get_namespace_member`, `get_property`, `type_info_to_python`,
  `format_annotation`.

The refactor is for maintainability, not behavior change. The verification bar
is **byte-identical output** against the legacy generator for each GI namespace
we ship stubs for.

---

## TL;DR

Finish the refactor by making `info.py` a **stable semantic tree of discovered
GI/Python facts**, and move all `build()`/string/import/override decisions back
into `Stub` as renderer methods. Do not finish the current
`Buildable.build(stub)` direction as the final architecture; use it only as a
temporary shim if needed.

Overall effort: **L/XL, ~2–4 days** if you keep byte-identical output as the
bar and port incrementally.

---

## 1. Critique of the current `info.py` design

1. **`Buildable.build(stub)` violates the target separation.** Current nodes
   know how to render themselves and call `stub.get_import()`, `stub.get_final()`,
   `stub.type_info_to_python()`, etc. That keeps the old entanglement, just
   moved into more classes.

   Recommended final direction:
   ```python
   # info.py
   @dataclass(slots=True)
   class Function:
       name: str
       func: Callable[..., object]
       container: Container
       ...

   # stub.py
   def render_function(self, node: info.Function) -> str:
       ...
   ```
   Transitional compromise: keep `node.build(stub)` as:
   ```python
   def build(self, stub: Stub) -> str:
       return stub.render(self)
   ```
   but make `Stub` the actual owner of rendering.

2. **`Container.__iter__` is too weak to preserve output.** Old output depends
   on explicit sections:
   1. annotations
   2. constants
   3. functions
   4. classes
   5. flags
   6. enums

   It also depends on conditional blank lines between non-empty groups. A
   generic iterator over `Buildable` nodes cannot encode this cleanly.

   Prefer explicit grouped fields:
   ```python
   @dataclass(slots=True)
   class Module:
       name: str
       annotations: dict[str, object]
       constants: dict[str, Constant]
       functions: dict[str, Function]
       classes: dict[str, Class]
       flags: dict[str, Enum]
       enums: dict[str, Enum]
   ```
   Then `Stub.render_module_body()` owns ordering and spacing.

3. **`_ContainedMixin` is brittle and not buying much.** It mixes generics,
   slots, dataclass inheritance, and optional containers. `full_name` currently
   risks producing `"NoneFoo"` if `container is None`.

   Simpler:
   ```python
   @dataclass(slots=True)
   class Node:
       name: str
       parent: Container | None = None

       @property
       def full_name(self) -> str:
           if self.parent is None:
               return self.name
           return f"{self.parent.full_name}.{self.name}"
   ```
   Or skip inheritance and implement `full_name` only where needed.

4. **`Argument` duplication should be removed.** `info.py` reimplements most of
   `Arguments.for_callable()`, but loses details already handled in
   `arguments.py` (varargs slots, closure targets, async transforms, callback
   user-data heuristics).

   Delete `info.Argument` and expose `Arguments` directly from `Function`:
   ```python
   @property
   def arguments(self) -> Arguments | None:
       if isinstance(self.func, GI.CallableInfo):
           return Arguments.for_callable(self.func)
       return None
   ```

5. **The lazy `_args` cache is the wrong shape.** Callable argument discovery
   depends on mode (normal, `allow_varargs=False`, async, async callback
   kwargs). A single cached `list[Argument]` is not enough.

   Better:
   ```python
   def get_arguments(self, *, allow_varargs: bool = True) -> Arguments | None:
       ...
   ```
   Let the renderer call:
   ```python
   args = node.arguments().as_async()
   args = node.arguments().as_async_callback_kwargs()
   ```

6. **`Class.__iter__` currently misses required synthetic sections.** Old
   `ClassInfo.build()` emits:
   1. docstring
   2. `Props` class
   3. `props` property
   4. fields
   5. synthesized `__init__`
   6. regular contents

   Current `Class.__iter__` only yields constants, fields, methods, nested
   classes. Don't hide these in `__iter__`. Make them explicit class fields or
   renderer phases.

7. **`Class.for_class()` has a likely annotations bug.** It currently does:
   ```python
   getattr(container, "__annotations__", {})
   ```
   But `container` is an info container, not the Python class being inspected.
   It should use the inspected class/source object:
   ```python
   getattr(cls_, "__annotations__", {})
   ```

8. **Current module enum order differs from old output.** Old order: flags
   before enums. Current `Module.__iter__`: enums before flags. This will break
   byte equivalence.

---

## 2. Recommended node taxonomy

Separate nodes into two categories: **info nodes** and **renderer-derived
cases**.

### 2.1 Info nodes (live in `info.py`)

These represent discovered facts, not rendered text.

1. **`DiscoveryContext`** — `info.py` should not depend on `Stub`, but property
   discovery needs `repo`.
   ```python
   @dataclass(slots=True, frozen=True)
   class DiscoveryContext:
       namespace: str
       repo: GIRepository.Repository
   ```

2. **`Module`**
   ```python
   class Module:
       name: str
       py_module: ModuleType
       annotations: dict[str, object]
       constants: dict[str, Constant]
       functions: dict[str, Function]
       classes: dict[str, Class]
       flags: dict[str, Enum]
       enums: dict[str, Enum]
       callbacks: dict[str, Callback]
   ```
   `callbacks` can stay empty until PyGObject callback exposure is usable.

3. **`Class`**
   ```python
   class Class:
       name: str
       cls: type[object]
       info: GI.RegisteredTypeInfo | None
       bases: tuple[type[object], ...]
       annotations: dict[str, object]

       constants: dict[str, Constant]
       fields: dict[str, Field]
       methods: dict[str, Method]
       nested_classes: dict[str, Class]
       flags: dict[str, Enum]
       enums: dict[str, Enum]

       properties: dict[str, Property]
       init_properties: dict[str, Property]
   ```
   Keep interface/object/struct/boxed as computed properties:
   ```python
   @property
   def is_object(self) -> bool: ...
   @property
   def is_interface(self) -> bool: ...
   ```

4. **`Enum`** — prefer a separate node over subclassing `Class`, unless
   subclassing is already too convenient to unwind.
   ```python
   class Enum:
       name: str
       cls: type[IntEnum | IntFlag]
       info: GI.EnumInfo | None
       is_flags: bool
       is_gobject: bool
       members: dict[str, EnumMember]
       methods: dict[str, Method]
   ```

5. **`EnumMember`**
   ```python
   class EnumMember:
       name: str
       value: object

       @property
       def literal_names(self) -> tuple[str, ...]:
           ...
   ```

6. **`Constant`**
   ```python
   class Constant:
       name: str
       value: object
       annotation: object | None
   ```

7. **`Field` / `Attribute`** — rename to `Field` if possible because it
   specifically wraps `GI.FieldInfo`.
   ```python
   class Field:
       name: str
       info: GI.FieldInfo
   ```

8. **`Function`**
   ```python
   class Function:
       name: str
       func: Callable[..., object]
       parent: Module | Class | Enum

       @property
       def callable_info(self) -> GI.CallableInfo | None:
           return self.func if isinstance(self.func, GI.CallableInfo) else None

       def arguments(
           self, *, allow_varargs: bool = True
       ) -> Arguments | None:
           if self.callable_info is None:
               return None
           return Arguments.for_callable(
               self.callable_info, allow_varargs=allow_varargs
           )
   ```

9. **`Method`** — could subclass `Function`, but keep only semantic additions:
   ```python
   class Method(Function):
       owner: Class | Enum
       py_owner: type[object]
   ```
   Renderer can still inspect `py_owner` to determine `@staticmethod` for
   Python override methods.

10. **`Property`** — replace current `PropertyInfo(stub, ...)` with a pure
    info node:
    ```python
    class Property:
        gi_info: GI.PropertyInfo
        gir_info: GIRepository.PropertyInfo
        gobject_name: str
        python_name: str
        readable: bool
        writable: bool
        construct: bool
        construct_only: bool
        type_info: GI.TypeInfo
        read_nullable: bool
        write_nullable: bool
    ```
    No `prop_type: str`, no `init_type: str` in info.

11. **`Callback`**
    ```python
    class Callback:
        name: str
        info: GI.CallbackInfo
        arguments: Arguments
    ```
    Keep this dormant until callback info generation is enabled.

12. **Synthetic semantic nodes (optional but useful).** Not raw GI objects, but
    semantic stub members. They can live in `info.py` if they contain no
    rendered text:
    ```python
    class PropsClass:
        owner: Class
        properties: dict[str, Property]

    class PropsAccessor:
        owner: Class

    class SyntheticInit:
        owner: Class
        init_properties: dict[str, Property]
        constructor_func: Function | None
    ```

### 2.2 Renderer-derived cases (do NOT make primary info nodes)

These are better handled inside `Stub.render_*()`.

1. **`Alias`** — don't discover as a first-class info node initially. Info
   stores the original object; renderer decides:
   ```python
   alias = self.get_alias(node.name, node.cls_or_func)
   ```

2. **`AsyncOverloadSet`** — don't store in info. It's a rendering expansion of
   a `Function` with a finish function. Renderer emits the three overloads.

3. **`WrappedStripBoolean`** — don't store as a node initially. Renderer
   detects `__wrapped__` plus `strip_boolean_result`, as old code does.

4. **`Final`** — definitely renderer-only. Whether to emit `Final[...]` depends
   on output style/import tracking.

---

## 3. What belongs in info vs `Stub`

### 3.1 Info layer should own

1. Walking module/class attributes.
2. Grouping discovered children into constants/functions/classes/flags/enums.
3. Normalizing class bases structurally.
4. Finding GI fields.
5. Finding GObject properties via `GIRepository.Repository`.
6. Computing property flags and nullability.
7. Exposing raw `GI.TypeInfo`, `GI.CallableInfo`, `GI.ArgInfo`.
8. Exposing `Arguments` from `arguments.py`.
9. Computing stable `full_name`.

### 3.2 `Stub` renderer should own

1. All string generation.
2. All import tracking.
3. All typevar tracking.
4. `type_info_to_python`.
5. `format_annotation` / `format_signature`.
6. `get_property`.
7. `get_final`.
8. `get_alias`.
9. `check_override`.
10. Namespace-specific rendering extras:
    - Gtk `import os`
    - GObject `ObjectProtocol`
    - Gio `_AsyncReadyCallback`
    - Gio `_AsyncReadyVarArgsCallback`
11. Async overload expansion.
12. `strip_boolean_result` rendering.
13. Deciding whether foreign-namespace functions/classes render as aliases.

### 3.3 Borderline case: name normalization

Move `fix_argument_name()` into a pure utility, e.g.
`utils.fix_python_identifier()`, and let `Stub.fix_argument_name()` delegate to
it.

Reason: property de-duplication and argument names are semantic Python
identifiers, not import/rendering state.

---

## 4. Incremental porting plan

### Step 0 — Add a legacy/new comparison harness

Effort: **S, <1h**

Before changing behavior, preserve the old implementation:

```python
def build_legacy(self) -> str:
    return self.build_contents_and_fields(self.parent, dir(self.parent), None, "")[0]
```

Add a temporary new entry point:

```python
def build_from_info(self) -> str:
    module = info.Module.from_module(
        info.DiscoveryContext(self.namespace, self.repo),
        self.parent,
    )
    return self.render_module(module)
```

For comparison, use two fresh `Stub` instances because rendering mutates
imports/typevars:

```python
old = make_stub().build()
new = make_stub().build_from_info()
assert old == new
```

Do this per namespace, not only globally.

---

### Step 1 — Make `info.py` a stable tree, not a renderer

Effort: **M, 1–3h**

1. Add `DiscoveryContext`.
2. Change `Module.from_module()` to accept context.
3. Replace generator-only `__iter__` traversal with explicit grouped fields.
4. Keep order byte-compatible:
   - annotations
   - constants
   - functions
   - classes
   - flags
   - enums
5. Fix `Class.for_class()` annotations to read from `cls_`.
6. Keep `build()` methods as temporary shims only if needed:
   ```python
   def build(self, stub: Stub) -> str:
       return stub.render(self)
   ```

Rationale: this gives you a real tree and stops output ordering from being
hidden in arbitrary iteration.

---

### Step 2 — Reuse `arguments.py`

Effort: **S/M, 1–2h**

Delete `info.Argument` and the duplicated argument-discovery code in
`Function.arguments`.

Recommended shape:

```python
@dataclass(slots=True)
class Function:
    name: str
    func: Callable[..., object]
    parent: Container

    def get_arguments(
        self, *, allow_varargs: bool = True
    ) -> Arguments | None:
        if isinstance(self.func, GI.CallableInfo):
            return Arguments.for_callable(self.func, allow_varargs=allow_varargs)
        return None

    @property
    def finish_function(self) -> GI.FunctionInfo | None:
        if isinstance(self.func, GI.FunctionInfo):
            return get_finish_func(self.func)
        return None
```

Do not precompute async variants in info. Renderer can call:

```python
arguments = node.get_arguments()
async_arguments = arguments.as_async()
callback_kwargs_arguments = arguments.as_async_callback_kwargs()
```

Rationale: `arguments.py` is already the correct discovery abstraction.

---

### Step 3 — Port function/method rendering first

Effort: **M, 1–3h**

Keep the old logic almost verbatim, but make it node-driven.

Add renderer methods:

```python
def render_function(self, node: info.Function) -> str:
    ...

def render_method(self, node: info.Method) -> str:
    ...
```

Port these old methods into node-aware renderer helpers:

1. `build_function(...)`
2. `__build_function(...)`
3. `__wrapped_strip_boolean_result(...)`

Recommended intermediate approach:

```python
def render_function(self, node: info.Function) -> str:
    return self._render_callable(
        name=node.name,
        function=node.func,
        in_class=node.parent.cls if isinstance(node.parent, info.Class) else None,
    )
```

Then later clean up the parameter list.

Preserve exactly:

1. private-name filtering.
2. override checks before rendering.
3. `strip_boolean_result` special case.
4. foreign namespace function aliasing.
5. Python overload handling via `typing.get_overloads`.
6. Python docstring handling.
7. staticmethod detection for Python override methods.
8. GI async triple-overload generation:
   - awaitable
   - callback required
   - callback kwargs

Rationale: functions are the most complex and most reused piece. Porting them
first gives fast feedback on the riskiest behavior.

---

### Step 4 — Port module rendering

Effort: **M, 1–2h**

Implement:

```python
def render_module_body(self, module: info.Module) -> str:
    parts: list[str] = []

    annotations = ...
    constants = ...
    functions = ...
    classes = ...
    flags = ...
    enums = ...

    return join_groups_with_old_spacing(parts)
```

Important: preserve the old blank-line rules. The old code inserts blank lines
only between non-empty groups.

Suggested helper:

```python
def _join_nonempty_groups(self, groups: Iterable[str]) -> str:
    return "\n\n".join(group.rstrip("\n") for group in groups if group)
```

But verify trailing newline behavior against old output. Byte equivalence may
require adding exactly one final `\n`.

Rationale: once functions render correctly, module rendering becomes mostly
ordering and spacing.

---

### Step 5 — Port class rendering, but initially keep property/init gaps

Effort: **M, 1–3h**

Implement:

```python
def render_class(self, node: info.Class) -> str:
    ...
```

Match old `ClassInfo.build()` order:

1. class override check.
2. top-level alias check.
3. bases.
4. docstring.
5. props block.
6. fields.
7. synthesized init.
8. regular contents.

At first, you can leave props/init as TODO and compare output on
non-GObject/simple classes. Then fill them in steps 6–7.

Important suppression rule from old `build_contents_and_fields()`:

```python
if (
    in_class and issubclass(in_class, (GI.Boxed, GI.Struct, GObject.Object))
) or self.check_override(prefix_name, "__init__"):
    functions.pop("__new__", None)
    functions.pop("__init__", None)
```

In the new renderer, do not delete methods during discovery. Instead, when
rendering class contents, skip `__new__` and `__init__` if the class renderer
is going to synthesize or override `__init__`.

Rationale: discovery should collect facts; rendering should decide which facts
are emitted.

---

### Step 6 — Replace `property_info.py` with pure `info.Property`

Effort: **M, 1–3h**

Refactor `PropertyInfo` so it no longer stores `stub`.

Current bad part:

```python
self.stub.type_info_to_python(...)
```

Replace with raw info:

```python
@dataclass(slots=True)
class Property:
    gi_info: GI.PropertyInfo
    gir_info: GIRepository.PropertyInfo
    gobject_name: str
    python_name: str
    type_info: GI.TypeInfo
    read_nullable: bool
    write_nullable: bool
    readable: bool
    writable: bool
    construct: bool
    construct_only: bool
```

Then the renderer computes:

```python
read_type = (
    self.type_info_to_python(prop.type_info, nullable=prop.read_nullable, out=True)
    if prop.readable
    else None
)

write_type = (
    self.type_info_to_python(prop.type_info, nullable=prop.write_nullable)
    if prop.writable and not prop.construct_only
    else None
)
```

Port old property discovery from `ClassInfo.__get_properties()` into
`info.Class.from_class()` or a helper.

Preserve:

1. current class/interface properties first.
2. include interface properties for objects.
3. parent init properties after current properties.
4. first property name wins.
5. de-dup by Python property name, not necessarily raw GObject name.

Rationale: this removes the biggest current discovery/rendering leak outside
function rendering.

---

### Step 7 — Port `Props` class and `props` accessor

Effort: **S/M, 1–2h**

Renderer methods:

```python
def render_props_class(self, node: info.Class) -> str | None:
    ...

def render_props_accessor(
    self, node: info.Class, props_class_rendered: bool
) -> str | None:
    ...
```

Preserve old behavior:

1. `Props` override check:
   ```python
   self.check_override(class_full_name, "Props")
   ```
2. Only emit `Props` for object/interface info with properties.
3. Parent props inheritance:
   ```python
   class Props(Parent.Props):
   ```
4. Decorate with:
   ```python
   @type_check_only
   ```
5. Emit `props` property only for `GI.ObjectInfo` and only if `Props` exists.

Rationale: props are synthetic rendering around discovered `Property` nodes.

---

### Step 8 — Port synthesized `__init__`

Effort: **M, 1–3h**

Implement renderer equivalent of `ClassInfo.__build_init()`.

Keep the old priority exactly:

1. If `Class.__init__` override exists, emit override.
2. For `GI.Boxed` / `GI.Struct`:
   - if `__new__` is the same as a GI method, render that method as `__init__`.
   - else if class defines `__new__`, render `__new__` as `__init__`.
   - else if class defines `__init__`, render it.
3. For non-`GI.ObjectInfo`, emit nothing.
4. If object has no init properties:
   - if class defines `__new__`, render it as `__init__`.
   - else emit nothing.
5. Otherwise synthesize:
   ```python
   def __init__(self, *, prop: Type = ..., ...) -> None: ...
   ```

Renderer computes init property types from `info.Property`.

Rationale: this is behavior-sensitive and strongly tied to class content
suppression, so keep it renderer-owned.

---

### Step 9 — Port enum rendering

Effort: **S/M, 1–2h**

Current `info.Enum` is close, but fix ordering and responsibility.

Renderer should own:

1. enum base import:
   - `GObject.GEnum` / `GObject.GFlags`
   - or `enum.IntEnum` / `enum.IntFlag`
2. enum member rendering.
3. enum method rendering.
4. literal/value type alias emission.

Info should own:

1. `is_flags`
2. `is_gobject`
3. members
4. GObject literal names from enum values.

Preserve old order:

1. flags group before enums group.
2. methods/members sorted as old `vars(enum_obj)` iteration was sorted.

---

### Step 10 — Add callbacks, but do not block cutover on them

Effort: **S now, M later**

Since old callback generation is commented out, do not make this part of the
equivalence-critical cutover.

Add shape now:

```python
callbacks: dict[str, Callback] = {}
```

Later, when enabling callback generation:

1. `info.Module.from_module()` or `Module.from_repository()` gathers
   `GI.CallbackInfo`.
2. `Stub.render_callback()` emits `TypeAlias`.
3. `type_info_to_python()` can refer to named callbacks instead of always
   emitting inline `Callable`.

Rationale: callback support is architecturally important but not required for
byte-identical current output.

---

### Step 11 — Keep module-level extras in `Stub`, not `info.py`

Effort: **S, <1h**

Do not make `Module.from_module()` gather these:

1. GObject `ObjectProtocol`
2. Gio `_AsyncReadyCallback`
3. Gio `_AsyncReadyVarArgsCallback`
4. Gtk `import os`

These are renderer/prelude concerns, not GI discovery.

Recommended final build flow:

```python
def build(self) -> str:
    module = info.Module.from_module(
        info.DiscoveryContext(self.namespace, self.repo),
        self.parent,
    )

    body = self.render_module_body(module)

    extras = self.render_namespace_extras()

    imports = self.render_imports()
    typevars = self.render_used_typevars(body, extras)

    return self.assemble(imports, typevars, extras, body)
```

Important: render `body` and `extras` before finalizing imports/typevars
because rendering mutates `needed_imports` and `needed_typevars`.

---

### Step 12 — Cut over only after byte-equivalence

Effort: **M/L, 0.5–1 day**

When `build_from_info()` matches `build()` for the installed GI module suite:

1. Make `Stub.build()` call the new path.
2. Keep `build_legacy()` temporarily behind a private/debug method.
3. Remove `ClassInfo` only after the new class renderer owns:
   - docstrings
   - props
   - fields
   - init synthesis
   - class contents
4. Remove `property_info.py` or keep it only as a pure helper if
   renamed/refactored.

---

## 5. Suggested renderer API shape

A small dispatcher is enough; avoid overengineering.

```python
def render(self, node: object) -> str:
    if isinstance(node, info.Module):
        return self.render_module_body(node)
    if isinstance(node, info.Class):
        return self.render_class(node)
    if isinstance(node, info.Enum):
        return self.render_enum(node)
    if isinstance(node, info.Function):
        return self.render_function(node)
    if isinstance(node, info.Constant):
        return self.render_constant(node)
    if isinstance(node, info.Field):
        return self.render_field(node)
    raise TypeError(type(node))
```

Keep the old helpers as private rendering helpers while porting:

```python
def _render_callable(
    self,
    name: str,
    function: Callable[..., Any],
    in_class: type[Any] | None,
    *,
    is_overload: bool = False,
) -> str:
    ...
```

This minimizes risk because you can move code mechanically first, then clean
it later.

---

## 6. Verification strategy and invariants

### 6.1 Byte-equivalence checks

Use fresh `Stub` instances:

```python
legacy = make_stub(namespace).build_legacy_full()
new = make_stub(namespace).build_from_info()
assert legacy == new
```

Run this for at least:

1. `GLib`
2. `GObject`
3. `Gio`
4. `Gtk`
5. one enum-heavy namespace
6. one override-heavy namespace

### 6.2 Add focused snapshot tests while porting

Good high-risk snapshots:

1. Gio async methods/functions.
2. GObject classes with properties.
3. classes with overrides.
4. structs/boxed constructors.
5. enum/flags literal alias generation.
6. foreign namespace aliases.
7. Python override functions with `typing.overload`.
8. `strip_boolean_result` wrappers.

### 6.3 Useful invariants

1. `info.py` must not call:
   - `stub.get_import`
   - `stub.get_final`
   - `stub.type_info_to_python`
   - `stub.format_annotation`
   - `stub.get_property`
2. `info.py` may import/use:
   - GI metadata
   - `Arguments`
   - pure utilities like identifier normalization.
3. Renderer may inspect raw GI objects, but should not discover new tree
   children.
4. Output section order must match old code.
5. A node should be renderable more than once without changing its own state.
6. Rendering should use a fresh `Stub` for comparison because imports/typevars
   are intentionally stateful.
7. Overrides are checked by renderer before normal node rendering.
8. Aliases are only emitted where old code emitted aliases:
   - top-level classes/enums/functions
   - foreign namespace GI functions at module level
   - not nested class aliases unless old behavior did so.

---

## 7. Main architectural pitfalls to avoid

1. **Circular discovery/rendering dependency.**

   Bad:
   ```python
   info.Class.from_class(..., stub)
   prop_type = stub.type_info_to_python(...)
   ```
   Good:
   ```python
   info.Property(type_info=...)
   stub.render_property(prop)
   ```

2. **Renderer asking nodes to synthesize render-only children.** Avoid
   `Class.__iter__()` dynamically yielding `PropsClass` based on renderer
   state. Either store semantic synthetic nodes during discovery, or have
   `render_class()` perform fixed rendering phases.

3. **Rendering order changing import order.** Imports are emitted in insertion
   order from calls to `get_import()`. Therefore even byte-identical body text
   can differ if rendering order changes. Preserve old traversal order
   carefully.

4. **Rendering the same `Stub` twice.** `Stub` is stateful. Equivalence tests
   must construct two separate stubs.

5. **Slots + lazy caches + inheritance.** `dataclass(slots=True)` with multiple
   inheritance and manual cached fields is easy to break. Prefer eager
   discovery into plain fields for child groups. Use explicit cache fields
   only for expensive local computations.

6. **Over-modeling render variants as info nodes.** `AsyncOverloadSet`,
   `WrappedStripBoolean`, `Alias`, and `Final` are not GI facts. Keep them in
   renderer unless you later add a separate "render plan" layer.

---

## 8. Recommended immediate next actions

1. **Stop expanding current node `build()` methods.**
2. Add `DiscoveryContext`.
3. Replace `info.Argument` with `Arguments`.
4. Add `Stub.render_function(info.Function)` by wrapping the existing
   `build_function()` logic.
5. Add `Stub.render_module_body(info.Module)` with exact old group ordering.
6. Run old-vs-new comparison for module-level constants/functions first.
7. Then port class rendering, properties, and `__init__` synthesis.

This path keeps the refactor incremental, preserves behavior, and prevents
`info.py` from becoming a second renderer.
