from gi.repository import GObject

_lock = ...  # FIXME Constant
_namespace: str = "win32"
_version: str = "1.0"

class MSG(GObject.GPointer): ...
