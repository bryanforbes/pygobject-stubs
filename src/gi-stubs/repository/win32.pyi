from typing import Final
from typing import TypeVar

from gi.repository import GObject

T = TypeVar("T")

_lock = ...  # FIXME Constant
_namespace: Final = "win32"
_version: Final = "1.0"

class MSG(GObject.GPointer): ...
