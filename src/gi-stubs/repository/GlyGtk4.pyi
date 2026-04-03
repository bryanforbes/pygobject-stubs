from typing import Final
from typing import TypeVar

from gi.repository import _Gdk4
from gi.repository import Gly

T = TypeVar("T")

_lock = ...  # FIXME Constant
_namespace: Final = "GlyGtk4"
_version: Final = "2"

def frame_get_texture(frame: Gly.Frame) -> _Gdk4.Texture: ...
