from typing import Final
from typing import TypeVar

from gi.repository import _Gtk4
from gi.repository import Xdp

T = TypeVar("T")

_lock = ...  # FIXME Constant
_namespace: Final = "XdpGtk4"
_version: Final = "1.0"

def parent_new_gtk(window: _Gtk4.Window) -> Xdp.Parent: ...
