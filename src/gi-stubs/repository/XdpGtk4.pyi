from gi.repository import _Gtk4 as Gtk
from gi.repository import Xdp

_lock = ...  # FIXME Constant
_namespace: str = "XdpGtk4"
_version: str = "1.0"

def parent_new_gtk(window: Gtk.Window) -> Xdp.Parent: ...
