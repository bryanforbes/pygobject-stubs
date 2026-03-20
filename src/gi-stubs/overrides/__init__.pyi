from typing import TypeVar

T = TypeVar("T")

def override(_type: type[T]) -> type[T]: ...
