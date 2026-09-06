"""Finite trajectory utilities for candidate discovery."""

from collections.abc import Iterator

from .accelerated import accelerated_step


def iterate(start: int, steps: int) -> Iterator[int]:
    """Yield a finite accelerated trajectory including its start value."""
    if steps < 0:
        raise ValueError("steps must be non-negative")
    current = start
    yield current
    for _ in range(steps):
        current = accelerated_step(current)
        yield current
