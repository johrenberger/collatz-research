"""Symbolic affine executor for accelerated Collatz trajectories.

Story 04: algebraic representation of the accelerated Collatz map
`T(n) = (3n + 1) / 2^ν₂(3n + 1)` and its iterations.

Represents `T` and its compositions as exact affine maps over ℤ:

- `AffineMap(a, b, k)` represents `n ↦ (a*n + b) / 2^k`.
- `BranchWord([k1, k2, ..., km])` represents a sequence of two-adic
  valuations; its induced affine map is the composition of the
  per-step `T` maps.
- `applies_to` checks whether the branch word is valid for a given
  input (positive odd, each step's valuation matches `ν₂(3nᵢ + 1)`).
- `execute` runs the word on a valid input.

The Python implementation is an untrusted witness for examples and
tests; the Lean counterpart in `Lean/CollatzResearch/Affine.lean` is
the formal module for proofs. See ADR-0007 for the design decision on
integer (vs. rational) representation with explicit denominator
exponent.
"""

from __future__ import annotations

from dataclasses import dataclass

from .accelerated import two_adic_valuation


@dataclass(frozen=True)
class AffineMap:
    """An affine map `n ↦ (a*n + b) / 2^k` over ℤ.

    `a` and `b` are arbitrary-precision integers (Python `int` is
    unbounded); `k` is a non-negative integer giving the denominator
    exponent (2^k).

    An `AffineMap` is well-formed at apply-time iff `2^k ∣ (a*n + b)`
    for the intended input `n`. The `apply` method validates this and
    raises `ValueError` on a violated divisibility rather than silently
    truncating.
    """

    a: int
    b: int
    k: int

    def __post_init__(self) -> None:
        if self.k < 0:
            raise ValueError(f"AffineMap.k must be non-negative; got {self.k}")

    @staticmethod
    def identity() -> AffineMap:
        """The identity map: `n ↦ n / 2^0 = n`."""
        return AffineMap(a=1, b=0, k=0)

    @staticmethod
    def step(k: int) -> AffineMap:
        """The single-step `T` map for a given two-adic valuation `k`:
        `n ↦ (3n + 1) / 2^k`. Valid on the positive odd domain when
        `k = ν₂(3n + 1)`."""
        if k < 1:
            raise ValueError(f"AffineMap.step(k) requires k >= 1; got {k}")
        return AffineMap(a=3, b=1, k=k)

    def apply(self, n: int) -> int:
        """Apply the map to `n`.

        Requires `2^k ∣ (a*n + b)`. Raises `ValueError` if the
        divisibility fails (rather than silently truncating with `//`).
        """
        numerator = self.a * n + self.b
        if self.k == 0:
            return numerator
        if numerator % (1 << self.k) != 0:
            raise ValueError(
                f"AffineMap.apply(n={n}): 2^{self.k} does not divide "
                f"a*n + b = {numerator}; map is (a={self.a}, b={self.b}, k={self.k})"
            )
        return numerator >> self.k

    def compose(self, other: AffineMap) -> AffineMap:
        """Return `self ∘ other` (apply `other` first, then `self`).

        The composed map satisfies:
            (self ∘ other).apply(n) = self.apply(other.apply(n))
        when both intermediate divisibilities hold.
        """
        # (a1*n + b1) / 2^k1 where n = (a2*n + b2) / 2^k2
        # = (a1 * ((a2*n + b2) / 2^k2) + b1) / 2^k1
        # = (a1*a2*n + a1*b2 + b1 * 2^k2) / 2^(k1+k2)
        return AffineMap(
            a=self.a * other.a,
            b=self.a * other.b + self.b * (1 << other.k),
            k=self.k + other.k,
        )


@dataclass(frozen=True)
class BranchWord:
    """A sequence of two-adic valuations describing an accelerated
    Collatz trajectory.

    A branch word `[k1, k2, ..., km]` is valid for an input `n` (a
    positive odd integer) when, at each step `i`, `ν₂(3*nᵢ + 1) = kᵢ`.
    The word's affine map is the composition of the per-step maps;
    executing the word on `n` yields the same result as applying that
    affine map.
    """

    valuations: tuple[int, ...]

    def __post_init__(self) -> None:
        for i, k in enumerate(self.valuations):
            if k < 1:
                raise ValueError(f"BranchWord.valuations[{i}] = {k} must be >= 1")

    @staticmethod
    def empty() -> BranchWord:
        """The empty branch word (zero steps)."""
        return BranchWord(valuations=())

    def to_affine(self) -> AffineMap:
        """Return the affine map representing this branch word.

        The composed map applies the steps in the order they appear in
        ``valuations``: the first valuation's step runs first, then the
        second, etc. The iteration is reversed so the composition
        convention ``self.compose(other)`` (= "apply other first, then
        self") produces the correct left-to-right order.
        """
        result = AffineMap.identity()
        for k in reversed(self.valuations):
            result = result.compose(AffineMap.step(k))
        return result

    def applies_to(self, n: int) -> bool:
        """`True` iff the branch word is valid for input `n` (positive
        odd integer; at each step `i`, `ν₂(3*nᵢ + 1) = kᵢ`)."""
        if n <= 0 or n % 2 == 0:
            return False
        current = n
        for k in self.valuations:
            t = 3 * current + 1
            if two_adic_valuation(t) != k:
                return False
            current = t >> k
        return True

    def execute(self, n: int) -> int:
        """Execute the branch word on `n`.

        Requires `self.applies_to(n)` to hold; raises `ValueError`
        otherwise. The result equals `self.to_affine().apply(n)`.
        """
        if not self.applies_to(n):
            raise ValueError(
                f"BranchWord.execute(n={n}): word {self.valuations} " f"does not apply to n"
            )
        current = n
        for k in self.valuations:
            current = (3 * current + 1) >> k
        return current
