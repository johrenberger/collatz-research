import Mathlib

/-!
# Residues and partitions

Formalizes residue classes modulo `m` and their completeness/disjointness
properties for the residue partition checker (Story 05).

This module makes no convergence, cycle-exclusion, or global descent
claim. It is the Lean foundation for the Python `is_partition` checker
in `python/collatz_research/partitions.py`.

**Proof status (2026-08-10, Story 05):**
- Definitions: complete.
- Structural theorems: `residue_lt`, `residue_zero`, `Partition.trivial_*`
  proved by `rw` + `omega` / `List.mem_range` / `List.nodup_range`.
- No `sorry` introduced.
-/

namespace CollatzResearch

/-- A residue is a canonical representative of a residue class
modulo `m`, i.e., a natural number `r < m`. -/
def Residue (m : ℕ) (r : ℕ) : Prop := r < m

/-- The canonical residue of `n` modulo `m`. -/
def residue (m n : ℕ) : ℕ := n % m

theorem residue_lt (m n : ℕ) (hm : m > 0) : residue m n < m := by
  unfold residue
  apply Nat.mod_lt
  exact hm

theorem residue_zero (m : ℕ) : residue m 0 = 0 := by
  rw [residue, Nat.zero_mod m]

/-- A partition of `ℤ/mℤ` is a list of residues that:
- Has no duplicates (disjointness).
- Covers all of `[0, m)` (completeness).
- All elements are valid residues (`< m`).
- The modulus is positive (`0 < m`), encoded as a structure field so
  that `Partition 0` is uninhabitable. This matches Python
  `is_partition`'s `m >= 1` rejection and makes the Lean type a sound
  target for a future checker-soundness theorem. -/
structure Partition (m : ℕ) where
  residues : List ℕ
  disjoint : residues.Nodup
  complete : ∀ r : ℕ, r < m → r ∈ residues
  valid : ∀ r ∈ residues, r < m
  positive : 0 < m

namespace Partition

/-- The trivial partition: `[0, 1, ..., m-1]`. -/
def trivial (m : ℕ) : List ℕ := List.range m

theorem trivial_mem (m r : ℕ) : r ∈ Partition.trivial m ↔ r < m := by
  rw [Partition.trivial, List.mem_range]

theorem trivial_nodup (m : ℕ) : (Partition.trivial m).Nodup := by
  rw [Partition.trivial]
  exact List.nodup_range

theorem trivial_valid (m : ℕ) :
    ∀ r ∈ Partition.trivial m, r < m := by
  intro r hr
  rw [Partition.trivial, List.mem_range] at hr
  exact hr

theorem trivial_complete (m : ℕ) :
    ∀ r : ℕ, r < m → r ∈ Partition.trivial m := by
  intro r hr
  rw [Partition.trivial, List.mem_range]
  exact hr

/-- The trivial partition is a valid partition (requires `0 < m`). -/
def trivial_partition (m : ℕ) (hm : 0 < m) : Partition m where
  residues := Partition.trivial m
  disjoint := Partition.trivial_nodup m
  complete := Partition.trivial_complete m
  valid := Partition.trivial_valid m
  positive := hm

end Partition

end CollatzResearch
