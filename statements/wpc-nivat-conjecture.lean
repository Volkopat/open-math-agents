import Mathlib

/-!
# Nivat's conjecture

Source: https://en.wikipedia.org/wiki/Nivat%27s_conjecture
Credit: @mgv27

If a colouring of ℤ² with finitely many colours has, for some m and n, at most mn distinct
m×n rectangular patterns, then it is periodic. Proved with mn replaced by mn/2 (Cyr–Kra) and
asymptotically by Kari–Szabados; the exact statement is open.

Formalization notes:
* A colouring is a map `c : ℤ × ℤ → α` with `α` a finite type (in `Type`).
* The `m × n` pattern at `z` is the map `(a, b) ↦ c (z + (a, b))` on `Fin m × Fin n`;
  the complexity is the number of distinct such patterns (a finite number since `α` is finite).
* `m, n ≥ 1`. Periodic means there is a nonzero `p ∈ ℤ²` with `c (z + p) = c z` for all `z`.
-/

namespace OMA.S_wpc_nivat_conjecture

/-- The `m × n` rectangular pattern of `c` with lower-left corner `z`. -/
def pattern {α : Type*} (c : ℤ × ℤ → α) (m n : ℕ) (z : ℤ × ℤ) : Fin m × Fin n → α :=
  fun a => c (z + (((a.1 : ℕ) : ℤ), ((a.2 : ℕ) : ℤ)))

/-- The number of distinct `m × n` patterns occurring in `c`. -/
noncomputable def complexity {α : Type*} (c : ℤ × ℤ → α) (m n : ℕ) : ℕ :=
  (Set.range (pattern c m n)).ncard

/-- `c` is periodic: it has a nonzero period vector. -/
def IsPeriodic {α : Type*} (c : ℤ × ℤ → α) : Prop :=
  ∃ p : ℤ × ℤ, p ≠ 0 ∧ ∀ z, c (z + p) = c z

/-- Nivat's conjecture. -/
theorem main : ∀ (α : Type) [Finite α] (c : ℤ × ℤ → α) (m n : ℕ), 1 ≤ m → 1 ≤ n →
    complexity c m n ≤ m * n → IsPeriodic c := by
  sorry

end OMA.S_wpc_nivat_conjecture
