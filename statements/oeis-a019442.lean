import Mathlib

/-!
# A019442: orders of Hadamard matrices

Source: https://oeis.org/A019442
Credit: @jagraj28

A019442 lists the numbers `m` such that a Hadamard matrix of order `m` exists:
1, 2, 4, 8, 12, 16, ... The entry records two conjectures:
1. the sequence consists of 1, 2 and all multiples of 4 (the Hadamard conjecture);
2. (Jean-François Alcover, 2016) its generating function is `(2x^3 + x^2 + 1)/(x - 1)^2`.

`main` is the conjunction of the two.

Conventions:
* A Hadamard matrix of order `m` is an `m × m` matrix with entries in `{1, -1}` such that
  `H * Hᵀ = m * I`. The sequence lists positive orders only, so `m = 0` (the empty matrix) is
  excluded.
* The generating function has constant term 1 = a(1), so it is `Σ_{n ≥ 0} a(n+1) x^n`, where
  `a(n+1)` is the `n`-th element (from 0) of the set in increasing order, `Nat.nth S n`.
  Conjecture 2 is stated without division: this series times `(x - 1)^2` is `2x^3 + x^2 + 1`.
-/

namespace OMA.S_oeis_a019442

/-- There is a Hadamard matrix of order `m`: an `m × m` matrix with entries `1` or `-1` such
that `H * Hᵀ = m • 1`. -/
def HasHadamard (m : ℕ) : Prop :=
  ∃ H : Matrix (Fin m) (Fin m) ℤ, (∀ i j, H i j = 1 ∨ H i j = -1) ∧
    H * H.transpose = (m : ℤ) • (1 : Matrix (Fin m) (Fin m) ℤ)

/-- The terms of OEIS A019442: the positive orders of Hadamard matrices. -/
def S : Set ℕ := {m | 0 < m ∧ HasHadamard m}

/-- Conjectures 1 and 2 of OEIS A019442. -/
theorem main :
    S = {m | m = 1 ∨ m = 2 ∨ (0 < m ∧ 4 ∣ m)} ∧
    PowerSeries.mk (fun n => (Nat.nth (· ∈ S) n : ℤ)) * (PowerSeries.X - 1) ^ 2 =
      2 * PowerSeries.X ^ 3 + PowerSeries.X ^ 2 + 1 := by
  sorry

end OMA.S_oeis_a019442
