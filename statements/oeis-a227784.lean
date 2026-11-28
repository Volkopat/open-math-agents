import Mathlib

/-!
# A227784: Least number of fourth powers which add to -1 mod n.

Source: https://oeis.org/A227784
Credit: @laurilehtinen

OEIS Foundation, CC BY-SA 4.0. The sequence starts at modulus one.
The first residue is nine in the published conjecture.
-/

namespace OMA.S_oeis_a227784

/-- The least number of fourth powers whose sum is minus one modulo `n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ x : Fin k → ZMod n, ∑ i, (x i) ^ 4 = -1}

theorem main : ∀ n : ℕ, 0 < n →
    (n % 16 = 9 → a n = 15) ∧ (n % 16 = 8 → a n = 7) ∧
    (n % 16 ≠ 9 → n % 16 ≠ 8 → a n ≤ 4) := by
  sorry

end OMA.S_oeis_a227784

