import Mathlib.NumberTheory.PythagoreanTriples

/-!
# No primitive Pythagorean triple has three triangular entries

Source: https://oeis.org/A340462 (Frank M. Jackson)
Credit: @Alienchisel

The entries are positive integers. Primitivity is expressed by requiring
the two legs to be coprime, as in Mathlib's Pythagorean triple classification.
-/

namespace OMA.S_oeis_a340462

/-- A triangular number is of the form k(k + 1)/2 for a natural number k. -/
def IsTriangular (n : ℕ) : Prop :=
  ∃ k : ℕ, n = k * (k + 1) / 2

theorem main : ¬ ∃ a b c : ℕ,
    0 < a ∧ 0 < b ∧ 0 < c ∧
    PythagoreanTriple (a : ℤ) (b : ℤ) (c : ℤ) ∧ Nat.Coprime a b ∧
    IsTriangular a ∧ IsTriangular b ∧ IsTriangular c := by
  sorry

end OMA.S_oeis_a340462
