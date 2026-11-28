import Mathlib

/-!
# Rectangular box plane partitions and their Gauss congruences

Source: https://oeis.org/A352657

The two conjectures concern the number of plane partitions in an
n by n by 3n box. The product below is MacMahon's formula, with the
height product telescoped. Divisibility of the difference of the two
integer counts is expressed by an integer witness in the rationals.
-/

namespace OMA.S_oeis_a352657

/-- Number of plane partitions fitting in the n by n by 3n box. -/
def a (n : ℕ) : ℚ :=
  ∏ i ∈ Finset.Icc 1 n, ∏ j ∈ Finset.Icc 1 n,
    ((3*n+i+j-1:ℕ):ℚ) / ((i+j-1:ℕ):ℚ)

/-- The Gauss congruence and its fourth-order companion. -/
theorem main :
    (∀ p n r : ℕ, p.Prime → 0 < n → 0 < r →
      ∃ m : ℤ, a (n*p^r) - a (n*p^(r-1)) = (p:ℚ)^r*m) ∧
    (∀ p n r : ℕ, p.Prime → 0 < n → 0 < r →
      ∃ m : ℤ, a (n*p^r) - a (n*p^(r-1))^p = (p:ℚ)^(4*r)*m) := by
  sorry

end OMA.S_oeis_a352657
