import Mathlib

/-!
# A371652: a(n) = (Sum_{k=0..n-1}(145*k^2+104*k+18)*C(2k,k)*C(3k,k)^2/(2k+1))/(6n*(2n-1)*C(3n,n)).

Source: https://oeis.org/A371652
Credit: @azmiozgen

Conjecture (from the entry, motivated by Conjecture 4.13 of Z.-W. Sun (2023)): all the terms are
integers.

Formalization notes:
* a(n), offset 1, is defined in ℚ by the formula in the name; the conjecture is that it is an
  integer for every n ≥ 1.
* Controls (computed): a(1..8) = 1, 3, 29, 399, 6514, 117711, 2275251, 46139015, as in the entry;
  a(n) is an integer for n < 60.
-/

namespace OMA.S_oeis_a371652

/-- A371652(n), in `ℚ`. -/
noncomputable def a (n : ℕ) : ℚ :=
  (∑ k ∈ Finset.range n, ((145 * k ^ 2 + 104 * k + 18) * (2 * k).choose k * ((3 * k).choose k) ^ 2 : ℕ) /
      (2 * k + 1 : ℚ)) / (6 * n * (2 * n - 1) * ((3 * n).choose n : ℚ))

/-- All terms are integers. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ z : ℤ, a n = z := by
  sorry

end OMA.S_oeis_a371652
