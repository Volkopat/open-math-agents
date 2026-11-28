import Mathlib

/-!
# A337247: a(n) = (Sum_{k=0..n-1} (-1)^k * (4k+1) * 160^(n-1-k) * C(2k,k) * Sum_{j=0..k} C(k,j) * C(k+2j,2j) * C(2j,j) * (-20)^(k-j)) / (n * C(2n,n)).

Source: https://oeis.org/A337247
Credit: @azmiozgen

Conjecture 1 (Zhi-Wei Sun, from the entry): a(n) is a positive integer for each n > 1. Moreover, a(n) is
odd if and only if n = 2^k + 1 for some nonnegative integer k. (Conjecture 2, a series identity, is not
stated here.)

Formalization notes:
* a(n), offset 2, is defined in ℚ by the formula in the name.
* Controls (computed): a(2..4) = 25, 809, 23020, as in the entry; for 2 ≤ n < 60 every a(n) is a positive
  integer, odd exactly at n = 2, 3, 5, 9, 17, 33.
-/

namespace OMA.S_oeis_a337247

/-- The inner sum `∑_{j=0}^{k} C(k,j) C(k+2j,2j) C(2j,j) (-20)^(k-j)`. -/
def inner (k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (k + 1), ((k.choose j * (k + 2 * j).choose (2 * j) * (2 * j).choose j : ℕ) : ℤ) *
    (-20 : ℤ) ^ (k - j)

/-- A337247(n), in `ℚ`. -/
noncomputable def a (n : ℕ) : ℚ :=
  (∑ k ∈ Finset.range n, ((-1 : ℤ) ^ k * (4 * k + 1) * 160 ^ (n - 1 - k) * ((2 * k).choose k : ℤ) *
    inner k : ℤ)) / (n * ((2 * n).choose n : ℚ))

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    ∀ n : ℕ, 1 < n → ∃ m : ℕ, 0 < m ∧ a n = m ∧ (Odd m ↔ ∃ k : ℕ, n = 2 ^ k + 1) := by
  sorry

end OMA.S_oeis_a337247
