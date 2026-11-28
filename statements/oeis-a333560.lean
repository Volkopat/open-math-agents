import Mathlib

/-!
# A333560: Square array read by antidiagonals: T(n,k) = Sum_{j = 0..n*k} binomial(n+j-1,j)*2^j; n,k >= 0.

Source: https://oeis.org/A333560
Credit: @azmiozgen

Conjecture (Peter Bala, from the entry): each column sequence satisfies the supercongruences
T(n*p^j, k) == T(n*p^(j-1), k) (mod p^(3*j)) for prime p >= 5 and positive integers n and j.

Formalization notes:
* T(n, k) is the sum in the name, computed in ℤ; in n + j - 1 the subtraction is in ℕ, which only
  matters at n = 0 (giving T(0, k) = 1, as in the entry).
* The conjecture is stated for every column k ≥ 0.
* Controls (computed): rows n = 0..3, columns k = 0..4 are 1,1,1,1,1 / 1,3,7,15,31 /
  1,17,129,769,4097 / 1,111,2815,47103,647167, matching the entry's antidiagonals
  1, 1,1, 1,3,1, 1,17,7,1, 1,111,129,15,1; the congruence holds for p = 5, 7, n = 1, 2, k = 1, 3
  with j = 1.
-/

namespace OMA.S_oeis_a333560

/-- `T(n, k) = ∑_{j=0}^{nk} C(n+j-1, j) 2^j`. -/
def T (n k : ℕ) : ℤ := ∑ j ∈ Finset.range (n * k + 1), ((n + j - 1).choose j * 2 ^ j : ℕ)

/-- The column supercongruences. -/
theorem main :
    ∀ k p : ℕ, p.Prime → 5 ≤ p → ∀ n j : ℕ, 1 ≤ n → 1 ≤ j →
      ((p : ℤ) ^ (3 * j) ∣ T (n * p ^ j) k - T (n * p ^ (j - 1)) k) := by
  sorry

end OMA.S_oeis_a333560
