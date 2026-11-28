import Mathlib

/-!
# A351856: Number of nonnegative integer solutions to 2*n = x_1 + x_2 + ... + x_n + 2*y_1 + 2*y_2 + ... + 2*y_n.

Source: https://oeis.org/A351856
Credit: @azmiozgen

Conjecture (formula section): the supercongruences a(n*p^k) == a(n*p^(k-1)) (mod p^(3*k)) hold
for all primes p >= 5 and positive integers n and k.

Formalization notes:
* A solution is a pair of n-tuples (x, y) of natural numbers with Sum x + 2 Sum y = 2n. Grouping by
  j = Sum y (so Sum x = 2n - 2j), a(n) = Sum_{j=0..n} #{x : Sum x = 2n - 2j} * #{y : Sum y = j},
  counted with Mathlib's `Finset.Nat.antidiagonalTuple n m` (the n-tuples with sum m).
* The congruence is stated in ℤ as divisibility of the difference by p^(3k).
* Controls (computed): a(1..7) = 2, 14, 119, 1086, 10252, 98735, 963832, as in the entry; the
  congruence holds for p = 5, 7 and n = 1, 2 with k = 1.
-/

namespace OMA.S_oeis_a351856

/-- A351856(n): the number of `(x, y) ∈ ℕⁿ × ℕⁿ` with `∑ x + 2 ∑ y = 2n`. -/
def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1),
    ((Finset.Nat.antidiagonalTuple n (2 * n - 2 * j)).card *
      (Finset.Nat.antidiagonalTuple n j).card : ℕ)

/-- The supercongruences `a(n p^k) ≡ a(n p^(k-1)) (mod p^(3k))` for primes `p ≥ 5`. -/
theorem main :
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
      ((p : ℤ) ^ (3 * k) ∣ a (n * p ^ k) - a (n * p ^ (k - 1))) := by
  sorry

end OMA.S_oeis_a351856
