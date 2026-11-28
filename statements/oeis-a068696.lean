import Mathlib

/-!
# A068696: Number of primes that are a concatenation nk of n and k for values of k from 1 to n

Source: https://oeis.org/A068696
Credit: @niclorusso

Conjecture (in the comments of A068696): a(2) is the only 0 in this sequence.

Conventions:
* The sequence has offset 1: a(n) is the number of k with 1 <= k <= n such that the decimal
  concatenation of n and k is prime.
* The decimal concatenation of n and k (k >= 1) is n * 10^(number of decimal digits of k) + k,
  where the number of digits of k is `(Nat.digits 10 k).length`.
* "a(2) is the only 0" is stated as: for every n >= 1, a(n) = 0 if and only if n = 2
  (a(2) = 0 because 21 and 22 are composite).
-/

namespace OMA.S_oeis_a068696

/-- The decimal concatenation of `n` and `k`: the digits of `n` followed by the digits of `k`. -/
def concat (n k : ℕ) : ℕ := n * 10 ^ (Nat.digits 10 k).length + k

/-- A068696: the number of `k` in `1..n` such that the concatenation `nk` is prime. -/
def a (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter (fun k => (concat n k).Prime)).card

/-- The conjecture on A068696: for `n >= 1`, `a n = 0` if and only if `n = 2`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n = 0 ↔ n = 2) := by
  sorry

end OMA.S_oeis_a068696
