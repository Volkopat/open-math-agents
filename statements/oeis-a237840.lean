import Mathlib

/-!
# A237840: a(n) = |{0 < k <= n: the number of twin prime pairs not exceeding k*n is a square}|.

Source: https://oeis.org/A237840
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n > 0, and a(n) = 1 for no n > 159.
(ii) For every n = 1, 2, 3, ..., there is a positive integer k <= n such that the number
|{{p, 2*p+1}: both p and 2*p + 1 are primes not exceeding k*n}| is a square.

Formalization notes:
* A twin prime pair not exceeding x is a pair {p, p + 2} of primes with p + 2 ≤ x; the count is
  the number of primes p with p + 2 prime and p + 2 ≤ x. Likewise the pairs {p, 2p + 1} are counted
  by the primes p with 2p + 1 prime and 2p + 1 ≤ x.
* Controls (computed): a(1..25) = 1, 2, 2, 1, 3, 3, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 2, 1, 2, 3, 1, 3,
  4, 3, as in the entry; (i) holds for n < 120 and a(n) ≠ 1 for 159 < n < 200; (ii) holds for
  n < 120.
-/

namespace OMA.S_oeis_a237840

/-- The number of twin prime pairs `{p, p+2}` with `p + 2 ≤ x`. -/
def twinCount (x : ℕ) : ℕ := ((Finset.range (x + 1)).filter fun p => p.Prime ∧ (p + 2).Prime ∧ p + 2 ≤ x).card

/-- The number of pairs `{p, 2p+1}` of primes with `2p + 1 ≤ x`. -/
def sgCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter fun p => p.Prime ∧ (2 * p + 1).Prime ∧ 2 * p + 1 ≤ x).card

/-- A237840(n). -/
def a (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter fun k => IsSquare (twinCount (k * n))).card

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 0 < n → 0 < a n) ∧ (∀ n : ℕ, 159 < n → a n ≠ 1) ∧
      ∀ n : ℕ, 0 < n → ∃ k, 1 ≤ k ∧ k ≤ n ∧ IsSquare (sgCount (k * n)) := by
  sorry

end OMA.S_oeis_a237840
