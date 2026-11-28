import Mathlib

/-!
# A384225: Irregular triangle read by rows: T(n,k) is the number of odd numbers in the k-th 2-dense sublist of divisors of n, with n >= 1, k >= 1.

Source: https://oeis.org/A384225
Credit: @esracummings31-blip

Conjecture 2 (OEIS, Omar E. Pol, Oct 13 2026): T(n,k) = A384222(n,k) / A001511(n).

This file states Conjecture 2 only. Conjecture 1 ("this is a duplicate of A280940", about
subparts of the symmetric representation of sigma(n)) is not stated here.

Conventions.
* The 2-dense sublists of divisors of `n`: list the divisors of `n` in increasing order and cut
  between adjacent divisors `d < e` exactly when `e > 2*d`; the pieces are the maximal
  sublists whose adjacent terms differ by a factor `≤ 2` (k is 0-indexed here, OEIS uses k ≥ 1).
* A384222(n,k) is the length of the k-th 2-dense sublist.
* A001511(n) is the 2-adic valuation of `2n`, i.e. `n.factorization 2 + 1`.
* `/` is exact division here (the conjecture asserts the quotient), so we state it with `/` on
  naturals as in the source.
-/

namespace OMA.S_oeis_a384225

/-- The 2-dense sublists of the divisors of `n`. -/
def blocks (n : ℕ) : List (List ℕ) :=
  (n.divisors.sort (· ≤ ·)).splitBy (fun d e => decide (e ≤ 2 * d))

/-- A384225(n,k): number of odd terms in the k-th 2-dense sublist. -/
def T (n k : ℕ) : ℕ := (((blocks n)[k]?).getD []).countP (fun d => decide (Odd d))

/-- A384222(n,k): length of the k-th 2-dense sublist. -/
def A384222 (n k : ℕ) : ℕ := (((blocks n)[k]?).getD []).length

/-- A001511(n) = 2-adic valuation of 2n. -/
def A001511 (n : ℕ) : ℕ := n.factorization 2 + 1

theorem main : ∀ n : ℕ, 1 ≤ n → ∀ k < (blocks n).length, T n k = A384222 n k / A001511 n := by
  sorry

end OMA.S_oeis_a384225
