import Mathlib

/-!
# A020481: Least p with p, q both prime, p+q = 2n.

Source: https://oeis.org/A020481
Credit: @EmircanEsen

Conjecture (Jon Perry, Apr 29 2014): a(n) ~ O(n^1/2).

Formalization notes:
* "`a(n) ~ O(n^1/2)`" is read as the big-O bound `a(n) = O(√n)` as `n → ∞`.
* `a n` is the least prime `p` such that `2n - p` is also prime (offset 2: `a 2 = 2`,
  `a 3 = 3`, …). Natural subtraction is harmless: for `p > 2n` it gives `0`, which is not prime.
* If Goldbach's conjecture failed at some `n`, the OEIS term would not exist while `a n` is
  `sInf ∅ = 0` here. That only lowers `a n`, and the conjecture is an upper bound, so it neither
  helps nor hurts.
* Checked numerically: `a(n) / √n ≤ 3.28` for `2 ≤ n < 500000`, the maximum being at `n = 496`.
-/

namespace OMA.S_oeis_a020481

/-- A020481: the least prime `p` such that `2n - p` is prime. -/
noncomputable def a (n : ℕ) : ℕ := sInf {p : ℕ | p.Prime ∧ (2 * n - p).Prime}

/-- `a(n) = O(√n)`. -/
theorem main :
    Asymptotics.IsBigO Filter.atTop (fun n : ℕ => (a n : ℝ)) (fun n : ℕ => Real.sqrt n) := by
  sorry

end OMA.S_oeis_a020481
