import Mathlib

/-!
# A401249: Minimum number of odd terms in a 2-dense sublist of divisors of n.

Source: https://oeis.org/A401249
Credit: @esracummings31-blip

Conjecture 1 (Omar E. Pol, Oct 28 2026): a(n) = A384225(n,1).

Only Conjecture 1 is stated here (the other conjectures refer to the symmetric representation
of sigma, A237271 / A279387, and are not addressed).

Conventions.
* The 2-dense sublists of divisors of `n`: list the divisors of `n` in increasing order and cut
  between adjacent divisors `d < e` exactly when `e > 2*d` (maximal sublists whose adjacent
  terms differ by a factor `≤ 2`).
* A384225(n,k) is the number of odd terms in the k-th 2-dense sublist (k ≥ 1; `0` if out of
  range).
* A401249(n) is the minimum of these counts over all 2-dense sublists (for `n ≥ 1` there is at
  least one sublist).
* Stated for every `n ≥ 1`.
-/

namespace OMA.S_oeis_a401249

/-- The 2-dense sublists of the divisors of `n`. -/
def blocks (n : ℕ) : List (List ℕ) :=
  (n.divisors.sort (· ≤ ·)).splitBy (fun d e => decide (e ≤ 2 * d))

/-- A384225(n,k): number of odd terms in the k-th 2-dense sublist of divisors of `n` (k ≥ 1). -/
def A384225 (n k : ℕ) : ℕ := (((blocks n)[k - 1]?).getD []).countP (fun d => decide (Odd d))

/-- A401249(n): minimum number of odd terms in a 2-dense sublist of divisors of `n`. -/
def A401249 (n : ℕ) : ℕ :=
  (((blocks n).map (fun B => B.countP (fun d => decide (Odd d)))).min?).getD 0

theorem main : ∀ n : ℕ, 1 ≤ n → A401249 n = A384225 n 1 := by
  sorry

end OMA.S_oeis_a401249
