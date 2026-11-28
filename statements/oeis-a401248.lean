import Mathlib

/-!
# A401248: Minimum number of terms in a 2-dense sublist of divisors of n.

Source: https://oeis.org/A401248
Credit: @esracummings31-blip

Conjecture 1 (Omar E. Pol, Oct 28 2026): a(n) = A384222(n,1).

Only Conjecture 1 is stated here (Conjecture 2 refers to A237271, the number of parts of the
symmetric representation of sigma, and is not addressed).

Conventions.
* The 2-dense sublists of divisors of `n`: list the divisors of `n` in increasing order and cut
  between adjacent divisors `d < e` exactly when `e > 2*d` (maximal sublists whose adjacent
  terms differ by a factor `≤ 2`).
* A384222(n,k) is the length of the k-th 2-dense sublist (k ≥ 1; `0` if out of range).
* A401248(n) is the minimum of these lengths (for `n ≥ 1` there is at least one sublist).
* Stated for every `n ≥ 1`.
-/

namespace OMA.S_oeis_a401248

/-- The 2-dense sublists of the divisors of `n`. -/
def blocks (n : ℕ) : List (List ℕ) :=
  (n.divisors.sort (· ≤ ·)).splitBy (fun d e => decide (e ≤ 2 * d))

/-- A384222(n,k): length of the k-th 2-dense sublist of divisors of `n` (k ≥ 1). -/
def A384222 (n k : ℕ) : ℕ := (((blocks n)[k - 1]?).getD []).length

/-- A401248(n): minimum length of a 2-dense sublist of divisors of `n`. -/
def A401248 (n : ℕ) : ℕ := (((blocks n).map List.length).min?).getD 0

theorem main : ∀ n : ℕ, 1 ≤ n → A401248 n = A384222 n 1 := by
  sorry

end OMA.S_oeis_a401248
