import Mathlib

/-!
# A239657: Number of odd divisors m of n such that there is a divisor d of n with d < m < 2*d.

Source: https://oeis.org/A239657
Credit: @esracummings31-blip

Conjecture (Omar E. Pol, Nov 22 2025): a(n) is the number of partitions of n into consecutive
parts minus the number of 2-dense sublists of divisors of n.

Conventions.
* A partition of `n` into consecutive parts is `a + (a+1) + ... + (a+k-1) = n` with `a ≥ 1`,
  `k ≥ 1`; it is recorded as the pair `(a, k)` (both necessarily `≤ n`).
* The 2-dense sublists of divisors of `n`: list the divisors of `n` in increasing order and cut
  between adjacent divisors `d < e` exactly when `e > 2*d` (maximal sublists whose adjacent
  terms differ by a factor `≤ 2`).
* Stated for every `n ≥ 1`.
-/

namespace OMA.S_oeis_a239657

/-- A239657(n). -/
def A239657 (n : ℕ) : ℕ :=
  (n.divisors.filter (fun m => Odd m ∧ ∃ d ∈ n.divisors, d < m ∧ m < 2 * d)).card

/-- Partitions of `n` into consecutive parts, as pairs (smallest part, number of parts). -/
def consecParts (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun p => ∑ i ∈ Finset.range p.2, (p.1 + i) = n)

/-- The 2-dense sublists of the divisors of `n`. -/
def blocks (n : ℕ) : List (List ℕ) :=
  (n.divisors.sort (· ≤ ·)).splitBy (fun d e => decide (e ≤ 2 * d))

theorem main : ∀ n : ℕ, 1 ≤ n → A239657 n = (consecParts n).card - (blocks n).length := by
  sorry

end OMA.S_oeis_a239657
