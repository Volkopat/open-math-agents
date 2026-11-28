import Mathlib

/-!
# Are the largely composite numbers the same as the fully composite numbers?

Source: https://mathoverflow.net/questions/44865 (CC BY-SA 4.0).

Let `d(n)` be the number of divisors of `n` and `p(n)` their product. Ramanujan called `n`
largely composite if `d(n) ≥ d(m)` for all `m < n`; call `n` fully composite if `p(n) ≥ p(m)` for
all `m < n`. It is conjectured that the largely composite numbers (OEIS A067128) and the fully
composite numbers (OEIS A034287) are the same; the two sequences agree for the 105834 terms below
`10^150`. Every largely composite number is fully composite (easy); the question is the converse.

We state the conjecture that the two notions coincide.

Formalization notes:
* `n` ranges over the positive integers, and so does `m` in "for all `m < n`".
* `d n = n.divisors.card` and `p n = ∏ d ∈ n.divisors, d`.
* Checked numerically: the two sets agree up to `10^5` (75 terms).
-/

namespace OMA.S_mo_44865

/-- The number of divisors. -/
def d (n : ℕ) : ℕ := n.divisors.card

/-- The product of the divisors. -/
def p (n : ℕ) : ℕ := ∏ k ∈ n.divisors, k

/-- `n` is largely composite: `d(m) ≤ d(n)` for every positive `m < n`. -/
def IsLargelyComposite (n : ℕ) : Prop := ∀ m : ℕ, 1 ≤ m → m < n → d m ≤ d n

/-- `n` is fully composite: `p(m) ≤ p(n)` for every positive `m < n`. -/
def IsFullyComposite (n : ℕ) : Prop := ∀ m : ℕ, 1 ≤ m → m < n → p m ≤ p n

/-- The largely composite and the fully composite positive integers are the same. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (IsFullyComposite n ↔ IsLargelyComposite n) := by
  sorry

end OMA.S_mo_44865
