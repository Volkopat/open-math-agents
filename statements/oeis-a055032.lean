import Mathlib

/-!
# A055032: Denominator of (Sum(m^(n-1),m=1..n-1)+1)/n.

Source: https://oeis.org/A055032
Credit: @azmiozgen

Conjecture (from the entry; Giuga's conjecture): this is 1 iff n is 1 or a prime.

Formalization notes:
* a(n), offset 1, is the denominator (in lowest terms) of the rational number
  (1^(n-1) + 2^(n-1) + ... + (n-1)^(n-1) + 1) / n.
* The conjecture is stated for every n ≥ 1.
* Controls: a(1..12) = 1, 1, 1, 4, 1, 3, 1, 8, 9, 5, 1, 12, as in the entry.
-/

namespace OMA.S_oeis_a055032

/-- A055032(n): the denominator of `(∑_{m=1}^{n-1} m^(n-1) + 1) / n`. -/
def a (n : ℕ) : ℕ := ((∑ m ∈ Finset.Icc 1 (n - 1), (m : ℚ) ^ (n - 1) + 1) / n).den

/-- Giuga's conjecture in the form of the entry: `a(n) = 1` iff `n` is `1` or a prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n = 1 ↔ n = 1 ∨ n.Prime) := by
  sorry

end OMA.S_oeis_a055032
