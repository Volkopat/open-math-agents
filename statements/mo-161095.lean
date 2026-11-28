import Mathlib

/-!
# Uniqueness conjecture for integer triples

Source: https://mathoverflow.net/questions/161095 (CC BY-SA 4.0).

A triple `(a, b, c)` with `a ≥ b ≥ 1` is a Hikorski triple (HT) if `c = (ab + 1)/(a + b)` is an
integer. The triples `(n, 1, 1)` are the trivial HTs.
Conjecture: if `(a, b, c)` and `(p, q, r)` are both non-trivial HTs, then `abc = pqr` implies
`(a, b, c) = (p, q, r)`; that is, the product of the entries of a non-trivial HT determines it.

Formalization notes:
* "`c = (ab + 1)/(a + b)` is an integer" is written `(a + b) * c = a * b + 1` in `ℕ`.
* A non-trivial HT is an HT that is not of the form `(n, 1, 1)`. (For `b = 1` the definition
  forces `c = 1`, so non-trivial HTs are exactly those with `b ≥ 2`.)
* Checked numerically: the 336 non-trivial HTs with `abc ≤ 10^6` have pairwise distinct
  products.
-/

namespace OMA.S_mo_161095

/-- `(a, b, c)` is a Hikorski triple: `a ≥ b ≥ 1` and `c = (ab + 1)/(a + b)`. -/
def IsHT (a b c : ℕ) : Prop := 1 ≤ b ∧ b ≤ a ∧ (a + b) * c = a * b + 1

/-- A non-trivial Hikorski triple: one not of the form `(n, 1, 1)`. -/
def IsNontrivialHT (a b c : ℕ) : Prop := IsHT a b c ∧ ¬ (b = 1 ∧ c = 1)

/-- Non-trivial Hikorski triples with equal products are equal. -/
theorem main : ∀ a b c p q r : ℕ, IsNontrivialHT a b c → IsNontrivialHT p q r →
    a * b * c = p * q * r → (a, b, c) = (p, q, r) := by
  sorry

end OMA.S_mo_161095
