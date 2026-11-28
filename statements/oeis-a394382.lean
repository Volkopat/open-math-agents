import Mathlib

/-!
# Decimal digits of prime roots whose squares reverse to distinct prime squares

Source: https://oeis.org/A394382
Conjectures by Chai Wah Wu. Translation by @laurilehtinen.
-/

namespace OMA.S_oeis_a394382

def reverseDecimal (n : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 n).reverse

/-- Membership in A394382, with both exclusions on the other prime root. -/
def IsTerm (p : ℕ) : Prop :=
  p.Prime ∧ ∃ q : ℕ, q.Prime ∧ reverseDecimal (p^2) = q^2 ∧
    q ≠ p ∧ q ≠ reverseDecimal p

/-- Mathlib stores the units digit first. -/
def outerDigitsOne (p : ℕ) : Prop :=
  (Nat.digits 10 p).getLast? = some 1 ∧ (Nat.digits 10 p).head? = some 1

def allowedDigits (p : ℕ) : Prop :=
  ∀ d ∈ Nat.digits 10 p, d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 9

theorem main :
    (∀ p : ℕ, IsTerm p → outerDigitsOne p) ∧
    (∀ p : ℕ, IsTerm p → allowedDigits p) := by
  sorry

end OMA.S_oeis_a394382
