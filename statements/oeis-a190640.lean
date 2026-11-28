import Mathlib

/-!
# Ternary digits and the Cantor gap numerators (OEIS A190640)

A190640 lists in increasing order the positive integers with final ternary
digit 2 and no ternary digit 1. In the middle-third construction a parent
interval with left endpoint `p / 3^k` has surviving children whose left
numerators are `3p` and `3p+2`. The gap removed from this parent therefore
has left numerator `3p+1`. These distinct gap numerators, in increasing
order, give A055246. Leading zeroes allow every finite stage to occur as
the initial segment at later stages. Both OEIS entries start at index one.

Michel Marcus conjectured their termwise difference is one (August 2016).
Sources: https://oeis.org/A190640 and https://oeis.org/A055246.
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a190640

def digitTerm (m : ℕ) : Prop :=
  m % 3 = 2 ∧ ∀ d ∈ Nat.digits 3 m, d = 0 ∨ d = 2

inductive CantorParent : ℕ → Prop where
  | root : CantorParent 0
  | left {p : ℕ} : CantorParent p → CantorParent (3 * p)
  | right {p : ℕ} : CantorParent p → CantorParent (3 * p + 2)

def gapNumerator (m : ℕ) : Prop := ∃ p, CantorParent p ∧ m = 3 * p + 1

/-- The zero-based index `i` here represents index `i+1` of both entries. -/
theorem main : ∀ i : ℕ, Nat.nth digitTerm i = Nat.nth gapNumerator i + 1 := by
  sorry

end OMA.S_oeis_a190640
