import Mathlib

/-!
# Szekeres's sequence and two increasing ternary sequences

A003278 consists of one plus the increasing sequence of sums of distinct
powers of three. The predicate Digits01 generates those sums by appending
a ternary 0 or 1. A191107 is defined by its own two affine generation
rules below. For A055246, a surviving Cantor interval with left numerator
p has children with left numerators 3p and 3p+2, and the middle third
removed from that interval has left numerator 3p+1.

All three OEIS sequences begin at index one, represented here by i=0.
The two denominator-cleared equalities express the conjectured exact
quotients (A191107(n)+2)/3 and (A055246(n)+5)/6.
Sources: https://oeis.org/A003278, https://oeis.org/A191107,
https://oeis.org/A055246
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a003278

inductive Digits01 : ℕ → Prop where
  | zero : Digits01 0
  | append0 {x} : Digits01 x → Digits01 (3*x)
  | append1 {x} : Digits01 x → Digits01 (3*x+1)

inductive Generated : ℕ → Prop where
  | seed : Generated 1
  | low {x} : Generated x → Generated (3*x-2)
  | high {x} : Generated x → Generated (3*x+1)

inductive CantorParent : ℕ → Prop where
  | root : CantorParent 0
  | left {p} : CantorParent p → CantorParent (3*p)
  | right {p} : CantorParent p → CantorParent (3*p+2)

def gap (x : ℕ) : Prop := ∃ p, CantorParent p ∧ x = 3*p+1

theorem main : ∀ i : ℕ, let s := Nat.nth Digits01 i + 1
  Nat.nth Generated i + 2 = 3*s ∧ Nat.nth gap i + 5 = 6*s := by
  sorry

end OMA.S_oeis_a003278
