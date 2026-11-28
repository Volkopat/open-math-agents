import Mathlib

/-!
# Doubly stochastic matrices whose character transforms are doubly stochastic

Source: David Roberson, https://mathoverflow.net/questions/443664 (CC BY-SA 4.0).
Credit: @connoranderson.

Rows of the character table are indexed by group elements, columns by
characters. The test on the original group is positive semidefiniteness of
the translation-invariant matrix on pairs of elements, together with the
prescribed row and column at the identity. Among permutation matrices the
criterion selects exactly the additive automorphisms.
-/

namespace OMA.S_mo_443664

open scoped ComplexOrder

noncomputable def dual {G : Type} [Fintype G] [AddCommGroup G] (M : Matrix G G ℂ) :
    Matrix (AddChar G ℂ) (AddChar G ℂ) ℂ := fun χ ψ =>
  (Fintype.card G : ℂ)⁻¹ * ∑ a, ∑ b, star (χ a) * M a b * ψ b

def Margins {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ) : Prop :=
  (∀ i, ∑ j, M i j = 1) ∧ ∀ j, ∑ i, M i j = 1

def Doubly {ι : Type} [Fintype ι] (M : Matrix ι ι ℂ) : Prop :=
  Margins M ∧ ∀ i j, 0 ≤ M i j

def liftMatrix {G : Type} [AddCommGroup G] (M : Matrix G G ℂ) : Matrix (G×G) (G×G) ℂ :=
  fun x y => M (x.1-y.1) (x.2-y.2)

def permMatrix {G : Type} [DecidableEq G] (σ : Equiv.Perm G) : Matrix G G ℂ :=
  fun a b => if a=σ b then 1 else 0

theorem main : ∀ {G : Type} [Fintype G] [AddCommGroup G] [DecidableEq G],
    (∀ M : Matrix G G ℂ, Doubly M → (Doubly (dual M) ↔
      ((∀ a, M a 0 = if a=0 then 1 else 0) ∧ (∀ b, M 0 b = if b=0 then 1 else 0)) ∧
      (liftMatrix M).PosSemidef)) ∧
    (∀ σ : Equiv.Perm G, Doubly (dual (permMatrix σ)) ↔ ∀ x y, σ (x+y) = σ x+σ y) := by
  sorry

end OMA.S_mo_443664
