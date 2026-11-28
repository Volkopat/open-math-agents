import Mathlib

/-!
# MathOverflow 18548

Source: https://mathoverflow.net/questions/18548
-/

namespace OMA.S_mo_18548

def IsSimplicialFaceFamily {V : Type} (F : Set (Finset V)) : Prop :=
  ∅ ∈ F ∧ ∀ ⦃s t : Finset V⦄, t ∈ F → s ⊆ t → s ∈ F

def FaceOrderLattice {V : Type} (F : Set (Finset V)) : Prop :=
  ∃ L : Lattice F, ∀ s t : F, @LE.le F L.toLE s t ↔ s.val ⊆ t.val

def faceOrderWithTop {V : Type} {F : Set (Finset V)} : Option F → Option F → Prop
  | _,none => True
  | none,some _ => False
  | some s,some t => s.val ⊆ t.val

def AugmentedFaceDistributive {V : Type} (F : Set (Finset V)) : Prop :=
  ∃ L : DistribLattice (Option F),
    ∀ s t : Option F, @LE.le _ L.toLE s t ↔ faceOrderWithTop s t

theorem main : ∃ F : Set (Finset (Fin 3)), IsSimplicialFaceFamily F ∧
      (∀ i : Fin 3, {i} ∈ F) ∧ ¬ FaceOrderLattice F ∧ ¬ AugmentedFaceDistributive F := by
  sorry

end OMA.S_mo_18548
