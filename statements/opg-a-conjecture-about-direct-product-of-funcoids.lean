import Mathlib.Order.Filter.Ultrafilter.Basic

/-!
# Porton's conjecture about the direct product of funcoids

Source: https://www.openproblemgarden.org/op/a_conjecture_about_direct_product_of_funcoids
Also Conjecture 4 of https://math.portonvictor.org/binaries/agt-open-problems.pdf

We use the filter presentation of ordinary funcoids, including the improper filter.
Filters have Mathlib's reverse-inclusion order. The destination of the proposed
pointfree funcoid is the ordered set of funcoids between the two destinations.
-/

namespace OMA.S_opg_a_conjecture_about_direct_product_of_funcoids

/-- Two filters overlap if their meet is proper. -/
def Overlap {A : Type*} (x y : Filter A) : Prop := (x ⊓ y).NeBot

/-- A pointfree funcoid has conjugate forward and reverse operations for overlap. -/
structure Pointfree (X Y : Type*) (overX : X → X → Prop) (overY : Y → Y → Prop) where
  forward : X → Y
  reverse : Y → X
  compatible (x : X) (y : Y) : overY (forward x) y ↔ overX x (reverse y)

abbrev Funcoid (A B : Type*) := Pointfree (Filter A) (Filter B) Overlap Overlap

/-- The order on ordinary funcoids compares their forward operations pointwise. -/
def Below {A B : Type*} (f g : Funcoid A B) : Prop := ∀ x, f.forward x ≤ g.forward x

/-- Overlap in the funcoid lattice means admitting a nonzero common lower bound. -/
def MeetNonzero {A B : Type*} (f g : Funcoid A B) : Prop :=
  ∃ k : Funcoid A B, Below k f ∧ Below k g ∧ ∃ x, (k.forward x).NeBot

/-- Entire definedness means the identity lies below the composite of the forward
operation followed by the reverse operation. -/
def Entire {A B : Type*} (f : Funcoid A B) : Prop := ∀ x, x ≤ f.reverse (f.forward x)

/-- Monovalence means the composite in the opposite order lies below the identity. -/
def Monovalued {A B : Type*} (f : Funcoid A B) : Prop := ∀ y, f.forward (f.reverse y) ≤ y

/-- The funcoidal product of two filters, acting on a filter in the first coordinate. -/
noncomputable def productAction {B C : Type*} (b : Filter B) (c : Filter C)
    (x : Filter B) : Filter C := by
  classical
  exact if Overlap x b then c else ⊥

/-- Porton's atomwise direct-product formula. The equivalence with every upper
bound expresses the join in the funcoid order. Its indexing atoms are precisely
the ultrafilters below the source filter. -/
theorem main :
    ∀ (A B C : Type*) (f : Funcoid A B) (g : Funcoid A C),
      Monovalued f → Entire f → Monovalued g → Entire g →
      ∃ d : Pointfree (Filter A) (Funcoid B C) Overlap MeetNonzero,
        ∀ (x : Filter A) (r : Funcoid B C), Below (d.forward x) r ↔
          ∀ u : Ultrafilter A, (u : Filter A) ≤ x →
            ∀ y : Filter B, productAction (f.forward u) (g.forward u) y ≤ r.forward y := by
  sorry

end OMA.S_opg_a_conjecture_about_direct_product_of_funcoids
