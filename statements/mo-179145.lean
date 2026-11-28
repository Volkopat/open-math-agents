import Mathlib

/-!
# MathOverflow 179145

Source: https://mathoverflow.net/questions/179145
-/

namespace OMA.S_mo_179145

/-- The two incidence rows for x and y share a hyperedge column. -/
def Cooccur {V : Type} (H : Set (Set V)) (x y : V) : Prop :=
  ∃ E ∈ H, x ∈ E ∧ y ∈ E

def Covered {V : Type} (H : Set (Set V)) (S : Set V) : Prop :=
  S.Pairwise (Cooccur H)

def Incomparable {V : Type} (H : Set (Set V)) : Prop :=
  ∀ E ∈ H, ∀ F ∈ H, E ⊆ F → E = F

def Conformal {V : Type} (H : Set (Set V)) : Prop :=
  ∀ S : Set V, Covered H S → ∃ E ∈ H, S ⊆ E

def Independent {V : Type} (G : SimpleGraph V) (S : Set V) : Prop :=
  S.Pairwise (fun x y => ¬ G.Adj x y)

def MaximalIndependent {V : Type} (G : SimpleGraph V) (S : Set V) : Prop :=
  Independent G S ∧ ∀ T, Independent G T → S ⊆ T → S = T

theorem main : ∀ (V : Type) (H : Set (Set V)),
    (∃ G : SimpleGraph V, ∀ S : Set V, S ∈ H ↔ MaximalIndependent G S) ↔
      Incomparable H ∧ Conformal H := by
  sorry

end OMA.S_mo_179145
