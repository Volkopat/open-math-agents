import Mathlib

/-!
# MathOverflow 264107

Source: https://mathoverflow.net/questions/264107
-/

namespace OMA.S_mo_264107

open Finset

def upperElements {L : Type} [Fintype L] [LE L] [DecidableRel (α := L) (· ≤ ·)] (a : L) : Finset L :=
  univ.filter fun b => a ≤ b

noncomputable def strictUpper {L : Type} [Fintype L] [LT L] (a : L) : Finset L := by
  classical
  exact univ.filter fun b => a < b

noncomputable def coatoms {L : Type} [Fintype L] [PartialOrder L] [OrderTop L] : Finset L := by
  classical
  exact univ.filter IsCoatom

noncomputable def coatomSum {L : Type} [Fintype L] [Lattice L] [OrderTop L] (a : L) : ℤ := by
  classical
  exact ∑ S ∈ (coatoms : Finset L).powerset, if S.inf id = a then (-1 : ℤ)^S.card else 0

theorem main : ∀ (L : Type) [Fintype L] [Lattice L] [BoundedOrder L],
    ∀ μ : L → ℤ, μ ⊤ = 1 →
    (∀ a : L, a ≠ ⊤ → μ a = -∑ b ∈ strictUpper a, μ b) →
    ∀ a : L, μ a = coatomSum a := by
  sorry

end OMA.S_mo_264107
