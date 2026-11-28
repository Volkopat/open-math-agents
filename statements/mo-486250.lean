import Mathlib

namespace OMA.S_mo_486250

abbrev GroupHilbert (G : Type) := ↥(lp (fun _ : G => ℂ) 2)

/-- The group von Neumann algebra as the commutant of right translations. -/
noncomputable def groupVonNeumann (G : Type) [Group G] :
    StarSubalgebra ℂ (GroupHilbert G →L[ℂ] GroupHilbert G) :=
  StarSubalgebra.centralizer ℂ
    {T | ∃ g : G, ∀ (f : GroupHilbert G) (x : G), T f x = f (x * g)}

/-- A finite generating set whose Cayley metric satisfies the four-point
criterion for Gromov hyperbolicity. -/
def wordHyperbolic (G : Type) [Group G] : Prop :=
  ∃ generators : Finset G,
    Subgroup.closure (generators : Set G) = ⊤ ∧
      let dist := (SimpleGraph.mulCayley (generators : Set G)).dist
      ∃ delta : ℕ, ∀ a b c d : G,
        dist a b + dist c d ≤ max (dist a c + dist b d) (dist a d + dist b c) + delta

theorem main :
    ∃ (G H : Type) (groupG : Group G) (groupH : Group H),
      letI := groupG
      letI := groupH
      wordHyperbolic G ∧ wordHyperbolic H ∧
        (∀ g : G, ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1) ∧
        (∀ h : H, ∀ k : ℕ, 0 < k → h ^ k = 1 → h = 1) ∧
        ¬ Nonempty (G ≃* H) ∧
        Nonempty (↥(groupVonNeumann G) ≃⋆ₐ[ℂ] ↥(groupVonNeumann H)) := by
  sorry

end OMA.S_mo_486250
