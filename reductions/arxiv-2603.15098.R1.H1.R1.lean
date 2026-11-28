import OMAReductions.R_arxiv_2603_15098_R1
import Mathlib

/-! Marked ends are identified on a compact exhaustion of a single conformal image.
Adapted from the assigned mixed limit and target contours of openai/math,
Apache-2.0, commit 3344da59991ed94f9ba711217b29c1d760badfa6. -/
namespace OMA.R_arxiv_2603_15098_R1_H1_R1
open Set OMA.S_arxiv_2603_15098
open scoped OnePoint

/-- The marked sets are intersections of ends of the *core images*, not
components of the unknown final complement. -/
def H1 : Prop :=
  ∀ U : Set Sphere, IsOpen U → IsConnected U → ∞ ∈ U →
    ∃ (f : Sphere → Sphere) (K : ℕ → Set Sphere) (M : Set Sphere),
      IsConformalEquivalence f U (f '' U) ∧ IsOpen (f '' U) ∧
      (∀ n, IsCompact (K n)) ∧ (∀ n, K n ⊆ interior (K (n+1))) ∧
      (⋃ n, K n) = U ∧ M ⊆ (f '' U)ᶜ ∧
      (∀ p ∈ M, let D := ⋂ n, connectedComponentIn (f '' K n)ᶜ p
                IsRoundClosedDisk D ∧ IsPreconnected D) ∧
      IsTotallyDisconnected ((f '' U)ᶜ \ ⋃ p ∈ M, ⋂ n, connectedComponentIn (f '' K n)ᶜ p)

/-- Topological disk-remainder criterion, with no conformal input. -/
def H2 : Prop :=
  ∀ (V M : Set Sphere), IsOpen V → IsConnected V →
    (∀ p ∈ M, IsRoundClosedDisk (connectedComponentIn Vᶜ p)) →
    IsTotallyDisconnected (Vᶜ \ ⋃ p ∈ M, connectedComponentIn Vᶜ p) → IsCircleDomain V

theorem main : H1 → H2 → OMA.R_arxiv_2603_15098_R1.H1 := by
  intro hlim hcrit U ho hc hi
  obtain ⟨f, K, M, hf, hfo, _, _, hU, hm, hD, ht⟩ := hlim U ho hc hi
  have he (p : Sphere) (hp : p ∈ M) :
      (⋂ n, connectedComponentIn (f '' K n)ᶜ p) = connectedComponentIn (f '' U)ᶜ p := by
    have hK (n : ℕ) : K n ⊆ U := hU ▸ subset_iUnion K n
    have hsub (n : ℕ) : (f '' U)ᶜ ⊆ (f '' K n)ᶜ := compl_subset_compl.mpr (image_mono (hK n))
    apply Subset.antisymm
    · apply (hD p hp).2.subset_connectedComponentIn
      · exact mem_iInter.mpr fun n => mem_connectedComponentIn (hsub n (hm hp))
      · intro z hz hzf
        obtain ⟨x, hx, rfl⟩ := hzf
        obtain ⟨n, hn⟩ := mem_iUnion.mp (hU.symm ▸ hx)
        exact connectedComponentIn_subset _ _ (mem_iInter.mp hz n) ⟨x, hn, rfl⟩
    · exact subset_iInter fun n => connectedComponentIn_mono p (hsub n)
  have hu : (⋃ p ∈ M, ⋂ n, connectedComponentIn (f '' K n)ᶜ p) =
      ⋃ p ∈ M, connectedComponentIn (f '' U)ᶜ p := by
    apply iUnion_congr; intro p; apply iUnion_congr; exact he p
  refine ⟨f '' U, f, hcrit _ M hfo (hc.image f ?_) (fun p hp => he p hp ▸ (hD p hp).1) (hu ▸ ht), hf⟩
  exact fun x hx => (hf.1 x hx).1.continuousWithinAt

end OMA.R_arxiv_2603_15098_R1_H1_R1
