import OMAReductions.R_erdos_132_R1
import Mathlib

/-!
# Rare distances on grids and in the remaining few-distance configurations

The grid estimate is quantitative, with a threshold independent of the axes,
the spacing and the aspect ratio. A separate counting argument discards every
configuration having a sufficiently small total multiplicity on some 2k distances.
-/

namespace OMA.R_erdos_132_R1_H2_R1

open Finset
open scoped Classical InnerProductSpace
open OMA.S_erdos_132 (pairMultiplicity rareDistances)

/-- Every complete grid with at least 128 k³ points has at least k rare distances. -/
def H1 : Prop :=
  ∀ (o u v : EuclideanSpace ℝ (Fin 2)), LinearIndependent ℝ ![u,v] → 0 ≤ ⟪u,v⟫_ℝ →
    ∀ x y : ℕ → ℝ, StrictMono x → StrictMono y → ∀ r s k : ℕ,
    128*k^3 ≤ (r+1)*(s+1) →
    k ≤ (rareDistances (((range (r+1)) ×ˢ (range (s+1))).image
      (fun p => o + x p.1 • u + y p.2 • v))).card

/-- The residual case excludes complete grids and configurations admitting a set
of 2k distances with at most 2k(n+1) ordered realizations in total. -/
def H2 : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ A : Finset (EuclideanSpace ℝ (Fin 2)), N ≤ A.card →
    (A.offDiag.image (fun p => dist p.1 p.2)).card + 2 ≤ A.card/2+k →
    (∀ (o u v : EuclideanSpace ℝ (Fin 2)), LinearIndependent ℝ ![u,v] → 0 ≤ ⟪u,v⟫_ℝ →
      ∀ x y : ℕ → ℝ, StrictMono x → StrictMono y → ∀ r s : ℕ,
      A ≠ (((range (r+1)) ×ˢ (range (s+1))).image (fun p => o + x p.1 • u + y p.2 • v))) →
    (∀ S ⊆ A.offDiag.image (fun p => dist p.1 p.2), 2*k ≤ S.card →
      2*k*(A.card+1) < (A.offDiag.filter (fun p => dist p.1 p.2 ∈ S)).card) →
    k ≤ (rareDistances A).card

lemma rare_of_sparse {A : Finset (EuclideanSpace ℝ (Fin 2))} {S : Finset ℝ} {k : ℕ}
    (sub : S ⊆ A.offDiag.image (fun p => dist p.1 p.2)) (size : 2*k ≤ S.card)
    (budget : (A.offDiag.filter (fun p => dist p.1 p.2 ∈ S)).card ≤ 2*k*(A.card+1)) :
    k ≤ (rareDistances A).card := by
  classical
  let f := fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) => dist p.1 p.2
  let B := S \ rareDistances A
  have heavy (d : ℝ) (hd : d ∈ B) :
      2*(A.card+1) ≤ (A.offDiag.filter (fun p => f p = d)).card := by
    obtain ⟨mem, out⟩ := mem_sdiff.mp hd
    have positive := OMA.R_erdos_132_R1.multiplicity_pos (sub mem)
    have large : A.card < pairMultiplicity A d := by
      by_contra! le
      exact out (mem_filter.mpr ⟨sub mem,positive,le⟩)
    change A.card < (A.offDiag.filter (fun p => f p = d)).card / 2 at large
    omega
  have bound : B.card*(2*(A.card+1)) ≤ 2*k*(A.card+1) := by
    calc
      _ = ∑ _d ∈ B, 2*(A.card+1) := by simp
      _ ≤ ∑ d ∈ B, (A.offDiag.filter (fun p => f p = d)).card :=
        sum_le_sum fun d hd => heavy d hd
      _ = (A.offDiag.filter (fun p => f p ∈ B)).card := sum_card_fiberwise_eq_card_filter _ _ _
      _ ≤ (A.offDiag.filter (fun p => f p ∈ S)).card :=
        card_le_card (monotone_filter_right _ fun _ _ h => (mem_sdiff.mp h).1)
      _ ≤ _ := budget
  have count : B.card ≤ k := by
    by_contra! more
    have strict := Nat.mul_lt_mul_of_pos_right more (show 0 < 2*(A.card+1) by omega)
    rw [show 2*k*(A.card+1) = k*(2*(A.card+1)) by ring] at bound
    omega
  have cover : S ⊆ B ∪ rareDistances A := by
    intro d hd
    by_cases h : d ∈ rareDistances A
    · exact mem_union_right _ h
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hd,h⟩)
  have := (card_le_card cover).trans (card_union_le _ _)
  omega

theorem main : H1 → H2 → OMA.R_erdos_132_R1.H2 := by
  classical
  intro grid remaining k
  obtain ⟨N, hN⟩ := remaining k
  refine ⟨max N (128*k^3), ?_⟩
  intro A large few
  by_contra! bad
  have nongrid (o u v : EuclideanSpace ℝ (Fin 2)) (ind : LinearIndependent ℝ ![u,v])
      (angle : 0 ≤ ⟪u,v⟫_ℝ) (x y : ℕ → ℝ) (hx : StrictMono x) (hy : StrictMono y) (r s : ℕ) :
      A ≠ (((range (r+1)) ×ˢ (range (s+1))).image (fun p => o + x p.1 • u + y p.2 • v)) := by
    intro eq
    have cardBound : A.card ≤ (r+1)*(s+1) := by
      rw [eq]
      exact card_image_le.trans (by simp)
    have size : 128*k^3 ≤ (r+1)*(s+1) := (le_max_right _ _).trans (large.trans cardBound)
    exact (not_le_of_gt bad) (by simpa only [eq] using grid o u v ind angle x y hx hy r s k size)
  apply (not_le_of_gt bad) (hN A ((le_max_left _ _).trans large) few nongrid ?_)
  intro S hsub hsize
  by_contra! small
  exact (not_le_of_gt bad) (rare_of_sparse hsub hsize small)

end OMA.R_erdos_132_R1_H2_R1
