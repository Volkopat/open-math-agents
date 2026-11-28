import OMAStatements.S_mo_229756
import Mathlib

/-
MathOverflow 229756: in a locally compact Hausdorff abelian group with Haar measure mu, a
measurable subgroup H with 0 < mu H < infinity is open and compact.

Open: by the Steinhaus theorem H / H is a neighbourhood of 1, and H / H is contained in H.
Compact: H is open, hence closed. Take a compact neighbourhood K of 1 inside H. If H were not
compact then, for every finite subset F of H, H is not covered by the compact set of all
f k k'^-1 (f in F, k and k' in K), so some h in H has h K disjoint from every f K. By
induction there are n pairwise disjoint translates of K inside H for every n, so
n mu(K) <= mu(H) for all n, which contradicts mu(K) > 0 and mu(H) < infinity.
-/

namespace OMA.PMO229756

open Set Filter MeasureTheory MeasureTheory.Measure
open scoped ENNReal Pointwise Topology

lemma main' : ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [T2Space G] [IsTopologicalGroup G]
      [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
      (μ : Measure G) [IsHaarMeasure μ] [μ.InnerRegularCompactLTTop],
      ∀ H : Subgroup G, MeasurableSet (H : Set G) → 0 < μ H → μ H ≠ ∞ →
        IsOpen (H : Set G) ∧ IsCompact (H : Set G) := by
  intro G _ _ _ _ _ _ _ μ _ _ H hmeas hpos hfin
  classical
  have hnhds : (H : Set G) ∈ 𝓝 (1 : G) := by
    refine Filter.mem_of_superset (div_mem_nhds_one_of_haar_pos_ne_top μ H hmeas hpos hfin) ?_
    rw [Set.div_subset_iff]
    exact fun x hx y hy => H.div_mem hx hy
  have hopen : IsOpen (H : Set G) := H.isOpen_of_mem_nhds hnhds
  have hclosed : IsClosed (H : Set G) := H.isClosed_of_isOpen hopen
  refine ⟨hopen, ?_⟩
  by_contra hnc
  obtain ⟨K0, K01, hK0, -⟩ : ∃ K ∈ 𝓝 (1 : G), IsCompact K ∧ IsClosed K :=
    exists_mem_nhds_isCompact_isClosed 1
  obtain ⟨K, hKdef⟩ : ∃ K : Set G, K = K0 ∩ H := ⟨_, rfl⟩
  have hK : IsCompact K := hKdef ▸ hK0.inter_right hclosed
  have hKH : K ⊆ H := hKdef ▸ Set.inter_subset_right
  have K1 : K ∈ 𝓝 (1 : G) := hKdef ▸ Filter.inter_mem K01 hnhds
  have h1K : (1 : G) ∈ K := mem_of_mem_nhds K1
  have Kpos : 0 < μ K := measure_pos_of_mem_nhds μ K1
  have key : ∀ n : ℕ, ∃ F : Finset G, F.card = n ∧ (∀ f ∈ F, f ∈ H) ∧
      (F : Set G).PairwiseDisjoint (fun f => f • K) := by
    intro n
    induction n with
    | zero => exact ⟨∅, rfl, by simp, by simp⟩
    | succ n ih =>
      obtain ⟨F, hc, hFH, hd⟩ := ih
      have hC : IsCompact (⋃ f ∈ F, f • (K * K⁻¹)) :=
        F.isCompact_biUnion fun f _ => (hK.mul hK.inv).smul f
      have hns : ¬ (H : Set G) ⊆ ⋃ f ∈ F, f • (K * K⁻¹) := fun hsub =>
        hnc (hC.of_isClosed_subset hclosed hsub)
      obtain ⟨h, hhH, hh⟩ := Set.not_subset.1 hns
      have hdis : ∀ f ∈ F, Disjoint (f • K) (h • K) := by
        intro f hf
        rw [Set.disjoint_left]
        rintro _ ⟨k1, hk1, rfl⟩ ⟨k2, hk2, e⟩
        apply hh
        simp only [Set.mem_iUnion]
        refine ⟨f, hf, k1 * k2⁻¹, Set.mul_mem_mul hk1 (Set.inv_mem_inv.2 hk2), ?_⟩
        simp only [smul_eq_mul] at e ⊢
        rw [← mul_assoc, ← e, mul_inv_cancel_right]
      have hnot : h ∉ F := fun hf =>
        Set.disjoint_left.1 (hdis h hf) (Set.smul_mem_smul_set h1K) (Set.smul_mem_smul_set h1K)
      refine ⟨insert h F, by rw [Finset.card_insert_of_notMem hnot, hc], ?_, ?_⟩
      · intro f hf
        rcases Finset.mem_insert.1 hf with rfl | hf
        exacts [hhH, hFH f hf]
      · rw [Finset.coe_insert, Set.pairwiseDisjoint_insert]
        exact ⟨hd, fun f hf _ => (hdis f hf).symm⟩
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt Kpos.ne' hfin
  obtain ⟨F, hc, hFH, hd⟩ := key n
  have hsub : (⋃ f ∈ F, f • K) ⊆ (H : Set G) := by
    refine Set.iUnion₂_subset fun f hf => ?_
    rintro _ ⟨k, hk, rfl⟩
    exact H.mul_mem (hFH f hf) (hKH hk)
  have hmu : μ (⋃ f ∈ F, f • K) = n * μ K := by
    rw [measure_biUnion_finset hd fun f _ => (hK.smul f).isClosed.measurableSet]
    simp [measure_smul, hc]
  exact absurd (hmu ▸ measure_mono hsub) (not_le.2 hn)

end OMA.PMO229756

theorem OMA.solution : type_of% @OMA.S_mo_229756.main := OMA.PMO229756.main'
