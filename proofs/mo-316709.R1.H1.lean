import OMAReductions.R_mo_316709_R1
import Mathlib

/-! Step mo-316709.R1.H1: two disjoint left cosets of finite-index subgroups have non-coprime
indices. Coprime indices give [G : H ∩ K] = [G : H][G : K], hence [H : H ∩ K] = [G : K], so the
embedding H ⧸ (H ∩ K) into G ⧸ K is onto, G = HK, and the cosets aH, bK meet. -/

namespace OMA.P316

open scoped Pointwise

/-- Coprime finite indices force `G = H K`: every `c` is `h k` with `h ∈ H`, `k ∈ K`. -/
theorem exists_mem_of_coprime {G : Type} [Group G] (H K : Subgroup G) (hH : H.index ≠ 0)
    (hK : K.index ≠ 0) (hc : Nat.Coprime H.index K.index) (c : G) :
    ∃ h ∈ H, h⁻¹ * c ∈ K := by
  have hinf : (H ⊓ K).index = H.index * K.index := by
    apply le_antisymm Subgroup.index_inf_le
    apply Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_inf_ne_zero hH hK))
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hc (Subgroup.index_dvd_of_le inf_le_left)
      (Subgroup.index_dvd_of_le inf_le_right)
  have hrel : K.relIndex H = K.index := by
    have h1 := Subgroup.relIndex_mul_index (inf_le_left : H ⊓ K ≤ H)
    rw [Subgroup.inf_relIndex_left, hinf, mul_comm H.index K.index] at h1
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hH) h1
  let e := Subgroup.quotientSubgroupOfEmbeddingOfLE K (le_top : H ≤ ⊤)
  have hcardT : Nat.card ((⊤ : Subgroup G) ⧸ K.subgroupOf ⊤) = K.index := by
    rw [← Subgroup.index, ← Subgroup.relIndex, Subgroup.relIndex_top_right]
  have hcardH : Nat.card (H ⧸ K.subgroupOf H) = K.index := by
    rw [← Subgroup.index, ← Subgroup.relIndex, hrel]
  have hfinT : Finite ((⊤ : Subgroup G) ⧸ K.subgroupOf ⊤) :=
    Nat.finite_of_card_ne_zero (by rw [hcardT]; exact hK)
  have hbij : Function.Bijective e :=
    e.injective.bijective_of_nat_card_le (by rw [hcardT, hcardH])
  obtain ⟨x, hx⟩ := hbij.2 (QuotientGroup.mk ⟨c, Subgroup.mem_top c⟩)
  induction x using QuotientGroup.induction_on with
  | H h =>
    rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq] at hx
    refine ⟨h, h.2, ?_⟩
    have := Subgroup.mem_subgroupOf.mp hx
    simpa using this

theorem solution_aux : ∀ (G : Type) [Group G] (H : Fin 2 → Subgroup G) (a : Fin 2 → G),
    (∀ i, (H i).index ≠ 0) →
    Pairwise (fun i j => Disjoint (a i • (H i : Set G)) (a j • (H j : Set G))) →
    ∃ i j : Fin 2, i < j ∧ 2 ≤ Nat.gcd (H i).index (H j).index := by
  intro G _ H a hfin hdisj
  refine ⟨0, 1, by decide, ?_⟩
  have hg0 : Nat.gcd (H 0).index (H 1).index ≠ 0 := by
    intro h
    exact hfin 0 (Nat.eq_zero_of_gcd_eq_zero_left h)
  have hg1 : Nat.gcd (H 0).index (H 1).index ≠ 1 := by
    intro hcop
    obtain ⟨h, hh, hk⟩ := exists_mem_of_coprime (H 0) (H 1) (hfin 0) (hfin 1) hcop
      ((a 0)⁻¹ * a 1)
    have hx0 : a 0 * h ∈ a 0 • (H 0 : Set G) := by
      rw [mem_leftCoset_iff]; simpa using hh
    have hx1 : a 0 * h ∈ a 1 • (H 1 : Set G) := by
      rw [mem_leftCoset_iff]
      have := (H 1).inv_mem hk
      simpa [mul_assoc] using this
    exact Set.disjoint_left.mp (hdisj (by decide : (0 : Fin 2) ≠ 1)) hx0 hx1
  omega

end OMA.P316

theorem OMA.solution : OMA.R_mo_316709_R1.H1 := OMA.P316.solution_aux
