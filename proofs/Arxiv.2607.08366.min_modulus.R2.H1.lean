import OMAReductions.R_Arxiv_2607_08366_min_modulus_R2

/-! Fix a₀ ∈ A and let B = A.erase a₀. The map S ↦ Σ_{x ∈ S} x - |S| · a₀ is injective on subsets
of B, so 2^(n-1) = #(powerset B) ≤ #(ZMod N) = N. Suppose S ≠ T collide, and let S' = S \ T and
T' = T \ S, with |S'| ≤ |T'| after swapping. The multiplicity function equal to 2 on S', 0 on T',
1 + |T'| - |S'| at a₀ and 1 elsewhere on A has total #A and weighted sum Σ_{x ∈ A} x, but is not
identically 1 on A. This contradicts validity. -/

namespace OMA.MinModulusR2

open Finset

theorem key {N : ℕ} (A : Finset (ZMod N)) (hv : Arxiv.«2607.08366».IsValidMod A) (a0 : ZMod N)
    (ha0 : a0 ∈ A) (S' T' : Finset (ZMod N)) (hS' : S' ⊆ A.erase a0) (hT' : T' ⊆ A.erase a0)
    (hd : Disjoint S' T') (hcard : S'.card ≤ T'.card) (hne : (S' ∪ T').Nonempty)
    (hsum : ∑ x ∈ S', x - ∑ x ∈ T', x = ((S'.card : ZMod N) - (T'.card : ZMod N)) * a0) :
    False := by
  classical
  set R := (A.erase a0 \ S') \ T' with hR
  have hB : A.erase a0 = S' ∪ T' ∪ R := by
    ext x
    simp only [hR, mem_union, mem_sdiff]
    constructor
    · intro hx
      by_cases h1 : x ∈ S'
      · exact Or.inl (Or.inl h1)
      · by_cases h2 : x ∈ T'
        · exact Or.inl (Or.inr h2)
        · exact Or.inr ⟨⟨hx, h1⟩, h2⟩
    · rintro ((h | h) | ⟨⟨h, -⟩, -⟩)
      · exact hS' h
      · exact hT' h
      · exact h
  have hd2 : Disjoint (S' ∪ T') R := by
    rw [hR, Finset.disjoint_left]
    intro x hx hxR
    simp only [mem_sdiff] at hxR
    rcases mem_union.1 hx with h | h
    · exact hxR.1.2 h
    · exact hxR.2 h
  have split : ∀ {M : Type} [AddCommMonoid M] (g : ZMod N → M),
      ∑ x ∈ A, g x = g a0 + (∑ x ∈ S', g x + ∑ x ∈ T', g x + ∑ x ∈ R, g x) := by
    intro M _ g
    conv_lhs => rw [← Finset.insert_erase ha0]
    rw [Finset.sum_insert (Finset.notMem_erase a0 A), hB, Finset.sum_union hd2,
      Finset.sum_union hd]
  have ha0S : a0 ∉ S' := fun h => Finset.notMem_erase a0 A (hS' h)
  have ha0T : a0 ∉ T' := fun h => Finset.notMem_erase a0 A (hT' h)
  let m : ZMod N → ℕ := fun x =>
    if x ∈ S' then 2 else if x ∈ T' then 0 else if x = a0 then 1 + T'.card - S'.card else 1
  have mS : ∀ x ∈ S', m x = 2 := fun x hx => by simp [m, hx]
  have mT : ∀ x ∈ T', m x = 0 := fun x hx => by
    simp [m, hx, Finset.disjoint_right.1 hd hx]
  have mR : ∀ x ∈ R, m x = 1 := fun x hx => by
    simp only [hR, mem_sdiff, mem_erase] at hx
    simp [m, hx.1.2, hx.2, hx.1.1.1]
  have ma0 : m a0 = 1 + T'.card - S'.card := by simp [m, ha0S, ha0T]
  have h1 : ∑ x ∈ A, m x = A.card := by
    have s1 := split m
    have s2 := split (fun _ : ZMod N => (1 : ℕ))
    beta_reduce at s2
    rw [Finset.card_eq_sum_ones, s1, s2, Finset.sum_congr rfl mS, Finset.sum_congr rfl mT,
      Finset.sum_congr rfl mR, ma0]
    simp only [Finset.sum_const, smul_eq_mul, mul_one, mul_zero]
    omega
  have h2 : ∑ x ∈ A, (m x : ZMod N) * x = ∑ x ∈ A, x := by
    have s1 := split (fun x => (m x : ZMod N) * x)
    have s2 := split (fun x : ZMod N => x)
    beta_reduce at s1 s2
    have eS : ∑ x ∈ S', (m x : ZMod N) * x = ∑ x ∈ S', 2 * x :=
      Finset.sum_congr rfl (fun x hx => by rw [mS x hx]; norm_num)
    have eT : ∑ x ∈ T', (m x : ZMod N) * x = 0 :=
      Finset.sum_eq_zero (fun x hx => by rw [mT x hx]; simp)
    have eR : ∑ x ∈ R, (m x : ZMod N) * x = ∑ x ∈ R, x :=
      Finset.sum_congr rfl (fun x hx => by rw [mR x hx]; simp)
    rw [s1, s2, eS, eT, eR, ma0, ← Finset.mul_sum, Nat.cast_sub (by omega), Nat.cast_add,
      Nat.cast_one]
    linear_combination hsum
  have h3 := hv m h1 h2
  obtain ⟨x, hx⟩ := hne
  rcases mem_union.1 hx with h | h
  · have := h3 x (Finset.mem_of_mem_erase (hS' h))
    rw [mS x h] at this
    omega
  · have := h3 x (Finset.mem_of_mem_erase (hT' h))
    rw [mT x h] at this
    omega

end OMA.MinModulusR2

open Finset in
theorem OMA.solution : OMA.R_Arxiv_2607_08366_min_modulus_R2.H1 := by
  intro n N hN A hA hv
  classical
  have := NeZero.of_pos hN
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num
    omega
  obtain ⟨a0, ha0⟩ : A.Nonempty := Finset.card_pos.1 (by omega)
  have hinj : Set.InjOn (fun S : Finset (ZMod N) => ∑ x ∈ S, x - (S.card : ZMod N) * a0)
      ((A.erase a0).powerset : Set (Finset (ZMod N))) := by
    intro S hS T hT hST
    simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset] at hS hT
    by_contra hne
    have hsS := Finset.sum_inter_add_sum_sdiff S T (fun x => x)
    have hsT := Finset.sum_inter_add_sum_sdiff T S (fun x => x)
    have hcS := Finset.card_sdiff_add_card_inter S T
    have hcT := Finset.card_sdiff_add_card_inter T S
    rw [Finset.inter_comm T S] at hsT hcT
    have hST' : ∑ x ∈ S, x - (S.card : ZMod N) * a0 = ∑ x ∈ T, x - (T.card : ZMod N) * a0 := hST
    have hsum : ∑ x ∈ S \ T, x - ∑ x ∈ T \ S, x =
        (((S \ T).card : ZMod N) - ((T \ S).card : ZMod N)) * a0 := by
      have e1 : (S.card : ZMod N) = ((S \ T).card : ZMod N) + ((S ∩ T).card : ZMod N) := by
        rw [← Nat.cast_add, hcS]
      have e2 : (T.card : ZMod N) = ((T \ S).card : ZMod N) + ((S ∩ T).card : ZMod N) := by
        rw [← Nat.cast_add, hcT]
      rw [← hsS, ← hsT, e1, e2] at hST'
      linear_combination hST'
    have hne' : ((S \ T) ∪ (T \ S)).Nonempty := by
      by_contra h0
      rw [Finset.not_nonempty_iff_eq_empty, Finset.union_eq_empty,
        Finset.sdiff_eq_empty_iff_subset, Finset.sdiff_eq_empty_iff_subset] at h0
      exact hne (Finset.Subset.antisymm h0.1 h0.2)
    have hsub1 : S \ T ⊆ A.erase a0 := (Finset.sdiff_subset).trans hS
    have hsub2 : T \ S ⊆ A.erase a0 := (Finset.sdiff_subset).trans hT
    rcases le_total (S \ T).card (T \ S).card with h | h
    · exact OMA.MinModulusR2.key A hv a0 ha0 (S \ T) (T \ S) hsub1 hsub2
        disjoint_sdiff_sdiff h hne' hsum
    · refine OMA.MinModulusR2.key A hv a0 ha0 (T \ S) (S \ T) hsub2 hsub1
        disjoint_sdiff_sdiff h (by rwa [Finset.union_comm]) ?_
      linear_combination -hsum
  have hc := Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) hinj
  rw [Finset.card_powerset, Finset.card_erase_of_mem ha0, hA, Finset.card_univ, ZMod.card] at hc
  exact hc
