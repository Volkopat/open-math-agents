import OMAStatements.S_oeis_a328151
import Mathlib.Tactic

namespace OMA.P_oeis_a328151

open OMA.S_oeis_a328151

open Classical in
private lemma ordered_eq_two_mul_distinct_add_diag (m : ℕ) :
    numOrderedPosSumTwoSq m =
      2 * numDistinctPosSumTwoSq m + if ∃ c : ℕ, 1 ≤ c ∧ m = 2 * c ^ 2 then 1 else 0 := by
  unfold numOrderedPosSumTwoSq numDistinctPosSumTwoSq
  set B := Finset.Icc 1 m ×ˢ Finset.Icc 1 m
  set S := B.filter (fun p => p.1 ^ 2 + p.2 ^ 2 = m)
  set Slt := B.filter (fun p => p.1 < p.2 ∧ p.1 ^ 2 + p.2 ^ 2 = m)
  set Sgt := B.filter (fun p => p.2 < p.1 ∧ p.1 ^ 2 + p.2 ^ 2 = m)
  set Seq := B.filter (fun p => p.1 = p.2 ∧ p.1 ^ 2 + p.2 ^ 2 = m)
  have hdisj1 : Disjoint Slt Sgt := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [Slt, Sgt, Finset.mem_filter] at h1 h2
    omega
  have hdisj2 : Disjoint (Slt ∪ Sgt) Seq := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    simp only [Finset.mem_union, Slt, Sgt, Seq, Finset.mem_filter] at h1 h2
    rcases h1 with h1 | h1 <;> omega
  have hunion : S = (Slt ∪ Sgt) ∪ Seq := by
    ext p
    simp only [Finset.mem_union, S, Slt, Sgt, Seq, Finset.mem_filter]
    constructor
    · rintro ⟨hp, hsq⟩
      rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
      · exact Or.inl (Or.inl ⟨hp, hlt, hsq⟩)
      · exact Or.inr ⟨hp, heq, hsq⟩
      · exact Or.inl (Or.inr ⟨hp, hgt, hsq⟩)
    · rintro ((⟨hp, _, hsq⟩ | ⟨hp, _, hsq⟩) | ⟨hp, _, hsq⟩) <;> exact ⟨hp, hsq⟩
  have hcard_gt : Sgt.card = Slt.card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp
      simp only [Sgt, Slt, B, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
      refine ⟨⟨hp.1.2, hp.1.1⟩, hp.2.1, ?_⟩
      linarith [hp.2.2]
    · intro p1 _ p2 _ h
      rcases p1 with ⟨a1, b1⟩; rcases p2 with ⟨a2, b2⟩
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.2 h.1
    · intro q hq
      refine ⟨(q.2, q.1), ?_, Prod.ext rfl rfl⟩
      simp only [Sgt, Slt, B, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hq ⊢
      refine ⟨⟨hq.1.2, hq.1.1⟩, hq.2.1, ?_⟩
      linarith [hq.2.2]
  have hcard_eq : Seq.card = if ∃ c : ℕ, 1 ≤ c ∧ m = 2 * c ^ 2 then 1 else 0 := by
    split_ifs with hex
    · rcases hex with ⟨c, hc1, rfl⟩
      have hseq_eq : Seq = {(c, c)} := by
        ext ⟨x, y⟩
        simp only [Seq, B, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
          Finset.mem_singleton, Prod.mk.injEq]
        constructor
        · rintro ⟨_, rfl, hsq⟩
          have hx2 : x ^ 2 = c ^ 2 := by linarith
          have hxc : x = c := by nlinarith
          exact ⟨hxc, hxc⟩
        · rintro ⟨hx, hy⟩
          rw [hx, hy]
          have hle : c ≤ 2 * c ^ 2 := by nlinarith
          exact ⟨⟨⟨hc1, hle⟩, ⟨hc1, hle⟩⟩, rfl, by ring⟩
      rw [hseq_eq, Finset.card_singleton]
    · have hseq_empty : Seq = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        rintro ⟨x, y⟩ hp
        simp only [Seq, B, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
        rcases hp with ⟨⟨⟨hx1, _⟩, _⟩, rfl, hsq⟩
        exact hex ⟨x, hx1, by linarith⟩
      rw [hseq_empty, Finset.card_empty]
  rw [hunion, Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1,
    hcard_gt, hcard_eq]
  ring

private lemma distinct_two_mul_sq (c : ℕ) (_hc : 1 ≤ c) :
    numDistinctPosSumTwoSq (2 * c ^ 2) = numDistinctPosSumTwoSq (c ^ 2) := by
  unfold numDistinctPosSumTwoSq
  refine Finset.card_bij (fun p _ => ((p.2 - p.1) / 2, (p.2 + p.1) / 2)) ?_ ?_ ?_
  · intro ⟨x, y⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
    rcases hp with ⟨⟨⟨hx1, _⟩, ⟨hy1, _⟩⟩, hxy, hsq⟩
    have hpar : (y - x) % 2 = 0 ∧ (y + x) % 2 = 0 := by
      have hmod : (x ^ 2 + y ^ 2) % 2 = 0 := by omega
      have hx2 : x ^ 2 % 2 = x % 2 := by
        have := Nat.div_add_mod x 2
        rcases Nat.mod_two_eq_zero_or_one x with h | h <;>
          simp [pow_two, Nat.mul_mod, h]
      have hy2 : y ^ 2 % 2 = y % 2 := by
        rcases Nat.mod_two_eq_zero_or_one y with h | h <;>
          simp [pow_two, Nat.mul_mod, h]
      have hxy2 : x % 2 = y % 2 := by omega
      omega
    have ha2 : 2 * ((y - x) / 2) = y - x := by omega
    have hb2 : 2 * ((y + x) / 2) = y + x := by omega
    have hsum : ((y - x) / 2) ^ 2 + ((y + x) / 2) ^ 2 = c ^ 2 := by
      have h4 : (2 * ((y - x) / 2)) ^ 2 + (2 * ((y + x) / 2)) ^ 2 = 4 * c ^ 2 := by
        rw [ha2, hb2]
        zify [le_of_lt hxy] at hsq ⊢
        linarith
      nlinarith
    have ha1 : 1 ≤ (y - x) / 2 := by omega
    have hb1 : 1 ≤ (y + x) / 2 := by omega
    have hab : (y - x) / 2 < (y + x) / 2 := by omega
    have hale : (y - x) / 2 ≤ c ^ 2 := by nlinarith
    have hble : (y + x) / 2 ≤ c ^ 2 := by nlinarith
    exact ⟨⟨⟨ha1, hale⟩, ⟨hb1, hble⟩⟩, hab, hsum⟩
  · intro ⟨x1, y1⟩ hp1 ⟨x2, y2⟩ hp2 heq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp1 hp2
    rcases hp1 with ⟨_, hxy1, hsq1⟩
    rcases hp2 with ⟨_, hxy2, hsq2⟩
    have hp_even : ∀ x y : ℕ, x ^ 2 + y ^ 2 = 2 * c ^ 2 → x % 2 = y % 2 := by
      intro x y hsq
      have hx2 : x ^ 2 % 2 = x % 2 := by
        rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [pow_two, Nat.mul_mod, h]
      have hy2 : y ^ 2 % 2 = y % 2 := by
        rcases Nat.mod_two_eq_zero_or_one y with h | h <;> simp [pow_two, Nat.mul_mod, h]
      omega
    have he1 := hp_even x1 y1 hsq1
    have he2 := hp_even x2 y2 hsq2
    simp only [Prod.mk.injEq] at heq
    exact Prod.ext (by omega) (by omega)
  · intro ⟨a, b⟩ hq
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hq
    rcases hq with ⟨⟨⟨ha1, _⟩, ⟨hb1, _⟩⟩, hab, hsq⟩
    refine ⟨(b - a, b + a), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      have hsq2 : (b - a) ^ 2 + (b + a) ^ 2 = 2 * c ^ 2 := by
        zify [le_of_lt hab] at hsq ⊢
        linarith
      have hba1 : 1 ≤ b - a := by omega
      have hba2 : b - a ≤ 2 * c ^ 2 := by nlinarith
      have hbp1 : 1 ≤ b + a := by omega
      have hbp2 : b + a ≤ 2 * c ^ 2 := by nlinarith
      exact ⟨⟨⟨hba1, hba2⟩, ⟨hbp1, hbp2⟩⟩, by omega, hsq2⟩
    · simp only [Prod.mk.injEq]
      omega

open Classical in
private lemma part_even (k : ℕ) (hk : 1 ≤ k) : A328151 (2 * k) = A093195 k := by
  unfold A328151 A093195
  set S := { m : ℕ | numOrderedPosSumTwoSq m = 2 * k }
  set T := { m : ℕ | 1 ≤ m ∧ numDistinctPosSumTwoSq m = k }
  have hsub : S ⊆ T := by
    intro m hm
    simp only [S, Set.mem_ofPred_eq] at hm
    have hform := ordered_eq_two_mul_distinct_add_diag m
    rw [hm] at hform
    have hnot : ¬ (∃ c : ℕ, 1 ≤ c ∧ m = 2 * c ^ 2) := by
      intro hex
      rw [if_pos hex] at hform
      omega
    rw [if_neg hnot] at hform
    have hdist : numDistinctPosSumTwoSq m = k := by omega
    have hm1 : 1 ≤ m := by
      by_contra hm0
      have hm_eq : m = 0 := by omega
      subst hm_eq
      have h0 : numDistinctPosSumTwoSq 0 = 0 := by simp [numDistinctPosSumTwoSq]
      omega
    exact ⟨hm1, hdist⟩
  by_cases hT : T.Nonempty
  · set m0 := sInf T
    have hm0_mem : m0 ∈ T := Nat.sInf_mem hT
    have hm0_not_diag : ¬ (∃ c : ℕ, 1 ≤ c ∧ m0 = 2 * c ^ 2) := by
      rintro ⟨c, hc1, hmc⟩
      have hc2_mem : c ^ 2 ∈ T := by
        refine ⟨by nlinarith, ?_⟩
        rw [← distinct_two_mul_sq c hc1, ← hmc]
        exact hm0_mem.2
      have hle : m0 ≤ c ^ 2 := Nat.sInf_le hc2_mem
      nlinarith
    have hm0_S : m0 ∈ S := by
      simp only [S, Set.mem_ofPred_eq]
      rw [ordered_eq_two_mul_distinct_add_diag m0, if_neg hm0_not_diag, hm0_mem.2, add_zero]
    have hS : S.Nonempty := ⟨m0, hm0_S⟩
    exact le_antisymm (Nat.sInf_le hm0_S) (le_csInf hS (fun m hm => Nat.sInf_le (hsub hm)))
  · have hT_empty : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
    have hS_empty : S = ∅ := Set.subset_empty_iff.mp (hT_empty ▸ hsub)
    rw [hS_empty, hT_empty]

open Classical in
private lemma part_odd (k : ℕ) : A328151 (2 * k + 1) = 2 * (A006339 k) ^ 2 := by
  unfold A328151 A006339
  set S := { m : ℕ | numOrderedPosSumTwoSq m = 2 * k + 1 }
  set C := { c : ℕ | 1 ≤ c ∧ numDistinctPosSumTwoSq (c ^ 2) = k }
  have hS_eq : S = (fun c => 2 * c ^ 2) '' C := by
    ext m
    simp only [S, C, Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro hm
      have hform := ordered_eq_two_mul_distinct_add_diag m
      rw [hm] at hform
      have hex : ∃ c : ℕ, 1 ≤ c ∧ m = 2 * c ^ 2 := by
        by_contra hnot
        rw [if_neg hnot] at hform
        omega
      rw [if_pos hex] at hform
      rcases hex with ⟨c, hc1, rfl⟩
      refine ⟨c, ⟨hc1, ?_⟩, rfl⟩
      rw [← distinct_two_mul_sq c hc1]
      omega
    · rintro ⟨c, ⟨hc1, hdk⟩, rfl⟩
      rw [ordered_eq_two_mul_distinct_add_diag (2 * c ^ 2),
        if_pos ⟨c, hc1, rfl⟩, distinct_two_mul_sq c hc1, hdk]
  by_cases hC : C.Nonempty
  · set c0 := sInf C
    have hc0_mem : c0 ∈ C := Nat.sInf_mem hC
    have h2c0_S : 2 * c0 ^ 2 ∈ S := by
      rw [hS_eq]
      exact ⟨c0, hc0_mem, rfl⟩
    have hS_ne : S.Nonempty := ⟨2 * c0 ^ 2, h2c0_S⟩
    refine le_antisymm (Nat.sInf_le h2c0_S) (le_csInf hS_ne ?_)
    intro m hm
    rw [hS_eq] at hm
    rcases hm with ⟨c, hc, rfl⟩
    have hle : c0 ≤ c := Nat.sInf_le hc
    nlinarith
  · have hC_empty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hC
    have hS_empty : S = ∅ := by rw [hS_eq, hC_empty, Set.image_empty]
    rw [hS_empty, hC_empty]
    simp

private theorem prove_solution :
    (∀ k : ℕ, 1 ≤ k → A328151 (2 * k) = A093195 k) ∧
    (∀ k : ℕ, A328151 (2 * k + 1) = 2 * (A006339 k) ^ 2) :=
  ⟨part_even, part_odd⟩

end OMA.P_oeis_a328151

theorem OMA.solution : type_of% @OMA.S_oeis_a328151.main :=
  OMA.P_oeis_a328151.prove_solution
