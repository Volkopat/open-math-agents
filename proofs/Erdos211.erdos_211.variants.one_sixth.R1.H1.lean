import OMAReductions.R_Erdos211_erdos_211_variants_one_sixth_R1

/-!
# Proof of `Erdos211.erdos_211.variants.one_sixth.R1.H1`

Elementary real 3-dimensional frame-energy proof of the quadratic part of Langer's
planar incidence inequality, following Kroeker and Lund (arXiv:2610.21415, Section 3.2
and Appendix A).
-/

-- Step Erdos211.erdos_211.variants.one_sixth.R1.H1: hypothesis H1 of reduction Erdos211.erdos_211.variants.one_sixth.R1
-- Credit: @LiJiaHua1024

namespace Erdos211H1Proof

open EuclideanGeometry Erdos211 Matrix
open scoped BigOperators Classical Matrix

/-- Lift a point in `ℝ²` to homogeneous coordinates in `Fin 3 → ℝ`. -/
def lift (p : ℝ²) : Fin 3 → ℝ := ![p 0, p 1, 1]

lemma lift_injective : Function.Injective lift := by
  intro p q h
  ext i
  fin_cases i
  · exact congrFun h 0
  · exact congrFun h 1

lemma lift_ne_zero (p : ℝ²) : lift p ≠ 0 := by
  intro h
  have := congrFun h 2
  simp [lift] at this

lemma lift_linearIndependent_pair {a b : ℝ²} (hab : a ≠ b) :
    LinearIndependent ℝ ![lift a, lift b] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h2 : g 0 + g 1 = 0 := by
    have := congrFun hg 2
    simp [Fin.sum_univ_two, lift] at this
    linarith
  have h0 : g 0 * a 0 + g 1 * b 0 = 0 := by
    have := congrFun hg 0
    simp [Fin.sum_univ_two, lift] at this
    linarith
  have h1 : g 0 * a 1 + g 1 * b 1 = 0 := by
    have := congrFun hg 1
    simp [Fin.sum_univ_two, lift] at this
    linarith
  have hg1 : g 1 = -g 0 := by linarith
  rw [hg1] at h0 h1
  have hne : a 0 ≠ b 0 ∨ a 1 ≠ b 1 := by
    by_contra hc
    push Not at hc
    apply hab
    ext i
    fin_cases i
    · exact hc.1
    · exact hc.2
  have hg0 : g 0 = 0 := by
    rcases hne with h | h
    · have : g 0 * (a 0 - b 0) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr h)
    · have : g 0 * (a 1 - b 1) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr h)
  intro i
  fin_cases i
  · exact hg0
  · show g 1 = 0; linarith

lemma mem_line_of_lift_mem_span_pair {a b p : ℝ²}
    (hp : lift p ∈ Submodule.span ℝ ({lift a, lift b} : Set (Fin 3 → ℝ))) :
    p ∈ line[ℝ, a, b] := by
  rw [Submodule.mem_span_pair] at hp
  obtain ⟨α, β, hαβ⟩ := hp
  have h2 : α + β = 1 := by
    have := congrFun hαβ 2
    simp [lift] at this
    linarith
  have hα : α = 1 - β := by linarith
  have hp_eq : p = AffineMap.lineMap a b β := by
    ext i
    have hi := congrFun hαβ i.castSucc
    fin_cases i
    · simp [lift, AffineMap.lineMap_apply_module] at hi ⊢
      rw [hα] at hi; linarith
    · simp [lift, AffineMap.lineMap_apply_module] at hi ⊢
      rw [hα] at hi; linarith
  rw [hp_eq]
  exact AffineMap.lineMap_mem_affineSpan_pair β a b

lemma lift_mem_span_pair_of_mem_line {a b p : ℝ²} (hp : p ∈ line[ℝ, a, b]) :
    lift p ∈ Submodule.span ℝ ({lift a, lift b} : Set (Fin 3 → ℝ)) := by
  have hdir : p -ᵥ a ∈ (line[ℝ, a, b]).direction :=
    AffineSubspace.vsub_mem_direction hp (left_mem_affineSpan_pair ℝ a b)
  rw [direction_affineSpan, vectorSpan_pair, Submodule.mem_span_singleton] at hdir
  obtain ⟨t, ht⟩ := hdir
  have hpa : p = (1 + t) • a + (-t) • b := by
    have h1 : p - a = t • (a - b) := by simpa [vsub_eq_sub] using ht.symm
    ext i
    have hi := congrFun (congrArg WithLp.ofLp h1) i
    simp at hi ⊢
    linarith
  rw [Submodule.mem_span_pair]
  refine ⟨1 + t, -t, ?_⟩
  ext i
  fin_cases i
  · simp [lift, hpa]
  · simp [lift, hpa]
  · simp [lift]

lemma card_ge_three (s : Finset ℝ²) (hs : 2 ≤ s.card)
    (hcap : ∀ L : AffineSubspace ℝ ℝ², IsLine L →
      3 * (s.filter fun p => p ∈ L).card ≤ 2 * s.card) :
    3 ≤ s.card := by
  by_contra hlt
  have hcard2 : s.card = 2 := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
  have hL := hcap (line[ℝ, a, b]) (isLine_pair hab)
  have hsub : ({a, b} : Finset ℝ²) ⊆ s.filter (fun p => p ∈ line[ℝ, a, b]) := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hp | hp
    · rw [hp]; exact Finset.mem_filter.mpr ⟨ha, left_mem_affineSpan_pair ℝ a b⟩
    · rw [hp]; exact Finset.mem_filter.mpr ⟨hb, right_mem_affineSpan_pair ℝ a b⟩
  have hge2 : 2 ≤ (s.filter fun p => p ∈ line[ℝ, a, b]).card := by
    calc 2 = ({a, b} : Finset ℝ²).card := (Finset.card_pair hab).symm
      _ ≤ _ := Finset.card_le_card hsub
  omega

lemma density_bound (s : Finset ℝ²) (hs3 : 3 ≤ s.card)
    (hcap : ∀ L : AffineSubspace ℝ ℝ², IsLine L →
      3 * (s.filter fun p => p ∈ L).card ≤ 2 * s.card)
    (W : Submodule ℝ (Fin 3 → ℝ)) :
    ((s.filter fun p => lift p ∈ W).card : ℝ) ≤
      (s.card : ℝ) / 3 * (Module.finrank ℝ W : ℝ) := by
  have hle3 : Module.finrank ℝ W ≤ 3 := by
    have := Submodule.finrank_le W
    simpa [Module.finrank_fin_fun] using this
  have hcases : Module.finrank ℝ W = 0 ∨ Module.finrank ℝ W = 1 ∨
      Module.finrank ℝ W = 2 ∨ Module.finrank ℝ W = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · have hW : W = ⊥ := Submodule.finrank_eq_zero.mp h0
    have hempty : (s.filter fun p => lift p ∈ W) = ∅ := by
      ext p
      simp [hW, lift_ne_zero p]
    simp [hempty, h0]
  · rw [h1]
    have hcard1 : (s.filter fun p => lift p ∈ W).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      have haW : lift a ∈ W := (Finset.mem_filter.mp ha).2
      have hbW : lift b ∈ W := (Finset.mem_filter.mp hb).2
      have hspan : Submodule.span ℝ ({lift a} : Set (Fin 3 → ℝ)) = W := by
        apply Submodule.eq_of_le_of_finrank_eq
        · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr haW)
        · rw [finrank_span_singleton (lift_ne_zero a), h1]
      rw [← hspan, Submodule.mem_span_singleton] at hbW
      obtain ⟨c, hc⟩ := hbW
      have hc1 : c = 1 := by
        have := congrFun hc 2
        simp [lift] at this
        exact this
      rw [hc1, one_smul] at hc
      exact lift_injective hc
    have h1r : ((s.filter fun p => lift p ∈ W).card : ℝ) ≤ 1 := by exact_mod_cast hcard1
    have h3r : (3 : ℝ) ≤ s.card := by exact_mod_cast hs3
    push_cast
    linarith
  · rw [h2]
    by_cases hsmall : (s.filter fun p => lift p ∈ W).card ≤ 1
    · have h1r : ((s.filter fun p => lift p ∈ W).card : ℝ) ≤ 1 := by exact_mod_cast hsmall
      have h3r : (3 : ℝ) ≤ s.card := by exact_mod_cast hs3
      push_cast
      linarith
    · push Not at hsmall
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hsmall
      have haW : lift a ∈ W := (Finset.mem_filter.mp ha).2
      have hbW : lift b ∈ W := (Finset.mem_filter.mp hb).2
      have hspan_eq : Submodule.span ℝ ({lift a, lift b} : Set (Fin 3 → ℝ)) = W := by
        apply Submodule.eq_of_le_of_finrank_eq
        · rw [Submodule.span_le]
          intro x hx
          rcases hx with rfl | rfl <;> assumption
        · have hli := lift_linearIndependent_pair hab
          have hfin := finrank_span_eq_card hli
          have hrange : Set.range ![lift a, lift b] = ({lift a, lift b} : Set (Fin 3 → ℝ)) := by
            ext x
            simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
            constructor
            · rintro ⟨i, rfl⟩; fin_cases i <;> simp
            · rintro (rfl | rfl)
              · exact ⟨0, rfl⟩
              · exact ⟨1, rfl⟩
          rw [hrange] at hfin
          simpa [h2] using hfin
      have hsub : (s.filter fun p => lift p ∈ W) ⊆ s.filter (fun p => p ∈ line[ℝ, a, b]) := by
        intro p hp
        obtain ⟨hps, hpW⟩ := Finset.mem_filter.mp hp
        rw [← hspan_eq] at hpW
        exact Finset.mem_filter.mpr ⟨hps, mem_line_of_lift_mem_span_pair hpW⟩
      have hcapL := hcap (line[ℝ, a, b]) (isLine_pair hab)
      have hnat : 3 * (s.filter fun p => lift p ∈ W).card ≤ 2 * s.card := by
        have := Finset.card_le_card hsub
        omega
      have hreal : (3 : ℝ) * ((s.filter fun p => lift p ∈ W).card : ℝ) ≤ 2 * (s.card : ℝ) := by
        exact_mod_cast hnat
      push_cast
      linarith
  · rw [h3]
    have hle : ((s.filter fun p => lift p ∈ W).card : ℝ) ≤ (s.card : ℝ) := by
      exact_mod_cast Finset.card_filter_le s _
    push_cast
    linarith

lemma lift_span_top (s : Finset ℝ²) (hs3 : 3 ≤ s.card)
    (hcap : ∀ L : AffineSubspace ℝ ℝ², IsLine L →
      3 * (s.filter fun p => p ∈ L).card ≤ 2 * s.card) :
    Submodule.span ℝ (Set.range (fun i : s => lift i.1)) = ⊤ := by
  set W := Submodule.span ℝ (Set.range (fun i : s => lift i.1))
  have hfilt : (s.filter fun p => lift p ∈ W) = s := by
    ext p
    simp only [Finset.mem_filter, and_iff_left_iff_imp]
    intro hp
    exact Submodule.subset_span ⟨⟨p, hp⟩, rfl⟩
  have hd := density_bound s hs3 hcap W
  rw [hfilt] at hd
  have h3r : (3 : ℝ) ≤ s.card := by exact_mod_cast hs3
  have hfr_ge : (3 : ℝ) ≤ (Module.finrank ℝ W : ℝ) := by nlinarith
  have hfr_ge_nat : 3 ≤ Module.finrank ℝ W := by exact_mod_cast hfr_ge
  have hfr_le : Module.finrank ℝ W ≤ 3 := by
    have := Submodule.finrank_le W
    simpa [Module.finrank_fin_fun] using this
  apply Submodule.eq_top_of_finrank_eq
  rw [Module.finrank_fin_fun]
  omega

/- Part 2: Extending lower weights (Appendix A.1 of Kroeker–Lund) -/

section Weights

noncomputable def rankOf {ι : Type*} (v : ι → (Fin 3 → ℝ)) (I : Finset ι) : ℕ :=
  Module.finrank ℝ (Submodule.span ℝ (v '' (I : Set ι)))

lemma rankOf_mono {ι : Type*} (v : ι → (Fin 3 → ℝ)) {I J : Finset ι} (hIJ : I ⊆ J) :
    rankOf v I ≤ rankOf v J := by
  apply Submodule.finrank_mono
  exact Submodule.span_mono (Set.image_mono (Finset.coe_subset.mpr hIJ))

lemma rankOf_singleton {ι : Type*} (v : ι → (Fin 3 → ℝ)) {i : ι} (hv : v i ≠ 0) :
    rankOf v {i} = 1 := by
  unfold rankOf
  rw [Finset.coe_singleton, Set.image_singleton]
  exact finrank_span_singleton hv

lemma rankOf_univ {ι : Type*} [Fintype ι] (v : ι → (Fin 3 → ℝ))
    (hspan : Submodule.span ℝ (Set.range v) = ⊤) :
    rankOf v Finset.univ = 3 := by
  unfold rankOf
  rw [Finset.coe_univ, Set.image_univ, hspan, finrank_top, Module.finrank_fin_fun]

lemma rankOf_submod {ι : Type*} [DecidableEq ι] (v : ι → (Fin 3 → ℝ)) (I J : Finset ι) :
    rankOf v (I ∪ J) + rankOf v (I ∩ J) ≤ rankOf v I + rankOf v J := by
  unfold rankOf
  set U := Submodule.span ℝ (v '' (I : Set ι))
  set V := Submodule.span ℝ (v '' (J : Set ι))
  have hsup : Submodule.span ℝ (v '' ((I ∪ J : Finset ι) : Set ι)) = U ⊔ V := by
    rw [Finset.coe_union, Set.image_union, Submodule.span_union]
  have hinf : Submodule.span ℝ (v '' ((I ∩ J : Finset ι) : Set ι)) ≤ U ⊓ V := by
    rw [Finset.coe_inter]
    refine le_inf ?_ ?_
    · exact Submodule.span_mono (Set.image_mono Set.inter_subset_left)
    · exact Submodule.span_mono (Set.image_mono Set.inter_subset_right)
  rw [hsup]
  have hle := Submodule.finrank_mono hinf
  have heq := Submodule.finrank_sup_add_finrank_inf_eq U V
  omega

lemma exists_tight_weights {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → (Fin 3 → ℝ)) (T : ℝ) (_hT : 0 < T)
    (hv_ne : ∀ i, v i ≠ 0)
    (hspan : Submodule.span ℝ (Set.range v) = ⊤)
    (hdens : ∀ I : Finset ι, (I.card : ℝ) / T ≤ (rankOf v I : ℝ)) :
    ∃ c : ι → ℝ, (∀ i, 1 / T ≤ c i) ∧
      (∀ I : Finset ι, ∑ i ∈ I, c i ≤ (rankOf v I : ℝ)) ∧
      ∑ i : ι, c i = 3 := by
  let K : Set (ι → ℝ) :=
    { c | (∀ i, 1 / T ≤ c i) ∧ (∀ I : Finset ι, ∑ i ∈ I, c i ≤ (rankOf v I : ℝ)) }
  have hKne : K.Nonempty := by
    refine ⟨fun _ => 1 / T, fun _ => le_rfl, fun I => ?_⟩
    simpa [div_eq_mul_inv, mul_comm] using hdens I
  have hKclosed : IsClosed K := by
    have h1 : IsClosed { c : ι → ℝ | ∀ i, 1 / T ≤ c i } := by
      rw [show { c : ι → ℝ | ∀ i, 1 / T ≤ c i } = ⋂ i, { c : ι → ℝ | 1 / T ≤ c i } by ext; simp]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    have h2 : IsClosed { c : ι → ℝ | ∀ I : Finset ι, ∑ i ∈ I, c i ≤ (rankOf v I : ℝ) } := by
      rw [show { c : ι → ℝ | ∀ I : Finset ι, ∑ i ∈ I, c i ≤ (rankOf v I : ℝ) } =
        ⋂ I : Finset ι, { c : ι → ℝ | ∑ i ∈ I, c i ≤ (rankOf v I : ℝ) } by ext; simp]
      exact isClosed_iInter fun I =>
        isClosed_le (continuous_finsetSum I fun i _ => continuous_apply i) continuous_const
    exact h1.inter h2
  have hKsub : K ⊆ Set.univ.pi (fun _ : ι => Set.Icc (1 / T) 1) := by
    intro c hc i _
    refine ⟨hc.1 i, ?_⟩
    have := hc.2 {i}
    simpa [rankOf_singleton v (hv_ne i)] using this
  have hKcompact : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hKclosed hKsub
  have hcont : Continuous (fun c : ι → ℝ => ∑ i : ι, c i) :=
    continuous_finsetSum Finset.univ fun i _ => continuous_apply i
  obtain ⟨c, hcK, hcmax⟩ := hKcompact.exists_isMaxOn hKne hcont.continuousOn
  refine ⟨c, hcK.1, hcK.2, ?_⟩
  have htight_union : ∀ I J : Finset ι,
      ∑ i ∈ I, c i = (rankOf v I : ℝ) →
      ∑ i ∈ J, c i = (rankOf v J : ℝ) →
      ∑ i ∈ I ∪ J, c i = (rankOf v (I ∪ J) : ℝ) := by
    intro I J hI hJ
    have hsum : ∑ i ∈ I ∪ J, c i + ∑ i ∈ I ∩ J, c i = ∑ i ∈ I, c i + ∑ i ∈ J, c i :=
      Finset.sum_union_inter
    have hle1 := hcK.2 (I ∪ J)
    have hle2 := hcK.2 (I ∩ J)
    have hsub : (rankOf v (I ∪ J) : ℝ) + (rankOf v (I ∩ J) : ℝ) ≤
        (rankOf v I : ℝ) + (rankOf v J : ℝ) := by
      exact_mod_cast rankOf_submod v I J
    linarith
  have hmem_tight : ∀ i : ι, ∃ I : Finset ι, i ∈ I ∧ ∑ j ∈ I, c j = (rankOf v I : ℝ) := by
    intro i
    by_contra hnone
    push Not at hnone
    have hpos : ∀ I : Finset ι, i ∈ I → 0 < (rankOf v I : ℝ) - ∑ j ∈ I, c j := by
      intro I hiI
      exact sub_pos.mpr (lt_of_le_of_ne (hcK.2 I) (hnone I hiI))
    let S := (Finset.univ : Finset (Finset ι)).filter (fun I => i ∈ I)
    have hSne : S.Nonempty := ⟨{i}, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_singleton_self i⟩⟩
    let gaps := S.image (fun I => (rankOf v I : ℝ) - ∑ j ∈ I, c j)
    have hgne : gaps.Nonempty := hSne.image _
    set ε := gaps.min' hgne
    have hε_pos : 0 < ε := by
      obtain ⟨I, hIS, hIeq⟩ := Finset.mem_image.mp (Finset.min'_mem gaps hgne)
      dsimp only [ε]
      rw [← hIeq]
      exact hpos I (Finset.mem_filter.mp hIS).2
    let c' : ι → ℝ := Function.update c i (c i + ε)
    have hc'K : c' ∈ K := by
      refine ⟨fun j => ?_, fun I => ?_⟩
      · by_cases hji : j = i
        · subst hji; simp only [c', Function.update_self]; linarith [hcK.1 j]
        · simp only [c', Function.update_of_ne hji]; exact hcK.1 j
      · by_cases hiI : i ∈ I
        · have hsum' : ∑ j ∈ I, c' j = (∑ j ∈ I, c j) + ε := by
            rw [← Finset.add_sum_erase _ _ hiI, ← Finset.add_sum_erase _ c hiI]
            have heq : ∑ j ∈ I.erase i, c' j = ∑ j ∈ I.erase i, c j := by
              apply Finset.sum_congr rfl
              intro j hj
              simp only [c', Function.update_of_ne (Finset.mem_erase.mp hj).1]
            simp only [c', Function.update_self, heq]; ring
          rw [hsum']
          have hε_le : ε ≤ (rankOf v I : ℝ) - ∑ j ∈ I, c j :=
            Finset.min'_le gaps _ (Finset.mem_image.mpr ⟨I, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiI⟩, rfl⟩)
          linarith
        · have hsum' : ∑ j ∈ I, c' j = ∑ j ∈ I, c j := by
            apply Finset.sum_congr rfl
            intro j hj
            have hji : j ≠ i := fun h => hiI (h ▸ hj)
            simp only [c', Function.update_of_ne hji]
          rw [hsum']
          exact hcK.2 I
    have hsum_gt : ∑ j : ι, c j < ∑ j : ι, c' j := by
      have hiU : i ∈ (Finset.univ : Finset ι) := Finset.mem_univ i
      rw [← Finset.add_sum_erase _ c hiU, ← Finset.add_sum_erase _ c' hiU]
      have heq : ∑ j ∈ Finset.univ.erase i, c' j = ∑ j ∈ Finset.univ.erase i, c j := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [c', Function.update_of_ne (Finset.mem_erase.mp hj).1]
      simp only [c', Function.update_self, heq]; linarith
    have hle : ∑ j : ι, c' j ≤ ∑ j : ι, c j := hcmax hc'K
    linarith
  have hcover : ∀ A : Finset ι, ∃ I : Finset ι, A ⊆ I ∧ ∑ j ∈ I, c j = (rankOf v I : ℝ) := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      refine ⟨∅, Finset.empty_subset _, ?_⟩
      rw [Finset.sum_empty, rankOf, Finset.coe_empty, Set.image_empty, Submodule.span_empty,
        finrank_bot, Nat.cast_zero]
    | @insert a s _ ih =>
      obtain ⟨I, hsI, hIt⟩ := ih
      obtain ⟨J, haJ, hJt⟩ := hmem_tight a
      refine ⟨I ∪ J, ?_, htight_union I J hIt hJt⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxs
      · exact Finset.mem_union_right _ haJ
      · exact Finset.mem_union_left _ (hsI hxs)
  obtain ⟨I, hUI, hIt⟩ := hcover Finset.univ
  have hIeq : I = Finset.univ := Finset.eq_univ_iff_forall.mpr fun x => hUI (Finset.mem_univ x)
  rw [hIeq, rankOf_univ v hspan] at hIt
  simpa using hIt

end Weights

/- Part 3: 3×3 Cauchy–Binet, Greedy Basis, and Log-Determinant Minimization (Appendix A.2) -/

section LogDet

lemma det_one_add_vecMulVec (u w : Fin 3 → ℝ) :
    (1 + Matrix.vecMulVec u w).det = 1 + dotProduct w u := by
  rw [Matrix.det_fin_three]
  simp [Matrix.vecMulVec, dotProduct, Fin.sum_univ_three]
  ring

lemma sum_mul_sum_mul_sum {ι : Type*} [Fintype ι] (A B C : ι → ℝ) :
    (∑ a : ι, A a) * (∑ b : ι, B b) * (∑ c : ι, C c) =
      ∑ a : ι, ∑ b : ι, ∑ c : ι, A a * B b * C c := by
  rw [mul_assoc, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro c _
  ring

lemma det_sum_vecMulVec_fin3 {ι : Type*} [Fintype ι] (v : ι → (Fin 3 → ℝ)) (w : ι → ℝ) :
    (∑ i : ι, w i • Matrix.vecMulVec (v i) (v i)).det =
      (1 / 6 : ℝ) * ∑ a : ι, ∑ b : ι, ∑ c : ι,
        w a * w b * w c * (Matrix.of ![v a, v b, v c]).det ^ 2 := by
  set M := ∑ i : ι, w i • Matrix.vecMulVec (v i) (v i)
  have hM : ∀ j k : Fin 3, M j k = ∑ i : ι, w i * v i j * v i k := by
    intro j k
    simp [M, Matrix.sum_apply, Matrix.vecMulVec, mul_assoc]
  let f : ι → ι → ι → ℝ := fun a b c =>
    w a * w b * w c * (v a 0 * v b 1 * v c 2) * (Matrix.of ![v a, v b, v c]).det
  have hdetM : M.det = ∑ a : ι, ∑ b : ι, ∑ c : ι, f a b c := by
    rw [Matrix.det_fin_three]
    simp only [hM, sum_mul_sum_mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro c _
    simp only [f, Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val]
    ring
  have hsym : ∀ a b c : ι,
      f a b c + f a c b + f b a c + f b c a + f c a b + f c b a =
        w a * w b * w c * (Matrix.of ![v a, v b, v c]).det ^ 2 := by
    intro a b c
    simp only [f, Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val]
    ring
  have s1 : (∑ a : ι, ∑ b : ι, ∑ c : ι, f a c b) = ∑ a : ι, ∑ b : ι, ∑ c : ι, f a b c :=
    Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have s2 : (∑ a : ι, ∑ b : ι, ∑ c : ι, f b a c) = ∑ a : ι, ∑ b : ι, ∑ c : ι, f a b c :=
    Finset.sum_comm
  have s3 : (∑ a : ι, ∑ b : ι, ∑ c : ι, f b c a) = ∑ a : ι, ∑ b : ι, ∑ c : ι, f a b c := by
    calc (∑ a, ∑ b, ∑ c, f b c a) = ∑ b, ∑ a, ∑ c, f b c a := Finset.sum_comm
      _ = ∑ b, ∑ c, ∑ a, f b c a := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have s4 : (∑ a : ι, ∑ b : ι, ∑ c : ι, f c a b) = ∑ a : ι, ∑ b : ι, ∑ c : ι, f a b c := by
    calc (∑ a, ∑ b, ∑ c, f c a b) = ∑ a, ∑ c, ∑ b, f c a b := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ c, ∑ a, ∑ b, f c a b := Finset.sum_comm
  have s5 : (∑ a : ι, ∑ b : ι, ∑ c : ι, f c b a) = ∑ a : ι, ∑ b : ι, ∑ c : ι, f a b c := by
    calc (∑ a, ∑ b, ∑ c, f c b a) = ∑ a, ∑ c, ∑ b, f c b a := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ c, ∑ a, ∑ b, f c b a := Finset.sum_comm
      _ = ∑ c, ∑ b, ∑ a, f c b a := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have h6 : (∑ a : ι, ∑ b : ι, ∑ c : ι,
      w a * w b * w c * (Matrix.of ![v a, v b, v c]).det ^ 2) =
      6 * ∑ a : ι, ∑ b : ι, ∑ c : ι, f a b c := by
    simp_rw [← hsym, Finset.sum_add_distrib, s1, s2, s3, s4, s5]
    ring
  rw [hdetM, h6]
  ring

lemma greedy_basis_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → (Fin 3 → ℝ)) (c z : ι → ℝ)
    (hv_ne : ∀ i, v i ≠ 0)
    (hspan : Submodule.span ℝ (Set.range v) = ⊤)
    (hc_le : ∀ I : Finset ι, ∑ i ∈ I, c i ≤ (rankOf v I : ℝ))
    (hc_sum : ∑ i : ι, c i = 3) :
    ∃ a b d : ι, (Matrix.of ![v a, v b, v d]).det ≠ 0 ∧
      ∑ i : ι, c i * z i ≤ z a + z b + z d := by
  let n := Fintype.card ι
  have hn3 : 3 ≤ n := by
    have h3 := rankOf_univ v hspan
    have hle : rankOf v Finset.univ ≤ Fintype.card ι := by
      unfold rankOf
      have h1 : Module.finrank ℝ (Submodule.span ℝ (Set.range v)) ≤ Fintype.card ι :=
        finrank_span_le_card (Set.range v) |>.trans (by
          have := Set.toFinset_card (Set.range v)
          simpa using (Finset.card_image_le (s := Finset.univ) (f := v)))
      rw [Finset.coe_univ, Set.image_univ]
      exact h1
    omega
  have : NeZero n := ⟨by omega⟩
  obtain ⟨e₀⟩ := Fintype.truncEquivFin ι
  let σ := Tuple.sort (fun k : Fin n => -(z (e₀.symm k)))
  let e : Fin n ≃ ι := σ.trans e₀.symm
  have he_anti : Antitone (fun k : Fin n => z (e k)) := by
    intro j k hjk
    have hmono := Tuple.monotone_sort (fun k : Fin n => -(z (e₀.symm k))) hjk
    simp only [Function.comp_apply] at hmono
    change z (e₀.symm (σ k)) ≤ z (e₀.symm (σ j))
    linarith
  let pref : Fin n → Finset ι := fun k => (Finset.univ.filter (fun j : Fin n => j ≤ k)).image e
  have hpref0 : rankOf v (pref ⟨0, by omega⟩) = 1 := by
    have hset : pref ⟨0, by omega⟩ = {e ⟨0, by omega⟩} := by
      ext x
      simp only [pref, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · rintro ⟨j, hj, rfl⟩
        have hj0 : j = ⟨0, by omega⟩ := Fin.le_antisymm hj (Fin.zero_le j)
        rw [hj0]
      · rintro rfl
        exact ⟨⟨0, by omega⟩, le_rfl, rfl⟩
    rw [hset]
    exact rankOf_singleton v (hv_ne _)
  have hpref_last : rankOf v (pref ⟨n - 1, by omega⟩) = 3 := by
    have hset : pref ⟨n - 1, by omega⟩ = Finset.univ := by
      ext x
      simp only [pref, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      refine ⟨e.symm x, ?_, Equiv.apply_symm_apply e x⟩
      change (e.symm x).1 ≤ n - 1
      have := (e.symm x).2
      omega
    rw [hset]
    exact rankOf_univ v hspan
  have hpref_mono : Monotone (fun k : Fin n => rankOf v (pref k)) := by
    intro j k hjk
    apply rankOf_mono
    apply Finset.image_subset_image
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
    exact hm.trans hjk
  have hpref_step : ∀ (k : Fin n) (hk : k.1 + 1 < n),
      rankOf v (pref ⟨k.1 + 1, hk⟩) ≤ rankOf v (pref k) + 1 := by
    intro k hk
    have hsub : pref ⟨k.1 + 1, hk⟩ ⊆ insert (e ⟨k.1 + 1, hk⟩) (pref k) := by
      intro x hx
      simp only [pref, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      by_cases hjeq : j = ⟨k.1 + 1, hk⟩
      · rw [hjeq]; exact Finset.mem_insert_self _ _
      · apply Finset.mem_insert_of_mem
        simp only [pref, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨j, ?_, rfl⟩
        change j.1 ≤ k.1
        have hj1 : j.1 ≤ k.1 + 1 := hj
        have hjne : j.1 ≠ k.1 + 1 := fun h => hjeq (Fin.ext h)
        omega
    calc rankOf v (pref ⟨k.1 + 1, hk⟩)
        ≤ rankOf v (insert (e ⟨k.1 + 1, hk⟩) (pref k)) := rankOf_mono v hsub
      _ = rankOf v ({e ⟨k.1 + 1, hk⟩} ∪ pref k) := by rw [Finset.singleton_union]
      _ ≤ rankOf v {e ⟨k.1 + 1, hk⟩} + rankOf v (pref k) := by
          have := rankOf_submod v {e ⟨k.1 + 1, hk⟩} (pref k)
          omega
      _ = rankOf v (pref k) + 1 := by
          rw [rankOf_singleton v (hv_ne _)]; omega
  let S2 := Finset.univ.filter (fun k : Fin n => 2 ≤ rankOf v (pref k))
  have hS2ne : S2.Nonempty := ⟨⟨n - 1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩
  let k2 := S2.min' hS2ne
  let S3 := Finset.univ.filter (fun k : Fin n => 3 ≤ rankOf v (pref k))
  have hS3ne : S3.Nonempty := ⟨⟨n - 1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩
  let k3 := S3.min' hS3ne
  have hk2_ge : 2 ≤ rankOf v (pref k2) := (Finset.mem_filter.mp (Finset.min'_mem S2 hS2ne)).2
  have hk3_ge : 3 ≤ rankOf v (pref k3) := (Finset.mem_filter.mp (Finset.min'_mem S3 hS3ne)).2
  have hk2_pos : 0 < k2.1 := by
    by_contra h0
    have hk20 : k2 = ⟨0, by omega⟩ := Fin.ext (by show k2.1 = 0; omega)
    rw [hk20, hpref0] at hk2_ge
    omega
  have hk2_prev : rankOf v (pref ⟨k2.1 - 1, by omega⟩) = 1 := by
    have hlt : (⟨k2.1 - 1, by omega⟩ : Fin n) < k2 := by
      change k2.1 - 1 < k2.1; omega
    have hnot : ¬ (2 ≤ rankOf v (pref ⟨k2.1 - 1, by omega⟩)) := by
      intro hge
      have hle := Finset.min'_le S2 ⟨k2.1 - 1, by omega⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hge⟩)
      exact not_le_of_gt hlt hle
    have hge1 : 1 ≤ rankOf v (pref ⟨k2.1 - 1, by omega⟩) := by
      calc 1 = rankOf v (pref ⟨0, by omega⟩) := hpref0.symm
        _ ≤ rankOf v (pref ⟨k2.1 - 1, by omega⟩) := hpref_mono (Fin.zero_le _)
    omega
  have hk2_eq : rankOf v (pref k2) = 2 := by
    have hst := hpref_step ⟨k2.1 - 1, by omega⟩ (by omega : (k2.1 - 1) + 1 < n)
    have heq : (⟨(k2.1 - 1) + 1, by omega⟩ : Fin n) = k2 := Fin.ext (by show (k2.1 - 1) + 1 = k2.1; omega)
    rw [heq, hk2_prev] at hst
    omega
  have hk2_lt_k3 : k2 < k3 := by
    by_contra hle
    push Not at hle
    have hmono : rankOf v (pref k3) ≤ rankOf v (pref k2) := hpref_mono hle
    omega
  have hk3_prev : rankOf v (pref ⟨k3.1 - 1, by omega⟩) = 2 := by
    have hlt : (⟨k3.1 - 1, by omega⟩ : Fin n) < k3 := by
      change k3.1 - 1 < k3.1; omega
    have hnot : ¬ (3 ≤ rankOf v (pref ⟨k3.1 - 1, by omega⟩)) := by
      intro hge
      have hle := Finset.min'_le S3 ⟨k3.1 - 1, by omega⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hge⟩)
      exact not_le_of_gt hlt hle
    have hge2 : 2 ≤ rankOf v (pref ⟨k3.1 - 1, by omega⟩) := by
      calc 2 = rankOf v (pref k2) := hk2_eq.symm
        _ ≤ rankOf v (pref ⟨k3.1 - 1, by omega⟩) := hpref_mono (by
            change k2.1 ≤ k3.1 - 1; have : k2.1 < k3.1 := hk2_lt_k3; omega)
    omega
  have hk3_eq : rankOf v (pref k3) = 3 := by
    have hle : rankOf v (pref k3) ≤ 3 := by
      calc rankOf v (pref k3) ≤ rankOf v (pref ⟨n - 1, by omega⟩) :=
            hpref_mono (by change k3.1 ≤ n - 1; have := k3.2; omega)
        _ = 3 := hpref_last
    omega
  have hdet_ne : (Matrix.of ![v (e ⟨0, by omega⟩), v (e k2), v (e k3)]).det ≠ 0 := by
    set u0 := v (e ⟨0, by omega⟩)
    set u1 := v (e k2)
    set u2 := v (e k3)
    have hnot1 : u1 ∉ Submodule.span ℝ ({u0} : Set (Fin 3 → ℝ)) := by
      intro hmem
      have hle : Submodule.span ℝ ({u0} : Set (Fin 3 → ℝ)) =
          Submodule.span ℝ (v '' (pref ⟨k2.1 - 1, by omega⟩ : Set ι)) := by
        apply Submodule.eq_of_le_of_finrank_eq
        · rw [Submodule.span_le, Set.singleton_subset_iff]
          apply Submodule.subset_span
          refine ⟨e ⟨0, by omega⟩, ?_, rfl⟩
          simp only [pref, Finset.mem_coe, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨⟨0, by omega⟩, Fin.zero_le _, rfl⟩
        · rw [finrank_span_singleton (hv_ne _)]
          exact hk2_prev.symm
      rw [hle] at hmem
      have hspan_le : Submodule.span ℝ (v '' (pref k2 : Set ι)) ≤
          Submodule.span ℝ (v '' (pref ⟨k2.1 - 1, by omega⟩ : Set ι)) := by
        rw [Submodule.span_le]
        rintro x ⟨i, hi, rfl⟩
        simp only [pref, Finset.mem_coe, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        obtain ⟨j, hj, rfl⟩ := hi
        by_cases hjk : j = k2
        · rw [hjk]; exact hmem
        · apply Submodule.subset_span
          refine ⟨e j, ?_, rfl⟩
          simp only [pref, Finset.mem_coe, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨j, by change j.1 ≤ k2.1 - 1; have : j.1 ≤ k2.1 := hj; have : j.1 ≠ k2.1 := fun h => hjk (Fin.ext h); omega, rfl⟩
      have hfr := Submodule.finrank_mono hspan_le
      change rankOf v (pref k2) ≤ rankOf v (pref ⟨k2.1 - 1, by omega⟩) at hfr
      omega
    have hnot2 : u2 ∉ Submodule.span ℝ ({u0, u1} : Set (Fin 3 → ℝ)) := by
      intro hmem
      have hfr01 : Module.finrank ℝ (Submodule.span ℝ ({u0, u1} : Set (Fin 3 → ℝ))) = 2 := by
        have hli : LinearIndependent ℝ ![u0, u1] := by
          rw [Fintype.linearIndependent_iff]
          intro g hg
          have hg1 : g 1 = 0 := by
            by_contra h1
            have : u1 = (-(g 1)⁻¹ * g 0) • u0 := by
              have hsum : g 0 • u0 + g 1 • u1 = 0 := by simpa [Fin.sum_univ_two] using hg
              have h1' : g 1 • u1 = -(g 0 • u0) := eq_neg_of_add_eq_zero_right hsum
              calc u1 = (g 1)⁻¹ • (g 1 • u1) := by rw [inv_smul_smul₀ h1]
                _ = (g 1)⁻¹ • (-(g 0 • u0)) := by rw [h1']
                _ = (-(g 1)⁻¹ * g 0) • u0 := by simp [smul_neg, smul_smul, neg_mul]
            exact hnot1 (this ▸ Submodule.smul_mem _ _ (Submodule.subset_span rfl))
          have hg0 : g 0 = 0 := by
            have hsum : g 0 • u0 + g 1 • u1 = 0 := by simpa [Fin.sum_univ_two] using hg
            rw [hg1, zero_smul, add_zero] at hsum
            exact (smul_eq_zero.mp hsum).resolve_right (hv_ne _)
          intro j; fin_cases j <;> assumption
        have hfin := finrank_span_eq_card hli
        have hrange : Set.range ![u0, u1] = ({u0, u1} : Set (Fin 3 → ℝ)) := by
          ext x; simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor
          · rintro ⟨j, rfl⟩; fin_cases j <;> simp
          · rintro (rfl | rfl); exact ⟨0, rfl⟩; exact ⟨1, rfl⟩
        rw [hrange] at hfin
        simpa using hfin
      have hle : Submodule.span ℝ ({u0, u1} : Set (Fin 3 → ℝ)) =
          Submodule.span ℝ (v '' (pref ⟨k3.1 - 1, by omega⟩ : Set ι)) := by
        apply Submodule.eq_of_le_of_finrank_eq
        · rw [Submodule.span_le]
          rintro x (rfl | rfl)
          · apply Submodule.subset_span
            refine ⟨e ⟨0, by omega⟩, ?_, rfl⟩
            simp only [pref, Finset.mem_coe, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨⟨0, by omega⟩, Fin.zero_le _, rfl⟩
          · apply Submodule.subset_span
            refine ⟨e k2, ?_, rfl⟩
            simp only [pref, Finset.mem_coe, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨k2, by change k2.1 ≤ k3.1 - 1; have : k2.1 < k3.1 := hk2_lt_k3; omega, rfl⟩
        · rw [hfr01]; exact hk3_prev.symm
      rw [hle] at hmem
      have hspan_le : Submodule.span ℝ (v '' (pref k3 : Set ι)) ≤
          Submodule.span ℝ (v '' (pref ⟨k3.1 - 1, by omega⟩ : Set ι)) := by
        rw [Submodule.span_le]
        rintro x ⟨i, hi, rfl⟩
        simp only [pref, Finset.mem_coe, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        obtain ⟨j, hj, rfl⟩ := hi
        by_cases hjk : j = k3
        · rw [hjk]; exact hmem
        · apply Submodule.subset_span
          refine ⟨e j, ?_, rfl⟩
          simp only [pref, Finset.mem_coe, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨j, by change j.1 ≤ k3.1 - 1; have : j.1 ≤ k3.1 := hj; have : j.1 ≠ k3.1 := fun h => hjk (Fin.ext h); omega, rfl⟩
      have hfr := Submodule.finrank_mono hspan_le
      change rankOf v (pref k3) ≤ rankOf v (pref ⟨k3.1 - 1, by omega⟩) at hfr
      omega
    have hli3 : LinearIndependent ℝ ![u0, u1, u2] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      have hsum : g 0 • u0 + g 1 • u1 + g 2 • u2 = 0 := by
        simpa [Fin.sum_univ_three, add_assoc] using hg
      have hg2 : g 2 = 0 := by
        by_contra h2
        have : u2 = (-(g 2)⁻¹ * g 0) • u0 + (-(g 2)⁻¹ * g 1) • u1 := by
          have h2' : g 2 • u2 = -(g 0 • u0 + g 1 • u1) := eq_neg_of_add_eq_zero_right hsum
          calc u2 = (g 2)⁻¹ • (g 2 • u2) := by rw [inv_smul_smul₀ h2]
            _ = (g 2)⁻¹ • (-(g 0 • u0 + g 1 • u1)) := by rw [h2']
            _ = (-(g 2)⁻¹ * g 0) • u0 + (-(g 2)⁻¹ * g 1) • u1 := by
                simp [smul_neg, smul_add, smul_smul, neg_mul, add_comm]
        exact hnot2 (this ▸ Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
          (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))))
      rw [hg2, zero_smul, add_zero] at hsum
      have hg1 : g 1 = 0 := by
        by_contra h1
        have : u1 = (-(g 1)⁻¹ * g 0) • u0 := by
          have h1' : g 1 • u1 = -(g 0 • u0) := eq_neg_of_add_eq_zero_right hsum
          calc u1 = (g 1)⁻¹ • (g 1 • u1) := by rw [inv_smul_smul₀ h1]
            _ = (g 1)⁻¹ • (-(g 0 • u0)) := by rw [h1']
            _ = (-(g 1)⁻¹ * g 0) • u0 := by simp [smul_neg, smul_smul, neg_mul]
        exact hnot1 (this ▸ Submodule.smul_mem _ _ (Submodule.subset_span rfl))
      rw [hg1, zero_smul, add_zero] at hsum
      have hg0 : g 0 = 0 := (smul_eq_zero.mp hsum).resolve_right (hv_ne _)
      intro j; fin_cases j <;> assumption
    have hunit : IsUnit (Matrix.of ![u0, u1, u2]) :=
      Matrix.linearIndependent_rows_iff_isUnit.mp hli3
    exact (Matrix.isUnit_iff_isUnit_det _).mp hunit |>.ne_zero
  refine ⟨e ⟨0, by omega⟩, e k2, e k3, hdet_ne, ?_⟩
  have hsum_eq : ∑ i : ι, c i * z i = ∑ j : Fin n, c (e j) * z (e j) :=
    (Equiv.sum_comp e (fun i => c i * z i)).symm
  rw [hsum_eq]
  have hc_sum_e : ∑ j : Fin n, c (e j) = 3 := by
    rw [Equiv.sum_comp e c]; exact hc_sum
  have habel : ∀ (f g : Fin n → ℝ),
      ∑ j : Fin n, f j * g j =
        (∑ j : Fin n, f j) * g ⟨n - 1, by omega⟩ +
          ∑ j : Fin (n - 1), (g ⟨j.1, by omega⟩ - g ⟨j.1 + 1, by omega⟩) *
            (∑ m ∈ Finset.univ.filter (fun m : Fin n => m.1 ≤ j.1), f m) := by
    intro f g
    have h1 : ∀ m : Fin n,
        g m = g ⟨n - 1, by omega⟩ +
          ∑ j ∈ Finset.univ.filter (fun j : Fin (n - 1) => m.1 ≤ j.1),
            (g ⟨j.1, by omega⟩ - g ⟨j.1 + 1, by omega⟩) := by
      intro m
      suffices ∀ d : ℕ, ∀ (hm : d < n),
          g ⟨d, hm⟩ = g ⟨n - 1, by omega⟩ +
            ∑ j ∈ Finset.univ.filter (fun j : Fin (n - 1) => d ≤ j.1),
              (g ⟨j.1, by omega⟩ - g ⟨j.1 + 1, by omega⟩) from this m.1 m.2
      intro d
      induction hd : (n - 1) - d generalizing d with
      | zero =>
        intro hm
        have hdeq : d = n - 1 := by omega
        subst hdeq
        have hempty : Finset.univ.filter (fun j : Fin (n - 1) => n - 1 ≤ j.1) = ∅ := by
          ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          omega
        rw [hempty]; simp
      | succ k ih =>
        intro hm
        have hd1 : d + 1 < n := by omega
        have hrec := ih (d + 1) (by omega) hd1
        have hsplit : Finset.univ.filter (fun j : Fin (n - 1) => d ≤ j.1) =
            insert ⟨d, by omega⟩ (Finset.univ.filter (fun j : Fin (n - 1) => d + 1 ≤ j.1)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
          omega
        have hnotmem : (⟨d, by omega⟩ : Fin (n - 1)) ∉
            Finset.univ.filter (fun j : Fin (n - 1) => d + 1 ≤ j.1) := by
          simp
        rw [hsplit, Finset.sum_insert hnotmem]
        linarith
    calc ∑ m : Fin n, f m * g m
        = ∑ m : Fin n, f m * (g ⟨n - 1, by omega⟩ +
            ∑ j ∈ Finset.univ.filter (fun j : Fin (n - 1) => m.1 ≤ j.1),
              (g ⟨j.1, by omega⟩ - g ⟨j.1 + 1, by omega⟩)) := by
            apply Finset.sum_congr rfl; intro m _; rw [h1 m]
      _ = (∑ m : Fin n, f m) * g ⟨n - 1, by omega⟩ +
            ∑ m : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin (n - 1) => m.1 ≤ j.1),
              f m * (g ⟨j.1, by omega⟩ - g ⟨j.1 + 1, by omega⟩) := by
            simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.mul_sum]
      _ = (∑ m : Fin n, f m) * g ⟨n - 1, by omega⟩ +
            ∑ j : Fin (n - 1), (g ⟨j.1, by omega⟩ - g ⟨j.1 + 1, by omega⟩) *
              (∑ m ∈ Finset.univ.filter (fun m : Fin n => m.1 ≤ j.1), f m) := by
            congr 1
            simp_rw [Finset.sum_filter]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro m _
            split_ifs <;> ring
  rw [habel (fun j => c (e j)) (fun j => z (e j)), hc_sum_e]
  have hstep_le :
      ∑ j : Fin (n - 1), (z (e ⟨j.1, by omega⟩) - z (e ⟨j.1 + 1, by omega⟩)) *
          (∑ m ∈ Finset.univ.filter (fun m : Fin n => m.1 ≤ j.1), c (e m)) ≤
      ∑ j : Fin (n - 1), (z (e ⟨j.1, by omega⟩) - z (e ⟨j.1 + 1, by omega⟩)) *
          (rankOf v (pref ⟨j.1, by omega⟩) : ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left
    · have hceq : ∑ m ∈ Finset.univ.filter (fun m : Fin n => m.1 ≤ j.1), c (e m) =
          ∑ i ∈ pref ⟨j.1, by omega⟩, c i := by
        rw [Finset.sum_image (fun a _ b _ hab => e.injective hab)]
        rfl
      rw [hceq]
      exact hc_le (pref ⟨j.1, by omega⟩)
    · have := he_anti (show (⟨j.1, by omega⟩ : Fin n) ≤ ⟨j.1 + 1, by omega⟩ by change j.1 ≤ j.1 + 1; omega)
      linarith
  let ind : Fin n → ℝ := fun m =>
    (if m = (0 : Fin n) then 1 else 0) +
    (if m = k2 then 1 else 0) +
    (if m = k3 then 1 else 0)
  have hind_sum : ∑ m : Fin n, ind m = 3 := by
    simp [ind, Finset.sum_add_distrib, Finset.sum_ite_eq']; norm_num
  have hind_dot : ∑ m : Fin n, ind m * z (e m) = z (e ⟨0, by omega⟩) + z (e k2) + z (e k3) := by
    change ∑ m : Fin n, ind m * z (e m) = z (e (0 : Fin n)) + z (e k2) + z (e k3)
    simp [ind, add_mul, Finset.sum_add_distrib]
  have hind_pref : ∀ j : Fin (n - 1),
      (∑ m ∈ Finset.univ.filter (fun m : Fin n => m.1 ≤ j.1), ind m) =
        (rankOf v (pref ⟨j.1, by omega⟩) : ℝ) := by
    intro j
    have h0 : (∑ m ∈ Finset.univ.filter (fun m : Fin n => m.1 ≤ j.1),
        if m = (0 : Fin n) then (1 : ℝ) else 0) = 1 := by
      rw [Finset.sum_ite_eq']
      simp
    have h1 : (∑ m ∈ Finset.univ.filter (fun m : Fin n => m.1 ≤ j.1),
        if m = k2 then (1 : ℝ) else 0) = if k2.1 ≤ j.1 then 1 else 0 := by
      rw [Finset.sum_ite_eq']
      simp
    have h2 : (∑ m ∈ Finset.univ.filter (fun m : Fin n => m.1 ≤ j.1),
        if m = k3 then (1 : ℝ) else 0) = if k3.1 ≤ j.1 then 1 else 0 := by
      rw [Finset.sum_ite_eq']
      simp
    have hsum_ind : ∑ m ∈ Finset.univ.filter (fun m : Fin n => m.1 ≤ j.1), ind m =
        1 + (if k2.1 ≤ j.1 then (1 : ℝ) else 0) + (if k3.1 ≤ j.1 then (1 : ℝ) else 0) := by
      simp only [ind, Finset.sum_add_distrib, h0, h1, h2]
    rw [hsum_ind]
    by_cases hjk2 : j.1 < k2.1
    · have hjk3 : j.1 < k3.1 := lt_trans hjk2 hk2_lt_k3
      have hr : rankOf v (pref ⟨j.1, by omega⟩) = 1 := by
        have hle1 : rankOf v (pref ⟨j.1, by omega⟩) ≤ 1 := by
          calc rankOf v (pref ⟨j.1, by omega⟩) ≤ rankOf v (pref ⟨k2.1 - 1, by omega⟩) :=
                hpref_mono (by change j.1 ≤ k2.1 - 1; omega)
            _ = 1 := hk2_prev
        have hge1 : 1 ≤ rankOf v (pref ⟨j.1, by omega⟩) := by
          calc 1 = rankOf v (pref ⟨0, by omega⟩) := hpref0.symm
            _ ≤ rankOf v (pref ⟨j.1, by omega⟩) := hpref_mono (Fin.zero_le _)
        omega
      simp [not_le.mpr hjk2, not_le.mpr hjk3, hr]
    · push Not at hjk2
      by_cases hjk3 : j.1 < k3.1
      · have hr : rankOf v (pref ⟨j.1, by omega⟩) = 2 := by
          have hle2 : rankOf v (pref ⟨j.1, by omega⟩) ≤ 2 := by
            calc rankOf v (pref ⟨j.1, by omega⟩) ≤ rankOf v (pref ⟨k3.1 - 1, by omega⟩) :=
                  hpref_mono (by change j.1 ≤ k3.1 - 1; omega)
              _ = 2 := hk3_prev
          have hge2 : 2 ≤ rankOf v (pref ⟨j.1, by omega⟩) := by
            calc 2 = rankOf v (pref k2) := hk2_eq.symm
              _ ≤ rankOf v (pref ⟨j.1, by omega⟩) := hpref_mono (by change k2.1 ≤ j.1; omega)
          omega
        simp [hjk2, not_le.mpr hjk3, hr]; norm_num
      · push Not at hjk3
        have hr : rankOf v (pref ⟨j.1, by omega⟩) = 3 := by
          have hle3 : rankOf v (pref ⟨j.1, by omega⟩) ≤ 3 := by
            calc rankOf v (pref ⟨j.1, by omega⟩) ≤ rankOf v (pref ⟨n - 1, by omega⟩) :=
                  hpref_mono (by change j.1 ≤ n - 1; omega)
              _ = 3 := hpref_last
          have hge3 : 3 ≤ rankOf v (pref ⟨j.1, by omega⟩) := by
            calc 3 = rankOf v (pref k3) := hk3_eq.symm
              _ ≤ rankOf v (pref ⟨j.1, by omega⟩) := hpref_mono (by change k3.1 ≤ j.1; omega)
          omega
        simp [hjk2, hjk3, hr]; norm_num
  have habel_ind := habel ind (fun j => z (e j))
  rw [hind_dot, hind_sum] at habel_ind
  simp_rw [hind_pref] at habel_ind
  linarith

noncomputable def Mmat {ι : Type*} [Fintype ι] (v : ι → (Fin 3 → ℝ)) (z : ι → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ i : ι, Real.exp (z i) • Matrix.vecMulVec (v i) (v i)

lemma Mmat_isHermitian {ι : Type*} [Fintype ι] (v : ι → (Fin 3 → ℝ)) (z : ι → ℝ) :
    (Mmat v z).IsHermitian := by
  ext j k
  simp [Mmat, Matrix.conjTranspose_apply, Matrix.sum_apply, Matrix.vecMulVec, mul_comm]

lemma Mmat_quadForm {ι : Type*} [Fintype ι] (v : ι → (Fin 3 → ℝ)) (z : ι → ℝ) (x : Fin 3 → ℝ) :
    dotProduct x (Mmat v z *ᵥ x) = ∑ i : ι, Real.exp (z i) * (dotProduct (v i) x) ^ 2 := by
  simp only [Mmat, Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  have h : dotProduct x (Matrix.vecMulVec (v i) (v i) *ᵥ x) = (dotProduct (v i) x) ^ 2 := by
    simp [Matrix.vecMulVec, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  rw [h]

lemma Mmat_posDef {ι : Type*} [Fintype ι] (v : ι → (Fin 3 → ℝ)) (z : ι → ℝ)
    (hspan : Submodule.span ℝ (Set.range v) = ⊤) :
    (Mmat v z).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨Mmat_isHermitian v z, fun x hx => ?_⟩
  simp only [star_trivial]
  rw [Mmat_quadForm]
  have hnonneg : ∀ i : ι, 0 ≤ Real.exp (z i) * (dotProduct (v i) x) ^ 2 := fun i => by positivity
  by_contra hle
  push Not at hle
  have hsum0 : ∑ i : ι, Real.exp (z i) * (dotProduct (v i) x) ^ 2 = 0 :=
    le_antisymm hle (Finset.sum_nonneg fun i _ => hnonneg i)
  have hall0 : ∀ i : ι, dotProduct (v i) x = 0 := by
    intro i
    have hi0 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp hsum0 i (Finset.mem_univ i)
    have hsq0 : (dotProduct (v i) x) ^ 2 = 0 :=
      (mul_eq_zero.mp hi0).resolve_left (Real.exp_pos _).ne'
    exact sq_eq_zero_iff.mp hsq0
  have hker : ∀ y : Fin 3 → ℝ, dotProduct y x = 0 := by
    intro y
    have hy : y ∈ Submodule.span ℝ (Set.range v) := hspan ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨i, rfl⟩ := hu
      exact hall0 i
    | zero => simp
    | add u w _ _ hu hw => simp [add_dotProduct, hu, hw]
    | smul r u _ hu => simp [smul_dotProduct, hu]
  have hxx := hker x
  apply hx
  ext j
  have hsq : (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 = 0 := by
    simpa [dotProduct, Fin.sum_univ_three, sq] using hxx
  fin_cases j <;> simp <;> nlinarith

lemma Mmat_det_pos {ι : Type*} [Fintype ι] (v : ι → (Fin 3 → ℝ)) (z : ι → ℝ)
    (hspan : Submodule.span ℝ (Set.range v) = ⊤) :
    0 < (Mmat v z).det :=
  (Mmat_posDef v z hspan).det_pos

lemma exists_small_gradient {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → (Fin 3 → ℝ)) (c : ι → ℝ)
    (hv_ne : ∀ i, v i ≠ 0)
    (hspan : Submodule.span ℝ (Set.range v) = ⊤)
    (hc_le : ∀ I : Finset ι, ∑ i ∈ I, c i ≤ (rankOf v I : ℝ))
    (hc_sum : ∑ i : ι, c i = 3)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ z : ι → ℝ, ∀ i : ι,
      |Real.exp (z i) * dotProduct (v i) ((Mmat v z)⁻¹ *ᵥ v i) - c i| < δ := by
  let Phi : (ι → ℝ) → ℝ := fun z => Real.log (Mmat v z).det - ∑ i : ι, c i * z i
  let good := (Finset.univ : Finset (ι × ι × ι)).filter
    (fun t => (Matrix.of ![v t.1, v t.2.1, v t.2.2]).det ≠ 0)
  have hgood_ne : good.Nonempty := by
    obtain ⟨a, b, d, hdet, _⟩ := greedy_basis_bound v c 0 hv_ne hspan hc_le hc_sum
    exact ⟨(a, b, d), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdet⟩⟩
  let detSqs := good.image (fun t => (Matrix.of ![v t.1, v t.2.1, v t.2.2]).det ^ 2)
  have hdetSqs_ne : detSqs.Nonempty := hgood_ne.image _
  set amin : ℝ := (1 / 6 : ℝ) * detSqs.min' hdetSqs_ne
  have hamin_pos : 0 < amin := by
    obtain ⟨t, ht, hteq⟩ := Finset.mem_image.mp (Finset.min'_mem detSqs hdetSqs_ne)
    have hne := (Finset.mem_filter.mp ht).2
    have hsq : 0 < (Matrix.of ![v t.1, v t.2.1, v t.2.2]).det ^ 2 := sq_pos_of_ne_zero hne
    rw [hteq] at hsq
    positivity
  set L : ℝ := Real.log amin
  have hPhi_ge : ∀ z : ι → ℝ, L ≤ Phi z := by
    intro z
    obtain ⟨a, b, d, hdet, hcz⟩ := greedy_basis_bound v c z hv_ne hspan hc_le hc_sum
    have hdet_eq := det_sum_vecMulVec_fin3 v (fun i => Real.exp (z i))
    have hsingle : (1 / 6 : ℝ) * (Real.exp (z a) * Real.exp (z b) * Real.exp (z d) *
        (Matrix.of ![v a, v b, v d]).det ^ 2) ≤ (Mmat v z).det := by
      change _ ≤ (∑ i : ι, Real.exp (z i) • Matrix.vecMulVec (v i) (v i)).det
      rw [hdet_eq]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hterm_nonneg : ∀ x y w : ι,
          0 ≤ Real.exp (z x) * Real.exp (z y) * Real.exp (z w) *
            (Matrix.of ![v x, v y, v w]).det ^ 2 := fun _ _ _ => by positivity
      calc Real.exp (z a) * Real.exp (z b) * Real.exp (z d) * (Matrix.of ![v a, v b, v d]).det ^ 2
          ≤ ∑ w : ι, Real.exp (z a) * Real.exp (z b) * Real.exp (z w) *
              (Matrix.of ![v a, v b, v w]).det ^ 2 :=
            Finset.single_le_sum (fun w _ => hterm_nonneg a b w) (Finset.mem_univ d)
        _ ≤ ∑ y : ι, ∑ w : ι, Real.exp (z a) * Real.exp (z y) * Real.exp (z w) *
              (Matrix.of ![v a, v y, v w]).det ^ 2 :=
            Finset.single_le_sum (fun y _ => Finset.sum_nonneg fun w _ => hterm_nonneg a y w) (Finset.mem_univ b)
        _ ≤ ∑ x : ι, ∑ y : ι, ∑ w : ι, Real.exp (z x) * Real.exp (z y) * Real.exp (z w) *
              (Matrix.of ![v x, v y, v w]).det ^ 2 :=
            Finset.single_le_sum (fun x _ => Finset.sum_nonneg fun y _ =>
              Finset.sum_nonneg fun w _ => hterm_nonneg x y w) (Finset.mem_univ a)
    have hamin_le : amin ≤ (1 / 6 : ℝ) * (Matrix.of ![v a, v b, v d]).det ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.min'_le detSqs _ (Finset.mem_image.mpr
        ⟨(a, b, d), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdet⟩, rfl⟩)
    have hexp_eq : Real.exp (z a) * Real.exp (z b) * Real.exp (z d) =
        Real.exp (z a + z b + z d) := by
      rw [Real.exp_add, Real.exp_add]
    have hbound : amin * Real.exp (∑ i : ι, c i * z i) ≤ (Mmat v z).det := by
      calc amin * Real.exp (∑ i : ι, c i * z i)
          ≤ amin * Real.exp (z a + z b + z d) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hcz) hamin_pos.le
        _ ≤ ((1 / 6 : ℝ) * (Matrix.of ![v a, v b, v d]).det ^ 2) * Real.exp (z a + z b + z d) :=
            mul_le_mul_of_nonneg_right hamin_le (Real.exp_pos _).le
        _ = (1 / 6 : ℝ) * (Real.exp (z a) * Real.exp (z b) * Real.exp (z d) *
              (Matrix.of ![v a, v b, v d]).det ^ 2) := by
            rw [hexp_eq]; ring
        _ ≤ (Mmat v z).det := hsingle
    have hlog := Real.log_le_log (by positivity) hbound
    rw [Real.log_mul hamin_pos.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
    dsimp only [Phi, L]
    linarith
  set gap : ℝ := Phi 0 - L + 1
  have hgap_pos : 0 < gap := by
    have := hPhi_ge 0
    dsimp only [gap]
    linarith
  set ρ : ℝ := δ ^ 2 / (4 * gap)
  have hρ_pos : 0 < ρ := by positivity
  let F : (ι → ℝ) → ℝ := fun z => Phi z + (ρ / 2) * ∑ i : ι, (z i) ^ 2
  have hcont_M : Continuous (fun z : ι → ℝ => Mmat v z) := by
    apply continuous_finsetSum
    intro i _
    exact (Real.continuous_exp.comp (continuous_apply i)).smul continuous_const
  have hcont_F : Continuous F := by
    have hdet : Continuous (fun z : ι → ℝ => (Mmat v z).det) :=
      Continuous.matrix_det hcont_M
    have hlog : Continuous (fun z : ι → ℝ => Real.log (Mmat v z).det) :=
      Continuous.log hdet (fun z => (Mmat_det_pos v z hspan).ne')
    have hlin : Continuous (fun z : ι → ℝ => ∑ i : ι, c i * z i) :=
      continuous_finsetSum Finset.univ fun i _ => continuous_const.mul (continuous_apply i)
    have hquad : Continuous (fun z : ι → ℝ => ∑ i : ι, (z i) ^ 2) :=
      continuous_finsetSum Finset.univ fun i _ => (continuous_apply i).pow 2
    exact (hlog.sub hlin).add (continuous_const.mul hquad)
  set R : ℝ := Real.sqrt (2 * gap / ρ)
  have hR_nonneg : 0 ≤ R := Real.sqrt_nonneg _
  let B : Set (ι → ℝ) := Set.univ.pi (fun _ : ι => Set.Icc (-R) R)
  have hB0 : (0 : ι → ℝ) ∈ B := fun _ _ => ⟨by simp; linarith, by simp; exact hR_nonneg⟩
  have hBcompact : IsCompact B := isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨z, hzB, hzmin⟩ := hBcompact.exists_isMinOn ⟨0, hB0⟩ hcont_F.continuousOn
  have hglobal : ∀ y : ι → ℝ, F z ≤ F y := by
    intro y
    by_cases hyB : y ∈ B
    · exact hzmin hyB
    · have hz0 : F z ≤ F 0 := hzmin hB0
      have hF0 : F 0 = Phi 0 := by simp [F]
      have hex : ∃ i : ι, R < |y i| := by
        by_contra hall
        push Not at hall
        apply hyB
        intro i _
        exact abs_le.mp (hall i)
      obtain ⟨i, hi⟩ := hex
      have hsq : R ^ 2 < ∑ j : ι, (y j) ^ 2 := by
        have h1 : R ^ 2 < (y i) ^ 2 := by
          nlinarith [sq_abs (y i), abs_nonneg (y i)]
        have h2 : (y i) ^ 2 ≤ ∑ j : ι, (y j) ^ 2 :=
          Finset.single_le_sum (fun j _ => sq_nonneg (y j)) (Finset.mem_univ i)
        linarith
      have hRsq : R ^ 2 = 2 * gap / ρ := Real.sq_sqrt (by positivity)
      have hFy : Phi 0 < F y := by
        have h1 := hPhi_ge y
        have h2 : (ρ / 2) * (2 * gap / ρ) < (ρ / 2) * ∑ j : ι, (y j) ^ 2 := by
          rw [← hRsq]
          exact mul_lt_mul_of_pos_left hsq (by positivity)
        have h3 : (ρ / 2) * (2 * gap / ρ) = gap := by field_simp
        dsimp only [F, gap] at h2 h3 ⊢
        linarith
      linarith
  refine ⟨z, fun i => ?_⟩
  let g : ℝ → ℝ := fun t => F (Function.update z i (z i + t))
  have hmin0 : IsLocalMin g 0 := by
    refine Filter.Eventually.of_forall fun t => ?_
    simpa [g] using hglobal (Function.update z i (z i + t))
  set a_i : ℝ := Real.exp (z i) * dotProduct (v i) ((Mmat v z)⁻¹ *ᵥ v i)
  have hdet_upd : ∀ t : ℝ,
      (Mmat v (Function.update z i (z i + t))).det =
        (Mmat v z).det * (1 + (Real.exp t - 1) * a_i) := by
    intro t
    have hM_upd : Mmat v (Function.update z i (z i + t)) =
        Mmat v z + ((Real.exp t - 1) * Real.exp (z i)) • Matrix.vecMulVec (v i) (v i) := by
      unfold Mmat
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
          ← Finset.add_sum_erase _ (fun j => Real.exp (z j) • Matrix.vecMulVec (v j) (v j))
            (Finset.mem_univ i)]
      have hrest : ∑ j ∈ Finset.univ.erase i,
          Real.exp (Function.update z i (z i + t) j) • Matrix.vecMulVec (v j) (v j) =
          ∑ j ∈ Finset.univ.erase i, Real.exp (z j) • Matrix.vecMulVec (v j) (v j) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [(Finset.mem_erase.mp hj).1]
      rw [hrest, Function.update_self, Real.exp_add]
      ext r s
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have hunit : IsUnit (Mmat v z).det := isUnit_iff_ne_zero.mpr (Mmat_det_pos v z hspan).ne'
    have hinv : Mmat v z * (Mmat v z)⁻¹ = 1 := Matrix.mul_nonsing_inv (Mmat v z) hunit
    set α : ℝ := (Real.exp t - 1) * Real.exp (z i)
    have hfact : Mmat v z + α • Matrix.vecMulVec (v i) (v i) =
        Mmat v z * (1 + Matrix.vecMulVec (α • ((Mmat v z)⁻¹ *ᵥ v i)) (v i)) := by
      rw [mul_add, mul_one]
      congr 1
      ext r s
      have hmv : (Mmat v z *ᵥ ((Mmat v z)⁻¹ *ᵥ v i)) r = v i r := by
        rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      simp only [Matrix.mul_apply, Matrix.vecMulVec, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
      calc α * (v i r * v i s) = α * ((Mmat v z *ᵥ ((Mmat v z)⁻¹ *ᵥ v i)) r * v i s) := by rw [hmv]
        _ = ∑ k : Fin 3, Mmat v z r k * (α * ((Mmat v z)⁻¹ *ᵥ v i) k * v i s) := by
            simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro k _
            apply Finset.sum_congr rfl; intro x _
            ring
    rw [hM_upd, hfact, Matrix.det_mul, det_one_add_vecMulVec]
    congr 1
    simp only [dotProduct_smul, smul_eq_mul, α, a_i]
    ring
  have hg_eq : ∀ t : ℝ, g t =
      Real.log (Mmat v z).det + Real.log (1 + (Real.exp t - 1) * a_i) -
      ((∑ j : ι, c j * z j) + c i * t) +
      (ρ / 2) * ((∑ j : ι, (z j) ^ 2) + 2 * z i * t + t ^ 2) := by
    intro t
    have hdet_pos_t := Mmat_det_pos v (Function.update z i (z i + t)) hspan
    have hdet_pos_0 := Mmat_det_pos v z hspan
    have hfac_pos : 0 < 1 + (Real.exp t - 1) * a_i := by
      rw [hdet_upd t] at hdet_pos_t
      exact pos_of_mul_pos_right hdet_pos_t hdet_pos_0.le
    have hlin : ∑ j : ι, c j * Function.update z i (z i + t) j = (∑ j : ι, c j * z j) + c i * t := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
          ← Finset.add_sum_erase _ (fun j => c j * z j) (Finset.mem_univ i)]
      have hrest : ∑ j ∈ Finset.univ.erase i, c j * Function.update z i (z i + t) j =
          ∑ j ∈ Finset.univ.erase i, c j * z j := by
        apply Finset.sum_congr rfl; intro j hj; simp [(Finset.mem_erase.mp hj).1]
      rw [hrest, Function.update_self]; ring
    have hquad : ∑ j : ι, (Function.update z i (z i + t) j) ^ 2 =
        (∑ j : ι, (z j) ^ 2) + 2 * z i * t + t ^ 2 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
          ← Finset.add_sum_erase _ (fun j => (z j) ^ 2) (Finset.mem_univ i)]
      have hrest : ∑ j ∈ Finset.univ.erase i, (Function.update z i (z i + t) j) ^ 2 =
          ∑ j ∈ Finset.univ.erase i, (z j) ^ 2 := by
        apply Finset.sum_congr rfl; intro j hj; simp [(Finset.mem_erase.mp hj).1]
      rw [hrest, Function.update_self]; ring
    dsimp only [g, F, Phi]
    rw [hdet_upd t, Real.log_mul hdet_pos_0.ne' hfac_pos.ne', hlin, hquad]
  have hderiv : HasDerivAt g (a_i - c i + ρ * z i) 0 := by
    have hfun : g = fun t =>
        Real.log (Mmat v z).det + Real.log (1 + (Real.exp t - 1) * a_i) -
        ((∑ j : ι, c j * z j) + c i * t) +
        (ρ / 2) * ((∑ j : ι, (z j) ^ 2) + 2 * z i * t + t ^ 2) := funext hg_eq
    rw [hfun]
    have h1 : HasDerivAt (fun t : ℝ => 1 + (Real.exp t - 1) * a_i) (1 * a_i) 0 := by
      have hexp := (Real.hasDerivAt_exp 0).sub_const 1
      simpa using (hexp.mul_const a_i).const_add 1
    have hlog : HasDerivAt (fun t : ℝ => Real.log (1 + (Real.exp t - 1) * a_i)) a_i 0 := by
      have := h1.log (by norm_num)
      simpa using this
    have hlin : HasDerivAt (fun t : ℝ => (∑ j : ι, c j * z j) + c i * t) (c i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (c i)).const_add (∑ j : ι, c j * z j)
    have hquad : HasDerivAt (fun t : ℝ => (∑ j : ι, (z j) ^ 2) + 2 * z i * t + t ^ 2)
        (2 * z i + 0) 0 := by
      have ht1 : HasDerivAt (fun t : ℝ => (∑ j : ι, (z j) ^ 2) + 2 * z i * t) (2 * z i) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (2 * z i)).const_add (∑ j : ι, (z j) ^ 2)
      have ht2 : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by
        simpa using hasDerivAt_pow 2 (0 : ℝ)
      exact ht1.add ht2
    have hall : HasDerivAt (fun t : ℝ =>
        Real.log (Mmat v z).det + Real.log (1 + (Real.exp t - 1) * a_i) -
        ((∑ j : ι, c j * z j) + c i * t) +
        (ρ / 2) * ((∑ j : ι, (z j) ^ 2) + 2 * z i * t + t ^ 2))
        (a_i - c i + (ρ / 2) * (2 * z i + 0)) 0 :=
      ((hlog.const_add (Real.log (Mmat v z).det)).sub hlin).add (hquad.const_mul (ρ / 2))
    convert hall using 1
    ring
  have hgrad0 : a_i - c i + ρ * z i = 0 := by
    rw [← hderiv.deriv]
    exact hmin0.deriv_eq_zero
  have hdiff : a_i - c i = -(ρ * z i) := by linarith
  have hnorm : (ρ / 2) * (z i) ^ 2 ≤ gap := by
    have h1 := hglobal 0
    have h2 := hPhi_ge z
    have h3 : (z i) ^ 2 ≤ ∑ j : ι, (z j) ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ i)
    have h4 : (ρ / 2) * (z i) ^ 2 ≤ (ρ / 2) * ∑ j : ι, (z j) ^ 2 :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    dsimp only [F, gap] at h1 ⊢
    simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero, mul_zero, add_zero] at h1
    linarith
  have hsq_lt : (a_i - c i) ^ 2 < δ ^ 2 := by
    rw [hdiff]
    have h1 : (-(ρ * z i)) ^ 2 = 2 * ρ * ((ρ / 2) * (z i) ^ 2) := by ring
    rw [h1]
    have h2 : 2 * ρ * ((ρ / 2) * (z i) ^ 2) ≤ 2 * ρ * gap :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    have h3 : 2 * ρ * gap = δ ^ 2 / 2 := by
      dsimp only [ρ]
      field_simp
      ring
    linarith [sq_pos_of_pos hδ]
  have habs_sq : |a_i - c i| ^ 2 < δ ^ 2 := by rwa [sq_abs]
  exact lt_of_pow_lt_pow_left₀ 2 hδ.le habs_sq

end LogDet

/- Part 4: Frame Normalization and Energy Bounds (Appendix A.3 + Lemma 2.2) -/

section FrameEnergy

lemma dotProduct_mulVec_self (A : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ) :
    dotProduct (A *ᵥ v) (A *ᵥ v) = dotProduct v ((Aᵀ * A) *ᵥ v) := by
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
  ring

lemma dotProduct_mulVec_transpose (A : Matrix (Fin 3) (Fin 3) ℝ) (x y : Fin 3 → ℝ) :
    dotProduct x (A *ᵥ y) = dotProduct (Aᵀ *ᵥ x) y := by
  simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fin.sum_univ_three]
  ring

lemma exists_whitening_matrix (M : Matrix (Fin 3) (Fin 3) ℝ) (hM : M.PosDef) :
    ∃ A : Matrix (Fin 3) (Fin 3) ℝ, A * M * Aᵀ = 1 ∧ Aᵀ * A = M⁻¹ := by
  have hH : M.IsHermitian := hM.isHermitian
  let U : Matrix (Fin 3) (Fin 3) ℝ := (hH.eigenvectorUnitary : Matrix (Fin 3) (Fin 3) ℝ)
  have hUUT : U * Uᵀ = 1 := by
    have h1 := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    simpa [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using h1
  have hUTU : Uᵀ * U = 1 := by
    have h1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    simpa [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using h1
  let lam : Fin 3 → ℝ := hH.eigenvalues
  have hspec : M = U * Matrix.diagonal lam * Uᵀ := by
    have h1 := hH.spectral_theorem
    have hstar : star U = Uᵀ := by
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    simpa [U, lam, Unitary.conjStarAlgAut_apply, hstar, Matrix.mul_assoc] using h1
  have heig_pos : ∀ k : Fin 3, 0 < lam k := hM.eigenvalues_pos
  let DinvSqrt : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.diagonal (fun k => (Real.sqrt (lam k))⁻¹)
  let A : Matrix (Fin 3) (Fin 3) ℝ := DinvSqrt * Uᵀ
  have hAT : Aᵀ = U * DinvSqrt := by
    simp [A, DinvSqrt, Matrix.transpose_mul, Matrix.diagonal_transpose]
  refine ⟨A, ?_, ?_⟩
  · calc A * M * Aᵀ
        = (DinvSqrt * Uᵀ) * (U * Matrix.diagonal lam * Uᵀ) * (U * DinvSqrt) := by
            rw [hAT]; conv_lhs => rw [hspec]
      _ = DinvSqrt * (Uᵀ * U) * Matrix.diagonal lam * (Uᵀ * U) * DinvSqrt := by
            simp only [Matrix.mul_assoc]
      _ = DinvSqrt * Matrix.diagonal lam * DinvSqrt := by
            rw [hUTU, Matrix.mul_one, Matrix.mul_one]
      _ = 1 := by
            simp only [DinvSqrt, Matrix.diagonal_mul_diagonal]
            rw [← Matrix.diagonal_one]
            congr 1; ext k
            have hk := heig_pos k
            have hsq : Real.sqrt (lam k) ≠ 0 := (Real.sqrt_pos.mpr hk).ne'
            field_simp [hsq]
            exact (Real.sq_sqrt hk.le).symm
  · have hmul : M * (Aᵀ * A) = 1 := by
      calc M * (Aᵀ * A)
          = (U * Matrix.diagonal lam * Uᵀ) * (U * DinvSqrt * (DinvSqrt * Uᵀ)) := by
              rw [hAT]; conv_lhs => rw [hspec]
        _ = U * Matrix.diagonal lam * (Uᵀ * U) * (DinvSqrt * DinvSqrt) * Uᵀ := by
              simp only [Matrix.mul_assoc]
        _ = U * (Matrix.diagonal lam * (DinvSqrt * DinvSqrt)) * Uᵀ := by
              rw [hUTU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = U * 1 * Uᵀ := by
              congr 2
              simp only [DinvSqrt, Matrix.diagonal_mul_diagonal]
              rw [← Matrix.diagonal_one]
              congr 1; ext k
              have hk := heig_pos k
              have hsq : Real.sqrt (lam k) ≠ 0 := (Real.sqrt_pos.mpr hk).ne'
              field_simp [hsq]
              exact (Real.sq_sqrt hk.le).symm
        _ = 1 := by rw [Matrix.mul_one, hUUT]
    have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hM.det_pos.ne'
    have hinv_left : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hunit
    calc Aᵀ * A = 1 * (Aᵀ * A) := (Matrix.one_mul _).symm
      _ = (M⁻¹ * M) * (Aᵀ * A) := by rw [hinv_left]
      _ = M⁻¹ * (M * (Aᵀ * A)) := Matrix.mul_assoc _ _ _
      _ = M⁻¹ := by rw [hmul, Matrix.mul_one]

lemma frame_energy_upper_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → (Fin 3 → ℝ)) (T : ℝ) (hT : 0 < T)
    (hv_ne : ∀ i, v i ≠ 0)
    (hspan : Submodule.span ℝ (Set.range v) = ⊤)
    (hdens : ∀ I : Finset ι, (I.card : ℝ) / T ≤ (rankOf v I : ℝ))
    (δ : ℝ) (hδ : 0 < δ) (hδT : δ < 1 / T) :
    ∃ A : Matrix (Fin 3) (Fin 3) ℝ, IsUnit A.det ∧
      let u : ι → (Fin 3 → ℝ) := fun i =>
        (Real.sqrt (dotProduct (A *ᵥ v i) (A *ᵥ v i)))⁻¹ • (A *ᵥ v i)
      (∀ i, dotProduct (u i) (u i) = 1) ∧
      ∑ i : ι, ∑ j ∈ Finset.univ.erase i, (dotProduct (u i) (u j)) ^ 2 ≤
        ((1 / T - δ)⁻¹ - 1) * (Fintype.card ι : ℝ) := by
  obtain ⟨c, hc_lo, hc_le, hc_sum⟩ := exists_tight_weights v T hT hv_ne hspan hdens
  obtain ⟨z, hz⟩ := exists_small_gradient v c hv_ne hspan hc_le hc_sum δ hδ
  have hMpos := Mmat_posDef v z hspan
  obtain ⟨A, hAMA, hATA⟩ := exists_whitening_matrix (Mmat v z) hMpos
  have hAdet : IsUnit A.det := by
    have h1 : A.det * (Mmat v z).det * Aᵀ.det = 1 := by
      have := congrArg Matrix.det hAMA
      simpa [Matrix.det_mul, Matrix.det_one] using this
    exact isUnit_iff_ne_zero.mpr (fun h0 => by rw [h0, zero_mul, zero_mul] at h1; norm_num at h1)
  have hAv_pos : ∀ i : ι, 0 < dotProduct (A *ᵥ v i) (A *ᵥ v i) := by
    intro i
    rw [dotProduct_mulVec_self, hATA]
    have hMinv := (Matrix.posDef_iff_dotProduct_mulVec.mp hMpos.inv).2 (hv_ne i)
    simpa [star_trivial] using hMinv
  have hu1_all : ∀ i : ι,
      dotProduct ((Real.sqrt (dotProduct (A *ᵥ v i) (A *ᵥ v i)))⁻¹ • (A *ᵥ v i))
        ((Real.sqrt (dotProduct (A *ᵥ v i) (A *ᵥ v i)))⁻¹ • (A *ᵥ v i)) = 1 := by
    intro i
    have hsq : Real.sqrt (dotProduct (A *ᵥ v i) (A *ᵥ v i)) ≠ 0 := (Real.sqrt_pos.mpr (hAv_pos i)).ne'
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
    field_simp [hsq]
    exact (Real.sq_sqrt (hAv_pos i).le).symm
  refine ⟨A, hAdet, hu1_all, ?_⟩
  dsimp only
  set u : ι → (Fin 3 → ℝ) := fun i =>
    (Real.sqrt (dotProduct (A *ᵥ v i) (A *ᵥ v i)))⁻¹ • (A *ᵥ v i)
  have hquad_le : ∀ x : Fin 3 → ℝ,
      (1 / T - δ) * ∑ i : ι, (dotProduct (u i) x) ^ 2 ≤ dotProduct x x := by
    intro x
    have hxx : dotProduct x x =
        ∑ i : ι, Real.exp (z i) * (dotProduct (A *ᵥ v i) x) ^ 2 := by
      calc dotProduct x x = dotProduct x ((A * Mmat v z * Aᵀ) *ᵥ x) := by rw [hAMA, Matrix.one_mulVec]
        _ = dotProduct x (A *ᵥ (Mmat v z *ᵥ (Aᵀ *ᵥ x))) := by
            rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        _ = dotProduct (Aᵀ *ᵥ x) (Mmat v z *ᵥ (Aᵀ *ᵥ x)) := dotProduct_mulVec_transpose A x _
        _ = ∑ i : ι, Real.exp (z i) * (dotProduct (v i) (Aᵀ *ᵥ x)) ^ 2 := Mmat_quadForm v z (Aᵀ *ᵥ x)
        _ = ∑ i : ι, Real.exp (z i) * (dotProduct (A *ᵥ v i) x) ^ 2 := by
            apply Finset.sum_congr rfl; intro i _
            congr 2
            rw [dotProduct_comm (v i), ← dotProduct_mulVec_transpose A x (v i), dotProduct_comm]
    rw [hxx, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hcoeff : 1 / T - δ ≤ Real.exp (z i) * dotProduct (A *ᵥ v i) (A *ᵥ v i) := by
      rw [dotProduct_mulVec_self, hATA]
      have hzi := (abs_lt.mp (hz i)).1
      linarith [hc_lo i]
    have hu_sq : (dotProduct (u i) x) ^ 2 =
        (dotProduct (A *ᵥ v i) x) ^ 2 / dotProduct (A *ᵥ v i) (A *ᵥ v i) := by
      simp only [u, smul_dotProduct, smul_eq_mul, mul_pow, inv_pow, Real.sq_sqrt (hAv_pos i).le,
        div_eq_inv_mul]
    rw [hu_sq]
    have hpos_i := hAv_pos i
    calc (1 / T - δ) * ((dotProduct (A *ᵥ v i) x) ^ 2 / dotProduct (A *ᵥ v i) (A *ᵥ v i))
        ≤ (Real.exp (z i) * dotProduct (A *ᵥ v i) (A *ᵥ v i)) *
            ((dotProduct (A *ᵥ v i) x) ^ 2 / dotProduct (A *ᵥ v i) (A *ᵥ v i)) :=
          mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ = Real.exp (z i) * (dotProduct (A *ᵥ v i) x) ^ 2 := by
          field_simp [(hAv_pos i).ne']
  have hpos : 0 < 1 / T - δ := sub_pos.mpr hδT
  have htotal : ∑ j : ι, ∑ i : ι, (dotProduct (u i) (u j)) ^ 2 ≤
      (1 / T - δ)⁻¹ * (Fintype.card ι : ℝ) := by
    have h1 : (1 / T - δ) * ∑ j : ι, ∑ i : ι, (dotProduct (u i) (u j)) ^ 2 ≤
        ∑ j : ι, dotProduct (u j) (u j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => hquad_le (u j)
    have h2 : ∑ j : ι, dotProduct (u j) (u j) = (Fintype.card ι : ℝ) := by
      simp [u, hu1_all]
    rw [h2] at h1
    calc ∑ j : ι, ∑ i : ι, (dotProduct (u i) (u j)) ^ 2
        = (1 / T - δ)⁻¹ * ((1 / T - δ) * ∑ j : ι, ∑ i : ι, (dotProduct (u i) (u j)) ^ 2) :=
            (inv_mul_cancel_left₀ hpos.ne' _).symm
      _ ≤ (1 / T - δ)⁻¹ * (Fintype.card ι : ℝ) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hpos.le)
  have hsplit : ∑ i : ι, ∑ j : ι, (dotProduct (u i) (u j)) ^ 2 =
      (Fintype.card ι : ℝ) + ∑ i : ι, ∑ j ∈ Finset.univ.erase i, (dotProduct (u i) (u j)) ^ 2 := by
    have hrow : ∀ i : ι, ∑ j : ι, (dotProduct (u i) (u j)) ^ 2 =
        1 + ∑ j ∈ Finset.univ.erase i, (dotProduct (u i) (u j)) ^ 2 := by
      intro i
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hu1_all i, one_pow]
    simp_rw [hrow, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [Finset.sum_comm] at htotal
  linarith

lemma line_energy_lower_bound {I : Finset ℝ²} (u : ℝ² → (Fin 3 → ℝ))
    (a b : ℝ²) (ha : a ∈ I) (_hb : b ∈ I) (_hab : a ≠ b)
    (hu_unit : ∀ p ∈ I, dotProduct (u p) (u p) = 1)
    (hu_span : ∀ p ∈ I, u p ∈ Submodule.span ℝ ({u a, u b} : Set (Fin 3 → ℝ)))
    (hu_li : LinearIndependent ℝ ![u a, u b]) :
    (1 / 2 : ℝ) * (I.card : ℝ) * ((I.card : ℝ) - 2) ≤
      ∑ p ∈ I, ∑ q ∈ I.erase p, (dotProduct (u p) (u q)) ^ 2 := by
  let e1 : Fin 3 → ℝ := u a
  let w : Fin 3 → ℝ := u b - (dotProduct e1 (u b)) • e1
  have hw_ne : w ≠ 0 := by
    intro hw0
    have hdep : (-(dotProduct e1 (u b))) • u a + (1 : ℝ) • u b = 0 := by
      have : (-(dotProduct e1 (u b))) • u a + (1 : ℝ) • u b = w := by
        dsimp only [w, e1]; module
      rw [this, hw0]
    have h0 := Fintype.linearIndependent_iff.mp hu_li ![-(dotProduct e1 (u b)), 1]
      (by simpa [Fin.sum_univ_two] using hdep) 1
    norm_num at h0
  have hw_pos : 0 < dotProduct w w := by
    by_contra hle
    push Not at hle
    have hsq0 : (w 0) ^ 2 + (w 1) ^ 2 + (w 2) ^ 2 ≤ 0 := by
      simpa [dotProduct, Fin.sum_univ_three, sq] using hle
    apply hw_ne
    ext k; fin_cases k <;> simp <;> nlinarith
  let e2 : Fin 3 → ℝ := (Real.sqrt (dotProduct w w))⁻¹ • w
  have he1 : dotProduct e1 e1 = 1 := hu_unit a ha
  have he2 : dotProduct e2 e2 = 1 := by
    have hsq : Real.sqrt (dotProduct w w) ≠ 0 := (Real.sqrt_pos.mpr hw_pos).ne'
    simp only [e2, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    field_simp [hsq]
    exact (Real.sq_sqrt hw_pos.le).symm
  have he12 : dotProduct e1 e2 = 0 := by
    simp only [e2, w, dotProduct_smul, dotProduct_sub, smul_eq_mul, he1, mul_one, sub_self, mul_zero]
  have he21 : dotProduct e2 e1 = 0 := by rw [dotProduct_comm, he12]
  have hdecomp : ∀ p ∈ I, u p = (dotProduct e1 (u p)) • e1 + (dotProduct e2 (u p)) • e2 := by
    intro p hp
    have hmem := hu_span p hp
    rw [Submodule.mem_span_pair] at hmem
    obtain ⟨α, β, hαβ⟩ := hmem
    have hub : u b = (dotProduct e1 (u b)) • e1 + (Real.sqrt (dotProduct w w)) • e2 := by
      have hsq : Real.sqrt (dotProduct w w) ≠ 0 := (Real.sqrt_pos.mpr hw_pos).ne'
      simp only [e2, smul_smul, mul_inv_cancel₀ hsq, one_smul, w]
      abel
    have hup : u p = (α + β * dotProduct e1 (u b)) • e1 + (β * Real.sqrt (dotProduct w w)) • e2 := by
      set c_ab : ℝ := dotProduct e1 (u b)
      have hub' : u b = c_ab • e1 + (Real.sqrt (dotProduct w w)) • e2 := hub
      calc u p = α • e1 + β • u b := hαβ.symm
        _ = α • e1 + β • (c_ab • e1 + (Real.sqrt (dotProduct w w)) • e2) := by rw [hub']
        _ = (α + β * c_ab) • e1 + (β * Real.sqrt (dotProduct w w)) • e2 := by module
    have hc1 : dotProduct e1 (u p) = α + β * dotProduct e1 (u b) := by
      rw [hup, dotProduct_add, dotProduct_smul, dotProduct_smul, he1, he12]
      simp
    have hc2 : dotProduct e2 (u p) = β * Real.sqrt (dotProduct w w) := by
      rw [hup, dotProduct_add, dotProduct_smul, dotProduct_smul, he21, he2]
      simp
    rw [hc1, hc2, ← hup]
  let x : ℝ² → ℝ := fun p => dotProduct e1 (u p)
  let y : ℝ² → ℝ := fun p => dotProduct e2 (u p)
  have hdot : ∀ p ∈ I, ∀ q ∈ I, dotProduct (u p) (u q) = x p * x q + y p * y q := by
    intro p hp q hq
    rw [hdecomp p hp, hdecomp q hq]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      he1, he2, he12, he21, smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
    ring
  have hxy1 : ∀ p ∈ I, (x p) ^ 2 + (y p) ^ 2 = 1 := by
    intro p hp
    have := hdot p hp p hp
    rw [hu_unit p hp] at this
    linarith
  have hsum_full : (1 / 2 : ℝ) * (I.card : ℝ) ^ 2 ≤
      ∑ p ∈ I, ∑ q ∈ I, (dotProduct (u p) (u q)) ^ 2 := by
    have hexpand : ∑ p ∈ I, ∑ q ∈ I, (dotProduct (u p) (u q)) ^ 2 =
        (∑ p ∈ I, (x p) ^ 2) ^ 2 + 2 * (∑ p ∈ I, x p * y p) ^ 2 + (∑ p ∈ I, (y p) ^ 2) ^ 2 := by
      have h1 : ∑ p ∈ I, ∑ q ∈ I, (dotProduct (u p) (u q)) ^ 2 =
          ∑ p ∈ I, ∑ q ∈ I, ((x p) ^ 2 * (x q) ^ 2 + 2 * (x p * y p) * (x q * y q) +
            (y p) ^ 2 * (y q) ^ 2) := by
        apply Finset.sum_congr rfl; intro p hp
        apply Finset.sum_congr rfl; intro q hq
        rw [hdot p hp q hq]; ring
      rw [h1]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, sq]
      ring
    rw [hexpand]
    have hsum1 : (∑ p ∈ I, (x p) ^ 2) + (∑ p ∈ I, (y p) ^ 2) = (I.card : ℝ) := by
      rw [← Finset.sum_add_distrib]
      have : ∑ p ∈ I, ((x p) ^ 2 + (y p) ^ 2) = ∑ _p ∈ I, (1 : ℝ) :=
        Finset.sum_congr rfl fun p hp => hxy1 p hp
      rw [this]
      simp
    set A1 := ∑ p ∈ I, (x p) ^ 2
    set B1 := ∑ p ∈ I, (y p) ^ 2
    set C1 := ∑ p ∈ I, x p * y p
    nlinarith [sq_nonneg (A1 - B1), sq_nonneg C1]
  have hsplit : ∑ p ∈ I, ∑ q ∈ I, (dotProduct (u p) (u q)) ^ 2 =
      (I.card : ℝ) + ∑ p ∈ I, ∑ q ∈ I.erase p, (dotProduct (u p) (u q)) ^ 2 := by
    have hrow : ∀ p ∈ I, ∑ q ∈ I, (dotProduct (u p) (u q)) ^ 2 =
        1 + ∑ q ∈ I.erase p, (dotProduct (u p) (u q)) ^ 2 := by
      intro p hp
      rw [← Finset.add_sum_erase _ _ hp, hu_unit p hp, one_pow]
    calc ∑ p ∈ I, ∑ q ∈ I, (dotProduct (u p) (u q)) ^ 2
        = ∑ p ∈ I, (1 + ∑ q ∈ I.erase p, (dotProduct (u p) (u q)) ^ 2) :=
            Finset.sum_congr rfl hrow
      _ = (I.card : ℝ) + ∑ p ∈ I, ∑ q ∈ I.erase p, (dotProduct (u p) (u q)) ^ 2 := by
            simp [Finset.sum_add_distrib]
  linarith

end FrameEnergy

end Erdos211H1Proof

open scoped BigOperators Classical Matrix in
theorem OMA.solution : OMA.R_Erdos211_erdos_211_variants_one_sixth_R1.H1 := by
  intro s hs2 hcap
  open EuclideanGeometry Erdos211 Matrix Erdos211H1Proof in
  have hs3 : 3 ≤ s.card := card_ge_three s hs2 hcap
  let v : s → (Fin 3 → ℝ) := fun i => lift i.1
  have hv_ne : ∀ i : s, v i ≠ 0 := fun i => lift_ne_zero i.1
  have hspan : Submodule.span ℝ (Set.range v) = ⊤ := lift_span_top s hs3 hcap
  set T : ℝ := (s.card : ℝ) / 3
  have hT : 0 < T := by
    have : (3 : ℝ) ≤ s.card := by exact_mod_cast hs3
    dsimp only [T]; linarith
  have hdens : ∀ I : Finset s, (I.card : ℝ) / T ≤ (rankOf v I : ℝ) := by
    intro I
    set W := Submodule.span ℝ (v '' (I : Set s))
    have hsub : I.image Subtype.val ⊆ s.filter (fun p => lift p ∈ W) := by
      intro p hp
      obtain ⟨i, hiI, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_filter.mpr ⟨i.2, Submodule.subset_span ⟨i, hiI, rfl⟩⟩
    have hcard : I.card ≤ (s.filter fun p => lift p ∈ W).card := by
      rw [← Finset.card_image_of_injective I Subtype.val_injective]
      exact Finset.card_le_card hsub
    have hcard_r : (I.card : ℝ) ≤ ((s.filter fun p => lift p ∈ W).card : ℝ) := by exact_mod_cast hcard
    have hd := density_bound s hs3 hcap W
    rw [div_le_iff₀ hT]
    calc (I.card : ℝ) ≤ ((s.filter fun p => lift p ∈ W).card : ℝ) := hcard_r
      _ ≤ T * (Module.finrank ℝ W : ℝ) := hd
      _ = (rankOf v I : ℝ) * T := by dsimp only [rankOf, W]; ring
  have hdelta : ∀ δ : ℝ, 0 < δ → δ < 1 / T →
      ∑ L ∈ determinedLines s,
        ((s.filter fun p => p ∈ L).card : ℝ) * (((s.filter fun p => p ∈ L).card : ℝ) - 2) ≤
      2 * ((1 / T - δ)⁻¹ - 1) * (s.card : ℝ) := by
    intro δ hδ hδT
    obtain ⟨A, hAdet, hu_unit, hupper⟩ :=
      frame_energy_upper_bound v T hT hv_ne hspan hdens δ hδ hδT
    let uAll : ℝ² → (Fin 3 → ℝ) := fun p =>
      (Real.sqrt (dotProduct (A *ᵥ lift p) (A *ᵥ lift p)))⁻¹ • (A *ᵥ lift p)
    have hline_lb : ∀ L ∈ determinedLines s,
        (1 / 2 : ℝ) * ((s.filter fun p => p ∈ L).card : ℝ) *
          (((s.filter fun p => p ∈ L).card : ℝ) - 2) ≤
        ∑ p ∈ (s.filter fun p => p ∈ L).offDiag, (dotProduct (uAll p.1) (uAll p.2)) ^ 2 := by
      intro L hL
      obtain ⟨a, ha, b, hb, hab, rfl⟩ := mem_determinedLines.mp hL
      set I := s.filter fun p => p ∈ line[ℝ, a, b]
      have haI : a ∈ I := Finset.mem_filter.mpr ⟨ha, left_mem_affineSpan_pair ℝ a b⟩
      have hbI : b ∈ I := Finset.mem_filter.mpr ⟨hb, right_mem_affineSpan_pair ℝ a b⟩
      have hu_unitI : ∀ p ∈ I, dotProduct (uAll p) (uAll p) = 1 := fun p hp =>
        hu_unit ⟨p, (Finset.mem_filter.mp hp).1⟩
      have hscale_ne : ∀ p : ℝ², (Real.sqrt (dotProduct (A *ᵥ lift p) (A *ᵥ lift p)))⁻¹ ≠ 0 := by
        intro p
        have hAv_ne : A *ᵥ lift p ≠ 0 := by
          intro h0
          have hinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hAdet
          have : lift p = 0 := by
            calc lift p = (1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ lift p := (Matrix.one_mulVec _).symm
              _ = (A⁻¹ * A) *ᵥ lift p := by rw [hinv]
              _ = A⁻¹ *ᵥ (A *ᵥ lift p) := (Matrix.mulVec_mulVec _ _ _).symm
              _ = 0 := by rw [h0, Matrix.mulVec_zero]
          exact lift_ne_zero p this
        have hpos : 0 < dotProduct (A *ᵥ lift p) (A *ᵥ lift p) := by
          by_contra hle; push Not at hle
          have hsq : ((A *ᵥ lift p) 0) ^ 2 + ((A *ᵥ lift p) 1) ^ 2 + ((A *ᵥ lift p) 2) ^ 2 ≤ 0 := by
            simpa [dotProduct, Fin.sum_univ_three, sq] using hle
          apply hAv_ne; ext k; fin_cases k <;> simp <;> nlinarith
        exact inv_ne_zero (Real.sqrt_pos.mpr hpos).ne'
      have hu_spanI : ∀ p ∈ I, uAll p ∈ Submodule.span ℝ ({uAll a, uAll b} : Set (Fin 3 → ℝ)) := by
        intro p hp
        have hpL := lift_mem_span_pair_of_mem_line (Finset.mem_filter.mp hp).2
        rw [Submodule.mem_span_pair] at hpL ⊢
        obtain ⟨α, β, hαβ⟩ := hpL
        set sp := (Real.sqrt (dotProduct (A *ᵥ lift p) (A *ᵥ lift p)))⁻¹
        set sa := (Real.sqrt (dotProduct (A *ᵥ lift a) (A *ᵥ lift a)))⁻¹
        set sb := (Real.sqrt (dotProduct (A *ᵥ lift b) (A *ᵥ lift b)))⁻¹
        refine ⟨sp * α * sa⁻¹, sp * β * sb⁻¹, ?_⟩
        have hA : A *ᵥ lift p = α • (A *ᵥ lift a) + β • (A *ᵥ lift b) := by
          rw [← hαβ, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
        have hsa : sa⁻¹ * sa = 1 := inv_mul_cancel₀ (hscale_ne a)
        have hsb : sb⁻¹ * sb = 1 := inv_mul_cancel₀ (hscale_ne b)
        change (sp * α * sa⁻¹) • (sa • (A *ᵥ lift a)) +
            (sp * β * sb⁻¹) • (sb • (A *ᵥ lift b)) = sp • (A *ᵥ lift p)
        rw [hA, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
        congr 1
        · rw [mul_assoc, hsa, mul_one]
        · rw [mul_assoc, hsb, mul_one]
      have hu_liI : LinearIndependent ℝ ![uAll a, uAll b] := by
        rw [Fintype.linearIndependent_iff]
        intro g hg
        set sa := (Real.sqrt (dotProduct (A *ᵥ lift a) (A *ᵥ lift a)))⁻¹
        set sb := (Real.sqrt (dotProduct (A *ᵥ lift b) (A *ᵥ lift b)))⁻¹
        have hA0 : A *ᵥ ((g 0 * sa) • lift a + (g 1 * sb) • lift b) = 0 := by
          rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
          simpa [Fin.sum_univ_two, uAll, smul_smul] using hg
        have h0 : (g 0 * sa) • lift a + (g 1 * sb) • lift b = 0 := by
          have hinv : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hAdet
          calc (g 0 * sa) • lift a + (g 1 * sb) • lift b
              = (A⁻¹ * A) *ᵥ _ := by rw [hinv, Matrix.one_mulVec]
            _ = A⁻¹ *ᵥ (A *ᵥ _) := (Matrix.mulVec_mulVec _ _ _).symm
            _ = 0 := by rw [hA0, Matrix.mulVec_zero]
        have hli := Fintype.linearIndependent_iff.mp (lift_linearIndependent_pair hab)
          ![g 0 * sa, g 1 * sb] (by simpa [Fin.sum_univ_two] using h0)
        intro k; fin_cases k
        · exact (mul_eq_zero.mp (hli 0)).resolve_right (hscale_ne a)
        · exact (mul_eq_zero.mp (hli 1)).resolve_right (hscale_ne b)
      have hlb := line_energy_lower_bound uAll a b haI hbI hab hu_unitI hu_spanI hu_liI
      have hoff : ∑ p ∈ I.offDiag, (dotProduct (uAll p.1) (uAll p.2)) ^ 2 =
          ∑ p ∈ I, ∑ q ∈ I.erase p, (dotProduct (uAll p) (uAll q)) ^ 2 := by
        have h1 : I.offDiag = (I ×ˢ I).filter (fun p => p.1 ≠ p.2) := by
          ext p; simp [Finset.mem_offDiag, and_assoc]
        rw [h1, Finset.sum_filter, Finset.sum_product]
        apply Finset.sum_congr rfl; intro p _
        rw [← Finset.sum_filter]
        congr 1; ext q; simp [Finset.mem_erase, eq_comm, and_comm]
      rw [hoff]
      exact hlb
    have hpartition : ∑ L ∈ determinedLines s,
        ∑ p ∈ (s.filter fun p => p ∈ L).offDiag, (dotProduct (uAll p.1) (uAll p.2)) ^ 2 =
        ∑ p ∈ s.offDiag, (dotProduct (uAll p.1) (uAll p.2)) ^ 2 := by
      have hfib := Finset.sum_fiberwise_of_maps_to
        (s := s.offDiag) (t := determinedLines s) (g := fun p : ℝ² × ℝ² => line[ℝ, p.1, p.2])
        (f := fun p : ℝ² × ℝ² => (dotProduct (uAll p.1) (uAll p.2)) ^ 2)
        (fun p hp => by
          obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hp
          exact mem_determinedLines.mpr ⟨p.1, ha, p.2, hb, hab, rfl⟩)
      rw [← hfib]
      apply Finset.sum_congr rfl
      intro L hL
      rw [pair_fiber_eq (isLine_of_mem_determinedLines hL)]
    have hmatch : ∑ p ∈ s.offDiag, (dotProduct (uAll p.1) (uAll p.2)) ^ 2 =
        ∑ i : s, ∑ j ∈ Finset.univ.erase i,
          (dotProduct ((Real.sqrt (dotProduct (A *ᵥ v i) (A *ᵥ v i)))⁻¹ • (A *ᵥ v i))
            ((Real.sqrt (dotProduct (A *ᵥ v j) (A *ᵥ v j)))⁻¹ • (A *ᵥ v j))) ^ 2 := by
      have h1 : s.offDiag = (s ×ˢ s).filter (fun p => p.1 ≠ p.2) := by
        ext p; simp [Finset.mem_offDiag, and_assoc]
      rw [h1, Finset.sum_filter, Finset.sum_product, ← Finset.sum_attach s]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_filter, ← Finset.sum_attach (s.filter (fun q => i.1 ≠ q))]
      refine Finset.sum_bij (fun j _ => ⟨j.1, (Finset.mem_filter.mp j.2).1⟩) ?_ ?_ ?_ ?_
      · intro j _
        exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_filter.mp j.2).2 (congrArg Subtype.val h).symm,
          Finset.mem_univ _⟩
      · intro j1 _ j2 _ h
        exact Subtype.ext (Subtype.mk.inj h)
      · intro j hj
        refine ⟨⟨j.1, Finset.mem_filter.mpr ⟨j.2, fun h => (Finset.mem_erase.mp hj).1 (Subtype.ext h.symm)⟩⟩,
          Finset.mem_attach _ _, rfl⟩
      · intro j _; rfl
    have hsum_lb := Finset.sum_le_sum hline_lb
    rw [hpartition, hmatch] at hsum_lb
    have hcard_eq : (Fintype.card s : ℝ) = (s.card : ℝ) := by simp
    rw [hcard_eq] at hupper
    have hcomb := hsum_lb.trans hupper
    have hmul2 : ∑ L ∈ determinedLines s,
        ((s.filter fun p => p ∈ L).card : ℝ) * (((s.filter fun p => p ∈ L).card : ℝ) - 2) =
        2 * ∑ L ∈ determinedLines s,
          (1 / 2 : ℝ) * ((s.filter fun p => p ∈ L).card : ℝ) *
            (((s.filter fun p => p ∈ L).card : ℝ) - 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro L _; ring
    linarith
  have hlim : ∑ L ∈ determinedLines s,
      ((s.filter fun p => p ∈ L).card : ℝ) * (((s.filter fun p => p ∈ L).card : ℝ) - 2) ≤
      2 * (T - 1) * (s.card : ℝ) := by
    by_contra hgt
    push Not at hgt
    set X := ∑ L ∈ determinedLines s,
      ((s.filter fun p => p ∈ L).card : ℝ) * (((s.filter fun p => p ∈ L).card : ℝ) - 2)
    set ε := (X - 2 * (T - 1) * (s.card : ℝ)) / (2 * (s.card : ℝ))
    have hsc_pos : (0 : ℝ) < s.card := by
      have : (3 : ℝ) ≤ s.card := by exact_mod_cast hs3
      linarith
    have hε_pos : 0 < ε := div_pos (sub_pos.mpr hgt) (by positivity)
    set δ := min (1 / (2 * T)) (ε / (2 * T * (T + ε)))
    have hδ_pos : 0 < δ := lt_min (by positivity) (by positivity)
    have hδ_lt : δ < 1 / T := lt_of_le_of_lt (min_le_left _ _) (by
      have : 0 < 1 / (2 * T) := by positivity
      linarith [show 1 / T = 1 / (2 * T) + 1 / (2 * T) by field_simp; ring])
    have hinv_lt : (1 / T - δ)⁻¹ < T + ε := by
      have hpos1 : 0 < 1 / T - δ := sub_pos.mpr hδ_lt
      rw [inv_lt_iff_one_lt_mul₀ hpos1]
      have hδ_le : δ ≤ ε / (2 * T * (T + ε)) := min_le_right _ _
      have h1 : (1 / T - ε / (2 * T * (T + ε))) * (T + ε) = 1 + ε / (2 * T) := by
        field_simp [hT.ne', (add_pos hT hε_pos).ne']
        ring
      have h2 : (1 / T - ε / (2 * T * (T + ε))) * (T + ε) ≤ (1 / T - δ) * (T + ε) :=
        mul_le_mul_of_nonneg_right (sub_le_sub_left hδ_le _) (by positivity)
      have h3 : 0 < ε / (2 * T) := by positivity
      linarith
    have hbound := hdelta δ hδ_pos hδ_lt
    have hstrict : 2 * ((1 / T - δ)⁻¹ - 1) * (s.card : ℝ) < X := by
      have hX_eq : X = 2 * (T + ε - 1) * (s.card : ℝ) := by
        dsimp only [ε]
        field_simp [hsc_pos.ne']
        ring
      rw [hX_eq]
      nlinarith
    linarith
  have hpair := OMA.R_Erdos211_erdos_211_variants_one_sixth_R1.ordered_pair_count_real s (by omega)
  have hdiff : ∑ L ∈ determinedLines s, ((s.filter fun p => p ∈ L).card : ℝ) =
      (s.card : ℝ) * ((s.card : ℝ) - 1) -
      ∑ L ∈ determinedLines s,
        ((s.filter fun p => p ∈ L).card : ℝ) * (((s.filter fun p => p ∈ L).card : ℝ) - 2) := by
    rw [hpair, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro L _
    ring
  have hsc_nonneg : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
  dsimp only [T] at hlim
  linarith
