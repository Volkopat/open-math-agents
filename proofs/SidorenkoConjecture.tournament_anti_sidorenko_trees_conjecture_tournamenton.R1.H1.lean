import OMAReductions.R_SidorenkoConjecture_tournament_anti_sidorenko_trees_conjecture_tournamenton_R1

namespace OMA.Proof_Sidorenko_tas_tournamenton_R1_H1

open SimpleGraph LimitObjects MeasureTheory

private lemma star_adj_center {V : Type*} {T : SimpleGraph V} (hT : T.IsTree) {c : V}
    (hc : ∀ u v : V, T.Adj u v → u = c ∨ v = c) {v : V} (hv : v ≠ c) :
    T.Adj c v := by
  have hwalk : ∀ {x y : V} (p : T.Walk x y), x ≠ y → y ≠ c → T.Adj c y := by
    intro x y p
    induction p with
    | nil => intro hne; exact absurd rfl hne
    | @cons a b d hab p' ih =>
      intro _ hdc
      by_cases hbd : b = d
      · subst hbd
        rcases hc a b hab with rfl | rfl
        · exact hab
        · exact absurd rfl hdc
      · exact ih hbd hdc
  obtain ⟨p⟩ := hT.connected c v
  exact hwalk p hv.symm hv

private lemma star_adj_iff {V : Type*} {T : SimpleGraph V} (hT : T.IsTree) {c : V}
    (hc : ∀ u v : V, T.Adj u v → u = c ∨ v = c) (u v : V) :
    T.Adj u v ↔ (u = c ∧ v ≠ c) ∨ (v = c ∧ u ≠ c) := by
  constructor
  · intro huv
    have hne : u ≠ v := T.ne_of_adj huv
    rcases hc u v huv with rfl | rfl
    · exact Or.inl ⟨rfl, hne.symm⟩
    · exact Or.inr ⟨rfl, hne⟩
  · rintro (⟨rfl, hv⟩ | ⟨rfl, hu⟩)
    · exact star_adj_center hT hc hv
    · exact (star_adj_center hT hc hu).symm

private lemma star_edgeFinset_card {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) {c : V}
    (hc : ∀ u v : V, T.Adj u v → u = c ∨ v = c) :
    T.edgeFinset.card = (Finset.univ.erase c).card := by
  symm
  refine Finset.card_bij (fun v _ => s(c, v)) ?_ ?_ ?_
  · intro v hv
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact star_adj_center hT hc (Finset.mem_erase.mp hv).1
  · intro v1 hv1 v2 hv2 heq
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨_, h12⟩ | ⟨hcv2, _⟩
    · exact h12
    · exact absurd hcv2.symm (Finset.mem_erase.mp hv2).1
  · intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeSet, star_adj_iff hT hc] at he
      rcases he with ⟨rfl, hv⟩ | ⟨rfl, hu⟩
      · exact ⟨v, Finset.mem_erase.mpr ⟨hv, Finset.mem_univ _⟩, rfl⟩
      · exact ⟨u, Finset.mem_erase.mpr ⟨hu, Finset.mem_univ _⟩, Sym2.eq_swap⟩

private lemma integral_deg_eq_half (W : Tournamenton) :
    ∫ x : unitInterval, (∫ y : unitInterval, (W (x, y) : ℝ)) = 1 / 2 := by
  have hint : Integrable (fun p : unitInterval × unitInterval => (W p : ℝ))
      ((volume : Measure unitInterval).prod (volume : Measure unitInterval)) := by
    refine Integrable.of_bound
      (continuous_subtype_val.measurable.comp W.measurable).aestronglyMeasurable 1 ?_
    refine Filter.Eventually.of_forall fun p => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (W p).2.1]
    exact (W p).2.2
  have h1 : ∫ x : unitInterval, (∫ y : unitInterval, (W (x, y) : ℝ)) =
      ∫ p : unitInterval × unitInterval, (W p : ℝ) ∂(volume.prod volume) :=
    (MeasureTheory.integral_prod (fun p => (W p : ℝ)) hint).symm
  have hswap : ∫ p : unitInterval × unitInterval, (W p.swap : ℝ) ∂(volume.prod volume) =
      ∫ p : unitInterval × unitInterval, (W p : ℝ) ∂(volume.prod volume) :=
    MeasureTheory.integral_prod_swap (fun p => (W p : ℝ))
  have hint_swap : Integrable (fun p : unitInterval × unitInterval => (W p.swap : ℝ))
      ((volume : Measure unitInterval).prod (volume : Measure unitInterval)) :=
    hint.swap
  have hsum : (∫ p : unitInterval × unitInterval, (W p : ℝ) ∂(volume.prod volume)) +
      (∫ p : unitInterval × unitInterval, (W p.swap : ℝ) ∂(volume.prod volume)) = 1 := by
    rw [← MeasureTheory.integral_add hint hint_swap]
    have hconst : (fun p : unitInterval × unitInterval => (W p : ℝ) + (W p.swap : ℝ)) =
        fun _ => (1 : ℝ) := by
      funext p
      exact W.tournament p.1 p.2
    rw [hconst, MeasureTheory.integral_const, smul_eq_mul, mul_one]
    simp
  linarith

end OMA.Proof_Sidorenko_tas_tournamenton_R1_H1

theorem OMA.solution :
    OMA.R_SidorenkoConjecture_tournament_anti_sidorenko_trees_conjecture_tournamenton_R1.H1 := by
  intro V _ _ T _ hT hstar
  open SimpleGraph LimitObjects MeasureTheory OMA.Proof_Sidorenko_tas_tournamenton_R1_H1 in
  classical
  obtain ⟨c, hc⟩ := hstar
  let L : Finset V := Finset.univ.erase c
  have hA_le : (L.card + 1) / 2 ≤ L.card := by omega
  obtain ⟨A, hAL, hA_card⟩ := Finset.exists_subset_card_eq hA_le
  let B : Finset V := L \ A
  have hB_card : B.card = L.card / 2 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAL, hA_card]; omega
  have hAB_disj : Disjoint A B := Finset.disjoint_sdiff
  have hAB_union : A ∪ B = L := Finset.union_sdiff_of_subset hAL
  let D : Digraph V := ⟨fun u v => (u = c ∧ v ∈ A) ∨ (v = c ∧ u ∈ B)⟩
  have hcA : c ∉ A := fun h => (Finset.mem_erase.mp (hAL h)).1 rfl
  have hcB : c ∉ B := fun h => (Finset.mem_erase.mp (Finset.sdiff_subset h)).1 rfl
  have hD_ori : D.IsOrientation T := by
    refine ⟨?_, ?_⟩
    · rintro u v (⟨rfl, hv⟩ | ⟨rfl, hu⟩)
      · exact star_adj_center hT hc (Finset.mem_erase.mp (hAL hv)).1
      · exact (star_adj_center hT hc (Finset.mem_erase.mp (Finset.sdiff_subset hu)).1).symm
    · intro u v huv
      rw [star_adj_iff hT hc] at huv
      rcases huv with ⟨rfl, hv⟩ | ⟨rfl, hu⟩
      · have hvL : v ∈ L := Finset.mem_erase.mpr ⟨hv, Finset.mem_univ _⟩
        simp only [D, true_and, hv, hcB, and_false, or_false, false_or, hcA]
        constructor
        · intro hvA hvB; exact Finset.disjoint_left.mp hAB_disj hvA hvB
        · intro hvB
          rw [← hAB_union, Finset.mem_union] at hvL
          exact hvL.resolve_right hvB
      · have huL : u ∈ L := Finset.mem_erase.mpr ⟨hu, Finset.mem_univ _⟩
        simp only [D, true_and, hu, hcB, and_false, or_false, false_or, hcA]
        constructor
        · intro huB huA; exact Finset.disjoint_left.mp hAB_disj huA huB
        · intro huA
          rw [← hAB_union, Finset.mem_union] at huL
          exact huL.resolve_left huA
  refine ⟨D, hD_ori, ?_⟩
  intro W
  have hedge : T.edgeFinset.card = L.card := star_edgeFinset_card T hT hc
  rw [hedge]
  let k := L.card
  let eL' : Fin k ≃ {v : V // v ∈ L} := (Fintype.equivFinOfCardEq (Fintype.card_coe L)).symm
  let eL : Fin k ≃ {v : V // v ≠ c} :=
    eL'.trans
      { toFun := fun v => ⟨v.1, (Finset.mem_erase.mp v.2).1⟩
        invFun := fun v => ⟨v.1, Finset.mem_erase.mpr ⟨v.2, Finset.mem_univ _⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  let eV : Fin (k + 1) ≃ V :=
    { toFun := Fin.cases c (fun i => (eL i).1)
      invFun := fun v => if h : v = c then 0 else (eL.symm ⟨v, h⟩).succ
      left_inv := fun i => by
        refine Fin.cases ?_ ?_ i
        · simp
        · intro j
          simp [(eL j).2]
      right_inv := fun v => by
        by_cases h : v = c
        · simp [h]
        · simp [h] }
  let D' : Digraph (Fin (k + 1)) := ⟨fun i j => D.Adj (eV i) (eV j)⟩
  refine le_trans (b := tournamentonHomDensity D' W) (le_of_eq ?_) ?_
  · convert OMA.R_SidorenkoConjecture_tournament_anti_sidorenko_trees_conjecture_tournamenton_R1.density_comap
      eV.symm D' D (fun u v => by simp [D']) W
  unfold tournamentonHomDensity
  let g : Fin k → unitInterval → unitInterval → ℝ := fun i x y =>
    if (eL i).1 ∈ A then (W (x, y) : ℝ) else (W (y, x) : ℝ)
  have hD'_edges : ∀ f : Fin (k + 1) → unitInterval,
      tournamentonHomIntegrand D' W f = ∏ i : Fin k, g i (f 0) (f i.succ) := by
    intro f
    unfold tournamentonHomIntegrand
    have hbij : digraphEdgeFinset D' =
        (Finset.univ : Finset (Fin k)).image (fun i =>
          if (eL i).1 ∈ A then ((0 : Fin (k + 1)), i.succ) else (i.succ, (0 : Fin (k + 1)))) := by
      ext p
      simp only [digraphEdgeFinset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hp
        rcases hp with ⟨h1, h2⟩ | ⟨h2, h1⟩
        · have hp1 : p.1 = 0 := eV.injective h1
          have hne : eV p.2 ≠ c := (Finset.mem_erase.mp (hAL h2)).1
          have hp2_ne : p.2 ≠ 0 := fun h => hne (by rw [h]; rfl)
          obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr hp2_ne
          refine ⟨i, ?_⟩
          have heLi : (eL i).1 = eV p.2 := by rw [← hi]; rfl
          rw [heLi, if_pos h2, ← hp1, hi]
        · have hp2 : p.2 = 0 := eV.injective h2
          have hne : eV p.1 ≠ c := (Finset.mem_erase.mp (Finset.sdiff_subset h1)).1
          have hp1_ne : p.1 ≠ 0 := fun h => hne (by rw [h]; rfl)
          obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr hp1_ne
          refine ⟨i, ?_⟩
          have heLi : (eL i).1 = eV p.1 := by rw [← hi]; rfl
          have hnA : (eL i).1 ∉ A := by
            rw [heLi]; exact Finset.disjoint_right.mp hAB_disj h1
          rw [if_neg hnA, ← hp2, hi]
      · rintro ⟨i, hi⟩
        by_cases hiA : (eL i).1 ∈ A
        · rw [if_pos hiA] at hi
          rw [← hi]
          exact Or.inl ⟨rfl, hiA⟩
        · rw [if_neg hiA] at hi
          rw [← hi]
          have hiL : (eL i).1 ∈ L := Finset.mem_erase.mpr ⟨(eL i).2, Finset.mem_univ _⟩
          have hiB : (eL i).1 ∈ B := by
            rw [← hAB_union, Finset.mem_union] at hiL
            exact hiL.resolve_left hiA
          exact Or.inr ⟨rfl, hiB⟩
    rw [hbij, Finset.prod_image]
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp only [g]
      split_ifs <;> rfl
    · intro i _ j _ hij
      by_cases hiA : (eL i).1 ∈ A <;> by_cases hjA : (eL j).1 ∈ A
      · simp only [hiA, hjA, ↓reduceIte, Prod.mk.injEq, true_and] at hij
        exact Fin.succ_injective _ hij
      · simp only [hiA, hjA, ↓reduceIte, Prod.mk.injEq] at hij
        exact absurd hij.1 (Fin.succ_ne_zero j).symm
      · simp only [hiA, hjA, ↓reduceIte, Prod.mk.injEq] at hij
        exact absurd hij.1 (Fin.succ_ne_zero i)
      · simp only [hiA, hjA, ↓reduceIte, Prod.mk.injEq, and_true] at hij
        exact Fin.succ_injective _ hij
  simp_rw [hD'_edges]
  let eSplit : unitInterval × (Fin k → unitInterval) ≃ᵐ (Fin (k + 1) → unitInterval) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => unitInterval) 0).symm
  have hmp : MeasurePreserving eSplit
      ((volume : Measure unitInterval).prod (Measure.pi fun _ : Fin k => (volume : Measure unitInterval)))
      (Measure.pi fun _ : Fin (k + 1) => (volume : Measure unitInterval)) :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => unitInterval) 0).symm
  rw [← hmp.integral_comp']
  have hsimp_split : ∀ z : unitInterval × (Fin k → unitInterval),
      (∏ i : Fin k, g i (eSplit z 0) (eSplit z i.succ)) = ∏ i : Fin k, g i z.1 (z.2 i) := by
    intro z
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [eSplit, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_apply_same,
      Fin.insertNth_apply_succAbove]
  simp_rw [hsimp_split]
  have hint_split : Integrable (fun z : unitInterval × (Fin k → unitInterval) =>
      ∏ i : Fin k, g i z.1 (z.2 i))
      ((volume : Measure unitInterval).prod (Measure.pi fun _ : Fin k => (volume : Measure unitInterval))) := by
    have hmeas : Measurable (fun z : unitInterval × (Fin k → unitInterval) =>
        ∏ i : Fin k, g i z.1 (z.2 i)) := by
      refine Finset.measurable_prod Finset.univ fun i _ => ?_
      simp only [g]
      split_ifs
      · exact continuous_subtype_val.measurable.comp
          (W.measurable.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))
      · exact continuous_subtype_val.measurable.comp
          (W.measurable.comp (((measurable_pi_apply i).comp measurable_snd).prodMk measurable_fst))
    refine Integrable.of_bound hmeas.aestronglyMeasurable 1 ?_
    refine Filter.Eventually.of_forall fun z => ?_
    have hnn : 0 ≤ ∏ i : Fin k, g i z.1 (z.2 i) :=
      Finset.prod_nonneg fun i _ => by
        simp only [g]; split_ifs <;> exact (W _).2.1
    have hle1 : ∏ i : Fin k, g i z.1 (z.2 i) ≤ 1 :=
      Finset.prod_le_one (fun i _ => by simp only [g]; split_ifs <;> exact (W _).2.1)
        (fun i _ => by simp only [g]; split_ifs <;> exact (W _).2.2)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hle1
  rw [MeasureTheory.integral_prod _ hint_split]
  let d : unitInterval → ℝ := fun x => ∫ y : unitInterval, (W (x, y) : ℝ)
  have hinner : ∀ x : unitInterval,
      (∫ y : Fin k → unitInterval, (∏ i : Fin k, g i x (y i)) ∂Measure.pi fun _ => volume) =
        d x ^ A.card * (1 - d x) ^ B.card := by
    intro x
    rw [MeasureTheory.integral_fintype_prod_eq_prod]
    have hg_int : ∀ i : Fin k,
        (∫ y : unitInterval, g i x y) = if (eL i).1 ∈ A then d x else 1 - d x := by
      intro i
      simp only [g]
      split_ifs
      · rfl
      · have hint_x : Integrable (fun y : unitInterval => (W (x, y) : ℝ)) volume := by
          refine Integrable.of_bound
            (continuous_subtype_val.measurable.comp
              (W.measurable.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable 1 ?_
          refine Filter.Eventually.of_forall fun y => ?_
          rw [Real.norm_eq_abs, abs_of_nonneg (W (x, y)).2.1]
          exact (W (x, y)).2.2
        have hsub : (fun y : unitInterval => (W (y, x) : ℝ)) =
            fun y => (1 : ℝ) - (W (x, y) : ℝ) := by
          funext y
          linarith [W.tournament x y]
        rw [hsub, MeasureTheory.integral_sub (integrable_const (1 : ℝ)) hint_x,
          MeasureTheory.integral_const, smul_eq_mul, mul_one]
        simp [d]
    simp_rw [hg_int]
    let SA : Finset (Fin k) := Finset.univ.filter (fun i => (eL i).1 ∈ A)
    let SB : Finset (Fin k) := Finset.univ.filter (fun i => (eL i).1 ∉ A)
    have hSA_card : SA.card = A.card := by
      refine Finset.card_bij (fun i _ => (eL i).1) ?_ ?_ ?_
      · intro i hi; exact (Finset.mem_filter.mp hi).2
      · intro i1 _ i2 _ heq; exact eL.injective (Subtype.ext heq)
      · intro v hv
        have hvne : v ≠ c := (Finset.mem_erase.mp (hAL hv)).1
        refine ⟨eL.symm ⟨v, hvne⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hv]⟩, by simp⟩
    have hSB_card : SB.card = B.card := by
      have hdisj : Disjoint SA SB := Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1
      have hunion : SA ∪ SB = Finset.univ := by
        ext i
        simp only [SA, SB, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        exact iff_true_intro (em _)
      have htot : SA.card + SB.card = k := by
        rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
      omega
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    exact congrArg₂ (· * ·) (congrArg (d x ^ ·) hSA_card) (congrArg ((1 - d x) ^ ·) hSB_card)
  simp_rw [hinner]
  have hd_bounds : ∀ x : unitInterval, 0 ≤ d x ∧ d x ≤ 1 := by
    intro x
    have hint_x : Integrable (fun y : unitInterval => (W (x, y) : ℝ)) volume := by
      refine Integrable.of_bound
        (continuous_subtype_val.measurable.comp
          (W.measurable.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable 1 ?_
      refine Filter.Eventually.of_forall fun y => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (W (x, y)).2.1]
      exact (W (x, y)).2.2
    constructor
    · exact MeasureTheory.integral_nonneg fun y => (W (x, y)).2.1
    · calc d x ≤ ∫ _y : unitInterval, (1 : ℝ) :=
            MeasureTheory.integral_mono hint_x (integrable_const 1) fun y => (W (x, y)).2.2
        _ = 1 := by simp
  have hW_sm : StronglyMeasurable (Function.uncurry fun x y : unitInterval => (W (x, y) : ℝ)) :=
    (continuous_subtype_val.measurable.comp W.measurable).stronglyMeasurable
  have hd_meas : Measurable d := hW_sm.integral_prod_right.measurable
  have hd_int : Integrable d volume := by
    refine Integrable.of_bound hd_meas.aestronglyMeasurable 1 ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hd_bounds x).1]
    exact (hd_bounds x).2
  have hprod_int : Integrable (fun x : unitInterval => d x ^ A.card * (1 - d x) ^ B.card) volume := by
    refine Integrable.of_bound
      ((hd_meas.pow_const A.card).mul ((measurable_const.sub hd_meas).pow_const B.card)).aestronglyMeasurable
      1 ?_
    refine Filter.Eventually.of_forall fun x => ?_
    obtain ⟨h0, h1⟩ := hd_bounds x
    have hnn : 0 ≤ d x ^ A.card * (1 - d x) ^ B.card :=
      mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)
    have hle : d x ^ A.card * (1 - d x) ^ B.card ≤ 1 :=
      mul_le_one₀ (pow_le_one₀ h0 h1) (pow_nonneg (by linarith) _) (pow_le_one₀ (by linarith) (by linarith))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hle
  have hprod_le : ∀ x : unitInterval, d x * (1 - d x) ≤ 1 / 4 := fun x => by
    nlinarith [sq_nonneg (d x - 1 / 2)]
  rcases Nat.even_or_odd L.card with ⟨r, hr⟩ | ⟨r, hr⟩
  · have hA_eq : A.card = r := by omega
    have hB_eq : B.card = r := by omega
    have hpt : ∀ x : unitInterval, d x ^ A.card * (1 - d x) ^ B.card ≤ (1 / 2 : ℝ) ^ L.card := by
      intro x
      rw [hA_eq, hB_eq, ← mul_pow]
      calc (d x * (1 - d x)) ^ r ≤ (1 / 4 : ℝ) ^ r :=
            pow_le_pow_left₀ (mul_nonneg (hd_bounds x).1 (by linarith [(hd_bounds x).2])) (hprod_le x) r
        _ = (1 / 2 : ℝ) ^ L.card := by
            rw [hr, show r + r = 2 * r by omega, pow_mul]; norm_num
    calc ∫ x : unitInterval, d x ^ A.card * (1 - d x) ^ B.card
        ≤ ∫ _x : unitInterval, (1 / 2 : ℝ) ^ L.card :=
          MeasureTheory.integral_mono hprod_int (integrable_const _) hpt
      _ = (1 / 2 : ℝ) ^ L.card := by simp
  · have hA_eq : A.card = r + 1 := by omega
    have hB_eq : B.card = r := by omega
    have hpt : ∀ x : unitInterval,
        d x ^ A.card * (1 - d x) ^ B.card ≤ d x * (1 / 4 : ℝ) ^ r := by
      intro x
      rw [hA_eq, hB_eq, pow_succ', mul_assoc, ← mul_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg (hd_bounds x).1 (by linarith [(hd_bounds x).2])) (hprod_le x) r)
        (hd_bounds x).1
    calc ∫ x : unitInterval, d x ^ A.card * (1 - d x) ^ B.card
        ≤ ∫ x : unitInterval, d x * (1 / 4 : ℝ) ^ r :=
          MeasureTheory.integral_mono hprod_int (hd_int.mul_const _) hpt
      _ = (∫ x : unitInterval, d x) * (1 / 4 : ℝ) ^ r := MeasureTheory.integral_mul_const _ _
      _ = (1 / 2 : ℝ) * (1 / 4 : ℝ) ^ r := by rw [integral_deg_eq_half W]
      _ = (1 / 2 : ℝ) ^ L.card := by
          rw [hr, pow_succ', pow_mul]; norm_num
