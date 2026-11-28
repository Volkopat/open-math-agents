import OMAReductions.R_Kakeya_kakeya_set_conjecture_R2

/-!
Taking a product with a bounded real interval raises the Hausdorff exponent
by at most one. For a set of positive diameter, cover the interval by a grid
at that diameter. Zero-diameter sets give vertical lines of zero measure in
every exponent above one.
-/

open Set Metric MeasureTheory
open scoped ENNReal NNReal

private noncomputable def horizontalOuter {X : Type*} (μ : OuterMeasure (X × ℝ))
    (I : Set ℝ) : OuterMeasure X where
  measureOf S := μ (S ×ˢ I)
  empty := by simp
  mono h := μ.mono (Set.prod_mono h Subset.rfl)
  iUnion_nat S _ := by
    rw [Set.iUnion_prod_const]
    exact measure_iUnion_le _

private theorem grid {D M : ℝ} (hD : 0 < D) :
    let N := ⌊(2 * M / D)⌋₊ + 1
    let J (j : Fin N) :=
      Icc ((j.val : ℝ) * D - M) (((j.val : ℝ) + 1) * D - M)
    Icc (-M) M ⊆ ⋃ j, J j := by
  dsimp only
  intro y hy
  have hy0 : 0 ≤ (y + M) / D := div_nonneg (by linarith [hy.1]) hD.le
  have hy1 : (y + M) / D ≤ 2 * M / D :=
    div_le_div_of_nonneg_right (by linarith [hy.2]) hD.le
  let j : Fin (⌊(2 * M / D)⌋₊ + 1) :=
    ⟨⌊((y + M) / D)⌋₊, Nat.lt_succ_of_le (Nat.floor_le_floor hy1)⟩
  refine mem_iUnion.mpr ⟨j, ?_⟩
  have hlo := (le_div_iff₀ hD).mp (Nat.floor_le hy0)
  have hhi := (div_lt_iff₀ hD).mp (Nat.lt_floor_add_one ((y + M) / D))
  exact ⟨by dsimp [j]; linarith, by dsimp [j]; linarith⟩

set_option maxHeartbeats 650000 in
private theorem column_bound {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] (s : ℝ) (hs : 0 < s) (ε : ℝ≥0∞) (hε : 0 < ε) (M : ℝ) (hM : 0 ≤ M)
    {S : Set X} (hS : ediam S ≤ min ε 1) :
    OuterMeasure.mkMetric'.pre (fun U : Set (X × ℝ) => ediam U ^ (s + 1)) ε
        (S ×ˢ Icc (-M) M) ≤ ENNReal.ofReal (2 * M + 1) * ediam S ^ s := by
  let pre : OuterMeasure (X × ℝ) :=
    OuterMeasure.mkMetric'.pre (fun U : Set (X × ℝ) => ediam U ^ (s + 1)) ε
  change pre (S ×ˢ Icc (-M) M) ≤ _
  by_cases hz : ediam S = 0
  · rcases S.eq_empty_or_nonempty with hempty | ⟨x, hx⟩
    · simp [hempty]
    let line (y : ℝ) : X × ℝ := (x, y)
    have hl : Isometry line := by intro a b; simp [line, Prod.edist_eq]
    have hlDim : dimH (range line) = 1 := by
      rw [← image_univ, hl.dimH_image, Real.dimH_univ]
    have hlineZero : (μH[s + 1] : Measure (X × ℝ)) (range line) = 0 := by
      let e : ℝ≥0 := ⟨s + 1, by linarith⟩
      have he : (1 : ℝ≥0) < e := by exact (show (1 : ℝ) < s + 1 by linarith)
      have hE : dimH (range line) < (e : ℝ≥0∞) := by
        rw [hlDim]
        exact_mod_cast he
      have h := hausdorffMeasure_of_dimH_lt (X := X × ℝ) (s := range line) (d := e) hE
      exact h
    have hcol : S ×ˢ Icc (-M) M ⊆ range line := by
      rintro ⟨a, y⟩ hy
      have hsame : x = a := (ediam_eq_zero_iff.mp hz) hx hy.1
      exact ⟨y, Prod.ext hsame rfl⟩
    have hmu : (μH[s + 1] : Measure (X × ℝ)) (S ×ˢ Icc (-M) M) = 0 :=
      measure_mono_null (μ := (μH[s + 1] : Measure (X × ℝ))) hcol hlineZero
    have hpre : pre ≤ (μH[s + 1] : Measure (X × ℝ)).toOuterMeasure := by
      rw [Measure.hausdorffMeasure, Measure.mkMetric_toOuterMeasure]
      unfold OuterMeasure.mkMetric OuterMeasure.mkMetric'
      exact le_iSup₂ (f := fun r (_ : 0 < r) =>
        OuterMeasure.mkMetric'.pre (fun U : Set (X × ℝ) => ediam U ^ (s + 1)) r) ε hε
    have hpreZero : pre (S ×ˢ Icc (-M) M) ≤ 0 := by
      simpa [hmu] using hpre (S ×ˢ Icc (-M) M)
    exact hpreZero.trans bot_le
  · let R := ediam S
    have hRfin : R ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hS.trans (min_le_right _ _))
    let D := R.toReal
    have hD : 0 < D := ENNReal.toReal_pos hz hRfin
    have hReal : ENNReal.ofReal D = R := ENNReal.ofReal_toReal hRfin
    have hD1 : D ≤ 1 := by
      have h := ENNReal.toReal_mono ENNReal.one_ne_top (hS.trans (min_le_right _ _))
      simpa [D, R] using h
    let N := ⌊(2 * M / D)⌋₊ + 1
    let J (j : Fin N) := Icc ((j.val : ℝ) * D - M) (((j.val : ℝ) + 1) * D - M)
    have hJ : Icc (-M) M ⊆ ⋃ j, J j := grid hD
    have hcover : S ×ˢ Icc (-M) M ⊆ ⋃ j, S ×ˢ J j := by
      rw [← Set.prod_iUnion]
      exact Set.prod_mono Subset.rfl hJ
    have hJdiam (j : Fin N) : ediam (J j) = R := by
      dsimp only [J]
      rw [Real.ediam_Icc, show ((j.val : ℝ) + 1) * D - M - ((j.val : ℝ) * D - M) = D by ring, hReal]
    have hbox (j : Fin N) : ediam (S ×ˢ J j) ≤ R := by
      apply ediam_le_iff.mpr
      intro a ha b hb
      rw [Prod.edist_eq, max_le_iff]
      exact ⟨edist_le_ediam_of_mem ha.1 hb.1,
        (edist_le_ediam_of_mem ha.2 hb.2).trans (hJdiam j).le⟩
    have hnReal : (N : ℝ) * D ≤ 2 * M + 1 := by
      have hM' : 0 ≤ 2 * M / D := by positivity
      have hf := (le_div_iff₀ hD).mp (Nat.floor_le hM')
      dsimp only [N]
      push_cast
      linarith [hf]
    have hnBound : (N : ℝ≥0∞) * R ≤ ENNReal.ofReal (2 * M + 1) := by
      rw [← hReal, ← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]
      exact ENNReal.ofReal_le_ofReal hnReal
    calc
      _ ≤ pre (⋃ j, S ×ˢ J j) := pre.mono hcover
      _ ≤ ∑' j : Fin N, pre (S ×ˢ J j) := measure_iUnion_le _
      _ ≤ ∑' _j : Fin N, R ^ (s + 1) := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        have hεR : R ≤ ε := hS.trans (min_le_left _ _)
        have hloc := OuterMeasure.mkMetric'.pre_le
          (m := fun U : Set (X × ℝ) => ediam U ^ (s + 1)) ((hbox j).trans hεR)
        exact hloc.trans (ENNReal.rpow_le_rpow (hbox j) (by linarith))
      _ = (N : ℝ≥0∞) * R ^ (s + 1) := by rw [tsum_fintype]; simp [nsmul_eq_mul]
      _ = ((N : ℝ≥0∞) * R) * R ^ s := by
        rw [ENNReal.rpow_add s 1 hz hRfin, ENNReal.rpow_one]
        ac_rfl
      _ ≤ _ := by gcongr

private theorem slab_null {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] {K : Set X} {s : ℝ} (hs : 0 < s)
    (hK : (μH[s] : Measure X) K = 0) (M : ℝ) (hM : 0 ≤ M) :
    (μH[s + 1] : Measure (X × ℝ)) (K ×ˢ Icc (-M) M) = 0 := by
  let C := ENNReal.ofReal (2 * M + 1)
  have hC0 : C ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have hC1 : C ≠ ⊤ := ENNReal.ofReal_ne_top
  have bounds (ε : ℝ≥0∞) (hε : 0 < ε) :
      OuterMeasure.mkMetric'.pre (fun U : Set (X × ℝ) => ediam U ^ (s + 1)) ε
      (K ×ˢ Icc (-M) M) = 0 := by
    let pre : OuterMeasure (X × ℝ) :=
      OuterMeasure.mkMetric'.pre (fun U : Set (X × ℝ) => ediam U ^ (s + 1)) ε
    let hor := horizontalOuter pre (Icc (-M) M)
    have hle : C⁻¹ • hor ≤ OuterMeasure.mkMetric (fun d : ℝ≥0∞ => d ^ s) :=
      OuterMeasure.le_mkMetric _ _ (min ε 1) (lt_min hε zero_lt_one) (fun S hS => by
        change C⁻¹ * pre (S ×ˢ Icc (-M) M) ≤ _
        calc
          _ ≤ C⁻¹ * (C * ediam S ^ s) :=
            mul_le_mul_of_nonneg_left (column_bound s hs ε hε M hM hS) bot_le
          _ = _ := by rw [← mul_assoc, ENNReal.inv_mul_cancel hC0 hC1, one_mul])
    have hMzero : OuterMeasure.mkMetric (fun d : ℝ≥0∞ => d ^ s) K = 0 := by
      rw [OuterMeasure.coe_mkMetric]
      exact hK
    have hz := hle K
    rw [hMzero] at hz
    change C⁻¹ * pre (K ×ˢ Icc (-M) M) ≤ 0 at hz
    exact (mul_eq_zero.mp (le_antisymm hz bot_le)).resolve_left
      (ENNReal.inv_ne_zero.mpr hC1)
  apply le_antisymm _ bot_le
  rw [Measure.hausdorffMeasure, ← OuterMeasure.coe_mkMetric]
  unfold OuterMeasure.mkMetric OuterMeasure.mkMetric'
  simp only [OuterMeasure.iSup_apply]
  exact iSup₂_le fun r hr => (bounds r hr).le

private theorem cylinder_null {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] {K : Set X} {s : ℝ} (hs : 0 < s)
    (hK : (μH[s] : Measure X) K = 0) :
    (μH[s + 1] : Measure (X × ℝ)) (K ×ˢ (univ : Set ℝ)) = 0 := by
  have hu : (univ : Set ℝ) = ⋃ n : ℕ, Icc (-(n : ℝ)) (n : ℝ) := by
    symm
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨n, hn⟩ := exists_nat_ge |x|
    exact mem_iUnion.mpr ⟨n, abs_le.mp hn⟩
  rw [hu, Set.prod_iUnion, measure_iUnion_null_iff]
  exact fun n => slab_null hs hK n (Nat.cast_nonneg n)

private theorem dimH_cylinder {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] (K : Set X) :
    dimH (K ×ˢ (univ : Set ℝ)) ≤ dimH K + 1 := by
  apply dimH_le
  intro d hd
  by_contra! hbad
  have h1 : (1 : ℝ≥0∞) ≤ dimH K + 1 := by
    simpa only [zero_add] using add_le_add (show (0 : ℝ≥0∞) ≤ dimH K from bot_le) (le_refl (1 : ℝ≥0∞))
  have hd' : (1 : ℝ≥0) < d := by exact_mod_cast h1.trans_lt hbad
  let r : ℝ≥0 := d - 1
  have radd : r + 1 = d := tsub_add_cancel_of_le hd'.le
  have rpos : 0 < r := tsub_pos_of_lt hd'
  have hk : dimH K < (r : ℝ≥0∞) := by
    apply (ENNReal.add_lt_add_iff_right ENNReal.one_ne_top).mp
    rw [show (r : ℝ≥0∞) + 1 = (d : ℝ≥0∞) by exact_mod_cast radd]
    exact hbad
  have h0 : (μH[(r : ℝ)] : Measure X) K = 0 :=
    hausdorffMeasure_of_dimH_lt (d := r) hk
  have hzero := cylinder_null (show 0 < (r : ℝ) from rpos) h0
  have rexp : (r : ℝ) + 1 = (d : ℝ) := by exact_mod_cast radd
  rw [rexp, hd] at hzero
  exact ENNReal.top_ne_zero hzero

theorem OMA.solution : OMA.R_Kakeya_kakeya_set_conjecture_R2.H1 := by
  intro n K
  let F : (EuclideanSpace ℝ (Fin n) × ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    { toFun := fun p => WithLp.toLp 2 (Fin.snoc (fun i => p.1 i) p.2)
      map_add' := by
        intro x y
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Fin.snoc_castSucc]
      map_smul' := by
        intro a x
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Fin.snoc_castSucc] }
  let f : (EuclideanSpace ℝ (Fin n) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    F.toContinuousLinearMap
  have hsub : {x : EuclideanSpace ℝ (Fin (n + 1)) |
        WithLp.toLp 2 (fun i : Fin n => x i.castSucc) ∈ K} ⊆
      f '' (K ×ˢ (univ : Set ℝ)) := by
    intro x hx
    refine ⟨(WithLp.toLp 2 (fun i : Fin n => x i.castSucc), x (Fin.last n)), ⟨hx, mem_univ _⟩, ?_⟩
    change WithLp.toLp 2 (Fin.snoc (Fin.init fun i => x i) (x (Fin.last n))) = x
    rw [Fin.snoc_init_self]
  exact (dimH_mono hsub).trans ((f.lipschitz.dimH_image_le _).trans (dimH_cylinder K))

