import OMAStatements.S_oeis_a005926
import Mathlib

open Filter MeasureTheory

open scoped Topology

noncomputable section

private def phi (u : Fin 3 → ℤ) : Fin 3 → ℝ :=
  if Even (∑ i, u i) then fun i ↦ (u i : ℝ) else fun i ↦ (u i : ℝ) - 1 / 2

private lemma phi_mem_diamond (u : Fin 3 → ℤ) : phi u ∈ OMA.S_oeis_a005926.diamond := by
  by_cases h : Even (∑ i, u i)
  · refine ⟨u, h, Or.inl fun i ↦ ?_⟩
    simp [phi, h]
  · refine ⟨fun i ↦ u i - 1, ?_, Or.inr fun i ↦ ?_⟩
    · rw [Fin.sum_univ_three] at h ⊢
      rcases Int.not_even_iff_odd.mp h with ⟨k, hk⟩
      refine ⟨k - 1, ?_⟩
      omega
    · simp [phi, h]
      ring

private lemma phi_injective : Function.Injective phi := by
  intro u w huw
  have hcoord : ∀ i : Fin 3, phi u i = phi w i := fun i ↦ congr_fun huw i
  by_cases hu : Even (∑ i, u i) <;> by_cases hw : Even (∑ i, w i)
  · ext i
    have hi := hcoord i
    simp only [phi, hu, hw, ↓reduceIte] at hi
    exact_mod_cast hi
  · exfalso
    have h0 := hcoord 0
    simp only [phi, hu, hw, ↓reduceIte] at h0
    have h2 : (2 * u 0 : ℤ) = 2 * w 0 - 1 := by
      have : ((2 * u 0 : ℤ) : ℝ) = ((2 * w 0 - 1 : ℤ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast this
    omega
  · exfalso
    have h0 := hcoord 0
    simp only [phi, hu, hw, ↓reduceIte] at h0
    have h2 : (2 * u 0 - 1 : ℤ) = 2 * w 0 := by
      have : ((2 * u 0 - 1 : ℤ) : ℝ) = ((2 * w 0 : ℤ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast this
    omega
  · ext i
    have hi := hcoord i
    simp only [phi, hu, hw, ↓reduceIte] at hi
    have : (u i : ℝ) = (w i : ℝ) := by linarith
    exact_mod_cast this

private lemma diamond_subset_range_phi {x : Fin 3 → ℝ}
    (hx : x ∈ OMA.S_oeis_a005926.diamond) : ∃ u : Fin 3 → ℤ, phi u = x := by
  rcases hx with ⟨v, hv, hleft | hright⟩
  · refine ⟨v, ?_⟩
    ext i
    simp [phi, hv, hleft i]
  · refine ⟨fun i ↦ v i + 1, ?_⟩
    have hodd : ¬ Even (∑ i : Fin 3, (v i + 1)) := by
      rw [Fin.sum_univ_three] at hv ⊢
      rcases hv with ⟨k, hk⟩
      intro ⟨m, hm⟩
      omega
    ext i
    simp only [phi, hodd, ↓reduceIte, Int.cast_add, Int.cast_one]
    linarith [hright i]

private def normSq16 (u : Fin 3 → ℤ) : ℕ :=
  ∑ i : Fin 3, (if Even (∑ j, u j) then 4 * u i - 1 else 4 * u i - 3).natAbs ^ 2

private lemma normSq16_pos (u : Fin 3 → ℤ) : 1 ≤ normSq16 u := by
  have h0 : 1 ≤ (if Even (∑ j, u j) then 4 * u 0 - 1 else 4 * u 0 - 3).natAbs ^ 2 := by
    have hne : (if Even (∑ j, u j) then 4 * u 0 - 1 else 4 * u 0 - 3) ≠ 0 := by
      split_ifs <;> omega
    have hpos : 1 ≤ (if Even (∑ j, u j) then 4 * u 0 - 1 else 4 * u 0 - 3).natAbs :=
      Int.natAbs_pos.mpr hne
    nlinarith
  refine h0.trans ?_
  dsimp only [normSq16]
  exact Finset.single_le_sum
    (f := fun i : Fin 3 ↦ (if Even (∑ j, u j) then 4 * u i - 1 else 4 * u i - 3).natAbs ^ 2)
    (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ (0 : Fin 3))

private lemma sqDist_phi_eq (u : Fin 3 → ℤ) :
    16 * OMA.S_oeis_a005926.sqDist (phi u) OMA.S_oeis_a005926.edgeMidpoint =
      (normSq16 u : ℝ) := by
  have hcast : ∀ m : ℤ, ((m.natAbs : ℝ) ^ 2) = (m : ℝ) ^ 2 := fun m ↦ by simp
  by_cases h : Even (∑ i, u i)
  · simp only [OMA.S_oeis_a005926.sqDist, OMA.S_oeis_a005926.edgeMidpoint, normSq16,
      phi, h, ↓reduceIte]
    simp only [Fin.sum_univ_three, Nat.cast_add, Nat.cast_pow, hcast]
    push_cast
    ring
  · simp only [OMA.S_oeis_a005926.sqDist, OMA.S_oeis_a005926.edgeMidpoint, normSq16,
      phi, h, ↓reduceIte]
    simp only [Fin.sum_univ_three, Nat.cast_add, Nat.cast_pow, hcast]
    push_cast
    ring

private def latBox (n : ℕ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset fun _ ↦ Finset.Icc (-(n + 2 : ℤ)) (n + 2 : ℤ)

private def latBall (n : ℕ) : Finset (Fin 3 → ℤ) :=
  (latBox n).filter fun u ↦ normSq16 u ≤ n

private lemma mem_latBall_iff (n : ℕ) (u : Fin 3 → ℤ) : u ∈ latBall n ↔ normSq16 u ≤ n := by
  refine ⟨fun h ↦ (Finset.mem_filter.mp h).2, fun h ↦ Finset.mem_filter.mpr ⟨?_, h⟩⟩
  rw [latBox, Fintype.mem_piFinset]
  intro i
  have hi : (if Even (∑ j, u j) then 4 * u i - 1 else 4 * u i - 3).natAbs ^ 2 ≤ n := by
    have hle : (if Even (∑ j, u j) then 4 * u i - 1 else 4 * u i - 3).natAbs ^ 2 ≤
        normSq16 u := by
      dsimp only [normSq16]
      exact Finset.single_le_sum
        (f := fun k : Fin 3 ↦ (if Even (∑ j, u j) then 4 * u k - 1 else 4 * u k - 3).natAbs ^ 2)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    exact hle.trans h
  have hlin : (if Even (∑ j, u j) then 4 * u i - 1 else 4 * u i - 3).natAbs ≤ n :=
    (Nat.le_self_pow (by decide : 2 ≠ 0) _).trans hi
  rw [Finset.mem_Icc]
  split_ifs at hlin <;> omega

private lemma sum_a_eq_card_latBall (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, (OMA.S_oeis_a005926.a k : ℝ)) = ((latBall n).card : ℝ) := by
  have hfiber : (latBall n).card =
      ∑ k ∈ Finset.Icc 1 n, ((latBall n).filter fun u ↦ normSq16 u = k).card := by
    refine Finset.card_eq_sum_card_fiberwise fun u hu ↦ Finset.mem_Icc.mpr ?_
    exact ⟨normSq16_pos u, (mem_latBall_iff n u).mp hu⟩
  have heq : ∀ k ∈ Finset.Icc 1 n,
      OMA.S_oeis_a005926.a k = ((latBall n).filter fun u ↦ normSq16 u = k).card := by
    intro k hk
    have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2
    have hset : {x : Fin 3 → ℝ | x ∈ OMA.S_oeis_a005926.diamond ∧
        16 * OMA.S_oeis_a005926.sqDist x OMA.S_oeis_a005926.edgeMidpoint = (k : ℝ)} =
        phi '' ↑((latBall n).filter fun u ↦ normSq16 u = k) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe, Finset.mem_filter,
        mem_latBall_iff]
      constructor
      · rintro ⟨hx, hdist⟩
        obtain ⟨u, rfl⟩ := diamond_subset_range_phi hx
        rw [sqDist_phi_eq] at hdist
        have huk : normSq16 u = k := by exact_mod_cast hdist
        exact ⟨u, ⟨huk.symm ▸ hkn, huk⟩, rfl⟩
      · rintro ⟨u, ⟨_, huk⟩, rfl⟩
        refine ⟨phi_mem_diamond u, ?_⟩
        rw [sqDist_phi_eq, huk]
    rw [OMA.S_oeis_a005926.a, hset, Set.ncard_image_of_injective _ phi_injective,
      Set.ncard_coe_finset]
  have hnat : ∑ k ∈ Finset.Icc 1 n, OMA.S_oeis_a005926.a k = (latBall n).card := by
    rw [hfiber]
    exact Finset.sum_congr rfl heq
  exact_mod_cast hnat

private def cube (u : Fin 3 → ℤ) : Set (Fin 3 → ℝ) :=
  Set.pi Set.univ fun i ↦ Set.Ico (u i : ℝ) ((u i : ℝ) + 1)

private lemma cube_measurable (u : Fin 3 → ℤ) : MeasurableSet (cube u) :=
  MeasurableSet.univ_pi fun _ ↦ measurableSet_Ico

private lemma cube_volume (u : Fin 3 → ℤ) : volume (cube u) = 1 := by
  rw [cube, MeasureTheory.volume_pi, MeasureTheory.Measure.pi_pi]
  simp [Real.volume_Ico]

private lemma cube_pairwiseDisjoint : Pairwise (fun u w ↦ Disjoint (cube u) (cube w)) := by
  intro u w huw
  rw [Set.disjoint_left]
  intro y hyu hyw
  have hex : ∃ i : Fin 3, u i ≠ w i := by
    by_contra h
    push Not at h
    exact huw (funext h)
  obtain ⟨i, hi⟩ := hex
  have h1 := hyu i (Set.mem_univ i)
  have h2 := hyw i (Set.mem_univ i)
  rcases lt_or_gt_of_ne hi with hlt | hgt
  · have hle : (u i : ℝ) + 1 ≤ (w i : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hlt
    linarith [h1.2, h2.1]
  · have hle : (w i : ℝ) + 1 ≤ (u i : ℝ) := by exact_mod_cast Int.add_one_le_iff.mpr hgt
    linarith [h2.2, h1.1]

private lemma cube_covering (y : Fin 3 → ℝ) : ∃ u : Fin 3 → ℤ, y ∈ cube u := by
  refine ⟨fun i ↦ Int.floor (y i), fun i _ ↦ ?_⟩
  exact ⟨Int.floor_le (y i), Int.lt_floor_add_one (y i)⟩

private lemma dist_cube_phi (u : Fin 3 → ℤ) {y : Fin 3 → ℝ} (hy : y ∈ cube u) :
    dist (WithLp.toLp 2 y) (WithLp.toLp 2 (phi u)) ≤ 3 := by
  have hsq : dist (WithLp.toLp 2 y) (WithLp.toLp 2 (phi u)) ^ 2 ≤ (3 : ℝ) ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq]
    have hcoord : ∀ i : Fin 3, dist (y i) (phi u i) ^ 2 ≤ (3 / 2 : ℝ) ^ 2 := by
      intro i
      rw [Real.dist_eq]
      have hmem := hy i (Set.mem_univ i)
      have hphi : (u i : ℝ) - 1 / 2 ≤ phi u i ∧ phi u i ≤ (u i : ℝ) := by
        by_cases h : Even (∑ j, u j) <;> simp [phi, h]
      have habs : |y i - phi u i| ≤ 3 / 2 := abs_le.mpr ⟨by linarith [hmem.1, hphi.2],
        by linarith [hmem.2, hphi.1]⟩
      nlinarith [abs_nonneg (y i - phi u i)]
    calc
      ∑ i : Fin 3, dist (y i) (phi u i) ^ 2 ≤ ∑ _ : Fin 3, (3 / 2 : ℝ) ^ 2 :=
        Finset.sum_le_sum fun i _ ↦ hcoord i
      _ = 3 * (3 / 2 : ℝ) ^ 2 := by simp
      _ ≤ (3 : ℝ) ^ 2 := by norm_num
  nlinarith [dist_nonneg (x := WithLp.toLp 2 y) (y := WithLp.toLp 2 (phi u))]

private def ballSet (r : ℝ) : Set (Fin 3 → ℝ) :=
  (WithLp.toLp 2) ⁻¹'
    Metric.closedBall (WithLp.toLp 2 OMA.S_oeis_a005926.edgeMidpoint) r

private lemma ballSet_volume (r : ℝ) :
    volume (ballSet r) = ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
  rw [ballSet, (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage
    measurableSet_closedBall.nullMeasurableSet]
  exact EuclideanSpace.volume_closedBall_fin_three _ r

private lemma mem_ballSet_iff {r : ℝ} (hr : 0 ≤ r) (x : Fin 3 → ℝ) :
    x ∈ ballSet r ↔ OMA.S_oeis_a005926.sqDist x OMA.S_oeis_a005926.edgeMidpoint ≤ r ^ 2 := by
  rw [ballSet, Set.mem_preimage, Metric.mem_closedBall]
  have hsq : dist (WithLp.toLp 2 x) (WithLp.toLp 2 OMA.S_oeis_a005926.edgeMidpoint) ^ 2 =
      OMA.S_oeis_a005926.sqDist x OMA.S_oeis_a005926.edgeMidpoint := by
    rw [EuclideanSpace.dist_sq_eq]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Real.dist_eq, sq_abs]
  constructor
  · intro h
    rw [← hsq]
    exact pow_le_pow_left₀ dist_nonneg h 2
  · intro h
    rw [← hsq] at h
    exact (abs_le_of_sq_le_sq' h hr).2

private lemma mem_latBall_iff_ballSet (n : ℕ) (u : Fin 3 → ℤ) :
    u ∈ latBall n ↔ phi u ∈ ballSet (√(n : ℝ) / 4) := by
  rw [mem_latBall_iff, mem_ballSet_iff (by positivity)]
  have h1 : (normSq16 u : ℝ) = 16 * OMA.S_oeis_a005926.sqDist (phi u)
      OMA.S_oeis_a005926.edgeMidpoint := (sqDist_phi_eq u).symm
  have h2 : (√(n : ℝ) / 4) ^ 2 = (n : ℝ) / 16 := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    norm_num
  rw [h2]
  constructor
  · intro h
    have hreal : (normSq16 u : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    linarith
  · intro h
    have hreal : (normSq16 u : ℝ) ≤ (n : ℝ) := by linarith
    exact_mod_cast hreal

private lemma card_latBall_le (n : ℕ) :
    ((latBall n).card : ℝ) ≤ (√(n : ℝ) / 4 + 3) ^ 3 * (Real.pi * 4 / 3) := by
  set R : ℝ := √(n : ℝ) / 4
  have hR_nonneg : 0 ≤ R + 3 := by positivity
  have hsub : (⋃ u ∈ latBall n, cube u) ⊆ ballSet (R + 3) := by
    intro y hy
    simp only [Set.mem_iUnion, exists_prop] at hy
    rcases hy with ⟨u, hu, hyu⟩
    have hphi : phi u ∈ ballSet R := (mem_latBall_iff_ballSet n u).mp hu
    rw [ballSet, Set.mem_preimage, Metric.mem_closedBall] at hphi ⊢
    calc
      dist (WithLp.toLp 2 y) (WithLp.toLp 2 OMA.S_oeis_a005926.edgeMidpoint)
        ≤ dist (WithLp.toLp 2 y) (WithLp.toLp 2 (phi u)) +
            dist (WithLp.toLp 2 (phi u)) (WithLp.toLp 2 OMA.S_oeis_a005926.edgeMidpoint) :=
          dist_triangle _ _ _
      _ ≤ 3 + R := add_le_add (dist_cube_phi u hyu) hphi
      _ = R + 3 := add_comm _ _
  have hmeas : volume (⋃ u ∈ latBall n, cube u) = ((latBall n).card : ENNReal) := by
    rw [MeasureTheory.measure_biUnion_finset (fun u _ w _ h ↦ cube_pairwiseDisjoint h)
      (fun u _ ↦ cube_measurable u)]
    simp [cube_volume]
  have hvol : ((latBall n).card : ENNReal) ≤
      ENNReal.ofReal ((R + 3) ^ 3 * (Real.pi * 4 / 3)) := by
    calc
      ((latBall n).card : ENNReal) = volume (⋃ u ∈ latBall n, cube u) := hmeas.symm
      _ ≤ volume (ballSet (R + 3)) := measure_mono hsub
      _ = ENNReal.ofReal (R + 3) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := ballSet_volume (R + 3)
      _ = ENNReal.ofReal ((R + 3) ^ 3 * (Real.pi * 4 / 3)) := by
        rw [← ENNReal.ofReal_pow hR_nonneg, ← ENNReal.ofReal_mul (pow_nonneg hR_nonneg 3)]
  have hreal := ENNReal.toReal_le_of_le_ofReal (by positivity) hvol
  simpa using hreal

private lemma le_card_latBall {n : ℕ} (hn : 145 ≤ n) :
    (√(n : ℝ) / 4 - 3) ^ 3 * (Real.pi * 4 / 3) ≤ ((latBall n).card : ℝ) := by
  set R : ℝ := √(n : ℝ) / 4
  have hR3 : 3 ≤ R := by
    have h144 : (144 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 144 ≤ n)
    have h12 : (12 : ℝ) ≤ √(n : ℝ) := by
      calc
        (12 : ℝ) = √(144 : ℝ) := by norm_num
        _ ≤ √(n : ℝ) := Real.sqrt_le_sqrt h144
    dsimp [R]
    linarith
  have hR_nonneg : 0 ≤ R - 3 := sub_nonneg.mpr hR3
  have hsub : ballSet (R - 3) ⊆ ⋃ u ∈ latBall n, cube u := by
    intro y hy
    obtain ⟨u, hyu⟩ := cube_covering y
    refine Set.mem_iUnion₂.mpr ⟨u, ?_, hyu⟩
    rw [mem_latBall_iff_ballSet, ballSet, Set.mem_preimage, Metric.mem_closedBall]
    rw [ballSet, Set.mem_preimage, Metric.mem_closedBall] at hy
    calc
      dist (WithLp.toLp 2 (phi u)) (WithLp.toLp 2 OMA.S_oeis_a005926.edgeMidpoint)
        ≤ dist (WithLp.toLp 2 (phi u)) (WithLp.toLp 2 y) +
            dist (WithLp.toLp 2 y) (WithLp.toLp 2 OMA.S_oeis_a005926.edgeMidpoint) :=
          dist_triangle _ _ _
      _ = dist (WithLp.toLp 2 y) (WithLp.toLp 2 (phi u)) +
            dist (WithLp.toLp 2 y) (WithLp.toLp 2 OMA.S_oeis_a005926.edgeMidpoint) := by
          rw [dist_comm]
      _ ≤ 3 + (R - 3) := add_le_add (dist_cube_phi u hyu) hy
      _ = R := by ring
  have hmeas : volume (⋃ u ∈ latBall n, cube u) = ((latBall n).card : ENNReal) := by
    rw [MeasureTheory.measure_biUnion_finset (fun u _ w _ h ↦ cube_pairwiseDisjoint h)
      (fun u _ ↦ cube_measurable u)]
    simp [cube_volume]
  have hvol : ENNReal.ofReal ((R - 3) ^ 3 * (Real.pi * 4 / 3)) ≤
      ((latBall n).card : ENNReal) := by
    calc
      ENNReal.ofReal ((R - 3) ^ 3 * (Real.pi * 4 / 3))
        = ENNReal.ofReal (R - 3) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
          rw [← ENNReal.ofReal_pow hR_nonneg, ← ENNReal.ofReal_mul (pow_nonneg hR_nonneg 3)]
      _ = volume (ballSet (R - 3)) := (ballSet_volume (R - 3)).symm
      _ ≤ volume (⋃ u ∈ latBall n, cube u) := measure_mono hsub
      _ = ((latBall n).card : ENNReal) := hmeas
  have hcard_eq : ((latBall n).card : ℝ) = ((latBall n).card : ENNReal).toReal := by simp
  rw [hcard_eq]
  have hfin : ((latBall n).card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hle := ENNReal.toReal_mono hfin hvol
  rwa [ENNReal.toReal_ofReal (by positivity)] at hle

end

theorem OMA.solution : type_of% @OMA.S_oeis_a005926.main := by
  have hnz : ∀ᶠ n : ℕ in atTop, Real.pi * (n : ℝ) ^ ((3 : ℝ) / 2) / 48 ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
    positivity
  rw [Asymptotics.isEquivalent_iff_tendsto_one hnz]
  have hsqrt : Tendsto (fun n : ℕ ↦ √(n : ℝ)) atTop atTop :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop).congr (fun n ↦ (Real.sqrt_eq_rpow (n : ℝ)).symm)
  have hR_tendsto : Tendsto (fun n : ℕ ↦ √(n : ℝ) / 4) atTop atTop :=
    hsqrt.atTop_div_const (by norm_num)
  have hinv : Tendsto (fun n : ℕ ↦ 3 / (√(n : ℝ) / 4)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hR_tendsto
  have hlow_lim : Tendsto (fun n : ℕ ↦ (1 - 3 / (√(n : ℝ) / 4)) ^ 3) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ ↦ 1 - 3 / (√(n : ℝ) / 4)) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hinv
    simpa using h1.pow 3
  have hhigh_lim : Tendsto (fun n : ℕ ↦ (1 + 3 / (√(n : ℝ) / 4)) ^ 3) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ ↦ 1 + 3 / (√(n : ℝ) / 4)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add hinv
    simpa using h1.pow 3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow_lim hhigh_lim ?_ ?_
  · filter_upwards [eventually_ge_atTop 145] with n hn
    dsimp only [Pi.div_apply]
    have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
    have hRpos : 0 < √(n : ℝ) / 4 := by positivity
    have hV : Real.pi * (n : ℝ) ^ ((3 : ℝ) / 2) / 48 =
        (√(n : ℝ) / 4) ^ 3 * (Real.pi * 4 / 3) := by
      have hrpow : (n : ℝ) ^ ((3 : ℝ) / 2) = √(n : ℝ) ^ 3 := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
        norm_num
      rw [hrpow]
      ring
    have hVpos : 0 < (√(n : ℝ) / 4) ^ 3 * (Real.pi * 4 / 3) := by positivity
    rw [sum_a_eq_card_latBall, hV]
    have hle := le_card_latBall hn
    have hdiv := div_le_div_of_nonneg_right hle hVpos.le
    refine le_trans ?_ hdiv
    have heq : (1 - 3 / (√(n : ℝ) / 4)) ^ 3 =
        (√(n : ℝ) / 4 - 3) ^ 3 * (Real.pi * 4 / 3) /
          ((√(n : ℝ) / 4) ^ 3 * (Real.pi * 4 / 3)) := by
      field_simp
    exact heq.le
  · filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp only [Pi.div_apply]
    have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
    have hRpos : 0 < √(n : ℝ) / 4 := by positivity
    have hV : Real.pi * (n : ℝ) ^ ((3 : ℝ) / 2) / 48 =
        (√(n : ℝ) / 4) ^ 3 * (Real.pi * 4 / 3) := by
      have hrpow : (n : ℝ) ^ ((3 : ℝ) / 2) = √(n : ℝ) ^ 3 := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
        norm_num
      rw [hrpow]
      ring
    have hVpos : 0 < (√(n : ℝ) / 4) ^ 3 * (Real.pi * 4 / 3) := by positivity
    rw [sum_a_eq_card_latBall, hV]
    have hle := card_latBall_le n
    have hdiv := div_le_div_of_nonneg_right hle hVpos.le
    refine le_trans hdiv ?_
    have heq : (1 + 3 / (√(n : ℝ) / 4)) ^ 3 =
        (√(n : ℝ) / 4 + 3) ^ 3 * (Real.pi * 4 / 3) /
          ((√(n : ℝ) / 4) ^ 3 * (Real.pi * 4 / 3)) := by
      field_simp
    exact heq.ge
