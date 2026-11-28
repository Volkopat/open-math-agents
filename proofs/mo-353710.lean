import OMAStatements.S_mo_353710
import Mathlib

namespace OMA.S_mo_353710_Proof

open MeasureTheory Matrix Finset

private lemma norm_sq_eq_sum_sq {d : ℕ} (x : OMA.S_mo_353710.E d) :
    ‖x‖ ^ 2 = ∑ i : Fin d, (x i) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs]

private lemma integrable_of_continuous {d : ℕ} {μ : Measure (OMA.S_mo_353710.E d)}
    [IsProbabilityMeasure μ] (hμ : OMA.S_mo_353710.IsUniform μ)
    {f : OMA.S_mo_353710.E d → ℝ} (hf : Continuous f) :
    Integrable f μ := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : OMA.S_mo_353710.E d) 1).exists_bound_of_continuousOn
    hf.continuousOn
  refine Integrable.of_bound hf.aestronglyMeasurable M ?_
  filter_upwards [hμ.1] with x hx
  apply hM x
  simp [Metric.mem_closedBall, hx]

private lemma integral_comp_iso {d : ℕ} {μ : Measure (OMA.S_mo_353710.E d)}
    (hμ : OMA.S_mo_353710.IsUniform μ) (e : OMA.S_mo_353710.E d ≃ₗᵢ[ℝ] OMA.S_mo_353710.E d)
    (f : OMA.S_mo_353710.E d → ℝ) :
    ∫ x, f (e x) ∂μ = ∫ x, f x ∂μ :=
  (hμ.2 e).integral_comp e.toHomeomorph.measurableEmbedding f

private noncomputable def mkIso {d : ℕ} (L : OMA.S_mo_353710.E d →ₗ[ℝ] OMA.S_mo_353710.E d)
    (Linv : OMA.S_mo_353710.E d →ₗ[ℝ] OMA.S_mo_353710.E d)
    (hl : ∀ x, Linv (L x) = x) (hr : ∀ x, L (Linv x) = x)
    (hnorm : ∀ x, ∑ i : Fin d, (L x i) ^ 2 = ∑ i : Fin d, (x i) ^ 2) :
    OMA.S_mo_353710.E d ≃ₗᵢ[ℝ] OMA.S_mo_353710.E d :=
  { toLinearEquiv := LinearEquiv.ofLinearMap L Linv (LinearMap.ext hr) (LinearMap.ext hl)
    norm_map' := fun x => by
      change ‖L x‖ = ‖x‖
      have hsq : ‖L x‖ ^ 2 = ‖x‖ ^ 2 := by
        rw [norm_sq_eq_sum_sq, norm_sq_eq_sum_sq]
        exact hnorm x
      have h1 : 0 ≤ ‖L x‖ := norm_nonneg _
      have h2 : 0 ≤ ‖x‖ := norm_nonneg _
      nlinarith }

private noncomputable def permLinear {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    OMA.S_mo_353710.E d →ₗ[ℝ] OMA.S_mo_353710.E d where
  toFun x := WithLp.toLp 2 (fun i => x (σ i))
  map_add' x y := by ext i; simp
  map_smul' c x := by ext i; simp

private noncomputable def permIso {d : ℕ} (σ : Equiv.Perm (Fin d)) :
    OMA.S_mo_353710.E d ≃ₗᵢ[ℝ] OMA.S_mo_353710.E d :=
  mkIso (permLinear σ) (permLinear σ⁻¹)
    (fun x => by ext i; simp [permLinear])
    (fun x => by ext i; simp [permLinear])
    (fun x => by
      simp only [permLinear, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
      exact Equiv.sum_comp σ (fun i => (x i) ^ 2))

private noncomputable def flipLinear {d : ℕ} (r : Fin d) :
    OMA.S_mo_353710.E d →ₗ[ℝ] OMA.S_mo_353710.E d where
  toFun x := WithLp.toLp 2 (fun i => if i = r then -(x i) else x i)
  map_add' x y := by
    ext i
    simp only [WithLp.ofLp_toLp, PiLp.add_apply]
    split_ifs <;> ring
  map_smul' c x := by
    ext i
    simp only [WithLp.ofLp_toLp, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

private noncomputable def flipIso {d : ℕ} (r : Fin d) :
    OMA.S_mo_353710.E d ≃ₗᵢ[ℝ] OMA.S_mo_353710.E d :=
  mkIso (flipLinear r) (flipLinear r)
    (fun x => by
      ext i
      simp only [flipLinear, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
      split_ifs <;> ring)
    (fun x => by
      ext i
      simp only [flipLinear, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
      split_ifs <;> ring)
    (fun x => by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [flipLinear, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
      split_ifs <;> ring)

private noncomputable def rotLinear {d : ℕ} (a b : Fin d) (hab : a ≠ b) :
    OMA.S_mo_353710.E d →ₗ[ℝ] OMA.S_mo_353710.E d where
  toFun x := WithLp.toLp 2 fun i =>
    if i = a then (x a + x b) / Real.sqrt 2
    else if i = b then (x a - x b) / Real.sqrt 2
    else x i
  map_add' x y := by
    ext i
    simp only [WithLp.ofLp_toLp, PiLp.add_apply]
    split_ifs <;> ring
  map_smul' c x := by
    ext i
    simp only [WithLp.ofLp_toLp, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

private noncomputable def rotIso {d : ℕ} (a b : Fin d) (hab : a ≠ b) :
    OMA.S_mo_353710.E d ≃ₗᵢ[ℝ] OMA.S_mo_353710.E d :=
  mkIso (rotLinear a b hab) (rotLinear a b hab)
    (fun x => by
      ext i
      have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hsne : Real.sqrt 2 ≠ 0 := by positivity
      simp only [rotLinear, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp,
        hab.symm, ↓reduceIte]
      split_ifs with h1 h2
      · subst h1; field_simp [hsne]; rw [hsq2]; ring
      · subst h2; field_simp [hsne]; rw [hsq2]; ring
      · rfl)
    (fun x => by
      ext i
      have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hsne : Real.sqrt 2 ≠ 0 := by positivity
      simp only [rotLinear, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp,
        hab.symm, ↓reduceIte]
      split_ifs with h1 h2
      · subst h1; field_simp [hsne]; rw [hsq2]; ring
      · subst h2; field_simp [hsne]; rw [hsq2]; ring
      · rfl)
    (fun x => by
      have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have hsne : Real.sqrt 2 ≠ 0 := by positivity
      have hsplit : ∀ f : Fin d → ℝ,
          ∑ i : Fin d, f i = f a + f b + ∑ i ∈ (Finset.univ.erase a).erase b, f i := by
        intro f
        have ha : a ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ a
        have hb : b ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩
        rw [← Finset.add_sum_erase _ _ ha, ← Finset.add_sum_erase _ _ hb, add_assoc]
      rw [hsplit, hsplit]
      have hrest :
          ∑ i ∈ (Finset.univ.erase a).erase b, (rotLinear a b hab x i) ^ 2 =
            ∑ i ∈ (Finset.univ.erase a).erase b, (x i) ^ 2 := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hib : i ≠ b := (Finset.mem_erase.mp hi).1
        have hia : i ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
        simp [rotLinear, hia, hib]
      rw [hrest]
      simp only [rotLinear, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp,
        ↓reduceIte, hab.symm]
      have hpair : ((x a + x b) / Real.sqrt 2) ^ 2 + ((x a - x b) / Real.sqrt 2) ^ 2 =
          (x a) ^ 2 + (x b) ^ 2 := by
        field_simp [hsne]
        nlinarith [hsq2]
      linarith)

private lemma continuous_coord {d : ℕ} (i : Fin d) :
    Continuous (fun x : OMA.S_mo_353710.E d => x i) :=
  (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i)

private lemma integral_four_eq_zero_of_odd {d : ℕ} {μ : Measure (OMA.S_mo_353710.E d)}
    (hμ : OMA.S_mo_353710.IsUniform μ) (i j k l r : Fin d)
    (hodd : ((if i = r then 1 else 0) + (if j = r then 1 else 0) +
      (if k = r then 1 else 0) + (if l = r then 1 else 0)) % 2 = 1) :
    ∫ x, x i * x j * x k * x l ∂μ = 0 := by
  have hflip := integral_comp_iso hμ (flipIso r) (fun x => x i * x j * x k * x l)
  have hneg : ∀ x : OMA.S_mo_353710.E d,
      flipIso r x i * flipIso r x j * flipIso r x k * flipIso r x l =
        -(x i * x j * x k * x l) := by
    intro x
    simp only [flipIso, mkIso, flipLinear, LinearIsometryEquiv.coe_mk,
      LinearEquiv.coe_ofLinearMap, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
    by_cases hi : i = r <;> by_cases hj : j = r <;> by_cases hk : k = r <;> by_cases hl : l = r <;>
      simp [hi, hj, hk, hl] at hodd ⊢ <;> ring
  simp_rw [hneg] at hflip
  rw [integral_neg] at hflip
  linarith

private lemma integral_pow4_eq {d : ℕ} {μ : Measure (OMA.S_mo_353710.E d)}
    (hμ : OMA.S_mo_353710.IsUniform μ) (i j : Fin d) :
    ∫ x, (x i) ^ 4 ∂μ = ∫ x, (x j) ^ 4 ∂μ := by
  have h := integral_comp_iso hμ (permIso (Equiv.swap i j)) (fun x => (x j) ^ 4)
  simpa [permIso, mkIso, permLinear] using h

private lemma integral_sq_sq_eq {d : ℕ} {μ : Measure (OMA.S_mo_353710.E d)}
    (hμ : OMA.S_mo_353710.IsUniform μ) {i j a b : Fin d} (hij : i ≠ j) (hab : a ≠ b) :
    ∫ x, (x i) ^ 2 * (x j) ^ 2 ∂μ = ∫ x, (x a) ^ 2 * (x b) ^ 2 ∂μ := by
  have h1 : ∃ σ : Equiv.Perm (Fin d), σ a = i ∧ σ b = j := by
    by_cases hbi : b = i
    · by_cases haj : a = j
      · refine ⟨Equiv.swap a b, ?_, ?_⟩
        · simp [hbi]
        · simp [haj]
      · refine ⟨Equiv.swap a j * Equiv.swap a b, ?_, ?_⟩
        · simp [hbi, Equiv.swap_apply_of_ne_of_ne (hbi ▸ hab.symm) hij]
        · simp
    · refine ⟨Equiv.swap b j * Equiv.swap a i, ?_, ?_⟩
      · simp [Equiv.swap_apply_of_ne_of_ne (Ne.symm hbi) hij]
      · simp [Equiv.swap_apply_of_ne_of_ne hab.symm hbi]
  rcases h1 with ⟨σ, hσa, hσb⟩
  have h := integral_comp_iso hμ (permIso σ) (fun x => (x a) ^ 2 * (x b) ^ 2)
  simpa [permIso, mkIso, permLinear, hσa, hσb] using h

private lemma integral_pow4_and_sq_sq {d : ℕ} (hd : 0 < d)
    {μ : Measure (OMA.S_mo_353710.E d)} [IsProbabilityMeasure μ]
    (hμ : OMA.S_mo_353710.IsUniform μ) :
    (∀ i : Fin d, ∫ x, (x i) ^ 4 ∂μ = 3 / ((d : ℝ) * ((d : ℝ) + 2))) ∧
    (∀ i j : Fin d, i ≠ j → ∫ x, (x i) ^ 2 * (x j) ^ 2 ∂μ = 1 / ((d : ℝ) * ((d : ℝ) + 2))) := by
  let i0 : Fin d := ⟨0, hd⟩
  let α : ℝ := ∫ x, (x i0) ^ 4 ∂μ
  have hα : ∀ i : Fin d, ∫ x, (x i) ^ 4 ∂μ = α := fun i => integral_pow4_eq hμ i i0
  have hint4 : ∀ i : Fin d, Integrable (fun x : OMA.S_mo_353710.E d => (x i) ^ 4) μ :=
    fun i => integrable_of_continuous hμ ((continuous_coord i).pow 4)
  have hint22 : ∀ i j : Fin d, Integrable (fun x : OMA.S_mo_353710.E d => (x i) ^ 2 * (x j) ^ 2) μ :=
    fun i j => integrable_of_continuous hμ (((continuous_coord i).pow 2).mul ((continuous_coord j).pow 2))
  have hsum1 : ∑ i : Fin d, ∑ j : Fin d, ∫ x, (x i) ^ 2 * (x j) ^ 2 ∂μ = 1 := by
    have h1 : ∀ᵐ x ∂μ, (∑ i : Fin d, ∑ j : Fin d, (x i) ^ 2 * (x j) ^ 2) = 1 := by
      filter_upwards [hμ.1] with x hx
      have hsq : ∑ i : Fin d, (x i) ^ 2 = 1 := by
        rw [← norm_sq_eq_sum_sq, hx, one_pow]
      calc ∑ i : Fin d, ∑ j : Fin d, (x i) ^ 2 * (x j) ^ 2
          = (∑ i : Fin d, (x i) ^ 2) * (∑ j : Fin d, (x j) ^ 2) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
        _ = 1 := by rw [hsq, one_mul]
    have hint_inner : ∀ i : Fin d,
        Integrable (fun x : OMA.S_mo_353710.E d => ∑ j : Fin d, (x i) ^ 2 * (x j) ^ 2) μ :=
      fun i => integrable_finsetSum _ fun j _ => hint22 i j
    calc ∑ i : Fin d, ∑ j : Fin d, ∫ x, (x i) ^ 2 * (x j) ^ 2 ∂μ
        = ∑ i : Fin d, ∫ x, (∑ j : Fin d, (x i) ^ 2 * (x j) ^ 2) ∂μ := by
          refine Finset.sum_congr rfl fun i _ => (integral_finsetSum _ fun j _ => hint22 i j).symm
      _ = ∫ x, (∑ i : Fin d, ∑ j : Fin d, (x i) ^ 2 * (x j) ^ 2) ∂μ :=
          (integral_finsetSum _ fun i _ => hint_inner i).symm
      _ = ∫ _ : OMA.S_mo_353710.E d, (1 : ℝ) ∂μ := integral_congr_ae h1
      _ = 1 := by simp
  by_cases hd1 : d = 1
  · subst hd1
    have hα1 : α = 1 := by
      simpa [α, i0, show ∀ r : ℝ, r ^ 2 * r ^ 2 = r ^ 4 by intro r; ring] using hsum1
    refine ⟨?_, ?_⟩
    · intro i
      rw [hα i, hα1]
      norm_num
    · intro i j hij
      exact absurd (Subsingleton.elim i j) hij
  · have hd2 : 2 ≤ d := by omega
    let i1 : Fin d := ⟨1, by omega⟩
    have h01 : i0 ≠ i1 := by
      intro h
      have := congrArg Fin.val h
      simp [i0, i1] at this
    let β : ℝ := ∫ x, (x i0) ^ 2 * (x i1) ^ 2 ∂μ
    have hβ : ∀ i j : Fin d, i ≠ j → ∫ x, (x i) ^ 2 * (x j) ^ 2 ∂μ = β :=
      fun i j hij => integral_sq_sq_eq hμ hij h01
    have hrot : α = 3 * β := by
      have h := integral_comp_iso hμ (rotIso i0 i1 h01) (fun x => (x i0) ^ 4)
      have hexp : ∀ x : OMA.S_mo_353710.E d,
          (rotIso i0 i1 h01 x i0) ^ 4 =
            (1 / 4 : ℝ) * (x i0) ^ 4 + (x i0) ^ 3 * x i1 +
            (3 / 2 : ℝ) * ((x i0) ^ 2 * (x i1) ^ 2) +
            x i0 * (x i1) ^ 3 + (1 / 4 : ℝ) * (x i1) ^ 4 := by
        intro x
        simp only [rotIso, mkIso, rotLinear, LinearIsometryEquiv.coe_mk,
          LinearEquiv.coe_ofLinearMap, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp,
          ↓reduceIte]
        have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        have h4 : Real.sqrt 2 ^ 4 = 4 := by
          calc Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 := by ring
            _ = 4 := by rw [hsq2]; norm_num
        rw [div_pow, h4]
        ring
      simp_rw [hexp] at h
      have h31 : ∫ x, (x i0) ^ 3 * x i1 ∂μ = 0 := by
        have hz := integral_four_eq_zero_of_odd hμ i0 i0 i0 i1 i1 (by simp [h01])
        simpa [show ∀ a b : ℝ, a * a * a * b = a ^ 3 * b by intro a b; ring] using hz
      have h13 : ∫ x, x i0 * (x i1) ^ 3 ∂μ = 0 := by
        have hz := integral_four_eq_zero_of_odd hμ i0 i1 i1 i1 i0 (by simp [h01.symm])
        simpa [show ∀ a b : ℝ, a * b * b * b = a * b ^ 3 by intro a b; ring] using hz
      have hi31 : Integrable (fun x : OMA.S_mo_353710.E d => (x i0) ^ 3 * x i1) μ :=
        integrable_of_continuous hμ (((continuous_coord i0).pow 3).mul (continuous_coord i1))
      have hi13 : Integrable (fun x : OMA.S_mo_353710.E d => x i0 * (x i1) ^ 3) μ :=
        integrable_of_continuous hμ ((continuous_coord i0).mul ((continuous_coord i1).pow 3))
      have hcalc :
          ∫ x, ((1 / 4 : ℝ) * (x i0) ^ 4 + (x i0) ^ 3 * x i1 +
            (3 / 2 : ℝ) * ((x i0) ^ 2 * (x i1) ^ 2) +
            x i0 * (x i1) ^ 3 + (1 / 4 : ℝ) * (x i1) ^ 4) ∂μ =
            (1 / 4 : ℝ) * α + 0 + (3 / 2 : ℝ) * β + 0 + (1 / 4 : ℝ) * α := by
        rw [integral_add, integral_add, integral_add, integral_add]
        · rw [integral_const_mul, integral_const_mul, integral_const_mul,
            h31, h13, hα i0, hα i1]
        · exact (hint4 i0).const_mul _
        · exact hi31
        · exact ((hint4 i0).const_mul _).add hi31
        · exact (hint22 i0 i1).const_mul _
        · exact (((hint4 i0).const_mul _).add hi31).add ((hint22 i0 i1).const_mul _)
        · exact hi13
        · exact ((((hint4 i0).const_mul _).add hi31).add ((hint22 i0 i1).const_mul _)).add hi13
        · exact (hint4 i1).const_mul _
      change _ = α at h
      linarith
    have hsum_eval : ∑ i : Fin d, ∑ j : Fin d, ∫ x, (x i) ^ 2 * (x j) ^ 2 ∂μ =
        (d : ℝ) * α + (d : ℝ) * ((d : ℝ) - 1) * β := by
      have hinner : ∀ i : Fin d,
          ∑ j : Fin d, ∫ x, (x i) ^ 2 * (x j) ^ 2 ∂μ = α + ((d : ℝ) - 1) * β := by
        intro i
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        have hdiag : ∫ x, (x i) ^ 2 * (x i) ^ 2 ∂μ = α := by
          simpa [show ∀ r : ℝ, r ^ 2 * r ^ 2 = r ^ 4 by intro r; ring] using hα i
        have hoff : ∑ j ∈ Finset.univ.erase i, ∫ x, (x i) ^ 2 * (x j) ^ 2 ∂μ =
            ((d : ℝ) - 1) * β := by
          have hc : ∀ j ∈ Finset.univ.erase i, ∫ x, (x i) ^ 2 * (x j) ^ 2 ∂μ = β :=
            fun j hj => hβ i j (Finset.mem_erase.mp hj).1.symm
          rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
          have hcard : (Finset.univ.erase i).card = d - 1 := by simp
          rw [hcard, Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
        rw [hdiag, hoff]
      rw [Finset.sum_congr rfl fun i _ => hinner i, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring
    have hdpos : (d : ℝ) * ((d : ℝ) + 2) ≠ 0 := by positivity
    have hβval : β = 1 / ((d : ℝ) * ((d : ℝ) + 2)) := by
      have hlin : (d : ℝ) * ((d : ℝ) + 2) * β = 1 := by nlinarith [hsum1, hsum_eval, hrot]
      field_simp [hdpos]
      linarith
    have hαval : α = 3 / ((d : ℝ) * ((d : ℝ) + 2)) := by
      rw [hrot, hβval]
      ring
    exact ⟨fun i => by rw [hα i, hαval], fun i j hij => by rw [hβ i j hij, hβval]⟩

private lemma wick_fourth_moment {d : ℕ} (hd : 0 < d)
    {μ : Measure (OMA.S_mo_353710.E d)} [IsProbabilityMeasure μ]
    (hμ : OMA.S_mo_353710.IsUniform μ) (i j k l : Fin d) :
    ∫ x, x i * x j * x k * x l ∂μ =
      (1 / ((d : ℝ) * ((d : ℝ) + 2))) *
        ((if i = j ∧ k = l then (1 : ℝ) else 0) +
         (if i = k ∧ j = l then (1 : ℝ) else 0) +
         (if i = l ∧ j = k then (1 : ℝ) else 0)) := by
  obtain ⟨hα, hβ⟩ := integral_pow4_and_sq_sq hd hμ
  by_cases hij : i = j
  · subst hij
    by_cases hkl : k = l
    · subst hkl
      by_cases hik : i = k
      · subst hik
        have h4 : (fun x : OMA.S_mo_353710.E d => x i * x i * x i * x i) =
            (fun x => (x i) ^ 4) := funext fun x => by ring
        rw [h4, hα i]
        simp only [and_self, ↓reduceIte]
        ring
      · have h22 : (fun x : OMA.S_mo_353710.E d => x i * x i * x k * x k) =
            (fun x => (x i) ^ 2 * (x k) ^ 2) := funext fun x => by ring
        rw [h22, hβ i k hik]
        simp [hik]
    · by_cases hik : i = k
      · subst hik
        rw [integral_four_eq_zero_of_odd hμ i i i l l (by simp [hkl])]
        simp [hkl]
      · rw [integral_four_eq_zero_of_odd hμ i i k l k (by simp [hik, Ne.symm hkl])]
        simp [hkl, hik]
  · by_cases hik : i = k
    · subst hik
      by_cases hjl : j = l
      · subst hjl
        have h22 : (fun x : OMA.S_mo_353710.E d => x i * x j * x i * x j) =
            (fun x => (x i) ^ 2 * (x j) ^ 2) := funext fun x => by ring
        rw [h22, hβ i j hij]
        simp [hij]
      · rw [integral_four_eq_zero_of_odd hμ i j i l j (by simp [hij, Ne.symm hij, hjl, Ne.symm hjl])]
        simp [hij, Ne.symm hij, hjl, Ne.symm hjl]
    · by_cases hil : i = l
      · subst hil
        by_cases hjk : j = k
        · subst hjk
          have h22 : (fun x : OMA.S_mo_353710.E d => x i * x j * x j * x i) =
              (fun x => (x i) ^ 2 * (x j) ^ 2) := funext fun x => by ring
          rw [h22, hβ i j hij]
          simp [hij]
        · rw [integral_four_eq_zero_of_odd hμ i j k i j (by simp [hij, Ne.symm hij, hjk, Ne.symm hjk])]
          simp [hij, Ne.symm hij, hik, Ne.symm hik, hjk, Ne.symm hjk]
      · rw [integral_four_eq_zero_of_odd hμ i j k l i (by simp [hij, Ne.symm hij, hik, Ne.symm hik, hil, Ne.symm hil])]
        simp [hij, hik, hil]

private lemma q_eq_sum {d : ℕ} (C : OMA.S_mo_353710.Mat d) (x : OMA.S_mo_353710.E d) :
    OMA.S_mo_353710.q C x = ∑ i : Fin d, ∑ j : Fin d, C i j * x i * x j := by
  unfold OMA.S_mo_353710.q
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [RCLike.inner_apply, conj_trivial, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => by ring

private lemma integral_q_sq {d : ℕ} (hd : 0 < d)
    {μ : Measure (OMA.S_mo_353710.E d)} [IsProbabilityMeasure μ]
    (hμ : OMA.S_mo_353710.IsUniform μ)
    (C : OMA.S_mo_353710.Mat d) (hC : C.IsHermitian) :
    ∫ x, (OMA.S_mo_353710.q C x) ^ 2 ∂μ =
      (1 / ((d : ℝ) * ((d : ℝ) + 2))) * (C.trace ^ 2 + 2 * (C * C).trace) := by
  have hsymm : ∀ i j : Fin d, C i j = C j i := by
    intro i j
    have h := congrFun (congrFun hC j) i
    simpa [Matrix.conjTranspose_apply] using h
  have hexp : ∀ x : OMA.S_mo_353710.E d,
      (OMA.S_mo_353710.q C x) ^ 2 =
        ∑ p : (Fin d × Fin d) × (Fin d × Fin d),
          (C p.1.1 p.1.2 * C p.2.1 p.2.2) * (x p.1.1 * x p.1.2 * x p.2.1 * x p.2.2) := by
    intro x
    rw [q_eq_sum, sq, Finset.sum_mul]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  simp_rw [hexp]
  have hint : ∀ p : (Fin d × Fin d) × (Fin d × Fin d),
      Integrable (fun x : OMA.S_mo_353710.E d =>
        (C p.1.1 p.1.2 * C p.2.1 p.2.2) * (x p.1.1 * x p.1.2 * x p.2.1 * x p.2.2)) μ :=
    fun p => integrable_of_continuous hμ (continuous_const.mul
      ((((continuous_coord p.1.1).mul (continuous_coord p.1.2)).mul
        (continuous_coord p.2.1)).mul (continuous_coord p.2.2)))
  rw [integral_finsetSum _ fun p _ => hint p]
  simp_rw [integral_const_mul, wick_fourth_moment hd hμ]
  have hfactor :
      ∑ p : (Fin d × Fin d) × (Fin d × Fin d),
        (C p.1.1 p.1.2 * C p.2.1 p.2.2) *
          ((1 / ((d : ℝ) * ((d : ℝ) + 2))) *
            ((if p.1.1 = p.1.2 ∧ p.2.1 = p.2.2 then (1 : ℝ) else 0) +
             (if p.1.1 = p.2.1 ∧ p.1.2 = p.2.2 then (1 : ℝ) else 0) +
             (if p.1.1 = p.2.2 ∧ p.1.2 = p.2.1 then (1 : ℝ) else 0))) =
      (1 / ((d : ℝ) * ((d : ℝ) + 2))) *
        ((∑ p : (Fin d × Fin d) × (Fin d × Fin d),
            if p.1.1 = p.1.2 ∧ p.2.1 = p.2.2 then C p.1.1 p.1.2 * C p.2.1 p.2.2 else 0) +
         (∑ p : (Fin d × Fin d) × (Fin d × Fin d),
            if p.1.1 = p.2.1 ∧ p.1.2 = p.2.2 then C p.1.1 p.1.2 * C p.2.1 p.2.2 else 0) +
         (∑ p : (Fin d × Fin d) × (Fin d × Fin d),
            if p.1.1 = p.2.2 ∧ p.1.2 = p.2.1 then C p.1.1 p.1.2 * C p.2.1 p.2.2 else 0)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> ring
  rw [hfactor]
  congr 1
  have hS1 :
      (∑ p : (Fin d × Fin d) × (Fin d × Fin d),
          if p.1.1 = p.1.2 ∧ p.2.1 = p.2.2 then C p.1.1 p.1.2 * C p.2.1 p.2.2 else 0) =
        C.trace ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    have h1 : ∀ i j k : Fin d,
        (∑ l : Fin d, if i = j ∧ k = l then C i j * C k l else 0) =
          if i = j then C i j * C k k else 0 := by
      intro i j k
      by_cases hij : i = j
      · simp [hij]
      · simp [hij]
    simp_rw [h1]
    have h2 : ∀ i j : Fin d,
        (∑ k : Fin d, if i = j then C i j * C k k else 0) =
          if i = j then C i j * C.trace else 0 := by
      intro i j
      by_cases hij : i = j
      · simp only [hij, ↓reduceIte, ← Finset.mul_sum, Matrix.trace, Matrix.diag]
      · simp [hij]
    simp_rw [h2]
    have h3 : ∀ i : Fin d,
        (∑ j : Fin d, if i = j then C i j * C.trace else 0) = C i i * C.trace := by
      intro i; simp
    simp_rw [h3, ← Finset.sum_mul]
    simp [Matrix.trace, sq]
  have hS2 :
      (∑ p : (Fin d × Fin d) × (Fin d × Fin d),
          if p.1.1 = p.2.1 ∧ p.1.2 = p.2.2 then C p.1.1 p.1.2 * C p.2.1 p.2.2 else 0) =
        (C * C).trace := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    have h1 : ∀ i j k : Fin d,
        (∑ l : Fin d, if i = k ∧ j = l then C i j * C k l else 0) =
          if i = k then C i j * C k j else 0 := by
      intro i j k
      by_cases hik : i = k
      · simp [hik]
      · simp [hik]
    simp_rw [h1]
    have h2 : ∀ i j : Fin d,
        (∑ k : Fin d, if i = k then C i j * C k j else 0) = C i j * C j i := by
      intro i j
      simp [hsymm i j]
    simp_rw [h2]
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  have hS3 :
      (∑ p : (Fin d × Fin d) × (Fin d × Fin d),
          if p.1.1 = p.2.2 ∧ p.1.2 = p.2.1 then C p.1.1 p.1.2 * C p.2.1 p.2.2 else 0) =
        (C * C).trace := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    have h1 : ∀ i j k : Fin d,
        (∑ l : Fin d, if i = l ∧ j = k then C i j * C k l else 0) =
          if j = k then C i j * C k i else 0 := by
      intro i j k
      by_cases hjk : j = k
      · simp [hjk]
      · simp [hjk]
    simp_rw [h1]
    have h2 : ∀ i j : Fin d,
        (∑ k : Fin d, if j = k then C i j * C k i else 0) = C i j * C j i := by
      intro i j; simp
    simp_rw [h2]
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  rw [hS1, hS2, hS3]
  ring

private lemma q_nonneg_of_psd {d : ℕ} {A : OMA.S_mo_353710.Mat d} (hA : A.PosSemidef)
    (x : OMA.S_mo_353710.E d) : 0 ≤ OMA.S_mo_353710.q A x := by
  have h := hA.dotProduct_mulVec_nonneg x.ofLp
  have heq : OMA.S_mo_353710.q A x = star x.ofLp ⬝ᵥ A *ᵥ x.ofLp := by
    unfold OMA.S_mo_353710.q
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial, Matrix.toLpLin_apply, dotProduct,
      Pi.star_apply, star_trivial]
    refine Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [heq]
  exact h

private lemma q_le_op {d : ℕ} (A : OMA.S_mo_353710.Mat d) {x : OMA.S_mo_353710.E d}
    (hx : ‖x‖ = 1) : OMA.S_mo_353710.q A x ≤ OMA.S_mo_353710.op A := by
  unfold OMA.S_mo_353710.q OMA.S_mo_353710.op
  calc inner ℝ x (A.toEuclideanLin x)
      ≤ ‖x‖ * ‖A.toEuclideanLin x‖ := real_inner_le_norm x _
    _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) A x‖ := by
        rw [hx, one_mul]
        rfl
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) A‖ * ‖x‖ :=
        ContinuousLinearMap.le_opNorm _ x
    _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) A‖ := by rw [hx, mul_one]

private lemma part1 {d : ℕ} (hd : 0 < d) {μ : Measure (OMA.S_mo_353710.E d)}
    [IsProbabilityMeasure μ] (hμ : OMA.S_mo_353710.IsUniform μ)
    (A B : OMA.S_mo_353710.Mat d) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A - B).trace ^ 2 + 2 * ((A - B) * (A - B)).trace ≤
      (d : ℝ) * ((d : ℝ) + 2) * (Real.sqrt (OMA.S_mo_353710.op A) +
        Real.sqrt (OMA.S_mo_353710.op B)) ^ 2 * OMA.S_mo_353710.squared μ A B := by
  have hC : (A - B).IsHermitian := hA.1.sub hB.1
  have hmom := integral_q_sq hd hμ (A - B) hC
  have hae : ∀ᵐ x ∂μ,
      (OMA.S_mo_353710.q (A - B) x) ^ 2 ≤
        (Real.sqrt (OMA.S_mo_353710.op A) + Real.sqrt (OMA.S_mo_353710.op B)) ^ 2 *
          (Real.sqrt (OMA.S_mo_353710.q A x) - Real.sqrt (OMA.S_mo_353710.q B x)) ^ 2 := by
    filter_upwards [hμ.1] with x hx
    have hqA0 : 0 ≤ OMA.S_mo_353710.q A x := q_nonneg_of_psd hA x
    have hqB0 : 0 ≤ OMA.S_mo_353710.q B x := q_nonneg_of_psd hB x
    have hqAop : OMA.S_mo_353710.q A x ≤ OMA.S_mo_353710.op A := q_le_op A hx
    have hqBop : OMA.S_mo_353710.q B x ≤ OMA.S_mo_353710.op B := q_le_op B hx
    have hdiff : OMA.S_mo_353710.q (A - B) x = OMA.S_mo_353710.q A x - OMA.S_mo_353710.q B x := by
      simp only [q_eq_sum, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
    have hfac : OMA.S_mo_353710.q A x - OMA.S_mo_353710.q B x =
        (Real.sqrt (OMA.S_mo_353710.q A x) + Real.sqrt (OMA.S_mo_353710.q B x)) *
          (Real.sqrt (OMA.S_mo_353710.q A x) - Real.sqrt (OMA.S_mo_353710.q B x)) := by
      nlinarith [Real.sq_sqrt hqA0, Real.sq_sqrt hqB0]
    have hsum_le :
        Real.sqrt (OMA.S_mo_353710.q A x) + Real.sqrt (OMA.S_mo_353710.q B x) ≤
          Real.sqrt (OMA.S_mo_353710.op A) + Real.sqrt (OMA.S_mo_353710.op B) :=
      add_le_add (Real.sqrt_le_sqrt hqAop) (Real.sqrt_le_sqrt hqBop)
    have hsum_nonneg : 0 ≤ Real.sqrt (OMA.S_mo_353710.q A x) + Real.sqrt (OMA.S_mo_353710.q B x) :=
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [hdiff, hfac, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (sq_le_sq' (by linarith) hsum_le) (sq_nonneg _)
  have hintL : Integrable (fun x : OMA.S_mo_353710.E d => (OMA.S_mo_353710.q (A - B) x) ^ 2) μ := by
    refine integrable_of_continuous hμ ?_
    have hqcont : Continuous (fun x : OMA.S_mo_353710.E d => OMA.S_mo_353710.q (A - B) x) := by
      simp_rw [q_eq_sum]
      exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        (continuous_const.mul (continuous_coord i)).mul (continuous_coord j)
    exact hqcont.pow 2
  have hintR : Integrable (fun x : OMA.S_mo_353710.E d =>
      (Real.sqrt (OMA.S_mo_353710.q A x) - Real.sqrt (OMA.S_mo_353710.q B x)) ^ 2) μ := by
    refine integrable_of_continuous hμ ?_
    have hqcont : ∀ M : OMA.S_mo_353710.Mat d,
        Continuous (fun x : OMA.S_mo_353710.E d => OMA.S_mo_353710.q M x) := fun M => by
      simp_rw [q_eq_sum]
      exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        (continuous_const.mul (continuous_coord i)).mul (continuous_coord j)
    exact ((Real.continuous_sqrt.comp (hqcont A)).sub (Real.continuous_sqrt.comp (hqcont B))).pow 2
  have hint_le := integral_mono_ae hintL (hintR.const_mul _) hae
  rw [hmom, integral_const_mul] at hint_le
  have hddpos : 0 < (d : ℝ) * ((d : ℝ) + 2) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hint_le hddpos.le
  have hne : (d : ℝ) * ((d : ℝ) + 2) ≠ 0 := hddpos.ne'
  calc (A - B).trace ^ 2 + 2 * ((A - B) * (A - B)).trace
      = (d : ℝ) * ((d : ℝ) + 2) *
          (1 / ((d : ℝ) * ((d : ℝ) + 2)) * ((A - B).trace ^ 2 + 2 * ((A - B) * (A - B)).trace)) := by
        field_simp [hne]
    _ ≤ (d : ℝ) * ((d : ℝ) + 2) *
          ((Real.sqrt (OMA.S_mo_353710.op A) + Real.sqrt (OMA.S_mo_353710.op B)) ^ 2 *
            OMA.S_mo_353710.squared μ A B) := hmul
    _ = (d : ℝ) * ((d : ℝ) + 2) *
          (Real.sqrt (OMA.S_mo_353710.op A) + Real.sqrt (OMA.S_mo_353710.op B)) ^ 2 *
          OMA.S_mo_353710.squared μ A B := by ring

private lemma part2 {d : ℕ} (hd : 0 < d) {μ : Measure (OMA.S_mo_353710.E d)}
    [IsProbabilityMeasure μ] (hμ : OMA.S_mo_353710.IsUniform μ)
    (A B : OMA.S_mo_353710.Mat d) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    OMA.S_mo_353710.squared μ A B = 0 ↔ A = B := by
  constructor
  · intro h0
    have hle := part1 hd hμ A B hA hB
    rw [h0, mul_zero] at hle
    have hC : (A - B).IsHermitian := hA.1.sub hB.1
    have hsymm : ∀ i j : Fin d, (A - B) j i = (A - B) i j := by
      intro i j
      have h := congrFun (congrFun hC i) j
      simpa [Matrix.conjTranspose_apply] using h
    have htr_sq : ((A - B) * (A - B)).trace = ∑ i : Fin d, ∑ j : Fin d, ((A - B) i j) ^ 2 := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hsymm j i, sq]
    have hsum_nonneg : 0 ≤ ∑ i : Fin d, ∑ j : Fin d, ((A - B) i j) ^ 2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    have hsum_zero : ∑ i : Fin d, ∑ j : Fin d, ((A - B) i j) ^ 2 = 0 := by
      nlinarith [sq_nonneg (A - B).trace, htr_sq, hle, hsum_nonneg]
    ext i j
    have hi : ∑ j' : Fin d, ((A - B) i j') ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i' _ =>
        Finset.sum_nonneg fun j' _ => sq_nonneg _)).mp hsum_zero i (Finset.mem_univ i)
    have hij : ((A - B) i j) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j' _ => sq_nonneg _)).mp hi j (Finset.mem_univ j)
    have hsub : (A - B) i j = 0 := sq_eq_zero_iff.mp hij
    simp only [Matrix.sub_apply] at hsub
    linarith
  · rintro rfl
    simp [OMA.S_mo_353710.squared]

private lemma part3 {d : ℕ} {μ : Measure (OMA.S_mo_353710.E d)}
    [IsProbabilityMeasure μ] (hμ : OMA.S_mo_353710.IsUniform μ)
    (a b : ℝ) (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    OMA.S_mo_353710.squared μ (a • (1 : OMA.S_mo_353710.Mat d)) (b • (1 : OMA.S_mo_353710.Mat d)) =
      (Real.sqrt a - Real.sqrt b) ^ 2 := by
  unfold OMA.S_mo_353710.squared
  have hae : ∀ᵐ x ∂μ,
      (Real.sqrt (OMA.S_mo_353710.q (a • (1 : OMA.S_mo_353710.Mat d)) x) -
        Real.sqrt (OMA.S_mo_353710.q (b • (1 : OMA.S_mo_353710.Mat d)) x)) ^ 2 =
      (Real.sqrt a - Real.sqrt b) ^ 2 := by
    filter_upwards [hμ.1] with x hx
    have hq_smul : ∀ c : ℝ, OMA.S_mo_353710.q (c • (1 : OMA.S_mo_353710.Mat d)) x = c := by
      intro c
      rw [q_eq_sum]
      have h1 : ∑ i : Fin d, ∑ j : Fin d, (c • (1 : OMA.S_mo_353710.Mat d)) i j * x i * x j =
          c * ∑ i : Fin d, (x i) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_eq_single i]
        · simp [sq]; ring
        · intro j _ hji
          simp [Matrix.one_apply_ne (Ne.symm hji)]
        · intro hi
          exact absurd (Finset.mem_univ i) hi
      rw [h1, ← norm_sq_eq_sum_sq, hx, one_pow, mul_one]
    rw [hq_smul a, hq_smul b]
  rw [integral_congr_ae hae]
  simp

end OMA.S_mo_353710_Proof

theorem OMA.solution : type_of% @OMA.S_mo_353710.main := by
  intro d hd μ _ hμ
  exact ⟨OMA.S_mo_353710_Proof.part1 hd hμ, OMA.S_mo_353710_Proof.part2 hd hμ,
    OMA.S_mo_353710_Proof.part3 hμ⟩
