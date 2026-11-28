import OMAReductions.R_OeisA117531_conjecture_R1

/-!
# A short prime test for the Rabinowitsch implication

For every p ≥ 2 it suffices to test t(t+1)+p for (2t+1)² ≤ 4p−1.
A root modulo a small prime gives two reflected residues whose smaller
representative lies in this interval. This excludes a composite discriminant
and excludes nonprincipal prime ideals up to the Minkowski bound.

This proves H1 of Marcus Buffett's reduction (project PR 2717). The
prime-ideal argument is adapted from PanPapag's prime-row proof (PR 3756).
The quadratic field and ideal-norm lemmas are adapted from the
tenth-discriminant authors (DrMurphyIsIn and contributors, Apache-2.0),
github.com/DrMurphyIsIn/tenth-discriminant, commit
9078b2bbf205e494b659035465b73e3451738463, via Steven Enamakel's PR 3263.
See also P. Ribenboim, Euler's Famous Prime Generating Polynomial and the
Class Number of Imaginary Quadratic Fields, section G (1988).
-/

section
namespace CN1.Foundations
open NumberField Module Polynomial
def disc (m : ℕ) : ℕ := if m % 4 = 3 then m else 4 * m
variable {K : Type*} [Field K] [NumberField K]
noncomputable def omega (m : ℕ) (α : K) : K := if m % 4 = 3 then (1 + α) / 2 else α
lemma squarefree_not_four_dvd {m : ℕ} (hm : Squarefree m) : ¬ 4 ∣ m := fun h ↦ by
  have := Nat.isUnit_iff.mp (hm 2 (by simpa using h))
  omega
lemma squarefree_mod_four_ne_zero {m : ℕ} (hm : Squarefree m) : m % 4 ≠ 0 :=
  fun h ↦ squarefree_not_four_dvd hm (Nat.dvd_of_mod_eq_zero h)
section FieldModel
variable {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
include hα in
lemma alpha_ne_zero (hm : m ≠ 0) : α ≠ 0 := by
  rintro rfl
  have h : (m : K) = 0 := by rw [← neg_eq_zero, ← hα]; simp
  exact hm (by exact_mod_cast h)
include hα in
lemma linearIndependent_one_alpha (hm : m ≠ 0) : LinearIndependent ℚ ![(1 : K), α] := by
  rw [linearIndependent_fin2]
  refine ⟨by simpa using alpha_ne_zero hα hm, fun a ha ↦ ?_⟩
  change a • α = 1 at ha
  have h2 : ((a : K)) ^ 2 * α ^ 2 = 1 := by rw [← mul_pow, ← Rat.smul_def, ha, one_pow]
  rw [hα] at h2
  have h3 : ((a ^ 2 * (-(m : ℚ)) : ℚ) : K) = ((1 : ℚ) : K) := by push_cast; exact h2
  have h4 : a ^ 2 * (-(m : ℚ)) = 1 := Rat.cast_injective h3
  have h5 : (0 : ℚ) ≤ a ^ 2 := sq_nonneg a
  have h6 : (0 : ℚ) ≤ m := Nat.cast_nonneg m
  nlinarith
variable (hK : finrank ℚ K = 2) (hm : m ≠ 0)
include hα hK hm
noncomputable def qBasis : Basis (Fin 2) ℚ K :=
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_one_alpha hα hm) (by simp [hK])
lemma qBasis_zero : qBasis hα hK hm 0 = 1 := by simp [qBasis]
lemma qBasis_one : qBasis hα hK hm 1 = α := by simp [qBasis]
lemma qBasis_repr (x : K) (c : Fin 2 → ℚ) (h : x = (c 0 : K) + (c 1 : K) * α) :
    (qBasis hα hK hm).repr x = c := by
  conv_rhs => rw [← (qBasis hα hK hm).repr_sum_self c]
  congr 1
  rw [h, Fin.sum_univ_two, qBasis_zero, qBasis_one, Rat.smul_def, Rat.smul_def, mul_one]
theorem exists_rat_add_rat_mul_alpha (x : K) : ∃ a b : ℚ, x = (a : K) + (b : K) * α := by
  refine ⟨(qBasis hα hK hm).repr x 0, (qBasis hα hK hm).repr x 1, ?_⟩
  conv_lhs => rw [← (qBasis hα hK hm).sum_repr x]
  rw [Fin.sum_univ_two, qBasis_zero, qBasis_one, Rat.smul_def, Rat.smul_def, mul_one]
theorem rat_add_rat_mul_alpha_inj {a b a' b' : ℚ}
    (h : (a : K) + (b : K) * α = (a' : K) + (b' : K) * α) : a = a' ∧ b = b' := by
  have h1 := qBasis_repr hα hK hm ((a : K) + (b : K) * α) ![a, b] (by simp)
  have h2 := qBasis_repr hα hK hm ((a' : K) + (b' : K) * α) ![a', b'] (by simp)
  rw [h, h2] at h1
  exact ⟨by simpa using (congrFun h1 0).symm, by simpa using (congrFun h1 1).symm⟩
lemma leftMulMatrix_rat_add_rat_mul_alpha (a b : ℚ) :
    Algebra.leftMulMatrix (qBasis hα hK hm) ((a : K) + (b : K) * α) =
      !![a, -(m : ℚ) * b; b, a] := by
  set B := qBasis hα hK hm with hB
  have h0 : B.repr (((a : K) + (b : K) * α) * B 0) = ![a, b] := by
    rw [hB, qBasis_zero, mul_one]
    exact qBasis_repr hα hK hm _ _ (by simp)
  have h1 : B.repr (((a : K) + (b : K) * α) * B 1) = ![-(m : ℚ) * b, a] := by
    rw [hB, qBasis_one]
    refine qBasis_repr hα hK hm _ _ ?_
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    push_cast
    linear_combination (b : K) * hα
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Algebra.leftMulMatrix_eq_repr_mul, h0, h1]
theorem trace_rat_add_rat_mul_alpha (a b : ℚ) :
    Algebra.trace ℚ K ((a : K) + (b : K) * α) = 2 * a := by
  rw [Algebra.trace_eq_matrix_trace (qBasis hα hK hm),
    leftMulMatrix_rat_add_rat_mul_alpha hα hK hm, Matrix.trace_fin_two_of]
  ring
theorem norm_rat_add_rat_mul_alpha (a b : ℚ) :
    Algebra.norm ℚ ((a : K) + (b : K) * α) = a ^ 2 + m * b ^ 2 := by
  rw [Algebra.norm_eq_matrix_det (qBasis hα hK hm),
    leftMulMatrix_rat_add_rat_mul_alpha hα hK hm, Matrix.det_fin_two_of]
  ring
end FieldModel
section RingOfIntegers
variable {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
include hα in
theorem omega_isIntegral : IsIntegral ℤ (omega m α) := by
  unfold omega
  split_ifs with h3
  · obtain ⟨c, hc⟩ : (4 : ℤ) ∣ (m : ℤ) + 1 := by omega
    refine ⟨X ^ 2 - X + C c, by monicity!, ?_⟩
    have hcK : (c : K) * 4 = (m : K) + 1 := by exact_mod_cast (by linarith : (c : ℤ) * 4 = m + 1)
    simp only [eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, algebraMap_int_eq,
      Int.coe_castRingHom]
    linear_combination (1 / 4 : K) * hα + (1 / 4 : K) * hcK
  · exact IsIntegral.of_pow two_pos (hα ▸ (isIntegral_natCast m).neg)
lemma exists_int_eq_two_mul_of_sq {m : ℕ} (hm : Squarefree m) {b : ℚ} {k : ℤ}
    (h : (m : ℚ) * (2 * b) ^ 2 = k) : ∃ v : ℤ, (v : ℚ) = 2 * b := by
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne_zero
  have hint : IsIntegral ℤ ((m : ℚ) * (2 * b)) := by
    refine IsIntegral.of_pow two_pos ?_
    have : ((m : ℚ) * (2 * b)) ^ 2 = ((m * k : ℤ) : ℚ) := by
      push_cast; rw [← h]; ring
    rw [this]; exact isIntegral_intCast _
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  simp only [algebraMap_int_eq, Int.coe_castRingHom] at hw
  have hw2 : w ^ 2 = m * k := by
    have : ((w ^ 2 : ℤ) : ℚ) = ((m * k : ℤ) : ℚ) := by
      push_cast; rw [hw]; linear_combination (m : ℚ) * h
    exact_mod_cast this
  have hdvd : (m : ℤ) ∣ w :=
    ((Int.squarefree_natCast.mpr hm).dvd_pow_iff_dvd two_ne_zero).mp ⟨k, hw2⟩
  obtain ⟨v, hv⟩ := hdvd
  refine ⟨v, mul_left_cancel₀ hm0 ?_⟩
  rw [← hw, hv]; push_cast; ring
lemma zmod_four_three (t v : ZMod 4) (h : t ^ 2 + 3 * v ^ 2 = 0) : 2 * (t - v) = 0 := by
  revert t v; decide
lemma zmod_four_one (t v : ZMod 4) (h : t ^ 2 + v ^ 2 = 0) : 2 * t = 0 ∧ 2 * v = 0 := by
  revert t v; decide
lemma zmod_four_two (t v : ZMod 4) (h : t ^ 2 + 2 * v ^ 2 = 0) : 2 * t = 0 ∧ 2 * v = 0 := by
  revert t v; decide
variable (hK : finrank ℚ K = 2) (hm : Squarefree m)
include hα hK hm in
theorem exists_int_add_int_mul_omega_of_isIntegral {x : K} (hx : IsIntegral ℤ x) :
    ∃ u v : ℤ, x = (u : K) + (v : K) * omega m α := by
  have hm0 := hm.ne_zero
  obtain ⟨a, b, rfl⟩ := exists_rat_add_rat_mul_alpha hα hK hm0 x
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace (L := ℚ) hx)
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_norm (K := ℚ) hx)
  rw [trace_rat_add_rat_mul_alpha hα hK hm0] at ht
  rw [norm_rat_add_rat_mul_alpha hα hK hm0] at hn
  simp only [algebraMap_int_eq, Int.coe_castRingHom] at ht hn
  obtain ⟨v, hv⟩ := exists_int_eq_two_mul_of_sq hm (b := b) (k := 4 * n - t ^ 2)
    (by push_cast; rw [hn, ht]; ring)
  have h4 : (4 : ℤ) ∣ t ^ 2 + m * v ^ 2 := by
    refine ⟨n, ?_⟩
    have : ((t ^ 2 + m * v ^ 2 : ℤ) : ℚ) = ((4 * n : ℤ) : ℚ) := by
      push_cast; rw [hv, ht, hn]; ring
    exact_mod_cast this
  have h4' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr h4
  push_cast at h4'
  have ht' : (t : K) = 2 * (a : K) := by exact_mod_cast congrArg (Rat.cast (K := K)) ht
  have hv' : (v : K) = 2 * (b : K) := by exact_mod_cast congrArg (Rat.cast (K := K)) hv
  unfold omega
  split_ifs with h3
  · have hm4 : ((m : ℕ) : ZMod 4) = 3 := by
      rw [← ZMod.natCast_mod, h3]; rfl
    rw [hm4] at h4'
    have key := zmod_four_three _ _ h4'
    have h2 : (2 : ℤ) ∣ t - v := by
      have : ((2 * (t - v) : ℤ) : ZMod 4) = 0 := by push_cast; exact key
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp this
      omega
    obtain ⟨u, hu⟩ := h2
    refine ⟨u, v, ?_⟩
    have hu' : (t : K) - (v : K) = 2 * (u : K) := by exact_mod_cast hu
    linear_combination (-1 / 2 : K) * ht' + (-α / 2) * hv' + (1 / 2 : K) * hu'
  · have h12 : m % 4 = 1 ∨ m % 4 = 2 := by have := squarefree_mod_four_ne_zero hm; omega
    have h2 : (2 : ℤ) ∣ t ∧ (2 : ℤ) ∣ v := by
      have key : 2 * (t : ZMod 4) = 0 ∧ 2 * (v : ZMod 4) = 0 := by
        rcases h12 with h1 | h1
        · have hm4 : ((m : ℕ) : ZMod 4) = 1 := by rw [← ZMod.natCast_mod, h1]; rfl
          rw [hm4, one_mul] at h4'
          exact zmod_four_one _ _ h4'
        · have hm4 : ((m : ℕ) : ZMod 4) = 2 := by rw [← ZMod.natCast_mod, h1]; rfl
          rw [hm4] at h4'
          exact zmod_four_two _ _ h4'
      constructor
      · have : ((2 * t : ℤ) : ZMod 4) = 0 := by push_cast; exact key.1
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp this
        omega
      · have : ((2 * v : ℤ) : ZMod 4) = 0 := by push_cast; exact key.2
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp this
        omega
    obtain ⟨⟨u, hu⟩, ⟨w, hw⟩⟩ := h2
    refine ⟨u, w, ?_⟩
    have hu' : (t : K) = 2 * (u : K) := by exact_mod_cast hu
    have hw' : (v : K) = 2 * (w : K) := by exact_mod_cast hw
    linear_combination (-1 / 2 : K) * ht' + (-α / 2) * hv' + (1 / 2 : K) * hu' + (α / 2) * hw'
include hα hK in
theorem int_add_int_mul_omega_inj (hm0 : m ≠ 0) {u v u' v' : ℤ}
    (h : (u : K) + (v : K) * omega m α = (u' : K) + (v' : K) * omega m α) : u = u' ∧ v = v' := by
  unfold omega at h
  split_ifs at h with h3
  · have e : ∀ x y : ℤ, (x : K) + (y : K) * ((1 + α) / 2) =
        (((x : ℚ) + (y : ℚ) / 2 : ℚ) : K) + (((y : ℚ) / 2 : ℚ) : K) * α := by
      intro x y; push_cast; ring
    rw [e, e] at h
    obtain ⟨h1, h2⟩ := rat_add_rat_mul_alpha_inj hα hK hm0 h
    have hv : v = v' := by
      have : (v : ℚ) = v' := by linarith
      exact_mod_cast this
    refine ⟨?_, hv⟩
    have : (u : ℚ) = u' := by rw [hv] at h1; linarith
    exact_mod_cast this
  · have e : ∀ x y : ℤ, (x : K) + (y : K) * α = ((x : ℚ) : K) + ((y : ℚ) : K) * α := by
      intro x y; push_cast; ring
    rw [e, e] at h
    obtain ⟨h1, h2⟩ := rat_add_rat_mul_alpha_inj hα hK hm0 h
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
noncomputable def omegaInt : 𝓞 K := ⟨omega m α, omega_isIntegral hα⟩
lemma coe_omegaInt : (omegaInt hα : K) = omega m α := rfl
lemma coe_int_add_int_mul_omegaInt (u v : ℤ) :
    (((u : 𝓞 K) + (v : 𝓞 K) * omegaInt hα : 𝓞 K) : K) = (u : K) + (v : K) * omega m α := by
  rw [RingOfIntegers.coe_eq_algebraMap]; simp [coe_omegaInt]
include hα hK hm in
theorem exists_int_add_int_mul_omegaInt (z : 𝓞 K) :
    ∃ u v : ℤ, z = (u : 𝓞 K) + (v : 𝓞 K) * omegaInt hα := by
  obtain ⟨u, v, h⟩ := exists_int_add_int_mul_omega_of_isIntegral hα hK hm z.isIntegral_coe
  exact ⟨u, v, RingOfIntegers.ext (by rw [coe_int_add_int_mul_omegaInt]; exact h)⟩
include hα hK in
theorem int_add_int_mul_omegaInt_inj (hm0 : m ≠ 0) {u v u' v' : ℤ}
    (h : (u : 𝓞 K) + (v : 𝓞 K) * omegaInt hα = (u' : 𝓞 K) + (v' : 𝓞 K) * omegaInt hα) :
    u = u' ∧ v = v' := by
  apply int_add_int_mul_omega_inj hα hK hm0
  rw [← coe_int_add_int_mul_omegaInt hα, ← coe_int_add_int_mul_omegaInt hα, h]
noncomputable def intBasis : Basis (Fin 2) ℤ (𝓞 K) :=
  Basis.mk (v := ![1, omegaInt hα])
    (by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h : (s : 𝓞 K) + (t : 𝓞 K) * omegaInt hα =
          ((0 : ℤ) : 𝓞 K) + ((0 : ℤ) : 𝓞 K) * omegaInt hα := by
        simpa [zsmul_eq_mul] using hst
      exact int_add_int_mul_omegaInt_inj hα hK hm.ne_zero h)
    (by
      rintro z -
      rw [Submodule.mem_span_range_iff_exists_fun]
      obtain ⟨u, v, huv⟩ := exists_int_add_int_mul_omegaInt hα hK hm z
      refine ⟨![u, v], ?_⟩
      rw [huv, Fin.sum_univ_two]
      simp [zsmul_eq_mul])
lemma intBasis_zero : intBasis hα hK hm 0 = 1 := by simp [intBasis]
lemma intBasis_one : intBasis hα hK hm 1 = omegaInt hα := by simp [intBasis]
end RingOfIntegers
section NormForm
variable {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K)) (hK : finrank ℚ K = 2) (hm0 : m ≠ 0)
include hα hK hm0 in
theorem trace_int_add_int_mul_omega (x y : ℤ) :
    Algebra.trace ℚ K ((x : K) + (y : K) * omega m α) =
      if m % 4 = 3 then (2 * x + y : ℚ) else (2 * x : ℚ) := by
  unfold omega
  split_ifs with h3
  · have e : (x : K) + (y : K) * ((1 + α) / 2) =
        (((x : ℚ) + (y : ℚ) / 2 : ℚ) : K) + (((y : ℚ) / 2 : ℚ) : K) * α := by push_cast; ring
    rw [e, trace_rat_add_rat_mul_alpha hα hK hm0]; ring
  · have e : (x : K) + (y : K) * α = ((x : ℚ) : K) + ((y : ℚ) : K) * α := by push_cast; ring
    rw [e, trace_rat_add_rat_mul_alpha hα hK hm0]
end NormForm
end CN1.Foundations
end

section
namespace CN1.Foundations
open NumberField Module
variable {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
  (hK : finrank ℚ K = 2)
include hα hK in
theorem trace_int_eq (hm0 : m ≠ 0) {z : 𝓞 K} {x y : ℤ}
    (h : z = (x : 𝓞 K) + (y : 𝓞 K) * omegaInt hα) :
    Algebra.trace ℤ (𝓞 K) z = if m % 4 = 3 then 2 * x + y else 2 * x := by
  apply Int.cast_injective (α := ℚ)
  rw [Algebra.coe_trace_int, h, coe_int_add_int_mul_omegaInt, trace_int_add_int_mul_omega hα hK hm0]
  split_ifs <;> push_cast <;> ring
include hα in
theorem omegaInt_sq :
    omegaInt hα ^ 2 = ((if m % 4 = 3 then -(((m + 1) / 4 : ℕ) : ℤ) else -(m : ℤ) : ℤ) : 𝓞 K) +
      ((if m % 4 = 3 then 1 else 0 : ℤ) : 𝓞 K) * omegaInt hα := by
  apply RingOfIntegers.ext
  rw [coe_int_add_int_mul_omegaInt, RingOfIntegers.coe_eq_algebraMap, map_pow,
    ← RingOfIntegers.coe_eq_algebraMap, coe_omegaInt]
  unfold omega
  split_ifs with h3
  · obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
    have hc' : ((m + 1) / 4 : ℕ) = c := by omega
    rw [hc']
    push_cast
    have hcK : (m : K) + 1 = 4 * c := by exact_mod_cast hc
    linear_combination (1 / 4 : K) * hα + (-1 / 4 : K) * hcK
  · push_cast
    linear_combination hα
include hα hK in
theorem discr_eq (hm : Squarefree m) : NumberField.discr K = -(disc m : ℤ) := by
  have hm0 := hm.ne_zero
  rw [← NumberField.discr_eq_discr K (intBasis hα hK hm), Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, intBasis_zero, intBasis_one,
    one_mul, mul_one]
  have h1 : Algebra.trace ℤ (𝓞 K) (1 : 𝓞 K) = if m % 4 = 3 then 2 * 1 + 0 else 2 * 1 :=
    trace_int_eq hα hK hm0 (x := 1) (y := 0) (by simp)
  have h2 : Algebra.trace ℤ (𝓞 K) (omegaInt hα) = if m % 4 = 3 then 2 * 0 + 1 else 2 * 0 :=
    trace_int_eq hα hK hm0 (x := 0) (y := 1) (by simp)
  have h3 : Algebra.trace ℤ (𝓞 K) (omegaInt hα * omegaInt hα) =
      if m % 4 = 3 then 2 * (if m % 4 = 3 then -(((m + 1) / 4 : ℕ) : ℤ) else -(m : ℤ)) +
        (if m % 4 = 3 then 1 else 0) else
        2 * (if m % 4 = 3 then -(((m + 1) / 4 : ℕ) : ℤ) else -(m : ℤ)) :=
    trace_int_eq hα hK hm0 (by rw [← sq, omegaInt_sq hα])
  rw [h1, h2, h3]
  unfold disc
  split_ifs with h3
  · obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
    have hc' : ((m + 1) / 4 : ℕ) = c := by omega
    rw [hc']
    have : (m : ℤ) + 1 = 4 * c := by exact_mod_cast hc
    linear_combination this
  · push_cast; ring
end CN1.Foundations
end

section
open NumberField NumberField.InfinitePlace Ideal Module Real Nat
namespace CN1.Finite
variable {K : Type*} [Field K] [NumberField K]
theorem le_two_thirds_sqrt_of_le_minkowski (hK : finrank ℚ K = 2) {d : ℕ}
    (hdisc : |discr K| ≤ (d : ℤ)) {N : ℕ}
    (hle : (N : ℝ) ≤ (4 / π) ^ nrComplexPlaces K *
      ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|(discr K : ℝ)|)) :
    (N : ℝ) ≤ 2 / 3 * √(d : ℝ) := by
  have hr2 : nrComplexPlaces K ≤ 1 := by
    have := card_add_two_mul_card_eq_rank K
    omega
  have h1 : (1 : ℝ) ≤ 4 / π := by
    rw [le_div_iff₀ pi_pos]; linarith [pi_le_four]
  have hpi : (4 / π : ℝ) ≤ 4 / 3 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) pi_gt_three.le
  have hpow : (4 / π : ℝ) ^ nrComplexPlaces K ≤ 4 / 3 :=
    (pow_le_pow_right₀ h1 hr2).trans (by rw [pow_one]; exact hpi)
  have hsqrt : √|(discr K : ℝ)| ≤ √(d : ℝ) := by
    apply Real.sqrt_le_sqrt
    rw [← Int.cast_abs]
    exact_mod_cast hdisc
  have hM : (4 / π : ℝ) ^ nrComplexPlaces K *
      ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|(discr K : ℝ)|) ≤ 2 / 3 * √(d : ℝ) := by
    rw [hK]
    have key := mul_le_mul hpow hsqrt (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 4 / 3)
    norm_num [Nat.factorial]
    nlinarith [key]
  exact hle.trans hM
theorem nat_lt_of_le_two_thirds_sqrt {N d B : ℕ} (hN : (N : ℝ) ≤ 2 / 3 * √(d : ℝ))
    (hB : 4 * d < 9 * B ^ 2) : N < B := by
  have hB0 : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h | h
    · subst h; simp at hB
    · exact h
  have hB0' : (0 : ℝ) < 3 * B / 2 := by positivity
  have hs : √(d : ℝ) < 3 * B / 2 := by
    rw [Real.sqrt_lt' hB0']
    have : (4 * d : ℝ) < 9 * (B : ℝ) ^ 2 := by exact_mod_cast hB
    nlinarith
  have : (N : ℝ) < B := by nlinarith
  exact_mod_cast this
theorem absNorm_maximal_cases (hK : finrank ℚ K = 2) (P : Ideal (𝓞 K)) [hP : P.IsMaximal] :
    ∃ q : ℕ, q.Prime ∧ (q : 𝓞 K) ∈ P ∧
      (absNorm P = q ∨ (absNorm P = q ^ 2 ∧ P = span {(q : 𝓞 K)})) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  obtain ⟨q, hq⟩ := CharP.exists (𝓞 K ⧸ P)
  obtain ⟨n, hqprime, hcard⟩ := FiniteField.card (𝓞 K ⧸ P) q
  have hN : absNorm P = q ^ (n : ℕ) := by
    rw [absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hcard]
  have hqmem : (q : 𝓞 K) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ q
  have hle : span {(q : 𝓞 K)} ≤ P := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hqmem)
  have hspan : absNorm (span {(q : 𝓞 K)}) = q ^ 2 := by
    rw [absNorm_span_singleton, ← map_natCast (algebraMap ℤ (𝓞 K)), Algebra.norm_algebraMap,
      RingOfIntegers.rank, hK, Int.natAbs_pow, Int.natAbs_natCast]
  have hdvd := absNorm_dvd_absNorm_of_le hle
  rw [hN, hspan, Nat.pow_dvd_pow_iff_le_right hqprime.one_lt] at hdvd
  refine ⟨q, hqprime, hqmem, ?_⟩
  rcases (show (n : ℕ) = 1 ∨ (n : ℕ) = 2 by have := n.pos; omega) with h | h
  · left; rw [hN, h, pow_one]
  · right
    refine ⟨by rw [hN, h], ?_⟩
    obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.mpr hle
    have hmul := congrArg absNorm hC
    rw [map_mul, hspan, hN, h] at hmul
    have hC1 : absNorm C = 1 := by
      have hq0 : 0 < q ^ 2 := pow_pos hqprime.pos 2
      have : q ^ 2 * absNorm C = q ^ 2 * 1 := by rw [mul_one]; exact hmul.symm
      exact Nat.eq_of_mul_eq_mul_left hq0 this
    rw [absNorm_eq_one_iff] at hC1
    rw [hC, hC1, mul_top]
theorem not_absNorm_eq_of_no_root (θ : 𝓞 K) (t c : ℤ)
    (hθ : θ ^ 2 = (t : 𝓞 K) * θ - (c : 𝓞 K))
    (P : Ideal (𝓞 K)) [hP : P.IsMaximal] (q : ℕ) (hq : q.Prime) (hN : absNorm P = q)
    (hroot : ∀ z : ZMod q, z ^ 2 - (t : ZMod q) * z + (c : ZMod q) ≠ 0) : False := by
  haveI := Fact.mk hq
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 K ⧸ P) = q := by
    rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← absNorm_apply, hN]
  haveI : CharP (𝓞 K ⧸ P) q := charP_of_card_eq_prime hcard
  let f : ZMod q →+* 𝓞 K ⧸ P := ZMod.castHom dvd_rfl _
  have hf : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨f.injective, by rw [ZMod.card, hcard]⟩
  obtain ⟨z, hz⟩ := hf.2 (Ideal.Quotient.mk P θ)
  apply hroot z
  apply f.injective
  have hθ' := congrArg (Ideal.Quotient.mk P) hθ
  simp only [map_pow, map_sub, map_mul, map_intCast] at hθ'
  rw [map_add, map_sub, map_mul, map_pow, map_zero, hz, map_intCast, map_intCast, hθ']
  ring
end CN1.Finite
end

namespace ELEM
def cq (q : ℕ) : ℕ := (q + 1) / 4
def IsInert (c p : ℕ) : Prop := ∀ r : ZMod p, r ^ 2 ≠ -(c : ZMod p) + 1 * r
theorem not_isInert_of_dvd {c p : ℕ} {y : ℤ} (hy : (p : ℤ) ∣ y ^ 2 - y + c) : ¬ IsInert c p := by
  intro h
  apply h (y : ZMod p)
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hy
  push_cast at this
  linear_combination this
theorem not_isInert_of_dvd_q {p q : ℕ} (hp : p.Prime) (hp2 : p % 2 = 1) (hq : q % 4 = 3)
    (hpq : p ∣ q) : ¬ IsInert (cq q) p := by
  set y : ℤ := (((p + 1) / 2 : ℕ) : ℤ) with hy
  have h2 : 2 * y = p + 1 := by
    have : 2 * ((p + 1) / 2) = p + 1 := by omega
    rw [hy]; exact_mod_cast this
  have h4 : 4 * (cq q : ℤ) = q + 1 := by
    have : 4 * cq q = q + 1 := by unfold cq; omega
    exact_mod_cast this
  have hid : 4 * (y ^ 2 - y + cq q) = (p : ℤ) ^ 2 + q := by
    linear_combination (2 * y + (p : ℤ) + 1) * h2 - 2 * h2 + h4
  have hdvd4 : (p : ℤ) ∣ 4 * (y ^ 2 - y + cq q) := by
    rw [hid]
    exact dvd_add (dvd_pow_self _ two_ne_zero) (Int.natCast_dvd_natCast.mpr hpq)
  have hcop : IsCoprime (p : ℤ) 4 := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : Nat.Coprime p 4 := by
      have h2' : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
      simpa using Nat.Coprime.pow_right 2 h2'
    simpa [Int.gcd] using this
  exact not_isInert_of_dvd (hcop.dvd_of_dvd_mul_left hdvd4)
end ELEM

section Bridge
open Polynomial NumberField

theorem OMABridge_monic (d : ℤ) : (X ^ 2 - C (d : ℚ) : ℚ[X]).Monic :=
  Polynomial.monic_X_pow_sub_C _ (by norm_num)

theorem OMABridge_deg (d : ℤ) : (X ^ 2 - C (d : ℚ) : ℚ[X]).natDegree = 2 :=
  Polynomial.natDegree_X_pow_sub_C

theorem OMABridge_irred (d : ℤ) (hd : d < 0) : Irreducible (X ^ 2 - C (d : ℚ) : ℚ[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [OMABridge_deg]; simp
  · intro x hx
    simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C] at hx
    have h1 : x ^ 2 = (d : ℚ) := sub_eq_zero.mp hx
    have h2 : (d : ℚ) < 0 := by exact_mod_cast hd
    nlinarith [sq_nonneg x]

end Bridge

namespace OMA.PrimeRow
open CN1.Finite CN1.Foundations NumberField Polynomial Ideal

/-- The smaller of the two reflected residues witnesses failure of the prime test. -/
lemma inert_of_short_row {p m q : ℕ}
    (row : ∀ t : ℕ, (2 * t + 1) ^ 2 ≤ m → (t * (t + 1) + p).Prime)
    (hq : q.Prime) (hqp : q < p) (hsq : q ^ 2 ≤ m) : ELEM.IsInert p q := by
  have : NeZero q := ⟨hq.ne_zero⟩
  intro z hz
  let r := (-z).val
  let s := q - 1 - r
  have hr : r < q := ZMod.val_lt _
  have hsum : s + 1 + r = q := by dsimp [s]; omega
  have hcast : (r : ZMod q) = -z := ZMod.natCast_zmod_val _
  have hroot : (r : ZMod q) * (r + 1) + p = 0 := by
    rw [hcast]
    linear_combination hz
  have hreflect : (s : ZMod q) + 1 + r = 0 := by
    exact_mod_cast (show ((s + 1 + r : ℕ) : ZMod q) = 0 by rw [hsum]; simp)
  have impossible (t : ℕ) (ht : 2 * t + 1 ≤ q)
      (hroot' : (t : ZMod q) * (t + 1) + p = 0) : False := by
    have hd : q ∣ t * (t + 1) + p := (ZMod.natCast_eq_zero_iff _ _).mp (by simpa using hroot')
    exact Nat.not_prime_of_dvd_of_lt hd hq.two_le (by omega)
      (row t ((Nat.pow_le_pow_left ht 2).trans hsq))
  by_cases hrs : r ≤ s
  · exact impossible r (by omega) hroot
  · apply impossible s (by omega)
    linear_combination hroot + (s - (r : ZMod q)) * hreflect

/-- A composite discriminant has a small ramified prime, excluded by the row. -/
lemma prime_discriminant {p m : ℕ} (hp : 2 ≤ p) (hm : m + 1 = 4 * p)
    (inert : ∀ q : ℕ, q.Prime → q < p → q ^ 2 ≤ m → ELEM.IsInert p q) : m.Prime := by
  by_cases hsmallp : p < 4
  · obtain rfl | rfl : m = 7 ∨ m = 11 := by omega
    all_goals decide
  by_contra h
  have hfac := Nat.minFac_prime (show m ≠ 1 by omega)
  have hsq := Nat.minFac_sq_le_self (show 0 < m by omega) h
  have hsmall : m.minFac < p := by
    by_contra! hge
    nlinarith [Nat.mul_self_le_mul_self hge, Nat.mul_le_mul_right p (show 4 ≤ p by omega)]
  have hodd : m.minFac % 2 = 1 := by
    rcases hfac.eq_two_or_odd with he | he
    · have hd := Nat.minFac_dvd m
      rw [he] at hd
      omega
    · exact he
  have hsplit := ELEM.not_isInert_of_dvd_q hfac hodd (show m % 4 = 3 by omega) (Nat.minFac_dvd m)
  have hc : ELEM.cq m = p := by unfold ELEM.cq; omega
  exact hsplit (hc ▸ inert _ hfac hsmall (by simpa [pow_two] using hsq))

/-- By Minkowski, the only possible obstruction is a small prime ideal of prime
norm. Its residue field would contain a root of the row polynomial. -/
lemma class_number_one {K : Type*} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    {p m : ℕ} (hp : 2 ≤ p) (hm : m + 1 = 4 * p) (hsq : Squarefree m)
    {α : K} (hα : α ^ 2 = -(m : K))
    (inert : ∀ q : ℕ, q.Prime → q < p → q ^ 2 ≤ m → ELEM.IsInert p q) : classNumber K = 1 := by
  have hm4 : m % 4 = 3 := by omega
  have hdisc : |discr K| ≤ (m : ℤ) := by
    simp [discr_eq hα hK hsq, disc, hm4]
  let θ := omegaInt hα
  have hθ : θ ^ 2 = ((1 : ℤ) : 𝓞 K) * θ - ((p : ℤ) : 𝓞 K) := by
    have h := omegaInt_sq hα
    have hc : (m + 1) / 4 = p := by omega
    simpa [θ, hm4, hc, sub_eq_neg_add] using h
  rw [NumberField.classNumber_eq_one_iff]
  refine RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime
    fun I hI hle ↦ ?_
  have hI0 : (I : Ideal (𝓞 K)) ≠ ⊥ := nonZeroDivisors.coe_ne_zero I
  have : (I : Ideal (𝓞 K)).IsMaximal := hI.isMaximal hI0
  have hbound := le_two_thirds_sqrt_of_le_minkowski hK hdisc hle
  obtain ⟨q, hq, -, hcases⟩ := absNorm_maximal_cases hK (I : Ideal (𝓞 K))
  rcases hcases with hN | ⟨-, hspan⟩
  · exfalso
    rw [hN] at hbound
    have hqp : q < p := nat_lt_of_le_two_thirds_sqrt hbound (by nlinarith [Nat.mul_le_mul_left p hp])
    have hqSq : q ^ 2 ≤ m := by
      have hle : (q : ℝ) ≤ Real.sqrt m := by linarith [Real.sqrt_nonneg (m : ℝ)]
      have h := sq_le_sq' (by linarith [Real.sqrt_nonneg (m : ℝ)]) hle
      rw [Real.sq_sqrt (Nat.cast_nonneg m)] at h
      exact_mod_cast h
    apply not_absNorm_eq_of_no_root θ _ _ hθ _ _ hq hN
    intro z hz
    apply inert q hq hqp hqSq z
    push_cast at hz
    linear_combination hz
  · rw [hspan]
    exact ⟨⟨_, rfl⟩⟩

/-- The forward Rabinowitsch implication with a square-root length prime test. -/
theorem criterion {p : ℕ} (hp : 2 ≤ p)
    (row : ∀ t : ℕ, (2 * t + 1) ^ 2 ≤ 4 * p - 1 → (t * (t + 1) + p).Prime) :
    let d : ℤ := 1 - 4 * (p : ℤ)
    Squarefree d ∧ ∃ h : Irreducible (X ^ 2 - C (d : ℚ)),
      letI : Fact (Irreducible (X ^ 2 - C (d : ℚ))) := ⟨h⟩
      classNumber (AdjoinRoot (X ^ 2 - C (d : ℚ))) = 1 := by
  let m := 4 * p - 1
  have hm : m + 1 = 4 * p := by dsimp [m]; omega
  have hinert := fun q (hq : q.Prime) (hqp : q < p) (hs : q ^ 2 ≤ m) => inert_of_short_row row hq hqp hs
  have hsq := (prime_discriminant hp hm hinert).squarefree
  let d : ℤ := -(m : ℤ)
  have hd : d < 0 := by dsimp [d]; omega
  let f : ℚ[X] := X ^ 2 - C (d : ℚ)
  let : Fact (Irreducible f) := ⟨OMABridge_irred d hd⟩
  let K := AdjoinRoot f
  have hK : Module.finrank ℚ K = 2 := by
    rw [(AdjoinRoot.powerBasis' (OMABridge_monic d)).finrank]
    exact OMABridge_deg d
  have hα : (AdjoinRoot.root f) ^ 2 = -(m : K) := by
    have h := AdjoinRoot.eval₂_root f
    change eval₂ (AdjoinRoot.of f) (AdjoinRoot.root f) (X ^ 2 - C (d : ℚ)) = 0 at h
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] at h
    rw [h, map_intCast]
    simp [d, K]
  have hclass := class_number_one hK hp hm hsq hα hinert
  dsimp only
  have hdEq : 1 - 4 * (p : ℤ) = d := by dsimp [d]; omega
  rw [hdEq]
  exact ⟨Int.squarefree_natAbs.mp (by simpa [d] using hsq), OMABridge_irred d hd, hclass⟩

end OMA.PrimeRow

theorem OMA.solution : OMA.R_OeisA117531_conjecture_R1.H1 := by
  intro p hp _ row
  apply OMA.PrimeRow.criterion hp.two_le
  intro t ht
  apply row
  have bound : (2 * t + 1) ^ 2 ≤ 4 * p := ht.trans (Nat.sub_le _ _)
  nlinarith [Nat.le_mul_self t]
