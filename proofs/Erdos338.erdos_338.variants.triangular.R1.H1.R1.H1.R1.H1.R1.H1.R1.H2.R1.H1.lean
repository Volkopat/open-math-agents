import OMAReductions.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1

/-! Ideals of each norm in `ℚ(√-s)`, `s ≡ 3 (mod 8)` squarefree, counted by `∑_{d ∣ n} (d | s)`.
Each rational prime `p` splits (two primes of norm `p`, `(p | s) = 1`), is inert (one prime of
norm `p²`, `(p | s) = -1`) or ramifies (one prime of norm `p`, `p ∣ s`), read off from the
Kummer–Dedekind factorisation of the minimal polynomial of `(1 + √-s)/2` modulo `p`. The ideal
count and the divisor sum then obey the same recurrence in each prime power, and agree by strong
induction on `n`. -/

/- The `CN1.Foundations` block (integral basis, Kronecker character, Kummer–Dedekind splitting) is
taken from OeisA38552.starkHeegner_classNumberOne in this repository, adapted from
github.com/DrMurphyIsIn/tenth-discriminant (commit 9078b2bbf205e494b659035465b73e3451738463), vendored
CN1.* modules, (c) the tenth-discriminant authors (DrMurphyIsIn and contributors), Apache-2.0.
The ramified case, the prime shapes and the counting are new. -/

section
namespace CN1.Foundations
open NumberField Module Polynomial
def disc (m : ℕ) : ℕ := if m % 4 = 3 then m else 4 * m
variable {K : Type*} [Field K] [NumberField K]
noncomputable def omega (m : ℕ) (α : K) : K := if m % 4 = 3 then (1 + α) / 2 else α
lemma disc_of_three_mod_four {m : ℕ} (h : m % 4 = 3) : disc m = m := by simp [disc, h]
lemma disc_of_not_three_mod_four {m : ℕ} (h : m % 4 ≠ 3) : disc m = 4 * m := by simp [disc, h]
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
end RingOfIntegers
section NormForm
variable {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K)) (hK : finrank ℚ K = 2) (hm0 : m ≠ 0)
end NormForm
section Units
variable {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K)) (hK : finrank ℚ K = 2) (hm : Squarefree m)
end Units
end CN1.Foundations
end

section
namespace CN1.Foundations
open ZMod
open DirichletCharacter (changeLevel changeLevel_eq_cast_of_dvd changeLevel_eq_cast_of_dvd')
section JacobiChar
lemma jacobiSym_val_eq (n : ℕ) [NeZero n] (a : ZMod n) (k : ℤ) (hk : (k : ZMod n) = a) :
    jacobiSym a.val n = jacobiSym k n := by
  apply jacobiSym.mod_left'
  rw [← ZMod.intCast_eq_intCast_iff']
  simp [hk]
noncomputable def jacobiChar (n : ℕ) [NeZero n] : DirichletCharacter ℂ n where
  toFun a := (jacobiSym a.val n : ℂ)
  map_one' := by
    show (jacobiSym (1 : ZMod n).val n : ℂ) = 1
    rw [jacobiSym_val_eq n 1 1 (by simp), jacobiSym.one_left]; simp
  map_mul' a b := by
    show (jacobiSym (a * b).val n : ℂ) = (jacobiSym a.val n : ℂ) * (jacobiSym b.val n : ℂ)
    rw [jacobiSym_val_eq n (a * b) (a.val * b.val) (by simp), jacobiSym.mul_left]
    push_cast; rfl
  map_nonunit' a ha := by
    show (jacobiSym a.val n : ℂ) = 0
    have hc : ¬ Nat.Coprime a.val n := by
      rwa [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
    have : jacobiSym a.val n = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime, Int.gcd_natCast_natCast]
      exact hc
    rw [this]; simp
lemma jacobiChar_apply (n : ℕ) [NeZero n] (a : ZMod n) :
    jacobiChar n a = (jacobiSym a.val n : ℂ) := rfl
theorem jacobiChar_intCast (n : ℕ) [NeZero n] (k : ℤ) :
    jacobiChar n (k : ZMod n) = (jacobiSym k n : ℂ) := by
  rw [jacobiChar_apply, jacobiSym_val_eq n _ k rfl]
theorem jacobiChar_isQuadratic (n : ℕ) [NeZero n] : (jacobiChar n).IsQuadratic := by
  intro a
  rw [jacobiChar_apply]
  rcases jacobiSym.trichotomy a.val n with h | h | h <;> rw [h] <;> norm_num
end JacobiChar
noncomputable def chi4 : DirichletCharacter ℂ 4 := χ₄.ringHomComp (Int.castRingHom ℂ)
noncomputable def chi8 : DirichletCharacter ℂ 8 := χ₈.ringHomComp (Int.castRingHom ℂ)
noncomputable def chi8' : DirichletCharacter ℂ 8 := χ₈'.ringHomComp (Int.castRingHom ℂ)
lemma chi4_apply (a : ZMod 4) : chi4 a = (χ₄ a : ℂ) := rfl
lemma chi4_isQuadratic : chi4.IsQuadratic := isQuadratic_χ₄.comp _
lemma chi8_isQuadratic : chi8.IsQuadratic := isQuadratic_χ₈.comp _
lemma chi8'_isQuadratic : chi8'.IsQuadratic := isQuadratic_χ₈'.comp _
section Quadratic
variable {R : Type*} [CommRing R]
lemma isQuadratic_changeLevel {n N : ℕ} (h : n ∣ N) {ψ : DirichletCharacter R n}
    (hψ : ψ.IsQuadratic) : (changeLevel h ψ).IsQuadratic := by
  intro a
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [changeLevel_eq_cast_of_dvd]
    exact hψ _
  · left; exact MulChar.map_nonunit _ ha
lemma isQuadratic_mul {M : Type*} [CommMonoid M] {χ ψ : MulChar M R}
    (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) : (χ * ψ).IsQuadratic := by
  intro a
  rw [MulChar.mul_apply]
  rcases hχ a with h | h | h <;> rcases hψ a with h' | h' | h' <;> simp [h, h']
lemma isQuadratic_one {M : Type*} [CommMonoid M] [Nontrivial R] :
    (1 : MulChar M R).IsQuadratic := by
  intro a
  by_cases ha : IsUnit a
  · right; left; exact MulChar.one_apply ha
  · left; exact MulChar.map_nonunit _ ha
end Quadratic
section Kronecker
variable {m : ℕ}
lemma four_dvd_disc (h3 : m % 4 ≠ 3) : 4 ∣ disc m := by
  rw [disc_of_not_three_mod_four h3]; exact dvd_mul_right 4 m
lemma dvd_disc (h3 : m % 4 ≠ 3) : m ∣ disc m := by
  rw [disc_of_not_three_mod_four h3]; exact dvd_mul_left m 4
lemma eight_dvd_disc (h3 : m % 4 ≠ 3) (h2 : m % 2 = 0) : 8 ∣ disc m := by
  rw [disc_of_not_three_mod_four h3]; exact ⟨m / 2, by omega⟩
lemma half_dvd_disc (h3 : m % 4 ≠ 3) (h2 : m % 2 = 0) : m / 2 ∣ disc m := by
  rw [disc_of_not_three_mod_four h3]; exact ⟨8, by omega⟩
noncomputable def kroneckerChar (m : ℕ) : DirichletCharacter ℂ (disc m) :=
  if h0 : m = 0 then 1
  else if h3 : m % 4 = 3 then
    changeLevel (dvd_of_eq (disc_of_three_mod_four h3).symm) (@jacobiChar m ⟨h0⟩)
  else if h2 : m % 2 = 1 then
    changeLevel (four_dvd_disc h3) chi4 * changeLevel (dvd_disc h3) (@jacobiChar m ⟨h0⟩)
  else
    changeLevel (eight_dvd_disc h3 (by omega)) (if m / 2 % 4 = 1 then chi8' else chi8) *
      changeLevel (half_dvd_disc h3 (by omega)) (@jacobiChar (m / 2) ⟨by omega⟩)
theorem kroneckerChar_apply_of_three_mod_four (h3 : m % 4 = 3) {a : ℤ}
    (ha : IsCoprime a (disc m)) : kroneckerChar m (a : ZMod (disc m)) = (jacobiSym a m : ℂ) := by
  have h0 : m ≠ 0 := by omega
  simp only [kroneckerChar, h0, h3, ↓reduceDIte]
  rw [changeLevel_eq_cast_of_dvd' _ _ ha, jacobiChar_intCast]
theorem kroneckerChar_apply_of_one_mod_four (h1 : m % 4 = 1) {a : ℤ}
    (ha : IsCoprime a (disc m)) :
    kroneckerChar m (a : ZMod (disc m)) = (χ₄ a : ℂ) * (jacobiSym a m : ℂ) := by
  have h0 : m ≠ 0 := by omega
  have h3 : m % 4 ≠ 3 := by omega
  have h2 : m % 2 = 1 := by omega
  simp only [kroneckerChar, h0, h3, h2, ↓reduceDIte]
  rw [MulChar.mul_apply, changeLevel_eq_cast_of_dvd' _ _ ha, changeLevel_eq_cast_of_dvd' _ _ ha,
    jacobiChar_intCast, chi4_apply]
theorem kroneckerChar_apply_of_two_mod_four (h2 : m % 4 = 2) {a : ℤ}
    (ha : IsCoprime a (disc m)) :
    kroneckerChar m (a : ZMod (disc m)) =
      (if m / 2 % 4 = 1 then (χ₈' a : ℂ) else (χ₈ a : ℂ)) * (jacobiSym a (m / 2) : ℂ) := by
  have h0 : m ≠ 0 := by omega
  have h3 : m % 4 ≠ 3 := by omega
  have h2' : ¬ m % 2 = 1 := by omega
  simp only [kroneckerChar, h0, h3, h2', ↓reduceDIte]
  rw [MulChar.mul_apply, changeLevel_eq_cast_of_dvd' _ _ ha, changeLevel_eq_cast_of_dvd' _ _ ha,
    jacobiChar_intCast]
  split_ifs <;> rfl
theorem kroneckerChar_isQuadratic (m : ℕ) : (kroneckerChar m).IsQuadratic := by
  by_cases h0 : m = 0
  · simp only [kroneckerChar, h0, ↓reduceDIte]
    exact isQuadratic_one
  have : NeZero m := ⟨h0⟩
  by_cases h3 : m % 4 = 3
  · simp only [kroneckerChar, h0, h3, ↓reduceDIte]
    exact isQuadratic_changeLevel _ (jacobiChar_isQuadratic m)
  by_cases h2 : m % 2 = 1
  · simp only [kroneckerChar, h0, h3, h2, ↓reduceDIte]
    exact isQuadratic_mul (isQuadratic_changeLevel _ chi4_isQuadratic)
      (isQuadratic_changeLevel _ (jacobiChar_isQuadratic m))
  · have : NeZero (m / 2) := ⟨by omega⟩
    simp only [kroneckerChar, h0, h3, h2, ↓reduceDIte]
    refine isQuadratic_mul (isQuadratic_changeLevel _ ?_)
      (isQuadratic_changeLevel _ (jacobiChar_isQuadratic (m / 2)))
    split_ifs
    · exact chi8'_isQuadratic
    · exact chi8_isQuadratic
lemma squarefree_mod_four_cases (hm : Squarefree m) : m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by
  have := squarefree_mod_four_ne_zero hm; omega
section Values
variable {p : ℕ} [hp : Fact p.Prime]
lemma jacobiSym_eq_legendreSym_neg_of_three_mod_four (h3 : m % 4 = 3) (hp2 : p ≠ 2) :
    jacobiSym p m = legendreSym p (-(m : ℤ)) := by
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  rw [legendreSym.at_neg hp2, jacobiSym.legendreSym.to_jacobiSym]
  rcases Nat.odd_mod_four_iff.mp hpodd with h1 | h1
  · rw [jacobiSym.quadratic_reciprocity_one_mod_four h1 (Nat.odd_iff.mpr (by omega)),
      χ₄_nat_one_mod_four h1, one_mul]
  · rw [jacobiSym.quadratic_reciprocity_three_mod_four h1 h3, χ₄_nat_three_mod_four h1,
      neg_one_mul]
lemma chi4_mul_jacobiSym_eq_legendreSym_neg_of_one_mod_four (h1 : m % 4 = 1) (hp2 : p ≠ 2) :
    χ₄ p * jacobiSym p m = legendreSym p (-(m : ℤ)) := by
  have hpodd : _root_.Odd p := hp.out.odd_of_ne_two hp2
  rw [legendreSym.at_neg hp2, jacobiSym.legendreSym.to_jacobiSym,
    jacobiSym.quadratic_reciprocity_one_mod_four' hpodd h1]
lemma chi8_mul_jacobiSym_eq_legendreSym_neg_of_two_mod_four (h2 : m % 4 = 2) (hp2 : p ≠ 2) :
    (if m / 2 % 4 = 1 then χ₈' p else χ₈ p) * jacobiSym p (m / 2) = legendreSym p (-(m : ℤ)) := by
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  have hm : (m : ℤ) = 2 * ((m / 2 : ℕ) : ℤ) := by push_cast; omega
  have hm'odd : _root_.Odd (m / 2) := Nat.odd_iff.mpr (by omega)
  rw [hm, neg_mul_eq_neg_mul, legendreSym.mul, legendreSym.at_neg_two hp2,
    jacobiSym.legendreSym.to_jacobiSym]
  have hm' : m / 2 % 4 = 1 ∨ m / 2 % 4 = 3 := by omega
  rcases hm' with h | h
  · rw [if_pos h, jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr hpodd) h]
  · rw [if_neg (by omega)]
    have h8 : χ₈' (p : ZMod 8) = χ₄ (p : ZMod 4) * χ₈ (p : ZMod 8) := by
      have := χ₈'_int_eq_χ₄_mul_χ₈ (p : ℤ)
      simpa using this
    rw [h8]
    rcases Nat.odd_mod_four_iff.mp hpodd with h1 | h1
    · rw [jacobiSym.quadratic_reciprocity_one_mod_four h1 hm'odd, χ₄_nat_one_mod_four h1, one_mul]
    · rw [jacobiSym.quadratic_reciprocity_three_mod_four h1 h, χ₄_nat_three_mod_four h1]
      ring
theorem kroneckerChar_apply_prime_of_ne_two (hm : Squarefree m) (hp2 : p ≠ 2)
    (hpd : ¬ p ∣ disc m) :
    kroneckerChar m (p : ZMod (disc m)) = (legendreSym p (-(m : ℤ)) : ℂ) := by
  have hcop : IsCoprime (p : ℤ) (disc m : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpd)
  rw [← Int.cast_natCast (R := ZMod (disc m))]
  rcases squarefree_mod_four_cases hm with h1 | h2 | h3
  · rw [kroneckerChar_apply_of_one_mod_four h1 hcop,
      ← chi4_mul_jacobiSym_eq_legendreSym_neg_of_one_mod_four h1 hp2]
    push_cast
    try rfl
  · rw [kroneckerChar_apply_of_two_mod_four h2 hcop,
      ← chi8_mul_jacobiSym_eq_legendreSym_neg_of_two_mod_four h2 hp2]
    split_ifs <;> push_cast <;> try rfl
  · rw [kroneckerChar_apply_of_three_mod_four h3 hcop,
      ← jacobiSym_eq_legendreSym_neg_of_three_mod_four h3 hp2]
theorem kroneckerChar_apply_two (h3 : m % 4 = 3) :
    kroneckerChar m (2 : ZMod (disc m)) = (χ₈ (m : ZMod 8) : ℂ) := by
  have hodd : _root_.Odd m := Nat.odd_iff.mpr (by omega)
  have hcop : IsCoprime (2 : ℤ) (disc m : ℤ) := by
    rw [disc_of_three_mod_four h3]
    have : IsCoprime ((2 : ℕ) : ℤ) (m : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr (Nat.coprime_two_left.mpr hodd)
    exact_mod_cast this
  have hcast : (2 : ZMod (disc m)) = ((2 : ℤ) : ZMod (disc m)) := by simp
  rw [hcast, kroneckerChar_apply_of_three_mod_four h3 hcop, jacobiSym.at_two hodd]
lemma neg_natCast_ne_zero_of_not_dvd_disc (hpd : ¬ p ∣ disc m) : (-(m : ZMod p)) ≠ 0 := by
  rw [neg_ne_zero, Ne, ZMod.natCast_eq_zero_iff]
  intro h
  refine hpd (h.trans ?_)
  unfold disc; split_ifs
  · exact dvd_rfl
  · exact dvd_mul_left m 4
theorem kroneckerChar_apply_prime_eq_one_iff (hm : Squarefree m) (hp2 : p ≠ 2)
    (hpd : ¬ p ∣ disc m) :
    kroneckerChar m (p : ZMod (disc m)) = 1 ↔ IsSquare (-(m : ZMod p)) := by
  rw [kroneckerChar_apply_prime_of_ne_two hm hp2 hpd]
  have hne : ((-(m : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    push_cast; exact neg_natCast_ne_zero_of_not_dvd_disc hpd
  have := legendreSym.eq_one_iff p hne
  push_cast at this
  rw [← this]
  norm_cast
end Values
end Kronecker
end CN1.Foundations
end

section
namespace CN1.Foundations
open NumberField Polynomial Ideal
def bInt (m : ℕ) : ℤ := if m % 4 = 3 then -1 else 0
def cInt (m : ℕ) : ℤ := if m % 4 = 3 then ((m + 1) / 4 : ℕ) else m
theorem bInt_sq_sub_four_mul_cInt (m : ℕ) : bInt m ^ 2 - 4 * cInt m = -(disc m : ℤ) := by
  unfold bInt cInt disc
  split_ifs with h3
  · obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
    have hc' : ((m + 1) / 4 : ℕ) = c := by omega
    rw [hc']
    have : (m : ℤ) + 1 = 4 * c := by exact_mod_cast hc
    linear_combination this
  · push_cast; ring
section Setup
variable {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
  (hK : Module.finrank ℚ K = 2) (hm : Squarefree m)
include hα hK hm in
theorem adjoin_omegaInt_eq_top : Algebra.adjoin ℤ {omegaInt hα} = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  obtain ⟨u, v, rfl⟩ := exists_int_add_int_mul_omegaInt hα hK hm z
  exact Subalgebra.add_mem _ (Subalgebra.intCast_mem _ u)
    (Subalgebra.mul_mem _ (Subalgebra.intCast_mem _ v) (Algebra.self_mem_adjoin_singleton ℤ _))
include hα hK hm in
theorem exponent_omegaInt_eq_one : RingOfIntegers.exponent (omegaInt hα) = 1 :=
  RingOfIntegers.exponent_eq_one_iff.mpr (adjoin_omegaInt_eq_top hα hK hm)
include hα hK hm in
theorem not_dvd_exponent_omegaInt (p : ℕ) [hp : Fact p.Prime] :
    ¬ p ∣ RingOfIntegers.exponent (omegaInt hα) := by
  rw [exponent_omegaInt_eq_one hα hK hm]; exact hp.out.not_dvd_one
include hα in
theorem minpoly_rat_omega (hm0 : m ≠ 0) :
    minpoly ℚ (omega m α) = X ^ 2 + C (bInt m : ℚ) * X + C (cInt m : ℚ) := by
  have hmpos : (0 : ℚ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  symm
  apply minpoly.eq_of_irreducible_of_monic
  · apply irreducible_of_degree_le_three_of_not_isRoot
    · have hdeg : (X ^ 2 + C (bInt m : ℚ) * X + C (cInt m : ℚ)).natDegree = 2 := by
        compute_degree!
      rw [hdeg]; decide
    · intro x hx
      rw [IsRoot.def, eval_add, eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_C] at hx
      unfold bInt cInt at hx
      split_ifs at hx with h3
      · obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
        have hc' : ((m + 1) / 4 : ℕ) = c := by omega
        rw [hc'] at hx
        push_cast at hx
        have hcq : (m : ℚ) + 1 = 4 * c := by exact_mod_cast hc
        nlinarith [sq_nonneg (2 * x - 1)]
      · push_cast at hx
        nlinarith [sq_nonneg x]
  · rw [map_add, map_add, map_mul, map_pow, aeval_X, aeval_C, aeval_C, eq_ratCast, eq_ratCast]
    unfold omega bInt cInt
    split_ifs with h3
    · obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
      have hc' : ((m + 1) / 4 : ℕ) = c := by omega
      rw [hc']
      push_cast
      have hcK : (m : K) + 1 = 4 * c := by exact_mod_cast hc
      linear_combination (1 / 4 : K) * hα + (-1 / 4 : K) * hcK
    · push_cast
      linear_combination hα
  · monicity!
include hα in
theorem minpoly_int_omegaInt (hm0 : m ≠ 0) :
    minpoly ℤ (omegaInt hα) = X ^ 2 + C (bInt m) * X + C (cInt m) := by
  rw [← RingOfIntegers.minpoly_coe, coe_omegaInt]
  apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
  rw [← algebraMap_int_eq, ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ (omega_isIntegral hα),
    minpoly_rat_omega hα hm0]
  simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]
section Prime
variable (p : ℕ) [hp : Fact p.Prime]
include hα in
theorem minpoly_omegaInt_map (hm0 : m ≠ 0) :
    (minpoly ℤ (omegaInt hα)).map (Int.castRingHom (ZMod p)) =
      X ^ 2 + C (bInt m : ZMod p) * X + C (cInt m : ZMod p) := by
  rw [minpoly_int_omegaInt hα hm0]
  simp [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]
lemma quad_eq_mul_of_root (b c r : ZMod p) (hr : r ^ 2 + b * r + c = 0) :
    X ^ 2 + C b * X + C c = (X - C r) * (X - C (-b - r)) := by
  have hc : c = -(r ^ 2) - b * r := by linear_combination hr
  rw [hc]
  simp only [map_sub, map_neg, map_mul, map_pow]
  ring
lemma natDegree_quad (b c : ZMod p) : (X ^ 2 + C b * X + C c).natDegree = 2 := by
  compute_degree!
lemma monic_quad (b c : ZMod p) : (X ^ 2 + C b * X + C c).Monic := by
  monicity!
lemma irreducible_quad_of_no_root (b c : ZMod p) (h : ∀ x : ZMod p, x ^ 2 + b * x + c ≠ 0) :
    Irreducible (X ^ 2 + C b * X + C c) := by
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_quad]; decide
  · intro x hx
    apply h x
    rw [IsRoot.def, eval_add, eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_C] at hx
    exact hx
include hα hK hm in
theorem monicFactorsMod_of_root {r : ZMod p} (hr : r ^ 2 + (bInt m : ZMod p) * r + cInt m = 0) :
    RingOfIntegers.monicFactorsMod (omegaInt hα) p =
      {X - C r, X - C (-(bInt m : ZMod p) - r)} := by
  unfold RingOfIntegers.monicFactorsMod
  rw [minpoly_omegaInt_map hα p hm.ne_zero, quad_eq_mul_of_root p _ _ r hr,
    UniqueFactorizationMonoid.normalizedFactors_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _),
    UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_X_sub_C _),
    UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_X_sub_C _),
    (monic_X_sub_C _).normalize_eq_self, (monic_X_sub_C _).normalize_eq_self,
    Multiset.singleton_add, Multiset.toFinset_cons, Multiset.toFinset_singleton]
include hα hK hm in
theorem monicFactorsMod_of_no_root
    (h : ∀ x : ZMod p, x ^ 2 + (bInt m : ZMod p) * x + cInt m ≠ 0) :
    RingOfIntegers.monicFactorsMod (omegaInt hα) p =
      {X ^ 2 + C (bInt m : ZMod p) * X + C (cInt m : ZMod p)} := by
  unfold RingOfIntegers.monicFactorsMod
  rw [minpoly_omegaInt_map hα p hm.ne_zero,
    UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_quad_of_no_root p _ _ h),
    (monic_quad p _ _).normalize_eq_self, Multiset.toFinset_singleton]
include hα hK hm in
theorem ncard_primesOver_eq_card_monicFactorsMod :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard =
      (RingOfIntegers.monicFactorsMod (omegaInt hα) p).card := by
  rw [← Nat.card_coe_set_eq,
    Nat.card_congr (Ideal.primesOverSpanEquivMonicFactorsMod (not_dvd_exponent_omegaInt hα hK hm p)),
    Nat.card_eq_finsetCard]
include hα hK hm in
theorem inertiaDeg_eq_natDegree {P : Ideal (𝓞 K)} (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K)) :
    P.inertiaDeg ℤ =
      ((Ideal.primesOverSpanEquivMonicFactorsMod (not_dvd_exponent_omegaInt hα hK hm p) ⟨P, hP⟩ :
        (ZMod p)[X])).natDegree := by
  set e := Ideal.primesOverSpanEquivMonicFactorsMod (not_dvd_exponent_omegaInt hα hK hm p)
  have := Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
    (not_dvd_exponent_omegaInt hα hK hm p) (e ⟨P, hP⟩).2
  rwa [Subtype.coe_eta, e.symm_apply_apply] at this
lemma root_ne_other_root (hpd : ¬ p ∣ disc m) {r : ZMod p}
    (hr : r ^ 2 + (bInt m : ZMod p) * r + cInt m = 0) : r ≠ -(bInt m : ZMod p) - r := by
  intro heq
  apply hpd
  rw [← ZMod.natCast_eq_zero_iff]
  have hdisc : (bInt m : ZMod p) ^ 2 - 4 * (cInt m : ZMod p) = -(disc m : ZMod p) := by
    exact_mod_cast congrArg (Int.cast (R := ZMod p)) (bInt_sq_sub_four_mul_cInt m)
  linear_combination hdisc + (-(2 * r + (bInt m : ZMod p))) * heq + 4 * hr
lemma two_ne_zero_of_ne_two (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
theorem exists_root_iff_isSquare (hp2 : p ≠ 2) :
    (∃ x : ZMod p, x ^ 2 + (bInt m : ZMod p) * x + cInt m = 0) ↔ IsSquare (-(m : ZMod p)) := by
  have h2 := two_ne_zero_of_ne_two p hp2
  unfold bInt cInt
  split_ifs with h3
  · obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
    have hc' : ((m + 1) / 4 : ℕ) = c := by omega
    rw [hc']
    push_cast
    have hc4 : (m : ZMod p) + 1 = 4 * c := by
      have := congrArg (Nat.cast (R := ZMod p)) hc
      push_cast at this
      exact this
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨2 * x - 1, by linear_combination (-4 : ZMod p) * hx + (-1 : ZMod p) * hc4⟩
    · rintro ⟨y, hy⟩
      refine ⟨(y + 1) * 2⁻¹, ?_⟩
      have hi : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
      have h4 : (4 : ZMod p) ≠ 0 := by
        have : (4 : ZMod p) = 2 * 2 := by norm_num
        rw [this]; exact mul_ne_zero h2 h2
      have key : (4 : ZMod p) * (((y + 1) * 2⁻¹) ^ 2 + -1 * ((y + 1) * 2⁻¹) + c) = 0 := by
        linear_combination ((y + 1) ^ 2 * (2 * 2⁻¹ + 1)) * hi + (-2 * (y + 1)) * hi
          + (-1 : ZMod p) * hy + (-1 : ZMod p) * hc4
      exact (mul_eq_zero.mp key).resolve_left h4
  · push_cast
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, by linear_combination -hx⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, by linear_combination -hy⟩
theorem exists_root_two_iff (h3 : m % 4 = 3) :
    (∃ x : ZMod 2, x ^ 2 + (bInt m : ZMod 2) * x + cInt m = 0) ↔ m % 8 = 7 := by
  unfold bInt cInt
  rw [if_pos h3, if_pos h3]
  obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
  have hc' : ((m + 1) / 4 : ℕ) = c := by omega
  rw [hc']
  have key : ∀ c' : ZMod 2, (∃ x : ZMod 2, x ^ 2 + ((-1 : ℤ) : ZMod 2) * x + ((c' : ZMod 2)) = 0) ↔
      c' = 0 := by decide
  rw [show ((c : ℤ) : ZMod 2) = ((c : ℕ) : ZMod 2) from Int.cast_natCast c, key,
    ZMod.natCast_eq_zero_iff_even, Nat.even_iff]
  omega
include hm in
theorem kroneckerChar_eq_one_iff_exists_root (hpd : ¬ p ∣ disc m) :
    kroneckerChar m (p : ZMod (disc m)) = 1 ↔
      ∃ x : ZMod p, x ^ 2 + (bInt m : ZMod p) * x + cInt m = 0 := by
  by_cases hp2 : p = 2
  · subst hp2
    have h3 : m % 4 = 3 := by
      by_contra h3
      exact hpd (by rw [disc_of_not_three_mod_four h3]; exact ⟨2 * m, by ring⟩)
    rw [exists_root_two_iff h3, show ((2 : ℕ) : ZMod (disc m)) = 2 from Nat.cast_ofNat,
      kroneckerChar_apply_two h3, ZMod.χ₈_nat_eq_if_mod_eight]
    have h8 : m % 8 = 3 ∨ m % 8 = 7 := by omega
    rcases h8 with h | h
    · rw [if_neg (by omega), if_neg (by omega)]
      norm_num
      omega
    · rw [if_neg (by omega), if_pos (by omega)]
      norm_num
      exact h
  · rw [kroneckerChar_apply_prime_eq_one_iff hm hp2 hpd, exists_root_iff_isSquare p hp2]
theorem kroneckerChar_eq_one_or_neg_one (hpd : ¬ p ∣ disc m) :
    kroneckerChar m (p : ZMod (disc m)) = 1 ∨ kroneckerChar m (p : ZMod (disc m)) = -1 := by
  have hcop : IsCoprime (p : ℤ) (disc m : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpd)
  have hne : kroneckerChar m (p : ZMod (disc m)) ≠ 0 := by
    rw [← Int.cast_natCast (R := ZMod (disc m))]
    exact (DirichletCharacter.apply_ne_zero_iff _ _).mpr hcop
  rcases kroneckerChar_isQuadratic m (p : ZMod (disc m)) with h | h | h
  · exact absurd h hne
  · exact Or.inl h
  · exact Or.inr h
include hα hK hm in
theorem ncard_primesOver_eq_two_of_kroneckerChar_eq_one (hpd : ¬ p ∣ disc m)
    (h1 : kroneckerChar m (p : ZMod (disc m)) = 1) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 2 ∧
      ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 1 := by
  obtain ⟨r, hr⟩ := (kroneckerChar_eq_one_iff_exists_root hm p hpd).mp h1
  have hF := monicFactorsMod_of_root hα hK hm p hr
  have hne : X - C r ≠ X - C (-(bInt m : ZMod p) - r) := by
    intro h
    exact root_ne_other_root p hpd hr (C_inj.mp (sub_right_injective h))
  constructor
  · rw [ncard_primesOver_eq_card_monicFactorsMod hα hK hm p, hF]
    exact Finset.card_pair_eq_two_iff.mpr hne
  · intro P hP
    rw [inertiaDeg_eq_natDegree hα hK hm p hP]
    have hmem := (Finset.ext_iff.mp hF _).mp
      (Ideal.primesOverSpanEquivMonicFactorsMod (not_dvd_exponent_omegaInt hα hK hm p) ⟨P, hP⟩).2
    rw [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h <;> rw [h, natDegree_X_sub_C]
include hα hK hm in
theorem ncard_primesOver_eq_one_of_kroneckerChar_eq_neg_one (hpd : ¬ p ∣ disc m)
    (h1 : kroneckerChar m (p : ZMod (disc m)) = -1) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 1 ∧
      ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 2 := by
  have hno : ∀ x : ZMod p, x ^ 2 + (bInt m : ZMod p) * x + cInt m ≠ 0 := by
    intro x hx
    have := (kroneckerChar_eq_one_iff_exists_root hm p hpd).mpr ⟨x, hx⟩
    rw [h1] at this
    norm_num at this
  have hF := monicFactorsMod_of_no_root hα hK hm p hno
  constructor
  · rw [ncard_primesOver_eq_card_monicFactorsMod hα hK hm p, hF, Finset.card_singleton]
  · intro P hP
    rw [inertiaDeg_eq_natDegree hα hK hm p hP]
    have hmem := (Finset.ext_iff.mp hF _).mp
      (Ideal.primesOverSpanEquivMonicFactorsMod (not_dvd_exponent_omegaInt hα hK hm p) ⟨P, hP⟩).2
    rw [Finset.mem_singleton] at hmem
    rw [hmem, natDegree_quad]
end Prime
end Setup
end CN1.Foundations
end

/-! Counting ideals by norm from the shape of the primes above each rational prime: a split prime
gives `a(n) = 2 a(n/p) - a(n/p²)`, an inert one `a(n) = a(n/p²)`, a ramified one `a(n) = a(n/p)`,
and `∑_{d ∣ n} χ d` obeys the same recurrences. -/

namespace H1Work
open NumberField Ideal

variable (K : Type*) [Field K] [NumberField K]

noncomputable def cnt (n : ℕ) : ℕ := {I : Ideal (𝓞 K) | absNorm I = n}.ncard

/-- Two distinct primes of norm `p` above `p`. -/
def Split (p : ℕ) : Prop := ∃ P Q : Ideal (𝓞 K), P ≠ ⊥ ∧ Q ≠ ⊥ ∧ absNorm P = p ∧ absNorm Q = p ∧
  (∀ I : Ideal (𝓞 K), P ∣ I → Q ∣ I → P * Q ∣ I) ∧
  (∀ I : Ideal (𝓞 K), I ≠ ⊥ → p ∣ absNorm I → P ∣ I ∨ Q ∣ I)

/-- A single prime above `p`, of norm `q`. -/
def One (p q : ℕ) : Prop := ∃ P : Ideal (𝓞 K), P ≠ ⊥ ∧ absNorm P = q ∧
  ∀ I : Ideal (𝓞 K), I ≠ ⊥ → p ∣ absNorm I → P ∣ I

variable {K}

theorem fin (n : ℕ) : {I : Ideal (𝓞 K) | absNorm I = n}.Finite := finite_setOfPred_absNorm_eq n

theorem cnt_eq (n : ℕ) : Nat.card {I : Ideal (𝓞 K) // absNorm I = n} = cnt K n := by
  rw [cnt, ← Nat.card_coe_set_eq]; rfl

theorem cnt_one : cnt K 1 = 1 := by
  have : {I : Ideal (𝓞 K) | absNorm I = 1} = {⊤} := by
    ext I; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, absNorm_eq_one_iff]
  rw [cnt, this, Set.ncard_singleton]

theorem ne_bot_of_norm {I : Ideal (𝓞 K)} {n : ℕ} (hn : 0 < n) (h : absNorm I = n) : I ≠ ⊥ := by
  intro hI; rw [hI, absNorm_bot] at h; omega

theorem cnt_dvd (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) (n : ℕ) (hd : absNorm J ∣ n) :
    {I : Ideal (𝓞 K) | absNorm I = n ∧ J ∣ I}.ncard = cnt K (n / absNorm J) := by
  have hJn : 0 < absNorm J := Nat.pos_of_ne_zero (by rwa [Ne, absNorm_eq_zero_iff])
  have himg : {I : Ideal (𝓞 K) | absNorm I = n ∧ J ∣ I} =
      (J * ·) '' {I | absNorm I = n / absNorm J} := by
    ext I
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hI, ⟨I', rfl⟩⟩
      refine ⟨I', ?_, rfl⟩
      rw [map_mul] at hI
      rw [← hI, Nat.mul_div_cancel_left _ hJn]
    · rintro ⟨I', hI', rfl⟩
      refine ⟨?_, dvd_mul_right J I'⟩
      rw [map_mul, hI', Nat.mul_div_cancel' hd]
  rw [himg, Set.ncard_image_of_injective _ (fun a b h => mul_left_cancel₀ hJ h), cnt]

theorem cnt_not_dvd (J : Ideal (𝓞 K)) (n : ℕ) (hd : ¬ absNorm J ∣ n) :
    {I : Ideal (𝓞 K) | absNorm I = n ∧ J ∣ I} = ∅ := by
  ext I
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  rintro rfl ⟨I', rfl⟩
  exact hd (by rw [map_mul]; exact dvd_mul_right _ _)

theorem cnt_dvd' (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) (n : ℕ) :
    {I : Ideal (𝓞 K) | absNorm I = n ∧ J ∣ I}.ncard =
      if absNorm J ∣ n then cnt K (n / absNorm J) else 0 := by
  split_ifs with hd
  · exact cnt_dvd J hJ n hd
  · rw [cnt_not_dvd J n hd, Set.ncard_empty]

theorem one_rec {p q : ℕ} (h : One K p q) (n : ℕ) (hn : 0 < n) (hp : p ∣ n) :
    cnt K n = if q ∣ n then cnt K (n / q) else 0 := by
  obtain ⟨P, hP, hPq, hdiv⟩ := h
  have : {I : Ideal (𝓞 K) | absNorm I = n} = {I : Ideal (𝓞 K) | absNorm I = n ∧ P ∣ I} := by
    ext I
    simp only [Set.mem_setOf_eq]
    exact ⟨fun hI => ⟨hI, hdiv I (ne_bot_of_norm hn hI) (hI ▸ hp)⟩, fun h => h.1⟩
  rw [cnt, this, cnt_dvd' P hP, hPq]

theorem split_rec {p : ℕ} (h : Split K p) (n : ℕ) (hn : 0 < n) (hp : p ∣ n) :
    cnt K n + (if p * p ∣ n then cnt K (n / (p * p)) else 0) = 2 * cnt K (n / p) := by
  obtain ⟨P, Q, hP, hQ, hPn, hQn, hPQ, hdiv⟩ := h
  have hPQ0 : P * Q ≠ ⊥ := mul_ne_zero hP hQ
  set A := {I : Ideal (𝓞 K) | absNorm I = n ∧ P ∣ I}
  set B := {I : Ideal (𝓞 K) | absNorm I = n ∧ Q ∣ I}
  have hU : A ∪ B = {I : Ideal (𝓞 K) | absNorm I = n} := by
    ext I
    simp only [A, B, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hI
      rcases hdiv I (ne_bot_of_norm hn hI) (hI ▸ hp) with h | h
      · exact Or.inl ⟨hI, h⟩
      · exact Or.inr ⟨hI, h⟩
  have hI : A ∩ B = {I : Ideal (𝓞 K) | absNorm I = n ∧ P * Q ∣ I} := by
    ext I
    simp only [A, B, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨_, h3⟩⟩; exact ⟨h1, hPQ I h2 h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, (dvd_mul_right P Q).trans h2⟩, ⟨h1, (dvd_mul_left Q P).trans h2⟩⟩
  have key := Set.ncard_union_add_ncard_inter A B ((fin n).subset fun I h => h.1)
    ((fin n).subset fun I h => h.1)
  rw [hU, hI] at key
  have hA : A.ncard = cnt K (n / p) := by rw [cnt_dvd P hP n (hPn ▸ hp), hPn]
  have hB : B.ncard = cnt K (n / p) := by rw [cnt_dvd Q hQ n (hQn ▸ hp), hQn]
  rw [cnt_dvd' _ hPQ0, map_mul, hPn, hQn, hA, hB] at key
  rw [cnt]; omega

/-! The divisor sums. -/

section Sums
variable (χ : ℕ → ℤ) (hmul : ∀ a b, χ (a * b) = χ a * χ b) (h1 : χ 1 = 1)
include hmul h1

theorem chi_pow (p j : ℕ) : χ (p ^ j) = χ p ^ j := by
  induction j with
  | zero => simp [h1]
  | succ j ih => rw [pow_succ, hmul, ih, pow_succ]

theorem sum_pow_mul (p : ℕ) (hp : p.Prime) (e m : ℕ) (hpm : ¬ p ∣ m) :
    ∑ d ∈ (p ^ e * m).divisors, χ d = (∑ j ∈ Finset.range (e + 1), χ p ^ j) * ∑ d ∈ m.divisors, χ d := by
  let χA : ArithmeticFunction ℤ := ⟨fun d => if d = 0 then 0 else χ d, by simp⟩
  have hχA : χA.IsMultiplicative := by
    refine ⟨by simp [χA, h1], fun {a b} _ => ?_⟩
    by_cases ha : a = 0
    · simp [χA, ha]
    by_cases hb : b = 0
    · simp [χA, hb]
    simp [χA, ha, hb, hmul]
  have hf := ArithmeticFunction.isMultiplicative_zeta.natCast.mul hχA
  have hval : ∀ x, ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) * χA) x = ∑ d ∈ x.divisors, χ d := by
    intro x
    rw [ArithmeticFunction.coe_zeta_mul_apply]
    refine Finset.sum_congr rfl fun d hd => ?_
    have : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
    simp [χA, this]
  have hcop : (p ^ e).Coprime m := Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm)
  rw [← hval, hf.map_mul_of_coprime hcop, hval, hval, Nat.sum_divisors_prime_pow hp]
  congr 1
  exact Finset.sum_congr rfl fun j _ => chi_pow χ hmul h1 p j

end Sums

/-! The count. -/

theorem count (χ : ℕ → ℤ) (hmul : ∀ a b, χ (a * b) = χ a * χ b) (h1 : χ 1 = 1)
    (hdata : ∀ p, p.Prime →
      (χ p = 1 ∧ Split K p) ∨ (χ p = -1 ∧ One K p (p * p)) ∨ (χ p = 0 ∧ One K p p)) :
    ∀ n, 0 < n → (cnt K n : ℤ) = ∑ d ∈ n.divisors, χ d := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  by_cases hn1 : n = 1
  · subst hn1; simp [cnt_one, h1]
  obtain ⟨p, hp, hpn⟩ : ∃ p, p.Prime ∧ p ∣ n := ⟨n.minFac, Nat.minFac_prime hn1, Nat.minFac_dvd n⟩
  obtain ⟨e, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.ne_one
  have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  have hp0 := hp.pos
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := by
    rcases e with _ | k
    · simp at hpn; exact absurd hpn hpm
    · exact ⟨k, rfl⟩
  have hS := sum_pow_mul χ hmul h1 p hp
  have hd1 : p ^ (k + 1) * m / p = p ^ k * m :=
    Nat.div_eq_of_eq_mul_left hp0 (by ring)
  have hpos1 : 0 < p ^ k * m := Nat.mul_pos (Nat.pow_pos (n := k) hp0) hm
  have hlt1 : p ^ k * m < p ^ (k + 1) * m := by
    have h := Nat.mul_lt_mul_of_pos_left hp.one_lt hpos1
    calc _ = p ^ k * m * 1 := by ring
      _ < _ := h
      _ = _ := by ring
  have ih1 := ih _ hlt1 hpos1
  rw [hS k m hpm] at ih1
  rw [hS (k + 1) m hpm]
  -- whether p² divides n
  have hpp : p * p ∣ p ^ (k + 1) * m ↔ 1 ≤ k := by
    constructor
    · intro h
      by_contra hk
      have hk0 : k = 0 := by omega
      subst hk0
      simp only [zero_add, pow_one] at h
      exact hpm ((Nat.mul_dvd_mul_iff_left hp0).1 h)
    · intro hk
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      exact ⟨p ^ j * m, by ring⟩
  rcases hdata p hp with ⟨hχ, hsp⟩ | ⟨hχ, hin⟩ | ⟨hχ, hra⟩
  · have hr := split_rec hsp _ hn (dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) m)
    rw [hd1] at hr
    rw [hχ] at ih1 ⊢
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at ih1 ⊢
    rcases k with _ | j
    · have : ¬ p * p ∣ p ^ (0 + 1) * m := fun h => absurd ((hpp).1 h) (by omega)
      rw [if_neg this] at hr
      simp only [zero_add, pow_zero, one_mul] at ih1 hr ⊢
      have := congrArg (fun x : ℕ => (x : ℤ)) hr
      push_cast at this
      push_cast at ih1 ⊢

      linarith
    · rw [if_pos ((hpp).2 (by omega))] at hr
      have hd2 : p ^ (j + 1 + 1) * m / (p * p) = p ^ j * m :=
        Nat.div_eq_of_eq_mul_left (Nat.mul_pos hp0 hp0) (by ring)
      rw [hd2] at hr
      have hlt2 : p ^ j * m < p ^ (j + 1 + 1) * m := by
        have : p ^ j * m < p ^ (j + 1) * m := by
          have h := Nat.mul_lt_mul_of_pos_left hp.one_lt (Nat.mul_pos (Nat.pow_pos (n := j) hp0) hm)
          calc _ = p ^ j * m * 1 := by ring
            _ < _ := h
            _ = _ := by ring
        exact this.trans hlt1
      have ih2 := ih _ hlt2 (Nat.mul_pos (Nat.pow_pos (n := j) hp0) hm)
      rw [hS j m hpm, hχ] at ih2
      simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at ih2
      have := congrArg (fun x : ℕ => (x : ℤ)) hr
      push_cast at this ih1 ih2 ⊢
      linear_combination this - ih2 + 2 * ih1
  · have hr := one_rec hin _ hn (dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) m)
    rw [hχ] at ih1 ⊢
    rcases k with _ | j
    · have : ¬ p * p ∣ p ^ (0 + 1) * m := fun h => absurd ((hpp).1 h) (by omega)
      rw [if_neg this] at hr
      rw [hr]; simp [Finset.sum_range_succ]
    · rw [if_pos ((hpp).2 (by omega))] at hr
      have hd2 : p ^ (j + 1 + 1) * m / (p * p) = p ^ j * m :=
        Nat.div_eq_of_eq_mul_left (Nat.mul_pos hp0 hp0) (by ring)
      rw [hd2] at hr
      have hlt2 : p ^ j * m < p ^ (j + 1 + 1) * m := by
        have : p ^ j * m < p ^ (j + 1) * m := by
          have h := Nat.mul_lt_mul_of_pos_left hp.one_lt (Nat.mul_pos (Nat.pow_pos (n := j) hp0) hm)
          calc _ = p ^ j * m * 1 := by ring
            _ < _ := h
            _ = _ := by ring
        exact this.trans hlt1
      have ih2 := ih _ hlt2 (Nat.mul_pos (Nat.pow_pos (n := j) hp0) hm)
      rw [hS j m hpm, hχ] at ih2
      rw [hr, ih2, Finset.sum_range_succ _ (j + 1 + 1), Finset.sum_range_succ _ (j + 1)]
      ring_nf
  · have hr := one_rec hra _ hn (dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) m)
    rw [if_pos (dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) m), hd1] at hr
    rw [hχ] at ih1 ⊢
    rw [hr, ih1, Finset.sum_range_succ _ (k + 1)]
    simp

/-! The shapes from the primes over `p`. -/

section Primes

theorem exists_over (p : ℕ) [hp : Fact p.Prime] (I : Ideal (𝓞 K)) (hI : p ∣ absNorm I) :
    ∃ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), P ∣ I := by
  obtain ⟨P, hPm, hPu, hPI⟩ := exists_isMaximal_dvd_of_dvd_absNorm' hp.out I hI
  exact ⟨P, ⟨hPm.isPrime, ⟨hPu.symm⟩⟩, hPI⟩

theorem norm_over (p : ℕ) [hp : Fact p.Prime] {P : Ideal (𝓞 K)}
    (hP : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K)) : absNorm P = p ^ P.inertiaDeg ℤ := by
  haveI := hP.1; haveI := hP.2
  exact (pow_inertiaDeg p P).symm

theorem one_of (p : ℕ) [hp : Fact p.Prime] (f : ℕ)
    (h1 : (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 1)
    (hf : ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = f) : One K p (p ^ f) := by
  obtain ⟨P, hP⟩ := Set.ncard_eq_one.mp h1
  have hPm : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) := by rw [hP]; rfl
  have hn : absNorm P = p ^ f := by rw [norm_over p hPm, hf P hPm]
  refine ⟨P, ne_bot_of_norm (pow_pos hp.out.pos f) hn, hn, fun I _ hpI => ?_⟩
  obtain ⟨Q, hQ, hQI⟩ := exists_over p I hpI
  rw [hP, Set.mem_singleton_iff] at hQ
  exact hQ ▸ hQI

theorem split_of (p : ℕ) [hp : Fact p.Prime]
    (h2 : (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 2)
    (hf : ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 1) : Split K p := by
  obtain ⟨P, Q, hPQ, hS⟩ := Set.ncard_eq_two.mp h2
  have hPm : P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) := by rw [hS]; simp
  have hQm : Q ∈ primesOver (span {(p : ℤ)}) (𝓞 K) := by rw [hS]; simp
  have nP : absNorm P = p := by rw [norm_over p hPm, hf P hPm, pow_one]
  have nQ : absNorm Q = p := by rw [norm_over p hQm, hf Q hQm, pow_one]
  have hPb := ne_bot_of_norm hp.out.pos nP
  have hQb := ne_bot_of_norm hp.out.pos nQ
  refine ⟨P, Q, hPb, hQb, nP, nQ, fun I hPI hQI => ?_, fun I _ hpI => ?_⟩
  · haveI : P.IsMaximal := hPm.1.isMaximal hPb
    haveI : Q.IsMaximal := hQm.1.isMaximal hQb
    have hcop : P ⊔ Q = ⊤ := Ideal.IsMaximal.coprime_of_ne ‹_› ‹_› hPQ
    rw [Ideal.dvd_iff_le] at hPI hQI ⊢
    rw [Ideal.mul_eq_inf_of_coprime hcop]
    exact le_inf hPI hQI
  · obtain ⟨R, hR, hRI⟩ := exists_over p I hpI
    rw [hS] at hR
    rcases hR with rfl | hR
    · exact Or.inl hRI
    · rw [Set.mem_singleton_iff] at hR; subst hR; exact Or.inr hRI

end Primes

end H1Work


section
namespace CN1.Foundations
open NumberField Polynomial Ideal
section Setup
variable {K : Type*} [Field K] [NumberField K] {m : ℕ} {α : K} (hα : α ^ 2 = -(m : K))
  (hK : Module.finrank ℚ K = 2) (hm : Squarefree m)
section Prime
variable (p : ℕ) [hp : Fact p.Prime]
include hα hK hm in
theorem monicFactorsMod_of_double {r : ZMod p}
    (hr : r ^ 2 + (bInt m : ZMod p) * r + cInt m = 0) (hrr : -(bInt m : ZMod p) - r = r) :
    RingOfIntegers.monicFactorsMod (omegaInt hα) p = {X - C r} := by
  unfold RingOfIntegers.monicFactorsMod
  rw [minpoly_omegaInt_map hα p hm.ne_zero, quad_eq_mul_of_root p _ _ r hr, hrr,
    UniqueFactorizationMonoid.normalizedFactors_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _),
    UniqueFactorizationMonoid.normalizedFactors_irreducible (irreducible_X_sub_C _),
    (monic_X_sub_C _).normalize_eq_self, Multiset.singleton_add, Multiset.toFinset_cons,
    Multiset.toFinset_singleton, Finset.insert_eq_of_mem (Finset.mem_singleton_self _)]
include hα hK hm in
/-- A prime dividing `m ≡ 3 (mod 4)` has one prime above it, of inertia degree one. -/
theorem ram_data (h3 : m % 4 = 3) (hpm : p ∣ m) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = 1 ∧
      ∀ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K), P.inertiaDeg ℤ = 1 := by
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have h2 := two_ne_zero_of_ne_two p hp2
  have hi : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ h2
  have hm0 : (m : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff m p).mpr hpm
  obtain ⟨c, hc⟩ : (4 : ℕ) ∣ m + 1 := by omega
  have hc' : ((m + 1) / 4 : ℕ) = c := by omega
  have hc4 : (m : ZMod p) + 1 = 4 * c := by
    have := congrArg (Nat.cast (R := ZMod p)) hc
    push_cast at this
    exact this
  have hb : (bInt m : ZMod p) = -1 := by simp [bInt, h3]
  have hcc : (cInt m : ZMod p) = c := by simp [cInt, h3, hc']
  set r : ZMod p := 2⁻¹
  have h4 : (4 : ZMod p) ≠ 0 := by
    have : (4 : ZMod p) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have hr : r ^ 2 + (bInt m : ZMod p) * r + cInt m = 0 := by
    rw [hb, hcc]
    have key : (4 : ZMod p) * (r ^ 2 + -1 * r + c) = 0 := by
      linear_combination (2 * r - 1) * hi - hc4 + hm0
    exact (mul_eq_zero.mp key).resolve_left h4
  have hrr : -(bInt m : ZMod p) - r = r := by
    rw [hb]; linear_combination -hi
  have hF := monicFactorsMod_of_double hα hK hm p hr hrr
  constructor
  · rw [ncard_primesOver_eq_card_monicFactorsMod hα hK hm p, hF, Finset.card_singleton]
  · intro P hP
    rw [inertiaDeg_eq_natDegree hα hK hm p hP]
    have hmem := (Finset.ext_iff.mp hF _).mp
      (Ideal.primesOverSpanEquivMonicFactorsMod (not_dvd_exponent_omegaInt hα hK hm p) ⟨P, hP⟩).2
    rw [Finset.mem_singleton] at hmem
    rw [hmem, natDegree_X_sub_C]
end Prime

include hα hK hm in
/-- The prime data for the Jacobi character `d ↦ (d | m)`, `m ≡ 3 (mod 4)` squarefree. -/
theorem jacobi_data (h3 : m % 4 = 3) (p : ℕ) (hpp : p.Prime) :
    (jacobiSym (p : ℤ) m = 1 ∧ H1Work.Split K p) ∨
      (jacobiSym (p : ℤ) m = -1 ∧ H1Work.One K p (p * p)) ∨
      (jacobiSym (p : ℤ) m = 0 ∧ H1Work.One K p p) := by
  haveI : Fact p.Prime := ⟨hpp⟩
  by_cases hpm : p ∣ m
  · right; right
    refine ⟨jacobiSym.eq_zero_iff.mpr ⟨hm.ne_zero, ?_⟩, ?_⟩
    · rw [Int.gcd_natCast_natCast, Nat.gcd_eq_left hpm]; exact hpp.ne_one
    · obtain ⟨h1, hf⟩ := ram_data hα hK hm p h3 hpm
      simpa using H1Work.one_of p 1 h1 hf
  · have hpd : ¬ p ∣ disc m := by rwa [disc_of_three_mod_four h3]
    have hcop : IsCoprime (p : ℤ) (disc m : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hpd)
    have hk := kroneckerChar_apply_of_three_mod_four h3 hcop
    rw [Int.cast_natCast] at hk
    rcases kroneckerChar_eq_one_or_neg_one p hpd with h | h
    · left
      refine ⟨by rw [h] at hk; exact_mod_cast hk.symm, ?_⟩
      obtain ⟨h2, hf⟩ := ncard_primesOver_eq_two_of_kroneckerChar_eq_one hα hK hm p hpd h
      exact H1Work.split_of p h2 hf
    · right; left
      refine ⟨by rw [h] at hk; exact_mod_cast hk.symm, ?_⟩
      obtain ⟨h2, hf⟩ := ncard_primesOver_eq_one_of_kroneckerChar_eq_neg_one hα hK hm p hpd h
      simpa [sq] using H1Work.one_of p 2 h2 hf

include hα hK hm in
theorem ideal_count (h3 : m % 4 = 3) (n : ℕ) (hn : 0 < n) :
    (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℤ) = ∑ a ∈ n.divisors, jacobiSym a m := by
  rw [H1Work.cnt_eq]
  exact H1Work.count (fun d : ℕ => jacobiSym (d : ℤ) m)
    (fun a b => by push_cast; exact jacobiSym.mul_left _ _ _)
    (by simpa using jacobiSym.one_left m)
    (fun p hp => jacobi_data hα hK hm h3 p hp) n hn
end Setup
end CN1.Foundations
end

open Polynomial NumberField Module in
theorem OMA.solution :
    OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1.H1 := by
  intro s hs hsq h8
  letI : Fact (Irreducible (X^2+C (s:ℚ))) :=
    ⟨OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1.quad_irred hs⟩
  let K := AdjoinRoot (X^2+C (s:ℚ))
  let δ : K := AdjoinRoot.root (X^2+C (s:ℚ))
  have ds : δ^2=-(s:K) := by
    have h := AdjoinRoot.eval₂_root (X^2+C (s:ℚ))
    rw [eval₂_add,eval₂_pow,eval₂_X,eval₂_C] at h
    apply eq_neg_iff_add_eq_zero.mpr
    simpa [δ,map_natCast] using h
  have rank : finrank ℚ K=2 := by
    let f : ℚ[X] := X^2+C (s:ℚ)
    have nz : f ≠ 0 :=
      (OMA.R_Erdos338_erdos_338_variants_triangular_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1.quad_irred hs).ne_zero
    change finrank ℚ (AdjoinRoot f)=2
    rw [(AdjoinRoot.powerBasis nz).finrank,AdjoinRoot.powerBasis_dim]
    exact natDegree_X_pow_add_C
  exact CN1.Foundations.ideal_count ds rank hsq (by omega)
