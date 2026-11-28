import OMAReductions.R_PartitionParity_zheng_odd_R2

/-!
Proof of `PartitionParity.zheng.odd.R2.H2`: for every squarefree `D > 1` with `D ≡ 23 (mod 24)`,
the class number of `ℚ(√(-D))` is bounded above by the number of reduced positive-definite binary
quadratic forms of discriminant `-D`.
-/

-- Step PartitionParity.zheng.odd.R2.H2: hypothesis H2 of reduction PartitionParity.zheng.odd.R2
-- Credit: @yhay81
-- H2 := ∀ (D : ℕ) (hD : 1 < D), Squarefree D → D % 24 = 23 →   haveI : Fact (Irreducible (X ^ 2 + C (D : ℚ))) :=     ⟨irreducible_X_sq_add_C_of_pos (Nat.cast_pos.2 (by omega))⟩   NumberField.classNumber (AdjoinRoot (X ^ 2 + C (D : ℚ))) ≤     {p : ℤ × ℤ × ℤ | PartitionParity.IsReducedForm D p.1 p.2.1 p.2.2}.ncard

namespace OMA.PartitionParity_zheng_odd_R2_H2

open Polynomial
open scoped NumberField nonZeroDivisors

private def mNat (D : ℕ) : ℕ := (D + 1) / 4

private lemma four_mul_mNat {D : ℕ} (hmod : D % 24 = 23) : 4 * mNat D = D + 1 := by
  unfold mNat
  omega

private def IsForm (D : ℕ) (a b c : ℤ) : Prop :=
  b ^ 2 - 4 * a * c = -(D : ℤ) ∧ 0 < a

private lemma isForm_c_pos {D : ℕ} (hD : 1 < D) {a b c : ℤ} (h : IsForm D a b c) : 0 < c := by
  rcases h with ⟨hdisc, ha⟩
  have hD0 : (0 : ℤ) < D := by exact_mod_cast (by omega : 0 < D)
  nlinarith [sq_nonneg b]

private lemma isForm_b_odd {D : ℕ} (hmod : D % 24 = 23) {a b c : ℤ} (h : IsForm D a b c) :
    2 * ((b - 1) / 2) + 1 = b := by
  have hdisc := h.1
  have hD4 : (D : ℤ) % 4 = 3 := by omega
  have hnot : b % 2 ≠ 0 := by
    intro hev
    have hb2 : b ^ 2 = 4 * (b / 2) ^ 2 := by
      set k := b / 2
      have : b = 2 * k := by omega
      rw [this]
      ring
    have hD_eq : (D : ℤ) = 4 * (a * c - (b / 2) ^ 2) := by linarith
    omega
  omega

private lemma isForm_r_eq {D : ℕ} (hmod : D % 24 = 23) {a b c : ℤ} (h : IsForm D a b c) :
    ((b - 1) / 2) ^ 2 + (b - 1) / 2 + (mNat D : ℤ) = a * c := by
  have hb := isForm_b_odd hmod h
  have hm : 4 * (mNat D : ℤ) = (D : ℤ) + 1 := by exact_mod_cast four_mul_mNat hmod
  have hdisc := h.1
  nlinarith

private lemma isForm_gcd_one {D : ℕ} (hsq : Squarefree D) {a b c : ℤ}
    (hdisc : b ^ 2 - 4 * a * c = -(D : ℤ)) : Int.gcd (Int.gcd a b) c = 1 := by
  let g : ℕ := Int.gcd (Int.gcd a b) c
  have hgab : (g : ℤ) ∣ ((Int.gcd a b : ℕ) : ℤ) := Int.gcd_dvd_left (Int.gcd a b : ℤ) c
  have hgc : (g : ℤ) ∣ c := Int.gcd_dvd_right (Int.gcd a b : ℤ) c
  have hga : (g : ℤ) ∣ a := hgab.trans (Int.gcd_dvd_left a b)
  have hgb : (g : ℤ) ∣ b := hgab.trans (Int.gcd_dvd_right a b)
  obtain ⟨a', ha'⟩ := hga
  obtain ⟨b', hb'⟩ := hgb
  obtain ⟨c', hc'⟩ := hgc
  have hdvd_z : ((g ^ 2 : ℕ) : ℤ) ∣ (D : ℤ) := by
    refine ⟨4 * a' * c' - b' ^ 2, ?_⟩
    push_cast
    rw [ha', hb', hc'] at hdisc
    linear_combination hdisc
  have hdvd_n : g ^ 2 ∣ D := Int.ofNat_dvd.mp hdvd_z
  exact Nat.isUnit_iff.mp (hsq g (by simpa [sq] using hdvd_n))

private lemma reduced_a_pos {D : ℕ} (hD : 1 < D) {a b c : ℤ}
    (h : PartitionParity.IsReducedForm D a b c) : 0 < a := by
  obtain ⟨hdisc, hba, _, _, _⟩ := h
  have ⟨h1, h2⟩ := abs_le.mp hba
  have hD0 : (0 : ℤ) < D := by exact_mod_cast (by omega : 0 < D)
  by_contra ha
  have : a = 0 := by omega
  have : b = 0 := by omega
  nlinarith

private lemma reduced_finite {D : ℕ} (hD : 1 < D) :
    {p : ℤ × ℤ × ℤ | PartitionParity.IsReducedForm D p.1 p.2.1 p.2.2}.Finite := by
  let B : Finset (ℤ × ℤ × ℤ) :=
    Finset.Icc (1 : ℤ) (D : ℤ) ×ˢ (Finset.Icc (-(D : ℤ)) (D : ℤ) ×ˢ Finset.Icc (1 : ℤ) (D : ℤ))
  refine (Finset.finite_toSet B).subset ?_
  rintro ⟨a, b, c⟩ hred
  have ha : 0 < a := reduced_a_pos hD hred
  obtain ⟨hdisc, hba, hac, _, _⟩ := hred
  dsimp only at hdisc hba hac
  have ⟨hb1, hb2⟩ := abs_le.mp hba
  have hb_sq : b ^ 2 ≤ a ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ a - b by omega) (show 0 ≤ a + b by omega)]
  have ha_sq : a ^ 2 ≤ a * c := by nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hac)]
  have ha_le : a ≤ (D : ℤ) := by nlinarith
  have hc_pos : 0 < c := by omega
  have hc_le : c ≤ (D : ℤ) := by nlinarith [mul_nonneg (show 0 ≤ a - 1 by omega) hc_pos.le]
  simp only [Finset.mem_coe, B, Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨by omega, ha_le⟩, ⟨by omega, by omega⟩, ⟨by omega, hc_le⟩⟩

private lemma span_singleton_mul_pair {R : Type*} [CommSemiring R] (x u v : R) :
    Ideal.span ({x} : Set R) * Ideal.span ({u, v} : Set R) = Ideal.span ({x * u, x * v} : Set R) := by
  rw [Ideal.span_mul_span]
  congr 1
  ext t
  simp [eq_comm]

section QuadField

variable (D : ℕ) [hf : Fact (Irreducible (X ^ 2 + C (D : ℚ)))]

private noncomputable abbrev QPoly : ℚ[X] := X ^ 2 + C (D : ℚ)

private abbrev QField : Type := AdjoinRoot (QPoly D)

private noncomputable def θ : QField D := AdjoinRoot.root (QPoly D)

private lemma θ_sq : θ D ^ 2 = -(D : QField D) := by
  have h := AdjoinRoot.eval₂_root (QPoly D)
  simp only [QPoly, eval₂_add, eval₂_X_pow, eval₂_C] at h
  have hof : AdjoinRoot.of (QPoly D) (D : ℚ) = (D : QField D) := map_natCast _ D
  rw [hof] at h
  exact eq_neg_of_add_eq_zero_left h

private lemma coords_exists (z : QField D) :
    ∃ x y : ℚ, z = (x : QField D) + (y : QField D) * θ D := by
  induction z using AdjoinRoot.induction_on with
  | ih p =>
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      obtain ⟨x₁, y₁, h₁⟩ := hp
      obtain ⟨x₂, y₂, h₂⟩ := hq
      refine ⟨x₁ + x₂, y₁ + y₂, ?_⟩
      rw [map_add, h₁, h₂]
      push_cast
      ring
    | monomial n a =>
      induction n with
      | zero =>
        refine ⟨a, 0, ?_⟩
        simp [AdjoinRoot.mk_C]
      | succ n ih =>
        obtain ⟨x, y, hxy⟩ := ih
        refine ⟨-(D : ℚ) * y, x, ?_⟩
        have hstep : AdjoinRoot.mk (QPoly D) (monomial (n + 1) a) =
            AdjoinRoot.mk (QPoly D) (monomial n a) * θ D := by
          rw [show monomial (n + 1) a = monomial n a * X by
            rw [← C_mul_X_pow_eq_monomial, ← C_mul_X_pow_eq_monomial, pow_succ, mul_assoc]]
          rw [map_mul, AdjoinRoot.mk_X]
          rfl
        rw [hstep, hxy]
        have hθ := θ_sq D
        push_cast
        linear_combination (y : QField D) * hθ

private lemma coords_unique (hD : 0 < D) {x y : ℚ}
    (h : (x : QField D) + (y : QField D) * θ D = 0) : x = 0 ∧ y = 0 := by
  have hy : y = 0 := by
    by_contra hy0
    have hyK : (y : QField D) ≠ 0 := Rat.cast_ne_zero.mpr hy0
    have hθ : θ D = ((-x / y : ℚ) : QField D) := by
      push_cast
      apply mul_left_cancel₀ hyK
      have hmul : (y : QField D) * (-(x : QField D) / (y : QField D)) = -(x : QField D) :=
        mul_div_cancel₀ _ hyK
      linear_combination h - hmul
    have hsq : (((-x / y) ^ 2 : ℚ) : QField D) = ((-(D : ℚ) : ℚ) : QField D) := by
      rw [Rat.cast_pow, Rat.cast_neg, Rat.cast_natCast, ← hθ, θ_sq]
    have hq : (-x / y) ^ 2 = -(D : ℚ) := Rat.cast_injective hsq
    have hpos : (0 : ℚ) < (D : ℚ) := Nat.cast_pos.mpr hD
    nlinarith [sq_nonneg (-x / y)]
  subst hy
  simp only [Rat.cast_zero, zero_mul, add_zero] at h
  exact ⟨Rat.cast_eq_zero.mp h, rfl⟩

private noncomputable def ωK : QField D := (1 + θ D) / 2

private lemma ωK_sq (hmod : D % 24 = 23) :
    ωK D ^ 2 = ωK D - (mNat D : QField D) := by
  have hm : (4 : QField D) * (mNat D : QField D) = (D : QField D) + 1 := by
    exact_mod_cast four_mul_mNat hmod
  have hθ := θ_sq D
  unfold ωK
  field_simp
  linear_combination hθ + hm

private lemma ωK_isIntegral (hmod : D % 24 = 23) : IsIntegral ℤ (ωK D) := by
  refine ⟨X ^ 2 - X + C (mNat D : ℤ), ?_, ?_⟩
  · have hmon : (X ^ 2 + (-X + C (mNat D : ℤ))).Monic := by
      apply Polynomial.monic_X_pow_add
      refine (Polynomial.degree_add_le _ _).trans_lt (max_lt ?_ ?_)
      · rw [Polynomial.degree_neg, Polynomial.degree_X]
        decide
      · exact Polynomial.degree_C_le.trans_lt (by decide)
    simpa [sub_eq_add_neg, add_assoc] using hmon
  · simp only [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C]
    simp only [eq_intCast, Int.cast_natCast]
    have hsq := ωK_sq D hmod
    linear_combination hsq

private noncomputable def ω (hmod : D % 24 = 23) : 𝓞 (QField D) :=
  ⟨ωK D, ωK_isIntegral D hmod⟩

private lemma ω_sq (hmod : D % 24 = 23) :
    ω D hmod ^ 2 = ω D hmod - (mNat D : 𝓞 (QField D)) := by
  apply NumberField.RingOfIntegers.ext
  change (ωK D) ^ 2 = ωK D - (mNat D : QField D)
  exact ωK_sq D hmod

private noncomputable def mkO (hmod : D % 24 = 23) (a b : ℤ) : 𝓞 (QField D) :=
  (a : 𝓞 (QField D)) + (b : 𝓞 (QField D)) * ω D hmod

private lemma mkO_coe (hmod : D % 24 = 23) (a b : ℤ) :
    ((mkO D hmod a b : 𝓞 (QField D)) : QField D) =
      (((a : ℚ) + (b : ℚ) / 2 : ℚ) : QField D) + (((b : ℚ) / 2 : ℚ) : QField D) * θ D := by
  change (a : QField D) + (b : QField D) * ωK D = _
  unfold ωK
  push_cast
  ring

private lemma mkO_inj (hD : 0 < D) (hmod : D % 24 = 23) {a₁ b₁ a₂ b₂ : ℤ}
    (h : mkO D hmod a₁ b₁ = mkO D hmod a₂ b₂) : a₁ = a₂ ∧ b₁ = b₂ := by
  have hc : ((mkO D hmod a₁ b₁ : 𝓞 (QField D)) : QField D) =
      ((mkO D hmod a₂ b₂ : 𝓞 (QField D)) : QField D) :=
    congrArg (fun z : 𝓞 (QField D) => (z : QField D)) h
  rw [mkO_coe, mkO_coe] at hc
  have hzero : ((((a₁ : ℚ) + (b₁ : ℚ) / 2) - ((a₂ : ℚ) + (b₂ : ℚ) / 2) : ℚ) : QField D) +
      (((b₁ : ℚ) / 2 - (b₂ : ℚ) / 2 : ℚ) : QField D) * θ D = 0 := by
    push_cast at hc ⊢
    linear_combination hc
  obtain ⟨h1, h2⟩ := coords_unique D hD hzero
  have hb : (b₁ : ℚ) = (b₂ : ℚ) := by linarith
  have ha : (a₁ : ℚ) = (a₂ : ℚ) := by linarith
  exact ⟨by exact_mod_cast ha, by exact_mod_cast hb⟩

private lemma mkO_add (hmod : D % 24 = 23) (a₁ b₁ a₂ b₂ : ℤ) :
    mkO D hmod a₁ b₁ + mkO D hmod a₂ b₂ = mkO D hmod (a₁ + a₂) (b₁ + b₂) := by
  unfold mkO
  push_cast
  ring

private lemma mkO_sub (hmod : D % 24 = 23) (a₁ b₁ a₂ b₂ : ℤ) :
    mkO D hmod a₁ b₁ - mkO D hmod a₂ b₂ = mkO D hmod (a₁ - a₂) (b₁ - b₂) := by
  unfold mkO
  push_cast
  ring

private lemma mkO_neg (hmod : D % 24 = 23) (a b : ℤ) :
    -(mkO D hmod a b) = mkO D hmod (-a) (-b) := by
  unfold mkO
  push_cast
  ring

private lemma mkO_zero_right (hmod : D % 24 = 23) (a : ℤ) :
    mkO D hmod a 0 = (a : 𝓞 (QField D)) := by
  simp [mkO]

private lemma mkO_int_mul (hmod : D % 24 = 23) (c a b : ℤ) :
    (c : 𝓞 (QField D)) * mkO D hmod a b = mkO D hmod (c * a) (c * b) := by
  unfold mkO
  push_cast
  ring

private lemma mkO_mul (hmod : D % 24 = 23) (a₁ b₁ a₂ b₂ : ℤ) :
    mkO D hmod a₁ b₁ * mkO D hmod a₂ b₂ =
      mkO D hmod (a₁ * a₂ - (mNat D : ℤ) * b₁ * b₂)
        (a₁ * b₂ + b₁ * a₂ + b₁ * b₂) := by
  unfold mkO
  have hsq := ω_sq D hmod
  push_cast
  linear_combination (b₁ : 𝓞 (QField D)) * (b₂ : 𝓞 (QField D)) * hsq

private lemma mkO_mul_ω (hmod : D % 24 = 23) (a b : ℤ) :
    mkO D hmod a b * ω D hmod = mkO D hmod (-(mNat D : ℤ) * b) (a + b) := by
  have hω : ω D hmod = mkO D hmod 0 1 := by simp [mkO]
  rw [hω, mkO_mul]
  congr 1 <;> ring

private lemma mkO_mul_conj (hmod : D % 24 = 23) (a b : ℤ) :
    mkO D hmod a b * mkO D hmod (a + b) (-b) =
      ((a ^ 2 + a * b + (mNat D : ℤ) * b ^ 2 : ℤ) : 𝓞 (QField D)) := by
  rw [mkO_mul, ← mkO_zero_right D hmod]
  congr 1 <;> ring

private lemma ringOfIntegers_surj (hD : 1 < D) (hsq : Squarefree D) (hmod : D % 24 = 23)
    (z : 𝓞 (QField D)) : ∃ a b : ℤ, z = mkO D hmod a b := by
  obtain ⟨x, y, hxy⟩ := coords_exists D (z : QField D)
  have hz_int : IsIntegral ℤ (z : QField D) := NumberField.RingOfIntegers.isIntegral_coe z
  by_cases hy : y = 0
  · subst hy
    simp only [Rat.cast_zero, zero_mul, add_zero] at hxy
    have hx_int : IsIntegral ℤ x := by
      have h1 : IsIntegral ℤ (algebraMap ℚ (QField D) x) := by
        simpa [Algebra.algebraMap_eq_smul_one, hxy] using hz_int
      exact (isIntegral_algebraMap_iff (algebraMap ℚ (QField D)).injective).mp h1
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx_int
    refine ⟨a, 0, NumberField.RingOfIntegers.ext ?_⟩
    rw [mkO_zero_right, hxy]
    have ha' : (a : ℚ) = x := by simpa using ha
    rw [← ha']
    simp
  · let q : ℚ[X] := X ^ 2 - C (2 * x) * X + C (x ^ 2 + (D : ℚ) * y ^ 2)
    have hq_eq : q = X ^ 2 + (C (-(2 * x)) * X + C (x ^ 2 + (D : ℚ) * y ^ 2)) := by
      dsimp [q]
      rw [map_neg]
      ring
    have hq_monic : q.Monic := by
      rw [hq_eq]
      apply Polynomial.monic_X_pow_add
      refine (Polynomial.degree_add_le _ _).trans_lt (max_lt ?_ ?_)
      · exact (Polynomial.degree_C_mul_X_le _).trans_lt (by decide)
      · exact Polynomial.degree_C_le.trans_lt (by decide)
    have hq_deg : q.natDegree = 2 := by
      rw [hq_eq, Polynomial.natDegree_add_eq_left_of_natDegree_lt, Polynomial.natDegree_X_pow]
      rw [Polynomial.natDegree_X_pow]
      refine (Polynomial.natDegree_add_le _ _).trans_lt (max_lt ?_ ?_)
      · have hle : (C (-(2 * x)) * X).natDegree ≤ 1 :=
          Polynomial.natDegree_mul_le.trans (by rw [Polynomial.natDegree_C, Polynomial.natDegree_X])
        omega
      · rw [Polynomial.natDegree_C]
        decide
    have hcast : ∀ r : ℚ, (algebraMap ℚ (QField D)) r = (r : QField D) := fun r =>
      map_ratCast (algebraMap ℚ (QField D)) r
    have hq_root : Polynomial.aeval (z : QField D) q = 0 := by
      simp only [q, map_add, map_sub, map_pow, map_mul, aeval_X, aeval_C, hcast]
      rw [hxy]
      have hθ := θ_sq D
      push_cast
      linear_combination (y : QField D) ^ 2 * hθ
    have hz_Q : IsIntegral ℚ (z : QField D) := hz_int.tower_top
    have hdvd : minpoly ℚ (z : QField D) ∣ q := minpoly.dvd ℚ (z : QField D) hq_root
    have hmin_monic : (minpoly ℚ (z : QField D)).Monic := minpoly.monic hz_Q
    have hmin_deg_ge : 2 ≤ (minpoly ℚ (z : QField D)).natDegree := by
      by_contra hlt
      push Not at hlt
      have hpos : 0 < (minpoly ℚ (z : QField D)).natDegree := minpoly.natDegree_pos hz_Q
      have hdeg1 : (minpoly ℚ (z : QField D)).natDegree = 1 := by omega
      let c0 : ℚ := (minpoly ℚ (z : QField D)).coeff 0
      have hlin : minpoly ℚ (z : QField D) =
          C ((minpoly ℚ (z : QField D)).coeff 1) * X + C c0 :=
        Polynomial.eq_X_add_C_of_natDegree_le_one (by omega)
      have hlc1 : (minpoly ℚ (z : QField D)).coeff 1 = 1 := by
        rw [← hdeg1]; exact hmin_monic.leadingCoeff
      rw [hlc1, map_one, one_mul] at hlin
      have hroot := minpoly.aeval ℚ (z : QField D)
      rw [hlin, map_add, aeval_X, aeval_C, hcast] at hroot
      rw [hxy] at hroot
      have hzero : ((x + c0 : ℚ) : QField D) + (y : QField D) * θ D = 0 := by
        push_cast
        linear_combination hroot
      exact hy (coords_unique D (by omega) hzero).2
    have hmin_eq : minpoly ℚ (z : QField D) = q := by
      obtain ⟨r, hr⟩ := hdvd
      have hr_ne : r ≠ 0 := by
        rintro rfl
        simp [hq_monic.ne_zero] at hr
      have hr_deg : r.natDegree = 0 := by
        have hdm := Polynomial.natDegree_mul hmin_monic.ne_zero hr_ne
        rw [← hr, hq_deg] at hdm
        omega
      have hr_lc : r.leadingCoeff = 1 := by
        have hlc := congrArg Polynomial.leadingCoeff hr
        rw [hq_monic.leadingCoeff, Polynomial.leadingCoeff_mul, hmin_monic.leadingCoeff,
          one_mul] at hlc
        exact hlc.symm
      have hr_c0 : r.coeff 0 = 1 := by
        simpa [Polynomial.leadingCoeff, hr_deg] using hr_lc
      have hr_one : r = 1 := by
        rw [Polynomial.eq_C_of_natDegree_eq_zero hr_deg, hr_c0, map_one]
      rw [hr, hr_one, mul_one]
    have hmap := minpoly.isIntegrallyClosed_eq_field_fractions' (R := ℤ) (K := ℚ) hz_int
    rw [hmin_eq] at hmap
    have hc1 := congrArg (fun p : ℚ[X] => p.coeff 1) hmap
    have hc0 := congrArg (fun p : ℚ[X] => p.coeff 0) hmap
    simp only [q, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C,
      Polynomial.coeff_map, eq_intCast] at hc1 hc0
    norm_num at hc1 hc0
    let u : ℤ := -((minpoly ℤ (z : QField D)).coeff 1)
    let n : ℤ := (minpoly ℤ (z : QField D)).coeff 0
    have hu : 2 * x = (u : ℚ) := by
      change 2 * x = (-((minpoly ℤ (z : QField D)).coeff 1) : ℤ)
      push_cast
      linarith
    have hn : x ^ 2 + (D : ℚ) * y ^ 2 = (n : ℚ) := hc0
    have h4 : (D : ℚ) * (2 * y) ^ 2 = ((4 * n - u ^ 2 : ℤ) : ℚ) := by
      push_cast
      linear_combination 4 * hn - (2 * x + (u : ℚ)) * hu
    let r : ℚ := 2 * y
    have hnum_den : (r.num : ℚ) / (r.den : ℚ) = r := Rat.num_div_den r
    have hden_pos : (0 : ℚ) < (r.den : ℚ) := Nat.cast_pos.mpr r.den_pos
    have hmul_q : ((D : ℤ) * r.num ^ 2 : ℚ) = ((4 * n - u ^ 2) * (r.den : ℤ) ^ 2 : ℚ) := by
      have h4' : (D : ℚ) * ((r.num : ℚ) / (r.den : ℚ)) ^ 2 = ((4 * n - u ^ 2 : ℤ) : ℚ) := by
        rw [hnum_den]; exact h4
      have hden_ne : (r.den : ℚ) ≠ 0 := hden_pos.ne'
      rw [div_pow, mul_div_assoc', div_eq_iff (pow_ne_zero 2 hden_ne)] at h4'
      push_cast at h4' ⊢
      linarith
    have hmul_z : (D : ℤ) * r.num ^ 2 = (4 * n - u ^ 2) * (r.den : ℤ) ^ 2 := by
      exact_mod_cast hmul_q
    have hdvd_z : ((r.den ^ 2 : ℕ) : ℤ) ∣ ((D * r.num.natAbs ^ 2 : ℕ) : ℤ) := by
      refine ⟨4 * n - u ^ 2, ?_⟩
      push_cast
      rw [sq_abs]
      linarith
    have hdvd_n : r.den ^ 2 ∣ D * r.num.natAbs ^ 2 := Int.ofNat_dvd.mp hdvd_z
    have hcop : (r.den ^ 2).Coprime (r.num.natAbs ^ 2) := (r.reduced.symm).pow 2 2
    have hden_sq_dvd : r.den ^ 2 ∣ D := hcop.dvd_of_dvd_mul_right hdvd_n
    have hden_unit : IsUnit r.den := hsq r.den (by simpa [sq] using hden_sq_dvd)
    have hden_one : r.den = 1 := Nat.isUnit_iff.mp hden_unit
    let v : ℤ := r.num
    have hv : 2 * y = (v : ℚ) := by
      change r = (r.num : ℚ)
      rw [← hnum_den, hden_one]
      simp
    have hcong_q : ((u ^ 2 + (D : ℤ) * v ^ 2 : ℤ) : ℚ) = ((4 * n : ℤ) : ℚ) := by
      push_cast
      rw [← hu, ← hv]
      nlinarith
    have hcong : u ^ 2 + (D : ℤ) * v ^ 2 = 4 * n := by exact_mod_cast hcong_q
    have hpar : (u - v) % 2 = 0 := by
      have hu2 : (u % 2) ^ 2 % 4 = u ^ 2 % 4 := by
        have h := (Int.emod_add_mul_ediv u 2).symm
        conv_rhs => rw [h]
        ring_nf
        omega
      have hv2 : (v % 2) ^ 2 % 4 = v ^ 2 % 4 := by
        have h := (Int.emod_add_mul_ediv v 2).symm
        conv_rhs => rw [h]
        ring_nf
        omega
      have hmod4 : (u ^ 2 + (D : ℤ) * v ^ 2) % 4 = 0 := by omega
      have hD4 : (D : ℤ) % 4 = 3 := by omega
      have hstep : ((u % 2) ^ 2 + 3 * (v % 2) ^ 2) % 4 = 0 := by
        have h1 : ((D : ℤ) * v ^ 2) % 4 = (3 * (v % 2) ^ 2) % 4 := by
          rw [Int.mul_emod, hD4, ← hv2]
          simp [Int.mul_emod]
        omega
      have hu_lt : 0 ≤ u % 2 ∧ u % 2 < 2 :=
        ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
      have hv_lt : 0 ≤ v % 2 ∧ v % 2 < 2 :=
        ⟨Int.emod_nonneg _ (by omega), Int.emod_lt_of_pos _ (by omega)⟩
      have heq_mod : u % 2 = v % 2 := by
        rcases (show u % 2 = 0 ∨ u % 2 = 1 by omega) with hu0 | hu1 <;>
          rcases (show v % 2 = 0 ∨ v % 2 = 1 by omega) with hv0 | hv1 <;>
          simp [*] at hstep ⊢
      omega
    let a : ℤ := (u - v) / 2
    let b : ℤ := v
    have hab : 2 * a + b = u := by dsimp [a, b]; omega
    refine ⟨a, b, NumberField.RingOfIntegers.ext ?_⟩
    rw [mkO_coe, hxy]
    have hx_eq : (a : ℚ) + (b : ℚ) / 2 = x := by
      have hab_q : (2 : ℚ) * (a : ℚ) + (b : ℚ) = (u : ℚ) := by exact_mod_cast hab
      linarith
    have hy_eq : (b : ℚ) / 2 = y := by
      dsimp [b]; linarith
    rw [hx_eq, hy_eq]

private noncomputable def formIdeal (hmod : D % 24 = 23) (a b : ℤ) : Ideal (𝓞 (QField D)) :=
  Ideal.span {(a : 𝓞 (QField D)), mkO D hmod ((b - 1) / 2) 1}

private lemma formIdeal_ne_bot (hmod : D % 24 = 23) {a : ℤ} (ha : a ≠ 0) (b : ℤ) :
    formIdeal D hmod a b ≠ ⊥ := by
  intro hbot
  have hmem : (a : 𝓞 (QField D)) ∈ formIdeal D hmod a b :=
    Ideal.subset_span (by simp)
  rw [hbot, Ideal.mem_bot] at hmem
  exact ha (Int.cast_eq_zero.mp hmem)

private noncomputable def formIdeal0 (hmod : D % 24 = 23) (a b : ℤ) (ha : a ≠ 0) :
    (Ideal (𝓞 (QField D)))⁰ :=
  ⟨formIdeal D hmod a b, mem_nonZeroDivisors_of_ne_zero (formIdeal_ne_bot D hmod ha b)⟩

private lemma ideal_eq_formClass (hD : 1 < D) (hsq : Squarefree D) (hmod : D % 24 = 23)
    (I : (Ideal (𝓞 (QField D)))⁰) :
    ∃ a b c : ℤ, ∃ h : IsForm D a b c,
      ClassGroup.mk0 I = ClassGroup.mk0 (formIdeal0 D hmod a b h.2.ne') := by
  have hI_ne : (I : Ideal (𝓞 (QField D))) ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp I.prop
  have he_ex : ∃ e : ℕ, 0 < e ∧ ((e : ℤ) : 𝓞 (QField D)) ∈ (I : Ideal (𝓞 (QField D))) := by
    obtain ⟨z, hzI, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI_ne
    obtain ⟨a, b, rfl⟩ := ringOfIntegers_surj D hD hsq hmod z
    have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_contra h0
      push Not at h0
      apply hz0
      simp [h0.1, h0.2, mkO]
    have hprod : ((a ^ 2 + a * b + (mNat D : ℤ) * b ^ 2 : ℤ) : 𝓞 (QField D)) ∈
        (I : Ideal (𝓞 (QField D))) := by
      rw [← mkO_mul_conj D hmod a b]
      exact Ideal.mul_mem_right _ _ hzI
    have hm : 4 * (mNat D : ℤ) = (D : ℤ) + 1 := by exact_mod_cast four_mul_mNat hmod
    have hpos_z : 0 < a ^ 2 + a * b + (mNat D : ℤ) * b ^ 2 := by
      have h4 : 4 * (a ^ 2 + a * b + (mNat D : ℤ) * b ^ 2) =
          (2 * a + b) ^ 2 + (D : ℤ) * b ^ 2 := by nlinarith
      have hD0 : (0 : ℤ) < D := by exact_mod_cast (by omega : 0 < D)
      rcases hab with ha | hb
      · by_cases hb0 : b = 0
        · subst hb0; nlinarith [sq_pos_of_ne_zero ha]
        · nlinarith [sq_nonneg (2 * a + b), sq_pos_of_ne_zero hb0]
      · nlinarith [sq_nonneg (2 * a + b), sq_pos_of_ne_zero hb]
    refine ⟨(a ^ 2 + a * b + (mNat D : ℤ) * b ^ 2).toNat, by omega, ?_⟩
    rwa [Int.toNat_of_nonneg (by omega)]
  have hd_ex : ∃ d : ℕ, 0 < d ∧ ∃ r : ℤ, mkO D hmod r d ∈ (I : Ideal (𝓞 (QField D))) := by
    obtain ⟨e, he_pos, he_mem⟩ := he_ex
    refine ⟨e, he_pos, 0, ?_⟩
    have h1 : mkO D hmod 0 e = ((e : ℤ) : 𝓞 (QField D)) * ω D hmod := by
      simp [mkO]
    rw [h1]
    exact Ideal.mul_mem_right _ _ he_mem
  classical
  let e : ℕ := Nat.find he_ex
  have he_spec : 0 < e ∧ ((e : ℤ) : 𝓞 (QField D)) ∈ (I : Ideal (𝓞 (QField D))) :=
    Nat.find_spec he_ex
  let d : ℕ := Nat.find hd_ex
  have hd_spec : 0 < d ∧ ∃ r : ℤ, mkO D hmod r d ∈ (I : Ideal (𝓞 (QField D))) :=
    Nat.find_spec hd_ex
  obtain ⟨r, hr_mem⟩ := hd_spec.2
  have hd_dvd : ∀ x y : ℤ, mkO D hmod x y ∈ (I : Ideal (𝓞 (QField D))) → (d : ℤ) ∣ y := by
    intro x y hmem
    let q := y / (d : ℤ)
    let rem := y % (d : ℤ)
    have hrem_nn : 0 ≤ rem := Int.emod_nonneg y (by omega)
    have hrem_lt : rem < (d : ℤ) := Int.emod_lt_of_pos y (by omega)
    have hdiv : y = (d : ℤ) * q + rem := (Int.mul_ediv_add_emod y (d : ℤ)).symm
    have hsub : mkO D hmod (x - q * r) rem ∈ (I : Ideal (𝓞 (QField D))) := by
      have h1 : mkO D hmod (x - q * r) rem =
          mkO D hmod x y - (q : 𝓞 (QField D)) * mkO D hmod r d := by
        rw [mkO_int_mul, mkO_sub]
        congr 1; linarith
      rw [h1]
      exact Ideal.sub_mem _ hmem (Ideal.mul_mem_left _ _ hr_mem)
    have hrem0 : rem = 0 := by
      by_contra hne
      have hpos : 0 < rem.toNat := by omega
      have hlt : rem.toNat < d := by omega
      have hcontra := Nat.find_min hd_ex hlt
      exact hcontra ⟨hpos, x - q * r, by rwa [Int.toNat_of_nonneg hrem_nn]⟩
    exact ⟨q, by omega⟩
  have he_dvd : ∀ x : ℤ, ((x : ℤ) : 𝓞 (QField D)) ∈ (I : Ideal (𝓞 (QField D))) → (e : ℤ) ∣ x := by
    intro x hmem
    let q := x / (e : ℤ)
    let rem := x % (e : ℤ)
    have hrem_nn : 0 ≤ rem := Int.emod_nonneg x (by omega)
    have hrem_lt : rem < (e : ℤ) := Int.emod_lt_of_pos x (by omega)
    have hdiv : x = (e : ℤ) * q + rem := (Int.mul_ediv_add_emod x (e : ℤ)).symm
    have hsub : ((rem : ℤ) : 𝓞 (QField D)) ∈ (I : Ideal (𝓞 (QField D))) := by
      have h1 : ((rem : ℤ) : 𝓞 (QField D)) =
          ((x : ℤ) : 𝓞 (QField D)) - (q : 𝓞 (QField D)) * ((e : ℤ) : 𝓞 (QField D)) := by
        have hrem_eq : rem = x - q * (e : ℤ) := by linarith
        rw [hrem_eq]; push_cast; ring
      rw [h1]
      exact Ideal.sub_mem _ hmem (Ideal.mul_mem_left _ _ he_spec.2)
    have hrem0 : rem = 0 := by
      by_contra hne
      have hpos : 0 < rem.toNat := by omega
      have hlt : rem.toNat < e := by omega
      have hcontra := Nat.find_min he_ex hlt
      exact hcontra ⟨hpos, by rwa [Int.toNat_of_nonneg hrem_nn]⟩
    exact ⟨q, by omega⟩
  have hd_dvd_e : (d : ℤ) ∣ (e : ℤ) := by
    apply hd_dvd 0 e
    have h1 : mkO D hmod 0 e = ((e : ℤ) : 𝓞 (QField D)) * ω D hmod := by simp [mkO]
    rw [h1]
    exact Ideal.mul_mem_right _ _ he_spec.2
  have hd_dvd_r : (d : ℤ) ∣ r := by
    have h1 : (d : ℤ) ∣ (r + d) := by
      apply hd_dvd (-(mNat D : ℤ) * d) (r + d)
      rw [← mkO_mul_ω]
      exact Ideal.mul_mem_right _ _ hr_mem
    obtain ⟨k, hk⟩ := h1
    exact ⟨k - 1, by linarith⟩
  obtain ⟨a₀, ha₀_eq⟩ := hd_dvd_e
  obtain ⟨r₀, hr₀_eq⟩ := hd_dvd_r
  have ha₀_pos : 0 < a₀ := by nlinarith [he_spec.1, hd_spec.1]
  have hprod_mem : (((d : ℤ) * (r₀ ^ 2 + r₀ + (mNat D : ℤ)) : ℤ) : 𝓞 (QField D)) ∈
      (I : Ideal (𝓞 (QField D))) := by
    have h1 : (((d : ℤ) * (r₀ ^ 2 + r₀ + (mNat D : ℤ)) : ℤ) : 𝓞 (QField D)) =
        mkO D hmod r d * mkO D hmod (r₀ + 1) (-1) := by
      have hfactor : mkO D hmod r d = ((d : ℤ) : 𝓞 (QField D)) * mkO D hmod r₀ 1 := by
        rw [mkO_int_mul, hr₀_eq, mul_one]
      rw [hfactor, mul_assoc, mkO_mul_conj]
      push_cast
      ring
    rw [h1]
    exact Ideal.mul_mem_right _ _ hr_mem
  obtain ⟨c₀, hc₀_eq⟩ := he_dvd _ hprod_mem
  have hac_eq : r₀ ^ 2 + r₀ + (mNat D : ℤ) = a₀ * c₀ := by
    have hd_pos : (0 : ℤ) < d := by exact_mod_cast hd_spec.1
    rw [ha₀_eq] at hc₀_eq
    nlinarith
  let b₀ : ℤ := 2 * r₀ + 1
  have hform : IsForm D a₀ b₀ c₀ := by
    refine ⟨?_, ha₀_pos⟩
    have hm : 4 * (mNat D : ℤ) = (D : ℤ) + 1 := by exact_mod_cast four_mul_mNat hmod
    dsimp [b₀]
    nlinarith
  have hI_eq : (I : Ideal (𝓞 (QField D))) =
      Ideal.span {((d : ℤ) : 𝓞 (QField D))} * formIdeal D hmod a₀ b₀ := by
    have hr0_div : (b₀ - 1) / 2 = r₀ := by dsimp [b₀]; omega
    unfold formIdeal
    rw [hr0_div, span_singleton_mul_pair]
    apply le_antisymm
    · intro z hz
      obtain ⟨x, y, rfl⟩ := ringOfIntegers_surj D hD hsq hmod z
      obtain ⟨q, hq⟩ := hd_dvd x y hz
      have hx_mem : ((x - q * r : ℤ) : 𝓞 (QField D)) ∈ (I : Ideal (𝓞 (QField D))) := by
        have h1 : ((x - q * r : ℤ) : 𝓞 (QField D)) =
            mkO D hmod x y - (q : 𝓞 (QField D)) * mkO D hmod r d := by
          rw [mkO_int_mul, mkO_sub, ← mkO_zero_right D hmod]
          congr 1; linarith
        rw [h1]
        exact Ideal.sub_mem _ hz (Ideal.mul_mem_left _ _ hr_mem)
      obtain ⟨p, hp⟩ := he_dvd _ hx_mem
      have hx_eq : x = p * ((d : ℤ) * a₀) + q * ((d : ℤ) * r₀) := by
        rw [ha₀_eq, hr₀_eq] at hp
        linear_combination hp
      have hy_eq : y = q * (d : ℤ) := by linarith
      have hz_decomp : mkO D hmod x y =
          (p : 𝓞 (QField D)) * (((d : ℤ) : 𝓞 (QField D)) * (a₀ : 𝓞 (QField D))) +
          (q : 𝓞 (QField D)) * (((d : ℤ) : 𝓞 (QField D)) * mkO D hmod r₀ 1) := by
        rw [hx_eq, hy_eq]
        unfold mkO
        push_cast
        ring
      rw [hz_decomp]
      exact Ideal.add_mem _
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    · rw [Ideal.span_le]
      rintro z (rfl | rfl)
      · have h1 : ((d : ℤ) : 𝓞 (QField D)) * (a₀ : 𝓞 (QField D)) =
            ((e : ℤ) : 𝓞 (QField D)) := by
          exact_mod_cast ha₀_eq.symm
        rw [h1]; exact he_spec.2
      · have h1 : ((d : ℤ) : 𝓞 (QField D)) * mkO D hmod r₀ 1 = mkO D hmod r d := by
          rw [mkO_int_mul, hr₀_eq, mul_one]
        rw [h1]; exact hr_mem
  refine ⟨a₀, b₀, c₀, hform, ?_⟩
  rw [ClassGroup.mk0_eq_mk0_iff]
  refine ⟨1, ((d : ℤ) : 𝓞 (QField D)), one_ne_zero, ?_, ?_⟩
  · exact Int.cast_ne_zero.mpr (by omega)
  · simp [Ideal.span_singleton_one, hI_eq, formIdeal0]

private lemma translate_form (hmod : D % 24 = 23) {a b c : ℤ} (h : IsForm D a b c) (k : ℤ) :
    IsForm D a (b + 2 * k * a) (c + k * b + k ^ 2 * a) ∧
      formIdeal D hmod a (b + 2 * k * a) = formIdeal D hmod a b := by
  have hform : IsForm D a (b + 2 * k * a) (c + k * b + k ^ 2 * a) :=
    ⟨by linear_combination h.1, h.2⟩
  refine ⟨hform, ?_⟩
  have hshift : (b + 2 * k * a - 1) / 2 = (b - 1) / 2 + k * a := by
    rw [show b + 2 * k * a - 1 = (b - 1) + 2 * (k * a) by ring,
      Int.add_mul_ediv_left _ _ (by decide)]
  unfold formIdeal
  rw [hshift]
  have hgen : mkO D hmod ((b - 1) / 2 + k * a) 1 =
      mkO D hmod ((b - 1) / 2) 1 + (k : 𝓞 (QField D)) * (a : 𝓞 (QField D)) := by
    unfold mkO
    push_cast
    ring
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro z (rfl | rfl)
    · exact Ideal.subset_span (by simp)
    · rw [hgen]
      exact Ideal.add_mem _ (Ideal.subset_span (by simp))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
  · rw [Ideal.span_le]
    rintro z (rfl | rfl)
    · exact Ideal.subset_span (by simp)
    · have hgen' : mkO D hmod ((b - 1) / 2) 1 =
          mkO D hmod ((b - 1) / 2 + k * a) 1 - (k : 𝓞 (QField D)) * (a : 𝓞 (QField D)) := by
        linear_combination -hgen
      rw [hgen']
      exact Ideal.sub_mem _ (Ideal.subset_span (by simp))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

private lemma invert_form (hD : 1 < D) (hmod : D % 24 = 23) {a b c : ℤ} (h : IsForm D a b c) :
    ∃ h' : IsForm D c (-b) a,
      ClassGroup.mk0 (formIdeal0 D hmod a b h.2.ne') =
        ClassGroup.mk0 (formIdeal0 D hmod c (-b) h'.2.ne') := by
  have hc : 0 < c := isForm_c_pos hD h
  have h' : IsForm D c (-b) a := ⟨by linear_combination h.1, hc⟩
  refine ⟨h', ?_⟩
  have hb := isForm_b_odd hmod h
  have hr_eq := isForm_r_eq hmod h
  let r := (b - 1) / 2
  have hr_neg : (-b - 1) / 2 = -(r + 1) := by dsimp [r]; omega
  let α := mkO D hmod r 1
  let αbar := mkO D hmod (r + 1) (-1)
  have hαbar_ne : αbar ≠ 0 := by
    intro h0
    have h0' : mkO D hmod (r + 1) (-1) = mkO D hmod 0 0 := by simpa [αbar, mkO] using h0
    have := (mkO_inj D (by omega) hmod h0').2
    omega
  have ha_ne : (a : 𝓞 (QField D)) ≠ 0 := Int.cast_ne_zero.mpr h.2.ne'
  have hprod : αbar * α = (a : 𝓞 (QField D)) * (c : 𝓞 (QField D)) := by
    rw [mul_comm]
    dsimp [α, αbar]
    rw [mkO_mul_conj]
    have : r ^ 2 + r * 1 + (mNat D : ℤ) * 1 ^ 2 = a * c := by
      dsimp [r]; linarith
    rw [this]
    push_cast
    rfl
  have hneg : mkO D hmod (-(r + 1)) 1 = -αbar := by
    dsimp [αbar]
    rw [mkO_neg]
    congr 1
  rw [ClassGroup.mk0_eq_mk0_iff]
  refine ⟨αbar, (a : 𝓞 (QField D)), hαbar_ne, ha_ne, ?_⟩
  change Ideal.span {αbar} * formIdeal D hmod a b =
    Ideal.span {(a : 𝓞 (QField D))} * formIdeal D hmod c (-b)
  unfold formIdeal
  rw [hr_neg, hneg]
  change Ideal.span {αbar} * Ideal.span {(a : 𝓞 (QField D)), α} =
    Ideal.span {(a : 𝓞 (QField D))} * Ideal.span {(c : 𝓞 (QField D)), -αbar}
  rw [span_singleton_mul_pair, span_singleton_mul_pair, hprod]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro z (rfl | rfl)
    · have h1 : αbar * (a : 𝓞 (QField D)) = -((a : 𝓞 (QField D)) * -αbar) := by ring
      rw [h1]
      exact Submodule.neg_mem _ (Ideal.subset_span (by simp))
    · exact Ideal.subset_span (by simp)
  · rw [Ideal.span_le]
    rintro z (rfl | rfl)
    · exact Ideal.subset_span (by simp)
    · have h1 : (a : 𝓞 (QField D)) * -αbar = -(αbar * (a : 𝓞 (QField D))) := by ring
      rw [h1]
      exact Submodule.neg_mem _ (Ideal.subset_span (by simp))

private lemma exists_reduced_eq_class (hD : 1 < D) (hsq : Squarefree D) (hmod : D % 24 = 23) :
    ∀ (n : ℕ) (a b c : ℤ) (h : IsForm D a b c), a.natAbs = n →
      ∃ a' b' c' : ℤ, PartitionParity.IsReducedForm D a' b' c' ∧
        ∃ ha' : a' ≠ 0,
          ClassGroup.mk0 (formIdeal0 D hmod a' b' ha') =
            ClassGroup.mk0 (formIdeal0 D hmod a b h.2.ne') := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a b c h han
    have ha : 0 < a := h.2
    let q := (b + a - 1) / (2 * a)
    let rem := (b + a - 1) % (2 * a)
    have hrem_nn : 0 ≤ rem := Int.emod_nonneg _ (by omega)
    have hrem_lt : rem < 2 * a := Int.emod_lt_of_pos _ (by omega)
    have hdiv : b + a - 1 = (2 * a) * q + rem := (Int.mul_ediv_add_emod _ _).symm
    let b₁ := b + 2 * (-q) * a
    let c₁ := c + (-q) * b + (-q) ^ 2 * a
    obtain ⟨h₁, hideal₁⟩ := translate_form D hmod h (-q)
    have hcls₁ : ClassGroup.mk0 (formIdeal0 D hmod a b₁ h₁.2.ne') =
        ClassGroup.mk0 (formIdeal0 D hmod a b h.2.ne') := by
      congr 1
      exact Subtype.ext hideal₁
    have hb₁_lo : -a < b₁ := by dsimp [b₁]; linarith
    have hb₁_hi : b₁ ≤ a := by dsimp [b₁]; linarith
    have habs_b₁ : |b₁| ≤ a := abs_le.mpr ⟨by omega, hb₁_hi⟩
    by_cases hca : c₁ < a
    · obtain ⟨hinv, hcls_inv⟩ := invert_form D hD hmod h₁
      have hc₁_pos : 0 < c₁ := hinv.2
      have hlt : c₁.natAbs < n := by omega
      obtain ⟨a', b', c', hred, ha', hcls'⟩ := ih c₁.natAbs hlt c₁ (-b₁) a hinv rfl
      exact ⟨a', b', c', hred, ha', hcls'.trans (hcls_inv.symm.trans hcls₁)⟩
    · by_cases heq_neg : a = c₁ ∧ b₁ < 0
      · obtain ⟨hac, hbneg⟩ := heq_neg
        obtain ⟨hinv, hcls_inv⟩ := invert_form D hD hmod h₁
        refine ⟨c₁, -b₁, a, ?_, hinv.2.ne', hcls_inv.symm.trans hcls₁⟩
        refine ⟨hinv.1, ?_, by omega, isForm_gcd_one hsq hinv.1, ?_⟩
        · rw [abs_neg]; omega
        · intro _; omega
      · refine ⟨a, b₁, c₁, ?_, h₁.2.ne', hcls₁⟩
        refine ⟨h₁.1, habs_b₁, by omega, isForm_gcd_one hsq h₁.1, ?_⟩
        rintro (heq | heq)
        · have : b₁ = a ∨ b₁ = -a := abs_eq (by omega) |>.mp heq
          omega
        · by_contra hneg
          exact heq_neg ⟨heq, by omega⟩

private theorem classNumber_le_ncard_reduced (hD : 1 < D) (hsq : Squarefree D) (hmod : D % 24 = 23) :
    NumberField.classNumber (QField D) ≤
      {p : ℤ × ℤ × ℤ | PartitionParity.IsReducedForm D p.1 p.2.1 p.2.2}.ncard := by
  let S : Set (ℤ × ℤ × ℤ) := {p | PartitionParity.IsReducedForm D p.1 p.2.1 p.2.2}
  have : Finite S := (reduced_finite hD).to_subtype
  let Φ : S → ClassGroup (𝓞 (QField D)) := fun p =>
    ClassGroup.mk0 (formIdeal0 D hmod p.1.1 p.1.2.1 (reduced_a_pos hD p.2).ne')
  have hΦ : Function.Surjective Φ := by
    intro C
    obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective C
    obtain ⟨a₀, b₀, c₀, hform, hcls₀⟩ := ideal_eq_formClass D hD hsq hmod I
    obtain ⟨a', b', c', hred, ha', hcls'⟩ :=
      exists_reduced_eq_class D hD hsq hmod a₀.natAbs a₀ b₀ c₀ hform rfl
    refine ⟨⟨(a', b', c'), hred⟩, ?_⟩
    dsimp [Φ]
    rw [hcls₀, ← hcls']
  calc
    NumberField.classNumber (QField D) = Fintype.card (ClassGroup (𝓞 (QField D))) := rfl
    _ = Nat.card (ClassGroup (𝓞 (QField D))) := Nat.card_eq_fintype_card.symm
    _ ≤ Nat.card S := Nat.card_le_card_of_surjective Φ hΦ
    _ = S.ncard := Nat.card_coe_set_eq S

end QuadField

end OMA.PartitionParity_zheng_odd_R2_H2

theorem OMA.solution : OMA.R_PartitionParity_zheng_odd_R2.H2 := by
  intro D hD hsq hmod
  exact OMA.PartitionParity_zheng_odd_R2_H2.classNumber_le_ncard_reduced (hf := _) D hD hsq hmod
