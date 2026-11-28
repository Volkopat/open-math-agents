import OMAStatements.S_oeis_a259440
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Analysis.Complex.Polynomial.Basic

-- Problem: A259440: Field discriminant of n-th composite, f(f(...f(r)...)), where r = 2 and f(x) = [x,x,x, ...] (continued fraction).
-- Upstream: statements/oeis-a259440.lean (declaration OMA.S_oeis_a259440.main)
-- Credit: @Raimo33 (the owner of the agent is credited as the solver)

namespace OMA.ProofA259440

open Polynomial IntermediateField OMA.S_oeis_a259440

private theorem discr_pow_finrank_dvd_discr (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    NumberField.discr K ^ Module.finrank K L ∣ NumberField.discr L := by
  rw [← Int.dvd_natAbs,
    NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K
      (NumberField.RingOfIntegers K) L (NumberField.RingOfIntegers L),
    Nat.cast_mul, Nat.cast_pow, ← Int.mul_sign_self, mul_pow, ← mul_assoc,
    mul_comm _ (NumberField.discr K ^ _), mul_assoc]
  exact Int.dvd_mul_right _ _

private lemma point_pos (n : ℕ) : 0 < (point n).val := by
  induction n with
  | zero =>
    change 0 < algebraMap ℚ ℝ 2
    rw [map_ofNat]
    norm_num
  | succ n ih =>
    change 0 < ((point n).val + Real.sqrt ((point n).val ^ 2 + 4)) * algebraMap ℚ ℝ (2⁻¹ : ℚ)
    rw [map_inv₀, map_ofNat]
    positivity

private lemma point_sq_sub (n : ℕ) :
    (point (n + 1)).val ^ 2 - (point n).val * (point (n + 1)).val - 1 = 0 := by
  have hx : (point (n + 1)).val = ((point n).val + Real.sqrt ((point n).val ^ 2 + 4)) / 2 := by
    change ((point n).val + Real.sqrt ((point n).val ^ 2 + 4)) * algebraMap ℚ ℝ (2⁻¹ : ℚ) = _
    simp [div_eq_mul_inv]
  have hsq : Real.sqrt ((point n).val ^ 2 + 4) ^ 2 = (point n).val ^ 2 + 4 :=
    Real.sq_sqrt (by positivity)
  rw [hx]
  nlinarith [hsq]

private lemma point_eq_sub_inv (n : ℕ) :
    (point n).val = (point (n + 1)).val - (point (n + 1)).val⁻¹ := by
  have hpos : (point (n + 1)).val ≠ 0 := (point_pos (n + 1)).ne'
  have hsq := point_sq_sub n
  field_simp [hpos]
  linarith

private lemma K_le_succ (n : ℕ) : K n ≤ K (n + 1) := by
  rw [K, IntermediateField.adjoin_le_iff]
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  rw [hx, point_eq_sub_inv n]
  have hmem : (point (n + 1)).val ∈ K (n + 1) :=
    IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)
  exact (K (n + 1)).sub_mem hmem ((K (n + 1)).inv_mem hmem)

private noncomputable def P : ℕ → ℤ[X]
  | 0 => X - C 2
  | n + 1 =>
      ∑ k ∈ Finset.range (2 ^ n + 1),
        C ((P n).coeff k) * X ^ (2 ^ n - k) * (X ^ 2 - 1) ^ k

private lemma monic_X_sq_sub_one : ((X ^ 2 - 1 : ℤ[X])).Monic := by
  have h : (X ^ 2 - 1 : ℤ[X]) = X ^ 2 - C 1 := by simp
  rw [h]
  exact Polynomial.monic_X_pow_sub_C 1 (by decide : 2 ≠ 0)

private lemma natDegree_X_sq_sub_one : ((X ^ 2 - 1 : ℤ[X])).natDegree = 2 := by
  have h : (X ^ 2 - 1 : ℤ[X]) = X ^ 2 - C 1 := by simp
  rw [h]
  exact Polynomial.natDegree_X_pow_sub_C

private lemma P_natDegree_and_monic (n : ℕ) :
    (P n).natDegree = 2 ^ n ∧ (P n).Monic := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [P, Polynomial.natDegree_X_sub_C]
      rfl
    · exact Polynomial.monic_X_sub_C 2
  | succ n ih =>
    rcases ih with ⟨hdeg, hmon⟩
    rw [P, Finset.sum_range_succ]
    have hlead : (P n).coeff (2 ^ n) = 1 := by
      rw [← hdeg]
      exact hmon.leadingCoeff
    have htop_eq : C ((P n).coeff (2 ^ n)) * X ^ (2 ^ n - 2 ^ n) * (X ^ 2 - 1) ^ (2 ^ n) =
        (X ^ 2 - 1 : ℤ[X]) ^ (2 ^ n) := by
      simp [hlead]
    have htop_mon : ((X ^ 2 - 1 : ℤ[X]) ^ (2 ^ n)).Monic :=
      monic_X_sq_sub_one.pow (2 ^ n)
    have htop_deg : ((X ^ 2 - 1 : ℤ[X]) ^ (2 ^ n)).natDegree = 2 ^ (n + 1) := by
      rw [monic_X_sq_sub_one.natDegree_pow, natDegree_X_sq_sub_one]
      ring
    have hrest_le : (∑ k ∈ Finset.range (2 ^ n),
        C ((P n).coeff k) * X ^ (2 ^ n - k) * (X ^ 2 - 1) ^ k).natDegree ≤ 2 ^ (n + 1) - 1 := by
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
      rw [Finset.mem_range] at hk
      have h1 : (C ((P n).coeff k) * X ^ (2 ^ n - k) * (X ^ 2 - 1) ^ k).natDegree ≤
          (C ((P n).coeff k) * X ^ (2 ^ n - k)).natDegree + ((X ^ 2 - 1 : ℤ[X]) ^ k).natDegree :=
        Polynomial.natDegree_mul_le
      have h2 : (C ((P n).coeff k) * X ^ (2 ^ n - k)).natDegree ≤
          (C ((P n).coeff k)).natDegree + (X ^ (2 ^ n - k) : ℤ[X]).natDegree :=
        Polynomial.natDegree_mul_le
      have h3 : ((X ^ 2 - 1 : ℤ[X]) ^ k).natDegree = 2 * k := by
        rw [monic_X_sq_sub_one.natDegree_pow, natDegree_X_sq_sub_one]
        ring
      simp only [Polynomial.natDegree_C, Polynomial.natDegree_X_pow, zero_add] at h2
      have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
      omega
    have hrest_lt : (∑ k ∈ Finset.range (2 ^ n),
        C ((P n).coeff k) * X ^ (2 ^ n - k) * (X ^ 2 - 1) ^ k).natDegree <
        ((X ^ 2 - 1 : ℤ[X]) ^ (2 ^ n)).natDegree := by
      rw [htop_deg]
      have hpos : 0 < 2 ^ (n + 1) := by positivity
      omega
    rw [htop_eq]
    refine ⟨?_, ?_⟩
    · rw [Polynomial.natDegree_add_eq_right_of_natDegree_lt hrest_lt, htop_deg]
    · exact htop_mon.add_of_right (Polynomial.degree_lt_degree hrest_lt)

private lemma aeval_P_succ {R : Type*} [CommRing R] (n : ℕ) {u v : R} (huv : u * v = 1) :
    Polynomial.aeval u (P (n + 1)) = u ^ (2 ^ n) * Polynomial.aeval (u - v) (P n) := by
  rw [P, map_sum]
  have hterm : ∀ k ∈ Finset.range (2 ^ n + 1),
      Polynomial.aeval u (C ((P n).coeff k) * X ^ (2 ^ n - k) * (X ^ 2 - 1) ^ k) =
        u ^ (2 ^ n) * (((P n).coeff k : R) * (u - v) ^ k) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hkle : k ≤ 2 ^ n := by omega
    have hsub : u ^ 2 - 1 = u * (u - v) := by
      calc u ^ 2 - 1 = u ^ 2 - u * v := by rw [huv]
        _ = u * (u - v) := by ring
    simp only [map_mul, map_pow, map_sub, map_one, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one,
      zsmul_eq_mul, mul_one]
    rw [hsub, mul_pow]
    calc ((P n).coeff k : R) * u ^ (2 ^ n - k) * (u ^ k * (u - v) ^ k)
        = (u ^ (2 ^ n - k) * u ^ k) * (((P n).coeff k : R) * (u - v) ^ k) := by ring
      _ = u ^ (2 ^ n) * (((P n).coeff k : R) * (u - v) ^ k) := by
          rw [← pow_add, Nat.sub_add_cancel hkle]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  rw [Polynomial.aeval_eq_sum_range' (lt_of_eq_of_lt (P_natDegree_and_monic n).1 (Nat.lt_succ_self _))]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Algebra.smul_def]

private lemma aeval_P_point (n : ℕ) : Polynomial.aeval (point n).val (P n) = 0 := by
  induction n with
  | zero =>
    change Polynomial.aeval (algebraMap ℚ ℝ 2) (X - C 2) = 0
    simp [map_ofNat]
  | succ n ih =>
    have hpos : (point (n + 1)).val ≠ 0 := (point_pos (n + 1)).ne'
    rw [aeval_P_succ n (mul_inv_cancel₀ hpos), ← point_eq_sub_inv n, ih, mul_zero]

private def twoI : GaussianInt := ⟨0, 2⟩

private lemma twoI_sq_sub_one_sub :
    twoI ^ 2 - 1 - twoI * (-twoI) = 3 * (-3 : GaussianInt) := by
  decide

private lemma three_dvd_aeval_twoI_sub (n : ℕ) :
    (3 : GaussianInt) ∣
      Polynomial.aeval twoI (P (n + 1)) - twoI ^ (2 ^ n) * Polynomial.aeval (-twoI) (P n) := by
  rw [P, map_sum]
  rw [Polynomial.aeval_eq_sum_range' (lt_of_eq_of_lt (P_natDegree_and_monic n).1 (Nat.lt_succ_self _))]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro k hk
  rw [Finset.mem_range] at hk
  have hkle : k ≤ 2 ^ n := by omega
  simp only [map_mul, map_pow, map_sub, map_one, map_intCast, aeval_X, Algebra.smul_def, eq_intCast]
  have hpow_eq : twoI ^ (2 ^ n) * (((P n).coeff k : GaussianInt) * (-twoI) ^ k) =
      ((P n).coeff k : GaussianInt) * twoI ^ (2 ^ n - k) * (twoI * (-twoI)) ^ k := by
    rw [mul_pow]
    calc twoI ^ (2 ^ n) * (((P n).coeff k : GaussianInt) * (-twoI) ^ k)
        = ((P n).coeff k : GaussianInt) * (twoI ^ (2 ^ n - k) * twoI ^ k) * (-twoI) ^ k := by
            rw [← pow_add, Nat.sub_add_cancel hkle]; ring
      _ = ((P n).coeff k : GaussianInt) * twoI ^ (2 ^ n - k) * (twoI ^ k * (-twoI) ^ k) := by ring
  rw [hpow_eq, ← mul_sub]
  apply dvd_mul_of_dvd_right
  have hdvd : (3 : GaussianInt) ∣ (twoI ^ 2 - 1) - (twoI * (-twoI)) :=
    ⟨-3, twoI_sq_sub_one_sub⟩
  exact dvd_trans hdvd (sub_dvd_pow_sub_pow _ _ k)

private lemma star_intCast_gaussianInt (a : ℤ) : star (a : GaussianInt) = (a : GaussianInt) := by
  ext <;> simp

private lemma aeval_neg_twoI_eq_star (p : ℤ[X]) :
    Polynomial.aeval (-twoI) p = star (Polynomial.aeval twoI p) := by
  have hneg : (-twoI : GaussianInt) = star twoI := by decide
  rw [hneg]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
    simp only [aeval_monomial, eq_intCast, star_mul', star_pow, star_intCast_gaussianInt]

private lemma norm_pow_gaussianInt (z : GaussianInt) (k : ℕ) : (z ^ k).norm = z.norm ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, Zsqrtd.norm_mul, ih]

private lemma four_pow_mod_three (k : ℕ) : (4 : ℤ) ^ k % 3 = 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ, Int.mul_emod, ih]
    norm_num

private lemma norm_aeval_twoI_mod_three (n : ℕ) :
    (Polynomial.aeval twoI (P n)).norm % 3 = 2 := by
  induction n with
  | zero =>
    have h : Polynomial.aeval twoI (P 0) = ⟨-2, 2⟩ := by
      simp only [P, map_sub, aeval_X, map_ofNat]
      decide
    rw [h]
    decide
  | succ n ih =>
    obtain ⟨w, hw⟩ := three_dvd_aeval_twoI_sub n
    set z1 := Polynomial.aeval twoI (P (n + 1))
    set z2 := twoI ^ (2 ^ n) * Polynomial.aeval (-twoI) (P n)
    have hz1 : z1 = z2 + 3 * w := eq_add_of_sub_eq' hw
    have hre : z1.re = z2.re + 3 * w.re := by rw [hz1]; simp
    have him : z1.im = z2.im + 3 * w.im := by rw [hz1]; simp
    have hmod_eq : z1.norm % 3 = z2.norm % 3 := by
      simp only [Zsqrtd.norm_def]
      rw [hre, him]
      have hdiff :
          ((z2.re + 3 * w.re) * (z2.re + 3 * w.re) - (-1) * (z2.im + 3 * w.im) * (z2.im + 3 * w.im)) -
          (z2.re * z2.re - (-1) * z2.im * z2.im) =
          3 * (2 * z2.re * w.re + 3 * w.re ^ 2 + 2 * z2.im * w.im + 3 * w.im ^ 2) := by ring
      omega
    rw [hmod_eq]
    have hnorm2 : z2.norm = 4 ^ (2 ^ n) * (Polynomial.aeval twoI (P n)).norm := by
      dsimp [z2]
      rw [Zsqrtd.norm_mul, norm_pow_gaussianInt, aeval_neg_twoI_eq_star, Zsqrtd.norm_conj]
      have h4 : twoI.norm = 4 := by decide
      rw [h4]
    rw [hnorm2, Int.mul_emod, four_pow_mod_three, ih]
    norm_num

private noncomputable def gToC : GaussianInt →+* ℂ :=
  Zsqrtd.lift ⟨Complex.I, by simp⟩

private lemma gToC_twoI : gToC twoI = 2 * Complex.I := by
  simp [gToC, twoI, Zsqrtd.lift_apply_apply]

private lemma gToC_mul_star (z : GaussianInt) :
    gToC z * gToC (star z) = (z.norm : ℂ) := by
  rcases z with ⟨a, b⟩
  simp only [gToC, Zsqrtd.lift_apply_apply, Zsqrtd.star_mk, Zsqrtd.norm_def]
  push_cast
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination -(b : ℂ) ^ 2 * hI

private lemma gToC_aeval (z : GaussianInt) (p : ℤ[X]) :
    gToC (Polynomial.aeval z p) = Polynomial.aeval (gToC z) p := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂]
  congr 1
  exact RingHom.ext_int _ _

private lemma norm_aeval_twoI_eq_complex (n : ℕ) :
    ((Polynomial.aeval twoI (P n)).norm : ℂ) =
      Polynomial.aeval (2 * Complex.I) (P n) * Polynomial.aeval (-(2 * Complex.I)) (P n) := by
  rw [← gToC_mul_star, ← aeval_neg_twoI_eq_star, gToC_aeval, gToC_aeval, map_neg, gToC_twoI]

private lemma not_isSquare_rat_of_mod_three_eq_two {m : ℤ} (hm : m % 3 = 2) :
    ¬ IsSquare (m : ℚ) := by
  rintro ⟨q, hq⟩
  have hmul : (m : ℚ) * (q.den : ℚ) ^ 2 = (q.num : ℚ) ^ 2 := by
    calc (m : ℚ) * (q.den : ℚ) ^ 2
        = (q * (q.den : ℚ)) ^ 2 := by rw [hq]; ring
      _ = (q.num : ℚ) ^ 2 := by rw [Rat.mul_den_eq_num]
  have hint : m * (q.den : ℤ) ^ 2 = q.num ^ 2 := by
    exact_mod_cast hmul
  have hcop : Nat.Coprime q.num.natAbs q.den := q.reduced
  have hndvd : ¬ (3 : ℤ) ∣ (q.den : ℤ) := by
    intro hd
    have h3num2 : (3 : ℤ) ∣ q.num * q.num := by
      rw [← sq, ← hint]
      exact dvd_mul_of_dvd_right (dvd_pow hd (by decide : 2 ≠ 0)) m
    have h3num : (3 : ℤ) ∣ q.num := by
      rcases Int.prime_three.dvd_or_dvd h3num2 with h | h <;> exact h
    have h3a : 3 ∣ q.num.natAbs := Int.natCast_dvd.mp h3num
    have h3b : 3 ∣ q.den := Int.natCast_dvd_natCast.mp hd
    have h3gcd : 3 ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd h3a h3b
    rw [hcop.gcd_eq_one] at h3gcd
    omega
  have hdmod : (q.den : ℤ) % 3 = 1 ∨ (q.den : ℤ) % 3 = 2 := by omega
  have hqmod : q.num % 3 = 0 ∨ q.num % 3 = 1 ∨ q.num % 3 = 2 := by omega
  have h1 : (m * (q.den : ℤ) ^ 2) % 3 = 2 := by
    rw [sq, Int.mul_emod, Int.mul_emod (q.den : ℤ), hm]
    rcases hdmod with h | h <;> rw [h] <;> norm_num
  have h2 : (q.num ^ 2) % 3 = 0 ∨ (q.num ^ 2) % 3 = 1 := by
    rw [sq, Int.mul_emod]
    rcases hqmod with h | h | h <;> rw [h] <;> norm_num
  rw [hint] at h1
  omega

private noncomputable def genK (n : ℕ) : K n :=
  ⟨(point n).val, IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩

private lemma norm_gen_sq_add_four (n : ℕ)
    (hmin : minpoly ℚ (point n).val = (P n).map (Int.castRingHom ℚ)) :
    Algebra.norm ℚ ((genK n) ^ 2 + 4) =
      ((Polynomial.aeval twoI (P n)).norm : ℚ) := by
  apply Rat.cast_injective (α := ℂ)
  change algebraMap ℚ ℂ (Algebra.norm ℚ ((genK n) ^ 2 + 4)) =
    ((Polynomial.aeval twoI (P n)).norm : ℂ)
  rw [Algebra.norm_eq_prod_embeddings ℚ ℂ, norm_aeval_twoI_eq_complex n]
  let pb : PowerBasis ℚ (K n) := IntermediateField.adjoin.powerBasis (point n).property
  have hpb_gen : pb.gen = genK n := by
    apply Subtype.ext
    exact congrArg Subtype.val (IntermediateField.adjoin.powerBasis_gen (point n).property)
  have hmin_pb : minpoly ℚ pb.gen = (P n).map (Int.castRingHom ℚ) := by
    have h1 := minpoly.algHom_eq (K n).val (K n).val.injective pb.gen
    have h2 : (K n).val pb.gen = (point n).val := by rw [hpb_gen]; rfl
    rw [h2] at h1
    exact h1.symm.trans hmin
  have hmapC : (minpoly ℚ pb.gen).map (algebraMap ℚ ℂ) = (P n).map (Int.castRingHom ℂ) := by
    rw [hmin_pb, Polynomial.map_map]
    congr 1
  have hP_monC : ((P n).map (Int.castRingHom ℂ)).Monic :=
    (P_natDegree_and_monic n).2.map _
  have hsep : (minpoly ℚ pb.gen).Separable :=
    Algebra.IsSeparable.isSeparable ℚ pb.gen
  have hprod_emb :
      ∏ σ : K n →ₐ[ℚ] ℂ, σ ((genK n) ^ 2 + 4) =
        (((minpoly ℚ pb.gen).aroots ℂ).map (fun r : ℂ => r ^ 2 + 4)).prod := by
    have hfun : ∀ σ : K n →ₐ[ℚ] ℂ,
        σ ((genK n) ^ 2 + 4) = (σ pb.gen) ^ 2 + 4 := by
      intro σ
      rw [← hpb_gen, map_add, map_pow, map_ofNat]
    simp_rw [hfun]
    rw [Fintype.prod_equiv pb.liftEquiv' (fun σ => (σ pb.gen) ^ 2 + 4)
      (fun r => (r : ℂ) ^ 2 + 4) (fun σ => by simp [PowerBasis.liftEquiv'_apply_coe])]
    rw [Finset.prod_mem_multiset, Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr (Polynomial.nodup_roots (hsep.map))]
    exact fun _ => rfl
  rw [hprod_emb]
  have hroots_eq : (minpoly ℚ pb.gen).aroots ℂ = ((P n).map (Int.castRingHom ℂ)).roots := by
    rw [Polynomial.aroots_def, hmapC]
  rw [hroots_eq]
  have hsplit := IsAlgClosed.splits ((P n).map (Int.castRingHom ℂ))
  have hfactor : (P n).map (Int.castRingHom ℂ) =
      (((P n).map (Int.castRingHom ℂ)).roots.map (fun r => X - C r)).prod := by
    have hcard := Polynomial.Splits.natDegree_eq_card_roots hsplit
    exact (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hP_monC hcard.symm).symm
  have heval : ∀ z : ℂ, Polynomial.aeval z (P n) =
      (((P n).map (Int.castRingHom ℂ)).roots.map (fun r => z - r)).prod := by
    intro z
    rw [← Polynomial.eval_map_algebraMap]
    change Polynomial.eval z ((P n).map (Int.castRingHom ℂ)) = _
    conv_lhs => rw [hfactor]
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    congr 1
    ext r
    simp
  rw [heval (2 * Complex.I), heval (-(2 * Complex.I)), ← Multiset.prod_map_mul]
  congr 1
  apply Multiset.map_congr rfl
  intro r _
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination 4 * hI

private noncomputable def Lstep (n : ℕ) : IntermediateField (K n) ℝ :=
  IntermediateField.adjoin (K n) {(point (n + 1)).val}

private lemma Lstep_restrict_eq (n : ℕ) : (Lstep n).restrictScalars ℚ = K (n + 1) := by
  apply le_antisymm
  · let Kn1_over : IntermediateField (K n) ℝ :=
      { (K (n + 1)).toSubfield with
        algebraMap_mem' := fun x => K_le_succ n x.property }
    have hsub : Lstep n ≤ Kn1_over := by
      rw [Lstep, IntermediateField.adjoin_le_iff]
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      rw [hx]
      exact IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)
    intro x hx
    exact hsub hx
  · rw [K, IntermediateField.adjoin_le_iff]
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    rw [hx]
    exact IntermediateField.subset_adjoin (K n) _ (Set.mem_singleton _)

private noncomputable def equivSucc (n : ℕ) : Lstep n ≃ₐ[ℚ] K (n + 1) :=
  IntermediateField.equivOfEq (Lstep_restrict_eq n)

private noncomputable instance (n : ℕ) : NumberField (Lstep n) where
  to_charZero := inferInstance
  to_finiteDimensional := (equivSucc n).symm.toLinearEquiv.finiteDimensional

private lemma finrank_and_minpoly (n : ℕ) :
    Module.finrank ℚ (K n) = 2 ^ n ∧
      minpoly ℚ (point n).val = (P n).map (Int.castRingHom ℚ) := by
  induction n with
  | zero =>
    have hval : (point 0).val = algebraMap ℚ ℝ 2 := rfl
    have hmin : minpoly ℚ (point 0).val = (P 0).map (Int.castRingHom ℚ) := by
      rw [hval, minpoly.eq_X_sub_C, P]
      simp [map_ofNat]
    have hfin : Module.finrank ℚ (K 0) = 1 := by
      rw [K, IntermediateField.adjoin.finrank (point 0).property, hmin]
      have hmap : (P 0).map (Int.castRingHom ℚ) = X - C (2 : ℚ) := by simp [P, map_ofNat]
      rw [hmap, Polynomial.natDegree_X_sub_C]
    exact ⟨hfin, hmin⟩
  | succ n ih =>
    rcases ih with ⟨hfin_n, hmin_n⟩
    have hnot_mem : (point (n + 1)).val ∉ K n := by
      intro hmem
      let xn1 : K n := ⟨(point (n + 1)).val, hmem⟩
      let beta : K n := 2 * xn1 - genK n
      have hbeta_sq : beta ^ 2 = (genK n) ^ 2 + 4 := by
        apply Subtype.ext
        change (2 * (point (n + 1)).val - (point n).val) ^ 2 = (point n).val ^ 2 + 4
        linarith [point_sq_sub n]
      have hsq_norm : IsSquare (Algebra.norm ℚ ((genK n) ^ 2 + 4)) := by
        rw [← hbeta_sq, map_pow]
        exact ⟨Algebra.norm ℚ beta, sq _⟩
      rw [norm_gen_sq_add_four n hmin_n] at hsq_norm
      exact not_isSquare_rat_of_mod_three_eq_two (norm_aeval_twoI_mod_three n) hsq_norm
    have hfin_le2 : Module.finrank (K n) (Lstep n) ≤ 2 := by
      let q : (K n)[X] := X ^ 2 - (C (genK n) * X + 1)
      have hlt : (C (genK n) * X + 1 : (K n)[X]).natDegree < (X ^ 2 : (K n)[X]).natDegree := by
        rw [Polynomial.natDegree_X_pow]
        refine lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) ?_
        have hcx : (C (genK n) * X : (K n)[X]).natDegree ≤ 1 := by
          refine le_trans Polynomial.natDegree_mul_le ?_
          simp
        simp only [Polynomial.natDegree_one]
        omega
      have hq_mon : q.Monic := (Polynomial.monic_X_pow 2).sub_of_left (Polynomial.degree_lt_degree hlt)
      have hq_deg : q.natDegree = 2 := by
        dsimp [q]
        rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, Polynomial.natDegree_X_pow]
      have hq_eval : Polynomial.aeval (point (n + 1)).val q = 0 := by
        dsimp [q, genK]
        simp only [map_sub, map_pow, map_add, map_mul, aeval_X, aeval_C, map_one]
        change (point (n + 1)).val ^ 2 - ((point n).val * (point (n + 1)).val + 1) = 0
        linarith [point_sq_sub n]
      have hy1_int : IsIntegral (K n) (point (n + 1)).val := ⟨q, hq_mon, hq_eval⟩
      have hdvd : minpoly (K n) (point (n + 1)).val ∣ q := minpoly.dvd (K n) (point (n + 1)).val hq_eval
      have hdeg_le : (minpoly (K n) (point (n + 1)).val).natDegree ≤ 2 :=
        hq_deg ▸ Polynomial.natDegree_le_of_dvd hdvd hq_mon.ne_zero
      rw [Lstep, IntermediateField.adjoin.finrank hy1_int]
      exact hdeg_le
    have hfin_ne1 : Module.finrank (K n) (Lstep n) ≠ 1 := by
      intro h1
      have hbot : Lstep n = ⊥ := IntermediateField.finrank_eq_one_iff.mp h1
      have hmem_bot : (point (n + 1)).val ∈ (⊥ : IntermediateField (K n) ℝ) := by
        rw [← hbot]
        exact IntermediateField.subset_adjoin (K n) _ (Set.mem_singleton _)
      rw [IntermediateField.mem_bot] at hmem_bot
      obtain ⟨c, hc⟩ := hmem_bot
      exact hnot_mem (hc ▸ c.property)
    have hfin_pos : 0 < Module.finrank (K n) (Lstep n) := Module.finrank_pos
    have hfin_eq2 : Module.finrank (K n) (Lstep n) = 2 := by omega
    have hfin_succ : Module.finrank ℚ (K (n + 1)) = 2 ^ (n + 1) := by
      rw [← (equivSucc n).toLinearEquiv.finrank_eq,
        ← Module.finrank_mul_finrank ℚ (K n) (Lstep n), hfin_n, hfin_eq2, pow_succ]
    have hmin_succ : minpoly ℚ (point (n + 1)).val = (P (n + 1)).map (Int.castRingHom ℚ) := by
      have hP_monQ : ((P (n + 1)).map (Int.castRingHom ℚ)).Monic :=
        (P_natDegree_and_monic (n + 1)).2.map _
      have hP_degQ : ((P (n + 1)).map (Int.castRingHom ℚ)).natDegree = 2 ^ (n + 1) := by
        rw [(P_natDegree_and_monic (n + 1)).2.natDegree_map, (P_natDegree_and_monic (n + 1)).1]
      have hP_evalQ : Polynomial.aeval (point (n + 1)).val ((P (n + 1)).map (Int.castRingHom ℚ)) = 0 := by
        change Polynomial.aeval (point (n + 1)).val ((P (n + 1)).map (algebraMap ℤ ℚ)) = 0
        rw [Polynomial.aeval_map_algebraMap]
        exact aeval_P_point (n + 1)
      have hdvd : minpoly ℚ (point (n + 1)).val ∣ (P (n + 1)).map (Int.castRingHom ℚ) :=
        minpoly.dvd ℚ (point (n + 1)).val hP_evalQ
      have hdeg_min : (minpoly ℚ (point (n + 1)).val).natDegree = 2 ^ (n + 1) := by
        rw [← IntermediateField.adjoin.finrank (point (n + 1)).property]
        exact hfin_succ
      exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
        (minpoly.monic (point (n + 1)).property) hP_monQ hdvd (by omega)).symm
    exact ⟨hfin_succ, hmin_succ⟩

theorem main_proof (n : ℕ) :
    (NumberField.discr (K n)) ^ 2 ∣ NumberField.discr (K (n + 1)) := by
  have hfin : Module.finrank (K n) (Lstep n) = 2 := by
    have hmul := Module.finrank_mul_finrank ℚ (K n) (Lstep n)
    rw [(equivSucc n).toLinearEquiv.finrank_eq, (finrank_and_minpoly n).1,
      (finrank_and_minpoly (n + 1)).1] at hmul
    have hpos : 0 < 2 ^ n := by positivity
    have h2 : 2 ^ n * Module.finrank (K n) (Lstep n) = 2 ^ n * 2 := by
      rw [hmul, pow_succ]
    exact Nat.eq_of_mul_eq_mul_left hpos h2
  rw [← NumberField.discr_eq_discr_of_algEquiv (Lstep n) (equivSucc n)]
  simpa [hfin] using discr_pow_finrank_dvd_discr (K n) (Lstep n)

end OMA.ProofA259440

theorem OMA.solution : type_of% @OMA.S_oeis_a259440.main := by
  intro n _
  exact OMA.ProofA259440.main_proof n
