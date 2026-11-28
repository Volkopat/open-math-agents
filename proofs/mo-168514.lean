import OMAStatements.S_mo_168514
import Mathlib

/-! Shortens @AkiRA-COM-FP’s proof from PR #17419 using shared localization denominators
and unit divisibility. Pending PR #31898 by @Aydin-codes was also reviewed. -/

open Polynomial

open OMA.S_mo_168514

private theorem rational_bezout_integer_multiple (p q : ℤ[X])
    (hC : IsCoprime (p.map (algebraMap ℤ ℚ)) (q.map (algebraMap ℤ ℚ))) :
    ∃ (u v : ℤ[X]) (c : ℤ), c ≠ 0 ∧ u*p+v*q = C c := by
  obtain ⟨a,b,hab⟩ := hC
  let := Polynomial.algebra (R := ℤ) (A := ℚ)
  let := Polynomial.isLocalization (nonZeroDivisors ℤ) ℚ
  obtain ⟨⟨_, c, hc, rfl⟩, h⟩ :=
    IsLocalization.exist_integer_multiples_of_finite
      ((nonZeroDivisors ℤ).map C) ![a, b]
  obtain ⟨u, hu⟩ := h 0
  obtain ⟨v, hv⟩ := h 1
  refine ⟨u, v, c, mem_nonZeroDivisors_iff_ne_zero.mp hc, ?_⟩
  apply Polynomial.map_injective (algebraMap ℤ ℚ) (FaithfulSMul.algebraMap_injective ℤ ℚ)
  simp only [Algebra.smul_def, Polynomial.algebraMap_def, Polynomial.coe_mapRingHom, map_C,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hu hv
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, hu, hv]
  calc
    _ = C (algebraMap ℤ ℚ c) *
        (a * p.map (algebraMap ℤ ℚ) + b * q.map (algebraMap ℤ ℚ)) := by ring
    _ = _ := by rw [hab, mul_one]

private theorem integer_coprime_over_rationals {p q : ℤ[X]} (hp : p ≠ 0) (h : IsRelPrime p q) :
    IsCoprime (p.map (algebraMap ℤ ℚ)) (q.map (algebraMap ℤ ℚ)) := by
  apply IsRelPrime.isCoprime
  intro d hP hQ
  have hd : d ≠ 0 := by
    intro hz
    rw [hz,zero_dvd_iff] at hP
    apply hp
    apply Polynomial.map_injective (algebraMap ℤ ℚ) (FaithfulSMul.algebraMap_injective ℤ ℚ)
    simpa using hP
  let S := nonZeroDivisors ℤ
  let D : ℤ[X] := IsLocalization.integerNormalization S d
  obtain ⟨c,hc,hNorm⟩ := IsLocalization.integerNormalization_spec S d
  have hc0 : c ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hc
  have hD : D.map (algebraMap ℤ ℚ) ∣ d := by
    change (IsLocalization.integerNormalization S d).map (algebraMap ℤ ℚ) ∣ d
    rw [hNorm, Algebra.smul_def, Polynomial.algebraMap_apply]
    exact (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by change (c : ℚ) ≠ 0; exact_mod_cast hc0))).mul_left_dvd.mpr
      (dvd_refl d)
  have hPrim : D.primPart.map (algebraMap ℤ ℚ) ∣ d :=
    (map_dvd (Polynomial.mapRingHom (algebraMap ℤ ℚ)) D.primPart_dvd).trans hD
  have hp' : D.primPart ∣ p :=
    (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast D.primPart p D.isPrimitive_primPart).mpr
      (hPrim.trans hP)
  have hq' : D.primPart ∣ q :=
    (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast D.primPart q D.isPrimitive_primPart).mpr
      (hPrim.trans hQ)
  exact Polynomial.isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart hd (h hp' hq')

theorem OMA.solution : type_of% @OMA.S_mo_168514.main := by
  intro p q hp _ h
  have hR := integer_coprime_over_rationals hp.ne_zero h
  obtain ⟨u,v,c,hc,he⟩ := rational_bezout_integer_multiple p q hR
  refine ⟨c.natAbs,?_⟩
  intro n
  have hEval := congrArg (Polynomial.eval n) he
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C] at hEval
  let g := Int.gcd (p.eval n) (q.eval n)
  have hp : (g : ℤ) ∣ p.eval n := Int.gcd_dvd_left _ _
  have hq : (g : ℤ) ∣ q.eval n := Int.gcd_dvd_right _ _
  have hDvd : (g : ℤ) ∣ c :=
    hEval ▸ dvd_add (dvd_mul_of_dvd_right hp _) (dvd_mul_of_dvd_right hq _)
  have hNat : g ∣ c.natAbs := by
    simpa using Int.natAbs_dvd_natAbs.mpr hDvd
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hc) hNat
