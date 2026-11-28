import OMAStatements.S_mo_168514
import Mathlib

open Polynomial

open OMA.S_mo_168514

private theorem rational_bezout_integer_multiple (p q : ℤ[X])
    (hC : IsCoprime (p.map (algebraMap ℤ ℚ)) (q.map (algebraMap ℤ ℚ))) :
    ∃ (u v : ℤ[X]) (c : ℤ), c ≠ 0 ∧ u*p+v*q = C c := by
  obtain ⟨a,b,hab⟩ := hC
  let S := nonZeroDivisors ℤ
  let aZ := IsLocalization.integerNormalization S a
  let bZ := IsLocalization.integerNormalization S b
  obtain ⟨r,hr,hrMap⟩ := IsLocalization.integerNormalization_spec S a
  obtain ⟨s,hs,hsMap⟩ := IsLocalization.integerNormalization_spec S b
  have hr0 : r ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hr
  have hs0 : s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hs
  refine ⟨C s*aZ,C r*bZ,r*s,mul_ne_zero hr0 hs0,?_⟩
  apply Polynomial.map_injective (algebraMap ℤ ℚ) (FaithfulSMul.algebraMap_injective ℤ ℚ)
  simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,aZ,bZ,hrMap,hsMap]
  simp only [Algebra.smul_def,Polynomial.algebraMap_apply,map_mul]
  calc
    _ = C (algebraMap ℤ ℚ r) * C (algebraMap ℤ ℚ s) *
        (a * p.map (algebraMap ℤ ℚ) + b * q.map (algebraMap ℤ ℚ)) := by ring
    _ = _ := by rw [hab,mul_one]

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
  let cQ := algebraMap ℤ ℚ c
  have hcQ : cQ ≠ 0 := by
    intro hz
    exact hc0 ((FaithfulSMul.algebraMap_injective ℤ ℚ) (by simpa [cQ] using hz))
  have hD : D.map (algebraMap ℤ ℚ) ∣ d := by
    refine ⟨C cQ⁻¹,?_⟩
    have hScale : D.map (algebraMap ℤ ℚ) = C cQ*d := by
      change (IsLocalization.integerNormalization S d).map (algebraMap ℤ ℚ) = _
      rw [hNorm,Algebra.smul_def,Polynomial.algebraMap_apply]
    calc
      d = (C cQ*C cQ⁻¹)*d := by rw [←map_mul,mul_inv_cancel₀ hcQ,map_one,one_mul]
      _ = _ := by rw [hScale]; ring
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
