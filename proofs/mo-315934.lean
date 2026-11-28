import OMAStatements.S_mo_315934
import Mathlib

open CategoryTheory

open OMA.S_mo_315934



theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_315934.main) := by
  rintro ⟨A,⟨R⟩⟩
  let a := R.equiv A (𝟙 A)
  obtain ⟨m,hm,hPow⟩ := a.property.exists_pow_eq_one
  let G := GrpCat.of (Multiplicative (ZMod (m+1)))
  let g : G := Multiplicative.ofAdd (1 : ZMod (m+1))
  have hgPow : g^(m+1) = 1 := by
    change (m+1) • (1 : ZMod (m+1)) = 0
    rw [nsmul_eq_mul,mul_one]
    exact ZMod.natCast_self _
  have hg : IsOfFinOrder g := isOfFinOrder_iff_pow_eq_one.mpr ⟨m+1,by omega,hgPow⟩
  let f := (R.equiv G).symm ⟨g,hg⟩
  have hEval : R.equiv G f = ⟨g,hg⟩ := (R.equiv G).apply_symm_apply _
  have hEq := R.compatible A G (𝟙 A) f
  rw [Category.id_comp,hEval] at hEq
  change g = f.hom a.val at hEq
  have hBad : g^m = 1 := by
    rw [hEq,←map_pow,hPow,map_one]
  change m • (1 : ZMod (m+1)) = 0 at hBad
  rw [nsmul_eq_mul,mul_one] at hBad
  have hMod : m ≡ 0 [MOD m+1] := (ZMod.natCast_eq_natCast_iff m 0 (m+1)).mp (by simpa using hBad)
  exact Nat.not_dvd_of_pos_of_lt hm (by omega) (Nat.modEq_zero_iff_dvd.mp hMod)
