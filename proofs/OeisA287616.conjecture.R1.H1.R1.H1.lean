import OMAReductions.R_OeisA287616_conjecture_R1_H1_R1
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.NumberTheory.Padics.WithVal
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Nat.Sqrt

namespace LegendreLatticeArithmetic

open Matrix

private theorem square_ratio_lift (n : ℕ) (u v : ZMod n)
    (hu : IsUnit u) (h : IsSquare (u * v)) : ∃ r : ℤ, u * (r : ZMod n) ^ 2 = v := by
  obtain ⟨U, rfl⟩ := hu
  obtain ⟨w, hw⟩ := h.exists_sq
  obtain ⟨r, hr⟩ := ZMod.intCast_surjective (w * (↑U⁻¹ : ZMod n))
  refine ⟨r, ?_⟩
  rw [hr]
  calc
    (↑U : ZMod n) * (w * (↑U⁻¹ : ZMod n)) ^ 2 =
      (↑U * (↑U⁻¹ : ZMod n)) * (↑U⁻¹ * w ^ 2) := by ring
    _ = v := by rw [Units.mul_inv, one_mul, ← hw, ← mul_assoc, Units.inv_mul, one_mul]

theorem congruence_matrix (a b c : ℕ)
    (hab : a.Coprime b) (hac : a.Coprime c) (hbc : b.Coprime c)
    (ha : IsSquare ((b : ZMod a) * (c : ZMod a)))
    (hb : IsSquare ((a : ZMod b) * (c : ZMod b)))
    (hc : IsSquare (-(a : ZMod c) * (b : ZMod c))) :
    ∃ T : Matrix (Fin 3) (Fin 3) ℤ, T.det = (a : ℤ) * b * c ∧
      ∀ v : Fin 3 → ℤ, let w := T *ᵥ v
        (a : ℤ) * b * c ∣ (a : ℤ) * (w 0) ^ 2 + b * (w 1) ^ 2 - c * (w 2) ^ 2 := by
  obtain ⟨r, hr⟩ := square_ratio_lift a (b : ZMod a) (c : ZMod a)
    ((ZMod.isUnit_iff_coprime _ _).mpr hab.symm) ha
  obtain ⟨s, hs⟩ := square_ratio_lift b (a : ZMod b) (c : ZMod b)
    ((ZMod.isUnit_iff_coprime _ _).mpr hab) hb
  obtain ⟨t, ht⟩ := square_ratio_lift c (a : ZMod c) (-(b : ZMod c))
    ((ZMod.isUnit_iff_coprime _ _).mpr hac) (by simpa only [neg_mul, mul_neg] using hc)
  let U := ZMod.unitOfCoprime b hbc
  have hU : (U : ZMod c) = (b : ZMod c) := ZMod.coe_unitOfCoprime _ _
  obtain ⟨j, hj⟩ := ZMod.intCast_surjective ((↑U⁻¹ : ZMod c) * ((t : ZMod c) * (a : ZMod c)))
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective ((↑U⁻¹ : ZMod c) * ((t : ZMod c) * (r : ZMod c) - (s : ZMod c)))
  have hj' : (b : ZMod c) * (j : ZMod c) = (t : ZMod c) * (a : ZMod c) := by
    rw [hj, ← hU, ← mul_assoc, Units.mul_inv, one_mul]
  have hk' : (b : ZMod c) * (k : ZMod c) = (t : ZMod c) * (r : ZMod c) - (s : ZMod c) := by
    rw [hk, ← hU, ← mul_assoc, Units.mul_inv, one_mul]
  let T : Matrix (Fin 3) (Fin 3) ℤ :=
    !![(b : ℤ) * c, (b : ℤ) * j, s + (b : ℤ) * k;
       0, (a : ℤ), r;
       0, 0, 1]
  refine ⟨T, ?_, ?_⟩
  · rw [Matrix.det_fin_three]
    simp [T]
    ring
  intro v
  let x := (b : ℤ) * c * v 0 + (b : ℤ) * j * v 1 + (s + (b : ℤ) * k) * v 2
  let y := (a : ℤ) * v 1 + r * v 2
  let z := v 2
  have hX : (T *ᵥ v) 0 = x := by simp [T, x, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hY : (T *ᵥ v) 1 = y := by simp [T, y, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hZ : (T *ᵥ v) 2 = z := by simp [T, z, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  let Q := (a : ℤ) * x ^ 2 + b * y ^ 2 - c * z ^ 2
  have hA : (a : ℤ) ∣ Q := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    have hy : (y : ZMod a) = (r : ZMod a) * (z : ZMod a) := by
      simp [y, z]
    push_cast [Q]
    rw [ZMod.natCast_self, zero_mul, zero_add, hy, mul_pow, ← mul_assoc, hr, sub_self]
  have hB : (b : ℤ) ∣ Q := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    have hx : (x : ZMod b) = (s : ZMod b) * (z : ZMod b) := by
      simp [x, z]
    push_cast [Q]
    rw [ZMod.natCast_self, zero_mul, add_zero, hx, mul_pow, ← mul_assoc, hs, sub_self]
  have hC : (c : ℤ) ∣ Q := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    have hx : (x : ZMod c) = (t : ZMod c) * (y : ZMod c) := by
      simp only [x, y, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero,
        zero_mul, zero_add, hj', hk']
      ring
    push_cast [Q]
    rw [ZMod.natCast_self, zero_mul, sub_zero, hx, mul_pow, ← mul_assoc, ht]
    ring
  have hAB : IsCoprime (a : ℤ) b := by exact_mod_cast hab
  have hAC : IsCoprime (a : ℤ) c := by exact_mod_cast hac
  have hBC : IsCoprime (b : ℤ) c := by exact_mod_cast hbc
  dsimp
  rw [hX, hY, hZ]
  exact (hAC.mul_left hBC).mul_dvd (hAB.mul_dvd hA hB) hC

theorem norm_descent {a b c x y z : ℚ} (ha : 0 < a) (hb : 0 < b)
    (h : a * x ^ 2 + b * y ^ 2 - c * z ^ 2 = a * b * c) :
    ∃ u v : ℚ, a * u ^ 2 + b * v ^ 2 = c := by
  let D := z ^ 2 + a * b
  have hD : 0 < D := by dsimp [D]; positivity
  let u := (x * z + b * y) / D
  let v := (y * z - a * x) / D
  have hn : a * (x * z + b * y) ^ 2 + b * (y * z - a * x) ^ 2 =
      (a * x ^ 2 + b * y ^ 2) * D := by dsimp [D]; ring
  have hc : a * x ^ 2 + b * y ^ 2 = c * D := by
    dsimp [D]
    linear_combination h
  refine ⟨u, v, ?_⟩
  dsimp [u, v]
  rw [div_pow, div_pow, ← mul_div_assoc, ← mul_div_assoc, ← add_div, hn, hc, mul_assoc, ← pow_two,
    mul_div_cancel_right₀ _ (pow_ne_zero _ hD.ne')]




theorem box_descent {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsq : Squarefree (a * b)) (hgt : 1 < a * b)
    (x y z : ℤ) (hn : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0)
    (hx : x ^ 2 ≤ (b : ℤ) * c) (hy : y ^ 2 ≤ (a : ℤ) * c) (hz : z ^ 2 ≤ (a : ℤ) * b)
    (hdvd : (a : ℤ) * b * c ∣ (a : ℤ) * x ^ 2 + b * y ^ 2 - c * z ^ 2) :
    ∃ u v : ℚ, (a : ℚ) * u ^ 2 + b * v ^ 2 = c := by
  let D : ℤ := (a : ℤ) * b * c
  let Q : ℤ := (a : ℤ) * x ^ 2 + b * y ^ 2 - c * z ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hax : 0 ≤ (a : ℤ) * x ^ 2 := by positivity
  have hby : 0 ≤ (b : ℤ) * y ^ 2 := by positivity
  have hcz : 0 ≤ (c : ℤ) * z ^ 2 := by positivity
  have hAx : (a : ℤ) * x ^ 2 ≤ D := by
    dsimp [D]
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hx (by positivity)
  have hBy : (b : ℤ) * y ^ 2 ≤ D := by
    dsimp [D]
    rw [mul_comm (a : ℤ), mul_assoc]
    exact mul_le_mul_of_nonneg_left hy (by positivity)
  have hCz : (c : ℤ) * z ^ 2 ≤ D := by
    dsimp [D]
    rw [mul_comm _ (c : ℤ)]
    exact mul_le_mul_of_nonneg_left hz (by positivity)
  obtain ⟨k, hk⟩ : D ∣ Q := hdvd
  have hlow : -D ≤ Q := by dsimp [Q]; linarith
  have hupp : Q ≤ 2 * D := by dsimp [Q]; linarith
  have hklo : -1 ≤ k := by
    by_contra h
    have hh : D * k < D * (-1) := mul_lt_mul_of_pos_left (lt_of_not_ge h) hD
    rw [← hk] at hh
    linarith
  have hkhi : k ≤ 2 := by
    by_contra h
    have hh : D * 2 < D * k := mul_lt_mul_of_pos_left (lt_of_not_ge h) hD
    rw [← hk] at hh
    linarith
  interval_cases k
  · have hcz' : (c : ℤ) * z ^ 2 = D := by dsimp [Q] at hk; linarith
    have hz' : z ^ 2 = (a : ℤ) * b := by
      apply mul_left_cancel₀ (show (c : ℤ) ≠ 0 by positivity)
      simpa only [D, mul_comm (c : ℤ)] using hcz'
    have hab : z.natAbs ^ 2 = a * b := by
      have he := congrArg Int.natAbs hz'
      simpa only [Int.natAbs_pow, Int.natAbs_mul, Int.natAbs_natCast] using he
    have hu : IsUnit z.natAbs := hsq z.natAbs (by rw [← hab, pow_two])
    have hunit := Nat.isUnit_iff.mp hu
    rw [hunit, one_pow] at hab
    omega
  · have hzero : (a : ℤ) * x ^ 2 + b * y ^ 2 - c * z ^ 2 = 0 := by
      simpa only [mul_zero] using hk
    have hzn : z ≠ 0 := by
      intro h
      rw [h] at hzero hcz
      have hAx' : (a : ℤ) * x ^ 2 = 0 := by nlinarith
      have hBy' : (b : ℤ) * y ^ 2 = 0 := by nlinarith
      have hx' : x = 0 := by
        have hh := (mul_eq_zero.mp hAx').resolve_left (by positivity : (a : ℤ) ≠ 0)
        simpa using hh
      have hy' : y = 0 := by
        have hh := (mul_eq_zero.mp hBy').resolve_left (by positivity : (b : ℤ) ≠ 0)
        simpa using hh
      exact hn.elim (fun h => h hx') (fun h' => h'.elim (fun h => h hy') (fun hh => hh h))
    have hq : (a : ℚ) * (x : ℚ) ^ 2 + b * (y : ℚ) ^ 2 - c * (z : ℚ) ^ 2 = 0 := by
      exact_mod_cast hzero
    refine ⟨(x : ℚ) / z, (y : ℚ) / z, ?_⟩
    field_simp
    · linarith
  · have hq : (a : ℚ) * (x : ℚ) ^ 2 + b * (y : ℚ) ^ 2 - c * (z : ℚ) ^ 2 = (a : ℚ) * b * c := by
      have he : (a : ℤ) * x ^ 2 + b * y ^ 2 - c * z ^ 2 = (a : ℤ) * b * c := by simpa [D, Q] using hk
      exact_mod_cast he
    exact norm_descent (by positivity) (by positivity) hq
  · have hax' : (a : ℤ) * x ^ 2 = D := by dsimp [Q] at hk; linarith
    have hbc : x ^ 2 = (b : ℤ) * c := by
      apply mul_left_cancel₀ (show (a : ℤ) ≠ 0 by positivity)
      simpa only [D, mul_assoc] using hax'
    have hq : (x : ℚ) ^ 2 = (b : ℚ) * c := by exact_mod_cast hbc
    refine ⟨0, (x : ℚ) / b, ?_⟩
    rw [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, div_pow, hq, pow_two]
    field_simp


end LegendreLatticeArithmetic

namespace LegendreMinkowskiBox

open Matrix MeasureTheory Set
open scoped ENNReal

theorem exists_integer_point_in_box (T : Matrix (Fin 3) (Fin 3) ℤ) (hT : T.det ≠ 0)
    (R : Fin 3 → ℝ) (hR : ∀ i, 0 ≤ R i) (hsize : |(T.det : ℝ)| ≤ ∏ i, R i) :
    ∃ v : Fin 3 → ℤ, T *ᵥ v ≠ 0 ∧ ∀ i, |((T *ᵥ v) i : ℝ)| ≤ R i := by
  classical
  let M := T.map (Int.castRingHom ℝ)
  have hdet : M.det = (T.det : ℝ) := (Int.castRingHom ℝ).map_det T |>.symm
  have hM : M.det ≠ 0 := by rw [hdet]; exact_mod_cast hT
  let e : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) :=
    M.toLinearEquiv' (Matrix.invertibleOfIsUnitDet M (isUnit_iff_ne_zero.mpr hM))
  let b := (Pi.basisFun ℝ (Fin 3)).map e
  have he (u : Fin 3 → ℝ) : e u = M *ᵥ u := rfl
  have hb : Matrix.of (b : Fin 3 → Fin 3 → ℝ) = Mᵀ := by
    ext i j
    change e ((Pi.basisFun ℝ (Fin 3)) i) j = M j i
    rw [he, Pi.basisFun_apply]
    change (M *ᵥ Pi.single i 1) j = M j i
    rw [Matrix.mulVec_single_one]
    rfl
  let L := Submodule.span ℤ (Set.range b)
  let B : Set (Fin 3 → ℝ) := Set.Icc (-R) R
  have hsym : ∀ x ∈ B, -x ∈ B := by
    intro x hx
    exact ⟨fun i => neg_le_neg (hx.2 i), fun i => by simpa using neg_le_neg (hx.1 i)⟩
  have hconv : Convex ℝ B := convex_Icc _ _
  have hcompact : IsCompact B := isCompact_Icc
  have hvol : volume (ZSpan.fundamentalDomain b) * 2 ^ Module.finrank ℝ (Fin 3 → ℝ)
      ≤ volume B := by
    rw [ZSpan.volume_fundamentalDomain, hb, Matrix.det_transpose, hdet]
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    change ENNReal.ofReal |(T.det : ℝ)| * (2 : ℝ≥0∞) ^ 3 ≤ volume (Set.Icc (-R) R)
    rw [Real.volume_Icc_pi]
    simp only [Fin.prod_univ_three, Pi.neg_apply, sub_neg_eq_add, ← two_mul]
    have r0 : 0 ≤ 2 * R 0 := mul_nonneg (by norm_num) (hR 0)
    have r1 : 0 ≤ 2 * R 1 := mul_nonneg (by norm_num) (hR 1)
    rw [← ENNReal.ofReal_mul r0, ← ENNReal.ofReal_mul (mul_nonneg r0 r1)]
    have hprod : |(T.det : ℝ)| ≤ R 0 * R 1 * R 2 := by
      simpa only [Fin.prod_univ_three, mul_assoc] using hsize
    rw [show (2 : ℝ≥0∞) ^ 3 = ENNReal.ofReal (2 ^ 3 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (abs_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  let : Countable (Submodule.span ℤ (Set.range b)).toAddSubgroup := by
    apply Function.Injective.countable (f :=
      fun (x : (Submodule.span ℤ (Set.range b)).toAddSubgroup) (i : Fin 3) =>
        ⌊b.repr (x : Fin 3 → ℝ) i⌋)
    intro x y hxy
    apply Subtype.ext
    have hx' := ZSpan.floor_eq_self_of_mem b (x : Fin 3 → ℝ) x.property
    have hy' := ZSpan.floor_eq_self_of_mem b (y : Fin 3 → ℝ) y.property
    rw [← hx', ← hy']
    apply b.ext_elem
    intro i
    rw [ZSpan.repr_floor_apply, ZSpan.repr_floor_apply]
    exact congrArg (fun n : ℤ => (n : ℝ)) (congrFun hxy i)
  obtain ⟨x, hx, hxB⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
    (ZSpan.isAddFundamentalDomain' b volume) hsym hconv hcompact hvol
  have hxL : (x : Fin 3 → ℝ) ∈ L := x.property
  obtain ⟨v, hv⟩ := Classical.axiomOfChoice ((b.mem_span_iff_repr_mem ℤ _).mp hxL)
  have hr : e (fun i => (v i : ℝ)) = (x : Fin 3 → ℝ) := by
    apply b.ext_elem
    intro i
    change b.repr (e (fun i => (v i : ℝ))) i = _
    rw [Module.Basis.map_repr]
    simpa [b] using hv i
  have hcast : (fun i => ((T *ᵥ v) i : ℝ)) = (x : Fin 3 → ℝ) := by
    funext i
    rw [he] at hr
    exact (RingHom.map_mulVec (Int.castRingHom ℝ) T v i).trans (congrFun hr i)
  refine ⟨v, ?_, fun i => ?_⟩
  · intro hz
    apply hx
    apply Subtype.coe_injective
    rw [hz] at hcast
    exact hcast.symm.trans (by funext i; simp)
  · rw [congrFun hcast i]
    exact abs_le.mpr ⟨hxB.1 i, hxB.2 i⟩


end LegendreMinkowskiBox

namespace LegendreMinkowskiAssembly

open Matrix LegendreLatticeArithmetic LegendreMinkowskiBox

theorem binary_representation_of_residues {a b c : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a.Coprime b) (hac : a.Coprime c) (hbc : b.Coprime c)
    (hsq : Squarefree (a * b)) (hgt : 1 < a * b)
    (h1 : IsSquare ((b : ZMod a) * (c : ZMod a)))
    (h2 : IsSquare ((a : ZMod b) * (c : ZMod b)))
    (h3 : IsSquare (-(a : ZMod c) * (b : ZMod c))) :
    ∃ u v : ℚ, (a : ℚ) * u ^ 2 + b * v ^ 2 = c := by
  obtain ⟨T, hT, hl⟩ := congruence_matrix a b c hab hac hbc h1 h2 h3
  let R : Fin 3 → ℝ := ![Real.sqrt ((b : ℝ) * c), Real.sqrt ((a : ℝ) * c), Real.sqrt ((a : ℝ) * b)]
  have hR (i : Fin 3) : 0 ≤ R i := by
    fin_cases i <;> apply Real.sqrt_nonneg
  have hp0 : R 0 ^ 2 = (b : ℝ) * c := Real.sq_sqrt (by positivity)
  have hp1 : R 1 ^ 2 = (a : ℝ) * c := Real.sq_sqrt (by positivity)
  have hp2 : R 2 ^ 2 = (a : ℝ) * b := Real.sq_sqrt (by positivity)
  have hT' : (T.det : ℝ) = (a : ℝ) * b * c := by exact_mod_cast hT
  have hsize : |(T.det : ℝ)| ≤ ∏ i, R i := by
    rw [hT', abs_of_nonneg (by positivity), Fin.prod_univ_three]
    apply ((sq_eq_sq₀ (mul_nonneg (mul_nonneg (hR 0) (hR 1)) (hR 2))
      (by positivity : 0 ≤ (a : ℝ) * b * c))).mp ?_ |>.ge
    rw [mul_pow, mul_pow, hp0, hp1, hp2]
    ring
  obtain ⟨v, hv, hw⟩ := exists_integer_point_in_box T (by rw [hT]; positivity) R hR hsize
  let w := T *ᵥ v
  have hn : w 0 ≠ 0 ∨ w 1 ≠ 0 ∨ w 2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    funext i
    fin_cases i
    · exact h.1
    · exact h.2.1
    · exact h.2.2
  have hs (i : Fin 3) : (w i : ℝ) ^ 2 ≤ R i ^ 2 := by
    rw [← sq_abs ((w i : ℝ))]
    exact (sq_le_sq₀ (abs_nonneg _) (hR i)).mpr (hw i)
  have h0 : (w 0) ^ 2 ≤ (b : ℤ) * c := by have h := hs 0; rw [hp0] at h; exact_mod_cast h
  have h1' : (w 1) ^ 2 ≤ (a : ℤ) * c := by have h := hs 1; rw [hp1] at h; exact_mod_cast h
  have h2' : (w 2) ^ 2 ≤ (a : ℤ) * b := by have h := hs 2; rw [hp2] at h; exact_mod_cast h
  exact box_descent ha hb hc hsq hgt (w 0) (w 1) (w 2) hn h0 h1' h2' (hl v)


end LegendreMinkowskiAssembly

namespace A287616RationalPrimes

open scoped NumberTheorySymbols

theorem square_cast_of_coprime {a b n : ℕ} (hab : a.Coprime b)
    (ha : IsSquare (n : ZMod a)) (hb : IsSquare (n : ZMod b)) :
    IsSquare (n : ZMod (a * b)) := by
  obtain ⟨x, hx⟩ := ha.exists_sq
  obtain ⟨y, hy⟩ := hb.exists_sq
  let f := ZMod.chineseRemainder hab
  refine (isSquare_iff_exists_sq _).mpr ⟨f.symm (x, y), f.injective ?_⟩
  rw [map_pow, RingEquiv.apply_symm_apply, map_natCast]
  exact Prod.ext hx hy

theorem prime_with_required_residue {m : ℕ} (hm : 0 < m)
    (hm12 : (12 : ℕ).Coprime m) (hm15 : (15 : ℕ).Coprime m) :
    ∃ p : ℕ, max 5 m < p ∧ p.Prime ∧ p % 12 = 1 ∧ (p : ZMod m) = -15 := by
  let : NeZero m := ⟨hm.ne'⟩
  let r := (-15 : ZMod m).val
  have hr : (r : ZMod m) = -15 := ZMod.natCast_zmod_val _
  let s := Nat.chineseRemainder hm12 1 r
  have hs12 : ((s : ℕ) : ZMod 12) = 1 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr s.property.1
  have hsm : ((s : ℕ) : ZMod m) = -15 :=
    ((ZMod.natCast_eq_natCast_iff _ _ _).mpr s.property.2).trans hr
  have hs12' : (s : ℕ).Coprime 12 := (ZMod.isUnit_iff_coprime _ _).mp (hs12 ▸ isUnit_one)
  have h15 : IsUnit (-(15 : ZMod m)) := ((ZMod.isUnit_iff_coprime 15 m).mpr hm15).neg
  have hsm' : (s : ℕ).Coprime m := (ZMod.isUnit_iff_coprime _ _).mp (hsm ▸ h15)
  obtain ⟨p, hp, hprime, hps⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max 5 m) (q := 12 * m) (a := s)
      (by positivity) (hs12'.mul_right hsm')
  have hps' := (Nat.modEq_and_modEq_iff_modEq_mul hm12).mpr hps
  refine ⟨p, hp, hprime, ?_, ?_⟩
  · have hh := hps'.1.trans s.property.1
    exact hh
  · exact ((ZMod.natCast_eq_natCast_iff _ _ _).mpr hps'.2).trans hsm

theorem jacobi_neg_fifteen_of_progression (m : ℕ) (hm : m % 60 = 23 ∨ m % 60 = 47) :
    J((-15 : ℤ) | m) = 1 := by
  have hodd : Odd m := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.mod_right (-15) hodd]
  change J((-15 : ℤ) | m % 60) = 1
  rcases hm with hm | hm <;> rw [hm] <;> norm_num

theorem residue_three_mul_at_auxiliary_prime {p m : ℕ} [Fact p.Prime]
    (hm : m % 60 = 23 ∨ m % 60 = 47) (hp : p % 12 = 1) (hpm : (p : ZMod m) = -15) :
    IsSquare ((3 : ZMod p) * (m : ZMod p)) := by
  have hoddm : Odd m := Nat.odd_iff.mpr (by omega)
  have hoddp : Odd p := Nat.odd_iff.mpr (by omega)
  have hp4 : p % 4 = 1 := by omega
  have h3 : J((3 : ℤ) | p) = 1 := by
    rw [jacobiSym.mod_right 3 hoddp]
    change J((3 : ℤ) | p % 12) = 1
    rw [hp]
    norm_num
  have hmod : ((p : ℤ) : ZMod m) = ((-15 : ℤ) : ZMod m) := by simpa using hpm
  have hx : (p : ℤ) % (m : ℤ) = -15 % (m : ℤ) :=
    (ZMod.intCast_eq_intCast_iff' _ _ _).mp hmod
  have hmp : J((m : ℤ) | p) = 1 := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four' hoddm hp4, jacobiSym.mod_left' hx]
    exact jacobi_neg_fifteen_of_progression m hm
  have h3m : J(3 * (m : ℤ) | p) = 1 := by rw [jacobiSym.mul_left, h3, hmp, mul_one]
  simpa using ZMod.isSquare_of_jacobiSym_eq_one h3m

theorem residue_neg_three_at_auxiliary_prime {p : ℕ} [Fact p.Prime]
    (hp : p % 12 = 1) : IsSquare (-(3 : ZMod p)) := by
  have hoddp : Odd p := Nat.odd_iff.mpr (by omega)
  have hf : J((-3 : ℤ) | p) = 1 := by
    rw [jacobiSym.mod_right (-3) hoddp]
    change J((-3 : ℤ) | p % 12) = 1
    rw [hp]
    norm_num
  simpa using ZMod.isSquare_of_jacobiSym_eq_one hf


end A287616RationalPrimes

namespace A287616RationalProgression

open LegendreMinkowskiAssembly A287616RationalPrimes

private theorem residue_coprime (m n : ℕ) (h : (m % n).Coprime n) : n.Coprime m := by
  rw [Nat.Coprime, Nat.gcd_rec]
  exact h

theorem rational_rep_arithmetic_progression (m : ℕ) (hm : 0 < m)
    (hm60 : m % 60 = 23 ∨ m % 60 = 47) :
    ∃ a b c : ℚ, 15 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 = (m : ℚ) := by
  have hm12 : (12 : ℕ).Coprime m := residue_coprime m 12 (by
    rw [show m % 12 = 11 by omega]; decide)
  have hm15 : (15 : ℕ).Coprime m := residue_coprime m 15 (by
    have he : m % 15 = 8 ∨ m % 15 = 2 := by omega
    rcases he with h | h <;> rw [h] <;> decide)
  obtain ⟨p, hp, hprime, hp12, hpm⟩ := prime_with_required_residue hm hm12 hm15
  let : Fact p.Prime := ⟨hprime⟩
  have hp3 : (3 : ℕ).Coprime p := residue_coprime p 3 (by rw [show p % 3 = 1 by omega]; decide)
  have hp5 : (5 : ℕ).Coprime p := by
    apply (hprime.coprime_iff_not_dvd.mpr ?_).symm
    intro hh
    exact (not_le_of_gt (lt_of_le_of_lt (le_max_left 5 m) hp)) (Nat.le_of_dvd (by decide) hh)
  have hmp : p.Coprime m := by
    apply hprime.coprime_iff_not_dvd.mpr
    intro hh
    exact (not_le_of_gt (lt_of_le_of_lt (le_max_right 5 m) hp)) (Nat.le_of_dvd hm hh)
  have hm3 : (3 : ℕ).Coprime m := residue_coprime m 3 (by rw [show m % 3 = 2 by omega]; decide)
  have hm5 : (5 : ℕ).Coprime m := residue_coprime m 5 (by
    have he : m % 5 = 3 ∨ m % 5 = 2 := by omega
    rcases he with h | h <;> rw [h] <;> decide)
  have cp3 : (p : ZMod 3) = 1 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (by
    change p % 3 = 1
    omega)
  have cm3 : (m : ZMod 3) = 2 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (by
    change m % 3 = 2
    omega)
  obtain ⟨x, y, hxy⟩ := binary_representation_of_residues
    (a := 1) (b := 3) (c := p) (by decide) (by decide) hprime.pos
    (by decide) (Nat.coprime_one_left p) hp3 (by simpa using Nat.prime_three.squarefree) (by decide)
    (by exact ⟨0, Subsingleton.elim _ _⟩)
    (by rw [cp3, Nat.cast_one, one_mul]; exact IsSquare.one)
    (by simpa using residue_neg_three_at_auxiliary_prime hp12)
  have hsa : IsSquare (((5 * p : ℕ) : ZMod 3) * (m : ZMod 3)) := by
    rw [Nat.cast_mul, cp3, cm3, mul_one]
    exact ⟨1, by decide⟩
  have hsb5 : IsSquare (((3 * m : ℕ) : ZMod 5)) := by
    rw [Nat.cast_mul]
    have h : (m : ZMod 5) = 2 ∨ (m : ZMod 5) = 3 := by
      have hr : m % 5 = 2 ∨ m % 5 = 3 := by omega
      exact hr.elim (fun h => Or.inl ((ZMod.natCast_eq_natCast_iff m 2 5).mpr h))
        (fun h => Or.inr ((ZMod.natCast_eq_natCast_iff m 3 5).mpr h))
    rcases h with hh | hh
    · rw [hh]
      exact ⟨1, by decide⟩
    · rw [hh]
      exact ⟨2, by decide⟩
  have hsbp : IsSquare (((3 * m : ℕ) : ZMod p)) := by
    rw [Nat.cast_mul]
    exact residue_three_mul_at_auxiliary_prime hm60 hp12 hpm
  have hsb : IsSquare ((3 : ZMod (5 * p)) * (m : ZMod (5 * p))) := by
    change IsSquare (((3 : ℕ) : ZMod (5 * p)) * (m : ZMod (5 * p)))
    rw [← Nat.cast_mul]
    exact square_cast_of_coprime hp5 hsb5 hsbp
  have hsc : IsSquare (-(3 : ZMod m) * ((5 * p : ℕ) : ZMod m)) := by
    rw [Nat.cast_mul, hpm]
    exact ⟨-15, by ring⟩
  have hs5p : Squarefree (5 * p) :=
    (Nat.squarefree_mul hp5).mpr ⟨Nat.prime_five.squarefree, hprime.squarefree⟩
  have hcop : (3 : ℕ).Coprime (5 * p) := (by decide : Nat.Coprime 3 5).mul_right hp3
  have hsq3 : Squarefree (3 * (5 * p)) :=
    (Nat.squarefree_mul hcop).mpr ⟨Nat.prime_three.squarefree, hs5p⟩
  have hlt : 1 < 3 * (5 * p) := by nlinarith [hprime.pos]
  obtain ⟨c, t, hct⟩ := binary_representation_of_residues
    (a := 3) (b := 5 * p) (c := m) (by decide) (Nat.mul_pos (by decide) hprime.pos) hm
    hcop hm3 (hm5.mul_left hmp) hsq3 hlt hsa hsb hsc
  push_cast at hct hxy
  refine ⟨y * t, x * t, c, ?_⟩
  linear_combination 5 * t ^ 2 * hxy + hct

theorem rational_rep_120n_add_23 (n : ℕ) :
    ∃ a b c : ℚ, 15 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 = 120 * n + 23 := by
  obtain ⟨a, b, c, h⟩ := rational_rep_arithmetic_progression (120 * n + 23)
    (by omega) (Or.inl (by omega))
  exact ⟨a, b, c, by exact_mod_cast h⟩


end A287616RationalProgression

/-! Finite Chinese-remainder patching for integral vectors in specified local lattices. -/

namespace FiniteLatticePatching

open Finset

theorem exists_vector_with_residues {ι ι' : Type*} [Fintype ι] (q : ι → ℕ)
    (hq : Pairwise fun i j => (q i).Coprime (q j)) (v : (i : ι) → ι' → ZMod (q i)) :
    ∃ w : ι' → ℤ, ∀ i j, (w j : ZMod (q i)) = v i j := by
  classical
  let M (i : ι) := ∏ k ∈ univ.erase i, q k
  have hC (i : ι) : (M i).Coprime (q i) := by
    exact Nat.Coprime.prod_left fun k hk => hq (ne_of_mem_erase hk)
  let u (i : ι) : (ZMod (q i))ˣ := ZMod.unitOfCoprime (M i) (hC i)
  let w (i : ι) (j : ι') : ℤ := (M i : ℤ) * ZMod.cast ((↑((u i)⁻¹) : ZMod (q i)) * v i j)
  have hd (i j) : (w i j : ZMod (q i)) = v i j := by
    simp only [w, Int.cast_mul, Int.cast_natCast, ZMod.intCast_zmod_cast]
    rw [← ZMod.coe_unitOfCoprime (M i) (hC i), ← mul_assoc, ← Units.val_mul]
    change (↑(u i * (u i)⁻¹) : ZMod (q i)) * v i j = _
    simp
  have hoff (i k : ι) (j : ι') (hki : k ≠ i) : (w k j : ZMod (q i)) = 0 := by
    have hdiv : q i ∣ M k := dvd_prod_of_mem q (mem_erase.mpr ⟨hki.symm, mem_univ i⟩)
    simp only [w, Int.cast_mul, Int.cast_natCast, (ZMod.natCast_eq_zero_iff _ _).mpr hdiv, zero_mul]
  refine ⟨fun j => ∑ i, w i j, ?_⟩
  intro i j
  change (Int.castRingHom (ZMod (q i))) (∑ k, w k j) = v i j
  rw [map_sum, sum_eq_single i]
  · exact hd i j
  · intro k _ hn
    exact hoff i k j hn
  · simp

theorem local_subgroup_projection {ι ι' : Type*} [Fintype ι] (q : ι → ℕ)
    (hq : Pairwise fun i j => (q i).Coprime (q j))
    (L : (i : ι) → AddSubgroup (ι' → ZMod (q i))) (i : ι) (v : ι' → ZMod (q i))
    (hv : v ∈ L i) :
    ∃ w : ι' → ℤ, (∀ k, (fun j => (w j : ZMod (q k))) ∈ L k) ∧
      ∀ j, (w j : ZMod (q i)) = v j := by
  classical
  let a (k : ι) : L k := if h : i = k then h ▸ ⟨v,hv⟩ else 0
  obtain ⟨w,hw⟩ := exists_vector_with_residues q hq fun k => (a k).val
  refine ⟨w, fun k => ?_, fun j => ?_⟩
  · have h : (fun j => (w j : ZMod (q k))) = (a k).val := funext (hw k)
    rw [h]
    exact (a k).property
  · simpa [a] using hw i j

theorem local_subgroup_high_precision {ι ι' : Type*} [Fintype ι] (q : ι → ℕ)
    (L : (i : ι) → AddSubgroup (ι' → ZMod (q i))) (i : ι) {r : ℕ}
    (hdiv : q i ∣ r) (hcop : ∀ k, k ≠ i → (q k).Coprime r) (v : ι' → ZMod r)
    (hv : (fun j => ZMod.castHom hdiv (ZMod (q i)) (v j)) ∈ L i) :
    ∃ w : ι' → ℤ, (∀ k, (fun j => (w j : ZMod (q k))) ∈ L k) ∧
      ∀ j, (w j : ZMod r) = v j := by
  classical
  let m := ∏ k ∈ univ.erase i, q k
  have hc : m.Coprime r := Nat.Coprime.prod_left fun k hk => hcop k (ne_of_mem_erase hk)
  let u : (ZMod r)ˣ := ZMod.unitOfCoprime m hc
  let w (j : ι') : ℤ := (m : ℤ) * ZMod.cast ((↑u⁻¹ : ZMod r) * v j)
  have hh (j : ι') : (w j : ZMod r) = v j := by
    simp only [w, Int.cast_mul, Int.cast_natCast, ZMod.intCast_zmod_cast]
    rw [← ZMod.coe_unitOfCoprime m hc, ← mul_assoc, ← Units.val_mul]
    change (↑(u * u⁻¹) : ZMod r) * v j = _
    simp
  refine ⟨w, ?_, hh⟩
  intro k
  by_cases he : k = i
  · subst k
    have heq (j : ι') : (w j : ZMod (q i)) = ZMod.castHom hdiv (ZMod (q i)) (v j) := by
      rw [← hh j, map_intCast]
    rwa [funext heq]
  · have hk : q k ∣ m := dvd_prod_of_mem q (mem_erase.mpr ⟨he, mem_univ k⟩)
    have hz : (fun j => (w j : ZMod (q k))) = 0 := by
      funext j
      simp only [w, Int.cast_mul, Int.cast_natCast, (ZMod.natCast_eq_zero_iff _ _).mpr hk,
        zero_mul, Pi.zero_apply]
    rw [hz]
    exact (L k).zero_mem

theorem local_subgroup_padic_approximation {ι ι' : Type*} [Fintype ι] {p : ℕ} [Fact p.Prime]
    (q : ι → ℕ) (L : (i : ι) → AddSubgroup (ι' → ZMod (q i))) (i : ι) (k : ℕ)
    (hdiv : q i ∣ p ^ k) (hcop : ∀ j, j ≠ i → (q j).Coprime (p ^ k)) (v : ι' → ℤ_[p])
    (hv : (fun j => ZMod.castHom hdiv (ZMod (q i)) (PadicInt.toZModPow k (v j))) ∈ L i) :
    ∃ w : ι' → ℤ, (∀ k, (fun j => (w j : ZMod (q k))) ∈ L k) ∧
      ∀ j, ‖(w j : ℤ_[p]) - v j‖ ≤ (p : ℝ) ^ (-k : ℤ) := by
  obtain ⟨w, hw, hres⟩ := local_subgroup_high_precision q L i hdiv hcop
    (fun j => PadicInt.toZModPow k (v j)) hv
  refine ⟨w, hw, fun j => ?_⟩
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
    map_sub, map_intCast, hres j, sub_self]

theorem local_subgroup_padic_closure {ι ι' : Type*} [Fintype ι] [Fintype ι'] {p : ℕ}
    [Fact p.Prime] (q : ι → ℕ) (L : (i : ι) → AddSubgroup (ι' → ZMod (q i)))
    (i : ι) (d : ℕ) (hdiv : q i ∣ p ^ d) (hcop : ∀ k, k ≠ i → (q k).Coprime p)
    (v : ι' → ℤ_[p])
    (hv : (fun j => ZMod.castHom hdiv (ZMod (q i)) (PadicInt.toZModPow d (v j))) ∈ L i) :
    v ∈ closure {x : ι' → ℤ_[p] | ∃ w : ι' → ℤ,
      (∀ j, x j = (w j : ℤ_[p])) ∧ ∀ k, (fun j => (w j : ZMod (q k))) ∈ L k} := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt p hε
  let k := max d n
  have hdk : d ≤ k := le_max_left _ _
  have hnk : n ≤ k := le_max_right _ _
  have hpk : q i ∣ p ^ k := hdiv.trans (pow_dvd_pow p hdk)
  have hcast (j : ι') :
      ZMod.castHom hpk (ZMod (q i)) (PadicInt.toZModPow k (v j)) =
      ZMod.castHom hdiv (ZMod (q i)) (PadicInt.toZModPow d (v j)) := by
    have hcomp : (ZMod.castHom hdiv (ZMod (q i))).comp
        (ZMod.castHom (pow_dvd_pow p hdk) (ZMod (p ^ d))) =
        ZMod.castHom hpk (ZMod (q i)) := Subsingleton.elim _ _
    rw [← hcomp, RingHom.comp_apply]
    congr 1
    exact PadicInt.cast_toZModPow d k hdk (v j)
  obtain ⟨w,hw,hnorm⟩ := local_subgroup_padic_approximation q L i k hpk
    (fun j hj => (hcop j hj).pow_right k) v (by simpa only [hcast] using hv)
  let b (j : ι') : ℤ_[p] := w j
  refine ⟨b, ⟨w, fun _ => rfl, hw⟩, ?_⟩
  rw [dist_comm, dist_eq_norm]
  have hbound : ‖b - v‖ ≤ (p : ℝ) ^ (-k : ℤ) :=
    (pi_norm_le_iff_of_nonneg (zpow_nonneg (Nat.cast_nonneg p) _)).mpr hnorm
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out (p := p.Prime)).one_lt.le
  have hpower : (p : ℝ) ^ (-k : ℤ) ≤ (p : ℝ) ^ (-n : ℤ) :=
    zpow_le_zpow_right₀ hp' (by exact_mod_cast (neg_le_neg (Int.ofNat_le.mpr hnk)))
  exact hbound.trans_lt (hpower.trans_lt hn)

theorem local_subgroup_padic_closure_iff {ι ι' : Type*} [Fintype ι] [Fintype ι'] {p : ℕ}
    [Fact p.Prime] (q : ι → ℕ) (L : (i : ι) → AddSubgroup (ι' → ZMod (q i)))
    (i : ι) (d : ℕ) (hdiv : q i ∣ p ^ d) (hcop : ∀ k, k ≠ i → (q k).Coprime p)
    (v : ι' → ℤ_[p]) :
    v ∈ closure {x : ι' → ℤ_[p] | ∃ w : ι' → ℤ,
      (∀ j, x j = (w j : ℤ_[p])) ∧ ∀ k, (fun j => (w j : ZMod (q k))) ∈ L k} ↔
    (fun j => ZMod.castHom hdiv (ZMod (q i)) (PadicInt.toZModPow d (v j))) ∈ L i := by
  constructor
  · intro hc
    have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out (p := p.Prime)).pos
    obtain ⟨b, ⟨w, hbw, hw⟩, hb⟩ := Metric.mem_closure_iff.mp hc _ (zpow_pos hp _)
    rw [dist_eq_norm] at hb
    have hval (j : ι') : (w j : ZMod (q i)) =
        ZMod.castHom hdiv (ZMod (q i)) (PadicInt.toZModPow d (v j)) := by
      have hcoord : ‖v j - b j‖ ≤ (p : ℝ) ^ (-d : ℤ) :=
        (pi_norm_le_iff_of_nonneg (zpow_nonneg hp.le _)).mp hb.le j
      have hzero := (PadicInt.norm_le_pow_iff_mem_span_pow _ _).mp hcoord
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero, hbw j,
        map_intCast] at hzero
      rw [hzero, map_intCast]
    rw [← funext hval]
    exact hw i
  · exact local_subgroup_padic_closure q L i d hdiv hcop v

def patchSubmodule {ι ι' : Type*} (q : ι → ℕ)
    (L : (i : ι) → AddSubgroup (ι' → ZMod (q i))) : Submodule ℤ (ι' → ℤ) where
  carrier := {w | ∀ k, (fun j => (w j : ZMod (q k))) ∈ L k}
  zero_mem' := by
    intro k
    have he : (fun j : ι' => ((0 : ι' → ℤ) j : ZMod (q k))) = 0 := by
      ext j
      exact Int.cast_zero
    rw [he]
    exact (L k).zero_mem
  add_mem' := by
    intro a b ha hb k
    have he : (fun j => ((a + b) j : ZMod (q k))) =
        (fun j => (a j : ZMod (q k))) + (fun j => (b j : ZMod (q k))) := by
      ext j
      exact Int.cast_add _ _
    rw [he]
    exact (L k).add_mem (ha k) (hb k)
  smul_mem' := by
    intro a b hb k
    have he : (fun j => ((a • b) j : ZMod (q k))) =
        a • (fun j => (b j : ZMod (q k))) := by
      ext j
      simp [zsmul_eq_mul]
    rw [he]
    exact (L k).zsmul_mem (hb k) a

theorem product_smul_mem_patch {ι ι' : Type*} [Fintype ι] (q : ι → ℕ)
    (L : (i : ι) → AddSubgroup (ι' → ZMod (q i))) (w : ι' → ℤ) :
    ((∏ i, q i : ℕ) : ℤ) • w ∈ patchSubmodule q L := by
  classical
  intro k
  have hq : q k ∣ ∏ i, q i := Finset.dvd_prod_of_mem q (Finset.mem_univ k)
  have hz : ((∏ i, q i : ℕ) : ZMod (q k)) = 0 := by
    obtain ⟨b, hb⟩ := hq
    rw [hb, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  have he : (fun j => (((((∏ i, q i : ℕ) : ℤ) • w) j : ℤ) : ZMod (q k))) = 0 := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast, hz, zero_mul, Pi.zero_apply]
  rw [he]
  exact (L k).zero_mem

theorem dense_patch_at_coprime_prime {ι ι' : Type*} [Fintype ι] [Fintype ι'] {p : ℕ}
    [Fact p.Prime] (q : ι → ℕ) (hq : Pairwise fun i j => (q i).Coprime (q j))
    (L : (i : ι) → AddSubgroup (ι' → ZMod (q i))) (hpq : ∀ i, (q i).Coprime p) :
    DenseRange (fun w : patchSubmodule q L => fun j => ((w : ι' → ℤ) j : ℤ_[p])) := by
  classical
  intro v
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hε
  let r : Option ι → ℕ
    | none => p ^ k
    | some i => q i
  have hr : Pairwise fun i j => (r i).Coprime (r j) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => exact ((hpq j).pow_right k).symm
    | some i =>
      cases j with
      | none => exact (hpq i).pow_right k
      | some j => exact hq (fun h => hij (congrArg some h))
  let a : (i : Option ι) → ι' → ZMod (r i)
    | none => fun j => PadicInt.toZModPow k (v j)
    | some _ => 0
  obtain ⟨w, hw⟩ := exists_vector_with_residues r hr a
  have hw₀ : w ∈ patchSubmodule q L := by
    intro i
    have hh : (fun j => (w j : ZMod (q i))) = 0 := funext (hw (some i))
    rw [hh]
    exact (L i).zero_mem
  let b (j : ι') : ℤ_[p] := w j
  refine ⟨b, ⟨⟨w, hw₀⟩, rfl⟩, ?_⟩
  rw [dist_comm, dist_eq_norm]
  have hnorm (j : ι') : ‖b j - v j‖ ≤ (p : ℝ) ^ (-k : ℤ) := by
    have hj : (w j : ZMod (p ^ k)) = PadicInt.toZModPow k (v j) := hw none j
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
      RingHom.mem_ker, map_sub]
    change PadicInt.toZModPow k (w j) - PadicInt.toZModPow k (v j) = 0
    rw [map_intCast, hj, sub_self]
  exact ((pi_norm_le_iff_of_nonneg (zpow_nonneg (Nat.cast_nonneg p) _)).mpr hnorm).trans_lt hk

theorem closure_patch_at_index {ι ι' : Type*} [Fintype ι] [Fintype ι'] {p : ℕ}
    [Fact p.Prime] (q : ι → ℕ) (L : (i : ι) → AddSubgroup (ι' → ZMod (q i)))
    (i : ι) (d : ℕ) (hdiv : q i ∣ p ^ d) (hcop : ∀ k, k ≠ i → (q k).Coprime p) :
    closure (Set.range fun w : patchSubmodule q L => fun j => ((w : ι' → ℤ) j : ℤ_[p])) =
      {v | (fun j => ZMod.castHom hdiv (ZMod (q i)) (PadicInt.toZModPow d (v j))) ∈ L i} := by
  have he : (Set.range fun w : patchSubmodule q L => fun j => ((w : ι' → ℤ) j : ℤ_[p])) =
      {x : ι' → ℤ_[p] | ∃ w : ι' → ℤ,
        (∀ j, x j = (w j : ℤ_[p])) ∧ ∀ k, (fun j => (w j : ZMod (q k))) ∈ L k} := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w, fun _ => rfl, w.property⟩
    · rintro ⟨w, hw, hL⟩
      exact ⟨⟨w, hL⟩, (funext hw).symm⟩
  rw [he]
  ext v
  exact local_subgroup_padic_closure_iff q L i d hdiv hcop v

end FiniteLatticePatching


namespace PadicLatticeResidues

noncomputable def coordinateReduction {n : Type*} {p : ℕ} [Fact p.Prime] (k : ℕ) :
    (n → ℤ_[p]) →+ (n → ZMod (p ^ k)) where
  toFun v i := PadicInt.toZModPow k (v i)
  map_zero' := by ext i; exact map_zero (PadicInt.toZModPow k)
  map_add' x y := by ext i; exact map_add (PadicInt.toZModPow k) _ _

theorem mem_iff_residue_mem_image {n : Type*} {p : ℕ} [Fact p.Prime] (k : ℕ)
    (S : AddSubgroup (n → ℤ_[p]))
    (hS : ∀ w : n → ℤ_[p], (p : ℤ_[p]) ^ k • w ∈ S) (v : n → ℤ_[p]) :
    v ∈ S ↔ coordinateReduction k v ∈ S.map (coordinateReduction k) := by
  constructor
  · intro hv
    exact ⟨v, hv, rfl⟩
  · rintro ⟨u, hu, huv⟩
    have hdvd (i : n) : (p : ℤ_[p]) ^ k ∣ (v - u) i := by
      have h := congrFun huv i
      change PadicInt.toZModPow k (u i) = PadicInt.toZModPow k (v i) at h
      rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
      change PadicInt.toZModPow k (v i - u i) = 0
      rw [map_sub, h, sub_self]
    choose z hz using hdvd
    have heq : v - u = (p : ℤ_[p]) ^ k • z := funext hz
    have hsub : v - u ∈ S := heq.symm ▸ hS z
    simpa using S.add_mem hsub hu


end PadicLatticeResidues

namespace IntegralLatticeBasis

open Matrix

theorem exists_matrix_basis {d : ℕ} (S : Submodule ℤ (Fin d → ℤ))
    (q : ℤ) (hq : q ≠ 0) (hS : ∀ v : Fin d → ℤ, q • v ∈ S) :
    ∃ B : Matrix (Fin d) (Fin d) ℤ, B.det ≠ 0 ∧
      (∀ v, v ∈ S ↔ ∃ z : Fin d → ℤ, B *ᵥ z = v) ∧
      ∃ C : Matrix (Fin d) (Fin d) ℤ, B * C = q • 1 := by
  classical
  let ιq : (Fin d → ℤ) →ₗ[ℤ] S :=
    (q • LinearMap.id).codRestrict S hS
  have hi : Function.Injective ιq := by
    intro x y h
    funext i
    apply mul_left_cancel₀ hq
    exact congrArg (fun v : S => (v : Fin d → ℤ) i) h
  have hle : Module.finrank ℤ (Fin d → ℤ) ≤ Module.finrank ℤ S :=
    LinearMap.finrank_le_finrank_of_injective hi
  have hrank : Module.finrank ℤ S = Module.finrank ℤ (Fin d → ℤ) :=
    le_antisymm (Submodule.finrank_le S) hle
  let b : Module.Basis (Fin d) ℤ S :=
    S.smithNormalFormBotBasis (Pi.basisFun ℤ (Fin d)) hrank
  let B : Matrix (Fin d) (Fin d) ℤ := fun i j => (b j : Fin d → ℤ) i
  have hmul (z : Fin d → ℤ) : B *ᵥ z = ((∑ j, z j • b j : S) : Fin d → ℤ) := by
    ext i
    simp only [Matrix.mulVec, dotProduct, B, Submodule.coe_sum, Finset.sum_apply,
      Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  have hrange (v : Fin d → ℤ) : v ∈ S ↔ ∃ z : Fin d → ℤ, B *ᵥ z = v := by
    constructor
    · intro hv
      refine ⟨fun j => b.repr ⟨v, hv⟩ j, ?_⟩
      rw [hmul, b.sum_repr]
    · rintro ⟨z, rfl⟩
      rw [hmul]
      exact (∑ j, z j • b j : S).property
  have hex (j : Fin d) : ∃ z : Fin d → ℤ, B *ᵥ z = q • Pi.single j 1 :=
    (hrange _).mp (hS _)
  choose z hz using hex
  let C : Matrix (Fin d) (Fin d) ℤ := fun i j => z j i
  have hBC : B * C = q • 1 := by
    ext i j
    have h := congrFun (hz j) i
    rw [Matrix.mul_apply]
    simpa [Matrix.mulVec, dotProduct, B, C, Pi.single_apply,
      Matrix.one_apply] using h
  have hdet := congrArg Matrix.det hBC
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at hdet
  refine ⟨B, ?_, hrange, C, hBC⟩
  intro h
  rw [h, zero_mul] at hdet
  exact pow_ne_zero _ hq hdet.symm



theorem lift_general_linear {n K : Type*} [Fintype n] [DecidableEq n] [CommRing K]
    (S : Subring K) (A : Matrix.GeneralLinearGroup n K)
    (hA : ∀ i j, (A : Matrix n n K) i j ∈ S)
    (hAi : ∀ i j, ((A⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) i j ∈ S) :
    ∃ U : Matrix.GeneralLinearGroup n S, (U : Matrix n n S).map S.subtype = A := by
  let B : Matrix n n S := fun i j => ⟨(A : Matrix n n K) i j, hA i j⟩
  let C : Matrix n n S := fun i j =>
    ⟨((A⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) i j, hAi i j⟩
  have hB : B.map S.subtype = (A : Matrix n n K) := rfl
  have hC : C.map S.subtype = ((A⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) := rfl
  have hBC : B * C = 1 := by
    apply Matrix.map_injective (f := S.subtype) Subtype.coe_injective
    change (B * C).map S.subtype = (1 : Matrix n n S).map S.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hB, hC]
    exact A.val_inv
  have hCB : C * B = 1 := by
    apply Matrix.map_injective (f := S.subtype) Subtype.coe_injective
    change (C * B).map S.subtype = (1 : Matrix n n S).map S.subtype
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hB, hC]
    exact A.inv_val
  exact ⟨⟨B, C, hBC, hCB⟩, hB⟩



def latticeRange {n K : Type*} [Fintype n] [DecidableEq n] [CommRing K]
    (S : Subring K) (A : Matrix.GeneralLinearGroup n K) : Set (n → K) :=
  Set.range fun w : n → S => (A : Matrix n n K) *ᵥ (S.subtype ∘ w)

theorem quotient_of_equal_lattices {n K : Type*} [Fintype n] [DecidableEq n] [CommRing K]
    (S : Subring K) (A B : Matrix.GeneralLinearGroup n K)
    (hab : latticeRange S A = latticeRange S B) :
    ∃ U : Matrix.GeneralLinearGroup n S, (U : Matrix n n S).map S.subtype =
      ((B⁻¹ * A : Matrix.GeneralLinearGroup n K) : Matrix n n K) := by
  have hcols (P Q : Matrix.GeneralLinearGroup n K)
      (hPQ : latticeRange S P ⊆ latticeRange S Q) :
      ∀ i j, ((Q⁻¹ * P : Matrix.GeneralLinearGroup n K) : Matrix n n K) i j ∈ S := by
    intro i j
    have he : S.subtype ∘ (Pi.single j 1 : n → S) = (Pi.single j 1 : n → K) := by
      ext k
      by_cases hj : k = j <;> simp [hj]
    have hp : (P : Matrix n n K) *ᵥ (Pi.single j 1 : n → K) ∈ latticeRange S P := by
      refine ⟨Pi.single j 1, ?_⟩
      change (P : Matrix n n K) *ᵥ (S.subtype ∘ (Pi.single j 1 : n → S)) = _
      rw [he]
    obtain ⟨w, hw⟩ := hPQ hp
    change (Q : Matrix n n K) *ᵥ (S.subtype ∘ w) =
      (P : Matrix n n K) *ᵥ (Pi.single j 1 : n → K) at hw
    have hh := congrArg (fun z => ((Q⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) *ᵥ z) hw
    simp only [Matrix.mulVec_mulVec] at hh
    have hIQ : ((Q⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) *
        (Q : Matrix n n K) = 1 := Q.inv_val
    rw [hIQ, Matrix.one_mulVec] at hh
    have hi := congrFun hh i
    rw [Matrix.mulVec_single_one] at hi
    change S.subtype (w i) =
      (((Q⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) * (P : Matrix n n K)) i j at hi
    change ((((Q⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) *
      (P : Matrix n n K)) i j) ∈ S
    rw [← hi]
    exact (w i).property
  apply lift_general_linear S (B⁻¹ * A) (hcols A B hab.le)
  rw [_root_.mul_inv_rev, inv_inv]
  exact hcols B A hab.ge



theorem closed_latticeRange {n K : Type*} [Fintype n] [DecidableEq n] [CommRing K]
    [TopologicalSpace K] [IsTopologicalRing K]
    (S : Subring K) (hS : IsClosed (S : Set K)) (A : Matrix.GeneralLinearGroup n K) :
    IsClosed (latticeRange S A) := by
  let Ai : Matrix n n K := (↑(A⁻¹ : Matrix.GeneralLinearGroup n K))
  have hAiA : Ai * (A : Matrix n n K) = 1 := A.inv_val
  have hAAi : (A : Matrix n n K) * Ai = 1 := A.val_inv
  have he : latticeRange S A = {x | ∀ i, (Ai *ᵥ x) i ∈ S} := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      change ∀ i, (Ai *ᵥ ((A : Matrix n n K) *ᵥ (S.subtype ∘ w))) i ∈ S
      rw [Matrix.mulVec_mulVec, hAiA, Matrix.one_mulVec]
      exact fun i => (w i).property
    · intro hx
      refine ⟨fun i => ⟨(Ai *ᵥ x) i, hx i⟩, ?_⟩
      change (A : Matrix n n K) *ᵥ (Ai *ᵥ x) = x
      rw [Matrix.mulVec_mulVec, hAAi, Matrix.one_mulVec]
  rw [he, show {x | ∀ i, (Ai *ᵥ x) i ∈ S} =
    ⋂ i, {x | (Ai *ᵥ x) i ∈ S} by ext x; simp]
  apply isClosed_iInter
  intro i
  apply hS.preimage
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

theorem padic_latticeRange_eq_closure {n : Type*} [Fintype n] [DecidableEq n]
    {p : ℕ} [Fact p.Prime] (A : Matrix.GeneralLinearGroup n ℚ_[p]) :
    closure (Set.range fun w : n → ℤ =>
      (A : Matrix n n ℚ_[p]) *ᵥ (fun i => (w i : ℚ_[p]))) =
      latticeRange (PadicInt.subring p) A := by
  let f (w : n → ℤ_[p]) := (A : Matrix n n ℚ_[p]) *ᵥ (PadicInt.Coe.ringHom ∘ w)
  let g (w : n → ℤ) : n → ℤ_[p] := fun i => w i
  have hf : Continuous f := by
    apply continuous_pi
    intro i
    simp only [f, Matrix.mulVec, dotProduct, Function.comp_apply]
    have hc : Continuous (PadicInt.Coe.ringHom : ℤ_[p] → ℚ_[p]) := continuous_subtype_val
    fun_prop
  have hg : DenseRange g := DenseRange.piMap (fun _ => PadicInt.denseRange_intCast)
  have hr : Set.range f = latticeRange (PadicInt.subring p) A := rfl
  have hc : IsClosed (Set.range f) := by
    rw [hr]
    apply closed_latticeRange
    exact isClosed_le continuous_norm continuous_const
  change closure (Set.range (f ∘ g)) = latticeRange (PadicInt.subring p) A
  rw [← hr, Set.range_comp]
  exact le_antisymm (closure_minimal (Set.image_subset_range f _) hc)
    (hf.range_subset_closure_image_dense hg)



theorem global_basis_with_local_changes {d : ℕ} (S : Submodule ℤ (Fin d → ℤ))
    (q : ℤ) (hq : q ≠ 0) (hS : ∀ v : Fin d → ℤ, q • v ∈ S)
    (A : (p : ℕ) → [Fact p.Prime] → Matrix.GeneralLinearGroup (Fin d) ℚ_[p])
    (hA : ∀ (p : ℕ) [_hp : Fact p.Prime],
      closure (Set.range fun w : S => fun i => ((w : Fin d → ℤ) i : ℚ_[p])) =
        latticeRange (PadicInt.subring p) (A p)) :
    ∃ B : Matrix (Fin d) (Fin d) ℤ, B.det ≠ 0 ∧
      (∀ v, v ∈ S ↔ ∃ z : Fin d → ℤ, B *ᵥ z = v) ∧
      (∀ (p : ℕ) [_hp : Fact p.Prime],
        ∃ U : Matrix.GeneralLinearGroup (Fin d) ℤ_[p],
          B.map (Int.castRingHom ℚ_[p]) = (A p : Matrix (Fin d) (Fin d) ℚ_[p]) *
            (U : Matrix (Fin d) (Fin d) ℤ_[p]).map PadicInt.Coe.ringHom) := by
  obtain ⟨B, hdet, hB, _⟩ := exists_matrix_basis S q hq hS
  refine ⟨B, hdet, hB, ?_⟩
  intro p hp
  let D := B.map (Int.castRingHom ℚ_[p])
  have hD : D.det ≠ 0 := by
    change (B.map fun x : ℤ => (x : ℚ_[p])).det ≠ 0
    rw [← Int.cast_det]
    exact_mod_cast hdet
  let G := Matrix.GeneralLinearGroup.mkOfDetNeZero D hD
  have hr : (Set.range fun w : Fin d → ℤ =>
      (G : Matrix (Fin d) (Fin d) ℚ_[p]) *ᵥ (fun i => (w i : ℚ_[p]))) =
      (Set.range fun w : S => fun i => ((w : Fin d → ℤ) i : ℚ_[p])) := by
    have hm (w : Fin d → ℤ) (i : Fin d) :
        ((G : Matrix (Fin d) (Fin d) ℚ_[p]) *ᵥ (fun j => (w j : ℚ_[p]))) i =
          ((B *ᵥ w) i : ℚ_[p]) := (RingHom.map_mulVec (Int.castRingHom ℚ_[p]) B w i).symm
    ext v
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨⟨B *ᵥ z, (hB _).mpr ⟨z, rfl⟩⟩, funext fun i => (hm z i).symm⟩
    · rintro ⟨w, rfl⟩
      obtain ⟨z, hz⟩ := (hB _).mp w.property
      exact ⟨z, funext fun i => (hm z i).trans (congrArg (fun v : Fin d → ℤ => (v i : ℚ_[p])) hz)⟩
  have heq : latticeRange (PadicInt.subring p) G = latticeRange (PadicInt.subring p) (A p) := by
    rw [← padic_latticeRange_eq_closure G, hr, hA p]
  obtain ⟨U, hU⟩ := quotient_of_equal_lattices _ G (A p) heq
  refine ⟨U, ?_⟩
  change (G : Matrix (Fin d) (Fin d) ℚ_[p]) = (A p : Matrix _ _ _) *
    (U : Matrix (Fin d) (Fin d) (PadicInt.subring p)).map (PadicInt.subring p).subtype
  rw [hU]
  have hh : A p * ((A p)⁻¹ * G) = G := by group
  exact (congrArg (fun V : Matrix.GeneralLinearGroup (Fin d) ℚ_[p] =>
    (V : Matrix (Fin d) (Fin d) ℚ_[p])) hh).symm


end IntegralLatticeBasis

namespace PrimitiveGenusDescent

open Matrix

theorem rational_integral (x : ℚ)
    (h : ∀ (p : ℕ) [Fact p.Prime], ‖(x : ℚ_[p])‖ ≤ 1) :
    (x.num : ℚ) = x := by
  apply Rat.coe_int_num_of_den_eq_one
  by_contra hden
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hden
  let : Fact p.Prime := ⟨hp⟩
  have hn := (Padic.norm_rat_le_one_iff_padicValuation_le_one p).mp (h p)
  exact (Rat.padicValuation_le_one_iff.mp hn) hdvd

theorem ternary_primitive (x : Fin 3 → ℤ)
    (h : ∀ (p : ℕ) [Fact p.Prime], ∃ i, IsUnit (x i : ℤ_[p])) :
    Int.gcd (x 0) (Int.gcd (x 1) (x 2)) = 1 := by
  by_contra hgcd
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hgcd
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨i, hu⟩ := h p
  have hg : (p : ℤ) ∣ (Int.gcd (x 0) (Int.gcd (x 1) (x 2)) : ℤ) :=
    Int.natCast_dvd_natCast.mpr hdvd
  have hx : (p : ℤ) ∣ x i := by
    fin_cases i
    · exact hg.trans (Int.gcd_dvd_left _ _)
    · exact hg.trans ((Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_left _ _))
    · exact hg.trans ((Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_right _ _))
  exact (not_lt_of_ge (PadicInt.isUnit_iff.mp hu).ge)
    ((PadicInt.norm_int_lt_one_iff_dvd _).mpr hx)

theorem certify_integral_genus
    (Q : Matrix (Fin 3) (Fin 3) ℤ) (A : Matrix (Fin 3) (Fin 3) ℚ)
    (x : Fin 3 → ℚ) (m : ℤ) (hs : A.IsSymm)
    (T : Matrix.GeneralLinearGroup (Fin 3) ℚ)
    (hT : A = (T : Matrix _ _ _)ᵀ * Q.map (Int.castRingHom ℚ) * (T : Matrix _ _ _))
    (hx : x ⬝ᵥ (A *ᵥ x) = (m : ℚ))
    (hloc : ∀ (p : ℕ) [Fact p.Prime],
      ∃ U : Matrix.GeneralLinearGroup (Fin 3) ℤ_[p], ∃ y : Fin 3 → ℤ_[p],
        A.map (Rat.castHom ℚ_[p]) =
          (((U : Matrix _ _ _)ᵀ * Q.map (Int.castRingHom ℤ_[p]) * (U : Matrix _ _ _)).map
            PadicInt.Coe.ringHom) ∧
        (∀ i, (x i : ℚ_[p]) = (y i : ℚ_[p])) ∧ ∃ i, IsUnit (y i)) :
    ∃ M : Matrix (Fin 3) (Fin 3) ℤ, ∃ v : Fin 3 → ℤ,
      M.IsSymm ∧
      (∃ V : Matrix.GeneralLinearGroup (Fin 3) ℝ,
        M.map (Int.castRingHom ℝ) = (V : Matrix _ _ _)ᵀ *
          Q.map (Int.castRingHom ℝ) * (V : Matrix _ _ _)) ∧
      (∀ (p : ℕ) [Fact p.Prime], ∃ U : Matrix.GeneralLinearGroup (Fin 3) ℤ_[p],
        M.map (Int.castRingHom ℤ_[p]) = (U : Matrix _ _ _)ᵀ *
          Q.map (Int.castRingHom ℤ_[p]) * (U : Matrix _ _ _)) ∧
      v ⬝ᵥ (M *ᵥ v) = m ∧ Int.gcd (v 0) (Int.gcd (v 1) (v 2)) = 1 := by
  let M : Matrix (Fin 3) (Fin 3) ℤ := fun i j => (A i j).num
  let v : Fin 3 → ℤ := fun i => (x i).num
  have hM : M.map (Int.castRingHom ℚ) = A := by
    ext i j
    apply rational_integral
    intro p hp
    obtain ⟨U, y, hU, hy, hprim⟩ := hloc p
    have hentry := congrArg (fun B : Matrix (Fin 3) (Fin 3) ℚ_[p] => B i j) hU
    change (A i j : ℚ_[p]) = _ at hentry
    rw [hentry]
    exact PadicInt.norm_le_one _
  have hv (i : Fin 3) : (v i : ℚ) = x i := by
    apply rational_integral
    intro p hp
    obtain ⟨U, y, hU, hy, hprim⟩ := hloc p
    rw [hy i]
    exact PadicInt.norm_le_one _
  have hcast {F : Type} [DivisionRing F] [CharZero F] :
      M.map (Int.castRingHom F) = A.map (Rat.castHom F) := by
    ext i j
    have hij : (M i j : ℚ) = A i j :=
      congrArg (fun B : Matrix (Fin 3) (Fin 3) ℚ => B i j) hM
    simpa using congrArg (Rat.castHom F) hij
  refine ⟨M, v, ?_, ?_, ?_, ?_, ?_⟩
  · change Mᵀ = M
    apply Matrix.map_injective (f := Int.castRingHom ℚ) (Int.cast_injective (α := ℚ))
    change Mᵀ.map (Int.castRingHom ℚ) = M.map (Int.castRingHom ℚ)
    rw [Matrix.transpose_map, hM]
    exact hs
  · refine ⟨Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) T, ?_⟩
    rw [hcast (F := ℝ)]
    have h := congrArg (fun B : Matrix (Fin 3) (Fin 3) ℚ =>
      B.map (Rat.castHom ℝ)) hT
    simp only [Matrix.map_mul, Matrix.transpose_map] at h
    rw [h]
    congr 2
  · intro p hp
    obtain ⟨U, y, hU, hy, hprim⟩ := hloc p
    refine ⟨U, Matrix.map_injective (f := PadicInt.Coe.ringHom) Subtype.coe_injective ?_⟩
    change ((M.map (Int.castRingHom ℤ_[p])).map PadicInt.Coe.ringHom) =
      (((U : Matrix _ _ _)ᵀ * Q.map (Int.castRingHom ℤ_[p]) *
        (U : Matrix _ _ _)).map PadicInt.Coe.ringHom)
    rw [← hU, ← hcast (F := ℚ_[p])]
    rfl
  · apply Int.cast_injective (α := ℚ)
    rw [show ((v ⬝ᵥ (M *ᵥ v) : ℤ) : ℚ) = (Int.castRingHom ℚ) (v ⬝ᵥ (M *ᵥ v)) by rfl,
      RingHom.map_dotProduct]
    have hv' : Int.castRingHom ℚ ∘ v = x := funext hv
    have hmul : Int.castRingHom ℚ ∘ (M *ᵥ v) = A *ᵥ x := by
      funext i
      simp only [Function.comp_apply, RingHom.map_mulVec, hM, hv']
    rw [hv', hmul]
    exact hx
  · apply ternary_primitive
    intro p hp
    obtain ⟨U, y, hU, hy, i, hi⟩ := hloc p
    refine ⟨i, ?_⟩
    have hi' : (v i : ℤ_[p]) = y i := by
      apply Subtype.coe_injective (p := fun z : ℚ_[p] => ‖z‖ ≤ 1)
      simpa only [PadicInt.coe_intCast, Rat.cast_intCast] using
        (congrArg (fun z : ℚ => (z : ℚ_[p])) (hv i)).trans (hy i)
    exact hi' ▸ hi


end PrimitiveGenusDescent

/-! Equal nonzero norms can be matched by one reflection, with a sign change if necessary. -/

namespace PrimitiveGenusReflection

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private def reflectMap (B : LinearMap.BilinForm K V) (v : V) : V →ₗ[K] V :=
  LinearMap.id - (((2 / B v v) : K) • B v).smulRight v

private theorem reflect_apply (B : LinearMap.BilinForm K V) (v x : V) :
    reflectMap B v x = x - (2 * B v x / B v v) • v := by
  simp [reflectMap, div_mul_eq_mul_div, smul_eq_mul]

private theorem reflect_involutive (B : LinearMap.BilinForm K V) {v : V} (hv : B v v ≠ 0) :
    Function.Involutive (reflectMap B v) := by
  intro x
  have he : B v (reflectMap B v x) = -B v x := by
    rw [reflect_apply, map_sub, map_smul, smul_eq_mul]
    field_simp
    ring
  rw [reflect_apply, he, reflect_apply, mul_neg, neg_div, neg_smul, sub_neg_eq_add, sub_add_cancel]

private theorem reflect_preserves (B : LinearMap.BilinForm K V) (hSymm : ∀ x y, B x y = B y x)
    {v : V} (hv : B v v ≠ 0) (x y : V) :
    B (reflectMap B v x) (reflectMap B v y) = B x y := by
  simp only [reflect_apply, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hSymm x v]
  field_simp
  ring

theorem exists_isometry_of_equal_nonzero_norm [CharZero K] (B : LinearMap.BilinForm K V)
    (hSymm : ∀ x y, B x y = B y x) (x y : V)
    (h : B x x = B y y) (hn : B x x ≠ 0) :
    ∃ e : V ≃ₗ[K] V, e x = y ∧ ∀ a b, B (e a) (e b) = B a b := by
  by_cases hdiff : B (x-y) (x-y) = 0
  · have hsum : B (x+y) (x+y) ≠ 0 := by
      have hh : B (x+y) (x+y) + B (x-y) (x-y) = 4 * B x x := by
        simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
        rw [← h]
        ring
      rw [hdiff, add_zero] at hh
      rw [hh]
      exact mul_ne_zero (by norm_num) hn
    let E := LinearEquiv.ofInvolutive (reflectMap B (x+y)) (reflect_involutive B hsum)
    have he : reflectMap B (x+y) x = -y := by
      have heq : 2 * B (x+y) x = B (x+y) (x+y) := by
        simp only [map_add, LinearMap.add_apply]
        rw [hSymm x y, ← h]
        ring
      rw [reflect_apply, heq, div_self hsum, one_smul]
      abel
    refine ⟨E.trans (LinearEquiv.neg K), ?_, ?_⟩
    · change -reflectMap B (x+y) x = y
      rw [he, neg_neg]
    · intro a b
      change B (-reflectMap B (x+y) a) (-reflectMap B (x+y) b) = B a b
      simp only [map_neg, LinearMap.neg_apply, neg_neg]
      exact reflect_preserves B hSymm hsum a b
  · let E := LinearEquiv.ofInvolutive (reflectMap B (x-y)) (reflect_involutive B hdiff)
    refine ⟨E, ?_, reflect_preserves B hSymm hdiff⟩
    change reflectMap B (x-y) x = y
    have heq : 2 * B (x-y) x = B (x-y) (x-y) := by
      simp only [map_sub, LinearMap.sub_apply]
      rw [hSymm x y, ← h]
      ring
    rw [reflect_apply, heq, div_self hdiff, one_smul]
    abel

end PrimitiveGenusReflection


namespace GlobalIntegralPatching

open FiniteLatticePatching PadicLatticeResidues

theorem exists_integral_patch {n : Type*} [Fintype n] (F : Finset ℕ)
    (hF : ∀ p ∈ F, Nat.Prime p) (k : ℕ → ℕ)
    (S : (p : ℕ) → [Fact p.Prime] → AddSubgroup (n → ℤ_[p]))
    (hS : ∀ (p : ℕ) [Fact p.Prime], ∀ v : n → ℤ_[p], (p : ℤ_[p]) ^ k p • v ∈ S p)
    (hout : ∀ (p : ℕ) [Fact p.Prime], p ∉ F → S p = ⊤) :
    ∃ T : Submodule ℤ (n → ℤ), ∃ q : ℤ, q ≠ 0 ∧
      (∀ v : n → ℤ, q • v ∈ T) ∧
      (∀ v : n → ℤ, v ∈ T ↔
        ∀ (p : ℕ) [Fact p.Prime], (fun j => (v j : ℤ_[p])) ∈ S p) ∧
      (∀ (p : ℕ) [Fact p.Prime],
        closure (Set.range fun w : T => fun j => ((w : n → ℤ) j : ℤ_[p])) = (S p : Set _)) := by
  classical
  let I := {p : ℕ // p ∈ F}
  let q (i : I) := i.val ^ k i.val
  let L (i : I) : AddSubgroup (n → ZMod (q i)) :=
    let : Fact (Nat.Prime i.val) := ⟨hF i.val i.property⟩
    (S i.val).map (coordinateReduction (k i.val))
  have hq : Pairwise fun i j : I => (q i).Coprime (q j) := by
    intro i j hij
    have hd : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    exact (((Nat.coprime_primes (hF i.val i.property) (hF j.val j.property)).mpr hd).pow_left _).pow_right _
  let T := patchSubmodule q L
  refine ⟨T, (∏ i, q i : ℕ), ?_, product_smul_mem_patch q L, ?_, ?_⟩
  · have hn : (∏ i, q i : ℕ) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hF i.val i.property).ne_zero
    exact_mod_cast hn
  · intro v
    have hlocal (i : I) [Fact (Nat.Prime i.val)] :
        (fun j => (v j : ZMod (q i))) ∈ L i ↔ (fun j => (v j : ℤ_[i.val])) ∈ S i.val := by
      have hc : (fun j => (v j : ZMod (q i))) =
          coordinateReduction (k i.val) (fun j => (v j : ℤ_[i.val])) := by
        ext j
        exact (map_intCast (PadicInt.toZModPow (k i.val)) (v j)).symm
      rw [hc]
      exact (mem_iff_residue_mem_image (k i.val) (S i.val) (hS i.val) _).symm
    constructor
    · intro hv p hp
      by_cases hi : p ∈ F
      · let i : I := ⟨p, hi⟩
        exact (hlocal i).mp (hv i)
      · rw [hout p hi]
        simp
    · intro hv i
      let : Fact (Nat.Prime i.val) := ⟨hF i.val i.property⟩
      exact (hlocal i).mpr (hv i.val)
  intro p hp
  by_cases h : p ∈ F
  · let i : I := ⟨p, h⟩
    have hc : ∀ j : I, j ≠ i → (q j).Coprime p := by
      intro j hj
      exact ((Nat.coprime_primes (hF j.val j.property) hp.out).mpr
        (fun hji => hj (Subtype.ext hji))).pow_left _
    have he := closure_patch_at_index q L i (k p) (dvd_refl (p ^ k p)) hc
    change closure (Set.range fun w : T => fun j => ((w : n → ℤ) j : ℤ_[p])) = _ at he
    rw [he]
    ext v
    have hi : ZMod.castHom (dvd_refl (p ^ k p)) (ZMod (p ^ k p)) = RingHom.id _ :=
      Subsingleton.elim _ _
    change (fun j => ZMod.castHom (dvd_refl (p ^ k p)) (ZMod (p ^ k p))
      (PadicInt.toZModPow (k p) (v j))) ∈ (S p).map (coordinateReduction (k p)) ↔ v ∈ S p
    rw [hi]
    exact (mem_iff_residue_mem_image (k p) (S p) (hS p) v).symm
  · have hc : ∀ j : I, (q j).Coprime p := by
      intro j
      exact ((Nat.coprime_primes (hF j.val j.property) hp.out).mpr
        (fun hj => h (hj ▸ j.property))).pow_left _
    rw [(dense_patch_at_coprime_prime q hq L hc).closure_range, hout p h]
    rfl

theorem closure_padic_field_of_integral_closure {n : Type*} {p : ℕ} [Fact p.Prime]
    (T : Submodule ℤ (n → ℤ)) (W : Set (n → ℤ_[p]))
    (hT : closure (Set.range fun w : T => fun j => ((w : n → ℤ) j : ℤ_[p])) = W) :
    closure (Set.range fun w : T => fun j => ((w : n → ℤ) j : ℚ_[p])) =
      (fun v : n → ℤ_[p] => fun i => (v i : ℚ_[p])) '' W := by
  let f (v : n → ℤ_[p]) (i : n) : ℚ_[p] := v i
  let g (w : T) (i : n) : ℤ_[p] := (w : n → ℤ) i
  have hc : IsClosed {x : ℚ_[p] | ‖x‖ ≤ 1} := isClosed_le continuous_norm continuous_const
  have he : Topology.IsClosedEmbedding f := Topology.IsClosedEmbedding.piMap fun _ => hc.isClosedEmbedding_subtypeVal
  change closure (Set.range (f ∘ g)) = f '' W
  rw [Set.range_comp, he.closure_image_eq, hT]




open IntegralLatticeBasis Matrix

noncomputable def padicVectorEmbedding {n : Type*} {p : ℕ} [Fact p.Prime] :
    (n → ℤ_[p]) →+ (n → ℚ_[p]) where
  toFun v i := v i
  map_zero' := by ext i; exact map_zero PadicInt.Coe.ringHom
  map_add' x y := by ext i; exact map_add PadicInt.Coe.ringHom (x i) (y i)

noncomputable def integralPart {n : Type*} [Fintype n] [DecidableEq n]
    {p : ℕ} [Fact p.Prime] (A : Matrix.GeneralLinearGroup n ℚ_[p]) :
    AddSubgroup (n → ℤ_[p]) :=
  (AddMonoidHom.range (((A : Matrix n n ℚ_[p]).mulVecLin.toAddMonoidHom).comp
    padicVectorEmbedding)).comap padicVectorEmbedding

theorem mem_integralPart {n : Type*} [Fintype n] [DecidableEq n]
    {p : ℕ} [Fact p.Prime] (A : Matrix.GeneralLinearGroup n ℚ_[p]) (v : n → ℤ_[p]) :
    v ∈ integralPart A ↔ padicVectorEmbedding v ∈ latticeRange (PadicInt.subring p) A := by
  rfl

theorem image_integralPart {n : Type*} [Fintype n] [DecidableEq n]
    {p : ℕ} [Fact p.Prime] (A : Matrix.GeneralLinearGroup n ℚ_[p])
    (hA : latticeRange (PadicInt.subring p) A ⊆ Set.range padicVectorEmbedding) :
    padicVectorEmbedding '' (integralPart A : Set (n → ℤ_[p])) =
      latticeRange (PadicInt.subring p) A := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (mem_integralPart A v).mp hv
  · intro hx
    obtain ⟨v, rfl⟩ := hA hx
    exact ⟨v, (mem_integralPart A v).mpr hx, rfl⟩

theorem patch_integral_matrix_lattices {d : ℕ} (F : Finset ℕ)
    (hF : ∀ p ∈ F, Nat.Prime p) (k : ℕ → ℕ)
    (A : (p : ℕ) → [Fact p.Prime] → Matrix.GeneralLinearGroup (Fin d) ℚ_[p])
    (hin : ∀ (p : ℕ) [Fact p.Prime],
      latticeRange (PadicInt.subring p) (A p) ⊆ Set.range padicVectorEmbedding)
    (hpowers : ∀ (p : ℕ) [Fact p.Prime], ∀ v : Fin d → ℤ_[p],
      padicVectorEmbedding ((p : ℤ_[p]) ^ k p • v) ∈ latticeRange (PadicInt.subring p) (A p))
    (hout : ∀ (p : ℕ) [Fact p.Prime], p ∉ F →
      Set.range padicVectorEmbedding ⊆ latticeRange (PadicInt.subring p) (A p)) :
    ∃ B : Matrix (Fin d) (Fin d) ℤ, B.det ≠ 0 ∧
      (∀ v : Fin d → ℤ, (∃ z : Fin d → ℤ, B *ᵥ z = v) ↔
        ∀ (p : ℕ) [Fact p.Prime], (fun i => (v i : ℚ_[p])) ∈ latticeRange (PadicInt.subring p) (A p)) ∧
      (∀ (p : ℕ) [Fact p.Prime],
        ∃ U : Matrix.GeneralLinearGroup (Fin d) ℤ_[p],
          B.map (Int.castRingHom ℚ_[p]) = (A p : Matrix (Fin d) (Fin d) ℚ_[p]) *
            (U : Matrix (Fin d) (Fin d) ℤ_[p]).map PadicInt.Coe.ringHom) := by
  let S (p : ℕ) [Fact p.Prime] := integralPart (A p)
  have hS (p : ℕ) [Fact p.Prime] (v : Fin d → ℤ_[p]) :
      (p : ℤ_[p]) ^ k p • v ∈ S p := (mem_integralPart (A p) _).mpr (hpowers p v)
  have he (p : ℕ) [Fact p.Prime] (hp : p ∉ F) : S p = ⊤ := by
    apply eq_top_iff.mpr
    intro v _
    exact (mem_integralPart (A p) v).mpr (hout p hp ⟨v, rfl⟩)
  obtain ⟨T, q, hq, hg, hmem, hcl⟩ := exists_integral_patch F hF k S hS he
  have hc (p : ℕ) [Fact p.Prime] :
      closure (Set.range fun w : T => fun i => ((w : Fin d → ℤ) i : ℚ_[p])) =
        latticeRange (PadicInt.subring p) (A p) := by
    rw [closure_padic_field_of_integral_closure T (S p : Set (Fin d → ℤ_[p])) (hcl p)]
    change padicVectorEmbedding '' (integralPart (A p) : Set (Fin d → ℤ_[p])) = _
    exact image_integralPart (A p) (hin p)
  obtain ⟨B, hB, hspan, hloc⟩ := global_basis_with_local_changes T q hq hg A hc
  refine ⟨B, hB, fun v => (hspan v).symm.trans ((hmem v).trans ?_), hloc⟩
  constructor
  · intro hv p hp
    exact (mem_integralPart (A p) _).mp (hv p)
  · intro hv p hp
    exact (mem_integralPart (A p) _).mpr (hv p)




theorem clear_padic_matrix_denominators {n : Type*} [Fintype n]
    {p : ℕ} [Fact p.Prime] (M : Matrix n n ℚ_[p]) :
    ∃ k : ℕ, ∀ i j, ‖(p : ℚ_[p]) ^ k * M i j‖ ≤ 1 := by
  classical
  have hex (i j : n) : ∃ k : ℕ, (p : ℝ) ^ (-k : ℤ) < (‖M i j‖ + 1)⁻¹ :=
    PadicInt.exists_pow_neg_lt p (by positivity)
  choose k hk using hex
  let K := (Finset.univ : Finset (n × n)).sup fun x => k x.1 x.2
  refine ⟨K, fun i j => ?_⟩
  have hkK : k i j ≤ K := Finset.le_sup (f := fun x : n × n => k x.1 x.2) (Finset.mem_univ (i, j))
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out (p := p.Prime)).one_lt.le
  have hmono : (p : ℝ) ^ (-K : ℤ) ≤ (p : ℝ) ^ (-k i j : ℤ) :=
    zpow_le_zpow_right₀ hp (by exact_mod_cast neg_le_neg (Int.ofNat_le.mpr hkK))
  rw [norm_mul, Padic.norm_p_pow]
  have hlt := hmono.trans_lt (hk i j)
  rw [← one_div] at hlt
  have hbound : (p : ℝ) ^ (-K : ℤ) * (‖M i j‖ + 1) < 1 :=
    (lt_div_iff₀ (by positivity : 0 < ‖M i j‖ + 1)).mp hlt
  exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (by positivity)).trans hbound.le

theorem integral_matrix_mulVec {n : Type*} [Fintype n]
    {p : ℕ} [Fact p.Prime] (M : Matrix n n ℚ_[p])
    (hM : ∀ i j, ‖M i j‖ ≤ 1) (v : n → ℤ_[p]) :
    M *ᵥ padicVectorEmbedding v ∈ Set.range padicVectorEmbedding := by
  let N : Matrix n n ℤ_[p] := fun i j => ⟨M i j, hM i j⟩
  refine ⟨N *ᵥ v, ?_⟩
  ext i
  exact RingHom.map_mulVec (PadicInt.Coe.ringHom : ℤ_[p] →+* ℚ_[p]) N v i

theorem matrix_lattice_contains_prime_power {n : Type*} [Fintype n] [DecidableEq n]
    {p : ℕ} [Fact p.Prime] (A : Matrix.GeneralLinearGroup n ℚ_[p]) :
    ∃ k : ℕ, ∀ v : n → ℤ_[p],
      padicVectorEmbedding ((p : ℤ_[p]) ^ k • v) ∈ latticeRange (PadicInt.subring p) A := by
  let C : Matrix n n ℚ_[p] := ↑(A⁻¹ : Matrix.GeneralLinearGroup n ℚ_[p])
  obtain ⟨k, hk⟩ := clear_padic_matrix_denominators C
  refine ⟨k, fun v => ?_⟩
  have hM : ∀ i j, ‖(((p : ℚ_[p]) ^ k) • C) i j‖ ≤ 1 := hk
  obtain ⟨w, hw⟩ := integral_matrix_mulVec ((p : ℚ_[p]) ^ k • C) hM v
  refine ⟨w, ?_⟩
  change (A : Matrix n n ℚ_[p]) *ᵥ padicVectorEmbedding w =
    padicVectorEmbedding ((p : ℤ_[p]) ^ k • v)
  rw [hw, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  have hh : (A : Matrix n n ℚ_[p]) * C = 1 := A.val_inv
  rw [hh, Matrix.one_mulVec]
  ext i
  change _ = PadicInt.Coe.ringHom (((p : ℤ_[p]) ^ k) * v i)
  rw [map_mul, map_pow, map_natCast]
  rfl




theorem exists_common_padic_denominator {n : Type*} [Fintype n] (F : Finset ℕ)
    (hF : ∀ p ∈ F, Nat.Prime p)
    (M : (p : ℕ) → [Fact p.Prime] → Matrix n n ℚ_[p]) :
    ∃ D : ℕ, D ≠ 0 ∧
      (∀ (p : ℕ) [Fact p.Prime], p ∈ F → ∀ i j, ‖(D : ℚ_[p]) * M p i j‖ ≤ 1) ∧
      (∀ (p : ℕ) [Fact p.Prime], p ∉ F → IsUnit (D : ℤ_[p])) := by
  classical
  let I := {p : ℕ // p ∈ F}
  have hex (i : I) : ∃ k : ℕ,
      let : Fact i.val.Prime := ⟨hF _ i.property⟩
      ∀ a b, ‖(i.val : ℚ_[i.val]) ^ k * M i.val a b‖ ≤ 1 := by
    let : Fact i.val.Prime := ⟨hF _ i.property⟩
    exact clear_padic_matrix_denominators (M i.val)
  choose k hk using hex
  let f (i : I) := i.val ^ k i
  let D := ∏ i, f i
  refine ⟨D, Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hF _ i.property).ne_zero), ?_, ?_⟩
  · intro p hp hpF a b
    let i : I := ⟨p, hpF⟩
    have hd : p ^ k i ∣ D := Finset.dvd_prod_of_mem f (Finset.mem_univ i)
    obtain ⟨b', hb'⟩ := hd
    have hscale : ‖(p : ℚ_[p]) ^ k i * M p a b‖ ≤ 1 := hk i a b
    have hnorm : ‖(b' : ℚ_[p])‖ ≤ 1 := PadicInt.norm_le_one (b' : ℤ_[p])
    rw [hb', Nat.cast_mul, Nat.cast_pow, mul_right_comm, norm_mul]
    simpa using mul_le_mul hscale hnorm (norm_nonneg _) zero_le_one
  · intro p hp hpF
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    have hcop (i : I) : (f i).Coprime p :=
      ((Nat.coprime_primes (hF _ i.property) hp.out).mpr
        (fun hi => hpF (hi ▸ i.property))).pow_left _
    have hcopD : D.Coprime p := Nat.Coprime.prod_left (fun i _ => hcop i)
    exact hcopD.symm




theorem patch_matrix_lattices {d : ℕ} (F : Finset ℕ)
    (hF : ∀ p ∈ F, Nat.Prime p)
    (A : (p : ℕ) → [Fact p.Prime] → Matrix.GeneralLinearGroup (Fin d) ℚ_[p])
    (hout : ∀ (p : ℕ) [Fact p.Prime], p ∉ F → A p = 1) :
    ∃ (D : ℕ) (B : Matrix (Fin d) (Fin d) ℤ) (hD : D ≠ 0), B.det ≠ 0 ∧
      (∀ v : Fin d → ℤ, (∃ z : Fin d → ℤ, B *ᵥ z = v) ↔
        ∀ (p : ℕ) [Fact p.Prime], (fun i => (v i : ℚ_[p])) ∈
          latticeRange (PadicInt.subring p)
            (Matrix.GeneralLinearGroup.scalar (Fin d) (Units.mk0 (D : ℚ_[p]) (by exact_mod_cast hD)) * A p)) ∧
      (∀ (p : ℕ) [Fact p.Prime],
        ∃ U : Matrix.GeneralLinearGroup (Fin d) ℤ_[p],
          B.map (Int.castRingHom ℚ_[p]) = (D : ℚ_[p]) •
            ((A p : Matrix (Fin d) (Fin d) ℚ_[p]) *
              (U : Matrix (Fin d) (Fin d) ℤ_[p]).map PadicInt.Coe.ringHom)) := by
  classical
  obtain ⟨D, hD, hin, hunit⟩ := exists_common_padic_denominator (n := Fin d) F hF (fun p _ => (A p : Matrix _ _ _))
  let G (p : ℕ) [Fact p.Prime] :=
    Matrix.GeneralLinearGroup.scalar (Fin d) (Units.mk0 (D : ℚ_[p]) (by exact_mod_cast hD)) * A p
  have hG (p : ℕ) [Fact p.Prime] :
      (G p : Matrix (Fin d) (Fin d) ℚ_[p]) = (D : ℚ_[p]) • (A p : Matrix _ _ _) := by
    change Matrix.scalar (Fin d) (D : ℚ_[p]) * (A p : Matrix _ _ _) = _
    rw [Matrix.scalar_apply]
    ext i j
    rw [Matrix.diagonal_mul]
    rfl
  have hg (p : ℕ) [Fact p.Prime] :
      latticeRange (PadicInt.subring p) (G p) ⊆ Set.range padicVectorEmbedding := by
    rintro _ ⟨v, rfl⟩
    apply integral_matrix_mulVec
    intro i j
    rw [hG]
    by_cases hp : p ∈ F
    · exact hin p hp i j
    · rw [hout p hp]
      change ‖(D : ℚ_[p]) * (1 : Matrix (Fin d) (Fin d) ℚ_[p]) i j‖ ≤ 1
      rw [Matrix.one_apply]
      split
      · rw [mul_one]
        exact PadicInt.norm_le_one (D : ℤ_[p])
      · simp
  have hq (p : ℕ) [Fact p.Prime] (hp : p ∉ F) :
      Set.range padicVectorEmbedding ⊆ latticeRange (PadicInt.subring p) (G p) := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨u, hu⟩ := hunit p hp
    refine ⟨(↑u⁻¹ : ℤ_[p]) • v, ?_⟩
    change (G p : Matrix (Fin d) (Fin d) ℚ_[p]) *ᵥ padicVectorEmbedding ((↑u⁻¹ : ℤ_[p]) • v) =
      padicVectorEmbedding v
    rw [hG, hout p hp]
    change ((D : ℚ_[p]) • 1) *ᵥ _ = _
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    ext i
    change (D : ℚ_[p]) * PadicInt.Coe.ringHom ((↑u⁻¹ : ℤ_[p]) * v i) = PadicInt.Coe.ringHom (v i)
    rw [← PadicInt.coe_natCast, ← hu]
    change PadicInt.Coe.ringHom (↑u : ℤ_[p]) * PadicInt.Coe.ringHom ((↑u⁻¹ : ℤ_[p]) * v i) = _
    rw [← map_mul, ← mul_assoc, Units.mul_inv, one_mul]
  have hex (p : ℕ) : ∃ k : ℕ, ∀ [Fact p.Prime], ∀ v : Fin d → ℤ_[p],
      padicVectorEmbedding ((p : ℤ_[p]) ^ k • v) ∈ latticeRange (PadicInt.subring p) (G p) := by
    by_cases hp : p.Prime
    · let : Fact p.Prime := ⟨hp⟩
      obtain ⟨k, hk⟩ := matrix_lattice_contains_prime_power (G p)
      refine ⟨k, ?_⟩
      intro hp' v
      exact hk v
    · refine ⟨0, ?_⟩
      intro hp' v
      exact (hp hp'.out).elim
  choose k hk using hex
  obtain ⟨B, hB, hm, hloc⟩ := patch_integral_matrix_lattices F hF k G hg hk hq
  refine ⟨D, B, hD, hB, hm, ?_⟩
  intro p hp
  obtain ⟨U, hU⟩ := hloc p
  refine ⟨U, ?_⟩
  rw [hU, hG, Matrix.smul_mul]


end GlobalIntegralPatching

namespace PrimitiveGenusAssembly

open Matrix GlobalIntegralPatching PrimitiveGenusDescent

theorem rational_basis_with_padic_changes {d : ℕ} (F : Finset ℕ)
    (hF : ∀ p ∈ F, Nat.Prime p)
    (A : (p : ℕ) → [Fact p.Prime] → GeneralLinearGroup (Fin d) ℚ_[p])
    (hout : ∀ (p : ℕ) [Fact p.Prime], p ∉ F → A p = 1) :
    ∃ T : GeneralLinearGroup (Fin d) ℚ, ∀ (p : ℕ) [Fact p.Prime],
      ∃ U : GeneralLinearGroup (Fin d) ℤ_[p],
        (T : Matrix (Fin d) (Fin d) ℚ).map (Rat.castHom ℚ_[p]) =
          (A p : Matrix _ _ _) * (U : Matrix _ _ _).map PadicInt.Coe.ringHom := by
  obtain ⟨D, B, hD, hB, _, hloc⟩ := patch_matrix_lattices F hF A hout
  let Tval : Matrix (Fin d) (Fin d) ℚ := (D : ℚ)⁻¹ • B.map (Int.castRingHom ℚ)
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have hBq : (B.map (Int.castRingHom ℚ)).det ≠ 0 := by
    change (B.map fun z : ℤ => (z : ℚ)).det ≠ 0
    rw [← Int.cast_det]
    exact_mod_cast hB
  have hTval : Tval.det ≠ 0 := by
    change ((D : ℚ)⁻¹ • B.map (Int.castRingHom ℚ)).det ≠ 0
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hDq)) hBq
  refine ⟨GeneralLinearGroup.mkOfDetNeZero Tval hTval, ?_⟩
  intro p hp
  obtain ⟨U, hU⟩ := hloc p
  refine ⟨U, ?_⟩
  have hmap : Tval.map (Rat.castHom ℚ_[p]) =
      (D : ℚ_[p])⁻¹ • B.map (Int.castRingHom ℚ_[p]) := by
    ext i j
    change Rat.castHom ℚ_[p] ((D : ℚ)⁻¹ * (B i j : ℚ)) = (D : ℚ_[p])⁻¹ * (B i j : ℚ_[p])
    rw [map_mul, map_inv₀, map_natCast, map_intCast]
  change Tval.map (Rat.castHom ℚ_[p]) = _
  rw [hmap, hU, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast hD

theorem some_unit_of_mulVec {n R : Type*} [Fintype n] [CommRing R] [IsLocalRing R]
    (M : Matrix n n R) (v : n → R) (h : ∃ i, IsUnit ((M *ᵥ v) i)) :
    ∃ i, IsUnit (v i) := by
  by_contra hn
  push Not at hn
  have hv (i : n) : v i ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hn i
  obtain ⟨i, hi⟩ := h
  apply (IsLocalRing.notMem_maximalIdeal.mpr hi)
  simp only [Matrix.mulVec, dotProduct]
  exact Submodule.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hv j)




theorem integral_genus_from_local_isometries
    (Q : Matrix (Fin 3) (Fin 3) ℤ) (hQ : Q.IsSymm) (r : Fin 3 → ℚ) (m : ℤ)
    (hr : r ⬝ᵥ (Q.map (Int.castRingHom ℚ) *ᵥ r) = (m : ℚ))
    (F : Finset ℕ) (hF : ∀ p ∈ F, Nat.Prime p)
    (A : (p : ℕ) → [Fact p.Prime] → GeneralLinearGroup (Fin 3) ℚ_[p])
    (hout : ∀ (p : ℕ) [Fact p.Prime], p ∉ F → A p = 1)
    (hiso : ∀ (p : ℕ) [Fact p.Prime],
      (A p : Matrix _ _ _)ᵀ * Q.map (Int.castRingHom ℚ_[p]) * (A p : Matrix _ _ _) =
        Q.map (Int.castRingHom ℚ_[p]))
    (hprim : ∀ (p : ℕ) [Fact p.Prime], ∃ y : Fin 3 → ℤ_[p],
      (A p : Matrix _ _ _) *ᵥ (fun i => (y i : ℚ_[p])) = (fun i => (r i : ℚ_[p])) ∧ ∃ i, IsUnit (y i)) :
    ∃ M : Matrix (Fin 3) (Fin 3) ℤ, ∃ v : Fin 3 → ℤ,
      M.IsSymm ∧
      (∃ V : GeneralLinearGroup (Fin 3) ℝ,
        M.map (Int.castRingHom ℝ) = (V : Matrix _ _ _)ᵀ *
          Q.map (Int.castRingHom ℝ) * (V : Matrix _ _ _)) ∧
      (∀ (p : ℕ) [Fact p.Prime], ∃ U : GeneralLinearGroup (Fin 3) ℤ_[p],
        M.map (Int.castRingHom ℤ_[p]) = (U : Matrix _ _ _)ᵀ *
          Q.map (Int.castRingHom ℤ_[p]) * (U : Matrix _ _ _)) ∧
      v ⬝ᵥ (M *ᵥ v) = m ∧ Int.gcd (v 0) (Int.gcd (v 1) (v 2)) = 1 := by
  obtain ⟨T, hT⟩ := rational_basis_with_padic_changes F hF A hout
  let X := (T : Matrix (Fin 3) (Fin 3) ℚ)
  let Xinv := ((T⁻¹ : GeneralLinearGroup (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ)
  let E := Xᵀ * Q.map (Int.castRingHom ℚ) * X
  let x := Xinv *ᵥ r
  have hx : X *ᵥ x = r := by
    change X *ᵥ (Xinv *ᵥ r) = r
    have he : X * Xinv = 1 := T.val_inv
    rw [Matrix.mulVec_mulVec, he, Matrix.one_mulVec]
  have he : E.IsSymm := by
    change (Xᵀ * Q.map (Int.castRingHom ℚ) * X)ᵀ = _
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      ← Matrix.transpose_map, show Qᵀ = Q from hQ]
    exact (Matrix.mul_assoc _ _ _).symm
  have hnorm : x ⬝ᵥ (E *ᵥ x) = (m : ℚ) := by
    change x ⬝ᵥ ((Xᵀ * Q.map (Int.castRingHom ℚ) * X) *ᵥ x) = _
    simp only [← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec, hx]
    rwa [dotProduct_comm]
  apply certify_integral_genus Q E x m he T rfl hnorm
  intro p hp
  obtain ⟨U, hU⟩ := hT p
  obtain ⟨y, hy, hyp⟩ := hprim p
  let C := (U : Matrix (Fin 3) (Fin 3) ℤ_[p]).map PadicInt.Coe.ringHom
  let V := ((U⁻¹ : GeneralLinearGroup (Fin 3) ℤ_[p]) : Matrix (Fin 3) (Fin 3) ℤ_[p])
  let z := V *ᵥ y
  have hUz : (U : Matrix (Fin 3) (Fin 3) ℤ_[p]) *ᵥ z = y := by
    change (U : Matrix (Fin 3) (Fin 3) ℤ_[p]) *ᵥ (V *ᵥ y) = y
    have hpU : (U : Matrix (Fin 3) (Fin 3) ℤ_[p]) * V = 1 := U.val_inv
    rw [Matrix.mulVec_mulVec, hpU, Matrix.one_mulVec]
  have hzp : ∃ i, IsUnit (z i) := by
    apply some_unit_of_mulVec (U : Matrix (Fin 3) (Fin 3) ℤ_[p])
    simpa only [hUz] using hyp
  refine ⟨U, z, ?_, ?_, hzp⟩
  · have hcastQ : (Q.map (Int.castRingHom ℚ)).map (Rat.castHom ℚ_[p]) =
        Q.map (Int.castRingHom ℚ_[p]) := by
      ext i j
      exact map_intCast (Rat.castHom ℚ_[p]) (Q i j)
    have hcastQ' : (Q.map (Int.castRingHom ℤ_[p])).map PadicInt.Coe.ringHom =
        Q.map (Int.castRingHom ℚ_[p]) := rfl
    change (Xᵀ * Q.map (Int.castRingHom ℚ) * X).map (Rat.castHom ℚ_[p]) = _
    simp only [Matrix.map_mul, Matrix.transpose_map, hcastQ, hcastQ']
    change X.map (Rat.castHom ℚ_[p]) = (A p : Matrix _ _ _) * C at hU
    rw [hU, Matrix.transpose_mul]
    change (Cᵀ * (A p : Matrix _ _ _)ᵀ) * Q.map (Int.castRingHom ℚ_[p]) *
      ((A p : Matrix _ _ _) * C) = Cᵀ * Q.map (Int.castRingHom ℚ_[p]) * C
    calc
      _ = Cᵀ * ((A p : Matrix _ _ _)ᵀ * Q.map (Int.castRingHom ℚ_[p]) *
        (A p : Matrix _ _ _)) * C := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hiso p]
  · let f := Rat.castHom ℚ_[p]
    let g : ℤ_[p] →+* ℚ_[p] := PadicInt.Coe.ringHom
    have h1 : X.map f *ᵥ (f ∘ x) = f ∘ r := by
      funext i
      exact (RingHom.map_mulVec f X x i).symm.trans (congrArg (fun v => f (v i)) hx)
    have h2 : C *ᵥ (g ∘ z) = g ∘ y := by
      funext i
      exact (RingHom.map_mulVec g _ z i).symm.trans (congrArg (fun v => g (v i)) hUz)
    have h3 : X.map f *ᵥ (g ∘ z) = f ∘ r := by
      change X.map f = (A p : Matrix _ _ _) * C at hU
      rw [hU, ← Matrix.mulVec_mulVec, h2]
      exact hy
    have hi : Xinv.map f * X.map f = 1 := by
      rw [← Matrix.map_mul, show Xinv * X = 1 from T.inv_val]
      exact Matrix.map_one _ f.map_zero f.map_one
    have hz := congrArg (fun w => Xinv.map f *ᵥ w) (h1.trans h3.symm)
    change Xinv.map f *ᵥ (X.map f *ᵥ (f ∘ x)) = Xinv.map f *ᵥ (X.map f *ᵥ (g ∘ z)) at hz
    simp only [Matrix.mulVec_mulVec, hi, Matrix.one_mulVec] at hz
    exact fun i => congrFun hz i




theorem rational_vector_primitive_away_finitely_many {n : Type*} [Fintype n]
    (r : n → ℚ) (hn : ∃ i, r i ≠ 0) :
    ∃ F : Finset ℕ, (∀ p ∈ F, p.Prime) ∧
      ∀ (p : ℕ) [Fact p.Prime], p ∉ F → ∃ y : n → ℤ_[p],
        (∀ i, (y i : ℚ_[p]) = (r i : ℚ_[p])) ∧ ∃ i, IsUnit (y i) := by
  classical
  obtain ⟨i, hi⟩ := hn
  let F := (r i).num.natAbs.primeFactors ∪ Finset.univ.biUnion (fun j => (r j).den.primeFactors)
  refine ⟨F, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_union.mp hp with hh | hh
    · exact Nat.prime_of_mem_primeFactors hh
    · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hh
      exact Nat.prime_of_mem_primeFactors hj
  intro p hp hpF
  have hd (j : n) : ¬p ∣ (r j).den := by
    intro h
    exact hpF (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hp.out.mem_primeFactors h (r j).den_nz⟩))
  let y (j : n) : ℤ_[p] := ⟨(r j : ℚ_[p]), Padic.norm_rat_le_one (hd j)⟩
  refine ⟨y, fun _ => rfl, i, PadicInt.isUnit_iff.mpr ?_⟩
  have hh : ¬p ∣ (r i).num.natAbs := by
    intro h
    have hz : (r i).num.natAbs ≠ 0 := by simpa using hi
    exact hpF (Finset.mem_union_left _ (hp.out.mem_primeFactors h hz))
  have hnum : ‖((r i).num : ℚ_[p])‖ = 1 := by
    apply le_antisymm (Padic.norm_int_le_one _)
    apply le_of_not_gt
    intro h
    exact hh (Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr (Padic.norm_intCast_lt_one_iff.mp h)))
  have hden : ‖((r i).den : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr ((hp.out.coprime_iff_not_dvd).mpr (hd i))
  change ‖(r i : ℚ_[p])‖ = 1
  rw [Rat.cast_def, norm_div, hnum, hden, div_one]

theorem exists_matrix_isometry_of_equal_value {n K : Type*} [Fintype n] [DecidableEq n]
    [Field K] [CharZero K] (Q : Matrix n n K) (hQ : Q.IsSymm) (x y : n → K)
    (hxy : x ⬝ᵥ (Q *ᵥ x) = y ⬝ᵥ (Q *ᵥ y)) (hn : x ⬝ᵥ (Q *ᵥ x) ≠ 0) :
    ∃ A : GeneralLinearGroup n K, (A : Matrix n n K) *ᵥ x = y ∧
      (A : Matrix n n K)ᵀ * Q * (A : Matrix n n K) = Q := by
  let B := Matrix.toBilin' Q
  have hsymm (u v : n → K) : B u v = B v u := by
    change Matrix.toBilin' Q u v = Matrix.toBilin' Q v u
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply']
    conv_lhs => rw [← show Qᵀ = Q from hQ]
    rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
  obtain ⟨e, he, hiso⟩ := PrimitiveGenusReflection.exists_isometry_of_equal_nonzero_norm B
    hsymm x y (by simpa only [B, Matrix.toBilin'_apply'] using hxy)
    (by simpa only [B, Matrix.toBilin'_apply'] using hn)
  let C := LinearMap.toMatrix' e.toLinearMap
  let D := LinearMap.toMatrix' e.symm.toLinearMap
  have hCD : C * D = 1 := by
    change LinearMap.toMatrix' e.toLinearMap * LinearMap.toMatrix' e.symm.toLinearMap = 1
    rw [← LinearMap.toMatrix'_comp, show e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id from
      LinearMap.ext fun v => e.apply_symm_apply v, LinearMap.toMatrix'_id]
  have hDC : D * C = 1 := by
    change LinearMap.toMatrix' e.symm.toLinearMap * LinearMap.toMatrix' e.toLinearMap = 1
    rw [← LinearMap.toMatrix'_comp, show e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id from
      LinearMap.ext fun v => e.symm_apply_apply v, LinearMap.toMatrix'_id]
  let A : GeneralLinearGroup n K := ⟨C, D, hCD, hDC⟩
  have hC (v : n → K) : C *ᵥ v = e v := LinearMap.toMatrix'_mulVec e.toLinearMap v
  refine ⟨A, (hC x).trans he, ?_⟩
  change Cᵀ * Q * C = Q
  apply Matrix.toBilin'.injective
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  simp only [Matrix.toBilin'_apply', ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec,
    hC, dotProduct_comm (Q *ᵥ e v)]
  simpa only [B, Matrix.toBilin'_apply'] using hiso u v




theorem map_quadratic_value {n R S : Type*} [Fintype n] [CommRing R] [CommRing S]
    (f : R →+* S) (Q : Matrix n n R) (v : n → R) :
    f (v ⬝ᵥ (Q *ᵥ v)) = (f ∘ v) ⬝ᵥ (Q.map f *ᵥ (f ∘ v)) := by
  rw [RingHom.map_dotProduct]
  congr 1
  funext i
  exact RingHom.map_mulVec f Q v i

theorem integral_genus_from_rational_and_primitive_local
    (Q : Matrix (Fin 3) (Fin 3) ℤ) (hQ : Q.IsSymm) (m : ℤ) (hm : m ≠ 0)
    (hrat : ∃ r : Fin 3 → ℚ, r ⬝ᵥ (Q.map (Int.castRingHom ℚ) *ᵥ r) = (m : ℚ))
    (hlocal : ∀ (p : ℕ) [Fact p.Prime], ∃ y : Fin 3 → ℤ_[p],
      y ⬝ᵥ (Q.map (Int.castRingHom ℤ_[p]) *ᵥ y) = (m : ℤ_[p]) ∧ ∃ i, IsUnit (y i)) :
    ∃ M : Matrix (Fin 3) (Fin 3) ℤ, ∃ v : Fin 3 → ℤ,
      M.IsSymm ∧
      (∃ V : GeneralLinearGroup (Fin 3) ℝ,
        M.map (Int.castRingHom ℝ) = (V : Matrix _ _ _)ᵀ *
          Q.map (Int.castRingHom ℝ) * (V : Matrix _ _ _)) ∧
      (∀ (p : ℕ) [Fact p.Prime], ∃ U : GeneralLinearGroup (Fin 3) ℤ_[p],
        M.map (Int.castRingHom ℤ_[p]) = (U : Matrix _ _ _)ᵀ *
          Q.map (Int.castRingHom ℤ_[p]) * (U : Matrix _ _ _)) ∧
      v ⬝ᵥ (M *ᵥ v) = m ∧ Int.gcd (v 0) (Int.gcd (v 1) (v 2)) = 1 := by
  classical
  obtain ⟨r, hr⟩ := hrat
  have hnonzero : ∃ i, r i ≠ 0 := by
    by_contra h
    push Not at h
    have hz : r = 0 := funext h
    rw [hz, Matrix.mulVec_zero, dotProduct_zero] at hr
    exact hm (by exact_mod_cast hr.symm)
  obtain ⟨F, hF, hFr⟩ := rational_vector_primitive_away_finitely_many r hnonzero
  have hchoice (p : ℕ) [Fact p.Prime] :
      ∃ A : GeneralLinearGroup (Fin 3) ℚ_[p],
        (p ∉ F → A = 1) ∧
        ((A : Matrix _ _ _)ᵀ * Q.map (Int.castRingHom ℚ_[p]) * (A : Matrix _ _ _) =
            Q.map (Int.castRingHom ℚ_[p])) ∧
        ∃ y : Fin 3 → ℤ_[p], (A : Matrix _ _ _) *ᵥ (fun i => (y i : ℚ_[p])) =
          (fun i => (r i : ℚ_[p])) ∧ ∃ i, IsUnit (y i) := by
    by_cases hp : p ∈ F
    · obtain ⟨y, hy, hu⟩ := hlocal p
      let Qp := Q.map (Int.castRingHom ℚ_[p])
      let yp (i : Fin 3) : ℚ_[p] := y i
      let rp (i : Fin 3) : ℚ_[p] := r i
      have hy' : yp ⬝ᵥ (Qp *ᵥ yp) = (m : ℚ_[p]) := by
        let f : ℤ_[p] →+* ℚ_[p] := PadicInt.Coe.ringHom
        exact (map_quadratic_value f (Q.map (Int.castRingHom ℤ_[p])) y).symm.trans (congrArg f hy)
      have hr' : rp ⬝ᵥ (Qp *ᵥ rp) = (m : ℚ_[p]) := by
        let f := Rat.castHom ℚ_[p]
        have hcast : (Q.map (Int.castRingHom ℚ)).map f = Qp := by
          ext i j
          exact map_intCast f _
        have hv := (map_quadratic_value f (Q.map (Int.castRingHom ℚ)) r).symm.trans (congrArg f hr)
        rw [hcast, map_intCast] at hv
        exact hv
      have hsym : Qp.IsSymm := by
        change (Q.map (Int.castRingHom ℚ_[p]))ᵀ = Q.map (Int.castRingHom ℚ_[p])
        rw [← Matrix.transpose_map, show Qᵀ = Q from hQ]
      obtain ⟨A, hA, hAQ⟩ := exists_matrix_isometry_of_equal_value Qp hsym yp rp (hy'.trans hr'.symm)
        (by rw [hy']; exact_mod_cast hm)
      exact ⟨A, fun h => (h hp).elim, hAQ, y, hA, hu⟩
    · obtain ⟨y, hy, hu⟩ := hFr p hp
      refine ⟨1, fun _ => rfl, ?_, y, ?_, hu⟩
      · change (1 : Matrix (Fin 3) (Fin 3) ℚ_[p])ᵀ * _ * 1 = _
        rw [Matrix.transpose_one, one_mul, mul_one]
      · change (1 : Matrix (Fin 3) (Fin 3) ℚ_[p]) *ᵥ (fun i => (y i : ℚ_[p])) = _
        rw [Matrix.one_mulVec]
        exact funext hy
  choose a ha using fun p : {p : ℕ // p.Prime} => @hchoice p.val ⟨p.property⟩
  let A (p : ℕ) [hp : Fact p.Prime] : GeneralLinearGroup (Fin 3) ℚ_[p] := a ⟨p, hp.out⟩
  apply integral_genus_from_local_isometries Q hQ r m hr F hF A
  · intro p hp
    exact (ha ⟨p, hp.out⟩).1
  · intro p hp
    exact (ha ⟨p, hp.out⟩).2.1
  · intro p hp
    exact (ha ⟨p, hp.out⟩).2.2


end PrimitiveGenusAssembly

namespace A287616SmallPrimes

open Polynomial

private theorem liftSquare {p : ℕ} [Fact p.Prime] (a b : ℤ_[p])
    (h : ‖a - b‖ < ‖2 * a‖ ^ 2) :
    ∃ z : ℤ_[p], a * z ^ 2 = b ∧ ‖2 * a * z‖ = ‖2 * a‖ := by
  let f : Polynomial ℤ_[p] := C a * X ^ 2 - C b
  have hf (t : ℤ_[p]) : f.aeval t = a * t ^ 2 - b := by simp [f]
  have hg (t : ℤ_[p]) : f.derivative.aeval t = 2 * a * t := by
    simp [f]
    ring
  have hstart : ‖f.aeval (1 : ℤ_[p])‖ < ‖f.derivative.aeval (1 : ℤ_[p])‖ ^ 2 := by
    simpa only [hf, hg, one_pow, mul_one] using h
  obtain ⟨z, hz, -, hnorm, -⟩ := hensels_lemma hstart
  exact ⟨z, sub_eq_zero.mp (by simpa only [hf] using hz),
    by simpa only [hg, mul_one] using hnorm⟩

private theorem liftSquareUnit {p : ℕ} [Fact p.Prime] (a b : ℤ_[p])
    (ha : ‖2 * a‖ = 1) (hab : ‖a - b‖ < 1) :
    ∃ z : ℤ_[p], a * z ^ 2 = b ∧ IsUnit z := by
  obtain ⟨z, hz, hnorm⟩ := liftSquare a b (by simpa [ha] using hab)
  exact ⟨z, hz, PadicInt.isUnit_iff.mpr (by simpa [norm_mul, ha] using hnorm)⟩

private theorem caseTwo (n : ℕ) :
    ∃ a b c : ℤ_[2], 15 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 = 120 * (n : ℤ_[2]) + 23 ∧
      (IsUnit a ∨ IsUnit b ∨ IsUnit c) := by
  have hdiv : (((2 : ℕ) ^ 3 : ℕ) : ℤ) ∣ -(120 * (n : ℤ)) :=
    ⟨-15 * (n : ℤ), by push_cast; ring⟩
  have hres : ‖((-(120 * (n : ℤ))) : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-3 : ℤ) := by
    simpa using (PadicInt.norm_int_le_pow_iff_dvd (p := 2) (n := 3)).mpr hdiv
  have hthree : ‖(3 : ℤ_[2])‖ = 1 := by
    change ‖((3 : ℕ) : ℤ_[2])‖ = 1
    exact PadicInt.norm_natCast_eq_one_iff.mpr (by decide)
  have hsix : ‖2 * (3 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := by
    rw [norm_mul, hthree, mul_one]
    exact PadicInt.norm_p (p := 2)
  have hh : ‖(3 : ℤ_[2]) - (120 * (n : ℤ_[2]) + 3)‖ < ‖2 * (3 : ℤ_[2])‖ ^ 2 := by
    rw [show (3 : ℤ_[2]) - (120 * (n : ℤ_[2]) + 3) = ((-(120 * (n : ℤ))) : ℤ_[2]) by
      push_cast; ring, hsix]
    exact hres.trans_lt (by norm_num)
  obtain ⟨z, hz, -⟩ := liftSquare 3 (120 * (n : ℤ_[2]) + 3) hh
  exact ⟨1, 1, z, by linear_combination hz, Or.inl isUnit_one⟩

private theorem caseThree (n : ℕ) :
    ∃ a b c : ℤ_[3], 15 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 = 120 * (n : ℤ_[3]) + 23 ∧
      (IsUnit a ∨ IsUnit b ∨ IsUnit c) := by
  have hder : ‖2 * (5 : ℤ_[3])‖ = 1 := by
    rw [show 2 * (5 : ℤ_[3]) = ((10 : ℕ) : ℤ_[3]) by push_cast; ring]
    exact PadicInt.norm_natCast_eq_one_iff.mpr (by decide)
  have hres : ‖(5 : ℤ_[3]) - (120 * (n : ℤ_[3]) + 23)‖ < 1 := by
    rw [show (5 : ℤ_[3]) - (120 * (n : ℤ_[3]) + 23) =
      ((-120 * (n : ℤ) - 18 : ℤ) : ℤ_[3]) by push_cast; ring]
    exact PadicInt.norm_intCast_lt_one_iff.mpr ⟨-40 * (n : ℤ) - 6, by ring⟩
  obtain ⟨z, hz, hunit⟩ := liftSquareUnit 5 (120 * (n : ℤ_[3]) + 23) hder hres
  exact ⟨0, z, 0, by linear_combination hz, Or.inr (Or.inl hunit)⟩

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem caseFive (n : ℕ) :
    ∃ a b c : ℤ_[5], 15 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 = 120 * (n : ℤ_[5]) + 23 ∧
      (IsUnit a ∨ IsUnit b ∨ IsUnit c) := by
  have hder : ‖2 * (3 : ℤ_[5])‖ = 1 := by
    rw [show 2 * (3 : ℤ_[5]) = ((6 : ℕ) : ℤ_[5]) by push_cast; ring]
    exact PadicInt.norm_natCast_eq_one_iff.mpr (by decide)
  have hres : ‖(3 : ℤ_[5]) - (120 * (n : ℤ_[5]) + 23)‖ < 1 := by
    rw [show (3 : ℤ_[5]) - (120 * (n : ℤ_[5]) + 23) =
      ((-120 * (n : ℤ) - 20 : ℤ) : ℤ_[5]) by push_cast; ring]
    exact PadicInt.norm_intCast_lt_one_iff.mpr ⟨-24 * (n : ℤ) - 4, by ring⟩
  obtain ⟨z, hz, hunit⟩ := liftSquareUnit 3 (120 * (n : ℤ_[5]) + 23) hder hres
  exact ⟨0, 0, z, by linear_combination hz, Or.inr (Or.inr hunit)⟩

theorem smallPrimes (n p : ℕ) [Fact p.Prime] (hp : p ∣ 30) :
    ∃ a b c : ℤ_[p], 15 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 = 120 * (n : ℤ_[p]) + 23 ∧
      (IsUnit a ∨ IsUnit b ∨ IsUnit c) := by
  have prime : p.Prime := Fact.out
  change p ∣ (2 * 3) * 5 at hp
  rcases prime.dvd_mul.mp hp with h | h
  · rcases prime.dvd_mul.mp h with h | h
    · have hp2 := (Nat.dvd_prime (by decide : Nat.Prime 2)).mp h
      rcases hp2 with hp1 | rfl
      · exact (prime.ne_one hp1).elim
      · exact caseTwo n
    · have hp3 := (Nat.dvd_prime (by decide : Nat.Prime 3)).mp h
      rcases hp3 with hp1 | rfl
      · exact (prime.ne_one hp1).elim
      · exact caseThree n
  · have hp5 := (Nat.dvd_prime (by decide : Nat.Prime 5)).mp h
    rcases hp5 with hp1 | rfl
    · exact (prime.ne_one hp1).elim
    · exact caseFive n

theorem otherPrimes (n p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ 30) :
    ∃ a b c : ℤ_[p], 15 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 = 120 * (n : ℤ_[p]) + 23 ∧
      (IsUnit a ∨ IsUnit b ∨ IsUnit c) := by
  have hprime : p.Prime := Fact.out
  have hodd : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card]
    rcases hprime.eq_two_or_odd with htwo | ho
    · exact (hp (htwo ▸ (by decide : 2 ∣ 30))).elim
    · exact ho
  have hnonzero (d : ℕ) (hd : d ∣ 30) : (d : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact fun h => hp (h.trans hd)
  have c3 : (3 : ZMod p) ≠ 0 := hnonzero 3 (by decide)
  have c5 : (5 : ZMod p) ≠ 0 := hnonzero 5 (by decide)
  let t : ZMod p := 120 * (n : ZMod p) + 8
  let f : (ZMod p)[X] := C 5 * X ^ 2 - C t
  let g : (ZMod p)[X] := C 3 * X ^ 2
  have hf : f.degree = 2 := by
    dsimp [f]
    rw [degree_sub_eq_left_of_degree_lt]
    · rw [degree_C_mul c5, degree_X_pow]; rfl
    · rw [degree_C_mul c5, degree_X_pow]
      exact degree_C_le.trans_lt (by decide)
  have hg : g.degree = 2 := by
    dsimp [g]
    rw [degree_C_mul c3, degree_X_pow]; rfl
  obtain ⟨y,z,h⟩ := FiniteField.exists_root_sum_quadratic hf hg hodd
  have hsum : 5 * y ^ 2 + 3 * z ^ 2 = t := by
    simp [f,g] at h
    linear_combination h
  let b : ℤ_[p] := y.val
  let c : ℤ_[p] := z.val
  let u := 120 * (n : ℤ_[p]) + 23 - 5 * b ^ 2 - 3 * c ^ 2
  have hmap : PadicInt.toZMod (15 - u) = 0 := by
    simp [u,b,c, map_ofNat]
    dsimp [t] at hsum
    linear_combination hsum
  have hsmall : ‖15 - u‖ < 1 := by
    rw [PadicInt.norm_lt_one_iff_dvd, ← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
      ← PadicInt.ker_toZMod, RingHom.mem_ker]
    exact hmap
  have hder : ‖2 * (15 : ℤ_[p])‖ = 1 := by
    rw [show 2 * (15 : ℤ_[p]) = ((30 : ℕ) : ℤ_[p]) by push_cast; ring]
    exact PadicInt.norm_natCast_eq_one_iff.mpr (hprime.coprime_iff_not_dvd.mpr hp)
  obtain ⟨a, ha, haUnit⟩ := liftSquareUnit 15 u hder hsmall
  dsimp [u] at ha
  exact ⟨a, b, c, by linear_combination ha, Or.inl haUnit⟩

end A287616SmallPrimes


/-! Elementary steps for the primitive local-to-genus implication in A287616. -/

namespace A287616GenusTransport

open Matrix

theorem primitive_mulVec (T : Matrix.GeneralLinearGroup (Fin 3) ℤ) (v : Fin 3 → ℤ)
    (hv : Int.gcd (v 0) (Int.gcd (v 1) (v 2)) = 1) :
    let w := (T : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ v
    Int.gcd (w 0) (Int.gcd (w 1) (w 2)) = 1 := by
  let w := (T : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ v
  change Int.gcd (w 0) (Int.gcd (w 1) (w 2)) = 1
  let d := Int.gcd (w 0) (Int.gcd (w 1) (w 2))
  have hdiv (i : Fin 3) : (d : ℤ) ∣ w i := by
    fin_cases i
    · exact Int.gcd_dvd_left _ _
    · exact (Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_left _ _)
    · exact (Int.gcd_dvd_right _ _).trans (Int.gcd_dvd_right _ _)
  let U := ((T⁻¹ : Matrix.GeneralLinearGroup (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ)
  have hInv : U *ᵥ w = v := by
    change U *ᵥ ((T : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ v) = v
    rw [Matrix.mulVec_mulVec]
    have hProd : U * (T : Matrix (Fin 3) (Fin 3) ℤ) = 1 := T.inv_val
    simp [hProd]
  have hback (i : Fin 3) : (d : ℤ) ∣ v i := by
    rw [← hInv]
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_right (hdiv j) _
  have hfinal := Int.dvd_gcd (hback 0) (Int.dvd_coe_gcd (hback 1) (hback 2))
  rw [hv] at hfinal
  exact Nat.dvd_one.mp hfinal

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem finite_nonisotropic : ∀ x y : ZMod 5,
    3 * x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0 := by decide

theorem no_primitive_zero_at_five (a b c : ℤ_[5])
    (h : 15 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 = 0) :
    ¬ (IsUnit a ∨ IsUnit b ∨ IsUnit c) := by
  let red := PadicInt.toZMod (p := 5)
  have hzero (z : ℤ_[5]) : red z = 0 ↔ (5 : ℤ_[5]) ∣ z := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton]
    norm_num
  have hc : red c = 0 := by
    have hz := congrArg red h
    have hc3 : 3 * red c ^ 2 = 0 := by
      simpa [map_ofNat, show (15 : ZMod 5) = 0 by decide, show (5 : ZMod 5) = 0 by decide] using hz
    rcases mul_eq_zero.mp hc3 with hbad | hsq
    · exact ((by decide : (3 : ZMod 5) ≠ 0) hbad).elim
    · rw [pow_two] at hsq
      exact (mul_eq_zero.mp hsq).elim id id
  obtain ⟨d, hd⟩ := (hzero c).mp hc
  have h5 : (5 : ℤ_[5]) ≠ 0 := by exact_mod_cast (by decide : (5 : ℕ) ≠ 0)
  have hdiv : 3 * a ^ 2 + b ^ 2 + 15 * d ^ 2 = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left h5
    rw [hd] at h
    linear_combination h
  have hab : 3 * red a ^ 2 + red b ^ 2 = 0 := by
    simpa [map_ofNat, show (15 : ZMod 5) = 0 by decide] using congrArg red hdiv
  obtain ⟨ha,hb⟩ := finite_nonisotropic _ _ hab
  have nonunit (z : ℤ_[5]) (hz : red z = 0) (hu : IsUnit z) : False := by
    have hred := hu.map red
    rw [hz] at hred
    exact not_isUnit_zero hred
  exact fun hu => hu.elim (nonunit a ha) (fun hw => hw.elim (nonunit b hb) (nonunit c hc))

theorem positive_of_primitive_local {m : ℤ}
    (hreal : ∃ a b c : ℝ, 15 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 = (m : ℝ))
    (hfive : ∃ a b c : ℤ_[5], 15 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 = (m : ℤ_[5]) ∧
      (IsUnit a ∨ IsUnit b ∨ IsUnit c)) : 0 < m := by
  obtain ⟨a,b,c,he⟩ := hreal
  have hreal' : (0 : ℝ) ≤ m := by rw [← he]; positivity
  have hnonneg : 0 ≤ m := by exact_mod_cast hreal'
  obtain ⟨i,j,k,hijk,hu⟩ := hfive
  refine lt_of_le_of_ne hnonneg ?_
  intro hm
  rw [← hm, Int.cast_zero] at hijk
  exact no_primitive_zero_at_five i j k hijk hu

def baseGram : Matrix (Fin 3) (Fin 3) ℤ := !![15, 0, 0; 0, 5, 0; 0, 0, 3]

def InGenus (M : Matrix (Fin 3) (Fin 3) ℤ) : Prop :=
  M.IsSymm ∧
  (∃ T : Matrix.GeneralLinearGroup (Fin 3) ℝ,
    M.map (Int.castRingHom ℝ) = (T : Matrix _ _ _).transpose *
      baseGram.map (Int.castRingHom ℝ) * (T : Matrix _ _ _)) ∧
  (∀ (p : ℕ) [Fact p.Prime], ∃ T : Matrix.GeneralLinearGroup (Fin 3) ℤ_[p],
    M.map (Int.castRingHom ℤ_[p]) = (T : Matrix _ _ _).transpose *
      baseGram.map (Int.castRingHom ℤ_[p]) * (T : Matrix _ _ _))

theorem genus_det {M : Matrix (Fin 3) (Fin 3) ℤ} (hM : InGenus M) : M.det = 225 := by
  have hbase : baseGram.det = 225 := by
    rw [Matrix.det_fin_three]
    change (15 : ℤ) * 5 * 3 - 15 * 0 * 0 - 0 * 0 * 3 + 0 * 0 * 0 + 0 * 0 * 0 - 0 * 5 * 0 = 225
    norm_num
  obtain ⟨-, ⟨T, hT⟩, hlocal⟩ := hM
  have hr := congrArg Matrix.det hT
  simp only [Int.coe_castRingHom, ← Int.cast_det, Matrix.det_mul, Matrix.det_transpose, hbase] at hr
  have hTne : ((T : Matrix (Fin 3) (Fin 3) ℝ).det) ≠ 0 := (Matrix.isUnits_det_units T).ne_zero
  have hpos : 0 < M.det := by
    have hp : 0 < (M.det : ℝ) := by
      rw [hr]
      calc
        0 < ((225 : ℤ) : ℝ) * (T : Matrix (Fin 3) (Fin 3) ℝ).det ^ 2 :=
          mul_pos (by norm_num) (sq_pos_of_ne_zero hTne)
        _ = _ := by ring
    exact_mod_cast hp
  let n := M.det.toNat
  have hn : (n : ℤ) = M.det := Int.toNat_of_nonneg hpos.le
  have hn₀ : n ≠ 0 := by omega
  have hpow (p k : ℕ) (hp : p.Prime) : p ^ k ∣ n ↔ p ^ k ∣ 225 := by
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨U,hU⟩ := hlocal p
    have hu := congrArg Matrix.det hU
    simp only [Int.coe_castRingHom, ← Int.cast_det, Matrix.det_mul, Matrix.det_transpose, hbase] at hu
    have hu₁ : ‖(U : Matrix (Fin 3) (Fin 3) ℤ_[p]).det‖ = 1 :=
      PadicInt.isUnit_iff.mp (Matrix.isUnits_det_units U)
    have hnorm : ‖(M.det : ℤ_[p])‖ = ‖((225 : ℤ) : ℤ_[p])‖ := by
      rw [hu, norm_mul, norm_mul, hu₁, one_mul, mul_one]
    have hInt : (((p ^ k : ℕ) : ℤ) ∣ M.det) ↔ (((p ^ k : ℕ) : ℤ) ∣ (225 : ℤ)) := by
      simp only [Nat.cast_pow]
      rw [← PadicInt.norm_int_le_pow_iff_dvd, hnorm, PadicInt.norm_int_le_pow_iff_dvd]
    rw [← hn] at hInt
    exact_mod_cast hInt
  have hNat : n = 225 := by
    apply Nat.eq_of_factorization_eq hn₀ (by decide)
    intro p
    by_cases hp : p.Prime
    · apply le_antisymm
      · exact (hp.pow_dvd_iff_le_factorization (by decide)).mp
          ((hpow p (n.factorization p) hp).mp ((hp.pow_dvd_iff_le_factorization hn₀).mpr le_rfl))
      · exact (hp.pow_dvd_iff_le_factorization hn₀).mp
          ((hpow p ((225 : ℕ).factorization p) hp).mpr ((hp.pow_dvd_iff_le_factorization (by decide)).mpr le_rfl))
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  omega

def PrimitiveGenusRepresentation : Prop :=
  ∀ m : ℤ, 0 < m →
    (∃ a b c : ℝ, 15 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 = (m : ℝ)) →
    (∀ (p : ℕ) [Fact p.Prime], ∃ a b c : ℤ_[p],
      15 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 = (m : ℤ_[p]) ∧
        (IsUnit a ∨ IsUnit b ∨ IsUnit c)) →
    ∃ (M : Matrix (Fin 3) (Fin 3) ℤ) (v : Fin 3 → ℤ), InGenus M ∧
      v ⬝ᵥ (M *ᵥ v) = m ∧ Int.gcd (v 0) (Int.gcd (v 1) (v 2)) = 1

def GenusClassification : Prop :=
  ∀ M, InGenus M →
    (∃ T : Matrix.GeneralLinearGroup (Fin 3) ℤ, ∀ v : Fin 3 → ℤ,
      let w := (T : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ v
      v ⬝ᵥ (M *ᵥ v) = 15 * (w 0) ^ 2 + 5 * (w 1) ^ 2 + 3 * (w 2) ^ 2) ∨
    (∃ T : Matrix.GeneralLinearGroup (Fin 3) ℤ, ∀ v : Fin 3 → ℤ,
      let w := (T : Matrix (Fin 3) (Fin 3) ℤ) *ᵥ v
      v ⬝ᵥ (M *ᵥ v) = 2 * (w 0) ^ 2 - 2 * w 0 * w 1 + 8 * (w 1) ^ 2 + 15 * (w 2) ^ 2)

theorem primitive_genus_reduction : PrimitiveGenusRepresentation → GenusClassification →
    ∀ m : ℤ,
      (∃ a b c : ℝ, 15 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 = (m : ℝ)) →
      (∀ (p : ℕ) [Fact p.Prime], ∃ a b c : ℤ_[p],
        15 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 = (m : ℤ_[p]) ∧
          (IsUnit a ∨ IsUnit b ∨ IsUnit c)) →
      (∃ u v w : ℤ, 15 * u ^ 2 + 5 * v ^ 2 + 3 * w ^ 2 = m ∧
        Int.gcd u (Int.gcd v w) = 1) ∨
      (∃ x y z : ℤ, 2 * x ^ 2 - 2 * x * y + 8 * y ^ 2 + 15 * z ^ 2 = m ∧
        Int.gcd x (Int.gcd y z) = 1) := by
  intro localGlobal classify m hreal hlocal
  obtain ⟨M,v,hM,hm,hv⟩ := localGlobal m (positive_of_primitive_local hreal (hlocal 5)) hreal hlocal
  rcases classify M hM with ⟨T, hT⟩ | ⟨T, hT⟩
  · exact Or.inl ⟨_,_,_,(hT v).symm.trans hm,primitive_mulVec T v hv⟩
  · exact Or.inr ⟨_,_,_,(hT v).symm.trans hm,primitive_mulVec T v hv⟩

end A287616GenusTransport


/-! Classification of the determinant-225 ternary genus. -/

/- Reducing a positive integral ternary Gram matrix by minimizing the trace. -/

namespace TernaryBasisReduction

open Matrix Finset

abbrev Gram := Matrix (Fin 3) (Fin 3) ℤ
abbrev IntegralBasis := Matrix.GeneralLinearGroup (Fin 3) ℤ

def changeBasis (A : Gram) (T : IntegralBasis) : Gram := (T : Gram)ᵀ * A * (T : Gram)

theorem change_one (A : Gram) : changeBasis A 1 = A := by simp [changeBasis]

theorem change_mul (A : Gram) (S T : IntegralBasis) :
    changeBasis (changeBasis A S) T = changeBasis A (S*T) := by
  simp only [changeBasis, Units.val_mul, transpose_mul, Matrix.mul_assoc]

theorem map_change {R : Type*} [CommRing R] (φ : ℤ →+* R) (A : Gram) (T : IntegralBasis) :
    let U := Matrix.GeneralLinearGroup.map φ T
    (changeBasis A T).map φ = (U : Matrix _ _ _)ᵀ * A.map φ * (U : Matrix _ _ _) := by
  change φ.mapMatrix ((T : Gram)ᵀ * A * (T : Gram)) = _
  rw [map_mul, map_mul]
  rfl

def nonnegativeForm (A : Gram) : Prop := ∀ v : Fin 3 → ℤ, 0 ≤ v ⬝ᵥ (A *ᵥ v)

theorem eval_change (A : Gram) (T : IntegralBasis) (v : Fin 3 → ℤ) :
    v ⬝ᵥ (changeBasis A T *ᵥ v) = ((T : Gram) *ᵥ v) ⬝ᵥ (A *ᵥ ((T : Gram) *ᵥ v)) := by
  rw [changeBasis, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec,
    dotProduct_comm]

theorem exists_trace_minimizer (A : Gram) (hA : nonnegativeForm A) :
    ∃ S : IntegralBasis, ∀ T : IntegralBasis, (changeBasis A S).trace ≤ (changeBasis A T).trace := by
  classical
  have hnonneg (T : IntegralBasis) : 0 ≤ (changeBasis A T).trace := by
    apply sum_nonneg
    intro i _
    have h := hA ((T : Gram) *ᵥ (Pi.single i 1))
    rw [← eval_change A T] at h
    simpa [Pi.single, Function.update, Matrix.mulVec, dotProduct] using h
  have hex : ∃ n : ℕ, ∃ T : IntegralBasis, ((changeBasis A T).trace).toNat = n := ⟨_,1,rfl⟩
  obtain ⟨S,hS⟩ := Nat.find_spec hex
  refine ⟨S, fun T => ?_⟩
  have hmin := Nat.find_min' hex (show ∃ S : IntegralBasis, ((changeBasis A S).trace).toNat =
    ((changeBasis A T).trace).toNat from ⟨T,rfl⟩)
  have hS0 := hnonneg S
  have hT0 := hnonneg T
  omega

private noncomputable def transvectionUnit {i j : Fin 3} (h : i ≠ j) (s : ℤ) : IntegralBasis :=
  Matrix.GeneralLinearGroup.mk'' (Matrix.transvection i j s) (by rw [det_transvection_of_ne i j h]; exact isUnit_one)

private theorem trace_transvection {i j : Fin 3} (h : i ≠ j) (A : Gram) (s : ℤ) :
    (changeBasis A (transvectionUnit h s)).trace = A.trace + s*A i j + s*A j i + s*s*A i i := by
  have ht : (Matrix.transvection i j s)ᵀ = Matrix.transvection j i s := by
    ext a b
    simp [Matrix.transvection, Matrix.single, Matrix.one_apply, eq_comm, and_comm]
  let B := changeBasis A (transvectionUnit h s)
  have hB : B = Matrix.transvection j i s * (A * Matrix.transvection i j s) := by
    change (Matrix.transvection i j s)ᵀ * A * Matrix.transvection i j s = _
    rw [ht, Matrix.mul_assoc]
  have hj : B j j = A j j + s*A i j + s*A j i + s*s*A i i := by
    rw [hB, Matrix.transvection_mul_apply_same, Matrix.mul_transvection_apply_same,
      Matrix.mul_transvection_apply_same]
    ring
  have ho (k : Fin 3) (hk : k ≠ j) : B k k = A k k := by
    rw [hB, Matrix.transvection_mul_apply_of_ne _ _ _ _ hk, Matrix.mul_transvection_apply_of_ne _ _ _ _ hk]
  change B.trace = _
  have hs : B.trace - A.trace = B j j - A j j := by
    simp only [Matrix.trace, Matrix.diag_apply, ← sum_sub_distrib]
    exact sum_eq_single j (fun k _ hk => by simp [ho k hk]) (by simp)
  omega

theorem trace_minimal_off_diagonal {A : Gram} (hs : A.IsSymm)
    (hmin : ∀ T : IntegralBasis, A.trace ≤ (changeBasis A T).trace) {i j : Fin 3} (hij : i ≠ j) :
    2 * |A i j| ≤ A i i := by
  have hg := hmin (transvectionUnit hij 1)
  have hl := hmin (transvectionUnit hij (-1))
  rw [trace_transvection hij] at hg hl
  have e : A j i = A i j := congrFun (congrFun hs.eq i) j
  rw [e] at hg hl
  rw [show 2 * |A i j| = |2 * A i j| by rw [abs_mul, abs_of_nonneg (by decide : 0 ≤ (2 : ℤ))], abs_le]
  constructor <;> linarith

private theorem change_transvection {i j : Fin 3} (h : i ≠ j) (A : Gram) (s : ℤ) :
    changeBasis A (transvectionUnit h s) = Matrix.transvection j i s * (A * Matrix.transvection i j s) := by
  have ht : (Matrix.transvection i j s)ᵀ = Matrix.transvection j i s := by
    ext a b
    simp [Matrix.transvection, Matrix.single, Matrix.one_apply, eq_comm, and_comm]
  change (Matrix.transvection i j s)ᵀ * A * Matrix.transvection i j s = _
  rw [ht, Matrix.mul_assoc]

theorem trace_minimal_triple {A : Gram} (hs : A.IsSymm)
    (hmin : ∀ T : IntegralBasis, A.trace ≤ (changeBasis A T).trace) :
    0 ≤ A 0 0 + A 1 1 + 2 * (A 0 1 + A 0 2 + A 1 2) := by
  let S := transvectionUnit (show (0 : Fin 3) ≠ 2 by decide) 1
  let T := transvectionUnit (show (1 : Fin 3) ≠ 2 by decide) 1
  let B := changeBasis A S
  have hB : B = Matrix.transvection 2 0 1 * (A * Matrix.transvection 0 2 1) :=
    change_transvection _ A 1
  have hS : B.trace = A.trace + A 0 2 + A 2 0 + A 0 0 := by
    simpa only [one_mul] using trace_transvection (show (0 : Fin 3) ≠ 2 by decide) A 1
  have hT : (changeBasis B T).trace = B.trace + B 1 2 + B 2 1 + B 1 1 := by
    simpa only [one_mul] using trace_transvection (show (1 : Fin 3) ≠ 2 by decide) B 1
  have h11 : B 1 1 = A 1 1 := by
    rw [hB, Matrix.transvection_mul_apply_of_ne _ _ _ _ (by decide : (1 : Fin 3) ≠ 2),
      Matrix.mul_transvection_apply_of_ne _ _ _ _ (by decide : (1 : Fin 3) ≠ 2)]
  have h12 : B 1 2 = A 1 2 + A 1 0 := by
    rw [hB, Matrix.transvection_mul_apply_of_ne _ _ _ _ (by decide : (1 : Fin 3) ≠ 2),
      Matrix.mul_transvection_apply_same, one_mul]
  have h21 : B 2 1 = A 2 1 + A 0 1 := by
    rw [hB, Matrix.transvection_mul_apply_same]
    simp only [Matrix.mul_transvection_apply_of_ne _ _ _ _ (by decide : (1 : Fin 3) ≠ 2), one_mul]
  have H := hmin (S*T)
  rw [← change_mul, show changeBasis A S = B from rfl, hT, hS, h11, h12, h21] at H
  have h10 : A 1 0 = A 0 1 := congrFun (congrFun hs.eq 0) 1
  have h20 : A 2 0 = A 0 2 := congrFun (congrFun hs.eq 0) 2
  have h21' : A 2 1 = A 1 2 := congrFun (congrFun hs.eq 1) 2
  rw [h10,h20,h21'] at H
  linarith

def relabel (σ : Equiv.Perm (Fin 3)) : IntegralBasis where
  val := (σ⁻¹).permMatrix ℤ
  inv := σ.permMatrix ℤ
  val_inv := by rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]
  inv_val := by rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]

theorem relabel_entries (A : Gram) (σ : Equiv.Perm (Fin 3)) :
    changeBasis A (relabel σ) = A.submatrix σ σ := by
  change ((σ⁻¹).permMatrix ℤ)ᵀ * A * (σ⁻¹).permMatrix ℤ = _
  rw [Matrix.transpose_permMatrix, inv_inv]
  change σ.toPEquiv.toMatrix * A * (σ⁻¹).toPEquiv.toMatrix = _
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl

private theorem sort_three (u : Fin 3 → ℤ) :
    ∃ σ : Equiv.Perm (Fin 3), u (σ 0) ≤ u (σ 1) ∧ u (σ 1) ≤ u (σ 2) := by
  by_cases h01 : u 0 ≤ u 1
  · by_cases h12 : u 1 ≤ u 2
    · exact ⟨Equiv.refl _,h01,h12⟩
    · by_cases h02 : u 0 ≤ u 2
      · refine ⟨Equiv.swap 1 2, ?_⟩
        simpa [Equiv.swap_apply_def] using And.intro h02 (le_of_not_ge h12)
      · refine ⟨(Equiv.swap 0 1).trans (Equiv.swap 1 2), ?_⟩
        simpa [Equiv.swap_apply_def] using And.intro (le_of_not_ge h02) h01
  · by_cases h02 : u 0 ≤ u 2
    · refine ⟨Equiv.swap 0 1, ?_⟩
      simpa [Equiv.swap_apply_def] using And.intro (le_of_not_ge h01) h02
    · by_cases h12 : u 1 ≤ u 2
      · refine ⟨(Equiv.swap 1 2).trans (Equiv.swap 0 1), ?_⟩
        simpa [Equiv.swap_apply_def] using And.intro h12 (le_of_not_ge h02)
      · refine ⟨Equiv.swap 0 2, ?_⟩
        simpa [Equiv.swap_apply_def] using And.intro (le_of_not_ge h12) (le_of_not_ge h01)

private def signs (s : Fin 3 → ℤ) (hs : ∀ i, s i * s i = 1) : IntegralBasis where
  val := Matrix.diagonal s
  inv := Matrix.diagonal s
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp [hs]
  inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp [hs]

private theorem signs_entries (A : Gram) (s : Fin 3 → ℤ) (hs : ∀ i, s i * s i = 1) (i j : Fin 3) :
    changeBasis A (signs s hs) i j = s i * A i j * s j := by
  change ((Matrix.diagonal s)ᵀ * A * Matrix.diagonal s) i j = _
  rw [Matrix.diagonal_transpose, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem change_symm {A : Gram} (hA : A.IsSymm) (T : IntegralBasis) : (changeBasis A T).IsSymm := by
  change (changeBasis A T)ᵀ = changeBasis A T
  rw [changeBasis, transpose_mul, transpose_mul, transpose_transpose, hA.eq, Matrix.mul_assoc]

theorem reduction_basis (A : Gram) (hA : nonnegativeForm A) :
    ∃ T : IntegralBasis, let B := changeBasis A T
      (∀ U : IntegralBasis, B.trace ≤ (changeBasis B U).trace) ∧
      B 0 0 ≤ B 1 1 ∧ B 1 1 ≤ B 2 2 ∧ B 0 1 ≤ 0 ∧ B 0 2 ≤ 0 := by
  obtain ⟨T,hT⟩ := exists_trace_minimizer A hA
  let B := changeBasis A T
  obtain ⟨σ,hσ1,hσ2⟩ := sort_three fun i => B i i
  let C := changeBasis B (relabel σ)
  have hCl : C = B.submatrix σ σ := relabel_entries B σ
  have htrace : C.trace = B.trace := by
    rw [hCl]
    exact Equiv.sum_comp σ (fun i => B i i)
  let s (i : Fin 3) : ℤ := if i = 0 then 1 else if 0 < C 0 i then -1 else 1
  have hs (i : Fin 3) : s i * s i = 1 := by
    by_cases hi : i = 0 <;> by_cases h : 0 < C 0 i <;> simp [s, hi, h]
  let U := signs s hs
  let D := changeBasis C U
  have hD : ∀ i j, D i j = s i * C i j * s j := signs_entries C s hs
  have hd (i : Fin 3) : D i i = C i i := by rw [hD]; linear_combination C i i * hs i
  have hDtrace : D.trace = C.trace := by
    simp only [Matrix.trace, Matrix.diag_apply, hd]
  have hsign (i : Fin 3) (hi : i ≠ 0) : D 0 i ≤ 0 := by
    rw [hD]
    simp only [s, if_pos rfl, one_mul, if_neg hi]
    split <;> (simp; omega)
  have hDform : D = changeBasis A (T * relabel σ * U) := by
    rw [← change_mul, ← change_mul]
  refine ⟨T * relabel σ * U, ?_⟩
  rw [← hDform]
  refine ⟨?_,?_,?_,hsign 1 (by decide),hsign 2 (by decide)⟩
  · intro V
    rw [hDtrace,htrace,hDform,change_mul]
    exact hT _
  · rw [hd,hd,hCl]
    exact hσ1
  · rw [hd,hd,hCl]
    exact hσ2

end TernaryBasisReduction

/- A determinant bound from the elementary basis-reduction inequalities. -/

namespace TernaryReducedBound

theorem determinant_lower {a b c d e f : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hd : 2 * |d| ≤ b) (he0 : 0 ≤ e) (hf0 : 0 ≤ f) (he : 2 * e ≤ a) (hf : 2 * f ≤ a)
    (htriple : 2 * (d + e + f) ≤ a + b) :
    a*b*c ≤ 5 * (a*b*c - a*d*d - b*e*e - c*f*f - 2*d*e*f) := by
  have hb := ha.trans_le hab
  have hc := hb.trans_le hbc
  have he' : e ≤ a / 2 := by linarith
  have hf' : f ≤ a / 2 := by linarith
  have hd' : |d| ≤ b / 2 := by linarith
  obtain ⟨hdlo,hdhi⟩ := abs_le.mp hd'
  have halfa : 0 ≤ a / 2 := by positivity
  have heSq := mul_le_mul he' he' he0 halfa
  have hfSq := mul_le_mul hf' hf' hf0 halfa
  have hAfirst : (3 / 4 : ℝ) * a*b ≤ a*b - f*f := by
    have hAA := mul_le_mul_of_nonneg_left hab ha.le
    nlinarith only [hfSq, hAA]
  have hAsecond : (3 / 4 : ℝ) * c ≤ c - e*e/a := by
    have hAA := mul_le_mul_of_nonneg_left (hab.trans hbc) ha.le
    have hE : e*e/a ≤ c / 4 := (div_le_iff₀ ha).mpr (by nlinarith only [heSq, hAA])
    linarith only [hE]
  let u := d + e*f/a
  have hulo : -(9 * b / 16) ≤ u := by
    dsimp [u]
    linarith only [hdlo, div_nonneg (mul_nonneg he0 hf0) ha.le, hb.le]
  have huhi : u ≤ 9 * b / 16 := by
    by_cases hdpos : 0 ≤ d
    · let t := b/2 - d
      let s := e + f
      have ht : 0 ≤ t := sub_nonneg.mpr hdhi
      have hs0 : 0 ≤ s := add_nonneg he0 hf0
      have hsA : s ≤ a := by dsimp [s]; linarith only [he',hf']
      have hst : s - a/2 ≤ t := by dsimp [s,t]; linarith only [htriple]
      have hs₁ := mul_le_mul_of_nonneg_right hst (add_nonneg hs0 halfa)
      have hs₂ := mul_le_mul_of_nonneg_left (show s + a/2 ≤ 3*a/2 by linarith only [hsA]) ht
      have heqs : e*f ≤ a*a/16 + a*t := by
        have hsq : 4*e*f ≤ s*s := by dsimp [s]; nlinarith only [sq_nonneg (e-f)]
        have hst' : 0 ≤ a*t := mul_nonneg ha.le ht
        nlinarith only [hs₁, hs₂, hsq, hst']
      have hediv : e*f/a ≤ a/16 + t := (div_le_iff₀ ha).mpr (by linarith only [heqs])
      dsimp [u,t] at *
      linarith only [hediv,hab]
    · have hef := mul_le_mul he' hf' hf0 halfa
      have hediv : e*f/a ≤ a/4 := (div_le_iff₀ ha).mpr (by nlinarith only [hef])
      dsimp [u]
      linarith only [le_of_not_ge hdpos, hediv, hab, hb.le]
  have hu : |u| ≤ 9*b/16 := abs_le.mpr ⟨hulo,huhi⟩
  have huSq : u*u ≤ (9*b/16)*(9*b/16) := by
    have h := mul_le_mul hu hu (abs_nonneg u) (by positivity : 0 ≤ 9*b/16)
    rwa [← abs_mul, abs_of_nonneg (mul_self_nonneg u)] at h
  have hlin : a*b*c - a*d*d - b*e*e - c*f*f - 2*d*e*f =
      (a*b - f*f) * (c - e*e/a) - a*u*u := by
    dsimp [u]
    field_simp
    ring
  have habc : 0 ≤ a*b*c := by positivity
  have hfst := mul_le_mul hAfirst hAsecond (by positivity : 0 ≤ (3 / 4 : ℝ) * c)
    ((by positivity : 0 ≤ (3 / 4 : ℝ) * a*b).trans hAfirst)
  have hsec := mul_le_mul_of_nonneg_left huSq ha.le
  have hBB := mul_le_mul_of_nonneg_left hbc (show 0 ≤ a*b from mul_nonneg ha.le hb.le)
  rw [hlin]
  nlinarith only [hfst,hsec,hBB,habc]

end TernaryReducedBound

/- Finite arithmetic in the classification of the determinant-225 ternary genus. -/

namespace A287616GenusCertificate

open Finset

def value (a b c d e f x y z : ℤ) : ℤ :=
  a*x*x + b*y*y + c*z*z - 2*d*y*z - 2*e*x*z - 2*f*x*y

def residueCount (m : ℕ) (r a b c d e f : ℤ) : ℕ :=
  ((univ : Finset (Fin m × Fin m × Fin m)).filter fun xyz =>
    value a b c d e f xyz.1.val xyz.2.1.val xyz.2.2.val % (m : ℤ) = r).card

def isRepresentative (a b c d e f : ℤ) : Prop :=
  (a = 3 ∧ b = 5 ∧ c = 15 ∧ d = 0 ∧ e = 0 ∧ f = 0) ∨
    (a = 2 ∧ b = 8 ∧ c = 15 ∧ d = 0 ∧ e = 0 ∧ f = 1)

instance (a b c d e f : ℤ) : Decidable (isRepresentative a b c d e f) := by
  unfold isRepresentative
  infer_instance

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 6000 in
private theorem finite_certificate :
    ∀ (aa : Fin 11) (bb : Fin ((1125 / aa.val).sqrt + 1)) (dd : Fin (bb.val + 1))
      (ee ff : Fin (aa.val / 2 + 1)),
      let a : ℤ := aa.val
      let b : ℤ := bb.val
      let d : ℤ := (dd.val : ℤ) - (bb.val : ℤ) / 2
      let e : ℤ := ee.val
      let f : ℤ := ff.val
      let c := (225 + a*d*d + b*e*e + 2*d*e*f) / (a*b - f*f)
      0 < a → a ≤ b → b ≤ c → a*b*c ≤ 1125 →
      2*|d| ≤ b → 2*e ≤ a → 2*f ≤ a →
      a*b*c - a*d*d - b*e*e - c*f*f - 2*d*e*f = 225 →
      residueCount 3 0 a b c d e f = 9 → residueCount 3 1 a b c d e f = 0 →
      residueCount 4 0 a b c d e f = 24 → isRepresentative a b c d e f := by
  intro a
  fin_cases a <;> decide +kernel

theorem classify_reduced {a b c d e f : ℤ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hprod : a*b*c ≤ 1125) (hd : 2*|d| ≤ b) (he0 : 0 ≤ e) (he : 2*e ≤ a)
    (hf0 : 0 ≤ f) (hf : 2*f ≤ a)
    (hdet : a*b*c - a*d*d - b*e*e - c*f*f - 2*d*e*f = 225)
    (h30 : residueCount 3 0 a b c d e f = 9)
    (h31 : residueCount 3 1 a b c d e f = 0)
    (h40 : residueCount 4 0 a b c d e f = 24) : isRepresentative a b c d e f := by
  have ha11 : a < 11 := by
    by_contra! h
    have hab121 : 121 ≤ a*b := by
      have hh := mul_le_mul h (h.trans hab) (by norm_num) ha.le
      norm_num at hh
      exact hh
    have hh := mul_le_mul hab121 (h.trans (hab.trans hbc)) (by norm_num) (by positivity : 0 ≤ a*b)
    norm_num at hh
    omega
  have hb0 := ha.le.trans hab
  have hbMax : b.toNat ≤ (1125 / a.toNat).sqrt := by
    rw [Nat.le_sqrt, Nat.le_div_iff_mul_le (by omega : 0 < a.toNat)]
    have h := (mul_le_mul_of_nonneg_left hbc (mul_nonneg ha.le hb0)).trans hprod
    have h' : b*b*a ≤ 1125 := by linarith only [h]
    exact_mod_cast (show ((b.toNat : ℤ) * (b.toNat : ℤ) * (a.toNat : ℤ)) ≤ (1125 : ℤ) by
      simpa only [Int.toNat_of_nonneg hb0, Int.toNat_of_nonneg ha.le] using h')
  have hdL : -(b / 2) ≤ d := by
    have hh := neg_abs_le d
    omega
  have hdU : d ≤ b / 2 := by
    have hh := le_abs_self d
    omega
  have hden : a*b - f*f ≠ 0 := by
    have hff := mul_self_lt_mul_self hf0 (by omega : f < a)
    have hAA := mul_le_mul_of_nonneg_left hab ha.le
    omega
  have hc : (225 + a*d*d + b*e*e + 2*d*e*f) / (a*b - f*f) = c := by
    have h := show 225 + a*d*d + b*e*e + 2*d*e*f = c * (a*b - f*f) by
      linear_combination -hdet
    rw [h, Int.mul_ediv_cancel _ hden]
  let aa : Fin 11 := ⟨a.toNat, by omega⟩
  let bb : Fin ((1125 / aa.val).sqrt + 1) := ⟨b.toNat, Nat.lt_succ_of_le hbMax⟩
  let dd : Fin (bb.val + 1) := ⟨(d+b/2).toNat, by change (d+b/2).toNat < b.toNat + 1; omega⟩
  let ee : Fin (aa.val / 2 + 1) := ⟨e.toNat, by change e.toNat < a.toNat / 2 + 1; omega⟩
  let ff : Fin (aa.val / 2 + 1) := ⟨f.toNat, by change f.toNat < a.toNat / 2 + 1; omega⟩
  have ha' : (aa.val : ℤ) = a := Int.toNat_of_nonneg ha.le
  have hb' : (bb.val : ℤ) = b := Int.toNat_of_nonneg (ha.le.trans hab)
  have hd' : (dd.val : ℤ) - (bb.val : ℤ) / 2 = d := by
    have h : (dd.val : ℤ) = d + b / 2 := Int.toNat_of_nonneg (by omega)
    rw [h,hb']; ring
  have he' : (ee.val : ℤ) = e := Int.toNat_of_nonneg he0
  have hf' : (ff.val : ℤ) = f := Int.toNat_of_nonneg hf0
  have h := finite_certificate aa bb dd ee ff
  dsimp only at h
  rw [hd',ha',hb',he',hf',hc] at h
  exact h ha hab hbc hprod hd he hf hdet h30 h31 h40

open Matrix

def gram (a b c d e f : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![a, -f, -e; -f, b, -d; -e, -d, c]

private def tripleEquiv (R : Type*) : R × R × R ≃ (Fin 3 → R) where
  toFun x := ![x.1, x.2.1, x.2.2]
  invFun v := (v 0, v 1, v 2)
  left_inv x := by cases x; rfl
  right_inv v := by funext i; fin_cases i <;> rfl

private def residues (m : ℕ) [NeZero m] : Fin m ≃ ZMod m where
  toFun i := i.val
  invFun x := ⟨x.val, x.val_lt⟩
  left_inv i := Fin.ext (ZMod.val_cast_of_lt i.isLt)
  right_inv x := ZMod.natCast_zmod_val x

private theorem gram_value {m : ℕ} (a b c d e f : ℤ) (x y z : ℕ) :
    let v : Fin 3 → ZMod m := ![(x : ZMod m), (y : ZMod m), (z : ZMod m)]
    v ⬝ᵥ ((gram a b c d e f).map (Int.castRingHom (ZMod m)) *ᵥ v) =
      (value a b c d e f (x : ℤ) y z : ZMod m) := by
  dsimp only [Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_three]
  simp only [Fin.sum_univ_three, Matrix.map_apply, Int.coe_castRingHom]
  change (x : ZMod m) * ((a : ZMod m) * x + (-f : ℤ) * y + (-e : ℤ) * z) +
    (y : ZMod m) * (((-f : ℤ) : ZMod m) * x + (b : ZMod m) * y + (-d : ℤ) * z) +
    (z : ZMod m) * (((-e : ℤ) : ZMod m) * x + ((-d : ℤ) : ZMod m) * y + (c : ZMod m) * z) = _
  push_cast [value]
  ring

theorem residue_count_as_gram {m : ℕ} [NeZero m] {r : ℤ} (hr : 0 ≤ r) (hrm : r < m)
    (a b c d e f : ℤ) : residueCount m r a b c d e f =
      Fintype.card {v : Fin 3 → ZMod m //
        v ⬝ᵥ ((gram a b c d e f).map (Int.castRingHom (ZMod m)) *ᵥ v) = (r : ZMod m)} := by
  let E : Fin m × Fin m × Fin m ≃ (Fin 3 → ZMod m) :=
    ((residues m).prodCongr ((residues m).prodCongr (residues m))).trans (tripleEquiv _)
  unfold residueCount
  rw [← Fintype.card_coe]
  apply Fintype.card_congr (E.subtypeEquiv ?_)
  intro x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change _ ↔ ![(x.1.val : ZMod m), (x.2.1.val : ZMod m), (x.2.2.val : ZMod m)] ⬝ᵥ
      ((gram a b c d e f).map (Int.castRingHom (ZMod m)) *ᵥ
        ![(x.1.val : ZMod m), (x.2.1.val : ZMod m), (x.2.2.val : ZMod m)]) = (r : ZMod m)
  rw [gram_value, ZMod.intCast_eq_intCast_iff', Int.emod_eq_of_lt hr hrm]

private def matrixEquiv {R : Type*} [CommRing R] (T : Matrix.GeneralLinearGroup (Fin 3) R) :
    (Fin 3 → R) ≃ (Fin 3 → R) where
  toFun v := (T : Matrix _ _ _) *ᵥ v
  invFun v := ((T⁻¹ : Matrix.GeneralLinearGroup (Fin 3) R) : Matrix _ _ _) *ᵥ v
  left_inv v := by
    dsimp only
    have hT : ((T⁻¹ : Matrix.GeneralLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) *
        (T : Matrix (Fin 3) (Fin 3) R) = 1 := T.inv_val
    rw [Matrix.mulVec_mulVec, hT, one_mulVec]
  right_inv v := by
    dsimp only
    have hT : (T : Matrix (Fin 3) (Fin 3) R) *
        ((T⁻¹ : Matrix.GeneralLinearGroup (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = 1 := T.val_inv
    rw [Matrix.mulVec_mulVec, hT, one_mulVec]

theorem card_of_gram_congruence {m : ℕ} [NeZero m] (r : ZMod m)
    (A B : Matrix (Fin 3) (Fin 3) (ZMod m)) (T : Matrix.GeneralLinearGroup (Fin 3) (ZMod m))
    (h : A = (T : Matrix _ _ _)ᵀ * B * (T : Matrix _ _ _)) :
    Fintype.card {v : Fin 3 → ZMod m // v ⬝ᵥ (A *ᵥ v) = r} =
      Fintype.card {v : Fin 3 → ZMod m // v ⬝ᵥ (B *ᵥ v) = r} := by
  apply Fintype.card_congr ((matrixEquiv T).subtypeEquiv ?_)
  intro v
  change v ⬝ᵥ (A *ᵥ v) = r ↔ ((T : Matrix _ _ _) *ᵥ v) ⬝ᵥ (B *ᵥ ((T : Matrix _ _ _) *ᵥ v)) = r
  rw [h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

private theorem descend_congruence {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {A B : Matrix (Fin 3) (Fin 3) ℤ} (T : Matrix.GeneralLinearGroup (Fin 3) R)
    (h : A.map (Int.castRingHom R) = (T : Matrix _ _ _)ᵀ * B.map (Int.castRingHom R) * (T : Matrix _ _ _)) :
    let U := Matrix.GeneralLinearGroup.map φ T
    A.map (Int.castRingHom S) = (U : Matrix _ _ _)ᵀ * B.map (Int.castRingHom S) * (U : Matrix _ _ _) := by
  dsimp only
  have h' := congrArg φ.mapMatrix h
  rw [map_mul, map_mul] at h'
  have hA : φ.mapMatrix (A.map (Int.castRingHom R)) = A.map (Int.castRingHom S) := by
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.map_apply]
  have hB : φ.mapMatrix (B.map (Int.castRingHom R)) = B.map (Int.castRingHom S) := by
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [hA, hB] at h'
  exact h'

theorem classify_reduced_padic {a b c d e f : ℤ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hprod : a*b*c ≤ 1125) (hd : 2*|d| ≤ b) (he0 : 0 ≤ e) (he : 2*e ≤ a)
    (hf0 : 0 ≤ f) (hf : 2*f ≤ a) (hdet : (gram a b c d e f).det = 225)
    (hloc : ∀ (p : ℕ) [Fact p.Prime], ∃ T : Matrix.GeneralLinearGroup (Fin 3) ℤ_[p],
      (gram a b c d e f).map (Int.castRingHom ℤ_[p]) =
        (T : Matrix _ _ _)ᵀ * (gram 15 5 3 0 0 0).map (Int.castRingHom ℤ_[p]) * (T : Matrix _ _ _)) :
    isRepresentative a b c d e f := by
  obtain ⟨T,hT⟩ := hloc 3
  obtain ⟨U,hU⟩ := hloc 2
  let T' := Matrix.GeneralLinearGroup.map (PadicInt.toZMod (p := 3)) T
  let U' := Matrix.GeneralLinearGroup.map (PadicInt.toZModPow (p := 2) 2) U
  have h3 := descend_congruence (PadicInt.toZMod (p := 3)) T hT
  have h4 := descend_congruence (PadicInt.toZModPow (p := 2) 2) U hU
  have hc3 (r : ℤ) (hr : 0 ≤ r) (hlt : r < 3) :
      residueCount 3 r a b c d e f = residueCount 3 r 15 5 3 0 0 0 := by
    rw [residue_count_as_gram hr hlt, residue_count_as_gram hr hlt]
    exact card_of_gram_congruence (r : ZMod 3) _ _ T' h3
  have hc4 : residueCount 4 0 a b c d e f = residueCount 4 0 15 5 3 0 0 0 := by
    rw [residue_count_as_gram (by norm_num) (by norm_num),
      residue_count_as_gram (by norm_num) (by norm_num)]
    exact card_of_gram_congruence ((0 : ℤ) : ZMod 4) _ _ U' h4
  refine classify_reduced ha hab hbc hprod hd he0 he hf0 hf ?_
    ((hc3 0 (by norm_num) (by norm_num)).trans (by decide))
    ((hc3 1 (by norm_num) (by norm_num)).trans (by decide)) (hc4.trans (by decide))
  rw [Matrix.det_fin_three] at hdet
  change a*b*c - a*(-d)*(-d) - (-f)*(-f)*c + (-f)*(-d)*(-e) + (-e)*(-f)*(-d) - (-e)*b*(-e) = 225 at hdet
  linear_combination hdet

end A287616GenusCertificate

/- Complete arithmetic classification of the two integral forms in the A287616 genus. -/

namespace A287616ClassifyGenus

open Matrix Finset
open TernaryBasisReduction
open A287616GenusCertificate (gram)

private theorem gram_eval {R : Type*} [CommRing R] (a b c d e f : ℤ) (v : Fin 3 → R) :
    v ⬝ᵥ ((gram a b c d e f).map (Int.castRingHom R) *ᵥ v) =
      a*(v 0)^2 + b*(v 1)^2 + c*(v 2)^2 - 2*d*v 1*v 2 - 2*e*v 0*v 2 - 2*f*v 0*v 1 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.map_apply, Int.coe_castRingHom]
  change v 0 * ((a : R) * v 0 + (-f : ℤ) * v 1 + (-e : ℤ) * v 2) +
    v 1 * (((-f : ℤ) : R) * v 0 + (b : R) * v 1 + (-d : ℤ) * v 2) +
    v 2 * (((-e : ℤ) : R) * v 0 + ((-d : ℤ) : R) * v 1 + (c : R) * v 2) = _
  push_cast
  ring

private theorem cast_eval (M : Gram) (v : Fin 3 → ℤ) :
    ((v ⬝ᵥ (M *ᵥ v) : ℤ) : ℝ) =
      (fun i => (v i : ℝ)) ⬝ᵥ (M.map (Int.castRingHom ℝ) *ᵥ fun i => (v i : ℝ)) := by
  simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Matrix.map_apply, Int.coe_castRingHom]

private theorem positive_eval {M : Gram} (T : Matrix.GeneralLinearGroup (Fin 3) ℝ)
    (hM : M.map (Int.castRingHom ℝ) = (T : Matrix _ _ _)ᵀ *
      (gram 15 5 3 0 0 0).map (Int.castRingHom ℝ) * (T : Matrix _ _ _))
    (v : Fin 3 → ℤ) (hv : v ≠ 0) : 0 < v ⬝ᵥ (M *ᵥ v) := by
  have h' : 0 < ((v ⬝ᵥ (M *ᵥ v) : ℤ) : ℝ) := by
    rw [cast_eval, hM, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_transpose_mulVec, dotProduct_comm, gram_eval]
    let w := (T : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ fun i => (v i : ℝ)
    have hw : w ≠ 0 := by
      intro h
      have he := congrArg (fun x => ((T⁻¹ : Matrix.GeneralLinearGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x) h
      dsimp only [w] at he
      have hmul : ((T⁻¹ : Matrix.GeneralLinearGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *
          (T : Matrix (Fin 3) (Fin 3) ℝ) = 1 := T.inv_val
      rw [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec, Matrix.mulVec_zero] at he
      apply hv
      funext i
      have hi := congrFun he i
      change (v i : ℝ) = 0 at hi
      change v i = 0
      exact_mod_cast hi
    norm_num only [Int.cast_ofNat, Int.cast_zero, mul_zero, zero_mul, sub_zero]
    change 0 < (15 : ℝ) * (w 0)^2 + 5*(w 1)^2 + 3*(w 2)^2
    have hw' : w 0 ≠ 0 ∨ w 1 ≠ 0 ∨ w 2 ≠ 0 := by
      by_contra! h
      apply hw
      funext i
      fin_cases i
      · exact h.1
      · exact h.2.1
      · exact h.2.2
    rcases hw' with h | h | h <;> nlinarith [sq_pos_of_ne_zero h, sq_nonneg (w 0),
      sq_nonneg (w 1), sq_nonneg (w 2)]
  exact_mod_cast h'

private theorem basis_congruence {R : Type*} [CommRing R] {M : Gram} (T : IntegralBasis)
    (S : Matrix.GeneralLinearGroup (Fin 3) R)
    (h : M.map (Int.castRingHom R) = (S : Matrix _ _ _)ᵀ *
      (gram 15 5 3 0 0 0).map (Int.castRingHom R) * (S : Matrix _ _ _)) :
    let U := S * Matrix.GeneralLinearGroup.map (Int.castRingHom R) T
    (changeBasis M T).map (Int.castRingHom R) = (U : Matrix _ _ _)ᵀ *
      (gram 15 5 3 0 0 0).map (Int.castRingHom R) * (U : Matrix _ _ _) := by
  rw [map_change, h]
  simp only [Units.val_mul, transpose_mul, Matrix.mul_assoc]

private theorem eval_gram_int (a b c d e f : ℤ) (v : Fin 3 → ℤ) :
    v ⬝ᵥ (gram a b c d e f *ᵥ v) =
      a*(v 0)^2 + b*(v 1)^2 + c*(v 2)^2 - 2*d*v 1*v 2 - 2*e*v 0*v 2 - 2*f*v 0*v 1 := by
  simpa [Matrix.map_id] using (gram_eval (R := ℤ) a b c d e f v)

theorem classify (M : Gram) (hSymm : M.IsSymm) (hDet : M.det = 225)
    (hReal : ∃ T : Matrix.GeneralLinearGroup (Fin 3) ℝ,
      M.map (Int.castRingHom ℝ) = (T : Matrix _ _ _)ᵀ *
        (gram 15 5 3 0 0 0).map (Int.castRingHom ℝ) * (T : Matrix _ _ _))
    (hLocal : ∀ (p : ℕ) [Fact p.Prime], ∃ T : Matrix.GeneralLinearGroup (Fin 3) ℤ_[p],
      M.map (Int.castRingHom ℤ_[p]) = (T : Matrix _ _ _)ᵀ *
        (gram 15 5 3 0 0 0).map (Int.castRingHom ℤ_[p]) * (T : Matrix _ _ _)) :
    (∃ T : IntegralBasis, ∀ v : Fin 3 → ℤ,
      let w := (T : Gram) *ᵥ v
      v ⬝ᵥ (M *ᵥ v) = 15*(w 0)^2 + 5*(w 1)^2 + 3*(w 2)^2) ∨
    (∃ T : IntegralBasis, ∀ v : Fin 3 → ℤ,
      let w := (T : Gram) *ᵥ v
      v ⬝ᵥ (M *ᵥ v) = 2*(w 0)^2 - 2*w 0*w 1 + 8*(w 1)^2 + 15*(w 2)^2) := by
  obtain ⟨R,hR⟩ := hReal
  obtain ⟨S,hmin,hab,hbc,hf0,he0⟩ := reduction_basis M (by
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · exact (positive_eval R hR v hv).le)
  let N := changeBasis M S
  have hnSymm := change_symm hSymm S
  have ha : 0 < N 0 0 := by
    have hv : (Pi.single (0 : Fin 3) (1 : ℤ) : Fin 3 → ℤ) ≠ 0 := by
      intro he
      have := congrFun he 0
      simp at this
    have hp := positive_eval (R * Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) S)
      (basis_congruence S R hR) _ hv
    simpa [dotProduct, Matrix.mulVec, Pi.single, Function.update] using hp
  let a := N 0 0
  let b := N 1 1
  let c := N 2 2
  let d := -N 1 2
  let e := -N 0 2
  let f := -N 0 1
  have hN : N = gram a b c d e f := by
    have h10 : N 1 0 = N 0 1 := congrFun (congrFun hnSymm.eq 0) 1
    have h20 : N 2 0 = N 0 2 := congrFun (congrFun hnSymm.eq 0) 2
    have h21 : N 2 1 = N 1 2 := congrFun (congrFun hnSymm.eq 1) 2
    ext i j
    fin_cases i <;> fin_cases j <;>
      first | rfl | change _ = -(-_) <;> rw [neg_neg] <;> first | rfl | assumption
  have hDetS : (S : Gram).det * (S : Gram).det = 1 := by
    rcases Int.isUnit_iff.mp (Matrix.isUnits_det_units S) with h | h <;> simp [h]
  have hDetN : N.det = 225 := by
    simp only [N, changeBasis, Matrix.det_mul, Matrix.det_transpose, hDet]
    rw [mul_comm ((S : Gram).det) 225, mul_assoc, hDetS, mul_one]
  have hpoly : a*b*c - a*d*d - b*e*e - c*f*f - 2*d*e*f = 225 := by
    rw [hN, Matrix.det_fin_three] at hDetN
    change a*b*c - a*(-d)*(-d) - (-f)*(-f)*c + (-f)*(-d)*(-e) + (-e)*(-f)*(-d) - (-e)*b*(-e) = 225 at hDetN
    linear_combination hDetN
  have hd : 2*|d| ≤ b := by
    simpa [d,b] using trace_minimal_off_diagonal hnSymm hmin (show (1 : Fin 3) ≠ 2 by decide)
  have he : 2*e ≤ a := by
    have hh := trace_minimal_off_diagonal hnSymm hmin (show (0 : Fin 3) ≠ 2 by decide)
    dsimp [e,a]
    linarith [neg_abs_le (N 0 2)]
  have hf : 2*f ≤ a := by
    have hh := trace_minimal_off_diagonal hnSymm hmin (show (0 : Fin 3) ≠ 1 by decide)
    dsimp [f,a]
    linarith [neg_abs_le (N 0 1)]
  have ht : 2*(d+e+f) ≤ a+b := by
    have hh := trace_minimal_triple hnSymm hmin
    dsimp [a,b,d,e,f]
    linarith
  have hbound : a*b*c ≤ 1125 := by
    have hh : a*b*c ≤ 5 * (a*b*c - a*d*d - b*e*e - c*f*f - 2*d*e*f) := by
      exact_mod_cast TernaryReducedBound.determinant_lower
        (a := (a : ℝ)) (b := (b : ℝ)) (c := (c : ℝ)) (d := (d : ℝ)) (e := (e : ℝ)) (f := (f : ℝ))
        (by exact_mod_cast ha) (by exact_mod_cast hab) (by exact_mod_cast hbc) (by exact_mod_cast hd)
        (by exact_mod_cast neg_nonneg.mpr he0) (by exact_mod_cast neg_nonneg.mpr hf0) (by exact_mod_cast he)
        (by exact_mod_cast hf) (by exact_mod_cast ht)
    rw [hpoly] at hh
    exact hh
  have hrep := A287616GenusCertificate.classify_reduced_padic ha hab hbc hbound hd
    (neg_nonneg.mpr he0) he (neg_nonneg.mpr hf0) hf (by rw [← hN]; exact hDetN) (by
      intro p hp
      obtain ⟨T,hT⟩ := hLocal p
      refine ⟨T * Matrix.GeneralLinearGroup.map (Int.castRingHom ℤ_[p]) S, ?_⟩
      rw [← hN]
      exact basis_congruence S T hT)
  rcases hrep with ⟨h1,h2,h3,h4,h5,h6⟩ | ⟨h1,h2,h3,h4,h5,h6⟩
  · change a = 3 at h1
    change b = 5 at h2
    change c = 15 at h3
    change e = 0 at h5
    change f = 0 at h6
    let P := relabel (Equiv.swap (0 : Fin 3) 2)
    let T := S * P
    have hT : changeBasis M T = gram 15 5 3 0 0 0 := by
      change changeBasis M (S * P) = _
      rw [← change_mul, show changeBasis M S = N from rfl, hN, h1,h2,h3,h4,h5,h6,
        relabel_entries]
      decide
    apply Or.inl
    refine ⟨T⁻¹, fun v => ?_⟩
    have hh : changeBasis (gram 15 5 3 0 0 0) T⁻¹ = M := by
      rw [← hT, change_mul, mul_inv_cancel, change_one]
    rw [← hh, eval_change]
    simpa only [Int.cast_ofNat, Int.cast_zero, mul_zero, zero_mul, sub_zero] using
      eval_gram_int 15 5 3 0 0 0 ((T⁻¹ : IntegralBasis) *ᵥ v)
  · change a = 2 at h1
    change b = 8 at h2
    change c = 15 at h3
    change e = 0 at h5
    change f = 1 at h6
    rw [h1,h2,h3,h4,h5,h6] at hN
    apply Or.inr
    refine ⟨S⁻¹, fun v => ?_⟩
    have hh : changeBasis (gram 2 8 15 0 0 1) S⁻¹ = M := by
      rw [← hN]
      change changeBasis (changeBasis M S) S⁻¹ = M
      rw [change_mul, mul_inv_cancel, change_one]
    rw [← hh, eval_change]
    have hh := eval_gram_int 2 8 15 0 0 1 ((S⁻¹ : IntegralBasis) *ᵥ v)
    linear_combination hh

end A287616ClassifyGenus


open Matrix

private theorem diagonal_progression_value {K : Type*} [CommRing K] (a b c : K) :
    (![a, b, c] : Fin 3 → K) ⬝ᵥ
      (A287616GenusTransport.baseGram.map (Int.castRingHom K) *ᵥ ![a, b, c]) =
      15 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 := by
  simp [A287616GenusTransport.baseGram, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

theorem OMA.solution : OMA.R_OeisA287616_conjecture_R1_H1_R1.H1 := by
  intro n
  let Q := A287616GenusTransport.baseGram
  let m := 120 * (n : ℤ) + 23
  have hQ : Q.IsSymm := by
    change Qᵀ = Q
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hm : m ≠ 0 := by dsimp [m]; positivity
  obtain ⟨a, b, c, hr⟩ := A287616RationalProgression.rational_rep_120n_add_23 n
  have hrat : ∃ r : Fin 3 → ℚ, r ⬝ᵥ (Q.map (Int.castRingHom ℚ) *ᵥ r) = (m : ℚ) := by
    refine ⟨![a, b, c], (diagonal_progression_value a b c).trans ?_⟩
    simpa [m] using hr
  have hp (p : ℕ) [Fact p.Prime] : ∃ y : Fin 3 → ℤ_[p],
      y ⬝ᵥ (Q.map (Int.castRingHom ℤ_[p]) *ᵥ y) = (m : ℤ_[p]) ∧ ∃ i, IsUnit (y i) := by
    have h := if hd : p ∣ 30 then A287616SmallPrimes.smallPrimes n p hd
      else A287616SmallPrimes.otherPrimes n p hd
    obtain ⟨d, e, f, hd, hu⟩ := h
    refine ⟨![d, e, f], (diagonal_progression_value d e f).trans ?_, ?_⟩
    · simpa [m] using hd
    · rcases hu with h | h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
  obtain ⟨M, v, hs, hre, hloc, hv, hprim⟩ :=
    PrimitiveGenusAssembly.integral_genus_from_rational_and_primitive_local Q hQ m hm hrat hp
  have hgen : A287616GenusTransport.InGenus M := ⟨hs, hre, hloc⟩
  have hdet := A287616GenusTransport.genus_det hgen
  rcases A287616ClassifyGenus.classify M hs hdet hre hloc with ⟨T, hT⟩ | ⟨T, hT⟩
  · exact Or.inl ⟨_, _, _, (hT v).symm.trans hv, A287616GenusTransport.primitive_mulVec T v hprim⟩
  · exact Or.inr ⟨_, _, _, (hT v).symm.trans hv, A287616GenusTransport.primitive_mulVec T v hprim⟩

