import FormalConjectures.GreensOpenProblems.«38»
import Mathlib.Analysis.Fourier.ZMod

open Finset Green38 ComplexConjugate
open scoped Pointwise

theorem OMA.solution : type_of% @Green38.green_38.variants.best_upper := by
  classical
  intro ε hε
  refine Filter.Eventually.of_forall fun n => ?_
  obtain ⟨A, hA, he⟩ := Nat.sSup_mem
    (show (ValidCardinalities n).Nonempty from ⟨0, green_38.test_zero_mem_validCardinalities⟩)
    green_38.test_bound_above
  let c := Real.cos (Real.pi / 7)
  have hc : 0 < c := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  let χ : AddChar (ZMod 7) ℂ := ZMod.stdAddChar
  let w (k : ZMod 7) := 1 + (χ k).re / c
  have hre (k : ZMod 7) : (χ k).re = Real.cos (2 * Real.pi * k.val / 7) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_eq_circleExp, Circle.coe_exp, Complex.exp_re]
    norm_num; ring_nf
  have hwn (k : ZMod 7) : 0 ≤ w k := by
    have hp := Real.pi_pos; have hk := k.val_lt
    have hb : -c ≤ Real.cos (2 * Real.pi * k.val / 7) := by
      rw [show -c = Real.cos (Real.pi - Real.pi / 7) by rw [Real.cos_pi_sub]]
      by_cases h : k.val ≤ 3
      · have hk' : (k.val : ℝ) ≤ 3 := by exact_mod_cast h
        exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith)
          (by nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hk')])
      · have h4 : (4 : ℝ) ≤ k.val := by exact_mod_cast (show 4 ≤ k.val by omega)
        have h7 : (k.val : ℝ) ≤ 7 := by exact_mod_cast hk.le
        rw [← Real.cos_two_pi_sub (2 * Real.pi * k.val / 7)]
        exact Real.cos_le_cos_of_nonneg_of_le_pi
          (by nlinarith [mul_nonneg hp.le (sub_nonneg.mpr h7)]) (by linarith)
          (by nlinarith [mul_nonneg hp.le (sub_nonneg.mpr h4)])
    rw [show w k = 1 + Real.cos (2 * Real.pi * k.val / 7) / c by rw [← hre]]
    have := (le_div_iff₀ hc).2 (show -1 * c ≤ _ by linarith); linarith
  have hneg (k : ZMod 7) : χ (-k) = conj (χ k) := by
    rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
  have hcs (d : ZMod 7) : ∑ k : ZMod 7, χ (k * d) = if d = 0 then 7 else 0 := by
    simpa using AddChar.sum_mulShift d (ZMod.isPrimitive_stdAddChar 7)
  let ker (d : ZMod 7) := ∑ k : ZMod 7, (w k : ℂ) * χ (k * d)
  have hker (d : ZMod 7) : ker d = (if d = 0 then 7 else 0) +
      ((if d + 1 = 0 then 7 else 0) + (if d - 1 = 0 then 7 else 0)) / (2 * (c : ℂ)) := by
    calc ker d = ∑ k : ZMod 7, (χ (k * d) + (χ (k * (d + 1)) + χ (k * (d - 1))) / (2 * (c : ℂ))) :=
        sum_congr rfl fun k _ => by
          rw [show (w k : ℂ) = 1 + (χ k + conj (χ k)) / 2 / (c : ℂ) by
            simp [w, Complex.re_eq_add_conj], mul_add, mul_sub, mul_one, sub_eq_add_neg,
            AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hneg]; ring
      _ = _ := by rw [sum_add_distrib, ← sum_div, sum_add_distrib, hcs, hcs, hcs]
  let W (k : Fin n → ZMod 7) := ∏ i, w (k i)
  let ph (k x : Fin n → ZMod 7) := ∏ i, χ (k i * x i)
  let K (x y : Fin n → ZMod 7) : ℂ := ∏ i, ker (x i - y i)
  let E (k : Fin n → ZMod 7) : ℝ := W k * Complex.normSq (∑ x ∈ A, ph k x)
  have hsum : ∑ k, E k = A.card * (7 : ℝ) ^ n := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum]
    have hexp : ∑ k, (E k : ℂ) = ∑ x ∈ A, ∑ y ∈ A, K x y := by
      calc _ = ∑ k, ∑ x ∈ A, ∑ y ∈ A, (W k : ℂ) * ph k x * conj (ph k y) :=
          sum_congr rfl fun k _ => by
            dsimp [E]; rw [Complex.ofReal_mul, ← Complex.mul_conj, map_sum]
            simp only [← mul_sum, ← sum_mul]; ring
        _ = _ := by
          rw [sum_comm]; refine sum_congr rfl fun x _ => ?_
          rw [sum_comm]; refine sum_congr rfl fun y _ => ?_
          simp only [W, ph, K, ker, Complex.ofReal_prod, map_prod, ← prod_mul_distrib]
          calc _ = ∑ k : Fin n → ZMod 7, ∏ i, (w (k i) : ℂ) * χ (k i * (x i - y i)) :=
              sum_congr rfl fun k _ => prod_congr rfl fun i _ => by
                rw [mul_sub, sub_eq_add_neg, AddChar.map_add_eq_mul, hneg, mul_assoc]
            _ = _ := by rw [prod_univ_sum, Fintype.piFinset_univ]
    rw [hexp]
    have hdiag (x : Fin n → ZMod 7) (hx : x ∈ A) (y : Fin n → ZMod 7) (hy : y ∈ A) :
        K x y = if x = y then (7 : ℂ) ^ n else 0 := by
      by_cases hxy : x = y
      · subst y; simp [K, hker, show (1 : ZMod 7) ≠ 0 by decide]
      · rw [if_neg hxy]
        have ⟨i, hi⟩ := not_forall.1 fun h =>
          hxy (sub_eq_zero.1 (hA _ (mem_sub.2 ⟨x, hx, y, hy, rfl⟩) h))
        refine prod_eq_zero (mem_univ i) ?_
        simp only [Pi.sub_apply, mem_insert, mem_singleton, not_or] at hi
        simp [hker, hi.2.1, show x i - y i + 1 ≠ 0 from fun h => hi.1 (by linear_combination h),
          sub_ne_zero.2 hi.2.2]
    simpa using (sum_congr rfl fun x hx => sum_congr rfl fun y hy => hdiag x hx y hy).trans (by simp)
  have hb := (single_le_sum (f := E) (fun k _ => mul_nonneg (prod_nonneg fun i _ => hwn _)
    (Complex.normSq_nonneg _)) (mem_univ (0 : Fin n → ZMod 7))).trans_eq hsum
  have h0 : E 0 = (1 + 1 / c) ^ n * (A.card * A.card : ℝ) := by
    simp [E, W, w, ph, Complex.normSq_natCast]
  rw [h0] at hb
  have hC : C₂ = 7 / (1 + 1 / c) := by
    change 7 * c / (1 + c) = 7 / (1 + 1 / c); field_simp [hc.ne']; rw [add_comm c 1]
  have hAcard : (A.card : ℝ) ≤ C₂ ^ n := by
    rw [hC, div_pow, le_div_iff₀ (pow_pos (by positivity) _)]
    rcases eq_or_lt_of_le (Nat.cast_nonneg (α := ℝ) A.card) with h | h
    · rw [← h, zero_mul]; positivity
    · exact le_of_mul_le_mul_left (a := (A.card : ℝ)) (by nlinarith) h
  rw [he] at hAcard
  exact hAcard.trans (pow_le_pow_left₀ (by change 0 ≤ 7 * c / (1 + c); positivity) (by linarith) _)
