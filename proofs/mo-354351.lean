import OMAStatements.S_mo_354351
import Mathlib

namespace InverseVectorCost

open OMA.S_mo_354351 Finset Filter
open Matrix hiding gram

private theorem dot_nonneg {d : ℕ} (v : Vec d) : 0 ≤ v ⬝ᵥ v := by
  simpa [dotProduct, pow_two] using
    (Finset.sum_nonneg (s := Finset.univ) fun i _ => sq_nonneg (v i))

private theorem length_sq {d : ℕ} (v : Vec d) : length v ^ 2 = v ⬝ᵥ v :=
  Real.sq_sqrt (dot_nonneg v)

private theorem length_nonneg {d : ℕ} (v : Vec d) : 0 ≤ length v :=
  Real.sqrt_nonneg _

private theorem dot_cauchy {d : ℕ} (v w : Vec d) :
    (v ⬝ᵥ w)^2 ≤ (v ⬝ᵥ v) * (w ⬝ᵥ w) := by
  simpa [dotProduct, pow_two] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v w

private theorem outer_psd {d : ℕ} (v : Vec d) : (outer v).PosSemidef := by
  simpa [outer] using posSemidef_vecMulVec_self_star v

private theorem gram_succ {d : ℕ} (x : ℕ → Vec d) (t : ℕ) :
    gram x (t + 1) = gram x t + outer (x t) := by
  simp only [gram, Finset.sum_range_succ, add_assoc]

private theorem gram_posDef {d : ℕ} (x : ℕ → Vec d) (t : ℕ) :
    (gram x t).PosDef := by
  apply Matrix.PosDef.one.add_posSemidef
  exact Matrix.posSemidef_sum _ (fun i _ => outer_psd (x i))

private theorem gram_sub_one_psd {d : ℕ} (x : ℕ → Vec d) (t : ℕ) :
    (gram x t - 1).PosSemidef := by
  simpa [gram] using Matrix.posSemidef_sum (Finset.range t) (fun i _ => outer_psd (x i))

private theorem inverse_rank_update {d : ℕ} (S : Mat d) (hS : S.PosDef) (v : Vec d) :
    let u := S⁻¹ *ᵥ v
    (S + outer v)⁻¹ = S⁻¹ - (1 + v ⬝ᵥ u)⁻¹ • outer u := by
  let u := S⁻¹ *ᵥ v
  let _ : Invertible S := hS.isUnit.invertible
  let _ : Invertible (S + outer v) := (hS.add_posSemidef (outer_psd v)).isUnit.invertible
  have hnon : 0 ≤ v ⬝ᵥ u := by simpa [u] using hS.inv.posSemidef.dotProduct_mulVec_nonneg v
  have hden : (1 + v ⬝ᵥ u) ≠ 0 := by linarith
  have hu : S *ᵥ u = v := by
    rw [show u = S⁻¹ *ᵥ v by rfl, mulVec_mulVec, mul_inv_of_invertible, one_mulVec]
  have huv : v ᵥ* S⁻¹ = u := by
    have hs : (S⁻¹)ᵀ = S⁻¹ := by simpa using hS.inv.isHermitian.eq
    rw [← hs, vecMul_transpose]
  change (S + outer v)⁻¹ = S⁻¹ - (1 + v ⬝ᵥ u)⁻¹ • outer u
  rw [← mul_one (S + outer v)⁻¹]
  apply (inv_mul_eq_iff_eq_mul_of_invertible _ _ _).2
  symm
  have houter : outer v * outer u = (v ⬝ᵥ u) • vecMulVec v u := by
    rw [outer, outer, vecMulVec_mul_vecMulVec, vecMulVec_smul]
  have hp : (S + outer v) * outer u = (1 + v ⬝ᵥ u) • vecMulVec v u := by
    rw [add_mul, houter, outer, mul_vecMulVec, hu, add_smul, one_smul]
  have hInv : (S + outer v) * S⁻¹ = 1 + vecMulVec v u := by
    rw [add_mul, mul_inv_of_invertible, outer, vecMulVec_mul, huv]
  rw [mul_sub, hInv, mul_smul_comm, hp, smul_smul, inv_mul_cancel₀ hden, one_smul,
    add_sub_cancel_right]

private theorem trace_step {d : ℕ} (x : ℕ → Vec d) (hx : ∀ i, length (x i) = 1)
    (t : ℕ) :
    length ((gram x t)⁻¹ *ᵥ x t)^2 ≤
      2 * ((gram x t)⁻¹.trace - (gram x (t+1))⁻¹.trace) := by
  let S := gram x t
  let v := x t
  let u := S⁻¹ *ᵥ v
  let q := v ⬝ᵥ u
  have hS : S.PosDef := gram_posDef x t
  let _ : Invertible S := hS.isUnit.invertible
  have hq : 0 ≤ q := by simpa [q, u] using hS.inv.posSemidef.dotProduct_mulVec_nonneg v
  have hu : S *ᵥ u = v := by
    rw [show u = S⁻¹ *ᵥ v by rfl, mulVec_mulVec, mul_inv_of_invertible, one_mulVec]
  have hle : u ⬝ᵥ u ≤ q := by
    have h := (gram_sub_one_psd x t).dotProduct_mulVec_nonneg u
    change 0 ≤ star u ⬝ᵥ ((S - 1) *ᵥ u) at h
    simpa [sub_mulVec, hu, dotProduct_sub, dotProduct_comm u v, q, sub_nonneg] using h
  have hunit : v ⬝ᵥ v = 1 := by
    have h := length_sq (x t)
    rw [hx, one_pow] at h
    exact h.symm
  have hb : q ≤ 1 := by
    have h := dot_cauchy v u
    rw [hunit, one_mul] at h
    change q ^ 2 ≤ u ⬝ᵥ u at h
    by_contra! hc
    nlinarith [mul_pos (show 0 < q by linarith) (sub_pos.mpr hc)]
  have hd : 0 < 1 + q := by linarith
  change length u ^ 2 ≤ 2 * (S⁻¹.trace - (gram x (t+1))⁻¹.trace)
  rw [gram_succ, inverse_rank_update S hS v, trace_sub, trace_smul]
  change length u ^ 2 ≤ 2 * (S⁻¹.trace - (S⁻¹.trace - ((1 + q)⁻¹ * (outer u).trace)))
  rw [show (outer u).trace = u ⬝ᵥ u by simp [outer, trace_vecMulVec], length_sq]
  have h := (le_div_iff₀ hd).2 (show (u ⬝ᵥ u) * (1 + q) ≤ 2 * (u ⬝ᵥ u) by
    nlinarith [mul_nonneg (dot_nonneg u) (sub_nonneg.mpr hb)])
  rw [div_eq_mul_inv, mul_comm (2 * (u ⬝ᵥ u))] at h
  nlinarith

private theorem upper {d : ℕ} (x : ℕ → Vec d) (hx : ∀ i, length (x i) = 1)
    (T : ℕ) : (cost x T)^2 ≤ 2*d*T := by
  let s : ℕ → ℝ := fun t => length ((gram x t)⁻¹ *ᵥ x t)
  have hsum (T : ℕ) : (∑ t ∈ range T, s t ^ 2) ≤ 2 * (d - (gram x T)⁻¹.trace) := by
    induction T with
    | zero => simp [gram]
    | succ T ih =>
      rw [Finset.sum_range_succ]
      have h := trace_step x hx T
      change s T ^ 2 ≤ _ at h
      nlinarith
  have htd : 0 ≤ (gram x T)⁻¹.trace := (gram_posDef x T).inv.posSemidef.trace_nonneg
  have hs : (∑ t ∈ range T, s t ^ 2) ≤ 2*d := (hsum T).trans (by linarith)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (range T) (fun _ => (1:ℝ)) s
  simp at hc
  change (∑ t ∈ range T, s t)^2 ≤ 2*d*T
  exact hc.trans (by nlinarith [mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg T)])

private theorem alternating_gram (a b : ℝ) (k : ℕ) :
    gram (fun t => (![a, if Even t then b else -b] : Vec 2)) (2*k) =
      diagonal ![1 + (2 * (k : ℝ)) * a^2, 1 + (2 * (k : ℝ)) * b^2] := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero, gram, range_zero, sum_empty]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ k ih =>
    have h₀ : Even (2 * k) := even_two_mul k
    have h₁ : ¬ Even (2 * k + 1) := by simp
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, gram_succ, gram_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [outer, h₀, h₁, pow_two] <;> ring

private theorem diagonal_inverse {d : ℕ} (v : Vec d) (hv : ∀ i, v i ≠ 0) :
    (diagonal v)⁻¹ = diagonal (fun i => (v i)⁻¹) := by
  have hvU : IsUnit v := Pi.isUnit_iff.mpr (fun i => isUnit_iff_ne_zero.mpr (hv i))
  let _ : Invertible (diagonal v) := (isUnit_diagonal.mpr hvU).invertible
  rw [← mul_one (diagonal v)⁻¹]
  apply (inv_mul_eq_iff_eq_mul_of_invertible _ _ _).2
  rw [diagonal_mul_diagonal]
  have h : (fun i => v i * (v i)⁻¹) = (1 : Vec d) := by
    funext i
    exact mul_inv_cancel₀ (hv i)
  rw [h]
  exact (diagonal_one : diagonal (fun _ : Fin d => (1 : ℝ)) = 1).symm

private theorem coordinate_le_length (v : Vec 2) : v 1 ≤ length v := by
  apply Real.le_sqrt_of_sq_le
  simp only [dotProduct, Fin.sum_univ_two, pow_two]
  nlinarith [sq_nonneg (v 0)]

private theorem lower (T : ℕ) (hT : 2 ≤ T) :
    ∃ x : ℕ → Vec 2, (∀ t, length (x t)=1) ∧ Real.sqrt T ≤ 9*cost x T := by
  let τ : ℝ := T
  have hτ : 2 ≤ τ := by change (2 : ℝ) ≤ (T:ℝ); exact_mod_cast hT
  have hs : 0 < Real.sqrt τ := Real.sqrt_pos.2 (by linarith)
  let b := (Real.sqrt τ)⁻¹
  let a := Real.sqrt (1 - τ⁻¹)
  have hb : 0 < b := inv_pos.mpr hs
  have hb2 : b ^ 2 = τ⁻¹ := by rw [inv_pow, Real.sq_sqrt (by linarith)]
  have ha2 : a ^ 2 = 1 - τ⁻¹ := by
    apply Real.sq_sqrt
    have : τ⁻¹ ≤ (1 : ℝ) := (inv_le_one₀ (by linarith : 0 < τ)).mpr (by linarith)
    linarith
  let x : ℕ → Vec 2 := fun t => ![a, if Even t then b else -b]
  have hunit (t : ℕ) : length (x t) = 1 := by
    have h := length_sq (x t)
    rw [show x t ⬝ᵥ x t = 1 by
      simp only [x, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      split_ifs <;> nlinarith] at h
    nlinarith [length_nonneg (x t)]
  refine ⟨x, hunit, ?_⟩
  let s : ℕ → ℝ := fun t => length ((gram x t)⁻¹ *ᵥ x t)
  have hpoint (k : ℕ) (hk : k < T/2) : b / 2 ≤ s (2*k) := by
    let u := (gram x (2*k))⁻¹ *ᵥ x (2*k)
    have hu : u 1 = b / (1 + (2 * (k:ℝ)) * b^2) := by
      change ((gram x (2*k))⁻¹ *ᵥ x (2*k)) 1 = _
      rw [alternating_gram, diagonal_inverse, mulVec_diagonal]
      · simp [x, div_eq_mul_inv, mul_comm]
      · intro i
        fin_cases i
        · exact (show 1 + (2 * (k:ℝ)) * a^2 ≠ 0 by positivity)
        · exact (show 1 + (2 * (k:ℝ)) * b^2 ≠ 0 by positivity)
    have hk' : (2 * (k:ℝ)) ≤ τ := by
      change 2 * (k:ℝ) ≤ (T:ℝ)
      exact_mod_cast (show 2*k ≤ T by omega)
    have hd : 0 < 1 + (2 * (k:ℝ)) * b^2 := by positivity
    have hbound : 1 + (2 * (k:ℝ)) * b^2 ≤ 2 := by
      rw [hb2, ← div_eq_mul_inv]
      have hh := (div_le_one (show 0 < τ by linarith)).mpr hk'
      linarith
    change b/2 ≤ length u
    refine le_trans ?_ (coordinate_le_length u)
    rw [hu]
    exact (div_le_div_iff₀ (by norm_num) hd).mpr (mul_le_mul_of_nonneg_left hbound hb.le)
  have hsums : (∑ k ∈ range (T/2), s (2*k)) ≤ cost x T := by
    rw [← Finset.sum_image (fun i _ j _ h => by omega)]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hk; omega)
    · intro t _ _
      exact length_nonneg _
  have hcost : ((T/2:ℕ):ℝ) * (b/2) ≤ cost x T := by
    have h := Finset.sum_le_sum (s := range (T/2))
      (fun k hk => hpoint k (Finset.mem_range.mp hk))
    exact (by simpa using h : ((T/2:ℕ):ℝ) * (b/2) ≤ _).trans hsums
  have hh : τ ≤ 3 * ((T/2:ℕ):ℝ) := by
    change (T:ℝ) ≤ 3 * ((T/2:ℕ):ℝ)
    exact_mod_cast (show T ≤ 3*(T/2) by omega)
  have hbτ : τ * b = Real.sqrt τ := by
    dsimp [b]
    have hsq := Real.sq_sqrt (show 0 ≤ τ by linarith)
    calc
      τ * (Real.sqrt τ)⁻¹ = (Real.sqrt τ)^2 * (Real.sqrt τ)⁻¹ :=
        congrArg (fun v : ℝ => v * (Real.sqrt τ)⁻¹) hsq.symm
      _ = Real.sqrt τ := by rw [pow_two, mul_assoc, mul_inv_cancel₀ hs.ne', mul_one]
  change Real.sqrt τ ≤ 9 * cost x T
  nlinarith [mul_le_mul_of_nonneg_right hh hb.le]

private theorem growth (C : ℝ) (T₀ : ℕ) :
    ∃ T : ℕ, T₀ ≤ T ∧ ∃ x : ℕ → Vec 2,
      (∀ t, length (x t)=1) ∧ C*Real.log ((T:ℝ)+1) < cost x T := by
  let δ : ℝ := (18 * (|C| + 1))⁻¹
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hlog := (isLittleO_log_rpow_atTop (r := (1/2 : ℝ)) (by norm_num)).def hδ
  obtain ⟨M, hM⟩ := eventually_atTop.1 hlog
  obtain ⟨N, hN⟩ := exists_nat_ge M
  let T := max (max T₀ 2) N
  have hT : 2 ≤ T := le_trans (le_max_right _ _) (le_max_left _ _)
  have hTN : N ≤ T := le_max_right _ _
  have hMT : M ≤ (T:ℝ)+1 := by exact hN.trans (by exact_mod_cast (show N ≤ T+1 by omega))
  have hreal : 2 ≤ (T:ℝ) := by exact_mod_cast hT
  have hpos : 0 < Real.sqrt (T:ℝ) := Real.sqrt_pos.2 (by linarith)
  have hL : 0 ≤ Real.log ((T:ℝ)+1) := Real.log_nonneg (by linarith)
  have hL' := hM _ hMT
  rw [← Real.sqrt_eq_rpow, Real.norm_eq_abs, abs_of_nonneg hL,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at hL'
  have hsq : Real.sqrt ((T:ℝ)+1) ≤ 2*Real.sqrt (T:ℝ) := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith [Real.sq_sqrt (show 0 ≤ (T:ℝ) by linarith)]⟩
  obtain ⟨x, hx, hcost⟩ := lower T hT
  refine ⟨T, (le_max_left _ _).trans (le_max_left _ _), x, hx, ?_⟩
  have hδid : δ * (18 * (|C|+1)) = 1 := inv_mul_cancel₀ (by positivity)
  have hcoef : |C| * δ * 2 < 1/9 := by nlinarith
  calc
    _ ≤ |C| * Real.log ((T:ℝ)+1) := mul_le_mul_of_nonneg_right (le_abs_self C) hL
    _ ≤ |C| * (δ * Real.sqrt ((T:ℝ)+1)) := mul_le_mul_of_nonneg_left hL' (abs_nonneg _)
    _ ≤ (|C| * δ * 2) * Real.sqrt (T:ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hsq (mul_nonneg (abs_nonneg C) hδ.le)]
    _ < (1/9) * Real.sqrt (T:ℝ) := mul_lt_mul_of_pos_right hcoef hpos
    _ ≤ cost x T := by linarith

theorem result : type_of% @main := ⟨upper, lower, growth⟩

end InverseVectorCost

theorem OMA.solution : type_of% @OMA.S_mo_354351.main := InverseVectorCost.result