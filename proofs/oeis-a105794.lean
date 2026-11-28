import OMAStatements.S_oeis_a105794
import Mathlib

open OMA.S_oeis_a105794

namespace P105794

open Polynomial Finset

noncomputable abbrev D (k : ℕ) : ℚ[X] := descPochhammer ℚ k

theorem natDeg_Q (n : ℕ) : ((D n).comp (X + 1)).natDegree = n := by
  rw [natDegree_comp, descPochhammer_natDegree, show (X + 1 : ℚ[X]) = X + C 1 by simp,
    natDegree_X_add_C, mul_one]

theorem a_zero_of_lt (n j : ℕ) (h : n < j) : A105793 n j = 0 := by
  unfold A105793
  exact coeff_eq_zero_of_natDegree_lt (by rw [natDeg_Q]; exact h)

theorem a_diag (n : ℕ) : A105793 n n = 1 := by
  unfold A105793
  have hm : ((D n).comp (X + C 1)).Monic := (monic_descPochhammer ℚ n).comp_X_add_C 1
  have := hm.coeff_natDegree
  rw [map_one, natDeg_Q] at this
  simpa using this

theorem expand_D (k : ℕ) : D k = ∑ j ∈ range (k + 1), C (A105793 k j) * (X - 1) ^ j := by
  have hQ := as_sum_range' ((D k).comp (X + 1)) (k + 1) (by rw [natDeg_Q]; omega)
  have h1 : D k = ((D k).comp (X + 1)).comp (X - 1) := by
    rw [comp_assoc]; simp
  rw [h1]
  conv_lhs => rw [hQ]
  rw [Polynomial.sum_comp]
  refine sum_congr rfl fun j _ => ?_
  rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp]
  rfl

theorem flip (T : ℕ → ℕ → ℚ) (hT : IsInverse T) (n j : ℕ) (hj : j ≤ n) :
    ∑ k ∈ range (n + 1), T n k * A105793 k j = if n = j then 1 else 0 := by
  let Am : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ := Matrix.of fun i l => A105793 i l
  let Tm : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ := Matrix.of fun i l => T i l
  have hAT : Am * Tm = 1 := by
    ext i l
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Am, Tm, Matrix.of_apply]
    rw [Fin.sum_univ_eq_sum_range (fun x => A105793 i x * T x l)]
    have hi := i.2
    rw [← Finset.sum_range_add_sum_Ico _ (show (i : ℕ) + 1 ≤ n + 1 by omega), hT i l]
    rw [Finset.sum_eq_zero (fun x hx => by
      rw [mem_Ico] at hx; rw [a_zero_of_lt _ _ (by omega), zero_mul]), add_zero]
    simp only [Fin.ext_iff]
  have hTA : Tm * Am = 1 := mul_eq_one_comm.mp hAT
  have := congrFun (congrFun hTA (Fin.last n)) ⟨j, by omega⟩
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  simp only [Am, Tm, Matrix.of_apply, Fin.val_last] at this
  rw [Fin.sum_univ_eq_sum_range (fun x => T n x * A105793 x j)] at this
  rw [this]
  simp only [Fin.ext_iff, Fin.val_last]

theorem expand_E (T : ℕ → ℕ → ℚ) (hT : IsInverse T) (n : ℕ) :
    (X - 1 : ℚ[X]) ^ n = ∑ k ∈ range (n + 1), C (T n k) * D k := by
  have step : ∀ k ∈ range (n + 1), C (T n k) * D k =
      ∑ j ∈ range (n + 1), C (T n k * A105793 k j) * (X - 1) ^ j := by
    intro k hk
    rw [mem_range] at hk
    rw [expand_D, Finset.mul_sum, ← Finset.sum_range_add_sum_Ico _ (show k + 1 ≤ n + 1 by omega)]
    rw [Finset.sum_eq_zero (s := Ico (k + 1) (n + 1)) (fun x hx => by
      rw [mem_Ico] at hx; rw [a_zero_of_lt _ _ (by omega), mul_zero, map_zero, zero_mul]), add_zero]
    refine sum_congr rfl fun j _ => ?_
    rw [map_mul, mul_assoc]
  rw [Finset.sum_congr rfl step, Finset.sum_comm]
  rw [Finset.sum_congr rfl fun j hj => by rw [← Finset.sum_mul, ← map_sum,
    flip T hT n j (by rw [mem_range] at hj; omega)]]
  rw [Finset.sum_eq_single n (fun b _ hb => by rw [if_neg (Ne.symm hb), map_zero, zero_mul])
    (by simp)]
  simp

theorem eval_D_neg (k m : ℕ) :
    (D k).eval (-((m : ℚ) + 1)) * m.factorial = (-1) ^ k * (k + m).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [descPochhammer_succ_eval, mul_right_comm, ih, show k + 1 + m = (k + m) + 1 by ring,
      Nat.factorial_succ]
    push_cast
    ring

theorem conj1 (T : ℕ → ℕ → ℚ) (hT : IsInverse T) (n m : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℚ) ^ (n - k) * T n k * ((k + m).factorial / m.factorial) =
      ((m : ℚ) + 2) ^ n := by
  have e := congrArg (eval (-((m : ℚ) + 1))) (expand_E T hT n)
  rw [eval_pow, eval_sub, eval_X, eval_one, eval_finsetSum] at e
  simp only [eval_mul, eval_C] at e
  have hm : (m.factorial : ℚ) ≠ 0 := by positivity
  have key : ∀ k ∈ range (n + 1), (-1 : ℚ) ^ (n - k) * T n k * ((k + m).factorial / m.factorial) =
      (-1) ^ n * (T n k * (D k).eval (-((m : ℚ) + 1))) := by
    intro k hk
    rw [mem_range] at hk
    have h1 := eval_D_neg k m
    have h2 : (D k).eval (-((m : ℚ) + 1)) = (-1) ^ k * (k + m).factorial / m.factorial := by
      field_simp; linear_combination h1
    rw [h2]
    have h3 : (-1 : ℚ) ^ n = (-1) ^ (n - k) * (-1) ^ k := by
      rw [← pow_add, Nat.sub_add_cancel (by omega)]
    rw [h3]
    have h4 : ((-1 : ℚ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; simp
    linear_combination (-(-1 : ℚ) ^ (n - k) * T n k * ((k + m).factorial / m.factorial)) * h4
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, ← e]
  rw [show -((m : ℚ) + 1) - 1 = (-1) * ((m : ℚ) + 2) by ring, mul_pow, ← mul_assoc, ← mul_pow]
  simp

/-- The Bernoulli functional `X^n ↦ B(n)`. -/
noncomputable def Λ : ℚ[X] →ₗ[ℚ] ℚ := lsum fun n => LinearMap.mulRight ℚ (_root_.bernoulli n)

theorem Λ_monomial (n : ℕ) (c : ℚ) : Λ (monomial n c) = c * _root_.bernoulli n := by
  simp [Λ, lsum_apply, sum_monomial_index]

theorem Λ_C_mul_X_pow (n : ℕ) (c : ℚ) : Λ (C c * X ^ n) = c * _root_.bernoulli n := by
  rw [C_mul_X_pow_eq_monomial, Λ_monomial]

theorem Λ_X_add_one_pow (n : ℕ) :
    Λ ((X + 1) ^ n) = ∑ j ∈ range (n + 1), (n.choose j : ℚ) * _root_.bernoulli j := by
  rw [add_pow, map_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [one_pow, mul_one, ← Polynomial.C_eq_natCast, mul_comm, Λ_C_mul_X_pow]

theorem F1 (p : ℚ[X]) : Λ (p.comp (X + 1) - p) = (derivative p).eval 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [add_comp, map_add, eval_add, ← hp, ← hq, ← map_add]; congr 1; ring
  | monomial n c =>
    have hm : (monomial n c : ℚ[X]) = C c * X ^ n := C_mul_X_pow_eq_monomial.symm
    have hx : Λ (X ^ n) = _root_.bernoulli n := by
      rw [← one_mul (X ^ n), ← map_one C, Λ_C_mul_X_pow, one_mul]
    rw [hm, mul_comp, C_comp, X_pow_comp, ← mul_sub, ← smul_eq_C_mul, map_smul, map_sub,
      Λ_X_add_one_pow, Finset.sum_range_succ, _root_.sum_bernoulli, Nat.choose_self, hx,
      derivative_C_mul_X_pow]
    simp only [eval_mul, eval_C, eval_pow, eval_X, smul_eq_mul, Nat.cast_one, one_mul]
    rcases n with _ | _ | n
    · simp
    · simp
    · simp

theorem D_diff (m : ℕ) : (D (m + 1)).comp (X + 1) - D (m + 1) = C ((m : ℚ) + 1) * D m := by
  have h := descPochhammer_succ_comp_X_sub_one (R := ℚ) m
  rw [smul_eq_mul] at h
  have h' := congrArg (fun p => p.comp (X + 1)) h
  simp only [sub_comp, mul_comp, comp_assoc, add_comp, natCast_comp, one_comp, X_comp,
    add_sub_cancel_right, comp_X] at h'
  rw [show C ((m : ℚ) + 1) = ((m : ℚ[X]) + 1) by simp]
  linear_combination -h'

theorem deriv_D_zero (m : ℕ) : (derivative (D (m + 1))).eval 0 = (-1) ^ m * m.factorial := by
  show (derivative (descPochhammer ℚ (m + 1))).eval 0 = _
  rw [descPochhammer_succ_left, derivative_mul, derivative_X, one_mul, eval_add, eval_mul, eval_X,
    zero_mul, add_zero, eval_comp, eval_sub, eval_X, eval_one, zero_sub]
  have := eval_D_neg m 0
  simpa using this

theorem Λ_D (m : ℕ) : Λ (D m) = (-1) ^ m * m.factorial / (m + 1) := by
  have h := F1 (D (m + 1))
  rw [D_diff, deriv_D_zero, ← smul_eq_C_mul, map_smul, smul_eq_mul] at h
  have hm : ((m : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  linear_combination h

theorem Λ_E (n : ℕ) : Λ ((X - 1) ^ n) = _root_.bernoulli n - n * (-1) ^ (n - 1) := by
  have hX : (X - 1 : ℚ[X]) = X - C 1 := by simp
  have h := F1 ((X - C 1) ^ n)
  rw [pow_comp, sub_comp, X_comp, C_comp, show (X + 1 - C 1 : ℚ[X]) = X by simp, map_sub,
    derivative_X_sub_C_pow] at h
  have : Λ (X ^ n) = _root_.bernoulli n := by
    rw [← one_mul (X ^ n), ← map_one C, Λ_C_mul_X_pow, one_mul]
  rw [this] at h
  simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_X, zero_sub] at h
  rw [hX]
  linear_combination -h

/-- `M(p) = p(0) - p'(0) - Λ(p)` -/
noncomputable def M (p : ℚ[X]) : ℚ := p.eval 0 - (derivative p).eval 0 - Λ p

theorem M_sum (s : Finset ℕ) (c : ℕ → ℚ) (f : ℕ → ℚ[X]) :
    M (∑ k ∈ s, C (c k) * f k) = ∑ k ∈ s, c k * M (f k) := by
  simp only [M, eval_finsetSum, map_sum, ← smul_eq_C_mul, map_smul, eval_smul, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib]

theorem M_E (n : ℕ) : M ((X - 1) ^ n) = (-1) ^ n - _root_.bernoulli n := by
  unfold M
  rw [Λ_E, show (X - 1 : ℚ[X]) = X - C 1 by simp, derivative_X_sub_C_pow]
  simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_X, map_one, eval_one, zero_sub]
  ring

theorem M_D (k : ℕ) :
    M (D k) = if k = 0 then 0 else (-1 : ℚ) ^ k * (((k - 1).factorial : ℚ) / ((k : ℚ) + 1)) := by
  rcases k with _ | j
  · have h1 : Λ 1 = 1 := by rw [← monomial_zero_one, Λ_monomial]; simp
    simp [M, h1]
  · rw [if_neg (by omega)]
    unfold M
    have h0 : (D (j + 1)).eval 0 = 0 := descPochhammer_ne_zero_eval_zero ℚ (Nat.succ_ne_zero j)
    rw [h0, deriv_D_zero, Λ_D, Nat.add_sub_cancel]
    have h1 : ((j + 1 : ℕ) : ℚ) + 1 ≠ 0 := by positivity
    have h2 : (((j + 1).factorial : ℕ) : ℚ) = (j + 1) * j.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    rw [h2]
    push_cast
    field_simp
    ring

theorem Icc_sum (n : ℕ) (f : ℕ → ℚ) : ∑ k ∈ Icc 1 n, f k = ∑ j ∈ range n, f (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem conj2 (T : ℕ → ℕ → ℚ) (hT : IsInverse T) (n : ℕ) :
    (-1 : ℚ) ^ n - _root_.bernoulli n =
      ∑ k ∈ Icc 1 n, (-1 : ℚ) ^ k * T n k * ((k - 1).factorial / (k + 1)) := by
  rw [← M_E, expand_E T hT, M_sum, Finset.sum_range_succ', Icc_sum]
  simp only [M_D, if_neg (Nat.succ_ne_zero _), if_pos, mul_zero, add_zero]
  refine sum_congr rfl fun j _ => ?_
  ring

noncomputable def Tr : ℕ → ℕ → ℚ
  | n, k => (if n = k then 1 else 0) - ∑ j : Fin n, A105793 n j * Tr j k
decreasing_by exact j.2

theorem exists_inv : ∃ T, IsInverse T := by
  refine ⟨Tr, fun n k => ?_⟩
  rw [Finset.sum_range_succ, a_diag, one_mul]
  conv_lhs => rw [Tr]
  rw [Fin.sum_univ_eq_sum_range (fun j => A105793 n j * Tr j k)]
  ring

end P105794

theorem OMA.solution : type_of% @OMA.S_oeis_a105794.main :=
  ⟨P105794.exists_inv, fun T hT => ⟨P105794.conj1 T hT, P105794.conj2 T hT⟩⟩
