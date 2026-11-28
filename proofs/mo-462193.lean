import OMAStatements.S_mo_462193
import Mathlib

namespace OMA.Helpers_mo_462193

open Matrix Finset

def toM (n : ℕ) (L : List (List ℤ)) : Matrix (Fin n) (Fin n) ℤ := fun i j => (L.getD i []).getD j 0

def ofF (n : ℕ) (f : Fin n → Fin n → ℤ) : List (List ℤ) := List.ofFn fun i => List.ofFn fun j => f i j

lemma toM_ofF (n : ℕ) (f : Fin n → Fin n → ℤ) (i j : Fin n) : toM n (ofF n f) i j = f i j := by
  simp [toM, ofF, List.getD_eq_getElem?_getD]

def mulL (n : ℕ) (A B : List (List ℤ)) : List (List ℤ) :=
  ofF n fun i j => ∑ l : Fin n, toM n A i l * toM n B l j

lemma toM_mulL (n : ℕ) (A B : List (List ℤ)) : toM n (mulL n A B) = toM n A * toM n B := by
  ext i j; rw [mulL, toM_ofF, Matrix.mul_apply]

def Al : List (List ℤ) := ofF 24 fun i j => if j = i ∨ j = i + 1 then 1 else 0

abbrev A : Matrix (Fin 24) (Fin 24) ℤ := toM 24 Al

lemma A_apply (l j : Fin 24) : A l j = if j = l ∨ j = l + 1 then 1 else 0 := by
  rw [A, Al, toM_ofF]

lemma mulA_eq (M : Matrix (Fin 24) (Fin 24) ℤ) (i j : Fin 24) :
    (M * A) i j = M i j + M i (j - 1) := by
  rw [Matrix.mul_apply]
  simp only [A_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have : Finset.univ.filter (fun l : Fin 24 => j = l ∨ j = l + 1) = {j, j - 1} := by
    ext l; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · left; exact h.symm
      · right; rw [h]; simp
    · rintro (h | h)
      · left; exact h.symm
      · right; rw [h]; simp
  rw [this, Finset.sum_pair (by decide +revert)]

def mulA (M : List (List ℤ)) : List (List ℤ) := ofF 24 fun i j => toM 24 M i j + toM 24 M i (j - 1)

lemma toM_mulA (M : List (List ℤ)) : toM 24 (mulA M) = toM 24 M * A := by
  ext i j; rw [mulA, toM_ofF, mulA_eq]

def tA (M : List (List ℤ)) : ℤ := ∑ a : Fin 24, (toM 24 M a a + toM 24 M (a - 1) a)

lemma tA_eq (M : List (List ℤ)) : tA M = (Aᵀ * toM 24 M).trace := by
  rw [tA, Matrix.trace, ← Matrix.transpose_transpose (Aᵀ * toM 24 M), Matrix.diag_transpose,
    Matrix.transpose_mul, Matrix.transpose_transpose]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.diag_apply, mulA_eq, Matrix.transpose_apply, Matrix.transpose_apply]

def loop : ℕ → ℕ → List (List ℤ) → ℤ
  | 0, _, _ => 0
  | f + 1, i, M => tA M * 2 ^ (38 - i) + loop f (i + 1) (mulA M)

lemma loop_spec : ∀ f i M, loop f i M =
    ∑ t ∈ range f, (Aᵀ * (toM 24 M * A ^ t)).trace * 2 ^ (38 - (i + t)) := by
  intro f
  induction f with
  | zero => intro i M; simp [loop]
  | succ f ih =>
    intro i M
    rw [loop, ih, sum_range_succ', tA_eq, pow_zero, mul_one, add_zero, add_comm]
    congr 1
    refine sum_congr rfl fun t _ => ?_
    rw [toM_mulA, show i + 1 + t = i + (t + 1) by omega, pow_succ', mul_assoc]

lemma key : loop 39 0 Al < 39 * 2 ^ 40 := by decide +kernel

lemma A_nonneg (i j : Fin 24) : (0 : ℤ) ≤ toM 24 Al i j := by
  rw [Al, toM_ofF]; split_ifs <;> norm_num
lemma A_row : ∀ i : Fin 24, ∑ j, toM 24 Al i j = 2 := by decide +kernel
lemma A_col : ∀ j : Fin 24, ∑ i, toM 24 Al i j = 2 := by decide +kernel

noncomputable def P : Matrix (Fin 24) (Fin 24) ℝ := (1 / 2 : ℝ) • A.map (Int.cast : ℤ → ℝ)

lemma P_apply (i j : Fin 24) : P i j = 1 / 2 * (A i j : ℝ) := rfl

lemma P_pow (k : ℕ) : P ^ k = (1 / 2 : ℝ) ^ k • (A ^ k).map (Int.cast : ℤ → ℝ) := by
  rw [P, smul_pow]
  congr 1
  exact (Matrix.map_pow A (Int.castRingHom ℝ) k).symm

lemma tr_term (i : ℕ) : (Pᵀ * P ^ (i + 1)).trace =
    (1 / 2 : ℝ) ^ (i + 2) * (((Aᵀ * A ^ (i + 1)).trace : ℤ) : ℝ) := by
  rw [P_pow, P, Matrix.transpose_smul, smul_mul_smul_comm, Matrix.trace_smul, smul_eq_mul, ← pow_succ']
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
  push_cast; rfl

lemma key_real : (∑ i ∈ Finset.range 39, (Pᵀ * P ^ (i + 1)).trace) < 39 := by
  have hk := key
  rw [loop_spec] at hk
  simp only [zero_add] at hk
  have hk' : ((∑ t ∈ Finset.range 39, (Aᵀ * (toM 24 Al * A ^ t)).trace * 2 ^ (38 - t) : ℤ) : ℝ) <
      ((39 * 2 ^ 40 : ℤ) : ℝ) := by exact_mod_cast hk
  push_cast at hk'
  simp only [tr_term]
  have e : ∀ t ∈ Finset.range 39, (((Aᵀ * (toM 24 Al * A ^ t)).trace : ℤ) : ℝ) * 2 ^ (38 - t) =
      2 ^ 40 * ((1 / 2 : ℝ) ^ (t + 2) * (((Aᵀ * A ^ (t + 1)).trace : ℤ) : ℝ)) := by
    intro t ht
    rw [Finset.mem_range] at ht
    rw [← pow_succ']
    have : (2 : ℝ) ^ 40 * (1 / 2) ^ (t + 2) = 2 ^ (38 - t) := by
      rw [show (40 : ℕ) = (38 - t) + (t + 2) by omega, pow_add, mul_assoc, ← mul_pow]; norm_num
    rw [← this]; ring
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum] at hk'
  nlinarith

end OMA.Helpers_mo_462193

open OMA.Helpers_mo_462193 Matrix in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_462193.main) := by
  intro h
  have hrev : OMA.S_mo_462193.reversal P (fun _ => (1 / 24 : ℝ)) = Pᵀ := by
    ext i j; simp [OMA.S_mo_462193.reversal]
  have hrow : ∀ i, ∑ j, P i j = 1 := by
    intro i
    simp only [P_apply, ← Finset.mul_sum]
    rw [← Int.cast_sum, A_row]; norm_num
  have hcol : ∀ j, ∑ i, P i j = 1 := by
    intro j
    simp only [P_apply, ← Finset.mul_sum]
    rw [← Int.cast_sum, A_col]; norm_num
  have := h (Fin 24) P (fun _ => 1 / 24)
    (fun i j => by rw [P_apply]; have := A_nonneg i j; positivity) hrow
    (fun _ => by norm_num) (by simp) (fun j => by rw [← Finset.mul_sum, hcol]; norm_num) 39 (by norm_num)
  rw [hrev] at this
  have := key_real
  push_cast at *
  rw [le_div_iff₀ (by norm_num)] at *
  linarith
