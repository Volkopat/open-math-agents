import OMAStatements.S_oeis_a355326

open scoped BigOperators Matrix Polynomial
open Polynomial Matrix

namespace OMA.S_oeis_a355326_proof

open OMA.S_oeis_a355326

private def matU (m n : ℕ) : Matrix (Fin n) (Fin (m + 1)) ℚ :=
  fun i r => (m.choose r.val : ℚ) * (i.val : ℚ) ^ r.val

private def matV (m n : ℕ) : Matrix (Fin (m + 1)) (Fin n) ℚ :=
  fun r j => (-(j.val : ℚ)) ^ (m - r.val)

private lemma powerToeplitz_eq_one_add (m n : ℕ) :
    powerToeplitz m n = 1 + matU m n * matV m n := by
  ext i j
  simp only [powerToeplitz, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, matU, matV]
  have hbin : ((i.val : ℚ) + (-(j.val : ℚ))) ^ m =
      ∑ r : Fin (m + 1), (m.choose r.val : ℚ) * (i.val : ℚ) ^ r.val * (-(j.val : ℚ)) ^ (m - r.val) := by
    rw [add_pow, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  have hsub : (i.val : ℚ) - j.val = (i.val : ℚ) + -(j.val : ℚ) := sub_eq_add_neg _ _
  rw [hsub, hbin]
  ring

private lemma one_add_matV_mul_matU (m n : ℕ) (r s : Fin (m + 1)) :
    ((1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ) + matV m n * matU m n) r s =
      (if r = s then 1 else 0) +
        (-1 : ℚ) ^ (m - r.val) * (m.choose s.val : ℚ) *
          ∑ j : Fin n, (j.val : ℚ) ^ (m - r.val + s.val) := by
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, matV, matU]
  have hterm : ∀ j : Fin n,
      (-(j.val : ℚ)) ^ (m - r.val) * ((m.choose s.val : ℚ) * (j.val : ℚ) ^ s.val) =
        (-1 : ℚ) ^ (m - r.val) * (m.choose s.val : ℚ) * (j.val : ℚ) ^ (m - r.val + s.val) := by
    intro j
    rw [neg_eq_neg_one_mul, mul_pow, pow_add]
    ring
  simp_rw [hterm, ← Finset.mul_sum]

private noncomputable def faulh : ℕ → ℚ[X]
  | k => C ((k + 1 : ℚ)⁻¹) *
      (X ^ (k + 1) - ∑ t : Fin k, C (((k + 1).choose t.val : ℚ)) * faulh t.val)

private lemma faulh_mul_succ (k : ℕ) :
    C (k + 1 : ℚ) * faulh k =
      X ^ (k + 1) - ∑ t : Fin k, C (((k + 1).choose t.val : ℚ)) * faulh t.val := by
  rw [faulh, ← mul_assoc, ← C_mul]
  have hk : (k + 1 : ℚ) ≠ 0 := by positivity
  rw [mul_inv_cancel₀ hk, C_1, one_mul]

private lemma faulh_comp_sub (k : ℕ) : (faulh k).comp (X + 1) - faulh k = X ^ k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have hk0 : (C (k + 1 : ℚ)) ≠ 0 := C_ne_zero.mpr (by positivity)
    apply mul_left_cancel₀ hk0
    rw [mul_sub]
    have hcomp : C (k + 1 : ℚ) * (faulh k).comp (X + 1) = (C (k + 1 : ℚ) * faulh k).comp (X + 1) := by
      simp [Polynomial.mul_comp]
    rw [hcomp, faulh_mul_succ]
    simp only [Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.X_comp,
      Polynomial.sum_comp, Polynomial.mul_comp, Polynomial.C_comp]
    have hih : ∑ t : Fin k, C (((k + 1).choose t.val : ℚ)) * (faulh t.val).comp (X + 1) -
        ∑ t : Fin k, C (((k + 1).choose t.val : ℚ)) * faulh t.val =
        ∑ t : Fin k, C (((k + 1).choose t.val : ℚ)) * X ^ t.val := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [← mul_sub, ih t.val t.isLt]
    have hpow : (X + 1 : ℚ[X]) ^ (k + 1) - X ^ (k + 1) =
        C (k + 1 : ℚ) * X ^ k + ∑ t : Fin k, C (((k + 1).choose t.val : ℚ)) * X ^ t.val := by
      rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ]
      simp only [Nat.choose_self, Nat.sub_self, pow_zero, mul_one, Nat.cast_one,
        add_sub_cancel_right, Nat.choose_succ_self_right, Nat.add_sub_cancel_left, pow_one,
        Nat.cast_add]
      have hsub : ∑ x ∈ Finset.range k, X ^ x * (1 : ℚ[X]) ^ (k + 1 - x) *
          ((k + 1).choose x : ℚ[X]) =
          ∑ t : Fin k, C (((k + 1).choose t.val : ℚ)) * X ^ t.val := by
        rw [← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl fun t _ => ?_
        simp [one_pow, mul_comm]
      rw [hsub, add_comm]
      congr 1
      simp [mul_comm]
    calc
      (X + 1 : ℚ[X]) ^ (k + 1) -
          ∑ t : Fin k, C (((k + 1).choose t.val : ℚ)) * (faulh t.val).comp (X + 1) -
          (X ^ (k + 1) - ∑ t : Fin k, C (((k + 1).choose t.val : ℚ)) * faulh t.val)
        = ((X + 1 : ℚ[X]) ^ (k + 1) - X ^ (k + 1)) -
            (∑ t : Fin k, C (((k + 1).choose t.val : ℚ)) * (faulh t.val).comp (X + 1) -
              ∑ t : Fin k, C (((k + 1).choose t.val : ℚ)) * faulh t.val) := by ring
      _ = C (k + 1 : ℚ) * X ^ k := by rw [hpow, hih]; ring

private lemma faulh_eval_zero (k : ℕ) : (faulh k).eval 0 = 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rw [faulh]
    simp only [eval_mul, eval_C, eval_sub, eval_pow, eval_X]
    rw [zero_pow (Nat.succ_ne_zero k)]
    have hevs : (∑ t : Fin k, C (((k + 1).choose t.val : ℚ)) * faulh t.val).eval 0 =
        ∑ t : Fin k, ((k + 1).choose t.val : ℚ) * (faulh t.val).eval 0 := by
      simp [← coe_evalRingHom, map_sum]
    have hs : ∑ t : Fin k, ((k + 1).choose t.val : ℚ) * (faulh t.val).eval 0 = 0 := by
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [ih t.val t.isLt, mul_zero]
    rw [hevs, hs, sub_self, mul_zero]

private lemma faulh_eval_nat (k n : ℕ) :
    (faulh k).eval (n : ℚ) = ∑ j : Fin n, (j.val : ℚ) ^ k := by
  induction n with
  | zero => simp [faulh_eval_zero]
  | succ n ih =>
    have hstep := congrArg (Polynomial.eval (n : ℚ)) (faulh_comp_sub k)
    simp only [eval_sub, eval_comp, eval_add, eval_X, eval_one, eval_pow] at hstep
    rw [Nat.cast_succ, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    linarith

private lemma faulh_eval_neg_one (k : ℕ) : (faulh k).eval (-1) = -((-1 : ℚ) ^ k) := by
  have h := congrArg (Polynomial.eval (-1 : ℚ)) (faulh_comp_sub k)
  simp only [eval_sub, eval_comp, eval_add, eval_X, eval_one, eval_pow, neg_add_cancel,
    faulh_eval_zero] at h
  linarith

private lemma faulh_deg_lc (k : ℕ) :
    (faulh k).natDegree = k + 1 ∧ (faulh k).leadingCoeff = (k + 1 : ℚ)⁻¹ := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    let S : ℚ[X] := ∑ t : Fin k, C (((k + 1).choose t.val : ℚ)) * faulh t.val
    have hS_le : S.natDegree ≤ k := by
      refine natDegree_sum_le_of_forall_le _ _ fun t _ => ?_
      refine (natDegree_C_mul_le _ _).trans ?_
      rw [(ih t.val t.isLt).1]
      exact t.isLt
    have hS : S.natDegree < k + 1 := Nat.lt_succ_of_le hS_le
    have hX : (X ^ (k + 1) : ℚ[X]).natDegree = k + 1 := natDegree_X_pow (k + 1)
    have hSlt : S.natDegree < (X ^ (k + 1) : ℚ[X]).natDegree := hX.symm ▸ hS
    have hsub_deg : (X ^ (k + 1) - S).natDegree = k + 1 :=
      (natDegree_sub_eq_left_of_natDegree_lt hSlt).trans hX
    have hsub_lc : (X ^ (k + 1) - S).leadingCoeff = 1 := by
      rw [leadingCoeff, hsub_deg, coeff_sub, coeff_X_pow_self,
        coeff_eq_zero_of_natDegree_lt hS, sub_zero]
    have hcinv : (k + 1 : ℚ)⁻¹ ≠ 0 := by positivity
    rw [faulh]
    constructor
    · rw [natDegree_C_mul hcinv, hsub_deg]
    · rw [leadingCoeff_mul, leadingCoeff_C, hsub_lc, mul_one]

private lemma faulh_natDegree (k : ℕ) : (faulh k).natDegree = k + 1 := (faulh_deg_lc k).1
private lemma faulh_leadingCoeff (k : ℕ) : (faulh k).leadingCoeff = (k + 1 : ℚ)⁻¹ := (faulh_deg_lc k).2

private noncomputable def matM (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ[X] :=
  fun r s => (if r = s then 1 else 0) +
    C ((-1 : ℚ) ^ (m - r.val) * (m.choose s.val : ℚ)) * faulh (m - r.val + s.val)

private lemma powerToeplitz_det_eq_eval (m n : ℕ) :
    (powerToeplitz m n).det = (matM m).det.eval (n : ℚ) := by
  rw [powerToeplitz_eq_one_add, Matrix.det_one_add_mul_comm]
  have hev : (matM m).det.eval (n : ℚ) = ((evalRingHom (n : ℚ)).mapMatrix (matM m)).det := by
    change evalRingHom (n : ℚ) (matM m).det = _
    exact RingHom.map_det (evalRingHom (n : ℚ)) (matM m)
  rw [hev]
  congr 1
  ext r s
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, coe_evalRingHom, one_add_matV_mul_matU]
  simp only [matM, eval_add, apply_ite (Polynomial.eval (n : ℚ)), eval_one, eval_zero, eval_mul,
    eval_C, faulh_eval_nat]

private lemma faulh_eval_0 (x : ℚ) : (faulh 0).eval x = x := by
  rw [faulh]
  simp

private lemma faulh_eval_1 (x : ℚ) : (faulh 1).eval x = (-1 / 2 : ℚ) * x + (1 / 2 : ℚ) * x ^ 2 := by
  rw [faulh]
  simp [faulh_eval_0]
  ring

private lemma faulh_eval_2 (x : ℚ) :
    (faulh 2).eval x = (1 / 6 : ℚ) * x - (1 / 2 : ℚ) * x ^ 2 + (1 / 3 : ℚ) * x ^ 3 := by
  rw [faulh]
  simp [Fin.sum_univ_two, faulh_eval_0, faulh_eval_1]
  ring

private lemma faulh_eval_3 (x : ℚ) :
    (faulh 3).eval x = (1 / 4 : ℚ) * x ^ 2 - (1 / 2 : ℚ) * x ^ 3 + (1 / 4 : ℚ) * x ^ 4 := by
  rw [faulh]
  simp [Fin.sum_univ_three, faulh_eval_0, faulh_eval_1, faulh_eval_2, Nat.choose]
  ring

private lemma faulh_eval_4 (x : ℚ) :
    (faulh 4).eval x =
      (-1 / 30 : ℚ) * x + (1 / 3 : ℚ) * x ^ 3 - (1 / 2 : ℚ) * x ^ 4 + (1 / 5 : ℚ) * x ^ 5 := by
  rw [faulh]
  simp [Fin.sum_univ_four, faulh_eval_0, faulh_eval_1, faulh_eval_2, faulh_eval_3, Nat.choose]
  ring

private lemma faulh_eval_5 (x : ℚ) :
    (faulh 5).eval x =
      (-1 / 12 : ℚ) * x ^ 2 + (5 / 12 : ℚ) * x ^ 4 - (1 / 2 : ℚ) * x ^ 5 + (1 / 6 : ℚ) * x ^ 6 := by
  rw [faulh]
  simp [Fin.sum_univ_five, faulh_eval_0, faulh_eval_1, faulh_eval_2, faulh_eval_3, faulh_eval_4,
    Nat.choose]
  ring

private lemma faulh_eval_6 (x : ℚ) :
    (faulh 6).eval x =
      (1 / 42 : ℚ) * x - (1 / 6 : ℚ) * x ^ 3 + (1 / 2 : ℚ) * x ^ 5 - (1 / 2 : ℚ) * x ^ 6 +
        (1 / 7 : ℚ) * x ^ 7 := by
  rw [faulh]
  simp [Fin.sum_univ_six, faulh_eval_0, faulh_eval_1, faulh_eval_2, faulh_eval_3, faulh_eval_4,
    faulh_eval_5, Nat.choose]
  ring

private lemma matM3_eval_det (x : ℚ) :
    ((matM 3).det).eval x =
      1 + cubicQuotient (x ^ 2) * x ^ 2 * (x ^ 2 - 1) / 672000 := by
  have hev : (matM 3).det.eval x = ((evalRingHom x).mapMatrix (matM 3)).det := by
    change evalRingHom x (matM 3).det = _
    exact RingHom.map_det (evalRingHom x) (matM 3)
  set M : Matrix (Fin 4) (Fin 4) ℚ := (evalRingHom x).mapMatrix (matM 3)
  have hM (r s : Fin 4) : M r s = (if r = s then (1 : ℚ) else 0) +
      (-1 : ℚ) ^ (3 - r.val) * (Nat.choose 3 s.val : ℚ) * (faulh (3 - r.val + s.val)).eval x := by
    simp only [M, RingHom.mapMatrix_apply, Matrix.map_apply, coe_evalRingHom, matM,
      eval_add, apply_ite (Polynomial.eval x), eval_one, eval_zero, eval_mul, eval_C]
  have e00 : M 0 0 = 1 - (faulh 3).eval x := by rw [hM]; split_ifs with h; { norm_num [Nat.choose]; ring }; exact absurd rfl h
  have e01 : M 0 1 = -3 * (faulh 4).eval x := by rw [hM]; split_ifs with h; { exact absurd h (by decide) }; norm_num [Nat.choose]
  have e02 : M 0 2 = -3 * (faulh 5).eval x := by rw [hM]; split_ifs with h; { exact absurd h (by decide) }; norm_num [Nat.choose]
  have e03 : M 0 3 = -(faulh 6).eval x := by rw [hM]; split_ifs with h; { exact absurd h (by decide) }; norm_num [Nat.choose]
  have e10 : M 1 0 = (faulh 2).eval x := by rw [hM]; split_ifs with h; { exact absurd h (by decide) }; norm_num [Nat.choose]
  have e11 : M 1 1 = 1 + 3 * (faulh 3).eval x := by rw [hM]; split_ifs with h; { norm_num [Nat.choose] }; exact absurd rfl h
  have e12 : M 1 2 = 3 * (faulh 4).eval x := by rw [hM]; split_ifs with h; { exact absurd h (by decide) }; norm_num [Nat.choose]
  have e13 : M 1 3 = (faulh 5).eval x := by rw [hM]; split_ifs with h; { exact absurd h (by decide) }; norm_num [Nat.choose]
  have e20 : M 2 0 = -(faulh 1).eval x := by rw [hM]; split_ifs with h; { exact absurd h (by decide) }; norm_num [Nat.choose]
  have e21 : M 2 1 = -3 * (faulh 2).eval x := by rw [hM]; split_ifs with h; { exact absurd h (by decide) }; norm_num [Nat.choose]
  have e22 : M 2 2 = 1 - 3 * (faulh 3).eval x := by rw [hM]; split_ifs with h; { norm_num [Nat.choose]; ring }; exact absurd rfl h
  have e23 : M 2 3 = -(faulh 4).eval x := by rw [hM]; split_ifs with h; { exact absurd h (by decide) }; norm_num [Nat.choose]
  have e30 : M 3 0 = (faulh 0).eval x := by rw [hM]; split_ifs with h; { exact absurd h (by decide) }; norm_num [Nat.choose]
  have e31 : M 3 1 = 3 * (faulh 1).eval x := by rw [hM]; split_ifs with h; { exact absurd h (by decide) }; norm_num [Nat.choose]
  have e32 : M 3 2 = 3 * (faulh 2).eval x := by rw [hM]; split_ifs with h; { exact absurd h (by decide) }; norm_num [Nat.choose]
  have e33 : M 3 3 = 1 + (faulh 3).eval x := by rw [hM]; split_ifs with h; { norm_num [Nat.choose] }; exact absurd rfl h
  have sa00 : (0 : Fin 4).succAbove 0 = 1 := rfl
  have sa01 : (0 : Fin 4).succAbove 1 = 2 := rfl
  have sa02 : (0 : Fin 4).succAbove 2 = 3 := rfl
  have sa10 : (1 : Fin 4).succAbove 0 = 0 := rfl
  have sa11 : (1 : Fin 4).succAbove 1 = 2 := rfl
  have sa12 : (1 : Fin 4).succAbove 2 = 3 := rfl
  have sa20 : (2 : Fin 4).succAbove 0 = 0 := rfl
  have sa21 : (2 : Fin 4).succAbove 1 = 1 := rfl
  have sa22 : (2 : Fin 4).succAbove 2 = 3 := rfl
  have sa30 : (3 : Fin 4).succAbove 0 = 0 := rfl
  have sa31 : (3 : Fin 4).succAbove 1 = 1 := rfl
  have sa32 : (3 : Fin 4).succAbove 2 = 2 := rfl
  have hs0 : Fin.succ (0 : Fin 3) = 1 := rfl
  have hs1 : Fin.succ (1 : Fin 3) = 2 := rfl
  have hs2 : Fin.succ (2 : Fin 3) = 3 := rfl
  have hv0 : ((0 : Fin 4) : ℕ) = 0 := rfl
  have hv1 : ((1 : Fin 4) : ℕ) = 1 := rfl
  have hv2 : ((2 : Fin 4) : ℕ) = 2 := rfl
  have hv3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [hev]
  change M.det = _
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply]
  rw [sa00, sa01, sa02, sa10, sa11, sa12, sa20, sa21, sa22, sa30, sa31, sa32,
    hs0, hs1, hs2, hv0, hv1, hv2, hv3,
    e00, e01, e02, e03, e10, e11, e12, e13, e20, e21, e22, e23, e30, e31, e32, e33,
    faulh_eval_0, faulh_eval_1, faulh_eval_2, faulh_eval_3, faulh_eval_4, faulh_eval_5,
    faulh_eval_6, cubicQuotient]
  ring

private lemma X_dvd_faulh (k : ℕ) : X ∣ faulh k := by
  rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
  exact faulh_eval_zero k

private lemma one_add_prod_mod_X_sq {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → ℚ[X])
    (hg : ∀ i ∈ s, X ∣ g i) :
    X ^ 2 ∣ (∏ i ∈ s, (1 + g i)) - (1 + ∑ i ∈ s, g i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have haX : X ∣ g a := hg a (Finset.mem_insert_self a s)
    have hsX : ∀ i ∈ s, X ∣ g i := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    rcases ih hsX with ⟨Q, hQ⟩
    have hsumX : X ∣ ∑ i ∈ s, g i := Finset.dvd_sum hsX
    have hmul : X ^ 2 ∣ g a * ∑ i ∈ s, g i := by
      rw [sq]
      exact mul_dvd_mul haX hsumX
    rcases hmul with ⟨R, hR⟩
    refine ⟨R + (1 + g a) * Q, ?_⟩
    have hQ' : ∏ i ∈ s, (1 + g i) = 1 + ∑ i ∈ s, g i + X ^ 2 * Q := by linear_combination hQ
    rw [hQ']
    linear_combination hR

private lemma X_sq_dvd_matM_det_sub_one (m : ℕ) (hm : 0 < m) :
    X ^ 2 ∣ (matM m).det - 1 := by
  rw [Matrix.det_apply]
  have hsplit : (∑ σ : Equiv.Perm (Fin (m + 1)), Equiv.Perm.sign σ • ∏ i, matM m (σ i) i) - 1 =
      ((∏ i : Fin (m + 1), matM m i i) - 1) +
        ∑ σ ∈ Finset.univ.erase (1 : Equiv.Perm (Fin (m + 1))),
          Equiv.Perm.sign σ • ∏ i, matM m (σ i) i := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (1 : Equiv.Perm (Fin (m + 1))))]
    simp only [Equiv.Perm.sign_one, one_smul, Equiv.Perm.coe_one, id_eq]
    ring
  rw [hsplit]
  refine dvd_add ?_ (Finset.dvd_sum fun σ hσ => ?_)
  · have hg : ∀ i : Fin (m + 1),
        X ∣ C ((-1 : ℚ) ^ (m - i.val) * (m.choose i.val : ℚ)) * faulh m := fun i =>
      dvd_mul_of_dvd_right (X_dvd_faulh m) _
    have hdiag : (∏ i : Fin (m + 1), matM m i i) =
        ∏ i : Fin (m + 1), (1 + C ((-1 : ℚ) ^ (m - i.val) * (m.choose i.val : ℚ)) * faulh m) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [matM, Nat.sub_add_cancel (Nat.le_of_lt_succ i.isLt)]
    have hsum0 : ∑ i : Fin (m + 1), C ((-1 : ℚ) ^ (m - i.val) * (m.choose i.val : ℚ)) * faulh m = 0 := by
      rw [← Finset.sum_mul, ← map_sum]
      have hc0 : (∑ i : Fin (m + 1), (-1 : ℚ) ^ (m - i.val) * (m.choose i.val : ℚ)) = 0 := by
        have hbin : (1 + (-1 : ℚ)) ^ m =
            ∑ i : Fin (m + 1), (-1 : ℚ) ^ (m - i.val) * (m.choose i.val : ℚ) := by
          rw [add_pow, ← Fin.sum_univ_eq_sum_range]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [mul_comm]
        rw [← hbin, add_neg_cancel, zero_pow hm.ne']
      rw [hc0, C_0, zero_mul]
    rw [hdiag]
    have hmod := one_add_prod_mod_X_sq Finset.univ
      (fun i : Fin (m + 1) => C ((-1 : ℚ) ^ (m - i.val) * (m.choose i.val : ℚ)) * faulh m)
      (fun i _ => hg i)
    rw [hsum0, add_zero] at hmod
    exact hmod
  · have hne1 : σ ≠ 1 := (Finset.mem_erase.mp hσ).1
    have hex1 : ∃ i₁ : Fin (m + 1), σ i₁ ≠ i₁ := by
      by_contra h
      apply hne1
      refine Equiv.Perm.ext fun i => ?_
      by_contra hi
      exact h ⟨i, hi⟩
    rcases hex1 with ⟨i₁, hi₁⟩
    let i₂ := σ i₁
    have hi₂ : σ i₂ ≠ i₂ := fun heq => hi₁ (σ.injective heq)
    have h12 : i₁ ≠ i₂ := hi₁.symm
    have hdvd1 : X ∣ matM m (σ i₁) i₁ := by
      simp only [matM, hi₁, ↓reduceIte, zero_add]
      exact dvd_mul_of_dvd_right (X_dvd_faulh _) _
    have hdvd2 : X ∣ matM m (σ i₂) i₂ := by
      simp only [matM, hi₂, ↓reduceIte, zero_add]
      exact dvd_mul_of_dvd_right (X_dvd_faulh _) _
    have hprod : X ^ 2 ∣ ∏ i, matM m (σ i) i := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₁)]
      have hi₂mem : i₂ ∈ Finset.univ.erase i₁ := Finset.mem_erase.mpr ⟨h12.symm, Finset.mem_univ _⟩
      rw [← Finset.mul_prod_erase _ _ hi₂mem, sq, ← mul_assoc]
      exact dvd_mul_of_dvd_left (mul_dvd_mul hdvd1 hdvd2) _
    rw [Units.smul_def, zsmul_eq_mul]
    exact dvd_mul_of_dvd_right hprod _

private lemma matM_det_eval_one (m : ℕ) (hm : 0 < m) : (matM m).det.eval 1 = 1 := by
  rw [← Nat.cast_one, ← powerToeplitz_det_eq_eval]
  simp [powerToeplitz, hm.ne']

private lemma matM_det_eval_neg_one (m : ℕ) (hm : 0 < m) : (matM m).det.eval (-1) = 1 := by
  have hev : (matM m).det.eval (-1) = ((evalRingHom (-1 : ℚ)).mapMatrix (matM m)).det := by
    change evalRingHom (-1 : ℚ) (matM m).det = _
    exact RingHom.map_det (evalRingHom (-1 : ℚ)) (matM m)
  rw [hev]
  have hmat : (evalRingHom (-1 : ℚ)).mapMatrix (matM m) =
      1 + Matrix.replicateCol Unit (fun _ : Fin (m + 1) => (-1 : ℚ)) *
        Matrix.replicateRow Unit (fun s : Fin (m + 1) => (m.choose s.val : ℚ) * (-1 : ℚ) ^ s.val) := by
    ext r s
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, coe_evalRingHom, matM,
      eval_add, apply_ite (Polynomial.eval (-1 : ℚ)), eval_one, eval_zero, eval_mul, eval_C,
      faulh_eval_neg_one, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply,
      Matrix.replicateCol_apply, Matrix.replicateRow_apply, Finset.univ_unique,
      Finset.sum_singleton]
    congr 1
    have hpow2 : (-1 : ℚ) ^ (m - r.val) * (-1 : ℚ) ^ (m - r.val + s.val) = (-1 : ℚ) ^ s.val := by
      rw [pow_add, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
    calc
      (-1 : ℚ) ^ (m - r.val) * (m.choose s.val : ℚ) * -(-1 : ℚ) ^ (m - r.val + s.val)
        = -(m.choose s.val : ℚ) * ((-1 : ℚ) ^ (m - r.val) * (-1 : ℚ) ^ (m - r.val + s.val)) := by ring
      _ = (-1 : ℚ) * ((m.choose s.val : ℚ) * (-1 : ℚ) ^ s.val) := by rw [hpow2]; ring
  rw [hmat, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hdot : (fun s : Fin (m + 1) => (m.choose s.val : ℚ) * (-1 : ℚ) ^ s.val) ⬝ᵥ
      (fun _ => (-1 : ℚ)) = 0 := by
    simp only [dotProduct, mul_neg_one, Finset.sum_neg_distrib, neg_eq_zero]
    have hbin : (-1 + (1 : ℚ)) ^ m =
        ∑ s : Fin (m + 1), (m.choose s.val : ℚ) * (-1 : ℚ) ^ s.val := by
      rw [add_pow, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun s _ => ?_
      simp [mul_comm]
    rw [← hbin, neg_add_cancel, zero_pow hm.ne']
  rw [hdot, add_zero]

private def cauchyMat (k : ℕ) (x y : Fin k → ℚ) : Matrix (Fin k) (Fin k) ℚ :=
  fun i j => (x i + y j)⁻¹

private lemma cauchyMat_det_ne_zero :
    ∀ (k : ℕ) (x y : Fin k → ℚ), Function.Injective x → Function.Injective y →
      (∀ i j, x i + y j ≠ 0) → (cauchyMat k x y).det ≠ 0
  | 0, _, _, _, _, _ => by simp
  | k + 1, x, y, hx, hy, hxy => by
    let L : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ :=
      fun i j => if i = j then 1 else if j = 0 then -((x 0 + y 0) / (x i + y 0)) else 0
    have hLtri : L.IsLowerTriangular := by
      intro i j hij
      have hij' : i ≠ j := ne_of_lt hij
      have hj0 : j ≠ 0 := Fin.ne_of_gt (lt_of_le_of_lt (Fin.zero_le i) hij)
      simp [L, hij', hj0]
    have hLdet : L.det = 1 := by
      rw [Matrix.det_of_isLowerTriangular L hLtri]
      exact Finset.prod_eq_one fun i _ => by simp [L]
    have hLC_row0 : ∀ j : Fin (k + 1), (L * cauchyMat (k + 1) x y) 0 j = (x 0 + y j)⁻¹ := by
      intro j
      rw [Matrix.mul_apply, Fin.sum_univ_succ]
      have hs : ∑ t : Fin k, L 0 t.succ * cauchyMat (k + 1) x y t.succ j = 0 :=
        Finset.sum_eq_zero fun t _ => by
          have h0ne : (0 : Fin (k + 1)) ≠ t.succ := (Fin.succ_ne_zero t).symm
          simp [L, h0ne]
      rw [hs, add_zero]
      simp [L, cauchyMat]
    have hLC_row_succ : ∀ (i : Fin k) (j : Fin (k + 1)),
        (L * cauchyMat (k + 1) x y) i.succ j =
          (x i.succ + y j)⁻¹ - ((x 0 + y 0) / (x i.succ + y 0)) * (x 0 + y j)⁻¹ := by
      intro i j
      rw [Matrix.mul_apply, Fin.sum_univ_succ]
      have h0 : L i.succ 0 * cauchyMat (k + 1) x y 0 j =
          -((x 0 + y 0) / (x i.succ + y 0)) * (x 0 + y j)⁻¹ := by
        simp [L, cauchyMat, Fin.succ_ne_zero]
      have hs : ∑ t : Fin k, L i.succ t.succ * cauchyMat (k + 1) x y t.succ j =
          (x i.succ + y j)⁻¹ := by
        have hsingle : ∀ t : Fin k, L i.succ t.succ * cauchyMat (k + 1) x y t.succ j =
            if i = t then (x i.succ + y j)⁻¹ else 0 := by
          intro t
          by_cases hit : i = t
          · subst hit
            simp [L, cauchyMat]
          · have hne : i.succ ≠ t.succ := fun h => hit (Fin.succ_inj.mp h)
            simp [L, hne, hit, Fin.succ_ne_zero]
        simp [hsingle]
      rw [h0, hs]
      ring
    have hcol0 : ∀ i : Fin k, (L * cauchyMat (k + 1) x y) i.succ 0 = 0 := by
      intro i
      rw [hLC_row_succ]
      have h1 : x i.succ + y 0 ≠ 0 := hxy i.succ 0
      have h2 : x 0 + y 0 ≠ 0 := hxy 0 0
      field_simp
      ring
    have hdet_eq : (cauchyMat (k + 1) x y).det =
        (x 0 + y 0)⁻¹ * ((L * cauchyMat (k + 1) x y).submatrix Fin.succ Fin.succ).det := by
      rw [← one_mul (cauchyMat (k + 1) x y).det, ← hLdet, ← Matrix.det_mul,
        Matrix.det_succ_column_zero, Fin.sum_univ_succ]
      have hs : ∑ i : Fin k, (-1 : ℚ) ^ i.succ.val * (L * cauchyMat (k + 1) x y) i.succ 0 *
          ((L * cauchyMat (k + 1) x y).submatrix i.succ.succAbove Fin.succ).det = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hcol0 i, mul_zero, zero_mul]
      rw [hs, add_zero, Fin.val_zero, pow_zero, one_mul, hLC_row0 0, Fin.succAbove_zero]
    let d₁ : Fin k → ℚ := fun i => (x i.succ - x 0) / (x i.succ + y 0)
    let d₂ : Fin k → ℚ := fun j => (y j.succ - y 0) / (x 0 + y j.succ)
    have hsub_eq : (L * cauchyMat (k + 1) x y).submatrix Fin.succ Fin.succ =
        Matrix.diagonal d₁ * cauchyMat k (x ∘ Fin.succ) (y ∘ Fin.succ) * Matrix.diagonal d₂ := by
      ext i j
      simp only [Matrix.submatrix_apply, hLC_row_succ, Matrix.mul_apply, Matrix.diagonal_apply,
        Function.comp_apply, cauchyMat, d₁, d₂]
      simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte, Finset.sum_ite_eq]
      have h1 : x i.succ + y j.succ ≠ 0 := hxy i.succ j.succ
      have h2 : x i.succ + y 0 ≠ 0 := hxy i.succ 0
      have h3 : x 0 + y j.succ ≠ 0 := hxy 0 j.succ
      field_simp
      ring
    rw [hdet_eq, hsub_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
    have h00 : (x 0 + y 0)⁻¹ ≠ 0 := inv_ne_zero (hxy 0 0)
    have hd1 : ∏ i : Fin k, d₁ i ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun i _ => div_ne_zero ?_ (hxy i.succ 0)
      exact sub_ne_zero.mpr fun h => Fin.succ_ne_zero i (hx h)
    have hd2 : ∏ j : Fin k, d₂ j ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun j _ => div_ne_zero ?_ (hxy 0 j.succ)
      exact sub_ne_zero.mpr fun h => Fin.succ_ne_zero j (hy h)
    have hIH : (cauchyMat k (x ∘ Fin.succ) (y ∘ Fin.succ)).det ≠ 0 :=
      cauchyMat_det_ne_zero k (x ∘ Fin.succ) (y ∘ Fin.succ)
        (hx.comp (@Fin.succ_injective k)) (hy.comp (@Fin.succ_injective k))
        fun i j => hxy i.succ j.succ
    exact mul_ne_zero h00 (mul_ne_zero (mul_ne_zero hd1 hIH) hd2)

private lemma prod_natDegree_and_coeff {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℚ[X]) (d : ι → ℕ)
    (hf : ∀ i ∈ s, (f i).natDegree ≤ d i) :
    (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, d i ∧
      (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (f i).coeff (d i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rcases ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) with ⟨hdegS, hcoeffS⟩
    have hda : (f a).natDegree ≤ d a := hf a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    constructor
    · exact (natDegree_mul_le).trans (add_le_add hda hdegS)
    · rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun u v => (f a).coeff u * (∏ i ∈ s, f i).coeff v)]
      have hsplit : ∑ k ∈ Finset.range (d a + ∑ i ∈ s, d i + 1),
          (f a).coeff k * (∏ i ∈ s, f i).coeff (d a + ∑ i ∈ s, d i - k) =
          (f a).coeff (d a) * (∏ i ∈ s, f i).coeff (∑ i ∈ s, d i) := by
        rw [Finset.sum_eq_single (d a)]
        · simp
        · intro k _ hkne
          rcases lt_or_gt_of_ne hkne with hlt | hgt
          · have hgtS : ∑ i ∈ s, d i < d a + ∑ i ∈ s, d i - k := by omega
            rw [coeff_eq_zero_of_natDegree_lt (hdegS.trans_lt hgtS), mul_zero]
          · rw [coeff_eq_zero_of_natDegree_lt (hda.trans_lt hgt), zero_mul]
        · intro hmem
          exfalso
          apply hmem
          rw [Finset.mem_range]
          omega
      rw [hsplit, hcoeffS]

private lemma matM_det_natDegree (m : ℕ) :
    (matM m).det.natDegree = (m + 1) ^ 2 := by
  let d : Fin (m + 1) → Fin (m + 1) → ℕ := fun r s => m - r.val + s.val + 1
  have hsum_d : ∀ σ : Equiv.Perm (Fin (m + 1)),
      ∑ i : Fin (m + 1), d (σ i) i = (m + 1) ^ 2 := by
    intro σ
    zify
    have hcast : ∀ i : Fin (m + 1), (d (σ i) i : ℤ) = (m : ℤ) - (σ i).val + i.val + 1 := by
      intro i
      have hle : (σ i).val ≤ m := Nat.le_of_lt_succ (σ i).isLt
      simp only [d]
      omega
    simp_rw [hcast]
    have hperm : ∑ i : Fin (m + 1), ((σ i).val : ℤ) = ∑ i : Fin (m + 1), (i.val : ℤ) :=
      Equiv.sum_comp σ fun x : Fin (m + 1) => (x.val : ℤ)
    have heq : ∑ i : Fin (m + 1), ((m : ℤ) - (σ i).val + i.val + 1) =
        ∑ _i : Fin (m + 1), ((m : ℤ) + 1) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hperm]
      ring
    rw [heq, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hdeg_entry : ∀ r s : Fin (m + 1), (matM m r s).natDegree ≤ d r s := by
    intro r s
    simp only [matM, d]
    exact (natDegree_add_le _ _).trans
      (max_le (by split_ifs <;> simp) ((natDegree_C_mul_le _ _).trans_eq (faulh_natDegree _)))
  have hdeg_le : (matM m).det.natDegree ≤ (m + 1) ^ 2 := by
    rw [Matrix.det_apply]
    refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
    refine natDegree_mul_le.trans ?_
    rw [natDegree_intCast, zero_add, ← hsum_d σ]
    exact (prod_natDegree_and_coeff Finset.univ (fun i => matM m (σ i) i)
      (fun i => d (σ i) i) fun i _ => hdeg_entry (σ i) i).1
  have hcoeff_ne : (matM m).det.coeff ((m + 1) ^ 2) ≠ 0 := by
    rw [Matrix.det_apply, finsetSum_coeff]
    have hterm : ∀ σ : Equiv.Perm (Fin (m + 1)),
        (Equiv.Perm.sign σ • ∏ i : Fin (m + 1), matM m (σ i) i).coeff ((m + 1) ^ 2) =
          (∏ r : Fin (m + 1), (-1 : ℚ) ^ (m - r.val)) *
            (∏ s : Fin (m + 1), (m.choose s.val : ℚ)) *
            (Equiv.Perm.sign σ • ∏ i : Fin (m + 1),
              (((m + 1 - (σ i).val : ℕ) : ℚ) + (i.val : ℚ))⁻¹) := by
      intro σ
      rw [Units.smul_def, zsmul_eq_mul, coeff_intCast_mul, ← hsum_d σ,
        (prod_natDegree_and_coeff Finset.univ (fun i => matM m (σ i) i)
          (fun i => d (σ i) i) fun i _ => hdeg_entry (σ i) i).2]
      have hce : ∀ i : Fin (m + 1),
          (matM m (σ i) i).coeff (d (σ i) i) =
            (-1 : ℚ) ^ (m - (σ i).val) * (m.choose i.val : ℚ) *
              (((m + 1 - (σ i).val : ℕ) : ℚ) + (i.val : ℚ))⁻¹ := by
        intro i
        simp only [matM, coeff_add, coeff_C_mul]
        have hif : (if σ i = i then (1 : ℚ[X]) else 0).coeff (d (σ i) i) = 0 := by
          split_ifs with heq
          · have hgt : d (σ i) i ≠ 0 := by simp [d]
            simp [coeff_one, hgt]
          · simp
        rw [hif, zero_add]
        have hlc : (faulh (m - (σ i).val + i.val)).coeff (d (σ i) i) =
            (((m + 1 - (σ i).val : ℕ) : ℚ) + (i.val : ℚ))⁻¹ := by
          have hd_eq : d (σ i) i = (faulh (m - (σ i).val + i.val)).natDegree := by
            rw [faulh_natDegree]
          rw [hd_eq, ← leadingCoeff, faulh_leadingCoeff]
          have hle : (σ i).val ≤ m := Nat.le_of_lt_succ (σ i).isLt
          congr 1
          norm_cast
          omega
        rw [hlc]
      simp_rw [hce, Finset.prod_mul_distrib]
      have hsign : (∏ i : Fin (m + 1), (-1 : ℚ) ^ (m - (σ i).val)) =
          ∏ r : Fin (m + 1), (-1 : ℚ) ^ (m - r.val) :=
        Equiv.prod_comp σ fun r : Fin (m + 1) => (-1 : ℚ) ^ (m - r.val)
      rw [hsign, Units.smul_def, zsmul_eq_mul]
      ring
    have hdet_cauchy :
        (cauchyMat (m + 1) (fun r => ((m + 1 - r.val : ℕ) : ℚ)) (fun s => (s.val : ℚ))).det =
          ∑ σ : Equiv.Perm (Fin (m + 1)),
            Equiv.Perm.sign σ • ∏ i : Fin (m + 1),
              (((m + 1 - (σ i).val : ℕ) : ℚ) + (i.val : ℚ))⁻¹ := by
      rw [Matrix.det_apply]
      rfl
    simp_rw [hterm, ← Finset.mul_sum]
    rw [← hdet_cauchy]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · exact Finset.prod_ne_zero_iff.mpr fun r _ => pow_ne_zero _ (by norm_num)
    · refine Finset.prod_ne_zero_iff.mpr fun s _ => ?_
      exact Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_of_lt_succ s.isLt)).ne'
    · refine cauchyMat_det_ne_zero (m + 1) (fun r => ((m + 1 - r.val : ℕ) : ℚ))
        (fun s => (s.val : ℚ)) ?_ ?_ ?_
      · intro r₁ r₂ h
        have hnat : m + 1 - r₁.val = m + 1 - r₂.val := Nat.cast_injective h
        have h1 : r₁.val ≤ m + 1 := Nat.le_of_lt r₁.isLt
        have h2 : r₂.val ≤ m + 1 := Nat.le_of_lt r₂.isLt
        exact Fin.ext (by omega)
      · intro s₁ s₂ h
        exact Fin.ext (Nat.cast_injective h)
      · intro r s
        have hpos : (0 : ℚ) < ((m + 1 - r.val : ℕ) : ℚ) + (s.val : ℚ) := by
          have hr : r.val < m + 1 := r.isLt
          have hq : (0 : ℚ) < ((m + 1 - r.val : ℕ) : ℚ) := Nat.cast_pos.mpr (Nat.sub_pos_of_lt hr)
          have hs : (0 : ℚ) ≤ (s.val : ℚ) := Nat.cast_nonneg _
          linarith
        exact hpos.ne'
  exact le_antisymm hdeg_le (le_natDegree_of_ne_zero hcoeff_ne)

end OMA.S_oeis_a355326_proof

open scoped BigOperators Matrix Polynomial
open Polynomial OMA.S_oeis_a355326 OMA.S_oeis_a355326_proof

theorem OMA.solution : type_of% @OMA.S_oeis_a355326.main := by
  constructor
  · intro n
    rw [a, powerToeplitz_det_eq_eval, matM3_eval_det]
  · intro m hm
    rcases X_sq_dvd_matM_det_sub_one m hm with ⟨P₀, hP₀⟩
    have hP₀_1 : P₀.eval 1 = 0 := by
      have h := congrArg (Polynomial.eval (1 : ℚ)) hP₀
      rw [eval_sub, matM_det_eval_one m hm, eval_one, sub_self, eval_mul, eval_pow, eval_X,
        one_pow, one_mul] at h
      exact h.symm
    rcases dvd_iff_isRoot.mpr hP₀_1 with ⟨P₁, hP₁⟩
    have hP₁_neg1 : P₁.eval (-1) = 0 := by
      have h := congrArg (Polynomial.eval (-1 : ℚ)) hP₀
      rw [hP₁] at h
      rw [eval_sub, matM_det_eval_neg_one m hm, eval_one, sub_self, eval_mul, eval_pow, eval_X,
        eval_mul, eval_sub, eval_X, eval_C] at h
      norm_num at h
      linarith
    have hdvd_neg1 : X - C (-1 : ℚ) ∣ P₁ := dvd_iff_isRoot.mpr hP₁_neg1
    rcases hdvd_neg1 with ⟨P, hP⟩
    have hfact : (matM m).det - 1 = X ^ 2 * (X ^ 2 - 1) * P := by
      rw [hP₀, hP₁, hP]
      simp only [C_1, map_neg]
      ring
    have hsub_deg : ((matM m).det - 1).natDegree = (m + 1) ^ 2 := by
      rw [natDegree_sub_eq_left_of_natDegree_lt]
      · exact matM_det_natDegree m
      · rw [natDegree_one, matM_det_natDegree m]
        nlinarith
    have hsub_ne : (matM m).det - 1 ≠ 0 := by
      intro h0
      rw [h0, natDegree_zero] at hsub_deg
      nlinarith
    have hP_ne : P ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hfact
      exact hsub_ne hfact
    have hQ_ne : (X ^ 2 * (X ^ 2 - 1) : ℚ[X]) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hfact
      exact hsub_ne hfact
    have hQ_deg : (X ^ 2 * (X ^ 2 - 1) : ℚ[X]).natDegree = 4 := by
      have h1 : (X ^ 2 - 1 : ℚ[X]).natDegree = 2 := by
        rw [natDegree_sub_eq_left_of_natDegree_lt]
        · exact natDegree_X_pow 2
        · rw [natDegree_one, natDegree_X_pow]
          norm_num
      have h1_ne : (X ^ 2 - 1 : ℚ[X]) ≠ 0 := by
        intro h0
        rw [h0, natDegree_zero] at h1
        norm_num at h1
      rw [natDegree_mul (pow_ne_zero 2 X_ne_zero) h1_ne, natDegree_X_pow, h1]
    have hP_deg : P.natDegree = (m + 1) ^ 2 - 4 := by
      have hm_deg := congrArg Polynomial.natDegree hfact
      rw [hsub_deg, natDegree_mul hQ_ne hP_ne, hQ_deg] at hm_deg
      omega
    refine ⟨P, hP_ne, hP_deg, fun n _ => ?_⟩
    rw [powerToeplitz_det_eq_eval]
    have hev := congrArg (Polynomial.eval (n : ℚ)) hfact
    simp only [eval_sub, eval_one, eval_mul, eval_pow, eval_X] at hev
    linarith
