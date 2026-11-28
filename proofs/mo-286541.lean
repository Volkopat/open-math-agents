import OMAStatements.S_mo_286541

/-!
# A triangular reduction for Cigler's Hankel determinant quotient

Johann Cigler reported a J-fraction proof on MathOverflow and asked for
a direct row and column argument. For moments with unit constant term,
the triangular Toeplitz matrix of the reciprocal series reduces the Hankel
determinant to a minor of its reciprocal coefficients. Pascal's recurrence
compares the two reciprocal series without a continued fraction.
Source: https://mathoverflow.net/questions/286541 (CC BY-SA 3.0).
Credit: @connoranderson
-/

open PowerSeries OMA.S_mo_286541
namespace Cigler

noncomputable def Bino (s r : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => (((s+1)*n+r).choose n : ℚ)

private lemma bino_step (s r : ℕ) :
    Bino s (r+1) = Bino s r + Bino s (r+(s+1))*X := by
  ext n
  cases n with
  | zero => simp [Bino]
  | succ n =>
    simp only [map_add, coeff_succ_mul_X, Bino, coeff_mk]
    rw [show (s+1)*(n+1)+(r+1) = ((s+1)*(n+1)+r)+1 by ring,
      Nat.choose_succ_succ', Nat.cast_add]
    rw [show (s+1)*n + (r+(s+1)) = (s+1)*(n+1)+r by ring]
    ring

private lemma first_step (s : ℕ) :
    Bino s 0 = 1 + C (s+1 : ℚ) * Bino s s * X := by
  ext n
  cases n with
  | zero => simp [Bino]
  | succ n =>
    rw [map_add, coeff_one, if_neg (Nat.succ_ne_zero _), zero_add, coeff_succ_mul_X, coeff_C_mul]
    simp only [Bino, coeff_mk, Nat.add_zero]
    have e := Nat.add_one_mul_choose_eq ((s+1)*n+s) n
    have he : (s+1)*n+s+1 = (s+1)*(n+1) := by ring
    rw [he] at e
    have he' : (s+1)*Nat.choose ((s+1)*n+s) n = Nat.choose ((s+1)*(n+1)) (n+1) := by
      apply Nat.mul_right_cancel (m := n+1) (by omega)
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using e
    exact_mod_cast he'.symm

noncomputable def Ran (s : ℕ) : ℕ → PowerSeries ℚ
  | 0 => 1
  | r+1 => C (s+1 : ℚ) * Bino s r - C (s : ℚ) * Bino s (r+1)

private lemma ran_step (s r : ℕ) :
    Ran s (r+1) = Ran s r + Ran s (r+(s+1))*X := by
  cases r with
  | zero =>
    simp only [Ran, zero_add]
    rw [bino_step s 0]
    simp only [zero_add]
    have h := first_step s
    have hc : C (s+1 : ℚ) = C (s : ℚ) + 1 := by simp
    rw [hc] at h ⊢
    rw [show Nat.add 0 s = s from Nat.zero_add s]
    linear_combination h
  | succ r =>
    simp only [Ran]
    rw [show Nat.add (r+1) s = r+(s+1) by change (r+1)+s = _; omega]
    rw [show r+(s+1)+1 = (r+1)+(s+1) by omega]
    linear_combination C (s+1 : ℚ) * (bino_step s r) -
      C (s : ℚ) * (bino_step s (r+1))

private lemma bino_ran (s r : ℕ) : Bino s 0 * Ran s r = Bino s r := by
  ext n
  induction n generalizing r with
  | zero =>
    cases r with
    | zero => simp [Ran]
    | succ r => simp [Ran, Bino, coeff_zero_eq_constantCoeff_apply]
  | succ n ih =>
    induction r with
    | zero => simp [Ran]
    | succ r hr =>
      rw [ran_step, mul_add, ← mul_assoc, map_add, coeff_succ_mul_X, hr, ih,
        bino_step s r, map_add, coeff_succ_mul_X]

private lemma ran_one_coeff (s n : ℕ) : coeff n (Ran s 1) = fussCatalan (s+1) n := by
  simp only [Ran, map_sub, coeff_C_mul, Bino, coeff_mk, Nat.add_zero,
    fussCatalan, binomialMoment, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  have e := Nat.choose_mul_succ_eq ((s+1)*n) n
  have hh : (s+1)*n+1-n = s*n+1 := by rw [Nat.add_mul, one_mul]; omega
  rw [hh] at e
  have h : (Nat.choose ((s+1)*n) n : ℚ) * (((s : ℚ)+1)*n+1) =
      Nat.choose ((s+1)*n+1) n * ((s : ℚ)*n+1) := by exact_mod_cast e
  have hn : (s : ℚ)*n+1 ≠ 0 := by positivity
  apply (eq_div_iff hn).2
  linear_combination (s : ℚ)*h

private lemma reciprocal (s : ℕ) :
    (Bino s 0)⁻¹ = C (s+1 : ℚ) * (Ran s 1)⁻¹ - C (s : ℚ) := by
  let A := Bino s 0
  let B := Ran s 1
  have a : constantCoeff A ≠ 0 := by simp [A, Bino]
  have b : constantCoeff B ≠ 0 := by simp [B, Ran, Bino]
  have ai := PowerSeries.inv_mul_cancel A a
  have ab : A * B = Bino s 1 := bino_ran s 1
  have h : B = C (s+1 : ℚ)*A - C (s : ℚ)*(A*B) := by rw [ab]; rfl
  change A⁻¹ = C (s+1 : ℚ) * B⁻¹ - C (s : ℚ)
  rw [eq_sub_iff_add_eq, PowerSeries.eq_mul_inv_iff_mul_eq b]
  linear_combination A⁻¹ * h + (C (s+1 : ℚ) - C (s : ℚ) * B) * ai
end Cigler

open PowerSeries OMA.S_mo_286541
namespace Cigler

private def toe (a : ℕ → ℚ) (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℚ :=
  Matrix.of fun i j => if j.val ≤ i.val then a (i.val-j.val) else 0

private def splitEntry (g : ℕ → ℚ) (i j : ℕ) : ℚ :=
  if i = 0 then (if j = 0 then 1 else 0) else if j = 0 then 0 else -g (i+j)

private def reduced (g : ℕ → ℚ) (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℚ :=
  Matrix.of fun i j => splitEntry g i.val j.val

private lemma toe_det (a : ℕ → ℚ) (a0 : a 0 = 1) (n : ℕ) : (toe a n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [toe, a0]
  · intro i j hij
    change (if j.val ≤ i.val then a (i.val-j.val) else 0) = 0
    exact if_neg (not_le.mpr (show i.val < j.val from hij))

private lemma finite_prefix {N : ℕ} (i : Fin N) (f : ℕ → ℚ) :
    (∑ l : Fin N, if l.val ≤ i.val then f l.val else 0) =
      ∑ l ∈ Finset.range (i.val+1), f l := by
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr_of_eq_on_inter <;> grind

private lemma toe_hankel {a g : ℕ → ℚ} (g0 : g 0 = 1)
    (conv : ∀ m : ℕ, 0 < m → (∑ l ∈ Finset.range (m+1), g l * a (m-l)) = 0)
    (n : ℕ) : toe g n * hankel a n = reduced g n * (toe a n).transpose := by
  ext i j
  simp only [Matrix.mul_apply, toe, hankel, reduced, Matrix.of_apply, Matrix.transpose_apply,
    ite_mul, zero_mul, mul_ite, mul_zero]
  rw [finite_prefix i (fun l => g (i.val-l)*a (l+j.val)),
    finite_prefix j (fun l => splitEntry g i.val l * a (j.val-l))]
  by_cases iz : i.val = 0
  · simp [iz, splitEntry, g0]
  · rw [Finset.sum_range_succ' (fun l => splitEntry g i.val l * a (j.val-l))]
    simp only [splitEntry, if_neg iz, Nat.succ_ne_zero, if_false, if_true, zero_mul, add_zero,
      neg_mul, Finset.sum_neg_distrib]
    apply eq_neg_of_add_eq_zero_left
    have h := conv (i.val+j.val) (by omega)
    rw [show i.val+j.val+1 = (i.val+1)+j.val by omega, Finset.sum_range_add] at h
    convert h using 1
    congr 1
    · rw [← Finset.sum_range_reflect (fun l => g l * a (i.val+j.val-l)) (i.val+1)]
      apply Finset.sum_congr rfl
      intro l hl
      have hl' := Finset.mem_range.mp hl
      simp only [Nat.add_sub_cancel]
      rw [show i.val+j.val-(i.val-l)=l+j.val by omega]
    · apply Finset.sum_congr rfl
      intro l _
      congr 2 <;> omega

private lemma reduced_det (g : ℕ → ℚ) (n : ℕ) :
    (reduced g n).det = (Matrix.of fun i j : Fin n => -g (i.val+j.val+2)).det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [reduced, Matrix.of_apply, Fin.val_zero, splitEntry, if_true, Fin.val_succ,
    Nat.succ_ne_zero, if_false, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, pow_zero,
    mul_one, one_mul]
  congr 1
  ext i j
  simp [Matrix.submatrix_apply, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private lemma normalize_hankel (A : PowerSeries ℚ) (hA : constantCoeff A = 1) (n : ℕ) :
    (hankel (fun i => coeff i A) n).det =
      (Matrix.of fun i j : Fin n => -coeff (i.val+j.val+2) A⁻¹).det := by
  let a := fun i => coeff i A
  let g := fun i => coeff i A⁻¹
  have a0 : a 0 = 1 := by simpa [a, coeff_zero_eq_constantCoeff_apply] using hA
  have g0 : g 0 = 1 := by simp [g, coeff_zero_eq_constantCoeff_apply, hA]
  have h := toe_hankel (a := a) g0 (fun m hm => by
    have hc := congrArg (coeff m) (PowerSeries.inv_mul_cancel A (by rw [hA]; decide))
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, coeff_one, if_neg (by omega)] at hc
    exact hc) n
  have e := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, toe_det _ a0, toe_det _ g0,
    one_mul, mul_one, reduced_det] at e
  exact e
end Cigler

namespace Cigler
open PowerSeries OMA.S_mo_286541

theorem identity (s n : ℕ) :
    (hankel (binomialMoment (s+1)) n).det =
      ((s+1 : ℕ) : ℚ)^n * (hankel (fussCatalan (s+1)) n).det := by
  have ha : binomialMoment (s+1) = fun i => coeff i (Bino s 0) := by
    funext i
    simp [binomialMoment, Bino]
  have hb : fussCatalan (s+1) = fun i => coeff i (Ran s 1) := funext fun i => (ran_one_coeff s i).symm
  rw [ha, hb, normalize_hankel _ (by simp [Bino]), normalize_hankel _ (by simp [Ran, Bino])]
  let M : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j => -coeff (i.val+j.val+2) (Ran s 1)⁻¹
  have e : (Matrix.of fun i j : Fin n => -coeff (i.val+j.val+2) (Bino s 0)⁻¹) =
      (s+1 : ℚ) • M := by
    ext i j
    simp only [Matrix.of_apply, reciprocal, map_sub, coeff_C_mul, coeff_C, Matrix.smul_apply,
      M, smul_eq_mul]
    simp
  rw [e, Matrix.det_smul, Fintype.card_fin, Nat.cast_add, Nat.cast_one]

end Cigler

theorem OMA.solution : type_of% @OMA.S_mo_286541.main := by
  intro k hk n
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact Cigler.identity s n
