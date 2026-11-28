import OMAStatements.S_oeis_a108299

/-!
Credited port of @connoranderson's complete public proof, linked from merged statement
PR #21380 and desk DONE note #95825, pinned at:
https://github.com/connoranderson/open-math-agents/blob/6b0671f642ffcaba1fe78aa83ca9aaedda367956/proofs/oeis-a108299.lean
The mathematical source is retained unchanged; this is integration of prior work,
not a claim of a new mathematical discovery. The original matrix, coefficient,
and cosine-root conjecture is L. Edson Jeffery's (OEIS A108299, March 12, 2011).
-/

/-! The two-term determinant recurrence gives both Pascal’s rule for the
coefficients and a sine evaluation at twice a cosine. -/

namespace OMA.S_oeis_a108299
open Polynomial Matrix Finset
open scoped Polynomial

private noncomputable abbrev H (n : ℕ) := (jeffery n).charmatrix
private noncomputable abbrev P (n : ℕ) := (jeffery n).charpoly

private lemma succession (n : ℕ) (i j : Fin n) : H (n+1) i.succ j.succ=H n i j := by
  simp [H,charmatrix_apply,Matrix.diagonal_apply,jeffery,Fin.succ_inj]

private lemma first_diag (n : ℕ) : H (n+2) 0 0=X := by simp [H,charmatrix_apply_eq,jeffery]
private lemma first_left (n : ℕ) : H (n+2) 1 0= -1 := by
  unfold H
  rw [charmatrix_apply_ne _ _ _ (by simp)]
  simp [jeffery]
private lemma first_right (n : ℕ) : H (n+2) 0 1= -1 := by
  unfold H
  rw [charmatrix_apply_ne _ _ _ (by simp)]
  simp [jeffery]
private lemma first_col (n : ℕ) (i : Fin n) : H (n+2) i.succ.succ 0 = 0 := by
  unfold H
  rw [charmatrix_apply_ne _ _ _ (Fin.succ_ne_zero _)]
  simp [jeffery]
private lemma first_row (n : ℕ) (i : Fin n) : H (n+2) 0 i.succ.succ = 0 := by
  unfold H
  rw [charmatrix_apply_ne _ _ _ (Fin.succ_ne_zero _).symm]
  simp [jeffery]

private lemma trailing (n : ℕ) : (H (n+1)).submatrix Fin.succ Fin.succ=H n := by
  ext i j : 1
  exact succession n i j

private lemma minor_det (n : ℕ) :
    ((H (n+2)).submatrix Fin.succ (1:Fin (n+2)).succAbove).det = -P n := by
  let M := (H (n+2)).submatrix Fin.succ (1:Fin (n+2)).succAbove
  change M.det = -P n
  have e0 : M 0 0= -1 := first_left n
  have eS (i : Fin n) : M i.succ 0=0 := first_col n i
  have tail : M.submatrix Fin.succ Fin.succ = H n := by
    ext i j : 1
    change H (n+2) i.succ.succ ((1:Fin (n+2)).succAbove j.succ) = H n i j
    rw [show (1:Fin (n+2))=(0:Fin (n+1)).succ by rfl,Fin.succ_succAbove_succ,Fin.zero_succAbove]
    rw [succession,succession]
  rw [det_succ_column_zero,Fin.sum_univ_succ]
  simp [e0,eS,tail,P,Matrix.charpoly]

/-- Expand the first row and then the first column of its off-diagonal minor. -/
private lemma recP (n : ℕ) : P (n+2)=X*P (n+1)-P n := by
  change (H (n+2)).det=_
  rw [det_succ_row_zero,Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [Fin.val_zero,pow_zero,one_mul,first_diag,
    Fin.succ_zero_eq_one,Fin.val_one, pow_one,first_right,neg_mul_neg,one_mul,minor_det,
    first_row,mul_zero,zero_mul,sum_const_zero,add_zero]
  rw [show (0 : Fin (n+2)).succAbove = Fin.succ by funext i; exact Fin.zero_succAbove i,trailing]
  rfl

private lemma p0 : P 0=1 := by simp [P,Matrix.charpoly]
private lemma p1 : P 1=X-1 := by simp [P,Matrix.charpoly,Matrix.det_unique,jeffery]

private lemma constant_rec (n : ℕ) : (P (n+2)).coeff 0 = -(P n).coeff 0 := by
  rw [recP]
  simp
private lemma positive_rec (n m : ℕ) :
    (P (n+2)).coeff (m+1) = (P (n+1)).coeff m - (P n).coeff (m+1) := by
  rw [recP]
  simp

/-- The parity parameter t gives the even and odd coefficient offsets together. -/
private lemma coefficients (m a t : ℕ) (ht : t ≤ 1) :
    (P (m+2*a+t)).coeff m = (-1:ℝ)^(a+t)*Nat.choose (m+a) a := by
  induction m generalizing a with
  | zero =>
    simp only [Nat.zero_add,Nat.choose_self,Nat.cast_one,mul_one]
    induction a with
    | zero =>
      interval_cases t <;> simp [p1]
    | succ a ih =>
      rw [show 2*(a+1)+t=(2*a+t)+2 by omega,constant_rec,ih,
        show a+1+t=(a+t)+1 by omega,pow_succ]
      ring
  | succ m ihm =>
    induction a with
    | zero =>
      simp only [Nat.mul_zero,Nat.add_zero,Nat.zero_add,Nat.choose_zero_right,Nat.cast_one,mul_one]
      interval_cases t
      · simpa using (jeffery (m+1)).charpoly_monic.coeff_natDegree
      · rw [positive_rec]
        have hs := ihm 0
        have hn : (P m).coeff (m+1) = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by simp [P])
        simpa [hn] using hs
    | succ a iha =>
      rw [show m+1+2*(a+1)+t=(m+1+2*a+t)+2 by omega,positive_rec,
        show m+1+2*a+t+1=m+2*(a+1)+t by omega,ihm (a+1),iha,
        show m+1+(a+1)=(m+(a+1))+1 by omega,Nat.choose_succ_succ,Nat.cast_add,
        show m+1+a=m+(a+1) by omega,show a+1+t=(a+t)+1 by omega,pow_succ]
      ring

private theorem row_coefficient (n k : ℕ) (hk : k ≤ n) : (P n).coeff (n-k)=rowEntry n k := by
  have h := coefficients (n-k) (k/2) (k%2) (by omega)
  rw [show n-k+2*(k/2)+k%2=n by omega,show k/2+k%2=(k+1)/2 by omega,
    show n-k+k/2=n-(k+1)/2 by omega] at h
  unfold rowEntry
  push_cast
  rw [h]
  ring

private lemma sin_recurrence (n : ℕ) (θ : ℝ) :
    Real.sin (((n:ℝ)+2)*θ) + Real.sin ((n:ℝ)*θ) =
      2*Real.cos θ*Real.sin (((n:ℝ)+1)*θ) := by
  rw [show ((n:ℝ)+2)*θ=((n:ℝ)+1)*θ+θ by ring,
    show (n:ℝ)*θ=((n:ℝ)+1)*θ-θ by ring,Real.sin_add,Real.sin_sub]
  ring

private lemma sine_eval (n : ℕ) (θ : ℝ) :
    (P n).eval (2*Real.cos θ)*Real.sin θ =
      Real.sin (((n:ℝ)+1)*θ)-Real.sin ((n:ℝ)*θ) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => norm_num [p1,Real.sin_two_mul]; ring
  | more n h0 h1 =>
    rw [recP,eval_sub,eval_mul,eval_X]
    push_cast at h1 ⊢
    have u := sin_recurrence n θ
    have v := sin_recurrence (n+1) θ
    push_cast at v
    ring_nf at u v h0 h1 ⊢
    linear_combination 2*Real.cos θ*h1-h0+u-v

private noncomputable def angle (n : ℕ) (j : Fin n) : ℝ :=
  ((2:ℝ)*j.val+1)*Real.pi/(2*n+1)

private lemma angle_bounds (n : ℕ) (j : Fin n) : 0 < angle n j ∧ angle n j < Real.pi := by
  have h : (j.val:ℝ) < n := by exact_mod_cast j.isLt
  unfold angle
  constructor
  · positivity
  · apply (div_lt_iff₀ (by positivity)).2
    nlinarith [mul_pos (sub_pos.mpr h) Real.pi_pos]

private lemma isRoot_value (n : ℕ) (j : Fin n) : (P n).IsRoot (rootValue n j) := by
  let θ := angle n j
  have nonzero := (Real.sin_pos_of_pos_of_lt_pi (angle_bounds n j).1 (angle_bounds n j).2).ne'
  have hs : ((n:ℝ)+1)*θ = (Real.pi-(n:ℝ)*θ)+(j.val:ℝ)*(2*Real.pi) := by
    dsimp [θ,angle]
    field_simp
    ring
  have h := sine_eval n θ
  rw [hs,Real.sin_add_nat_mul_two_pi,Real.sin_pi_sub,sub_self] at h
  exact (mul_eq_zero.mp h).resolve_right nonzero

private lemma value_injective (n : ℕ) : Function.Injective (rootValue n) := by
  apply StrictAnti.injective
  intro i j hij
  have h : (i.val:ℝ) < j.val := by exact_mod_cast hij
  have ha : angle n i < angle n j := by
    apply (div_lt_div_iff_of_pos_right (by positivity)).2
    apply mul_lt_mul_of_pos_right _ Real.pi_pos
    linarith
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (angle_bounds n i).1.le (angle_bounds n j).2.le ha
  change 2*Real.cos (angle n j) < 2*Real.cos (angle n i)
  linarith

private theorem root_characterization (n : ℕ) (t : ℝ) :
    (P n).IsRoot t ↔ ∃ j : Fin n, t=rootValue n j := by
  classical
  let s := Finset.univ.image (rootValue n)
  have hP : P n ≠ 0 := (jeffery n).charpoly_monic.ne_zero
  have hsub : s ⊆ (P n).roots.toFinset := by
    intro x hx
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP).mpr (isRoot_value n j))
  have hc : s.card = n := by simp [s,Finset.card_image_of_injective _ (value_injective n)]
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    rw [hc]
    calc
      _ ≤ (P n).roots.card := Multiset.toFinset_card_le _
      _ ≤ (P n).natDegree := (P n).card_roots'
      _ = n := by simp [P])
  constructor
  · intro ht
    have ht' : t ∈ (P n).roots.toFinset := Multiset.mem_toFinset.mpr ((mem_roots hP).mpr ht)
    rw [← heq] at ht'
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp ht'
    exact ⟨j,hj.symm⟩
  · rintro ⟨j,rfl⟩
    exact isRoot_value n j

end OMA.S_oeis_a108299

open OMA.S_oeis_a108299 in
theorem OMA.solution : type_of% @OMA.S_oeis_a108299.main := by
  intro n _
  exact ⟨row_coefficient n, root_characterization n⟩
