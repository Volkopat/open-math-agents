import OMAStatements.S_oeis_a083392
import Mathlib

namespace A083392

open OMA.S_oeis_a083392

/-- The matrix entry as a function of natural-number indices. -/
def G0 (r j : ℕ) : ℤ := (((r - j) + (j - r) + 1) / 2 : ℕ)

def G1 (r j : ℕ) : ℤ :=
  if r = 0 then (((j + 1) / 2 : ℕ) : ℤ) else
    if j < r then ((r - j : ℕ) : ℤ) else ((j - r + 1 : ℕ) : ℤ)

def G2 (r j : ℕ) : ℤ :=
  if r = 0 then (((j + 1) / 2 : ℕ) : ℤ) else
    if r = 1 then ((((1 - j) + (j - 1) + 1) / 2 : ℕ) : ℤ) else
      if j + 1 < r then 1 else if j + 1 = r then 0 else -1

def G3 (r j : ℕ) : ℤ :=
  if r = 0 then (((j + 1) / 2 : ℕ) : ℤ) else
    if r = 1 then ((((1 - j) + (j - 1) + 1) / 2 : ℕ) : ℤ) else
      if r = 2 then (if j < 1 then 1 else if j = 1 then 0 else -1) else
        if j + 2 = r ∨ j + 1 = r then 1 else 0

def G4 (r j : ℕ) : ℤ :=
  if r = 0 then (if j % 2 = 1 then (((j + 1) / 2 : ℕ) : ℤ) else 0) else
    if r = 1 then (if j % 2 = 0 then ((j / 2 + 1 : ℕ) : ℤ) else -1) else
      if r = 2 then (if j = 0 then 1 else if j % 2 = 1 then -1 else 0) else
        if j + 2 = r then 1 else 0

def G5 (p r j : ℕ) : ℤ :=
  if r = 0 then (if j = 0 then 1 else 0) else
    if r = p + 1 then (if j % 2 = 1 then (((j + 1) / 2 : ℕ) : ℤ) else 0) else
      if r = p + 2 then (if j % 2 = 0 then ((j / 2 + 1 : ℕ) : ℤ) else 0) else
        if j = r then 1 else 0

lemma t_apply (n : ℕ) (i j : Fin n) : toeplitz n i j = G0 i.val j.val := rfl

lemma stepA (p : ℕ) :
    (toeplitz (p+3)).det = (Matrix.of fun i j : Fin (p+3) => G1 i.val j.val).det := by
  apply Matrix.det_eq_of_forall_row_eq_smul_add_pred (fun _ => (-1 : ℤ))
  · intro j
    rw [t_apply, Matrix.of_apply]
    simp only [Fin.val_zero]
    unfold G0 G1
    omega
  · intro i j
    rw [t_apply, t_apply, Matrix.of_apply]
    simp only [Fin.val_succ, Fin.val_castSucc, neg_one_mul]
    unfold G0 G1
    omega

lemma stepB (p : ℕ) :
    (Matrix.of fun i j : Fin (p+3) => G1 i.val j.val).det =
      (Matrix.of fun i j : Fin (p+3) => G2 i.val j.val).det := by
  apply Matrix.det_eq_of_forall_row_eq_smul_add_pred (fun _ => (1 : ℤ))
  · intro j
    simp only [Matrix.of_apply, Fin.val_zero]
    unfold G1 G2
    omega
  · intro i j
    simp only [Matrix.of_apply, Fin.val_succ, Fin.val_castSucc, one_mul]
    unfold G1 G2
    omega

lemma stepC (p : ℕ) :
    (Matrix.of fun i j : Fin (p+3) => G2 i.val j.val).det =
      (Matrix.of fun i j : Fin (p+3) => G3 i.val j.val).det := by
  apply Matrix.det_eq_of_forall_row_eq_smul_add_pred
    (fun i : Fin (p+2) => if i.val < 2 then (0 : ℤ) else 1)
  · intro j
    simp only [Matrix.of_apply, Fin.val_zero]
    unfold G2 G3
    omega
  · intro i j
    simp only [Matrix.of_apply, Fin.val_succ, Fin.val_castSucc]
    by_cases h : i.val < 2
    · rw [if_pos h, zero_mul, add_zero]
      unfold G2 G3
      omega
    · rw [if_neg h, one_mul]
      unfold G2 G3
      omega

lemma stepD (p : ℕ) :
    (Matrix.of fun i j : Fin (p+3) => G3 i.val j.val).det =
      (Matrix.of fun i j : Fin (p+3) => G4 i.val j.val).det := by
  symm
  apply Matrix.det_eq_of_forall_col_eq_smul_add_pred (fun _ => (-1 : ℤ))
  · intro i
    simp only [Matrix.of_apply, Fin.val_zero]
    unfold G3 G4
    omega
  · intro i j
    simp only [Matrix.of_apply, Fin.val_succ, Fin.val_castSucc, neg_one_mul]
    unfold G3 G4
    omega

lemma rot_val (k : ℕ) (i : Fin (k+1)) :
    ((finRotate (k+1)) i).val = if i.val = k then 0 else i.val + 1 := by
  rw [coe_finRotate]
  by_cases h : i = Fin.last k
  · rw [if_pos h, if_pos (by rw [h]; rfl)]
  · have h' : i.val ≠ k := fun hh => h (Fin.ext hh)
    rw [if_neg h, if_neg h']

lemma rot2_val (p : ℕ) (i : Fin (p+3)) :
    ((finRotate (p+3)) ((finRotate (p+3)) i)).val =
      if i.val = p + 1 then 0 else if i.val = p + 2 then 1 else i.val + 2 := by
  have hi := i.isLt
  rw [rot_val (p+2), rot_val (p+2)]
  split_ifs <;> omega

lemma stepE (p : ℕ) :
    (Matrix.of fun i j : Fin (p+3) => G4 i.val j.val).det =
      (((Matrix.of fun i j : Fin (p+3) => G4 i.val j.val).submatrix (finRotate (p+3)) id).submatrix
        (finRotate (p+3)) id).det := by
  have h1 := Matrix.det_permute (finRotate (p+3))
    (Matrix.of fun i j : Fin (p+3) => G4 i.val j.val)
  have h2 := Matrix.det_permute (finRotate (p+3))
    ((Matrix.of fun i j : Fin (p+3) => G4 i.val j.val).submatrix (finRotate (p+3)) id)
  rw [h1] at h2
  rcases Int.units_eq_one_or (Equiv.Perm.sign (finRotate (p+3))) with h | h
  · rw [h] at h2
    simp only [Units.val_one, Int.cast_one, one_mul] at h2
    exact h2.symm
  · rw [h] at h2
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul,
      neg_neg] at h2
    exact h2.symm

lemma stepF (p : ℕ) :
    (((Matrix.of fun i j : Fin (p+3) => G4 i.val j.val).submatrix (finRotate (p+3)) id).submatrix
        (finRotate (p+3)) id).det =
      (Matrix.of fun i j : Fin (p+3) => G5 p i.val j.val).det := by
  rw [← Matrix.det_transpose (((Matrix.of fun i j : Fin (p+3) => G4 i.val j.val).submatrix
      (finRotate (p+3)) id).submatrix (finRotate (p+3)) id),
    ← Matrix.det_transpose (Matrix.of fun i j : Fin (p+3) => G5 p i.val j.val)]
  apply Matrix.det_eq_of_forall_row_eq_smul_add_const
    (fun j : Fin (p+3) => if j.val = 0 then (0 : ℤ) else if j.val % 2 = 1 then -1 else 0) 0
  · simp
  · intro j i
    simp only [Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.of_apply, id_eq,
      Fin.val_zero]
    have hs := rot2_val p i
    have hi := i.isLt
    have hj := j.isLt
    generalize ((finRotate (p+3)) ((finRotate (p+3)) i)).val = s at hs ⊢
    have hs' : (i.val = p + 1 ∧ s = 0) ∨ (i.val = p + 2 ∧ s = 1) ∨
        (i.val ≠ p + 1 ∧ i.val ≠ p + 2 ∧ s = i.val + 2) := by
      rw [hs]
      split_ifs <;> omega
    clear hs
    by_cases c0 : j.val = 0
    · rw [if_pos c0, zero_mul, add_zero]
      unfold G4 G5
      omega
    · rw [if_neg c0]
      by_cases c1 : j.val % 2 = 1
      · rw [if_pos c1, neg_one_mul]
        unfold G4 G5
        omega
      · rw [if_neg c1, zero_mul, add_zero]
        unfold G4 G5
        omega

lemma tri_even (p : ℕ) (hp : p % 2 = 0) :
    (Matrix.of fun i j : Fin (p+3) => G5 p i.val j.val).det =
      (((p + 2) / 2 : ℕ) : ℤ) * (((p + 2) / 2 + 1 : ℕ) : ℤ) := by
  have htri : (Matrix.of fun i j : Fin (p+3) => G5 p i.val j.val).IsLowerTriangular := by
    intro i j hij
    have hij' : i.val < j.val := hij
    have hj := j.isLt
    rw [Matrix.of_apply]
    unfold G5
    omega
  rw [Matrix.det_of_isLowerTriangular _ htri]
  simp only [Matrix.of_apply]
  rw [Fin.prod_univ_eq_prod_range (fun k => G5 p k k) (p+3), Finset.prod_range_succ,
    Finset.prod_range_succ]
  have h1 : ∀ k ∈ Finset.range (p+1), G5 p k k = 1 := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    unfold G5
    omega
  have e1 : G5 p (p+1) (p+1) = (((p + 2) / 2 : ℕ) : ℤ) := by
    unfold G5
    omega
  have e2 : G5 p (p+2) (p+2) = (((p + 2) / 2 + 1 : ℕ) : ℤ) := by
    unfold G5
    omega
  rw [Finset.prod_eq_one h1, one_mul, e1, e2]

lemma swap_val (p : ℕ) (i : Fin (p+3)) :
    (Equiv.swap (⟨p+1, by omega⟩ : Fin (p+3)) ⟨p+2, by omega⟩ i).val =
      if i.val = p + 1 then p + 2 else if i.val = p + 2 then p + 1 else i.val := by
  rw [Equiv.swap_apply_def]
  by_cases h1 : i = ⟨p+1, by omega⟩
  · rw [if_pos h1, if_pos (by rw [h1])]
  · have h1' : i.val ≠ p + 1 := fun hh => h1 (Fin.ext hh)
    rw [if_neg h1, if_neg h1']
    by_cases h2 : i = ⟨p+2, by omega⟩
    · rw [if_pos h2, if_pos (by rw [h2])]
    · have h2' : i.val ≠ p + 2 := fun hh => h2 (Fin.ext hh)
      rw [if_neg h2, if_neg h2']

lemma tri_odd (p : ℕ) (hp : p % 2 = 1) :
    (Matrix.of fun i j : Fin (p+3) => G5 p i.val j.val).det =
      -((((p + 1) / 2 + 1 : ℕ) : ℤ) * (((p + 3) / 2 : ℕ) : ℤ)) := by
  have hne : (⟨p+1, by omega⟩ : Fin (p+3)) ≠ ⟨p+2, by omega⟩ := by
    intro h
    have h2 := congrArg Fin.val h
    simp at h2
  have hperm := Matrix.det_permute (Equiv.swap (⟨p+1, by omega⟩ : Fin (p+3)) ⟨p+2, by omega⟩)
    (Matrix.of fun i j : Fin (p+3) => G5 p i.val j.val)
  rw [Equiv.Perm.sign_swap hne] at hperm
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul] at hperm
  have htri : ((Matrix.of fun i j : Fin (p+3) => G5 p i.val j.val).submatrix
      (Equiv.swap (⟨p+1, by omega⟩ : Fin (p+3)) ⟨p+2, by omega⟩) id).IsLowerTriangular := by
    intro i j hij
    have hij' : i.val < j.val := hij
    have hj := j.isLt
    rw [Matrix.submatrix_apply, Matrix.of_apply]
    have hs := swap_val p i
    generalize (Equiv.swap (⟨p+1, by omega⟩ : Fin (p+3)) ⟨p+2, by omega⟩ i).val = s at hs ⊢
    have hs' : (i.val = p + 1 ∧ s = p + 2) ∨ (i.val = p + 2 ∧ s = p + 1) ∨
        (i.val ≠ p + 1 ∧ i.val ≠ p + 2 ∧ s = i.val) := by
      rw [hs]
      split_ifs <;> omega
    clear hs
    simp only [id_eq]
    unfold G5
    omega
  have hdet := Matrix.det_of_isLowerTriangular _ htri
  simp only [Matrix.submatrix_apply, Matrix.of_apply, id_eq, swap_val] at hdet
  rw [Fin.prod_univ_eq_prod_range
    (fun k => G5 p (if k = p + 1 then p + 2 else if k = p + 2 then p + 1 else k) k) (p+3),
    Finset.prod_range_succ, Finset.prod_range_succ] at hdet
  have h1 : ∀ k ∈ Finset.range (p+1),
      G5 p (if k = p + 1 then p + 2 else if k = p + 2 then p + 1 else k) k = 1 := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    rw [if_neg (show ¬ k = p + 1 by omega), if_neg (show ¬ k = p + 2 by omega)]
    unfold G5
    omega
  have e1 : G5 p (if p + 1 = p + 1 then p + 2 else if p + 1 = p + 2 then p + 1 else p + 1)
      (p + 1) = (((p + 1) / 2 + 1 : ℕ) : ℤ) := by
    rw [if_pos rfl]
    unfold G5
    omega
  have e2 : G5 p (if p + 2 = p + 1 then p + 2 else if p + 2 = p + 2 then p + 1 else p + 2)
      (p + 2) = (((p + 3) / 2 : ℕ) : ℤ) := by
    rw [if_neg (show ¬ p + 2 = p + 1 by omega), if_pos rfl]
    unfold G5
    omega
  rw [Finset.prod_eq_one h1, one_mul, e1, e2] at hdet
  linarith

lemma a_succ (m : ℕ) :
    a (m + 1) = a m + (-1 : ℤ) ^ (m + 1) * (((m + 1) * (m + 1 + 1) / 2 : ℕ) : ℤ) := by
  unfold a
  rw [Finset.sum_range_succ]

lemma a_closed (k : ℕ) :
    a (2 * k) = (k : ℤ) * ((k : ℤ) + 1) ∧ a (2 * k + 1) = -(((k : ℤ) + 1) ^ 2) := by
  induction k with
  | zero => constructor <;> simp [a, Finset.sum_range_succ]
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have e1 : a (2 * (k + 1)) = ((k : ℤ) + 1) * ((k : ℤ) + 2) := by
      have hh : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
      rw [hh, a_succ, h2]
      have hev : (-1 : ℤ) ^ (2 * k + 1 + 1) = 1 := Even.neg_one_pow ⟨k + 1, by ring⟩
      have hd : (2 * k + 1 + 1) * (2 * k + 1 + 1 + 1) / 2 = (k + 1) * (2 * k + 3) := by
        have h3 : (2 * k + 1 + 1) * (2 * k + 1 + 1 + 1) = 2 * ((k + 1) * (2 * k + 3)) := by ring
        rw [h3, Nat.mul_div_cancel_left _ (by norm_num)]
      rw [hev, hd]
      push_cast
      ring
    have e2 : a (2 * (k + 1) + 1) = -(((k : ℤ) + 2) ^ 2) := by
      rw [a_succ, e1]
      have hodd : (-1 : ℤ) ^ (2 * (k + 1) + 1) = -1 := Odd.neg_one_pow ⟨k + 1, by ring⟩
      have hd : (2 * (k + 1) + 1) * (2 * (k + 1) + 1 + 1) / 2 = (2 * k + 3) * (k + 2) := by
        have h3 : (2 * (k + 1) + 1) * (2 * (k + 1) + 1 + 1) = 2 * ((2 * k + 3) * (k + 2)) := by
          ring
        rw [h3, Nat.mul_div_cancel_left _ (by norm_num)]
      rw [hodd, hd]
      push_cast
      ring
    refine ⟨?_, ?_⟩
    · rw [e1]
      push_cast
      ring
    · rw [e2]
      push_cast
      ring

end A083392

theorem OMA.solution : type_of% @OMA.S_oeis_a083392.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases m with _ | _ | p
  · show (OMA.S_oeis_a083392.toeplitz 1).det = OMA.S_oeis_a083392.a 0
    rw [Matrix.det_fin_one]
    simp [OMA.S_oeis_a083392.toeplitz, OMA.S_oeis_a083392.a]
  · show (OMA.S_oeis_a083392.toeplitz 2).det = OMA.S_oeis_a083392.a 1
    rw [Matrix.det_fin_two]
    simp [OMA.S_oeis_a083392.toeplitz, OMA.S_oeis_a083392.a, Finset.sum_range_succ]
  · show (OMA.S_oeis_a083392.toeplitz (p + 3)).det = OMA.S_oeis_a083392.a (p + 2)
    rw [A083392.stepA, A083392.stepB, A083392.stepC, A083392.stepD, A083392.stepE,
      A083392.stepF]
    rcases Nat.even_or_odd' p with ⟨k, rfl | rfl⟩
    · rw [A083392.tri_even (2 * k) (by omega)]
      have e : 2 * k + 2 = 2 * (k + 1) := by ring
      have e1 : (2 * k + 2) / 2 = k + 1 := by omega
      rw [e, (A083392.a_closed (k + 1)).1, ← e, e1]
      push_cast
      ring
    · rw [A083392.tri_odd (2 * k + 1) (by omega)]
      have e : 2 * k + 1 + 2 = 2 * (k + 1) + 1 := by ring
      have e1 : (2 * k + 1 + 1) / 2 + 1 = k + 2 := by omega
      have e2 : (2 * k + 1 + 3) / 2 = k + 2 := by omega
      rw [e, (A083392.a_closed (k + 1)).2, e1, e2]
      push_cast
      ring
