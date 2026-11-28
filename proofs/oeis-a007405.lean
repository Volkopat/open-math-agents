import OMAStatements.S_oeis_a007405

open Finset Matrix OMA.S_oeis_a007405

-- Fried's determinant identity for Irwin's matrix. Consecutive row differences
-- expose a Hessenberg matrix whose last row expansion gives the Dowling recurrence.
private def hessenberg (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if j.val = i.val + 1 then -2 else (i.val.choose j.val : ℤ) + if i = j then 1 else 0

private theorem hessenberg_castSucc (n : ℕ) (i j : Fin n) :
    hessenberg (n + 1) i.castSucc j.castSucc = hessenberg n i j := by
  simp [hessenberg]

private def lastMinor (n : ℕ) (j : Fin (n + 1)) : Matrix (Fin n) (Fin n) ℤ :=
  (hessenberg (n + 1)).submatrix Fin.castSucc j.succAbove

private theorem lastMinor_last (n : ℕ) : lastMinor n (Fin.last n) = hessenberg n := by
  ext i j
  simp [lastMinor, hessenberg_castSucc]

private theorem lastMinor_det (n : ℕ) (j : Fin (n + 1)) :
    (lastMinor n j).det = (-2 : ℤ) ^ (n - j.val) * (hessenberg j.val).det := by
  induction n with
  | zero =>
    have hj : j = Fin.last 0 := Fin.ext (by have := j.isLt; simp at *)
    subst j
    simp
  | succ n ih =>
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [lastMinor_last]
    · let A := lastMinor (n + 1) k.castSucc
      have hk : k.castSucc ≠ Fin.last (n + 1) := by simp
      have hentry (i : Fin (n + 1)) :
          A i (Fin.last n) = if i = Fin.last n then -2 else 0 := by
        simp only [A, lastMinor, submatrix_apply, Fin.succAbove_ne_last_last hk,
          hessenberg, Fin.val_last, Fin.val_castSucc]
        by_cases hi : i = Fin.last n
        · simp [hi]
        · have hil : i.val < n := by
            have hne : i.val ≠ n := fun h => hi (Fin.ext h)
            omega
          have hne2 : i.castSucc ≠ Fin.last (n + 1) := by simp
          simp [hi, hne2, show n ≠ i.val by omega,
            Nat.choose_eq_zero_of_lt (show i.val < n + 1 by omega)]
      have hminor : A.submatrix (Fin.last n).succAbove (Fin.last n).succAbove = lastMinor n k := by
        ext i l
        simp [A, lastMinor, hessenberg_castSucc]
      have hA : A.det = -2 * (lastMinor n k).det := by
        rw [Matrix.det_succ_column A (Fin.last n)]
        simp_rw [hentry]
        rw [sum_eq_single (Fin.last n)]
        · rw [if_pos rfl, hminor]
          simp [← two_mul, pow_mul]
        · intro b _ hb
          simp [hb]
        · simp
      change A.det = (-2 : ℤ) ^ ((n + 1) - k.val) * (hessenberg k.val).det
      rw [hA, ih k, show (n + 1) - k.val = (n - k.val) + 1 by omega, pow_succ]
      ring

private theorem hessenberg_recurrence (n : ℕ) :
    (hessenberg (n + 1)).det = (hessenberg n).det +
      ∑ k : Fin (n + 1), (n.choose k.val : ℤ) * 2 ^ k.val * (hessenberg (n - k.val)).det := by
  rw [Matrix.det_succ_row _ (Fin.last n)]
  have hentry (j : Fin (n + 1)) :
      hessenberg (n + 1) (Fin.last n) j = (n.choose j.val : ℤ) + if j = Fin.last n then 1 else 0 := by
    simp [hessenberg, show j.val ≠ n + 1 by omega, eq_comm]
  simp only [Fin.succAbove_last, Fin.val_last]
  change (∑ j : Fin (n + 1), (-1 : ℤ) ^ (n + j.val) *
    hessenberg (n + 1) (Fin.last n) j * (lastMinor n j).det) = _
  simp_rw [lastMinor_det, hentry]
  have hsign (j : Fin (n + 1)) :
      (-1 : ℤ) ^ (n + j.val) * (-2 : ℤ) ^ (n - j.val) = 2 ^ (n - j.val) := by
    rw [show (-2 : ℤ) = (-1) * 2 by decide, mul_pow, ← mul_assoc, ← pow_add,
      show n + j.val + (n - j.val) = 2 * n by omega, pow_mul]
    norm_num
  have hterm (j : Fin (n + 1)) :
      (-1 : ℤ) ^ (n + j.val) * ((n.choose j.val : ℤ) + if j = Fin.last n then 1 else 0) *
          ((-2 : ℤ) ^ (n - j.val) * (hessenberg j.val).det) =
      (n.choose j.val : ℤ) * 2 ^ (n - j.val) * (hessenberg j.val).det +
        if j = Fin.last n then (hessenberg n).det else 0 := by
    calc
      _ = ((n.choose j.val : ℤ) + if j = Fin.last n then 1 else 0) *
          ((-1 : ℤ) ^ (n + j.val) * (-2 : ℤ) ^ (n - j.val)) * (hessenberg j.val).det := by ring
      _ = _ := by
        rw [hsign]
        by_cases hj : j = Fin.last n
        · subst j
          simp [two_mul]
        · simp [hj]
  simp_rw [hterm, sum_add_distrib]
  simp only [sum_ite_eq', mem_univ, if_true]
  rw [add_comm]
  congr 1
  rw [← Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (n + 1)))
    (fun j => (n.choose j.val : ℤ) * 2 ^ (n - j.val) * (hessenberg j.val).det)]
  refine sum_congr rfl fun k _ => ?_
  change (n.choose (Fin.rev k).val : ℤ) * 2 ^ (n - (Fin.rev k).val) *
      (hessenberg (Fin.rev k).val).det = _
  rw [show (Fin.rev k).val = n - k.val by simp [Fin.val_rev],
    Nat.choose_symm (show k.val ≤ n by omega), show n - (n - k.val) = k.val by omega]

private theorem dowling_det (n : ℕ) : a n = (hessenberg n).det := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => rw [a]; simp
    | succ n =>
      rw [a, hessenberg_recurrence, ih n (by omega)]
      congr 1
      refine sum_congr rfl fun k _ => ?_
      rw [ih (n - k.val) (by omega)]

private def pascalMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if i.val + 1 < j.val then 1 else if i.val + 1 = j.val then -1 else (i.val.choose j.val : ℤ)

private theorem pascal_reindex (n : ℕ) :
    pascalMatrix n = Matrix.reindex Fin.revPerm Fin.revPerm (binomialMatrix n)ᵀ := by
  ext i j
  change pascalMatrix n i j = binomialMatrix n (Fin.rev j) (Fin.rev i)
  simp only [pascalMatrix, binomialMatrix, Fin.val_rev]
  have hlt : n - (j.val + 1) + 1 < n - (i.val + 1) ↔ i.val + 1 < j.val := by omega
  have heq : n - (j.val + 1) + 1 = n - (i.val + 1) ↔ i.val + 1 = j.val := by omega
  simp only [hlt, heq]
  split
  · rfl
  split
  · rfl
  next hi hj =>
    rw [show n - 1 - (n - (i.val + 1)) = i.val by omega,
      show n - (j.val + 1) - (n - (i.val + 1)) = i.val - j.val by omega,
      Nat.choose_symm (show j.val ≤ i.val by omega)]

private def rowDifference (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => (if i = j then 1 else 0) - if j.val + 1 = i.val then 1 else 0

private theorem rowDifference_det (n : ℕ) : (rowDifference n).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [rowDifference]
  · intro i j hij
    have h : i.val < j.val := hij
    simp [rowDifference, show i ≠ j by intro he; subst j; omega,
      show j.val + 1 ≠ i.val by omega]

private theorem pascal_diff_zero (n : ℕ) (j : Fin (n + 1)) :
    (rowDifference (n + 1) * pascalMatrix (n + 1)) 0 j = pascalMatrix (n + 1) 0 j := by
  simp [Matrix.mul_apply, rowDifference, ite_mul]

private theorem pascal_diff_succ (n : ℕ) (i : Fin n) (j : Fin (n + 1)) :
    (rowDifference (n + 1) * pascalMatrix (n + 1)) i.succ j =
      pascalMatrix (n + 1) i.succ j - pascalMatrix (n + 1) i.castSucc j := by
  have h (k : Fin (n + 1)) : k.val + 1 = i.succ.val ↔ k = i.castSucc := by
    simp [Fin.ext_iff]
  simp_rw [Matrix.mul_apply, rowDifference, sub_mul, sum_sub_distrib, ite_mul, one_mul, zero_mul, h]
  simp

private theorem pascal_diff_entries (n : ℕ) (i j : Fin n) :
    (rowDifference (n + 1) * pascalMatrix (n + 1)) i.succ j.succ = hessenberg n i j := by
  rw [pascal_diff_succ]
  simp only [pascalMatrix, hessenberg, Fin.val_succ, Fin.val_castSucc]
  rcases lt_trichotomy j.val i.val with h | h | h
  · have hj : j.val ≠ i.val + 1 := by omega
    have hij : i ≠ j := fun e => by subst j; omega
    simp only [if_neg (show ¬ i.val + 1 + 1 < j.val + 1 by omega),
      if_neg (show i.val + 1 + 1 ≠ j.val + 1 by omega),
      if_neg (show ¬ i.val + 1 < j.val + 1 by omega),
      if_neg (show i.val + 1 ≠ j.val + 1 by omega), if_neg hj, if_neg hij, add_zero]
    rw [Nat.choose_succ_succ, Nat.cast_add]
    ring
  · have hij : i = j := Fin.ext h.symm
    subst j
    simp
  · by_cases he : j.val = i.val + 1
    · simp [he]
    · have hij : i ≠ j := fun e => by subst j; omega
      simp [he, hij, Nat.choose_eq_zero_of_lt h, show i.val + 1 + 1 < j.val + 1 by omega,
        show i.val + 1 < j.val + 1 by omega]

private theorem det_pascal_succ (n : ℕ) : (pascalMatrix (n + 1)).det = (hessenberg n).det := by
  let D := rowDifference (n + 1) * pascalMatrix (n + 1)
  have hD : D.det = (pascalMatrix (n + 1)).det := by
    simp [D, Matrix.det_mul, rowDifference_det]
  have hentry (i : Fin (n + 1)) : D i 0 = if i = 0 then 1 else 0 := by
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [D, pascal_diff_zero, pascalMatrix]
    · simp [D, pascal_diff_succ, pascalMatrix]
  have hsub : D.submatrix Fin.succ Fin.succ = hessenberg n := by
    ext i j
    exact pascal_diff_entries n i j
  rw [← hD, Matrix.det_succ_column D 0]
  simp_rw [hentry]
  rw [sum_eq_single (0 : Fin (n + 1))]
  · simp [hsub]
  · intro b _ hb
    simp [hb]
  · simp

theorem OMA.solution : type_of% @OMA.S_oeis_a007405.main := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [Nat.succ_sub_one, dowling_det, ← det_pascal_succ, pascal_reindex,
    Matrix.det_reindex_self, Matrix.det_transpose]
