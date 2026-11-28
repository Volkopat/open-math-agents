import OMAStatements.S_mo_235344

open Matrix OMA.S_mo_235344

namespace ReciprocalMinors

private def left : Matrix (Fin 6) (Fin 6) ℚ :=
  !![-4 / 3, -1 / 3, 5 / 3, 1 / 3, 1 / 3, 1 / 3;
    5 / 3, 2 / 3, -7 / 3, 1 / 3, 1 / 3, 1 / 3;
    -1 / 3, -1 / 3, 2 / 3, 1 / 3, 1 / 3, 1 / 3;
    1 / 3, 1 / 3, 1 / 3, -1 / 3, -1 / 3, 2 / 3;
    1 / 3, 1 / 3, 1 / 3, 2 / 3, -1 / 3, -1 / 3;
    1 / 3, 1 / 3, 1 / 3, -1 / 3, 2 / 3, -1 / 3]

private def right : Matrix (Fin 6) (Fin 6) ℚ :=
  !![-4 / 3, -1 / 3, 5 / 3, 1 / 3, 1 / 3, 1 / 3;
    5 / 3, 2 / 3, -7 / 3, 1 / 3, 1 / 3, 1 / 3;
    -1 / 3, -1 / 3, 2 / 3, 1 / 3, 1 / 3, 1 / 3;
    1 / 3, 1 / 3, 1 / 3, -1 / 3, 2 / 3, -1 / 3;
    1 / 3, 1 / 3, 1 / 3, -1 / 3, -1 / 3, 2 / 3;
    1 / 3, 1 / 3, 1 / 3, 2 / 3, -1 / 3, -1 / 3]

private def expandDet : {n : ℕ} → Matrix (Fin n) (Fin n) ℚ → ℚ
  | 0, _ => 1
  | n + 1, A => (List.ofFn fun j : Fin (n + 1) =>
      (-1) ^ (j : ℕ) * A 0 j * expandDet (A.submatrix Fin.succ j.succAbove)).sum

private theorem expandDet_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    expandDet A = A.det := by
  induction n with
  | zero => simp [expandDet]
  | succ n ih => rw [Matrix.det_succ_row_zero]; simp only [expandDet, List.sum_ofFn, ih]

private def select (s : Finset (Fin 6)) (i : Fin s.card) : Fin 6 :=
  s.sort[i]'(by rw [Finset.length_sort]; exact i.isLt)

private def listMat (M : Matrix (Fin 6) (Fin 6) ℚ) (l : List (Fin 6)) :
    Matrix (Fin l.length) (Fin l.length) ℚ :=
  fun i j => M l[i.val] l[j.val]

private def marked (f : Fin 6 → Bool) : List (Fin 6) :=
  (List.finRange 6).filter f

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
private theorem markedMinors :
    ∀ f : Fin 6 → Bool,
      expandDet (listMat left (marked f)) = expandDet (listMat right (marked f)) := by
  intro f
  have hf : f = ![f 0, f 1, f 2, f 3, f 4, f 5] := by
    funext i
    fin_cases i <;> rfl
  rw [hf]
  generalize f 0 = b0, f 1 = b1, f 2 = b2, f 3 = b3, f 4 = b4, f 5 = b5
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
    decide +kernel

private theorem minors (s : Finset (Fin 6)) :
    (left.submatrix (select s) (select s)).det =
      (right.submatrix (select s) (select s)).det := by
  have hs : marked (fun i => decide (i ∈ s)) = s.sort := by
    refine (((List.sortedLT_finRange 6).pairwise.filter _).sortedLT).eq_of_mem_iff (s.sortedLT_sort) ?_
    intro x
    simp
  have h := markedMinors (fun i => decide (i ∈ s))
  rw [hs, expandDet_eq, expandDet_eq] at h
  let e : Fin s.card ≃ Fin s.sort.length := finCongr (Finset.length_sort (s := s) (fun a b => a ≤ b)).symm
  have he (M : Matrix (Fin 6) (Fin 6) ℚ) :
      (listMat M s.sort).submatrix e e = M.submatrix (select s) (select s) := by
    ext i j
    rfl
  rw [← he, ← he, Matrix.det_submatrix_equiv_self, Matrix.det_submatrix_equiv_self]
  exact h

private theorem mulEntries :
    ∀ i j : Fin 6, (left * right) i j = (1 : Matrix (Fin 6) (Fin 6) ℚ) i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem nonzeroEntries : ∀ i j : Fin 6, left i j ≠ 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;> decide +kernel

private noncomputable def A := left.map (Rat.castHom ℝ)
private noncomputable def B := right.map (Rat.castHom ℝ)

private theorem mul_eq : A * B = 1 := by
  rw [A, B, ← Matrix.map_mul]
  have h : left * right = 1 := Matrix.ext mulEntries
  rw [h]
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

private theorem inverse_eq : A⁻¹ = B := Matrix.inv_eq_right_inv mul_eq

private theorem unit_det : IsUnit A.det := by
  have h : A.det * B.det = 1 := by rw [← Matrix.det_mul, mul_eq, Matrix.det_one]
  exact isUnit_iff_ne_zero.mpr (by intro h0; rw [h0, zero_mul] at h; exact zero_ne_one h)

private theorem irreducible : IrreducibleSupport A := by
  intro s hs hproper
  obtain ⟨i, hi⟩ := hs
  have hout : ∃ j, j ∉ s := by
    by_contra! hall
    exact hproper (Finset.eq_univ_of_forall hall)
  obtain ⟨j, hj⟩ := hout
  refine ⟨i, hi, j, hj, ?_⟩
  simpa [A] using nonzeroEntries i j

private theorem principal_eq (s : Finset (Fin 6)) :
    principalMinor A s = principalMinor A⁻¹ s := by
  rw [inverse_eq]
  have h := minors s
  unfold principalMinor A B
  change ((Rat.castHom ℝ).mapMatrix (left.submatrix (select s) (select s))).det =
    ((Rat.castHom ℝ).mapMatrix (right.submatrix (select s) (select s))).det
  rw [← RingHom.map_det, ← RingHom.map_det, h]

private theorem obstruction (d : Fin 6 → ℝ) (hd : ∀ i, d i ≠ 0) :
    ¬ (A * diagonal d = diagonal d * A⁻¹ ∨
        A.transpose * diagonal d = diagonal d * A⁻¹) := by
  rw [inverse_eq]
  rintro (h | h)
  · have h1 := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℝ => M 0 3) h
    have h2 := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℝ => M 3 4) h
    have h3 := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℝ => M 4 0) h
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1 h2 h3
    change ((1 / 3 : ℚ) : ℝ) * d 3 = d 0 * ((1 / 3 : ℚ) : ℝ) at h1
    change ((-1 / 3 : ℚ) : ℝ) * d 4 = d 3 * ((2 / 3 : ℚ) : ℝ) at h2
    change ((1 / 3 : ℚ) : ℝ) * d 0 = d 4 * ((1 / 3 : ℚ) : ℝ) at h3
    norm_num at h1 h2 h3
    exact hd 0 (by linarith)
  · have h1 := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℝ => M 0 1) h
    have h2 := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℝ => M 1 2) h
    have h3 := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℝ => M 2 0) h
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1 h2 h3
    change ((5 / 3 : ℚ) : ℝ) * d 1 = d 0 * ((-1 / 3 : ℚ) : ℝ) at h1
    change ((-1 / 3 : ℚ) : ℝ) * d 2 = d 1 * ((-7 / 3 : ℚ) : ℝ) at h2
    change ((5 / 3 : ℚ) : ℝ) * d 0 = d 2 * ((-1 / 3 : ℚ) : ℝ) at h3
    norm_num at h1 h2 h3
    exact hd 0 (by linarith)

theorem counterexample : ¬ (type_of% @OMA.S_mo_235344.main) := by
  intro h
  obtain ⟨d, hd, hsim⟩ := h 6 A unit_det irreducible principal_eq
  exact obstruction d hd hsim

end ReciprocalMinors

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_235344.main) :=
  ReciprocalMinors.counterexample