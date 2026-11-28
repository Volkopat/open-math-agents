import OMAStatements.S_oeis_a319053

-- Credit: @oh-meh
open OMA.S_oeis_a319053 Matrix Finset

private def stepMatrix : Matrix (Fin 2) (Fin 2) ℤ := !![4,1;1,0]

private theorem normalized (q r : ℕ) (hr : r=1 ∨ r=2) :
    ∃ B : Matrix (Fin 2) (Fin 2) ℤ,
    M^(3*q+r) = (2^(3*q+r-1) : ℤ) • B ∧ ∀ i j, Odd (B i j) := by
  induction q with
  | zero =>
    rcases hr with rfl | rfl
    · refine ⟨M, by decide, ?_⟩
      intro i j
      fin_cases i <;> fin_cases j <;> norm_num [M, Int.odd_iff]
    · refine ⟨!![5,1;1,1], by decide, ?_⟩
      intro i j
      fin_cases i <;> fin_cases j <;> norm_num [Int.odd_iff]
  | succ q ih =>
    obtain ⟨B,hB,ho⟩ := ih
    refine ⟨stepMatrix * B, ?_, ?_⟩
    · rw [show 3*(q+1)+r = 3+(3*q+r) by omega, pow_add,
        show M^3=(8:ℤ) • stepMatrix by decide, hB, smul_mul_assoc, mul_smul_comm, smul_smul,
        show 3+(3*q+r)-1 = 3+(3*q+r-1) by omega, pow_add]
      norm_num
    · intro i j
      have h₀ := ho 0 j
      have h₁ := ho 1 j
      fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_two, stepMatrix, Int.odd_iff] at * <;> omega

private theorem valuation (t : ℕ) (x : ℤ) (hx : Odd x) :
    padicValInt 2 ((2:ℤ)^t*x) = t := by
  have hodd := Int.odd_iff.mp hx
  induction t with
  | zero =>
    simp only [pow_zero, one_mul, padicValInt]
    apply padicValNat.eq_zero_of_not_dvd
    intro h
    have hd : (2:ℤ) ∣ x := Int.natCast_dvd.mpr h
    omega
  | succ t ih =>
    have hn : (2:ℤ)^t*x ≠ 0 := mul_ne_zero (by positivity) (by omega)
    rw [pow_succ, mul_right_comm _ 2 x]
    exact (padicValInt_mul_eq_succ (p:=2) _ hn).trans (congrArg (·+1) ih)

theorem OMA.solution : type_of% @OMA.S_oeis_a319053.main := by
  intro n hn h3
  obtain ⟨B,hB,ho⟩ := normalized (n/3) (n%3) (by omega)
  rw [show 3*(n/3)+n%3=n by omega] at hB
  unfold a
  rw [hB]
  calc
    _ = univ.sup (fun _ : Fin 2 × Fin 2 => n-1) := by
      apply sup_congr rfl
      intro ij _
      exact valuation _ _ (ho ij.1 ij.2)
    _ = _ := sup_const univ_nonempty _
