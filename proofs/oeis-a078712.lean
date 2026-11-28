import OMAStatements.S_oeis_a078712

open Matrix OMA.S_oeis_a078712 in
theorem OMA.solution : type_of% @OMA.S_oeis_a078712.main := by
  intro p hp
  have := Fact.mk hp
  let M : Matrix (Fin 3) (Fin 3) ℤ := !![0, 0, 1; 1, 0, 0; 0, 1, -1]
  have c : M ^ 3 = -(M ^ 2) + 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M, pow_succ, mul_apply, Fin.sum_univ_three]
  have e (n : ℕ) : a n = -trace (M ^ n) := by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    match n, ih with
    | 0, _ | 1, _ | 2, _ => simp [a, M, trace, Fin.sum_univ_three, pow_two]
    | n + 3, ih => simp [a, ih, pow_add, c, mul_add, trace_add]; abel
  have m : (M ^ p).map (Int.cast : ℤ → ZMod p) = M.map Int.cast ^ p := Matrix.map_pow M (Int.castRingHom (ZMod p)) p
  rw [← ZMod.intCast_eq_intCast_iff, e, Int.cast_neg, show ((trace (M ^ p) : ℤ) : ZMod p) = trace ((M ^ p).map Int.cast) by simp [trace],
    m, ZMod.trace_pow_card, ZMod.pow_card]
  simp [trace, M, Fin.sum_univ_three]
