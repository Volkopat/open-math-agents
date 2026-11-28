import OMAStatements.S_oeis_a001653

open OMA.S_oeis_a001653

private theorem recurrence_preserves (n : ℕ) :
    a n ^ 2 - 6 * a n * a (n + 1) + a (n + 1) ^ 2 = -4 := by
  induction n with
  | zero => decide
  | succ n ih =>
    change a (n + 1) ^ 2 - 6 * a (n + 1) * a (n + 2) + a (n + 2) ^ 2 = -4
    rw [a]
    calc
      _ = a n ^ 2 - 6 * a n * a (n + 1) + a (n + 1) ^ 2 := by ring
      _ = -4 := ih

private theorem classify (N : ℕ) :
    ∀ x y : ℤ, x.toNat = N → 0 < x → x < y →
      x ^ 2 - 6 * x * y + y ^ 2 = -4 →
      ∃ j : ℕ, x = a j ∧ y = a (j + 1) := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro x y hN hx hxy hEq
    by_cases hbase : x = 1
    · subst x
      have hf : (y - 1) * (y - 5) = 0 := by nlinarith
      rcases mul_eq_zero.mp hf with h | h
      · omega
      · exact ⟨0, rfl, by change y = 5; omega⟩
    · let z := 6 * x - y
      have hy : 0 < y := lt_trans hx hxy
      have hz : 0 < z := by
        by_contra! h
        have hprod := mul_nonpos_of_nonneg_of_nonpos hy.le h
        dsimp [z] at hprod
        nlinarith [sq_nonneg x]
      have hy5 : 5 * x < y := by
        by_contra! h
        have hprod := mul_nonneg (sub_nonneg.mpr hxy.le) (sub_nonneg.mpr h)
        have hxsq := mul_nonneg (show 0 ≤ x - 2 by omega) (show 0 ≤ x + 2 by omega)
        nlinarith
      have hzx : z < x := by dsimp [z]; omega
      have hZ : z.toNat < N := by omega
      have hEq' : z ^ 2 - 6 * z * x + x ^ 2 = -4 := by
        calc
          _ = x ^ 2 - 6 * x * y + y ^ 2 := by dsimp [z]; ring
          _ = -4 := hEq
      obtain ⟨j, hj, hj'⟩ := ih z.toNat hZ z x rfl hz hzx hEq'
      refine ⟨j + 1, hj', ?_⟩
      change y = a (j + 2)
      rw [a, ← hj', ← hj]
      dsimp [z]
      ring

theorem OMA.solution : type_of% @OMA.S_oeis_a001653.main := by
  intro x y hx hxy
  constructor
  · exact classify x.toNat x y rfl hx hxy
  · rintro ⟨n, rfl, rfl⟩
    exact recurrence_preserves n
