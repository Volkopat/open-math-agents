import OMAStatements.S_oeis_a007051

-- Credit: @oh-meh
open OMA.S_oeis_a007051

private theorem twice_a (n : ℕ) : 2 * a n = 3 ^ n + 1 := by
  obtain ⟨k, hk⟩ := (show Odd (3 : ℕ) by decide).pow (n := n)
  unfold a
  omega

theorem OMA.solution : type_of% @OMA.S_oeis_a007051.main := by
  intro s first step n hn
  induction n, hn using Nat.le_induction with
  | base => rw [first]; norm_num [a]
  | succ n hn ih =>
    have next := twice_a (n+1)
    rw [pow_succ] at next
    have current := twice_a n
    have hrec : (a (n+1) : ℚ) + 1 = 3 * (a n : ℚ) := by
      exact_mod_cast (show a (n+1) + 1 = 3 * a n by omega)
    have hpow : 3 ≤ 3 ^ n := by simpa using (Nat.pow_le_pow_right (by decide : 0 < 3) hn)
    have h : (2 : ℚ) ≤ a n := by exact_mod_cast (show 2 ≤ a n by omega)
    rw [step (n+1) (by omega), Nat.add_sub_cancel, ih]
    have den : 0 < (a n : ℚ) / ((a n : ℚ) - 1) + 2 := by
      have := div_pos (show (0 : ℚ) < a n by linarith) (show (0 : ℚ) < a n - 1 by linarith)
      linarith
    rw [show (a (n+1) : ℚ) = 3 * (a n : ℚ) - 1 by linarith]
    apply (div_eq_div_iff (ne_of_gt den) (by linarith)).2
    field_simp [show (a n : ℚ) - 1 ≠ 0 by linarith]
    ring
