import OMAStatements.S_oeis_a053827

-- Problem: A053827: Sum of digits of (n written in base 6).
-- Upstream: formal-conjectures statements/oeis-a053827.lean:0 (declaration OMA.S_oeis_a053827.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: a(n) = n % 6 + a(n / 6), hence by induction on m: a(6^m + j) = 1 + a(j) for j < 6^m
-- (adding 6^m to a number below 6^m puts one new digit 1 in front). Take K = n.

namespace H07A053827

open OMA.S_oeis_a053827

theorem a_zero : a 0 = 0 := by
  simp [a]

theorem a_step (n : ℕ) : a n = n % 6 + a (n / 6) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp
  · unfold a
    rw [Nat.digits_def' (by norm_num : 1 < 6) h, List.sum_cons]

theorem a_one : a 1 = 1 := by
  have h := a_step 1
  have e1 : (1 : ℕ) / 6 = 0 := by norm_num
  have e2 : (1 : ℕ) % 6 = 1 := by norm_num
  rw [e1, e2, a_zero] at h
  omega

theorem a_shift (m : ℕ) : ∀ j : ℕ, j < 6 ^ m → a (6 ^ m + j) = 1 + a j := by
  induction m with
  | zero =>
    intro j hj
    have hj0 : j = 0 := by
      rw [pow_zero] at hj
      omega
    subst hj0
    have e : 6 ^ 0 + 0 = 1 := by norm_num
    rw [e]
    have h1 := a_one
    have h0 := a_zero
    omega
  | succ m ih =>
    intro j hj
    have hN := a_step (6 ^ (m + 1) + j)
    have e1 : (6 ^ (m + 1) + j) % 6 = j % 6 := by
      rw [pow_succ]
      omega
    have e2 : (6 ^ (m + 1) + j) / 6 = 6 ^ m + j / 6 := by
      rw [pow_succ]
      omega
    have hj' : j / 6 < 6 ^ m := by
      rw [pow_succ] at hj
      omega
    have hI := ih (j / 6) hj'
    have hj2 := a_step j
    rw [e1, e2, hI] at hN
    omega

theorem lt_pow6 (n : ℕ) : n < 6 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]
    omega

end H07A053827

open OMA.S_oeis_a053827 H07A053827 in
theorem OMA.solution : type_of% @OMA.S_oeis_a053827.main := by
  intro n _
  refine ⟨n, fun k hk => ?_⟩
  have hlt : n < 6 ^ k :=
    calc n < 6 ^ n := lt_pow6 n
      _ ≤ 6 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  constructor
  · omega
  · unfold rowEntry A173526
    exact a_shift k (n - 1) (by omega)
