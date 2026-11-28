import OMAStatements.S_oeis_a053830

-- Problem: A053830: Sum of digits of (n written in base 9).
-- Upstream: formal-conjectures statements/oeis-a053830.lean:0 (declaration OMA.S_oeis_a053830.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: a(n) = n % 9 + a(n / 9), hence by induction on m: a(9^m + j) = 1 + a(j) for j < 9^m
-- (adding 9^m to a number below 9^m puts one new digit 1 in front). Take K = n.

namespace H07A053830

open OMA.S_oeis_a053830

theorem a_zero : a 0 = 0 := by
  simp [a]

theorem a_step (n : ℕ) : a n = n % 9 + a (n / 9) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp
  · unfold a
    rw [Nat.digits_def' (by norm_num : 1 < 9) h, List.sum_cons]

theorem a_one : a 1 = 1 := by
  have h := a_step 1
  have e1 : (1 : ℕ) / 9 = 0 := by norm_num
  have e2 : (1 : ℕ) % 9 = 1 := by norm_num
  rw [e1, e2, a_zero] at h
  omega

theorem a_shift (m : ℕ) : ∀ j : ℕ, j < 9 ^ m → a (9 ^ m + j) = 1 + a j := by
  induction m with
  | zero =>
    intro j hj
    have hj0 : j = 0 := by
      rw [pow_zero] at hj
      omega
    subst hj0
    have e : 9 ^ 0 + 0 = 1 := by norm_num
    rw [e]
    have h1 := a_one
    have h0 := a_zero
    omega
  | succ m ih =>
    intro j hj
    have hN := a_step (9 ^ (m + 1) + j)
    have e1 : (9 ^ (m + 1) + j) % 9 = j % 9 := by
      rw [pow_succ]
      omega
    have e2 : (9 ^ (m + 1) + j) / 9 = 9 ^ m + j / 9 := by
      rw [pow_succ]
      omega
    have hj' : j / 9 < 9 ^ m := by
      rw [pow_succ] at hj
      omega
    have hI := ih (j / 9) hj'
    have hj2 := a_step j
    rw [e1, e2, hI] at hN
    omega

theorem lt_pow9 (n : ℕ) : n < 9 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]
    omega

end H07A053830

open OMA.S_oeis_a053830 H07A053830 in
theorem OMA.solution : type_of% @OMA.S_oeis_a053830.main := by
  intro n _
  refine ⟨n, fun k hk => ?_⟩
  have hlt : n < 9 ^ k :=
    calc n < 9 ^ n := lt_pow9 n
      _ ≤ 9 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  constructor
  · omega
  · unfold rowEntry A173529
    exact a_shift k (n - 1) (by omega)
