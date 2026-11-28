import OMAStatements.S_oeis_a173528

-- Problem: A173528: a(n) = 1 + sum of digits of n-1 written in base 8.
-- Upstream: formal-conjectures statements/oeis-a173528.lean:0 (declaration OMA.S_oeis_a173528.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: s(n) = n % 8 + s(n / 8) for the base-8 digit sum s, hence by induction on m:
-- s(8^m + j) = 1 + s(j) for j < 8^m (adding 8^m to a number below 8^m puts one new digit 1 in
-- front). Take K = n.

namespace FS1A173528

open OMA.S_oeis_a173528

theorem s_zero : A053829 0 = 0 := by
  simp [A053829]

theorem s_step (n : ℕ) : A053829 n = n % 8 + A053829 (n / 8) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp
  · unfold A053829
    rw [Nat.digits_def' (by norm_num : 1 < 8) h, List.sum_cons]

theorem s_one : A053829 1 = 1 := by
  have h := s_step 1
  have e1 : (1 : ℕ) / 8 = 0 := by norm_num
  have e2 : (1 : ℕ) % 8 = 1 := by norm_num
  rw [e1, e2, s_zero] at h
  omega

theorem s_shift (m : ℕ) : ∀ j : ℕ, j < 8 ^ m → A053829 (8 ^ m + j) = 1 + A053829 j := by
  induction m with
  | zero =>
    intro j hj
    have hj0 : j = 0 := by
      rw [pow_zero] at hj
      omega
    subst hj0
    have e : 8 ^ 0 + 0 = 1 := by norm_num
    rw [e]
    have h1 := s_one
    have h0 := s_zero
    omega
  | succ m ih =>
    intro j hj
    have hN := s_step (8 ^ (m + 1) + j)
    have e1 : (8 ^ (m + 1) + j) % 8 = j % 8 := by
      rw [pow_succ]
      omega
    have e2 : (8 ^ (m + 1) + j) / 8 = 8 ^ m + j / 8 := by
      rw [pow_succ]
      omega
    have hj' : j / 8 < 8 ^ m := by
      rw [pow_succ] at hj
      omega
    have hI := ih (j / 8) hj'
    have hj2 := s_step j
    rw [e1, e2, hI] at hN
    omega

theorem lt_pow8 (n : ℕ) : n < 8 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]
    omega

end FS1A173528

open OMA.S_oeis_a173528 FS1A173528 in
theorem OMA.solution : type_of% @OMA.S_oeis_a173528.main := by
  intro n _
  refine ⟨n, fun k hk => ?_⟩
  have hlt : n < 8 ^ k :=
    calc n < 8 ^ n := lt_pow8 n
      _ ≤ 8 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  constructor
  · omega
  · unfold rowEntry a
    exact s_shift k (n - 1) (by omega)
