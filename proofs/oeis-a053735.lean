import OMAStatements.S_oeis_a053735

-- Problem: A053735: Sum of digits of (n written in base 3).
-- Upstream: formal-conjectures statements/oeis-a053735.lean:0 (declaration OMA.S_oeis_a053735.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: a(n) = n % 3 + a(n / 3), hence by induction on m: a(3^m + j) = 1 + a(j) for j < 3^m
-- (adding 3^m to a number below 3^m puts one new digit 1 in front). The row starts are
-- 1 + 2 + 6 + ... + 2*3^(k-1) = 3^k. For the convergence take K = n + 1.

namespace FS5A053735

open OMA.S_oeis_a053735

theorem a_zero : a 0 = 0 := by
  simp [a]

theorem a_step (n : ℕ) : a n = n % 3 + a (n / 3) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp
  · unfold a
    rw [Nat.digits_def' (by norm_num : 1 < 3) h, List.sum_cons]

theorem a_one : a 1 = 1 := by
  have h := a_step 1
  have e1 : (1 : ℕ) / 3 = 0 := by norm_num
  have e2 : (1 : ℕ) % 3 = 1 := by norm_num
  rw [e1, e2, a_zero] at h
  omega

theorem a_shift (m : ℕ) : ∀ j : ℕ, j < 3 ^ m → a (3 ^ m + j) = 1 + a j := by
  induction m with
  | zero =>
    intro j hj
    have hj0 : j = 0 := by
      rw [pow_zero] at hj
      omega
    subst hj0
    have e : 3 ^ 0 + 0 = 1 := by norm_num
    rw [e]
    have h1 := a_one
    have h0 := a_zero
    omega
  | succ m ih =>
    intro j hj
    have hN := a_step (3 ^ (m + 1) + j)
    have e1 : (3 ^ (m + 1) + j) % 3 = j % 3 := by
      rw [pow_succ]
      omega
    have e2 : (3 ^ (m + 1) + j) / 3 = 3 ^ m + j / 3 := by
      rw [pow_succ]
      omega
    have hj' : j / 3 < 3 ^ m := by
      rw [pow_succ] at hj
      omega
    have hI := ih (j / 3) hj'
    have hj2 := a_step j
    rw [e1, e2, hI] at hN
    omega

theorem lt_pow3 (n : ℕ) : n < 3 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]
    omega

theorem rowStart_zero : rowStart 0 = 0 := by
  unfold rowStart
  rw [Finset.sum_range_zero]

theorem rowStart_succ (k : ℕ) : rowStart (k + 1) = 3 ^ k := by
  induction k with
  | zero =>
    unfold rowStart
    rw [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add]
    rfl
  | succ k ih =>
    unfold rowStart at ih ⊢
    rw [Finset.sum_range_succ, ih]
    show 3 ^ k + 2 * 3 ^ k = 3 ^ (k + 1)
    ring

end FS5A053735

open OMA.S_oeis_a053735 FS5A053735 in
theorem OMA.solution : type_of% @OMA.S_oeis_a053735.main := by
  refine ⟨?_, ?_, ?_⟩
  · unfold T
    rw [rowStart_zero, Nat.add_zero]
    exact a_zero
  · intro k
    refine ⟨rfl, ?_⟩
    intro i _
    unfold T
    rw [rowStart_succ]
  · intro n _
    refine ⟨n + 1, fun r hr => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
    have hlt : n < 3 ^ k :=
      calc n < 3 ^ n := lt_pow3 n
        _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    constructor
    · show n - 1 < 2 * 3 ^ k
      omega
    · unfold T A173523
      rw [rowStart_succ]
      exact a_shift k (n - 1) (by omega)
