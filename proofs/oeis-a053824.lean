import OMAStatements.S_oeis_a053824

-- Problem: A053824: Sum of digits of (n written in base 5).
-- Upstream: formal-conjectures statements/oeis-a053824.lean:0 (declaration OMA.S_oeis_a053824.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: a(5*i + j) = a(i) + j for j < 5, hence by induction on k: a(5^k * m + r) = a(m) + a(r)
-- for r < 5^k. With m = 1: a(5^k + j) = 1 + a(j) for j < 5^k (convergence, K = n). Writing
-- j = 5^k * q + r with q < 4: a(5^k + j) = q + 1 + a(r) = 1 + a(j) = a(5^(k+1) + j).

namespace FS1A053824

open OMA.S_oeis_a053824

theorem a_zero : a 0 = 0 := by
  simp [a]

theorem a_step (n : ℕ) : a n = n % 5 + a (n / 5) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp
  · unfold a
    rw [Nat.digits_def' (by norm_num : 1 < 5) h, List.sum_cons]

theorem key (i j : ℕ) (hj : j < 5) : a (5 * i + j) = a i + j := by
  have h := a_step (5 * i + j)
  rw [show (5 * i + j) % 5 = j by omega, show (5 * i + j) / 5 = i by omega] at h
  omega

theorem a_small (q : ℕ) (hq : q < 5) : a q = q := by
  have h := key 0 q hq
  rw [Nat.mul_zero, Nat.zero_add, a_zero] at h
  omega

theorem a_mul_add (k : ℕ) : ∀ m r : ℕ, r < 5 ^ k → a (5 ^ k * m + r) = a m + a r := by
  induction k with
  | zero =>
    intro m r hr
    have hr0 : r = 0 := by
      rw [pow_zero] at hr
      omega
    subst hr0
    rw [pow_zero, Nat.one_mul, Nat.add_zero, a_zero, Nat.add_zero]
  | succ k ih =>
    intro m r hr
    have e0 : 5 ^ (k + 1) * m + r = 5 * (5 ^ k * m + r / 5) + r % 5 := by
      have h1 : 5 ^ (k + 1) * m = 5 * (5 ^ k * m) := by ring
      have h2 := Nat.div_add_mod r 5
      rw [h1]
      generalize 5 ^ k * m = X
      omega
    have hr' : r / 5 < 5 ^ k := by
      rw [pow_succ] at hr
      omega
    have hmod : r % 5 < 5 := Nat.mod_lt r (by norm_num)
    rw [e0, key (5 ^ k * m + r / 5) (r % 5) hmod, ih m (r / 5) hr', a_step r]
    omega

theorem a_shift (k j : ℕ) (hj : j < 5 ^ k) : a (5 ^ k + j) = 1 + a j := by
  have h := a_mul_add k 1 j hj
  rw [Nat.mul_one, a_small 1 (by norm_num)] at h
  exact h

theorem row_init (k j : ℕ) (hj : j < 4 * 5 ^ k) : a (5 ^ (k + 1) + j) = a (5 ^ k + j) := by
  have hpos : 0 < 5 ^ k := by positivity
  have hq : j / 5 ^ k < 4 := by
    rw [Nat.div_lt_iff_lt_mul hpos]
    exact hj
  have hr : j % 5 ^ k < 5 ^ k := Nat.mod_lt j hpos
  have hj1 : j < 5 ^ (k + 1) := by
    rw [pow_succ]
    omega
  have e1 : 5 ^ k + j = 5 ^ k * (j / 5 ^ k + 1) + j % 5 ^ k := by
    have h := Nat.div_add_mod j (5 ^ k)
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have h1 := a_mul_add k (j / 5 ^ k + 1) (j % 5 ^ k) hr
  have h2 := a_mul_add k (j / 5 ^ k) (j % 5 ^ k) hr
  rw [← e1, a_small (j / 5 ^ k + 1) (by omega)] at h1
  rw [Nat.div_add_mod, a_small (j / 5 ^ k) (by omega)] at h2
  rw [a_shift (k + 1) j hj1]
  omega

theorem lt_pow5 (n : ℕ) : n < 5 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]
    omega

end FS1A053824

open OMA.S_oeis_a053824 FS1A053824 in
theorem OMA.solution : type_of% @OMA.S_oeis_a053824.main := by
  refine ⟨?_, ?_⟩
  · intro k j hj
    unfold rowEntry
    exact row_init k j hj
  · intro n _
    refine ⟨n, fun k hk => ?_⟩
    have hlt : n < 5 ^ k :=
      calc n < 5 ^ n := lt_pow5 n
        _ ≤ 5 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    constructor
    · omega
    · unfold rowEntry A173525
      exact a_shift k (n - 1) (by omega)
