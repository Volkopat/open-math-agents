import OMAStatements.S_oeis_a173524

-- Problem: A173524: a(n) = A053737(4^k+n-1) in the limit k->infinity, where k plays the role of a row index in A053737.
-- Upstream: formal-conjectures statements/oeis-a173524.lean:0 (declaration OMA.S_oeis_a173524.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: s(4*i + j) = s(i) + j for j < 4 (s = A053737), hence by induction on k:
-- s(4^k * m + r) = s(m) + s(r) for r < 4^k. So s(4^k + j) = 1 + s(j) for j < 3*4^k (write
-- j = 4^k * q + r with q < 3), a(n) = 1 + s(n - 1), and everything follows.

namespace FS1A173524

open OMA.S_oeis_a173524

theorem s_zero : A053737 0 = 0 := by
  simp [A053737]

theorem s_step (n : ℕ) : A053737 n = n % 4 + A053737 (n / 4) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp
  · unfold A053737
    rw [Nat.digits_def' (by norm_num : 1 < 4) h, List.sum_cons]

theorem key (i j : ℕ) (hj : j < 4) : A053737 (4 * i + j) = A053737 i + j := by
  have h := s_step (4 * i + j)
  rw [show (4 * i + j) % 4 = j by omega, show (4 * i + j) / 4 = i by omega] at h
  omega

theorem s_small (q : ℕ) (hq : q < 4) : A053737 q = q := by
  have h := key 0 q hq
  rw [Nat.mul_zero, Nat.zero_add, s_zero] at h
  omega

theorem s_mul_add (k : ℕ) :
    ∀ m r : ℕ, r < 4 ^ k → A053737 (4 ^ k * m + r) = A053737 m + A053737 r := by
  induction k with
  | zero =>
    intro m r hr
    have hr0 : r = 0 := by
      rw [pow_zero] at hr
      omega
    subst hr0
    rw [pow_zero, Nat.one_mul, Nat.add_zero, s_zero, Nat.add_zero]
  | succ k ih =>
    intro m r hr
    have e0 : 4 ^ (k + 1) * m + r = 4 * (4 ^ k * m + r / 4) + r % 4 := by
      have h1 : 4 ^ (k + 1) * m = 4 * (4 ^ k * m) := by ring
      have h2 := Nat.div_add_mod r 4
      rw [h1]
      generalize 4 ^ k * m = X
      omega
    have hr' : r / 4 < 4 ^ k := by
      rw [pow_succ] at hr
      omega
    have hmod : r % 4 < 4 := Nat.mod_lt r (by norm_num)
    rw [e0, key (4 ^ k * m + r / 4) (r % 4) hmod, ih m (r / 4) hr', s_step r]
    omega

theorem s_shift (k j : ℕ) (hj : j < 4 ^ k) : A053737 (4 ^ k + j) = 1 + A053737 j := by
  have h := s_mul_add k 1 j hj
  rw [Nat.mul_one, s_small 1 (by norm_num)] at h
  exact h

theorem s_row (k j : ℕ) (hj : j < 3 * 4 ^ k) : A053737 (4 ^ k + j) = 1 + A053737 j := by
  have hpos : 0 < 4 ^ k := by positivity
  have hq : j / 4 ^ k < 3 := by
    rw [Nat.div_lt_iff_lt_mul hpos]
    exact hj
  have hr : j % 4 ^ k < 4 ^ k := Nat.mod_lt j hpos
  have e1 : 4 ^ k + j = 4 ^ k * (j / 4 ^ k + 1) + j % 4 ^ k := by
    have h := Nat.div_add_mod j (4 ^ k)
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have h1 := s_mul_add k (j / 4 ^ k + 1) (j % 4 ^ k) hr
  have h2 := s_mul_add k (j / 4 ^ k) (j % 4 ^ k) hr
  rw [← e1, s_small (j / 4 ^ k + 1) (by omega)] at h1
  rw [Nat.div_add_mod, s_small (j / 4 ^ k) (by omega)] at h2
  omega

theorem lt_pow4 (n : ℕ) : n < 4 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]
    omega

theorem a_eq (n : ℕ) (hn : 1 ≤ n) : a n = 1 + A053737 (n - 1) := by
  have hlt := lt_pow4 n
  unfold a
  rw [show 4 ^ n + n - 1 = 4 ^ n + (n - 1) by omega]
  exact s_shift n (n - 1) (by omega)

end FS1A173524

open OMA.S_oeis_a173524 FS1A173524 in
theorem OMA.solution : type_of% @OMA.S_oeis_a173524.main := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    refine ⟨n, fun k hk => ?_⟩
    have hlt : n < 4 ^ k :=
      calc n < 4 ^ n := lt_pow4 n
        _ ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    rw [a_eq n hn, show 4 ^ k + n - 1 = 4 ^ k + (n - 1) by omega]
    exact s_shift k (n - 1) (by omega)
  · intro k j hj
    unfold rowEntry
    rw [a_eq (j + 1) (by omega), show j + 1 - 1 = j by omega]
    exact s_row k j hj
  · rw [a_eq 1 le_rfl, Nat.sub_self, s_zero, Nat.add_zero]
  · intro i j hj
    rw [a_eq (4 * i + j + 1) (by omega), a_eq (i + 1) (by omega),
      show 4 * i + j + 1 - 1 = 4 * i + j by omega, show i + 1 - 1 = i by omega, key i j hj]
    omega
