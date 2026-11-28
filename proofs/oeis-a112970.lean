import OMAStatements.S_oeis_a112970

open OMA.S_oeis_a112970

private theorem odd_index (m : ℕ) : a (2 * m + 1) = a m := by
  cases m with
  | zero => change a 1 = a 0; simp only [a]
  | succ m =>
    have he : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by omega
    conv_lhs => rw [he, a]
    rw [if_pos (show ((2 * m + 1) + 2) % 2 = 1 by omega),
      show ((2 * m + 1) + 2) / 2 = m + 1 by omega]

private theorem even_index {m : ℕ} (hm : 1 ≤ m) :
    a (2 * m) = a m + if 2 ≤ m then a (m - 2) else 0 := by
  have he : 2 * m = (2 * m - 2) + 2 := by omega
  conv_lhs => rw [he, a]
  rw [if_neg (show ¬ ((2 * m - 2) + 2) % 2 = 1 by omega),
    show ((2 * m - 2) + 2) / 2 = m by omega]

private theorem before_multiple (b n : ℕ) (hb : 1 ≤ b) :
    a (2 ^ n * b - 1) = a (b - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 0 < 2 ^ n * b := Nat.mul_pos (by positivity) (by omega)
    rw [show 2 ^ (n + 1) * b - 1 = 2 * (2 ^ n * b - 1) + 1 by
      rw [pow_succ, show 2 ^ n * 2 * b = 2 * (2 ^ n * b) by ring]
      omega, odd_index, ih]

private theorem before_power (n : ℕ) : a (2 ^ n - 1) = 1 := by
  simpa only [mul_one, Nat.sub_self, a] using before_multiple 1 n (by decide)

private theorem before_power_step (n : ℕ) :
    a (2 ^ (n + 3) - 2) = 1 + a (2 ^ (n + 1) - 2) := by
  have hp : 0 < 2 ^ n := by positivity
  have e₁ : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
  have e₂ : 2 ^ (n + 2) = 2 ^ n * 4 := by rw [pow_add]; rfl
  have e₃ : 2 ^ (n + 3) = 2 ^ n * 8 := by rw [pow_add]; rfl
  have hm : 2 ≤ 2 ^ (n + 2) - 1 := by omega
  rw [show 2 ^ (n + 3) - 2 = 2 * (2 ^ (n + 2) - 1) by omega,
    even_index (show 1 ≤ 2 ^ (n + 2) - 1 by omega), if_pos hm, before_power,
    show 2 ^ (n + 2) - 1 - 2 = 2 * (2 ^ (n + 1) - 2) + 1 by omega, odd_index]

private theorem before_power_pair (n : ℕ) : a (2 ^ (n + 1) - 2) = n / 2 + 1 := by
  induction n using Nat.twoStepInduction with
  | zero => change a 0 = 1; simp only [a]
  | one => change a 2 = 1; norm_num [a]
  | more n ih _ =>
    rw [show n + 2 + 1 = n + 3 by omega, before_power_step, ih]
    omega

private theorem quarter_step (n : ℕ) :
    (n + 2) ^ 2 / 4 = (n + 1) ^ 2 / 4 + n / 2 + 1 := by
  let m := n / 2
  by_cases h : n % 2 = 0
  · have e : n = 2 * m := by dsimp [m]; omega
    rw [e, show (2 * m + 2) ^ 2 = 4 * (m * m + 2 * m + 1) by ring,
      show (2 * m + 1) ^ 2 = 4 * (m * m + m) + 1 by ring]
    omega
  · have e : n = 2 * m + 1 := by dsimp [m]; omega
    rw [e, show (2 * m + 1 + 2) ^ 2 = 4 * (m * m + 3 * m + 2) + 1 by ring,
      show (2 * m + 1 + 1) ^ 2 = 4 * (m * m + 2 * m + 1) by ring]
    omega

private theorem power_value (n : ℕ) : a (2 ^ n) = a033638 n := by
  cases n with
  | zero => change a 1 = 1; simp only [a]
  | succ n =>
    induction n with
    | zero => change a 2 = 1; norm_num [a]
    | succ n ih =>
      have hp : 2 ≤ 2 ^ (n + 1) := by
        have : 0 < 2 ^ n := by positivity
        rw [pow_succ]
        omega
      rw [show 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) by rw [pow_succ, Nat.mul_comm],
        even_index (show 1 ≤ 2 ^ (n + 1) by omega), if_pos hp, ih, before_power_pair]
      unfold a033638
      rw [quarter_step n]
      omega

theorem OMA.solution : type_of% @OMA.S_oeis_a112970.main := by
  intro n
  refine ⟨power_value n, ?_, before_power n, ?_⟩
  · rw [show 2 ^ (n + 1) + 1 = 2 * 2 ^ n + 1 by rw [pow_succ, Nat.mul_comm], odd_index,
      power_value]
  · rw [Nat.mul_comm, before_multiple 3 n (by decide)]
    change a 2 = 1
    norm_num [a]