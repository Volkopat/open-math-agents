import OMAStatements.S_oeis_a188644

-- Problem: A188644: Array of (k^n + k^(-n))/2 where k = (sqrt(x^2-1) + x)^2 for integers x >= 1.
-- Upstream: formal-conjectures statements/oeis-a188644.lean:0 (declaration OMA.S_oeis_a188644.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: with s = sqrt(x^2+y), k = (s+x)^2 and k' = (s-x)^2 satisfy k*k' = (s^2-x^2)^2 = y^2 = 1
-- and k + k' = 2(s^2+x^2) = 2c with c = 2x^2+y an integer. So k^(-n) = k'^n, and
-- u(n) = (k^n + k'^n)/2 satisfies u(0) = 1, u(1) = c, u(n+2) = 2c u(n+1) - u(n): all integers.

open OMA.S_oeis_a188644 in
theorem OMA.solution : type_of% @OMA.S_oeis_a188644.main := by
  intro x y hx hy n
  have hx' : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hy2 : (y : ℝ) ^ 2 = 1 := by
    rcases hy with h | h
    · rw [h]
      norm_num
    · rw [h]
      norm_num
  have hy' : (-1 : ℝ) ≤ (y : ℝ) := by
    rcases hy with h | h
    · rw [h]
      norm_num
    · rw [h]
      norm_num
  have hrad : (0 : ℝ) ≤ (x : ℝ) ^ 2 + y := by nlinarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt ((x : ℝ) ^ 2 + y) := ⟨_, rfl⟩
  have hss : s ^ 2 = (x : ℝ) ^ 2 + y := by
    rw [hs]
    exact Real.sq_sqrt hrad
  have hfk : f x y = (s + x) ^ 2 := by
    rw [hs]
    rfl
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = (s + x) ^ 2 := ⟨_, rfl⟩
  obtain ⟨k', hk'⟩ : ∃ k' : ℝ, k' = (s - x) ^ 2 := ⟨_, rfl⟩
  have hprod : k * k' = 1 := by
    rw [hk, hk']
    linear_combination (s ^ 2 - (x : ℝ) ^ 2 + y) * hss + hy2
  have hsum : k + k' = 2 * (2 * (x : ℝ) ^ 2 + y) := by
    rw [hk, hk']
    linear_combination 2 * hss
  have hkinv : k ^ (-(n : ℤ)) = k' ^ n := by
    rw [zpow_neg, zpow_natCast]
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_pow, hprod, one_pow]
  have key : ∀ j : ℕ, ∃ a b : ℤ, (k ^ j + k' ^ j) / 2 = (a : ℝ) ∧
      (k ^ (j + 1) + k' ^ (j + 1)) / 2 = (b : ℝ) := by
    intro j
    induction j with
    | zero =>
      refine ⟨1, 2 * x ^ 2 + y, ?_, ?_⟩
      · norm_num
      · rw [zero_add, pow_one, pow_one, hsum]
        push_cast
        ring
    | succ j ih =>
      obtain ⟨a, b, ha, hb⟩ := ih
      refine ⟨b, 2 * (2 * x ^ 2 + y) * b - a, hb, ?_⟩
      push_cast
      linear_combination (1 / 2 : ℝ) * (k ^ (j + 1) + k' ^ (j + 1)) * hsum -
        (1 / 2 : ℝ) * (k ^ j + k' ^ j) * hprod + (2 * (2 * (x : ℝ) ^ 2 + y)) * hb - ha
  obtain ⟨a, b, ha, _⟩ := key n
  refine ⟨a, ?_⟩
  rw [hfk, ← hk, hkinv]
  exact ha
