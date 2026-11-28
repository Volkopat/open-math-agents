import OMAStatements.S_oeis_a188645

open OMA.S_oeis_a188645 in
/-- With `s = sqrt(x^2+y)` and `L = (s-x)^2` we get `k * L = y^2 = 1` and
`k + L = 2(2x^2+y)`, so `T n = (k^n + L^n)/2` satisfies `T (n+2) = 2(2x^2+y) T (n+1) - T n`
with `T 0 = 1`, `T 1 = 2x^2+y`. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a188645.main := by
  intro x y hx hy n
  set s := Real.sqrt ((x : ℝ) ^ 2 + y) with hs
  have hx' : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hy2 : (y : ℝ) ^ 2 = 1 := by rcases hy with rfl | rfl <;> norm_num
  have hnn : 0 ≤ (x : ℝ) ^ 2 + y := by
    rcases hy with rfl | rfl <;> push_cast <;> nlinarith
  have hss : s ^ 2 = (x : ℝ) ^ 2 + y := Real.sq_sqrt hnn
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set K := k x y with hK
  set L := (s - x) ^ 2 with hL
  have hKL : K * L = 1 := by
    rw [hK, k, ← hs, hL, ← mul_pow]
    have : (s + x) * (s - x) = y := by nlinarith
    rw [this, hy2]
  have hKinv : K⁻¹ = L := by
    exact inv_eq_of_mul_eq_one_right hKL
  have hsum : K + L = 2 * (2 * (x : ℝ) ^ 2 + y) := by
    rw [hK, k, ← hs, hL]; nlinarith
  clear_value K L s
  have key : ∀ n : ℕ, (∃ m : ℤ, (K ^ n + L ^ n) / 2 = m) ∧
      (∃ m : ℤ, (K ^ (n + 1) + L ^ (n + 1)) / 2 = m) := by
    intro n
    induction n with
    | zero => exact ⟨⟨1, by norm_num⟩, ⟨2 * x ^ 2 + y, by rw [pow_one, pow_one, hsum]; push_cast; ring⟩⟩
    | succ n ih =>
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := ih
      refine ⟨⟨b, hb⟩, ⟨2 * (2 * x ^ 2 + y) * b - a, ?_⟩⟩
      have : K ^ (n + 1 + 1) + L ^ (n + 1 + 1) =
          (K + L) * (K ^ (n + 1) + L ^ (n + 1)) - (K * L) * (K ^ n + L ^ n) := by ring
      rw [this, hKL, hsum]
      push_cast
      linear_combination (2 * (2 * (x : ℝ) ^ 2 + y)) * hb - ha
  obtain ⟨⟨m, hm⟩, _⟩ := key n
  refine ⟨m, ?_⟩
  rw [zpow_neg, zpow_natCast, ← inv_pow, hKinv, hm]
