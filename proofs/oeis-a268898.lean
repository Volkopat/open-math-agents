import OMAStatements.S_oeis_a268898

-- Problem: A268898: Number of n X 2 0..2 arrays with some element plus some horizontally or antidiagonally adjacent neighbor totalling two exactly onc
-- Upstream: formal-conjectures statements/oeis-a268898.lean:0 (declaration OMA.S_oeis_a268898.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)

open OMA.S_oeis_a268898 PowerSeries

lemma OMA.c0 : ∀ (k : ℕ) (x : Color), count k x 0 = 2 ^ k := by
  intro k
  induction k with
  | zero => intro x; simp [count]
  | succ k ih =>
    intro x
    fin_cases x <;> simp [count, colors, ih] <;> ring

lemma OMA.c1 : ∀ (k : ℕ) (x : Color), 2 * count k x 1 = k * 2 ^ k := by
  intro k
  induction k with
  | zero => intro x; simp [count]
  | succ k ih =>
    intro x
    have h0 := ih 0
    have h1 := ih 1
    have h2 := ih 2
    have e : (k + 1) * 2 ^ (k + 1) = 2 * (k * 2 ^ k) + 2 * 2 ^ k := by ring
    rw [e]
    fin_cases x <;> simp [count, colors, OMA.c0] <;> linarith

lemma OMA.closed : ∀ n : ℕ, a (n + 1) = 4 ^ n * (6 * n + 3) := by
  intro n
  have h0 := OMA.c1 (2 * n + 1) 0
  have h1 := OMA.c1 (2 * n + 1) 1
  have h2 := OMA.c1 (2 * n + 1) 2
  have e4 : (4 : ℕ) ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
  have e : (2 * n + 1) * 2 ^ (2 * n + 1) = 4 * (n * 2 ^ (2 * n)) + 2 * 2 ^ (2 * n) := by ring
  rw [e] at h0 h1 h2
  have e2 : (4 : ℕ) ^ n * (6 * n + 3) = 6 * (n * 2 ^ (2 * n)) + 3 * 2 ^ (2 * n) := by rw [e4]; ring
  rw [e2]
  simp [a, colors]
  linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a268898.main := by
  have hrec : ∀ n : ℕ, a (n+3)+16*a (n+1)=8*a (n+2) := by
    intro n
    rw [OMA.closed, OMA.closed, OMA.closed]
    ring
  refine ⟨hrec, ?_, OMA.closed⟩
  have h : (1-4*X)^2*(PowerSeries.mk (fun n => (a n : ℚ)))
      = PowerSeries.mk (fun n => (a n : ℚ)) - (8 : ℕ) • (X * PowerSeries.mk (fun n => (a n : ℚ)))
        + (16 : ℕ) • (X * (X * PowerSeries.mk (fun n => (a n : ℚ)))) := by
    simp only [nsmul_eq_mul]
    push_cast
    ring
  have h' : (3*X*(1+4*X) : PowerSeries ℚ) = (3 : ℕ) • X + (12 : ℕ) • (X * X) := by
    simp only [nsmul_eq_mul]
    push_cast
    ring
  rw [h, h']
  ext n
  have a0 : a 0 = 0 := rfl
  have a1 : a 1 = 3 := by rw [OMA.closed]; norm_num
  have a2 : a 2 = 36 := by rw [OMA.closed]; norm_num
  rcases n with _ | _ | _ | m
  · simp [a0]
  · simp only [map_add, map_sub, map_nsmul, coeff_succ_X_mul, coeff_zero_X_mul, coeff_mk,
      coeff_X, coeff_zero_X]
    norm_num [a0, a1]
  · simp only [map_add, map_sub, map_nsmul, coeff_succ_X_mul, coeff_zero_X_mul, coeff_mk,
      coeff_X, coeff_zero_X]
    norm_num [a0, a1, a2]
  · have hq : ((a (m + 3) : ℚ)) + 16 * a (m + 1) = 8 * a (m + 2) := by exact_mod_cast hrec m
    simp only [map_add, map_sub, map_nsmul, coeff_succ_X_mul, coeff_zero_X_mul, coeff_mk,
      coeff_X, coeff_zero_X]
    norm_num
    rw [if_neg (by omega)]
    have e3 : m + 1 + 1 + 1 = m + 3 := rfl
    rw [e3]
    linarith
