import OMAStatements.S_oeis_a371898

-- Problem: A371898: Triangle read by rows: T(n, k) = n * k * (T(n-1, k-1) + T(n-1, k)) for k > 0 with initial values T(n, 0) = 1 and T(i, j) = 0 for j > i.
-- Upstream: formal-conjectures statements/oeis-a371898.lean:0 (declaration OMA.S_oeis_a371898.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: T(n, k) = 0 for k > n, so T(n+1, k+1) = (n+1)(k+1)(T(n, k) + T(n, k+1)) for all n, k.
-- With E(k) the e.g.f. of column k, this gives E(k+1) (1 - (k+1) t) = (k+1) t E(k) coefficientwise,
-- and E(0) = exp(t); induction on k gives E(k) Prod_{i=0..k} (1 - i t) = k! t^k exp(t).
-- For the second claim let S(n) = Sum_k (-1)^k T(n, k). With f(j) = (-1)^j j T(n, j) the recurrence
-- gives S(n+1) = 1 - (n+1) S(n) by a telescoping sum, so S(n) = (-1)^n d(n) for the derangement
-- numbers d (d(n+1) = (n+1) d(n) - (-1)^n), and Sum_k (-1)^(n-k) T(n, k) = (-1)^n S(n) = d(n).

namespace P1A371898

open OMA.S_oeis_a371898

theorem T_zero_right (n : ℕ) : T n 0 = 1 := by
  cases n <;> rfl

theorem T_vanish (n k : ℕ) (hk : n < k) : T n k = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  cases n with
  | zero => rfl
  | succ m =>
    show (if m + 1 < j + 1 then 0 else (m + 1) * (j + 1) * (T m j + T m (j + 1))) = 0
    rw [if_pos hk]

theorem T_rec (n k : ℕ) : T (n + 1) (k + 1) = (n + 1) * (k + 1) * (T n k + T n (k + 1)) := by
  show (if n + 1 < k + 1 then 0 else (n + 1) * (k + 1) * (T n k + T n (k + 1))) = _
  by_cases h : n + 1 < k + 1
  · rw [if_pos h, T_vanish n k (by omega), T_vanish n (k + 1) (by omega), add_zero, mul_zero]
  · rw [if_neg h]

/-- The coefficients of the e.g.f. of column k. -/
def cf (k n : ℕ) : ℚ := (T n k : ℚ) / (n.factorial : ℚ)

theorem coef (a b c f m : ℚ) (hm : m + 1 ≠ 0) :
    (m + 1) * c * (a + b) / ((m + 1) * f) - c * (b / f) = c * (a / f) := by
  rw [mul_assoc (m + 1) c (a + b), mul_div_mul_left (c * (a + b)) f hm]
  ring

theorem step (k : ℕ) :
    PowerSeries.mk (cf (k + 1)) * (1 - ((k + 1 : ℕ) : PowerSeries ℚ) * PowerSeries.X) =
      ((k + 1 : ℕ) : PowerSeries ℚ) * (PowerSeries.mk (cf k) * PowerSeries.X ^ 1) := by
  rw [← map_natCast (PowerSeries.C : ℚ →+* PowerSeries ℚ) (k + 1)]
  have e : PowerSeries.mk (cf (k + 1)) *
      (1 - (PowerSeries.C : ℚ →+* PowerSeries ℚ) ((k + 1 : ℕ) : ℚ) * PowerSeries.X) =
      PowerSeries.mk (cf (k + 1)) - (PowerSeries.C : ℚ →+* PowerSeries ℚ) ((k + 1 : ℕ) : ℚ) *
        (PowerSeries.mk (cf (k + 1)) * PowerSeries.X ^ 1) := by
    ring
  rw [e]
  ext n
  simp only [cf, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk]
  cases n with
  | zero =>
    rw [if_neg (show ¬ (1 ≤ 0) by omega), if_neg (show ¬ (1 ≤ 0) by omega),
      show T 0 (k + 1) = 0 from rfl]
    simp
  | succ m =>
    have hm : (m : ℚ) + 1 ≠ 0 := by positivity
    have hT : (T (m + 1) (k + 1) : ℚ) =
        ((m : ℚ) + 1) * ((k + 1 : ℕ) : ℚ) * ((T m k : ℚ) + (T m (k + 1) : ℚ)) := by
      exact_mod_cast T_rec m k
    have hF : ((m + 1).factorial : ℚ) = ((m : ℚ) + 1) * (m.factorial : ℚ) := by
      exact_mod_cast Nat.factorial_succ m
    rw [if_pos (show 1 ≤ m + 1 by omega), if_pos (show 1 ≤ m + 1 by omega),
      show m + 1 - 1 = m by omega, hT, hF]
    exact coef _ _ _ _ _ hm

theorem egf (k : ℕ) :
    PowerSeries.mk (cf k) * ∏ i ∈ Finset.range (k + 1), (1 - (i : PowerSeries ℚ) * PowerSeries.X) =
      (k.factorial : PowerSeries ℚ) * PowerSeries.X ^ k * PowerSeries.exp ℚ := by
  induction k with
  | zero =>
    have h0 : PowerSeries.mk (cf 0) = PowerSeries.exp ℚ := by
      ext n
      simp only [cf, PowerSeries.coeff_mk, PowerSeries.coeff_exp, T_zero_right]
      simp
    rw [h0]
    simp
  | succ k ih =>
    rw [Finset.prod_range_succ]
    calc PowerSeries.mk (cf (k + 1)) * ((∏ i ∈ Finset.range (k + 1), (1 - (i : PowerSeries ℚ) * PowerSeries.X)) *
          (1 - ((k + 1 : ℕ) : PowerSeries ℚ) * PowerSeries.X))
        = (PowerSeries.mk (cf (k + 1)) * (1 - ((k + 1 : ℕ) : PowerSeries ℚ) * PowerSeries.X)) *
          ∏ i ∈ Finset.range (k + 1), (1 - (i : PowerSeries ℚ) * PowerSeries.X) := by ring
      _ = ((k + 1 : ℕ) : PowerSeries ℚ) * (PowerSeries.mk (cf k) * PowerSeries.X ^ 1) *
          ∏ i ∈ Finset.range (k + 1), (1 - (i : PowerSeries ℚ) * PowerSeries.X) := by
        rw [step k]
      _ = ((k + 1 : ℕ) : PowerSeries ℚ) * PowerSeries.X *
          (PowerSeries.mk (cf k) * ∏ i ∈ Finset.range (k + 1), (1 - (i : PowerSeries ℚ) * PowerSeries.X)) := by
        ring
      _ = ((k + 1 : ℕ) : PowerSeries ℚ) * PowerSeries.X *
          ((k.factorial : PowerSeries ℚ) * PowerSeries.X ^ k * PowerSeries.exp ℚ) := by
        rw [ih]
      _ = (((k + 1).factorial : ℕ) : PowerSeries ℚ) * PowerSeries.X ^ (k + 1) *
          PowerSeries.exp ℚ := by
        rw [Nat.factorial_succ, Nat.cast_mul]
        ring

theorem sq_one (n : ℕ) : ((-1 : ℤ) ^ n) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]

theorem sgn (n k : ℕ) (hk : k ≤ n) : (-1 : ℤ) ^ (n - k) = (-1) ^ n * (-1) ^ k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = k + m := ⟨n - k, by omega⟩
  rw [show k + m - k = m by omega, pow_add]
  linear_combination (-(-1 : ℤ) ^ m) * sq_one k

theorem alt (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1 + 1), (-1 : ℤ) ^ k * (T (n + 1) k : ℤ) =
      1 - ((n : ℤ) + 1) * ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * (T n k : ℤ) := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℤ, ∀ j, f j = (-1 : ℤ) ^ j * (j : ℤ) * (T n j : ℤ) :=
    ⟨_, fun _ => rfl⟩
  have key : ∀ k, (-1 : ℤ) ^ (k + 1) * (T (n + 1) (k + 1) : ℤ) =
      -(((n : ℤ) + 1) * ((-1 : ℤ) ^ k * (T n k : ℤ))) + ((n : ℤ) + 1) * (f (k + 1) - f k) := by
    intro k
    rw [hf, hf, T_rec n k]
    push_cast
    ring
  rw [Finset.sum_range_succ' (fun k => (-1 : ℤ) ^ k * (T (n + 1) k : ℤ)) (n + 1),
    Finset.sum_congr rfl (fun k _ => key k), Finset.sum_add_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_range_sub, hf, hf,
    T_vanish n (n + 1) (by omega), T_zero_right (n + 1)]
  push_cast
  ring

theorem alt_closed (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * (T n k : ℤ) =
      (-1 : ℤ) ^ n * (numDerangements n : ℤ) := by
  induction n with
  | zero => simp [T_zero_right, numDerangements_zero]
  | succ n ih =>
    rw [alt n, ih, numDerangements_succ]
    linear_combination (-1 : ℤ) * sq_one n

theorem der (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * (T n k : ℤ) = (numDerangements n : ℤ) := by
  have e : ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * (T n k : ℤ) =
      (-1 : ℤ) ^ n * ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * (T n k : ℤ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := by
      have := Finset.mem_range.mp hk
      omega
    rw [sgn n k hk']
    ring
  rw [e, alt_closed n]
  linear_combination (numDerangements n : ℤ) * sq_one n

end P1A371898

open OMA.S_oeis_a371898 P1A371898 in
theorem OMA.solution : type_of% @OMA.S_oeis_a371898.main := by
  exact ⟨fun k => egf k, fun n => der n⟩
