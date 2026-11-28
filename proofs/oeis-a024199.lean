import OMAStatements.S_oeis_a024199

-- Problem: A024199: a(n) = (2n-1)!! * Sum_{k=0..n-1}(-1)^k/(2k+1).
-- Upstream: formal-conjectures statements/oeis-a024199.lean:0 (declaration OMA.S_oeis_a024199.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: Gamma(s+1) = s*Gamma(s) gives D(m+1) = (2m+1)*D(m) for D(m) = dfact(2m-1), every
-- integer m, and D(0) = 1, so D(n) = (2n-1)!! for n >= 0. Let T(n,k) be the k-th summand. Then
-- T(n+1,k) = -(2n+1)*T(n,k) + 2*T(n+1,k+1), and (2n+1)*(T(n,2n) + T(n,2n+1)) = 2*T(n+1,2n+2),
-- T(n+1,0) = (-1)^n*(2n-1)!!. Summing, S(n) = Sum_{k<2n} T(n,k) satisfies
-- S(n+1) = (2n+1)*S(n) + 2*(-1)^n*(2n-1)!!, which is twice the recurrence
-- a(n+1) = (2n+1)*a(n) + (-1)^n*(2n-1)!!; with S(0) = 0 = 2a(0) induction gives S(n) = 2a(n).

open OMA.S_oeis_a024199 in
theorem OMA.solution : type_of% @OMA.S_oeis_a024199.main := by
  have hD : ∀ m : ℤ, dfact (2 * (m + 1) - 1) = (2 * (m : ℝ) + 1) * dfact (2 * m - 1) := by
    intro m
    have hm : (m : ℝ) + 1 / 2 ≠ 0 := by
      intro h
      have h2 : ((2 * m + 1 : ℤ) : ℝ) = 0 := by
        push_cast
        linarith
      have h3 : (2 * m + 1 : ℤ) = 0 := by exact_mod_cast h2
      omega
    have e1 : (((2 * (m + 1) - 1 : ℤ) : ℝ) + 1) / 2 = (m : ℝ) + 1 := by
      push_cast
      ring
    have e2 : ((2 * (m + 1) - 1 : ℤ) : ℝ) / 2 + 1 = ((m : ℝ) + 1 / 2) + 1 := by
      push_cast
      ring
    have e3 : (((2 * m - 1 : ℤ) : ℝ) + 1) / 2 = (m : ℝ) := by
      push_cast
      ring
    have e4 : ((2 * m - 1 : ℤ) : ℝ) / 2 + 1 = (m : ℝ) + 1 / 2 := by
      push_cast
      ring
    unfold dfact
    rw [e1, e2, e3, e4, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one,
      Real.Gamma_add_one hm]
    ring
  have hD0 : dfact (-1) = 1 := by
    have e1 : (((-1 : ℤ) : ℝ) + 1) / 2 = 0 := by norm_num
    have e2 : ((-1 : ℤ) : ℝ) / 2 + 1 = 1 / 2 := by norm_num
    unfold dfact
    rw [e1, e2, Real.rpow_zero, Real.Gamma_one_half_eq, one_mul]
    exact div_self (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  have df_succ : ∀ n : ℕ, Nat.doubleFactorial (2 * (n + 1) - 1) =
      (2 * n + 1) * Nat.doubleFactorial (2 * n - 1) := by
    intro n
    cases n with
    | zero => rfl
    | succ m =>
      rw [show 2 * (m + 1 + 1) - 1 = 2 * (m + 1) + 1 by omega,
        show 2 * (m + 1) - 1 = 2 * m + 1 by omega,
        show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega, Nat.doubleFactorial_add_two]
  have dfN : ∀ n : ℕ, dfact (2 * (n : ℤ) - 1) = ((Nat.doubleFactorial (2 * n - 1) : ℕ) : ℝ) := by
    intro n
    induction n with
    | zero => simpa using hD0
    | succ m ih =>
      have hc : ((2 * m + 1 : ℕ) : ℝ) = 2 * (m : ℝ) + 1 := by norm_cast
      rw [show 2 * ((m + 1 : ℕ) : ℤ) - 1 = 2 * ((m : ℤ) + 1) - 1 by omega, hD, ih, df_succ,
        Nat.cast_mul, Int.cast_natCast, hc]
  have ha : ∀ n : ℕ, a (n + 1) = (2 * (n : ℚ) + 1) * a n +
      (-1 : ℚ) ^ n * ((Nat.doubleFactorial (2 * n - 1) : ℕ) : ℚ) := by
    intro n
    have hq : (2 * (n : ℚ) + 1) ≠ 0 := by positivity
    have hc : ((2 * n + 1 : ℕ) : ℚ) = 2 * (n : ℚ) + 1 := by norm_cast
    have h1 : (2 * (n : ℚ) + 1) * ((-1 : ℚ) ^ n / (2 * (n : ℚ) + 1)) = (-1 : ℚ) ^ n :=
      mul_div_cancel₀ _ hq
    unfold a
    rw [Finset.sum_range_succ, df_succ, Nat.cast_mul, hc]
    linear_combination ((Nat.doubleFactorial (2 * n - 1) : ℕ) : ℚ) * h1
  have ha' : ∀ n : ℕ, ((a (n + 1) : ℚ) : ℝ) = (2 * (n : ℝ) + 1) * ((a n : ℚ) : ℝ) +
      (-1 : ℝ) ^ n * ((Nat.doubleFactorial (2 * n - 1) : ℕ) : ℝ) := by
    intro n
    exact_mod_cast ha n
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℕ → ℝ, ∀ n k : ℕ, T n k =
      (-1 : ℝ) ^ ((n : ℤ) - k + 1) * (Nat.factorial k : ℝ) * dfact (2 * (n : ℤ) - 2 * k - 3) :=
    ⟨_, fun _ _ => rfl⟩
  have key : ∀ n k : ℕ, T (n + 1) k = -(2 * (n : ℝ) + 1) * T n k + 2 * T (n + 1) (k + 1) := by
    intro n k
    have s1 : (-1 : ℝ) ^ (((n + 1 : ℕ) : ℤ) - (k : ℤ) + 1) =
        -((-1 : ℝ) ^ ((n : ℤ) - (k : ℤ) + 1)) := by
      rw [show ((n + 1 : ℕ) : ℤ) - (k : ℤ) + 1 = ((n : ℤ) - (k : ℤ) + 1) + 1 by omega,
        zpow_add_one₀ (by norm_num : (-1 : ℝ) ≠ 0)]
      ring
    have s2 : (-1 : ℝ) ^ (((n + 1 : ℕ) : ℤ) - ((k + 1 : ℕ) : ℤ) + 1) =
        (-1 : ℝ) ^ ((n : ℤ) - (k : ℤ) + 1) := by
      rw [show ((n + 1 : ℕ) : ℤ) - ((k + 1 : ℕ) : ℤ) + 1 = (n : ℤ) - (k : ℤ) + 1 by omega]
    have d1 : dfact (2 * ((n + 1 : ℕ) : ℤ) - 2 * (k : ℤ) - 3) =
        (2 * (((n : ℤ) - k - 1 : ℤ) : ℝ) + 1) * dfact (2 * (n : ℤ) - 2 * (k : ℤ) - 3) := by
      rw [show 2 * ((n + 1 : ℕ) : ℤ) - 2 * (k : ℤ) - 3 = 2 * (((n : ℤ) - k - 1) + 1) - 1 by omega,
        show 2 * (n : ℤ) - 2 * (k : ℤ) - 3 = 2 * ((n : ℤ) - k - 1) - 1 by omega]
      exact hD _
    have d2 : dfact (2 * ((n + 1 : ℕ) : ℤ) - 2 * ((k + 1 : ℕ) : ℤ) - 3) =
        dfact (2 * (n : ℤ) - 2 * (k : ℤ) - 3) := by
      rw [show 2 * ((n + 1 : ℕ) : ℤ) - 2 * ((k + 1 : ℕ) : ℤ) - 3 =
        2 * (n : ℤ) - 2 * (k : ℤ) - 3 by omega]
    rw [hT, hT, hT, s1, s2, d1, d2, Nat.factorial_succ]
    push_cast
    ring
  have bd : ∀ n : ℕ, (2 * (n : ℝ) + 1) * (T n (2 * n) + T n (2 * n + 1)) =
      2 * T (n + 1) (2 * n + 1 + 1) := by
    intro n
    have s1 : (-1 : ℝ) ^ ((n : ℤ) - ((2 * n : ℕ) : ℤ) + 1) = -((-1 : ℝ) ^ (-(n : ℤ))) := by
      rw [show (n : ℤ) - ((2 * n : ℕ) : ℤ) + 1 = -(n : ℤ) + 1 by omega,
        zpow_add_one₀ (by norm_num : (-1 : ℝ) ≠ 0)]
      ring
    have s2 : (-1 : ℝ) ^ ((n : ℤ) - ((2 * n + 1 : ℕ) : ℤ) + 1) = (-1 : ℝ) ^ (-(n : ℤ)) := by
      rw [show (n : ℤ) - ((2 * n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) by omega]
    have s3 : (-1 : ℝ) ^ (((n + 1 : ℕ) : ℤ) - ((2 * n + 1 + 1 : ℕ) : ℤ) + 1) =
        (-1 : ℝ) ^ (-(n : ℤ)) := by
      rw [show ((n + 1 : ℕ) : ℤ) - ((2 * n + 1 + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) by omega]
    have d1 : dfact (2 * (n : ℤ) - 2 * ((2 * n : ℕ) : ℤ) - 3) =
        (2 * ((-(n : ℤ) - 2 : ℤ) : ℝ) + 1) * dfact (2 * (n : ℤ) - 2 * ((2 * n + 1 : ℕ) : ℤ) - 3) := by
      rw [show 2 * (n : ℤ) - 2 * ((2 * n : ℕ) : ℤ) - 3 = 2 * ((-(n : ℤ) - 2) + 1) - 1 by omega,
        show 2 * (n : ℤ) - 2 * ((2 * n + 1 : ℕ) : ℤ) - 3 = 2 * (-(n : ℤ) - 2) - 1 by omega]
      exact hD _
    have d2 : dfact (2 * ((n + 1 : ℕ) : ℤ) - 2 * ((2 * n + 1 + 1 : ℕ) : ℤ) - 3) =
        dfact (2 * (n : ℤ) - 2 * ((2 * n + 1 : ℕ) : ℤ) - 3) := by
      rw [show 2 * ((n + 1 : ℕ) : ℤ) - 2 * ((2 * n + 1 + 1 : ℕ) : ℤ) - 3 =
        2 * (n : ℤ) - 2 * ((2 * n + 1 : ℕ) : ℤ) - 3 by omega]
    have hf1 : Nat.factorial (2 * n + 1) = (2 * n + 1) * Nat.factorial (2 * n) :=
      Nat.factorial_succ (2 * n)
    have hf2 : Nat.factorial (2 * n + 1 + 1) =
        (2 * n + 1 + 1) * ((2 * n + 1) * Nat.factorial (2 * n)) := by
      rw [Nat.factorial_succ (2 * n + 1), hf1]
    have f1 : ((Nat.factorial (2 * n + 1) : ℕ) : ℝ) =
        (2 * (n : ℝ) + 1) * ((Nat.factorial (2 * n) : ℕ) : ℝ) := by
      exact_mod_cast hf1
    have f2 : ((Nat.factorial (2 * n + 1 + 1) : ℕ) : ℝ) =
        (2 * (n : ℝ) + 1 + 1) * ((2 * (n : ℝ) + 1) * ((Nat.factorial (2 * n) : ℕ) : ℝ)) := by
      exact_mod_cast hf2
    rw [hT, hT, hT, s1, s2, s3, d1, d2, f1, f2]
    push_cast
    ring
  have ht0 : ∀ n : ℕ, T (n + 1) 0 = (-1 : ℝ) ^ n * ((Nat.doubleFactorial (2 * n - 1) : ℕ) : ℝ) := by
    intro n
    have s : (-1 : ℝ) ^ (((n + 1 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) + 1) = (-1 : ℝ) ^ n := by
      rw [show ((n + 1 : ℕ) : ℤ) - ((0 : ℕ) : ℤ) + 1 = ((n + 2 : ℕ) : ℤ) by omega, zpow_natCast,
        pow_add]
      norm_num
    have d : dfact (2 * ((n + 1 : ℕ) : ℤ) - 2 * ((0 : ℕ) : ℤ) - 3) =
        ((Nat.doubleFactorial (2 * n - 1) : ℕ) : ℝ) := by
      rw [show 2 * ((n + 1 : ℕ) : ℤ) - 2 * ((0 : ℕ) : ℤ) - 3 = 2 * (n : ℤ) - 1 by omega]
      exact dfN n
    rw [hT, s, d, Nat.factorial_zero, Nat.cast_one, mul_one]
  have hS : ∀ n : ℕ, ∑ k ∈ Finset.range (2 * n), T n k = 2 * ((a n : ℚ) : ℝ) := by
    intro n
    induction n with
    | zero => simp [a]
    | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
      have hsum : ∑ k ∈ Finset.range (2 * n + 1 + 1), T (n + 1) k =
          -(2 * (n : ℝ) + 1) * ∑ k ∈ Finset.range (2 * n + 1 + 1), T n k +
            2 * ∑ k ∈ Finset.range (2 * n + 1 + 1), T (n + 1) (k + 1) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun k _ => key n k)
      have r1a := Finset.sum_range_succ (T n) (2 * n + 1)
      have r1b := Finset.sum_range_succ (T n) (2 * n)
      have r2a := Finset.sum_range_succ' (T (n + 1)) (2 * n + 1 + 1)
      have r2b := Finset.sum_range_succ (T (n + 1)) (2 * n + 1 + 1)
      have hb := bd n
      have h0 := ht0 n
      have hA := ha' n
      linear_combination (-1 : ℝ) * hsum + (2 * (n : ℝ) + 1) * r1a + (2 * (n : ℝ) + 1) * r1b +
        2 * r2a - 2 * r2b + hb + 2 * h0 + (2 * (n : ℝ) + 1) * ih - 2 * hA
  intro n
  have hsumT : ∑ k ∈ Finset.range (2 * n),
      (-1 : ℝ) ^ ((n : ℤ) - k + 1) * (Nat.factorial k : ℝ) * dfact (2 * (n : ℤ) - 2 * k - 3) =
        ∑ k ∈ Finset.range (2 * n), T n k :=
    Finset.sum_congr rfl (fun k _ => (hT n k).symm)
  rw [hsumT, hS n]
  ring
