import OMAStatements.S_oeis_a235643

-- Problem: A235643: Total number of sides of a tetraflake-like fractal after n iterations, a(1) = 16 (see comments).
-- Upstream: formal-conjectures statements/oeis-a235643.lean:0 (declaration OMA.S_oeis_a235643.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: with T(n) = Sum_{i=3..n} 2*3^(n-i+1)*a(i-3) one has T(n+1) = 3 T(n) + 6 a(n-2),
-- and eliminating T from the rules at n and n+1 gives a(n+1) = 6 a(n) - 7 a(n-1) for n >= 2.
-- The closed form satisfies the same recurrence because (3 -+ sqrt 2)^2 = 6 (3 -+ sqrt 2) - 7,
-- and agrees at n = 1, 2 (a(1) = 16, a(2) = 68); the g.f. follows by comparing coefficients.

open OMA.S_oeis_a235643 in
theorem OMA.solution : type_of% @OMA.S_oeis_a235643.main := by
  intro a h0 h1 hrec
  have hR : ∀ m, a (m + 3) + 7 * a (m + 1) = 6 * a (m + 2) := by
    intro m
    have e2 := hrec (m + 2) (by omega)
    have e3 := hrec (m + 2 + 1) (by omega)
    rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega] at e2
    rw [show m + 2 + 1 - 1 = m + 2 by omega, show m + 2 + 1 - 2 = m + 1 by omega,
      Finset.sum_Icc_succ_top (show 3 ≤ m + 2 + 1 by omega)] at e3
    have hs : ∑ i ∈ Finset.Icc 3 (m + 2), 2 * 3 ^ (m + 2 + 1 - i + 1) * a (i - 3) =
        3 * ∑ i ∈ Finset.Icc 3 (m + 2), 2 * 3 ^ (m + 2 - i + 1) * a (i - 3) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_Icc] at hi
      rw [show m + 2 + 1 - i + 1 = m + 2 - i + 1 + 1 by omega]
      ring
    rw [hs, show m + 2 + 1 - (m + 2 + 1) + 1 = 1 by omega, show m + 2 + 1 - 3 = m by omega,
      pow_one] at e3
    show a (m + 2 + 1) + 7 * a (m + 1) = 6 * a (m + 2)
    omega
  have ha2 : a 2 = 68 := by
    have e := hrec 2 (by norm_num)
    rw [Finset.Icc_eq_empty_of_lt (show 2 < 3 by norm_num), Finset.sum_empty,
      show (2 : ℕ) - 1 = 1 by norm_num, show (2 : ℕ) - 2 = 0 by norm_num, h1, h0] at e
    omega
  obtain ⟨F, hF_def⟩ : ∃ F : ℕ → ℝ, ∀ n, F n = Real.sqrt 2 * ((3 - Real.sqrt 2) ^ n *
      (-1 + Real.sqrt 2) + (1 + Real.sqrt 2) * (3 + Real.sqrt 2) ^ n) := ⟨_, fun _ => rfl⟩
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hF : ∀ n, F (n + 2) = 6 * F (n + 1) - 7 * F n := by
    intro n
    rw [hF_def, hF_def, hF_def]
    have p1 : (3 - Real.sqrt 2) ^ (n + 2) = (3 - Real.sqrt 2) ^ n * (3 - Real.sqrt 2) ^ 2 :=
      pow_add _ _ _
    have p2 : (3 - Real.sqrt 2) ^ (n + 1) = (3 - Real.sqrt 2) ^ n * (3 - Real.sqrt 2) :=
      pow_succ _ _
    have p3 : (3 + Real.sqrt 2) ^ (n + 2) = (3 + Real.sqrt 2) ^ n * (3 + Real.sqrt 2) ^ 2 :=
      pow_add _ _ _
    have p4 : (3 + Real.sqrt 2) ^ (n + 1) = (3 + Real.sqrt 2) ^ n * (3 + Real.sqrt 2) :=
      pow_succ _ _
    rw [p1, p2, p3, p4]
    generalize (3 - Real.sqrt 2) ^ n = U
    generalize (3 + Real.sqrt 2) ^ n = W
    linear_combination (Real.sqrt 2 * (U * (-1 + Real.sqrt 2) + (1 + Real.sqrt 2) * W)) * hs2
  have hR' : ∀ m, (a (m + 3) : ℝ) = 6 * (a (m + 2) : ℝ) - 7 * (a (m + 1) : ℝ) := by
    intro m
    have h := congrArg (fun x : ℕ => (x : ℝ)) (hR m)
    push_cast at h
    linarith
  have hcl : ∀ k : ℕ, (a (k + 1) : ℝ) = F (k + 1) ∧ (a (k + 2) : ℝ) = F (k + 2) := by
    intro k
    induction k with
    | zero =>
      show (a 1 : ℝ) = F 1 ∧ (a 2 : ℝ) = F 2
      constructor
      · rw [h1, hF_def]
        push_cast
        linear_combination (-8 : ℝ) * hs2
      · rw [ha2, hF_def]
        push_cast
        linear_combination (-(2 * Real.sqrt 2 ^ 2 + 34)) * hs2
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have e := hF (k + 1)
      rw [show k + 1 + 2 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega] at e
      show (a (k + 3) : ℝ) = F (k + 3)
      rw [hR' k, ih.1, ih.2, e]
  refine ⟨fun n hn => ?_, fun n hn => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact (hcl k).1.trans (hF_def (k + 1))
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega]
    have h := congrArg (fun x : ℕ => (x : ℤ)) (hR m)
    push_cast at h
    linarith
  · have hq : ∀ k : ℕ, (a (k + 3) : ℚ) = 6 * (a (k + 2) : ℚ) - 7 * (a (k + 1) : ℚ) := by
      intro k
      have h := congrArg (fun x : ℕ => (x : ℚ)) (hR k)
      push_cast at h
      linarith
    have e : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        (7 * PowerSeries.X ^ 2 - 6 * PowerSeries.X + 1) =
        (PowerSeries.C : ℚ →+* PowerSeries ℚ) 7 *
            (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * PowerSeries.X ^ 2)
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6 *
            (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * PowerSeries.X ^ 1)
          + PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 7,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6]
      ring
    have e2 : (4 * PowerSeries.X * (-7 * PowerSeries.X + 4) : PowerSeries ℚ) =
        PowerSeries.X ^ 1 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 16
          - PowerSeries.X ^ 2 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 28 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 16,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 28]
      ring
    rw [e, e2]
    ext n
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C,
      PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk, PowerSeries.coeff_X_pow]
    rcases Nat.lt_or_ge n 3 with hn | hn
    · interval_cases n
      · norm_num
      · norm_num [h1]
      · norm_num [h1, ha2]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      rw [if_pos (show 2 ≤ k + 3 by omega), if_pos (show 1 ≤ k + 3 by omega),
        show k + 3 - 2 = k + 1 by omega, show k + 3 - 1 = k + 2 by omega,
        if_neg (show ¬ (k + 1 = 0) by omega), if_neg (show ¬ (k + 2 = 0) by omega),
        if_neg (show ¬ (k + 3 = 0) by omega), if_neg (show ¬ (k + 3 = 1) by omega),
        if_neg (show ¬ (k + 3 = 2) by omega)]
      linear_combination hq k
