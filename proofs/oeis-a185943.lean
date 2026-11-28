import OMAStatements.S_oeis_a185943

-- Problem: A185943: Riordan array ((1/(1-x))^m, x*A000108(x)), m = 2.
-- Upstream: formal-conjectures statements/oeis-a185943.lean:0 (declaration OMA.S_oeis_a185943.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: (1-x)^(-1) is the series with all coefficients 1, so multiplying by it takes
-- partial sums, and multiplying by (1-x)^(-2) takes partial sums twice. Column 1 is
-- (1-x)^(-2) x C(x), so R(n+1,1) is the double partial sum of the Catalan numbers up to n.
-- Column 2 is (1-x)^(-2) x^2 C(x)^2, and the coefficient of x^k in C(x)^2 is catalan(k+1)
-- (the Catalan recurrence), so R(n+2,2) is the double partial sum of catalan(k+1), which is A014143(n).

open OMA.S_oeis_a185943 in
theorem OMA.solution : type_of% @OMA.S_oeis_a185943.main := by
  have hinv : ((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹ = PowerSeries.mk 1 := by
    have h0 : PowerSeries.constantCoeff ((1 : PowerSeries ℚ) - PowerSeries.X) ≠ 0 := by
      simp
    exact ((PowerSeries.eq_inv_iff_mul_eq_one h0).mpr
      (PowerSeries.mk_one_mul_one_sub_eq_one ℚ)).symm
  have psum : ∀ (F : PowerSeries ℚ) (n : ℕ),
      PowerSeries.coeff n (((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹ * F) =
        ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff k F := by
    intro F n
    rw [hinv, mul_comm (PowerSeries.mk (1 : ℕ → ℚ)) F, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp [PowerSeries.coeff_mk]
  have psum2 : ∀ (F : PowerSeries ℚ) (n : ℕ),
      PowerSeries.coeff n (((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹ ^ 2 * F) =
        ∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k F := by
    intro F n
    rw [sq, mul_assoc, psum]
    exact Finset.sum_congr rfl (fun m _ => psum F m)
  have hC : ∀ k : ℕ, PowerSeries.coeff k catGF = (catalan k : ℚ) := by
    intro k
    rw [catGF, PowerSeries.coeff_mk]
  have hCC : ∀ k : ℕ, PowerSeries.coeff k (catGF * catGF) = (catalan (k + 1) : ℚ) := by
    intro k
    rw [PowerSeries.coeff_mul, catalan_succ', Nat.cast_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [hC, hC, Nat.cast_mul]
  have e1 : ∀ G : PowerSeries ℚ,
      G ^ 2 * (PowerSeries.X * catGF) ^ 1 = PowerSeries.X * (G ^ 2 * catGF) := by
    intro G
    ring
  have e2 : ∀ G : PowerSeries ℚ, G ^ 2 * (PowerSeries.X * catGF) ^ 2 =
      PowerSeries.X * (PowerSeries.X * (G ^ 2 * (catGF * catGF))) := by
    intro G
    ring
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
    rw [show N + 1 - 1 = N by omega]
    show PowerSeries.coeff (N + 1)
      (((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹ ^ 2 * (PowerSeries.X * catGF) ^ 1) = _
    rw [e1, PowerSeries.coeff_succ_X_mul, psum2]
    simp only [A014140, hC, Nat.cast_sum]
  · obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 + 1 := ⟨n - 2, by omega⟩
    rw [show N + 1 + 1 - 2 = N by omega]
    show PowerSeries.coeff (N + 1 + 1)
      (((1 : PowerSeries ℚ) - PowerSeries.X)⁻¹ ^ 2 * (PowerSeries.X * catGF) ^ 2) = _
    rw [e2, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul, psum2]
    simp only [A014143, A014138, hCC, Nat.cast_sum]
