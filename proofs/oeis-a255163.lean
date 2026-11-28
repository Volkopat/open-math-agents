import OMAStatements.S_oeis_a255163

-- Problem: A255163: Irrational parts of circle radii in nested circles and hexagons (see comment).
-- Upstream: formal-conjectures statements/oeis-a255163.lean:0 (declaration OMA.S_oeis_a255163.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: the step (A, B) to (12B - 6A, 4A - 6B) has the matrix [[-6, 12], [4, -6]] with trace -12
-- and determinant -12, so by Cayley-Hamilton B(n+2) = -12 B(n+1) + 12 B(n) (checked by unfolding two
-- steps). The g.f. follows by comparing coefficients, with a(0) = 1 and a(1) = 2.

open OMA.S_oeis_a255163 in
theorem OMA.solution : type_of% @OMA.S_oeis_a255163.main := by
  have hrecZ : ∀ m, a (m + 2) = -12 * a (m + 1) + 12 * a m := by
    intro m
    have e1 : (AB (m + 1)).1 = 12 * (AB m).2 - 6 * (AB m).1 := rfl
    have e2 : (AB (m + 1)).2 = 4 * (AB m).1 - 6 * (AB m).2 := rfl
    have e3 : (AB (m + 2)).2 = 4 * (AB (m + 1)).1 - 6 * (AB (m + 1)).2 := rfl
    show (AB (m + 2)).2 = -12 * (AB (m + 1)).2 + 12 * (AB m).2
    rw [e3, e1, e2]
    ring
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
    exact hrecZ m
  · have hrec : ∀ m, (a (m + 2) : ℚ) = -12 * (a (m + 1) : ℚ) + 12 * (a m : ℚ) := by
      intro m
      exact_mod_cast hrecZ m
    have a0 : (a 0 : ℚ) = 1 := by
      have h : a 0 = 1 := by decide
      exact_mod_cast h
    have a1 : (a 1 : ℚ) = 2 := by
      have h : a 1 = 2 := by decide
      exact_mod_cast h
    obtain ⟨A, hA⟩ : ∃ A : PowerSeries ℚ, A = PowerSeries.mk (fun n => (a n : ℚ)) := ⟨_, rfl⟩
    rw [← hA]
    have cA : ∀ m, PowerSeries.coeff m A = (a m : ℚ) := by
      intro m
      rw [hA, PowerSeries.coeff_mk]
    have h1 : (PowerSeries.C (1 : ℚ) : PowerSeries ℚ) = 1 := map_one _
    have h12 : (PowerSeries.C (12 : ℚ) : PowerSeries ℚ) = 12 := map_ofNat _ 12
    have h14 : (PowerSeries.C (14 : ℚ) : PowerSeries ℚ) = 14 := map_ofNat _ 14
    have e : A * (12 * PowerSeries.X ^ 2 - 12 * PowerSeries.X - 1) =
        PowerSeries.C (12 : ℚ) * (A * PowerSeries.X ^ 2) -
          PowerSeries.C (12 : ℚ) * (A * PowerSeries.X ^ 1) - A := by
      rw [h12]
      ring
    have e2 : (-(14 * PowerSeries.X + 1) : PowerSeries ℚ) =
        -(PowerSeries.C (14 : ℚ) * PowerSeries.X ^ 1) - PowerSeries.C (1 : ℚ) := by
      rw [h14, h1]
      ring
    refine e.trans (Eq.trans ?_ e2.symm)
    ext m
    simp only [map_sub, map_neg, PowerSeries.coeff_C_mul]
    rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m <;>
        simp only [PowerSeries.coeff_mul_X_pow', cA, PowerSeries.coeff_X_pow, PowerSeries.coeff_C] <;>
        norm_num [a0, a1]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
      have t1 : PowerSeries.coeff (k + 2) (A * PowerSeries.X ^ 1) = (a (k + 1) : ℚ) := by
        rw [show k + 2 = k + 1 + 1 by omega, PowerSeries.coeff_mul_X_pow, cA]
      have t2 : PowerSeries.coeff (k + 2) (A * PowerSeries.X ^ 2) = (a k : ℚ) := by
        rw [PowerSeries.coeff_mul_X_pow, cA]
      have u0 : PowerSeries.coeff (k + 2) (PowerSeries.C (1 : ℚ)) = 0 := by
        rw [PowerSeries.coeff_C, if_neg (show ¬(k + 2 = 0) by omega)]
      have u1 : PowerSeries.coeff (k + 2) (PowerSeries.X ^ 1 : PowerSeries ℚ) = 0 := by
        rw [PowerSeries.coeff_X_pow, if_neg (show ¬(k + 2 = 1) by omega)]
      rw [cA (k + 2), t1, t2, u0, u1, hrec k]
      ring
