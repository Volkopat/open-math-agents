import OMAStatements.S_oeis_a045626

-- Problem: A045626: Bends in loxodromic sequence of spheres in which each 5 consecutive spheres are in mutual contact.
-- Upstream: formal-conjectures statements/oeis-a045626.lean:0 (declaration OMA.S_oeis_a045626.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: (1 + x)(1 - 2x + x^2 - 2x^3 + x^4) = 1 - x - x^2 - x^3 - x^4 + x^5, so the coefficient
-- of x^m on the left is a(m) - a(m-1) - a(m-2) - a(m-3) - a(m-4) + a(m-5), the terms with a negative
-- index left out. For m >= 5 it is 0 by the defining recurrence, and for m < 5 it is the coefficient
-- of the numerator, by the five initial values.

open OMA.S_oeis_a045626 in
theorem OMA.solution : type_of% @OMA.S_oeis_a045626.main := by
  have hq : ∀ k, (a (k + 5) : ℚ) = (a (k + 4) : ℚ) + (a (k + 3) : ℚ) + (a (k + 2) : ℚ) +
      (a (k + 1) : ℚ) - (a k : ℚ) := by
    intro k
    have h : a (k + 5) = a (k + 4) + a (k + 3) + a (k + 2) + a (k + 1) - a k := rfl
    exact_mod_cast h
  have hq' : ∀ m, 5 ≤ m → (a m : ℚ) = (a (m - 1) : ℚ) + (a (m - 2) : ℚ) + (a (m - 3) : ℚ) +
      (a (m - 4) : ℚ) - (a (m - 5) : ℚ) := by
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 5 := ⟨m - 5, by omega⟩
    rw [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
      show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega,
      show k + 5 - 5 = k by omega]
    exact hq k
  have a0 : (a 0 : ℚ) = -1 := by
    have h : a 0 = -1 := rfl
    exact_mod_cast h
  have a1 : (a 1 : ℚ) = 2 := by
    have h : a 1 = 2 := rfl
    exact_mod_cast h
  have a2 : (a 2 : ℚ) = 3 := by
    have h : a 2 = 3 := rfl
    exact_mod_cast h
  have a3 : (a 3 : ℚ) = 3 := by
    have h : a 3 = 3 := rfl
    exact_mod_cast h
  have a4 : (a 4 : ℚ) = 5 := by
    have h : a 4 = 5 := rfl
    exact_mod_cast h
  have e : PowerSeries.mk (fun n => (a n : ℚ)) *
      ((1 + PowerSeries.X) * (1 - 2 * PowerSeries.X + PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3 +
        PowerSeries.X ^ 4)) =
      PowerSeries.mk (fun n => (a n : ℚ))
        - PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 1
        - PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 2
        - PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 3
        - PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 4
        + PowerSeries.mk (fun n => (a n : ℚ)) * PowerSeries.X ^ 5 := by
    ring
  have e2 : -(1 - 3 * PowerSeries.X - 2 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3 +
      2 * PowerSeries.X ^ 4 : PowerSeries ℚ) =
      (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3 * PowerSeries.X ^ 1
        + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 * PowerSeries.X ^ 2
        - PowerSeries.X ^ 3
        - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 * PowerSeries.X ^ 4 - 1 := by
    rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3,
      map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
    ring
  rw [e, e2]
  ext m
  simp only [map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
    PowerSeries.coeff_C, PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
  rcases Nat.lt_or_ge m 5 with hm | hm
  · interval_cases m
    · norm_num [a0]
    · norm_num [a0, a1]
    · norm_num [a0, a1, a2]
    · norm_num [a0, a1, a2, a3]
    · norm_num [a0, a1, a2, a3, a4]
  · simp (disch := omega) only [if_pos, if_neg]
    linarith [hq' m hm]
