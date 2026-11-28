import OMAStatements.S_oeis_a264745

-- Problem: A264745: Rectangular array A read by upward antidiagonals in which the entry in row n and column k is defined by A(n,k) = Fibonacci(2^(n-1)*(2*k-1) + 1), n,k >= 1.
-- Upstream: formal-conjectures statements/oeis-a264745.lean:0 (declaration OMA.S_oeis_a264745.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Disproof idea: the claim fails already for row n = 1, whose entries are F(2k) = 1, 3, 8, ...
-- There A001566(1) = 3^2 - 2 = 7, and the coefficient of x^2 in
-- (x + 3x^2 + ...) * (1 - 7x + x^2) is 3 - 7 = -4, while x * (F(2) - F(0) x) = x has coefficient 0
-- at x^2. (The row g.f. holds with A001566(n-1) = Lucas(2^n) in place of A001566(n).)

open OMA.S_oeis_a264745 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a264745.main) := by
  intro h
  have h1 := h 1 le_rfl
  have hA1 : A 1 1 = 1 := by decide
  have hA2 : A 1 2 = 3 := by decide
  have hc : A001566 1 = 7 := by decide
  have eL : PowerSeries.X * PowerSeries.mk (fun j => (A 1 (j + 1) : ℚ)) *
        (1 - (PowerSeries.C : ℚ →+* PowerSeries ℚ) (A001566 1 : ℚ) * PowerSeries.X +
          PowerSeries.X ^ 2) =
      PowerSeries.mk (fun j => (A 1 (j + 1) : ℚ)) * PowerSeries.X ^ 1 -
        (PowerSeries.C : ℚ →+* PowerSeries ℚ) (A001566 1 : ℚ) *
          (PowerSeries.mk (fun j => (A 1 (j + 1) : ℚ)) * PowerSeries.X ^ 2) +
        PowerSeries.mk (fun j => (A 1 (j + 1) : ℚ)) * PowerSeries.X ^ 3 := by
    ring
  have eR : PowerSeries.X *
        ((PowerSeries.C : ℚ →+* PowerSeries ℚ) (Nat.fib (2 ^ (1 - 1) + 1) : ℚ) -
          (PowerSeries.C : ℚ →+* PowerSeries ℚ) (Nat.fib (2 ^ (1 - 1) - 1) : ℚ) *
            PowerSeries.X) =
      PowerSeries.X ^ 1 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) (Nat.fib (2 ^ (1 - 1) + 1) : ℚ) -
        PowerSeries.X ^ 2 *
          (PowerSeries.C : ℚ →+* PowerSeries ℚ) (Nat.fib (2 ^ (1 - 1) - 1) : ℚ) := by
    ring
  have h2 := congrArg (fun f : PowerSeries ℚ => PowerSeries.coeff 2 f)
    (eL.symm.trans (h1.trans eR))
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_X_pow, PowerSeries.coeff_mul_C] at h2
  norm_num [hA1, hA2, hc] at h2
