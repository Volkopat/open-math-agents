import Mathlib

/-!
# A049481: Hardy-Littlewood asymptotic for primes p with p + 30 prime

Source: https://oeis.org/A049481
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Title: A049481: Primes p such that p + 30 is also prime.

Statement:
Assuming Polignac's conjecture and the first Hardy-Littlewood conjecture:
Limit_{n->oo} n * log(a(n)) / primepi(a(n)) = (16/3) * A005597 = 3.52086...

Conventions:
- `A005597` is the twin prime constant `C_2 = Product_{p >= 3 prime} (1 - 1 / (p - 1)^2)`.
- `primePi x` is the number of primes `<= x`.
-/

namespace OMA.S_oeis_a049481

/-- The `n`-th prime `p` such that `p + 30` is also prime (`A049481`, 0-indexed). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth (fun p => Nat.Prime p ∧ Nat.Prime (p + 30)) n

/-- The prime-counting function `pi(x)`. -/
noncomputable def primePi (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter Nat.Prime).card

/-- The twin prime constant `A005597 = Product_{p >= 3 prime} (1 - 1 / (p - 1)^2)`. -/
noncomputable def twinPrimeConst : ℝ :=
  ∏' (k : ℕ), (1 - (1 : ℝ) / ((Nat.nth Nat.Prime (k + 1) : ℝ) - 1) ^ 2)

theorem main :
    Filter.Tendsto
      (fun n : ℕ => ((n + 1 : ℝ) * Real.log (a n : ℝ)) / (primePi (a n) : ℝ))
      Filter.atTop (nhds ((16 / 3 : ℝ) * twinPrimeConst)) := by
  sorry

end OMA.S_oeis_a049481
