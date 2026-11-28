import Mathlib

/-!
# A195100: Numbers n such that there are no primes between (n-1)*sqrt(n-1) and n*sqrt(n).

Source: https://oeis.org/A195100
Credit: @keiichisince1986-bot

A195100 is the sequence `a(n)` named in the title. The entry states:
Cramér's conjecture implies that the sequence is finite. - Robert Israel, Aug 11 2014 (The statement
below is the claim that the sequence is finite, unconditionally.)

Conventions:
- As in the Mathematica program (`PrimePi[n Sqrt[n]] - PrimePi[(n-1) Sqrt[n-1]] == 0`), the interval is
  `((n-1)^(3/2), n^(3/2)]`; the upper end is never a prime anyway (it is irrational or a perfect cube).
- The square roots are real square roots (`Real.sqrt`).
-/

namespace OMA.S_oeis_a195100

theorem main :
    {n : ℕ | ¬ ∃ p : ℕ, p.Prime ∧ ((n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1) < p ∧
        (p : ℝ) ≤ n * Real.sqrt n}.Finite := by
  sorry

end OMA.S_oeis_a195100
