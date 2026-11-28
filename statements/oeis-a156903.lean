import Mathlib

/-!
# Preservation of membership in OEIS A156903

Source: https://oeis.org/A156903
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A156/A156903.seq
Credit: @Heart-galaxy

A156903 contains the abundant numbers whose abundance is odd. We use the
equivalent description in the entry, abundance together with an odd sum of
divisors, because the abundance differs from that sum by the even number 2*n.

Sergey Pavlov conjectured preservation under multiplication by 100 in 2017.
Giovanni Resta resolved it in 2018 and gave the stated closures under a
positive square and under twice a positive square.
-/

namespace OMA.S_oeis_a156903

open Finset
open scoped ArithmeticFunction.sigma

def InSequence (n : ℕ) : Prop := n.Abundant ∧ Odd (σ 1 n)

theorem main :
    (∀ n : ℕ, InSequence n → InSequence (100 * n)) ∧
    (∀ n : ℕ, InSequence n → ∀ t : ℕ, 0 < t →
      InSequence (t ^ 2 * n) ∧ InSequence (2 * t ^ 2 * n)) := by
  sorry

end OMA.S_oeis_a156903
