import Mathlib

/-!
# Successive quotients of A130095

OEIS A130095 is the inverse Möbius transform of the odd-indexed Fibonacci
numbers, beginning at index 1. Peter Bala gives the equivalent divisor sum
used below. The entry conjectures that a(n)/a(n-1) tends to φ².

Source: https://oeis.org/A130095
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a130095
open Filter Topology

def term (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, Nat.fib (2*d-1)

theorem main :
    Tendsto (fun n : ℕ => (term n : ℝ)/(term (n-1) : ℝ)) atTop
      (𝓝 (Real.goldenRatio^2)) := by
  sorry

end OMA.S_oeis_a130095
