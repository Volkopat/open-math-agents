import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Nat.Fib.Basic

/-!
# Mathar's recurrence for the Catalan–Fibonacci convolution

Antti Karttunen's sequence starts at zero and is the ordinary convolution
of the Catalan and Fibonacci numbers, with `fib 0 = 0`. R. J. Mathar's
four-term recurrence uses `a (n-3)`, so it starts at index three.
Its coefficients are interpreted in the integers.

Source: https://oeis.org/A090826. Formalization by @anmolspace.
-/

namespace OMA.S_oeis_a090826

def a (n : ℕ) : ℕ := ∑ j ∈ Finset.range (n+1), catalan j * Nat.fib (n-j)

theorem main : ∀ n : ℕ, 3 ≤ n →
    (n : ℤ)*a n + (-5*(n : ℤ)+6)*a (n-1) + 3*((n : ℤ)-2)*a (n-2)
      + 2*(2*(n : ℤ)-3)*a (n-3) = 0 := by
  sorry

end OMA.S_oeis_a090826
