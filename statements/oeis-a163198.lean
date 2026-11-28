import Mathlib

/-!
# A163198: Sum of the cubes of the first n even-indexed Fibonacci numbers

Source: https://oeis.org/A163198
Credit: @ivillar

Stuart Clary's sequence (offset 0): a(n) = Sum_{k=1..n} F(2k)^3, with F = A000045 (Mathlib's
`Nat.fib`).

The entry states (in the form listed with the conjecture, credited there to Wolfdieter Lang):
  a(n) = (F(2*n+1)-1)^2*(F(2*n+1) + 2)/4, n >= 0. See the Melham reference for a general
  conjecture.
This identity is formalized below, over ℚ (with exact division by 4).
-/

namespace OMA.S_oeis_a163198

/-- a(n) = Sum_{k=1..n} F(2k)^3 (offset 0). -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, Nat.fib (2 * k) ^ 3

/-- The stated formula a(n) = (F(2n+1)-1)^2*(F(2n+1)+2)/4, for every n ≥ 0. -/
theorem main : ∀ n : ℕ,
    (a n : ℚ) = ((Nat.fib (2 * n + 1) : ℚ) - 1) ^ 2 * ((Nat.fib (2 * n + 1) : ℚ) + 2) / 4 := by
  sorry

end OMA.S_oeis_a163198
