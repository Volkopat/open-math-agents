import Mathlib

/-!
# Limits for the sum of Fibonacci remainders

A072523 sums the remainders of the nth Fibonacci number upon division by each
smaller Fibonacci number exceeding one. In the sum below the divisor index is
`n-(k+1)`, running backwards over the earlier Fibonacci numbers. Indices below
three supply no divisor. McGarvey conjectured both displayed limits.

Source: https://oeis.org/A072523 (OEIS Foundation, CC BY-SA 4.0)
Credit: @connoranderson
-/

namespace OMA.S_oeis_a072523
open Filter Topology

def remainder (n k : ℕ) : ℕ :=
  if 3 ≤ n-(k+1) then n.fib % (n-(k+1)).fib else 0

def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, remainder n k

theorem main :
    Tendsto (fun n : ℕ => (n.fib:ℝ) / a n) atTop (𝓝 (Real.sqrt 5/2)) ∧
    Tendsto (fun n : ℕ => (a n:ℝ) / a (n-1)) atTop (𝓝 Real.goldenRatio) := by
  sorry

end OMA.S_oeis_a072523
