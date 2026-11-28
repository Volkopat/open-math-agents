import Mathlib

/-!
# Detlefs's Fibonacci product for the antidiagonals of A035317

We use the Fibonacci convolution formula for A080239 recorded by Johannes
W. Meijer in the entry. The harmless final summand at a multiple of four is
`F 0 = 0`. The two four-periodic functions in Detlefs's conjecture are written
by their residue values. His Fourier notation `r4(1,0,3,2,n)` takes values
2,1,0,3 at residues 0,1,2,3, and `r4(0,0,1,0,n)` detects residue 3.

Source: https://oeis.org/A080239 (OEIS Foundation, CC BY-SA 4.0)
Credit: @connoranderson
-/

namespace OMA.S_oeis_a080239

def a (n : ℕ) : ℕ := ∑ j ∈ Finset.range (n/4+1), (n-4*j).fib

def p (n : ℕ) : ℕ := 2*((n+3)/2 - (n+3)/4)

def q (n : ℕ) : ℕ := match n%4 with
  | 0 => 2
  | 1 => 1
  | 2 => 0
  | _ => 3

theorem main : ∀ n : ℕ, 1 ≤ n →
    a n = (p n).fib * (p n-q n).fib - (if n%4=3 then 1 else 0) := by
  sorry

end OMA.S_oeis_a080239
