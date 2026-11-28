import Mathlib

/-!
# A071055: number of 0's in row n of the Rule 182 triangle
Source: https://oeis.org/A071055 (conjectures by Ralf Stephan, Mar 05 2004, and Falk Hueffner, Jul 26 2019)

a(n) (offset 0) is the number of 0's in the n-th row of the triangle A071038, the successive states
of the elementary cellular automaton Rule 182 (Wolfram code 182, binary 10110110) started from a
single ON cell at position 0 on an otherwise OFF line; row n consists of the 2n+1 cells at positions
-n..n, scanned here as positions j - n for j < 2n+1.

Conjectures (both are formalized):
1. a(n) = b(n+1), where b(0) = 0, b(2n) = b(n), b(2n+1) = 2b(n) + 2 - 2[n = 0].
2. a(n) = pext(n, n+1), where pext(x, mask) is the parallel bits extract operation: the bits of x
   at the positions where mask has a 1 are packed, in order, into the low bits of the result.
   It is defined here on unbounded natural numbers (no word-size truncation is needed).
-/

namespace OMA.S_oeis_a071055

/-- Rule 182: the new state of a cell with neighbourhood (l, c, r) is bit number
4l + 2c + r of the binary expansion of 182. -/
def rule182 (l c r : Bool) : Bool :=
  Nat.testBit 182 (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- `state t i`: is cell `i` ON in generation `t`? -/
def state : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | t + 1, i => rule182 (state t (i - 1)) (state t i) (state t (i + 1))

/-- A071055(n): number of OFF cells among positions -n..n in generation n. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (2 * n + 1)).filter fun j : ℕ => state n ((j : ℤ) - (n : ℤ)) = false).card

/-- b(0) = 0, b(2n) = b(n), b(2n+1) = 2b(n) + 2 - 2[n = 0]. -/
def b : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    if (k + 1) % 2 = 0 then b ((k + 1) / 2)
    else 2 * b ((k + 1) / 2) + 2 - (if (k + 1) / 2 = 0 then 2 else 0)

/-- Parallel bits extract: pext x 0 = 0; for mask m > 0, if the lowest bit of m is set, the lowest
bit of x becomes the lowest bit of the result, followed by pext (x/2) (m/2); otherwise the lowest
bit of x is skipped. -/
def pext : ℕ → ℕ → ℕ
  | _, 0 => 0
  | x, m + 1 =>
    if (m + 1) % 2 = 1 then x % 2 + 2 * pext (x / 2) ((m + 1) / 2)
    else pext (x / 2) ((m + 1) / 2)

theorem main : (∀ n : ℕ, a n = b (n + 1)) ∧ (∀ n : ℕ, a n = pext n (n + 1)) := by
  sorry

end OMA.S_oeis_a071055
