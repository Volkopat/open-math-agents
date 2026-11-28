import Mathlib

/-!
# OEIS A269729: the sequence is its own inverse

Source: https://oeis.org/A269729 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (N. J. A. Sloane, Mar 08 2016), offset 0: a(n) = row number of extended Wythoff array (see
A035513) which contains the sequence obtained by reading the n-th row backwards (and adjusting
signs). Comment: Conjecture: sequence is its own inverse. (R. J. Mathar, May 08 2019.)
Example: Take n=5: reading row 5 of A035513 backwards gives ... 23, 14, 9, 5, 4, 1, 3, -2, 5,
-7, 12, -19, ..., which after adjusting the signs is row 7, so a(5) = 7.
The entry's program uses W[n, k] = Fibonacci[k+1] Floor[n GoldenRatio] + (n-1) Fibonacci[k] for
the Wythoff array (rows n >= 1), extended to all integer columns k, and reports row n as n - 1.

Formalization notes:
* Row r (counted from 0, so row r is the program's row r + 1) at column k in ℤ is
  W(r, k) = F(k+1) floor((r+1) phi) + r F(k), with F = `Int.fib` the Fibonacci numbers on ℤ
  (F(-k) = (-1)^(k+1) F(k), as Mathematica's Fibonacci) and phi the golden ratio. Columns -1 and 0
  hold r and floor((r+1) phi), the two extra columns of the extended array.
* Row n read backwards with the signs adjusted is k |-> (-1)^k W(n, -k).
* A row contains a two-sided Fibonacci-type sequence when it equals it after a shift of the
  columns, up to a global sign (the adjustment of signs). a(n) is the least such row; the proof
  file shows that exactly one row qualifies, so the least is the only one.
* `main` is the conjecture: a(a(n)) = n for every n >= 0.
* Controls proved in the proof file: a(0) = 0 and a(5) = 7 (the entry's example).
-/

namespace OMA.S_oeis_a269729

/-- Row r (counted from 0) of the extended Wythoff array, at column k in ℤ:
W(r, k) = F(k+1) floor((r+1) phi) + r F(k), with F the Fibonacci numbers on ℤ. -/
noncomputable def W (r : ℕ) (k : ℤ) : ℤ :=
  Int.fib (k + 1) * ⌊((r : ℝ) + 1) * Real.goldenRatio⌋ + (r : ℤ) * Int.fib k

/-- Row n read backwards, with the signs adjusted: k ↦ (-1)^k W(n, -k). -/
noncomputable def rev (n : ℕ) (k : ℤ) : ℤ := (-1) ^ k.natAbs * W n (-k)

/-- A269729(n): the row of the extended Wythoff array that contains row n read backwards, that
is, equals it up to a shift of the columns and a sign. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {r : ℕ | ∃ s : ℤ, (∀ k : ℤ, W r k = rev n (k + s)) ∨ (∀ k : ℤ, W r k = -rev n (k + s))}

/-- Mathar's conjecture: the sequence is its own inverse. -/
theorem main : ∀ n : ℕ, a (a n) = n := by
  sorry

end OMA.S_oeis_a269729
