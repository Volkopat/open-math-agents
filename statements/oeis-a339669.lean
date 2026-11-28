import Mathlib

/-!
# A339669: number of Fibonacci divisors of Lucas(n)^2 + 1

Source: https://oeis.org/A339669 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A339669 (Michel Lagneau, Dec 12 2020), offset 0: number of Fibonacci divisors of
Lucas(n)^2 + 1. Data
2, 2, 3, 1, 3, 2, 3, 2, 5, 1, 5, 2, 4, 2, 5, 1, 5, 2, 4, 2, 6, 1, 6, 2, 4, 2, 6, 1, 6, 2, 4, 2, ...
Example: a(8) = 5 because Lucas(8)^2 + 1 = 47^2 + 1 = 2210 has the 5 Fibonacci divisors
1, 2, 5, 13 and 34.

Comments: we propose two conjectures verified for n < 156.
Conjecture 1: a(6*n+3) = 1.
Conjecture 2: a(6*n+1) = a(6*n+5) = 2.

Formalization notes.
* `lucas` is the sequence of Lucas numbers A000032: L(0) = 2, L(1) = 1, L(n+2) = L(n+1) + L(n).
* `a n` is the number of natural numbers d such that d divides Lucas(n)^2 + 1 and d is a
  Fibonacci number (d = `Nat.fib k` for some k). The count is `Set.ncard` of this finite set, so
  the Fibonacci number 1 = F(1) = F(2) is counted one time, as in the example of the entry.
* `main` is the conjunction of the two conjectures, for each n >= 0.
-/

namespace OMA.S_oeis_a339669

/-- The Lucas numbers A000032. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucas (n + 1) + lucas n

/-- A339669(n): the number of Fibonacci numbers that divide Lucas(n)^2 + 1. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {d : ℕ | d ∣ lucas n ^ 2 + 1 ∧ ∃ k : ℕ, Nat.fib k = d}

/-- a(6n+3) = 1 and a(6n+1) = a(6n+5) = 2. -/
theorem main : ∀ n : ℕ, a (6 * n + 3) = 1 ∧ a (6 * n + 1) = 2 ∧ a (6 * n + 5) = 2 := by
  sorry

end OMA.S_oeis_a339669
