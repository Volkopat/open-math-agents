import Mathlib

/-!
# A309231: the column c of the solution of c(n) = a(2n) + b(2n)

Source: https://oeis.org/A309231 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A309231 (Clark Kimberling), offset 1: Column 3 of the array at A326662 see Comments.
Data 7, 17, 25, 34, 43, 53, 61, 71, 79, 89, 97, 106, 115, 125, 133, 142, 151, 161, 169, 178, ...

Comments: This is the sequence (c(n)) defined by the complementary equation
c(n) = a(2n) + b(2n), with initial value a(1) = 1. See A326662.
Conjecture: 9n-c(n) is in {1,2} for all n.

Related entry A326662: Rectangular array in 3 columns that solve the complementary equation
c(n) = a(2n) + b(2n), where a(1) = 1. Let A = (a(n)), B = (b(n)), and C = (c(n)). A unique
solution (A,B,C) exists for the following conditions: (1) A,B,C must partition the positive
integers, and (2) A and B are defined by mex (minimal excludant); that is, a(n) is the least
"new" positive integer, and likewise for b(n). Example: b(1) = mex{1} = 2; a(2) = mex{1,2} = 3;
b(2) = mex{1,2,3} = 4; ... c(1) = 7. Rows (a(n), b(n), c(n)): (1, 2, 7), (3, 4, 17), (5, 6, 25),
(8, 9, 34), (10, 11, 43), (12, 13, 53), (14, 15, 61), (16, 18, 71), (19, 20, 79), ...

Formalization notes.
* `leastNew s` is the least positive integer that is not in the finite set `s` of the numbers
  already placed (the mex over the positive integers).
* The solution is generated in steps, as in the example of A326662. Step n (n >= 1) places
  a(2n-1), b(2n-1), a(2n), b(2n) in this order, each as the least new number at its turn, and
  then places c(n) = a(2n) + b(2n). This gives the rows above: step 1 places 1, 2, 3, 4 and
  c(1) = 7; step 2 places 5, 6, 8, 9 and c(2) = 17; and so on.
* `state n` is the tuple (a(2n-1), b(2n-1), a(2n), b(2n), c(n), set of the numbers placed up to
  step n); `state 0` is the empty start (no number placed, entries 0).
* `main` is the conjecture: for each n >= 1, 9n - c(n) is 1 or 2.
-/

namespace OMA.S_oeis_a309231

/-- The least positive integer that is not yet placed. -/
noncomputable def leastNew (s : Finset ℕ) : ℕ := sInf {k : ℕ | 0 < k ∧ k ∉ s}

/-- The state after step n: (a(2n-1), b(2n-1), a(2n), b(2n), c(n), placed numbers). -/
noncomputable def state : ℕ → ℕ × ℕ × ℕ × ℕ × ℕ × Finset ℕ
  | 0 => (0, 0, 0, 0, 0, ∅)
  | n + 1 =>
    let U := (state n).2.2.2.2.2
    let A1 := leastNew U
    let B1 := leastNew (insert A1 U)
    let A2 := leastNew (insert B1 (insert A1 U))
    let B2 := leastNew (insert A2 (insert B1 (insert A1 U)))
    (A1, B1, A2, B2, A2 + B2, insert (A2 + B2) (insert B2 (insert A2 (insert B1 (insert A1 U)))))

/-- A309231. -/
noncomputable def c (n : ℕ) : ℕ := (state n).2.2.2.2.1

/-- Conjecture of Kimberling: 9n - c(n) is in {1, 2}. -/
theorem main : ∀ n : ℕ, 1 ≤ n → c n + 1 = 9 * n ∨ c n + 2 = 9 * n := by
  sorry

end OMA.S_oeis_a309231
