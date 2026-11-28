import Mathlib

/-!
# A326663: the column c of the solution of c(n) = a(n) + b(2n)

Source: https://oeis.org/A326663 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A326663 (Clark Kimberling), offset 1: Column 3 of the array at A309157; see Comments.
Data 5, 12, 20, 26, 33, 41, 47, 54, 61, 68, 75, 83, 89, 96, 104, 110, 117, 124, 131, 138, ...

Comments: This is the sequence (c(n)) defined by the complementary equation
c(n) = a(n) + b(2n), with initial value a(1) = 1. See A309157.
Conjecture: 7n-c(n) is in {1,2} for all n.

Related entry A309157: Rectangular array in 3 columns that solve the complementary equation
c(n) = a(n) + b(2n), where a(1) = 1. Let A = (a(n)), B = (b(n)), and C = (c(n)). A unique
solution (A,B,C) exists for these conditions: (1) A,B,C must partition the positive integers,
and (2) A and B are defined by mex (minimal excludant); that is, a(n) is the least "new"
positive integer, and likewise for b(n). Example: a(2) = mex{1,2} = 3; b(2) = mex{1,2,3} = 4;
c(1) = 5. Then a(3) = 6, b(3) = 7; a(4) = 8, b(4) = 9; c(2) = a(2) + b(4) = 3 + 9 = 12.
Rows (a(n), b(n), c(n)): (1, 2, 5), (3, 4, 12), (6, 7, 20), (8, 9, 26), (10, 11, 33),
(13, 14, 41), (15, 16, 47), (17, 18, 54), (19, 21, 61), ...

Formalization notes.
* `leastNew s` is the least positive integer that is not in the finite set `s` of the numbers
  already placed (the mex over the positive integers).
* The solution is generated in steps, as in the example of A309157. Step n (n >= 1) places
  a(2n-1), b(2n-1), a(2n), b(2n) in this order, each as the least new number at its turn, and
  then places c(n) = a(n) + b(2n) (the value a(n) is known at this time, because n <= 2n).
  This gives the rows above: step 1 places 1, 2, 3, 4 and c(1) = 1 + 4 = 5; step 2 places
  6, 7, 8, 9 and c(2) = 3 + 9 = 12; step 3 places 10, 11, 13, 14 and c(3) = 6 + 14 = 20.
* `state n` is the tuple (the function a on the indices placed so far, the function b on the
  indices placed so far, c(n), set of the numbers placed up to step n). The functions have
  the value 0 at the indices that are not yet placed; `state 0` is the empty start.
* `main` is the conjecture: for each n >= 1, 7n - c(n) is 1 or 2.
-/

namespace OMA.S_oeis_a326663

/-- The least positive integer that is not yet placed. -/
noncomputable def leastNew (s : Finset ℕ) : ℕ := sInf {k : ℕ | 0 < k ∧ k ∉ s}

/-- The state after step n: (a on the indices up to 2n, b on the indices up to 2n, c(n),
placed numbers). -/
noncomputable def state : ℕ → (ℕ → ℕ) × (ℕ → ℕ) × ℕ × Finset ℕ
  | 0 => (fun _ => 0, fun _ => 0, 0, ∅)
  | n + 1 =>
    let U := (state n).2.2.2
    let A1 := leastNew U
    let B1 := leastNew (insert A1 U)
    let A2 := leastNew (insert B1 (insert A1 U))
    let B2 := leastNew (insert A2 (insert B1 (insert A1 U)))
    let α := Function.update (Function.update (state n).1 (2 * n + 1) A1) (2 * n + 2) A2
    let β := Function.update (Function.update (state n).2.1 (2 * n + 1) B1) (2 * n + 2) B2
    (α, β, α (n + 1) + β (2 * n + 2),
      insert (α (n + 1) + β (2 * n + 2)) (insert B2 (insert A2 (insert B1 (insert A1 U)))))

/-- A326663. -/
noncomputable def c (n : ℕ) : ℕ := (state n).2.2.1

/-- Conjecture of Kimberling: 7n - c(n) is in {1, 2}. -/
theorem main : ∀ n : ℕ, 1 ≤ n → c n + 1 = 7 * n ∨ c n + 2 = 7 * n := by
  sorry

end OMA.S_oeis_a326663
