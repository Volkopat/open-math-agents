import Mathlib

/-!
# A297465: the sequence b of a system of four complementary equations

Source: https://oeis.org/A297465 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A297465 (Clark Kimberling), offset 0: Solution (b(n)) of the system of 4 complementary
equations in Comments.
Data 2, 5, 9, 12, 15, 19, 22, 25, 29, 32, 35, 39, 42, 45, 49, 52, 55, 59, 62, 65, 69, 72, ...

Comments: Define sequences a(n), b(n), c(n), d(n) recursively, starting with a(0) = 1,
b(0) = 2, c(0) = 3:
a(n) = least new;
b(n) = least new;
c(n) = least new;
d(n) = a(n) + b(n) + c(n);
where "least new k" means the least positive integer not yet placed.
Conjecture: for all n >= 0,
0 <= 10n - 6 - 3 a(n) <= 2
0 <= 10n - 2 - 3 b(n) <= 3
0 <= 10n + 1 - 3 c(n) <= 3
0 <= 10n - 3 - d(n) <= 2

Formalization notes.
* `leastNew s` is the least positive integer that is not in the finite set `s` of the numbers
  already placed.
* `state n` is the tuple (a(n), b(n), c(n), d(n), set of the numbers placed up to step n).
  Step 0 places a(0) = 1, b(0) = 2, c(0) = 3 and d(0) = 1 + 2 + 3 = 6. In step n + 1 the
  numbers are placed in the order a, b, c, d: each of a, b, c is the least new number at its
  turn, and then d = a + b + c is placed.
* Index shift. With the offset 0 of the entry the four inequalities are false as written:
  for n = 0 they give 10*0 - 6 - 3*a(0) = -9, and the left sides are -10, ..., -7 for each n.
  The inequalities hold when the terms are counted from 1 (first terms a = 1, b = 2, c = 3,
  d = 6 give 10 - 6 - 3 = 1, 10 - 2 - 6 = 2, 10 + 1 - 9 = 2, 10 - 3 - 6 = 1). So with the
  offset 0 of the entry the conjecture is, for all n >= 0:
  0 <= 10(n+1) - 6 - 3 a(n) <= 2, 0 <= 10(n+1) - 2 - 3 b(n) <= 3,
  0 <= 10(n+1) + 1 - 3 c(n) <= 3, 0 <= 10(n+1) - 3 - d(n) <= 2.
  This is the form in `main` (inequalities in the integers).
-/

namespace OMA.S_oeis_a297465

/-- The least positive integer that is not yet placed. -/
noncomputable def leastNew (s : Finset ℕ) : ℕ := sInf {k : ℕ | 0 < k ∧ k ∉ s}

/-- The state after step n: (a(n), b(n), c(n), d(n), set of the numbers placed so far). -/
noncomputable def state : ℕ → ℕ × ℕ × ℕ × ℕ × Finset ℕ
  | 0 => (1, 2, 3, 6, {1, 2, 3, 6})
  | n + 1 =>
    let U := (state n).2.2.2.2
    let A := leastNew U
    let B := leastNew (insert A U)
    let C := leastNew (insert B (insert A U))
    (A, B, C, A + B + C, insert (A + B + C) (insert C (insert B (insert A U))))

noncomputable def a (n : ℕ) : ℕ := (state n).1
/-- A297465. -/
noncomputable def b (n : ℕ) : ℕ := (state n).2.1
noncomputable def c (n : ℕ) : ℕ := (state n).2.2.1
noncomputable def d (n : ℕ) : ℕ := (state n).2.2.2.1

/-- Conjecture of Kimberling (terms counted from 1, see the notes). -/
theorem main : ∀ n : ℕ,
    (0 ≤ 10 * ((n : ℤ) + 1) - 6 - 3 * (a n : ℤ) ∧ 10 * ((n : ℤ) + 1) - 6 - 3 * (a n : ℤ) ≤ 2) ∧
    (0 ≤ 10 * ((n : ℤ) + 1) - 2 - 3 * (b n : ℤ) ∧ 10 * ((n : ℤ) + 1) - 2 - 3 * (b n : ℤ) ≤ 3) ∧
    (0 ≤ 10 * ((n : ℤ) + 1) + 1 - 3 * (c n : ℤ) ∧ 10 * ((n : ℤ) + 1) + 1 - 3 * (c n : ℤ) ≤ 3) ∧
    (0 ≤ 10 * ((n : ℤ) + 1) - 3 - (d n : ℤ) ∧ 10 * ((n : ℤ) + 1) - 3 - (d n : ℤ) ≤ 2) := by
  sorry

end OMA.S_oeis_a297465
