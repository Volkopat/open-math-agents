import Mathlib

/-!
# A297293: the sequence c of a system of three complementary equations

Source: https://oeis.org/A297293 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A297293 (Clark Kimberling), offset 0: Solution (c(n)) of the system of 3 complementary
equations in Comments.
Data 2, 8, 10, 18, 24, 26, 33, 35, 42, 45, 54, 56, 63, 66, 74, 76, 82, 88, 94, 96, 102, 105, ...

Comments: Define sequences a(n), b(n), c(n) recursively:
a(n) = least new;
b(n) = least new > = a(n) + 2;
c(n) = a(n) + b(n) - 2;
where "least new k" means the least positive integer not yet placed.
The sequences a,b,c partition the positive integers.
Conjectures: for n >= 0,
0 <= 5*n + 4 - 2*a(n) <= 5,
0 <= 5*n + 8 - 2*b(n) <= 4,
0 <= c(n) - 5n <= 4.

Formalization notes.
* `leastNewFrom s t` is the least integer k >= t that is not in the finite set `s` of the
  numbers already placed. "Least new" is `leastNewFrom s 1` (the least positive integer not
  yet placed), and "least new >= a(n) + 2" is `leastNewFrom s (a(n) + 2)`.
* `step U` does one step from the set U of placed numbers: it places a, then b (the least new
  number >= a + 2, after a is placed), then c = a + b - 2.
* `state n` is the tuple (a(n), b(n), c(n), set of the numbers placed up to step n); step 0
  starts from the empty set. This gives a(0), b(0), c(0) = 1, 3, 2, then 4, 6, 8, then
  5, 7, 10, as in the data.
* `main` is the conjunction of the three two-sided bounds for each n >= 0 (inequalities in the
  integers).
-/

namespace OMA.S_oeis_a297293

/-- The least integer k >= t that is not yet placed. -/
noncomputable def leastNewFrom (s : Finset ℕ) (t : ℕ) : ℕ := sInf {k : ℕ | t ≤ k ∧ k ∉ s}

/-- One step from the set U of placed numbers: (a, b, c, new set of placed numbers). -/
noncomputable def step (U : Finset ℕ) : ℕ × ℕ × ℕ × Finset ℕ :=
  let A := leastNewFrom U 1
  let B := leastNewFrom (insert A U) (A + 2)
  (A, B, A + B - 2, insert (A + B - 2) (insert B (insert A U)))

/-- The state after step n: (a(n), b(n), c(n), set of the numbers placed so far). -/
noncomputable def state : ℕ → ℕ × ℕ × ℕ × Finset ℕ
  | 0 => step ∅
  | n + 1 => step (state n).2.2.2

noncomputable def a (n : ℕ) : ℕ := (state n).1
noncomputable def b (n : ℕ) : ℕ := (state n).2.1
/-- A297293. -/
noncomputable def c (n : ℕ) : ℕ := (state n).2.2.1

/-- Conjectures of Kimberling. -/
theorem main : ∀ n : ℕ,
    (0 ≤ 5 * (n : ℤ) + 4 - 2 * (a n : ℤ) ∧ 5 * (n : ℤ) + 4 - 2 * (a n : ℤ) ≤ 5) ∧
    (0 ≤ 5 * (n : ℤ) + 8 - 2 * (b n : ℤ) ∧ 5 * (n : ℤ) + 8 - 2 * (b n : ℤ) ≤ 4) ∧
    (0 ≤ (c n : ℤ) - 5 * (n : ℤ) ∧ (c n : ℤ) - 5 * (n : ℤ) ≤ 4) := by
  sorry

end OMA.S_oeis_a297293
