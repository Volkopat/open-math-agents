import Mathlib

/-!
# A297469: the sequence bb of a system of three complementary equations

Source: https://oeis.org/A297469 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A297469 (Clark Kimberling, May 04 2018), offset 0: Solution (bb(n)) of the system of 3
complementary equations in Comments.
Data 2, 7, 11, 17, 22, 27, 31, 37, 41, 47, 51, 57, 62, 67, 71, 77, 82, 87, 91, 97, 102, 107, ...

Comments: Define sequences aa(n), bb(n), cc(n) recursively, starting with aa(0) = 1,
bb(0) = 2, cc(0) = 3:
aa(n) = least new;
bb(n) = aa(n) + cc(n-1);
cc(n) = least new;
where "least new k" means the least positive integer not yet placed.

From N. J. A. Sloane, Nov 05 2019: Conjecture: For t >= 0, bb(2t) = 10t + 1 (+1 if binary
expansion of t ends in an odd number of 0's), bb(2t+1) = 10t + 7.

Formalization notes.
* `leastNew s` is the least positive integer that is not in the finite set `s` of the numbers
  already placed.
* `state n` is the tuple (aa(n), bb(n), cc(n), set of the numbers placed up to step n). Step 0
  places 1, 2, 3. In step n + 1 the numbers are placed in the order aa, bb, cc: aa(n+1) is
  the least new number, bb(n+1) = aa(n+1) + cc(n), and cc(n+1) is the least new number after
  aa(n+1) and bb(n+1) are placed.
* The number of 0's at the end of the binary expansion of t >= 1 is the exponent of 2 in t,
  `padicValNat 2 t`. For t = 0 the first formula is not stated (the binary expansion of 0 has
  no clear number of final zeros; the value bb(0) = 2 is an initial condition).
* `main` is the conjecture: bb(2t) = 10t + 1 + [the exponent of 2 in t is odd] for t >= 1, and
  bb(2t+1) = 10t + 7 for t >= 0.
-/

namespace OMA.S_oeis_a297469

/-- The least positive integer that is not yet placed. -/
noncomputable def leastNew (s : Finset ℕ) : ℕ := sInf {k : ℕ | 0 < k ∧ k ∉ s}

/-- The state after step n: (aa(n), bb(n), cc(n), set of the numbers placed so far). -/
noncomputable def state : ℕ → ℕ × ℕ × ℕ × Finset ℕ
  | 0 => (1, 2, 3, {1, 2, 3})
  | n + 1 =>
    let A := leastNew (state n).2.2.2
    let B := A + (state n).2.2.1
    let C := leastNew (insert B (insert A (state n).2.2.2))
    (A, B, C, insert C (insert B (insert A (state n).2.2.2)))

/-- A297469. -/
noncomputable def bb (n : ℕ) : ℕ := (state n).2.1

/-- Conjecture of Sloane. -/
theorem main :
    (∀ t : ℕ, 1 ≤ t → bb (2 * t) = 10 * t + 1 + if Odd (padicValNat 2 t) then 1 else 0) ∧
    (∀ t : ℕ, bb (2 * t + 1) = 10 * t + 7) := by
  sorry

end OMA.S_oeis_a297469
