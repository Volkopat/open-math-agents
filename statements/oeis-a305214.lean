import Mathlib

/-!
# A305214: some residue modulo n is not a sum of two cubes exactly when 7 or 9 divides n

Source: https://oeis.org/A305214 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A305214, offset 1: Numbers k such that A305212(k) is not zero. Data
7, 9, 14, 18, 21, 27, 28, 35, 36, 42, 45, 49, 54, 56, 63, 70, 72, 77, 81, 84, 90, 91, 98, ...
Entry A305212, comment: Number of integers d from 0 to n-1 such that x^3 + y^3 == d (mod n)
has no solutions in integers. Data 0, 0, 0, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 4, 0, 0, 0, 8, ...

Comments: Conjecture: These are simply the positive integers that are divisible by 7 or 9.

Formalization notes.
* A305212(n) is not zero if and only if there is a residue d modulo n for which
  x^3 + y^3 == d (mod n) has no solution. The residues are the elements of `ZMod n`, and a
  solution in integers modulo n is a pair x, y in `ZMod n`.
* `main` states for each n >= 1 that n is a term of A305214 if and only if 7 divides n or
  9 divides n.
-/

namespace OMA.S_oeis_a305214

/-- The conjecture on A305214: for n ≥ 1, some residue d modulo n is not a sum of two cubes
modulo n (that is, A305212(n) is not zero) if and only if n is divisible by 7 or by 9. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ((∃ d : ZMod n, ¬ ∃ x y : ZMod n, x ^ 3 + y ^ 3 = d) ↔ (7 ∣ n ∨ 9 ∣ n)) := by
  sorry

end OMA.S_oeis_a305214
