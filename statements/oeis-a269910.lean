import Mathlib

/-!
# OEIS A269910: Barker's conjectures for the two-dimensional Rule 3

Source: https://oeis.org/A269910 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A269910 (Robert Price, Mar 07 2016), offset 0: Number of active (ON, black) cells in n-th
stage of growth of two-dimensional cellular automaton defined by Rule 3, based on the 5-celled von
Neumann neighborhood. Comment: Initialized with a single black (ON) cell at stage zero.
Formula section:
Conjectures from Colin Barker, Mar 08 2016:
a(n) = (-1+2*(-1)^n-2*(-1+(-1)^n)*n-2*(-1+(-1)^n)*n^2).
a(n) = 1 for n even.
a(n) = 4*n^2+4*n-3 for n odd.
a(n) = 3*a(n-2)-3*a(n-4)+a(n-6) for n>5.
G.f.: (1+5*x-2*x^2+30*x^3+x^4-3*x^5) / ((1-x)^3*(1+x)^3).

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code for the 5-cell von Neumann neighborhood, as in
  the entry's program (CAStep with the kernel {{0,2,0},{2,1,2},{0,2,0}}): the new state of a cell
  is bit c + 2s of the rule number, where c is its own state (1 for ON) and s the number of ON
  cells among its four orthogonal neighbors.
* Initial condition: at stage 0 the origin is ON and every other cell of the plane Z^2 is OFF;
  each stage applies the rule to every cell, so the background evolves with the rule. The entry's
  program runs on a finite torus of side 2*128+1, which agrees with the plane for the stages
  listed.
* Counting convention: a(n) is the number of ON cells of stage n in the square |x|, |y| <= n, as
  the entry's program trims stage n to its central (2n+1) x (2n+1) square before counting.
* The statement is the conjunction of the five conjectures. The first closed form and the
  recurrence are stated in the integers. The generating function is A(x) = Sum_{n >= 0} a(n) x^n
  in the formal power series ring over the rationals, and the identity is A = N * D⁻¹, where D
  has constant term 1.
* Controls from the entry: the definition gives 1, 5, 1, 45, 1, 117 for n = 0..5.
-/

namespace OMA.S_oeis_a269910

open PowerSeries

/-- One step of the outer totalistic automaton with code rule on the von Neumann neighborhood. -/
def step (rule : ℕ) (s : ℤ × ℤ → Bool) (p : ℤ × ℤ) : Bool :=
  Nat.testBit rule ((s p).toNat + 2 * ((s (p.1 - 1, p.2)).toNat + (s (p.1 + 1, p.2)).toNat +
    (s (p.1, p.2 - 1)).toNat + (s (p.1, p.2 + 1)).toNat))

/-- Stage n of the automaton started from a single ON cell at the origin. -/
def state (rule : ℕ) : ℕ → ℤ × ℤ → Bool
  | 0 => fun p => decide (p.1 = 0 ∧ p.2 = 0)
  | n + 1 => step rule (state rule n)

/-- The number of ON cells of a stage in the square |x|, |y| <= n. -/
noncomputable def count (s : ℤ × ℤ → Bool) (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter fun p => s p = true).card

/-- A269910(n). -/
noncomputable def a (n : ℕ) : ℕ := count (state 3 n) n

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's closed forms, recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, (a n : ℤ) =
      -1 + 2 * (-1) ^ n - 2 * (-1 + (-1) ^ n) * n - 2 * (-1 + (-1) ^ n) * n ^ 2) ∧
    (∀ n : ℕ, Even n → a n = 1) ∧
    (∀ n : ℕ, Odd n → (a n : ℤ) = 4 * n ^ 2 + 4 * n - 3) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 3 * a (n - 2) - 3 * a (n - 4) + a (n - 6)) ∧
    A = (1 + 5 * X - 2 * X ^ 2 + 30 * X ^ 3 + X ^ 4 - 3 * X ^ 5) *
      ((1 - X) ^ 3 * (1 + X) ^ 3)⁻¹ := by
  sorry

end OMA.S_oeis_a269910
