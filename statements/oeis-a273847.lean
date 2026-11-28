import Mathlib

/-!
# OEIS A273847: Barker's conjectures for the two-dimensional Rule 969

Source: https://oeis.org/A273847 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A273847 (Robert Price, Jun 01 2016), offset 0: Number of active (ON, black) cells in n-th
stage of growth of two-dimensional cellular automaton defined by Rule 969, based on the 5-celled
von Neumann neighborhood. Comment: Initialized with a single black (ON) cell at stage zero.
Formula section:
Conjectures from Colin Barker, Jun 01 2016:
a(n) = (1+2*n)^2 for n>4.
a(n) = 3*a(n-1)-3*a(n-2)+a(n-3) for n>7.
G.f.: (1+x+12*x^2-7*x^3+7*x^5-11*x^6+5*x^7) / (1-x)^3.

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
* The statement is the conjunction of the three conjectures; the recurrence is stated in the
  integers. The generating function is A(x) = Sum_{n >= 0} a(n) x^n in the formal power series
  ring over the rationals, and the identity is A = N * D⁻¹, where D has constant term 1.
* Controls from the entry: the definition gives 1, 4, 21, 45, 76 for n = 0..4.
-/

namespace OMA.S_oeis_a273847

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

/-- A273847(n). -/
noncomputable def a (n : ℕ) : ℕ := count (state 969 n) n

/-- The generating function Sum_{n >= 0} a(n) x^n. -/
noncomputable def A : ℚ⟦X⟧ := PowerSeries.mk fun n => (a n : ℚ)

/-- Barker's closed form, recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 4 < n → a n = (1 + 2 * n) ^ 2) ∧
    (∀ n : ℕ, 7 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) ∧
    A = (1 + X + 12 * X ^ 2 - 7 * X ^ 3 + 7 * X ^ 5 - 11 * X ^ 6 + 5 * X ^ 7) *
      ((1 - X) ^ 3)⁻¹ := by
  sorry

end OMA.S_oeis_a273847
