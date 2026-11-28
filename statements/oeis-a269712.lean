import Mathlib

/-!
# OEIS A269712: Barker's conjectures for the two-dimensional Rule 20 at stages 2^n - 1

Source: https://oeis.org/A269712 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A269712 (Robert Price, Mar 04 2016), offset 0: Number of active (ON, black) cells at stage
2^n-1 of the two-dimensional cellular automaton defined by Rule 20, based on the 5-celled von
Neumann neighborhood. Comment: Initialized with a single black (ON) cell at stage zero.
Formula section:
Conjectures from Colin Barker, Mar 08 2016:
a(n) = 4*(2^n-1) =A028399(n+2) for n>0.
a(n) = 3*a(n-1)-2*a(n-2) for n>2.
G.f.: (1+x+2*x^2) / ((1-x)*(1-2*x)).
Entry A028399: a(n) = 2^n - 4.

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code for the 5-cell von Neumann neighborhood, as in
  the entry's program (CAStep with the kernel {{0,2,0},{2,1,2},{0,2,0}}): the new state of a cell
  is bit c + 2s of the rule number, where c is its own state (1 for ON) and s the number of ON
  cells among its four orthogonal neighbors.
* Initial condition: at stage 0 the origin is ON and every other cell of the plane Z^2 is OFF;
  each stage applies the rule to every cell (Rule 20 keeps the background OFF). The entry's
  program runs on a finite torus of side 2*128+1, which agrees with the plane for the stages
  listed.
* Counting convention: as the program does (it trims stage t to its central (2t+1) X (2t+1)
  square and counts the ON cells there), count rule t is the number of ON cells of stage t in the
  square |x|, |y| <= t, and a(n) = count 20 (2^n - 1).
* The first conjecture is read as the chain a(n) = 4*(2^n - 1) and a(n) = A028399(n+2) for every
  n > 0, with A028399(n) = 2^n - 4 as in that entry; the closed forms and the recurrence are stated
  in the integers. Since the denominator of the generating function has constant term 1, the
  identity A(x) = N/D for A(x) = Sum_{n >= 0} a(n) x^n is stated as A * D = N in the formal power
  series ring over the integers.
* Controls from the entry, proved in the proof file: a(0..15) = 1, 4, 12, 28, 60, 124, 252, 508,
  1020, 2044, 4092, 8188, 16380, 32764, 65532, 131068.
-/

namespace OMA.S_oeis_a269712

open PowerSeries

/-- Stage t of the two-dimensional outer totalistic automaton `rule` (Wolfram's code for the 5-cell
von Neumann neighborhood) from a single ON cell at the origin. -/
def state (rule : ℕ) : ℕ → ℤ → ℤ → Bool
  | 0, x, y => decide (x = 0 ∧ y = 0)
  | t + 1, x, y => Nat.testBit rule ((state rule t x y).toNat + 2 * ((state rule t (x - 1) y).toNat +
      (state rule t (x + 1) y).toNat + (state rule t x (y - 1)).toNat + (state rule t x (y + 1)).toNat))

/-- The number of ON cells of stage t of the automaton `rule` in the square |x|, |y| <= t. -/
noncomputable def count (rule t : ℕ) : ℕ :=
  ((Finset.Icc (-(t : ℤ)) t ×ˢ Finset.Icc (-(t : ℤ)) t).filter
    (fun p => state rule t p.1 p.2 = true)).card

/-- A269712(n): the number of ON cells of stage 2^n - 1 of Rule 20 in its square. -/
noncomputable def a (n : ℕ) : ℕ := count 20 (2 ^ n - 1)

/-- A028399(n) = 2^n - 4. -/
def A028399 (n : ℕ) : ℤ := 2 ^ n - 4

/-- Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 0 < n → (a n : ℤ) = 4 * (2 ^ n - 1) ∧ (a n : ℤ) = A028399 (n + 2)) ∧
    (∀ n : ℕ, 2 < n → (a n : ℤ) = 3 * a (n - 1) - 2 * a (n - 2)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 - 2 * X)) = 1 + X + 2 * X ^ 2 := by
  sorry

end OMA.S_oeis_a269712
