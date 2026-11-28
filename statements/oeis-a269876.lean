import Mathlib

/-!
# OEIS A269876: Barker's conjectures for the two-dimensional Rule 43

Source: https://oeis.org/A269876 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A269876 (Robert Price, Mar 06 2016), offset 0: Number of active (ON, black) cells in n-th
stage of growth of two-dimensional cellular automaton defined by Rule 43, based on the 5-celled
von Neumann neighborhood. Comment: Initialized with a single black (ON) cell at stage zero.
Formula section:
Conjectures from Colin Barker, Mar 08 2016:
a(n) = (1+3*(-1)^n-2*(-3+(-1)^n)*n+(8-6*(-1)^n)*n^2)/4.
a(n) = (n^2+2*n+2)/2 for n even.
a(n) = (7*n^2+4*n-1)/2 for n odd.
a(n) = 3*a(n-2)-3*a(n-4)+a(n-6) for n>5.
G.f.: (1+5*x+2*x^2+22*x^3+x^4+x^5) / ((1-x)^3*(1+x)^3).

Formalization notes:
* Rule numbering: Wolfram's outer totalistic code for the 5-cell von Neumann neighborhood, as in
  the entry's program (CAStep with the kernel {{0,2,0},{2,1,2},{0,2,0}}): the new state of a cell
  is bit s + 2k of the rule number, where s is its own state (1 for ON) and k the number of ON
  cells among its four orthogonal neighbors.
* Initial condition: at stage 0 the origin is ON and every other cell of the plane Z^2 is OFF;
  each stage applies the rule to every cell, so the background evolves with the rule. The entry's
  program runs on a finite torus of side 2*128+1, which agrees with the plane for the stages
  listed.
* Counting convention: a(n) is the number of ON cells of stage n in the square [-n, n]^2, as the
  entry's program trims stage n to its central (2n+1) x (2n+1) square before counting.
* The statement is the conjunction of the five conjectures. The closed forms are stated in the
  integers with integer division; every numerator is divisible by its denominator (for n = 2m
  the numerators of the first and second forms are 8m^2+8m+4 and 4m^2+4m+2, and for n = 2m+1
  those of the first and third forms are 56m^2+72m+20 and 28m^2+36m+10), so the divisions are
  exact. The recurrence is stated in the integers. Since the
  denominator of the generating function has constant term 1, the identity A(x) = N/D for
  A(x) = Sum_{n >= 0} a(n) x^n is stated as A * D = N in the formal power series ring over the
  integers.
* Controls from the entry: the definition gives a(0) = 1 and a(1) = 5.
-/

namespace OMA.S_oeis_a269876

open PowerSeries

/-- The outer totalistic rule: bit s + 2k of the rule number r. -/
def rule (r : ℕ) (s : Bool) (k : ℕ) : Bool := r.testBit (s.toNat + 2 * k)

/-- Stage n of rule r from a single ON cell at the origin, the rule applied to every cell. -/
def grid (r : ℕ) : ℕ → ℤ → ℤ → Bool
  | 0 => fun i j => decide (i = 0 ∧ j = 0)
  | n + 1 => fun i j => rule r (grid r n i j)
      ((grid r n (i - 1) j).toNat + (grid r n (i + 1) j).toNat + (grid r n i (j - 1)).toNat +
        (grid r n i (j + 1)).toNat)

/-- A269876(n): the number of ON cells of stage n of Rule 43 on [-n, n]^2. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (2 * n + 1) ×ˢ Finset.range (2 * n + 1)).filter
    (fun p : ℕ × ℕ => grid 43 n ((p.1 : ℤ) - n) ((p.2 : ℤ) - n) = true)).card

/-- Barker's closed forms, recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, (a n : ℤ) =
      (1 + 3 * (-1) ^ n - 2 * (-3 + (-1) ^ n) * n + (8 - 6 * (-1) ^ n) * n ^ 2) / 4) ∧
    (∀ n : ℕ, n % 2 = 0 → (a n : ℤ) = (n ^ 2 + 2 * n + 2) / 2) ∧
    (∀ n : ℕ, n % 2 = 1 → (a n : ℤ) = (7 * n ^ 2 + 4 * n - 1) / 2) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 3 * a (n - 2) - 3 * a (n - 4) + a (n - 6)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 3) =
      1 + 5 * X + 2 * X ^ 2 + 22 * X ^ 3 + X ^ 4 + X ^ 5 := by
  sorry

end OMA.S_oeis_a269876
