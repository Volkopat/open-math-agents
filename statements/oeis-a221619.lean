import Mathlib

/-!
# OEIS A221619: Barker's generating function and closed form for rows of nondecreasing descents

Source: https://oeis.org/A221619 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 21 2013), offset 1: Number of n X 4 arrays with each row a permutation
of 1..4 having at least as many downsteps as the preceding row. Data: 24, 410, 6120, 85035,
1130256, ... Formula: Empirical: a(n) = 24*a(n-1) - 166*a(n-2) + 264*a(n-3) - 121*a(n-4).
Conjectures from Colin Barker, Aug 09 2018: (Start) G.f.: x*(12 - 11*x)*(2 - 12*x + 11*x^2) /
((1 - x)^2*(1 - 11*x)^2). a(n) = (4*(4+11^(2+n)) + 5*(1+11^(2+n))*n) / 500. (End)

Formalization notes:
* A row is a permutation p of Fin 4, read as the row p(0)+1, p(1)+1, p(2)+1, p(3)+1 (a permutation
  of 1..4; the shift by 1 does not change downsteps). Its downsteps are the positions i in 0..2
  with p(i + 1) < p(i).
* An n X 4 array is a function from the n rows to permutations; the condition is that row i + 1
  has at least as many downsteps as row i, for every i.
* The g.f. is Sum_{n >= 1} a(n) x^n (offset 1). The identity A(x) = N(x)/D(x) is stated as
  A(x) D(x) = N(x) in Z[[x]], which is equivalent because D = (1 - x)^2 (1 - 11x)^2 has
  constant term 1.
* `main` is the conjunction of Barker's two conjectures; the closed form is stated in the
  rationals for every n >= 1.
* Controls proved in the proof file: a(1..4) = 24, 410, 6120, 85035, and the numbers of rows with
  0, 1, 2, 3 downsteps, 1, 11, 11, 1.
-/

namespace OMA.S_oeis_a221619

open PowerSeries Finset

/-- The number of downsteps of a row p: the positions i in 0..2 with p(i + 1) < p(i). -/
def des (p : Equiv.Perm (Fin 4)) : ℕ :=
  ((Finset.univ : Finset (Fin 3)).filter (fun i => p i.succ < p i.castSucc)).card

/-- A221619(n): the number of n X 4 arrays whose rows are permutations, every row having at
least as many downsteps as the preceding row. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Equiv.Perm (Fin 4))).filter
    (fun f => ∀ i j : Fin n, j.val = i.val + 1 → des (f i) ≤ des (f j))).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) *
      ((1 - X) ^ 2 * (1 - 11 * X) ^ 2) = X * (12 - 11 * X) * (2 - 12 * X + 11 * X ^ 2) ∧
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℚ) = (4 * (4 + 11 ^ (2 + n)) + 5 * (1 + 11 ^ (2 + n)) * n) / 500 := by
  sorry

end OMA.S_oeis_a221619
