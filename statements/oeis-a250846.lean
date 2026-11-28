import Mathlib

/-!
# OEIS A250846: Barker's g.f. for (n+1) X 2 0..3 arrays with nondecreasing horizontal differences down the columns and nondecreasing vertical minima along the rows

Source: https://oeis.org/A250846 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A250846 (R. H. Hardin, Nov 28 2014), offset 1: Number of (n+1) X (1+1) 0..3 arrays with
nondecreasing x(i,j)-x(i,j-1) in the i direction and nondecreasing min(x(i,j),x(i-1,j)) in the j
direction. Column 1 of A250853. Data: 100, 543, 2670, 12311, 54410, 233683, ... Formula section:
Empirical: a(n) = 10*a(n-1) -35*a(n-2) +50*a(n-3) -24*a(n-4); a(n) = (832*4^n-846*3^n+204*2^n+2)/12.
G.f.: x*(100 - 457*x + 740*x^2 - 384*x^3) / ((1 - x)*(1 - 2*x)*(1 - 3*x)*(1 - 4*x)) (conjectured). -
Colin Barker, Jan 18 2018

Formalization notes:
* An array is a function x : Fin (n + 1) -> Fin 2 -> Fin 4, x i j being the element in row i and
  column j. The entry indexes the conditions by the later cell: x(i,j)-x(i,j-1) nondecreasing in the
  i direction means that for consecutive columns j - 1, j the difference does not decrease as i
  grows, here x(i,j') - x(i,j) <= x(i',j') - x(i',j) for i' = i + 1, j' = j + 1 (differences in Z);
  min(x(i,j),x(i-1,j)) nondecreasing in the j direction means min(x(i,j), x(i',j)) <= min(x(i,j'),
  x(i',j')). This reading reproduces the entry's data and the whole table A250853 (brute force over
  all arrays for small sizes, a row transfer for the rest); the reading with the two directions
  exchanged does not.
* The live problem block of the site lists Barker's g.f. only (Hardin's lines are empirical and are
  not part of it); `main` states the g.f. as A(x) (1 - x)(1 - 2x)(1 - 3x)(1 - 4x) = x(100 - 457x +
  740x^2 - 384x^3) in Q[[x]], with A(x) = Sum_{n >= 1} a(n) x^n (offset 1), which is equivalent to
  the quotient form because the denominator has constant term 1.
* Controls proved in the proof file: a(1..20) = 100, 543, 2670, 12311, 54410, 233683, 983950,
  4085631, 16796370, 68555723, 278351030, 1125823351, 4540620730, 18274604163, 73435058910,
  294750719471, 1182035443490, 4737241699003, 18976271027590, 75987005717991, the entry's data.
-/

namespace OMA.S_oeis_a250846

open PowerSeries

/-- A250846(n): the number of (n+1) X 2 arrays x with entries 0..3 (x i j in row i and column j)
such that for consecutive rows i, i' = i + 1 and consecutive columns j, j' = j + 1 the difference
x(i,j') - x(i,j) does not decrease from row i to row i' (nondecreasing x(i,j)-x(i,j-1) in the i
direction) and min(x(i,j), x(i',j)) does not decrease from column j to column j' (nondecreasing
min(x(i,j),x(i-1,j)) in the j direction). -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (n + 1) → Fin 2 → Fin 4)).filter (fun x =>
    ∀ i i' : Fin (n + 1), i'.val = i.val + 1 → ∀ j j' : Fin 2, j'.val = j.val + 1 →
      ((x i j').val : ℤ) - (x i j).val ≤ ((x i' j').val : ℤ) - (x i' j).val ∧
        min (x i j).val (x i' j).val ≤ min (x i j').val (x i' j').val)).card

/-- Barker's conjectured g.f. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 2 * X) * (1 - 3 * X) * (1 - 4 * X)) =
        X * (100 - 457 * X + 740 * X ^ 2 - 384 * X ^ 3) := by
  sorry

end OMA.S_oeis_a250846
