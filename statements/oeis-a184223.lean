import Mathlib

/-!
# OEIS A184223: Barker's recurrence and g.f. for half the number of (n+1) X 2 0..3 arrays whose 2 X 2 diagonal and antidiagonal sums differ by more than 3

Source: https://oeis.org/A184223 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A184223 (R. H. Hardin, Jan 10 2011), offset 1: Half the number of (n+1) X 2 0..3 arrays with
every 2 X 2 subblock diagonal sum differing from its antidiagonal sum by more than 3. Column 1 of
A184231. Data: 15, 57, 180, 621, 2061, 6966, 23355, 78597, ... Formula section: Conjectures: a(n) =
3*a(n-1)+3*a(n-2)-6*a(n-3); G.f.: -3*x*(2*x+1)*(6*x-5) / (6*x^3-3*x^2-3*x+1). - Colin Barker, Sep 26
2014

Formalization notes:
* An array is a function x : Fin (n + 1) -> Fin 2 -> Fin 4, x i j being the element in row i and
  column j. The 2 X 2 subblocks are the blocks of rows i, i' = i + 1 and columns j, j' = j + 1; the
  diagonal is x(i,j), x(i',j') and the antidiagonal x(i,j'), x(i',j). Differing by more than 3 means
  that the absolute value of the difference of the two sums is greater than 3. This reading
  reproduces the entry's data and the table A184231 (brute force over all arrays for small sizes, a
  row transfer for the rest of the table).
* `a n` is the number of these arrays divided by 2 in the natural numbers; the proof shows that the
  number is even.
* The recurrence is stated for n >= 4, the indices at which a(n-3) is a term of the sequence (offset
  1). The g.f. is A(x) = Sum_{n >= 1} a(n) x^n, stated as A(x) (6x^3 - 3x^2 - 3x + 1) = -3x(2x +
  1)(6x - 5) in Q[[x]], which is equivalent because the denominator has constant term 1.
* `main` is the conjunction of the two conjectures.
* Controls proved in the proof file: a(1..23) = 15, 57, 180, 621, 2061, 6966, 23355, 78597, 264060,
  887841, 2984121, 10031526, 33719895, 113349537, 381019140, 1280786661, 4305320181, 14472205686,
  48647857635, 163528268877, 549695145420, 1847783097081, 6211265114241, the entry's data.
-/

namespace OMA.S_oeis_a184223

open PowerSeries

/-- A184223(n): half the number of (n+1) X 2 arrays x with entries 0..3 (x i j in row i and column
j) in which every 2 X 2 subblock, rows i, i' = i + 1 and columns j, j' = j + 1, has its diagonal sum
x(i,j) + x(i',j') differing from its antidiagonal sum x(i,j') + x(i',j) by more than 3 (the absolute
value of the difference exceeds 3). -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (n + 1) → Fin 2 → Fin 4)).filter (fun x =>
    ∀ i i' : Fin (n + 1), i'.val = i.val + 1 → ∀ j j' : Fin 2, j'.val = j.val + 1 →
      3 < |((x i j).val + (x i' j').val : ℤ) - ((x i j').val + (x i' j).val)|)).card / 2

/-- The conjectures, as stated in the entry. -/
theorem main :
    (∀ n : ℕ, 4 ≤ n → (a n : ℤ) = 3 * a (n - 1) + 3 * a (n - 2) - 6 * a (n - 3)) ∧
      PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        (6 * X ^ 3 - 3 * X ^ 2 - 3 * X + 1) = -3 * X * (2 * X + 1) * (6 * X - 5) := by
  sorry

end OMA.S_oeis_a184223
