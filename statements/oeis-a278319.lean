import Mathlib

/-!
# OEIS A278319: Barker's generating function and recurrence

Source: https://oeis.org/A278319 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Nov 18 2016), offset 1: Number of n X 2 0..1 arrays with rows and columns in
lexicographic nondecreasing order but with exactly two mistakes. Data: 0, 3, 20, 94, 395, ... The
formula section states: Empirical: a(n) = (1/39916800)*n^11 + (1/725760)*n^10 + (13/362880)*n^9 +
(43/120960)*n^8 + (223/172800)*n^7 - (227/34560)*n^6 + (1019/45360)*n^5 + (27263/181440)*n^4 +
(12193/113400)*n^3 - (121/840)*n^2 - (13/99)*n. Conjectures from _Colin Barker_, Feb 09 2019:
(Start) G.f.: x^2*(3 - 16*x + 52*x^2 - 73*x^3 + 41*x^4 + x^5 - 10*x^6 + 3*x^7) / (1 - x)^12. a(n) =
12*a(n-1) - 66*a(n-2) + 220*a(n-3) - 495*a(n-4) + 792*a(n-5) - 924*a(n-6) + 792*a(n-7) - 495*a(n-8)
+ 220*a(n-9) - 66*a(n-10) + 12*a(n-11) - a(n-12) for n>12. (End)

Formalization notes:
* An n X 2 array over 0..1 is a function `Fin n → Fin 2 → Fin 2`, x i j being the element in row i
  and column j, both counted from 0; row i is read from left to right (`List.ofFn (x i)`) and column
  j from top to bottom.
* Rows and columns in lexicographic nondecreasing order means that each row is lexicographically at
  most the next row and each column at most the next column; a mistake is a consecutive pair (of
  rows, or of columns) in which the second is lexicographically less than the first. `mistakes` adds
  the two counts; the order on `List (Fin 2)` is the library's lexicographic order.
* `a n` is `Set.ncard` of the arrays with exactly two mistakes, a set of functions between finite
  types.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1; the count for n = 0 is not a term of the
  sequence and is replaced by 0), stated as A(x) (1 - x)^12 = the numerator in Z[[x]], which is
  equivalent because (1 - x)^12 has constant term 1. The recurrence is stated in the integers for n
  > 12, as in the entry.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..13), all the entry's listed terms.
-/

namespace OMA.S_oeis_a278319

open PowerSeries

/-- The mistakes of the n X 2 array x: the consecutive rows (row i, row i + 1), each read from
left to right, with row i + 1 lexicographically less than row i, and the consecutive columns
(column j, column j + 1), each read from top to bottom, with column j + 1 lexicographically less
than column j (the order on lists of Fin 2 is the lexicographic one). -/
noncomputable def mistakes (n : ℕ) (x : Fin n → Fin 2 → Fin 2) : ℕ :=
  Set.ncard {i : Fin n | ∃ i' : Fin n, i'.val = i.val + 1 ∧ List.ofFn (x i') < List.ofFn (x i)} +
    Set.ncard {j : Fin 2 | ∃ j' : Fin 2, j'.val = j.val + 1 ∧
      List.ofFn (fun i => x i j') < List.ofFn (fun i => x i j)}

/-- A278319(n): the number of n X 2 arrays over 0..1 with rows and columns in lexicographic
nondecreasing order but with exactly two mistakes. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {x : Fin n → Fin 2 → Fin 2 | mistakes n x = 2}

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 12 = X ^ 2 * (3 - 16 * X + 52 * X ^ 2 - 73 * X ^ 3 + 41 * X ^ 4 + X ^ 5 - 10 * X ^ 6 + 3 * X ^ 7) ∧
    ∀ n : ℕ, 12 < n → (a n : ℤ) = 12 * a (n - 1) - 66 * a (n - 2) + 220 * a (n - 3) - 495 * a (n - 4) + 792 * a (n - 5) - 924 * a (n - 6) + 792 * a (n - 7) - 495 * a (n - 8) + 220 * a (n - 9) - 66 * a (n - 10) + 12 * a (n - 11) - a (n - 12) := by
  sorry

end OMA.S_oeis_a278319
