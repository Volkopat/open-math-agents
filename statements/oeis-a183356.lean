import Mathlib

/-!
# OEIS A183356: Barker's generating function and closed form, and the Fibonacci form

Source: https://oeis.org/A183356 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 04 2011), offset 1: One quarter the number of n X 4 1..4 arrays with no
two neighbors of any element equal to each other. Data: 36, 576, 1296, 3600, 9216, 24336, ...
The formula section states: Empirical: a(n) = 2*a(n-1) + 2*a(n-2) - a(n-3) for n>4. Conjectures
from Colin Barker, Mar 28 2018: (Start) G.f.: 36*x*(1 + 14*x + 2*x^2 - 3*x^3) / ((1 + x)*(1 - 3*x
+ x^2)). a(n) = (9/5)*2^(3-n)*((-1)^n*2^(2+n) + (3-sqrt(5))^(1+n) + (3+sqrt(5))^(1+n)) for n>1.
(End) Assuming Colin Barker's conjectures, a(n) = (12*Fibonacci(n+1))^2, n>1. (Ehren Metcalfe,
Apr 21 2018)

Formalization notes:
* An n X 4 array is a function `Fin n → Fin 4 → Fin 4`, x i j being the element in row i and
  column j. The values 1..4 are represented by `Fin 4` (the value k + 1 as k), which changes
  nothing because the condition only compares values. The neighbors of an element are the
  elements directly above, below, left and right of it that lie in the array. `nbrs` lists
  their values for each element of a row, given the rows above and below it, and `rowOK` asks
  that no value repeats in that list, for every element of the row (the neighbors of an element
  are different cells, so no two of them may hold equal values). `okRows` checks every row with
  its neighboring rows, and `valid` starts the scan at the top row. This reading reproduces the
  entry's data, and a cell-by-cell count of the condition agrees for n <= 4.
* `a n` is the number of valid arrays divided by 4 in the natural numbers; the proof shows that
  the number is a multiple of 4.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 + x)(1 - 3x + x^2) =
  36x(1 + 14x + 2x^2 - 3x^3) in Z[[x]], which is equivalent because (1 + x)(1 - 3x + x^2) has
  constant term 1. The closed form is stated in the reals for n > 1, with 2^(3-n) as an integer
  power. Fibonacci is `Nat.fib` (fib 0 = 0, fib 1 = 1), the indexing of the OEIS (A000045).
* The Fibonacci form is stated in the entry assuming Barker's conjectures; `main` states it
  outright, together with both of Barker's conjectures.
* Controls proved in the proof file: a(1..24), all the entry's listed terms.
-/

namespace OMA.S_oeis_a183356

open PowerSeries

/-- The values of the neighbors of the element in column j of the row c of an array with four
columns, given the row p above c and the row q below c (none at an edge of the array): the
elements directly above, below, left and right of it, those that lie in the array. -/
def nbrs (p : Option (Fin 4 → Fin 4)) (c : Fin 4 → Fin 4) (q : Option (Fin 4 → Fin 4)) (j : Fin 4) :
    List (Fin 4) :=
  (p.map fun r => r j).toList ++ (q.map fun r => r j).toList ++
    ((if j.val = 0 then [] else [c (j - 1)]) ++ (if j.val = 3 then [] else [c (j + 1)]))

/-- No two neighbors of any element of the row c hold equal values. -/
def rowOK (p : Option (Fin 4 → Fin 4)) (c : Fin 4 → Fin 4) (q : Option (Fin 4 → Fin 4)) : Bool :=
  decide (∀ j : Fin 4, (nbrs p c q j).Nodup)

/-- Scanning the rows below the row p, from the current row c on. -/
def okRows : Option (Fin 4 → Fin 4) → (Fin 4 → Fin 4) → List (Fin 4 → Fin 4) → Bool
  | p, c, [] => rowOK p c none
  | p, c, r :: l => rowOK p c (some r) && okRows (some c) r l

/-- An n X 4 array, read as its list of rows from the top, in which every row passes `rowOK`. -/
def valid : List (Fin 4 → Fin 4) → Bool
  | [] => true
  | c :: l => okRows none c l

/-- A183356(n): one quarter of the number of valid n X 4 arrays; x i j is the element in row i and
column j, and the values 1..4 are represented by `Fin 4`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun x : Fin n → Fin 4 → Fin 4 => valid (List.ofFn x) = true).card / 4

/-- Barker's g.f. and closed form, and the Fibonacci form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * ((1 + X) * (1 - 3 * X + X ^ 2)) =
      36 * X * (1 + 14 * X + 2 * X ^ 2 - 3 * X ^ 3) ∧
    (∀ n : ℕ, 1 < n → (a n : ℝ) = 9 / 5 * 2 ^ ((3 : ℤ) - n) *
      ((-1) ^ n * 2 ^ (2 + n) + (3 - Real.sqrt 5) ^ (1 + n) + (3 + Real.sqrt 5) ^ (1 + n))) ∧
    ∀ n : ℕ, 1 < n → a n = (12 * Nat.fib (n + 1)) ^ 2 := by
  sorry

end OMA.S_oeis_a183356
