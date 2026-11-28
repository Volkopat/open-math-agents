import Mathlib

/-!
# OEIS A278008: Barker's generating function and closed form

Source: https://oeis.org/A278008 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Nov 08 2016), offset 1: Number of n X 2 0..2 arrays with every element plus 1
mod 3 equal to some element at offset (-1,-1) (-1,0) (-1,1) (0,-1) (0,1) or (1,0), with upper left
element zero. Data: 0, 6, 30, 198, 1230, 7734, 48510, ... The formula section states: Empirical:
a(n) = 5*a(n-1) + 8*a(n-2). Conjectures from Colin Barker, Feb 07 2019: (Start) G.f.: 6*x^2 /
(1 - 5*x - 8*x^2). a(n) = 2^(-3-n) * ((57-5*sqrt(57))*(5+sqrt(57))^n +
(5-sqrt(57))^n*(57+5*sqrt(57))) / 19. (End)

Formalization notes:
* An n X 2 array is a function `Fin n → Fin 3 × Fin 3` giving each row (x(i,0), x(i,1)); `Fin 3`
  addition is modulo 3. An offset (di, dj) refers to the element x(i+di, j+dj), which counts only
  when it lies in the array. `rowOK` lists, for each element of a row, the offsets that stay in
  the array; `okRows` checks every row with its neighboring rows, and `valid` adds that the upper
  left element is zero. This reading reproduces the entry's data and agrees with a brute force of
  the condition read cell by cell for n <= 4.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - 5x - 8x^2) = 6x^2 in
  Z[[x]], which is equivalent because 1 - 5x - 8x^2 has constant term 1. The closed form is
  stated in the reals for the terms of the sequence, n >= 1, with 2^(-3-n) as an integer power.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..21), all the entry's listed terms.
-/

namespace OMA.S_oeis_a278008

open PowerSeries

/-- Some element of the optional row o, read by f, equals t (false where there is no row). -/
def hasAt (o : Option (Fin 3 × Fin 3)) (f : Fin 3 × Fin 3 → Fin 3) (t : Fin 3) : Bool :=
  match o with
  | none => false
  | some r => decide (f r = t)

/-- The condition of the entry for both elements of the row c, with the row p above it and the row
q below it (none where there is no such row): every element plus 1 mod 3 equals some element at
offset (-1,-1), (-1,0), (-1,1), (0,-1), (0,1) or (1,0). For c.1 (column 0) the offsets that stay in
the array are (-1,0), (-1,1), (0,1), (1,0), that is p.1, p.2, c.2, q.1; for c.2 (column 1) they are
(-1,-1), (-1,0), (0,-1), (1,0), that is p.1, p.2, c.1, q.2. -/
def rowOK (p : Option (Fin 3 × Fin 3)) (c : Fin 3 × Fin 3) (q : Option (Fin 3 × Fin 3)) : Bool :=
  (hasAt p Prod.fst (c.1 + 1) || hasAt p Prod.snd (c.1 + 1) || decide (c.2 = c.1 + 1) ||
      hasAt q Prod.fst (c.1 + 1)) &&
    (hasAt p Prod.fst (c.2 + 1) || hasAt p Prod.snd (c.2 + 1) || decide (c.1 = c.2 + 1) ||
      hasAt q Prod.snd (c.2 + 1))

/-- Scanning the rows below the row p, from the current row c on. -/
def okRows : Option (Fin 3 × Fin 3) → Fin 3 × Fin 3 → List (Fin 3 × Fin 3) → Bool
  | p, c, [] => rowOK p c none
  | p, c, r :: l => rowOK p c (some r) && okRows (some c) r l

/-- An n X 2 array, read as its list of rows from the top: the upper left element is zero and
every row passes `rowOK`. -/
def valid : List (Fin 3 × Fin 3) → Bool
  | [] => true
  | c :: l => decide (c.1 = 0) && okRows none c l

/-- A278008(n): the number of valid n X 2 arrays with entries 0..2; row i is the pair
(x(i,0), x(i,1)). -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin n → Fin 3 × Fin 3 => valid (List.ofFn x) = true).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - 5 * X - 8 * X ^ 2) = 6 * X ^ 2 ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℝ) = 2 ^ (-3 - (n : ℤ)) *
      ((57 - 5 * Real.sqrt 57) * (5 + Real.sqrt 57) ^ n + (5 - Real.sqrt 57) ^ n * (57 + 5 * Real.sqrt 57)) / 19 := by
  sorry

end OMA.S_oeis_a278008
