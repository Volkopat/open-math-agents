import Mathlib

/-!
# OEIS A265989: Barker's generating function and closed form

Source: https://oeis.org/A265989 (OEIS Foundation, CC BY-SA 4.0).

Entry (R. H. Hardin, Dec 19 2015), offset 1: Number of n X 6 integer arrays with each element
equal to the number of horizontal and antidiagonal neighbors not equal to itself. Data: 2, 6, 9,
4, 26, 5, 101, 17, 401, 65, 1601, 257, ... The formula section states: Empirical: a(n) =
a(n-1) + 4*a(n-2) - 4*a(n-3) for n>7. Conjectures from Colin Barker, Jan 09 2019: (Start) G.f.:
x*(2 + 4*x - 5*x^2 - 21*x^3 + 10*x^4 - x^5 + 8*x^6) / ((1 - x)*(1 - 2*x)*(1 + 2*x)). a(n) =
(64 - 23*(-2)^n + 27*2^n) / 64 for n>4. (End)

Formalization notes:
* An n X 6 integer array is a function `Fin n → Fin 6 → ℤ`: row i is `x i`, read from the top.
* The horizontal and antidiagonal neighbours of x(i,j) are x(i,j-1), x(i,j+1), x(i-1,j+1) and
  x(i+1,j-1), where they exist. `nbrs u r w j` lists the neighbours of entry j of the row r,
  where u and w are the rows above and below (none at the top or bottom of the array), and
  `cellOk` asks that the entry equals the number of its neighbours different from it. `ok`
  scans the rows from the top. This reading reproduces the entry's data a(1..11).
* The arrays are counted with `Nat.card`; every entry of a counted array is a number of
  neighbours, so there are finitely many.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as
  A(x) (1 - x)(1 - 2x)(1 + 2x) = x (2 + 4x - 5x^2 - 21x^3 + 10x^4 - x^5 + 8x^6) in Z[[x]], which
  is equivalent because the denominator has constant term 1. The closed form is stated in the
  rationals for n >= 5.
* `main` is the conjunction of Barker's two conjectures.
-/

namespace OMA.S_oeis_a265989

open PowerSeries

/-- Entry k of the row r, as a list with one element, or the empty list when k is not in 0..5. -/
def entry (r : Fin 6 → ℤ) (k : ℕ) : List ℤ :=
  if h : k < 6 then [r ⟨k, h⟩] else []

/-- The neighbours of entry j of the row r, where u and w are the rows above and below: the
horizontal neighbours r(j-1), r(j+1), the upper antidiagonal neighbour u(j+1) and the lower
antidiagonal neighbour w(j-1), where they exist. -/
def nbrs (u : Option (Fin 6 → ℤ)) (r : Fin 6 → ℤ) (w : Option (Fin 6 → ℤ)) (j : ℕ) : List ℤ :=
  (if j = 0 then [] else entry r (j - 1)) ++ entry r (j + 1) ++
    (match u with | none => [] | some u => entry u (j + 1)) ++
    (match w with | none => [] | some w => if j = 0 then [] else entry w (j - 1))

/-- Entry j of r equals the number of its neighbours that are not equal to it. -/
def cellOk (u : Option (Fin 6 → ℤ)) (r : Fin 6 → ℤ) (w : Option (Fin 6 → ℤ)) (j : Fin 6) : Bool :=
  decide (r j = (((nbrs u r w j).filter (fun y => decide (y ≠ r j))).length : ℤ))

/-- Every entry of the row r passes `cellOk`. -/
def rowOk (u : Option (Fin 6 → ℤ)) (r : Fin 6 → ℤ) (w : Option (Fin 6 → ℤ)) : Bool :=
  (List.finRange 6).all (cellOk u r w)

/-- Scanning the rows from the top, where u is the row above the first row of the list. -/
def ok : Option (Fin 6 → ℤ) → List (Fin 6 → ℤ) → Bool
  | _, [] => true
  | u, [r] => rowOk u r none
  | u, r :: w :: l => rowOk u r (some w) && ok (some r) (w :: l)

/-- A265989(n): the number of n X 6 integer arrays in which every element passes `cellOk`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin n → Fin 6 → ℤ // ok none (List.ofFn x) = true}

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) *
        ((1 - X) * (1 - 2 * X) * (1 + 2 * X)) =
      X * (2 + 4 * X - 5 * X ^ 2 - 21 * X ^ 3 + 10 * X ^ 4 - X ^ 5 + 8 * X ^ 6) ∧
    ∀ n : ℕ, 5 ≤ n → (a n : ℚ) = (64 - 23 * (-2) ^ n + 27 * 2 ^ n) / 64 := by
  sorry

end OMA.S_oeis_a265989
