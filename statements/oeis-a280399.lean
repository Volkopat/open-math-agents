import Mathlib

/-!
# OEIS A280399: Barker's generating function and closed form

Source: https://oeis.org/A280399 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 02 2017), offset 1: Number of 1 X n 0..2 arrays with no element
unequal to a strict majority of its horizontal and antidiagonal neighbors, with the exception of
exactly one element, and with new values introduced in order 0 sequentially upwards. Data: 0, 0,
2, 2, 8, 14, 36, 74, ... Formula section: Conjectures from Colin Barker, Feb 13 2019:
G.f.: 2*x^3*(1 - x - x^2) / ((1 + x)^2*(1 - 2*x)^2).
a(n) = (8*((-1)^(1+n)+2^n) + 3*(-8*(-1)^n+2^n)*n) / 108 for n>1.

Formalization notes:
* A 1 X n array has no antidiagonal neighbours, so the neighbours of an element are the elements
  directly to its left and right. An element is unequal to a strict majority of its neighbours
  when it differs from both of them (two neighbours) or from its only neighbour (an end element);
  an element without neighbours (n = 1) never is. Exactly one element of the row has this
  property. New values introduced in order 0 sequentially upwards means that the values first
  appear in the order 0, 1, 2: the first element is 0, and each element is at most the number k
  of distinct values to its left. The array is a function `Fin n → Fin 3` and its row is
  `List.ofFn x`.
* `ok q p k e l` scans the rest `l` of the row, where `p` is the element to its left, `q` the
  element before `p` (`none` at the start), `k` the number of values used so far and `e` the
  number of exceptional elements found so far (the exceptionality of `p` is known once the next
  element is read, and that of the last element at the end); stopping as soon as e exceeds one
  does not change the count of rows with exactly one. This reading reproduces the first ten terms
  of the entry's data by brute force.
* The g.f. is the formal power series Sum_{n >= 1} a(n) x^n over the rationals (offset 1, so the
  constant coefficient is 0), and the claim is that it equals the numerator times the inverse of
  the denominator, whose constant term is 1. The closed form is stated in the rationals for
  n > 1.
* `main` is the conjunction of Barker's two conjectures.
* Controls (proved in the proof file): a(1..17) = 0, 0, 2, 2, 8, 14, 36, 74, 168, 358, 780, 1666,
  3568, 7582, 16084, 33978, 71608, the entry's data, and a(4) = 2 by direct enumeration of the 81
  arrays.
-/

namespace OMA.S_oeis_a280399

open PowerSeries

/-- 1 if the element `p`, with the element `q` to its left (`none` at the left end) and the
element `c` to its right, is unequal to a strict majority of its neighbours: unequal to both
when it has two neighbours, unequal to `c` when `c` is its only neighbour. -/
def bad (q : Option (Fin 3)) (p c : Fin 3) : ℕ :=
  if (q.all fun v => decide (v ≠ p)) && decide (c ≠ p) then 1 else 0

/-- 1 if the last element `p`, with the element `q` to its left, is unequal to a strict majority
of its neighbours (its only neighbour is `q`; an element without neighbours never is). -/
def lastBad (q : Option (Fin 3)) (p : Fin 3) : ℕ :=
  if q.any (fun v => decide (v ≠ p)) then 1 else 0

/-- Scanning a row from the left. `q` is the element two places to the left of the rest of the
row (`none` at the start), `p` the element directly to its left, `k` the number of values used so
far (they are 0, ..., k - 1) and `e` the number of exceptions found so far, which may never exceed
one; at the end there must be exactly one. Every element is at most k, so a value that has not
been used is the next new value. -/
def ok : Option (Fin 3) → Fin 3 → ℕ → ℕ → List (Fin 3) → Bool
  | q, p, _, e, [] => decide (e + lastBad q p = 1)
  | q, p, k, e, c :: l =>
    decide (c.val ≤ k) && decide (e + bad q p c ≤ 1) &&
      ok (some p) c (max k (c.val + 1)) (e + bad q p c) l

/-- A 1 X n array, read as its single row from the left: the first element is 0, the first new
value, and the rest of the row passes the scan. -/
def valid : List (Fin 3) → Bool
  | [] => false
  | c :: l => decide (c = 0) && ok none c 1 0 l

/-- A280399(n): the number of valid 1 X n arrays with entries 0..2. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin n → Fin 3 => valid (List.ofFn x) = true).card

/-- The generating function Sum_{n >= 1} a(n) x^n (offset 1). -/
noncomputable def gf : ℚ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)

/-- Barker's conjectures: the g.f. and the closed form for n > 1. -/
theorem main :
    gf = 2 * X ^ 3 * (1 - X - X ^ 2) * ((1 + X) ^ 2 * (1 - 2 * X) ^ 2)⁻¹ ∧
    ∀ n : ℕ, 1 < n →
      (a n : ℚ) = (8 * ((-1) ^ (1 + n) + 2 ^ n) + 3 * (-8 * (-1) ^ n + 2 ^ n) * n) / 108 := by
  sorry

end OMA.S_oeis_a280399
