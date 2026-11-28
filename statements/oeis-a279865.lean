import Mathlib

/-!
# OEIS A279865: Barker's generating function and closed forms

Source: https://oeis.org/A279865 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Dec 21 2016), offset 1: Number of n X 1 0..2 arrays with no element unequal
to a strict majority of its horizontal and vertical neighbors, with the exception of exactly two
elements, and with new values introduced in order 0 sequentially upwards. Data: 0, 1, 0, 6, 6,
30, 54, 158, ... Formula section: Conjectures from Colin Barker, Feb 26 2018:
G.f.: x^2*(1 - x)^3 / ((1 + x)^3*(1 - 2*x)^3).
a(n) = (3*2^n*n^2 + 96*n^2 + 21*2^n*n + 2^(n+4) - 16) / 648 for n even.
a(n) = (3*2^n*n^2 - 96*n^2 + 21*2^n*n + 2^(n+4) + 16) / 648 for n odd.

Formalization notes:
* An n X 1 array has no horizontal neighbours, so the neighbours of an element are the elements
  directly above and below it. An element is unequal to a strict majority of its neighbours when
  it differs from both of them (two neighbours) or from its only neighbour (an end element); an
  element without neighbours (n = 1) never is. Exactly two elements of the column have this
  property. New values introduced in order 0 sequentially upwards means that the values first
  appear in the order 0, 1, 2 from the top: the top element is 0, and each element is at most the
  number k of distinct values above it. The array is a function `Fin n → Fin 3` and its column is
  `List.ofFn x`.
* `ok q p k e l` scans the rest `l` of the column, where `p` is the element above it, `q` the
  element above `p` (`none` at the start), `k` the number of values used so far and `e` the
  number of exceptional elements found so far (the exceptionality of `p` is known once the next
  element is read, and that of the last element at the end); stopping as soon as e exceeds two
  does not change the count of columns with exactly two. This reading reproduces the first ten
  terms of the entry's data by brute force and gives the six solutions listed for n = 4.
* The g.f. is the formal power series Sum_{n >= 1} a(n) x^n over the rationals (offset 1, so the
  constant coefficient is 0), and the claim is that it equals the numerator times the inverse of
  the denominator, whose constant term is 1. The two closed forms are stated in the rationals for
  the terms of the sequence, n >= 1, even or odd.
* `main` is the conjunction of Barker's three conjectures.
* Controls (proved in the proof file): a(1..16) = 0, 1, 0, 6, 6, 30, 54, 158, 342, 846, 1910,
  4446, 10038, 22734, 50838, 113310, the entry's data, and a(4) = 6 by direct enumeration of the
  81 arrays.
-/

namespace OMA.S_oeis_a279865

open PowerSeries

/-- 1 if the element `p`, with the element `q` above it (`none` at the top) and the element `c`
below it, is unequal to a strict majority of its neighbours: unequal to both when it has two
neighbours, unequal to `c` when `c` is its only neighbour. -/
def bad (q : Option (Fin 3)) (p c : Fin 3) : ℕ :=
  if (q.all fun v => decide (v ≠ p)) && decide (c ≠ p) then 1 else 0

/-- 1 if the last element `p`, with the element `q` above it, is unequal to a strict majority of
its neighbours (its only neighbour is `q`; an element without neighbours never is). -/
def lastBad (q : Option (Fin 3)) (p : Fin 3) : ℕ :=
  if q.any (fun v => decide (v ≠ p)) then 1 else 0

/-- Scanning a column from the top. `q` is the element two rows above the rest of the column
(`none` at the start), `p` the element directly above it, `k` the number of values used so far
(they are 0, ..., k - 1) and `e` the number of exceptions found so far, which may never exceed
two; at the end there must be exactly two. Every element is at most k, so a value that has not
been used is the next new value. -/
def ok : Option (Fin 3) → Fin 3 → ℕ → ℕ → List (Fin 3) → Bool
  | q, p, _, e, [] => decide (e + lastBad q p = 2)
  | q, p, k, e, c :: l =>
    decide (c.val ≤ k) && decide (e + bad q p c ≤ 2) &&
      ok (some p) c (max k (c.val + 1)) (e + bad q p c) l

/-- An n X 1 array, read as its single column from the top: the top element is 0, the first new
value, and the rest of the column passes the scan. -/
def valid : List (Fin 3) → Bool
  | [] => false
  | c :: l => decide (c = 0) && ok none c 1 0 l

/-- A279865(n): the number of valid n X 1 arrays with entries 0..2. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin n → Fin 3 => valid (List.ofFn x) = true).card

/-- The generating function Sum_{n >= 1} a(n) x^n (offset 1). -/
noncomputable def gf : ℚ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 0 else (a n : ℚ)

/-- Barker's conjectures: the g.f. and the closed forms for even and odd n >= 1. -/
theorem main :
    gf = X ^ 2 * (1 - X) ^ 3 * ((1 + X) ^ 3 * (1 - 2 * X) ^ 3)⁻¹ ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℚ) =
      (3 * 2 ^ n * n ^ 2 + 96 * n ^ 2 + 21 * 2 ^ n * n + 2 ^ (n + 4) - 16) / 648) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℚ) =
      (3 * 2 ^ n * n ^ 2 - 96 * n ^ 2 + 21 * 2 ^ n * n + 2 ^ (n + 4) + 16) / 648) := by
  sorry

end OMA.S_oeis_a279865
