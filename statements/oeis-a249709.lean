import Mathlib

/-!
# A249709: Number of length 3+3 0..n arrays with every four consecutive terms having the maximum of some two terms equal to the minimum of the remaining two terms.

Source: https://oeis.org/A249709
Credit: @Salofe

The sequence is due to R. H. Hardin (Nov 04 2014); it is row 3 of A249707.

Conjectures from Colin Barker, Nov 10 2018, quoted verbatim from the entry:
* "G.f.: x*(20 + 5*x - 10*x^2 - 12*x^3 + 6*x^4 - x^5) / (1 - x)^6."
* "a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>6."

The entry also lists Hardin's "Empirical: a(n) = (1/15)*n^5 + 2*n^4 + 7*n^3 + 7*n^2 +
(44/15)*n + 1."; that closed form is not part of this statement, which states Barker's two
conjectures only.

Formalization notes:
* Offset 1, as in the entry (data: 20, 125, 440, 1153, 2524, 4893, 8688, ...). The value `a 0`
  is never used: the g.f. has coefficient 0 at x^0, and the recurrence (n > 6) only involves
  a(n-6), ..., a(n) with n - 6 ≥ 1.
* "Length 3+3" is the array length 3 + 3 = 6. An array is `x : Fin 6 → Fin (n + 1)`: the terms
  x_0, ..., x_5 with entries in 0..n, compared as natural numbers. Arrays are not identified up to
  symmetry. `get x k` is the term x_k as a natural number (it is only read at positions k ≤ 5).
* "Every four consecutive terms": for each of the three windows x_i, x_(i+1), x_(i+2), x_(i+3)
  with i = 0, 1, 2 (positions i + t, t = 0, 1, 2, 3).
* "The maximum of some two terms equal to the minimum of the remaining two terms": there is a
  set `S` of two of the four positions of the window (two distinct terms) and a value `v` such
  that `v` is the maximum of the two terms at the positions in `S` (both are ≤ v and one of them
  equals v) and `v` is the minimum of the remaining two terms (both are ≥ v and one of them
  equals v). The bound `v < n + 1` holds automatically, since `v` is one of the terms; it only
  makes the condition decidable. `a n` is the number of arrays all of whose windows satisfy it.
* This reading reproduces the data: an exhaustive enumeration of all 0..n arrays of length 6,
  computing exactly the definitions below, gives 20, 125, 440, 1153, 2524, 4893, 8688 for
  n = 1, ..., 7; all sixteen arrays shown in the entry for n = 6 satisfy `good`; a recursion over
  threshold sets computing the same count gives all 210 terms of the b-file (n = 1..210).
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power series
  over `ℚ` with the denominator `(1 - x)^6` cleared (it has constant coefficient 1, so it is
  invertible). The coefficient of x^0 is 0 since the sequence starts at n = 1.
* The recurrence is stated in `ℤ` for every n > 6, as in the entry.
-/

namespace OMA.S_oeis_a249709

/-- The term of the array `x` at position `k` as a natural number (`0` past the end). -/
def get {n : ℕ} (x : Fin 6 → Fin (n + 1)) (k : ℕ) : ℕ :=
  if h : k < 6 then (x ⟨k, h⟩ : ℕ) else 0

/-- Every four consecutive terms (the windows at positions `i + t`, `t < 4`, for `i < 3`) have the
maximum of some two terms (at the positions of a 2-element set `S` of the window) equal to the
minimum of the remaining two terms. -/
def good {n : ℕ} (x : Fin 6 → Fin (n + 1)) : Bool :=
  decide (∀ i < (3 : ℕ), ∃ S ∈ (Finset.univ : Finset (Fin 4)).powersetCard 2, ∃ v < n + 1,
    (∀ t ∈ S, get x (i + t) ≤ v) ∧ (∃ t ∈ S, get x (i + t) = v) ∧
    (∀ t ∉ S, v ≤ get x (i + t)) ∧ (∃ t ∉ S, get x (i + t) = v))

/-- A249709(n): the number of arrays of length 6 with entries in `0..n` all of whose windows of
four consecutive terms satisfy the condition. -/
def a (n : ℕ) : ℤ :=
  ((Finset.univ : Finset (Fin 6 → Fin (n + 1))).filter (fun x => good x)).card

open PowerSeries in
/-- Barker's conjectures: the generating function
`x(20 + 5x - 10x^2 - 12x^3 + 6x^4 - x^5)/(1 - x)^6`, and the recurrence
`a(n) = 6a(n-1) - 15a(n-2) + 20a(n-3) - 15a(n-4) + 6a(n-5) - a(n-6)` for `n > 6`. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 6 =
        X * (20 + 5 * X - 10 * X ^ 2 - 12 * X ^ 3 + 6 * X ^ 4 - X ^ 5) ∧
    (∀ n : ℕ, 6 < n → a n = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) +
      6 * a (n - 5) - a (n - 6)) := by
  sorry

end OMA.S_oeis_a249709
