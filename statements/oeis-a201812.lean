import Mathlib

/-!
# A201812: Number of arrays of 4 integers in -n..n with sum zero and equal numbers of elements greater than zero and less than zero.

Source: https://oeis.org/A201812
Credit: @Salofe

Conjectures from Colin Barker, May 25 2018, quoted verbatim from the entry (sequence by
R. H. Hardin, Dec 05 2011):
"Conjectures from Colin Barker, May 25 2018: (Start)
G.f.: x*(19 - 15*x + 21*x^2 - x^3) / (1 - x)^4.
a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>4.
(End)"

Formalization notes:
* Offset 1, as in the entry (data: 19, 61, 151, 313, 571, 949, ...).
* An array of 4 integers in -n..n is a map `f : Fin 4 → ℤ` (positions 0..3) with
  `-n ≤ f i ≤ n` at every position `i`; these maps form the finite set
  `Fintype.piFinset (fun _ => Finset.Icc (-n) n)`. Arrays are labelled: they are not identified
  up to a permutation of the positions or any other symmetry.
* "Sum zero" is `∑ i, f i = 0`. "Equal numbers of elements greater than zero and less than zero"
  says that the number of positions `i` with `0 < f i` equals the number of positions `i` with
  `f i < 0` (elements are counted by position, so a repeated value counts once per occurrence;
  zero entries are in neither group).
* This reading reproduces the data: a brute-force evaluation of this definition gives
  19, 61, 151, 313, 571, 949 for n = 1, ..., 6 and agrees with all 37 terms of the entry's data
  (n = 1..37), and the 16 solutions shown in the entry for n = 21 satisfy it.
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power
  series over `ℤ` with the denominator `(1 - x)^4` cleared (its constant coefficient is 1, so it
  is invertible and clearing it is an equivalence). The definition also makes sense for n = 0,
  outside the range of the entry (it gives 1, the zero array); the coefficient of x^0 of the
  series is set to 0, matching the g.f. sum over n >= 1.
* The recurrence is stated in `ℤ` for every n > 4, as in the entry (all indices are then >= 1).
* The entry also lists R. H. Hardin's empirical formula a(n) = 4*n^3 + 14*n + 1; it is not part
  of Barker's conjectures and is not stated here.
-/

namespace OMA.S_oeis_a201812

/-- A201812(n): the number of arrays `f` of 4 integers in `-n..n` (maps `Fin 4 → ℤ` with every
value in `[-n, n]`) with sum zero and as many entries greater than zero as entries less than
zero. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(n : ℤ)) n).filter fun f =>
    (∑ i, f i) = 0 ∧
      (Finset.univ.filter fun i => 0 < f i).card = (Finset.univ.filter fun i => f i < 0).card).card

open PowerSeries in
/-- Barker's conjectures: the g.f. `x(19 - 15x + 21x^2 - x^3)/(1 - x)^4` of
`Sum_{n ≥ 1} a(n) x^n`, and the recurrence `a(n) = 4a(n-1) - 6a(n-2) + 4a(n-3) - a(n-4)` for
`n > 4`. -/
theorem main :
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) * (1 - X) ^ 4 =
        X * (19 - 15 * X + 21 * X ^ 2 - X ^ 3)) ∧
    ∀ n : ℕ, n > 4 →
      (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a201812
