import Mathlib

/-!
# A201044: Number of -n..n arrays of 5 elements with adjacent element differences also in -n..n.

Source: https://oeis.org/A201044
Credit: @Salofe

Conjectures from Colin Barker, May 22 2018, quoted verbatim from the entry (by R. H. Hardin,
Nov 26 2011):
"Conjectures from Colin Barker, May 22 2018: (Start)
G.f.: x*(99 + 567*x + 602*x^2 + 78*x^3 + 7*x^4 - x^5) / (1 - x)^6.
a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>6.
(End)"

Formalization notes:
* Offset 1, as in the entry (data: 99, 1161, 6083, 21141, 57343, 131781, ...).
* An array of 5 elements is a map `x : Fin 5 → ℤ` (positions 0..4). "-n..n" means that every
  entry `x i` lies in `Finset.Icc (-n) n`. The adjacent element differences are
  x(i+1) - x(i) for i = 0..3, that is `x i.succ - x i.castSucc` for `i : Fin 4`, and each of
  them must lie in `Finset.Icc (-n) n` as well. (The interval is symmetric, so the sign
  convention of a difference does not matter.) Arrays are labelled: they are not identified
  up to symmetry.
* `a n` is the number of such arrays: the arrays with entries in -n..n form the finite set
  `Fintype.piFinset (fun _ => Finset.Icc (-n) n)`, and `a n` is the cardinality of its subset
  of arrays whose adjacent differences are in -n..n. (`a` is marked `noncomputable` only because
  the order instance on `ℤ` that `Finset.Icc` picks up is; this does not affect its value.)
* The definition also makes sense for n = 0, outside the range of the entry (it counts only
  the all-zero array, so it gives 1 there). The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n,
  so the coefficient of x^0 of the series is set to 0.
* The g.f. is stated as an identity of formal power series over `ℚ`; the division by
  (1 - x)^6 is multiplication by its inverse in `ℚ⟦X⟧` (its constant coefficient is 1, so it
  is invertible).
* The recurrence is stated in `ℤ` for every n > 6, as in the entry (all indices are then >= 1).
* The entry's empirical polynomial formula (R. H. Hardin) is not part of these conjectures and
  is not stated here.
* Checks: a brute-force evaluation of this definition gives 99, 1161, 6083, 21141, 57343,
  131781, 268983, 502265 for n = 1..8; a transfer count of the same definition agrees with all
  26 terms of the entry's data and with the b-file for n = 1..30; the 16 example solutions
  shown in the entry for n = 5 satisfy the definition.
-/

namespace OMA.S_oeis_a201044

/-- A201044(n): the number of arrays `x : Fin 5 → ℤ` with every entry in -n..n and every
adjacent difference `x (i + 1) - x i` (i = 0..3) in -n..n. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin 5 => Finset.Icc (-(n : ℤ)) n).filter
    (fun x => ∀ i : Fin 4, x i.succ - x i.castSucc ∈ Finset.Icc (-(n : ℤ)) n)).card

open PowerSeries in
/-- Barker's conjectures: the generating function
`x(99 + 567x + 602x^2 + 78x^3 + 7x^4 - x^5)/(1 - x)^6` and the recurrence
`a(n) = 6a(n-1) - 15a(n-2) + 20a(n-3) - 15a(n-4) + 6a(n-5) - a(n-6)` for `n > 6`. -/
theorem main :
    (PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℚ)) =
      (X : PowerSeries ℚ) * (99 + 567 * X + 602 * X ^ 2 + 78 * X ^ 3 + 7 * X ^ 4 - X ^ 5) *
        ((1 - X) ^ 6 : PowerSeries ℚ)⁻¹) ∧
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) +
        6 * a (n - 5) - a (n - 6)) := by
  sorry

end OMA.S_oeis_a201044
