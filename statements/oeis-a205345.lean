import Mathlib

/-!
# A205345: Number of length 8 nonnegative integer arrays starting and ending with 0 with adjacent elements unequal but differing by no more than n.

Source: https://oeis.org/A205345
Credit: @Salofe

Conjectures from Colin Barker, Jun 11 2018, quoted verbatim from the entry (by R. H. Hardin,
Jan 26 2012):
"Conjectures from Colin Barker, Jun 11 2018: (Start)
G.f.: 2*x^2*(136 + 684*x + 730*x^2 + 129*x^3 + 3*x^4) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.
(End)"

Formalization notes:
* Offset 1, as in the entry (data: 0, 272, 3272, 18652, 71630, 214724, ...).
* An array of length 8 is a map `x : Fin 8 → ℕ` (positions 0..7); its entries are nonnegative
  integers. "Starting and ending with 0" means `x 0 = 0` and `x 7 = 0`. The adjacent pairs are
  x(i), x(i+1) for i = 0..6, that is `x i.castSucc` and `x i.succ` for `i : Fin 7`. "Unequal"
  is `≠`, and "differing by no more than n" is |x(i) - x(i+1)| ≤ n, written in `ℕ` as the two
  inequalities `x i.castSucc ≤ x i.succ + n` and `x i.succ ≤ x i.castSucc + n`. Arrays are
  labelled: they are not identified up to symmetry.
* `a n` is the number of such arrays, `Nat.card` of the subtype of valid arrays. This set is
  finite (entry i of a valid array is at most min(i, 7 - i) * n <= 3n, since each step changes
  the value by at most n), so `Nat.card` is its number of elements.
* The definition also makes sense for n = 0, outside the range of the entry: there no array is
  valid (adjacent entries would have to be unequal and differ by 0), so it gives 0. The g.f. is
  the ordinary one, Sum_{n>=1} a(n) x^n, so the coefficient of x^0 of the series is set to 0.
* The g.f. is stated as an identity of formal power series over `ℚ` with the denominator
  (1 - x)^7 cleared (it has constant coefficient 1, so it is invertible in `ℚ⟦X⟧`).
* The recurrence is stated in `ℤ` for every n > 7, as in the entry (all indices are then >= 1).
* The entry's empirical polynomial formula (R. H. Hardin) is not part of these conjectures and
  is not stated here.
* Checks: a brute-force evaluation of this definition (entries searched up to 4n + 3) gives
  0, 0, 272, 3272, 18652 for n = 0..4, and no valid array has an entry above 3n; a transfer
  count of the same definition agrees with the b-file for n = 1..60; the 16 example solutions
  shown in the entry for n = 5 satisfy the definition.
-/

namespace OMA.S_oeis_a205345

/-- An array `x(0..7)` of nonnegative integers is valid for `n` when it starts and ends with 0
and any two adjacent entries are unequal and differ by at most `n`. -/
def IsValid (n : ℕ) (x : Fin 8 → ℕ) : Prop :=
  x 0 = 0 ∧ x 7 = 0 ∧
    ∀ i : Fin 7, x i.castSucc ≠ x i.succ ∧ x i.castSucc ≤ x i.succ + n ∧
      x i.succ ≤ x i.castSucc + n

/-- A205345(n): the number of valid length 8 arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {x : Fin 8 → ℕ // IsValid n x}

open PowerSeries in
/-- Barker's conjectures: the generating function
`2x^2(136 + 684x + 730x^2 + 129x^3 + 3x^4)/(1 - x)^7` and the recurrence
`a(n) = 7a(n-1) - 21a(n-2) + 35a(n-3) - 35a(n-4) + 21a(n-5) - 7a(n-6) + a(n-7)` for `n > 7`. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
        2 * X ^ 2 * (136 + 684 * X + 730 * X ^ 2 + 129 * X ^ 3 + 3 * X ^ 4) ∧
    ∀ n : ℕ, 7 < n →
      (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) +
        21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a205345
