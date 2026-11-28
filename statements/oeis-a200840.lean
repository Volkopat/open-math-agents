import Mathlib

/-!
# A200840: Number of 0..n arrays x(0..4) of 5 elements without any two consecutive increases or two consecutive decreases.

Source: https://oeis.org/A200840
Credit: @Salofe

Conjectures from Colin Barker, Oct 14 2017, quoted verbatim from the entry:
* "G.f.: x*(32 - x + 10*x^2 - 14*x^3 + 6*x^4 - x^5) / (1 - x)^6."
* "a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>6."

Formalization notes:
* Offset 1, as in the entry (data: 32, 191, 676, 1817, 4108, 8239, ...). The value `a 0`
  (entries in 0..0) is never used.
* An array is a map `x : Fin 5 → Fin (n + 1)`: an entry `x i` in 0..n at each position
  `i ∈ {0, 1, 2, 3, 4}`, the positions of x(0..4). Arrays are labelled: they are not identified
  up to symmetry.
* "Two consecutive increases" means three consecutive positions `i`, `j = i + 1`, `k = j + 1`
  with `x i < x j < x k`; "two consecutive decreases" means `x i > x j > x k`. Equal
  neighbours are neither an increase nor a decrease, so they are allowed.
* This reading reproduces the data: exhaustive enumeration gives 32, 191, 676, 1817, 4108, 8239,
  15128 for n = 1, ..., 7 (a(1) = 2^5, as no array with entries in 0..1 has two consecutive
  strict increases or decreases), the 16 solutions shown in the entry for n = 3 satisfy it, and a
  transfer count over consecutive entries agrees with all 210 terms of the b-file.
* The g.f. is the ordinary one, Sum_{n>=1} a(n) x^n, stated as an identity of formal power series
  over `ℚ` with the denominator `(1 - x)^6` cleared (it has constant coefficient 1, so it is
  invertible). The coefficient of x^0 is 0 since the sequence starts at n = 1.
* The recurrence is stated in `ℤ` for every n > 6, as in the entry.
-/

namespace OMA.S_oeis_a200840

/-- The array `x` (positions 0..4, entries in 0..n) has no two consecutive increases and no two
consecutive decreases: for any three consecutive positions `i`, `j = i + 1`, `k = j + 1`, it is
neither the case that `x i < x j < x k` nor that `x i > x j > x k`. -/
def Good {n : ℕ} (x : Fin 5 → Fin (n + 1)) : Prop :=
  ∀ i j k : Fin 5, j.val = i.val + 1 → k.val = j.val + 1 →
    ¬ (x i < x j ∧ x j < x k) ∧ ¬ (x i > x j ∧ x j > x k)

/-- A200840(n): the number of arrays x(0..4) of 5 elements in 0..n without any two consecutive
increases or two consecutive decreases. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact Fintype.card {x : Fin 5 → Fin (n + 1) // Good x}

open PowerSeries in
/-- Barker's conjectures: the generating function
`x(32 - x + 10x^2 - 14x^3 + 6x^4 - x^5)/(1 - x)^6`, and the recurrence
`a(n) = 6a(n-1) - 15a(n-2) + 20a(n-3) - 15a(n-4) + 6a(n-5) - a(n-6)` for `n > 6`. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 6 =
        X * (32 - X + 10 * X ^ 2 - 14 * X ^ 3 + 6 * X ^ 4 - X ^ 5) ∧
    ∀ n : ℕ, 6 < n → (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) -
      15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  sorry

end OMA.S_oeis_a200840
