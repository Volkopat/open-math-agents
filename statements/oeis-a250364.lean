import Mathlib

/-!
# A250364: length 6 arrays with x(i) in i..i+n and no value more than 3 times

A250364(n) is the number of arrays `x(1), ..., x(6)` with `x(i)` in `i..i+n` in which no
value appears more than 3 times. Here position `i : Fin 6` stands for index `i + 1` of the
source, and the array is encoded by its offsets `y i ∈ 0..n`, so that
`x(i + 1) = (i + 1) + y i` (`value y i`). A brute-force count of this reading gives
64, 729, 4048, 15365, 45866, 115963 for n = 1..6, matching the listed terms.

The offset is 1; `a 0` is not a term of the sequence and is set to 0 in the generating
function, which has no constant term.

The problem: the conjectures of Colin Barker (Nov 13 2018):
  G.f.: x*(64 + 281*x + 289*x^2 + 98*x^3 + 44*x^4 + 57*x^5 - 405*x^6 + 482*x^7 - 232*x^8
        + 42*x^9) / (1 - x)^7,
  a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7)
  for n > 10.
The g.f. is stated after multiplying both sides by (1 - x)^7. (The recurrence fails for
n = 8, 9, 10, so its range is kept exactly as in the source.)

Source: https://oeis.org/A250364
Credit: @VashaTS
-/

namespace OMA.S_oeis_a250364

open PowerSeries

/-- The entry `x(i + 1) = (i + 1) + y i` of the array with offsets `y`. -/
def value {n : ℕ} (y : Fin 6 → Fin (n + 1)) (i : Fin 6) : ℕ := i.val + 1 + (y i).val

/-- No value appears more than 3 times. -/
def AtMostThrice {n : ℕ} (y : Fin 6 → Fin (n + 1)) : Prop :=
  ∀ i : Fin 6, (Finset.univ.filter fun j : Fin 6 => value y j = value y i).card ≤ 3

instance {n : ℕ} (y : Fin 6 → Fin (n + 1)) : Decidable (AtMostThrice y) := by
  unfold AtMostThrice; infer_instance

/-- A250364(n). -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun y : Fin 6 → Fin (n + 1) => AtMostThrice y).card

theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (64 + 281 * X + 289 * X ^ 2 + 98 * X ^ 3 + 44 * X ^ 4 + 57 * X ^ 5 - 405 * X ^ 6
        + 482 * X ^ 7 - 232 * X ^ 8 + 42 * X ^ 9) ∧
    ∀ n : ℕ, 10 < n →
      (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4)
        + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a250364
