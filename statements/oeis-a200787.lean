import Mathlib

/-!
# A200787: Number of 0..n arrays x(0..4) of 5 elements without any two consecutive increases.

Source: https://oeis.org/A200787
Credit: @rtflynn (agent: Claude Code, model claude-fable-5-2)

The entry (offset 1, data 32, 216, 840, 2425, 5796, 12152, 23136, 40905, 68200, 108416, ...)
records in its FORMULA section:

  Empirical: a(n) = (7/12)*n^5 + (47/12)*n^4 + (39/4)*n^3 + (133/12)*n^2 + (17/3)*n + 1.
  Conjectures from Colin Barker, Oct 15 2017:
  G.f.: x*(32 + 24*x + 24*x^2 - 15*x^3 + 6*x^4 - x^5) / (1 - x)^6.
  a(n) = (1 + n)^2*(12 + 44*n + 33*n^2 + 7*n^3) / 12.
  a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>6.

Conventions:
* An array `x(0..4)` with entries in `0..n` is a function `x : Fin 5 → Fin (n + 1)`
  (positions `0, 1, 2, 3, 4`).
* It has two consecutive increases when `x i < x j < x k` for three successive positions
  `i, j = i + 1, k = j + 1`. `a n` counts the arrays with no such triple.
* `a n` is defined for every `n : ℕ`; the entry has offset `1`. The definition gives `a 0 = 1`
  (the single constant array), which the closed form also gives, so the closed form is stated
  for all `n`. The g.f. of the entry is `Sum_{n>=1} a(n) x^n`, so its coefficient at `x^0`
  is `0`: it is the power series with coefficients `if n = 0 then 0 else a n`.
* The empirical formula and Barker's closed form are the same polynomial
  (`(1 + n)^2*(12 + 44*n + 33*n^2 + 7*n^3) = 7*n^5 + 47*n^4 + 117*n^3 + 133*n^2 + 68*n + 12`);
  it is stated without division as `12 * a n = (1 + n)^2*(12 + 44*n + 33*n^2 + 7*n^3)` in `ℤ`.
* The statement is the conjunction of the closed form, the order-6 linear recurrence for
  `n > 6` (in `ℤ`), and the g.f. identity written without division as
  `(1 - x)^6 * A(x) = x*(32 + 24*x + 24*x^2 - 15*x^3 + 6*x^4 - x^5)` in `PowerSeries ℤ`.
-/

namespace OMA.S_oeis_a200787

/-- `a n` = number of arrays `x : Fin 5 → Fin (n + 1)` with no three successive positions
`i, j, k` such that `x i < x j < x k`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin 5 → Fin (n + 1))).filter fun x =>
    ∀ i j k : Fin 5, i.val + 1 = j.val → j.val + 1 = k.val → ¬(x i < x j ∧ x j < x k)).card

/-- The empirical closed form and Colin Barker's conjectures for A200787: the closed form,
the linear recurrence for `n > 6`, and the g.f.
`x*(32 + 24*x + 24*x^2 - 15*x^3 + 6*x^4 - x^5) / (1 - x)^6`. -/
theorem main :
    (∀ n : ℕ, 12 * (a n : ℤ) =
      (1 + (n : ℤ)) ^ 2 * (12 + 44 * (n : ℤ) + 33 * (n : ℤ) ^ 2 + 7 * (n : ℤ) ^ 3)) ∧
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4)
        + 6 * a (n - 5) - a (n - 6)) ∧
    (1 - PowerSeries.X) ^ 6 * PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) =
      PowerSeries.X * (32 + 24 * PowerSeries.X + 24 * PowerSeries.X ^ 2 - 15 * PowerSeries.X ^ 3
        + 6 * PowerSeries.X ^ 4 - PowerSeries.X ^ 5) := by
  sorry

end OMA.S_oeis_a200787
