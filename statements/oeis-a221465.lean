import Mathlib

/-!
# A221465: Number of 0..n arrays of length 6 with each element unequal to at least one neighbor, starting with 0.

Source: https://oeis.org/A221465
Credit: @cj-55m (agent: Claude Code, model claude-opus-5-5)

The entry (offset 1, data 5, 88, 513, 1856, 5125, 11880, 24353, 45568, 79461, 131000, ...)
records in its FORMULA section:

  Conjectures from Colin Barker, Aug 05 2018:
  G.f.: x*(5 + 58*x + 60*x^2 - 2*x^3 - x^4) / (1 - x)^6.
  a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>6.

Conventions:
* An array of length 6 with entries in `0..n` is a function `x : Fin 6 → Fin (n + 1)`
  (positions `0, 1, 2, 3, 4, 5`). It starts with `0` when `x 0 = 0`.
* Positions `i` and `j` are neighbors when they are adjacent, i.e. `j + 1 = i` or `i + 1 = j`;
  the two end positions have a single neighbor each. Each element is unequal to at least one
  neighbor when every position `i` has a neighbor `j` with `x i ≠ x j`.
* `a n` is the number of such arrays, defined for every `n : ℕ`. The entry has offset `1`;
  the definition gives `a 0 = 0` (the only array is constant), so the g.f. of the entry,
  `Sum_{n>=1} a(n) x^n`, is the power series with coefficients `a n` for all `n ≥ 0`.
* The statement is the conjunction of both conjectures: the order-6 linear recurrence for
  `n > 6` (in `ℤ`), and the g.f. identity written without division as
  `(1 - x)^6 * A(x) = x*(5 + 58*x + 60*x^2 - 2*x^3 - x^4)` in `PowerSeries ℤ`.
-/

namespace OMA.S_oeis_a221465

/-- `a n` = number of arrays `x : Fin 6 → Fin (n + 1)` with `x 0 = 0` in which every element
differs from at least one of its (adjacent) neighbors. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin 6 → Fin (n + 1))).filter fun x =>
    x 0 = 0 ∧ ∀ i : Fin 6, ∃ j : Fin 6, (j.val + 1 = i.val ∨ i.val + 1 = j.val) ∧ x i ≠ x j).card

/-- Colin Barker's conjectures for A221465: the linear recurrence for `n > 6` and the g.f.
`x*(5 + 58*x + 60*x^2 - 2*x^3 - x^4) / (1 - x)^6`. -/
theorem main :
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4)
        + 6 * a (n - 5) - a (n - 6)) ∧
    (1 - PowerSeries.X) ^ 6 * PowerSeries.mk (fun n => (a n : ℤ)) =
      PowerSeries.X * (5 + 58 * PowerSeries.X + 60 * PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3
        - PowerSeries.X ^ 4) := by
  sorry

end OMA.S_oeis_a221465
