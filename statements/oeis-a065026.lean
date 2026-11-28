import Mathlib

/-!
# A065026: a(1) = 1; for n>1, a(n) = smallest number that is not a sum or product of any subset of the numbers a(1) to a(n-1).

Source: https://oeis.org/A065026
Credit: @cblly (agent: Claude Code, model claude-opus-5-5)

The entry has offset 1 and data `1, 2, 4, 9, 17, 25, 59, 67, 176, 226, 578, 628, 1340, …`.
Its Formula section records:

  Conjectures from Colin Barker, Jun 19 2019:
  G.f.: x*(1 - x)*(1 + 3*x + 5*x^2 + 10*x^3 + 15*x^4 + 14*x^5 + 25*x^6 + 10*x^7 + 8*x^8
    + 18*x^9 + 42*x^10 - 402*x^12 - 552*x^13 - 720*x^14 - 804*x^15) / (1 - 2*x^2 - 4*x^4 + 2*x^6).
  a(n) = 2*a(n-2) + 4*a(n-4) - 2*a(n-6) for n>17.

Both conjectures are formalized, as a conjunction.

Conventions.
- "Sum or product of any subset" is read, as in the entry's example for `a(4) = 9`, as the sum or
  the product of the elements of a nonempty subset of `{a(1), …, a(n-1)}` (one or more terms).
  The terms are distinct, so subsets of terms and subsets of the set of terms are the same.
- "Smallest number" is the smallest positive integer.
- With these readings the definition reproduces the first 22 listed terms (checked by computer).
- `terms n` is the list `[a(1), …, a(n)]` and `a n` is its last element.
- The recurrence is stated in `ℤ`, so the subtraction is not truncated.
- The generating function `∑_{n ≥ 1} a(n) x^n` is stated as a formal power series over `ℤ` whose
  coefficient of `x ^ 0` is `0` (the sequence starts at `n = 1`), multiplied out by the
  denominator `1 - 2x^2 - 4x^4 + 2x^6`.
-/

namespace OMA.S_oeis_a065026

open PowerSeries

/-- `m` is the sum, or the product, of the elements of some nonempty subset of `s`. -/
def Reachable (s : Finset ℕ) (m : ℕ) : Prop :=
  ∃ t ⊆ s, t.Nonempty ∧ ((∑ x ∈ t, x) = m ∨ (∏ x ∈ t, x) = m)

/-- `terms n` is the list `[a(1), …, a(n)]`: `a(1) = 1`, and for `n > 1`, `a(n)` is the smallest
positive integer that is not a sum or product of a nonempty subset of `a(1), …, a(n-1)`. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | n + 2 => terms (n + 1) ++ [sInf {m : ℕ | 0 < m ∧ ¬ Reachable (terms (n + 1)).toFinset m}]

/-- `a n`, the `n`-th term of A065026 (offset 1, so `a 1 = 1`). -/
noncomputable def a (n : ℕ) : ℕ :=
  (terms n).getLast?.getD 0

/-- Colin Barker's conjectures: the recurrence for `n > 17` and the rational generating function. -/
theorem main :
    (∀ n : ℕ, 17 < n →
      (a n : ℤ) = 2 * (a (n - 2) : ℤ) + 4 * (a (n - 4) : ℤ) - 2 * (a (n - 6) : ℤ)) ∧
    ((1 - 2 * X ^ 2 - 4 * X ^ 4 + 2 * X ^ 6) *
        PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) =
      X * (1 - X) * (1 + 3 * X + 5 * X ^ 2 + 10 * X ^ 3 + 15 * X ^ 4 + 14 * X ^ 5 + 25 * X ^ 6
        + 10 * X ^ 7 + 8 * X ^ 8 + 18 * X ^ 9 + 42 * X ^ 10 - 402 * X ^ 12 - 552 * X ^ 13
        - 720 * X ^ 14 - 804 * X ^ 15)) := by
  sorry

end OMA.S_oeis_a065026
