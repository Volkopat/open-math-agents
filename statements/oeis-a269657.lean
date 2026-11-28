import Mathlib

/-!
# A269657: Number of length-4 0..n arrays with no adjacent pair x,x+1 repeated

Source: https://oeis.org/A269657 (conjectures by Colin Barker, Jan 25 2019)

Entry (offset 0): Number of length-4 0..n arrays with no adjacent pair x,x+1 repeated.
Formula section, Conjectures from Colin Barker, Jan 25 2019:
G.f.: (1 + 10*x + 14*x^2 - 2*x^3 + x^4) / (1 - x)^5.
a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5.

Formalization notes:
* An array is a function `v : Fin 4 → Fin (n + 1)`, i.e. entries in {0,...,n}.
* Its adjacent pairs are `(v i, v (i+1))` for `i = 0, 1, 2` (indexed by `i : Fin 3`).
  An adjacent pair `x,x+1` is repeated when two different positions `i < j` carry the same
  adjacent pair and that pair has the form `x, x+1`; `repeated` expresses this.
* `a n` counts the arrays with no repeated adjacent pair `x,x+1`.
* Since `(1 - x)^5` has constant term 1, the identity A(x) = N/D for
  A(x) = Sum_(n >= 0) a(n) x^n is stated as A * D = N in the formal power series ring over the
  integers. The recurrence is stated in the integers, for n > 5 as in the entry.
* Controls from the entry: a(0..) = 1, 15, 79, 253, 621.
-/

namespace OMA.S_oeis_a269657

open PowerSeries

/-- Some adjacent pair of the form `x, x+1` occurs at two different positions of `w`. -/
abbrev repeated (w : Fin 4 → ℕ) : Prop :=
  ∃ i j : Fin 3, i < j ∧ w i.castSucc = w j.castSucc ∧ w i.succ = w j.succ ∧
    w i.succ = w i.castSucc + 1

/-- A269657(n): the number of length-4 arrays with entries in {0,...,n} and no repeated
adjacent pair `x, x+1`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun v : Fin 4 → Fin (n + 1) => ¬ repeated (fun i => (v i : ℕ))).card

/-- Barker's generating function and recurrence. -/
theorem main :
    mk (fun n => (a n : ℤ)) * (1 - X) ^ 5 =
      (1 + 10 * X + 14 * X ^ 2 - 2 * X ^ 3 + X ^ 4 : PowerSeries ℤ) ∧
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5)) := by
  sorry

end OMA.S_oeis_a269657
