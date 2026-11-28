import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Real.Lemmas

namespace OMA.S_oeis_a346952

/-- `IsProdEnd3 m` holds if `m` is the product of two positive integers ending with decimal
digit `3`. -/
def IsProdEnd3 (m : ℕ) : Prop :=
  ∃ x y : ℕ, x % 10 = 3 ∧ y % 10 = 3 ∧ m = x * y

/-- `a(n)` (OEIS A346952): the number of `n`-digit positive integers (`10^(n-1) ≤ m < 10^n`)
that are the product of two integers ending with `3`. -/
noncomputable def a (n : ℕ) : ℕ :=
  letI := Classical.decPred IsProdEnd3
  ((Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter IsProdEnd3).card

/-- Conjecture (OEIS A346952): `lim_{n → ∞} a(n) / a(n - 1) = 10`. -/
theorem main :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (a (n - 1) : ℝ)) Filter.atTop (nhds (10 : ℝ)) := by
  sorry

end OMA.S_oeis_a346952
