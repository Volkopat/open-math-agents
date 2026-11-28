import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Topology.Instances.Real.Lemmas

namespace OMA.S_oeis_a346509

/-- `IsProdGt1End1 m` holds if `m` is the product of two integers greater than `1` ending with
decimal digit `1`. -/
def IsProdGt1End1 (m : ℕ) : Prop :=
  ∃ x y : ℕ, 1 < x ∧ 1 < y ∧ x % 10 = 1 ∧ y % 10 = 1 ∧ m = x * y

/-- `a(n)` (OEIS A346509): the number of `n`-digit positive integers (`10^(n-1) ≤ m < 10^n`)
that are the product of two integers greater than `1` and ending with `1`. -/
noncomputable def a (n : ℕ) : ℕ :=
  letI := Classical.decPred IsProdGt1End1
  ((Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter IsProdGt1End1).card

/-- Conjecture (OEIS A346509): `lim_{n → ∞} a(n) / a(n - 1) = 10`. -/
theorem main :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (a (n - 1) : ℝ)) Filter.atTop (nhds (10 : ℝ)) := by
  sorry

end OMA.S_oeis_a346509
