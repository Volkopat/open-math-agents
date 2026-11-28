import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OMA.S_mo_514194

open Filter
open scoped BigOperators Topology

/-- The ordinary limit of the partial sums of a real series. -/
def SeriesEquals (term : ℕ → ℝ) (value : ℝ) : Prop :=
  Tendsto (fun m : ℕ => ∑ n ∈ Finset.range m, term n) atTop (𝓝 value)

/-- The binomial coefficient sequence in the final identity of the question. -/
noncomputable def b (n : ℕ) : ℝ :=
  if n = 0 then 1 else
    3 * ∑ k ∈ Finset.range (n / 3 + 1),
      (-1 : ℝ) ^ k * (Nat.choose n k : ℝ) ^ 3 *
        (Nat.choose (n + k) n : ℝ) * (Nat.choose (2 * n - k) n : ℝ) *
        (Nat.choose (2 * n - 3 * k) n : ℝ) *
        ((n : ℝ) - 2 * k) / (2 * (n : ℝ) - 3 * k)

/-- The five identities marked as conjectural in the original question. -/
theorem main :
    SeriesEquals (fun n =>
      ((3 * n).factorial : ℝ) * (5 * n).factorial /
        (2 ^ (15 * n) * (2 * n).factorial * (n.factorial : ℝ) ^ 6) *
        (6671 * (n : ℝ) ^ 3 + 5278 * (n : ℝ) ^ 2 + 1185 * n + 90) / (2 * n + 1))
      (1920 / Real.pi ^ 2) ∧
    SeriesEquals (fun n =>
      ((4 * n).factorial : ℝ) * (5 * n).factorial /
        (2 ^ (10 * n) * 3 ^ (5 * n) * ((2 * n).factorial : ℝ) ^ 2 *
          (n.factorial : ℝ) ^ 5) *
        (2924 * (n : ℝ) ^ 3 + 2247 * (n : ℝ) ^ 2 + 445 * n + 30) / (2 * n + 1))
      (360 / Real.pi ^ 2) ∧
    SeriesEquals (fun n =>
      ((8 * n).factorial : ℝ) /
        (7 ^ (8 * n) * ((2 * n).factorial : ℝ) ^ 2 * (n.factorial : ℝ) ^ 4) *
        (209610 * (n : ℝ) ^ 3 + 149637 * (n : ℝ) ^ 2 + 25824 * n + 1440) / (2 * n + 1))
      (16807 / Real.pi ^ 2) ∧
    SeriesEquals (fun n =>
      ((12 * n).factorial : ℝ) /
        (33 ^ (6 * n) * (6 * n).factorial * (2 * n).factorial * (n.factorial : ℝ) ^ 4) *
        (534060 * (n : ℝ) ^ 3 + 363222 * (n : ℝ) ^ 2 + 51776 * n + 2240) / (2 * n + 1))
      (3993 * Real.sqrt 33 / Real.pi ^ 2) ∧
    SeriesEquals (fun n =>
      b n * (8210 * (n : ℝ) ^ 2 + 5095 * n + 1014) * (-1 / 243 : ℝ) ^ n)
      (13851 / (2 * Real.pi ^ 2)) := by
  sorry

end OMA.S_mo_514194
