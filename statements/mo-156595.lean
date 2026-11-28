import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Choose.Basic

/-! Source: https://mathoverflow.net/questions/156595
Sequence: https://oeis.org/A111138 -/

namespace OMA.S_mo_156595

open Filter
open scoped Topology

def TriRep (m t s : ℕ) : Prop := m = t.choose 2 + s ∧ s < t

def TriCount (t s : ℕ) : ℕ := t.choose 3 + s.choose 2

/-- The triangular-row count has leading term (√(2m))³/6, with explicit
error at most 12m for every positive m. -/
theorem main :
    (∀ m t s : ℕ, 0 < m → TriRep m t s →
      |(TriCount t s : ℝ) - (Real.sqrt (2 * (m : ℝ))) ^ 3 / 6| ≤ 12 * (m : ℝ)) ∧
    (∀ T S : ℕ → ℕ, (∀ m, TriRep m (T m) (S m)) →
      Tendsto (fun m : ℕ => (TriCount (T m) (S m) : ℝ) / (Real.sqrt (2 * (m : ℝ))) ^ 3)
        atTop (𝓝 (1 / 6 : ℝ))) := by
  sorry

end OMA.S_mo_156595
