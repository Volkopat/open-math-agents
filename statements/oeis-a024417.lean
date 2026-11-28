import Mathlib

/-!
# A024417: Index of maximum Stirling number of the second kind in row n

Source: https://oeis.org/A024417
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: For `n ≥ 1`, let `a(n)` be the least `k ∈ {1, ..., n}` maximizing the
Stirling number of the second kind `S(n, k)`. Then `a(n) ~ n / W(n) - 1` as `n → ∞`,
where `W` is the principal branch of the Lambert W function (`W(x) * exp(W(x)) = x`).
-/

namespace OMA.S_oeis_a024417

open Filter Topology

/-- Stirling numbers of the second kind `S(n, k)`. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (k + 1) * stirling2 n (k + 1) + stirling2 n k

/-- `a(n)` is the least `k ∈ {1, ..., n}` maximizing `S(n, k)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ k ≤ n ∧ ∀ j ∈ Finset.Icc 1 n, stirling2 n j ≤ stirling2 n k}

/-- Principal branch of the Lambert W function on `[0, ∞)`. -/
noncomputable def lambertW (x : ℝ) : ℝ :=
  sInf {w : ℝ | 0 ≤ w ∧ x ≤ w * Real.exp w}

theorem main :
    Tendsto (fun n : ℕ => (a n : ℝ) / ((n : ℝ) / lambertW (n : ℝ) - 1))
      atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a024417
