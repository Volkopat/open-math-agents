import Mathlib

/-!
# ℓ², ℓ³ and ℓ⁴: a possible fixed point result?

Source: https://mathoverflow.net/questions/18264
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Let `K` be the closed unit ball of `ℓ²` and `T : K → K` with
`‖Tx - Ty‖_{ℓ⁴} ≤ ‖x - y‖_{ℓ³}` for all `x, y ∈ K`. Is it true that `T` has a fixed point?

Conventions:
* Real sequences `x : ℕ → ℝ`. `K = {x | ∑ xᵢ² converges and is ≤ 1}`; since `ℓ² ⊆ ℓ³ ⊆ ℓ⁴`, the
  `ℓ³` and `ℓ⁴` norms of differences of points of `K` are finite, and are written
  `(∑ |xᵢ - yᵢ|^p)^(1/p)` with `tsum`.
* A self-map of `K` is a map `T : (ℕ → ℝ) → (ℕ → ℝ)` sending `K` into `K` (its values outside
  `K` are irrelevant).
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_mo_18264

/-- The closed unit ball of `ℓ²`. -/
def K : Set (ℕ → ℝ) := {x | Summable (fun i => x i ^ 2) ∧ ∑' i, x i ^ 2 ≤ 1}

/-- The `ℓ^p` norm `(∑ |xᵢ|^p)^(1/p)`. -/
noncomputable def lpNorm (p : ℝ) (x : ℕ → ℝ) : ℝ := (∑' i, |x i| ^ p) ^ (1 / p)

/-- Such a `T` has a fixed point. -/
theorem main : ∀ T : (ℕ → ℝ) → (ℕ → ℝ), (∀ x ∈ K, T x ∈ K) →
    (∀ x ∈ K, ∀ y ∈ K, lpNorm 4 (T x - T y) ≤ lpNorm 3 (x - y)) →
    ∃ x ∈ K, T x = x := by
  sorry

end OMA.S_mo_18264
