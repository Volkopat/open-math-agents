import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic

/-!
# Median of a uniform multinomial variable

Source: R B, MathOverflow question 237342, https://mathoverflow.net/questions/237342
Credit: @LDJAI

Each of the `n` jobs independently chooses one of `2*k+1` servers uniformly.
Thus all functions from job indices to server indices are equally likely.
The order statistic includes multiplicities. The question fixes `k ≥ 1` while
`n` tends to infinity and asks for the order of the variance of the median.
-/

namespace OMA.S_mo_237342

open scoped BigOperators

/-- Number of jobs assigned to server `i`. -/
def load {n q : ℕ} (w : Fin n → Fin q) (i : Fin q) : ℕ :=
  ∑ j, if w j = i then 1 else 0

/-- Middle entry after sorting all server loads in nondecreasing order. -/
noncomputable def medianLoad {n k : ℕ} (w : Fin n → Fin (2 * k + 1)) : ℕ :=
  load w (Tuple.sort (load w) ⟨k, by omega⟩)

/-- Population variance under the uniform distribution on assignments. -/
noncomputable def medianVariance (k n : ℕ) : ℝ :=
  let Z := fun w : Fin n → Fin (2 * k + 1) ↦ (medianLoad w : ℝ)
  𝔼 w, (Z w - 𝔼 u, Z u) ^ 2

/-- For each fixed positive `k`, the median variance has the same asymptotic order
as the variance of one server, `n*p*(1-p)` with `p = 1/(2*k+1)`. -/
theorem main : ∀ k : ℕ, 0 < k →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      let p : ℝ := 1 / (2 * (k : ℝ) + 1)
      c * ((n : ℝ) * p * (1 - p)) ≤ medianVariance k n ∧
        medianVariance k n ≤ C * ((n : ℝ) * p * (1 - p)) := by
  sorry

end OMA.S_mo_237342
