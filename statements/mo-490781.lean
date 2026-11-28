import Mathlib

/-!
# Manickam–Miklós–Singhi and Manickam–Miklós conjectures

Source: https://mathoverflow.net/questions/490781
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Let `A(n, k)` be the minimum, over reals `x₁, …, x_n` with nonnegative sum, of the number of
`k`-element subsets with nonnegative sum. The question recalls two conjectures from
Manickam–Miklós (1987): (MMS) `A(n, k) = C(n-1, k-1)` for `n ≥ 4k`; (MM)
`A(n, k) = C(n - ⌊n/k⌋, k)` for `n < 4k` with `k ∤ n`.

Conventions:
* `1 ≤ k ≤ n`. `main` states both conjectures as listed in the question.
-/

namespace OMA.S_mo_490781

/-- The number of `k`-subsets of `Fin n` with nonnegative `x`-sum. -/
noncomputable def cnt (n k : ℕ) (x : Fin n → ℝ) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card = k ∧ 0 ≤ ∑ i ∈ S, x i)).card

/-- `A(n, k)`. -/
noncomputable def A (n k : ℕ) : ℕ := sInf {m | ∃ x : Fin n → ℝ, 0 ≤ ∑ i, x i ∧ m = cnt n k x}

theorem main :
    (∀ n k : ℕ, 1 ≤ k → 4 * k ≤ n → A n k = (n - 1).choose (k - 1)) ∧
    (∀ n k : ℕ, 1 ≤ k → k ≤ n → n < 4 * k → ¬ k ∣ n → A n k = (n - n / k).choose k) := by
  sorry

end OMA.S_mo_490781
