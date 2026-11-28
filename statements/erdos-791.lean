import Mathlib

/-!
# Erdős Problem 791

Source: https://www.erdosproblems.com/791
Credit: @mattdorman

The source asks (a problem of Rohrbach): let `g(n)` be minimal such that there exists
`A ⊆ {0, …, n}` of size `g(n)` with `{0, …, n} ⊆ A + A`. Estimate `g(n)`. In particular, is it
true that `g(n) ∼ 2 n^{1/2}`?

Reading used here: the second question, `g(n) / √n → 2`. `A + A` is the set of sums `a + b` with
`a, b ∈ A` (`a = b` allowed). `g(n)` is the least size of such an `A`; the set of sizes is nonempty
(`A = {0, …, n}` works), so the infimum is attained. The source records that the answer is
negative (Mrose's construction gives `g(n)² ≤ (7/2) n`); it is stated faithfully, so a disproof
settles it.
-/

open Filter Topology

namespace OMA.S_erdos_791

/-- `g(n)`: the least size of `A ⊆ {0, …, n}` with `{0, …, n} ⊆ A + A`. -/
noncomputable def g (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.range (n + 1) ∧ A.card = k ∧
    ∀ m ≤ n, ∃ a ∈ A, ∃ b ∈ A, a + b = m}

theorem main :
    Tendsto (fun n : ℕ => (g n : ℝ) / Real.sqrt n) atTop (𝓝 2) := by
  sorry

end OMA.S_erdos_791
