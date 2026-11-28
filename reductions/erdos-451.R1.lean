import OMAStatements.S_erdos_451
import Mathlib

/-!
Reduction erdos-451.R1: Erdős Problem 451 split into well-definedness and the two asymptotics.

`n` is good for `k` when `n > 2k` and no prime `p` with `k < p < 2k` divides
`(n - 1) (n - 2) ⋯ (n - k)`, and `leastGood k n` says that `n` is the least such integer.
The statement of the problem asks for a function `f` with `leastGood k (f k)` for every `k`,
subexponential, and beyond every fixed power of `k`.

H1 is well-definedness: a least good integer exists for every `k ≥ 1`.  It is a small counting
argument: `n = (2k)! (2k + 2)` is good for `k`, because every prime `p < 2k` divides `(2k)!`, so
`n` is divisible by `p` while `n - i` is not, for `1 ≤ i ≤ k`.
H2 is the subexponential upper bound for any function that picks the least good integer.
H3 is the lower bound `k^d < f k` for every fixed `d`, for such a function.
H2 and H3 are the open content of the problem.
-/

namespace OMA.R_erdos_451_R1

open Filter
open OMA.S_erdos_451 (good leastGood)

/-- Well-definedness: for every `k ≥ 1` there is a least good integer. -/
def H1 : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ n : ℕ, leastGood k n

/-- The subexponential upper bound, for any function that is pointwise a least good integer. -/
def H2 : Prop :=
  ∀ g : ℕ → ℕ, (∀ k : ℕ, 1 ≤ k → leastGood k (g k)) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (g k : ℝ) < Real.exp (ε * k)

/-- The lower bound `k ^ d < f k` for every fixed real `d > 0`, for any such function. -/
def H3 : Prop :=
  ∀ g : ℕ → ℕ, (∀ k : ℕ, 1 ≤ k → leastGood k (g k)) →
    ∀ d : ℝ, 0 < d → ∀ᶠ k : ℕ in atTop, (k : ℝ) ^ d < g k

theorem main : H1 → H2 → H3 → type_of% @OMA.S_erdos_451.main := by
  rintro h1 h2 h3
  classical
  set f : ℕ → ℕ := fun k => if h : 1 ≤ k then Classical.choose (h1 k h) else 0 with hf
  have hfm : ∀ k : ℕ, 1 ≤ k → leastGood k (f k) := by
    intro k hk
    have hfk : f k = Classical.choose (h1 k hk) := by
      simp only [hf, dif_pos hk]
    rw [hfk]
    exact Classical.choose_spec (h1 k hk)
  exact ⟨f, hfm, h2 f hfm, h3 f hfm⟩

end OMA.R_erdos_451_R1
