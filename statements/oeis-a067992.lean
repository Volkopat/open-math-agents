import Mathlib

/-!
# OEIS A067992: adjacent terms are coprime

Source: https://oeis.org/A067992
`a 0 = 1` and, for `n > 0`, `a n` is the smallest positive integer such that the ratios
`min(a k / a (k-1), a (k-1) / a k)` for `0 < k ≤ n` are all distinct. Every positive rational
appears exactly once as a ratio of adjacent terms. Conjecture: adjacent terms are always
relatively prime.

Conventions. The sequence is determined by its greedy definition; `main` quantifies over
every `a : ℕ → ℕ` satisfying it. `r k = min(a k / a (k-1), a (k-1) / a k)` is computed in `ℚ`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a067992

/-- The ratio `min(x/y, y/x)` in `ℚ`. -/
def ratio (x y : ℕ) : ℚ := min ((x : ℚ) / y) ((y : ℚ) / x)

/-- Taking `a n = m` keeps the ratios `r 1, …, r n` pairwise distinct. -/
def Admissible (a : ℕ → ℕ) (n m : ℕ) : Prop :=
  ∀ k, 0 < k → k < n → ratio (a k) (a (k - 1)) ≠ ratio m (a (n - 1))

theorem main :
    ∀ a : ℕ → ℕ, a 0 = 1 →
      (∀ n, 0 < n → 0 < a n ∧ Admissible a n (a n) ∧
        ∀ m, 0 < m → m < a n → ¬ Admissible a n m) →
      ∀ n, Nat.Coprime (a n) (a (n + 1)) := by
  sorry

end OMA.S_oeis_a067992
