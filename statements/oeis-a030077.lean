import Mathlib

/-!
# OEIS A030077: distinct path lengths on a regular polygon, prime case

Source: https://oeis.org/A030077
Take `n` equally spaced points on a circle and connect them by a path with `n - 1` segments
(a Hamiltonian path); `a n` is the number of distinct path lengths. There are `⌊n/2⌋`
distinct segment lengths, so `a n` is at most the number of compositions of `n - 1` into
`⌊n/2⌋` nonnegative parts, `binom(n - 2 + ⌊n/2⌋, ⌊n/2⌋ - 1)` (A099578(n-2)). Conjecture: the
bound is attained when `n` is prime.

Conventions. Points are `exp(2πik/n)`, `k : Fin n`; a path is a bijection `p : Fin n ≃ Fin n`
(visiting order); its length is `∑_{i < n-1} |z(p i) - z(p (i+1))|`. `n ≥ 3`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a030077

open Complex

/-- The `k`-th of `n` equally spaced points on the unit circle. -/
noncomputable def pt (n : ℕ) (k : Fin n) : ℂ := exp (2 * Real.pi * I * (k : ℕ) / n)

/-- Length of the path visiting the points in the order `p 0, p 1, …, p (n-1)`. -/
noncomputable def pathLength {n : ℕ} (p : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i : Fin n, if h : i.val + 1 < n then ‖pt n (p i) - pt n (p ⟨i.val + 1, h⟩)‖ else 0

/-- The number of distinct path lengths. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard (Set.range (pathLength (n := n)))

theorem main :
    ∀ n : ℕ, n.Prime → 3 ≤ n → a n = (n - 2 + n / 2).choose (n / 2 - 1) := by
  sorry

end OMA.S_oeis_a030077
