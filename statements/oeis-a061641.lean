import Mathlib

/-!
# OEIS A061641: density of pure Collatz numbers

Source: https://oeis.org/A061641
A number `n` is pure if every preimage of `n` under iteration of the Collatz map `C` is
`≥ n`; equivalently there is no `r < n` with `C^k(r) = n` for some `k`. The sequence lists
the pure numbers `0, 1, 3, 6, 7, 9, …`. Conjecture (Adamson): `a(n)/n → C` for a constant
`C = 2.311…`. `main` states that `a(n)/n` converges (to some real `C`).

Conventions. `C n = n/2` for even `n` and `3n + 1` for odd `n`; `a n` is the `n`-th pure
number counted from `a 0 = 0` (the index shift does not affect the limit).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a061641

open Filter Topology

/-- The Collatz map. -/
def collatz (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- `n` is pure: no smaller number reaches `n`. -/
def IsPure (n : ℕ) : Prop := ¬ ∃ r < n, ∃ k : ℕ, collatz^[k] r = n

theorem main :
    ∃ C : ℝ, Tendsto (fun n : ℕ => (Nat.nth IsPure n : ℝ) / n) atTop (𝓝 C) := by
  sorry

end OMA.S_oeis_a061641
