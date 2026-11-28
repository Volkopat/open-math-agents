import Mathlib

/-!
# A014197: Number of positive integers m with Euler's totient phi(m) = n

Source: https://oeis.org/A014197

Conjecture (R. D. Carmichael):
There are no `1`'s in this sequence; that is, for every `n ≥ 1`, the equation
`φ(m) = n` never has a unique solution `m`.

Conventions:
- Offset: `1` (`n ≥ 1`).
- First terms: `a(1) = 2` (`m ∈ {1, 2}`), `a(2) = 3` (`m ∈ {3, 4, 6}`), `a(3) = 0`,
  `a(4) = 4`, `a(5) = 0`, `a(6) = 4`, `a(7) = 0`, `a(8) = 5`, ...
- For `n ≥ 1`, `{m : ℕ | Nat.totient m = n}` is finite and excludes `0` since
  `Nat.totient 0 = 0`, so `Set.ncard` counts the exact number of solutions.
-/

namespace OMA.S_oeis_a014197

/-- Number of integers `m : ℕ` such that `Nat.totient m = n` (OEIS A014197). -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {m : ℕ | Nat.totient m = n}

/-- Conjecture (Carmichael): `a(n) ≠ 1` for all `n ≥ 1`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → a n ≠ 1 := by
  sorry

end OMA.S_oeis_a014197
