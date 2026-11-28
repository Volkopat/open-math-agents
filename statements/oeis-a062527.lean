import Mathlib

/-!
# A062527: Smallest number (> 1) which appears at least n times in Pascal's triangle

Source: https://oeis.org/A062527

Conjecture (Singmaster's Conjecture):
The multiplicity of any integer `m > 1` in Pascal's triangle is bounded by a finite
universal constant; equivalently, the sequence A062527 is finite.

Conventions:
- Offset: `1`; first terms: `a(1) = 2`, `a(2) = 3`, `a(3) = 6`, `a(4) = 10`,
  `a(5) = 120`, `a(6) = 120`, `a(7) = 3003`, `a(8) = 3003`.
- For `m ≥ 2`, the set `{(n, k) | k ≤ n ∧ Nat.choose n k = m}` is finite (since `m ≥ 2`
  forces `1 ≤ k ≤ n - 1` and `n ≤ m`), so `Set.ncard` gives its exact multiplicity.
-/

namespace OMA.S_oeis_a062527

/-- Number of pairs `(n, k)` with `k ≤ n` such that `Nat.choose n k = m`. -/
noncomputable def pascalMultiplicity (m : ℕ) : ℕ :=
  Set.ncard {p : ℕ × ℕ | p.2 ≤ p.1 ∧ Nat.choose p.1 p.2 = m}

/-- Singmaster's Conjecture: there is a uniform upper bound on the multiplicity of every
integer `m ≥ 2` in Pascal's triangle (so OEIS A062527 is finite). -/
theorem main :
    ∃ B : ℕ, ∀ m : ℕ, 2 ≤ m → pascalMultiplicity m ≤ B := by
  sorry

end OMA.S_oeis_a062527
