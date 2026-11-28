import Mathlib

namespace OMA.S_oeis_a397245

/-- OEIS A397245: O.g.f. satisfies `A(x) = exp(x + ∑_{n ≥ 2} (4*n^2 - 1) * a(n) * x^n / (4*n^2))`,
equivalently `a(0) = 1`, `a(1) = 1`, and for `n ≥ 2`,
`a(n) = 4 * n * (a(n - 1) + ∑_{k=2}^{n-1} ((4*k^2 - 1) / (4*k)) * a(k) * a(n - k))`.
Conjectures:
1. `a(n) ≡ 1 (mod 3)` iff `n + 2` is of the form `3^m` or `2 * 3^m`.
2. `a(n) ≡ 2 (mod 3)` iff `n + 2` is a sum of two distinct powers of `3`. -/
theorem main :
    ∀ a : ℕ → ℤ,
      a 0 = 1 →
      a 1 = 1 →
      (∀ n : ℕ, 2 ≤ n →
        (a n : ℚ) = (4 * n : ℚ) * ((a (n - 1) : ℚ) +
          ∑ k ∈ Finset.Icc 2 (n - 1),
            ((4 * k ^ 2 - 1 : ℕ) : ℚ) / (4 * k : ℚ) * (a k : ℚ) * (a (n - k) : ℚ))) →
      (∀ n : ℕ,
        ((a n : ZMod 3) = 1 ↔ (∃ m : ℕ, n + 2 = 3 ^ m) ∨ (∃ m : ℕ, n + 2 = 2 * 3 ^ m))) ∧
      (∀ n : ℕ,
        ((a n : ZMod 3) = 2 ↔ ∃ j k : ℕ, j < k ∧ n + 2 = 3 ^ j + 3 ^ k)) := by
  sorry

end OMA.S_oeis_a397245
