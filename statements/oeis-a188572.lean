import Mathlib

/-!
# A188572: Coefficient of sqrt(3) in (1 + sqrt(2) + sqrt(3))^n

Source: https://oeis.org/A188572

Conjecture (Clark Kimberling, Oct 23 2024):
Every prime `p` divides `a(n)` for infinitely many `n`.

Conventions:
- Offset: `0`, with `a 0 = 0`, `a 1 = 1`, `a 2 = 2`, `a 3 = 12`, `a 4 = 40`, ...
- We represent elements of `ℤ[√2, √3]` computably in the basis `(1, √2, √3, √6)` as tuples
  `(c1, c2, c3, c6) : ℤ × ℤ × ℤ × ℤ`.
-/

namespace OMA.S_oeis_a188572

/-- Multiplication by `1 + √2 + √3` in the basis `(1, √2, √3, √6)` of `ℤ[√2, √3]`. -/
def quadStep (v : ℤ × ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ × ℤ :=
  let (c1, c2, c3, c6) := v
  (c1 + 2 * c2 + 3 * c3, c1 + c2 + 3 * c6, c1 + c3 + 2 * c6, c2 + c3 + c6)

/-- Coordinates of `(1 + √2 + √3)^n` in the basis `(1, √2, √3, √6)`. -/
def quadPow : ℕ → ℤ × ℤ × ℤ × ℤ
  | 0 => (1, 0, 0, 0)
  | n + 1 => quadStep (quadPow n)

/-- The sequence A188572: coefficient of `√3` in `(1 + √2 + √3)^n`. -/
def a (n : ℕ) : ℤ := (quadPow n).2.2.1

/-- Conjecture (Clark Kimberling): every prime divides `a n` for infinitely many `n`. -/
theorem main :
    ∀ p : ℕ, Nat.Prime p → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ (p : ℤ) ∣ a n := by
  sorry

end OMA.S_oeis_a188572
