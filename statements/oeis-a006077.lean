import Mathlib

/-!
# A006077: (n+1)^2*a(n+1) = (9n^2+9n+3)*a(n) - 27*n^2*a(n-1), with a(0) = 1, a(1) = 3

Source: https://oeis.org/A006077
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjectures:
Let `W(n)` be the `(n+1) × (n+1)` Hankel determinant with `(i, j)`-entry `a(i + j)`
for `0 ≤ i, j ≤ n`.
1. If `n ≡ 1 (mod 3)`, then `W(n) = 0`.
2. If `n ≡ 0` or `2 (mod 3)`, then `W(n) * (-1)^(⌊(n+1)/3⌋) / 6^n` is a positive
   odd integer.
3. Let `p ≡ 1 (mod 3)` be a prime, and write `4p = x^2 + 27y^2` with integers `x, y`
   and `x ≡ 1 (mod 3)`. Then `W(p - 1) ≡ (-1)^((p+1)/2) * (x - p / x) (mod p^2)`,
   equivalently `x * W(p - 1) ≡ (-1)^((p+1)/2) * (x^2 - p) (mod p^2)` (since `gcd(x, p) = 1`).
-/

namespace OMA.S_oeis_a006077

/-- The sequence A006077 defined recursively over `ℚ`. -/
def a : ℕ → ℚ
  | 0 => 1
  | 1 => 3
  | n + 2 =>
      ((9 * (n + 1 : ℚ) ^ 2 + 9 * (n + 1 : ℚ) + 3) * a (n + 1) -
        27 * (n + 1 : ℚ) ^ 2 * a n) / ((n + 2 : ℚ) ^ 2)

/-- The `(n+1) × (n+1)` Hankel determinant `W(n) = det(a(i + j))_{0 ≤ i, j ≤ n}`. -/
def W (n : ℕ) : ℚ :=
  Matrix.det (fun (i j : Fin (n + 1)) => a (i.1 + j.1))

/-- Combined Hankel determinant conjectures for A006077. -/
theorem main :
    (∀ n : ℕ, n % 3 = 1 → W n = 0) ∧
    (∀ n : ℕ, (n % 3 = 0 ∨ n % 3 = 2) →
      ∃ k : ℕ, W n * (-1 : ℚ) ^ ((n + 1) / 3) / (6 : ℚ) ^ n = (2 * k + 1 : ℚ)) ∧
    (∀ (p : ℕ) (x y : ℤ), Nat.Prime p → p % 3 = 1 →
      4 * (p : ℤ) = x ^ 2 + 27 * y ^ 2 → x % 3 = 1 →
      ∃ m : ℤ, W (p - 1) = (m : ℚ) ∧
        x * m ≡ (-1 : ℤ) ^ ((p + 1) / 2) * (x ^ 2 - (p : ℤ)) [ZMOD ((p : ℤ) ^ 2)]) := by
  sorry

end OMA.S_oeis_a006077
