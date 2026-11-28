import Mathlib

/-!
# A223925: a(2n + 1) = 2n - 1; a(2n) = 4^n

Source: https://oeis.org/A223925

Conjecture (OEIS A223925):
For every `n ≥ 1`, `4 ^ n` divides `A132049(2 * n)`, where `A132049(m)` is the
numerator of the reduced fraction `2 * m * E(m - 1) / E(m)` and `E(k)` denotes the
`k`-th Euler zigzag (up/down) number (OEIS A000111).

Conventions:
- Euler zigzag numbers `E(k)` (`A000111`): `1, 1, 1, 2, 5, 16, 61, 272, 1385, ...`,
  computed via the Entringer triangle `entringer n k` with `E(n) = entringer n n`.
- Since `2 * m * E(m - 1) > 0` and `E(m) > 0`, the reduced numerator is
  `(2 * m * E(m - 1)) / Nat.gcd (2 * m * E(m - 1)) (E(m))`.
-/

namespace OMA.S_oeis_a223925

/-- Entringer triangle `T(n, k)` (OEIS A008281), whose diagonal `T(n, n)` gives the
Euler zigzag numbers `A000111(n)`. -/
def entringer : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => entringer (n + 1) k + entringer n (n - k)

/-- The `n`-th Euler zigzag (up/down) number (OEIS A000111). -/
def eulerZigzag (n : ℕ) : ℕ :=
  entringer n n

/-- Numerator of the reduced fraction `2 * m * E(m - 1) / E(m)` (OEIS A132049). -/
def a132049 (m : ℕ) : ℕ :=
  let num := 2 * m * eulerZigzag (m - 1)
  let den := eulerZigzag m
  num / Nat.gcd num den

/-- Conjecture: `4 ^ n` divides `A132049(2 * n)` for every `n ≥ 1`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → 4 ^ n ∣ a132049 (2 * n) := by
  sorry

end OMA.S_oeis_a223925
