import Mathlib

/-!
# Four-square Conjecture

Source: https://mathoverflow.net/questions/334474 (Zhi-Wei Sun, CC BY-SA 4.0).

Conjecture (much stronger than Lagrange's four-square theorem). Each integer `n > 1` can be
written as `x² + y² + (2^a 3^b)² + (2^c 5^d)²` with `x, y, a, b, c, d` nonnegative integers.
(Verified by the asker for `2 ≤ n ≤ 5·10^8`, OEIS A308734. Example:
`11 = 0² + 1² + (2^0 3^1)² + (2^0 5^0)²`.)

Formalization notes:
* All variables range over `ℕ`.
* Checked numerically for `2 ≤ n ≤ 20000`.
-/

namespace OMA.S_mo_334474

/-- Every `n > 1` is `x² + y² + (2^a 3^b)² + (2^c 5^d)²` with nonnegative integers. -/
theorem main : ∀ n : ℕ, 1 < n →
    ∃ x y a b c d : ℕ, n = x ^ 2 + y ^ 2 + (2 ^ a * 3 ^ b) ^ 2 + (2 ^ c * 5 ^ d) ^ 2 := by
  sorry

end OMA.S_mo_334474
