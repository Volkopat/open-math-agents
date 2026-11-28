import Mathlib

/-!
# Integrality of (1^k + ... + n^k)(1/1^k + ... + 1/n^k) for k = 2 and k = 3

Source: https://mathoverflow.net/questions/434166
Asked by MathOverflow user gigi.

For a positive integer `n` let
`F_k(n) = (1^k + 2^k + ... + n^k) * (1/1^k + 1/2^k + ... + 1/n^k)`.
The asker recalls that for `k = 1` the value `F_1(n)` is an integer only for `n = 3`
(besides the trivial `n = 1`), and asks for which `n` the number `F_k(n)` is an integer when
`k ≥ 2`, in general or for particular values of `k`, for example `k = 2`.

This file formalizes the answer for the two smallest cases `k = 2` and `k = 3`: for every
positive integer `n`, `F_k(n)` is an integer if and only if `n = 1`. The case of a general
exponent `k` is not formalized here.

Translation choices.
* `F k n` is the rational number `(∑_{j=1}^n j^k) * (∑_{j=1}^n 1/j^k)`.
* `F k n` is an integer means `F k n = m` for some `m : ℤ`.
-/

namespace OMA.S_mo_434166

/-- `F k n = (1^k + ... + n^k) * (1/1^k + ... + 1/n^k)` as a rational number. -/
def F (k n : ℕ) : ℚ :=
  (∑ j ∈ Finset.Icc 1 n, (j : ℚ) ^ k) * (∑ j ∈ Finset.Icc 1 n, 1 / (j : ℚ) ^ k)

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      ((∃ m : ℤ, F 2 n = m) ↔ n = 1) ∧ ((∃ m : ℤ, F 3 n = m) ↔ n = 1) := by
  sorry

end OMA.S_mo_434166
