import Mathlib

/-!
# OEIS A204983

A204983: `a(n) = 2^(k - 1) - 2^(j - 1)`, where `(2^(k - 1), 2^(j - 1))` is the
least pair of distinct positive powers of `2` for which `n` divides
`2^(k - 1) - 2^(j - 1)`.

Conjecture from Andrew T. Porter (Dec 20 2022):
- `a(n) = 2^A007814(n) * (2^A007733(n) - 1)` for all `n ≥ 1`,
  where `A007814(n) = padicValNat 2 n` is the 2-adic valuation of `n`, and
  `A007733(n)` is the period of the binary expansion of `1 / n` (the least
  positive integer `d ≥ 1` such that the odd part of `n` divides `2^d - 1`).

Note: OEIS A204983 has offset 1 and data
`1, 2, 3, 4, 15, 6, 7, 8, 63, 30, 1023, 12, 4095, 14, 15, 16, 255, ...`.
The positive powers of `2` are `2^0, 2^1, 2^2, ...`, so `a(n)` is the least
positive integer of the form `2^b - 2^a` (with `a < b`) divisible by `n`.

Reference: https://oeis.org/A204983
-/

namespace OMA.S_oeis_a204983

/-- The odd part of `n`: `n / 2^(padicValNat 2 n)`. -/
def oddPart (n : ℕ) : ℕ :=
  n / 2 ^ padicValNat 2 n

/-- OEIS A007733: the period of the binary expansion of `1 / n`, defined as the
least positive integer `d ≥ 1` such that `oddPart n ∣ 2^d - 1` (and `0` at `n = 0`). -/
noncomputable def a007733 (n : ℕ) : ℕ :=
  sInf {d : ℕ | 0 < d ∧ oddPart n ∣ 2 ^ d - 1}

/-- OEIS A204983: the least positive integer of the form `2^b - 2^a` (`a < b`)
divisible by `n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {x : ℕ | ∃ a b : ℕ, a < b ∧ x = 2 ^ b - 2 ^ a ∧ n ∣ x}

/-- Andrew T. Porter's conjecture for OEIS A204983:
`a(n) = 2^(padicValNat 2 n) * (2^(a007733 n) - 1)` for all `n ≥ 1`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → a n = 2 ^ padicValNat 2 n * (2 ^ a007733 n - 1) := by
  sorry

end OMA.S_oeis_a204983
