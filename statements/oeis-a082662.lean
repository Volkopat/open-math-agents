import Mathlib

/-!
# A082662: (P1) ⇔ (P7), odd part against the divisor sum of the even part

Source: https://oeis.org/A082662
Credit: @landvaluetaxfan

OEIS A082662 records that eight definitions of the sequence coincide, (P1)–(P8). Two of them are

* (P1) the odd part of `k` is `< √(2k)`;
* (P7) the odd part of `k` is `≤` the sum of the divisors of the even part of `k`.

Every `k ≥ 1` is uniquely `2^m * s` with `s` odd, in which case the odd part is `s` and the even
part is `2^m`. `main` states the arithmetic core of that equivalence: with `s` odd and positive,

  `s ^ 2 < 2 * (2 ^ m * s)`  (that is `s < √(2k)`, written without square roots)

if and only if

  `s ≤ ∑ d ∈ (2 ^ m).divisors, d`  (that is `s ≤ σ(2^m)`, the (P7) bound).

The two sides both reduce to `s < 2 ^ (m + 1)`, since `σ(2^m) = 2 ^ (m + 1) - 1`.
-/

namespace OMA.S_oeis_a082662

/-- The arithmetic core of (P1) ⇔ (P7) in A082662: for `k = 2 ^ m * s` with `s` odd and positive,
`s` is below `√(2k)` (stated as `s ^ 2 < 2 * (2 ^ m * s)`) exactly when `s` is at most the sum of
the divisors of the even part `2 ^ m` of `k`. -/
theorem main : ∀ (m s : ℕ), Odd s → 0 < s →
    (s ^ 2 < 2 * (2 ^ m * s) ↔ s ≤ ∑ d ∈ (2 ^ m).divisors, d) := by
  sorry

end OMA.S_oeis_a082662
