import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Int.ModEq

/-!
# A341724: Triangle read by rows — coefficients of P_2(n, k) in Ledin's Fibonacci power sums

Source: https://oeis.org/A341724

`T(n, k)` is the coefficient of `x^k` in the polynomial `P_2(x)` of Ledin's Fibonacci sum
`∑_{j=0}^N j^n F_j = P_1(N) F_N + P_2(N) F_{N+1} + C`.
By Mélika Tebni (Sep 04 2023), `T(n, k) = (-1)^(n - k) * C(n, k) * A000557(n - k)`,
where `A000557` has e.g.f. `1 / (1 - 2 * sinh(x))` and satisfies
`A000557(0) = 1` and `A000557(n) = 2 * ∑_{j odd, 1 ≤ j ≤ n} C(n, j) * A000557(n - j)` for `n ≥ 1`.

Mélika Tebni (Sep 04 2023) conjectured in OEIS A341724:
1. For `0 < k < p` and `p` prime, `T(p, k) ≡ 0 (mod p)`.
2. For `0 ≤ k < 2^m` (`m : ℕ`), `T(2^m, k) ≡ 0 (mod 2^m)`.
-/

namespace OMA.S_oeis_a341724

/-- `M n` is OEIS A000557: `M 0 = 1`, and for `n ≥ 1`,
`M n = 2 * ∑_{j odd, 1 ≤ j ≤ n} C(n, j) * M (n - j)`. -/
def M : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
    2 * ∑ j ∈ ((Finset.range (n + 2)).filter Odd).attach,
      (n + 1).choose j.1 * M (n + 1 - j.1)
termination_by n => n
decreasing_by
  have hj : Odd j.1 := (Finset.mem_filter.mp j.2).2
  have hjpos : 1 ≤ j.1 := by obtain ⟨t, ht⟩ := hj; omega
  omega

/-- `T n k` is the `(n, k)`-th entry of OEIS A341724:
`T(n, k) = (-1)^(n - k) * C(n, k) * A000557(n - k)`. -/
def T (n k : ℕ) : ℤ :=
  (-1 : ℤ) ^ (n - k) * ((n.choose k : ℤ) * (M (n - k) : ℤ))

/-- Mélika Tebni's conjectures for OEIS A341724:
1. For every prime `p` and `0 < k < p`, `T(p, k) ≡ 0 (mod p)`.
2. For every `m : ℕ` and `0 ≤ k < 2^m`, `T(2^m, k) ≡ 0 (mod 2^m)`. -/
theorem main :
    (∀ p k : ℕ, p.Prime → 0 < k → k < p → (p : ℤ) ∣ T p k) ∧
    (∀ m k : ℕ, k < 2 ^ m → ((2 ^ m : ℕ) : ℤ) ∣ T (2 ^ m) k) := by
  sorry

end OMA.S_oeis_a341724
