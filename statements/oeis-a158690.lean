import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient

/-!
# A158690: Expansion of the basic hypergeometric series 1 + ∑_{m ≥ 1} ∏_{k=1}^m (1 - exp(-(2k-1)t))

Source: https://oeis.org/A158690

`a(n)` is `n! * [t^n]` in the formal power series
`1 + (1 - exp(-t)) + (1 - exp(-t))(1 - exp(-3t)) + (1 - exp(-t))(1 - exp(-3t))(1 - exp(-5t)) + ...`.
Since `∏_{k=1}^m (1 - exp(-(2k-1)t))` has order `≥ m` in `t`, the series truncates at `m ≤ n`,
giving the exact finite integer formula:
`a(n) = ∑_{m=0}^n ∑_{S ⊆ {0, …, m - 1}} (-1)^|S| * (-∑_{i ∈ S} (2i + 1))^n`.

Peter Bala conjectured in OEIS A158690:
1. For every integer `k ≥ 1`, `a(n) mod k` is eventually periodic with period dividing `φ(k)`
   (i.e., `∃ N, ∀ n ≥ N, a (n + k.totient) ≡ a n [ZMOD k]`).
2. For every shift `i : ℕ`, every prime `p`, and all positive integers `n` and `k`,
   the Gauss congruence `a (n * p ^ k + i) ≡ a (n * p ^ (k - 1) + i) [ZMOD p ^ k]` holds.
-/

namespace OMA.S_oeis_a158690

/-- The `m`-th summand `w m n = n! * [t^n] ∏_{j=0}^{m-1} (1 - exp(-(2j + 1) t))`. -/
def w (m n : ℕ) : ℤ :=
  ∑ S ∈ (Finset.range m).powerset,
    (-1 : ℤ) ^ S.card * (-(∑ i ∈ S, (2 * (i : ℤ) + 1))) ^ n

/-- `a n` is the `n`-th term of OEIS A158690 (`1, 1, 5, 55, 1073, 32671, ...`). -/
def a (n : ℕ) : ℤ :=
  ∑ m ∈ Finset.range (n + 1), w m n

/-- Peter Bala's conjectures for OEIS A158690:
1. Eventual periodicity modulo any `k ≥ 1` with period dividing `φ(k)`.
2. Gauss congruences for every shift `i : ℕ`, prime `p`, and positive integers `n, k`. -/
theorem main :
    (∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a (n + k.totient) ≡ a n [ZMOD (k : ℤ)]) ∧
    (∀ i p n k : ℕ, p.Prime → 1 ≤ n → 1 ≤ k →
      a (n * p ^ k + i) ≡ a (n * p ^ (k - 1) + i) [ZMOD ((p ^ k : ℕ) : ℤ)]) := by
  sorry

end OMA.S_oeis_a158690
