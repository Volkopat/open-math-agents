import Mathlib

/-!
# OEIS A224899

Expansion of e.g.f. `Sum_{m >= 0} sinh(m * x)^m`:
`a(n) = Sum_{m = 0..n} m^n * m! * partOdd(n, m)`,
where `partOdd(n, m)` is the number of partitions of an `n`-set into `m` blocks of odd size
(so `m! * partOdd(n, m) = n! * [x^n] sinh(x)^m`).

Conjecture (Peter Bala, May 29 2022):
For every odd prime `p`, the sequence `a(n) (mod p)` for `n >= 1` is purely periodic with
period dividing `p - 1` (i.e. `a(n + (p - 1)) ≡ a(n) [MOD p]` for all `n >= 1`).
-/

namespace OMA.S_oeis_a224899

/-- Number of partitions of an `n`-element set into `m` blocks of odd size. -/
def partOdd : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | _ + 1, 0 => 0
  | 0, _ + 1 => 0
  | n + 1, m + 1 => ∑ j ∈ Finset.range (n / 2 + 1), Nat.choose n (2 * j) * partOdd (n - 2 * j) m
termination_by n _ => n
decreasing_by omega

/-- Sequence A224899: `a(n) = Sum_{m = 0..n} m^n * m! * partOdd(n, m)`. -/
def a (n : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (n + 1), m ^ n * m.factorial * partOdd n m

theorem main :
    ∀ p n : ℕ, p.Prime → p ≠ 2 → 1 ≤ n → a (n + (p - 1)) ≡ a n [MOD p] := by
  sorry

end OMA.S_oeis_a224899
