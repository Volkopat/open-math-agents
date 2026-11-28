import Mathlib

/-!
# A269737: Indices where A092243 strictly changes sign

Source: https://oeis.org/A269737

Conjecture (OEIS A269737):
Let `A092243(n) = ∑_{i=1}^n sgn((prime(i + 2) - prime(i + 1)) - (prime(i + 1) - prime(i)))`
be the running tug-of-war score between increases and decreases of consecutive prime gaps.
Then `A092243(n)` changes sign infinitely often (equivalently, it takes both strictly
positive and strictly negative values infinitely often).

Conventions:
- `gapStep i` computes `sgn((p_{i+2} - p_{i+1}) - (p_{i+1} - p_i))` for `0`-indexed primes
  `p_i = Nat.nth Nat.Prime i`.
- First terms of A092243 (`n ≥ 1`): `1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, ...`.
-/

namespace OMA.S_oeis_a269737

/-- Sign (`-1`, `0`, or `1`) of the change between consecutive prime gaps at `0`-based index `i`. -/
noncomputable def gapStep (i : ℕ) : ℤ :=
  let g1 : ℕ := Nat.nth Nat.Prime (i + 1) - Nat.nth Nat.Prime i
  let g2 : ℕ := Nat.nth Nat.Prime (i + 2) - Nat.nth Nat.Prime (i + 1)
  if g1 < g2 then 1 else if g2 < g1 then -1 else 0

/-- Running sum of signs of consecutive prime gap changes (OEIS A092243). -/
noncomputable def a092243 (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, gapStep i

/-- Conjecture: `A092243` changes sign infinitely often (attaining both positive and
negative values for infinitely many `n ≥ 1`). -/
theorem main :
    Set.Infinite {n : ℕ | 1 ≤ n ∧ 0 < a092243 n} ∧
    Set.Infinite {n : ℕ | 1 ≤ n ∧ a092243 n < 0} := by
  sorry

end OMA.S_oeis_a269737
