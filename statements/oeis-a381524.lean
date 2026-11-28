import Mathlib

/-!
# A381524: Smallest exponent of x of maximal absolute coefficient in Hermite polynomial H_n(x)

Source: https://oeis.org/A381524

Conjecture (OEIS A381524):
Let `a(n)` be the smallest exponent `k` (`0 ≤ k ≤ n`) of `x` attaining the maximum
absolute coefficient in the physicist's Hermite polynomial
`H_n(x) = ∑_{j=0}^{⌊n/2⌋} (-1)^j * (n! / (j! * (n - 2j)!)) * (2x)^(n - 2j)`.
Then consecutive differences `a(n + 1) - a(n)` are always `+1` or `-1`.

Conventions:
- Offset: `0`; first terms: `0, 1, 2, 1, 2, 3, 2, 3, 2, 3, 4, 3, 4, 3, 4, 5, 4, 5, ...`.
- `hermiteAbsCoeff n k` computes the exact absolute coefficient of `x ^ k` in `H_n(x)`
  in `ℕ` (namely `(n! / (((n - k) / 2)! * k!)) * 2 ^ k` when `k ≤ n` and `2 ∣ (n - k)`,
  and `0` otherwise).
-/

namespace OMA.S_oeis_a381524

/-- Absolute value of the coefficient of `x ^ k` in the physicist's Hermite polynomial `H_n(x)`. -/
def hermiteAbsCoeff (n k : ℕ) : ℕ :=
  if k ≤ n ∧ (n - k) % 2 = 0 then
    let j := (n - k) / 2
    (n.factorial / (j.factorial * k.factorial)) * 2 ^ k
  else
    0

/-- Predicate stating that `k` is the smallest exponent `≤ n` maximizing `hermiteAbsCoeff n`
(OEIS A381524). -/
def IsA381524 (n k : ℕ) : Prop :=
  IsLeast {e : ℕ | e ≤ n ∧ ∀ m ≤ n, hermiteAbsCoeff n m ≤ hermiteAbsCoeff n e} k

/-- Conjecture: consecutive terms of A381524 always differ by `±1`. -/
theorem main :
    ∀ n k₁ k₂ : ℕ, IsA381524 n k₁ → IsA381524 (n + 1) k₂ →
      k₂ = k₁ + 1 ∨ k₁ = k₂ + 1 := by
  sorry

end OMA.S_oeis_a381524
