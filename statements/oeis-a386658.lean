import Mathlib

/-!
# OEIS A386658

Expansion of e.g.f. `Sum_{n >= 0} (5^n * x + LambertW(x))^n / n!`, with explicit formula
`a(n) = 5^(n^2) + Sum_{k = 0..n-1} binomial(n, k) * 5^(k * (k + 1)) * (5^k - (n - k))^(n - k - 1)`.
(First terms: `1, 6, 674, 2000229, 153566609748, 298500361403750381, ...`)

Conjecture:
For all `n >= 6`, `a(n) (mod 6)` equals `[4, 3, 0, 3, 0, 5]` repeating
(i.e., `a(n) % 6` is `4, 3, 0, 3, 0, 5` for `n % 6 = 0, 1, 2, 3, 4, 5` respectively).
-/

namespace OMA.S_oeis_a386658

/-- Sequence A386658:
`a(n) = 5^(n^2) + Sum_{k = 0..n-1} binomial(n, k) * 5^(k * (k + 1)) * (5^k - (n - k))^(n - k - 1)`. -/
def a (n : ℕ) : ℤ :=
  (5 : ℤ) ^ (n ^ 2) +
    ∑ k ∈ Finset.range n,
      (Nat.choose n k : ℤ) * (5 : ℤ) ^ (k * (k + 1)) *
        ((5 : ℤ) ^ k - ((n - k : ℕ) : ℤ)) ^ (n - k - 1)

/-- The conjectured repeating pattern `[4, 3, 0, 3, 0, 5]` for `n % 6 = 0, 1, 2, 3, 4, 5`. -/
def targetMod6 (n : ℕ) : ℤ :=
  match n % 6 with
  | 0 => 4
  | 1 => 3
  | 2 => 0
  | 3 => 3
  | 4 => 0
  | _ => 5

theorem main :
    ∀ n : ℕ, 6 ≤ n → a n ≡ targetMod6 n [ZMOD 6] := by
  sorry

end OMA.S_oeis_a386658
