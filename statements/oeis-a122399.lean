import Mathlib

/-!
# OEIS A122399

`a(n) = Sum_{k = 0..n} k^n * k! * Stirling2(n, k)`.

Conjecture (Peter Bala):
For every prime `p`, the sequence `a(n) (mod p)` for `n >= 1` is purely periodic with
period dividing `p - 1` (i.e. `a(n + (p - 1)) ≡ a(n) [MOD p]` for all `n >= 1`).
-/

namespace OMA.S_oeis_a122399

/-- Stirling numbers of the second kind `S(n, j)`. -/
def stirling2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | _ + 1, 0 => 0
  | 0, _ + 1 => 0
  | n + 1, j + 1 => (j + 1) * stirling2 n (j + 1) + stirling2 n j

/-- Sequence A122399: `a(n) = Sum_{j = 0..n} j^n * j! * S(n, j)`. -/
def a (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1), j ^ n * j.factorial * stirling2 n j

theorem main :
    ∀ p n : ℕ, p.Prime → 1 ≤ n → a (n + (p - 1)) ≡ a n [MOD p] := by
  sorry

end OMA.S_oeis_a122399
