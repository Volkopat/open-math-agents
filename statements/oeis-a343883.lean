import Mathlib

/-!
# A343883: Numbers k such that A023896(k) is a multiple of A340179(k)

Source: https://oeis.org/A343883

Conjecture (OEIS A343883):
There are only 8 positive integers `k` such that `A023896(k)` (the sum of the totatives
of `k`) is a multiple of `A340179(k)` (the sum of `A023896(k) mod x` over all totatives
`x` of `k`), namely `3, 4, 6, 8, 10, 16, 30, 54`.

Conventions:
- Offset: `1`; known terms: `3, 4, 6, 8, 10, 16, 30, 54`.
- For `k = 1, 2`, `A023896(k) = 1` and `A340179(k) = 0`, so `A340179(k) ∣ A023896(k)`
  is false in `ℕ`.
- For `k = 16`, `A023896(16) = 64` and `A340179(16) = 32`, and `32 ∣ 64`.
-/

namespace OMA.S_oeis_a343883

/-- The finite set of positive integers `≤ n` coprime to `n` (the totatives of `n`). -/
def totatives (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (fun k => Nat.Coprime k n)

/-- Sum of the totatives of `n` (OEIS A023896). -/
def a023896 (n : ℕ) : ℕ :=
  ∑ x ∈ totatives n, x

/-- Sum of `A023896(n) mod x` over all totatives `x` of `n` (OEIS A340179). -/
def a340179 (n : ℕ) : ℕ :=
  ∑ x ∈ totatives n, a023896 n % x

/-- Conjecture: `{3, 4, 6, 8, 10, 16, 30, 54}` are the only positive integers `k` such
that `A340179(k)` divides `A023896(k)`. -/
theorem main :
    ∀ k : ℕ, 1 ≤ k →
      (a340179 k ∣ a023896 k) ↔ k ∈ ({3, 4, 6, 8, 10, 16, 30, 54} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a343883
