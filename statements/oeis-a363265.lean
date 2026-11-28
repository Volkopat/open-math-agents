import Mathlib

/-!
# A363265: Number of integer factorizations of n with a unique mode

Source: https://oeis.org/A363265

Conjecture (OEIS A363265):
The value `9` never occurs in the sequence `a(n)` counting multiplicative factorizations
of `n` into integers `> 1` whose multiset of factors has a unique mode (a factor
appearing strictly more often than every other distinct factor).

Conventions:
- Offset: `1`; first terms: `0, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, ...`.
- For `n = 1`, the only factorization into factors `> 1` is the empty multiset, which
  has no mode, so `a(1) = 0`.
- For `n = 12`, the factorizations are `{12}`, `{2, 6}`, `{3, 4}`, `{2, 2, 3}`, of
  which `{12}` and `{2, 2, 3}` have a unique mode, giving `a(12) = 2`.
-/

namespace OMA.S_oeis_a363265

/-- Predicate stating that `f` is a multiplicative factorization of `n` into factors `> 1`
with a unique mode. -/
def IsUniqueModeFactorization (n : ℕ) (f : Multiset ℕ) : Prop :=
  (∀ x ∈ f, 1 < x) ∧ f.prod = n ∧
    ∃ m ∈ f, ∀ x ∈ f, x ≠ m → f.count x < f.count m

/-- Number of integer factorizations of `n` with a unique mode (OEIS A363265). -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {f : Multiset ℕ | IsUniqueModeFactorization n f}

/-- Conjecture: `9` does not occur in OEIS A363265. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → a n ≠ 9 := by
  sorry

end OMA.S_oeis_a363265
