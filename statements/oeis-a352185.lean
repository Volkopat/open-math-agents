import Mathlib

/-!
# OEIS A352185: minimal steps for composite arithmetic progressions

Source: https://oeis.org/A352185

Victor Pambuccian asked whether every term of this sequence is prime. The
index starts at 1. For index `n`, the sequence takes the least step `m`
with a coprime shift `k`, strictly between 0 and `m`, such that the first
`n` terms `i * m + k` for `i = 1, …, n` are composite.

The source records Michael S. Branicky's counterexample `a(135) = 8207`.
Here `main` states the original primality claim for refutation.
-/

namespace OMA.S_oeis_a352185

/-- Steps admitting a progression of `n` composite terms as in the entry. -/
def Admissible (n m : ℕ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ k < m ∧ Nat.Coprime k m ∧
    ∀ i : ℕ, 1 ≤ i → i ≤ n → ¬ Nat.Prime (i * m + k)

/-- The least admissible step for each positive length is prime. -/
theorem main : ∀ n : ℕ, 0 < n → ∀ m : ℕ,
    IsLeast {m | Admissible n m} m → Nat.Prime m := by
  sorry

end OMA.S_oeis_a352185
