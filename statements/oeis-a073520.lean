import Mathlib

/-!
# OEIS A073520: Smallest magic constant for an n x n magic square of consecutive primes

Source: https://oeis.org/A073520
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Let `a(n)` be the smallest magic constant of an `n × n` magic square whose entries
are `n^2` consecutive primes.

Conjecture: For every `n ≥ 5`, `a(n)` exists and equals the smallest integer `c` of
the same parity as `n` such that `n * c` is the sum of `n^2` consecutive primes.
-/

namespace OMA.S_oeis_a073520

noncomputable def nthPrime (k : ℕ) : ℕ :=
  Nat.nth Nat.Prime k

def IsConsecPrimeMagicSquare (n : ℕ) (M : Fin n → Fin n → ℕ) (c : ℕ) : Prop :=
  (∃ s : ℕ, Set.BijOn (fun p : Fin n × Fin n => M p.1 p.2) Set.univ
      (Set.image nthPrime (Set.Ico s (s + n ^ 2)))) ∧
  (∀ i : Fin n, ∑ j : Fin n, M i j = c) ∧
  (∀ j : Fin n, ∑ i : Fin n, M i j = c) ∧
  (∑ i : Fin n, M i i = c) ∧
  (∑ i : Fin n, M i ⟨n - 1 - i.val, by omega⟩ = c)

def HasConsecPrimeMagicConstant (n c : ℕ) : Prop :=
  ∃ M : Fin n → Fin n → ℕ, IsConsecPrimeMagicSquare n M c

def IsCandidateConstant (n c : ℕ) : Prop :=
  c % 2 = n % 2 ∧
  ∃ s : ℕ, ∑ k ∈ Finset.range (n ^ 2), nthPrime (s + k) = n * c

theorem main :
    ∀ n : ℕ, 5 ≤ n →
      ∃ c : ℕ,
        IsLeast { m : ℕ | HasConsecPrimeMagicConstant n m } c ∧
        IsLeast { m : ℕ | IsCandidateConstant n m } c := by
  sorry

end OMA.S_oeis_a073520
