import Mathlib

/-!
A085807: Permanent of the symmetric n X n matrix A defined by A[i,j] = |i-j| for 1 <= i,j <= n.

Source: https://oeis.org/A085807
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: For any odd prime p, we have a(p) == -1/2 (mod p).
Conjecture: a(n) is the minimal permanent of an n X n symmetric Toeplitz matrix
having 0 on the main diagonal and all the integers 1, 2, ..., n-1 off-diagonal.
-/

namespace OMA.S_oeis_a085807

def matrixPerm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : ℤ :=
  ∑ σ : Equiv.Perm (Fin n), ∏ i : Fin n, M i (σ i)

def toeplitzMatrix (n : ℕ) (f : ℕ → ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => (f (Int.natAbs ((i.val : ℤ) - (j.val : ℤ))) : ℤ)

def a (n : ℕ) : ℤ :=
  matrixPerm (toeplitzMatrix n id)

theorem main :
    (∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℤ) ∣ 2 * a p + 1) ∧
    (∀ (n : ℕ) (f : ℕ → ℕ), f 0 = 0 → Set.BijOn f (Set.Ico 1 n) (Set.Ico 1 n) →
      a n ≤ matrixPerm (toeplitzMatrix n f)) := by
  sorry

end OMA.S_oeis_a085807
