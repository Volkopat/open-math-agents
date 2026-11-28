import Mathlib

/-!
# A091351: Triangle T, read by rows, such that T(n,k) equals the (n-k)-th row sum of T^k.

Source: https://oeis.org/A091351
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: given this triangle T as a triangular matrix, then we have the relation
[T^p](n+q-1,q-1) = [T^q](n+p-1,p-1) for n >= 0, p > 0, q > 0; that is, column q-1 of
matrix power T^p equals column p-1 of matrix power T^q, for all positive integers p and q.
-/

namespace OMA.S_oeis_a091351

def matPow (T : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, r, c => if r = c then 1 else 0
  | k + 1, r, c => ∑ j ∈ Finset.range (r + 1), matPow T k r j * T j c

def IsA091351 (T : ℕ → ℕ → ℕ) : Prop :=
  (∀ n k : ℕ, n < k → T n k = 0) ∧
  (∀ n k : ℕ, k ≤ n → T n k = ∑ j ∈ Finset.range (n - k + 1), matPow T k (n - k) j)

theorem main :
    ∀ T : ℕ → ℕ → ℕ, IsA091351 T →
      ∀ p q n : ℕ, 0 < p → 0 < q →
        matPow T p (n + q - 1) (q - 1) = matPow T q (n + p - 1) (p - 1) := by
  sorry

end OMA.S_oeis_a091351
