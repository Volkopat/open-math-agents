import Mathlib

/-!
# OEIS A066488: Composite Numbers Dividing Jacobsthal(k - 1)

Source: https://oeis.org/A066488
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Let $J(n)$ be the $n$-th Jacobsthal number (OEIS A001045), defined by
$J(0) = 0$, $J(1) = 1$, $J(n + 2) = J(n + 1) + 2 J(n)$, and let $M(k) = 2^k - 1$.

Conjecture (OEIS entry, 2019):
A composite integer $k$ divides $J(k - 1)$ if and only if
$$2^{M(k - 1)} \equiv -1 \pmod{M(k)^2 + M(k) + 1}.$$
-/

namespace OMA.S_oeis_a066488

/-- The Jacobsthal sequence `J(0) = 0, J(1) = 1, J(n+2) = J(n+1) + 2*J(n)`. -/
def jacobsthal : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => jacobsthal (n + 1) + 2 * jacobsthal n

/-- Mersenne number `M(k) = 2^k - 1`. -/
def mersenne (k : ℕ) : ℕ :=
  2 ^ k - 1

theorem main :
    ∀ k : ℕ, 2 ≤ k → ¬ Nat.Prime k →
      (k ∣ jacobsthal (k - 1) ↔
        (mersenne k ^ 2 + mersenne k + 1) ∣ (2 ^ mersenne (k - 1) + 1)) := by
  sorry

end OMA.S_oeis_a066488
