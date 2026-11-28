import Mathlib

/-!
# OEIS A033493: Sum of Numbers in the 3x+1 Trajectory

Source: https://oeis.org/A033493
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

For a positive integer $n$, consider its Collatz ($3x+1$) trajectory under
$T(x) = x/2$ if $x$ is even and $T(x) = 3x + 1$ if $x$ is odd, terminating upon first
reaching $1$. Let $s(n)$ (OEIS A006577) be the number of steps to reach $1$, and let
$a(n)$ (OEIS A033493) be the sum of all terms in the trajectory from $n$ through $1$.

Conjecture: Among all positive integers $n \ge 1$ whose Collatz trajectory reaches $1$,
$a(n) = s(n)^2$ holds if and only if $n = 3$ (where $a(3) = 49 = 7^2$).
-/

namespace OMA.S_oeis_a033493

/-- One step of the Collatz map. -/
def collatz (x : ℕ) : ℕ :=
  if x % 2 = 0 then x / 2 else 3 * x + 1

/-- `ReachesOneIn n k` holds when `k` is the least number of steps for `n` to reach `1`. -/
def ReachesOneIn (n k : ℕ) : Prop :=
  collatz^[k] n = 1 ∧ ∀ j < k, collatz^[j] n ≠ 1

/-- Sum of the first `k + 1` terms `n, T(n), ..., T^k(n)` of the Collatz trajectory. -/
def trajSum (n k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k + 1), collatz^[j] n

theorem main :
    ∀ n k : ℕ, 1 ≤ n → ReachesOneIn n k → (trajSum n k = k ^ 2 ↔ n = 3) := by
  sorry

end OMA.S_oeis_a033493
