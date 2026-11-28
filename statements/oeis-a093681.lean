import Mathlib

/-!
# A093681: Sequence contains no 3-term arithmetic progression, starting with 1, 28.

Source: https://oeis.org/A093681
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

a(n) = (Sum_{k=1..n-1} (3^A007814(k) + 1)/2) + f(n), with f(n) a 16-periodic function
with values {1, 27, 26, 27, 23, 27, 26, 27, 14, 28, 28, 28, 28, 28, 28, 28, ...},
n >= 1 (conjectured and checked up to n=1000).
-/

namespace OMA.S_oeis_a093681

/-- Prefix list of length `n` of the lexicographically earliest strictly increasing
sequence starting with `1, 28` and containing no 3-term arithmetic progression. -/
noncomputable def prefixList : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | 2 => [1, 28]
  | n + 3 =>
    let prev := prefixList (n + 2)
    let last := prev.getLastD 0
    let nxt := sInf {m : ℕ | last < m ∧ ∀ x ∈ prev, ∀ y ∈ prev, x < y → 2 * y ≠ x + m}
    prev ++ [nxt]

/-- The `n`-th term of A093681 (1-indexed). -/
noncomputable def a (n : ℕ) : ℕ :=
  (prefixList n).getLastD 0

/-- The 16-periodic function `f(n)` (1-indexed). -/
def f (n : ℕ) : ℕ :=
  match (n - 1) % 16 with
  | 0 => 1
  | 1 => 27
  | 2 => 26
  | 3 => 27
  | 4 => 23
  | 5 => 27
  | 6 => 26
  | 7 => 27
  | 8 => 14
  | _ => 28

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      a n = (∑ k ∈ Finset.Icc 1 (n - 1), (3 ^ (k.factorization 2) + 1) / 2) + f n := by
  sorry

end OMA.S_oeis_a093681
