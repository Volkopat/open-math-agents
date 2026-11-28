import Mathlib

/-!
# A025529: a(n) = (1/1 + 1/2 + ... + 1/n) * lcm{1, 2, ..., n}

Source: https://oeis.org/A025529
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture (OEIS entry; a converse of Wolstenholme's theorem):
For `a(n) = (∑_{k=1}^n 1/k) * lcm(1, ..., n)`, if `n > 3` and `n^2 ∣ a(n - 1)`, then `n`
is prime.
-/

namespace OMA.S_oeis_a025529

/-- `a(n) = (∑_{k=1}^n 1/k) * lcm(1, ..., n)` as a natural number. -/
def a (n : ℕ) : ℕ :=
  let L := (Finset.Icc 1 n).lcm id
  ∑ k ∈ Finset.Icc 1 n, L / k

theorem main :
    ∀ n : ℕ, 3 < n → n ^ 2 ∣ a (n - 1) → Nat.Prime n := by
  sorry

end OMA.S_oeis_a025529
