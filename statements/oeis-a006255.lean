import Mathlib

/-!
# A006255: Conjecture on R. L. Graham's Sequence

Source: https://oeis.org/A006255
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

R. L. Graham's sequence `a(n)` is the smallest integer `m ≥ n` for which there exists a strictly
increasing sequence `n = b_1 < b_2 < ... < b_t = m` whose product `b_1 * b_2 * ... * b_t` is a
perfect square.

Let `b(n)` be the greatest prime factor of the squarefree part of `n` (with `b(n) = 1` if `n` is a
square).

Conjecture (OEIS entry, in its corrected form): If `b(n)^2 ≥ 2 * n`, then
`a(n) = n + b(n)` except for `n = 2, 3, 10, 171`.
-/

namespace OMA.S_oeis_a006255

/-- R. L. Graham's sequence `a(n)`. -/
noncomputable def grahamSeq (n : ℕ) : ℕ :=
  sInf { m : ℕ | ∃ s : Finset ℕ, n ∈ s ∧ m ∈ s ∧ (∀ x ∈ s, n ≤ x ∧ x ≤ m) ∧
    IsSquare (∏ x ∈ s, x) }

/-- The squarefree part of `n` (A007913). -/
noncomputable def squarefreePart (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, if Odd (n.factorization p) then p else 1

/-- Greatest prime factor of `m`, or `1` if `m ≤ 1` (A006530). -/
def greatestPrimeFactor (m : ℕ) : ℕ :=
  max 1 (m.primeFactors.sup id)

/-- `b(n) = A006530(A007913(n))`. -/
noncomputable def b (n : ℕ) : ℕ :=
  greatestPrimeFactor (squarefreePart n)

theorem main :
    ∀ n : ℕ, 0 < n → 2 * n ≤ (b n) ^ 2 → n ≠ 2 → n ≠ 3 → n ≠ 10 → n ≠ 171 →
      grahamSeq n = n + b n := by
  sorry

end OMA.S_oeis_a006255
