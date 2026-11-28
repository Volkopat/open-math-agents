import OMAStatements.S_oeis_a220554

-- Reduction oeis-a220554.R1 of A220554: Number of ways to write 2n = p+q (q>0) with p, 2p+1 and (p-1)^2+q^2 all prime
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a220554: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 638`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 638`. This is the open conjecture.
-/

namespace OMA.R_oeis_a220554_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → n ≤ 638 →
    ∃ p q : ℕ, 0 < q ∧ p + q = 2 * n ∧
    p.Prime ∧ (2 * p + 1).Prime ∧ ((p - 1) ^ 2 + q ^ 2).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → 638 < n →
    ∃ p q : ℕ, 0 < q ∧ p + q = 2 * n ∧
    p.Prime ∧ (2 * p + 1).Prime ∧ ((p - 1) ^ 2 + q ^ 2).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a220554.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 638
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a220554_R1
