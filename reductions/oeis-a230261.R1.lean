import OMAStatements.S_oeis_a230261

-- Reduction oeis-a230261.R1 of A230261: Number of ways to write 2*n - 1 = p + q with p, p + 6 and q^4 + 1 all prime, where q is a positive integer.
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a230261: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 73`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 73`. This is the open conjecture.
-/

namespace OMA.R_oeis_a230261_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 3 < n → n ≤ 73 →
    ∃ p q : ℕ, 0 < q ∧ p.Prime ∧ (p + 6).Prime ∧ (q ^ 4 + 1).Prime ∧
      p + q = 2 * n - 1

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 3 < n → 73 < n →
    ∃ p q : ℕ, 0 < q ∧ p.Prime ∧ (p + 6).Prime ∧ (q ^ 4 + 1).Prime ∧
      p + q = 2 * n - 1

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a230261.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 73
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a230261_R1
