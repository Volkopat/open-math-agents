import Mathlib

namespace OMA.S_oeis_a395546

/-- A 3-SAT clause in the multiset clause model on `n` variables: a multiset of 3 literals
chosen from `{x_1, ..., x_n, ¬x_1, ..., ¬x_n}` (repeated literals allowed). -/
abbrev Clause3 (n : ℕ) := Sym (Fin n × Bool) 3

/-- A 5-clause 3-SAT formula in the multiset clause model on `n` variables (repeated clauses
allowed). -/
abbrev Formula3SAT5 (n : ℕ) := Sym (Clause3 n) 5

/-- A 5-clause 3-SAT formula `F` is satisfiable if there is a truth assignment `α : Fin n → Bool`
that satisfies at least one literal in every clause of `F`. -/
def Satisfiable {n : ℕ} (F : Formula3SAT5 n) : Prop :=
  ∃ α : Fin n → Bool, ∀ c ∈ F, ∃ l ∈ c, α l.1 = l.2

/-- OEIS A395546: the number of satisfiable 3-SAT formulas with `n` variables and 5 clauses
in the multiset clause model. -/
noncomputable def a395546 (n : ℕ) : ℕ :=
  Nat.card { F : Formula3SAT5 n // Satisfiable F }

/-- Conjectured formula in OEIS A395546:
`a(n) = binomial(binomial(2*n+2, 3) + 4, 5) - (129332*n^6 - 2237100*n^5 + 16427761*n^4 - 63136975*n^3 + 130884126*n^2 - 135887564*n + 53820480) / 3`
(stated over `ℤ` cleared of the denominator `3`). -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      3 * (a395546 n : ℤ) =
        3 * ((((2 * n + 2).choose 3 + 4).choose 5 : ℕ) : ℤ) -
          (129332 * (n : ℤ) ^ 6 - 2237100 * (n : ℤ) ^ 5 + 16427761 * (n : ℤ) ^ 4 -
            63136975 * (n : ℤ) ^ 3 + 130884126 * (n : ℤ) ^ 2 -
            135887564 * (n : ℤ) + 53820480) := by sorry

end OMA.S_oeis_a395546
