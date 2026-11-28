import FormalConjectures.OEIS.«219023»

-- Reduction OeisA219023.conjecture_3.R1 of A219023 — conjecture 3
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# OeisA219023.conjecture_3: a kernel-checkable initial range, and the open rest

* `H1`: every `n > 1828` has a prime `p < n` with `n^2 - n - p` and `n^2 + n + p` prime, for `n ≤ 1934`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1934`. This is the open conjecture.
-/

namespace OMA.R_OeisA219023_conjecture_3_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 1828 < n → n ≤ 1934 →
    ∃ p : ℕ, p.Prime ∧ p < n ∧
      Nat.Prime (n ^ 2 - n - p) ∧ Nat.Prime (n ^ 2 + n + p)

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 1828 < n → 1934 < n →
    ∃ p : ℕ, p.Prime ∧ p < n ∧
      Nat.Prime (n ^ 2 - n - p) ∧ Nat.Prime (n ^ 2 + n + p)

theorem main : H1 → H2 → type_of% @OeisA219023.conjecture_3 := by
  intro h1 h2 n hn
  by_cases h : n ≤ 1934
  · exact h1 n hn h
  · exact h2 n hn (by omega)

end OMA.R_OeisA219023_conjecture_3_R1
