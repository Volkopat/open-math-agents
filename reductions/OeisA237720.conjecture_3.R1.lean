import FormalConjectures.OEIS.«237720»

-- Reduction OeisA237720.conjecture_3.R1 of A237720 — conjecture 3
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# OeisA237720.conjecture_3: a kernel-checkable initial range, and the open rest

* `H1`: every `n > 2` has a prime `p < n` with `⌊√(n + p)⌋` prime, for `n ≤ 1002`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1002`. This is the open conjecture.
-/

namespace OMA.R_OeisA237720_conjecture_3_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 2 < n → n ≤ 1002 →
    ∃ p : ℕ, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 2 < n → 1002 < n →
    ∃ p : ℕ, p.Prime ∧ p < n ∧ (Nat.sqrt (n + p)).Prime

theorem main : H1 → H2 → type_of% @OeisA237720.conjecture_3 := by
  intro h1 h2 n hn
  by_cases h : n ≤ 1002
  · exact h1 n hn h
  · exact h2 n hn (by omega)

end OMA.R_OeisA237720_conjecture_3_R1
