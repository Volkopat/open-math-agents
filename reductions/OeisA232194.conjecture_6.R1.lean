import FormalConjectures.OEIS.«232194»

-- Reduction OeisA232194.conjecture_6.R1 of Ways to write $n = x + y$ with $nx + y$ and $ny - x$ both prime — conjecture 6
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Conjecture 6 of A232194: a kernel-checkable initial range, and the open rest

* `H1`: for `5 < n ≤ 1000` there are a prime `p` and `q > 0` with `p + q = n` and `n * q ^ 2 + 1`
  prime. A finite statement, checkable inside the Lean kernel by a verified trial-division search.
* `H2`: the same for every `n > 1000`. This is the open conjecture.
-/

namespace OMA.R_OeisA232194_conjecture_6_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, n > 5 → n ≤ 1000 →
    ∃ p q : ℕ, 0 < q ∧ p + q = n ∧ p.Prime ∧ (n * q ^ 2 + 1).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 1000 < n →
    ∃ p q : ℕ, 0 < q ∧ p + q = n ∧ p.Prime ∧ (n * q ^ 2 + 1).Prime

theorem main : H1 → H2 → type_of% @OeisA232194.conjecture_6 := by
  intro h1 h2 n hn
  by_cases h : n ≤ 1000
  · exact h1 n hn h
  · exact h2 n (by omega)

end OMA.R_OeisA232194_conjecture_6_R1
