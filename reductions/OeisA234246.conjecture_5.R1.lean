import FormalConjectures.OEIS.«234246»

-- Reduction OeisA234246.conjecture_5.R1 of A234246 — conjecture 5
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# OeisA234246.conjecture_5: a kernel-checkable initial range, and the open rest

* `H1`: every `n > 7`, `n ∉ {10, 20}`, has `0 < k < n` with `φ(k) φ(n - k) + 1` a square, for `n ≤ 407`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 407`. This is the open conjecture.
-/

namespace OMA.R_OeisA234246_conjecture_5_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 7 < n → n ≠ 10 → n ≠ 20 → n ≤ 407 →
    ∃ k, 0 < k ∧ k < n ∧ IsSquare (k.totient * (n - k).totient + 1)

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 7 < n → n ≠ 10 → n ≠ 20 → 407 < n →
    ∃ k, 0 < k ∧ k < n ∧ IsSquare (k.totient * (n - k).totient + 1)

theorem main : H1 → H2 → type_of% @OeisA234246.conjecture_5 := by
  intro h1 h2 n hn hne10 hne20
  by_cases h : n ≤ 407
  · exact h1 n hn hne10 hne20 h
  · exact h2 n hn hne10 hne20 (by omega)

end OMA.R_OeisA234246_conjecture_5_R1
