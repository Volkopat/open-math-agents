import FormalConjectures.OEIS.«236998»

-- Reduction OeisA236998.conjecture_3.R1 of A236998 — conjecture 3
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# OeisA236998.conjecture_3: a kernel-checkable initial range, and the open rest

* `H1`: every `n > 1` outside `{4, 7, 60, 199, 267}` has `0 < k < n` with `k φ(n - k)` a square, for `n ≤ 401`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 401`. This is the open conjecture.
-/

namespace OMA.R_OeisA236998_conjecture_3_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → n ≠ 4 → n ≠ 7 → n ≠ 60 → n ≠ 199 → n ≠ 267 → n ≤ 401 →
    ∃ k : ℕ, 0 < k ∧ k < n ∧ IsSquare (k * (n - k).totient)

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → n ≠ 4 → n ≠ 7 → n ≠ 60 → n ≠ 199 → n ≠ 267 → 401 < n →
    ∃ k : ℕ, 0 < k ∧ k < n ∧ IsSquare (k * (n - k).totient)

theorem main : H1 → H2 → type_of% @OeisA236998.conjecture_3 := by
  intro h1 h2 n hn h4 h7 h60 h199 h267
  by_cases h : n ≤ 401
  · exact h1 n hn h4 h7 h60 h199 h267 h
  · exact h2 n hn h4 h7 h60 h199 h267 (by omega)

end OMA.R_OeisA236998_conjecture_3_R1
