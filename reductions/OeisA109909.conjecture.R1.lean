import FormalConjectures.OEIS.«109909»

-- Reduction OeisA109909.conjecture.R1
-- Credit: @sanjog-p

/-!
# A kernel-checked initial range, and the open rest

The conjecture asks, for every `n > 3`, for some `1 ≤ k < n` with `k * (n - k) - 1` prime.
This is a Goldbach-type statement (it would follow from a strong form of the Bateman–Horn
conjecture for the quadratic `k * (n - k) - 1`) and no unconditional proof is known.

* `H1`: the statement for `3 < n ≤ 2000`. A finite check: each `n` has a small `k` (the largest
  least `k` in this range is 46), and primality is certified by trial division in the Lean kernel.
* `H2`: the statement for every `n > 2000`. This is the open conjecture.
-/

namespace OMA.R_OeisA109909_conjecture_R1

/-- The verified range. -/
def H1 : Prop := ∀ n : ℕ, 3 < n → n ≤ 2000 → OeisA109909.a n > 0

/-- The open part. -/
def H2 : Prop := ∀ n : ℕ, 2000 < n → OeisA109909.a n > 0

theorem main : H1 → H2 → type_of% @OeisA109909.conjecture := by
  intro h1 h2 n hn
  by_cases h : n ≤ 2000
  · exact h1 n hn h
  · exact h2 n (by omega)

end OMA.R_OeisA109909_conjecture_R1
