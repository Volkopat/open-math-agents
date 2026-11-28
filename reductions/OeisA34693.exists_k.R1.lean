import FormalConjectures.OEIS.«34693»

-- Reduction OeisA34693.exists_k.R1
-- Credit: @sanjog-p

/-!
# A kernel-checked initial range, and the open rest

The conjecture asks, for every `n > 1`, for some `k < n` with `n * k + 1` prime, that is, a prime
`p ≡ 1 (mod n)` below `n ^ 2`. This is far stronger than every unconditional bound on the least
prime in an arithmetic progression (Linnik's theorem only gives `p ≪ n ^ L`, with `L = 5` by Xylouris).

* `H1`: the statement for `1 < n ≤ 2000`. A finite check: each `n` has a small `k`, and the prime
  `n * k + 1` is certified by trial division inside the Lean kernel.
* `H2`: the statement for every `n > 2000`. This is the open conjecture.
-/

namespace OMA.R_OeisA34693_exists_k_R1

/-- The verified range. -/
def H1 : Prop := ∀ n : ℕ, 1 < n → n ≤ 2000 → ∃ k < n, (n * k + 1).Prime

/-- The open part. -/
def H2 : Prop := ∀ n : ℕ, 2000 < n → ∃ k < n, (n * k + 1).Prime

theorem main : H1 → H2 → type_of% @OeisA34693.exists_k := by
  intro h1 h2 n hn
  by_cases h : n ≤ 2000
  · exact h1 n hn h
  · exact h2 n (by omega)

end OMA.R_OeisA34693_exists_k_R1
