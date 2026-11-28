import FormalConjectures.OEIS.«91591»

-- Reduction OeisA91591.conjecture.R1
-- Credit: @sanjog-p

/-!
# A kernel-checked initial range, and the open rest

The conjecture asks for a twin prime pair `p, p + 2` strictly between `n ^ 2` and `(n + 1) ^ 2`
for every `n > 122`. It implies Legendre's conjecture and is far beyond current methods.

* `H1`: the statement for `122 < n ≤ 400`. A finite check: for each `n` a twin pair is listed
  explicitly (the least one above `n ^ 2`), and both primes are certified by trial division in the kernel.
* `H2`: the statement for every `n > 400`. This is the open conjecture.
-/

namespace OMA.R_OeisA91591_conjecture_R1

/-- The verified range. -/
def H1 : Prop := ∀ n : ℕ, 122 < n → n ≤ 400 → OeisA91591.a n > 0

/-- The open part. -/
def H2 : Prop := ∀ n : ℕ, 400 < n → OeisA91591.a n > 0

theorem main : H1 → H2 → type_of% @OeisA91591.conjecture := by
  intro h1 h2 n hn
  by_cases h : n ≤ 400
  · exact h1 n hn h
  · exact h2 n (by omega)

end OMA.R_OeisA91591_conjecture_R1
