import Mathlib

/-!
# A001700: `binomial(2n+1, n+1)` as a hypergeometric value

Source: https://oeis.org/A001700
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (listed in A001700): `a(n) = 4^n · ₂F₁(1/2, -n; 2; 1)`, where
`a(n) = binomial(2n+1, n+1)`.

Conventions:
* `₂F₁(a, -n; c; 1)` terminates: it is `∑_{k=0}^{n} (a)_k (-n)_k / ((c)_k k!)` with rising
  factorials `(x)_k` (Mathlib's `ascPochhammer`).
* The entry lists several conjectures; this file states the first one, for every `n ≥ 0`.
-/

namespace OMA.S_oeis_a001700

/-- The terminating value `₂F₁(1/2, -n; 2; 1)`. -/
noncomputable def hyp (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    (ascPochhammer ℚ k).eval (1 / 2) * (ascPochhammer ℚ k).eval (-(n : ℚ)) /
      ((ascPochhammer ℚ k).eval 2 * (k.factorial : ℚ))

theorem main : ∀ n : ℕ, ((Nat.choose (2 * n + 1) (n + 1) : ℕ) : ℚ) = 4 ^ n * hyp n := by
  sorry

end OMA.S_oeis_a001700
