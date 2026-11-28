import Mathlib

/-!
# OEIS A097933: an Euler-type product over primes with 3 a quadratic residue

Source: https://oeis.org/A097933
`a n` lists the primes `p` that divide `3^((p-1)/2) - 1` (11, 13, 23, 37, …). Conjecture
(Valianatos, 2021): with `r(n) = (a(n) - 1)/(a(n) + 1)` if `a(n) ≡ 1 (mod 4)` and
`r(n) = (a(n) + 1)/(a(n) - 1)` otherwise, `∏_{n ≥ 1} r(n) = 2/√3`.

Conventions. The product is the limit of its partial products in the natural order of the
primes. `a` is indexed from `1`; `p` ranges over primes with `p ∣ 3^((p-1)/2) - 1` (this
excludes `2` and `3`).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a097933

open Filter Topology Real

/-- `p` is a prime dividing `3^((p-1)/2) - 1`. -/
def P (p : ℕ) : Prop := p.Prime ∧ p ∣ 3 ^ ((p - 1) / 2) - 1

/-- The factor `r` attached to `p`. -/
noncomputable def r (p : ℕ) : ℝ :=
  if p % 4 = 1 then ((p : ℝ) - 1) / (p + 1) else ((p : ℝ) + 1) / (p - 1)

theorem main :
    Tendsto (fun N : ℕ => ∏ i ∈ Finset.range N, r (Nat.nth P i)) atTop (𝓝 (2 / √3)) := by
  sorry

end OMA.S_oeis_a097933
