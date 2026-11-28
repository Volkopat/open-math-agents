import Mathlib

/-!
# OEIS A001358: second-order asymptotics of the semiprimes

Source: https://oeis.org/A001358
`a n` is the `n`-th semiprime (`a 1 = 4`). Conjecture (Rocchelli):
`a(n)/n ~ (log n / log log n) * (1 - M / log log n)` with `M` Mertens's constant.

Conventions. Since the first-order term alone already gives `a(n)/n ~ log n / log log n`, the
second-order term is read as an expansion with error `o(1 / log log n)`:
`(a n / n) / (log n / log log n) = 1 - M / log log n + o(1 / log log n)`.
`M` is characterised as the limit of `∑_{p ≤ x} 1/p - log log x`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a001358

open Filter Topology Asymptotics Real

/-- The `n`-th semiprime, indexed from `1` as in OEIS. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun m => m.primeFactorsList.length = 2) (n - 1)

theorem main :
    ∀ M : ℝ,
      Tendsto (fun x : ℕ => (∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 : ℝ) / p) -
        log (log x)) atTop (𝓝 M) →
      (fun n : ℕ => ((a n : ℝ) / n) / (log n / log (log n)) - (1 - M / log (log n)))
        =o[atTop] (fun n : ℕ => 1 / log (log (n : ℝ))) := by
  sorry

end OMA.S_oeis_a001358
