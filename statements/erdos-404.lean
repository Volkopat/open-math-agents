import Mathlib

/-!
# Erdős Problem 404

Source: https://www.erdosproblems.com/404
Credit: @shc261392

The source: for which integers `a ≥ 1` and primes `p` is there a finite upper bound on those `k`
such that there are `a = a₁ < ⋯ < aₙ` with `p^k ∣ (a₁! + ⋯ + aₙ!)`? If `f(a, p)` is the greatest
such `k`, how does this function behave? Is there a prime `p` and an infinite sequence
`a₁ < a₂ < ⋯` such that if `p^{m_k}` is the highest power of `p` dividing `∑_{i ≤ k} aᵢ!` then
`m_k → ∞`?

The first two questions ask for a description ("for which", "how does it behave") that the source
does not conjecture. This file states the precise third question, in its affirmative form: a proof
of `main` answers it yes, a proof of `¬ main` answers it no.

Reading used here:
* The sequence is `a : ℕ → ℕ`, strictly increasing, of positive integers (as in the first
  question, `a ≥ 1`); it is indexed from `0`, so `∑_{i ≤ k} aᵢ!` is the sum over `i ∈ range (k+1)`.
* "`p^{m_k}` is the highest power of `p` dividing" the sum is `padicValNat p` of the sum (the sum
  is positive), and `m_k → ∞` is `Tendsto … atTop atTop`.
-/

namespace OMA.S_erdos_404

open Filter

theorem main :
    ∃ p : ℕ, p.Prime ∧ ∃ a : ℕ → ℕ, StrictMono a ∧ 1 ≤ a 0 ∧
      Tendsto (fun k : ℕ => padicValNat p (∑ i ∈ Finset.range (k + 1), (a i).factorial))
        atTop atTop := by
  sorry

end OMA.S_erdos_404
