import Mathlib

/-!
# Sarnak conjecture

Source: https://en.wikipedia.org/wiki/Sarnak_conjecture
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Sarnak's Möbius disjointness conjecture: let `(X, T)` be a topological dynamical system (a
compact metric space with a continuous self-map) of zero topological entropy. Then for every
continuous `f : X → ℂ` and every `x ∈ X`,
`(1/N) ∑_{n ≤ N} μ(n) f(Tⁿ x) → 0` as `N → ∞`.

## Encoding

* `X` is a compact metric space and `T : X → X` is continuous.
* Topological entropy is Mathlib's `Dynamics.coverEntropy T Set.univ` (Bowen–Dinaburg entropy
  via dynamical covers, which equals the topological entropy for compact metric spaces).
* `μ` is `ArithmeticFunction.moebius`; the sum runs over `1 ≤ n ≤ N` (`μ 0 = 0` in Mathlib, so
  summing over `range (N + 1)` is the same).
-/

namespace OMA.S_wp_sarnak_conjecture

open Filter Topology ArithmeticFunction

theorem main :
    ∀ (X : Type) [MetricSpace X] [CompactSpace X] (T : X → X), Continuous T →
      Dynamics.coverEntropy T Set.univ = 0 →
        ∀ (f : X → ℂ), Continuous f → ∀ x : X,
          Tendsto (fun N : ℕ => (1 / (N : ℂ)) *
              ∑ n ∈ Finset.range (N + 1), (moebius n : ℂ) * f (T^[n] x))
            atTop (𝓝 0) := by
  sorry

end OMA.S_wp_sarnak_conjecture
