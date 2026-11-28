import Mathlib

namespace OMA.S_oeis_a304314

open PowerSeries BigOperators

/-- A deterministic finite automaton with `k` inputs on state set `Fin n` is a transition function
`δ : Fin n → Fin k → Fin n`. It is strongly connected if every state is reachable from every other. -/
def IsStronglyConnected {k n : ℕ} (δ : Fin n → Fin k → Fin n) : Prop :=
  ∀ u v : Fin n, Relation.ReflTransGen (fun a b => ∃ i : Fin k, δ a i = b) u v

/-- Number of labeled strongly connected `n`-state finite automata with `k` inputs. -/
noncomputable def numLabeledSC (k n : ℕ) : ℕ :=
  by classical exact Fintype.card { δ : Fin n → Fin k → Fin n // IsStronglyConnected δ }

/-- Conjecture on OEIS A304314 (Paul D. Hanna):
If `F, invF ∈ ℚ[[X]]` satisfy `F * invF = 1`, `F(0) = 1`, and `[x^n] exp(n^4 * x) / F(x) = 0`
for all `n ≥ 1`, then for every `n ≥ 1`, `[x^(n - 1)] (F'(x) / F(x))` equals the number of
strongly connected `n`-state finite automata with 4 inputs (4-input strongly connected finite automata), i.e.
`numLabeledSC 4 n / (n - 1)!`. -/
theorem main :
    ∀ F invF : PowerSeries ℚ,
      F * invF = 1 →
      PowerSeries.coeff 0 F = 1 →
      (∀ n : ℕ, 1 ≤ n →
        PowerSeries.coeff n (PowerSeries.rescale ((n ^ 4 : ℕ) : ℚ) (PowerSeries.exp ℚ) * invF) = 0) →
      ∀ n : ℕ, 1 ≤ n →
        PowerSeries.coeff (n - 1) (PowerSeries.derivative ℚ F * invF) =
          (numLabeledSC 4 n : ℚ) / ((Nat.factorial (n - 1) : ℕ) : ℚ) := by
  sorry

end OMA.S_oeis_a304314
