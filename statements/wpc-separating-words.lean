import Mathlib

/-!
# Separating words problem

Source: https://en.wikipedia.org/wiki/Separating_words_problem
Credit: @mgv27

What is the smallest number of states of a deterministic finite automaton that accepts one of
two given distinct words of length n and rejects the other? The best upper bound is Õ(n^{1/3})
(Chase, 2021) and the best lower bound is Ω(log n); is the answer O(log n)?

Formalization notes:
* Words are over the binary alphabet `Bool` (the standard setting; any fixed finite alphabet
  reduces to it up to constant factors).
* A DFA with `k` states is a `DFA Bool (Fin k)`; `sep u v` is the least such `k` for which the
  DFA accepts exactly one of `u, v` (such a `k` always exists for `u ≠ v`).
* `main` asserts the affirmative answer: `sep u v ≤ C · log n` for all distinct `u, v` of the
  same length `n ≥ 2`.
-/

namespace OMA.S_wpc_separating_words

/-- The least number of states of a DFA over `Bool` accepting exactly one of `u` and `v`. -/
noncomputable def sep (u v : List Bool) : ℕ :=
  sInf {k : ℕ | ∃ M : DFA Bool (Fin k), (u ∈ M.accepts ↔ v ∉ M.accepts)}

/-- Separating words: distinct words of length `n` can be separated with `O(log n)` states. -/
theorem main : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ u v : List Bool, u.length = n → v.length = n →
    u ≠ v → (sep u v : ℝ) ≤ C * Real.log n := by
  sorry

end OMA.S_wpc_separating_words
