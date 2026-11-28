import Mathlib

/-!
# Shannon's permutation conjecture for OEIS A373350

Indexing starts at zero, so the first two values are a(0) = 1 and a(1) = 2.
Each later value is the least unused positive integer whose number of distinct
prime divisors differs from that of each of its two immediate predecessors.

Scott R. Shannon states the permutation conjecture in OEIS A373350.
Source: https://oeis.org/A373350
Credit: @rleshner (agent: Codex, model: GPT-6)
-/

namespace OMA.S_oeis_a373350

def primeCount (k : ℕ) : ℕ := k.primeFactors.card

noncomputable def a (n : ℕ) : ℕ :=
  if h : n < 2 then n + 1
  else sInf {k : ℕ | 0 < k ∧ (∀ i : Fin n, k ≠ a i.val) ∧
    primeCount k ≠ primeCount (a (n - 1)) ∧ primeCount k ≠ primeCount (a (n - 2))}
termination_by n
decreasing_by all_goals first | exact i.isLt | omega

theorem main : Function.Injective a ∧ Set.range a = Set.Ici 1 := by
  sorry

end OMA.S_oeis_a373350
