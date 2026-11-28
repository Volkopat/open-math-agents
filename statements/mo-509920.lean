import Mathlib

/-!
# Partition of Fibonacci decompositions according to Zeckendorf blocks

Source: https://mathoverflow.net/questions/509920
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

With `F₁ = 1, F₂ = 2, …`, every `n ≥ 1` has a Zeckendorf representation
`n = F_{k₁} + ⋯ + F_{k_s}` (non-consecutive indices). A Fibonacci decomposition of `n` is a finite
set `S` of distinct Fibonacci numbers with sum `n`. Conjecture (Brindel, 2026): every Fibonacci
decomposition `S` of `n` can be partitioned as `S = S₁ ⊔ ⋯ ⊔ S_s` with `∑ Sᵢ = F_{kᵢ}`.

Conventions:
* The Fibonacci numbers `1, 2, 3, 5, …` are Mathlib's `Nat.fib k` for `k ≥ 2`, and the
  Zeckendorf representation is Mathlib's `Nat.zeckendorf n` (a list of indices `≥ 2`, pairwise
  non-consecutive, with `∑ fib = n`). The partition is a map assigning each element of `S` a
  position in that list; parts are automatically nonempty since Fibonacci numbers are positive.
-/

namespace OMA.S_mo_509920

/-- Every Fibonacci decomposition refines the Zeckendorf representation. -/
theorem main : ∀ (n : ℕ) (S : Finset ℕ), (∀ x ∈ S, ∃ k, 2 ≤ k ∧ x = Nat.fib k) →
    ∑ x ∈ S, x = n →
    ∃ g : ℕ → Fin (Nat.zeckendorf n).length, ∀ i : Fin (Nat.zeckendorf n).length,
      ∑ x ∈ S.filter (fun x => g x = i), x = Nat.fib ((Nat.zeckendorf n).get i) := by
  sorry

end OMA.S_mo_509920
