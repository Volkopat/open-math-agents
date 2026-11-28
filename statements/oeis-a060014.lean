import Mathlib

/-!
# A060014: Sum of orders of all permutations of n letters

Source: https://oeis.org/A060014
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Isaac Saffold, OEIS, 2019): the sequence eventually becomes cyclic modulo `m` for all
`m`.

## Encoding

* `a n = ∑_{σ ∈ S_n} ord(σ)` with `S_n = Equiv.Perm (Fin n)` and `ord = orderOf`.
* "Eventually cyclic modulo `m`" (for each positive integer `m`): there are `N` and a period
  `p ≥ 1` with `a(n + p) ≡ a(n) (mod m)` for all `n ≥ N`.
-/

namespace OMA.S_oeis_a060014

/-- `a n`: the sum of the orders of all permutations of `n` letters. -/
noncomputable def a (n : ℕ) : ℕ := ∑ σ : Equiv.Perm (Fin n), orderOf σ

theorem main :
    ∀ m : ℕ, 0 < m → ∃ N p : ℕ, 0 < p ∧ ∀ n : ℕ, N ≤ n → a (n + p) ≡ a n [MOD m] := by
  sorry

end OMA.S_oeis_a060014
