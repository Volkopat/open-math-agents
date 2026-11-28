import Mathlib

/-!
# Nonrepetitive nonhomogeneous partition regularity

Source: https://mathoverflow.net/questions/462095 (domotorp)
Credit: Sudharsan Rajendiran

Is it true that for every `k` and every `k`-colouring of the natural numbers there are naturals
`a_1, …, a_{2l}` for some `l ≥ 2` with `a_1 + a_3 = 2 a_2 + 2`, `a_2 + a_4 = 2 a_3 + 2`, …,
`a_{2l-2} + a_{2l} = 2 a_{2l-1} + 2`, such that `a_i` and `a_{l+i}` have the same colour for every
`i ≤ l`?

The accepted answer on the source page shows that the answer is no: the `12`-colouring
`n ↦ ⌊12 {n / √2}⌋` admits no such sequence. We state this negative answer.

Conventions:
- The natural numbers are `ℕ` and a `k`-colouring is a map `c : ℕ → Fin k`.
- The sequence `a_1, …, a_{2l}` is `a 0, …, a (2l - 1)` (values of `a` at other indices are
  irrelevant). The condition `a_j + a_{j+2} = 2 a_{j+1} + 2` for `1 ≤ j ≤ 2l - 2` becomes
  `a i + a (i + 2) = 2 a (i + 1) + 2` for `i + 2 < 2l`, and "`a_i`, `a_{l+i}` have the same colour
  for `1 ≤ i ≤ l`" becomes `c (a i) = c (a (i + l))` for `i < l`.
-/

namespace OMA.S_mo_462095
theorem main : ¬ ∀ k : ℕ, ∀ c : ℕ → Fin k, ∃ l : ℕ, 2 ≤ l ∧ ∃ a : ℕ → ℕ,
    (∀ i, i + 2 < 2 * l → a i + a (i + 2) = 2 * a (i + 1) + 2) ∧
    ∀ i < l, c (a i) = c (a (i + l)) := by
  sorry
end OMA.S_mo_462095
