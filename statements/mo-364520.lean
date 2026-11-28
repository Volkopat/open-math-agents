import Mathlib

/-!
# Number of smallest circuits in a matroid of odd girth

Source: https://mathoverflow.net/questions/364520
Asked by MathOverflow user Antoine Labelle.

For a simple graph of odd girth `g` with `n` vertices and `m` edges, the number of cycles of
length `g` is at most `n (m - n + 1) / g`. The asker rewrites this in matroid terms (for a
connected graph, `n` is the rank of the cycle matroid plus one) and asks: is it true that for any
matroid of size `m`, rank `r` and odd girth `g`, the number of circuits of size `g` is at most
`(r + 1) (m - r) / g`?

Translation choices.
* `M` is a Mathlib `Matroid α` with finite ground set `M.E`; its size is `m = M.E.ncard`.
* The rank `r` is given as the size of some base of `M` (all bases of a finite matroid have the
  same size).
* The girth `g` is the least size of a circuit: some circuit has `g` elements and every circuit
  has at least `g` elements; `g` is assumed odd.
* The bound `#circuits ≤ (r + 1) (m - r) / g` is stated without division as
  `#circuits * g ≤ (r + 1) * (m - r)`; since `r ≤ m`, the natural-number subtraction is exact.
* `main` is the affirmative answer to the question. No simplicity assumption is added, as the
  question says any matroid (a counterexample that is simple would refute the simple version too).
-/

namespace OMA.S_mo_364520

theorem main :
    ∀ (α : Type) (M : Matroid α) (r g : ℕ), M.E.Finite →
      (∃ B, M.IsBase B ∧ B.ncard = r) → Odd g →
      (∃ C, M.IsCircuit C ∧ C.ncard = g) → (∀ C, M.IsCircuit C → g ≤ C.ncard) →
      {C | M.IsCircuit C ∧ C.ncard = g}.ncard * g ≤ (r + 1) * (M.E.ncard - r) := by
  sorry

end OMA.S_mo_364520
