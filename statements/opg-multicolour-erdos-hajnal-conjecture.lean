import Mathlib

/-!
# Multicolour Erdős–Hajnal Conjecture

Source: https://www.openproblemgarden.org/op/multicolour_erdos_hajnal_conjecture
(see J. Fox, A. Grinshpun, J. Pach, *The Erdős–Hajnal conjecture for rainbow triangles*)
Credit: @ishaanzee

**Conjecture** (Erdős–Hajnal). For every fixed `k ≥ 2` and fixed colouring `χ` of `E(K_k)` with
`m` colours, there exists `ε > 0` such that every colouring of the edges of `K_n` contains either
`k` vertices whose edges are coloured according to `χ` or `n^ε` vertices whose edges are coloured
with at most `m - 1` colours.

Formalization:
* Colourings use the palette `Fin m`: `χ : Sym2 (Fin k) → Fin m` and `col : Sym2 (Fin n) → Fin m`
  (values on the diagonal are irrelevant). The colourings of `K_n` are `m`-colourings, as in the
  source (with an unbounded palette a rainbow `K_n` would make the statement false).
* We take `m ≥ 2`. (For `m = 1` the second alternative asks for `n^ε` vertices spanning no edge,
  which fails for `2 ≤ n < k`; the statement is meant for at least two colours.)
* `k` vertices coloured according to `χ`: an injective `f : Fin k → Fin n` with
  `col s(f a, f b) = χ s(a, b)` for all `a ≠ b`.
* `n^ε` vertices whose edges use at most `m - 1` colours: a set `S` with `|S| ≥ n^ε` such that
  the edges inside `S` take at most `m - 1` distinct colours.
-/

namespace OMA.S_opg_multicolour_erdos_hajnal_conjecture

/-- The set of colours on the edges inside `S`. -/
def colorsOn {n m : ℕ} (col : Sym2 (Fin n) → Fin m) (S : Finset (Fin n)) : Finset (Fin m) :=
  ((S ×ˢ S).filter fun p => p.1 ≠ p.2).image fun p => col s(p.1, p.2)

/-- **Multicolour Erdős–Hajnal conjecture.** -/
theorem main : ∀ (k m : ℕ) (χ : Sym2 (Fin k) → Fin m), 2 ≤ k → 2 ≤ m →
    ∃ ε : ℝ, 0 < ε ∧ ∀ (n : ℕ) (col : Sym2 (Fin n) → Fin m),
      (∃ f : Fin k → Fin n, Function.Injective f ∧
        ∀ a b : Fin k, a ≠ b → col s(f a, f b) = χ s(a, b)) ∨
      (∃ S : Finset (Fin n), (n : ℝ) ^ ε ≤ (S.card : ℝ) ∧ (colorsOn col S).card ≤ m - 1) := by
  sorry

end OMA.S_opg_multicolour_erdos_hajnal_conjecture
