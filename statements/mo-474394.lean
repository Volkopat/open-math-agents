import Mathlib

/-!
# Latin subsquares of balanced frequency squares

Source: https://mathoverflow.net/questions/474394
Asked by MathOverflow user So Ya.

Consider an `n × n` array with `n = a b` in which each row and each column contains each of the
`a` symbols `1, ..., a` exactly `b` times (a balanced frequency square). The question asks
whether there is always a subsquare, given by a set of `a` rows and a possibly different set
of `a` columns, which forms an `a × a` Latin square.

Translation choices.
* The array is a function `M : Fin (a * b) → Fin (a * b) → Fin a` (rows, columns, symbols),
  with `a, b ≥ 1`.
* Balanced: for every row `i` and symbol `s` there are exactly `b` columns `j` with
  `M i j = s`, and for every column `j` and symbol `s` there are exactly `b` rows `i` with
  `M i j = s`.
* The subsquare on row set `R` and column set `C` with `|R| = |C| = a` is Latin when every
  symbol occurs in every row of the subsquare and in every column of the subsquare (with `a`
  cells and `a` symbols this means each symbol occurs exactly once).
* `main` is the affirmative answer.
-/

namespace OMA.S_mo_474394

theorem main :
    ∀ a b : ℕ, 0 < a → 0 < b → ∀ M : Fin (a * b) → Fin (a * b) → Fin a,
      (∀ i s, (Finset.univ.filter fun j => M i j = s).card = b) →
      (∀ j s, (Finset.univ.filter fun i => M i j = s).card = b) →
      ∃ R C : Finset (Fin (a * b)), R.card = a ∧ C.card = a ∧
        (∀ i ∈ R, ∀ s : Fin a, ∃ j ∈ C, M i j = s) ∧
        (∀ j ∈ C, ∀ s : Fin a, ∃ i ∈ R, M i j = s) := by
  sorry

end OMA.S_mo_474394
