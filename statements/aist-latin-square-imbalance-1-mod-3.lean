import Mathlib

/-!
# Minimum imbalance of Latin squares of order n ≡ 1 (mod 3)

Source: https://arxiv.org/abs/2603.08322
(H. Xia, C. P. Gomes, B. Selman, S. Szeider, *Agentic Neurosymbolic Collaboration for
Mathematical Discovery: A Case Study in Combinatorial Design*, 2026), Section 2 and Section 4.
Credit: @eltociear

Conventions, following Section 2 of the source:
* rows, columns and symbols are `ℤ_n = {0, …, n-1}`, here `Fin n`; a square is
  `L : Fin n → Fin n → Fin n`, `L r c` being the symbol in row `r`, column `c`;
* `pos(r, s)` is the column containing symbol `s` in row `r`;
* the distance between rows `r₁, r₂` is `d(r₁, r₂) = ∑_s |pos(r₁, s) - pos(r₂, s)|`;
* the imbalance is `I(L) = (1/3) ∑_{0 ≤ r₁ < r₂ ≤ n-1} |3·d(r₁, r₂) - n(n+1)|`,
  i.e. `∑_{r₁<r₂} |d(r₁, r₂) - n(n+1)/3|`, computed in `ℚ`.

To avoid inverting the rows, `d(r₁, r₂)` is written as the sum of `|c₁ - c₂|` over all pairs of
columns with `L r₁ c₁ = L r₂ c₂`. In a Latin square each symbol `s` gives exactly one such pair,
namely `(pos(r₁, s), pos(r₂, s))`, so this is the source's `d`.

The catalogue entry phrases the distance between two *symbols* (summing over rows), while the
source (Section 2, eq. (1)) measures the distance between two *rows* (summing over symbols).
The source's definition is used here. The two minima coincide: the conjugate square obtained
by swapping the roles of rows and symbols is again Latin and exchanges the two quantities.

Theorem 3 of the source proves `I(L) ≥ 4n(n-1)/9` for every Latin square of order
`n ≡ 1 (mod 3)`, and Theorem 6 gives squares attaining it for `4 ≤ n ≤ 52`. The open question
is whether the minimum equals `4n(n-1)/9` for every `n ≡ 1 (mod 3)`; this file states the
positive answer. (For `n = 1` both sides are `0`.)
-/

namespace OMA.S_aist_latin_square_imbalance_1_mod_3

/-- A Latin square of order `n`: each symbol occurs exactly once in every row and in every
column. -/
def IsLatin {n : ℕ} (L : Fin n → Fin n → Fin n) : Prop :=
  (∀ r, Function.Bijective (L r)) ∧ ∀ c, Function.Bijective (fun r => L r c)

/-- The distance `d(r₁, r₂) = ∑_s |pos(r₁, s) - pos(r₂, s)|` between rows `r₁` and `r₂`,
written as a sum over the pairs of columns `(c₁, c₂)` carrying the same symbol. -/
def rowDist {n : ℕ} (L : Fin n → Fin n → Fin n) (r₁ r₂ : Fin n) : ℤ :=
  ∑ c₁ : Fin n, ∑ c₂ : Fin n, if L r₁ c₁ = L r₂ c₂ then |(c₁ : ℤ) - (c₂ : ℤ)| else 0

/-- The imbalance `I(L) = (1/3) ∑_{r₁ < r₂} |3·d(r₁, r₂) - n(n+1)|` (eq. (1) of the source). -/
def imbalance {n : ℕ} (L : Fin n → Fin n → Fin n) : ℚ :=
  (1 / 3 : ℚ) * ∑ r₁ : Fin n, ∑ r₂ : Fin n,
    if r₁ < r₂ then (|3 * rowDist L r₁ r₂ - (n : ℤ) * (n + 1)| : ℚ) else 0

/-- For every `n ≡ 1 (mod 3)`, the minimum imbalance of a Latin square of order `n` is
`4n(n-1)/9`. -/
theorem main :
    ∀ n : ℕ, n % 3 = 1 →
      IsLeast {I : ℚ | ∃ L : Fin n → Fin n → Fin n, IsLatin L ∧ imbalance L = I}
        (4 * n * (n - 1) / 9 : ℚ) := by
  sorry

end OMA.S_aist_latin_square_imbalance_1_mod_3
