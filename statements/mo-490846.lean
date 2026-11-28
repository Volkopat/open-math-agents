import Mathlib

/-!
# An additive version of the algebraic strengthening of Frankl's union-closed conjecture

Source: https://mathoverflow.net/questions/490846
Asked by MathOverflow user "Thinh Dinh" ("More about the algebraic strengthening of Frankl's
union-closed conjecture").
Credit: @ShoQo

The question states three related conjectures for a union-closed family `F` of subsets of
`[n] = {1, ..., n}`. Conjecture (1), for reals `x_i ≥ 1`, contains Frankl's conjecture itself
(take every `x_i = 1`) and is not stated here. Conjecture (2) is the version for `x_i > 1` and all
large exponents `K`. The asker shows that (2) is equivalent to conjecture (3), stated with
`y_i = ln x_i > 0`, which is the one formalized here:

  Let `S = {s_1 > s_2 > ... > s_m}` be the set of reals of the form `∑_{i ∈ A} y_i`, `A ⊆ [n]`.
  There exist `k ∈ [n]` and `0 ≤ l ≤ m` such that
  `|{A ∈ F | k ∈ A, ∑_{i ∈ A} y_i = s_j}| = |{A ∈ F | k ∉ A, ∑_{i ∈ A ∪ {k}} y_i = s_j}|`
  for all `j ≤ l`, and either `l = m` or the first count exceeds the second at `s_{l+1}`.

Formalization notes.
* `[n]` is `Fin n`; `F` is a finset of finsets, closed under union.
* `L k s` and `R k s` are the two counts at the value `s`. Both vanish unless `s ∈ S` (a set
  `A ∪ {k}` is a subset of `[n]`), so scanning `s_1 > s_2 > ...` from the top is the same as
  ranging over all reals in decreasing order. The condition then reads: either `L k s = R k s`
  for every `s` (the case `l = m`), or there is an `s` with `R k s < L k s` and `L k t = R k t`
  for every `t > s` (the case `l < m`, with `s = s_{l+1}`).
* As in Frankl's conjecture, `F` is assumed to contain a nonempty set. (For `F = {∅}` and
  `n ≥ 1` the condition fails for every `k`: the only nonzero count is `R k (y_k) = 1`.)
-/

namespace OMA.S_mo_490846

open Finset

/-- Number of members of `F` containing `k` with weight `s`. -/
noncomputable def L {n : ℕ} (F : Finset (Finset (Fin n))) (y : Fin n → ℝ) (k : Fin n) (s : ℝ) :
    ℕ := by
  classical
  exact (F.filter fun A => k ∈ A ∧ ∑ i ∈ A, y i = s).card

/-- Number of members `A` of `F` not containing `k` with `A ∪ {k}` of weight `s`. -/
noncomputable def R {n : ℕ} (F : Finset (Finset (Fin n))) (y : Fin n → ℝ) (k : Fin n) (s : ℝ) :
    ℕ := by
  classical
  exact (F.filter fun A => k ∉ A ∧ ∑ i ∈ insert k A, y i = s).card

/-- Conjecture (3) of the question. -/
theorem main : ∀ (n : ℕ) (F : Finset (Finset (Fin n))),
    (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) → (∃ A ∈ F, A.Nonempty) →
    ∀ (y : Fin n → ℝ), (∀ i, 0 < y i) →
    ∃ k : Fin n, (∀ s, L F y k s = R F y k s) ∨
      ∃ s, R F y k s < L F y k s ∧ ∀ t, s < t → L F y k t = R F y k t := by
  sorry

end OMA.S_mo_490846
