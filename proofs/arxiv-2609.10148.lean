import OMAStatements.S_arxiv_2609_10148
import Mathlib

/-!
# arXiv 2609.10148: extremal restricted sumsets need not be arithmetic progressions

Counterexample modulo `p = 11`: `A = {0, 1, 2, 4}` and `B = {0, 1, 2, 3, 4}`.
The restricted sumset `{a + b : a ∈ A, b ∈ B, a ≠ b}` is `{1, …, 7}`, which has
`7 = |A| + |B| - 2` elements, and `|A| = 4 ≠ 5 = |B|`, `|A| + |B| = 9 ≤ 11`.
But `A` is not an arithmetic progression modulo `11` (a finite check over all first terms and
differences).
-/

open OMA.S_arxiv_2609_10148 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2609_10148.main) := by
  intro h
  have key := h 11 (by norm_num) ({0, 1, 2, 4} : Finset (ZMod 11))
    ({0, 1, 2, 3, 4} : Finset (ZMod 11)) (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel)
  have hA : ¬ IsArithProg ({0, 1, 2, 4} : Finset (ZMod 11)) := by
    unfold IsArithProg
    decide +kernel
  exact hA key.1
