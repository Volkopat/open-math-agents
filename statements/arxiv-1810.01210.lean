import Mathlib

/-!
# Grytczuk's (k+2)-conjecture on k-Thue sequences

Source: https://arxiv.org/abs/1810.01210, Conjecture 1 (Grytczuk, 2002), as
stated by Borut Lužar, Martina Mockovčiaková, Pascal Ochem, Alexandre Pinlou
and Roman Soták
Credit: @pyaf

A d-subsequence of x₁ ⋯ xₙ is an arithmetic subsequence x_i x_(i+d) x_(i+2d) ⋯.
A sequence is k-Thue if every d-subsequence with 1 ≤ d ≤ k is non-repetitive,
i.e. contains no two consecutive equal blocks. Conjecture: for every positive
integer k, k + 2 symbols suffice to construct a k-Thue sequence of any length.
The paper confirms k ≤ 8; searches of arXiv for k-Thue sequences and for
nonrepetitive sequences on arithmetic progressions found no later resolution.

Indices start at 0. A repetition in the d-subsequence starting at index i consists of the
2t consecutive terms x_i, x_(i+d), …, x_(i+(2t-1)d) with the first t equal
to the last t.
-/

namespace OMA.S_arxiv_1810_01210

/-- The first n terms of x form a k-Thue sequence: every d-subsequence with
1 ≤ d ≤ k is non-repetitive. Terms from index n on are ignored. -/
def IsKThue {m : ℕ} (k n : ℕ) (x : ℕ → Fin m) : Prop :=
  ∀ d ∈ Finset.Icc 1 k, ∀ i ∈ Finset.range n, ∀ t ∈ Finset.Icc 1 n,
    i + (2 * t - 1) * d < n → ¬ ∀ j ∈ Finset.range t, x (i + j * d) = x (i + (j + t) * d)

theorem main : ∀ k, 1 ≤ k → ∀ n, ∃ x : ℕ → Fin (k + 2), IsKThue k n x := by
  sorry

end OMA.S_arxiv_1810_01210
