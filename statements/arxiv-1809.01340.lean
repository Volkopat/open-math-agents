import Mathlib

/-!
# Log-concavity of the first-entry refinement of Lassalle's sequence

Source: https://arxiv.org/abs/1809.01340, Conjecture 7.1
(Colin Defant, Michael Engen and Jordan A. Miller)
Credit: @pyaf

West's stack-sorting map s sends L n R, with n the largest entry, to
s(L) s(R) n. A permutation is uniquely sorted if it has exactly one preimage
under s. Let A_(k+1)(ℓ) be the number of uniquely sorted permutations of
1, …, 2k+1 whose first entry is ℓ; summing over ℓ gives Lassalle's sequence
1, 1, 5, 56, …. Conjecture: for every k ≥ 0 the sequence
(A_(k+1)(ℓ))_(1 ≤ ℓ ≤ 2k+1) is log-concave, i.e.
A_(k+1)(ℓ)² ≥ A_(k+1)(ℓ−1) A_(k+1)(ℓ+1) for 2 ≤ ℓ ≤ 2k.

Later work: arXiv:2008.08222 (Sankar) proves unimodality, verifies
log-concavity for k ≤ 53 and states that log-concavity remains open.

The map s is computed by the usual stack algorithm: before pushing an entry,
pop every smaller entry from the top of the stack; at the end, pop the rest.
It gives 1, 1, 5, 56 uniquely sorted permutations for k = 0, 1, 2, 3.
-/

namespace OMA.S_arxiv_1809_01340

/-- West's stack-sorting map, run on the input with the given stack (top first). -/
def stackSort : List ℕ → List ℕ → List ℕ
  | [], st => st
  | x :: xs, st => st.takeWhile (· < x) ++ stackSort xs (x :: st.dropWhile (· < x))

/-- All permutations of 1, …, n, each once. -/
def perms (n : ℕ) : List (List ℕ) := (List.range' 1 n).permutations

/-- A_(k+1)(ℓ): uniquely sorted permutations of 1, …, 2k+1 with first entry ℓ. -/
def A (k ℓ : ℕ) : ℕ :=
  ((perms (2 * k + 1)).filter (fun π => π.head? = some ℓ ∧
    ((perms (2 * k + 1)).filter (fun σ => stackSort σ [] = π)).length = 1)).length

theorem main : ∀ k ℓ : ℕ, 2 ≤ ℓ → ℓ ≤ 2 * k →
    A k (ℓ - 1) * A k (ℓ + 1) ≤ A k ℓ ^ 2 := by
  sorry

end OMA.S_arxiv_1809_01340
