import Mathlib

/-!
# The "No Justice in the Universe" phenomenon: why honesty of effort may not be rewarded in tournaments

Source: https://arxiv.org/abs/1803.00823 (P. Hegarty, A. Martinsson, E. Wedin, 2018), Conjecture 4.2.
Credit: @tatashbar

Conjecture 4.2 of the source: `𝒜*_n = 𝒜_n` for every `n ∈ ℕ`, where
* `𝒜_n` is the closure of the set of win vectors `wv(T, P)` over all symmetric and honest `n`-player
  tournaments `T` and all doubly monotonic matrices `P`;
* `𝒜*_n` is the convex hull of the vectors `v(G)`, `G ∈ 𝒢_n`, a family of digraphs defined in Section 4.

`main` states the conjecture as posed.

What the source proves: `𝒜*_n = 𝒜_n` for `n = 1, 2, 3` (Theorem 3.6 for `n = 3`) and `𝒜*_n ⊆ 𝒜_n` for
every `n` (Theorem 4.3). The inclusion `𝒜_n ⊆ 𝒜*_n` is the open part for `n ≥ 4`.

Status: computations by the contributor (not a Lean proof, and not in the source) indicate that the
conjecture is false for `n = 4`. For the doubly monotonic matrix with `p₁₂ = p₃₄ = 1/2` and
`p₁₃ = p₁₄ = p₂₃ = p₂₄ = 1` there is a symmetric and honest 4-player tournament (a double round robin,
12 matches, followed by a lottery that depends on the results) with win vector
`(11/48, 11/48, 13/48, 13/48)`, while every point of `𝒜*_4` has first coordinate at least `1/4`.
If that is right, the result to prove here is the negation of `main`.

Conventions of this translation (Section 2 of the source).
* Players are `Fin n` (player `i` of the source is `i - 1`). `ℕ` in the source is the positive integers,
  so `main` assumes `1 ≤ n`. (For `n = 0` the two sets below differ for a trivial reason.)
* `ℳ_n` is the set of real `n × n` matrices with entries in `[0, 1]` and `P + Pᵀ = 1`; `P i j` is the
  probability that `i` beats `j`. `𝒟_n` is the subset of doubly monotonic matrices: `P i j` is
  non-increasing in `i` and non-decreasing in `j`.
* A tournament is, in the source, a randomized algorithm that repeatedly announces a pair of players to
  play a match, sees only who won, uses at most a bounded number of matches, and finally announces a
  winner. Here it is a finite tree: `declare w` announces the winner `w`; `chance k w next` moves to
  the subtree `next t` with probability `w t` (`k` branches); `play i j ifI ifJ` lets `i` and `j` play
  and continues with `ifI` if `i` wins and with `ifJ` if `j` wins. `WellFormed` asks the weights of each
  chance node to be a probability vector and the two players of a match to be distinct. A general
  randomized algorithm with a bound on the number of matches has, for every `P`, the same win
  probabilities as such a tree (group its internal states by the visible history of announced pairs
  and results), and honesty is preserved by this grouping, so the set of achievable win vectors is
  the same.
* `winProb P T k` is the probability that `k` wins `T` when each match between `i` and `j` is won by
  `i` with probability `P i j`, independently.
* Symmetric: for every `P ∈ ℳ_n`, every permutation `σ` and every player `i`,
  `π_i(P) = π_{σ(i)}(Q)`, where `Q (σ i) (σ j) = P i j`.
* Honest: in every state in which a pair `{i, j}` has just been announced, and for every `P ∈ ℳ_n`,
  the probability that `i` wins the tournament given that he wins this match is at least the
  probability given that he loses it (and the same for `j`). The states are the `play` nodes that can
  be reached, that is, those not below a chance branch of weight zero. As in Remark 2.1 of the source,
  randomness drawn before a match is part of the state (a chance node above the `play` node).
* `𝒢_n`: digraphs on `{1, ..., n}`, loops and multiple arcs allowed, with exactly two arcs out of each
  vertex (Rule 1), every arc `(i, j)` with `j ≤ i` (Rule 2), and the two arcs out of `i` having the same
  head only if that head is `1` or `i` (Rule 3). A digraph is given by the heads `a i`, `b i` of the two
  arcs out of each vertex `i`. `v(G)_i = indeg(i) / (2n)`.
-/

namespace OMA.S_arxiv_1803_00823

/-- `ℳ_n`: matrices of match-winning probabilities, entries in `[0, 1]` and `P + Pᵀ = 1`. -/
def matchMatrices (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {P | (∀ i j, 0 ≤ P i j ∧ P i j ≤ 1) ∧ ∀ i j, P i j + P j i = 1}

/-- `𝒟_n`: the doubly monotonic matrices, `P i j` non-increasing in `i` and non-decreasing in `j`. -/
def doublyMonotonic (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {P | P ∈ matchMatrices n ∧ (∀ i i' j, i ≤ i' → P i' j ≤ P i j) ∧ ∀ i j j', j ≤ j' → P i j ≤ P i j'}

/-- An `n`-player tournament, as a finite tree of announcements, random choices and matches. -/
inductive Tournament (n : ℕ) : Type
  /-- Announce the winner. -/
  | declare (w : Fin n) : Tournament n
  /-- Continue with `next t` with probability `weight t`. -/
  | chance (k : ℕ) (weight : Fin k → ℝ) (next : Fin k → Tournament n) : Tournament n
  /-- Players `i` and `j` play a match; continue with `ifI` if `i` wins, with `ifJ` if `j` wins. -/
  | play (i j : Fin n) (ifI ifJ : Tournament n) : Tournament n

/-- The weights of every chance node form a probability vector, and a match is between two distinct
players. -/
def Tournament.WellFormed {n : ℕ} : Tournament n → Prop
  | .declare _ => True
  | .chance _ weight next =>
      (∀ t, 0 ≤ weight t) ∧ (∑ t, weight t) = 1 ∧ ∀ t, (next t).WellFormed
  | .play i j ifI ifJ => i ≠ j ∧ ifI.WellFormed ∧ ifJ.WellFormed

/-- `π_k(P)`: the probability that player `k` wins the tournament when every match between `i` and
`j` is won by `i` with probability `P i j`. -/
noncomputable def Tournament.winProb {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) :
    Tournament n → Fin n → ℝ
  | .declare w, k => if k = w then 1 else 0
  | .chance _ weight next, k => ∑ t, weight t * (next t).winProb P k
  | .play i j ifI ifJ, k => P i j * ifI.winProb P k + P j i * ifJ.winProb P k

/-- Symmetry: renaming the players by `σ` renames the win probabilities, for every `P ∈ ℳ_n`.
`P.submatrix σ.symm σ.symm` is the matrix `Q` with `Q (σ i) (σ j) = P i j`. -/
def Tournament.Symmetric {n : ℕ} (T : Tournament n) : Prop :=
  ∀ P ∈ matchMatrices n, ∀ σ : Equiv.Perm (Fin n), ∀ i : Fin n,
    T.winProb P i = T.winProb (P.submatrix σ.symm σ.symm) (σ i)

/-- Honesty: at every reachable match and for every `P ∈ ℳ_n`, each of the two players is at least as
likely to win the tournament after winning the match as after losing it. -/
def Tournament.Honest {n : ℕ} : Tournament n → Prop
  | .declare _ => True
  | .chance _ weight next => ∀ t, 0 < weight t → (next t).Honest
  | .play i j ifI ifJ =>
      (∀ P ∈ matchMatrices n, ifJ.winProb P i ≤ ifI.winProb P i ∧ ifI.winProb P j ≤ ifJ.winProb P j) ∧
        ifI.Honest ∧ ifJ.Honest

/-- The achievable win vectors: `wv(T, P)` for `T` symmetric and honest and `P` doubly monotonic. -/
def achievable (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∃ T : Tournament n, T.WellFormed ∧ T.Symmetric ∧ T.Honest ∧
    ∃ P ∈ doublyMonotonic n, x = T.winProb P}

/-- `𝒜_n`: the closure of the set of achievable win vectors. -/
def setA (n : ℕ) : Set (Fin n → ℝ) := closure (achievable n)

/-- The vectors `v(G)`, `G ∈ 𝒢_n`. The digraph `G` has the arcs `i → a i` and `i → b i`; Rule 2 is
`a i ≤ i` and `b i ≤ i`, Rule 3 is `a i = b i → a i` is the first vertex or `a i = i`, and
`v(G) i = indeg(i) / (2n)`. -/
def starPoints (n : ℕ) : Set (Fin n → ℝ) :=
  {v | ∃ a b : Fin n → Fin n,
    (∀ i, a i ≤ i ∧ b i ≤ i ∧ (a i = b i → (a i : ℕ) = 0 ∨ a i = i)) ∧
    ∀ i, v i = (((Finset.univ.filter fun k => a k = i).card : ℝ) +
      ((Finset.univ.filter fun k => b k = i).card : ℝ)) / (2 * n)}

/-- `𝒜*_n`: the convex hull of the vectors `v(G)`, `G ∈ 𝒢_n`. -/
def setAStar (n : ℕ) : Set (Fin n → ℝ) := convexHull ℝ (starPoints n)

/-- Conjecture 4.2 of the source: `𝒜*_n = 𝒜_n` for every `n`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → setAStar n = setA n := by
  sorry

end OMA.S_arxiv_1803_00823
