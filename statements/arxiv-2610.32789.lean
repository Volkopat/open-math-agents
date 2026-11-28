import Mathlib

/-!
# Triangle-free sets in exact-distance Hamming graphs: fixed even distances

Source: arXiv:2610.32789, "Triangle-Free Sets in Exact-Distance Hamming Graphs",
Conjecture 1.7.
Credit: @jagraj28

For `q ≥ 2`, `n ≥ 0` and `r ≥ 1`, the graph `H_q(n, r)` has vertex set `[q]^n` (words of length
`n` over an alphabet of size `q`), and two words are adjacent when their Hamming distance is
exactly `r` (Definition 1.1 and the paragraph before it). `T_q(n, r)` is the largest size of a
set `A ⊆ [q]^n` such that the induced subgraph `H_q(n, r)[A]` is triangle-free.

Conjecture 1.7 (fixed even distances): for every fixed `q ≥ 2` and `h ≥ 1`,
`T_q(n, 2h) = Θ_{q,h}(q^n / n^h)` as `n → ∞`.

Proposition 1.2 of the paper proves the upper bound `T_q(n, 2h) = O_h(q^n / n^h)`, and
Theorem 1.3 proves the case `h = 1`; the open part is the lower bound for `h ≥ 2`. The
statement below is the full conjecture as written in the paper.

Conventions.
* The alphabet `[q]` is `Fin q` and a word of length `n` is a function `Fin n → Fin q`.
* Hamming distance is Mathlib's `hammingDist`, the number of coordinates where two words differ.
* The graph is `SimpleGraph.fromRel` of the relation `hammingDist x y = r`: `x` and `y` are
  adjacent when `x ≠ y` and `hammingDist x y = r` (the symmetric closure adds nothing, because
  Hamming distance is symmetric). For `r ≥ 1` the condition `x ≠ y` is automatic.
* "Triangle-free" is `CliqueFree 3` of the induced subgraph `G.induce A`.
* `T q n r` is the supremum (a maximum, since all sizes are at most `q ^ n`) of the sizes of
  such finite sets `A`; the empty set always qualifies.
* `Θ_{q,h}` with `q, h` fixed and `n → ∞` is Mathlib's `Asymptotics.IsTheta` along `atTop`,
  for real-valued functions of `n`.
-/

namespace OMA.S_arxiv_2610_32789

open Asymptotics Filter

/-- The exact-distance Hamming graph `H_q(n, r)`: words at Hamming distance exactly `r`. -/
def hammingGraph (q n r : ℕ) : SimpleGraph (Fin n → Fin q) :=
  SimpleGraph.fromRel fun x y => hammingDist x y = r

/-- `T_q(n, r)`: the largest size of a vertex set of `H_q(n, r)` inducing a triangle-free
subgraph. -/
noncomputable def T (q n r : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset (Fin n → Fin q), A.card = k ∧
    ((hammingGraph q n r).induce (A : Set (Fin n → Fin q))).CliqueFree 3}

/-- Conjecture 1.7 of arXiv:2610.32789: `T_q(n, 2h) = Θ(q^n / n^h)` for fixed `q ≥ 2`,
`h ≥ 1`. -/
theorem main : ∀ q ≥ 2, ∀ h ≥ 1,
    (fun n : ℕ => (T q n (2 * h) : ℝ)) =Θ[atTop] (fun n : ℕ => (q : ℝ) ^ n / (n : ℝ) ^ h) := by
  sorry

end OMA.S_arxiv_2610_32789
