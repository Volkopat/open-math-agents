import Mathlib

/-!
# Torus queen independence

Source: K. K. Williams, *Torus Queen Independence*, https://arxiv.org/abs/2404.18237
(Conjecture 6 and the abstract, in v4)
Credit: @SulkBash

## The problem (as the source states it)

A queen on $\mathbb{Z}_n^d$ can move by $\lambda \in \mathbb{Z}_n$ times
$e \in \{-1, 0, 1\}^d$. Two queens are in conflict if they are mutually a move apart.
- In 1918, Pólya showed that $n$ queens on $\mathbb{Z}_n^2$ cannot be conflict-free if $n$ is a
  multiple of $2$ or $3$.
- Conjecture: no $n^{d-1}$ queens on $\mathbb{Z}_n^d$ are conflict-free if $n$ is divisible by a
  prime less than $2^d$.

This is the open direction of the paper's Conjecture 6,
$Q_d(n) = n^{d-1} \iff \gcd(n, (2^d - 1)!) = 1$. Its Theorem 8 proves the other direction. The
paper notes that the open direction is unknown in general, and its Theorem 7 implies it for
squarefree $n$.

## Formalization notes

* **Board.** The board is `Fin d → ZMod n`, i.e. $\mathbb{Z}_n^d$ with `n > 0`. A set of queens is
  a `Finset` of cells.
* **Conflict.** Cells `y ≠ z` conflict when `z - y = t • e` for some `t : ZMod n` and some
  `e : Fin d → ZMod n` with every entry in `{-1, 0, 1}`, as in the source's Definition 3.
  - With `y ≠ z`, such an `e` is automatically nonzero.
  - The relation is symmetric: replace `t` by `-t`.
* **Conflict-free.** No two distinct queens in the set conflict.
* **Statement.** `main` takes the literal form of the source: when some prime `p < 2 ^ d` divides
  `n`, there is no conflict-free set of exactly `n ^ (d - 1)` queens.
  - Every subset of a conflict-free set is conflict-free, so this is equivalent to
    $Q_d(n) < n^{d-1}$ in the paper's notation.
  - For `d = 0` and `d = 1` there is no prime below `2 ^ d`, so the hypothesis never holds.
-/

namespace OMA.S_arxiv_2404_18237

/-- Two cells `y z` of `ℤ_n^d` are a queen move apart: `z - y = t • e` with `t ∈ ℤ_n` and
`e ∈ {-1, 0, 1}^d`. -/
def QueenMove (n d : ℕ) (y z : Fin d → ZMod n) : Prop :=
  ∃ (t : ZMod n) (e : Fin d → ZMod n), (∀ i, e i = -1 ∨ e i = 0 ∨ e i = 1) ∧ z - y = t • e

/-- A set of queens on `ℤ_n^d` is conflict-free if no two distinct queens are a move apart. -/
def ConflictFree (n d : ℕ) (S : Finset (Fin d → ZMod n)) : Prop :=
  ∀ y ∈ S, ∀ z ∈ S, y ≠ z → ¬ QueenMove n d y z

/-- If `n` has a prime divisor less than `2 ^ d`, then no `n ^ (d - 1)` queens on `ℤ_n^d` are
conflict-free. -/
theorem main :
    ∀ n d : ℕ, 0 < n → (∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p < 2 ^ d) →
      ¬ ∃ S : Finset (Fin d → ZMod n), S.card = n ^ (d - 1) ∧ ConflictFree n d S := by
  sorry

end OMA.S_arxiv_2404_18237
