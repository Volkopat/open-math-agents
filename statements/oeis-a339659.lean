import Mathlib

/-!
# A339659: column sums of the triangle of graphical partitions

Source: https://oeis.org/A339659
Credit: @avivorly

A339659 is the irregular triangle read by rows where `T(n,k)` is the number of graphical partitions of `2n` into `k`
parts, `0 <= k <= 2n`. The entry adds: an integer partition is graphical if it comprises the multiset of
vertex-degrees of some graph.

Conjecture (Gus Wiseman, in the entry): The column sums 1, 0, 1, 2, 7, 20, 67, ... are given by A304787.

A304787 is the expansion of `Product_{k>=1} (1 + x^k)^(binomial(2*k,k)/(k+1))` (offset 0; data 1, 1, 2, 7, 20, 67,
222, ...).

Conventions:
- A graphical partition with `k` parts is a multiset `m` of `k` positive integers that is the multiset of vertex
  degrees of a simple graph on `k` vertices, one vertex per part (`IsGraphical k m`, with the vertex set `Fin k`).
  Every part is `≥ 1`, so such a graph has no isolated vertex; the entry's program likewise uses exactly `k` vertex
  labels. The `DecidableRel` witness only serves to compute degrees; degrees do not depend on it.
- Column sums: each graphical partition with `k` parts lies in exactly one row `n`, the one with `2n` = its sum, so
  `Sum_n T(n,k)` is the number of multisets `m` with `k` parts, all parts `≥ 1`, even sum and `IsGraphical k m`; this
  is `colSum k`. (The sum of a degree multiset is always even, so the evenness condition only mirrors the row index
  `2n`.) The set is finite: every degree is at most `k - 1`, so only rows with `2n <= k(k-1)` contribute.
- `A304787 n` is the coefficient of `x^n` in `Product_{j=1..n} (1 + x^j)^(binomial(2j,j)/(j+1))` over `Polynomial ℕ`;
  the factors with `j > n` are `1 + x^j * (...)` and do not change that coefficient. The division is exact
  (`binomial(2j,j)/(j+1)` is the Catalan number).
- Index matching: the listed column sums are those of columns `k = 0, 1, ..., 6`. They agree with
  `A304787(k-1)` for `k = 2, ..., 6` (1, 2, 7, 20, 67), and with no other shift of A304787 on that range; columns 0 and 1
  (values 1 and 0) fit no shift together with the rest (with no shift, column 1 would already fail, as
  `A304787(1) = 1`). So the claim is read as: the column-`k` sum is `A304787(k-1)` for every `k >= 2`.
-/

namespace OMA.S_oeis_a339659

/-- `m` is graphical with `k` parts: it is the multiset of vertex degrees of some simple graph on the vertex set
`Fin k`. -/
def IsGraphical (k : ℕ) (m : Multiset ℕ) : Prop :=
  ∃ G : SimpleGraph (Fin k), ∃ _ : DecidableRel G.Adj, (Finset.univ.val.map fun v => G.degree v) = m

/-- The sum of column `k` of A339659 over all rows: the number of graphical partitions with `k` parts (all parts
`≥ 1`, even sum). -/
noncomputable def colSum (k : ℕ) : ℕ :=
  Set.ncard {m : Multiset ℕ | Multiset.card m = k ∧ (∀ x ∈ m, 1 ≤ x) ∧ Even m.sum ∧ IsGraphical k m}

/-- A304787(n): the coefficient of `x^n` in `Product_{j=1..n} (1 + x^j)^(binomial(2j,j)/(j+1))`. -/
noncomputable def A304787 (n : ℕ) : ℕ :=
  (∏ j ∈ Finset.Icc 1 n,
    ((1 + Polynomial.X ^ j : Polynomial ℕ) ^ (Nat.choose (2 * j) j / (j + 1)))).coeff n

theorem main : ∀ k : ℕ, 2 ≤ k → colSum k = A304787 (k - 1) := by
  sorry

end OMA.S_oeis_a339659
