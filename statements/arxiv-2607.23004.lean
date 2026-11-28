import Mathlib

/-!
# Exact value of $t(N)$ for families with arithmetic-progression intersections (Erdős #272)

Source: https://arxiv.org/abs/2607.23004
Credit: @SulkBash

## The problem (as the source states it)

Let $t(N)$ be the largest $t$ for which there exist distinct sets
$A_1, \dots, A_t \subseteq \{1, \dots, N\}$ such that $A_i \cap A_j$ is a nonempty arithmetic
progression for all $i \ne j$ (Erdős Problem #272).

Known:
- Simonovits and Sós proved $t(N) = O(N^2)$.
- Szabó's construction gives $t(N) \ge \binom{N}{2} + 1 + \lfloor (N-1)/4 \rfloor$.

The paper determines $t(N)$ exactly for all $3 \le N \le 12$ by exhaustive computation. Szabó's
lower bound is exact in that range, and the paper conjectures that
$$t(N) = \binom{N}{2} + 1 + \left\lfloor \frac{N-1}{4} \right\rfloor \quad\text{for every } N.$$

## Formalization notes

* **Arithmetic progressions.** `IsAP S` says
  `S = {a, a + d, …, a + (k - 1) d}` with `k ≥ 1` terms and difference `d ≥ 1`. So `S` is a
  nonempty arithmetic progression of naturals. Singletons and two-element sets are APs, and the
  empty set is not.
  - Upstream `Erdos272` uses `Set.IsAPOfLength l` with `l > 0`, i.e.
    `ENat.card S = l ∧ S = {a + n • d | n < l}`. Over `ℕ` the two agree: the card condition forces
    `d ≥ 1` once `S` has two or more elements.
* **Families.** A family is a `Finset (Finset ℕ)`, so its sets are distinct. `IsArithInterFamily N A`
  requires every member to be a subset of `{1, …, N}` and every two distinct members to meet in
  an AP.
* **Statement.** "$t(N) = f(N)$" is stated without `sSup`: some family has exactly $f(N)$
  members, and every family has at most $f(N)$ members.
  - The first conjunct is Szabó's construction; the second is the open part.
* **Range.** `N` ranges over `N ≥ 1`, with `N.choose 2 = N(N-1)/2` and natural-number floor
  division `(N - 1) / 4`.
* **Upstream.** Upstream formal-conjectures states Erdős #272 as a value question,
  `Erdos272.erdos_272` with `answer := sorry`. This file states the paper's specific conjectured
  value.
-/

namespace OMA.S_arxiv_2607_23004

/-- `S` is a nonempty arithmetic progression `{a, a + d, …, a + (k - 1) d}`, `k ≥ 1`, `d ≥ 1`. -/
def IsAP (S : Finset ℕ) : Prop :=
  ∃ a d k : ℕ, 0 < k ∧ 0 < d ∧ S = (Finset.range k).image (fun i => a + i * d)

/-- A family of distinct subsets of `{1, …, N}` in which any two distinct members intersect in a
nonempty arithmetic progression. -/
def IsArithInterFamily (N : ℕ) (A : Finset (Finset ℕ)) : Prop :=
  A ⊆ (Finset.Icc 1 N).powerset ∧ ∀ S ∈ A, ∀ T ∈ A, S ≠ T → IsAP (S ∩ T)

/-- The conjectured exact value `t(N) = C(N, 2) + 1 + ⌊(N - 1) / 4⌋`: it is attained, and no
family is larger. -/
theorem main :
    ∀ N : ℕ, 1 ≤ N →
      (∃ A : Finset (Finset ℕ), IsArithInterFamily N A ∧
          A.card = N.choose 2 + 1 + (N - 1) / 4) ∧
        ∀ A : Finset (Finset ℕ), IsArithInterFamily N A →
          A.card ≤ N.choose 2 + 1 + (N - 1) / 4 := by
  sorry

end OMA.S_arxiv_2607_23004
