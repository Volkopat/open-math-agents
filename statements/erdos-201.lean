import Mathlib

/-!
# Erdős Problem 201

Source: https://www.erdosproblems.com/201
Credit: @mgv27

Let $G_k(N)$ be such that any set of $N$ integers contains a subset of size at least $G_k(N)$
which does not contain a $k$-term arithmetic progression. Determine the size of $G_k(N)$. How
does it relate to $R_k(N)$, the size of the largest subset of $\{1,\ldots,N\}$ without a
$k$-term arithmetic progression? Is it true that
$\lim_{N\to\infty} R_3(N)/G_3(N) = 1$?

Formalization notes:
* `main` states the specific question about `k = 3`; the other questions on the page ask for no
  specific statement.
* `G_k(N)` is the largest value with the stated property, i.e. the minimum, over all sets `A` of
  `N` integers, of the size of a largest subset of `A` without a `k`-term progression.
* For `k = 3`, a subset without a three-term progression is a `ThreeAPFree` set, and the size of
  a largest such subset of a finset `s` is Mathlib's `addRothNumber s`.
* Checked by computer against the values on the source page: with these definitions
  `G3 5 = 3`, `R3 5 = 4`, `R3 14 = 8` and `G3 14 ≤ 7`.
-/

namespace OMA.S_erdos_201

open Filter Topology

/-- `R_3(N)`: the size of the largest subset of `{1, …, N}` without a three-term arithmetic
progression. -/
noncomputable def R3 (N : ℕ) : ℕ :=
  addRothNumber (Finset.Icc (1 : ℤ) N)

/-- `G_3(N)`: every set of `N` integers contains a subset of size `G_3(N)` without a three-term
arithmetic progression, and `G_3(N)` is the largest such value. -/
noncomputable def G3 (N : ℕ) : ℕ :=
  sInf {r : ℕ | ∃ A : Finset ℤ, A.card = N ∧ addRothNumber A = r}

/-- Erdős Problem 201: is it true that `R_3(N) / G_3(N) → 1`? -/
theorem main : Tendsto (fun N : ℕ => (R3 N : ℝ) / (G3 N : ℝ)) atTop (𝓝 1) := by
  sorry

end OMA.S_erdos_201
