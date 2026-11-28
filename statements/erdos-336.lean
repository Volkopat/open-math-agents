import Mathlib

/-!
# Erdős Problem 336

Source: https://www.erdosproblems.com/336
Credit: @jbhooper9000

## The problem (as stated at the source, [ErGr80, p.51])

For $r \ge 2$ let $h(r)$ be the maximal finite $k$ such that there exists a basis
$A \subseteq \mathbb{N}$ of order $r$ (so every large integer is the sum of at most $r$
integers from $A$) and exact order $k$ (so every large integer is the sum of exactly $k$
integers from $A$). Find the value of
$$\lim_r \frac{h(r)}{r^2}.$$

Known (from the source): Erdős and Graham [ErGr80b] showed a basis has an exact order iff
$a_2 - a_1, a_3 - a_2, \dots$ are coprime, and $1/4 \le \lim h(r)/r^2 \le 5/4$; the best
bounds are $1/3$ (Grekos [Gr88]) and $1/2$ (Nash [Na93]). $h(2) = 4$, $h(3) = 7$,
$10 \le h(4) \le 11$. A proof claim on the source page (Colin Snyder, 2026-07-15, with a
Lean formalization) asserts that the limit exists and equals $1/3$.

## Formalization notes

* `IsSumOfExactly A k n`: `n` is a sum of exactly `k` elements of `A`, repetitions allowed
  (a multiset of size `k` drawn from `A`). Sums of `0` elements are `0`.
* `IsBasisOfOrder A r`: every sufficiently large integer is a sum of at most `r` elements
  of `A`, exactly as in the parenthetical of the source ("at most `r`").
* `HasExactSums A k`: every sufficiently large integer is a sum of exactly `k` elements of
  `A`. This property is upward closed in `k` (add a fixed element `a ∈ A` to a
  representation of `n - a`), so the *exact order* is the least such `k`: `exactOrder A`.
  Only bases having some exact order are admitted ("maximal finite `k`").
* `h r` is the supremum of the exact orders of bases of order `r`. This set is bounded
  (Erdős–Graham), so `sSup` is its maximum; were it unbounded, `sSup` would be the junk
  value `0` and `main` would be false, which matches the source's use of a finite maximum.
* Whether `0 ∈ A` is allowed does not change `h`: a basis containing `0` has exact order at
  most `r`, which never exceeds the maximum.
* "Find the value of the limit": `main` states the value `1/3` claimed on the source page
  (together with existence of the limit, via `Tendsto`). `1/3` is also the best known
  lower bound, and a disproof of `main` would show the claim wrong. The restriction
  `r ≥ 2` is immaterial for a limit at infinity.
-/

namespace OMA.S_erdos_336

open Filter
open scoped Topology

/-- `n` is the sum of exactly `k` elements of `A` (repetitions allowed). -/
def IsSumOfExactly (A : Set ℕ) (k n : ℕ) : Prop :=
  ∃ s : Multiset ℕ, Multiset.card s = k ∧ (∀ a ∈ s, a ∈ A) ∧ s.sum = n

/-- `A` is a basis of order `r`: every sufficiently large integer is the sum of at most `r`
elements of `A`. -/
def IsBasisOfOrder (A : Set ℕ) (r : ℕ) : Prop :=
  ∀ᶠ n in atTop, ∃ j ≤ r, IsSumOfExactly A j n

/-- Every sufficiently large integer is the sum of exactly `k` elements of `A`. -/
def HasExactSums (A : Set ℕ) (k : ℕ) : Prop :=
  ∀ᶠ n in atTop, IsSumOfExactly A k n

/-- The exact order of `A`: the least `k` such that every sufficiently large integer is the
sum of exactly `k` elements of `A`. -/
noncomputable def exactOrder (A : Set ℕ) : ℕ :=
  sInf {k | HasExactSums A k}

/-- `h r`: the maximal finite exact order of a basis of order `r`. -/
noncomputable def h (r : ℕ) : ℕ :=
  sSup {k | ∃ A : Set ℕ, IsBasisOfOrder A r ∧ (∃ m, HasExactSums A m) ∧ exactOrder A = k}

/-- Erdős Problem 336, with the value `1/3` claimed on the source page:
`h(r) / r ^ 2 → 1/3`. -/
theorem main : Tendsto (fun r : ℕ => (h r : ℝ) / (r : ℝ) ^ 2) atTop (𝓝 (1 / 3)) := by
  sorry

end OMA.S_erdos_336
