import Mathlib

/-!
# Erdős Problem 327

Source: https://www.erdosproblems.com/327
Credit: @jbhooper9000

## The problem (as stated at the source, [ErGr80])

Suppose $A \subseteq \{1, \dots, N\}$ is such that if $a, b \in A$ and $a \neq b$ then
$a + b \nmid ab$. Can $A$ be 'substantially more' than the odd numbers?

What if $a, b \in A$ with $a \neq b$ implies $a + b \nmid 2ab$? Must $|A| = o(N)$?

The connection to unit fractions: $\frac1a + \frac1b$ is a unit fraction iff $a + b \mid ab$.
Wouter van Doorn proved that $|A| \ge (25/28 + o(1))N$ forces some $a \ne b$ in $A$ with
$a + b \mid ab$ (improved on the forum to $0.7769$). Computations on the forum (OEIS A384927)
give maximal densities around $0.70$ for $N \le 5000$. Status at the source: open.

## Formalization notes

* `IsAdmissible k A`: no two distinct `a, b ∈ A` satisfy `a + b ∣ k * a * b`. The first
  question is about `k = 1`, the second about `k = 2`.
* The odd numbers in `{1, …, N}` are admissible for `k = 1` (`a + b` is even, `ab` is odd),
  giving about `N / 2` elements. "Substantially more than the odd numbers" is read in the
  standard way: there is a constant `c > 0` such that, for all large `N`, some admissible
  `A ⊆ {1, …, N}` has `|A| ≥ (1/2 + c) N`. `main` states this affirmative answer to the
  first question; a disproof of `main` is the negative answer.
* The second question ("must `|A| = o(N)` when `a + b ∤ 2ab`?") is NOT conjoined to `main`,
  on purpose. As noted on the source's forum (Adenwalla), an affirmative answer to the first
  question implies a negative answer to the second: if `A ⊆ {1, …, 2N}` is admissible for
  `k = 1` with `|A| ≥ (1/2 + c) · 2N`, then `A` has at least `2cN` even elements `2a`, and the
  halves `a` form a `k = 2` admissible subset of `{1, …, N}` (since `2a + 2b ∣ 4ab` iff
  `a + b ∣ 2ab`) of size `≥ 2cN`. So "yes ∧ yes" is refutable and would be a wrong
  statement. The second question deserves its own statement:
  `Tendsto (fun N => (max size of a k = 2 admissible A ⊆ {1, …, N}) / N) atTop (𝓝 0)`.
-/

namespace OMA.S_erdos_327

open Filter

/-- `A` has no two distinct elements `a, b` with `a + b ∣ k * a * b`. -/
def IsAdmissible (k : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ (a + b ∣ k * a * b)

/-- First question of Erdős Problem 327, affirmative answer: admissible subsets of
`{1, …, N}` (for `a + b ∤ ab`) can be substantially larger than the odd numbers. -/
theorem main :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsAdmissible 1 A ∧
        (1 / 2 + c) * (N : ℝ) ≤ (A.card : ℝ) := by
  sorry

end OMA.S_erdos_327
