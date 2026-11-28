import Mathlib

/-!
# Primes of the form $ax + by$

Source: https://arxiv.org/abs/2506.03620
Credit: @SulkBash

## The problem (as the source states it)

For two coprime positive integers $a, b$, let $T(a,b) = \{ax + by : x, y \in \mathbb{Z}_{\ge 0}\}$
and let $s(a,b) = ab - a - b$. All integers greater than $s(a,b)$ are in $T(a,b)$. Let
$\pi(a,b)$ be the number of primes in $T(a,b)$ which are less than or equal to $s(a,b)$.

The paper proves $\pi(a,b) > 0.005\, s(a,b)/\log s(a,b)$ when $b > a \ge 3$ and
$\gcd(a,b) = 1$, and conjectures that
$$\frac{13}{66}\,\pi(s(a,b)) \le \pi(a,b) \le \frac12\,\pi(s(a,b))$$
for all $b > a \ge 3$ with $\gcd(a,b) = 1$, where $\pi(x)$ is the prime-counting function.

## Formalization notes

* `T a b` is `{m | ∃ x y : ℕ, m = a * x + b * y}`, with `x, y ≥ 0` as in the source.
* `s(a,b)` is `a * b - a - b` in `ℕ`. For `b > a ≥ 3` we have `ab ≥ a + b`, so the truncated
  subtraction is exact.
* `piAB a b` is the `Set.ncard` of the primes `p ≤ s(a,b)` lying in `T a b`. This set is finite,
  being bounded by `s(a,b)`, so `ncard` is its genuine size.
* $\pi(x)$ is `Nat.primeCounting`, the number of primes `≤ x`.
* The two inequalities are stated in `ℝ`, with the constants `13 / 66` and `1 / 2` from the
  source.
-/

namespace OMA.S_arxiv_2506_03620

/-- $T(a,b) = \{ax + by : x, y \ge 0\}$. -/
def T (a b : ℕ) : Set ℕ := {m | ∃ x y : ℕ, m = a * x + b * y}

/-- $\pi(a,b)$: the number of primes $p \le s(a,b) = ab - a - b$ that lie in $T(a,b)$. -/
noncomputable def piAB (a b : ℕ) : ℕ :=
  {p : ℕ | p.Prime ∧ p ≤ a * b - a - b ∧ p ∈ T a b}.ncard

/-- For all coprime `b > a ≥ 3`, `(13/66) π(s(a,b)) ≤ π(a,b) ≤ (1/2) π(s(a,b))`. -/
theorem main :
    ∀ a b : ℕ, 3 ≤ a → a < b → Nat.Coprime a b →
      (13 / 66 : ℝ) * (Nat.primeCounting (a * b - a - b) : ℝ) ≤ (piAB a b : ℝ) ∧
        (piAB a b : ℝ) ≤ (1 / 2 : ℝ) * (Nat.primeCounting (a * b - a - b) : ℝ) := by
  sorry

end OMA.S_arxiv_2506_03620
