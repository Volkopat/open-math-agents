import Mathlib

/-!
# OEIS A040027: Gould numbers via alternating factorials

Source: https://oeis.org/A040027
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Yanev, 2021): `a(n) = ∑_{k=0}^{n} A058006(k) · A048993(n+1, k+1)`, where `a` is the
Gould numbers `1, 1, 3, 9, 31, 121, …`, `A058006(k) = ∑_{i=0}^{k} (-1)^i i!` (alternating
factorials) and `A048993(n, k) = S(n, k)` (Stirling numbers of the second kind).

Conventions:
* `a` is given by the recurrence in the entry: `a(0) = a(1) = 1` and
  `a(n) = n + ∑_{j=1}^{n-1} C(n, j+1) a(j)` for `n > 1` (this reproduces the listed terms).
* `S(n, k)` is `Nat.stirlingSecond n k`.
-/

namespace OMA.S_oeis_a040027

/-- The Gould numbers, via the recurrence of the entry. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => (n + 2 : ℤ) + ∑ j : Fin (n + 2),
      if (j : ℕ) = 0 then 0 else ((n + 2).choose (j + 1) : ℤ) * a j
decreasing_by exact j.isLt

/-- Alternating factorials `A058006(k) = ∑_{i=0}^{k} (-1)^i i!`. -/
def altFact (k : ℕ) : ℤ := ∑ i ∈ Finset.range (k + 1), (-1 : ℤ) ^ i * (i.factorial : ℤ)

/-- `a(n) = ∑_{k=0}^{n} A058006(k) · S(n+1, k+1)`. -/
theorem main : ∀ n : ℕ,
    a n = ∑ k ∈ Finset.range (n + 1), altFact k * (Nat.stirlingSecond (n + 1) (k + 1) : ℤ) := by
  sorry

end OMA.S_oeis_a040027
