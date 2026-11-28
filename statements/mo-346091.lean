import Mathlib

/-!
# Sum of two `n`-th powers, of two `m`-th powers, but not of two `mn`-th powers

Source: https://mathoverflow.net/questions/346091 (CC BY-SA 4.0).

Let `m` and `n` be coprime, and let `S_n` be the set of integers that are a sum of two `n`-th
powers of integers (for example `7 ∈ S_3`, as `7 = 2^3 + (-1)^3`); define `S_m`, `S_{mn}` in the
same way. The question: is `(S_n ∩ S_m) \ S_{mn}` infinite?

The asker proved it for `n = 2`, `m = 3` (by an elementary construction). The answer on the page
gives heuristics but no proof; it suggests that for `min(m, n) ≥ 5` one may expect all solutions
of `x^m + y^m = u^n + v^n` to come from `S_{mn}`, which would make the answer negative there.
We state the question as asked, for all coprime `m, n`; a disproof answers it negatively.

Formalization notes:
* `S k` is `{x : ℤ | ∃ a b : ℤ, a ^ k + b ^ k = x}`; negative bases are allowed, as in the
  source's example.
* The question presupposes `m, n ≥ 2`: for `n = 1` every integer lies in `S_1`, so the set
  `(S_1 ∩ S_m) \ S_m` is empty.
-/

namespace OMA.S_mo_346091

/-- The integers that are a sum of two `k`-th powers of integers. -/
def S (k : ℕ) : Set ℤ :=
  {x : ℤ | ∃ a b : ℤ, a ^ k + b ^ k = x}

/-- For coprime `m, n ≥ 2`, infinitely many integers are a sum of two `n`-th powers and a sum of
two `m`-th powers without being a sum of two `mn`-th powers. -/
theorem main : ∀ m n : ℕ, 2 ≤ m → 2 ≤ n → Nat.Coprime m n →
    ((S n ∩ S m) \ S (m * n)).Infinite := by
  sorry

end OMA.S_mo_346091
