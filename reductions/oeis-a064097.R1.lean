import OMAStatements.S_oeis_a064097
import Mathlib

-- Reduction oeis-a064097.R1 of OEIS A064097 (bounds for a quasi-logarithm)
-- Credit: @marcusbuffett

/-!
# A064097: the lower bound `⌊log₂ n⌋ ≤ a(n)`, and the open upper bound

`a(1) = 0`, `a(p) = 1 + a(p - 1)` for primes `p`, `a(nm) = a(n) + a(m)` for `n, m > 1`. The
conjecture is `⌊log₂ n⌋ ≤ a(n) < (5/2) log n` for `n > 1`. This splits off the lower bound,
which is elementary; the upper bound is the open part.

* `H1` (proved): `⌊log₂ n⌋ ≤ a(n)` for `n > 1`. Proof: `n ≤ 2^{a(n)}` for `n ≥ 1` by strong
  induction (`2^{a(p)} = 2 · 2^{a(p-1)} ≥ 2(p - 1) ≥ p` for primes, multiplicativity of
  `2^{a(·)}` on products of factors `> 1`), so `n < 2^{a(n)+1}`.
* `H2`: `a(n) < (5/2) log n` for `n > 1`. This is the open part of the conjecture.
-/

namespace OMA.R_oeis_a064097_R1

open Real

/-- The lower bound. -/
def H1 : Prop :=
  ∀ a : ℕ → ℕ, a 1 = 0 → (∀ p : ℕ, p.Prime → a p = 1 + a (p - 1)) →
    (∀ n m : ℕ, 1 < n → 1 < m → a (n * m) = a n + a m) →
    ∀ n : ℕ, 1 < n → Nat.log 2 n ≤ a n

/-- The open upper bound. -/
def H2 : Prop :=
  ∀ a : ℕ → ℕ, a 1 = 0 → (∀ p : ℕ, p.Prime → a p = 1 + a (p - 1)) →
    (∀ n m : ℕ, 1 < n → 1 < m → a (n * m) = a n + a m) →
    ∀ n : ℕ, 1 < n → (a n : ℝ) < 5 / 2 * log n

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a064097.main := by
  intro h1 h2 a h0 hp hm n hn
  exact ⟨h1 a h0 hp hm n hn, h2 a h0 hp hm n hn⟩

end OMA.R_oeis_a064097_R1
