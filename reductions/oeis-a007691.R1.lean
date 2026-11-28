import OMAStatements.S_oeis_a007691
import Mathlib

-- Reduction oeis-a007691.R1 of OEIS A007691 (infinitely many multiply-perfect numbers).
-- Credit: @marcusbuffett

/-!
# Multiply-perfect numbers from Mersenne primes: Euclid's theorem, and the open rest

* `H1` (classical, Euclid, Elements IX.36): if `2 ^ (k + 1) - 1` is prime then
  `2 ^ k (2 ^ (k + 1) - 1)` is perfect. By multiplicativity of `σ` on the coprime factors,
  `σ = (2 ^ (k + 1) - 1) · 2 ^ (k + 1)`, twice the number.
* `H2` (open): there are infinitely many Mersenne primes.

A perfect number `n` has `σ(n) = 2n`, so `n ∣ σ(n)`, and `2 ^ k (2 ^ (k + 1) - 1) ≥ 2 ^ k > k`
makes these numbers unbounded. This is the classical route, not progress on the conjecture:
the infinitude of Mersenne primes in `H2` is open.
-/

namespace OMA.R_oeis_a007691_R1

open ArithmeticFunction

/-- Euclid: `2 ^ k (2 ^ (k + 1) - 1)` is perfect when `2 ^ (k + 1) - 1` is prime. -/
def H1 : Prop :=
  ∀ k : ℕ, (2 ^ (k + 1) - 1).Prime → Nat.Perfect (2 ^ k * (2 ^ (k + 1) - 1))

/-- The open part: infinitely many Mersenne primes. -/
def H2 : Prop :=
  {k : ℕ | (2 ^ (k + 1) - 1).Prime}.Infinite

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a007691.main := by
  intro h1 h2
  apply Set.infinite_of_forall_exists_gt
  intro B
  obtain ⟨k, hk, hBk⟩ := h2.exists_gt B
  have hM : (2 ^ (k + 1) - 1).Prime := hk
  have hperf := h1 k hM
  have hpos := hperf.2
  have hsig : sigma 1 (2 ^ k * (2 ^ (k + 1) - 1)) = 2 * (2 ^ k * (2 ^ (k + 1) - 1)) := by
    rw [sigma_one_apply]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul hpos).mp hperf
  refine ⟨2 ^ k * (2 ^ (k + 1) - 1), ⟨hpos, ?_⟩, ?_⟩
  · rw [hsig]; exact dvd_mul_left _ _
  · have h1 : k < 2 ^ k := Nat.lt_two_pow_self
    have h2 : 2 ^ k ≤ 2 ^ k * (2 ^ (k + 1) - 1) := Nat.le_mul_of_pos_right _ hM.pos
    omega

end OMA.R_oeis_a007691_R1
