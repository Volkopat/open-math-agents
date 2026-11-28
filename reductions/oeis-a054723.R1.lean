import OMAStatements.S_oeis_a054723
import Mathlib

-- Reduction oeis-a054723.R1 of OEIS A054723 (infinitely many prime exponents with composite
-- Mersenne numbers).
-- Credit: @marcusbuffett

/-!
# Composite Mersenne numbers from Sophie Germain primes: Euler's criterion, and the open rest

* `H1` (classical, Euler 1750 and Lagrange 1775): for a prime `p ≡ 3 (mod 4)`, `2p + 1` is prime
  if and only if `2p + 1 ∣ 2 ^ p - 1`. Forward: `q = 2p + 1 ≡ 7 (mod 8)`, so `2` is a quadratic
  residue modulo `q` and Euler's criterion gives `2 ^ p = 2 ^ ((q - 1) / 2) ≡ 1 (mod q)`.
  Backward: a prime factor `r` of `2p + 1` divides `2 ^ p - 1`, so the order of `2` modulo `r`
  is `p`, `2p ∣ r - 1`, and `r = 2p + 1`.
* `H2` (open): there are infinitely many Sophie Germain primes `p ≡ 3 (mod 4)`.

With `H1`, every such `p > 3` gives a proper factor `2p + 1 < 2 ^ p - 1`, so `2 ^ p - 1` is
composite. This is the textbook route (Guy, Unsolved Problems in Number Theory, A3), not
progress on the conjecture: the infinitude in `H2` is open.
-/

namespace OMA.R_oeis_a054723_R1

/-- Euler–Lagrange: for a prime `p ≡ 3 (mod 4)`, `2p + 1` is prime iff it divides `2 ^ p - 1`. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → p % 4 = 3 → ((2 * p + 1).Prime ↔ 2 * p + 1 ∣ 2 ^ p - 1)

/-- The open part: infinitely many Sophie Germain primes `p ≡ 3 (mod 4)`. -/
def H2 : Prop :=
  {p : ℕ | p.Prime ∧ p % 4 = 3 ∧ (2 * p + 1).Prime}.Infinite

lemma two_mul_add_lt_pow (n : ℕ) (hn : 7 ≤ n) : 2 * n + 2 < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a054723.main := by
  intro h1 h2
  refine (h2.diff (Set.finite_singleton 3)).mono ?_
  rintro p ⟨⟨hp, hp4, hq⟩, hp3⟩
  have hp3' : p ≠ 3 := hp3
  refine ⟨hp, fun hM => ?_⟩
  have hd := (h1 p hp hp4).mp hq
  have heq := (Nat.prime_dvd_prime_iff_eq hq hM).mp hd
  have h7 : 7 ≤ p := by
    have := hp.two_le
    omega
  have := two_mul_add_lt_pow p h7
  omega

end OMA.R_oeis_a054723_R1
