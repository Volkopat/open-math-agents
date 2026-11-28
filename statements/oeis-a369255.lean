import Mathlib

/-!
# A369255: Parity of A140773, where A140773 is the inverse Möbius transform of A038548.

Source: https://oeis.org/A369255
Credit: @agchua

Formula lines of A369255 (Antti Karttunen, Nov 14 2024):
  Following convolution formulas have been conjectured for this sequence by Sequence Machine,
  with both computing the first 2^20 terms correctly:
  a(n) = Sum_{d|n} A007875(d)*A219009(n/d).
  a(n) = Sum_{d|n} A140773(d)*A355837(n/d).

All sequences involved have offset 1, so both identities are stated for all n >= 1.
Definitions follow the literal OEIS name lines:
- A038548(n) is the number of divisors d of n with d <= sqrt(n), i.e. d * d <= n.
- A140773(n) is the inverse Möbius transform Sum_{d|n} A038548(d).
- A369255(n) = A140773(n) mod 2.
- A007875(n) is the number of ways to write n = p * q with p <= q and gcd(p, q) = 1.
- A219009(n) is the coefficient of n^(-s) in zeta(4s)/zeta(s), i.e., the Möbius transform of
  the characteristic function of fourth powers.
- A322327(n) = A005361(n) * A034444(n) = Prod_{p|n} (2 * v_p(n)), and A355837 is its
  Dirichlet inverse.
-/

namespace OMA.S_oeis_a369255

/-- A038548(n): number of divisors d of n with d <= sqrt(n) (i.e. d * d <= n). -/
def a038548 (n : ℕ) : ℕ :=
  (n.divisors.filter (fun d => d * d ≤ n)).card

/-- A140773(n): inverse Möbius transform of A038548. -/
def a140773 (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, a038548 d

/-- A369255(n): parity of A140773(n). -/
def a (n : ℕ) : ℕ :=
  a140773 n % 2

/-- A007875(n): number of ways of writing n = p * q with p <= q and gcd(p, q) = 1. -/
def a007875 (n : ℕ) : ℕ :=
  (n.divisors.filter (fun d => d ≤ n / d ∧ Nat.Coprime d (n / d))).card

open scoped Classical in
/-- A219009(n): coefficients of zeta(4s)/zeta(s), i.e., the Möbius transform of the
characteristic function of fourth powers. -/
noncomputable def a219009 (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, (if ∃ m : ℕ, m ^ 4 = d then (1 : ℤ) else 0) *
    ArithmeticFunction.moebius (n / d)

/-- A322327(n) = A005361(n) * A034444(n), multiplicative with a(p^e) = 2 * e. -/
noncomputable def a322327 (n : ℕ) : ℕ :=
  if n = 0 then 0 else ∏ p ∈ n.primeFactors, (2 * n.factorization p)

/-- A355837(n): Dirichlet inverse of A322327. -/
noncomputable def a355837 (n : ℕ) : ℤ :=
  if h0 : n = 0 then 0
  else if n = 1 then 1
  else - ∑ d ∈ (n.divisors.erase n).attach,
    (a322327 (n / d.1) : ℤ) * a355837 d.1
termination_by n
decreasing_by
  have hd := d.2
  rw [Finset.mem_erase, Nat.mem_divisors] at hd
  exact Nat.lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd.2.1) hd.1

/-- Both conjectured convolution formulas from A369255 (Antti Karttunen, Nov 14 2024). -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (a n : ℤ) = ∑ d ∈ n.divisors, (a007875 d : ℤ) * a219009 (n / d) ∧
    (a n : ℤ) = ∑ d ∈ n.divisors, (a140773 d : ℤ) * a355837 (n / d) := by
  sorry

end OMA.S_oeis_a369255
