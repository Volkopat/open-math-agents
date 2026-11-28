import OMAStatements.S_oeis_a366029
import Mathlib

/-! The conjecture recorded at OEIS A366029 is an equivalence. One direction is provable: if
2^k - 1 is prime then k is prime, Fermat's little theorem gives the congruence modulo 2^k - 1, and
the binomial expansion of (k - 1)^(2j) modulo k^2 together with k | 2^k - 2 gives it modulo k^2;
if k is a Fermat number F = 2^(2^m) + 1, prime or not, then F divides 2^(F - 1) - 1, which gives
both congruences again. The other direction (the divisibility forces 2^k - 1 to be prime or k to
be a Fermat number) is the open part. -/

namespace OMA.R_oeis_a366029_R1

/-- Mersenne exponents and Fermat numbers satisfy the divisibility. -/
def H1 : Prop :=
  ∀ k : ℕ, 1 < k → ((2 ^ k - 1).Prime ∨ ∃ m : ℕ, k = 2 ^ (2 ^ m) + 1) →
    (2 ^ k - 1) * k ^ 2 ∣ (k - 1) ^ (2 ^ k - 2) - 1

/-- The open direction: the divisibility characterises these exponents. -/
def H2 : Prop :=
  ∀ k : ℕ, 1 < k → (2 ^ k - 1) * k ^ 2 ∣ (k - 1) ^ (2 ^ k - 2) - 1 →
    ((2 ^ k - 1).Prime ∨ ∃ m : ℕ, k = 2 ^ (2 ^ m) + 1)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a366029.main := by
  intro h1 h2 k hk
  exact ⟨h2 k hk, h1 k hk⟩

end OMA.R_oeis_a366029_R1
