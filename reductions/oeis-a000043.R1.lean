import OMAStatements.S_oeis_a000043
import Mathlib

/-! The two conjectures recorded at OEIS A000043 are equivalences. Their forward directions are
provable: if 2^k - 1 is prime then k is prime, Fermat's little theorem gives the congruence
modulo 2^k - 1, and the binomial expansion of (k - 1)^(2j) modulo k^2 together with
k | 2^k - 2 gives it modulo k^2; if k is a Fermat number F = 2^(2^m) + 1, prime or not, then F
divides 2^(F - 1) - 1, which gives both congruences again. The backward directions (the
congruence forces 2^k - 1 to be prime or k to be a Fermat number) are the open part. -/

namespace OMA.R_oeis_a000043_R1

/-- The forward directions: Mersenne exponents and Fermat numbers satisfy the congruences. -/
def H1 : Prop :=
  (∀ k : ℕ, 1 < k → ((2 ^ k - 1).Prime ∨ ∃ m : ℕ, k = 2 ^ (2 ^ m) + 1) →
      (k - 1) ^ (2 ^ k - 2) ≡ 1 [MOD (2 ^ k - 1) * k ^ 2]) ∧
    (∀ p : ℕ, p.Prime → ((2 ^ p - 1).Prime ∨ ∃ m : ℕ, p = 2 ^ (2 ^ m) + 1) →
      (p - 1) ^ (2 ^ p - 2) ≡ 1 [MOD 2 ^ p - 1])

/-- The open backward directions: the congruences characterise these exponents. -/
def H2 : Prop :=
  (∀ k : ℕ, 1 < k → (k - 1) ^ (2 ^ k - 2) ≡ 1 [MOD (2 ^ k - 1) * k ^ 2] →
      ((2 ^ k - 1).Prime ∨ ∃ m : ℕ, k = 2 ^ (2 ^ m) + 1)) ∧
    (∀ p : ℕ, p.Prime → (p - 1) ^ (2 ^ p - 2) ≡ 1 [MOD 2 ^ p - 1] →
      ((2 ^ p - 1).Prime ∨ ∃ m : ℕ, p = 2 ^ (2 ^ m) + 1))

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a000043.main := by
  intro h1 h2
  exact ⟨fun k hk => ⟨h1.1 k hk, h2.1 k hk⟩, fun p hp => ⟨h1.2 p hp, h2.2 p hp⟩⟩

end OMA.R_oeis_a000043_R1
