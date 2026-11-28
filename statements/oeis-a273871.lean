import Mathlib

/-!
# A273871: primes p such that (4^(p-1) - 1) == 0 mod ((p-1)^2 + 1)

Source: https://oeis.org/A273871
Credit: @xor2k

Formalizes both OEIS A273871 conjectures:
Conjecture 1: also primes p such that ((4^k)^(p-1)-1) == 0 mod ((p-1)^2+1) for all k >= 0.
Conjecture 2: supersequence of Fermat primes (A019434).

Conventions:
* `InSeq p` is membership in A273871: `p` is prime and `(p - 1) ^ 2 + 1` divides `4 ^ (p - 1) - 1`.
  For prime `p` all subtractions are exact (`p ≥ 2`, `4 ^ k ≥ 1`), so natural subtraction is harmless.
* Conjecture 1 is read as an equality of sets: a prime `p` is in A273871 iff
  `(p - 1) ^ 2 + 1` divides `(4 ^ k) ^ (p - 1) - 1` for every `k : ℕ`.
* A019434 (Fermat primes, primes of the form `2 ^ (2 ^ k) + 1`, `k ≥ 0`) is expressed with Mathlib's
  `Nat.fermatNumber m = 2 ^ (2 ^ m) + 1`; conjecture 2 says every prime Fermat number is in A273871.
-/

namespace OMA.S_oeis_a273871

/-- Membership in A273871: `p` is prime and `(p - 1) ^ 2 + 1 ∣ 4 ^ (p - 1) - 1`. -/
def InSeq (p : ℕ) : Prop :=
  p.Prime ∧ (p - 1) ^ 2 + 1 ∣ 4 ^ (p - 1) - 1

/-- Conjecture 1 (characterization with all powers `4 ^ k`) and conjecture 2 (Fermat primes are
terms). -/
theorem main :
    (∀ p : ℕ, InSeq p ↔ (p.Prime ∧ ∀ k : ℕ, (p - 1) ^ 2 + 1 ∣ (4 ^ k) ^ (p - 1) - 1)) ∧
    (∀ m : ℕ, (Nat.fermatNumber m).Prime → InSeq (Nat.fermatNumber m)) := by
  sorry

end OMA.S_oeis_a273871
