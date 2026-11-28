import Mathlib

/-!
# A176997: Integers k such that 2^(k-1) == 1 (mod k)

Source: https://oeis.org/A176997
Credit: @xor2k

Formalizes the following comment of the entry (Max Alekseyev, Sep 22 2016), both parts:
The union of {1}, the odd primes, and the Fermat pseudoprimes, i.e., {1} U A065091 U A001567.
Also, the union of A006005 and A001567 (conjectured by Alois P. Heinz, Dec 10 2010).

Conventions:
* A176997 is the set of positive integers k (offset 1) with `2^(k-1) ≡ 1 [MOD k]`; for k = 1
  this holds since everything is congruent mod 1.
* A065091 (odd primes): primes p with `Odd p`.
* A006005 (the odd prime numbers together with 1): odd k with k = 1 or k prime.
* A001567 (Fermat pseudoprimes to base 2: composite k with 2^(k-1) ≡ 1 mod k) is Mathlib's
  `Nat.FermatPsp k 2`, i.e. `k ∣ 2^(k-1) - 1`, k not prime and 1 < k.
-/

namespace OMA.S_oeis_a176997

/-- A176997: positive integers `k` with `2^(k-1) ≡ 1 (mod k)`. -/
def A176997 : Set ℕ := {k | 0 < k ∧ 2 ^ (k - 1) ≡ 1 [MOD k]}

/-- A065091: the odd primes. -/
def A065091 : Set ℕ := {p | p.Prime ∧ Odd p}

/-- A006005: the odd prime numbers together with 1. -/
def A006005 : Set ℕ := {k | Odd k ∧ (k = 1 ∨ k.Prime)}

/-- A001567: Fermat pseudoprimes to base 2. -/
def A001567 : Set ℕ := {k | Nat.FermatPsp k 2}

/-- A176997 equals {1} ∪ A065091 ∪ A001567, and also equals A006005 ∪ A001567. -/
theorem main :
    A176997 = {1} ∪ A065091 ∪ A001567 ∧ A176997 = A006005 ∪ A001567 := by
  sorry

end OMA.S_oeis_a176997
