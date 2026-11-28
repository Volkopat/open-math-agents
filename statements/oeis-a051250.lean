import Mathlib

/-!
# A051250: Numbers whose reduced residue system consists of 1 and prime powers only

Source: https://oeis.org/A051250
Credit: @niclorusso

Conjecture (Reinhard Zumkeller, Oct 27 2010, in the comments of A051250): the sequence is finite
and 60 is the largest term, empirically verified up to 10^7.

Conventions:
* n >= 1 is a term when every k with 1 < k < n and gcd(k, n) = 1 is a prime power (`IsPrimePow`,
  i.e. p^e with p prime and e >= 1); the residue 1 is always allowed.
* "finite and 60 is the largest term" is stated with `IsGreatest` (which also gives finiteness).
-/

namespace OMA.S_oeis_a051250

/-- `n` is a term of A051250. -/
def IsTerm (n : ℕ) : Prop :=
  0 < n ∧ ∀ k : ℕ, 1 < k → k < n → Nat.Coprime k n → IsPrimePow k

/-- Zumkeller's conjecture on A051250: `60` is the largest term. -/
theorem main : IsGreatest {n : ℕ | IsTerm n} 60 := by
  sorry

end OMA.S_oeis_a051250
