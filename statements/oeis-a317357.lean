import Mathlib

/-!
# A317357: a(n) is the smallest composite k > n such that 1^(k-1) + 2^(k-1) + ... + n^(k-1) == n (mod k).

Source: https://oeis.org/A317357
Credit: @azmiozgen

Conjecture (from the entry, a consequence of the Agoh-Giuga conjecture): a(n) > n + 1.

Formalization notes:
* a(n) > n + 1 says that k = n + 1 is not a solution when it is composite.
* Stated for every n ≥ 1 with n + 1 composite: 1^n + 2^n + ... + n^n is not ≡ n (mod n + 1). (This is
  the Agoh-Giuga conjecture for the modulus n + 1.)
* Controls (computed): no composite n + 1 with n < 3000 satisfies the congruence.
-/

namespace OMA.S_oeis_a317357



/-- The conjecture of the entry. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → ¬ (n + 1).Prime → 2 ≤ n →
      ¬ (∑ i ∈ Finset.Icc 1 n, i ^ n) ≡ n [MOD n + 1] := by
  sorry

end OMA.S_oeis_a317357
