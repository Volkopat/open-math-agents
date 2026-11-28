import Mathlib

/-!
# A263429: Smallest prime p such that binomial(2*p-1, p-1) == 1 (mod p^n), or 0 if no such p exists.

Source: https://oeis.org/A263429
Credit: @prasledi

Conjecture (in the COMMENTS of A263429, attributed to McIntosh, 1995, p. 387):
a(n) = 0 for n > 4.

Formalization notes:
* By definition a(n) = 0 exactly when no prime p satisfies
  binomial(2p-1, p-1) == 1 (mod p^n). So the conjecture says: for every n > 4 and every
  prime p, binomial(2p-1, p-1) is not congruent to 1 modulo p^n. This is stated directly,
  without introducing the minimum.
* For a prime p we have p >= 2, so the natural-number subtractions 2 * p - 1 and p - 1 are the
  ordinary ones.
* Known terms: a(1) = 2, a(2) = 3, a(3) = 5, a(4) = 16843 (a Wolstenholme prime).
-/

namespace OMA.S_oeis_a263429

/-- McIntosh's conjecture, as recorded in A263429: no prime `p` has
`binomial(2p-1, p-1) ≡ 1 (mod p^n)` for any `n > 4`. -/
theorem main :
    ∀ n : ℕ, 4 < n → ∀ p : ℕ, p.Prime → ¬ Nat.choose (2 * p - 1) (p - 1) ≡ 1 [MOD p ^ n] := by
  sorry

end OMA.S_oeis_a263429
