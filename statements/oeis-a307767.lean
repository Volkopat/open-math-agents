import Mathlib

/-!
# A307767: non-residue pseudoprimes and the least quadratic nonresidue

Source: https://oeis.org/A307767
Credit: @avivorly

A307767 (Thomas Ordowski) lists the non-residue pseudoprimes: odd composite numbers `n` such that
`b(n)^((n-1)/2) == -1 (mod n)`, where the base `b(n) = A020649(n)`.

Definition (A020649, offset 3): `A020649(n)` is the least quadratic nonresidue modulo `n` (with `n >= 3`), that is, the
smallest `q` such that the congruence `x^2 == q (mod n)` has no solution `0 <= x < n`.

Conjecture (Thomas Ordowski, in the entry): If `2^((n-1)/2) == -1 (mod n)`, then `b(n) = 2`, where `b(n)` as above.
This is true for odd primes `n`; is it for odd composites `n`? If so, then all composite numbers `n` such that
`2^((n-1)/2) == -1 (mod n)` are in this sequence.

Conventions:
- `A020649 n` is the `sInf` of the set of `q : ℕ` such that no `x < n` has `x ^ 2 ≡ q [MOD n]`: a literal
  transcription of the definition. For `n ≥ 3` the set is nonempty (`x` and `n - x` have the same square, and
  `1 ≠ n - 1`, so squaring is not injective, hence not onto, on the residues mod `n`), so the `sInf` is its least
  element. A020649 starts at `n = 3` (for `n = 1, 2` every `q` is a square mod `n`, and `sInf ∅ = 0`), so `main`
  assumes `3 ≤ n`.
- The congruence `2^((n-1)/2) == -1 (mod n)` is read in `ZMod n`, with the exponent `(n - 1) / 2` in `ℕ`. `n` is odd,
  as the integer exponent `(n-1)/2` and the comment (odd primes, odd composites) require; for `n ≥ 3` this is no
  restriction, since an even `n` never divides the odd number `2^k + 1`.
- `InA307767 n` is the definition of the sequence: `n` is odd and composite (`1 < n` and `n` not prime), and
  `b(n)^((n-1)/2) == -1 (mod n)` in `ZMod n`, with `b(n) = A020649 n`.
- `main` states both claims of the comment: every odd `n ≥ 3` with `2^((n-1)/2) == -1 (mod n)`, prime or composite,
  has `A020649 n = 2`; and every such composite `n` is a term of A307767.
-/

namespace OMA.S_oeis_a307767

/-- `A020649 n`, the least quadratic nonresidue modulo `n` (for `n ≥ 3`): the smallest `q` such that the congruence
`x ^ 2 ≡ q [MOD n]` has no solution `0 ≤ x < n`. -/
noncomputable def A020649 (n : ℕ) : ℕ :=
  sInf {q : ℕ | ¬ ∃ x : ℕ, x < n ∧ x ^ 2 ≡ q [MOD n]}

/-- `n` is a term of A307767 (a non-residue pseudoprime): `n` is an odd composite number with
`A020649 n ^ ((n - 1) / 2) ≡ -1 (mod n)`. -/
def InA307767 (n : ℕ) : Prop :=
  Odd n ∧ 1 < n ∧ ¬ n.Prime ∧ (A020649 n : ZMod n) ^ ((n - 1) / 2) = -1

theorem main :
    ∀ n : ℕ, 3 ≤ n → Odd n → (2 : ZMod n) ^ ((n - 1) / 2) = -1 →
      A020649 n = 2 ∧ (¬ n.Prime → InA307767 n) := by
  sorry

end OMA.S_oeis_a307767
