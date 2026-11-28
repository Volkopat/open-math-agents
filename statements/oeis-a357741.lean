import Mathlib

/-!
# A357741: Semiprimes divisible by their index in the sequence of semiprimes

Source: https://oeis.org/A357741

Conjecture (OEIS A357741):
`a(18) > 10^17`; equivalently, there are at most `17` semiprimes `k ≤ 10^17` that are
divisible by their `1`-based index in the sequence of semiprimes (OEIS A001358).

Conventions:
- Offset: `1`; first terms: `4, 6, 9, 21, 33, 129, 159, ...`.
- The `1`-based index of a semiprime `k` in A001358 is
  `Set.ncard {m : ℕ | m ≤ k ∧ IsSemiprime m}`.
-/

namespace OMA.S_oeis_a357741

/-- Predicate stating that `m` is a semiprime (product of two primes, OEIS A001358). -/
def IsSemiprime (m : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ m = p * q

/-- The `1`-based index of a semiprime `k` in the sequence of semiprimes (OEIS A001358). -/
noncomputable def semiprimeIndex (k : ℕ) : ℕ :=
  Set.ncard {m : ℕ | m ≤ k ∧ IsSemiprime m}

/-- The set of semiprimes divisible by their `1`-based index (OEIS A357741). -/
def S : Set ℕ :=
  {k : ℕ | IsSemiprime k ∧ semiprimeIndex k ∣ k}

/-- Conjecture: `a(18) > 10^17` (at most `17` terms of A357741 are `≤ 10^17`). -/
theorem main :
    Set.ncard {k : ℕ | k ∈ S ∧ k ≤ 10 ^ 17} ≤ 17 := by
  sorry

end OMA.S_oeis_a357741
