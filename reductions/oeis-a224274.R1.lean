import OMAStatements.S_oeis_a224274
import Mathlib

/-! The conjecture recorded at OEIS A224274 is an equivalence: for `n ≥ 2`,
`a(n) = binomial(4n, n) / 4 ≡ 1 (mod n^3)` if and only if `n` is an odd prime.

The forward direction (every odd prime satisfies the congruence) is classical: since
`binomial(4p, p) = 4 * binomial(4p - 1, p - 1)`, it says `binomial(4p - 1, p - 1) ≡ 1 (mod p^3)`,
a case of the theorems of Wolstenholme, Ljunggren and Jacobsthal on `binomial(ap, bp)`
modulo `p^3` for `p ≥ 5`; for `p = 3` it is the computation `a(3) = 55 ≡ 1 (mod 27)`.
It is `H1`.

The backward direction (the congruence forces `n` to be an odd prime), a converse of
Wolstenholme type, is the open part of the conjecture. It is `H2`. -/

namespace OMA.R_oeis_a224274_R1

/-- The classical direction: every odd prime `p` satisfies `a(p) ≡ 1 (mod p^3)`. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → Odd p → OMA.S_oeis_a224274.a p ≡ 1 [MOD p ^ 3]

/-- The open direction: for `n ≥ 2`, `a(n) ≡ 1 (mod n^3)` forces `n` to be an odd prime. -/
def H2 : Prop :=
  ∀ n : ℕ, 2 ≤ n → OMA.S_oeis_a224274.a n ≡ 1 [MOD n ^ 3] → n.Prime ∧ Odd n

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a224274.main := by
  intro h1 h2 n hn
  exact ⟨h2 n hn, fun h => h1 n h.1 h.2⟩

end OMA.R_oeis_a224274_R1
