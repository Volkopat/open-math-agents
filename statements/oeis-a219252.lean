import Mathlib

/-!
# A219252: smallest prime `q` with `2n + 1 = p + 4q` for an odd prime `p`

Source: https://oeis.org/A219252
Credit: @Lenqth

A219252(n) is the smallest prime `q` such that `2n + 1 = p + 4q` for some odd prime `p`, or `0` if
there is none (offset 1). Since `2n + 1` is odd and `4q` is even, any prime `p` with
`2n + 1 = p + 4q` is automatically odd, so the condition "odd" can be dropped.

Formalizes the conjecture in the comments of A219252: except `m = 77`, every odd number `m > 9`
is of the form `p + 4q` with `p` and `q` prime. (The entry records `a(38) = 0`, i.e. `77` is not of
this form.)
-/

namespace OMA.S_oeis_a219252

/-- The odd numbers `m > 9` that are not of the form `p + 4q` with `p, q` prime are exactly `77`. -/
theorem main :
    {m : ℕ | Odd m ∧ 9 < m ∧ ¬ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ m = p + 4 * q} = {77} := by
  sorry

end OMA.S_oeis_a219252
