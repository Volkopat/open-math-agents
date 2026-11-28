import Mathlib

/-!
# Are the multiplicative orders of 2 and 3 coprime for infinitely many primes?

Source: https://mathoverflow.net/questions/497324 (2025).
Credit: @jagraj28

The post conjectures that there are infinitely many primes `q` with
`gcd(ord_q(2), ord_q(3)) = 1`, where `ord_q(n)` is the least `d ≥ 1` with `n ^ d ≡ 1 (mod q)`.
The known such primes are listed in OEIS A344202 (`683, 599479, 108390409, …`). The post has no
answer.

Formalization notes:
* `ord_q(2)` and `ord_q(3)` are defined only when `q ∤ 6`, so `q` ranges over primes `q ≥ 5`;
  they are `orderOf (2 : ZMod q)` and `orderOf (3 : ZMod q)`.
* `main` states the conjecture. A direct computation gives `683` and `599479` as the only such
  primes below `10 ^ 6`, as in A344202.
-/

namespace OMA.S_mo_497324

/-- There are infinitely many primes `q` for which the orders of `2` and `3` modulo `q` are
coprime. -/
theorem main :
    {q : ℕ | q.Prime ∧ 5 ≤ q ∧
      Nat.Coprime (orderOf (2 : ZMod q)) (orderOf (3 : ZMod q))}.Infinite := by
  sorry

end OMA.S_mo_497324
