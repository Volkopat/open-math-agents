import Mathlib

/-!
# A361891: a(n) = S(7,n)/S(1,n), where S(r,n) = Sum_{k = 0..floor(n/2)} ( binomial(n,k) - binomial(n,k-1) )^r.

Source: https://oeis.org/A361891
Credit: @azmiozgen

Conjecture (Peter Bala, from the entry, extending Gould's 1974 conjecture for r = 3): calculation
suggests that if r is odd then S(r,n) is always divisible by S(1,n). The present sequence is the
case r = 7, so the conjecture for it is that S(1,n) divides S(7,n) for every n ≥ 0.

Formalization notes:
* binomial(n, -1) = 0, so the k = 0 term of S(r, n) is 1. S is computed in ℤ.
* Only the case r = 7 (this sequence) is stated.
* Controls (computed): S(7,n)/S(1,n) for n = 0..9 is 1, 1, 1, 43, 386, 9451, 246961, 6031627, 212559508, 6571985126, as in the entry; S(1,n) divides S(7,n)
  for n < 200.
-/

namespace OMA.S_oeis_a361891

/-- `S(r, n) = ∑_{k=0}^{⌊n/2⌋} (C(n,k) - C(n,k-1))^r`, with `C(n,-1) = 0`. -/
def S (r n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    ((n.choose k : ℤ) - (if k = 0 then 0 else (n.choose (k - 1) : ℤ))) ^ r

/-- `S(1, n)` divides `S(7, n)` for every `n`. -/
theorem main : ∀ n : ℕ, S 1 n ∣ S 7 n := by
  sorry

end OMA.S_oeis_a361891
