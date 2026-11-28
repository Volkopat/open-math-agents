import Mathlib

/-!
# A361887: a(n) = S(5,n), where S(r,n) = Sum_{k = 0..floor(n/2)} ( binomial(n,k) - binomial(n,k-1) )^r.

Source: https://oeis.org/A361887
Credit: @azmiozgen

Conjecture (from the entry, extending Gould's 1974 conjecture for r = 3): calculation suggests that if
r is odd then S(r,n) is always divisible by S(1,n). For the present sequence (r = 5) this says that
S(1,n) divides a(n) = S(5,n) for every n ≥ 0.

Formalization notes:
* binomial(n, -1) = 0, so the k = 0 term of S(r, n) is 1. S is computed in ℤ.
* Only the case r = 5 (this sequence) is stated.
* Controls (computed): a(0..6) = 1, 1, 2, 33, 276, 4150, 65300, as in the entry; S(1,n) divides S(5,n) for n < 200.
-/

namespace OMA.S_oeis_a361887

/-- `S(r, n) = ∑_{k=0}^{⌊n/2⌋} (C(n,k) - C(n,k-1))^r`, with `C(n,-1) = 0`. -/
def S (r n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    ((n.choose k : ℤ) - (if k = 0 then 0 else (n.choose (k - 1) : ℤ))) ^ r

/-- `S(1, n)` divides `a(n) = S(5, n)` for every `n`. -/
theorem main : ∀ n : ℕ, S 1 n ∣ S 5 n := by
  sorry

end OMA.S_oeis_a361887
