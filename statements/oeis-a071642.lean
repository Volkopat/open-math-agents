import Mathlib

/-!
# A071642: Numbers n such that x^n + x^(n-1) + x^(n-2) + ... + x + 1 is irreducible over GF(2).

Source: https://oeis.org/A071642
Credit: @avivorly

A071642 lists the `n` such that the all-ones polynomial `x^n + x^(n-1) + ... + x + 1` is irreducible
over GF(2): 0, 1, 2, 4, 10, 12, 18, 28, 36, 52, 58, 60, 66, ...

Conjecture (Luis H. Gallardo, Dec 23 2019): Terms >= 2 are numbers `n` such that
`P^n + P^(n-1) + P^(n-2) + ... + P + 1` is irreducible over GF(2), where `P = x^2 + x + 1`.

That is: the set of terms `n ≥ 2` of A071642 equals the set of `n` for which
`P^n + ... + P + 1` is irreducible over GF(2), and the conjecture is stated as this equality of sets.

Conventions:
- GF(2) is `ZMod 2`, and irreducible is Mathlib's `Irreducible` in `(ZMod 2)[X]`.
- `allOnes n = 1 + X + ... + X^n`. The entry also lists 0 and 1 (the polynomials 1 and `x + 1`); the
  conjecture is about the terms `≥ 2` only, which is the condition `2 ≤ n` on the left.
- On the right `n` ranges over all natural numbers; for `n = 0, 1` the polynomials `1` and `P + 1 = x^2 + x`
  are not irreducible, so no `n < 2` belongs to the right-hand set either.
-/

namespace OMA.S_oeis_a071642

open Polynomial

/-- The all-ones polynomial `1 + X + ... + X^n` over GF(2). -/
noncomputable def allOnes (n : ℕ) : (ZMod 2)[X] := ∑ i ∈ Finset.range (n + 1), X ^ i

/-- `P = X^2 + X + 1` over GF(2). -/
noncomputable def P : (ZMod 2)[X] := X ^ 2 + X + 1

theorem main :
    {n : ℕ | 2 ≤ n ∧ Irreducible (allOnes n)} =
      {n : ℕ | Irreducible (∑ i ∈ Finset.range (n + 1), P ^ i)} := by
  sorry

end OMA.S_oeis_a071642
