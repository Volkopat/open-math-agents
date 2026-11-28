import Mathlib

/-!
# A130091: Numbers having in their canonical prime factorization mutually distinct exponents

Source: https://oeis.org/A130091
Credit: @xor2k

The entry's text is a remark (Danny Rorabaugh, Sep 23 2015), not a conjecture:
This sequence does not contain any number of the form 36n-6 or 36n+6, as such numbers are
divisible by 6 but not by 4 or 9. Consequently, this sequence does not contain 24 consecutive
integers. The quest for the greatest number of consecutive integers in this sequence has ties
to the ABC conjecture (see the MathOverflow link).

Formalized: exactly the two precise claims of the remark, (i) no number `36n-6` (`n ≥ 1`) and
no number `36n+6` (`n ≥ 0`) is a term, and (ii) there are no 24 consecutive integers
`m, m+1, ..., m+23` that are all terms. The ABC conjecture is only mentioned and is not
formalized.

Conventions: terms are positive integers (`1` is a term, offset 1); mutually distinct exponents
means that `p ↦ k.factorization p` is injective on the set of prime factors of `k`. The range
`n ≥ 1` for `36n-6` makes that number positive (it is then `≥ 30`, so natural subtraction does
not truncate); `36*0+6 = 6` is included in the second family.
-/

namespace OMA.S_oeis_a130091

/-- `k` is a term of A130091: `k` is positive and the exponents in its canonical prime
factorization are mutually distinct. -/
def InSeq (k : ℕ) : Prop :=
  0 < k ∧ Set.InjOn k.factorization (k.primeFactors : Set ℕ)

/-- No number `36n-6` (`n ≥ 1`) or `36n+6` (`n ≥ 0`) is a term, and the sequence contains no
24 consecutive integers. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ¬ InSeq (36 * n - 6)) ∧
    (∀ n : ℕ, ¬ InSeq (36 * n + 6)) ∧
    (¬ ∃ m : ℕ, ∀ i : ℕ, i < 24 → InSeq (m + i)) := by
  sorry

end OMA.S_oeis_a130091
