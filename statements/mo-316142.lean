import Mathlib

/-!
# A conjectural lower bound for `|{∑ k a_k : a_1, …, a_n distinct elements of A}|`

Source: https://mathoverflow.net/questions/316142
Credit: @koolkao

Question (Zhi-Wei Sun, MathOverflow 316142, 2018; CC BY-SA 4.0). Let `n` be a positive integer
and let `F` be a field with `p(F) > n + 1`, where `p(F) = p` if the characteristic of `F` is a
prime `p` and `p(F) = +∞` if the characteristic is zero. Let `A` be a finite subset of `F` with
`|A| ≥ n + δ_{n,3}`. Is it true that the set
`S(A) = {∑_{k=1}^n k a_k : a_1, …, a_n are distinct elements of A}` satisfies
`|S(A)| ≥ min {p(F), (|A| - n) n (n + 1) / 2 + n (n² - 1) / 6 + 1}`?

`main` states that the answer is yes. A disproof is a choice of `n`, `F` and `A` satisfying the
hypotheses for which the bound fails.

Translation choices:
* `p(F)` is `ringChar F` when it is nonzero; for `ringChar F = 0` the minimum is just the second
  term;
* `δ_{n,3}` is `if n = 3 then 1 else 0`;
* an `n`-tuple of distinct elements of `A` is an injective `a : Fin n → F` with values in `A`, and
  index `k : Fin n` carries the weight `k + 1`;
* `|S(A)|` is `Set.ncard`; the arithmetic of the bound is in `ℕ`, where all the divisions are
  exact.
-/

namespace OMA.S_mo_316142

/-- The source's lower bound for `|S(A)|`. -/
theorem main :
    ∀ (n : ℕ), 1 ≤ n → ∀ (F : Type) [Field F], (ringChar F = 0 ∨ n + 1 < ringChar F) →
      ∀ A : Finset F, n + (if n = 3 then 1 else 0) ≤ A.card →
        (if ringChar F = 0 then (A.card - n) * (n * (n + 1) / 2) + n * (n ^ 2 - 1) / 6 + 1
          else min (ringChar F) ((A.card - n) * (n * (n + 1) / 2) + n * (n ^ 2 - 1) / 6 + 1)) ≤
          {s : F | ∃ a : Fin n → F, Function.Injective a ∧ (∀ k, a k ∈ A) ∧
            s = ∑ k : Fin n, ((k : ℕ) + 1 : F) * a k}.ncard := by
  sorry

end OMA.S_mo_316142
