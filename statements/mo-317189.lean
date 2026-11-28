import Mathlib

/-!
# The one-dimensional case of the tripling versus doubling inequality

Source: https://mathoverflow.net/questions/317189
Asked by MathOverflow user Hailong Dao.

For a finite set `A` of vectors in `ℤ^d` whose real span is `ℝ^d`, write `s_i(A)` for the size of
the `i`-fold sumset `A + ⋯ + A`. Question 2 of the post asks for sufficient conditions on `A`
for the inequality `s_3(A) ≥ (d+1) s_2(A) - binom(d+1,2) s_1(A) + binom(d+1,3)`, and adds:
for `d = 1` it reads `s_3(A) ≥ 2 s_2(A) - s_1(A)`, and in fact the asker does not know any set
of integers that fails it.

This file formalizes that last remark: the claim that the `d = 1` inequality of Question 2 holds
for every finite set of integers whose real span is `ℝ`.

Translation choices.
* `A` is a `Finset ℤ`; its real span is `ℝ` exactly when `A` contains a nonzero integer.
* `A + A` and `A + A + A` are pointwise sumsets, so `s_1 = A.card`, `s_2 = (A + A).card` and
  `s_3 = (A + A + A).card`; the inequality `s_3 ≥ 2 s_2 - s_1` is written without subtraction
  as `2 s_2 ≤ s_3 + s_1`.
* The general question (sufficient conditions in every dimension) is not formalized.
-/

namespace OMA.S_mo_317189

open Pointwise

theorem main :
    ∀ A : Finset ℤ, (∃ a ∈ A, a ≠ 0) → 2 * (A + A).card ≤ (A + A + A).card + A.card := by
  sorry

end OMA.S_mo_317189
