import Mathlib

/-!
# Polynomials of degree and height `M` taking prime values at `1, 2, …, M`

Source: https://mathoverflow.net/questions/512119/do-there-exist-polynomials-of-degree-and-height-m-taking-prime-values-at-1-2
Credit: @shc261392

Question. Is it true that for every positive integer `M` there exists a polynomial
`f(x) = 1 + ∑_{i=1}^{M} a_i x^i` with `a_i ∈ {0, 1, …, M}`, not all `a_i` equal to `0`, such that
`f(1), f(2), …, f(M)` are all prime?

Reading used here (the affirmative answer): the coefficients are `a : Fin M → ℕ`, with `a i` the
coefficient of `x^(i+1)`. (A brute-force search finds such polynomials for `M ≤ 7`.)
-/

namespace OMA.S_mo_512119

theorem main :
    ∀ M : ℕ, 0 < M → ∃ a : Fin M → ℕ, (∀ i, a i ≤ M) ∧ (∃ i, a i ≠ 0) ∧
      ∀ x : ℕ, 1 ≤ x → x ≤ M → (1 + ∑ i : Fin M, a i * x ^ (i.val + 1)).Prime := by
  sorry

end OMA.S_mo_512119
