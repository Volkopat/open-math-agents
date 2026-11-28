import Mathlib

/-!
# Multivariate polynomial with positive coefficients

Source: https://mathoverflow.net/questions/121687 (CC BY-SA 4.0).

For an integer `n ≥ 3` let
`f(x_1, …, x_n) = ((1/n) ∑_k x_k^n)^(2n-2) - ∏_k (x_k^(2n-2) + (∏_{j ≠ k} x_j)^2) / 2`
and `g(y_1, …, y_n) = f(y_1, y_1 + y_2, …, y_1 + ⋯ + y_n)`. The asker conjectures (checked by
computer for `n = 3, 4, 5`) that (1) on `(0, ∞)^n`, `g` is increasing in each variable, and
(2) all the coefficients of `g` are nonnegative, (2) being the stronger claim.

We state (2).

Formalization notes:
* `g` is an `MvPolynomial (Fin n) ℚ`; `x k = ∑_{i ≤ k} X i` is the substitution `x_k = y_1 + ⋯ + y_k`.
* Checked by exact expansion: for `n = 3` (88 terms) and `n = 4` (2921 terms) no coefficient is negative.
-/

namespace OMA.S_mo_121687

/-- For `n ≥ 3`, every coefficient of `g` is nonnegative. -/
theorem main :
    ∀ (n : ℕ) (hn : 3 ≤ n),
    let x : Fin n → MvPolynomial (Fin n) ℚ :=
      fun k => ∑ i ∈ Finset.univ.filter (fun i => i ≤ k), MvPolynomial.X i
    let g : MvPolynomial (Fin n) ℚ :=
      (MvPolynomial.C (1 / (n : ℚ)) * ∑ k, x k ^ n) ^ (2 * n - 2) -
        ∏ k, MvPolynomial.C (1 / 2 : ℚ) * (x k ^ (2 * n - 2) + (∏ j ∈ Finset.univ.erase k, x j) ^ 2)
    ∀ m, 0 ≤ g.coeff m := by
  sorry

end OMA.S_mo_121687
