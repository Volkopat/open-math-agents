import Mathlib

namespace OMA.S_oeis_a123516

/-- Triangle entry from OEIS A123516:
`T(n, k) = (-1)^k * n! * 2^(n - 2k) * C(n, k) * C(2k, k)` for `0 ≤ k ≤ n`. -/
noncomputable def T (n k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * (n.factorial : ℝ) * (2 : ℝ) ^ ((n : ℤ) - 2 * (k : ℤ)) *
    (Nat.choose n k : ℝ) * (Nat.choose (2 * k) k : ℝ)

/-- Row polynomial `P(n, x) = ∑_{k=0}^n T(n, k) * x^(n - k)` over `ℝ`. -/
noncomputable def P (n : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (T n k) * Polynomial.X ^ (n - k)

/-- Complexification of `P(n, x)`. -/
noncomputable def PComplex (n : ℕ) : Polynomial ℂ :=
  (P n).map (algebraMap ℝ ℂ)

/-- Reduced polynomial `p(n, u)` satisfying `P(n, 1/2 + x) = p(n, x^2)` for even `n`
and `P(n, 1/2 + x) = x * p(n, x^2)` for odd `n`. -/
noncomputable def pPoly : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => Polynomial.C 2
  | n + 2 =>
      if Even (n + 2) then
        Polynomial.C (2 * (2 * ((n + 2 : ℕ) : ℝ) - 1)) * Polynomial.X * pPoly (n + 1) +
          Polynomial.C (((n + 1 : ℕ) : ℝ) ^ 2) * (1 - Polynomial.C 4 * Polynomial.X) * pPoly n
      else
        Polynomial.C (2 * (2 * ((n + 2 : ℕ) : ℝ) - 1)) * pPoly (n + 1) +
          Polynomial.C (((n + 1 : ℕ) : ℝ) ^ 2) * (1 - Polynomial.C 4 * Polynomial.X) * pPoly n

/-- Peter Bala's Conjectures 1 and 2 (OEIS A123516, Aug 09 2024):
1. `P(n, 1/2 + x) = p(n, x^2)` for even `n` and `x * p(n, x^2)` for odd `n`.
2. (Conjecture 1 — Riemann hypothesis): For every `n ≥ 1`, every complex zero `z` of `P(n, z)`
   lies on the vertical line `Re(z) = 1 / 2`.
3. (Conjecture 2 — Negative interlacing zeros): There exist strictly increasing negative real
   root sequences `roots n : Fin (n / 2) → ℝ` enumerating all real roots of `p(n, u)` such that
   for every `m ≥ 1`:
   - `roots (2 * m + 1)` and `roots (2 * m)` interlace as
     `roots (2 * m + 1) i < roots (2 * m) i` for all `i : Fin m` and
     `roots (2 * m) i < roots (2 * m + 1) (i + 1)` for `i + 1 < m`;
   - `roots (2 * m + 2)` and `roots (2 * m + 1)` interlace as
     `roots (2 * m + 2) i < roots (2 * m + 1) i < roots (2 * m + 2) (i + 1)` for all `i : Fin m`. -/
theorem main :
    (∀ (n : ℕ) (x : ℝ),
      (P n).eval (1 / 2 + x) =
        if Even n then (pPoly n).eval (x ^ 2) else x * (pPoly n).eval (x ^ 2)) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ z : ℂ, (PComplex n).eval z = 0 → z.re = 1 / 2) ∧
    (∃ roots : ∀ n : ℕ, Fin (n / 2) → ℝ,
      (∀ n : ℕ, StrictMono (roots n)) ∧
      (∀ (n : ℕ) (i : Fin (n / 2)), roots n i < 0) ∧
      (∀ (n : ℕ) (u : ℝ), (pPoly n).eval u = 0 ↔ ∃ i : Fin (n / 2), u = roots n i) ∧
      (∀ (m : ℕ), 1 ≤ m →
        (∀ (i : Fin m),
          roots (2 * m + 1) ⟨i.val, by omega⟩ < roots (2 * m) ⟨i.val, by omega⟩) ∧
        (∀ (i : ℕ) (hi : i + 1 < m),
          roots (2 * m) ⟨i, by omega⟩ < roots (2 * m + 1) ⟨i + 1, by omega⟩) ∧
        (∀ (i : Fin m),
          roots (2 * m + 2) ⟨i.val, by omega⟩ < roots (2 * m + 1) ⟨i.val, by omega⟩ ∧
          roots (2 * m + 1) ⟨i.val, by omega⟩ < roots (2 * m + 2) ⟨i.val + 1, by omega⟩))) := by
  sorry

end OMA.S_oeis_a123516
