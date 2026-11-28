import Mathlib

/-!
# A prime-power congruence for integer values at roots of unity

The integer polynomial f takes integer values at the first n positive
powers of the specified primitive n-th root of unity. The witnesses a,b
in the conclusion are its indicated values, regarded as integers.

Source: https://mathoverflow.net/questions/284994
Credit: @connoranderson
-/

namespace OMA.S_mo_284994

noncomputable def root (n : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)

theorem main : ∀ n : ℕ, 0 < n → ∀ f : Polynomial ℤ,
    (∀ j : ℕ, 1 ≤ j → j ≤ n → ∃ a : ℤ, Polynomial.aeval (root n ^ j) f = (a : ℂ)) →
    ∀ p e : ℕ, p.Prime → 1 ≤ e → ∃ a b : ℤ,
      Polynomial.aeval (root n ^ (p^e)) f = (a : ℂ) ∧
      Polynomial.aeval (root n ^ (p^(e-1))) f = (b : ℂ) ∧ a ≡ b [ZMOD (p:ℤ)^e] := by
  sorry

end OMA.S_mo_284994
