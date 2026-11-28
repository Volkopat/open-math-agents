import Mathlib

/-!
# Monotonicity of determinants for two insurance recurrences

Source: Fancier of Mathematica, https://mathoverflow.net/questions/217457 (CC BY-SA 4.0).
Credit: @connoranderson.

A joint PMF describes three nonnegative integer claims with arbitrary
dependence, as clarified by the author. The mass at total zero lies strictly
between zero and one. The two determinants use the row gaps one and two
from the original question.
-/

namespace OMA.S_mo_217457

abbrev Claims := ℕ × ℕ × ℕ

noncomputable def mass (p : PMF Claims) (f : Claims → ℕ) (k : ℕ) : ℝ :=
  ((p.map f) k).toReal

def total (v : Claims) : ℕ := v.1+v.2.1+v.2.2

/-- Common linear recurrence; the forcing term distinguishes α and β. -/
noncomputable def seq (s force : ℕ → ℝ) (u₀ u₁ u₂ : ℝ) : ℕ → ℝ
  | 0 => u₀
  | 1 => u₁
  | 2 => u₂
  | n+3 => (seq s force u₀ u₁ u₂ n + force (n+3) -
      ∑ k : Fin (n+2), s (k.val+1) * seq s force u₀ u₁ u₂ (n+2-k.val)) / s 0
termination_by n => n
decreasing_by all_goals omega

noncomputable def alpha (p : PMF Claims) : ℕ → ℝ :=
  let a := mass p (fun v => v.1)
  let b := mass p (fun v => v.2.1)
  let c := mass p (fun v => v.2.2)
  seq (mass p total) (fun n => -a (n-2)) 1 0 (-1/(b 0*c 0))

noncomputable def beta (p : PMF Claims) : ℕ → ℝ :=
  let a := mass p (fun v => v.1)
  let b := mass p (fun v => v.2.1)
  let c := mass p (fun v => v.2.2)
  seq (mass p total)
    (fun n => -a (n-2)*c 0 + c 0 * ∑ k ∈ Finset.range n, a k*b (n-1-k))
    0 1 (-(c 1)/(c 0)-1/(b 0))

/-- The determinant with rows n and n+h. -/
noncomputable def detAt (p : PMF Claims) (h n : ℕ) : ℝ :=
  alpha p n * beta p (n+h) - beta p n * alpha p (n+h)

theorem main :
    ∀ p : PMF Claims, 0 < mass p total 0 → mass p total 0 < 1 → ∀ n : ℕ,
      (0 < detAt p 1 n ∧ detAt p 1 n < detAt p 1 (n+1)) ∧
      (detAt p 2 (n+1) < detAt p 2 n ∧ detAt p 2 n < 0) := by
  sorry

end OMA.S_mo_217457
