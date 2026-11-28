import OMAReductions.R_Erdos114_erdos_114_R1
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Set.Card

/-!
# Structural Reduction of Erdős Problem 114 Step R1.H2 (Unit Critical Values)

Follows Teng Zhang (arXiv:2611.12830, Nov 2026) and Dahlke (cubic case):
- Degrees n = 1, 2 are vacuous under the hypothesis of at least two distinct critical values
  (proved directly in `main` below).
- `H1`: Zhang's Möbius-variation circle-to-line transfer for all n ≥ 28
  (Proposition `prop:uniform-circle-transfer`), reducing the unit-critical-value lemniscate
  bound to a uniform lower bound `4/5` on the Cauchy–Crofton inverse-line deficit.
- `H2`: Effective inverse-line deficit `> 4/5` for all n ≥ 256 (Theorem `thm:line256`).
- `H3`: Finite-degree inverse-line deficit `> 4/5` for 28 ≤ n ≤ 255
  (Proposition `prop:finite-line`, slice interpolation and rational arithmetic).
- `H4`: Small degrees 3 ≤ n ≤ 27 with all critical values on the unit circle and at least
  two distinct critical values (Dahlke for n = 3; Zhang Sections 8–14 for 4 ≤ n ≤ 27).
-/

namespace OMA.R_Erdos114_erdos_114_R1_H2_R1

open Polynomial MeasureTheory Set

private lemma derivative_ne_zero_of_monic_pos {q : ℂ[X]} (hq : q.Monic) (hpos : 0 < q.natDegree) :
    q.derivative ≠ 0 := by
  intro h0
  have hlc : q.derivative.coeff (q.natDegree - 1) = (q.natDegree : ℂ) := by
    rw [coeff_derivative, show q.natDegree - 1 + 1 = q.natDegree by omega, hq.coeff_natDegree,
      one_mul]
    exact_mod_cast (Nat.sub_add_cancel hpos)
  rw [h0, coeff_zero] at hlc
  have hne : (q.natDegree : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  exact hne hlc.symm

private lemma deg_ge_three_of_two_crit_vals {n : ℕ} (hn : 0 < n) {q : ℂ[X]}
    (hq : q.Monic) (hdq : q.natDegree = n)
    (hmulti : ∃ x y : ℂ, q.derivative.IsRoot x ∧ q.derivative.IsRoot y ∧ q.eval x ≠ q.eval y) :
    3 ≤ n := by
  classical
  by_contra hlt
  have hle : n ≤ 2 := by omega
  obtain ⟨x, y, hx, hy, hneq⟩ := hmulti
  have hxy : x ≠ y := fun h => hneq (congrArg q.eval h)
  have hdne : q.derivative ≠ 0 := derivative_ne_zero_of_monic_pos hq (hdq ▸ hn)
  have hdeg : q.derivative.natDegree ≤ 1 := by
    have := Polynomial.natDegree_derivative_le q
    omega
  have hcard : q.derivative.roots.toFinset.card ≤ 1 :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' q.derivative).trans hdeg)
  have hsub : ({x, y} : Finset ℂ) ⊆ q.derivative.roots.toFinset := by
    intro a ha
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hdne]
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> assumption
  have htwo : 2 ≤ q.derivative.roots.toFinset.card := by
    simpa [Finset.card_pair hxy] using Finset.card_le_card hsub
  omega

/-- Zhang's Möbius-variation circle-to-line transfer (`prop:uniform-circle-transfer`) for `n ≥ 28`. -/
def H1 : Prop :=
  ∀ n : ℕ, 28 ≤ n →
    (∀ F : ℂ[X], F.Monic → F.natDegree = n → F.coeff (n - 1) = 0 →
      (∃ x y : ℂ, F.derivative.IsRoot x ∧ F.derivative.IsRoot y ∧ ‖F.eval x - F.eval y‖ = 2) →
      (∀ x y : ℂ, F.derivative.IsRoot x → F.derivative.IsRoot y → ‖F.eval x - F.eval y‖ ≤ 2) →
      ∀ w₀ : ℂ, ∀ ψ : ℝ, (4 : ℝ) / 5 <
        (1 / 2 : ℝ) * ∫ θ in Set.Ioo (0 : ℝ) Real.pi, ∫ h : ℝ, ((n : ℝ) -
          (({x : ℝ | (Complex.exp (-(ψ : ℂ) * Complex.I) *
            (F.eval (Complex.exp ((θ : ℂ) * Complex.I) * ((x : ℂ) + (h : ℂ) * Complex.I)) - w₀)).im = 0}).ncard : ℝ))) →
    ∀ q : ℂ[X], q.Monic → q.natDegree = n →
      (∀ x : ℂ, q.derivative.IsRoot x → ‖q.eval x‖ = 1) →
      (∃ x y : ℂ, q.derivative.IsRoot x ∧ q.derivative.IsRoot y ∧ q.eval x ≠ q.eval y) →
      Erdos114.lemniscateLength q ≤ Erdos114.lemniscateLength (X ^ n - 1)

/-- Zhang's effective inverse-line deficit bound (`thm:line256`) for all degrees `n ≥ 256`. -/
def H2 : Prop :=
  ∀ n : ℕ, 256 ≤ n →
    ∀ F : ℂ[X], F.Monic → F.natDegree = n → F.coeff (n - 1) = 0 →
      (∃ x y : ℂ, F.derivative.IsRoot x ∧ F.derivative.IsRoot y ∧ ‖F.eval x - F.eval y‖ = 2) →
      (∀ x y : ℂ, F.derivative.IsRoot x → F.derivative.IsRoot y → ‖F.eval x - F.eval y‖ ≤ 2) →
      ∀ w₀ : ℂ, ∀ ψ : ℝ, (4 : ℝ) / 5 <
        (1 / 2 : ℝ) * ∫ θ in Set.Ioo (0 : ℝ) Real.pi, ∫ h : ℝ, ((n : ℝ) -
          (({x : ℝ | (Complex.exp (-(ψ : ℂ) * Complex.I) *
            (F.eval (Complex.exp ((θ : ℂ) * Complex.I) * ((x : ℂ) + (h : ℂ) * Complex.I)) - w₀)).im = 0}).ncard : ℝ))

/-- Zhang's finite-degree inverse-line deficit bound (`prop:finite-line`) for `28 ≤ n ≤ 255`. -/
def H3 : Prop :=
  ∀ n : ℕ, 28 ≤ n → n ≤ 255 →
    ∀ F : ℂ[X], F.Monic → F.natDegree = n → F.coeff (n - 1) = 0 →
      (∃ x y : ℂ, F.derivative.IsRoot x ∧ F.derivative.IsRoot y ∧ ‖F.eval x - F.eval y‖ = 2) →
      (∀ x y : ℂ, F.derivative.IsRoot x → F.derivative.IsRoot y → ‖F.eval x - F.eval y‖ ≤ 2) →
      ∀ w₀ : ℂ, ∀ ψ : ℝ, (4 : ℝ) / 5 <
        (1 / 2 : ℝ) * ∫ θ in Set.Ioo (0 : ℝ) Real.pi, ∫ h : ℝ, ((n : ℝ) -
          (({x : ℝ | (Complex.exp (-(ψ : ℂ) * Complex.I) *
            (F.eval (Complex.exp ((θ : ℂ) * Complex.I) * ((x : ℂ) + (h : ℂ) * Complex.I)) - w₀)).im = 0}).ncard : ℝ))

/-- Small degrees `3 ≤ n ≤ 27` with all critical values on the unit circle and at least two
distinct critical values (Dahlke for `n = 3`; Zhang Sections 8–14 for `4 ≤ n ≤ 27`). -/
def H4 : Prop :=
  ∀ n : ℕ, 3 ≤ n → n ≤ 27 →
    ∀ q : ℂ[X], q.Monic → q.natDegree = n →
      (∀ x : ℂ, q.derivative.IsRoot x → ‖q.eval x‖ = 1) →
      (∃ x y : ℂ, q.derivative.IsRoot x ∧ q.derivative.IsRoot y ∧ q.eval x ≠ q.eval y) →
      Erdos114.lemniscateLength q ≤ Erdos114.lemniscateLength (X ^ n - 1)

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos114_erdos_114_R1.H2 := by
  intro h1 h2 h3 h4 n hn q hq hdq hunit hmulti
  have h3le : 3 ≤ n := deg_ge_three_of_two_crit_vals hn hq hdq hmulti
  by_cases h27 : n ≤ 27
  · exact h4 n h3le h27 q hq hdq hunit hmulti
  · have h28 : 28 ≤ n := by omega
    by_cases h255 : n ≤ 255
    · exact h1 n h28 (h3 n h28 h255) q hq hdq hunit hmulti
    · exact h1 n h28 (h2 n (by omega)) q hq hdq hunit hmulti

end OMA.R_Erdos114_erdos_114_R1_H2_R1
