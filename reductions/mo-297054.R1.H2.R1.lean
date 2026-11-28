import OMAReductions.R_mo_297054_R1

-- Reduction mo-297054.R1.H2.R1 of step mo-297054.R1.H2
-- Credit: @AlfredMelson

namespace OMA.R_mo_297054_R1_H2_R1

open Metric Complex Filter
open scoped Topology

/-! A logarithm with nonpositive real part has a positive Herglotz measure.
Its first n complex moments live in real dimension 2n, so at most 2n+1
atoms suffice. We keep unnormalized derivatives in the recurrence. -/

private noncomputable def logJet {m : ℕ} (w : Fin m → ℝ) (u : Fin m → ℂ) (j : ℕ) : ℂ :=
  -2 * (j.factorial : ℂ) * ∑ i, (w i : ℂ) * (u i)^j

/-- Finite Herglotz moment representation, including its mass. -/
def H1 : Prop := ∀ (L : ℂ → ℂ), DifferentiableOn ℂ L (ball 0 1) →
  (∀ z ∈ ball (0 : ℂ) 1, (L z).re ≤ 0) → ∀ n : ℕ,
  ∃ (m : ℕ) (w : Fin m → ℝ) (u : Fin m → ℂ),
    m ≤ 2*n+1 ∧ (∀ i, 0 ≤ w i) ∧ (∀ i, ‖u i‖ = 1) ∧
    ∑ i, w i = -(L 0).re ∧
    ∀ j, 1 ≤ j → j ≤ n → iteratedDeriv j L 0 = logJet w u j

/-- A finite coefficient inequality for atomic moments; no functions on the disk occur. -/
def H2 : Prop := ∀ n m : ℕ, 6 ≤ n → m ≤ 2*n+1 →
  ∀ (w : Fin m → ℝ) (u : Fin m → ℂ), (∀ i, 0 ≤ w i) → (∀ i, ‖u i‖ = 1) →
  ∀ a : ℕ → ℂ, ‖a 0‖ = Real.exp (-(∑ i, w i)) →
  (∀ j < n, a (j+1) = ∑ i ∈ Finset.range (j+1),
    (j.choose i : ℂ) * a i * logJet w u (j-i+1)) →
  ‖a n / n.factorial‖ ≤ 2 / Real.exp 1

theorem main : H1 → H2 → OMA.R_mo_297054_R1.H2 := by
  intro moments bound f hf hb n hn
  have hz : (0:ℂ) ∈ ball (0:ℂ) 1 := mem_ball_self one_pos
  obtain ⟨L,_,hL,hExp⟩ := OMA.R_mo_297054_R1.holo_log f hf (fun z h => (hb z h).1)
  have hdiff : DifferentiableOn ℂ L (ball 0 1) :=
    fun z h => (hL z h).differentiableAt.differentiableWithinAt
  have hreal : ∀ z ∈ ball (0:ℂ) 1, (L z).re ≤ 0 := by
    intro z h
    have hnorm := (hb z h).2
    rw [hExp z h, Complex.norm_exp] at hnorm
    exact Real.exp_le_one_iff.mp hnorm
  obtain ⟨m,w,u,hm,hw,hu,mass,jet⟩ := moments L hdiff hreal n
  apply bound n m hn hm w u hw hu (fun j => iteratedDeriv j f 0)
  · simp only [iteratedDeriv_zero, mass, neg_neg]
    rw [hExp 0 hz, Complex.norm_exp]
  · intro j hj
    have near : deriv f =ᶠ[𝓝 0] f * deriv L := by
      filter_upwards [isOpen_ball.mem_nhds hz] with z h
      change deriv f z = f z * deriv L z
      rw [(hL z h).deriv]
      field_simp [(hb z h).1]
    have fs : ContDiffAt ℂ j f 0 := (hf.contDiffOn isOpen_ball).contDiffAt (isOpen_ball.mem_nhds hz)
    have ls : ContDiffAt ℂ j (deriv L) 0 := ((hdiff.deriv isOpen_ball).contDiffOn isOpen_ball).contDiffAt (isOpen_ball.mem_nhds hz)
    rw [iteratedDeriv_succ', near.iteratedDeriv_eq, iteratedDeriv_mul fs ls]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← iteratedDeriv_succ', jet (j-i+1) (by omega) (by omega)]

end OMA.R_mo_297054_R1_H2_R1
