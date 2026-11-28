import OMAReductions.R_RamanujanTau_ramanujan_petersson_R1

namespace OMA.R_RamanujanTau_ramanujan_petersson_R1_H2_R1

open UpperHalfPlane
open scoped ComplexConjugate

/-- Reality of the prime coefficients of the analytic discriminant. -/
def H1 : Prop :=
  ∀ p : ℕ, Prime p → ((qExpansion 1 ModularForm.discriminant).coeff p).im = 0

/-- The real trace lies in the interval where the local quadratic has
nonpositive discriminant, including the repeated-root endpoints. -/
def H2 : Prop :=
  ∀ p : ℕ, Prime p →
    ((qExpansion 1 ModularForm.discriminant).coeff p).re ^ 2 ≤ 4 * (p : ℝ)^11

lemma roots {t : ℂ} {r : ℝ} (hr : 0 ≤ r) (hi : t.im = 0)
    (ht : t.re^2 ≤ 4*r^2) :
    ∃ z w : ℂ, t = z+w ∧ z*w = (r^2 : ℝ) ∧ ‖z‖ = r ∧ ‖w‖ = r := by
  let x := t.re / 2
  let y := Real.sqrt (r^2 - x^2)
  let z : ℂ := ⟨x,y⟩
  have hxy : x^2 + y^2 = r^2 := by
    have h : 0 ≤ r^2 - x^2 := by dsimp [x]; nlinarith
    dsimp [y]
    rw [Real.sq_sqrt h]
    ring
  have hn : ‖z‖ = r := by
    have h := Complex.sq_norm z
    change ‖z‖^2 = x*x + y*y at h
    nlinarith [norm_nonneg z]
  refine ⟨z,conj z,?_,?_,hn,by simpa using hn⟩
  · apply Complex.ext
    · change t.re = x+x
      dsimp [x]
      ring
    · change t.im = y + -y
      simpa using hi
  · rw [Complex.mul_conj', hn]
    norm_cast

theorem main : H1 → H2 → OMA.R_RamanujanTau_ramanujan_petersson_R1.H2 := by
  intro reality bound p hp
  let r := (p : ℝ)^((11 : ℝ)/2)
  have hr : 0 ≤ r := Real.rpow_nonneg (by positivity) _
  have hs : r^2 = (p : ℝ)^11 := by
    dsimp [r]
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  obtain ⟨z,w,ht,hprod,hz,hw⟩ := roots hr (reality p hp) (by rw [hs]; exact bound p hp)
  refine ⟨z,w,ht,?_,hz,hw⟩
  rw [hprod,hs]
  push_cast <;> rfl

end OMA.R_RamanujanTau_ramanujan_petersson_R1_H2_R1
