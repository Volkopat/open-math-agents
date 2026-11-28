import FormalConjectures.Millennium.RiemannHypothesis

/-!
# Dedekind zeros of low-degree and cyclotomic fields

Credit: @deepqntm. The first step transfers zeros of the indicated fields to primitive
Dirichlet L-functions. The second step is primitive Dirichlet GRH. It remains to continue the
reciprocal germ from 2 to each off-line strip point for the remaining number fields.
-/

namespace OMA.R_ERH_extended_riemann_hypothesis_R2

open NumberField Complex Filter Set
open scoped Topology

/-- Primitive character zero transfer for all quadratic, degree-one and cyclotomic fields. -/
def H1 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    (Module.finrank ℚ K ≤ 2 ∨ ∃ n : ℕ, 0 < n ∧ IsCyclotomicExtension {n} ℚ K) →
    ∀ Z : ℂ → ℂ, ERH.IsDedekindZeta K Z → ∀ s : ℂ, 0 < s.re → s ≠ 1 → Z s = 0 →
    ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q), χ.IsPrimitive ∧ χ.LFunction s = 0

/-- The primitive critical-strip theorem of the Dirichlet GRH project. -/
def H2 : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → χ.LFunction s = 0 → s.re = 1 / 2

/-- For a remaining field, continue the reciprocal of the convergent Euler product to each
off-line strip point on a connected neighborhood avoiding the pole. -/
def H3 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], 2 < Module.finrank ℚ K →
    (∀ n : ℕ, 0 < n → ¬ IsCyclotomicExtension {n} ℚ K) →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ 1 / 2 →
    ∃ (U : Set ℂ) (F : ℂ → ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ ({1}ᶜ : Set ℂ) ∧
      (2 : ℂ) ∈ U ∧ s ∈ U ∧ DifferentiableOn ℂ F U ∧
      ∀ᶠ w in 𝓝 (2 : ℂ), dedekindZeta K w * F w = 1

/-- Ring isomorphism preserves ideal norms and the Dedekind series, as in reduction R1. -/
theorem dedekindZeta_eq_of_ringEquiv {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] (e : K ≃+* L) : dedekindZeta K = dedekindZeta L := by
  let r : 𝓞 K ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv e
  let i : Ideal (𝓞 K) ≃ Ideal (𝓞 L) := (Ideal.relIsoOfBijective r.toRingHom r.bijective).symm.toEquiv
  have hnorm (I : Ideal (𝓞 K)) : Ideal.absNorm I = Ideal.absNorm (i I) :=
    Nat.card_congr (Ideal.quotientEquiv I (i I) r rfl).toEquiv
  have hcard (n : ℕ) : Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} =
      Nat.card {J : Ideal (𝓞 L) // Ideal.absNorm J = n} :=
    Nat.card_congr (i.subtypeEquiv fun I => by rw [hnorm I])
  funext z
  simp only [dedekindZeta, hcard]

theorem main : H1 → H2 → H3 → type_of% @ERH.extended_riemann_hypothesis := by
  intro htransfer hgrh hremaining K _ _ Z hZ s hpos hlt hz
  let f : K →ₐ[ℚ] ℂ := IsAlgClosed.lift (R := ℚ)
  let L := f.fieldRange
  let e : K ≃+* L := f.equivFieldRange.toRingEquiv
  let _ : NumberField L := NumberField.of_ringEquiv K L e
  have hL : ERH.IsDedekindZeta L Z :=
    ⟨hZ.1, fun z h => (hZ.2 z h).trans (congrFun (dedekindZeta_eq_of_ringEquiv e) z)⟩
  by_cases hc : Module.finrank ℚ L ≤ 2 ∨ ∃ n : ℕ, 0 < n ∧ IsCyclotomicExtension {n} ℚ L
  · obtain ⟨q, hq, χ, hχ, hzero⟩ := htransfer L hc Z hL s hpos (fun he => by simp [he] at hlt) hz
    exact hgrh q χ hχ s hpos hlt hzero
  · by_contra hline
    obtain ⟨U, F, hU, hconn, hoff, h2, hsU, hF, hnear⟩ := hremaining L (lt_of_not_ge (mt Or.inl hc))
      (fun n hn he => hc (Or.inr ⟨n, hn, he⟩)) s hpos hlt hline
    have hano : AnalyticOnNhd ℂ (fun w => Z w * F w) U :=
      ((hL.1.mono hoff).analyticOnNhd hU).mul (hF.analyticOnNhd hU)
    have hhalf : ∀ᶠ w in 𝓝 (2 : ℂ), 1 < w.re :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
    have hgerm : (fun w => Z w * F w) =ᶠ[𝓝 (2 : ℂ)] (fun _ => (1 : ℂ)) := by
      filter_upwards [hnear, hhalf] with w hw hw'
      rw [hL.2 w hw']
      exact hw
    have hone := (hano.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hconn h2 hgerm) hsU
    change Z s * F s = 1 at hone
    simp [hz] at hone

end OMA.R_ERH_extended_riemann_hypothesis_R2
