import OMAReductions.R_ERH_extended_riemann_hypothesis_R2

/-!
# Cyclotomic subfields and reflection for the Dedekind reciprocal

Credit: @deepqntm.

A rational embedding into a cyclotomic field selects the fields whose Dedekind zeros can be
transferred to Dirichlet characters. For both families the functional equation reduces
zero exclusion to the half-strip to the right of the critical line. Removing the pole and
the isolated zeros of one continuation then gives a single domain for the reciprocal.
-/

namespace OMA.R_ERH_extended_riemann_hypothesis_R2_H3_R1

open Complex Filter NumberField Set
open scoped Topology

/-- Every zero of a cyclotomic subfield in the positive half-plane away from the pole
comes from a primitive Dirichlet character. The embedding may have proper image. -/
def H1 : Prop :=
  ∀ (n : ℕ) [NeZero n] (K : Type) [Field K] [NumberField K],
    (K →ₐ[ℚ] CyclotomicField n ℚ) →
    ∀ Z : ℂ → ℂ, ERH.IsDedekindZeta K Z →
    ∀ s : ℂ, 0 < s.re → s ≠ 1 → Z s = 0 →
      ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q), χ.IsPrimitive ∧ χ.LFunction s = 0

/-- Primitive Dirichlet L-functions have no zeros in the open right half of the strip. -/
def H2 : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → χ.LFunction s ≠ 0

/-- For each field under consideration there exists a normalized Dedekind continuation
whose zeros in the open critical strip are invariant under `s ↦ 1 - s`. -/
def H3 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], 2 < Module.finrank ℚ K →
    (∀ n : ℕ, 0 < n → ¬ IsCyclotomicExtension {n} ℚ K) →
    ∃ Z : ℂ → ℂ, ERH.IsDedekindZeta K Z ∧
      ∀ s : ℂ, 0 < s.re → s.re < 1 → Z s = 0 → Z (1 - s) = 0

/-- The remaining right-half-strip zero exclusion, for fields admitting no rational
embedding into any cyclotomic field of positive level. -/
def H4 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], 2 < Module.finrank ℚ K →
    (¬ ∃ n : ℕ, 0 < n ∧ Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ)) →
    ∀ Z : ℂ → ℂ, ERH.IsDedekindZeta K Z →
    ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → Z s ≠ 0

open scoped ComplexOrder in
/-- The nonzero class-number residue gives a point of convergence below 2. Positivity
of the ideal counts, including the contribution of the unit ideal, gives a nonzero value at 2. -/
theorem dedekindZeta_two_ne_zero (K : Type) [Field K] [NumberField K] :
    dedekindZeta K 2 ≠ 0 := by
  let a (n : ℕ) : ℂ := Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}
  have hres : ((dedekindZeta_residue K : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast dedekindZeta_residue_ne_zero K
  have hnear := (tendsto_sub_one_mul_dedekindZeta_nhdsGT K).eventually_ne hres
  have hlt : ∀ᶠ x : ℝ in 𝓝[>] 1, x < 2 :=
    (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2)).filter_mono nhdsWithin_le_nhds
  obtain ⟨x, hx, hn⟩ := (hlt.and hnear).exists
  have hsum : LSeriesSummable a (x : ℂ) := by
    by_contra hf
    exact hn (mul_eq_zero_of_right _ (LSeries.eq_zero_of_not_LSeriesSummable a x hf))
  have hpos : 0 < a 1 := by
    simp [a, Ideal.absNorm_eq_one_iff]
  have hbound : LSeries.abscissaOfAbsConv a < ((2 : ℝ) : EReal) :=
    hsum.abscissaOfAbsConv_le.trans_lt (by exact_mod_cast hx)
  change LSeries a 2 ≠ 0
  simpa only [ofReal_ofNat] using
    (LSeries.positive (a := a) (fun n => Nat.cast_nonneg _) hpos hbound).ne'

/-- The pole and the zeros form a countable exceptional set. Its open complement in the
complex plane is connected and carries the reciprocal wherever the continuation is nonzero. -/
theorem reciprocal_of_nonzero {K : Type} [Field K] [NumberField K] {Z : ℂ → ℂ}
    (hZ : ERH.IsDedekindZeta K Z) {s : ℂ} (hs : s ≠ 1) (hsZ : Z s ≠ 0) :
    ∃ (U : Set ℂ) (F : ℂ → ℂ), IsOpen U ∧ IsPreconnected U ∧ U ⊆ ({1}ᶜ : Set ℂ) ∧
      (2 : ℂ) ∈ U ∧ s ∈ U ∧ DifferentiableOn ℂ F U ∧
      ∀ᶠ w in 𝓝 (2 : ℂ), dedekindZeta K w * F w = 1 := by
  let D := ({1}ᶜ : Set ℂ)
  let U := D ∩ Z ⁻¹' ({0}ᶜ : Set ℂ)
  have hrank : 1 < Module.rank ℝ ℂ := by simp [Complex.rank_real_complex]
  have hD : IsOpen D := isOpen_compl_singleton
  have h2D : (2 : ℂ) ∈ D := by norm_num [D]
  have h2Z : Z 2 ≠ 0 := (hZ.2 2 (by norm_num)) ▸ dedekindZeta_two_ne_zero K
  have h2U : (2 : ℂ) ∈ U := ⟨h2D, h2Z⟩
  have hU : IsOpen U := hZ.1.continuousOn.isOpen_inter_preimage hD isOpen_compl_singleton
  have hdisc : IsDiscrete ((Z ⁻¹' {0}) ∩ D) :=
    isDiscrete_of_codiscreteWithin ((hZ.1.analyticOnNhd hD).preimage_zero_mem_codiscreteWithin
      h2Z h2D (isConnected_compl_singleton_of_one_lt_rank hrank 1))
  have hzeros := (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete hdisc
  have hbad : Uᶜ.Countable := by
    refine ((countable_singleton (1 : ℂ)).union hzeros).mono ?_
    intro w hw
    by_cases h : w = 1
    · exact Or.inl h
    · exact Or.inr ⟨Classical.byContradiction fun hn => hw ⟨h, hn⟩, h⟩
  have hconn : IsPreconnected U := by
    simpa only [compl_compl] using (hbad.isConnected_compl_of_one_lt_rank hrank).isPreconnected
  refine ⟨U, fun w => (Z w)⁻¹, hU, hconn, inter_subset_left, h2U, ⟨hs, hsZ⟩,
    (hZ.1.mono inter_subset_left).inv (fun _ hw => hw.2), ?_⟩
  filter_upwards [hU.mem_nhds h2U, (isOpen_lt continuous_const continuous_re).mem_nhds
    (show 1 < (2 : ℂ).re by norm_num)] with w hw hwre
  rw [← hZ.2 w hwre]
  exact mul_inv_cancel₀ hw.2

theorem main : H1 → H2 → H3 → H4 → OMA.R_ERH_extended_riemann_hypothesis_R2.H3 := by
  intro htransfer hdirichlet hcontinuation hremaining K _ _ hdegree hfull s hpos hlt hoff
  obtain ⟨Z, hZ, hreflect⟩ := hcontinuation K hdegree hfull
  have hright (w : ℂ) (hw : 1 / 2 < w.re) (hw' : w.re < 1) : Z w ≠ 0 := by
    by_cases he : ∃ n : ℕ, 0 < n ∧ Nonempty (K →ₐ[ℚ] CyclotomicField n ℚ)
    · obtain ⟨n, hn, ⟨e⟩⟩ := he
      let : NeZero n := ⟨hn.ne'⟩
      intro hz
      have hwpos : 0 < w.re := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hw
      have hwone : w ≠ 1 := fun he => by simp [he] at hw'
      obtain ⟨q, hq, χ, hχ, hzero⟩ := htransfer n K e Z hZ w hwpos hwone hz
      exact hdirichlet q χ hχ w hw hw' hzero
    · exact hremaining K hdegree he Z hZ w hw hw'
  apply reciprocal_of_nonzero hZ (fun he => by simp [he] at hlt)
  rcases lt_or_gt_of_ne hoff with hleft | hright'
  · intro hz
    apply hright (1 - s) _ _ (hreflect s hpos hlt hz)
    · rw [sub_re, one_re]
      linarith
    · rw [sub_re, one_re]
      linarith
  · exact hright s hright' hlt

end OMA.R_ERH_extended_riemann_hypothesis_R2_H3_R1
