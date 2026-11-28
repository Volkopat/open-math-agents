import OMAReductions.R_Erdos90_erdos_90_variants_sawin_explicit_R1_H3_R1
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Analysis.Calculus.MeanValue

-- Credit: @skhakim

/-!
# Norm Index on Ordinary Ideal Classes for Quadratic CM Extensions

We prove `OMA.R_Erdos90_erdos_90_variants_sawin_explicit_R1_H3_R1.H2`: for a totally real
number field `F` and a totally complex quadratic extension `K/F`, any class-group
homomorphism `T : ClassGroup (𝓞 K) →* ClassGroup (𝓞 F)` compatible with `Ideal.relNorm (𝓞 F)`
has `T.range.index ≤ 2`.

## Proof Overview

1. **Exponent-2 quotient & real characters**: For every nonzero ideal `I` of `𝓞 F`,
   `Ideal.relNorm (𝓞 F) (I.map _) = I ^ 2`, so `g ^ 2 ∈ H := T.range` for all
   `g : ClassGroup (𝓞 F)`. Thus `Cl(F) / H` is an elementary abelian 2-group of cardinality
   `m = H.index`, admitting `m` real `{±1}`-valued characters `χ_i : Cl(F) →* ℝ` trivial on `H`.
2. **Prime-by-prime Euler factor inequality**: For every nonzero prime ideal `p` of `𝓞 F`,
   `∑_{P | p} e(P|p) f(P|p) = [K : F] = 2`. Comparing local Euler factors gives
   `(∏_{P | p} (1 - NP^{-s})⁻¹)^m ≤ (∏_i (1 - χ_i([p]) Np^{-s})⁻¹)^2` for all `s > 1`.
3. **Finite Euler products**: Taking finite products over primes of norm `≤ X` and letting
   `X → ∞` yields `ζ_K(s)^m ≤ ζ_F(s)^2 * (∏_{i ≠ 0} L(s, χ_i))^2` for all `s > 1`.
4. **Weber ideal-class counting with `O(x^{1 - 1/n})` error**: Using `NormLeOne` and a
   Lipschitz-boundary lattice-point counting bound on `ℤ^n`, every ideal class `C` of the
   totally real field `F` satisfies `|A_C(x) - κ x| ≤ M x^{1 - 1/n}`. By discrete Abel
   summation, `|L(s, χ_i)|` is uniformly bounded on `s ∈ (1, 2]` for every nontrivial `χ_i`.
5. **Residue comparison at `s → 1⁺`**: Multiplying by `(s - 1)^m` and applying Mathlib's
   Dirichlet class number formula (`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`)
   forces `m ≤ 2`.
-/

namespace OMA.Proof_Erdos90_erdos_90_variants_sawin_explicit_R1_H3_R1_H2

open Filter Topology NumberField NumberField.InfinitePlace Ideal MeasureTheory
open scoped nonZeroDivisors Real Pointwise

/- ## Section 1: Real characters of a finite abelian group modulo an exponent-2 subgroup -/

section Characters

variable {G : Type*} [CommGroup G] [Finite G] (H : Subgroup G)

lemma zmod2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  fin_cases z
  · left; rfl
  · right; rfl

/-- Construct `H.index` real `{±1}`-valued characters on `G` trivial on `H`, assuming
every square lies in `H`. -/
lemma exists_real_characters_of_sq_mem (hsq : ∀ g : G, g ^ 2 ∈ H) :
    ∃ (d : ℕ) (χ : (Fin d → ZMod 2) → (G →* ℝ)),
      2 ^ d = H.index ∧
      (∀ g, χ 0 g = 1) ∧
      (∀ w g, χ w g = 1 ∨ χ w g = -1) ∧
      (∀ w₁ w₂ g, χ (w₁ + w₂) g = χ w₁ g * χ w₂ g) ∧
      (∀ w, ∀ g ∈ H, χ w g = 1) ∧
      (∀ g, g ∉ H → ∃ w, χ w g = -1) ∧
      (∀ w, w ≠ 0 → ∃ g, χ w g = -1) := by
  classical
  -- Work in the additive group V := Additive (G ⧸ H), which is a ZMod 2 vector space.
  let V := Additive (G ⧸ H)
  have hv2 : ∀ v : V, v + v = 0 := by
    intro v
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    change Additive.ofMul (Additive.toMul v * Additive.toMul v) = Additive.ofMul 1
    rw [← hg, ← QuotientGroup.mk_mul]
    congr 1
    rw [QuotientGroup.eq_one_iff]
    simpa [sq] using hsq g
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  let smul2 : ZMod 2 → V → V := fun c v => if c = 0 then 0 else v
  let _ : SMul (ZMod 2) V := ⟨smul2⟩
  let _ : Module (ZMod 2) V :=
    { one_smul := fun v => by
        change smul2 1 v = v
        simp [smul2]
      mul_smul := fun a b v => by
        change smul2 (a * b) v = smul2 a (smul2 b v)
        rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
          simp [smul2]
      smul_zero := fun a => by
        change smul2 a 0 = 0
        simp [smul2]
      smul_add := fun a v w => by
        change smul2 a (v + w) = smul2 a v + smul2 a w
        rcases zmod2_cases a with rfl | rfl <;> simp [smul2]
      add_smul := fun a b v => by
        change smul2 (a + b) v = smul2 a v + smul2 b v
        rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
          simp [smul2, hv2, h11]
      zero_smul := fun v => by
        change smul2 0 v = 0
        simp [smul2] }
  have hfinV : Finite V := by
    have : Finite (G ⧸ H) := Finite.of_surjective _ QuotientGroup.mk_surjective
    exact Finite.of_equiv (G ⧸ H) Additive.ofMul
  let _ : Fintype V := Fintype.ofFinite V
  let _ : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  have : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  let d := Module.finrank (ZMod 2) V
  let B : Module.Basis (Fin d) (ZMod 2) V := Module.finBasis (ZMod 2) V
  let qmap : G → V := fun g => Additive.ofMul (QuotientGroup.mk g)
  have hqmap_mul : ∀ g₁ g₂ : G, qmap (g₁ * g₂) = qmap g₁ + qmap g₂ := by
    intro g₁ g₂
    simp [qmap, QuotientGroup.mk_mul]
  have hqmap_one : qmap 1 = 0 := by simp [qmap]
  have hqmap_surj : Function.Surjective qmap := by
    intro v
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    exact ⟨g, by simp [qmap, hg]⟩
  let sign2 : ZMod 2 → ℝ := fun z => if z = 0 then 1 else -1
  have hsign2_add : ∀ a b : ZMod 2, sign2 (a + b) = sign2 a * sign2 b := by
    intro a b
    rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
      simp [sign2, h11]
  have hsign2_zero : sign2 0 = 1 := by simp [sign2]
  let dot : (Fin d → ZMod 2) → V → ZMod 2 := fun w v => ∑ j : Fin d, w j * B.repr v j
  have hdot_add_right : ∀ w v₁ v₂, dot w (v₁ + v₂) = dot w v₁ + dot w v₂ := by
    intro w v₁ v₂
    simp [dot, map_add, mul_add, Finset.sum_add_distrib]
  have hdot_add_left : ∀ w₁ w₂ v, dot (w₁ + w₂) v = dot w₁ v + dot w₂ v := by
    intro w₁ w₂ v
    simp [dot, add_mul, Finset.sum_add_distrib]
  let χ : (Fin d → ZMod 2) → (G →* ℝ) := fun w =>
    { toFun := fun g => sign2 (dot w (qmap g))
      map_one' := by simp [hqmap_one, dot, hsign2_zero]
      map_mul' := fun g₁ g₂ => by rw [hqmap_mul, hdot_add_right, hsign2_add] }
  refine ⟨d, χ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 2 ^ d = H.index
    have hcard : Fintype.card V = 2 ^ d := by
      rw [Fintype.card_congr B.equivFun.toEquiv, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    rw [← hcard, Subgroup.index_eq_card, Nat.card_eq_fintype_card]
    exact Fintype.card_congr Additive.toMul
  · intro g
    simp [χ, dot, sign2]
  · intro w g
    change sign2 (dot w (qmap g)) = 1 ∨ sign2 (dot w (qmap g)) = -1
    dsimp [sign2]
    split_ifs <;> simp
  · intro w₁ w₂ g
    change sign2 (dot (w₁ + w₂) (qmap g)) = sign2 (dot w₁ (qmap g)) * sign2 (dot w₂ (qmap g))
    rw [hdot_add_left, hsign2_add]
  · intro w g hg
    have hq : qmap g = 0 := by
      change Additive.ofMul (QuotientGroup.mk g) = Additive.ofMul 1
      rw [(QuotientGroup.eq_one_iff g).mpr hg]
    simp [χ, hq, dot, sign2]
  · intro g hg
    have hq : qmap g ≠ 0 := by
      intro h
      apply hg
      rw [← QuotientGroup.eq_one_iff]
      exact congrArg Additive.toMul h
    have hr : B.repr (qmap g) ≠ 0 := fun h => hq (B.repr.map_eq_zero_iff.mp h)
    have hex : ∃ j : Fin d, B.repr (qmap g) j ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hr
      ext j
      exact hall j
    obtain ⟨j₀, hj₀⟩ := hex
    have hj1 : B.repr (qmap g) j₀ = 1 := (zmod2_cases _).resolve_left hj₀
    refine ⟨Pi.single j₀ 1, ?_⟩
    change sign2 (dot (Pi.single j₀ 1) (qmap g)) = -1
    have hdot1 : dot (Pi.single j₀ 1) (qmap g) = 1 := by
      simp [dot, Pi.single_apply, hj1]
    rw [hdot1]
    simp [sign2]
  · intro w hw
    have hex : ∃ j : Fin d, w j ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hw (funext hall)
    obtain ⟨j₀, hj₀⟩ := hex
    have hj1 : w j₀ = 1 := (zmod2_cases _).resolve_left hj₀
    obtain ⟨g, hg⟩ := hqmap_surj (B j₀)
    refine ⟨g, ?_⟩
    change sign2 (dot w (qmap g)) = -1
    have hdot1 : dot w (qmap g) = 1 := by
      rw [hg]
      simp [dot, B.repr_self, Finsupp.single_apply, hj1]
    rw [hdot1]
    simp [sign2]

lemma sum_character_eq_zero {G : Type*} [CommGroup G] [Fintype G]
    (f : G →* ℝ) (hneg : ∃ g₁ : G, f g₁ = -1) :
    ∑ g : G, f g = 0 := by
  obtain ⟨g₁, hg₁⟩ := hneg
  have hshift : ∑ g : G, f (g * g₁) = ∑ g : G, f g :=
    Fintype.sum_equiv (Equiv.mulRight g₁) _ _ (fun _ => rfl)
  have hmul : ∑ g : G, f (g * g₁) = -(∑ g : G, f g) := by
    simp only [map_mul, hg₁, mul_neg_one, Finset.sum_neg_distrib]
  linarith

omit [Finite G] in
lemma prod_euler_factor_sq_of_neg {d : ℕ}
    (χ : (Fin d → ZMod 2) → (G →* ℝ))
    (hpm : ∀ w g, χ w g = 1 ∨ χ w g = -1)
    (hadd : ∀ w₁ w₂ g, χ (w₁ + w₂) g = χ w₁ g * χ w₂ g)
    {g : G} {w₁ : Fin d → ZMod 2} (hw₁ : χ w₁ g = -1)
    (u : ℝ) :
    (∏ w : Fin d → ZMod 2, (1 - χ w g * u)⁻¹) ^ 2 = ((1 - u ^ 2)⁻¹) ^ (2 ^ d) := by
  have hshift : ∏ w : Fin d → ZMod 2, (1 - χ (w + w₁) g * u)⁻¹ =
      ∏ w : Fin d → ZMod 2, (1 - χ w g * u)⁻¹ :=
    Fintype.prod_equiv (Equiv.addRight w₁) _ _ (fun _ => rfl)
  rw [sq]
  conv_lhs => rhs; rw [← hshift]
  rw [← Finset.prod_mul_distrib]
  have hterm : ∀ w : Fin d → ZMod 2,
      (1 - χ w g * u)⁻¹ * (1 - χ (w + w₁) g * u)⁻¹ = (1 - u ^ 2)⁻¹ := by
    intro w
    rw [hadd, hw₁, mul_neg_one, neg_mul, sub_neg_eq_add, ← mul_inv]
    congr 1
    rcases hpm w g with h | h <;> rw [h] <;> ring
  simp_rw [hterm, Finset.prod_const, Finset.card_univ, Fintype.card_fun, ZMod.card,
    Fintype.card_fin]

end Characters

/- ## Section 2: Quadratic ideal norm, prime splitting, and local Euler inequality -/

section QuadraticNorm

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]

lemma finrank_ringOfIntegers_eq_two :
    Module.finrank (𝓞 F) (𝓞 K) = 2 := by
  rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 K) K]
  exact Algebra.IsQuadraticExtension.finrank_eq_two F K

lemma sq_mem_range_of_relNorm_spec
    (T : ClassGroup (𝓞 K) →* ClassGroup (𝓞 F))
    (hT : ∀ I : (Ideal (𝓞 K))⁰, ∃ J : (Ideal (𝓞 F))⁰,
      J.val = Ideal.relNorm (𝓞 F) I.val ∧ T (ClassGroup.mk0 I) = ClassGroup.mk0 J)
    (g : ClassGroup (𝓞 F)) : g ^ 2 ∈ T.range := by
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective g
  let IK : Ideal (𝓞 K) := I.val.map (algebraMap (𝓞 F) (𝓞 K))
  have hrel : Ideal.relNorm (𝓞 F) IK = I.val ^ 2 := by
    dsimp [IK]
    rw [Ideal.relNorm_algebraMap (𝓞 K) I.val, finrank_ringOfIntegers_eq_two]
  have hI_ne : I.val ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have hIK_ne : IK ≠ ⊥ := by
    intro hbot
    have h0 : Ideal.relNorm (𝓞 F) IK = ⊥ := by rw [hbot, Ideal.relNorm_bot]
    rw [hrel] at h0
    exact pow_ne_zero 2 hI_ne h0
  let IK0 : (Ideal (𝓞 K))⁰ := ⟨IK, mem_nonZeroDivisors_iff_ne_zero.mpr hIK_ne⟩
  obtain ⟨J, hJval, hTJ⟩ := hT IK0
  have hJeq : J = I ^ 2 := by
    apply Subtype.ext
    rw [hJval, hrel]
    rfl
  refine ⟨ClassGroup.mk0 IK0, ?_⟩
  rw [hTJ, hJeq, map_pow]

/-- For a nonzero prime `p` of `𝓞 F` in a quadratic extension `K/F`, either `p` has a prime
above it of inertia degree 1 (so `[p] ∈ T.range`, at most 2 primes lie over `p`, all of norm
`absNorm p`), or a unique inert prime `P` lies over `p` with `absNorm P = (absNorm p)^2`. -/
lemma primesOver_quadratic_dichotomy
    (T : ClassGroup (𝓞 K) →* ClassGroup (𝓞 F))
    (hT : ∀ I : (Ideal (𝓞 K))⁰, ∃ J : (Ideal (𝓞 F))⁰,
      J.val = Ideal.relNorm (𝓞 F) I.val ∧ T (ClassGroup.mk0 I) = ClassGroup.mk0 J)
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    (ClassGroup.mk0 ⟨p.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr p.ne_bot⟩ ∈ T.range ∧
      (IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K)).card ≤ 2 ∧
      ∀ P ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K),
        Ideal.absNorm P = Ideal.absNorm p.asIdeal) ∨
    (∃ P₀ : Ideal (𝓞 K), IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K) = {P₀} ∧
      Ideal.absNorm P₀ = (Ideal.absNorm p.asIdeal) ^ 2) := by
  classical
  have : p.asIdeal.IsPrime := p.isPrime
  have : p.asIdeal.IsMaximal := p.isMaximal
  let _ : Fintype (p.asIdeal.primesOver (𝓞 K)) :=
    (IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 K)).fintype
  have hsum_sub :
      ∑ q : p.asIdeal.primesOver (𝓞 K), q.1.ramificationIdx (𝓞 F) * q.1.inertiaDeg (𝓞 F) = 2 := by
    rw [Ideal.sum_ramification_inertia_eq_finrank, finrank_ringOfIntegers_eq_two]
  let S := IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K)
  have hS_eq : (S : Set (Ideal (𝓞 K))) = p.asIdeal.primesOver (𝓞 K) :=
    IsDedekindDomain.coe_primesOverFinset (B := 𝓞 K) p.ne_bot
  have hsum : ∑ P ∈ S, P.ramificationIdx (𝓞 F) * P.inertiaDeg (𝓞 F) = 2 := by
    rw [← hsum_sub]
    symm
    refine Finset.sum_bij (fun (q : p.asIdeal.primesOver (𝓞 K)) _ => q.1) ?_ ?_ ?_ ?_
    · intro q _
      exact (IsDedekindDomain.mem_primesOverFinset_iff (B := 𝓞 K) p.ne_bot).mpr q.2
    · intro q₁ _ q₂ _ h
      exact Subtype.ext h
    · intro P hP
      exact ⟨⟨P, (IsDedekindDomain.mem_primesOverFinset_iff (B := 𝓞 K) p.ne_bot).mp hP⟩,
        Finset.mem_univ _, rfl⟩
    · intro q _; rfl
  have hP_props : ∀ P ∈ S, P.IsPrime ∧ P.LiesOver p.asIdeal ∧ P.IsMaximal ∧ P ≠ ⊥ ∧
      1 ≤ P.ramificationIdx (𝓞 F) ∧ 1 ≤ P.inertiaDeg (𝓞 F) ∧
      Ideal.relNorm (𝓞 F) P = p.asIdeal ^ P.inertiaDeg (𝓞 F) ∧
      Ideal.absNorm P = (Ideal.absNorm p.asIdeal) ^ P.inertiaDeg (𝓞 F) := by
    intro P hP
    have hmem : P ∈ p.asIdeal.primesOver (𝓞 K) :=
      (IsDedekindDomain.mem_primesOverFinset_iff (B := 𝓞 K) p.ne_bot).mp hP
    have : P.IsPrime := hmem.1
    have : P.LiesOver p.asIdeal := hmem.2
    have : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P p.asIdeal
    have hne : P ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver p.ne_bot hmem
    have he : 1 ≤ P.ramificationIdx (𝓞 F) := Ideal.ramificationIdx_pos (R := 𝓞 F) (q := P)
    have hf : 1 ≤ P.inertiaDeg (𝓞 F) := Ideal.inertiaDeg_pos P (𝓞 F)
    have hrel : Ideal.relNorm (𝓞 F) P = p.asIdeal ^ P.inertiaDeg (𝓞 F) :=
      Ideal.relNorm_eq_pow_of_isMaximal P p.asIdeal
    have habs : Ideal.absNorm P = (Ideal.absNorm p.asIdeal) ^ P.inertiaDeg (𝓞 F) := by
      rw [← Ideal.absNorm_relNorm (R := 𝓞 F) (S := 𝓞 K) P, hrel, map_pow]
    exact ⟨hmem.1, hmem.2, inferInstance, hne, he, hf, hrel, habs⟩
  have hSne : S.Nonempty := by
    have hpos : 1 ≤ (p.asIdeal.primesOver (𝓞 K)).ncard :=
      IsDedekindDomain.one_le_primesOver_ncard p.asIdeal (𝓞 K)
    rw [← hS_eq, Set.ncard_coe_finset] at hpos
    exact Finset.card_pos.mp hpos
  by_cases hiner : ∃ P₀ ∈ S, 2 ≤ P₀.inertiaDeg (𝓞 F)
  · right
    obtain ⟨P₀, hP₀S, hf₀⟩ := hiner
    have hp0 := hP_props P₀ hP₀S
    have hterm_ge : 2 ≤ P₀.ramificationIdx (𝓞 F) * P₀.inertiaDeg (𝓞 F) := by
      have := hp0.2.2.2.2.1; nlinarith
    have hrest_zero : ∑ P ∈ S.erase P₀, P.ramificationIdx (𝓞 F) * P.inertiaDeg (𝓞 F) = 0 := by
      have hadd := Finset.add_sum_erase S (fun P => P.ramificationIdx (𝓞 F) * P.inertiaDeg (𝓞 F)) hP₀S
      omega
    have hS_sing : S = {P₀} := by
      ext P
      simp only [Finset.mem_singleton]
      constructor
      · intro hPS
        by_contra hne
        have hmem_e : P ∈ S.erase P₀ := Finset.mem_erase.mpr ⟨hne, hPS⟩
        have hle := Finset.single_le_sum (f := fun Q => Q.ramificationIdx (𝓞 F) * Q.inertiaDeg (𝓞 F))
          (fun _ _ => Nat.zero_le _) hmem_e
        have hpP := hP_props P hPS
        have hpos : 1 ≤ P.ramificationIdx (𝓞 F) * P.inertiaDeg (𝓞 F) :=
          Nat.mul_pos hpP.2.2.2.2.1 hpP.2.2.2.2.2.1
        omega
      · rintro rfl; exact hP₀S
    have hprod_eq : P₀.ramificationIdx (𝓞 F) * P₀.inertiaDeg (𝓞 F) = 2 := by
      rw [hS_sing, Finset.sum_singleton] at hsum; exact hsum
    have hf_eq : P₀.inertiaDeg (𝓞 F) = 2 := by
      have := hp0.2.2.2.2.1; nlinarith
    refine ⟨P₀, hS_sing, ?_⟩
    rw [hp0.2.2.2.2.2.2.2, hf_eq]
  · left
    push Not at hiner
    have hf1 : ∀ P ∈ S, P.inertiaDeg (𝓞 F) = 1 := fun P hP => by
      have := (hP_props P hP).2.2.2.2.2.1
      have := hiner P hP
      omega
    obtain ⟨P₀, hP₀S⟩ := hSne
    have hp0 := hP_props P₀ hP₀S
    have hrel0 : Ideal.relNorm (𝓞 F) P₀ = p.asIdeal := by
      rw [hp0.2.2.2.2.2.2.1, hf1 P₀ hP₀S, pow_one]
    have hmemH : ClassGroup.mk0 ⟨p.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr p.ne_bot⟩ ∈ T.range := by
      let P0 : (Ideal (𝓞 K))⁰ := ⟨P₀, mem_nonZeroDivisors_iff_ne_zero.mpr hp0.2.2.2.1⟩
      obtain ⟨J, hJval, hTJ⟩ := hT P0
      have hJeq : J = ⟨p.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr p.ne_bot⟩ := by
        apply Subtype.ext
        rw [hJval, hrel0]
      exact ⟨ClassGroup.mk0 P0, by rw [hTJ, hJeq]⟩
    have hcard : S.card ≤ 2 := by
      calc S.card = ∑ _P ∈ S, 1 := by simp
        _ ≤ ∑ P ∈ S, P.ramificationIdx (𝓞 F) * P.inertiaDeg (𝓞 F) :=
          Finset.sum_le_sum fun P hP => Nat.mul_pos (hP_props P hP).2.2.2.2.1 (hP_props P hP).2.2.2.2.2.1
        _ = 2 := hsum
    refine ⟨hmemH, hcard, fun P hP => ?_⟩
    rw [(hP_props P hP).2.2.2.2.2.2.2, hf1 P hP, pow_one]

/-- Prime-by-prime local Euler factor inequality for any `s > 1`. -/
lemma local_euler_factor_ineq
    (T : ClassGroup (𝓞 K) →* ClassGroup (𝓞 F))
    (hT : ∀ I : (Ideal (𝓞 K))⁰, ∃ J : (Ideal (𝓞 F))⁰,
      J.val = Ideal.relNorm (𝓞 F) I.val ∧ T (ClassGroup.mk0 I) = ClassGroup.mk0 J)
    {d : ℕ} (χ : (Fin d → ZMod 2) → (ClassGroup (𝓞 F) →* ℝ))
    (hcard : 2 ^ d = T.range.index)
    (hpm : ∀ w g, χ w g = 1 ∨ χ w g = -1)
    (hadd : ∀ w₁ w₂ g, χ (w₁ + w₂) g = χ w₁ g * χ w₂ g)
    (htriv : ∀ w, ∀ g ∈ T.range, χ w g = 1)
    (hneg : ∀ g, g ∉ T.range → ∃ w, χ w g = -1)
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    {s : ℝ} (hs : 1 < s) :
    (∏ P ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K),
      (1 - (Ideal.absNorm P : ℝ) ^ (-s))⁻¹) ^ T.range.index ≤
    (∏ w : Fin d → ZMod 2,
      (1 - χ w (ClassGroup.mk0 ⟨p.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr p.ne_bot⟩) *
        (Ideal.absNorm p.asIdeal : ℝ) ^ (-s))⁻¹) ^ 2 := by
  let g : ClassGroup (𝓞 F) :=
    ClassGroup.mk0 ⟨p.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr p.ne_bot⟩
  let u : ℝ := (Ideal.absNorm p.asIdeal : ℝ) ^ (-s)
  have hNp_gt1 : 1 < Ideal.absNorm p.asIdeal := by
    have hne0 : Ideal.absNorm p.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot
    have hne1 : Ideal.absNorm p.asIdeal ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr p.isPrime.ne_top
    omega
  have hu0 : 0 < u := Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < Ideal.absNorm p.asIdeal)) _
  have hu1 : u < 1 := by
    dsimp [u]
    rw [Real.rpow_neg (by positivity)]
    exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by exact_mod_cast hNp_gt1) (by linarith))
  have h1u_pos : 0 < 1 - u := sub_pos.mpr hu1
  have hinv_ge1 : 1 ≤ (1 - u)⁻¹ := (one_le_inv₀ h1u_pos).mpr (by linarith)
  have hrhs_inH : g ∈ T.range →
      (∏ w : Fin d → ZMod 2, (1 - χ w g * u)⁻¹) ^ 2 = ((1 - u)⁻¹ ^ 2) ^ T.range.index := by
    intro hg
    have h1 : ∏ w : Fin d → ZMod 2, (1 - χ w g * u)⁻¹ = (1 - u)⁻¹ ^ T.range.index := by
      simp_rw [htriv _ g hg, one_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fun,
        ZMod.card, Fintype.card_fin, hcard]
    rw [h1, ← pow_mul, mul_comm, pow_mul]
  rcases primesOver_quadratic_dichotomy T hT p with ⟨hgH, hle2, hnorm⟩ | ⟨P₀, hsing, hnorm⟩
  · -- Case 1: split or ramified
    rw [hrhs_inH hgH]
    have hlhs : ∏ P ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K),
          (1 - (Ideal.absNorm P : ℝ) ^ (-s))⁻¹ =
        (1 - u)⁻¹ ^ (IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K)).card := by
      have : ∀ P ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K),
          (1 - (Ideal.absNorm P : ℝ) ^ (-s))⁻¹ = (1 - u)⁻¹ := fun P hP => by
        rw [hnorm P hP]
      rw [Finset.prod_congr rfl this, Finset.prod_const]
    rw [hlhs]
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hinv_ge1 hle2) _
  · -- Case 2: inert
    have hu2 : (Ideal.absNorm P₀ : ℝ) ^ (-s) = u ^ 2 := by
      rw [hnorm, Nat.cast_pow]
      dsimp [u]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast,
        ← Real.rpow_mul (by positivity), mul_comm]
    rw [hsing, Finset.prod_singleton, hu2]
    by_cases hgH : g ∈ T.range
    · rw [hrhs_inH hgH]
      have hstep : (1 - u ^ 2)⁻¹ ≤ (1 - u)⁻¹ ^ 2 := by
        rw [inv_pow]
        have hpos2 : 0 < (1 - u) ^ 2 := sq_pos_of_pos h1u_pos
        exact inv_anti₀ hpos2 (by nlinarith)
      exact pow_le_pow_left₀ (inv_nonneg.mpr (by nlinarith)) hstep _
    · obtain ⟨w₁, hw₁⟩ := hneg g hgH
      rw [prod_euler_factor_sq_of_neg χ hpm hadd hw₁ u, hcard]

end QuadraticNorm

/- ## Section 3: Lattice-point counting with Lipschitz boundary and Weber's theorem -/

section LatticeCounting

/-- A finite product of bounded Lipschitz functions on a set is Lipschitz on that set. -/
lemma exists_lipschitzOnWith_finset_prod {α β : Type*} [PseudoMetricSpace α]
    (s : Set α) (t : Finset β) (f : β → α → ℝ)
    (hlip : ∀ i ∈ t, ∃ L : NNReal, LipschitzOnWith L (f i) s)
    (hbdd : ∀ i ∈ t, ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ s, |f i x| ≤ M) :
    ∃ L : NNReal, LipschitzOnWith L (fun x => ∏ i ∈ t, f i x) s := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    refine ⟨0, ?_⟩
    simp only [Finset.prod_empty]
    exact (LipschitzWith.const 1).lipschitzOnWith
  | @insert a t ha ih =>
    obtain ⟨La, hLa⟩ := hlip a (Finset.mem_insert_self a t)
    obtain ⟨Ma, hMa0, hMa⟩ := hbdd a (Finset.mem_insert_self a t)
    obtain ⟨Lt, hLt⟩ := ih (fun i hi => hlip i (Finset.mem_insert_of_mem hi))
      (fun i hi => hbdd i (Finset.mem_insert_of_mem hi))
    have hMt_ex : ∃ Mt : ℝ, 0 ≤ Mt ∧ ∀ x ∈ s, |∏ i ∈ t, f i x| ≤ Mt := by
      choose M hM0 hM using fun i : t => hbdd i.1 (Finset.mem_insert_of_mem i.2)
      refine ⟨∏ i : t, M i, Finset.prod_nonneg (fun i _ => hM0 i), fun x hx => ?_⟩
      rw [Finset.abs_prod, ← Finset.prod_coe_sort t]
      exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hM i x hx)
    obtain ⟨Mt, hMt0, hMt⟩ := hMt_ex
    refine ⟨⟨Ma, hMa0⟩ * Lt + ⟨Mt, hMt0⟩ * La, ?_⟩
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    simp only [Finset.prod_insert ha, Real.dist_eq, NNReal.coe_add]
    have h1 := (lipschitzOnWith_iff_dist_le_mul.mp hLa) x hx y hy
    have h2 := (lipschitzOnWith_iff_dist_le_mul.mp hLt) x hx y hy
    simp only [Real.dist_eq] at h1 h2
    calc |f a x * ∏ i ∈ t, f i x - f a y * ∏ i ∈ t, f i y|
        = |f a x * (∏ i ∈ t, f i x - ∏ i ∈ t, f i y) +
            (f a x - f a y) * ∏ i ∈ t, f i y| := by ring_nf
      _ ≤ |f a x| * |∏ i ∈ t, f i x - ∏ i ∈ t, f i y| +
            |f a x - f a y| * |∏ i ∈ t, f i y| := by
          calc _ ≤ |f a x * (∏ i ∈ t, f i x - ∏ i ∈ t, f i y)| +
                |(f a x - f a y) * ∏ i ∈ t, f i y| := abs_add_le _ _
            _ = _ := by rw [abs_mul, abs_mul]
      _ ≤ Ma * (↑Lt * dist x y) + (↑La * dist x y) * Mt := by
          gcongr
          · exact hMa x hx
          · exact hMt y hy
      _ = (Ma * ↑Lt + Mt * ↑La) * dist x y := by ring

lemma exists_lipschitzOnWith_rpow_const {a : ℝ} (ha : 0 < a) :
    ∃ L : NNReal, LipschitzOnWith L (fun t : ℝ => a ^ t) (Set.Icc 0 1) := by
  let M : ℝ := |Real.log a| * max 1 a
  have hM0 : 0 ≤ M := by positivity
  let Mnn : NNReal := ⟨M, hM0⟩
  refine ⟨Mnn, lipschitzOnWith_iff_dist_le_mul.mpr ?_⟩
  have hbound : ∀ x y : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → y ∈ Set.Icc (0 : ℝ) 1 → x < y →
      |a ^ y - a ^ x| ≤ M * (y - x) := by
    intro x y hx hy hxy
    have hfn : (fun t : ℝ => a ^ t) = (fun t : ℝ => Real.exp (t * Real.log a)) := by
      ext t; rw [Real.rpow_def_of_pos ha, mul_comm]
    have hcont : ContinuousOn (fun t : ℝ => a ^ t) (Set.Icc x y) := by
      rw [hfn]; fun_prop
    have hderiv : ∀ t ∈ Set.Ioo x y, HasDerivAt (fun t : ℝ => a ^ t) (a ^ t * Real.log a) t := by
      intro t _
      rw [hfn]
      have h1 : HasDerivAt (fun u : ℝ => Real.exp (u * Real.log a))
          (Real.exp (t * Real.log a) * (1 * Real.log a)) t :=
        ((hasDerivAt_id t).mul_const (Real.log a)).exp
      simpa [Real.rpow_def_of_pos ha, mul_comm] using h1
    obtain ⟨c, hc, hce⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => a ^ t) _ hxy hcont hderiv
    have hsub : a ^ y - a ^ x = (a ^ c * Real.log a) * (y - x) := by
      have hne : y - x ≠ 0 := (sub_pos.mpr hxy).ne'
      rw [eq_div_iff hne] at hce
      exact hce.symm
    have hc_mem : c ∈ Set.Icc (0 : ℝ) 1 := ⟨le_trans hx.1 hc.1.le, le_trans hc.2.le hy.2⟩
    have hpow : a ^ c ≤ max 1 a := by
      rcases le_or_gt 1 a with h1 | h1
      · calc a ^ c ≤ a ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hc_mem.2
          _ = a := Real.rpow_one a
          _ ≤ max 1 a := le_max_right _ _
      · calc a ^ c ≤ a ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_ge ha h1.le hc_mem.1
          _ = 1 := Real.rpow_zero a
          _ ≤ max 1 a := le_max_left _ _
    rw [hsub, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg ha.le c),
      abs_of_pos (sub_pos.mpr hxy)]
    have hle : a ^ c * |Real.log a| ≤ M := by
      dsimp [M]; rw [mul_comm]; gcongr
    exact mul_le_mul_of_nonneg_right hle (sub_pos.mpr hxy).le
  intro x hx y hy
  simp only [Real.dist_eq]
  change |a ^ x - a ^ y| ≤ M * |x - y|
  rcases lt_trichotomy x y with hlt | rfl | hgt
  · rw [abs_sub_comm (a ^ x), abs_sub_comm x, abs_of_pos (sub_pos.mpr hlt)]
    exact hbound x y hx hy hlt
  · simp
  · rw [abs_of_pos (sub_pos.mpr hgt)]
    exact hbound y x hy hx hgt

/-- Elementary lattice-point counting error for a bounded measurable set `S ⊆ (ι → ℝ)` whose
frontier is covered by finitely many Lipschitz images of the `(n - 1)`-dimensional unit cube. -/
lemma lattice_card_sub_volume_le
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {S : Set (ι → ℝ)} (hSbdd : Bornology.IsBounded S)
    {M : ℕ} (L : NNReal)
    (f : Fin M → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ))
    (hlip : ∀ k, LipschitzOnWith L (f k)
      (Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1))
    (hcov : frontier S ⊆ ⋃ k : Fin M, f k '' (Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      |(Nat.card ((R • S) ∩ Set.range (fun z : ι → ℤ => fun i => (z i : ℝ)) : Set (ι → ℝ)) : ℝ) -
        volume.real S * R ^ Fintype.card ι| ≤ C * R ^ (Fintype.card ι - 1) := by
  classical
  let n := Fintype.card ι
  let cube : Set (Fin (n - 1) → ℝ) := Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1
  let castZ : (ι → ℤ) → (ι → ℝ) := fun z i => (z i : ℝ)
  have hcastZ_inj : Function.Injective castZ := by
    intro z₁ z₂ h
    ext i
    have hi : (z₁ i : ℝ) = (z₂ i : ℝ) := congrFun h i
    exact_mod_cast hi
  let box : (ι → ℤ) → Set (ι → ℝ) :=
    fun z => Set.univ.pi fun i => Set.Ico (z i : ℝ) ((z i : ℝ) + 1)
  have hbox_meas : ∀ z, MeasurableSet (box z) :=
    fun z => MeasurableSet.univ_pi fun _ => measurableSet_Ico
  have hbox_vol : ∀ z, volume (box z) = 1 := by
    intro z
    rw [volume_pi, Measure.pi_pi]
    simp [Real.volume_Ico]
  have hbox_disj : Pairwise (fun z₁ z₂ => Disjoint (box z₁) (box z₂)) := by
    intro z₁ z₂ hne
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    apply hne
    ext i
    have h1 := hx₁ i (Set.mem_univ i)
    have h2 := hx₂ i (Set.mem_univ i)
    have h1' : (z₁ i : ℝ) < (z₂ i : ℝ) + 1 := lt_of_le_of_lt h1.1 h2.2
    have h2' : (z₂ i : ℝ) < (z₁ i : ℝ) + 1 := lt_of_le_of_lt h2.1 h1.2
    have hz1 : z₁ i ≤ z₂ i := by
      have : z₁ i < z₂ i + 1 := by exact_mod_cast h1'
      omega
    have hz2 : z₂ i ≤ z₁ i := by
      have : z₂ i < z₁ i + 1 := by exact_mod_cast h2'
      omega
    omega
  have hbox_cover : ∀ x : ι → ℝ, ∃ z : ι → ℤ, x ∈ box z := by
    intro x
    refine ⟨fun i => ⌊x i⌋, fun i _ => ⟨Int.floor_le (x i), Int.lt_floor_add_one (x i)⟩⟩
  have hcast_mem_box : ∀ z, castZ z ∈ box z := fun z i _ => ⟨le_rfl, by linarith⟩
  -- Bounding box for S
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp hSbdd
  let B' := max B 0
  have hB'0 : 0 ≤ B' := le_max_right _ _
  have hBS : ∀ x ∈ S, ∀ i, |x i| ≤ B' := fun x hx i => by
    have := (pi_norm_le_iff_of_nonneg hB'0).mp ((hB x hx).trans (le_max_left _ _)) i
    simpa [Real.norm_eq_abs] using this
  -- Constant for lattice points near a fixed point
  let K : ℕ := 2 * (Nat.ceil (1 + (L : ℝ)) + 2) + 1
  let C : ℝ := (M : ℝ) * (K : ℝ) ^ n * (2 : ℝ) ^ (n - 1)
  refine ⟨C, by positivity, fun R hR => ?_⟩
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  -- Finite superset of all z whose box hits R • S
  let Rbox : ℤ := ⌈R * B'⌉ + 2
  let Zall : Finset (ι → ℤ) := Fintype.piFinset fun _ : ι => Finset.Icc (-Rbox) Rbox
  have hhit_mem_Zall : ∀ z : ι → ℤ, ((box z) ∩ (R • S)).Nonempty → z ∈ Zall := by
    rintro z ⟨x, hxz, ⟨y, hyS, rfl⟩⟩
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have hxi : (z i : ℝ) ≤ R * y i ∧ R * y i < (z i : ℝ) + 1 := hxz i (Set.mem_univ i)
    have hyi : |y i| ≤ B' := hBS y hyS i
    have hRyi : |R * y i| ≤ R * B' := by
      rw [abs_mul, abs_of_pos hRpos]
      exact mul_le_mul_of_nonneg_left hyi hRpos.le
    have hle1 : (z i : ℝ) ≤ R * B' := le_trans hxi.1 (le_trans (le_abs_self _) hRyi)
    have hle2 : -(R * B') - 1 < (z i : ℝ) := by
      have : -(R * B') ≤ R * y i := neg_le_of_abs_le hRyi
      linarith [hxi.2]
    have hceil : R * B' ≤ (⌈R * B'⌉ : ℝ) := Int.le_ceil _
    have hRbox_val : (Rbox : ℝ) = (⌈R * B'⌉ : ℝ) + 2 := by dsimp [Rbox]; push_cast; ring
    constructor
    · have : ((-Rbox : ℤ) : ℝ) < (z i : ℝ) := by
        rw [Int.cast_neg, hRbox_val]; linarith [hle2, hceil]
      exact le_of_lt (by exact_mod_cast this)
    · have : (z i : ℝ) ≤ (Rbox : ℝ) := by
        rw [hRbox_val]; linarith [hle1, hceil]
      exact_mod_cast this
  let Z_in : Finset (ι → ℤ) := Zall.filter fun z => box z ⊆ R • S
  let Z_pt : Finset (ι → ℤ) := Zall.filter fun z => castZ z ∈ R • S
  let Z_hit : Finset (ι → ℤ) := Zall.filter fun z => ((box z) ∩ (R • S)).Nonempty
  have h_in_pt : Z_in ⊆ Z_pt := by
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, hz.2 (hcast_mem_box z)⟩
  have h_pt_hit : Z_pt ⊆ Z_hit := by
    intro z hz
    rw [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, ⟨castZ z, hcast_mem_box z, hz.2⟩⟩
  -- Identify Nat.card with Z_pt.card
  have hcard_eq :
      Nat.card ((R • S) ∩ Set.range castZ : Set (ι → ℝ)) = Z_pt.card := by
    rw [Nat.card_coe_set_eq]
    have heq : ((R • S) ∩ Set.range castZ : Set (ι → ℝ)) = castZ '' (Z_pt : Set (ι → ℤ)) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_image, Finset.mem_coe,
        Finset.mem_filter, Z_pt]
      constructor
      · rintro ⟨hx, z, rfl⟩
        exact ⟨z, ⟨hhit_mem_Zall z ⟨castZ z, hcast_mem_box z, hx⟩, hx⟩, rfl⟩
      · rintro ⟨z, ⟨_, hz⟩, rfl⟩
        exact ⟨hz, z, rfl⟩
    rw [heq, Set.ncard_image_of_injective _ hcastZ_inj, Set.ncard_coe_finset]
  -- Volume sandwich
  have hvol_smul : volume.real (R • S) = volume.real S * R ^ n := by
    rw [measureReal_def, measureReal_def, Measure.addHaar_smul volume R S,
      Module.finrank_pi, Fintype.card_eq_nat_card, Nat.card_eq_fintype_card,
      abs_of_pos (pow_pos hRpos _), ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hRpos.le _),
      mul_comm]
  have hvol_le_hit : volume (R • S) ≤ (Z_hit.card : ENNReal) := by
    have hsub : R • S ⊆ ⋃ z ∈ Z_hit, box z := by
      intro x hx
      obtain ⟨z, hxz⟩ := hbox_cover x
      refine Set.mem_biUnion ?_ hxz
      rw [Finset.mem_coe, Finset.mem_filter]
      exact ⟨hhit_mem_Zall z ⟨x, hxz, hx⟩, ⟨x, hxz, hx⟩⟩
    calc volume (R • S) ≤ volume (⋃ z ∈ Z_hit, box z) := measure_mono hsub
      _ = ∑ z ∈ Z_hit, volume (box z) :=
          measure_biUnion_finset (fun z₁ _ z₂ _ hne => hbox_disj hne) (fun z _ => hbox_meas z)
      _ = (Z_hit.card : ENNReal) := by simp [hbox_vol]
  have hin_le_vol : (Z_in.card : ENNReal) ≤ volume (R • S) := by
    have hsub : ⋃ z ∈ Z_in, box z ⊆ R • S := Set.iUnion₂_subset fun z hz =>
      (Finset.mem_filter.mp hz).2
    calc (Z_in.card : ENNReal) = ∑ z ∈ Z_in, volume (box z) := by simp [hbox_vol]
      _ = volume (⋃ z ∈ Z_in, box z) :=
          (measure_biUnion_finset (fun z₁ _ z₂ _ hne => hbox_disj hne) (fun z _ => hbox_meas z)).symm
      _ ≤ volume (R • S) := measure_mono hsub
  have hvol_ne_top : volume (R • S) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) hvol_le_hit
  have hin_real : (Z_in.card : ℝ) ≤ volume.real (R • S) := by
    rw [measureReal_def, ← ENNReal.toReal_natCast]
    exact ENNReal.toReal_mono hvol_ne_top hin_le_vol
  have hhit_real : volume.real (R • S) ≤ (Z_hit.card : ℝ) := by
    rw [measureReal_def, ← ENNReal.toReal_natCast]
    exact ENNReal.toReal_mono (ENNReal.natCast_ne_top _) hvol_le_hit
  have hpt_ge : (Z_in.card : ℝ) ≤ (Z_pt.card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card h_in_pt)
  have hpt_le : (Z_pt.card : ℝ) ≤ (Z_hit.card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card h_pt_hit)
  have habs_le_sdiff : |(Z_pt.card : ℝ) - volume.real S * R ^ n| ≤ ((Z_hit \ Z_in).card : ℝ) := by
    rw [← hvol_smul]
    have hsdiff : ((Z_hit \ Z_in).card : ℝ) = (Z_hit.card : ℝ) - (Z_in.card : ℝ) := by
      have hsub : Z_in ⊆ Z_hit := h_in_pt.trans h_pt_hit
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Nat.cast_sub (Finset.card_le_card hsub)]
    rw [hsdiff, abs_le]
    constructor <;> linarith
  rw [hcard_eq]
  refine habs_le_sdiff.trans ?_
  -- Every z ∈ Z_hit \ Z_in has box z intersecting frontier (R • S) = R • frontier S
  have hbox_frontier : ∀ z ∈ Z_hit \ Z_in, ∃ y ∈ frontier S, R • y ∈ box z := by
    intro z hz
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter] at hz
    obtain ⟨⟨_, ⟨p, hpbox, hpS⟩⟩, hnot⟩ := hz
    have hnot_sub : ¬ box z ⊆ R • S := fun h => hnot ⟨hhit_mem_Zall z ⟨p, hpbox, hpS⟩, h⟩
    rw [Set.not_subset] at hnot_sub
    obtain ⟨q, hqbox, hqS⟩ := hnot_sub
    let γ : ℝ → (ι → ℝ) := fun t => (1 - t) • p + t • q
    have hγ_cont : Continuous γ :=
      ((continuous_const.sub continuous_id).smul continuous_const).add
        (continuous_id.smul continuous_const)
    have hγ_box : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ box z := by
      intro t ht i _
      have hpi := hpbox i (Set.mem_univ i)
      have hqi := hqbox i (Set.mem_univ i)
      have ht0 : 0 ≤ 1 - t := by linarith [ht.2]
      have ht1 : 0 ≤ t := ht.1
      change (z i : ℝ) ≤ (1 - t) * p i + t * q i ∧ (1 - t) * p i + t * q i < (z i : ℝ) + 1
      constructor
      · have h1 : (1 - t) * (z i : ℝ) ≤ (1 - t) * p i := mul_le_mul_of_nonneg_left hpi.1 ht0
        have h2 : t * (z i : ℝ) ≤ t * q i := mul_le_mul_of_nonneg_left hqi.1 ht1
        linarith
      · rcases eq_or_lt_of_le ht1 with rfl | ht_pos
        · simpa using hpi.2
        · have h1 : (1 - t) * p i ≤ (1 - t) * ((z i : ℝ) + 1) :=
            mul_le_mul_of_nonneg_left hpi.2.le ht0
          have h2 : t * q i < t * ((z i : ℝ) + 1) :=
            mul_lt_mul_of_pos_left hqi.2 ht_pos
          linarith
    let T : Set ℝ := {t ∈ Set.Icc (0 : ℝ) 1 | γ t ∈ R • S}
    have hTne : T.Nonempty := ⟨0, ⟨⟨le_rfl, zero_le_one⟩, by simpa [γ] using hpS⟩⟩
    have hTbdd : BddAbove T := ⟨1, fun _ ht => ht.1.2⟩
    let t0 : ℝ := sSup T
    have ht0_mem : t0 ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨le_csSup hTbdd ⟨⟨le_rfl, zero_le_one⟩, by simpa [γ] using hpS⟩,
        csSup_le hTne fun _ ht => ht.1.2⟩
    have hγt0_cl : γ t0 ∈ closure (R • S) := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      have hcont_at := Metric.continuousAt_iff.mp (hγ_cont.continuousAt (x := t0)) ε hε
      obtain ⟨δ, hδ, hδγ⟩ := hcont_at
      obtain ⟨t, htT, htt0⟩ := exists_lt_of_lt_csSup hTne (show t0 - δ < t0 by linarith)
      have ht_le : t ≤ t0 := le_csSup hTbdd htT
      refine ⟨γ t, htT.2, ?_⟩
      rw [dist_comm]
      exact hδγ (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    have hγt0_nint : γ t0 ∉ interior (R • S) := by
      intro hint
      have hopen : IsOpen (γ ⁻¹' interior (R • S)) := isOpen_interior.preimage hγ_cont
      obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen t0 hint
      have ht0_lt1 : t0 < 1 := by
        rcases lt_or_eq_of_le ht0_mem.2 with hlt | heq
        · exact hlt
        · exfalso
          have : γ 1 ∈ R • S := interior_subset (heq ▸ hint)
          exact hqS (by simpa [γ] using this)
      let t1 : ℝ := min 1 (t0 + δ / 2)
      have ht1_gt : t0 < t1 := lt_min ht0_lt1 (by linarith)
      have ht1_mem : t1 ∈ T := by
        refine ⟨⟨le_trans ht0_mem.1 ht1_gt.le, min_le_left _ _⟩, ?_⟩
        apply interior_subset
        exact hball (by
          rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr ht1_gt)]
          have : t1 ≤ t0 + δ / 2 := min_le_right _ _
          linarith)
      exact not_lt_of_ge (le_csSup hTbdd ht1_mem) ht1_gt
    have hfr : γ t0 ∈ frontier (R • S) := ⟨hγt0_cl, hγt0_nint⟩
    -- frontier (R • S) = R • frontier S via Homeomorph.smulOfNeZero
    let hR_homeo := Homeomorph.smulOfNeZero R hRpos.ne' (α := ι → ℝ)
    have hfr_eq : frontier (R • S) = R • frontier S := by
      change frontier (hR_homeo '' S) = hR_homeo '' frontier S
      exact (hR_homeo.image_frontier S).symm
    rw [hfr_eq] at hfr
    obtain ⟨y, hyfr, hy_eq⟩ := hfr
    change R • y = γ t0 at hy_eq
    exact ⟨y, hyfr, by rw [hy_eq]; exact hγ_box t0 ht0_mem⟩
  -- Grid covering of the (n-1)-cube
  let N : ℕ := Nat.ceil R
  have hN_ge1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hRpos).ne'
  have hR_le_N : R ≤ (N : ℝ) := Nat.le_ceil R
  have hN_le_2R : (N : ℝ) ≤ 2 * R := by
    have : (N : ℝ) < R + 1 := Nat.ceil_lt_add_one hRpos.le
    linarith
  let gridPt : (Fin (n - 1) → Fin N) → (Fin (n - 1) → ℝ) :=
    fun α j => ((α j : ℕ) : ℝ) / (N : ℝ)
  have hgridPt_mem : ∀ α, gridPt α ∈ cube := by
    intro α j _
    have hle : ((α j : ℕ) : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr (α j).2.le
    exact ⟨by positivity, (div_le_one (by positivity : (0 : ℝ) < N)).mpr hle⟩
  let r_int : ℤ := ⌈1 + (L : ℝ)⌉ + 2
  let nearBox (p : ι → ℝ) : Finset (ι → ℤ) :=
    Fintype.piFinset fun i : ι => Finset.Icc (⌊p i⌋ - r_int) (⌊p i⌋ + r_int)
  have hnearBox_card : ∀ p : ι → ℝ, (nearBox p).card ≤ K ^ n := by
    intro p
    rw [Fintype.card_piFinset]
    calc ∏ i : ι, (Finset.Icc (⌊p i⌋ - r_int) (⌊p i⌋ + r_int)).card
        ≤ ∏ _i : ι, K := by
          refine Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => ?_)
          rw [Int.card_Icc]
          have hr : r_int = (Nat.ceil (1 + (L : ℝ)) : ℤ) + 2 := by
            dsimp [r_int]
            rw [Int.natCast_ceil_eq_ceil (by positivity : (0 : ℝ) ≤ 1 + (L : ℝ))]
          have : ((⌊p i⌋ + r_int) + 1 - (⌊p i⌋ - r_int)).toNat = K := by
            dsimp [K]; omega
          exact this.le
      _ = K ^ n := by simp [n]
  have hsdiff_sub :
      Z_hit \ Z_in ⊆ (Finset.univ : Finset (Fin M × (Fin (n - 1) → Fin N))).biUnion
        fun p => nearBox (R • f p.1 (gridPt p.2)) := by
    intro z hz
    obtain ⟨y, hyfr, hRybox⟩ := hbox_frontier z hz
    have hcov_y := hcov hyfr
    rw [Set.mem_iUnion] at hcov_y
    obtain ⟨k, u, hu_cube, rfl⟩ := hcov_y
    let α : Fin (n - 1) → Fin N := fun j =>
      ⟨min (N - 1) ⌊(N : ℝ) * u j⌋₊, by omega⟩
    refine Finset.mem_biUnion.mpr ⟨(k, α), Finset.mem_univ _, ?_⟩
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    have hdist_u : dist u (gridPt α) ≤ 1 / (N : ℝ) := by
      rw [dist_pi_le_iff (by positivity)]
      intro j
      have huj := hu_cube j (Set.mem_univ j)
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN_ge1
      rw [Real.dist_eq]
      dsimp [gridPt, α]
      have hfl_le : (⌊(N : ℝ) * u j⌋₊ : ℝ) ≤ (N : ℝ) * u j :=
        Nat.floor_le (mul_nonneg hNpos.le huj.1)
      have hfl_gt : (N : ℝ) * u j < (⌊(N : ℝ) * u j⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      by_cases hlt : ⌊(N : ℝ) * u j⌋₊ ≤ N - 1
      · rw [Nat.min_eq_right hlt, abs_le]
        constructor
        · rw [← mul_le_mul_iff_of_pos_left hNpos]
          field_simp [hNpos.ne']
          linarith
        · rw [← mul_le_mul_iff_of_pos_left hNpos]
          field_simp [hNpos.ne']
          linarith
      · have hge : N ≤ ⌊(N : ℝ) * u j⌋₊ := by omega
        have hmin : min (N - 1) ⌊(N : ℝ) * u j⌋₊ = N - 1 := Nat.min_eq_left (by omega)
        rw [hmin, Nat.cast_sub hN_ge1, Nat.cast_one]
        have hu1 : u j = 1 := by
          have : (N : ℝ) ≤ (N : ℝ) * u j :=
            le_trans (by exact_mod_cast hge) hfl_le
          have : 1 ≤ u j := by nlinarith
          linarith [huj.2]
        rw [hu1]
        have hval : 1 - ((N : ℝ) - 1) / (N : ℝ) = 1 / (N : ℝ) := by field_simp; ring
        rw [hval, abs_of_pos (by positivity)]
    have hdist_f : dist (f k u) (f k (gridPt α)) ≤ (L : ℝ) * (1 / (N : ℝ)) :=
      ((lipschitzOnWith_iff_dist_le_mul.mp (hlip k)) u hu_cube (gridPt α) (hgridPt_mem α)).trans
        (mul_le_mul_of_nonneg_left hdist_u (NNReal.coe_nonneg L))
    have hdist_Rf : |(R • f k u) i - (R • f k (gridPt α)) i| ≤ (L : ℝ) := by
      have hi : |f k u i - f k (gridPt α) i| ≤ (L : ℝ) * (1 / (N : ℝ)) := by
        simpa [Real.dist_eq] using (dist_le_pi_dist (f k u) (f k (gridPt α)) i).trans hdist_f
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN_ge1
      calc |(R • f k u) i - (R • f k (gridPt α)) i|
          = R * |f k u i - f k (gridPt α) i| := by
            simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub, abs_mul, abs_of_pos hRpos]
        _ ≤ R * ((L : ℝ) * (1 / (N : ℝ))) := mul_le_mul_of_nonneg_left hi hRpos.le
        _ = (L : ℝ) * (R / (N : ℝ)) := by ring
        _ ≤ (L : ℝ) * 1 := mul_le_mul_of_nonneg_left ((div_le_one hNpos).mpr hR_le_N)
            (NNReal.coe_nonneg L)
        _ = (L : ℝ) := mul_one _
    have hzi := hRybox i (Set.mem_univ i)
    have hfl1 := Int.floor_le ((R • f k (gridPt α)) i)
    have hfl2 := Int.lt_floor_add_one ((R • f k (gridPt α)) i)
    have hceilL : 1 + (L : ℝ) ≤ (⌈1 + (L : ℝ)⌉ : ℝ) := Int.le_ceil _
    have habs_Rf := abs_le.mp hdist_Rf
    have hr_val : (r_int : ℝ) = (⌈1 + (L : ℝ)⌉ : ℝ) + 2 := by dsimp [r_int]; push_cast; ring
    constructor
    · have : ((⌊(R • f k (gridPt α)) i⌋ - r_int : ℤ) : ℝ) < (z i : ℝ) := by
        rw [Int.cast_sub, hr_val]
        linarith [hzi.2, hfl1, hceilL, habs_Rf.1]
      exact le_of_lt (by exact_mod_cast this)
    · have : (z i : ℝ) ≤ ((⌊(R • f k (gridPt α)) i⌋ + r_int : ℤ) : ℝ) := by
        rw [Int.cast_add, hr_val]
        linarith [hzi.1, hfl2, hceilL, habs_Rf.2]
      exact_mod_cast this
  have hcard_bound : (Z_hit \ Z_in).card ≤ M * N ^ (n - 1) * K ^ n := by
    calc (Z_hit \ Z_in).card
        ≤ ∑ p : Fin M × (Fin (n - 1) → Fin N), (nearBox (R • f p.1 (gridPt p.2))).card :=
          (Finset.card_le_card hsdiff_sub).trans Finset.card_biUnion_le
      _ ≤ ∑ _p : Fin M × (Fin (n - 1) → Fin N), K ^ n :=
          Finset.sum_le_sum fun p _ => hnearBox_card _
      _ = M * N ^ (n - 1) * K ^ n := by
          simp [Finset.sum_const, Fintype.card_prod, Fintype.card_fin]
  calc ((Z_hit \ Z_in).card : ℝ)
      ≤ ((M * N ^ (n - 1) * K ^ n : ℕ) : ℝ) := Nat.cast_le.mpr hcard_bound
    _ = (M : ℝ) * (K : ℝ) ^ n * (N : ℝ) ^ (n - 1) := by push_cast; ring
    _ ≤ (M : ℝ) * (K : ℝ) ^ n * (2 * R) ^ (n - 1) := by
        gcongr
    _ = C * R ^ (n - 1) := by dsimp [C]; rw [mul_pow]; ring

open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.Units NumberField.Units.dirichletUnitTheorem in
/-- For a totally real number field `F` of degree `n`, the number of nonzero integral ideals
of norm `≤ x` in a fixed ideal class `C` equals `κ * x + O(x^{1 - 1/n})`, where `κ` is
independent of `C`. -/
lemma weber_ideal_class_counting_error (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (C : ClassGroup (𝓞 F)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, 1 ≤ x →
      |(Nat.card {I : (Ideal (𝓞 F))⁰ //
          Ideal.absNorm (I : Ideal (𝓞 F)) ≤ x ∧ ClassGroup.mk0 I = C} : ℝ) -
        ((2 ^ nrRealPlaces F * (2 * π) ^ nrComplexPlaces F * Units.regulator F) /
          (Units.torsionOrder F * Real.sqrt |discr F|)) * x| ≤
        M * x ^ (1 - (Module.finrank ℚ F : ℝ)⁻¹) := by
  classical
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective C⁻¹
  let L := ZLattice.comap ℝ (mixedEmbedding.idealLattice F (FractionalIdeal.mk0 F J))
    (euclidean.toMixed F).toLinearMap
  let b := Module.Free.chooseBasis ℤ L
  let ι := Module.Free.ChooseBasisIndex ℤ L
  let _ : Fintype ι := Module.Free.ChooseBasisIndex.fintype ℤ L
  have hn_eq : Fintype.card ι = Module.finrank ℚ F := by
    have h1 : Fintype.card ι = Module.finrank ℝ (euclidean.mixedSpace F) := by
      rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L]
    rw [h1, euclidean.finrank]
  have : Nonempty ι := Fintype.card_pos_iff.mp (hn_eq ▸ Module.finrank_pos)
  let eL : euclidean.mixedSpace F ≃L[ℝ] (ι → ℝ) := (b.ofZLatticeBasis ℝ).equivFunL
  let toCoord : mixedSpace F →L[ℝ] (ι → ℝ) := eL.toContinuousLinearMap.comp
    (euclidean.toMixed F).symm.toContinuousLinearMap
  let D : Set (euclidean.mixedSpace F) := (euclidean.toMixed F) ⁻¹' (normLeOne F)
  let S : Set (ι → ℝ) := eL '' D
  -- Boundedness and measurability of S
  have hDbdd : Bornology.IsBounded D :=
    (euclidean.toMixed F).antilipschitz.isBounded_preimage (isBounded_normLeOne F)
  have hSbdd : Bornology.IsBounded S := by
    rw [← NormedSpace.isVonNBounded_iff ℝ] at hDbdd ⊢
    exact Bornology.IsVonNBounded.image hDbdd eL.toContinuousLinearMap
  have hDmeas : MeasurableSet D :=
    (euclidean.toMixed F).continuous.measurable (measurableSet_normLeOne F)
  have hSmeas : MeasurableSet S :=
    eL.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hDmeas
  -- Volume of S
  have hvolS : volume.real S =
      (2 ^ nrRealPlaces F * (2 * π) ^ nrComplexPlaces F * Units.regulator F) /
        (Real.sqrt |discr F| * Ideal.absNorm (J : Ideal (𝓞 F))) := by
    have h1 : volume S = volume D / ENNReal.ofReal (ZLattice.covolume L) :=
      ZLattice.volume_image_eq_volume_div_covolume' L b hDmeas.nullMeasurableSet
    rw [measureReal_def, h1, ENNReal.toReal_div,
      ENNReal.toReal_ofReal (ZLattice.covolume_pos L volume).le]
    have hvolD : volume D = volume (normLeOne F) :=
      (euclidean.volumePreserving_toMixed F).measure_preimage
        (measurableSet_normLeOne F).nullMeasurableSet
    have hcovL : ZLattice.covolume L =
        ZLattice.covolume (mixedEmbedding.idealLattice F (FractionalIdeal.mk0 F J)) :=
      ZLattice.covolume_comap _ _ _ (euclidean.volumePreserving_toMixed F)
    rw [hvolD, hcovL, volume_normLeOne, covolume_idealLattice,
      IsTotallyReal.nrComplexPlaces_eq_zero F]
    simp only [pow_zero, mul_one, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal (Units.regulator_pos F).le, FractionalIdeal.coe_mk0,
      FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]
    ring
  -- Cover frontier S by finitely many Lipschitz images of the (n-1)-cube
  let n := Fintype.card ι
  have hcard_inf : Fintype.card (InfinitePlace F) = n := by
    dsimp [n]
    rw [hn_eq, IsTotallyReal.finrank F]
    exact Fintype.card_congr
      { toFun := fun w => ⟨w, IsTotallyReal.isReal w⟩
        invFun := Subtype.val
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hnoComplex : ∀ w : {w : InfinitePlace F // IsComplex w}, False := fun w =>
    (Fintype.card_eq_zero_iff.mp (IsTotallyReal.nrComplexPlaces_eq_zero F)).false w
  -- Sign maps from realSpace F to mixedSpace F (using IsTotallyReal F)
  let signMap : (InfinitePlace F → Bool) → realSpace F →L[ℝ] mixedSpace F :=
    fun σ =>
      { toFun := fun y =>
          (fun w => (if σ w.1 then (1 : ℝ) else -1) * y w.1,
           fun w => (hnoComplex w).elim)
        map_add' := fun y₁ y₂ => by
          ext w
          · simp [mul_add]
          · exact (hnoComplex w).elim
        map_smul' := fun c y => by
          ext w
          · simp [mul_left_comm]
          · exact (hnoComplex w).elim
        cont := by
          refine Continuous.prodMk ?_ ?_
          · exact continuous_pi fun w => continuous_const.mul (continuous_apply w.1)
          · exact continuous_pi fun w => (hnoComplex w).elim }
  have hpreimage_sign : ∀ T : Set (realSpace F),
      normAtAllPlaces ⁻¹' T ⊆ ⋃ σ : InfinitePlace F → Bool, signMap σ '' T := by
    intro T x hx
    refine Set.mem_iUnion.mpr ⟨fun w => decide (0 ≤ x.1 ⟨w, IsTotallyReal.isReal w⟩),
      normAtAllPlaces x, hx, ?_⟩
    ext w
    · change (if decide (0 ≤ x.1 w) then (1 : ℝ) else -1) * normAtPlace w.1 x = x.1 w
      have hnw : normAtPlace w.1 x = |x.1 w| := by
        change (if hw : w.1.IsReal then ‖x.1 ⟨w.1, hw⟩‖ else ‖x.2 ⟨w.1, _⟩‖) = |x.1 w|
        rw [dif_pos w.2, Real.norm_eq_abs]
      rw [hnw]
      by_cases h0 : 0 ≤ x.1 w
      · simp [h0, abs_of_nonneg h0]
      · simp [h0, abs_of_neg (lt_of_not_ge h0)]
    · exact (hnoComplex w).elim
  -- Parametrization Φ on the unit cube in realSpace F
  let cubeInf : Set (InfinitePlace F → ℝ) := Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1
  let Φ : (InfinitePlace F → ℝ) → realSpace F :=
    fun u => (u w₀) • expMapBasis (fun w => if w = w₀ then 0 else u w)
  have hΦ_lip : ∃ LΦ : NNReal, LipschitzOnWith LΦ Φ cubeInf := by
    have hcoord : ∀ w : InfinitePlace F, ∃ Lw : NNReal,
        LipschitzOnWith Lw (fun u => Φ u w) cubeInf := by
      intro w
      let P : (InfinitePlace F → ℝ) → ℝ := fun u =>
        ∏ i : {v : InfinitePlace F // v ≠ w₀},
          (w (fundSystem F (equivFinRank.symm i))) ^ (u i.1)
      have hform : ∀ u, Φ u w = u w₀ * P u := by
        intro u
        dsimp [Φ, P]
        rw [expMapBasis_apply']
        simp only [↓reduceIte, Real.exp_zero, one_smul]
        congr 1
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [if_neg i.2]
      simp_rw [hform]
      have ha_pos_fn : ∀ i : {v : InfinitePlace F // v ≠ w₀},
          0 < w (fundSystem F (equivFinRank.symm i)) := fun i =>
        InfinitePlace.pos_iff.mpr (by
          rw [map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)]
          exact Units.ne_zero _)
      have hprod_lip : ∃ Lp : NNReal, LipschitzOnWith Lp P cubeInf := by
        refine exists_lipschitzOnWith_finset_prod cubeInf Finset.univ _ (fun i _ => ?_) (fun i _ => ?_)
        · obtain ⟨Li, hLi⟩ := exists_lipschitzOnWith_rpow_const (ha_pos_fn i)
          refine ⟨Li, lipschitzOnWith_iff_dist_le_mul.mpr fun u hu v hv => ?_⟩
          have h1 := (lipschitzOnWith_iff_dist_le_mul.mp hLi) (u i.1) (hu i.1 (Set.mem_univ _))
            (v i.1) (hv i.1 (Set.mem_univ _))
          exact h1.trans (mul_le_mul_of_nonneg_left (dist_le_pi_dist u v i.1) (NNReal.coe_nonneg Li))
        · have ha_pos := ha_pos_fn i
          refine ⟨max 1 (w (fundSystem F (equivFinRank.symm i))), by positivity, fun u hu => ?_⟩
          have hui := hu i.1 (Set.mem_univ _)
          rw [abs_of_nonneg (Real.rpow_nonneg ha_pos.le _)]
          rcases le_or_gt 1 (w (fundSystem F (equivFinRank.symm i))) with h1 | h1
          · exact (Real.rpow_le_rpow_of_exponent_le h1 hui.2).trans (by rw [Real.rpow_one]; exact le_max_right _ _)
          · exact (Real.rpow_le_rpow_of_exponent_ge ha_pos h1.le hui.1).trans (by rw [Real.rpow_zero]; exact le_max_left _ _)
      obtain ⟨Lp, hLp⟩ := hprod_lip
      have hprod_bdd : ∃ Mp : ℝ, 0 ≤ Mp ∧ ∀ u ∈ cubeInf, |P u| ≤ Mp := by
        refine ⟨∏ i : {v : InfinitePlace F // v ≠ w₀},
            max 1 (w (fundSystem F (equivFinRank.symm i))),
            Finset.prod_nonneg fun _ _ => by positivity, fun u hu => ?_⟩
        dsimp [P]
        rw [Finset.abs_prod]
        refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => ?_
        have ha_pos := ha_pos_fn i
        have hui := hu i.1 (Set.mem_univ _)
        rw [abs_of_nonneg (Real.rpow_nonneg ha_pos.le _)]
        rcases le_or_gt 1 (w (fundSystem F (equivFinRank.symm i))) with h1 | h1
        · exact (Real.rpow_le_rpow_of_exponent_le h1 hui.2).trans (by rw [Real.rpow_one]; exact le_max_right _ _)
        · exact (Real.rpow_le_rpow_of_exponent_ge ha_pos h1.le hui.1).trans (by rw [Real.rpow_zero]; exact le_max_left _ _)
      obtain ⟨Mp, hMp0, hMp⟩ := hprod_bdd
      let Mnn : NNReal := ⟨Mp, hMp0⟩
      refine ⟨Lp + Mnn, lipschitzOnWith_iff_dist_le_mul.mpr fun u hu v hv => ?_⟩
      simp only [Real.dist_eq, NNReal.coe_add]
      change |u w₀ * P u - v w₀ * P v| ≤ ((Lp : ℝ) + Mp) * dist u v
      have hu0 := hu w₀ (Set.mem_univ _)
      have h1 := (lipschitzOnWith_iff_dist_le_mul.mp hLp) u hu v hv
      simp only [Real.dist_eq] at h1
      have h2 : |u w₀ - v w₀| ≤ dist u v := by
        simpa [Real.dist_eq] using dist_le_pi_dist u v w₀
      calc |u w₀ * P u - v w₀ * P v|
          = |u w₀ * (P u - P v) + (u w₀ - v w₀) * P v| := by ring_nf
        _ ≤ |u w₀| * |P u - P v| + |u w₀ - v w₀| * |P v| := by
            calc _ ≤ |u w₀ * (P u - P v)| + |(u w₀ - v w₀) * P v| := abs_add_le _ _
              _ = _ := by rw [abs_mul, abs_mul]
        _ ≤ 1 * ((Lp : ℝ) * dist u v) + dist u v * Mp := by
            gcongr
            · rw [abs_of_nonneg hu0.1]; exact hu0.2
            · exact hMp v hv
        _ = ((Lp : ℝ) + Mp) * dist u v := by ring
    choose Lw hLw using hcoord
    refine ⟨Finset.univ.sup Lw, lipschitzOnWith_iff_dist_le_mul.mpr fun u hu v hv => ?_⟩
    rw [dist_pi_le_iff (by positivity)]
    intro w
    calc dist (Φ u w) (Φ v w)
        ≤ (Lw w : ℝ) * dist u v := (lipschitzOnWith_iff_dist_le_mul.mp (hLw w)) u hu v hv
      _ ≤ ((Finset.univ.sup Lw : NNReal) : ℝ) * dist u v := by
          gcongr
          exact Finset.le_sup (Finset.mem_univ w)
  obtain ⟨LΦ, hLΦ⟩ := hΦ_lip
  -- Cover compactSet F \ expMapBasis '' interior (paramSet F) by the faces of cubeInf
  let eW (w : InfinitePlace F) : {v : InfinitePlace F // v ≠ w} ≃ Fin (n - 1) :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hcard_inf, Fintype.card_fin])
  let faceEmbed (w : InfinitePlace F) (bval : Bool) :
      (Fin (n - 1) → ℝ) → (InfinitePlace F → ℝ) :=
    fun y v => if h : v = w then (if bval then (0 : ℝ) else 1) else y (eW w ⟨v, h⟩)
  have hface_mem : ∀ w bval y,
      y ∈ (Set.univ.pi fun _ : Fin (n - 1) => Set.Icc (0 : ℝ) 1) →
      faceEmbed w bval y ∈ cubeInf := by
    intro w bval y hy v _
    dsimp [faceEmbed]
    split_ifs
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨zero_le_one, le_rfl⟩
    · exact hy _ (Set.mem_univ _)
  have hface_lip : ∀ w bval, LipschitzWith 1 (faceEmbed w bval) := by
    intro w bval
    rw [lipschitzWith_iff_dist_le_mul]
    intro y₁ y₂
    rw [NNReal.coe_one, one_mul, dist_pi_le_iff dist_nonneg]
    intro v
    dsimp [faceEmbed]
    by_cases hv : v = w
    · simp [hv, dist_nonneg]
    · simp only [dif_neg hv]
      exact dist_le_pi_dist y₁ y₂ _
  have hcompact_diff_cov :
      compactSet F \ expMapBasis '' interior (paramSet F) ⊆
        ⋃ p : InfinitePlace F × Bool,
          (Φ ∘ faceEmbed p.1 p.2) '' (Set.univ.pi fun _ : Fin (n - 1) => Set.Icc (0 : ℝ) 1) := by
    intro x ⟨hx_comp, hx_nint⟩
    obtain ⟨c, hc, ⟨_, ⟨y, hy, rfl⟩, rfl⟩⟩ := hx_comp
    have hyw₀ : y w₀ = 0 := by simpa using hy w₀ (Set.mem_univ _)
    let u : InfinitePlace F → ℝ := fun v => if v = w₀ then c else y v
    have hu_cube : u ∈ cubeInf := by
      intro v _
      dsimp [u]
      split_ifs with hv
      · exact hc
      · simpa [hv] using hy v (Set.mem_univ _)
    have hΦu : Φ u = c • expMapBasis y := by
      dsimp [Φ, u]
      rw [if_pos rfl]
      congr 2
      ext v
      split_ifs with hv
      · rw [hv, hyw₀]
      · rfl
    have hbdry : ∃ w : InfinitePlace F, u w = 0 ∨ u w = 1 := by
      by_contra hall
      push Not at hall
      apply hx_nint
      have hc0 : 0 < c := lt_of_le_of_ne hc.1 (Ne.symm (by simpa [u] using (hall w₀).1))
      have hc1 : c < 1 := lt_of_le_of_ne hc.2 (by simpa [u] using (hall w₀).2)
      refine ⟨fun v => if v = w₀ then Real.log c else y v, ?_, ?_⟩
      · rw [interior_paramSet, Set.mem_univ_pi]
        intro v
        split_ifs with hv
        · exact Real.log_neg hc0 hc1
        · have hv_mem := hu_cube v (Set.mem_univ _)
          have hv_ne := hall v
          dsimp [u] at hv_mem hv_ne
          rw [if_neg hv] at hv_mem hv_ne
          exact ⟨lt_of_le_of_ne hv_mem.1 (Ne.symm hv_ne.1), lt_of_le_of_ne hv_mem.2 hv_ne.2⟩
      · rw [expMapBasis_apply'', if_pos rfl, Real.exp_log hc0]
        congr 2
        ext v
        split_ifs with hv
        · rw [hv, hyw₀]
        · rfl
    obtain ⟨w, hw0 | hw1⟩ := hbdry
    · refine Set.mem_iUnion.mpr ⟨(w, true), ?_⟩
      refine ⟨fun j => u ((eW w).symm j).1, fun j _ => hu_cube _ (Set.mem_univ _), ?_⟩
      change Φ (faceEmbed w true fun j => u ((eW w).symm j).1) = c • expMapBasis y
      rw [← hΦu]
      congr 1
      ext v
      dsimp [faceEmbed]
      split_ifs with hv
      · subst hv; exact hw0.symm
      · simp
    · refine Set.mem_iUnion.mpr ⟨(w, false), ?_⟩
      refine ⟨fun j => u ((eW w).symm j).1, fun j _ => hu_cube _ (Set.mem_univ _), ?_⟩
      change Φ (faceEmbed w false fun j => u ((eW w).symm j).1) = c • expMapBasis y
      rw [← hΦu]
      congr 1
      ext v
      dsimp [faceEmbed]
      split_ifs with hv
      · subst hv; exact hw1.symm
      · simp
  -- Assemble the finite family of Lipschitz maps covering frontier S
  let Idx := (InfinitePlace F → Bool) × InfinitePlace F × Bool
  let eIdx : Idx ≃ Fin (Fintype.card Idx) := Fintype.equivFin Idx
  let fmap : Fin (Fintype.card Idx) → (Fin (n - 1) → ℝ) → (ι → ℝ) := fun k y =>
    let p := eIdx.symm k
    toCoord (signMap p.1 (Φ (faceEmbed p.2.1 p.2.2 y)))
  have hlip_each : ∀ k, ∃ Lk : NNReal,
      LipschitzOnWith Lk (fmap k) (Set.univ.pi fun _ : Fin (n - 1) => Set.Icc (0 : ℝ) 1) := by
    intro k
    let p := eIdx.symm k
    have h1 : LipschitzWith (‖toCoord‖₊ * ‖signMap p.1‖₊) (fun z => toCoord (signMap p.1 z)) :=
      toCoord.lipschitz.comp (signMap p.1).lipschitz
    have h2 : LipschitzOnWith (‖toCoord‖₊ * ‖signMap p.1‖₊ * LΦ)
        (fun u => toCoord (signMap p.1 (Φ u))) cubeInf :=
      h1.comp_lipschitzOnWith hLΦ
    have h3 : LipschitzOnWith (‖toCoord‖₊ * ‖signMap p.1‖₊ * LΦ * 1) (fmap k)
        (Set.univ.pi fun _ : Fin (n - 1) => Set.Icc (0 : ℝ) 1) :=
      h2.comp (hface_lip p.2.1 p.2.2).lipschitzOnWith (fun y hy => hface_mem p.2.1 p.2.2 y hy)
    exact ⟨_, h3⟩
  choose Lk hLk using hlip_each
  let Lmax : NNReal := Finset.univ.sup Lk
  have hlip_all : ∀ k, LipschitzOnWith Lmax (fmap k)
      (Set.univ.pi fun _ : Fin (n - 1) => Set.Icc (0 : ℝ) 1) :=
    fun k => (hLk k).weaken (Finset.le_sup (Finset.mem_univ k))
  have hcov_S : frontier S ⊆ ⋃ k : Fin (Fintype.card Idx),
      fmap k '' (Set.univ.pi fun _ : Fin (n - 1) => Set.Icc (0 : ℝ) 1) := by
    intro z hz
    -- frontier (eL '' D) = eL '' frontier D = toCoord '' frontier (normLeOne F)
    have hz' : z ∈ toCoord '' frontier (normLeOne F) := by
      have hfeL : frontier S = eL '' frontier D := by
        dsimp [S]; exact (eL.toHomeomorph.image_frontier D).symm
      have hfD : frontier D = (euclidean.toMixed F).toHomeomorph ⁻¹' frontier (normLeOne F) :=
        ((euclidean.toMixed F).toHomeomorph.preimage_frontier (normLeOne F)).symm
      rw [hfeL, hfD] at hz
      obtain ⟨v, hv, rfl⟩ := hz
      refine ⟨euclidean.toMixed F v, hv, ?_⟩
      simp [toCoord]
    obtain ⟨x, hxfr, rfl⟩ := hz'
    have hx_comp : normAtAllPlaces x ∈ compactSet F := closure_normLeOne_subset F hxfr.1
    have hx_nint : normAtAllPlaces x ∉ expMapBasis '' interior (paramSet F) :=
      fun h => hxfr.2 (subset_interior_normLeOne F h)
    have hmem_diff := hcompact_diff_cov ⟨hx_comp, hx_nint⟩
    rw [Set.mem_iUnion] at hmem_diff
    obtain ⟨⟨w, bval⟩, y, hy, hΦy⟩ := hmem_diff
    change Φ (faceEmbed w bval y) = normAtAllPlaces x at hΦy
    have hx_sign := hpreimage_sign {normAtAllPlaces x} (Set.mem_singleton _)
    rw [Set.mem_iUnion] at hx_sign
    obtain ⟨σ, _, rfl, hx_eq⟩ := hx_sign
    refine Set.mem_iUnion.mpr ⟨eIdx (σ, w, bval), y, hy, ?_⟩
    dsimp [fmap]
    rw [Equiv.symm_apply_apply]
    dsimp only
    rw [hΦy, hx_eq]
  -- Apply the lattice-point counting error lemma to S
  obtain ⟨C₀, hC₀0, hlat⟩ := lattice_card_sub_volume_le hSbdd Lmax fmap hlip_all hcov_S
  -- Relate Nat.card {I : ... | absNorm I ≤ x ∧ mk0 I = C} to Nat.card ((R • S) ∩ ℤ^ι)
  have hn_pos : 0 < n := by dsimp [n]; rw [hn_eq]; exact Module.finrank_pos
  have hn_real : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
  have hJ_pos : 0 < Ideal.absNorm (J : Ideal (𝓞 F)) := Ideal.absNorm_pos_of_nonZeroDivisors J
  have hJ_rpos : (0 : ℝ) < Ideal.absNorm (J : Ideal (𝓞 F)) := Nat.cast_pos.mpr hJ_pos
  have htor_pos : (0 : ℝ) < Units.torsionOrder F := Nat.cast_pos.mpr (Units.torsionOrder_pos F)
  let M : ℝ := C₀ * (Ideal.absNorm (J : Ideal (𝓞 F)) : ℝ) ^ (1 - (n : ℝ)⁻¹) / (Units.torsionOrder F : ℝ)
  refine ⟨M, by positivity, fun x hx => ?_⟩
  let s : ℝ := x * (Ideal.absNorm (J : Ideal (𝓞 F)) : ℝ)
  have hs_ge1 : 1 ≤ s := by
    have hJ1 : (1 : ℝ) ≤ Ideal.absNorm (J : Ideal (𝓞 F)) := by exact_mod_cast hJ_pos
    nlinarith
  have hs_pos : 0 < s := lt_of_lt_of_le zero_lt_one hs_ge1
  let R : ℝ := s ^ ((n : ℝ)⁻¹)
  have hR_ge1 : 1 ≤ R := Real.one_le_rpow hs_ge1 (by positivity)
  have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one hR_ge1
  have hRn : R ^ n = s := by
    dsimp [R]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs_pos.le, inv_mul_cancel₀ hn_real.ne', Real.rpow_one]
  -- Bijection between {I // absNorm I ≤ x ∧ mk0 I = C} × torsion and (R • S) ∩ ℤ^ι
  have hcard_rel :
      (Nat.card {I : (Ideal (𝓞 F))⁰ //
        Ideal.absNorm (I : Ideal (𝓞 F)) ≤ x ∧ ClassGroup.mk0 I = C} : ℝ) *
        (Units.torsionOrder F : ℝ) =
      (Nat.card ((R • S) ∩ Set.range (fun z : ι → ℤ => fun i => (z i : ℝ)) : Set (ι → ℝ)) : ℝ) := by
    have h1 :
        Nat.card {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm (I : Ideal (𝓞 F)) ≤ x ∧ ClassGroup.mk0 I = C} =
        Nat.card {I : (Ideal (𝓞 F))⁰ // (J : Ideal (𝓞 F)) ∣ I ∧ Submodule.IsPrincipal (I : Ideal (𝓞 F)) ∧
          Ideal.absNorm (I : Ideal (𝓞 F)) ≤ s} := by
      have hdvd_iff : ∀ I : (Ideal (𝓞 F))⁰, ((J : Ideal (𝓞 F)) ∣ (I : Ideal (𝓞 F))) ↔ J ∣ I := by
        intro I
        constructor
        · rintro ⟨K, hK⟩
          refine ⟨⟨K, mem_nonZeroDivisors_iff_ne_zero.mpr fun h0 =>
            mem_nonZeroDivisors_iff_ne_zero.mp I.2 (by rw [hK, h0, mul_zero])⟩, Subtype.ext hK⟩
        · rintro ⟨K, hK⟩
          exact ⟨K.1, congrArg Subtype.val hK⟩
      simp_rw [hdvd_iff]
      refine Nat.card_congr ?_
      refine ((Equiv.dvd J).subtypeEquiv fun I => ?_).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter (fun I : (Ideal (𝓞 F))⁰ => J ∣ I) _)
      rw [← ClassGroup.mk0_eq_one_iff (SetLike.coe_mem _)]
      dsimp only [s]
      simp_rw [Equiv.dvd_apply, Submonoid.coe_mul, ← Submonoid.mul_def, _root_.map_mul, hJ,
        inv_mul_eq_one, Nat.cast_mul, mul_comm x, eq_comm, and_comm, and_congr_left_iff]
      exact fun _ => (mul_le_mul_iff_of_pos_left hJ_rpos).symm
    have heq2 :
        ↑({v : euclidean.mixedSpace F | v ∈ (euclidean.toMixed F) ⁻¹' fundamentalCone F ∧
            mixedEmbedding.norm ((euclidean.toMixed F) v) ≤ s} ∩ (L : Set (euclidean.mixedSpace F))) ≃
        {a : idealSet F J // mixedEmbedding.norm (a : mixedSpace F) ≤ s} := by
      dsimp [L]
      refine (((euclidean.toMixed F).toEquiv.image _).trans (Equiv.subtypeEquivProp ?_)).trans
        (Equiv.subtypeSubtypeEquivSubtypeInter _ (mixedEmbedding.norm · ≤ s)).symm
      ext
      simp_rw [mem_idealSet, Set.mem_image, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe,
        mem_idealLattice, FractionalIdeal.coe_mk0]
      constructor
      · rintro ⟨_, ⟨⟨hx₁, hx₂⟩, _, ⟨y, hy₃, rfl⟩, h⟩, rfl⟩
        exact ⟨⟨hx₁, y, hy₃, h⟩, hx₂⟩
      · rintro ⟨⟨hx₁, ⟨y, hy₂, rfl⟩⟩, hx₃⟩
        refine ⟨(euclidean.toMixed F).symm (mixedEmbedding F (algebraMap (𝓞 F) F y)),
          ⟨⟨?_, ?_⟩, algebraMap (𝓞 F) F y, ⟨y, hy₂, rfl⟩, ?_⟩, ?_⟩
        · rw [(euclidean.toMixed F).apply_symm_apply]; exact hx₁
        · rw [(euclidean.toMixed F).apply_symm_apply]; exact hx₃
        · exact ((euclidean.toMixed F).apply_symm_apply _).symm
        · exact (euclidean.toMixed F).apply_symm_apply _
    have h2 := Nat.card_congr heq2
    have h3 := card_isPrincipal_dvd_norm_le F J s
    rw [h1, ← Nat.cast_mul, h3, ← h2]
    congr 1
    -- Bijection between ({v ∈ toMixed⁻¹' fundamentalCone ∧ norm(toMixed v) ≤ s} ∩ L) and ((R • S) ∩ ℤ^ι)
    have hD_scale : R • D = {v : euclidean.mixedSpace F |
        v ∈ (euclidean.toMixed F) ⁻¹' fundamentalCone F ∧
        mixedEmbedding.norm (euclidean.toMixed F v) ≤ s} := by
      ext v
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ hR_pos.ne']
      simp only [D, Set.mem_preimage, mem_normLeOne, map_smul, Set.mem_ofPred_eq,
        mixedEmbedding.norm_smul, abs_of_pos (inv_pos.mpr hR_pos), inv_pow, ← hn_eq]
      have hRn' : R ^ Fintype.card ι = s := hRn
      rw [hRn', fundamentalCone.smul_mem_iff_mem (inv_ne_zero hR_pos.ne'),
        inv_mul_le_iff₀ hs_pos, mul_one]
    refine Nat.card_congr ?_
    refine eL.toEquiv.subtypeEquiv fun v => ?_
    rw [Set.mem_inter_iff, Set.mem_inter_iff, ← hD_scale]
    constructor
    · rintro ⟨hvD, hvL⟩
      refine ⟨?_, ?_⟩
      · obtain ⟨u, huD, rfl⟩ := hvD
        exact ⟨eL u, ⟨u, huD, rfl⟩, (map_smul eL R u).symm⟩
      · have hmem : v ∈ Submodule.span ℤ (Set.range (b.ofZLatticeBasis ℝ)) := by
          rwa [b.ofZLatticeBasis_span ℝ]
        rw [Module.Basis.mem_span_iff_repr_mem] at hmem
        refine ⟨fun i => (hmem i).choose, ?_⟩
        ext i
        simpa [eL, Module.Basis.equivFun_apply] using (hmem i).choose_spec
    · rintro ⟨⟨w, ⟨u, huD, rfl⟩, hw⟩, ⟨z, hz⟩⟩
      have hvu : v = R • u := eL.injective (by rw [map_smul]; exact hw.symm)
      refine ⟨hvu ▸ ⟨u, huD, rfl⟩, ?_⟩
      rw [← b.ofZLatticeBasis_span ℝ, SetLike.mem_coe, Module.Basis.mem_span_iff_repr_mem]
      intro i
      exact ⟨z i, by simpa [eL, Module.Basis.equivFun_apply] using congrFun hz i⟩
  -- Combine hcard_rel, hvolS, and hlat
  have hlat_R := hlat R hR_ge1
  rw [hRn, hvolS] at hlat_R
  have hR_nm1 : R ^ (n - 1) = s ^ (1 - (n : ℝ)⁻¹) := by
    dsimp [R]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs_pos.le, Nat.cast_sub hn_pos, Nat.cast_one]
    congr 1
    rw [mul_sub, mul_one, inv_mul_cancel₀ hn_real.ne']
  rw [hR_nm1] at hlat_R
  have hs_pow : s ^ (1 - (n : ℝ)⁻¹) =
      x ^ (1 - (n : ℝ)⁻¹) * (Ideal.absNorm (J : Ideal (𝓞 F)) : ℝ) ^ (1 - (n : ℝ)⁻¹) :=
    Real.mul_rpow (by linarith) hJ_rpos.le
  rw [hs_pow] at hlat_R
  have hmain_eq :
      (Nat.card {I : (Ideal (𝓞 F))⁰ //
        Ideal.absNorm (I : Ideal (𝓞 F)) ≤ x ∧ ClassGroup.mk0 I = C} : ℝ) -
      ((2 ^ nrRealPlaces F * (2 * π) ^ nrComplexPlaces F * Units.regulator F) /
        (Units.torsionOrder F * Real.sqrt |discr F|)) * x =
      ((Nat.card ((R • S) ∩ Set.range (fun z : ι → ℤ => fun i => (z i : ℝ)) : Set (ι → ℝ)) : ℝ) -
        ((2 ^ nrRealPlaces F * (2 * π) ^ nrComplexPlaces F * Units.regulator F) /
          (Real.sqrt |discr F| * Ideal.absNorm (J : Ideal (𝓞 F)))) * s) /
        (Units.torsionOrder F : ℝ) := by
    rw [← hcard_rel, sub_div, mul_div_cancel_right₀ _ htor_pos.ne']
    congr 1
    dsimp only [s]
    have h1' : ((2 ^ nrRealPlaces F * (2 * π) ^ nrComplexPlaces F * Units.regulator F) /
        (Real.sqrt |discr F| * ↑(Ideal.absNorm (J : Ideal (𝓞 F))))) *
        (x * ↑(Ideal.absNorm (J : Ideal (𝓞 F)))) =
        ((2 ^ nrRealPlaces F * (2 * π) ^ nrComplexPlaces F * Units.regulator F) /
          Real.sqrt |discr F|) * x := by
      rw [div_mul_eq_div_div, div_mul_eq_mul_div, ← mul_assoc,
        mul_div_cancel_right₀ _ hJ_rpos.ne']
    rw [h1']
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [hmain_eq, abs_div, abs_of_pos htor_pos, div_le_iff₀ htor_pos]
  calc _ ≤ C₀ * (x ^ (1 - (n : ℝ)⁻¹) * (Ideal.absNorm (J : Ideal (𝓞 F)) : ℝ) ^ (1 - (n : ℝ)⁻¹)) :=
        hlat_R
    _ = M * x ^ (1 - (Module.finrank ℚ F : ℝ)⁻¹) * (Units.torsionOrder F : ℝ) := by
        dsimp only [M, n]
        rw [hn_eq, div_mul_eq_mul_div, div_mul_cancel₀ _ htor_pos.ne']
        ring

end LatticeCounting

/- ## Section 4: Real L-series, discrete Abel summation, and finite Euler products -/

section LSeriesAndEuler

variable {E : Type} [Field E] [NumberField E]

lemma summable_ideal_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun I : (Ideal (𝓞 E))⁰ => (Ideal.absNorm (I : Ideal (𝓞 E)) : ℝ) ^ (-s)) := by
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n,
      (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = k} : ℝ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    have htend : Tendsto (fun n : ℕ =>
        (∑ k ∈ Finset.Icc 1 n, (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = k} : ℝ)) / (n : ℝ))
        atTop (𝓝 (dedekindZeta_residue E)) := by
      refine ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ E).comp
        tendsto_natCast_atTop_atTop).congr fun n => ?_
      simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
      congr
      rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
        show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
        show 1 = Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
        Finset.sum_Ioc_add_eq_sum_Icc n.zero_le,
        ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ => Ideal.finite_setOfPred_absNorm_eq k)]
      simp [Set.coe_eq_subtype]
    have h1 := (htend.isBigO_one ℝ).mul (Asymptotics.isBigO_refl (fun n : ℕ => (n : ℝ)) atTop)
    refine h1.congr' ?_ (Eventually.of_forall fun n => by simp)
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    simp [div_mul_cancel₀ _ hnR]
  have hLS : LSeriesSummable
      (fun n : ℕ => (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℂ)) (s : ℂ) := by
    refine LSeriesSummable_of_sum_norm_bigO_and_nonneg hO (fun _ => Nat.cast_nonneg _) zero_le_one ?_
    simpa using hs
  have hnat : Summable (fun n : ℕ =>
      if n = 0 then (0 : ℝ) else
        (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s)) := by
    have hnorm := hLS.norm
    refine hnorm.congr fun n => ?_
    by_cases hn : n = 0
    · simp [LSeries.term, hn]
    · simp only [LSeries.term, if_neg hn, div_eq_mul_inv, norm_mul, Complex.norm_natCast,
        norm_inv, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Complex.ofReal_re,
        Real.rpow_neg (Nat.cast_nonneg n)]
  -- Group ideals by absNorm
  rw [← Equiv.summable_iff (Equiv.sigmaFiberEquiv (fun I : (Ideal (𝓞 E))⁰ => Ideal.absNorm I.1))]
  change Summable (fun c : (n : ℕ) × {I : (Ideal (𝓞 E))⁰ // Ideal.absNorm I.1 = n} =>
    (Ideal.absNorm c.2.1.1 : ℝ) ^ (-s))
  refine (summable_sigma_of_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)).mpr ?_
  constructor
  · intro n
    have : Finite {I : Ideal (𝓞 E) // Ideal.absNorm I = n} :=
      (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 E) n).to_subtype
    have : Finite {I : (Ideal (𝓞 E))⁰ // Ideal.absNorm I.1 = n} :=
      Finite.of_injective
        (fun x : {I : (Ideal (𝓞 E))⁰ // Ideal.absNorm I.1 = n} =>
          (⟨x.1.1, x.2⟩ : {I : Ideal (𝓞 E) // Ideal.absNorm I = n}))
        (fun _ _ h => Subtype.ext (Subtype.ext (Subtype.mk.inj h)))
    exact Summable.of_finite
  · refine hnat.congr fun n => ?_
    by_cases hn : n = 0
    · subst hn
      have : IsEmpty {I : (Ideal (𝓞 E))⁰ // Ideal.absNorm I.1 = 0} :=
        ⟨fun x => Ideal.absNorm_ne_zero_of_nonZeroDivisors x.1 x.2⟩
      simp
    · simp only [if_neg hn]
      have : Finite {I : Ideal (𝓞 E) // Ideal.absNorm I = n} :=
        (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 E) n).to_subtype
      have : Finite {I : (Ideal (𝓞 E))⁰ // Ideal.absNorm I.1 = n} :=
        Finite.of_injective
          (fun x : {I : (Ideal (𝓞 E))⁰ // Ideal.absNorm I.1 = n} =>
            (⟨x.1.1, x.2⟩ : {I : Ideal (𝓞 E) // Ideal.absNorm I = n}))
          (fun _ _ h => Subtype.ext (Subtype.ext (Subtype.mk.inj h)))
      let _ : Fintype {I : (Ideal (𝓞 E))⁰ // Ideal.absNorm I.1 = n} := Fintype.ofFinite _
      rw [tsum_fintype, Finset.sum_congr rfl (fun x _ => by rw [x.2]),
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      congr 1
      have heq : {I : (Ideal (𝓞 E))⁰ // Ideal.absNorm I.1 = n} ≃
          {I : Ideal (𝓞 E) // Ideal.absNorm I = n} :=
        { toFun := fun x => ⟨x.1.1, x.2⟩
          invFun := fun x => ⟨⟨x.1, mem_nonZeroDivisors_iff_ne_zero.mpr (by
            intro hbot; exact hn (by rw [← x.2, hbot, Ideal.zero_eq_bot, Ideal.absNorm_bot]))⟩, x.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [← Nat.card_eq_fintype_card, Nat.card_congr heq]

lemma dedekindZeta_re_eq_tsum_ideals {s : ℝ} (hs : 1 < s) :
    (NumberField.dedekindZeta E (s : ℂ)).re =
      ∑' I : (Ideal (𝓞 E))⁰, (Ideal.absNorm (I : Ideal (𝓞 E)) : ℝ) ^ (-s) := by
  have hsI := summable_ideal_absNorm_rpow (E := E) hs
  have hfib :
      ∑' I : (Ideal (𝓞 E))⁰, (Ideal.absNorm (I : Ideal (𝓞 E)) : ℝ) ^ (-s) =
      ∑' n : ℕ, if n = 0 then (0 : ℝ) else
        (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) := by
    rw [← Equiv.tsum_eq (Equiv.sigmaFiberEquiv (fun I : (Ideal (𝓞 E))⁰ => Ideal.absNorm I.1))]
    change ∑' c : (n : ℕ) × {I : (Ideal (𝓞 E))⁰ // Ideal.absNorm I.1 = n},
      (Ideal.absNorm c.2.1.1 : ℝ) ^ (-s) = _
    have hsig := Summable.tsum_sigma'
      (f := fun c : (n : ℕ) × {I : (Ideal (𝓞 E))⁰ // Ideal.absNorm I.1 = n} =>
        (Ideal.absNorm c.2.1.1 : ℝ) ^ (-s))
      (fun n => by
        have : Finite {I : Ideal (𝓞 E) // Ideal.absNorm I = n} :=
          (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 E) n).to_subtype
        have : Finite {I : (Ideal (𝓞 E))⁰ // Ideal.absNorm I.1 = n} :=
          Finite.of_injective
            (fun x : {I : (Ideal (𝓞 E))⁰ // Ideal.absNorm I.1 = n} =>
              (⟨x.1.1, x.2⟩ : {I : Ideal (𝓞 E) // Ideal.absNorm I = n}))
            (fun _ _ h => Subtype.ext (Subtype.ext (Subtype.mk.inj h)))
        exact Summable.of_finite)
      ((Equiv.summable_iff (Equiv.sigmaFiberEquiv (fun I : (Ideal (𝓞 E))⁰ => Ideal.absNorm I.1))).mpr hsI)
    rw [hsig]
    refine tsum_congr fun n => ?_
    by_cases hn : n = 0
    · subst hn
      have : IsEmpty {I : (Ideal (𝓞 E))⁰ // Ideal.absNorm I.1 = 0} :=
        ⟨fun x => Ideal.absNorm_ne_zero_of_nonZeroDivisors x.1 x.2⟩
      simp
    · simp only [if_neg hn]
      have : Finite {I : Ideal (𝓞 E) // Ideal.absNorm I = n} :=
        (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 E) n).to_subtype
      have : Finite {I : (Ideal (𝓞 E))⁰ // Ideal.absNorm I.1 = n} :=
        Finite.of_injective
          (fun x : {I : (Ideal (𝓞 E))⁰ // Ideal.absNorm I.1 = n} =>
            (⟨x.1.1, x.2⟩ : {I : Ideal (𝓞 E) // Ideal.absNorm I = n}))
          (fun _ _ h => Subtype.ext (Subtype.ext (Subtype.mk.inj h)))
      let _ : Fintype {I : (Ideal (𝓞 E))⁰ // Ideal.absNorm I.1 = n} := Fintype.ofFinite _
      rw [tsum_fintype, Finset.sum_congr rfl (fun x _ => by rw [x.2]),
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      congr 1
      have heq : {I : (Ideal (𝓞 E))⁰ // Ideal.absNorm I.1 = n} ≃
          {I : Ideal (𝓞 E) // Ideal.absNorm I = n} :=
        { toFun := fun x => ⟨x.1.1, x.2⟩
          invFun := fun x => ⟨⟨x.1, mem_nonZeroDivisors_iff_ne_zero.mpr (by
            intro hbot; exact hn (by rw [← x.2, hbot, Ideal.zero_eq_bot, Ideal.absNorm_bot]))⟩, x.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [← Nat.card_eq_fintype_card, Nat.card_congr heq]
  rw [hfib, NumberField.dedekindZeta, LSeries]
  have hterm : ∀ n : ℕ,
      LSeries.term (fun k => (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = k} : ℂ)) (s : ℂ) n =
      ((if n = 0 then (0 : ℝ) else
        (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) : ℝ) : ℂ) := by
    intro n
    by_cases hn : n = 0
    · simp [LSeries.term, hn]
    · simp only [LSeries.term, if_neg hn, div_eq_mul_inv, Complex.ofReal_mul,
        Complex.ofReal_natCast, Real.rpow_neg (Nat.cast_nonneg n), Complex.ofReal_inv]
      congr 2
      have hcp : ((n : ℝ) : ℂ) ^ (s : ℂ) = (((n : ℝ) ^ s : ℝ) : ℂ) :=
        (Complex.ofReal_cpow (Nat.cast_nonneg n) s).symm
      simpa [Complex.ofReal_natCast] using hcp
  simp_rw [hterm]
  rw [Complex.re_tsum]
  · simp
  · -- Summable of complexification from summable of real series
    have hreal : Summable (fun n : ℕ =>
        if n = 0 then (0 : ℝ) else
          (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℝ) * (n : ℝ) ^ (-s)) := by
      have h1 : Summable (fun c : (n : ℕ) × {I : (Ideal (𝓞 E))⁰ // Ideal.absNorm I.1 = n} =>
          (Ideal.absNorm c.2.1.1 : ℝ) ^ (-s)) :=
        (Equiv.summable_iff (Equiv.sigmaFiberEquiv
          (fun I : (Ideal (𝓞 E))⁰ => Ideal.absNorm I.1))).mpr hsI
      have h2 := (summable_sigma_of_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)).mp h1
      refine h2.2.congr fun n => ?_
      by_cases hn : n = 0
      · subst hn
        have : IsEmpty {I : (Ideal (𝓞 E))⁰ // Ideal.absNorm I.1 = 0} :=
          ⟨fun x => Ideal.absNorm_ne_zero_of_nonZeroDivisors x.1 x.2⟩
        simp
      · simp only [if_neg hn]
        have : Finite {I : Ideal (𝓞 E) // Ideal.absNorm I = n} :=
          (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 E) n).to_subtype
        have : Finite {I : (Ideal (𝓞 E))⁰ // Ideal.absNorm I.1 = n} :=
          Finite.of_injective
            (fun x : {I : (Ideal (𝓞 E))⁰ // Ideal.absNorm I.1 = n} =>
              (⟨x.1.1, x.2⟩ : {I : Ideal (𝓞 E) // Ideal.absNorm I = n}))
            (fun _ _ h => Subtype.ext (Subtype.ext (Subtype.mk.inj h)))
        let _ : Fintype {I : (Ideal (𝓞 E))⁰ // Ideal.absNorm I.1 = n} := Fintype.ofFinite _
        rw [tsum_fintype, Finset.sum_congr rfl (fun x _ => by rw [x.2]),
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        congr 1
        have heq : {I : (Ideal (𝓞 E))⁰ // Ideal.absNorm I.1 = n} ≃
            {I : Ideal (𝓞 E) // Ideal.absNorm I = n} :=
          { toFun := fun x => ⟨x.1.1, x.2⟩
            invFun := fun x => ⟨⟨x.1, mem_nonZeroDivisors_iff_ne_zero.mpr (by
              intro hbot; exact hn (by rw [← x.2, hbot, Ideal.zero_eq_bot, Ideal.absNorm_bot]))⟩, x.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        rw [← Nat.card_eq_fintype_card, Nat.card_congr heq]
    exact Complex.summable_ofReal.mpr hreal

/-- Discrete Abel summation: if `|∑_{k=1}^N a_k| ≤ M * N^(1 - δ)` with `0 < δ ≤ 1`, then
`|∑' n, a_n * n^(-s)|` is uniformly bounded for all `s ∈ (1, 2]`. -/
lemma abs_tsum_rpow_le_of_partial_sum_bound
    (a : ℕ → ℝ) (ha0 : a 0 = 0) {M δ : ℝ} (hM : 0 ≤ M) (hδ0 : 0 < δ)
    (hS : ∀ N : ℕ, 1 ≤ N → |∑ k ∈ Finset.Icc 1 N, a k| ≤ M * (N : ℝ) ^ (1 - δ))
    {s : ℝ} (hs1 : 1 < s) (hs2 : s ≤ 2)
    (hsumm : Summable (fun n : ℕ => a n * (n : ℝ) ^ (-s))) :
    |∑' n : ℕ, a n * (n : ℝ) ^ (-s)| ≤
      2 * M * ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-(1 + δ)) := by
  let S : ℕ → ℝ := fun N => ∑ k ∈ Finset.Icc 1 N, a k
  have hS0 : S 0 = 0 := by simp [S]
  have ha_eq : ∀ k : ℕ, a (k + 1) = S (k + 1) - S k := by
    intro k
    dsimp [S]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
    ring
  -- Summation by parts on range (N + 1)
  have hpart : ∀ N : ℕ, 1 ≤ N →
      ∑ n ∈ Finset.range (N + 1), a n * (n : ℝ) ^ (-s) =
        S N * (N : ℝ) ^ (-s) +
        ∑ k ∈ Finset.range (N - 1),
          S (k + 1) * (((k + 1 : ℕ) : ℝ) ^ (-s) - ((k + 2 : ℕ) : ℝ) ^ (-s)) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      simp [Finset.sum_range_succ, ha0, S]
    | succ N hN ih =>
      rw [Finset.sum_range_succ, ih, ha_eq N]
      have hsub : N + 1 - 1 = (N - 1) + 1 := by omega
      rw [hsub, Finset.sum_range_succ]
      have hN1 : N - 1 + 1 = N := by omega
      have hN2 : N - 1 + 2 = N + 1 := by omega
      rw [hN1, hN2]
      ring
  -- Bound on k^(-s) - (k+1)^(-s) ≤ s * k^(-s-1) by MVT
  have hdiff_le : ∀ k : ℕ,
      0 ≤ ((k + 1 : ℕ) : ℝ) ^ (-s) - ((k + 2 : ℕ) : ℝ) ^ (-s) ∧
      ((k + 1 : ℕ) : ℝ) ^ (-s) - ((k + 2 : ℕ) : ℝ) ^ (-s) ≤
        s * ((k + 1 : ℕ) : ℝ) ^ (-s - 1) := by
    intro k
    have hk1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hk2 : ((k + 1 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : k + 1 ≤ k + 2)
    constructor
    · rw [sub_nonneg]
      exact Real.rpow_le_rpow_of_nonpos hk1 hk2 (by linarith)
    · have hlt : ((k + 1 : ℕ) : ℝ) < ((k + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : k + 1 < k + 2)
      have hcont : ContinuousOn (fun t : ℝ => t ^ (-s)) (Set.Icc ((k + 1 : ℕ) : ℝ) ((k + 2 : ℕ) : ℝ)) :=
        fun t ht => (Real.continuousAt_rpow_const t (-s) (Or.inl (lt_of_lt_of_le hk1 ht.1).ne')).continuousWithinAt
      have hderiv : ∀ t ∈ Set.Ioo ((k + 1 : ℕ) : ℝ) ((k + 2 : ℕ) : ℝ),
          HasDerivAt (fun t : ℝ => t ^ (-s)) ((-s) * t ^ (-s - 1)) t :=
        fun t ht => Real.hasDerivAt_rpow_const (Or.inl (hk1.trans ht.1).ne')
      obtain ⟨c, hc, hce⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ (-s)) _ hlt hcont hderiv
      have hsub1 : ((k + 2 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ) = 1 := by push_cast; ring
      rw [hsub1, div_one] at hce
      have hneg : ((k + 1 : ℕ) : ℝ) ^ (-s) - ((k + 2 : ℕ) : ℝ) ^ (-s) = s * c ^ (-s - 1) := by
        linarith
      rw [hneg]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hk1 hc.1.le (by linarith)) (by linarith)
  -- Bound each term of the partial sum for N ≥ 1
  have hsumm_maj : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-(1 + δ))) := by
    have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-(1 + δ))) := by
      simpa [Real.rpow_neg (Nat.cast_nonneg _)] using
        Real.summable_nat_rpow_inv.mpr (by linarith : 1 < 1 + δ)
    exact (summable_nat_add_iff 1).mpr h1
  have hterm_le : ∀ k : ℕ,
      |S (k + 1) * (((k + 1 : ℕ) : ℝ) ^ (-s) - ((k + 2 : ℕ) : ℝ) ^ (-s))| ≤
        2 * M * ((k + 1 : ℕ) : ℝ) ^ (-(1 + δ)) := by
    intro k
    have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 1)
    have hk0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    rw [abs_mul, abs_of_nonneg (hdiff_le k).1]
    calc |S (k + 1)| * (((k + 1 : ℕ) : ℝ) ^ (-s) - ((k + 2 : ℕ) : ℝ) ^ (-s))
        ≤ (M * ((k + 1 : ℕ) : ℝ) ^ (1 - δ)) * (s * ((k + 1 : ℕ) : ℝ) ^ (-s - 1)) := by
          exact mul_le_mul (hS (k + 1) (by omega)) (hdiff_le k).2 (hdiff_le k).1 (by positivity)
      _ = s * M * (((k + 1 : ℕ) : ℝ) ^ (1 - δ) * ((k + 1 : ℕ) : ℝ) ^ (-s - 1)) := by ring
      _ = s * M * ((k + 1 : ℕ) : ℝ) ^ (-s - δ) := by
          rw [← Real.rpow_add hk0]; congr 2; ring
      _ ≤ 2 * M * ((k + 1 : ℕ) : ℝ) ^ (-s - δ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs2 hM)
            (Real.rpow_nonneg hk0.le _)
      _ ≤ 2 * M * ((k + 1 : ℕ) : ℝ) ^ (-(1 + δ)) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hk1 (by linarith)) (by positivity)
  -- Take limit as N → ∞
  have htend_lhs : Tendsto (fun N : ℕ => |∑ n ∈ Finset.range (N + 1), a n * (n : ℝ) ^ (-s)|)
      atTop (𝓝 |∑' n : ℕ, a n * (n : ℝ) ^ (-s)|) :=
    (hsumm.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).abs
  have htend_rem : Tendsto (fun N : ℕ => |S N * (N : ℝ) ^ (-s)|) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (show Tendsto (fun N : ℕ => M * (N : ℝ) ^ (1 - δ - s)) atTop (𝓝 0) by
      simpa using ((tendsto_rpow_neg_atTop (show 0 < -(1 - δ - s) by linarith)).comp
        tendsto_natCast_atTop_atTop).const_mul M)
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Real.norm_eq_abs, abs_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hN0.le _)]
    calc |S N| * (N : ℝ) ^ (-s)
        ≤ M * (N : ℝ) ^ (1 - δ) * (N : ℝ) ^ (-s) :=
          mul_le_mul_of_nonneg_right (hS N hN) (Real.rpow_nonneg hN0.le _)
      _ = M * (N : ℝ) ^ (1 - δ - s) := by
          rw [mul_assoc, ← Real.rpow_add hN0, ← sub_eq_add_neg]
  have htend_rhs : Tendsto (fun N : ℕ =>
      |S N * (N : ℝ) ^ (-s)| + 2 * M * ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-(1 + δ)))
      atTop (𝓝 (2 * M * ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-(1 + δ)))) := by
    have := htend_rem.add (tendsto_const_nhds (x := 2 * M * ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-(1 + δ))))
    rwa [zero_add] at this
  refine le_of_tendsto_of_tendsto' htend_lhs htend_rhs ?_
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [zero_add, Finset.sum_range_one, ha0, zero_mul, abs_zero, S,
      Finset.Icc_eq_empty (by omega : ¬ 1 ≤ 0), Finset.sum_empty]
    exact mul_nonneg (by positivity) (tsum_nonneg fun k => Real.rpow_nonneg (by positivity) _)
  · rw [hpart N hN]
    calc |S N * (N : ℝ) ^ (-s) + ∑ k ∈ Finset.range (N - 1),
            S (k + 1) * (((k + 1 : ℕ) : ℝ) ^ (-s) - ((k + 2 : ℕ) : ℝ) ^ (-s))|
        ≤ |S N * (N : ℝ) ^ (-s)| + |∑ k ∈ Finset.range (N - 1),
            S (k + 1) * (((k + 1 : ℕ) : ℝ) ^ (-s) - ((k + 2 : ℕ) : ℝ) ^ (-s))| := abs_add_le _ _
      _ ≤ |S N * (N : ℝ) ^ (-s)| +
            ∑ k ∈ Finset.range (N - 1), 2 * M * ((k + 1 : ℕ) : ℝ) ^ (-(1 + δ)) := by
          gcongr
          exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hterm_le k)
      _ ≤ |S N * (N : ℝ) ^ (-s)| + 2 * M * ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-(1 + δ)) := by
          gcongr
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left
            (hsumm_maj.sum_le_tsum (Finset.range (N - 1))
              (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)) (by positivity)

/-- Fiberwise decomposition of ideals of norm `≤ N` in a fixed ideal class. -/
lemma card_norm_le_and_mk_eq_sum (F : Type) [Field F] [NumberField F]
    (C : ClassGroup (𝓞 F)) (N : ℕ) :
    Nat.card {I : (Ideal (𝓞 F))⁰ //
        (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) ≤ (N : ℝ) ∧ ClassGroup.mk0 I = C} =
      ∑ k ∈ Finset.Icc 1 N,
        Nat.card {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm I.1 = k ∧ ClassGroup.mk0 I = C} := by
  classical
  have hfinLe := Ideal.finite_setOfPred_absNorm_le₀ (S := 𝓞 F) N
  let Sle : Finset (Ideal (𝓞 F))⁰ := hfinLe.toFinset.filter (fun I => ClassGroup.mk0 I = C)
  have hSle_iff : ∀ I : (Ideal (𝓞 F))⁰,
      ((Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) ≤ (N : ℝ) ∧ ClassGroup.mk0 I = C) ↔ I ∈ Sle := by
    intro I
    simp only [Sle, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Nat.cast_le]
  have hlhs :
      Nat.card {I : (Ideal (𝓞 F))⁰ //
          (Ideal.absNorm (I : Ideal (𝓞 F)) : ℝ) ≤ (N : ℝ) ∧ ClassGroup.mk0 I = C} = Sle.card := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight hSle_iff), Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hlhs, Finset.card_eq_sum_card_fiberwise (f := fun I : (Ideal (𝓞 F))⁰ => Ideal.absNorm I.1)
    (s := Sle) (t := Finset.Icc 1 N) (fun I hI => by
      have hI' : Ideal.absNorm I.1 ≤ N :=
        (Set.Finite.mem_toFinset hfinLe).mp (Finset.mem_filter.mp hI).1
      exact Finset.mem_Icc.mpr ⟨Ideal.absNorm_pos_of_nonZeroDivisors I, hI'⟩)]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hSk_iff : ∀ I : (Ideal (𝓞 F))⁰,
      (Ideal.absNorm I.1 = k ∧ ClassGroup.mk0 I = C) ↔
        I ∈ Sle.filter (fun I => Ideal.absNorm I.1 = k) := by
    intro I
    simp only [Sle, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hkI, hC⟩
      exact ⟨⟨le_trans (le_of_eq hkI) (Finset.mem_Icc.mp hk).2, hC⟩, hkI⟩
    · rintro ⟨⟨_, hC⟩, hkI⟩
      exact ⟨hkI, hC⟩
  rw [Nat.card_congr (Equiv.subtypeEquivRight hSk_iff), Nat.card_eq_fintype_card, Fintype.card_coe]

/-- Group a real character L-series over ideals by absolute norm into a Dirichlet series over `ℕ`. -/
lemma tsum_character_eq_tsum_nat (F : Type) [Field F] [NumberField F]
    [Fintype (ClassGroup (𝓞 F))]
    (χ : ClassGroup (𝓞 F) →* ℝ) (hpm : ∀ g, χ g = 1 ∨ χ g = -1)
    {s : ℝ} (hs1 : 1 < s) :
    let a : ℕ → ℝ := fun n =>
      if n = 0 then 0 else
        ∑ C : ClassGroup (𝓞 F),
          χ C * (Nat.card {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm I.1 = n ∧ ClassGroup.mk0 I = C} : ℝ)
    (∑' I : (Ideal (𝓞 F))⁰, χ (ClassGroup.mk0 I) * (Ideal.absNorm I.1 : ℝ) ^ (-s) =
      ∑' n : ℕ, a n * (n : ℝ) ^ (-s)) ∧
    Summable (fun n : ℕ => a n * (n : ℝ) ^ (-s)) := by
  classical
  intro a
  have hsI := summable_ideal_absNorm_rpow (E := F) hs1
  have hsχ : Summable (fun I : (Ideal (𝓞 F))⁰ =>
      χ (ClassGroup.mk0 I) * (Ideal.absNorm I.1 : ℝ) ^ (-s)) := by
    refine Summable.of_norm_bounded hsI fun I => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    rcases hpm (ClassGroup.mk0 I) with h | h <;> simp [h]
  have hSn_fin : ∀ n : ℕ, Set.Finite {I : (Ideal (𝓞 F))⁰ | Ideal.absNorm I.1 = n} :=
    fun n => (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 F) n).preimage
      (by intro _ _ _ _ h; exact Subtype.ext h)
  let Sn (n : ℕ) : Finset (Ideal (𝓞 F))⁰ := (hSn_fin n).toFinset
  have hSn_mem : ∀ n I, I ∈ Sn n ↔ Ideal.absNorm I.1 = n := fun n I =>
    Set.Finite.mem_toFinset (hSn_fin n)
  have hfiber_val : ∀ n : ℕ,
      ∑' x : {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm I.1 = n},
        χ (ClassGroup.mk0 x.1) * (Ideal.absNorm x.1.1 : ℝ) ^ (-s) = a n * (n : ℝ) ^ (-s) := by
    intro n
    have htsum_eq :
        ∑' x : {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm I.1 = n},
          χ (ClassGroup.mk0 x.1) * (Ideal.absNorm x.1.1 : ℝ) ^ (-s) =
        ∑ I ∈ Sn n, χ (ClassGroup.mk0 I) * (Ideal.absNorm I.1 : ℝ) ^ (-s) := by
      let heqS : {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm I.1 = n} ≃ ↥(Sn n) :=
        Equiv.subtypeEquivRight fun I => (hSn_mem n I).symm
      rw [← Equiv.tsum_eq heqS.symm, tsum_fintype]
      have hcoe : ∀ b : ↥(Sn n), (heqS.symm b).1 = b.1 := fun _ => rfl
      simp_rw [hcoe]
      exact Finset.sum_coe_sort (Sn n) fun I => χ (ClassGroup.mk0 I) * (Ideal.absNorm I.1 : ℝ) ^ (-s)
    rw [htsum_eq]
    by_cases hn : n = 0
    · subst hn
      simp only [a, if_pos rfl, zero_mul]
      have hSn0 : Sn 0 = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro I hI
        exact Ideal.absNorm_ne_zero_of_nonZeroDivisors I ((hSn_mem 0 I).mp hI)
      simp [hSn0]
    · simp only [a, if_neg hn]
      rw [Finset.sum_congr rfl (fun I hI => by rw [(hSn_mem n I).mp hI]), ← Finset.sum_mul]
      congr 1
      rw [← Finset.sum_fiberwise (Sn n) (fun I => ClassGroup.mk0 I) (fun I => χ (ClassGroup.mk0 I))]
      refine Finset.sum_congr rfl fun C _ => ?_
      rw [Finset.sum_congr rfl (fun I hI => by rw [(Finset.mem_filter.mp hI).2]),
        Finset.sum_const, nsmul_eq_mul, mul_comm]
      congr 1
      have hiff : ∀ I : (Ideal (𝓞 F))⁰,
          (Ideal.absNorm I.1 = n ∧ ClassGroup.mk0 I = C) ↔
            I ∈ (Sn n).filter (fun I => ClassGroup.mk0 I = C) := by
        intro I
        simp only [Finset.mem_filter, hSn_mem]
      rw [Nat.card_congr (Equiv.subtypeEquivRight hiff), Nat.card_eq_fintype_card, Fintype.card_coe]
  constructor
  · rw [← Equiv.tsum_eq (Equiv.sigmaFiberEquiv (fun I : (Ideal (𝓞 F))⁰ => Ideal.absNorm I.1))]
    change ∑' c : (n : ℕ) × {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm I.1 = n},
      χ (ClassGroup.mk0 c.2.1) * (Ideal.absNorm c.2.1.1 : ℝ) ^ (-s) = _
    have hsig := Summable.tsum_sigma'
      (f := fun c : (n : ℕ) × {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm I.1 = n} =>
        χ (ClassGroup.mk0 c.2.1) * (Ideal.absNorm c.2.1.1 : ℝ) ^ (-s))
      (fun n => by
        have : Finite {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm I.1 = n} := (hSn_fin n).to_subtype
        exact Summable.of_finite)
      ((Equiv.summable_iff (Equiv.sigmaFiberEquiv (fun I : (Ideal (𝓞 F))⁰ => Ideal.absNorm I.1))).mpr hsχ)
    rw [hsig]
    exact tsum_congr hfiber_val
  · have h1 : Summable (fun c : (n : ℕ) × {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm I.1 = n} =>
        (Ideal.absNorm c.2.1.1 : ℝ) ^ (-s)) :=
      (Equiv.summable_iff (Equiv.sigmaFiberEquiv
        (fun I : (Ideal (𝓞 F))⁰ => Ideal.absNorm I.1))).mpr hsI
    have h2 : Summable (fun n : ℕ =>
        ∑' x : {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm I.1 = n}, (Ideal.absNorm x.1.1 : ℝ) ^ (-s)) :=
      ((summable_sigma_of_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)).mp h1).2
    refine Summable.of_norm_bounded h2 fun n => ?_
    rw [← hfiber_val n]
    let heqS : {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm I.1 = n} ≃ ↥(Sn n) :=
      Equiv.subtypeEquivRight fun I => (hSn_mem n I).symm
    rw [← Equiv.tsum_eq heqS.symm, ← Equiv.tsum_eq heqS.symm, tsum_fintype, tsum_fintype,
      Real.norm_eq_abs]
    have hcoe : ∀ b : ↥(Sn n), (heqS.symm b).1 = b.1 := fun _ => rfl
    simp_rw [hcoe]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    rcases hpm (ClassGroup.mk0 x.1) with h | h <;> simp [h]

/-- For a totally real number field `F` and a nontrivial `{±1}`-valued character `χ` on
`ClassGroup (𝓞 F)`, the real L-series `L(s, χ)` is uniformly bounded on `s ∈ (1, 2]`. -/
lemma nontrivial_character_LSeries_bdd (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (χ : ClassGroup (𝓞 F) →* ℝ)
    (hpm : ∀ g, χ g = 1 ∨ χ g = -1)
    (hneg : ∃ g, χ g = -1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℝ, 1 < s → s ≤ 2 →
      |∑' I : (Ideal (𝓞 F))⁰, χ (ClassGroup.mk0 I) * (Ideal.absNorm I.1 : ℝ) ^ (-s)| ≤ B := by
  classical
  let _ : Fintype (ClassGroup (𝓞 F)) := Fintype.ofFinite _
  let κ : ℝ := (2 ^ nrRealPlaces F * (2 * π) ^ nrComplexPlaces F * Units.regulator F) /
    (Units.torsionOrder F * Real.sqrt |discr F|)
  choose MC hMC0 hMC using fun C : ClassGroup (𝓞 F) => weber_ideal_class_counting_error F C
  let M : ℝ := ∑ C : ClassGroup (𝓞 F), MC C
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun C _ => hMC0 C
  let δ : ℝ := (Module.finrank ℚ F : ℝ)⁻¹
  have hδ0 : 0 < δ := inv_pos.mpr (Nat.cast_pos.mpr Module.finrank_pos)
  let a : ℕ → ℝ := fun n =>
    if n = 0 then 0 else
      ∑ C : ClassGroup (𝓞 F),
        χ C * (Nat.card {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm I.1 = n ∧ ClassGroup.mk0 I = C} : ℝ)
  have hsum_χ : ∑ C : ClassGroup (𝓞 F), χ C = 0 := sum_character_eq_zero χ hneg
  have hS_bound : ∀ N : ℕ, 1 ≤ N → |∑ k ∈ Finset.Icc 1 N, a k| ≤ M * (N : ℝ) ^ (1 - δ) := by
    intro N hN
    have hswap : ∑ k ∈ Finset.Icc 1 N, a k =
        ∑ C : ClassGroup (𝓞 F), χ C *
          ((Nat.card {I : (Ideal (𝓞 F))⁰ //
            Ideal.absNorm (I : Ideal (𝓞 F)) ≤ (N : ℝ) ∧ ClassGroup.mk0 I = C} : ℝ) - κ * N) := by
      have h1 : ∑ k ∈ Finset.Icc 1 N, a k =
          ∑ C : ClassGroup (𝓞 F), χ C *
            (∑ k ∈ Finset.Icc 1 N,
              (Nat.card {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm I.1 = k ∧ ClassGroup.mk0 I = C} : ℝ)) := by
        calc ∑ k ∈ Finset.Icc 1 N, a k
            = ∑ k ∈ Finset.Icc 1 N, ∑ C : ClassGroup (𝓞 F),
                χ C * (Nat.card {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm I.1 = k ∧ ClassGroup.mk0 I = C} : ℝ) :=
              Finset.sum_congr rfl fun k hk => by
                have hk0 : k ≠ 0 := (lt_of_lt_of_le zero_lt_one (Finset.mem_Icc.mp hk).1).ne'
                simp [a, hk0]
          _ = ∑ C : ClassGroup (𝓞 F), ∑ k ∈ Finset.Icc 1 N,
                χ C * (Nat.card {I : (Ideal (𝓞 F))⁰ // Ideal.absNorm I.1 = k ∧ ClassGroup.mk0 I = C} : ℝ) :=
              Finset.sum_comm
          _ = _ := Finset.sum_congr rfl fun C _ => (Finset.mul_sum _ _ _).symm
      rw [h1]
      have hκ0 : ∑ C : ClassGroup (𝓞 F), χ C * (κ * N) = 0 := by
        rw [← Finset.sum_mul, hsum_χ, zero_mul]
      have hsub :
          ∑ C : ClassGroup (𝓞 F), χ C *
            ((Nat.card {I : (Ideal (𝓞 F))⁰ //
              Ideal.absNorm (I : Ideal (𝓞 F)) ≤ (N : ℝ) ∧ ClassGroup.mk0 I = C} : ℝ) - κ * N) =
          (∑ C : ClassGroup (𝓞 F), χ C *
            (Nat.card {I : (Ideal (𝓞 F))⁰ //
              Ideal.absNorm (I : Ideal (𝓞 F)) ≤ (N : ℝ) ∧ ClassGroup.mk0 I = C} : ℝ)) -
          ∑ C : ClassGroup (𝓞 F), χ C * (κ * N) := by
        simp_rw [mul_sub, Finset.sum_sub_distrib]
      rw [hsub, hκ0, sub_zero]
      refine Finset.sum_congr rfl fun C _ => ?_
      rw [card_norm_le_and_mk_eq_sum F C N, Nat.cast_sum]
    rw [hswap]
    calc |∑ C : ClassGroup (𝓞 F), _|
        ≤ ∑ C : ClassGroup (𝓞 F), |χ C * _| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ C : ClassGroup (𝓞 F),
            |(Nat.card {I : (Ideal (𝓞 F))⁰ //
              Ideal.absNorm (I : Ideal (𝓞 F)) ≤ (N : ℝ) ∧ ClassGroup.mk0 I = C} : ℝ) - κ * N| :=
          Finset.sum_congr rfl fun C _ => by
            rw [abs_mul]
            rcases hpm C with h | h <;> rw [h] <;> simp
      _ ≤ ∑ C : ClassGroup (𝓞 F), MC C * (N : ℝ) ^ (1 - δ) :=
          Finset.sum_le_sum fun C _ => hMC C N (by exact_mod_cast hN)
      _ = M * (N : ℝ) ^ (1 - δ) := (Finset.sum_mul _ _ _).symm
  refine ⟨2 * M * ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (-(1 + δ)),
    mul_nonneg (by positivity) (tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _), fun s hs1 hs2 => ?_⟩
  obtain ⟨hfib_eq, hsumm_n⟩ := tsum_character_eq_tsum_nat F χ hpm hs1
  rw [hfib_eq]
  exact abs_tsum_rpow_le_of_partial_sum_bound a (by simp [a]) hM0 hδ0 hS_bound hs1 hs2 hsumm_n

/- ### Finite Euler products -/

lemma normalizedFactors_finset_prod_ideals {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → Ideal (𝓞 E)) (hf : ∀ a ∈ s, f a ≠ ⊥) :
    UniqueFactorizationMonoid.normalizedFactors (∏ a ∈ s, f a) =
      ∑ a ∈ s, UniqueFactorizationMonoid.normalizedFactors (f a) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty, UniqueFactorizationMonoid.normalizedFactors_one]
  | @insert a s has ih =>
    have ha : f a ≠ ⊥ := hf a (Finset.mem_insert_self a s)
    have hs : ∏ b ∈ s, f b ≠ ⊥ := Finset.prod_ne_zero_iff.mpr fun b hb =>
      hf b (Finset.mem_insert_of_mem hb)
    rw [Finset.prod_insert has, Finset.sum_insert has,
      UniqueFactorizationMonoid.normalizedFactors_mul ha hs,
      ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))]

lemma multiset_prod_eq_toFinset_count_pow {M : Type*} [CommMonoid M] [DecidableEq M]
    (m : Multiset M) :
    m.prod = ∏ x ∈ m.toFinset, x ^ Multiset.count x m := by
  induction m using Multiset.induction_on with
  | empty => simp
  | @cons a m ih =>
    rw [Multiset.prod_cons, ih, Multiset.toFinset_cons]
    by_cases ha : a ∈ m.toFinset
    · rw [Finset.insert_eq_of_mem ha]
      calc a * ∏ x ∈ m.toFinset, x ^ Multiset.count x m
          = a * (a ^ Multiset.count a m * ∏ x ∈ m.toFinset.erase a, x ^ Multiset.count x m) := by
            rw [← Finset.mul_prod_erase m.toFinset (fun x => x ^ Multiset.count x m) ha]
        _ = a ^ (Multiset.count a m + 1) * ∏ x ∈ m.toFinset.erase a, x ^ Multiset.count x m := by
            rw [← mul_assoc, pow_succ']
        _ = a ^ Multiset.count a (a ::ₘ m) *
              ∏ x ∈ m.toFinset.erase a, x ^ Multiset.count x (a ::ₘ m) := by
            rw [Multiset.count_cons_self]
            congr 1
            refine Finset.prod_congr rfl fun x hx => ?_
            rw [Multiset.count_cons_of_ne (Finset.mem_erase.mp hx).1]
        _ = ∏ x ∈ m.toFinset, x ^ Multiset.count x (a ::ₘ m) :=
            Finset.mul_prod_erase m.toFinset (fun x => x ^ Multiset.count x (a ::ₘ m)) ha
    · rw [Finset.prod_insert ha, Multiset.count_cons_self,
        Multiset.count_eq_zero.mpr (by simpa using ha), pow_one]
      congr 1
      refine Finset.prod_congr rfl fun x hx => ?_
      have hne : x ≠ a := fun h => ha (h ▸ hx)
      rw [Multiset.count_cons_of_ne hne]

/-- Expansion of a finite Euler product over a `Finset` of nonzero prime ideals `S` into a
sum over `S`-smooth nonzero ideals (ideals whose prime factors all lie in `S`). -/
lemma finite_euler_prod_eq_tsum_smooth
    (g : (Ideal (𝓞 E))⁰ →* ℝ) (hg : ∀ I, |g I| ≤ 1)
    {s : ℝ} (hs : 1 < s)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) :
    let smooth (I : (Ideal (𝓞 E))⁰) : Prop :=
      ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 E), p.asIdeal ∣ I.1 → p ∈ S
    ∏ p ∈ S,
      (1 - g ⟨p.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr p.ne_bot⟩ *
        (Ideal.absNorm p.asIdeal : ℝ) ^ (-s))⁻¹ =
    ∑' I : {I : (Ideal (𝓞 E))⁰ // smooth I},
      g I.1 * (Ideal.absNorm I.1.1 : ℝ) ^ (-s) := by
  classical
  -- Step 1: By induction on S, expand the product into a tsum over exponent functions S → ℕ.
  have hexp :
      ∏ p ∈ S,
        (1 - g ⟨p.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr p.ne_bot⟩ *
          (Ideal.absNorm p.asIdeal : ℝ) ^ (-s))⁻¹ =
      ∑' e : S → ℕ,
        g (∏ p : S, (⟨p.1.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr p.1.ne_bot⟩ : (Ideal (𝓞 E))⁰) ^ e p) *
          (Ideal.absNorm (∏ p : S, p.1.asIdeal ^ e p) : ℝ) ^ (-s) := by
    induction S using Finset.induction_on with
    | empty =>
      simp
    | @insert p S hpS ih =>
      rw [Finset.prod_insert hpS, ih]
      let p0 : (Ideal (𝓞 E))⁰ := ⟨p.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr p.ne_bot⟩
      let r : ℝ := g p0 * (Ideal.absNorm p.asIdeal : ℝ) ^ (-s)
      have hNp_gt1 : 1 < Ideal.absNorm p.asIdeal := by
        have hne0 : Ideal.absNorm p.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot
        have hne1 : Ideal.absNorm p.asIdeal ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr p.isPrime.ne_top
        omega
      have hr_lt1 : |r| < 1 := by
        dsimp [r]
        have hrpow_nn : 0 ≤ (Ideal.absNorm p.asIdeal : ℝ) ^ (-s) :=
          Real.rpow_nonneg (Nat.cast_nonneg _) _
        rw [abs_mul, abs_of_nonneg hrpow_nn]
        have hpow : (Ideal.absNorm p.asIdeal : ℝ) ^ (-s) < 1 := by
          rw [Real.rpow_neg (Nat.cast_nonneg _)]
          exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by exact_mod_cast hNp_gt1) (by linarith))
        calc |g p0| * (Ideal.absNorm p.asIdeal : ℝ) ^ (-s)
            ≤ 1 * (Ideal.absNorm p.asIdeal : ℝ) ^ (-s) :=
              mul_le_mul_of_nonneg_right (hg p0) hrpow_nn
          _ < 1 := by linarith
      have hgeom : (1 - r)⁻¹ = ∑' k : ℕ, r ^ k := (tsum_geometric_of_abs_lt_one hr_lt1).symm
      have hsum_r : Summable (fun k : ℕ => ‖r ^ k‖) := by
        simpa [Real.norm_eq_abs, abs_pow] using summable_geometric_of_lt_one (abs_nonneg r) hr_lt1
      -- Summability of the S-exponent sum (injection into ideals)
      have hinj_S : Function.Injective (fun e : S → ℕ =>
          (∏ q : S, (⟨q.1.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr q.1.ne_bot⟩ : (Ideal (𝓞 E))⁰) ^ e q)) := by
        intro e₁ e₂ heq
        ext ⟨q, hqS⟩
        have hval : ∏ a : S, a.1.asIdeal ^ e₁ a = ∏ a : S, a.1.asIdeal ^ e₂ a := by
          simpa [Submonoid.coe_finsetProd] using congrArg Subtype.val heq
        have hcnt := congrArg (fun I => Multiset.count q.asIdeal (UniqueFactorizationMonoid.normalizedFactors I)) hval
        -- Use Ideal.count_normalizedFactors / multiplicity at q
        have hcnt_prod : ∀ e : S → ℕ,
            Multiset.count q.asIdeal (UniqueFactorizationMonoid.normalizedFactors (∏ a : S, a.1.asIdeal ^ e a)) =
              e ⟨q, hqS⟩ := by
          intro e
          have hne : ∀ a : S, a.1.asIdeal ^ e a ≠ ⊥ := fun a => pow_ne_zero _ a.1.ne_bot
          rw [normalizedFactors_finset_prod_ideals Finset.univ _ (fun a _ => hne a),
            Multiset.count_sum']
          have hterm : ∀ a : S,
              Multiset.count q.asIdeal (UniqueFactorizationMonoid.normalizedFactors (a.1.asIdeal ^ e a)) =
                if a = ⟨q, hqS⟩ then e a else 0 := by
            intro a
            rw [UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul,
              UniqueFactorizationMonoid.normalizedFactors_irreducible a.1.prime.irreducible,
              normalize_eq, Multiset.count_singleton]
            by_cases haq : a = ⟨q, hqS⟩
            · subst haq; simp
            · have hne_id : q.asIdeal ≠ a.1.asIdeal := fun h =>
                haq (Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext h.symm))
              simp [haq, hne_id]
          simp_rw [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_pos trivial]
        rw [hcnt_prod e₁, hcnt_prod e₂] at hcnt
        exact hcnt
      have hsum_S : Summable (fun e : S → ℕ =>
          ‖g (∏ q : S, (⟨q.1.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr q.1.ne_bot⟩ : (Ideal (𝓞 E))⁰) ^ e q) *
            (Ideal.absNorm (∏ q : S, q.1.asIdeal ^ e q) : ℝ) ^ (-s)‖) := by
        have hsE := (summable_ideal_absNorm_rpow (E := E) hs).comp_injective hinj_S
        refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun e => ?_) hsE
        have hrpow_nn : 0 ≤ (Ideal.absNorm (∏ q : S, q.1.asIdeal ^ e q) : ℝ) ^ (-s) :=
          Real.rpow_nonneg (Nat.cast_nonneg _) _
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hrpow_nn]
        have hcoe : (∏ q : S, (⟨q.1.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr q.1.ne_bot⟩ :
            (Ideal (𝓞 E))⁰) ^ e q).1 = ∏ q : S, q.1.asIdeal ^ e q := by
          simp
        change |g _| * (Ideal.absNorm (∏ q : S, q.1.asIdeal ^ e q) : ℝ) ^ (-s) ≤
          (Ideal.absNorm (∏ q : S, (⟨q.1.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr q.1.ne_bot⟩ :
            (Ideal (𝓞 E))⁰) ^ e q).1 : ℝ) ^ (-s)
        rw [hcoe]
        exact mul_le_of_le_one_left hrpow_nn (hg _)
      rw [hgeom, tsum_mul_tsum_of_summable_norm hsum_r hsum_S]
      -- Equiv between (ℕ × (S → ℕ)) and (insert p S → ℕ)
      let eSplit : (ℕ × (S → ℕ)) ≃ (↥(insert p S) → ℕ) :=
        { toFun := fun x q => if h : q.1 = p then x.1 else x.2 ⟨q.1, (Finset.mem_insert.mp q.2).resolve_left h⟩
          invFun := fun f => (f ⟨p, Finset.mem_insert_self p S⟩,
            fun q => f ⟨q.1, Finset.mem_insert_of_mem q.2⟩)
          left_inv := fun ⟨k, f⟩ => by
            ext
            · simp
            · rename_i q
              have hne : q.1 ≠ p := fun h => hpS (h ▸ q.2)
              simp [hne]
          right_inv := fun f => by
            ext ⟨q, hq⟩
            by_cases h : q = p
            · subst h; simp
            · simp [h] }
      rw [← Equiv.tsum_eq eSplit]
      refine tsum_congr fun ⟨k, f⟩ => ?_
      have hprod_id :
          ∏ q : ↥(insert p S), (⟨q.1.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr q.1.ne_bot⟩ :
            (Ideal (𝓞 E))⁰) ^ eSplit (k, f) q =
          p0 ^ k * ∏ q : S, (⟨q.1.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr q.1.ne_bot⟩ :
            (Ideal (𝓞 E))⁰) ^ f q := by
        have hmem_p : (⟨p, Finset.mem_insert_self p S⟩ : ↥(insert p S)) ∈
            (Finset.univ : Finset ↥(insert p S)) := Finset.mem_univ _
        rw [← Finset.mul_prod_erase _ _ hmem_p]
        have hp_term : (⟨p.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr p.ne_bot⟩ : (Ideal (𝓞 E))⁰) ^
            eSplit (k, f) ⟨p, Finset.mem_insert_self p S⟩ = p0 ^ k := by
          simp [eSplit, p0]
        rw [hp_term]
        congr 1
        refine Finset.prod_bij (fun (q : ↥(insert p S)) (hq : q ∈ Finset.univ.erase ⟨p, Finset.mem_insert_self p S⟩) =>
            (⟨q.1, (Finset.mem_insert.mp q.2).resolve_left
              (fun h => (Finset.mem_erase.mp hq).1 (Subtype.ext h))⟩ : S)) ?_ ?_ ?_ ?_
        · intro _ _; exact Finset.mem_univ _
        · intro q₁ _ q₂ _ h
          exact Subtype.ext (Subtype.mk.inj h)
        · intro q _
          refine ⟨⟨q.1, Finset.mem_insert_of_mem q.2⟩,
            Finset.mem_erase.mpr ⟨fun h => hpS ((Subtype.mk.inj h) ▸ q.2), Finset.mem_univ _⟩,
            rfl⟩
        · intro q hq
          have hne : q.1 ≠ p := fun h => (Finset.mem_erase.mp hq).1 (Subtype.ext h)
          simp [eSplit, hne]
      have hprod_val :
          ∏ q : ↥(insert p S), q.1.asIdeal ^ eSplit (k, f) q =
          p.asIdeal ^ k * ∏ q : S, q.1.asIdeal ^ f q := by
        have := congrArg Subtype.val hprod_id
        simpa [p0] using this
      rw [hprod_id, hprod_val, map_mul, map_pow, map_mul, map_pow, Nat.cast_mul, Nat.cast_pow,
        Real.mul_rpow (by positivity) (by positivity)]
      have hpow_comm : ((Ideal.absNorm p.asIdeal : ℝ) ^ k) ^ (-s) =
          ((Ideal.absNorm p.asIdeal : ℝ) ^ (-s)) ^ k := by
        rw [← Real.rpow_natCast (Ideal.absNorm p.asIdeal : ℝ) k,
          ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm (k : ℝ),
          Real.rpow_mul (Nat.cast_nonneg _), Real.rpow_natCast]
      rw [hpow_comm]
      dsimp [r]
      rw [mul_pow]
      ring
  -- Step 2: Bijection between (S → ℕ) and {I : (Ideal (𝓞 E))⁰ // smooth I}
  rw [hexp]
  let smooth (I : (Ideal (𝓞 E))⁰) : Prop :=
    ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 E), p.asIdeal ∣ I.1 → p ∈ S
  let toSmooth : (S → ℕ) → {I : (Ideal (𝓞 E))⁰ // smooth I} := fun e =>
    ⟨∏ p : S, (⟨p.1.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr p.1.ne_bot⟩ : (Ideal (𝓞 E))⁰) ^ e p,
      fun q hq => by
        have hcoe : (∏ p : S, (⟨p.1.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr p.1.ne_bot⟩ :
            (Ideal (𝓞 E))⁰) ^ e p).1 = ∏ p : S, p.1.asIdeal ^ e p := by
          simp
        rw [hcoe] at hq
        obtain ⟨p, _, hpq⟩ := (q.prime.dvd_finsetProd_iff _).mp hq
        have hpq' : q.asIdeal ∣ p.1.asIdeal := q.prime.dvd_of_dvd_pow hpq
        have heq : q.asIdeal = p.1.asIdeal :=
          (p.1.isMaximal.eq_of_le q.isPrime.ne_top (Ideal.le_of_dvd hpq')).symm
        rw [IsDedekindDomain.HeightOneSpectrum.ext heq]
        exact p.2⟩
  have hbij : Function.Bijective toSmooth := by
    constructor
    · intro e₁ e₂ h
      ext ⟨q, hqS⟩
      have hval : ∏ a : S, a.1.asIdeal ^ e₁ a = ∏ a : S, a.1.asIdeal ^ e₂ a := by
        have := congrArg (fun x => x.1.1) h
        simpa [toSmooth] using this
      have hcnt := congrArg (fun I => Multiset.count q.asIdeal (UniqueFactorizationMonoid.normalizedFactors I)) hval
      have hcnt_prod : ∀ e : S → ℕ,
          Multiset.count q.asIdeal (UniqueFactorizationMonoid.normalizedFactors (∏ a : S, a.1.asIdeal ^ e a)) =
            e ⟨q, hqS⟩ := by
        intro e
        have hne : ∀ a : S, a.1.asIdeal ^ e a ≠ ⊥ := fun a => pow_ne_zero _ a.1.ne_bot
        rw [normalizedFactors_finset_prod_ideals Finset.univ _ (fun a _ => hne a),
          Multiset.count_sum']
        have hterm : ∀ a : S,
            Multiset.count q.asIdeal (UniqueFactorizationMonoid.normalizedFactors (a.1.asIdeal ^ e a)) =
              if a = ⟨q, hqS⟩ then e a else 0 := by
          intro a
          rw [UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul,
            UniqueFactorizationMonoid.normalizedFactors_irreducible a.1.prime.irreducible,
            normalize_eq, Multiset.count_singleton]
          by_cases haq : a = ⟨q, hqS⟩
          · subst haq; simp
          · have hne_id : q.asIdeal ≠ a.1.asIdeal := fun h =>
              haq (Subtype.ext (IsDedekindDomain.HeightOneSpectrum.ext h.symm))
            simp [haq, hne_id]
        simp_rw [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_pos trivial]
      rw [hcnt_prod e₁, hcnt_prod e₂] at hcnt
      exact hcnt
    · intro ⟨I, hI⟩
      let e : S → ℕ := fun p =>
        Multiset.count p.1.asIdeal (UniqueFactorizationMonoid.normalizedFactors I.1)
      refine ⟨e, Subtype.ext (Subtype.ext ?_)⟩
      have hI_ne : I.1 ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp I.2
      have hcoe : (toSmooth e).1.1 = ∏ p : S, p.1.asIdeal ^ e p := by
        simp [toSmooth]
      rw [hcoe, ← Ideal.prod_normalizedFactors_eq_self hI_ne,
        multiset_prod_eq_toFinset_count_pow]
      calc ∏ p : S, p.1.asIdeal ^ e p
          = ∏ J ∈ S.image (fun p => p.asIdeal),
              J ^ Multiset.count J (UniqueFactorizationMonoid.normalizedFactors I.1) := by
            rw [Finset.prod_image (fun p₁ _ p₂ _ h => IsDedekindDomain.HeightOneSpectrum.ext h),
              ← Finset.prod_coe_sort S]
        _ = ∏ J ∈ (UniqueFactorizationMonoid.normalizedFactors I.1).toFinset,
              J ^ Multiset.count J (UniqueFactorizationMonoid.normalizedFactors I.1) := by
            refine (Finset.prod_subset_one_on_sdiff ?_ ?_ (fun _ _ => rfl)).symm
            · intro J hJ
              rw [Multiset.mem_toFinset] at hJ
              have hJne : J ≠ ⊥ := UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hJ
              have hJp : J.IsPrime := (Ideal.mem_normalizedFactors_iff hI_ne).mp hJ |>.1
              have hJdvd : J ∣ I.1 := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hJ
              let pJ : IsDedekindDomain.HeightOneSpectrum (𝓞 E) := ⟨J, hJp, hJne⟩
              exact Finset.mem_image.mpr ⟨pJ, hI pJ hJdvd, rfl⟩
            · intro J hJ
              rw [Finset.mem_sdiff, Multiset.mem_toFinset] at hJ
              rw [Multiset.count_eq_zero.mpr hJ.2, pow_zero]
  dsimp only
  rw [← Equiv.tsum_eq (Equiv.ofBijective toSmooth hbij)]
  refine tsum_congr fun e => ?_
  have hcoe : ((Equiv.ofBijective toSmooth hbij e).1 : Ideal (𝓞 E)) = ∏ p : S, p.1.asIdeal ^ e p := by
    simp [toSmooth]
  rw [hcoe]
  rfl

/-- Convergence of finite Euler products over an exhausting sequence of finite prime sets
`S_X` (containing all primes of norm `≤ X`) to the full Dirichlet series. -/
lemma tendsto_finite_euler_prod
    (g : (Ideal (𝓞 E))⁰ →* ℝ) (hg : ∀ I, |g I| ≤ 1)
    {s : ℝ} (hs : 1 < s)
    (S : ℕ → Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 E)))
    (hS : ∀ X : ℕ, ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 E),
      Ideal.absNorm p.asIdeal ≤ X → p ∈ S X) :
    Tendsto (fun X : ℕ =>
      ∏ p ∈ S X,
        (1 - g ⟨p.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr p.ne_bot⟩ *
          (Ideal.absNorm p.asIdeal : ℝ) ^ (-s))⁻¹)
      atTop
      (𝓝 (∑' I : (Ideal (𝓞 E))⁰, g I * (Ideal.absNorm I.1 : ℝ) ^ (-s))) := by
  classical
  have hsI := summable_ideal_absNorm_rpow (E := E) hs
  have hsg : Summable (fun I : (Ideal (𝓞 E))⁰ => g I * (Ideal.absNorm I.1 : ℝ) ^ (-s)) := by
    refine Summable.of_norm_bounded hsI fun I => ?_
    have hrpow_nn : 0 ≤ (Ideal.absNorm I.1 : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hrpow_nn]
    exact mul_le_of_le_one_left hrpow_nn (hg I)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨F₀, hF₀⟩ := Metric.tendsto_atTop.mp hsI.hasSum ε hε
  let X₀ : ℕ := F₀.sup fun I => Ideal.absNorm I.1
  refine ⟨X₀, fun X hX => ?_⟩
  rw [finite_euler_prod_eq_tsum_smooth g hg hs (S X)]
  let smooth (I : (Ideal (𝓞 E))⁰) : Prop :=
    ∀ p : IsDedekindDomain.HeightOneSpectrum (𝓞 E), p.asIdeal ∣ I.1 → p ∈ S X
  have htsum_split :
      (∑' I : (Ideal (𝓞 E))⁰, g I * (Ideal.absNorm I.1 : ℝ) ^ (-s)) =
      (∑' I : {I : (Ideal (𝓞 E))⁰ // smooth I}, g I.1 * (Ideal.absNorm I.1.1 : ℝ) ^ (-s)) +
      (∑' I : {I : (Ideal (𝓞 E))⁰ // ¬ smooth I}, g I.1 * (Ideal.absNorm I.1.1 : ℝ) ^ (-s)) :=
    (hsg.tsum_subtype_add_tsum_subtype_compl {I | smooth I}).symm
  rw [Real.dist_eq, htsum_split, sub_add_cancel_left, abs_neg]
  have hF₀_smooth : ∀ I ∈ F₀, smooth I := by
    intro I hI p hp
    apply hS X p
    have hdvd : Ideal.absNorm p.asIdeal ∣ Ideal.absNorm I.1 :=
      Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hp)
    have hle : Ideal.absNorm p.asIdeal ≤ Ideal.absNorm I.1 :=
      Nat.le_of_dvd (Ideal.absNorm_pos_of_nonZeroDivisors I) hdvd
    exact hle.trans ((Finset.le_sup hI).trans hX)
  have hsum_compl :
      |∑' I : {I : (Ideal (𝓞 E))⁰ // ¬ smooth I}, g I.1 * (Ideal.absNorm I.1.1 : ℝ) ^ (-s)| ≤
      ∑' I : {I : (Ideal (𝓞 E))⁰ // ¬ smooth I}, (Ideal.absNorm I.1.1 : ℝ) ^ (-s) := by
    calc |∑' I : {I : (Ideal (𝓞 E))⁰ // ¬ smooth I}, _|
        ≤ ∑' I : {I : (Ideal (𝓞 E))⁰ // ¬ smooth I}, |g I.1 * (Ideal.absNorm I.1.1 : ℝ) ^ (-s)| :=
          norm_tsum_le_tsum_norm (hsg.subtype _).norm
      _ ≤ ∑' I : {I : (Ideal (𝓞 E))⁰ // ¬ smooth I}, (Ideal.absNorm I.1.1 : ℝ) ^ (-s) := by
          refine Summable.tsum_le_tsum (fun I => ?_) (hsg.subtype _).norm (hsI.subtype _)
          have hrpow_nn : 0 ≤ (Ideal.absNorm I.1.1 : ℝ) ^ (-s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
          rw [abs_mul, abs_of_nonneg hrpow_nn]
          exact mul_le_of_le_one_left hrpow_nn (hg I.1)
  have htail_lt :
      ∑' I : {I : (Ideal (𝓞 E))⁰ // ¬ smooth I}, (Ideal.absNorm I.1.1 : ℝ) ^ (-s) < ε := by
    have hsum_F0_le :
        ∑ I ∈ F₀, (Ideal.absNorm I.1 : ℝ) ^ (-s) ≤
        ∑' I : {I : (Ideal (𝓞 E))⁰ // smooth I}, (Ideal.absNorm I.1.1 : ℝ) ^ (-s) := by
      let F₀' : Finset {I : (Ideal (𝓞 E))⁰ // smooth I} := F₀.attach.map
        ⟨fun x => ⟨x.1, hF₀_smooth x.1 x.2⟩, fun _ _ h => Subtype.ext (Subtype.mk.inj h)⟩
      have hsum_eq : ∑ I ∈ F₀, (Ideal.absNorm I.1 : ℝ) ^ (-s) =
          ∑ I ∈ F₀', (Ideal.absNorm I.1.1 : ℝ) ^ (-s) := by
        dsimp [F₀']
        rw [Finset.sum_map]
        exact (Finset.sum_attach F₀ (fun I => (Ideal.absNorm I.1 : ℝ) ^ (-s))).symm
      rw [hsum_eq]
      exact (hsI.subtype _).sum_le_tsum F₀' (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hfull :
        (∑' I : {I : (Ideal (𝓞 E))⁰ // smooth I}, (Ideal.absNorm I.1.1 : ℝ) ^ (-s)) +
        (∑' I : {I : (Ideal (𝓞 E))⁰ // ¬ smooth I}, (Ideal.absNorm I.1.1 : ℝ) ^ (-s)) =
        ∑' I : (Ideal (𝓞 E))⁰, (Ideal.absNorm I.1 : ℝ) ^ (-s) :=
      hsI.tsum_subtype_add_tsum_subtype_compl {I | smooth I}
    have hdistF0 := hF₀ F₀ le_rfl
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr
      (hsI.sum_le_tsum F₀ (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)))] at hdistF0
    linarith
  exact lt_of_le_of_lt hsum_compl htail_lt

end LSeriesAndEuler

/- ## Section 5: Main Theorem -/

theorem main : OMA.R_Erdos90_erdos_90_variants_sawin_explicit_R1_H3_R1.H2 := by
  classical
  intro F K _ _ _ _ _ _ _ _ T hT
  -- Step 1: Construct real characters of Cl(F) / T.range
  have hsq : ∀ g : ClassGroup (𝓞 F), g ^ 2 ∈ T.range :=
    sq_mem_range_of_relNorm_spec T hT
  obtain ⟨d, χ, hcard, hχ0, hpm, hadd, htriv, hneg_notH, hneg_ne0⟩ :=
    exists_real_characters_of_sq_mem T.range hsq
  set m : ℕ := T.range.index
  -- Step 2: Uniform bound on L(s, χ w) for w ≠ 0 on s ∈ (1, 2]
  have hL_bdd : ∀ w : Fin d → ZMod 2, w ≠ 0 → ∃ B : ℝ, 0 ≤ B ∧ ∀ s : ℝ, 1 < s → s ≤ 2 →
      |∑' I : (Ideal (𝓞 F))⁰, χ w (ClassGroup.mk0 I) * (Ideal.absNorm I.1 : ℝ) ^ (-s)| ≤ B :=
    fun w hw => nontrivial_character_LSeries_bdd F (χ w) (hpm w) (hneg_ne0 w hw)
  choose Bw hBw0 hBw using fun w : {w : Fin d → ZMod 2 // w ≠ 0} => hL_bdd w.1 w.2
  let Bprod : ℝ := (∏ w : {w : Fin d → ZMod 2 // w ≠ 0}, Bw w) ^ 2
  -- Step 3: Global zeta inequality ζ_K(s)^m ≤ ζ_F(s)^2 * (∏_{w ≠ 0} L(s, χ w))^2 for s > 1
  have hzeta_ineq : ∀ s : ℝ, 1 < s →
      (NumberField.dedekindZeta K (s : ℂ)).re ^ m ≤
        (NumberField.dedekindZeta F (s : ℂ)).re ^ 2 *
          (∏ w : {w : Fin d → ZMod 2 // w ≠ 0},
            ∑' I : (Ideal (𝓞 F))⁰, χ w.1 (ClassGroup.mk0 I) * (Ideal.absNorm I.1 : ℝ) ^ (-s)) ^ 2 := by
    intro s hs
    -- Finite prime sets P_F(X) = {p | absNorm p ≤ X}
    have hPF_fin : ∀ X : ℕ,
        Set.Finite {p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) | Ideal.absNorm p.asIdeal ≤ X} :=
      fun X => (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) X).preimage
        (by intro _ _ _ _ h; exact IsDedekindDomain.HeightOneSpectrum.ext h)
    let PF : ℕ → Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)) := fun X =>
      (hPF_fin X).toFinset
    have hPF_mem : ∀ X p, p ∈ PF X ↔ Ideal.absNorm p.asIdeal ≤ X := fun X p =>
      Set.Finite.mem_toFinset (hPF_fin X)
    -- Primes of K lying over PF(X)
    let liftOver (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
        Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
      (IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K)).attach.map
        ⟨fun P => ⟨P.1, ((IsDedekindDomain.mem_primesOverFinset_iff (B := 𝓞 K) p.ne_bot).mp P.2).1,
            Ideal.ne_bot_of_mem_primesOver p.ne_bot
              ((IsDedekindDomain.mem_primesOverFinset_iff (B := 𝓞 K) p.ne_bot).mp P.2)⟩,
          fun _ _ h => Subtype.ext (congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h)⟩
    let QK : ℕ → Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
      fun X => (PF X).biUnion liftOver
    have hlift_disj : ∀ p₁ p₂ : IsDedekindDomain.HeightOneSpectrum (𝓞 F), p₁ ≠ p₂ →
        Disjoint (liftOver p₁) (liftOver p₂) := by
      intro p₁ p₂ hne
      rw [Finset.disjoint_left]
      intro P hP₁ hP₂
      simp only [liftOver, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists] at hP₁ hP₂
      obtain ⟨Q₁, hQ₁, hE₁⟩ := hP₁
      obtain ⟨Q₂, hQ₂, hE₂⟩ := hP₂
      have hQeq : Q₁ = Q₂ := by
        have := congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal (hE₁.trans hE₂.symm)
        exact this
      subst hQeq
      have hL₁ : Q₁.LiesOver p₁.asIdeal :=
        ((IsDedekindDomain.mem_primesOverFinset_iff (B := 𝓞 K) p₁.ne_bot).mp hQ₁).2
      have hL₂ : Q₁.LiesOver p₂.asIdeal :=
        ((IsDedekindDomain.mem_primesOverFinset_iff (B := 𝓞 K) p₂.ne_bot).mp hQ₂).2
      have hp_eq : p₁.asIdeal = p₂.asIdeal :=
        ((Ideal.liesOver_iff _ _).mp hL₁).trans ((Ideal.liesOver_iff _ _).mp hL₂).symm
      exact hne (IsDedekindDomain.HeightOneSpectrum.ext hp_eq)
    have hQK_exhaust : ∀ X : ℕ, ∀ P : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
        Ideal.absNorm P.asIdeal ≤ X → P ∈ QK X := by
      intro X P hPX
      have : P.asIdeal.IsPrime := P.isPrime
      let pI : Ideal (𝓞 F) := Ideal.under (𝓞 F) P.asIdeal
      have : pI.IsPrime := Ideal.IsPrime.under (𝓞 F) P.asIdeal
      have hpI_ne : pI ≠ ⊥ := by
        intro hbot
        have : P.asIdeal.LiesOver (⊥ : Ideal (𝓞 F)) := by
          rw [← hbot]; infer_instance
        exact P.ne_bot (Ideal.eq_bot_of_liesOver_bot (𝓞 F) P.asIdeal)
      let p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) := ⟨pI, inferInstance, hpI_ne⟩
      have : P.asIdeal.LiesOver p.asIdeal := by dsimp [p, pI]; infer_instance
      have : p.asIdeal.IsMaximal := p.isMaximal
      have : P.asIdeal.IsMaximal := P.isMaximal
      have hpX : Ideal.absNorm p.asIdeal ≤ X := by
        have hrel : Ideal.relNorm (𝓞 F) P.asIdeal = p.asIdeal ^ P.asIdeal.inertiaDeg (𝓞 F) :=
          Ideal.relNorm_eq_pow_of_isMaximal P.asIdeal p.asIdeal
        have habs : Ideal.absNorm P.asIdeal = (Ideal.absNorm p.asIdeal) ^ P.asIdeal.inertiaDeg (𝓞 F) := by
          rw [← Ideal.absNorm_relNorm (R := 𝓞 F) (S := 𝓞 K) P.asIdeal, hrel, map_pow]
        have hf : 1 ≤ P.asIdeal.inertiaDeg (𝓞 F) := Ideal.inertiaDeg_pos P.asIdeal (𝓞 F)
        have hle : Ideal.absNorm p.asIdeal ≤ (Ideal.absNorm p.asIdeal) ^ P.asIdeal.inertiaDeg (𝓞 F) :=
          Nat.le_self_pow (by omega) _
        omega
      refine Finset.mem_biUnion.mpr ⟨p, (hPF_mem X p).mpr hpX, ?_⟩
      simp only [liftOver, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists]
      exact ⟨P.asIdeal, (IsDedekindDomain.mem_primesOverFinset_iff (B := 𝓞 K) p.ne_bot).mpr
        ⟨P.isPrime, inferInstance⟩, rfl⟩
    -- Finite product inequality for every X
    have hfin_ineq : ∀ X : ℕ,
        (∏ P ∈ QK X, (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s))⁻¹) ^ m ≤
        (∏ w : Fin d → ZMod 2,
          ∏ p ∈ PF X,
            (1 - χ w (ClassGroup.mk0 ⟨p.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr p.ne_bot⟩) *
              (Ideal.absNorm p.asIdeal : ℝ) ^ (-s))⁻¹) ^ 2 := by
      intro X
      rw [Finset.prod_biUnion (fun p₁ _ p₂ _ hne => hlift_disj p₁ p₂ hne),
        ← Finset.prod_pow, Finset.prod_comm, ← Finset.prod_pow]
      refine Finset.prod_le_prod (fun p _ => ?_) (fun p _ => ?_)
      · refine pow_nonneg (Finset.prod_nonneg fun P _ => ?_) _
        have hNP : 1 < Ideal.absNorm P.asIdeal := by
          have hne0 := Ideal.absNorm_eq_zero_iff.not.mpr P.ne_bot
          have hne1 := Ideal.absNorm_eq_one_iff.not.mpr P.isPrime.ne_top
          omega
        have hu1 : (Ideal.absNorm P.asIdeal : ℝ) ^ (-s) < 1 := by
          rw [Real.rpow_neg (Nat.cast_nonneg _)]
          exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by exact_mod_cast hNP) (by linarith))
        exact inv_nonneg.mpr (by linarith)
      · have hprod_lift :
            ∏ P ∈ liftOver p, (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s))⁻¹ =
            ∏ P ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K),
              (1 - (Ideal.absNorm P : ℝ) ^ (-s))⁻¹ := by
          dsimp [liftOver]
          rw [Finset.prod_map]
          exact Finset.prod_attach (IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K))
            (fun P => (1 - (Ideal.absNorm P : ℝ) ^ (-s))⁻¹)
        rw [hprod_lift]
        exact local_euler_factor_ineq T hT χ hcard hpm hadd htriv hneg_notH p hs
    -- Pass to the limit X → ∞
    have htend_K :
        Tendsto (fun X : ℕ => (∏ P ∈ QK X, (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s))⁻¹) ^ m)
          atTop (𝓝 ((NumberField.dedekindZeta K (s : ℂ)).re ^ m)) := by
      rw [dedekindZeta_re_eq_tsum_ideals hs]
      have h1 := tendsto_finite_euler_prod (E := K) (1 : (Ideal (𝓞 K))⁰ →* ℝ)
        (fun _ => by simp) hs QK hQK_exhaust
      simpa using h1.pow m
    have htend_F :
        Tendsto (fun X : ℕ =>
          (∏ w : Fin d → ZMod 2,
            ∏ p ∈ PF X,
              (1 - χ w (ClassGroup.mk0 ⟨p.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr p.ne_bot⟩) *
                (Ideal.absNorm p.asIdeal : ℝ) ^ (-s))⁻¹) ^ 2)
          atTop
          (𝓝 ((∏ w : Fin d → ZMod 2,
            ∑' I : (Ideal (𝓞 F))⁰, χ w (ClassGroup.mk0 I) * (Ideal.absNorm I.1 : ℝ) ^ (-s)) ^ 2)) := by
      refine (tendsto_finsetProd Finset.univ fun w _ => ?_).pow 2
      have h1 := tendsto_finite_euler_prod (E := F)
        ((χ w).comp ClassGroup.mk0)
        (fun I => by rcases hpm w (ClassGroup.mk0 I) with h | h <;> simp [h])
        hs PF (fun X p hp => (hPF_mem X p).mpr hp)
      simpa using h1
    have hlim := le_of_tendsto_of_tendsto htend_K htend_F (Eventually.of_forall hfin_ineq)
    -- Split w = 0 from the product over w
    have hsplit :
        ∏ w : Fin d → ZMod 2,
          ∑' I : (Ideal (𝓞 F))⁰, χ w (ClassGroup.mk0 I) * (Ideal.absNorm I.1 : ℝ) ^ (-s) =
        (NumberField.dedekindZeta F (s : ℂ)).re *
          ∏ w : {w : Fin d → ZMod 2 // w ≠ 0},
            ∑' I : (Ideal (𝓞 F))⁰, χ w.1 (ClassGroup.mk0 I) * (Ideal.absNorm I.1 : ℝ) ^ (-s) := by
      rw [Fintype.prod_eq_mul_prod_subtype_ne _ (0 : Fin d → ZMod 2)]
      congr 1
      rw [dedekindZeta_re_eq_tsum_ideals hs]
      simp [hχ0]
    rw [hsplit, mul_pow] at hlim
    exact hlim
  -- Step 4: Deduce m ≤ 2 from residues at s → 1⁺
  by_contra hm_gt
  have hm3 : 3 ≤ m := by omega
  have hresK : Tendsto (fun s : ℝ => ((s - 1) * (NumberField.dedekindZeta K (s : ℂ)).re) ^ m)
      (𝓝[>] 1) (𝓝 ((dedekindZeta_residue K) ^ m)) := by
    have h1 := (Complex.continuous_re.tendsto _).comp
      (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
    have h2 : Tendsto (fun s : ℝ => (s - 1) * (NumberField.dedekindZeta K (s : ℂ)).re)
        (𝓝[>] 1) (𝓝 (dedekindZeta_residue K)) := by
      refine h1.congr fun s => ?_
      simp [Function.comp_apply, Complex.mul_re]
    exact h2.pow m
  have hresF : Tendsto (fun s : ℝ => ((s - 1) * (NumberField.dedekindZeta F (s : ℂ)).re) ^ 2)
      (𝓝[>] 1) (𝓝 ((dedekindZeta_residue F) ^ 2)) := by
    have h1 := (Complex.continuous_re.tendsto _).comp
      (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT F)
    have h2 : Tendsto (fun s : ℝ => (s - 1) * (NumberField.dedekindZeta F (s : ℂ)).re)
        (𝓝[>] 1) (𝓝 (dedekindZeta_residue F)) := by
      refine h1.congr fun s => ?_
      simp [Function.comp_apply, Complex.mul_re]
    exact h2.pow 2
  have hpow_zero : Tendsto (fun s : ℝ => (s - 1) ^ (m - 2)) (𝓝[>] 1) (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝 (1 - 1)) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).sub tendsto_const_nhds
    simpa [sub_self, zero_pow (by omega : m - 2 ≠ 0)] using h1.pow (m - 2)
  have hrhs_zero : Tendsto (fun s : ℝ =>
      (s - 1) ^ (m - 2) * ((s - 1) * (NumberField.dedekindZeta F (s : ℂ)).re) ^ 2 * Bprod)
      (𝓝[>] 1) (𝓝 0) := by
    have := (hpow_zero.mul hresF).mul_const Bprod
    simpa using this
  have hle_ev : ∀ᶠ s : ℝ in 𝓝[>] 1,
      ((s - 1) * (NumberField.dedekindZeta K (s : ℂ)).re) ^ m ≤
      (s - 1) ^ (m - 2) * ((s - 1) * (NumberField.dedekindZeta F (s : ℂ)).re) ^ 2 * Bprod := by
    have hmem : Set.Ioo (1 : ℝ) 2 ∈ 𝓝[>] (1 : ℝ) :=
      Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [hmem] with s ⟨hs1, hs2⟩
    have hs10 : 0 ≤ s - 1 := by linarith
    have hprod_le :
        (∏ w : {w : Fin d → ZMod 2 // w ≠ 0},
          ∑' I : (Ideal (𝓞 F))⁰, χ w.1 (ClassGroup.mk0 I) * (Ideal.absNorm I.1 : ℝ) ^ (-s)) ^ 2 ≤
        Bprod := by
      rw [← sq_abs]
      dsimp [Bprod]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun w _ => hBw w s hs1 hs2.le)
    have hmul := mul_le_mul_of_nonneg_left (hzeta_ineq s hs1) (pow_nonneg hs10 m)
    have hF_sq_nonneg : 0 ≤ (NumberField.dedekindZeta F (s : ℂ)).re ^ 2 := sq_nonneg _
    have hstep2 :
        (s - 1) ^ m * ((NumberField.dedekindZeta F (s : ℂ)).re ^ 2 *
          (∏ w : {w : Fin d → ZMod 2 // w ≠ 0},
            ∑' I : (Ideal (𝓞 F))⁰, χ w.1 (ClassGroup.mk0 I) * (Ideal.absNorm I.1 : ℝ) ^ (-s)) ^ 2) ≤
        (s - 1) ^ m * ((NumberField.dedekindZeta F (s : ℂ)).re ^ 2 * Bprod) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod_le hF_sq_nonneg) (pow_nonneg hs10 m)
    have hpow_split : (s - 1) ^ m = (s - 1) ^ (m - 2) * (s - 1) ^ 2 := by
      rw [← pow_add]; congr 1; omega
    calc ((s - 1) * (NumberField.dedekindZeta K (s : ℂ)).re) ^ m
        = (s - 1) ^ m * (NumberField.dedekindZeta K (s : ℂ)).re ^ m := mul_pow _ _ _
      _ ≤ (s - 1) ^ m * ((NumberField.dedekindZeta F (s : ℂ)).re ^ 2 * Bprod) := hmul.trans hstep2
      _ = (s - 1) ^ (m - 2) * ((s - 1) * (NumberField.dedekindZeta F (s : ℂ)).re) ^ 2 * Bprod := by
          rw [hpow_split, mul_pow]; ring
  have hle_lim : (dedekindZeta_residue K) ^ m ≤ 0 :=
    le_of_tendsto_of_tendsto hresK hrhs_zero hle_ev
  have hpos_lim : 0 < (dedekindZeta_residue K) ^ m :=
    pow_pos (dedekindZeta_residue_pos K) m
  linarith

end OMA.Proof_Erdos90_erdos_90_variants_sawin_explicit_R1_H3_R1_H2

theorem OMA.solution : OMA.R_Erdos90_erdos_90_variants_sawin_explicit_R1_H3_R1.H2 :=
  OMA.Proof_Erdos90_erdos_90_variants_sawin_explicit_R1_H3_R1_H2.main
