import OMAReductions.R_arxiv_1902_03207_R1
import Mathlib
-- Credit: @my-other-github-account
/- Adapted from OpenAI critical percolation Lean formalization, revision 3344da59991ed94f9ba711217b29c1d760badfa6; Apache-2.0. -/
open Set MeasureTheory ProbabilityTheory
open scoped Classical
namespace CriticalPercolationLeaf
/-- Finite-size criterion for independent labelled bond percolation.
The coordinates may depend on the requested mesh, and the seed radius may not. -/
def FiniteSizeCriterion (V E : Type*) : Prop :=
  ∀ ends : E → Sym2 V,
  let graph := fun ω : Set E => SimpleGraph.fromEdgeSet (ends '' ω)
  let full := graph Set.univ
  let pc := sInf {p : unitInterval | 0 < (setBernoulli (Set.univ : Set E) p)
    {ω | ∃ v : V, {w | (graph ω).Reachable v w}.Infinite}}
  let ball := fun y : V => Nat.rec (motive := fun _ => Set V) ({y} : Set V) (fun _ B => B ∪ ⋃ v ∈ B, full.neighborSet v)
  full.Connected → (∀ v : V, {i : E | v ∈ ends i}.Finite) →
  (∃ S : Set V, S.Finite ∧ ∀ v, ∃ u ∈ S, ∃ f : V ≃ V, ∃ g : E ≃ E,
    (∀ i, ends (g i) = Sym2.map f (ends i)) ∧ f u = v) →
  0 < (pc : ℝ) → (pc : ℝ) < 1 →
  (∀ e η : ℝ, 0 < e → e < 1/10 → 0 < η → η < 1/10 →
    ∃ m : ℕ, ∀ ρ : ℝ, 0 < ρ → ∃ t z : V → ℝ, ∃ p : unitInterval,
    (pc : ℝ)/2 ≤ p ∧ p < pc ∧
    (∀ ⦃u v⦄, full.Adj u v → |t u - t v| ≤ ρ) ∧
    (∀ ⦃u v⦄, full.Adj u v → |z u - z v| ≤ ρ) ∧
    ∀ y s, |s| = 1 → 1-η ≤ (setBernoulli (Set.univ : Set E) p).real
      {ω | ∃ a ∈ ball y m, ∃ b, ∃ w : (graph ω).Walk a b,
        (∀ x ∈ w.support, |t x - t y| ≤ 100 ∧ |z x - z y| ≤ 100) ∧
        |t b - (t y+1)| ≤ e/4 ∧ |z b - (z y+s)| ≤ e/4}) → False
end CriticalPercolationLeaf

-- OAI.Probability.CriticalPercolation.ProductMeasure.Density
section

namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
open Set
namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]
noncomputable def density (w : E → A → ℝ) (ω : E → A) : ℝ := ∏ e, w e (ω e)
noncomputable def expect (w : E → A → ℝ) (f : (E → A) → ℝ) : ℝ := by
  classical
  exact ∑ ω, density w ω * f ω
omit [Fintype A] in
lemma density_nonneg {w : E → A → ℝ} (h : ∀ e a, 0 ≤ w e a) (ω : E → A) :
    0 ≤ density w ω := Finset.prod_nonneg fun e _ => h e (ω e)
lemma sum_density [DecidableEq E] (w : E → A → ℝ) (h : ∀ e, ∑ a, w e a = 1) :
    ∑ ω, density w ω = 1 := by
  classical
  unfold density
  rw [← Fintype.prod_sum]
  simp [h]
lemma expect_const (w : E → A → ℝ) (h : ∀ e, ∑ a, w e a = 1) (c : ℝ) :
    expect w (fun _ => c) = c := by
  classical
  rw [expect, ← Finset.sum_mul, sum_density w h, one_mul]
lemma expect_sub (w : E → A → ℝ) (f g : (E → A) → ℝ) :
    expect w (fun ω => f ω - g ω) = expect w f - expect w g := by
  classical
  simp [expect, mul_sub, Finset.sum_sub_distrib]
lemma expect_mono {w : E → A → ℝ} (hw : ∀ e a, 0 ≤ w e a)
    {f g : (E → A) → ℝ} (hfg : ∀ ω, f ω ≤ g ω) : expect w f ≤ expect w g := by
  classical
  exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (density_nonneg hw ω)
omit [Fintype A] in
lemma density_split (w : E → A → ℝ) (P : E → Prop) [DecidablePred P] (ω : E → A) :
    density w ω =
      density (fun e : {e // P e} => w e) (fun e => ω e) *
      density (fun e : {e // ¬ P e} => w e) (fun e => ω e) := by
  exact (Fintype.prod_subtype_mul_prod_subtype P (fun e => w e (ω e))).symm
lemma expect_split (w : E → A → ℝ) (P : E → Prop) [DecidablePred P]
    (f : (E → A) → ℝ) :
    expect w f =
      expect (fun e : {e // P e} => w e) (fun a =>
        expect (fun e : {e // ¬ P e} => w e) (fun b =>
          f ((Equiv.piEquivPiSubtypeProd P (fun _ => A)).symm (a, b)))) := by
  classical
  let e := Equiv.piEquivPiSubtypeProd P (fun _ => A)
  unfold expect
  rw [← e.symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr (by ext; simp)
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr (by ext; simp)
  intro b _
  have h₁ : (fun i : {e // P e} => e.symm (a, b) i) = a :=
    congrArg Prod.fst (e.apply_symm_apply (a, b))
  have h₂ : (fun i : {e // ¬ P e} => e.symm (a, b) i) = b :=
    congrArg Prod.snd (e.apply_symm_apply (a, b))
  rw [density_split w P, h₁, h₂, mul_assoc]
lemma expect_factor (w : E → A → ℝ) (P : E → Prop) [DecidablePred P]
    (f : ({e // P e} → A) → ℝ) (g : ({e // ¬ P e} → A) → ℝ) :
    expect w (fun ω => f (fun e => ω e) * g (fun e => ω e)) =
      expect (fun e : {e // P e} => w e) f *
        expect (fun e : {e // ¬ P e} => w e) g := by
  classical
  rw [expect_split w P]
  have h₁ : ∀ (a : {e // P e} → A) (b : {e // ¬ P e} → A),
      (fun i : {e // P e} =>
        (Equiv.piEquivPiSubtypeProd P (fun _ => A)).symm (a, b) i) = a := by
    intro a b
    exact congrArg Prod.fst ((Equiv.piEquivPiSubtypeProd P (fun _ => A)).apply_symm_apply (a, b))
  have h₂ : ∀ (a : {e // P e} → A) (b : {e // ¬ P e} → A),
      (fun i : {e // ¬ P e} =>
        (Equiv.piEquivPiSubtypeProd P (fun _ => A)).symm (a, b) i) = b := by
    intro a b
    exact congrArg Prod.snd ((Equiv.piEquivPiSubtypeProd P (fun _ => A)).apply_symm_apply (a, b))
  simp_rw [h₁, h₂]
  unfold expect
  rw [Finset.sum_mul]
  apply Finset.sum_congr (by ext; simp)
  intro a _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr (by ext; simp)
  intro b _
  ring
lemma expect_indep (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (S : Set E) {f g : (E → A) → ℝ}
    (hf : DependsOn f S) (hg : DependsOn g Sᶜ) :
    expect w (fun ω => f ω * g ω) = expect w f * expect w g := by
  classical
  obtain ⟨f', rfl⟩ := dependsOn_iff_exists_comp.mp hf
  obtain ⟨g', rfl⟩ := dependsOn_iff_exists_comp.mp hg
  have hw₁ : ∀ e : S, ∑ a, w e a = 1 := fun e => hw e
  have hw₂ : ∀ e : {e // e ∉ S}, ∑ a, w e a = 1 := fun e => hw e
  have hf' : expect w (fun ω => f' (fun e => ω e)) =
      expect (fun e : S => w e) f' := by
    have h := expect_factor w (fun e => e ∈ S) f' (fun _ => 1)
    simpa only [mul_one, expect_const _ hw₂] using h
  have hg' : expect w (fun ω => g' (fun e => ω e)) =
      expect (fun e : {e // e ∉ S} => w e) g' := by
    have h := expect_factor w (fun e => e ∈ S) (fun _ => 1) g'
    simp only [one_mul, expect_const _ hw₁] at h
    convert h using 1
    rfl
  change expect w (fun ω => f' (fun e => ω e) * g' (fun e => ω e)) =
    expect w (fun ω => f' (fun e => ω e)) * expect w (fun ω => g' (fun e => ω e))
  rw [hf', hg']
  convert expect_factor w (fun e => e ∈ S) f' g' using 1
  rfl
lemma expect_mul_const (w : E → A → ℝ) (f : (E → A) → ℝ) (c : ℝ) :
    expect w (fun ω => f ω * c) = expect w f * c := by
  classical
  unfold expect
  rw [Finset.sum_mul]
  apply Finset.sum_congr (by ext; simp)
  intro ω _
  ring
lemma expect_partition {B : Type*} [Fintype B] [DecidableEq B] (w : E → A → ℝ)
    (r : (E → A) → B) (f : B → (E → A) → ℝ) :
    expect w (fun ω => f (r ω) ω) =
      ∑ b, expect w (fun ω => if r ω = b then f b ω else 0) := by
  classical
  simp only [expect]
  rw [Finset.sum_comm]
  apply Finset.sum_congr (by ext; simp)
  intro ω _
  rw [← Finset.mul_sum]
  simp
lemma expect_exposure {B : Type*} [Fintype B] (w : E → A → ℝ)
    (hw : ∀ e, ∑ a, w e a = 1) (r : (E → A) → B) (D : B → Set E)
    (hr : ∀ b, DependsOn (fun ω => r ω = b) (D b))
    (f : B → (E → A) → ℝ) (hf : ∀ b, DependsOn (f b) (D b)ᶜ) :
    expect w (fun ω => f (r ω) ω) =
      expect w (fun ω => expect w (f (r ω))) := by
  classical
  rw [expect_partition w r f,
    expect_partition w r (fun b _ => expect w (f b))]
  apply Finset.sum_congr (by ext; simp)
  intro b _
  have hi : DependsOn (fun ω => if r ω = b then (1 : ℝ) else 0) (D b) := by
    intro ω ω' hω
    change (if r ω = b then (1 : ℝ) else 0) = (if r ω' = b then 1 else 0)
    have hh : (r ω = b) = (r ω' = b) := hr b hω
    rw [hh]
  have hleft : (fun ω => if r ω = b then f b ω else 0) =
      (fun ω => (if r ω = b then (1 : ℝ) else 0) * f b ω) := by
    funext ω
    split_ifs <;> simp
  have hright : (fun ω => if r ω = b then expect w (f b) else 0) =
      (fun ω => (if r ω = b then (1 : ℝ) else 0) * expect w (f b)) := by
    funext ω
    split_ifs <;> simp
  rw [hleft, hright, expect_indep w hw (D b) hi (hf b), expect_mul_const]
end CriticalPercolation.FiniteProduct
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.ProductMeasure.Distribution
section

namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]
lemma expect_zero (w : E → A → ℝ) : expect w (fun _ => 0) = 0 := by
  simp [expect]
lemma expect_sum {J : Type*} [Fintype J] (w : E → A → ℝ)
    (f : J → (E → A) → ℝ) :
    expect w (fun ω => ∑ j, f j ω) = ∑ j, expect w (f j) := by
  classical
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm
lemma expect_nonneg {w : E → A → ℝ} (hw : ∀ e a, 0 ≤ w e a)
    {f : (E → A) → ℝ} (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ expect w f := by
  rw [← expect_zero w]
  exact expect_mono hw hf
end CriticalPercolation.FiniteProduct
namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]
lemma expect_const_mul (w : E → A → ℝ) (c : ℝ) (f : (E → A) → ℝ) :
    expect w (fun ω => c * f ω) = c * expect w f := by
  simp only [mul_comm c]
  exact expect_mul_const w f c
end CriticalPercolation.FiniteProduct
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.ProductMeasure.BitMeasure
section

namespace OAI
section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation
namespace BernoulliProduct
noncomputable def bitMeasure (p : unitInterval) : Measure Prop :=
  unitInterval.toNNReal p • Measure.dirac True +
    unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac False
instance bitMeasure_probability (p : unitInterval) : IsProbabilityMeasure (bitMeasure p) := by
  constructor
  simp [bitMeasure]
noncomputable def bitWeight (p : unitInterval) (b : Prop) : ℝ :=
  if b then p else 1-p
lemma bitWeight_sum (p : unitInterval) : ∑ b, bitWeight p b = 1 := by
  simp [bitWeight]
lemma bitWeight_nonneg (p : unitInterval) (b : Prop) : 0 ≤ bitWeight p b := by
  unfold bitWeight
  split_ifs
  · exact p.property.1
  · exact sub_nonneg.mpr p.property.2
lemma bitMeasure_real_singleton (p : unitInterval) (b : Prop) :
    (bitMeasure p).real {b} = bitWeight p b := by
  by_cases hb : b
  · have he : b = True := propext (iff_true_intro hb)
    subst b
    simp [bitMeasure, bitWeight, measureReal_def]
  · have he : b = False := propext (iff_false_intro hb)
    subst b
    simp [bitMeasure, bitWeight, measureReal_def]
variable {E : Type*}
noncomputable def law (q : E → unitInterval) : Measure (Set E) :=
  Measure.map MeasurableEquiv.setOfPred (Measure.infinitePi fun e => bitMeasure (q e))
instance law_probability (q : E → unitInterval) : IsProbabilityMeasure (law q) := by
  unfold law
  exact Measure.isProbabilityMeasure_map MeasurableEquiv.setOfPred.measurable.aemeasurable
lemma law_const (p : unitInterval) :
    law (fun _ : E => p) = setBernoulli Set.univ p := by
  rw [law, setBernoulli_eq_map]
  rfl
lemma integral_bits_eq_expect [Fintype E] (q : E → unitInterval) (f : (E → Prop) → ℝ) :
    (∫ ω, f ω ∂(Measure.infinitePi fun e => bitMeasure (q e))) =
      FiniteProduct.expect (fun e => bitWeight (q e)) f := by
  rw [Measure.infinitePi_eq_pi, integral_fintype Integrable.of_finite]
  unfold FiniteProduct.expect FiniteProduct.density
  apply Finset.sum_congr rfl
  intro ω _
  rw [smul_eq_mul]
  congr 1
  simp only [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl (fun e _ => bitMeasure_real_singleton (q e) (ω e))
lemma integral_law_eq_expect [Fintype E] (q : E → unitInterval) (f : Set E → ℝ) :
    (∫ ω, f ω ∂law q) =
      FiniteProduct.expect (fun e => bitWeight (q e)) (fun ω => f {e | ω e}) := by
  rw [law, integral_map MeasurableEquiv.setOfPred.measurable.aemeasurable
    Integrable.of_finite.aestronglyMeasurable, integral_bits_eq_expect]
  rfl
lemma law_map_restrict (q : E → unitInterval) (s : Set E) :
    (law q).map (fun ω : Set E => Subtype.val ⁻¹' ω : Set E → Set s) =
      law (fun e : s => q e) := by
  have hmeas : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
    measurable_set_iff.mpr (fun bond => measurable_set_mem bond.val)
  unfold law
  rw [Measure.map_map hmeas MeasurableEquiv.setOfPred.measurable]
  have hcomp : (fun ω : Set E => Subtype.val ⁻¹' ω : Set E → Set s) ∘
      MeasurableEquiv.setOfPred =
      MeasurableEquiv.setOfPred ∘ s.domRestrict := rfl
  rw [hcomp, ← Measure.map_map MeasurableEquiv.setOfPred.measurable (by fun_prop),
    Measure.infinitePi_map_restrict']
end BernoulliProduct
end CriticalPercolation
open Set
open scoped Classical
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.ProductMeasure.TailProduct
section

namespace OAI
section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical
namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}
lemma law_eq_infinitePi (q : E → unitInterval) :
    law q = Measure.infinitePi (fun e => bitMeasure (q e)) := by
  change Measure.map id _ = _
  exact Measure.map_id
abbrev coordinateSigma (e : E) : MeasurableSpace (Set E) :=
  MeasurableSpace.comap (fun ω : Set E => e ∈ ω) inferInstance
abbrev blockSigma (S : Set E) : MeasurableSpace (Set E) := ⨆ e ∈ S, coordinateSigma e
lemma coordinateSigma_le (e : E) : coordinateSigma e ≤ (Set.instMeasurableSpace : MeasurableSpace (Set E)) :=
  (measurable_set_mem e).comap_le
lemma blockSigma_le (S : Set E) : blockSigma S ≤ (Set.instMeasurableSpace : MeasurableSpace (Set E)) :=
  iSup₂_le fun e _ => coordinateSigma_le e
lemma independent_coordinates (q : E → unitInterval) :
    iIndep coordinateSigma (law q) := by
  rw [law_eq_infinitePi]
  exact iIndepFun_infinitePi (X := fun _ (b : Prop) => b) (fun _ => measurable_id)
lemma independent_blocks (q : E → unitInterval) (S : Set E) :
    Indep (blockSigma S) (blockSigma Sᶜ) (law q) :=
  indep_biSup_compl coordinateSigma_le (independent_coordinates q) S
def forceOn (S : Set E) (σ ω : Set E) : Set E := fun e => if e ∈ S then e ∈ σ else e ∈ ω
lemma measurable_forceOn_block (S σ : Set E) :
    @Measurable (Set E) (Set E) (blockSigma Sᶜ) inferInstance (forceOn S σ) := by
  refine (@measurable_pi_iff (Set E) E (fun _ => Prop) (blockSigma Sᶜ)
    (fun _ => inferInstance) _).mpr ?_
  intro e
  by_cases he : e ∈ S
  · simpa only [forceOn, if_pos he] using
      (@measurable_const Prop (Set E) inferInstance (blockSigma Sᶜ) (e ∈ σ))
  · have hm : @Measurable (Set E) Prop (coordinateSigma e) inferInstance
        (fun ω => e ∈ ω) := measurable_iff_comap_le.mpr le_rfl
    have hl : coordinateSigma e ≤ blockSigma Sᶜ := le_iSup_of_le e (le_iSup_of_le he le_rfl)
    simpa only [forceOn, if_neg he] using hm.mono hl le_rfl
lemma measurable_forceOn (S σ : Set E) : Measurable (forceOn S σ) :=
  (measurable_forceOn_block S σ).mono (blockSigma_le Sᶜ) le_rfl
end CriticalPercolation.BernoulliProduct
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.ProductMeasure.ProductConditioning
section

namespace OAI
section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}
@[simp] lemma mem_forceOn (S σ ω : Set E) (e : E) :
    e∈forceOn S σ ω ↔ if e∈S then e∈σ else e∈ω := Iff.rfl
lemma measurable_forceOn_joint (S : Set E) :
    Measurable (fun z : Set E × Set E => forceOn S z.1 z.2) := by
  refine (@measurable_pi_iff (Set E × Set E) E (fun _ => Prop)
    inferInstance (fun _ => inferInstance) _).mpr ?_
  intro e
  by_cases he : e∈S
  · simpa only [forceOn,if_pos he,Function.comp_def] using (measurable_set_mem e).comp measurable_fst
  · simpa only [forceOn,if_neg he,Function.comp_def] using (measurable_set_mem e).comp measurable_snd
lemma measurable_forceOn_joint_block (S : Set E) :
    @Measurable (Set E × Set E) (Set E)
      ((blockSigma S).prod inferInstance) inferInstance
      (fun z => forceOn S z.1 z.2) := by
  refine (@measurable_pi_iff (Set E × Set E) E (fun _ => Prop)
    ((blockSigma S).prod inferInstance) (fun _ => inferInstance) _).mpr ?_
  intro e
  by_cases he : e∈S
  · have hm : @Measurable (Set E) Prop (blockSigma S) inferInstance
        (fun σ => e∈σ) := by
      apply measurable_iff_comap_le.mpr
      exact le_iSup_of_le e (le_iSup_of_le he le_rfl)
    simpa only [forceOn,if_pos he,Function.comp_def] using hm.comp measurable_fst
  · simpa only [forceOn,if_neg he,Function.comp_def] using (measurable_set_mem e).comp measurable_snd
lemma forceOn_resample_law (q : E → unitInterval) (S : Set E) :
    ((law q).prod (law q)).map (fun z : Set E × Set E => forceOn S z.1 z.2)=law q := by
  let f : Set E → Set E := forceOn Sᶜ ∅
  let g : Set E → Set E := forceOn S ∅
  have hf : Measurable f := measurable_forceOn _ _
  have hg : Measurable g := measurable_forceOn _ _
  have hfb : @Measurable (Set E) (Set E) (blockSigma S) inferInstance f := by
    have hh := measurable_forceOn_block Sᶜ (∅ : Set E)
    rw [compl_compl] at hh
    exact hh
  have hgb : @Measurable (Set E) (Set E) (blockSigma Sᶜ) inferInstance g :=
    measurable_forceOn_block S ∅
  have hi : IndepFun f g (law q) :=
    indep_of_indep_of_le (independent_blocks q S) hfb.comap_le hgb.comap_le
  have hm := hi.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable
  have hp := congrArg (Measure.map (fun z : Set E × Set E => forceOn S z.1 z.2)) hm
  rw [Measure.map_prod_map _ _ hf hg,Measure.map_map (measurable_forceOn_joint S)
    (hf.prodMk hg),Measure.map_map (measurable_forceOn_joint S) (hf.prodMap hg)] at hp
  have he1 : (fun z : Set E × Set E => forceOn S z.1 z.2) ∘ (fun ω => (f ω,g ω))=id := by
    funext ω
    ext e
    by_cases he : e∈S <;> simp [f,g,he]
  have he2 : (fun z : Set E × Set E => forceOn S z.1 z.2) ∘ Prod.map f g=
      (fun z : Set E × Set E => forceOn S z.1 z.2) := by
    funext z
    ext e
    by_cases he : e∈S <;> simp [f,g,he]
  rw [he1,he2,Measure.map_id] at hp
  exact hp.symm
def pinnedParameters (q : E → unitInterval) (S σ : Set E) : E → unitInterval :=
  fun e => if e∈S then if e∈σ then 1 else 0 else q e
lemma forceOn_map_law (q : E → unitInterval) (S σ : Set E) :
    (law q).map (forceOn S σ)=law (pinnedParameters q S σ) := by
  simp only [law_eq_infinitePi]
  have hm (e : E) : Measurable (fun b : Prop => if e∈S then e∈σ else b) := .of_discrete
  have h := Measure.infinitePi_map_pi (fun e => bitMeasure (q e)) hm
  change (Measure.infinitePi (fun e => bitMeasure (q e))).map
    (fun (ω : E → Prop) e => if e∈S then e∈σ else ω e)=
    Measure.infinitePi (fun e => bitMeasure (pinnedParameters q S σ e))
  rw [h]
  congr 1
  funext e
  by_cases he : e∈S
  · simp only [if_pos he,Measure.map_const,measure_univ,one_smul]
    by_cases hs : e∈σ <;> simp [pinnedParameters,he,hs,bitMeasure]
  · simp [pinnedParameters,he]
def blockProbability (q : E → unitInterval) (S : Set E) (A : Set (Set E))
    (σ : Set E) : ℝ≥0∞ := law q ((forceOn S σ) ⁻¹' A)
lemma blockProbability_eq_lintegral (q : E → unitInterval) (S : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) (σ : Set E) :
    blockProbability q S A σ=∫⁻ ω, A.indicator (1 : Set E → ℝ≥0∞) (forceOn S σ ω) ∂law q := by
  unfold blockProbability
  rw [← lintegral_indicator_one (hA.preimage (measurable_forceOn S σ))]
  rfl
lemma blockProbability_le_one (q : E → unitInterval) (S : Set E)
    (A : Set (Set E)) (σ : Set E) : blockProbability q S A σ≤1 := prob_le_one
lemma measurable_blockProbability (q : E → unitInterval) (S : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) :
    @Measurable (Set E) ℝ≥0∞ (blockSigma S) inferInstance (blockProbability q S A) := by
  have hI : @Measurable (Set E × Set E) ℝ≥0∞
      ((blockSigma S).prod Set.instMeasurableSpace) inferInstance
      (fun z => A.indicator (1 : Set E → ℝ≥0∞) (forceOn S z.1 z.2)) :=
    @Measurable.comp (Set E × Set E) (Set E) ℝ≥0∞
      ((blockSigma S).prod Set.instMeasurableSpace) Set.instMeasurableSpace inferInstance
      _ _ (measurable_const.indicator hA) (measurable_forceOn_joint_block S)
  have hm := @Measurable.lintegral_prod_right' (Set E) (Set E)
    (blockSigma S) Set.instMeasurableSpace (law q) inferInstance _ hI
  convert hm using 1
  funext σ
  exact blockProbability_eq_lintegral q S A hA σ
lemma blockProbability_monotone (q : E → unitInterval) (S : Set E)
    (A : Set (Set E)) (hA : IsUpperSet A) : Monotone (blockProbability q S A) := by
  intro σ τ hστ
  apply measure_mono
  intro ω hω
  apply hA _ hω
  intro e he
  by_cases hs : e∈S
  · have hh : e∈σ := by simpa only [mem_forceOn,if_pos hs] using he
    simpa only [mem_forceOn,if_pos hs] using hστ hh
  · simpa only [mem_forceOn,if_neg hs] using he
lemma lintegral_blockProbability (q : E → unitInterval) (S : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) :
    (∫⁻ σ, blockProbability q S A σ ∂law q)=law q A := by
  simp_rw [blockProbability_eq_lintegral q S A hA]
  have hm : Measurable (fun z : Set E × Set E =>
      A.indicator (1 : Set E → ℝ≥0∞) (forceOn S z.1 z.2)) :=
    (measurable_const.indicator hA).comp (measurable_forceOn_joint S)
  rw [← lintegral_prod _ hm.aemeasurable]
  have hi : Measurable (A.indicator (1 : Set E → ℝ≥0∞)) := measurable_const.indicator hA
  rw [← lintegral_map hi (measurable_forceOn_joint S),
    forceOn_resample_law,lintegral_indicator_one hA]
lemma blockSigma_eq_comap (S : Set E) :
    blockSigma S=MeasurableSpace.comap (fun σ : Set E => (Subtype.val ⁻¹' σ : Set S))
      Set.instMeasurableSpace := by
  change (⨆ e∈S, MeasurableSpace.comap (fun σ : Set E => e∈σ) inferInstance)=
    MeasurableSpace.comap (fun σ : Set E => (Subtype.val ⁻¹' σ : Set S))
      (⨆ e : S, MeasurableSpace.comap (fun σ : Set S => e∈σ) inferInstance)
  rw [MeasurableSpace.comap_iSup,iSup_subtype']
  congr 1
  funext e
  rw [MeasurableSpace.comap_comp]
  rfl
lemma block_event_forceOn (S : Set E) (B : Set (Set E))
    (hB : MeasurableSet[blockSigma S] B) (σ ω : Set E) :
    forceOn S σ ω∈B ↔ σ∈B := by
  rw [blockSigma_eq_comap] at hB
  obtain ⟨C,hC,rfl⟩ := hB
  have he : (Subtype.val ⁻¹' forceOn S σ ω : Set S)=Subtype.val ⁻¹' σ := by
    ext e
    simp only [mem_preimage,mem_forceOn,if_pos e.property]
  change (Subtype.val ⁻¹' forceOn S σ ω)∈C ↔ (Subtype.val ⁻¹' σ)∈C
  rw [he]
lemma blockProbability_inter_block (q : E → unitInterval) (S : Set E)
    (A B : Set (Set E)) (hB : MeasurableSet[blockSigma S] B) (σ : Set E) :
    blockProbability q S (A∩B) σ=B.indicator (blockProbability q S A) σ := by
  unfold blockProbability
  by_cases hσ : σ∈B
  · rw [Set.indicator_of_mem hσ]
    congr 1
    ext ω
    simp only [Set.mem_preimage,Set.mem_inter_iff,block_event_forceOn S B hB,hσ,and_true]
  · rw [Set.indicator_of_notMem hσ]
    have he : forceOn S σ ⁻¹' (A∩B)=∅ := by
      ext ω
      simp only [Set.mem_preimage,Set.mem_inter_iff,block_event_forceOn S B hB,hσ,
        and_false,Set.mem_empty_iff_false]
    rw [he,measure_empty]
lemma setLIntegral_blockProbability (q : E → unitInterval) (S : Set E)
    (A B : Set (Set E)) (hA : MeasurableSet A) (hB : MeasurableSet[blockSigma S] B) :
    (∫⁻ σ in B, blockProbability q S A σ ∂law q)=law q (A∩B) := by
  have hmB := (blockSigma_le S) _ hB
  rw [← lintegral_indicator hmB]
  simp_rw [← blockProbability_inter_block q S A B hB]
  exact lintegral_blockProbability q S (A∩B) (hA.inter hmB)
lemma forceOn_absorb (S T σ τ : Set E) (hST : S⊆T) :
    forceOn T τ ∘ forceOn S σ=forceOn T τ := by
  funext ω
  ext e
  change (e∈forceOn T τ (forceOn S σ ω)) ↔ e∈forceOn T τ ω
  by_cases heT : e∈T
  · simp only [mem_forceOn,if_pos heT]
  · have heS : e∉S := fun he => heT (hST he)
    simp only [mem_forceOn,if_neg heT,if_neg heS]
lemma blockProbability_pin_smaller (q : E → unitInterval) (S T σ : Set E)
    (hST : S⊆T) (A : Set (Set E)) (hA : MeasurableSet A) (τ : Set E) :
    blockProbability (pinnedParameters q S σ) T A τ=blockProbability q T A τ := by
  unfold blockProbability
  rw [← forceOn_map_law q S σ,Measure.map_apply (measurable_forceOn S σ)
    (hA.preimage (measurable_forceOn T τ)),← Set.preimage_comp,forceOn_absorb S T σ τ hST]
end CriticalPercolation.BernoulliProduct
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.FreshTrial
section

namespace OAI
section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}
def allOpen (F : Set E) : Set (Set E) := {ω | F⊆ω}
lemma measurable_allOpen_block [Countable E] (F : Set E) :
    MeasurableSet[blockSigma F] (allOpen F) := by
  have he : allOpen F=⋂ e : F, {ω : Set E | (e:E)∈ω} := by
    ext ω
    simp only [allOpen,Set.mem_ofPred_eq,Set.mem_iInter]
    exact ⟨fun h e => h e.property,fun h e he => h ⟨e,he⟩⟩
  rw [he]
  apply MeasurableSet.iInter
  intro e
  have hm : MeasurableSet[coordinateSigma (e:E)] {ω : Set E | (e:E)∈ω} :=
    ⟨{True},MeasurableSet.singleton _,by ext ω; simp⟩
  exact (le_iSup_of_le (e:E) (le_iSup_of_le e.property le_rfl) :
    coordinateSigma (e:E)≤blockSigma F) _ hm
lemma allOpen_inter_lower_le [Countable E] (q : E → unitInterval) (F : Set E)
    (B : Set (Set E)) (hB : MeasurableSet B) (hBl : IsLowerSet B) :
    (law q).real (allOpen F∩B)≤(law q).real (allOpen F)*(law q).real B := by
  let C := forceOn F Set.univ ⁻¹' B
  have hmC : MeasurableSet[blockSigma Fᶜ] C := hB.preimage (measurable_forceOn_block F _)
  have hi := ((independent_blocks q F).indepSet_of_measurableSet
    (measurable_allOpen_block F) hmC).measure_inter_eq_mul
  have he : allOpen F∩B=allOpen F∩C := by
    ext ω
    by_cases hω : F⊆ω
    · have hf : forceOn F Set.univ ω=ω := by
        ext e
        by_cases he : e∈F
        · simp only [mem_forceOn,if_pos he,Set.mem_univ,true_iff]
          exact hω he
        · simp only [mem_forceOn,if_neg he]
      simp only [Set.mem_inter_iff,allOpen,Set.mem_ofPred_eq,hω,true_and,C,Set.mem_preimage,hf]
    · simp only [Set.mem_inter_iff,allOpen,Set.mem_ofPred_eq,hω,false_and]
  have hsub : C⊆B := by
    intro ω hω
    apply hBl _ hω
    intro e he
    by_cases heF : e∈F <;> simp [heF,he]
  have hr : (law q).real (allOpen F∩B)=(law q).real (allOpen F)*(law q).real C := by
    simp only [measureReal_def,he,hi,ENNReal.toReal_mul]
  rw [hr]
  exact mul_le_mul_of_nonneg_left (measureReal_mono hsub) measureReal_nonneg
lemma integrable_blockProbability_real (q : E → unitInterval) (S : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) :
    Integrable (fun σ => (blockProbability q S A σ).toReal) (law q) := by
  have hm := (measurable_blockProbability q S A hA).mono (blockSigma_le S) le_rfl
  apply (integrable_const (1:ℝ)).mono' hm.ennreal_toReal.aestronglyMeasurable
  filter_upwards [] with σ
  rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono (by simp) (blockProbability_le_one q S A σ)
lemma integral_blockProbability_real (q : E → unitInterval) (S : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) :
    (∫ σ, (blockProbability q S A σ).toReal ∂law q)=(law q).real A := by
  have hm := (measurable_blockProbability q S A hA).mono (blockSigma_le S) le_rfl
  rw [integral_toReal hm.aemeasurable (ae_of_all _ (fun σ =>
    (blockProbability_le_one q S A σ).trans_lt ENNReal.one_lt_top)),
    lintegral_blockProbability q S A hA]
  rfl
theorem good_trial_bound [Countable E] (q : E → unitInterval) (S F : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) (hAu : IsUpperSet A)
    (η lam : ℝ) (hlam : 0<lam) (hmean : 1-η≤(law q).real A) :
    (law q).real (allOpen F∩{σ | (blockProbability q S A σ).toReal<1-lam})≤
      (law q).real (allOpen F)*η/lam := by
  let g : Set E → ℝ := fun σ => (blockProbability q S A σ).toReal
  let B : Set (Set E) := {σ | g σ<1-lam}
  have hg : Measurable g :=
    ((measurable_blockProbability q S A hA).mono (blockSigma_le S) le_rfl).ennreal_toReal
  have hgi : Integrable g (law q) := integrable_blockProbability_real q S A hA
  have hg1 : ∀ σ, g σ≤1 := fun σ =>
    ENNReal.toReal_mono (by simp) (blockProbability_le_one q S A σ)
  have hgm : Monotone g := by
    intro σ τ h
    exact ENNReal.toReal_mono (ne_of_lt ((blockProbability_le_one q S A τ).trans_lt
      ENNReal.one_lt_top)) (blockProbability_monotone q S A hAu h)
  have hBm : MeasurableSet B := measurableSet_lt hg measurable_const
  have hBl : IsLowerSet B := fun _ _ h hB => (hgm h).trans_lt hB
  have hmark : lam*(law q).real B≤η := by
    have hcomp : Integrable (fun σ => lam*B.indicator (1 : Set E → ℝ) σ) (law q) :=
      ((integrable_const (1:ℝ)).indicator hBm).const_mul lam
    have hd : Integrable (fun σ => 1-g σ) (law q) := (integrable_const 1).sub hgi
    have hi := integral_mono hcomp hd (fun σ => by
      by_cases hσ : σ∈B
      · rw [Set.indicator_of_mem hσ]
        have hh : g σ<1-lam := hσ
        dsimp only [Pi.one_apply]
        linarith
      · rw [Set.indicator_of_notMem hσ,mul_zero]
        exact sub_nonneg.mpr (hg1 σ))
    rw [integral_const_mul,integral_indicator_one hBm,integral_sub (integrable_const 1) hgi,
      integral_const,probReal_univ,smul_eq_mul,one_mul] at hi
    have he := integral_blockProbability_real q S A hA
    change (∫ σ, g σ ∂law q)=(law q).real A at he
    rw [he] at hi
    linarith
  have hh := allOpen_inter_lower_le q F B hBm hBl
  have hb : (law q).real B≤η/lam := (le_div_iff₀ hlam).mpr (by nlinarith [hmark])
  exact hh.trans (by simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left hb (show 0≤(law q).real (allOpen F) from measureReal_nonneg))
end CriticalPercolation.BernoulliProduct
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.PredictionFailure
section

namespace OAI
section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}
lemma prediction_persists (q : E → unitInterval) (S T U σ τ : Set E)
    (A : Set (Set E)) (hA : MeasurableSet[blockSigma U] A)
    (hST : S∩U=T∩U) (hstates : ∀ e∈S∩U, (e∈σ ↔ e∈τ)) :
    blockProbability q S A σ=blockProbability q T A τ := by
  unfold blockProbability
  congr 1
  ext ω
  have hrestrict : U∩forceOn S σ ω=U∩forceOn T τ ω := by
    ext e
    by_cases he : e∈U
    · have heST : e∈S ↔ e∈T := by
        have hh := Set.ext_iff.mp hST e
        simpa only [Set.mem_inter_iff,he,and_true] using hh
      by_cases heS : e∈S
      · have heT := heST.mp heS
        simp only [Set.mem_inter_iff,he,true_and,mem_forceOn,if_pos heS,if_pos heT]
        exact hstates e ⟨heS,he⟩
      · have heT : e∉T := fun h => heS (heST.mpr h)
        simp only [Set.mem_inter_iff,he,true_and,mem_forceOn,if_neg heS,if_neg heT]
    · simp only [Set.mem_inter_iff,he,false_and]
  have hforce : forceOn U (forceOn S σ ω) (forceOn T τ ω)=forceOn T τ ω := by
    ext e
    by_cases he : e∈U
    · have hh := Set.ext_iff.mp hrestrict e
      simpa only [Set.mem_inter_iff,he,true_and,mem_forceOn,ite_true,if_pos he] using hh
    · simp only [mem_forceOn,if_neg he]
  have hh := block_event_forceOn U A hA (forceOn S σ ω) (forceOn T τ ω)
  rw [hforce] at hh
  exact hh.symm
lemma blockProbability_real_compl (q : E → unitInterval) (S σ : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) :
    (blockProbability q S Aᶜ σ).toReal=1-(blockProbability q S A σ).toReal := by
  change (law q).real ((forceOn S σ ⁻¹' A)ᶜ)=1-(law q).real (forceOn S σ ⁻¹' A)
  exact probReal_compl_eq_one_sub (hA.preimage (measurable_forceOn S σ))
lemma integral_known_prediction_defect (q : E → unitInterval) (S : Set E)
    (A C : Set (Set E)) (hA : MeasurableSet[blockSigma S] A) (hC : MeasurableSet C) :
    (∫ σ, A.indicator (fun σ => 1-(blockProbability q S C σ).toReal) σ ∂law q)=
      (law q).real (A\C) := by
  have he : (fun σ => A.indicator (fun σ => 1-(blockProbability q S C σ).toReal) σ)=
      (fun σ => (blockProbability q S (Cᶜ∩A) σ).toReal) := by
    funext σ
    rw [blockProbability_inter_block q S Cᶜ A hA]
    by_cases hσ : σ∈A
    · simp only [Set.indicator_of_mem hσ,blockProbability_real_compl q S σ C hC]
    · simp only [Set.indicator_of_notMem hσ,ENNReal.toReal_zero]
  rw [he,integral_blockProbability_real q S (Cᶜ∩A) (hC.compl.inter ((blockSigma_le S) _ hA))]
  congr 1
  exact Set.inter_comm _ _
lemma bad_prediction_bound (q : E → unitInterval) (S : Set E)
    (A C : Set (Set E)) (hA : MeasurableSet[blockSigma S] A) (hC : MeasurableSet C)
    (δ : ℝ) (hδ : 0<δ) :
    (law q).real (A∩{σ : Set E | (blockProbability q S C σ).toReal<1-δ})≤
      (law q).real (A\C)/δ := by
  let g := fun σ => (blockProbability q S C σ).toReal
  let B := A∩{σ : Set E | g σ<1-δ}
  have hg : Measurable g :=
    ((measurable_blockProbability q S C hC).mono (blockSigma_le S) le_rfl).ennreal_toReal
  have hma := (blockSigma_le S) _ hA
  have hmb : MeasurableSet B := hma.inter (measurableSet_lt hg measurable_const)
  have hgi : Integrable g (law q) := integrable_blockProbability_real q S C hC
  have hdef : Integrable (A.indicator (fun σ => 1-g σ)) (law q) :=
    ((integrable_const 1).sub hgi).indicator hma
  have hl : Integrable (fun σ => δ*B.indicator (1 : Set E → ℝ) σ) (law q) :=
    ((integrable_const 1).indicator hmb).const_mul δ
  have hi := integral_mono hl hdef (fun σ => by
    by_cases hσ : σ∈B
    · rw [Set.indicator_of_mem hσ,Set.indicator_of_mem hσ.1]
      dsimp only [Pi.one_apply]
      have hh := hσ.2
      dsimp only [Set.mem_ofPred_eq] at hh
      linarith
    · rw [Set.indicator_of_notMem hσ,mul_zero]
      by_cases hσA : σ∈A
      · rw [Set.indicator_of_mem hσA]
        exact sub_nonneg.mpr (ENNReal.toReal_mono (by simp) (blockProbability_le_one q S C σ))
      · rw [Set.indicator_of_notMem hσA])
  rw [integral_const_mul,integral_indicator_one hmb] at hi
  have he := integral_known_prediction_defect q S A C hA hC
  change (∫ σ, A.indicator (fun σ => 1-g σ) σ ∂law q)=(law q).real (A\C) at he
  rw [he] at hi
  exact (le_div_iff₀ hδ).mpr (by nlinarith [hi])
theorem two_prediction_failure (q : E → unitInterval) (S : Set E)
    (A C D : Set (Set E)) (hA : MeasurableSet[blockSigma S] A)
    (hC : MeasurableSet C) (hD : MeasurableSet D)
    (δ a : ℝ) (hδ : 0<δ) (hin : 1-δ≤(law q).real A)
    (hCfail : (law q).real (A\C)≤a) (hDfail : (law q).real (A\D)≤a) :
    (law q).real (Aᶜ ∪
      (A∩{σ : Set E | (blockProbability q S C σ).toReal<1-δ}) ∪
      (A∩{σ : Set E | (blockProbability q S D σ).toReal<1-δ}))≤δ+2*a/δ := by
  have hma := (blockSigma_le S) _ hA
  have hcomp : (law q).real Aᶜ≤δ := by rw [probReal_compl_eq_one_sub hma]; linarith
  have hc := (bad_prediction_bound q S A C hA hC δ hδ).trans
    (div_le_div_of_nonneg_right hCfail hδ.le)
  have hd := (bad_prediction_bound q S A D hA hD δ hδ).trans
    (div_le_div_of_nonneg_right hDfail hδ.le)
  have h1 := measureReal_union_le (μ := law q) (s₁ := Aᶜ)
    (s₂ := A∩{σ : Set E | (blockProbability q S C σ).toReal<1-δ})
  have h2 := measureReal_union_le (μ := law q)
    (s₁ := Aᶜ∪(A∩{σ : Set E | (blockProbability q S C σ).toReal<1-δ}))
    (s₂ := A∩{σ : Set E | (blockProbability q S D σ).toReal<1-δ})
  calc
    _ ≤ _ := h2
    _ ≤ (law q).real Aᶜ+(law q).real
        (A∩{σ : Set E | (blockProbability q S C σ).toReal<1-δ})+
        (law q).real (A∩{σ : Set E | (blockProbability q S D σ).toReal<1-δ}) :=
      add_le_add h1 le_rfl
    _ ≤ δ+a/δ+a/δ := add_le_add (add_le_add hcomp hc) hd
    _ = δ+2*a/δ := by ring
end CriticalPercolation.BernoulliProduct
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Model
section

namespace OAI
open Set MeasureTheory ProbabilityTheory
namespace CriticalPercolation
structure BondGraph (V E : Type*) where
  ends : E → Sym2 V
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)
def openGraph (ω : Set E) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (G.ends '' ω)
def fullGraph : SimpleGraph V := G.openGraph Set.univ
def LocallyFinite : Prop := ∀ v : V, {e : E | v ∈ G.ends e}.Finite
structure Aut where
  vertex : V ≃ V
  edge : E ≃ E
  preserves : ∀ e, G.ends (edge e) = Sym2.map vertex (G.ends e)
def QuasiTransitive : Prop :=
  ∃ S : Set V, S.Finite ∧ ∀ v : V, ∃ s ∈ S, ∃ φ : G.Aut, φ.vertex s = v
def cluster (ω : Set E) (v : V) : Set V := {w | (G.openGraph ω).Reachable v w}
def percolates : Set (Set E) := {ω | ∃ v : V, (G.cluster ω v).Infinite}
noncomputable def law (_G : BondGraph V E) (p : unitInterval) : Measure (Set E) :=
  ProbabilityTheory.setBernoulli Set.univ p
noncomputable def criticalProbability : unitInterval :=
  sInf {p : unitInterval | 0 < G.law p G.percolates}
end BondGraph
end CriticalPercolation
end OAI

end
-- OAI.Probability.CriticalPercolation.GraphGeometry.VertexBall
section

namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
namespace CriticalPercolation
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)
theorem openGraph_mono {ω ω' : Set E} (h : ω ⊆ ω') :
    G.openGraph ω ≤ G.openGraph ω' :=
  SimpleGraph.fromEdgeSet_mono (Set.image_mono h)
theorem cluster_mono {ω ω' : Set E} (h : ω ⊆ ω') (v : V) :
    G.cluster ω v ⊆ G.cluster ω' v :=
  fun _ hw => hw.mono (G.openGraph_mono h)
theorem finite_neighbors (hlocal : G.LocallyFinite) (v : V) :
    (G.fullGraph.neighborSet v).Finite := by
  classical
  have hf : (⋃ e ∈ {e : E | v ∈ G.ends e}, (↑(G.ends e).toFinset : Set V)).Finite :=
    (hlocal v).biUnion fun e _ => (G.ends e).toFinset.finite_toSet
  apply hf.subset
  intro w hw
  obtain ⟨⟨e, _, he⟩, _⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hw
  apply Set.mem_iUnion₂.mpr
  refine ⟨e, ?_, ?_⟩ <;> simp [he]
def vertexBall (G : BondGraph V E) (o : V) : ℕ → Set V
  | 0 => {o}
  | n + 1 => G.vertexBall o n ∪ ⋃ v ∈ G.vertexBall o n, G.fullGraph.neighborSet v
lemma vertexBall_finite (hlocal : G.LocallyFinite) (o : V) (n : ℕ) :
    (G.vertexBall o n).Finite := by
  induction n with
  | zero => exact Set.finite_singleton o
  | succ n ih => exact ih.union (ih.biUnion fun v _ => G.finite_neighbors hlocal v)
lemma reachable_mem_vertexBall {o v : V} (h : G.fullGraph.Reachable o v) :
    ∃ n, v ∈ G.vertexBall o n := by
  have hr := (G.fullGraph.reachable_iff_reflTransGen o v).mp h
  clear h
  induction hr with
  | refl => exact ⟨0, rfl⟩
  | @tail u w hr huv ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, Or.inr (Set.mem_iUnion₂.mpr ⟨u, hn, huv⟩)⟩
theorem countable_vertices (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) : Countable V := by
  obtain ⟨o⟩ := hconnected.nonempty
  have hc : (⋃ n : ℕ, G.vertexBall o n).Countable :=
    Set.countable_iUnion fun n => (G.vertexBall_finite hlocal o n).countable
  have heq : (⋃ n : ℕ, G.vertexBall o n) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    obtain ⟨n, hn⟩ := G.reachable_mem_vertexBall (hconnected o v)
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  rw [heq] at hc
  exact Set.countable_univ_iff.mp hc
theorem countable_bonds (hconnected : G.fullGraph.Connected)
    (hlocal : G.LocallyFinite) : Countable E := by
  let := G.countable_vertices hconnected hlocal
  have hc : (⋃ v : V, {e : E | v ∈ G.ends e}).Countable :=
    Set.countable_iUnion fun v => (hlocal v).countable
  have heq : (⋃ v : V, {e : E | v ∈ G.ends e}) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro e
    exact Set.mem_iUnion.mpr ⟨(G.ends e).out.1, Sym2.out_fst_mem _⟩
  rw [heq] at hc
  exact Set.countable_univ_iff.mp hc
def lengthReach (H : SimpleGraph V) : ℕ → V → V → Prop
  | 0, v, w => v = w
  | n + 1, v, w => ∃ u, lengthReach H n v u ∧ H.Adj u w
lemma reachable_iff_exists_lengthReach (H : SimpleGraph V) (v w : V) :
    H.Reachable v w ↔ ∃ n, lengthReach H n v w := by
  rw [H.reachable_iff_reflTransGen]
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | @tail u w h huw ih =>
        obtain ⟨n, hn⟩ := ih
        exact ⟨n + 1, u, hn, huw⟩
  · rintro ⟨n, hn⟩
    induction n generalizing w with
    | zero => exact hn ▸ Relation.ReflTransGen.refl
    | succ n ih =>
        obtain ⟨u, hu, huw⟩ := hn
        exact (ih u hu).tail huw
lemma measurable_openGraph_adj [Countable E] (v w : V) :
    Measurable (fun ω : Set E => (G.openGraph ω).Adj v w) := by
  simp only [openGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_image]
  exact (Measurable.exists fun e =>
    (measurable_set_mem e).and measurable_const).and measurable_const
lemma measurable_lengthReach [Countable V] [Countable E] (n : ℕ) (v w : V) :
    Measurable (fun ω : Set E => lengthReach (G.openGraph ω) n v w) := by
  induction n generalizing w with
  | zero => exact measurable_const
  | succ n ih =>
      exact Measurable.exists fun u => (ih u).and (G.measurable_openGraph_adj u w)
lemma measurable_reachable [Countable V] [Countable E] (v w : V) :
    Measurable (fun ω : Set E => (G.openGraph ω).Reachable v w) := by
  simp_rw [reachable_iff_exists_lengthReach]
  exact Measurable.exists fun n => G.measurable_lengthReach n v w
lemma measurable_cluster [Countable V] [Countable E] (v : V) :
    Measurable (fun ω : Set E => G.cluster ω v) := by
  exact measurable_pi_lambda _ fun vertex => G.measurable_reachable v vertex
@[simp] lemma openGraph_empty : G.openGraph ∅ = ⊥ := by
  simp [openGraph]
lemma criticalProbability_le_of_pos {p : unitInterval}
    (hp : 0 < G.law p G.percolates) : G.criticalProbability ≤ p :=
  sInf_le hp
lemma mem_cluster_finite_witness {ω : Set E} {v w : V} (h : w ∈ G.cluster ω v) :
    ∃ s : Set E, s.Finite ∧ s ⊆ ω ∧ w ∈ G.cluster s v := by
  classical
  have hr := ((G.openGraph ω).reachable_iff_reflTransGen v w).mp h
  clear h
  induction hr with
  | refl => exact ⟨∅, Set.finite_empty, Set.empty_subset _, .refl _⟩
  | @tail u w hr huw ih =>
      obtain ⟨s, hs, hsω, hvs⟩ := ih
      obtain ⟨⟨e, heω, heq⟩, hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp huw
      refine ⟨insert e s, hs.insert e, Set.insert_subset heω hsω, ?_⟩
      have hvu : (G.openGraph (insert e s)).Reachable v u :=
        hvs.mono (G.openGraph_mono (Set.subset_insert _ _))
      apply hvu.trans
      apply SimpleGraph.Adj.reachable
      exact (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e, Set.mem_insert _ _, heq⟩, hne⟩
end BondGraph
namespace ClusterDeletion
variable {V : Type*}
def delete (H : SimpleGraph V) (U : Set V) : SimpleGraph V where
  Adj v w := H.Adj v w ∧ v ∉ U ∧ w ∉ U
  symm.symm _v _w h := ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless.irrefl v h := H.loopless.irrefl v h.1
def roots (H : SimpleGraph V) (S : Set V) : Set V :=
  {v | ∃ s ∈ S, H.Reachable s v}
def component (H : SimpleGraph V) (s : V) : Set V :=
  {v | H.Reachable s v}
lemma delete_antitone (H : SimpleGraph V) {U U' : Set V} (h : U ⊆ U') :
    delete H U' ≤ delete H U :=
  fun _ _ hh => ⟨hh.1, fun hv => hh.2.1 (h hv), fun hw => hh.2.2 (h hw)⟩
lemma delete_le (H : SimpleGraph V) (U : Set V) : delete H U ≤ H :=
  fun _ _ h => h.1
lemma roots_mono {H H' : SimpleGraph V} (h : H ≤ H') (S : Set V) :
    roots H S ⊆ roots H' S := by
  rintro v ⟨s, hs, hsv⟩
  exact ⟨s, hs, hsv.mono h⟩
lemma component_mono {H H' : SimpleGraph V} (h : H ≤ H') (s : V) :
    component H s ⊆ component H' s :=
  fun _ hv => hv.mono h
lemma roots_self (H : SimpleGraph V) (S : Set V) : S ⊆ roots H S :=
  fun s hs => ⟨s, hs, .refl _⟩
lemma reachable_not_mem_roots {H : SimpleGraph V} {S : Set V} {s v : V}
    (hs : s ∉ roots H S) (hsv : H.Reachable s v) : v ∉ roots H S := by
  rintro ⟨u, hu, huv⟩
  exact hs ⟨u, hu, huv.trans hsv.symm⟩
lemma roots_closed {H : SimpleGraph V} {S : Set V} {v w : V}
    (hv : v ∈ roots H S) (hvw : H.Adj v w) : w ∈ roots H S := by
  obtain ⟨s, hs, hsv⟩ := hv
  exact ⟨s, hs, hsv.trans hvw.reachable⟩
lemma reachable_mem_of_closed {H : SimpleGraph V} {U : Set V}
    (hU : ∀ ⦃v w⦄, v ∈ U → H.Adj v w → w ∈ U) {s v : V}
    (hs : s ∈ U) (hsv : H.Reachable s v) : v ∈ U := by
  have hr := (H.reachable_iff_reflTransGen s v).mp hsv
  clear hsv
  induction hr with
  | refl => exact hs
  | tail _ huv ih => exact hU ih huv
lemma roots_subset_of_adj {H H' : SimpleGraph V} (S : Set V)
    (hh : ∀ ⦃v w⦄, v ∈ roots H S → H.Adj v w → H'.Adj v w) :
    roots H S ⊆ roots H' S := by
  rintro v ⟨s, hs, hsv⟩
  refine ⟨s, hs, ?_⟩
  have hr := (H.reachable_iff_reflTransGen s v).mp hsv
  clear hsv
  induction hr with
  | refl => exact .refl _
  | @tail u v hr huv ih =>
      exact ih.trans (hh ⟨s, hs, (H.reachable_iff_reflTransGen s u).mpr hr⟩ huv).reachable
lemma roots_eq_of_adj_eq_incident {H H' : SimpleGraph V} {S U : Set V}
    (hU : roots H S = U)
    (hh : ∀ ⦃v w⦄, v ∈ U → (H.Adj v w ↔ H'.Adj v w)) :
    roots H' S = U := by
  subst U
  apply Set.Subset.antisymm
  · rintro v ⟨s, hs, hsv⟩
    exact reachable_mem_of_closed
      (fun {_ _} hv hvw => roots_closed hv ((hh hv).mpr hvw)) (roots_self H S hs) hsv
  · exact roots_subset_of_adj S fun {_ _} hv hvw => (hh hv).mp hvw
lemma delete_roots_component (H : SimpleGraph V) (S : Set V) (s : V)
    (hs : s ∉ roots H S) :
    component (delete H (roots H S)) s = component H s := by
  apply Set.Subset.antisymm (component_mono (delete_le _ _) _)
  intro v hv
  have hr := (H.reachable_iff_reflTransGen s v).mp hv
  clear hv
  induction hr with
  | refl => exact .refl _
  | @tail u v hr huv ih =>
      have hsu : H.Reachable s u := (H.reachable_iff_reflTransGen _ _).mpr hr
      have hsv : H.Reachable s v := hsu.trans huv.reachable
      exact ih.trans (SimpleGraph.Adj.reachable
        ⟨huv, reachable_not_mem_roots hs hsu, reachable_not_mem_roots hs hsv⟩)
lemma delete_delete (H : SimpleGraph V) (U W : Set V) :
    delete (delete H U) W = delete H (W ∪ U) := by
  ext v w
  simp only [delete, Set.mem_union, not_or]
  tauto
lemma delete_roots_union_component (H : SimpleGraph V) (S U : Set V) (s : V)
    (hs : s ∉ roots (delete H U) S) :
    component (delete H (roots (delete H U) S ∪ U)) s = component (delete H U) s := by
  rw [← delete_delete]
  exact delete_roots_component _ _ _ hs
noncomputable def residual (H : SimpleGraph V) (S : Set V) (s : V)
    (F : Set V → ℝ) (U : Set V) : ℝ := by
  classical
  exact if s ∉ roots (delete H U) S then
    F (component (delete H (roots (delete H U) S)) s) -
      F (component (delete H (roots (delete H U) S ∪ U)) s)
  else 0
lemma residual_nonneg (H : SimpleGraph V) (S : Set V) (s : V)
    {F : Set V → ℝ} (hF : Monotone F) (U : Set V) : 0 ≤ residual H S s F U := by
  classical
  unfold residual
  split_ifs
  · rfl
  · exact sub_nonneg.mpr (hF (component_mono (delete_antitone H Set.subset_union_left) s))
lemma residual_monotone (H : SimpleGraph V) (S : Set V) (s : V)
    {F : Set V → ℝ} (hF : Monotone F) : Monotone (residual H S s F) := by
  classical
  intro U U' hUU'
  have hW : roots (delete H U') S ⊆ roots (delete H U) S :=
    roots_mono (delete_antitone H hUU') S
  by_cases hs : s ∉ roots (delete H U) S
  · have hs' : s ∉ roots (delete H U') S := fun h => hs (hW h)
    rw [residual, if_pos hs, residual, if_pos hs']
    rw [delete_roots_union_component H S U s hs,
      delete_roots_union_component H S U' s hs']
    have hh₁ := hF (component_mono (delete_antitone H hW) s)
    have hh₂ := hF (component_mono (delete_antitone H hUU') s)
    exact sub_le_sub hh₁ hh₂
  · rw [residual, if_neg hs]
    exact residual_nonneg H S s hF U'
end ClusterDeletion
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)
def incidentEdges (U : Set V) : Set E := {e | ∃ v ∈ U, v ∈ G.ends e}
lemma openGraph_adj_eq_of_incident {U : Set V} {ω ω' : Set E}
    (hω : ∀ e ∈ G.incidentEdges U, e ∈ ω ↔ e ∈ ω') {v w : V} (hv : v ∈ U) :
    (G.openGraph ω).Adj v w ↔ (G.openGraph ω').Adj v w := by
  simp only [openGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_image]
  have he : ∀ e, G.ends e = s(v, w) → e ∈ G.incidentEdges U := by
    intro e heq
    exact ⟨v, hv, by simp [heq]⟩
  constructor
  · rintro ⟨⟨e, heω, heq⟩, hne⟩
    exact ⟨⟨e, (hω e (he e heq)).mp heω, heq⟩, hne⟩
  · rintro ⟨⟨e, heω, heq⟩, hne⟩
    exact ⟨⟨e, (hω e (he e heq)).mpr heω, heq⟩, hne⟩
lemma delete_openGraph_dependsOn (U : Set V) :
    DependsOn (fun ω : Set E => ClusterDeletion.delete (G.openGraph ω) U)
      (G.incidentEdges U)ᶜ := by
  intro ω ω' hω
  ext v w
  change ((G.openGraph ω).Adj v w ∧ v ∉ U ∧ w ∉ U) ↔
    ((G.openGraph ω').Adj v w ∧ v ∉ U ∧ w ∉ U)
  by_cases hv : v ∈ U
  · simp [hv]
  by_cases hw : w ∈ U
  · simp [hw]
  simp only [hv, hw, not_false_eq_true, and_self, and_true, openGraph,
    SimpleGraph.fromEdgeSet_adj]
  have he : ∀ e, G.ends e = s(v, w) → e ∈ (G.incidentEdges U)ᶜ := by
    intro e heq
    rintro ⟨x, hxU, hxe⟩
    have := hxe
    simp only [heq, Sym2.mem_iff] at this
    rcases this with rfl | rfl
    · exact hv hxU
    · exact hw hxU
  constructor
  · rintro ⟨⟨e, heω, heq⟩, hne⟩
    exact ⟨⟨e, (hω e (he e heq)).to_iff.mp heω, heq⟩, hne⟩
  · rintro ⟨⟨e, heω, heq⟩, hne⟩
    exact ⟨⟨e, (hω e (he e heq)).to_iff.mpr heω, heq⟩, hne⟩
lemma deleted_roots_eq_of_incident {S U W : Set V} {ω ω' : Set E}
    (hW : ClusterDeletion.roots (ClusterDeletion.delete (G.openGraph ω) U) S = W)
    (hω : ∀ e ∈ G.incidentEdges W, e ∈ ω ↔ e ∈ ω') :
    ClusterDeletion.roots (ClusterDeletion.delete (G.openGraph ω') U) S = W := by
  apply ClusterDeletion.roots_eq_of_adj_eq_incident hW
  intro v v' hv
  change ((G.openGraph ω).Adj v v' ∧ v ∉ U ∧ v' ∉ U) ↔
    ((G.openGraph ω').Adj v v' ∧ v ∉ U ∧ v' ∉ U)
  rw [G.openGraph_adj_eq_of_incident hω hv]
lemma dependsOn_exact_deleted_roots (S U W : Set V) :
    DependsOn (fun ω : Set E =>
      ClusterDeletion.roots (ClusterDeletion.delete (G.openGraph ω) U) S = W)
      (G.incidentEdges W) := by
  intro ω ω' hω
  apply propext
  exact ⟨fun h => G.deleted_roots_eq_of_incident h (fun e he => (hω e he).to_iff),
    fun h => G.deleted_roots_eq_of_incident h (fun e he => (hω e he).symm.to_iff)⟩
end BondGraph
end CriticalPercolation
open scoped BigOperators
open Set
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.GraphGeometry.FiniteInduced
section

namespace OAI
section
section
noncomputable section
open Set
open scoped Classical
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)
def inducedEdges (S : Set V) : Set E := {e | ∀ v ∈ G.ends e, v∈S}
lemma finite_incident (hG : G.LocallyFinite) {S : Set V} (hS : S.Finite) :
    (G.incidentEdges S).Finite := by
  have hh := hS.biUnion (fun v _ => hG v)
  convert hh using 1
  ext e
  simp only [incidentEdges,Set.mem_ofPred_eq,Set.mem_iUnion,exists_prop]
end CriticalPercolation.BondGraph
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Clusters.HitValue
section

namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CriticalPercolation.ClusterColumns
open CriticalPercolation.ClusterDeletion
open scoped Classical
variable {V : Type*}
noncomputable def hitValue (A U : Set V) : ℝ := if (U ∩ A).Nonempty then 1 else 0
noncomputable def jointHitValue (A T U : Set V) : ℝ :=
  if (U ∩ A).Nonempty ∧ (U ∩ T).Nonempty then 1 else 0
lemma jointHitValue_nonneg (A T U : Set V) : 0 ≤ jointHitValue A T U := by
  unfold jointHitValue; positivity
lemma jointHitValue_monotone (A T : Set V) : Monotone (jointHitValue A T) := by
  intro U W hUW
  unfold jointHitValue
  split_ifs with hU hW hW
  · exact le_rfl
  · exact (hW ⟨hU.1.mono (Set.inter_subset_inter_left A hUW),
      hU.2.mono (Set.inter_subset_inter_left T hUW)⟩).elim
  · norm_num
  · exact le_rfl
lemma jointHitValue_eq_hitValue {A T U : Set V} (hA : (U ∩ A).Nonempty) :
    jointHitValue A T U = hitValue T U := by simp [jointHitValue, hitValue, hA]
lemma component_inter_nonempty_iff (H : SimpleGraph V) (s : V) (A : Set V) :
    (component H s ∩ A).Nonempty ↔ s ∈ roots H A := by
  constructor
  · rintro ⟨t, ht, hA⟩
    exact ⟨t, hA, ht.symm⟩
  · rintro ⟨t, hA, ht⟩
    exact ⟨t, ht.symm, hA⟩
end CriticalPercolation.ClusterColumns
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Clusters.ComponentSelf
section

namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
namespace CriticalPercolation.ClusterDeletion
variable {V : Type*}
lemma component_self (H : SimpleGraph V) (s : V) : s ∈ component H s :=
  SimpleGraph.Reachable.refl s
lemma roots_singleton (H : SimpleGraph V) (s : V) : roots H {s} = component H s := by
  ext v
  simp [roots, component]
lemma component_eq_of_mem {H : SimpleGraph V} {s t : V}
    (h : t ∈ component H s) : component H t = component H s := by
  ext v
  exact ⟨fun hv => h.trans hv, fun hv => h.symm.trans hv⟩
lemma not_mem_roots_iff_disjoint (H : SimpleGraph V) (S : Set V) (s : V) :
    s ∉ roots H S ↔ Disjoint (component H s) S := by
  rw [Set.disjoint_left]
  constructor
  · intro hs t ht hS
    exact hs ⟨t, hS, ht.symm⟩
  · intro hd ⟨t, ht, hts⟩
    exact hd hts.symm ht
lemma component_delete_component (H : SimpleGraph V) (s t : V)
    (h : t ∉ component H s) :
    component (delete H (component H s)) t = component H t := by
  simpa only [roots_singleton] using
    (delete_roots_component H {s} t (by simpa only [roots_singleton] using h))
lemma roots_delete_component (H : SimpleGraph V) (S : Set V) (s : V)
    (h : s ∉ roots H S) : roots (delete H (component H s)) S = roots H S := by
  ext v
  constructor
  · intro hv
    exact roots_mono (delete_le H _) S hv
  · rintro ⟨t, ht, htv⟩
    refine ⟨t, ht, ?_⟩
    have hts : t ∉ component H s := fun hg => h ⟨t, ht, hg.symm⟩
    change v ∈ component (delete H (component H s)) t
    rw [component_delete_component H s t hts]
    exact htv
lemma delete_empty (H : SimpleGraph V) : delete H ∅ = H := by
  ext v w
  simp only [delete, Set.mem_empty_iff_false, not_false_eq_true, and_true]
end CriticalPercolation.ClusterDeletion
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Clusters.Earlier
section

namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CriticalPercolation.ClusterColumns
open CriticalPercolation.ClusterDeletion
open scoped Classical
variable {V : Type*} {n : ℕ}
def earlier (x : Fin n → V) (k : Fin n) : Set V := {v | ∃ j < k, x j = v}
def first (H : SimpleGraph V) (x : Fin n → V) (k : Fin n) : Prop :=
  x k ∉ roots H (earlier x k)
noncomputable def select (H : SimpleGraph V) (x : Fin n → V) (k i : Fin n) : ℝ :=
  if first H x k ∧ x i ∈ component H (x k) then 1 else 0
lemma root_not_mem_earlier {x : Fin n → V} (hx : Function.Injective x) (k : Fin n) :
    x k ∉ earlier x k := by
  rintro ⟨j, hj, heq⟩
  exact (ne_of_lt hj) (hx heq)
lemma earlier_mono (x : Fin n → V) {k l : Fin n} (hkl : k ≤ l) :
    earlier x k ⊆ earlier x l := by
  rintro v ⟨j, hj, rfl⟩
  exact ⟨j, hj.trans_le hkl, rfl⟩
lemma first_unique {H : SimpleGraph V} {x : Fin n → V} {k l i : Fin n}
    (hk : first H x k) (hki : x i ∈ component H (x k))
    (hl : first H x l) (hli : x i ∈ component H (x l)) : k = l := by
  apply le_antisymm
  · by_contra! h
    exact hk ⟨x l, ⟨l, h, rfl⟩, hli.trans hki.symm⟩
  · by_contra! h
    exact hl ⟨x k, ⟨k, h, rfl⟩, hki.trans hli.symm⟩
lemma exists_first (H : SimpleGraph V) (x : Fin n → V) (i : Fin n) :
    ∃ k, first H x k ∧ x i ∈ component H (x k) := by
  classical
  let J := Finset.univ.filter (fun j => x i ∈ component H (x j))
  have hi : i ∈ J := by simp [J, component_self]
  have hJ : J.Nonempty := ⟨i, hi⟩
  let k := J.min' hJ
  have hkJ : k ∈ J := Finset.min'_mem J hJ
  have hki : x i ∈ component H (x k) := (Finset.mem_filter.mp hkJ).2
  refine ⟨k, ?_, hki⟩
  rintro ⟨v, ⟨j, hj, rfl⟩, hjk⟩
  have hjJ : j ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjk.trans hki⟩
  have hkj : k ≤ j := Finset.min'_le J j hjJ
  exact (not_lt_of_ge hkj) hj
lemma select_nonneg (H : SimpleGraph V) (x : Fin n → V) (k i : Fin n) :
    0 ≤ select H x k i := by unfold select; positivity
lemma select_zero_of_lt (H : SimpleGraph V) (x : Fin n → V) {k i : Fin n} (hik : i < k) :
    select H x k i = 0 := by
  apply if_neg
  rintro ⟨hk, hki⟩
  exact hk ⟨x i, ⟨i, hik, rfl⟩, hki.symm⟩
lemma select_diag (H : SimpleGraph V) (x : Fin n → V) (k : Fin n) :
    select H x k k = if first H x k then 1 else 0 := by
  simp only [select, component_self, and_true]
lemma select_mul_sum (H : SimpleGraph V) (x : Fin n → V) (i : Fin n)
    (a : Fin n → ℝ) {k : Fin n} (hk : first H x k)
    (hki : x i ∈ component H (x k)) :
    ∑ l, select H x l i * a l = a k := by
  classical
  rw [Finset.sum_eq_single k]
  · simp [select, hk, hki]
  · intro l _ hlk
    have hh : ¬ (first H x l ∧ x i ∈ component H (x l)) := by
      rintro ⟨hl, hli⟩
      exact hlk (first_unique hl hli hk hki)
    simp [select, hh]
  · simp
lemma select_mass (H : SimpleGraph V) (x : Fin n → V) (i : Fin n) :
    ∑ k, select H x k i = 1 := by
  obtain ⟨k, hk, hki⟩ := exists_first H x i
  simpa using select_mul_sum H x i (fun _ => 1) hk hki
lemma cluster_partition (H : SimpleGraph V) (x : Fin n → V)
    (F : Set V → ℝ) (i : Fin n) :
    F (component H (x i)) = ∑ k, select H x k i * F (component H (x k)) := by
  obtain ⟨k, hk, hki⟩ := exists_first H x i
  rw [select_mul_sum H x i _ hk hki, component_eq_of_mem hki]
lemma first_hit_not_mem_roots_iff (H : SimpleGraph V) (x : Fin n → V)
    {j i : Fin n} (hj : first H x j) (hji : x i ∈ component H (x j)) (k : Fin n) :
    x i ∉ roots H (earlier x k) ↔ k ≤ j := by
  constructor
  · intro hi
    by_contra! hjk
    exact hi ⟨x j, ⟨j, hjk, rfl⟩, hji⟩
  · rintro hkj ⟨v, ⟨l, hlk, rfl⟩, hli⟩
    exact hj ⟨x l, ⟨l, hlk.trans_le hkj, rfl⟩, hli.trans hji.symm⟩
lemma select_truncation (H : SimpleGraph V) (x : Fin n → V) (k i : Fin n) :
    (if x i ∉ roots H (earlier x k) then (1 : ℝ) else 0) =
      select H x k i + ∑ l, if k < l then select H x l i else 0 := by
  classical
  obtain ⟨j, hj, hji⟩ := exists_first H x i
  have he : ∀ l, select H x l i = if l = j then 1 else 0 := by
    intro l
    by_cases hlj : l = j
    · subst l
      simp [select, hj, hji]
    · have hh : ¬ (first H x l ∧ x i ∈ component H (x l)) := by
        rintro ⟨hl, hli⟩
        exact hlj (first_unique hl hli hj hji)
      simp [select, hh, hlj]
  simp_rw [he]
  have hsum : (∑ l : Fin n, if k < l then if l = j then (1 : ℝ) else 0 else 0) =
      if k < j then 1 else 0 := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro l _ hlj
      simp [hlj]
    · simp
  rw [hsum]
  simp only [first_hit_not_mem_roots_iff H x hj hji k]
  rcases lt_trichotomy k j with h | h | h
  · simp [h, ne_of_lt h, le_of_lt h]
  · subst j
    simp
  · simp [ne_of_gt h, not_le_of_gt h, not_lt_of_gt h]
end CriticalPercolation.ClusterColumns
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Clusters.ExpectedCluster
section

namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
open Set
namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)
lemma finite_spatialMarkov (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S U : Set V) (F : Set V → SimpleGraph V → ℝ) :
    expect w (fun ω =>
      F (roots (delete (G.openGraph ω) U) S)
        (delete (G.openGraph ω) (roots (delete (G.openGraph ω) U) S))) =
    expect w (fun ω => expect w (fun ω' =>
      F (roots (delete (G.openGraph ω) U) S)
        (delete (G.openGraph ω') (roots (delete (G.openGraph ω) U) S)))) := by
  classical
  refine expect_exposure w hw
    (fun ω => roots (delete (G.openGraph ω) U) S) G.incidentEdges
    (G.dependsOn_exact_deleted_roots S U)
    (fun W ω => F W (delete (G.openGraph ω) W)) ?_
  intro W ω ω' hω
  exact congrArg (F W) (G.delete_openGraph_dependsOn W hω)
noncomputable def expectedCluster (w : E → Prop → ℝ) (s : V)
    (F : Set V → ℝ) (W : Set V) : ℝ :=
  expect w (fun ω => F (component (delete (G.openGraph ω) W) s))
noncomputable def expectedResidual (w : E → Prop → ℝ) (S : Set V) (s : V)
    (F : Set V → ℝ) (U : Set V) : ℝ := by
  classical
  exact expect w (fun ω =>
    if s ∉ roots (delete (G.openGraph ω) U) S then
      G.expectedCluster w s F (roots (delete (G.openGraph ω) U) S) -
      G.expectedCluster w s F (roots (delete (G.openGraph ω) U) S ∪ U)
    else 0)
lemma expectedResidual_eq (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (F : Set V → ℝ) (U : Set V) :
    G.expectedResidual w S s F U =
      expect w (fun ω => residual (G.openGraph ω) S s F U) := by
  classical
  have h := G.finite_spatialMarkov w hw S U
    (fun W H => if s ∉ W then F (component H s) - F (component (delete H U) s) else 0)
  have hu : ∀ H W, delete (delete H W) U = delete H (W ∪ U) := by
    intro H W
    rw [delete_delete, Set.union_comm]
  simp_rw [hu] at h
  change _ = expect w (fun ω => if s ∉ roots (delete (G.openGraph ω) U) S then
    F (component (delete (G.openGraph ω) (roots (delete (G.openGraph ω) U) S)) s) -
    F (component (delete (G.openGraph ω) (roots (delete (G.openGraph ω) U) S ∪ U)) s)
    else 0)
  rw [h]
  unfold expectedResidual
  congr 1
  funext ω
  split_ifs
  · rw [expect_const w hw]
  · rw [expect_sub]
    rfl
lemma expectedResidual_nonneg (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (S : Set V) (s : V) {F : Set V → ℝ} (hF : Monotone F) (U : Set V) :
    0 ≤ G.expectedResidual w S s F U := by
  rw [expectedResidual_eq G w hw, ← expect_const w hw 0]
  exact expect_mono hpos fun ω => residual_nonneg (G.openGraph ω) S s hF U
lemma expectedResidual_monotone (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (S : Set V) (s : V) {F : Set V → ℝ} (hF : Monotone F) :
    Monotone (G.expectedResidual w S s F) := by
  intro U U' hUU'
  rw [expectedResidual_eq G w hw, expectedResidual_eq G w hw]
  exact expect_mono hpos fun ω => residual_monotone (G.openGraph ω) S s hF hUU'
end CriticalPercolation.BondGraph
open scoped BigOperators
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Clusters.ClusterUpdate
section

namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)
open scoped Classical
noncomputable def clusterUpdate (w : E → Prop → ℝ) (S : Set V) (s : V)
    (F : Set V → ℝ) (U : Set V) : ℝ :=
  expect w (fun ω => G.expectedCluster w s F (roots (delete (G.openGraph ω) U) S))
omit [Fintype V] in
lemma expectedCluster_antitone (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (s : V) {F : Set V → ℝ} (hF : Monotone F) :
    Antitone (G.expectedCluster w s F) := by
  intro U U' hU
  exact expect_mono hpos fun ω => hF (component_mono (delete_antitone _ hU) s)
omit [Fintype V] in
lemma clusterUpdate_monotone (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (S : Set V) (s : V) {F : Set V → ℝ} (hF : Monotone F) :
    Monotone (G.clusterUpdate w S s F) := by
  intro U U' hU
  exact expect_mono hpos fun ω => G.expectedCluster_antitone w hpos s hF
    (roots_mono (delete_antitone _ hU) S)
omit [Fintype V] in
lemma clusterUpdate_nonneg (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (S : Set V) (s : V) {F : Set V → ℝ} (hF : ∀ U, 0 ≤ F U) (U : Set V) :
    0 ≤ G.clusterUpdate w S s F U :=
  expect_nonneg hpos fun _ => expect_nonneg hpos fun _ => hF _
noncomputable def avoidedAverage (w : E → Prop → ℝ) (S : Set V) (s : V)
    (F : Set V → ℝ) : ℝ := by
  classical
  exact expect w (fun ω => if s ∉ roots (G.openGraph ω) S then
    F (component (G.openGraph ω) s) else 0)
lemma clusterUpdate_exposure (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (F g : Set V → ℝ) :
    (expect w (fun ω => if s ∉ roots (G.openGraph ω) S then
      g (component (G.openGraph ω) s) * G.expectedCluster w s F (roots (G.openGraph ω) S)
      else 0)) =
    G.avoidedAverage w S s (fun U => g U * G.clusterUpdate w S s F U) := by
  classical
  have h := G.finite_spatialMarkov w hw {s} ∅
    (fun U H => if Disjoint U S then g U * G.expectedCluster w s F (roots H S) else 0)
  simp only [delete_empty, roots_singleton] at h
  have hleft : (fun ω : E → Prop =>
      if Disjoint (component (G.openGraph ω) s) S then
        g (component (G.openGraph ω) s) * G.expectedCluster w s F
          (roots (delete (G.openGraph ω) (component (G.openGraph ω) s)) S) else 0) =
      (fun ω => if s ∉ roots (G.openGraph ω) S then
        g (component (G.openGraph ω) s) * G.expectedCluster w s F
          (roots (G.openGraph ω) S) else 0) := by
    funext ω
    rw [← not_mem_roots_iff_disjoint]
    split_ifs with hs
    · rfl
    · rw [roots_delete_component _ S s hs]
  rw [hleft] at h
  erw [h]
  unfold avoidedAverage
  congr 1
  funext ω
  rw [← not_mem_roots_iff_disjoint]
  split_ifs
  · rw [expect_zero]
  · rw [expect_const_mul]
    rfl
lemma avoidedAverage_exposure (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (F : Set V → ℝ) :
    G.avoidedAverage w S s F =
      expect w (fun ω => if s ∉ roots (G.openGraph ω) S then
        G.expectedCluster w s F (roots (G.openGraph ω) S) else 0) := by
  classical
  have h := G.finite_spatialMarkov w hw S ∅
    (fun W H => if s ∉ W then F (component H s) else 0)
  simp only [delete_empty] at h
  have hleft : (fun ω : E → Prop => if s ∉ roots (G.openGraph ω) S then
      F (component (delete (G.openGraph ω) (roots (G.openGraph ω) S)) s) else 0) =
      (fun ω => if s ∉ roots (G.openGraph ω) S then F (component (G.openGraph ω) s) else 0) := by
    funext ω
    split_ifs with hs
    · rfl
    · rw [delete_roots_component _ S s hs]
  rw [hleft] at h
  change expect w _ = _
  erw [h]
  congr 1
  funext ω
  split_ifs
  · rw [expect_zero]
  · rfl
lemma clusterUpdate_stationary (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (F : Set V → ℝ) :
    G.avoidedAverage w S s (G.clusterUpdate w S s F) = G.avoidedAverage w S s F := by
  have h := G.clusterUpdate_exposure w hw S s F (fun _ => 1)
  simp only [one_mul] at h
  exact h.symm.trans (G.avoidedAverage_exposure w hw S s F).symm
end CriticalPercolation.BondGraph
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.GraphGeometry.ExpectedResidualAlt
section

namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)
lemma expectedResidual_alt (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (F : Set V → ℝ) (U : Set V) :
    G.expectedResidual w S s F U =
      expect w (fun ω => if s ∉ roots (delete (G.openGraph ω) U) S then
        G.expectedCluster w s F (roots (delete (G.openGraph ω) U) S) -
          F (component (delete (G.openGraph ω) U) s) else 0) := by
  have h := G.finite_spatialMarkov w hw S U
    (fun W H => if s ∉ W then G.expectedCluster w s F W -
      F (component (delete H U) s) else 0)
  have hdel : ∀ H W, delete (delete H W) U = delete H (W ∪ U) := by
    intro H W
    rw [delete_delete, Set.union_comm]
  simp_rw [hdel] at h
  have hleft : (fun ω : E → Prop => if s ∉ roots (delete (G.openGraph ω) U) S then
      G.expectedCluster w s F (roots (delete (G.openGraph ω) U) S) -
        F (component (delete (G.openGraph ω) (roots (delete (G.openGraph ω) U) S ∪ U)) s)
      else 0) =
      (fun ω => if s ∉ roots (delete (G.openGraph ω) U) S then
        G.expectedCluster w s F (roots (delete (G.openGraph ω) U) S) -
          F (component (delete (G.openGraph ω) U) s) else 0) := by
    funext ω
    split_ifs with hs
    · rfl
    · rw [delete_roots_union_component _ S U s hs]
  rw [hleft] at h
  erw [h]
  unfold expectedResidual
  congr 1
  funext ω
  split_ifs
  · rw [expect_zero]
  · rw [expect_sub, expect_const w hw]
    rfl
lemma later_cluster_residual (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s t : V) (F g : Set V → ℝ) (Q : Set V → Prop)
    (hQ : ∀ U, Q U → Disjoint U S ∧ s ∉ U) :
    (expect w (fun ω => if Q (component (G.openGraph ω) t) then
      if s ∉ roots (G.openGraph ω) S then
        g (component (G.openGraph ω) t) *
          (G.expectedCluster w s F (roots (G.openGraph ω) S) -
            F (component (G.openGraph ω) s)) else 0 else 0)) =
    expect w (fun ω => if Q (component (G.openGraph ω) t) then
      g (component (G.openGraph ω) t) *
        G.expectedResidual w S s F (component (G.openGraph ω) t) else 0) := by
  have h := G.finite_spatialMarkov w hw {t} ∅
    (fun U H => if Q U then if s ∉ roots H S then
      g U * (G.expectedCluster w s F (roots H S) - F (component H s)) else 0 else 0)
  simp only [delete_empty, roots_singleton] at h
  have hleft : (fun ω : E → Prop => if Q (component (G.openGraph ω) t) then
      if s ∉ roots (delete (G.openGraph ω) (component (G.openGraph ω) t)) S then
        g (component (G.openGraph ω) t) *
          (G.expectedCluster w s F (roots (delete (G.openGraph ω) (component (G.openGraph ω) t)) S) -
            F (component (delete (G.openGraph ω) (component (G.openGraph ω) t)) s))
        else 0 else 0) =
      (fun ω => if Q (component (G.openGraph ω) t) then
        if s ∉ roots (G.openGraph ω) S then
          g (component (G.openGraph ω) t) *
            (G.expectedCluster w s F (roots (G.openGraph ω) S) - F (component (G.openGraph ω) s))
          else 0 else 0) := by
    funext ω
    by_cases hq : Q (component (G.openGraph ω) t)
    · simp only [if_pos hq]
      obtain ⟨hd, hs⟩ := hQ _ hq
      rw [roots_delete_component _ S t ((not_mem_roots_iff_disjoint _ S t).mpr hd),
        component_delete_component _ t s hs]
    · simp only [if_neg hq]
  rw [hleft] at h
  erw [h]
  congr 1
  funext ω
  by_cases hq : Q (component (G.openGraph ω) t)
  · simp only [if_pos hq]
    rw [G.expectedResidual_alt w hw]
    rw [← expect_const_mul]
    congr 1
    funext ω'
    split_ifs <;> simp
  · simp only [if_neg hq, expect_zero]
end CriticalPercolation.BondGraph
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.GraphGeometry.Column
section

namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)
lemma avoided_drift_zero (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (F b : Set V → ℝ) :
    expect w (fun ω => if s ∉ roots (G.openGraph ω) S then
      b (roots (G.openGraph ω) S) * (F (component (G.openGraph ω) s) -
        G.expectedCluster w s F (roots (G.openGraph ω) S)) else 0) = 0 := by
  have h := G.finite_spatialMarkov w hw S ∅
    (fun W H => if s ∉ W then b W * (F (component H s) - G.expectedCluster w s F W) else 0)
  simp only [delete_empty] at h
  have hleft : (fun ω : E → Prop => if s ∉ roots (G.openGraph ω) S then
      b (roots (G.openGraph ω) S) * (F (component (delete (G.openGraph ω) (roots (G.openGraph ω) S)) s) -
        G.expectedCluster w s F (roots (G.openGraph ω) S)) else 0) =
      (fun ω => if s ∉ roots (G.openGraph ω) S then
        b (roots (G.openGraph ω) S) * (F (component (G.openGraph ω) s) -
          G.expectedCluster w s F (roots (G.openGraph ω) S)) else 0) := by
    funext ω
    split_ifs with hs
    · rfl
    · rw [delete_roots_component _ S s hs]
  rw [hleft] at h
  erw [h]
  have hz : ∀ W : Set V, expect w (fun ω => if s ∉ W then
      b W * (F (component (delete (G.openGraph ω) W) s) - G.expectedCluster w s F W)
      else 0) = 0 := by
    intro W
    split_ifs
    · exact expect_zero w
    · rw [expect_const_mul, expect_sub, expect_const w hw]
      change b W * (G.expectedCluster w s F W - G.expectedCluster w s F W) = 0
      ring
  simp only [hz, expect_zero]
noncomputable def column {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
    (k : Fin n) (F : Set V → ℝ) (i : Fin n) : ℝ :=
  expect w (fun ω => select (G.openGraph ω) x k i * F (component (G.openGraph ω) (x k)))
omit [Fintype V] in
lemma column_as_avoidedAverage {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
    (k : Fin n) (F : Set V → ℝ) (i : Fin n) :
    G.column w x k F i = G.avoidedAverage w (earlier x k) (x k)
      (fun U => (if x i ∈ U then 1 else 0) * F U) := by
  unfold column avoidedAverage select first
  congr 1
  funext ω
  split_ifs <;> simp_all
lemma column_update {n : ℕ} (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (x : Fin n → V) (k : Fin n) (F : Set V → ℝ) (i : Fin n) :
    G.column w x k (G.clusterUpdate w (earlier x k) (x k) F) i =
      expect w (fun ω => select (G.openGraph ω) x k i *
        G.expectedCluster w (x k) F (roots (G.openGraph ω) (earlier x k))) := by
  rw [G.column_as_avoidedAverage]
  rw [← G.clusterUpdate_exposure w hw]
  congr 1
  funext ω
  simp only [select, first]
  split_ifs <;> simp_all
lemma column_later_residual {n : ℕ} (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (x : Fin n → V) {k l : Fin n} (hkl : k < l) (F : Set V → ℝ) (i : Fin n) :
    G.column w x l (G.expectedResidual w (earlier x k) (x k) F) i =
    expect w (fun ω => if first (G.openGraph ω) x k then
      select (G.openGraph ω) x l i *
        (G.expectedCluster w (x k) F (roots (G.openGraph ω) (earlier x k)) -
          F (component (G.openGraph ω) (x k))) else 0) := by
  have h := G.later_cluster_residual w hw (earlier x k) (x k) (x l) F
    (fun U => if x i ∈ U then 1 else 0) (fun U => Disjoint U (earlier x l))
    (fun U hU => ⟨hU.mono_right (earlier_mono x hkl.le),
      fun hs => (Set.disjoint_left.mp hU) hs ⟨k, hkl, rfl⟩⟩)
  have hc : (fun ω : E → Prop => if Disjoint (component (G.openGraph ω) (x l)) (earlier x l) then
      (if x i ∈ component (G.openGraph ω) (x l) then 1 else 0) *
        G.expectedResidual w (earlier x k) (x k) F (component (G.openGraph ω) (x l)) else 0) =
      (fun ω => select (G.openGraph ω) x l i *
        G.expectedResidual w (earlier x k) (x k) F (component (G.openGraph ω) (x l))) := by
    funext ω
    simp only [select, first, not_mem_roots_iff_disjoint]
    split_ifs <;> simp_all
  rw [hc] at h
  unfold column
  erw [← h]
  congr 1
  funext ω
  simp only [select, first, not_mem_roots_iff_disjoint]
  split_ifs <;> simp_all
lemma column_decomposition {n : ℕ} (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (x : Fin n → V) (k : Fin n) (F : Set V → ℝ) (i : Fin n) :
    G.column w x k F i =
      G.column w x k (G.clusterUpdate w (earlier x k) (x k) F) i +
        ∑ l, if k < l then G.column w x l (G.expectedResidual w (earlier x k) (x k) F) i else 0 := by
  have hzero := G.avoided_drift_zero w hw (earlier x k) (x k) F
    (fun W => if x i ∉ W then 1 else 0)
  have hpoint : (fun ω : E → Prop => if x k ∉ roots (G.openGraph ω) (earlier x k) then
      (if x i ∉ roots (G.openGraph ω) (earlier x k) then (1 : ℝ) else 0) *
        (F (component (G.openGraph ω) (x k)) -
          G.expectedCluster w (x k) F (roots (G.openGraph ω) (earlier x k))) else 0) =
      (fun ω => select (G.openGraph ω) x k i *
        (F (component (G.openGraph ω) (x k)) -
          G.expectedCluster w (x k) F (roots (G.openGraph ω) (earlier x k))) -
        ∑ l, if k < l then if first (G.openGraph ω) x k then
          select (G.openGraph ω) x l i *
            (G.expectedCluster w (x k) F (roots (G.openGraph ω) (earlier x k)) -
              F (component (G.openGraph ω) (x k))) else 0 else 0) := by
    funext ω
    by_cases hk : first (G.openGraph ω) x k
    · simp only [show x k ∉ roots (G.openGraph ω) (earlier x k) from hk,
        not_false_eq_true, ite_true]
      rw [select_truncation]
      simp only [hk, ite_true]
      have hsum : ∀ a : ℝ,
          (∑ l, if k < l then select (G.openGraph ω) x l i * a else 0) =
          (∑ l, if k < l then select (G.openGraph ω) x l i else 0) * a := by
        intro a
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l _
        split_ifs <;> simp
      rw [hsum]
      ring
    · have hk' : ¬ (x k ∉ roots (G.openGraph ω) (earlier x k)) := hk
      simp [hk', hk, select]
  rw [hpoint] at hzero
  erw [expect_sub, expect_sum] at hzero
  have hlater : (∑ l, expect w (fun ω => if k < l then if first (G.openGraph ω) x k then
          select (G.openGraph ω) x l i *
            (G.expectedCluster w (x k) F (roots (G.openGraph ω) (earlier x k)) -
              F (component (G.openGraph ω) (x k))) else 0 else 0)) =
      ∑ l, if k < l then G.column w x l (G.expectedResidual w (earlier x k) (x k) F) i else 0 := by
    apply Finset.sum_congr rfl
    intro l _
    by_cases hkl : k < l
    · simp only [hkl, ite_true]
      exact (G.column_later_residual w hw x hkl F i).symm
    · simp only [hkl, ite_false, expect_zero]
  erw [hlater] at hzero
  have hdiff : G.column w x k F i -
      G.column w x k (G.clusterUpdate w (earlier x k) (x k) F) i =
      expect w (fun ω => select (G.openGraph ω) x k i *
        (F (component (G.openGraph ω) (x k)) -
          G.expectedCluster w (x k) F (roots (G.openGraph ω) (earlier x k)))) := by
    rw [G.column_update w hw]
    unfold column
    erw [← expect_sub]
    congr 1
    funext ω
    ring
  exact sub_eq_iff_eq_add'.mp (hdiff.trans (sub_eq_zero.mp hzero))
end CriticalPercolation.BondGraph
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.ProductMeasure.FiniteMarkovAvg
section

namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
namespace CriticalPercolation.FiniteMarkov
variable {X : Type*} [Fintype X]
noncomputable def avg (μ : X → ℝ) (f : X → ℝ) : ℝ := ∑ x, μ x * f x
noncomputable def step (K : X → X → ℝ) (f : X → ℝ) (x : X) : ℝ := avg (K x) f
lemma avg_const (μ : X → ℝ) (c : ℝ) : avg μ (fun _ => c) = (∑ x, μ x) * c := by
  classical
  exact (Finset.sum_mul _ _ _).symm
lemma avg_mono {μ : X → ℝ} (hμ : ∀ x, 0 ≤ μ x) {f g : X → ℝ}
    (h : ∀ x, f x ≤ g x) : avg μ f ≤ avg μ g :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (hμ x)
lemma avg_stationary (K : X → X → ℝ) (μ : X → ℝ)
    (hstat : ∀ y, ∑ x, μ x * K x y = μ y) (f : X → ℝ) :
    avg μ (step K f) = avg μ f := by
  classical
  simp only [step, avg]
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hstat]
lemma avg_iterate (K : X → X → ℝ) (μ : X → ℝ)
    (hstat : ∀ y, ∑ x, μ x * K x y = μ y) (f : X → ℝ) (n : ℕ) :
    avg μ ((step K)^[n] f) = avg μ f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', avg_stationary K μ hstat, ih]
noncomputable def remainder (K : X → X → ℝ) (a : ℝ) (z x y : X) : ℝ := by
  classical
  exact K x y - if y = z then a else 0
omit [Fintype X] in
lemma remainder_nonneg {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
    {a : ℝ} {z : X} (haK : ∀ x, a ≤ K x z) (x y : X) :
    0 ≤ remainder K a z x y := by
  classical
  unfold remainder
  split_ifs with h
  · subst y
    exact sub_nonneg.mpr (haK x)
  · simpa using hK x y
lemma remainder_mass (K : X → X → ℝ) (hK : ∀ x, ∑ y, K x y = 1)
    (a : ℝ) (z x : X) : ∑ y, remainder K a z x y = 1 - a := by
  classical
  simp [remainder, Finset.sum_sub_distrib, hK]
lemma step_remainder (K : X → X → ℝ) (a : ℝ) (z : X) (f : X → ℝ) (x : X) :
    step K f x = a * f z + avg (remainder K a z x) f := by
  classical
  simp [step, avg, remainder, sub_mul, Finset.sum_sub_distrib, ite_mul]
lemma step_bounds {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
    (hmass : ∀ x, ∑ y, K x y = 1) {a : ℝ} {z : X}
    (haK : ∀ x, a ≤ K x z) {f : X → ℝ} {l u : ℝ}
    (hf : ∀ x, l ≤ f x ∧ f x ≤ u) (x : X) :
    a * f z + (1 - a) * l ≤ step K f x ∧
      step K f x ≤ a * f z + (1 - a) * u := by
  rw [step_remainder K a z]
  have hlo := avg_mono (remainder_nonneg hK haK x) (fun x => (hf x).1)
  have hup := avg_mono (remainder_nonneg hK haK x) (fun x => (hf x).2)
  rw [avg_const, remainder_mass K hmass] at hlo
  rw [avg_const, remainder_mass K hmass] at hup
  constructor <;> linarith
lemma iterate_bounds {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
    (hmass : ∀ x, ∑ y, K x y = 1) {a : ℝ} {z : X}
    (haK : ∀ x, a ≤ K x z) {f : X → ℝ} {l u : ℝ}
    (hf : ∀ x, l ≤ f x ∧ f x ≤ u) (n : ℕ) :
    ∃ l' u', (∀ x, l' ≤ (step K)^[n] f x ∧ (step K)^[n] f x ≤ u') ∧
      u' - l' = (1 - a)^n * (u-l) := by
  induction n with
  | zero => exact ⟨l, u, hf, by simp⟩
  | succ n ih =>
      obtain ⟨l', u', hb, hd⟩ := ih
      refine ⟨a * (step K)^[n] f z + (1-a)*l',
        a * (step K)^[n] f z + (1-a)*u', ?_, ?_⟩
      · intro x
        simpa only [Function.iterate_succ_apply'] using step_bounds hK hmass haK hb x
      · calc
          _ = (1-a) * (u'-l') := by ring
          _ = _ := by rw [hd, pow_succ]; ring
lemma iterate_distance {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
    (hmass : ∀ x, ∑ y, K x y = 1) {a : ℝ} {z : X}
    (haK : ∀ x, a ≤ K x z) (μ : X → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hμmass : ∑ x, μ x = 1)
    (hstat : ∀ y, ∑ x, μ x * K x y = μ y)
    {f : X → ℝ} {l u : ℝ} (hf : ∀ x, l ≤ f x ∧ f x ≤ u)
    (n : ℕ) (x : X) :
    |(step K)^[n] f x - avg μ f| ≤ (1-a)^n * (u-l) := by
  obtain ⟨l', u', hb, hd⟩ := iterate_bounds hK hmass haK hf n
  have hlo := avg_mono hμ (fun x => (hb x).1)
  have hup := avg_mono hμ (fun x => (hb x).2)
  rw [avg_const, hμmass, one_mul, avg_iterate K μ hstat] at hlo
  rw [avg_const, hμmass, one_mul, avg_iterate K μ hstat] at hup
  rw [← hd, abs_le]
  have := hb x
  constructor <;> linarith
lemma tendsto_iterate {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
    (hmass : ∀ x, ∑ y, K x y = 1) {a : ℝ} {z : X}
    (ha : 0 < a) (ha_one : a ≤ 1) (haK : ∀ x, a ≤ K x z)
    (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hμmass : ∑ x, μ x = 1)
    (hstat : ∀ y, ∑ x, μ x * K x y = μ y) (f : X → ℝ) (x : X) :
    Filter.Tendsto (fun n => (step K)^[n] f x) Filter.atTop (nhds (avg μ f)) := by
  classical
  let : Nonempty X := ⟨z⟩
  let l := Finset.univ.inf' Finset.univ_nonempty f
  let u := Finset.univ.sup' Finset.univ_nonempty f
  have hb : ∀ y, l ≤ f y ∧ f y ≤ u := by
    intro y
    exact ⟨Finset.inf'_le _ (Finset.mem_univ y), Finset.le_sup' _ (Finset.mem_univ y)⟩
  have hpow : Filter.Tendsto (fun n : ℕ => (1-a)^n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr ha_one) (by linarith)
  have hlim := hpow.mul_const (u-l)
  simp only [zero_mul] at hlim
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have he := (Metric.tendsto_atTop.mp hlim) ε hε
  obtain ⟨N, hN⟩ := he
  refine ⟨N, fun n hn => ?_⟩
  have hlt := hN n hn
  rw [Real.dist_eq, sub_zero] at hlt
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (iterate_distance hK hmass haK μ hμ hμmass hstat hb n x)
    (lt_of_le_of_lt (le_abs_self _) hlt)
end CriticalPercolation.FiniteMarkov
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Clusters.DeleteBot
section

namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CriticalPercolation.ClusterDeletion
variable {V : Type*}
@[simp] lemma delete_bot (U : Set V) : delete (⊥ : SimpleGraph V) U = ⊥ := by
  ext v w
  simp [delete]
@[simp] lemma component_bot (s : V) : component (⊥ : SimpleGraph V) s = {s} := by
  ext v
  simp [component, SimpleGraph.reachable_bot, eq_comm]
@[simp] lemma roots_bot (S : Set V) : roots (⊥ : SimpleGraph V) S = S := by
  ext v
  simp [roots, SimpleGraph.reachable_bot]
end CriticalPercolation.ClusterDeletion
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.ProductMeasure.DensityMulExpect
section

namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]
lemma density_mul_le_expect {w : E → A → ℝ} (hw : ∀ e a, 0 ≤ w e a)
    {f : (E → A) → ℝ} (hf : ∀ ω, 0 ≤ f ω) (ω : E → A) :
    density w ω * f ω ≤ expect w f := by
  classical
  exact Finset.single_le_sum (fun ω _ => mul_nonneg (density_nonneg hw ω) (hf ω))
    (Finset.mem_univ ω)
end CriticalPercolation.FiniteProduct
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.GraphGeometry.UpdateKernel
section

namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)
noncomputable def updateKernel (w : E → Prop → ℝ) (S : Set V) (s : V)
    (U Z : Set V) : ℝ :=
  G.clusterUpdate w S s (fun Y => if Y = Z then 1 else 0) U
lemma clusterUpdate_eq_sum (w : E → Prop → ℝ) (S : Set V) (s : V)
    (F : Set V → ℝ) (U : Set V) :
    G.clusterUpdate w S s F U = ∑ Z, G.updateKernel w S s U Z * F Z := by
  classical
  unfold updateKernel clusterUpdate expectedCluster
  simp_rw [← expect_mul_const, ← expect_sum]
  congr 1
  funext ω
  congr 1
  funext ω'
  simp
omit [Fintype V] in
lemma updateKernel_nonneg (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (S : Set V) (s : V) (U Z : Set V) : 0 ≤ G.updateKernel w S s U Z :=
  G.clusterUpdate_nonneg w hpos S s (fun _ => by split_ifs <;> norm_num) U
lemma updateKernel_mass (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (U : Set V) : ∑ Z, G.updateKernel w S s U Z = 1 := by
  have h := G.clusterUpdate_eq_sum w S s (fun _ => 1) U
  simpa only [clusterUpdate, expectedCluster, expect_const w hw, mul_one] using h.symm
omit [Fintype V] in
lemma allClosed_weight_le_kernel (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hpos : ∀ e b, 0 ≤ w e b) (S : Set V) (s : V) (U : Set V) :
    density w (fun _ => False) ≤ G.updateKernel w S s U {s} := by
  unfold updateKernel clusterUpdate expectedCluster
  rw [← expect_const w hw (density w (fun _ => False))]
  apply expect_mono hpos
  intro ω
  have h := density_mul_le_expect hpos
    (f := fun ω' => if component (delete (G.openGraph ω')
      (roots (delete (G.openGraph ω) U) S)) s = {s} then 1 else 0)
    (fun _ => by split_ifs <;> norm_num) (fun _ => False)
  simpa only [show (fun _ : E => False) = (∅ : Set E) from rfl,
    G.openGraph_empty, delete_bot, component_bot, ite_true, mul_one] using h
lemma avoidedAverage_eq_sum (w : E → Prop → ℝ) (S : Set V) (s : V)
    (F : Set V → ℝ) :
    G.avoidedAverage w S s F = ∑ U,
      G.avoidedAverage w S s (fun Z => if Z = U then 1 else 0) * F U := by
  classical
  unfold avoidedAverage
  simp_rw [← expect_mul_const, ← expect_sum]
  congr 1
  funext ω
  split_ifs <;> simp_all
noncomputable def avoidedLaw (w : E → Prop → ℝ) (S : Set V) (s : V) (U : Set V) : ℝ :=
  G.avoidedAverage w S s (fun Z => if Z = U then 1 else 0) /
    G.avoidedAverage w S s (fun _ => 1)
lemma avoidedLaw_avg (w : E → Prop → ℝ) (S : Set V) (s : V) (F : Set V → ℝ) :
    FiniteMarkov.avg (G.avoidedLaw w S s) F =
      G.avoidedAverage w S s F / G.avoidedAverage w S s (fun _ => 1) := by
  classical
  unfold FiniteMarkov.avg avoidedLaw
  simp only [div_mul_eq_mul_div, ← Finset.sum_div]
  rw [← G.avoidedAverage_eq_sum]
omit [Fintype V] in
lemma avoidedLaw_nonneg (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (S : Set V) (s : V) (U : Set V) : 0 ≤ G.avoidedLaw w S s U := by
  unfold avoidedLaw avoidedAverage
  apply div_nonneg <;> apply expect_nonneg hpos <;> intro ω <;> positivity
omit [Fintype V] in
lemma allClosed_weight_le_avoidance (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (S : Set V) (s : V) (hs : s ∉ S) :
    density w (fun _ => False) ≤ G.avoidedAverage w S s (fun _ => 1) := by
  unfold avoidedAverage
  have h := density_mul_le_expect hpos
    (f := fun ω => if s ∉ roots (G.openGraph ω) S then (1 : ℝ) else 0)
    (fun _ => by split_ifs <;> norm_num) (fun _ => False)
  simpa only [show (fun _ : E => False) = (∅ : Set E) from rfl,
    G.openGraph_empty, roots_bot, if_pos hs, mul_one] using h
omit [Fintype V] in
lemma avoidance_pos (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (S : Set V) (s : V) (hs : s ∉ S) :
    0 < G.avoidedAverage w S s (fun _ => 1) := by
  have hp : 0 < density w (fun _ => False) := Finset.prod_pos fun e _ => hclosed e
  exact hp.trans_le (G.allClosed_weight_le_avoidance w hpos S s hs)
lemma avoidedLaw_mass (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (S : Set V) (s : V) (hs : s ∉ S) :
    ∑ U, G.avoidedLaw w S s U = 1 := by
  have h := G.avoidedLaw_avg w S s (fun _ => 1)
  simpa only [FiniteMarkov.avg, mul_one, div_self (ne_of_gt (G.avoidance_pos w hpos hclosed S s hs))]
    using h
lemma avoidedLaw_stationary (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (Z : Set V) :
    ∑ U, G.avoidedLaw w S s U * G.updateKernel w S s U Z = G.avoidedLaw w S s Z := by
  change FiniteMarkov.avg (G.avoidedLaw w S s)
    (G.clusterUpdate w S s (fun Y => if Y = Z then 1 else 0)) = _
  rw [G.avoidedLaw_avg, G.clusterUpdate_stationary w hw]
  rfl
lemma tendsto_clusterUpdate (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hpos : ∀ e b, 0 ≤ w e b) (hclosed : ∀ e, 0 < w e False)
    (S : Set V) (s : V) (hs : s ∉ S) (F : Set V → ℝ) (U : Set V) :
    Filter.Tendsto (fun n => (G.clusterUpdate w S s)^[n] F U) Filter.atTop
      (nhds (G.avoidedAverage w S s F / G.avoidedAverage w S s (fun _ => 1))) := by
  have hstep : G.clusterUpdate w S s = FiniteMarkov.step (G.updateKernel w S s) := by
    funext f Z
    exact G.clusterUpdate_eq_sum w S s f Z
  have ha : 0 < density w (fun _ => False) := Finset.prod_pos fun e _ => hclosed e
  have haone : density w (fun _ => False) ≤ 1 := by
    have h := density_mul_le_expect hpos (f := fun _ => 1) (fun _ => by norm_num)
      (fun _ => False)
    simpa only [mul_one, expect_const w hw] using h
  rw [hstep, ← G.avoidedLaw_avg]
  exact FiniteMarkov.tendsto_iterate (G.updateKernel_nonneg w hpos S s)
    (G.updateKernel_mass w hw S s) ha haone
    (G.allClosed_weight_le_kernel w hw hpos S s) _ (G.avoidedLaw_nonneg w hpos S s)
    (G.avoidedLaw_mass w hpos hclosed S s hs) (G.avoidedLaw_stationary w hw S s) F U
end CriticalPercolation.BondGraph
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.LinearGroups.ClusterMatrix
section

namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical Matrix
variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)
noncomputable def clusterMatrix {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V) :
    Matrix (Fin n) (Fin n) ℝ := fun i k => G.column w x k (fun _ => 1) i
omit [Fintype V] in
lemma column_zero_of_lt {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
    {k i : Fin n} (hik : i < k) (F : Set V → ℝ) : G.column w x k F i = 0 := by
  unfold column
  simp only [select_zero_of_lt _ _ hik, zero_mul, expect_zero]
omit [Fintype V] in
lemma column_diag {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
    (k : Fin n) (F : Set V → ℝ) :
    G.column w x k F k = G.avoidedAverage w (earlier x k) (x k) F := by
  unfold column avoidedAverage
  simp only [select_diag, first]
  congr 1
  funext ω
  split_ifs <;> simp_all
omit [Fintype V] in
lemma clusterMatrix_lower {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V) :
    (G.clusterMatrix w x).IsLowerTriangular := by
  intro i k hik
  exact G.column_zero_of_lt w x hik _
omit [Fintype V] in
lemma clusterMatrix_det_pos {n : ℕ} (w : E → Prop → ℝ)
    (hpos : ∀ e b, 0 ≤ w e b) (hclosed : ∀ e, 0 < w e False)
    (x : Fin n → V) (hx : Function.Injective x) : 0 < (G.clusterMatrix w x).det := by
  rw [Matrix.det_of_isLowerTriangular _ (G.clusterMatrix_lower w x)]
  apply Finset.prod_pos
  intro k _
  change 0 < G.column w x k (fun _ => 1) k
  rw [G.column_diag]
  exact G.avoidance_pos w hpos hclosed _ _ (root_not_mem_earlier hx k)
noncomputable def inverseColumn {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
    (k : Fin n) (F : Set V → ℝ) : Fin n → ℝ :=
  (G.clusterMatrix w x)⁻¹ *ᵥ G.column w x k F
omit [Fintype V] in
lemma inverseColumn_const {n : ℕ} (w : E → Prop → ℝ)
    (hpos : ∀ e b, 0 ≤ w e b) (hclosed : ∀ e, 0 < w e False)
    (x : Fin n → V) (hx : Function.Injective x) (k : Fin n) (c : ℝ) :
    G.inverseColumn w x k (fun _ => c) = c • Pi.single k 1 := by
  have hc : G.column w x k (fun _ => c) = c • G.column w x k (fun _ => 1) := by
    funext i
    change expect w _ = c * expect w _
    rw [← expect_const_mul]
    congr 1
    funext ω
    ring
  have hunit : IsUnit (G.clusterMatrix w x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (G.clusterMatrix_det_pos w hpos hclosed x hx))
  unfold inverseColumn
  rw [hc, Matrix.mulVec_smul]
  congr 1
  have hcol : G.column w x k (fun _ => 1) = G.clusterMatrix w x *ᵥ Pi.single k 1 := by
    ext i
    simp [Matrix.mulVec_single, clusterMatrix]
  rw [hcol, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
lemma inverseColumn_decomposition {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (x : Fin n → V) (k : Fin n) (F : Set V → ℝ) :
    G.inverseColumn w x k F =
      G.inverseColumn w x k (G.clusterUpdate w (earlier x k) (x k) F) +
        ∑ l, if k < l then G.inverseColumn w x l
          (G.expectedResidual w (earlier x k) (x k) F) else 0 := by
  have hc : G.column w x k F =
      G.column w x k (G.clusterUpdate w (earlier x k) (x k) F) +
        ∑ l, if k < l then G.column w x l
          (G.expectedResidual w (earlier x k) (x k) F) else 0 := by
    ext i
    simpa only [Pi.add_apply, Finset.sum_apply, ite_apply, Pi.zero_apply] using
      G.column_decomposition w hw x k F i
  unfold inverseColumn
  rw [hc, Matrix.mulVec_add, Matrix.mulVec_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  split_ifs <;> simp
omit [Fintype V] in
lemma continuous_inverseColumn {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
    (k i : Fin n) : Continuous (fun F : Set V → ℝ => G.inverseColumn w x k F i) := by
  unfold inverseColumn Matrix.mulVec dotProduct column expect
  fun_prop
lemma inverseColumn_nonneg {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (x : Fin n → V) (hx : Function.Injective x)
    (k : Fin n) {F : Set V → ℝ} (hF : Monotone F) (hF0 : ∀ U, 0 ≤ F U) :
    ∀ i, 0 ≤ G.inverseColumn w x k F i := by
  induction k using WellFoundedGT.induction generalizing F with
  | ind k ih =>
    have hstep (f : Set V → ℝ) (hf : Monotone f) (i : Fin n) :
        G.inverseColumn w x k (G.clusterUpdate w (earlier x k) (x k) f) i ≤
          G.inverseColumn w x k f i := by
      have hd := congrFun (G.inverseColumn_decomposition w hw x k f) i
      simp only [Pi.add_apply, Finset.sum_apply, ite_apply, Pi.zero_apply] at hd
      have hr : 0 ≤ ∑ l, if k < l then G.inverseColumn w x l
          (G.expectedResidual w (earlier x k) (x k) f) i else 0 := by
        apply Finset.sum_nonneg
        intro l _
        split_ifs with hkl
        · exact ih l hkl (G.expectedResidual_monotone w hw hpos _ _ hf)
            (G.expectedResidual_nonneg w hw hpos _ _ hf) i
        · exact le_rfl
      linarith only [hd, hr]
    have hmono (j : ℕ) : Monotone ((G.clusterUpdate w (earlier x k) (x k))^[j] F) := by
      induction j with
      | zero => exact hF
      | succ j hj =>
        rw [Function.iterate_succ_apply']
        exact G.clusterUpdate_monotone w hpos _ _ hj
    have hbound (j : ℕ) (i : Fin n) :
        G.inverseColumn w x k ((G.clusterUpdate w (earlier x k) (x k))^[j] F) i ≤
          G.inverseColumn w x k F i := by
      induction j with
      | zero => exact le_rfl
      | succ j hj =>
        rw [Function.iterate_succ_apply']
        exact (hstep _ (hmono j) i).trans hj
    let m := G.avoidedAverage w (earlier x k) (x k) F /
      G.avoidedAverage w (earlier x k) (x k) (fun _ => 1)
    have hm : 0 ≤ m := by
      apply div_nonneg
      · unfold avoidedAverage
        apply expect_nonneg hpos
        intro ω
        split_ifs
        · exact le_rfl
        · exact hF0 _
      · exact le_of_lt (G.avoidance_pos w hpos hclosed _ _ (root_not_mem_earlier hx k))
    have hlim : Filter.Tendsto
        (fun j => (G.clusterUpdate w (earlier x k) (x k))^[j] F) Filter.atTop
        (nhds (fun _ => m)) :=
      tendsto_pi_nhds.mpr (fun U => G.tendsto_clusterUpdate w hw hpos hclosed _ _
        (root_not_mem_earlier hx k) F U)
    intro i
    have hi := (G.continuous_inverseColumn w x k i).tendsto (fun _ => m) |>.comp hlim
    have hb := le_of_tendsto hi (Filter.Eventually.of_forall (fun j => hbound j i))
    rw [G.inverseColumn_const w hpos hclosed x hx] at hb
    apply le_trans _ hb
    change 0 ≤ m * (Pi.single (M := fun _ : Fin n => ℝ) k 1 i)
    apply mul_nonneg hm
    by_cases hki : k = i <;> simp [hki]
end CriticalPercolation.BondGraph
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Clusters.HitOthers
section

namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CriticalPercolation.ClusterColumns
open scoped Classical
variable {V : Type*} {n : ℕ}
noncomputable def hitOthers (x : Fin n → V) (k : Fin n) (U : Set V) : ℝ :=
  if ∃ j, j ≠ k ∧ x j ∈ U then 1 else 0
lemma hitOthers_nonneg (x : Fin n → V) (k : Fin n) (U : Set V) :
    0 ≤ hitOthers x k U := by unfold hitOthers; positivity
lemma hitOthers_le_one (x : Fin n → V) (k : Fin n) (U : Set V) :
    hitOthers x k U ≤ 1 := by unfold hitOthers; split_ifs <;> norm_num
lemma hitOthers_monotone (x : Fin n → V) (k : Fin n) : Monotone (hitOthers x k) := by
  intro U W hUW
  unfold hitOthers
  split_ifs with hU hW hW
  · exact le_rfl
  · obtain ⟨j, hj, hjU⟩ := hU
    exact (hW ⟨j, hj, hUW hjU⟩).elim
  · norm_num
  · exact le_rfl
lemma hitOthers_singleton (x : Fin n → V) (hx : Function.Injective x) (k : Fin n) :
    hitOthers x k {x k} = 0 := by
  apply if_neg
  rintro ⟨j, hj, hjk⟩
  exact hj (hx hjk)
end CriticalPercolation.ClusterColumns
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.GraphGeometry.ColumnHitOthersOffdiag
section

namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical Matrix
variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)
omit [Fintype V] in
lemma column_hitOthers_offdiag {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
    (k i : Fin n) (hik : i ≠ k) :
    G.column w x k (hitOthers x k) i = G.column w x k (fun _ => 1) i := by
  unfold column
  congr 1
  funext ω
  by_cases hc : first (G.openGraph ω) x k ∧ x i ∈ component (G.openGraph ω) (x k)
  · have hh : ∃ j, j ≠ k ∧ x j ∈ component (G.openGraph ω) (x k) := ⟨i, hik, hc.2⟩
    simp [select, hitOthers, hc, hh]
  · simp [select, hc]
omit [Fintype V] in
lemma column_hitOthers_gap_pos {n : ℕ} (w : E → Prop → ℝ)
    (hpos : ∀ e b, 0 ≤ w e b) (hclosed : ∀ e, 0 < w e False)
    (x : Fin n → V) (hx : Function.Injective x) (k : Fin n) :
    0 < G.column w x k (fun _ => 1) k - G.column w x k (hitOthers x k) k := by
  have he : G.column w x k (fun _ => 1) k - G.column w x k (hitOthers x k) k =
      expect w (fun ω => select (G.openGraph ω) x k k *
        (1 - hitOthers x k (component (G.openGraph ω) (x k)))) := by
    unfold column
    erw [← expect_sub]
    congr 1
    funext ω
    ring
  rw [he]
  have hf (ω : E → Prop) : 0 ≤ select (G.openGraph ω) x k k *
      (1 - hitOthers x k (component (G.openGraph ω) (x k))) :=
    mul_nonneg (select_nonneg _ _ _ _) (sub_nonneg.mpr (hitOthers_le_one _ _ _))
  have hd := density_mul_le_expect hpos hf (fun _ => False)
  have hs : first (⊥ : SimpleGraph V) x k := by
    simpa only [first, roots_bot] using root_not_mem_earlier hx k
  simp only [show (fun _ : E => False) = (∅ : Set E) from rfl,
    G.openGraph_empty, component_bot, hitOthers_singleton x hx, sub_zero,
    select_diag, hs, ite_true, mul_one] at hd
  have hp : 0 < density w (∅ : Set E) := Finset.prod_pos (fun e _ => hclosed e)
  simpa only [select_diag] using hp.trans_le hd
lemma inverseMatrix_offdiag_nonpos {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (x : Fin n → V) (hx : Function.Injective x)
    (k i : Fin n) (hik : i ≠ k) : (G.clusterMatrix w x)⁻¹ i k ≤ 0 := by
  let a := G.column w x k (fun _ => 1) k - G.column w x k (hitOthers x k) k
  have ha : 0 < a := G.column_hitOthers_gap_pos w hpos hclosed x hx k
  have he : G.column w x k (fun _ => 1) =
      G.column w x k (hitOthers x k) + a • Pi.single k 1 := by
    ext j
    by_cases hj : j = k
    · subst j
      simp [a]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hj, mul_zero,
        add_zero]
      exact (G.column_hitOthers_offdiag w x k j hj).symm
  have he' := congrArg (fun v => (G.clusterMatrix w x)⁻¹ *ᵥ v) he
  change G.inverseColumn w x k (fun _ => 1) = _ at he'
  rw [G.inverseColumn_const w hpos hclosed x hx, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_single_one] at he'
  have he'' := congrFun he' i
  simp only [Pi.single_eq_of_ne hik, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.col_apply] at he''
  have hp := G.inverseColumn_nonneg w hw hpos hclosed x hx k
    (hitOthers_monotone x k) (hitOthers_nonneg x k) i
  change 0 ≤ ((G.clusterMatrix w x)⁻¹ *ᵥ G.column w x k (hitOthers x k)) i at hp
  nlinarith only [he'', hp, ha]
omit [Fintype V] in
lemma clusterMatrix_row_mass {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (x : Fin n → V) :
    G.clusterMatrix w x *ᵥ (fun _ => 1) = fun _ => 1 := by
  ext i
  change (∑ k, G.column w x k (fun _ => 1) i * 1) = 1
  simp only [mul_one, column]
  erw [← expect_sum]
  simpa only [mul_one, select_mass] using expect_const w hw 1
omit [Fintype V] in
lemma inverseMatrix_row_mass {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (x : Fin n → V) (hx : Function.Injective x) :
    (G.clusterMatrix w x)⁻¹ *ᵥ (fun _ => 1) = fun _ => 1 := by
  have h := congrArg (fun v => (G.clusterMatrix w x)⁻¹ *ᵥ v)
    (G.clusterMatrix_row_mass w hw x)
  have hu : IsUnit (G.clusterMatrix w x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (G.clusterMatrix_det_pos w hpos hclosed x hx))
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec] at h
  exact h.symm
omit [Fintype V] in
lemma clusterFunction_sum_columns {n : ℕ} (w : E → Prop → ℝ)
    (x : Fin n → V) (F : Set V → ℝ) :
    (fun i => expect w (fun ω => F (component (G.openGraph ω) (x i)))) =
      ∑ k, G.column w x k F := by
  ext i
  simp only [Finset.sum_apply, column]
  erw [← expect_sum]
  congr 1
  funext ω
  exact cluster_partition (G.openGraph ω) x F i
lemma inverse_clusterFunction_nonneg {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (x : Fin n → V) (hx : Function.Injective x)
    {F : Set V → ℝ} (hF : Monotone F) (hF0 : ∀ U, 0 ≤ F U) (i : Fin n) :
    0 ≤ ((G.clusterMatrix w x)⁻¹ *ᵥ
      (fun j => expect w (fun ω => F (component (G.openGraph ω) (x j))))) i := by
  rw [G.clusterFunction_sum_columns, Matrix.mulVec_sum, Finset.sum_apply]
  exact Finset.sum_nonneg (fun k _ => G.inverseColumn_nonneg w hw hpos hclosed x hx k hF hF0 i)
end CriticalPercolation.BondGraph
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.GraphGeometry.LastInverseDiagonal
section

namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical Matrix
variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)
omit [Fintype V] in
lemma last_inverse_diagonal {n : ℕ} (w : E → Prop → ℝ)
    (hpos : ∀ e b, 0 ≤ w e b) (hclosed : ∀ e, 0 < w e False)
    (x : Fin (n+1) → V) (hx : Function.Injective x) :
    G.avoidedAverage w (earlier x (Fin.last n)) (x (Fin.last n)) (fun _ => 1) *
      (G.clusterMatrix w x)⁻¹ (Fin.last n) (Fin.last n) = 1 := by
  have hu : IsUnit (G.clusterMatrix w x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (G.clusterMatrix_det_pos w hpos hclosed x hx))
  have h := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ =>
    M (Fin.last n) (Fin.last n)) (Matrix.nonsing_inv_mul (G.clusterMatrix w x) hu)
  simp only [Matrix.mul_apply, Matrix.one_apply_eq, Fin.sum_univ_castSucc,
    clusterMatrix, column_zero_of_lt _ _ _ (Fin.castSucc_lt_last _), mul_zero,
    Finset.sum_const_zero, zero_add, column_diag] at h
  simpa only [mul_comm] using h
lemma finite_cluster_relay {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (x : Fin (n+1) → V) (hx : Function.Injective x)
    {F : Set V → ℝ} (hF : Monotone F) (hF0 : ∀ U, 0 ≤ F U)
    (a : ℝ) (ha : ∀ j : Fin n, a ≤ expect w
      (fun ω => F (component (G.openGraph ω) (x j.castSucc)))) :
    (1 - G.avoidedAverage w (earlier x (Fin.last n)) (x (Fin.last n)) (fun _ => 1)) * a ≤
      expect w (fun ω => F (component (G.openGraph ω) (x (Fin.last n)))) := by
  let N := (G.clusterMatrix w x)⁻¹
  let y : Fin (n+1) → ℝ := fun j => expect w (fun ω => F (component (G.openGraph ω) (x j)))
  let d := G.avoidedAverage w (earlier x (Fin.last n)) (x (Fin.last n)) (fun _ => 1)
  have hd : 0 < d := G.avoidance_pos w hpos hclosed _ _ (root_not_mem_earlier hx _)
  have hdiag : d * N (Fin.last n) (Fin.last n) = 1 := G.last_inverse_diagonal w hpos hclosed x hx
  have hmass := congrFun (G.inverseMatrix_row_mass w hw hpos hclosed x hx) (Fin.last n)
  change ∑ j, N (Fin.last n) j * 1 = 1 at hmass
  simp only [mul_one, Fin.sum_univ_castSucc] at hmass
  have hzero := G.inverse_clusterFunction_nonneg w hw hpos hclosed x hx hF hF0 (Fin.last n)
  change 0 ≤ ∑ j, N (Fin.last n) j * y j at hzero
  rw [Fin.sum_univ_castSucc] at hzero
  have hs : (∑ j : Fin n, N (Fin.last n) j.castSucc * y j.castSucc) ≤
      (∑ j : Fin n, N (Fin.last n) j.castSucc) * a := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonpos_left (ha j)
      (G.inverseMatrix_offdiag_nonpos w hw hpos hclosed x hx j.castSucc (Fin.last n)
        (ne_of_gt (Fin.castSucc_lt_last j)))
  have hb : (N (Fin.last n) (Fin.last n) - 1) * a ≤
      N (Fin.last n) (Fin.last n) * y (Fin.last n) := by
    have hm : (∑ j : Fin n, N (Fin.last n) j.castSucc) =
        1 - N (Fin.last n) (Fin.last n) := by linarith only [hmass]
    rw [hm] at hs
    linarith only [hzero, hs]
  change (1-d)*a ≤ y (Fin.last n)
  calc
    (1-d)*a = (d * N (Fin.last n) (Fin.last n) - d) * a := by rw [hdiag]
    _ = d * ((N (Fin.last n) (Fin.last n) - 1) * a) := by ring
    _ ≤ d * (N (Fin.last n) (Fin.last n) * y (Fin.last n)) :=
      mul_le_mul_of_nonneg_left hb hd.le
    _ = y (Fin.last n) := by rw [← mul_assoc, hdiag, one_mul]
end CriticalPercolation.BondGraph
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.GraphGeometry.HittingSubAvoidance
section

namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)
omit [Fintype V] in
lemma hitting_eq_one_sub_avoidance (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (A : Set V) (s : V) :
    expect w (fun ω => hitValue A (component (G.openGraph ω) s)) =
      1 - G.avoidedAverage w A s (fun _ => 1) := by
  conv_rhs => lhs; rw [← expect_const w hw 1]
  unfold avoidedAverage
  erw [← expect_sub]
  congr 1
  funext ω
  simp only [hitValue, component_inter_nonempty_iff]
  split_ifs <;> norm_num
lemma finite_joint_gluing_list {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (x : Fin (n+1) → V) (hx : Function.Injective x)
    (T : Set V) (a : ℝ) (ha : ∀ j : Fin n, a ≤ expect w
      (fun ω => hitValue T (component (G.openGraph ω) (x j.castSucc)))) :
    expect w (fun ω => hitValue (earlier x (Fin.last n))
        (component (G.openGraph ω) (x (Fin.last n)))) * a ≤
      expect w (fun ω => jointHitValue (earlier x (Fin.last n)) T
        (component (G.openGraph ω) (x (Fin.last n)))) := by
  rw [G.hitting_eq_one_sub_avoidance w hw]
  apply G.finite_cluster_relay w hw hpos hclosed x hx
    (jointHitValue_monotone _ _) (jointHitValue_nonneg _ _)
  intro j
  have he : (fun ω : E → Prop => jointHitValue (earlier x (Fin.last n)) T
      (component (G.openGraph ω) (x j.castSucc))) =
      (fun ω => hitValue T (component (G.openGraph ω) (x j.castSucc))) := by
    funext ω
    apply jointHitValue_eq_hitValue
    exact ⟨x j.castSucc, component_self _ _, ⟨j.castSucc, Fin.castSucc_lt_last j, rfl⟩⟩
  rw [he]
  exact ha j
end CriticalPercolation.BondGraph
open Set MeasureTheory ProbabilityTheory
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.FiniteJointGluingStrict
section

namespace OAI
section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)
lemma finite_joint_gluing_strict (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (o : V) (A T : Set V) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ expect w
      (fun ω => hitValue T (component (G.openGraph ω) v))) :
    expect w (fun ω => hitValue A (component (G.openGraph ω) o)) * a ≤
      expect w (fun ω => jointHitValue A T (component (G.openGraph ω) o)) := by
  classical
  by_cases ho : o ∈ A
  · have hA (ω : Set E) : (component (G.openGraph ω) o ∩ A).Nonempty :=
      ⟨o, component_self _ _, ho⟩
    have hh : (fun ω : Set E => hitValue A (component (G.openGraph ω) o)) =
        (fun _ => (1 : ℝ)) := by
      funext ω
      exact if_pos (hA ω)
    have hj : (fun ω : Set E => jointHitValue A T (component (G.openGraph ω) o)) =
        (fun ω => hitValue T (component (G.openGraph ω) o)) := by
      funext ω
      exact jointHitValue_eq_hitValue (hA ω)
    erw [hh, hj, expect_const w hw, one_mul]
    exact ha o ho
  · let n := Fintype.card A
    let e : Fin n ≃ A := (Fintype.equivFin A).symm
    let f : Fin n → V := fun j => e j
    let x : Fin (n+1) → V := Fin.snoc f o
    have hx : Function.Injective x := by
      apply Fin.snoc_injective_iff.mpr
      refine ⟨?_, ?_⟩
      · exact Subtype.val_injective.comp e.injective
      · rintro ⟨j, hj⟩
        exact ho (hj ▸ (e j).property)
    have hlast : x (Fin.last n) = o := Fin.snoc_last _ _
    have hearlier : earlier x (Fin.last n) = A := by
      ext v
      constructor
      · rintro ⟨j, hj, h⟩
        rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
        · have he : x i.castSucc = f i := Fin.snoc_castSucc _ _ _
          exact h ▸ he ▸ (e i).property
        · exact (lt_irrefl _ hj).elim
      · intro hv
        let i := e.symm ⟨v, hv⟩
        refine ⟨i.castSucc, Fin.castSucc_lt_last i, ?_⟩
        dsimp only [x]
        rw [Fin.snoc_castSucc]
        exact congrArg Subtype.val (e.apply_symm_apply ⟨v, hv⟩)
    have h := G.finite_joint_gluing_list w hw hpos hclosed x hx T a (by
      intro j
      simpa only [x, Fin.snoc_castSucc] using ha (f j) (e j).property)
    rwa [hearlier, hlast] at h
end CriticalPercolation.BondGraph
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.ProductMeasure.ContinuousExpectWeights
section

namespace OAI
section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
namespace CriticalPercolation.FiniteProduct
variable {E B : Type*} [Fintype E] [Fintype B]
lemma continuous_expect_weights (f : (E → B) → ℝ) :
    Continuous (fun w : E → B → ℝ => expect w f) := by
  classical
  unfold expect density
  apply continuous_finsetSum
  intro ω _
  apply Continuous.mul _ continuous_const
  apply continuous_finsetProd
  intro e _
  exact (continuous_apply (ω e)).comp (continuous_apply e)
end CriticalPercolation.FiniteProduct
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.FiniteJointGluing
section

namespace OAI
section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)
lemma finite_joint_gluing (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (o : V) (A T : Set V) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ expect w
      (fun ω => hitValue T (component (G.openGraph ω) v))) :
    expect w (fun ω => hitValue A (component (G.openGraph ω) o)) * a ≤
      expect w (fun ω => jointHitValue A T (component (G.openGraph ω) o)) := by
  classical
  let w' : ℝ → E → Prop → ℝ := fun t e b => (1-t) * w e b + if b then 0 else t
  have hzero : w' 0 = w := by funext e b; simp [w']
  have hcont : Continuous w' := by
    apply continuous_pi
    intro e
    apply continuous_pi
    intro b
    dsimp only [w']
    split_ifs <;> fun_prop
  let err : ℝ → ℝ := fun t => ∑ v : V,
    |expect (w' t) (fun ω => hitValue T (component (G.openGraph ω) v)) -
      expect w (fun ω => hitValue T (component (G.openGraph ω) v))|
  have herr : Continuous err := by
    apply continuous_finsetSum
    intro v _
    exact (((continuous_expect_weights _).comp hcont).sub continuous_const).abs
  have herr0 : err 0 = 0 := by simp [err, hzero]
  have hbound (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
      expect (w' t) (fun ω => hitValue A (component (G.openGraph ω) o)) * (a-err t) ≤
        expect (w' t) (fun ω => jointHitValue A T (component (G.openGraph ω) o)) := by
    apply G.finite_joint_gluing_strict
    · intro e
      have hs := hw e
      simp only [Fintype.sum_Prop] at hs ⊢
      dsimp only [w']
      rw [if_pos True.intro, if_neg (by trivial : ¬ False)]
      nlinarith
    · intro e b
      have hm := mul_nonneg (sub_nonneg.mpr ht1) (hpos e b)
      dsimp only [w']
      apply add_nonneg hm
      split_ifs <;> linarith
    · intro e
      have hm := mul_nonneg (sub_nonneg.mpr ht1) (hpos e False)
      dsimp only [w']
      rw [if_neg (by trivial : ¬ False)]
      exact add_pos_of_nonneg_of_pos hm ht
    · intro v hv
      have hsingle :
          |expect (w' t) (fun ω => hitValue T (component (G.openGraph ω) v)) -
            expect w (fun ω => hitValue T (component (G.openGraph ω) v))| ≤ err t := by
        dsimp only [err]
        exact Finset.single_le_sum (f := fun u : V =>
          |expect (w' t) (fun ω => hitValue T (component (G.openGraph ω) u)) -
            expect w (fun ω => hitValue T (component (G.openGraph ω) u))|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ v)
      have hneg := (abs_le.mp hsingle).1
      linarith [ha v hv]
  have ht : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ)+1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hL := ((((continuous_expect_weights
    (fun ω => hitValue A (component (G.openGraph ω) o))).comp hcont).mul
      ((continuous_const (y := a)).sub herr)).tendsto 0).comp ht
  have hR := (((continuous_expect_weights
    (fun ω => jointHitValue A T (component (G.openGraph ω) o))).comp hcont).tendsto 0).comp ht
  have hh := le_of_tendsto_of_tendsto hL hR (Filter.Eventually.of_forall (fun n : ℕ =>
    hbound (1/((n : ℝ)+1)) (by positivity) (by
      apply (div_le_one (by positivity : (0 : ℝ) < n+1)).mpr
      have hn := Nat.cast_nonneg (α := ℝ) n
      linarith)))
  simpa only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply, hzero, herr0, sub_zero] using hh
end CriticalPercolation.BondGraph
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.GraphGeometry.RestrictVertices
section

namespace OAI
section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
open Set
open scoped Classical
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)
noncomputable def restrictVertices (U : Set V)
    (hU : ∀ e v, v ∈ G.ends e → v ∈ U) : BondGraph U E where
  ends e := (G.ends e).attachWith (hU e)
lemma restrictVertices_adj (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    (ω : Set E) (v w : U) :
    ((G.restrictVertices U hU).openGraph ω).Adj v w ↔
      (G.openGraph ω).Adj v.val w.val := by
  simp only [openGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_image]
  constructor
  · rintro ⟨⟨e, he, hend⟩, hne⟩
    refine ⟨⟨e, he, ?_⟩, fun h => hne (Subtype.ext h)⟩
    have h := congrArg (Sym2.map Subtype.val) hend
    simpa only [restrictVertices, Sym2.attachWith_map_subtypeVal, Sym2.map_mk] using h
  · rintro ⟨⟨e, he, hend⟩, hne⟩
    refine ⟨⟨e, he, ?_⟩, fun h => hne (congrArg Subtype.val h)⟩
    apply Sym2.map.injective Subtype.val_injective
    simp only [restrictVertices, Sym2.attachWith_map_subtypeVal, Sym2.map_mk]
    exact hend
lemma restrictVertices_graph (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    (ω : Set E) :
    (G.restrictVertices U hU).openGraph ω = (G.openGraph ω).induce U := by
  ext v w
  exact G.restrictVertices_adj U hU ω v w
lemma adj_mem_support (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    {ω : Set E} {v w : V} (h : (G.openGraph ω).Adj v w) : v ∈ U ∧ w ∈ U := by
  obtain ⟨⟨e, _, he⟩, _⟩ := (SimpleGraph.fromEdgeSet_adj _).mp h
  exact ⟨hU e v (by simp [he]), hU e w (by simp [he])⟩
lemma walk_support_subset (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    {ω : Set E} {v w : V} (p : (G.openGraph ω).Walk v w) (hv : v ∈ U) :
    ∀ u ∈ p.support, u ∈ U := by
  induction p with
  | nil => simpa
  | @cons v w z hvw p ih =>
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact hv
      · exact ih (G.adj_mem_support U hU hvw).2 u hu
lemma cluster_subset_support (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    {ω : Set E} {v : V} (hv : v ∈ U) : G.cluster ω v ⊆ U := by
  rintro w ⟨p⟩
  exact G.walk_support_subset U hU p hv w p.end_mem_support
lemma restrictVertices_reachable (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    (ω : Set E) (v w : U) :
    ((G.restrictVertices U hU).openGraph ω).Reachable v w ↔
      (G.openGraph ω).Reachable v.val w.val := by
  rw [G.restrictVertices_graph]
  constructor
  · intro h
    exact h.map (SimpleGraph.Embedding.induce U).toHom
  · rintro ⟨p⟩
    exact ⟨p.induce U (G.walk_support_subset U hU p v.property)⟩
open CriticalPercolation.ClusterColumns CriticalPercolation.ClusterDeletion
open CriticalPercolation.FiniteProduct
lemma restrictVertices_hit_iff (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    (ω : Set E) (v : U) (A : Set V) :
    (component ((G.restrictVertices U hU).openGraph ω) v ∩ (Subtype.val ⁻¹' A)).Nonempty ↔
      (component (G.openGraph ω) v.val ∩ A).Nonempty := by
  constructor
  · rintro ⟨w, hw, hA⟩
    exact ⟨w.val, (G.restrictVertices_reachable U hU ω v w).mp hw, hA⟩
  · rintro ⟨w, hw, hA⟩
    have hwU := G.cluster_subset_support U hU v.property hw
    exact ⟨⟨w, hwU⟩, (G.restrictVertices_reachable U hU ω v ⟨w, hwU⟩).mpr hw, hA⟩
lemma restrictVertices_hitValue (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    (ω : Set E) (v : U) (A : Set V) :
    hitValue (Subtype.val ⁻¹' A) (component ((G.restrictVertices U hU).openGraph ω) v) =
      hitValue A (component (G.openGraph ω) v.val) := by
  simp only [hitValue, G.restrictVertices_hit_iff]
lemma restrictVertices_jointHitValue (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    (ω : Set E) (v : U) (A T : Set V) :
    jointHitValue (Subtype.val ⁻¹' A) (Subtype.val ⁻¹' T)
        (component ((G.restrictVertices U hU).openGraph ω) v) =
      jointHitValue A T (component (G.openGraph ω) v.val) := by
  simp only [jointHitValue, G.restrictVertices_hit_iff]
lemma finite_edge_joint_gluing [Fintype E] (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (o : V) (A T : Set V) (hA : A.Finite) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ expect w
      (fun ω => hitValue T (component (G.openGraph ω) v))) :
    expect w (fun ω => hitValue A (component (G.openGraph ω) o)) * a ≤
      expect w (fun ω => jointHitValue A T (component (G.openGraph ω) o)) := by
  let U : Set V := insert o (A ∪ ⋃ e, (↑(G.ends e).toFinset : Set V))
  have hUf : U.Finite :=
    (hA.union (Set.finite_iUnion fun e => (G.ends e).toFinset.finite_toSet)).insert o
  let : Fintype U := hUf.fintype
  have hU : ∀ e v, v ∈ G.ends e → v ∈ U := by
    intro e v hv
    exact Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨e, by simpa using hv⟩))
  let R := G.restrictVertices U hU
  let o' : U := ⟨o, Set.mem_insert _ _⟩
  have h := R.finite_joint_gluing w hw hpos o' (Subtype.val ⁻¹' A)
    (Subtype.val ⁻¹' T) a (by
      intro v hv
      have heq : (fun ω : E → Prop =>
          hitValue (Subtype.val ⁻¹' T) (component (R.openGraph ω) v)) =
          (fun ω => hitValue T (component (G.openGraph ω) v.val)) := by
        funext ω
        exact G.restrictVertices_hitValue U hU ω v T
      rw [heq]
      exact ha v.val hv)
  have heq : (fun ω : E → Prop =>
      hitValue (Subtype.val ⁻¹' A) (component (R.openGraph ω) o')) =
      (fun ω => hitValue A (component (G.openGraph ω) o)) := by
    funext ω
    exact G.restrictVertices_hitValue U hU ω o' A
  have heq' : (fun ω : E → Prop =>
      jointHitValue (Subtype.val ⁻¹' A) (Subtype.val ⁻¹' T)
        (component (R.openGraph ω) o')) =
      (fun ω => jointHitValue A T (component (G.openGraph ω) o)) := by
    funext ω
    exact G.restrictVertices_jointHitValue U hU ω o' A T
  rwa [heq, heq'] at h
end CriticalPercolation.BondGraph
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.GraphGeometry.HitEvent
section

namespace OAI
section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
open Set
open scoped Classical
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns CriticalPercolation.BernoulliProduct
variable {V E : Type*} (G : BondGraph V E)
def hitEvent (o : V) (A : Set V) : Set (Set E) :=
  {ω | (G.cluster ω o ∩ A).Nonempty}
lemma measurableSet_hitEvent [Countable V] [Countable E] (o : V) (A : Set V) :
    MeasurableSet (G.hitEvent o A) := by
  exact (Measurable.exists fun v => (G.measurable_reachable o v).and measurable_const).setOf
lemma hitEvent_mono_edges (o : V) (A : Set V) {ω ω' : Set E} (h : ω ⊆ ω') :
    ω ∈ G.hitEvent o A → ω' ∈ G.hitEvent o A :=
  fun hω => hω.mono (Set.inter_subset_inter_left A (G.cluster_mono h o))
lemma hitEvent_mono_target (o : V) {A A' : Set V} (h : A ⊆ A') :
    G.hitEvent o A ⊆ G.hitEvent o A' :=
  fun _ hω => hω.mono (Set.inter_subset_inter_right _ h)
lemma expect_hit_eq_real [Fintype E] (q : E → unitInterval) (o : V) (A : Set V) :
    expect (fun e => bitWeight (q e))
      (fun ω => hitValue A (component (G.openGraph ω) o)) =
        (BernoulliProduct.law q).real (G.hitEvent o A) := by
  erw [← integral_law_eq_expect q (fun ω : Set E =>
    hitValue A (component (G.openGraph ω) o))]
  have he : (fun ω : Set E => hitValue A (component (G.openGraph ω) o)) =
      (G.hitEvent o A).indicator (1 : Set E → ℝ) := by
    funext ω
    simp only [hitValue, Set.indicator_apply, Pi.one_apply, hitEvent,
      component, cluster, Set.mem_ofPred_eq]
    rfl
  rw [he, integral_indicator_one (.of_discrete)]
lemma expect_jointHit_eq_real [Fintype E] (q : E → unitInterval) (o : V) (A T : Set V) :
    expect (fun e => bitWeight (q e))
      (fun ω => jointHitValue A T (component (G.openGraph ω) o)) =
        (BernoulliProduct.law q).real (G.hitEvent o A ∩ G.hitEvent o T) := by
  erw [← integral_law_eq_expect q (fun ω : Set E =>
    jointHitValue A T (component (G.openGraph ω) o))]
  have he : (fun ω : Set E => jointHitValue A T (component (G.openGraph ω) o)) =
      (G.hitEvent o A ∩ G.hitEvent o T).indicator (1 : Set E → ℝ) := by
    funext ω
    simp only [jointHitValue, Set.indicator_apply, Pi.one_apply, hitEvent,
      component, cluster, Set.mem_inter_iff, Set.mem_ofPred_eq]
    rfl
  rw [he, integral_indicator_one (.of_discrete)]
lemma finite_edge_joint_gluing_law [Fintype E] (q : E → unitInterval)
    (o : V) (A T : Set V) (hA : A.Finite) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ (BernoulliProduct.law q).real (G.hitEvent v T)) :
    (BernoulliProduct.law q).real (G.hitEvent o A) * a ≤
      (BernoulliProduct.law q).real (G.hitEvent o A ∩ G.hitEvent o T) := by
  rw [← G.expect_hit_eq_real, ← G.expect_jointHit_eq_real]
  apply G.finite_edge_joint_gluing _ (fun e => bitWeight_sum (q e))
    (fun e b => bitWeight_nonneg (q e) b) o A T hA a
  intro v hv
  rw [G.expect_hit_eq_real]
  exact ha v hv
def restrictEdges (s : Set E) : BondGraph V s where
  ends e := G.ends e
lemma restrictEdges_openGraph (s : Set E) (ω : Set E) :
    (G.restrictEdges s).openGraph (Subtype.val ⁻¹' ω) = G.openGraph (s ∩ ω) := by
  unfold openGraph restrictEdges
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff, Subtype.exists]
  constructor
  · rintro ⟨e, hs, hω, rfl⟩
    exact ⟨e, ⟨hs, hω⟩, rfl⟩
  · rintro ⟨e, ⟨hs, hω⟩, rfl⟩
    exact ⟨e, hs, hω, rfl⟩
lemma restrictEdges_hitEvent (s : Set E) (o : V) (A : Set V) :
    (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) ⁻¹'
        ((G.restrictEdges s).hitEvent o A) =
      {ω | s ∩ ω ∈ G.hitEvent o A} := by
  ext ω
  simp only [Set.mem_preimage, hitEvent, cluster, Set.mem_ofPred_eq,
    G.restrictEdges_openGraph]
lemma finite_subgraph_joint_gluing [Countable V] [Countable E]
    (q : E → unitInterval) (s : Set E) (hs : s.Finite)
    (o : V) (A T : Set V) (hA : A.Finite) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ (BernoulliProduct.law q).real {ω | s ∩ ω ∈ G.hitEvent v T}) :
    (BernoulliProduct.law q).real {ω | s ∩ ω ∈ G.hitEvent o A} * a ≤
      (BernoulliProduct.law q).real ({ω | s ∩ ω ∈ G.hitEvent o A} ∩
        {ω | s ∩ ω ∈ G.hitEvent o T}) := by
  let : Fintype s := hs.fintype
  have hmeas : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
    measurable_pi_lambda _ (fun edge => measurable_set_mem edge.val)
  have hr (B : Set (Set s)) (hB : MeasurableSet B) :
      (BernoulliProduct.law (fun e : s => q e)).real B =
        (BernoulliProduct.law q).real ((fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) ⁻¹' B) := by
    rw [← law_map_restrict q s]
    simp only [measureReal_def, Measure.map_apply hmeas hB]
  have h := (G.restrictEdges s).finite_edge_joint_gluing_law
    (fun e : s => q e) o A T hA a (by
      intro v hv
      rw [hr _ (.of_discrete), G.restrictEdges_hitEvent]
      exact ha v hv)
  rw [hr _ (.of_discrete), hr _ (.of_discrete), Set.preimage_inter,
    G.restrictEdges_hitEvent, G.restrictEdges_hitEvent] at h
  exact h
lemma finite_subset_exhaustion {X : Type*} {U S : Set X}
    (K : Set.FiniteExhaustion U) (hS : S.Finite) (hSU : S ⊆ U) :
    ∃ n, S ⊆ K n := by
  classical
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨0, Set.empty_subset _⟩
  | @insert x S hx hS ih =>
      obtain ⟨n, hn⟩ := ih (Set.Subset.trans (Set.subset_insert _ _) hSU)
      have hxU := hSU (Set.mem_insert x S)
      rw [← K.iUnion_eq, Set.mem_iUnion] at hxU
      obtain ⟨m, hm⟩ := hxU
      exact ⟨max m n, Set.insert_subset (K.mono (le_max_left _ _) hm)
        (Set.Subset.trans hn (K.mono (le_max_right _ _)))⟩
lemma hitEvent_exhaustion (K : Set.FiniteExhaustion (Set.univ : Set E))
    (o : V) (A : Set V) :
    (⋃ n, {ω | K n ∩ ω ∈ G.hitEvent o A}) = G.hitEvent o A := by
  ext ω
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
    exact G.hitEvent_mono_edges o A Set.inter_subset_right hn
  · rintro ⟨v, hv, hvA⟩
    obtain ⟨s, hs, hsω, hvs⟩ := G.mem_cluster_finite_witness hv
    obtain ⟨n, hn⟩ := finite_subset_exhaustion K hs (Set.subset_univ s)
    exact Set.mem_iUnion.mpr ⟨n, v, G.cluster_mono
      (Set.subset_inter hn hsω) o hvs, hvA⟩
lemma hitEvent_exhaustion_mono (K : Set.FiniteExhaustion (Set.univ : Set E))
    (o : V) (A : Set V) :
    Monotone (fun n => {ω | K n ∩ ω ∈ G.hitEvent o A}) := by
  intro m n h ω hω
  exact G.hitEvent_mono_edges o A (Set.inter_subset_inter_left _ (K.mono h)) hω
lemma tendsto_real_hitEvent_exhaustion [Countable E]
    (q : E → unitInterval) (K : Set.FiniteExhaustion (Set.univ : Set E))
    (o : V) (A : Set V) :
    Tendsto (fun n => (BernoulliProduct.law q).real {ω | K n ∩ ω ∈ G.hitEvent o A})
      atTop (𝓝 ((BernoulliProduct.law q).real (G.hitEvent o A))) := by
  have h := tendsto_measure_iUnion_atTop (μ := BernoulliProduct.law q)
    (G.hitEvent_exhaustion_mono K o A)
  rw [G.hitEvent_exhaustion K o A] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
lemma jointHitEvent_exhaustion (K : Set.FiniteExhaustion (Set.univ : Set E))
    (o : V) (A T : Set V) :
    (⋃ n, ({ω | K n ∩ ω ∈ G.hitEvent o A} ∩
      {ω | K n ∩ ω ∈ G.hitEvent o T})) = G.hitEvent o A ∩ G.hitEvent o T := by
  calc
    _ = (⋃ n, {ω | K n ∩ ω ∈ G.hitEvent o A}) ∩
        (⋃ n, {ω | K n ∩ ω ∈ G.hitEvent o T}) :=
      Set.iUnion_inter_of_monotone (G.hitEvent_exhaustion_mono K o A)
        (G.hitEvent_exhaustion_mono K o T)
    _ = _ := by rw [G.hitEvent_exhaustion K o A, G.hitEvent_exhaustion K o T]
lemma tendsto_real_jointHitEvent_exhaustion [Countable E]
    (q : E → unitInterval) (K : Set.FiniteExhaustion (Set.univ : Set E))
    (o : V) (A T : Set V) :
    Tendsto (fun n => (BernoulliProduct.law q).real
      ({ω | K n ∩ ω ∈ G.hitEvent o A} ∩ {ω | K n ∩ ω ∈ G.hitEvent o T}))
      atTop (𝓝 ((BernoulliProduct.law q).real (G.hitEvent o A ∩ G.hitEvent o T))) := by
  have h := tendsto_measure_iUnion_atTop (μ := BernoulliProduct.law q)
    ((G.hitEvent_exhaustion_mono K o A).inter (G.hitEvent_exhaustion_mono K o T))
  rw [G.jointHitEvent_exhaustion K o A T] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
lemma finite_sum_abs_sub_bound {X : Type*} [Fintype X] (f g : X → ℝ) (x : X) :
    |f x - g x| ≤ ∑ y, |f y - g y| := by
  exact Finset.single_le_sum (fun y _ => abs_nonneg (f y - g y)) (Finset.mem_univ x)
lemma countable_joint_gluing_finite [Countable V] [Countable E]
    (q : E → unitInterval) (o : V) (A T : Set V) (hA : A.Finite) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ (BernoulliProduct.law q).real (G.hitEvent v T)) :
    (BernoulliProduct.law q).real (G.hitEvent o A) * a ≤
      (BernoulliProduct.law q).real (G.hitEvent o A ∩ G.hitEvent o T) := by
  classical
  let : Fintype A := hA.fintype
  let K := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  let err : ℕ → ℝ := fun n => ∑ v : A,
    |(BernoulliProduct.law q).real {ω | K n ∩ ω ∈ G.hitEvent v T} -
      (BernoulliProduct.law q).real (G.hitEvent v T)|
  have herr : Tendsto err atTop (𝓝 0) := by
    have h : Tendsto err atTop (𝓝 (∑ _v : A, (0 : ℝ))) := by
      apply tendsto_finsetSum
      intro v _
      simpa using ((G.tendsto_real_hitEvent_exhaustion q K v T).sub_const
        ((BernoulliProduct.law q).real (G.hitEvent v T))).abs
    simpa using h
  have hbound (n : ℕ) :
      (BernoulliProduct.law q).real {ω | K n ∩ ω ∈ G.hitEvent o A} * (a - err n) ≤
      (BernoulliProduct.law q).real ({ω | K n ∩ ω ∈ G.hitEvent o A} ∩
        {ω | K n ∩ ω ∈ G.hitEvent o T}) := by
    refine G.finite_subgraph_joint_gluing q (K n) (K.finite n) o A T hA (a - err n) ?_
    intro v hv
    have hs : |(BernoulliProduct.law q).real {ω | K n ∩ ω ∈ G.hitEvent v T} -
        (BernoulliProduct.law q).real (G.hitEvent v T)| ≤ err n := by
      exact finite_sum_abs_sub_bound
        (fun u : A => (BernoulliProduct.law q).real {ω | K n ∩ ω ∈ G.hitEvent u T})
        (fun u : A => (BernoulliProduct.law q).real (G.hitEvent u T)) ⟨v, hv⟩
    have hneg := (abs_le.mp hs).1
    linarith [ha v hv]
  have hL := (G.tendsto_real_hitEvent_exhaustion q K o A).mul ((tendsto_const_nhds (x := a)).sub herr)
  have hR := G.tendsto_real_jointHitEvent_exhaustion q K o A T
  have h := le_of_tendsto_of_tendsto hL hR (Eventually.of_forall hbound)
  simpa only [sub_zero] using h
lemma hitEvent_iUnion {I : Type*} (o : V) (A : I → Set V) :
    G.hitEvent o (⋃ i, A i) = ⋃ i, G.hitEvent o (A i) := by
  ext ω
  simp only [hitEvent, Set.mem_ofPred_eq, Set.mem_iUnion, Set.nonempty_def,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨v, hv, i, hi⟩
    exact ⟨i, v, hv, hi⟩
  · rintro ⟨i, v, hv, hi⟩
    exact ⟨v, hv, i, hi⟩
theorem countable_joint_gluing [Countable V] [Countable E]
    (q : E → unitInterval) (o : V) (A T : Set V) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ (BernoulliProduct.law q).real (G.hitEvent v T)) :
    (BernoulliProduct.law q).real (G.hitEvent o A) * a ≤
      (BernoulliProduct.law q).real (G.hitEvent o A ∩ G.hitEvent o T) := by
  let K := (Set.to_countable A).finiteExhaustion
  have hKA (n : ℕ) : K n ⊆ A := by
    exact Set.Subset.trans (Set.subset_iUnion K n) (le_of_eq K.iUnion_eq)
  have hmono : Monotone (fun n => G.hitEvent o (K n)) := by
    intro m n h
    exact G.hitEvent_mono_target o (K.mono h)
  have hunion : (⋃ n, G.hitEvent o (K n)) = G.hitEvent o A := by
    rw [← G.hitEvent_iUnion, K.iUnion_eq]
  have hL : Tendsto (fun n => (BernoulliProduct.law q).real (G.hitEvent o (K n)))
      atTop (𝓝 ((BernoulliProduct.law q).real (G.hitEvent o A))) := by
    have h := tendsto_measure_iUnion_atTop (μ := BernoulliProduct.law q) hmono
    rw [hunion] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  have hR : Tendsto (fun n => (BernoulliProduct.law q).real
      (G.hitEvent o (K n) ∩ G.hitEvent o T))
      atTop (𝓝 ((BernoulliProduct.law q).real (G.hitEvent o A ∩ G.hitEvent o T))) := by
    have h := tendsto_measure_iUnion_atTop (μ := BernoulliProduct.law q)
      (hmono.inter (monotone_const (c := G.hitEvent o T)))
    rw [← Set.iUnion_inter, hunion] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  exact le_of_tendsto_of_tendsto (hL.mul_const a) hR
    (Eventually.of_forall fun n => G.countable_joint_gluing_finite q o (K n) T
      (K.finite n) a (fun v hv => ha v (hKA n hv)))
end CriticalPercolation.BondGraph
open Set MeasureTheory ProbabilityTheory
open scoped Classical
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.LevelContactGeometry
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
namespace CriticalPercolation.BondGraph
open BernoulliProduct
variable {V E : Type*} (G : BondGraph V E)
def exteriorCluster (π : V → ℤ) (j : ℤ) (o : V) (ω : Set E) : Set V :=
  G.cluster (ω∩G.inducedEdges {v | j ≤ π v}) o
def levelContacts (π : V → ℤ) (j : ℤ) (o : V) (ω : Set E) : Set V :=
  G.exteriorCluster π j o ω∩{v | π v=j}
def contactDrop (π : V → ℤ) (j : ℤ) (o : V) (ω : Set E) : Set E :=
  {e | ∃ v∈G.levelContacts π j o ω, ∃ w, π w<j ∧ G.ends e=s(v,w)}
lemma contactDrop_subset_incident (π : V → ℤ) (j : ℤ) (o : V) (ω : Set E) :
    G.contactDrop π j o ω ⊆ G.incidentEdges (G.levelContacts π j o ω) := by
  rintro e ⟨v,hv,w,hw,he⟩
  exact ⟨v,hv,by rw [he]; simp⟩
lemma contactDrop_disjoint_exterior (π : V → ℤ) (j : ℤ) (o : V) (ω : Set E) :
    Disjoint (G.contactDrop π j o ω) (G.inducedEdges {v | j ≤ π v}) := by
  apply Set.disjoint_left.mpr
  rintro e ⟨v,hv,w,hw,he⟩ he'
  exact (not_le.mpr hw) (he' w (by rw [he]; simp))
lemma exteriorCluster_subset_level (π : V → ℤ) (j : ℤ) (o : V)
    (ho : j ≤ π o) (ω : Set E) : G.exteriorCluster π j o ω ⊆ {v | j ≤ π v} := by
  intro v hv
  have hc : ∀ ⦃x y⦄, x∈{v | j ≤ π v} →
      (G.openGraph (ω∩G.inducedEdges {v | j ≤ π v})).Adj x y → y∈{v | j ≤ π v} := by
    intro x y hx hxy
    obtain ⟨⟨e,he,hend⟩,_⟩ := hxy
    exact he.2 y (by rw [hend]; simp)
  exact ClusterDeletion.reachable_mem_of_closed hc ho hv
lemma cluster_eq_exterior_of_drop_closed (π : V → ℤ) (j : ℤ) (o : V)
    (ho : j ≤ π o)
    (hcross : ∀ e v w, G.ends e=s(v,w) → j ≤ π v → π w<j → π v=j)
    (ω : Set E) (hclosed : Disjoint (G.contactDrop π j o ω) ω) :
    G.cluster ω o=G.exteriorCluster π j o ω := by
  apply Set.Subset.antisymm
  · intro v hv
    have hc : ∀ ⦃x y⦄, x∈G.exteriorCluster π j o ω →
        (G.openGraph ω).Adj x y → y∈G.exteriorCluster π j o ω := by
      intro x y hx hxy
      obtain ⟨⟨e,he,hend⟩,hne⟩ := hxy
      have hxj := G.exteriorCluster_subset_level π j o ho ω hx
      by_cases hy : j ≤ π y
      · apply hx.trans
        apply SimpleGraph.Adj.reachable
        refine ⟨⟨e,⟨he,?_⟩,hend⟩,hne⟩
        intro z hz
        rw [hend] at hz
        rcases Sym2.mem_iff.mp hz with rfl|rfl
        · exact hxj
        · exact hy
      · have hy' := lt_of_not_ge hy
        exact False.elim (Set.disjoint_left.mp hclosed
          ⟨x,⟨hx,hcross e x y hend hxj hy'⟩,y,hy',hend⟩ he)
    exact ClusterDeletion.reachable_mem_of_closed hc (SimpleGraph.Reachable.refl o) hv
  · exact G.cluster_mono Set.inter_subset_left o
def minimumLevel (π : V → ℤ) (o : V) (j : ℤ) : Set (Set E) :=
  G.hitEvent o {v | π v=j}\G.hitEvent o {v | π v<j}
lemma minimumLevel_of_drop_closed (π : V → ℤ) (j : ℤ) (o : V)
    (ho : j ≤ π o)
    (hcross : ∀ e v w, G.ends e=s(v,w) → j ≤ π v → π w<j → π v=j)
    (ω : Set E) (hcontact : (G.levelContacts π j o ω).Nonempty)
    (hclosed : Disjoint (G.contactDrop π j o ω) ω) :
    ω∈G.minimumLevel π o j := by
  have he := G.cluster_eq_exterior_of_drop_closed π j o ho hcross ω hclosed
  constructor
  · obtain ⟨v,hv,hj⟩ := hcontact
    exact ⟨v,he.symm ▸ hv,hj⟩
  · rintro ⟨v,hv,hj⟩
    have hlt : π v < j := hj
    have hle : j ≤ π v := G.exteriorCluster_subset_level π j o ho ω (he ▸ hv)
    omega
lemma minimumLevel_pairwiseDisjoint (π : V → ℤ) (o : V) :
    Pairwise (fun i j => Disjoint (G.minimumLevel π o i) (G.minimumLevel π o j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro ω ⟨⟨v,hv,hvi⟩,hnoti⟩ ⟨⟨w,hw,hwj⟩,hnotj⟩
  rcases lt_or_gt_of_ne hij with hlt|hgt
  · exact hnotj ⟨v,hv,by change π v < j; rw [hvi]; exact hlt⟩
  · exact hnoti ⟨w,hw,by change π w < i; rw [hwj]; exact hgt⟩
lemma measurableSet_minimumLevel [Countable V] [Countable E] (π : V → ℤ) (o : V) (j : ℤ) :
    MeasurableSet (G.minimumLevel π o j) :=
  (G.measurableSet_hitEvent o _).diff (G.measurableSet_hitEvent o _)
end CriticalPercolation.BondGraph
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.ProductMeasure.LevelContactMeasurability
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
namespace CriticalPercolation
def finiteSetChoice {E : Type*} (S : Set E) : Finset E :=
  if h : S.Finite then h.toFinset else ∅
lemma finiteSetChoice_coe {E : Type*} {S : Set E} (hS : S.Finite) :
    (finiteSetChoice S : Set E)=S := by simp [finiteSetChoice,hS]
lemma finiteSetChoice_eq_iff {E : Type*} (S : Set E) (U : Finset E) :
    finiteSetChoice S=U ↔ S=(U : Set E) ∨ (¬S.Finite ∧ U=∅) := by
  by_cases hS : S.Finite
  · have hh : finiteSetChoice S=U ↔ S=(U : Set E) := by
      calc
        finiteSetChoice S=U ↔ (finiteSetChoice S : Set E)=(U : Set E) := Finset.coe_inj.symm
        _ ↔ S=(U : Set E) := by rw [finiteSetChoice_coe hS]
    simpa [hS] using hh
  · have hne : S≠(U : Set E) := fun h => hS (h ▸ U.finite_toSet)
    simp [finiteSetChoice,hS,hne,eq_comm]
lemma measurableSet_set_eq_const {Ω E : Type*} {m : MeasurableSpace Ω} [Countable E]
    (S : Ω → Set E) (hS : @Measurable Ω (Set E) m inferInstance S) (U : Set E) :
    MeasurableSet[m] {ω | S ω=U} := by
  let : MeasurableSpace Ω := m
  have he : {ω | S ω=U}={ω | ∀ e, e∈S ω ↔ e∈U} := by
    ext ω
    exact Set.ext_iff
  rw [he]
  exact (Measurable.forall (fun e => ((measurable_pi_apply e).comp hS).iff measurable_const)).setOf
lemma measurableSet_finiteSetChoice {Ω E : Type*} [MeasurableSpace Ω] [Countable E]
    (S : Ω → Set E) (hS : Measurable S) (U : Finset E) :
    MeasurableSet {ω | finiteSetChoice (S ω)=U} := by
  have hmfinite : MeasurableSet {ω | (S ω).Finite} := by
    have he : {ω | (S ω).Finite}=⋃ F : Finset E, {ω | S ω=(F : Set E)} := by
      ext ω
      simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
      exact ⟨fun h => ⟨h.toFinset,h.coe_toFinset.symm⟩,
        fun ⟨F,hF⟩ => hF ▸ F.finite_toSet⟩
    rw [he]
    exact MeasurableSet.iUnion (fun F => measurableSet_set_eq_const S hS _)
  simp_rw [finiteSetChoice_eq_iff]
  exact (measurableSet_set_eq_const S hS _).union
    (hmfinite.compl.inter (MeasurableSet.const _))
namespace BernoulliProduct
variable {E : Type*}
lemma measurable_inter_block (X : Set E) :
    @Measurable (Set E) (Set E) (blockSigma X) inferInstance (fun ω => ω∩X) := by
  have hh := measurable_forceOn_block Xᶜ (∅ : Set E)
  rw [compl_compl] at hh
  have he : forceOn Xᶜ (∅ : Set E)=(fun ω : Set E => ω∩X) := by
    unfold forceOn
    funext configuration
    apply Set.ext
    intro edge
    rw [Set.mem_inter_iff]
    simp only [Membership.mem, Set.Mem]
    split_ifs with hedge
    · exact ⟨False.elim, fun hmem => hedge hmem.2⟩
    · exact ⟨fun hmem => ⟨hmem, not_not.mp hedge⟩, And.left⟩
  rw [he] at hh
  exact hh
end BernoulliProduct
namespace BondGraph
open BernoulliProduct
variable {V E : Type*} (G : BondGraph V E)
lemma incident_ncard_le (S : Set V) (hS : S.Finite)
    (D : ℕ) (hD : ∀ v∈S, (G.incidentEdges {v}).ncard ≤ D) :
    (G.incidentEdges S).ncard ≤ S.ncard*D := by
  have he : G.incidentEdges S=⋃ v∈hS.toFinset, G.incidentEdges {v} := by
    ext e
    simp [incidentEdges]
  rw [he]
  calc
    _ ≤ ∑ v∈hS.toFinset, (G.incidentEdges {v}).ncard :=
      Finset.set_ncard_biUnion_le hS.toFinset _
    _ ≤ ∑ _v∈hS.toFinset, D := Finset.sum_le_sum (fun v hv => hD v (hS.mem_toFinset.mp hv))
    _ = _ := by simp [Set.ncard_eq_toFinset_card S hS]
lemma finite_contactDrop (hlocal : G.LocallyFinite) (π : V → ℤ) (j : ℤ) (o : V) (ω : Set E)
    (hS : (G.levelContacts π j o ω).Finite) : (G.contactDrop π j o ω).Finite :=
  (G.finite_incident hlocal hS).subset (G.contactDrop_subset_incident π j o ω)
lemma contactDrop_ncard_le (hlocal : G.LocallyFinite) (π : V → ℤ) (j : ℤ) (o : V) (ω : Set E)
    (hS : (G.levelContacts π j o ω).Finite) (D : ℕ)
    (hD : ∀ v∈G.levelContacts π j o ω, (G.incidentEdges {v}).ncard ≤ D) :
    (G.contactDrop π j o ω).ncard ≤ (G.levelContacts π j o ω).ncard*D :=
  (Set.ncard_le_ncard (G.contactDrop_subset_incident π j o ω) (G.finite_incident hlocal hS)).trans
    (G.incident_ncard_le _ hS D hD)
variable [Countable V] [Countable E]
lemma measurable_exteriorCluster (π : V → ℤ) (j : ℤ) (o : V) :
    @Measurable (Set E) (Set V) (blockSigma (G.inducedEdges {v | j ≤ π v})) inferInstance
      (G.exteriorCluster π j o) :=
  (G.measurable_cluster o).comp (measurable_inter_block _)
lemma measurable_levelContacts (π : V → ℤ) (j : ℤ) (o : V) :
    @Measurable (Set E) (Set V) (blockSigma (G.inducedEdges {v | j ≤ π v})) inferInstance
      (G.levelContacts π j o) := by
  refine @measurable_pi_lambda (Set E) V (fun _ => Prop)
    (blockSigma (G.inducedEdges {v | j ≤ π v})) (fun _ => inferInstance) _ ?_
  intro v
  exact @Measurable.and (Set E) (blockSigma (G.inducedEdges {v | j ≤ π v})) _ _
    ((measurable_pi_apply v).comp (G.measurable_exteriorCluster π j o)) measurable_const
lemma measurable_contactDrop (π : V → ℤ) (j : ℤ) (o : V) :
    @Measurable (Set E) (Set E) (blockSigma (G.inducedEdges {v | j ≤ π v})) inferInstance
      (G.contactDrop π j o) := by
  refine @measurable_pi_lambda (Set E) E (fun _ => Prop)
    (blockSigma (G.inducedEdges {v | j ≤ π v})) (fun _ => inferInstance) _ ?_
  intro e
  exact @Measurable.exists (Set E) V (blockSigma (G.inducedEdges {v | j ≤ π v})) _ _ (fun v =>
    @Measurable.and (Set E) (blockSigma (G.inducedEdges {v | j ≤ π v})) _ _
      ((measurable_pi_apply v).comp (G.measurable_levelContacts π j o)) measurable_const)
def fewContacts (π : V → ℤ) (j : ℤ) (o : V) (k : ℕ) : Set (Set E) :=
  {ω | ∃ U : Finset V, G.levelContacts π j o ω=(U : Set V) ∧ U.Nonempty ∧ U.card<k}
lemma measurableSet_fewContacts (π : V → ℤ) (j : ℤ) (o : V) (k : ℕ) :
    MeasurableSet[blockSigma (G.inducedEdges {v | j ≤ π v})] (G.fewContacts π j o k) := by
  have he : G.fewContacts π j o k=⋃ U : Finset V,
      ({ω | G.levelContacts π j o ω=(U : Set V)}∩{_ω | U.Nonempty ∧ U.card<k}) := by
    ext ω
    simp [fewContacts]
  rw [he]
  exact MeasurableSet.iUnion (fun U =>
    (measurableSet_set_eq_const _ (G.measurable_levelContacts π j o) (U : Set V)).inter
      (MeasurableSet.const _))
omit [Countable V] [Countable E] in
lemma fewContacts_finite (π : V → ℤ) (j : ℤ) (o : V) (k : ℕ) (ω : Set E)
    (hω : ω∈G.fewContacts π j o k) :
    (G.levelContacts π j o ω).Finite ∧ (G.levelContacts π j o ω).Nonempty ∧
      (G.levelContacts π j o ω).ncard<k := by
  obtain ⟨U,hU,hne,hcard⟩ := hω
  rw [hU]
  exact ⟨U.finite_toSet,hne,by simpa using hcard⟩
end BondGraph
end CriticalPercolation
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Criticality.FiniteEnergy
section

namespace OAI
section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}
lemma law_coordinate (q : E → unitInterval) (e : E) (b : Prop) :
    law q {ω : Set E | (e ∈ ω) = b} = bitMeasure (q e) {b} := by
  rw [law_eq_infinitePi]
  have h := congrArg (fun μ : Measure Prop => μ {b})
    (Measure.infinitePi_map_eval (fun e => bitMeasure (q e)) e)
  rw [Measure.map_apply (measurable_pi_apply e) (MeasurableSet.singleton b)] at h
  exact h
end CriticalPercolation.BernoulliProduct
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Criticality.BlockIndependence
section

namespace OAI
section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
namespace CriticalPercolation.BernoulliProduct
variable {E I : Type*}
lemma blockSigma_mono {S T : Set E} (h : S ⊆ T) : blockSigma S ≤ blockSigma T := by
  apply iSup₂_le
  intro e he
  exact le_iSup_of_le e (le_iSup_of_le (h he) le_rfl)
lemma independent_disjoint_blocks (q : E → unitInterval) (S T : Set E)
    (h : Disjoint S T) : Indep (blockSigma S) (blockSigma T) (law q) :=
  indep_iSup_of_disjoint coordinateSigma_le (independent_coordinates q) h
theorem independent_block_family (q : E → unitInterval) (S : I → Set E)
    (hS : Pairwise (fun i j => Disjoint (S i) (S j))) :
    iIndep (fun i => blockSigma (S i)) (law q) := by
  apply (iIndep_iff _ _).mpr
  intro t
  induction t using Finset.induction_on with
  | empty => intro f hf; simp
  | @insert i t hi ih =>
    intro f hf
    let T := ⋃ j ∈ t, S j
    have hj : ∀ j ∈ t, blockSigma (S j) ≤ blockSigma T := by
      intro j hj
      exact blockSigma_mono (fun e he => Set.mem_iUnion₂.mpr ⟨j,hj,he⟩)
    have hm : MeasurableSet[blockSigma T] (⋂ j ∈ t, f j) := by
      apply MeasurableSet.biInter t.finite_toSet.countable
      intro j hjt
      exact hj j hjt _ (hf j (Finset.mem_insert_of_mem hjt))
    have hdis : Disjoint (S i) T := by
      apply Set.disjoint_left.mpr
      intro e hei heT
      obtain ⟨j,hjt,hje⟩ := Set.mem_iUnion₂.mp heT
      exact Set.disjoint_left.mp (hS (by intro h; subst j; exact hi hjt)) hei hje
    have hmuli := ((independent_disjoint_blocks q (S i) T hdis).indepSet_of_measurableSet
      (hf i (Finset.mem_insert_self i t)) hm).measure_inter_eq_mul
    rw [Finset.set_biInter_insert,Finset.prod_insert hi,hmuli]
    rw [ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]
def closedBlock (S : Set E) : Set (Set E) := {ω | Disjoint S ω}
lemma measurableSet_closed_coordinate (e : E) :
    MeasurableSet[coordinateSigma e] {ω : Set E | e ∉ ω} := by
  refine ⟨{False},MeasurableSet.singleton _,?_⟩
  ext ω
  simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_ofPred_eq]
  constructor
  · intro h hp
    exact Eq.mp h hp
  · intro h
    exact propext (iff_false_intro h)
lemma measurableSet_closedBlock (S : Set E) (hS : S.Countable) :
    MeasurableSet[blockSigma S] (closedBlock S) := by
  have heq : closedBlock S = ⋂ e ∈ S, {ω : Set E | e ∉ ω} := by
    ext ω
    simp only [closedBlock,Set.mem_ofPred_eq,Set.mem_iInter,Set.disjoint_left]
  rw [heq]
  apply MeasurableSet.biInter hS
  intro e he
  exact (le_iSup_of_le e (le_iSup_of_le he le_rfl) : coordinateSigma e ≤ blockSigma S)
    _ (measurableSet_closed_coordinate e)
lemma law_closedBlock (q : E → unitInterval) (S : Set E) (hS : S.Finite) :
    law q (closedBlock S) = ∏ e ∈ hS.toFinset, bitMeasure (q e) {False} := by
  have heq : closedBlock S = ⋂ e ∈ hS.toFinset, {ω : Set E | (e ∈ ω) = False} := by
    ext ω
    simp only [closedBlock,Set.mem_ofPred_eq,Set.mem_iInter,Set.disjoint_left,
      Set.Finite.mem_toFinset]
    constructor
    · intro h e he
      exact propext (iff_false_intro (h he))
    · intro h e he hp
      exact Eq.mp (h e he) hp
  rw [heq,(independent_coordinates q).meas_biInter]
  · exact Finset.prod_congr rfl (fun e _ => law_coordinate q e False)
  · intro e _
    exact ⟨{False},MeasurableSet.singleton _,rfl⟩
end CriticalPercolation.BernoulliProduct
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.ConditionalGluing
section

namespace OAI
section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.BondGraph
open CriticalPercolation.BernoulliProduct
variable {V E : Type*} (G : BondGraph V E)
lemma countable_gluing_failure [Countable V] [Countable E]
    (q : E → unitInterval) (o : V) (A T : Set V) (lam : ℝ)
    (ha : ∀ v∈A, 1-lam ≤ (BernoulliProduct.law q).real (G.hitEvent v T)) :
    (BernoulliProduct.law q).real (G.hitEvent o A \ G.hitEvent o T) ≤
      lam * (BernoulliProduct.law q).real (G.hitEvent o A) := by
  have h := G.countable_joint_gluing q o A T (1-lam) ha
  have he := measureReal_sdiff_add_inter (μ := BernoulliProduct.law q)
    (s := G.hitEvent o A) (G.measurableSet_hitEvent o T)
  nlinarith
lemma countable_gluing_failure_le [Countable V] [Countable E]
    (q : E → unitInterval) (o : V) (A T : Set V) (lam : ℝ) (hlam : 0≤lam)
    (ha : ∀ v∈A, 1-lam ≤ (BernoulliProduct.law q).real (G.hitEvent v T)) :
    (BernoulliProduct.law q).real (G.hitEvent o A \ G.hitEvent o T) ≤ lam := by
  have h := G.countable_gluing_failure q o A T lam ha
  have ht : (BernoulliProduct.law q).real (G.hitEvent o A)≤1 := measureReal_le_one
  nlinarith
lemma measurableSet_randomHit [Countable V] [Countable E]
    (o : V) (A : Set E → Set V)
    (hA : ∀ v, MeasurableSet {ω : Set E | v∈A ω}) :
    MeasurableSet {ω : Set E | ω∈G.hitEvent o (A ω)} := by
  have he : {ω : Set E | ω∈G.hitEvent o (A ω)} =
      ⋃ v : V, ({ω : Set E | (G.openGraph ω).Reachable o v}∩{ω | v∈A ω}) := by
    ext ω
    simp only [hitEvent,cluster,Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_inter_iff,
      Set.Nonempty]
  rw [he]
  exact MeasurableSet.iUnion fun v => (G.measurable_reachable o v).setOf.inter (hA v)
theorem random_relay_gluing [Countable V] [Countable E]
    (q : E → unitInterval) (S : Set E) (o : V) (A : Set E → Set V) (T : Set V)
    (hA : ∀ v, MeasurableSet[blockSigma S] {σ : Set E | v∈A σ})
    (lam : ℝ) (hlam : 0≤lam)
    (ha : ∀ σ v, v∈A σ → 1-lam ≤
      (BernoulliProduct.law (pinnedParameters q S σ)).real (G.hitEvent v T)) :
    (BernoulliProduct.law q).real
      {ω : Set E | ω∈G.hitEvent o (A ω) ∧ ω∉G.hitEvent o T} ≤ lam := by
  let F := {ω : Set E | ω∈G.hitEvent o (A ω) ∧ ω∉G.hitEvent o T}
  have hmF : MeasurableSet F :=
    (G.measurableSet_randomHit o A (fun v => (blockSigma_le S) _ (hA v))).inter
      (G.measurableSet_hitEvent o T).compl
  have hpin (σ : Set E) : blockProbability q S F σ =
      BernoulliProduct.law (pinnedParameters q S σ)
        (G.hitEvent o (A σ) \ G.hitEvent o T) := by
    rw [← forceOn_map_law,Measure.map_apply (measurable_forceOn S σ)
      ((G.measurableSet_hitEvent o _).diff (G.measurableSet_hitEvent o T))]
    unfold blockProbability
    congr 1
    ext ω
    have hfixed : A (forceOn S σ ω)=A σ := by
      ext v
      exact block_event_forceOn S {τ : Set E | v∈A τ} (hA v) σ ω
    change (forceOn S σ ω∈G.hitEvent o (A (forceOn S σ ω)) ∧
      forceOn S σ ω∉G.hitEvent o T) ↔
        (forceOn S σ ω∈G.hitEvent o (A σ) ∧ forceOn S σ ω∉G.hitEvent o T)
    rw [hfixed]
  have hb (σ : Set E) : blockProbability q S F σ ≤ ENNReal.ofReal lam := by
    rw [hpin]
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hlam]
    exact G.countable_gluing_failure_le _ o (A σ) T lam hlam (ha σ)
  have hint := lintegral_mono (μ := BernoulliProduct.law q) hb
  rw [lintegral_blockProbability q S F hmF,lintegral_const,measure_univ,mul_one] at hint
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hint
  simpa only [ENNReal.toReal_ofReal hlam,Measure.real,F] using hh
def seedHitEvent (B T : Set V) : Set (Set E) :=
  ⋃ b∈B, G.hitEvent b T
lemma measurableSet_seedHitEvent [Countable V] [Countable E] (B T : Set V) :
    MeasurableSet (G.seedHitEvent B T) :=
  MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun _ => G.measurableSet_hitEvent b T
lemma seedHitEvent_upper (B T : Set V) : IsUpperSet (G.seedHitEvent B T) := by
  intro ω τ hωτ hω
  obtain ⟨b,hb,hω⟩ := Set.mem_iUnion₂.mp hω
  exact Set.mem_iUnion₂.mpr ⟨b,hb,G.hitEvent_mono_edges b T hωτ hω⟩
lemma seed_trial_connects (v : V) (B T : Set V) (F ω : Set E)
    (hF : F⊆ω) (hconnect : ∀ b∈B, (G.openGraph F).Reachable v b)
    (hB : ω∈G.seedHitEvent B T) : ω∈G.hitEvent v T := by
  obtain ⟨b,hb,x,hbx,hx⟩ := Set.mem_iUnion₂.mp hB
  exact ⟨x, ((hconnect b hb).mono (G.openGraph_mono hF)).trans hbx, hx⟩
lemma seed_trial_probability [Countable V] [Countable E]
    (q : E → unitInterval) (S σ F : Set E) (v : V) (B T : Set V)
    (hFS : F⊆S) (hFσ : F⊆σ)
    (hconnect : ∀ b∈B, (G.openGraph F).Reachable v b) :
    (blockProbability q S (G.seedHitEvent B T) σ).toReal ≤
      (BernoulliProduct.law (pinnedParameters q S σ)).real (G.hitEvent v T) := by
  rw [← forceOn_map_law,Measure.real,Measure.map_apply (measurable_forceOn S σ)
    (G.measurableSet_hitEvent v T)]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro ω hω
  apply G.seed_trial_connects v B T F (forceOn S σ ω) ?_ hconnect hω
  intro e he
  simp only [mem_forceOn,if_pos (hFS he)]
  exact hFσ he
def goodRelay (q : E → unitInterval) (S : Set E) (L : Set V)
    (F : V → Set E) (B : V → Set V) (T : Set V) (lam : ℝ) (σ : Set E) : Set V :=
  {v | v∈L ∧ F v⊆σ ∧ 1-lam≤(blockProbability q S (G.seedHitEvent (B v) T) σ).toReal}
lemma goodRelay_measurable [Countable V] [Countable E]
    (q : E → unitInterval) (S : Set E) (L : Set V)
    (F : V → Set E) (B : V → Set V) (T : Set V) (lam : ℝ)
    (hFS : ∀ v, F v⊆S) (v : V) :
    MeasurableSet[blockSigma S] {σ : Set E | v∈G.goodRelay q S L F B T lam σ} := by
  have hW : MeasurableSet[blockSigma S] (allOpen (F v)) :=
    (blockSigma_mono (hFS v)) _ (measurable_allOpen_block (F v))
  have hg := (measurable_blockProbability q S (G.seedHitEvent (B v) T)
    (G.measurableSet_seedHitEvent (B v) T)).ennreal_toReal
  exact MeasurableSet.inter (MeasurableSet.const _) (hW.inter (measurableSet_le measurable_const hg))
theorem goodRelay_gluing [Countable V] [Countable E]
    (q : E → unitInterval) (S : Set E) (L : Set V)
    (F : V → Set E) (B : V → Set V) (T : Set V)
    (hFS : ∀ v, F v⊆S)
    (hconnect : ∀ v∈L, ∀ b∈B v, (G.openGraph (F v)).Reachable v b)
    (o : V) (lam : ℝ) (hlam : 0≤lam) :
    (BernoulliProduct.law q).real {ω : Set E |
      ω∈G.hitEvent o (G.goodRelay q S L F B T lam ω) ∧ ω∉G.hitEvent o T}≤lam := by
  apply G.random_relay_gluing q S o _ T
    (G.goodRelay_measurable q S L F B T lam hFS) lam hlam
  intro σ v hv
  exact hv.2.2.trans (G.seed_trial_probability q S σ (F v) v (B v) T
    (hFS v) hv.2.1 (hconnect v hv.1))
end CriticalPercolation.BondGraph
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Criticality.RestrictedSeed
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.BondGraph
open BernoulliProduct
variable {V E : Type*} (G : BondGraph V E)
def restrictedSeed (A T : Set V) (S : Set E) : Set (Set E) :=
  {ω | ω∩S∈G.seedHitEvent A T}
lemma restrictedSeed_mono (A T : Set V) {S U : Set E} (h : S⊆U) :
    G.restrictedSeed A T S⊆G.restrictedSeed A T U := by
  intro ω hω
  exact G.seedHitEvent_upper A T (Set.inter_subset_inter_right _ h) hω
lemma measurableSet_restrictedSeed [Countable V] [Countable E] (A T : Set V) (S : Set E) :
    MeasurableSet[blockSigma S] (G.restrictedSeed A T S) :=
  (G.measurableSet_seedHitEvent A T).preimage (measurable_inter_block S)
lemma restrictedSeed_measurable [Countable V] [Countable E] (A T : Set V) (S : Set E) :
    MeasurableSet (G.restrictedSeed A T S) :=
  (blockSigma_le S) _ (G.measurableSet_restrictedSeed A T S)
lemma seed_prediction_persists [Countable V] [Countable E]
    (q : E → unitInterval) (A T : Set V) (I F D σ : Set E)
    (hIF : I⊆F) (hfresh : F∩D⊆I) :
    blockProbability q I (G.restrictedSeed A T (I∪D)) σ ≤
      blockProbability q F (G.restrictedSeed A T (F∪D)) σ := by
  have hrestrict : I∩(I∪D)=F∩(I∪D) := by
    ext e
    constructor <;> intro h
    · exact ⟨hIF h.1,h.2⟩
    · rcases h.2 with hi|hd
      · exact ⟨hi,Or.inl hi⟩
      · exact ⟨hfresh ⟨h.1,hd⟩,Or.inr hd⟩
  rw [prediction_persists q I F (I∪D) σ σ _
    (G.measurableSet_restrictedSeed A T (I∪D)) hrestrict (fun _ _ => Iff.rfl)]
  apply measure_mono
  intro ω hω
  exact G.restrictedSeed_mono A T (Set.union_subset_union_left D hIF) hω
lemma restrictedSeed_self (A T : Set V) (h : (A∩T).Nonempty) (S : Set E) :
    G.restrictedSeed A T S=Set.univ := by
  apply Set.eq_univ_of_forall
  intro ω
  obtain ⟨v,hvA,hvT⟩ := h
  exact Set.mem_iUnion₂.mpr ⟨v,hvA,v,SimpleGraph.Reachable.refl _,hvT⟩
end CriticalPercolation.BondGraph
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Exploration.AdaptiveReveal
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
namespace CriticalPercolation.BernoulliProduct
structure RevealPartition (E I : Type*) [Fintype I] where
  block : I → Set E
  cell : I → Set (Set E)
  measurable : ∀ i, MeasurableSet[blockSigma (block i)] (cell i)
  disjoint : Pairwise (Disjoint on cell)
  cover : (⋃ i, cell i)=Set.univ
namespace RevealPartition
variable {E I : Type*} [Fintype I] (P : RevealPartition E I)
lemma cell_measurable (i : I) : MeasurableSet (P.cell i) :=
  (blockSigma_le (P.block i)) _ (P.measurable i)
lemma exists_cell (σ : Set E) : ∃ i, σ∈P.cell i := by
  have h : σ∈⋃ i, P.cell i := by rw [P.cover]; trivial
  exact Set.mem_iUnion.mp h
lemma cell_unique {σ : Set E} {i j : I} (hi : σ∈P.cell i) (hj : σ∈P.cell j) : i=j := by
  by_contra h
  exact Set.disjoint_left.mp (P.disjoint h) hi hj
abbrev historySigma : MeasurableSpace (Set E) where
  MeasurableSet' A := ∀ i, MeasurableSet[blockSigma (P.block i)] (A∩P.cell i)
  measurableSet_empty := by intro i; simp
  measurableSet_compl := by
    intro A hA i
    have he : Aᶜ∩P.cell i=P.cell i\(A∩P.cell i) := by ext σ; simp; tauto
    rw [he]
    exact (P.measurable i).diff (hA i)
  measurableSet_iUnion := by
    intro A hA i
    rw [Set.iUnion_inter]
    exact MeasurableSet.iUnion (fun n => hA n i)
lemma historySigma_le : P.historySigma ≤ (inferInstance : MeasurableSpace (Set E)) := by
  intro A hA
  have he : A=⋃ i, A∩P.cell i := by rw [← Set.inter_iUnion,P.cover,Set.inter_univ]
  rw [he]
  exact MeasurableSet.iUnion (fun i => (blockSigma_le (P.block i)) _ (hA i))
def probability (q : E → unitInterval) (A : Set (Set E)) (σ : Set E) : ℝ≥0∞ :=
  ∑ i, (P.cell i).indicator (blockProbability q (P.block i) A) σ
lemma probability_on_cell (q : E → unitInterval) (A : Set (Set E))
    {σ : Set E} {i : I} (hi : σ∈P.cell i) :
    P.probability q A σ=blockProbability q (P.block i) A σ := by
  rw [probability,Finset.sum_eq_single i]
  · exact Set.indicator_of_mem hi _
  · intro j _ hji
    apply Set.indicator_of_notMem
    intro hj
    exact hji (P.cell_unique hj hi)
  · simp
theorem setLIntegral_probability (q : E → unitInterval) (A B : Set (Set E))
    (hA : MeasurableSet A) (hB : MeasurableSet[P.historySigma] B) :
    (∫⁻ σ in B, P.probability q A σ ∂law q)=law q (A∩B) := by
  have hmB := P.historySigma_le _ hB
  have hf (i : I) : Measurable ((P.cell i).indicator (blockProbability q (P.block i) A)) :=
    ((measurable_blockProbability q (P.block i) A hA).mono (blockSigma_le _) le_rfl).indicator
      (P.cell_measurable i)
  change (∫⁻ σ in B, ∑ i, (P.cell i).indicator (blockProbability q (P.block i) A) σ ∂law q)=_
  rw [lintegral_finsetSum _ (fun i _ => hf i)]
  have he (i : I) :
      (∫⁻ σ in B, (P.cell i).indicator (blockProbability q (P.block i) A) σ ∂law q)=
      law q (A∩(B∩P.cell i)) := by
    rw [lintegral_indicator (P.cell_measurable i),Measure.restrict_restrict
      (P.cell_measurable i),Set.inter_comm (P.cell i) B]
    exact setLIntegral_blockProbability q (P.block i) A (B∩P.cell i) hA (hB i)
  simp_rw [he]
  have hd : Pairwise (Disjoint on (fun i => A∩(B∩P.cell i))) := by
    intro i j hij
    exact (P.disjoint hij).mono (fun _ h => h.2.2) (fun _ h => h.2.2)
  rw [← tsum_fintype (L := .unconditional _),← measure_iUnion hd (fun i => hA.inter (hmB.inter (P.cell_measurable i)))]
  congr 1
  rw [← Set.inter_iUnion,← Set.inter_iUnion,P.cover,Set.inter_univ]
def enlarge (T : I → Set E) (hT : ∀ i, P.block i⊆T i) : RevealPartition E I where
  block := T
  cell := P.cell
  measurable i := (by
    have hmono : blockSigma (P.block i) ≤ blockSigma (T i) :=
      iSup₂_mono' (fun e he => ⟨e,hT i he,le_rfl⟩)
    exact hmono _ (P.measurable i))
  disjoint := P.disjoint
  cover := P.cover
def decide {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    (d : I → Set E → J)
    (hd : ∀ i, @Measurable (Set E) J (blockSigma (P.block i)) inferInstance (d i)) :
    RevealPartition E (I×J) where
  block ij := P.block ij.1
  cell ij := P.cell ij.1∩(d ij.1 ⁻¹' {ij.2})
  measurable ij := (P.measurable ij.1).inter (hd ij.1 (MeasurableSet.singleton _))
  disjoint := by
    intro ij kl hne
    apply Set.disjoint_left.mpr
    intro σ hσ hτ
    have hi : ij.1=kl.1 := P.cell_unique hσ.1 hτ.1
    have hj : ij.2=kl.2 := by
      have ht : d kl.1 σ=kl.2 := hτ.2
      rw [← hi] at ht
      exact hσ.2.symm.trans ht
    exact hne (Prod.ext hi hj)
  cover := by
    apply Set.eq_univ_of_forall
    intro σ
    obtain ⟨i,hi⟩ := P.exists_cell σ
    exact Set.mem_iUnion.mpr ⟨(i,d i σ),hi,rfl⟩
lemma measureReal_inter_le (q : E → unitInterval) (A B : Set (Set E))
    (hA : MeasurableSet A) (hB : MeasurableSet[P.historySigma] B)
    (ε : ℝ) (hε : 0≤ε)
    (hb : ∀ σ∈B, P.probability q A σ≤ENNReal.ofReal ε) :
    (law q).real (B∩A)≤ε*(law q).real B := by
  have hh : law q (A∩B)≤ENNReal.ofReal ε*law q B := by
    rw [← P.setLIntegral_probability q A B hA hB]
    calc
      (∫⁻ σ in B, P.probability q A σ ∂law q) ≤
          ∫⁻ _ in B, ENNReal.ofReal ε ∂law q :=
        setLIntegral_mono' (P.historySigma_le _ hB) hb
      _ = _ := by rw [lintegral_const,Measure.restrict_apply_univ]
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (measure_ne_top _ _)) hh
  simpa only [Set.inter_comm A B,ENNReal.toReal_mul,ENNReal.toReal_ofReal hε,
    Measure.real] using ht
end RevealPartition
end CriticalPercolation.BernoulliProduct
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Exploration.DecisionHistory
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.BernoulliProduct
def DecisionCode : ℕ → Type
  | 0 => Unit
  | n+1 => DecisionCode n×Bool
instance (n : ℕ) : Fintype (DecisionCode n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact inferInstanceAs (Fintype (DecisionCode n×Bool))
structure DecisionRule (E S : Type*) where
  initial : S
  block : S → Set E
  further : ℕ → S → Set E
  contained : ∀ n s, block s⊆further n s
  active : ℕ → S → Prop
  accept : ℕ → S → Set (Set E)
  measurable : ∀ n s, MeasurableSet[blockSigma (further n s)] (accept n s)
  update : ℕ → S → Bool → S
  block_update : ∀ n s b, block (update n s b)=further n s
namespace DecisionRule
variable {E S : Type*} (D : DecisionRule E S)
def state : (n : ℕ) → DecisionCode n → S
  | 0,_ => D.initial
  | n+1,(w,b) => D.update n (state n w) b
def partitionWithBlock : (n : ℕ) →
    {P : RevealPartition E (DecisionCode n) // ∀ w, P.block w=D.block (D.state n w)}
  | 0 => ⟨{
      block := fun _ => D.block D.initial
      cell := fun _ => Set.univ
      measurable := fun _ => MeasurableSet.univ
      disjoint := by intro i j hne; have he : i=j := @Subsingleton.elim Unit _ i j; exact (hne he).elim
      cover := Set.eq_univ_of_forall (fun _ => Set.mem_iUnion.mpr ⟨(),Set.mem_univ _⟩) },
      fun _ => rfl⟩
  | n+1 => by
      let P := (partitionWithBlock n).val
      have hP := (partitionWithBlock n).property
      let Q := P.enlarge (fun w => D.further n (D.state n w)) (by
        intro w
        rw [hP w]
        exact D.contained n (D.state n w))
      let T := Q.decide (fun w ω => if ω∈D.accept n (D.state n w) then true else false) (by
        intro w
        exact Measurable.ite (D.measurable n (D.state n w)) measurable_const measurable_const)
      refine ⟨T,?_⟩
      intro w
      change D.further n (D.state n w.1)=D.block (D.update n (D.state n w.1) w.2)
      exact (D.block_update n _ _).symm
def partition (n : ℕ) : RevealPartition E (DecisionCode n) :=
  (D.partitionWithBlock n).val
lemma partition_block (n : ℕ) (w : DecisionCode n) :
    (D.partition n).block w=D.block (D.state n w) :=
  (D.partitionWithBlock n).property w
lemma partition_cell_succ (n : ℕ) (w : DecisionCode n) (b : Bool) :
    (D.partition (n+1)).cell (w,b)=(D.partition n).cell w∩
      {ω | (if ω∈D.accept n (D.state n w) then true else false)=b} := rfl
lemma historySigma_step (n : ℕ) : (D.partition n).historySigma ≤ (D.partition (n+1)).historySigma := by
  intro A hA w
  rcases w with ⟨w,b⟩
  change MeasurableSet[blockSigma (D.further n (D.state n w))]
    (A ∩ ((D.partition n).cell w ∩
      {ω | (if ω∈D.accept n (D.state n w) then true else false)=b}))
  rw [← Set.inter_assoc]
  have hmono : blockSigma (D.block (D.state n w)) ≤ blockSigma (D.further n (D.state n w)) :=
    iSup₂_mono' (fun e he => ⟨e,D.contained n (D.state n w) he,le_rfl⟩)
  refine (hmono _ ?_).inter ?_
  · rw [← D.partition_block n w]
    exact hA w
  · have hm : @Measurable (Set E) Bool (blockSigma (D.further n (D.state n w))) inferInstance
        (fun ω => if ω∈D.accept n (D.state n w) then true else false) :=
      Measurable.ite (D.measurable n (D.state n w)) measurable_const measurable_const
    exact hm (MeasurableSet.singleton b)
lemma historySigma_mono : Monotone (fun n => (D.partition n).historySigma) :=
  monotone_nat_of_le_succ D.historySigma_step
def failure (n : ℕ) : Set (Set E) := ⋃ w : DecisionCode n,
  (D.partition n).cell w∩{ω | D.active n (D.state n w) ∧ ω∉D.accept n (D.state n w)}
lemma failure_on_cell (n : ℕ) {w : DecisionCode n} {ω : Set E}
    (hw : ω∈(D.partition n).cell w) :
    ω∈D.failure n ↔ D.active n (D.state n w) ∧ ω∉D.accept n (D.state n w) := by
  constructor
  · intro h
    obtain ⟨v,hv,hf⟩ := Set.mem_iUnion.mp h
    have he := (D.partition n).cell_unique hv hw
    change D.active n (D.state n v) ∧ ω∉D.accept n (D.state n v) at hf
    simpa only [he] using hf
  · intro h
    exact Set.mem_iUnion.mpr ⟨w,hw,h⟩
lemma failure_measurable (n : ℕ) : MeasurableSet (D.failure n) := by
  apply MeasurableSet.iUnion
  intro w
  exact ((D.partition n).cell_measurable w).inter
    ((MeasurableSet.const _).inter ((blockSigma_le _) _ (D.measurable n (D.state n w))).compl)
lemma failure_history_measurable (n : ℕ) :
    MeasurableSet[(D.partition (n+1)).historySigma] (D.failure n) := by
  intro w
  rcases w with ⟨w,b⟩
  have he : D.failure n∩(D.partition (n+1)).cell (w,b)=
      {ω | D.active n (D.state n w) ∧ ω∉D.accept n (D.state n w)}∩
        (D.partition (n+1)).cell (w,b) := by
    ext ω
    constructor <;> intro h
    · exact ⟨(D.failure_on_cell n (by rw [D.partition_cell_succ] at h; exact h.2.1)).mp h.1,h.2⟩
    · exact ⟨(D.failure_on_cell n (by rw [D.partition_cell_succ] at h; exact h.2.1)).mpr h.1,h.2⟩
  rw [he]
  apply MeasurableSet.inter _ ((D.partition (n+1)).measurable (w,b))
  change MeasurableSet[blockSigma (D.further n (D.state n w))] _
  exact (MeasurableSet.const _).inter (D.measurable n (D.state n w)).compl
lemma failure_probability_on_cell (q : E → unitInterval) (n : ℕ)
    {w : DecisionCode n} {σ : Set E} (hw : σ∈(D.partition n).cell w) :
    blockProbability q ((D.partition n).block w) (D.failure n) σ=
      blockProbability q (D.block (D.state n w))
        {ω | D.active n (D.state n w) ∧ ω∉D.accept n (D.state n w)} σ := by
  rw [← D.partition_block n w]
  unfold blockProbability
  congr 1
  ext ω
  apply D.failure_on_cell
  exact (block_event_forceOn _ _ ((D.partition n).measurable w) σ ω).mpr hw
theorem conditional_failure_bound (q : E → unitInterval) (B : Set (Set E))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hlocal : ∀ n w σ, σ∈(D.partition n).cell w → σ∈B →
      (blockProbability q (D.block (D.state n w))
        {ω | D.active n (D.state n w) ∧ ω∉D.accept n (D.state n w)} σ).toReal ≤ ε) :
    ∀ n A, MeasurableSet[(D.partition n).historySigma] A → A⊆B →
      (law q).real (A∩D.failure n) ≤ ε*(law q).real A := by
  intro n A hmA hAB
  apply (D.partition n).measureReal_inter_le q (D.failure n) A (D.failure_measurable n) hmA ε hε
  intro σ hσ
  obtain ⟨w,hw⟩ := (D.partition n).exists_cell σ
  rw [(D.partition n).probability_on_cell q (D.failure n) hw,D.failure_probability_on_cell q n hw]
  exact (ENNReal.toReal_le_toReal (ne_of_lt (lt_of_le_of_lt (blockProbability_le_one _ _ _ _) ENNReal.one_lt_top))
    ENNReal.ofReal_ne_top).mp (by rw [ENNReal.toReal_ofReal hε]; exact hlocal n w σ hw (hAB hσ))
def codeOf : (n : ℕ) → Set E → DecisionCode n
  | 0,_ => ()
  | n+1,ω => (codeOf n ω,if ω∈D.accept n (D.state n (codeOf n ω)) then true else false)
lemma codeOf_mem (n : ℕ) (ω : Set E) : ω∈(D.partition n).cell (D.codeOf n ω) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨ih,rfl⟩
end DecisionRule
end CriticalPercolation.BernoulliProduct
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Criticality.SpecifiedFailures
section

namespace OAI
section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation
theorem specified_failures_with_initialization {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : ℕ → MeasurableSpace Ω) (hM : Monotone M)
    (F : ℕ → Set Ω) (hF : ∀ n, MeasurableSet[M (n+1)] (F n))
    (B₀ : Set Ω) (hB₀ : MeasurableSet[M 0] B₀)
    (ε : ℝ) (hε : 0≤ε)
    (hcond : ∀ n B, MeasurableSet[M n] B → B⊆B₀ →
      μ.real (B∩F n)≤ε*μ.real B)
    (s : Finset ℕ) : μ.real (B₀∩⋂ n∈s, F n) ≤ μ.real B₀*ε^s.card := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert n s hn ih =>
    have hns : n∉s := fun h => (lt_irrefl n) (hn n h)
    have hbs : MeasurableSet[M n] (B₀∩⋂ j∈s, F j) := by
      refine ((hM (Nat.zero_le n)) _ hB₀).inter ?_
      apply MeasurableSet.biInter s.finite_toSet.countable
      intro j hj
      exact hM (Nat.succ_le_of_lt (hn j hj)) _ (hF j)
    have h := hcond n (B₀∩⋂ j∈s, F j) hbs Set.inter_subset_left
    have he : B₀∩⋂ j∈insert n s, F j=(B₀∩⋂ j∈s, F j)∩F n := by
      rw [Finset.set_biInter_insert]
      ext x
      simp only [Set.mem_inter_iff]
      tauto
    rw [he,Finset.card_insert_of_notMem hns,pow_succ]
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_left ih hε])
end CriticalPercolation
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Criticality.BalancedCycles
section

namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical
namespace CriticalPercolation.Boundary
def balancedPermutation {V E : Type*} [Fintype E] (tail head : E → V)
    (hb : ∀ v, Fintype.card {e // head e=v}=Fintype.card {e // tail e=v}) : Equiv.Perm E :=
  Equiv.ofFiberEquiv (fun v => Fintype.equivOfCardEq (hb v))
lemma balancedPermutation_tail {V E : Type*} [Fintype E] (tail head : E → V)
    (hb : ∀ v, Fintype.card {e // head e=v}=Fintype.card {e // tail e=v}) (e : E) :
    tail (balancedPermutation tail head hb e)=head e :=
  Equiv.ofFiberEquiv_map _ e
theorem exists_closed_trail {V E : Type*} [Fintype E] (tail head : E → V)
    (hb : ∀ v, Fintype.card {e // head e=v}=Fintype.card {e // tail e=v}) (e₀ : E) :
    ∃ n : ℕ, 0<n ∧ ∃ e : ℕ → E, e 0=e₀ ∧ e n=e₀ ∧
      (∀ i, head (e i)=tail (e (i+1))) ∧ Set.InjOn e (Set.Iio n) := by
  let p := balancedPermutation tail head hb
  let n := Function.minimalPeriod p e₀
  have hn : 0<n := Function.minimalPeriod_pos_of_mem_periodicPts (p.injective.mem_periodicPts e₀)
  refine ⟨n,hn,(fun i => p^[i] e₀),rfl,?_,?_,Function.iterate_injOn_Iio_minimalPeriod⟩
  · exact Function.isPeriodicPt_minimalPeriod p e₀
  · intro i
    dsimp only
    rw [Function.iterate_succ_apply']
    exact (balancedPermutation_tail tail head hb _).symm
end CriticalPercolation.Boundary
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Criticality.SquareBoundary
section

namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical BigOperators
namespace CriticalPercolation.Boundary
abbrev Grid := ℤ×ℤ
abbrev Dir := Fin 4
abbrev Edge := Grid×Dir
def step : Dir → Grid := ![(1,0),(0,1),(-1,0),(0,-1)]
def leftOffset : Dir → Grid := ![(0,0),(-1,0),(-1,-1),(0,-1)]
def rightOffset : Dir → Grid := ![(0,-1),(0,0),(-1,0),(-1,-1)]
def tail (e : Edge) : Grid := e.1
def head (e : Edge) : Grid := e.1+step e.2
def leftSite (e : Edge) : Grid := e.1+leftOffset e.2
def rightSite (e : Edge) : Grid := e.1+rightOffset e.2
def squareBoundary (S : Set Grid) : Set Edge :=
  {e | leftSite e∈S ∧ rightSite e∉S}
lemma squareBoundary_finite {S : Set Grid} (hS : S.Finite) : (squareBoundary S).Finite := by
  apply Set.Finite.of_injOn (f := fun e : Edge => (leftSite e,e.2))
    (t := S×ˢ(Set.univ : Set Dir)) ?_ ?_ (hS.prod Set.finite_univ)
  · intro e he
    exact ⟨he.1,Set.mem_univ _⟩
  · rintro ⟨p,d⟩ _ ⟨q,c⟩ _ h
    have hd : d=c := congrArg Prod.snd h
    subst c
    have hp : p=q := add_right_cancel (congrArg Prod.fst h)
    exact Prod.ext hp rfl
def outgoingEquiv (S : Set Grid) (v : Grid) :
    {e : squareBoundary S // tail e=v} ≃ {d : Dir // (v,d)∈squareBoundary S} where
  toFun e := ⟨e.1.1.2,by
    have h := e.1.2
    have hv := e.2
    change e.1.1.1=v at hv
    change leftSite (e.1.1.1,e.1.1.2)∈S ∧ rightSite (e.1.1.1,e.1.1.2)∉S at h
    rwa [hv] at h⟩
  invFun d := ⟨⟨(v,d.1),d.2⟩,rfl⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext e.2.symm rfl
  right_inv d := rfl
def incomingEquiv (S : Set Grid) (v : Grid) :
    {e : squareBoundary S // head e=v} ≃
      {d : Dir // (v-step d,d)∈squareBoundary S} where
  toFun e := ⟨e.1.1.2,by
    have hv : e.1.1.1=v-step e.1.1.2 := eq_sub_iff_add_eq.mpr e.2
    have h := e.1.2
    change leftSite (e.1.1.1,e.1.1.2)∈S ∧ rightSite (e.1.1.1,e.1.1.2)∉S at h
    rwa [hv] at h⟩
  invFun d := ⟨⟨(v-step d.1,d.1),d.2⟩,sub_add_cancel _ _⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    change (v-step e.1.1.2,e.1.1.2)=e.1.1
    exact Prod.ext (eq_sub_iff_add_eq.mpr e.2).symm rfl
  right_inv d := rfl
lemma squareBoundary_balanced (S : Set Grid) (v : Grid) :
    Fintype.card {d : Dir // (v-step d,d)∈squareBoundary S}=
      Fintype.card {d : Dir // (v,d)∈squareBoundary S} := by
  rcases v with ⟨x,y⟩
  rw [Fintype.card_subtype (fun d : Dir => ((x,y)-step d,d)∈squareBoundary S),
    Fintype.card_subtype (fun d : Dir => ((x,y),d)∈squareBoundary S)]
  simp only [Finset.card_filter,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  simp only [squareBoundary,Set.mem_ofPred_eq,leftSite,rightSite,step,leftOffset,rightOffset]
  simp only [Matrix.cons_val_zero,Prod.mk_add_mk,add_zero,sub_eq_add_neg]
  by_cases h1 : (x,y)∈S <;> by_cases h2 : (x+-1,y)∈S <;>
    by_cases h3 : (x+-1,y+-1)∈S <;> by_cases h4 : (x,y+-1)∈S <;>
    simp_all
theorem squareBoundary_closed_trail {S : Set Grid} (hS : S.Finite)
    (e₀ : Edge) (he₀ : e₀∈squareBoundary S) :
    ∃ n : ℕ, 0<n ∧ ∃ e : ℕ → Edge, e 0=e₀ ∧ e n=e₀ ∧
      (∀ i, e i∈squareBoundary S) ∧ (∀ i, head (e i)=tail (e (i+1))) ∧
      Set.InjOn e (Set.Iio n) := by
  let := (squareBoundary_finite hS).fintype
  have hb (v : Grid) : Fintype.card {e : squareBoundary S // head e=v}=
      Fintype.card {e : squareBoundary S // tail e=v} :=
    (Fintype.card_congr (incomingEquiv S v)).trans
      ((squareBoundary_balanced S v).trans (Fintype.card_congr (outgoingEquiv S v)).symm)
  obtain ⟨n,hn,e,h0,hn0,hchain,hinj⟩ := exists_closed_trail
    (fun e : squareBoundary S => tail e) (fun e : squareBoundary S => head e) (by intro v; simpa only [Fintype.card_eq_nat_card] using hb v) ⟨e₀,he₀⟩
  refine ⟨n,hn,(fun i => (e i).1),congrArg Subtype.val h0,congrArg Subtype.val hn0,
    fun i => (e i).2,hchain,?_⟩
  intro i hi j hj he
  exact hinj hi hj (Subtype.ext he)
lemma west_root_edge_mem (S : Set Grid) (hroot : (0,0)∈S)
    (hquad : ∀ v∈S, 0≤v.1 ∧ 0≤v.2) : ((0,1),3)∈squareBoundary S := by
  constructor
  · simpa [leftSite,leftOffset] using hroot
  · have hbad : (-1,0)∉S := by
      intro h
      have ht := (hquad _ h).1
      norm_num at ht
    simpa [rightSite,rightOffset] using hbad
end CriticalPercolation.Boundary
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.ContourSites
section

namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical BigOperators
namespace CriticalPercolation.Boundary
def forwardDir (d : Dir) : Prop := d=1 ∨ d=2
def forwardIndices (e : ℕ → Edge) (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun i => forwardDir (e i).2)
def outsideSites (e : ℕ → Edge) (n : ℕ) : Finset Grid :=
  (forwardIndices e n).image (fun i => rightSite (e i))
lemma forward_step (d : Dir) : (step d).1-(step d).2=
    if forwardDir d then (-1 : ℤ) else 1 := by
  fin_cases d <;> norm_num [step,forwardDir,Fin.ext_iff]
lemma twice_forward_card (e : ℕ → Edge) (n : ℕ)
    (hchain : ∀ i, head (e i)=tail (e (i+1))) (hclose : e n=e 0) :
    2*(forwardIndices e n).card=n := by
  have hv (i : ℕ) : (e (i+1)).1=(e i).1+step (e i).2 := (hchain i).symm
  have hd (i : ℕ) :
      ((e (i+1)).1.1-(e (i+1)).1.2)-((e i).1.1-(e i).1.2)=
      if forwardDir (e i).2 then (-1 : ℤ) else 1 := by
    rw [hv]
    simpa only [Prod.fst_add,Prod.snd_add] using (by
      rw [← forward_step]
      ring : ((e i).1.1+(step (e i).2).1-((e i).1.2+(step (e i).2).2))-
        ((e i).1.1-(e i).1.2)=if forwardDir (e i).2 then (-1 : ℤ) else 1)
  have hz : (∑ i∈Finset.range n, (if forwardDir (e i).2 then (-1 : ℤ) else 1))=0 := by
    simp_rw [← hd]
    rw [Finset.sum_range_sub (fun i => (e i).1.1-(e i).1.2),hclose,sub_self]
  have hf : ∑ i∈Finset.range n, (if forwardDir (e i).2 then (1 : ℤ) else 0)=
      ((forwardIndices e n).card : ℤ) := by
    simp [forwardIndices,Finset.sum_boole]
  have he (i : ℕ) : (if forwardDir (e i).2 then (-1 : ℤ) else 1)=
      1-2*(if forwardDir (e i).2 then (1 : ℤ) else 0) := by split <;> norm_num
  simp_rw [he] at hz
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,hf] at hz
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] at hz
  omega
lemma rightSite_direction_injective :
    Function.Injective (fun e : Edge => (rightSite e,e.2)) := by
  rintro ⟨p,d⟩ ⟨q,c⟩ h
  have hd : d=c := congrArg Prod.snd h
  subst c
  have hp : p=q := add_right_cancel (congrArg Prod.fst h)
  exact Prod.ext hp rfl
lemma forward_card_le_twice_outside (e : ℕ → Edge) (n : ℕ)
    (hinj : Set.InjOn e (Set.Iio n)) :
    (forwardIndices e n).card≤2*(outsideSites e n).card := by
  have hb := Finset.card_le_card_of_injOn
    (s := forwardIndices e n) (t := outsideSites e n ×ˢ ({1,2} : Finset Dir))
    (f := fun i => (rightSite (e i),(e i).2))
    (by
      intro i hi
      refine Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨i,hi,rfl⟩,?_⟩
      simpa only [forwardDir,Finset.mem_insert,Finset.mem_singleton] using (Finset.mem_filter.mp hi).2)
    (by
      intro i hi j hj he
      exact hinj (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hj).1) (rightSite_direction_injective he))
  have hc : ({1,2} : Finset Dir).card=2 := by decide
  rw [Finset.card_product,hc] at hb
  omega
theorem length_le_four_outside (e : ℕ → Edge) (n : ℕ)
    (hchain : ∀ i, head (e i)=tail (e (i+1))) (hclose : e n=e 0)
    (hinj : Set.InjOn e (Set.Iio n)) : n≤4*(outsideSites e n).card := by
  have h := twice_forward_card e n hchain hclose
  have h' := forward_card_le_twice_outside e n hinj
  omega
lemma forward_child (e : Edge) (hdir : forwardDir e.2) :
    rightSite e=leftSite e+(1,0) ∨ rightSite e=leftSite e+(0,1) := by
  rcases e with ⟨⟨x,y⟩,d⟩
  rcases hdir with h|h
  · change d=1 at h
    subst d
    left
    simp [rightSite,leftSite,rightOffset,leftOffset]
  · change d=2 at h
    subst d
    right
    simp [rightSite,leftSite,rightOffset,leftOffset]
lemma outsideSites_failed_children (S : Set Grid) (e : ℕ → Edge) (n : ℕ)
    (hmem : ∀ i, e i∈squareBoundary S) :
    ∀ z∈outsideSites e n, z∉S ∧ ∃ y∈S, z=y+(1,0) ∨ z=y+(0,1) := by
  intro z hz
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
  exact ⟨(hmem i).2,leftSite (e i),(hmem i).1,
    forward_child (e i) (Finset.mem_filter.mp hi).2⟩
end CriticalPercolation.Boundary
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.ContourWords
section

namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical BigOperators
namespace CriticalPercolation.Boundary
def wordDir {n : ℕ} (w : Fin n → Dir) (i : ℕ) : Dir :=
  if h : i<n then w ⟨i,h⟩ else if h₀ : 0<n then w ⟨0,h₀⟩ else 0
def wordEdge {n : ℕ} (p : Grid) (w : Fin n → Dir) (i : ℕ) : Edge :=
  (p+∑ j∈Finset.range i, step (wordDir w j),wordDir w i)
lemma wordEdge_chain {n : ℕ} (p : Grid) (w : Fin n → Dir) (i : ℕ) :
    head (wordEdge p w i)=tail (wordEdge p w (i+1)) := by
  simp [wordEdge,head,tail,Finset.sum_range_succ,add_assoc]
lemma wordEdge_zero {n : ℕ} (p : Grid) (w : Fin n → Dir) :
    (wordEdge p w 0).1=p := by simp [wordEdge]
lemma wordEdge_reconstruct {n : ℕ} (hn : 0<n) (e : ℕ → Edge)
    (hchain : ∀ i, head (e i)=tail (e (i+1))) (hclose : e n=e 0) :
    ∀ i≤n, wordEdge (e 0).1 (fun j : Fin n => (e j).2) i=e i := by
  let w : Fin n → Dir := fun j => (e j).2
  have hd (i : ℕ) (hi : i<n) : wordDir w i=(e i).2 := by simp [wordDir,hi,w]
  have hv : ∀ i≤n, (wordEdge (e 0).1 w i).1=(e i).1 := by
    intro i hi
    induction i with
    | zero => exact wordEdge_zero _ _
    | succ i ih =>
      have hh : i<n := by omega
      have ih' := ih (by omega)
      have hc := wordEdge_chain (e 0).1 w i
      change (wordEdge (e 0).1 w i).1+step (wordDir w i)=
        (wordEdge (e 0).1 w (i+1)).1 at hc
      rw [← hc,ih',hd i hh]
      exact hchain i
  intro i hi
  apply Prod.ext (hv i hi)
  change wordDir w i=(e i).2
  by_cases hlt : i<n
  · exact hd i hlt
  · have hie : i=n := by omega
    subst i
    simp [wordDir,hn,hclose,w]
lemma card_words (n : ℕ) : Fintype.card (Fin n → Dir)=4^n := by
  simp [Dir]
def wordValid {n : ℕ} (p : Grid) (w : Fin n → Dir) : Prop :=
  wordEdge p w n=wordEdge p w 0 ∧ Set.InjOn (wordEdge p w) (Set.Iio n)
lemma wordValid_reconstruct {n : ℕ} (hn : 0<n) (e : ℕ → Edge)
    (hchain : ∀ i, head (e i)=tail (e (i+1))) (hclose : e n=e 0)
    (hinj : Set.InjOn e (Set.Iio n)) :
    wordValid (e 0).1 (fun j : Fin n => (e j).2) := by
  have hr := wordEdge_reconstruct hn e hchain hclose
  refine ⟨?_,?_⟩
  · rw [hr n le_rfl,hr 0 (Nat.zero_le n),hclose]
  · intro i hi j hj he
    rw [hr i hi.le,hr j hj.le] at he
    exact hinj hi hj he
lemma outsideSites_congr {n : ℕ} {e f : ℕ → Edge}
    (h : ∀ i<n, e i=f i) : outsideSites e n=outsideSites f n := by
  have hf : forwardIndices e n=forwardIndices f n := by
    apply Finset.filter_congr
    intro i hi
    rw [h i (Finset.mem_range.mp hi)]
  unfold outsideSites
  rw [hf]
  apply Finset.image_congr
  intro i hi
  dsimp only
  rw [h i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)]
theorem finite_good_contour (S : Set Grid) (hS : S.Finite) (hroot : (0,0)∈S)
    (hquad : ∀ v∈S, 0≤v.1 ∧ 0≤v.2) :
    ∃ n : ℕ, ∃ w : Fin (n+1) → Dir,
      wordValid (0,1) w ∧
      (∀ z∈outsideSites (wordEdge (0,1) w) (n+1),
        z∉S ∧ ∃ y∈S, z=y+(1,0) ∨ z=y+(0,1)) := by
  obtain ⟨l,hl,e,h0,hend,hmem,hchain,hinj⟩ := squareBoundary_closed_trail hS
    ((0,1),3) (west_root_edge_mem S hroot hquad)
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hl)
  have he : e (n+1)=e 0 := hend.trans h0.symm
  have hp : (e 0).1=(0,1) := congrArg Prod.fst h0
  refine ⟨n,(fun j : Fin (n+1) => (e j).2),?_,?_⟩
  · simpa only [hp] using wordValid_reconstruct hl e hchain he hinj
  · have hr := wordEdge_reconstruct hl e hchain he
    rw [hp] at hr
    rw [outsideSites_congr (fun i hi => hr i hi.le)]
    exact outsideSites_failed_children S e (n+1) hmem
end CriticalPercolation.Boundary
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.ProductMeasure.ContourProbability
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
namespace CriticalPercolation
lemma measureReal_countable_union_bound {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A : I → Set Ω) (b : I → ℝ)
    (hb : ∀ i, 0≤b i) (hs : Summable b) (hA : ∀ i, μ.real (A i)≤b i) :
    μ.real (⋃ i, A i)≤∑' i, b i := by
  have hh (i : I) : μ (A i)≤ENNReal.ofReal (b i) := by
    calc μ (A i)=ENNReal.ofReal (μ.real (A i)) := by simp [Measure.real]
         _ ≤ ENNReal.ofReal (b i) := ENNReal.ofReal_le_ofReal (hA i)
  have h := (measure_iUnion_le A).trans (ENNReal.tsum_le_tsum hh)
  rw [← ENNReal.ofReal_tsum_of_nonneg hb hs] at h
  have ht := ENNReal.toReal_mono (by finiteness) h
  simpa only [Measure.real,ENNReal.toReal_ofReal (tsum_nonneg hb)] using ht
namespace Boundary
def wordFailure {Ω : Type*} (B : Set Ω) (F : Grid → Set Ω)
    {n : ℕ} (w : Fin n → Dir) : Set Ω :=
  if wordValid (0,1) w then B∩⋂ z∈outsideSites (wordEdge (0,1) w) n, F z else ∅
lemma wordFailure_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (B : Set Ω) (F : Grid → Set Ω)
    (q : ℝ) (hq₀ : 0≤q) (hq₁ : q≤1)
    (hfail : ∀ s : Finset Grid, μ.real (B∩⋂ z∈s, F z)≤μ.real B*(q^4)^s.card)
    (n : ℕ) (w : Fin n → Dir) : μ.real (wordFailure B F w)≤μ.real B*q^n := by
  by_cases hw : wordValid (0,1) w
  · rw [wordFailure,if_pos hw]
    apply (hfail _).trans
    apply mul_le_mul_of_nonneg_left _ (measureReal_nonneg)
    rw [← pow_mul]
    exact pow_le_pow_of_le_one hq₀ hq₁
      (length_le_four_outside _ _ (wordEdge_chain (0,1) w) hw.1 hw.2)
  · rw [wordFailure,if_neg hw]
    simp only [measureReal_empty]
    positivity
theorem finite_good_probability_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (B : Set Ω)
    (S : Ω → Set Grid) (F : Grid → Set Ω)
    (hroot : ∀ ω∈B, (0,0)∈S ω)
    (hquad : ∀ ω∈B, ∀ v∈S ω, 0≤v.1 ∧ 0≤v.2)
    (hchild : ∀ ω∈B, ∀ z, z∉S ω →
      (∃ y∈S ω, z=y+(1,0) ∨ z=y+(0,1)) → ω∈F z)
    (q : ℝ) (hq₀ : 0≤q) (hq : 4*q<1)
    (hfail : ∀ s : Finset Grid, μ.real (B∩⋂ z∈s, F z)≤μ.real B*(q^4)^s.card) :
    μ.real (B∩{ω | (S ω).Finite})≤μ.real B*(4*q)/(1-4*q) := by
  have hsub : B∩{ω | (S ω).Finite}⊆
      ⋃ n : ℕ, ⋃ w : Fin (n+1) → Dir, wordFailure B F w := by
    intro ω hω
    obtain ⟨n,w,hw,hz⟩ := finite_good_contour (S ω) hω.2 (hroot ω hω.1) (hquad ω hω.1)
    refine Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨w,?_⟩⟩
    rw [wordFailure,if_pos hw]
    refine ⟨hω.1,Set.mem_iInter.mpr fun z => Set.mem_iInter.mpr fun hs => ?_⟩
    exact hchild ω hω.1 z (hz z hs).1 (hz z hs).2
  have hq₁ : q≤1 := by linarith
  have hterm (n : ℕ) :
      μ.real (⋃ w : Fin (n+1) → Dir, wordFailure B F w)≤μ.real B*(4*q)^(n+1) := by
    apply (measureReal_iUnion_fintype_le _).trans
    calc
      (∑ w : Fin (n+1) → Dir, μ.real (wordFailure B F w))≤
          ∑ _w : Fin (n+1) → Dir, μ.real B*q^(n+1) :=
        Finset.sum_le_sum (fun w _ => wordFailure_bound μ B F q hq₀ hq₁ hfail (n+1) w)
      _ = μ.real B*(4*q)^(n+1) := by
        simp only [Finset.sum_const,Finset.card_univ,card_words,nsmul_eq_mul,
          Nat.cast_pow,Nat.cast_ofNat,mul_pow]
        ring
  have hs₀ : Summable (fun n : ℕ => (4*q)^n) :=
    summable_geometric_of_lt_one (by positivity) hq
  have hs : Summable (fun n : ℕ => μ.real B*(4*q)^(n+1)) :=
    ((summable_nat_add_iff 1).mpr hs₀).mul_left _
  have hu := measureReal_countable_union_bound μ
    (fun n => ⋃ w : Fin (n+1) → Dir, wordFailure B F w)
    (fun n => μ.real B*(4*q)^(n+1)) (fun _ => by positivity) hs hterm
  apply ((measureReal_mono hsub).trans hu).trans_eq
  simp_rw [pow_succ]
  rw [tsum_mul_left,tsum_mul_right,tsum_geometric_of_lt_one (by positivity) hq]
  ring
theorem infinite_good_positive {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (B : Set Ω)
    (S : Ω → Set Grid) (F : Grid → Set Ω)
    (hB : 0<μ.real B)
    (hroot : ∀ ω∈B, (0,0)∈S ω)
    (hquad : ∀ ω∈B, ∀ v∈S ω, 0≤v.1 ∧ 0≤v.2)
    (hchild : ∀ ω∈B, ∀ z, z∉S ω →
      (∃ y∈S ω, z=y+(1,0) ∨ z=y+(0,1)) → ω∈F z)
    (q : ℝ) (hq₀ : 0≤q) (hq : 8*q<1)
    (hfail : ∀ s : Finset Grid, μ.real (B∩⋂ z∈s, F z)≤μ.real B*(q^4)^s.card) :
    0<μ.real (B∩{ω | (S ω).Infinite}) := by
  have hh : 4*q<1 := by linarith
  have hf := finite_good_probability_bound μ B S F hroot hquad hchild q hq₀ hh hfail
  have hratio : μ.real B*(4*q)/(1-4*q)<μ.real B := by
    apply (div_lt_iff₀ (by linarith : 0<1-4*q)).mpr
    nlinarith [mul_pos hB (by linarith : 0<1-8*q)]
  have he : B=(B∩{ω | (S ω).Finite})∪(B∩{ω | (S ω).Infinite}) := by
    ext ω
    simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_ofPred_eq,Set.Infinite]
    tauto
  have hu := measureReal_union_le (μ := μ)
    (B∩{ω | (S ω).Finite}) (B∩{ω | (S ω).Infinite})
  rw [← he] at hu
  linarith
end Boundary
end CriticalPercolation
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.SlotContour
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
namespace CriticalPercolation.Boundary
def gridSlot (v : Grid) : ℕ := Nat.pair v.1.toNat v.2.toNat
def quadrant (v : Grid) : Prop := 0≤v.1 ∧ 0≤v.2
lemma gridSlot_injective : Set.InjOn gridSlot {v | quadrant v} := by
  intro v hv w hw he
  have hh := Nat.pairEquiv.injective (show Nat.pairEquiv (v.1.toNat,v.2.toNat)=
    Nat.pairEquiv (w.1.toNat,w.2.toNat) from he)
  change (v.1.toNat,v.2.toNat)=(w.1.toNat,w.2.toNat) at hh
  have hx := congrArg Prod.fst hh
  have hy := congrArg Prod.snd hh
  apply Prod.ext <;> dsimp only [quadrant,Set.mem_ofPred_eq] at hv hw <;> omega
lemma gridSlot_east (v : Grid) (hv : quadrant v) : gridSlot v<gridSlot (v+(1,0)) := by
  change Nat.pair v.1.toNat v.2.toNat<Nat.pair (v.1+1).toNat (v.2+0).toNat
  rw [add_zero]
  exact Nat.pair_lt_pair_left _ (by dsimp [quadrant] at hv; omega)
lemma gridSlot_north (v : Grid) (hv : quadrant v) : gridSlot v<gridSlot (v+(0,1)) := by
  change Nat.pair v.1.toNat v.2.toNat<Nat.pair (v.1+0).toNat (v.2+1).toNat
  rw [add_zero]
  exact Nat.pair_lt_pair_right _ (by dsimp [quadrant] at hv; omega)
def gridFailure {Ω : Type*} (F : ℕ → Set Ω) (v : Grid) : Set Ω :=
  if quadrant v then F (gridSlot v) else ∅
lemma specified_grid_failures {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : ℕ → MeasurableSpace Ω) (hM : Monotone M)
    (F : ℕ → Set Ω) (hF : ∀ n, MeasurableSet[M (n+1)] (F n))
    (B : Set Ω) (hB : MeasurableSet[M 0] B)
    (ε : ℝ) (hε : 0≤ε)
    (hcond : ∀ n A, MeasurableSet[M n] A → A⊆B → μ.real (A∩F n)≤ε*μ.real A)
    (s : Finset Grid) : μ.real (B∩⋂ z∈s, gridFailure F z)≤μ.real B*ε^s.card := by
  by_cases hs : ∀ z∈s, quadrant z
  · have he : (⋂ z∈s, gridFailure F z)=⋂ n∈s.image gridSlot, F n := by
      ext ω
      constructor
      · intro h
        refine Set.mem_iInter.mpr fun n => Set.mem_iInter.mpr fun hn => ?_
        obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hn
        have hh := Set.mem_iInter.mp (Set.mem_iInter.mp h z) hz
        simpa only [gridFailure,if_pos (hs z hz)] using hh
      · intro h
        refine Set.mem_iInter.mpr fun z => Set.mem_iInter.mpr fun hz => ?_
        have hh := Set.mem_iInter.mp (Set.mem_iInter.mp h (gridSlot z))
          (Finset.mem_image.mpr ⟨z,hz,rfl⟩)
        simpa only [gridFailure,if_pos (hs z hz)] using hh
    rw [he]
    have hc : (s.image gridSlot).card=s.card := Finset.card_image_iff.mpr (by
      intro z hz w hw he
      exact gridSlot_injective (hs z hz) (hs w hw) he)
    have h := specified_failures_with_initialization μ M hM F hF B hB ε hε hcond
      (s.image gridSlot)
    rwa [hc] at h
  · push Not at hs
    obtain ⟨z,hz,hq⟩ := hs
    have he : (⋂ z∈s, gridFailure F z)=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω h
      have hh := Set.mem_iInter.mp (Set.mem_iInter.mp h z) hz
      simp only [gridFailure,if_neg hq,Set.mem_empty_iff_false] at hh
    rw [he,Set.inter_empty,measureReal_empty]
    positivity
theorem infinitely_many_good_from_tests {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (M : ℕ → MeasurableSpace Ω) (hM : Monotone M)
    (F : ℕ → Set Ω) (hF : ∀ n, MeasurableSet[M (n+1)] (F n))
    (B : Set Ω) (hmB : MeasurableSet[M 0] B) (hB : 0<μ.real B)
    (S : Ω → Set Grid)
    (hroot : ∀ ω∈B, (0,0)∈S ω)
    (hquad : ∀ ω∈B, ∀ v∈S ω, quadrant v)
    (hchild : ∀ ω∈B, ∀ z, z∉S ω →
      (∃ y∈S ω, z=y+(1,0) ∨ z=y+(0,1)) → ω∈F (gridSlot z))
    (q : ℝ) (hq₀ : 0≤q) (hq : 8*q<1)
    (hcond : ∀ n A, MeasurableSet[M n] A → A⊆B →
      μ.real (A∩F n)≤q^4*μ.real A) :
    0<μ.real (B∩{ω | (S ω).Infinite}) := by
  apply infinite_good_positive μ B S (gridFailure F) hB hroot hquad ?_ q hq₀ hq
    (specified_grid_failures μ M hM F hF B hmB (q^4) (by positivity) hcond)
  intro ω hω z hz hc
  have hqz : quadrant z := by
    obtain ⟨y,hy,he|he⟩ := hc
    · rw [he]
      have h := hquad ω hω y hy
      change 0≤y.1+1 ∧ 0≤y.2+0
      exact ⟨by linarith [h.1],by linarith [h.2]⟩
    · rw [he]
      have h := hquad ω hω y hy
      change 0≤y.1+0 ∧ 0≤y.2+1
      exact ⟨by linarith [h.1],by linarith [h.2]⟩
  simpa only [gridFailure,if_pos hqz] using hchild ω hω z hz hc
end CriticalPercolation.Boundary
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.CorridorSeparation
section

namespace OAI
section
section
noncomputable section
open Set
open scoped Classical
namespace CriticalPercolation.Corridor
abbrev Site := ℤ×ℤ
abbrev Point := ℝ×ℝ
abbrev Edge := Site×Bool
def source (e : Edge) : Site := e.1
def target (e : Edge) : Site := if e.2 then e.1+(1,0) else e.1+(0,1)
def endpoints (e : Edge) : Set Site := {source e,target e}
def box (j h : ℝ) (v : Site) : Set Point := {x |
    |x.1-((v.1 : ℝ)+v.2)|≤j ∧ |x.2-((v.1 : ℝ)-v.2)|≤j+h}
def tube (h : ℝ) (e : Edge) : Set Point := {x |
    (e.1.1 : ℝ)+e.1.2≤x.1 ∧ x.1≤(e.1.1 : ℝ)+e.1.2+1 ∧
    if e.2 then |x.2-(x.1-2*(e.1.2 : ℝ))|≤h
    else |x.2-(2*(e.1.1 : ℝ)-x.1)|≤h}
def domain (j h : ℝ) (e : Edge) : Set Point :=
  box j h (source e)∪box j h (target e)∪tube h e
lemma int_eq_of_close (a b : ℤ) (h1 : (a : ℝ)-b<1) (h2 : (b : ℝ)-a<1) : a=b := by
  have h1' : a-b<1 := by exact_mod_cast h1
  have h2' : b-a<1 := by exact_mod_cast h2
  omega
lemma int_endpoint_interval (a b : ℤ) (h1 : (a : ℝ)-b<1) (h2 : (b : ℝ)-a<2) :
    b=a ∨ b=a+1 := by
  have h1' : a-b<1 := by exact_mod_cast h1
  have h2' : b-a<2 := by exact_mod_cast h2
  omega
lemma box_disjoint (j h : ℝ) (hs : 2*j+h<1) {v w : Site} (hv : v≠w) :
    Disjoint (box j h v) (box j h w) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨hx1,hx2⟩ := hx
  obtain ⟨hy1,hy2⟩ := hy
  rw [abs_le] at hx1 hx2 hy1 hy2
  apply hv
  apply Prod.ext
  · apply int_eq_of_close <;> linarith
  · apply int_eq_of_close <;> linarith
lemma box_tube_endpoint (j h : ℝ) (hs : j+h<1) (hj : j<1)
    {v : Site} {e : Edge} {x : Point} (hx : x∈box j h v) (hy : x∈tube h e) :
    v=source e ∨ v=target e := by
  obtain ⟨a,b⟩ := v
  obtain ⟨⟨c,d⟩,s⟩ := e
  obtain ⟨hx1,hx2⟩ := hx
  rw [abs_le] at hx1 hx2
  cases s with
  | true =>
    change (c : ℝ)+d≤x.1 ∧ x.1≤(c : ℝ)+d+1 ∧ |x.2-(x.1-2*(d : ℝ))|≤h at hy
    rw [abs_le] at hy
    have hb : b=d := int_eq_of_close _ _ (by linarith) (by linarith)
    subst d
    have ha : a=c ∨ a=c+1 := int_endpoint_interval _ _ (by linarith) (by linarith)
    rcases ha with rfl|rfl <;> simp [source,target]
  | false =>
    change (c : ℝ)+d≤x.1 ∧ x.1≤(c : ℝ)+d+1 ∧ |x.2-(2*(c : ℝ)-x.1)|≤h at hy
    rw [abs_le] at hy
    have ha : a=c := int_eq_of_close _ _ (by linarith) (by linarith)
    subst c
    have hb : b=d ∨ b=d+1 := int_endpoint_interval _ _ (by linarith) (by linarith)
    rcases hb with rfl|rfl <;> simp [source,target]
lemma tubes_opposite (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hh1 : h<1)
    (a b c d : ℤ) {x : Point} (hx : x∈tube h ((a,b),true))
    (hy : x∈tube h ((c,d),false)) :
    ∃ v, v∈endpoints ((a,b),true) ∧ v∈endpoints ((c,d),false) ∧ x∈box j h v := by
  change (a : ℝ)+b≤x.1 ∧ x.1≤(a : ℝ)+b+1 ∧ |x.2-(x.1-2*(b : ℝ))|≤h at hx
  change (c : ℝ)+d≤x.1 ∧ x.1≤(c : ℝ)+d+1 ∧ |x.2-(2*(c : ℝ)-x.1)|≤h at hy
  rw [abs_le] at hx hy
  have hac : c=a ∨ c=a+1 := int_endpoint_interval _ _ (by linarith) (by linarith)
  have hdb : b=d ∨ b=d+1 := int_endpoint_interval _ _ (by linarith) (by linarith)
  refine ⟨(c,b),?_,?_,?_⟩
  · rcases hac with rfl|rfl <;> simp [endpoints,source,target]
  · rcases hdb with rfl|rfl <;> simp [endpoints,source,target]
  · constructor <;> rw [abs_le] <;> constructor <;> dsimp <;> linarith
lemma tubes_parallel_true (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hh1 : h<1)
    (a b c d : ℤ) (hne : (a,b)≠(c,d)) {x : Point}
    (hx : x∈tube h ((a,b),true)) (hy : x∈tube h ((c,d),true)) :
    ∃ v, v∈endpoints ((a,b),true) ∧ v∈endpoints ((c,d),true) ∧ x∈box j h v := by
  change (a : ℝ)+b≤x.1 ∧ x.1≤(a : ℝ)+b+1 ∧ |x.2-(x.1-2*(b : ℝ))|≤h at hx
  change (c : ℝ)+d≤x.1 ∧ x.1≤(c : ℝ)+d+1 ∧ |x.2-(x.1-2*(d : ℝ))|≤h at hy
  rw [abs_le] at hx hy
  have hb : b=d := int_eq_of_close _ _ (by linarith) (by linarith)
  subst d
  have ha : a≠c := by intro h; subst c; exact hne rfl
  have hab : a=c+1 ∨ c=a+1 := by
    have h1 : a≤c+1 := by exact_mod_cast (show (a : ℝ)≤c+1 by linarith)
    have h2 : c≤a+1 := by exact_mod_cast (show (c : ℝ)≤a+1 by linarith)
    omega
  rcases hab with rfl|rfl
  · refine ⟨(c+1,b),by simp [endpoints,source,target],by simp [endpoints,source,target],?_⟩
    push_cast at hx hy
    constructor <;> rw [abs_le] <;> constructor <;> push_cast <;> linarith
  · refine ⟨(a+1,b),by simp [endpoints,source,target],by simp [endpoints,source,target],?_⟩
    push_cast at hx hy
    constructor <;> rw [abs_le] <;> constructor <;> push_cast <;> linarith
lemma tubes_parallel_false (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hh1 : h<1)
    (a b c d : ℤ) (hne : (a,b)≠(c,d)) {x : Point}
    (hx : x∈tube h ((a,b),false)) (hy : x∈tube h ((c,d),false)) :
    ∃ v, v∈endpoints ((a,b),false) ∧ v∈endpoints ((c,d),false) ∧ x∈box j h v := by
  change (a : ℝ)+b≤x.1 ∧ x.1≤(a : ℝ)+b+1 ∧ |x.2-(2*(a : ℝ)-x.1)|≤h at hx
  change (c : ℝ)+d≤x.1 ∧ x.1≤(c : ℝ)+d+1 ∧ |x.2-(2*(c : ℝ)-x.1)|≤h at hy
  rw [abs_le] at hx hy
  have ha : a=c := int_eq_of_close _ _ (by linarith) (by linarith)
  subst c
  have hb : b≠d := by intro h; subst d; exact hne rfl
  have hbd : b=d+1 ∨ d=b+1 := by
    have h1 : b≤d+1 := by exact_mod_cast (show (b : ℝ)≤d+1 by linarith)
    have h2 : d≤b+1 := by exact_mod_cast (show (d : ℝ)≤b+1 by linarith)
    omega
  rcases hbd with rfl|rfl
  · refine ⟨(a,d+1),by simp [endpoints,source,target],by simp [endpoints,source,target],?_⟩
    push_cast at hx hy
    constructor <;> rw [abs_le] <;> constructor <;> push_cast <;> linarith
  · refine ⟨(a,b+1),by simp [endpoints,source,target],by simp [endpoints,source,target],?_⟩
    push_cast at hx hy
    constructor <;> rw [abs_le] <;> constructor <;> push_cast <;> linarith
lemma distinct_tubes_intersection (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hh1 : h<1)
    {e f : Edge} (hne : e≠f) {x : Point} (hx : x∈tube h e) (hy : x∈tube h f) :
    ∃ v, v∈endpoints e ∧ v∈endpoints f ∧ x∈box j h v := by
  obtain ⟨⟨a,b⟩,s⟩ := e
  obtain ⟨⟨c,d⟩,t⟩ := f
  cases s <;> cases t
  · exact tubes_parallel_false j h hh hhj hh1 a b c d (by intro he; exact hne (congrArg (fun z => (z,false)) he)) hx hy
  · obtain ⟨v,hv,hv',hb⟩ := tubes_opposite j h hh hhj hh1 c d a b hy hx
    exact ⟨v,hv',hv,hb⟩
  · exact tubes_opposite j h hh hhj hh1 a b c d hx hy
  · exact tubes_parallel_true j h hh hhj hh1 a b c d (by intro he; exact hne (congrArg (fun z => (z,true)) he)) hx hy
lemma box_domain_endpoint (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {v : Site} {e : Edge} {x : Point} (hx : x∈box j h v) (hy : x∈domain j h e) :
    v∈endpoints e := by
  rcases hy with (hy|hy)|hy
  · have he : v=source e := by
      by_contra he
      exact Set.disjoint_left.mp (box_disjoint j h hs he) hx hy
    simp [endpoints,he]
  · have he : v=target e := by
      by_contra he
      exact Set.disjoint_left.mp (box_disjoint j h hs he) hx hy
    simp [endpoints,he]
  · exact (box_tube_endpoint j h (by linarith) (by linarith) hx hy)
theorem distinct_domains_intersection (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {e f : Edge} (hne : e≠f) {x : Point} (hx : x∈domain j h e) (hy : x∈domain j h f) :
    ∃ v, v∈endpoints e ∧ v∈endpoints f ∧ x∈box j h v := by
  rcases hx with (hx|hx)|hx
  · exact ⟨source e,by simp [endpoints],box_domain_endpoint j h hh hhj hs hx hy,hx⟩
  · exact ⟨target e,by simp [endpoints],box_domain_endpoint j h hh hhj hs hx hy,hx⟩
  · rcases hy with (hy|hy)|hy
    · exact ⟨source f,box_domain_endpoint j h hh hhj hs hy (Or.inr hx),by simp [endpoints],hy⟩
    · exact ⟨target f,box_domain_endpoint j h hh hhj hs hy (Or.inr hx),by simp [endpoints],hy⟩
    · exact distinct_tubes_intersection j h hh hhj (by linarith) hne hx hy
lemma nonincident_domains_disjoint (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {e f : Edge} (he : Disjoint (endpoints e) (endpoints f)) :
    Disjoint (domain j h e) (domain j h f) := by
  have hne : e≠f := by
    intro hh
    subst f
    exact Set.disjoint_left.mp he (show source e∈endpoints e by simp [endpoints])
      (by simp [endpoints])
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨v,hv,hv',_⟩ := distinct_domains_intersection j h hh hhj hs hne hx hy
  exact Set.disjoint_left.mp he hv hv'
lemma nonendpoint_domain_box_disjoint (j h : ℝ) (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {e : Edge} {v : Site} (hv : v∉endpoints e) : Disjoint (box j h v) (domain j h e) := by
  exact Set.disjoint_left.mpr fun _ hx hy => hv (box_domain_endpoint j h hh hhj hs hx hy)
end CriticalPercolation.Corridor
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.GraphGeometry.LatticeGrowth
section

namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical
namespace CriticalPercolation.Corridor
open Boundary
def slotSite (n : ℕ) : Site := ((Nat.unpair n).1,(Nat.unpair n).2)
lemma slotSite_quadrant (n : ℕ) : quadrant (slotSite n) := by
  exact ⟨Int.natCast_nonneg _,Int.natCast_nonneg _⟩
lemma gridSlot_slotSite (n : ℕ) : gridSlot (slotSite n)=n := by
  simp [gridSlot,slotSite]
lemma slotSite_gridSlot (v : Site) (hv : quadrant v) : slotSite (gridSlot v)=v := by
  apply gridSlot_injective (slotSite_quadrant _) hv
  exact gridSlot_slotSite _
lemma parent_slot_lt (e : Edge) (h : quadrant (source e)) :
    gridSlot (source e)<gridSlot (target e) := by
  obtain ⟨v,b⟩ := e
  cases b with
  | true => exact gridSlot_east v h
  | false => exact gridSlot_north v h
lemma target_quadrant (e : Edge) (h : quadrant (source e)) : quadrant (target e) := by
  obtain ⟨⟨a,b⟩,s⟩ := e
  change 0≤a ∧ 0≤b at h
  cases s <;> dsimp [target,quadrant] <;> omega
def incoming (n : ℕ) (S : Finset Site) : Option Edge :=
  if (slotSite n-(1,0))∈S then some (slotSite n-(1,0),true)
  else if (slotSite n-(0,1))∈S then some (slotSite n-(0,1),false) else none
lemma incoming_source {n : ℕ} {S : Finset Site} {e : Edge}
    (h : incoming n S=some e) : source e∈S := by
  unfold incoming at h
  split_ifs at h with hw hn
  · have he := Option.some.inj h
    subst e
    exact hw
  · have he := Option.some.inj h
    subst e
    exact hn
lemma incoming_target {n : ℕ} {S : Finset Site} {e : Edge}
    (h : incoming n S=some e) : target e=slotSite n := by
  unfold incoming at h
  split_ifs at h with hw hn
  · have he := Option.some.inj h
    subst e
    simp [target]
  · have he := Option.some.inj h
    subst e
    simp [target]
lemma incoming_exists (n : ℕ) (S : Finset Site)
    (h : ∃ y∈S, slotSite n=y+(1,0) ∨ slotSite n=y+(0,1)) :
    ∃ e, incoming n S=some e := by
  unfold incoming
  split_ifs with hw hn
  · exact ⟨_,rfl⟩
  · exact ⟨_,rfl⟩
  · obtain ⟨y,hy,he|he⟩ := h
    · exact (hw (by rwa [he,add_sub_cancel_right])).elim
    · exact (hn (by rwa [he,add_sub_cancel_right])).elim
structure GrowthState where
  good : Finset Site
  seen : Finset Edge
def GrowthState.initial : GrowthState := ⟨{(0,0)},∅⟩
def GrowthState.advance (n : ℕ) (S : GrowthState) (b : Bool) : GrowthState where
  good := if (incoming n S.good).isSome ∧ b=true then insert (slotSite n) S.good else S.good
  seen := S.seen∪(incoming n S.good).toFinset
lemma GrowthState.good_mono (n : ℕ) (S : GrowthState) (b : Bool) :
    S.good⊆(S.advance n b).good := by
  dsimp [advance]
  split_ifs <;> intro v hv
  · exact Finset.mem_insert_of_mem hv
  · exact hv
lemma GrowthState.seen_mono (n : ℕ) (S : GrowthState) (b : Bool) :
    S.seen⊆(S.advance n b).seen := Finset.subset_union_left
def GrowthState.Valid (n : ℕ) (S : GrowthState) : Prop :=
  (0,0)∈S.good ∧
  (∀ v∈S.good, quadrant v ∧ (v=(0,0) ∨ gridSlot v<n)) ∧
  (∀ e∈S.seen, source e∈S.good ∧ gridSlot (target e)<n)
lemma GrowthState.initial_valid : GrowthState.initial.Valid 0 := by
  refine ⟨by simp [initial],?_,by simp [initial]⟩
  intro v hv
  have he : v=(0,0) := by simpa [initial] using hv
  subst v
  exact ⟨by norm_num [quadrant],Or.inl rfl⟩
lemma GrowthState.advance_valid (n : ℕ) (S : GrowthState) (b : Bool)
    (h : S.Valid n) : (S.advance n b).Valid (n+1) := by
  refine ⟨S.good_mono n b h.1,?_,?_⟩
  · intro v hv
    change v∈(if (incoming n S.good).isSome ∧ b=true then insert (slotSite n) S.good else S.good) at hv
    split_ifs at hv with ha
    · rcases Finset.mem_insert.mp hv with rfl|hv
      · exact ⟨slotSite_quadrant n,Or.inr (by rw [gridSlot_slotSite]; omega)⟩
      · exact ⟨(h.2.1 v hv).1,(h.2.1 v hv).2.imp_right (fun hh => by omega)⟩
    · exact ⟨(h.2.1 v hv).1,(h.2.1 v hv).2.imp_right (fun hh => by omega)⟩
  · intro e he
    rcases Finset.mem_union.mp he with he|he
    · exact ⟨S.good_mono n b (h.2.2 e he).1,by have hh := (h.2.2 e he).2; omega⟩
    · have hei : incoming n S.good=some e := by simpa using he
      exact ⟨S.good_mono n b (incoming_source hei),by rw [incoming_target hei,gridSlot_slotSite]; omega⟩
lemma GrowthState.seen_intersection (n : ℕ) (S : GrowthState) (h : S.Valid n)
    {e : Edge} (ht : n ≤ gridSlot (target e)) :
    e∉S.seen ∧ ∀ f∈S.seen, endpoints f∩endpoints e⊆{source e} := by
  refine ⟨fun hei => (Nat.not_lt_of_ge ht) (h.2.2 e hei).2,?_⟩
  intro f hf v hv
  have hfs := (h.2.1 (source f) (h.2.2 f hf).1).1
  have hft := (h.2.2 f hf).2
  have hfst := parent_slot_lt f hfs
  rcases hv.1 with rfl|hvf <;> rcases hv.2 with hve|hve
  · exact hve
  · have heq : source f=target e := hve
    rw [heq] at hfst
    omega
  · exact hve
  · have heq : target f=target e := hvf.symm.trans hve
    rw [heq] at hft
    omega
def GrowthState.Covered (S : GrowthState) : Prop :=
  ∀ v∈S.good, v=(0,0) ∨ ∃ e∈S.seen, target e=v
lemma GrowthState.initial_covered : GrowthState.initial.Covered := by
  intro v hv
  exact Or.inl (by simpa [initial] using hv)
lemma GrowthState.advance_covered (n : ℕ) (S : GrowthState) (b : Bool)
    (h : S.Covered) : (S.advance n b).Covered := by
  intro v hv
  change v∈(if (incoming n S.good).isSome ∧ b=true then insert (slotSite n) S.good else S.good) at hv
  have hold : ∀ v∈S.good, v=(0,0) ∨ ∃ e∈(S.advance n b).seen, target e=v := by
    intro v hv
    rcases h v hv with hv|⟨e,he,hv⟩
    · exact Or.inl hv
    · exact Or.inr ⟨e,S.seen_mono n b he,hv⟩
  split_ifs at hv with ha
  · rcases Finset.mem_insert.mp hv with rfl|hv
    · obtain ⟨e,he⟩ := Option.isSome_iff_exists.mp ha.1
      exact Or.inr ⟨e,Finset.mem_union.mpr (Or.inr (by simp [he])),incoming_target he⟩
    · exact hold v hv
  · exact hold v hv
lemma GrowthState.outgoing_nonincident (n : ℕ) (S : GrowthState) (h : S.Valid n)
    {e : Edge} (he : source e=slotSite n) {f : Edge} (hf : f∈S.seen) :
    Disjoint (endpoints f) (endpoints e) := by
  have hq := (h.2.1 _ (h.2.2 f hf).1).1
  have hf1 := parent_slot_lt f hq
  have hf2 := (h.2.2 f hf).2
  have he1 := parent_slot_lt e (he ▸ slotSite_quadrant n)
  have he2 : gridSlot (source e)=n := by rw [he,gridSlot_slotSite]
  apply Set.disjoint_left.mpr
  intro v hv hw
  rcases hv with hv|hv <;> rcases hw with hw|hw
  · have hh : source f=source e := hv.symm.trans hw
    rw [hh,he2] at hf1
    omega
  · have hh : source f=target e := hv.symm.trans hw
    rw [hh] at hf1
    omega
  · have hh : target f=source e := hv.symm.trans hw
    rw [hh,he2] at hf2
    omega
  · have hh : target f=target e := hv.symm.trans hw
    rw [hh] at hf2
    omega
end CriticalPercolation.Corridor
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.CollarDistance
section

namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)
def vertexCollar (B : Set V) (n : ℕ) : Set V := ⋃ b∈B, G.vertexBall b n
def distanceTo (B : Set V) (v : V) : ℕ :=
  if h : ∃ n, v∈G.vertexCollar B n then Nat.find h else 0
lemma vertexCollar_exists (hc : G.fullGraph.Connected) {B : Set V} (hB : B.Nonempty) (v : V) :
    ∃ n, v∈G.vertexCollar B n := by
  obtain ⟨b,hb⟩ := hB
  obtain ⟨n,hn⟩ := G.reachable_mem_vertexBall (hc b v)
  exact ⟨n,Set.mem_iUnion₂.mpr ⟨b,hb,hn⟩⟩
lemma distanceTo_mem {B : Set V} {v : V} (h : ∃ n, v∈G.vertexCollar B n) :
    v∈G.vertexCollar B (G.distanceTo B v) := by
  simp only [distanceTo,dif_pos h]
  exact Nat.find_spec h
lemma distanceTo_le {B : Set V} {v : V} {n : ℕ} (h : v∈G.vertexCollar B n) :
    G.distanceTo B v ≤ n := by
  have he : ∃ k, v∈G.vertexCollar B k := ⟨n,h⟩
  simp only [distanceTo,dif_pos he]
  exact Nat.find_min' he h
lemma distanceTo_le_iff (hc : G.fullGraph.Connected) {B : Set V} (hB : B.Nonempty)
    (v : V) (n : ℕ) : G.distanceTo B v ≤ n ↔ v∈G.vertexCollar B n := by
  constructor
  · intro hn
    obtain ⟨b,hb,hv⟩ := Set.mem_iUnion₂.mp (G.distanceTo_mem (G.vertexCollar_exists hc hB v))
    have hmono : Monotone (G.vertexBall b) :=
      monotone_nat_of_le_succ fun _ => Set.subset_union_left
    exact Set.mem_iUnion₂.mpr ⟨b,hb,hmono hn hv⟩
  · exact G.distanceTo_le
lemma distanceTo_eq_zero_iff (hc : G.fullGraph.Connected) {B : Set V} (hB : B.Nonempty)
    (v : V) : G.distanceTo B v=0 ↔ v∈B := by
  rw [← Nat.le_zero,G.distanceTo_le_iff hc hB]
  simp [vertexCollar,vertexBall]
lemma distanceTo_adj (hc : G.fullGraph.Connected) {B : Set V} (hB : B.Nonempty)
    {v w : V} (hvw : G.fullGraph.Adj v w) : G.distanceTo B w ≤ G.distanceTo B v+1 := by
  obtain ⟨b,hb,hv⟩ := Set.mem_iUnion₂.mp (G.distanceTo_mem (G.vertexCollar_exists hc hB v))
  apply G.distanceTo_le
  exact Set.mem_iUnion₂.mpr ⟨b,hb,Or.inr (Set.mem_iUnion₂.mpr ⟨v,hv,hvw⟩)⟩
lemma distanceTo_ball (hc : G.fullGraph.Connected) {B : Set V} (hB : B.Nonempty)
    {v w : V} {n : ℕ} (hvw : w∈G.vertexBall v n) : G.distanceTo B w ≤ G.distanceTo B v+n := by
  induction n generalizing w with
  | zero =>
    have he : w=v := hvw
    subst w
    exact Nat.le_refl _
  | succ n ih =>
    rcases hvw with hvw|hvw
    · exact (ih hvw).trans (by omega)
    · obtain ⟨z,hz,hzw⟩ := Set.mem_iUnion₂.mp hvw
      have h1 := ih hz
      have h2 := G.distanceTo_adj hc hB hzw
      omega
lemma distanceTo_predecessor (hc : G.fullGraph.Connected) {B : Set V} (hB : B.Nonempty)
    (v : V) (hv : G.distanceTo B v≠0) :
    ∃ w, G.fullGraph.Adj v w ∧ G.distanceTo B w+1=G.distanceTo B v := by
  obtain ⟨n,heq⟩ := Nat.exists_eq_succ_of_ne_zero hv
  have hmem := G.distanceTo_mem (G.vertexCollar_exists hc hB v)
  rw [heq] at hmem
  obtain ⟨b,hb,hv⟩ := Set.mem_iUnion₂.mp hmem
  rcases hv with hv|hv
  · have hh : v∈G.vertexCollar B n := Set.mem_iUnion₂.mpr ⟨b,hb,hv⟩
    have := G.distanceTo_le hh
    omega
  · obtain ⟨w,hw,hwv⟩ := Set.mem_iUnion₂.mp hv
    have h1 := G.distanceTo_le (B := B) (Set.mem_iUnion₂.mpr ⟨b,hb,hw⟩)
    have h2 := G.distanceTo_adj hc hB hwv
    exact ⟨w,hwv.symm,by omega⟩
end CriticalPercolation.BondGraph
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.GraphGeometry.OpenGraphIso
section

namespace OAI
section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
open Set MeasureTheory ProbabilityTheory
open scoped Classical
namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}
end CriticalPercolation.BernoulliProduct
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)
instance law_probability (p : unitInterval) : IsProbabilityMeasure (G.law p) := by
  unfold law
  infer_instance
lemma Aut.adj_map (φ : G.Aut) (ω : Set E) (v w : V) :
    (G.openGraph (φ.edge '' ω)).Adj (φ.vertex v) (φ.vertex w) ↔
      (G.openGraph ω).Adj v w := by
  simp only [openGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_image]
  constructor
  · rintro ⟨⟨e, ⟨f, hf, rfl⟩, hend⟩, hne⟩
    rw [φ.preserves, ← Sym2.map_mk] at hend
    exact ⟨⟨f, hf, Sym2.map.injective φ.vertex.injective hend⟩,
      fun h => hne (congrArg φ.vertex h)⟩
  · rintro ⟨⟨e, he, hend⟩, hne⟩
    refine ⟨⟨φ.edge e, ⟨e, he, rfl⟩, ?_⟩, ?_⟩
    · rw [φ.preserves, hend, Sym2.map_mk]
    · exact fun h => hne (φ.vertex.injective h)
end CriticalPercolation.BondGraph
open Filter Topology
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls
section

namespace OAI
section
section
noncomputable section
open Set
open scoped Classical
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)
lemma vertexBall_mono (o : V) : Monotone (G.vertexBall o) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Set.subset_union_left
lemma mem_vertexBall_self (o : V) (n : ℕ) : o ∈ G.vertexBall o n :=
  G.vertexBall_mono o (Nat.zero_le n) rfl
lemma vertexBall_step {o v w : V} {n : ℕ} (hv : v ∈ G.vertexBall o n)
    (he : G.fullGraph.Adj v w) : w ∈ G.vertexBall o (n+1) :=
  Or.inr (Set.mem_iUnion₂.mpr ⟨v,hv,he⟩)
lemma vertexBall_add {o v : V} {n : ℕ} (hv : v ∈ G.vertexBall o n) (m : ℕ) :
    G.vertexBall v m ⊆ G.vertexBall o (n+m) := by
  induction m with
  | zero => simpa only [vertexBall,Nat.add_zero,Set.singleton_subset_iff] using hv
  | succ m ih =>
    rintro w (hw | hw)
    · exact G.vertexBall_mono o (by omega) (ih hw)
    · obtain ⟨z,hz,hzw⟩ := Set.mem_iUnion₂.mp hw
      exact G.vertexBall_step (ih hz) hzw
lemma vertexBall_comm {o v : V} {n : ℕ} : v ∈ G.vertexBall o n ↔ o ∈ G.vertexBall v n := by
  have h : ∀ n (o v : V), v ∈ G.vertexBall o n → o ∈ G.vertexBall v n := by
    intro n
    induction n with
    | zero => intro o v hv; simpa only [vertexBall,Set.mem_singleton_iff] using hv.symm
    | succ n ih =>
      intro o v hv
      rcases hv with hv | hv
      · exact G.vertexBall_mono v (Nat.le_succ n) (ih o v hv)
      · obtain ⟨z,hz,hzv⟩ := Set.mem_iUnion₂.mp hv
        have h1 : z ∈ G.vertexBall v 1 := G.vertexBall_step (G.mem_vertexBall_self v 0) hzv.symm
        simpa only [Nat.add_comm 1] using G.vertexBall_add h1 n (ih o z hz)
  exact ⟨h n o v,h n v o⟩
lemma Aut.fullGraph_adj (φ : G.Aut) (u v : V) :
    G.fullGraph.Adj (φ.vertex u) (φ.vertex v) ↔ G.fullGraph.Adj u v := by
  simpa only [fullGraph,Set.image_univ,Equiv.range_eq_univ] using Aut.adj_map G φ Set.univ u v
lemma Aut.vertexBall_mem (φ : G.Aut) (o v : V) (n : ℕ) :
    φ.vertex v ∈ G.vertexBall (φ.vertex o) n ↔ v ∈ G.vertexBall o n := by
  induction n generalizing v with
  | zero => simp only [vertexBall,Set.mem_singleton_iff,φ.vertex.injective.eq_iff]
  | succ n ih =>
    simp only [vertexBall,Set.mem_union,Set.mem_iUnion,exists_prop,SimpleGraph.mem_neighborSet]
    constructor
    · rintro (h | ⟨z,hz,hzv⟩)
      · exact Or.inl ((ih v).mp h)
      · obtain ⟨w,rfl⟩ := φ.vertex.surjective z
        exact Or.inr ⟨w,(ih w).mp hz,
          (Aut.fullGraph_adj G φ w v).mp hzv⟩
    · rintro (h | ⟨z,hz,hzv⟩)
      · exact Or.inl ((ih v).mpr h)
      · exact Or.inr ⟨φ.vertex z,(ih z).mpr hz,(Aut.fullGraph_adj G φ z v).mpr hzv⟩
lemma Aut.vertexBall_image (φ : G.Aut) (o : V) (n : ℕ) :
    φ.vertex '' G.vertexBall o n = G.vertexBall (φ.vertex o) n := by
  ext v
  obtain ⟨w,rfl⟩ := φ.vertex.surjective v
  simpa only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right] using
    (Aut.vertexBall_mem G φ o w n).symm
lemma Aut.vertexBall_ncard (φ : G.Aut) (o : V) (n : ℕ) :
    (G.vertexBall (φ.vertex o) n).ncard = (G.vertexBall o n).ncard := by
  rw [← Aut.vertexBall_image G φ,Set.ncard_image_of_injective _ φ.vertex.injective]
lemma Aut.incident_singleton_image (φ : G.Aut) (v : V) :
    φ.edge '' G.incidentEdges {v} = G.incidentEdges {φ.vertex v} := by
  ext e
  obtain ⟨f,rfl⟩ := φ.edge.surjective e
  simp only [Set.mem_image,φ.edge.injective.eq_iff,exists_eq_right,incidentEdges,
    Set.mem_ofPred_eq,Set.mem_singleton_iff,exists_eq_left,φ.preserves]
  simp only [Sym2.mem_map,φ.vertex.injective.eq_iff,exists_eq_right]
lemma uniform_incident_bound (hquasi : G.QuasiTransitive) :
    ∃ D : ℕ, 1≤D ∧ ∀ v, (G.incidentEdges {v}).ncard ≤ D := by
  obtain ⟨S,hS,hcover⟩ := hquasi
  let D := 1 + ∑ v ∈ hS.toFinset, (G.incidentEdges {v}).ncard
  refine ⟨D,by dsimp [D]; omega,?_⟩
  intro v
  obtain ⟨z,hz,φ,rfl⟩ := hcover v
  rw [← Aut.incident_singleton_image G φ,Set.ncard_image_of_injective _ φ.edge.injective]
  exact (Finset.single_le_sum (f := fun v => (G.incidentEdges {v}).ncard) (fun _ _ => Nat.zero_le _) (hS.mem_toFinset.mpr hz)).trans (Nat.le_add_left _ _)
lemma uniform_ball_bound (hquasi : G.QuasiTransitive) (n : ℕ) :
    ∃ M : ℕ, ∀ v, (G.vertexBall v n).ncard ≤ M := by
  obtain ⟨S,hS,hcover⟩ := hquasi
  refine ⟨∑ v ∈ hS.toFinset, (G.vertexBall v n).ncard,?_⟩
  intro v
  obtain ⟨z,hz,φ,rfl⟩ := hcover v
  rw [Aut.vertexBall_ncard G φ]
  exact Finset.single_le_sum (f := fun v => (G.vertexBall v n).ncard) (fun _ _ => Nat.zero_le _) (hS.mem_toFinset.mpr hz)
end CriticalPercolation.BondGraph
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.OpenTrialBound
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}
lemma law_allOpen (q : E → unitInterval) (S : Set E) (hS : S.Finite) :
    law q (allOpen S)=∏ e∈hS.toFinset, bitMeasure (q e) {True} := by
  have he : allOpen S=⋂ e∈hS.toFinset, {ω : Set E | (e∈ω)=True} := by
    ext ω
    simp [allOpen,Set.subset_def]
  rw [he,(independent_coordinates q).meas_biInter]
  · exact Finset.prod_congr rfl (fun e _ => law_coordinate q e True)
  · intro e _
    exact ⟨{True},MeasurableSet.singleton _,rfl⟩
lemma law_allOpen_lower (q : E → unitInterval) (S : Set E) (hS : S.Finite)
    (p : unitInterval) (N : ℕ) (hN : S.ncard ≤ N) (hq : ∀ e∈S, (p : ℝ) ≤ q e) :
    (p : ℝ)^N ≤ (law q).real (allOpen S) := by
  rw [measureReal_def,law_allOpen q S hS,ENNReal.toReal_prod]
  calc
    _ ≤ (p : ℝ)^S.ncard := pow_le_pow_of_le_one p.2.1 p.2.2 hN
    _ = ∏ e∈hS.toFinset, (p : ℝ) := by simp [Set.ncard_eq_toFinset_card S hS]
    _ ≤ _ := by
      apply Finset.prod_le_prod
      · intro edge hedge; exact p.2.1
      · intro e he
        change (p : ℝ) ≤ (bitMeasure (q e)).real {True}
        rw [bitMeasure_real_singleton]
        simpa only [bitWeight,if_pos True.intro] using hq e (hS.mem_toFinset.mp he)
end BernoulliProduct
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)
lemma vertexBalls_disjoint {v w : V} {n : ℕ} (h : w∉G.vertexBall v (n+n)) :
    Disjoint (G.vertexBall v n) (G.vertexBall w n) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  exact h (G.vertexBall_add hz n (G.vertexBall_comm.mp hz'))
lemma inducedEdges_disjoint {S T : Set V} (h : Disjoint S T) :
    Disjoint (G.inducedEdges S) (G.inducedEdges T) := by
  apply Set.disjoint_left.mpr
  intro e he he'
  obtain ⟨⟨x,y⟩,hxy⟩ := Sym2.mk_surjective (G.ends e)
  have hx : x∈G.ends e := by rw [← hxy]; simp
  exact Set.disjoint_left.mp h (he x hx) (he' x hx)
lemma inward_trials_disjoint (F : V → Set E) (m : ℕ)
    (hF : ∀ v, F v⊆G.inducedEdges (G.vertexBall v (2*m+1)))
    {v w : V} (h : w∉G.vertexBall v (4*m+2)) : Disjoint (F v) (F w) := by
  have h' : w∉G.vertexBall v ((2*m+1)+(2*m+1)) := by
    simpa only [show (2*m+1)+(2*m+1)=4*m+2 by omega] using h
  exact (G.inducedEdges_disjoint (G.vertexBalls_disjoint h')).mono (hF v) (hF w)
end BondGraph
end CriticalPercolation
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.CorridorGraph
section

namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)
lemma coordinate_ball_bound (f : V → ℝ) (ρ : ℝ) (hρ : 0≤ρ)
    (hf : ∀ ⦃v w⦄, G.fullGraph.Adj v w → |f v-f w|≤ρ)
    {v w : V} {n : ℕ} (hw : w∈G.vertexBall v n) : |f w-f v|≤n*ρ := by
  induction n generalizing w with
  | zero =>
    have he : w=v := hw
    subst w
    simp
  | succ n ih =>
    rcases hw with hw|hw
    · exact (ih hw).trans (by push_cast; nlinarith)
    · obtain ⟨u,hu,huw⟩ := Set.mem_iUnion₂.mp hw
      calc
        |f w-f v| ≤ |f w-f u|+|f u-f v| := abs_sub_le _ _ _
        _ ≤ ρ+n*ρ := add_le_add (hf huw.symm) (ih hu)
        _ = _ := by push_cast; ring
lemma coordinate_collar_bound (f : V → ℝ) (ρ : ℝ) (hρ : 0≤ρ)
    (hf : ∀ ⦃v w⦄, G.fullGraph.Adj v w → |f v-f w|≤ρ)
    (B : Set V) (c r : ℝ) (hB : ∀ v∈B, |f v-c|≤r)
    {w : V} {n : ℕ} (hw : w∈G.vertexCollar B n) : |f w-c|≤r+n*ρ := by
  obtain ⟨v,hv,hw⟩ := Set.mem_iUnion₂.mp hw
  calc
    |f w-c| ≤ |f w-f v|+|f v-c| := abs_sub_le _ _ _
    _ ≤ n*ρ+r := add_le_add (G.coordinate_ball_bound f ρ hρ hf hw) (hB v hv)
    _ = _ := add_comm _ _
lemma inducedEdges_mono {S T : Set V} (h : S⊆T) :
    G.inducedEdges S⊆G.inducedEdges T := by
  intro e he v hv
  exact h (he v hv)
end CriticalPercolation.BondGraph
namespace CriticalPercolation.Corridor
open BondGraph
variable {V E : Type*} (G : BondGraph V E) (ξ : V → Point) (j h : ℝ)
def graphBox (v : Site) : Set V := ξ ⁻¹' box j h v
def graphDomain (e : Edge) : Set V := ξ ⁻¹' domain j h e
def boxEdges (v : Site) : Set E := G.inducedEdges (graphBox ξ j h v)
def corridorEdges (e : Edge) : Set E := G.inducedEdges (graphDomain ξ j h e)
lemma graph_boxes_disjoint (hs : 2*j+h<1) {v w : Site} (hv : v≠w) :
    Disjoint (graphBox ξ j h v) (graphBox ξ j h w) :=
  (box_disjoint j h hs hv).preimage ξ
lemma graph_nonincident_disjoint (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {e f : Edge} (hef : Disjoint (endpoints e) (endpoints f)) :
    Disjoint (graphDomain ξ j h e) (graphDomain ξ j h f) :=
  (nonincident_domains_disjoint j h hh hhj hs hef).preimage ξ
lemma edge_nonincident_disjoint (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {e f : Edge} (hef : Disjoint (endpoints e) (endpoints f)) :
    Disjoint (corridorEdges G ξ j h e) (corridorEdges G ξ j h f) :=
  G.inducedEdges_disjoint (graph_nonincident_disjoint ξ j h hh hhj hs hef)
lemma edge_box_disjoint (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    {e : Edge} {v : Site} (hv : v∉endpoints e) :
    Disjoint (boxEdges G ξ j h v) (corridorEdges G ξ j h e) :=
  G.inducedEdges_disjoint
    ((nonendpoint_domain_box_disjoint j h hh hhj hs hv).preimage ξ)
lemma history_disjoint (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    (H : Set Edge) {e : Edge} (he : ∀ f∈H, Disjoint (endpoints f) (endpoints e)) :
    Disjoint (⋃ f∈H, corridorEdges G ξ j h f) (corridorEdges G ξ j h e) := by
  apply Set.disjoint_left.mpr
  intro b hb he'
  obtain ⟨f,hf,hb⟩ := Set.mem_iUnion₂.mp hb
  exact Set.disjoint_left.mp (edge_nonincident_disjoint G ξ j h hh hhj hs (he f hf)) hb he'
lemma history_intersection_subset (hh : 0≤h) (hhj : h≤j) (hs : 2*j+h<1)
    (H : Set Edge) {e : Edge} {v : Site}
    (he : e∉H) (hH : ∀ f∈H, endpoints f∩endpoints e⊆{v}) :
    (⋃ f∈H, corridorEdges G ξ j h f)∩corridorEdges G ξ j h e⊆boxEdges G ξ j h v := by
  intro b hb
  obtain ⟨f,hf,hbf⟩ := Set.mem_iUnion₂.mp hb.1
  have hne : f≠e := fun h => he (h ▸ hf)
  intro w hw
  obtain ⟨u,hu,hu',hwu⟩ := distinct_domains_intersection j h hh hhj hs hne
    (hbf w hw) (hb.2 w hw)
  have huv : u=v := hH f hf ⟨hu,hu'⟩
  rwa [huv] at hwu
end CriticalPercolation.Corridor
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Exploration.GrowthHistoryGeometry
section

namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical
namespace CriticalPercolation.Corridor
open BondGraph Boundary
variable {V E : Type*} (G : BondGraph V E) (ξ : V → Point) (j h : ℝ)
def revealed (S : GrowthState) : Set E :=
  boxEdges G ξ j h (0,0)∪⋃ e∈S.seen, corridorEdges G ξ j h e
lemma revealed_mono {S T : GrowthState} (hST : S.seen⊆T.seen) :
    revealed G ξ j h S⊆revealed G ξ j h T := by
  apply Set.union_subset_union_right
  intro b hb
  obtain ⟨e,he,hb⟩ := Set.mem_iUnion₂.mp hb
  exact Set.mem_iUnion₂.mpr ⟨e,hST he,hb⟩
lemma boxEdges_subset_corridor_target (e : Edge) :
    boxEdges G ξ j h (target e)⊆corridorEdges G ξ j h e := by
  intro b hb v hv
  exact Or.inl (Or.inr (hb v hv))
lemma good_box_revealed {S : GrowthState} (hs : S.Covered) {v : Site} (hv : v∈S.good) :
    boxEdges G ξ j h v⊆revealed G ξ j h S := by
  rcases hs v hv with rfl|⟨e,he,rfl⟩
  · exact Set.subset_union_left
  · intro b hb
    exact Or.inr (Set.mem_iUnion₂.mpr ⟨e,he,boxEdges_subset_corridor_target G ξ j h e hb⟩)
lemma revealed_advance (n : ℕ) (S : GrowthState) (b : Bool) :
    revealed G ξ j h (S.advance n b)=revealed G ξ j h S∪
      ⋃ e∈(incoming n S.good).toFinset, corridorEdges G ξ j h e := by
  ext e
  constructor
  · rintro (he|he)
    · exact Or.inl (Or.inl he)
    · obtain ⟨f,hf,he⟩ := Set.mem_iUnion₂.mp he
      rcases Finset.mem_union.mp hf with hf|hf
      · exact Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨f,hf,he⟩))
      · exact Or.inr (Set.mem_iUnion₂.mpr ⟨f,hf,he⟩)
  · rintro ((he|he)|he)
    · exact Or.inl he
    · obtain ⟨f,hf,he⟩ := Set.mem_iUnion₂.mp he
      exact Or.inr (Set.mem_iUnion₂.mpr ⟨f,Finset.mem_union.mpr (Or.inl hf),he⟩)
    · obtain ⟨f,hf,he⟩ := Set.mem_iUnion₂.mp he
      exact Or.inr (Set.mem_iUnion₂.mpr ⟨f,Finset.mem_union.mpr (Or.inr hf),he⟩)
lemma revealed_incoming (n : ℕ) (S : GrowthState) (b : Bool) {e : Edge}
    (he : incoming n S.good=some e) :
    revealed G ξ j h (S.advance n b)=revealed G ξ j h S∪corridorEdges G ξ j h e := by
  rw [revealed_advance,he]
  simp
lemma later_revealed_intersection (hh : 0≤h) (hhj : h≤j) (hsep : 2*j+h<1)
    (n : ℕ) (S T : GrowthState) (hc : S.Covered) (hv : T.Valid n)
    {e : Edge} (hp : source e∈S.good) (ht : n ≤ gridSlot (target e)) :
    revealed G ξ j h T∩corridorEdges G ξ j h e⊆revealed G ξ j h S := by
  intro b hb
  rcases hb.1 with hb0|hbT
  · exact Or.inl hb0
  · have hh' := T.seen_intersection n hv ht
    have hh'' := history_intersection_subset G ξ j h hh hhj hsep (↑T.seen) hh'.1 hh'.2
    exact good_box_revealed G ξ j h hc hp (hh'' ⟨hbT,hb.2⟩)
lemma outgoing_unrevealed (hh : 0≤h) (hhj : h≤j) (hsep : 2*j+h<1)
    (n : ℕ) (S : GrowthState) (hv : S.Valid n) (hn : 0<n)
    {e : Edge} (he : source e=slotSite n) :
    Disjoint (revealed G ξ j h S) (corridorEdges G ξ j h e) := by
  apply Disjoint.sup_left
  · apply edge_box_disjoint G ξ j h hh hhj hsep
    intro hroot
    have he1 := parent_slot_lt e (he ▸ slotSite_quadrant n)
    have he2 : gridSlot (source e)=n := by rw [he,gridSlot_slotSite]
    rcases hroot with hh|hh
    · have he0 : gridSlot (source e)=0 := by rw [← hh]; rfl
      omega
    · have he0 : gridSlot (target e)=0 := by rw [← hh]; rfl
      omega
  · exact history_disjoint G ξ j h hh hhj hsep (↑S.seen)
      (fun f hf => S.outgoing_nonincident n hv he hf)
end CriticalPercolation.Corridor
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.PinnedTest
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}
lemma blockProbability_eq_pinnedLaw (q : E → unitInterval) (I σ : Set E)
    (A : Set (Set E)) (hA : MeasurableSet A) :
    blockProbability q I A σ=law (pinnedParameters q I σ) A := by
  rw [← forceOn_map_law,Measure.map_apply (measurable_forceOn I σ) hA]
  rfl
def predictionFailure (q : E → unitInterval) (F : Set E)
    (A C D : Set (Set E)) (δ : ℝ) : Set (Set E) :=
  Aᶜ ∪ (A∩{σ | (blockProbability q F C σ).toReal<1-δ}) ∪
    (A∩{σ | (blockProbability q F D σ).toReal<1-δ})
lemma measurableSet_predictionFailure (q : E → unitInterval) (F : Set E)
    (A C D : Set (Set E)) (hA : MeasurableSet[blockSigma F] A)
    (hC : MeasurableSet C) (hD : MeasurableSet D) (δ : ℝ) :
    MeasurableSet[blockSigma F] (predictionFailure q F A C D δ) := by
  exact (hA.compl.union (hA.inter (measurableSet_lt
    (measurable_blockProbability q F C hC).ennreal_toReal measurable_const))).union
    (hA.inter (measurableSet_lt
      (measurable_blockProbability q F D hD).ennreal_toReal measurable_const))
theorem pinned_prediction_failure (q : E → unitInterval) (I F σ : Set E)
    (hIF : I⊆F) (A C D : Set (Set E))
    (hA : MeasurableSet[blockSigma F] A) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (δ a : ℝ) (hδ : 0<δ)
    (hin : 1-δ ≤ (blockProbability q I A σ).toReal)
    (hCfail : (blockProbability q I (A\C) σ).toReal ≤ a)
    (hDfail : (blockProbability q I (A\D) σ).toReal ≤ a) :
    (blockProbability q I (predictionFailure q F A C D δ) σ).toReal ≤ δ+2*a/δ := by
  have hma := (blockSigma_le F) _ hA
  rw [blockProbability_eq_pinnedLaw q I σ A hma] at hin
  rw [blockProbability_eq_pinnedLaw q I σ (A\C) (hma.diff hC)] at hCfail
  rw [blockProbability_eq_pinnedLaw q I σ (A\D) (hma.diff hD)] at hDfail
  have hh := two_prediction_failure (pinnedParameters q I σ) F A C D hA hC hD δ a hδ
    hin hCfail hDfail
  simp_rw [blockProbability_pin_smaller q I F σ hIF C hC,
    blockProbability_pin_smaller q I F σ hIF D hD] at hh
  rw [blockProbability_eq_pinnedLaw q I σ _
    ((blockSigma_le F) _ (measurableSet_predictionFailure q F A C D hA hC hD δ))]
  exact hh
end CriticalPercolation.BernoulliProduct
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Criticality.GrowthProcess
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.Corridor
open BondGraph Boundary BernoulliProduct
structure Scheme (V E : Type*) where
  graph : BondGraph V E
  coordinate : V → Point
  j : ℝ
  h : ℝ
  seed : Set V
  mark : Site → Set V
  parameter : E → unitInterval
  delta : ℝ
namespace Scheme
variable {V E : Type*} [Countable V] [Countable E] (P : Scheme V E)
def block (S : GrowthState) : Set E := revealed P.graph P.coordinate P.j P.h S
def edgeDomain (e : Edge) : Set E := corridorEdges P.graph P.coordinate P.j P.h e
def enlarged (n : ℕ) (S : GrowthState) : Set E := P.block (S.advance n false)
def hit (v : Site) (R : Set E) : Set (Set E) := P.graph.restrictedSeed P.seed (P.mark v) R
def incomingHit (n : ℕ) (S : GrowthState) : Set (Set E) := P.hit (slotSite n) (P.enlarged n S)
def nextHit (n : ℕ) (S : GrowthState) (b : Bool) : Set (Set E) :=
  P.hit (target (slotSite n,b)) (P.enlarged n S∪P.edgeDomain (slotSite n,b))
def accepted (n : ℕ) (S : GrowthState) : Set (Set E) :=
  (predictionFailure P.parameter (P.enlarged n S) (P.incomingHit n S)
    (P.nextHit n S true) (P.nextHit n S false) P.delta)ᶜ
lemma accepted_measurable (n : ℕ) (S : GrowthState) :
    MeasurableSet[blockSigma (P.enlarged n S)] (P.accepted n S) :=
  (measurableSet_predictionFailure P.parameter (P.enlarged n S) _ _ _
    (P.graph.measurableSet_restrictedSeed _ _ _) (P.graph.restrictedSeed_measurable _ _ _)
    (P.graph.restrictedSeed_measurable _ _ _) P.delta).compl
omit [Countable V] [Countable E] in
lemma accepted_iff (n : ℕ) (S : GrowthState) (ω : Set E) :
    ω∈P.accepted n S ↔ ω∈P.incomingHit n S ∧
      ∀ b : Bool, 1-P.delta ≤ (blockProbability P.parameter (P.enlarged n S) (P.nextHit n S b) ω).toReal := by
  change (¬((ω∉P.incomingHit n S ∨ ω∈P.incomingHit n S ∧
    (blockProbability P.parameter (P.enlarged n S) (P.nextHit n S true) ω).toReal<1-P.delta) ∨
    ω∈P.incomingHit n S ∧
    (blockProbability P.parameter (P.enlarged n S) (P.nextHit n S false) ω).toReal<1-P.delta)) ↔ _
  constructor
  · intro h
    have ha : ω∈P.incomingHit n S := Classical.byContradiction (fun hn => h (Or.inl (Or.inl hn)))
    refine ⟨ha,fun b => ?_⟩
    cases b
    · exact not_lt.mp (fun hb => h (Or.inr ⟨ha,hb⟩))
    · exact not_lt.mp (fun hb => h (Or.inl (Or.inr ⟨ha,hb⟩)))
  · rintro ⟨ha,hb⟩ (h|h)
    · rcases h with h|h
      · exact h ha
      · exact not_lt_of_ge (hb true) h.2
    · exact not_lt_of_ge (hb false) h.2
def rule : DecisionRule E GrowthState where
  initial := GrowthState.initial
  block := P.block
  further := P.enlarged
  contained n S := revealed_mono P.graph P.coordinate P.j P.h (S.seen_mono n false)
  active n S := (incoming n S.good).isSome
  accept := P.accepted
  measurable := P.accepted_measurable
  update := GrowthState.advance
  block_update _ _ _ := rfl
lemma state_valid (n : ℕ) (w : DecisionCode n) : (P.rule.state n w).Valid n := by
  induction n with
  | zero => exact GrowthState.initial_valid
  | succ n ih => exact GrowthState.advance_valid n _ w.2 (ih w.1)
lemma state_covered (n : ℕ) (w : DecisionCode n) : (P.rule.state n w).Covered := by
  induction n with
  | zero => exact GrowthState.initial_covered
  | succ n ih => exact GrowthState.advance_covered n _ w.2 (ih w.1)
omit [Countable V] [Countable E] in
lemma block_enlarged (n : ℕ) (S : GrowthState) : P.block S⊆P.enlarged n S :=
  revealed_mono P.graph P.coordinate P.j P.h (S.seen_mono n false)
omit [Countable V] [Countable E] in
lemma enlarged_incoming (n : ℕ) (S : GrowthState) {e : Edge} (he : incoming n S.good=some e) :
    P.enlarged n S=P.block S∪P.edgeDomain e :=
  revealed_incoming P.graph P.coordinate P.j P.h n S false he
def rootEvent : Set (Set E) := {ω | ∀ b : Bool,
  1-P.delta ≤ (blockProbability P.parameter (P.block GrowthState.initial)
    (P.hit (target ((0,0),b)) (P.block GrowthState.initial∪P.edgeDomain ((0,0),b))) ω).toReal}
lemma rootEvent_measurable : MeasurableSet[blockSigma (P.block GrowthState.initial)] P.rootEvent := by
  simp only [rootEvent,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro b
  exact measurableSet_le measurable_const
    (measurable_blockProbability P.parameter _ _ (P.graph.restrictedSeed_measurable _ _ _)).ennreal_toReal
lemma rootEvent_history : MeasurableSet[(P.rule.partition 0).historySigma] P.rootEvent := by
  intro w
  change MeasurableSet[blockSigma (P.block GrowthState.initial)] (P.rootEvent∩Set.univ)
  simpa only [Set.inter_univ] using P.rootEvent_measurable
end Scheme
end CriticalPercolation.Corridor
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.RelayGeometry
section

namespace OAI
section
section
noncomputable section
open Set
open scoped Classical
namespace CriticalPercolation.Relay
def width (i : ℕ) : ℝ := max 2 (210-(i : ℝ)/2)
def selectedSign (u : ℝ) : ℝ := if 0 ≤ u then -1 else 1
def domain (J T σ : ℝ) : Set (ℝ×ℝ) :=
  {x | |x.1| ≤ J ∧ |x.2| ≤ J/4+630} ∪
  {x | |x.1-T| ≤ J ∧ |x.2-σ*T/4| ≤ J/4+630} ∪
  {x | 0 ≤ x.1 ∧ x.1 ≤ T ∧ |x.2-σ*x.1/4| ≤ 630}
lemma width_lower (i : ℕ) : 2 ≤ width i := le_max_left _ _
lemma width_upper (i : ℕ) : width i ≤ 210 := by
  apply max_le (by norm_num)
  linarith [Nat.cast_nonneg (α := ℝ) i]
lemma width_next (i : ℕ) : width i ≤ width (i+1)+1/2 := by
  have h1 := width_lower (i+1)
  have h2 : 210-((i+1 : ℕ) : ℝ)/2 ≤ width (i+1) := le_max_right _ _
  unfold width at h1 h2 ⊢
  push_cast at h1 h2 ⊢
  exact max_le (by linarith) (by linarith)
lemma width_last (L : ℕ) (hL : 416 ≤ L) : width L=2 := by
  apply max_eq_left
  have : (416 : ℝ) ≤ L := by exact_mod_cast hL
  linarith
lemma selectedSign_cases (u : ℝ) : selectedSign u=-1 ∨ selectedSign u=1 := by
  unfold selectedSign
  split  <;>  simp
lemma selectedSign_abs (u : ℝ) : |selectedSign u|=1 := by
  rcases selectedSign_cases u with h|h  <;>  rw [h]  <;>  norm_num
lemma move_towards_axis (u b : ℝ) (hu : |u| ≤ b) :
    |u+selectedSign u| ≤ max 1 (b-1) := by
  rw [abs_le] at hu ⊢
  have h1 : 1 ≤ max 1 (b-1) := le_max_left _ _
  have h2 : b-1 ≤ max 1 (b-1) := le_max_right _ _
  unfold selectedSign
  split  <;>  constructor  <;>  linarith
lemma full_step_height (i : ℕ) (u σ d e ε : ℝ) (hσ : |σ|=1)
    (hu : |u| ≤ width i+d) (hd₀ : 0 ≤ d) (hd : d+e/4 ≤ 1/4)
    (hε : |ε| ≤ e/4) :
    |u+selectedSign u-σ/4+ε| ≤ width (i+1) := by
  have h1 := width_lower (i+1)
  have h2 := width_next i
  have hs : |σ/4|=1/4 := by rw [abs_div,hσ]; norm_num
  calc
    _  ≤  |u+selectedSign u|+|σ/4|+|ε| :=
      by linarith [abs_add_le (u+selectedSign u-σ/4) ε, abs_sub (u+selectedSign u) (σ/4)]
    _  ≤  max 1 (width i+d-1)+1/4+e/4 := by
      rw [hs]
      linarith [move_towards_axis u (width i+d) hu]
    _  ≤  width (i+1) := by
      rcases le_total 1 (width i+d-1) with hh|hh
      · rw [max_eq_right hh]; linarith
      · rw [max_eq_left hh]; linarith
lemma full_step_time (i : ℕ) (y z d e : ℝ)
    (hy : |y-(i : ℝ)| ≤ (i+1)*e+d) (hz : |z-(y+1)| ≤ e/4)
    (hde : d+e/4 ≤ e) : |z-((i+1 : ℕ) : ℝ)| ≤ (i+2)*e := by
  rw [abs_le] at hy hz ⊢
  push_cast
  constructor  <;>  nlinarith
lemma path_axis_bound (L i : ℕ) (hi : i ≤ L) (y x : ℝ×ℝ) (d e σ : ℝ)
    (hσ : |σ|=1) (he : 0 ≤ e)
    (hyt : |y.1-(i : ℝ)| ≤ (i+1)*e+d)
    (hyz : |y.2-σ*(i : ℝ)/4| ≤ width i+d)
    (hxt : |x.1-y.1| ≤ 100) (hxz : |x.2-y.2| ≤ 100) :
    |x.2-σ*x.1/4| ≤ 210+d+100+((L+1)*e+d+100)/4 := by
  have ht : |x.1-(i : ℝ)| ≤ (L+1)*e+d+100 := by
    have hc : (i : ℝ) ≤ L := by exact_mod_cast hi
    calc
      _  ≤  |x.1-y.1|+|y.1-(i : ℝ)| := abs_sub_le _ _ _
      _  ≤  100+((i+1)*e+d) := add_le_add hxt hyt
      _  ≤  _ := by nlinarith
  have hsame : σ*(i : ℝ)/4-σ*x.1/4=σ*((i : ℝ)-x.1)/4 := by ring
  calc
    _  ≤  |x.2-y.2|+|y.2-σ*(i : ℝ)/4|+|σ*(i : ℝ)/4-σ*x.1/4| := by
      linarith [abs_sub_le x.2 (σ*(i : ℝ)/4) (σ*x.1/4),
        abs_sub_le x.2 y.2 (σ*(i : ℝ)/4)]
    _  ≤  100+(width i+d)+((L+1)*e+d+100)/4 := by
      rw [hsame,abs_div,abs_mul,hσ,one_mul,abs_of_pos (by norm_num : (0:ℝ) < 4),abs_sub_comm (i : ℝ)]
      exact add_le_add (add_le_add hxz hyz) (div_le_div_of_nonneg_right ht (by norm_num))
    _  ≤  _ := by linarith [width_upper i]
lemma band_mem_domain (J T σ : ℝ) (hσ : |σ|=1)
    (x : ℝ×ℝ) (ht : -J ≤ x.1 ∧ x.1 ≤ T+J)
    (hz : |x.2-σ*x.1/4| ≤ 630) : x∈domain J T σ := by
  have ha : |σ|=1 := hσ
  by_cases h0 : x.1 < 0
  · apply Or.inl; apply Or.inl
    have hx : |x.1| ≤ J := by rw [abs_of_neg h0]; linarith [ht.1]
    refine ⟨hx,?_⟩
    calc
      |x.2|  ≤  |x.2-σ*x.1/4|+|σ*x.1/4| := by simpa using abs_sub_le x.2 (σ*x.1/4) 0
      _  ≤  630+J/4 := by
        rw [abs_div,abs_mul,ha,one_mul,abs_of_pos (by norm_num : (0:ℝ) < 4)]
        exact add_le_add hz (div_le_div_of_nonneg_right hx (by norm_num))
      _ = _ := add_comm _ _
  · by_cases h1 : T < x.1
    · apply Or.inl; apply Or.inr
      have hx : |x.1-T| ≤ J := by rw [abs_of_pos (by linarith)]; linarith [ht.2]
      refine ⟨hx,?_⟩
      calc
        _  ≤  |x.2-σ*x.1/4|+|σ*x.1/4-σ*T/4| := abs_sub_le _ _ _
        _ = |x.2-σ*x.1/4|+|x.1-T|/4 := by
          rw [show σ*x.1/4-σ*T/4=σ*(x.1-T)/4 by ring,abs_div,abs_mul,ha,one_mul]
          norm_num
        _  ≤  630+J/4 := add_le_add hz (div_le_div_of_nonneg_right hx (by norm_num))
        _ = _ := add_comm _ _
    · exact Or.inr ⟨by linarith,by linarith,hz⟩
lemma move_path_contained (J : ℝ) (L i : ℕ) (hi : i ≤ L) (hJ : 26200 < J)
    (y x : ℝ×ℝ) (d e σ : ℝ) (hσ : |σ|=1) (he : 0 ≤ e)
    (hsmall : (L+1)*e+d < 1)
    (hyt : |y.1-(i : ℝ)| ≤ (i+1)*e+d)
    (hyz : |y.2-σ*(i : ℝ)/4| ≤ width i+d)
    (hxt : |x.1-y.1| ≤ 100) (hxz : |x.2-y.2| ≤ 100) :
    x∈domain J (L+1/2) σ := by
  have hi' : (i : ℝ) ≤ L := by exact_mod_cast hi
  have hi₀ : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have heL : 0 ≤ (L+1)*e := mul_nonneg (by positivity) he
  apply band_mem_domain J (L+1/2) σ hσ x
  · rw [abs_le] at hyt hxt
    constructor  <;>  nlinarith
  · exact (path_axis_bound L i hi y x d e σ hσ he hyt hyz hxt hxz).trans (by linarith)
lemma last_crossing_height (L : ℕ) (y x : ℝ×ℝ) (d σ : ℝ) (hσ : |σ|=1)
    (hy : |y.2-σ*(L : ℝ)/4| ≤ 2+d) (hx : |x.2-y.2| ≤ 100) (hd : d < 1) :
    |x.2-σ*(L+1/2)/4| < 210 := by
  have he : σ*(L : ℝ)/4-σ*(L+1/2)/4=-σ/8 := by ring
  calc
    _  ≤  |x.2-y.2|+|y.2-σ*(L : ℝ)/4|+|σ*(L : ℝ)/4-σ*(L+1/2)/4| :=
      by linarith [abs_sub_le x.2 (σ*(L : ℝ)/4) (σ*(L+1/2)/4),
        abs_sub_le x.2 y.2 (σ*(L : ℝ)/4)]
    _  ≤  100+(2+d)+1/8 := by
      rw [he,abs_div,abs_neg,hσ]
      norm_num
      linarith
    _  <  _ := by linarith
end CriticalPercolation.Relay
namespace SimpleGraph.Walk
open scoped _root_.SimpleGraph _root_.SimpleGraph.Walk
variable {V : Type*} {H : SimpleGraph V}
lemma exists_first_crossing (f : V → ℝ) (ρ T : ℝ)
    (hf : ∀ ⦃x y⦄, H.Adj x y → |f x-f y| ≤ ρ)
    {a b : V} (w : H.Walk a b) (ha : f a < T) (hb : T ≤ f b) :
    ∃ x∈w.support, T ≤ f x ∧ f x ≤ T+ρ := by
  induction w with
  | nil =>  exact (not_le_of_gt ha hb).elim
  | @cons a c b hac w ih =>
    by_cases hc : T ≤ f c
    · refine ⟨c,?_,hc,?_⟩
      · simp only [_root_.SimpleGraph.Walk.support_cons,List.mem_cons]
        exact Or.inr w.start_mem_support
      · have hh := hf hac
        rw [abs_le] at hh
        linarith
    · obtain ⟨x,hx,h1,h2⟩ := ih (lt_of_not_ge hc) hb
      exact ⟨x,by simp only [_root_.SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr hx,h1,h2⟩
end SimpleGraph.Walk
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.RelayMoves
section

namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)
lemma open_induced_adj (S : Set V) (ω : Set E) (u v : V) :
    (G.openGraph (ω∩G.inducedEdges S)).Adj u v ↔
    (G.openGraph ω).Adj u v ∧ u∈S ∧ v∈S := by
  constructor
  · rintro ⟨⟨b,hb,hend⟩,hne⟩
    exact ⟨⟨⟨b,hb.1,hend⟩,hne⟩,hb.2 u (by rw [hend]; simp),
      hb.2 v (by rw [hend]; simp)⟩
  · rintro ⟨⟨⟨b,hb,hend⟩,hne⟩,hu,hv⟩
    refine ⟨⟨b,⟨hb,?_⟩,hend⟩,hne⟩
    intro w hw
    rw [hend] at hw
    rcases (Sym2.mem_iff.mp hw) with rfl|rfl <;> assumption
lemma walk_reachable_induced (S : Set V) (ω : Set E) {a b : V}
    (w : (G.openGraph ω).Walk a b) (hw : ∀ x∈w.support,x∈S) :
    (G.openGraph (ω∩G.inducedEdges S)).Reachable a b := by
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a c b hac w ih =>
    have hc : c∈S := hw c (by simp only [SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr w.start_mem_support)
    have ha : a∈S := hw a (by simp)
    exact ((G.open_induced_adj S ω a c).mpr ⟨hac,ha,hc⟩).reachable.trans
      (ih (fun x hx => hw x (by simp only [SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr hx)))
def coordinateMove (t z : V → ℝ) (m : ℕ) (e : ℝ) (y : V) (s : ℝ) : Set (Set E) :=
  {ω | ∃ a∈G.vertexBall y m, ∃ b, ∃ w : (G.openGraph ω).Walk a b,
    (∀ x∈w.support, |t x-t y| ≤ 100 ∧ |z x-z y| ≤ 100) ∧
    |t b-(t y+1)| ≤ e/4 ∧ |z b-(z y+s)| ≤ e/4}
def relayRegion (t z : V → ℝ) (σ e : ℝ) (i : ℕ) : Set V :=
  {v | |t v-(i : ℝ)| ≤ (i+1)*e ∧ |z v-σ*(i : ℝ)/4| ≤ Relay.width i}
def relayMark (t z : V → ℝ) (T σ ρ : ℝ) : Set V :=
  {v | T ≤ t v ∧ t v ≤ T+ρ ∧ |z v-σ*T/4| ≤ 210}
def relayDomain (t z : V → ℝ) (J T σ : ℝ) : Set V :=
  (fun v => (t v,z v)) ⁻¹' Relay.domain J T σ
lemma relay_collar_bounds (t z : V → ℝ) (σ e ρ : ℝ) (hρ : 0 ≤ ρ)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    (R i : ℕ) {y : V} (hy : y∈G.vertexCollar (relayRegion t z σ e i) R) :
    |t y-(i : ℝ)| ≤ (i+1)*e+R*ρ ∧ |z y-σ*(i : ℝ)/4| ≤ Relay.width i+R*ρ := by
  exact ⟨G.coordinate_collar_bound t ρ hρ ht _ _ _ (fun _ h => h.1) hy,
    G.coordinate_collar_bound z ρ hρ hz _ _ _ (fun _ h => h.2) hy⟩
lemma full_relay_move (t z : V → ℝ) (σ e ρ J : ℝ) (L R m i : ℕ)
    (hσ : |σ|=1) (he : 0 ≤ e) (hρ : 0 ≤ ρ) (hJ : 26200<J)
    (hi : i<L) (hsmall : (L+1)*e+R*ρ<1)
    (hheight : R*ρ+e/4 ≤ 1/4) (htime : R*ρ+e/4 ≤ e)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    {y : V} (hy : y∈G.vertexCollar (relayRegion t z σ e i) R) :
    coordinateMove G t z m e y (Relay.selectedSign (z y-σ*(i : ℝ)/4)) ⊆
      {ω | ω∩G.inducedEdges (relayDomain t z J (L+1/2) σ)∈
        G.seedHitEvent (G.vertexBall y m) (relayRegion t z σ e (i+1))} := by
  intro ω hω
  obtain ⟨a,ha,b,w,hw,hbt,hbz⟩ := hω
  have hy' := G.relay_collar_bounds t z σ e ρ hρ ht hz R i hy
  have hb : b∈relayRegion t z σ e (i+1) := by
    refine ⟨?_,?_⟩
    · simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using
        Relay.full_step_time i (t y) (t b) (R*ρ) e hy'.1 hbt htime
    have hh := Relay.full_step_height i (z y-σ*(i : ℝ)/4) σ (R*ρ) e
      (z b-(z y+Relay.selectedSign (z y-σ*(i : ℝ)/4))) hσ hy'.2
      (mul_nonneg (Nat.cast_nonneg _) hρ) hheight hbz
    convert hh using 1
    push_cast
    ring_nf
  apply Set.mem_iUnion₂.mpr
  refine ⟨a,ha,b,G.walk_reachable_induced _ ω w ?_,hb⟩
  intro x hx
  exact Relay.move_path_contained J L i hi.le hJ (t y,z y) (t x,z x)
    (R*ρ) e σ hσ he hsmall hy'.1 hy'.2 (hw x hx).1 (hw x hx).2
lemma last_relay_move (t z : V → ℝ) (σ e ρ J : ℝ) (L R m : ℕ)
    (hσ : |σ|=1) (he : 0 ≤ e) (hρ : 0 ≤ ρ) (hJ : 26200<J)
    (hL : 416 ≤ L) (hsmall : (L+1)*e+(R+m)*ρ+e/4<1/2)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    {y : V} (hy : y∈G.vertexCollar (relayRegion t z σ e L) R) (s : ℝ) :
    coordinateMove G t z m e y s ⊆
      {ω | ω∩G.inducedEdges (relayDomain t z J (L+1/2) σ)∈
        G.seedHitEvent (G.vertexBall y m) (relayMark t z (L+1/2) σ ρ)} := by
  intro ω hω
  obtain ⟨a,ha,b,w,hw,hbt,_⟩ := hω
  have hy' := G.relay_collar_bounds t z σ e ρ hρ ht hz R L hy
  have hma : |t a-t y| ≤ m*ρ := G.coordinate_ball_bound t ρ hρ ht ha
  have hnR : 0 ≤ (R : ℝ)*ρ := mul_nonneg (Nat.cast_nonneg _) hρ
  have hnm : 0 ≤ (m : ℝ)*ρ := mul_nonneg (Nat.cast_nonneg _) hρ
  have hnL : 0 ≤ (L+1 : ℝ)*e := mul_nonneg (by positivity) he
  have hyt := abs_le.mp hy'.1
  have hbt' := abs_le.mp hbt
  have hma' := abs_le.mp hma
  have haT : t a<L+1/2 := by linarith
  have hbT : (L : ℝ)+1/2 ≤ t b := by linarith
  have hadj : ∀ ⦃u v⦄, (G.openGraph ω).Adj u v → |t u-t v| ≤ ρ :=
    fun _ _ h => ht (G.openGraph_mono (Set.subset_univ _) h)
  obtain ⟨x,hx,hx₁,hx₂⟩ := _root_.OAI.SimpleGraph.Walk.exists_first_crossing t ρ (L+1/2) hadj w haT hbT
  have hxz : |z x-σ*(L+1/2)/4|<210 := by
    apply Relay.last_crossing_height L (t y,z y) (t x,z x) (R*ρ) σ hσ
    · simpa only [Relay.width_last L hL] using hy'.2
    · exact (hw x hx).2
    · linarith
  apply Set.mem_iUnion₂.mpr
  refine ⟨a,ha,x,?_,⟨hx₁,hx₂,hxz.le⟩⟩
  apply G.walk_reachable_induced _ ω (w.takeUntil x hx)
  intro v hv
  have hv' : v∈w.support := (w.isSubwalk_takeUntil hx).support_subset hv
  apply Relay.move_path_contained J L L le_rfl hJ (t y,z y) (t v,z v)
    (R*ρ) e σ hσ he _ hy'.1 hy'.2 (hw v hv').1 (hw v hv').2
  linarith
end CriticalPercolation.BondGraph
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.CorridorNormalization
section

namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical
namespace CriticalPercolation.Corridor
open BondGraph
variable {V : Type*}
def timeCenter (T : ℝ) (v : Site) : ℝ := ((v.1 : ℝ)+v.2)*T
def heightCenter (T : ℝ) (v : Site) : ℝ := ((v.1 : ℝ)-v.2)*T/4
def normalized (t z : V → ℝ) (T : ℝ) : V → Point := fun x => (t x/T,4*z x/T)
def localTime (t : V → ℝ) (T : ℝ) (v : Site) : V → ℝ := fun x => t x-timeCenter T v
def localHeight (z : V → ℝ) (T : ℝ) (v : Site) : V → ℝ := fun x => z x-heightCenter T v
def sign (b : Bool) : ℝ := if b then 1 else -1
def mark (t z : V → ℝ) (T ρ : ℝ) (v : Site) : Set V :=
  {x | 0≤localTime t T v x ∧ localTime t T v x≤ρ ∧ |localHeight z T v x|≤210}
lemma sign_abs (b : Bool) : |sign b|=1 := by cases b <;> norm_num [sign]
lemma timeCenter_target (T : ℝ) (v : Site) (b : Bool) :
    timeCenter T (target (v,b))=timeCenter T v+T := by
  cases b <;> simp [target,timeCenter] <;> ring
lemma heightCenter_target (T : ℝ) (v : Site) (b : Bool) :
    heightCenter T (target (v,b))=heightCenter T v+sign b*T/4 := by
  cases b <;> simp [target,heightCenter,sign] <;> ring
lemma normalized_box (t z : V → ℝ) (T J : ℝ) (hT : 0<T) (v : Site) :
    graphBox (normalized t z T) (J/T) (2520/T) v=
      {x | |localTime t T v x|≤J ∧ |localHeight z T v x|≤J/4+630} := by
  ext x
  change (|t x/T-((v.1 : ℝ)+v.2)|≤J/T ∧
    |4*z x/T-((v.1 : ℝ)-v.2)|≤J/T+2520/T) ↔ _
  have ht : t x/T-((v.1 : ℝ)+v.2)=localTime t T v x/T := by
    dsimp [localTime,timeCenter]; field_simp
  have hz : 4*z x/T-((v.1 : ℝ)-v.2)=4*localHeight z T v x/T := by
    dsimp [localHeight,heightCenter]; field_simp
  rw [ht,hz,abs_div,abs_div,abs_of_pos hT,div_le_div_iff_of_pos_right hT,
    show J/T+2520/T=(J+2520)/T by ring,div_le_div_iff_of_pos_right hT,
    abs_mul,show |(4 : ℝ)|=4 by norm_num]
  change (_ ∧ _) ↔ (_ ∧ _)
  constructor <;> rintro ⟨ht,hz⟩ <;> exact ⟨ht,by linarith⟩
lemma normalized_tube (t z : V → ℝ) (T : ℝ) (hT : 0<T) (v : Site) (b : Bool) :
    (normalized t z T) ⁻¹' tube (2520/T) (v,b)=
      {x | 0≤localTime t T v x ∧ localTime t T v x≤T ∧
        |localHeight z T v x-sign b*localTime t T v x/4|≤630} := by
  ext x
  have ht : ((v.1 : ℝ)+v.2≤t x/T) ↔ 0≤localTime t T v x := by
    rw [le_div_iff₀ hT]; dsimp [localTime,timeCenter]; constructor <;> intro h <;> linarith
  have ht' : (t x/T≤(v.1 : ℝ)+v.2+1) ↔ localTime t T v x≤T := by
    rw [div_le_iff₀ hT]; dsimp [localTime,timeCenter]; constructor <;> intro h <;> nlinarith
  cases b with
  | true =>
    change (((v.1 : ℝ)+v.2≤t x/T) ∧ (t x/T≤(v.1 : ℝ)+v.2+1) ∧
      |4*z x/T-(t x/T-2*(v.2 : ℝ))|≤2520/T) ↔ _
    have he : 4*z x/T-(t x/T-2*(v.2 : ℝ))=
        4*(localHeight z T v x-sign true*localTime t T v x/4)/T := by
      dsimp [localHeight,heightCenter,localTime,timeCenter,sign]; field_simp; ring
    rw [ht,ht',he,abs_div,abs_of_pos hT,div_le_div_iff_of_pos_right hT,
      abs_mul,show |(4 : ℝ)|=4 by norm_num]
    change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
    constructor <;> rintro ⟨ha,hb,hc⟩ <;> exact ⟨ha,hb,by linarith⟩
  | false =>
    change (((v.1 : ℝ)+v.2≤t x/T) ∧ (t x/T≤(v.1 : ℝ)+v.2+1) ∧
      |4*z x/T-(2*(v.1 : ℝ)-t x/T)|≤2520/T) ↔ _
    have he : 4*z x/T-(2*(v.1 : ℝ)-t x/T)=
        4*(localHeight z T v x-sign false*localTime t T v x/4)/T := by
      dsimp [localHeight,heightCenter,localTime,timeCenter,sign]; field_simp; ring
    rw [ht,ht',he,abs_div,abs_of_pos hT,div_le_div_iff_of_pos_right hT,
      abs_mul,show |(4 : ℝ)|=4 by norm_num]
    change (_ ∧ _ ∧ _) ↔ (_ ∧ _ ∧ _)
    constructor <;> rintro ⟨ha,hb,hc⟩ <;> exact ⟨ha,hb,by linarith⟩
lemma normalized_domain (t z : V → ℝ) (T J : ℝ) (hT : 0<T) (v : Site) (b : Bool) :
    graphDomain (normalized t z T) (J/T) (2520/T) (v,b)=
      relayDomain (localTime t T v) (localHeight z T v) J T (sign b) := by
  change (normalized t z T) ⁻¹' (box _ _ v∪box _ _ (target (v,b))∪tube _ (v,b))=_
  rw [Set.preimage_union,Set.preimage_union]
  change graphBox _ _ _ v∪graphBox _ _ _ (target (v,b))∪_=_
  rw [normalized_box t z T J hT,normalized_box t z T J hT,normalized_tube t z T hT]
  ext x
  change ((_ ∧ _) ∨ (_ ∧ _)) ∨ (_ ∧ _ ∧ _) ↔ ((_ ∧ _) ∨ (_ ∧ _)) ∨ (_ ∧ _ ∧ _)
  simp only [localTime,localHeight,timeCenter_target,heightCenter_target,sub_add_eq_sub_sub]
lemma mark_initial (t z : V → ℝ) (T ρ : ℝ) (v : Site) (b : Bool) :
    relayMark (localTime t T v) (localHeight z T v) 0 (sign b) ρ=mark t z T ρ v := by
  ext x
  simp only [relayMark,mark,Set.mem_ofPred_eq,mul_zero,zero_div,sub_zero,zero_add]
lemma mark_target (t z : V → ℝ) (T ρ : ℝ) (v : Site) (b : Bool) :
    relayMark (localTime t T v) (localHeight z T v) T (sign b) ρ=mark t z T ρ (target (v,b)) := by
  ext x
  change (T≤localTime t T v x ∧ localTime t T v x≤T+ρ ∧
    |localHeight z T v x-sign b*T/4|≤210) ↔ _
  change _ ↔ (0≤localTime t T (target (v,b)) x ∧ localTime t T (target (v,b)) x≤ρ ∧
    |localHeight z T (target (v,b)) x|≤210)
  simp only [localTime,localHeight,timeCenter_target,heightCenter_target]
  have he : z x-heightCenter T v-sign b*T/4=z x-(heightCenter T v+sign b*T/4) := by ring
  rw [he]
  constructor <;> rintro ⟨ha,hb,hc⟩ <;> exact ⟨by linarith,by linarith,hc⟩
lemma mark_subset_box (t z : V → ℝ) (T J ρ : ℝ) (hT : 0<T) (hJ : 0≤J) (hρJ : ρ≤J) (v : Site) :
    mark t z T ρ v⊆graphBox (normalized t z T) (J/T) (2520/T) v := by
  rw [normalized_box t z T J hT]
  intro x hx
  exact ⟨by rw [abs_of_nonneg hx.1]; exact hx.2.1.trans hρJ,by linarith [hx.2.2]⟩
lemma coordinateMove_translate {E : Type*} (G : BondGraph V E) (t z : V → ℝ)
    (T : ℝ) (v : Site) (m : ℕ) (e : ℝ) (y : V) (s : ℝ) :
    G.coordinateMove (localTime t T v) (localHeight z T v) m e y s=
      G.coordinateMove t z m e y s := by
  unfold coordinateMove localTime localHeight
  simp only [sub_sub_sub_cancel_right]
  have ht : ∀ b, t b-timeCenter T v-(t y-timeCenter T v+1)=t b-(t y+1) := by intro b; ring
  have hz : ∀ b, z b-heightCenter T v-(z y-heightCenter T v+s)=z b-(z y+s) := by intro b; ring
  simp only [ht,hz]
end CriticalPercolation.Corridor
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.RelayScales
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)
lemma vertexCollar_mono {S T : Set V} (hST : S⊆T) (R : ℕ) :
    G.vertexCollar S R⊆G.vertexCollar T R := by
  intro y hy
  obtain ⟨v,hv,hy⟩ := Set.mem_iUnion₂.mp hy
  exact Set.mem_iUnion₂.mpr ⟨v,hST hv,hy⟩
lemma initial_mark_subset_relay (t z : V → ℝ) (σ e ρ : ℝ) (hρ : ρ ≤ e) :
    relayMark t z 0 σ ρ⊆relayRegion t z σ e 0 := by
  intro v hv
  obtain ⟨ht₀,ht₁,hz⟩ := hv
  change |t v-(0:ℕ)| ≤ ((0:ℕ)+1)*e ∧ |z v-σ*(0:ℕ)/4| ≤ Relay.width 0
  norm_num [Relay.width] at ht₀ ht₁ hz ⊢
  exact ⟨by rw [abs_of_nonneg ht₀]; linarith,hz⟩
lemma relay_coordinate_scale (L R m : ℕ) (e ρ : ℝ) (he : 0<e) (hρ : 0 ≤ ρ)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10) :
    ρ ≤ e ∧ (L+1)*e+R*ρ<1 ∧ R*ρ+e/4 ≤ 1/4 ∧ R*ρ+e/4 ≤ e ∧
      (L+1)*e+(R+m)*ρ+e/4<1/2 := by
  have hR : 0 ≤ (R:ℝ)*ρ := mul_nonneg (Nat.cast_nonneg _) hρ
  have hm : 0 ≤ (m:ℝ)*ρ := mul_nonneg (Nat.cast_nonneg _) hρ
  have hL : 0 ≤ (L:ℝ)*e := mul_nonneg (Nat.cast_nonneg _) he.le
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith
lemma relay_collar_in_domain (t z : V → ℝ) (σ e ρ J : ℝ) (L R i : ℕ)
    (hσ : |σ|=1) (he : 0 ≤ e) (hρ : 0 ≤ ρ) (hJ : 26200<J)
    (hi : i ≤ L) (hsmall : (L+1)*e+R*ρ<1)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ) :
    G.vertexCollar (relayRegion t z σ e i) R⊆relayDomain t z J (L+1/2) σ := by
  intro y hy
  have hy' := G.relay_collar_bounds t z σ e ρ hρ ht hz R i hy
  apply Relay.move_path_contained J L i hi hJ (t y,z y) (t y,z y)
    (R*ρ) e σ hσ he hsmall hy'.1 hy'.2 <;> norm_num
lemma forceOutside_induced (S : Set V) (ω : Set E) :
    BernoulliProduct.forceOn (G.inducedEdges S)ᶜ ∅ ω=ω∩G.inducedEdges S := by
  ext b
  by_cases hb : b∈G.inducedEdges S <;> simp [hb]
def corridorRelay (t z : V → ℝ) (σ e ρ : ℝ) (L i : ℕ) : Set V :=
  if i=0 then relayMark t z 0 σ ρ
  else if i ≤ L then relayRegion t z σ e i else relayMark t z (L+1/2) σ ρ
lemma corridorRelay_subset (t z : V → ℝ) (σ e ρ : ℝ) (hρe : ρ ≤ e)
    (L i : ℕ) (hi : i ≤ L) : corridorRelay t z σ e ρ L i⊆relayRegion t z σ e i := by
  by_cases h0 : i=0
  · subst i
    simpa [corridorRelay] using initial_mark_subset_relay t z σ e ρ hρe
  · simp only [corridorRelay,if_neg h0,if_pos hi,Subset.rfl]
theorem coordinate_moves_relay_estimates (t z : V → ℝ) (σ e ρ J : ℝ) (L R m : ℕ)
    (hσ : |σ|=1) (he : 0<e) (hρ : 0 ≤ ρ) (hJ : 26200<J) (hL : 416 ≤ L)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    (p : unitInterval) (η : ℝ)
    (hmove : ∀ y s, |s|=1 → 1-η ≤ (BernoulliProduct.law (fun _ : E => p)).real
      (G.coordinateMove t z m e y s)) :
    ∀ i ≤ L,
      G.vertexCollar (corridorRelay t z σ e ρ L i) R⊆relayDomain t z J (L+1/2) σ ∧
      ∀ y∈G.vertexCollar (corridorRelay t z σ e ρ L i) R,
        1-η ≤ (BernoulliProduct.law (fun _ : E => p)).real
          ((BernoulliProduct.forceOn (G.inducedEdges (relayDomain t z J (L+1/2) σ))ᶜ ∅) ⁻¹'
            G.seedHitEvent (G.vertexBall y m) (corridorRelay t z σ e ρ L (i+1))) := by
  obtain ⟨hρe,hsmall,hheight,htime,hlast⟩ := relay_coordinate_scale L R m e ρ he hρ heL hr
  intro i hi
  have hsub := G.vertexCollar_mono (corridorRelay_subset t z σ e ρ hρe L i hi) R
  refine ⟨hsub.trans (G.relay_collar_in_domain t z σ e ρ J L R i hσ he.le hρ hJ hi hsmall ht hz),?_⟩
  intro y hy
  apply (hmove y (Relay.selectedSign (z y-σ*(i:ℝ)/4)) (Relay.selectedSign_abs _)).trans
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro ω hω
  rw [Set.mem_preimage,G.forceOutside_induced]
  by_cases hiL : i<L
  · have hh := G.full_relay_move t z σ e ρ J L R m i hσ he.le hρ hJ hiL hsmall
      hheight htime ht hz (hsub hy) hω
    change ω∩G.inducedEdges (relayDomain t z J (L+1/2) σ)∈
      G.seedHitEvent (G.vertexBall y m) (relayRegion t z σ e (i+1)) at hh
    simpa only [corridorRelay,Nat.add_one_ne_zero,ite_false,if_pos (by omega : i+1 ≤ L)] using hh
  · have hiEq : i=L := by omega
    subst i
    have hh := G.last_relay_move t z σ e ρ J L R m hσ he.le hρ hJ hL hlast ht hz
      (hsub hy) _ hω
    change ω∩G.inducedEdges (relayDomain t z J (L+1/2) σ)∈
      G.seedHitEvent (G.vertexBall y m) (relayMark t z (L+1/2) σ ρ) at hh
    simpa only [corridorRelay,Nat.add_one_ne_zero,ite_false,if_neg (by omega : ¬L+1 ≤ L)] using hh
end CriticalPercolation.BondGraph
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.GraphGeometry.CoordinateScheme
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.Corridor
open BondGraph Boundary BernoulliProduct
structure CoordinateData (V E : Type*) where
  graph : BondGraph V E
  origin : V
  time : V → ℝ
  height : V → ℝ
  J : ℝ
  L : ℕ
  R : ℕ
  m : ℕ
  D : ℕ
  k : ℕ
  M : ℕ
  VM : ℕ
  e : ℝ
  rho : ℝ
  kappa : ℝ
  eta : ℝ
  delta : ℝ
  contour : ℝ
  pc : unitInterval
  p : unitInterval
namespace CoordinateData
variable {V E : Type*} (C : CoordinateData V E)
def T : ℝ := C.L+1/2
def scheme : Scheme V E where
  graph := C.graph
  coordinate := normalized C.time C.height C.T
  j := C.J/C.T
  h := 2520/C.T
  seed := C.graph.vertexBall C.origin C.m
  mark := Corridor.mark C.time C.height C.T C.rho
  parameter := fun _ => C.p
  delta := C.delta
structure Bounds : Prop where
  connected : C.graph.fullGraph.Connected
  locallyFinite : C.graph.LocallyFinite
  time_origin : C.time C.origin=0
  height_origin : C.height C.origin=0
  time_step : ∀ ⦃u v⦄, C.graph.fullGraph.Adj u v → |C.time u-C.time v|≤C.rho
  height_step : ∀ ⦃u v⦄, C.graph.fullGraph.Adj u v → |C.height u-C.height v|≤C.rho
  J_lower : 26200<C.J
  L_lower : 10*(C.J+210)<C.L
  e_pos : 0<C.e
  rho_nonneg : 0≤C.rho
  e_small : (C.L+3)*C.e<1/100
  rho_small : (C.R+C.m+1)*C.rho<C.e/10
  R_gt : C.m<C.R
  pc_pos : 0<(C.pc : ℝ)
  pc_lt : (C.pc : ℝ)<1
  p_lower : (C.pc : ℝ)/2≤C.p
  p_upper : (C.p : ℝ)≤C.pc
  degree : ∀ v, (C.graph.incidentEdges {v}).ncard≤C.D
  M_pos : 0<C.M
  M_bound : ∀ v, (C.graph.vertexBall v (4*C.m+2)).ncard≤C.M
  VM_bound : ∀ v, (C.graph.vertexBall v C.m).ncard≤C.VM
  kappa_pos : 0<C.kappa
  kappa_le : C.kappa≤1
  eta_nonneg : 0≤C.eta
  eta_small : C.eta≤C.kappa*(C.kappa/4)/(4*(Real.log (4/C.kappa)+1))
  k_large : C.M*⌈Real.log (4/C.kappa)/((C.pc : ℝ)/2)^(C.m+1+C.VM)⌉₊≤C.k
  R_large : 4/(C.kappa*(1-(C.pc : ℝ))^(C.D*C.k))<(C.R : ℝ)-C.m
  delta_pos : 0<C.delta
  root_error : 2*(C.eta+C.L*C.kappa)<C.delta
  contour_nonneg : 0≤C.contour
  contour_small : 8*C.contour<1
  test_error : C.delta+2*((C.L+1)*C.kappa)/C.delta≤C.contour^4
lemma T_pos : 0<C.T := by unfold T; positivity
lemma L_large (h : C.Bounds) : 416≤C.L := by
  have : (416 : ℝ)≤C.L := by linarith [h.J_lower,h.L_lower]
  exact_mod_cast this
lemma small_rho (h : C.Bounds) : C.rho≤C.J := by
  have he := h.e_small
  have hr := h.rho_small
  have hle : C.rho≤C.e := (relay_coordinate_scale C.L C.R C.m C.e C.rho
    h.e_pos h.rho_nonneg he hr).1
  have hLp : 0≤(C.L : ℝ)*C.e := mul_nonneg (Nat.cast_nonneg _) h.e_pos.le
  linarith [h.J_lower]
lemma layout (h : C.Bounds) :
    0≤C.scheme.h ∧ C.scheme.h≤C.scheme.j ∧ 2*C.scheme.j+C.scheme.h<1 := by
  change 0≤2520/C.T ∧ 2520/C.T≤C.J/C.T ∧ 2*(C.J/C.T)+2520/C.T<1
  refine ⟨div_nonneg (by norm_num) C.T_pos.le, (div_le_div_iff_of_pos_right C.T_pos).mpr (by linarith [h.J_lower]),?_⟩
  rw [show 2*(C.J/C.T)+2520/C.T=(2*C.J+2520)/C.T by ring,div_lt_one C.T_pos]
  dsimp [T]
  linarith [h.J_lower,h.L_lower]
lemma root_seed (h : C.Bounds) : (C.scheme.seed∩C.scheme.mark (0,0)).Nonempty := by
  refine ⟨C.origin,C.graph.mem_vertexBall_self C.origin C.m,?_⟩
  change 0≤localTime C.time C.T (0,0) C.origin ∧
    localTime C.time C.T (0,0) C.origin≤C.rho ∧ |localHeight C.height C.T (0,0) C.origin|≤210
  simp [localTime,localHeight,timeCenter,heightCenter,h.time_origin,h.height_origin,h.rho_nonneg]
lemma marks_disjoint (h : C.Bounds) : Pairwise (Disjoint on C.scheme.mark) := by
  intro v w hvw
  exact (graph_boxes_disjoint (normalized C.time C.height C.T) (C.J/C.T) (2520/C.T)
    (C.layout h).2.2 hvw).mono
    (mark_subset_box C.time C.height C.T C.J C.rho C.T_pos (by linarith [h.J_lower]) (C.small_rho h) v)
    (mark_subset_box C.time C.height C.T C.J C.rho C.T_pos (by linarith [h.J_lower]) (C.small_rho h) w)
lemma domain_eq (v : Site) (b : Bool) : C.scheme.edgeDomain (v,b)=
    C.graph.inducedEdges (relayDomain (localTime C.time C.T v) (localHeight C.height C.T v)
      C.J C.T (sign b)) := by
  change C.graph.inducedEdges (graphDomain (normalized C.time C.height C.T) (C.J/C.T) (2520/C.T) (v,b))=_
  rw [normalized_domain C.time C.height C.T C.J C.T_pos]
lemma local_time_step (h : C.Bounds) (v : Site) {u w : V} (huw : C.graph.fullGraph.Adj u w) :
    |localTime C.time C.T v u-localTime C.time C.T v w|≤C.rho := by
  simpa only [localTime,sub_sub_sub_cancel_right] using h.time_step huw
lemma local_height_step (h : C.Bounds) (v : Site) {u w : V} (huw : C.graph.fullGraph.Adj u w) :
    |localHeight C.height C.T v u-localHeight C.height C.T v w|≤C.rho := by
  simpa only [localHeight,sub_sub_sub_cancel_right] using h.height_step huw
lemma source_behind (h : C.Bounds) (n : ℕ) (hn : 0<n) :
    ∀ a∈C.scheme.seed, localTime C.time C.T (slotSite n) a≤C.m*C.rho-C.T := by
  intro a ha
  have ht := (abs_le.mp (C.graph.coordinate_ball_bound C.time C.rho h.rho_nonneg h.time_step ha)).2
  rw [h.time_origin,sub_zero] at ht
  have hv := slotSite_quadrant n
  have hnz : slotSite n≠(0,0) := by
    intro he
    have he' := congrArg gridSlot he
    rw [gridSlot_slotSite] at he'
    change n=0 at he'
    omega
  have hsumInt : 1≤(slotSite n).1+(slotSite n).2 := by
    by_contra hs
    have hx : (slotSite n).1=0 := by dsimp [quadrant] at hv; omega
    have hy : (slotSite n).2=0 := by dsimp [quadrant] at hv; omega
    exact hnz (Prod.ext hx hy)
  have hsum : (1 : ℝ)≤((slotSite n).1 : ℝ)+(slotSite n).2 := by exact_mod_cast hsumInt
  have hmul := mul_le_mul_of_nonneg_right hsum C.T_pos.le
  change C.time a-(((slotSite n).1 : ℝ)+(slotSite n).2)*C.T≤_
  linarith
end CoordinateData
end CriticalPercolation.Corridor
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.CorridorScaleChoice
section

namespace OAI
section
section
noncomputable section
open scoped Classical
namespace CriticalPercolation.Corridor.ScaleChoice
def J : ℝ := 30000
def L : ℕ := 1000000
def contour : ℝ := 1/16
def epsilon : ℝ := contour^4
def delta : ℝ := epsilon/4
def kappa : ℝ := epsilon*delta/(8*(L+1))
def e : ℝ := 1/(200*(L+3))
def eta : ℝ := kappa^2/(32*(Real.log (4/kappa)+1))
lemma J_lower : 26200<J := by norm_num [J]
lemma L_lower : 10*(J+210)<L := by norm_num [J,L]
lemma e_pos : 0<e := by norm_num [e,L]
lemma e_lt : e<1/10 := by norm_num [e,L]
lemma e_small : (L+3)*e<1/100 := by norm_num [e,L]
lemma kappa_pos : 0<kappa := by norm_num [kappa,epsilon,delta,contour,L]
lemma kappa_le : kappa≤1 := by norm_num [kappa,epsilon,delta,contour,L]
lemma log_nonneg : 0≤Real.log (4/kappa) :=
  Real.log_nonneg (by norm_num [kappa,epsilon,delta,contour,L])
lemma eta_pos : 0<eta := by
  unfold eta
  exact div_pos (sq_pos_of_pos kappa_pos) (mul_pos (by norm_num) (by linarith [log_nonneg]))
lemma eta_le : eta≤kappa := by
  unfold eta
  rw [div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ)<32) (by linarith [log_nonneg]))]
  have hk := kappa_pos
  have hkl := kappa_le
  have hlog := mul_nonneg hk.le log_nonneg
  nlinarith
lemma eta_lt : eta<1/10 :=
  eta_le.trans_lt (by norm_num [kappa,epsilon,delta,contour,L])
lemma eta_small : eta≤kappa*(kappa/4)/(4*(Real.log (4/kappa)+1)) := by
  have hp : 0<Real.log (4/kappa)+1 := by linarith [log_nonneg]
  unfold eta
  field_simp
  nlinarith [sq_nonneg kappa]
lemma delta_pos : 0<delta := by norm_num [delta,epsilon,contour]
lemma root_error : 2*(eta+L*kappa)<delta := by
  have he := eta_le
  have hn : 2*(kappa+L*kappa)<delta := by norm_num [delta,kappa,epsilon,contour,L]
  linarith
lemma contour_nonneg : 0≤contour := by norm_num [contour]
lemma contour_small : 8*contour<1 := by norm_num [contour]
lemma test_error : delta+2*((L+1)*kappa)/delta≤contour^4 := by
  norm_num [delta,kappa,epsilon,contour,L]
lemma trial_scales (pc : ℝ) (D M VM m : ℕ) :
    ∃ k R : ℕ,
      M*⌈Real.log (4/kappa)/(pc/2)^(m+1+VM)⌉₊<k ∧ m<R ∧
      4/(kappa*(1-pc)^(D*k))<(R : ℝ)-m := by
  let k := M*⌈Real.log (4/kappa)/(pc/2)^(m+1+VM)⌉₊+1
  obtain ⟨r,hr⟩ := exists_nat_gt (4/(kappa*(1-pc)^(D*k)))
  refine ⟨k,m+r+1,by dsimp [k]; omega,by omega,?_⟩
  push_cast
  linarith
lemma mesh (R m : ℕ) : ∃ rho : ℝ, 0<rho ∧ (R+m+1)*rho<e/10 := by
  have hd : (0 : ℝ)<(R:ℝ)+m+1 := by positivity
  refine ⟨e/(20*((R:ℝ)+m+1)),div_pos e_pos (mul_pos (by norm_num) hd),?_⟩
  have he : ((R:ℝ)+m+1)*(e/(20*((R:ℝ)+m+1)))=e/20 := by field_simp
  rw [he]
  linarith [e_pos]
end CriticalPercolation.Corridor.ScaleChoice
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.ProductMeasure.RelayProbability
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators
namespace CriticalPercolation
variable {Ω : Type*} [MeasurableSpace Ω]
lemma relay_failure_bound (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : ℕ → Set Ω) (κ : ℝ) (N : ℕ)
    (h : ∀ i<N, μ.real (A i\A (i+1)) ≤ κ) :
    μ.real (A 0\A N) ≤ N*κ := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hsub : A 0\A (N+1) ⊆ (A 0\A N)∪(A N\A (N+1)) := by
      intro ω hω
      by_cases hn : ω∈A N
      · exact Or.inr ⟨hn,hω.2⟩
      · exact Or.inl ⟨hω.1,hn⟩
    calc
      _ ≤ μ.real ((A 0\A N)∪(A N\A (N+1))) := measureReal_mono hsub
      _ ≤ μ.real (A 0\A N)+μ.real (A N\A (N+1)) := measureReal_union_le _ _
      _ ≤ N*κ+κ := add_le_add (ih (fun i hi => h i (by omega))) (h N (by omega))
      _ = _ := by push_cast; ring
lemma relay_miss_bound (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : ℕ → Set Ω) (κ η : ℝ) (N : ℕ)
    (hfirst : μ.real (A 0)ᶜ ≤ η)
    (h : ∀ i<N, μ.real (A i\A (i+1)) ≤ κ) :
    μ.real (A N)ᶜ ≤ η+N*κ := by
  have hsub : (A N)ᶜ⊆(A 0)ᶜ∪(A 0\A N) := by
    intro ω hω
    by_cases h0 : ω∈A 0
    · exact Or.inr ⟨h0,hω⟩
    · exact Or.inl h0
  calc
    _ ≤ μ.real ((A 0)ᶜ∪(A 0\A N)) := measureReal_mono hsub
    _ ≤ μ.real (A 0)ᶜ+μ.real (A 0\A N) := measureReal_union_le _ _
    _ ≤ _ := add_le_add hfirst (relay_failure_bound μ A κ N h)
namespace BernoulliProduct
variable {E : Type*}
def twoPredictions (q : E → unitInterval) (S : Set E) (C D : Set (Set E))
    (δ : ℝ) : Set (Set E) :=
  {σ | 1-δ ≤ (blockProbability q S C σ).toReal ∧
    1-δ ≤ (blockProbability q S D σ).toReal}
lemma measurableSet_twoPredictions (q : E → unitInterval) (S : Set E)
    (C D : Set (Set E)) (hC : MeasurableSet C) (hD : MeasurableSet D) (δ : ℝ) :
    MeasurableSet[blockSigma S] (twoPredictions q S C D δ) :=
  (measurableSet_le measurable_const
    ((measurable_blockProbability q S C hC).ennreal_toReal)).inter
  (measurableSet_le measurable_const
    ((measurable_blockProbability q S D hD).ennreal_toReal))
theorem twoPredictions_positive (q : E → unitInterval) (S : Set E)
    (C D : Set (Set E)) (hC : MeasurableSet C) (hD : MeasurableSet D)
    (δ a : ℝ) (hδ : 0<δ) (ha : 2*a<δ)
    (hc : (law q).real Cᶜ ≤ a) (hd : (law q).real Dᶜ ≤ a) :
    0<(law q).real (twoPredictions q S C D δ) := by
  have h1 := bad_prediction_bound q S Set.univ C MeasurableSet.univ hC δ hδ
  have h2 := bad_prediction_bound q S Set.univ D MeasurableSet.univ hD δ hδ
  have hcEq : Set.univ \ C = Cᶜ := by ext; simp
  have hdEq : Set.univ \ D = Dᶜ := by ext; simp
  simp only [Set.univ_inter,hcEq,hdEq] at h1 h2
  have he : (twoPredictions q S C D δ)ᶜ=
      {σ | (blockProbability q S C σ).toReal<1-δ}∪
      {σ | (blockProbability q S D σ).toReal<1-δ} := by
    ext σ
    simp only [twoPredictions,Set.mem_compl_iff,Set.mem_ofPred_eq,Set.mem_union,not_and_or,not_le]
  have hm := (blockSigma_le S) _ (measurableSet_twoPredictions q S C D hC hD δ)
  have hcomp : (law q).real (twoPredictions q S C D δ)ᶜ<1 := by
    rw [he]
    calc
      _ ≤ (law q).real {σ | (blockProbability q S C σ).toReal<1-δ}+
          (law q).real {σ | (blockProbability q S D σ).toReal<1-δ} := measureReal_union_le _ _
      _ ≤ (law q).real Cᶜ/δ+(law q).real Dᶜ/δ := add_le_add h1 h2
      _ ≤ a/δ+a/δ := add_le_add (div_le_div_of_nonneg_right hc hδ.le)
        (div_le_div_of_nonneg_right hd hδ.le)
      _ = 2*a/δ := by ring
      _ < 1 := (div_lt_one hδ).mpr ha
  rw [probReal_compl_eq_one_sub hm] at hcomp
  linarith
end BernoulliProduct
end CriticalPercolation
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.StoredPrediction
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.Corridor.Scheme
open BondGraph Boundary BernoulliProduct
variable {V E : Type*} [Countable V] [Countable E] (P : Scheme V E)
def Stable (n : ℕ) (S : GrowthState) (ω : Set E) : Prop :=
  (∀ v∈S.good, ω∈P.hit v (P.block S)) ∧
  (∀ e : Edge, source e∈S.good → n ≤ gridSlot (target e) →
    1-P.delta ≤ (blockProbability P.parameter (P.block S)
      (P.hit (target e) (P.block S∪P.edgeDomain e)) ω).toReal)
omit [Countable V] [Countable E] in
lemma stable_initial (hroot : (P.seed∩P.mark (0,0)).Nonempty)
    {ω : Set E} (hω : ω∈P.rootEvent) : P.Stable 0 GrowthState.initial ω := by
  constructor
  · intro v hv
    have he : v=(0,0) := by simpa [GrowthState.initial] using hv
    subst v
    change ω∈P.graph.restrictedSeed P.seed (P.mark (0,0)) _
    rw [P.graph.restrictedSeed_self _ _ hroot]
    trivial
  · intro e he _hn
    obtain ⟨v,b⟩ := e
    have hv : v=(0,0) := by simpa [GrowthState.initial,source] using he
    subst v
    exact hω b
lemma stable_advance (hh : 0≤P.h) (hhj : P.h≤P.j) (hsep : 2*P.j+P.h<1)
    (n : ℕ) (S : GrowthState) (b : Bool) (ω : Set E)
    (hv : S.Valid n) (hc : S.Covered) (hs : P.Stable n S ω)
    (ha : b=true → ω∈P.accepted n S) : P.Stable (n+1) (S.advance n b) ω := by
  have hold_hit : ∀ v∈S.good, ω∈P.hit v (P.block (S.advance n b)) := by
    intro v hv
    exact P.graph.restrictedSeed_mono _ _ (P.block_enlarged n S) (hs.1 v hv)
  have hold_pred : ∀ e : Edge, source e∈S.good → n+1 ≤ gridSlot (target e) →
      1-P.delta ≤ (blockProbability P.parameter (P.block (S.advance n b))
        (P.hit (target e) (P.block (S.advance n b)∪P.edgeDomain e)) ω).toReal := by
    intro e hp ht
    have hI := later_revealed_intersection P.graph P.coordinate P.j P.h hh hhj hsep
      (n+1) S (S.advance n b) hc (S.advance_valid n b hv) hp ht
    have hprob := P.graph.seed_prediction_persists P.parameter P.seed (P.mark (target e))
      (P.block S) (P.block (S.advance n b)) (P.edgeDomain e) ω (P.block_enlarged n S) hI
    exact (hs.2 e hp (by omega)).trans
      (ENNReal.toReal_mono (ne_of_lt (lt_of_le_of_lt (blockProbability_le_one _ _ _ _) ENNReal.one_lt_top)) hprob)
  constructor
  · intro v hv
    change v∈(if (incoming n S.good).isSome ∧ b=true then insert (slotSite n) S.good else S.good) at hv
    split_ifs at hv with hb
    · rcases Finset.mem_insert.mp hv with rfl|hv
      · exact (P.accepted_iff n S ω).mp (ha hb.2) |>.1
      · exact hold_hit v hv
    · exact hold_hit v hv
  · intro e hp ht
    change source e∈(if (incoming n S.good).isSome ∧ b=true then insert (slotSite n) S.good else S.good) at hp
    split_ifs at hp with hb
    · rcases Finset.mem_insert.mp hp with he|hp
      · have he' : e=(slotSite n,e.2) := Prod.ext he rfl
        rw [he']
        exact (P.accepted_iff n S ω).mp (ha hb.2) |>.2 e.2
      · exact hold_pred e hp ht
    · exact hold_pred e hp ht
theorem stable_on_cell (hh : 0≤P.h) (hhj : P.h≤P.j) (hsep : 2*P.j+P.h<1)
    (hroot : (P.seed∩P.mark (0,0)).Nonempty) (n : ℕ) (w : DecisionCode n)
    (ω : Set E) (hc : ω∈(P.rule.partition n).cell w) (hB : ω∈P.rootEvent) :
    P.Stable n (P.rule.state n w) ω := by
  induction n with
  | zero => exact P.stable_initial hroot hB
  | succ n ih =>
    rcases w with ⟨w,b⟩
    rw [P.rule.partition_cell_succ] at hc
    apply P.stable_advance hh hhj hsep n (P.rule.state n w) b ω
      (P.state_valid n w) (P.state_covered n w) (ih w hc.1)
    intro hb
    have hdecision := hc.2
    rw [hb] at hdecision
    change (if ω∈P.accepted n (P.rule.state n w) then true else false)=true at hdecision
    by_contra hn
    simp only [if_neg hn,Bool.false_eq_true] at hdecision
end CriticalPercolation.Corridor.Scheme
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Criticality.ActualGrowth
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.Corridor.Scheme
open BondGraph Boundary BernoulliProduct
variable {V E : Type*} [Countable V] [Countable E] (P : Scheme V E)
def actual (n : ℕ) (ω : Set E) : GrowthState := P.rule.state n (P.rule.codeOf n ω)
lemma actual_succ (n : ℕ) (ω : Set E) :
    P.actual (n+1) ω=(P.actual n ω).advance n
      (if ω∈P.accepted n (P.actual n ω) then true else false) := rfl
lemma actual_good_mono (ω : Set E) : Monotone (fun n => ((P.actual n ω).good : Set Site)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [P.actual_succ]
  exact GrowthState.good_mono _ _ _
lemma actual_root (n : ℕ) (ω : Set E) : (0,0)∈(P.actual n ω).good :=
  P.state_valid n (P.rule.codeOf n ω) |>.1
def allGood (ω : Set E) : Set Site := ⋃ n, ((P.actual n ω).good : Set Site)
lemma allGood_root (ω : Set E) : (0,0)∈P.allGood ω := Set.mem_iUnion.mpr ⟨0,P.actual_root 0 ω⟩
lemma allGood_quadrant (ω : Set E) {v : Site} (hv : v∈P.allGood ω) : quadrant v := by
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hv
  exact P.state_valid n (P.rule.codeOf n ω) |>.2.1 v hn |>.1
lemma actual_good_birth (n : ℕ) (ω : Set E) {v : Site} (hv : v∈(P.actual n ω).good) :
    v=(0,0) ∨ ∃ k, v=slotSite k ∧ v∈(P.actual (k+1) ω).good := by
  induction n with
  | zero => exact Or.inl (by simpa [actual,DecisionRule.state,rule,GrowthState.initial] using hv)
  | succ n ih =>
    have hvo := hv
    rw [P.actual_succ] at hv
    change v∈(if (incoming n (P.actual n ω).good).isSome ∧
      (if ω∈P.accepted n (P.actual n ω) then true else false)=true
      then insert (slotSite n) (P.actual n ω).good else (P.actual n ω).good) at hv
    by_cases ha : (incoming n (P.actual n ω).good).isSome ∧
      (if ω∈P.accepted n (P.actual n ω) then true else false)=true
    · rw [if_pos ha] at hv
      rcases Finset.mem_insert.mp hv with hv|hv
      · exact Or.inr ⟨n,hv,hvo⟩
      · exact ih hv
    · rw [if_neg ha] at hv
      exact ih hv
lemma good_parent_present (ω : Set E) {e : Edge} (hp : source e∈P.allGood ω) :
    source e∈(P.actual (gridSlot (target e)) ω).good := by
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hp
  have hq := (P.state_valid n (P.rule.codeOf n ω)).2.1 _ hn |>.1
  have hlt := parent_slot_lt e hq
  rcases P.actual_good_birth n ω hn with he|⟨k,he,hg⟩
  · rw [he]
    exact P.actual_root _ _
  · have hsk : gridSlot (source e)=k := by rw [he,gridSlot_slotSite]
    exact P.actual_good_mono ω (show k+1 ≤ gridSlot (target e) by omega) hg
lemma missing_child_fails (ω : Set E) (z : Site) (hz : z∉P.allGood ω)
    (hc : ∃ y∈P.allGood ω, z=y+(1,0) ∨ z=y+(0,1)) :
    ω∈P.rule.failure (gridSlot z) := by
  obtain ⟨y,hy,hz'⟩ := hc
  let e : Edge := (y,if z=y+(1,0) then true else false)
  have he : target e=z := by
    by_cases hh : z=y+(1,0)
    · simp [e,target,hh]
    · rcases hz' with hz'|hz'
      · exact (hh hz').elim
      · simp [e,target,hz']
  have hp : source e∈P.allGood ω := hy
  have hyp := P.good_parent_present ω hp
  rw [he] at hyp
  have hqz := target_quadrant e (P.allGood_quadrant ω hp)
  rw [he] at hqz
  have hs : slotSite (gridSlot z)=z := slotSite_gridSlot z hqz
  have hex : ∃ f, incoming (gridSlot z) (P.actual (gridSlot z) ω).good=some f := by
    apply incoming_exists
    refine ⟨y,hyp,?_⟩
    rwa [hs]
  obtain ⟨f,hf⟩ := hex
  apply (P.rule.failure_on_cell (gridSlot z) (P.rule.codeOf_mem _ ω)).mpr
  constructor
  · change (incoming (gridSlot z) (P.actual (gridSlot z) ω).good).isSome
    simp [hf]
  · change ω∉P.accepted (gridSlot z) (P.actual (gridSlot z) ω)
    intro ha
    apply hz
    apply Set.mem_iUnion.mpr
    refine ⟨gridSlot z+1,?_⟩
    rw [P.actual_succ]
    change z∈(if (incoming (gridSlot z) (P.actual (gridSlot z) ω).good).isSome ∧
      (if ω∈P.accepted (gridSlot z) (P.actual (gridSlot z) ω) then true else false)=true
      then insert (slotSite (gridSlot z)) (P.actual (gridSlot z) ω).good else (P.actual (gridSlot z) ω).good)
    simp [hf,ha,hs]
lemma allGood_reached (hh : 0≤P.h) (hhj : P.h≤P.j) (hsep : 2*P.j+P.h<1)
    (hroot : (P.seed∩P.mark (0,0)).Nonempty) {ω : Set E} (hB : ω∈P.rootEvent)
    {v : Site} (hv : v∈P.allGood ω) : ω∈P.graph.seedHitEvent P.seed (P.mark v) := by
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hv
  have hs := P.stable_on_cell hh hhj hsep hroot n (P.rule.codeOf n ω) ω (P.rule.codeOf_mem n ω) hB
  have hr := hs.1 v hn
  exact P.graph.seedHitEvent_upper _ _ (Set.inter_subset_left) hr
end CriticalPercolation.Corridor.Scheme
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.GraphGeometry.MarkConnectivity
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation
theorem infinite_cluster_of_reached_marks {V I : Type*} (H : SimpleGraph V)
    (seed : Finset V) (J : Set I) (hJ : J.Infinite) (mark : I → Set V)
    (hdis : Pairwise (Disjoint on mark))
    (hreach : ∀ i∈J, ∃ v∈mark i, ∃ a∈seed, H.Reachable a v) :
    ∃ a∈seed, ({v | H.Reachable a v} : Set V).Infinite := by
  let := hJ.to_subtype
  have hex (i : J) : ∃ v∈mark i, ∃ a∈seed, H.Reachable a v := hreach i i.2
  choose v hv using hex
  have hinj : Function.Injective v := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    exact Set.disjoint_left.mp (hdis hne) (hv i).1 (hij ▸ (hv j).1)
  have hi : (Set.range v).Infinite := Set.infinite_range_of_injective hinj
  by_contra hn
  push Not at hn
  have hf : (⋃ a∈seed, {v | H.Reachable a v}).Finite :=
    seed.finite_toSet.biUnion (fun a ha => hn a ha)
  apply hi.not_finite (hf.subset ?_)
  rintro _ ⟨i,rfl⟩
  obtain ⟨a,ha,hr⟩ := (hv i).2
  exact Set.mem_iUnion.mpr ⟨a,Set.mem_iUnion.mpr ⟨ha,hr⟩⟩
namespace BondGraph
variable {V E I : Type*} (G : BondGraph V E)
lemma percolation_of_infinite_marks (p : unitInterval) (B : Set (Set E))
    (J : Set E → Set I) (seed : Finset V) (mark : I → Set V)
    (hdis : Pairwise (Disjoint on mark))
    (hreach : ∀ ω∈B, ∀ i∈J ω, ∃ v∈mark i, ∃ a∈seed,
      (G.openGraph ω).Reachable a v)
    (hpos : 0 < (G.law p).real (B∩{ω | (J ω).Infinite})) :
    0<G.law p G.percolates := by
  have hsub : B∩{ω | (J ω).Infinite}⊆G.percolates := by
    intro ω hω
    obtain ⟨a,_ha,hi⟩ := infinite_cluster_of_reached_marks (G.openGraph ω) seed
      (J ω) hω.2 mark hdis (hreach ω hω.1)
    exact ⟨a,hi⟩
  exact (ENNReal.toReal_pos_iff.mp hpos).1.trans_le (measure_mono hsub)
end BondGraph
end CriticalPercolation
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Criticality.GrowthEstimate
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.Corridor.Scheme
open BondGraph Boundary BernoulliProduct
variable {V E : Type*} [Countable V] [Countable E] (P : Scheme V E)
lemma local_failure_bound (hh : 0≤P.h) (hhj : P.h≤P.j) (hsep : 2*P.j+P.h<1)
    (hroot : (P.seed∩P.mark (0,0)).Nonempty) (hδ : 0<P.delta)
    (a : ℝ) (hε : 0≤P.delta+2*a/P.delta)
    (hpros : ∀ n S, S.Valid n → S.Covered → (incoming n S.good).isSome →
      ∀ ω b, (blockProbability P.parameter (P.block S)
        (P.incomingHit n S\P.nextHit n S b) ω).toReal ≤ a)
    (n : ℕ) (w : DecisionCode n) (ω : Set E)
    (hw : ω∈(P.rule.partition n).cell w) (hB : ω∈P.rootEvent) :
    (blockProbability P.parameter (P.rule.block (P.rule.state n w))
      {σ | P.rule.active n (P.rule.state n w) ∧ σ∉P.rule.accept n (P.rule.state n w)} ω).toReal
      ≤ P.delta+2*a/P.delta := by
  let S := P.rule.state n w
  have hs := P.stable_on_cell hh hhj hsep hroot n w ω hw hB
  by_cases ha : (incoming n S.good).isSome
  · obtain ⟨e,he⟩ := Option.isSome_iff_exists.mp ha
    have ht : target e=slotSite n := incoming_target he
    have hh := hs.2 e (incoming_source he) (by rw [ht,gridSlot_slotSite])
    have hin : 1-P.delta ≤ (blockProbability P.parameter (P.block S) (P.incomingHit n S) ω).toReal := by
      simpa only [incomingHit,P.enlarged_incoming n S he,ht] using hh
    have hloc := pinned_prediction_failure P.parameter (P.block S) (P.enlarged n S) ω
      (P.block_enlarged n S) (P.incomingHit n S) (P.nextHit n S true) (P.nextHit n S false)
      (P.graph.measurableSet_restrictedSeed _ _ _)
      (P.graph.restrictedSeed_measurable _ _ _) (P.graph.restrictedSeed_measurable _ _ _)
      P.delta a hδ hin (hpros n S (P.state_valid n w) (P.state_covered n w) ha ω true)
      (hpros n S (P.state_valid n w) (P.state_covered n w) ha ω false)
    have hevent : {σ | P.rule.active n S ∧ σ∉P.rule.accept n S}=
        predictionFailure P.parameter (P.enlarged n S) (P.incomingHit n S)
          (P.nextHit n S true) (P.nextHit n S false) P.delta := by
      ext σ
      change ((incoming n S.good).isSome ∧ ¬¬σ∈_) ↔ _
      simp only [ha,true_and,not_not]
    change (blockProbability P.parameter (P.block S) _ ω).toReal ≤ _
    rw [hevent]
    exact hloc
  · have hevent : {σ | P.rule.active n S ∧ σ∉P.rule.accept n S}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro σ hσ
      exact ha hσ.1
    change (blockProbability P.parameter (P.block S) _ ω).toReal ≤ _
    rw [hevent]
    simpa only [blockProbability,Set.preimage_empty,measure_empty,ENNReal.toReal_zero] using hε
theorem exploration_percolates (hh : 0≤P.h) (hhj : P.h≤P.j) (hsep : 2*P.j+P.h<1)
    (seed : Finset V) (hseed : P.seed=seed) (hroot : (P.seed∩P.mark (0,0)).Nonempty)
    (hmark : Pairwise (Disjoint on P.mark))
    (p : unitInterval) (hp : P.parameter=fun _ => p)
    (hB : 0<(law P.parameter).real P.rootEvent) (hδ : 0<P.delta)
    (a q : ℝ) (hq₀ : 0≤q) (hq : 8*q<1) (ha : 0≤a)
    (herr : P.delta+2*a/P.delta ≤ q^4)
    (hpros : ∀ n S, S.Valid n → S.Covered → (incoming n S.good).isSome →
      ∀ ω b, (blockProbability P.parameter (P.block S)
        (P.incomingHit n S\P.nextHit n S b) ω).toReal ≤ a) :
    0<P.graph.law p P.graph.percolates := by
  have hε : 0≤P.delta+2*a/P.delta := by positivity
  have hlocal := P.local_failure_bound hh hhj hsep hroot hδ a hε hpros
  have hcond := P.rule.conditional_failure_bound P.parameter P.rootEvent _ hε hlocal
  have hi := infinitely_many_good_from_tests (law P.parameter)
    (fun n => (P.rule.partition n).historySigma) P.rule.historySigma_mono P.rule.failure
    P.rule.failure_history_measurable P.rootEvent P.rootEvent_history hB P.allGood
    (fun ω _ => P.allGood_root ω) (fun ω _ v hv => P.allGood_quadrant ω hv)
    (fun ω _ => P.missing_child_fails ω) q hq₀ hq (by
      intro n A hm hAB
      exact (hcond n A hm hAB).trans (mul_le_mul_of_nonneg_right herr (measureReal_nonneg)))
  have hlaw : law P.parameter=P.graph.law p := by rw [hp]; exact BernoulliProduct.law_const p
  rw [hlaw] at hi
  apply P.graph.percolation_of_infinite_marks p P.rootEvent P.allGood seed P.mark hmark _ hi
  intro ω hω v hv
  have hr := P.allGood_reached hh hhj hsep hroot hω hv
  obtain ⟨a,ha,b,hr,hb⟩ := Set.mem_iUnion₂.mp hr
  exact ⟨b,hb,a,by simpa only [hseed,Finset.mem_coe] using ha,hr⟩
end CriticalPercolation.Corridor.Scheme
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.ProductMeasure.FreshRegionLaw
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}
lemma trim_law_eq (q r : E → unitInterval) (S : Set E) (h : ∀ e∈S, q e=r e) :
    (law q).map (forceOn Sᶜ ∅)=(law r).map (forceOn Sᶜ ∅) := by
  rw [forceOn_map_law,forceOn_map_law]
  congr 1
  funext e
  by_cases he : e∈S
  · simp [pinnedParameters,he,h e he]
  · simp [pinnedParameters,he]
lemma fresh_region_lower (q r : E → unitInterval) (S : Set E) (h : ∀ e∈S, q e=r e)
    (B : Set (Set E)) (hm : MeasurableSet B) (hu : IsUpperSet B) :
    (law r).real ((forceOn Sᶜ ∅) ⁻¹' B) ≤ (law q).real B := by
  have he : (law r) ((forceOn Sᶜ ∅) ⁻¹' B)=(law q) ((forceOn Sᶜ ∅) ⁻¹' B) := by
    rw [← Measure.map_apply (measurable_forceOn _ _) hm,
      ← Measure.map_apply (measurable_forceOn _ _) hm,trim_law_eq q r S h]
  rw [measureReal_def,he]
  change (law q).real ((forceOn Sᶜ ∅) ⁻¹' B) ≤ _
  apply measureReal_mono _ (measure_ne_top _ _)
  intro ω hω
  apply hu (a := forceOn Sᶜ ∅ ω) (b := ω) ?_ hω
  intro e he
  by_cases hes : e∈S
  · simpa [forceOn,hes] using he
  · simp [hes] at he
end CriticalPercolation.BernoulliProduct
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.ProductMeasure.ProductEmbedding
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical
namespace CriticalPercolation.BernoulliProduct
variable {A E : Type*}
lemma law_map_preimage (q : E → unitInterval) (i : A → E) (hi : Injective i) :
    (law q).map (fun ω : Set E => i ⁻¹' ω)=law (q∘i) := by
  have hind : iIndepFun (fun a (ω : Set E) => i a∈ω) (law q) :=
    iIndepFun.precomp hi (independent_coordinates q)
  have hh := hind.map_fun_eq_infinitePi_map (fun a => measurable_set_mem (i a))
  change (law q).map (fun ω : Set E => i ⁻¹' ω)=_ at hh
  rw [hh]
  rw [law_eq_infinitePi (q∘i)]
  apply congrArg Measure.infinitePi
  funext a
  rw [law_eq_infinitePi]
  exact Measure.infinitePi_map_eval _ (i a)
end CriticalPercolation.BernoulliProduct
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.SourceGraph
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)
def withSource (A : Set V) : BondGraph (Option V) (E⊕A) where
  ends e := match e with
    | Sum.inl b => Sym2.map Option.some (G.ends b)
    | Sum.inr a => s(none,some a.val)
lemma withSource_local (hl : G.LocallyFinite) {A : Set V} (hA : A.Finite) :
    (G.withSource A).LocallyFinite := by
  intro v
  have hw : (Set.range (Sum.inr : A → E⊕A)).Finite := by
    let := hA.fintype
    exact Set.finite_range _
  cases v with
  | none =>
    apply hw.subset
    intro e he
    cases e with
    | inl e => simp [withSource] at he
    | inr a => exact ⟨a,rfl⟩
  | some v =>
    apply ((hl v).image Sum.inl |>.union hw).subset
    intro e he
    cases e with
    | inl e =>
      apply Or.inl
      refine ⟨e,?_,rfl⟩
      simpa [withSource] using he
    | inr a => exact Or.inr ⟨a,rfl⟩
lemma withSource_original_adj (A : Set V) (ω : Set (E⊕A)) {v w : V}
    (h : (G.openGraph (Sum.inl ⁻¹' ω)).Adj v w) :
    ((G.withSource A).openGraph ω).Adj (some v) (some w) := by
  obtain ⟨⟨e,he,hend⟩,hne⟩ := h
  exact ⟨⟨Sum.inl e,he,by simp [withSource,hend]⟩,fun h => hne (Option.some.inj h)⟩
lemma withSource_original_reachable (A : Set V) (ω : Set (E⊕A)) {v w : V}
    (h : (G.openGraph (Sum.inl ⁻¹' ω)).Reachable v w) :
    ((G.withSource A).openGraph ω).Reachable (some v) (some w) :=
  h.map ⟨Option.some,fun hvw => G.withSource_original_adj A ω hvw⟩
lemma withSource_seedHit [Countable V] [Countable E] (A B T : Set V)
    (q : (E⊕A) → unitInterval) :
    (BernoulliProduct.law (fun e => q (Sum.inl e))).real (G.seedHitEvent B T) ≤
      (BernoulliProduct.law q).real ((G.withSource A).seedHitEvent (Option.some '' B) (Option.some '' T)) := by
  have hm : Measurable (fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω : Set (E⊕A) → Set E) :=
    measurable_pi_lambda _ (fun edge => measurable_set_mem (Sum.inl edge))
  have hlaw : BernoulliProduct.law (fun e => q (Sum.inl e)) =
      (BernoulliProduct.law q).map (fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω) :=
    (BernoulliProduct.law_map_preimage q Sum.inl Sum.inl_injective).symm
  rw [hlaw,measureReal_def,
    Measure.map_apply hm (G.measurableSet_seedHitEvent B T)]
  change (BernoulliProduct.law q).real ((fun ω => Sum.inl ⁻¹' ω) ⁻¹' G.seedHitEvent B T) ≤ _
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  obtain ⟨v,hv,w,hvw,hw⟩ := Set.mem_iUnion₂.mp hω
  exact Set.mem_iUnion₂.mpr ⟨some v,⟨v,hv,rfl⟩,some w,
    G.withSource_original_reachable A ω hvw,⟨w,hw,rfl⟩⟩
lemma withSource_incident (A : Set V) {v : V} (hv : v∉A) :
    (G.withSource A).incidentEdges {some v}=Sum.inl '' G.incidentEdges {v} := by
  ext e
  cases e with
  | inl e => simp [incidentEdges,withSource]
  | inr a =>
    have hne : v≠a.val := fun hh => hv (hh.symm ▸ a.property)
    simp [incidentEdges,withSource,hne]
lemma withSource_trial_reachable (A : Set V) (F : Set E) {v w : V}
    (h : (G.openGraph F).Reachable v w) :
    ((G.withSource A).openGraph (Sum.inl '' F)).Reachable (some v) (some w) := by
  apply G.withSource_original_reachable
  simpa only [Set.preimage_image_eq _ Sum.inl_injective] using h
end CriticalPercolation.BondGraph
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.HonestChoice
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory
open scoped Classical
namespace CriticalPercolation
variable {Ω I : Type*} [MeasurableSpace Ω]
def firstTest (P : ℕ → Ω → Prop) (ω : Ω) : ℕ :=
  if h : ∃ n, P n ω then Nat.find h else 0
omit [MeasurableSpace Ω] in
lemma firstTest_eq (P : ℕ → Ω → Prop) (ω : Ω) (n : ℕ) :
    firstTest P ω=n ↔ (P n ω ∧ ∀ m<n, ¬P m ω) ∨ ((¬∃ m, P m ω) ∧ n=0) := by
  by_cases h : ∃ m, P m ω
  · simp [firstTest,h,Nat.find_eq_iff]
  · have hn : ¬P n ω := fun hn => h ⟨n,hn⟩
    simp [firstTest,h,hn,eq_comm]
lemma measurableSet_firstTest (P : ℕ → Ω → Prop) (hP : ∀ n, MeasurableSet {ω | P n ω}) (n : ℕ) :
    MeasurableSet {ω | firstTest P ω=n} := by
  simp_rw [firstTest_eq]
  apply MeasurableSet.union
  · exact (hP n).inter ((Measurable.forall (fun m => measurable_const.imp (hP m).mem.not)).setOf)
  · exact (Measurable.exists (fun m => (hP m).mem)).setOf.compl.inter (MeasurableSet.const _)
theorem exists_honest_selector [Countable I] [Nonempty I] (P : Ω → I → Prop)
    (hP : ∀ i, MeasurableSet {ω | P ω i}) :
    ∃ d : Ω → I, (∀ i, MeasurableSet {ω | d ω=i}) ∧
      ∀ ω, (∃ i, P ω i) → P ω (d ω) := by
  obtain ⟨e,he⟩ := exists_surjective_nat I
  let d : Ω → I := fun ω => e (firstTest (fun n ω => P ω (e n)) ω)
  refine ⟨d,?_,?_⟩
  · intro i
    have hh : {ω | d ω=i}=⋃ n : ℕ, ({ω | firstTest (fun n ω => P ω (e n)) ω=n}∩{_ω | e n=i}) := by
      ext ω
      simp only [Set.mem_iUnion,Set.mem_inter_iff,Set.mem_ofPred_eq]
      exact ⟨fun h => ⟨_,rfl,h⟩,fun ⟨n,hn,hni⟩ => by dsimp [d]; rw [hn,hni]⟩
    rw [hh]
    exact MeasurableSet.iUnion (fun n => (measurableSet_firstTest _ (fun m => hP (e m)) n).inter
      (MeasurableSet.const _))
  · intro ω ⟨i,hi⟩
    obtain ⟨n,rfl⟩ := he i
    have hex : ∃ n, P ω (e n) := ⟨n,hi⟩
    dsimp [d,firstTest]
    rw [dif_pos hex]
    exact Nat.find_spec hex
end CriticalPercolation
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.TrialSelection
section

namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical BigOperators
namespace CriticalPercolation
theorem separated_subset_of_card {V : Type*} (C : V → V → Prop)
    (hrefl : ∀ v, C v v) (hsymm : ∀ {v w}, C v w → C w v)
    (M N : ℕ) (hM : 0 < M) (S : Finset V)
    (hb : ∀ v∈S, (S.filter (C v)).card ≤ M) (hcard : M*N ≤ S.card) :
    ∃ U ⊆ S, U.card=N ∧ (U : Set V).Pairwise (fun v w => ¬C v w) := by
  induction N generalizing S with
  | zero => exact ⟨∅,Finset.empty_subset _,by simp,by simp⟩
  | succ N ih =>
    have hSpos : 0 < S.card := by nlinarith
    obtain ⟨v,hv⟩ := Finset.card_pos.mp hSpos
    let T := S.filter (fun w => ¬C v w)
    have hT : T ⊆ S := Finset.filter_subset _ _
    have hbT : ∀ w∈T, (T.filter (C w)).card ≤ M := by
      intro w hw
      exact (Finset.card_le_card (Finset.filter_subset_filter _ hT)).trans (hb w (hT hw))
    have hcT : M*N ≤ T.card := by
      have he := S.card_filter_add_card_filter_not (C v)
      have hh := hb v hv
      change M*N ≤ (S.filter (fun w => ¬C v w)).card
      nlinarith
    obtain ⟨U,hUT,hUc,hUp⟩ := ih T hbT hcT
    have hvU : v∉U := by
      intro h
      exact (Finset.mem_filter.mp (hUT h)).2 (hrefl v)
    refine ⟨insert v U,Finset.insert_subset hv (hUT.trans hT),by simp [hvU,hUc],?_⟩
    intro x hx y hy hxy
    simp only [Finset.coe_insert,Set.mem_insert_iff] at hx hy
    rcases hx with rfl|hx  <;> rcases hy with rfl|hy
    · exact (hxy rfl).elim
    · exact (Finset.mem_filter.mp (hUT hy)).2
    · intro h
      exact (Finset.mem_filter.mp (hUT hx)).2 (hsymm h)
    · exact hUp hx hy hxy
theorem exists_weight_interval {V : Type*} (S : Finset V) (s : V → ℝ)
    (hs : ∀ v∈S, s v ≤ 1) (K : ℝ) (hK : 0 ≤ K) (hSK : K ≤ ∑ v∈S, s v) :
    ∃ U ⊆ S, K ≤ ∑ v∈U, s v ∧ (∑ v∈U, s v) ≤ K+1 := by
  induction S using Finset.induction_on with
  | empty => exact ⟨∅,by simp,by simpa using hSK,by simp; linarith⟩
  | @insert v S hv ih =>
    by_cases h : K ≤ ∑ w∈S, s w
    · obtain ⟨U,hU,hlo,hhi⟩ := ih (fun w hw => hs w (Finset.mem_insert_of_mem hw)) h
      exact ⟨U,hU.trans (Finset.subset_insert _ _),hlo,hhi⟩
    · refine ⟨insert v S,Finset.Subset.refl _,hSK,?_⟩
      rw [Finset.sum_insert hv]
      have hh := hs v (Finset.mem_insert_self _ _)
      linarith
theorem separated_weighted_trials {V : Type*} (C : V → V → Prop)
    (hrefl : ∀ v, C v v) (hsymm : ∀ {v w}, C v w → C w v)
    (M N : ℕ) (hM : 0 < M) (S : Finset V)
    (hb : ∀ v∈S, (S.filter (C v)).card ≤ M) (hcard : M*N ≤ S.card)
    (s : V → ℝ) (s₀ K : ℝ) (hK : 0 ≤ K)
    (hs : ∀ v∈S, s₀ ≤ s v ∧ s v ≤ 1) (hN : K ≤ N*s₀) :
    ∃ U ⊆ S, (U : Set V).Pairwise (fun v w => ¬C v w) ∧
      K ≤ ∑ v∈U, s v ∧ (∑ v∈U, s v) ≤ K+1 := by
  obtain ⟨T,hTS,hTc,hTp⟩ := separated_subset_of_card C hrefl hsymm M N hM S hb hcard
  have hKT : K ≤ ∑ v∈T, s v := by
    calc K ≤ N*s₀ := hN
         _ = ∑ _v∈T, s₀ := by simp [hTc]
         _  ≤  _ := Finset.sum_le_sum (fun v hv => (hs v (hTS hv)).1)
  obtain ⟨U,hUT,hlo,hhi⟩ := exists_weight_interval T s (fun v hv => (hs v (hTS hv)).2)
    K hK hKT
  exact ⟨U,hUT.trans hTS,hTp.mono hUT,hlo,hhi⟩
end CriticalPercolation
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.ContactSelection
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory
open scoped Classical BigOperators
namespace CriticalPercolation
lemma measurableSet_finset_subset {Ω V : Type*} {m : MeasurableSpace Ω}
    (S : Ω → Set V) (hS : @Measurable Ω (Set V) m inferInstance S) (U : Finset V) :
    MeasurableSet[m] {ω | (U : Set V)⊆S ω} := by
  have he : {ω | (U : Set V)⊆S ω}=⋂ v∈U, {ω | v∈S ω} := by
    ext ω
    simp [Set.subset_def]
  rw [he]
  exact MeasurableSet.biInter U.countable_toSet (fun v _ =>
    ((measurable_pi_apply v).comp hS).setOf)
namespace BondGraph
open BernoulliProduct
variable {V E : Type*} (G : BondGraph V E)
lemma levelContacts_reachable (π : V → ℤ) (j : ℤ) (o : V) (ω : Set E)
    {v : V} (hv : v∈G.levelContacts π j o ω) : (G.openGraph ω).Reachable o v :=
  G.cluster_mono Set.inter_subset_left o hv.1
lemma levelContacts_nonempty_of_hit (π : V → ℤ) (j : ℤ) (o : V) (ho : j ≤ π o)
    (hcross : ∀ e v w, G.ends e=s(v,w) → j ≤ π v → π w<j → π v=j)
    (ω : Set E) (hhit : ω∈G.hitEvent o {v | π v<j}) :
    (G.levelContacts π j o ω).Nonempty := by
  by_contra h
  have hd : G.contactDrop π j o ω=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro e ⟨v,hv,w,hw,hend⟩
    exact h ⟨v,hv⟩
  have hc : Disjoint (G.contactDrop π j o ω) ω := by rw [hd]; exact Set.empty_disjoint _
  have he := G.cluster_eq_exterior_of_drop_closed π j o ho hcross ω hc
  obtain ⟨v,hv,hlt⟩ := hhit
  have hle : j ≤ π v := G.exteriorCluster_subset_level π j o ho ω (he ▸ hv)
  exact (not_le.mpr hlt) hle
lemma levelContacts_supply (π : V → ℤ) (j : ℤ) (o : V) (k : ℕ) (ω : Set E)
    (hne : (G.levelContacts π j o ω).Nonempty) (hfew : ω∉G.fewContacts π j o k) :
    ∃ S : Finset V, (S : Set V)⊆G.levelContacts π j o ω ∧ k ≤ S.card := by
  by_cases hfin : (G.levelContacts π j o ω).Finite
  · refine ⟨hfin.toFinset,by simp,?_⟩
    by_contra hcard
    exact hfew ⟨hfin.toFinset,hfin.coe_toFinset.symm,
      by simpa using hne,lt_of_not_ge hcard⟩
  · obtain ⟨S,hS,hSfin,hcard⟩ := Set.Infinite.exists_subset_ncard_eq hfin k
    exact ⟨hSfin.toFinset,by simpa using hS,by simpa [Set.ncard_eq_toFinset_card S hSfin] using hcard.ge⟩
variable [Countable V] [Countable E]
def manyContacts (π : V → ℤ) (j : ℤ) (o : V) (k : ℕ) : Set (Set E) :=
  {ω | (G.levelContacts π j o ω).Nonempty}\G.fewContacts π j o k
lemma measurableSet_manyContacts (π : V → ℤ) (j : ℤ) (o : V) (k : ℕ) :
    MeasurableSet[blockSigma (G.inducedEdges {v | j ≤ π v})] (G.manyContacts π j o k) := by
  apply MeasurableSet.diff _ (G.measurableSet_fewContacts π j o k)
  have he : {ω | (G.levelContacts π j o ω).Nonempty}=⋃ v : V, {ω | v∈G.levelContacts π j o ω} := by
    ext ω
    simp [Set.Nonempty]
  rw [he]
  exact MeasurableSet.iUnion (fun v =>
    @Measurable.setOf (Set E) (blockSigma (G.inducedEdges {v | j ≤ π v})) _
      ((measurable_pi_apply v).comp (G.measurable_levelContacts π j o)))
theorem honest_contact_selection (π : V → ℤ) (j : ℤ) (o : V) (k : ℕ)
    (C : V → V → Prop) (hrefl : ∀ v, C v v) (hsymm : ∀ {v w}, C v w → C w v)
    (M N : ℕ) (hM : 0 < M) (hk : M*N ≤ k)
    (hfinite : ∀ v, {w | C v w}.Finite) (hbound : ∀ v, {w | C v w}.ncard ≤ M)
    (s : V → ℝ) (s₀ K : ℝ) (hK : 0 ≤ K)
    (hs : ∀ v, π v=j → s₀ ≤ s v ∧ s v ≤ 1) (hN : K ≤ N*s₀) :
    ∃ d : Set E → Finset V,
      (∀ U, MeasurableSet[blockSigma (G.inducedEdges {v | j ≤ π v})] {ω | d ω=U}) ∧
      ∀ ω∈G.manyContacts π j o k,
        (d ω : Set V)⊆G.levelContacts π j o ω ∧
        (d ω : Set V).Pairwise (fun v w => ¬C v w) ∧
        K ≤ ∑ v∈d ω, s v ∧ (∑ v∈d ω, s v) ≤ K+1 := by
  let P := fun (ω : Set E) (U : Finset V) =>
    (U : Set V)⊆G.levelContacts π j o ω ∧
    (U : Set V).Pairwise (fun v w => ¬C v w) ∧
    K ≤ ∑ v∈U, s v ∧ (∑ v∈U, s v) ≤ K+1
  have hm (U : Finset V) : MeasurableSet[blockSigma (G.inducedEdges {v | j ≤ π v})] {ω | P ω U} :=
    (measurableSet_finset_subset _ (G.measurable_levelContacts π j o) U).inter (MeasurableSet.const _)
  obtain ⟨d,hd,hgood⟩ := @exists_honest_selector (Set E) (Finset V)
    (blockSigma (G.inducedEdges {v | j ≤ π v})) inferInstance inferInstance P hm
  refine ⟨d,hd,?_⟩
  intro ω hω
  apply hgood
  obtain ⟨S,hS,hcard⟩ := G.levelContacts_supply π j o k ω hω.1 hω.2
  have hb : ∀ v∈S, (S.filter (C v)).card ≤ M := by
    intro v _hv
    have hh : (S.filter (C v) : Set V)⊆{w | C v w} := by
      intro w hw
      exact (Finset.mem_filter.mp hw).2
    have hz := (Set.ncard_le_ncard hh (hfinite v)).trans (hbound v)
    simpa only [Set.ncard_coe_finset] using hz
  obtain ⟨U,hU,hsep,hlo,hhi⟩ := separated_weighted_trials C hrefl hsymm M N hM S hb
    (hk.trans hcard) s s₀ K hK (fun v hv => hs v (hS hv).2) hN
  exact ⟨U,(fun _ hv => hS (hU hv)),hsep,hlo,hhi⟩
end BondGraph
end CriticalPercolation
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.SelectedFresh
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
namespace CriticalPercolation.BernoulliProduct
variable {E I : Type*}
lemma block_event_disjoint_forceOn (X Y : Set E) (hXY : Disjoint X Y)
    (A : Set (Set E)) (hA : MeasurableSet[blockSigma Y] A) (σ ω : Set E) :
    forceOn X σ ω∈A ↔ ω∈A := by
  have he : forceOn Y (forceOn X σ ω) ω=ω := by
    ext e
    by_cases heY : e∈Y
    · have heX : e∉X := fun h => Set.disjoint_left.mp hXY h heY
      simp only [mem_forceOn,if_pos heY,if_neg heX]
    · simp only [mem_forceOn,if_neg heY]
  have hh := block_event_forceOn Y A hA (forceOn X σ ω) ω
  rw [he] at hh
  exact hh.symm
def selectedEvent (d : Set E → I) (A : I → Set (Set E)) : Set (Set E) :=
  {ω | ω∈A (d ω)}
lemma selectedEvent_eq_iUnion (d : Set E → I) (A : I → Set (Set E)) :
    selectedEvent d A=⋃ i, ({ω | d ω=i}∩A i) := by
  ext ω
  simp only [selectedEvent,Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_inter_iff]
  exact ⟨fun h => ⟨d ω,rfl,h⟩,fun ⟨i,hi,h⟩ => hi.symm ▸ h⟩
lemma measurableSet_selectedEvent [Countable I] (d : Set E → I)
    (A : I → Set (Set E)) (hd : ∀ i, MeasurableSet {ω | d ω=i})
    (hA : ∀ i, MeasurableSet (A i)) : MeasurableSet (selectedEvent d A) := by
  rw [selectedEvent_eq_iUnion]
  exact MeasurableSet.iUnion (fun i => (hd i).inter (hA i))
theorem blockProbability_selected (q : E → unitInterval) (X Y : Set E)
    (hXY : Disjoint X Y) (d : Set E → I) (A : I → Set (Set E))
    (hd : ∀ i, MeasurableSet[blockSigma X] {ω | d ω=i})
    (hA : ∀ i, MeasurableSet[blockSigma Y] (A i)) (σ : Set E) :
    blockProbability q X (selectedEvent d A) σ=law q (A (d σ)) := by
  unfold blockProbability
  congr 1
  ext ω
  change forceOn X σ ω∈A (d (forceOn X σ ω)) ↔ ω∈A (d σ)
  have hh : d (forceOn X σ ω)=d σ :=
    (block_event_forceOn X {τ | d τ=d σ} (hd _) σ ω).mpr rfl
  rw [hh]
  exact block_event_disjoint_forceOn X Y hXY (A (d σ)) (hA _) σ ω
theorem selected_fresh_bound [Countable I] (q : E → unitInterval) (X Y : Set E)
    (hXY : Disjoint X Y) (d : Set E → I) (A : I → Set (Set E))
    (hd : ∀ i, MeasurableSet[blockSigma X] {ω | d ω=i})
    (hA : ∀ i, MeasurableSet[blockSigma Y] (A i))
    (C : Set (Set E)) (hC : MeasurableSet[blockSigma X] C)
    (r : ℝ) (hr : 0 ≤ r) (hb : ∀ σ∈C, (law q).real (A (d σ)) ≤ r) :
    (law q).real (C∩selectedEvent d A) ≤ r*(law q).real C := by
  have hmA := measurableSet_selectedEvent d A (fun i => blockSigma_le X _ (hd i))
    (fun i => blockSigma_le Y _ (hA i))
  have hk (σ : Set E) (hσ : σ∈C) :
      blockProbability q X (selectedEvent d A) σ ≤ ENNReal.ofReal r := by
    rw [blockProbability_selected q X Y hXY d A hd hA σ]
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hr]
    exact hb σ hσ
  have hh : law q (selectedEvent d A∩C) ≤ ENNReal.ofReal r*law q C := by
    rw [← setLIntegral_blockProbability q X _ C hmA hC]
    calc
      (∫⁻ σ in C, blockProbability q X (selectedEvent d A) σ ∂law q) ≤
          ∫⁻ _ in C, ENNReal.ofReal r ∂law q :=
        setLIntegral_mono' (blockSigma_le X _ hC) hk
      _ = _ := by rw [lintegral_const,Measure.restrict_apply_univ]
  have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (measure_ne_top _ _)) hh
  simpa only [Set.inter_comm (selectedEvent d A) C,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hr,Measure.real] using ht
end CriticalPercolation.BernoulliProduct
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.ProductMeasure.LevelCutProbability
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
namespace CriticalPercolation.BernoulliProduct
variable {E I : Type*}
theorem selected_fresh_lower [Countable I] (q : E → unitInterval) (X Y : Set E)
    (hXY : Disjoint X Y) (d : Set E → I) (A : I → Set (Set E))
    (hd : ∀ i, MeasurableSet[blockSigma X] {ω | d ω=i})
    (hA : ∀ i, MeasurableSet[blockSigma Y] (A i))
    (C : Set (Set E)) (hC : MeasurableSet[blockSigma X] C)
    (r : ℝ) (hr : 0 ≤ r) (hb : ∀ σ∈C, r ≤ (law q).real (A (d σ))) :
    r*(law q).real C ≤ (law q).real (C∩selectedEvent d A) := by
  have hmA := measurableSet_selectedEvent d A (fun i => blockSigma_le X _ (hd i))
    (fun i => blockSigma_le Y _ (hA i))
  have hk (σ : Set E) (hσ : σ∈C) :
      ENNReal.ofReal r ≤ blockProbability q X (selectedEvent d A) σ := by
    rw [blockProbability_selected q X Y hXY d A hd hA σ]
    apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (measure_ne_top _ _)).mp
    rw [ENNReal.toReal_ofReal hr]
    exact hb σ hσ
  have hh : ENNReal.ofReal r*law q C ≤ law q (selectedEvent d A∩C) := by
    rw [← setLIntegral_blockProbability q X _ C hmA hC]
    calc
      _ = ∫⁻ _ in C, ENNReal.ofReal r ∂law q := by
        rw [lintegral_const,Measure.restrict_apply_univ]
      _ ≤ _ := setLIntegral_mono' (blockSigma_le X _ hC) hk
  have ht := ENNReal.toReal_mono (measure_ne_top _ _) hh
  simpa only [Set.inter_comm (selectedEvent d A) C,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hr,Measure.real] using ht
lemma law_closedBlock_lower (q : E → unitInterval) (S : Set E) (hS : S.Finite)
    (p : unitInterval) (N : ℕ) (hN : S.ncard ≤ N)
    (hq : ∀ e∈S, (q e : ℝ) ≤ p) :
    (1-(p : ℝ))^N ≤ (law q).real (closedBlock S) := by
  have hp0 : 0 ≤ 1-(p : ℝ) := sub_nonneg.mpr p.2.2
  have hp1 : 1-(p : ℝ) ≤ 1 := by linarith [p.2.1]
  rw [measureReal_def,law_closedBlock q S hS,ENNReal.toReal_prod]
  calc
    _ ≤ (1-(p : ℝ))^S.ncard := pow_le_pow_of_le_one hp0 hp1 hN
    _ = ∏ e∈hS.toFinset, (1-(p : ℝ)) := by simp [Set.ncard_eq_toFinset_card S hS]
    _ ≤ _ := by
      apply Finset.prod_le_prod
      · intro e he; exact hp0
      · intro e he
        change 1-(p : ℝ) ≤ (bitMeasure (q e)).real {False}
        rw [bitMeasure_real_singleton]
        simpa only [bitWeight,if_neg (not_false)] using sub_le_sub_left (hq e (hS.mem_toFinset.mp he)) 1
lemma exists_level_small (μ : Measure (Set E)) [IsProbabilityMeasure μ]
    (J : Finset I) (hJ : J.Nonempty) (C M : I → Set (Set E))
    (hM : ∀ i∈J, MeasurableSet (M i))
    (hdis : (J : Set I).PairwiseDisjoint M) (c : ℝ) (hc : 0 < c)
    (hb : ∀ i∈J, c*μ.real (C i) ≤ μ.real (M i)) :
    ∃ i∈J, μ.real (C i) ≤ 1/((J.card : ℝ)*c) := by
  have hsum : (∑ i∈J, μ.real (M i)) ≤ 1 := by
    rw [← measureReal_biUnion_finset hdis hM]
    exact measureReal_le_one
  have hcard : 0 < (J.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hJ
  by_contra h
  push Not at h
  have hs : (∑ i∈J, 1/(J.card : ℝ)) < ∑ i∈J, μ.real (M i) := by
    apply Finset.sum_lt_sum_of_nonempty hJ
    intro i hi
    have hh := mul_lt_mul_of_pos_left (h i hi) hc
    have he : c*(1/((J.card : ℝ)*c))=1/(J.card : ℝ) := by field_simp
    rw [he] at hh
    exact hh.trans_le (hb i hi)
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  have he : (J.card : ℝ)*(1/(J.card : ℝ))=1 := by field_simp
  rw [he] at hs
  exact (not_lt_of_ge hsum) hs
end CriticalPercolation.BernoulliProduct
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.FewContacts
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
namespace CriticalPercolation.BondGraph
open BernoulliProduct
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)
theorem few_contacts_cost (hlocal : G.LocallyFinite) (q : E → unitInterval)
    (π : V → ℤ) (j : ℤ) (o : V) (ho : j ≤ π o)
    (hcross : ∀ e v w, G.ends e=s(v,w) → j ≤ π v → π w<j → π v=j)
    (p : unitInterval)
    (hq : ∀ e v w, G.ends e=s(v,w) → π v=j → π w<j → (q e : ℝ) ≤ p)
    (D k : ℕ) (hD : ∀ v, π v=j → (G.incidentEdges {v}).ncard ≤ D) :
    (1-(p : ℝ))^(D*k)*(BernoulliProduct.law q).real (G.fewContacts π j o k) ≤
      (BernoulliProduct.law q).real (G.minimumLevel π o j) := by
  let X := G.inducedEdges {v | j ≤ π v}
  let d : Set E → Finset E := fun ω => finiteSetChoice (G.contactDrop π j o ω)
  let A : Finset E → Set (Set E) := fun U => closedBlock ((U : Set E)∩Xᶜ)
  have hd (U : Finset E) : MeasurableSet[blockSigma X] {ω | d ω=U} :=
    @measurableSet_finiteSetChoice (Set E) E (blockSigma X) inferInstance
      (G.contactDrop π j o) (G.measurable_contactDrop π j o) U
  have hA (U : Finset E) : MeasurableSet[blockSigma Xᶜ] (A U) :=
    (blockSigma_mono Set.inter_subset_right) _
      (measurableSet_closedBlock _ ((U.finite_toSet.subset Set.inter_subset_left).countable))
  have he (ω : Set E) (hω : ω∈G.fewContacts π j o k) :
      ((d ω : Set E)∩Xᶜ)=G.contactDrop π j o ω := by
    rw [finiteSetChoice_coe (G.finite_contactDrop hlocal π j o ω
      (G.fewContacts_finite π j o k ω hω).1)]
    exact Set.inter_eq_left.mpr (Set.disjoint_left.mp
      (G.contactDrop_disjoint_exterior π j o ω))
  have hb (ω : Set E) (hω : ω∈G.fewContacts π j o k) :
      (1-(p : ℝ))^(D*k) ≤ (BernoulliProduct.law q).real (A (d ω)) := by
    change _ ≤ (BernoulliProduct.law q).real (closedBlock ((d ω : Set E)∩Xᶜ))
    rw [he ω hω]
    have hω' := G.fewContacts_finite π j o k ω hω
    apply law_closedBlock_lower q _ (G.finite_contactDrop hlocal π j o ω hω'.1) p
    · calc
        _ ≤ (G.levelContacts π j o ω).ncard*D :=
          G.contactDrop_ncard_le hlocal π j o ω hω'.1 D (fun v hv => hD v hv.2)
        _ ≤ k*D := Nat.mul_le_mul_right D (Nat.le_of_lt hω'.2.2)
        _ = D*k := Nat.mul_comm _ _
    · rintro e ⟨v,hv,w,hw,hend⟩
      exact hq e v w hend hv.2 hw
  have hh := selected_fresh_lower q X Xᶜ disjoint_compl_right d A hd hA
    (G.fewContacts π j o k) (G.measurableSet_fewContacts π j o k)
    ((1-(p : ℝ))^(D*k)) (pow_nonneg (sub_nonneg.mpr p.2.2) _) hb
  apply hh.trans
  refine measureReal_mono ?_ (measure_ne_top _ _)
  rintro ω ⟨hω,hclosed⟩
  apply G.minimumLevel_of_drop_closed π j o ho hcross ω
    (G.fewContacts_finite π j o k ω hω).2.1
  change Disjoint ((d ω : Set E)∩Xᶜ) ω at hclosed
  rwa [he ω hω] at hclosed
theorem exists_few_contact_level (hlocal : G.LocallyFinite) (q : E → unitInterval)
    (π : V → ℤ) (o : V) (J : Finset ℤ) (hJ : J.Nonempty)
    (ho : ∀ j∈J, j ≤ π o)
    (hcross : ∀ j∈J, ∀ e v w, G.ends e=s(v,w) → j ≤ π v → π w<j → π v=j)
    (p : unitInterval) (hp : (p : ℝ)<1)
    (hq : ∀ j∈J, ∀ e v w, G.ends e=s(v,w) → π v=j → π w<j → (q e : ℝ) ≤ p)
    (D k : ℕ) (hD : ∀ j∈J, ∀ v, π v=j → (G.incidentEdges {v}).ncard ≤ D) :
    ∃ j∈J, (BernoulliProduct.law q).real (G.fewContacts π j o k) ≤
      1/((J.card : ℝ)*(1-(p : ℝ))^(D*k)) := by
  apply exists_level_small (BernoulliProduct.law q) J hJ (fun j => G.fewContacts π j o k)
    (G.minimumLevel π o) (fun j _ => G.measurableSet_minimumLevel π o j)
  · intro i hi j hj hij
    exact G.minimumLevel_pairwiseDisjoint π o hij
  · exact pow_pos (sub_pos.mpr hp) _
  · intro j hj
    exact G.few_contacts_cost hlocal q π j o (ho j hj) (hcross j hj) p (hq j hj) D k (hD j hj)
end CriticalPercolation.BondGraph
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.ProductMeasure.TrialProbability
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
namespace CriticalPercolation.BernoulliProduct
variable {E V : Type*}
theorem disjoint_trials_no_success [Countable E] (q : E → unitInterval) (F : V → Set E)
    (U : Finset V) (hdis : (U : Set V).Pairwise (fun v w => Disjoint (F v) (F w))) :
    (law q).real (⋂ v∈U, (allOpen (F v))ᶜ)=
      ∏ v∈U, (1-(law q).real (allOpen (F v))) := by
  have hpair : Pairwise (fun v w : U => Disjoint (F v) (F w)) := by
    intro v w hvw
    exact hdis v.2 w.2 (fun h => hvw (Subtype.ext h))
  have he : (⋂ v∈U, (allOpen (F v))ᶜ)=⋂ v : U, (allOpen (F v))ᶜ := by
    ext ω
    simp
  have hi := (independent_block_family q (fun v : U => F v) hpair).meas_iInter
    (fun v => (measurable_allOpen_block (F v)).compl)
  rw [he,measureReal_def,hi,ENNReal.toReal_prod]
  change (∏ v : U, (law q).real ((allOpen (F v))ᶜ))=_
  rw [Finset.prod_coe_sort U (fun v => (law q).real ((allOpen (F v))ᶜ))]
  apply Finset.prod_congr rfl
  intro v _hv
  exact probReal_compl_eq_one_sub ((blockSigma_le _) _ (measurable_allOpen_block (F v)))
theorem disjoint_trials_no_success_le [Countable E] (q : E → unitInterval) (F : V → Set E)
    (U : Finset V) (hdis : (U : Set V).Pairwise (fun v w => Disjoint (F v) (F w)))
    (K : ℝ) (hK : K ≤ ∑ v∈U, (law q).real (allOpen (F v))) :
    (law q).real (⋂ v∈U, (allOpen (F v))ᶜ) ≤ Real.exp (-K) := by
  rw [disjoint_trials_no_success q F U hdis]
  calc
    _ ≤ ∏ v∈U, Real.exp (-(law q).real (allOpen (F v))) := by
      apply Finset.prod_le_prod
      · intro v _hv
        exact sub_nonneg.mpr measureReal_le_one
      · intro v _hv
        simpa only [sub_eq_add_neg,add_comm] using
          Real.add_one_le_exp (-(law q).real (allOpen (F v)))
    _ = Real.exp (-(∑ v∈U, (law q).real (allOpen (F v)))) := by
      rw [← Real.exp_sum,Finset.sum_neg_distrib]
    _ ≤ _ := Real.exp_le_exp.mpr (neg_le_neg hK)
lemma bad_trial_union_bound (q : E → unitInterval) (U : Finset V)
    (Bad : V → Set (Set E)) (s : V → ℝ) (K a : ℝ) (ha : 0 ≤ a)
    (hb : ∀ v∈U, (law q).real (Bad v) ≤ s v*a)
    (hs : (∑ v∈U, s v) ≤ K+1) :
    (law q).real (⋃ v∈U, Bad v) ≤ (K+1)*a := by
  calc
    _ ≤ ∑ v∈U, (law q).real (Bad v) := measureReal_biUnion_finset_le U Bad
    _ ≤ ∑ v∈U, s v*a := Finset.sum_le_sum hb
    _ = (∑ v∈U, s v)*a := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hs ha
end CriticalPercolation.BernoulliProduct
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.SelectedTrials
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
namespace CriticalPercolation.BernoulliProduct
variable {E V : Type*} [Countable E] [Countable V]
lemma selected_no_success_bound (q : E → unitInterval) (X Y : Set E)
    (hXY : Disjoint X Y) (d : Set E → Finset V) (F : V → Set E)
    (hd : ∀ U, MeasurableSet[blockSigma X] {ω | d ω=U})
    (hF : ∀ v, F v ⊆ Y) (C : Set (Set E)) (hC : MeasurableSet[blockSigma X] C)
    (K : ℝ)
    (hdis : ∀ σ∈C, (d σ : Set V).Pairwise (fun v w => Disjoint (F v) (F w)))
    (hs : ∀ σ∈C, K ≤ ∑ v∈d σ, (law q).real (allOpen (F v))) :
    (law q).real (C∩{ω | ∀ v∈d ω, ω∉allOpen (F v)}) ≤ Real.exp (-K)*(law q).real C := by
  have hA (U : Finset V) : MeasurableSet[blockSigma Y] (⋂ v∈U, (allOpen (F v))ᶜ) :=
    MeasurableSet.biInter U.countable_toSet (fun v _ =>
      ((blockSigma_mono (hF v)) _ (measurable_allOpen_block (F v))).compl)
  have hh := selected_fresh_bound q X Y hXY d (fun U => ⋂ v∈U, (allOpen (F v))ᶜ)
    hd hA C hC (Real.exp (-K)) (Real.exp_nonneg _)
    (fun σ hσ => disjoint_trials_no_success_le q F (d σ) (hdis σ hσ) K (hs σ hσ))
  simpa only [selectedEvent,Set.mem_iInter,Set.mem_compl_iff] using hh
lemma selected_bad_trial_bound (q : E → unitInterval) (X Y : Set E)
    (hXY : Disjoint X Y) (d : Set E → Finset V) (F : V → Set E)
    (A : V → Set (Set E)) (hA : ∀ v, MeasurableSet (A v))
    (hAu : ∀ v, IsUpperSet (A v))
    (hd : ∀ U, MeasurableSet[blockSigma X] {ω | d ω=U})
    (hF : ∀ v, F v ⊆ Y) (C : Set (Set E)) (hC : MeasurableSet[blockSigma X] C)
    (K η lam : ℝ) (hK : 0 ≤ K+1) (hη : 0 ≤ η) (hlam : 0 < lam)
    (hmean : ∀ σ∈C, ∀ v∈d σ, 1-η ≤ (law q).real (A v))
    (hs : ∀ σ∈C, (∑ v∈d σ, (law q).real (allOpen (F v))) ≤ K+1) :
    (law q).real (C∩{ω | ∃ v∈d ω, ω∈allOpen (F v) ∧
      (blockProbability q Y (A v) ω).toReal<1-lam}) ≤
        ((K+1)*η/lam)*(law q).real C := by
  let Bad := fun v => allOpen (F v)∩{σ | (blockProbability q Y (A v) σ).toReal<1-lam}
  have hmB (v : V) : MeasurableSet[blockSigma Y] (Bad v) :=
    ((blockSigma_mono (hF v)) _ (measurable_allOpen_block (F v))).inter
      (measurableSet_lt (measurable_blockProbability q Y (A v) (hA v)).ennreal_toReal
        measurable_const)
  have hb (σ : Set E) (hσ : σ∈C) (v : V) (hv : v∈d σ) : (law q).real (Bad v) ≤ (law q).real (allOpen (F v))*(η/lam) := by
    simpa only [mul_div_assoc] using good_trial_bound q Y (F v) (A v) (hA v) (hAu v)
      η lam hlam (hmean σ hσ v hv)
  have hh := selected_fresh_bound q X Y hXY d (fun U => ⋃ v∈U, Bad v) hd
    (fun U => MeasurableSet.biUnion U.countable_toSet (fun v _ => hmB v))
    C hC ((K+1)*(η/lam)) (mul_nonneg hK (div_nonneg hη hlam.le))
    (fun σ hσ => bad_trial_union_bound q (d σ) Bad (fun v => (law q).real (allOpen (F v)))
      K (η/lam) (div_nonneg hη hlam.le) (fun v hv => hb σ hσ v hv) (hs σ hσ))
  have he : selectedEvent d (fun U => ⋃ v∈U, Bad v)=
      {ω | ∃ v∈d ω, ω∈allOpen (F v) ∧
        (blockProbability q Y (A v) ω).toReal<1-lam} := by
    ext ω
    simp only [selectedEvent, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, Bad]
    aesop
  rw [he] at hh
  simpa only [mul_div_assoc] using hh
end CriticalPercolation.BernoulliProduct
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.FreshContactTransfer
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
namespace CriticalPercolation.BondGraph
open BernoulliProduct
variable {E V : Type*} [Countable E] [Countable V] (G : BondGraph V E)
theorem fresh_contact_transfer (q : E → unitInterval) (X Y : Set E)
    (hXY : Disjoint X Y) (d : Set E → Finset V) (F : V → Set E)
    (B : V → Set V) (L T Input : Set V) (o : V)
    (hd : ∀ U, MeasurableSet[blockSigma X] {ω | d ω=U})
    (hF : ∀ v, F v ⊆ Y)
    (hconnect : ∀ v∈L, ∀ b∈B v, (G.openGraph (F v)).Reachable v b)
    (C Small : Set (Set E)) (hC : MeasurableSet[blockSigma X] C)
    (hinput : G.hitEvent o Input ⊆ Small∪C)
    (hcontact : ∀ ω∈C, ∀ v∈d ω, v∈L ∧ (G.openGraph ω).Reachable o v)
    (K η lam : ℝ) (hK : 0 ≤ K+1) (hη : 0 ≤ η) (hlam : 0 < lam)
    (hmean : ∀ v∈L, 1-η ≤ (BernoulliProduct.law q).real (G.seedHitEvent (B v) T))
    (hdis : ∀ σ∈C, (d σ : Set V).Pairwise (fun v w => Disjoint (F v) (F w)))
    (hs : ∀ σ∈C, K ≤ ∑ v∈d σ, (BernoulliProduct.law q).real (allOpen (F v)))
    (hs' : ∀ σ∈C, (∑ v∈d σ, (BernoulliProduct.law q).real (allOpen (F v))) ≤ K+1) :
    (BernoulliProduct.law q).real (G.hitEvent o Input\G.hitEvent o T) ≤
      (BernoulliProduct.law q).real Small+Real.exp (-K)+(K+1)*η/lam+lam := by
  let No := C∩{ω | ∀ v∈d ω, ω∉allOpen (F v)}
  let Bad := C∩{ω | ∃ v∈d ω, ω∈allOpen (F v) ∧
    (blockProbability q Y (G.seedHitEvent (B v) T) ω).toReal<1-lam}
  let Glue := {ω : Set E | ω∈G.hitEvent o (G.goodRelay q Y L F B T lam ω) ∧
    ω∉G.hitEvent o T}
  have hcover : G.hitEvent o Input\G.hitEvent o T ⊆ ((Small∪No)∪Bad)∪Glue := by
    intro ω hω
    obtain hSmall|hCω := hinput hω.1
    · exact Or.inl (Or.inl (Or.inl hSmall))
    · by_cases hno : ∀ v∈d ω, ω∉allOpen (F v)
      · exact Or.inl (Or.inl (Or.inr ⟨hCω,hno⟩))
      · push Not at hno
        obtain ⟨v,hv,hopen⟩ := hno
        by_cases hbad : (blockProbability q Y (G.seedHitEvent (B v) T) ω).toReal<1-lam
        · exact Or.inl (Or.inr ⟨hCω,v,hv,hopen,hbad⟩)
        · exact Or.inr ⟨⟨v,(hcontact ω hCω v hv).2,
            (hcontact ω hCω v hv).1,hopen,le_of_not_gt hbad⟩,hω.2⟩
  have hno := selected_no_success_bound q X Y hXY d F hd hF C hC K hdis hs
  have hbad := selected_bad_trial_bound q X Y hXY d F (fun v => G.seedHitEvent (B v) T)
    (fun v => G.measurableSet_seedHitEvent (B v) T) (fun v => G.seedHitEvent_upper (B v) T)
    hd hF C hC K η lam hK hη hlam
    (fun σ hσ v hv => hmean v (hcontact σ hσ v hv).1) hs'
  have hglue := G.goodRelay_gluing q Y L F B T hF hconnect o lam hlam.le
  have hno' : (BernoulliProduct.law q).real No ≤ Real.exp (-K) :=
    hno.trans (mul_le_of_le_one_right (Real.exp_nonneg _) measureReal_le_one)
  have hbad' : (BernoulliProduct.law q).real Bad ≤ (K+1)*η/lam :=
    hbad.trans (mul_le_of_le_one_right (div_nonneg (mul_nonneg hK hη) hlam.le)
      measureReal_le_one)
  have hu := measureReal_union_le ((Small∪No)∪Bad) Glue (μ := BernoulliProduct.law q)
  have hu' := measureReal_union_le (Small∪No) Bad (μ := BernoulliProduct.law q)
  have hu'' := measureReal_union_le Small No (μ := BernoulliProduct.law q)
  have hmono := measureReal_mono (μ := BernoulliProduct.law q) hcover
  change (BernoulliProduct.law q).real Glue ≤ lam at hglue
  linarith
end CriticalPercolation.BondGraph
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.FreshCollar
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
namespace CriticalPercolation.BondGraph
open BernoulliProduct
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)
theorem fresh_collar_transfer_from_geometry (hlocal : G.LocallyFinite)
    (q : E → unitInterval) (π : V → ℤ) (o : V) (Input T : Set V)
    (J : Finset ℤ) (hJ : J.Nonempty) (ho : ∀ j∈J, j ≤ π o)
    (hInput : ∀ j∈J, ∀ v∈Input, π v<j)
    (hcross : ∀ j∈J, ∀ e v w, G.ends e=s(v,w) → j ≤ π v → π w<j → π v=j)
    (p : unitInterval) (hp : (p : ℝ)<1)
    (hq : ∀ j∈J, ∀ e v w, G.ends e=s(v,w) → π v=j → π w<j → (q e : ℝ) ≤ p)
    (D k M N : ℕ) (hD : ∀ j∈J, ∀ v, π v=j → (G.incidentEdges {v}).ncard ≤ D)
    (hM : 0 < M) (hk : M*N ≤ k)
    (C : V → V → Prop) (hrefl : ∀ v, C v v) (hsymm : ∀ {v w}, C v w → C w v)
    (hfinite : ∀ v, {w | C v w}.Finite) (hbound : ∀ v, {w | C v w}.ncard ≤ M)
    (F : ℤ → V → Set E) (B : ℤ → V → Set V)
    (hF : ∀ j∈J, ∀ v, F j v ⊆ (G.inducedEdges {w | j ≤ π w})ᶜ)
    (hconnect : ∀ j∈J, ∀ v, π v=j → ∀ b∈B j v, (G.openGraph (F j v)).Reachable v b)
    (hdis : ∀ j∈J, ∀ v w, ¬C v w → Disjoint (F j v) (F j w))
    (s₀ K η lam : ℝ) (hK : 0 ≤ K) (hη : 0 ≤ η) (hlam : 0 < lam)
    (hs : ∀ j∈J, ∀ v, π v=j → s₀ ≤ (BernoulliProduct.law q).real (allOpen (F j v)))
    (hN : K ≤ N*s₀)
    (hmean : ∀ j∈J, ∀ v, π v=j →
      1-η ≤ (BernoulliProduct.law q).real (G.seedHitEvent (B j v) T)) :
    (BernoulliProduct.law q).real (G.hitEvent o Input\G.hitEvent o T) ≤
      1/((J.card : ℝ)*(1-(p : ℝ))^(D*k))+Real.exp (-K)+(K+1)*η/lam+lam := by
  obtain ⟨j,hj,hfew⟩ := G.exists_few_contact_level hlocal q π o J hJ ho hcross p hp hq D k hD
  obtain ⟨d,hd,hsel⟩ := G.honest_contact_selection π j o k C hrefl hsymm M N hM hk
    hfinite hbound (fun v => (BernoulliProduct.law q).real (allOpen (F j v))) s₀ K hK
    (fun v hv => ⟨hs j hj v hv,measureReal_le_one⟩) hN
  have hh := G.fresh_contact_transfer q (G.inducedEdges {v | j ≤ π v})
    (G.inducedEdges {v | j ≤ π v})ᶜ disjoint_compl_right d (F j) (B j)
    {v | π v=j} T Input o hd (hF j hj) (hconnect j hj)
    (G.manyContacts π j o k) (G.fewContacts π j o k) (G.measurableSet_manyContacts π j o k)
    (by
      intro ω hω
      have hne := G.levelContacts_nonempty_of_hit π j o (ho j hj) (hcross j hj) ω
        (G.hitEvent_mono_target o (hInput j hj) hω)
      by_cases hf : ω∈G.fewContacts π j o k
      · exact Or.inl hf
      · exact Or.inr ⟨hne,hf⟩)
    (by
      intro ω hω v hv
      have hmem := (hsel ω hω).1 hv
      exact ⟨hmem.2,G.levelContacts_reachable π j o ω hmem⟩)
    K η lam (by linarith) hη hlam (hmean j hj)
    (by
      intro ω hω v hv w hw hvw
      exact hdis j hj v w ((hsel ω hω).2.1 hv hw hvw))
    (fun ω hω => (hsel ω hω).2.2.1) (fun ω hω => (hsel ω hω).2.2.2)
  linarith
end CriticalPercolation.BondGraph
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.SourceLift
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
namespace CriticalPercolation.BondGraph
open BernoulliProduct
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)
omit [Countable V] [Countable E] in
lemma withSource_edge_cases (A : Set V) (e : E⊕A) (v w : Option V)
    (he : (G.withSource A).ends e=s(v,w)) :
    (∃ b x y, e=Sum.inl b ∧ v=some x ∧ w=some y ∧ G.ends b=s(x,y)) ∨
    (∃ a : A, e=Sum.inr a ∧ ((v=none ∧ w=some a.val) ∨ (w=none ∧ v=some a.val))) := by
  cases e with
  | inl e =>
    obtain ⟨⟨x,y⟩,hxy⟩ := Sym2.mk_surjective (G.ends e)
    change s(x,y)=G.ends e at hxy
    have hh : s(some x,some y)=s(v,w) := by simpa [withSource,← hxy] using he
    rcases Sym2.eq_iff.mp hh with hh|hh
    · exact Or.inl ⟨e,x,y,rfl,hh.1.symm,hh.2.symm,hxy.symm⟩
    · exact Or.inl ⟨e,y,x,rfl,hh.2.symm,hh.1.symm,by simpa only [Sym2.eq_swap] using hxy.symm⟩
  | inr a =>
    right
    refine ⟨a,rfl,?_⟩
    have hh : s(none,some a.val)=s(v,w) := he
    rcases Sym2.eq_iff.mp hh with hh|hh
    · exact Or.inl ⟨hh.1.symm,hh.2.symm⟩
    · exact Or.inr ⟨hh.1.symm,hh.2.symm⟩
theorem withSource_transfer_from_geometry (hlocal : G.LocallyFinite)
    (A Input T : Set V) (hA : A.Finite) (q : (E⊕A) → unitInterval)
    (π : V → ℤ) (H : ℤ) (J : Finset ℤ) (hJ : J.Nonempty)
    (hH : ∀ j∈J, j<H) (hAlevel : ∀ a∈A, H ≤ π a)
    (hInput : ∀ j∈J, ∀ v∈Input, π v<j)
    (hcross : ∀ j∈J, ∀ e v w, G.ends e=s(v,w) → j ≤ π v → π w<j → π v=j)
    (p : unitInterval) (hp : (p : ℝ)<1)
    (hq : ∀ j∈J, ∀ e v w, G.ends e=s(v,w) → π v=j → π w<j → (q (Sum.inl e) : ℝ) ≤ p)
    (D k M N : ℕ) (hD : ∀ j∈J, ∀ v, π v=j → (G.incidentEdges {v}).ncard ≤ D)
    (hM : 0 < M) (hk : M*N ≤ k)
    (C : V → V → Prop) (hrefl : ∀ v, C v v) (hsymm : ∀ {v w}, C v w → C w v)
    (hfinite : ∀ v, {w | C v w}.Finite) (hbound : ∀ v, {w | C v w}.ncard ≤ M)
    (F : ℤ → V → Set E) (B : ℤ → V → Set V)
    (hF : ∀ j∈J, ∀ v, F j v ⊆ (G.inducedEdges {w | j ≤ π w})ᶜ)
    (hconnect : ∀ j∈J, ∀ v, π v=j → ∀ b∈B j v, (G.openGraph (F j v)).Reachable v b)
    (hdis : ∀ j∈J, ∀ v w, ¬C v w → Disjoint (F j v) (F j w))
    (s₀ K η lam : ℝ) (hK : 0 ≤ K) (hη : 0 ≤ η) (hlam : 0 < lam)
    (hs : ∀ j∈J, ∀ v, π v=j → s₀ ≤ (BernoulliProduct.law (fun e => q (Sum.inl e))).real (allOpen (F j v)))
    (hN : K ≤ N*s₀)
    (hmean : ∀ j∈J, ∀ v, π v=j →
      1-η ≤ (BernoulliProduct.law (fun e => q (Sum.inl e))).real (G.seedHitEvent (B j v) T)) :
    (BernoulliProduct.law q).real ((G.withSource A).hitEvent none (some '' Input)\
      (G.withSource A).hitEvent none (some '' T)) ≤
      1/((J.card : ℝ)*(1-(p : ℝ))^(D*k))+Real.exp (-K)+(K+1)*η/lam+lam := by
  let π' : Option V → ℤ := Option.elim' H π
  let C' : Option V → Option V → Prop := fun v w => match v,w with
    | none,none => True
    | some v,some w => C v w
    | _,_ => False
  let F' : ℤ → Option V → Set (E⊕A) := fun j => Option.elim' ∅ (fun v => Sum.inl '' F j v)
  let B' : ℤ → Option V → Set (Option V) := fun j => Option.elim' ∅ (fun v => some '' B j v)
  have hvA (j : ℤ) (hj : j∈J) (v : V) (hv : π v=j) : v∉A := by
    intro hva
    have := hAlevel v hva
    have := hH j hj
    omega
  have hcross' (j : ℤ) (hj : j∈J) (e : E⊕A) (v w : Option V)
      (he : (G.withSource A).ends e=s(v,w)) (hv : j ≤ π' v) (hw : π' w<j) : π' v=j := by
    rcases G.withSource_edge_cases A e v w he with ⟨b,x,y,rfl,rfl,rfl,hb⟩|⟨a,rfl,hh⟩
    · exact hcross j hj b x y hb hv hw
    · obtain hh|hh := hh
      · obtain ⟨rfl,rfl⟩ := hh
        have := hAlevel a a.property
        have := hH j hj
        change π a<j at hw
        omega
      · obtain ⟨rfl,rfl⟩ := hh
        change H<j at hw
        have := hH j hj
        omega
  have hs' (j : ℤ) (hj : j∈J) (v : V) (hv : π v=j) :
      s₀ ≤ (BernoulliProduct.law q).real (allOpen (Sum.inl '' F j v)) := by
    have hm : Measurable (fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω : Set (E⊕A) → Set E) :=
      measurable_pi_lambda _ (fun edge => measurable_set_mem (Sum.inl edge))
    have lawproj := BernoulliProduct.law_map_preimage q Sum.inl Sum.inl_injective
    have heq : allOpen (Sum.inl '' F j v)=(fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω) ⁻¹' allOpen (F j v) := by
      ext ω
      simp only [allOpen,mem_ofPred_eq,mem_preimage]
      exact Set.image_subset_iff
    rw [heq,measureReal_def,← Measure.map_apply hm ((blockSigma_le _) _ (measurable_allOpen_block (F j v))),lawproj]
    exact hs j hj v hv
  apply (G.withSource A).fresh_collar_transfer_from_geometry (G.withSource_local hlocal hA)
    q π' none (some '' Input) (some '' T) J hJ (fun j hj => (hH j hj).le)
    (by rintro j hj _ ⟨v,hv,rfl⟩; exact hInput j hj v hv) hcross' p hp
    (by
      intro j hj e v w he hv hw
      rcases G.withSource_edge_cases A e v w he with ⟨b,x,y,rfl,rfl,rfl,hb⟩|⟨a,rfl,hh⟩
      · exact hq j hj b x y hb hv hw
      · obtain hh|hh := hh
        · obtain ⟨rfl,rfl⟩ := hh
          change H=j at hv
          have := hH j hj
          omega
        · obtain ⟨rfl,rfl⟩ := hh
          change H<j at hw
          have := hH j hj
          omega)
    D k M N
    (by
      intro j hj v hv
      cases v with
      | none => have := hH j hj; change H=j at hv; omega
      | some v =>
        rw [G.withSource_incident A (hvA j hj v hv),Set.ncard_image_of_injective _ Sum.inl_injective]
        exact hD j hj v hv)
    hM hk C'
    (by intro v; cases v; trivial; exact hrefl _)
    (by intro v w h; cases v <;> cases w <;> simp_all only [C'])
    (by
      intro v
      cases v with
      | none =>
        have he : {w | C' none w}={none} := by ext w; cases w <;> simp [C']
        rw [he]
        exact Set.finite_singleton _
      | some v =>
        have he : {w | C' (some v) w}=some '' {w | C v w} := by ext w; cases w <;> simp [C']
        rw [he]
        exact (hfinite v).image _)
    (by
      intro v
      cases v with
      | none =>
        have he : {w | C' none w}={none} := by ext w; cases w <;> simp [C']
        rw [he,Set.ncard_singleton]
        omega
      | some v =>
        have he : {w | C' (some v) w}=some '' {w | C v w} := by ext w; cases w <;> simp [C']
        rw [he,Set.ncard_image_of_injective _ (Option.some_injective V)]
        exact hbound v)
    F' B'
    (by
      intro j hj v
      cases v with
      | none => exact Set.empty_subset _
      | some v =>
        rintro e ⟨b,hb,rfl⟩ he
        apply hF j hj v hb
        intro z hz
        exact he (some z) (by simpa [withSource] using hz))
    (by
      intro j hj v hv b hb
      cases v with
      | none => have := hH j hj; change H=j at hv; omega
      | some v =>
        obtain ⟨z,hz,rfl⟩ := hb
        exact G.withSource_trial_reachable A (F j v) (hconnect j hj v hv z hz))
    (by
      intro j hj v w h
      cases v <;> cases w
      · simp [F']
      · simp [F']
      · simp [F']
      · exact Set.disjoint_image_of_injective Sum.inl_injective (hdis j hj _ _ h))
    s₀ K η lam hK hη hlam
    (by
      intro j hj v hv
      cases v with
      | none => have := hH j hj; change H=j at hv; omega
      | some v => exact hs' j hj v hv)
    hN
    (by
      intro j hj v hv
      cases v with
      | none => have := hH j hj; change H=j at hv; omega
      | some v => exact (hmean j hj v hv).trans (G.withSource_seedHit A (B j v) T q))
end CriticalPercolation.BondGraph
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.SourceConnectivity
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)
lemma withSource_reachable_from_seed (A : Set V) (ω : Set (E⊕A))
    (hw : ∀ a : A, Sum.inr a∈ω) {v : V}
    (hv : ∃ a∈A, (G.openGraph (Sum.inl ⁻¹' ω)).Reachable a v) :
    ((G.withSource A).openGraph ω).Reachable none (some v) := by
  obtain ⟨a,ha,hav⟩ := hv
  have hh : ((G.withSource A).openGraph ω).Adj none (some a) :=
    ⟨⟨Sum.inr ⟨a,ha⟩,hw ⟨a,ha⟩,rfl⟩,by simp⟩
  exact hh.reachable.trans (G.withSource_original_reachable A ω hav)
lemma withSource_reachable_to_seed (A : Set V) (ω : Set (E⊕A)) {v : V}
    (hv : ((G.withSource A).openGraph ω).Reachable none (some v)) :
    ∃ a∈A, (G.openGraph (Sum.inl ⁻¹' ω)).Reachable a v := by
  have hi : ∀ w, ((G.withSource A).openGraph ω).Reachable none w →
      Option.elim' True (fun v => ∃ a∈A, (G.openGraph (Sum.inl ⁻¹' ω)).Reachable a v) w := by
    intro w hw
    rw [SimpleGraph.reachable_iff_reflTransGen] at hw
    induction hw with
    | refl => trivial
    | @tail u w hr huw ih =>
      obtain ⟨⟨b,hb,hend⟩,hne⟩ := huw
      cases w with
      | none => trivial
      | some w =>
        rcases G.withSource_edge_cases A b u (some w) hend with
          ⟨b,v,w',rfl,rfl,hw',hb'⟩|⟨a,rfl,hh⟩
        · have he : w'=w := Option.some.inj hw'.symm
          subst w'
          obtain ⟨a,ha,hav⟩ := ih
          refine ⟨a,ha,hav.trans ?_⟩
          exact (show (G.openGraph (Sum.inl ⁻¹' ω)).Adj v w from
            ⟨⟨b,hb,hb'⟩,fun h => hne (congrArg some h)⟩).reachable
        · rcases hh with ⟨rfl,hh⟩|⟨hh,_⟩
          · have he : w=a.val := Option.some.inj hh
            exact ⟨a.val,a.property,he.symm ▸ SimpleGraph.Reachable.refl _⟩
          · simp at hh
  exact hi (some v) hv
lemma source_hit_iff_seedHit (A T : Set V) (ω : Set (E⊕A))
    (hw : ∀ a : A, Sum.inr a∈ω) :
    ω∈(G.withSource A).hitEvent none (some '' T) ↔
      Sum.inl ⁻¹' ω∈G.seedHitEvent A T := by
  constructor
  · rintro ⟨w,hr,v,hv,rfl⟩
    obtain ⟨a,ha,hav⟩ := G.withSource_reachable_to_seed A ω hr
    exact Set.mem_iUnion₂.mpr ⟨a,ha,v,hav,hv⟩
  · intro h
    obtain ⟨a,ha,v,hav,hv⟩ := Set.mem_iUnion₂.mp h
    exact ⟨some v,G.withSource_reachable_from_seed A ω hw ⟨a,ha,hav⟩,v,hv,rfl⟩
lemma source_hit_probability [Countable V] [Countable E] (A T : Set V)
    (q : (E⊕A) → unitInterval) (hq : ∀ a : A, q (Sum.inr a)=1) :
    BernoulliProduct.law q ((G.withSource A).hitEvent none (some '' T))=
      BernoulliProduct.law (fun b => q (Sum.inl b)) (G.seedHitEvent A T) := by
  have ha (a : A) : ∀ᵐ ω ∂BernoulliProduct.law q, Sum.inr a∈ω := by
    rw [ae_iff]
    have he : {ω : Set (E⊕A) | ¬Sum.inr a∈ω}={ω | (Sum.inr a∈ω)=False} := by
      ext ω; simp
    rw [he,BernoulliProduct.law_coordinate,hq a]
    simp [BernoulliProduct.bitMeasure]
  have hall : ∀ᵐ ω ∂BernoulliProduct.law q, ∀ a : A, Sum.inr a∈ω := ae_all_iff.mpr ha
  have heq : BernoulliProduct.law q ((G.withSource A).hitEvent none (some '' T))=
      BernoulliProduct.law q ((fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω) ⁻¹' G.seedHitEvent A T) := by
    apply measure_congr
    filter_upwards [hall] with ω hω
    exact propext (G.source_hit_iff_seedHit A T ω hω)
  rw [heq]
  change BernoulliProduct.law q ((fun ω : Set (E⊕A) => fun b => Sum.inl b∈ω) ⁻¹' G.seedHitEvent A T)=_
  rw [← Measure.map_apply
    (measurable_pi_lambda _ (fun bond => measurable_set_mem (Sum.inl bond)))
    (G.measurableSet_seedHitEvent A T)]
  change (Measure.map (fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω) (BernoulliProduct.law q)) (G.seedHitEvent A T)=_
  rw [BernoulliProduct.law_map_preimage q Sum.inl Sum.inl_injective]
  rfl
end CriticalPercolation.BondGraph
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.CollarErrorBudget
section

namespace OAI
section
section
noncomputable section
open scoped BigOperators
namespace CriticalPercolation
lemma collar_error_budget (κ η shells closed : ℝ) (hκ : 0<κ) (hκ1 : κ≤1)
    (hη : η ≤ κ*(κ/4)/(4*(Real.log (4/κ)+1)))
    (hclosed : 0<closed) (hshells : 4/(κ*closed)<shells) :
    1/(shells*closed)+Real.exp (-Real.log (4/κ))+
      (Real.log (4/κ)+1)*η/(κ/4)+κ/4 ≤ κ := by
  have hratio : 1 ≤ 4/κ := (le_div_iff₀ hκ).mpr (by linarith)
  have hK : 0 ≤ Real.log (4/κ) := Real.log_nonneg hratio
  have hK1 : 0<Real.log (4/κ)+1 := by linarith
  have hlam : 0<κ/4 := by linarith
  have hden : 0<κ*closed := mul_pos hκ hclosed
  have hs : 0<shells := (div_pos (by norm_num) hden).trans hshells
  have hfirst : 1/(shells*closed) ≤ κ/4 := by
    apply (div_le_iff₀ (mul_pos hs hclosed)).mpr
    have hh := (div_lt_iff₀ hden).mp hshells
    nlinarith
  have hexp : Real.exp (-Real.log (4/κ))=κ/4 := by
    rw [Real.exp_neg,Real.exp_log (div_pos (by norm_num) hκ)]
    simp
  have hthird : (Real.log (4/κ)+1)*η/(κ/4) ≤ κ/4 := by
    apply (div_le_iff₀ hlam).mpr
    have hh := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<4) hK1)).mp hη
    nlinarith
  rw [hexp]
  linarith
lemma positive_trial_power (p : ℝ) (hp : 0<p) (m VM : ℕ) :
    0<(p/2)^(m+1+VM) := pow_pos (by linarith) _
lemma trial_ceiling_budget (K s : ℝ) (hs : 0<s) :
    K ≤ (⌈K/s⌉₊ : ℝ)*s := by
  have hh : K/s ≤ (⌈K/s⌉₊ : ℝ) := Nat.le_ceil _
  exact (div_le_iff₀ hs).mp hh
end CriticalPercolation
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Criticality.FiniteSeedTree
section

namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)
lemma finite_seed_tree_of_rank {S : Set V} (hS : S.Finite) (o : V)
    (r : V → ℕ)
    (hparent : ∀ v∈S, v≠o → ∃ w∈S, G.fullGraph.Adj w v ∧ r w<r v) :
    ∃ F : Set E, F.Finite ∧ F⊆G.inducedEdges S ∧ F.ncard ≤ S.ncard ∧
      ∀ v∈S, (G.openGraph F).Reachable o v := by
  let U := S\{o}
  have hU : U.Finite := hS.sdiff
  let := hU.fintype
  have hh : ∀ v : U, ∃ (w : V) (e : E), w∈S ∧ G.ends e=s(w,v.val) ∧
      w≠v.val ∧ r w<r v.val := by
    intro v
    obtain ⟨w,hw,⟨⟨e,_,he⟩,hne⟩,hr⟩ := hparent v.val v.property.1 v.property.2
    exact ⟨w,e,hw,he,hne,hr⟩
  choose w e hw hend hne hr using hh
  let F : Set E := Set.range e
  have hF : F.Finite := Set.finite_range e
  refine ⟨F,hF,?_,?_,?_⟩
  · rintro b ⟨v,rfl⟩ z hz
    rw [hend v] at hz
    rcases Sym2.mem_iff.mp hz with rfl|rfl
    · exact hw v
    · exact v.property.1
  · calc
      F.ncard ≤ (Set.univ : Set U).ncard := by
        simpa only [F,Set.image_univ] using (Set.ncard_image_le (f := e) (Set.finite_univ : (Set.univ : Set U).Finite))
      _ = U.ncard := by simp
      _ ≤ S.ncard := Set.ncard_le_ncard Set.sdiff_subset hS
  · intro v hv
    generalize hn : r v=n
    induction n using Nat.strong_induction_on generalizing v with
    | h n ih =>
      by_cases hvo : v=o
      · subst v; exact SimpleGraph.Reachable.refl _
      · let a : U := ⟨v,hv,hvo⟩
        have hprev := ih (r (w a)) (by simpa only [← hn] using hr a) (w a) (hw a) rfl
        apply hprev.trans
        exact (show (G.openGraph F).Adj (w a) v from
          ⟨⟨e a,⟨a,rfl⟩,hend a⟩,hne a⟩).reachable
def ballRank (o v : V) : ℕ :=
  if h : ∃ n, v∈G.vertexBall o n then Nat.find h else 0
lemma ballRank_mem {o v : V} (h : ∃ n, v∈G.vertexBall o n) :
    v∈G.vertexBall o (G.ballRank o v) := by
  simp only [ballRank,dif_pos h]
  exact Nat.find_spec h
lemma ballRank_le {o v : V} {n : ℕ} (h : v∈G.vertexBall o n) : G.ballRank o v ≤ n := by
  have he : ∃ k, v∈G.vertexBall o k := ⟨n,h⟩
  simp only [ballRank,dif_pos he]
  exact Nat.find_min' he h
lemma ballRank_eq_zero_iff {o v : V} (h : ∃ n, v∈G.vertexBall o n) :
    G.ballRank o v=0 ↔ v=o := by
  constructor
  · intro hz
    have hh := G.ballRank_mem h
    rw [hz] at hh
    exact hh
  · intro hvo
    subst v
    exact Nat.eq_zero_of_le_zero (G.ballRank_le (show o∈G.vertexBall o 0 from rfl))
lemma ballRank_predecessor {o v : V} (h : ∃ n, v∈G.vertexBall o n) (hne : v≠o) :
    ∃ w, G.fullGraph.Adj w v ∧ G.ballRank o w+1=G.ballRank o v ∧
      w∈G.vertexBall o (G.ballRank o w) := by
  have hn : 0 < G.ballRank o v := Nat.pos_of_ne_zero (fun hh => hne ((G.ballRank_eq_zero_iff h).mp hh))
  obtain ⟨n,heq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hv := G.ballRank_mem h
  rw [heq] at hv
  rcases hv with hv|hv
  · have hb := G.ballRank_le hv
    omega
  · obtain ⟨w,hw,hvw⟩ := Set.mem_iUnion₂.mp hv
    have h1 := G.ballRank_le hw
    have h2 := G.ballRank_le (G.vertexBall_step (G.ballRank_mem ⟨n,hw⟩) hvw)
    refine ⟨w,hvw,by omega,G.ballRank_mem ⟨n,hw⟩⟩
lemma finite_seed_tree (hlocal : G.LocallyFinite) (o : V) (m : ℕ) :
    ∃ F : Set E, F.Finite ∧ F⊆G.inducedEdges (G.vertexBall o m) ∧
      F.ncard ≤ (G.vertexBall o m).ncard ∧
      ∀ v∈G.vertexBall o m, (G.openGraph F).Reachable o v := by
  apply G.finite_seed_tree_of_rank (G.vertexBall_finite hlocal o m) o (G.ballRank o)
  intro v hv hne
  obtain ⟨w,hw,hr,hmem⟩ := G.ballRank_predecessor ⟨m,hv⟩ hne
  exact ⟨w,G.vertexBall_mono o (by have := G.ballRank_le hv; omega) hmem,hw,by omega⟩
end CriticalPercolation.BondGraph
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.InwardTrial
section

namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)
lemma inward_path (hc : G.fullGraph.Connected) {B : Set V} (hB : B.Nonempty)
    (v : V) (l : ℕ) (hl : l ≤ G.distanceTo B v) :
    ∃ (y : V) (P : Set E), P.Finite ∧ P.ncard ≤ l ∧
      G.distanceTo B y+l=G.distanceTo B v ∧ y∈G.vertexBall v l ∧
      P⊆G.inducedEdges (G.vertexBall v l∩{z | G.distanceTo B z ≤ G.distanceTo B v}) ∧
      P⊆(G.inducedEdges {z | G.distanceTo B v ≤ G.distanceTo B z})ᶜ ∧
      (G.openGraph P).Reachable v y := by
  induction l generalizing v with
  | zero =>
    exact ⟨v,∅,Set.finite_empty,by simp,by omega,rfl,Set.empty_subset _,Set.empty_subset _,
      SimpleGraph.Reachable.refl _⟩
  | succ l ih =>
    obtain ⟨w,hw,hr⟩ := G.distanceTo_predecessor hc hB v (by omega)
    obtain ⟨y,P,hP,hcard,hy,hyball,hends,hfresh,hreach⟩ := ih w (by omega)
    have hwball : w∈G.vertexBall v 1 := G.vertexBall_step (G.mem_vertexBall_self v 0) hw
    obtain ⟨⟨e,_,he⟩,hne⟩ := hw
    refine ⟨y,insert e P,hP.insert _,?_,by omega,?_,?_,?_,?_⟩
    · exact (Set.ncard_insert_le _ _).trans (by omega)
    · simpa only [Nat.add_comm 1] using G.vertexBall_add hwball l hyball
    · intro f hf z hz
      rcases hf with rfl|hf
      · rw [he] at hz
        have hz' : z=v ∨ z=w := Sym2.mem_iff.mp hz
        rcases hz' with hz'|hz'
        · subst z
          exact ⟨G.mem_vertexBall_self v (l+1),show G.distanceTo B v ≤ G.distanceTo B v from le_rfl⟩
        · subst z
          exact ⟨G.vertexBall_mono v (by omega) hwball,by change G.distanceTo B w ≤ G.distanceTo B v; omega⟩
      · have hh := hends hf z hz
        have hh2 : G.distanceTo B z ≤ G.distanceTo B w := hh.2
        refine ⟨?_,by change G.distanceTo B z ≤ G.distanceTo B v; omega⟩
        simpa only [Nat.add_comm 1] using G.vertexBall_add hwball l hh.1
    · intro f hf hf'
      rcases hf with rfl|hf
      · have hh := hf' w (by rw [he]; simp)
        change G.distanceTo B v ≤ G.distanceTo B w at hh
        omega
      · apply hfresh hf
        intro z hz
        have hh := hf' z hz
        change G.distanceTo B v ≤ G.distanceTo B z at hh
        change G.distanceTo B w ≤ G.distanceTo B z
        omega
    · apply (show (G.openGraph (insert e P)).Adj v w from
          ⟨⟨e,Set.mem_insert e P,he⟩,hne⟩).reachable.trans
      exact hreach.mono (G.openGraph_mono (Set.subset_insert e P))
lemma inward_seed_trial (hc : G.fullGraph.Connected) (hlocal : G.LocallyFinite)
    {B : Set V} (hB : B.Nonempty) (v : V) (m : ℕ) (hm : m<G.distanceTo B v) :
    ∃ (y : V) (F : Set E), F.Finite ∧
      F.ncard ≤ m+1+(G.vertexBall y m).ncard ∧
      G.distanceTo B y+(m+1)=G.distanceTo B v ∧
      F⊆G.inducedEdges (G.vertexBall v (2*m+1)∩{z | G.distanceTo B z ≤ G.distanceTo B v}) ∧
      F⊆(G.inducedEdges {z | G.distanceTo B v ≤ G.distanceTo B z})ᶜ ∧
      ∀ z∈G.vertexBall y m, (G.openGraph F).Reachable v z := by
  obtain ⟨y,P,hP,hcard,hy,hyball,hends,hfresh,hreach⟩ := G.inward_path hc hB v (m+1) (by omega)
  obtain ⟨Q,hQ,hQends,hQcard,hQreach⟩ := G.finite_seed_tree hlocal y m
  refine ⟨y,P∪Q,hP.union hQ,?_,hy,?_,?_,?_⟩
  · exact (Set.ncard_union_le P Q).trans (by omega)
  · intro e he z hz
    rcases he with he|he
    · have hh := hends he z hz
      exact ⟨G.vertexBall_mono v (by omega) hh.1,hh.2⟩
    · have hh := hQends he z hz
      have hle := G.distanceTo_ball hc hB hh
      refine ⟨?_,by change G.distanceTo B z ≤ G.distanceTo B v; omega⟩
      have := G.vertexBall_add hyball m hh
      simpa only [show m+1+m=2*m+1 by omega] using this
  · intro e he he'
    rcases he with he|he
    · exact hfresh he he'
    · obtain ⟨⟨x,z⟩,hxz⟩ := Sym2.mk_surjective (G.ends e)
      have hx : x∈G.ends e := by rw [← hxz]; simp
      have hh := G.distanceTo_ball hc hB (hQends he x hx)
      have hh' := he' x hx
      change G.distanceTo B v ≤ G.distanceTo B x at hh'
      omega
  · intro z hz
    exact (hreach.mono (G.openGraph_mono Set.subset_union_left)).trans
      ((hQreach z hz).mono (G.openGraph_mono Set.subset_union_right))
end CriticalPercolation.BondGraph
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.SourceCollarTransfer
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
namespace CriticalPercolation.BondGraph
open BernoulliProduct
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)
theorem source_distance_collar_transfer (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (A Input T : Set V) (hA : A.Finite) (q : (E⊕A) → unitInterval) (hInput : Input.Nonempty)
    (m R : ℕ) (J : Finset ℤ) (hJ : J.Nonempty)
    (hJrange : ∀ j∈J, (m : ℤ)<j ∧ j ≤ R)
    (houtside : ∀ a∈A, a∉G.vertexCollar Input R)
    (p₀ p : unitInterval) (hp : (p : ℝ)<1)
    (hq : ∀ e∈G.inducedEdges (G.vertexCollar Input R), (p₀ : ℝ) ≤ q (Sum.inl e) ∧ (q (Sum.inl e) : ℝ) ≤ p)
    (D k M N VM : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (hM : 0 < M) (hk : M*N ≤ k)
    (hMbound : ∀ v, (G.vertexBall v (4*m+2)).ncard ≤ M)
    (hVM : ∀ v, (G.vertexBall v m).ncard ≤ VM)
    (K η lam : ℝ) (hK : 0 ≤ K) (hη : 0 ≤ η) (hlam : 0 < lam)
    (hN : K ≤ N*(p₀ : ℝ)^(m+1+VM))
    (hmean : ∀ y∈G.vertexCollar Input R,
      1-η ≤ (BernoulliProduct.law (fun e => q (Sum.inl e))).real (G.seedHitEvent (G.vertexBall y m) T)) :
    (BernoulliProduct.law q).real ((G.withSource A).hitEvent none (some '' Input)\
      (G.withSource A).hitEvent none (some '' T)) ≤
      1/((J.card : ℝ)*(1-(p : ℝ))^(D*k))+Real.exp (-K)+(K+1)*η/lam+lam := by
  let π : V → ℤ := fun v => G.distanceTo Input v
  let Q : Set V := {v | m<G.distanceTo Input v}
  have ht : ∀ v : Q, ∃ (y : V) (F : Set E), F.Finite ∧
      F.ncard ≤ m+1+(G.vertexBall y m).ncard ∧
      G.distanceTo Input y+(m+1)=G.distanceTo Input v ∧
      F⊆G.inducedEdges (G.vertexBall v (2*m+1)∩{z | G.distanceTo Input z ≤ G.distanceTo Input v}) ∧
      F⊆(G.inducedEdges {z | G.distanceTo Input v ≤ G.distanceTo Input z})ᶜ ∧
      ∀ z∈G.vertexBall y m, (G.openGraph F).Reachable v z := by
    intro v
    exact G.inward_seed_trial hc hl hInput v m v.2
  choose y F hfin hcard hy hends hfresh hreach using ht
  let Ft (j : ℤ) (v : V) : Set E := if h : π v=j ∧ v∈Q then F ⟨v,h.2⟩ else ∅
  let Bt (j : ℤ) (v : V) : Set V := if h : π v=j ∧ v∈Q then G.vertexBall (y ⟨v,h.2⟩) m else ∅
  have hlevel (j : ℤ) (hj : j∈J) (v : V) (hv : π v=j) : π v=j ∧ v∈Q := by
    refine ⟨hv,?_⟩
    change m<G.distanceTo Input v
    have hh := (hJrange j hj).1
    change (G.distanceTo Input v : ℤ)=j at hv
    omega
  have hsupp (j : ℤ) (v : V) : Ft j v⊆G.inducedEdges (G.vertexBall v (2*m+1)) := by
    dsimp only [Ft]
    split_ifs with h
    · intro e he z hz
      exact (hends ⟨v,h.2⟩ he z hz).1
    · exact Set.empty_subset _
  have hcollar (j : ℤ) (hj : j∈J) (v : V) : Ft j v⊆G.inducedEdges (G.vertexCollar Input R) := by
    dsimp only [Ft]
    split_ifs with h
    · intro e he z hz
      apply (G.distanceTo_le_iff hc hInput z R).mp
      have h1 : G.distanceTo Input z ≤ G.distanceTo Input v := (hends ⟨v,h.2⟩ he z hz).2
      have h2 := (hJrange j hj).2
      have h3 : (G.distanceTo Input v : ℤ)=j := h.1
      omega
    · exact Set.empty_subset _
  apply G.withSource_transfer_from_geometry hl A Input T hA q π (R+1) J hJ
    (by intro j hj; have := (hJrange j hj).2; omega)
    (by
      intro a ha
      have hh : ¬G.distanceTo Input a ≤ R := by
        intro hh
        exact houtside a ha ((G.distanceTo_le_iff hc hInput a R).mp hh)
      change (R : ℤ)+1 ≤ (G.distanceTo Input a : ℤ)
      omega)
    (by
      intro j hj v hv
      have hv0 := (G.distanceTo_eq_zero_iff hc hInput v).mpr hv
      change (G.distanceTo Input v : ℤ)<j
      have := (hJrange j hj).1
      omega)
    (by
      intro j hj e v w he hv hw
      by_cases hvw : v=w
      · subst w; omega
      · have ha : G.fullGraph.Adj w v := ⟨⟨e,Set.mem_univ _,by simpa only [Sym2.eq_swap] using he⟩,Ne.symm hvw⟩
        have hs := G.distanceTo_adj hc hInput ha
        change j ≤ (G.distanceTo Input v : ℤ) at hv
        change (G.distanceTo Input w : ℤ)<j at hw
        change (G.distanceTo Input v : ℤ)=j
        omega)
    p hp
    (by
      intro j hj e v w he hv hw
      apply (hq e ?_).2
      intro z hz
      rw [he] at hz
      have hz' : z=v ∨ z=w := Sym2.mem_iff.mp hz
      apply (G.distanceTo_le_iff hc hInput z R).mp
      have hjR := (hJrange j hj).2
      change (G.distanceTo Input v : ℤ)=j at hv
      change (G.distanceTo Input w : ℤ)<j at hw
      rcases hz' with hz'|hz' <;> subst z <;> omega)
    D k M N (fun _j _hj v _hv => hD v) hM hk
    (fun v w => w∈G.vertexBall v (4*m+2))
    (fun v => G.mem_vertexBall_self v _) (fun {_ _} h => G.vertexBall_comm.mp h)
    (fun v => G.vertexBall_finite hl v _) hMbound Ft Bt
    (by
      intro j hj v
      dsimp only [Ft]
      split_ifs with h
      · intro e he he'
        apply hfresh ⟨v,h.2⟩ he
        intro z hz
        have hh := he' z hz
        change j ≤ (G.distanceTo Input z : ℤ) at hh
        have hv : (G.distanceTo Input v : ℤ)=j := h.1
        change G.distanceTo Input v ≤ G.distanceTo Input z
        omega
      · exact Set.empty_subset _)
    (by
      intro j hj v hv b hb
      have hh := hlevel j hj v hv
      dsimp only [Bt] at hb
      rw [dif_pos hh] at hb
      dsimp only [Ft]
      rw [dif_pos hh]
      exact hreach ⟨v,hh.2⟩ b hb)
    (by
      intro j hj v w h
      exact G.inward_trials_disjoint (Ft j) m (hsupp j) h)
    ((p₀ : ℝ)^(m+1+VM)) K η lam hK hη hlam
    (by
      intro j hj v hv
      have hh := hlevel j hj v hv
      have hFfinite : (Ft j v).Finite := by simpa only [Ft,dif_pos hh] using hfin ⟨v,hh.2⟩
      apply law_allOpen_lower (fun e => q (Sum.inl e)) (Ft j v) hFfinite p₀ (m+1+VM)
      · rw [show Ft j v=F ⟨v,hh.2⟩ by simp only [Ft,dif_pos hh]]
        exact (hcard ⟨v,hh.2⟩).trans (by have := hVM (y ⟨v,hh.2⟩); omega)
      · intro e he
        exact (hq e (hcollar j hj v he)).1)
    hN
    (by
      intro j hj v hv
      have hh := hlevel j hj v hv
      dsimp only [Bt]
      rw [dif_pos hh]
      apply hmean
      apply (G.distanceTo_le_iff hc hInput _ R).mp
      have h1 := hy ⟨v,hh.2⟩
      change G.distanceTo Input (y ⟨v,hh.2⟩)+(m+1)=G.distanceTo Input v at h1
      have h2 := (hJrange j hj).2
      change (G.distanceTo Input v : ℤ)=j at hv
      omega)
end CriticalPercolation.BondGraph
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.FreshCollarExact
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
namespace CriticalPercolation.BondGraph
open BernoulliProduct
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)
theorem fresh_collar_transfer (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (A Input T : Set V) (hA : A.Finite) (q : (E⊕A) → unitInterval)
    (m R : ℕ) (hcR : m<R) (Dstar : Set E)
    (houtside : ∀ a∈A, a∉G.vertexCollar Input R)
    (hregion : G.inducedEdges (G.vertexCollar Input R)⊆Dstar)
    (pc p' : unitInterval) (hpc₀ : 0<(pc : ℝ)) (hpc : (pc : ℝ)<1)
    (hpp : (pc : ℝ)/2 ≤ p') (hppc : (p' : ℝ) ≤ pc)
    (hq : ∀ e∈Dstar, q (Sum.inl e)=p')
    (D k M VM : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (hM : 0 < M) (hMbound : ∀ v, (G.vertexBall v (4*m+2)).ncard ≤ M)
    (hVM : ∀ v, (G.vertexBall v m).ncard ≤ VM)
    (κ η : ℝ) (hκ : 0<κ) (hκ1 : κ≤1) (hη₀ : 0≤η)
    (hη : η ≤ κ*(κ/4)/(4*(Real.log (4/κ)+1)))
    (hk : M*⌈Real.log (4/κ)/((pc : ℝ)/2)^(m+1+VM)⌉₊ ≤ k)
    (hR : 4/(κ*(1-(pc : ℝ))^(D*k))<(R : ℝ)-m)
    (hmean : ∀ y∈G.vertexCollar Input R,
      1-η ≤ (BernoulliProduct.law (fun _ : E => p')).real
        ((forceOn Dstarᶜ ∅) ⁻¹' G.seedHitEvent (G.vertexBall y m) T)) :
    (BernoulliProduct.law q).real ((G.withSource A).hitEvent none (some '' Input)\
      (G.withSource A).hitEvent none (some '' T)) ≤ κ := by
  by_cases hI : Input.Nonempty
  · let p₀ : unitInterval := ⟨(pc : ℝ)/2,by constructor <;> linarith [pc.2.1,pc.2.2]⟩
    let J : Finset ℤ := Finset.Icc ((m : ℤ)+1) (R : ℤ)
    have hJ : J.Nonempty := Finset.nonempty_Icc.mpr (by omega)
    have hJcard : (J.card : ℝ)=(R : ℝ)-m := by
      have hjc : J.card=R-m := by
        change (Finset.Icc ((m : ℤ)+1) (R : ℤ)).card=R-m
        rw [Int.card_Icc]
        omega
      rw [hjc,Nat.cast_sub hcR.le]
    have hK : 0 ≤ Real.log (4/κ) := Real.log_nonneg ((le_div_iff₀ hκ).mpr (by linarith))
    have hs : 0<((pc : ℝ)/2)^(m+1+VM) := positive_trial_power _ hpc₀ _ _
    have hh := G.source_distance_collar_transfer hc hl A Input T hA q hI m R J hJ
      (by intro j hj; have hh := Finset.mem_Icc.mp hj; omega) houtside p₀ pc hpc
      (by
        intro e he
        rw [hq e (hregion he)]
        exact ⟨hpp,hppc⟩)
      D k M ⌈Real.log (4/κ)/((pc : ℝ)/2)^(m+1+VM)⌉₊ VM hD hM hk hMbound hVM
      (Real.log (4/κ)) η (κ/4) hK hη₀ (by linarith)
      (trial_ceiling_budget _ _ hs)
      (by
        intro y hy
        exact (hmean y hy).trans (fresh_region_lower (fun e => q (Sum.inl e))
          (fun _ => p') Dstar hq _ (G.measurableSet_seedHitEvent _ _)
          (G.seedHitEvent_upper _ _)))
    rw [hJcard] at hh
    exact hh.trans (collar_error_budget κ η ((R : ℝ)-m) _ hκ hκ1 hη
      (pow_pos (by linarith) _) hR)
  · have he : Input=∅ := Set.not_nonempty_iff_eq_empty.mp hI
    subst Input
    have he : (G.withSource A).hitEvent none (some '' (∅ : Set V))=∅ := by
      ext ω
      simp [hitEvent]
    rw [he,Set.empty_sdiff,measureReal_empty]
    exact hκ.le
end CriticalPercolation.BondGraph
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.SourceRelaySeparation
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)
lemma source_outside_relay_collar (t z : V → ℝ) (σ e ρ P : ℝ) (L R m i : ℕ)
    (he : 0<e) (hρ : 0 ≤ ρ) (hi : i ≤ L) (hPi : 1 ≤ P+i)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    {a : V} (ha : t a ≤ m*ρ-P) :
    a∉G.vertexCollar (corridorRelay t z σ e ρ L i) R := by
  intro hin
  obtain ⟨hρe,_,_,_,hlast⟩ := relay_coordinate_scale L R m e ρ he hρ heL hr
  have hs := G.vertexCollar_mono (corridorRelay_subset t z σ e ρ hρe L i hi) R hin
  have hb := (G.relay_collar_bounds t z σ e ρ hρ ht hz R i hs).1
  have hi' : (i:ℝ) ≤ L := by exact_mod_cast hi
  have hile : (i+1)*e ≤ (L+1)*e := mul_le_mul_of_nonneg_right (by linarith) he.le
  have hb' := (abs_le.mp hb).1
  nlinarith
end CriticalPercolation.BondGraph
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.RootCorridor
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)
theorem root_corridor_miss (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o : V) (t z : V → ℝ) (σ e ρ J : ℝ) (L R m : ℕ)
    (q : (E⊕G.vertexBall o m) → unitInterval)
    (hwire : ∀ a : G.vertexBall o m, q (Sum.inr a)=1)
    (hσ : |σ|=1) (he : 0<e) (hρ : 0 ≤ ρ) (hJ : 26200<J) (hL : 416 ≤ L)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10) (hto : t o=0) (hzo : z o=0)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    (hcR : m<R) (pc p' : unitInterval) (hpc₀ : 0<(pc : ℝ)) (hpc : (pc : ℝ)<1)
    (hpp : (pc : ℝ)/2 ≤ p') (hppc : (p' : ℝ) ≤ pc)
    (hq : ∀ b∈G.inducedEdges (relayDomain t z J (L+1/2) σ), q (Sum.inl b)=p')
    (D k M VM : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (hM : 0<M) (hMbound : ∀ v, (G.vertexBall v (4*m+2)).ncard ≤ M)
    (hVM : ∀ v, (G.vertexBall v m).ncard ≤ VM)
    (κ η : ℝ) (hκ : 0<κ) (hκ1 : κ ≤ 1) (hη₀ : 0 ≤ η)
    (hη : η ≤ κ*(κ/4)/(4*(Real.log (4/κ)+1)))
    (hk : M*⌈Real.log (4/κ)/((pc : ℝ)/2)^(m+1+VM)⌉₊ ≤ k)
    (hR : 4/(κ*(1-(pc : ℝ))^(D*k))<(R : ℝ)-m)
    (hmove : ∀ y s, |s|=1 → 1-η ≤ (BernoulliProduct.law (fun _ : E => p')).real
      (G.coordinateMove t z m e y s)) :
    (BernoulliProduct.law q).real
      ((G.withSource (G.vertexBall o m)).hitEvent none
        (some '' relayMark t z (L+1/2) σ ρ))ᶜ ≤ η+L*κ := by
  let A := G.vertexBall o m
  let H : ℕ → Set (Set (E⊕A)) := fun i =>
    (G.withSource A).hitEvent none (some '' corridorRelay t z σ e ρ L (i+1))
  have h0 := G.coordinate_moves_relay_estimates t z σ e ρ J L R m
    hσ he hρ hJ hL heL hr ht hz p' η hmove 0 (Nat.zero_le L)
  have ho : o∈G.vertexCollar (corridorRelay t z σ e ρ L 0) R := by
    apply Set.mem_iUnion₂.mpr
    refine ⟨o,?_,G.mem_vertexBall_self o R⟩
    simp only [corridorRelay]
    exact ⟨by simp [hto],by simp [hto,hρ],by simp [hzo]⟩
  have hh0 : 1-η ≤ (BernoulliProduct.law q).real (H 0) := by
    rw [measureReal_def,G.source_hit_probability A _ q hwire]
    exact (h0.2 o ho).trans (BernoulliProduct.fresh_region_lower (fun b => q (Sum.inl b))
      (fun _ => p') (G.inducedEdges (relayDomain t z J (L+1/2) σ)) hq _
      (G.measurableSet_seedHitEvent _ _) (G.seedHitEvent_upper _ _))
  have hfirst : (BernoulliProduct.law q).real (H 0)ᶜ ≤ η := by
    rw [probReal_compl_eq_one_sub ((G.withSource A).measurableSet_hitEvent _ _)]
    linarith
  have hh := relay_miss_bound (BernoulliProduct.law q) H κ η L hfirst (by
    intro i hi
    have hiL : i+1 ≤ L := by omega
    obtain ⟨hcoll,hmean⟩ := G.coordinate_moves_relay_estimates t z σ e ρ J L R m
      hσ he hρ hJ hL heL hr ht hz p' η hmove (i+1) hiL
    apply G.fresh_collar_transfer hc hl A _ _ (G.vertexBall_finite hl o m) q m R hcR
      (G.inducedEdges (relayDomain t z J (L+1/2) σ))
      (fun a ha => G.source_outside_relay_collar t z σ e ρ 0 L R m (i+1) he hρ hiL
        (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) i]) heL hr ht hz ?_)
      (G.inducedEdges_mono hcoll) pc p' hpc₀ hpc hpp hppc hq D k M VM hD hM hMbound hVM
      κ η hκ hκ1 hη₀ hη hk hR hmean
    have hb := (abs_le.mp (G.coordinate_ball_bound t ρ hρ ht ha)).2
    simpa [hto] using hb)
  simpa only [H,corridorRelay,Nat.add_one_ne_zero,ite_false,
    if_neg (by omega : ¬L+1 ≤ L)] using hh
end CriticalPercolation.BondGraph
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.ProductMeasure.SourceMissLaw
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.BondGraph
open BernoulliProduct
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)
lemma source_miss_real (A T : Set V) (q : (E⊕A) → unitInterval)
    (hq : ∀ a : A, q (Sum.inr a)=1) :
    (BernoulliProduct.law q).real ((G.withSource A).hitEvent none (some '' T))ᶜ=
      (BernoulliProduct.law (fun b => q (Sum.inl b))).real (G.seedHitEvent A T)ᶜ := by
  rw [probReal_compl_eq_one_sub ((G.withSource A).measurableSet_hitEvent _ _),
    probReal_compl_eq_one_sub (G.measurableSet_seedHitEvent A T),
    measureReal_def,measureReal_def,G.source_hit_probability A T q hq]
lemma restricted_seed_probability (A T : Set V) (q : E → unitInterval) (R : Set E) :
    BernoulliProduct.law q (G.restrictedSeed A T R)=
      BernoulliProduct.law (pinnedParameters q Rᶜ ∅) (G.seedHitEvent A T) := by
  rw [← forceOn_map_law,Measure.map_apply (measurable_forceOn _ _) (G.measurableSet_seedHitEvent A T)]
  congr 1
  ext ω
  have he : forceOn Rᶜ ∅ ω=ω∩R := by
    ext e
    by_cases he : e∈R <;> simp [he]
  simp only [Set.mem_preimage,restrictedSeed,Set.mem_ofPred_eq,he]
lemma restricted_seed_miss_real (A T : Set V) (q : E → unitInterval) (R : Set E) :
    (BernoulliProduct.law q).real (G.restrictedSeed A T R)ᶜ=
      (BernoulliProduct.law (Sum.elim (pinnedParameters q Rᶜ ∅) (fun _ : A => 1))).real
        ((G.withSource A).hitEvent none (some '' T))ᶜ := by
  rw [G.source_miss_real _ _ _ (fun _ => rfl),
    probReal_compl_eq_one_sub (G.restrictedSeed_measurable A T R),
    probReal_compl_eq_one_sub (G.measurableSet_seedHitEvent A T),
    measureReal_def,measureReal_def,G.restricted_seed_probability]
  rfl
theorem original_root_corridor_miss (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o : V) (t z : V → ℝ) (σ e ρ J : ℝ) (L R m : ℕ) (U : Set E)
    (hDU : G.inducedEdges (relayDomain t z J (L+1/2) σ)⊆U)
    (hσ : |σ|=1) (he : 0<e) (hρ : 0 ≤ ρ) (hJ : 26200<J) (hL : 416 ≤ L)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10) (hto : t o=0) (hzo : z o=0)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    (hcR : m<R) (pc p' : unitInterval) (hpc₀ : 0<(pc : ℝ)) (hpc : (pc : ℝ)<1)
    (hpp : (pc : ℝ)/2 ≤ p') (hppc : (p' : ℝ) ≤ pc)
    (D k M VM : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (hM : 0<M) (hMbound : ∀ v, (G.vertexBall v (4*m+2)).ncard ≤ M)
    (hVM : ∀ v, (G.vertexBall v m).ncard ≤ VM)
    (κ η : ℝ) (hκ : 0<κ) (hκ1 : κ ≤ 1) (hη₀ : 0 ≤ η)
    (hη : η ≤ κ*(κ/4)/(4*(Real.log (4/κ)+1)))
    (hk : M*⌈Real.log (4/κ)/((pc : ℝ)/2)^(m+1+VM)⌉₊ ≤ k)
    (hR : 4/(κ*(1-(pc : ℝ))^(D*k))<(R : ℝ)-m)
    (hmove : ∀ y s, |s|=1 → 1-η ≤ (BernoulliProduct.law (fun _ : E => p')).real
      (G.coordinateMove t z m e y s)) :
    (BernoulliProduct.law (fun _ : E => p')).real
      (G.restrictedSeed (G.vertexBall o m) (relayMark t z (L+1/2) σ ρ) U)ᶜ ≤ η+L*κ := by
  rw [G.restricted_seed_miss_real]
  apply G.root_corridor_miss hc hl o t z σ e ρ J L R m _ (fun _ => rfl)
    hσ he hρ hJ hL heL hr hto hzo ht hz hcR pc p' hpc₀ hpc hpp hppc _
    D k M VM hD hM hMbound hVM κ η hκ hκ1 hη₀ hη hk hR hmove
  intro b hb
  simp only [Sum.elim_inl,pinnedParameters,Set.mem_compl_iff,if_neg (not_not_intro (hDU hb))]
end CriticalPercolation.BondGraph
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.ProductMeasure.SourceEventLaw
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.BondGraph
open BernoulliProduct
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)
omit [Countable E] in
lemma source_hit_ae_seed (A T : Set V) (q : (E⊕A) → unitInterval)
    (hq : ∀ a : A, q (Sum.inr a)=1) :
    (G.withSource A).hitEvent none (some '' T) =ᵐ[BernoulliProduct.law q]
      ((fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω) ⁻¹' G.seedHitEvent A T) := by
  have ha (a : A) : ∀ᵐ ω ∂BernoulliProduct.law q, Sum.inr a∈ω := by
    rw [ae_iff]
    have he : {ω : Set (E⊕A) | ¬Sum.inr a∈ω}={ω | (Sum.inr a∈ω)=False} := by
      ext ω; simp
    rw [he,law_coordinate,hq a]
    simp [bitMeasure]
  filter_upwards [ae_all_iff.mpr ha] with ω hω
  exact propext (G.source_hit_iff_seedHit A T ω hω)
lemma source_hit_diff_probability (A B T : Set V) (q : (E⊕A) → unitInterval)
    (hq : ∀ a : A, q (Sum.inr a)=1) :
    BernoulliProduct.law q ((G.withSource A).hitEvent none (some '' B)\
      (G.withSource A).hitEvent none (some '' T))=
      BernoulliProduct.law (fun b => q (Sum.inl b)) (G.seedHitEvent A B\G.seedHitEvent A T) := by
  have heq : BernoulliProduct.law q ((G.withSource A).hitEvent none (some '' B)\
      (G.withSource A).hitEvent none (some '' T))=
      BernoulliProduct.law q ((fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω) ⁻¹'
        (G.seedHitEvent A B\G.seedHitEvent A T)) := by
    apply measure_congr
    filter_upwards [G.source_hit_ae_seed A B q hq,G.source_hit_ae_seed A T q hq] with ω hB hT
    exact propext (and_congr (eq_iff_iff.mp hB) (not_congr (eq_iff_iff.mp hT)))
  rw [heq]
  change BernoulliProduct.law q ((fun ω : Set (E⊕A) => fun b => Sum.inl b∈ω) ⁻¹' _)=_
  rw [← Measure.map_apply (measurable_pi_lambda _ (fun bond => measurable_set_mem (Sum.inl bond)))
    ((G.measurableSet_seedHitEvent A B).diff (G.measurableSet_seedHitEvent A T))]
  change (Measure.map (fun ω : Set (E⊕A) => Sum.inl ⁻¹' ω) (BernoulliProduct.law q)) _=_
  rw [law_map_preimage q Sum.inl Sum.inl_injective]
  rfl
lemma restricted_seed_diff_probability (A B T : Set V) (q : E → unitInterval) (R : Set E) :
    BernoulliProduct.law q (G.restrictedSeed A B R\G.restrictedSeed A T R)=
      BernoulliProduct.law (pinnedParameters q Rᶜ ∅) (G.seedHitEvent A B\G.seedHitEvent A T) := by
  rw [← forceOn_map_law,Measure.map_apply (measurable_forceOn _ _)
    ((G.measurableSet_seedHitEvent A B).diff (G.measurableSet_seedHitEvent A T))]
  congr 1
  have he (ω : Set E) : forceOn Rᶜ ∅ ω=ω∩R := by
    ext e
    by_cases he : e∈R <;> simp [he]
  ext ω
  simp only [Set.mem_sdiff,Set.mem_preimage,restrictedSeed,Set.mem_ofPred_eq,he]
lemma restricted_seed_diff_le_source (A B T : Set V) (q : E → unitInterval)
    (I F R σ : Set E) (hFR : F⊆R) :
    (blockProbability q I (G.restrictedSeed A B F\G.restrictedSeed A T R) σ).toReal ≤
      (BernoulliProduct.law (Sum.elim (pinnedParameters (pinnedParameters q I σ) Rᶜ ∅)
        (fun _ : A => 1))).real
        ((G.withSource A).hitEvent none (some '' B)\(G.withSource A).hitEvent none (some '' T)) := by
  rw [blockProbability_eq_pinnedLaw q I σ _
    ((G.restrictedSeed_measurable _ _ _).diff (G.restrictedSeed_measurable _ _ _))]
  rw [measureReal_def,G.source_hit_diff_probability A B T _ (fun _ => rfl)]
  change (BernoulliProduct.law (pinnedParameters q I σ)).real _ ≤
    (BernoulliProduct.law (pinnedParameters (pinnedParameters q I σ) Rᶜ ∅)).real _
  rw [measureReal_def,measureReal_def,← G.restricted_seed_diff_probability]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  exact Set.sdiff_subset_sdiff_left (G.restrictedSeed_mono A B hFR)
end CriticalPercolation.BondGraph
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.FreshCorridor
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)
theorem coordinate_corridor_failure (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (A : Set V) (hA : A.Finite) (q : (E⊕A) → unitInterval)
    (t z : V → ℝ) (σ e ρ J P : ℝ) (L R m : ℕ)
    (hσ : |σ|=1) (he : 0<e) (hρ : 0 ≤ ρ) (hJ : 26200<J) (hL : 416 ≤ L)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10)
    (hP : 1 ≤ P) (hsource : ∀ a∈A, t a ≤ m*ρ-P)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    (hcR : m<R) (pc p' : unitInterval) (hpc₀ : 0<(pc : ℝ)) (hpc : (pc : ℝ)<1)
    (hpp : (pc : ℝ)/2 ≤ p') (hppc : (p' : ℝ) ≤ pc)
    (hq : ∀ b∈G.inducedEdges (relayDomain t z J (L+1/2) σ), q (Sum.inl b)=p')
    (D k M VM : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (hM : 0<M) (hMbound : ∀ v, (G.vertexBall v (4*m+2)).ncard ≤ M)
    (hVM : ∀ v, (G.vertexBall v m).ncard ≤ VM)
    (κ η : ℝ) (hκ : 0<κ) (hκ1 : κ ≤ 1) (hη₀ : 0 ≤ η)
    (hη : η ≤ κ*(κ/4)/(4*(Real.log (4/κ)+1)))
    (hk : M*⌈Real.log (4/κ)/((pc : ℝ)/2)^(m+1+VM)⌉₊ ≤ k)
    (hR : 4/(κ*(1-(pc : ℝ))^(D*k))<(R : ℝ)-m)
    (hmove : ∀ y s, |s|=1 → 1-η ≤ (BernoulliProduct.law (fun _ : E => p')).real
      (G.coordinateMove t z m e y s)) :
    (BernoulliProduct.law q).real
      ((G.withSource A).hitEvent none (some '' relayMark t z 0 σ ρ)\
        (G.withSource A).hitEvent none (some '' relayMark t z (L+1/2) σ ρ)) ≤ (L+1)*κ := by
  let H : ℕ → Set (Set (E⊕A)) := fun i =>
    (G.withSource A).hitEvent none (some '' corridorRelay t z σ e ρ L i)
  have hh := relay_failure_bound (BernoulliProduct.law q) H κ (L+1) (by
    intro i hi
    have hiL : i ≤ L := by omega
    obtain ⟨hcoll,hmean⟩ := G.coordinate_moves_relay_estimates t z σ e ρ J L R m
      hσ he hρ hJ hL heL hr ht hz p' η hmove i hiL
    apply G.fresh_collar_transfer hc hl A _ _ hA q m R hcR
      (G.inducedEdges (relayDomain t z J (L+1/2) σ))
      (fun a ha => G.source_outside_relay_collar t z σ e ρ P L R m i he hρ hiL
        (by linarith [Nat.cast_nonneg (α := ℝ) i]) heL hr ht hz (hsource a ha))
      (G.inducedEdges_mono hcoll) pc p' hpc₀ hpc hpp hppc hq D k M VM hD hM hMbound hVM
      κ η hκ hκ1 hη₀ hη hk hR hmean)
  simpa [H,corridorRelay,show ¬L+1 ≤ L by omega] using hh
end CriticalPercolation.BondGraph
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.ProspectiveCorridor
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.BondGraph
open BernoulliProduct
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)
theorem coordinate_pinned_corridor_failure (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (A : Set V) (hA : A.Finite) (q : E → unitInterval)
    (I F U ω : Set E) (hFU : F⊆U)
    (t z : V → ℝ) (σ e ρ J P : ℝ) (L R m : ℕ)
    (hσ : |σ|=1) (he : 0<e) (hρ : 0 ≤ ρ) (hJ : 26200<J) (hL : 416 ≤ L)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10)
    (hP : 1 ≤ P) (hsource : ∀ a∈A, t a ≤ m*ρ-P)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    (hcR : m<R) (pc p' : unitInterval) (hpc₀ : 0<(pc : ℝ)) (hpc : (pc : ℝ)<1)
    (hpp : (pc : ℝ)/2 ≤ p') (hppc : (p' : ℝ) ≤ pc)
    (hq : ∀ b∈G.inducedEdges (relayDomain t z J (L+1/2) σ), q b=p')
    (hDU : G.inducedEdges (relayDomain t z J (L+1/2) σ)⊆U)
    (hfresh : Disjoint I (G.inducedEdges (relayDomain t z J (L+1/2) σ)))
    (D k M VM : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (hM : 0<M) (hMbound : ∀ v, (G.vertexBall v (4*m+2)).ncard ≤ M)
    (hVM : ∀ v, (G.vertexBall v m).ncard ≤ VM)
    (κ η : ℝ) (hκ : 0<κ) (hκ1 : κ ≤ 1) (hη₀ : 0 ≤ η)
    (hη : η ≤ κ*(κ/4)/(4*(Real.log (4/κ)+1)))
    (hk : M*⌈Real.log (4/κ)/((pc : ℝ)/2)^(m+1+VM)⌉₊ ≤ k)
    (hR : 4/(κ*(1-(pc : ℝ))^(D*k))<(R : ℝ)-m)
    (hmove : ∀ y s, |s|=1 → 1-η ≤ (BernoulliProduct.law (fun _ : E => p')).real
      (G.coordinateMove t z m e y s)) :
    (BernoulliProduct.blockProbability q I
      (G.restrictedSeed A (relayMark t z 0 σ ρ) F\
        G.restrictedSeed A (relayMark t z (L+1/2) σ ρ) U) ω).toReal ≤ (L+1)*κ := by
  let r : E → unitInterval := pinnedParameters (pinnedParameters q I ω) Uᶜ ∅
  let q' : (E⊕A) → unitInterval := Sum.elim r (fun _ => 1)
  have hq' : ∀ b∈G.inducedEdges (relayDomain t z J (L+1/2) σ), q' (Sum.inl b)=p' := by
    intro b hb
    have hbU := hDU hb
    have hbI : b∉I := fun hi => Set.disjoint_left.mp hfresh hi hb
    simpa [q',r,pinnedParameters,hbU,hbI] using hq b hb
  exact (G.restricted_seed_diff_le_source A _ _ q I F U ω hFU).trans
    (G.coordinate_corridor_failure hc hl A hA q' t z σ e ρ J P L R m
      hσ he hρ hJ hL heL hr hP hsource ht hz hcR pc p' hpc₀ hpc hpp hppc hq'
      D k M VM hD hM hMbound hVM κ η hκ hκ1 hη₀ hη hk hR hmove)
end CriticalPercolation.BondGraph
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.CoordinateProspective
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.Corridor.CoordinateData
open BondGraph Boundary BernoulliProduct
variable {V E : Type*} [Countable V] [Countable E] (C : CoordinateData V E)
lemma active_slot_positive (n : ℕ) (S : GrowthState) (hv : S.Valid n)
    (ha : (incoming n S.good).isSome) : 0<n := by
  obtain ⟨e,he⟩ := Option.isSome_iff_exists.mp ha
  have ht := parent_slot_lt e (hv.2.1 _ (incoming_source he)).1
  rw [incoming_target he,gridSlot_slotSite] at ht
  omega
theorem prospective_estimate (h : C.Bounds)
    (hmove : ∀ y s, |s|=1 → 1-C.eta≤(BernoulliProduct.law (fun _ : E => C.p)).real
      (C.graph.coordinateMove C.time C.height C.m C.e y s))
    (n : ℕ) (S : GrowthState) (hv : S.Valid n) (_hc : S.Covered)
    (ha : (incoming n S.good).isSome) (ω : Set E) (b : Bool) :
    (blockProbability C.scheme.parameter (C.scheme.block S)
      (C.scheme.incomingHit n S\C.scheme.nextHit n S b) ω).toReal≤(C.L+1)*C.kappa := by
  let v := slotSite n
  let F := C.scheme.enlarged n S
  let U := F∪C.scheme.edgeDomain (v,b)
  have hdom := C.domain_eq v b
  have hDU : C.graph.inducedEdges (relayDomain (localTime C.time C.T v)
      (localHeight C.height C.T v) C.J C.T (sign b))⊆U := by
    rw [← hdom]
    exact Set.subset_union_right
  have hfresh : Disjoint (C.scheme.block S)
      (C.graph.inducedEdges (relayDomain (localTime C.time C.T v)
        (localHeight C.height C.T v) C.J C.T (sign b))) := by
    rw [← hdom]
    exact outgoing_unrevealed C.graph (normalized C.time C.height C.T) (C.J/C.T) (2520/C.T)
      (C.layout h).1 (C.layout h).2.1 (C.layout h).2.2 n S hv (active_slot_positive n S hv ha) rfl
  have hmoves : ∀ y s, |s|=1 → 1-C.eta≤(BernoulliProduct.law (fun _ : E => C.p)).real
      (C.graph.coordinateMove (localTime C.time C.T v) (localHeight C.height C.T v)
        C.m C.e y s) := by
    intro y s hs
    rw [coordinateMove_translate]
    exact hmove y s hs
  have hP : 1≤C.T := by
    have hh : (416 : ℝ)≤C.L := by exact_mod_cast C.L_large h
    dsimp [T]; linarith
  have hh := C.graph.coordinate_pinned_corridor_failure h.connected h.locallyFinite
    C.scheme.seed (C.graph.vertexBall_finite h.locallyFinite C.origin C.m) C.scheme.parameter
    (C.scheme.block S) F U ω Set.subset_union_left
    (localTime C.time C.T v) (localHeight C.height C.T v) (sign b) C.e C.rho C.J C.T
    C.L C.R C.m (sign_abs b) h.e_pos h.rho_nonneg h.J_lower (C.L_large h) h.e_small h.rho_small
    hP (C.source_behind h n (active_slot_positive n S hv ha))
    (fun {_ _} hh => C.local_time_step h v hh) (fun {_ _} hh => C.local_height_step h v hh) h.R_gt C.pc C.p h.pc_pos h.pc_lt
    h.p_lower h.p_upper (fun _ _ => rfl) hDU hfresh C.D C.k C.M C.VM h.degree h.M_pos
    h.M_bound h.VM_bound C.kappa C.eta h.kappa_pos h.kappa_le h.eta_nonneg h.eta_small
    h.k_large h.R_large hmoves
  change (blockProbability C.scheme.parameter (C.scheme.block S)
    (C.graph.restrictedSeed C.scheme.seed (relayMark (localTime C.time C.T v) (localHeight C.height C.T v) 0 (sign b) C.rho) F\
      C.graph.restrictedSeed C.scheme.seed (relayMark (localTime C.time C.T v) (localHeight C.height C.T v) C.T (sign b) C.rho) U) ω).toReal≤_ at hh
  rw [mark_initial,mark_target] at hh
  exact hh
lemma root_corridor_estimate (h : C.Bounds)
    (hmove : ∀ y s, |s|=1 → 1-C.eta≤(BernoulliProduct.law (fun _ : E => C.p)).real
      (C.graph.coordinateMove C.time C.height C.m C.e y s)) (b : Bool) :
    (BernoulliProduct.law C.scheme.parameter).real
      (C.scheme.hit (target ((0,0),b))
        (C.scheme.block GrowthState.initial∪C.scheme.edgeDomain ((0,0),b)))ᶜ≤C.eta+C.L*C.kappa := by
  let U := C.scheme.block GrowthState.initial∪C.scheme.edgeDomain ((0,0),b)
  have hDU : C.graph.inducedEdges (relayDomain (localTime C.time C.T (0,0))
      (localHeight C.height C.T (0,0)) C.J C.T (sign b))⊆U := by
    rw [← C.domain_eq]
    exact Set.subset_union_right
  have hmoves : ∀ y s, |s|=1 → 1-C.eta≤(BernoulliProduct.law (fun _ : E => C.p)).real
      (C.graph.coordinateMove (localTime C.time C.T (0,0)) (localHeight C.height C.T (0,0))
        C.m C.e y s) := by
    intro y s hs
    rw [coordinateMove_translate]
    exact hmove y s hs
  have hh := C.graph.original_root_corridor_miss h.connected h.locallyFinite C.origin
    (localTime C.time C.T (0,0)) (localHeight C.height C.T (0,0)) (sign b) C.e C.rho C.J
    C.L C.R C.m U hDU (sign_abs b) h.e_pos h.rho_nonneg h.J_lower (C.L_large h) h.e_small h.rho_small
    (by simp [localTime,timeCenter,h.time_origin]) (by simp [localHeight,heightCenter,h.height_origin])
    (fun {_ _} hh => C.local_time_step h (0,0) hh) (fun {_ _} hh => C.local_height_step h (0,0) hh) h.R_gt C.pc C.p h.pc_pos h.pc_lt
    h.p_lower h.p_upper C.D C.k C.M C.VM h.degree h.M_pos h.M_bound h.VM_bound
    C.kappa C.eta h.kappa_pos h.kappa_le h.eta_nonneg h.eta_small h.k_large h.R_large hmoves
  change (BernoulliProduct.law (fun _ : E => C.p)).real
    (C.graph.restrictedSeed (C.graph.vertexBall C.origin C.m)
      (relayMark (localTime C.time C.T (0,0)) (localHeight C.height C.T (0,0)) C.T (sign b) C.rho) U)ᶜ≤_ at hh
  rw [mark_target] at hh
  exact hh
lemma root_positive (h : C.Bounds)
    (hmove : ∀ y s, |s|=1 → 1-C.eta≤(BernoulliProduct.law (fun _ : E => C.p)).real
      (C.graph.coordinateMove C.time C.height C.m C.e y s)) :
    0<(BernoulliProduct.law C.scheme.parameter).real C.scheme.rootEvent := by
  have he : C.scheme.rootEvent=twoPredictions C.scheme.parameter (C.scheme.block GrowthState.initial)
      (C.scheme.hit (target ((0,0),true))
        (C.scheme.block GrowthState.initial∪C.scheme.edgeDomain ((0,0),true)))
      (C.scheme.hit (target ((0,0),false))
        (C.scheme.block GrowthState.initial∪C.scheme.edgeDomain ((0,0),false))) C.delta := by
    ext ω
    change (∀ b : Bool, 1-C.delta≤(blockProbability C.scheme.parameter
      (C.scheme.block GrowthState.initial) (C.scheme.hit (target ((0,0),b))
        (C.scheme.block GrowthState.initial∪C.scheme.edgeDomain ((0,0),b))) ω).toReal) ↔ (_ ∧ _)
    constructor
    · intro hh; exact ⟨hh true,hh false⟩
    · rintro ⟨ht,hf⟩ b; cases b <;> assumption
  rw [he]
  apply twoPredictions_positive _ _ _ _
    (C.graph.restrictedSeed_measurable _ _ _) (C.graph.restrictedSeed_measurable _ _ _)
    C.delta (C.eta+C.L*C.kappa) h.delta_pos h.root_error
    (C.root_corridor_estimate h hmove true) (C.root_corridor_estimate h hmove false)
theorem moves_force_percolation (h : C.Bounds)
    (hmove : ∀ y s, |s|=1 → 1-C.eta≤(BernoulliProduct.law (fun _ : E => C.p)).real
      (C.graph.coordinateMove C.time C.height C.m C.e y s)) :
    0<C.graph.law C.p C.graph.percolates := by
  let hf := C.graph.vertexBall_finite h.locallyFinite C.origin C.m
  exact C.scheme.exploration_percolates (C.layout h).1 (C.layout h).2.1 (C.layout h).2.2
    hf.toFinset (by simp only [Set.Finite.coe_toFinset]; rfl) (C.root_seed h) (C.marks_disjoint h)
    C.p rfl (C.root_positive h hmove) h.delta_pos ((C.L+1)*C.kappa) C.contour
    h.contour_nonneg h.contour_small (mul_nonneg (by positivity) h.kappa_pos.le) h.test_error (C.prospective_estimate h hmove)
theorem moves_impossible_below_criticality (h : C.Bounds)
    (hp : C.p<C.graph.criticalProbability)
    (hmove : ∀ y s, |s|=1 → 1-C.eta≤(BernoulliProduct.law (fun _ : E => C.p)).real
      (C.graph.coordinateMove C.time C.height C.m C.e y s)) : False :=
  (not_le_of_gt hp) (C.graph.criticalProbability_le_of_pos (C.moves_force_percolation h hmove))
end CriticalPercolation.Corridor.CoordinateData
end
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.Gluing.ApproximateMoveEndgame
section

namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.BondGraph
open Corridor
variable {V E : Type*} (G : BondGraph V E)
lemma coordinateMove_sub_const (t z : V → ℝ) (a b : ℝ) (m : ℕ) (e : ℝ) (y : V) (s : ℝ) :
    G.coordinateMove (fun x => t x-a) (fun x => z x-b) m e y s=G.coordinateMove t z m e y s := by
  unfold coordinateMove
  simp only [sub_sub_sub_cancel_right]
  have ht : ∀ x, t x-a-(t y-a+1)=t x-(t y+1) := by intro x; ring
  have hz : ∀ x, z x-b-(z y-b+s)=z x-(z y+s) := by intro x; ring
  simp only [ht,hz]
theorem approximate_moves_contradiction
    (hconnected : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : 0<(G.criticalProbability : ℝ)) (hpc1 : (G.criticalProbability : ℝ)<1)
    (hmoves : ∀ e eta : ℝ, 0<e → e<1/10 → 0<eta → eta<1/10 →
      ∃ m : ℕ, ∀ rho : ℝ, 0<rho → ∃ t z : V → ℝ, ∃ p : unitInterval,
        (G.criticalProbability : ℝ)/2≤p ∧ p<G.criticalProbability ∧
        (∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v|≤rho) ∧
        (∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v|≤rho) ∧
        ∀ y s, |s|=1 → 1-eta≤(BernoulliProduct.law (fun _ : E => p)).real
          (G.coordinateMove t z m e y s)) : False := by
  let := G.countable_vertices hconnected hl
  let := G.countable_bonds hconnected hl
  obtain ⟨o⟩ := hconnected.nonempty
  obtain ⟨m,hm⟩ := hmoves ScaleChoice.e ScaleChoice.eta ScaleChoice.e_pos ScaleChoice.e_lt
    ScaleChoice.eta_pos ScaleChoice.eta_lt
  obtain ⟨D,_hDpos,hD⟩ := G.uniform_incident_bound hq
  obtain ⟨M,hM⟩ := G.uniform_ball_bound hq (4*m+2)
  obtain ⟨VM,hVM⟩ := G.uniform_ball_bound hq m
  obtain ⟨k,R,hk,hR,hRlarge⟩ := ScaleChoice.trial_scales (G.criticalProbability : ℝ) D (M+1) VM m
  obtain ⟨rho,hrho,hrhosmall⟩ := ScaleChoice.mesh R m
  obtain ⟨t,z,p,hpl,hpu,ht,hz,hmv⟩ := hm rho hrho
  let C : CoordinateData V E := {
    graph := G, origin := o, time := fun x => t x-t o, height := fun x => z x-z o,
    J := ScaleChoice.J, L := ScaleChoice.L, R := R, m := m, D := D, k := k,
    M := M+1, VM := VM, e := ScaleChoice.e, rho := rho, kappa := ScaleChoice.kappa,
    eta := ScaleChoice.eta, delta := ScaleChoice.delta, contour := ScaleChoice.contour,
    pc := G.criticalProbability, p := p }
  have hb : C.Bounds := {
    connected := hconnected
    locallyFinite := hl
    time_origin := sub_self _
    height_origin := sub_self _
    time_step := fun {_ _} h => by simpa only [C,sub_sub_sub_cancel_right] using ht h
    height_step := fun {_ _} h => by simpa only [C,sub_sub_sub_cancel_right] using hz h
    J_lower := ScaleChoice.J_lower
    L_lower := ScaleChoice.L_lower
    e_pos := ScaleChoice.e_pos
    rho_nonneg := hrho.le
    e_small := ScaleChoice.e_small
    rho_small := hrhosmall
    R_gt := hR
    pc_pos := hpc
    pc_lt := hpc1
    p_lower := hpl
    p_upper := hpu.le
    degree := hD
    M_pos := Nat.succ_pos M
    M_bound := fun v => (hM v).trans (Nat.le_succ M)
    VM_bound := hVM
    kappa_pos := ScaleChoice.kappa_pos
    kappa_le := ScaleChoice.kappa_le
    eta_nonneg := ScaleChoice.eta_pos.le
    eta_small := ScaleChoice.eta_small
    k_large := hk.le
    R_large := hRlarge
    delta_pos := ScaleChoice.delta_pos
    root_error := ScaleChoice.root_error
    contour_nonneg := ScaleChoice.contour_nonneg
    contour_small := ScaleChoice.contour_small
    test_error := ScaleChoice.test_error }
  apply C.moves_impossible_below_criticality hb hpu
  intro y s hs
  change 1-ScaleChoice.eta≤(BernoulliProduct.law (fun _ : E => p)).real
    (G.coordinateMove (fun x => t x-t o) (fun x => z x-z o) m ScaleChoice.e y s)
  rw [coordinateMove_sub_const]
  exact hmv y s hs
end CriticalPercolation.BondGraph
end
end
end
end OAI

end



namespace CriticalPercolationLeaf
open OAI.CriticalPercolation
theorem finiteSizeCriterion (V E : Type*) : FiniteSizeCriterion V E := by
  intro ends graph full pc ball hc hl hq hp hp1 hm
  let G : BondGraph V E := ⟨ends⟩
  refine G.approximate_moves_contradiction hc hl ?_ hp hp1 ?_
  · obtain ⟨S,hS,h⟩ := hq
    refine ⟨S,hS,fun v => ?_⟩
    obtain ⟨u,hu,f,g,hfg,hv⟩ := h v
    exact ⟨u,hu,⟨f,g,hfg⟩,hv⟩
  · have hb (y : V) (n : ℕ) : G.vertexBall y n = ball y n := by
      induction n with
      | zero => rfl
      | succ n ih => simp only [BondGraph.vertexBall, ih]; rfl
    intro e η he he1 hη hη1
    obtain ⟨m,hr⟩ := hm e η he he1 hη hη1
    refine ⟨m,fun ρ hρ => ?_⟩
    obtain ⟨t,z,p,hlp,hup,ht,hz,hmv⟩ := hr ρ hρ
    refine ⟨t,z,p,hlp,hup,ht,hz,fun y s hs => ?_⟩
    rw [BernoulliProduct.law_const]
    unfold BondGraph.coordinateMove
    rw [hb]
    exact hmv y s hs
end CriticalPercolationLeaf

theorem OMA.solution : OMA.R_arxiv_1902_03207_R1.H1 := CriticalPercolationLeaf.finiteSizeCriterion
