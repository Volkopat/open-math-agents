import OMAReductions.R_Green91_green_91_variants_fknss_R1_H1_R1
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! A direct Hoeffding-and-union-bound formalization of Lemma 2.1 in
Ferber--Kwan--Narayanan--Sah--Sawhney, https://arxiv.org/html/2105.13337. -/


namespace OMA.Green91Concentration

open MeasureTheory ProbabilityTheory Finset Real Filter
open scoped ENNReal NNReal Topology

variable {Ω ι σ : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
variable [IsProbabilityMeasure μ] [Fintype ι]

private theorem bounded_sum_mgf (X : ι → Ω → ℝ) (hind : iIndepFun X μ)
    (hmeas : ∀ i, AEMeasurable (X i) μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (-1 : ℝ) 1)
    (hzero : ∀ i, ∫ ω, X i ω ∂μ = 0) :
    HasSubgaussianMGF (fun ω => ∑ i, X i ω) (Fintype.card ι : ℝ≥0) μ := by
  have ht : ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2 : ℝ≥0) = 1 := by
    apply NNReal.coe_injective
    norm_num
  have hh (i : ι) : HasSubgaussianMGF (X i) 1 μ := ht ▸
    hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hmeas i) (hb i) (hzero i)
  simpa using HasSubgaussianMGF.sum_of_iIndepFun hind
    (c := fun _ => (1 : ℝ≥0)) (s := Finset.univ) (fun i _ => hh i)

omit [IsProbabilityMeasure μ] in
private theorem mgf_weaken {Y : Ω → ℝ} {a b : ℝ≥0}
    (h : HasSubgaussianMGF Y a μ) (hab : a ≤ b) : HasSubgaussianMGF Y b μ := by
  refine ⟨h.integrable_exp_mul, fun t => (h.mgf_le t).trans ?_⟩
  exact Real.exp_le_exp.mpr
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hab (sq_nonneg t)) (by norm_num))

private theorem one_tail {Y : Ω → ℝ} {b : ℝ≥0}
    (h : HasSubgaussianMGF Y b μ) {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t ≤ Y ω} ≤ ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * b))) := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  exact ENNReal.ofReal_le_ofReal (h.measure_ge_le ht)

private theorem two_tails {Y : Ω → ℝ} {b : ℝ≥0}
    (h : HasSubgaussianMGF Y b μ) {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t ≤ |Y ω|} ≤ 2 * ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * b))) := by
  let P : Set Ω := {ω | t ≤ Y ω}
  let Q : Set Ω := {ω | t ≤ -Y ω}
  have hsub : {ω | t ≤ |Y ω|} ⊆ P ∪ Q := by
    intro ω hw
    change t ≤ |Y ω| at hw
    by_cases hs : 0 ≤ Y ω
    · exact Or.inl (by simpa only [P, Set.mem_ofPred_eq, abs_of_nonneg hs] using hw)
    · exact Or.inr (by simpa only [Q, Set.mem_ofPred_eq, abs_of_nonpos (le_of_not_ge hs)] using hw)
  calc
    _ ≤ μ (P ∪ Q) := measure_mono hsub
    _ ≤ μ P + μ Q := measure_union_le _ _
    _ ≤ _ := by
      rw [two_mul]
      exact add_le_add (one_tail μ h ht) (one_tail μ h.neg ht)

/-- A two-sided Hoeffding estimate with a variance bound supplied by the order of
the ambient vertex set. This also covers an empty family of summands. -/
theorem sum_tail (n : ℕ) (hn : 0 < n) (hc : Fintype.card ι ≤ n ^ 2)
    (X : ι → Ω → ℝ) (hind : iIndepFun X μ) (hmeas : ∀ i, AEMeasurable (X i) μ)
    (hb : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (-1 : ℝ) 1)
    (hzero : ∀ i, ∫ ω, X i ω ∂μ = 0) :
    μ {ω | (2 : ℝ) * n * Real.sqrt n ≤ |∑ i, X i ω|} ≤
      2 * ENNReal.ofReal (Real.exp (-2 * n)) := by
  have hmgf := bounded_sum_mgf μ X hind hmeas hb hzero
  have hcard : (Fintype.card ι : ℝ≥0) ≤ (n : ℝ≥0) ^ 2 := by exact_mod_cast hc
  have hbound := two_tails μ (mgf_weaken μ hmgf hcard)
    (t := (2 : ℝ) * n * Real.sqrt n) (by positivity)
  have he : -((2 : ℝ) * n * Real.sqrt n) ^ 2 / (2 * (↑((n : ℝ≥0) ^ 2) : ℝ)) = -2 * n := by
    push_cast
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    field_simp
  simpa only [he] using hbound

variable [Fintype σ]

/-- Union bound over a finite family of cuts. -/
theorem cut_union_tail (n : ℕ) (hn : 0 < n) (hc : Fintype.card ι ≤ n ^ 2)
    (hs : Fintype.card σ ≤ 2 ^ n)
    (X : σ → ι → Ω → ℝ) (hind : ∀ s, iIndepFun (X s) μ)
    (hmeas : ∀ s i, AEMeasurable (X s i) μ)
    (hb : ∀ s i, ∀ᵐ ω ∂μ, X s i ω ∈ Set.Icc (-1 : ℝ) 1)
    (hzero : ∀ s i, ∫ ω, X s i ω ∂μ = 0) :
    μ {ω | ∃ s, (2 : ℝ) * n * Real.sqrt n ≤ |∑ i, X s i ω|} ≤
      (2 : ℝ≥0∞) ^ n * (2 * ENNReal.ofReal (Real.exp (-2 * n))) := by
  let B (s : σ) : Set Ω := {ω | (2 : ℝ) * n * Real.sqrt n ≤ |∑ i, X s i ω|}
  have hset : {ω | ∃ s, (2 : ℝ) * n * Real.sqrt n ≤ |∑ i, X s i ω|} = ⋃ s, B s := by
    ext ω
    simp [B]
  rw [hset]
  calc
    _ ≤ ∑ s, μ (B s) := measure_iUnion_fintype_le μ B
    _ ≤ ∑ _s : σ, (2 * ENNReal.ofReal (Real.exp (-2 * n))) := by
      apply sum_le_sum
      intro s _
      exact sum_tail μ n hn hc (X s) (hind s) (hmeas s) (hb s) (hzero s)
    _ ≤ _ := by
      rw [sum_const, card_univ, nsmul_eq_mul]
      have hrs : (Fintype.card σ : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ n := by exact_mod_cast hs
      exact mul_le_mul_left hrs _

theorem cut_union_bound_tendsto :
    Tendsto (fun n : ℕ => (2 : ℝ≥0∞) ^ n * (2 * ENNReal.ofReal (Real.exp (-2 * n))))
      atTop (𝓝 0) := by
  have h2 : (2 : ℝ) * Real.exp (-2) < 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact (div_lt_one (Real.exp_pos _)).mpr
      ((by norm_num : (2 : ℝ) < 2 + 1).trans_le (Real.add_one_le_exp 2))
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (show 0 ≤ (2 : ℝ) * Real.exp (-2) by positivity) h2).const_mul (2 : ℝ)
  have hte := ENNReal.tendsto_ofReal ht
  simp only [mul_zero, ENNReal.ofReal_zero] at hte
  convert hte using 1
  ext n
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2 * Real.exp (-2)),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    mul_pow, ← ENNReal.ofReal_pow (Real.exp_nonneg _), ← Real.exp_nat_mul,
    show (n : ℝ) * -2 = -2 * n by ring]
  norm_num [mul_comm, mul_left_comm, mul_assoc]

end OMA.Green91Concentration


namespace OMA.Green91Concentration

open MeasureTheory Measure ProbabilityTheory Finset SimpleGraph unitInterval
open scoped Classical ENNReal NNReal

private abbrev OrderedPair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

private def edgeIndex {n : ℕ} (e : OrderedPair n) : Sym2 (Fin n) := s(e.val.1, e.val.2)

private theorem edgeIndex_injective {n : ℕ} : Function.Injective (edgeIndex (n := n)) := by
  intro a b hab
  rcases Sym2.mk_eq_mk_iff.mp hab with h | h
  · exact Subtype.ext h
  · have hx : a.val.1 = b.val.2 := congrArg Prod.fst h
    have hy : a.val.2 = b.val.1 := congrArg Prod.snd h
    have ha := a.property
    rw [hx, hy] at ha
    exact (lt_asymm ha b.property).elim

private noncomputable def coinLaw (n : ℕ) (e : Sym2 (Fin n)) : Measure Prop :=
  (1 / 2 : ℝ≥0) • Measure.dirac (e ∈ (Sym2.diagSet : Set (Sym2 (Fin n)))ᶜ) +
  (1 / 2 : ℝ≥0) • Measure.dirac False

private instance (n : ℕ) (e : Sym2 (Fin n)) : IsProbabilityMeasure (coinLaw n e) := by
  constructor
  rw [coinLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  norm_num [smul_eq_mul]
  simpa only [one_div] using ENNReal.add_halves (1 : ℝ≥0∞)

private noncomputable def half : unitInterval := ⟨1 / 2, by norm_num⟩

private noncomputable def sampleGraph {n : ℕ} (ω : Sym2 (Fin n) → Prop) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e | ω e}

private theorem sample_measurable (n : ℕ) :
    Measurable (sampleGraph (n := n)) :=
  SimpleGraph.measurable_fromEdgeSet.comp MeasurableEquiv.setOfPred.measurable

private theorem sample_law (n : ℕ) :
    (Measure.infinitePi (coinLaw n)).map sampleGraph = SimpleGraph.binomialRandom (Fin n) half := by
  have hh : toNNReal half = 1 / 2 := by
    apply NNReal.coe_injective
    norm_num [half]
  have hs : toNNReal (unitInterval.symm half) = 1 / 2 := by
    apply NNReal.coe_injective
    norm_num [half, unitInterval.symm]
  have hset : Measurable (fun ω : Sym2 (Fin n) → Prop => {e | ω e}) :=
    MeasurableEquiv.setOfPred.measurable
  rw [SimpleGraph.binomialRandom_eq_map, setBernoulli_eq_map, hh, hs]
  exact (Measure.map_map SimpleGraph.measurable_fromEdgeSet hset).symm

theorem measurable_graph_event {n : ℕ} (E : Set (SimpleGraph (Fin n))) :
    MeasurableSet E := by
  let _ : MeasurableSingletonClass (SimpleGraph (Fin n)) := ⟨fun G => by
    have h := SimpleGraph.measurable_edgeSet (measurableSet_singleton G.edgeSet)
    have he : (SimpleGraph.edgeSet : SimpleGraph (Fin n) → Set (Sym2 (Fin n))) ⁻¹'
        {G.edgeSet} = {G} := by
      ext K
      simp [SimpleGraph.edgeSet_injective.eq_iff]
    exact he ▸ h⟩
  exact (Set.to_countable _).measurableSet

private theorem fair_mean_zero {n : ℕ} (e : OrderedPair n) (w : ℝ) :
    ∫ ω, (if ω (edgeIndex e) then w else -w) ∂Measure.infinitePi (coinLaw n) = 0 := by
  let f (b : Prop) : ℝ := if b then w else -w
  have hf : Measurable f := measurable_of_countable f
  have hπ : Measurable (fun ω : Sym2 (Fin n) → Prop => ω (edgeIndex e)) := measurable_pi_apply _
  change ∫ ω, f (ω (edgeIndex e)) ∂Measure.infinitePi (coinLaw n) = 0
  rw [← integral_map hπ.aemeasurable hf.aestronglyMeasurable, Measure.infinitePi_map_eval]
  let supported : Prop := edgeIndex e ∈ (Sym2.diagSet : Set (Sym2 (Fin n)))ᶜ
  have hI : supported := by
    change ¬ (edgeIndex e).IsDiag
    exact fun h => e.property.ne (Sym2.mk_isDiag_iff.mp h)
  have h1 : Integrable f ((1 / 2 : ℝ≥0) • Measure.dirac supported) :=
    (integrable_dirac enorm_lt_top).smul_measure_nnreal
  have h0 : Integrable f ((1 / 2 : ℝ≥0) • Measure.dirac False) :=
    (integrable_dirac enorm_lt_top).smul_measure_nnreal
  change (∫ b, f b ∂((1 / 2 : ℝ≥0) • Measure.dirac supported +
    (1 / 2 : ℝ≥0) • Measure.dirac False)) = 0
  rw [integral_add_measure h1 h0]
  simp [f, hI]

/-- Signed edge sums obey a simultaneous tail bound over all vertex cuts. -/
theorem binomial_cut_union_tail (n : ℕ) (hn : 0 < n)
    (weight : Finset (Fin n) → OrderedPair n → ℝ)
    (hWeight : ∀ s e, weight s e ∈ Set.Icc (-1 : ℝ) 1) :
    SimpleGraph.binomialRandom (Fin n) ⟨1 / 2, by norm_num⟩
      {G | ∃ s : Finset (Fin n), (2 : ℝ) * n * Real.sqrt n ≤
        |∑ e : OrderedPair n, weight s e *
          (2 * (if G.Adj e.val.1 e.val.2 then (1 : ℝ) else 0) - 1)|} ≤
      (2 : ℝ≥0∞) ^ n * (2 * ENNReal.ofReal (Real.exp (-2 * n))) := by
  let μ := Measure.infinitePi (coinLaw n)
  let X (s : Finset (Fin n)) (e : OrderedPair n) (ω : Sym2 (Fin n) → Prop) : ℝ :=
    if ω (edgeIndex e) then weight s e else -weight s e
  have hind0 : iIndepFun (fun e (ω : Sym2 (Fin n) → Prop) => ω e) μ :=
    iIndepFun_infinitePi (P := coinLaw n) (X := fun _ => id) (fun _ => measurable_id)
  have hind (s : Finset (Fin n)) : iIndepFun (X s) μ :=
    (hind0.precomp edgeIndex_injective).comp
      (fun e b => if b then weight s e else -weight s e) (fun _ => measurable_of_countable _)
  have hmeas (s : Finset (Fin n)) (e : OrderedPair n) : AEMeasurable (X s e) μ :=
    ((measurable_of_countable (fun b : Prop => if b then weight s e else -weight s e)).comp
      (measurable_pi_apply (edgeIndex e))).aemeasurable
  have hb (s : Finset (Fin n)) (e : OrderedPair n) :
      ∀ᵐ ω ∂μ, X s e ω ∈ Set.Icc (-1 : ℝ) 1 := by
    apply ae_of_all
    intro ω
    dsimp only [X]
    split
    · exact hWeight s e
    · obtain ⟨h₁, h₂⟩ := hWeight s e
      exact ⟨by linarith, by linarith⟩
  have he (s : Finset (Fin n)) (e : OrderedPair n) : ∫ ω, X s e ω ∂μ = 0 :=
    fair_mean_zero e (weight s e)
  have hcard : Fintype.card (OrderedPair n) ≤ n ^ 2 := by
    simpa [pow_two] using Fintype.card_subtype_le
      (fun p : Fin n × Fin n => p.1 < p.2)
  have hcuts : Fintype.card (Finset (Fin n)) ≤ 2 ^ n := by simp [Fintype.card_finset]
  have hTail := cut_union_tail μ n hn hcard hcuts X hind hmeas hb he
  let E : Set (SimpleGraph (Fin n)) :=
    {G | ∃ s : Finset (Fin n), (2 : ℝ) * n * Real.sqrt n ≤
      |∑ e : OrderedPair n, weight s e *
        (2 * (if G.Adj e.val.1 e.val.2 then (1 : ℝ) else 0) - 1)|}
  change SimpleGraph.binomialRandom (Fin n) half E ≤ _
  rw [← sample_law, Measure.map_apply (sample_measurable n) (measurable_graph_event E)]
  have hterm (s : Finset (Fin n)) (e : OrderedPair n) (ω : Sym2 (Fin n) → Prop) :
      weight s e * (2 * (if (sampleGraph ω).Adj e.val.1 e.val.2 then (1 : ℝ) else 0) - 1) =
        X s e ω := by
    have hAdj : (sampleGraph ω).Adj e.val.1 e.val.2 ↔ ω (edgeIndex e) := by
      simp [sampleGraph, SimpleGraph.fromEdgeSet_adj, edgeIndex, e.property.ne]
    by_cases hw : ω (edgeIndex e) <;> norm_num [X, hAdj, hw]
  have hSet : sampleGraph ⁻¹' E =
      {ω | ∃ s, (2 : ℝ) * n * Real.sqrt n ≤ |∑ e, X s e ω|} := by
    ext ω
    simp only [Set.mem_preimage, E, Set.mem_ofPred_eq, hterm]
  rw [hSet]
  exact hTail

end OMA.Green91Concentration


/-! Write the score of a balanced bisection as a centered edge sum. -/

namespace OMA.Green91Score
open Finset
open scoped Classical

abbrev OrderedEdge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

noncomputable def side {n : ℕ} (s : Finset (Fin n)) (x : Fin n) : ℝ :=
  if x ∈ s then 1 else -1

noncomputable def edgeSign {n : ℕ} (s : Finset (Fin n)) (x y : Fin n) : ℝ :=
  side s x * side s y

noncomputable def adjacency {n : ℕ} (G : SimpleGraph (Fin n)) (x y : Fin n) : ℝ :=
  if G.Adj x y then 1 else 0

private theorem ordered_pairs {V : Type*} [LinearOrder V] [Fintype V]
    (f : V → V → ℝ) (hsym : ∀ x y, f y x = f x y) (hdiag : ∀ x, f x x = 0) :
    (∑ x, ∑ y, f x y) = 2 * ∑ p : {p : V × V // p.1 < p.2}, f p.1.1 p.1.2 := by
  let part (p : V × V) := if p.1 < p.2 then f p.1 p.2 else 0
  let lower (p : V × V) := if p.2 < p.1 then f p.1 p.2 else 0
  have hsplit (p : V × V) : f p.1 p.2 = part p + lower p := by
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · simp [part, lower, h, not_lt_of_gt h]
    · simp [part, lower, h, hdiag]
    · simp [part, lower, h, not_lt_of_gt h]
  have hswap : (∑ p, lower p) = ∑ p, part p := by
    apply Fintype.sum_equiv (Equiv.prodComm V V)
    intro p
    simp [part, lower, hsym]
  have hrestrict : (∑ p, part p) = ∑ p : {p : V × V // p.1 < p.2}, f p.1.1 p.1.2 := by
    dsimp only [part]
    rw [← sum_filter]
    exact sum_subtype _ (by simp) _
  calc
    _ = ∑ p : V × V, f p.1 p.2 := (Fintype.sum_prod_type (fun p => f p.1 p.2)).symm
    _ = ∑ p, (part p + lower p) := sum_congr rfl fun p _ => hsplit p
    _ = _ := by rw [sum_add_distrib, hswap, hrestrict, two_mul]

private theorem friendliness_row {n : ℕ} (G : SimpleGraph (Fin n)) (s : Finset (Fin n))
    (x : Fin n) : (Green91.friendliness G s x : ℝ) =
      ∑ y, edgeSign s x y * adjacency G x y := by
  unfold Green91.friendliness
  push_cast
  rw [← sum_boole, ← sum_boole, ← sum_sub_distrib]
  refine sum_congr rfl fun y _ => ?_
  by_cases hx : x ∈ s <;> by_cases hy : y ∈ s <;> by_cases hxy : G.Adj x y <;>
    simp [edgeSign, side, adjacency, hx, hy, hxy]

theorem graph_score {n : ℕ} (G : SimpleGraph (Fin n)) (s : Finset (Fin n)) :
    (∑ x, (Green91.friendliness G s x : ℝ)) =
      2 * ∑ p : OrderedEdge n, edgeSign s p.1.1 p.1.2 * adjacency G p.1.1 p.1.2 := by
  simp only [friendliness_row]
  apply ordered_pairs
  · intro x y
    simp [adjacency, G.adj_comm y x, edgeSign, mul_comm]
  · simp [adjacency]

private theorem balanced_weight {m : ℕ} (s : Finset (Fin (2*m))) (hs : s.card = m) :
    (∑ x, side s x) = 0 := by
  have hcompl : sᶜ.card = m := by
    simp [card_compl, hs]
    omega
  have hfilter : (Finset.univ.filter fun x => x ∉ s) = sᶜ := by ext; simp
  unfold side
  rw [sum_ite]
  rw [hfilter]
  simp [hcompl, hs]

theorem balanced_center {m : ℕ} (s : Finset (Fin (2*m))) (hs : s.card = m) :
    (∑ p : OrderedEdge (2*m), edgeSign s p.1.1 p.1.2) = -(m : ℝ) := by
  let f (x y : Fin (2*m)) : ℝ := if x = y then 0 else edgeSign s x y
  have hf (x y : Fin (2*m)) : f x y = side s x * side s y - if x = y then 1 else 0 := by
    by_cases h : x = y
    · subst y
      by_cases hx : x ∈ s <;> simp [f, side, hx]
    · simp [f, h, edgeSign]
  have hupper := ordered_pairs f (by
    intro x y
    simp [f, eq_comm, edgeSign, mul_comm]) (by simp [f])
  have hsum : (∑ x, ∑ y, f x y) = -(2 * (m : ℝ)) := by
    simp_rw [hf, sum_sub_distrib, ← mul_sum, balanced_weight s hs]
    simp
  rw [hsum] at hupper
  have heq : (∑ p : OrderedEdge (2*m), f p.1.1 p.1.2) =
      ∑ p : OrderedEdge (2*m), edgeSign s p.1.1 p.1.2 := by
    exact sum_congr rfl fun p _ => if_neg p.2.ne
  rw [heq] at hupper
  linarith

theorem balanced_score {m : ℕ} (G : SimpleGraph (Fin (2*m))) (s : Finset (Fin (2*m)))
    (hs : s.card = m) :
    (∑ x, (Green91.friendliness G s x : ℝ)) =
      (∑ p : OrderedEdge (2*m), edgeSign s p.1.1 p.1.2 * (2 * adjacency G p.1.1 p.1.2 - 1)) -
        (m : ℝ) := by
  rw [graph_score]
  simp_rw [mul_sub, mul_one, mul_left_comm (edgeSign s _ _) 2, sum_sub_distrib, ← mul_sum,
    balanced_center s hs]
  ring

theorem normalized_score_le {m : ℕ} (hm : 0 < m) (G : SimpleGraph (Fin (2*m)))
    (s : Finset (Fin (2*m))) (hs : s.card = m)
    (h : |∑ p : OrderedEdge (2*m), edgeSign s p.1.1 p.1.2 * (2 * adjacency G p.1.1 p.1.2 - 1)| ≤
      2 * ((2*m : ℕ) : ℝ) * Real.sqrt (2*m : ℕ)) :
    |(∑ x, (Green91.friendliness G s x : ℝ)) / (((2*m : ℕ) : ℝ) * Real.sqrt (2*m : ℕ))| ≤ 3 := by
  let n : ℝ := (2*m : ℕ)
  have hn : 1 ≤ n := by
    dsimp only [n]
    exact_mod_cast (show 1 ≤ 2*m by omega)
  have hnpos : 0 < n := by linarith
  have hsqrt : 1 ≤ Real.sqrt n := Real.le_sqrt_of_sq_le (by simpa using hn)
  have hD : 0 < n * Real.sqrt n := mul_pos hnpos (by linarith)
  have hmle : (m : ℝ) ≤ n := by
    dsimp only [n]
    exact_mod_cast (show m ≤ 2*m by omega)
  have hmD : (m : ℝ) ≤ n * Real.sqrt n := hmle.trans (le_mul_of_one_le_right hnpos.le hsqrt)
  rw [abs_div, abs_of_pos hD, div_le_iff₀ hD, balanced_score G s hs]
  apply (abs_sub _ _).trans
  have hmnonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  rw [abs_of_nonneg hmnonneg]
  change _ ≤ 3 * (n * Real.sqrt n)
  change _ ≤ 2 * n * Real.sqrt n at h
  nlinarith only [h, hmD]

end OMA.Green91Score


/-! The union bound yields the score event in the merged reduction. -/

namespace OMA.Green91Score

open Filter MeasureTheory
open scoped ENNReal Topology Classical
open OMA.Green91Concentration

private def typical (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ s : Finset (Fin n),
    |∑ e : OrderedEdge n, edgeSign s e.1.1 e.1.2 * (2 * adjacency G e.1.1 e.1.2 - 1)| <
      2 * (n : ℝ) * Real.sqrt n

private theorem weight_range (n : ℕ) (s : Finset (Fin n)) (e : OrderedEdge n) :
    edgeSign s e.1.1 e.1.2 ∈ Set.Icc (-1 : ℝ) 1 := by
  by_cases h₁ : e.1.1 ∈ s <;> by_cases h₂ : e.1.2 ∈ s <;>
    norm_num [edgeSign, side, h₁, h₂, Set.mem_Icc]

private theorem typical_prob_lower (n : ℕ) (hn : 0 < n) :
    1 - (2 : ℝ≥0∞) ^ n * (2 * ENNReal.ofReal (Real.exp (-2 * n))) ≤
      Green91.prob n (typical n) := by
  let P : Set (SimpleGraph (Fin n)) := {G | typical n G}
  let μ := SimpleGraph.binomialRandom (Fin n) ⟨1 / 2, by norm_num⟩
  have htail := binomial_cut_union_tail n hn (fun s e => edgeSign s e.1.1 e.1.2)
    (weight_range n)
  have hbad : μ Pᶜ ≤ (2 : ℝ≥0∞) ^ n * (2 * ENNReal.ofReal (Real.exp (-2 * n))) := by
    convert htail using 2
    ext G
    simp [P, typical, adjacency, not_lt, not_forall]
  rw [prob_compl_eq_one_sub (measurable_graph_event P)] at hbad
  change _ ≤ μ P
  apply tsub_le_iff_right.mpr
  rw [add_comm]
  exact tsub_le_iff_right.mp hbad

private theorem half_order_limit : Tendsto (fun m : ℕ => 2 * m) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop b] with m hm
  omega

private theorem typical_prob_limit :
    Tendsto (fun m : ℕ => Green91.prob (2*m) (typical (2*m))) atTop (𝓝 1) := by
  have hb := cut_union_bound_tendsto.comp half_order_limit
  have hOne : Tendsto (fun _ : ℕ => (1 : ℝ≥0∞)) atTop (𝓝 1) := tendsto_const_nhds
  have hlow : Tendsto
      (fun m : ℕ => 1 - (2 : ℝ≥0∞) ^ (2*m) * (2 * ENNReal.ofReal (Real.exp (-2 * (2*m : ℕ)))))
      atTop (𝓝 1) := by
    simpa only [Function.comp_apply, tsub_zero] using
      ENNReal.Tendsto.sub hOne hb (Or.inl ENNReal.one_ne_top)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hOne
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    exact typical_prob_lower (2*m) (by omega)
  · exact Eventually.of_forall fun _ => OMA.FriendlyBisection.prob_le_one_event _

end OMA.Green91Score

open Filter
open scoped Topology Classical

theorem OMA.solution : OMA.R_Green91_green_91_variants_fknss_R1_H1_R1.H1 := by
  refine ⟨3, by norm_num, ?_⟩
  change Tendsto (fun m : ℕ => Green91.prob (2*m) (fun G => ∀ s : Finset (Fin (2*m)),
    s.card = m →
    |(∑ x, (Green91.friendliness G s x : ℝ)) / (((2*m : ℕ) : ℝ) * Real.sqrt (2*m : ℕ))| ≤ 3))
    atTop (𝓝 1)
  apply OMA.FriendlyBisection.high_mono (P := fun m => OMA.Green91Score.typical (2*m))
    _ OMA.Green91Score.typical_prob_limit
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  intro G hG s hs
  exact OMA.Green91Score.normalized_score_le hm G s hs (hG s).le
