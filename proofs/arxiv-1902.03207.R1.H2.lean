import OMAReductions.R_arxiv_1902_03207_R1

/-!
# Strict upper bound for the rooted percolation threshold

Credit: @my-other-github-account. The contour and product-measure lemmas are
adapted from OpenAI, openai/math@3344da59991ed94f9ba711217b29c1d760badfa6
(Apache-2.0). Embed the first quadrant using two coordinate directions.
A finite reachable set has a closed boundary whose outside sites require
failures on disjoint bond blocks. Summing over contours leaves positive
probability of an infinite cluster at the parameter 1 − 1/20000.
-/

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
def cluster (ω : Set E) (v : V) : Set V := {w | (G.openGraph ω).Reachable v w}
noncomputable def law (_G : BondGraph V E) (p : unitInterval) : Measure (Set E) :=
  ProbabilityTheory.setBernoulli Set.univ p
end BondGraph
end CriticalPercolation
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
end BernoulliProduct
end CriticalPercolation
open Set
open scoped Classical
end
end
end OAI

end
-- OAI.Probability.CriticalPercolation.GraphGeometry.OpenGraphIso
namespace OAI.CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)
def infiniteEvent (o : V) : Set (Set E) := {ω | (G.cluster ω o).Infinite}
end OAI.CriticalPercolation.BondGraph
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
end CriticalPercolation.BernoulliProduct
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
lemma independent_block_events (q : E → unitInterval) (S : I → Set E)
    (hS : Pairwise (fun i j => Disjoint (S i) (S j))) (A : I → Set (Set E))
    (hA : ∀ i, MeasurableSet[blockSigma (S i)] (A i)) : iIndepSet A (law q) :=
  (independent_block_family q S hS).iIndepSets'.iIndepSet_of_mem hA
    (fun i => blockSigma_le (S i) _ (hA i))
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
end CriticalPercolation.BernoulliProduct
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

namespace OMA.P_arxiv_1902_03207
open Set MeasureTheory ProbabilityTheory OAI.CriticalPercolation OMA.S_arxiv_1902_03207

variable {d : ℕ}

def L (d : ℕ) : BondGraph (Vertex d) (Bond d) := ⟨ends⟩

abbrev u (i : Fin d) : Vertex d := Pi.single i 1

lemma ne_step (x : Vertex d) (i : Fin d) : x ≠ x + u i := by
  intro h
  have := congrFun h i
  simp at this

section Peierls
variable (h2 : 2 ≤ d)

def i0 : Fin d := ⟨0, by omega⟩
def i1 : Fin d := ⟨1, by omega⟩

lemma i01 : i0 h2 ≠ i1 h2 := by simp [i0, i1, Fin.ext_iff]

def emb (v : Boundary.Grid) : Vertex d := v.1 • u (i0 h2) + v.2 • u (i1 h2)

lemma emb_add (a b : Boundary.Grid) : emb h2 (a + b) = emb h2 a + emb h2 b := by
  simp only [emb, Prod.fst_add, Prod.snd_add, add_smul]
  abel

lemma emb_zero : emb h2 (0, 0) = 0 := by simp [emb]

lemma emb_e : emb h2 (1, 0) = u (i0 h2) := by simp [emb]
lemma emb_n : emb h2 (0, 1) = u (i1 h2) := by simp [emb]

lemma emb_inj : Function.Injective (emb h2) := by
  intro a b h
  have h0 := congrFun h (i0 h2)
  have h1 := congrFun h (i1 h2)
  have hne := i01 h2
  simp [emb, hne, hne.symm] at h0 h1
  exact Prod.ext h0 h1

def R (ω : Set (Bond d)) (y z : Boundary.Grid) : Prop :=
  (z = y + (1, 0) ∧ (emb h2 y, i0 h2) ∈ ω) ∨ (z = y + (0, 1) ∧ (emb h2 y, i1 h2) ∈ ω)

def S (ω : Set (Bond d)) : Set Boundary.Grid := {z | Relation.ReflTransGen (R h2 ω) (0, 0) z}

def F (z : Boundary.Grid) : Set (Set (Bond d)) :=
  {ω | (emb h2 (z - (1, 0)), i0 h2) ∉ ω} ∪ {ω | (emb h2 (z - (0, 1)), i1 h2) ∉ ω}

def blk (z : Boundary.Grid) : Set (Bond d) :=
  {(emb h2 (z - (1, 0)), i0 h2), (emb h2 (z - (0, 1)), i1 h2)}

lemma S_quad (ω : Set (Bond d)) : ∀ v ∈ S h2 ω, 0 ≤ v.1 ∧ 0 ≤ v.2 := by
  intro v hv
  induction hv with
  | refl => simp
  | tail _ h ih =>
    rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · simp only [Prod.fst_add, Prod.snd_add]; constructor <;> linarith [ih.1, ih.2]
    · simp only [Prod.fst_add, Prod.snd_add]; constructor <;> linarith [ih.1, ih.2]

lemma S_reach (ω : Set (Bond d)) {z : Boundary.Grid} (hz : z ∈ S h2 ω) :
    ((L d).openGraph ω).Reachable 0 (emb h2 z) := by
  induction hz with
  | refl => rw [emb_zero]
  | @tail y z _ h ih =>
    refine ih.trans (SimpleGraph.Adj.reachable ?_)
    rcases h with ⟨rfl, hb⟩ | ⟨rfl, hb⟩
    · refine ⟨⟨_, hb, ?_⟩, ?_⟩
      · change s(emb h2 y, emb h2 y + u (i0 h2)) = _
        rw [emb_add, emb_e]
      · rw [emb_add, emb_e]; exact ne_step _ _
    · refine ⟨⟨_, hb, ?_⟩, ?_⟩
      · change s(emb h2 y, emb h2 y + u (i1 h2)) = _
        rw [emb_add, emb_n]
      · rw [emb_add, emb_n]; exact ne_step _ _

lemma blk_disj : Pairwise (fun a b => Disjoint (blk h2 a) (blk h2 b)) := by
  intro a b hab
  have hne := i01 h2
  rw [Set.disjoint_left]
  intro e ha hb
  simp only [blk, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with h | h <;>
    simp only [Prod.mk.injEq] at h
  · exact hab (sub_left_injective (emb_inj h2 h.1))
  · exact hne h.2
  · exact hne h.2.symm
  · exact hab (sub_left_injective (emb_inj h2 h.1))

noncomputable def p0 : unitInterval := ⟨1 - 1 / 20000, by norm_num, by norm_num⟩

lemma closed_real (e : Bond d) :
    (BernoulliProduct.law (fun _ : Bond d => p0)).real {ω | e ∉ ω} = 1 / 20000 := by
  have h := BernoulliProduct.law_coordinate (fun _ : Bond d => p0) e False
  have hs : {ω : Set (Bond d) | (e ∈ ω) = False} = {ω | e ∉ ω} := by
    ext ω; simp
  rw [hs] at h
  rw [measureReal_def, h, ← measureReal_def, BernoulliProduct.bitMeasure_real_singleton]
  simp [BernoulliProduct.bitWeight, p0]

lemma F_meas (z : Boundary.Grid) :
    MeasurableSet[BernoulliProduct.blockSigma (blk h2 z)] (F h2 z) := by
  apply MeasurableSet.union
  · exact (le_iSup_of_le _ (le_iSup_of_le (by simp [blk]) le_rfl) :
      BernoulliProduct.coordinateSigma _ ≤ BernoulliProduct.blockSigma (blk h2 z)) _
      (BernoulliProduct.measurableSet_closed_coordinate _)
  · exact (le_iSup_of_le _ (le_iSup_of_le (by simp [blk]) le_rfl) :
      BernoulliProduct.coordinateSigma _ ≤ BernoulliProduct.blockSigma (blk h2 z)) _
      (BernoulliProduct.measurableSet_closed_coordinate _)

lemma theta_pos (h2 : 2 ≤ d) : 0 < (L d).law p0 ((L d).infiniteEvent 0) := by
  let μ := BernoulliProduct.law (fun _ : Bond d => p0)
  have hμ : (L d).law p0 = μ := (BernoulliProduct.law_const p0).symm
  have hind := BernoulliProduct.independent_block_events (fun _ : Bond d => p0) (blk h2)
    (blk_disj h2) (F h2) (F_meas h2)
  have hF : ∀ z, μ.real (F h2 z) ≤ (1 / 10 : ℝ) ^ 4 := by
    intro z
    refine (measureReal_union_le _ _).trans ?_
    rw [closed_real, closed_real]
    norm_num
  have hfail : ∀ s : Finset Boundary.Grid,
      μ.real (Set.univ ∩ ⋂ z ∈ s, F h2 z) ≤ μ.real Set.univ * ((1 / 10 : ℝ) ^ 4) ^ s.card := by
    intro s
    rw [Set.univ_inter, probReal_univ, one_mul, measureReal_def, hind.meas_biInter s,
      ENNReal.toReal_prod]
    calc ∏ z ∈ s, (μ (F h2 z)).toReal ≤ ∏ _z ∈ s, (1 / 10 : ℝ) ^ 4 :=
          Finset.prod_le_prod (fun _ _ => ENNReal.toReal_nonneg) (fun z _ => hF z)
      _ = _ := Finset.prod_const _
  have hpos := Boundary.infinite_good_positive μ Set.univ (S h2) (F h2)
    (by rw [probReal_univ]; norm_num) (fun ω _ => Relation.ReflTransGen.refl)
    (fun ω _ => S_quad h2 ω) ?_ (1 / 10) (by norm_num) (by norm_num) hfail
  · rw [hμ]
    apply ENNReal.toReal_pos_iff.mp (lt_of_lt_of_le hpos (measureReal_mono ?_)) |>.1
    rintro ω ⟨-, hω⟩
    change ((L d).cluster ω 0).Infinite
    apply ((hω.image (emb_inj h2).injOn)).mono
    rintro _ ⟨z, hz, rfl⟩
    exact S_reach h2 ω hz
  · rintro ω - z hz ⟨y, hy, hzy | hzy⟩
    · left
      rw [hzy, add_sub_cancel_right]
      exact fun hb => hz (Relation.ReflTransGen.tail hy (Or.inl ⟨hzy, hb⟩))
    · right
      rw [hzy, add_sub_cancel_right]
      exact fun hb => hz (Relation.ReflTransGen.tail hy (Or.inr ⟨hzy, hb⟩))

end Peierls
end OMA.P_arxiv_1902_03207

open OMA.P_arxiv_1902_03207 OMA.S_arxiv_1902_03207 in
theorem OMA.solution : OMA.R_arxiv_1902_03207_R1.H2 := by
  intro d hd
  have h : 0 < theta d p0 := theta_pos hd
  exact lt_of_le_of_lt (sInf_le (s := {p | 0 < theta d p}) h)
    (by rw [← Subtype.coe_lt_coe]; norm_num [p0])
