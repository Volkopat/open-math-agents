import OMAReductions.R_arxiv_2009_03418_R1_H2_R2
import Mathlib
/- Adapted from OpenAI openai/math@3344da59991ed94f9ba711217b29c1d760badfa6,
CompleteCrossing/Deletion. Apache-2.0. -/
namespace HillDeletionPort
open OMA.S_arxiv_2009_03418
open scoped BigOperators Classical

def H1 : Prop := ∀ n : ℕ, 4 ≤ n → ∀ D : AdmissibleDrawing (completeGraph (n+1)),
  ∃ B : AdmissibleDrawing (completeGraph (n+1)), crossingCount B ≤ crossingCount D ∧
    (∀ e f : CompleteEdge (n+1), e ≠ f →
      (e.val.1 = f.val.1 ∨ e.val.1 = f.val.2 ∨ e.val.2 = f.val.1 ∨ e.val.2 = f.val.2) →
      Disjoint (edgeInterior B.toContinuousDrawing e) (edgeInterior B.toContinuousDrawing f))

def H2 : Prop := ∀ n : ℕ, 4 ≤ n → ∀ B : AdmissibleDrawing (completeGraph (n+1)),
    (∀ e f : CompleteEdge (n+1), e ≠ f →
      (e.val.1 = f.val.1 ∨ e.val.1 = f.val.2 ∨ e.val.2 = f.val.1 ∨ e.val.2 = f.val.2) →
      Disjoint (edgeInterior B.toContinuousDrawing e) (edgeInterior B.toContinuousDrawing f)) →
  ∃ A : Fin (n+1) → AdmissibleDrawing (completeGraph n), (∑ v, crossingCount (A v)) = (n+1-4) * crossingCount B

theorem main : H1 → H2 → OMA.R_arxiv_2009_03418_R1_H2_R2.H2 := by
  intro normalize count n hn D
  obtain ⟨B, hle, hB⟩ := normalize n hn D
  obtain ⟨A, hA⟩ := count n hn B hB
  exact ⟨A, hA.le.trans (Nat.mul_le_mul_left _ hle)⟩
end HillDeletionPort

/- Adapted from openai/math@3344da59991ed94f9ba711217b29c1d760badfa6, Apache-2.0. -/
section
namespace OAI
section
noncomputable section
namespace Paper170
end Paper170
end
end
section
noncomputable section
namespace Paper170
end Paper170
end
end
section
noncomputable section
namespace Paper170
end Paper170
end
end
section
noncomputable section
namespace Paper170
end Paper170
end
end
end OAI
end
section
namespace OAI
namespace Zarankiewicz
end Zarankiewicz
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
abbrev Plane := ℝ × ℝ
def ProperCrossing (A B : Set Plane) (x : Plane) : Prop :=
  ∃ chart : OpenPartialHomeomorph Plane Plane,
    x ∈ chart.source ∧ chart x = (0,0) ∧
    chart '' (chart.source ∩ A) = chart.target ∩ {y | y.2 = 0} ∧
    chart '' (chart.source ∩ B) = chart.target ∩ {y | y.1 = 0}
end Zarankiewicz
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Set
open scoped BigOperators Classical
namespace Paper170
abbrev Plane := ℝ × ℝ
/-- One chosen orientation of each edge of a finite simple graph. -/
structure Graph (V E : Type) where
  src : E → V
  dst : E → V
  loopless : ∀ e, src e ≠ dst e
  simple : ∀ e f, ((src e = src f ∧ dst e = dst f) ∨
    (src e = dst f ∧ dst e = src f)) → e = f
abbrev CompleteEdge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
instance (n : ℕ) : Fintype (CompleteEdge n) := Fintype.ofFinite _
def completeGraph (n : ℕ) : Graph (Fin n) (CompleteEdge n) where
  src e := e.val.1
  dst e := e.val.2
  loopless e := ne_of_lt e.property
  simple e f h := by
    rcases h with h | h
    · exact Subtype.ext (Prod.ext h.1 h.2)
    · have he := e.property
      have hf := f.property
      rw [h.1, h.2] at he
      exact (lt_asymm he hf).elim
variable {V E : Type} (G : Graph V E)
namespace Graph
end Graph
/-- Actual injective continuous edge arcs, with unrestricted routing. -/
structure ContinuousDrawing where
  vertex : V → Plane
  vertex_injective : Function.Injective vertex
  edge : ∀ e : E, Path (vertex (G.src e)) (vertex (G.dst e))
  edge_injective : ∀ e, Function.Injective (edge e)
  interior_avoids_vertices : ∀ e t, t ∈ Ioo (0 : unitInterval) 1 →
    ∀ v, edge e t ≠ vertex v
variable {G}
def edgeInterior (D : ContinuousDrawing G) (e : E) : Set Plane :=
  D.edge e '' Ioo (0 : unitInterval) 1
/-- A proper double crossing is locally homeomorphic to two coordinate axes. -/
structure ProperCrossing (A B : Set Plane) (x : Plane) : Prop where
  chart_exists : ∃ chart : OpenPartialHomeomorph Plane Plane,
    x ∈ chart.source ∧ chart x = (0, 0) ∧
    chart '' (chart.source ∩ A) = chart.target ∩ {y | y.2 = 0} ∧
    chart '' (chart.source ∩ B) = chart.target ∩ {y | y.1 = 0}
/-- Spatial intersection points. Different meetings of the same pair remain distinct. -/
def crossingPoints (D : ContinuousDrawing G) : Set Plane :=
  {x | ∃ e f : E, e ≠ f ∧ x ∈ edgeInterior D e ∧ x ∈ edgeInterior D f}
structure AdmissibleDrawing (G : Graph V E) extends ContinuousDrawing G where
  crossings_finite : (crossingPoints toContinuousDrawing).Finite
  crossings_proper : ∀ e f, e ≠ f → ∀ x,
    x ∈ edgeInterior toContinuousDrawing e → x ∈ edgeInterior toContinuousDrawing f →
      ProperCrossing (edgeInterior toContinuousDrawing e) (edgeInterior toContinuousDrawing f) x
  no_triples : ∀ e f g, e ≠ f → e ≠ g → f ≠ g →
    edgeInterior toContinuousDrawing e ∩ edgeInterior toContinuousDrawing f ∩
      edgeInterior toContinuousDrawing g = ∅
def crossingCount (D : AdmissibleDrawing G) : ℕ := D.crossings_finite.toFinset.card
/-- The minimum spatial crossing count over admissible drawings. -/
def ordinaryCrossingNumber (G : Graph V E) : ℕ := sInf (range (@crossingCount V E G))
end Paper170
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
theorem edgeInterior_subset_range (D : Paper170.ContinuousDrawing graph) (e : Edge) :
    Paper170.edgeInterior D e ⊆ Set.range (D.edge e) := by
  rintro x ⟨t,_,he⟩
  exact ⟨t,he⟩
theorem edgeInterior_of_range_not_vertices (D : Paper170.ContinuousDrawing graph) (e : Edge)
    (x : Plane) (hx : x ∈ Set.range (D.edge e)) (hvertex : ∀ j, x ≠ D.vertex j) :
    x ∈ Paper170.edgeInterior D e := by
  obtain ⟨t,he⟩ := hx
  have ht0 : t ≠ 0 := by
    intro ht
    subst t
    exact hvertex _ (he.symm.trans (D.edge e).source)
  have ht1 : t ≠ 1 := by
    intro ht
    subst t
    exact hvertex _ (he.symm.trans (D.edge e).target)
  exact ⟨t,⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
    lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩,he⟩
theorem edgeInterior_not_vertex (D : Paper170.ContinuousDrawing graph) (e : Edge)
    (x : Plane) (hx : x ∈ Paper170.edgeInterior D e) (j : Vertex) : x ≠ D.vertex j := by
  obtain ⟨t,ht,he⟩ := hx
  exact fun hj => D.interior_avoids_vertices e t ht j (he.trans hj)
theorem crossing_of_ranges_not_vertices (D : Paper170.ContinuousDrawing graph) (e f : Edge)
    (hef : e ≠ f) (x : Plane) (he : x ∈ Set.range (D.edge e)) (hf : x ∈ Set.range (D.edge f))
    (hv : ∀ j, x ≠ D.vertex j) : x ∈ Paper170.crossingPoints D :=
  ⟨e,f,hef,edgeInterior_of_range_not_vertices D e x he hv,edgeInterior_of_range_not_vertices D f x hf hv⟩
end Paper170Geometry
end
end
section
namespace Paper170Geometry
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
theorem drawing_edge_vertex_parameter (D : Paper170.ContinuousDrawing graph) (e : Edge)
    (t : unitInterval) (v : Vertex) (he : D.edge e t=D.vertex v) :
    (t=0 ∧ v=(graph.src e)) ∨ (t=1 ∧ v=(graph.dst e)) := by
  by_cases ht0 : t=0
  · subst t
    exact Or.inl ⟨rfl,(D.vertex_injective ((D.edge e).source.symm.trans he)).symm⟩
  by_cases ht1 : t=1
  · subst t
    exact Or.inr ⟨rfl,(D.vertex_injective ((D.edge e).target.symm.trans he)).symm⟩
  exact False.elim (D.interior_avoids_vertices e t
    ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩ v he)
end Paper170Geometry
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
structure FiniteIntersectionDrawing (graph : Paper170.Graph Vertex Edge) extends Paper170.ContinuousDrawing graph where
  crossings_finite : (Paper170.crossingPoints toContinuousDrawing).Finite
  no_triples : ∀ e f g, e ≠ f → e ≠ g → f ≠ g →
    Paper170.edgeInterior toContinuousDrawing e ∩ Paper170.edgeInterior toContinuousDrawing f ∩
      Paper170.edgeInterior toContinuousDrawing g = ∅
abbrev toFiniteIntersectionDrawing  (D : Paper170.AdmissibleDrawing graph) :
    FiniteIntersectionDrawing graph where
  toContinuousDrawing := D.toContinuousDrawing
  crossings_finite := D.crossings_finite
  no_triples := D.no_triples
def finiteCrossingCount  (D : FiniteIntersectionDrawing graph) : ℕ :=
  D.crossings_finite.toFinset.card
theorem finiteCrossingCount_eq_ncard  (D : FiniteIntersectionDrawing graph) :
    finiteCrossingCount D=(Paper170.crossingPoints D.toContinuousDrawing).ncard :=
  (Set.ncard_eq_toFinset_card _ D.crossings_finite).symm
end Paper170Geometry
namespace Paper170.AdmissibleDrawing
abbrev toFiniteIntersectionDrawing {V E : Type} {G : Graph V E} (D : AdmissibleDrawing G) :
    Paper170Geometry.FiniteIntersectionDrawing G := Paper170Geometry.toFiniteIntersectionDrawing D
end Paper170.AdmissibleDrawing
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
open scoped BigOperators Classical
/-- A minimum exists once an actual admissible drawing has been constructed.
This is the well-ordering step; construction of a drawing remains a separate obligation. -/
theorem crossingCount_attainment (D₀ : Paper170.AdmissibleDrawing graph) :
    ∃ D : Paper170.AdmissibleDrawing graph, Paper170.crossingCount D = Paper170.ordinaryCrossingNumber graph := by
  exact csInf_mem (show (Set.range (@Paper170.crossingCount Vertex Edge graph)).Nonempty from
    ⟨Paper170.crossingCount D₀, D₀, rfl⟩)
theorem ordinaryCrossingNumber_le_count (D : Paper170.AdmissibleDrawing graph) :
    Paper170.ordinaryCrossingNumber graph ≤ Paper170.crossingCount D :=
  csInf_le' ⟨D, rfl⟩
theorem crossing_incident_iff (D : Paper170.AdmissibleDrawing graph) (x : Plane)
    (e f : Edge) (hef : e ≠ f)
    (he : x ∈ Paper170.edgeInterior D.toContinuousDrawing e)
    (hf : x ∈ Paper170.edgeInterior D.toContinuousDrawing f) (g : Edge) :
    x ∈ Paper170.edgeInterior D.toContinuousDrawing g ↔ g = e ∨ g = f := by
  constructor
  · intro hg
    by_contra hh
    have hge : e ≠ g := by tauto
    have hgf : f ≠ g := by tauto
    have hmem : x ∈ Paper170.edgeInterior D.toContinuousDrawing e ∩ Paper170.edgeInterior D.toContinuousDrawing f ∩
        Paper170.edgeInterior D.toContinuousDrawing g := ⟨⟨he,hf⟩,hg⟩
    rw [D.no_triples e f g hef hge hgf] at hmem
    exact hmem
  · rintro (rfl | rfl) <;> assumption
end Paper170Geometry
end
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
open scoped Classical
def det2 (u v : Plane) : ℝ := u.1*v.2-u.2*v.1
def segmentPoint (a b : Plane) (t : ℝ) : Plane := (1-t) • a+t • b
def openSegmentTrace (a b : Plane) : Set Plane := segmentPoint a b '' Set.Ioo 0 1
def SegmentsCrossProperly (a b c d : Plane) : Prop :=
  det2 (b-a) (d-c) ≠ 0 ∧
    ∃ t ∈ Set.Ioo (0 : ℝ) 1, ∃ u ∈ Set.Ioo (0 : ℝ) 1,
      segmentPoint a b t = segmentPoint c d u
@[simp] theorem segmentPoint_zero (a b : Plane) : segmentPoint a b 0 = a := by
  simp [segmentPoint]
@[simp] theorem segmentPoint_one (a b : Plane) : segmentPoint a b 1 = b := by
  simp [segmentPoint]
theorem segment_intersection_parameters_unique (a b c d : Plane)
    (hn : det2 (b-a) (d-c) ≠ 0) (t u t' u' : ℝ)
    (h : segmentPoint a b t = segmentPoint c d u)
    (h' : segmentPoint a b t' = segmentPoint c d u') : t = t' ∧ u = u' := by
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  have h₁' := congrArg Prod.fst h'
  have h₂' := congrArg Prod.snd h'
  change (1-t)*a.1+t*b.1 = (1-u)*c.1+u*d.1 at h₁
  change (1-t)*a.2+t*b.2 = (1-u)*c.2+u*d.2 at h₂
  change (1-t')*a.1+t'*b.1 = (1-u')*c.1+u'*d.1 at h₁'
  change (1-t')*a.2+t'*b.2 = (1-u')*c.2+u'*d.2 at h₂'
  have ht : (t-t') * det2 (b-a) (d-c) = 0 := by
    dsimp [det2]
    linear_combination (d.2-c.2)*h₁ - (d.1-c.1)*h₂ - (d.2-c.2)*h₁' + (d.1-c.1)*h₂'
  have hu : (u-u') * det2 (b-a) (d-c) = 0 := by
    dsimp [det2]
    linear_combination (b.2-a.2)*h₁ - (b.1-a.1)*h₂ - (b.2-a.2)*h₁' + (b.1-a.1)*h₂'
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp ht).resolve_right hn),
    sub_eq_zero.mp ((mul_eq_zero.mp hu).resolve_right hn)⟩
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
open Polynomial
open scoped BigOperators Classical
def lineAvoidancePolynomial (z a v : Plane) : ℝ[X] :=
  C v.2 * X - C v.1 * X^2 + C (det2 (z-a) v)
theorem lineAvoidancePolynomial_eval (z a v : Plane) (t : ℝ) :
    (lineAvoidancePolynomial z a v).eval t = det2 (z+(t,t^2)-a) v := by
  simp [lineAvoidancePolynomial,det2]
  ring
theorem lineAvoidancePolynomial_ne_zero (z a v : Plane) (hv : v ≠ 0) :
    lineAvoidancePolynomial z a v ≠ 0 := by
  intro h
  have h₁ := congrArg (fun p : ℝ[X] => p.coeff 1) h
  have h₂ := congrArg (fun p : ℝ[X] => p.coeff 2) h
  norm_num [lineAvoidancePolynomial,coeff_C_mul] at h₁ h₂
  apply hv
  exact Prod.ext h₂ h₁
theorem exists_near_avoiding_lines {ι : Type*} [Fintype ι] (a v : ι → Plane)
    (hv : ∀ i, v i ≠ 0) (z : Plane) (ε : ℝ) (hε : 0 < ε) :
    ∃ o : Plane, dist o z < ε ∧ ∀ i, det2 (o-a i) (v i) ≠ 0 := by
  let bad : Finset ℝ := Finset.univ.biUnion (fun i => (lineAvoidancePolynomial z (a i) (v i)).roots.toFinset)
  have hδ : 0 < min ε 1 := lt_min hε (by norm_num)
  obtain ⟨t,ht⟩ := ((Set.Ioo_infinite hδ).sdiff bad.finite_toSet).nonempty
  have ht0 : 0 < t := ht.1.1
  have htε : t < ε := lt_of_lt_of_le ht.1.2 (min_le_left _ _)
  have ht1 : t < 1 := lt_of_lt_of_le ht.1.2 (min_le_right _ _)
  refine ⟨z+(t,t^2),?_,?_⟩
  · have ht2 : t^2 < ε := by nlinarith
    simp only [Prod.dist_eq,Prod.fst_add,Prod.snd_add,Real.dist_eq,add_sub_cancel_left]
    exact max_lt (by simpa [abs_of_pos ht0] using htε) (by simpa [abs_of_nonneg (sq_nonneg t)] using ht2)
  · intro i hi
    have hp : (lineAvoidancePolynomial z (a i) (v i)).eval t = 0 := by
      rwa [lineAvoidancePolynomial_eval]
    apply ht.2
    change t ∈ bad
    apply Finset.mem_biUnion.mpr
    refine ⟨i,Finset.mem_univ i,?_⟩
    simpa [mem_roots (lineAvoidancePolynomial_ne_zero z (a i) (v i) (hv i))] using hp
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
def orient2 (a b c : Plane) : ℝ := det2 (b-a) (c-a)
theorem orient2_self_segment (a b : Plane) (t : ℝ) : orient2 a b (segmentPoint a b t) = 0 := by
  dsimp [orient2, det2, segmentPoint]
  ring
theorem orient2_segment (a b c d : Plane) (u : ℝ) :
    orient2 a b (segmentPoint c d u) = (1-u)*orient2 a b c+u*orient2 a b d := by
  dsimp [orient2,det2,segmentPoint]
  ring
theorem orient2_difference (a b c d : Plane) :
    orient2 a b d-orient2 a b c = det2 (b-a) (d-c) := by
  dsimp [orient2,det2]
  ring
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
open scoped Topology Classical
def SegmentPairTransverse (a b c d : Plane) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ Set.Icc (0 : ℝ) 1,
    segmentPoint a b t = segmentPoint c d u →
      det2 (b-a) (d-c) ≠ 0 ∧ t ∈ Set.Ioo (0 : ℝ) 1 ∧ u ∈ Set.Ioo (0 : ℝ) 1
end Zarankiewicz
end
end OAI
end
section
namespace OAI
namespace Zarankiewicz
theorem finite_positive_lower_bound {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 < f i) : ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ S, ε < f i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert i S hi ih =>
    obtain ⟨ε,hε,hbound⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hfi := hf i (Finset.mem_insert_self i S)
    refine ⟨min (ε/2) (f i/2),lt_min (by linarith) (by linarith),?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (min_le_right _ _).trans_lt (by linarith)
    · exact (min_le_left _ _).trans_lt (by have hh := hbound j hj; linarith)
theorem finite_node_separation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (node : ι → ℝ) (hn : Function.Injective node) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i j, i ≠ j → ε < |node i-node j| := by
  obtain ⟨ε,hε,hb⟩ := finite_positive_lower_bound
    (Finset.univ.filter (fun ij : ι × ι => ij.1 ≠ ij.2))
    (fun ij => |node ij.1-node ij.2|) (by
      intro ij hij
      exact abs_pos.mpr (sub_ne_zero.mpr (hn.ne (Finset.mem_filter.mp hij).2)))
  exact ⟨ε,hε,fun i j hij => hb (i,j) (by simpa using hij)⟩
end Zarankiewicz
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
namespace Zarankiewicz
def intervalSegment (a b t : unitInterval) : unitInterval :=
  ⟨(1-t.val)*a.val+t.val*b.val,by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) a.property.1)
        (mul_nonneg t.property.1 b.property.1)
    · have h₀ := mul_le_mul_of_nonneg_left a.property.2 (sub_nonneg.mpr t.property.2)
      have h₁ := mul_le_mul_of_nonneg_left b.property.2 t.property.1
      linarith⟩
theorem intervalSegment_between (a b t : unitInterval) (hab : a ≤ b) :
    a ≤ intervalSegment a b t ∧ intervalSegment a b t ≤ b := by
  have hab' : a.val ≤ b.val := hab
  have h₀ := mul_nonneg t.property.1 (sub_nonneg.mpr hab')
  have h₁ := mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr hab')
  change a.val ≤ (1-t.val)*a.val+t.val*b.val ∧ (1-t.val)*a.val+t.val*b.val ≤ b.val
  constructor <;> nlinarith
end Zarankiewicz
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem intervalSegment_surjective_interval (a b : unitInterval) (hab : a < b)
    (t : unitInterval) (ht : a ≤ t ∧ t ≤ b) : ∃ u : unitInterval, intervalSegment a b u=t := by
  have hd : 0 < b.val-a.val := sub_pos.mpr hab
  have ht0 : 0 ≤ (t.val-a.val)/(b.val-a.val) := div_nonneg (sub_nonneg.mpr ht.1) hd.le
  have ht1 : (t.val-a.val)/(b.val-a.val) ≤ 1 :=
    (div_le_one hd).mpr (sub_le_sub_right (show t.val ≤ b.val from ht.2) a.val)
  refine ⟨⟨(t.val-a.val)/(b.val-a.val),ht0,ht1⟩,?_⟩
  apply Subtype.ext
  change (1-(t.val-a.val)/(b.val-a.val))*a.val+((t.val-a.val)/(b.val-a.val))*b.val=t.val
  field_simp
  ring
def pathSubarc {a b : Plane} (γ : Path a b) (u v : unitInterval) : Path (γ u) (γ v) where
  toFun := fun t => γ (intervalSegment u v t)
  continuous_toFun := by
    apply γ.continuous.comp
    unfold intervalSegment
    fun_prop
  source' := by simp [intervalSegment]
  target' := by simp [intervalSegment]
theorem pathSubarc_range {a b : Plane} (γ : Path a b) (u v : unitInterval) (huv : u < v) :
    Set.range (pathSubarc γ u v)=γ '' Set.Icc u v := by
  apply Set.Subset.antisymm
  · rintro x ⟨t,rfl⟩
    exact ⟨intervalSegment u v t,intervalSegment_between u v t huv.le,rfl⟩
  · rintro x ⟨t,ht,rfl⟩
    obtain ⟨s,hs⟩ := intervalSegment_surjective_interval u v huv t ht
    exact ⟨s,congrArg γ hs⟩
end Zarankiewicz
end
end OAI
end
section
namespace OAI
namespace Zarankiewicz
theorem intervalSegment_strict_between (a b t : unitInterval) (hab : a < b)
    (ht : t ∈ Set.Ioo (0 : unitInterval) 1) :
    a < intervalSegment a b t ∧ intervalSegment a b t < b := by
  have hab' : a.val < b.val := hab
  have ht0 : 0 < t.val := ht.1
  have ht1 : t.val < 1 := ht.2
  have h₀ := mul_pos ht0 (sub_pos.mpr hab')
  have h₁ := mul_pos (sub_pos.mpr ht1) (sub_pos.mpr hab')
  change a.val < (1-t.val)*a.val+t.val*b.val ∧ (1-t.val)*a.val+t.val*b.val < b.val
  constructor <;> nlinarith
end Zarankiewicz
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
def intervalLeft (t : unitInterval) : unitInterval := ⟨t.val/2,by constructor <;> linarith [t.property.1,t.property.2]⟩
def intervalRight (t : unitInterval) : unitInterval := ⟨(1+t.val)/2,by constructor <;> linarith [t.property.1,t.property.2]⟩
theorem intervalLeft_strictMono : StrictMono intervalLeft := by
  intro s t hst
  change s.val/2 < t.val/2
  exact div_lt_div_of_pos_right hst (by norm_num)
theorem intervalRight_strictMono : StrictMono intervalRight := by
  intro s t hst
  change (1+s.val)/2 < (1+t.val)/2
  have hh : s.val < t.val := hst
  linarith
theorem intervalSegment_left (a b t : unitInterval) :
    intervalSegment (intervalLeft a) (intervalLeft b) t=intervalLeft (intervalSegment a b t) := by
  apply Subtype.ext
  change (1-t.val)*(a.val/2)+t.val*(b.val/2)=((1-t.val)*a.val+t.val*b.val)/2
  ring
theorem intervalSegment_right (a b t : unitInterval) :
    intervalSegment (intervalRight a) (intervalRight b) t=intervalRight (intervalSegment a b t) := by
  apply Subtype.ext
  change (1-t.val)*((1+a.val)/2)+t.val*((1+b.val)/2)=(1+((1-t.val)*a.val+t.val*b.val))/2
  ring
theorem path_trans_intervalLeft {a b c : Plane} (γ : Path a b) (η : Path b c) (t : unitInterval) :
    (γ.trans η) (intervalLeft t)=γ t := by
  rw [← (γ.trans η).extend_extends' (intervalLeft t)]
  rw [Path.extend_trans_of_le_half γ η (show (intervalLeft t).val ≤ 1/2 by
    change t.val/2 ≤ 1/2
    linarith [t.property.2])]
  have he : 2*(intervalLeft t).val=t.val := by change 2*(t.val/2)=t.val; ring
  rw [he,γ.extend_extends']
theorem path_trans_intervalRight {a b c : Plane} (γ : Path a b) (η : Path b c) (t : unitInterval) :
    (γ.trans η) (intervalRight t)=η t := by
  rw [← (γ.trans η).extend_extends' (intervalRight t)]
  rw [Path.extend_trans_of_half_le γ η (show 1/2 ≤ (intervalRight t).val by
    change 1/2 ≤ (1+t.val)/2
    linarith [t.property.1])]
  have he : 2*(intervalRight t).val-1=t.val := by change 2*((1+t.val)/2)-1=t.val; ring
  rw [he,η.extend_extends']
theorem intervalSegment_zero_one (t : unitInterval) : intervalSegment 0 1 t=t := by
  apply Subtype.ext
  change (1-t.val)*0+t.val*1=t.val
  ring
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
open scoped Topology
def SegmentReach (O : Set Plane) (a b : Plane) : Prop :=
  Relation.ReflTransGen (fun x y => segment ℝ x y ⊆ O) a b
theorem segmentReach_mem {O : Set Plane} {a b : Plane} (ha : a ∈ O) (h : SegmentReach O a b) : b ∈ O := by
  induction h with
  | refl => exact ha
  | @tail b c hab hbc ih => exact hbc (right_mem_segment ℝ b c)
theorem isOpen_segmentReach (O : Set Plane) (hO : IsOpen O) (a : Plane) (ha : a ∈ O) :
    IsOpen {b | SegmentReach O a b} := by
  apply Metric.isOpen_iff.mpr
  intro b hb
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds (segmentReach_mem ha hb))
  refine ⟨ε,hε,?_⟩
  intro c hc
  apply Relation.ReflTransGen.tail hb
  exact ((convex_ball b ε).segment_subset (Metric.mem_ball_self hε) hc).trans hball
theorem isOpen_non_segmentReach (O : Set Plane) (hO : IsOpen O) (a : Plane) :
    IsOpen (O \ {b | SegmentReach O a b}) := by
  apply Metric.isOpen_iff.mpr
  intro b hb
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hb.1)
  refine ⟨ε,hε,?_⟩
  intro c hc
  refine ⟨hball hc,?_⟩
  intro hreach
  apply hb.2
  apply Relation.ReflTransGen.tail hreach
  exact ((convex_ball b ε).segment_subset hc (Metric.mem_ball_self hε)).trans hball
theorem segmentReach_of_path {a b : Plane} (γ : Path a b) (O : Set Plane)
    (hO : IsOpen O) (hγ : ∀ t, γ t ∈ O) : SegmentReach O a b := by
  have ha : a ∈ O := by simpa using hγ 0
  let A : Set unitInterval := {t | SegmentReach O a (γ t)}
  have hopen : IsOpen A := (isOpen_segmentReach O hO a ha).preimage γ.continuous
  have hcomp : IsOpen Aᶜ := by
    have heq : Aᶜ = γ ⁻¹' (O \ {x | SegmentReach O a x}) := by
      ext t
      simp only [A,Set.mem_compl_iff,Set.mem_ofPred_eq,Set.mem_preimage,Set.mem_sdiff,hγ t,true_and]
    rw [heq]
    exact (isOpen_non_segmentReach O hO a).preimage γ.continuous
  have hall : A=Set.univ := (show IsClopen A from ⟨by simpa using hcomp.isClosed_compl,hopen⟩).eq_univ ⟨0,by
    change SegmentReach O a (γ 0)
    rw [γ.source]
    exact Relation.ReflTransGen.refl⟩
  have hb : (1 : unitInterval) ∈ A := by rw [hall]; trivial
  change SegmentReach O a (γ 1) at hb
  rwa [γ.target] at hb
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
def polygonalArcPath (v : ℕ → Plane) : (n : ℕ) → Path (v 0) (v n)
  | 0 => Path.refl (v 0)
  | 1 => Path.segment (v 0) (v 1)
  | n+2 => (polygonalArcPath v (n+1)).trans (Path.segment (v (n+1)) (v (n+2)))
structure PolygonalChain (O : Set Plane) (a b : Plane) where
  pieces : ℕ
  vertices : ℕ → Plane
  first : vertices 0=a
  last : vertices pieces=b
  start_mem : a ∈ O
  inside : ∀ i, i < pieces → segment ℝ (vertices i) (vertices (i+1)) ⊆ O
namespace PolygonalChain
variable {O : Set Plane} {a b : Plane}
def point (O : Set Plane) (a : Plane) (ha : a ∈ O) : PolygonalChain O a a where
  pieces := 0
  vertices := fun _ => a
  first := rfl
  last := rfl
  start_mem := ha
  inside := by intro i hi; omega
def append (P : PolygonalChain O a b) (c : Plane) (h : segment ℝ b c ⊆ O) : PolygonalChain O a c where
  pieces := P.pieces+1
  vertices := fun i => if i ≤ P.pieces then P.vertices i else c
  first := by simp [P.first]
  last := by simp
  start_mem := P.start_mem
  inside := by
    intro i hi
    by_cases hin : i < P.pieces
    · simpa only [if_pos (show i ≤ P.pieces by omega),if_pos (show i+1 ≤ P.pieces by omega)] using P.inside i hin
    · have he : i=P.pieces := by omega
      subst i
      simpa [P.last] using h
def path (P : PolygonalChain O a b) : Path a b :=
  (polygonalArcPath P.vertices P.pieces).cast P.first.symm P.last.symm
end PolygonalChain
theorem nonempty_polygonalChain_of_reach {O : Set Plane} {a b : Plane}
    (ha : a ∈ O) (h : SegmentReach O a b) : Nonempty (PolygonalChain O a b) := by
  induction h with
  | refl => exact ⟨PolygonalChain.point O a ha⟩
  | @tail b c hab hbc ih =>
    obtain ⟨P⟩ := ih
    exact ⟨P.append c hbc⟩
theorem nonempty_polygonalChain_of_path {a b : Plane} (γ : Path a b) (O : Set Plane)
    (hO : IsOpen O) (hγ : ∀ t, γ t ∈ O) : Nonempty (PolygonalChain O a b) := by
  exact nonempty_polygonalChain_of_reach (by simpa using hγ 0) (segmentReach_of_path γ O hO hγ)
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
def HasFiniteAffineCover {a b : Plane} (γ : Path a b) : Prop :=
  ∃ S : Finset (unitInterval × unitInterval),
    (∀ ab ∈ S, ab.1 < ab.2) ∧
    (∀ t : unitInterval, ∃ ab ∈ S, ab.1 ≤ t ∧ t ≤ ab.2) ∧
    (∀ ab ∈ S, ∀ t : unitInterval,
      γ (intervalSegment ab.1 ab.2 t)=segmentPoint (γ ab.1) (γ ab.2) t.val)
theorem hasFiniteAffineCover_refl (a : Plane) : HasFiniteAffineCover (Path.refl a) := by
  classical
  refine ⟨{(0,1)},?_,?_,?_⟩
  · intro ab hab
    have he : ab=(0,1) := Finset.mem_singleton.mp hab
    subst ab
    norm_num
  · intro t
    exact ⟨(0,1),Finset.mem_singleton_self _,t.property.1,t.property.2⟩
  · intro ab hab t
    change a=segmentPoint a a t.val
    simp [segmentPoint,← add_smul]
theorem hasFiniteAffineCover_segment (a b : Plane) : HasFiniteAffineCover (Path.segment a b) := by
  classical
  refine ⟨{(0,1)},?_,?_,?_⟩
  · intro ab hab
    have he : ab=(0,1) := Finset.mem_singleton.mp hab
    subst ab
    norm_num
  · intro t
    exact ⟨(0,1),Finset.mem_singleton_self _,t.property.1,t.property.2⟩
  · intro ab hab t
    have he : ab=(0,1) := Finset.mem_singleton.mp hab
    subst ab
    simp only [intervalSegment_zero_one,Path.source,Path.target]
    simp only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint]
theorem HasFiniteAffineCover.trans {a b c : Plane} {γ : Path a b} {η : Path b c}
    (hγ : HasFiniteAffineCover γ) (hη : HasFiniteAffineCover η) : HasFiniteAffineCover (γ.trans η) := by
  classical
  obtain ⟨S,hSlt,hScov,hSaff⟩ := hγ
  obtain ⟨T,hTlt,hTcov,hTaff⟩ := hη
  let L : unitInterval × unitInterval → unitInterval × unitInterval := fun ab => (intervalLeft ab.1,intervalLeft ab.2)
  let R : unitInterval × unitInterval → unitInterval × unitInterval := fun ab => (intervalRight ab.1,intervalRight ab.2)
  refine ⟨S.image L ∪ T.image R,?_,?_,?_⟩
  · intro ab hab
    rcases Finset.mem_union.mp hab with hab | hab
    · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
      exact intervalLeft_strictMono (hSlt cd hcd)
    · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
      exact intervalRight_strictMono (hTlt cd hcd)
  · intro t
    by_cases ht : t.val ≤ 1/2
    · let u : unitInterval := ⟨2*t.val,by constructor <;> linarith [t.property.1]⟩
      obtain ⟨ab,hab,ha,hb⟩ := hScov u
      have hu : intervalLeft u=t := by apply Subtype.ext; change (2*t.val)/2=t.val; ring
      refine ⟨L ab,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩),?_,?_⟩
      · change intervalLeft ab.1 ≤ t
        rw [← hu]
        exact intervalLeft_strictMono.monotone ha
      · change t ≤ intervalLeft ab.2
        rw [← hu]
        exact intervalLeft_strictMono.monotone hb
    · let u : unitInterval := ⟨2*t.val-1,by constructor <;> linarith [t.property.2]⟩
      obtain ⟨ab,hab,ha,hb⟩ := hTcov u
      have hu : intervalRight u=t := by apply Subtype.ext; change (1+(2*t.val-1))/2=t.val; ring
      refine ⟨R ab,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩),?_,?_⟩
      · change intervalRight ab.1 ≤ t
        rw [← hu]
        exact intervalRight_strictMono.monotone ha
      · change t ≤ intervalRight ab.2
        rw [← hu]
        exact intervalRight_strictMono.monotone hb
  · intro ab hab t
    rcases Finset.mem_union.mp hab with hab | hab
    · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
      change (γ.trans η) (intervalSegment (intervalLeft cd.1) (intervalLeft cd.2) t)=_
      rw [intervalSegment_left,path_trans_intervalLeft]
      exact (hSaff cd hcd t).trans (by simp only [L,path_trans_intervalLeft])
    · obtain ⟨cd,hcd,rfl⟩ := Finset.mem_image.mp hab
      change (γ.trans η) (intervalSegment (intervalRight cd.1) (intervalRight cd.2) t)=_
      rw [intervalSegment_right,path_trans_intervalRight]
      exact (hTaff cd hcd t).trans (by simp only [R,path_trans_intervalRight])
theorem HasFiniteAffineCover.cast {a b c d : Plane} {γ : Path a b}
    (hγ : HasFiniteAffineCover γ) (ha : c=a) (hb : d=b) : HasFiniteAffineCover (γ.cast ha hb) := hγ
theorem polygonalArcPath_hasFiniteAffineCover (v : ℕ → Plane) :
    (k : ℕ) → HasFiniteAffineCover (polygonalArcPath v k)
  | 0 => hasFiniteAffineCover_refl _
  | 1 => hasFiniteAffineCover_segment _ _
  | k+2 => (polygonalArcPath_hasFiniteAffineCover v (k+1)).trans (hasFiniteAffineCover_segment _ _)
theorem PolygonalChain.hasFiniteAffineCover {O : Set Plane} {a b : Plane}
    (P : PolygonalChain O a b) : HasFiniteAffineCover P.path :=
  (polygonalArcPath_hasFiniteAffineCover P.vertices P.pieces).cast P.first.symm P.last.symm
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem intervalSegment_interpolate (a b u v t : unitInterval) :
    intervalSegment (intervalSegment a b u) (intervalSegment a b v) t=
      intervalSegment a b (intervalSegment u v t) := by
  apply Subtype.ext
  dsimp [intervalSegment]
  ring
theorem segmentPoint_interpolate (a b : Plane) (u v t : ℝ) :
    segmentPoint (segmentPoint a b u) (segmentPoint a b v) t=
      segmentPoint a b ((1-t)*u+t*v) := by
  ext <;> dsimp [segmentPoint] <;> ring
theorem path_affine_restrict {a b : Plane} (γ : Path a b) (l r : unitInterval) (hlr : l < r)
    (haff : ∀ t : unitInterval, γ (intervalSegment l r t)=segmentPoint (γ l) (γ r) t.val)
    (u v : unitInterval) (hu : l ≤ u ∧ u ≤ r) (hv : l ≤ v ∧ v ≤ r) (t : unitInterval) :
    γ (intervalSegment u v t)=segmentPoint (γ u) (γ v) t.val := by
  obtain ⟨u',rfl⟩ := intervalSegment_surjective_interval l r hlr u hu
  obtain ⟨v',rfl⟩ := intervalSegment_surjective_interval l r hlr v hv
  rw [intervalSegment_interpolate,haff,haff,haff,segmentPoint_interpolate]
  rfl
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem exists_sorted_unitInterval_finset (S : Finset unitInterval)
    (h0 : (0 : unitInterval) ∈ S) (h1 : (1 : unitInterval) ∈ S) :
    ∃ k : ℕ, 0 < k ∧ ∃ t : Fin (k+1) → unitInterval,
      StrictMono t ∧ t 0=0 ∧ t (Fin.last k)=1 ∧ Set.range t=(S : Set unitInterval) := by
  have hc : 1 < S.card := Finset.one_lt_card.mpr ⟨0,h0,1,h1,zero_ne_one⟩
  let k := S.card-1
  have hk : 0 < k := by dsimp [k]; omega
  have hcard : S.card=k+1 := by dsimp [k]; omega
  let e := S.orderEmbOfFin hcard
  have hrange : Set.range e=(S : Set unitInterval) := Finset.range_orderEmbOfFin S hcard
  obtain ⟨i,hi⟩ : ∃ i, e i=0 := by
    have hm : (0 : unitInterval) ∈ Set.range e := hrange.symm ▸ h0
    exact hm
  obtain ⟨j,hj⟩ : ∃ j, e j=1 := by
    have hm : (1 : unitInterval) ∈ Set.range e := hrange.symm ▸ h1
    exact hm
  have he0 : e 0=0 := by
    apply le_antisymm
    · exact (e.monotone (Fin.zero_le i)).trans_eq hi
    · exact (e 0).property.1
  have he1 : e (Fin.last k)=1 := by
    apply le_antisymm
    · exact (e (Fin.last k)).property.2
    · exact hj.symm.trans_le (e.monotone (Fin.le_last j))
  exact ⟨k,hk,e,e.strictMono,he0,he1,hrange⟩
end Zarankiewicz
end
end OAI
end
section
namespace OAI
namespace Zarankiewicz
@[simp] theorem det2_zero_left (u : Plane) : det2 0 u = 0 := by simp [det2]
@[simp] theorem det2_zero_right (u : Plane) : det2 u 0 = 0 := by simp [det2]
end Zarankiewicz
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
def rotateQuarter (v : Plane) : Plane := (-v.2,v.1)
def squaredLength (v : Plane) : ℝ := v.1^2+v.2^2
theorem squaredLength_pos (v : Plane) (hv : v ≠ 0) : 0 < squaredLength v := by
  have hx := sq_nonneg v.1
  have hy := sq_nonneg v.2
  have hnon : 0 ≤ squaredLength v := by dsimp [squaredLength]; linarith
  rcases eq_or_lt_of_le hnon with hzero | hpos
  · have h₁ : v.1=0 := by dsimp [squaredLength] at hzero; nlinarith
    have h₂ : v.2=0 := by dsimp [squaredLength] at hzero; nlinarith
    exact False.elim (hv (Prod.ext h₁ h₂))
  · exact hpos
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
open scoped Topology
def dot2 (u v : Plane) : ℝ := u.1*v.1+u.2*v.2
theorem planar_vector_decomposition (u v : Plane) :
    squaredLength u • v = dot2 u v • u+det2 u v • rotateQuarter u := by
  apply Prod.ext <;> dsimp [squaredLength,dot2,det2,rotateQuarter] <;> ring
theorem vector_parallel_of_det_zero (u v : Plane) (hu : u ≠ 0) (h : det2 u v=0) :
    v = (dot2 u v/squaredLength u) • u := by
  have hs := ne_of_gt (squaredLength_pos u hu)
  have hh := planar_vector_decomposition u v
  rw [h,zero_smul,add_zero] at hh
  calc
    v = (squaredLength u)⁻¹ • (squaredLength u • v) := by rw [smul_smul,inv_mul_cancel₀ hs,one_smul]
    _ = (squaredLength u)⁻¹ • (dot2 u v • u) := by rw [hh]
    _ = _ := by rw [smul_smul,div_eq_mul_inv,mul_comm]
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
structure PolygonalParametrization {a b : Plane} (γ : Path a b) where
  pieces : ℕ
  knot : Fin (pieces+1) → unitInterval
  increasing : StrictMono knot
  first : knot 0=0
  last : knot (Fin.last pieces)=1
  affine : ∀ i : Fin pieces, ∀ t : unitInterval,
    γ (intervalSegment (knot i.castSucc) (knot i.succ) t) =
      segmentPoint (γ (knot i.castSucc)) (γ (knot i.succ)) t.val
namespace PolygonalParametrization
variable {a b : Plane} {γ : Path a b}
def vertices (P : PolygonalParametrization γ) (i : ℕ) : Plane :=
  γ (P.knot ⟨min i P.pieces,Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩)
theorem vertices_at (P : PolygonalParametrization γ) (i : Fin (P.pieces+1)) :
    P.vertices i.val=γ (P.knot i) := by
  unfold vertices
  congr 2
  apply Fin.ext
  exact Nat.min_eq_left (Nat.le_of_lt_succ i.isLt)
theorem vertices_first (P : PolygonalParametrization γ) : P.vertices 0=a := by
  have he := P.vertices_at (0 : Fin (P.pieces+1))
  rw [P.first] at he
  simpa using he.trans γ.source
theorem vertices_last (P : PolygonalParametrization γ) : P.vertices P.pieces=b := by
  have he := P.vertices_at (Fin.last P.pieces)
  rw [P.last] at he
  simpa using he.trans γ.target
end PolygonalParametrization
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem strictMono_no_between_successors {k : ℕ} (t : Fin (k+1) → unitInterval)
    (ht : StrictMono t) (i : Fin k) (j : Fin (k+1)) :
    ¬ (t i.castSucc < t j ∧ t j < t i.succ) := by
  intro h
  have hlo : i.castSucc < j := by
    by_contra hn
    exact h.1.not_ge (ht.monotone (le_of_not_gt hn))
  have hhi : j < i.succ := by
    by_contra hn
    exact h.2.not_ge (ht.monotone (le_of_not_gt hn))
  change i.val < j.val at hlo
  change j.val < i.val+1 at hhi
  omega
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem polygonalArcPath_range_subset (v : ℕ → Plane) (O : Set Plane) (h0 : v 0 ∈ O) :
    (n : ℕ) → (∀ i, i < n → segment ℝ (v i) (v (i+1)) ⊆ O) →
      Set.range (polygonalArcPath v n) ⊆ O
  | 0, _ => by rintro x ⟨t,rfl⟩; exact h0
  | 1, h => by
    rw [polygonalArcPath,Path.range_segment]
    exact h 0 (by omega)
  | n+2, h => by
    rw [polygonalArcPath,Path.trans_range,Set.union_subset_iff]
    refine ⟨polygonalArcPath_range_subset v O h0 (n+1) (fun i hi => h i (by omega)),?_⟩
    rw [Path.range_segment]
    exact h (n+1) (by omega)
namespace PolygonalChain
variable {O : Set Plane} {a b : Plane}
theorem path_range_subset (P : PolygonalChain O a b) : Set.range P.path ⊆ O := by
  change Set.range (polygonalArcPath P.vertices P.pieces) ⊆ O
  exact polygonalArcPath_range_subset P.vertices O (by rw [P.first]; exact P.start_mem) P.pieces P.inside
end PolygonalChain
theorem exists_minimum_polygonalChain {O : Set Plane} {a b : Plane}
    (h : Nonempty (PolygonalChain O a b)) :
    ∃ P : PolygonalChain O a b, ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces := by
  classical
  obtain ⟨P⟩ := h
  have hex : ∃ n : ℕ, ∃ Q : PolygonalChain O a b, Q.pieces=n := ⟨P.pieces,P,rfl⟩
  obtain ⟨Q,hQ⟩ := Nat.find_spec hex
  refine ⟨Q,?_⟩
  intro R
  rw [hQ]
  exact Nat.find_min' hex ⟨R,rfl⟩
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
open scoped BigOperators
def joinedSequence (v w : ℕ → Plane) (n : ℕ) (i : ℕ) : Plane :=
  if i<n then v i else w (i-n)
theorem joinedSequence_left (v w : ℕ → Plane) (n : ℕ) (h : v n=w 0)
    (i : ℕ) (hi : i≤n) : joinedSequence v w n i=v i := by
  unfold joinedSequence
  by_cases hin : i<n
  · rw [if_pos hin]
  · have he : i=n := by omega
    subst i
    simp [h]
theorem joinedSequence_right (v w : ℕ → Plane) (n j : ℕ) :
    joinedSequence v w n (n+j)=w j := by
  simp [joinedSequence,show ¬ n+j<n by omega]
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.PolygonalChain
variable {O : Set Plane} {a b c : Plane}
theorem vertex_mem (P : PolygonalChain O a b) (i : ℕ) (hi : i ≤ P.pieces) : P.vertices i ∈ O := by
  by_cases h0 : i=0
  · subst i
    rw [P.first]
    exact P.start_mem
  · have hp : 0 < i := by omega
    have hh := P.inside (i-1) (by omega) (right_mem_segment ℝ (P.vertices (i-1)) (P.vertices (i-1+1)))
    simpa [Nat.sub_add_cancel (show 1 ≤ i by omega)] using hh
def single (O : Set Plane) (a b : Plane) (ha : a ∈ O) (h : segment ℝ a b ⊆ O) : PolygonalChain O a b where
  pieces := 1
  vertices := fun i => if i=0 then a else b
  first := by simp
  last := by simp
  start_mem := ha
  inside := by
    intro i hi
    have he : i = 0 := by omega
    subst i
    simpa using h
def take (P : PolygonalChain O a b) (k : ℕ) (hk : k ≤ P.pieces) : PolygonalChain O a (P.vertices k) where
  pieces := k
  vertices := P.vertices
  first := P.first
  last := rfl
  start_mem := P.start_mem
  inside := fun i hi => P.inside i (by omega)
def drop (P : PolygonalChain O a b) (k : ℕ) (hk : k ≤ P.pieces) : PolygonalChain O (P.vertices k) b where
  pieces := P.pieces-k
  vertices := fun i => P.vertices (k+i)
  first := by simp
  last := by simpa [Nat.add_sub_of_le hk] using P.last
  start_mem := P.vertex_mem k hk
  inside := by
    intro i hi
    simpa [Nat.add_assoc] using P.inside (k+i) (by omega)
def join (P : PolygonalChain O a b) (Q : PolygonalChain O b c) : PolygonalChain O a c where
  pieces := P.pieces+Q.pieces
  vertices := joinedSequence P.vertices Q.vertices P.pieces
  first := (joinedSequence_left _ _ _ (P.last.trans Q.first.symm) 0 (Nat.zero_le _)).trans P.first
  last := (joinedSequence_right _ _ P.pieces Q.pieces).trans Q.last
  start_mem := P.start_mem
  inside := by
    intro i hi
    have hglue : P.vertices P.pieces=Q.vertices 0 := P.last.trans Q.first.symm
    by_cases hin : i < P.pieces
    · rw [joinedSequence_left _ _ _ hglue i (by omega),joinedSequence_left _ _ _ hglue (i+1) (by omega)]
      exact P.inside i hin
    · have hbase : i=P.pieces+(i-P.pieces) := by omega
      have hnext : i+1=P.pieces+((i-P.pieces)+1) := by omega
      have h₀ : joinedSequence P.vertices Q.vertices P.pieces i = Q.vertices (i-P.pieces) := by
        conv_lhs => rw [hbase]
        exact joinedSequence_right _ _ _ _
      have h₁ : joinedSequence P.vertices Q.vertices P.pieces (i+1) = Q.vertices ((i-P.pieces)+1) := by
        rw [hnext, joinedSequence_right]
      rw [h₀,h₁]
      exact Q.inside (i-P.pieces) (by omega)
@[simp] theorem pieces_single (ha : a ∈ O) (h : segment ℝ a b ⊆ O) : (single O a b ha h).pieces=1 := rfl
@[simp] theorem pieces_take (P : PolygonalChain O a b) (k : ℕ) (hk : k ≤ P.pieces) : (P.take k hk).pieces=k := rfl
@[simp] theorem pieces_drop (P : PolygonalChain O a b) (k : ℕ) (hk : k ≤ P.pieces) : (P.drop k hk).pieces=P.pieces-k := rfl
@[simp] theorem pieces_join (P : PolygonalChain O a b) (Q : PolygonalChain O b c) : (P.join Q).pieces=P.pieces+Q.pieces := rfl
end Zarankiewicz.PolygonalChain
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.PolygonalChain
variable {O : Set Plane} {a b : Plane}
def withEndpoints (P : PolygonalChain O a b) {a' b' : Plane}
    (ha : a'=a) (hb : b'=b) : PolygonalChain O a' b' where
  pieces := P.pieces
  vertices := P.vertices
  first := P.first.trans ha.symm
  last := P.last.trans hb.symm
  start_mem := ha.symm ▸ P.start_mem
  inside := P.inside
theorem minimum_shortcut_bound (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ P.pieces)
    (Q : PolygonalChain O (P.vertices i) (P.vertices j)) : j-i ≤ Q.pieces := by
  have hh := hmin (((P.take i (by omega)).join Q).join (P.drop j hj))
  simp only [pieces_join,pieces_take,pieces_drop] at hh
  omega
theorem minimum_vertices_ne (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i j : ℕ) (hij : i < j) (hj : j ≤ P.pieces) : P.vertices i ≠ P.vertices j := by
  intro he
  let Q := (point O (P.vertices i) (P.vertex_mem i (by omega))).withEndpoints rfl he.symm
  have hh := P.minimum_shortcut_bound hmin i j (by omega) hj Q
  change j-i ≤ 0 at hh
  omega
theorem minimum_nonadjacent_disjoint (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i j : ℕ) (hij : i+1 < j) (hj : j < P.pieces) :
    Disjoint (segment ℝ (P.vertices i) (P.vertices (i+1)))
      (segment ℝ (P.vertices j) (P.vertices (j+1))) := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hleft : segment ℝ (P.vertices i) x ⊆ O :=
    ((convex_segment (𝕜 := ℝ) _ _).segment_subset (left_mem_segment ℝ _ _) hxi).trans
      (P.inside i (by omega))
  have hright : segment ℝ x (P.vertices (j+1)) ⊆ O :=
    ((convex_segment (𝕜 := ℝ) _ _).segment_subset hxj (right_mem_segment ℝ _ _)).trans
      (P.inside j hj)
  let Q := (single O (P.vertices i) x (P.vertex_mem i (by omega)) hleft).join
    (single O x (P.vertices (j+1)) (P.inside i (by omega) hxi) hright)
  have hh := P.minimum_shortcut_bound hmin i (j+1) (by omega) (by omega) Q
  change j+1-i ≤ 1+1 at hh
  omega
theorem minimum_two_step_not_subset (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i+2 ≤ P.pieces) :
    ¬ segment ℝ (P.vertices i) (P.vertices (i+2)) ⊆ O := by
  intro h
  have hh := P.minimum_shortcut_bound hmin i (i+2) (by omega) hi
    (single O (P.vertices i) (P.vertices (i+2)) (P.vertex_mem i (by omega)) h)
  change i+2-i ≤ 1 at hh
  omega
end Zarankiewicz.PolygonalChain
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem collinear_segment_subset_union (a b c : Plane) (hac : a ≠ c)
    (h : det2 (b-a) (c-b)=0) :
    segment ℝ a c ⊆ segment ℝ a b ∪ segment ℝ b c := by
  have hd : det2 (c-a) (b-a)=0 := by
    have he : det2 (c-a) (b-a) = -det2 (b-a) (c-b) := by dsimp [det2]; ring
    rw [he,h,neg_zero]
  have hp := vector_parallel_of_det_zero (c-a) (b-a) (sub_ne_zero.mpr (Ne.symm hac)) hd
  have hb : b ∈ Set.range (AffineMap.lineMap a c : ℝ → Plane) := by
    refine ⟨dot2 (c-a) (b-a)/squaredLength (c-a),?_⟩
    rw [AffineMap.lineMap_apply]
    change (dot2 (c-a) (b-a)/squaredLength (c-a)) • (c-a)+a=b
    rw [← hp,sub_add_cancel]
  intro x hx
  rw [← insert_endpoints_openSegment] at hx
  rcases hx with hxa | hxc | hxo
  · subst x
    exact Or.inl (left_mem_segment ℝ a b)
  · subst x
    exact Or.inr (right_mem_segment ℝ b c)
  · rcases openSegment_subset_union a c hb hxo with hxb | hx'
    · subst x
      exact Or.inl (right_mem_segment ℝ a b)
    · exact hx'.elim (fun hh => Or.inl (openSegment_subset_segment ℝ a b hh))
        (fun hh => Or.inr (openSegment_subset_segment ℝ b c hh))
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem adjacent_segments_meet_only_at_bend (a b c : Plane)
    (h : det2 (b-a) (c-b) ≠ 0) {x : Plane}
    (hx : x ∈ segment ℝ a b) (hy : x ∈ segment ℝ b c) : x=b := by
  rw [← Path.range_segment] at hx hy
  obtain ⟨s,hs⟩ := hx
  obtain ⟨t,ht⟩ := hy
  have hs' : segmentPoint a b s.val=x := by simpa [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hs
  have ht' : segmentPoint b c t.val=x := by simpa [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht
  have he := segment_intersection_parameters_unique a b b c h s.val t.val 1 0
    (hs'.trans ht'.symm) (by simp)
  rw [he.1,segmentPoint_one] at hs'
  exact hs'.symm
namespace PolygonalChain
variable {O : Set Plane} {a b : Plane}
theorem minimum_bend_det_ne_zero (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i+2 ≤ P.pieces) :
    det2 (P.vertices (i+1)-P.vertices i) (P.vertices (i+2)-P.vertices (i+1)) ≠ 0 := by
  intro he
  apply P.minimum_two_step_not_subset hmin i hi
  exact (collinear_segment_subset_union _ _ _ (P.minimum_vertices_ne hmin i (i+2) (by omega) hi) he).trans
    (Set.union_subset (P.inside i (by omega)) (P.inside (i+1) (by omega)))
theorem minimum_adjacent_intersection (P : PolygonalChain O a b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces)
    (i : ℕ) (hi : i+2 ≤ P.pieces) {x : Plane}
    (hx : x ∈ segment ℝ (P.vertices i) (P.vertices (i+1)))
    (hy : x ∈ segment ℝ (P.vertices (i+1)) (P.vertices (i+2))) : x=P.vertices (i+1) := by
  exact adjacent_segments_meet_only_at_bend _ _ _ (P.minimum_bend_det_ne_zero hmin i hi) hx hy
end PolygonalChain
end Zarankiewicz
end
end OAI
end
section
namespace OAI
namespace Zarankiewicz
theorem path_meeting_parameters {X : Type*} [TopologicalSpace X] {a b c : X}
    (γ : Path a b) (η : Path b c) (hγ : Function.Injective γ) (hη : Function.Injective η)
    (hm : ∀ x, x ∈ Set.range γ → x ∈ Set.range η → x=b)
    (s t : unitInterval) (he : γ s=η t) : s=1 ∧ t=0 := by
  have hx : γ s=b := hm _ ⟨s,rfl⟩ ⟨t,he.symm⟩
  exact ⟨hγ (hx.trans γ.target.symm),hη (he.symm.trans (hx.trans η.source.symm))⟩
theorem path_trans_injective {X : Type*} [TopologicalSpace X] {a b c : X}
    (γ : Path a b) (η : Path b c) (hγ : Function.Injective γ) (hη : Function.Injective η)
    (hm : ∀ x, x ∈ Set.range γ → x ∈ Set.range η → x=b) :
    Function.Injective (γ.trans η) := by
  intro s t he
  by_cases hs : (s : ℝ) ≤ 1/2 <;> by_cases ht : (t : ℝ) ≤ 1/2
  · simp only [Path.trans_apply,dif_pos hs,dif_pos ht] at he
    have hh := congrArg Subtype.val (hγ he)
    apply Subtype.ext
    change 2*(s : ℝ)=2*(t : ℝ) at hh
    linarith
  · simp only [Path.trans_apply,dif_pos hs,dif_neg ht] at he
    have hh := congrArg Subtype.val (path_meeting_parameters γ η hγ hη hm _ _ he).2
    change 2*(t : ℝ)-1=0 at hh
    exfalso
    linarith
  · simp only [Path.trans_apply,dif_neg hs,dif_pos ht] at he
    have hh := congrArg Subtype.val (path_meeting_parameters γ η hγ hη hm _ _ he.symm).2
    change 2*(s : ℝ)-1=0 at hh
    exfalso
    linarith
  · simp only [Path.trans_apply,dif_neg hs,dif_neg ht] at he
    have hh := congrArg Subtype.val (hη he)
    apply Subtype.ext
    change 2*(s : ℝ)-1=2*(t : ℝ)-1 at hh
    linarith
end Zarankiewicz
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem polygonalArcPath_range_piece (v : ℕ → Plane) :
    (n : ℕ) → 0 < n → ∀ x ∈ Set.range (polygonalArcPath v n),
      ∃ i, i < n ∧ x ∈ segment ℝ (v i) (v (i+1))
  | 0, hn, _, _ => by omega
  | 1, _, x, hx => by
    refine ⟨0,by omega,?_⟩
    simpa only [polygonalArcPath,Path.range_segment] using hx
  | n+2, _, x, hx => by
    rw [polygonalArcPath,Path.trans_range] at hx
    rcases hx with hx | hx
    · obtain ⟨i,hi,hh⟩ := polygonalArcPath_range_piece v (n+1) (by omega) x hx
      exact ⟨i,by omega,hh⟩
    · exact ⟨n+1,by omega,by simpa only [Path.range_segment] using hx⟩
theorem polygonalArcPath_injective (v : ℕ → Plane) : (n : ℕ) → 0 < n →
    (∀ i, i < n → v i ≠ v (i+1)) →
    (∀ i j, i < j → j < n → ∀ x,
      x ∈ segment ℝ (v i) (v (i+1)) → x ∈ segment ℝ (v j) (v (j+1)) →
      j=i+1 ∧ x=v j) → Function.Injective (polygonalArcPath v n)
  | 0, hn, _, _ => by omega
  | 1, _, hn, _ => Path.segment_injective_of_ne (hn 0 (by omega))
  | n+2, _, hn, hm => by
    apply path_trans_injective
    · exact polygonalArcPath_injective v (n+1) (by omega)
        (fun i hi => hn i (by omega)) (fun i j hij hj => hm i j hij (by omega))
    · exact Path.segment_injective_of_ne (hn (n+1) (by omega))
    · intro x hx hy
      obtain ⟨i,hi,hh⟩ := polygonalArcPath_range_piece v (n+1) (by omega) x hx
      rw [Path.range_segment] at hy
      exact (hm i (n+1) hi (by omega) x hh hy).2
namespace PolygonalChain
variable {O : Set Plane} {a b : Plane}
theorem minimum_path_injective (P : PolygonalChain O a b) (hab : a ≠ b)
    (hmin : ∀ Q : PolygonalChain O a b, P.pieces ≤ Q.pieces) : Function.Injective P.path := by
  have hp : 0 < P.pieces := by
    by_contra h
    have hz : P.pieces=0 := by omega
    exact hab (P.first.symm.trans (hz ▸ P.last))
  change Function.Injective (polygonalArcPath P.vertices P.pieces)
  apply polygonalArcPath_injective P.vertices P.pieces hp
  · intro i hi
    exact P.minimum_vertices_ne hmin i (i+1) (by omega) (by omega)
  · intro i j hij hj x hx hy
    by_cases he : j=i+1
    · subst j
      exact ⟨rfl,P.minimum_adjacent_intersection hmin i (by omega) hx hy⟩
    · exact False.elim ((Set.disjoint_left.mp (P.minimum_nonadjacent_disjoint hmin i j (by omega) hj)) hx hy)
end PolygonalChain
end Zarankiewicz
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Paper170
end Paper170
end
end
section
noncomputable section
namespace Paper170
end Paper170
end
end
section
noncomputable section
namespace Paper170Geometry
end Paper170Geometry
end
end
section
noncomputable section
namespace Paper170
end Paper170
end
end
section
noncomputable section
namespace Paper170
end Paper170
end
end
section
noncomputable section
namespace Paper170
end Paper170
end
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem chart_image_mem_iff (e : OpenPartialHomeomorph Plane Plane) (A L : Set Plane)
    (h : e '' (e.source ∩ A)=e.target ∩ L) (x : Plane) (hx : x ∈ e.source) :
    x ∈ A ↔ e x ∈ L := by
  constructor
  · intro ha
    have hh : e x ∈ e '' (e.source ∩ A) := ⟨x,⟨hx,ha⟩,rfl⟩
    rw [h] at hh
    exact hh.2
  · intro hl
    have hh : e x ∈ e '' (e.source ∩ A) := h.symm ▸ ⟨e.map_source hx,hl⟩
    obtain ⟨y,hy,he⟩ := hh
    have hyx : y=x := e.injOn hy.1 hx he
    exact hyx ▸ hy.2
theorem chart_restr_image_of_local_eq (e : OpenPartialHomeomorph Plane Plane)
    (A A' L U : Set Plane) (hU : IsOpen U) (hA : ∀ x ∈ U, x ∈ A ↔ x ∈ A')
    (h : e '' (e.source ∩ A)=e.target ∩ L) :
    (e.restrOpen U hU) '' ((e.restrOpen U hU).source ∩ A')=(e.restrOpen U hU).target ∩ L := by
  let f := e.restrOpen U hU
  apply Set.Subset.antisymm
  · rintro y ⟨x,hx,rfl⟩
    have hs : x ∈ e.source ∩ U := hx.1
    exact ⟨f.map_source hx.1,(chart_image_mem_iff e A L h x hs.1).mp ((hA x hs.2).mpr hx.2)⟩
  · rintro y ⟨hy,hl⟩
    have hs : f.symm y ∈ f.source := f.map_target hy
    have hs' : f.symm y ∈ e.source ∩ U := hs
    have he : e (f.symm y)=y := f.right_inv hy
    have ha : f.symm y ∈ A := (chart_image_mem_iff e A L h _ hs'.1).mpr (he.symm ▸ hl)
    exact ⟨f.symm y,⟨hs,(hA _ hs'.2).mp ha⟩,f.right_inv hy⟩
theorem properCrossing_of_local_eq (A B A' B' : Set Plane) (x : Plane)
    (h : ProperCrossing A B x) (U : Set Plane) (hU : IsOpen U) (hx : x ∈ U)
    (hA : ∀ z ∈ U, z ∈ A ↔ z ∈ A') (hB : ∀ z ∈ U, z ∈ B ↔ z ∈ B') :
    ProperCrossing A' B' x := by
  obtain ⟨e,hs,he,hEA,hEB⟩ := h
  refine ⟨e.restrOpen U hU,⟨hs,hx⟩,he,?_,?_⟩
  · exact chart_restr_image_of_local_eq e A A' {y | y.2=0} U hU hA hEA
  · exact chart_restr_image_of_local_eq e B B' {y | y.1=0} U hU hB hEB
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
def crossingCoordinates (o u v x : Plane) : Plane :=
  (det2 (x-o) v/det2 u v,det2 u (x-o)/det2 u v)
def crossingCoordinateInverse (o u v s : Plane) : Plane := o+s.1 • u+s.2 • v
theorem crossingCoordinates_left_inverse (o u v : Plane) (h : det2 u v ≠ 0) (x : Plane) :
    crossingCoordinateInverse o u v (crossingCoordinates o u v x)=x := by
  have hc := mul_inv_cancel₀ h
  apply Prod.ext
  · dsimp [crossingCoordinateInverse,crossingCoordinates,det2] at *
    simp only [div_eq_mul_inv]
    linear_combination (x.1-o.1)*hc
  · dsimp [crossingCoordinateInverse,crossingCoordinates,det2] at *
    simp only [div_eq_mul_inv]
    linear_combination (x.2-o.2)*hc
theorem crossingCoordinates_right_inverse (o u v : Plane) (h : det2 u v ≠ 0) (s : Plane) :
    crossingCoordinates o u v (crossingCoordinateInverse o u v s)=s := by
  have hc := mul_inv_cancel₀ h
  apply Prod.ext
  · dsimp [crossingCoordinateInverse,crossingCoordinates,det2] at *
    simp only [div_eq_mul_inv]
    linear_combination s.1*hc
  · dsimp [crossingCoordinateInverse,crossingCoordinates,det2] at *
    simp only [div_eq_mul_inv]
    linear_combination s.2*hc
theorem crossingCoordinates_continuous (o u v : Plane) : Continuous (crossingCoordinates o u v) := by
  unfold crossingCoordinates det2
  fun_prop
theorem crossingCoordinateInverse_continuous (o u v : Plane) : Continuous (crossingCoordinateInverse o u v) := by
  unfold crossingCoordinateInverse
  fun_prop
def crossingCoordinateChart (o u v : Plane) (h : det2 u v ≠ 0)
    (U : Set Plane) (hU : IsOpen U) : OpenPartialHomeomorph Plane Plane where
  toFun := crossingCoordinates o u v
  invFun := crossingCoordinateInverse o u v
  source := crossingCoordinates o u v ⁻¹' U
  target := U
  map_source' := fun {_} hx => hx
  map_target' := fun {s} hs => by
    change crossingCoordinates o u v (crossingCoordinateInverse o u v s) ∈ U
    rw [crossingCoordinates_right_inverse o u v h]
    exact hs
  left_inv' := fun {x} _ => crossingCoordinates_left_inverse o u v h x
  right_inv' := fun {s} _ => crossingCoordinates_right_inverse o u v h s
  continuousOn_toFun := (crossingCoordinates_continuous o u v).continuousOn
  continuousOn_invFun := (crossingCoordinateInverse_continuous o u v).continuousOn
  open_source := hU.preimage (crossingCoordinates_continuous o u v)
  open_target := hU
@[simp] theorem crossingCoordinates_origin (o u v : Plane) : crossingCoordinates o u v o=(0,0) := by
  simp [crossingCoordinates]
end Zarankiewicz
end
end OAI
end
section
namespace OAI
namespace Zarankiewicz
theorem inverseCoordinates_first_segment (a b c d o : Plane) (t s : ℝ)
    (ho : o=segmentPoint a b t) :
    crossingCoordinateInverse o (b-a) (d-c) (s-t,0)=segmentPoint a b s := by
  rw [ho]
  apply Prod.ext <;> dsimp [crossingCoordinateInverse,segmentPoint] <;> ring
theorem inverseCoordinates_second_segment (a b c d o : Plane) (t s : ℝ)
    (ho : o=segmentPoint c d t) :
    crossingCoordinateInverse o (b-a) (d-c) (0,s-t)=segmentPoint c d s := by
  rw [ho]
  apply Prod.ext <;> dsimp [crossingCoordinateInverse,segmentPoint] <;> ring
theorem crossingCoordinates_first_segment (a b c d o : Plane) (t s : ℝ)
    (hd : det2 (b-a) (d-c) ≠ 0) (ho : o=segmentPoint a b t) :
    crossingCoordinates o (b-a) (d-c) (segmentPoint a b s)=(s-t,0) := by
  rw [← inverseCoordinates_first_segment a b c d o t s ho]
  exact crossingCoordinates_right_inverse o (b-a) (d-c) hd _
theorem crossingCoordinates_second_segment (a b c d o : Plane) (t s : ℝ)
    (hd : det2 (b-a) (d-c) ≠ 0) (ho : o=segmentPoint c d t) :
    crossingCoordinates o (b-a) (d-c) (segmentPoint c d s)=(0,s-t) := by
  rw [← inverseCoordinates_second_segment a b c d o t s ho]
  exact crossingCoordinates_right_inverse o (b-a) (d-c) hd _
end Zarankiewicz
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem properCrossing_openSegments (a b c d x : Plane) (hd : det2 (b-a) (d-c) ≠ 0)
    (hx : x ∈ openSegmentTrace a b) (hy : x ∈ openSegmentTrace c d) :
    ProperCrossing (openSegmentTrace a b) (openSegmentTrace c d) x := by
  obtain ⟨t,ht,hxt⟩ := hx
  obtain ⟨u,hu,hxu⟩ := hy
  let U : Set Plane := Set.Ioo (-t) (1-t) ×ˢ Set.Ioo (-u) (1-u)
  have hU : IsOpen U := isOpen_Ioo.prod isOpen_Ioo
  let chart := crossingCoordinateChart x (b-a) (d-c) hd U hU
  have hzero : (0,0) ∈ U := ⟨⟨by linarith [ht.1],by linarith [ht.2]⟩,
    ⟨by linarith [hu.1],by linarith [hu.2]⟩⟩
  have hsource : x ∈ chart.source := by
    change crossingCoordinates x (b-a) (d-c) x ∈ U
    rw [crossingCoordinates_origin]
    exact hzero
  refine ⟨chart,hsource,crossingCoordinates_origin x (b-a) (d-c),?_,?_⟩
  · apply Set.Subset.antisymm
    · rintro y ⟨z,hz,rfl⟩
      refine ⟨chart.map_source hz.1,?_⟩
      obtain ⟨s,hs,he⟩ := hz.2
      rw [← he]
      change (crossingCoordinates x (b-a) (d-c) (segmentPoint a b s)).2=0
      rw [crossingCoordinates_first_segment a b c d x t s hd hxt.symm]
    · rintro y ⟨hy,hy0⟩
      have hs : t+y.1 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hy.1.1],by linarith [hy.1.2]⟩
      have he : chart (segmentPoint a b (t+y.1))=y := by
        change crossingCoordinates x (b-a) (d-c) (segmentPoint a b (t+y.1))=y
        rw [crossingCoordinates_first_segment a b c d x t (t+y.1) hd hxt.symm]
        apply Prod.ext
        · dsimp
          ring
        · exact hy0.symm
      refine ⟨segmentPoint a b (t+y.1),⟨?_,⟨t+y.1,hs,rfl⟩⟩,he⟩
      change chart (segmentPoint a b (t+y.1)) ∈ U
      rw [he]
      exact hy
  · apply Set.Subset.antisymm
    · rintro y ⟨z,hz,rfl⟩
      refine ⟨chart.map_source hz.1,?_⟩
      obtain ⟨s,hs,he⟩ := hz.2
      rw [← he]
      change (crossingCoordinates x (b-a) (d-c) (segmentPoint c d s)).1=0
      rw [crossingCoordinates_second_segment a b c d x u s hd hxu.symm]
    · rintro y ⟨hy,hy0⟩
      have hs : u+y.2 ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hy.2.1],by linarith [hy.2.2]⟩
      have he : chart (segmentPoint c d (u+y.2))=y := by
        change crossingCoordinates x (b-a) (d-c) (segmentPoint c d (u+y.2))=y
        rw [crossingCoordinates_second_segment a b c d x u (u+y.2) hd hxu.symm]
        apply Prod.ext
        · exact hy0.symm
        · dsimp
          ring
      refine ⟨segmentPoint c d (u+y.2),⟨?_,⟨u+y.2,hs,rfl⟩⟩,he⟩
      change chart (segmentPoint c d (u+y.2)) ∈ U
      rw [he]
      exact hy
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem squaredLength_add_smul (u v : Plane) (t : ℝ) :
    squaredLength (u+t • v)=squaredLength u+2*t*dot2 u v+t^2*squaredLength v := by
  dsimp [squaredLength,dot2]
  ring
theorem squaredLength_segment_translated (a b z : Plane) (t : ℝ) :
    squaredLength (segmentPoint a b t-z)=
      squaredLength (a-z)+2*t*dot2 (a-z) (b-a)+t^2*squaredLength (b-a) := by
  dsimp [squaredLength,dot2,segmentPoint]
  ring
theorem exterior_segment_of_dot (z a b : Plane) (r : ℝ)
    (ha : r^2 < squaredLength (a-z)) (hd : 0 ≤ dot2 (a-z) (b-a)) :
    segment ℝ a b ⊆ {x | r^2 < squaredLength (x-z)} := by
  intro x hx
  rw [← Path.range_segment] at hx
  obtain ⟨t,rfl⟩ := hx
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module]
  change r^2 < squaredLength (segmentPoint a b t.val-z)
  rw [squaredLength_segment_translated]
  have h₁ : 0 ≤ 2*t.val*dot2 (a-z) (b-a) := mul_nonneg (mul_nonneg (by norm_num) t.property.1) hd
  have h₂ : 0 ≤ t.val^2*squaredLength (b-a) := by dsimp [squaredLength]; positivity
  linarith
theorem radial_spur_exterior (z x : Plane) (r α : ℝ)
    (hx : squaredLength (x-z)=r^2) (hr : 0 < r) (hα : 0 < α) :
    segment ℝ x (x+α • (x-z)) ⊆ insert x {y | r^2 < squaredLength (y-z)} := by
  intro y hy
  rw [← Path.range_segment] at hy
  obtain ⟨t,rfl⟩ := hy
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module]
  by_cases ht : t.val=0
  · left
    change segmentPoint x (x+α • (x-z)) t.val=x
    rw [ht,segmentPoint_zero]
  · right
    have htpos : 0 < t.val := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    change r^2 < squaredLength (segmentPoint x (x+α • (x-z)) t.val-z)
    have he : squaredLength (segmentPoint x (x+α • (x-z)) t.val-z)=
        (1+t.val*α)^2*squaredLength (x-z) := by
      dsimp [squaredLength,segmentPoint]
      ring
    rw [he,hx]
    have hp := mul_pos htpos hα
    nlinarith [sq_pos_of_pos hr,mul_pos hp (sq_pos_of_pos hr)]
theorem radial_tip_dot (z x : Plane) (α : ℝ) :
    dot2 (x-z) ((x+α • (x-z))-x)=α*squaredLength (x-z) := by
  dsimp [dot2,squaredLength]
  ring
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem segmentPairTransverse_of_noncollinear_endpoints (a b c d : Plane)
    (ha : orient2 c d a ≠ 0) (hb : orient2 c d b ≠ 0)
    (hc : orient2 a b c ≠ 0) (hd : orient2 a b d ≠ 0) :
    SegmentPairTransverse a b c d := by
  intro t ht u hu he
  have hdet : det2 (b-a) (d-c) ≠ 0 := by
    intro hz
    have hdiff := orient2_difference a b c d
    have heq : orient2 a b c=orient2 a b d := by linarith
    have hh := congrArg (orient2 a b) he
    rw [orient2_self_segment,orient2_segment,← heq] at hh
    apply hc
    nlinarith
  have ht0 : t ≠ 0 := by
    intro h
    subst t
    rw [segmentPoint_zero] at he
    exact ha (by rw [he,orient2_self_segment])
  have ht1 : t ≠ 1 := by
    intro h
    subst t
    rw [segmentPoint_one] at he
    exact hb (by rw [he,orient2_self_segment])
  have hu0 : u ≠ 0 := by
    intro h
    subst u
    rw [segmentPoint_zero] at he
    exact hc (by rw [← he,orient2_self_segment])
  have hu1 : u ≠ 1 := by
    intro h
    subst u
    rw [segmentPoint_one] at he
    exact hd (by rw [← he,orient2_self_segment])
  exact ⟨hdet,⟨lt_of_le_of_ne ht.1 ht0.symm,lt_of_le_of_ne ht.2 ht1⟩,
    ⟨lt_of_le_of_ne hu.1 hu0.symm,lt_of_le_of_ne hu.2 hu1⟩⟩
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem round_circle_line_two_points (z a b c : Plane) (r : ℝ)
    (ha : squaredLength (a-z)=r^2) (hb : squaredLength (b-z)=r^2)
    (hc : squaredLength (c-z)=r^2) (hab : a ≠ b)
    (hd : det2 (b-a) (c-a)=0) : c=a ∨ c=b := by
  have hlen := squaredLength_pos (b-a) (sub_ne_zero.mpr (Ne.symm hab))
  let t := dot2 (b-a) (c-a)/squaredLength (b-a)
  have hp : c-a=t • (b-a) := vector_parallel_of_det_zero (b-a) (c-a)
    (sub_ne_zero.mpr (Ne.symm hab)) hd
  have hba : (a-z)+(b-a)=b-z := by abel
  have hca : c-z=(a-z)+t • (b-a) := by rw [← hp]; abel
  have h₁ := squaredLength_add_smul (a-z) (b-a) 1
  simp only [one_smul,hba,ha,hb,one_pow,one_mul] at h₁
  rw [hca,squaredLength_add_smul,ha] at hc
  have hh : t*(t-1)*squaredLength (b-a)=0 := by linear_combination hc+t*h₁
  have ht := (mul_eq_zero.mp hh).resolve_right (ne_of_gt hlen)
  rcases mul_eq_zero.mp ht with ht | ht
  · left
    rw [ht,zero_smul] at hp
    exact sub_eq_zero.mp hp
  · right
    have ht1 : t=1 := sub_eq_zero.mp ht
    rw [ht1,one_smul] at hp
    exact sub_left_injective hp
theorem round_circle_orient_ne_zero (z a b c : Plane) (r : ℝ)
    (ha : squaredLength (a-z)=r^2) (hb : squaredLength (b-z)=r^2)
    (hc : squaredLength (c-z)=r^2) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    orient2 a b c ≠ 0 := by
  intro hd
  exact (round_circle_line_two_points z a b c r ha hb hc hab hd).elim
    (fun h => hac h.symm) (fun h => hbc h.symm)
theorem round_circle_chords_transverse (z a b c d : Plane) (r : ℝ)
    (ha : squaredLength (a-z)=r^2) (hb : squaredLength (b-z)=r^2)
    (hc : squaredLength (c-z)=r^2) (hd : squaredLength (d-z)=r^2)
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    SegmentPairTransverse a b c d := by
  exact segmentPairTransverse_of_noncollinear_endpoints a b c d
    (round_circle_orient_ne_zero z c d a r hc hd ha hcd hac.symm had.symm)
    (round_circle_orient_ne_zero z c d b r hc hd hb hcd hbc.symm hbd.symm)
    (round_circle_orient_ne_zero z a b c r ha hb hc hab hac hbc)
    (round_circle_orient_ne_zero z a b d r ha hb hd hab had hbd)
theorem round_chord_in_open_disk (z a b : Plane) (r : ℝ)
    (ha : squaredLength (a-z)=r^2) (hb : squaredLength (b-z)=r^2)
    (hab : a ≠ b) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    squaredLength (segmentPoint a b t-z) < r^2 := by
  have he : squaredLength (segmentPoint a b t-z)=
      (1-t)*squaredLength (a-z)+t*squaredLength (b-z)-t*(1-t)*squaredLength (b-a) := by
    dsimp [squaredLength,segmentPoint]
    ring
  have hp := mul_pos (mul_pos ht.1 (sub_pos.mpr ht.2))
    (squaredLength_pos (b-a) (sub_ne_zero.mpr hab.symm))
  rw [he,ha,hb]
  linarith
end Zarankiewicz
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Paper170
end Paper170
end
end
section
noncomputable section
namespace Paper170
end Paper170
end
end
section
noncomputable section
namespace Paper170
end Paper170
end
end
section
noncomputable section
namespace Paper170
end Paper170
end
end
section
noncomputable section
namespace Paper170
end Paper170
end
end
section
noncomputable section
namespace Paper170
end Paper170
end
end
section
noncomputable section
namespace Paper170
end Paper170
end
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
namespace Zarankiewicz
end Zarankiewicz
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem HasFiniteAffineCover.refine {a b : Plane} {γ : Path a b}
    (hγ : HasFiniteAffineCover γ) (R : Finset unitInterval) :
    ∃ P : PolygonalParametrization γ, (R : Set unitInterval) ⊆ Set.range P.knot := by
  classical
  obtain ⟨S,hSlt,hScov,hSaff⟩ := hγ
  let T : Finset unitInterval := insert 0 (insert 1 ((S.image Prod.fst ∪ S.image Prod.snd) ∪ R))
  obtain ⟨k,hk,t,ht,h0,h1,hR⟩ := exists_sorted_unitInterval_finset T (by simp [T]) (by simp [T])
  have hleft (ab : unitInterval × unitInterval) (hab : ab ∈ S) : ab.1 ∈ Set.range t := by
    rw [hR]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩))))
  have hright (ab : unitInterval × unitInterval) (hab : ab ∈ S) : ab.2 ∈ Set.range t := by
    rw [hR]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨ab,hab,rfl⟩))))
  have haff : ∀ i : Fin k, ∀ u : unitInterval,
      γ (intervalSegment (t i.castSucc) (t i.succ) u)=segmentPoint (γ (t i.castSucc)) (γ (t i.succ)) u.val := by
    intro i u
    let mid : unitInterval := ⟨1/2,by norm_num⟩
    let z := intervalSegment (t i.castSucc) (t i.succ) mid
    have hz : t i.castSucc < z ∧ z < t i.succ :=
      intervalSegment_strict_between _ _ mid (ht (by change i.val < i.val+1; omega)) (by
        constructor <;> change (_ : ℝ) < _ <;> norm_num [mid])
    obtain ⟨ab,hab,ha,hb⟩ := hScov z
    have hlo : ab.1 ≤ t i.castSucc := by
      by_contra hn
      obtain ⟨j,hj⟩ := hleft ab hab
      exact strictMono_no_between_successors t ht i j
        ⟨by rw [hj]; exact lt_of_not_ge hn,by rw [hj]; exact ha.trans_lt hz.2⟩
    have hhi : t i.succ ≤ ab.2 := by
      by_contra hn
      obtain ⟨j,hj⟩ := hright ab hab
      exact strictMono_no_between_successors t ht i j
        ⟨by rw [hj]; exact hz.1.trans_le hb,by rw [hj]; exact lt_of_not_ge hn⟩
    have hle : t i.castSucc ≤ t i.succ := ht.monotone (by change i.val ≤ i.val+1; omega)
    exact path_affine_restrict γ ab.1 ab.2 (hSlt ab hab) (hSaff ab hab)
      (t i.castSucc) (t i.succ) ⟨hlo,hle.trans hhi⟩ ⟨hlo.trans hle,hhi⟩ u
  refine ⟨{pieces:=k,knot:=t,increasing:=ht,first:=h0,last:=h1,affine:=haff},?_⟩
  intro u hu
  change u ∈ Set.range t
  rw [hR]
  exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ hu))
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.PolygonalParametrization
variable {a b : Plane} {γ : Path a b}
def pieceTrace (P : PolygonalParametrization γ) (i : Fin P.pieces) : Set Plane :=
  segment ℝ (γ (P.knot i.castSucc)) (γ (P.knot i.succ))
theorem pieceTrace_parameter (P : PolygonalParametrization γ) (i : Fin P.pieces)
    (x : Plane) (hx : x ∈ P.pieceTrace i) :
    ∃ t : unitInterval, γ (intervalSegment (P.knot i.castSucc) (P.knot i.succ) t)=x := by
  rw [pieceTrace,← Path.range_segment] at hx
  obtain ⟨t,ht⟩ := hx
  refine ⟨t,(P.affine i t).trans ?_⟩
  simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht
theorem pieceTrace_subset_range (P : PolygonalParametrization γ) (i : Fin P.pieces) :
    P.pieceTrace i ⊆ Set.range γ := by
  intro x hx
  obtain ⟨t,ht⟩ := P.pieceTrace_parameter i x hx
  exact ⟨intervalSegment (P.knot i.castSucc) (P.knot i.succ) t,ht⟩
theorem pieceTrace_knot_endpoint (P : PolygonalParametrization γ) (hγ : Function.Injective γ)
    (i : Fin P.pieces) (j : Fin (P.pieces+1))
    (hx : γ (P.knot j) ∈ P.pieceTrace i) :
    γ (P.knot j)=γ (P.knot i.castSucc) ∨ γ (P.knot j)=γ (P.knot i.succ) := by
  obtain ⟨t,ht⟩ := P.pieceTrace_parameter i _ hx
  by_cases ht0 : t=0
  · subst t
    simpa [intervalSegment] using Or.inl ht.symm
  by_cases ht1 : t=1
  · subst t
    simpa [intervalSegment] using Or.inr ht.symm
  have hmid := intervalSegment_strict_between (P.knot i.castSucc) (P.knot i.succ) t
    (P.increasing (by change i.val < i.val+1; omega))
    ⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
      lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩
  have he := hγ ht
  rw [he] at hmid
  exact False.elim (strictMono_no_between_successors P.knot P.increasing i j hmid)
theorem pieceTrace_other_piece_endpoint (P : PolygonalParametrization γ) (hγ : Function.Injective γ)
    (i j : Fin P.pieces) (hij : i ≠ j) (x : Plane)
    (hx : x ∈ P.pieceTrace i) (hy : x ∈ P.pieceTrace j) :
    x=γ (P.knot i.castSucc) ∨ x=γ (P.knot i.succ) := by
  obtain ⟨s,hs⟩ := P.pieceTrace_parameter i x hx
  obtain ⟨t,ht⟩ := P.pieceTrace_parameter j x hy
  by_cases hs0 : s=0
  · subst s
    exact Or.inl (by simpa [intervalSegment] using hs.symm)
  by_cases hs1 : s=1
  · subst s
    exact Or.inr (by simpa [intervalSegment] using hs.symm)
  have hsbetween := intervalSegment_strict_between (P.knot i.castSucc) (P.knot i.succ) s
    (P.increasing (by change i.val < i.val+1; omega))
    ⟨lt_of_le_of_ne (show 0 ≤ s from s.property.1) (Ne.symm hs0),
      lt_of_le_of_ne (show s ≤ 1 from s.property.2) hs1⟩
  have htbetween := intervalSegment_between (P.knot j.castSucc) (P.knot j.succ) t
    (P.increasing.monotone (by change j.val ≤ j.val+1; omega))
  have he := hγ (hs.trans ht.symm)
  rw [he] at hsbetween
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hgap := P.increasing.monotone (show i.succ ≤ j.castSucc by change i.val+1 ≤ j.val; exact hij)
    exact False.elim (hsbetween.2.not_ge (hgap.trans htbetween.1))
  · have hgap := P.increasing.monotone (show j.succ ≤ i.castSucc by change j.val+1 ≤ i.val; exact hji)
    exact False.elim (hsbetween.1.not_ge (htbetween.2.trans hgap))
end Zarankiewicz.PolygonalParametrization
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
namespace Zarankiewicz
end Zarankiewicz
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
def StraightEdgeEmbedding {V : Type*} (G : SimpleGraph V) (pos : V → Plane) : Prop :=
  Function.Injective pos ∧
    ∀ a b c d, G.Adj a b → G.Adj c d → ∀ x,
      x ∈ segment ℝ (pos a) (pos b) → x ∈ segment ℝ (pos c) (pos d) →
      (a=c ∧ b=d) ∨ (a=d ∧ b=c) ∨
      (a=c ∧ x=pos a) ∨ (a=d ∧ x=pos a) ∨
      (b=c ∧ x=pos b) ∨ (b=d ∧ x=pos b)
def graphWalkPath {V : Type*} {G : SimpleGraph V} (pos : V → Plane) {a b : V} (p : G.Walk a b) :
    Path (pos a) (pos b) :=
  (polygonalArcPath (fun i => pos (p.getVert i)) p.length).cast
    (congrArg pos p.getVert_zero).symm (congrArg pos p.getVert_length).symm
theorem graphWalkPath_injective {V : Type*} {G : SimpleGraph V} (pos : V → Plane)
    (hemb : StraightEdgeEmbedding G pos) {a b : V} (hab : a ≠ b)
    (p : G.Walk a b) (hp : p.IsPath) : Function.Injective (graphWalkPath pos p) := by
  have hn : 0 < p.length := by
    by_contra h
    have hz : p.length=0 := by omega
    have he := p.getVert_zero.symm.trans (hz ▸ p.getVert_length)
    exact hab he
  change Function.Injective (polygonalArcPath (fun i => pos (p.getVert i)) p.length)
  apply polygonalArcPath_injective _ _ hn
  · intro i hi he
    have hij := hp.getVert_injOn (show i ≤ p.length by omega) (show i+1 ≤ p.length by omega) (hemb.1 he)
    omega
  · intro i j hij hj x hx hy
    have hmeet := hemb.2 _ _ _ _ (p.adj_getVert_succ (show i < p.length by omega))
      (p.adj_getVert_succ hj) x hx hy
    have hindex (r s : ℕ) (hr : r ≤ p.length) (hs : s ≤ p.length)
        (he : p.getVert r=p.getVert s) : r=s := hp.getVert_injOn hr hs he
    rcases hmeet with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ | ⟨h₁,hx⟩ | ⟨h₁,hx⟩ | ⟨h₁,hx⟩ | ⟨h₁,hx⟩
    · have hh := hindex i j (by omega) (by omega) h₁
      omega
    · have hh := hindex i (j+1) (by omega) (by omega) h₁
      omega
    · have hh := hindex i j (by omega) (by omega) h₁
      omega
    · have hh := hindex i (j+1) (by omega) (by omega) h₁
      omega
    · have hh := hindex (i+1) j (by omega) (by omega) h₁
      exact ⟨hh.symm,hx.trans (congrArg pos h₁)⟩
    · have hh := hindex (i+1) (j+1) (by omega) (by omega) h₁
      omega
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem common_endpoint_alternatives (a b c d x : Plane) (hab : x=a ∨ x=b) (hcd : x=c ∨ x=d) :
    (a=c ∧ x=a) ∨ (a=d ∧ x=a) ∨ (b=c ∧ x=b) ∨ (b=d ∧ x=b) := by
  rcases hab with ha | hb <;> rcases hcd with hc | hd
  · exact Or.inl ⟨ha.symm.trans hc,ha⟩
  · exact Or.inr (Or.inl ⟨ha.symm.trans hd,ha⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hb.symm.trans hc,hb⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hb.symm.trans hd,hb⟩))
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem segment_endpoint_or_open (a b x : Plane) (hx : x ∈ segment ℝ a b) :
    x=a ∨ x=b ∨ x ∈ openSegmentTrace a b := by
  rw [← Path.range_segment] at hx
  obtain ⟨t,ht⟩ := hx
  by_cases ht0 : t=0
  · subst t
    exact Or.inl (by simpa only [Path.source] using ht.symm)
  by_cases ht1 : t=1
  · subst t
    exact Or.inr (Or.inl (by simpa only [Path.target] using ht.symm))
  refine Or.inr (Or.inr ⟨t.val,⟨?_,?_⟩,?_⟩)
  · exact lt_of_le_of_ne t.property.1 (fun he => ht0 (Subtype.ext he.symm))
  · exact lt_of_le_of_ne t.property.2 (fun he => ht1 (Subtype.ext he))
  · simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht
def segmentAugmentedGraph {ι : Type*} (G : SimpleGraph Plane) (a b : ι → Plane)
    (hne : ∀ i, a i ≠ b i) : SimpleGraph Plane where
  Adj := fun x y => G.Adj x y ∨ ∃ i, (x=a i ∧ y=b i) ∨ (x=b i ∧ y=a i)
  symm := ⟨by
    rintro x y (hxy | ⟨i,⟨hx,hy⟩ | ⟨hx,hy⟩⟩)
    · exact Or.inl hxy.symm
    · exact Or.inr ⟨i,Or.inr ⟨hy,hx⟩⟩
    · exact Or.inr ⟨i,Or.inl ⟨hy,hx⟩⟩⟩
  loopless := ⟨by
    rintro x (hxx | ⟨i,⟨hx,hy⟩ | ⟨hx,hy⟩⟩)
    · exact G.loopless.irrefl x hxx
    · exact hne i (hx.symm.trans hy)
    · exact hne i (hy.symm.trans hx)⟩
theorem le_segmentAugmentedGraph {ι : Type*} (G : SimpleGraph Plane) (a b : ι → Plane)
    (hne : ∀ i, a i ≠ b i) : G ≤ segmentAugmentedGraph G a b hne := fun _ _ h => Or.inl h
theorem segmentAugmentedGraph_added_adj {ι : Type*} (G : SimpleGraph Plane) (a b : ι → Plane)
    (hne : ∀ i, a i ≠ b i) (i : ι) : (segmentAugmentedGraph G a b hne).Adj (a i) (b i) :=
  Or.inr ⟨i,Or.inl ⟨rfl,rfl⟩⟩
theorem exterior_segment_chord_meeting (G : SimpleGraph Plane) (U : Set Plane) (a b x y z : Plane)
    (hxy : G.Adj x y) (hout : ∀ x y, G.Adj x y → Disjoint (segment ℝ x y) U)
    (hin : openSegmentTrace a b ⊆ U)
    (ha : a ∈ segment ℝ x y → a=x ∨ a=y) (hb : b ∈ segment ℝ x y → b=x ∨ b=y)
    (hz : z ∈ segment ℝ x y) (hchord : z ∈ segment ℝ a b) :
    (z=x ∨ z=y) ∧ (z=a ∨ z=b) := by
  rcases segment_endpoint_or_open a b z hchord with rfl | rfl | hz'
  · exact ⟨ha hz,Or.inl rfl⟩
  · exact ⟨hb hz,Or.inr rfl⟩
  · exact False.elim (Set.disjoint_left.mp (hout x y hxy) hz (hin hz'))
theorem segmentAugmentedGraph_embedding {ι : Type*} (G : SimpleGraph Plane) (a b : ι → Plane)
    (hne : ∀ i, a i ≠ b i) (hemb : StraightEdgeEmbedding G id) (U : Set Plane)
    (hout : ∀ x y, G.Adj x y → Disjoint (segment ℝ x y) U)
    (hin : ∀ i, openSegmentTrace (a i) (b i) ⊆ U)
    (hdisj : ∀ i j, i ≠ j → Disjoint (segment ℝ (a i) (b i)) (segment ℝ (a j) (b j)))
    (hend : ∀ i x y, G.Adj x y →
      (a i ∈ segment ℝ x y → a i=x ∨ a i=y) ∧
      (b i ∈ segment ℝ x y → b i=x ∨ b i=y)) :
    StraightEdgeEmbedding (segmentAugmentedGraph G a b hne) id := by
  refine ⟨Function.injective_id,?_⟩
  intro x y z w hxy hzw r hrx hrz
  rcases hxy with hxy | ⟨i,hi⟩ <;> rcases hzw with hzw | ⟨j,hj⟩
  · exact hemb.2 x y z w hxy hzw r hrx hrz
  · have hchord : r ∈ segment ℝ (a j) (b j) := by
      rcases hj with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hrz
      · simpa only [id_eq,segment_symm] using hrz
    obtain ⟨hold,hnew⟩ := exterior_segment_chord_meeting G U (a j) (b j) x y r hxy hout
      (hin j) (hend j x y hxy).1 (hend j x y hxy).2 hrx hchord
    have hrzw : r=z ∨ r=w := by
      rcases hj with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hnew
      · exact hnew.symm
    exact Or.inr (Or.inr (common_endpoint_alternatives x y z w r hold hrzw))
  · have hchord : r ∈ segment ℝ (a i) (b i) := by
      rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hrx
      · simpa only [id_eq,segment_symm] using hrx
    obtain ⟨hold,hnew⟩ := exterior_segment_chord_meeting G U (a i) (b i) z w r hzw hout
      (hin i) (hend i z w hzw).1 (hend i z w hzw).2 hrz hchord
    have hrxy : r=x ∨ r=y := by
      rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hnew
      · exact hnew.symm
    exact Or.inr (Or.inr (common_endpoint_alternatives x y z w r hrxy hold))
  · by_cases hij : i=j
    · subst j
      rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rcases hj with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Or.inl ⟨rfl,rfl⟩
      · exact Or.inr (Or.inl ⟨rfl,rfl⟩)
      · exact Or.inr (Or.inl ⟨rfl,rfl⟩)
      · exact Or.inl ⟨rfl,rfl⟩
    · apply False.elim
      apply Set.disjoint_left.mp (hdisj i j hij)
      · rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hrx
        · simpa only [id_eq,segment_symm] using hrx
      · rcases hj with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hrz
        · simpa only [id_eq,segment_symm] using hrz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem crossingCoordinates_affine (o u v a b : Plane) (t : ℝ) :
    crossingCoordinates o u v (segmentPoint a b t)=
      segmentPoint (crossingCoordinates o u v a) (crossingCoordinates o u v b) t := by
  apply Prod.ext <;> dsimp [crossingCoordinates,segmentPoint,det2] <;>
    simp only [div_eq_mul_inv] <;> ring
theorem convex_combination_pos (a b t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 < (1-t)*a+t*b := by
  have hm : 0 < min a b := lt_min ha hb
  have hl := mul_le_mul_of_nonneg_left (min_le_left a b) (sub_nonneg.mpr ht.2)
  have hr := mul_le_mul_of_nonneg_left (min_le_right a b) ht.1
  nlinarith
theorem crossing_reconnections_disjoint (a b c d : Plane) (h : SegmentsCrossProperly a b c d) :
    Disjoint (segment ℝ c b) (segment ℝ a d) := by
  obtain ⟨hd,s,hs,t,ht,hst⟩ := h
  let o := segmentPoint a b s
  let F := crossingCoordinates o (b-a) (d-c)
  have hFa : F a=(-s,0) := by
    have he := crossingCoordinates_first_segment a b c d o s 0 hd rfl
    simpa only [segmentPoint_zero,zero_sub] using he
  have hFb : F b=(1-s,0) := by
    have he := crossingCoordinates_first_segment a b c d o s 1 hd rfl
    simpa only [segmentPoint_one] using he
  have hFc : F c=(0,-t) := by
    have he := crossingCoordinates_second_segment a b c d o t 0 hd hst
    simpa only [segmentPoint_zero,zero_sub] using he
  have hFd : F d=(0,1-t) := by
    have he := crossingCoordinates_second_segment a b c d o t 1 hd hst
    simpa only [segmentPoint_one] using he
  apply Set.disjoint_left.mpr
  intro x hleft hright
  rw [← Path.range_segment] at hleft hright
  obtain ⟨u,hu⟩ := hleft
  obtain ⟨v,hv⟩ := hright
  have hu' : segmentPoint c b u.val=x := by
    simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hu
  have hv' : segmentPoint a d v.val=x := by
    simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hv
  have hleftF : F x=segmentPoint (0,-t) (1-s,0) u.val := by
    rw [← hu']
    exact (crossingCoordinates_affine o (b-a) (d-c) c b u.val).trans (by
      change segmentPoint (F c) (F b) u.val=_
      rw [hFc,hFb])
  have hrightF : F x=segmentPoint (-s,0) (0,1-t) v.val := by
    rw [← hv']
    exact (crossingCoordinates_affine o (b-a) (d-c) a d v.val).trans (by
      change segmentPoint (F a) (F d) v.val=_
      rw [hFa,hFd])
  have hl : 0 < (F x).1-(F x).2 := by
    rw [hleftF]
    have hh := convex_combination_pos t (1-s) u.val ht.1 (sub_pos.mpr hs.2) u.property
    dsimp [segmentPoint]
    nlinarith
  have hr : (F x).1-(F x).2 < 0 := by
    rw [hrightF]
    have hh := convex_combination_pos s (1-t) v.val hs.1 (sub_pos.mpr ht.2) v.property
    dsimp [segmentPoint]
    nlinarith
  exact hl.not_ge hr.le
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
def alternatingPath (a b : ℕ → Plane) (p : ∀ i, Path (a i) (b i))
    (q : ∀ i, Path (b i) (a (i+1))) : (n : ℕ) → Path (a 0) (b n)
  | 0 => p 0
  | n+1 => ((alternatingPath a b p q n).trans (q n)).trans (p (n+1))
theorem alternatingPath_range_iff (a b : ℕ → Plane) (p : ∀ i, Path (a i) (b i))
    (q : ∀ i, Path (b i) (a (i+1))) : (n : ℕ) → ∀ x,
    x ∈ Set.range (alternatingPath a b p q n) ↔
      (∃ i, i ≤ n ∧ x ∈ Set.range (p i)) ∨ (∃ i, i < n ∧ x ∈ Set.range (q i))
  | 0, x => by
    constructor
    · intro h
      exact Or.inl ⟨0,le_rfl,h⟩
    · rintro (⟨i,hi,h⟩ | ⟨i,hi,h⟩)
      · have he : i=0 := by omega
        subst i
        exact h
      · omega
  | n+1, x => by
    rw [alternatingPath,Path.trans_range,Path.trans_range,Set.mem_union,Set.mem_union,
      alternatingPath_range_iff a b p q n]
    constructor
    · intro hx
      rcases hx with hx | hx
      · rcases hx with hx | hx
        · rcases hx with ⟨i,hi,h⟩ | ⟨i,hi,h⟩
          · exact Or.inl ⟨i,by omega,h⟩
          · exact Or.inr ⟨i,by omega,h⟩
        · exact Or.inr ⟨n,by omega,hx⟩
      · exact Or.inl ⟨n+1,le_rfl,hx⟩
    · rintro (⟨i,hi,h⟩ | ⟨i,hi,h⟩)
      · by_cases he : i=n+1
        · subst i
          exact Or.inr h
        · exact Or.inl (Or.inl (Or.inl ⟨i,by omega,h⟩))
      · by_cases he : i=n
        · subst i
          exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl (Or.inr ⟨i,by omega,h⟩))
theorem alternatingPath_injective (a b : ℕ → Plane) (p : ∀ i, Path (a i) (b i))
    (q : ∀ i, Path (b i) (a (i+1))) : (n : ℕ) →
    (∀ i, i ≤ n → Function.Injective (p i)) → (∀ i, i < n → Function.Injective (q i)) →
    (∀ i j, i ≤ n → j ≤ n → i ≠ j → Disjoint (Set.range (p i)) (Set.range (p j))) →
    (∀ i j, i < n → j < n → i ≠ j → Disjoint (Set.range (q i)) (Set.range (q j))) →
    (∀ i j, i ≤ n → j < n → ∀ x, x ∈ Set.range (p i) → x ∈ Set.range (q j) →
      (i=j ∧ x=b j) ∨ (i=j+1 ∧ x=a (j+1))) →
    Function.Injective (alternatingPath a b p q n)
  | 0, hp, _, _, _, _ => hp 0 le_rfl
  | n+1, hp, hq, hpp, hqq, hpq => by
    have hprev : Function.Injective (alternatingPath a b p q n) :=
      alternatingPath_injective a b p q n (fun i hi => hp i (by omega))
        (fun i hi => hq i (by omega)) (fun i j hi hj => hpp i j (by omega) (by omega))
        (fun i j hi hj => hqq i j (by omega) (by omega))
        (fun i j hi hj => hpq i j (by omega) (by omega))
    have hfirst : Function.Injective ((alternatingPath a b p q n).trans (q n)) := by
      apply path_trans_injective _ _ hprev (hq n (by omega))
      intro x hx hy
      rcases (alternatingPath_range_iff a b p q n x).mp hx with ⟨i,hi,hh⟩ | ⟨i,hi,hh⟩
      · rcases hpq i n (by omega) (by omega) x hh hy with ⟨he,hx⟩ | ⟨he,hx⟩
        · exact hx
        · omega
      · exact False.elim (Set.disjoint_left.mp (hqq i n (by omega) (by omega) (by omega)) hh hy)
    apply path_trans_injective _ _ hfirst (hp (n+1) le_rfl)
    intro x hx hy
    rw [Path.trans_range] at hx
    rcases hx with hx | hx
    · rcases (alternatingPath_range_iff a b p q n x).mp hx with ⟨i,hi,hh⟩ | ⟨i,hi,hh⟩
      · exact False.elim (Set.disjoint_left.mp (hpp i (n+1) (by omega) le_rfl (by omega)) hh hy)
      · rcases hpq (n+1) i le_rfl (by omega) x hy hh with ⟨he,hx⟩ | ⟨he,hx⟩ <;> omega
    · rcases hpq (n+1) n le_rfl (by omega) x hy hx with ⟨he,hx⟩ | ⟨he,hx⟩
      · omega
      · exact hx
end Zarankiewicz
end
end OAI
end
section
namespace OAI
namespace Zarankiewicz
def parameterNeighborhood (t : unitInterval) (δ : ℝ) : Set unitInterval :=
  {s | |s.val-t.val| < δ}
theorem parameterNeighborhood_open (t : unitInterval) (δ : ℝ) :
    IsOpen (parameterNeighborhood t δ) := by
  apply isOpen_lt _ continuous_const
  fun_prop
theorem parameterNeighborhood_between (t : unitInterval) (δ : ℝ)
    (u v w : unitInterval) (hu : u ∈ parameterNeighborhood t δ)
    (hv : v ∈ parameterNeighborhood t δ) (huw : u ≤ w) (hwv : w ≤ v) :
    w ∈ parameterNeighborhood t δ := by
  change |w.val-t.val| < δ
  change |u.val-t.val| < δ at hu
  change |v.val-t.val| < δ at hv
  rw [abs_lt] at hu hv ⊢
  have h₁ : u.val ≤ w.val := huw
  have h₂ : w.val ≤ v.val := hwv
  constructor <;> linarith
theorem parameterNeighborhood_ordered (a b : unitInterval) (δ : ℝ) (hδ : 0 < δ)
    (hab : a < b) (hd : Disjoint (parameterNeighborhood a δ) (parameterNeighborhood b δ))
    (u v : unitInterval) (hu : u ∈ parameterNeighborhood a δ)
    (hv : v ∈ parameterNeighborhood b δ) : u < v := by
  by_contra hn
  have hvu : v ≤ u := le_of_not_gt hn
  have ha : a ∈ parameterNeighborhood a δ := by simpa [parameterNeighborhood] using hδ
  have hb : b ∈ parameterNeighborhood b δ := by simpa [parameterNeighborhood] using hδ
  by_cases hva : v ≤ a
  · exact Set.disjoint_left.mp hd ha (parameterNeighborhood_between b δ v b a hv hb hva hab.le)
  · have hav : a ≤ v := (lt_of_not_ge hva).le
    exact Set.disjoint_left.mp hd (parameterNeighborhood_between a δ a u v ha hu hav hvu) hv
theorem finite_parameter_neighborhoods {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ι → unitInterval) (ht : Function.Injective t) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ i, t i ∈ parameterNeighborhood (t i) δ) ∧
      (∀ i j, i ≠ j → Disjoint (closure (parameterNeighborhood (t i) δ))
        (closure (parameterNeighborhood (t j) δ))) := by
  obtain ⟨ε,hε,hsep⟩ := finite_node_separation (fun i => (t i).val)
    (Subtype.val_injective.comp ht)
  let δ := ε/3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hclosed (i : ι) : IsClosed {s : unitInterval | |s.val-(t i).val| ≤ δ} := by
    apply isClosed_le _ continuous_const
    fun_prop
  have hcl (i : ι) : closure (parameterNeighborhood (t i) δ) ⊆
      {s : unitInterval | |s.val-(t i).val| ≤ δ} :=
    closure_minimal (fun s hh => le_of_lt (show |s.val-(t i).val| < δ from hh)) (hclosed i)
  refine ⟨δ,hδ,fun i => by simpa [parameterNeighborhood] using hδ,?_⟩
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hx' := hcl i hx
  have hy' := hcl j hy
  have hg := hsep i j hij
  have htri := abs_sub_le (t i).val x.val (t j).val
  rw [abs_sub_comm (t i).val x.val] at htri
  change |x.val-(t i).val| ≤ δ at hx'
  change |x.val-(t j).val| ≤ δ at hy'
  dsimp [δ] at hx' hy'
  linarith
end Zarankiewicz
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
open scoped Classical Topology
def closedRoundDisk (z : Plane) (r : ℝ) : Set Plane := {x | squaredLength (x-z) ≤ r^2}
theorem dist_le_of_mem_closedRoundDisk (z x : Plane) (r : ℝ) (hr : 0 ≤ r)
    (hx : x ∈ closedRoundDisk z r) : dist x z ≤ r := by
  change (x.1-z.1)^2+(x.2-z.2)^2 ≤ r^2 at hx
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_le_iff,abs_le,abs_le]
  have h₁ := sq_nonneg (x.1-z.1)
  have h₂ := sq_nonneg (x.2-z.2)
  constructor <;> constructor <;> nlinarith
theorem exists_round_disk_clearance {ι : Type*} [Fintype ι]
    (z : ι → Plane) (K : ι → Set Plane) (hK : ∀ i, IsCompact (K i))
    (hz : ∀ i, z i ∉ K i) :
    ∃ r : ℝ, 0 < r ∧ ∀ i, Disjoint (closedRoundDisk (z i) r) (K i) := by
  have hex (i : ι) : ∃ ε : ℝ, 0 < ε ∧ Metric.ball (z i) ε ⊆ (K i)ᶜ :=
    Metric.mem_nhds_iff.mp ((hK i).isClosed.isOpen_compl.mem_nhds (hz i))
  choose radius hpos hclear using hex
  obtain ⟨r,hr,hbound⟩ := finite_positive_lower_bound Finset.univ radius (fun i _ => hpos i)
  refine ⟨r,hr,?_⟩
  intro i
  apply Set.disjoint_left.mpr
  intro x hx hmem
  have hd := dist_le_of_mem_closedRoundDisk (z i) x r hr.le hx
  exact hclear i (hd.trans_lt (hbound i (Finset.mem_univ _))) hmem
theorem exists_disjoint_round_disks {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → Plane) (hz : Function.Injective z) :
    ∃ r : ℝ, 0 < r ∧ ∀ i j, i ≠ j → Disjoint (closedRoundDisk (z i) r) (closedRoundDisk (z j) r) := by
  obtain ⟨δ,hδ,hgap⟩ := finite_positive_lower_bound
    (Finset.univ.filter (fun ij : ι × ι => ij.1 ≠ ij.2)) (fun ij => dist (z ij.1) (z ij.2)) (by
      intro ij hij
      exact dist_pos.mpr (hz.ne (Finset.mem_filter.mp hij).2))
  refine ⟨δ/3,by positivity,?_⟩
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  have h₁ := dist_le_of_mem_closedRoundDisk (z i) x (δ/3) (by positivity) hx
  have h₂ := dist_le_of_mem_closedRoundDisk (z j) x (δ/3) (by positivity) hy
  have htri := dist_triangle (z i) x (z j)
  rw [dist_comm (z i) x] at htri
  have hg := hgap (i,j) (by simpa using hij)
  linarith
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem closedRoundDisk_mono (z : Plane) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    closedRoundDisk z r ⊆ closedRoundDisk z s := by
  intro x hx
  change squaredLength (x-z) ≤ r^2 at hx
  change squaredLength (x-z) ≤ s^2
  nlinarith
theorem finite_curve_mark_isolation {E M : Type*} [Fintype E] [Fintype M] [DecidableEq M]
    (γ : E → unitInterval → Plane) (hγ : ∀ e, Continuous (γ e))
    (mark : M → Plane) (hm : Function.Injective mark)
    (O : E → M → Set unitInterval) (hO : ∀ e k, IsOpen (O e k))
    (hvisit : ∀ e k t, γ e t=mark k → t ∈ O e k) :
    ∃ r : ℝ, 0 < r ∧
      (∀ k l, k ≠ l → Disjoint (closedRoundDisk (mark k) r) (closedRoundDisk (mark l) r)) ∧
      (∀ e k t, γ e t ∈ closedRoundDisk (mark k) r → t ∈ O e k) := by
  let K : E × M → Set Plane := fun ek => γ ek.1 '' (O ek.1 ek.2)ᶜ
  have hK (ek : E × M) : IsCompact (K ek) :=
    (hO ek.1 ek.2).isClosed_compl.isCompact.image (hγ ek.1)
  have hnot (ek : E × M) : mark ek.2 ∉ K ek := by
    rintro ⟨t,ht,he⟩
    exact ht (hvisit ek.1 ek.2 t he)
  obtain ⟨ρ,hρ,hclear⟩ := exists_round_disk_clearance (fun ek : E × M => mark ek.2) K hK hnot
  obtain ⟨σ,hσ,hdisjoint⟩ := exists_disjoint_round_disks mark hm
  refine ⟨min ρ σ,lt_min hρ hσ,?_,?_⟩
  · intro k l hkl
    exact (hdisjoint k l hkl).mono
      (closedRoundDisk_mono _ (le_of_lt (lt_min hρ hσ)) (min_le_right _ _))
      (closedRoundDisk_mono _ (le_of_lt (lt_min hρ hσ)) (min_le_right _ _))
  · intro e k t ht
    by_contra hn
    have hd : γ e t ∈ closedRoundDisk (mark k) ρ :=
      closedRoundDisk_mono _ (le_of_lt (lt_min hρ hσ)) (min_le_left _ _) ht
    exact Set.disjoint_left.mp (hclear (e,k)) hd ⟨t,hn,rfl⟩
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem finite_injective_curve_disk_isolation {E M : Type*}
    [Fintype E] [Fintype M] [DecidableEq M]
    (γ : E → unitInterval → Plane) (hc : ∀ e, Continuous (γ e))
    (hi : ∀ e, Function.Injective (γ e)) (mark : M → Plane) (hm : Function.Injective mark) :
    ∃ δ : E → ℝ, ∃ r : ℝ, (∀ e, 0 < δ e) ∧ 0 < r ∧
      (∀ k l, k ≠ l → Disjoint (closedRoundDisk (mark k) r) (closedRoundDisk (mark l) r)) ∧
      (∀ e k t, γ e t ∈ closedRoundDisk (mark k) r →
        ∃ u : unitInterval, γ e u=mark k ∧ t ∈ parameterNeighborhood u (δ e)) ∧
      (∀ e u v, γ e u ∈ Set.range mark → γ e v ∈ Set.range mark → u ≠ v →
        Disjoint (closure (parameterNeighborhood u (δ e)))
          (closure (parameterNeighborhood v (δ e)))) := by
  have hfinite (e : E) : ((γ e) ⁻¹' Set.range mark).Finite :=
    Set.Finite.preimage (hi e).injOn (Set.finite_range mark)
  have hex (e : E) : ∃ δ : ℝ, 0 < δ ∧
      ∀ u v, γ e u ∈ Set.range mark → γ e v ∈ Set.range mark → u ≠ v →
        Disjoint (closure (parameterNeighborhood u δ)) (closure (parameterNeighborhood v δ)) := by
    let S := (γ e) ⁻¹' Set.range mark
    let : Fintype S := (hfinite e).fintype
    let : DecidableEq S := Classical.decEq _
    obtain ⟨δ,hδ,_,hd⟩ := finite_parameter_neighborhoods (fun t : S => t.val) Subtype.val_injective
    refine ⟨δ,hδ,?_⟩
    intro u v hu hv huv
    exact hd ⟨u,hu⟩ ⟨v,hv⟩ (fun he => huv (congrArg Subtype.val he))
  choose δ hδ hseparate using hex
  let O : E → M → Set unitInterval := fun e k =>
    {t | ∃ u, γ e u=mark k ∧ t ∈ parameterNeighborhood u (δ e)}
  have hO (e : E) (k : M) : IsOpen (O e k) := by
    apply isOpen_iff_mem_nhds.mpr
    rintro t ⟨u,hu,ht⟩
    exact Filter.mem_of_superset ((parameterNeighborhood_open u (δ e)).mem_nhds ht)
      (fun s hs => ⟨u,hu,hs⟩)
  obtain ⟨r,hr,hdisks,hvisits⟩ := finite_curve_mark_isolation γ hc mark hm O hO (by
    intro e k t ht
    exact ⟨t,ht,by simpa [parameterNeighborhood] using hδ e⟩)
  exact ⟨δ,r,hδ,hr,hdisks,hvisits,hseparate⟩
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem sublevel_passage_extrema (f : ℝ → ℝ) (hf : Continuous f) (r τ : ℝ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hvisit : f τ < r) :
    ∃ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 ∧ b ∈ Set.Icc (0 : ℝ) 1 ∧
      a ≤ τ ∧ τ ≤ b ∧ f a ≤ r ∧ f b ≤ r ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≤ r → a ≤ t ∧ t ≤ b) ∧
      (0 < a → f a=r) ∧ (b < 1 → f b=r) ∧
      (0 < τ → a < τ) ∧ (τ < 1 → τ < b) := by
  let S : Set ℝ := Set.Icc 0 1 ∩ {t | f t ≤ r}
  have hS : IsCompact S := isCompact_Icc.inter_right (isClosed_le hf continuous_const)
  have hτS : τ ∈ S := ⟨hτ,hvisit.le⟩
  obtain ⟨a,ha⟩ := hS.exists_isLeast ⟨τ,hτS⟩
  obtain ⟨b,hb⟩ := hS.exists_isGreatest ⟨τ,hτS⟩
  have hfa (ha0 : 0 < a) : f a=r := by
    have hf0 : r < f 0 := by
      apply lt_of_not_ge
      intro h
      have hh := ha.2 (show (0 : ℝ) ∈ S from ⟨⟨le_rfl,zero_le_one⟩,h⟩)
      linarith
    apply le_antisymm ha.1.2
    by_contra hn
    have hlt : f a < r := lt_of_not_ge hn
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc' ha.1.1.1 hf.continuousOn ⟨hlt.le,hf0.le⟩
    have hmem : t ∈ S := ⟨⟨ht.1,ht.2.trans ha.1.1.2⟩,he.le⟩
    have hta : t=a := le_antisymm ht.2 (ha.2 hmem)
    rw [hta] at he
    exact hlt.ne he
  have hfb (hb1 : b < 1) : f b=r := by
    have hf1 : r < f 1 := by
      apply lt_of_not_ge
      intro h
      have hh := hb.2 (show (1 : ℝ) ∈ S from ⟨⟨zero_le_one,le_rfl⟩,h⟩)
      linarith
    apply le_antisymm hb.1.2
    by_contra hn
    have hlt : f b < r := lt_of_not_ge hn
    obtain ⟨t,ht,he⟩ := intermediate_value_Icc hb.1.1.2 hf.continuousOn ⟨hlt.le,hf1.le⟩
    have hmem : t ∈ S := ⟨⟨hb.1.1.1.trans ht.1,ht.2⟩,he.le⟩
    have htb : t=b := le_antisymm (hb.2 hmem) ht.1
    rw [htb] at he
    exact hlt.ne he
  refine ⟨a,b,ha.1.1,hb.1.1,ha.2 hτS,hb.2 hτS,ha.1.2,hb.1.2,
    fun t ht hh => ⟨ha.2 ⟨ht,hh⟩,hb.2 ⟨ht,hh⟩⟩,hfa,hfb,?_,?_⟩
  · intro ht0
    apply lt_of_le_of_ne (ha.2 hτS)
    intro he
    have h := hfa (he.symm ▸ ht0)
    rw [he] at h
    exact hvisit.ne h
  · intro ht1
    apply lt_of_le_of_ne (hb.2 hτS)
    intro he
    have h := hfb (he ▸ ht1)
    rw [← he] at h
    exact hvisit.ne h
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem continuous_path_squared_distance {a b : Plane} (γ : Path a b) (z : Plane) :
    Continuous (fun t : ℝ => squaredLength (γ.extend t-z)) := by
  unfold squaredLength
  fun_prop
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
structure DiskPassage {a b : Plane} (γ : Path a b) (z : Plane) (r : ℝ) (τ : unitInterval) where
  enter : unitInterval
  leave : unitInterval
  enter_le_mark : enter ≤ τ
  mark_le_leave : τ ≤ leave
  enter_mem : γ enter ∈ closedRoundDisk z r
  leave_mem : γ leave ∈ closedRoundDisk z r
  all_visits : ∀ t, γ t ∈ closedRoundDisk z r → enter ≤ t ∧ t ≤ leave
  enter_boundary : 0 < enter → squaredLength (γ enter-z)=r^2
  leave_boundary : leave < 1 → squaredLength (γ leave-z)=r^2
  strict_enter : 0 < τ → enter < τ
  strict_leave : τ < 1 → τ < leave
theorem nonempty_diskPassage {a b : Plane} (γ : Path a b) (z : Plane) (r : ℝ)
    (τ : unitInterval) (hτ : squaredLength (γ τ-z) < r^2) :
    Nonempty (DiskPassage γ z r τ) := by
  obtain ⟨u,v,hu,hv,huτ,hτv,hfu,hfv,hall,hbu,hbv,hsu,hsv⟩ := sublevel_passage_extrema
    (fun t => squaredLength (γ.extend t-z)) (continuous_path_squared_distance γ z) (r^2) τ.val τ.property
    (by simpa using hτ)
  let u' : unitInterval := ⟨u,hu⟩
  let v' : unitInterval := ⟨v,hv⟩
  have heu : γ.extend u=γ u' := γ.extend_extends' u'
  have hev : γ.extend v=γ v' := γ.extend_extends' v'
  rw [heu] at hfu hbu
  rw [hev] at hfv hbv
  exact ⟨{
    enter := u'
    leave := v'
    enter_le_mark := huτ
    mark_le_leave := hτv
    enter_mem := hfu
    leave_mem := hfv
    all_visits := fun t ht => hall t.val t.property (by simpa [closedRoundDisk] using ht)
    enter_boundary := hbu
    leave_boundary := hbv
    strict_enter := hsu
    strict_leave := hsv }⟩
namespace DiskPassage
variable {a b z : Plane} {γ : Path a b} {r : ℝ} {τ : unitInterval}
theorem enter_lt_leave (P : DiskPassage γ z r τ) : P.enter < P.leave := by
  by_cases ht : τ=0
  · exact P.enter_le_mark.trans_lt (P.strict_leave (by rw [ht]; exact zero_lt_one))
  · exact (P.strict_enter (lt_of_le_of_ne (show 0 ≤ τ from τ.property.1) (Ne.symm ht))).trans_le P.mark_le_leave
end DiskPassage
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem diskPassage_separated {a b z w : Plane} {γ : Path a b} {r δ : ℝ}
    {s t : unitInterval} (P : DiskPassage γ z r s) (Q : DiskPassage γ w r t)
    (hst : s < t) (hδ : 0 < δ)
    (hd : Disjoint (closure (parameterNeighborhood s δ)) (closure (parameterNeighborhood t δ)))
    (hP : P.leave ∈ parameterNeighborhood s δ) (hQ : Q.enter ∈ parameterNeighborhood t δ) :
    P.leave < Q.enter :=
  parameterNeighborhood_ordered s t δ hδ hst (hd.mono subset_closure subset_closure) P.leave Q.enter hP hQ
def retainedSubarc {a b : Plane} (γ : Path a b) {k : ℕ}
    (τ : Fin (k+1) → unitInterval) (r : ℝ)
    (P : ∀ i, DiskPassage γ (γ (τ i)) r (τ i)) (i : Fin k) :
    Path (γ (P i.castSucc).leave) (γ (P i.succ).enter) :=
  pathSubarc γ (P i.castSucc).leave (P i.succ).enter
theorem ordered_passage_enter_strictMono {a b : Plane} (γ : Path a b) {k : ℕ}
    (τ : Fin (k+1) → unitInterval) (r : ℝ) (P : ∀ i, DiskPassage γ (γ (τ i)) r (τ i))
    (hsep : ∀ i j, i < j → (P i).leave < (P j).enter) :
    StrictMono (fun i => (P i).enter) := by
  intro i j hij
  exact (P i).enter_lt_leave.trans (hsep i j hij)
theorem ordered_passage_leave_strictMono {a b : Plane} (γ : Path a b) {k : ℕ}
    (τ : Fin (k+1) → unitInterval) (r : ℝ) (P : ∀ i, DiskPassage γ (γ (τ i)) r (τ i))
    (hsep : ∀ i j, i < j → (P i).leave < (P j).enter) :
    StrictMono (fun i => (P i).leave) := by
  intro i j hij
  exact (hsep i j hij).trans (P j).enter_lt_leave
theorem retained_interval_no_mark {a b : Plane} (γ : Path a b) {k : ℕ}
    (τ : Fin (k+1) → unitInterval) (hτ : StrictMono τ) (h0 : τ 0=0)
    (h1 : τ (Fin.last k)=1) (r : ℝ) (P : ∀ i, DiskPassage γ (γ (τ i)) r (τ i))
    (i : Fin k) (t : unitInterval)
    (ht : t ∈ Set.Icc (P i.castSucc).leave (P i.succ).enter) : t ∉ Set.range τ := by
  rintro ⟨j,hj⟩
  have hleft : τ i.castSucc < 1 := by
    rw [← h1]
    exact hτ (show i.castSucc < Fin.last k from i.isLt)
  have hright : 0 < τ i.succ := by
    rw [← h0]
    exact hτ (show (0 : Fin (k+1)) < i.succ by change 0 < i.val+1; omega)
  by_cases hji : j ≤ i.castSucc
  · have hh := (hτ.monotone hji).trans_lt ((P i.castSucc).strict_leave hleft)
    exact hh.not_ge (ht.1.trans_eq hj.symm)
  · have hij : i.succ ≤ j := by
      change i.val+1 ≤ j.val
      have hh : ¬ j.val ≤ i.val := hji
      omega
    have hh := ((P i.succ).strict_enter hright).trans_le (hτ.monotone hij)
    exact hh.not_ge (hj.trans_le ht.2)
theorem retained_interval_pair_disjoint {a b : Plane} (γ : Path a b) {k : ℕ}
    (τ : Fin (k+1) → unitInterval) (r : ℝ) (P : ∀ i, DiskPassage γ (γ (τ i)) r (τ i))
    (hsep : ∀ i j, i < j → (P i).leave < (P j).enter)
    (i j : Fin k) (hij : i < j) :
    Disjoint (Set.Icc (P i.castSucc).leave (P i.succ).enter)
      (Set.Icc (P j.castSucc).leave (P j.succ).enter) := by
  have hi : i.succ ≤ j.castSucc := by change i.val+1 ≤ j.val; omega
  have hgap := ((ordered_passage_enter_strictMono γ τ r P hsep).monotone hi).trans_lt (P j.castSucc).enter_lt_leave
  apply Set.disjoint_left.mpr
  intro t ht hu
  exact hgap.not_ge (hu.1.trans ht.2)
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
open scoped Topology
theorem exists_radial_tip_collar (z x : Plane) (r : ℝ) (hr : 0 < r)
    (hx : squaredLength (x-z)=r^2) (U : Set Plane) (hU : IsOpen U) (hxu : x ∈ U) :
    ∃ α ρ : ℝ, 0 < α ∧ 0 < ρ ∧
      segment ℝ x (x+α • (x-z)) ⊆ U ∩ insert x {y | r^2 < squaredLength (y-z)} ∧
      (∀ y, dist y x < ρ → r^2 < squaredLength (y-z) →
        segment ℝ (x+α • (x-z)) y ⊆ U ∩ {p | r^2 < squaredLength (p-z)}) := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU x hxu
  have hmove : Continuous (fun α : ℝ => x+α • (x-z)) := by fun_prop
  have hevent : ∀ᶠ α : ℝ in 𝓝 0, x+α • (x-z) ∈ Metric.ball x ε :=
    hmove.continuousAt.preimage_mem_nhds (by simpa using Metric.ball_mem_nhds x hε)
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp hevent
  let α := δ/2
  have hα : 0 < α := by dsimp [α]; positivity
  have htip : x+α • (x-z) ∈ Metric.ball x ε := hd (by
    rw [Real.dist_eq,sub_zero,abs_of_pos hα]
    dsimp [α]
    linarith)
  have hdpos : 0 < dot2 (x-z) ((x+α • (x-z))-x) := by
    rw [radial_tip_dot,hx]
    exact mul_pos hα (sq_pos_of_pos hr)
  have hdot : Continuous (fun y : Plane => dot2 (y-z) ((x+α • (x-z))-y)) := by
    unfold dot2
    fun_prop
  have hev : ∀ᶠ y : Plane in 𝓝 x, 0 < dot2 (y-z) ((x+α • (x-z))-y) :=
    continuousAt_const.eventually_lt hdot.continuousAt hdpos
  obtain ⟨σ,hσ,hσdot⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨α,min ε σ,hα,lt_min hε hσ,?_,?_⟩
  · apply Set.subset_inter
    · exact ((convex_ball x ε).segment_subset (Metric.mem_ball_self hε) htip).trans hball
    · exact radial_spur_exterior z x r α hx hr hα
  · intro y hy hout
    apply Set.subset_inter
    · exact ((convex_ball x ε).segment_subset htip (hy.trans_le (min_le_left _ _))).trans hball
    · rw [segment_symm]
      exact exterior_segment_of_dot z y (x+α • (x-z)) r hout
        (hσdot (hy.trans_le (min_le_right _ _))).le
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
def outsideDisks {ι : Type*} (z : ι → Plane) (r : ℝ) : Set Plane :=
  {x | ∀ i, r^2 < squaredLength (x-z i)}
theorem isOpen_disk_exterior (z : Plane) (r : ℝ) :
    IsOpen {x | r^2 < squaredLength (x-z)} := by
  apply isOpen_lt continuous_const
  unfold squaredLength
  fun_prop
theorem isOpen_outsideDisks {ι : Type*} [Finite ι] (z : ι → Plane) (r : ℝ) :
    IsOpen (outsideDisks z r) := by
  have he : outsideDisks z r=⋂ i, {x | r^2 < squaredLength (x-z i)} := by
    ext x
    simp [outsideDisks]
  rw [he]
  exact isOpen_iInter_of_finite (fun i => isOpen_disk_exterior (z i) r)
theorem exists_finite_disk_collar {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → Plane) (r : ℝ) (hr : 0 < r)
    (hd : ∀ i j, i ≠ j → Disjoint (closedRoundDisk (z i) r) (closedRoundDisk (z j) r))
    (k : ι) (x : Plane) (hx : squaredLength (x-z k)=r^2)
    (U : Set Plane) (hU : IsOpen U) (hxu : x ∈ U) :
    ∃ α ρ : ℝ, 0 < α ∧ 0 < ρ ∧
      segment ℝ x (x+α • (x-z k)) ⊆ U ∩ insert x (outsideDisks z r) ∧
      (∀ y, dist y x < ρ → y ∈ outsideDisks z r →
        segment ℝ (x+α • (x-z k)) y ⊆ U ∩ outsideDisks z r) := by
  let V : Set Plane := U ∩ ⋂ j : {j : ι // j ≠ k}, {y | r^2 < squaredLength (y-z j.val)}
  have hV : IsOpen V := hU.inter (isOpen_iInter_of_finite (fun j => isOpen_disk_exterior (z j.val) r))
  have hxV : x ∈ V := by
    refine ⟨hxu,Set.mem_iInter.mpr (fun j => ?_)⟩
    change r^2 < squaredLength (x-z j.val)
    apply lt_of_not_ge
    intro hh
    exact Set.disjoint_left.mp (hd k j.val (Ne.symm j.property)) (show x ∈ closedRoundDisk (z k) r from hx.le) hh
  obtain ⟨α,ρ,hα,hρ,hspur,hnear⟩ := exists_radial_tip_collar (z k) x r hr hx V hV hxV
  have hout : V ∩ {p | r^2 < squaredLength (p-z k)} ⊆ U ∩ outsideDisks z r := by
    intro p hp
    refine ⟨hp.1.1,fun j => ?_⟩
    by_cases he : j=k
    · simpa [he] using hp.2
    · exact Set.mem_iInter.mp hp.1.2 ⟨j,he⟩
  refine ⟨α,ρ,hα,hρ,?_,?_⟩
  · intro p hp
    obtain ⟨hpV,hpx | hpout⟩ := hspur hp
    · exact ⟨hpV.1,Or.inl hpx⟩
    · exact ⟨hpV.1,Or.inr (hout ⟨hpV,hpout⟩).2⟩
  · intro y hy hyout
    exact (hnear y hy (hyout k)).trans hout
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.DrawingPassages
end Zarankiewicz.DrawingPassages
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.DrawingPassages
end Zarankiewicz.DrawingPassages
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
open scoped Topology
theorem path_near_endpoints {a b : Plane} (γ : Path a b) (ρ σ : ℝ)
    (hρ : 0 < ρ) (hσ : 0 < σ) :
    ∃ u v : unitInterval, 0 < u ∧ u < v ∧ v < 1 ∧
      dist (γ u) a < ρ ∧ dist (γ v) b < σ := by
  have he0 : ∀ᶠ t : ℝ in 𝓝 0, γ.extend t ∈ Metric.ball a ρ :=
    γ.continuous_extend.continuousAt.preimage_mem_nhds (by simpa using Metric.ball_mem_nhds a hρ)
  have he1 : ∀ᶠ t : ℝ in 𝓝 1, γ.extend t ∈ Metric.ball b σ :=
    γ.continuous_extend.continuousAt.preimage_mem_nhds (by simpa using Metric.ball_mem_nhds b hσ)
  obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp he0
  obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp he1
  let p := min (δ/2) (1/4)
  let q := min (ε/2) (1/4)
  have hp : 0 < p := lt_min (by positivity) (by norm_num)
  have hq : 0 < q := lt_min (by positivity) (by norm_num)
  have hp4 : p ≤ 1/4 := min_le_right _ _
  have hq4 : q ≤ 1/4 := min_le_right _ _
  have hpd : p < δ := (min_le_left _ _).trans_lt (by linarith)
  have hqe : q < ε := (min_le_left _ _).trans_lt (by linarith)
  let u : unitInterval := ⟨p,hp.le,by linarith⟩
  let v : unitInterval := ⟨1-q,by linarith,by linarith⟩
  have hu : γ.extend p ∈ Metric.ball a ρ := hd (by simpa [Real.dist_eq,abs_of_pos hp] using hpd)
  have hv : γ.extend (1-q) ∈ Metric.ball b σ := he (by
    simpa [Real.dist_eq,abs_of_pos hq] using hqe)
  rw [show γ.extend p=γ u from γ.extend_extends' u] at hu
  rw [show γ.extend (1-q)=γ v from γ.extend_extends' v] at hv
  exact ⟨u,v,hp,(by change p < 1-q; linarith),(by change 1-q < 1; linarith),hu,hv⟩
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem finite_compact_corridors {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K O : ι → Set Plane) (hK : ∀ i, IsCompact (K i))
    (hd : ∀ i j, i ≠ j → Disjoint (K i) (K j))
    (hO : ∀ i, IsOpen (O i)) (hKO : ∀ i, K i ⊆ O i) :
    ∃ U : ι → Set Plane, (∀ i, IsOpen (U i)) ∧ (∀ i, K i ⊆ U i) ∧
      (∀ i, U i ⊆ O i) ∧ (∀ i j, i ≠ j → Disjoint (U i) (U j)) := by
  have hex (i j : ι) : ∃ A B : Set Plane, IsOpen A ∧ IsOpen B ∧ K i ⊆ A ∧ K j ⊆ B ∧
      (i ≠ j → Disjoint A B) := by
    by_cases he : i=j
    · exact ⟨Set.univ,Set.univ,isOpen_univ,isOpen_univ,Set.subset_univ _,Set.subset_univ _,fun hn => False.elim (hn he)⟩
    · obtain ⟨A,B,hA,hB,hi,hj,hab⟩ := normal_separation (hK i).isClosed (hK j).isClosed (hd i j he)
      exact ⟨A,B,hA,hB,hi,hj,fun _ => hab⟩
  choose A B hA hB hKA hKB hAB using hex
  let U : ι → Set Plane := fun i => O i ∩ ⋂ j, A i j ∩ B j i
  refine ⟨U,?_,?_,?_,?_⟩
  · intro i
    exact (hO i).inter (isOpen_iInter_of_finite (fun j => (hA i j).inter (hB j i)))
  · intro i x hx
    exact ⟨hKO i hx,Set.mem_iInter.mpr (fun j => ⟨hKA i j hx,hKB j i hx⟩)⟩
  · intro i x hx
    exact hx.1
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp (hAB i j hij)
      (Set.mem_iInter.mp hx.2 j).1 (Set.mem_iInter.mp hy.2 i).2
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem exists_simple_polygonalChain {O : Set Plane} {a b : Plane} (hab : a ≠ b)
    (h : Nonempty (PolygonalChain O a b)) :
    ∃ P : PolygonalChain O a b, Function.Injective P.path ∧ Set.range P.path ⊆ O := by
  obtain ⟨P,hmin⟩ := exists_minimum_polygonalChain h
  exact ⟨P,P.minimum_path_injective hab hmin,P.path_range_subset⟩
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
def PolygonalChain.widen {S T : Set Plane} {a b : Plane} (P : PolygonalChain S a b)
    (hST : S ⊆ T) : PolygonalChain T a b where
  pieces := P.pieces
  vertices := P.vertices
  first := P.first
  last := P.last
  start_mem := hST P.start_mem
  inside := fun i hi => (P.inside i hi).trans hST
theorem simple_path_interior_of_range_insert {a b : Plane} (γ : Path a b)
    (hinj : Function.Injective γ) (O : Set Plane)
    (hrange : Set.range γ ⊆ insert a (insert b O))
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) : γ t ∈ O := by
  rcases hrange ⟨t,rfl⟩ with ha | hb | ho
  · have he := hinj (ha.trans γ.source.symm)
    exact False.elim (ht.1.ne he.symm)
  · have he := hinj (hb.trans γ.target.symm)
    exact False.elim (ht.2.ne he)
  · exact ho
theorem polygonal_replacement_with_spurs (O : Set Plane) (hO : IsOpen O)
    (a a' b' b : Plane) (hab : a ≠ b) (γ : Path a' b')
    (hγ : ∀ t, γ t ∈ O)
    (ha : segment ℝ a a' ⊆ insert a (insert b O))
    (hb : segment ℝ b' b ⊆ insert a (insert b O)) :
    ∃ P : PolygonalChain (insert a (insert b O)) a b,
      Function.Injective P.path ∧
      (∀ t : unitInterval, t ∈ Set.Ioo (0 : unitInterval) 1 → P.path t ∈ O) := by
  obtain ⟨Q⟩ := nonempty_polygonalChain_of_path γ O hO hγ
  let S := insert a (insert b O)
  let Q' : PolygonalChain S a' b' := Q.widen (fun _ hx => Or.inr (Or.inr hx))
  let L : PolygonalChain S a a' := PolygonalChain.single S a a' (Or.inl rfl) ha
  let R : PolygonalChain S b' b := PolygonalChain.single S b' b
    (Or.inr (Or.inr (by simpa using hγ 1))) hb
  obtain ⟨P,hP,hR⟩ := exists_simple_polygonalChain hab ⟨(L.join Q').join R⟩
  exact ⟨P,hP,fun t ht => simple_path_interior_of_range_insert P.path hP O hR t ht⟩
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem exterior_arc_polygonal_replacement {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : ι → Plane) (r : ℝ) (hr : 0 < r)
    (hd : ∀ i j, i ≠ j → Disjoint (closedRoundDisk (z i) r) (closedRoundDisk (z j) r))
    (k l : ι) (a b : Plane) (hab : a ≠ b)
    (ha : squaredLength (a-z k)=r^2) (hb : squaredLength (b-z l)=r^2)
    (γ : Path a b) (U : Set Plane) (hU : IsOpen U) (hγU : ∀ t, γ t ∈ U)
    (hγout : ∀ t, t ∈ Set.Ioo (0 : unitInterval) 1 → γ t ∈ outsideDisks z r) :
    ∃ P : PolygonalChain U a b, Function.Injective P.path ∧
      (∀ t, t ∈ Set.Ioo (0 : unitInterval) 1 → P.path t ∈ outsideDisks z r) := by
  obtain ⟨α,ρ,hα,hρ,hspurA,hnearA⟩ := exists_finite_disk_collar z r hr hd k a ha U hU
    (by simpa using hγU 0)
  obtain ⟨β,σ,hβ,hσ,hspurB,hnearB⟩ := exists_finite_disk_collar z r hr hd l b hb U hU
    (by simpa using hγU 1)
  obtain ⟨u,v,hu0,huv,hv1,hu,hv⟩ := path_near_endpoints γ ρ σ hρ hσ
  let a' := a+α • (a-z k)
  let b' := b+β • (b-z l)
  let O := U ∩ outsideDisks z r
  have hO : IsOpen O := hU.inter (isOpen_outsideDisks z r)
  have hleft : segment ℝ a' (γ u) ⊆ O := hnearA (γ u) hu (hγout u ⟨hu0,huv.trans hv1⟩)
  have hright : segment ℝ (γ v) b' ⊆ O := by
    rw [segment_symm]
    exact hnearB (γ v) hv (hγout v ⟨hu0.trans huv,hv1⟩)
  have hmiddle : Set.range (pathSubarc γ u v) ⊆ O := by
    rw [pathSubarc_range γ u v huv]
    rintro x ⟨t,ht,rfl⟩
    exact ⟨hγU t,hγout t ⟨hu0.trans_le ht.1,ht.2.trans_lt hv1⟩⟩
  let η : Path a' b' := (Path.segment a' (γ u)).trans
    ((pathSubarc γ u v).trans (Path.segment (γ v) b'))
  have hη : Set.range η ⊆ O := by
    dsimp [η]
    rw [Path.trans_range,Path.trans_range,Path.range_segment,Path.range_segment]
    exact Set.union_subset hleft (Set.union_subset hmiddle hright)
  have hA : segment ℝ a a' ⊆ insert a (insert b O) := by
    intro x hx
    obtain ⟨hxU,hxa | hxout⟩ := hspurA hx
    · exact Or.inl hxa
    · exact Or.inr (Or.inr ⟨hxU,hxout⟩)
  have hB : segment ℝ b' b ⊆ insert a (insert b O) := by
    rw [segment_symm]
    intro x hx
    obtain ⟨hxU,hxb | hxout⟩ := hspurB hx
    · exact Or.inr (Or.inl hxb)
    · exact Or.inr (Or.inr ⟨hxU,hxout⟩)
  obtain ⟨Q,hQ,hQout⟩ := polygonal_replacement_with_spurs O hO a a' b' b hab η
    (fun t => hη ⟨t,rfl⟩) hA hB
  have hSU : insert a (insert b O) ⊆ U := by
    intro x hx
    rcases hx with rfl | rfl | hx
    · simpa using hγU 0
    · simpa using hγU 1
    · exact hx.1
  exact ⟨Q.widen hSU,hQ,fun t ht => (hQout t ht).2⟩
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem finite_exterior_arc_replacements {E M : Type*}
    [Fintype E] [DecidableEq E] [Fintype M] [DecidableEq M]
    (z : M → Plane) (r : ℝ) (hr : 0 < r)
    (hd : ∀ i j, i ≠ j → Disjoint (closedRoundDisk (z i) r) (closedRoundDisk (z j) r))
    (k l : E → M) (a b : E → Plane) (hab : ∀ e, a e ≠ b e)
    (ha : ∀ e, squaredLength (a e-z (k e))=r^2)
    (hb : ∀ e, squaredLength (b e-z (l e))=r^2)
    (γ : ∀ e, Path (a e) (b e))
    (hdisjoint : ∀ e f, e ≠ f → Disjoint (Set.range (γ e)) (Set.range (γ f)))
    (hγ : ∀ e t, t ∈ Set.Ioo (0 : unitInterval) 1 → γ e t ∈ outsideDisks z r) :
    ∃ U : E → Set Plane, ∃ P : ∀ e, PolygonalChain (U e) (a e) (b e),
      (∀ e, IsOpen (U e)) ∧ (∀ e, Function.Injective (P e).path) ∧
      (∀ e t, t ∈ Set.Ioo (0 : unitInterval) 1 → (P e).path t ∈ outsideDisks z r) ∧
      (∀ e f, e ≠ f → Disjoint (Set.range (P e).path) (Set.range (P f).path)) := by
  obtain ⟨U,hU,hKU,_,hUU⟩ := finite_compact_corridors (fun e => Set.range (γ e))
    (fun _ => Set.univ) (fun e => isCompact_range (γ e).continuous) hdisjoint
    (fun _ => isOpen_univ) (fun _ => Set.subset_univ _)
  have hex (e : E) : ∃ P : PolygonalChain (U e) (a e) (b e), Function.Injective P.path ∧
      (∀ t, t ∈ Set.Ioo (0 : unitInterval) 1 → P.path t ∈ outsideDisks z r) :=
    exterior_arc_polygonal_replacement z r hr hd (k e) (l e) (a e) (b e) (hab e)
      (ha e) (hb e) (γ e) (U e) (hU e) (fun t => hKU e ⟨t,rfl⟩) (hγ e)
  choose P hP hR using hex
  exact ⟨U,P,hU,hP,hR,fun e f hef =>
    (hUU e f hef).mono (P e).path_range_subset (P f).path_range_subset⟩
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.DrawingPassages
end Zarankiewicz.DrawingPassages
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.DrawingPassages
end Zarankiewicz.DrawingPassages
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.DrawingPassages
end Zarankiewicz.DrawingPassages
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem spokes_meet_only_at_center (v a b : Plane) (hd : det2 (a-v) (b-v) ≠ 0)
    {x : Plane} (ha : x ∈ segment ℝ v a) (hb : x ∈ segment ℝ v b) : x=v := by
  rw [← Path.range_segment] at ha hb
  obtain ⟨s,hs⟩ := ha
  obtain ⟨t,ht⟩ := hb
  have hs' : segmentPoint v a s.val=x := by simpa [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hs
  have ht' : segmentPoint v b t.val=x := by simpa [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht
  have hp := segment_intersection_parameters_unique v a v b hd s.val t.val 0 0
    (hs'.trans ht'.symm) (by simp)
  rw [hp.1,segmentPoint_zero] at hs'
  exact hs'.symm
theorem spoke_in_open_disk (z v a : Plane) (r : ℝ)
    (hv : squaredLength (v-z) < r^2) (ha : squaredLength (a-z)=r^2)
    (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    squaredLength (segmentPoint v a t-z) < r^2 := by
  have he : squaredLength (segmentPoint v a t-z)=
      (1-t)*squaredLength (v-z)+t*squaredLength (a-z)-t*(1-t)*squaredLength (a-v) := by
    dsimp [squaredLength,segmentPoint]
    ring
  have hpos := mul_pos (sub_pos.mpr ht.2) (sub_pos.mpr hv)
  have hnon : 0 ≤ t*(1-t)*squaredLength (a-v) := by
    apply mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2.le))
    dsimp [squaredLength]
    positivity
  rw [he,ha]
  nlinarith
theorem exists_vertex_disk_point {ι : Type*} [Fintype ι] [DecidableEq ι]
    (z : Plane) (r : ℝ) (hr : 0 < r) (p : ι → Plane) (hp : Function.Injective p)
    (hcircle : ∀ i, squaredLength (p i-z)=r^2) :
    ∃ v : Plane, squaredLength (v-z) < r^2 ∧
      (∀ i, v ≠ p i) ∧ (∀ i j, i ≠ j → det2 (p i-v) (p j-v) ≠ 0) := by
  classical
  let S := {ij : ι × ι // ij.1 ≠ ij.2}
  obtain ⟨v,hv,havoid⟩ := exists_near_avoiding_lines
    (fun ij : S => p ij.val.1) (fun ij : S => p ij.val.2-p ij.val.1)
    (fun ij => sub_ne_zero.mpr (hp.ne (Ne.symm ij.property))) z (r/3) (by positivity)
  have hinside : squaredLength (v-z) < r^2 := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,max_lt_iff,abs_lt,abs_lt] at hv
    have h₁ := mul_pos (sub_pos.mpr hv.1.2) (show 0 < r/3+(v.1-z.1) by linarith [hv.1.1])
    have h₂ := mul_pos (sub_pos.mpr hv.2.2) (show 0 < r/3+(v.2-z.2) by linarith [hv.2.1])
    change (v.1-z.1)^2+(v.2-z.2)^2 < r^2
    nlinarith [sq_pos_of_pos hr]
  refine ⟨v,hinside,?_,?_⟩
  · intro i he
    rw [he,hcircle i] at hinside
    exact lt_irrefl _ hinside
  · intro i j hij
    have he : det2 (p i-v) (p j-v) = -det2 (v-p i) (p j-p i) := by dsimp [det2]; ring
    rw [he]
    exact neg_ne_zero.mpr (havoid ⟨(i,j),hij⟩)
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.DrawingPassages
end Zarankiewicz.DrawingPassages
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
namespace DrawingPassages
end DrawingPassages
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
namespace PolygonalExterior
end PolygonalExterior
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.PolygonalExterior
end Zarankiewicz.PolygonalExterior
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.DrawingPassages
end Zarankiewicz.DrawingPassages
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.DrawingPassages
end DrawingPassages
namespace PolygonalExterior
end PolygonalExterior
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.PolygonalExterior
end Zarankiewicz.PolygonalExterior
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.PolygonalExterior
end Zarankiewicz.PolygonalExterior
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.DrawingPassages
end DrawingPassages
namespace PolygonalExterior
end PolygonalExterior
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.PolygonalExterior
end Zarankiewicz.PolygonalExterior
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.DrawingPassages
end DrawingPassages
namespace PolygonalExterior
end PolygonalExterior
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.PolygonalExterior
end Zarankiewicz.PolygonalExterior
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem transverse_segment_intersection_subsingleton (a b c d : Plane)
    (h : SegmentPairTransverse a b c d) :
    (Set.range (Path.segment a b) ∩ Set.range (Path.segment c d)).Subsingleton := by
  intro x hx y hy
  obtain ⟨⟨s,hs⟩,⟨t,ht⟩⟩ := hx
  obtain ⟨⟨u,hu⟩,⟨v,hv⟩⟩ := hy
  have hxs : segmentPoint a b s.val=x := by simpa [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hs
  have hxt : segmentPoint c d t.val=x := by simpa [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht
  have hyu : segmentPoint a b u.val=y := by simpa [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hu
  have hyv : segmentPoint c d v.val=y := by simpa [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hv
  have hdet := (h s.val s.property t.val t.property (hxs.trans hxt.symm)).1
  have he := segment_intersection_parameters_unique a b c d hdet s.val t.val u.val v.val
    (hxs.trans hxt.symm) (hyu.trans hyv.symm)
  exact hxs.symm.trans ((congrArg (segmentPoint a b) he.1).trans hyu)
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.DrawingPassages
end Zarankiewicz.DrawingPassages
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.DrawingPassages
end Zarankiewicz.DrawingPassages
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.DrawingPassages
end DrawingPassages
namespace PolygonalExterior
end PolygonalExterior
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.PolygonalExterior
end Zarankiewicz.PolygonalExterior
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.DrawingPassages
end DrawingPassages
namespace PolygonalExterior
end PolygonalExterior
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.DrawingPassages
end Zarankiewicz.DrawingPassages
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
namespace Zarankiewicz
theorem walk_dart_parameters {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (d : G.Dart) (hd : d ∈ p.darts) :
    ∃ i : ℕ, i < p.length ∧ d.fst=p.getVert i ∧ d.snd=p.getVert (i+1) := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hd
  have he := SimpleGraph.Walk.darts_getElem_eq_getVert (p:=p) i.val i.isLt
  have hd' := hi.symm.trans he
  refine ⟨i.val,by simpa only [p.length_darts] using i.isLt,?_,?_⟩
  · exact congrArg (fun r : G.Dart => r.fst) hd'
  · exact congrArg (fun r : G.Dart => r.snd) hd'
end Zarankiewicz
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem polygonalArcPath_piece_subset_range (v : ℕ → Plane) :
    (k : ℕ) → ∀ i, i < k → segment ℝ (v i) (v (i+1)) ⊆ Set.range (polygonalArcPath v k)
  | 0, i, hi => by omega
  | 1, i, hi => by
    have he : i=0 := by omega
    subst i
    rw [polygonalArcPath,Path.range_segment]
  | k+2, i, hi => by
    rw [polygonalArcPath,Path.trans_range]
    by_cases hin : i < k+1
    · exact (polygonalArcPath_piece_subset_range v (k+1) i hin).trans Set.subset_union_left
    · have he : i=k+1 := by omega
      subst i
      rw [Path.range_segment]
      exact Set.subset_union_right
theorem graphWalkPath_dart_subset_range {V : Type*} {G : SimpleGraph V} (pos : V → Plane)
    {a b : V} (p : G.Walk a b) (d : G.Dart) (hd : d ∈ p.darts) :
    segment ℝ (pos d.fst) (pos d.snd) ⊆ Set.range (graphWalkPath pos p) := by
  obtain ⟨i,hi,hfst,hsnd⟩ := walk_dart_parameters p d hd
  rw [hfst,hsnd]
  exact polygonalArcPath_piece_subset_range (fun i => pos (p.getVert i)) p.length i hi
theorem walk_dart_at {V : Type*} {G : SimpleGraph V} {a b : V} (p : G.Walk a b)
    (i : ℕ) (hi : i < p.length) :
    ∃ d : G.Dart, d ∈ p.darts ∧ d.fst=p.getVert i ∧ d.snd=p.getVert (i+1) := by
  have hi' : i < p.darts.length := by simpa only [p.length_darts] using hi
  refine ⟨p.darts[i],List.getElem_mem hi',?_,?_⟩
  · rw [SimpleGraph.Walk.darts_getElem_eq_getVert]
  · rw [SimpleGraph.Walk.darts_getElem_eq_getVert]
theorem graphWalkPath_range_subset_of_darts_subset {V : Type*} {G : SimpleGraph V}
    (pos : V → Plane) {a b : V} (p q : G.Walk a b) (hd : q.darts ⊆ p.darts) :
    Set.range (graphWalkPath pos q) ⊆ Set.range (graphWalkPath pos p) := by
  intro x hx
  by_cases hq : q.length=0
  · change x ∈ Set.range (polygonalArcPath (fun i => pos (q.getVert i)) q.length) at hx
    rw [hq] at hx
    obtain ⟨t,ht⟩ := hx
    have he : x=pos a := by simpa [polygonalArcPath,q.getVert_zero] using ht.symm
    exact ⟨0,(graphWalkPath pos p).source.trans he.symm⟩
  · obtain ⟨i,hi,hxi⟩ := polygonalArcPath_range_piece (fun i => pos (q.getVert i)) q.length (by omega) x hx
    obtain ⟨d,hdq,hfst,hsnd⟩ := walk_dart_at q i hi
    apply graphWalkPath_dart_subset_range pos p d (hd hdq)
    simpa only [hfst,hsnd] using hxi
theorem graphWalkPath_bypass_range_subset {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (pos : V → Plane) {a b : V} (p : G.Walk a b) :
    Set.range (graphWalkPath pos p.bypass) ⊆ Set.range (graphWalkPath pos p) :=
  graphWalkPath_range_subset_of_darts_subset pos p p.bypass p.darts_bypass_subset_darts
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
def exteriorSegmentGraph (G : SimpleGraph Plane) (U : Set Plane) : SimpleGraph Plane where
  Adj := fun a b => G.Adj a b ∧ Disjoint (segment ℝ a b) U
  symm := ⟨by
    intro a b h
    exact ⟨h.1.symm,by simpa only [segment_symm] using h.2⟩⟩
  loopless := ⟨by intro a h; exact G.loopless.irrefl a h.1⟩
theorem graphWalkPath_edge_subset_range {G : SimpleGraph Plane} {a b : Plane}
    (p : G.Walk a b) (u v : Plane) (huv : s(u,v) ∈ p.edges) :
    segment ℝ u v ⊆ Set.range (graphWalkPath id p) := by
  obtain ⟨i,hi,he⟩ := (p.mk_mem_edges_iff_exists).mp huv
  have hpiece := polygonalArcPath_piece_subset_range (fun i => p.getVert i) p.length i hi
  change segment ℝ u v ⊆ Set.range (polygonalArcPath (fun i => p.getVert i) p.length)
  rcases Sym2.eq_iff.mp he with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · simpa only [h0,h1] using hpiece
  · simpa only [h0,h1,segment_symm] using hpiece
def exteriorGraphWalk {G : SimpleGraph Plane} {a b : Plane} (p : G.Walk a b)
    (U : Set Plane) (h : Disjoint (Set.range (graphWalkPath id p)) U) :
    (exteriorSegmentGraph G U).Walk a b :=
  p.transfer (exteriorSegmentGraph G U) (by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
      intro huv
      exact ⟨p.adj_of_mem_edges huv,h.mono_left (graphWalkPath_edge_subset_range p u v huv)⟩)
theorem exteriorGraphWalk_getVert {G : SimpleGraph Plane} {a b : Plane} (p : G.Walk a b)
    (U : Set Plane) (h : Disjoint (Set.range (graphWalkPath id p)) U) (i : ℕ) :
    (exteriorGraphWalk p U h).getVert i=p.getVert i := by
  have hlen : (exteriorGraphWalk p U h).length=p.length := by
    simp only [exteriorGraphWalk,SimpleGraph.Walk.length_transfer]
  have hsupport : (exteriorGraphWalk p U h).support=p.support := by
    simp only [exteriorGraphWalk,SimpleGraph.Walk.support_transfer]
  by_cases hi : i ≤ p.length
  · have hi' : i ≤ (exteriorGraphWalk p U h).length := by rw [hlen]; exact hi
    rw [SimpleGraph.Walk.getVert_eq_support_getElem _ hi',p.getVert_eq_support_getElem hi]
    simp only [hsupport]
  · rw [SimpleGraph.Walk.getVert_of_length_le _ (by
      rw [hlen]
      omega),p.getVert_of_length_le (by omega)]
theorem exteriorGraphWalk_length {G : SimpleGraph Plane} {a b : Plane} (p : G.Walk a b)
    (U : Set Plane) (h : Disjoint (Set.range (graphWalkPath id p)) U) :
    (exteriorGraphWalk p U h).length=p.length := by
  simp only [exteriorGraphWalk,SimpleGraph.Walk.length_transfer]
theorem exteriorGraphWalk_trace {G : SimpleGraph Plane} {a b : Plane} (p : G.Walk a b)
    (U : Set Plane) (h : Disjoint (Set.range (graphWalkPath id p)) U) :
    Set.range (graphWalkPath id (exteriorGraphWalk p U h))=Set.range (graphWalkPath id p) := by
  change Set.range (polygonalArcPath (fun i => (exteriorGraphWalk p U h).getVert i)
    (exteriorGraphWalk p U h).length)=Set.range (polygonalArcPath (fun i => p.getVert i) p.length)
  have hf : (fun i => (exteriorGraphWalk p U h).getVert i)=(fun i => p.getVert i) :=
    funext (exteriorGraphWalk_getVert p U h)
  exact congrArg₂ (fun (seq : ℕ → Plane) (k : ℕ) =>
    Set.range (fun t : unitInterval => polygonalArcPath seq k t)) hf (exteriorGraphWalk_length p U h)
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
def OrderedPathPart {a b c d : Plane} (γ : Path a b) (δ : Path c d) : Prop :=
  ∃ f : unitInterval → unitInterval, StrictMono f ∧ ∀ t, γ (f t)=δ t
theorem OrderedPathPart.refl {a b : Plane} (γ : Path a b) : OrderedPathPart γ γ :=
  ⟨id,strictMono_id,fun _ => rfl⟩
theorem OrderedPathPart.trans {a b c d e f : Plane} {γ : Path a b} {δ : Path c d} {η : Path e f}
    (hγ : OrderedPathPart γ δ) (hδ : OrderedPathPart δ η) : OrderedPathPart γ η := by
  obtain ⟨u,hu,he⟩ := hγ
  obtain ⟨v,hv,hf⟩ := hδ
  exact ⟨u ∘ v,hu.comp hv,fun t => (he (v t)).trans (hf t)⟩
theorem OrderedPathPart.left {a b c d e : Plane} {γ : Path a b} {δ : Path d e}
    (h : OrderedPathPart γ δ) (η : Path b c) : OrderedPathPart (γ.trans η) δ :=
  (show OrderedPathPart (γ.trans η) γ from
    ⟨intervalLeft,intervalLeft_strictMono,path_trans_intervalLeft γ η⟩).trans h
theorem OrderedPathPart.right {a b c d e : Plane} {γ : Path b c} {δ : Path d e}
    (h : OrderedPathPart γ δ) (η : Path a b) : OrderedPathPart (η.trans γ) δ :=
  (show OrderedPathPart (η.trans γ) γ from
    ⟨intervalRight,intervalRight_strictMono,path_trans_intervalRight η γ⟩).trans h
theorem OrderedPathPart.congr_right {a b c d e f : Plane} {γ : Path a b}
    {δ : Path c d} {η : Path e f} (h : OrderedPathPart γ δ) (he : ∀ t, δ t=η t) :
    OrderedPathPart γ η := by
  obtain ⟨u,hu,hh⟩ := h
  exact ⟨u,hu,fun t => (hh t).trans (he t)⟩
theorem OrderedPathPart.endpoints_ordered {a b c d : Plane} {γ : Path a b} {δ : Path c d}
    (h : OrderedPathPart γ δ) :
    ∃ u v : unitInterval, u < v ∧ γ u=c ∧ γ v=d := by
  obtain ⟨f,hf,he⟩ := h
  exact ⟨f 0,f 1,hf zero_lt_one,(he 0).trans δ.source,(he 1).trans δ.target⟩
theorem alternatingPath_contains_bridge (a b : ℕ → Plane) (p : ∀ i, Path (a i) (b i))
    (q : ∀ i, Path (b i) (a (i+1))) :
    (n : ℕ) → ∀ i, i < n → OrderedPathPart (alternatingPath a b p q n) (q i)
  | 0, i, hi => by omega
  | n+1, i, hi => by
    by_cases he : i=n
    · subst i
      exact ((OrderedPathPart.refl (q n)).right _).left _
    · exact ((alternatingPath_contains_bridge a b p q n i (by omega)).left (q n)).left (p (n+1))
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.PolygonalExterior
end Zarankiewicz.PolygonalExterior
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.DrawingPassages
end DrawingPassages
namespace PolygonalExterior
end PolygonalExterior
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem alternatingPath_hasFiniteAffineCover (a b : ℕ → Plane) (p : ∀ i, Path (a i) (b i))
    (q : ∀ i, Path (b i) (a (i+1))) (hp : ∀ i, HasFiniteAffineCover (p i))
    (hq : ∀ i, HasFiniteAffineCover (q i)) :
    (k : ℕ) → HasFiniteAffineCover (alternatingPath a b p q k)
  | 0 => hp 0
  | k+1 => ((alternatingPath_hasFiniteAffineCover a b p q hp hq k).trans (hq k)).trans (hp (k+1))
namespace PolygonalExterior
end PolygonalExterior
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
namespace PolygonalExterior
end PolygonalExterior
end Zarankiewicz
end
end OAI
end
section
namespace OAI
namespace Zarankiewicz
def graphSequenceWalk {V : Type*} (G : SimpleGraph V) (v : ℕ → V) :
    (k : ℕ) → (∀ i, i < k → G.Adj (v i) (v (i+1))) → G.Walk (v 0) (v k)
  | 0, _ => .nil
  | k+1, h => (graphSequenceWalk G v k (fun i hi => h i (by omega))).concat (h k (by omega))
theorem graphSequenceWalk_length {V : Type*} (G : SimpleGraph V) (v : ℕ → V) :
    (k : ℕ) → (h : ∀ i, i < k → G.Adj (v i) (v (i+1))) → (graphSequenceWalk G v k h).length=k
  | 0, _ => rfl
  | k+1, h => by rw [graphSequenceWalk,SimpleGraph.Walk.length_concat,graphSequenceWalk_length]
theorem graphSequenceWalk_getVert {V : Type*} (G : SimpleGraph V) (v : ℕ → V) :
    (k : ℕ) → (h : ∀ i, i < k → G.Adj (v i) (v (i+1))) →
    ∀ i, i ≤ k → (graphSequenceWalk G v k h).getVert i=v i
  | 0, h, i, hi => by
    have he : i=0 := by omega
    subst i
    exact SimpleGraph.Walk.getVert_zero _
  | k+1, h, i, hi => by
    by_cases hik : i ≤ k
    · rw [graphSequenceWalk,SimpleGraph.Walk.concat_eq_append,SimpleGraph.Walk.getVert_append',
        graphSequenceWalk_length,if_pos hik]
      exact graphSequenceWalk_getVert G v k _ i hik
    · have he : i=k+1 := by omega
      subst i
      simpa only [graphSequenceWalk_length] using (graphSequenceWalk G v (k+1) h).getVert_length
end Zarankiewicz
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.PolygonalExterior
end Zarankiewicz.PolygonalExterior
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.DrawingPassages
end DrawingPassages
namespace PolygonalExterior
end PolygonalExterior
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.PolygonalParametrization
end Zarankiewicz.PolygonalParametrization
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem graphWalkPath_range_cases {V : Type*} {G : SimpleGraph V} (pos : V → Plane)
    {a b : V} (p : G.Walk a b) (x : Plane) (hx : x ∈ Set.range (graphWalkPath pos p)) :
    x=pos a ∨ ∃ i, i < p.length ∧ x ∈ segment ℝ (pos (p.getVert i)) (pos (p.getVert (i+1))) := by
  by_cases hp : p.length=0
  · change x ∈ Set.range (polygonalArcPath (fun i => pos (p.getVert i)) p.length) at hx
    rw [hp] at hx
    obtain ⟨t,ht⟩ := hx
    exact Or.inl (by simpa [polygonalArcPath,p.getVert_zero] using ht.symm)
  · exact Or.inr (polygonalArcPath_range_piece _ _ (by omega) x hx)
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz.PolygonalExterior
end Zarankiewicz.PolygonalExterior
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
theorem graphWalkPath_range_iff {G : SimpleGraph Plane} {a b : Plane}
    (p : G.Walk a b) (x : Plane) :
    x ∈ Set.range (graphWalkPath id p) ↔
      x=a ∨ ∃ u v, s(u,v) ∈ p.edges ∧ x ∈ segment ℝ u v := by
  constructor
  · intro hx
    rcases graphWalkPath_range_cases id p x hx with h | ⟨i,hi,hx⟩
    · exact Or.inl h
    · refine Or.inr ⟨p.getVert i,p.getVert (i+1),?_,hx⟩
      exact (p.mk_mem_edges_iff_exists).mpr ⟨i,hi,rfl⟩
  · rintro (rfl | ⟨u,v,h,hx⟩)
    · exact ⟨0,(graphWalkPath id p).source⟩
    · exact graphWalkPath_edge_subset_range p u v h hx
theorem graphWalkPath_copy_range {G : SimpleGraph Plane} {a b a' b' : Plane}
    (p : G.Walk a b) (ha : a=a') (hb : b=b') :
    Set.range (graphWalkPath id (p.copy ha hb))=Set.range (graphWalkPath id p) := by
  subst a'
  subst b'
  rfl
theorem graphWalkPath_mapLe_range {G H : SimpleGraph Plane} (hle : G ≤ H)
    {a b : Plane} (p : G.Walk a b) :
    Set.range (graphWalkPath id (p.mapLe hle))=Set.range (graphWalkPath id p) := by
  ext x
  simp only [graphWalkPath_range_iff,SimpleGraph.Walk.edges_mapLe_eq_edges]
theorem graphWalkPath_append_range {G : SimpleGraph Plane} {a b c : Plane}
    (p : G.Walk a b) (q : G.Walk b c) :
    Set.range (graphWalkPath id (p.append q))=
      Set.range (graphWalkPath id p) ∪ Set.range (graphWalkPath id q) := by
  ext x
  simp only [Set.mem_union,graphWalkPath_range_iff,SimpleGraph.Walk.edges_append,List.mem_append]
  constructor
  · rintro (hx | ⟨u,v,h,hx⟩)
    · exact Or.inl (Or.inl hx)
    · rcases h with h | h
      · exact Or.inl (Or.inr ⟨u,v,h,hx⟩)
      · exact Or.inr (Or.inr ⟨u,v,h,hx⟩)
  · rintro ((hx | ⟨u,v,h,hx⟩) | (hx | ⟨u,v,h,hx⟩))
    · exact Or.inl hx
    · exact Or.inr ⟨u,v,Or.inl h,hx⟩
    · have hb : x ∈ Set.range (graphWalkPath id p) := ⟨1,(graphWalkPath id p).target.trans hx.symm⟩
      rcases (graphWalkPath_range_iff p x).mp hb with h | ⟨u,v,h,hx⟩
      · exact Or.inl h
      · exact Or.inr ⟨u,v,Or.inl h,hx⟩
    · exact Or.inr ⟨u,v,Or.inr h,hx⟩
theorem graphWalkPath_toWalk_range {G : SimpleGraph Plane} {a b : Plane} (h : G.Adj a b) :
    Set.range (graphWalkPath id h.toWalk)=segment ℝ a b := by
  change Set.range (Path.segment a b)=segment ℝ a b
  exact Path.range_segment a b
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
namespace ExteriorCrossingCut
end ExteriorCrossingCut
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
namespace ExteriorCrossingCut
end ExteriorCrossingCut
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
namespace Zarankiewicz
end Zarankiewicz
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
namespace Zarankiewicz
end Zarankiewicz
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
namespace Zarankiewicz
end Zarankiewicz
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
namespace Zarankiewicz
end Zarankiewicz
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Paper170
end Paper170
end
end
section
noncomputable section
namespace Paper170
end Paper170
end
end
section
noncomputable section
namespace Paper170
end Paper170
end
end
section
noncomputable section
namespace Paper170
end Paper170
end
end
section
noncomputable section
namespace Paper170
end Paper170
end
end
section
noncomputable section
namespace Paper170
end Paper170
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Paper170
end Paper170
end
end
section
noncomputable section
namespace Paper170
end Paper170
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
def drawingMarks (D : FiniteIntersectionDrawing graph) : Set Plane :=
  Set.range D.vertex ∪ Paper170.crossingPoints D.toContinuousDrawing
theorem drawingMarks_finite [Fintype Vertex] (D : FiniteIntersectionDrawing graph) : (drawingMarks D).Finite :=
  (Set.finite_range D.vertex).union D.crossings_finite
theorem crossing_not_vertex (D : FiniteIntersectionDrawing graph) (x : Plane)
    (hx : x ∈ Paper170.crossingPoints D.toContinuousDrawing) (v : Vertex) : x ≠ D.vertex v := by
  obtain ⟨e,f,hef,⟨t,ht,he⟩,hf⟩ := hx
  intro hh
  exact D.interior_avoids_vertices e t ht v (he.trans hh)
theorem marked_parameters_finite [Fintype Vertex] (D : FiniteIntersectionDrawing graph) (e : Edge) :
    ((D.edge e) ⁻¹' drawingMarks D).Finite :=
  Set.Finite.preimage (D.edge_injective e).injOn (drawingMarks_finite D)
theorem marked_parameter_zero (D : FiniteIntersectionDrawing graph) (e : Edge) :
    (0 : unitInterval) ∈ (D.edge e) ⁻¹' drawingMarks D := by
  exact Or.inl ⟨graph.src e,(D.edge e).source.symm⟩
theorem marked_parameter_one (D : FiniteIntersectionDrawing graph) (e : Edge) :
    (1 : unitInterval) ∈ (D.edge e) ⁻¹' drawingMarks D := by
  exact Or.inl ⟨graph.dst e,(D.edge e).target.symm⟩
theorem unmarked_edge_point_interior (D : FiniteIntersectionDrawing graph) (e : Edge)
    (t : unitInterval) (ht : D.edge e t ∉ drawingMarks D) : t ∈ Set.Ioo (0 : unitInterval) 1 := by
  have ht0 : t ≠ 0 := by
    intro he
    subst t
    exact ht (marked_parameter_zero D e)
  have ht1 : t ≠ 1 := by
    intro he
    subst t
    exact ht (marked_parameter_one D e)
  exact ⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
    lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩
theorem unmarked_intersection_same_edge (D : FiniteIntersectionDrawing graph)
    (e f : Edge) (s t : unitInterval)
    (he : D.edge e s=D.edge f t) (hs : D.edge e s ∉ drawingMarks D) : e=f := by
  by_contra hef
  have hsi := unmarked_edge_point_interior D e s hs
  have hti := unmarked_edge_point_interior D f t (he ▸ hs)
  exact hs (Or.inr ⟨e,f,hef,⟨s,hsi,rfl⟩,⟨t,hti,he.symm⟩⟩)
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
theorem exists_sorted_drawing_parameters [Fintype Vertex] (D : FiniteIntersectionDrawing graph)
    (e : Edge) :
    ∃ k : ℕ, 0 < k ∧ ∃ t : Fin (k+1) → unitInterval,
      StrictMono t ∧ t 0=0 ∧ t (Fin.last k)=1 ∧
      Set.range t=(D.edge e) ⁻¹' drawingMarks D := by
  obtain ⟨k,hk,t,ht,h0,h1,hR⟩ := exists_sorted_unitInterval_finset (marked_parameters_finite D e).toFinset
    (by simpa using marked_parameter_zero D e) (by simpa using marked_parameter_one D e)
  exact ⟨k,hk,t,ht,h0,h1,by simpa using hR⟩
end Paper170Geometry
end
end
section
noncomputable section
namespace Paper170Geometry
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
theorem subdivision_mark_endpoint (D : Paper170.AdmissibleDrawing graph)
    (P : ∀ e, PolygonalParametrization (D.edge e))
    (hmark : ∀ e t, D.edge e t ∈ drawingMarks D.toFiniteIntersectionDrawing → t ∈ Set.range (P e).knot)
    (e : Edge) (i : Fin (P e).pieces) (x : Plane)
    (hx : x ∈ (P e).pieceTrace i) (hm : x ∈ drawingMarks D.toFiniteIntersectionDrawing) :
    x=D.edge e ((P e).knot i.castSucc) ∨ x=D.edge e ((P e).knot i.succ) := by
  obtain ⟨t,ht⟩ := (P e).pieceTrace_subset_range i hx
  obtain ⟨j,hj⟩ := hmark e t (ht.symm ▸ hm)
  have he : D.edge e ((P e).knot j)=x := (congrArg (D.edge e) hj).trans ht
  have hh := (P e).pieceTrace_knot_endpoint (D.edge_injective e) i j (he.symm ▸ hx)
  simpa only [he] using hh
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
theorem drawing_curve_meeting_mark (D : Paper170.AdmissibleDrawing graph) (e f : Edge)
    (hef : e ≠ f) (x : Plane) (hx : x ∈ Set.range (D.edge e)) (hy : x ∈ Set.range (D.edge f)) :
    x ∈ drawingMarks D.toFiniteIntersectionDrawing := by
  obtain ⟨s,hs⟩ := hx
  obtain ⟨t,ht⟩ := hy
  by_cases hs0 : s=0
  · subst s
    exact Or.inl ⟨(graph.src e),by simpa using hs⟩
  by_cases hs1 : s=1
  · subst s
    exact Or.inl ⟨(graph.dst e),by simpa using hs⟩
  by_cases ht0 : t=0
  · subst t
    exact Or.inl ⟨(graph.src f),by simpa using ht⟩
  by_cases ht1 : t=1
  · subst t
    exact Or.inl ⟨(graph.dst f),by simpa using ht⟩
  exact Or.inr ⟨e,f,hef,
    ⟨s,⟨lt_of_le_of_ne (show 0 ≤ s from s.property.1) (Ne.symm hs0),
      lt_of_le_of_ne (show s ≤ 1 from s.property.2) hs1⟩,hs⟩,
    ⟨t,⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
      lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩,ht⟩⟩
abbrev DrawingPiece {D : Paper170.AdmissibleDrawing graph} (P : ∀ e, PolygonalParametrization (D.edge e)) :=
  (e : Edge) × Fin (P e).pieces
def drawingPieceStart {D : Paper170.AdmissibleDrawing graph} (P : ∀ e, PolygonalParametrization (D.edge e))
    (i : DrawingPiece P) : Plane := D.edge i.1 ((P i.1).knot i.2.castSucc)
def drawingPieceEnd {D : Paper170.AdmissibleDrawing graph} (P : ∀ e, PolygonalParametrization (D.edge e))
    (i : DrawingPiece P) : Plane := D.edge i.1 ((P i.1).knot i.2.succ)
theorem drawingPiece_endpoints_ne {D : Paper170.AdmissibleDrawing graph}
    (P : ∀ e, PolygonalParametrization (D.edge e)) (i : DrawingPiece P) :
    drawingPieceStart P i ≠ drawingPieceEnd P i := by
  intro he
  have hh := D.edge_injective i.1 he
  exact ((P i.1).increasing (show i.2.castSucc < i.2.succ by change i.2.val < i.2.val+1; omega)).ne hh
theorem drawing_pieces_meeting_endpoints (D : Paper170.AdmissibleDrawing graph)
    (P : ∀ e, PolygonalParametrization (D.edge e))
    (hmark : ∀ e t, D.edge e t ∈ drawingMarks D.toFiniteIntersectionDrawing → t ∈ Set.range (P e).knot)
    (p q : DrawingPiece P) (hpq : p ≠ q) (x : Plane)
    (hx : x ∈ segment ℝ (drawingPieceStart P p) (drawingPieceEnd P p))
    (hy : x ∈ segment ℝ (drawingPieceStart P q) (drawingPieceEnd P q)) :
    (x=drawingPieceStart P p ∨ x=drawingPieceEnd P p) ∧
      (x=drawingPieceStart P q ∨ x=drawingPieceEnd P q) := by
  rcases p with ⟨e,i⟩
  rcases q with ⟨f,j⟩
  by_cases hef : e=f
  · subst f
    have hij : i ≠ j := fun he => hpq (by subst j; rfl)
    exact ⟨(P e).pieceTrace_other_piece_endpoint (D.edge_injective e) i j hij x hx hy,
      (P e).pieceTrace_other_piece_endpoint (D.edge_injective e) j i (Ne.symm hij) x hy hx⟩
  · have hm := drawing_curve_meeting_mark D e f hef x
      ((P e).pieceTrace_subset_range i hx) ((P f).pieceTrace_subset_range j hy)
    exact ⟨subdivision_mark_endpoint D P hmark e i x hx hm,
      subdivision_mark_endpoint D P hmark f j x hy hm⟩
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
variable  {D : Paper170.AdmissibleDrawing graph}
def drawingSubdivisionGraph (P : ∀ e, PolygonalParametrization (D.edge e)) : SimpleGraph Plane where
  Adj := fun a b => a ≠ b ∧ ∃ p : DrawingPiece P,
    (a=drawingPieceStart P p ∧ b=drawingPieceEnd P p) ∨
      (a=drawingPieceEnd P p ∧ b=drawingPieceStart P p)
  symm := ⟨by
    rintro a b ⟨hab,p,hp⟩
    refine ⟨Ne.symm hab,p,?_⟩
    rcases hp with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact Or.inr ⟨hb,ha⟩
    · exact Or.inl ⟨hb,ha⟩⟩
  loopless := ⟨by rintro a ⟨ha,_⟩; exact ha rfl⟩
theorem drawingSubdivisionGraph_piece_adj (P : ∀ e, PolygonalParametrization (D.edge e))
    (p : DrawingPiece P) :
    (drawingSubdivisionGraph P).Adj (drawingPieceStart P p) (drawingPieceEnd P p) :=
  ⟨drawingPiece_endpoints_ne P p,p,Or.inl ⟨rfl,rfl⟩⟩
theorem common_endpoint_alternatives (a b c d x : Plane) (hab : x=a ∨ x=b) (hcd : x=c ∨ x=d) :
    (a=c ∧ x=a) ∨ (a=d ∧ x=a) ∨ (b=c ∧ x=b) ∨ (b=d ∧ x=b) := by
  rcases hab with ha | hb <;> rcases hcd with hc | hd
  · exact Or.inl ⟨ha.symm.trans hc,ha⟩
  · exact Or.inr (Or.inl ⟨ha.symm.trans hd,ha⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hb.symm.trans hc,hb⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hb.symm.trans hd,hb⟩))
theorem drawingSubdivisionGraph_embedding (P : ∀ e, PolygonalParametrization (D.edge e))
    (hmark : ∀ e t, D.edge e t ∈ drawingMarks D.toFiniteIntersectionDrawing → t ∈ Set.range (P e).knot) :
    StraightEdgeEmbedding (drawingSubdivisionGraph P) id := by
  refine ⟨Function.injective_id,?_⟩
  rintro a b c d ⟨hab,p,hp⟩ ⟨hcd,q,hq⟩ x hx hy
  by_cases hpq : p=q
  · subst q
    rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rcases hq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl ⟨rfl,rfl⟩
    · exact Or.inr (Or.inl ⟨rfl,rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl,rfl⟩)
    · exact Or.inl ⟨rfl,rfl⟩
  · have hxp : x ∈ segment ℝ (drawingPieceStart P p) (drawingPieceEnd P p) := by
      rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hx
      · simpa only [id_eq,segment_symm] using hx
    have hxq : x ∈ segment ℝ (drawingPieceStart P q) (drawingPieceEnd P q) := by
      rcases hq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hy
      · simpa only [id_eq,segment_symm] using hy
    obtain ⟨hpe,hqe⟩ := drawing_pieces_meeting_endpoints D P hmark p q hpq x hxp hxq
    have heab : x=a ∨ x=b := by
      rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hpe
      · exact hpe.symm
    have hecd : x=c ∨ x=d := by
      rcases hq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hqe
      · exact hqe.symm
    exact Or.inr (Or.inr (common_endpoint_alternatives a b c d x heab hecd))
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
variable  {D : Paper170.AdmissibleDrawing graph}
theorem subdivision_point_endpoint (P : ∀ e, PolygonalParametrization (D.edge e))
    (x : Plane) (hpoint : ∀ e t, D.edge e t=x → t ∈ Set.range (P e).knot)
    (e : Edge) (i : Fin (P e).pieces) (hx : x ∈ (P e).pieceTrace i) :
    x=D.edge e ((P e).knot i.castSucc) ∨ x=D.edge e ((P e).knot i.succ) := by
  obtain ⟨t,ht⟩ := (P e).pieceTrace_subset_range i hx
  obtain ⟨j,hj⟩ := hpoint e t ht
  have he : D.edge e ((P e).knot j)=x := (congrArg (D.edge e) hj).trans ht
  have hh := (P e).pieceTrace_knot_endpoint (D.edge_injective e) i j (he.symm ▸ hx)
  simpa only [he] using hh
theorem drawingSubdivisionGraph_point_endpoint (P : ∀ e, PolygonalParametrization (D.edge e))
    (x : Plane) (hpoint : ∀ e t, D.edge e t=x → t ∈ Set.range (P e).knot)
    (a b : Plane) (hab : (drawingSubdivisionGraph P).Adj a b) (hx : x ∈ segment ℝ a b) :
    x=a ∨ x=b := by
  obtain ⟨hab,p,hp⟩ := hab
  rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact subdivision_point_endpoint P x hpoint p.1 p.2 hx
  · have hx' : x ∈ segment ℝ (drawingPieceStart P p) (drawingPieceEnd P p) := by
      simpa only [segment_symm] using hx
    exact (subdivision_point_endpoint P x hpoint p.1 p.2 hx').symm
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
variable  {D : Paper170.AdmissibleDrawing graph}
theorem drawingEdgeSequence_adj (P : ∀ e, PolygonalParametrization (D.edge e))
    (e : Edge) (i : ℕ) (hi : i < (P e).pieces) :
    (drawingSubdivisionGraph P).Adj ((P e).vertices i) ((P e).vertices (i+1)) := by
  let j : Fin (P e).pieces := ⟨i,hi⟩
  have h0 : (P e).vertices i=drawingPieceStart P ⟨e,j⟩ := (P e).vertices_at j.castSucc
  have h1 : (P e).vertices (i+1)=drawingPieceEnd P ⟨e,j⟩ := (P e).vertices_at j.succ
  rw [h0,h1]
  exact drawingSubdivisionGraph_piece_adj P ⟨e,j⟩
def drawingEdgeWalk (P : ∀ e, PolygonalParametrization (D.edge e)) (e : Edge) :
    (drawingSubdivisionGraph P).Walk (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))) :=
  (graphSequenceWalk (drawingSubdivisionGraph P) (P e).vertices (P e).pieces
    (drawingEdgeSequence_adj P e)).copy (P e).vertices_first (P e).vertices_last
theorem drawingEdgeWalk_length (P : ∀ e, PolygonalParametrization (D.edge e)) (e : Edge) :
    (drawingEdgeWalk P e).length=(P e).pieces := by
  simp only [drawingEdgeWalk,SimpleGraph.Walk.length_copy,graphSequenceWalk_length]
theorem drawingEdgeWalk_getVert (P : ∀ e, PolygonalParametrization (D.edge e))
    (e : Edge) (i : ℕ) (hi : i ≤ (P e).pieces) :
    (drawingEdgeWalk P e).getVert i=(P e).vertices i := by
  simp only [drawingEdgeWalk,SimpleGraph.Walk.getVert_copy]
  exact graphSequenceWalk_getVert _ _ _ _ i hi
end Paper170Geometry
end
end
section
noncomputable section
namespace Paper170Geometry
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
theorem graphWalkPath_range_cases {V : Type*} {G : SimpleGraph V} (pos : V → Plane)
    {a b : V} (p : G.Walk a b) (x : Plane) (hx : x ∈ Set.range (graphWalkPath pos p)) :
    x=pos a ∨ ∃ i, i < p.length ∧ x ∈ segment ℝ (pos (p.getVert i)) (pos (p.getVert (i+1))) := by
  by_cases hp : p.length=0
  · change x ∈ Set.range (polygonalArcPath (fun i => pos (p.getVert i)) p.length) at hx
    rw [hp] at hx
    obtain ⟨t,ht⟩ := hx
    exact Or.inl (by simpa [polygonalArcPath,p.getVert_zero] using ht.symm)
  · exact Or.inr (polygonalArcPath_range_piece _ _ (by omega) x hx)
variable  {D : Paper170.AdmissibleDrawing graph}
theorem drawingEdgeWalk_take_trace (P : ∀ e, PolygonalParametrization (D.edge e))
    (e : Edge) (k : Fin ((P e).pieces+1)) :
    Set.range (graphWalkPath id ((drawingEdgeWalk P e).take k.val)) ⊆
      D.edge e '' Set.Icc (0 : unitInterval) ((P e).knot k) := by
  intro x hx
  rcases graphWalkPath_range_cases id ((drawingEdgeWalk P e).take k.val) x hx with he | ⟨i,hi,hxi⟩
  · exact ⟨0,⟨le_rfl,((P e).knot k).property.1⟩,(D.edge e).source.trans he.symm⟩
  · have hil : i < (P e).pieces := by
      rw [SimpleGraph.Walk.take_length,drawingEdgeWalk_length] at hi
      omega
    have hik : i+1 ≤ k.val := by
      rw [SimpleGraph.Walk.take_length,drawingEdgeWalk_length] at hi
      omega
    simp only [id_eq,SimpleGraph.Walk.take_getVert] at hxi
    rw [show min k.val i=i by omega,show min k.val (i+1)=i+1 by omega,
      drawingEdgeWalk_getVert P e i (by omega),drawingEdgeWalk_getVert P e (i+1) (by omega)] at hxi
    let j : Fin (P e).pieces := ⟨i,hil⟩
    have h0 : (P e).vertices i=D.edge e ((P e).knot j.castSucc) := (P e).vertices_at j.castSucc
    have h1 : (P e).vertices (i+1)=D.edge e ((P e).knot j.succ) := (P e).vertices_at j.succ
    rw [h0,h1] at hxi
    obtain ⟨t,ht⟩ := (P e).pieceTrace_parameter j x hxi
    have hbetween := intervalSegment_between ((P e).knot j.castSucc) ((P e).knot j.succ) t
      ((P e).increasing.monotone (by change i ≤ i+1; omega))
    exact ⟨intervalSegment ((P e).knot j.castSucc) ((P e).knot j.succ) t,
      ⟨(intervalSegment _ _ t).property.1,hbetween.2.trans ((P e).increasing.monotone hik)⟩,ht⟩
theorem drawingEdgeWalk_drop_trace (P : ∀ e, PolygonalParametrization (D.edge e))
    (e : Edge) (k : Fin ((P e).pieces+1)) :
    Set.range (graphWalkPath id ((drawingEdgeWalk P e).drop k.val)) ⊆
      D.edge e '' Set.Icc ((P e).knot k) (1 : unitInterval) := by
  intro x hx
  rcases graphWalkPath_range_cases id ((drawingEdgeWalk P e).drop k.val) x hx with he | ⟨i,hi,hxi⟩
  · refine ⟨(P e).knot k,⟨le_rfl,((P e).knot k).property.2⟩,?_⟩
    have hh : (drawingEdgeWalk P e).getVert k.val=D.edge e ((P e).knot k) :=
      (drawingEdgeWalk_getVert P e k.val (by omega)).trans ((P e).vertices_at k)
    exact hh.symm.trans he.symm
  · have hil : k.val+i < (P e).pieces := by
      rw [SimpleGraph.Walk.drop_length,drawingEdgeWalk_length] at hi
      omega
    simp only [id_eq,SimpleGraph.Walk.drop_getVert] at hxi
    rw [drawingEdgeWalk_getVert P e (k.val+i) (by omega),
      drawingEdgeWalk_getVert P e (k.val+(i+1)) (by omega)] at hxi
    let j : Fin (P e).pieces := ⟨k.val+i,hil⟩
    have h0 : (P e).vertices (k.val+i)=D.edge e ((P e).knot j.castSucc) := (P e).vertices_at j.castSucc
    have h1 : (P e).vertices (k.val+(i+1))=D.edge e ((P e).knot j.succ) := by
      have hh : (P e).vertices (k.val+i+1)=D.edge e ((P e).knot j.succ) := (P e).vertices_at j.succ
      simpa only [Nat.add_assoc] using hh
    rw [h0,h1] at hxi
    obtain ⟨t,ht⟩ := (P e).pieceTrace_parameter j x hxi
    have hbetween := intervalSegment_between ((P e).knot j.castSucc) ((P e).knot j.succ) t
      ((P e).increasing.monotone (by change k.val+i ≤ k.val+i+1; omega))
    refine ⟨intervalSegment ((P e).knot j.castSucc) ((P e).knot j.succ) t,⟨?_,?_⟩,ht⟩
    · exact ((P e).increasing.monotone (show k ≤ j.castSucc by change k.val ≤ k.val+i; omega)).trans hbetween.1
    · exact (intervalSegment _ _ t).property.2
end Paper170Geometry
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
abbrev DrawingMark (D : FiniteIntersectionDrawing graph) := ↥(drawingMarks D)
theorem drawing_disk_isolation [Fintype Vertex] [Fintype Edge] (D : FiniteIntersectionDrawing graph) :
    ∃ δ : Edge → ℝ, ∃ r : ℝ, (∀ e, 0 < δ e) ∧ 0 < r ∧
      (∀ x y : DrawingMark D, x ≠ y →
        Disjoint (closedRoundDisk x.val r) (closedRoundDisk y.val r)) ∧
      (∀ e (x : DrawingMark D) t, D.edge e t ∈ closedRoundDisk x.val r →
        ∃ u : unitInterval, D.edge e u=x.val ∧ t ∈ parameterNeighborhood u (δ e)) ∧
      (∀ e u v, D.edge e u ∈ drawingMarks D → D.edge e v ∈ drawingMarks D → u ≠ v →
        Disjoint (closure (parameterNeighborhood u (δ e)))
          (closure (parameterNeighborhood v (δ e)))) := by
  let : Fintype (DrawingMark D) := (drawingMarks_finite D).fintype
  let : DecidableEq (DrawingMark D) := Classical.decEq _
  obtain ⟨δ,r,hδ,hr,hd,hv,hs⟩ := finite_injective_curve_disk_isolation
    (fun e => D.edge e) (fun e => (D.edge e).continuous) D.edge_injective
    (fun x : DrawingMark D => x.val) Subtype.val_injective
  refine ⟨δ,r,hδ,hr,hd,hv,?_⟩
  intro e u v hu hv huv
  exact hs e u v ⟨⟨D.edge e u,hu⟩,rfl⟩ ⟨⟨D.edge e v,hv⟩,rfl⟩ huv
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
/-- Geometric cut data for the original drawing. Existence is proved below;
this record asserts no crossing bound or drawing-normalization conclusion. -/
structure DrawingPassages (D : FiniteIntersectionDrawing graph) where
  radius : ℝ
  radius_pos : 0 < radius
  disks_disjoint : ∀ x y : DrawingMark D, x ≠ y →
    Disjoint (closedRoundDisk x.val radius) (closedRoundDisk y.val radius)
  count : Edge → ℕ
  count_pos : ∀ e, 0 < count e
  node : ∀ e, Fin (count e+1) → unitInterval
  increasing : ∀ e, StrictMono (node e)
  first : ∀ e, node e 0=0
  last : ∀ e, node e (Fin.last (count e))=1
  node_range : ∀ e, Set.range (node e)=(D.edge e) ⁻¹' drawingMarks D
  passage : ∀ e i, DiskPassage (D.edge e) (D.edge e (node e i)) radius (node e i)
  separated : ∀ e i j, i < j → (passage e i).leave < (passage e j).enter
  visited_mark_on_edge : ∀ e (x : DrawingMark D) t,
    D.edge e t ∈ closedRoundDisk x.val radius → ∃ u, D.edge e u=x.val
theorem nonempty_drawingPassages [Fintype Vertex] [Fintype Edge] (D : FiniteIntersectionDrawing graph) : Nonempty (DrawingPassages D) := by
  classical
  obtain ⟨δ,r,hδ,hr,hdisks,hvisits,hparam⟩ := drawing_disk_isolation D
  choose k hk τ hτ h0 h1 hR using (fun e => exists_sorted_drawing_parameters D e)
  have hnode (e : Edge) (i : Fin (k e+1)) : D.edge e (τ e i) ∈ drawingMarks D := by
    change τ e i ∈ (D.edge e) ⁻¹' drawingMarks D
    rw [← hR e]
    exact ⟨i,rfl⟩
  have hex (e : Edge) (i : Fin (k e+1)) :
      Nonempty (DiskPassage (D.edge e) (D.edge e (τ e i)) r (τ e i)) :=
    nonempty_diskPassage (D.edge e) (D.edge e (τ e i)) r (τ e i)
      (by simpa [squaredLength] using sq_pos_of_pos hr)
  let P (e : Edge) (i : Fin (k e+1)) := Classical.choice (hex e i)
  have hlocal (e : Edge) (i : Fin (k e+1)) (t : unitInterval)
      (ht : D.edge e t ∈ closedRoundDisk (D.edge e (τ e i)) r) :
      t ∈ parameterNeighborhood (τ e i) (δ e) := by
    obtain ⟨u,hu,hh⟩ := hvisits e ⟨D.edge e (τ e i),hnode e i⟩ t ht
    have he : u=τ e i := D.edge_injective e hu
    simpa [he] using hh
  have hsep (e : Edge) (i j : Fin (k e+1)) (hij : i < j) :
      (P e i).leave < (P e j).enter := by
    apply diskPassage_separated (P e i) (P e j) (hτ e hij) (hδ e)
    · exact hparam e (τ e i) (τ e j) (hnode e i) (hnode e j) ((hτ e).injective.ne (ne_of_lt hij))
    · exact hlocal e i _ (P e i).leave_mem
    · exact hlocal e j _ (P e j).enter_mem
  exact ⟨{
    radius := r
    radius_pos := hr
    disks_disjoint := hdisks
    count := k
    count_pos := hk
    node := τ
    increasing := hτ
    first := h0
    last := h1
    node_range := hR
    passage := P
    separated := hsep
    visited_mark_on_edge := fun e x t ht => by
      obtain ⟨u,hu,_⟩ := hvisits e x t ht
      exact ⟨u,hu⟩ }⟩
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}
abbrev ArcIndex (C : DrawingPassages D) := (e : Edge) × Fin (C.count e)
theorem node_mark (C : DrawingPassages D) (e : Edge) (i : Fin (C.count e+1)) :
    D.edge e (C.node e i) ∈ drawingMarks D := by
  change C.node e i ∈ (D.edge e) ⁻¹' drawingMarks D
  rw [← C.node_range e]
  exact ⟨i,rfl⟩
def arcStartMark (C : DrawingPassages D) (i : C.ArcIndex) : DrawingMark D :=
  ⟨D.edge i.1 (C.node i.1 i.2.castSucc),C.node_mark i.1 i.2.castSucc⟩
def arcEndMark (C : DrawingPassages D) (i : C.ArcIndex) : DrawingMark D :=
  ⟨D.edge i.1 (C.node i.1 i.2.succ),C.node_mark i.1 i.2.succ⟩
def arcStart (C : DrawingPassages D) (i : C.ArcIndex) : Plane :=
  D.edge i.1 (C.passage i.1 i.2.castSucc).leave
def arcEnd (C : DrawingPassages D) (i : C.ArcIndex) : Plane :=
  D.edge i.1 (C.passage i.1 i.2.succ).enter
def arc (C : DrawingPassages D) (i : C.ArcIndex) : Path (C.arcStart i) (C.arcEnd i) :=
  retainedSubarc (D.edge i.1) (C.node i.1) C.radius (C.passage i.1) i.2
theorem arc_gap (C : DrawingPassages D) (i : C.ArcIndex) :
    (C.passage i.1 i.2.castSucc).leave < (C.passage i.1 i.2.succ).enter :=
  C.separated i.1 i.2.castSucc i.2.succ (by change i.2.val < i.2.val+1; omega)
theorem arc_endpoints_ne (C : DrawingPassages D) (i : C.ArcIndex) : C.arcStart i ≠ C.arcEnd i := by
  intro he
  exact (C.arc_gap i).ne (D.edge_injective i.1 he)
theorem arc_range (C : DrawingPassages D) (i : C.ArcIndex) :
    Set.range (C.arc i)=D.edge i.1 '' Set.Icc (C.passage i.1 i.2.castSucc).leave (C.passage i.1 i.2.succ).enter :=
  pathSubarc_range (D.edge i.1) _ _ (C.arc_gap i)
theorem arc_avoids_marks (C : DrawingPassages D) (i : C.ArcIndex) (x : Plane)
    (hx : x ∈ Set.range (C.arc i)) : x ∉ drawingMarks D := by
  rw [C.arc_range] at hx
  obtain ⟨t,ht,rfl⟩ := hx
  intro hh
  have hp : t ∈ Set.range (C.node i.1) := by rw [C.node_range]; exact hh
  exact retained_interval_no_mark (D.edge i.1) (C.node i.1) (C.increasing i.1)
    (C.first i.1) (C.last i.1) C.radius (C.passage i.1) i.2 t ht hp
theorem retained_parameter_outside (C : DrawingPassages D) (i : C.ArcIndex) (t : unitInterval)
    (ht : t ∈ Set.Ioo (C.passage i.1 i.2.castSucc).leave (C.passage i.1 i.2.succ).enter) :
    D.edge i.1 t ∈ outsideDisks (fun x : DrawingMark D => x.val) C.radius := by
  intro x
  apply lt_of_not_ge
  intro hh
  obtain ⟨u,hu⟩ := C.visited_mark_on_edge i.1 x t hh
  have hmu : u ∈ Set.range (C.node i.1) := by
    rw [C.node_range]
    change D.edge i.1 u ∈ drawingMarks D
    rw [hu]
    exact x.property
  obtain ⟨j,hj⟩ := hmu
  have hc : D.edge i.1 (C.node i.1 j)=x.val := (congrArg (D.edge i.1) hj).trans hu
  have hv := (C.passage i.1 j).all_visits t (by rw [hc]; exact hh)
  by_cases hji : j ≤ i.2.castSucc
  · have hm := (ordered_passage_leave_strictMono (D.edge i.1) (C.node i.1) C.radius
      (C.passage i.1) (C.separated i.1)).monotone hji
    exact ht.1.not_ge (hv.2.trans hm)
  · have hij : i.2.succ ≤ j := by
      change i.2.val+1 ≤ j.val
      have hn : ¬ j.val ≤ i.2.val := hji
      omega
    have hm := (ordered_passage_enter_strictMono (D.edge i.1) (C.node i.1) C.radius
      (C.passage i.1) (C.separated i.1)).monotone hij
    exact ht.2.not_ge (hm.trans hv.1)
theorem arc_interior_outside (C : DrawingPassages D) (i : C.ArcIndex) (t : unitInterval)
    (ht : t ∈ Set.Ioo (0 : unitInterval) 1) :
    C.arc i t ∈ outsideDisks (fun x : DrawingMark D => x.val) C.radius := by
  exact C.retained_parameter_outside i _ (intervalSegment_strict_between _ _ t (C.arc_gap i) ht)
theorem arc_start_on_circle (C : DrawingPassages D) (i : C.ArcIndex) :
    squaredLength (C.arcStart i-(C.arcStartMark i).val)=C.radius^2 := by
  exact (C.passage i.1 i.2.castSucc).leave_boundary
    ((C.arc_gap i).trans_le (show (C.passage i.1 i.2.succ).enter ≤ 1 from (C.passage i.1 i.2.succ).enter.property.2))
theorem arc_end_on_circle (C : DrawingPassages D) (i : C.ArcIndex) :
    squaredLength (C.arcEnd i-(C.arcEndMark i).val)=C.radius^2 := by
  exact (C.passage i.1 i.2.succ).enter_boundary
    ((show 0 ≤ (C.passage i.1 i.2.castSucc).leave from (C.passage i.1 i.2.castSucc).leave.property.1).trans_lt (C.arc_gap i))
end Paper170Geometry.DrawingPassages
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}
theorem arcs_pairwise_disjoint (C : DrawingPassages D) (p q : C.ArcIndex) (hpq : p ≠ q) :
    Disjoint (Set.range (C.arc p)) (Set.range (C.arc q)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hxm := C.arc_avoids_marks p x hx
  rcases p with ⟨e,i⟩
  rcases q with ⟨f,j⟩
  rw [C.arc_range] at hx hy
  obtain ⟨s,hs,hsx⟩ := hx
  obtain ⟨t,ht,htx⟩ := hy
  have hef : e=f := unmarked_intersection_same_edge D e f s t (hsx.trans htx.symm)
    (hsx.symm ▸ hxm)
  subst f
  have hst : s=t := D.edge_injective e (hsx.trans htx.symm)
  rw [← hst] at ht
  have hij : i ≠ j := by
    intro he
    subst j
    exact hpq rfl
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact Set.disjoint_left.mp
      (retained_interval_pair_disjoint (D.edge e) (C.node e) C.radius (C.passage e) (C.separated e) i j hij) hs ht
  · exact Set.disjoint_left.mp
      (retained_interval_pair_disjoint (D.edge e) (C.node e) C.radius (C.passage e) (C.separated e) j i hji) ht hs
end Paper170Geometry.DrawingPassages
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}
abbrev Port (C : DrawingPassages D) := C.ArcIndex × Bool
def portPoint (C : DrawingPassages D) (p : C.Port) : Plane :=
  if p.2 then C.arcEnd p.1 else C.arcStart p.1
def portMark (C : DrawingPassages D) (p : C.Port) : DrawingMark D :=
  if p.2 then C.arcEndMark p.1 else C.arcStartMark p.1
theorem portPoint_mem_arc (C : DrawingPassages D) (p : C.Port) :
    C.portPoint p ∈ Set.range (C.arc p.1) := by
  rcases p with ⟨i,flag⟩
  cases flag
  · exact ⟨0,(C.arc i).source⟩
  · exact ⟨1,(C.arc i).target⟩
theorem portPoint_injective (C : DrawingPassages D) : Function.Injective C.portPoint := by
  rintro ⟨i,s⟩ ⟨j,t⟩ he
  have hij : i=j := by
    by_contra h
    exact Set.disjoint_left.mp (C.arcs_pairwise_disjoint i j h)
      (C.portPoint_mem_arc (i,s)) (he.symm ▸ C.portPoint_mem_arc (j,t))
  subst j
  have hst : s=t := by
    cases s <;> cases t
    · rfl
    · exact False.elim (C.arc_endpoints_ne i he)
    · exact False.elim (C.arc_endpoints_ne i he.symm)
    · rfl
  subst t
  rfl
theorem portPoint_on_circle (C : DrawingPassages D) (p : C.Port) :
    squaredLength (C.portPoint p-(C.portMark p).val)=C.radius^2 := by
  rcases p with ⟨i,flag⟩
  cases flag
  · exact C.arc_start_on_circle i
  · exact C.arc_end_on_circle i
abbrev PortsAt (C : DrawingPassages D) (x : DrawingMark D) := {p : C.Port // C.portMark p=x}
theorem portsAt_on_circle (C : DrawingPassages D) (x : DrawingMark D) (p : C.PortsAt x) :
    squaredLength (C.portPoint p.val-x.val)=C.radius^2 := by
  simpa only [p.property] using C.portPoint_on_circle p.val
end Paper170Geometry.DrawingPassages
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}
abbrev InnerIndex (C : DrawingPassages D) :=
  (e : Edge) × {i : Fin (C.count e+1) // 0 < i.val ∧ i.val < C.count e}
def innerMark (C : DrawingPassages D) (p : C.InnerIndex) : DrawingMark D :=
  ⟨D.edge p.1 (C.node p.1 p.2.val),C.node_mark p.1 p.2.val⟩
def incomingArc (C : DrawingPassages D) (p : C.InnerIndex) : C.ArcIndex :=
  ⟨p.1,⟨p.2.val.val-1,by have h := p.2.property; omega⟩⟩
def outgoingArc (C : DrawingPassages D) (p : C.InnerIndex) : C.ArcIndex :=
  ⟨p.1,⟨p.2.val.val,p.2.property.2⟩⟩
def incomingPort (C : DrawingPassages D) (p : C.InnerIndex) : C.Port := (C.incomingArc p,true)
def outgoingPort (C : DrawingPassages D) (p : C.InnerIndex) : C.Port := (C.outgoingArc p,false)
theorem incoming_node (C : DrawingPassages D) (p : C.InnerIndex) :
    (C.incomingArc p).2.succ=p.2.val := by
  apply Fin.ext
  change p.2.val.val-1+1=p.2.val.val
  have h := p.2.property.1
  omega
theorem incomingPort_mark (C : DrawingPassages D) (p : C.InnerIndex) :
    C.portMark (C.incomingPort p)=C.innerMark p := by
  apply Subtype.ext
  change D.edge p.1 (C.node p.1 (C.incomingArc p).2.succ)=D.edge p.1 (C.node p.1 p.2.val)
  rw [C.incoming_node]
theorem outgoingPort_mark (C : DrawingPassages D) (p : C.InnerIndex) :
    C.portMark (C.outgoingPort p)=C.innerMark p := rfl
theorem incomingPort_point (C : DrawingPassages D) (p : C.InnerIndex) :
    C.portPoint (C.incomingPort p)=D.edge p.1 (C.passage p.1 p.2.val).enter := by
  change D.edge p.1 (C.passage p.1 (C.incomingArc p).2.succ).enter=_
  rw [C.incoming_node]
theorem outgoingPort_point (C : DrawingPassages D) (p : C.InnerIndex) :
    C.portPoint (C.outgoingPort p)=D.edge p.1 (C.passage p.1 p.2.val).leave := rfl
theorem inner_parameter_interior (C : DrawingPassages D) (p : C.InnerIndex) :
    C.node p.1 p.2.val ∈ Set.Ioo (0 : unitInterval) 1 := by
  constructor
  · rw [← C.first p.1]
    exact C.increasing p.1 (show (0 : Fin (C.count p.1+1)) < p.2.val from p.2.property.1)
  · rw [← C.last p.1]
    exact C.increasing p.1 (show p.2.val < Fin.last (C.count p.1) from p.2.property.2)
theorem innerMark_is_crossing (C : DrawingPassages D) (p : C.InnerIndex) :
    (C.innerMark p).val ∈ Paper170.crossingPoints D.toContinuousDrawing := by
  have hm := (C.innerMark p).property
  rcases hm with ⟨v,hv⟩ | hcross
  · exact False.elim (D.interior_avoids_vertices p.1 (C.node p.1 p.2.val)
      (C.inner_parameter_interior p) v hv.symm)
  · exact hcross
def crossingChord (C : DrawingPassages D) (p : C.InnerIndex) :
    Path (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p)) :=
  Path.segment _ _
theorem crossingChord_injective (C : DrawingPassages D) (p : C.InnerIndex) :
    Function.Injective (C.crossingChord p) := by
  apply Path.segment_injective_of_ne
  intro he
  rw [C.incomingPort_point,C.outgoingPort_point] at he
  exact (C.passage p.1 p.2.val).enter_lt_leave.ne (D.edge_injective p.1 he)
end Paper170Geometry.DrawingPassages
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}
def vertexMark (_C : DrawingPassages D) (v : Vertex) : DrawingMark D :=
  ⟨D.vertex v,Or.inl ⟨v,rfl⟩⟩
theorem vertexMark_injective (C : DrawingPassages D) : Function.Injective C.vertexMark := by
  intro v w he
  exact D.vertex_injective (congrArg Subtype.val he)
theorem exists_drawing_vertex_placement [Fintype Edge] (C : DrawingPassages D) :
    ∃ v : Vertex → Plane, Function.Injective v ∧
      (∀ i, squaredLength (v i-D.vertex i) < C.radius^2) ∧
      (∀ i (p : C.PortsAt (C.vertexMark i)), v i ≠ C.portPoint p.val) ∧
      (∀ i (p q : C.PortsAt (C.vertexMark i)), p ≠ q →
        det2 (C.portPoint p.val-v i) (C.portPoint q.val-v i) ≠ 0) := by
  classical
  have hex (i : Vertex) : ∃ v : Plane,
      squaredLength (v-D.vertex i) < C.radius^2 ∧
      (∀ p : C.PortsAt (C.vertexMark i), v ≠ C.portPoint p.val) ∧
      (∀ p q : C.PortsAt (C.vertexMark i), p ≠ q → det2 (C.portPoint p.val-v) (C.portPoint q.val-v) ≠ 0) :=
    exists_vertex_disk_point (D.vertex i) C.radius C.radius_pos
      (fun p : C.PortsAt (C.vertexMark i) => C.portPoint p.val)
      (C.portPoint_injective.comp Subtype.val_injective) (C.portsAt_on_circle (C.vertexMark i))
  choose v hv hne hdet using hex
  refine ⟨v,?_,hv,hne,hdet⟩
  intro i j he
  by_contra hij
  have hd := C.disks_disjoint (C.vertexMark i) (C.vertexMark j) (C.vertexMark_injective.ne hij)
  have hi : v i ∈ closedRoundDisk (C.vertexMark i).val C.radius := (hv i).le
  have hj : v j ∈ closedRoundDisk (C.vertexMark j).val C.radius := (hv j).le
  exact Set.disjoint_left.mp hd hi (he.symm ▸ hj)
theorem vertex_spoke_injective (C : DrawingPassages D) (v : Vertex → Plane)
    (hv : ∀ i, squaredLength (v i-D.vertex i) < C.radius^2)
    (i : Vertex) (p : C.PortsAt (C.vertexMark i)) :
    Function.Injective (Path.segment (v i) (C.portPoint p.val)) := by
  apply Path.segment_injective_of_ne
  intro he
  have h := hv i
  have hp : squaredLength (C.portPoint p.val-D.vertex i)=C.radius^2 := C.portsAt_on_circle (C.vertexMark i) p
  rw [he,hp] at h
  exact lt_irrefl _ h
theorem vertex_spoke_interior (C : DrawingPassages D) (v : Vertex → Plane)
    (hv : ∀ i, squaredLength (v i-D.vertex i) < C.radius^2)
    (i : Vertex) (p : C.PortsAt (C.vertexMark i)) (t : unitInterval)
    (ht : t < 1) : squaredLength ((Path.segment (v i) (C.portPoint p.val)) t-D.vertex i) < C.radius^2 := by
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module]
  exact spoke_in_open_disk (D.vertex i) (v i) (C.portPoint p.val) C.radius (hv i)
    (C.portsAt_on_circle (C.vertexMark i) p) t.val ⟨t.property.1,ht⟩
end Paper170Geometry.DrawingPassages
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}
theorem innerIndex_eq_of_edge_mark (C : DrawingPassages D) (p q : C.InnerIndex)
    (he : p.1=q.1) (hm : C.innerMark p=C.innerMark q) : p=q := by
  rcases p with ⟨e,i⟩
  rcases q with ⟨f,j⟩
  change e=f at he
  subst f
  congr 1
  apply Subtype.ext
  exact (C.increasing e).injective (D.edge_injective e (congrArg Subtype.val hm))
theorem incomingPort_injective (C : DrawingPassages D) : Function.Injective C.incomingPort := by
  intro p q he
  apply C.innerIndex_eq_of_edge_mark p q (congrArg (fun x : C.Port => x.1.1) he)
  have hh := congrArg C.portMark he
  simpa only [C.incomingPort_mark] using hh
theorem outgoingPort_injective (C : DrawingPassages D) : Function.Injective C.outgoingPort := by
  intro p q he
  apply C.innerIndex_eq_of_edge_mark p q (congrArg (fun x : C.Port => x.1.1) he)
  have hh := congrArg C.portMark he
  simpa only [C.outgoingPort_mark] using hh
theorem incomingPort_ne_outgoingPort (C : DrawingPassages D) (p q : C.InnerIndex) :
    C.incomingPort p ≠ C.outgoingPort q := by
  intro he
  have hh : true=false := congrArg Prod.snd he
  cases hh
theorem incomingPoint_on_circle (C : DrawingPassages D) (p : C.InnerIndex) :
    squaredLength (C.portPoint (C.incomingPort p)-(C.innerMark p).val)=C.radius^2 := by
  simpa only [C.incomingPort_mark] using C.portPoint_on_circle (C.incomingPort p)
theorem outgoingPoint_on_circle (C : DrawingPassages D) (p : C.InnerIndex) :
    squaredLength (C.portPoint (C.outgoingPort p)-(C.innerMark p).val)=C.radius^2 := by
  simpa only [C.outgoingPort_mark] using C.portPoint_on_circle (C.outgoingPort p)
theorem crossing_chords_transverse_at_mark (C : DrawingPassages D) (p q : C.InnerIndex)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) :
    SegmentPairTransverse (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)) := by
  apply round_circle_chords_transverse (C.innerMark p).val _ _ _ _ C.radius
  · exact C.incomingPoint_on_circle p
  · exact C.outgoingPoint_on_circle p
  · simpa only [hm] using C.incomingPoint_on_circle q
  · simpa only [hm] using C.outgoingPoint_on_circle q
  · exact C.portPoint_injective.ne (C.incomingPort_ne_outgoingPort p p)
  · exact C.portPoint_injective.ne (C.incomingPort_ne_outgoingPort q q)
  · exact C.portPoint_injective.ne (C.incomingPort_injective.ne hpq)
  · exact C.portPoint_injective.ne (C.incomingPort_ne_outgoingPort p q)
  · exact C.portPoint_injective.ne (Ne.symm (C.incomingPort_ne_outgoingPort q p))
  · exact C.portPoint_injective.ne (C.outgoingPort_injective.ne hpq)
theorem innerMark_no_triples (C : DrawingPassages D) (p q r : C.InnerIndex)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hpqM : C.innerMark p=C.innerMark q) (hprM : C.innerMark p=C.innerMark r) : False := by
  have heq : p.1 ≠ q.1 := fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hpqM)
  have her : p.1 ≠ r.1 := fun he => hpr (C.innerIndex_eq_of_edge_mark p r he hprM)
  have hqrM : C.innerMark q=C.innerMark r := hpqM.symm.trans hprM
  have hfr : q.1 ≠ r.1 := fun he => hqr (C.innerIndex_eq_of_edge_mark q r he hqrM)
  have hp : (C.innerMark p).val ∈ Paper170.edgeInterior D.toContinuousDrawing p.1 :=
    ⟨C.node p.1 p.2.val,C.inner_parameter_interior p,rfl⟩
  have hq : (C.innerMark p).val ∈ Paper170.edgeInterior D.toContinuousDrawing q.1 := by
    rw [hpqM]
    exact ⟨C.node q.1 q.2.val,C.inner_parameter_interior q,rfl⟩
  have hr : (C.innerMark p).val ∈ Paper170.edgeInterior D.toContinuousDrawing r.1 := by
    rw [hprM]
    exact ⟨C.node r.1 r.2.val,C.inner_parameter_interior r,rfl⟩
  have hmem : (C.innerMark p).val ∈ Paper170.edgeInterior D.toContinuousDrawing p.1 ∩
      Paper170.edgeInterior D.toContinuousDrawing q.1 ∩ Paper170.edgeInterior D.toContinuousDrawing r.1 := ⟨⟨hp,hq⟩,hr⟩
  rw [D.no_triples p.1 q.1 r.1 heq her hfr] at hmem
  exact hmem
end Paper170Geometry.DrawingPassages
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}
def firstArc (C : DrawingPassages D) (e : Edge) : C.ArcIndex :=
  ⟨e,⟨0,C.count_pos e⟩⟩
def lastArc (C : DrawingPassages D) (e : Edge) : C.ArcIndex :=
  ⟨e,⟨C.count e-1,by have h := C.count_pos e; omega⟩⟩
theorem lastArc_node (C : DrawingPassages D) (e : Edge) :
    (C.lastArc e).2.succ=Fin.last (C.count e) := by
  apply Fin.ext
  have h := C.count_pos e
  change C.count e-1+1=C.count e
  omega
theorem firstArc_mark (C : DrawingPassages D) (e : Edge) :
    C.arcStartMark (C.firstArc e)=C.vertexMark (graph.src e) := by
  apply Subtype.ext
  change D.edge e (C.node e 0)=D.vertex (graph.src e)
  rw [C.first,Path.source]
theorem lastArc_mark (C : DrawingPassages D) (e : Edge) :
    C.arcEndMark (C.lastArc e)=C.vertexMark (graph.dst e) := by
  apply Subtype.ext
  change D.edge e (C.node e (C.lastArc e).2.succ)=D.vertex (graph.dst e)
  rw [C.lastArc_node,C.last,Path.target]
def startPortAt (C : DrawingPassages D) (e : Edge) : C.PortsAt (C.vertexMark (graph.src e)) :=
  ⟨(C.firstArc e,false),C.firstArc_mark e⟩
def endPortAt (C : DrawingPassages D) (e : Edge) : C.PortsAt (C.vertexMark (graph.dst e)) :=
  ⟨(C.lastArc e,true),C.lastArc_mark e⟩
end Paper170Geometry.DrawingPassages
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
theorem round_chord_in_disk (z a b : Plane) (r : ℝ)
    (ha : squaredLength (a-z)=r^2) (hb : squaredLength (b-z)=r^2)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    squaredLength (segmentPoint a b t-z) ≤ r^2 := by
  have he : squaredLength (segmentPoint a b t-z)=
      (1-t)*squaredLength (a-z)+t*squaredLength (b-z)-t*(1-t)*squaredLength (b-a) := by
    dsimp [squaredLength,segmentPoint]
    ring
  have hnon : 0 ≤ t*(1-t)*squaredLength (b-a) := by
    apply mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
    dsimp [squaredLength]
    positivity
  rw [he,ha,hb]
  linarith
namespace DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}
theorem crossingChord_range_subset_disk (C : DrawingPassages D) (p : C.InnerIndex) :
    Set.range (C.crossingChord p) ⊆ closedRoundDisk (C.innerMark p).val C.radius := by
  rintro x ⟨t,rfl⟩
  change squaredLength ((Path.segment _ _) t-(C.innerMark p).val) ≤ C.radius^2
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module]
  exact round_chord_in_disk _ _ _ _ (C.incomingPoint_on_circle p) (C.outgoingPoint_on_circle p) t.val t.property
theorem crossingChord_interior_in_disk (C : DrawingPassages D) (p : C.InnerIndex)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) :
    squaredLength (C.crossingChord p t-(C.innerMark p).val) < C.radius^2 := by
  change squaredLength ((Path.segment _ _) t-(C.innerMark p).val) < C.radius^2
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module]
  exact round_chord_in_open_disk _ _ _ _ (C.incomingPoint_on_circle p) (C.outgoingPoint_on_circle p)
    (C.portPoint_injective.ne (C.incomingPort_ne_outgoingPort p p)) t.val ht
theorem crossingChords_disjoint_of_marks_ne (C : DrawingPassages D) (p q : C.InnerIndex)
    (hm : C.innerMark p ≠ C.innerMark q) :
    Disjoint (Set.range (C.crossingChord p)) (Set.range (C.crossingChord q)) :=
  (C.disks_disjoint _ _ hm).mono (C.crossingChord_range_subset_disk p) (C.crossingChord_range_subset_disk q)
theorem portPoint_outside_other_disk (C : DrawingPassages D) (p : C.Port) (x : DrawingMark D)
    (hx : C.portMark p ≠ x) : C.radius^2 < squaredLength (C.portPoint p-x.val) := by
  apply lt_of_not_ge
  intro hh
  have hp : C.portPoint p ∈ closedRoundDisk (C.portMark p).val C.radius := (C.portPoint_on_circle p).le
  exact Set.disjoint_left.mp (C.disks_disjoint _ _ hx) hp hh
theorem portPoint_outside_open_disks (C : DrawingPassages D) (p : C.Port) (x : DrawingMark D) :
    C.radius^2 ≤ squaredLength (C.portPoint p-x.val) := by
  by_cases he : C.portMark p=x
  · have hp := C.portPoint_on_circle p
    rw [he] at hp
    exact hp.ge
  · exact (C.portPoint_outside_other_disk p x he).le
theorem crossingChord_avoids_vertex_disks (C : DrawingPassages D) (p : C.InnerIndex)
    (v : Vertex) :
    Disjoint (Set.range (C.crossingChord p)) (closedRoundDisk (D.vertex v) C.radius) := by
  have hn : C.innerMark p ≠ C.vertexMark v := by
    intro he
    exact crossing_not_vertex D (C.innerMark p).val (C.innerMark_is_crossing p) v (congrArg Subtype.val he)
  exact (C.disks_disjoint _ _ hn).mono (C.crossingChord_range_subset_disk p) Set.Subset.rfl
end DrawingPassages
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}
theorem innerIndex_at_mark_pair (C : DrawingPassages D) (p q r : C.InnerIndex)
    (hpq : p ≠ q) (hpqM : C.innerMark p=C.innerMark q) (hprM : C.innerMark p=C.innerMark r) :
    r=p ∨ r=q := by
  by_cases hrp : r=p
  · exact Or.inl hrp
  by_cases hrq : r=q
  · exact Or.inr hrq
  exact False.elim (C.innerMark_no_triples p q r hpq (Ne.symm hrp) (Ne.symm hrq) hpqM hprM)
def chordCrossingsAt (C : DrawingPassages D) (w : DrawingMark D) : Set Plane :=
  {x | ∃ p q : C.InnerIndex, p ≠ q ∧ C.innerMark p=w ∧ C.innerMark q=w ∧
    x ∈ Set.range (C.crossingChord p) ∧ x ∈ Set.range (C.crossingChord q)}
theorem chordCrossingsAt_subsingleton (C : DrawingPassages D) (w : DrawingMark D) :
    (C.chordCrossingsAt w).Subsingleton := by
  rintro x ⟨p,q,hpq,hp,hq,hxp,hxq⟩ y ⟨r,s,hrs,hr,hs,hyr,hys⟩
  have hpm : C.innerMark p=C.innerMark q := hp.trans hq.symm
  have hrpair := C.innerIndex_at_mark_pair p q r hpq hpm (hp.trans hr.symm)
  have hspair := C.innerIndex_at_mark_pair p q s hpq hpm (hp.trans hs.symm)
  have hunique := transverse_segment_intersection_subsingleton _ _ _ _
    (C.crossing_chords_transverse_at_mark p q hpq hpm)
  rcases hrpair with rfl | rfl <;> rcases hspair with rfl | rfl
  · exact False.elim (hrs rfl)
  · exact hunique ⟨hxp,hxq⟩ ⟨hyr,hys⟩
  · exact hunique ⟨hxp,hxq⟩ ⟨hys,hyr⟩
  · exact False.elim (hrs rfl)
theorem chord_meeting_marks_eq (C : DrawingPassages D) (p q : C.InnerIndex) {x : Plane}
    (hp : x ∈ Set.range (C.crossingChord p)) (hq : x ∈ Set.range (C.crossingChord q)) :
    C.innerMark p=C.innerMark q := by
  by_contra h
  exact Set.disjoint_left.mp (C.crossingChords_disjoint_of_marks_ne p q h) hp hq
def chordCrossings (C : DrawingPassages D) : Set Plane :=
  {x | ∃ p q : C.InnerIndex, p ≠ q ∧ x ∈ Set.range (C.crossingChord p) ∧ x ∈ Set.range (C.crossingChord q)}
theorem chord_crossing_original_mark (C : DrawingPassages D) {x : Plane} (hx : x ∈ C.chordCrossings) :
    ∃ w : DrawingMark D, w.val ∈ Paper170.crossingPoints D.toContinuousDrawing ∧ x ∈ C.chordCrossingsAt w := by
  obtain ⟨p,q,hpq,hp,hq⟩ := hx
  refine ⟨C.innerMark p,C.innerMark_is_crossing p,p,q,hpq,rfl,?_,hp,hq⟩
  exact (C.chord_meeting_marks_eq p q hp hq).symm
end Paper170Geometry.DrawingPassages
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.DrawingPassages
open scoped Classical
variable  {D : FiniteIntersectionDrawing graph}
def chordCrossingOrigin (C : DrawingPassages D) (x : Plane) : Plane :=
  if hx : x ∈ C.chordCrossings then (C.chord_crossing_original_mark hx).choose.val else 0
theorem chordCrossingOrigin_mapsTo (C : DrawingPassages D) :
    Set.MapsTo C.chordCrossingOrigin C.chordCrossings (Paper170.crossingPoints D.toContinuousDrawing) := by
  intro x hx
  have hh := (C.chord_crossing_original_mark hx).choose_spec.1
  simpa only [chordCrossingOrigin,dif_pos hx] using hh
theorem chordCrossingOrigin_injOn (C : DrawingPassages D) :
    Set.InjOn C.chordCrossingOrigin C.chordCrossings := by
  intro x hx y hy he
  let w : DrawingMark D := (C.chord_crossing_original_mark hx).choose
  let v : DrawingMark D := (C.chord_crossing_original_mark hy).choose
  have hwx : x ∈ C.chordCrossingsAt w := (C.chord_crossing_original_mark hx).choose_spec.2
  have hvy : y ∈ C.chordCrossingsAt v := (C.chord_crossing_original_mark hy).choose_spec.2
  have hvw : w=v := by
    apply Subtype.ext
    simpa only [chordCrossingOrigin,dif_pos hx,dif_pos hy] using he
  rw [← hvw] at hvy
  exact (C.chordCrossingsAt_subsingleton w) hwx hvy
theorem chordCrossings_finite (C : DrawingPassages D) : C.chordCrossings.Finite :=
  Set.Finite.of_injOn C.chordCrossingOrigin_mapsTo C.chordCrossingOrigin_injOn D.crossings_finite
/-- Different original crossing disks remain separately counted, even when
their two chords come from the same pair of graph edges. -/
theorem chordCrossings_ncard_le (C : DrawingPassages D) :
    C.chordCrossings.ncard ≤ finiteCrossingCount D := by
  calc
    C.chordCrossings.ncard ≤ (Paper170.crossingPoints D.toContinuousDrawing).ncard :=
      Set.ncard_le_ncard_of_injOn C.chordCrossingOrigin C.chordCrossingOrigin_mapsTo
        C.chordCrossingOrigin_injOn D.crossings_finite
    _ = finiteCrossingCount D := Set.ncard_eq_toFinset_card _ D.crossings_finite
end Paper170Geometry.DrawingPassages
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Paper170Geometry
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
variable  {D : FiniteIntersectionDrawing graph}
structure PolygonalExterior (C : DrawingPassages D) where
  chain : ∀ i : C.ArcIndex, PolygonalChain Set.univ (C.arcStart i) (C.arcEnd i)
  injective : ∀ i, Function.Injective (chain i).path
  outside : ∀ i t, t ∈ Set.Ioo (0 : unitInterval) 1 →
    (chain i).path t ∈ outsideDisks (fun x : DrawingMark D => x.val) C.radius
  disjoint : ∀ i j, i ≠ j → Disjoint (Set.range (chain i).path) (Set.range (chain j).path)
theorem nonempty_polygonalExterior [Fintype Vertex] [Fintype Edge] (C : DrawingPassages D) : Nonempty (PolygonalExterior C) := by
  classical
  let : Fintype (DrawingMark D) := (drawingMarks_finite D).fintype
  obtain ⟨U,P,hU,hP,hout,hdisjoint⟩ := finite_exterior_arc_replacements
    (fun x : DrawingMark D => x.val) C.radius C.radius_pos C.disks_disjoint
    C.arcStartMark C.arcEndMark C.arcStart C.arcEnd C.arc_endpoints_ne
    C.arc_start_on_circle C.arc_end_on_circle C.arc C.arcs_pairwise_disjoint C.arc_interior_outside
  exact ⟨{
    chain := fun i => (P i).widen (Set.subset_univ _)
    injective := hP
    outside := hout
    disjoint := hdisjoint }⟩
namespace PolygonalExterior
variable {C : DrawingPassages D}
theorem outside_open_disks (E : PolygonalExterior C) (i : C.ArcIndex) (t : unitInterval)
    (x : DrawingMark D) : C.radius^2 ≤ squaredLength ((E.chain i).path t-x.val) := by
  by_cases ht0 : t=0
  · subst t
    rw [(E.chain i).path.source]
    exact C.portPoint_outside_open_disks (i,false) x
  by_cases ht1 : t=1
  · subst t
    rw [(E.chain i).path.target]
    exact C.portPoint_outside_open_disks (i,true) x
  exact (E.outside i t ⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
    lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩ x).le
theorem avoids_new_vertices (E : PolygonalExterior C) (v : Vertex → Plane)
    (hv : ∀ i, squaredLength (v i-D.vertex i) < C.radius^2)
    (i : C.ArcIndex) (t : unitInterval) (j : Vertex) : (E.chain i).path t ≠ v j := by
  intro he
  have h := E.outside_open_disks i t (C.vertexMark j)
  rw [he] at h
  exact (hv j).not_ge h
theorem parameter_endpoint_of_mem_disk (E : PolygonalExterior C) (i : C.ArcIndex)
    (t : unitInterval) (x : DrawingMark D)
    (ht : (E.chain i).path t ∈ closedRoundDisk x.val C.radius) : t=0 ∨ t=1 := by
  by_cases h0 : t=0
  · exact Or.inl h0
  by_cases h1 : t=1
  · exact Or.inr h1
  have h := E.outside i t ⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm h0),
    lt_of_le_of_ne (show t ≤ 1 from t.property.2) h1⟩ x
  exact False.elim (h.not_ge ht)
end PolygonalExterior
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}
theorem chord_parameter_endpoint (E : PolygonalExterior C) (i : C.ArcIndex) (p : C.InnerIndex)
    (s t : unitInterval) (he : (E.chain i).path s=C.crossingChord p t) : t=0 ∨ t=1 := by
  by_cases ht0 : t=0
  · exact Or.inl ht0
  by_cases ht1 : t=1
  · exact Or.inr ht1
  have h := C.crossingChord_interior_in_disk p t
    ⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
      lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩
  have hx := E.outside_open_disks i s (C.innerMark p)
  rw [he] at hx
  exact False.elim (h.not_ge hx)
theorem exterior_chord_meeting_parameters (E : PolygonalExterior C) (i : C.ArcIndex) (p : C.InnerIndex)
    (s t : unitInterval) (he : (E.chain i).path s=C.crossingChord p t) :
    (i=C.incomingArc p ∧ s=1 ∧ t=0) ∨ (i=C.outgoingArc p ∧ s=0 ∧ t=1) := by
  have hs := E.parameter_endpoint_of_mem_disk i s (C.innerMark p) (by
    rw [he]
    exact C.crossingChord_range_subset_disk p ⟨t,rfl⟩)
  have ht := E.chord_parameter_endpoint i p s t he
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
  · simp only [Path.source] at he
    have hp : (i,false)=C.incomingPort p := C.portPoint_injective he
    have hh : false=true := congrArg Prod.snd hp
    cases hh
  · simp only [Path.source,Path.target] at he
    have hp : (i,false)=C.outgoingPort p := C.portPoint_injective he
    exact Or.inr ⟨congrArg Prod.fst hp,rfl,rfl⟩
  · simp only [Path.source,Path.target] at he
    have hp : (i,true)=C.incomingPort p := C.portPoint_injective he
    exact Or.inl ⟨congrArg Prod.fst hp,rfl,rfl⟩
  · simp only [Path.target] at he
    have hp : (i,true)=C.outgoingPort p := C.portPoint_injective he
    have hh : true=false := congrArg Prod.snd hp
    cases hh
end Paper170Geometry.PolygonalExterior
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}
theorem exterior_spoke_meeting_parameters (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (i : C.ArcIndex) (j : Vertex) (p : C.PortsAt (C.vertexMark j))
    (s t : unitInterval) (he : (E.chain i).path s=(Path.segment (v j) (C.portPoint p.val)) t) :
    t=1 ∧ ((s=0 ∧ (i,false)=p.val) ∨ (s=1 ∧ (i,true)=p.val)) := by
  have ht : t=1 := by
    apply le_antisymm (show t ≤ 1 from t.property.2)
    apply le_of_not_gt
    intro ht1
    have hinside := C.vertex_spoke_interior v hv j p t ht1
    have hout := E.outside_open_disks i s (C.vertexMark j)
    rw [he] at hout
    exact hinside.not_ge hout
  subst t
  rw [Path.target] at he
  have hs := E.parameter_endpoint_of_mem_disk i s (C.vertexMark j) (by
    rw [he]
    exact (C.portsAt_on_circle (C.vertexMark j) p).le)
  refine ⟨rfl,?_⟩
  rcases hs with rfl | rfl
  · rw [Path.source] at he
    exact Or.inl ⟨rfl,C.portPoint_injective he⟩
  · rw [Path.target] at he
    exact Or.inr ⟨rfl,C.portPoint_injective he⟩
end Paper170Geometry.PolygonalExterior
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}
def orderedArc (C : DrawingPassages D) (e : Edge) (i : ℕ) : C.ArcIndex :=
  ⟨e,⟨min i (C.count e-1),by have h := C.count_pos e; omega⟩⟩
theorem orderedArc_val (C : DrawingPassages D) (e : Edge) (i : ℕ)
    (hi : i < C.count e) : (C.orderedArc e i).2.val=i := by
  change min i (C.count e-1)=i
  omega
theorem orderedArc_inj (C : DrawingPassages D) (e : Edge) (i j : ℕ)
    (hi : i < C.count e) (hj : j < C.count e)
    (h : C.orderedArc e i=C.orderedArc e j) : i=j := by
  have hh := congrArg (fun p : C.ArcIndex => p.2.val) h
  simpa only [C.orderedArc_val e i hi,C.orderedArc_val e j hj] using hh
theorem orderedArc_first (C : DrawingPassages D) (e : Edge) :
    C.orderedArc e 0=C.firstArc e := by
  simp [orderedArc,firstArc]
theorem orderedArc_last (C : DrawingPassages D) (e : Edge) :
    C.orderedArc e (C.count e-1)=C.lastArc e := by
  simp [orderedArc,lastArc]
def orderedInner (C : DrawingPassages D) (e : Edge) (j : ℕ)
    (hj : j+1 < C.count e) : C.InnerIndex :=
  ⟨e,⟨⟨j+1,by omega⟩,⟨Nat.succ_pos j,hj⟩⟩⟩
theorem orderedInner_incoming (C : DrawingPassages D) (e : Edge)
    (j : ℕ) (hj : j+1 < C.count e) :
    C.incomingArc (C.orderedInner e j hj)=C.orderedArc e j := by
  unfold incomingArc orderedInner orderedArc
  congr 1
  apply Fin.ext
  change j+1-1=min j (C.count e-1)
  omega
theorem orderedInner_outgoing (C : DrawingPassages D) (e : Edge)
    (j : ℕ) (hj : j+1 < C.count e) :
    C.outgoingArc (C.orderedInner e j hj)=C.orderedArc e (j+1) := by
  unfold outgoingArc orderedInner orderedArc
  congr 1
  apply Fin.ext
  change j+1=min (j+1) (C.count e-1)
  omega
theorem orderedInner_inj (C : DrawingPassages D) (e : Edge) (i j : ℕ)
    (hi : i+1 < C.count e) (hj : j+1 < C.count e)
    (h : C.orderedInner e i hi=C.orderedInner e j hj) : i=j := by
  have hh : i+1=j+1 := congrArg (fun p : C.InnerIndex => p.2.val.val) h
  omega
end DrawingPassages
namespace PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}
def orderedPath (E : PolygonalExterior C) (e : Edge) (i : ℕ) :
    Path (C.arcStart (C.orderedArc e i)) (C.arcEnd (C.orderedArc e i)) :=
  (E.chain (C.orderedArc e i)).path
def orderedBridge (C : DrawingPassages D) (e : Edge) (i : ℕ) :
    Path (C.arcEnd (C.orderedArc e i)) (C.arcStart (C.orderedArc e (i+1))) := Path.segment _ _
theorem orderedBridge_apply (e : Edge) (j : ℕ) (hj : j+1 < C.count e)
    (t : unitInterval) :
    orderedBridge C e j t=C.crossingChord (C.orderedInner e j hj) t := by
  change (Path.segment _ _ : Path _ _) t=(Path.segment _ _ : Path _ _) t
  have ha : C.portPoint (C.incomingPort (C.orderedInner e j hj))=C.arcEnd (C.orderedArc e j) := by
    change C.arcEnd (C.incomingArc (C.orderedInner e j hj))=_
    rw [C.orderedInner_incoming]
  have hb : C.portPoint (C.outgoingPort (C.orderedInner e j hj))=C.arcStart (C.orderedArc e (j+1)) := by
    change C.arcStart (C.outgoingArc (C.orderedInner e j hj))=_
    rw [C.orderedInner_outgoing]
  simp only [Path.segment_apply,ha,hb]
theorem orderedBridge_range (e : Edge) (j : ℕ) (hj : j+1 < C.count e) :
    Set.range (orderedBridge C e j)=Set.range (C.crossingChord (C.orderedInner e j hj)) := by
  congr 1
  funext t
  exact orderedBridge_apply e j hj t
def middlePath (E : PolygonalExterior C) (e : Edge) :
    Path (C.arcStart (C.orderedArc e 0)) (C.arcEnd (C.orderedArc e (C.count e-1))) :=
  alternatingPath (fun i => C.arcStart (C.orderedArc e i))
    (fun i => C.arcEnd (C.orderedArc e i)) (E.orderedPath e) (orderedBridge C e) (C.count e-1)
end PolygonalExterior
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}
theorem middlePath_injective (E : PolygonalExterior C) (e : Edge) :
    Function.Injective (E.middlePath e) := by
  have hc := C.count_pos e
  apply alternatingPath_injective
  · intro i hi
    exact E.injective _
  · intro j hj
    have h := C.crossingChord_injective (C.orderedInner e j (by omega))
    intro s t he
    apply h
    simpa only [orderedBridge_apply (C:=C) e j (by omega)] using he
  · intro i j hi hj hij
    exact E.disjoint _ _ (fun he => hij (C.orderedArc_inj e i j (by omega) (by omega) he))
  · intro i j hi hj hij
    rw [orderedBridge_range e i (by omega),orderedBridge_range e j (by omega)]
    apply C.crossingChords_disjoint_of_marks_ne
    intro he
    apply hij
    apply C.orderedInner_inj e i j
    exact C.innerIndex_eq_of_edge_mark _ _ rfl he
  · intro i j hi hj x hx hy
    obtain ⟨s,hs⟩ := hx
    obtain ⟨t,ht⟩ := hy
    have hbridge := orderedBridge_apply (C:=C) e j (by omega) t
    have hm := E.exterior_chord_meeting_parameters (C.orderedArc e i)
      (C.orderedInner e j (by omega)) s t (hs.trans (ht.symm.trans hbridge))
    rcases hm with ⟨he,rfl,rfl⟩ | ⟨he,rfl,rfl⟩
    · rw [C.orderedInner_incoming] at he
      have hij := C.orderedArc_inj e i j (by omega) (by omega) he
      refine Or.inl ⟨hij,?_⟩
      subst i
      exact hs.symm.trans (E.orderedPath e j).target
    · rw [C.orderedInner_outgoing] at he
      have hij := C.orderedArc_inj e i (j+1) (by omega) (by omega) he
      refine Or.inr ⟨hij,?_⟩
      subst i
      exact hs.symm.trans (E.orderedPath e (j+1)).source
theorem middlePath_range_iff (E : PolygonalExterior C) (e : Edge) (x : Plane) :
    x ∈ Set.range (E.middlePath e) ↔
      (∃ i : C.ArcIndex, i.1=e ∧ x ∈ Set.range (E.chain i).path) ∨
      (∃ p : C.InnerIndex, p.1=e ∧ x ∈ Set.range (C.crossingChord p)) := by
  have hc := C.count_pos e
  rw [middlePath,alternatingPath_range_iff]
  constructor
  · rintro (⟨i,hi,hx⟩ | ⟨j,hj,hx⟩)
    · exact Or.inl ⟨C.orderedArc e i,rfl,hx⟩
    · exact Or.inr ⟨C.orderedInner e j (by omega),rfl,
        by simpa only [orderedBridge_range (C:=C) e j (by omega)] using hx⟩
  · rintro (⟨⟨f,i⟩,he,hx⟩ | ⟨⟨f,⟨j,hj⟩⟩,he,hx⟩)
    · change f=e at he
      subst f
      refine Or.inl ⟨i.val,by omega,?_⟩
      have heq : C.orderedArc e i.val=⟨e,i⟩ := by
        unfold DrawingPassages.orderedArc
        congr 1
        apply Fin.ext
        change min i.val (C.count e-1)=i.val
        omega
      change x ∈ Set.range (E.chain (C.orderedArc e i.val)).path
      rw [heq]
      exact hx
    · change f=e at he
      subst f
      refine Or.inr ⟨j.val-1,by omega,?_⟩
      rw [orderedBridge_range e (j.val-1) (by omega)]
      have heq : C.orderedInner e (j.val-1) (by omega)=⟨e,⟨j,hj⟩⟩ := by
        unfold DrawingPassages.orderedInner
        congr 1
        apply Subtype.ext
        apply Fin.ext
        change j.val-1+1=j.val
        omega
      rw [heq]
      exact hx
end Paper170Geometry.PolygonalExterior
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}
theorem vertex_spoke_range_in_disk (C : DrawingPassages D)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (j : Vertex) (p : C.PortsAt (C.vertexMark j)) :
    Set.range (Path.segment (v j) (C.portPoint p.val)) ⊆ closedRoundDisk (D.vertex j) C.radius := by
  rintro x ⟨t,rfl⟩
  by_cases ht : t=1
  · subst t
    rw [Path.target]
    exact (C.portsAt_on_circle (C.vertexMark j) p).le
  · exact (C.vertex_spoke_interior v hv j p t
      (lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht)).le
theorem vertex_spokes_disjoint_of_vertices_ne (C : DrawingPassages D)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (j k : Vertex) (hjk : j ≠ k)
    (p : C.PortsAt (C.vertexMark j)) (q : C.PortsAt (C.vertexMark k)) :
    Disjoint (Set.range (Path.segment (v j) (C.portPoint p.val)))
      (Set.range (Path.segment (v k) (C.portPoint q.val))) :=
  (C.disks_disjoint _ _ (C.vertexMark_injective.ne hjk)).mono
    (C.vertex_spoke_range_in_disk v hv j p) (C.vertex_spoke_range_in_disk v hv k q)
end DrawingPassages
namespace PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}
theorem middle_spoke_meeting (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : Edge) (j : Vertex) (p : C.PortsAt (C.vertexMark j))
    (x : Plane) (hx : x ∈ Set.range (E.middlePath e))
    (hy : x ∈ Set.range (Path.segment (v j) (C.portPoint p.val))) : x=C.portPoint p.val := by
  rcases (E.middlePath_range_iff e x).mp hx with ⟨i,hi,⟨s,hs⟩⟩ | ⟨q,hq,hx⟩
  · obtain ⟨t,ht⟩ := hy
    have he := E.exterior_spoke_meeting_parameters v hv i j p s t (hs.trans ht.symm)
    rw [he.1,Path.target] at ht
    exact ht.symm
  · exact False.elim (Set.disjoint_left.mp (C.crossingChord_avoids_vertex_disks q j)
      hx (C.vertex_spoke_range_in_disk v hv j p hy))
def anchoredMiddle (E : PolygonalExterior C) (e : Edge) :
    Path (C.arcStart (C.firstArc e)) (C.arcEnd (C.lastArc e)) :=
  (E.middlePath e).cast (congrArg C.arcStart (C.orderedArc_first e).symm)
    (congrArg C.arcEnd (C.orderedArc_last e).symm)
theorem anchoredMiddle_range (E : PolygonalExterior C) (e : Edge) :
    Set.range (E.anchoredMiddle e)=Set.range (E.middlePath e) := rfl
theorem anchoredMiddle_injective (E : PolygonalExterior C) (e : Edge) :
    Function.Injective (E.anchoredMiddle e) := E.middlePath_injective e
end PolygonalExterior
end Paper170Geometry
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}
def startSpoke (C : DrawingPassages D) (v : Vertex → Plane) (e : Edge) :
    Path (v (graph.src e)) (C.arcStart (C.firstArc e)) := Path.segment _ _
def endSpoke (C : DrawingPassages D) (v : Vertex → Plane) (e : Edge) :
    Path (C.arcEnd (C.lastArc e)) (v (graph.dst e)) := (Path.segment _ _).symm
def assembledEdge (E : PolygonalExterior C) (v : Vertex → Plane)
    (e : Edge) : Path (v (graph.src e)) (v (graph.dst e)) :=
  ((startSpoke C v e).trans (E.anchoredMiddle e)).trans (endSpoke C v e)
theorem startSpoke_injective (v : Vertex → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (e : Edge) :
    Function.Injective (startSpoke C v e) := C.vertex_spoke_injective v hv _ (C.startPortAt e)
theorem endSpoke_range (v : Vertex → Plane) (e : Edge) :
    Set.range (endSpoke C v e)=Set.range (Path.segment (v (graph.dst e)) (C.portPoint (C.endPortAt e).val)) := by
  exact Path.symm_range _
theorem endSpoke_injective (v : Vertex → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (e : Edge) :
    Function.Injective (endSpoke C v e) := by
  intro s t he
  have hh := C.vertex_spoke_injective v hv _ (C.endPortAt e) he
  have hval := congrArg Subtype.val hh
  apply Subtype.ext
  change 1-s.val=1-t.val at hval
  linarith
theorem assembledEdge_injective (E : PolygonalExterior C) (v : Vertex → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (e : Edge) :
    Function.Injective (E.assembledEdge v e) := by
  have hfirst : Function.Injective ((startSpoke C v e).trans (E.anchoredMiddle e)) := by
    apply path_trans_injective _ _ (startSpoke_injective v hv e) (E.anchoredMiddle_injective e)
    intro x hx hy
    exact E.middle_spoke_meeting v hv e _ (C.startPortAt e) x hy hx
  apply path_trans_injective _ _ hfirst (endSpoke_injective v hv e)
  intro x hx hy
  rw [Path.trans_range] at hx
  rw [endSpoke_range] at hy
  rcases hx with hx | hx
  · have hd := C.vertex_spokes_disjoint_of_vertices_ne v hv (graph.src e) (graph.dst e)
      (graph.loopless e) (C.startPortAt e) (C.endPortAt e)
    exact False.elim (Set.disjoint_left.mp hd hx hy)
  · exact E.middle_spoke_meeting v hv e _ (C.endPortAt e) x hx hy
theorem assembledEdge_range_iff (E : PolygonalExterior C) (v : Vertex → Plane)
    (e : Edge) (x : Plane) :
    x ∈ Set.range (E.assembledEdge v e) ↔
      (x ∈ Set.range (startSpoke C v e) ∨
        (∃ i : C.ArcIndex, i.1=e ∧ x ∈ Set.range (E.chain i).path) ∨
        (∃ p : C.InnerIndex, p.1=e ∧ x ∈ Set.range (C.crossingChord p))) ∨
      x ∈ Set.range (endSpoke C v e) := by
  simp only [assembledEdge,Path.trans_range,Set.mem_union,anchoredMiddle_range,E.middlePath_range_iff]
end Paper170Geometry.PolygonalExterior
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}
theorem vertex_spoke_vertex_eq (C : DrawingPassages D)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (j k : Vertex) (p : C.PortsAt (C.vertexMark j))
    (hk : v k ∈ Set.range (Path.segment (v j) (C.portPoint p.val))) : k=j := by
  by_contra hkj
  have hd := C.disks_disjoint _ _ (C.vertexMark_injective.ne (Ne.symm hkj))
  exact Set.disjoint_left.mp hd (C.vertex_spoke_range_in_disk v hv j p hk) (hv k).le
end DrawingPassages
namespace PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}
theorem middlePath_avoids_vertices (E : PolygonalExterior C) (v : Vertex → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (e : Edge)
    (j : Vertex) : v j ∉ Set.range (E.middlePath e) := by
  intro hx
  rcases (E.middlePath_range_iff e (v j)).mp hx with ⟨i,hi,⟨t,ht⟩⟩ | ⟨p,hp,hx⟩
  · exact E.avoids_new_vertices v hv i t j ht
  · exact Set.disjoint_left.mp (C.crossingChord_avoids_vertex_disks p j) hx (hv j).le
theorem assembledEdge_vertex_eq (E : PolygonalExterior C) (v : Vertex → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (e : Edge)
    (j : Vertex) (hj : v j ∈ Set.range (E.assembledEdge v e)) :
    j=graph.src e ∨ j=graph.dst e := by
  rw [assembledEdge,Path.trans_range,Path.trans_range] at hj
  rcases hj with (hj | hj) | hj
  · exact Or.inl (C.vertex_spoke_vertex_eq v hv _ j (C.startPortAt e) hj)
  · exact False.elim (E.middlePath_avoids_vertices v hv e j hj)
  · rw [endSpoke_range] at hj
    exact Or.inr (C.vertex_spoke_vertex_eq v hv _ j (C.endPortAt e) hj)
theorem assembledEdge_interior_avoids_vertices (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : Edge) (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1)
    (j : Vertex) : E.assembledEdge v e t ≠ v j := by
  intro he
  rcases E.assembledEdge_vertex_eq v hv e j ⟨t,he⟩ with rfl | rfl
  · have hh := E.assembledEdge_injective v hv e (he.trans (E.assembledEdge v e).source.symm)
    exact ht.1.ne hh.symm
  · have hh := E.assembledEdge_injective v hv e (he.trans (E.assembledEdge v e).target.symm)
    exact ht.2.ne hh
def assembledDrawing (E : PolygonalExterior C) (v : Vertex → Plane)
    (hvinj : Function.Injective v) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) :
    Paper170.ContinuousDrawing graph where
  vertex := v
  vertex_injective := hvinj
  edge := E.assembledEdge v
  edge_injective := E.assembledEdge_injective v hv
  interior_avoids_vertices := E.assembledEdge_interior_avoids_vertices v hv
end PolygonalExterior
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}
theorem middle_exterior_edge_eq (E : PolygonalExterior C) (e : Edge)
    (i : C.ArcIndex) (x : Plane) (hx : x ∈ Set.range (E.middlePath e))
    (hy : x ∈ Set.range (E.chain i).path) : e=i.1 := by
  rcases (E.middlePath_range_iff e x).mp hx with ⟨j,hj,hx⟩ | ⟨p,hp,hx⟩
  · have he : j=i := by
      by_contra hji
      exact Set.disjoint_left.mp (E.disjoint j i hji) hx hy
    exact hj.symm.trans (congrArg Sigma.fst he)
  · obtain ⟨s,hs⟩ := hy
    obtain ⟨t,ht⟩ := hx
    rcases E.exterior_chord_meeting_parameters i p s t (hs.trans ht.symm) with
      ⟨hi,_,_⟩ | ⟨hi,_,_⟩
    · exact hp.symm.trans (congrArg Sigma.fst hi).symm
    · exact hp.symm.trans (congrArg Sigma.fst hi).symm
theorem middle_spoke_edge_eq (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : Edge) (j : Vertex) (p : C.PortsAt (C.vertexMark j))
    (x : Plane) (hx : x ∈ Set.range (E.middlePath e))
    (hy : x ∈ Set.range (Path.segment (v j) (C.portPoint p.val))) : e=p.val.1.1 := by
  rcases (E.middlePath_range_iff e x).mp hx with ⟨i,hi,⟨s,hs⟩⟩ | ⟨q,hq,hx⟩
  · obtain ⟨t,ht⟩ := hy
    have hm := E.exterior_spoke_meeting_parameters v hv i j p s t (hs.trans ht.symm)
    rcases hm.2 with ⟨_,he⟩ | ⟨_,he⟩
    · exact hi.symm.trans (congrArg (fun r : C.Port => r.1.1) he)
    · exact hi.symm.trans (congrArg (fun r : C.Port => r.1.1) he)
  · exact False.elim (Set.disjoint_left.mp (C.crossingChord_avoids_vertex_disks q j)
      hx (C.vertex_spoke_range_in_disk v hv j p hy))
theorem middle_middle_meeting_chords (E : PolygonalExterior C) (e f : Edge)
    (hef : e ≠ f) (x : Plane) (hx : x ∈ Set.range (E.middlePath e))
    (hy : x ∈ Set.range (E.middlePath f)) :
    ∃ p q : C.InnerIndex, p.1=e ∧ q.1=f ∧
      x ∈ Set.range (C.crossingChord p) ∧ x ∈ Set.range (C.crossingChord q) := by
  have he : ∃ p : C.InnerIndex, p.1=e ∧ x ∈ Set.range (C.crossingChord p) := by
    rcases (E.middlePath_range_iff e x).mp hx with ⟨i,hi,hh⟩ | hh
    · exact False.elim (hef ((E.middle_exterior_edge_eq f i x hy hh).trans hi).symm)
    · exact hh
  have hf : ∃ q : C.InnerIndex, q.1=f ∧ x ∈ Set.range (C.crossingChord q) := by
    rcases (E.middlePath_range_iff f x).mp hy with ⟨i,hi,hh⟩ | hh
    · exact False.elim (hef ((E.middle_exterior_edge_eq e i x hx hh).trans hi))
    · exact hh
  obtain ⟨p,hp,hxp⟩ := he
  obtain ⟨q,hq,hxq⟩ := hf
  exact ⟨p,q,hp,hq,hxp,hxq⟩
end Paper170Geometry.PolygonalExterior
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}
theorem vertex_spokes_meeting (C : DrawingPassages D)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (j k : Vertex) (p : C.PortsAt (C.vertexMark j)) (q : C.PortsAt (C.vertexMark k))
    (hpq : p.val ≠ q.val) (x : Plane)
    (hx : x ∈ Set.range (Path.segment (v j) (C.portPoint p.val)))
    (hy : x ∈ Set.range (Path.segment (v k) (C.portPoint q.val))) : x=v j := by
  by_cases hjk : j=k
  · subst k
    exact spokes_meet_only_at_center _ _ _ (hdet j p q (fun he => hpq (congrArg Subtype.val he)))
      (by simpa only [Path.range_segment] using hx) (by simpa only [Path.range_segment] using hy)
  · exact False.elim (Set.disjoint_left.mp (C.vertex_spokes_disjoint_of_vertices_ne v hv j k hjk p q) hx hy)
end DrawingPassages
namespace PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}
theorem assembled_spoke_meeting (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (e : Edge) (j : Vertex) (p : C.PortsAt (C.vertexMark j))
    (hep : e ≠ p.val.1.1) (x : Plane) (hx : x ∈ Set.range (E.assembledEdge v e))
    (hy : x ∈ Set.range (Path.segment (v j) (C.portPoint p.val))) : x=v j := by
  rw [assembledEdge,Path.trans_range,Path.trans_range] at hx
  rcases hx with (hx | hx) | hx
  · exact C.vertex_spokes_meeting v hv hdet j _ p (C.startPortAt e)
      (fun he => hep (congrArg (fun r : C.Port => r.1.1) he).symm) x hy hx
  · exact False.elim (hep (E.middle_spoke_edge_eq v hv e j p x hx hy))
  · rw [endSpoke_range] at hx
    exact C.vertex_spokes_meeting v hv hdet j _ p (C.endPortAt e)
      (fun he => hep (congrArg (fun r : C.Port => r.1.1) he).symm) x hy hx
theorem assembled_meeting_chords (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (e f : Edge) (hef : e ≠ f) (x : Plane)
    (havoid : ∀ j, x ≠ v j) (hx : x ∈ Set.range (E.assembledEdge v e))
    (hy : x ∈ Set.range (E.assembledEdge v f)) :
    ∃ p q : C.InnerIndex, p.1=e ∧ q.1=f ∧
      x ∈ Set.range (C.crossingChord p) ∧ x ∈ Set.range (C.crossingChord q) := by
  have hm (a b : Edge) (hab : a ≠ b)
      (ha : x ∈ Set.range (E.assembledEdge v a)) (hb : x ∈ Set.range (E.assembledEdge v b)) :
      x ∈ Set.range (E.middlePath a) := by
    rw [assembledEdge,Path.trans_range,Path.trans_range] at ha
    rcases ha with (ha | ha) | ha
    · exact False.elim (havoid _ (E.assembled_spoke_meeting v hv hdet b _ (C.startPortAt a)
        (Ne.symm hab) x hb ha))
    · exact ha
    · rw [endSpoke_range] at ha
      exact False.elim (havoid _ (E.assembled_spoke_meeting v hv hdet b _ (C.endPortAt a)
        (Ne.symm hab) x hb ha))
  exact E.middle_middle_meeting_chords e f hef x (hm e f hef hx hy) (hm f e (Ne.symm hef) hy hx)
theorem assembled_crossings_subset (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) :
    Paper170.crossingPoints (E.assembledDrawing v hvinj hv) ⊆ C.chordCrossings := by
  rintro x ⟨e,f,hef,⟨s,hs,he⟩,⟨t,ht,hf⟩⟩
  obtain ⟨p,q,hp,hq,hxp,hxq⟩ := E.assembled_meeting_chords v hv hdet e f hef x
    (fun j heq => E.assembledEdge_interior_avoids_vertices v hv e s hs j (he.trans heq))
    ⟨s,he⟩ ⟨t,hf⟩
  exact ⟨p,q,(fun heq => hef (hp.symm.trans ((congrArg Sigma.fst heq).trans hq))),hxp,hxq⟩
theorem assembled_crossings_finite (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) :
    (Paper170.crossingPoints (E.assembledDrawing v hvinj hv)).Finite :=
  C.chordCrossings_finite.subset (E.assembled_crossings_subset v hvinj hv hdet)
end PolygonalExterior
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}
theorem assembled_no_triples (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (e f g : Edge) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    Paper170.edgeInterior (E.assembledDrawing v hvinj hv) e ∩
      Paper170.edgeInterior (E.assembledDrawing v hvinj hv) f ∩
      Paper170.edgeInterior (E.assembledDrawing v hvinj hv) g=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨⟨⟨s,hs,he⟩,⟨t,ht,hf⟩⟩,⟨u,hu,hg⟩⟩
  have ha : ∀ j, x ≠ v j := fun j heq =>
    E.assembledEdge_interior_avoids_vertices v hv e s hs j (he.trans heq)
  obtain ⟨p,q,hp,hq,hxp,hxq⟩ := E.assembled_meeting_chords v hv hdet e f hef x ha ⟨s,he⟩ ⟨t,hf⟩
  obtain ⟨r,z,hr,hz,hxr,hxz⟩ := E.assembled_meeting_chords v hv hdet e g heg x ha ⟨s,he⟩ ⟨u,hg⟩
  apply C.innerMark_no_triples p q z
  · intro heq
    exact hef (hp.symm.trans ((congrArg Sigma.fst heq).trans hq))
  · intro heq
    exact heg (hp.symm.trans ((congrArg Sigma.fst heq).trans hz))
  · intro heq
    exact hfg (hq.symm.trans ((congrArg Sigma.fst heq).trans hz))
  · exact C.chord_meeting_marks_eq p q hxp hxq
  · exact C.chord_meeting_marks_eq p z hxp hxz
end Paper170Geometry.PolygonalExterior
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
theorem portPoint_mem_exterior (E : PolygonalExterior C) (p : C.Port) :
    C.portPoint p ∈ Set.range (E.chain p.1).path := by
  rcases p with ⟨i,b⟩
  cases b
  · exact ⟨0,(E.chain i).path.source⟩
  · exact ⟨1,(E.chain i).path.target⟩
theorem assembled_exterior_edge_eq (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : Edge) (i : C.ArcIndex) (x : Plane)
    (hx : x ∈ Set.range (E.assembledEdge v e)) (hy : x ∈ Set.range (E.chain i).path) : e=i.1 := by
  rw [assembledEdge,Path.trans_range,Path.trans_range] at hx
  rcases hx with (hx | hx) | hx
  · obtain ⟨s,hs⟩ := hy
    obtain ⟨t,ht⟩ := hx
    have hh := E.exterior_spoke_meeting_parameters v hv i _ (C.startPortAt e) s t (hs.trans ht.symm)
    rcases hh.2 with ⟨_,he⟩ | ⟨_,he⟩
    · exact (congrArg (fun p : C.Port => p.1.1) he).symm
    · exact (congrArg (fun p : C.Port => p.1.1) he).symm
  · exact E.middle_exterior_edge_eq e i x hx hy
  · rw [endSpoke_range] at hx
    obtain ⟨s,hs⟩ := hy
    obtain ⟨t,ht⟩ := hx
    have hh := E.exterior_spoke_meeting_parameters v hv i _ (C.endPortAt e) s t (hs.trans ht.symm)
    rcases hh.2 with ⟨_,he⟩ | ⟨_,he⟩
    · exact (congrArg (fun p : C.Port => p.1.1) he).symm
    · exact (congrArg (fun p : C.Port => p.1.1) he).symm
theorem assembled_port_unique_edge (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : Edge) (p : C.Port)
    (hp : C.portPoint p ∈ Set.range (E.assembledEdge v e)) : e=p.1.1 :=
  E.assembled_exterior_edge_eq v hv e p.1 (C.portPoint p) hp (E.portPoint_mem_exterior p)
end Paper170Geometry.PolygonalExterior
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}
def crossingDisk (C : DrawingPassages D) (p : C.InnerIndex) : Set Plane :=
  {x | squaredLength (x-(C.innerMark p).val) < C.radius^2}
theorem crossingDisk_isOpen (C : DrawingPassages D) (p : C.InnerIndex) : IsOpen (C.crossingDisk p) := by
  apply isOpen_lt _ continuous_const
  unfold squaredLength
  fun_prop
theorem crossingDisk_subset_closed (C : DrawingPassages D) (p : C.InnerIndex) :
    C.crossingDisk p ⊆ closedRoundDisk (C.innerMark p).val C.radius := by
  intro x hx
  exact (show squaredLength (x-(C.innerMark p).val) < C.radius^2 from hx).le
theorem crossingDisk_disjoint_vertex_disk (C : DrawingPassages D) (p : C.InnerIndex)
    (j : Vertex) :
    Disjoint (C.crossingDisk p) (closedRoundDisk (D.vertex j) C.radius) := by
  have hn : C.innerMark p ≠ C.vertexMark j := by
    intro he
    exact crossing_not_vertex D (C.innerMark p).val (C.innerMark_is_crossing p) j (congrArg Subtype.val he)
  exact (C.disks_disjoint _ _ hn).mono (C.crossingDisk_subset_closed p) Set.Subset.rfl
theorem crossingChord_openTrace_iff (C : DrawingPassages D) (p : C.InnerIndex)
    (x : Plane) (hx : x ∈ C.crossingDisk p) :
    x ∈ Set.range (C.crossingChord p) ↔
      x ∈ openSegmentTrace (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p)) := by
  constructor
  · rintro ⟨t,ht⟩
    have ht0 : t ≠ 0 := by
      intro he
      subst t
      rw [Path.source] at ht
      change squaredLength (x-(C.innerMark p).val) < C.radius^2 at hx
      rw [← ht,C.incomingPoint_on_circle] at hx
      exact lt_irrefl _ hx
    have ht1 : t ≠ 1 := by
      intro he
      subst t
      rw [Path.target] at ht
      change squaredLength (x-(C.innerMark p).val) < C.radius^2 at hx
      rw [← ht,C.outgoingPoint_on_circle] at hx
      exact lt_irrefl _ hx
    refine ⟨t.val,⟨?_,?_⟩,?_⟩
    · exact lt_of_le_of_ne t.property.1 (fun he => ht0 (Subtype.ext he.symm))
    · exact lt_of_le_of_ne t.property.2 (fun he => ht1 (Subtype.ext he))
    · simpa only [crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht
  · rintro ⟨t,ht,he⟩
    refine ⟨⟨t,ht.1.le,ht.2.le⟩,?_⟩
    simpa only [crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using he
end DrawingPassages
namespace PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}
theorem assembled_range_in_crossingDisk (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p : C.InnerIndex) (x : Plane) (hx : x ∈ C.crossingDisk p) :
    x ∈ Set.range (E.assembledEdge v p.1) ↔ x ∈ Set.range (C.crossingChord p) := by
  constructor
  · intro he
    rcases (E.assembledEdge_range_iff v p.1 x).mp he with (he | ⟨i,hi,he⟩ | ⟨q,hq,he⟩) | he
    · exact False.elim (Set.disjoint_left.mp (C.crossingDisk_disjoint_vertex_disk p _)
        hx (C.vertex_spoke_range_in_disk v hv _ (C.startPortAt p.1) he))
    · obtain ⟨t,rfl⟩ := he
      exact False.elim (hx.not_ge (E.outside_open_disks i t (C.innerMark p)))
    · have hm : C.innerMark q=C.innerMark p := by
        by_contra hn
        exact Set.disjoint_left.mp (C.disks_disjoint _ _ hn)
          (C.crossingChord_range_subset_disk q he) (C.crossingDisk_subset_closed p hx)
      have hqp := C.innerIndex_eq_of_edge_mark q p hq hm
      exact hqp ▸ he
    · rw [endSpoke_range] at he
      exact False.elim (Set.disjoint_left.mp (C.crossingDisk_disjoint_vertex_disk p _)
        hx (C.vertex_spoke_range_in_disk v hv _ (C.endPortAt p.1) he))
  · intro he
    apply (E.assembledEdge_range_iff v p.1 x).mpr
    exact Or.inl (Or.inr (Or.inr ⟨p,rfl,he⟩))
theorem assembled_trace_in_crossingDisk (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p : C.InnerIndex) (x : Plane) (hx : x ∈ C.crossingDisk p) :
    x ∈ Paper170.edgeInterior (E.assembledDrawing v hvinj hv) p.1 ↔
      x ∈ openSegmentTrace (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p)) := by
  have havoid : ∀ j, x ≠ v j := by
    intro j he
    exact Set.disjoint_left.mp (C.crossingDisk_disjoint_vertex_disk p j) hx (he.symm ▸ (hv j).le)
  rw [← C.crossingChord_openTrace_iff p x hx,← E.assembled_range_in_crossingDisk v hv p x hx]
  constructor
  · rintro ⟨t,ht,he⟩
    exact ⟨t,he⟩
  · rintro ⟨t,he⟩
    have ht0 : t ≠ 0 := by
      intro ht
      subst t
      rw [Path.source] at he
      exact havoid _ he.symm
    have ht1 : t ≠ 1 := by
      intro ht
      subst t
      rw [Path.target] at he
      exact havoid _ he.symm
    exact ⟨t,⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
      lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩,he⟩
end PolygonalExterior
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.DrawingPassages
variable  {D : FiniteIntersectionDrawing graph}
theorem crossingChord_meeting_proper (C : DrawingPassages D) (p q : C.InnerIndex)
    (hpq : p ≠ q) (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p))
    (hxq : x ∈ Set.range (C.crossingChord q)) :
    x ∈ C.crossingDisk p ∧
      Paper170.ProperCrossing
        (openSegmentTrace (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p)))
        (openSegmentTrace (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q))) x := by
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  obtain ⟨s,hs⟩ := hxp
  obtain ⟨t,ht⟩ := hxq
  have hst : segmentPoint (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p)) s.val =
      segmentPoint (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)) t.val := by
    simpa only [crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hs.trans ht.symm
  obtain ⟨hd,hsi,hti⟩ := C.crossing_chords_transverse_at_mark p q hpq hm s.val s.property t.val t.property hst
  refine ⟨?_,?_⟩
  · rw [← hs]
    exact C.crossingChord_interior_in_disk p s hsi
  · constructor
    apply properCrossing_openSegments _ _ _ _ x hd
    · exact ⟨s.val,hsi,by simpa only [crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hs⟩
    · exact ⟨t.val,hti,by simpa only [crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht⟩
end DrawingPassages
namespace PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}
theorem assembled_crossings_proper (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (e f : Edge) (hef : e ≠ f) (x : Plane)
    (hx : x ∈ Paper170.edgeInterior (E.assembledDrawing v hvinj hv) e)
    (hy : x ∈ Paper170.edgeInterior (E.assembledDrawing v hvinj hv) f) :
    Paper170.ProperCrossing (Paper170.edgeInterior (E.assembledDrawing v hvinj hv) e)
      (Paper170.edgeInterior (E.assembledDrawing v hvinj hv) f) x := by
  obtain ⟨s,hs,he⟩ := hx
  obtain ⟨t,ht,hf⟩ := hy
  obtain ⟨p,q,hp,hq,hxp,hxq⟩ := E.assembled_meeting_chords v hv hdet e f hef x
    (fun j heq => E.assembledEdge_interior_avoids_vertices v hv e s hs j (he.trans heq)) ⟨s,he⟩ ⟨t,hf⟩
  have hpq : p ≠ q := fun heq => hef (hp.symm.trans ((congrArg Sigma.fst heq).trans hq))
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  obtain ⟨hxin,hproper⟩ := C.crossingChord_meeting_proper p q hpq x hxp hxq
  constructor
  apply properCrossing_of_local_eq _ _ _ _ x hproper.chart_exists (C.crossingDisk p) (C.crossingDisk_isOpen p) hxin
  · intro z hz
    simpa only [hp] using (E.assembled_trace_in_crossingDisk v hvinj hv p z hz).symm
  · intro z hz
    have hzq : z ∈ C.crossingDisk q := by
      change squaredLength (z-(C.innerMark q).val) < C.radius^2
      rw [← hm]
      exact hz
    simpa only [hq] using (E.assembled_trace_in_crossingDisk v hvinj hv q z hzq).symm
def assembledAdmissible (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) : Paper170.AdmissibleDrawing graph where
  toContinuousDrawing := E.assembledDrawing v hvinj hv
  crossings_finite := E.assembled_crossings_finite v hvinj hv hdet
  crossings_proper := E.assembled_crossings_proper v hvinj hv hdet
  no_triples := E.assembled_no_triples v hvinj hv hdet
theorem assembled_crossingCount_le (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) :
    Paper170.crossingCount (E.assembledAdmissible v hvinj hv hdet) ≤ finiteCrossingCount D := by
  have h := Set.ncard_le_ncard (E.assembled_crossings_subset v hvinj hv hdet) C.chordCrossings_finite
  have hcount : Paper170.crossingCount (E.assembledAdmissible v hvinj hv hdet)=
      (Paper170.crossingPoints (E.assembledDrawing v hvinj hv)).ncard := by
    rw [Set.ncard_eq_toFinset_card _ (E.assembled_crossings_finite v hvinj hv hdet)]
    rfl
  rw [hcount]
  exact h.trans C.chordCrossings_ncard_le
end PolygonalExterior
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
namespace PolygonalExterior
variable  {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}
theorem middlePath_hasFiniteAffineCover (E : PolygonalExterior C) (e : Edge) :
    HasFiniteAffineCover (E.middlePath e) :=
  alternatingPath_hasFiniteAffineCover _ _ _ _ (fun i => (E.chain (C.orderedArc e i)).hasFiniteAffineCover)
    (fun _ => hasFiniteAffineCover_segment _ _) _
theorem assembledEdge_hasFiniteAffineCover (E : PolygonalExterior C)
    (v : Vertex → Plane) (e : Edge) :
    HasFiniteAffineCover (E.assembledEdge v e) := by
  apply HasFiniteAffineCover.trans
  · apply HasFiniteAffineCover.trans (hasFiniteAffineCover_segment _ _)
    exact E.middlePath_hasFiniteAffineCover e
  · simp only [endSpoke,Path.segment_symm]
    exact hasFiniteAffineCover_segment _ _
end PolygonalExterior
/-- Finite contacts and no triples suffice to construct genuinely proper crossings. -/
theorem finite_intersection_normalization [Fintype Vertex] [Fintype Edge] (D : FiniteIntersectionDrawing graph) :
    ∃ D' : Paper170.AdmissibleDrawing graph,
      (∀ e, HasFiniteAffineCover (D'.edge e)) ∧ Paper170.crossingCount D' ≤ finiteCrossingCount D := by
  obtain ⟨C⟩ := nonempty_drawingPassages D
  obtain ⟨E⟩ := nonempty_polygonalExterior C
  obtain ⟨v,hvinj,hv,hne,hdet⟩ := C.exists_drawing_vertex_placement
  exact ⟨E.assembledAdmissible v hvinj hv hdet,E.assembledEdge_hasFiniteAffineCover v,
    E.assembled_crossingCount_le v hvinj hv hdet⟩
end Paper170Geometry
end
end
section
noncomputable section
open Set
namespace Paper170Geometry
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace DrawingPassages
variable {D : FiniteIntersectionDrawing graph}
theorem chordCrossingOrigin_eq_innerMark (C : DrawingPassages D) {y : Plane}
    (hy : y ∈ C.chordCrossings) (p : C.InnerIndex) (hp : y ∈ Set.range (C.crossingChord p)) :
    C.chordCrossingOrigin y = (C.innerMark p).val := by
  unfold chordCrossingOrigin
  rw [dif_pos hy]
  obtain ⟨r,s,hrs,hr,hs,hyr,hys⟩ := (C.chord_crossing_original_mark hy).choose_spec.2
  exact congrArg Subtype.val ((C.chord_meeting_marks_eq p r hp hyr).trans hr).symm
end DrawingPassages
namespace PolygonalExterior
variable {D : FiniteIntersectionDrawing graph} {C : DrawingPassages D}
theorem assembled_origin_mem_pair (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (e f : Edge) (hef : e ≠ f) (y : Plane)
    (he : y ∈ Paper170.edgeInterior (E.assembledDrawing v hvinj hv) e)
    (hf : y ∈ Paper170.edgeInterior (E.assembledDrawing v hvinj hv) f) :
    C.chordCrossingOrigin y ∈ Paper170.edgeInterior D.toContinuousDrawing e ∧
      C.chordCrossingOrigin y ∈ Paper170.edgeInterior D.toContinuousDrawing f := by
  have hy := E.assembled_crossings_subset v hvinj hv hdet ⟨e,f,hef,he,hf⟩
  obtain ⟨s,hs,hys⟩ := he
  obtain ⟨t,ht,hyt⟩ := hf
  obtain ⟨p,q,hp,hq,hyp,hyq⟩ := E.assembled_meeting_chords v hv hdet e f hef y
    (fun j heq => E.assembledEdge_interior_avoids_vertices v hv e s hs j (hys.trans heq))
    ⟨s,hys⟩ ⟨t,hyt⟩
  constructor
  · rw [C.chordCrossingOrigin_eq_innerMark hy p hyp, ← hp]
    exact ⟨C.node p.1 p.2.val,C.inner_parameter_interior p,rfl⟩
  · rw [C.chordCrossingOrigin_eq_innerMark hy q hyq, ← hq]
    exact ⟨C.node q.1 q.2.val,C.inner_parameter_interior q,rfl⟩
theorem assembled_origin_surj_of_count_eq (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (hcount : Paper170.crossingCount (E.assembledAdmissible v hvinj hv hdet) = finiteCrossingCount D) :
    Set.SurjOn C.chordCrossingOrigin (Paper170.crossingPoints (E.assembledDrawing v hvinj hv))
      (Paper170.crossingPoints D.toContinuousDrawing) := by
  have hsub := E.assembled_crossings_subset v hvinj hv hdet
  have hmap := C.chordCrossingOrigin_mapsTo.mono_left hsub
  have hinj := C.chordCrossingOrigin_injOn.mono hsub
  have hsize : (Paper170.crossingPoints D.toContinuousDrawing).ncard ≤
      (C.chordCrossingOrigin '' Paper170.crossingPoints (E.assembledDrawing v hvinj hv)).ncard := by
    rw [hinj.ncard_image, ← finiteCrossingCount_eq_ncard]
    rw [Set.ncard_eq_toFinset_card _ (E.assembled_crossings_finite v hvinj hv hdet)]
    exact hcount.ge
  have heq := Set.eq_of_subset_of_ncard_le hmap.image_subset hsize D.crossings_finite
  intro x hx
  rw [← heq] at hx
  exact hx
theorem assembled_pair_retained_of_count_eq
    {D₀ : Paper170.AdmissibleDrawing graph} {C₀ : DrawingPassages D₀.toFiniteIntersectionDrawing}
    (E : PolygonalExterior C₀) (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D₀.vertex j) < C₀.radius^2)
    (hdet : ∀ j (p q : C₀.PortsAt (C₀.vertexMark j)), p ≠ q →
      det2 (C₀.portPoint p.val-v j) (C₀.portPoint q.val-v j) ≠ 0)
    (hcount : Paper170.crossingCount (E.assembledAdmissible v hvinj hv hdet) =
      Paper170.crossingCount D₀)
    (e f : Edge) (hef : e ≠ f) (x : Plane)
    (hxe : x ∈ Paper170.edgeInterior D₀.toContinuousDrawing e)
    (hxf : x ∈ Paper170.edgeInterior D₀.toContinuousDrawing f) :
    ∃ y, y ∈ Paper170.edgeInterior (E.assembledDrawing v hvinj hv) e ∧
      y ∈ Paper170.edgeInterior (E.assembledDrawing v hvinj hv) f := by
  obtain ⟨y,hy,hxy⟩ := E.assembled_origin_surj_of_count_eq v hvinj hv hdet hcount
    (show x ∈ Paper170.crossingPoints D₀.toContinuousDrawing from ⟨e,f,hef,hxe,hxf⟩)
  obtain ⟨a,b,hab,hya,hyb⟩ := hy
  have hold := E.assembled_origin_mem_pair v hvinj hv hdet a b hab y hya hyb
  rw [hxy] at hold
  have ha := (crossing_incident_iff D₀ x e f hef hxe hxf a).mp hold.1
  have hb := (crossing_incident_iff D₀ x e f hef hxe hxf b).mp hold.2
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact False.elim (hab rfl)
  · exact ⟨y,hya,hyb⟩
  · exact ⟨y,hyb,hya⟩
  · exact False.elim (hab rfl)
end PolygonalExterior
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
theorem exists_drawing_subdivision_at [Fintype Vertex] (D : Paper170.AdmissibleDrawing graph)
    (hpoly : ∀ e, HasFiniteAffineCover (D.edge e)) (S : Set Plane) (hS : S.Finite) :
    ∃ P : ∀ e, PolygonalParametrization (D.edge e),
      (∀ e t, D.edge e t ∈ drawingMarks D.toFiniteIntersectionDrawing → t ∈ Set.range (P e).knot) ∧
      (∀ e t, D.edge e t ∈ S → t ∈ Set.range (P e).knot) := by
  classical
  have hfinite (e : Edge) : ((D.edge e) ⁻¹' (drawingMarks D.toFiniteIntersectionDrawing ∪ S)).Finite :=
    ((drawingMarks_finite D.toFiniteIntersectionDrawing).union hS).preimage (D.edge_injective e).injOn
  have hex (e : Edge) := (hpoly e).refine (hfinite e).toFinset
  choose P hP using hex
  refine ⟨P,?_,?_⟩
  · intro e t ht
    exact hP e (by simpa using Or.inl ht)
  · intro e t ht
    exact hP e (by simpa using Or.inr ht)
namespace PolygonalExterior
variable {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
theorem exists_assembled_port_subdivision [Fintype Vertex] [Fintype Edge] (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0) :
    ∃ P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e),
      (∀ e t, E.assembledEdge v e t ∈ drawingMarks (E.assembledAdmissible v hvinj hv hdet).toFiniteIntersectionDrawing →
        t ∈ Set.range (P e).knot) ∧
      (∀ e t, E.assembledEdge v e t ∈ Set.range C.portPoint → t ∈ Set.range (P e).knot) :=
  exists_drawing_subdivision_at (E.assembledAdmissible v hvinj hv hdet)
    (E.assembledEdge_hasFiniteAffineCover v) (Set.range C.portPoint) (Set.finite_range _)
end PolygonalExterior
end Paper170Geometry
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.DrawingPassages
variable  {D : Paper170.AdmissibleDrawing graph}
def reconnectionStart (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex) (i : Bool) : Plane :=
  if i then C.portPoint (C.incomingPort p) else C.portPoint (C.incomingPort q)
def reconnectionEnd (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex) (i : Bool) : Plane :=
  if i then C.portPoint (C.outgoingPort q) else C.portPoint (C.outgoingPort p)
theorem reconnection_endpoints_ne (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex) (i : Bool) :
    C.reconnectionStart p q i ≠ C.reconnectionEnd p q i := by
  cases i
  · exact C.portPoint_injective.ne (C.incomingPort_ne_outgoingPort q p)
  · exact C.portPoint_injective.ne (C.incomingPort_ne_outgoingPort p q)
theorem crossingChord_meeting_segmentsCrossProperly (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex)
    (hpq : p ≠ q) (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p))
    (hxq : x ∈ Set.range (C.crossingChord q)) :
    SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)) := by
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  obtain ⟨s,hs⟩ := hxp
  obtain ⟨t,ht⟩ := hxq
  have he : segmentPoint (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p)) s.val=
      segmentPoint (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)) t.val := by
    simpa only [crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hs.trans ht.symm
  obtain ⟨hd,hsi,hti⟩ := C.crossing_chords_transverse_at_mark p q hpq hm s.val s.property t.val t.property he
  exact ⟨hd,s.val,hsi,t.val,hti,he⟩
theorem reconnection_chords_disjoint (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex)
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q))) :
    ∀ i j : Bool, i ≠ j → Disjoint
      (segment ℝ (C.reconnectionStart p q i) (C.reconnectionEnd p q i))
      (segment ℝ (C.reconnectionStart p q j) (C.reconnectionEnd p q j)) := by
  have hh := crossing_reconnections_disjoint _ _ _ _ hcross
  intro i j hij
  cases i <;> cases j
  · exact False.elim (hij rfl)
  · exact hh
  · exact hh.symm
  · exact False.elim (hij rfl)
theorem reconnection_endpoints_on_circle (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex)
    (hm : C.innerMark p=C.innerMark q) (i : Bool) :
    squaredLength (C.reconnectionStart p q i-(C.innerMark p).val)=C.radius^2 ∧
      squaredLength (C.reconnectionEnd p q i-(C.innerMark p).val)=C.radius^2 := by
  cases i
  · change squaredLength (C.portPoint (C.incomingPort q)-(C.innerMark p).val)=C.radius^2 ∧
      squaredLength (C.portPoint (C.outgoingPort p)-(C.innerMark p).val)=C.radius^2
    exact ⟨by simpa only [hm] using C.incomingPoint_on_circle q,C.outgoingPoint_on_circle p⟩
  · change squaredLength (C.portPoint (C.incomingPort p)-(C.innerMark p).val)=C.radius^2 ∧
      squaredLength (C.portPoint (C.outgoingPort q)-(C.innerMark p).val)=C.radius^2
    exact ⟨C.incomingPoint_on_circle p,by simpa only [hm] using C.outgoingPoint_on_circle q⟩
theorem reconnection_open_in_disk (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex)
    (hm : C.innerMark p=C.innerMark q) (i : Bool) :
    openSegmentTrace (C.reconnectionStart p q i) (C.reconnectionEnd p q i) ⊆ C.crossingDisk p := by
  rintro x ⟨t,ht,rfl⟩
  exact round_chord_in_open_disk _ _ _ _ (C.reconnection_endpoints_on_circle p q hm i).1
    (C.reconnection_endpoints_on_circle p q hm i).2 (C.reconnection_endpoints_ne p q i) t ht
end Paper170Geometry.DrawingPassages
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.DrawingPassages
variable  {D : Paper170.AdmissibleDrawing graph}
theorem reconnection_segment_in_disk (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex)
    (hm : C.innerMark p=C.innerMark q) (i : Bool) :
    segment ℝ (C.reconnectionStart p q i) (C.reconnectionEnd p q i) ⊆
      closedRoundDisk (C.innerMark p).val C.radius := by
  intro x hx
  rw [← Path.range_segment] at hx
  obtain ⟨t,ht⟩ := hx
  rw [← ht]
  change squaredLength ((Path.segment _ _) t-(C.innerMark p).val) ≤ C.radius^2
  simp only [Path.segment_apply,AffineMap.lineMap_apply_module]
  exact round_chord_in_disk _ _ _ _ (C.reconnection_endpoints_on_circle p q hm i).1
    (C.reconnection_endpoints_on_circle p q hm i).2 t.val t.property
theorem reconnection_segment_avoids_vertices (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex)
    (hm : C.innerMark p=C.innerMark q) (v : Vertex → Plane)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2) (i : Bool) (j : Vertex) :
    v j ∉ segment ℝ (C.reconnectionStart p q i) (C.reconnectionEnd p q i) := by
  intro hx
  have hn : C.innerMark p ≠ C.vertexMark j := by
    intro he
    exact crossing_not_vertex D.toFiniteIntersectionDrawing (C.innerMark p).val (C.innerMark_is_crossing p) j (congrArg Subtype.val he)
  exact Set.disjoint_left.mp (C.disks_disjoint _ _ hn)
    (C.reconnection_segment_in_disk p q hm i hx) (hv j).le
end Paper170Geometry.DrawingPassages
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
theorem segment_avoids_of_affine_positive (f : Plane → ℝ) (a b x : Plane)
    (hf : ∀ t, f (segmentPoint a b t)=(1-t)*f a+t*f b)
    (ha : 0 < f a) (hb : 0 < f b) (hx : f x=0) : x ∉ segment ℝ a b := by
  intro h
  rw [← Path.range_segment] at h
  obtain ⟨t,ht⟩ := h
  have ht' : segmentPoint a b t.val=x := by
    simpa only [Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht
  have hp := convex_combination_pos (f a) (f b) t.val ha hb t.property
  rw [← hf t.val,ht',hx] at hp
  exact lt_irrefl 0 hp
theorem crossing_reconnections_avoid_point (a b c d x : Plane)
    (hd : det2 (b-a) (d-c) ≠ 0) (s t : ℝ)
    (hs : s ∈ Set.Ioo (0 : ℝ) 1) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hx : x=segmentPoint a b s) (hy : x=segmentPoint c d t) :
    x ∉ segment ℝ c b ∧ x ∉ segment ℝ a d := by
  let F := crossingCoordinates x (b-a) (d-c)
  have hFa : F a=(-s,0) := by
    simpa only [segmentPoint_zero,zero_sub] using crossingCoordinates_first_segment a b c d x s 0 hd hx
  have hFb : F b=(1-s,0) := by
    simpa only [segmentPoint_one] using crossingCoordinates_first_segment a b c d x s 1 hd hx
  have hFc : F c=(0,-t) := by
    simpa only [segmentPoint_zero,zero_sub] using crossingCoordinates_second_segment a b c d x t 0 hd hy
  have hFd : F d=(0,1-t) := by
    simpa only [segmentPoint_one] using crossingCoordinates_second_segment a b c d x t 1 hd hy
  have hF (u v : Plane) (r : ℝ) : F (segmentPoint u v r)=segmentPoint (F u) (F v) r :=
    crossingCoordinates_affine x (b-a) (d-c) u v r
  have hzero : F x=(0,0) := crossingCoordinates_origin x (b-a) (d-c)
  constructor
  · apply segment_avoids_of_affine_positive (fun z => (F z).1-(F z).2) c b x
    · intro r
      rw [hF]
      dsimp [segmentPoint]
      ring
    · rw [hFc]
      dsimp
      linarith [ht.1]
    · rw [hFb]
      dsimp
      linarith [hs.2]
    · rw [hzero]
      norm_num
  · apply segment_avoids_of_affine_positive (fun z => (F z).2-(F z).1) a d x
    · intro r
      rw [hF]
      dsimp [segmentPoint]
      ring
    · rw [hFa]
      dsimp
      linarith [hs.1]
    · rw [hFd]
      dsimp
      linarith [ht.2]
    · rw [hzero]
      norm_num
theorem DrawingPassages.reconnection_avoids_chord_meeting  {D : Paper170.AdmissibleDrawing graph}
    (C : DrawingPassages D.toFiniteIntersectionDrawing) (p q : C.InnerIndex) (hpq : p ≠ q) (x : Plane)
    (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    x ∈ C.crossingDisk p ∧ ∀ i : Bool,
      x ∉ segment ℝ (C.reconnectionStart p q i) (C.reconnectionEnd p q i) := by
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  obtain ⟨s,hs⟩ := hxp
  obtain ⟨t,ht⟩ := hxq
  have hs' : segmentPoint (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p)) s.val=x := by
    simpa only [DrawingPassages.crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using hs
  have ht' : segmentPoint (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)) t.val=x := by
    simpa only [DrawingPassages.crossingChord,Path.segment_apply,AffineMap.lineMap_apply_module,segmentPoint] using ht
  obtain ⟨hd,hsi,hti⟩ := C.crossing_chords_transverse_at_mark p q hpq hm s.val s.property t.val t.property
    (hs'.trans ht'.symm)
  constructor
  · change squaredLength (x-(C.innerMark p).val) < C.radius^2
    rw [← hs]
    exact C.crossingChord_interior_in_disk p s hsi
  · have ha := crossing_reconnections_avoid_point _ _ _ _ x hd s.val t.val hsi hti hs'.symm ht'.symm
    intro i
    cases i
    · exact ha.1
    · exact ha.2
end Paper170Geometry
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}
def crossingSurgeryGraph (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q : C.InnerIndex) : SimpleGraph Plane :=
  segmentAugmentedGraph (exteriorSegmentGraph (drawingSubdivisionGraph P) (C.crossingDisk p))
    (C.reconnectionStart p q) (C.reconnectionEnd p q) (C.reconnection_endpoints_ne p q)
theorem crossingSurgeryGraph_embedding (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e))
    (hmark : ∀ e t, D'.edge e t ∈ drawingMarks D'.toFiniteIntersectionDrawing → t ∈ Set.range (P e).knot)
    (hport : ∀ e t, D'.edge e t ∈ Set.range C.portPoint → t ∈ Set.range (P e).knot)
    (p q : C.InnerIndex) (hm : C.innerMark p=C.innerMark q)
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q))) :
    StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id := by
  have hemb := drawingSubdivisionGraph_embedding P hmark
  have houtEmb : StraightEdgeEmbedding
      (exteriorSegmentGraph (drawingSubdivisionGraph P) (C.crossingDisk p)) id := by
    refine ⟨hemb.1,?_⟩
    intro a b c d hab hcd x hx hy
    exact hemb.2 a b c d hab.1 hcd.1 x hx hy
  apply segmentAugmentedGraph_embedding _ _ _ _ houtEmb (C.crossingDisk p)
  · intro x y hxy
    exact hxy.2
  · exact C.reconnection_open_in_disk p q hm
  · exact C.reconnection_chords_disjoint p q hcross
  · intro i x y hxy
    constructor
    · apply drawingSubdivisionGraph_point_endpoint P _ ?_ x y hxy.1
      intro e t ht
      apply hport e t
      cases i
      · exact ⟨C.incomingPort q,ht.symm⟩
      · exact ⟨C.incomingPort p,ht.symm⟩
    · apply drawingSubdivisionGraph_point_endpoint P _ ?_ x y hxy.1
      intro e t ht
      apply hport e t
      cases i
      · exact ⟨C.outgoingPort p,ht.symm⟩
      · exact ⟨C.outgoingPort q,ht.symm⟩
theorem exterior_le_crossingSurgeryGraph (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q : C.InnerIndex) :
    exteriorSegmentGraph (drawingSubdivisionGraph P) (C.crossingDisk p) ≤ crossingSurgeryGraph C P p q :=
  le_segmentAugmentedGraph _ _ _ _
theorem crossingSurgeryGraph_reconnection_adj (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q : C.InnerIndex) (i : Bool) :
    (crossingSurgeryGraph C P p q).Adj (C.reconnectionStart p q i) (C.reconnectionEnd p q i) :=
  segmentAugmentedGraph_added_adj _ _ _ _ i
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
theorem middlePath_contains_chord (E : PolygonalExterior C) (p : C.InnerIndex) :
    OrderedPathPart (E.middlePath p.1) (C.crossingChord p) := by
  rcases p with ⟨e,⟨i,hi⟩⟩
  have hj : i.val-1+1 < C.count e := by omega
  have hinner : C.orderedInner e (i.val-1) hj=⟨e,⟨i,hi⟩⟩ := by
    unfold DrawingPassages.orderedInner
    congr 1
    apply Subtype.ext
    apply Fin.ext
    change i.val-1+1=i.val
    omega
  have hpart : OrderedPathPart (E.middlePath e) (orderedBridge C e (i.val-1)) :=
    alternatingPath_contains_bridge _ _ _ _ (C.count e-1) (i.val-1) (by omega)
  apply hpart.congr_right
  intro t
  rw [orderedBridge_apply (C:=C) e (i.val-1) hj t,hinner]
theorem assembledEdge_contains_chord (E : PolygonalExterior C)
    (v : Vertex → Plane) (p : C.InnerIndex) :
    OrderedPathPart (E.assembledEdge v p.1) (C.crossingChord p) := by
  have h : OrderedPathPart (E.anchoredMiddle p.1) (C.crossingChord p) := E.middlePath_contains_chord p
  exact (h.right (startSpoke C v p.1)).left (endSpoke C v p.1)
theorem assembled_crossing_ports_ordered (E : PolygonalExterior C)
    (v : Vertex → Plane) (p : C.InnerIndex) :
    ∃ u w : unitInterval, u < w ∧
      E.assembledEdge v p.1 u=C.portPoint (C.incomingPort p) ∧
      E.assembledEdge v p.1 w=C.portPoint (C.outgoingPort p) :=
  (E.assembledEdge_contains_chord v p).endpoints_ordered
theorem crossing_port_walk_indices (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
    (hport : ∀ e t, E.assembledEdge v e t ∈ Set.range C.portPoint → t ∈ Set.range (P e).knot)
    (p : C.InnerIndex) :
    ∃ i j : Fin ((P p.1).pieces+1), i < j ∧
      (drawingEdgeWalk P p.1).getVert i.val=C.portPoint (C.incomingPort p) ∧
      (drawingEdgeWalk P p.1).getVert j.val=C.portPoint (C.outgoingPort p) := by
  obtain ⟨u,w,huw,hu,hw⟩ := E.assembled_crossing_ports_ordered v p
  obtain ⟨i,hi⟩ := hport p.1 u ⟨C.incomingPort p,hu.symm⟩
  obtain ⟨j,hj⟩ := hport p.1 w ⟨C.outgoingPort p,hw.symm⟩
  have hij : i < j := by
    by_contra hn
    have hh := (P p.1).increasing.monotone (le_of_not_gt hn)
    rw [hi,hj] at hh
    exact huw.not_ge hh
  refine ⟨i,j,hij,?_,?_⟩
  · rw [drawingEdgeWalk_getVert P p.1 i.val (by omega)]
    have he := (P p.1).vertices_at i
    change (P p.1).vertices i.val=E.assembledEdge v p.1 ((P p.1).knot i) at he
    exact he.trans ((congrArg (E.assembledEdge v p.1) hi).trans hu)
  · rw [drawingEdgeWalk_getVert P p.1 j.val (by omega)]
    have he := (P p.1).vertices_at j
    change (P p.1).vertices j.val=E.assembledEdge v p.1 ((P p.1).knot j) at he
    exact he.trans ((congrArg (E.assembledEdge v p.1) hj).trans hw)
end Paper170Geometry.PolygonalExterior
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
theorem assembled_in_crossingDisk_chord (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : Edge) (p : C.InnerIndex) (x : Plane)
    (hx : x ∈ Set.range (E.assembledEdge v e)) (hxin : x ∈ C.crossingDisk p) :
    ∃ r : C.InnerIndex, r.1=e ∧ C.innerMark r=C.innerMark p ∧ x ∈ Set.range (C.crossingChord r) := by
  rcases (E.assembledEdge_range_iff v e x).mp hx with (hx | ⟨i,hi,hx⟩ | ⟨r,hr,hx⟩) | hx
  · exact False.elim (Set.disjoint_left.mp (C.crossingDisk_disjoint_vertex_disk p _)
      hxin (C.vertex_spoke_range_in_disk v hv _ (C.startPortAt e) hx))
  · obtain ⟨t,rfl⟩ := hx
    exact False.elim (hxin.not_ge (E.outside_open_disks i t (C.innerMark p)))
  · refine ⟨r,hr,?_,hx⟩
    by_contra hn
    exact Set.disjoint_left.mp (C.disks_disjoint _ _ hn)
      (C.crossingChord_range_subset_disk r hx) (C.crossingDisk_subset_closed p hxin)
  · rw [endSpoke_range] at hx
    exact False.elim (Set.disjoint_left.mp (C.crossingDisk_disjoint_vertex_disk p _)
      hxin (C.vertex_spoke_range_in_disk v hv _ (C.endPortAt e) hx))
theorem assembled_crossingDisk_owner (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p q : C.InnerIndex) (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (e : Edge) (x : Plane)
    (hx : x ∈ Set.range (E.assembledEdge v e)) (hxin : x ∈ C.crossingDisk p) : e=p.1 ∨ e=q.1 := by
  obtain ⟨r,hr,hrm,hxr⟩ := E.assembled_in_crossingDisk_chord v hv e p x hx hxin
  rcases C.innerIndex_at_mark_pair p q r hpq hm hrm.symm with rfl | rfl
  · exact Or.inl hr.symm
  · exact Or.inr hr.symm
theorem assembled_other_edge_avoids_crossingDisk (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p q : C.InnerIndex) (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (e : Edge) (hep : e ≠ p.1) (heq : e ≠ q.1) :
    Disjoint (Set.range (E.assembledEdge v e)) (C.crossingDisk p) := by
  apply Set.disjoint_left.mpr
  intro x hx hxin
  rcases E.assembled_crossingDisk_owner v hv p q hpq hm e x hx hxin with h | h
  · exact hep h
  · exact heq h
end Paper170Geometry.PolygonalExterior
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.DrawingPassages
variable  {D : Paper170.AdmissibleDrawing graph}
theorem crossingChord_parameter_interior (C : DrawingPassages D.toFiniteIntersectionDrawing) (p : C.InnerIndex)
    (t : unitInterval) (ht : C.crossingChord p t ∈ C.crossingDisk p) :
    t ∈ Set.Ioo (0 : unitInterval) 1 := by
  have ht0 : t ≠ 0 := by
    intro he
    subst t
    change squaredLength (C.crossingChord p 0-(C.innerMark p).val) < C.radius^2 at ht
    rw [Path.source,C.incomingPoint_on_circle] at ht
    exact lt_irrefl _ ht
  have ht1 : t ≠ 1 := by
    intro he
    subst t
    change squaredLength (C.crossingChord p 1-(C.innerMark p).val) < C.radius^2 at ht
    rw [Path.target,C.outgoingPoint_on_circle] at ht
    exact lt_irrefl _ ht
  exact ⟨lt_of_le_of_ne (show 0 ≤ t from t.property.1) (Ne.symm ht0),
    lt_of_le_of_ne (show t ≤ 1 from t.property.2) ht1⟩
end DrawingPassages
namespace PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
theorem assembled_crossing_disk_parameter_between (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p : C.InnerIndex) (u w : unitInterval)
    (hu : E.assembledEdge v p.1 u=C.portPoint (C.incomingPort p))
    (hw : E.assembledEdge v p.1 w=C.portPoint (C.outgoingPort p))
    (t : unitInterval) (ht : E.assembledEdge v p.1 t ∈ C.crossingDisk p) : u < t ∧ t < w := by
  obtain ⟨f,hf,he⟩ := E.assembledEdge_contains_chord v p
  have h0 : f 0=u := E.assembledEdge_injective v hv p.1
    (((he 0).trans (C.crossingChord p).source).trans hu.symm)
  have h1 : f 1=w := E.assembledEdge_injective v hv p.1
    (((he 1).trans (C.crossingChord p).target).trans hw.symm)
  have hmem : E.assembledEdge v p.1 t ∈ Set.range (C.crossingChord p) :=
    (E.assembled_range_in_crossingDisk v hv p _ ht).mp ⟨t,rfl⟩
  obtain ⟨s,hs⟩ := hmem
  have hsint := C.crossingChord_parameter_interior p s (hs.symm ▸ ht)
  have hst : f s=t := E.assembledEdge_injective v hv p.1 ((he s).trans hs)
  exact ⟨by simpa only [h0,hst] using hf hsint.1,by simpa only [h1,hst] using hf hsint.2⟩
theorem assembled_crossing_port_clearance (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p : C.InnerIndex) (u w : unitInterval)
    (hu : E.assembledEdge v p.1 u=C.portPoint (C.incomingPort p))
    (hw : E.assembledEdge v p.1 w=C.portPoint (C.outgoingPort p))
    (t : unitInterval) (ht : t ≤ u ∨ w ≤ t) : E.assembledEdge v p.1 t ∉ C.crossingDisk p := by
  intro hmem
  have hbetween := E.assembled_crossing_disk_parameter_between v hv p u w hu hw t hmem
  rcases ht with ht | ht
  · exact hbetween.1.not_ge ht
  · exact hbetween.2.not_ge ht
end PolygonalExterior
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
theorem crossing_cut_traces_disjoint (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
    (p : C.InnerIndex) (i j : Fin ((P p.1).pieces+1))
    (hi : (drawingEdgeWalk P p.1).getVert i.val=C.portPoint (C.incomingPort p))
    (hj : (drawingEdgeWalk P p.1).getVert j.val=C.portPoint (C.outgoingPort p)) :
    Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).take i.val))) (C.crossingDisk p) ∧
      Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).drop j.val))) (C.crossingDisk p) := by
  have hki : (drawingEdgeWalk P p.1).getVert i.val=E.assembledEdge v p.1 ((P p.1).knot i) :=
    (drawingEdgeWalk_getVert P p.1 i.val (by omega)).trans ((P p.1).vertices_at i)
  have hkj : (drawingEdgeWalk P p.1).getVert j.val=E.assembledEdge v p.1 ((P p.1).knot j) :=
    (drawingEdgeWalk_getVert P p.1 j.val (by omega)).trans ((P p.1).vertices_at j)
  have hu := hki.symm.trans hi
  have hw := hkj.symm.trans hj
  constructor
  · apply Set.disjoint_left.mpr
    intro x hx hxin
    obtain ⟨t,ht,he⟩ := drawingEdgeWalk_take_trace P p.1 i hx
    exact E.assembled_crossing_port_clearance v hv p _ _ hu hw t (Or.inl ht.2) (he.symm ▸ hxin)
  · apply Set.disjoint_left.mpr
    intro x hx hxin
    obtain ⟨t,ht,he⟩ := drawingEdgeWalk_drop_trace P p.1 j hx
    exact E.assembled_crossing_port_clearance v hv p _ _ hu hw t (Or.inr ht.1) (he.symm ▸ hxin)
theorem exists_exterior_crossing_cuts (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
    (hport : ∀ e t, E.assembledEdge v e t ∈ Set.range C.portPoint → t ∈ Set.range (P e).knot)
    (p : C.InnerIndex) :
    ∃ i j : Fin ((P p.1).pieces+1), i < j ∧
      (drawingEdgeWalk P p.1).getVert i.val=C.portPoint (C.incomingPort p) ∧
      (drawingEdgeWalk P p.1).getVert j.val=C.portPoint (C.outgoingPort p) ∧
      Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).take i.val))) (C.crossingDisk p) ∧
      Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).drop j.val))) (C.crossingDisk p) := by
  obtain ⟨i,j,hij,hi,hj⟩ := E.crossing_port_walk_indices v hvinj hv hdet P hport p
  exact ⟨i,j,hij,hi,hj,E.crossing_cut_traces_disjoint v hvinj hv hdet P p i j hi hj⟩
end Paper170Geometry.PolygonalExterior
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}
def surgeryPrefixWalk (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q r : C.InnerIndex)
    (i : ℕ) (hi : (drawingEdgeWalk P r.1).getVert i=C.portPoint (C.incomingPort r))
    (hout : Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take i))) (C.crossingDisk p)) :
    (crossingSurgeryGraph C P p q).Walk (D'.vertex ((graph.src r.1))) (C.portPoint (C.incomingPort r)) :=
  ((exteriorGraphWalk ((drawingEdgeWalk P r.1).take i) (C.crossingDisk p) hout).mapLe
    (exterior_le_crossingSurgeryGraph C P p q)).copy rfl hi
def surgerySuffixWalk (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q r : C.InnerIndex)
    (j : ℕ) (hj : (drawingEdgeWalk P r.1).getVert j=C.portPoint (C.outgoingPort r))
    (hout : Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop j))) (C.crossingDisk p)) :
    (crossingSurgeryGraph C P p q).Walk (C.portPoint (C.outgoingPort r)) (D'.vertex ((graph.dst r.1))) :=
  ((exteriorGraphWalk ((drawingEdgeWalk P r.1).drop j) (C.crossingDisk p) hout).mapLe
    (exterior_le_crossingSurgeryGraph C P p q)).copy hj rfl
theorem surgeryPrefixWalk_trace (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q r : C.InnerIndex)
    (i : ℕ) (hi : (drawingEdgeWalk P r.1).getVert i=C.portPoint (C.incomingPort r))
    (hout : Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take i))) (C.crossingDisk p)) :
    Set.range (graphWalkPath id (surgeryPrefixWalk C P p q r i hi hout))=
      Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take i)) := by
  rw [surgeryPrefixWalk,graphWalkPath_copy_range,graphWalkPath_mapLe_range,exteriorGraphWalk_trace]
theorem surgerySuffixWalk_trace (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (p q r : C.InnerIndex)
    (j : ℕ) (hj : (drawingEdgeWalk P r.1).getVert j=C.portPoint (C.outgoingPort r))
    (hout : Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop j))) (C.crossingDisk p)) :
    Set.range (graphWalkPath id (surgerySuffixWalk C P p q r j hj hout))=
      Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop j)) := by
  rw [surgerySuffixWalk,graphWalkPath_copy_range,graphWalkPath_mapLe_range,exteriorGraphWalk_trace]
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}
structure ExteriorCrossingCut (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (P : ∀ e, PolygonalParametrization (D'.edge e)) (r : C.InnerIndex) where
  first : Fin ((P r.1).pieces+1)
  last : Fin ((P r.1).pieces+1)
  ordered : first < last
  first_point : (drawingEdgeWalk P r.1).getVert first.val=C.portPoint (C.incomingPort r)
  last_point : (drawingEdgeWalk P r.1).getVert last.val=C.portPoint (C.outgoingPort r)
  prefix_outside : Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take first.val))) (C.crossingDisk r)
  suffix_outside : Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop last.val))) (C.crossingDisk r)
theorem PolygonalExterior.nonempty_exteriorCrossingCut {C : DrawingPassages D.toFiniteIntersectionDrawing} (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
    (hport : ∀ e t, E.assembledEdge v e t ∈ Set.range C.portPoint → t ∈ Set.range (P e).knot)
    (r : C.InnerIndex) : Nonempty (ExteriorCrossingCut C P r) := by
  obtain ⟨i,j,hij,hi,hj,hout,hout'⟩ := E.exists_exterior_crossing_cuts v hvinj hv hdet P hport r
  exact ⟨⟨i,j,hij,hi,hj,hout,hout'⟩⟩
namespace ExteriorCrossingCut
variable {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q r : C.InnerIndex}
def prefixInSurgery (K : ExteriorCrossingCut C P r) (p q : C.InnerIndex)
    (hr : C.innerMark r=C.innerMark p) :
    (crossingSurgeryGraph C P p q).Walk (D'.vertex ((graph.src r.1))) (C.portPoint (C.incomingPort r)) :=
  surgeryPrefixWalk C P p q r K.first.val K.first_point (by
    simpa only [DrawingPassages.crossingDisk,hr] using K.prefix_outside)
def suffixInSurgery (K : ExteriorCrossingCut C P r) (p q : C.InnerIndex)
    (hr : C.innerMark r=C.innerMark p) :
    (crossingSurgeryGraph C P p q).Walk (C.portPoint (C.outgoingPort r)) (D'.vertex ((graph.dst r.1))) :=
  surgerySuffixWalk C P p q r K.last.val K.last_point (by
    simpa only [DrawingPassages.crossingDisk,hr] using K.suffix_outside)
theorem prefixInSurgery_trace (K : ExteriorCrossingCut C P r) (p q : C.InnerIndex)
    (hr : C.innerMark r=C.innerMark p) :
    Set.range (graphWalkPath id (K.prefixInSurgery p q hr))=
      Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take K.first.val)) :=
  surgeryPrefixWalk_trace _ _ _ _ _ _ _ _
theorem suffixInSurgery_trace (K : ExteriorCrossingCut C P r) (p q : C.InnerIndex)
    (hr : C.innerMark r=C.innerMark p) :
    Set.range (graphWalkPath id (K.suffixInSurgery p q hr))=
      Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop K.last.val)) :=
  surgerySuffixWalk_trace _ _ _ _ _ _ _ _
end ExteriorCrossingCut
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
def walkThroughChord {G : SimpleGraph Plane} {a u v b : Plane}
    (A : G.Walk a u) (h : G.Adj u v) (B : G.Walk v b) : G.Walk a b :=
  (A.append h.toWalk).append B
theorem walkThroughChord_range {G : SimpleGraph Plane} {a u v b : Plane}
    (A : G.Walk a u) (h : G.Adj u v) (B : G.Walk v b) :
    Set.range (graphWalkPath id (walkThroughChord A h B))=
      (Set.range (graphWalkPath id A) ∪ segment ℝ u v) ∪ Set.range (graphWalkPath id B) := by
  rw [walkThroughChord,graphWalkPath_append_range,graphWalkPath_append_range,graphWalkPath_toWalk_range]
variable  {D D' : Paper170.AdmissibleDrawing graph}
theorem surgery_mixed_endpoints_ne (C : DrawingPassages D.toFiniteIntersectionDrawing)
    (p q : C.InnerIndex) (hadj : graph.src p.1 = graph.src q.1 ∨ graph.dst p.1 = graph.dst q.1) :
    D'.vertex (graph.src p.1) ≠ D'.vertex (graph.dst q.1) := by
  intro h
  have he := D'.vertex_injective h
  rcases hadj with hs | ht
  · exact graph.loopless q.1 (hs.symm.trans he)
  · exact graph.loopless p.1 (he.trans ht.symm)
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}
namespace ExteriorCrossingCut
variable {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {r : C.InnerIndex}
theorem first_parameter_lt_one (K : ExteriorCrossingCut C P r) : (P r.1).knot K.first < 1 := by
  rw [← (P r.1).last]
  exact (P r.1).increasing (K.ordered.trans_le (Fin.le_last _))
theorem last_parameter_pos (K : ExteriorCrossingCut C P r) : 0 < (P r.1).knot K.last := by
  rw [← (P r.1).first]
  exact (P r.1).increasing ((Fin.zero_le K.first).trans_lt K.ordered)
theorem prefix_vertex_eq (K : ExteriorCrossingCut C P r) (v : Vertex)
    (hv : D'.vertex v ∈ Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take K.first.val))) :
    v=(graph.src r.1) := by
  obtain ⟨t,ht,he⟩ := drawingEdgeWalk_take_trace P r.1 K.first hv
  rcases drawing_edge_vertex_parameter D'.toContinuousDrawing r.1 t v he with ⟨_,hv⟩ | ⟨ht1,_⟩
  · exact hv
  · exact False.elim ((ht1 ▸ ht.2).not_gt K.first_parameter_lt_one)
theorem suffix_vertex_eq (K : ExteriorCrossingCut C P r) (v : Vertex)
    (hv : D'.vertex v ∈ Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop K.last.val))) :
    v=(graph.dst r.1) := by
  obtain ⟨t,ht,he⟩ := drawingEdgeWalk_drop_trace P r.1 K.last hv
  rcases drawing_edge_vertex_parameter D'.toContinuousDrawing r.1 t v he with ⟨ht0,_⟩ | ⟨_,hv⟩
  · exact False.elim ((ht0 ▸ ht.1).not_gt K.last_parameter_pos)
  · exact hv
end ExteriorCrossingCut
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.ExteriorCrossingCut
variable  {D D' : Paper170.AdmissibleDrawing graph}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {r : C.InnerIndex}
theorem first_parameter_point (K : ExteriorCrossingCut C P r) :
    D'.edge r.1 ((P r.1).knot K.first)=C.portPoint (C.incomingPort r) :=
  ((drawingEdgeWalk_getVert P r.1 K.first.val (by have h := K.first.isLt; omega)).trans
    ((P r.1).vertices_at K.first)).symm.trans K.first_point
theorem last_parameter_point (K : ExteriorCrossingCut C P r) :
    D'.edge r.1 ((P r.1).knot K.last)=C.portPoint (C.outgoingPort r) :=
  ((drawingEdgeWalk_getVert P r.1 K.last.val (by have h := K.last.isLt; omega)).trans
    ((P r.1).vertices_at K.last)).symm.trans K.last_point
theorem prefix_subset_edge (K : ExteriorCrossingCut C P r) :
    Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take K.first.val)) ⊆ Set.range (D'.edge r.1) := by
  intro x hx
  obtain ⟨t,_,he⟩ := drawingEdgeWalk_take_trace P r.1 K.first hx
  exact ⟨t,he⟩
theorem suffix_subset_edge (K : ExteriorCrossingCut C P r) :
    Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop K.last.val)) ⊆ Set.range (D'.edge r.1) := by
  intro x hx
  obtain ⟨t,_,he⟩ := drawingEdgeWalk_drop_trace P r.1 K.last hx
  exact ⟨t,he⟩
theorem incoming_not_suffix (K : ExteriorCrossingCut C P r) :
    C.portPoint (C.incomingPort r) ∉ Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop K.last.val)) := by
  intro hx
  obtain ⟨t,ht,he⟩ := drawingEdgeWalk_drop_trace P r.1 K.last hx
  have heq := D'.edge_injective r.1 (he.trans K.first_parameter_point.symm)
  exact ((P r.1).increasing K.ordered).not_ge (heq ▸ ht.1)
theorem outgoing_not_prefix (K : ExteriorCrossingCut C P r) :
    C.portPoint (C.outgoingPort r) ∉ Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take K.first.val)) := by
  intro hx
  obtain ⟨t,ht,he⟩ := drawingEdgeWalk_take_trace P r.1 K.first hx
  have heq := D'.edge_injective r.1 (he.trans K.last_parameter_point.symm)
  exact ((P r.1).increasing K.ordered).not_ge (heq ▸ ht.2)
theorem prefix_suffix_disjoint (K : ExteriorCrossingCut C P r) :
    Disjoint (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).take K.first.val)))
      (Set.range (graphWalkPath id ((drawingEdgeWalk P r.1).drop K.last.val))) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  obtain ⟨t,ht,he⟩ := drawingEdgeWalk_take_trace P r.1 K.first hx
  obtain ⟨u,hu,hf⟩ := drawingEdgeWalk_drop_trace P r.1 K.last hy
  have heq := D'.edge_injective r.1 (he.trans hf.symm)
  exact ((P r.1).increasing K.ordered).not_ge (hu.1.trans (heq ▸ ht.2))
end Paper170Geometry.ExteriorCrossingCut
end
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}
theorem surgery_forward_adj : (crossingSurgeryGraph C P p q).Adj
    (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort q)) :=
  crossingSurgeryGraph_reconnection_adj C P p q true
theorem surgery_backward_adj : (crossingSurgeryGraph C P p q).Adj
    (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort p)) :=
  crossingSurgeryGraph_reconnection_adj C P p q false
def reconnectedForwardWalk (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) :
    (crossingSurgeryGraph C P p q).Walk (D'.vertex ((graph.src p.1))) (D'.vertex ((graph.dst q.1))) :=
  walkThroughChord (Kp.prefixInSurgery p q rfl)
    surgery_forward_adj (Kq.suffixInSurgery p q hm.symm)
def reconnectedBackwardWalk (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) :
    (crossingSurgeryGraph C P p q).Walk (D'.vertex ((graph.src q.1))) (D'.vertex ((graph.dst p.1))) :=
  walkThroughChord (Kq.prefixInSurgery p q hm.symm)
    surgery_backward_adj (Kp.suffixInSurgery p q rfl)
theorem reconnectedForwardWalk_trace (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) :
    Set.range (graphWalkPath id (reconnectedForwardWalk Kp Kq hm))=
      (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).take Kp.first.val)) ∪
        segment ℝ (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort q))) ∪
      Set.range (graphWalkPath id ((drawingEdgeWalk P q.1).drop Kq.last.val)) := by
  rw [reconnectedForwardWalk,walkThroughChord_range,
    ExteriorCrossingCut.prefixInSurgery_trace,ExteriorCrossingCut.suffixInSurgery_trace]
theorem reconnectedBackwardWalk_trace (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) :
    Set.range (graphWalkPath id (reconnectedBackwardWalk Kp Kq hm))=
      (Set.range (graphWalkPath id ((drawingEdgeWalk P q.1).take Kq.first.val)) ∪
        segment ℝ (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort p))) ∪
      Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).drop Kp.last.val)) := by
  rw [reconnectedBackwardWalk,walkThroughChord_range,
    ExteriorCrossingCut.prefixInSurgery_trace,ExteriorCrossingCut.suffixInSurgery_trace]
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}
def reconnectedForwardPath (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) : Path (D'.vertex ((graph.src p.1))) (D'.vertex ((graph.dst q.1))) := by
  classical
  exact graphWalkPath id (reconnectedForwardWalk Kp Kq hm).bypass
def reconnectedBackwardPath (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) : Path (D'.vertex ((graph.src q.1))) (D'.vertex ((graph.dst p.1))) := by
  classical
  exact graphWalkPath id (reconnectedBackwardWalk Kp Kq hm).bypass
theorem reconnectedForwardPath_injective (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q)
    (hadj : graph.src p.1 = graph.src q.1 ∨ graph.dst p.1 = graph.dst q.1)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    Function.Injective (reconnectedForwardPath Kp Kq hm) := by
  classical
  exact graphWalkPath_injective id hemb (surgery_mixed_endpoints_ne C p q hadj)
    _ (reconnectedForwardWalk Kp Kq hm).bypass_isPath
theorem reconnectedBackwardPath_injective (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q)
    (hadj : graph.src p.1 = graph.src q.1 ∨ graph.dst p.1 = graph.dst q.1)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    Function.Injective (reconnectedBackwardPath Kp Kq hm) := by
  classical
  exact graphWalkPath_injective id hemb (surgery_mixed_endpoints_ne C q p (hadj.imp Eq.symm Eq.symm))
    _ (reconnectedBackwardWalk Kp Kq hm).bypass_isPath
theorem reconnectedForwardPath_trace (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) :
    Set.range (reconnectedForwardPath Kp Kq hm) ⊆
      (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).take Kp.first.val)) ∪
        segment ℝ (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort q))) ∪
      Set.range (graphWalkPath id ((drawingEdgeWalk P q.1).drop Kq.last.val)) := by
  classical
  exact (graphWalkPath_bypass_range_subset id (reconnectedForwardWalk Kp Kq hm)).trans
    (by rw [reconnectedForwardWalk_trace])
theorem reconnectedBackwardPath_trace (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) :
    Set.range (reconnectedBackwardPath Kp Kq hm) ⊆
      (Set.range (graphWalkPath id ((drawingEdgeWalk P q.1).take Kq.first.val)) ∪
        segment ℝ (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort p))) ∪
      Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).drop Kp.last.val)) := by
  classical
  exact (graphWalkPath_bypass_range_subset id (reconnectedBackwardWalk Kp Kq hm)).trans
    (by rw [reconnectedBackwardWalk_trace])
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}
theorem reconnected_paths_avoid_crossing (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hpq : p ≠ q) (x : Plane)
    (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    x ∉ Set.range (reconnectedForwardPath Kp Kq hm) ∧
      x ∉ Set.range (reconnectedBackwardPath Kp Kq hm) := by
  obtain ⟨hxin,havoid⟩ := C.reconnection_avoids_chord_meeting p q hpq x hxp hxq
  have hxinq : x ∈ C.crossingDisk q := by
    simpa only [DrawingPassages.crossingDisk,hm] using hxin
  constructor
  · intro hx
    rcases reconnectedForwardPath_trace Kp Kq hm hx with (hx | hx) | hx
    · exact Set.disjoint_left.mp Kp.prefix_outside hx hxin
    · exact havoid true hx
    · exact Set.disjoint_left.mp Kq.suffix_outside hx hxinq
  · intro hx
    rcases reconnectedBackwardPath_trace Kp Kq hm hx with (hx | hx) | hx
    · exact Set.disjoint_left.mp Kq.prefix_outside hx hxinq
    · exact havoid false hx
    · exact Set.disjoint_left.mp Kp.suffix_outside hx hxin
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}
theorem path_interior_avoids_vertices_of_range {V : Type*} (vertex : V → Plane) (a b : V)
    (γ : Path (vertex a) (vertex b)) (hinj : Function.Injective γ)
    (hrange : ∀ v, vertex v ∈ Set.range γ → v=a ∨ v=b)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) (v : V) : γ t ≠ vertex v := by
  intro he
  rcases hrange v ⟨t,he⟩ with rfl | rfl
  · exact ht.1.ne (hinj (he.trans γ.source.symm)).symm
  · exact ht.2.ne (hinj (he.trans γ.target.symm))
theorem reconnectedForwardPath_vertex_eq (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (j : Vertex) (hj : D'.vertex j ∈ Set.range (reconnectedForwardPath Kp Kq hm)) :
    j=(graph.src p.1) ∨ j=(graph.dst q.1) := by
  rcases reconnectedForwardPath_trace Kp Kq hm hj with (hj | hj) | hj
  · exact Or.inl (Kp.prefix_vertex_eq j hj)
  · exact False.elim (C.reconnection_segment_avoids_vertices p q hm D'.vertex hv true j hj)
  · exact Or.inr (Kq.suffix_vertex_eq j hj)
theorem reconnectedBackwardPath_vertex_eq (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (j : Vertex) (hj : D'.vertex j ∈ Set.range (reconnectedBackwardPath Kp Kq hm)) :
    j=(graph.src q.1) ∨ j=(graph.dst p.1) := by
  rcases reconnectedBackwardPath_trace Kp Kq hm hj with (hj | hj) | hj
  · exact Or.inl (Kq.prefix_vertex_eq j hj)
  · exact False.elim (C.reconnection_segment_avoids_vertices p q hm D'.vertex hv false j hj)
  · exact Or.inr (Kp.suffix_vertex_eq j hj)
theorem reconnectedForwardPath_interior_avoids_vertices
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hadj : graph.src p.1 = graph.src q.1 ∨ graph.dst p.1 = graph.dst q.1)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) (j : Vertex) :
    reconnectedForwardPath Kp Kq hm t ≠ D'.vertex j :=
  path_interior_avoids_vertices_of_range D'.vertex _ _ _
    (reconnectedForwardPath_injective Kp Kq hm hadj hemb)
    (reconnectedForwardPath_vertex_eq Kp Kq hm hv) t ht j
theorem reconnectedBackwardPath_interior_avoids_vertices
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q)
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hadj : graph.src p.1 = graph.src q.1 ∨ graph.dst p.1 = graph.dst q.1)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) (j : Vertex) :
    reconnectedBackwardPath Kp Kq hm t ≠ D'.vertex j :=
  path_interior_avoids_vertices_of_range D'.vertex _ _ _
    (reconnectedBackwardPath_injective Kp Kq hm hadj hemb)
    (reconnectedBackwardPath_vertex_eq Kp Kq hm hv) t ht j
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170.ContinuousDrawing
def replaceTwoRoutes (D : Paper170.ContinuousDrawing graph) (e f : Edge)
    (γ : Path (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (δ : Path (D.vertex ((graph.src f))) (D.vertex ((graph.dst f))))
    (g : Edge) : Path (D.vertex ((graph.src g))) (D.vertex ((graph.dst g))) := by
  classical
  exact if h : g=e then γ.cast (congrArg (fun k : Edge => D.vertex ((graph.src k))) h)
    (congrArg (fun k : Edge => D.vertex ((graph.dst k))) h)
  else if h : g=f then δ.cast (congrArg (fun k : Edge => D.vertex ((graph.src k))) h)
    (congrArg (fun k : Edge => D.vertex ((graph.dst k))) h)
  else D.edge g
theorem replaceTwoRoutes_first (D : Paper170.ContinuousDrawing graph) (e f : Edge)
    (γ : Path (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (δ : Path (D.vertex ((graph.src f))) (D.vertex ((graph.dst f)))) :
    D.replaceTwoRoutes e f γ δ e=γ := by
  simp only [replaceTwoRoutes,dif_pos rfl,Path.cast_rfl_rfl]
theorem replaceTwoRoutes_second (D : Paper170.ContinuousDrawing graph) (e f : Edge) (hef : e ≠ f)
    (γ : Path (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (δ : Path (D.vertex ((graph.src f))) (D.vertex ((graph.dst f)))) :
    D.replaceTwoRoutes e f γ δ f=δ := by
  simp only [replaceTwoRoutes,dif_neg (Ne.symm hef),dif_pos rfl,Path.cast_rfl_rfl]
theorem replaceTwoRoutes_other (D : Paper170.ContinuousDrawing graph) (e f : Edge)
    (γ : Path (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (δ : Path (D.vertex ((graph.src f))) (D.vertex ((graph.dst f))))
    (g : Edge) (hge : g ≠ e) (hgf : g ≠ f) :
    D.replaceTwoRoutes e f γ δ g=D.edge g := by
  simp only [replaceTwoRoutes,dif_neg hge,dif_neg hgf]
def replaceTwoEdges (D : Paper170.ContinuousDrawing graph) (e f : Edge)
    (γ : Path (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (δ : Path (D.vertex ((graph.src f))) (D.vertex ((graph.dst f))))
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hvγ : ∀ t, t ∈ Set.Ioo (0 : unitInterval) 1 → ∀ j, γ t ≠ D.vertex j)
    (hvδ : ∀ t, t ∈ Set.Ioo (0 : unitInterval) 1 → ∀ j, δ t ≠ D.vertex j) :
    Paper170.ContinuousDrawing graph where
  vertex := D.vertex
  vertex_injective := D.vertex_injective
  edge := D.replaceTwoRoutes e f γ δ
  edge_injective := by
    intro g
    classical
    by_cases hge : g=e
    · subst g
      rw [replaceTwoRoutes_first]
      exact hγ
    by_cases hgf : g=f
    · subst g
      rw [replaceTwoRoutes_second _ _ _ (Ne.symm hge)]
      exact hδ
    · rw [replaceTwoRoutes_other _ _ _ _ _ _ hge hgf]
      exact D.edge_injective g
  interior_avoids_vertices := by
    intro g t ht j
    classical
    by_cases hge : g=e
    · subst g
      rw [replaceTwoRoutes_first]
      exact hvγ t ht j
    by_cases hgf : g=f
    · subst g
      rw [replaceTwoRoutes_second _ _ _ (Ne.symm hge)]
      exact hvδ t ht j
    · rw [replaceTwoRoutes_other _ _ _ _ _ _ hge hgf]
      exact D.interior_avoids_vertices g t ht j
end Paper170.ContinuousDrawing
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170.ContinuousDrawing
theorem replaceTwoRoutes_range_cases (D : Paper170.ContinuousDrawing graph) (e f : Edge)
    (γ : Path (D.vertex ((graph.src e))) (D.vertex ((graph.dst e))))
    (δ : Path (D.vertex ((graph.src f))) (D.vertex ((graph.dst f))))
    (g : Edge) (x : Plane) (hx : x ∈ Set.range (D.replaceTwoRoutes e f γ δ g)) :
    (g=e ∧ x ∈ Set.range γ) ∨ (g=f ∧ x ∈ Set.range δ) ∨
      (g ≠ e ∧ g ≠ f ∧ x ∈ Set.range (D.edge g)) := by
  classical
  by_cases hge : g=e
  · subst g
    exact Or.inl ⟨rfl,by simpa only [replaceTwoRoutes_first] using hx⟩
  by_cases hgf : g=f
  · subst g
    exact Or.inr (Or.inl ⟨rfl,by simpa only [replaceTwoRoutes_second D e f (Ne.symm hge)] using hx⟩)
  · exact Or.inr (Or.inr ⟨hge,hgf,by simpa only [replaceTwoRoutes_other D e f γ δ g hge hgf] using hx⟩)
end Paper170.ContinuousDrawing
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}
def adjacentSurgeryRouteP (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1)) :
    Path (D'.vertex ((graph.src p.1))) (D'.vertex ((graph.dst p.1))) := by
  classical
  exact if h : (graph.src p.1)=(graph.src q.1) then (reconnectedBackwardPath Kp Kq hm).cast
    (congrArg (fun i => D'.vertex (i)) h) rfl
  else (reconnectedForwardPath Kp Kq hm).cast rfl
    (congrArg (fun j => D'.vertex (j)) (hadj.resolve_left h))
def adjacentSurgeryRouteQ (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1)) :
    Path (D'.vertex ((graph.src q.1))) (D'.vertex ((graph.dst q.1))) := by
  classical
  exact if h : (graph.src p.1)=(graph.src q.1) then (reconnectedForwardPath Kp Kq hm).cast
    (congrArg (fun i => D'.vertex (i)) h.symm) rfl
  else (reconnectedBackwardPath Kp Kq hm).cast rfl
    (congrArg (fun j => D'.vertex (j)) (hadj.resolve_left h).symm)
theorem adjacentSurgeryRouteP_injective (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    Function.Injective (adjacentSurgeryRouteP Kp Kq hm hadj) := by
  unfold adjacentSurgeryRouteP
  split
  · exact reconnectedBackwardPath_injective Kp Kq hm hadj hemb
  · exact reconnectedForwardPath_injective Kp Kq hm hadj hemb
theorem adjacentSurgeryRouteQ_injective (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    Function.Injective (adjacentSurgeryRouteQ Kp Kq hm hadj) := by
  unfold adjacentSurgeryRouteQ
  split
  · exact reconnectedForwardPath_injective Kp Kq hm hadj hemb
  · exact reconnectedBackwardPath_injective Kp Kq hm hadj hemb
theorem adjacentSurgeryRouteP_avoids_vertices
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) (j : Vertex) :
    adjacentSurgeryRouteP Kp Kq hm hadj t ≠ D'.vertex j := by
  unfold adjacentSurgeryRouteP
  split
  · exact reconnectedBackwardPath_interior_avoids_vertices Kp Kq hm hv hadj hemb t ht j
  · exact reconnectedForwardPath_interior_avoids_vertices Kp Kq hm hv hadj hemb t ht j
theorem adjacentSurgeryRouteQ_avoids_vertices
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (t : unitInterval) (ht : t ∈ Set.Ioo (0 : unitInterval) 1) (j : Vertex) :
    adjacentSurgeryRouteQ Kp Kq hm hadj t ≠ D'.vertex j := by
  unfold adjacentSurgeryRouteQ
  split
  · exact reconnectedForwardPath_interior_avoids_vertices Kp Kq hm hv hadj hemb t ht j
  · exact reconnectedBackwardPath_interior_avoids_vertices Kp Kq hm hv hadj hemb t ht j
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}
def adjacentSurgeryDrawing (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) : Paper170.ContinuousDrawing graph :=
  D'.toContinuousDrawing.replaceTwoEdges p.1 q.1
    (adjacentSurgeryRouteP Kp Kq hm hadj) (adjacentSurgeryRouteQ Kp Kq hm hadj)
    (adjacentSurgeryRouteP_injective Kp Kq hm hadj hemb)
    (adjacentSurgeryRouteQ_injective Kp Kq hm hadj hemb)
    (adjacentSurgeryRouteP_avoids_vertices Kp Kq hm hadj hv hemb)
    (adjacentSurgeryRouteQ_avoids_vertices Kp Kq hm hadj hv hemb)
theorem adjacentSurgeryDrawing_first (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb).edge p.1=adjacentSurgeryRouteP Kp Kq hm hadj :=
  Paper170.ContinuousDrawing.replaceTwoRoutes_first _ _ _ _ _
theorem adjacentSurgeryDrawing_second (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hpq : p ≠ q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb).edge q.1=adjacentSurgeryRouteQ Kp Kq hm hadj :=
  Paper170.ContinuousDrawing.replaceTwoRoutes_second _ _ _ (fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hm)) _ _
theorem adjacentSurgeryDrawing_other (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (e : Edge) (hep : e ≠ p.1) (heq : e ≠ q.1) :
    (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb).edge e=D'.edge e :=
  Paper170.ContinuousDrawing.replaceTwoRoutes_other _ _ _ _ _ _ hep heq
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
variable  {D D' : Paper170.AdmissibleDrawing graph}
  {C : DrawingPassages D.toFiniteIntersectionDrawing} {P : ∀ e, PolygonalParametrization (D'.edge e)}
  {p q : C.InnerIndex}
theorem adjacentSurgeryRoutes_avoid_crossing
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hpq : p ≠ q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    x ∉ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj) ∧
      x ∉ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj) := by
  have ha := reconnected_paths_avoid_crossing Kp Kq hm hpq x hxp hxq
  constructor
  · unfold adjacentSurgeryRouteP
    split
    · exact ha.2
    · exact ha.1
  · unfold adjacentSurgeryRouteQ
    split
    · exact ha.1
    · exact ha.2
theorem adjacentSurgeryDrawing_avoids_crossing
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hm : C.innerMark p=C.innerMark q) (hpq : p ≠ q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hv : ∀ j, squaredLength (D'.vertex j-D.vertex j) < C.radius^2)
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q))
    (hother : ∀ e, e ≠ p.1 → e ≠ q.1 → x ∉ Set.range (D'.edge e)) :
    ∀ e, x ∉ Set.range ((adjacentSurgeryDrawing Kp Kq hm hadj hv hemb).edge e) := by
  have ha := adjacentSurgeryRoutes_avoid_crossing Kp Kq hm hpq hadj x hxp hxq
  intro e
  classical
  by_cases hep : e=p.1
  · subst e
    rw [adjacentSurgeryDrawing_first]
    exact ha.1
  by_cases heq : e=q.1
  · subst e
    rw [adjacentSurgeryDrawing_second Kp Kq hm hpq]
    exact ha.2
  · rw [adjacentSurgeryDrawing_other Kp Kq hm hadj hv hemb e hep heq]
    exact hother e hep heq
end Paper170Geometry
end
end
section
noncomputable section
namespace Paper170Geometry.PolygonalExterior
end Paper170Geometry.PolygonalExterior
end
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry
theorem segment_disjoint_of_open_containment (a b : Plane) (U S : Set Plane)
    (hin : openSegmentTrace a b ⊆ U) (hout : Disjoint S U)
    (ha : a ∉ S) (hb : b ∉ S) : Disjoint (segment ℝ a b) S := by
  apply Set.disjoint_left.mpr
  intro x hx hs
  rcases segment_endpoint_or_open a b x hx with rfl | rfl | hx
  · exact ha hs
  · exact hb hs
  · exact Set.disjoint_left.mp hout hs (hin hx)
namespace PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
theorem assembled_port_not_mem_other_edge (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (e : Edge) (r : C.Port) (her : e ≠ r.1.1) :
    C.portPoint r ∉ Set.range (E.assembledEdge v e) :=
  fun hx => her (E.assembled_port_unique_edge v hv e r hx)
theorem reconnection_other_edge_disjoint (E : PolygonalExterior C)
    (v : Vertex → Plane) (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (p q : C.InnerIndex) (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (i : Bool) (e : Edge) (hep : e ≠ p.1) (heq : e ≠ q.1) :
    Disjoint (segment ℝ (C.reconnectionStart p q i) (C.reconnectionEnd p q i))
      (Set.range (E.assembledEdge v e)) := by
  apply segment_disjoint_of_open_containment _ _ (C.crossingDisk p) _
    (C.reconnection_open_in_disk p q hm i)
    (E.assembled_other_edge_avoids_crossingDisk v hv p q hpq hm e hep heq)
  · cases i
    · exact E.assembled_port_not_mem_other_edge v hv e (C.incomingPort q) heq
    · exact E.assembled_port_not_mem_other_edge v hv e (C.incomingPort p) hep
  · cases i
    · exact E.assembled_port_not_mem_other_edge v hv e (C.outgoingPort p) hep
    · exact E.assembled_port_not_mem_other_edge v hv e (C.outgoingPort q) heq
end PolygonalExterior
end Paper170Geometry
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : Vertex → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
  {p q : C.InnerIndex}
theorem forward_chord_disjoint_opposite_prefix
    (Kq : ExteriorCrossingCut C P q) (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) :
    Disjoint (segment ℝ (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort q)))
      (Set.range (graphWalkPath id ((drawingEdgeWalk P q.1).take Kq.first.val))) := by
  have hqp : q.1 ≠ p.1 := fun he => hpq (C.innerIndex_eq_of_edge_mark p q he.symm hm)
  apply segment_disjoint_of_open_containment _ _ (C.crossingDisk p) _ (C.reconnection_open_in_disk p q hm true)
  · simpa only [DrawingPassages.crossingDisk,hm] using Kq.prefix_outside
  · intro hx
    exact E.assembled_port_not_mem_other_edge v hv q.1 (C.incomingPort p) hqp (Kq.prefix_subset_edge hx)
  · exact Kq.outgoing_not_prefix
theorem forward_chord_disjoint_opposite_suffix
    (Kp : ExteriorCrossingCut C P p) (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) :
    Disjoint (segment ℝ (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort q)))
      (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).drop Kp.last.val))) := by
  have hpqe : p.1 ≠ q.1 := fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hm)
  apply segment_disjoint_of_open_containment _ _ (C.crossingDisk p) _
    (C.reconnection_open_in_disk p q hm true) Kp.suffix_outside
  · exact Kp.incoming_not_suffix
  · intro hx
    exact E.assembled_port_not_mem_other_edge v hv p.1 (C.outgoingPort q) hpqe (Kp.suffix_subset_edge hx)
theorem backward_chord_disjoint_opposite_prefix
    (Kp : ExteriorCrossingCut C P p) (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) :
    Disjoint (segment ℝ (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort p)))
      (Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).take Kp.first.val))) := by
  have hpqe : p.1 ≠ q.1 := fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hm)
  apply segment_disjoint_of_open_containment _ _ (C.crossingDisk p) _
    (C.reconnection_open_in_disk p q hm false) Kp.prefix_outside
  · intro hx
    exact E.assembled_port_not_mem_other_edge v hv p.1 (C.incomingPort q) hpqe (Kp.prefix_subset_edge hx)
  · exact Kp.outgoing_not_prefix
theorem backward_chord_disjoint_opposite_suffix
    (Kq : ExteriorCrossingCut C P q) (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) :
    Disjoint (segment ℝ (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort p)))
      (Set.range (graphWalkPath id ((drawingEdgeWalk P q.1).drop Kq.last.val))) := by
  have hqp : q.1 ≠ p.1 := fun he => hpq (C.innerIndex_eq_of_edge_mark p q he.symm hm)
  apply segment_disjoint_of_open_containment _ _ (C.crossingDisk p) _ (C.reconnection_open_in_disk p q hm false)
  · simpa only [DrawingPassages.crossingDisk,hm] using Kq.suffix_outside
  · exact Kq.incoming_not_suffix
  · intro hx
    exact E.assembled_port_not_mem_other_edge v hv q.1 (C.outgoingPort p) hqp (Kq.suffix_subset_edge hx)
end Paper170Geometry.PolygonalExterior
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : Vertex → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
  {p q : C.InnerIndex}
theorem reconnected_paths_meeting_cases
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)))
    (x : Plane) (hx : x ∈ Set.range (reconnectedForwardPath Kp Kq hm))
    (hy : x ∈ Set.range (reconnectedBackwardPath Kp Kq hm)) :
    (x ∈ Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).take Kp.first.val)) ∧
      x ∈ Set.range (graphWalkPath id ((drawingEdgeWalk P q.1).take Kq.first.val))) ∨
    (x ∈ Set.range (graphWalkPath id ((drawingEdgeWalk P p.1).drop Kp.last.val)) ∧
      x ∈ Set.range (graphWalkPath id ((drawingEdgeWalk P q.1).drop Kq.last.val))) := by
  have hFP := E.forward_chord_disjoint_opposite_prefix v hvinj hv hdet P Kq hpq hm
  have hFS := E.forward_chord_disjoint_opposite_suffix v hvinj hv hdet P Kp hpq hm
  have hBP := E.backward_chord_disjoint_opposite_prefix v hvinj hv hdet P Kp hpq hm
  have hBS := E.backward_chord_disjoint_opposite_suffix v hvinj hv hdet P Kq hpq hm
  have hchord := C.reconnection_chords_disjoint p q hcross true false (by decide)
  rcases reconnectedForwardPath_trace Kp Kq hm hx with (hx | hx) | hx
  · rcases reconnectedBackwardPath_trace Kp Kq hm hy with (hy | hy) | hy
    · exact Or.inl ⟨hx,hy⟩
    · exact False.elim (Set.disjoint_left.mp hBP hy hx)
    · exact False.elim (Set.disjoint_left.mp Kp.prefix_suffix_disjoint hx hy)
  · rcases reconnectedBackwardPath_trace Kp Kq hm hy with (hy | hy) | hy
    · exact False.elim (Set.disjoint_left.mp hFP hx hy)
    · exact False.elim (Set.disjoint_left.mp hchord hx hy)
    · exact False.elim (Set.disjoint_left.mp hFS hx hy)
  · rcases reconnectedBackwardPath_trace Kp Kq hm hy with (hy | hy) | hy
    · exact False.elim (Set.disjoint_left.mp Kq.prefix_suffix_disjoint hy hx)
    · exact False.elim (Set.disjoint_left.mp hBS hy hx)
    · exact Or.inr ⟨hy,hx⟩
theorem reconnected_paths_meeting_old_edges
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)))
    (x : Plane) (hx : x ∈ Set.range (reconnectedForwardPath Kp Kq hm))
    (hy : x ∈ Set.range (reconnectedBackwardPath Kp Kq hm)) :
    x ∈ Set.range (E.assembledEdge v p.1) ∧ x ∈ Set.range (E.assembledEdge v q.1) := by
  rcases E.reconnected_paths_meeting_cases v hvinj hv hdet P Kp Kq hpq hm hcross x hx hy with h | h
  · exact ⟨Kp.prefix_subset_edge h.1,Kq.prefix_subset_edge h.2⟩
  · exact ⟨Kp.suffix_subset_edge h.1,Kq.suffix_subset_edge h.2⟩
end Paper170Geometry.PolygonalExterior
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : Vertex → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
  {p q : C.InnerIndex}
theorem reconnectedForwardPath_meeting_other
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (e : Edge) (hep : e ≠ p.1) (heq : e ≠ q.1)
    (x : Plane) (hx : x ∈ Set.range (reconnectedForwardPath Kp Kq hm))
    (hy : x ∈ Set.range (E.assembledEdge v e)) :
    x ∈ Set.range (E.assembledEdge v p.1) ∨ x ∈ Set.range (E.assembledEdge v q.1) := by
  rcases reconnectedForwardPath_trace Kp Kq hm hx with (hx | hx) | hx
  · exact Or.inl (Kp.prefix_subset_edge hx)
  · exact False.elim (Set.disjoint_left.mp (E.reconnection_other_edge_disjoint v hv p q hpq hm true e hep heq) hx hy)
  · exact Or.inr (Kq.suffix_subset_edge hx)
theorem reconnectedBackwardPath_meeting_other
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q)
    (e : Edge) (hep : e ≠ p.1) (heq : e ≠ q.1)
    (x : Plane) (hx : x ∈ Set.range (reconnectedBackwardPath Kp Kq hm))
    (hy : x ∈ Set.range (E.assembledEdge v e)) :
    x ∈ Set.range (E.assembledEdge v p.1) ∨ x ∈ Set.range (E.assembledEdge v q.1) := by
  rcases reconnectedBackwardPath_trace Kp Kq hm hx with (hx | hx) | hx
  · exact Or.inr (Kq.prefix_subset_edge hx)
  · exact False.elim (Set.disjoint_left.mp (E.reconnection_other_edge_disjoint v hv p q hpq hm false e hep heq) hx hy)
  · exact Or.inl (Kp.suffix_subset_edge hx)
theorem adjacentSurgeryRoutes_meeting_other
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (e : Edge) (hep : e ≠ p.1) (heq : e ≠ q.1)
    (x : Plane) (hx : x ∈ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj) ∨
      x ∈ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj))
    (hy : x ∈ Set.range (E.assembledEdge v e)) :
    x ∈ Set.range (E.assembledEdge v p.1) ∨ x ∈ Set.range (E.assembledEdge v q.1) := by
  have hf := E.reconnectedForwardPath_meeting_other v hvinj hv hdet P Kp Kq hpq hm e hep heq x
  have hb := E.reconnectedBackwardPath_meeting_other v hvinj hv hdet P Kp Kq hpq hm e hep heq x
  rcases hx with hx | hx
  · unfold adjacentSurgeryRouteP at hx
    split at hx
    · exact hb hx hy
    · exact hf hx hy
  · unfold adjacentSurgeryRouteQ at hx
    split at hx
    · exact hf hx hy
    · exact hb hx hy
theorem adjacentSurgeryRoutes_meeting_each_other
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)))
    (x : Plane) (hx : x ∈ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj))
    (hy : x ∈ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj)) :
    x ∈ Set.range (E.assembledEdge v p.1) ∧ x ∈ Set.range (E.assembledEdge v q.1) := by
  have hh := E.reconnected_paths_meeting_old_edges v hvinj hv hdet P Kp Kq hpq hm hcross x
  by_cases h : (graph.src p.1)=(graph.src q.1)
  · simp only [adjacentSurgeryRouteP,adjacentSurgeryRouteQ,dif_pos h] at hx hy
    exact hh hy hx
  · simp only [adjacentSurgeryRouteP,adjacentSurgeryRouteQ,dif_neg h] at hx hy
    exact hh hx hy
end Paper170Geometry.PolygonalExterior
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : Vertex → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
  {p q : C.InnerIndex}
theorem adjacentSurgeryDrawing_crossings_subset
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)))
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id) :
    Paper170.crossingPoints (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb) ⊆
      Paper170.crossingPoints (E.assembledAdmissible v hvinj hv hdet).toContinuousDrawing := by
  let B := (E.assembledAdmissible v hvinj hv hdet).toContinuousDrawing
  let A := adjacentSurgeryDrawing Kp Kq hm hadj hv hemb
  intro x hx
  obtain ⟨e,f,hef,hxe,hxf⟩ := hx
  have havoid : ∀ j, x ≠ B.vertex j := edgeInterior_not_vertex A e x hxe
  have hpair (hx : x ∈ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj))
      (hy : x ∈ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj)) : x ∈ Paper170.crossingPoints B := by
    have hh := E.adjacentSurgeryRoutes_meeting_each_other v hvinj hv hdet P Kp Kq hpq hm hadj hcross x hx hy
    exact crossing_of_ranges_not_vertices B p.1 q.1
      (fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hm)) x hh.1 hh.2 havoid
  have hmixed (g : Edge) (hgp : g ≠ p.1) (hgq : g ≠ q.1)
      (hx : x ∈ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj) ∨
        x ∈ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj))
      (hy : x ∈ Set.range (B.edge g)) : x ∈ Paper170.crossingPoints B := by
    rcases E.adjacentSurgeryRoutes_meeting_other v hvinj hv hdet P Kp Kq hpq hm hadj g hgp hgq x hx hy with h | h
    · exact crossing_of_ranges_not_vertices B p.1 g (Ne.symm hgp) x h hy havoid
    · exact crossing_of_ranges_not_vertices B q.1 g (Ne.symm hgq) x h hy havoid
  have hcases (g : Edge) (hg : x ∈ Set.range (A.edge g)) :=
    B.replaceTwoRoutes_range_cases p.1 q.1 (adjacentSurgeryRouteP Kp Kq hm hadj)
      (adjacentSurgeryRouteQ Kp Kq hm hadj) g x hg
  rcases hcases e (edgeInterior_subset_range A e hxe) with ⟨hep,hx⟩ | ⟨heq,hx⟩ | ⟨hep,heq,hx⟩
  · rcases hcases f (edgeInterior_subset_range A f hxf) with ⟨hfp,hy⟩ | ⟨hfq,hy⟩ | ⟨hfp,hfq,hy⟩
    · exact False.elim (hef (hep.trans hfp.symm))
    · exact hpair hx hy
    · exact hmixed f hfp hfq (Or.inl hx) hy
  · rcases hcases f (edgeInterior_subset_range A f hxf) with ⟨hfp,hy⟩ | ⟨hfq,hy⟩ | ⟨hfp,hfq,hy⟩
    · exact hpair hy hx
    · exact False.elim (hef (heq.trans hfq.symm))
    · exact hmixed f hfp hfq (Or.inr hx) hy
  · rcases hcases f (edgeInterior_subset_range A f hxf) with ⟨hfp,hy⟩ | ⟨hfq,hy⟩ | ⟨hfp,hfq,hy⟩
    · exact hmixed e hep heq (Or.inl hy) hx
    · exact hmixed e hep heq (Or.inr hy) hx
    · exact crossing_of_ranges_not_vertices B e f hef x hx hy havoid
end Paper170Geometry.PolygonalExterior
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : Vertex → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  {p q : C.InnerIndex}
theorem crossingChord_meeting_is_assembled_crossing (hpq : p ≠ q) (x : Plane)
    (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    x ∈ Paper170.crossingPoints (E.assembledAdmissible v hvinj hv hdet).toContinuousDrawing := by
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  have hxin := (C.reconnection_avoids_chord_meeting p q hpq x hxp hxq).1
  have hxinq : x ∈ C.crossingDisk q := by
    simpa only [DrawingPassages.crossingDisk,hm] using hxin
  apply crossing_of_ranges_not_vertices (E.assembledAdmissible v hvinj hv hdet).toContinuousDrawing
    p.1 q.1 (fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hm)) x
    ((E.assembled_range_in_crossingDisk v hv p x hxin).mpr hxp)
    ((E.assembled_range_in_crossingDisk v hv q x hxinq).mpr hxq)
  intro j he
  exact Set.disjoint_left.mp (C.crossingDisk_disjoint_vertex_disk p j) hxin (he.symm ▸ (hv j).le)
theorem adjacentSurgeryDrawing_strict_crossing_ncard
    (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    (Paper170.crossingPoints (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb)).Finite ∧
      (Paper170.crossingPoints (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb)).ncard <
        (Paper170.crossingPoints (E.assembledAdmissible v hvinj hv hdet).toContinuousDrawing).ncard := by
  have hcross := C.crossingChord_meeting_segmentsCrossProperly p q hpq x hxp hxq
  have hsub := E.adjacentSurgeryDrawing_crossings_subset v hvinj hv hdet P Kp Kq hpq hm hadj hcross hemb
  have hfinite := (E.assembledAdmissible v hvinj hv hdet).crossings_finite
  have hremoved := adjacentSurgeryDrawing_avoids_crossing Kp Kq hm hpq hadj hv hemb x hxp hxq (by
    intro e hep heq hx
    exact Set.disjoint_left.mp (E.assembled_other_edge_avoids_crossingDisk v hv p q hpq hm e hep heq)
      hx (C.reconnection_avoids_chord_meeting p q hpq x hxp hxq).1)
  have hnot : x ∉ Paper170.crossingPoints (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb) := by
    rintro ⟨e,f,hef,hxe,hxf⟩
    exact hremoved e (edgeInterior_subset_range _ e hxe)
  refine ⟨hfinite.subset hsub,Set.ncard_lt_ncard ⟨hsub,?_⟩ hfinite⟩
  intro hrev
  exact hnot (hrev (E.crossingChord_meeting_is_assembled_crossing v hvinj hv hdet hpq x hxp hxq))
end Paper170Geometry.PolygonalExterior
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : Vertex → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
  {p q : C.InnerIndex}
theorem adjacentSurgeryDrawing_no_triples
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hcross : SegmentsCrossProperly (C.portPoint (C.incomingPort p)) (C.portPoint (C.outgoingPort p))
      (C.portPoint (C.incomingPort q)) (C.portPoint (C.outgoingPort q)))
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (e f g : Edge) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    Paper170.edgeInterior (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb) e ∩
      Paper170.edgeInterior (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb) f ∩
      Paper170.edgeInterior (adjacentSurgeryDrawing Kp Kq hm hadj hv hemb) g = ∅ := by
  let B := E.assembledAdmissible v hvinj hv hdet
  let A := adjacentSurgeryDrawing Kp Kq hm hadj hv hemb
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨⟨hxe,hxf⟩,hxg⟩ := hx
  have havoid : ∀ j, x ≠ B.vertex j := edgeInterior_not_vertex A e x hxe
  have hthree (a b c : Edge) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (ha : x ∈ Set.range (B.edge a)) (hb : x ∈ Set.range (B.edge b))
      (hc : x ∈ Set.range (B.edge c)) : False := by
    have hmem : x ∈ Paper170.edgeInterior B.toContinuousDrawing a ∩ Paper170.edgeInterior B.toContinuousDrawing b ∩
        Paper170.edgeInterior B.toContinuousDrawing c :=
      ⟨⟨edgeInterior_of_range_not_vertices _ a x ha havoid,
        edgeInterior_of_range_not_vertices _ b x hb havoid⟩,edgeInterior_of_range_not_vertices _ c x hc havoid⟩
    rw [B.no_triples a b c hab hac hbc] at hmem
    exact hmem
  have htwo (a : Edge) (hap : a ≠ p.1) (haq : a ≠ q.1)
      (hp : x ∈ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj))
      (hq : x ∈ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj))
      (ha : x ∈ Set.range (B.edge a)) : False := by
    have hh := E.adjacentSurgeryRoutes_meeting_each_other v hvinj hv hdet P Kp Kq hpq hm hadj hcross x hp hq
    exact hthree p.1 q.1 a (fun he => hpq (C.innerIndex_eq_of_edge_mark p q he hm))
      (Ne.symm hap) (Ne.symm haq) hh.1 hh.2 ha
  have hone (a b : Edge) (hab : a ≠ b)
      (hap : a ≠ p.1) (haq : a ≠ q.1) (hbp : b ≠ p.1) (hbq : b ≠ q.1)
      (hh : x ∈ Set.range (adjacentSurgeryRouteP Kp Kq hm hadj) ∨
        x ∈ Set.range (adjacentSurgeryRouteQ Kp Kq hm hadj))
      (ha : x ∈ Set.range (B.edge a)) (hb : x ∈ Set.range (B.edge b)) : False := by
    rcases E.adjacentSurgeryRoutes_meeting_other v hvinj hv hdet P Kp Kq hpq hm hadj a hap haq x hh ha with hp | hq
    · exact hthree p.1 a b (Ne.symm hap) (Ne.symm hbp) hab hp ha hb
    · exact hthree q.1 a b (Ne.symm haq) (Ne.symm hbq) hab hq ha hb
  have hcases (a : Edge) (ha : x ∈ Set.range (A.edge a)) :=
    B.toContinuousDrawing.replaceTwoRoutes_range_cases p.1 q.1 (adjacentSurgeryRouteP Kp Kq hm hadj)
      (adjacentSurgeryRouteQ Kp Kq hm hadj) a x ha
  have hec := hcases e (edgeInterior_subset_range A e hxe)
  have hfc := hcases f (edgeInterior_subset_range A f hxf)
  have hgc := hcases g (edgeInterior_subset_range A g hxg)
  rcases hec with ⟨hep,hx⟩ | ⟨heq,hx⟩ | ⟨hep,heq,hx⟩
  · rcases hfc with ⟨hfp,hy⟩ | ⟨hfq,hy⟩ | ⟨hfp,hfq,hy⟩
    · exact hef (hep.trans hfp.symm)
    · rcases hgc with ⟨hgp,hz⟩ | ⟨hgq,hz⟩ | ⟨hgp,hgq,hz⟩
      · exact heg (hep.trans hgp.symm)
      · exact hfg (hfq.trans hgq.symm)
      · exact htwo g hgp hgq hx hy hz
    · rcases hgc with ⟨hgp,hz⟩ | ⟨hgq,hz⟩ | ⟨hgp,hgq,hz⟩
      · exact heg (hep.trans hgp.symm)
      · exact htwo f hfp hfq hx hz hy
      · exact hone f g hfg hfp hfq hgp hgq (Or.inl hx) hy hz
  · rcases hfc with ⟨hfp,hy⟩ | ⟨hfq,hy⟩ | ⟨hfp,hfq,hy⟩
    · rcases hgc with ⟨hgp,hz⟩ | ⟨hgq,hz⟩ | ⟨hgp,hgq,hz⟩
      · exact hfg (hfp.trans hgp.symm)
      · exact heg (heq.trans hgq.symm)
      · exact htwo g hgp hgq hy hx hz
    · exact hef (heq.trans hfq.symm)
    · rcases hgc with ⟨hgp,hz⟩ | ⟨hgq,hz⟩ | ⟨hgp,hgq,hz⟩
      · exact htwo f hfp hfq hz hx hy
      · exact heg (heq.trans hgq.symm)
      · exact hone f g hfg hfp hfq hgp hgq (Or.inr hx) hy hz
  · rcases hfc with ⟨hfp,hy⟩ | ⟨hfq,hy⟩ | ⟨hfp,hfq,hy⟩
    · rcases hgc with ⟨hgp,hz⟩ | ⟨hgq,hz⟩ | ⟨hgp,hgq,hz⟩
      · exact hfg (hfp.trans hgp.symm)
      · exact htwo e hep heq hy hz hx
      · exact hone e g heg hep heq hgp hgq (Or.inl hy) hx hz
    · rcases hgc with ⟨hgp,hz⟩ | ⟨hgq,hz⟩ | ⟨hgp,hgq,hz⟩
      · exact htwo e hep heq hz hy hx
      · exact hfg (hfq.trans hgq.symm)
      · exact hone e g heg hep heq hgp hgq (Or.inr hy) hx hz
    · rcases hgc with ⟨hgp,hz⟩ | ⟨hgq,hz⟩ | ⟨hgp,hgq,hz⟩
      · exact hone e f hef hep heq hfp hfq (Or.inl hz) hx hy
      · exact hone e f hef hep heq hfp hfq (Or.inr hz) hx hy
      · exact hthree e f g hef heg hfg hx hy hz
end Paper170Geometry.PolygonalExterior
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
  (E : PolygonalExterior C) (v : Vertex → Plane) (hvinj : Function.Injective v)
  (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
  (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
    det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
  (P : ∀ e, PolygonalParametrization ((E.assembledAdmissible v hvinj hv hdet).edge e))
  {p q : C.InnerIndex}
def adjacentSurgeryFiniteDrawing
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    FiniteIntersectionDrawing graph where
  toContinuousDrawing := adjacentSurgeryDrawing Kp Kq hm hadj hv hemb
  crossings_finite := (E.adjacentSurgeryDrawing_strict_crossing_ncard v hvinj hv hdet P Kp Kq hpq hm hadj hemb x hxp hxq).1
  no_triples := E.adjacentSurgeryDrawing_no_triples v hvinj hv hdet P Kp Kq hpq hm hadj
    (C.crossingChord_meeting_segmentsCrossProperly p q hpq x hxp hxq) hemb
theorem adjacentSurgeryFiniteDrawing_count_lt
    (Kp : ExteriorCrossingCut C P p) (Kq : ExteriorCrossingCut C P q)
    (hpq : p ≠ q) (hm : C.innerMark p=C.innerMark q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (hemb : StraightEdgeEmbedding (crossingSurgeryGraph C P p q) id)
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    finiteCrossingCount (E.adjacentSurgeryFiniteDrawing v hvinj hv hdet P Kp Kq hpq hm hadj hemb x hxp hxq) <
      Paper170.crossingCount (E.assembledAdmissible v hvinj hv hdet) := by
  rw [finiteCrossingCount_eq_ncard]
  have h := (E.adjacentSurgeryDrawing_strict_crossing_ncard v hvinj hv hdet P Kp Kq hpq hm hadj hemb x hxp hxq).2
  exact h.trans_eq (Set.ncard_eq_toFinset_card _ (E.assembledAdmissible v hvinj hv hdet).crossings_finite)
end Paper170Geometry.PolygonalExterior
end
end
section
noncomputable section
open Zarankiewicz
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
namespace Paper170Geometry.PolygonalExterior
variable  {D : Paper170.AdmissibleDrawing graph} {C : DrawingPassages D.toFiniteIntersectionDrawing}
theorem exists_admissible_adjacent_surgery [Fintype Vertex] [Fintype Edge] (E : PolygonalExterior C)
    (v : Vertex → Plane) (hvinj : Function.Injective v)
    (hv : ∀ j, squaredLength (v j-D.vertex j) < C.radius^2)
    (hdet : ∀ j (p q : C.PortsAt (C.vertexMark j)), p ≠ q →
      det2 (C.portPoint p.val-v j) (C.portPoint q.val-v j) ≠ 0)
    (p q : C.InnerIndex) (hpq : p ≠ q) (hadj : (graph.src p.1)=(graph.src q.1) ∨ (graph.dst p.1)=(graph.dst q.1))
    (x : Plane) (hxp : x ∈ Set.range (C.crossingChord p)) (hxq : x ∈ Set.range (C.crossingChord q)) :
    ∃ A : Paper170.AdmissibleDrawing graph, (∀ e, HasFiniteAffineCover (A.edge e)) ∧
      Paper170.crossingCount A < Paper170.crossingCount (E.assembledAdmissible v hvinj hv hdet) := by
  have hm := C.chord_meeting_marks_eq p q hxp hxq
  have hcross := C.crossingChord_meeting_segmentsCrossProperly p q hpq x hxp hxq
  obtain ⟨P,hmark,hport⟩ := E.exists_assembled_port_subdivision v hvinj hv hdet
  obtain ⟨Kp⟩ := E.nonempty_exteriorCrossingCut v hvinj hv hdet P hport p
  obtain ⟨Kq⟩ := E.nonempty_exteriorCrossingCut v hvinj hv hdet P hport q
  have hemb := crossingSurgeryGraph_embedding C P hmark hport p q hm hcross
  let B := E.adjacentSurgeryFiniteDrawing v hvinj hv hdet P Kp Kq hpq hm hadj hemb x hxp hxq
  obtain ⟨A,hpoly,hcount⟩ := finite_intersection_normalization B
  exact ⟨A,hpoly,hcount.trans_lt
    (E.adjacentSurgeryFiniteDrawing_count_lt v hvinj hv hdet P Kp Kq hpq hm hadj hemb x hxp hxq)⟩
end Paper170Geometry.PolygonalExterior
end
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
namespace Zarankiewicz
end Zarankiewicz
end OAI
end
section
namespace OAI
section
noncomputable section
open Zarankiewicz
namespace Paper170Geometry
variable {Vertex Edge : Type} {graph : Paper170.Graph Vertex Edge}
structure NoAdjacentCrossings (D : Paper170.AdmissibleDrawing graph) : Prop where
  eq_empty : ∀ e f : Edge, e≠f →
    (graph.src e=graph.src f ∨ graph.src e=graph.dst f ∨
      graph.dst e=graph.src f ∨ graph.dst e=graph.dst f) →
    Paper170.edgeInterior D.toContinuousDrawing e ∩
      Paper170.edgeInterior D.toContinuousDrawing f = ∅
end Paper170Geometry
end
end
section
noncomputable section
namespace Paper170Geometry
end Paper170Geometry
end
end
section
noncomputable section
namespace Paper170Geometry
end Paper170Geometry
end
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
end Zarankiewicz
end
end OAI
end
section
namespace OAI
section
noncomputable section
namespace Paper170Geometry
end Paper170Geometry
end
end
section
noncomputable section
namespace Paper170Geometry
end Paper170Geometry
end
end
section
noncomputable section
namespace Paper170Geometry
end Paper170Geometry
end
end
section
noncomputable section
namespace Paper170Geometry
end Paper170Geometry
end
end
section
noncomputable section
namespace Paper170Geometry
end Paper170Geometry
end
end
section
noncomputable section
namespace Paper170Geometry
end Paper170Geometry
end
end
section
noncomputable section
namespace Paper170Geometry
end Paper170Geometry
end
end
section
noncomputable section
namespace Paper170Geometry
end Paper170Geometry
end
end
section
noncomputable section
namespace Paper170Geometry
end Paper170Geometry
end
end
end OAI
end
section
namespace OAI
noncomputable section
namespace Zarankiewicz
namespace PolygonalExterior
end PolygonalExterior
end Zarankiewicz
end
end OAI
end
section
namespace OAI
section
noncomputable section
open Set
open scoped Classical
namespace Paper170
variable {V E : Type}
def Graph.reorient (G : Graph V E) (reverse : E → Bool) : Graph V E where
  src e := if reverse e = true then G.dst e else G.src e
  dst e := if reverse e = true then G.src e else G.dst e
  loopless e := by
    by_cases h : reverse e = true
    · simpa only [if_pos h] using (G.loopless e).symm
    · simpa only [if_neg h] using G.loopless e
  simple e f h := by
    apply G.simple e f
    by_cases he : reverse e = true <;> by_cases hf : reverse f = true <;>
      simp [he,hf] at h <;> tauto
theorem unitInterval_symm_mem_Ioo (t : unitInterval) :
    unitInterval.symm t ∈ Ioo (0 : unitInterval) 1 ↔ t ∈ Ioo (0 : unitInterval) 1 := by
  change (0 < 1-(t : ℝ) ∧ 1-(t : ℝ) < 1) ↔ (0 < (t : ℝ) ∧ (t : ℝ) < 1)
  constructor <;> rintro ⟨h0,h1⟩ <;> constructor <;> linarith
namespace ContinuousDrawing
variable {G : Graph V E}
def reorientedPath (D : ContinuousDrawing G) (reverse : E → Bool) (e : E) :
    Path (D.vertex ((G.reorient reverse).src e)) (D.vertex ((G.reorient reverse).dst e)) :=
  if h : reverse e = true then (D.edge e).symm.cast
    (by simp only [Graph.reorient,if_pos h]) (by simp only [Graph.reorient,if_pos h])
  else (D.edge e).cast
    (by simp only [Graph.reorient,if_neg h]) (by simp only [Graph.reorient,if_neg h])
theorem reorientedPath_apply (D : ContinuousDrawing G) (reverse : E → Bool) (e : E)
    (t : unitInterval) : D.reorientedPath reverse e t =
      if reverse e = true then D.edge e (unitInterval.symm t) else D.edge e t := by
  unfold reorientedPath
  split <;> rfl
def reorient (D : ContinuousDrawing G) (reverse : E → Bool) :
    ContinuousDrawing (G.reorient reverse) where
  vertex := D.vertex
  vertex_injective := D.vertex_injective
  edge := D.reorientedPath reverse
  edge_injective e := by
    intro s t hst
    rw [reorientedPath_apply,reorientedPath_apply] at hst
    by_cases h : reverse e = true
    · rw [if_pos h,if_pos h] at hst
      exact unitInterval.symm_bijective.1 (D.edge_injective e hst)
    · rw [if_neg h,if_neg h] at hst
      exact D.edge_injective e hst
  interior_avoids_vertices e t ht v := by
    rw [reorientedPath_apply]
    by_cases h : reverse e = true
    · rw [if_pos h]
      exact D.interior_avoids_vertices e _ ((unitInterval_symm_mem_Ioo t).mpr ht) v
    · rw [if_neg h]
      exact D.interior_avoids_vertices e t ht v
theorem reorient_edgeInterior (D : ContinuousDrawing G) (reverse : E → Bool) (e : E) :
    edgeInterior (D.reorient reverse) e = edgeInterior D e := by
  ext x
  by_cases h : reverse e = true
  · constructor
    · rintro ⟨t,ht,hx⟩
      refine ⟨unitInterval.symm t,(unitInterval_symm_mem_Ioo t).mpr ht,?_⟩
      change D.reorientedPath reverse e t = x at hx
      simpa only [reorientedPath_apply,if_pos h] using hx
    · rintro ⟨t,ht,hx⟩
      refine ⟨unitInterval.symm t,(unitInterval_symm_mem_Ioo t).mpr ht,?_⟩
      change D.reorientedPath reverse e (unitInterval.symm t) = x
      simpa only [reorientedPath_apply,if_pos h,unitInterval.symm_symm] using hx
  · constructor
    · rintro ⟨t,ht,hx⟩
      refine ⟨t,ht,?_⟩
      change D.reorientedPath reverse e t = x at hx
      simpa only [reorientedPath_apply,if_neg h] using hx
    · rintro ⟨t,ht,hx⟩
      refine ⟨t,ht,?_⟩
      change D.reorientedPath reverse e t = x
      simpa only [reorientedPath_apply,if_neg h] using hx
theorem reorient_crossingPoints (D : ContinuousDrawing G) (reverse : E → Bool) :
    crossingPoints (D.reorient reverse) = crossingPoints D := by
  ext x
  simp only [crossingPoints, mem_ofPred_eq, reorient_edgeInterior]
end ContinuousDrawing
namespace AdmissibleDrawing
variable {G : Graph V E}
def reorient (D : AdmissibleDrawing G) (reverse : E → Bool) :
    AdmissibleDrawing (G.reorient reverse) where
  toContinuousDrawing := D.toContinuousDrawing.reorient reverse
  crossings_finite := by
    rw [ContinuousDrawing.reorient_crossingPoints]
    exact D.crossings_finite
  crossings_proper e f hef x he hf := by
    rw [ContinuousDrawing.reorient_edgeInterior] at he hf
    rw [ContinuousDrawing.reorient_edgeInterior,ContinuousDrawing.reorient_edgeInterior]
    exact D.crossings_proper e f hef x he hf
  no_triples e f g hef heg hfg := by
    simp only [ContinuousDrawing.reorient_edgeInterior]
    exact D.no_triples e f g hef heg hfg
theorem reorient_crossingCount (D : AdmissibleDrawing G) (reverse : E → Bool) :
    crossingCount (D.reorient reverse) = crossingCount D := by
  unfold crossingCount
  congr 1
  ext x
  simp only [Set.Finite.mem_toFinset, reorient, ContinuousDrawing.reorient_crossingPoints]
end AdmissibleDrawing
end Paper170
end
end
section
noncomputable section
namespace Paper170
variable {V E : Type}
theorem Graph.eq_of_endpoints {G H : Graph V E} (hs : G.src = H.src)
    (ht : G.dst = H.dst) : G = H := by
  cases G
  cases H
  cases hs
  cases ht
  rfl
theorem Graph.reorient_reorient (G : Graph V E) (reverse : E → Bool) :
    (G.reorient reverse).reorient reverse = G := by
  apply Graph.eq_of_endpoints
  · funext e
    by_cases h : reverse e = true <;> simp [Graph.reorient,h]
  · funext e
    by_cases h : reverse e = true <;> simp [Graph.reorient,h]
namespace AdmissibleDrawing
variable {G H : Graph V E}
def castGraph (h : G = H) (D : AdmissibleDrawing G) : AdmissibleDrawing H := h ▸ D
theorem castGraph_crossingCount (h : G = H) (D : AdmissibleDrawing G) :
    crossingCount (D.castGraph h) = crossingCount D := by
  cases h
  rfl
theorem reorient_minimal (D : AdmissibleDrawing G) (reverse : E → Bool)
    (hmin : ∀ A : AdmissibleDrawing G, crossingCount D ≤ crossingCount A) :
    ∀ A : AdmissibleDrawing (G.reorient reverse),
      crossingCount (D.reorient reverse) ≤ crossingCount A := by
  intro A
  have h := hmin ((A.reorient reverse).castGraph (G.reorient_reorient reverse))
  simpa only [castGraph_crossingCount,reorient_crossingCount] using h
end AdmissibleDrawing
end Paper170
end
end
section
noncomputable section
namespace Paper170
end Paper170
end
end
section
noncomputable section
namespace Paper170Geometry
namespace PolygonalExterior
end PolygonalExterior
end Paper170Geometry
end
end
section
noncomputable section
namespace Paper170Geometry
open Zarankiewicz
open scoped Classical
variable {Vertex Edge : Type} [Fintype Vertex] [Fintype Edge]
  {graph : Paper170.Graph Vertex Edge}
theorem minimum_no_common_source_or_target (D : Paper170.AdmissibleDrawing graph)
    (hmin : ∀ A : Paper170.AdmissibleDrawing graph,
      Paper170.crossingCount D ≤ Paper170.crossingCount A)
    (e f : Edge) (hef : e ≠ f)
    (hadj : graph.src e = graph.src f ∨ graph.dst e = graph.dst f) :
    Paper170.edgeInterior D.toContinuousDrawing e ∩
      Paper170.edgeInterior D.toContinuousDrawing f = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hxe,hxf⟩
  obtain ⟨C⟩ := nonempty_drawingPassages D.toFiniteIntersectionDrawing
  obtain ⟨E⟩ := nonempty_polygonalExterior C
  obtain ⟨v,hvinj,hv,hne,hdet⟩ := C.exists_drawing_vertex_placement
  have hcount : Paper170.crossingCount (E.assembledAdmissible v hvinj hv hdet) =
      Paper170.crossingCount D :=
    le_antisymm (E.assembled_crossingCount_le v hvinj hv hdet) (hmin _)
  obtain ⟨y,hye,hyf⟩ := E.assembled_pair_retained_of_count_eq v hvinj hv hdet hcount e f hef x hxe hxf
  obtain ⟨p,q,hp,hq,hyp,hyq⟩ := E.assembled_meeting_chords v hv hdet e f hef y
    (edgeInterior_not_vertex (E.assembledDrawing v hvinj hv) e y hye)
    (edgeInterior_subset_range (E.assembledDrawing v hvinj hv) e hye)
    (edgeInterior_subset_range (E.assembledDrawing v hvinj hv) f hyf)
  have hpq : p ≠ q := fun h => hef (hp.symm.trans ((congrArg Sigma.fst h).trans hq))
  have hadj' : graph.src p.1 = graph.src q.1 ∨ graph.dst p.1 = graph.dst q.1 := by
    simpa only [hp,hq] using hadj
  obtain ⟨R,hRpoly,hRcount⟩ := E.exists_admissible_adjacent_surgery
    v hvinj hv hdet p q hpq hadj' y hyp hyq
  rw [hcount] at hRcount
  exact (not_lt_of_ge (hmin R)) hRcount
theorem minimum_no_adjacent (D : Paper170.AdmissibleDrawing graph)
    (hmin : ∀ A : Paper170.AdmissibleDrawing graph,
      Paper170.crossingCount D ≤ Paper170.crossingCount A) : NoAdjacentCrossings D := by
  constructor
  intro e f hef hadj
  obtain ⟨i,he,hf⟩ : ∃ i, (graph.src e = i ∨ graph.dst e = i) ∧
      (graph.src f = i ∨ graph.dst f = i) := by
    rcases hadj with h | h | h | h
    · exact ⟨graph.src e,Or.inl rfl,Or.inl h.symm⟩
    · exact ⟨graph.src e,Or.inl rfl,Or.inr h.symm⟩
    · exact ⟨graph.dst e,Or.inr rfl,Or.inl h.symm⟩
    · exact ⟨graph.dst e,Or.inr rfl,Or.inr h.symm⟩
  let reverse : Edge → Bool := fun a => decide (graph.dst a = i)
  have hsource (a : Edge) (ha : graph.src a = i ∨ graph.dst a = i) :
      (graph.reorient reverse).src a = i := by
    simp only [Paper170.Graph.reorient,reverse,decide_eq_true_eq]
    split
    · assumption
    · exact ha.resolve_right (by assumption)
  have h := minimum_no_common_source_or_target (D.reorient reverse)
    (D.reorient_minimal reverse hmin) e f hef
    (Or.inl ((hsource e he).trans (hsource f hf).symm))
  simpa only [Paper170.AdmissibleDrawing.reorient,
    Paper170.ContinuousDrawing.reorient_edgeInterior] using h
end Paper170Geometry
end
end
section
noncomputable section
namespace Paper170
end Paper170
end
end
end OAI
end
namespace AdjPort
open OAI OMA.S_arxiv_2009_03418
noncomputable section
def push {n} (D : AdmissibleDrawing (completeGraph n)) : Paper170.AdmissibleDrawing (Paper170.completeGraph n) where
  vertex := D.vertex
  vertex_injective := D.vertex_injective
  edge := D.edge
  edge_injective := D.edge_injective
  interior_avoids_vertices := D.interior_avoids_vertices
  crossings_finite := D.crossings_finite
  no_triples := D.no_triples
  crossings_proper e f h x he hf := ⟨(D.crossings_proper e f h x he hf).chart_exists⟩


def pull {n} (D : Paper170.AdmissibleDrawing (Paper170.completeGraph n)) : AdmissibleDrawing (completeGraph n) where
  vertex := D.vertex
  vertex_injective := D.vertex_injective
  edge := D.edge
  edge_injective := D.edge_injective
  interior_avoids_vertices := D.interior_avoids_vertices
  crossings_finite := D.crossings_finite
  no_triples := D.no_triples
  crossings_proper e f h x he hf := ⟨(D.crossings_proper e f h x he hf).chart_exists⟩


end
end AdjPort
theorem HillDeletionPort.leaf1 : HillDeletionPort.H1 := by
  intro n _ D
  obtain ⟨B,hB⟩ := OAI.Paper170Geometry.crossingCount_attainment (AdjPort.push D)
  have hmin (A : OAI.Paper170.AdmissibleDrawing (OAI.Paper170.completeGraph (n+1))) : OAI.Paper170.crossingCount B ≤ OAI.Paper170.crossingCount A := hB.trans_le (OAI.Paper170Geometry.ordinaryCrossingNumber_le_count A)
  refine ⟨AdjPort.pull B,hmin (AdjPort.push D),?_⟩
  intro e f hef hadj
  exact Set.disjoint_iff_inter_eq_empty.mpr ((OAI.Paper170Geometry.minimum_no_adjacent B hmin).eq_empty e f hef hadj)

/- Adapted from OpenAI openai/math@3344da59991ed94f9ba711217b29c1d760badfa6,
CompleteCrossing/Deletion. Apache-2.0. -/
namespace DeletionPort
open OMA.S_arxiv_2009_03418 Set
open scoped BigOperators Classical
noncomputable section
variable {V E : Type} {G : OMA.S_arxiv_2009_03418.Graph V E}
structure CleanDrawing (G : OMA.S_arxiv_2009_03418.Graph V E) extends AdmissibleDrawing G where
  no_adjacent : ∀ e f, e ≠ f →
    (G.src e = G.src f ∨ G.src e = G.dst f ∨ G.dst e = G.src f ∨ G.dst e = G.dst f) →
    Disjoint (edgeInterior toContinuousDrawing e) (edgeInterior toContinuousDrawing f)
theorem crossing_incident_iff (D : AdmissibleDrawing G) (x : Plane)
    (e f : E) (hef : e ≠ f)
    (he : x ∈ edgeInterior D.toContinuousDrawing e)
    (hf : x ∈ edgeInterior D.toContinuousDrawing f) (g : E) :
    x ∈ edgeInterior D.toContinuousDrawing g ↔ g = e ∨ g = f := by
  constructor
  · intro hg
    by_contra hh
    have hge : e ≠ g := by tauto
    have hgf : f ≠ g := by tauto
    have hmem : x ∈ edgeInterior D.toContinuousDrawing e ∩ edgeInterior D.toContinuousDrawing f ∩
        edgeInterior D.toContinuousDrawing g := ⟨⟨he,hf⟩,hg⟩
    rw [D.no_triples e f g hef hge hgf] at hmem
    exact hmem
  · rintro (rfl | rfl) <;> assumption

structure VertexDeletion {n : ℕ} (D : AdmissibleDrawing (completeGraph (n + 1)))
    (v : Fin (n + 1)) (A : AdmissibleDrawing (completeGraph n)) : Prop where
  vertex_eq : ∀ i, A.vertex i = D.vertex (v.succAbove i)
  edge_eq : ∀ (e : CompleteEdge n) (f : CompleteEdge (n + 1)),
    f.val.1 = v.succAbove e.val.1 → f.val.2 = v.succAbove e.val.2 →
    ∀ t, A.edge e t = D.edge f t

def deletionEdge {n : ℕ} (v : Fin (n + 1)) (e : CompleteEdge n) : CompleteEdge (n + 1) :=
  ⟨(v.succAbove e.val.1, v.succAbove e.val.2), Fin.strictMono_succAbove v e.property⟩

lemma deletionEdge_injective {n : ℕ} (v : Fin (n + 1)) :
    Function.Injective (deletionEdge v) := by
  intro e f h
  apply Subtype.ext
  apply Prod.ext
  · exact Fin.succAbove_right_injective (congrArg (fun a => a.val.1) h)
  · exact Fin.succAbove_right_injective (congrArg (fun a => a.val.2) h)

lemma deletionEdge_range {n : ℕ} (v : Fin (n + 1)) (e : CompleteEdge (n + 1)) :
    (∃ f, deletionEdge v f = e) ↔ e.val.1 ≠ v ∧ e.val.2 ≠ v := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨Fin.succAbove_ne v _, Fin.succAbove_ne v _⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq h1
    obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq h2
    have hab : a < b := (Fin.strictMono_succAbove v).lt_iff_lt.mp (by
      rw [ha, hb]
      exact e.property)
    exact ⟨⟨(a,b), hab⟩, Subtype.ext (Prod.ext ha hb)⟩

def deleteContinuousDrawing {n : ℕ} (D : ContinuousDrawing (completeGraph (n + 1)))
    (v : Fin (n + 1)) : ContinuousDrawing (completeGraph n) where
  vertex i := D.vertex (v.succAbove i)
  vertex_injective := D.vertex_injective.comp Fin.succAbove_right_injective
  edge e := D.edge (deletionEdge v e)
  edge_injective e := D.edge_injective (deletionEdge v e)
  interior_avoids_vertices e t ht i :=
    D.interior_avoids_vertices (deletionEdge v e) t ht (v.succAbove i)

lemma deletion_crossings_subset {n : ℕ} (D : ContinuousDrawing (completeGraph (n + 1)))
    (v : Fin (n + 1)) : crossingPoints (deleteContinuousDrawing D v) ⊆ crossingPoints D := by
  rintro x ⟨e, f, hef, he, hf⟩
  exact ⟨deletionEdge v e, deletionEdge v f,
    fun h => hef (deletionEdge_injective v h), he, hf⟩

def deleteDrawing {n : ℕ} (D : AdmissibleDrawing (completeGraph (n + 1)))
    (v : Fin (n + 1)) : AdmissibleDrawing (completeGraph n) where
  toContinuousDrawing := deleteContinuousDrawing D.toContinuousDrawing v
  crossings_finite := D.crossings_finite.subset (deletion_crossings_subset _ v)
  crossings_proper e f hef x he hf := D.crossings_proper (deletionEdge v e) (deletionEdge v f)
    (fun h => hef (deletionEdge_injective v h)) x he hf
  no_triples e f g hef heg hfg := D.no_triples (deletionEdge v e) (deletionEdge v f)
    (deletionEdge v g) (fun h => hef (deletionEdge_injective v h))
    (fun h => heg (deletionEdge_injective v h)) (fun h => hfg (deletionEdge_injective v h))

lemma deleteDrawing_spec {n : ℕ} (D : AdmissibleDrawing (completeGraph (n + 1)))
    (v : Fin (n + 1)) : VertexDeletion D v (deleteDrawing D v) := by
  refine ⟨fun _ => rfl, ?_⟩
  intro e f h1 h2 t
  have h : f = deletionEdge v e := Subtype.ext (Prod.ext h1 h2)
  subst f
  rfl

lemma deletion_crossing_iff {n : ℕ} (D : AdmissibleDrawing (completeGraph (n + 1)))
    (v : Fin (n + 1)) (x : Plane) (e f : CompleteEdge (n + 1)) (hef : e ≠ f)
    (he : x ∈ edgeInterior D.toContinuousDrawing e)
    (hf : x ∈ edgeInterior D.toContinuousDrawing f) :
    x ∈ crossingPoints (deleteDrawing D v).toContinuousDrawing ↔
      e.val.1 ≠ v ∧ e.val.2 ≠ v ∧ f.val.1 ≠ v ∧ f.val.2 ≠ v := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have ha' := (crossing_incident_iff D x e f hef he hf
      (deletionEdge v a)).mp ha
    have hb' := (crossing_incident_iff D x e f hef he hf
      (deletionEdge v b)).mp hb
    have hab' : deletionEdge v a ≠ deletionEdge v b :=
      fun h => hab (deletionEdge_injective v h)
    have hae := (deletionEdge_range v (deletionEdge v a)).mp ⟨a, rfl⟩
    have hbe := (deletionEdge_range v (deletionEdge v b)).mp ⟨b, rfl⟩
    rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
    · exact (hab' (ha'.trans hb'.symm)).elim
    · simpa [ha', hb', and_assoc] using And.intro hae hbe
    · simpa [ha', hb', and_assoc] using And.intro hbe hae
    · exact (hab' (ha'.trans hb'.symm)).elim
  · rintro ⟨he1, he2, hf1, hf2⟩
    obtain ⟨a, ha⟩ := (deletionEdge_range v e).mpr ⟨he1, he2⟩
    obtain ⟨b, hb⟩ := (deletionEdge_range v f).mpr ⟨hf1, hf2⟩
    refine ⟨a, b, ?_, ?_, ?_⟩
    · intro h
      exact hef (ha.symm.trans ((congrArg (deletionEdge v) h).trans hb))
    · change x ∈ edgeInterior D.toContinuousDrawing (deletionEdge v a)
      simpa [ha] using he
    · change x ∈ edgeInterior D.toContinuousDrawing (deletionEdge v b)
      simpa [hb] using hf

lemma crossing_endpoints_distinct {n : ℕ} (N : CleanDrawing (completeGraph n))
    (x : Plane) (e f : CompleteEdge n) (hef : e ≠ f)
    (he : x ∈ edgeInterior N.toContinuousDrawing e)
    (hf : x ∈ edgeInterior N.toContinuousDrawing f) :
    e.val.1 ≠ f.val.1 ∧ e.val.1 ≠ f.val.2 ∧ e.val.2 ≠ f.val.1 ∧ e.val.2 ≠ f.val.2 := by
  have hn : ¬ (e.val.1 = f.val.1 ∨ e.val.1 = f.val.2 ∨
      e.val.2 = f.val.1 ∨ e.val.2 = f.val.2) := by
    intro h
    exact Set.disjoint_left.mp (N.no_adjacent e f hef h) he hf
  tauto

lemma deletion_survivor_card {n : ℕ} (N : CleanDrawing (completeGraph (n + 1)))
    (x : Plane) (hx : x ∈ crossingPoints N.toContinuousDrawing) :
    (Finset.univ.filter (fun v : Fin (n + 1) =>
      x ∈ crossingPoints (deleteDrawing N.toAdmissibleDrawing v).toContinuousDrawing)).card =
      n + 1 - 4 := by
  obtain ⟨e, f, hef, he, hf⟩ := hx
  rcases crossing_endpoints_distinct N x e f hef he hf with ⟨h13, h14, h23, h24⟩
  have h12 : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  have h34 : f.val.1 ≠ f.val.2 := ne_of_lt f.property
  simp_rw [deletion_crossing_iff N.toAdmissibleDrawing _ x e f hef he hf]
  have hset : Finset.univ.filter (fun v : Fin (n + 1) =>
      e.val.1 ≠ v ∧ e.val.2 ≠ v ∧ f.val.1 ≠ v ∧ f.val.2 ≠ v) =
      Finset.univ \ {e.val.1, e.val.2, f.val.1, f.val.2} := by
    ext v
    simp [eq_comm]
  rw [hset, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp [h12, h13, h14, h23, h24, h34]

lemma deleteDrawing_count_filter {n : ℕ} (D : AdmissibleDrawing (completeGraph (n + 1)))
    (v : Fin (n + 1)) :
    crossingCount (deleteDrawing D v) = (D.crossings_finite.toFinset.filter fun x =>
      x ∈ crossingPoints (deleteDrawing D v).toContinuousDrawing).card := by
  unfold crossingCount
  congr 1
  ext x
  simp only [Set.Finite.mem_toFinset, Finset.mem_filter]
  exact ⟨fun h => ⟨deletion_crossings_subset D.toContinuousDrawing v h, h⟩, And.right⟩

theorem vertex_deletion_count (n : ℕ) (_hn : 4 ≤ n)
    (N : CleanDrawing (completeGraph (n + 1))) :
    ∃ A : Fin (n + 1) → AdmissibleDrawing (completeGraph n),
      (∀ v, VertexDeletion N.toAdmissibleDrawing v (A v)) ∧
      (∑ v, crossingCount (A v)) = (n + 1 - 4) * crossingCount N.toAdmissibleDrawing := by
  refine ⟨deleteDrawing N.toAdmissibleDrawing, deleteDrawing_spec N.toAdmissibleDrawing, ?_⟩
  simp_rw [deleteDrawing_count_filter, Finset.card_filter]
  rw [Finset.sum_comm]
  calc
    (∑ x ∈ N.crossings_finite.toFinset,
      ∑ v : Fin (n + 1), if x ∈ crossingPoints
        (deleteDrawing N.toAdmissibleDrawing v).toContinuousDrawing then 1 else 0) =
        ∑ _x ∈ N.crossings_finite.toFinset, (n + 1 - 4) := by
      apply Finset.sum_congr rfl
      intro x hx
      simpa only [Finset.card_filter] using
        deletion_survivor_card N x (by simpa using hx)
    _ = (n + 1 - 4) * crossingCount N.toAdmissibleDrawing := by
      simp [crossingCount, Nat.mul_comm]

end
end DeletionPort

theorem HillDeletionPort.leaf2 : HillDeletionPort.H2 := by
  intro n hn B hB
  obtain ⟨A, _, hA⟩ := DeletionPort.vertex_deletion_count n hn ⟨B, hB⟩
  exact ⟨A,hA⟩

theorem OMA.solution : OMA.R_arxiv_2009_03418_R1_H2_R2.H2 := HillDeletionPort.main HillDeletionPort.leaf1 HillDeletionPort.leaf2
