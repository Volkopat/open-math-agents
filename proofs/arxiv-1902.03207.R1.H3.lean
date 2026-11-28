import OMAReductions.R_arxiv_1902_03207_R1
import Mathlib
-- Credit: @my-other-github-account
/- Adapted from OpenAI critical percolation Lean formalization, revision 3344da59991ed94f9ba711217b29c1d760badfa6; Apache-2.0. -/
open Set MeasureTheory ProbabilityTheory
open scoped Classical
namespace CriticalPercolationLeaf
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
section
namespace OAI
open Set MeasureTheory ProbabilityTheory
namespace CriticalPercolation
structure z2 (V E : Type*) where
  ends : E → Sym2 V
namespace z2
variable {V E : Type*} (G : z2 V E)
def z1 (ω : Set E) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (G.ends '' ω)
def z7 : SimpleGraph V := G.z1 Set.univ
def LocallyFinite : Prop := ∀ v : V, {e : E | v ∈ G.ends e}.Finite
structure Aut where
  vertex : V ≃ V
  edge : E ≃ E
  preserves : ∀ e, G.ends (edge e) = Sym2.map vertex (G.ends e)
def QuasiTransitive : Prop :=
  ∃ S : Set V, S.Finite ∧ ∀ v : V, ∃ s ∈ S, ∃ φ : G.Aut, φ.vertex s = v
def cluster (ω : Set E) (v : V) : Set V := {w | (G.z1 ω).Reachable v w}
def z12 : Set (Set E) := {ω | ∃ v : V, (G.cluster ω v).Infinite}
noncomputable def law (_G : z2 V E) (p : unitInterval) : Measure (Set E) :=
  ProbabilityTheory.setBernoulli Set.univ p
noncomputable def z3 : unitInterval :=
  sInf {p : unitInterval | 0 < G.law p G.z12}
end z2
end CriticalPercolation
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set
open scoped Classical
namespace CriticalPercolation.EquivariantCoordinates
variable {Λ N T V : Type*} [Group Λ] [Group N] [Group T] [MulAction Λ V]
lemma z564 (a : Λ →* T)
    (hstab : ∀ (g : Λ) (v : V), g • v=v → a g=1) (g h : Λ) (v : V)
    (heq : g • v=h • v) : a g=a h := by
  have hs : (g⁻¹*h) • v=v := by rw [mul_smul,← heq,inv_smul_smul]
  have hh := hstab (g⁻¹*h) v hs
  rw [map_mul,map_inv,inv_mul_eq_one] at hh
  exact hh
lemma z397 [IsMulTorsionFree T] (ρ : Λ →* N) (φ : N →* T)
    (hfinite : ∀ v : V, ((MulAction.stabilizer Λ v).map ρ : Set N).Finite) :
    ∀ (g : Λ) (v : V), g • v=v → (φ.comp ρ) g=1 := by
  intro g v hg
  let H := (MulAction.stabilizer Λ v).map ρ
  have hmem : ρ g ∈ H := ⟨g,hg,rfl⟩
  let : Finite H := (hfinite v).to_subtype
  have hh := isOfFinOrder_of_finite (⟨ρ g,hmem⟩ : H)
  have hm := ((φ.comp H.subtype).isOfFinOrder hh).eq_one'
  exact hm
theorem z345 (a : Λ →* T)
    (hstab : ∀ (g : Λ) (v : V), g • v=v → a g=1) :
    ∃ π : V → T, ∀ g v, π (g • v)=a g*π v := by
  let q : V → MulAction.orbitRel.Quotient Λ V := Quotient.mk''
  let r : V → V := fun v => (q v).out
  have hex : ∀ v, ∃ g : Λ, g • r v=v := by
    intro v
    exact Quotient.exact (Quotient.out_eq' (q v)).symm
  choose b hb using hex
  let π : V → T := fun v => a (b v)
  refine ⟨π,?_⟩
  intro g v
  have hr : r (g • v)=r v := by
    apply congrArg Quotient.out
    exact MulAction.orbitRel.Quotient.quotient_smul_eq
  have hh : b (g • v) • r v=(g*b v) • r v := by
    rw [mul_smul,hb,← hr,hb]
  exact (z564 a hstab _ _ _ hh).trans (map_mul a g (b v))
lemma z346 [Nonempty V] (a : Λ →* T)
    (ha : Function.Surjective a) (π : V → T)
    (hπ : ∀ g v, π (g • v)=a g*π v) : Function.Surjective π := by
  intro t
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨g,hg⟩ := ha (t*(π v)⁻¹)
  exact ⟨g • v,by rw [hπ,hg,inv_mul_cancel_right]⟩
lemma z173 (a : Λ →* T) (π : V → T)
    (hπ : ∀ g v, π (g • v)=a g*π v) (x y : V)
    (hxy : y ∈ MulAction.orbit Λ x) (heq : π y=π x) :
    y ∈ MulAction.orbit a.ker x := by
  obtain ⟨g,hg⟩ := hxy
  change g • x=y at hg
  have hga : a g=1 := by
    have hh := hπ g x
    rw [hg,heq] at hh
    have hmul : a g*π x=1*π x := by simpa only [one_mul] using hh.symm
    exact mul_right_cancel hmul
  exact ⟨⟨g,hga⟩,hg⟩
theorem finite_fibers (a : Λ →* T) (π : V → T)
    (hπ : ∀ g v, π (g • v)=a g*π v)
    (hker : ∀ v : V, (MulAction.orbit a.ker v).Finite)
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (t : T) : (π ⁻¹' {t}).Finite := by
  have hf : ∀ s : V, {v | π v=t ∧ v∈MulAction.orbit Λ s}.Finite := by
    intro s
    by_cases he : ∃ y, π y=t ∧ y∈MulAction.orbit Λ s
    · obtain ⟨y,hyt,hys⟩ := he
      apply (hker y).subset
      rintro v ⟨hvt,hvs⟩
      apply z173 a π hπ y v _ (hvt.trans hyt.symm)
      rw [MulAction.orbit_eq_iff.mpr hys]
      exact hvs
    · convert Set.finite_empty using 1
      ext v
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      exact fun h => he ⟨v,h⟩
  apply (hS.biUnion fun s _ => hf s).subset
  intro v hv
  obtain ⟨s,hs,hvs⟩ := hcover v
  exact Set.mem_iUnion₂.mpr ⟨s,hs,hv,hvs⟩
end CriticalPercolation.EquivariantCoordinates
end
end
end
end OAI
end
section
namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
namespace CriticalPercolation
namespace z2
variable {V E : Type*} (G : z2 V E)
theorem openGraph_mono {ω ω' : Set E} (h : ω ⊆ ω') :
    G.z1 ω ≤ G.z1 ω' :=
  SimpleGraph.fromEdgeSet_mono (Set.image_mono h)
theorem cluster_mono {ω ω' : Set E} (h : ω ⊆ ω') (v : V) :
    G.cluster ω v ⊆ G.cluster ω' v :=
  fun _ hw => hw.mono (G.openGraph_mono h)
theorem z319 {ω ω' : Set E} (h : ω ⊆ ω')
    (hω : ω ∈ G.z12) : ω' ∈ G.z12 := by
  obtain ⟨v, hv⟩ := hω
  exact ⟨v, hv.mono (G.cluster_mono h v)⟩
theorem z420 (hlocal : G.LocallyFinite) (v : V) :
    (G.z7.neighborSet v).Finite := by
  classical
  have hf : (⋃ e ∈ {e : E | v ∈ G.ends e}, (↑(G.ends e).toFinset : Set V)).Finite :=
    (hlocal v).biUnion fun e _ => (G.ends e).toFinset.finite_toSet
  apply hf.subset
  intro w hw
  obtain ⟨⟨e, _, he⟩, _⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hw
  apply Set.mem_iUnion₂.mpr
  refine ⟨e, ?_, ?_⟩ <;> simp [he]
def z5 (G : z2 V E) (o : V) : ℕ → Set V
  | 0 => {o}
  | n + 1 => G.z5 o n ∪ ⋃ v ∈ G.z5 o n, G.z7.neighborSet v
lemma z19 (hlocal : G.LocallyFinite) (o : V) (n : ℕ) :
    (G.z5 o n).Finite := by
  induction n with
  | zero => exact Set.finite_singleton o
  | succ n ih => exact ih.union (ih.biUnion fun v _ => G.z420 hlocal v)
lemma z48 {o v : V} (h : G.z7.Reachable o v) :
    ∃ n, v ∈ G.z5 o n := by
  have hr := (G.z7.reachable_iff_reflTransGen o v).mp h
  clear h
  induction hr with
  | refl => exact ⟨0, rfl⟩
  | @tail u w hr huv ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, Or.inr (Set.mem_iUnion₂.mpr ⟨u, hn, huv⟩)⟩
theorem z53 (hconnected : G.z7.Connected)
    (hlocal : G.LocallyFinite) : Countable V := by
  obtain ⟨o⟩ := hconnected.nonempty
  have hc : (⋃ n : ℕ, G.z5 o n).Countable :=
    Set.countable_iUnion fun n => (G.z19 hlocal o n).countable
  have heq : (⋃ n : ℕ, G.z5 o n) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    obtain ⟨n, hn⟩ := G.z48 (hconnected o v)
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  rw [heq] at hc
  exact Set.countable_univ_iff.mp hc
theorem z113 (hconnected : G.z7.Connected)
    (hlocal : G.LocallyFinite) : Countable E := by
  let := G.z53 hconnected hlocal
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
lemma z72 (H : SimpleGraph V) (v w : V) :
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
lemma z385 [Countable E] (v w : V) :
    Measurable (fun ω : Set E => (G.z1 ω).Adj v w) := by
  simp only [z1, SimpleGraph.fromEdgeSet_adj, Set.mem_image]
  exact (Measurable.exists fun e =>
    (measurable_set_mem e).and measurable_const).and measurable_const
lemma z439 [Countable V] [Countable E] (n : ℕ) (v w : V) :
    Measurable (fun ω : Set E => lengthReach (G.z1 ω) n v w) := by
  induction n generalizing w with
  | zero => exact measurable_const
  | succ n ih =>
      exact Measurable.exists fun u => (ih u).and (G.z385 u w)
lemma z79 [Countable V] [Countable E] (v w : V) :
    Measurable (fun ω : Set E => (G.z1 ω).Reachable v w) := by
  simp_rw [z72]
  exact Measurable.exists fun n => G.z439 n v w
lemma z548 [Countable V] [Countable E] (v : V) :
    Measurable (fun ω : Set E => G.cluster ω v) := by
  exact measurable_pi_lambda _ fun vertex => G.z79 v vertex
lemma z39 [Countable V] [Countable E] (v : V) :
    Measurable (fun ω : Set E => (G.cluster ω v).Infinite) := by
  simp_rw [← Set.encard_eq_top_iff]
  exact (measurable_encard.comp (G.z548 v)).eq_const ⊤
theorem z37 [Countable V] [Countable E] :
    MeasurableSet G.z12 := by
  exact (Measurable.exists fun v => G.z39 v).setOf
theorem z157 [Countable V] (μ : Measure (Set E)) :
    μ G.z12 = 0 ↔ ∀ v, μ {ω | (G.cluster ω v).Infinite} = 0 := by
  have heq : G.z12 = ⋃ v, {ω | (G.cluster ω v).Infinite} := by
    ext ω
    simp [z12]
  rw [heq, measure_iUnion_null_iff]
@[simp] lemma z333 : G.z1 ∅ = ⊥ := by
  simp [z1]
@[simp] lemma cluster_empty (v : V) : G.cluster ∅ v = {v} := by
  ext w
  simp [cluster, SimpleGraph.reachable_bot, eq_comm]
@[simp] lemma z614 : ∅ ∉ G.z12 := by
  simp [z12]
lemma z527 [Countable V] [Countable E] : G.law 0 G.z12 = 0 := by
  rw [law, ProbabilityTheory.setBernoulli_zero,
    Measure.dirac_apply' _ G.z37]
  simp
lemma z51 {p : unitInterval}
    (hp : 0 < G.law p G.z12) : G.z3 ≤ p :=
  sInf_le hp
lemma z43 {ω : Set E} {v w : V} (h : w ∈ G.cluster ω v) :
    ∃ s : Set E, s.Finite ∧ s ⊆ ω ∧ w ∈ G.cluster s v := by
  classical
  have hr := ((G.z1 ω).reachable_iff_reflTransGen v w).mp h
  clear h
  induction hr with
  | refl => exact ⟨∅, Set.finite_empty, Set.empty_subset _, .refl _⟩
  | @tail u w hr huw ih =>
      obtain ⟨s, hs, hsω, hvs⟩ := ih
      obtain ⟨⟨e, heω, heq⟩, hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp huw
      refine ⟨insert e s, hs.insert e, Set.insert_subset heω hsω, ?_⟩
      have hvu : (G.z1 (insert e s)).Reachable v u :=
        hvs.mono (G.openGraph_mono (Set.subset_insert _ _))
      apply hvu.trans
      apply SimpleGraph.Adj.reachable
      exact (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e, Set.mem_insert _ _, heq⟩, hne⟩
lemma z119 {ω : Set E} {v : V} {K : Set V}
    (hK : K.Finite) (hKv : K ⊆ G.cluster ω v) :
    ∃ s : Set E, s.Finite ∧ s ⊆ ω ∧ K ⊆ G.cluster s v := by
  classical
  have h : ∀ w ∈ K, ∃ s : Set E, s.Finite ∧ s ⊆ ω ∧ w ∈ G.cluster s v :=
    fun w hw => G.z43 (hKv hw)
  choose s hs hsω hws using h
  let := hK.fintype
  refine ⟨⋃ w : K, s w w.property, ?_, ?_, ?_⟩
  · exact Set.finite_iUnion fun w => hs w w.property
  · exact Set.iUnion_subset fun w => hsω w w.property
  · intro w hw
    exact G.cluster_mono (Set.subset_iUnion (fun w : K => s w w.property) ⟨w, hw⟩)
      v (hws w hw)
end z2
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
lemma z83 (H : SimpleGraph V) {U U' : Set V} (h : U ⊆ U') :
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
lemma z170 {H : SimpleGraph V} {S : Set V} {s v : V}
    (hs : s ∉ roots H S) (hsv : H.Reachable s v) : v ∉ roots H S := by
  rintro ⟨u, hu, huv⟩
  exact hs ⟨u, hu, huv.trans hsv.symm⟩
lemma roots_closed {H : SimpleGraph V} {S : Set V} {v w : V}
    (hv : v ∈ roots H S) (hvw : H.Adj v w) : w ∈ roots H S := by
  obtain ⟨s, hs, hsv⟩ := hv
  exact ⟨s, hs, hsv.trans hvw.reachable⟩
lemma z172 {H : SimpleGraph V} {U : Set V}
    (hU : ∀ ⦃v w⦄, v ∈ U → H.Adj v w → w ∈ U) {s v : V}
    (hs : s ∈ U) (hsv : H.Reachable s v) : v ∈ U := by
  have hr := (H.reachable_iff_reflTransGen s v).mp hsv
  clear hsv
  induction hr with
  | refl => exact hs
  | tail _ huv ih => exact hU ih huv
lemma z524 {H H' : SimpleGraph V} (S : Set V)
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
lemma z101 {H H' : SimpleGraph V} {S U : Set V}
    (hU : roots H S = U)
    (hh : ∀ ⦃v w⦄, v ∈ U → (H.Adj v w ↔ H'.Adj v w)) :
    roots H' S = U := by
  subst U
  apply Set.Subset.antisymm
  · rintro v ⟨s, hs, hsv⟩
    exact z172
      (fun {_ _} hv hvw => roots_closed hv ((hh hv).mpr hvw)) (roots_self H S hs) hsv
  · exact z524 S fun {_ _} hv hvw => (hh hv).mp hvw
lemma z64 (H : SimpleGraph V) (S : Set V) (s : V)
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
        ⟨huv, z170 hs hsu, z170 hs hsv⟩)
lemma delete_delete (H : SimpleGraph V) (U W : Set V) :
    delete (delete H U) W = delete H (W ∪ U) := by
  ext v w
  simp only [delete, Set.mem_union, not_or]
  tauto
lemma z55 (H : SimpleGraph V) (S U : Set V) (s : V)
    (hs : s ∉ roots (delete H U) S) :
    component (delete H (roots (delete H U) S ∪ U)) s = component (delete H U) s := by
  rw [← delete_delete]
  exact z64 _ _ _ hs
noncomputable def residual (H : SimpleGraph V) (S : Set V) (s : V)
    (F : Set V → ℝ) (U : Set V) : ℝ := by
  classical
  exact if s ∉ roots (delete H U) S then
    F (component (delete H (roots (delete H U) S)) s) -
      F (component (delete H (roots (delete H U) S ∪ U)) s)
  else 0
lemma z490 (H : SimpleGraph V) (S : Set V) (s : V)
    {F : Set V → ℝ} (hF : Monotone F) (U : Set V) : 0 ≤ residual H S s F U := by
  classical
  unfold residual
  split_ifs
  · rfl
  · exact sub_nonneg.mpr (hF (component_mono (z83 H Set.subset_union_left) s))
lemma z571 (H : SimpleGraph V) (S : Set V) (s : V)
    {F : Set V → ℝ} (hF : Monotone F) : Monotone (residual H S s F) := by
  classical
  intro U U' hUU'
  have hW : roots (delete H U') S ⊆ roots (delete H U) S :=
    roots_mono (z83 H hUU') S
  by_cases hs : s ∉ roots (delete H U) S
  · have hs' : s ∉ roots (delete H U') S := fun h => hs (hW h)
    rw [residual, if_pos hs, residual, if_pos hs']
    rw [z55 H S U s hs,
      z55 H S U' s hs']
    have hh₁ := hF (component_mono (z83 H hW) s)
    have hh₂ := hF (component_mono (z83 H hUU') s)
    exact sub_le_sub hh₁ hh₂
  · rw [residual, if_neg hs]
    exact z490 H S s hF U'
end ClusterDeletion
namespace z2
variable {V E : Type*} (G : z2 V E)
def z9 (U : Set V) : Set E := {e | ∃ v ∈ U, v ∈ G.ends e}
lemma z99 {U : Set V} {ω ω' : Set E}
    (hω : ∀ e ∈ G.z9 U, e ∈ ω ↔ e ∈ ω') {v w : V} (hv : v ∈ U) :
    (G.z1 ω).Adj v w ↔ (G.z1 ω').Adj v w := by
  simp only [z1, SimpleGraph.fromEdgeSet_adj, Set.mem_image]
  have he : ∀ e, G.ends e = s(v, w) → e ∈ G.z9 U := by
    intro e heq
    exact ⟨v, hv, by simp [heq]⟩
  constructor
  · rintro ⟨⟨e, heω, heq⟩, hne⟩
    exact ⟨⟨e, (hω e (he e heq)).mp heω, heq⟩, hne⟩
  · rintro ⟨⟨e, heω, heq⟩, hne⟩
    exact ⟨⟨e, (hω e (he e heq)).mpr heω, heq⟩, hne⟩
lemma z500 {S U : Set V} {ω ω' : Set E}
    (hU : ClusterDeletion.roots (G.z1 ω) S = U)
    (hω : ∀ e ∈ G.z9 U, e ∈ ω ↔ e ∈ ω') :
    ClusterDeletion.roots (G.z1 ω') S = U :=
  ClusterDeletion.z101 hU (fun {_ _} hv => G.z99 hω hv)
lemma z337 (U : Set V) :
    DependsOn (fun ω : Set E => ClusterDeletion.delete (G.z1 ω) U)
      (G.z9 U)ᶜ := by
  intro ω ω' hω
  ext v w
  change ((G.z1 ω).Adj v w ∧ v ∉ U ∧ w ∉ U) ↔
    ((G.z1 ω').Adj v w ∧ v ∉ U ∧ w ∉ U)
  by_cases hv : v ∈ U
  · simp [hv]
  by_cases hw : w ∈ U
  · simp [hw]
  simp only [hv, hw, not_false_eq_true, and_self, and_true, z1,
    SimpleGraph.fromEdgeSet_adj]
  have he : ∀ e, G.ends e = s(v, w) → e ∈ (G.z9 U)ᶜ := by
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
lemma z98 {S U W : Set V} {ω ω' : Set E}
    (hW : ClusterDeletion.roots (ClusterDeletion.delete (G.z1 ω) U) S = W)
    (hω : ∀ e ∈ G.z9 W, e ∈ ω ↔ e ∈ ω') :
    ClusterDeletion.roots (ClusterDeletion.delete (G.z1 ω') U) S = W := by
  apply ClusterDeletion.z101 hW
  intro v v' hv
  change ((G.z1 ω).Adj v v' ∧ v ∉ U ∧ v' ∉ U) ↔
    ((G.z1 ω').Adj v v' ∧ v ∉ U ∧ v' ∉ U)
  rw [G.z99 hω hv]
lemma z247 (S U W : Set V) :
    DependsOn (fun ω : Set E =>
      ClusterDeletion.roots (ClusterDeletion.delete (G.z1 ω) U) S = W)
      (G.z9 W) := by
  intro ω ω' hω
  apply propext
  exact ⟨fun h => G.z98 h (fun e he => (hω e he).to_iff),
    fun h => G.z98 h (fun e he => (hω e he).symm.to_iff)⟩
end z2
end CriticalPercolation
open scoped BigOperators
open Set
end
end
end OAI
end
section
namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical
namespace CriticalPercolation.z2
open scoped Classical
variable {V E : Type*}
def cutEdges (G : z2 V E) (O : Set V) : Set E :=
  {e | ∃ x y, G.ends e = s(x,y) ∧ x ∉ O ∧ y ∈ O}
lemma z102 (G : z2 V E) (O : Set V) (ω : Set E)
    (hc : ∀ e ∈ G.cutEdges O, ¬ω e) {a b : V} (ha : a ∉ O) (hb : b ∈ O) :
    ¬(G.z1 ω).Reachable a b := by
  intro hab
  have hclosed : ∀ ⦃v z⦄, v ∈ Oᶜ → (G.z1 ω).Adj v z → z ∈ Oᶜ := by
    intro v z hv hvz hz
    obtain ⟨⟨e,he,heq⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hvz
    exact hc e ⟨v,z,heq,hv,hz⟩ he
  exact (ClusterDeletion.z172 hclosed ha hab) hb
end CriticalPercolation.z2
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set
open scoped Classical
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
def z4 (S : Set V) : Set E := {e | ∀ v ∈ G.ends e, v∈S}
def induce (S : Set V) : z2 S (G.z4 S) where
  ends e := (G.ends e.val).attachWith e.property
lemma z107 (S : Set V) (e : G.z4 S) :
    Sym2.map Subtype.val ((G.induce S).ends e) = G.ends e.val :=
  Sym2.attachWith_map_subtypeVal _
lemma induce_ends_eq (S : Set V) (e : G.z4 S) (u v : S) :
    (G.induce S).ends e = s(u,v) ↔ G.ends e.val = s(u.val,v.val) := by
  rw [← G.z107 S e,← Sym2.map_mk]
  exact (Sym2.map.injective Subtype.val_injective).eq_iff.symm
lemma z323 (hG : G.LocallyFinite) {S : Set V} (hS : S.Finite) :
    (G.z9 S).Finite := by
  have hh := hS.biUnion (fun v _ => hG v)
  convert hh using 1
  ext e
  simp only [z9,Set.mem_ofPred_eq,Set.mem_iUnion,exists_prop]
lemma z27 (hG : G.LocallyFinite) {S : Set V} (hS : S.Finite) :
    (G.z4 S).Finite := by
  apply (G.z323 hG hS).subset
  intro e he
  obtain ⟨⟨u,v⟩,huv⟩ := Sym2.mk_surjective (G.ends e)
  have hu : u ∈ G.ends e := by rw [← huv]; simp
  exact ⟨u,he u hu,hu⟩
lemma induce_adj (S : Set V) (ω : Set (G.z4 S)) (u v : S) :
    ((G.induce S).z1 ω).Adj u v ↔
      (G.z1 (Subtype.val '' ω)).Adj u.val v.val := by
  simp only [z1,SimpleGraph.fromEdgeSet_adj,Set.mem_image]
  constructor
  · rintro ⟨⟨e,he,hend⟩,hne⟩
    exact ⟨⟨e.val,⟨e,he,rfl⟩,(G.induce_ends_eq S e u v).mp hend⟩,
      fun h => hne (Subtype.ext h)⟩
  · rintro ⟨⟨e,⟨a,ha,rfl⟩,hend⟩,hne⟩
    exact ⟨⟨a,ha,(G.induce_ends_eq S a u v).mpr hend⟩,
      fun h => hne (congrArg Subtype.val h)⟩
lemma z489 (S : Set V) (ω : Set (G.z4 S)) {u v : V}
    (h : (G.z1 (Subtype.val '' ω)).Adj u v) : u∈S ∧ v∈S := by
  obtain ⟨⟨e,⟨a,ha,rfl⟩,he⟩,_⟩ := h
  constructor
  · exact a.property u (by rw [he]; simp)
  · exact a.property v (by rw [he]; simp)
lemma z148 (S : Set V) (ω : Set (G.z4 S)) (u v : S) :
    ((G.induce S).z1 ω).Reachable u v ↔
      (G.z1 (Subtype.val '' ω)).Reachable u.val v.val := by
  constructor
  · intro h
    exact h.map ⟨Subtype.val, fun {a b} hab => (G.induce_adj S ω a b).mp hab⟩
  · intro h
    have H : ∀ w, (G.z1 (Subtype.val '' ω)).Reachable u.val w →
        ∀ hw : w∈S, ((G.induce S).z1 ω).Reachable u ⟨w,hw⟩ := by
      intro w hh
      rw [SimpleGraph.reachable_iff_reflTransGen] at hh
      induction hh with
      | refl => intro _; exact SimpleGraph.Reachable.refl _
      | @tail w z _ hz ih =>
        intro hmem
        have hw := (G.z489 S ω hz).1
        exact (ih hw).trans ((G.induce_adj S ω ⟨w,hw⟩ ⟨z,hmem⟩).mpr hz).reachable
    exact H v.val h v.property
lemma z204 (S : Set V) (ω : Set (G.z4 S)) (u : S) :
    G.cluster (Subtype.val '' ω) u.val ⊆ S := by
  intro v hv
  rw [cluster,Set.mem_ofPred_eq,SimpleGraph.reachable_iff_reflTransGen] at hv
  induction hv with
  | refl => exact u.property
  | tail _ hadj _ => exact (G.z489 S ω hadj).2
lemma z282 (S : Set V) (ω : Set (G.z4 S)) (u : S) :
    Subtype.val '' ((G.induce S).cluster ω u) = G.cluster (Subtype.val '' ω) u.val := by
  ext v
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact (G.z148 S ω u a).mp ha
  · intro hv
    have hmem := G.z204 S ω u hv
    exact ⟨⟨v,hmem⟩,(G.z148 S ω u ⟨v,hmem⟩).mpr hv,rfl⟩
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
open Set
namespace CriticalPercolation.z8
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
lemma expect_add (w : E → A → ℝ) (f g : (E → A) → ℝ) :
    expect w (fun ω => f ω + g ω) = expect w f + expect w g := by
  classical
  simp [expect, mul_add, Finset.sum_add_distrib]
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
lemma z146 (w : E → A → ℝ) (f : (E → A) → ℝ) (c : ℝ) :
    expect w (fun ω => f ω * c) = expect w f * c := by
  classical
  unfold expect
  rw [Finset.sum_mul]
  apply Finset.sum_congr (by ext; simp)
  intro ω _
  ring
lemma z424 {B : Type*} [Fintype B] [DecidableEq B] (w : E → A → ℝ)
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
lemma z608 {B : Type*} [Fintype B] (w : E → A → ℝ)
    (hw : ∀ e, ∑ a, w e a = 1) (r : (E → A) → B) (D : B → Set E)
    (hr : ∀ b, DependsOn (fun ω => r ω = b) (D b))
    (f : B → (E → A) → ℝ) (hf : ∀ b, DependsOn (f b) (D b)ᶜ) :
    expect w (fun ω => f (r ω) ω) =
      expect w (fun ω => expect w (f (r ω))) := by
  classical
  rw [z424 w r f,
    z424 w r (fun b _ => expect w (f b))]
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
  rw [hleft, hright, expect_indep w hw (D b) hi (hf b), z146]
end CriticalPercolation.z8
end
end
end OAI
end
section
namespace OAI
section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation
namespace z0
noncomputable def bitMeasure (p : unitInterval) : Measure Prop :=
  unitInterval.toNNReal p • Measure.dirac True +
    unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac False
instance z613 (p : unitInterval) : IsProbabilityMeasure (bitMeasure p) := by
  constructor
  simp [bitMeasure]
noncomputable def z28 (p : unitInterval) (b : Prop) : ℝ :=
  if b then p else 1-p
lemma bitWeight_sum (p : unitInterval) : ∑ b, z28 p b = 1 := by
  simp [z28]
lemma z143 (p : unitInterval) (b : Prop) : 0 ≤ z28 p b := by
  unfold z28
  split_ifs
  · exact p.property.1
  · exact sub_nonneg.mpr p.property.2
lemma z46 (p : unitInterval) (b : Prop) :
    (bitMeasure p).real {b} = z28 p b := by
  by_cases hb : b
  · have he : b = True := propext (iff_true_intro hb)
    subst b
    simp [bitMeasure, z28, measureReal_def]
  · have he : b = False := propext (iff_false_intro hb)
    subst b
    simp [bitMeasure, z28, measureReal_def]
variable {E : Type*}
noncomputable def law (q : E → unitInterval) : Measure (Set E) :=
  Measure.map MeasurableEquiv.setOfPred (Measure.infinitePi fun e => bitMeasure (q e))
instance z603 (q : E → unitInterval) : IsProbabilityMeasure (law q) := by
  unfold law
  exact Measure.isProbabilityMeasure_map MeasurableEquiv.setOfPred.measurable.aemeasurable
lemma law_const (p : unitInterval) :
    law (fun _ : E => p) = setBernoulli Set.univ p := by
  rw [law, setBernoulli_eq_map]
  rfl
lemma z410 [Fintype E] (q : E → unitInterval) (f : (E → Prop) → ℝ) :
    (∫ ω, f ω ∂(Measure.infinitePi fun e => bitMeasure (q e))) =
      z8.expect (fun e => z28 (q e)) f := by
  rw [Measure.infinitePi_eq_pi, integral_fintype Integrable.of_finite]
  unfold z8.expect z8.density
  apply Finset.sum_congr rfl
  intro ω _
  rw [smul_eq_mul]
  congr 1
  simp only [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl (fun e _ => z46 (q e) (ω e))
lemma z63 [Fintype E] (q : E → unitInterval) (f : Set E → ℝ) :
    (∫ ω, f ω ∂law q) =
      z8.expect (fun e => z28 (q e)) (fun ω => f {e | ω e}) := by
  rw [law, integral_map MeasurableEquiv.setOfPred.measurable.aemeasurable
    Integrable.of_finite.aestronglyMeasurable, z410]
  rfl
lemma z97 (q : E → unitInterval) (s : Set E) :
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
end z0
end CriticalPercolation
open Set
open scoped Classical
end
end
end OAI
end
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
namespace CriticalPercolation.z0
variable {E : Type*}
lemma z62 (e : E ≃ E) :
    Measurable (fun ω : Set E => e '' ω) := by
  have he : (fun ω : Set E => e '' ω) = (fun ω => e.symm ⁻¹' ω) := by
    funext ω
    ext i
    simp
  rw [he]
  exact measurable_pi_lambda _ (fun index => measurable_set_mem (e.symm index))
lemma law_map_equiv (p : unitInterval) (e : E ≃ E) :
    (law (fun _ : E => p)).map (fun ω : Set E => e '' ω) = law (fun _ : E => p) := by
  unfold law
  rw [Measure.map_map (z62 e) MeasurableEquiv.setOfPred.measurable]
  have he : (fun ω : Set E => e '' ω) ∘ MeasurableEquiv.setOfPred =
      MeasurableEquiv.setOfPred ∘ MeasurableEquiv.piCongrLeft (fun _ : E => Prop) e := by
    funext ω
    ext i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  rw [he, ← Measure.map_map MeasurableEquiv.setOfPred.measurable (by fun_prop),
    Measure.infinitePi_map_piCongrLeft (fun _ : E => bitMeasure p) e]
lemma z611 (p : unitInterval) (s : Set E) (hs : s.Finite) :
    (law (fun _ : E => p)).real {ω | s ⊆ ω} = (p : ℝ) ^ s.ncard := by
  let : Fintype s := hs.fintype
  have hmeas : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
    measurable_pi_lambda _ (fun edge => measurable_set_mem edge.val)
  have he : {ω : Set E | s ⊆ ω} =
      (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) ⁻¹' {Set.univ} := by
    ext ω
    simp [Set.subset_def, Set.eq_univ_iff_forall]
  rw [he, measureReal_def, ← Measure.map_apply hmeas (.of_discrete),
    z97, law_const]
  change (setBernoulli (Set.univ : Set s) p).real {Set.univ} = _
  rw [setBernoulli_real_singleton p (Subset.rfl) Set.finite_univ]
  simp [Set.ncard_univ]
end CriticalPercolation.z0
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
instance z603 (p : unitInterval) : IsProbabilityMeasure (G.law p) := by
  unfold law
  infer_instance
lemma Aut.adj_map (φ : G.Aut) (ω : Set E) (v w : V) :
    (G.z1 (φ.edge '' ω)).Adj (φ.vertex v) (φ.vertex w) ↔
      (G.z1 ω).Adj v w := by
  simp only [z1, SimpleGraph.fromEdgeSet_adj, Set.mem_image]
  constructor
  · rintro ⟨⟨e, ⟨f, hf, rfl⟩, hend⟩, hne⟩
    rw [φ.preserves, ← Sym2.map_mk] at hend
    exact ⟨⟨f, hf, Sym2.map.injective φ.vertex.injective hend⟩,
      fun h => hne (congrArg φ.vertex h)⟩
  · rintro ⟨⟨e, he, hend⟩, hne⟩
    refine ⟨⟨φ.edge e, ⟨e, he, rfl⟩, ?_⟩, ?_⟩
    · rw [φ.preserves, hend, Sym2.map_mk]
    · exact fun h => hne (φ.vertex.injective h)
noncomputable def Aut.openGraphIso (φ : G.Aut) (ω : Set E) :
    G.z1 ω ≃g G.z1 (φ.edge '' ω) where
  toEquiv := φ.vertex
  map_rel_iff' := fun {v w} => Aut.adj_map G φ ω v w
lemma Aut.cluster_image (φ : G.Aut) (ω : Set E) (o : V) :
    φ.vertex '' G.cluster ω o = G.cluster (φ.edge '' ω) (φ.vertex o) := by
  ext v
  obtain ⟨w, rfl⟩ := φ.vertex.surjective v
  simp only [Set.mem_image, φ.vertex.injective.eq_iff, exists_eq_right]
  change (G.z1 ω).Reachable o w ↔
    (G.z1 (φ.edge '' ω)).Reachable (φ.vertex o) (φ.vertex w)
  exact (SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω) (u := o) (v := w)).symm
def z14 (o : V) : Set (Set E) := {ω | (G.cluster ω o).Infinite}
lemma z60 [Countable V] [Countable E] (o : V) :
    MeasurableSet (G.z14 o) := (G.z39 o).setOf
lemma Aut.z461 (φ : G.Aut) (o : V) :
    (fun ω : Set E => φ.edge '' ω) ⁻¹' (G.z14 (φ.vertex o)) =
      G.z14 o := by
  ext ω
  change (G.cluster (φ.edge '' ω) (φ.vertex o)).Infinite ↔ (G.cluster ω o).Infinite
  rw [← φ.cluster_image]
  exact Set.infinite_image_iff φ.vertex.injective.injOn
lemma law_map_aut (p : unitInterval) (φ : G.Aut) :
    (G.law p).map (fun ω : Set E => φ.edge '' ω) = G.law p := by
  simpa only [z0.law_const, law] using
    z0.law_map_equiv p φ.edge
lemma Aut.z227 [Countable V] [Countable E]
    (φ : G.Aut) (p : unitInterval) (o : V) :
    G.law p (G.z14 (φ.vertex o)) = G.law p (G.z14 o) := by
  conv_lhs => rw [← G.law_map_aut p φ]
  rw [Measure.map_apply (z0.z62 φ.edge)
    (G.z60 _), φ.z461]
lemma Aut.z543 [Countable V] [Countable E]
    (φ : G.Aut) (p : unitInterval) (o : V) :
    (G.law p).real (G.z14 (φ.vertex o)) = (G.law p).real (G.z14 o) := by
  simp only [measureReal_def, φ.z227]
end CriticalPercolation.z2
open Filter Topology
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set
open scoped Classical
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
lemma z26 (o : V) : Monotone (G.z5 o) := by
  apply monotone_nat_of_le_succ
  intro n
  exact Set.subset_union_left
lemma z45 (o : V) (n : ℕ) : o ∈ G.z5 o n :=
  G.z26 o (Nat.zero_le n) rfl
lemma z186 {o v w : V} {n : ℕ} (hv : v ∈ G.z5 o n)
    (he : G.z7.Adj v w) : w ∈ G.z5 o (n+1) :=
  Or.inr (Set.mem_iUnion₂.mpr ⟨v,hv,he⟩)
lemma vertexBall_add {o v : V} {n : ℕ} (hv : v ∈ G.z5 o n) (m : ℕ) :
    G.z5 v m ⊆ G.z5 o (n+m) := by
  induction m with
  | zero => simpa only [z5,Nat.add_zero,Set.singleton_subset_iff] using hv
  | succ m ih =>
    rintro w (hw | hw)
    · exact G.z26 o (by omega) (ih hw)
    · obtain ⟨z,hz,hzw⟩ := Set.mem_iUnion₂.mp hw
      exact G.z186 (ih hz) hzw
lemma z330 {o v : V} {n : ℕ} : v ∈ G.z5 o n ↔ o ∈ G.z5 v n := by
  have h : ∀ n (o v : V), v ∈ G.z5 o n → o ∈ G.z5 v n := by
    intro n
    induction n with
    | zero => intro o v hv; simpa only [z5,Set.mem_singleton_iff] using hv.symm
    | succ n ih =>
      intro o v hv
      rcases hv with hv | hv
      · exact G.z26 v (Nat.le_succ n) (ih o v hv)
      · obtain ⟨z,hz,hzv⟩ := Set.mem_iUnion₂.mp hv
        have h1 : z ∈ G.z5 v 1 := G.z186 (G.z45 v 0) hzv.symm
        simpa only [Nat.add_comm 1] using G.vertexBall_add h1 n (ih o z hz)
  exact ⟨h n o v,h n v o⟩
lemma Aut.fullGraph_adj (φ : G.Aut) (u v : V) :
    G.z7.Adj (φ.vertex u) (φ.vertex v) ↔ G.z7.Adj u v := by
  simpa only [z7,Set.image_univ,Equiv.range_eq_univ] using Aut.adj_map G φ Set.univ u v
lemma Aut.vertexBall_mem (φ : G.Aut) (o v : V) (n : ℕ) :
    φ.vertex v ∈ G.z5 (φ.vertex o) n ↔ v ∈ G.z5 o n := by
  induction n generalizing v with
  | zero => simp only [z5,Set.mem_singleton_iff,φ.vertex.injective.eq_iff]
  | succ n ih =>
    simp only [z5,Set.mem_union,Set.mem_iUnion,exists_prop,SimpleGraph.mem_neighborSet]
    constructor
    · rintro (h | ⟨z,hz,hzv⟩)
      · exact Or.inl ((ih v).mp h)
      · obtain ⟨w,rfl⟩ := φ.vertex.surjective z
        exact Or.inr ⟨w,(ih w).mp hz,
          (Aut.fullGraph_adj G φ w v).mp hzv⟩
    · rintro (h | ⟨z,hz,hzv⟩)
      · exact Or.inl ((ih v).mpr h)
      · exact Or.inr ⟨φ.vertex z,(ih z).mpr hz,(Aut.fullGraph_adj G φ z v).mpr hzv⟩
lemma Aut.z430 (φ : G.Aut) (o : V) (n : ℕ) :
    φ.vertex '' G.z5 o n = G.z5 (φ.vertex o) n := by
  ext v
  obtain ⟨w,rfl⟩ := φ.vertex.surjective v
  simpa only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right] using
    (Aut.vertexBall_mem G φ o w n).symm
lemma Aut.z592 (φ : G.Aut) (o : V) (n : ℕ) :
    (G.z5 (φ.vertex o) n).ncard = (G.z5 o n).ncard := by
  rw [← Aut.z430 G φ,Set.ncard_image_of_injective _ φ.vertex.injective]
lemma Aut.z391 (φ : G.Aut) (v : V) :
    φ.edge '' G.z9 {v} = G.z9 {φ.vertex v} := by
  ext e
  obtain ⟨f,rfl⟩ := φ.edge.surjective e
  simp only [Set.mem_image,φ.edge.injective.eq_iff,exists_eq_right,z9,
    Set.mem_ofPred_eq,Set.mem_singleton_iff,exists_eq_left,φ.preserves]
  simp only [Sym2.mem_map,φ.vertex.injective.eq_iff,exists_eq_right]
lemma z190 (hquasi : G.QuasiTransitive) :
    ∃ D : ℕ, 1≤D ∧ ∀ v, (G.z9 {v}).ncard ≤ D := by
  obtain ⟨S,hS,hcover⟩ := hquasi
  let D := 1 + ∑ v ∈ hS.toFinset, (G.z9 {v}).ncard
  refine ⟨D,by dsimp [D]; omega,?_⟩
  intro v
  obtain ⟨z,hz,φ,rfl⟩ := hcover v
  rw [← Aut.z391 G φ,Set.ncard_image_of_injective _ φ.edge.injective]
  exact (Finset.single_le_sum (f := fun v => (G.z9 {v}).ncard) (fun _ _ => Nat.zero_le _) (hS.mem_toFinset.mpr hz)).trans (Nat.le_add_left _ _)
lemma z562 (hquasi : G.QuasiTransitive) (n : ℕ) :
    ∃ M : ℕ, ∀ v, (G.z5 v n).ncard ≤ M := by
  obtain ⟨S,hS,hcover⟩ := hquasi
  refine ⟨∑ v ∈ hS.toFinset, (G.z5 v n).ncard,?_⟩
  intro v
  obtain ⟨z,hz,φ,rfl⟩ := hcover v
  rw [Aut.z592 G φ]
  exact Finset.single_le_sum (f := fun v => (G.z5 v n).ncard) (fun _ _ => Nat.zero_le _) (hS.mem_toFinset.mpr hz)
lemma z76 (hconnected : G.z7.Connected)
    (o : V) {S : Set V} (hS : S.Finite) : ∃ n, S ⊆ G.z5 o n := by
  have hh : ∀ v : S, ∃ n, v.val ∈ G.z5 o n :=
    fun v => G.z48 (hconnected o v)
  choose n hn using hh
  let := hS.fintype
  refine ⟨∑ v : S, n v,?_⟩
  intro v hv
  exact G.z26 o (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ (⟨v,hv⟩ : S))) (hn ⟨v,hv⟩)
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set
open scoped Classical
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
protected def Aut.symm (φ : G.Aut) : G.Aut where
  vertex := φ.vertex.symm
  edge := φ.edge.symm
  preserves e := by
    have h := φ.preserves (φ.edge.symm e)
    have hh := congrArg (Sym2.map φ.vertex.symm) h
    simpa only [Equiv.apply_symm_apply,Sym2.map_map,Equiv.symm_comp_self,Sym2.map_id',id_eq] using hh.symm
protected def Aut.trans (φ ψ : G.Aut) : G.Aut where
  vertex := φ.vertex.trans ψ.vertex
  edge := φ.edge.trans ψ.edge
  preserves e := by
    simp only [Equiv.trans_apply,ψ.preserves,φ.preserves,Sym2.map_map]
    rfl
lemma z255 (hconnected : G.z7.Connected)
    (hquasi : G.QuasiTransitive) :
    ∃ C : ℕ, ∀ u v, ∃ φ : G.Aut, φ.vertex u ∈ G.z5 v C := by
  obtain ⟨S,hS,hcover⟩ := hquasi
  obtain ⟨o⟩ := hconnected.nonempty
  obtain ⟨R,hR⟩ := G.z76 hconnected o hS
  refine ⟨R+R,?_⟩
  intro u v
  obtain ⟨z,hz,φ,hφ⟩ := hcover u
  obtain ⟨w,hw,ψ,hψ⟩ := hcover v
  refine ⟨Aut.trans G (Aut.symm G φ) ψ,?_⟩
  change ψ.vertex (φ.vertex.symm u) ∈ G.z5 v (R+R)
  rw [← hφ,Equiv.symm_apply_apply,← hψ,Aut.vertexBall_mem]
  exact G.vertexBall_add ((G.z330).mp (hR hw)) R (hR hz)
lemma z288 (hlocal : G.LocallyFinite) (o : V) (n : ℕ) :
    0 < (G.z5 o n).ncard :=
  (Set.ncard_pos (G.z19 hlocal o n)).mpr ⟨o,G.z45 o n⟩
lemma z289 (hquasi : G.QuasiTransitive)
    (n : ℕ) : ∃ M : ℕ, 1≤M ∧ ∀ v, (G.z5 v n).ncard ≤ M := by
  obtain ⟨M,hM⟩ := G.z562 hquasi n
  exact ⟨M+1,by omega,fun v => (hM v).trans (Nat.le_succ M)⟩
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
def heightCut (π : V → ℤ) (t : ℤ) : Set E := G.cutEdges {v | t < π v}
lemma z203 (π : V → ℤ) (hπ : ∀ t, (π ⁻¹' {t}).Finite)
    (a b : ℤ) : (π ⁻¹' Set.Icc a b).Finite := by
  have hh := (Set.finite_Icc a b).biUnion (fun t _ => hπ t)
  convert hh using 1
  ext v
  simp
lemma z438 (hlocal : G.LocallyFinite) (π : V → ℤ)
    (hπ : ∀ t, (π ⁻¹' {t}).Finite) (J : ℕ)
    (hJ : ∀ e x y, G.ends e=s(x,y) → |π x-π y|≤(J:ℤ)) (t : ℤ) :
    (G.heightCut π t).Finite := by
  apply (G.z323 hlocal (z203 π hπ (t-J) t)).subset
  rintro e ⟨x,y,he,hx,hy⟩
  have hxy := (abs_le.mp (hJ e x y he)).1
  refine ⟨x,?_,?_⟩
  · change t-(J:ℤ) ≤ π x ∧ π x ≤ t
    change ¬t<π x at hx
    change t<π y at hy
    omega
  · simp [he]
lemma z359 (π : V → ℤ) (J : ℕ)
    (hJ : ∀ e x y, G.ends e=s(x,y) → |π x-π y|≤(J:ℤ))
    (t u : ℤ) (htu : (J:ℤ) ≤ |t-u|) :
    Disjoint (G.heightCut π t) (G.heightCut π u) := by
  apply Set.disjoint_left.mpr
  rintro e ⟨x,y,he,hx,hy⟩ ⟨a,b,hef,ha,hb⟩
  change ¬t<π x at hx
  change t<π y at hy
  change ¬u<π a at ha
  change u<π b at hb
  have hj := abs_le.mp (hJ e x y he)
  rcases Sym2.eq_iff.mp (he.symm.trans hef) with ⟨hxa,hyb⟩|⟨hxb,hya⟩
  · subst a; subst b
    rcases le_total t u with hl|hl
    · rw [abs_of_nonpos (sub_nonpos.mpr hl)] at htu
      omega
    · rw [abs_of_nonneg (sub_nonneg.mpr hl)] at htu
      omega
  · subst b; subst a
    omega
lemma z526 (π : V → ℤ) (φ : G.Aut) (a : ℤ)
    (hφ : ∀ v, π (φ.vertex v)=π v+a) (t : ℤ) :
    φ.edge '' G.heightCut π t = G.heightCut π (t+a) := by
  ext e
  constructor
  · rintro ⟨f,⟨x,y,hf,hx,hy⟩,rfl⟩
    refine ⟨φ.vertex x,φ.vertex y,?_,?_,?_⟩
    · rw [φ.preserves,hf,Sym2.map_mk]
    · change ¬t+a<π (φ.vertex x)
      rw [hφ]
      change ¬t<π x at hx
      omega
    · change t+a<π (φ.vertex y)
      rw [hφ]
      change t<π y at hy
      omega
  · rintro ⟨x,y,he,hx,hy⟩
    refine ⟨φ.edge.symm e,?_,φ.edge.apply_symm_apply e⟩
    refine ⟨φ.vertex.symm x,φ.vertex.symm y,?_,?_,?_⟩
    · have hh := (Aut.symm G φ).preserves e
      change G.ends (φ.edge.symm e) = s(φ.vertex.symm x,φ.vertex.symm y)
      change G.ends (φ.edge.symm e) = Sym2.map φ.vertex.symm (G.ends e) at hh
      rw [hh,he,Sym2.map_mk]
    · have hh := hφ (φ.vertex.symm x)
      simp only [Equiv.apply_symm_apply] at hh
      change ¬t<π (φ.vertex.symm x)
      change ¬t+a<π x at hx
      omega
    · have hh := hφ (φ.vertex.symm y)
      simp only [Equiv.apply_symm_apply] at hh
      change t<π (φ.vertex.symm y)
      change t+a<π y at hy
      omega
lemma z492 (π : V → ℤ)
    (htrans : ∀ t, ∃ φ : G.Aut, ∀ v, π (φ.vertex v)=π v+t) (t : ℤ) :
    (G.heightCut π t).ncard = (G.heightCut π 0).ncard := by
  obtain ⟨φ,hφ⟩ := htrans t
  have he := G.z526 π φ t hφ 0
  simp only [zero_add] at he
  rw [← he,Set.ncard_image_of_injective _ φ.edge.injective]
lemma z218 (π : V → ℤ) (ω : Set E) (a b : ℤ)
    (ha : Disjoint (G.heightCut π a) ω) (hb : Disjoint (G.heightCut π b) ω)
    (o : V) (hoa : a<π o) (hob : π o≤b) :
    G.cluster ω o ⊆ π ⁻¹' Set.Icc (a+1) b := by
  intro v hv
  constructor
  · by_contra h
    have hva : ¬a<π v := by change ¬a+1≤π v at h; omega
    exact G.z102 {v | a<π v} ω
      (fun e he => Set.disjoint_left.mp ha he) hva hoa hv.symm
  · by_contra h
    have hvb : b<π v := lt_of_not_ge h
    exact G.z102 {v | b<π v} ω
      (fun e he => Set.disjoint_left.mp hb he) (not_lt.mpr hob) hvb hv
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical
namespace CriticalPercolation.z0
variable {E : Type*}
lemma z393 (q : E → unitInterval) :
    law q = Measure.infinitePi (fun e => bitMeasure (q e)) := by
  change Measure.map id _ = _
  exact Measure.map_id
abbrev coordinateSigma (e : E) : MeasurableSpace (Set E) :=
  MeasurableSpace.comap (fun ω : Set E => e ∈ ω) inferInstance
abbrev blockSigma (S : Set E) : MeasurableSpace (Set E) := ⨆ e ∈ S, coordinateSigma e
lemma z177 (e : E) : coordinateSigma e ≤ (Set.instMeasurableSpace : MeasurableSpace (Set E)) :=
  (measurable_set_mem e).comap_le
lemma blockSigma_le (S : Set E) : blockSigma S ≤ (Set.instMeasurableSpace : MeasurableSpace (Set E)) :=
  iSup₂_le fun e _ => z177 e
lemma z86 (q : E → unitInterval) :
    iIndep coordinateSigma (law q) := by
  rw [z393]
  exact iIndepFun_infinitePi (X := fun _ (b : Prop) => b) (fun _ => measurable_id)
lemma z357 (q : E → unitInterval) (S : Set E) :
    Indep (blockSigma S) (blockSigma Sᶜ) (law q) :=
  indep_biSup_compl z177 (z86 q) S
def forceOn (S : Set E) (σ ω : Set E) : Set E := fun e => if e ∈ S then e ∈ σ else e ∈ ω
lemma z77 (S σ : Set E) :
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
theorem z34 (q : E → unitInterval)
    (A : Set (Set E)) (hA : MeasurableSet A)
    (hinvariant : ∀ (S : Set E), S.Finite → ∀ ω,
      forceOn S ∅ ω ∈ A ↔ ω ∈ A) : law q A = 0 ∨ law q A = 1 := by
  let mA : MeasurableSpace (Set E) := MeasurableSpace.generateFrom {A}
  have hmA : mA ≤ (Set.instMeasurableSpace : MeasurableSpace (Set E)) := MeasurableSpace.generateFrom_singleton_le hA
  have hi : ∀ S : Finset E, Indep (blockSigma (S : Set E)) mA (law q) := by
    intro S
    have htail : MeasurableSet[blockSigma (S : Set E)ᶜ] A := by
      have hh := hA.preimage (z77 (S : Set E) ∅)
      have heq : forceOn (S : Set E) ∅ ⁻¹' A = A := by
        ext ω
        exact hinvariant _ S.finite_toSet ω
      rwa [heq] at hh
    exact indep_of_indep_of_le_right (z357 q (S : Set E))
      (MeasurableSpace.generateFrom_singleton_le htail)
  have hd : Directed (· ≤ ·) (fun S : Finset E => blockSigma (S : Set E)) := by
    intro S T
    refine ⟨S ∪ T, ?_, ?_⟩ <;> apply iSup₂_le <;> intro e he
    · exact le_iSup_of_le e (le_iSup_of_le (Finset.mem_union_left T he) le_rfl)
    · exact le_iSup_of_le e (le_iSup_of_le (Finset.mem_union_right S he) le_rfl)
  have hall : (⨆ S : Finset E, blockSigma (S : Set E)) =
      (Set.instMeasurableSpace : MeasurableSpace (Set E)) := by
    apply le_antisymm (iSup_le fun S => blockSigma_le _)
    change (⨆ e, coordinateSigma e) ≤ _
    apply iSup_le
    intro e
    exact le_iSup_of_le {e} (le_iSup_of_le e
      (le_iSup_of_le (Finset.mem_singleton_self e) le_rfl))
  have h := indep_iSup_of_directed_le hi (fun S => blockSigma_le (S : Set E)) hmA hd
  rw [hall] at h
  exact measure_eq_zero_or_one_of_indepSet_self
    (h.indepSet_of_measurableSet hA (MeasurableSpace.measurableSet_generateFrom (by simp)))
end CriticalPercolation.z0
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
namespace CriticalPercolation.z0
variable {E : Type*}
lemma law_coordinate (q : E → unitInterval) (e : E) (b : Prop) :
    law q {ω : Set E | (e ∈ ω) = b} = bitMeasure (q e) {b} := by
  rw [z393]
  have h := congrArg (fun μ : Measure Prop => μ {b})
    (Measure.infinitePi_map_eval (fun e => bitMeasure (q e)) e)
  rw [Measure.map_apply (measurable_pi_apply e) (MeasurableSet.singleton b)] at h
  exact h
lemma z246 (q : E → unitInterval) (e : E) (σ : Set E)
    (hb : bitMeasure (q e) {e ∈ σ} ≠ 0)
    (A : Set (Set E)) (hA : MeasurableSet A) (hnull : law q A = 0) :
    law q (forceOn {e} σ ⁻¹' A) = 0 := by
  let B := forceOn {e} σ ⁻¹' A
  let C := {ω : Set E | (e ∈ ω) = (e ∈ σ)}
  have hmC : MeasurableSet[blockSigma {e}] C := by
    have hc : MeasurableSet[coordinateSigma e] C :=
      ⟨{e ∈ σ}, MeasurableSet.singleton _, rfl⟩
    exact (le_iSup_of_le e (le_iSup_of_le (Set.mem_singleton e) le_rfl) :
      coordinateSigma e ≤ blockSigma {e}) _ hc
  have hmB : MeasurableSet[blockSigma ({e} : Set E)ᶜ] B :=
    hA.preimage (z77 {e} σ)
  have hmul := ((z357 q {e}).indepSet_of_measurableSet hmC hmB).measure_inter_eq_mul
  have hsub : C ∩ B ⊆ A := by
    intro ω hω
    have heq : forceOn {e} σ ω = ω := by
      ext f
      change (if f ∈ ({e} : Set E) then f ∈ σ else f ∈ ω) ↔ f ∈ ω
      by_cases hf : f = e
      · subst f
        simpa only [Set.mem_singleton_iff, ↓reduceIte] using (Iff.of_eq hω.1.symm)
      · simp only [Set.mem_singleton_iff, if_neg hf]
    have hh : forceOn {e} σ ω ∈ A := hω.2
    rwa [heq] at hh
  have hz : law q (C ∩ B) = 0 := measure_mono_null hsub hnull
  rw [hz, law_coordinate] at hmul
  exact (mul_eq_zero.mp hmul.symm).resolve_left hb
lemma z415 (p : unitInterval) (hp : (0:ℝ) < p) :
    bitMeasure p {True} ≠ 0 := by
  have hh := z46 p True
  simp only [z28, ↓reduceIte] at hh
  intro hz
  have : (bitMeasure p).real {True} = 0 := by simp only [measureReal_def,hz,ENNReal.toReal_zero]
  rw [hh] at this
  exact (ne_of_gt hp) this
lemma z512 (q : E → unitInterval) (hq : ∀ e, (0:ℝ) < q e)
    (e : E) (A : Set (Set E)) (hA : MeasurableSet A) (hnull : law q A = 0) :
    law q ((fun ω => insert e ω) ⁻¹' A) = 0 := by
  have hh := z246 q e Set.univ (z415 (q e) (hq e))
    A hA hnull
  have heq : forceOn {e} Set.univ = (fun ω : Set E => insert e ω) := by
    funext ω
    ext f
    change (if f ∈ ({e} : Set E) then True else f ∈ ω) ↔ (f = e ∨ f ∈ ω)
    simp only [Set.mem_singleton_iff]
    split_ifs <;> tauto
  rwa [heq] at hh
lemma z482 (S : Set E) : Measurable (fun ω : Set E => S ∪ ω) :=
  measurable_pi_lambda _ (fun edge => measurable_const.or (measurable_set_mem edge))
lemma z322 (q : E → unitInterval) (hq : ∀ e, (0:ℝ) < q e)
    (S : Set E) (hS : S.Finite) (A : Set (Set E)) (hA : MeasurableSet A)
    (hnull : law q A = 0) : law q ((fun ω => S ∪ ω) ⁻¹' A) = 0 := by
  induction S,hS using Set.Finite.induction_on generalizing A with
  | empty =>
    have hh : (fun ω : Set E => (∅ : Set E) ∪ ω) = id := funext (fun _ => Set.empty_union _)
    rw [hh,Set.preimage_id_eq]
    exact hnull
  | @insert e S he hS ih =>
    have hi := z512 q hq e A hA hnull
    have hm : Measurable (fun ω : Set E => insert e ω) := by
      simpa only [Set.singleton_union] using z482 ({e} : Set E)
    have hh := ih ((fun ω => insert e ω) ⁻¹' A) (hA.preimage hm) hi
    simpa only [Set.preimage_preimage,Function.comp_def,Set.insert_union] using hh
end CriticalPercolation.z0
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
namespace CriticalPercolation.z0
variable {E I : Type*}
lemma z604 {S T : Set E} (h : S ⊆ T) : blockSigma S ≤ blockSigma T := by
  apply iSup₂_le
  intro e he
  exact le_iSup_of_le e (le_iSup_of_le (h he) le_rfl)
lemma z292 (q : E → unitInterval) (S T : Set E)
    (h : Disjoint S T) : Indep (blockSigma S) (blockSigma T) (law q) :=
  indep_iSup_of_disjoint z177 (z86 q) h
theorem z373 (q : E → unitInterval) (S : I → Set E)
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
      exact z604 (fun e he => Set.mem_iUnion₂.mpr ⟨j,hj,he⟩)
    have hm : MeasurableSet[blockSigma T] (⋂ j ∈ t, f j) := by
      apply MeasurableSet.biInter t.finite_toSet.countable
      intro j hjt
      exact hj j hjt _ (hf j (Finset.mem_insert_of_mem hjt))
    have hdis : Disjoint (S i) T := by
      apply Set.disjoint_left.mpr
      intro e hei heT
      obtain ⟨j,hjt,hje⟩ := Set.mem_iUnion₂.mp heT
      exact Set.disjoint_left.mp (hS (by intro h; subst j; exact hi hjt)) hei hje
    have hmuli := ((z292 q (S i) T hdis).indepSet_of_measurableSet
      (hf i (Finset.mem_insert_self i t)) hm).measure_inter_eq_mul
    rw [Finset.set_biInter_insert,Finset.prod_insert hi,hmuli]
    rw [ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]
lemma z145 (q : E → unitInterval) (S : I → Set E)
    (hS : Pairwise (fun i j => Disjoint (S i) (S j))) (A : I → Set (Set E))
    (hA : ∀ i, MeasurableSet[blockSigma (S i)] (A i)) : iIndepSet A (law q) :=
  (z373 q S hS).iIndepSets'.iIndepSet_of_mem hA
    (fun i => blockSigma_le (S i) _ (hA i))
def closedBlock (S : Set E) : Set (Set E) := {ω | Disjoint S ω}
lemma z44 (e : E) :
    MeasurableSet[coordinateSigma e] {ω : Set E | e ∉ ω} := by
  refine ⟨{False},MeasurableSet.singleton _,?_⟩
  ext ω
  simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_ofPred_eq]
  constructor
  · intro h hp
    exact Eq.mp h hp
  · intro h
    exact propext (iff_false_intro h)
lemma z353 (S : Set E) (hS : S.Countable) :
    MeasurableSet[blockSigma S] (closedBlock S) := by
  have heq : closedBlock S = ⋂ e ∈ S, {ω : Set E | e ∉ ω} := by
    ext ω
    simp only [closedBlock,Set.mem_ofPred_eq,Set.mem_iInter,Set.disjoint_left]
  rw [heq]
  apply MeasurableSet.biInter hS
  intro e he
  exact (le_iSup_of_le e (le_iSup_of_le he le_rfl) : coordinateSigma e ≤ blockSigma S)
    _ (z44 e)
lemma z609 (q : E → unitInterval) (S : Set E) (hS : S.Finite) :
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
  rw [heq,(z86 q).meas_biInter]
  · exact Finset.prod_congr rfl (fun e _ => law_coordinate q e False)
  · intro e _
    exact ⟨{False},MeasurableSet.singleton _,rfl⟩
lemma z478 (p : unitInterval) (S : Set E) (hS : S.Finite) :
    law (fun _ : E => p) (closedBlock S) =
      (bitMeasure p {False}) ^ S.ncard := by
  rw [z609 (fun _ : E => p) S hS,Finset.prod_const]
  rw [Set.ncard_eq_toFinset_card S hS]
end CriticalPercolation.z0
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal
namespace CriticalPercolation.z0
variable {E : Type*}
lemma z390 (p : unitInterval) (hp : (p:ℝ)<1) :
    bitMeasure p {False} ≠ 0 := by
  have hh := z46 p False
  simp only [z28,↓reduceIte] at hh
  intro hz
  have : (bitMeasure p).real {False}=0 := by simp only [measureReal_def,hz,ENNReal.toReal_zero]
  linarith
theorem z131 (p : unitInterval) (hp : (p:ℝ)<1)
    (S : ℕ → Set E) (hS : ∀ n, (S n).Finite)
    (hdis : Pairwise (fun n m => Disjoint (S n) (S m))) (N : ℕ)
    (hN : ∀ n, (S n).ncard=N) :
    ∀ᵐ ω ∂law (fun _ : E => p), ∃ᶠ n in atTop, ω ∈ closedBlock (S n) := by
  let A := fun n => closedBlock (S n)
  have hm' : ∀ n, MeasurableSet[blockSigma (S n)] (A n) :=
    fun n => z353 (S n) (hS n).countable
  have hm : ∀ n, MeasurableSet (A n) := fun n => blockSigma_le (S n) _ (hm' n)
  have hi := z145 (fun _ : E => p) S hdis A hm'
  have hprob : ∀ n, law (fun _ : E => p) (A n) = (bitMeasure p {False})^N := by
    intro n
    rw [z478 p (S n) (hS n),hN]
  have hsum : (∑' n, law (fun _ : E => p) (A n)) = ∞ := by
    simp_rw [hprob]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (pow_ne_zero _ (z390 p hp))
  have hlim := measure_limsup_eq_one hm hi hsum
  have hl : ∀ᵐ ω ∂law (fun _ : E => p), ω ∈ limsup A atTop :=
    (mem_ae_iff_prob_eq_one (MeasurableSet.measurableSet_limsup hm)).mpr hlim
  exact hl.mono (fun _ h => Filter.mem_limsup_iff_frequently_mem.mp h)
end CriticalPercolation.z0
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
lemma z223 (J n m : ℕ) (hnm : n≠m) :
    (J:ℤ) ≤ |(n:ℤ)*(J+1)-(m:ℤ)*(J+1)| := by
  have hne : (n:ℤ)-(m:ℤ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hnm)
  have hpos : 1 ≤ |(n:ℤ)-(m:ℤ)| := Int.add_one_le_iff.mpr (abs_pos.mpr hne)
  rw [← sub_mul,abs_mul,abs_of_nonneg (by omega : (0:ℤ)≤(J:ℤ)+1)]
  nlinarith [Int.natCast_nonneg J]
theorem z111 (hlocal : G.LocallyFinite)
    (π : V → ℤ) (hπ : ∀ t, (π ⁻¹' {t}).Finite) (J : ℕ)
    (hJ : ∀ e x y, G.ends e=s(x,y) → |π x-π y|≤(J:ℤ))
    (htrans : ∀ t, ∃ φ : G.Aut, ∀ v, π (φ.vertex v)=π v+t)
    (p : unitInterval) (hp : (p:ℝ)<1) : G.law p G.z12 = 0 := by
  let Cpos : ℕ → Set E := fun n => G.heightCut π ((n:ℤ)*(J+1))
  let Cneg : ℕ → Set E := fun n => G.heightCut π (-((n:ℤ)*(J+1)))
  have hpdis : Pairwise (fun n m => Disjoint (Cpos n) (Cpos m)) := by
    intro n m hnm
    exact G.z359 π J hJ _ _ (z223 J n m hnm)
  have hmdis : Pairwise (fun n m => Disjoint (Cneg n) (Cneg m)) := by
    intro n m hnm
    apply G.z359 π J hJ
    rw [neg_sub_neg,abs_sub_comm]
    exact z223 J n m hnm
  have hplus := z0.z131 p hp Cpos
    (fun n => G.z438 hlocal π hπ J hJ _) hpdis (G.heightCut π 0).ncard
    (fun n => G.z492 π htrans _)
  have hminus := z0.z131 p hp Cneg
    (fun n => G.z438 hlocal π hπ J hJ _) hmdis (G.heightCut π 0).ncard
    (fun n => G.z492 π htrans _)
  rw [z0.law_const] at hplus hminus
  have hno : ∀ᵐ ω ∂G.law p, ω ∉ G.z12 := by
    filter_upwards [hplus,hminus] with ω hpω hmω
    rintro ⟨o,ho⟩
    obtain ⟨n,hn,hncut⟩ := Filter.frequently_atTop.mp hpω ((π o).natAbs+1)
    obtain ⟨m,hm,hmcut⟩ := Filter.frequently_atTop.mp hmω ((π o).natAbs+1)
    have hno : π o ≤ (n:ℤ)*(J+1) := by
      have habs : π o ≤ ((π o).natAbs : ℤ) := Int.le_natAbs
      have hh : (π o).natAbs+1 ≤ (n:ℤ) := by exact_mod_cast hn
      have hprod : (n:ℤ) ≤ (n:ℤ)*(J+1) := by nlinarith [Int.natCast_nonneg n,Int.natCast_nonneg J]
      omega
    have hmo : -((m:ℤ)*(J+1)) < π o := by
      have habs : -((π o).natAbs : ℤ) ≤ π o := by
        simpa only [Int.natCast_natAbs] using neg_abs_le (π o)
      have hh : (π o).natAbs+1 ≤ (m:ℤ) := by exact_mod_cast hm
      have hprod : (m:ℤ) ≤ (m:ℤ)*(J+1) := by nlinarith [Int.natCast_nonneg m,Int.natCast_nonneg J]
      omega
    exact ho ((z203 π hπ _ _).subset
      (G.z218 π ω _ _ hmcut hncut o hmo hno))
  rw [ae_iff] at hno
  simpa only [not_not,Set.ofPred_mem_eq] using hno
theorem z151 (hlocal : G.LocallyFinite)
    (π : V → ℤ) (hπ : ∀ t, (π ⁻¹' {t}).Finite) (J : ℕ)
    (hJ : ∀ e x y, G.ends e=s(x,y) → |π x-π y|≤(J:ℤ))
    (htrans : ∀ t, ∃ φ : G.Aut, ∀ v, π (φ.vertex v)=π v+t) :
    G.z3=1 := by
  apply le_antisymm le_top
  apply le_sInf
  intro p hp
  by_contra h
  have hlt : (p:ℝ)<1 := lt_of_not_ge h
  have hz := G.z111 hlocal π hπ J hJ htrans p hlt
  exact (ne_of_gt hp) hz
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set
open scoped Classical
namespace CriticalPercolation.EquivariantCoordinates
variable {Λ N T V : Type*} [Group Λ] [Group N] [Group T] [MulAction Λ V]
theorem z96 (ρ : Λ →* N) (L : Subgroup Λ)
    (hfin : (L.map ρ : Set N).Finite)
    (hker : ∀ v : V, (MulAction.orbit ρ.ker v).Finite) (v : V) :
    (MulAction.orbit L v).Finite := by
  have hex : ∀ a : L.map ρ, ∃ g : Λ, g∈L ∧ ρ g=a := by
    intro a
    exact a.property
  choose r hr using hex
  let : Finite (L.map ρ) := hfin.to_subtype
  have hset : (⋃ a : L.map ρ, (fun x : V => r a • x) '' MulAction.orbit ρ.ker v).Finite :=
    Set.finite_iUnion (fun a => (hker v).image _)
  apply hset.subset
  rintro w ⟨g,hg⟩
  change (g : Λ) • v=w at hg
  let a : L.map ρ := ⟨ρ g,⟨g,g.property,rfl⟩⟩
  have hk : (r a)⁻¹*(g : Λ)∈ρ.ker := by
    change ρ ((r a)⁻¹*(g : Λ))=1
    rw [map_mul,map_inv,(hr a).2]
    exact inv_mul_cancel (ρ g)
  apply Set.mem_iUnion.mpr
  refine ⟨a,((r a)⁻¹*(g : Λ)) • v,?_,?_⟩
  · exact ⟨⟨(r a)⁻¹*(g : Λ),hk⟩,rfl⟩
  · change r a • (((r a)⁻¹*(g : Λ)) • v)=w
    rw [← mul_smul,mul_inv_cancel_left,hg]
lemma z211 (ρ : Λ →* N) (φ : N →* T)
    (hφ : (φ.ker : Set N).Finite)
    (hker : ∀ v : V, (MulAction.orbit ρ.ker v).Finite) (v : V) :
    (MulAction.orbit (φ.comp ρ).ker v).Finite := by
  apply z96 ρ _ _ hker v
  apply hφ.subset
  rintro n ⟨g,hg,rfl⟩
  exact hg
lemma z144 (ρ : Λ →* N) [Finite N]
    (hker : ∀ v : V, (MulAction.orbit ρ.ker v).Finite)
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s) :
    (Set.univ : Set V).Finite := by
  have hf : ∀ s : V, (MulAction.orbit Λ s).Finite := by
    intro s
    have hh := z96 ρ ⊤ (Set.toFinite _) hker s
    apply hh.subset
    rintro v ⟨g,hg⟩
    exact ⟨⟨g,Subgroup.mem_top g⟩,hg⟩
  apply (hS.biUnion fun s _ => hf s).subset
  intro v _
  obtain ⟨s,hs,hvs⟩ := hcover v
  exact Set.mem_iUnion₂.mpr ⟨s,hs,hvs⟩
end CriticalPercolation.EquivariantCoordinates
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set
open scoped Classical
namespace CriticalPercolation.z2
variable {V E Λ : Type*} (G : z2 V E) [Group Λ] [MulAction Λ V] [MulAction Λ E]
def PreservesEnds : Prop :=
  ∀ (g : Λ) (e : E), G.ends (g • e)=Sym2.map (fun v : V => g • v) (G.ends e)
def smulAut (h : G.PreservesEnds (Λ := Λ)) (g : Λ) : G.Aut where
  vertex := MulAction.toPerm g
  edge := MulAction.toPerm g
  preserves := h g
lemma z344 (h : G.PreservesEnds (Λ := Λ))
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s) :
    G.QuasiTransitive := by
  refine ⟨S,hS,?_⟩
  intro v
  obtain ⟨s,hs,g,hg⟩ := hcover v
  exact ⟨s,hs,G.smulAut h g,hg⟩
lemma z152 {A : Type*} [NormedAddCommGroup A]
    (hl : G.LocallyFinite) (h : G.PreservesEnds (Λ := Λ))
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (a : Λ → A) (π : V → A) (hπ : ∀ g v, π (g • v)=a g+π v) :
    ∃ D : ℝ, 0≤D ∧ ∀ e x y, G.ends e=s(x,y) → ‖π x-π y‖≤D := by
  let F : Set (V×V) := ⋃ s∈S, (fun w => (s,w)) '' G.z7.neighborSet s
  have hF : F.Finite := hS.biUnion fun s _ => (G.z420 hl s).image _
  obtain ⟨D,hD⟩ := (hF.image (fun z => ‖π z.1-π z.2‖)).bddAbove
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro e x y he
  by_cases hxy : x=y
  · subst y
    simpa only [sub_self,norm_zero] using le_max_right D 0
  · have hadj : G.z7.Adj x y := (SimpleGraph.fromEdgeSet_adj _).mpr
      ⟨⟨e,Set.mem_univ _,he⟩,hxy⟩
    obtain ⟨s,hs,g,hgx⟩ := hcover x
    change g • s=x at hgx
    let w := g⁻¹ • y
    have hgw : g • w=y := smul_inv_smul g y
    have hsw : G.z7.Adj s w := by
      apply (Aut.fullGraph_adj G (G.smulAut h g) s w).mp
      change G.z7.Adj (g • s) (g • w)
      rwa [hgx,hgw]
    have hf : (s,w)∈F := Set.mem_iUnion₂.mpr ⟨s,hs,w,hsw,rfl⟩
    have hd : ‖π s-π w‖≤D := hD ⟨(s,w),hf,rfl⟩
    have hdiff : π x-π y=π s-π w := by
      rw [← hgx,← hgw,hπ,hπ]
      abel
    rw [hdiff]
    exact hd.trans (le_max_left _ _)
theorem z205 {N : Type*} [Group N]
    (hl : G.LocallyFinite) (h : G.PreservesEnds (Λ := Λ))
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (ρ : Λ →* N) (hρ : Function.Surjective ρ)
    (φ : N →* Multiplicative ℤ) (hφ : Function.Surjective φ)
    (hf : (φ.ker : Set N).Finite)
    (hker : ∀ v : V, (MulAction.orbit ρ.ker v).Finite)
    (hstab : ∀ v : V, ((MulAction.stabilizer Λ v).map ρ : Set N).Finite) :
    G.z3=1 := by
  let a := φ.comp ρ
  obtain ⟨π,hπ⟩ := EquivariantCoordinates.z345 a
    (EquivariantCoordinates.z397 ρ φ hstab)
  let πa : V → ℤ := fun v => (π v).toAdd
  have hπa : ∀ (g : Λ) (v : V), πa (g • v)=(a g).toAdd+πa v := by
    intro g v
    exact congrArg Multiplicative.toAdd (hπ g v)
  have hfib : ∀ t : ℤ, (πa ⁻¹' {t}).Finite := by
    intro t
    exact EquivariantCoordinates.finite_fibers a π hπ
      (EquivariantCoordinates.z211 ρ φ hf hker)
      S hS hcover (Multiplicative.ofAdd t)
  have htrans : ∀ t : ℤ, ∃ ψ : G.Aut, ∀ v, πa (ψ.vertex v)=πa v+t := by
    intro t
    obtain ⟨g,hg⟩ := hφ.comp hρ (Multiplicative.ofAdd t)
    refine ⟨G.smulAut h g,?_⟩
    intro v
    change πa (g • v)=πa v+t
    rw [hπa]
    rw [show a g=Multiplicative.ofAdd t from hg]
    exact add_comm _ _
  obtain ⟨D,hD,hjump⟩ := G.z152 hl h S hS hcover
    (fun g => (a g).toAdd) πa hπa
  obtain ⟨J,hJ⟩ := exists_nat_gt D
  apply G.z151 hl πa hfib J _ htrans
  intro e x y he
  have hh := (hjump e x y he).trans hJ.le
  rw [Int.norm_eq_abs,← Int.cast_abs] at hh
  exact_mod_cast hh
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical
namespace CriticalPercolation.z2
variable {V E Λ : Type*} (G : z2 V E) [Group Λ] [MulAction Λ V]
variable (α : Λ → G.Aut) (hα : ∀ g x, (α g).vertex x=g • x)
include α hα in
lemma z541 (hc : G.z7.Connected) (S : Set V) (hS : S.Finite)
    (hcover : ∀ x, ∃ s∈S, ∃ g : Λ, g • s=x) (o : V) :
    ∃ c : ℕ, ∀ y, ∃ g : Λ, g • o∈G.z5 y c := by
  obtain ⟨c,hc'⟩ := G.z76 hc o hS
  refine ⟨c,?_⟩
  intro y
  obtain ⟨s,hs,g,rfl⟩ := hcover y
  refine ⟨g,?_⟩
  rw [←hα g o,←hα g s,Aut.vertexBall_mem]
  exact G.z330.mp (hc' hs)
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
namespace CriticalPercolation.z8
variable {E B : Type*} [Fintype E] [Fintype B]
lemma z47 (f : (E → B) → ℝ) :
    Continuous (fun w : E → B → ℝ => expect w f) := by
  classical
  unfold expect density
  apply continuous_finsetSum
  intro ω _
  apply Continuous.mul _ continuous_const
  apply continuous_finsetProd
  intro e _
  exact (continuous_apply (ω e)).comp (continuous_apply e)
end CriticalPercolation.z8
end
end
end OAI
end
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
lemma z516 (A T U : Set V) : 0 ≤ jointHitValue A T U := by
  unfold jointHitValue; positivity
lemma z450 (A T : Set V) : Monotone (jointHitValue A T) := by
  intro U W hUW
  unfold jointHitValue
  split_ifs with hU hW hW
  · exact le_rfl
  · exact (hW ⟨hU.1.mono (Set.inter_subset_inter_left A hUW),
      hU.2.mono (Set.inter_subset_inter_left T hUW)⟩).elim
  · norm_num
  · exact le_rfl
lemma z126 {A T U : Set V} (hA : (U ∩ A).Nonempty) :
    jointHitValue A T U = hitValue T U := by simp [jointHitValue, hitValue, hA]
lemma z272 (H : SimpleGraph V) (s : V) (A : Set V) :
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
lemma z84 (H : SimpleGraph V) (s : V) : roots H {s} = component H s := by
  ext v
  simp [roots, component]
lemma z530 {H : SimpleGraph V} {s t : V}
    (h : t ∈ component H s) : component H t = component H s := by
  ext v
  exact ⟨fun hv => h.trans hv, fun hv => h.symm.trans hv⟩
lemma z32 (H : SimpleGraph V) (S : Set V) (s : V) :
    s ∉ roots H S ↔ Disjoint (component H s) S := by
  rw [Set.disjoint_left]
  constructor
  · intro hs t ht hS
    exact hs ⟨t, hS, ht.symm⟩
  · intro hd ⟨t, ht, hts⟩
    exact hd hts.symm ht
lemma z108 (H : SimpleGraph V) (s t : V)
    (h : t ∉ component H s) :
    component (delete H (component H s)) t = component H t := by
  simpa only [z84] using
    (z64 H {s} t (by simpa only [z84] using h))
lemma z200 (H : SimpleGraph V) (S : Set V) (s : V)
    (h : s ∉ roots H S) : roots (delete H (component H s)) S = roots H S := by
  ext v
  constructor
  · intro hv
    exact roots_mono (delete_le H _) S hv
  · rintro ⟨t, ht, htv⟩
    refine ⟨t, ht, ?_⟩
    have hts : t ∉ component H s := fun hg => h ⟨t, ht, hg.symm⟩
    change v ∈ component (delete H (component H s)) t
    rw [z108 H s t hts]
    exact htv
lemma delete_empty (H : SimpleGraph V) : delete H ∅ = H := by
  ext v w
  simp only [delete, Set.mem_empty_iff_false, not_false_eq_true, and_true]
end CriticalPercolation.ClusterDeletion
end
end
end OAI
end
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
lemma z57 {x : Fin n → V} (hx : Function.Injective x) (k : Fin n) :
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
lemma z576 (H : SimpleGraph V) (x : Fin n → V) {k i : Fin n} (hik : i < k) :
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
lemma z568 (H : SimpleGraph V) (x : Fin n → V)
    (F : Set V → ℝ) (i : Fin n) :
    F (component H (x i)) = ∑ k, select H x k i * F (component H (x k)) := by
  obtain ⟨k, hk, hki⟩ := exists_first H x i
  rw [select_mul_sum H x i _ hk hki, z530 hki]
lemma z302 (H : SimpleGraph V) (x : Fin n → V)
    {j i : Fin n} (hj : first H x j) (hji : x i ∈ component H (x j)) (k : Fin n) :
    x i ∉ roots H (earlier x k) ↔ k ≤ j := by
  constructor
  · intro hi
    by_contra! hjk
    exact hi ⟨x j, ⟨j, hjk, rfl⟩, hji⟩
  · rintro hkj ⟨v, ⟨l, hlk, rfl⟩, hli⟩
    exact hj ⟨x l, ⟨l, hlk.trans_le hkj, rfl⟩, hli.trans hji.symm⟩
lemma z578 (H : SimpleGraph V) (x : Fin n → V) (k i : Fin n) :
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
  simp only [z302 H x hj hji k]
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
section
namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
open Set
namespace CriticalPercolation.z2
open CriticalPercolation.z8 CriticalPercolation.ClusterDeletion
variable {V E : Type*} [Fintype V] [Fintype E] (G : z2 V E)
lemma z42 (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S U : Set V) (F : Set V → SimpleGraph V → ℝ) :
    expect w (fun ω =>
      F (roots (delete (G.z1 ω) U) S)
        (delete (G.z1 ω) (roots (delete (G.z1 ω) U) S))) =
    expect w (fun ω => expect w (fun ω' =>
      F (roots (delete (G.z1 ω) U) S)
        (delete (G.z1 ω') (roots (delete (G.z1 ω) U) S)))) := by
  classical
  refine z608 w hw
    (fun ω => roots (delete (G.z1 ω) U) S) G.z9
    (G.z247 S U)
    (fun W ω => F W (delete (G.z1 ω) W)) ?_
  intro W ω ω' hω
  exact congrArg (F W) (G.z337 W hω)
noncomputable def expectedCluster (w : E → Prop → ℝ) (s : V)
    (F : Set V → ℝ) (W : Set V) : ℝ :=
  expect w (fun ω => F (component (delete (G.z1 ω) W) s))
noncomputable def expectedResidual (w : E → Prop → ℝ) (S : Set V) (s : V)
    (F : Set V → ℝ) (U : Set V) : ℝ := by
  classical
  exact expect w (fun ω =>
    if s ∉ roots (delete (G.z1 ω) U) S then
      G.expectedCluster w s F (roots (delete (G.z1 ω) U) S) -
      G.expectedCluster w s F (roots (delete (G.z1 ω) U) S ∪ U)
    else 0)
lemma z150 (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (F : Set V → ℝ) (U : Set V) :
    G.expectedResidual w S s F U =
      expect w (fun ω => residual (G.z1 ω) S s F U) := by
  classical
  have h := G.z42 w hw S U
    (fun W H => if s ∉ W then F (component H s) - F (component (delete H U) s) else 0)
  have hu : ∀ H W, delete (delete H W) U = delete H (W ∪ U) := by
    intro H W
    rw [delete_delete, Set.union_comm]
  simp_rw [hu] at h
  change _ = expect w (fun ω => if s ∉ roots (delete (G.z1 ω) U) S then
    F (component (delete (G.z1 ω) (roots (delete (G.z1 ω) U) S)) s) -
    F (component (delete (G.z1 ω) (roots (delete (G.z1 ω) U) S ∪ U)) s)
    else 0)
  rw [h]
  unfold expectedResidual
  congr 1
  funext ω
  split_ifs
  · rw [expect_const w hw]
  · rw [expect_sub]
    rfl
lemma z405 (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (S : Set V) (s : V) {F : Set V → ℝ} (hF : Monotone F) (U : Set V) :
    0 ≤ G.expectedResidual w S s F U := by
  rw [z150 G w hw, ← expect_const w hw 0]
  exact expect_mono hpos fun ω => z490 (G.z1 ω) S s hF U
lemma z362 (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (S : Set V) (s : V) {F : Set V → ℝ} (hF : Monotone F) :
    Monotone (G.expectedResidual w S s F) := by
  intro U U' hUU'
  rw [z150 G w hw, z150 G w hw]
  exact expect_mono hpos fun ω => z571 (G.z1 ω) S s hF hUU'
end CriticalPercolation.z2
open scoped BigOperators
end
end
end OAI
end
section
namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
namespace CriticalPercolation.z8
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
end CriticalPercolation.z8
namespace CriticalPercolation.z8
variable {E A : Type*} [Fintype E] [Fintype A]
lemma z25 (w : E → A → ℝ) (c : ℝ) (f : (E → A) → ℝ) :
    expect w (fun ω => c * f ω) = c * expect w f := by
  simp only [mul_comm c]
  exact z146 w f c
end CriticalPercolation.z8
end
end
end OAI
end
section
namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CriticalPercolation.z2
open CriticalPercolation.z8 CriticalPercolation.ClusterDeletion
variable {V E : Type*} [Fintype V] [Fintype E] (G : z2 V E)
open scoped Classical
noncomputable def clusterUpdate (w : E → Prop → ℝ) (S : Set V) (s : V)
    (F : Set V → ℝ) (U : Set V) : ℝ :=
  expect w (fun ω => G.expectedCluster w s F (roots (delete (G.z1 ω) U) S))
omit [Fintype V] in
lemma z367 (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (s : V) {F : Set V → ℝ} (hF : Monotone F) :
    Antitone (G.expectedCluster w s F) := by
  intro U U' hU
  exact expect_mono hpos fun ω => hF (component_mono (z83 _ hU) s)
omit [Fintype V] in
lemma z434 (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (S : Set V) (s : V) {F : Set V → ℝ} (hF : Monotone F) :
    Monotone (G.clusterUpdate w S s F) := by
  intro U U' hU
  exact expect_mono hpos fun ω => G.z367 w hpos s hF
    (roots_mono (z83 _ hU) S)
omit [Fintype V] in
lemma z513 (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (S : Set V) (s : V) {F : Set V → ℝ} (hF : ∀ U, 0 ≤ F U) (U : Set V) :
    0 ≤ G.clusterUpdate w S s F U :=
  expect_nonneg hpos fun _ => expect_nonneg hpos fun _ => hF _
noncomputable def avoidedAverage (w : E → Prop → ℝ) (S : Set V) (s : V)
    (F : Set V → ℝ) : ℝ := by
  classical
  exact expect w (fun ω => if s ∉ roots (G.z1 ω) S then
    F (component (G.z1 ω) s) else 0)
lemma z197 (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (F g : Set V → ℝ) :
    (expect w (fun ω => if s ∉ roots (G.z1 ω) S then
      g (component (G.z1 ω) s) * G.expectedCluster w s F (roots (G.z1 ω) S)
      else 0)) =
    G.avoidedAverage w S s (fun U => g U * G.clusterUpdate w S s F U) := by
  classical
  have h := G.z42 w hw {s} ∅
    (fun U H => if Disjoint U S then g U * G.expectedCluster w s F (roots H S) else 0)
  simp only [delete_empty, z84] at h
  have hleft : (fun ω : E → Prop =>
      if Disjoint (component (G.z1 ω) s) S then
        g (component (G.z1 ω) s) * G.expectedCluster w s F
          (roots (delete (G.z1 ω) (component (G.z1 ω) s)) S) else 0) =
      (fun ω => if s ∉ roots (G.z1 ω) S then
        g (component (G.z1 ω) s) * G.expectedCluster w s F
          (roots (G.z1 ω) S) else 0) := by
    funext ω
    rw [← z32]
    split_ifs with hs
    · rfl
    · rw [z200 _ S s hs]
  rw [hleft] at h
  erw [h]
  unfold avoidedAverage
  congr 1
  funext ω
  rw [← z32]
  split_ifs
  · rw [expect_zero]
  · rw [z25]
    rfl
lemma z401 (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (F : Set V → ℝ) :
    G.avoidedAverage w S s F =
      expect w (fun ω => if s ∉ roots (G.z1 ω) S then
        G.expectedCluster w s F (roots (G.z1 ω) S) else 0) := by
  classical
  have h := G.z42 w hw S ∅
    (fun W H => if s ∉ W then F (component H s) else 0)
  simp only [delete_empty] at h
  have hleft : (fun ω : E → Prop => if s ∉ roots (G.z1 ω) S then
      F (component (delete (G.z1 ω) (roots (G.z1 ω) S)) s) else 0) =
      (fun ω => if s ∉ roots (G.z1 ω) S then F (component (G.z1 ω) s) else 0) := by
    funext ω
    split_ifs with hs
    · rfl
    · rw [z64 _ S s hs]
  rw [hleft] at h
  change expect w _ = _
  erw [h]
  congr 1
  funext ω
  split_ifs
  · rw [expect_zero]
  · rfl
lemma z381 (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (F : Set V → ℝ) :
    G.avoidedAverage w S s (G.clusterUpdate w S s F) = G.avoidedAverage w S s F := by
  have h := G.z197 w hw S s F (fun _ => 1)
  simp only [one_mul] at h
  exact h.symm.trans (G.z401 w hw S s F).symm
end CriticalPercolation.z2
end
end
end OAI
end
section
namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CriticalPercolation.z2
open CriticalPercolation.z8 CriticalPercolation.ClusterDeletion
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (G : z2 V E)
lemma z515 (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (F : Set V → ℝ) (U : Set V) :
    G.expectedResidual w S s F U =
      expect w (fun ω => if s ∉ roots (delete (G.z1 ω) U) S then
        G.expectedCluster w s F (roots (delete (G.z1 ω) U) S) -
          F (component (delete (G.z1 ω) U) s) else 0) := by
  have h := G.z42 w hw S U
    (fun W H => if s ∉ W then G.expectedCluster w s F W -
      F (component (delete H U) s) else 0)
  have hdel : ∀ H W, delete (delete H W) U = delete H (W ∪ U) := by
    intro H W
    rw [delete_delete, Set.union_comm]
  simp_rw [hdel] at h
  have hleft : (fun ω : E → Prop => if s ∉ roots (delete (G.z1 ω) U) S then
      G.expectedCluster w s F (roots (delete (G.z1 ω) U) S) -
        F (component (delete (G.z1 ω) (roots (delete (G.z1 ω) U) S ∪ U)) s)
      else 0) =
      (fun ω => if s ∉ roots (delete (G.z1 ω) U) S then
        G.expectedCluster w s F (roots (delete (G.z1 ω) U) S) -
          F (component (delete (G.z1 ω) U) s) else 0) := by
    funext ω
    split_ifs with hs
    · rfl
    · rw [z55 _ S U s hs]
  rw [hleft] at h
  erw [h]
  unfold expectedResidual
  congr 1
  funext ω
  split_ifs
  · rw [expect_zero]
  · rw [expect_sub, expect_const w hw]
    rfl
lemma z432 (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s t : V) (F g : Set V → ℝ) (Q : Set V → Prop)
    (hQ : ∀ U, Q U → Disjoint U S ∧ s ∉ U) :
    (expect w (fun ω => if Q (component (G.z1 ω) t) then
      if s ∉ roots (G.z1 ω) S then
        g (component (G.z1 ω) t) *
          (G.expectedCluster w s F (roots (G.z1 ω) S) -
            F (component (G.z1 ω) s)) else 0 else 0)) =
    expect w (fun ω => if Q (component (G.z1 ω) t) then
      g (component (G.z1 ω) t) *
        G.expectedResidual w S s F (component (G.z1 ω) t) else 0) := by
  have h := G.z42 w hw {t} ∅
    (fun U H => if Q U then if s ∉ roots H S then
      g U * (G.expectedCluster w s F (roots H S) - F (component H s)) else 0 else 0)
  simp only [delete_empty, z84] at h
  have hleft : (fun ω : E → Prop => if Q (component (G.z1 ω) t) then
      if s ∉ roots (delete (G.z1 ω) (component (G.z1 ω) t)) S then
        g (component (G.z1 ω) t) *
          (G.expectedCluster w s F (roots (delete (G.z1 ω) (component (G.z1 ω) t)) S) -
            F (component (delete (G.z1 ω) (component (G.z1 ω) t)) s))
        else 0 else 0) =
      (fun ω => if Q (component (G.z1 ω) t) then
        if s ∉ roots (G.z1 ω) S then
          g (component (G.z1 ω) t) *
            (G.expectedCluster w s F (roots (G.z1 ω) S) - F (component (G.z1 ω) s))
          else 0 else 0) := by
    funext ω
    by_cases hq : Q (component (G.z1 ω) t)
    · simp only [if_pos hq]
      obtain ⟨hd, hs⟩ := hQ _ hq
      rw [z200 _ S t ((z32 _ S t).mpr hd),
        z108 _ t s hs]
    · simp only [if_neg hq]
  rw [hleft] at h
  erw [h]
  congr 1
  funext ω
  by_cases hq : Q (component (G.z1 ω) t)
  · simp only [if_pos hq]
    rw [G.z515 w hw]
    rw [← z25]
    congr 1
    funext ω'
    split_ifs <;> simp
  · simp only [if_neg hq, expect_zero]
end CriticalPercolation.z2
end
end
end OAI
end
section
namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CriticalPercolation.z2
open CriticalPercolation.z8 CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (G : z2 V E)
lemma z546 (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (F b : Set V → ℝ) :
    expect w (fun ω => if s ∉ roots (G.z1 ω) S then
      b (roots (G.z1 ω) S) * (F (component (G.z1 ω) s) -
        G.expectedCluster w s F (roots (G.z1 ω) S)) else 0) = 0 := by
  have h := G.z42 w hw S ∅
    (fun W H => if s ∉ W then b W * (F (component H s) - G.expectedCluster w s F W) else 0)
  simp only [delete_empty] at h
  have hleft : (fun ω : E → Prop => if s ∉ roots (G.z1 ω) S then
      b (roots (G.z1 ω) S) * (F (component (delete (G.z1 ω) (roots (G.z1 ω) S)) s) -
        G.expectedCluster w s F (roots (G.z1 ω) S)) else 0) =
      (fun ω => if s ∉ roots (G.z1 ω) S then
        b (roots (G.z1 ω) S) * (F (component (G.z1 ω) s) -
          G.expectedCluster w s F (roots (G.z1 ω) S)) else 0) := by
    funext ω
    split_ifs with hs
    · rfl
    · rw [z64 _ S s hs]
  rw [hleft] at h
  erw [h]
  have hz : ∀ W : Set V, expect w (fun ω => if s ∉ W then
      b W * (F (component (delete (G.z1 ω) W) s) - G.expectedCluster w s F W)
      else 0) = 0 := by
    intro W
    split_ifs
    · exact expect_zero w
    · rw [z25, expect_sub, expect_const w hw]
      change b W * (G.expectedCluster w s F W - G.expectedCluster w s F W) = 0
      ring
  simp only [hz, expect_zero]
noncomputable def column {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
    (k : Fin n) (F : Set V → ℝ) (i : Fin n) : ℝ :=
  expect w (fun ω => select (G.z1 ω) x k i * F (component (G.z1 ω) (x k)))
omit [Fintype V] in
lemma z388 {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
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
      expect w (fun ω => select (G.z1 ω) x k i *
        G.expectedCluster w (x k) F (roots (G.z1 ω) (earlier x k))) := by
  rw [G.z388]
  rw [← G.z197 w hw]
  congr 1
  funext ω
  simp only [select, first]
  split_ifs <;> simp_all
lemma z475 {n : ℕ} (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (x : Fin n → V) {k l : Fin n} (hkl : k < l) (F : Set V → ℝ) (i : Fin n) :
    G.column w x l (G.expectedResidual w (earlier x k) (x k) F) i =
    expect w (fun ω => if first (G.z1 ω) x k then
      select (G.z1 ω) x l i *
        (G.expectedCluster w (x k) F (roots (G.z1 ω) (earlier x k)) -
          F (component (G.z1 ω) (x k))) else 0) := by
  have h := G.z432 w hw (earlier x k) (x k) (x l) F
    (fun U => if x i ∈ U then 1 else 0) (fun U => Disjoint U (earlier x l))
    (fun U hU => ⟨hU.mono_right (earlier_mono x hkl.le),
      fun hs => (Set.disjoint_left.mp hU) hs ⟨k, hkl, rfl⟩⟩)
  have hc : (fun ω : E → Prop => if Disjoint (component (G.z1 ω) (x l)) (earlier x l) then
      (if x i ∈ component (G.z1 ω) (x l) then 1 else 0) *
        G.expectedResidual w (earlier x k) (x k) F (component (G.z1 ω) (x l)) else 0) =
      (fun ω => select (G.z1 ω) x l i *
        G.expectedResidual w (earlier x k) (x k) F (component (G.z1 ω) (x l))) := by
    funext ω
    simp only [select, first, z32]
    split_ifs <;> simp_all
  rw [hc] at h
  unfold column
  erw [← h]
  congr 1
  funext ω
  simp only [select, first, z32]
  split_ifs <;> simp_all
lemma z519 {n : ℕ} (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (x : Fin n → V) (k : Fin n) (F : Set V → ℝ) (i : Fin n) :
    G.column w x k F i =
      G.column w x k (G.clusterUpdate w (earlier x k) (x k) F) i +
        ∑ l, if k < l then G.column w x l (G.expectedResidual w (earlier x k) (x k) F) i else 0 := by
  have hzero := G.z546 w hw (earlier x k) (x k) F
    (fun W => if x i ∉ W then 1 else 0)
  have hpoint : (fun ω : E → Prop => if x k ∉ roots (G.z1 ω) (earlier x k) then
      (if x i ∉ roots (G.z1 ω) (earlier x k) then (1 : ℝ) else 0) *
        (F (component (G.z1 ω) (x k)) -
          G.expectedCluster w (x k) F (roots (G.z1 ω) (earlier x k))) else 0) =
      (fun ω => select (G.z1 ω) x k i *
        (F (component (G.z1 ω) (x k)) -
          G.expectedCluster w (x k) F (roots (G.z1 ω) (earlier x k))) -
        ∑ l, if k < l then if first (G.z1 ω) x k then
          select (G.z1 ω) x l i *
            (G.expectedCluster w (x k) F (roots (G.z1 ω) (earlier x k)) -
              F (component (G.z1 ω) (x k))) else 0 else 0) := by
    funext ω
    by_cases hk : first (G.z1 ω) x k
    · simp only [show x k ∉ roots (G.z1 ω) (earlier x k) from hk,
        not_false_eq_true, ite_true]
      rw [z578]
      simp only [hk, ite_true]
      have hsum : ∀ a : ℝ,
          (∑ l, if k < l then select (G.z1 ω) x l i * a else 0) =
          (∑ l, if k < l then select (G.z1 ω) x l i else 0) * a := by
        intro a
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l _
        split_ifs <;> simp
      rw [hsum]
      ring
    · have hk' : ¬ (x k ∉ roots (G.z1 ω) (earlier x k)) := hk
      simp [hk', hk, select]
  rw [hpoint] at hzero
  erw [expect_sub, expect_sum] at hzero
  have hlater : (∑ l, expect w (fun ω => if k < l then if first (G.z1 ω) x k then
          select (G.z1 ω) x l i *
            (G.expectedCluster w (x k) F (roots (G.z1 ω) (earlier x k)) -
              F (component (G.z1 ω) (x k))) else 0 else 0)) =
      ∑ l, if k < l then G.column w x l (G.expectedResidual w (earlier x k) (x k) F) i else 0 := by
    apply Finset.sum_congr rfl
    intro l _
    by_cases hkl : k < l
    · simp only [hkl, ite_true]
      exact (G.z475 w hw x hkl F i).symm
    · simp only [hkl, ite_false, expect_zero]
  erw [hlater] at hzero
  have hdiff : G.column w x k F i -
      G.column w x k (G.clusterUpdate w (earlier x k) (x k) F) i =
      expect w (fun ω => select (G.z1 ω) x k i *
        (F (component (G.z1 ω) (x k)) -
          G.expectedCluster w (x k) F (roots (G.z1 ω) (earlier x k)))) := by
    rw [G.column_update w hw]
    unfold column
    erw [← expect_sub]
    congr 1
    funext ω
    ring
  exact sub_eq_iff_eq_add'.mp (hdiff.trans (sub_eq_zero.mp hzero))
end CriticalPercolation.z2
end
end
end OAI
end
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
lemma z437 {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
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
  have hlo := avg_mono (z437 hK haK x) (fun x => (hf x).1)
  have hup := avg_mono (z437 hK haK x) (fun x => (hf x).2)
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
lemma z597 {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
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
lemma z598 {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
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
  exact lt_of_le_of_lt (z597 hK hmass haK μ hμ hμmass hstat hb n x)
    (lt_of_le_of_lt (le_abs_self _) hlt)
end CriticalPercolation.FiniteMarkov
end
end
end OAI
end
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
section
namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CriticalPercolation.z8
variable {E A : Type*} [Fintype E] [Fintype A]
lemma z69 {w : E → A → ℝ} (hw : ∀ e a, 0 ≤ w e a)
    {f : (E → A) → ℝ} (hf : ∀ ω, 0 ≤ f ω) (ω : E → A) :
    density w ω * f ω ≤ expect w f := by
  classical
  exact Finset.single_le_sum (fun ω _ => mul_nonneg (density_nonneg hw ω) (hf ω))
    (Finset.mem_univ ω)
end CriticalPercolation.z8
end
end
end OAI
end
section
namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CriticalPercolation.z2
open CriticalPercolation.z8 CriticalPercolation.ClusterDeletion
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (G : z2 V E)
noncomputable def updateKernel (w : E → Prop → ℝ) (S : Set V) (s : V)
    (U Z : Set V) : ℝ :=
  G.clusterUpdate w S s (fun Y => if Y = Z then 1 else 0) U
lemma z256 (w : E → Prop → ℝ) (S : Set V) (s : V)
    (F : Set V → ℝ) (U : Set V) :
    G.clusterUpdate w S s F U = ∑ Z, G.updateKernel w S s U Z * F Z := by
  classical
  unfold updateKernel clusterUpdate expectedCluster
  simp_rw [← z146, ← expect_sum]
  congr 1
  funext ω
  congr 1
  funext ω'
  simp
omit [Fintype V] in
lemma z522 (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (S : Set V) (s : V) (U Z : Set V) : 0 ≤ G.updateKernel w S s U Z :=
  G.z513 w hpos S s (fun _ => by split_ifs <;> norm_num) U
lemma z575 (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (U : Set V) : ∑ Z, G.updateKernel w S s U Z = 1 := by
  have h := G.z256 w S s (fun _ => 1) U
  simpa only [clusterUpdate, expectedCluster, expect_const w hw, mul_one] using h.symm
omit [Fintype V] in
lemma z328 (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hpos : ∀ e b, 0 ≤ w e b) (S : Set V) (s : V) (U : Set V) :
    density w (fun _ => False) ≤ G.updateKernel w S s U {s} := by
  unfold updateKernel clusterUpdate expectedCluster
  rw [← expect_const w hw (density w (fun _ => False))]
  apply expect_mono hpos
  intro ω
  have h := z69 hpos
    (f := fun ω' => if component (delete (G.z1 ω')
      (roots (delete (G.z1 ω) U) S)) s = {s} then 1 else 0)
    (fun _ => by split_ifs <;> norm_num) (fun _ => False)
  simpa only [show (fun _ : E => False) = (∅ : Set E) from rfl,
    G.z333, delete_bot, component_bot, ite_true, mul_one] using h
lemma z481 (w : E → Prop → ℝ) (S : Set V) (s : V)
    (F : Set V → ℝ) :
    G.avoidedAverage w S s F = ∑ U,
      G.avoidedAverage w S s (fun Z => if Z = U then 1 else 0) * F U := by
  classical
  unfold avoidedAverage
  simp_rw [← z146, ← expect_sum]
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
  rw [← G.z481]
omit [Fintype V] in
lemma z579 (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (S : Set V) (s : V) (U : Set V) : 0 ≤ G.avoidedLaw w S s U := by
  unfold avoidedLaw avoidedAverage
  apply div_nonneg <;> apply expect_nonneg hpos <;> intro ω <;> positivity
omit [Fintype V] in
lemma z240 (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (S : Set V) (s : V) (hs : s ∉ S) :
    density w (fun _ => False) ≤ G.avoidedAverage w S s (fun _ => 1) := by
  unfold avoidedAverage
  have h := z69 hpos
    (f := fun ω => if s ∉ roots (G.z1 ω) S then (1 : ℝ) else 0)
    (fun _ => by split_ifs <;> norm_num) (fun _ => False)
  simpa only [show (fun _ : E => False) = (∅ : Set E) from rfl,
    G.z333, roots_bot, if_pos hs, mul_one] using h
omit [Fintype V] in
lemma avoidance_pos (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (S : Set V) (s : V) (hs : s ∉ S) :
    0 < G.avoidedAverage w S s (fun _ => 1) := by
  have hp : 0 < density w (fun _ => False) := Finset.prod_pos fun e _ => hclosed e
  exact hp.trans_le (G.z240 w hpos S s hs)
lemma z607 (w : E → Prop → ℝ) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (S : Set V) (s : V) (hs : s ∉ S) :
    ∑ U, G.avoidedLaw w S s U = 1 := by
  have h := G.avoidedLaw_avg w S s (fun _ => 1)
  simpa only [FiniteMarkov.avg, mul_one, div_self (ne_of_gt (G.avoidance_pos w hpos hclosed S s hs))]
    using h
lemma z479 (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (S : Set V) (s : V) (Z : Set V) :
    ∑ U, G.avoidedLaw w S s U * G.updateKernel w S s U Z = G.avoidedLaw w S s Z := by
  change FiniteMarkov.avg (G.avoidedLaw w S s)
    (G.clusterUpdate w S s (fun Y => if Y = Z then 1 else 0)) = _
  rw [G.avoidedLaw_avg, G.z381 w hw]
  rfl
lemma z469 (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hpos : ∀ e b, 0 ≤ w e b) (hclosed : ∀ e, 0 < w e False)
    (S : Set V) (s : V) (hs : s ∉ S) (F : Set V → ℝ) (U : Set V) :
    Filter.Tendsto (fun n => (G.clusterUpdate w S s)^[n] F U) Filter.atTop
      (nhds (G.avoidedAverage w S s F / G.avoidedAverage w S s (fun _ => 1))) := by
  have hstep : G.clusterUpdate w S s = FiniteMarkov.step (G.updateKernel w S s) := by
    funext f Z
    exact G.z256 w S s f Z
  have ha : 0 < density w (fun _ => False) := Finset.prod_pos fun e _ => hclosed e
  have haone : density w (fun _ => False) ≤ 1 := by
    have h := z69 hpos (f := fun _ => 1) (fun _ => by norm_num)
      (fun _ => False)
    simpa only [mul_one, expect_const w hw] using h
  rw [hstep, ← G.avoidedLaw_avg]
  exact FiniteMarkov.z598 (G.z522 w hpos S s)
    (G.z575 w hw S s) ha haone
    (G.z328 w hw hpos S s) _ (G.z579 w hpos S s)
    (G.z607 w hpos hclosed S s hs) (G.z479 w hw S s) F U
end CriticalPercolation.z2
end
end
end OAI
end
section
namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CriticalPercolation.z2
open CriticalPercolation.z8 CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical Matrix
variable {V E : Type*} [Fintype V] [Fintype E] (G : z2 V E)
noncomputable def clusterMatrix {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V) :
    Matrix (Fin n) (Fin n) ℝ := fun i k => G.column w x k (fun _ => 1) i
omit [Fintype V] in
lemma z396 {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
    {k i : Fin n} (hik : i < k) (F : Set V → ℝ) : G.column w x k F i = 0 := by
  unfold column
  simp only [z576 _ _ hik, zero_mul, expect_zero]
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
lemma z528 {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V) :
    (G.clusterMatrix w x).IsLowerTriangular := by
  intro i k hik
  exact G.z396 w x hik _
omit [Fintype V] in
lemma z104 {n : ℕ} (w : E → Prop → ℝ)
    (hpos : ∀ e b, 0 ≤ w e b) (hclosed : ∀ e, 0 < w e False)
    (x : Fin n → V) (hx : Function.Injective x) : 0 < (G.clusterMatrix w x).det := by
  rw [Matrix.det_of_isLowerTriangular _ (G.z528 w x)]
  apply Finset.prod_pos
  intro k _
  change 0 < G.column w x k (fun _ => 1) k
  rw [G.column_diag]
  exact G.avoidance_pos w hpos hclosed _ _ (z57 hx k)
noncomputable def inverseColumn {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
    (k : Fin n) (F : Set V → ℝ) : Fin n → ℝ :=
  (G.clusterMatrix w x)⁻¹ *ᵥ G.column w x k F
omit [Fintype V] in
lemma z310 {n : ℕ} (w : E → Prop → ℝ)
    (hpos : ∀ e b, 0 ≤ w e b) (hclosed : ∀ e, 0 < w e False)
    (x : Fin n → V) (hx : Function.Injective x) (k : Fin n) (c : ℝ) :
    G.inverseColumn w x k (fun _ => c) = c • Pi.single k 1 := by
  have hc : G.column w x k (fun _ => c) = c • G.column w x k (fun _ => 1) := by
    funext i
    change expect w _ = c * expect w _
    rw [← z25]
    congr 1
    funext ω
    ring
  have hunit : IsUnit (G.clusterMatrix w x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (G.z104 w hpos hclosed x hx))
  unfold inverseColumn
  rw [hc, Matrix.mulVec_smul]
  congr 1
  have hcol : G.column w x k (fun _ => 1) = G.clusterMatrix w x *ᵥ Pi.single k 1 := by
    ext i
    simp [Matrix.mulVec_single, clusterMatrix]
  rw [hcol, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
lemma z294 {n : ℕ} (w : E → Prop → ℝ)
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
      G.z519 w hw x k F i
  unfold inverseColumn
  rw [hc, Matrix.mulVec_add, Matrix.mulVec_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  split_ifs <;> simp
omit [Fintype V] in
lemma z376 {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
    (k i : Fin n) : Continuous (fun F : Set V → ℝ => G.inverseColumn w x k F i) := by
  unfold inverseColumn Matrix.mulVec dotProduct column expect
  fun_prop
lemma z270 {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (x : Fin n → V) (hx : Function.Injective x)
    (k : Fin n) {F : Set V → ℝ} (hF : Monotone F) (hF0 : ∀ U, 0 ≤ F U) :
    ∀ i, 0 ≤ G.inverseColumn w x k F i := by
  induction k using WellFoundedGT.induction generalizing F with
  | ind k ih =>
    have hstep (f : Set V → ℝ) (hf : Monotone f) (i : Fin n) :
        G.inverseColumn w x k (G.clusterUpdate w (earlier x k) (x k) f) i ≤
          G.inverseColumn w x k f i := by
      have hd := congrFun (G.z294 w hw x k f) i
      simp only [Pi.add_apply, Finset.sum_apply, ite_apply, Pi.zero_apply] at hd
      have hr : 0 ≤ ∑ l, if k < l then G.inverseColumn w x l
          (G.expectedResidual w (earlier x k) (x k) f) i else 0 := by
        apply Finset.sum_nonneg
        intro l _
        split_ifs with hkl
        · exact ih l hkl (G.z362 w hw hpos _ _ hf)
            (G.z405 w hw hpos _ _ hf) i
        · exact le_rfl
      linarith only [hd, hr]
    have hmono (j : ℕ) : Monotone ((G.clusterUpdate w (earlier x k) (x k))^[j] F) := by
      induction j with
      | zero => exact hF
      | succ j hj =>
        rw [Function.iterate_succ_apply']
        exact G.z434 w hpos _ _ hj
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
      · exact le_of_lt (G.avoidance_pos w hpos hclosed _ _ (z57 hx k))
    have hlim : Filter.Tendsto
        (fun j => (G.clusterUpdate w (earlier x k) (x k))^[j] F) Filter.atTop
        (nhds (fun _ => m)) :=
      tendsto_pi_nhds.mpr (fun U => G.z469 w hw hpos hclosed _ _
        (z57 hx k) F U)
    intro i
    have hi := (G.z376 w x k i).tendsto (fun _ => m) |>.comp hlim
    have hb := le_of_tendsto hi (Filter.Eventually.of_forall (fun j => hbound j i))
    rw [G.z310 w hpos hclosed x hx] at hb
    apply le_trans _ hb
    change 0 ≤ m * (Pi.single (M := fun _ : Fin n => ℝ) k 1 i)
    apply mul_nonneg hm
    by_cases hki : k = i <;> simp [hki]
end CriticalPercolation.z2
end
end
end OAI
end
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
lemma z593 (x : Fin n → V) (k : Fin n) (U : Set V) :
    0 ≤ hitOthers x k U := by unfold hitOthers; positivity
lemma z583 (x : Fin n → V) (k : Fin n) (U : Set V) :
    hitOthers x k U ≤ 1 := by unfold hitOthers; split_ifs <;> norm_num
lemma z550 (x : Fin n → V) (k : Fin n) : Monotone (hitOthers x k) := by
  intro U W hUW
  unfold hitOthers
  split_ifs with hU hW hW
  · exact le_rfl
  · obtain ⟨j, hj, hjU⟩ := hU
    exact (hW ⟨j, hj, hUW hjU⟩).elim
  · norm_num
  · exact le_rfl
lemma z521 (x : Fin n → V) (hx : Function.Injective x) (k : Fin n) :
    hitOthers x k {x k} = 0 := by
  apply if_neg
  rintro ⟨j, hj, hjk⟩
  exact hj (hx hjk)
end CriticalPercolation.ClusterColumns
end
end
end OAI
end
section
namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CriticalPercolation.z2
open CriticalPercolation.z8 CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical Matrix
variable {V E : Type*} [Fintype V] [Fintype E] (G : z2 V E)
omit [Fintype V] in
lemma z392 {n : ℕ} (w : E → Prop → ℝ) (x : Fin n → V)
    (k i : Fin n) (hik : i ≠ k) :
    G.column w x k (hitOthers x k) i = G.column w x k (fun _ => 1) i := by
  unfold column
  congr 1
  funext ω
  by_cases hc : first (G.z1 ω) x k ∧ x i ∈ component (G.z1 ω) (x k)
  · have hh : ∃ j, j ≠ k ∧ x j ∈ component (G.z1 ω) (x k) := ⟨i, hik, hc.2⟩
    simp [select, hitOthers, hc, hh]
  · simp [select, hc]
omit [Fintype V] in
lemma z363 {n : ℕ} (w : E → Prop → ℝ)
    (hpos : ∀ e b, 0 ≤ w e b) (hclosed : ∀ e, 0 < w e False)
    (x : Fin n → V) (hx : Function.Injective x) (k : Fin n) :
    0 < G.column w x k (fun _ => 1) k - G.column w x k (hitOthers x k) k := by
  have he : G.column w x k (fun _ => 1) k - G.column w x k (hitOthers x k) k =
      expect w (fun ω => select (G.z1 ω) x k k *
        (1 - hitOthers x k (component (G.z1 ω) (x k)))) := by
    unfold column
    erw [← expect_sub]
    congr 1
    funext ω
    ring
  rw [he]
  have hf (ω : E → Prop) : 0 ≤ select (G.z1 ω) x k k *
      (1 - hitOthers x k (component (G.z1 ω) (x k))) :=
    mul_nonneg (select_nonneg _ _ _ _) (sub_nonneg.mpr (z583 _ _ _))
  have hd := z69 hpos hf (fun _ => False)
  have hs : first (⊥ : SimpleGraph V) x k := by
    simpa only [first, roots_bot] using z57 hx k
  simp only [show (fun _ : E => False) = (∅ : Set E) from rfl,
    G.z333, component_bot, z521 x hx, sub_zero,
    select_diag, hs, ite_true, mul_one] at hd
  have hp : 0 < density w (∅ : Set E) := Finset.prod_pos (fun e _ => hclosed e)
  simpa only [select_diag] using hp.trans_le hd
lemma z287 {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (x : Fin n → V) (hx : Function.Injective x)
    (k i : Fin n) (hik : i ≠ k) : (G.clusterMatrix w x)⁻¹ i k ≤ 0 := by
  let a := G.column w x k (fun _ => 1) k - G.column w x k (hitOthers x k) k
  have ha : 0 < a := G.z363 w hpos hclosed x hx k
  have he : G.column w x k (fun _ => 1) =
      G.column w x k (hitOthers x k) + a • Pi.single k 1 := by
    ext j
    by_cases hj : j = k
    · subst j
      simp [a]
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hj, mul_zero,
        add_zero]
      exact (G.z392 w x k j hj).symm
  have he' := congrArg (fun v => (G.clusterMatrix w x)⁻¹ *ᵥ v) he
  change G.inverseColumn w x k (fun _ => 1) = _ at he'
  rw [G.z310 w hpos hclosed x hx, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_single_one] at he'
  have he'' := congrFun he' i
  simp only [Pi.single_eq_of_ne hik, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.col_apply] at he''
  have hp := G.z270 w hw hpos hclosed x hx k
    (z550 x k) (z593 x k) i
  change 0 ≤ ((G.clusterMatrix w x)⁻¹ *ᵥ G.column w x k (hitOthers x k)) i at hp
  nlinarith only [he'', hp, ha]
omit [Fintype V] in
lemma z422 {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (x : Fin n → V) :
    G.clusterMatrix w x *ᵥ (fun _ => 1) = fun _ => 1 := by
  ext i
  change (∑ k, G.column w x k (fun _ => 1) i * 1) = 1
  simp only [mul_one, column]
  erw [← expect_sum]
  simpa only [mul_one, select_mass] using expect_const w hw 1
omit [Fintype V] in
lemma z458 {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (x : Fin n → V) (hx : Function.Injective x) :
    (G.clusterMatrix w x)⁻¹ *ᵥ (fun _ => 1) = fun _ => 1 := by
  have h := congrArg (fun v => (G.clusterMatrix w x)⁻¹ *ᵥ v)
    (G.z422 w hw x)
  have hu : IsUnit (G.clusterMatrix w x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (G.z104 w hpos hclosed x hx))
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec] at h
  exact h.symm
omit [Fintype V] in
lemma z297 {n : ℕ} (w : E → Prop → ℝ)
    (x : Fin n → V) (F : Set V → ℝ) :
    (fun i => expect w (fun ω => F (component (G.z1 ω) (x i)))) =
      ∑ k, G.column w x k F := by
  ext i
  simp only [Finset.sum_apply, column]
  erw [← expect_sum]
  congr 1
  funext ω
  exact z568 (G.z1 ω) x F i
lemma z209 {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (x : Fin n → V) (hx : Function.Injective x)
    {F : Set V → ℝ} (hF : Monotone F) (hF0 : ∀ U, 0 ≤ F U) (i : Fin n) :
    0 ≤ ((G.clusterMatrix w x)⁻¹ *ᵥ
      (fun j => expect w (fun ω => F (component (G.z1 ω) (x j))))) i := by
  rw [G.z297, Matrix.mulVec_sum, Finset.sum_apply]
  exact Finset.sum_nonneg (fun k _ => G.z270 w hw hpos hclosed x hx k hF hF0 i)
end CriticalPercolation.z2
end
end
end OAI
end
section
namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CriticalPercolation.z2
open CriticalPercolation.z8 CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical Matrix
variable {V E : Type*} [Fintype V] [Fintype E] (G : z2 V E)
omit [Fintype V] in
lemma z480 {n : ℕ} (w : E → Prop → ℝ)
    (hpos : ∀ e b, 0 ≤ w e b) (hclosed : ∀ e, 0 < w e False)
    (x : Fin (n+1) → V) (hx : Function.Injective x) :
    G.avoidedAverage w (earlier x (Fin.last n)) (x (Fin.last n)) (fun _ => 1) *
      (G.clusterMatrix w x)⁻¹ (Fin.last n) (Fin.last n) = 1 := by
  have hu : IsUnit (G.clusterMatrix w x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (G.z104 w hpos hclosed x hx))
  have h := congrArg (fun M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ =>
    M (Fin.last n) (Fin.last n)) (Matrix.nonsing_inv_mul (G.clusterMatrix w x) hu)
  simp only [Matrix.mul_apply, Matrix.one_apply_eq, Fin.sum_univ_castSucc,
    clusterMatrix, z396 _ _ _ (Fin.castSucc_lt_last _), mul_zero,
    Finset.sum_const_zero, zero_add, column_diag] at h
  simpa only [mul_comm] using h
lemma z510 {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (x : Fin (n+1) → V) (hx : Function.Injective x)
    {F : Set V → ℝ} (hF : Monotone F) (hF0 : ∀ U, 0 ≤ F U)
    (a : ℝ) (ha : ∀ j : Fin n, a ≤ expect w
      (fun ω => F (component (G.z1 ω) (x j.castSucc)))) :
    (1 - G.avoidedAverage w (earlier x (Fin.last n)) (x (Fin.last n)) (fun _ => 1)) * a ≤
      expect w (fun ω => F (component (G.z1 ω) (x (Fin.last n)))) := by
  let N := (G.clusterMatrix w x)⁻¹
  let y : Fin (n+1) → ℝ := fun j => expect w (fun ω => F (component (G.z1 ω) (x j)))
  let d := G.avoidedAverage w (earlier x (Fin.last n)) (x (Fin.last n)) (fun _ => 1)
  have hd : 0 < d := G.avoidance_pos w hpos hclosed _ _ (z57 hx _)
  have hdiag : d * N (Fin.last n) (Fin.last n) = 1 := G.z480 w hpos hclosed x hx
  have hmass := congrFun (G.z458 w hw hpos hclosed x hx) (Fin.last n)
  change ∑ j, N (Fin.last n) j * 1 = 1 at hmass
  simp only [mul_one, Fin.sum_univ_castSucc] at hmass
  have hzero := G.z209 w hw hpos hclosed x hx hF hF0 (Fin.last n)
  change 0 ≤ ∑ j, N (Fin.last n) j * y j at hzero
  rw [Fin.sum_univ_castSucc] at hzero
  have hs : (∑ j : Fin n, N (Fin.last n) j.castSucc * y j.castSucc) ≤
      (∑ j : Fin n, N (Fin.last n) j.castSucc) * a := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonpos_left (ha j)
      (G.z287 w hw hpos hclosed x hx j.castSucc (Fin.last n)
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
end CriticalPercolation.z2
end
end
end OAI
end
section
namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CriticalPercolation.z2
open CriticalPercolation.z8 CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (G : z2 V E)
omit [Fintype V] in
lemma z251 (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (A : Set V) (s : V) :
    expect w (fun ω => hitValue A (component (G.z1 ω) s)) =
      1 - G.avoidedAverage w A s (fun _ => 1) := by
  conv_rhs => lhs; rw [← expect_const w hw 1]
  unfold avoidedAverage
  erw [← expect_sub]
  congr 1
  funext ω
  simp only [hitValue, z272]
  split_ifs <;> norm_num
lemma z375 {n : ℕ} (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (x : Fin (n+1) → V) (hx : Function.Injective x)
    (T : Set V) (a : ℝ) (ha : ∀ j : Fin n, a ≤ expect w
      (fun ω => hitValue T (component (G.z1 ω) (x j.castSucc)))) :
    expect w (fun ω => hitValue (earlier x (Fin.last n))
        (component (G.z1 ω) (x (Fin.last n)))) * a ≤
      expect w (fun ω => jointHitValue (earlier x (Fin.last n)) T
        (component (G.z1 ω) (x (Fin.last n)))) := by
  rw [G.z251 w hw]
  apply G.z510 w hw hpos hclosed x hx
    (z450 _ _) (z516 _ _)
  intro j
  have he : (fun ω : E → Prop => jointHitValue (earlier x (Fin.last n)) T
      (component (G.z1 ω) (x j.castSucc))) =
      (fun ω => hitValue T (component (G.z1 ω) (x j.castSucc))) := by
    funext ω
    apply z126
    exact ⟨x j.castSucc, component_self _ _, ⟨j.castSucc, Fin.castSucc_lt_last j, rfl⟩⟩
  rw [he]
  exact ha j
end CriticalPercolation.z2
open Set MeasureTheory ProbabilityTheory
end
end
end OAI
end
section
namespace OAI
section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
namespace CriticalPercolation.z2
open CriticalPercolation.z8 CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (G : z2 V E)
lemma z314 (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (hclosed : ∀ e, 0 < w e False) (o : V) (A T : Set V) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ expect w
      (fun ω => hitValue T (component (G.z1 ω) v))) :
    expect w (fun ω => hitValue A (component (G.z1 ω) o)) * a ≤
      expect w (fun ω => jointHitValue A T (component (G.z1 ω) o)) := by
  classical
  by_cases ho : o ∈ A
  · have hA (ω : Set E) : (component (G.z1 ω) o ∩ A).Nonempty :=
      ⟨o, component_self _ _, ho⟩
    have hh : (fun ω : Set E => hitValue A (component (G.z1 ω) o)) =
        (fun _ => (1 : ℝ)) := by
      funext ω
      exact if_pos (hA ω)
    have hj : (fun ω : Set E => jointHitValue A T (component (G.z1 ω) o)) =
        (fun ω => hitValue T (component (G.z1 ω) o)) := by
      funext ω
      exact z126 (hA ω)
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
    have h := G.z375 w hw hpos hclosed x hx T a (by
      intro j
      simpa only [x, Fin.snoc_castSucc] using ha (f j) (e j).property)
    rwa [hearlier, hlast] at h
end CriticalPercolation.z2
end
end
end OAI
end
section
namespace OAI
section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
namespace CriticalPercolation.z2
open CriticalPercolation.z8 CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (G : z2 V E)
lemma z529 (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (o : V) (A T : Set V) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ expect w
      (fun ω => hitValue T (component (G.z1 ω) v))) :
    expect w (fun ω => hitValue A (component (G.z1 ω) o)) * a ≤
      expect w (fun ω => jointHitValue A T (component (G.z1 ω) o)) := by
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
    |expect (w' t) (fun ω => hitValue T (component (G.z1 ω) v)) -
      expect w (fun ω => hitValue T (component (G.z1 ω) v))|
  have herr : Continuous err := by
    apply continuous_finsetSum
    intro v _
    exact (((z47 _).comp hcont).sub continuous_const).abs
  have herr0 : err 0 = 0 := by simp [err, hzero]
  have hbound (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
      expect (w' t) (fun ω => hitValue A (component (G.z1 ω) o)) * (a-err t) ≤
        expect (w' t) (fun ω => jointHitValue A T (component (G.z1 ω) o)) := by
    apply G.z314
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
          |expect (w' t) (fun ω => hitValue T (component (G.z1 ω) v)) -
            expect w (fun ω => hitValue T (component (G.z1 ω) v))| ≤ err t := by
        dsimp only [err]
        exact Finset.single_le_sum (f := fun u : V =>
          |expect (w' t) (fun ω => hitValue T (component (G.z1 ω) u)) -
            expect w (fun ω => hitValue T (component (G.z1 ω) u))|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ v)
      have hneg := (abs_le.mp hsingle).1
      linarith [ha v hv]
  have ht : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ)+1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hL := ((((z47
    (fun ω => hitValue A (component (G.z1 ω) o))).comp hcont).mul
      ((continuous_const (y := a)).sub herr)).tendsto 0).comp ht
  have hR := (((z47
    (fun ω => jointHitValue A T (component (G.z1 ω) o))).comp hcont).tendsto 0).comp ht
  have hh := le_of_tendsto_of_tendsto hL hR (Filter.Eventually.of_forall (fun n : ℕ =>
    hbound (1/((n : ℝ)+1)) (by positivity) (by
      apply (div_le_one (by positivity : (0 : ℝ) < n+1)).mpr
      have hn := Nat.cast_nonneg (α := ℝ) n
      linarith)))
  simpa only [Pi.mul_apply, Pi.sub_apply, Function.comp_apply, hzero, herr0, sub_zero] using hh
end CriticalPercolation.z2
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
end
end
end OAI
end
section
namespace OAI
section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
open Set
open scoped Classical
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
noncomputable def restrictVertices (U : Set V)
    (hU : ∀ e v, v ∈ G.ends e → v ∈ U) : z2 U E where
  ends e := (G.ends e).attachWith (hU e)
lemma z517 (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    (ω : Set E) (v w : U) :
    ((G.restrictVertices U hU).z1 ω).Adj v w ↔
      (G.z1 ω).Adj v.val w.val := by
  simp only [z1, SimpleGraph.fromEdgeSet_adj, Set.mem_image]
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
lemma z456 (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    (ω : Set E) :
    (G.restrictVertices U hU).z1 ω = (G.z1 ω).induce U := by
  ext v w
  exact G.z517 U hU ω v w
lemma z600 (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    {ω : Set E} {v w : V} (h : (G.z1 ω).Adj v w) : v ∈ U ∧ w ∈ U := by
  obtain ⟨⟨e, _, he⟩, _⟩ := (SimpleGraph.fromEdgeSet_adj _).mp h
  exact ⟨hU e v (by simp [he]), hU e w (by simp [he])⟩
lemma z306 (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    {ω : Set E} {v w : V} (p : (G.z1 ω).Walk v w) (hv : v ∈ U) :
    ∀ u ∈ p.support, u ∈ U := by
  induction p with
  | nil => simpa
  | @cons v w z hvw p ih =>
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact hv
      · exact ih (G.z600 U hU hvw).2 u hu
lemma z443 (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    {ω : Set E} {v : V} (hv : v ∈ U) : G.cluster ω v ⊆ U := by
  rintro w ⟨p⟩
  exact G.z306 U hU p hv w p.end_mem_support
lemma z116 (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    (ω : Set E) (v w : U) :
    ((G.restrictVertices U hU).z1 ω).Reachable v w ↔
      (G.z1 ω).Reachable v.val w.val := by
  rw [G.z456]
  constructor
  · intro h
    exact h.map (SimpleGraph.Embedding.induce U).toHom
  · rintro ⟨p⟩
    exact ⟨p.induce U (G.z306 U hU p v.property)⟩
open CriticalPercolation.ClusterColumns CriticalPercolation.ClusterDeletion
open CriticalPercolation.z8
lemma z149 (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    (ω : Set E) (v : U) (A : Set V) :
    (component ((G.restrictVertices U hU).z1 ω) v ∩ (Subtype.val ⁻¹' A)).Nonempty ↔
      (component (G.z1 ω) v.val ∩ A).Nonempty := by
  constructor
  · rintro ⟨w, hw, hA⟩
    exact ⟨w.val, (G.z116 U hU ω v w).mp hw, hA⟩
  · rintro ⟨w, hw, hA⟩
    have hwU := G.z443 U hU v.property hw
    exact ⟨⟨w, hwU⟩, (G.z116 U hU ω v ⟨w, hwU⟩).mpr hw, hA⟩
lemma z128 (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    (ω : Set E) (v : U) (A : Set V) :
    hitValue (Subtype.val ⁻¹' A) (component ((G.restrictVertices U hU).z1 ω) v) =
      hitValue A (component (G.z1 ω) v.val) := by
  simp only [hitValue, G.z149]
lemma z214 (U : Set V) (hU : ∀ e v, v ∈ G.ends e → v ∈ U)
    (ω : Set E) (v : U) (A T : Set V) :
    jointHitValue (Subtype.val ⁻¹' A) (Subtype.val ⁻¹' T)
        (component ((G.restrictVertices U hU).z1 ω) v) =
      jointHitValue A T (component (G.z1 ω) v.val) := by
  simp only [jointHitValue, G.z149]
lemma z366 [Fintype E] (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hpos : ∀ e b, 0 ≤ w e b)
    (o : V) (A T : Set V) (hA : A.Finite) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ expect w
      (fun ω => hitValue T (component (G.z1 ω) v))) :
    expect w (fun ω => hitValue A (component (G.z1 ω) o)) * a ≤
      expect w (fun ω => jointHitValue A T (component (G.z1 ω) o)) := by
  let U : Set V := insert o (A ∪ ⋃ e, (↑(G.ends e).toFinset : Set V))
  have hUf : U.Finite :=
    (hA.union (Set.finite_iUnion fun e => (G.ends e).toFinset.finite_toSet)).insert o
  let : Fintype U := hUf.fintype
  have hU : ∀ e v, v ∈ G.ends e → v ∈ U := by
    intro e v hv
    exact Or.inr (Or.inr (Set.mem_iUnion.mpr ⟨e, by simpa using hv⟩))
  let R := G.restrictVertices U hU
  let o' : U := ⟨o, Set.mem_insert _ _⟩
  have h := R.z529 w hw hpos o' (Subtype.val ⁻¹' A)
    (Subtype.val ⁻¹' T) a (by
      intro v hv
      have heq : (fun ω : E → Prop =>
          hitValue (Subtype.val ⁻¹' T) (component (R.z1 ω) v)) =
          (fun ω => hitValue T (component (G.z1 ω) v.val)) := by
        funext ω
        exact G.z128 U hU ω v T
      rw [heq]
      exact ha v.val hv)
  have heq : (fun ω : E → Prop =>
      hitValue (Subtype.val ⁻¹' A) (component (R.z1 ω) o')) =
      (fun ω => hitValue A (component (G.z1 ω) o)) := by
    funext ω
    exact G.z128 U hU ω o' A
  have heq' : (fun ω : E → Prop =>
      jointHitValue (Subtype.val ⁻¹' A) (Subtype.val ⁻¹' T)
        (component (R.z1 ω) o')) =
      (fun ω => jointHitValue A T (component (G.z1 ω) o)) := by
    funext ω
    exact G.z214 U hU ω o' A T
  rwa [heq, heq'] at h
end CriticalPercolation.z2
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
end
end
end OAI
end
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
namespace CriticalPercolation.z2
open CriticalPercolation.z8 CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns CriticalPercolation.z0
variable {V E : Type*} (G : z2 V E)
def hitEvent (o : V) (A : Set V) : Set (Set E) :=
  {ω | (G.cluster ω o ∩ A).Nonempty}
lemma z194 [Countable V] [Countable E] (o : V) (A : Set V) :
    MeasurableSet (G.hitEvent o A) := by
  exact (Measurable.exists fun v => (G.z79 o v).and measurable_const).setOf
lemma z155 (o : V) (A : Set V) {ω ω' : Set E} (h : ω ⊆ ω') :
    ω ∈ G.hitEvent o A → ω' ∈ G.hitEvent o A :=
  fun hω => hω.mono (Set.inter_subset_inter_left A (G.cluster_mono h o))
lemma z266 (o : V) {A A' : Set V} (h : A ⊆ A') :
    G.hitEvent o A ⊆ G.hitEvent o A' :=
  fun _ hω => hω.mono (Set.inter_subset_inter_right _ h)
lemma z348 [Fintype E] (q : E → unitInterval) (o : V) (A : Set V) :
    expect (fun e => z28 (q e))
      (fun ω => hitValue A (component (G.z1 ω) o)) =
        (z0.law q).real (G.hitEvent o A) := by
  erw [← z63 q (fun ω : Set E =>
    hitValue A (component (G.z1 ω) o))]
  have he : (fun ω : Set E => hitValue A (component (G.z1 ω) o)) =
      (G.hitEvent o A).indicator (1 : Set E → ℝ) := by
    funext ω
    simp only [hitValue, Set.indicator_apply, Pi.one_apply, hitEvent,
      component, cluster, Set.mem_ofPred_eq]
    rfl
  rw [he, integral_indicator_one (.of_discrete)]
lemma z408 [Fintype E] (q : E → unitInterval) (o : V) (A T : Set V) :
    expect (fun e => z28 (q e))
      (fun ω => jointHitValue A T (component (G.z1 ω) o)) =
        (z0.law q).real (G.hitEvent o A ∩ G.hitEvent o T) := by
  erw [← z63 q (fun ω : Set E =>
    jointHitValue A T (component (G.z1 ω) o))]
  have he : (fun ω : Set E => jointHitValue A T (component (G.z1 ω) o)) =
      (G.hitEvent o A ∩ G.hitEvent o T).indicator (1 : Set E → ℝ) := by
    funext ω
    simp only [jointHitValue, Set.indicator_apply, Pi.one_apply, hitEvent,
      component, cluster, Set.mem_inter_iff, Set.mem_ofPred_eq]
    rfl
  rw [he, integral_indicator_one (.of_discrete)]
lemma z275 [Fintype E] (q : E → unitInterval)
    (o : V) (A T : Set V) (hA : A.Finite) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ (z0.law q).real (G.hitEvent v T)) :
    (z0.law q).real (G.hitEvent o A) * a ≤
      (z0.law q).real (G.hitEvent o A ∩ G.hitEvent o T) := by
  rw [← G.z348, ← G.z408]
  apply G.z366 _ (fun e => bitWeight_sum (q e))
    (fun e b => z143 (q e) b) o A T hA a
  intro v hv
  rw [G.z348]
  exact ha v hv
def restrictEdges (s : Set E) : z2 V s where
  ends e := G.ends e
lemma z404 (s : Set E) (ω : Set E) :
    (G.restrictEdges s).z1 (Subtype.val ⁻¹' ω) = G.z1 (s ∩ ω) := by
  unfold z1 restrictEdges
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff, Subtype.exists]
  constructor
  · rintro ⟨e, hs, hω, rfl⟩
    exact ⟨e, ⟨hs, hω⟩, rfl⟩
  · rintro ⟨e, ⟨hs, hω⟩, rfl⟩
    exact ⟨e, hs, hω, rfl⟩
lemma z94 (s : Set E) (o : V) (A : Set V) :
    (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) ⁻¹'
        ((G.restrictEdges s).hitEvent o A) =
      {ω | s ∩ ω ∈ G.hitEvent o A} := by
  ext ω
  simp only [Set.mem_preimage, hitEvent, cluster, Set.mem_ofPred_eq,
    G.z404]
lemma z268 [Countable V] [Countable E]
    (q : E → unitInterval) (s : Set E) (hs : s.Finite)
    (o : V) (A T : Set V) (hA : A.Finite) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ (z0.law q).real {ω | s ∩ ω ∈ G.hitEvent v T}) :
    (z0.law q).real {ω | s ∩ ω ∈ G.hitEvent o A} * a ≤
      (z0.law q).real ({ω | s ∩ ω ∈ G.hitEvent o A} ∩
        {ω | s ∩ ω ∈ G.hitEvent o T}) := by
  let : Fintype s := hs.fintype
  have hmeas : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
    measurable_pi_lambda _ (fun edge => measurable_set_mem edge.val)
  have hr (B : Set (Set s)) (hB : MeasurableSet B) :
      (z0.law (fun e : s => q e)).real B =
        (z0.law q).real ((fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) ⁻¹' B) := by
    rw [← z97 q s]
    simp only [measureReal_def, Measure.map_apply hmeas hB]
  have h := (G.restrictEdges s).z275
    (fun e : s => q e) o A T hA a (by
      intro v hv
      rw [hr _ (.of_discrete), G.z94]
      exact ha v hv)
  rw [hr _ (.of_discrete), hr _ (.of_discrete), Set.preimage_inter,
    G.z94, G.z94] at h
  exact h
lemma z78 {X : Type*} {U S : Set X}
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
lemma z141 (K : Set.FiniteExhaustion (Set.univ : Set E))
    (o : V) (A : Set V) :
    (⋃ n, {ω | K n ∩ ω ∈ G.hitEvent o A}) = G.hitEvent o A := by
  ext ω
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
    exact G.z155 o A Set.inter_subset_right hn
  · rintro ⟨v, hv, hvA⟩
    obtain ⟨s, hs, hsω, hvs⟩ := G.z43 hv
    obtain ⟨n, hn⟩ := z78 K hs (Set.subset_univ s)
    exact Set.mem_iUnion.mpr ⟨n, v, G.cluster_mono
      (Set.subset_inter hn hsω) o hvs, hvA⟩
lemma z38 (K : Set.FiniteExhaustion (Set.univ : Set E))
    (o : V) (A : Set V) :
    Monotone (fun n => {ω | K n ∩ ω ∈ G.hitEvent o A}) := by
  intro m n h ω hω
  exact G.z155 o A (Set.inter_subset_inter_left _ (K.mono h)) hω
lemma z71 [Countable E]
    (q : E → unitInterval) (K : Set.FiniteExhaustion (Set.univ : Set E))
    (o : V) (A : Set V) :
    Tendsto (fun n => (z0.law q).real {ω | K n ∩ ω ∈ G.hitEvent o A})
      atTop (𝓝 ((z0.law q).real (G.hitEvent o A))) := by
  have h := tendsto_measure_iUnion_atTop (μ := z0.law q)
    (G.z38 K o A)
  rw [G.z141 K o A] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
lemma z370 (K : Set.FiniteExhaustion (Set.univ : Set E))
    (o : V) (A T : Set V) :
    (⋃ n, ({ω | K n ∩ ω ∈ G.hitEvent o A} ∩
      {ω | K n ∩ ω ∈ G.hitEvent o T})) = G.hitEvent o A ∩ G.hitEvent o T := by
  calc
    _ = (⋃ n, {ω | K n ∩ ω ∈ G.hitEvent o A}) ∩
        (⋃ n, {ω | K n ∩ ω ∈ G.hitEvent o T}) :=
      Set.iUnion_inter_of_monotone (G.z38 K o A)
        (G.z38 K o T)
    _ = _ := by rw [G.z141 K o A, G.z141 K o T]
lemma z106 [Countable E]
    (q : E → unitInterval) (K : Set.FiniteExhaustion (Set.univ : Set E))
    (o : V) (A T : Set V) :
    Tendsto (fun n => (z0.law q).real
      ({ω | K n ∩ ω ∈ G.hitEvent o A} ∩ {ω | K n ∩ ω ∈ G.hitEvent o T}))
      atTop (𝓝 ((z0.law q).real (G.hitEvent o A ∩ G.hitEvent o T))) := by
  have h := tendsto_measure_iUnion_atTop (μ := z0.law q)
    ((G.z38 K o A).inter (G.z38 K o T))
  rw [G.z370 K o A T] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
lemma z377 {X : Type*} [Fintype X] (f g : X → ℝ) (x : X) :
    |f x - g x| ≤ ∑ y, |f y - g y| := by
  exact Finset.single_le_sum (fun y _ => abs_nonneg (f y - g y)) (Finset.mem_univ x)
lemma z233 [Countable V] [Countable E]
    (q : E → unitInterval) (o : V) (A T : Set V) (hA : A.Finite) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ (z0.law q).real (G.hitEvent v T)) :
    (z0.law q).real (G.hitEvent o A) * a ≤
      (z0.law q).real (G.hitEvent o A ∩ G.hitEvent o T) := by
  classical
  let : Fintype A := hA.fintype
  let K := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  let err : ℕ → ℝ := fun n => ∑ v : A,
    |(z0.law q).real {ω | K n ∩ ω ∈ G.hitEvent v T} -
      (z0.law q).real (G.hitEvent v T)|
  have herr : Tendsto err atTop (𝓝 0) := by
    have h : Tendsto err atTop (𝓝 (∑ _v : A, (0 : ℝ))) := by
      apply tendsto_finsetSum
      intro v _
      simpa using ((G.z71 q K v T).sub_const
        ((z0.law q).real (G.hitEvent v T))).abs
    simpa using h
  have hbound (n : ℕ) :
      (z0.law q).real {ω | K n ∩ ω ∈ G.hitEvent o A} * (a - err n) ≤
      (z0.law q).real ({ω | K n ∩ ω ∈ G.hitEvent o A} ∩
        {ω | K n ∩ ω ∈ G.hitEvent o T}) := by
    refine G.z268 q (K n) (K.finite n) o A T hA (a - err n) ?_
    intro v hv
    have hs : |(z0.law q).real {ω | K n ∩ ω ∈ G.hitEvent v T} -
        (z0.law q).real (G.hitEvent v T)| ≤ err n := by
      exact z377
        (fun u : A => (z0.law q).real {ω | K n ∩ ω ∈ G.hitEvent u T})
        (fun u : A => (z0.law q).real (G.hitEvent u T)) ⟨v, hv⟩
    have hneg := (abs_le.mp hs).1
    linarith [ha v hv]
  have hL := (G.z71 q K o A).mul ((tendsto_const_nhds (x := a)).sub herr)
  have hR := G.z106 q K o A T
  have h := le_of_tendsto_of_tendsto hL hR (Eventually.of_forall hbound)
  simpa only [sub_zero] using h
lemma z605 {I : Type*} (o : V) (A : I → Set V) :
    G.hitEvent o (⋃ i, A i) = ⋃ i, G.hitEvent o (A i) := by
  ext ω
  simp only [hitEvent, Set.mem_ofPred_eq, Set.mem_iUnion, Set.nonempty_def,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨v, hv, i, hi⟩
    exact ⟨i, v, hv, hi⟩
  · rintro ⟨i, v, hv, hi⟩
    exact ⟨v, hv, i, hi⟩
theorem z457 [Countable V] [Countable E]
    (q : E → unitInterval) (o : V) (A T : Set V) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ (z0.law q).real (G.hitEvent v T)) :
    (z0.law q).real (G.hitEvent o A) * a ≤
      (z0.law q).real (G.hitEvent o A ∩ G.hitEvent o T) := by
  let K := (Set.to_countable A).finiteExhaustion
  have hKA (n : ℕ) : K n ⊆ A := by
    exact Set.Subset.trans (Set.subset_iUnion K n) (le_of_eq K.iUnion_eq)
  have hmono : Monotone (fun n => G.hitEvent o (K n)) := by
    intro m n h
    exact G.z266 o (K.mono h)
  have hunion : (⋃ n, G.hitEvent o (K n)) = G.hitEvent o A := by
    rw [← G.z605, K.iUnion_eq]
  have hL : Tendsto (fun n => (z0.law q).real (G.hitEvent o (K n)))
      atTop (𝓝 ((z0.law q).real (G.hitEvent o A))) := by
    have h := tendsto_measure_iUnion_atTop (μ := z0.law q) hmono
    rw [hunion] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  have hR : Tendsto (fun n => (z0.law q).real
      (G.hitEvent o (K n) ∩ G.hitEvent o T))
      atTop (𝓝 ((z0.law q).real (G.hitEvent o A ∩ G.hitEvent o T))) := by
    have h := tendsto_measure_iUnion_atTop (μ := z0.law q)
      (hmono.inter (monotone_const (c := G.hitEvent o T)))
    rw [← Set.iUnion_inter, hunion] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  exact le_of_tendsto_of_tendsto (hL.mul_const a) hR
    (Eventually.of_forall fun n => G.z233 q o (K n) T
      (K.finite n) a (fun v hv => ha v (hKA n hv)))
theorem joint_gluing [Countable V] [Countable E]
    (p : unitInterval) (o : V) (A T : Set V) (a : ℝ)
    (ha : ∀ v ∈ A, a ≤ (G.law p).real (G.hitEvent v T)) :
    (G.law p).real (G.hitEvent o A) * a ≤
      (G.law p).real (G.hitEvent o A ∩ G.hitEvent o T) := by
  have he : z0.law (fun _ : E => p) = G.law p := law_const p
  simpa only [he] using G.z457 (fun _ => p) o A T a
    (by simpa only [he] using ha)
end CriticalPercolation.z2
open Set MeasureTheory ProbabilityTheory
open scoped Classical
end
end
end OAI
end
section
namespace OAI
section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open scoped Classical Topology
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Filter Topology
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical
namespace CriticalPercolation.z0
variable {E : Type*}
lemma z511 (b : Prop) : Continuous (fun p : unitInterval => z28 p b) := by
  by_cases hb : b
  · simpa [z28, hb] using (continuous_subtype_val : Continuous (fun p : unitInterval => (p : ℝ)))
  · simp only [z28, if_neg hb]
    fun_prop
lemma z315 [Fintype E] (A : Set (Set E)) :
    Continuous (fun p : unitInterval => (law (fun _ : E => p)).real A) := by
  have h (p : unitInterval) : (law (fun _ : E => p)).real A =
      z8.expect (fun _ : E => z28 p)
        (fun ω : E → Prop => A.indicator (fun _ => (1 : ℝ)) {e | ω e}) := by
    rw [← z63]
    exact (integral_indicator_one (.of_discrete) :
      (∫ ω, A.indicator (1 : Set E → ℝ) ω ∂law (fun _ : E => p)) = _).symm
  simp_rw [h]
  apply (z8.z47 _).comp
  exact continuous_pi fun _ => continuous_pi fun b => z511 b
lemma z398 (p : unitInterval) (s : Set E) (hs : s.Finite)
    (A : Set (Set E)) :
    (law (fun _ : E => p)).real {ω | s ∩ ω ∈ A} =
      (law (fun _ : s => p)).real {ω | Subtype.val '' ω ∈ A} := by
  let := hs.fintype
  have hi (ω : Set E) : Subtype.val '' (Subtype.val ⁻¹' ω : Set s) = s ∩ ω := by
    ext e
    simp
  rw [← z97 (fun _ : E => p) s]
  have hf : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
    measurable_pi_lambda _ (fun edge => measurable_set_mem edge.val)
  simp only [Measure.real]
  rw [Measure.map_apply hf (.of_discrete)]
  simp only [Set.preimage_ofPred_eq, hi]
lemma z274 (s : Set E) (hs : s.Finite) (A : Set (Set E)) :
    Continuous (fun p : unitInterval => (law (fun _ : E => p)).real
      {ω | s ∩ ω ∈ A}) := by
  let := hs.fintype
  simp_rw [z398 _ s hs A]
  exact z315 _
def z11 (A : Set (Set E)) : Prop :=
  ∀ ω ∈ A, ∃ s : Set E, s.Finite ∧ s ⊆ ω ∧ s ∈ A
lemma z49 (A : Set (Set E)) (hmono : IsUpperSet A)
    (hw : z11 A) (K : Set.FiniteExhaustion (Set.univ : Set E)) :
    (⋃ n, {ω | K n ∩ ω ∈ A}) = A := by
  ext ω
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
    exact hmono Set.inter_subset_right hn
  · intro h
    obtain ⟨s, hs, hsω, hsA⟩ := hw ω h
    obtain ⟨n, hn⟩ := z2.z78 K hs (Set.subset_univ _)
    exact Set.mem_iUnion.mpr ⟨n, hmono (Set.subset_inter hn hsω) hsA⟩
lemma z50 (A : Set (Set E)) (hmono : IsUpperSet A)
    (K : Set.FiniteExhaustion (Set.univ : Set E)) :
    Monotone (fun n => {ω | K n ∩ ω ∈ A}) := by
  intro m n h ω hω
  exact hmono (Set.inter_subset_inter_left _ (K.mono h)) hω
lemma z112 (p : unitInterval) (A : Set (Set E))
    (hmono : IsUpperSet A) (hw : z11 A)
    (K : Set.FiniteExhaustion (Set.univ : Set E)) :
    Tendsto (fun n => (law (fun _ : E => p)).real {ω | K n ∩ ω ∈ A})
      atTop (𝓝 ((law (fun _ : E => p)).real A)) := by
  have h := tendsto_measure_iUnion_atTop (μ := law (fun _ : E => p))
    (z50 A hmono K)
  rw [z49 A hmono hw K] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
lemma z103 [Countable E] (A : Set (Set E))
    (hmono : IsUpperSet A) (hw : z11 A) :
    LowerSemicontinuous (fun p : unitInterval => (law (fun _ : E => p)).real A) := by
  let K := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  intro p a ha
  have ht := (z112 p A hmono hw K).eventually (lt_mem_nhds ha)
  obtain ⟨n, hn⟩ := ht.exists
  have hc := (z274 (K n) (K.finite n) A).continuousAt (x := p)
  filter_upwards [hc.eventually (lt_mem_nhds hn)] with q hq
  exact lt_of_lt_of_le hq (measureReal_mono (fun ω hω => hmono Set.inter_subset_right hω))
lemma z426 [Countable E] {I : Type*} [Finite I]
    (A : I → Set (Set E)) (hmono : ∀ i, IsUpperSet (A i))
    (hw : ∀ i, z11 (A i)) (p : unitInterval) (hp : 0 < p)
    (a : I → ℝ) (ha : ∀ i, a i < (law (fun _ : E => p)).real (A i)) :
    ∃ q : unitInterval, (p : ℝ) / 2 ≤ q ∧ q < p ∧
      ∀ i, a i < (law (fun _ : E => q)).real (A i) := by
  have hall : ∀ᶠ q in 𝓝 p, ∀ i, a i < (law (fun _ : E => q)).real (A i) :=
    Filter.eventually_all.mpr fun i =>
      z103 (A i) (hmono i) (hw i) p (a i) (ha i)
  have hp' : (0 : ℝ) < p := hp
  have hhalf : ∀ᶠ q : unitInterval in 𝓝 p, (p : ℝ) / 2 < q :=
    continuous_subtype_val.continuousAt.eventually (lt_mem_nhds (by linarith : (p : ℝ) / 2 < p))
  have : NeBot (𝓝[<] p) := nhdsLT_neBot_of_exists_lt ⟨0, hp⟩
  obtain ⟨q, hq, hqp, hqA⟩ :=
    ((hhalf.filter_mono nhdsWithin_le_nhds).and
      ((show ∀ᶠ q in 𝓝[<] p, q < p from self_mem_nhdsWithin).and
        (hall.filter_mono nhdsWithin_le_nhds))).exists
  exact ⟨q, le_of_lt hq, hqp, hqA⟩
end CriticalPercolation.z0
end
end
end OAI
end
section
namespace OAI
section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Filter Topology
open scoped Topology Classical
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
namespace CriticalPercolation.z0
variable {E : Type*}
lemma z199 (s : Set E) (hs : s.Finite) (A : Set (Set E)) :
    MeasurableSet {ω | s ∩ ω ∈ A} := by
  let := hs.fintype
  have hf : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
    measurable_pi_lambda _ (fun edge => measurable_set_mem edge.val)
  have he : {ω : Set E | s ∩ ω ∈ A} =
      (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) ⁻¹'
        {u : Set s | Subtype.val '' u ∈ A} := by
    ext ω
    have hi : Subtype.val '' (Subtype.val ⁻¹' ω : Set s) = s ∩ ω := by
      ext e
      simp
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hi]
  rw [he]
  exact hf (.of_discrete)
lemma z61 [Countable E] (A : Set (Set E))
    (hmono : IsUpperSet A) (hw : z11 A) : MeasurableSet A := by
  let K := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  rw [← z49 A hmono hw K]
  exact MeasurableSet.iUnion fun n => z199 (K n) (K.finite n) A
end CriticalPercolation.z0
end
end
end OAI
end
section
namespace OAI
section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Filter Topology
open scoped Topology Classical
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
def z17 (o : V) (n : ℕ) : Set (Set E) :=
  {ω | ∃ K : Set V, K.Finite ∧ K ⊆ G.cluster ω o ∧ n ≤ K.ncard}
lemma z24 (o : V) (n : ℕ) : IsUpperSet (G.z17 o n) := by
  rintro ω ω' h ⟨K, hK, hKω, hn⟩
  exact ⟨K, hK, hKω.trans (G.cluster_mono h o), hn⟩
lemma z30 (o : V) (n : ℕ) :
    z0.z11 (G.z17 o n) := by
  rintro ω ⟨K, hK, hKω, hn⟩
  obtain ⟨s, hs, hsω, hKs⟩ := G.z119 hK hKω
  exact ⟨s, hs, hsω, K, hK, hKs, hn⟩
lemma z342 [Countable E] (o : V) (n : ℕ) :
    MeasurableSet (G.z17 o n) :=
  z0.z61 _ (G.z24 o n)
    (G.z30 o n)
lemma z258 (o : V) : Antitone (G.z17 o) := by
  rintro m n h ω ⟨K, hK, hKω, hn⟩
  exact ⟨K, hK, hKω, h.trans hn⟩
lemma z29 (o : V) (n : ℕ) :
    G.z14 o ⊆ G.z17 o n := by
  intro ω hω
  obtain ⟨K, hKω, hK, hn⟩ := hω.exists_subset_ncard_eq n
  exact ⟨K, hK, hKω, hn.ge⟩
lemma Aut.z514 (φ : G.Aut) (o : V) (n : ℕ) :
    (fun ω : Set E => φ.edge '' ω) ⁻¹' G.z17 (φ.vertex o) n =
      G.z17 o n := by
  ext ω
  simp only [Set.mem_preimage, z17, Set.mem_ofPred_eq]
  rw [← φ.cluster_image]
  constructor
  · rintro ⟨K, hK, hKω, hn⟩
    refine ⟨φ.vertex.symm '' K, hK.image _, ?_, ?_⟩
    · rintro _ ⟨v, hv, rfl⟩
      obtain ⟨w, hw, rfl⟩ := hKω hv
      simpa using hw
    · rwa [Set.ncard_image_of_injective _ φ.vertex.symm.injective]
  · rintro ⟨K, hK, hKω, hn⟩
    exact ⟨φ.vertex '' K, hK.image _, Set.image_mono hKω,
      by rwa [Set.ncard_image_of_injective _ φ.vertex.injective]⟩
end CriticalPercolation.z2
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
namespace CriticalPercolation
namespace z0
variable {E : Type*}
lemma z92 (X : Set E) :
    @Measurable (Set E) (Set E) (blockSigma X) inferInstance (fun ω => ω∩X) := by
  have hh := z77 Xᶜ (∅ : Set E)
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
end z0
namespace z2
open z0
variable {V E : Type*} (G : z2 V E)
variable [Countable V] [Countable E]
end z2
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
namespace CriticalPercolation.z8
open scoped Classical
variable {E : Type*} [Fintype E]
lemma z601 (w : E → Prop → ℝ) (x y : E → Prop) :
    density w x * density w y = density w (x ⊓ y) * density w (x ⊔ y) := by
  unfold density
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  simp only [Pi.inf_apply, Pi.sup_apply]
  by_cases hx : x e <;> by_cases hy : y e <;> simp [hx, hy, mul_comm]
lemma expect_mul_ge (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hpos : ∀ e b, 0 ≤ w e b) (f g : (E → Prop) → ℝ)
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω)
    (hf : Monotone f) (hg : Monotone g) :
    expect w f * expect w g ≤ expect w (fun ω => f ω * g ω) := by
  have h := fkg f g (density w) (fun ω => density_nonneg hpos ω) hf0 hg0 hf hg
    (fun x y => le_of_eq (z601 w x y))
  simpa only [expect, sum_density w hw, one_mul] using h
end CriticalPercolation.z8
end
end
end OAI
end
section
namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
namespace CriticalPercolation.z8
open scoped Classical
variable {E : Type*} [Fintype E]
noncomputable def prob (w : E → Prop → ℝ) (P : Set E → Prop) : ℝ :=
  expect w (fun ω => if P ω then 1 else 0)
end CriticalPercolation.z8
end
end
end OAI
end
section
namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical
namespace CriticalPercolation.z8
open scoped Classical
variable {E A : Type*} [Fintype E] [Fintype A]
noncomputable def pin (w : E → A → ℝ) (e : E) (b : A) : E → A → ℝ :=
  Function.update w e (fun a => if a = b then 1 else 0)
omit [Fintype E] in
lemma pin_normalized (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1) (e : E) (b : A) :
    ∀ j, ∑ a, pin w e b j a = 1 := by
  intro j
  by_cases h : j = e
  · subst j; simp [pin]
  · simpa [pin,h] using hw j
omit [Fintype A] in
lemma density_pin (w : E → A → ℝ) (e : E) (b : A) (ω : E → A) :
    density (pin w e b) ω =
      (if ω e = b then 1 else 0)*∏ j ∈ (Finset.univ : Finset E).erase e, w j (ω j) := by
  rw [density,← Finset.prod_erase_mul _ _ (Finset.mem_univ e)]
  simp only [pin,Function.update_self]
  have he : (∏ j ∈ (Finset.univ : Finset E).erase e, Function.update w e
      (fun a => if a = b then 1 else 0) j (ω j)) =
      ∏ j ∈ (Finset.univ : Finset E).erase e, w j (ω j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [he,mul_comm]
lemma z488 (w : E → A → ℝ) (e : E) (b : A) (f : (E → A) → ℝ) :
    expect w (fun ω => if ω e = b then f ω else 0) = w e b*expect (pin w e b) f := by
  unfold expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [density_pin]
  dsimp only
  by_cases h : ω e = b
  · rw [if_pos h,if_pos h,one_mul]
    rw [density,← Finset.prod_erase_mul _ _ (Finset.mem_univ e),h]
    ring
  · simp [h]
end CriticalPercolation.z8
end
end
end OAI
end
section
namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical
namespace CriticalPercolation.FiniteVariance
end CriticalPercolation.FiniteVariance
namespace CriticalPercolation.z8
open scoped Classical
variable {E : Type*} [Fintype E]
lemma z81 (w : E → Prop → ℝ) (e : E) (b : Prop) (f : (E → Prop) → ℝ) :
    expect w (fun ω => if ω e = b then f ω else 0) = w e b*expect (pin w e b) f := by
  convert z488 w e b f using 1
  congr 1
  funext ω
  by_cases h : ω e = b <;> simp [h]
end CriticalPercolation.z8
end
end
end OAI
end
section
namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical
namespace CriticalPercolation.z8
variable {E A : Type*} [Fintype E] [Fintype A]
lemma z465 (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (e : E) (b : A) : expect w (fun ω => if ω e = b then 1 else 0) = w e b := by
  classical
  have ht (ω : E → A) : density w ω * (if ω e = b then 1 else 0) =
      ∏ j, w j (ω j) * (if j = e then if ω j = b then 1 else 0 else 1) := by
    rw [Finset.prod_mul_distrib]
    simp [density]
  simp only [expect, ht]
  rw [← Fintype.prod_sum (fun j a => w j a * (if j = e then if a = b then 1 else 0 else 1))]
  have hs (j : E) : (∑ a, w j a * (if j = e then if a = b then 1 else 0 else 1)) =
      if j = e then w e b else 1 := by
    split_ifs with he
    · subst j; simp
    · simp [hw]
  simp only [hs]
  simp
end CriticalPercolation.z8
namespace CriticalPercolation.z8
open scoped Classical
variable {E A : Type*} [Fintype E] [Fintype A]
lemma z459 (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1)
    (e : E) (b : A) (f : (E → A) → ℝ) :
    expect w (fun ω => if ω e = b then f ω else 0) =
      w e b * expect w (fun ω => f (Function.update ω e b)) := by
  have hid : (fun ω => if ω e = b then f ω else 0) =
      (fun ω => (if ω e = b then (1:ℝ) else 0)*f (Function.update ω e b)) := by
    funext ω
    split_ifs with h
    · have hu : Function.update ω e b = ω := by rw [← h]; exact Function.update_eq_self _ _
      simp [hu]
    · simp
  rw [hid]
  have hI : DependsOn (fun ω : E → A => if ω e = b then (1:ℝ) else 0) ({e} : Set E) := by
    intro ω ω' heq
    dsimp only
    rw [heq e (Set.mem_singleton e)]
  have hF : DependsOn (fun ω => f (Function.update ω e b)) ({e} : Set E)ᶜ := by
    intro ω ω' heq
    change f (Function.update ω e b) = f (Function.update ω' e b)
    congr 1
    funext j
    by_cases hj : j = e
    · subst j; simp
    · simp only [Function.update_of_ne hj]
      exact heq j hj
  rw [expect_indep w hw _ hI hF]
  congr 1
  exact z465 w hw e b
end CriticalPercolation.z8
namespace CriticalPercolation.z8
open scoped Classical
variable {E : Type*} [Fintype E]
lemma z307 (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (b : Prop) (hb : w e b ≠ 0) (f : (E → Prop) → ℝ) :
    expect (pin w e b) f = expect w (fun ω => f (Function.update ω e b)) := by
  apply mul_left_cancel₀ hb
  exact (z488 w e b f).symm.trans (z459 w hw e b f)
lemma z495 (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (a b : Prop) (ha : w e a ≠ 0) (hb : w e b ≠ 0) (f : (E → Prop) → ℝ) :
    expect (pin w e b) f = expect (pin w e a) (fun ω => f (Function.update ω e b)) := by
  rw [z307 w hw e b hb,z307 w hw e a ha]
  simp only [Function.update_idem]
end CriticalPercolation.z8
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
lemma z225 (f : V → ℝ) (ρ : ℝ) (hρ : 0≤ρ)
    (hf : ∀ ⦃v w⦄, G.z7.Adj v w → |f v-f w|≤ρ)
    {v w : V} {n : ℕ} (hw : w∈G.z5 v n) : |f w-f v|≤n*ρ := by
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
lemma z207 {S T : Set V} (h : S⊆T) :
    G.z4 S⊆G.z4 T := by
  intro e he v hv
  exact h (he v hv)
end CriticalPercolation.z2
namespace CriticalPercolation.Corridor
open z2
variable {V E : Type*} (G : z2 V E) (ξ : V → Point) (j h : ℝ)
end CriticalPercolation.Corridor
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.z2
open CriticalPercolation.z0
variable {V E : Type*} (G : z2 V E)
def seedHitEvent (B T : Set V) : Set (Set E) :=
  ⋃ b∈B, G.hitEvent b T
lemma z340 [Countable V] [Countable E] (B T : Set V) :
    MeasurableSet (G.seedHitEvent B T) :=
  MeasurableSet.iUnion fun b => MeasurableSet.iUnion fun _ => G.z194 b T
lemma z549 (B T : Set V) : IsUpperSet (G.seedHitEvent B T) := by
  intro ω τ hωτ hω
  obtain ⟨b,hb,hω⟩ := Set.mem_iUnion₂.mp hω
  exact Set.mem_iUnion₂.mpr ⟨b,hb,G.z155 b T hωτ hω⟩
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
lemma z70 (S : Set V) (ω : Set E) (u v : V) :
    (G.z1 (ω∩G.z4 S)).Adj u v ↔
    (G.z1 ω).Adj u v ∧ u∈S ∧ v∈S := by
  constructor
  · rintro ⟨⟨b,hb,hend⟩,hne⟩
    exact ⟨⟨⟨b,hb.1,hend⟩,hne⟩,hb.2 u (by rw [hend]; simp),
      hb.2 v (by rw [hend]; simp)⟩
  · rintro ⟨⟨⟨b,hb,hend⟩,hne⟩,hu,hv⟩
    refine ⟨⟨b,⟨hb,?_⟩,hend⟩,hne⟩
    intro w hw
    rw [hend] at hw
    rcases (Sym2.mem_iff.mp hw) with rfl|rfl <;> assumption
lemma z35 (S : Set V) (ω : Set E) {a b : V}
    (w : (G.z1 ω).Walk a b) (hw : ∀ x∈w.support,x∈S) :
    (G.z1 (ω∩G.z4 S)).Reachable a b := by
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a c b hac w ih =>
    have hc : c∈S := hw c (by simp only [SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr w.start_mem_support)
    have ha : a∈S := hw a (by simp)
    exact ((G.z70 S ω a c).mpr ⟨hac,ha,hc⟩).reachable.trans
      (ih (fun x hx => hw x (by simp only [SimpleGraph.Walk.support_cons,List.mem_cons]; exact Or.inr hx)))
def coordinateMove (t z : V → ℝ) (m : ℕ) (e : ℝ) (y : V) (s : ℝ) : Set (Set E) :=
  {ω | ∃ a∈G.z5 y m, ∃ b, ∃ w : (G.z1 ω).Walk a b,
    (∀ x∈w.support, |t x-t y| ≤ 100 ∧ |z x-z y| ≤ 100) ∧
    |t b-(t y+1)| ≤ e/4 ∧ |z b-(z y+s)| ≤ e/4}
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
structure OpenRay (ω : Set E) where
  vertex : ℕ → V
  injective : Function.Injective vertex
  adjacent : ∀ n, (G.z1 ω).Adj (vertex n) (vertex (n+1))
structure RayPrefix (ω : Set E) (o : V) (n : ℕ) where
  vertex : Fin (n+1) → V
  start : vertex 0=o
  adjacent : ∀ i : Fin n, (G.z1 ω).Adj (vertex i.castSucc) (vertex i.succ)
  injective : Function.Injective vertex
  ball : ∀ i, vertex i∈G.z5 o i.val
lemma RayPrefix.ext {ω : Set E} {o : V} {n : ℕ} {a b : G.RayPrefix ω o n}
    (h : a.vertex = b.vertex) : a = b := by cases a; cases b; congr
lemma z68 {ω : Set E} {a b : V} (w : (G.z1 ω).Walk a b) :
    ∀ n≤w.length, w.getVert n∈G.z5 a n := by
  intro n
  induction n with
  | zero => intro _; simpa using G.z45 a 0
  | succ n ih =>
    intro hn
    exact G.z186 (ih (by omega))
      (G.openGraph_mono (Set.subset_univ _) (w.adj_getVert_succ (by omega)))
lemma z551 (hl : G.LocallyFinite) {ω : Set E} {o : V}
    (hi : (G.cluster ω o).Infinite) (n : ℕ) : Nonempty (G.RayPrefix ω o n) := by
  have hn : ¬G.cluster ω o⊆G.z5 o n := fun h => hi ((G.z19 hl o n).subset h)
  obtain ⟨b,hb,hbn⟩ := Set.not_subset.mp hn
  obtain ⟨w⟩ := hb
  let p := w.toPath
  have hlen : n<p.val.length := by
    by_contra hn
    have h := G.z68 p.val p.val.length le_rfl
    rw [SimpleGraph.Walk.getVert_length] at h
    exact hbn (G.z26 o (by omega) h)
  refine ⟨{ vertex := fun i => p.val.getVert i.val
            start := p.val.getVert_zero
            adjacent := ?_
            injective := ?_
            ball := ?_ }⟩
  · intro i
    exact p.val.adj_getVert_succ (by omega)
  · intro i j hij
    apply Fin.ext
    exact p.property.getVert_injOn (by change i.val≤p.val.length; omega)
      (by change j.val≤p.val.length; omega) hij
  · intro i
    exact G.z68 p.val i.val (by omega)
lemma z591 (hl : G.LocallyFinite) (ω : Set E) (o : V) (n : ℕ) :
    Finite (G.RayPrefix ω o n) := by
  let := (G.z19 hl o n).to_subtype
  let f : G.RayPrefix ω o n → (Fin (n+1) → G.z5 o n) := fun p i =>
    ⟨p.vertex i,G.z26 o (by omega) (p.ball i)⟩
  apply Finite.of_injective f
  intro p q hpq
  apply RayPrefix.ext G
  funext i
  exact congrArg Subtype.val (congrFun hpq i)
def RayPrefix.restrict {ω : Set E} {o : V} {i j : ℕ} (h : i≤j)
    (p : G.RayPrefix ω o j) : G.RayPrefix ω o i where
  vertex k := p.vertex (Fin.castLE (Nat.succ_le_succ h) k)
  start := p.start
  adjacent k := p.adjacent (Fin.castLE h k)
  injective := by
    intro x y heq
    exact Fin.ext (congrArg (fun z : Fin (j+1) => z.val) (p.injective heq))
  ball k := p.ball (Fin.castLE (Nat.succ_le_succ h) k)
lemma RayPrefix.restrict_refl {ω : Set E} {o : V} {i : ℕ} (p : G.RayPrefix ω o i) :
    p.restrict G le_rfl=p := by apply RayPrefix.ext G; rfl
lemma RayPrefix.restrict_trans {ω : Set E} {o : V} {i j k : ℕ}
    (hij : i≤j) (hjk : j≤k) (p : G.RayPrefix ω o k) :
    (p.restrict G hjk).restrict G hij=p.restrict G (hij.trans hjk) := by apply RayPrefix.ext G; rfl
theorem z364 (hl : G.LocallyFinite) {ω : Set E} {o : V}
    (hi : (G.cluster ω o).Infinite) : ∃ r : G.OpenRay ω, r.vertex 0=o := by
  let : ∀ n, Finite (G.RayPrefix ω o n) := G.z591 hl ω o
  let : ∀ n, Nonempty (G.RayPrefix ω o n) := G.z551 hl hi
  obtain ⟨f,hf⟩ := exists_seq_forall_proj_of_forall_finite (α := fun n => G.RayPrefix ω o n)
    (fun {i j} h p => RayPrefix.restrict G (i := i) (j := j) h p)
    (fun {_} p => p.restrict_refl G) (fun {_ _ _} hij hjk p => p.restrict_trans G hij hjk)
    (fun _ _ => Set.toFinite _)
  let r : ℕ → V := fun n => (f n).vertex ⟨n,Nat.lt_succ_self n⟩
  have hcoh : ∀ i j (h : i≤j), (f j).vertex ⟨i,by omega⟩=r i := by
    intro i j hij
    have h := congrArg (fun p : G.RayPrefix ω o i => p.vertex ⟨i,Nat.lt_succ_self i⟩) (hf hij)
    exact h
  have hinj : Function.Injective r := by
    intro i j hij
    have hh : (f (max i j)).vertex ⟨i,by omega⟩=(f (max i j)).vertex ⟨j,by omega⟩ := by
      rw [hcoh i _ (le_max_left _ _),hcoh j _ (le_max_right _ _),hij]
    exact congrArg Fin.val ((f (max i j)).injective hh)
  have hadj : ∀ n, (G.z1 ω).Adj (r n) (r (n+1)) := by
    intro n
    have h := (f (n+1)).adjacent ⟨n,Nat.lt_succ_self n⟩
    change (G.z1 ω).Adj ((f (n+1)).vertex ⟨n,by omega⟩)
      ((f (n+1)).vertex ⟨n+1,by omega⟩) at h
    simpa only [hcoh n (n+1) (Nat.le_succ n),hcoh (n+1) (n+1) le_rfl] using h
  exact ⟨⟨r,hinj,hadj⟩,(f 0).start⟩
theorem z380 (hl : G.LocallyFinite) (ω : Set E) (S : Set V) (o : V)
    (hi : (G.cluster (ω∩G.z4 S) o).Infinite) :
    ∃ r : G.OpenRay ω, r.vertex 0=o ∧ ∀ n, r.vertex n∈S := by
  obtain ⟨r,hr⟩ := G.z364 hl hi
  refine ⟨⟨r.vertex,r.injective,fun n => G.openGraph_mono Set.inter_subset_left (r.adjacent n)⟩,
    hr,?_⟩
  intro n
  exact ((G.z70 S ω _ _).mp (r.adjacent n)).2.1
lemma z130 (hl : G.LocallyFinite) (u v : V → ℝ) (ω : Set E)
    (h : ¬∃ r : G.OpenRay ω, ∃ U W : ℝ,
      ∀ n, |u (r.vertex n)|≤U ∧ |v (r.vertex n)|≤W) :
    ∀ U W : ℝ, ∀ a,
      (G.cluster (ω∩G.z4 {x | |u x|≤U ∧ |v x|≤W}) a).Finite := by
  intro U W a
  by_contra hi
  obtain ⟨r,_hr,hS⟩ := G.z380 hl ω _ a hi
  exact h ⟨r,U,W,hS⟩
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.z2
open z0
variable {V E : Type*} (G : z2 V E)
def restrictedSeed (A T : Set V) (S : Set E) : Set (Set E) :=
  {ω | ω∩S∈G.seedHitEvent A T}
lemma z257 [Countable V] [Countable E] (A T : Set V) (S : Set E) :
    MeasurableSet[blockSigma S] (G.restrictedSeed A T S) :=
  (G.z340 A T).preimage (z92 S)
lemma z343 [Countable V] [Countable E] (A T : Set V) (S : Set E) :
    MeasurableSet (G.restrictedSeed A T S) :=
  (blockSigma_le S) _ (G.z257 A T S)
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical
namespace CriticalPercolation.Corridor
open z2
variable {V : Type*}
def sign (b : Bool) : ℝ := if b then 1 else -1
lemma sign_abs (b : Bool) : |sign b|=1 := by cases b <;> norm_num [sign]
end CriticalPercolation.Corridor
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
def boxMove (t z : V → ℝ) (m : ℕ) (precision radius : ℝ) (y : V) (s : ℝ) : Set (Set E) :=
  {ω | ∃ a∈G.z5 y m, ∃ b, ∃ w : (G.z1 ω).Walk a b,
    (∀ x∈w.support, |t x-t y|≤radius ∧ |z x-z y|≤radius) ∧
    |t b-(t y+1)|≤precision ∧ |z b-(z y+s)|≤precision}
lemma z58 {S : Set V} {ω : Set E} {a b : V}
    (w : (G.z1 (ω∩G.z4 S)).Walk a b) (hb : b∈S) :
    ∀ x∈w.support, x∈S := by
  induction w with
  | nil =>
    intro x hx
    simp only [SimpleGraph.Walk.support_nil,List.mem_singleton] at hx
    subst x
    exact hb
  | @cons a c b hac w ih =>
    intro x hx
    rcases (List.mem_cons.mp hx) with hxa|hx
    · rw [hxa]
      exact ((G.z70 S ω a c).mp hac).2.1
    · exact ih hb x hx
lemma z73 (t z : V → ℝ) (m : ℕ) (q B : ℝ) (y : V) (s : ℝ) :
    G.boxMove t z m q B y s=G.restrictedSeed (G.z5 y m)
      {b | (|t b-(t y+1)|≤q ∧ |z b-(z y+s)|≤q) ∧ |t b-t y|≤B ∧ |z b-z y|≤B}
      (G.z4 {x | |t x-t y|≤B ∧ |z x-z y|≤B}) := by
  ext ω
  constructor
  · rintro ⟨a,ha,b,w,hw,ht,hz⟩
    exact Set.mem_iUnion₂.mpr ⟨a,ha,b,G.z35 _ ω w hw,⟨ht,hz⟩,hw b w.end_mem_support⟩
  · intro h
    obtain ⟨a,ha,b,⟨w⟩,hb⟩ := Set.mem_iUnion₂.mp h
    let w' := w.mapLe (G.openGraph_mono Set.inter_subset_left)
    refine ⟨a,ha,b,w',?_,hb.1.1,hb.1.2⟩
    intro x hx
    rw [SimpleGraph.Walk.support_mapLe_eq_support] at hx
    exact G.z58 w hb.2 x hx
lemma z121 (A T : Set V) (S : Set E) : IsUpperSet (G.restrictedSeed A T S) := by
  intro ω τ h hω
  exact G.z549 A T (Set.inter_subset_inter_left S h) hω
lemma z54 (A T : Set V) (S : Set E) :
    z0.z11 (G.restrictedSeed A T S) := by
  intro ω hω
  obtain ⟨a,ha,b,hr,hb⟩ := Set.mem_iUnion₂.mp hω
  obtain ⟨K,hK,hKsub,hKr⟩ := G.z43 hr
  refine ⟨K,hK,fun _ he => (hKsub he).1,?_⟩
  change K∩S∈G.seedHitEvent A T
  rw [Set.inter_eq_left.mpr (fun _ he => (hKsub he).2)]
  exact Set.mem_iUnion₂.mpr ⟨a,ha,b,hKr,hb⟩
lemma boxMove_upper (t z : V → ℝ) (m : ℕ) (q B : ℝ) (y : V) (s : ℝ) :
    IsUpperSet (G.boxMove t z m q B y s) := by
  rw [G.z73]
  exact G.z121 _ _ _
lemma z484 (t z : V → ℝ) (m : ℕ) (q B : ℝ) (y : V) (s : ℝ) :
    z0.z11 (G.boxMove t z m q B y s) := by
  rw [G.z73]
  exact G.z54 _ _ _
lemma z542 [Countable V] [Countable E]
    (t z : V → ℝ) (m : ℕ) (q B : ℝ) (y : V) (s : ℝ) :
    MeasurableSet (G.boxMove t z m q B y s) := by
  rw [G.z73]
  exact G.z343 _ _ _
lemma z556 [Countable E] (t z : V → ℝ) (m : ℕ) (q B : ℝ)
    (o : V) (pc : unitInterval) (hpc : 0<pc) (eta : ℝ)
    (hm : ∀ b : Bool, 1-eta<(z0.law (fun _ : E => pc)).real
      (G.boxMove t z m q B o (Corridor.sign b))) :
    ∃ p : unitInterval, (pc : ℝ)/2≤p ∧ p<pc ∧ ∀ b : Bool,
      1-eta<(z0.law (fun _ : E => p)).real
        (G.boxMove t z m q B o (Corridor.sign b)) :=
  z0.z426 _ (fun _ => G.boxMove_upper _ _ _ _ _ _ _)
    (fun _ => G.z484 _ _ _ _ _ _ _) pc hpc (fun _ => 1-eta) hm
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
def seedDomainTail (A S : Set V) (n : ℕ) : Set (Set E) :=
  ⋃ a∈A, (fun ω : Set E => ω∩G.z4 S) ⁻¹' G.z17 a n
def seedDomainInfinite (A S : Set V) : Set (Set E) :=
  {ω | ∃ a∈A, (G.cluster (ω∩G.z4 S) a).Infinite}
lemma z352 [Countable V] [Countable E] (A S : Set V) (n : ℕ) :
    MeasurableSet (G.seedDomainTail A S n) := by
  have hm : Measurable (fun ω : Set E => ω∩G.z4 S) :=
    (z0.z92 _).mono (z0.blockSigma_le _) le_rfl
  exact MeasurableSet.biUnion (Set.to_countable _) fun a _ =>
    (G.z342 a n).preimage hm
lemma z416 (A S : Set V) : Antitone (G.seedDomainTail A S) := by
  intro n m hnm ω hω
  obtain ⟨a,ha,ht⟩ := Set.mem_iUnion₂.mp hω
  exact Set.mem_iUnion₂.mpr ⟨a,ha,G.z258 a hnm ht⟩
lemma z264 (A S : Set V) (hA : A.Finite) :
    G.seedDomainInfinite A S=⋂ n, G.seedDomainTail A S n := by
  ext ω
  constructor
  · rintro ⟨a,ha,hi⟩
    exact Set.mem_iInter.mpr fun n => Set.mem_iUnion₂.mpr
      ⟨a,ha,G.z29 a n hi⟩
  · intro hω
    by_contra hn
    have hf : ∀ a∈A, (G.cluster (ω∩G.z4 S) a).Finite := by
      intro a ha
      by_contra hi
      exact hn ⟨a,ha,hi⟩
    let K := ⋃ a∈A, G.cluster (ω∩G.z4 S) a
    have hK : K.Finite := hA.biUnion hf
    obtain ⟨a,ha,L,hL,hLa,hLn⟩ := Set.mem_iUnion₂.mp
      (Set.mem_iInter.mp hω (K.ncard+1))
    have hs : L⊆K := fun x hx => Set.mem_iUnion₂.mpr ⟨a,ha,hLa hx⟩
    have hc := Set.ncard_le_ncard hs hK
    omega
lemma z212 [Countable V] [Countable E]
    (μ : Measure (Set E)) [IsFiniteMeasure μ] (A S : Set V) (hA : A.Finite)
    (r : ℝ) (h : ∀ n, r≤μ.real (G.seedDomainTail A S n)) :
    r≤μ.real (G.seedDomainInfinite A S) := by
  have ht := tendsto_measure_iInter_atTop (μ := μ)
    (fun n => (G.z352 A S n).nullMeasurableSet)
    (G.z416 A S) ⟨0,measure_ne_top _ _⟩
  rw [←G.z264 A S hA] at ht
  exact ge_of_tendsto ((ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht)
    (Filter.Eventually.of_forall h)
lemma RayPrefix.reachable {ω : Set E} {a : V} {n : ℕ} (p : G.RayPrefix ω a n)
    (i : Fin (n+1)) : (G.z1 ω).Reachable a (p.vertex i) := by
  suffices hh : ∀ k, ∀ hk : k<n+1, (G.z1 ω).Reachable a (p.vertex ⟨k,hk⟩) from
    hh i.val i.isLt
  intro k
  induction k with
  | zero =>
    intro hk
    have he : (⟨0,hk⟩ : Fin (n+1))=0 := by ext; simp
    rw [he,p.start]
  | succ k ih =>
    intro hk
    exact (ih (by omega)).trans (p.adjacent ⟨k,by omega⟩).reachable
lemma RayPrefix.z17 {ω : Set E} {a : V} {n : ℕ} (p : G.RayPrefix ω a n) :
    ω∈G.z17 a (n+1) := by
  refine ⟨Set.range p.vertex,Set.finite_range _,?_,?_⟩
  · rintro _ ⟨i,rfl⟩
    exact p.reachable G i
  · rw [Set.ncard_range_of_injective p.injective,Nat.card_fin]
lemma z572 (A S K : Set V) (n : ℕ)
    (hK : ∀ a∈A, G.z5 a n⊆K) {ω : Set E}
    (hω : ω∈G.restrictedSeed A (S\K) (G.z4 S)) :
    ∃ a∈A, ∃ p : G.RayPrefix ω a n, ∀ i, p.vertex i∈S∩K := by
  obtain ⟨a,ha,b,⟨w⟩,hb⟩ := Set.mem_iUnion₂.mp hω
  let p := w.toPath
  let q := p.val.mapLe (G.openGraph_mono Set.inter_subset_left)
  have hlen : n<q.length := by
    by_contra hn
    have h := G.z68 q q.length le_rfl
    rw [SimpleGraph.Walk.getVert_length] at h
    exact hb.2 (hK a ha (G.z26 a (by omega) h))
  let r : G.RayPrefix ω a n := {
    vertex := fun i => q.getVert i.val
    start := q.getVert_zero
    adjacent := fun i => q.adj_getVert_succ (by omega)
    injective := by
      intro i j hij
      apply Fin.ext
      have hpath : q.IsPath := p.property.mapLe _
      exact hpath.getVert_injOn (by change i.val≤q.length; omega)
        (by change j.val≤q.length; omega) hij
    ball := fun i => G.z68 q i.val (by omega) }
  refine ⟨a,ha,r,?_⟩
  intro i
  refine ⟨?_,hK a ha (G.z26 a (by omega) (r.ball i))⟩
  have hs := G.z58 p.val hb.1 (p.val.getVert i.val)
    (p.val.getVert_mem_support i.val)
  simpa only [r,q,SimpleGraph.Walk.mapLe,SimpleGraph.Walk.getVert_map,SimpleGraph.Hom.ofLE_apply] using hs
def z502 {ω : Set E} {a : V} {n : ℕ} (p : G.RayPrefix ω a n)
    (S : Set V) (hS : ∀ i, p.vertex i∈S) :
    G.RayPrefix (ω∩G.z4 S) a n := {
  vertex := p.vertex, start := p.start, injective := p.injective, ball := p.ball
  adjacent := fun i => (G.z70 S ω _ _).mpr
    ⟨p.adjacent i,hS i.castSucc,hS i.succ⟩ }
theorem z238 [Countable V] [Countable E]
    (hl : G.LocallyFinite) (μ : Measure (Set E)) [IsFiniteMeasure μ]
    (A S : Set V) (hA : A.Finite) (Sj Tj : ℕ → Set V) (r : ℝ)
    (hlocal : ∀ K : Set V, K.Finite → ∀ᶠ j in atTop, Sj j∩K⊆S)
    (hescape : ∀ K : Set V, K.Finite → ∀ᶠ j in atTop, Disjoint (Tj j) K)
    (hprob : ∀ j, r≤μ.real (G.restrictedSeed A (Sj j∩Tj j) (G.z4 (Sj j)))) :
    r≤μ.real (G.seedDomainInfinite A S) := by
  apply G.z212 μ A S hA r
  intro n
  let K := ⋃ a∈A, G.z5 a n
  have hK : K.Finite := hA.biUnion (fun a _ => G.z19 hl a n)
  obtain ⟨j,hj,hj'⟩ := ((hlocal K hK).and (hescape K hK)).exists
  apply (hprob j).trans
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω
  have hout : ω∈G.restrictedSeed A (Sj j\K) (G.z4 (Sj j)) := by
    obtain ⟨a,ha,b,hr,hb⟩ := Set.mem_iUnion₂.mp hω
    exact Set.mem_iUnion₂.mpr ⟨a,ha,b,hr,hb.1,fun hk => Set.disjoint_left.mp hj' hb.2 hk⟩
  obtain ⟨a,ha,p,hp⟩ := G.z572 A (Sj j) K n
    (fun a ha x hx => Set.mem_iUnion₂.mpr ⟨a,ha,hx⟩) hout
  have ht := (G.z502 p S (fun i => hj (hp i))).z17 G
  exact Set.mem_iUnion₂.mpr ⟨a,ha,G.z258 a (Nat.le_succ n) ht⟩
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
lemma z503 (ω S : Set E) (o : V) :
    G.cluster (ω ∪ S) o ⊆ G.cluster ω o ∪
      ⋃ e ∈ S, ⋃ v ∈ (G.ends e).toFinset, G.cluster ω v := by
  intro z hz
  have hr := ((G.z1 (ω ∪ S)).reachable_iff_reflTransGen o z).mp hz
  clear hz
  induction hr with
  | refl => exact Or.inl (.refl _)
  | @tail x y hr hxy ih =>
    obtain ⟨⟨e, he, heq⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
    rcases he with he | he
    · have hadj : (G.z1 ω).Adj x y :=
        (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,he,heq⟩,hne⟩
      rcases ih with ho | h
      · exact Or.inl (ho.trans hadj.reachable)
      · obtain ⟨f,hf,h⟩ := Set.mem_iUnion₂.mp h
        obtain ⟨v,hv,hh⟩ := Set.mem_iUnion₂.mp h
        exact Or.inr (Set.mem_iUnion₂.mpr ⟨f,hf,Set.mem_iUnion₂.mpr
          ⟨v,hv,hh.trans hadj.reachable⟩⟩)
    · exact Or.inr (Set.mem_iUnion₂.mpr ⟨e,he,Set.mem_iUnion₂.mpr
        ⟨y,by simp [heq], .refl _⟩⟩)
lemma z300 (ω S : Set E) (hS : S.Finite) :
    ω ∪ S ∈ G.z12 ↔ ω ∈ G.z12 := by
  constructor
  · rintro ⟨o,ho⟩
    by_contra hω
    have hfinite : ∀ v, (G.cluster ω v).Finite :=
      fun v => Set.not_infinite.mp (fun hv => hω ⟨v,hv⟩)
    exact ho (((hfinite o).union (hS.biUnion fun e _ =>
      (G.ends e).toFinset.finite_toSet.biUnion fun v _ => hfinite v)).subset
        (G.z503 ω S o))
  · exact G.z319 Set.subset_union_left
lemma z114 (ω S : Set E) (hS : S.Finite) :
    ω \ S ∈ G.z12 ↔ ω ∈ G.z12 := by
  constructor
  · exact G.z319 Set.sdiff_subset
  · intro hω
    have hh := G.z319 (show ω ⊆ (ω \ S) ∪ S from
      fun e he => by by_cases hs : e ∈ S; exact Or.inr hs; exact Or.inl ⟨he,hs⟩) hω
    exact (G.z300 (ω \ S) S hS).mp hh
theorem z532 [Countable V] [Countable E] (q : E → unitInterval) :
    z0.law q G.z12 = 0 ∨
      z0.law q G.z12 = 1 := by
  apply z0.z34 q G.z12
    G.z37
  intro S hS ω
  have heq : z0.forceOn S ∅ ω = ω \ S := by
    ext e
    change (if e ∈ S then False else e ∈ ω) ↔ (e ∈ ω ∧ e ∉ S)
    split_ifs <;> tauto
  rw [heq]
  exact G.z114 ω S hS
lemma z313 [Countable V] [Countable E] (p : unitInterval)
    (h : 0 < G.law p G.z12) : G.law p G.z12 = 1 := by
  have hh := G.z532 (fun _ => p)
  rw [z0.law_const] at hh
  exact hh.resolve_left (ne_of_gt h)
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
open scoped BigOperators
open scoped Classical ENNReal
open Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical
open Filter Topology
open scoped Topology Classical
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
namespace CriticalPercolation.z0
variable {E : Type*}
lemma z142 (A : Set (Set E)) (hA : IsUpperSet A) :
    Monotone (fun ω : E → Prop => A.indicator (1 : Set E → ℝ) {e | ω e}) := by
  intro ω ω' h
  change (if {e | ω e} ∈ A then (1 : ℝ) else 0) ≤
    (if {e | ω' e} ∈ A then (1 : ℝ) else 0)
  split_ifs with ha hb
  · rfl
  · exact (hb (hA h ha)).elim
  · norm_num
  · rfl
lemma z159 [Fintype E] (q : E → unitInterval) (A : Set (Set E)) :
    (law q).real A = z8.expect (fun e => z28 (q e))
      (fun ω : E → Prop => A.indicator (1 : Set E → ℝ) {e | ω e}) := by
  rw [← z63]
  exact (integral_indicator_one (.of_discrete)).symm
lemma finite_harris [Fintype E] (q : E → unitInterval)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (law q).real A * (law q).real B ≤ (law q).real (A ∩ B) := by
  simp_rw [z159]
  have he : (fun ω : E → Prop => (A ∩ B).indicator (1 : Set E → ℝ) {e | ω e}) =
      (fun ω => A.indicator (1 : Set E → ℝ) {e | ω e} *
        B.indicator (1 : Set E → ℝ) {e | ω e}) := by
    funext ω
    by_cases ha : {e | ω e} ∈ A <;> by_cases hb : {e | ω e} ∈ B <;> simp [ha, hb]
  rw [he]
  exact z8.expect_mul_ge _ (fun e => bitWeight_sum (q e))
    (fun e b => z143 (q e) b) _ _
    (Set.indicator_nonneg (fun _ _ => zero_le_one))
    (Set.indicator_nonneg (fun _ _ => zero_le_one))
    (z142 A hA) (z142 B hB)
lemma z361 (q : E → unitInterval) (s : Set E) (hs : s.Finite)
    (A : Set (Set E)) :
    (law q).real {ω | s ∩ ω ∈ A} =
      (law (fun e : s => q e)).real {ω | Subtype.val '' ω ∈ A} := by
  let := hs.fintype
  have hi (ω : Set E) : Subtype.val '' (Subtype.val ⁻¹' ω : Set s) = s ∩ ω := by
    ext e
    simp
  rw [← z97 q s]
  have hf : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
    measurable_pi_lambda _ (fun edge => measurable_set_mem edge.val)
  simp only [Measure.real]
  rw [Measure.map_apply hf (.of_discrete)]
  simp only [Set.preimage_ofPred_eq, hi]
lemma z354 (q : E → unitInterval) (s : Set E) (hs : s.Finite)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B) :
    (law q).real {ω | s ∩ ω ∈ A} * (law q).real {ω | s ∩ ω ∈ B} ≤
      (law q).real {ω | s ∩ ω ∈ A ∩ B} := by
  let := hs.fintype
  simp_rw [z361 _ s hs]
  exact finite_harris _ _ _ (fun _ _ h => hA (Set.image_mono h))
    (fun _ _ h => hB (Set.image_mono h))
lemma z11.inter {A B : Set (Set E)}
    (hA : z11 A) (hB : z11 B)
    (hAm : IsUpperSet A) (hBm : IsUpperSet B) : z11 (A ∩ B) := by
  rintro ω ⟨hωA, hωB⟩
  obtain ⟨s, hs, hsω, hsA⟩ := hA ω hωA
  obtain ⟨t, ht, htω, htB⟩ := hB ω hωB
  exact ⟨s ∪ t, hs.union ht, Set.union_subset hsω htω,
    hAm Set.subset_union_left hsA, hBm Set.subset_union_right htB⟩
lemma z36 (q : E → unitInterval) (A : Set (Set E))
    (hmono : IsUpperSet A) (hw : z11 A)
    (K : Set.FiniteExhaustion (Set.univ : Set E)) :
    Tendsto (fun n => (law q).real {ω | K n ∩ ω ∈ A})
      atTop (𝓝 ((law q).real A)) := by
  have h := tendsto_measure_iUnion_atTop (μ := law q)
    (z50 A hmono K)
  rw [z49 A hmono hw K] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
theorem z265 [Countable E] (q : E → unitInterval)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hwA : z11 A) (hwB : z11 B) :
    (law q).real A * (law q).real B ≤ (law q).real (A ∩ B) := by
  let K := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  exact le_of_tendsto_of_tendsto
    ((z36 q A hA hwA K).mul
      (z36 q B hB hwB K))
    (z36 q (A ∩ B) (hA.inter hB)
      (hwA.inter hwB hA hB) K)
    (Eventually.of_forall fun n => z354 q (K n) (K.finite n) A B hA hB)
end CriticalPercolation.z0
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace SimpleGraph.Walk
open scoped _root_.SimpleGraph _root_.SimpleGraph.Walk
variable {V : Type*} {H : SimpleGraph V}
lemma z201 (f : V → ℝ) (D T : ℝ) (hD : 0≤D)
    (hf : ∀ ⦃x y⦄, H.Adj x y → |f x-f y|≤D)
    {a b : V} (w : H.Walk a b) (ha : f a<T) (hb : T≤f b) :
    ∃ x, ∃ p : H.Walk a x, p.support⊆w.support ∧
      (∀ v∈p.support, f v≤T+D) ∧ T≤f x := by
  induction w with
  | nil => exact (not_le_of_gt ha hb).elim
  | @cons a c b hac w ih =>
    by_cases hc : T≤f c
    · refine ⟨c,hac.toWalk,?_,?_,hc⟩
      · intro v hv
        simp only [SimpleGraph.Adj.support_toWalk,List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl|rfl
        · exact (_root_.SimpleGraph.Walk.cons hac w).start_mem_support
        · exact List.mem_cons_of_mem a w.start_mem_support
      · intro v hv
        simp only [SimpleGraph.Adj.support_toWalk,List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl|rfl
        · linarith
        · have hh := (abs_le.mp (hf hac)).1
          linarith
    · obtain ⟨x,p,hp,hpb,hpx⟩ := ih (lt_of_not_ge hc) hb
      refine ⟨x,_root_.SimpleGraph.Walk.cons hac p,?_,?_,hpx⟩
      · intro v hv
        rcases List.mem_cons.mp hv with hv|hv
        · exact List.mem_cons.mpr (Or.inl hv)
        · exact List.mem_cons.mpr (Or.inr (hp hv))
      · intro v hv
        rcases List.mem_cons.mp hv with hv|hv
        · rw [hv]
          linarith
        · exact hpb v hv
end SimpleGraph.Walk
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
def axisExit (u v : V → ℝ) (A : Set V) (L W D : ℝ) (b : Bool) : Set (Set E) :=
  G.restrictedSeed A {x | L≤Corridor.sign b*u x ∧ Corridor.sign b*u x≤L+D ∧
    |u x|≤L+D ∧ |v x|≤W} (G.z4 {x | |u x|≤L+D ∧ |v x|≤W})
lemma axisExit_upper (u v : V → ℝ) (A : Set V) (L W D : ℝ) (b : Bool) :
    IsUpperSet (G.axisExit u v A L W D b) := G.z121 _ _ _
lemma z66 (u v : V → ℝ) (A : Set V) (L W D : ℝ) (b : Bool) :
    z0.z11 (G.axisExit u v A L W D b) :=
  G.z54 _ _ _
lemma axisExit_iff (u v : V → ℝ) (A : Set V) (L W D : ℝ) (b : Bool) (ω : Set E) :
    ω∈G.axisExit u v A L W D b ↔
      ∃ a∈A, ∃ x, ∃ w : (G.z1 ω).Walk a x,
        (∀ y∈w.support, |u y|≤L+D ∧ |v y|≤W) ∧
        L≤Corridor.sign b*u x ∧ Corridor.sign b*u x≤L+D := by
  constructor
  · intro h
    obtain ⟨a,ha,x,⟨w⟩,hx⟩ := Set.mem_iUnion₂.mp h
    refine ⟨a,ha,x,w.mapLe (G.openGraph_mono Set.inter_subset_left),?_,hx.1,hx.2.1⟩
    intro y hy
    rw [SimpleGraph.Walk.support_mapLe_eq_support] at hy
    exact G.z58 w hx.2.2 y hy
  · rintro ⟨a,ha,x,w,hw,hx⟩
    exact Set.mem_iUnion₂.mpr ⟨a,ha,x,G.z35 _ ω w hw,
      hx.1,hx.2,hw x w.end_mem_support⟩
lemma z284 (u v : V → ℝ) (A : Set V) (L W D : ℝ)
    (hD : 0≤D) (hu : ∀ ⦃x y⦄, G.z7.Adj x y → |u x-u y|≤D)
    {ω : Set E} {a x : V} (ha : a∈A) (hal : |u a|<L)
    (w : (G.z1 ω).Walk a x) (hx : L≤|u x|)
    (hv : ∀ y∈w.support, |v y|≤W) :
    ω∈G.axisExit u v A L W D true ∪ G.axisExit u v A L W D false := by
  have hu' : ∀ ⦃x y⦄, (G.z1 ω).Adj x y → |abs (u x)-abs (u y)|≤D := by
    intro x y hxy
    exact (abs_abs_sub_abs_le _ _).trans (hu (G.openGraph_mono (Set.subset_univ _) hxy))
  obtain ⟨y,p,hp,hpb,hpy⟩ := _root_.OAI.SimpleGraph.Walk.z201 (fun x => |u x|) D L hD hu' w hal hx
  have hpath : ∀ z∈p.support, |u z|≤L+D ∧ |v z|≤W :=
    fun z hz => ⟨hpb z hz,hv z (hp hz)⟩
  by_cases hy : 0≤u y
  · apply Or.inl
    apply (G.axisExit_iff u v A L W D true ω).mpr
    refine ⟨a,ha,y,p,hpath,?_,?_⟩
    · simpa [Corridor.sign,abs_of_nonneg hy] using hpy
    · simpa [Corridor.sign,abs_of_nonneg hy] using hpb y p.end_mem_support
  · apply Or.inr
    apply (G.axisExit_iff u v A L W D false ω).mpr
    have hy' : u y≤0 := (lt_of_not_ge hy).le
    refine ⟨a,ha,y,p,hpath,?_,?_⟩
    · simpa [Corridor.sign,abs_of_nonpos hy'] using hpy
    · simpa [Corridor.sign,abs_of_nonpos hy'] using hpb y p.end_mem_support
lemma z427 [Countable E] (q : E → unitInterval)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hwA : z0.z11 A)
    (hwB : z0.z11 B)
    (a : ℝ) (ha : 0≤a) (hu : 1-a^2<(z0.law q).real (A∪B)) :
    1-a<(z0.law q).real A ∨ 1-a<(z0.law q).real B := by
  have hH := z0.z265 q A B hA hB hwA hwB
  have hBmeas := z0.z61 B hB hwB
  have hunion := measureReal_union_add_inter (s := A) hBmeas (μ := z0.law q)
    (measure_ne_top _ _) (measure_ne_top _ _)
  have hAl : (z0.law q).real A≤1 := measureReal_le_one
  have hBl : (z0.law q).real B≤1 := measureReal_le_one
  by_contra hn
  push Not at hn
  have hm : a^2≤(1-(z0.law q).real A)*(1-(z0.law q).real B) := by
    nlinarith [mul_le_mul (by linarith : a≤1-(z0.law q).real A)
      (by linarith : a≤1-(z0.law q).real B) ha (by linarith : 0≤1-(z0.law q).real A)]
  nlinarith
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
lemma z188 (ω : Set E) (S : Set V) {a : V} (ha : a∈S) :
    G.cluster (ω∩G.z4 S) a⊆S := by
  rintro b ⟨w⟩
  exact G.z58 w.reverse ha b w.reverse.start_mem_support
lemma z387 (u v : V → ℝ) (W L : ℝ) (ω : Set E) (a : V)
    (ha : |v a|≤W)
    (hi : (G.cluster (ω∩G.z4 {x | |v x|≤W}) a).Infinite)
    (hbox : (G.cluster (ω∩G.z4 {x | |u x|≤L ∧ |v x|≤W}) a).Finite) :
    ∃ b∈G.cluster (ω∩G.z4 {x | |v x|≤W}) a, L < |u b| := by
  by_contra hn
  push Not at hn
  apply hi
  apply hbox.subset
  rintro b ⟨w⟩
  let w' := w.mapLe (G.openGraph_mono Set.inter_subset_left)
  apply G.z35 _ ω w'
  intro x hx
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hx
  have hr : x∈G.cluster (ω∩G.z4 {x | |v x|≤W}) a := (w.takeUntil x hx).reachable
  exact ⟨hn x hr,G.z188 ω _ ha hr⟩
lemma z374 (u v : V → ℝ) (A : Set V) (W L D : ℝ)
    (hD : 0≤D) (hu : ∀ ⦃x y⦄, G.z7.Adj x y → |u x-u y|≤D)
    (hA : ∀ a∈A, |u a|<L ∧ |v a|≤W)
    {ω : Set E} (hi : ∃ a∈A, (G.cluster (ω∩G.z4 {x | |v x|≤W}) a).Infinite)
    (hbox : ∀ a∈A, (G.cluster (ω∩G.z4 {x | |u x|≤L ∧ |v x|≤W}) a).Finite) :
    ω∈G.axisExit u v A L W D true∪G.axisExit u v A L W D false := by
  obtain ⟨a,ha,hi⟩ := hi
  obtain ⟨b,⟨w⟩,hb⟩ := G.z387 u v W L ω a (hA a ha).2 hi (hbox a ha)
  apply G.z284 u v A L W D hD hu ha (hA a ha).1
    (w.mapLe (G.openGraph_mono Set.inter_subset_left)) hb.le
  intro x hx
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hx
  exact G.z188 ω _ (hA a ha).2 (w.takeUntil x hx).reachable
def stripPercolates (v : V → ℝ) (W : ℝ) : Set (Set E) :=
  {ω | ω∩G.z4 {x | |v x|≤W}∈G.z12}
def someStripPercolates (v : V → ℝ) : Set (Set E) :=
  ⋃ n : ℕ, G.stripPercolates v n
lemma z321 [Countable V] [Countable E] (v : V → ℝ) (W : ℝ) :
    MeasurableSet (G.stripPercolates v W) := by
  exact G.z37.preimage ((z0.z92 _).mono (z0.blockSigma_le _) le_rfl)
lemma z208 [Countable V] [Countable E] (v : V → ℝ) :
    MeasurableSet (G.someStripPercolates v) :=
  MeasurableSet.iUnion (fun n => G.z321 v n)
lemma z368 (v : V → ℝ) (W : ℝ) (ω S : Set E) (hS : S.Finite) :
    ω\S∈G.stripPercolates v W ↔ ω∈G.stripPercolates v W := by
  change (ω\S)∩G.z4 {x | |v x|≤W}∈G.z12 ↔ _
  have heq : (ω\S)∩G.z4 {x | |v x|≤W}=
      (ω∩G.z4 {x | |v x|≤W})\S := by ext e; simp only [Set.mem_inter_iff,Set.mem_sdiff]; tauto
  rw [heq]
  exact G.z114 _ S hS
lemma z276 [Countable V] [Countable E]
    (v : V → ℝ) (q : E → unitInterval) :
    z0.law q (G.someStripPercolates v)=0 ∨
      z0.law q (G.someStripPercolates v)=1 := by
  apply z0.z34 q _ (G.z208 v)
  intro S hS ω
  have heq : z0.forceOn S ∅ ω=ω\S := by
    ext e
    change (if e∈S then False else e∈ω) ↔ e∈ω ∧ e∉S
    split_ifs <;> tauto
  rw [heq]
  simp only [someStripPercolates,Set.mem_iUnion]
  exact exists_congr (fun n => G.z368 v n ω S hS)
def seedStripInfinite (v : V → ℝ) (A : Set V) (W : ℝ) : Set (Set E) :=
  {ω | ∃ a∈A, (G.cluster (ω∩G.z4 {x | |v x|≤W}) a).Infinite}
lemma z91 (v : V → ℝ) {A B : Set V} (hAB : A⊆B)
    {W U : ℝ} (hWU : W≤U) : G.seedStripInfinite v A W⊆G.seedStripInfinite v B U := by
  rintro ω ⟨a,ha,hi⟩
  exact ⟨a,hAB ha,hi.mono (G.cluster_mono
    (Set.inter_subset_inter_right _ (G.z207 (fun _ hx => hx.trans hWU))) a)⟩
lemma z269 (hc : G.z7.Connected) (v : V → ℝ) (o : V) :
    (⋃ n : ℕ, G.seedStripInfinite v (G.z5 o n) n)=G.someStripPercolates v := by
  ext ω
  constructor
  · intro h
    obtain ⟨n,a,_ha,hi⟩ := Set.mem_iUnion.mp h
    exact Set.mem_iUnion.mpr ⟨n,a,hi⟩
  · intro h
    obtain ⟨n,a,hi⟩ := Set.mem_iUnion.mp h
    obtain ⟨r,hr⟩ := G.z48 (hc o a)
    refine Set.mem_iUnion.mpr ⟨max n r,?_⟩
    exact G.z91 v (G.z26 o (le_max_right n r))
      (by exact_mod_cast le_max_left n r) ⟨a,hr,hi⟩
theorem z249 [Countable V] [Countable E]
    (hc : G.z7.Connected) (hl : G.LocallyFinite)
    (v : V → ℝ) (o : V) (q : E → unitInterval)
    (hpos : 0<z0.law q (G.someStripPercolates v))
    (eps : ℝ) (heps : 0<eps) :
    ∃ m : ℕ, ∃ W : ℝ, 0≤W ∧
      (∀ a∈G.z5 o m, |v a|≤W) ∧
      1-eps<(z0.law q).real (G.seedStripInfinite v (G.z5 o m) W) := by
  have hone := (G.z276 v q).resolve_left (ne_of_gt hpos)
  let A := fun n : ℕ => G.seedStripInfinite v (G.z5 o n) n
  have hmono : Monotone A := fun n r hn => G.z91 v
    (G.z26 o hn) (Nat.cast_le.mpr hn)
  have ht := tendsto_measure_iUnion_atTop (μ := z0.law q) hmono
  have heq : (⋃ n, A n)=G.someStripPercolates v := G.z269 hc v o
  rw [heq,hone] at ht
  have hreal := (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞)≠⊤)).comp ht
  have hnear : ∀ᶠ n in atTop, 1-eps<(z0.law q).real (A n) :=
    hreal.eventually (lt_mem_nhds (by simpa using heps : 1-eps<ENNReal.toReal 1))
  obtain ⟨m,hm⟩ := hnear.exists
  obtain ⟨M,hM⟩ := ((G.z19 hl o m).image (fun a => |v a|)).bddAbove
  refine ⟨m,max (m : ℝ) M,?_,?_,?_⟩
  · exact (Nat.cast_nonneg m).trans (le_max_left _ _)
  · intro a ha
    exact (hM (Set.mem_image_of_mem _ ha)).trans (le_max_right _ _)
  · apply hm.trans_le
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    exact measure_mono (G.z91 v (Set.Subset.refl _) (le_max_left _ _))
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
def parallelCoordinate (u v : V → ℝ) (a b : ℝ) (x : V) : ℝ := a*u x+b*v x
def z10 (u v : V → ℝ) (a b : ℝ) (x : V) : ℝ := -b*u x+a*v x
def longStripExit (u v : V → ℝ) (A : Set V) (W L a b : ℝ) : Set (Set E) :=
  G.restrictedSeed A
    ({x | |z10 u v a b x|≤W}∩{x | L≤|parallelCoordinate u v a b x|})
    (G.z4 {x | |z10 u v a b x|≤W})
lemma z454 {a b : ℝ} (h : a^2+b^2=1) :
    -1≤a ∧ a≤1 ∧ -1≤b ∧ b≤1 := by
  have ha : a^2≤1 := by nlinarith [sq_nonneg b]
  have hb : b^2≤1 := by nlinarith [sq_nonneg a]
  constructor
  · nlinarith [sq_nonneg (a+1)]
  constructor
  · nlinarith [sq_nonneg (a-1)]
  constructor <;> nlinarith [sq_nonneg (b+1),sq_nonneg (b-1)]
theorem z389 [Countable V] [Countable E]
    (hl : G.LocallyFinite) (μ : Measure (Set E)) [IsFiniteMeasure μ]
    (u v : V → ℝ) (A : Set V) (hA : A.Finite) (W r : ℝ)
    (hW : 0<W) (hr : 0<r)
    (hnull : ∀ a b : ℝ, a^2+b^2=1 →
      μ (G.stripPercolates (z10 u v a b) (2*W))=0) :
    ∃ N : ℕ, ∀ L : ℝ, (N : ℝ)≤L → ∀ a b : ℝ, a^2+b^2=1 →
      μ.real (G.longStripExit u v A W L a b)<r := by
  by_contra hn
  push Not at hn
  choose L hL a b hab hprob using hn
  have hseq : ∀ n, (a n,b n)∈Set.Icc ((-1 : ℝ),(-1 : ℝ)) (1,1) := by
    intro n
    have h := z454 (hab n)
    exact ⟨⟨h.1,h.2.2.1⟩,h.2.1,h.2.2.2⟩
  obtain ⟨c,_hc,φ,hφ,hc⟩ := isCompact_Icc.tendsto_subseq hseq
  have ha : Tendsto (fun n => a (φ n)) atTop (𝓝 c.1) := (continuous_fst.tendsto c).comp hc
  have hb : Tendsto (fun n => b (φ n)) atTop (𝓝 c.2) := (continuous_snd.tendsto c).comp hc
  have hunit : c.1^2+c.2^2=1 := by
    apply tendsto_nhds_unique ((ha.pow 2).add (hb.pow 2))
    simpa only [hab] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have hpar : ∀ x, Tendsto (fun n => parallelCoordinate u v (a (φ n)) (b (φ n)) x)
      atTop (𝓝 (parallelCoordinate u v c.1 c.2 x)) := fun x =>
    (ha.mul_const (u x)).add (hb.mul_const (v x))
  have hnorm : ∀ x, Tendsto (fun n => z10 u v (a (φ n)) (b (φ n)) x)
      atTop (𝓝 (z10 u v c.1 c.2 x)) := fun x =>
    (hb.neg.mul_const (u x)).add (ha.mul_const (v x))
  have hLtop : Tendsto (fun n => L (φ n)) atTop atTop :=
    tendsto_atTop_mono (fun n => hL (φ n))
      (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
  let Sj := fun n => {x | |z10 u v (a (φ n)) (b (φ n)) x|≤W}
  let Tj := fun n => {x | L (φ n)≤|parallelCoordinate u v (a (φ n)) (b (φ n)) x|}
  let S := {x | |z10 u v c.1 c.2 x|≤2*W}
  have hlocal : ∀ K : Set V, K.Finite → ∀ᶠ n in atTop, Sj n∩K⊆S := by
    intro K hK
    have he : ∀ᶠ n in atTop, ∀ x∈K,
        |z10 u v (a (φ n)) (b (φ n)) x|≤W → x∈S := by
      apply hK.eventually_all.mpr
      intro x _hx
      by_cases hx : x∈S
      · exact Eventually.of_forall (fun _ _ => hx)
      · have hh : W < |z10 u v c.1 c.2 x| := by
          change ¬|z10 u v c.1 c.2 x|≤2*W at hx
          linarith
        filter_upwards [(hnorm x).abs.eventually (lt_mem_nhds hh)] with n hn
        exact fun hnx => False.elim (not_lt_of_ge hnx hn)
    exact he.mono fun n hn x hx => hn x hx.2 hx.1
  have hescape : ∀ K : Set V, K.Finite → ∀ᶠ n in atTop, Disjoint (Tj n) K := by
    intro K hK
    have he : ∀ᶠ n in atTop, ∀ x∈K,
        |parallelCoordinate u v (a (φ n)) (b (φ n)) x|<L (φ n) := by
      apply hK.eventually_all.mpr
      intro x _hx
      let M := |parallelCoordinate u v c.1 c.2 x|+1
      have hm : |parallelCoordinate u v c.1 c.2 x|<M := by dsimp [M]; linarith
      filter_upwards [(hpar x).abs.eventually (gt_mem_nhds hm),
        (tendsto_atTop.mp hLtop M)] with n hn hn'
      exact hn.trans_le hn'
    exact he.mono fun n hn => Set.disjoint_left.mpr (fun x hx hk =>
      not_lt_of_ge hx (hn x hk))
  have hmass := G.z238 hl μ A S hA Sj Tj r hlocal hescape
    (fun n => hprob (φ n))
  have hf : μ (G.seedDomainInfinite A S)=0 := measure_mono_null
    (fun ω hω => by obtain ⟨x,_hx,hx⟩ := hω; exact ⟨x,hx⟩) (hnull c.1 c.2 hunit)
  rw [measureReal_def,hf,ENNReal.toReal_zero] at hmass
  exact not_le_of_gt hr hmass
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
lemma z129 (a r : ℝ) (ha : a≠0) : ∃ m : ℤ, r<a*m := by
  rcases lt_or_gt_of_ne ha with ha|ha
  · obtain ⟨m,hm⟩ := exists_int_lt (r/a)
    exact ⟨m,by have := (lt_div_iff_of_neg ha).mp hm; nlinarith only [this]⟩
  · obtain ⟨m,hm⟩ := exists_int_gt (r/a)
    exact ⟨m,by have := (div_lt_iff₀ ha).mp hm; nlinarith only [this]⟩
lemma z100 (pi : V → ℂ)
    (honto : ∀ m n : ℤ, ∃ x, (pi x).re=m ∧ (pi x).im=n)
    (a b : ℝ) (hab : a^2+b^2=1) :
    ∀ r : ℕ, ∃ x, (r : ℝ)<z10 (fun x => (pi x).re) (fun x => (pi x).im) a b x := by
  intro r
  by_cases ha : a=0
  · have hb : -b≠0 := by intro hh; have : b=0 := neg_eq_zero.mp hh; simp [ha,this] at hab
    obtain ⟨m,hm⟩ := z129 (-b) r hb
    obtain ⟨x,hx,hy⟩ := honto m 0
    exact ⟨x,by simpa [z10,hx,hy] using hm⟩
  · obtain ⟨n,hn⟩ := z129 a r ha
    obtain ⟨x,hx,hy⟩ := honto 0 n
    exact ⟨x,by simpa [z10,hx,hy] using hn⟩
lemma z318 (u v : V → ℝ) (a b : ℝ) (hab : a^2+b^2=1) (x : V) :
    u x=a*parallelCoordinate u v a b x-b*z10 u v a b x ∧
    v x=b*parallelCoordinate u v a b x+a*z10 u v a b x := by
  constructor <;> dsimp [parallelCoordinate,z10] <;>
    nlinarith [congrArg (fun t => t*u x) hab,congrArg (fun t => t*v x) hab]
lemma z573 (u v : V → ℝ) (a b U W : ℝ) (hab : a^2+b^2=1) (x : V)
    (hx : |parallelCoordinate u v a b x|≤U) (hy : |z10 u v a b x|≤W) :
    |u x|≤|a| *U+|b| *W ∧ |v x|≤|b| *U+|a| *W := by
  obtain ⟨he,hf⟩ := z318 u v a b hab x
  constructor
  · rw [he]
    apply (abs_sub _ _).trans
    rw [abs_mul,abs_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg a))
      (mul_le_mul_of_nonneg_left hy (abs_nonneg b))
  · rw [hf]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg b))
      (mul_le_mul_of_nonneg_left hy (abs_nonneg a))
lemma z429 (u v : V → ℝ) (a b : ℝ) (hab : a^2+b^2=1) (ω : Set E)
    (h : ¬∃ r : G.OpenRay ω, ∃ U W : ℝ, ∀ n, |u (r.vertex n)|≤U ∧ |v (r.vertex n)|≤W) :
    ¬∃ r : G.OpenRay ω, ∃ U W : ℝ, ∀ n,
      |parallelCoordinate u v a b (r.vertex n)|≤U ∧ |z10 u v a b (r.vertex n)|≤W := by
  rintro ⟨r,U,W,hr⟩
  exact h ⟨r,|a| *U+|b| *W,|b| *U+|a| *W,fun n => z573 u v a b U W hab _ (hr n).1 (hr n).2⟩
lemma z21 (u v : V → ℝ) (a b : ℝ) (x y : V) :
    parallelCoordinate u v a b x-parallelCoordinate u v a b y=a*(u x-u y)+b*(v x-v y) ∧
    z10 u v a b x-z10 u v a b y= -b*(u x-u y)+a*(v x-v y) := by
  constructor <;> dsimp [parallelCoordinate,z10] <;> ring
lemma z245 (u v : V → ℝ) (a b D : ℝ) (hab : a^2+b^2=1) (hD : 0≤D)
    (hu : ∀ ⦃x y⦄, G.z7.Adj x y → |u x-u y|≤D)
    (hv : ∀ ⦃x y⦄, G.z7.Adj x y → |v x-v y|≤D) :
    (∀ ⦃x y⦄, G.z7.Adj x y → |parallelCoordinate u v a b x-parallelCoordinate u v a b y|≤2*D) ∧
    (∀ ⦃x y⦄, G.z7.Adj x y → |z10 u v a b x-z10 u v a b y|≤2*D) := by
  obtain ⟨ha,ha',hb,hb'⟩ := z454 hab
  have haa : |a|≤1 := abs_le.mpr ⟨ha,ha'⟩
  have hbb : |b|≤1 := abs_le.mpr ⟨hb,hb'⟩
  have bound : ∀ A B : ℝ, |A|≤1 → |B|≤1 → ∀ x y, G.z7.Adj x y →
      |A*(u x-u y)+B*(v x-v y)|≤2*D := by
    intro A B hA hB x y hxy
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul]
    have hu' := mul_le_mul_of_nonneg_left (hu hxy) (abs_nonneg A)
    have hv' := mul_le_mul_of_nonneg_left (hv hxy) (abs_nonneg B)
    nlinarith [mul_le_mul_of_nonneg_right hA hD,mul_le_mul_of_nonneg_right hB hD]
  constructor
  · intro x y hxy
    rw [(z21 u v a b x y).1]
    exact bound a b haa hbb x y hxy
  · intro x y hxy
    rw [(z21 u v a b x y).2]
    exact bound (-b) a (by simpa only [abs_neg] using hbb) haa x y hxy
lemma z407 (u v : V → ℝ) (a b : ℝ) (phi : G.Aut)
    (hu : ∀ x y, u (phi.vertex x)-u (phi.vertex y)=u x-u y)
    (hv : ∀ x y, v (phi.vertex x)-v (phi.vertex y)=v x-v y) :
    (∀ x y, parallelCoordinate u v a b (phi.vertex x)-parallelCoordinate u v a b (phi.vertex y)=
      parallelCoordinate u v a b x-parallelCoordinate u v a b y) ∧
    (∀ x y, z10 u v a b (phi.vertex x)-z10 u v a b (phi.vertex y)=
      z10 u v a b x-z10 u v a b y) := by
  constructor
  · intro x y
    rw [(z21 u v a b _ _).1,(z21 u v a b x y).1,hu,hv]
  · intro x y
    rw [(z21 u v a b _ _).2,(z21 u v a b x y).2,hu,hv]
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open scoped Topology
namespace CriticalPercolation.EuclideanEllipse
def diagonal (a b : ℝ) (z : ℂ) : ℂ := ⟨a*z.re,b*z.im⟩
lemma diagonal_add (a b : ℝ) (z w : ℂ) :
    diagonal a b (z+w)=diagonal a b z+diagonal a b w := by
  apply Complex.ext <;> simp [diagonal,mul_add]
lemma diagonal_sub (a b : ℝ) (z w : ℂ) :
    diagonal a b (z-w)=diagonal a b z-diagonal a b w := by
  apply Complex.ext <;> simp [diagonal,mul_sub]
lemma diagonal_comp (a b c d : ℝ) (z : ℂ) :
    diagonal a b (diagonal c d z)=diagonal (a*c) (b*d) z := by
  apply Complex.ext <;> simp [diagonal,mul_assoc]
lemma diagonal_one (z : ℂ) : diagonal 1 1 z=z := by apply Complex.ext <;> simp [diagonal]
lemma diagonal_neg (a b : ℝ) (z : ℂ) : diagonal a b (-z)= -diagonal a b z := by
  apply Complex.ext <;> simp [diagonal]
lemma z428 (a b M : ℝ) (hM : 0≤M) (ha : |a|≤M) (hb : |b|≤M) (z : ℂ) :
    ‖diagonal a b z‖≤M*‖z‖ := by
  have ha2 : a^2≤M^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hM).mpr ha
  have hb2 : b^2≤M^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hM).mpr hb
  have hsq : ‖diagonal a b z‖^2≤(M*‖z‖)^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply,mul_pow,Complex.sq_norm,Complex.normSq_apply]
    dsimp [diagonal]
    nlinarith [mul_le_mul_of_nonneg_right ha2 (sq_nonneg z.re),
      mul_le_mul_of_nonneg_right hb2 (sq_nonneg z.im)]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mp hsq
def normalize (R W : ℝ) (c : Circle) (z : ℂ) : ℂ :=
  (c : ℂ)*diagonal (1/R) (1/W) ((c : ℂ)⁻¹*z)
def expand (R W : ℝ) (c : Circle) (z : ℂ) : ℂ :=
  (c : ℂ)*diagonal R W ((c : ℂ)⁻¹*z)
lemma normalize_sub (R W : ℝ) (c : Circle) (z w : ℂ) :
    normalize R W c (z-w)=normalize R W c z-normalize R W c w := by
  simp only [normalize,mul_sub,diagonal_sub]
lemma z451 (R W : ℝ) (hR : R≠0) (hW : W≠0) (c : Circle) (z : ℂ) :
    expand R W c (normalize R W c z)=z := by
  simp only [normalize,expand,←mul_assoc,inv_mul_cancel₀ c.coe_ne_zero,one_mul,
    diagonal_comp,mul_one_div_cancel hR,mul_one_div_cancel hW,diagonal_one]
  rw [mul_assoc,mul_inv_cancel_left₀ c.coe_ne_zero]
lemma z584 (R W : ℝ) (hR : R≠0) (hW : W≠0) (c : Circle) (z : ℂ) :
    normalize R W c (expand R W c z)=z := by
  simp only [normalize,expand,←mul_assoc,inv_mul_cancel₀ c.coe_ne_zero,one_mul,
    diagonal_comp,one_div_mul_cancel hR,one_div_mul_cancel hW,diagonal_one]
  rw [mul_assoc,mul_inv_cancel_left₀ c.coe_ne_zero]
lemma z395 (R W : ℝ) (hW : 0<W) (hWR : W≤R) (c : Circle) (z : ℂ) :
    ‖normalize R W c z‖≤‖z‖/W := by
  have hR : 0<R := hW.trans_le hWR
  have h1 : |1/R|≤1/W := by rw [abs_of_pos (one_div_pos.mpr hR)]; exact one_div_le_one_div_of_le hW hWR
  have h2 : |1/W|≤1/W := (abs_of_pos (one_div_pos.mpr hW)).le
  have h := z428 (1/R) (1/W) (1/W) (by positivity) h1 h2 ((c : ℂ)⁻¹*z)
  simpa [normalize,norm_mul,Circle.norm_coe,div_eq_mul_inv,mul_comm]
    using h
lemma expand_norm_le (R W : ℝ) (hW : 0≤W) (hWR : W≤R) (c : Circle) (z : ℂ) :
    ‖expand R W c z‖≤R*‖z‖ := by
  have hR := hW.trans hWR
  have h := z428 R W R hR (by simp [abs_of_nonneg hR])
    (by simpa [abs_of_nonneg hW] using hWR) ((c : ℂ)⁻¹*z)
  simpa only [expand,norm_mul,Circle.norm_coe,norm_inv,inv_one,one_mul] using h
lemma z588 (W : ℝ) (c : Circle) (z : ℂ) :
    normalize W W c z=(1/W : ℝ)•z := by
  have he : ∀ w : ℂ, diagonal (1/W) (1/W) w=(1/W : ℝ)•w := by intro w; apply Complex.ext <;> simp [diagonal]
  rw [normalize,he,mul_smul_comm,←mul_assoc,mul_inv_cancel₀ c.coe_ne_zero,one_mul]
lemma normalize_neg (R W : ℝ) (c : Circle) (z : ℂ) :
    normalize R W (-c) z=normalize R W c z := by
  simp only [normalize,Circle.coe_neg,inv_neg,neg_mul,diagonal_neg,mul_neg,neg_neg]
lemma z504 (R W : ℝ) (c : Circle) (z : ℂ) :
    (((c : ℂ)⁻¹*normalize R W c z).re=(1/R)*((c : ℂ)⁻¹*z).re) ∧
    (((c : ℂ)⁻¹*normalize R W c z).im=(1/W)*((c : ℂ)⁻¹*z).im) := by
  simp [normalize,diagonal]
lemma z594 (R W : ℝ) (c : Circle) : normalize R W c 0=0 := by
  simp [normalize,diagonal,Complex.ext_iff]
lemma z485 (R W : ℝ) (c : Circle) (z w : ℂ) (a b : ℝ) :
    normalize R W c (a•z+b•w)=a•normalize R W c z+b•normalize R W c w := by
  have hd : ∀ q : ℂ, ∀ t : ℝ, diagonal (1/R) (1/W) (t•q)=t•diagonal (1/R) (1/W) q := by
    intro q t
    apply Complex.ext <;> simp [diagonal,Complex.mul_re,Complex.mul_im] <;> ring
  simp only [normalize,mul_add,mul_smul_comm,diagonal_add,hd]
end CriticalPercolation.EuclideanEllipse
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.EuclideanEllipse
lemma z535 (zeta : ℝ) (hzeta : 0<zeta) :
    ∃ S : Finset Circle, ∀ c : Circle, ∃ d∈S, ‖(c : ℂ)-(d : ℂ)‖<zeta := by
  obtain ⟨S,_hS,hSf,hcover⟩ := (isCompact_univ : IsCompact (Set.univ : Set Circle)).finite_cover_balls hzeta
  refine ⟨hSf.toFinset,?_⟩
  intro c
  obtain ⟨d,hd,hcd⟩ := Set.mem_iUnion₂.mp (hcover (Set.mem_univ c))
  change dist (c : ℂ) (d : ℂ)<zeta at hcd
  exact ⟨d,hSf.mem_toFinset.mpr hd,by simpa only [dist_eq_norm] using hcd⟩
lemma z518 (z : ℂ) (hz : z≠0) :
    ∃ c : Circle, z=‖z‖•(c : ℂ) := by
  let c : Circle := ⟨‖z‖⁻¹•z,by
    apply mem_sphere_zero_iff_norm.mpr
    exact norm_smul_inv_norm (𝕜 := ℝ) hz⟩
  refine ⟨c,?_⟩
  change z=‖z‖•(‖z‖⁻¹•z)
  rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz),one_smul]
lemma z606 (S : Finset Circle) (zeta : ℝ)
    (hcover : ∀ c : Circle, ∃ d∈S, ‖(c : ℂ)-(d : ℂ)‖<zeta)
    (z : ℂ) (hlo : 1≤‖z‖) (hhi : ‖z‖≤1+zeta) :
    ∃ d∈S, ‖z-(d : ℂ)‖≤2*zeta := by
  have hz : z≠0 := by intro h; subst z; norm_num at hlo
  obtain ⟨c,hc⟩ := z518 z hz
  obtain ⟨d,hd,hcd⟩ := hcover c
  have he : z-(c : ℂ)=(‖z‖-1)•(c : ℂ) := by rw [sub_smul,one_smul,←hc]
  have hdiff : ‖z-(c : ℂ)‖=‖z‖-1 := by
    rw [he,norm_smul,Real.norm_eq_abs,Circle.norm_coe,mul_one,abs_of_nonneg (by linarith)]
  refine ⟨d,hd,?_⟩
  have htri : ‖z-(d : ℂ)‖≤‖z-(c : ℂ)‖+‖(c : ℂ)-(d : ℂ)‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (z-(c : ℂ)) ((c : ℂ)-(d : ℂ))
  linarith
end CriticalPercolation.EuclideanEllipse
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
def ellipseExit (Psi : V → ℂ) (A : Set V) (zeta : ℝ) (c : Circle) : Set (Set E) :=
  G.restrictedSeed A {x | ‖Psi x-(c : ℂ)‖≤2*zeta ∧ ‖Psi x‖≤1+zeta}
    (G.z4 {x | ‖Psi x‖≤1+zeta})
lemma z324 (Psi : V → ℂ) (A : Set V) (zeta : ℝ) (c : Circle) (ω : Set E) :
    ω∈G.ellipseExit Psi A zeta c ↔ ∃ a∈A, ∃ x, ∃ w : (G.z1 ω).Walk a x,
      (∀ v∈w.support, ‖Psi v‖≤1+zeta) ∧ ‖Psi x-(c : ℂ)‖≤2*zeta := by
  constructor
  · intro h
    obtain ⟨a,ha,x,⟨w⟩,hx⟩ := Set.mem_iUnion₂.mp h
    refine ⟨a,ha,x,w.mapLe (G.openGraph_mono Set.inter_subset_left),?_,hx.1⟩
    intro v hv
    rw [SimpleGraph.Walk.support_mapLe_eq_support] at hv
    exact G.z58 w hx.2 v hv
  · rintro ⟨a,ha,x,w,hw,hx⟩
    exact Set.mem_iUnion₂.mpr ⟨a,ha,x,G.z35 _ ω w hw,hx,hw x w.end_mem_support⟩
lemma z581 (Psi : V → ℂ) (A : Set V) (zeta : ℝ) (c : Circle) :
    IsUpperSet (G.ellipseExit Psi A zeta c) := G.z121 _ _ _
lemma z341 (Psi : V → ℂ) (A : Set V) (zeta : ℝ) (c : Circle) :
    z0.z11 (G.ellipseExit Psi A zeta c) := G.z54 _ _ _
lemma z338 (Psi : V → ℂ) (ω : Set E) (a : V)
    (hi : (G.cluster ω a).Infinite)
    (hbound : (G.cluster (ω∩G.z4 {x | ‖Psi x‖≤1}) a).Finite) :
    ∃ b∈G.cluster ω a, 1<‖Psi b‖ := by
  by_contra hn
  push Not at hn
  apply hi
  apply hbound.subset
  rintro b ⟨w⟩
  apply G.z35 _ ω w
  intro x hx
  exact hn x (w.takeUntil x hx).reachable
theorem z278 (Psi : V → ℂ) (A : Set V) (zeta D : ℝ)
    (hD : 0≤D) (hDz : D≤zeta)
    (hPsi : ∀ ⦃x y⦄, G.z7.Adj x y → ‖Psi x-Psi y‖≤D)
    (hseed : ∀ a∈A, ‖Psi a‖<1) (S : Finset Circle)
    (hcover : ∀ c : Circle, ∃ d∈S, ‖(c : ℂ)-(d : ℂ)‖<zeta)
    {ω : Set E} (hi : ∃ a∈A, (G.cluster ω a).Infinite)
    (hbound : ∀ a∈A, (G.cluster (ω∩G.z4 {x | ‖Psi x‖≤1}) a).Finite) :
    ω∈⋃ c∈S, G.ellipseExit Psi A zeta c := by
  obtain ⟨a,ha,hi⟩ := hi
  obtain ⟨b,⟨w⟩,hb⟩ := G.z338 Psi ω a hi (hbound a ha)
  have hstep : ∀ ⦃x y⦄, (G.z1 ω).Adj x y → |‖Psi x‖-‖Psi y‖|≤D := by
    intro x y hxy
    exact (abs_norm_sub_norm_le _ _).trans (hPsi (G.openGraph_mono (Set.subset_univ _) hxy))
  obtain ⟨x,p,_hp,hpb,hpx⟩ := _root_.OAI.SimpleGraph.Walk.z201 (fun x => ‖Psi x‖) D 1 hD hstep w (hseed a ha) hb.le
  obtain ⟨c,hc,hcx⟩ := EuclideanEllipse.z606 S zeta hcover (Psi x) hpx (by linarith [hpb x p.end_mem_support])
  apply Set.mem_iUnion₂.mpr
  refine ⟨c,hc,(G.z324 Psi A zeta c ω).mpr ⟨a,ha,x,p,?_,hcx⟩⟩
  intro v hv
  linarith [hpb v hv]
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open scoped BigOperators
namespace CriticalPercolation.DiskWinding
def increment (a b : Real.Angle) : ℝ := (b-a).toReal
lemma z187 {a b c : Real.Angle}
    (hab : |increment a b|<Real.pi/4) (hbc : |increment b c|<Real.pi/4)
    (hac : |increment a c|<Real.pi/4) :
    increment a b+increment b c=increment a c := by
  let z := increment a b+increment b c-increment a c
  have hco : (z : Real.Angle)=0 := by
    simp only [z,increment,Real.Angle.coe_sub,Real.Angle.coe_add,Real.Angle.coe_toReal]
    abel
  have hbounded : -Real.pi<z ∧ z≤Real.pi := by
    obtain ⟨habl,habu⟩ := abs_lt.mp hab
    obtain ⟨hbcl,hbcu⟩ := abs_lt.mp hbc
    obtain ⟨hacl,hacu⟩ := abs_lt.mp hac
    dsimp [z]
    constructor <;> linarith [Real.pi_pos]
  have hz := Real.Angle.toReal_coe_eq_self_iff.mpr hbounded
  rw [hco,Real.Angle.toReal_zero] at hz
  dsimp [z] at hz
  linarith
lemma z355 (f : ℕ → ℝ) (K : ℕ) :
    ∑ k∈Finset.range K, (f (k+1)-f k)=f K-f 0 := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ,ih]; ring
lemma cell_balance {a b c d : Real.Angle}
    (hab : |increment a b|<Real.pi/4) (hbc : |increment b c|<Real.pi/4)
    (hac : |increment a c|<Real.pi/4) (had : |increment a d|<Real.pi/4)
    (hdc : |increment d c|<Real.pi/4) :
    increment a b+increment b c=increment a d+increment d c :=
  (z187 hab hbc hac).trans (z187 had hdc hac).symm
theorem z570 (F : ℕ → ℕ → Real.Angle) (N K : ℕ)
    (hcenter : ∀ k≤K, F 0 k=F 0 0)
    (hseam : ∀ i≤N, F i K=F i 0)
    (hhoriz : ∀ i≤N, ∀ k<K, |increment (F i k) (F i (k+1))|<Real.pi/4)
    (hvert : ∀ i<N, ∀ k≤K, |increment (F i k) (F (i+1) k)|<Real.pi/4)
    (hdiag : ∀ i<N, ∀ k<K, |increment (F i k) (F (i+1) (k+1))|<Real.pi/4) :
    ∑ k∈Finset.range K, increment (F N k) (F N (k+1))=0 := by
  have step : ∀ i<N,
      (∑ k∈Finset.range K, increment (F (i+1) k) (F (i+1) (k+1)))=
      ∑ k∈Finset.range K, increment (F i k) (F i (k+1)) := by
    intro i hi
    let v : ℕ → ℝ := fun k => increment (F i k) (F (i+1) k)
    have hver : ∑ k∈Finset.range K, (v (k+1)-v k)=0 := by
      rw [z355]
      dsimp [v]
      rw [hseam i (by omega),hseam (i+1) (by omega),sub_self]
    have heach : ∀ k∈Finset.range K,
        increment (F (i+1) k) (F (i+1) (k+1))=
        increment (F i k) (F i (k+1))+(v (k+1)-v k) := by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have h := cell_balance (hhoriz i (by omega) k hk')
        (hvert i hi (k+1) (by omega)) (hdiag i hi k hk')
        (hvert i hi k (by omega)) (hhoriz (i+1) (by omega) k hk')
      dsimp [v]
      linarith
    rw [Finset.sum_congr rfl heach,Finset.sum_add_distrib,hver,add_zero]
  have all : ∀ i≤N, ∑ k∈Finset.range K, increment (F i k) (F i (k+1))=0 := by
    intro i
    induction i with
    | zero =>
      intro _
      apply Finset.sum_eq_zero
      intro k hk
      rw [hcenter k (by have := Finset.mem_range.mp hk; omega),
        hcenter (k+1) (by have := Finset.mem_range.mp hk; omega)]
      simp [increment]
    | succ i ih =>
      intro hi
      rw [step i (by omega),ih (by omega)]
  exact all N le_rfl
lemma z565 (F : ℕ → Real.Angle) (b : ℕ → ℝ) (K : ℕ)
    (hlift : ∀ k≤K, F k=(b k : Real.Angle))
    (hstep : ∀ k<K, |b (k+1)-b k|<Real.pi) :
    ∑ k∈Finset.range K, increment (F k) (F (k+1))=b K-b 0 := by
  rw [←z355 b K]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [increment,hlift k (by omega),hlift (k+1) (by omega),←Real.Angle.coe_sub]
  exact Real.Angle.toReal_coe_eq_self_iff.mpr ⟨(abs_lt.mp (hstep k hk')).1,
    (abs_lt.mp (hstep k hk')).2.le⟩
theorem z574 (F : ℕ → ℕ → Real.Angle) (N K : ℕ) (b : ℕ → ℝ)
    (hcenter : ∀ k≤K, F 0 k=F 0 0)
    (hseam : ∀ i≤N, F i K=F i 0)
    (hlift : ∀ k≤K, F N k=(b k : Real.Angle))
    (hstep : ∀ k<K, |b (k+1)-b k|<Real.pi)
    (hturn : b K-b 0=2*Real.pi) :
    (∃ i≤N, ∃ k<K, Real.pi/4≤|increment (F i k) (F i (k+1))|) ∨
    (∃ i<N, ∃ k≤K, Real.pi/4≤|increment (F i k) (F (i+1) k)|) ∨
    (∃ i<N, ∃ k<K, Real.pi/4≤|increment (F i k) (F (i+1) (k+1))|) := by
  by_contra hn
  push Not at hn
  have hz := z570 F N K hcenter hseam hn.1 hn.2.1 hn.2.2
  have ht := z565 (F N) b K hlift hstep
  rw [hz,hturn] at ht
  linarith [Real.pi_pos]
lemma z533 (φ e : ℕ → ℝ) (K : ℕ)
    (hmesh : ∀ k<K, |φ (k+1)-φ k|<Real.pi/32)
    (herr : ∀ k≤K, |e k|<Real.pi/8) :
    ∀ k<K, |(2*φ (k+1)+Real.pi+e (k+1))-(2*φ k+Real.pi+e k)|<Real.pi := by
  intro k hk
  obtain ⟨hma,hmb⟩ := abs_lt.mp (hmesh k hk)
  obtain ⟨hea,heb⟩ := abs_lt.mp (herr k (by omega))
  obtain ⟨hfa,hfb⟩ := abs_lt.mp (herr (k+1) (by omega))
  apply abs_lt.mpr
  constructor <;> linarith [Real.pi_pos]
end CriticalPercolation.DiskWinding
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open LinearMap
namespace CriticalPercolation.EllipseLinear
def det (a b c d : ℝ) : ℝ := a*d-b*c
def time (a b c d x y : ℝ) : ℝ := ((d-b)*x+(a-c)*y)/det a b c d
def height (a b c d x y : ℝ) : ℝ := ((d+b)*x-(c+a)*y)/det a b c d
lemma center_left (a b c d : ℝ) (h : det a b c d≠0) :
    time a b c d a b=1 ∧ height a b c d a b=1 := by
  constructor <;> dsimp only [time,height] <;> field_simp [h] <;> unfold det <;> ring
lemma center_right (a b c d : ℝ) (h : det a b c d≠0) :
    time a b c d c d=1 ∧ height a b c d c d= -1 := by
  constructor <;> dsimp only [time,height] <;> field_simp [h] <;> unfold det <;> ring
lemma z412 (θ ψ : ℝ)
    (hsep : Real.pi/4≤|DiskWinding.increment ((2*θ : ℝ) : Real.Angle)
      ((2*ψ : ℝ) : Real.Angle)|) :
    (1 : ℝ)/4≤|det (Real.cos θ) (Real.sin θ) (Real.cos ψ) (Real.sin ψ)| := by
  let t : Real.Angle := ((2*ψ : ℝ) : Real.Angle)-((2*θ : ℝ) : Real.Angle)
  have ht : t=((2*(ψ-θ) : ℝ) : Real.Angle) := by
    dsimp [t]
    rw [←Real.Angle.coe_sub]
    congr 1
    ring
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    (by positivity : 0≤Real.pi/4) (Real.Angle.abs_toReal_le_pi t) hsep
  rw [Real.cos_abs,Real.Angle.cos_toReal,ht,Real.Angle.cos_coe,
    Real.cos_two_mul,Real.cos_pi_div_four] at hcos
  have hsqrt : Real.sqrt 2≤(7 : ℝ)/4 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ)≤2),Real.sqrt_nonneg 2]
  have hsq := Real.sin_sq_add_cos_sq (ψ-θ)
  have hsin : (1 : ℝ)/4≤|Real.sin (ψ-θ)| := by
    nlinarith [sq_abs (Real.sin (ψ-θ)),abs_nonneg (Real.sin (ψ-θ))]
  have heq : det (Real.cos θ) (Real.sin θ) (Real.cos ψ) (Real.sin ψ)=
      Real.sin (ψ-θ) := by rw [Real.sin_sub]; unfold det; ring
  rwa [heq]
lemma row_bound {a b c d : ℝ} (ha : |a|≤1) (hb : |b|≤1)
    (hc : |c|≤1) (hd : |d|≤1) (hdet : (1 : ℝ)/4≤|det a b c d|)
    (x y q : ℝ) (hq : 0≤q) (hx : |x|≤q) (hy : |y|≤q) :
    |time a b c d x y|≤16*q ∧ |height a b c d x y|≤16*q := by
  have hpos : 0 < |det a b c d| := by linarith
  have hdb : |d-b|≤2 := (abs_sub d b).trans (by linarith)
  have hac : |a-c|≤2 := (abs_sub a c).trans (by linarith)
  have hdb' : |d+b|≤2 := (abs_add_le d b).trans (by linarith)
  have hca : |c+a|≤2 := (abs_add_le c a).trans (by linarith)
  have hprod : ∀ z w : ℝ, |z|≤2 → |w|≤q → |z*w|≤2*q := by
    intro z w hz hw
    rw [abs_mul]
    exact mul_le_mul hz hw (abs_nonneg _) (by norm_num)
  constructor
  · unfold time
    rw [abs_div]
    apply (div_le_iff₀ hpos).mpr
    calc
      |(d-b)*x+(a-c)*y|≤|(d-b)*x|+|(a-c)*y| := abs_add_le _ _
      _ ≤4*q := by linarith [hprod (d-b) x hdb hx,hprod (a-c) y hac hy]
      _ ≤16*q*|det a b c d| := by nlinarith
  · unfold height
    rw [abs_div]
    apply (div_le_iff₀ hpos).mpr
    calc
      |(d+b)*x-(c+a)*y|≤|(d+b)*x|+|(c+a)*y| := abs_sub _ _
      _ ≤4*q := by linarith [hprod (d+b) x hdb' hx,hprod (c+a) y hca hy]
      _ ≤16*q*|det a b c d| := by nlinarith
lemma time_sub (a b c d x y x' y' : ℝ) :
    time a b c d x y-time a b c d x' y'=time a b c d (x-x') (y-y') := by
  unfold time; ring
lemma height_sub (a b c d x y x' y' : ℝ) :
    height a b c d x y-height a b c d x' y'=height a b c d (x-x') (y-y') := by
  unfold height; ring
lemma source_budgets {eps : ℝ} (heps : 0<eps) (heps' : eps<1/10) :
    16*(4*(eps/1000))<eps/8 ∧
    16*((1+eps/1000)^2)<30 := by constructor <;> nlinarith
end CriticalPercolation.EllipseLinear
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
def ellipseTime (Psi : V → ℂ) (c d : Circle) (x : V) : ℝ :=
  EllipseLinear.time (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im (Psi x).re (Psi x).im
def ellipseHeight (Psi : V → ℂ) (c d : Circle) (x : V) : ℝ :=
  EllipseLinear.height (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im (Psi x).re (Psi x).im
lemma z59 (c : Circle) : |(c : ℂ).re|≤1 ∧ |(c : ℂ).im|≤1 := by
  constructor
  · exact (Complex.abs_re_le_norm _).trans_eq (Circle.norm_coe c)
  · exact (Complex.abs_im_le_norm _).trans_eq (Circle.norm_coe c)
lemma z33 (Psi : V → ℂ) (c d : Circle)
    (hdet : (1 : ℝ)/4≤|EllipseLinear.det (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im|)
    (x : V) : |ellipseTime Psi c d x|≤16*‖Psi x‖ ∧ |ellipseHeight Psi c d x|≤16*‖Psi x‖ := by
  exact EllipseLinear.row_bound (z59 c).1 (z59 c).2
    (z59 d).1 (z59 d).2 hdet (Psi x).re (Psi x).im
    ‖Psi x‖ (norm_nonneg _) (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)
lemma z31 (Psi : V → ℂ) (c d : Circle) (x y : V) :
    ellipseTime Psi c d x-ellipseTime Psi c d y=
      ellipseTime (fun v => Psi v-Psi y) c d x ∧
    ellipseHeight Psi c d x-ellipseHeight Psi c d y=
      ellipseHeight (fun v => Psi v-Psi y) c d x := by
  constructor
  · exact EllipseLinear.time_sub _ _ _ _ _ _ _ _
  · exact EllipseLinear.height_sub _ _ _ _ _ _ _ _
lemma z386 (Psi : V → ℂ) (c d : Circle)
    (hdet : (1 : ℝ)/4≤|EllipseLinear.det (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im|)
    (D : ℝ) (hPsi : ∀ ⦃x y⦄, G.z7.Adj x y → ‖Psi x-Psi y‖≤D) :
    (∀ ⦃x y⦄, G.z7.Adj x y → |ellipseTime Psi c d x-ellipseTime Psi c d y|≤16*D) ∧
    (∀ ⦃x y⦄, G.z7.Adj x y → |ellipseHeight Psi c d x-ellipseHeight Psi c d y|≤16*D) := by
  constructor
  · intro x y hxy
    rw [(z31 Psi c d x y).1]
    exact (z33 (fun v => Psi v-Psi y) c d hdet x).1.trans (by nlinarith [hPsi hxy])
  · intro x y hxy
    rw [(z31 Psi c d x y).2]
    exact (z33 (fun v => Psi v-Psi y) c d hdet x).2.trans (by nlinarith [hPsi hxy])
theorem z309 (Psi Psi' : V → ℂ) (o : V) (m : ℕ) (c d : Circle)
    (hdet : (1 : ℝ)/4≤|EllipseLinear.det (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im|)
    (eps : ℝ) (heps : 0<eps) (heps' : eps<1/10) (ho : Psi o=0)
    (hpert : ∀ x, ‖Psi x-Psi' x‖≤(eps/1000)*‖Psi' x‖) (b : Bool) :
    G.ellipseExit Psi' (G.z5 o m) (eps/1000) (if b then c else d) ⊆
      G.boxMove (ellipseTime Psi c d) (ellipseHeight Psi c d) m (eps/8) 30 o (Corridor.sign b) := by
  intro ω hω
  obtain ⟨a,ha,x,w,hw,hx⟩ := (G.z324 _ _ _ _ ω).mp hω
  have hzeta : 0<eps/1000 := by positivity
  have hzeta' : eps/1000<1/10000 := by linarith
  have hdet' : EllipseLinear.det (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im≠0 := by
    intro he
    rw [he,abs_zero] at hdet
    norm_num at hdet
  have hto : ellipseTime Psi c d o=0 := by simp [ellipseTime,ho,EllipseLinear.time]
  have hzo : ellipseHeight Psi c d o=0 := by simp [ellipseHeight,ho,EllipseLinear.height]
  have hpath : ∀ y∈w.support, ‖Psi y‖≤(1+eps/1000)^2 := by
    intro y hy
    have htri : ‖Psi y‖≤‖Psi y-Psi' y‖+‖Psi' y‖ := by
      simpa only [sub_add_cancel] using norm_add_le (Psi y-Psi' y) (Psi' y)
    nlinarith [hpert y,hw y hy]
  have hterminal : ‖Psi x-((if b then c else d) : Circle)‖≤4*(eps/1000) := by
    have htri : ‖Psi x-((if b then c else d) : Circle)‖≤
        ‖Psi x-Psi' x‖+‖Psi' x-((if b then c else d) : Circle)‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (Psi x-Psi' x)
        (Psi' x-((if b then c else d) : Circle))
    nlinarith [hpert x,hw x w.end_mem_support,mul_pos hzeta (by linarith : 0<1-eps/1000)]
  have hcenter : EllipseLinear.time (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im
      (((if b then c else d) : Circle) : ℂ).re (((if b then c else d) : Circle) : ℂ).im=1 ∧
      EllipseLinear.height (c : ℂ).re (c : ℂ).im (d : ℂ).re (d : ℂ).im
      (((if b then c else d) : Circle) : ℂ).re (((if b then c else d) : Circle) : ℂ).im=Corridor.sign b := by
    cases b
    · exact EllipseLinear.center_right _ _ _ _ hdet'
    · exact EllipseLinear.center_left _ _ _ _ hdet'
  have hend := z33 (fun v => Psi v-((if b then c else d) : Circle)) c d hdet x
  have htend : |ellipseTime Psi c d x-1|≤eps/8 := by
    rw [←hcenter.1,ellipseTime,EllipseLinear.time_sub]
    exact hend.1.trans ((mul_le_mul_of_nonneg_left hterminal (by norm_num)).trans
      (EllipseLinear.source_budgets heps heps').1.le)
  have hzend : |ellipseHeight Psi c d x-Corridor.sign b|≤eps/8 := by
    rw [←hcenter.2,ellipseHeight,EllipseLinear.height_sub]
    exact hend.2.trans ((mul_le_mul_of_nonneg_left hterminal (by norm_num)).trans
      (EllipseLinear.source_budgets heps heps').1.le)
  refine ⟨a,ha,x,w,?_,?_,?_⟩
  · intro y hy
    rw [hto,hzo,sub_zero,sub_zero]
    have hnorm := z33 Psi c d hdet y
    have hbudget : 16*‖Psi y‖≤30 := (mul_le_mul_of_nonneg_left (hpath y hy) (by norm_num)).trans
      (EllipseLinear.source_budgets heps heps').2.le
    exact ⟨hnorm.1.trans hbudget,hnorm.2.trans hbudget⟩
  · simpa only [hto,zero_add] using htend
  · simpa only [hzo,zero_add] using hzend
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
lemma z308 (u v : V → ℝ) (A : Set V) (L D : ℝ) (b : Bool)
    {W M : ℝ} (h : W≤M) : G.axisExit u v A L W D b⊆G.axisExit u v A L M D b := by
  intro ω hω
  obtain ⟨a,ha,x,w,hw,hx⟩ := (G.axisExit_iff u v A L W D b ω).mp hω
  exact (G.axisExit_iff u v A L M D b ω).mpr
    ⟨a,ha,x,w,fun y hy => ⟨(hw y hy).1,(hw y hy).2.trans h⟩,hx⟩
lemma z217 (u v : V → ℝ) (A : Set V) (Q D : ℝ)
    (hD : 0≤D) (hv : ∀ ⦃x y⦄, G.z7.Adj x y → |v x-v y|≤D)
    {ω : Set E} {a x : V} (ha : a∈A) (hva : |v a|<Q)
    (hw : (G.z1 ω).Reachable a x) (hx : Q≤|v x|) :
    ω∈⋃ n : ℕ, G.axisExit v u A Q n D true∪G.axisExit v u A Q n D false := by
  obtain ⟨w⟩ := hw
  obtain ⟨M,hM⟩ := (w.support.toFinset.finite_toSet.image (fun x => |u x|)).bddAbove
  obtain ⟨n,hn⟩ := exists_nat_gt M
  apply Set.mem_iUnion.mpr
  refine ⟨n,G.z284 v u A Q n D hD hv ha hva w hx ?_⟩
  intro y hy
  exact (hM (Set.mem_image_of_mem _ (by simpa using hy))).trans hn.le
theorem z140 [Countable V] [Countable E]
    (u v : V → ℝ) (A : Set V) (W Q D : ℝ) (q : E → unitInterval) (r : ℝ)
    (hD : 0≤D) (hv : ∀ ⦃x y⦄, G.z7.Adj x y → |v x-v y|≤D)
    (hA : ∀ a∈A, |v a|<Q)
    (hdir : ∀ᵐ ω ∂z0.law q, ∀ a, (G.cluster ω a).Infinite →
      ∀ n : ℕ, ∃ x∈G.cluster ω a, (n : ℝ)<v x)
    (hprob : r<(z0.law q).real (G.seedStripInfinite v A W)) :
    ∃ M : ℕ, r<(z0.law q).real
      (G.axisExit v u A Q M D true∪G.axisExit v u A Q M D false) := by
  let B := fun n : ℕ => G.axisExit v u A Q n D true∪G.axisExit v u A Q n D false
  have hmono : Monotone B := fun n m hnm =>
    Set.union_subset_union (G.z308 v u A Q D true (Nat.cast_le.mpr hnm))
      (G.z308 v u A Q D false (Nat.cast_le.mpr hnm))
  have hsub : G.seedStripInfinite v A W ≤ᵐ[z0.law q] ⋃ n, B n := by
    filter_upwards [hdir] with ω hω
    intro hseed
    obtain ⟨a,ha,hi⟩ := hseed
    have hi' : (G.cluster ω a).Infinite := hi.mono (G.cluster_mono Set.inter_subset_left a)
    obtain ⟨n,hn⟩ := exists_nat_gt Q
    obtain ⟨x,hx,hvx⟩ := hω a hi' n
    exact G.z217 u v A Q D hD hv ha (hA a ha) hx
      (hn.le.trans (hvx.le.trans (le_abs_self _)))
  have hb : r<(z0.law q).real (⋃ n, B n) :=
    hprob.trans_le (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub))
  have ht := tendsto_measure_iUnion_atTop (μ := z0.law q) hmono
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht
  exact (hreal.eventually (lt_mem_nhds hb)).exists
lemma z242 [Countable V] [Countable E]
    (u v : V → ℝ) (A : Set V) (W U D : ℝ) (q : E → unitInterval) (r : ℝ)
    (hD : 0≤D) (hu : ∀ ⦃x y⦄, G.z7.Adj x y → |u x-u y|≤D)
    (hA : ∀ a∈A, |u a|<U ∧ |v a|≤W)
    (hbox : ∀ᵐ ω ∂z0.law q, ∀ a∈A,
      (G.cluster (ω∩G.z4 {x | |u x|≤U ∧ |v x|≤W}) a).Finite)
    (hprob : r<(z0.law q).real (G.seedStripInfinite v A W)) :
    r<(z0.law q).real
      (G.axisExit u v A U W D true∪G.axisExit u v A U W D false) := by
  apply hprob.trans_le
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hbox] with ω hω
  exact fun hseed => G.z374 u v A W U D hD hu hA hseed hω
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
lemma signed_div_abs (b : Bool) (x U : ℝ) (hU : 0<U) :
    |Corridor.sign b*x/U|=|x|/U := by
  rw [abs_div,abs_mul,Corridor.sign_abs,one_mul,abs_of_pos hU]
lemma z394 (b : Bool) (x U D : ℝ) (hU : 0<U)
    (hx : U≤Corridor.sign b*x) (hx' : Corridor.sign b*x≤U+D) :
    |Corridor.sign b*x/U-1|≤D/U := by
  rw [abs_of_nonneg (by exact sub_nonneg.mpr ((le_div_iff₀ hU).mpr (by simpa using hx)))]
  exact (sub_le_iff_le_add).mpr ((div_le_iff₀ hU).mpr (by
    simpa only [add_mul,div_mul_cancel₀ _ hU.ne',one_mul,add_comm] using hx'))
def stripTime (u v : V → ℝ) (U Q : ℝ) (a b : Bool) (x : V) : ℝ :=
  Corridor.sign a*u x/U+Corridor.sign b*v x/Q
def stripHeight (u v : V → ℝ) (U Q : ℝ) (a b : Bool) (x : V) : ℝ :=
  Corridor.sign a*u x/U-Corridor.sign b*v x/Q
lemma z176 (u v : V → ℝ) (U Q : ℝ) (a b : Bool)
    (hU : 0<U) (hQ : 0<Q) (x : V) :
    |stripTime u v U Q a b x|≤|u x|/U+|v x|/Q ∧
    |stripHeight u v U Q a b x|≤|u x|/U+|v x|/Q := by
  constructor
  · exact (abs_add_le _ _).trans_eq (by rw [signed_div_abs a _ _ hU,signed_div_abs b _ _ hQ])
  · exact (abs_sub _ _).trans_eq (by rw [signed_div_abs a _ _ hU,signed_div_abs b _ _ hQ])
lemma z295 (u v : V → ℝ) (U Q D : ℝ) (a b : Bool)
    (hU : 0<U) (hQ : 0<Q)
    (hu : ∀ ⦃x y⦄, G.z7.Adj x y → |u x-u y|≤D)
    (hv : ∀ ⦃x y⦄, G.z7.Adj x y → |v x-v y|≤D) :
    (∀ ⦃x y⦄, G.z7.Adj x y →
      |stripTime u v U Q a b x-stripTime u v U Q a b y|≤D/U+D/Q) ∧
    (∀ ⦃x y⦄, G.z7.Adj x y →
      |stripHeight u v U Q a b x-stripHeight u v U Q a b y|≤D/U+D/Q) := by
  have hsum : ∀ ⦃x y⦄, G.z7.Adj x y →
      |Corridor.sign a*(u x-u y)/U|+|Corridor.sign b*(v x-v y)/Q|≤D/U+D/Q := by
    intro x y hxy
    rw [signed_div_abs a _ _ hU,signed_div_abs b _ _ hQ]
    exact add_le_add (div_le_div_of_nonneg_right (hu hxy) hU.le)
      (div_le_div_of_nonneg_right (hv hxy) hQ.le)
  constructor
  · intro x y hxy
    calc
      _ = |Corridor.sign a*(u x-u y)/U+Corridor.sign b*(v x-v y)/Q| := by
        congr 1; unfold stripTime; ring
      _ ≤ _ := (abs_add_le _ _).trans (hsum hxy)
  · intro x y hxy
    calc
      _ = |Corridor.sign a*(u x-u y)/U-Corridor.sign b*(v x-v y)/Q| := by
        congr 1; unfold stripHeight; ring
      _ ≤ _ := (abs_sub _ _).trans (hsum hxy)
lemma z358 (u v : V → ℝ) (o : V) (m : ℕ)
    (U Q W D eps : ℝ) (a b : Bool) (huo : u o=0) (hvo : v o=0)
    (hU : 0<U) (hQ : 0<Q) (heps : 0<eps) (hep : eps<1/10)
    (hDU : D/U≤eps/1000) (hWQ : W/Q≤eps/1000) :
    G.axisExit u v (G.z5 o m) U W D a ⊆
      G.boxMove (stripTime u v U Q a b) (stripHeight u v U Q a b) m (eps/8) 30 o 1 := by
  intro ω hω
  obtain ⟨x,hx,y,w,hw,hy,hy'⟩ := (G.axisExit_iff u v (G.z5 o m) U W D a ω).mp hω
  have ho : stripTime u v U Q a b o=0 ∧ stripHeight u v U Q a b o=0 := by
    simp [stripTime,stripHeight,huo,hvo]
  have hpath : ∀ x∈w.support,
      |stripTime u v U Q a b x|≤30 ∧ |stripHeight u v U Q a b x|≤30 := by
    intro z hz
    have hb := z176 u v U Q a b hU hQ z
    have h1 := div_le_div_of_nonneg_right (hw z hz).1 hU.le
    have h2 := div_le_div_of_nonneg_right (hw z hz).2 hQ.le
    have huq : (U+D)/U=1+D/U := by rw [add_div,div_self hU.ne']
    rw [huq] at h1
    constructor <;> linarith [hb.1,hb.2]
  have he1 := z394 a (u y) U D hU hy hy'
  have he2 : |Corridor.sign b*v y/Q|≤W/Q := by
    rw [signed_div_abs b _ _ hQ]
    exact div_le_div_of_nonneg_right (hw y w.end_mem_support).2 hQ.le
  refine ⟨x,hx,y,w,?_,?_,?_⟩
  · simpa only [ho.1,ho.2,sub_zero] using hpath
  · rw [ho.1,zero_add]
    have h := abs_add_le (Corridor.sign a*u y/U-1) (Corridor.sign b*v y/Q)
    have heq : stripTime u v U Q a b y-1=(Corridor.sign a*u y/U-1)+Corridor.sign b*v y/Q := by
      unfold stripTime; ring
    rw [heq]
    linarith
  · rw [ho.2,zero_add]
    have h := abs_sub (Corridor.sign a*u y/U-1) (Corridor.sign b*v y/Q)
    have heq : stripHeight u v U Q a b y-1=(Corridor.sign a*u y/U-1)-Corridor.sign b*v y/Q := by
      unfold stripHeight; ring
    rw [heq]
    linarith
lemma z409 (u v : V → ℝ) (o : V) (m : ℕ)
    (U Q M D eps : ℝ) (a b : Bool) (huo : u o=0) (hvo : v o=0)
    (hU : 0<U) (hQ : 0<Q) (heps : 0<eps) (hep : eps<1/10)
    (hMU : M/U≤eps/1000) (hDQ : D/Q≤eps/1000) :
    G.axisExit v u (G.z5 o m) Q M D b ⊆
      G.boxMove (stripTime u v U Q a b) (stripHeight u v U Q a b) m (eps/8) 30 o (-1) := by
  intro ω hω
  obtain ⟨x,hx,y,w,hw,hy,hy'⟩ := (G.axisExit_iff v u (G.z5 o m) Q M D b ω).mp hω
  have ho : stripTime u v U Q a b o=0 ∧ stripHeight u v U Q a b o=0 := by
    simp [stripTime,stripHeight,huo,hvo]
  have hpath : ∀ x∈w.support,
      |stripTime u v U Q a b x|≤30 ∧ |stripHeight u v U Q a b x|≤30 := by
    intro z hz
    have hb := z176 u v U Q a b hU hQ z
    have h1 := div_le_div_of_nonneg_right (hw z hz).1 hQ.le
    have h2 := div_le_div_of_nonneg_right (hw z hz).2 hU.le
    have huq : (Q+D)/Q=1+D/Q := by rw [add_div,div_self hQ.ne']
    rw [huq] at h1
    constructor <;> linarith [hb.1,hb.2]
  have he1 := z394 b (v y) Q D hQ hy hy'
  have he2 : |Corridor.sign a*u y/U|≤M/U := by
    rw [signed_div_abs a _ _ hU]
    exact div_le_div_of_nonneg_right (hw y w.end_mem_support).2 hU.le
  refine ⟨x,hx,y,w,?_,?_,?_⟩
  · simpa only [ho.1,ho.2,sub_zero] using hpath
  · rw [ho.1,zero_add]
    have h := abs_add_le (Corridor.sign a*u y/U) (Corridor.sign b*v y/Q-1)
    have heq : stripTime u v U Q a b y-1=Corridor.sign a*u y/U+(Corridor.sign b*v y/Q-1) := by
      unfold stripTime; ring
    rw [heq]
    linarith
  · rw [ho.2,zero_add]
    have h := abs_sub (Corridor.sign a*u y/U) (Corridor.sign b*v y/Q-1)
    have heq : stripHeight u v U Q a b y-(-1)=Corridor.sign a*u y/U-(Corridor.sign b*v y/Q-1) := by
      unfold stripHeight; ring
    rw [heq]
    linarith
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
lemma z183 (B K d : ℝ) (hd : 0<d) :
    ∃ U : ℝ, 0<U ∧ B<U ∧ K/U<d := by
  obtain ⟨U,hU⟩ := exists_gt (max 0 (max B (K/d)))
  have hU0 : 0<U := (le_max_left _ _).trans_lt hU
  have hBU : B<U := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hU
  have hKU : K/d<U := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hU
  exact ⟨U,hU0,hBU,(div_lt_iff₀ hU0).mpr (by nlinarith [(div_lt_iff₀ hd).mp hKU])⟩
theorem z557 [Countable V] [Countable E]
    (hc : G.z7.Connected) (hl : G.LocallyFinite)
    (u v : V → ℝ) (o : V) (D : ℝ) (p : unitInterval)
    (hD : 0≤D) (huo : u o=0) (hvo : v o=0)
    (hu : ∀ ⦃x y⦄, G.z7.Adj x y → |u x-u y|≤D)
    (hv : ∀ ⦃x y⦄, G.z7.Adj x y → |v x-v y|≤D)
    (hstrip : 0<(z0.law (fun _ : E => p)) (G.someStripPercolates v))
    (hdir : ∀ᵐ ω ∂z0.law (fun _ : E => p),
      ∀ a, (G.cluster ω a).Infinite → ∀ n : ℕ, ∃ x∈G.cluster ω a, (n : ℝ)<v x)
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂z0.law (fun _ : E => p), ∀ a,
      (G.cluster (ω∩G.z4 {x | |u x|≤U ∧ |v x|≤W}) a).Finite)
    (eps eta : ℝ) (heps : 0<eps) (heps' : eps<1/10) (heta : 0<eta) :
    ∃ m : ℕ, ∀ rho : ℝ, 0<rho → ∃ U Q : ℝ, ∃ a b : Bool,
      0<U ∧ 0<Q ∧
      (∀ ⦃x y⦄, G.z7.Adj x y →
        |stripTime u v U Q a b x-stripTime u v U Q a b y|≤rho) ∧
      (∀ ⦃x y⦄, G.z7.Adj x y →
        |stripHeight u v U Q a b x-stripHeight u v U Q a b y|≤rho) ∧
      ∀ s : Bool, 1-eta<(z0.law (fun _ : E => p)).real
        (G.boxMove (stripTime u v U Q a b) (stripHeight u v U Q a b) m (eps/8) 30 o
          (Corridor.sign s)) := by
  obtain ⟨m,W,hW,hseed,hprob⟩ := G.z249 hc hl v o
    (fun _ : E => p) hstrip ((eta/30)^2) (sq_pos_of_pos (by linarith))
  refine ⟨m,?_⟩
  intro rho hrho
  let d := min (eps/1000) (rho/2)
  have hd : 0<d := lt_min (by linarith) (by linarith)
  have hde : d≤eps/1000 := min_le_left _ _
  have hdr : d≤rho/2 := min_le_right _ _
  obtain ⟨Q,hQ,hWQ,hKQ⟩ := z183 W (max W D) d hd
  have hDQ : D/Q≤d := ((div_le_div_of_nonneg_right (le_max_right W D) hQ.le).trans hKQ.le)
  have hWQ' : W/Q≤d := ((div_le_div_of_nonneg_right (le_max_left W D) hQ.le).trans hKQ.le)
  obtain ⟨M,hMprob⟩ := G.z140 u v (G.z5 o m) W Q D
    (fun _ : E => p) (1-(eta/30)^2) hD hv (fun a ha => (hseed a ha).trans_lt hWQ) hdir hprob
  obtain ⟨K,hK⟩ := ((G.z19 hl o m).image (fun x => |u x|)).bddAbove
  obtain ⟨U,hU,hKU,hMU⟩ := z183 K (max (M : ℝ) D) d hd
  have hDU : D/U≤d := ((div_le_div_of_nonneg_right (le_max_right (M : ℝ) D) hU.le).trans hMU.le)
  have hMU' : (M : ℝ)/U≤d := ((div_le_div_of_nonneg_right (le_max_left (M : ℝ) D) hU.le).trans hMU.le)
  have hUprob := G.z242 u v (G.z5 o m) W U D
    (fun _ : E => p) (1-(eta/30)^2) hD hu
    (fun a ha => ⟨(hK (Set.mem_image_of_mem _ ha)).trans_lt hKU,hseed a ha⟩)
    ((hbox U W).mono (fun _ h a _ => h a)) hprob
  have hesq : 1-(eta/10)^2≤1-(eta/30)^2 := by nlinarith [sq_nonneg eta]
  have hsignU := z427 (fun _ : E => p) _ _
    (G.axisExit_upper u v _ U W D true) (G.axisExit_upper u v _ U W D false)
    (G.z66 u v _ U W D true) (G.z66 u v _ U W D false)
    (eta/10) (by linarith) (hesq.trans_lt hUprob)
  have hsignQ := z427 (fun _ : E => p) _ _
    (G.axisExit_upper v u _ Q M D true) (G.axisExit_upper v u _ Q M D false)
    (G.z66 v u _ Q M D true) (G.z66 v u _ Q M D false)
    (eta/10) (by linarith) (hesq.trans_lt hMprob)
  have hbool : ∀ (F : Bool → ℝ), (1-eta/10<F true ∨ 1-eta/10<F false) →
      ∃ a : Bool, 1-eta<F a := by
    intro F h
    rcases h with h|h
    · exact ⟨true,(by linarith : 1-eta<1-eta/10).trans h⟩
    · exact ⟨false,(by linarith : 1-eta<1-eta/10).trans h⟩
  obtain ⟨a,ha⟩ := hbool (fun a => (z0.law (fun _ : E => p)).real
    (G.axisExit u v (G.z5 o m) U W D a)) hsignU
  obtain ⟨b,hb⟩ := hbool (fun b => (z0.law (fun _ : E => p)).real
    (G.axisExit v u (G.z5 o m) Q M D b)) hsignQ
  have hcmesh := G.z295 u v U Q D a b hU hQ hu hv
  have hmesh : D/U+D/Q≤rho := by linarith
  refine ⟨U,Q,a,b,hU,hQ,(fun {_ _} h => (hcmesh.1 h).trans hmesh),
    (fun {_ _} h => (hcmesh.2 h).trans hmesh),?_⟩
  intro s
  cases s
  · apply hb.trans_le
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    exact measure_mono (G.z409 u v o m U Q M D eps a b huo hvo hU hQ heps heps'
      (hMU'.trans hde) (hDQ.trans hde))
  · apply ha.trans_le
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    exact measure_mono (G.z358 u v o m U Q W D eps a b huo hvo hU hQ heps heps'
      (hDU.trans hde) (hWQ'.trans hde))
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Topology
namespace CriticalPercolation.EuclideanEllipse
lemma z493 (R W : ℝ) (c : Circle) (z : ℂ) :
    normalize R W c z=z.re•normalize R W c 1+z.im•normalize R W c Complex.I := by
  have hz : z=z.re•(1 : ℂ)+z.im•Complex.I := by
    apply Complex.ext <;> simp
  rw [hz,z485]
  simp
lemma z446 (R W R' W' : ℝ) (c d : Circle) (q : ℝ) (hq : 0≤q)
    (h1 : ‖normalize R W c 1-normalize R' W' d 1‖≤q)
    (hI : ‖normalize R W c Complex.I-normalize R' W' d Complex.I‖≤q) (z : ℂ) :
    ‖normalize R W c z-normalize R' W' d z‖≤2*q*‖z‖ := by
  have he : normalize R W c z-normalize R' W' d z=
      z.re•(normalize R W c 1-normalize R' W' d 1)+
      z.im•(normalize R W c Complex.I-normalize R' W' d Complex.I) := by
    rw [z493 R W c z,z493 R' W' d z]
    simp only [smul_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖z.re•(normalize R W c 1-normalize R' W' d 1)‖+
      ‖z.im•(normalize R W c Complex.I-normalize R' W' d Complex.I)‖ := norm_add_le _ _
    _ = |z.re| * ‖normalize R W c 1-normalize R' W' d 1‖+
      |z.im| * ‖normalize R W c Complex.I-normalize R' W' d Complex.I‖ := by rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs]
    _ ≤ |z.re| * q+|z.im| * q := add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hI (abs_nonneg _))
    _ ≤ 2*q*‖z‖ := by nlinarith [mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm z) hq,
      mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z) hq]
def diskRadius (W U : ℝ) (p : ℝ×ℝ) : ℝ := W+(U-W)*p.1
def diskNormalize (W U : ℝ) (p : ℝ×ℝ) : ℂ → ℂ :=
  normalize (diskRadius W U p) W (Circle.exp p.2)
def diskExpand (W U : ℝ) (p : ℝ×ℝ) : ℂ → ℂ :=
  expand (diskRadius W U p) W (Circle.exp p.2)
def parameterDisk : Set (ℝ×ℝ) := Set.Icc (0,0) (1,Real.pi)
lemma z117 (W U : ℝ) (hWU : W≤U) {p : ℝ×ℝ} (hp : p∈parameterDisk) :
    W≤diskRadius W U p ∧ diskRadius W U p≤U := by
  obtain ⟨⟨hs,_hφ⟩,hs',_hφ'⟩ := hp
  dsimp [diskRadius]
  constructor <;> nlinarith
lemma z115 (W U : ℝ) (hW : 0<W) (hWU : W≤U) (z : ℂ) :
    ContinuousOn (fun p => diskNormalize W U p z) parameterDisk := by
  have hR : ∀ p∈parameterDisk, diskRadius W U p≠0 := fun p hp =>
    ne_of_gt (hW.trans_le (z117 W U hWU hp).1)
  have hc : Continuous (fun p : ℝ×ℝ => (Circle.exp p.2 : ℂ)) := by
    simp only [Circle.coe_exp]
    fun_prop
  have hcinv : Continuous (fun p : ℝ×ℝ => (Circle.exp p.2 : ℂ)⁻¹) :=
    hc.inv₀ (fun p => (Circle.exp p.2).coe_ne_zero)
  have hRd : ContinuousOn (fun p => 1/diskRadius W U p) parameterDisk := by
    apply continuousOn_const.div
    · unfold diskRadius
      fun_prop
    · exact hR
  unfold diskNormalize normalize diagonal
  apply hc.continuousOn.mul
  have hre := hRd.mul (Complex.continuous_re.comp (hcinv.mul (continuous_const : Continuous (fun _ : ℝ×ℝ => z)))).continuousOn
  have him := (continuousOn_const : ContinuousOn (fun _ : ℝ×ℝ => 1/W) parameterDisk).mul
    (Complex.continuous_im.comp (hcinv.mul (continuous_const : Continuous (fun _ : ℝ×ℝ => z)))).continuousOn
  have hd := (Complex.continuous_ofReal.comp_continuousOn hre).add
    ((Complex.continuous_ofReal.comp_continuousOn him).mul
      (continuousOn_const : ContinuousOn (fun _ : ℝ×ℝ => Complex.I) parameterDisk))
  convert hd using 1
  funext p
  apply Complex.ext <;> simp only [Pi.add_apply,Pi.mul_apply,Function.comp_apply,
    Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,add_zero,zero_add,sub_zero]
theorem z182 (W U zeta : ℝ)
    (hW : 0<W) (hWU : W≤U) (hzeta : 0<zeta) :
    ∃ delta : ℝ, 0<delta ∧ ∀ p∈parameterDisk, ∀ q∈parameterDisk,
      dist p q<delta → ∀ z : ℂ,
        ‖diskNormalize W U p (diskExpand W U q z)-z‖≤zeta*‖z‖ := by
  let F : (ℝ×ℝ) → (ℂ × ℂ) := fun p => (diskNormalize W U p 1,diskNormalize W U p Complex.I)
  have hc : ContinuousOn F parameterDisk := (z115 W U hW hWU 1).prodMk
    (z115 W U hW hWU Complex.I)
  have hcompact : IsCompact parameterDisk := isCompact_Icc
  have hu := hcompact.uniformContinuousOn_of_continuous hc
  have hU : 0<U := hW.trans_le hWU
  obtain ⟨delta,hdelta,hclose⟩ := Metric.uniformContinuousOn_iff.mp hu (zeta/(2*U)) (by positivity)
  refine ⟨delta,hdelta,?_⟩
  intro p hp q hq hpq z
  have h := hclose p hp q hq hpq
  rw [Prod.dist_eq] at h
  have h1 : ‖diskNormalize W U p 1-diskNormalize W U q 1‖≤zeta/(2*U) := by
    have hh := (lt_of_le_of_lt (le_max_left _ _) h).le
    simpa only [F,dist_eq_norm] using hh
  have hI : ‖diskNormalize W U p Complex.I-diskNormalize W U q Complex.I‖≤zeta/(2*U) := by
    have hh := (lt_of_le_of_lt (le_max_right _ _) h).le
    simpa only [F,dist_eq_norm] using hh
  have hnorm := z446 (diskRadius W U p) W (diskRadius W U q) W
    (Circle.exp p.2) (Circle.exp q.2) (zeta/(2*U)) (by positivity) h1 hI (diskExpand W U q z)
  have hqR := z117 W U hWU hq
  have hexpand : ‖diskExpand W U q z‖≤U*‖z‖ :=
    (expand_norm_le (diskRadius W U q) W hW.le hqR.1 (Circle.exp q.2) z).trans
      (mul_le_mul_of_nonneg_right hqR.2 (norm_nonneg _))
  have hcancel : diskNormalize W U q (diskExpand W U q z)=z :=
    z584 _ W (ne_of_gt (hW.trans_le hqR.1)) hW.ne' _ z
  change ‖diskNormalize W U p (diskExpand W U q z)-diskNormalize W U q (diskExpand W U q z)‖≤_ at hnorm
  rw [hcancel] at hnorm
  apply hnorm.trans
  have hmul := mul_le_mul_of_nonneg_left hexpand (by positivity : 0≤2*(zeta/(2*U)))
  convert hmul using 1
  field_simp
end CriticalPercolation.EuclideanEllipse
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
namespace CriticalPercolation.EuclideanEllipse
def gridPoint (N K i k : ℕ) : ℝ×ℝ := ((i : ℝ)/N,(k : ℝ)*Real.pi/K)
lemma gridPoint_mem {N K i k : ℕ} (hN : 0<N) (hK : 0<K) (hi : i≤N) (hk : k≤K) :
    gridPoint N K i k∈parameterDisk := by
  have hNr : 0<(N : ℝ) := Nat.cast_pos.mpr hN
  have hKr : 0<(K : ℝ) := Nat.cast_pos.mpr hK
  have hir : (i : ℝ)≤N := Nat.cast_le.mpr hi
  have hkr : (k : ℝ)≤K := Nat.cast_le.mpr hk
  change (0≤(i : ℝ)/N ∧ 0≤(k : ℝ)*Real.pi/K) ∧ (i : ℝ)/N≤1 ∧ (k : ℝ)*Real.pi/K≤Real.pi
  exact ⟨⟨by positivity,by positivity⟩,(div_le_one hNr).mpr hir,
    (div_le_iff₀ hKr).mpr (by nlinarith [Real.pi_pos])⟩
lemma gridPoint_dist {N K : ℕ} (hN : 0<N) (hK : 0<K) (i k : ℕ) (a b : ℕ)
    (ha : a≤1) (hb : b≤1) :
    dist (gridPoint N K i k) (gridPoint N K (i+a) (k+b)) ≤ max (1/(N : ℝ)) (Real.pi/K) := by
  have hNr : 0<(N : ℝ) := Nat.cast_pos.mpr hN
  have hKr : 0<(K : ℝ) := Nat.cast_pos.mpr hK
  rw [Prod.dist_eq]
  have hfirst : dist (gridPoint N K i k).1 (gridPoint N K (i+a) (k+b)).1≤1/(N : ℝ) := by
    change |(i : ℝ)/N-(i+a : ℕ)/N|≤_
    rw [Nat.cast_add]
    have he : (i : ℝ)/N-((i : ℝ)+a)/N= -(a : ℝ)/N := by ring
    rw [he,abs_div,abs_neg,abs_of_nonneg (Nat.cast_nonneg a),abs_of_pos hNr]
    exact div_le_div_of_nonneg_right (by exact_mod_cast ha) hNr.le
  have hsecond : dist (gridPoint N K i k).2 (gridPoint N K (i+a) (k+b)).2≤Real.pi/K := by
    change |(k : ℝ)*Real.pi/K-(k+b : ℕ)*Real.pi/K|≤_
    rw [Nat.cast_add]
    have he : (k : ℝ)*Real.pi/K-((k : ℝ)+b)*Real.pi/K= -((b : ℝ)*Real.pi)/K := by ring
    rw [he,abs_div,abs_neg,abs_of_nonneg (by positivity : 0≤(b : ℝ)*Real.pi),abs_of_pos hKr]
    apply div_le_div_of_nonneg_right _ hKr.le
    have hb' : (b : ℝ)≤1 := by exact_mod_cast hb
    nlinarith [Real.pi_pos]
  exact max_le_max hfirst hsecond
lemma z590 (delta : ℝ) (hdelta : 0<delta) :
    ∃ N K : ℕ, 0<N ∧ 0<K ∧ max (1/(N : ℝ)) (Real.pi/K)<delta ∧ Real.pi/K<Real.pi/32 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (1/delta)
  obtain ⟨K,hK⟩ := exists_nat_gt (max (Real.pi/delta) 32)
  have hNr : 0<(N : ℝ) := lt_trans (by positivity) hN
  have hKr : 0<(K : ℝ) := lt_trans (by norm_num : (0 : ℝ)<32) ((le_max_right _ _).trans_lt hK)
  have hNm : 1/(N : ℝ)<delta := (div_lt_iff₀ hNr).mpr (by
    have := (div_lt_iff₀ hdelta).mp hN
    nlinarith)
  have hKm : Real.pi/(K : ℝ)<delta := (div_lt_iff₀ hKr).mpr (by
    have := (div_lt_iff₀ hdelta).mp ((le_max_left _ _).trans_lt hK)
    nlinarith)
  have hK32 : Real.pi/(K : ℝ)<Real.pi/32 := div_lt_div_of_pos_left Real.pi_pos (by norm_num)
    ((le_max_right _ _).trans_lt hK)
  exact ⟨N,K,Nat.cast_pos.mp hNr,Nat.cast_pos.mp hKr,max_lt hNm hKm,hK32⟩
lemma z425 (N K k : ℕ) (hK : 0<K) :
    |(gridPoint N K (0 : ℕ) (k+1)).2-(gridPoint N K 0 k).2|=Real.pi/K := by
  change |((k+1 : ℕ) : ℝ)*Real.pi/K-(k : ℝ)*Real.pi/K|=_
  rw [Nat.cast_add,Nat.cast_one]
  have he : ((k : ℝ)+1)*Real.pi/K-(k : ℝ)*Real.pi/K=Real.pi/K := by ring
  rw [he,abs_of_nonneg (by positivity)]
theorem z460 (W U zeta : ℝ) (hW : 0<W) (hWU : W≤U) (hzeta : 0<zeta) :
    ∃ N K : ℕ, 0<N ∧ 0<K ∧ Real.pi/K<Real.pi/32 ∧
      ∀ i≤N, ∀ k≤K, ∀ a≤1, ∀ b≤1, i+a≤N → k+b≤K → ∀ z : ℂ,
        ‖diskNormalize W U (gridPoint N K i k) (diskExpand W U (gridPoint N K (i+a) (k+b)) z)-z‖≤zeta*‖z‖ := by
  obtain ⟨delta,hd,hcomp⟩ := z182 W U zeta hW hWU hzeta
  obtain ⟨N,K,hN,hK,hm,hangle⟩ := z590 delta hd
  refine ⟨N,K,hN,hK,hangle,?_⟩
  intro i hi k hk a ha b hb hia hkb z
  exact hcomp _ (gridPoint_mem hN hK hi hk) _ (gridPoint_mem hN hK hia hkb)
    ((gridPoint_dist hN hK i k a b ha hb).trans_lt hm) z
end CriticalPercolation.EuclideanEllipse
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.EuclideanEllipse
lemma rotated_re (c : Circle) (z : ℂ) :
    ((c : ℂ)⁻¹*z).re=(c : ℂ).re*z.re+(c : ℂ).im*z.im := by
  rw [←Circle.coe_inv,Circle.coe_inv_eq_conj]
  simp [Complex.mul_re]
lemma rotated_im (c : Circle) (z : ℂ) :
    ((c : ℂ)⁻¹*z).im= -(c : ℂ).im*z.re+(c : ℂ).re*z.im := by
  rw [←Circle.coe_inv,Circle.coe_inv_eq_conj]
  simp [Complex.mul_im,add_comm]
lemma norm_rotated (c : Circle) (z : ℂ) : ‖(c : ℂ)⁻¹*z‖=‖z‖ := by
  rw [norm_mul,norm_inv,Circle.norm_coe,inv_one,one_mul]
lemma z305 (R W : ℝ) (hR : R≠0) (hW : W≠0) (c : Circle) (z : ℂ) :
    ((c : ℂ)⁻¹*z).re=R*((c : ℂ)⁻¹*normalize R W c z).re ∧
    ((c : ℂ)⁻¹*z).im=W*((c : ℂ)⁻¹*normalize R W c z).im := by
  obtain ⟨hre,him⟩ := z504 R W c z
  rw [hre,him]
  constructor <;> field_simp
lemma z399 (R W zeta : ℝ) (hR : R≠0) (hW : 0<W)
    (c : Circle) (z : ℂ) (hz : ‖normalize R W c z‖≤1+zeta) :
    |((c : ℂ)⁻¹*z).im|≤W*(1+zeta) := by
  rw [(z305 R W hR hW.ne' c z).2,abs_mul,abs_of_pos hW]
  apply mul_le_mul_of_nonneg_left _ hW.le
  exact ((Complex.abs_im_le_norm _).trans_eq (norm_rotated c _)).trans hz
lemma z499 (R W zeta : ℝ) (hR : 0<R) (hW : W≠0)
    (hzeta : zeta≤1/10000) (c d : Circle)
    (hd : (1 : ℝ)/8≤|((c : ℂ)⁻¹*(d : ℂ)).re|)
    (z : ℂ) (hz : ‖normalize R W c z-(d : ℂ)‖≤2*zeta) :
    R/10≤|((c : ℂ)⁻¹*z).re| := by
  have hdiff : |((c : ℂ)⁻¹*normalize R W c z).re-((c : ℂ)⁻¹*(d : ℂ)).re|≤2*zeta := by
    calc
      _ = |((c : ℂ)⁻¹*(normalize R W c z-(d : ℂ))).re| := by rw [mul_sub,Complex.sub_re]
      _ ≤ ‖(c : ℂ)⁻¹*(normalize R W c z-(d : ℂ))‖ := Complex.abs_re_le_norm _
      _ = ‖normalize R W c z-(d : ℂ)‖ := norm_rotated c _
      _ ≤ 2*zeta := hz
  have ha := abs_sub_abs_le_abs_sub (((c : ℂ)⁻¹*(d : ℂ)).re)
    (((c : ℂ)⁻¹*normalize R W c z).re)
  rw [abs_sub_comm] at ha
  have hmajor : (1 : ℝ)/10≤|((c : ℂ)⁻¹*normalize R W c z).re| := by linarith
  rw [(z305 R W hR.ne' hW c z).1,abs_mul,abs_of_pos hR]
  nlinarith
lemma z486 (theta : ℝ) :
    |((2*theta : ℝ) : Real.Angle).toReal|≤Real.pi*|Real.sin theta| := by
  let t : Real.Angle := ((2*theta : ℝ) : Real.Angle)
  have ht : |t.toReal/2|≤Real.pi/2 := by rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]; exact div_le_div_of_nonneg_right (Real.Angle.abs_toReal_le_pi t) (by norm_num)
  have heq : 2•((t.toReal/2 : ℝ) : Real.Angle)=2•((theta : ℝ) : Real.Angle) := by
    rw [Real.Angle.two_nsmul_coe_div_two,Real.Angle.coe_toReal]
    dsimp [t]
    rw [←Real.Angle.coe_nsmul]
    congr 1
    simp only [two_smul]
    ring
  have hs := Real.Angle.abs_sin_eq_of_two_nsmul_eq heq
  simp only [Real.Angle.sin_coe] at hs
  have hj := Real.mul_abs_le_abs_sin ht
  rw [hs,abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)] at hj
  have hp := Real.pi_pos
  have hm := mul_le_mul_of_nonneg_left hj hp.le
  field_simp at hm
  dsimp [t] at hm
  nlinarith
end CriticalPercolation.EuclideanEllipse
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
lemma z279 (pi : V → ℂ) (A : Set V) (R W zeta : ℝ)
    (hR : 0<R) (hW : 0<W) (hzeta : zeta≤1/10000) (c d : Circle)
    (hd : (1 : ℝ)/8≤|((c : ℂ)⁻¹*(d : ℂ)).re|) :
    G.ellipseExit (EuclideanEllipse.normalize R W c ∘ pi) A zeta d ⊆
      G.longStripExit (fun x => (pi x).re) (fun x => (pi x).im) A
        (W*(1+zeta)) (R/10) (c : ℂ).re (c : ℂ).im := by
  intro ω hω
  obtain ⟨a,ha,x,w,hw,hx⟩ := (G.z324 _ A zeta d ω).mp hω
  have hpath : ∀ y∈w.support, |z10 (fun x => (pi x).re)
      (fun x => (pi x).im) (c : ℂ).re (c : ℂ).im y|≤W*(1+zeta) := by
    intro y hy
    change |-(c : ℂ).im*(pi y).re+(c : ℂ).re*(pi y).im|≤_
    rw [←EuclideanEllipse.rotated_im]
    exact EuclideanEllipse.z399 R W zeta hR.ne' hW c (pi y) (hw y hy)
  apply Set.mem_iUnion₂.mpr
  refine ⟨a,ha,x,G.z35 _ ω w hpath,hpath x w.end_mem_support,?_⟩
  change R/10≤|(c : ℂ).re*(pi x).re+(c : ℂ).im*(pi x).im|
  rw [←EuclideanEllipse.rotated_re]
  exact EuclideanEllipse.z499 R W zeta hR hW.ne' hzeta c d hd (pi x) hx
theorem z262 [Countable V] [Countable E]
    (hl : G.LocallyFinite) (mu : Measure (Set E)) [IsFiniteMeasure mu]
    (pi : V → ℂ) (A : Set V) (hA : A.Finite) (W zeta r : ℝ)
    (hW : 0<W) (hzeta : 0≤zeta) (hzeta' : zeta≤1/10000) (hr : 0<r)
    (hnull : ∀ a b : ℝ, a^2+b^2=1 → ∀ w : ℝ,
      mu (G.stripPercolates (z10 (fun x => (pi x).re) (fun x => (pi x).im) a b) w)=0) :
    ∃ N : ℕ, ∀ R : ℝ, 0<R → 10*(N : ℝ)≤R → ∀ c d : Circle,
      r ≤ mu.real (G.ellipseExit (EuclideanEllipse.normalize R W c ∘ pi) A zeta d) →
      |((c : ℂ)⁻¹*(d : ℂ)).re|<1/8 := by
  obtain ⟨N,hN⟩ := G.z389 hl mu (fun x => (pi x).re)
    (fun x => (pi x).im) A hA (W*(1+zeta)) r (by positivity) hr
    (fun a b hab => hnull a b hab _)
  refine ⟨N,?_⟩
  intro R hR hRN c d hprob
  by_contra hn
  have hunit : (c : ℂ).re^2+(c : ℂ).im^2=1 := by
    have h := Circle.normSq_coe c
    simpa [Complex.normSq_apply,pow_two] using h
  have hsmall := hN (R/10) (by linarith) (c : ℂ).re (c : ℂ).im hunit
  have hmono := ENNReal.toReal_mono (measure_ne_top mu _)
    (measure_mono (G.z279 pi A R W zeta hR hW hzeta' c d (le_of_not_gt hn)))
  exact (not_lt_of_ge (hprob.trans hmono) hsmall).elim
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
namespace CriticalPercolation.EuclideanEllipse
def lineAngle (c : Circle) : Real.Angle := ((2*(c : ℂ).arg : ℝ) : Real.Angle)
def boundaryError (phi : ℝ) (c : Circle) : ℝ :=
  (lineAngle c-((2*phi+Real.pi : ℝ) : Real.Angle)).toReal
lemma circle_arg_re (c : Circle) : Real.cos (c : ℂ).arg=(c : ℂ).re := by
  simpa only [Circle.norm_coe,div_one] using Complex.cos_arg c.coe_ne_zero
lemma circle_arg_im (c : Circle) : Real.sin (c : ℂ).arg=(c : ℂ).im := by
  simpa only [Circle.norm_coe,div_one] using Complex.sin_arg (c : ℂ)
lemma circle_exp_re (phi : ℝ) : (Circle.exp phi : ℂ).re=Real.cos phi := by
  simp only [Circle.coe_exp,Complex.exp_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,sub_zero,Real.exp_zero,one_mul,Complex.mul_im,
    mul_one,add_zero]
lemma circle_exp_im (phi : ℝ) : (Circle.exp phi : ℂ).im=Real.sin phi := by
  simp only [Circle.coe_exp,Complex.exp_im,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,sub_zero,Real.exp_zero,one_mul,Complex.mul_im,
    mul_one,add_zero]
lemma z566 (phi : ℝ) (c : Circle) :
    ((Circle.exp phi : ℂ)⁻¹*(c : ℂ)).re=Real.cos ((c : ℂ).arg-phi) := by
  rw [rotated_re,circle_exp_re,circle_exp_im,Real.cos_sub,circle_arg_re,circle_arg_im]
  ring
lemma z567 (phi : ℝ) (c : Circle)
    (hc : |((Circle.exp phi : ℂ)⁻¹*(c : ℂ)).re|<1/8) :
    |boundaryError phi c|<Real.pi/8 := by
  have he : lineAngle c-((2*phi+Real.pi : ℝ) : Real.Angle)=
      ((2*((c : ℂ).arg-phi-Real.pi/2) : ℝ) : Real.Angle) := by
    rw [lineAngle,←Real.Angle.coe_sub]
    congr 1
    ring
  have hs : |Real.sin ((c : ℂ).arg-phi-Real.pi/2)|<1/8 := by
    rw [Real.sin_sub,Real.cos_pi_div_two,Real.sin_pi_div_two,mul_zero,mul_one,zero_sub,abs_neg]
    rwa [z566] at hc
  have hh := z486 ((c : ℂ).arg-phi-Real.pi/2)
  rw [boundaryError,he]
  exact hh.trans_lt (by nlinarith [Real.pi_pos])
lemma boundary_lift (phi : ℝ) (c : Circle) :
    lineAngle c=((2*phi+Real.pi+boundaryError phi c : ℝ) : Real.Angle) := by
  simp only [Real.Angle.coe_add,boundaryError,Real.Angle.coe_toReal]
  abel
lemma z525 (c : Circle) : boundaryError Real.pi c=boundaryError 0 c := by
  unfold boundaryError
  congr 1
  have he : ((2*Real.pi+Real.pi : ℝ) : Real.Angle)=((Real.pi : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_add,Real.Angle.coe_two_pi,zero_add]
  simp [he]
lemma circle_exp_pi : Circle.exp Real.pi= -(Circle.exp 0) := by
  apply Subtype.ext
  apply Complex.ext
  · simp only [circle_exp_re,Circle.coe_neg,Complex.neg_re,Real.cos_pi,Real.cos_zero]
  · simp only [circle_exp_im,Circle.coe_neg,Complex.neg_im,Real.sin_pi,Real.sin_zero,neg_zero]
lemma z544 (W U s : ℝ) : diskNormalize W U (s,Real.pi)=diskNormalize W U (s,0) := by
  funext z
  change normalize _ W (Circle.exp Real.pi) z=normalize _ W (Circle.exp 0) z
  rw [circle_exp_pi,normalize_neg]
  rfl
lemma z501 (W U phi : ℝ) : diskNormalize W U (0,phi)=diskNormalize W U (0,0) := by
  funext z
  simp only [diskNormalize,diskRadius,mul_zero,add_zero,z588]
end CriticalPercolation.EuclideanEllipse
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
namespace CriticalPercolation.EuclideanEllipse
theorem z220 (W U zeta : ℝ)
    (hW : 0<W) (hWU : W≤U) (hzeta : 0<zeta)
    (chooseCenter : (ℂ → ℂ) → Circle)
    (hboundary : ∀ phi : ℝ,
      |((Circle.exp phi : ℂ)⁻¹*(chooseCenter (normalize U W (Circle.exp phi)) : ℂ)).re|<1/8) :
    ∃ p∈parameterDisk, ∃ q∈parameterDisk,
      (∀ z : ℂ, ‖diskNormalize W U p (diskExpand W U q z)-z‖≤zeta*‖z‖) ∧
      (1 : ℝ)/4≤|EllipseLinear.det
        (chooseCenter (diskNormalize W U p) : ℂ).re (chooseCenter (diskNormalize W U p) : ℂ).im
        (chooseCenter (diskNormalize W U q) : ℂ).re (chooseCenter (diskNormalize W U q) : ℂ).im| := by
  obtain ⟨N,K,hN,hK,hangle,hcomp⟩ := z460 W U zeta hW hWU hzeta
  have hNr : (N : ℝ)≠0 := (Nat.cast_pos.mpr hN).ne'
  have hKr : (K : ℝ)≠0 := (Nat.cast_pos.mpr hK).ne'
  let phi : ℕ → ℝ := fun k => (k : ℝ)*Real.pi/K
  let centers : ℕ → ℕ → Circle := fun i k => chooseCenter (diskNormalize W U (gridPoint N K i k))
  let F : ℕ → ℕ → Real.Angle := fun i k => lineAngle (centers i k)
  have hp0 : phi 0=0 := by simp [phi]
  have hpK : phi K=Real.pi := by dsimp [phi]; field_simp
  have hn : ∀ k, diskNormalize W U (gridPoint N K N k)=normalize U W (Circle.exp (phi k)) := by
    intro k
    simp only [diskNormalize,gridPoint,div_self hNr,diskRadius,mul_one,add_sub_cancel,phi]
  have hc : ∀ k≤K, F 0 k=F 0 0 := by
    intro k _hk
    dsimp [F,centers,gridPoint]
    simp only [Nat.cast_zero,zero_div,zero_mul]
    rw [z501 W U ((k : ℝ)*Real.pi/K)]
  have hs : ∀ i≤N, F i K=F i 0 := by
    intro i _hi
    have he : gridPoint N K i K=((i : ℝ)/N,Real.pi) := by
      simp only [gridPoint]
      congr 1
    have he0 : gridPoint N K i 0=((i : ℝ)/N,0) := by simp [gridPoint]
    dsimp [F,centers]
    rw [he,he0,z544]
  let err : ℕ → ℝ := fun k => boundaryError (phi k) (centers N k)
  let b : ℕ → ℝ := fun k => 2*phi k+Real.pi+err k
  have herr : ∀ k≤K, |err k|<Real.pi/8 := by
    intro k _hk
    apply z567
    simpa only [centers,hn] using hboundary (phi k)
  have hlift : ∀ k≤K, F N k=(b k : Real.Angle) := by
    intro k _hk
    exact boundary_lift (phi k) (centers N k)
  have hmesh : ∀ k<K, |phi (k+1)-phi k|<Real.pi/32 := by
    intro k _hk
    have he := z425 N K k hK
    exact he.trans_lt hangle
  have hstep := DiskWinding.z533 phi err K hmesh herr
  have hturn : b K-b 0=2*Real.pi := by
    have hcseam : centers N K=centers N 0 := by
      dsimp [centers]
      rw [hn,hn,hpK,hp0,circle_exp_pi]
      congr 1
      funext z
      exact normalize_neg U W (Circle.exp 0) z
    have heseam : err K=err 0 := by
      dsimp [err]
      rw [hpK,hp0,hcseam,z525]
    dsimp [b]
    rw [hpK,hp0,heseam]
    ring
  have hex := DiskWinding.z574 F N K b hc hs hlift hstep hturn
  have edge : ∀ i≤N, ∀ k≤K, ∀ a≤1, ∀ b≤1, i+a≤N → k+b≤K →
      Real.pi/4≤|DiskWinding.increment (F i k) (F (i+a) (k+b))| →
      ∃ p∈parameterDisk, ∃ q∈parameterDisk,
        (∀ z : ℂ, ‖diskNormalize W U p (diskExpand W U q z)-z‖≤zeta*‖z‖) ∧
        (1 : ℝ)/4≤|EllipseLinear.det
          (chooseCenter (diskNormalize W U p) : ℂ).re (chooseCenter (diskNormalize W U p) : ℂ).im
          (chooseCenter (diskNormalize W U q) : ℂ).re (chooseCenter (diskNormalize W U q) : ℂ).im| := by
    intro i hi k hk a ha b hb hia hkb hsep
    refine ⟨gridPoint N K i k,gridPoint_mem hN hK hi hk,
      gridPoint N K (i+a) (k+b),gridPoint_mem hN hK hia hkb,hcomp i hi k hk a ha b hb hia hkb,?_⟩
    have hd := EllipseLinear.z412 (centers i k : ℂ).arg (centers (i+a) (k+b) : ℂ).arg hsep
    simpa only [circle_arg_re,circle_arg_im] using hd
  rcases hex with ⟨i,hi,k,hk,hik⟩ | ⟨i,hi,k,hk,hik⟩ | ⟨i,hi,k,hk,hik⟩
  · exact edge i hi k (by omega) 0 (by omega) 1 (by omega) (by omega) (by omega) (by simpa using hik)
  · exact edge i (by omega) k hk 1 (by omega) 0 (by omega) (by omega) (by omega) (by simpa using hik)
  · exact edge i (by omega) k (by omega) 1 (by omega) 1 (by omega) (by omega) (by omega) hik
end CriticalPercolation.EuclideanEllipse
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.z0
variable {E I : Type*}
lemma upper_biUnion (A : I → Set (Set E)) (s : Finset I)
    (hA : ∀ i∈s, IsUpperSet (A i)) : IsUpperSet (⋃ i∈s, A i) := by
  intro ω τ h hω
  obtain ⟨i,hi,hω⟩ := Set.mem_iUnion₂.mp hω
  exact Set.mem_iUnion₂.mpr ⟨i,hi,hA i hi h hω⟩
lemma z472 (A : I → Set (Set E)) (s : Finset I)
    (hA : ∀ i∈s, z11 (A i)) :
    z11 (⋃ i∈s, A i) := by
  intro ω hω
  obtain ⟨i,hi,hω⟩ := Set.mem_iUnion₂.mp hω
  obtain ⟨K,hK,hKs,hKA⟩ := hA i hi ω hω
  exact ⟨K,hK,hKs,Set.mem_iUnion₂.mpr ⟨i,hi,hKA⟩⟩
theorem z539 [Countable E] (q : E → unitInterval) (A : I → Set (Set E))
    (s : Finset I) (hA : ∀ i∈s, IsUpperSet (A i))
    (hw : ∀ i∈s, z11 (A i)) :
    ∏ i∈s, (1-(law q).real (A i)) ≤ 1-(law q).real (⋃ i∈s, A i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hm := hA i (Finset.mem_insert_self i s)
    have hw' := hw i (Finset.mem_insert_self i s)
    have hs : ∀ j∈s, IsUpperSet (A j) := fun j hj => hA j (Finset.mem_insert_of_mem hj)
    have hsw : ∀ j∈s, z11 (A j) := fun j hj => hw j (Finset.mem_insert_of_mem hj)
    have hind := ih hs hsw
    let B := ⋃ j∈s, A j
    have hBm := upper_biUnion A s hs
    have hBw := z472 A s hsw
    have hH := z265 q (A i) B hm hBm hw' hBw
    have hu := measureReal_union_add_inter (s := A i)
      (z61 B hBm hBw) (μ := law q)
      (measure_ne_top _ _) (measure_ne_top _ _)
    have hb : (law q).real (A i)≤1 := measureReal_le_one
    have hp := mul_le_mul_of_nonneg_left hind (by linarith : 0≤1-(law q).real (A i))
    rw [Finset.prod_insert hi]
    rw [Finset.set_biUnion_insert]
    change (1-(law q).real (A i))*(∏ j∈s, (1-(law q).real (A j)))≤
      1-(law q).real (A i∪B)
    change _≤1-(law q).real B at hind
    change _≤(1-(law q).real (A i))*(1-(law q).real B) at hp
    nlinarith
theorem z463 [Countable E] (q : E → unitInterval) (A : I → Set (Set E))
    (s : Finset I) (hA : ∀ i∈s, IsUpperSet (A i))
    (hw : ∀ i∈s, z11 (A i)) (a : ℝ) (ha : 0≤a)
    (hu : 1-a^s.card<(law q).real (⋃ i∈s, A i)) :
    ∃ i∈s, 1-a<(law q).real (A i) := by
  by_contra hn
  push Not at hn
  have hp : a^s.card≤∏ i∈s, (1-(law q).real (A i)) := by
    rw [←Finset.prod_const]
    apply Finset.prod_le_prod (fun _ _ => ha)
    intro i hi
    linarith [hn i hi]
  have hH := z539 q A s hA hw
  linarith
end CriticalPercolation.z0
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
def seedInfiniteEvent (A : Set V) : Set (Set E) :=
  {ω | ∃ a∈A, (G.cluster ω a).Infinite}
lemma z421 {A B : Set V} (hAB : A⊆B) :
    G.seedInfiniteEvent A⊆G.seedInfiniteEvent B := by
  rintro ω ⟨a,ha,hi⟩
  exact ⟨a,hAB ha,hi⟩
theorem z178 [Countable V] [Countable E]
    (hc : G.z7.Connected) (o : V) (q : E → unitInterval)
    (hone : z0.law q G.z12=1) (eps : ℝ) (heps : 0<eps) :
    ∃ m : ℕ, 1-eps<(z0.law q).real (G.seedInfiniteEvent (G.z5 o m)) := by
  let A : ℕ → Set (Set E) := fun n => G.seedInfiniteEvent (G.z5 o n)
  have hmono : Monotone A := fun _ _ h => G.z421 (G.z26 o h)
  have heq : (⋃ n, A n)=G.z12 := by
    ext ω
    constructor
    · intro h
      obtain ⟨n,a,_ha,hi⟩ := Set.mem_iUnion.mp h
      exact ⟨a,hi⟩
    · rintro ⟨a,hi⟩
      obtain ⟨n,hn⟩ := G.z48 (hc o a)
      exact Set.mem_iUnion.mpr ⟨n,a,hn,hi⟩
  have ht := tendsto_measure_iUnion_atTop (μ := z0.law q) hmono
  rw [heq,hone] at ht
  have hreal := (ENNReal.tendsto_toReal (by simp : (1 : ℝ≥0∞)≠⊤)).comp ht
  have hnear : ∀ᶠ n in atTop, 1-eps<(z0.law q).real (A n) :=
    hreal.eventually (lt_mem_nhds (by simpa using heps : 1-eps<ENNReal.toReal 1))
  exact hnear.exists
theorem z423 [Countable E]
    (Psi : V → ℂ) (A : Set V) (zeta D : ℝ) (hD : 0≤D) (hDz : D≤zeta)
    (hPsi : ∀ ⦃x y⦄, G.z7.Adj x y → ‖Psi x-Psi y‖≤D)
    (hseed : ∀ a∈A, ‖Psi a‖<1) (S : Finset Circle)
    (hcover : ∀ c : Circle, ∃ d∈S, ‖(c : ℂ)-(d : ℂ)‖<zeta)
    (q : E → unitInterval) (a : ℝ) (ha : 0≤a)
    (hi : 1-a^S.card<(z0.law q).real (G.seedInfiniteEvent A))
    (hbound : ∀ᵐ ω ∂z0.law q, ∀ x∈A,
      (G.cluster (ω∩G.z4 {x | ‖Psi x‖≤1}) x).Finite) :
    ∃ c∈S, 1-a<(z0.law q).real (G.ellipseExit Psi A zeta c) := by
  have hsub : G.seedInfiniteEvent A ≤ᵐ[z0.law q] ⋃ c∈S, G.ellipseExit Psi A zeta c := by
    filter_upwards [hbound] with ω hω
    exact fun hi => G.z278 Psi A zeta D hD hDz hPsi hseed S hcover hi hω
  have hprob := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  exact z0.z463 q (fun c => G.ellipseExit Psi A zeta c) S
    (fun c _ => G.z581 Psi A zeta c) (fun c _ => G.z341 Psi A zeta c)
    a ha (hi.trans_le hprob)
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
lemma z221 (pi : V → ℂ) (R W D : ℝ) (hW : 0<W) (hWR : W≤R)
    (c : Circle) (hpi : ∀ ⦃x y⦄, G.z7.Adj x y → ‖pi x-pi y‖≤D) :
    ∀ ⦃x y⦄, G.z7.Adj x y →
      ‖EuclideanEllipse.normalize R W c (pi x)-EuclideanEllipse.normalize R W c (pi y)‖≤D/W := by
  intro x y hxy
  rw [←EuclideanEllipse.normalize_sub]
  exact (EuclideanEllipse.z395 R W hW hWR c _).trans
    (div_le_div_of_nonneg_right (hpi hxy) hW.le)
lemma z325 (pi : V → ℂ) (R W : ℝ) (hW : 0<W) (hWR : W≤R)
    (c : Circle) (mu : Measure (Set E))
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂mu, ∀ a,
      (G.cluster (ω∩G.z4 {x | |(pi x).re|≤U ∧ |(pi x).im|≤W}) a).Finite) :
    ∀ᵐ ω ∂mu, ∀ a,
      (G.cluster (ω∩G.z4 {x | ‖EuclideanEllipse.normalize R W c (pi x)‖≤1}) a).Finite := by
  have hR : 0<R := hW.trans_le hWR
  have hsub : {x | ‖EuclideanEllipse.normalize R W c (pi x)‖≤1}⊆
      {x | |(pi x).re|≤R ∧ |(pi x).im|≤R} := by
    intro x hx
    change ‖EuclideanEllipse.normalize R W c (pi x)‖≤1 at hx
    have hn : ‖pi x‖≤R := by
      calc
        _ = ‖EuclideanEllipse.expand R W c (EuclideanEllipse.normalize R W c (pi x))‖ := by
          rw [EuclideanEllipse.z451 R W hR.ne' hW.ne']
        _ ≤ R*‖EuclideanEllipse.normalize R W c (pi x)‖ := EuclideanEllipse.expand_norm_le R W hW.le hWR c _
        _ ≤ R := by nlinarith
    exact ⟨(Complex.abs_re_le_norm _).trans hn,(Complex.abs_im_le_norm _).trans hn⟩
  filter_upwards [hbox R R] with ω hω a
  exact (hω a).subset (G.cluster_mono (Set.inter_subset_inter_right _ (G.z207 hsub)) a)
theorem z505 [Countable E]
    (pi : V → ℂ) (A : Set V) (W B D zeta : ℝ) (hD : 0≤D) (hW : 0<W)
    (hBW : B<W) (hDz : D/W≤zeta)
    (hpi : ∀ ⦃x y⦄, G.z7.Adj x y → ‖pi x-pi y‖≤D)
    (hA : ∀ a∈A, ‖pi a‖≤B) (S : Finset Circle)
    (hcover : ∀ c : Circle, ∃ d∈S, ‖(c : ℂ)-(d : ℂ)‖<zeta)
    (q : E → unitInterval) (a : ℝ) (ha : 0≤a)
    (hi : 1-a^S.card<(z0.law q).real (G.seedInfiniteEvent A))
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂z0.law q, ∀ x,
      (G.cluster (ω∩G.z4 {x | |(pi x).re|≤U ∧ |(pi x).im|≤W}) x).Finite) :
    ∀ R : ℝ, W≤R → ∀ c : Circle, ∃ d∈S,
      1-a<(z0.law q).real (G.ellipseExit (EuclideanEllipse.normalize R W c ∘ pi) A zeta d) := by
  intro R hWR c
  have hseed : ∀ x∈A, ‖EuclideanEllipse.normalize R W c (pi x)‖<1 := by
    intro x hx
    exact (EuclideanEllipse.z395 R W hW hWR c (pi x)).trans_lt
      ((div_lt_one hW).mpr ((hA x hx).trans_lt hBW))
  have hbound : ∀ᵐ ω ∂z0.law q, ∀ x∈A,
      (G.cluster (ω∩G.z4 {x | ‖EuclideanEllipse.normalize R W c (pi x)‖≤1}) x).Finite := by
    filter_upwards [G.z325 pi R W hW hWR c (z0.law q) hbox] with ω hω x _hx
    exact hω x
  exact G.z423 _ A zeta (D/W) (by positivity) hDz
    (G.z221 pi R W D hW hWR c hpi) hseed S hcover q a ha hi hbound
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
theorem z498 [Countable V] [Countable E]
    (hc : G.z7.Connected) (hl : G.LocallyFinite)
    (pi : V → ℂ) (o : V) (D : ℝ) (pc : unitInterval)
    (hD : 0≤D) (hpo : pi o=0)
    (hpi : ∀ ⦃x y⦄, G.z7.Adj x y → ‖pi x-pi y‖≤D)
    (hone : z0.law (fun _ : E => pc) G.z12=1)
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂z0.law (fun _ : E => pc), ∀ x,
      (G.cluster (ω∩G.z4 {x | |(pi x).re|≤U ∧ |(pi x).im|≤W}) x).Finite)
    (hnull : ∀ a b : ℝ, a^2+b^2=1 → ∀ w : ℝ,
      z0.law (fun _ : E => pc)
        (G.stripPercolates (z10 (fun x => (pi x).re) (fun x => (pi x).im) a b) w)=0)
    (eps eta : ℝ) (heps : 0<eps) (heps' : eps<1/10) (heta : 0<eta) :
    ∃ m : ℕ, ∀ rho : ℝ, 0<rho → ∃ R W : ℝ, ∃ c d e : Circle,
      (∀ ⦃x y⦄, G.z7.Adj x y →
        |ellipseTime (EuclideanEllipse.normalize R W c ∘ pi) d e x-
          ellipseTime (EuclideanEllipse.normalize R W c ∘ pi) d e y|≤rho) ∧
      (∀ ⦃x y⦄, G.z7.Adj x y →
        |ellipseHeight (EuclideanEllipse.normalize R W c ∘ pi) d e x-
          ellipseHeight (EuclideanEllipse.normalize R W c ∘ pi) d e y|≤rho) ∧
      ∀ b : Bool, 1-eta<(z0.law (fun _ : E => pc)).real
        (G.boxMove (ellipseTime (EuclideanEllipse.normalize R W c ∘ pi) d e)
          (ellipseHeight (EuclideanEllipse.normalize R W c ∘ pi) d e) m (eps/8) 30 o (Corridor.sign b)) := by
  let zeta := eps/1000
  have hzeta : 0<zeta := by dsimp [zeta]; positivity
  have hzeta' : zeta≤1/10000 := by dsimp [zeta]; linarith
  let a := min (eta/2) (1/2)
  have ha : 0<a := lt_min (by positivity) (by norm_num)
  have haeta : a<eta := (min_le_left _ _).trans_lt (by linarith)
  have haone : a<1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨S,hS⟩ := EuclideanEllipse.z535 zeta hzeta
  obtain ⟨m,hm⟩ := G.z178 hc o (fun _ : E => pc) hone (a^S.card) (pow_pos ha _)
  have hAfin := G.z19 hl o m
  obtain ⟨B,hB⟩ := (hAfin.image (fun x => ‖pi x‖)).bddAbove
  have hAB : ∀ x∈G.z5 o m, ‖pi x‖≤B := fun x hx => hB ⟨x,hx,rfl⟩
  refine ⟨m,?_⟩
  intro rho hrho
  obtain ⟨W,hW,hBW,hmesh⟩ := z183 B D (min zeta (rho/16)) (lt_min hzeta (by positivity))
  have hDz : D/W≤zeta := hmesh.le.trans (min_le_left _ _)
  have hDrho : 16*(D/W)≤rho := by have := hmesh.trans_le (min_le_right _ _); linarith
  have hfav := G.z505 pi (G.z5 o m) W B D zeta hD hW hBW hDz hpi hAB
    S hS (fun _ : E => pc) a ha.le hm hbox
  let chooseCenter : (ℂ → ℂ) → Circle := fun f => Classical.epsilon
    (fun c => c∈S ∧ 1-a<(z0.law (fun _ : E => pc)).real
      (G.ellipseExit (f ∘ pi) (G.z5 o m) zeta c))
  have hselect : ∀ R : ℝ, W≤R → ∀ c : Circle,
      1-a<(z0.law (fun _ : E => pc)).real
        (G.ellipseExit (EuclideanEllipse.normalize R W c ∘ pi) (G.z5 o m) zeta
          (chooseCenter (EuclideanEllipse.normalize R W c))) := by
    intro R hWR c
    exact (Classical.epsilon_spec (hfav R hWR c)).2
  obtain ⟨N,hN⟩ := G.z262 hl (z0.law (fun _ : E => pc))
    pi (G.z5 o m) hAfin W zeta (1-a) hW hzeta.le hzeta' (by linarith) hnull
  let U := max W (10*(N : ℝ))
  have hWU : W≤U := le_max_left _ _
  have hU : 0<U := hW.trans_le hWU
  have hboundary : ∀ phi : ℝ,
      |((Circle.exp phi : ℂ)⁻¹*(chooseCenter (EuclideanEllipse.normalize U W (Circle.exp phi)) : ℂ)).re|<1/8 := by
    intro phi
    exact hN U hU (le_max_right _ _) _ _ (hselect U hWU _).le
  obtain ⟨p,hp,q,hq,hcomp,hdet⟩ := EuclideanEllipse.z220 W U zeta hW hWU hzeta chooseCenter hboundary
  have hpR := EuclideanEllipse.z117 W U hWU hp
  have hqR := EuclideanEllipse.z117 W U hWU hq
  let R := EuclideanEllipse.diskRadius W U p
  let c := Circle.exp p.2
  let Psi := EuclideanEllipse.diskNormalize W U p ∘ pi
  let Psi' := EuclideanEllipse.diskNormalize W U q ∘ pi
  let d := chooseCenter (EuclideanEllipse.diskNormalize W U p)
  let e := chooseCenter (EuclideanEllipse.diskNormalize W U q)
  have hstep := G.z386 Psi d e hdet (D/W)
    (G.z221 pi R W D hW hpR.1 c hpi)
  have hpert : ∀ x, ‖Psi x-Psi' x‖≤zeta*‖Psi' x‖ := by
    intro x
    have hh := hcomp (Psi' x)
    have he : EuclideanEllipse.diskExpand W U q (Psi' x)=pi x :=
      EuclideanEllipse.z451 _ W (ne_of_gt (hW.trans_le hqR.1)) hW.ne' _ (pi x)
    rwa [he] at hh
  have hPsi0 : Psi o=0 := by
    change EuclideanEllipse.normalize R W c (pi o)=0
    rw [hpo,EuclideanEllipse.z594]
  refine ⟨R,W,c,d,e,(fun {_ _} h => (hstep.1 h).trans hDrho),
    (fun {_ _} h => (hstep.2 h).trans hDrho),?_⟩
  intro b
  cases b
  · have hfavored := hselect (EuclideanEllipse.diskRadius W U q) hqR.1 (Circle.exp q.2)
    have hmono := ENNReal.toReal_mono (measure_ne_top (z0.law (fun _ : E => pc)) _)
      (measure_mono (G.z309 Psi Psi' o m d e hdet eps heps heps' hPsi0 hpert false))
    exact (by linarith : 1-eta<1-a).trans (hfavored.trans_le hmono)
  · have hfavored := hselect (EuclideanEllipse.diskRadius W U p) hpR.1 (Circle.exp p.2)
    have hsame : ∀ x, ‖Psi x-Psi x‖≤(eps/1000)*‖Psi x‖ := by intro x; simp only [sub_self,norm_zero]; positivity
    have hmono := ENNReal.toReal_mono (measure_ne_top (z0.law (fun _ : E => pc)) _)
      (measure_mono (G.z309 Psi Psi o m d e hdet eps heps heps' hPsi0 hsame true))
    exact (by linarith : 1-eta<1-a).trans (hfavored.trans_le hmono)
end CriticalPercolation.z2
end
end
end
end OAI
end
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
lemma z382 {V E : Type*} [Fintype E] (tail head : E → V)
    (hb : ∀ v, Fintype.card {e // head e=v}=Fintype.card {e // tail e=v}) (e : E) :
    tail (balancedPermutation tail head hb e)=head e :=
  Equiv.ofFiberEquiv_map _ e
theorem z534 {V E : Type*} [Fintype E] (tail head : E → V)
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
    exact (z382 tail head hb _).symm
end CriticalPercolation.Boundary
end
end
end
end OAI
end
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
lemma z471 {S : Set Grid} (hS : S.Finite) : (squareBoundary S).Finite := by
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
lemma z406 (S : Set Grid) (v : Grid) :
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
theorem z301 {S : Set Grid} (hS : S.Finite)
    (e₀ : Edge) (he₀ : e₀∈squareBoundary S) :
    ∃ n : ℕ, 0<n ∧ ∃ e : ℕ → Edge, e 0=e₀ ∧ e n=e₀ ∧
      (∀ i, e i∈squareBoundary S) ∧ (∀ i, head (e i)=tail (e (i+1))) ∧
      Set.InjOn e (Set.Iio n) := by
  let := (z471 hS).fintype
  have hb (v : Grid) : Fintype.card {e : squareBoundary S // head e=v}=
      Fintype.card {e : squareBoundary S // tail e=v} :=
    (Fintype.card_congr (incomingEquiv S v)).trans
      ((z406 S v).trans (Fintype.card_congr (outgoingEquiv S v)).symm)
  obtain ⟨n,hn,e,h0,hn0,hchain,hinj⟩ := z534
    (fun e : squareBoundary S => tail e) (fun e : squareBoundary S => head e) (by intro v; simpa only [Fintype.card_eq_nat_card] using hb v) ⟨e₀,he₀⟩
  refine ⟨n,hn,(fun i => (e i).1),congrArg Subtype.val h0,congrArg Subtype.val hn0,
    fun i => (e i).2,hchain,?_⟩
  intro i hi j hj he
  exact hinj hi hj (Subtype.ext he)
lemma z552 (S : Set Grid) (hroot : (0,0)∈S)
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
lemma z554 (e : ℕ → Edge) (n : ℕ)
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
lemma z234 :
    Function.Injective (fun e : Edge => (rightSite e,e.2)) := by
  rintro ⟨p,d⟩ ⟨q,c⟩ h
  have hd : d=c := congrArg Prod.snd h
  subst c
  have hp : p=q := add_right_cancel (congrArg Prod.fst h)
  exact Prod.ext hp rfl
lemma z236 (e : ℕ → Edge) (n : ℕ)
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
        (Finset.mem_range.mp (Finset.mem_filter.mp hj).1) (z234 he))
  have hc : ({1,2} : Finset Dir).card=2 := by decide
  rw [Finset.card_product,hc] at hb
  omega
theorem z462 (e : ℕ → Edge) (n : ℕ)
    (hchain : ∀ i, head (e i)=tail (e (i+1))) (hclose : e n=e 0)
    (hinj : Set.InjOn e (Set.Iio n)) : n≤4*(outsideSites e n).card := by
  have h := z554 e n hchain hclose
  have h' := z236 e n hinj
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
lemma z285 (S : Set Grid) (e : ℕ → Edge) (n : ℕ)
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
lemma z253 {n : ℕ} (hn : 0<n) (e : ℕ → Edge)
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
lemma z466 {n : ℕ} (hn : 0<n) (e : ℕ → Edge)
    (hchain : ∀ i, head (e i)=tail (e (i+1))) (hclose : e n=e 0)
    (hinj : Set.InjOn e (Set.Iio n)) :
    wordValid (e 0).1 (fun j : Fin n => (e j).2) := by
  have hr := z253 hn e hchain hclose
  refine ⟨?_,?_⟩
  · rw [hr n le_rfl,hr 0 (Nat.zero_le n),hclose]
  · intro i hi j hj he
    rw [hr i hi.le,hr j hj.le] at he
    exact hinj hi hj he
lemma z559 {n : ℕ} {e f : ℕ → Edge}
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
theorem z536 (S : Set Grid) (hS : S.Finite) (hroot : (0,0)∈S)
    (hquad : ∀ v∈S, 0≤v.1 ∧ 0≤v.2) :
    ∃ n : ℕ, ∃ w : Fin (n+1) → Dir,
      wordValid (0,1) w ∧
      (∀ z∈outsideSites (wordEdge (0,1) w) (n+1),
        z∉S ∧ ∃ y∈S, z=y+(1,0) ∨ z=y+(0,1)) := by
  obtain ⟨l,hl,e,h0,hend,hmem,hchain,hinj⟩ := z301 hS
    ((0,1),3) (z552 S hroot hquad)
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hl)
  have he : e (n+1)=e 0 := hend.trans h0.symm
  have hp : (e 0).1=(0,1) := congrArg Prod.fst h0
  refine ⟨n,(fun j : Fin (n+1) => (e j).2),?_,?_⟩
  · simpa only [hp] using z466 hl e hchain he hinj
  · have hr := z253 hl e hchain he
    rw [hp] at hr
    rw [z559 (fun i hi => hr i hi.le)]
    exact z285 S e (n+1) hmem
end CriticalPercolation.Boundary
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
namespace CriticalPercolation
lemma z160 {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
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
lemma z582 {Ω : Type*} [MeasurableSpace Ω]
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
      (z462 _ _ (wordEdge_chain (0,1) w) hw.1 hw.2)
  · rw [wordFailure,if_neg hw]
    simp only [measureReal_empty]
    positivity
theorem z243 {Ω : Type*} [MeasurableSpace Ω]
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
    obtain ⟨n,w,hw,hz⟩ := z536 (S ω) hω.2 (hroot ω hω.1) (hquad ω hω.1)
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
        Finset.sum_le_sum (fun w _ => z582 μ B F q hq₀ hq₁ hfail (n+1) w)
      _ = μ.real B*(4*q)^(n+1) := by
        simp only [Finset.sum_const,Finset.card_univ,card_words,nsmul_eq_mul,
          Nat.cast_pow,Nat.cast_ofNat,mul_pow]
        ring
  have hs₀ : Summable (fun n : ℕ => (4*q)^n) :=
    summable_geometric_of_lt_one (by positivity) hq
  have hs : Summable (fun n : ℕ => μ.real B*(4*q)^(n+1)) :=
    ((summable_nat_add_iff 1).mpr hs₀).mul_left _
  have hu := z160 μ
    (fun n => ⋃ w : Fin (n+1) → Dir, wordFailure B F w)
    (fun n => μ.real B*(4*q)^(n+1)) (fun _ => by positivity) hs hterm
  apply ((measureReal_mono hsub).trans hu).trans_eq
  simp_rw [pow_succ]
  rw [tsum_mul_left,tsum_mul_right,tsum_geometric_of_lt_one (by positivity) hq]
  ring
theorem z419 {Ω : Type*} [MeasurableSpace Ω]
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
  have hf := z243 μ B S F hroot hquad hchild q hq₀ hh hfail
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
local instance {V E : Type} [h : Fact (∀ V E : Type, CriticalPercolationLeaf.FiniteSizeCriterion V E)] : Fact (CriticalPercolationLeaf.FiniteSizeCriterion V E) := ⟨h.out V E⟩
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
theorem z75 [Fact (CriticalPercolationLeaf.FiniteSizeCriterion V E)]
    (hconnected : G.z7.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : 0<(G.z3 : ℝ)) (hpc1 : (G.z3 : ℝ)<1)
    (hmoves : ∀ e eta : ℝ, 0<e → e<1/10 → 0<eta → eta<1/10 →
      ∃ m : ℕ, ∀ rho : ℝ, 0<rho → ∃ t z : V → ℝ, ∃ p : unitInterval,
        (G.z3 : ℝ)/2≤p ∧ p<G.z3 ∧
        (∀ ⦃u v⦄, G.z7.Adj u v → |t u-t v|≤rho) ∧
        (∀ ⦃u v⦄, G.z7.Adj u v → |z u-z v|≤rho) ∧
        ∀ y s, |s|=1 → 1-eta≤(z0.law (fun _ : E => p)).real
          (G.coordinateMove t z m e y s)) : False := by
  refine (Fact.out : CriticalPercolationLeaf.FiniteSizeCriterion V E) G.ends hconnected hl ?_ hpc hpc1 ?_
  · obtain ⟨S,hS,h⟩ := hq
    refine ⟨S,hS,fun v => ?_⟩
    obtain ⟨u,hu,f,hv⟩ := h v
    exact ⟨u,hu,f.vertex,f.edge,f.preserves,hv⟩
  · intro e η he he1 hη hη1
    obtain ⟨m,hr⟩ := hmoves e η he he1 hη hη1
    refine ⟨m,fun ρ hρ => ?_⟩
    obtain ⟨t,z,p,hlp,hup,ht,hz,hmv⟩ := hr ρ hρ
    refine ⟨t,z,p,hlp,hup,ht,hz,fun y s hs => ?_⟩
    have hh := hmv y s hs
    rw [z0.law_const] at hh
    unfold coordinateMove at hh
    have hb (y : V) (n : ℕ) : G.z5 y n = Nat.rec (motive := fun _ => Set V) ({y} : Set V) (fun _ B => B ∪ ⋃ v ∈ B, G.z7.neighborSet v) n := by
      induction n with
      | zero => rfl
      | succ n ih => simp only [z5, ih]
    rw [hb] at hh
    exact hh
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
lemma z558 (t z : V → ℝ) (m : ℕ) (q B : ℝ) (o : V) (s : ℝ)
    (φ : G.Aut) (ht : ∀ x y, t (φ.vertex x)-t (φ.vertex y)=t x-t y)
    (hz : ∀ x y, z (φ.vertex x)-z (φ.vertex y)=z x-z y) :
    G.boxMove t z m q B o s ⊆ (fun ω => φ.edge '' ω) ⁻¹'
      G.boxMove t z m q B (φ.vertex o) s := by
  rintro ω ⟨a,ha,b,w,hw,hbt,hbz⟩
  let w' := w.map (Aut.openGraphIso G φ ω).toHom
  refine ⟨φ.vertex a,(Aut.vertexBall_mem G φ o a m).mpr ha,φ.vertex b,w',?_,?_,?_⟩
  · intro x hx
    change x∈(w.map (Aut.openGraphIso G φ ω).toHom).support at hx
    rw [SimpleGraph.Walk.support_map] at hx
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    change |t (φ.vertex v)-t (φ.vertex o)|≤B ∧ |z (φ.vertex v)-z (φ.vertex o)|≤B
    rw [ht,hz]
    exact hw v hv
  · have h : t (φ.vertex b)-(t (φ.vertex o)+1)=t b-(t o+1) := by linarith [ht b o]
    rwa [h]
  · have h : z (φ.vertex b)-(z (φ.vertex o)+s)=z b-(z o+s) := by linarith [hz b o]
    rwa [h]
lemma z400 [Countable V] [Countable E]
    (t z : V → ℝ) (m : ℕ) (q B : ℝ) (o : V) (s : ℝ) (p : unitInterval)
    (φ : G.Aut) (ht : ∀ x y, t (φ.vertex x)-t (φ.vertex y)=t x-t y)
    (hz : ∀ x y, z (φ.vertex x)-z (φ.vertex y)=z x-z y) :
    (G.law p).real (G.boxMove t z m q B o s) ≤
      (G.law p).real (G.boxMove t z m q B (φ.vertex o) s) := by
  have hm : G.law p (G.boxMove t z m q B o s) ≤
      G.law p (G.boxMove t z m q B (φ.vertex o) s) := by
    conv_rhs => rw [← G.law_map_aut p φ]
    rw [Measure.map_apply (z0.z62 φ.edge)
      (G.z542 _ _ _ _ _ _ _)]
    exact measure_mono (G.z558 t z m q B o s φ ht hz)
  exact ENNReal.toReal_mono (measure_ne_top _ _) hm
lemma z509 (t z : V → ℝ) (m c : ℕ) (e s : ℝ) (he : e<1/10)
    {x y : V} (hxy : x∈G.z5 y c)
    (ht : |t x-t y|≤e/8) (hz : |z x-z y|≤e/8) :
    G.boxMove t z m (e/8) 30 x s ⊆ G.coordinateMove t z (m+c) e y s := by
  rintro ω ⟨a,ha,b,w,hw,hbt,hbz⟩
  refine ⟨a,?_,b,w,?_,?_,?_⟩
  · simpa only [Nat.add_comm c m] using G.vertexBall_add hxy m ha
  · intro v hv
    have hvb := hw v hv
    constructor
    · have := abs_sub_le (t v) (t x) (t y)
      linarith [hvb.1]
    · have := abs_sub_le (z v) (z x) (z y)
      linarith [hvb.2]
  · have hh := abs_sub_le (t b) (t x+1) (t y+1)
    rw [add_sub_add_right_eq_sub] at hh
    linarith
  · have hh := abs_sub_le (z b) (z x+s) (z y+s)
    rw [add_sub_add_right_eq_sub] at hh
    linarith
theorem z175 [Countable V] [Countable E]
    (t z : V → ℝ) (o : V) (m c : ℕ) (e eta rho : ℝ)
    (he : e<1/10) (hrho : 0≤rho) (hmesh : c*rho≤e/8)
    (ht : ∀ ⦃x y⦄, G.z7.Adj x y → |t x-t y|≤rho)
    (hz : ∀ ⦃x y⦄, G.z7.Adj x y → |z x-z y|≤rho)
    (hdense : ∀ y, ∃ φ : G.Aut, φ.vertex o∈G.z5 y c ∧
      (∀ x y, t (φ.vertex x)-t (φ.vertex y)=t x-t y) ∧
      (∀ x y, z (φ.vertex x)-z (φ.vertex y)=z x-z y))
    (pc : unitInterval) (hpc : 0<pc)
    (horigin : ∀ b : Bool, 1-eta<(z0.law (fun _ : E => pc)).real
      (G.boxMove t z m (e/8) 30 o (Corridor.sign b))) :
    ∃ p : unitInterval, (pc : ℝ)/2≤p ∧ p<pc ∧ ∀ y s, |s|=1 →
      1-eta≤(z0.law (fun _ : E => p)).real
        (G.coordinateMove t z (m+c) e y s) := by
  obtain ⟨p,hpl,hpu,hp⟩ := G.z556 t z m (e/8) 30 o pc hpc eta horigin
  refine ⟨p,hpl,hpu,?_⟩
  intro y s hs
  obtain ⟨b,hb⟩ : ∃ b : Bool, Corridor.sign b=s := by
    rcases (abs_eq (by norm_num : (0 : ℝ)≤1)).mp hs with h|h
    · exact ⟨true,by simpa [Corridor.sign] using h.symm⟩
    · exact ⟨false,by simpa [Corridor.sign] using h.symm⟩
  obtain ⟨φ,hφ,hφt,hφz⟩ := hdense y
  have htt := (G.z225 t rho hrho ht hφ).trans hmesh
  have hzz := (G.z225 z rho hrho hz hφ).trans hmesh
  have hsub := G.z509 t z m c e s he hφ htt hzz
  have hm : (G.law p).real (G.boxMove t z m (e/8) 30 (φ.vertex o) s)≤
      (G.law p).real (G.coordinateMove t z (m+c) e y s) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have hp' := hp b
  rw [hb] at hp'
  have hp'' : 1-eta≤(G.law p).real (G.boxMove t z m (e/8) 30 o s) := by
    simpa only [law,z0.law_const] using hp'.le
  simpa only [law,z0.law_const] using
    hp''.trans ((G.z400 t z m (e/8) 30 o s p φ hφt hφz).trans hm)
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal
namespace CriticalPercolation.z2
variable {V E : Type} (G : z2 V E)
lemma z418 (pi : V → ℂ) (R W : ℝ) (c d e : Circle) (phi : G.Aut)
    (hphi : ∀ x y, pi (phi.vertex x)-pi (phi.vertex y)=pi x-pi y) :
    (∀ x y, ellipseTime (EuclideanEllipse.normalize R W c ∘ pi) d e (phi.vertex x)-
      ellipseTime (EuclideanEllipse.normalize R W c ∘ pi) d e (phi.vertex y)=
      ellipseTime (EuclideanEllipse.normalize R W c ∘ pi) d e x-
      ellipseTime (EuclideanEllipse.normalize R W c ∘ pi) d e y) ∧
    (∀ x y, ellipseHeight (EuclideanEllipse.normalize R W c ∘ pi) d e (phi.vertex x)-
      ellipseHeight (EuclideanEllipse.normalize R W c ∘ pi) d e (phi.vertex y)=
      ellipseHeight (EuclideanEllipse.normalize R W c ∘ pi) d e x-
      ellipseHeight (EuclideanEllipse.normalize R W c ∘ pi) d e y) := by
  have hPsi : ∀ x y,
      EuclideanEllipse.normalize R W c (pi (phi.vertex x))-EuclideanEllipse.normalize R W c (pi (phi.vertex y))=
      EuclideanEllipse.normalize R W c (pi x)-EuclideanEllipse.normalize R W c (pi y) := by
    intro x y
    rw [←EuclideanEllipse.normalize_sub,←EuclideanEllipse.normalize_sub,hphi]
  constructor
  · intro x y
    rw [(z31 _ d e (phi.vertex x) (phi.vertex y)).1,
      (z31 _ d e x y).1]
    exact congrArg (fun z : ℂ => EllipseLinear.time (d : ℂ).re (d : ℂ).im (e : ℂ).re (e : ℂ).im z.re z.im) (hPsi x y)
  · intro x y
    rw [(z31 _ d e (phi.vertex x) (phi.vertex y)).2,
      (z31 _ d e x y).2]
    exact congrArg (fun z : ℂ => EllipseLinear.height (d : ℂ).re (d : ℂ).im (e : ℂ).re (e : ℂ).im z.re z.im) (hPsi x y)
theorem z474 [Countable V] [Countable E]
    (hc : G.z7.Connected) (hl : G.LocallyFinite)
    (pi : V → ℂ) (o : V) (c : ℕ) (D : ℝ) (pc : unitInterval)
    (hD : 0≤D) (hpc : 0<pc) (hpo : pi o=0)
    (hpi : ∀ ⦃x y⦄, G.z7.Adj x y → ‖pi x-pi y‖≤D)
    (hdense : ∀ y, ∃ phi : G.Aut, phi.vertex o∈G.z5 y c ∧
      ∀ x y, pi (phi.vertex x)-pi (phi.vertex y)=pi x-pi y)
    (hone : z0.law (fun _ : E => pc) G.z12=1)
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂z0.law (fun _ : E => pc), ∀ x,
      (G.cluster (ω∩G.z4 {x | |(pi x).re|≤U ∧ |(pi x).im|≤W}) x).Finite)
    (hnull : ∀ a b : ℝ, a^2+b^2=1 → ∀ w : ℝ,
      z0.law (fun _ : E => pc)
        (G.stripPercolates (z10 (fun x => (pi x).re) (fun x => (pi x).im) a b) w)=0)
    (eps eta : ℝ) (heps : 0<eps) (heps' : eps<1/10) (heta : 0<eta) :
    ∃ m : ℕ, ∀ rho : ℝ, 0<rho → ∃ t z : V → ℝ, ∃ p : unitInterval,
      (pc : ℝ)/2≤p ∧ p<pc ∧
      (∀ ⦃x y⦄, G.z7.Adj x y → |t x-t y|≤rho) ∧
      (∀ ⦃x y⦄, G.z7.Adj x y → |z x-z y|≤rho) ∧
      ∀ y s, |s|=1 → 1-eta≤(z0.law (fun _ : E => p)).real
        (G.coordinateMove t z m eps y s) := by
  obtain ⟨m,hm⟩ := G.z498 hc hl pi o D pc hD hpo hpi hone hbox hnull eps eta heps heps' heta
  refine ⟨m+c,?_⟩
  intro rho hrho
  let r := min rho (eps/(8*((c : ℝ)+1)))
  have hr : 0<r := lt_min hrho (div_pos heps (by positivity))
  have hrrho : r≤rho := min_le_left _ _
  have hrs : r≤eps/(8*((c : ℝ)+1)) := min_le_right _ _
  have hmesh : (c : ℝ)*r≤eps/8 := by
    have hh := (le_div_iff₀ (by positivity : 0<8*((c : ℝ)+1))).mp hrs
    nlinarith
  obtain ⟨R,W,a,b,d,ht,hz,hmoves⟩ := hm r hr
  let t := ellipseTime (EuclideanEllipse.normalize R W a ∘ pi) b d
  let z := ellipseHeight (EuclideanEllipse.normalize R W a ∘ pi) b d
  have htdense : ∀ y, ∃ phi : G.Aut, phi.vertex o∈G.z5 y c ∧
      (∀ x y, t (phi.vertex x)-t (phi.vertex y)=t x-t y) ∧
      (∀ x y, z (phi.vertex x)-z (phi.vertex y)=z x-z y) := by
    intro y
    obtain ⟨phi,hphi,hphiP⟩ := hdense y
    exact ⟨phi,hphi,G.z418 pi R W a b d phi hphiP⟩
  obtain ⟨p,hpl,hpu,hp⟩ := G.z175 t z o m c eps eta r heps' hr.le hmesh ht hz htdense pc hpc hmoves
  exact ⟨t,z,p,hpl,hpu,fun {_ _} h => (ht h).trans hrrho,fun {_ _} h => (hz h).trans hrrho,hp⟩
theorem z219 [Fact (∀ V E : Type, CriticalPercolationLeaf.FiniteSizeCriterion V E)] [Countable V] [Countable E]
    (hc : G.z7.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (pi : V → ℂ) (o : V) (c : ℕ) (D : ℝ)
    (hD : 0≤D) (hpc : 0<(G.z3 : ℝ)) (hpc1 : (G.z3 : ℝ)<1)
    (hpo : pi o=0)
    (hpi : ∀ ⦃x y⦄, G.z7.Adj x y → ‖pi x-pi y‖≤D)
    (hdense : ∀ y, ∃ phi : G.Aut, phi.vertex o∈G.z5 y c ∧
      ∀ x y, pi (phi.vertex x)-pi (phi.vertex y)=pi x-pi y)
    (hone : z0.law (fun _ : E => G.z3) G.z12=1)
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂z0.law (fun _ : E => G.z3), ∀ x,
      (G.cluster (ω∩G.z4 {x | |(pi x).re|≤U ∧ |(pi x).im|≤W}) x).Finite)
    (hnull : ∀ a b : ℝ, a^2+b^2=1 → ∀ w : ℝ,
      z0.law (fun _ : E => G.z3)
        (G.stripPercolates (z10 (fun x => (pi x).re) (fun x => (pi x).im) a b) w)=0) : False := by
  apply G.z75 hc hl hq hpc hpc1
  intro eps eta he he' heta _heta'
  exact G.z474 hc hl pi o c D G.z3 hD hpc hpo hpi hdense hone hbox hnull eps eta he he' heta
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set
open scoped Classical
namespace CriticalPercolation
lemma z334 (v : ℕ → ℕ) (hv : ∀ n, 0<v n)
    (hg : ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n≥N, Real.log (v n : ℝ) ≤ ε*n)
    (t R : ℕ) : ∃ n≥R, v (n+t) ≤ 2*v n := by
  by_contra! hbad
  have hc : 0<Real.log 2 := Real.log_pos (by norm_num)
  let ε := Real.log 2/(2*((t:ℝ)+1))
  have hd : 0<2*((t:ℝ)+1) := by positivity
  have hε : 0<ε := div_pos hc hd
  have hεeq : ε*(2*((t:ℝ)+1)) = Real.log 2 := div_mul_cancel₀ _ hd.ne'
  obtain ⟨N,hN⟩ := hg ε hε
  let n₀ := max R N
  have hnR : R≤n₀ := le_max_left _ _
  have hnN : N≤n₀ := le_max_right _ _
  have hstep (n : ℕ) (hn : R≤n) :
      Real.log (v n : ℝ)+Real.log 2 < Real.log (v (n+t) : ℝ) := by
    have hp : (0:ℝ)<v n := Nat.cast_pos.mpr (hv n)
    have hh : (2:ℝ)*(v n:ℝ) < (v (n+t):ℝ) := by exact_mod_cast hbad n hn
    have hl := Real.log_lt_log (mul_pos (by norm_num) hp) hh
    rwa [Real.log_mul (by norm_num) hp.ne',add_comm] at hl
  have hlow : ∀ k : ℕ, (k:ℝ)*Real.log 2 ≤ Real.log (v (n₀+k*t) : ℝ) := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.add_zero,Nat.cast_zero,zero_mul]
      exact Real.log_nonneg (by exact_mod_cast hv n₀)
    | succ k ih =>
      have hs := hstep (n₀+k*t) (hnR.trans (Nat.le_add_right _ _))
      have he : n₀+(k+1)*t = n₀+k*t+t := by ring
      rw [he,Nat.cast_add,Nat.cast_one]
      nlinarith
  let k := n₀+1
  have hboth : (k:ℝ)*Real.log 2 ≤ ε*(n₀+k*t : ℕ) :=
    (hlow k).trans (hN _ (hnN.trans (Nat.le_add_right _ _)))
  have hnum : (k:ℝ)*(2*((t:ℝ)+1)) ≤ (n₀+k*t : ℕ) := by
    apply (mul_le_mul_iff_left₀ hc).mp
    calc
      _ = ((k:ℝ)*Real.log 2)*(2*((t:ℝ)+1)) := by ring
      _ ≤ (ε*(n₀+k*t : ℕ))*(2*((t:ℝ)+1)) :=
        mul_le_mul_of_nonneg_right hboth hd.le
      _ = _ := by rw [mul_right_comm,hεeq]; ring
  dsimp only [k] at hnum
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one] at hnum
  nlinarith [(Nat.cast_nonneg n₀ : (0:ℝ)≤n₀),(Nat.cast_nonneg t : (0:ℝ)≤t),mul_nonneg (Nat.cast_nonneg n₀ : (0:ℝ)≤n₀)
    (Nat.cast_nonneg t : (0:ℝ)≤t)]
namespace z2
variable {V E : Type*} (G : z2 V E)
def SubexponentialGrowth : Prop :=
  ∀ o : V, ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n≥N,
    Real.log ((G.z5 o n).ncard : ℝ) ≤ ε*n
lemma z202 (hlocal : G.LocallyFinite)
    (hg : G.SubexponentialGrowth) (o : V) (t R : ℕ) :
    ∃ n≥R, (G.z5 o (n+t)).ncard ≤ 2*(G.z5 o n).ncard := by
  apply z334 _ _ (hg o)
  intro n
  exact (Set.ncard_pos (G.z19 hlocal o n)).mpr ⟨o,G.z45 o n⟩
end z2
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set
open scoped Classical
namespace CriticalPercolation
lemma z403 {α β : Type*} (S : Finset α) (T : Finset β)
    (g : α → β) (f : β → ℝ) (L : ℕ) (hf : ∀ b, 0≤f b)
    (hmap : ∀ a∈S, g a∈T) (hL : ∀ b, (S.filter (fun a => g a=b)).card≤L) :
    ∑ a∈S, f (g a) ≤ (L:ℝ)*∑ b∈T, f b := by
  rw [Finset.sum_comp]
  calc
    _ ≤ ∑ b∈S.image g, (L:ℝ)*f b := by
      apply Finset.sum_le_sum
      intro b _
      simp only [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hL b)) (hf b)
    _ ≤ ∑ b∈T, (L:ℝ)*f b := Finset.sum_le_sum_of_subset_of_nonneg
      (by rintro b hb; obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb; exact hmap a ha)
      (fun b _ _ => mul_nonneg (Nat.cast_nonneg _) (hf b))
    _ = _ := (Finset.mul_sum _ _ _).symm
namespace z2
variable {V E : Type*} (G : z2 V E)
lemma z473 {K : Set E} (hK : K.Finite) :
    (⋃ e∈K, {v | v∈G.ends e}).Finite := by
  apply hK.biUnion
  intro e _
  convert (G.ends e).toFinset.finite_toSet using 1
  ext v
  exact Sym2.mem_toFinset.symm
lemma z286 (hconnected : G.z7.Connected) (o : V)
    {K : Set E} (hK : K.Finite) : ∃ W, K ⊆ G.z4 (G.z5 o W) := by
  obtain ⟨W,hW⟩ := G.z76 hconnected o (G.z473 hK)
  refine ⟨W,?_⟩
  intro e he v hv
  exact hW (Set.mem_iUnion₂.mpr ⟨e,he,hv⟩)
lemma z228 : Monotone G.z4 := by
  intro S T h e he v hv
  exact h (he v hv)
def inducedBallExhaustion (hconnected : G.z7.Connected) (hlocal : G.LocallyFinite)
    (o : V) : Set.FiniteExhaustion (Set.univ : Set E) where
  toFun n := G.z4 (G.z5 o n)
  finite' n := G.z27 hlocal (G.z19 hlocal o n)
  subset_succ' n := G.z228 (G.z26 o (Nat.le_succ n))
  iUnion_eq' := by
    apply Set.eq_univ_of_forall
    intro e
    obtain ⟨W,hW⟩ := G.z286 hconnected o (Set.finite_singleton e)
    exact Set.mem_iUnion.mpr ⟨W,hW rfl⟩
lemma Aut.z596 (φ : G.Aut) {K : Set E} {S : Set V}
    (hKS : K⊆G.z4 S) : φ.edge '' K ⊆ G.z4 (φ.vertex '' S) := by
  rintro e ⟨a,ha,rfl⟩ v hv
  rw [φ.preserves] at hv
  obtain ⟨w,hw,rfl⟩ := Sym2.mem_map.mp hv
  exact ⟨w,hKS ha w hw,rfl⟩
lemma z139 (o u v : V) (n C W : ℕ) (φ : G.Aut)
    (hv : v∈G.z5 o n) (hφ : φ.vertex u ∈ G.z5 v C)
    {K : Set E} (hK : K⊆G.z4 (G.z5 u W)) :
    φ.edge '' K ⊆ G.z4 (G.z5 o (n+C+W)) := by
  apply (Aut.z596 G φ hK).trans
  apply G.z228
  rw [Aut.z430]
  exact G.vertexBall_add (G.vertexBall_add hv C hφ) W
lemma z455 (hlocal : G.LocallyFinite) (C M : ℕ)
    (hM : ∀ v, (G.z5 v C).ncard≤M) (u : V) (e : E) (hu : u∈G.ends e)
    (φ : V → G.Aut) (hφ : ∀ v, (φ v).vertex u ∈ G.z5 v C)
    (S : Finset V) (f : E) : (S.filter (fun v => (φ v).edge e=f)).card ≤ 2*M := by
  have hsub : (↑(S.filter (fun v => (φ v).edge e=f)) : Set V) ⊆
      G.z5 (G.ends f).out.1 C ∪ G.z5 (G.ends f).out.2 C := by
    intro v hv
    have he : (φ v).edge e=f := (Finset.mem_filter.mp hv).2
    have hm : (φ v).vertex u ∈ G.ends f := by
      rw [← he,(φ v).preserves]
      exact Sym2.mem_map.mpr ⟨u,hu,rfl⟩
    rw [(G.ends f).out_eq.symm,Sym2.mem_iff] at hm
    have hd := (G.z330).mp (hφ v)
    exact hm.elim (fun h => Or.inl (h ▸ hd)) (fun h => Or.inr (h ▸ hd))
  have hc := Set.ncard_le_ncard hsub
    ((G.z19 hlocal _ C).union (G.z19 hlocal _ C))
  simp only [Set.ncard_coe_finset] at hc
  have hh := Set.ncard_union_le (G.z5 (G.ends f).out.1 C)
    (G.z5 (G.ends f).out.2 C)
  exact hc.trans (hh.trans (by have h1 := hM (G.ends f).out.1; have h2 := hM (G.ends f).out.2; omega))
end z2
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical
namespace CriticalPercolation
inductive z18 (E R : Type*) where
  | done (r : R)
  | ask (e : E) (left right : z18 E R)
namespace z18
variable {E R : Type*}
def run : z18 E R → (E → Bool) → R
  | .done r, _ => r
  | .ask e l r, ω => if ω e then run r ω else run l ω
def reads : z18 E R → (E → Bool) → List E
  | .done _, _ => []
  | .ask e l r, ω => e :: if ω e then reads r ω else reads l ω
def Valid [DecidableEq E] : z18 E R → Finset E → Prop
  | .done _, _ => True
  | .ask e l r, used => e ∉ used ∧ l.Valid (insert e used) ∧ r.Valid (insert e used)
lemma reads_disjoint [DecidableEq E] (t : z18 E R) (used : Finset E) (h : t.Valid used)
    (ω : E → Bool) : ∀ e ∈ t.reads ω, e ∉ used := by
  induction t generalizing used with
  | done r => simp [reads]
  | ask e l r hl hr =>
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact h.1
    · by_cases he : ω e = true
      · have hm : f ∈ r.reads ω := by simpa [reads,he] using hf
        exact fun hx => hr _ h.2.2 _ hm (Finset.mem_insert_of_mem hx)
      · have hm : f ∈ l.reads ω := by simpa [reads,he] using hf
        exact fun hx => hl _ h.2.1 _ hm (Finset.mem_insert_of_mem hx)
lemma reads_nodup [DecidableEq E] (t : z18 E R) (used : Finset E) (h : t.Valid used)
    (ω : E → Bool) : (t.reads ω).Nodup := by
  induction t generalizing used with
  | done r => simp [reads]
  | ask e l r hl hr =>
    rw [reads,List.nodup_cons]
    by_cases he : ω e = true
    · simp only [he,↓reduceIte]
      exact ⟨fun hm => reads_disjoint r _ h.2.2 ω e hm (Finset.mem_insert_self _ _), hr _ h.2.2⟩
    · simp only [he]
      exact ⟨fun hm => reads_disjoint l _ h.2.1 ω e hm (Finset.mem_insert_self _ _), hl _ h.2.1⟩
end z18
namespace LazyDFS
variable {V E : Type*} [DecidableEq V] [DecidableEq E]
structure State (V E : Type*) where
variable [Fintype V]
end LazyDFS
end CriticalPercolation
end
end
end OAI
end
section
namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
namespace CriticalPercolation.z2
open ClusterDeletion z8
open scoped Classical
variable {V E : Type*} (G : z2 V E)
lemma z547 {S T : Set V} (h : S ⊆ T) : G.z9 S ⊆ G.z9 T := by
  rintro e ⟨v, hv, he⟩
  exact ⟨v, h hv, he⟩
end CriticalPercolation.z2
end
end
end OAI
end
section
namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
namespace CriticalPercolation
namespace Wiring
variable {V : Type*} (H : SimpleGraph V)
def link (s b u v : V) : Prop :=
  H.Reachable u v ∨ (H.Reachable u s ∧ H.Reachable b v) ∨
    (H.Reachable u b ∧ H.Reachable s v)
lemma link_refl (s b u : V) : link H s b u u := Or.inl (.refl _)
lemma link_trans {s b u v z : V} : link H s b u v → link H s b v z → link H s b u z := by
  rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩) (k | ⟨k1,k2⟩ | ⟨k1,k2⟩)
  · exact Or.inl (h.trans k)
  · exact Or.inr (Or.inl ⟨h.trans k1,k2⟩)
  · exact Or.inr (Or.inr ⟨h.trans k1,k2⟩)
  · exact Or.inr (Or.inl ⟨h1,h2.trans k⟩)
  · exact Or.inr (Or.inl ⟨h1,k2⟩)
  · exact Or.inl (h1.trans k2)
  · exact Or.inr (Or.inr ⟨h1,h2.trans k⟩)
  · exact Or.inl (h1.trans k2)
  · exact Or.inr (Or.inr ⟨h1,k2⟩)
lemma edge_reachable (s b : V) : (SimpleGraph.edge s b).Reachable s b := by
  rcases eq_or_ne s b with rfl | h
  · exact .refl _
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,h⟩)
theorem z561 (s b u v : V) :
    (H ⊔ SimpleGraph.edge s b).Reachable u v ↔ link H s b u v := by
  constructor
  · intro h
    have h' := ((H ⊔ SimpleGraph.edge s b).reachable_iff_reflTransGen u v).mp h
    clear h
    induction h' with
    | refl => exact link_refl H s b u
    | @tail z v _ hz ih =>
      apply link_trans H ih
      rcases hz with hz | hz
      · exact Or.inl hz.reachable
      · rcases ((SimpleGraph.edge_adj _ _ _ _).mp hz).1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact Or.inr (Or.inl ⟨.refl _,.refl _⟩)
        · exact Or.inr (Or.inr ⟨.refl _,.refl _⟩)
  · rintro (h | ⟨h1,h2⟩ | ⟨h1,h2⟩)
    · exact h.mono le_sup_left
    · exact (h1.mono le_sup_left).trans ((edge_reachable s b).mono le_sup_right |>.trans
        (h2.mono le_sup_left))
    · exact (h1.mono le_sup_left).trans ((edge_reachable s b).symm.mono le_sup_right |>.trans
        (h2.mono le_sup_left))
end Wiring
end CriticalPercolation
end
end
end OAI
end
section
namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical
namespace CriticalPercolation.z18
open scoped Classical
open z8
variable {E R : Type*} [Fintype E]
lemma z317 (w : E → Prop → ℝ) (e : E) (f g : Set E → ℝ) :
    expect w (fun ω => if ω e then f ω else g ω) =
      w e True*expect (pin w e True) f+w e False*expect (pin w e False) g := by
  calc
    _ = expect w (fun ω => (if ω e = True then f ω else 0) +
        (if ω e = False then g ω else 0)) := by
      congr 1
      funext ω
      by_cases h : ω e <;> simp [h]
    _ = _ := by
      rw [expect_add]
      apply congrArg₂ (· + ·)
      · convert z81 w e True f using 1
        congr 1
        funext ω
        by_cases h : ω e <;> simp [h]
      · convert z81 w e False g using 1
        congr 1
        funext ω
        by_cases h : ω e <;> simp [h]
end CriticalPercolation.z18
namespace CriticalPercolation.LazyDFS
open scoped Classical
open z8 z18
variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
def Fresh (w : E → Prop → ℝ) (p : ℝ) (read : Finset E) : Prop :=
  ∀ e ∉ read, w e False = 1-p ∧ w e True = p
omit [Fintype E] [DecidableEq V] in
lemma fresh_pin (w : E → Prop → ℝ) (p : ℝ) (read : Finset E) (hf : Fresh w p read)
    (e : E) (b : Prop) : Fresh (pin w e b) p (insert e read) := by
  intro j hj
  have hj' : j ≠ e ∧ j ∉ read := by simpa only [Finset.mem_insert,not_or] using hj
  have hje : j ≠ e := hj'.1
  unfold pin
  simp only [Function.update,dif_neg hje]
  exact hf j hj'.2
omit [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma z174 (G : z2 V E) (ω : Set E)
    {v e t} (he : ω e) (heq : G.ends e = s(v,t)) :
    (G.z1 ω).Reachable v t := by
  rcases eq_or_ne v t with rfl | hne
  · exact .refl _
  · exact SimpleGraph.Adj.reachable ((SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,he,heq⟩,hne⟩)
end CriticalPercolation.LazyDFS
end
end
end OAI
end
section
namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical
namespace CriticalPercolation.z2
variable {V E : Type*}
lemma z595 (G : z2 V E) (s : Set E) (e : E) (a b : V)
    (he : G.ends e = s(a,b)) :
    G.z1 (insert e s) = G.z1 s ⊔ SimpleGraph.edge a b := by
  rw [z1,Set.image_insert_eq,he,← Set.singleton_union,SimpleGraph.fromEdgeSet_union]
  exact sup_comm _ _
end CriticalPercolation.z2
end
end
end OAI
end
section
namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical
namespace CriticalPercolation.LazyDFS
open scoped Classical
open z8 z18 z2
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
end CriticalPercolation.LazyDFS
namespace CriticalPercolation.z18
open scoped Classical
open z8 LazyDFS
variable {E R : Type*} [Fintype E] [DecidableEq E]
omit [DecidableEq E] in
lemma z168 (v : E → Prop → ℝ) (hv : ∀ e, ∑ b, v e b = 1)
    (a : ℝ) (f : (E → Prop) → ℝ) :
    expect v (fun ω => (a+f ω)^2) = a^2+2*a*expect v f+expect v (fun ω => (f ω)^2) := by
  have heq : (fun ω => (a+f ω)^2) = (fun ω => a^2+2*a*f ω+(f ω)^2) := by
    funext ω; ring
  rw [heq,expect_add,expect_add,expect_const v hv,z25]
end CriticalPercolation.z18
end
end
end OAI
end
section
namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical
namespace CriticalPercolation.z8
open scoped Classical
variable {E : Type*} [Fintype E]
lemma z555 (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (h0 : w e False = 1-p) (h1 : w e True = p) (f : Set E → ℝ) :
    expect w (fun ω => if ¬ω e then p*f (Function.update ω e True) else 0) =
      expect w (fun ω => if ω e then (1-p)*f ω else 0) := by
  have he0 : w e False ≠ 0 := by rw [h0]; linarith [hp.2]
  have he1 : w e True ≠ 0 := by rw [h1]; exact hp.1.ne'
  have he := z495 w hw e False True he0 he1 f
  have hc : expect w (fun ω => if ¬ω e then p*f (Function.update ω e True) else 0) =
      w e False * expect (pin w e False) (fun ω => p*f (Function.update ω e True)) := by
    convert z81 w e False (fun ω => p*f (Function.update ω e True)) using 1
    congr 1
    funext ω
    by_cases hb : ω e <;> simp [hb]
  have ho : expect w (fun ω => if ω e then (1-p)*f ω else 0) =
      w e True * expect (pin w e True) (fun ω => (1-p)*f ω) := by
    convert z81 w e True (fun ω => (1-p)*f ω) using 1
    congr 1
    funext ω
    by_cases hb : ω e <;> simp [hb]
  erw [hc,ho,z25,z25,h0,h1,he]
  ring
lemma z280 [d : DecidableEq E]
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) {p : ℝ} (hp : p ∈ Set.Ioo 0 1)
    (h0 : w e False = 1-p) (h1 : w e True = p) (f : Set E → ℝ) :
    expect w (fun ω => if ¬ω e then p*f (Function.update ω e True) else 0) =
      expect w (fun ω => if ω e then (1-p)*f ω else 0) := by
  have hup (ω : Set E) :
      @Function.update E (fun _ => Prop) (fun a b => Classical.propDecidable (a=b)) ω e True =
        Function.update ω e True := by
    have hd : (fun a b => Classical.propDecidable (a=b)) = d := Subsingleton.elim _ _
    exact congrArg (fun d' : DecidableEq E =>
      @Function.update E (fun _ => Prop) d' ω e True) hd
  have h := z555 w hw e hp h0 h1 f
  convert h using 1
  congr 1
  funext ω
  by_cases hc : ω e
  · simp only [hc,not_true_eq_false,ite_false]
  · simp only [hc,not_false_eq_true,ite_true]
    exact congrArg (fun σ : Set E => p*f σ) (hup ω).symm
end CriticalPercolation.z8
end
end
end OAI
end
section
namespace OAI
section
section
open Set MeasureTheory ProbabilityTheory
open Real
open Set Real
open scoped Topology
open scoped BigOperators
open Set
open Set MeasureTheory
open Set MeasureTheory Real
open scoped Interval
open scoped Classical
namespace CriticalPercolation.FiniteEntropy
variable {X A : Type*} [Fintype X] [Fintype A]
lemma z612 (w f g : X → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ x, w x * f x * g x)^2 ≤ (∑ x, w x * (f x)^2) * ∑ x, w x * (g x)^2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro x _; exact mul_nonneg (hw x) (sq_nonneg _)
  · intro x _; exact mul_nonneg (hw x) (sq_nonneg _)
  · intro x _; apply le_of_eq; ring
end CriticalPercolation.FiniteEntropy
end
end
end OAI
end
section
namespace OAI
section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open z8 z2
universe uE
variable {V E : Type*} (G : z2 V E)
section Density
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (p : ℝ) (w : E → Prop → ℝ) (r₀ : (E → Prop) → ℝ)
end Density
section Seed
variable [Fintype V] [Fintype E]
def endpointEvent (u v : V) (s : ℕ) (ω : Set E) : Prop :=
  ¬ (G.z1 ω).Reachable u v ∧
    s ≤ (G.cluster ω u).toFinset.card ∧ s ≤ (G.cluster ω v).toFinset.card
end Seed
section ExactLaw
variable [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
end ExactLaw
end CriticalPercolation.BinaryLaw
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
namespace CriticalPercolation
namespace z0
variable {E : Type*} [Fintype E]
lemma prob_eq_real (q : E → unitInterval) (A : Set (Set E)) :
    z8.prob (fun e => z28 (q e)) (fun ω => ω ∈ A) = (law q).real A := by
  rw [z159]
  unfold z8.prob
  rfl
end z0
namespace z2
variable {V E : Type*} (G : z2 V E)
def z15 (u v : V) (s : ℕ) : Set (Set E) :=
  {ω | ¬ (G.z1 ω).Reachable u v} ∩ G.z17 u s ∩ G.z17 v s
lemma z271 [Fintype V] (ω : Set E) (u : V) (s : ℕ) :
    ω ∈ G.z17 u s ↔ s ≤ (G.cluster ω u).toFinset.card := by
  constructor
  · rintro ⟨K,hK,hsub,hs⟩
    exact hs.trans (by simpa only [Set.ncard_eq_toFinset_card'] using Set.ncard_le_ncard hsub)
  · intro hs
    exact ⟨G.cluster ω u, Set.toFinite _, Set.Subset.rfl, by simpa only [Set.ncard_eq_toFinset_card'] using hs⟩
lemma z252 [Fintype V] (ω : Set E) (u v : V) (s : ℕ) :
    ω ∈ G.z15 u v s ↔ BinaryLaw.endpointEvent G u v s ω := by
  simp only [z15, Set.mem_inter_iff, Set.mem_ofPred_eq,
    z271, BinaryLaw.endpointEvent, and_assoc]
lemma z507 [Fintype V] [Fintype E] (p : unitInterval) (u v : V) (s : ℕ) :
    z8.prob (fun _ : E => z0.z28 p)
      (BinaryLaw.endpointEvent G u v s) = (G.law p).real (G.z15 u v s) := by
  rw [law, ← z0.law_const, ← z0.prob_eq_real]
  congr 1
  funext ω
  exact propext (G.z252 ω u v s).symm
end z2
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
namespace CriticalPercolation
namespace z0
variable {E : Type*}
lemma z180 (p : unitInterval) (A B : Set (Set E))
    (hmono : IsUpperSet A) (hw : z11 A)
    (K : Set.FiniteExhaustion (Set.univ : Set E)) :
    Tendsto (fun n => (law (fun _ : E => p)).real (B ∩ {ω | K n ∩ ω ∈ A}))
      atTop (𝓝 ((law (fun _ : E => p)).real (B∩A))) := by
  have hm : Monotone (fun n => B ∩ {ω | K n ∩ ω ∈ A}) :=
    fun _ _ h => Set.inter_subset_inter_right _ (z50 A hmono K h)
  have h := tendsto_measure_iUnion_atTop (μ := law (fun _ : E => p)) hm
  rw [← Set.inter_iUnion,z49 A hmono hw K] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
end z0
namespace z2
variable {V E : Type*} (G : z2 V E)
def z23 (K : Set E) (u v : V) (s : ℕ) : Set (Set E) :=
  {ω | ¬ (G.z1 ω).Reachable u v} ∩
    {ω | K∩ω ∈ G.z17 u s ∩ G.z17 v s}
lemma z133 {K S : Set E} (hKS : K⊆S) (u v : V) (s : ℕ) :
    G.z23 K u v s ⊆ {ω | S∩ω ∈ G.z15 u v s} := by
  rintro ω ⟨hsep,hu,hv⟩
  refine ⟨⟨?_,G.z24 u s (Set.inter_subset_inter_left _ hKS) hu⟩,
    G.z24 v s (Set.inter_subset_inter_left _ hKS) hv⟩
  intro h
  exact hsep (G.cluster_mono Set.inter_subset_right u h)
lemma z165 [Countable V] [Countable E]
    (K : Set E) (hK : K.Finite) (u v : V) (s : ℕ) :
    MeasurableSet (G.z23 K u v s) :=
  (G.z79 u v).setOf.compl.inter
    (z0.z199 K hK _)
lemma z181 (p : unitInterval) (u v : V) (s : ℕ)
    (K : Set.FiniteExhaustion (Set.univ : Set E)) :
    Tendsto (fun n => (G.law p).real (G.z23 (K n) u v s)) atTop
      (𝓝 ((G.law p).real (G.z15 u v s))) := by
  have ht := z0.z180 p
    (G.z17 u s ∩ G.z17 v s) {ω | ¬(G.z1 ω).Reachable u v}
    ((G.z24 u s).inter (G.z24 v s))
    ((G.z30 u s).inter (G.z30 v s)
      (G.z24 u s) (G.z24 v s)) K
  simpa only [z23,z15,Set.inter_assoc,law,
    ← z0.law_const] using ht
lemma z166 [Countable E] (p : unitInterval) (u v : V) (s : ℕ)
    (hpos : 0 < (G.law p).real (G.z15 u v s)) :
    ∃ K : Set E, K.Finite ∧ (G.law p).real (G.z15 u v s)/2 ≤
      (G.law p).real (G.z23 K u v s) := by
  let K := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  obtain ⟨n,hn⟩ := ((G.z181 p u v s K).eventually
    (eventually_gt_nhds (by linarith : (G.law p).real (G.z15 u v s)/2 <
      (G.law p).real (G.z15 u v s)))).exists
  exact ⟨K n,K.finite n,hn.le⟩
lemma Aut.reachable_map (φ : G.Aut) (ω : Set E) (u v : V) :
    (G.z1 (φ.edge '' ω)).Reachable (φ.vertex u) (φ.vertex v) ↔
      (G.z1 ω).Reachable u v :=
  SimpleGraph.Iso.reachable_iff (φ := Aut.openGraphIso G φ ω)
lemma Aut.z491 (φ : G.Aut) (ω : Set E) (u : V) (s : ℕ) :
    φ.edge '' ω ∈ G.z17 (φ.vertex u) s ↔ ω ∈ G.z17 u s := by
  exact Set.ext_iff.mp (Aut.z514 G φ u s) ω
lemma Aut.z260 (φ : G.Aut) (K : Set E) (u v : V) (s : ℕ) :
    (fun ω : Set E => φ.edge '' ω) ⁻¹'
      G.z23 (φ.edge '' K) (φ.vertex u) (φ.vertex v) s =
        G.z23 K u v s := by
  ext ω
  simp only [z23,Set.mem_preimage,Set.mem_inter_iff,Set.mem_ofPred_eq]
  rw [← Set.image_inter φ.edge.injective,Aut.reachable_map,
    Aut.z491,Aut.z491]
lemma Aut.z379 [Countable V] [Countable E]
    (φ : G.Aut) (p : unitInterval) (K : Set E) (hK : K.Finite) (u v : V) (s : ℕ) :
    (G.law p).real (G.z23 (φ.edge '' K) (φ.vertex u) (φ.vertex v) s) =
      (G.law p).real (G.z23 K u v s) := by
  simp only [measureReal_def]
  congr 1
  conv_lhs => rw [← G.law_map_aut p φ]
  rw [Measure.map_apply (z0.z62 φ.edge)
    (G.z165 _ (hK.image _) _ _ _),
    Aut.z260]
lemma z508 (u v : V) (s : ℕ) :
    G.z15 u v s = G.z15 v u s := by
  ext ω
  simp only [z15,Set.mem_inter_iff,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨h,hu⟩,hv⟩
    exact ⟨⟨fun hc => h hc.symm,hv⟩,hu⟩
  · rintro ⟨⟨h,hv⟩,hu⟩
    exact ⟨⟨fun hc => h hc.symm,hu⟩,hv⟩
lemma z254 {u v x y : V} (h : s(u,v)=s(x,y)) (s : ℕ) :
    G.z15 u v s = G.z15 x y s := by
  rcases Sym2.eq_iff.mp h with h | h
  · rcases h with ⟨rfl,rfl⟩; rfl
  · rcases h with ⟨rfl,rfl⟩; exact G.z508 _ _ _
end z2
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set
open scoped Classical
namespace CriticalPercolation.z2
variable {V E : Type*} [Fintype V] (G : z2 V E)
noncomputable def z16 (ω : Set E) (v : V) : ℕ :=
  (G.cluster ω v).toFinset.card
omit [Fintype V] in
lemma z40 {ω : Set E} {u v : V}
    (h : (G.z1 ω).Reachable u v) : G.cluster ω u = G.cluster ω v := by
  ext z
  exact ⟨fun hz => h.symm.trans hz, fun hz => h.trans hz⟩
omit [Fintype V] in
lemma z161 {ω : Set E} {u v : V}
    (h : ¬ (G.z1 ω).Reachable u v) : Disjoint (G.cluster ω u) (G.cluster ω v) := by
  apply Set.disjoint_left.mpr
  intro z hu hv
  exact h (hu.trans hv.symm)
lemma z332 (ω : Set E) (v : V) : 0 < G.z16 ω v := by
  apply Finset.card_pos.mpr
  exact ⟨v, Set.mem_toFinset.mpr (SimpleGraph.Reachable.refl _)⟩
lemma z296 {ω : Set E} {u v : V}
    (h : (G.z1 ω).Reachable u v) : G.z16 ω u = G.z16 ω v := by
  unfold z16
  rw [G.z40 h]
noncomputable def rootMass (f : ℕ → ℝ) (ω : Set E) (v : V) : ℝ :=
  f (G.z16 ω v) / G.z16 ω v
lemma z125 (f : ℕ → ℝ) (ω : Set E) (u : V) :
    (∑ v, if (G.z1 ω).Reachable u v then G.rootMass f ω v else 0) =
      f (G.z16 ω u) := by
  have he : (fun v => if (G.z1 ω).Reachable u v then G.rootMass f ω v else 0) =
      (fun v => if v ∈ G.cluster ω u then G.rootMass f ω u else 0) := by
    funext v
    by_cases hv : (G.z1 ω).Reachable u v
    · simp only [cluster, Set.mem_ofPred_eq, hv,ite_true,rootMass,
        G.z296 hv]
    · simp [cluster,hv]
  rw [he,Finset.sum_ite]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_zero,add_zero]
  have hfilter : Finset.univ.filter (fun v => v ∈ G.cluster ω u) = (G.cluster ω u).toFinset := by
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Set.mem_toFinset]
  rw [hfilter]
  change (G.z16 ω u : ℝ) * (f (G.z16 ω u) / G.z16 ω u) = _
  field_simp [show (G.z16 ω u : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr (G.z332 ω u).ne']
omit [Fintype V] in
lemma z494 (ω : Set E) (e : E) (x y : V) (he : G.ends e = s(x,y)) (v : V) :
    e ∈ G.z9 (G.cluster ω v) ↔
      (G.z1 ω).Reachable x v ∨ (G.z1 ω).Reachable y v := by
  constructor
  · rintro ⟨z,hz,hze⟩
    rw [he] at hze
    rcases (by simpa using hze : z=x ∨ z=y) with rfl|rfl
    · exact Or.inl hz.symm
    · exact Or.inr hz.symm
  · rintro (hx|hy)
    · exact ⟨x,hx.symm,by simp [he]⟩
    · exact ⟨y,hy.symm,by simp [he]⟩
lemma z222 (f : ℕ → ℝ) (ω : Set E) (e : E) (x y : V)
    (he : G.ends e = s(x,y)) :
    (∑ v, if e ∈ G.z9 (G.cluster ω v) then G.rootMass f ω v else 0) =
      f (G.z16 ω x) + if (G.z1 ω).Reachable x y then 0 else f (G.z16 ω y) := by
  simp_rw [G.z494 ω e x y he]
  by_cases hxy : (G.z1 ω).Reachable x y
  · have hi : ∀ v, ((G.z1 ω).Reachable x v ∨ (G.z1 ω).Reachable y v) ↔
          (G.z1 ω).Reachable x v := fun v =>
        ⟨fun h => h.elim id (fun hy => hxy.trans hy), Or.inl⟩
    simp_rw [hi]
    rw [G.z125,if_pos hxy,add_zero]
  · have hi : ∀ v, (if (G.z1 ω).Reachable x v ∨ (G.z1 ω).Reachable y v
          then G.rootMass f ω v else 0) =
        (if (G.z1 ω).Reachable x v then G.rootMass f ω v else 0) +
        (if (G.z1 ω).Reachable y v then G.rootMass f ω v else 0) := by
      intro v
      by_cases hx : (G.z1 ω).Reachable x v <;>
        by_cases hy : (G.z1 ω).Reachable y v <;> simp [hx,hy]
      exact (hxy (hx.trans hy.symm)).elim
    simp_rw [hi]
    rw [Finset.sum_add_distrib,G.z125,G.z125,if_neg hxy]
omit [Fintype V] in
lemma z169 (ω : Set E) (e : E) (x y : V) (he : G.ends e = s(x,y)) :
    G.cluster (insert e ω) x = G.cluster ω x ∪ G.cluster ω y := by
  ext v
  simp only [cluster,Set.mem_ofPred_eq,Set.mem_union,G.z595 ω e x y he,
    Wiring.z561]
  constructor
  · rintro (h|⟨_,h⟩|⟨_,h⟩)
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h|h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _,h⟩)
lemma z158 (ω : Set E) (e : E) (x y : V)
    (he : G.ends e = s(x,y)) (hxy : ¬ (G.z1 ω).Reachable x y) :
    G.z16 (insert e ω) x = G.z16 ω x + G.z16 ω y := by
  unfold z16
  rw [G.z169 ω e x y he,Set.toFinset_union,Finset.card_union_of_disjoint]
  exact Set.disjoint_toFinset.mpr (G.z161 hxy)
lemma z195 (ω : Set E) (e : E) (x y : V)
    (he : G.ends e = s(x,y)) (hxy : (G.z1 ω).Reachable x y) :
    G.z16 (insert e ω) x = G.z16 ω x := by
  unfold z16
  rw [G.z169 ω e x y he,G.z40 hxy,Set.union_self]
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set
open scoped Classical
namespace CriticalPercolation
lemma z577 {a b : ℝ} (ha : 0≤a) (hb : 0≤b) :
    0 ≤ min a 1 + min b 1 - min (a+b) 1 := by
  rcases le_total a 1 with ha1|ha1 <;> rcases le_total b 1 with hb1|hb1
  · rw [min_eq_left ha1,min_eq_left hb1]
    exact sub_nonneg.mpr (min_le_left _ _)
  · rw [min_eq_left ha1,min_eq_right hb1]
    linarith [min_le_right (a+b) 1]
  · rw [min_eq_right ha1,min_eq_left hb1]
    linarith [min_le_right (a+b) 1]
  · rw [min_eq_right ha1,min_eq_right hb1]
    linarith [min_le_right (a+b) 1]
def cappedMass (s m : ℕ) : ℝ := min ((m:ℝ)/s) 1
lemma z569 (s m : ℕ) : 0≤cappedMass s m := by
  unfold cappedMass
  positivity
lemma cappedMass_gap (s a b : ℕ) (hs : 0<s) :
    (if s≤a ∧ s≤b then (1:ℝ) else 0) ≤
      cappedMass s a + cappedMass s b - cappedMass s (a+b) := by
  have hs' : 0<(s:ℝ) := Nat.cast_pos.mpr hs
  simp only [cappedMass,Nat.cast_add,add_div]
  split_ifs with h
  · have ha : 1 ≤ (a:ℝ)/s := (le_div_iff₀ hs').mpr (by simpa only [one_mul] using (Nat.cast_le.mpr h.1 : (s:ℝ)≤a))
    have hb : 1 ≤ (b:ℝ)/s := (le_div_iff₀ hs').mpr (by simpa only [one_mul] using (Nat.cast_le.mpr h.2 : (s:ℝ)≤b))
    rw [min_eq_right ha,min_eq_right hb]
    linarith [min_le_right ((a:ℝ)/s+(b:ℝ)/s) 1]
  · exact z577 (by positivity) (by positivity)
namespace z2
open z8
variable {V E : Type*} [Fintype V] (G : z2 V E)
def z20 (f : ℕ → ℝ) (ω : Set E) (e : E) : ℝ :=
  ∑ v, if e ∈ G.z9 (G.cluster ω v) then G.rootMass f ω v else 0
lemma z320 (f : ℕ → ℝ) (ω : Set E) (e : E) (x y : V)
    (he : G.ends e = s(x,y)) :
    G.z20 f ω e - G.z20 f (insert e ω) e =
      if (G.z1 ω).Reachable x y then 0 else
        f (G.z16 ω x) + f (G.z16 ω y) -
          f (G.z16 ω x + G.z16 ω y) := by
  have hopen : (G.z1 (insert e ω)).Reachable x y :=
    LazyDFS.z174 G (insert e ω) (Set.mem_insert e ω) he
  simp only [z20,G.z222 f ω e x y he,
    G.z222 f (insert e ω) e x y he,if_pos hopen,add_zero]
  by_cases hc : (G.z1 ω).Reachable x y
  · rw [if_pos hc,G.z195 ω e x y he hc]
    simp only [if_pos hc,add_zero,sub_self]
  · rw [if_neg hc,G.z158 ω e x y he hc,if_neg hc]
lemma z599 (ω : Set E) (e : E) (x y : V) (he : G.ends e = s(x,y))
    (s : ℕ) (hs : 0<s) :
    (if BinaryLaw.endpointEvent G x y s ω then (1:ℝ) else 0) ≤
      G.z20 (cappedMass s) ω e - G.z20 (cappedMass s) (insert e ω) e := by
  rw [G.z320 _ ω e x y he]
  by_cases hc : (G.z1 ω).Reachable x y
  · simp [BinaryLaw.endpointEvent,hc]
  · have hh := cappedMass_gap s (G.z16 ω x) (G.z16 ω y) hs
    simp only [BinaryLaw.endpointEvent,hc,not_false_eq_true,true_and,ite_false,z16,
      ← Set.ncard_eq_toFinset_card'] at hh ⊢
    exact hh
variable [Fintype E]
def clusterDiscrepancy (p : ℝ) (ω : Set E) (v : V) : ℝ :=
  ∑ e, if e ∈ G.z9 (G.cluster ω v) then (if ω e then -(1-p)/p else 1) else 0
def edgeDiscrepancy (f : ℕ → ℝ) (p : ℝ) (ω : Set E) (e : E) : ℝ :=
  (if ω e then -(1-p)/p else 1) * G.z20 f ω e
lemma z448 (f : ℕ → ℝ) (p : ℝ) (hp : p ∈ Set.Ioo 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b=1)
    (e : E) (h0 : w e False=1-p) (h1 : w e True=p) :
    expect w (fun ω => G.edgeDiscrepancy f p ω e) =
      expect w (fun ω => if ¬ω e then
        G.z20 f ω e - G.z20 f (insert e ω) e else 0) := by
  let : DecidableEq E := Classical.decEq E
  have hflip := z280 w hw e hp h0 h1 (fun ω => G.z20 f ω e / p)
  have hu (ω : Set E) : {a | Function.update ω e True a} = insert e ω := by
    ext a
    change Function.update (fun a => ω a) e True a ↔ a=e ∨ a∈ω
    by_cases ha : a=e
    · subst a; simp [Function.update]
    · simp only [Function.update_of_ne ha,ha,false_or]; rfl
  have hleft : (fun ω : Set E => if ¬ω e then p*(G.z20 f (Function.update ω e True) e / p) else 0) =
      (fun ω => if ¬ω e then G.z20 f (insert e ω) e else 0) := by
    funext ω
    rw [show (Function.update ω e True : Set E) = insert e ω from hu ω]
    split_ifs <;> field_simp [hp.1.ne']
  erw [hleft] at hflip
  have heq (ω : Set E) : G.edgeDiscrepancy f p ω e =
      (if ¬ω e then G.z20 f ω e else 0) -
        (if ω e then (1-p)*(G.z20 f ω e / p) else 0) := by
    change (if ω e then -(1-p)/p else 1) * G.z20 f ω e = _
    by_cases hb : ω e <;> simp only [hb,ite_true,ite_false,not_true_eq_false,not_false_eq_true,sub_zero,zero_sub,one_mul]
    ring
  have hfunc : (fun ω : Set E => G.edgeDiscrepancy f p ω e) =
      (fun ω => (if ¬ω e then G.z20 f ω e else 0) -
        (if ω e then (1-p)*(G.z20 f ω e / p) else 0)) := funext heq
  erw [hfunc]
  erw [expect_sub,← hflip,← expect_sub]
  congr 1
  funext ω
  by_cases hb : ω e <;> simp [hb]
lemma z261 (p : ℝ) (hp : p ∈ Set.Ioo 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b=1) (hn : ∀ e b, 0≤w e b)
    (e : E) (x y : V) (he : G.ends e = s(x,y))
    (h0 : w e False=1-p) (h1 : w e True=p) (s : ℕ) (hs : 0<s) :
    prob w (BinaryLaw.endpointEvent G x y s) ≤
      expect w (fun ω => G.edgeDiscrepancy (cappedMass s) p ω e) := by
  rw [G.z448 _ p hp w hw e h0 h1]
  apply expect_mono hn
  intro ω
  by_cases hb : ω e
  · have hconn : (G.z1 ω).Reachable x y := LazyDFS.z174 G ω hb he
    simp [hb,BinaryLaw.endpointEvent,hconn]
  · simp only [hb,not_false_eq_true,ite_true]
    exact G.z599 ω e x y he s hs
lemma z538 (f : ℕ → ℝ) (p : ℝ) (ω : Set E) :
    (∑ e, G.edgeDiscrepancy f p ω e) =
      ∑ v, G.rootMass f ω v * G.clusterDiscrepancy p ω v := by
  simp only [edgeDiscrepancy,z20,clusterDiscrepancy,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> ring
end z2
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set
open scoped Classical
namespace CriticalPercolation.z2
variable {V E : Type*} [Fintype V] [Fintype E] (G : z2 V E)
lemma incident_card_le (S : Set V) (D : ℕ)
    (hD : ∀ v, (G.z9 {v}).toFinset.card ≤ D) :
    (G.z9 S).toFinset.card ≤ S.toFinset.card * D := by
  have he : (G.z9 S).toFinset =
      S.toFinset.biUnion (fun v => (G.z9 {v}).toFinset) := by
    ext e
    constructor
    · intro hh
      obtain ⟨v,hv,hev⟩ := Set.mem_toFinset.mp hh
      exact Finset.mem_biUnion.mpr ⟨v,Set.mem_toFinset.mpr hv,
        Set.mem_toFinset.mpr ⟨v,Set.mem_singleton v,hev⟩⟩
    · intro hh
      obtain ⟨v,hv,hev⟩ := Finset.mem_biUnion.mp hh
      obtain ⟨z,hz,he⟩ := Set.mem_toFinset.mp hev
      have hzv : z=v := Set.mem_singleton_iff.mp hz
      subst z
      exact Set.mem_toFinset.mpr ⟨v,Set.mem_toFinset.mp hv,he⟩
  rw [he]
  calc _ ≤ ∑ v ∈ S.toFinset, (G.z9 {v}).toFinset.card := Finset.card_biUnion_le
       _ ≤ ∑ _v ∈ S.toFinset, D := Finset.sum_le_sum (fun v _ => hD v)
       _ = _ := by simp
omit [Fintype E] in
lemma z545 (s : ℕ) (hs : 0<s) (ω : Set E) (v : V) :
    G.rootMass (cappedMass s) ω v = min (1/(s:ℝ)) (1/(G.z16 ω v : ℝ)) := by
  have hm : (0:ℝ)<G.z16 ω v := Nat.cast_pos.mpr (G.z332 ω v)
  have hs' : (0:ℝ)<s := Nat.cast_pos.mpr hs
  unfold rootMass cappedMass
  by_cases hms : (G.z16 ω v : ℝ)/s ≤ 1
  · rw [min_eq_left hms,min_eq_left]
    · field_simp
    · apply (div_le_div_iff₀ hs' hm).mpr
      have hh := (div_le_one hs').mp hms
      simpa only [one_mul] using hh
  · have hh : (s:ℝ) ≤ G.z16 ω v := by
      have hh := le_of_lt (lt_of_not_ge hms)
      exact (one_le_div hs').mp hh
    rw [min_eq_right (le_of_lt (lt_of_not_ge hms)),min_eq_right]
    apply (div_le_div_iff₀ hm hs').mpr
    simpa only [one_mul] using hh
omit [Fintype E] in
lemma z350 (s T D : ℕ) (hs : 0<s) (hT : 0<T) (hD : 1≤D)
    (ω : Set E) (v : V) (hTD : T ≤ D*G.z16 ω v) :
    G.rootMass (cappedMass s) ω v ≤ (D:ℝ)*min (1/(s:ℝ)) (1/(T:ℝ)) := by
  rw [G.z545 s hs ω v,mul_min_of_nonneg _ _ (Nat.cast_nonneg D)]
  apply le_min
  · calc min (1/(s:ℝ)) (1/(G.z16 ω v : ℝ)) ≤ 1/(s:ℝ) := min_le_left _ _
         _ ≤ (D:ℝ)*(1/(s:ℝ)) := by
           exact le_mul_of_one_le_left (by positivity) (Nat.one_le_cast.mpr hD)
  · calc min (1/(s:ℝ)) (1/(G.z16 ω v : ℝ)) ≤ 1/(G.z16 ω v : ℝ) := min_le_right _ _
         _ ≤ (D:ℝ)*(1/(T:ℝ)) := by
           rw [mul_one_div]
           apply (div_le_div_iff₀ (Nat.cast_pos.mpr (G.z332 ω v)) (Nat.cast_pos.mpr hT)).mpr
           simpa only [one_mul,Nat.cast_mul] using (Nat.cast_le.mpr hTD : (T:ℝ)≤ (D*G.z16 ω v : ℕ))
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
namespace CriticalPercolation.z18
open scoped Classical
open z8
variable {E R : Type*}
def z13 : z18 E R → (E → Prop) → ℕ
  | .done _, _ => 0
  | .ask e l r, ω => 1 + if ω e then z13 r ω else z13 l ω
def centeredSum (p : ℝ) : z18 E R → (E → Prop) → ℝ
  | .done _, _ => 0
  | .ask e l r, ω => if ω e then (1-p)+centeredSum p r ω else -p+centeredSum p l ω
def truncate : z18 E R → ℕ → z18 E Unit
  | _, 0 => .done ()
  | .done _, _+1 => .done ()
  | .ask e l r, n+1 => .ask e (truncate l n) (truncate r n)
lemma truncate_valid [DecidableEq E] (t : z18 E R) (n : ℕ) (used : Finset E)
    (h : t.Valid used) : (t.truncate n).Valid used := by
  induction n generalizing t used with
  | zero => simp [truncate,Valid]
  | succ n ih =>
    cases t with
    | done r => trivial
    | ask e l r => exact ⟨h.1, ih l _ h.2.1, ih r _ h.2.2⟩
lemma z453 (t : z18 E R) (n : ℕ) (ω : E → Prop) :
    (t.truncate n).z13 ω ≤ n := by
  induction n generalizing t with
  | zero => simp [truncate,z13]
  | succ n ih =>
    cases t with
    | done r => simp [truncate,z13]
    | ask e l r =>
      simp only [truncate,z13]
      split_ifs <;> have := ih r <;> have := ih l <;> omega
lemma z402 (t : z18 E R) (n : ℕ) (ω : E → Prop)
    (h : t.z13 ω ≤ n) (p : ℝ) :
    (t.truncate n).centeredSum p ω = t.centeredSum p ω := by
  induction n generalizing t with
  | zero =>
    cases t with
    | done r => rfl
    | ask e l r => simp [z13] at h
  | succ n ih =>
    cases t with
    | done r => rfl
    | ask e l r =>
      by_cases he : ω e
      · simp only [z13,if_pos he] at h
        simp only [truncate,centeredSum,if_pos he]
        rw [ih r (by omega)]
      · simp only [z13,if_neg he] at h
        simp only [truncate,centeredSum,if_neg he]
        rw [ih l (by omega)]
variable [Fintype E] [DecidableEq E]
lemma z312 (t : z18 E R) (used : Finset E) (ht : t.Valid used)
    (p : ℝ) (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hf : LazyDFS.Fresh w p used) :
    expect w (t.centeredSum p) = 0 ∧
      expect w (fun ω => (t.centeredSum p ω)^2) =
        p*(1-p)*expect w (fun ω => (t.z13 ω : ℝ)) := by
  induction t generalizing used w with
  | done r => simp [centeredSum,z13,expect_const w hw]
  | ask e l r hl hr =>
    have h0 := hl (insert e used) ht.2.1 (pin w e False)
      (pin_normalized w hw e False) (LazyDFS.fresh_pin w p used hf e False)
    have h1 := hr (insert e used) ht.2.2 (pin w e True)
      (pin_normalized w hw e True) (LazyDFS.fresh_pin w p used hf e True)
    have he := hf e ht.1
    constructor
    · simp only [centeredSum]
      erw [z317]
      simp only [expect_add, expect_const _ (pin_normalized w hw e False),
        expect_const _ (pin_normalized w hw e True),h0.1,h1.1,he.1,he.2]
      ring
    · have hx : (fun ω => ((.ask e l r : z18 E R).centeredSum p ω)^2) =
          (fun ω => if ω e then ((1-p)+r.centeredSum p ω)^2
            else (-p+l.centeredSum p ω)^2) := by funext ω; simp only [centeredSum]; split_ifs <;> rfl
      rw [hx]
      erw [z317,
        z168 _ (pin_normalized w hw e False),
        z168 _ (pin_normalized w hw e True),h0.1,h1.1,h0.2,h1.2,he.1,he.2]
      have hc : (fun ω => ((.ask e l r : z18 E R).z13 ω : ℝ)) =
          (fun ω => 1+(if ω e then (r.z13 ω : ℝ) else (l.z13 ω : ℝ))) := by
        funext ω; simp only [z13]; split_ifs <;> simp
      rw [hc,expect_add]
      erw [z317,expect_const w hw,he.1,he.2]
      ring
lemma z531 (t : z18 E R) (used : Finset E) (ht : t.Valid used)
    (p : ℝ) (hp : p ∈ Set.Icc 0 1) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0 ≤ w e b)
    (hf : LazyDFS.Fresh w p used) (n : ℕ) :
    expect w (fun ω => ((t.truncate n).centeredSum p ω)^2) ≤ p*(1-p)*n := by
  rw [(t.truncate n).z312 used (t.truncate_valid n used ht) p w hw hf |>.2]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hp.1 (sub_nonneg.mpr hp.2))
  calc expect w (fun ω => ((t.truncate n).z13 ω : ℝ)) ≤ expect w (fun _ => (n:ℝ)) :=
        expect_mono hn (fun ω => Nat.cast_le.mpr (t.z453 n ω))
       _ = n := expect_const w hw _
end CriticalPercolation.z18
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set
open scoped Classical
namespace CriticalPercolation.IncidenceSearch
structure State (E : Type*) where
  opened : Finset E
  read : Finset E
variable {V E : Type*} [DecidableEq E]
 def State.closed (st : State E) (e : E) : State E := ⟨st.opened,insert e st.read⟩
 def State.open (st : State E) (e : E) : State E := ⟨insert e st.opened,insert e st.read⟩
 def Available (G : z2 V E) (v : V) (st : State E) (e : E) : Prop :=
  e ∉ st.read ∧ e ∈ G.z9 (G.cluster (st.opened : Set E) v)
 def compile (G : z2 V E) (v : V) : ℕ → State E → z18 E (State E)
  | 0, st => .done st
  | n+1, st => if h : ∃ e, Available G v st e then
      let e := h.choose
      .ask e (compile G v n (st.closed e)) (compile G v n (st.open e))
    else .done st
lemma compile_valid (G : z2 V E) (v : V) (n : ℕ) (st : State E) :
    (compile G v n st).Valid st.read := by
  induction n generalizing st with
  | zero => trivial
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · exact ⟨h.choose_spec.1,ih _,ih _⟩
    · trivial
 def Good (G : z2 V E) (v : V) (ω : Set E) (st : State E) : Prop :=
  st.opened ⊆ st.read ∧
  (∀ e ∈ st.read, e ∈ st.opened ↔ e ∈ ω) ∧
  ∀ e ∈ st.read, e ∈ G.z9 (G.cluster (st.opened : Set E) v)
lemma good_closed (G : z2 V E) (v : V) (ω : Set E) (st : State E)
    (hs : Good G v ω st) (e : E) (he : Available G v st e) (hω : e ∉ ω) :
    Good G v ω (st.closed e) := by
  refine ⟨fun a ha => Finset.mem_insert_of_mem (hs.1 ha),?_,?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl|ha
    · exact iff_of_false (fun h => he.1 (hs.1 h)) hω
    · exact hs.2.1 a ha
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl|ha
    · exact he.2
    · exact hs.2.2 a ha
lemma good_open (G : z2 V E) (v : V) (ω : Set E) (st : State E)
    (hs : Good G v ω st) (e : E) (he : Available G v st e) (hω : e ∈ ω) :
    Good G v ω (st.open e) := by
  refine ⟨Finset.insert_subset_insert e hs.1,?_,?_⟩
  · intro a ha
    rcases Finset.mem_insert.mp ha with rfl|ha
    · exact iff_of_true (Finset.mem_insert_self _ _) hω
    · have hae : a≠e := fun hh => he.1 (hh ▸ ha)
      simpa only [State.open,Finset.mem_insert,hae,false_or] using hs.2.1 a ha
  · intro a ha
    change a ∈ G.z9 (G.cluster ((insert e st.opened : Finset E) : Set E) v)
    rw [Finset.coe_insert]
    apply G.z547 (G.cluster_mono (Set.subset_insert e (st.opened : Set E)) v)
    rcases Finset.mem_insert.mp ha with rfl|ha
    · exact he.2
    · exact hs.2.2 a ha
lemma z586 (G : z2 V E) (v : V) (ω : Set E) (st : State E)
    (hs : Good G v ω st) (ht : ¬∃ e, Available G v st e) :
    G.cluster ω v = G.cluster (st.opened : Set E) v ∧
      (st.read : Set E) = G.z9 (G.cluster ω v) := by
  have hread : ∀ e ∈ G.z9 (G.cluster (st.opened : Set E) v), e ∈ st.read := by
    intro e he
    by_contra hh
    exact ht ⟨e,hh,he⟩
  have hc : G.cluster ω v = G.cluster (st.opened : Set E) v := by
    have hh := G.z500 (S := {v}) (U := G.cluster (st.opened : Set E) v)
      (ω := (st.opened : Set E)) (ω' := ω)
      (by simp only [ClusterDeletion.z84,ClusterDeletion.component,z2.cluster])
      (fun e he => hs.2.1 e (hread e he))
    simpa only [ClusterDeletion.z84,ClusterDeletion.component,z2.cluster] using hh
  refine ⟨hc,?_⟩
  rw [hc]
  exact Set.Subset.antisymm hs.2.2 hread
variable [Fintype E]
lemma z587 (G : z2 V E) (v : V) (ω : Set E) (n : ℕ) (st : State E)
    (hs : Good G v ω st) (hn : Fintype.card E - st.read.card < n) :
    let out := (compile G v n st).run (fun e => decide (e∈ω))
    Good G v ω out ∧ ¬∃ e, Available G v out e := by
  induction n generalizing st with
  | zero => omega
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · let e := h.choose
      have he : Available G v st e := h.choose_spec
      have hc : (insert e st.read).card = st.read.card+1 := Finset.card_insert_of_notMem he.1
      have hle : st.read.card < Fintype.card E := by
        have hh := Finset.card_le_univ (s := insert e st.read)
        rw [hc] at hh
        omega
      have hn' : Fintype.card E - (insert e st.read).card < n := by rw [hc]; omega
      simp only [z18.run]
      change (let out := if decide (e∈ω) then
        (compile G v n (st.open e)).run (fun a => decide (a∈ω)) else
        (compile G v n (st.closed e)).run (fun a => decide (a∈ω));
        Good G v ω out ∧ ¬∃ a, Available G v out a)
      by_cases hω : e∈ω
      · simp only [hω,decide_true,ite_true]
        exact ih (st.open e) (good_open G v ω st hs e he hω) hn'
      · simp only [hω,decide_false,Bool.false_eq_true,ite_false]
        exact ih (st.closed e) (good_closed G v ω st hs e he hω) hn'
    · exact ⟨hs,h⟩
end CriticalPercolation.IncidenceSearch
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set
open scoped Classical
namespace CriticalPercolation.IncidenceSearch
variable {V E : Type*}
 def readSum (p : ℝ) (ω : Set E) (st : State E) : ℝ :=
  ∑ e ∈ st.read, if e∈ω then 1-p else -p
lemma compile_trace (G : z2 V E) (v : V) (n : ℕ) (st : State E)
    (ω : Set E) (p : ℝ) :
    let t := compile G v n st
    let out := t.run (fun e => decide (e∈ω))
    t.z13 ω + st.read.card = out.read.card ∧
      t.centeredSum p ω + readSum p ω st = readSum p ω out := by
  induction n generalizing st with
  | zero => simp [compile,z18.run,z18.z13,z18.centeredSum]
  | succ n ih =>
    rw [compile]
    split_ifs with h
    · let e := h.choose
      have he : e∉st.read := h.choose_spec.1
      have hopen := ih (st.open e)
      have hclosed := ih (st.closed e)
      have hcard : (insert e st.read).card = st.read.card + 1 := Finset.card_insert_of_notMem he
      have hsum : readSum p ω (st.open e) =
          (if e∈ω then 1-p else -p)+readSum p ω st := by
        simp only [readSum,State.open,Finset.sum_insert he]
      have hsum' : readSum p ω (st.closed e) =
          (if e∈ω then 1-p else -p)+readSum p ω st := by
        simp only [readSum,State.closed,Finset.sum_insert he]
      change (let out := if decide (e∈ω) then
        (compile G v n (st.open e)).run (fun a => decide (a∈ω)) else
        (compile G v n (st.closed e)).run (fun a => decide (a∈ω));
        (1 + if ω e then (compile G v n (st.open e)).z13 ω else
          (compile G v n (st.closed e)).z13 ω) + st.read.card = out.read.card ∧
        (if ω e then (1-p)+(compile G v n (st.open e)).centeredSum p ω else
          -p+(compile G v n (st.closed e)).centeredSum p ω) + readSum p ω st = readSum p ω out)
      by_cases hω : e∈ω
      · have hω' : ω e := hω
        simp only [hω,hω',decide_true,ite_true]
        dsimp only at hopen
        constructor
        · have hh := hopen.1
          change _ + (insert e st.read).card = _ at hh
          rw [hcard] at hh
          omega
        · rw [hsum,if_pos hω] at hopen
          linarith [hopen.2]
      · have hω' : ¬ω e := hω
        simp only [hω,hω',decide_false,Bool.false_eq_true,ite_false]
        dsimp only at hclosed
        constructor
        · have hh := hclosed.1
          change _ + (insert e st.read).card = _ at hh
          rw [hcard] at hh
          omega
        · rw [hsum',if_neg hω] at hclosed
          linarith [hclosed.2]
    · simp [z18.run,z18.z13,z18.centeredSum]
variable [Fintype E]
 def tree (G : z2 V E) (v : V) : z18 E (State E) :=
  compile G v (Fintype.card E + 1) ⟨∅,∅⟩
lemma tree_valid (G : z2 V E) (v : V) : (tree G v).Valid ∅ :=
  compile_valid G v _ _
lemma tree_read (G : z2 V E) (v : V) (ω : Set E) :
    (((tree G v).run (fun e => decide (e∈ω))).read : Set E) =
      G.z9 (G.cluster ω v) := by
  have hg : Good G v ω (⟨∅,∅⟩ : State E) := by simp [Good]
  have hh := z587 G v ω (Fintype.card E+1) ⟨∅,∅⟩ hg (by simp)
  exact (z586 G v ω _ hh.1 hh.2).2
lemma tree_mem_read (G : z2 V E) (v : V) (ω : Set E) (e : E) :
    e ∈ ((tree G v).run (fun a => decide (a∈ω))).read ↔
      e ∈ G.z9 (G.cluster ω v) := by
  exact Set.ext_iff.mp (tree_read G v ω) e
lemma tree_count (G : z2 V E) (v : V) (ω : Set E) :
    (tree G v).z13 ω = (G.z9 (G.cluster ω v)).toFinset.card := by
  have h := (compile_trace G v (Fintype.card E+1) ⟨∅,∅⟩ ω (0:ℝ)).1
  change (tree G v).z13 ω + (∅ : Finset E).card =
    ((tree G v).run (fun e => decide (e∈ω))).read.card at h
  simp only [Finset.card_empty,add_zero] at h
  refine h.trans (congrArg Finset.card ?_)
  ext e
  rw [Set.mem_toFinset]
  exact tree_mem_read G v ω e
lemma tree_centered (G : z2 V E) (v : V) (ω : Set E) (p : ℝ) :
    (tree G v).centeredSum p ω = ∑ e,
      if e∈G.z9 (G.cluster ω v) then (if e∈ω then 1-p else -p) else 0 := by
  have h := (compile_trace G v (Fintype.card E+1) ⟨∅,∅⟩ ω p).2
  change (tree G v).centeredSum p ω + readSum p ω ⟨∅,∅⟩ =
    readSum p ω ((tree G v).run (fun e => decide (e∈ω))) at h
  simp only [readSum,Finset.sum_empty,add_zero] at h
  rw [h]
  calc
    _ = ∑ e, if e∈((tree G v).run (fun a => decide (a∈ω))).read then
        (if e∈ω then 1-p else -p) else 0 := by
      simp only [← Finset.sum_filter]
      congr 1
      ext e
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      simp only [tree_mem_read]
end CriticalPercolation.IncidenceSearch
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
namespace CriticalPercolation.z8
open scoped Classical
variable {E : Type*} [Fintype E]
lemma z585 (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hn : ∀ e b, 0≤w e b) (f : (E → Prop) → ℝ) :
    (expect w (fun ω => |f ω|))^2 ≤ expect w (fun ω => (f ω)^2) := by
  have h := FiniteEntropy.z612 (density w) (fun ω => |f ω|) (fun _ => 1)
    (fun ω => density_nonneg hn ω)
  simp only [mul_one,one_pow,sq_abs] at h
  have hw1 : ∑ ω, density w ω = 1 := by
    simpa only [expect,mul_one] using expect_const w hw (1:ℝ)
  simpa only [hw1,mul_one,expect] using h
lemma z326 (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hn : ∀ e b, 0≤w e b) (f : (E → Prop) → ℝ) {a : ℝ} (ha : 0≤a)
    (hf : expect w (fun ω => (f ω)^2) ≤ a^2) : expect w (fun ω => |f ω|) ≤ a := by
  nlinarith [z585 w hw hn f]
end CriticalPercolation.z8
namespace CriticalPercolation.z18
open scoped Classical
open z8
variable {E R : Type*}
lemma z327 (t : z18 E R) (ω : E → Prop) :
    t.z13 ω = (t.reads (fun e => decide (ω e))).length := by
  induction t with
  | done r => rfl
  | ask e l r hl hr =>
    by_cases he : ω e <;> simp [z13,reads,he,hl,hr,Nat.add_comm]
lemma z93 (t : z18 E R) (ω : E → Prop)
    (h : t.z13 ω = 0) (p : ℝ) : t.centeredSum p ω = 0 := by
  cases t with
  | done r => rfl
  | ask e l r => simp [z13] at h
variable [Fintype E] [DecidableEq E]
lemma z560 (t : z18 E R) (used : Finset E) (ht : t.Valid used)
    (ω : E → Prop) : t.z13 ω ≤ Fintype.card E := by
  rw [z327]
  exact List.Nodup.length_le_card (t.reads_nodup used ht _)
lemma z520 (t : z18 E R) (used : Finset E) (ht : t.Valid used)
    (p : ℝ) (hp : p ∈ Set.Icc 0 1) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0≤w e b)
    (hf : LazyDFS.Fresh w p used) (k : ℕ) :
    expect w (fun ω => if 4^k ≤ t.z13 ω ∧ t.z13 ω < 4^(k+1)
      then |t.centeredSum p ω| else 0) ≤ (2:ℝ)^(k+1) := by
  calc
    _ ≤ expect w (fun ω => |(t.truncate (4^(k+1))).centeredSum p ω|) := by
      apply expect_mono hn
      intro ω
      split_ifs with h
      · rw [t.z402 _ ω h.2.le p]
      · exact abs_nonneg _
    _ ≤ (2:ℝ)^(k+1) := by
      apply z326 w hw hn _ (by positivity)
      have ht' := t.z531 used ht p hp w hw hn hf (4^(k+1))
      have hpp : p*(1-p) ≤ 1 := by nlinarith [hp.2,sq_nonneg p]
      have hN : (4^(k+1) : ℝ) = ((2:ℝ)^(k+1))^2 := by
        rw [← pow_mul, mul_comm (k+1) 2, pow_mul]
        norm_num
      calc _ ≤ p*(1-p)*(4^(k+1) : ℕ) := ht'
           _ ≤ (4^(k+1) : ℝ) := by
             simpa using mul_le_mul_of_nonneg_right hpp (by positivity : 0≤(4^(k+1):ℝ))
           _ = _ := hN
end CriticalPercolation.z18
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open scoped BigOperators
namespace CriticalPercolation
lemma sum_two_pow (N : ℕ) : ∑ k ∈ Finset.range N, (2:ℝ)^k = 2^N-1 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ,ih,pow_succ]; ring
lemma z610 (N : ℕ) : ∑ k ∈ Finset.range N, 1/(2:ℝ)^k = 2-2/2^N := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,pow_succ]
    field_simp
    ring
lemma z589 (N K : ℕ) :
    (∑ k ∈ Finset.range N,
      min ((2:ℝ)^(k+1)/4^K) ((2:ℝ)^(k+1)/4^k)) ≤ 6/2^K := by
  have hfour (k : ℕ) : (4:ℝ)^k = (2^k)^2 := by
    rw [← pow_mul,mul_comm k 2,pow_mul]
    norm_num
  have hnonneg (k : ℕ) : 0 ≤ min ((2:ℝ)^(k+1)/4^K) ((2:ℝ)^(k+1)/4^k) := by positivity
  calc
    _ ≤ ∑ k ∈ Finset.range (K+N),
        min ((2:ℝ)^(k+1)/4^K) ((2:ℝ)^(k+1)/4^k) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      intro k _ _
      exact hnonneg k
    _ = (∑ k ∈ Finset.range K,
        min ((2:ℝ)^(k+1)/4^K) ((2:ℝ)^(k+1)/4^k)) +
        ∑ k ∈ Finset.range N,
        min ((2:ℝ)^(K+k+1)/4^K) ((2:ℝ)^(K+k+1)/4^(K+k)) :=
      Finset.sum_range_add _ _ _
    _ ≤ (∑ k ∈ Finset.range K, (2:ℝ)^(k+1)/4^K) +
        ∑ k ∈ Finset.range N, (2:ℝ)^(K+k+1)/4^(K+k) := by
      apply add_le_add
      · exact Finset.sum_le_sum (fun k _ => min_le_left _ _)
      · exact Finset.sum_le_sum (fun k _ => min_le_right _ _)
    _ ≤ 6/2^K := by
      have h1 : (∑ k ∈ Finset.range K, (2:ℝ)^(k+1)/4^K) =
          2*(2^K-1)/4^K := by
        simp only [pow_succ,mul_div_assoc]
        rw [← Finset.sum_mul,sum_two_pow]
        ring
      have h2 : (∑ k ∈ Finset.range N, (2:ℝ)^(K+k+1)/4^(K+k)) =
          2/2^K * (2-2/2^N) := by
        have he (k : ℕ) : (2:ℝ)^(K+k+1)/4^(K+k) = (2/2^K)*(1/2^k) := by
          rw [hfour,pow_succ,pow_add]
          field_simp
        simp_rw [he]
        rw [← Finset.mul_sum,z610]
      rw [h1,h2,hfour]
      have hpowK : (0:ℝ)<2^K := by positivity
      have hpowN : (0:ℝ)<2^N := by positivity
      have h1' : 2*((2:ℝ)^K-1)/((2:ℝ)^K)^2 ≤ 2/2^K := by
        apply (div_le_iff₀ (sq_pos_of_pos hpowK)).mpr
        field_simp
        nlinarith
      have h2' : (2/(2:ℝ)^K) * (2-2/2^N) ≤ 4/2^K := by
        calc _ ≤ (2/(2:ℝ)^K)*2 := mul_le_mul_of_nonneg_left (by have := (div_nonneg (by norm_num : (0:ℝ)≤2) hpowN.le); linarith) (by positivity)
             _ = _ := by ring
      calc _ ≤ 2/(2:ℝ)^K+4/2^K := add_le_add h1' h2'
           _ = _ := by ring
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
namespace CriticalPercolation.z18
open scoped Classical
open z8
variable {E R : Type*} [Fintype E] [DecidableEq E]
lemma z347 (t : z18 E R) (used : Finset E) (ht : t.Valid used)
    (p : ℝ) (hp : p ∈ Set.Icc 0 1) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hn : ∀ e b, 0≤w e b)
    (hf : LazyDFS.Fresh w p used) (K : ℕ) :
    expect w (fun ω => |t.centeredSum p ω| *
      min (1/(4:ℝ)^K) (1/(t.z13 ω : ℝ))) ≤ 6/(2:ℝ)^K := by
  let N := Fintype.card E + 1
  let a (k : ℕ) := min (1/(4:ℝ)^K) (1/(4:ℝ)^k)
  let b (k : ℕ) (ω : E → Prop) :=
    if 4^k ≤ t.z13 ω ∧ t.z13 ω < 4^(k+1)
      then |t.centeredSum p ω| else 0
  have ha (k : ℕ) : 0≤a k := by dsimp [a]; positivity
  have hb (k : ℕ) (ω : E → Prop) : 0≤b k ω := by
    dsimp [b]; split_ifs <;> positivity
  have hpoint (ω : E → Prop) : |t.centeredSum p ω| *
      min (1/(4:ℝ)^K) (1/(t.z13 ω : ℝ)) ≤
        ∑ k ∈ Finset.range N, b k ω * a k := by
    by_cases hT : t.z13 ω = 0
    · rw [t.z93 ω hT p,abs_zero,zero_mul]
      exact Finset.sum_nonneg (fun k _ => mul_nonneg (hb k ω) (ha k))
    · let k := Nat.log 4 (t.z13 ω)
      have hklo : 4^k ≤ t.z13 ω := Nat.pow_log_le_self 4 hT
      have hkhi : t.z13 ω < 4^(k+1) := Nat.lt_pow_succ_log_self (by omega) _
      have hkN : k ∈ Finset.range N := by
        apply Finset.mem_range.mpr
        have h1 := Nat.log_le_self 4 (t.z13 ω)
        have h2 := t.z560 used ht ω
        dsimp [k,N]
        omega
      calc
        _ ≤ b k ω * a k := by
          have hband : 4^k ≤ t.z13 ω ∧ t.z13 ω < 4^(k+1) := ⟨hklo,hkhi⟩
          simp only [b,if_pos hband]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply min_le_min le_rfl
          apply one_div_le_one_div_of_le (by positivity : (0:ℝ)<(4:ℝ)^k)
          exact_mod_cast hklo
        _ ≤ _ := Finset.single_le_sum (fun j _ => mul_nonneg (hb j ω) (ha j)) hkN
  calc
    _ ≤ expect w (fun ω => ∑ k ∈ Finset.range N, b k ω * a k) := expect_mono hn hpoint
    _ = ∑ k ∈ Finset.range N, expect w (b k) * a k := by
      simp only [expect,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ ≤ ∑ k ∈ Finset.range N, (2:ℝ)^(k+1)*a k := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right (t.z520 used ht p hp w hw hn hf k) (ha k)
    _ = ∑ k ∈ Finset.range N,
        min ((2:ℝ)^(k+1)/4^K) ((2:ℝ)^(k+1)/4^k) := by
      apply Finset.sum_congr rfl
      intro k _
      dsimp [a]
      rw [mul_min_of_nonneg _ _ (by positivity)]
      simp only [mul_one_div]
    _ ≤ _ := z589 N K
end CriticalPercolation.z18
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set
open scoped Classical
namespace CriticalPercolation
open z8
namespace z2
variable {V E : Type*} [Fintype V] [Fintype E] (G : z2 V E)
omit [Fintype V] in
lemma z206 (p : ℝ) (hp : p≠0) (ω : Set E) (v : V) :
    G.clusterDiscrepancy p ω v = -(IncidenceSearch.tree G v).centeredSum p ω / p := by
  rw [IncidenceSearch.tree_centered,clusterDiscrepancy,← Finset.sum_neg_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  change (if e∈G.z9 (G.cluster ω v) then
      (if e∈ω then -(1-p)/p else 1) else 0) =
    -(if e∈G.z9 (G.cluster ω v) then (if e∈ω then 1-p else -p) else 0)/p
  by_cases he : e∈G.z9 (G.cluster ω v)
  · by_cases hω : e∈ω <;> simp [he,hω,hp]
  · simp [he]
lemma z445 (p : ℝ) (hp : p ∈ Set.Ioo 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b=1) (hn : ∀ e b, 0≤w e b)
    (hf : LazyDFS.Fresh w p ∅) (D : ℕ) (hDpos : 1≤D)
    (hD : ∀ v, (G.z9 {v}).toFinset.card ≤ D) (K : ℕ) (v : V) :
    expect w (fun ω => G.rootMass (cappedMass (4^K)) ω v * |G.clusterDiscrepancy p ω v|) ≤
      (D:ℝ)/p*(6/(2:ℝ)^K) := by
  let t := IncidenceSearch.tree G v
  have hwel : ∀ ω : Set E, G.rootMass (cappedMass (4^K)) ω v * |G.clusterDiscrepancy p ω v| ≤
      (D:ℝ)/p * (|t.centeredSum p ω| * min (1/(4:ℝ)^K) (1/(t.z13 ω : ℝ))) := by
    intro ω
    rw [G.z206 p hp.1.ne' ω v,abs_div,abs_neg,abs_of_pos hp.1]
    change G.rootMass (cappedMass (4^K)) ω v * (|t.centeredSum p ω|/p) ≤ _
    by_cases hT : t.z13 ω = 0
    · rw [t.z93 ω hT p]
      simp
    · have hTD : t.z13 ω ≤ D*G.z16 ω v := by
        rw [IncidenceSearch.tree_count]
        simpa only [z16,mul_comm] using G.incident_card_le (G.cluster ω v) D hD
      have hh := G.z350 (4^K) (t.z13 ω) D
        (by positivity) (Nat.pos_of_ne_zero hT) hDpos ω v hTD
      have hh' : G.rootMass (cappedMass (4^K)) ω v ≤ (D:ℝ)*
          min (1/(4:ℝ)^K) (1/(t.z13 ω : ℝ)) := by
        simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
      calc
        _ ≤ ((D:ℝ)*min (1/(4:ℝ)^K) (1/(t.z13 ω : ℝ))) *
            (|t.centeredSum p ω|/p) := mul_le_mul_of_nonneg_right hh'
              (div_nonneg (abs_nonneg _) hp.1.le)
        _ = _ := by ring
  calc
    _ ≤ expect w (fun ω => (D:ℝ)/p *
        (|t.centeredSum p ω| * min (1/(4:ℝ)^K) (1/(t.z13 ω : ℝ)))) := by
      exact expect_mono hn (fun ω => hwel ω)
    _ = (D:ℝ)/p * expect w (fun ω =>
        |t.centeredSum p ω| * min (1/(4:ℝ)^K) (1/(t.z13 ω : ℝ))) := z25 _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (t.z347 ∅ (IncidenceSearch.tree_valid G v) p
        ⟨hp.1.le,hp.2.le⟩ w hw hn hf K) (div_nonneg (Nat.cast_nonneg D) hp.1.le)
theorem z371 (p : ℝ) (hp : p ∈ Set.Ioo 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b=1) (hn : ∀ e b, 0≤w e b)
    (h0 : ∀ e, w e False=1-p) (h1 : ∀ e, w e True=p)
    (D : ℕ) (hDpos : 1≤D) (hD : ∀ v, (G.z9 {v}).toFinset.card ≤ D)
    (x y : E → V) (he : ∀ e, G.ends e = s(x e,y e)) (K : ℕ) :
    (∑ e, prob w (BinaryLaw.endpointEvent G (x e) (y e) (4^K))) ≤
      (Fintype.card V : ℝ)*((D:ℝ)/p*(6/(2:ℝ)^K)) := by
  have hf : LazyDFS.Fresh w p ∅ := fun e _ => ⟨h0 e,h1 e⟩
  calc
    _ ≤ ∑ e, expect w (fun ω => G.edgeDiscrepancy (cappedMass (4^K)) p ω e) := by
      apply Finset.sum_le_sum
      intro e _
      exact G.z261 p hp w hw hn e (x e) (y e) (he e)
        (h0 e) (h1 e) (4^K) (by positivity)
    _ = expect w (fun ω => ∑ v, G.rootMass (cappedMass (4^K)) ω v * G.clusterDiscrepancy p ω v) := by
      erw [← expect_sum]
      congr 1
      funext ω
      exact G.z538 _ p ω
    _ ≤ expect w (fun ω => ∑ v, G.rootMass (cappedMass (4^K)) ω v * |G.clusterDiscrepancy p ω v|) := by
      apply expect_mono hn
      intro ω
      apply Finset.sum_le_sum
      intro v _
      apply mul_le_mul_of_nonneg_left (le_abs_self _)
      exact div_nonneg (z569 _ _) (Nat.cast_nonneg _)
    _ = ∑ v, expect w (fun ω => G.rootMass (cappedMass (4^K)) ω v * |G.clusterDiscrepancy p ω v|) := by
      erw [expect_sum]
    _ ≤ ∑ _v : V, (D:ℝ)/p*(6/(2:ℝ)^K) := by
      exact Finset.sum_le_sum (fun v _ => G.z445 p hp w hw hn hf D hDpos hD K v)
    _ = _ := by simp
end z2
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
namespace CriticalPercolation
lemma z365 {α β : Type*} (f : α → β) (hf : Function.Injective f)
    (S : Set α) (n : ℕ) :
    (∃ K : Set β, K.Finite ∧ K ⊆ f '' S ∧ n≤K.ncard) ↔
      ∃ K : Set α, K.Finite ∧ K ⊆ S ∧ n≤K.ncard := by
  constructor
  · rintro ⟨K,hK,hKS,hn⟩
    refine ⟨f ⁻¹' K,hK.preimage hf.injOn,?_,?_⟩
    · intro a ha
      obtain ⟨b,hb,heq⟩ := hKS ha
      exact hf heq ▸ hb
    · rwa [Set.ncard_preimage_of_injective_subset_range hf
        (hKS.trans (Set.image_subset_range _ _))]
  · rintro ⟨K,hK,hKS,hn⟩
    exact ⟨f '' K,hK.image f,Set.image_mono hKS,
      (Set.ncard_image_of_injective K hf) ▸ hn⟩
namespace z2
variable {V E : Type*} (G : z2 V E)
lemma z360 (S : Set V) (ω : Set (G.z4 S)) (u : S) (n : ℕ) :
    ω ∈ (G.induce S).z17 u n ↔
      Subtype.val '' ω ∈ G.z17 u.val n := by
  change _ ↔ ∃ K : Set V, K.Finite ∧ K ⊆ G.cluster (Subtype.val '' ω) u.val ∧ n≤K.ncard
  rw [← G.z282]
  exact (z365 Subtype.val Subtype.val_injective _ n).symm
lemma z441 (S : Set V) (ω : Set (G.z4 S)) (u v : S) (n : ℕ) :
    ω ∈ (G.induce S).z15 u v n ↔
      Subtype.val '' ω ∈ G.z15 u.val v.val n := by
  simp only [z15,Set.mem_inter_iff,Set.mem_ofPred_eq,
    G.z148,G.z360]
lemma z440 (S : Set V) (hS : (G.z4 S).Finite)
    (p : unitInterval) (A : Set (Set E)) :
    ((G.induce S).law p).real {ω | Subtype.val '' ω ∈ A} =
      (G.law p).real {ω | G.z4 S ∩ ω ∈ A} := by
  simpa only [law,← z0.law_const] using
    (z0.z398 p (G.z4 S) hS A).symm
lemma z452 (S : Set V) (hS : (G.z4 S).Finite)
    (p : unitInterval) (u v : S) (n : ℕ) :
    ((G.induce S).law p).real ((G.induce S).z15 u v n) =
      (G.law p).real {ω | G.z4 S ∩ ω ∈ G.z15 u.val v.val n} := by
  have he : (G.induce S).z15 u v n =
      {ω | Subtype.val '' ω ∈ G.z15 u.val v.val n} := by
    ext ω
    exact G.z441 S ω u v n
  rw [he,G.z440 S hS]
end z2
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
lemma z185 [Fintype V] [Fintype E]
    (p : unitInterval) (hp : (p : ℝ) ∈ Set.Ioo 0 1)
    (D : ℕ) (hDpos : 1≤D) (hD : ∀ v, (G.z9 {v}).ncard ≤ D)
    (x y : E → V) (he : ∀ e, G.ends e = s(x e,y e)) (K : ℕ) :
    (∑ e, (G.law p).real (G.z15 (x e) (y e) (4^K))) ≤
      (Fintype.card V : ℝ)*((D:ℝ)/(p:ℝ)*(6/(2:ℝ)^K)) := by
  have h := G.z371 p hp (fun _ : E => z0.z28 p)
    (fun _ => z0.bitWeight_sum p) (fun _ => z0.z143 p)
    (fun _ => by simp [z0.z28])
    (fun _ => by simp [z0.z28]) D hDpos
    (fun v => by simpa only [← Set.ncard_eq_toFinset_card'] using hD v) x y he K
  simpa only [G.z507] using h
lemma z283 (S : Set V) (v : S) :
    Subtype.val '' ((G.induce S).z9 {v}) ⊆ G.z9 {v.val} := by
  rintro e ⟨a,ha,rfl⟩
  simp only [z9,Set.mem_ofPred_eq,Set.mem_singleton_iff,exists_eq_left] at ha ⊢
  rw [← G.z107 S a]
  exact Sym2.mem_map.mpr ⟨v,ha,rfl⟩
lemma z226 (hlocal : G.LocallyFinite) (D : ℕ)
    (hD : ∀ v, (G.z9 {v}).ncard ≤ D) (S : Set V) (v : S) :
    ((G.induce S).z9 {v}).ncard ≤ D := by
  calc
    _ = (Subtype.val '' ((G.induce S).z9 {v})).ncard :=
      (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (G.z9 {v.val}).ncard := Set.ncard_le_ncard
      (G.z283 S v) (G.z323 hlocal (Set.finite_singleton _))
    _ ≤ D := hD v.val
lemma z356 (hlocal : G.LocallyFinite)
    (p : unitInterval) (hp : (p : ℝ) ∈ Set.Ioo 0 1)
    (D : ℕ) (hDpos : 1≤D) (hD : ∀ v, (G.z9 {v}).ncard ≤ D)
    (S : Set V) (hS : S.Finite) (K : ℕ) :
    ∑ e ∈ (G.z27 hlocal hS).toFinset,
      (G.law p).real {ω | G.z4 S ∩ ω ∈
        G.z15 (G.ends e).out.1 (G.ends e).out.2 (4^K)} ≤
      (S.ncard : ℝ)*((D:ℝ)/(p:ℝ)*(6/(2:ℝ)^K)) := by
  let := hS.fintype
  let := (G.z27 hlocal hS).fintype
  let x (e : G.z4 S) : S := ⟨(G.ends e.val).out.1,e.property _ (Sym2.out_fst_mem _)⟩
  let y (e : G.z4 S) : S := ⟨(G.ends e.val).out.2,e.property _ (Sym2.out_snd_mem _)⟩
  have he (e : G.z4 S) : (G.induce S).ends e = s(x e,y e) := by
    apply (G.induce_ends_eq S e (x e) (y e)).mpr
    exact (G.ends e.val).out_eq.symm
  have hh := (G.induce S).z185 p hp D hDpos
    (G.z226 hlocal D hD S) x y he K
  simp_rw [G.z452 S (G.z27 hlocal hS)] at hh
  rw [Finset.sum_subtype (G.z27 hlocal hS).toFinset
    (fun e => (G.z27 hlocal hS).mem_toFinset)]
  simpa only [x,y,Set.ncard_eq_toFinset_card',Set.toFinset_card] using hh
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
namespace CriticalPercolation.z2
variable {V E : Type*} [Countable V] [Countable E] (G : z2 V E)
lemma z339 (hconnected : G.z7.Connected)
    (hlocal : G.LocallyFinite) (hg : G.SubexponentialGrowth)
    (C M D : ℕ) (hM : ∀ v, (G.z5 v C).ncard≤M)
    (hDpos : 1≤D) (hD : ∀ v, (G.z9 {v}).ncard≤D)
    (hdense : ∀ u v, ∃ φ : G.Aut, φ.vertex u ∈ G.z5 v C)
    (p : unitInterval) (hp : (p:ℝ)∈Set.Ioo 0 1) (e : E) (K : ℕ) :
    (G.law p).real (G.z15 (G.ends e).out.1 (G.ends e).out.2 (4^K)) ≤
      8*(M:ℝ)*((D:ℝ)/(p:ℝ)*(6/(2:ℝ)^K)) := by
  let a := (G.ends e).out.1
  let b := (G.ends e).out.2
  let δ := (G.law p).real (G.z15 a b (4^K))
  let Q := (D:ℝ)/(p:ℝ)*(6/(2:ℝ)^K)
  have hQ : 0≤Q := by
    dsimp [Q]
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) hp.1.le) (by positivity)
  change δ ≤ 8*(M:ℝ)*Q
  by_cases hδ : 0<δ
  swap
  · exact (not_lt.mp hδ).trans (by positivity)
  obtain ⟨J,hJ,hJmass⟩ := G.z166 p a b (4^K) hδ
  obtain ⟨W,hW⟩ := G.z286 hconnected a (hJ.insert e)
  have hJW : J⊆G.z4 (G.z5 a W) := fun f hf => hW (Or.inr hf)
  have heW : e∈G.z4 (G.z5 a W) := hW (Or.inl rfl)
  choose φ hφ using hdense a
  obtain ⟨n,_,hn⟩ := G.z202 hlocal hg a (C+W) 0
  let B := G.z5 a n
  let S := G.z5 a (n+C+W)
  have hBf : B.Finite := G.z19 hlocal a n
  have hSf : S.Finite := G.z19 hlocal a _
  have hEf := G.z27 hlocal hSf
  let q (f : E) := (G.law p).real {ω | G.z4 S∩ω ∈
    G.z15 (G.ends f).out.1 (G.ends f).out.2 (4^K)}
  have hq : ∀ f, 0≤q f := fun _ => measureReal_nonneg
  have hmap : ∀ v∈hBf.toFinset, (φ v).edge e∈hEf.toFinset := by
    intro v hv
    apply hEf.mem_toFinset.mpr
    exact G.z139 a a v n C W (φ v) (hBf.mem_toFinset.mp hv)
      (hφ v) (Set.singleton_subset_iff.mpr heW) ⟨e,rfl,rfl⟩
  have hvbound : ∀ v∈hBf.toFinset, δ/2≤q ((φ v).edge e) := by
    intro v hv
    have hsub := G.z139 a a v n C W (φ v)
      (hBf.mem_toFinset.mp hv) (hφ v) hJW
    have hm := measureReal_mono (G.z133 hsub
      ((φ v).vertex a) ((φ v).vertex b) (4^K)) (μ := G.law p)
    rw [Aut.z379 G (φ v) p J hJ a b (4^K)] at hm
    have hend : s((φ v).vertex a,(φ v).vertex b) =
        s((G.ends ((φ v).edge e)).out.1,(G.ends ((φ v).edge e)).out.2) := by
      calc
        _ = G.ends ((φ v).edge e) := by
          rw [(φ v).preserves,(G.ends e).out_eq.symm,Sym2.map_mk]
        _ = _ := (G.ends ((φ v).edge e)).out_eq.symm
    rw [G.z254 hend (4^K)] at hm
    exact hJmass.trans hm
  have hfib := G.z455 hlocal C M hM a e (Sym2.out_fst_mem _)
    φ hφ hBf.toFinset
  have havg := G.z356 hlocal p hp D hDpos hD S hSf K
  change (∑ f∈hEf.toFinset, q f) ≤ (S.ncard:ℝ)*Q at havg
  have hratio : S.ncard≤2*B.ncard := by simpa only [S,B,Nat.add_assoc] using hn
  have hsum : (B.ncard:ℝ)*(δ/2) ≤ (B.ncard:ℝ)*(4*(M:ℝ)*Q) := by
    calc
      _ = ∑ v∈hBf.toFinset, δ/2 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [Set.ncard_eq_toFinset_card B hBf]
      _ ≤ ∑ v∈hBf.toFinset, q ((φ v).edge e) := Finset.sum_le_sum hvbound
      _ ≤ (2*M:ℕ)*∑ f∈hEf.toFinset, q f :=
        z403 hBf.toFinset hEf.toFinset (fun v => (φ v).edge e) q
          (2*M) hq hmap hfib
      _ ≤ (2*M:ℕ)*((S.ncard:ℝ)*Q) :=
        mul_le_mul_of_nonneg_left havg (Nat.cast_nonneg _)
      _ ≤ (2*M:ℕ)*(((2*B.ncard:ℕ):ℝ)*Q) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hratio) hQ) (Nat.cast_nonneg _)
      _ = _ := by push_cast; ring
  have hBpos : (0:ℝ)<B.ncard := Nat.cast_pos.mpr (G.z288 hlocal a n)
  have hh := (mul_le_mul_iff_right₀ hBpos).mp hsum
  linarith
theorem z232 (hconnected : G.z7.Connected)
    (hlocal : G.LocallyFinite) (hquasi : G.QuasiTransitive)
    (hg : G.SubexponentialGrowth) :
    ∃ A : ℝ, 0<A ∧ ∀ (p : unitInterval), (p:ℝ)∈Set.Ioo 0 1 → ∀ (e : E) (K : ℕ),
      (G.law p).real (G.z15 (G.ends e).out.1 (G.ends e).out.2 (4^K)) ≤
        A/((p:ℝ)*(2:ℝ)^K) := by
  obtain ⟨C,hC⟩ := G.z255 hconnected hquasi
  obtain ⟨M,hMpos,hM⟩ := G.z289 hquasi C
  obtain ⟨D,hDpos,hD⟩ := G.z190 hquasi
  have hm : (0:ℝ)<M := by exact_mod_cast hMpos
  have hd : (0:ℝ)<D := by exact_mod_cast hDpos
  refine ⟨48*(M:ℝ)*D, by positivity, ?_⟩
  intro p hp e K
  have hh := G.z339 hconnected hlocal hg C M D hM hDpos hD hC p hp e K
  convert hh using 1
  ring
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
def distinctInfiniteEvent (x y : V) : Set (Set E) :=
  {ω | (G.cluster ω x).Infinite ∧ (G.cluster ω y).Infinite ∧
    ¬ (G.z1 ω).Reachable x y}
lemma z132 [Countable V] [Countable E] (x y : V) :
    MeasurableSet (G.distinctInfiniteEvent x y) :=
  ((G.z39 x).and
    ((G.z39 y).and (G.z79 x y).not)).setOf
lemma z80 (x y : V) (s : ℕ) :
    G.distinctInfiniteEvent x y ⊆ G.z15 x y s := by
  rintro ω ⟨hx,hy,hxy⟩
  exact ⟨⟨hxy,G.z29 x s hx⟩,
    G.z29 y s hy⟩
lemma z237 (ω : Set E) (e : E) (o : V)
    (hends : ∀ v ∈ G.ends e, v ∉ G.cluster ω o) :
    G.cluster (insert e ω) o = G.cluster ω o := by
  apply Set.Subset.antisymm
  · intro y hy
    have hr := ((G.z1 (insert e ω)).reachable_iff_reflTransGen o y).mp hy
    clear hy
    induction hr with
    | refl => exact .refl _
    | @tail x y hr hxy ih =>
      obtain ⟨⟨f,hf,hfe⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
      rcases hf with rfl | hf
      · exact False.elim (hends x (by simp [hfe]) ih)
      · have hadj : (G.z1 ω).Adj x y :=
          (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨f,hf,hfe⟩,hne⟩
        exact ih.trans hadj.reachable
  · exact G.cluster_mono (Set.subset_insert e ω) o
lemma z105 (n : ℕ) :
    ∀ (ω : Set E) (x y : V), lengthReach G.z7 n x y →
      ω ∈ G.distinctInfiniteEvent x y →
      ∃ S : Set E, S.Finite ∧ ∃ a b : V, G.z7.Adj a b ∧
        S ∪ ω ∈ G.distinctInfiniteEvent a b := by
  induction n with
  | zero =>
    intro ω x y hxy h
    exact False.elim (h.2.2 (hxy ▸ SimpleGraph.Reachable.refl x))
  | succ n ih =>
    rintro ω x y ⟨u,hxu,huy⟩ ⟨hx,hy,hxy⟩
    by_cases hxuω : (G.z1 ω).Reachable x u
    · refine ⟨∅,Set.finite_empty,u,y,huy,?_⟩
      rw [Set.empty_union]
      refine ⟨?_,hy,fun huy => hxy (hxuω.trans huy)⟩
      rwa [← G.z40 hxuω]
    · obtain ⟨⟨e,_,he⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp huy
      have hends : ∀ v ∈ G.ends e, v ∉ G.cluster ω x := by
        intro v hv
        rw [he,Sym2.mem_iff] at hv
        rcases hv with rfl | rfl
        · exact hxuω
        · exact hxy
      have hc := G.z237 ω e x hends
      have hnewx : (G.cluster (insert e ω) x).Infinite := hc ▸ hx
      have hay : (G.z1 (insert e ω)).Adj u y :=
        (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,Set.mem_insert e ω,he⟩,hne⟩
      have hnewu : (G.cluster (insert e ω) u).Infinite := by
        have hh := hy.mono (G.cluster_mono (Set.subset_insert e ω) y)
        rwa [← G.z40 hay.reachable] at hh
      have hnot : ¬ (G.z1 (insert e ω)).Reachable x u := by
        change u ∉ G.cluster (insert e ω) x
        rwa [hc]
      obtain ⟨S,hS,a,b,hab,hhab⟩ := ih (insert e ω) x u hxu ⟨hnewx,hnewu,hnot⟩
      refine ⟨insert e S,hS.insert e,a,b,hab,?_⟩
      simpa only [Set.insert_union,Set.union_insert] using hhab
lemma z192 (hconnected : G.z7.Connected)
    (ω : Set E) (x y : V) (h : ω ∈ G.distinctInfiniteEvent x y) :
    ∃ S : Set E, S.Finite ∧ ∃ a b : V, G.z7.Adj a b ∧
      S ∪ ω ∈ G.distinctInfiniteEvent a b := by
  obtain ⟨n,hn⟩ := (z72 G.z7 x y).mp (hconnected x y)
  exact G.z105 n ω x y hn h
theorem z210 [Countable V] [Countable E]
    (hconnected : G.z7.Connected) (hlocal : G.LocallyFinite)
    (hquasi : G.QuasiTransitive) (hg : G.SubexponentialGrowth)
    (p : unitInterval) (hp : (p:ℝ) ∈ Set.Ioo 0 1) (x y : V)
    (hxy : G.z7.Adj x y) : G.law p (G.distinctInfiniteEvent x y) = 0 := by
  obtain ⟨A,_,hA⟩ := G.z232 hconnected hlocal hquasi hg
  obtain ⟨⟨e,_,he⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
  have hbound : ∀ K : ℕ, (G.law p).real (G.distinctInfiniteEvent x y) ≤
      A/((p:ℝ)*(2:ℝ)^K) := by
    intro K
    have hsub := measureReal_mono (G.z80 x y (4^K))
      (μ := G.law p)
    have heq : s(x,y) = s((G.ends e).out.1,(G.ends e).out.2) := by
      exact he.symm.trans (G.ends e).out_eq.symm
    rw [G.z254 heq (4^K)] at hsub
    exact hsub.trans (hA p hp e K)
  have ht : Tendsto (fun K : ℕ => A/((p:ℝ)*(2:ℝ)^K)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).const_mul_atTop hp.1)
  have hz : (G.law p).real (G.distinctInfiniteEvent x y) = 0 :=
    le_antisymm (ge_of_tendsto ht (Eventually.of_forall hbound)) measureReal_nonneg
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mp hz
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical
namespace CriticalPercolation.z2
variable {V E : Type*} [Countable V] [Countable E] (G : z2 V E)
def atMostOneInfinite : Set (Set E) :=
  {ω | ∀ x y, (G.cluster ω x).Infinite → (G.cluster ω y).Infinite →
    (G.z1 ω).Reachable x y}
theorem z497 (hconnected : G.z7.Connected)
    (hlocal : G.LocallyFinite) (hquasi : G.QuasiTransitive)
    (hg : G.SubexponentialGrowth) (p : unitInterval)
    (hp : (p:ℝ) ∈ Set.Ioo 0 1) : ∀ᵐ ω ∂G.law p, ω ∈ G.atMostOneInfinite := by
  have hn : ∀ (S : Finset E) (x y : V), ∀ᵐ ω ∂G.law p,
      G.z7.Adj x y → (S : Set E) ∪ ω ∉ G.distinctInfiniteEvent x y := by
    intro S x y
    by_cases hxy : G.z7.Adj x y
    · have hz := z0.z322 (fun _ : E => p)
        (fun _ => hp.1) (S : Set E) S.finite_toSet (G.distinctInfiniteEvent x y)
        (G.z132 x y)
        (by rw [z0.law_const];
            exact G.z210 hconnected hlocal hquasi hg p hp x y hxy)
      rw [z0.law_const] at hz
      have hh : ∀ᵐ ω ∂G.law p, (S : Set E) ∪ ω ∉ G.distinctInfiniteEvent x y := by
        rw [ae_iff]
        simp only [not_not]
        exact hz
      exact hh.mono (fun _ h _ => h)
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hxy h))
  have hall := ae_all_iff.mpr (fun S => ae_all_iff.mpr (fun x => ae_all_iff.mpr (hn S x)))
  filter_upwards [hall] with ω hω
  intro x y hx hy
  by_contra hxy
  obtain ⟨S,hS,a,b,hab,hh⟩ := G.z192 hconnected ω x y ⟨hx,hy,hxy⟩
  have hnot := hω hS.toFinset a b hab
  exact hnot (by simpa only [Set.Finite.coe_toFinset] using hh)
end CriticalPercolation.z2
end
end
end
end OAI
end
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
open Filter Topology
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
lemma z82 (o : V) (K : Set V) (hK : K.Finite) :
    G.z14 o ⊆ G.hitEvent o Kᶜ := by
  intro ω hω
  exact (hω.sdiff hK).nonempty
lemma z163
    (K : Set.FiniteExhaustion (Set.univ : Set V)) (o : V) :
    G.z14 o = ⋂ n, G.hitEvent o (K n)ᶜ := by
  ext ω
  constructor
  · intro hω
    exact Set.mem_iInter.mpr fun n => G.z82 o (K n) (K.finite n) hω
  · intro hω
    change (G.cluster ω o).Infinite
    intro hfin
    obtain ⟨n, hn⟩ := z78 K hfin (Set.subset_univ _)
    obtain ⟨v, hv, hvK⟩ := Set.mem_iInter.mp hω n
    exact hvK (hn hv)
lemma z436 [Countable V] [Countable E]
    (p : unitInterval) (K : Set.FiniteExhaustion (Set.univ : Set V)) (o : V) :
    Tendsto (fun n => (G.law p).real (G.hitEvent o (K n)ᶜ)) atTop
      (𝓝 ((G.law p).real (G.z14 o))) := by
  have h := tendsto_measure_iInter_atTop (μ := G.law p)
    (fun n => (G.z194 o (K n)ᶜ).nullMeasurableSet)
    (show Antitone (fun n => G.hitEvent o (K n)ᶜ) from
      fun _ _ h => G.z266 o (Set.compl_subset_compl.mpr (K.mono h)))
    ⟨0, measure_ne_top _ _⟩
  rw [← G.z163 K o] at h
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
lemma z433 (hconnected : G.z7.Connected)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (o v : V) :
    0 < (G.law p).real (G.hitEvent o {v}) := by
  obtain ⟨s, hs, _, hsv⟩ := G.z43 (hconnected o v)
  have hsub : {ω : Set E | s ⊆ ω} ⊆ G.hitEvent o {v} := by
    intro ω hω
    exact ⟨v, G.cluster_mono hω o hsv, rfl⟩
  have hpos : 0 < (G.law p).real {ω : Set E | s ⊆ ω} := by
    rw [law, ← z0.law_const (E := E) p]
    rw [z0.z611 p s hs]
    exact pow_pos hp _
  exact lt_of_lt_of_le hpos (measureReal_mono hsub)
lemma z304 [Countable V] [Countable E]
    (p : unitInterval) (o v : V) :
    (G.law p).real (G.hitEvent o {v}) * (G.law p).real (G.z14 v) ≤
      (G.law p).real (G.z14 o) := by
  let K := (Set.to_countable (Set.univ : Set V)).finiteExhaustion
  have hn (n : ℕ) :
      (G.law p).real (G.hitEvent o {v}) * (G.law p).real (G.z14 v) ≤
        (G.law p).real (G.hitEvent o (K n)ᶜ) := by
    apply le_trans (G.joint_gluing p o {v} (K n)ᶜ
      ((G.law p).real (G.z14 v)) ?_)
      (measureReal_mono Set.inter_subset_right)
    intro w hw
    rcases Set.mem_singleton_iff.mp hw with rfl
    exact measureReal_mono (G.z82 w (K n) (K.finite n))
  exact ge_of_tendsto (G.z436 p K o) (Eventually.of_forall hn)
lemma z316 [Countable V] [Countable E]
    (hconnected : G.z7.Connected) (p : unitInterval) (hp : 0 < (p : ℝ))
    {v : V} (hv : 0 < (G.law p).real (G.z14 v)) (o : V) :
    0 < (G.law p).real (G.z14 o) :=
  lt_of_lt_of_le (mul_pos (G.z433 hconnected p hp o v) hv)
    (G.z304 p o v)
theorem z336
    (hconnected : G.z7.Connected) (hlocal : G.LocallyFinite)
    (hquasi : G.QuasiTransitive) (p : unitInterval)
    (hp : 0 < G.law p G.z12) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ o : V, θ ≤ (G.law p).real (G.z14 o) := by
  let := G.z53 hconnected hlocal
  let := G.z113 hconnected hlocal
  have hp0 : 0 < (p : ℝ) := by
    by_contra h
    have hz : p = 0 := Subtype.ext (le_antisymm (not_lt.mp h) p.property.1)
    subst p
    rw [G.z527] at hp
    exact (lt_irrefl _ hp)
  have hn : ¬ ∀ v, G.law p (G.z14 v) = 0 := by
    intro h
    exact (ne_of_gt hp) ((G.z157 _).mpr h)
  push Not at hn
  obtain ⟨v, hv⟩ := hn
  have hvpos : 0 < (G.law p).real (G.z14 v) :=
    ENNReal.toReal_pos hv (measure_ne_top _ _)
  have hall := G.z316 hconnected p hp0 hvpos
  obtain ⟨S, hS, horbit⟩ := hquasi
  have hSne : S.Nonempty := by
    obtain ⟨s, hs, _⟩ := horbit v
    exact ⟨s, hs⟩
  obtain ⟨s, hs, hmin⟩ := Set.exists_min_image S
    (fun o => (G.law p).real (G.z14 o)) hS hSne
  refine ⟨(G.law p).real (G.z14 s), hall s, ?_⟩
  intro o
  obtain ⟨t, ht, φ, rfl⟩ := horbit o
  rw [Aut.z543]
  exact hmin t ht
end CriticalPercolation.z2
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology Classical
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
def infiniteVertices (ω : Set E) : Set V := {v | (G.cluster ω v).Infinite}
lemma z468 {ω τ : Set E} (h : ω⊆τ) :
    G.infiniteVertices ω⊆G.infiniteVertices τ := fun v hv => hv.mono (G.cluster_mono h v)
lemma z413 (ω S : Set E) (o : V)
    (hends : ∀ e∈S, ∀ v∈G.ends e, v∉G.cluster ω o) :
    G.cluster (ω∪S) o=G.cluster ω o := by
  apply Set.Subset.antisymm
  · intro z hz
    have hr := ((G.z1 (ω∪S)).reachable_iff_reflTransGen o z).mp hz
    clear hz
    induction hr with
    | refl => exact .refl _
    | @tail x y hr hxy ih =>
      obtain ⟨⟨e,he,hend⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
      rcases he with he|he
      · have hadj : (G.z1 ω).Adj x y :=
          (SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,he,hend⟩,hne⟩
        exact ih.trans hadj.reachable
      · exact False.elim (hends e he x (by simp [hend]) ih)
  · exact G.cluster_mono Set.subset_union_left o
lemma z135 (ω S : Set E) (hS : S.Finite) :
    (G.infiniteVertices (ω∪S)\G.infiniteVertices ω).Finite := by
  let K := ⋃ e∈S, ⋃ v∈(G.ends e).toFinset,
    {x | x∈G.cluster ω v ∧ (G.cluster ω v).Finite}
  have hK : K.Finite := hS.biUnion fun e _ => (G.ends e).toFinset.finite_toSet.biUnion fun v _ => by
    by_cases hv : (G.cluster ω v).Finite
    · exact hv.subset (fun _ h => h.1)
    · have heq : {x | x∈G.cluster ω v ∧ (G.cluster ω v).Finite}=(∅ : Set V) := by
        ext x
        simp [hv]
      rw [heq]
      exact Set.finite_empty
  apply hK.subset
  intro x hx
  have hfin : (G.cluster ω x).Finite := Set.not_infinite.mp hx.2
  by_contra hn
  have hends : ∀ e∈S, ∀ v∈G.ends e, v∉G.cluster ω x := by
    intro e he v hv hvc
    apply hn
    refine Set.mem_iUnion₂.mpr ⟨e,he,Set.mem_iUnion₂.mpr ⟨v,?_,hvc.symm,?_⟩⟩
    · simpa only [Sym2.mem_toFinset] using hv
    · rwa [← G.z40 hvc]
  exact hx.1 (by rwa [G.z413 ω S x hends])
def directionUnbounded (f : V → ℝ) : Set (Set E) :=
  {ω | ∀ n : ℕ, ∃ v, (n : ℝ)<f v ∧ v∈G.infiniteVertices ω}
lemma z85 (f : V → ℝ) : IsUpperSet (G.directionUnbounded f) := by
  intro ω τ h hω n
  obtain ⟨v,hv,hv'⟩ := hω n
  exact ⟨v,hv,G.z468 h hv'⟩
lemma z138 (f : V → ℝ) (ω S : Set E) (hS : S.Finite) :
    ω∪S∈G.directionUnbounded f ↔ ω∈G.directionUnbounded f := by
  constructor
  · intro h n
    have hK := (G.z135 ω S hS).image f
    obtain ⟨M,hM⟩ := hK.bddAbove
    obtain ⟨N,hN⟩ := exists_nat_gt (max M n)
    obtain ⟨v,hv,hinf⟩ := h N
    refine ⟨v,lt_trans (lt_of_le_of_lt (le_max_right M n) hN) hv,?_⟩
    by_contra hnot
    have hfM := hM (Set.mem_image_of_mem f ⟨hinf,hnot⟩)
    have : M<(N : ℝ) := lt_of_le_of_lt (le_max_left M n) hN
    linarith
  · exact G.z85 f Set.subset_union_left
lemma z153 (f : V → ℝ) (ω S : Set E) (hS : S.Finite) :
    ω\S∈G.directionUnbounded f ↔ ω∈G.directionUnbounded f := by
  constructor
  · exact G.z85 f Set.sdiff_subset
  · intro h
    have hs : ω⊆(ω\S)∪S := fun e he => by
      by_cases hh : e∈S
      · exact Or.inr hh
      · exact Or.inl ⟨he,hh⟩
    exact (G.z138 f (ω\S) S hS).mp
      (G.z85 f hs h)
lemma z88 [Countable V] [Countable E] (f : V → ℝ) :
    MeasurableSet (G.directionUnbounded f) := by
  have heq : G.directionUnbounded f=⋂ n : ℕ, ⋃ v∈{v | (n : ℝ)<f v}, G.z14 v := by
    ext ω
    simp only [directionUnbounded,infiniteVertices,z14,Set.mem_ofPred_eq,
      Set.mem_iInter,Set.mem_iUnion,exists_prop]
  rw [heq]
  exact MeasurableSet.iInter fun n => MeasurableSet.biUnion (Set.to_countable _) fun v _ =>
    G.z60 v
lemma z303 [Countable V] [Countable E]
    (q : E → unitInterval) (f : V → ℝ) :
    z0.law q (G.directionUnbounded f)=0 ∨
      z0.law q (G.directionUnbounded f)=1 := by
  apply z0.z34 q _ (G.z88 f)
  intro S hS ω
  have heq : z0.forceOn S ∅ ω=ω\S := by
    ext e
    change (if e∈S then False else e∈ω) ↔ e∈ω ∧ e∉S
    split_ifs <;> tauto
  rw [heq]
  exact G.z153 f ω S hS
lemma z298 [Countable V] [Countable E]
    (p : unitInterval) (f : V → ℝ) (hf : ∀ n : ℕ, ∃ v, (n : ℝ)<f v)
    (theta : ℝ) (htheta : 0<theta)
    (hroot : ∀ v, theta≤(G.law p).real (G.z14 v)) :
    0<G.law p (G.directionUnbounded f) := by
  let A := fun n : ℕ => ⋃ v∈{v | (n : ℝ)<f v}, G.z14 v
  have hA : ∀ n, MeasurableSet (A n) := fun n =>
    MeasurableSet.biUnion (Set.to_countable _) fun v _ => G.z60 v
  have hanti : Antitone A := by
    intro n m hnm ω hω
    obtain ⟨v,hv,hh⟩ := Set.mem_iUnion₂.mp hω
    exact Set.mem_iUnion₂.mpr ⟨v,(show (n : ℝ)<f v from lt_of_le_of_lt (Nat.cast_le.mpr hnm) hv),hh⟩
  have heq : (⋂ n, A n)=G.directionUnbounded f := by
    ext ω
    simp only [A,directionUnbounded,infiniteVertices,z14,Set.mem_ofPred_eq,
      Set.mem_iInter,Set.mem_iUnion,exists_prop]
  have ht := tendsto_measure_iInter_atTop (μ := G.law p)
    (fun n => (hA n).nullMeasurableSet) hanti ⟨0,measure_ne_top _ _⟩
  rw [heq] at ht
  have hreal := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp ht
  have hbound : ∀ n, theta≤(G.law p).real (A n) := by
    intro n
    obtain ⟨v,hv⟩ := hf n
    have hs : G.z14 v⊆A n := fun ω hω => Set.mem_iUnion₂.mpr ⟨v,hv,hω⟩
    exact (hroot v).trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hs))
  have hp : 0<(G.law p).real (G.directionUnbounded f) :=
    htheta.trans_le (ge_of_tendsto hreal (Eventually.of_forall hbound))
  exact ENNReal.toReal_pos_iff.mp hp |>.1
theorem z435 [Countable V] [Countable E]
    (hc : G.z7.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (hpositive : 0<G.law p G.z12)
    (f : V → ℝ) (hf : ∀ n : ℕ, ∃ v, (n : ℝ)<f v) :
    G.law p (G.directionUnbounded f)=1 := by
  obtain ⟨theta,htheta,hroot⟩ := G.z336 hc hl hq p hpositive
  have hp := G.z298 p f hf theta htheta hroot
  have hz := G.z303 (fun _ => p) f
  rw [z0.law_const] at hz
  exact hz.resolve_left (ne_of_gt hp)
theorem z109 [Countable V] [Countable E]
    (hc : G.z7.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hg : G.SubexponentialGrowth) (p : unitInterval)
    (hp : (p : ℝ)∈Set.Ioo 0 1) (hpositive : 0<G.law p G.z12)
    (f : V → ℝ) (hf : ∀ n : ℕ, ∃ v, (n : ℝ)<f v) :
    ∀ᵐ ω ∂G.law p, ∀ v, (G.cluster ω v).Infinite →
      ∀ n : ℕ, ∃ w∈G.cluster ω v, (n : ℝ)<f w := by
  have hu : ∀ᵐ ω ∂G.law p, ω∈G.directionUnbounded f := by
    rw [ae_iff]
    change G.law p (G.directionUnbounded f)ᶜ=0
    rw [measure_compl (G.z88 f) (measure_ne_top _ _),
      G.z435 hc hl hq p hpositive f hf,measure_univ,tsub_self]
  filter_upwards [hu,G.z497 hc hl hq hg p hp] with ω hω huniq
  intro v hv n
  obtain ⟨w,hw,hwinf⟩ := hω n
  exact ⟨w,huniq v w hv hwinf,hw⟩
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set
open scoped Classical
namespace CriticalPercolation
open z8
namespace z2
variable {V E : Type*} (G : z2 V E)
def openIncident (ω : Set E) (v : V) : Set E :=
  G.z9 (G.cluster ω v) ∩ ω
lemma z235 (ω : Set E) (v : V) :
    G.cluster ω v ⊆ {v} ∪ ((fun e => (G.ends e).out.1) '' G.openIncident ω v ∪
      (fun e => (G.ends e).out.2) '' G.openIncident ω v) := by
  intro z hz
  change (G.z1 ω).Reachable v z at hz
  rw [SimpleGraph.reachable_iff_reflTransGen] at hz
  induction hz with
  | refl => exact Or.inl rfl
  | @tail u z hv hu _ =>
    obtain ⟨⟨e,he,heq⟩,_⟩ := hu
    have hzmem : z ∈ G.ends e := by rw [heq]; simp
    have heI : e ∈ G.openIncident ω v := by
      exact ⟨⟨u,(SimpleGraph.reachable_iff_reflTransGen _ _).mpr hv,
        by rw [heq]; simp⟩,he⟩
    have hout : G.ends e = s((G.ends e).out.1,(G.ends e).out.2) :=
      (G.ends e).out_eq.symm
    rw [hout,Sym2.mem_iff] at hzmem
    exact Or.inr (hzmem.elim (fun h => Or.inl ⟨e,heI,h.symm⟩)
      (fun h => Or.inr ⟨e,heI,h.symm⟩))
lemma z250 [Fintype V] [Fintype E] (ω : Set E) (v : V) :
    G.z16 ω v ≤ 1 + 2*(G.openIncident ω v).ncard := by
  calc
    _ ≤ ({v} ∪ ((fun e => (G.ends e).out.1) '' G.openIncident ω v ∪
      (fun e => (G.ends e).out.2) '' G.openIncident ω v)).ncard := by
      simpa only [z16,← Set.ncard_eq_toFinset_card'] using
        Set.ncard_le_ncard (G.z235 ω v)
    _ ≤ ({v} : Set V).ncard + (((fun e => (G.ends e).out.1) '' G.openIncident ω v).ncard +
      ((fun e => (G.ends e).out.2) '' G.openIncident ω v).ncard) :=
      (Set.ncard_union_le _ _).trans (Nat.add_le_add_left (Set.ncard_union_le _ _) _)
    _ ≤ _ := by
      have h1 := Set.ncard_image_le (s := G.openIncident ω v) (f := fun e => (G.ends e).out.1)
      have h2 := Set.ncard_image_le (s := G.openIncident ω v) (f := fun e => (G.ends e).out.2)
      simp only [Set.ncard_singleton]
      omega
lemma z331 [Fintype E] (p : ℝ) (ω : Set E) (v : V) :
    ((G.openIncident ω v).ncard : ℝ) = (IncidenceSearch.tree G v).centeredSum p ω +
      p*((IncidenceSearch.tree G v).z13 ω : ℝ) := by
  rw [IncidenceSearch.tree_centered,IncidenceSearch.tree_count]
  simp only [Set.ncard_eq_toFinset_card']
  have ha : ((G.openIncident ω v).toFinset.card : ℝ) =
      ∑ e : E, if e ∈ G.openIncident ω v then (1:ℝ) else 0 := by simp
  have hb : ((G.z9 (G.cluster ω v)).toFinset.card : ℝ) =
      ∑ e : E, if e ∈ G.z9 (G.cluster ω v) then (1:ℝ) else 0 := by simp
  rw [ha,hb,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hi : e∈G.z9 (G.cluster ω v) <;> by_cases ho : e∈ω <;>
    simp [openIncident,hi,ho]
lemma z299 [Fintype V] [Fintype E]
    (p : ℝ) (hp : p ∈ Set.Icc 0 1) (w : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b=1) (hn : ∀ e b, 0≤w e b)
    (h0 : ∀ e, w e False=1-p) (h1 : ∀ e, w e True=p)
    (D : ℕ) (hD : ∀ v, (G.z9 {v}).toFinset.card ≤ D)
    (hpD : 4*p*D ≤ 1) (v : V) :
    expect w (fun ω => (G.z16 {e | ω e} v : ℝ)) ≤ 2 := by
  let t := IncidenceSearch.tree G v
  let a := expect w (fun ω => (G.z16 {e | ω e} v : ℝ))
  have hmean := (t.z312 ∅ (IncidenceSearch.tree_valid G v) p w hw
    (fun e _ => ⟨h0 e,h1 e⟩)).1
  have hquery : expect w (fun ω => (t.z13 ω : ℝ)) ≤ D*a := by
    calc
      _ ≤ expect w (fun ω => (D:ℝ)*(G.z16 {e | ω e} v : ℝ)) := by
        apply expect_mono hn
        intro ω
        have hcount : t.z13 ω = (G.z9 (G.cluster {e | ω e} v)).toFinset.card :=
          IncidenceSearch.tree_count G v {e | ω e}
        rw [hcount]
        exact_mod_cast (by simpa only [z16,mul_comm] using
          G.incident_card_le (G.cluster {e | ω e} v) D hD)
      _ = _ := z25 _ _ _
  have hcluster : a ≤ 1+2*p*(D*a) := by
    calc
      _ ≤ expect w (fun ω => 1+2*((G.openIncident {e | ω e} v).ncard : ℝ)) := by
        apply expect_mono hn
        intro ω
        exact_mod_cast G.z250 {e | ω e} v
      _ = 1+2*p*expect w (fun ω => (t.z13 ω : ℝ)) := by
        have hopen (ω : E → Prop) : ((G.openIncident {e | ω e} v).ncard : ℝ) =
            t.centeredSum p ω + p*(t.z13 ω : ℝ) :=
          G.z331 p {e | ω e} v
        simp_rw [hopen]
        rw [expect_add,expect_const w hw,z25,expect_add,hmean,
          z25]
        ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hquery (mul_nonneg (by norm_num) hp.1 : 0≤2*p)
        linarith
  have ha : 0≤a := expect_nonneg hn (fun _ => Nat.cast_nonneg _)
  nlinarith
end z2
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
namespace CriticalPercolation.z2
open z8
variable {V E : Type*} (G : z2 V E)
lemma z179 [Fintype V] [Fintype E]
    (p : unitInterval) (D : ℕ) (hD : ∀ v, (G.z9 {v}).ncard≤D)
    (hpD : 4*(p:ℝ)*D≤1) (u : V) (s : ℕ) :
    (s:ℝ)*(G.law p).real (G.z17 u s) ≤ 2 := by
  let w := fun _ : E => z0.z28 p
  have hn : ∀ e b, 0≤w e b := fun _ => z0.z143 p
  have ht := G.z299 p p.property w
    (fun _ => z0.bitWeight_sum p) hn
    (fun _ => by simp [w,z0.z28])
    (fun _ => by simp [w,z0.z28]) D
    (fun v => by simpa only [← Set.ncard_eq_toFinset_card'] using hD v) hpD u
  have hprob : (G.law p).real (G.z17 u s) = prob w (fun ω => ω∈G.z17 u s) := by
    simpa only [law,← z0.law_const,w] using
      (z0.prob_eq_real (fun _ : E => p) (G.z17 u s)).symm
  rw [hprob,prob,← z25]
  refine le_trans (expect_mono hn ?_) ht
  intro ω
  change (s:ℝ)*(if {e | ω e}∈G.z17 u s then 1 else 0) ≤
    (G.z16 {e | ω e} u : ℝ)
  by_cases hh : {e | ω e} ∈ G.z17 u s
  · simp only [if_pos hh,mul_one]
    exact_mod_cast (G.z271 {e | ω e} u s).mp hh
  · simp only [if_neg hh,mul_zero]
    exact Nat.cast_nonneg _
lemma z417 (S : Set V) (hS : (G.z4 S).Finite)
    (p : unitInterval) (u : S) (s : ℕ) :
    ((G.induce S).law p).real ((G.induce S).z17 u s) =
      (G.law p).real {ω | G.z4 S ∩ ω ∈ G.z17 u.val s} := by
  have he : (G.induce S).z17 u s =
      {ω | Subtype.val '' ω ∈ G.z17 u.val s} := by
    ext ω
    exact G.z360 S ω u s
  rw [he,G.z440 S hS]
lemma z162 (hlocal : G.LocallyFinite)
    (p : unitInterval) (D : ℕ) (hD : ∀ v, (G.z9 {v}).ncard≤D)
    (hpD : 4*(p:ℝ)*D≤1) (S : Set V) (hS : S.Finite) (u : S) (s : ℕ) :
    (s:ℝ)*(G.law p).real {ω | G.z4 S ∩ ω ∈ G.z17 u.val s} ≤ 2 := by
  let := hS.fintype
  let := (G.z27 hlocal hS).fintype
  have h := (G.induce S).z179 p D
    (G.z226 hlocal D hD S) hpD u s
  rwa [G.z417 S (G.z27 hlocal hS)] at h
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
lemma z329 (hconnected : G.z7.Connected)
    (hlocal : G.LocallyFinite) (p : unitInterval) (D : ℕ)
    (hD : ∀ v, (G.z9 {v}).ncard≤D) (hpD : 4*(p:ℝ)*D≤1)
    (u : V) (s : ℕ) : (s:ℝ)*(G.law p).real (G.z17 u s) ≤ 2 := by
  let K := G.inducedBallExhaustion hconnected hlocal u
  have ht := z0.z112 p (G.z17 u s)
    (G.z24 u s) (G.z30 u s) K
  have ht' : Tendsto (fun n => (s:ℝ)*(G.law p).real {ω | K n ∩ ω ∈ G.z17 u s})
      atTop (𝓝 ((s:ℝ)*(G.law p).real (G.z17 u s))) := by
    simpa only [law,← z0.law_const] using ht.const_mul (s:ℝ)
  apply le_of_tendsto ht'
  exact Filter.Eventually.of_forall (fun n => G.z162 hlocal p D hD hpD
    (G.z5 u n) (G.z19 hlocal u n) ⟨u,G.z45 u n⟩ s)
lemma z248 (hconnected : G.z7.Connected)
    (hlocal : G.LocallyFinite) (p : unitInterval) (D : ℕ)
    (hD : ∀ v, (G.z9 {v}).ncard≤D) (hpD : 4*(p:ℝ)*D≤1) (u : V) :
    G.law p (G.z14 u) = 0 := by
  have hreal : (G.law p).real (G.z14 u) = 0 := by
    apply le_antisymm _ measureReal_nonneg
    by_contra! hp
    obtain ⟨n,hn⟩ := exists_nat_gt (2/(G.law p).real (G.z14 u))
    have hh : (n:ℝ)*(G.law p).real (G.z14 u) ≤ 2 := by
      calc
        _ ≤ (n:ℝ)*(G.law p).real (G.z17 u n) :=
          mul_le_mul_of_nonneg_left (measureReal_mono (G.z29 u n))
            (Nat.cast_nonneg _)
        _ ≤ 2 := G.z329 hconnected hlocal p D hD hpD u n
    have hlt := (div_lt_iff₀ hp).mp hn
    linarith
  have hh := (ENNReal.toReal_eq_zero_iff _).mp hreal
  exact hh.resolve_right (measure_ne_top _ _)
lemma z191 (hconnected : G.z7.Connected)
    (hlocal : G.LocallyFinite) (p : unitInterval) (D : ℕ)
    (hD : ∀ v, (G.z9 {v}).ncard≤D) (hpD : 4*(p:ℝ)*D≤1) :
    G.law p G.z12 = 0 := by
  let := G.z53 hconnected hlocal
  let := G.z113 hconnected hlocal
  apply (G.z157 (G.law p)).mpr
  exact G.z248 hconnected hlocal p D hD hpD
theorem z167 (hconnected : G.z7.Connected)
    (hlocal : G.LocallyFinite) (hquasi : G.QuasiTransitive) :
    (0:ℝ)<G.z3 := by
  obtain ⟨D,_,hD⟩ := G.z190 hquasi
  have hd : (0:ℝ)<4*(D:ℝ)+1 := by positivity
  let p₀ : unitInterval := ⟨1/(4*(D:ℝ)+1), by
    constructor
    · positivity
    · exact (div_le_one hd).mpr (by
        have hh : (0:ℝ) ≤ 4 * (D:ℝ) := by positivity
        linarith)⟩
  have he : (p₀:ℝ)*(4*(D:ℝ)+1)=1 := div_mul_cancel₀ _ hd.ne'
  have hp₀ : (0:ℝ)<p₀ := one_div_pos.mpr hd
  have hsmall : ∀ p : unitInterval, p≤p₀ → 4*(p:ℝ)*D≤1 := by
    intro p hp
    have hn : (0:ℝ)≤D := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_right (show (p:ℝ)≤p₀ from hp) hn
    nlinarith [p₀.property.1]
  have hle : p₀≤G.z3 := by
    apply le_sInf
    intro p hp
    by_contra h
    have hpp : p≤p₀ := (not_le.mp h).le
    have hz := G.z191 hconnected hlocal p D hD (hsmall p hpp)
    exact (ne_of_gt hp) hz
  exact hp₀.trans_le hle
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal
namespace CriticalPercolation.z2
variable {V E : Type} (G : z2 V E)
lemma z483 (u v : V → ℝ) (U Q : ℝ) (a b : Bool) (φ : G.Aut)
    (hu : ∀ x y, u (φ.vertex x)-u (φ.vertex y)=u x-u y)
    (hv : ∀ x y, v (φ.vertex x)-v (φ.vertex y)=v x-v y) :
    (∀ x y, stripTime u v U Q a b (φ.vertex x)-stripTime u v U Q a b (φ.vertex y)=
      stripTime u v U Q a b x-stripTime u v U Q a b y) ∧
    (∀ x y, stripHeight u v U Q a b (φ.vertex x)-stripHeight u v U Q a b (φ.vertex y)=
      stripHeight u v U Q a b x-stripHeight u v U Q a b y) := by
  constructor
  · intro x y
    calc
      _ = Corridor.sign a*(u (φ.vertex x)-u (φ.vertex y))/U+
        Corridor.sign b*(v (φ.vertex x)-v (φ.vertex y))/Q := by unfold stripTime; ring
      _ = _ := by rw [hu,hv]; unfold stripTime; ring
  · intro x y
    calc
      _ = Corridor.sign a*(u (φ.vertex x)-u (φ.vertex y))/U-
        Corridor.sign b*(v (φ.vertex x)-v (φ.vertex y))/Q := by unfold stripHeight; ring
      _ = _ := by rw [hu,hv]; unfold stripHeight; ring
theorem z523 [Countable V] [Countable E]
    (hc : G.z7.Connected) (hl : G.LocallyFinite)
    (u v : V → ℝ) (o : V) (c : ℕ) (D : ℝ) (pc : unitInterval)
    (hD : 0≤D) (hpc : 0<pc) (huo : u o=0) (hvo : v o=0)
    (hu : ∀ ⦃x y⦄, G.z7.Adj x y → |u x-u y|≤D)
    (hv : ∀ ⦃x y⦄, G.z7.Adj x y → |v x-v y|≤D)
    (hdense : ∀ y, ∃ φ : G.Aut, φ.vertex o∈G.z5 y c ∧
      (∀ x y, u (φ.vertex x)-u (φ.vertex y)=u x-u y) ∧
      (∀ x y, v (φ.vertex x)-v (φ.vertex y)=v x-v y))
    (hstrip : 0<(z0.law (fun _ : E => pc)) (G.someStripPercolates v))
    (hdir : ∀ᵐ ω ∂z0.law (fun _ : E => pc),
      ∀ a, (G.cluster ω a).Infinite → ∀ n : ℕ, ∃ x∈G.cluster ω a, (n : ℝ)<v x)
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂z0.law (fun _ : E => pc), ∀ a,
      (G.cluster (ω∩G.z4 {x | |u x|≤U ∧ |v x|≤W}) a).Finite)
    (eps eta : ℝ) (heps : 0<eps) (heps' : eps<1/10) (heta : 0<eta) :
    ∃ m : ℕ, ∀ rho : ℝ, 0<rho → ∃ t z : V → ℝ, ∃ p : unitInterval,
      (pc : ℝ)/2≤p ∧ p<pc ∧
      (∀ ⦃x y⦄, G.z7.Adj x y → |t x-t y|≤rho) ∧
      (∀ ⦃x y⦄, G.z7.Adj x y → |z x-z y|≤rho) ∧
      ∀ y s, |s|=1 → 1-eta≤(z0.law (fun _ : E => p)).real
        (G.coordinateMove t z m eps y s) := by
  obtain ⟨m,hm⟩ := G.z557 hc hl u v o D pc hD huo hvo hu hv
    hstrip hdir hbox eps eta heps heps' heta
  refine ⟨m+c,?_⟩
  intro rho hrho
  let r := min rho (eps/(8*((c : ℝ)+1)))
  have hcpos : 0<(c : ℝ)+1 := by positivity
  have hr : 0<r := lt_min hrho (div_pos heps (by positivity))
  have hrrho : r≤rho := min_le_left _ _
  have hrs : r≤eps/(8*((c : ℝ)+1)) := min_le_right _ _
  have hmesh : (c : ℝ)*r≤eps/8 := by
    have hh := (le_div_iff₀ (by positivity : 0<8*((c : ℝ)+1))).mp hrs
    nlinarith
  obtain ⟨U,Q,a,b,_hU,_hQ,ht,hz,hmoves⟩ := hm r hr
  have htdense : ∀ y, ∃ φ : G.Aut, φ.vertex o∈G.z5 y c ∧
      (∀ x y, stripTime u v U Q a b (φ.vertex x)-stripTime u v U Q a b (φ.vertex y)=
        stripTime u v U Q a b x-stripTime u v U Q a b y) ∧
      (∀ x y, stripHeight u v U Q a b (φ.vertex x)-stripHeight u v U Q a b (φ.vertex y)=
        stripHeight u v U Q a b x-stripHeight u v U Q a b y) := by
    intro y
    obtain ⟨φ,hφ,hφu,hφv⟩ := hdense y
    exact ⟨φ,hφ,G.z483 u v U Q a b φ hφu hφv⟩
  obtain ⟨p,hpl,hpu,hp⟩ := G.z175 (stripTime u v U Q a b)
    (stripHeight u v U Q a b) o m c eps eta r heps' hr.le hmesh ht hz htdense pc hpc hmoves
  exact ⟨stripTime u v U Q a b,stripHeight u v U Q a b,p,hpl,hpu,
    fun {_ _} h => (ht h).trans hrrho,fun {_ _} h => (hz h).trans hrrho,hp⟩
theorem z281 [Fact (∀ V E : Type, CriticalPercolationLeaf.FiniteSizeCriterion V E)] [Countable V] [Countable E]
    (hc : G.z7.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (u v : V → ℝ) (o : V) (c : ℕ) (D : ℝ)
    (hD : 0≤D) (hpc : 0<(G.z3 : ℝ))
    (hpc1 : (G.z3 : ℝ)<1) (huo : u o=0) (hvo : v o=0)
    (hu : ∀ ⦃x y⦄, G.z7.Adj x y → |u x-u y|≤D)
    (hv : ∀ ⦃x y⦄, G.z7.Adj x y → |v x-v y|≤D)
    (hdense : ∀ y, ∃ φ : G.Aut, φ.vertex o∈G.z5 y c ∧
      (∀ x y, u (φ.vertex x)-u (φ.vertex y)=u x-u y) ∧
      (∀ x y, v (φ.vertex x)-v (φ.vertex y)=v x-v y))
    (hstrip : 0<(z0.law (fun _ : E => G.z3)) (G.someStripPercolates v))
    (hdir : ∀ᵐ ω ∂z0.law (fun _ : E => G.z3),
      ∀ a, (G.cluster ω a).Infinite → ∀ n : ℕ, ∃ x∈G.cluster ω a, (n : ℝ)<v x)
    (hbox : ∀ U W : ℝ, ∀ᵐ ω ∂z0.law (fun _ : E => G.z3), ∀ a,
      (G.cluster (ω∩G.z4 {x | |u x|≤U ∧ |v x|≤W}) a).Finite) : False := by
  apply G.z75 hc hl hq hpc hpc1
  intro eps eta he he' heta _heta'
  exact G.z523 hc hl u v o c D G.z3 hD hpc huo hvo hu hv hdense
    hstrip hdir hbox eps eta he he' heta
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal
namespace CriticalPercolation.z2
variable {V E : Type} (G : z2 V E)
theorem z540 [Fact (∀ V E : Type, CriticalPercolationLeaf.FiniteSizeCriterion V E)] (hc : G.z7.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (hg : G.SubexponentialGrowth)
    (hpc1 : G.z3<1)
    (u v : V → ℝ) (o : V) (c : ℕ) (D : ℝ)
    (hD : 0≤D) (huo : u o=0) (hvo : v o=0)
    (hu : ∀ ⦃x y⦄, G.z7.Adj x y → |u x-u y|≤D)
    (hv : ∀ ⦃x y⦄, G.z7.Adj x y → |v x-v y|≤D)
    (hvunbounded : ∀ n : ℕ, ∃ x, (n : ℝ)<v x)
    (hdense : ∀ y, ∃ φ : G.Aut, φ.vertex o∈G.z5 y c ∧
      (∀ x y, u (φ.vertex x)-u (φ.vertex y)=u x-u y) ∧
      (∀ x y, v (φ.vertex x)-v (φ.vertex y)=v x-v y))
    (hnoray : ∀ᵐ ω ∂G.law G.z3,
      ¬∃ r : G.OpenRay ω, ∃ U W : ℝ, ∀ n, |u (r.vertex n)|≤U ∧ |v (r.vertex n)|≤W) :
    G.law G.z3 (G.someStripPercolates v)=0 := by
  let := G.z53 hc hl
  let := G.z113 hc hl
  by_contra hne
  have hstrip : 0<(z0.law (fun _ : E => G.z3))
      (G.someStripPercolates v) := by
    simpa only [law,z0.law_const] using (pos_iff_ne_zero.mpr hne)
  have hsub : G.someStripPercolates v⊆G.z12 := by
    intro ω hω
    obtain ⟨n,a,ha⟩ := Set.mem_iUnion.mp hω
    exact ⟨a,ha.mono (G.cluster_mono Set.inter_subset_left a)⟩
  have hpositive : 0<G.law G.z3 G.z12 :=
    (pos_iff_ne_zero.mpr hne).trans_le (measure_mono hsub)
  have hpc := G.z167 hc hl hq
  have hdir := G.z109 hc hl hq hg G.z3
    ⟨hpc,hpc1⟩ hpositive v hvunbounded
  have hdir' : ∀ᵐ ω ∂z0.law (fun _ : E => G.z3),
      ∀ a, (G.cluster ω a).Infinite → ∀ n : ℕ, ∃ x∈G.cluster ω a, (n : ℝ)<v x := by
    simpa only [law,z0.law_const] using hdir
  have hbox : ∀ U W : ℝ, ∀ᵐ ω ∂z0.law (fun _ : E => G.z3), ∀ a,
      (G.cluster (ω∩G.z4 {x | |u x|≤U ∧ |v x|≤W}) a).Finite := by
    intro U W
    have h := hnoray.mono (fun ω hω => G.z130 hl u v ω hω U W)
    simpa only [law,z0.law_const] using h
  exact G.z281 hc hl hq u v o c D hD hpc hpc1 huo hvo hu hv hdense
    hstrip hdir' hbox
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal
namespace CriticalPercolation.z2
variable {V E : Type} (G : z2 V E)
lemma z293 (v : V → ℝ) (w : ℝ) :
    G.stripPercolates v w⊆G.someStripPercolates v := by
  obtain ⟨n,hn⟩ := exists_nat_ge w
  rintro ω ⟨a,ha⟩
  apply Set.mem_iUnion.mpr
  exact ⟨n,a,ha.mono (G.cluster_mono (Set.inter_subset_inter_right _
    (G.z207 (fun _ hx => hx.trans hn))) a)⟩
theorem z110 [Fact (∀ V E : Type, CriticalPercolationLeaf.FiniteSizeCriterion V E)]
    (hc : G.z7.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hg : G.SubexponentialGrowth) (hpc1 : G.z3<1)
    (pi : V → ℂ) (o : V) (c : ℕ) (D : ℝ) (hD : 0≤D) (hpo : pi o=0)
    (hpi : ∀ ⦃x y⦄, G.z7.Adj x y → ‖pi x-pi y‖≤D)
    (honto : ∀ m n : ℤ, ∃ x, (pi x).re=m ∧ (pi x).im=n)
    (hdense : ∀ y, ∃ phi : G.Aut, phi.vertex o∈G.z5 y c ∧
      ∀ x y, pi (phi.vertex x)-pi (phi.vertex y)=pi x-pi y)
    (hnoray : ∀ᵐ ω ∂G.law G.z3,
      ¬∃ r : G.OpenRay ω, ∃ U W : ℝ,
        ∀ n, |(pi (r.vertex n)).re|≤U ∧ |(pi (r.vertex n)).im|≤W) :
    G.law G.z3 G.z12=0 := by
  let := G.z53 hc hl
  let := G.z113 hc hl
  have hpc := G.z167 hc hl hq
  have hur : ∀ ⦃x y⦄, G.z7.Adj x y → |(pi x).re-(pi y).re|≤D :=
    fun {_ _} h => (Complex.abs_re_le_norm _).trans (hpi h)
  have hvi : ∀ ⦃x y⦄, G.z7.Adj x y → |(pi x).im-(pi y).im|≤D :=
    fun {_ _} h => (Complex.abs_im_le_norm _).trans (hpi h)
  have hnull : ∀ a b : ℝ, a^2+b^2=1 → ∀ w : ℝ,
      z0.law (fun _ : E => G.z3)
        (G.stripPercolates (z10 (fun x => (pi x).re) (fun x => (pi x).im) a b) w)=0 := by
    intro a b hab w
    let u := parallelCoordinate (fun x => (pi x).re) (fun x => (pi x).im) a b
    let v := z10 (fun x => (pi x).re) (fun x => (pi x).im) a b
    have huo : u o=0 := by simp [u,parallelCoordinate,hpo]
    have hvo : v o=0 := by simp [v,z10,hpo]
    have hsteps := G.z245 (fun x => (pi x).re) (fun x => (pi x).im) a b D hab hD hur hvi
    have hdense' : ∀ y, ∃ phi : G.Aut, phi.vertex o∈G.z5 y c ∧
        (∀ x y, u (phi.vertex x)-u (phi.vertex y)=u x-u y) ∧
        (∀ x y, v (phi.vertex x)-v (phi.vertex y)=v x-v y) := by
      intro y
      obtain ⟨phi,hphi,hP⟩ := hdense y
      have hpr : ∀ x y, (pi (phi.vertex x)).re-(pi (phi.vertex y)).re=(pi x).re-(pi y).re :=
        fun x y => congrArg Complex.re (hP x y)
      have hpi' : ∀ x y, (pi (phi.vertex x)).im-(pi (phi.vertex y)).im=(pi x).im-(pi y).im :=
        fun x y => congrArg Complex.im (hP x y)
      exact ⟨phi,hphi,G.z407 _ _ a b phi hpr hpi'⟩
    have hn : ∀ᵐ ω ∂G.law G.z3,
        ¬∃ r : G.OpenRay ω, ∃ U W : ℝ, ∀ n, |u (r.vertex n)|≤U ∧ |v (r.vertex n)|≤W := by
      filter_upwards [hnoray] with ω hω
      exact G.z429 _ _ a b hab ω hω
    have hs := G.z540 hc hl hq hg hpc1 u v o c (2*D) (by positivity) huo hvo hsteps.1 hsteps.2
      (z100 pi honto a b hab) hdense' hn
    have hm := measure_mono (μ := G.law G.z3) (G.z293 v w)
    rw [hs] at hm
    simpa only [law,z0.law_const] using le_antisymm hm (bot_le)
  by_contra hne
  have hpos := pos_iff_ne_zero.mpr hne
  have hone : z0.law (fun _ : E => G.z3) G.z12=1 := by
    simpa only [law,z0.law_const] using G.z313 G.z3 hpos
  have hbox : ∀ U W : ℝ, ∀ᵐ ω ∂z0.law (fun _ : E => G.z3), ∀ x,
      (G.cluster (ω∩G.z4 {x | |(pi x).re|≤U ∧ |(pi x).im|≤W}) x).Finite := by
    intro U W
    have hh := hnoray.mono (fun ω hω => G.z130 hl (fun x => (pi x).re) (fun x => (pi x).im) ω hω U W)
    simpa only [law,z0.law_const] using hh
  exact G.z219 hc hl hq pi o c D hD hpc hpc1 hpo hpi hdense hone hbox hnull
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.z2
variable {V E Λ N : Type} (G : z2 V E)
  [Group Λ] [Group N] [MulAction Λ V] [MulAction Λ E]
def integerPairComplex (z : ℤ×ℤ) : ℂ := (z.1 : ℂ)+(z.2 : ℂ)*Complex.I
lemma z449 (a b : ℤ×ℤ) :
    integerPairComplex (a+b)=integerPairComplex a+integerPairComplex b := by
  simp only [integerPairComplex,Prod.fst_add,Prod.snd_add,Int.cast_add]
  ring
lemma z230 (z : ℤ×ℤ) : (integerPairComplex z).re=z.1 := by
  simp [integerPairComplex]
lemma z224 (z : ℤ×ℤ) : (integerPairComplex z).im=z.2 := by
  simp [integerPairComplex]
theorem z193
    (ρ : Λ →* N) (hρ : Surjective ρ)
    (φ : N →* Multiplicative (ℤ×ℤ)) (hφ : Surjective φ)
    (hstab : ∀ v : V, ((MulAction.stabilizer Λ v).map ρ : Set N).Finite)
    [Nonempty V] :
    ∃ z : V → ℤ×ℤ, Surjective z ∧
      ∀ g v, z (g • v)=(φ (ρ g)).toAdd+z v := by
  obtain ⟨π,hπ⟩ := EquivariantCoordinates.z345 (φ.comp ρ)
    (EquivariantCoordinates.z397 ρ φ hstab)
  refine ⟨fun v => (π v).toAdd,?_,?_⟩
  · intro t
    obtain ⟨v,hv⟩ := EquivariantCoordinates.z346
      (φ.comp ρ) (hφ.comp hρ) π hπ (Multiplicative.ofAdd t)
    exact ⟨v,congrArg Multiplicative.toAdd hv⟩
  · intro g v
    exact congrArg Multiplicative.toAdd (hπ g v)
lemma z184
    (hc : G.z7.Connected) (hl : G.LocallyFinite)
    (ha : G.PreservesEnds (Λ := Λ))
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (a : Λ → ℤ×ℤ) (z : V → ℤ×ℤ) (honto : Surjective z)
    (hz : ∀ g v, z (g • v)=a g+z v) :
    ∃ (o : V) (c : ℕ) (D : ℝ), 0≤D ∧ integerPairComplex (z o)=0 ∧
      (∀ ⦃x y⦄, G.z7.Adj x y →
        ‖integerPairComplex (z x)-integerPairComplex (z y)‖≤D) ∧
      (∀ m n : ℤ, ∃ x, (integerPairComplex (z x)).re=m ∧
        (integerPairComplex (z x)).im=n) ∧
      (∀ y, ∃ psi : G.Aut, psi.vertex o∈G.z5 y c ∧
        ∀ x y, integerPairComplex (z (psi.vertex x))-integerPairComplex (z (psi.vertex y))=
          integerPairComplex (z x)-integerPairComplex (z y)) := by
  let pi : V → ℂ := fun v => integerPairComplex (z v)
  have hpi : ∀ g v, pi (g • v)=integerPairComplex (a g)+pi v := by
    intro g v
    exact (congrArg integerPairComplex (hz g v)).trans (z449 _ _)
  obtain ⟨o,ho⟩ := honto 0
  obtain ⟨c,hc'⟩ := G.z541 (fun g => G.smulAut ha g) (fun _ _ => rfl)
    hc S hS hcover o
  obtain ⟨D,hD,hj⟩ := G.z152 hl ha S hS hcover
    (fun g => integerPairComplex (a g)) pi hpi
  refine ⟨o,c,D,hD,?_,?_,?_,?_⟩
  · simp [ho,integerPairComplex]
  · intro x y hxy
    obtain ⟨⟨e,_,he⟩,_⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hxy
    exact hj e x y he
  · intro m n
    obtain ⟨x,hx⟩ := honto (m,n)
    exact ⟨x,by rw [hx,z230],by rw [hx,z224]⟩
  · intro y
    obtain ⟨g,hg⟩ := hc' y
    refine ⟨G.smulAut ha g,hg,?_⟩
    intro x y
    change pi (g • x)-pi (g • y)=pi x-pi y
    rw [hpi,hpi]
    abel
theorem z136 [Fact (∀ V E : Type, CriticalPercolationLeaf.FiniteSizeCriterion V E)]
    (hc : G.z7.Connected) (hl : G.LocallyFinite)
    (ha : G.PreservesEnds (Λ := Λ))
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (hg : G.SubexponentialGrowth) (hpc : G.z3<1)
    (a : Λ → ℤ×ℤ) (z : V → ℤ×ℤ) (honto : Surjective z)
    (hz : ∀ g v, z (g • v)=a g+z v)
    (hnoray : ∀ᵐ ω ∂G.law G.z3,
      ¬∃ r : G.OpenRay ω, ∃ U W : ℝ, ∀ n,
        |(z (r.vertex n)).1|≤U ∧ |(z (r.vertex n)).2|≤W) :
    G.law G.z3 G.z12=0 := by
  obtain ⟨o,c,D,hD,ho,hjump,honto',hdense⟩ :=
    G.z184 hc hl ha S hS hcover a z honto hz
  apply G.z110 hc hl
    (G.z344 ha S hS hcover) hg hpc
    (fun v => integerPairComplex (z v)) o c D hD ho hjump honto' hdense
  simpa only [z230,z224,Int.cast_abs] using hnoray
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
lemma z263 (hl : G.LocallyFinite) (S : Set V) : (G.induce S).LocallyFinite := by
  intro v
  apply (Set.Finite.preimage Subtype.val_injective.injOn (hl v.val)).subset
  intro e he
  have hh : v.val∈Sym2.map Subtype.val ((G.induce S).ends e) := Sym2.mem_map.mpr ⟨v,he,rfl⟩
  rwa [G.z107] at hh
lemma z506 (S : Set V) (x y : S) :
    (G.induce S).z7.Adj x y → G.z7.Adj x.val y.val := by
  intro h
  exact G.openGraph_mono (Set.subset_univ _) ((G.induce_adj S Set.univ x y).mp h)
lemma z378 (S : Set V) (o : S) (n : ℕ) :
    Subtype.val '' (G.induce S).z5 o n ⊆ G.z5 o.val n := by
  induction n with
  | zero => rintro x ⟨y,rfl,rfl⟩; rfl
  | succ n ih =>
    rintro x ⟨y,hy,rfl⟩
    rcases hy with hy|hy
    · exact G.z26 o.val (Nat.le_succ n) (ih ⟨y,hy,rfl⟩)
    · obtain ⟨z,hz,hzy⟩ := Set.mem_iUnion₂.mp hy
      exact G.z186 (ih ⟨z,hz,rfl⟩) (G.z506 S z y hzy)
lemma z477 (hl : G.LocallyFinite) (hg : G.SubexponentialGrowth) (S : Set V) :
    (G.induce S).SubexponentialGrowth := by
  intro o ε hε
  obtain ⟨N,hN⟩ := hg o.val ε hε
  refine ⟨N,fun n hn => ?_⟩
  have hcard : ((G.induce S).z5 o n).ncard ≤ (G.z5 o.val n).ncard := by
    rw [←Set.ncard_image_of_injective _ Subtype.val_injective]
    exact Set.ncard_le_ncard (G.z378 S o n) (G.z19 hl o.val n)
  have hpositive : 0<(((G.induce S).z5 o n).ncard : ℝ) := by
    exact_mod_cast (Set.ncard_pos ((G.induce S).z19 (G.z263 hl S) o n)).mpr
      ⟨o,(G.induce S).z45 o n⟩
  exact (Real.log_le_log hpositive (by exact_mod_cast hcard)).trans (hN n hn)
lemma z384 (S : Set V) :
    (fun ω : Set E => Subtype.val ⁻¹' ω : Set E → Set (G.z4 S)) ⁻¹' (G.induce S).z12
      ⊆G.z12 := by
  rintro ω ⟨o,ho⟩
  refine ⟨o.val,?_⟩
  have hi := ho.image Subtype.val_injective.injOn
  rw [G.z282] at hi
  exact hi.mono (G.cluster_mono (by rintro e ⟨a,ha,rfl⟩; exact ha) o.val)
lemma law_induce [Countable V] [Countable E] (S : Set V) (p : unitInterval) :
    (G.law p).map (fun ω : Set E => Subtype.val ⁻¹' ω : Set E → Set (G.z4 S)) =
      (G.induce S).law p := by
  simpa only [law,z0.law_const] using
    z0.z97 (fun _ : E => p) (G.z4 S)
lemma z383 [Countable V] [Countable E] (S : Set V) (p : unitInterval) :
    (G.induce S).law p (G.induce S).z12 ≤ G.law p G.z12 := by
  rw [←G.law_induce S p,Measure.map_apply]
  · exact measure_mono (G.z384 S)
  · exact measurable_pi_iff.mpr (fun edge => measurable_set_mem edge.val)
  · exact (G.induce S).z37
lemma z239 [Countable V] [Countable E] (S : Set V) :
    G.z3≤(G.induce S).z3 := by
  apply le_sInf
  intro p hp
  exact G.z51 (hp.trans_le (G.z383 S p))
lemma z122 [Countable V] [Countable E] (S : Set V)
    (hpos : 0<(G.induce S).law G.z3 (G.induce S).z12) :
    (G.induce S).z3=G.z3 :=
  le_antisymm ((G.induce S).z51 hpos) (G.z239 S)
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
lemma image_restrict (S : Set V) (ω : Set E) :
    Subtype.val '' (Subtype.val ⁻¹' ω : Set (G.z4 S))=ω∩G.z4 S := by
  ext e
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨ha,a.property⟩
  · rintro ⟨he,hs⟩
    exact ⟨⟨e,hs⟩,he,rfl⟩
def domainComponent (S : Set V) (o : V) : Set V := G.cluster (G.z4 S) o
lemma z431 {S : Set V} {o : V} (ho : o∈S) :
    G.domainComponent S o⊆S := by
  have h := G.z204 S Set.univ (⟨o,ho⟩ : S)
  simpa only [Set.image_univ,Subtype.range_coe,domainComponent] using h
lemma z273 (S : Set V) (o : V) : o∈G.domainComponent S o :=
  SimpleGraph.Reachable.refl o
lemma z196 (S : Set V) (o : V) {x y : V}
    (hx : x∈G.domainComponent S o) (hxy : (G.z1 (G.z4 S)).Adj x y) :
    y∈G.domainComponent S o := hx.trans hxy.reachable
lemma z351 (S : Set V) (o : V) :
    (G.induce (G.domainComponent S o)).z7.Connected := by
  let C := G.domainComponent S o
  let a : C := ⟨o,G.z273 S o⟩
  have hreach : ∀ x : C, ((G.induce C).z7).Reachable a x := by
    intro x
    apply (G.z148 C Set.univ a x).mpr
    rw [Set.image_univ,Subtype.range_coe]
    have h : (G.z1 (G.z4 S)).Reachable o x.val := x.property
    rw [SimpleGraph.reachable_iff_reflTransGen] at h ⊢
    have H : ∀ y, Relation.ReflTransGen (G.z1 (G.z4 S)).Adj o y →
        Relation.ReflTransGen (G.z1 (G.z4 C)).Adj o y := by
      intro y hy
      induction hy with
      | refl => exact .refl
      | @tail b c hr hadj ih =>
        have hb : b∈C := (SimpleGraph.reachable_iff_reflTransGen _ _).mpr hr
        have hc : c∈C := G.z196 S o hb hadj
        obtain ⟨⟨e,he,hend⟩,hne⟩ := (SimpleGraph.fromEdgeSet_adj _).mp hadj
        have hC : e∈G.z4 C := by
          intro v hv
          rw [hend] at hv
          rcases Sym2.mem_iff.mp hv with rfl|rfl
          · exact hb
          · exact hc
        exact ih.tail ((SimpleGraph.fromEdgeSet_adj _).mpr ⟨⟨e,hC,hend⟩,hne⟩)
    exact H _ h
  exact (SimpleGraph.connected_iff_exists_forall_reachable _).mpr ⟨a,hreach⟩
lemma OpenRay.z602 {ω : Set E} (r : G.OpenRay ω) (n : ℕ) :
    (G.z1 ω).Reachable (r.vertex 0) (r.vertex n) := by
  induction n with
  | zero => exact .refl _
  | succ n ih => exact ih.trans (r.adjacent n).reachable
lemma OpenRay.z12 {ω : Set E} (r : G.OpenRay ω) : ω∈G.z12 := by
  refine ⟨r.vertex 0,?_⟩
  exact (Set.infinite_range_of_injective r.injective).mono (by
    rintro x ⟨n,rfl⟩
    exact r.z602 G n)
def OpenRay.induce {ω : Set E} (r : G.OpenRay ω) (S : Set V)
    (hS : ∀ n, r.vertex n∈S) :
    (G.induce S).OpenRay (Subtype.val ⁻¹' ω) where
  vertex n := ⟨r.vertex n,hS n⟩
  injective := fun _ _ h => r.injective (congrArg Subtype.val h)
  adjacent n := by
    apply (G.induce_adj S (Subtype.val ⁻¹' ω) _ _).mpr
    rw [G.image_restrict]
    exact (G.z70 S ω _ _).mpr ⟨r.adjacent n,hS n,hS (n+1)⟩
lemma OpenRay.z537 {ω : Set E} (r : G.OpenRay ω) (S : Set V)
    (hS : ∀ n, r.vertex n∈S) (n : ℕ) :
    r.vertex n∈G.domainComponent S (r.vertex 0) := by
  induction n with
  | zero => exact G.z273 S _
  | succ n ih =>
    apply G.z196 S _ ih
    apply G.openGraph_mono Set.inter_subset_right
    exact (G.z70 S ω _ _).mpr ⟨r.adjacent n,hS n,hS (n+1)⟩
lemma z231 [Countable V] [Countable E]
    (S : Set V) (p : unitInterval) (h : (G.induce S).law p (G.induce S).z12=0) :
    ∀ᵐ ω ∂G.law p, Subtype.val ⁻¹' ω∉(G.induce S).z12 := by
  rw [←G.law_induce S p,Measure.map_apply] at h
  · apply ae_iff.mpr
    convert h using 1
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_preimage,not_not]
  · exact measurable_pi_iff.mpr (fun edge => measurable_set_mem edge.val)
  · exact (G.induce S).z37
theorem z213 [Countable V] [Countable E]
    (u v : V → ℝ)
    (hbad : ¬∀ᵐ ω ∂G.law G.z3,
      ¬∃ r : G.OpenRay ω, ∃ U W : ℝ,
        ∀ n, |u (r.vertex n)|≤U ∧ |v (r.vertex n)|≤W) :
    ∃ (k : ℕ) (o : V),
      let S := {x | |u x|≤(k:ℝ) ∧ |v x|≤(k:ℝ)}
      o∈S ∧
      let H := G.induce (G.domainComponent S o)
      H.z3=G.z3 ∧
      0<H.law H.z3 H.z12 := by
  let S : ℕ → Set V := fun k => {x | |u x|≤(k:ℝ) ∧ |v x|≤(k:ℝ)}
  have hex : ∃ (k : ℕ) (o : V), o∈S k ∧
      0<(G.induce (G.domainComponent (S k) o)).law G.z3
        (G.induce (G.domainComponent (S k) o)).z12 := by
    by_contra hh
    push Not at hh
    have ha : ∀ k o, ∀ᵐ ω ∂G.law G.z3,
        o∈S k → Subtype.val ⁻¹' ω∉(G.induce (G.domainComponent (S k) o)).z12 := by
      intro k o
      by_cases ho : o∈S k
      · exact (G.z231 _ _ (le_antisymm (hh k o ho) bot_le)).mono
          (fun _ h _ => h)
      · exact Filter.Eventually.of_forall (fun _ h => (ho h).elim)
    have hall : ∀ᵐ ω ∂G.law G.z3, ∀ k o,
        o∈S k → Subtype.val ⁻¹' ω∉(G.induce (G.domainComponent (S k) o)).z12 :=
      (ae_all_iff.mpr fun k => ae_all_iff.mpr (ha k))
    apply hbad
    filter_upwards [hall] with ω hω
    rintro ⟨r,U,W,hr⟩
    obtain ⟨k,hk⟩ := exists_nat_ge (max U W)
    have hrS : ∀ n, r.vertex n∈S k := fun n =>
      ⟨(hr n).1.trans ((le_max_left _ _).trans hk),
       (hr n).2.trans ((le_max_right _ _).trans hk)⟩
    exact hω k (r.vertex 0) (hrS 0)
      ((r.induce G _ (r.z537 G _ hrS)).z12 _)
  obtain ⟨k,o,ho,hp⟩ := hex
  have heq := G.z122 (G.domainComponent (S k) o) hp
  exact ⟨k,o,ho,heq,by rwa [heq]⟩
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical
namespace CriticalPercolation.z2
variable {V E : Type*} (G : z2 V E)
lemma Aut.z95 (phi : G.Aut) (S : Set V)
    (hS : ∀ x, phi.vertex x∈S ↔ x∈S) (e : E) :
    phi.edge e∈G.z4 S ↔ e∈G.z4 S := by
  constructor
  · intro h x hx
    apply (hS x).mp
    apply h (phi.vertex x)
    rw [phi.preserves]
    exact Sym2.mem_map.mpr ⟨x,hx,rfl⟩
  · intro h y hy
    rw [phi.preserves] at hy
    obtain ⟨x,hx,rfl⟩ := Sym2.mem_map.mp hy
    exact (hS x).mpr (h x hx)
lemma Aut.z563 (phi : G.Aut) (S : Set V)
    (hS : ∀ x, phi.vertex x∈S ↔ x∈S) :
    phi.edge '' G.z4 S=G.z4 S := by
  ext e
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact (Aut.z95 G phi S hS a).mpr ha
  · intro he
    exact ⟨phi.edge.symm e,(Aut.z95 G phi S hS (phi.edge.symm e)).mp
      (by simpa only [Equiv.apply_symm_apply] using he),phi.edge.apply_symm_apply e⟩
def Aut.restrict (phi : G.Aut) (S : Set V)
    (hS : ∀ x, phi.vertex x∈S ↔ x∈S) : (G.induce S).Aut where
  vertex :=
    { toFun := fun x => ⟨phi.vertex x,(hS x).mpr x.property⟩
      invFun := fun x => ⟨phi.vertex.symm x,(hS (phi.vertex.symm x)).mp
        (by simpa only [Equiv.apply_symm_apply] using x.property)⟩
      left_inv := fun x => Subtype.ext (phi.vertex.symm_apply_apply x)
      right_inv := fun x => Subtype.ext (phi.vertex.apply_symm_apply x) }
  edge :=
    { toFun := fun e => ⟨phi.edge e,(Aut.z95 G phi S hS e).mpr e.property⟩
      invFun := fun e => ⟨phi.edge.symm e,(Aut.z95 G phi S hS (phi.edge.symm e)).mp
        (by simpa only [Equiv.apply_symm_apply] using e.property)⟩
      left_inv := fun e => Subtype.ext (phi.edge.symm_apply_apply e)
      right_inv := fun e => Subtype.ext (phi.edge.apply_symm_apply e) }
  preserves e := by
    apply Sym2.map.injective Subtype.val_injective
    rw [G.z107,Sym2.map_map]
    change G.ends (phi.edge e.val)=Sym2.map (fun x : S => phi.vertex x.val) ((G.induce S).ends e)
    calc
      G.ends (phi.edge e.val)=Sym2.map phi.vertex (G.ends e.val) := phi.preserves e.val
      _=Sym2.map phi.vertex (Sym2.map (Subtype.val : S → V) ((G.induce S).ends e)) :=
        congrArg (Sym2.map phi.vertex) (G.z107 S e).symm
      _=_ := Sym2.map_map _
lemma Aut.z476 (phi : G.Aut) (S : Set V)
    (hS : ∀ x, phi.vertex x∈S ↔ x∈S) (o : V) :
    phi.vertex '' G.domainComponent S o=G.domainComponent S (phi.vertex o) := by
  change phi.vertex '' G.cluster (G.z4 S) o=G.cluster (G.z4 S) (phi.vertex o)
  rw [Aut.cluster_image,Aut.z563 G phi S hS]
lemma z127 (S : Set V) {o x : V} (hx : x∈G.domainComponent S o) :
    G.domainComponent S x=G.domainComponent S o := by
  ext y
  exact ⟨fun h => hx.trans h,fun h => hx.symm.trans h⟩
lemma Aut.z349 (phi : G.Aut) (S : Set V)
    (hS : ∀ x, phi.vertex x∈S ↔ x∈S) (o x : V)
    (hx : x∈G.domainComponent S o) (hpx : phi.vertex x∈G.domainComponent S o) :
    ∀ y, phi.vertex y∈G.domainComponent S o ↔ y∈G.domainComponent S o := by
  have heq : phi.vertex '' G.domainComponent S o=G.domainComponent S o := calc
    phi.vertex '' G.domainComponent S o=phi.vertex '' G.domainComponent S x :=
      congrArg (Set.image phi.vertex) (G.z127 S hx).symm
    _=G.domainComponent S (phi.vertex x) := Aut.z476 G phi S hS x
    _=G.domainComponent S o := G.z127 S hpx
  intro y
  constructor
  · intro hy
    have him : phi.vertex y∈phi.vertex '' G.domainComponent S o := by rwa [heq]
    obtain ⟨z,hz,hzy⟩ := him
    exact phi.vertex.injective hzy ▸ hz
  · intro hy
    rw [←heq]
    exact ⟨y,hy,rfl⟩
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical
namespace CriticalPercolation.z2
variable {V E Λ : Type*} (G : z2 V E) [Group Λ] [MulAction Λ V] [MulAction Λ E]
def domainPreserver (C : Set V) : Subgroup Λ where
  carrier := {g | ∀ x, g • x∈C ↔ x∈C}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro g h hg hh x
    rw [mul_smul,hg,hh]
  inv_mem' := by
    intro g hg x
    simpa only [smul_inv_smul] using (hg (g⁻¹ • x)).symm
abbrev restrictedVertexAction (C : Set V) (L : Subgroup Λ) (hL : L≤domainPreserver C) :
    MulAction L C where
  smul g x := ⟨(g : Λ) • x.val,(hL g.property x.val).mpr x.property⟩
  one_smul x := Subtype.ext (one_smul Λ x.val)
  mul_smul g h x := Subtype.ext (mul_smul (g : Λ) (h : Λ) x.val)
abbrev restrictedEdgeAction (ha : G.PreservesEnds (Λ := Λ))
    (C : Set V) (L : Subgroup Λ) (hL : L≤domainPreserver C) :
    MulAction L (G.z4 C) where
  smul g e := ⟨(g : Λ) • e.val,
    (Aut.z95 G (G.smulAut ha g.val) C (hL g.property) e.val).mpr e.property⟩
  one_smul e := Subtype.ext (one_smul Λ e.val)
  mul_smul g h e := Subtype.ext (mul_smul (g : Λ) (h : Λ) e.val)
lemma z372 (ha : G.PreservesEnds (Λ := Λ))
    (C : Set V) (L : Subgroup Λ) (hL : L≤domainPreserver C) :
    let _ := restrictedVertexAction C L hL
    let _ := G.restrictedEdgeAction ha C L hL
    (G.induce C).PreservesEnds (Λ := L) := by
  intro _ _ g e
  exact (Aut.restrict G (G.smulAut ha g.val) C (hL g.property)).preserves e
lemma z369 {N : Type*} [Group N]
    (ρ : Λ →* N) (hker : ∀ v : V, (MulAction.orbit ρ.ker v).Finite)
    (C : Set V) (L : Subgroup Λ) (hL : L≤domainPreserver C) :
    let _ := restrictedVertexAction C L hL
    ∀ v : C, (MulAction.orbit (ρ.comp L.subtype).ker v).Finite := by
  intro _ v
  apply (Set.Finite.preimage Subtype.val_injective.injOn (hker v.val)).subset
  rintro w ⟨g,hg⟩
  refine ⟨⟨(g.val : Λ),g.property⟩,?_⟩
  exact congrArg Subtype.val hg
lemma z267 {N : Type*} [Group N]
    (ρ : Λ →* N)
    (hstab : ∀ v : V, ((MulAction.stabilizer Λ v).map ρ : Set N).Finite)
    (C : Set V) (L : Subgroup Λ) (hL : L≤domainPreserver C) :
    let _ := restrictedVertexAction C L hL
    ∀ v : C, ((MulAction.stabilizer L v).map (ρ.comp L.subtype) : Set N).Finite := by
  intro _ v
  apply (hstab v.val).subset
  rintro n ⟨g,hg,rfl⟩
  exact ⟨g.val,congrArg Subtype.val hg,rfl⟩
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical
namespace CriticalPercolation.z2
variable {V E Λ T : Type*} (G : z2 V E)
  [Group Λ] [Group T] [MulAction Λ V] [MulAction Λ E]
def componentKernel (a : Λ →* T) (C : Set V) : Subgroup Λ :=
  a.ker ⊓ domainPreserver C
lemma z41 (a : Λ →* T) (C : Set V) :
    componentKernel a C≤domainPreserver C := inf_le_right
lemma z335
    (ha : G.PreservesEnds (Λ := Λ)) (a : Λ →* T) (z : V → T)
    (hz : ∀ g v, z (g • v)=a g*z v)
    (Q : Set T) (o : V) (x y : G.domainComponent (z ⁻¹' Q) o)
    (horbit : y.val∈MulAction.orbit Λ x.val) (hlevel : z y.val=z x.val) :
    ∃ g : componentKernel a (G.domainComponent (z ⁻¹' Q) o),
      (g.val : Λ) • x.val=y.val := by
  obtain ⟨g,hg⟩ := EquivariantCoordinates.z173 a z hz x.val y.val horbit hlevel
  change g.val • x.val=y.val at hg
  have hS : ∀ v, (G.smulAut ha g.val).vertex v∈z ⁻¹' Q ↔ v∈z ⁻¹' Q := by
    intro v
    change z (g.val • v)∈Q ↔ z v∈Q
    rw [hz,g.property,one_mul]
  have hp := Aut.z349 G (G.smulAut ha g.val) (z ⁻¹' Q)
    hS o x.val x.property (by change g.val • x.val∈_; rw [hg]; exact y.property)
  exact ⟨⟨g.val,g.property,hp⟩,hg⟩
theorem z244
    (ha : G.PreservesEnds (Λ := Λ))
    (R : Set V) (hR : R.Finite) (hcover : ∀ v, ∃ s∈R, v∈MulAction.orbit Λ s)
    (a : Λ →* T) (z : V → T) (hz : ∀ g v, z (g • v)=a g*z v)
    (Q : Set T) (hQ : Q.Finite) (o : V) (ho : z o∈Q) :
    let C := G.domainComponent (z ⁻¹' Q) o
    let L := componentKernel a C
    let _ := restrictedVertexAction C L (z41 a C)
    ∃ S : Set C, S.Finite ∧ ∀ v : C, ∃ s∈S, v∈MulAction.orbit L s := by
  let C := G.domainComponent (z ⁻¹' Q) o
  let L := componentKernel a C
  let _ := restrictedVertexAction C L (z41 a C)
  let I : Set (V×T) := {q | q.1∈R ∧ q.2∈Q ∧ ∃ x : C,
    x.val∈MulAction.orbit Λ q.1 ∧ z x.val=q.2}
  have hI : I.Finite := (hR.prod hQ).subset (fun _ h => ⟨h.1,h.2.1⟩)
  let _ := hI.to_subtype
  have hex : ∀ q : I, ∃ x : C, x.val∈MulAction.orbit Λ q.val.1 ∧ z x.val=q.val.2 :=
    fun q => q.property.2.2
  choose r hr using hex
  refine ⟨Set.range r,Set.finite_range r,?_⟩
  intro y
  obtain ⟨s,hs,hys⟩ := hcover y.val
  have hyQ : z y.val∈Q := G.z431 ho y.property
  let q : I := ⟨(s,z y.val),hs,hyQ,y,hys,rfl⟩
  refine ⟨r q,⟨q,rfl⟩,?_⟩
  have hyorbit : y.val∈MulAction.orbit Λ (r q).val := by
    rw [MulAction.orbit_eq_iff.mpr (hr q).1]
    exact hys
  obtain ⟨g,hg⟩ := G.z335 ha a z hz Q o (r q) y hyorbit (hr q).2.symm
  exact ⟨g,Subtype.ext hg⟩
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical
namespace CriticalPercolation.z2
variable {V Λ N T : Type*} [Group Λ] [Group N] [Group T] [MulAction Λ V]
lemma z291 (f : Λ →* N)
    (hf : ∀ v : V, (MulAction.orbit f.ker v).Finite) :
    ∀ v : V, (MulAction.orbit f.rangeRestrict.ker v).Finite := by
  intro v
  apply (hf v).subset
  rintro w ⟨g,hg⟩
  have hgm : f g.val=1 := congrArg Subtype.val g.property
  exact ⟨⟨g.val,hgm⟩,hg⟩
lemma z198 (f : Λ →* N)
    (hf : ∀ v : V, ((MulAction.stabilizer Λ v).map f : Set N).Finite) :
    ∀ v : V, ((MulAction.stabilizer Λ v).map f.rangeRestrict : Set f.range).Finite := by
  intro v
  apply (Set.Finite.preimage Subtype.val_injective.injOn (hf v)).subset
  rintro n ⟨g,hg,rfl⟩
  exact ⟨g,hg,rfl⟩
lemma z259 (ρ : Λ →* N) (φ : N →* T) (C : Set V) :
    (ρ.comp (componentKernel (φ.comp ρ) C).subtype).range≤φ.ker := by
  rintro n ⟨g,rfl⟩
  exact g.property.1
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical
namespace CriticalPercolation
universe u
inductive AlgebraicDescent : (N : Type u) → [Group N] → Prop
  | finite (N : Type u) [Group N] [Finite N] : AlgebraicDescent N
  | cyclic (N : Type u) [Group N]
      (φ : N →* Multiplicative ℤ) (hφ : Surjective φ)
      (hf : (φ.ker : Set N).Finite) : AlgebraicDescent N
  | plane (N : Type u) [Group N]
      (φ : N →* Multiplicative (ℤ×ℤ)) (hφ : Surjective φ)
      (lower : ∀ J : Subgroup N, J≤φ.ker → AlgebraicDescent J) : AlgebraicDescent N
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set
open scoped Classical
namespace CriticalPercolation
def integerPairBox (k : ℕ) : Set (Multiplicative (ℤ×ℤ)) :=
  {t | |(t.toAdd.1 : ℝ)|≤(k:ℝ) ∧ |(t.toAdd.2 : ℝ)|≤(k:ℝ)}
lemma z467 (k : ℕ) : (integerPairBox k).Finite := by
  have hh := ((Set.finite_Icc (-(k:ℤ)) (k:ℤ)).prod
    (Set.finite_Icc (-(k:ℤ)) (k:ℤ))).image (Multiplicative.ofAdd : ℤ×ℤ → _)
  apply hh.subset
  intro t ht
  refine ⟨t.toAdd,?_,rfl⟩
  have h₁ := abs_le.mp ht.1
  have h₂ := abs_le.mp ht.2
  exact ⟨⟨by exact_mod_cast h₁.1,by exact_mod_cast h₁.2⟩,
    ⟨by exact_mod_cast h₂.1,by exact_mod_cast h₂.2⟩⟩
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.z2
universe groupUniverse vertexUniverse edgeUniverse actionUniverse
theorem z154 [Fact (∀ V E : Type, CriticalPercolationLeaf.FiniteSizeCriterion V E)] {N : Type} [Group N]
    (hN : AlgebraicDescent N) :
    ∀ {V : Type} {E : Type} {Λ : Type}
      [Group Λ] [MulAction Λ V] [MulAction Λ E]
      (G : z2 V E),
      G.z7.Connected → G.LocallyFinite → G.SubexponentialGrowth →
      G.PreservesEnds (Λ := Λ) →
      ∀ (S : Set V), S.Finite → (∀ v, ∃ s∈S, v∈MulAction.orbit Λ s) →
      ∀ (ρ : Λ →* N), Surjective ρ →
      (∀ v : V, (MulAction.orbit ρ.ker v).Finite) →
      (∀ v : V, ((MulAction.stabilizer Λ v).map ρ : Set N).Finite) →
      G.z3<1 → G.law G.z3 G.z12=0 := by
  induction hN with
  | @finite N _ _ =>
    intro V E Λ _ _ _ G _ _ _ _ S hS hcover ρ _ hker _ _
    have hV := EquivariantCoordinates.z144 ρ hker S hS hcover
    have hempty : G.z12=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨v,hv⟩
      exact hv (hV.subset (Set.subset_univ _))
    rw [hempty,measure_empty]
  | @cyclic N _ φ hφ hf =>
    intro V E Λ _ _ _ G _ hl _ ha S hS hcover ρ hρ hker hstab hpc
    have heq := G.z205 hl ha S hS hcover ρ hρ φ hφ hf hker hstab
    exact False.elim ((ne_of_lt hpc) heq)
  | @plane N _ φ hφ lower ih =>
    intro V E Λ _ _ _ G hc hl hg ha S hS hcover ρ hρ hker hstab hpc
    let _ := hc.nonempty
    let _ := G.z53 hc hl
    let _ := G.z113 hc hl
    obtain ⟨z,hzonto,hz⟩ := z193 ρ hρ φ hφ hstab
    apply G.z136 hc hl ha S hS hcover hg hpc
      (fun g => (φ (ρ g)).toAdd) z hzonto hz
    by_contra hbad
    obtain ⟨k,o,ho,hcrit,hpos⟩ := G.z213
      (fun v => ((z v).1 : ℝ)) (fun v => ((z v).2 : ℝ)) (by simpa only [Int.cast_abs] using hbad)
    let zM : V → Multiplicative (ℤ×ℤ) := fun v => Multiplicative.ofAdd (z v)
    let Q := integerPairBox k
    let C := G.domainComponent (zM ⁻¹' Q) o
    let L := componentKernel (φ.comp ρ) C
    let H := G.induce C
    let _ := restrictedVertexAction C L (z41 (φ.comp ρ) C)
    let _ := G.restrictedEdgeAction ha C L (z41 (φ.comp ρ) C)
    have hzm : ∀ g v, zM (g • v)=(φ.comp ρ) g*zM v :=
      fun g v => congrArg Multiplicative.ofAdd (hz g v)
    obtain ⟨R,hR,hRcover⟩ := G.z244 ha S hS hcover
      (φ.comp ρ) zM hzm Q (z467 k) o ho
    let f := ρ.comp L.subtype
    have hfker : ∀ v : C, (MulAction.orbit f.rangeRestrict.ker v).Finite :=
      z291 f
        (z369 ρ hker C L (z41 (φ.comp ρ) C))
    have hfstab : ∀ v : C,
        ((MulAction.stabilizer L v).map f.rangeRestrict : Set f.range).Finite :=
      z198 f
        (z267 ρ hstab C L (z41 (φ.comp ρ) C))
    have hle : f.range≤φ.ker := z259 ρ φ C
    have hnull := ih f.range hle H
      (G.z351 (zM ⁻¹' Q) o) (G.z263 hl C)
      (G.z477 hl hg C)
      (G.z372 ha C L (z41 (φ.comp ρ) C))
      R hR hRcover f.rangeRestrict f.rangeRestrict_surjective hfker hfstab
      (by change H.z3=G.z3 at hcrit
          rw [hcrit]; exact hpc)
    exact (ne_of_gt hpos) hnull
end CriticalPercolation.z2
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement
namespace CriticalPercolation
variable {G : Type*} [Group G]
private lemma z87 {z : G} (hz : z∈Subgroup.center G) (a : G) :
    a*z*a⁻¹=z := by
  rw [Subgroup.mem_center_iff.mp hz a,mul_assoc,mul_inv_cancel,mul_one]
private lemma z487 {a b : G} (h : ⁅a,b⁆∈Subgroup.center G) :
    ⁅a⁻¹,b⁆=⁅a,b⁆⁻¹ := by
  rw [commutatorElement_inv_left,←commutatorElement_inv]
  simpa using z87 ((Subgroup.center G).inv_mem h) a⁻¹
private lemma z444 {a b : G} (h : ⁅a,b⁆∈Subgroup.center G) :
    ⁅a,b⁻¹⁆=⁅a,b⁆⁻¹ := by
  rw [commutatorElement_inv_right,←commutatorElement_inv]
  simpa using z87 ((Subgroup.center G).inv_mem h) b⁻¹
theorem z277 (S T : Set G)
    (hc : ⁅Subgroup.closure S,Subgroup.closure T⁆≤Subgroup.center G) :
    ⁅Subgroup.closure S,Subgroup.closure T⁆=
      Subgroup.closure (Set.image2 (fun a b : G => ⁅a,b⁆) S T) := by
  let K := Subgroup.closure (Set.image2 (fun a b : G => ⁅a,b⁆) S T)
  have hz {a b : G} (ha : a∈Subgroup.closure S) (hb : b∈Subgroup.closure T) :
      ⁅a,b⁆∈Subgroup.center G := hc (Subgroup.commutator_mem_commutator ha hb)
  apply le_antisymm
  · apply Subgroup.commutator_le.mpr
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem a ha =>
      intro b hb
      induction hb using Subgroup.closure_induction with
      | mem b hb => exact Subgroup.subset_closure (Set.mem_image2.mpr ⟨a,ha,b,hb,rfl⟩)
      | one => simp
      | mul b c hb hc' ihb ihc =>
        rw [commutatorElement_mul_right_eq_mul_conj]
        have he : ⁅a,b⁆*b*⁅a,c⁆*b⁻¹=⁅a,b⁆*(b*⁅a,c⁆*b⁻¹) := by group
        rw [he,z87 (hz (Subgroup.subset_closure ha) hc') b]
        exact K.mul_mem ihb ihc
      | inv b hb ih =>
        rw [z444 (hz (Subgroup.subset_closure ha) hb)]
        exact K.inv_mem ih
    | one => intro b _; simp
    | mul a c ha hc' iha ihc =>
      intro b hb
      rw [commutatorElement_mul_left_eq_conj_mul,
        z87 (hz hc' hb) a]
      exact K.mul_mem (ihc b hb) (iha b hb)
    | inv a ha ih =>
      intro b hb
      rw [z487 (hz ha hb)]
      exact K.inv_mem (ih b hb)
  · apply (Subgroup.closure_le _).mpr
    rintro z ⟨a,ha,b,hb,rfl⟩
    exact Subgroup.commutator_mem_commutator (Subgroup.subset_closure ha)
      (Subgroup.subset_closure hb)
theorem z229 (H J : Subgroup G) (hH : H.FG) (hJ : J.FG)
    (hc : ⁅H,J⁆≤Subgroup.center G) : ⁅H,J⁆.FG := by
  obtain ⟨S,hS,hfinS⟩ := Subgroup.fg_iff H |>.mp hH
  obtain ⟨T,hT,hfinT⟩ := Subgroup.fg_iff J |>.mp hJ
  apply (Subgroup.fg_iff _).mpr
  refine ⟨Set.image2 (fun a b : G => ⁅a,b⁆) S T,?_,hfinS.image2 _ hfinT⟩
  rw [←z277 S T (by rwa [hS,hT]),hS,hT]
theorem z414 [Group.FG G]
    (hc : commutator G≤Subgroup.center G) : Group.FG (commutator G) := by
  apply (Group.fg_iff_subgroup_fg _).mpr
  exact z229 ⊤ ⊤ (Group.fg_def.mp inferInstance)
    (Group.fg_def.mp inferInstance) hc
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement
namespace CriticalPercolation
variable {G Q : Type*} [Group G] [Group Q]
lemma z171 [Group.FG Q] {H : Type*} [Group H]
    (f : H →* Q) (hf : Surjective f) :
    ∃ S : Set H, S.Finite ∧ (Subgroup.closure S).map f=⊤ := by
  obtain ⟨T,hT,hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG Q)
  choose s hs using hf
  refine ⟨s '' T,hfin.image s,?_⟩
  rw [MonoidHom.map_closure,Set.image_image]
  have he : (fun x => f (s x))=id := funext hs
  rw [he,Set.image_id,hT]
theorem z67 [Group.FG G] [Group.FG Q]
    (H : Subgroup G) (f : H →* Q) (hf : Surjective f)
    (hker : f.ker.map H.subtype≤Subgroup.center G)
    (hcentral : ⁅(⊤ : Subgroup G),H⁆≤Subgroup.center G) :
    ⁅(⊤ : Subgroup G),H⁆.FG := by
  obtain ⟨S,hS,himage⟩ := z171 f hf
  let L := Subgroup.closure S
  let M := L.map H.subtype
  have hM : M.FG := by
    apply (Subgroup.fg_iff M).mpr
    refine ⟨H.subtype '' S,?_,hS.image H.subtype⟩
    exact (MonoidHom.map_closure H.subtype S).symm
  have hMH : M≤H := by
    rintro x ⟨y,_,rfl⟩
    exact y.property
  suffices he : ⁅(⊤ : Subgroup G),H⁆=⁅(⊤ : Subgroup G),M⁆ by
    rw [he]
    exact z229 ⊤ M (Group.fg_def.mp inferInstance) hM
      ((Subgroup.commutator_mono le_rfl hMH).trans hcentral)
  apply le_antisymm
  · apply Subgroup.commutator_le.mpr
    intro g _ h hh
    have him : f ⟨h,hh⟩∈L.map f := by rw [himage]; trivial
    obtain ⟨l,hl,he⟩ := him
    let z : H := l⁻¹*⟨h,hh⟩
    have hzker : z∈f.ker := by
      change f (l⁻¹*⟨h,hh⟩)=1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    have hz : (z:G)∈Subgroup.center G := hker ⟨z,hzker,rfl⟩
    have hgz : ⁅g,(z:G)⁆=1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz g)
    have hdecomp : h=(l:G)*(z:G) := by simp [z]
    rw [hdecomp,commutatorElement_mul_right_eq_mul_conj,hgz]
    simpa using (Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup G))
      (H₂ := M) (by trivial) (show (l:G)∈M from ⟨l,hl,rfl⟩) : ⁅g,(l:G)⁆∈⁅⊤,M⁆)
  · exact Subgroup.commutator_mono le_rfl hMH
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement
namespace CriticalPercolation
variable (G : Type*) [Group G]
def lowerFactor (n : ℕ) : Subgroup (G ⧸ (⊤ : Subgroup G).lowerCentralSeries (n+1)) :=
  ((⊤ : Subgroup G).lowerCentralSeries n).map
    (QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (n+1)))
lemma z22 (n : ℕ) : lowerFactor G n≤
    Subgroup.center (G ⧸ (⊤ : Subgroup G).lowerCentralSeries (n+1)) := by
  apply Subgroup.commutator_top_right_eq_bot_iff_le_center.mp
  let f := QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (n+1))
  have hf : (⊤ : Subgroup G).map f=⊤ :=
    Subgroup.map_top_of_surjective f QuotientGroup.mk_surjective
  change ⁅((⊤ : Subgroup G).lowerCentralSeries n).map f,⊤⁆=⊥
  rw [←hf,←Subgroup.map_commutator,←Subgroup.lowerCentralSeries_succ]
  apply (Subgroup.map_eq_bot_iff _).mpr
  rw [QuotientGroup.ker_mk']
theorem lowerFactor_fg [Group.FG G] (n : ℕ) : Group.FG (lowerFactor G n) := by
  induction n with
  | zero =>
    unfold lowerFactor
    rw [Subgroup.lowerCentralSeries_zero,←MonoidHom.range_eq_map]
    infer_instance
  | succ n ih =>
    let N := (⊤ : Subgroup G).lowerCentralSeries (n+1)
    let M := (⊤ : Subgroup G).lowerCentralSeries (n+2)
    let π := QuotientGroup.mk' M
    let σ := QuotientGroup.mk' N
    have hMN : M≤N := (⊤ : Subgroup G).lowerCentralSeries_antitone (by omega)
    let q : (G ⧸ M) →* (G ⧸ N) := QuotientGroup.lift M σ (by
      rw [QuotientGroup.ker_mk']; exact hMN)
    have hq (g : G) : q (π g)=σ g := rfl
    let H := ((⊤ : Subgroup G).lowerCentralSeries n).map π
    let f : H →* lowerFactor G n := {
      toFun := fun h => ⟨q h.val,by
        obtain ⟨g,hg,he⟩ := h.property
        exact ⟨g,hg,by change σ g=q h.val; rw [←he,hq]⟩⟩
      map_one' := by apply Subtype.ext; exact q.map_one
      map_mul' := by intros; apply Subtype.ext; exact q.map_mul _ _ }
    have hf : Surjective f := by
      rintro ⟨x,g,hg,rfl⟩
      exact ⟨⟨π g,⟨g,hg,rfl⟩⟩,rfl⟩
    have hker : f.ker.map H.subtype≤Subgroup.center (G ⧸ M) := by
      rintro x ⟨h,hh,rfl⟩
      obtain ⟨g,hg,he⟩ := h.property
      apply z22 G (n+1)
      refine ⟨g,?_,he⟩
      have heq : σ g=1 := by
        rw [←hq,he]
        exact congrArg Subtype.val hh
      change g∈N
      rw [←QuotientGroup.ker_mk' N]
      exact heq
    have hcomm : ⁅(⊤ : Subgroup (G ⧸ M)),H⁆=lowerFactor G (n+1) := by
      have hπ : (⊤ : Subgroup G).map π=⊤ :=
        Subgroup.map_top_of_surjective π QuotientGroup.mk_surjective
      change ⁅⊤,((⊤ : Subgroup G).lowerCentralSeries n).map π⁆=
        ((⊤ : Subgroup G).lowerCentralSeries (n+1)).map π
      rw [←hπ,←Subgroup.map_commutator,Subgroup.commutator_comm,
        ←Subgroup.lowerCentralSeries_succ]
    let _ := ih
    have hfg := z67 H f hf hker
      (hcomm ▸ z22 G (n+1))
    apply (Group.fg_iff_subgroup_fg _).mpr
    rwa [hcomm] at hfg
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical
namespace CriticalPercolation
theorem z464 {G Q : Type*} [Group G] [Group Q] [Group.FG Q]
    (f : G →* Q) (hf : Surjective f) [Group.FG f.ker] : Group.FG G := by
  obtain ⟨S,hS,himage⟩ := z171 f hf
  obtain ⟨T,hT,hfinT⟩ := Group.fg_iff.mp (inferInstance : Group.FG f.ker)
  let U := S ∪ f.ker.subtype '' T
  let L := Subgroup.closure U
  have hSle : Subgroup.closure S≤L := Subgroup.closure_mono Set.subset_union_left
  have hker : f.ker≤L := by
    have he : (Subgroup.closure T).map f.ker.subtype=f.ker := by
      rw [hT,←MonoidHom.range_eq_map,Subgroup.subtype_range]
    rw [←he,MonoidHom.map_closure]
    exact Subgroup.closure_mono Set.subset_union_right
  have htop : L=⊤ := by
    apply top_unique
    intro g _
    have hg : f g∈(Subgroup.closure S).map f := by rw [himage]; trivial
    obtain ⟨a,ha,he⟩ := hg
    have hz : a⁻¹*g∈f.ker := by
      change f (a⁻¹*g)=1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    simpa using L.mul_mem (hSle ha) (hker hz)
  exact Group.fg_iff.mpr ⟨U,htop,hS.union (hfinT.image _)⟩
theorem z311 {A : Type*} [CommGroup A] [Group.FG A]
    (H : Subgroup A) : Group.FG H := by
  let K := H.toAddSubgroup.toIntSubmodule
  let _ : Module.Finite ℤ (Additive A) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  let _ : AddGroup.FG K := Module.Finite.iff_addGroup_fg.mp inferInstance
  let e : Multiplicative K ≃* H := {
    toFun := fun a => ⟨a.toAdd.val.toMul,a.toAdd.property⟩
    invFun := fun h => Multiplicative.ofAdd ⟨Additive.ofMul h.val,h.property⟩
    left_inv := by intro a; rfl
    right_inv := by intro h; rfl
    map_mul' := by intros; rfl }
  exact Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical
namespace CriticalPercolation
theorem z470 (G : Type*) [Group G] [Group.FG G]
    [Group.IsNilpotent G] (J : Subgroup G) : Group.FG J := by
  obtain ⟨c,hc⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp
    (inferInstance : Group.IsNilpotent G)
  let L := fun n => J ⊓ (⊤ : Subgroup G).lowerCentralSeries n
  have step (n : ℕ) (hn : Group.FG (L (n+1))) : Group.FG (L n) := by
    let F := lowerFactor G n
    let _ : CommGroup F := {
      (inferInstance : Group F) with
      mul_comm := fun a b => Subtype.ext
        (Subgroup.mem_center_iff.mp (z22 G n b.property) a.val) }
    let _ : Group.FG F := lowerFactor_fg G n
    let q := QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (n+1))
    let f : L n →* F := {
      toFun := fun x => ⟨q x.val,⟨x.val,x.property.2,rfl⟩⟩
      map_one' := by apply Subtype.ext; exact q.map_one
      map_mul' := by intros; apply Subtype.ext; exact q.map_mul _ _ }
    let _ : Group.FG f.range := z311 f.range
    let _ : Group.FG (L (n+1)) := hn
    have hemem (x : L n) : x∈f.ker ↔ x.val∈(⊤ : Subgroup G).lowerCentralSeries (n+1) := by
      change f x=1 ↔ _
      rw [Subtype.ext_iff]
      change q x.val=1 ↔ _
      exact QuotientGroup.eq_one_iff _
    let e : L (n+1) ≃* f.ker := {
      toFun := fun x => ⟨⟨x.val,⟨x.property.1,
        (⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.le_succ n) x.property.2⟩⟩,
        (hemem _).mpr x.property.2⟩
      invFun := fun x => ⟨x.val.val,⟨x.val.property.1,(hemem _).mp x.property⟩⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_mul' := by intros; rfl }
    let _ : Group.FG f.ker := Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
    have he : f.rangeRestrict.ker=f.ker := by
      ext x
      change f.rangeRestrict x=1 ↔ f x=1
      exact Subtype.ext_iff
    let _ : Group.FG f.rangeRestrict.ker := he.symm ▸ (inferInstance : Group.FG f.ker)
    exact z464 f.rangeRestrict f.rangeRestrict_surjective
  have base : Group.FG (L c) := by
    have he : L c=⊥ := by simp [L,hc]
    rw [he]
    infer_instance
  have hall : ∀ k, Group.FG (L (c-k)) := by
    intro k
    induction k with
    | zero => simpa using base
    | succ k ih =>
      by_cases hk : k<c
      · have he : c-k=(c-(k+1))+1 := by omega
        rw [he] at ih
        exact step _ ih
      · simpa [Nat.sub_eq_zero_of_le (by omega : c≤k),
          Nat.sub_eq_zero_of_le (by omega : c≤k+1)] using ih
  have h := hall c
  simpa [L] using h
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement
namespace CriticalPercolation
variable {G Q : Type*} [Group G] [Group Q]
theorem z52 [Group.FG G] [Finite Q]
    (H : Subgroup G) (f : H →* Q) (hf : Surjective f)
    (hker : f.ker.map H.subtype≤Subgroup.center G)
    (hc : ⁅(⊤ : Subgroup G),H⁆≤Subgroup.center G) :
    ((⁅(⊤ : Subgroup G),H⁆ : Subgroup G) : Set G).Finite := by
  let C := ⁅(⊤ : Subgroup G),H⁆
  let _ : CommGroup C := {
    (inferInstance : Group C) with
    mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hc b.property) a.val) }
  let _ : Group.FG C := (Group.fg_iff_subgroup_fg C).mpr
    (z67 H f hf hker hc)
  have hpair (a : G) (b : H) : IsOfFinOrder (⁅a,(b:G)⁆) := by
    let t : H →* G := {
      toFun := fun b => ⁅a,(b:G)⁆
      map_one' := by simp
      map_mul' := by
        intro b d
        change ⁅a,(b:G)*(d:G)⁆=⁅a,(b:G)⁆*⁅a,(d:G)⁆
        rw [commutatorElement_mul_right_eq_mul_conj]
        have hd := hc (Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup G))
          (by trivial) d.property : ⁅a,(d:G)⁆∈C)
        calc
          ⁅a,(b:G)⁆*(b:G)*⁅a,(d:G)⁆*(b:G)⁻¹ =
            ⁅a,(b:G)⁆*((b:G)*⁅a,(d:G)⁆)*(b:G)⁻¹ := by group
          _ = ⁅a,(b:G)⁆*(⁅a,(d:G)⁆*(b:G))*(b:G)⁻¹ := by
            rw [Subgroup.mem_center_iff.mp hd (b:G)]
          _ = _ := by group }
    obtain ⟨m,hm,he⟩ := (isOfFinOrder_of_finite (f b)).exists_pow_eq_one
    have hb : b^m∈f.ker := by change f (b^m)=1; rwa [map_pow]
    have hz : ((b^m:H):G)∈Subgroup.center G := hker ⟨b^m,hb,rfl⟩
    have heq : t (b^m)=1 := commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp hz a)
    rw [map_pow] at heq
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m,hm,heq⟩
  have ht : C≤(CommGroup.torsion C).map C.subtype := by
    apply Subgroup.commutator_le.mpr
    intro a _ b hb
    let c : C := ⟨⁅a,b⁆,Subgroup.commutator_mem_commutator (by trivial) hb⟩
    refine ⟨c,?_,rfl⟩
    change IsOfFinOrder c
    obtain ⟨m,hm,he⟩ := (hpair a ⟨b,hb⟩).exists_pow_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m,hm,Subtype.ext he⟩
  let _ : Finite C := CommGroup.finite_of_fg_isMulTorsion C (fun c => by
    obtain ⟨d,hd,he⟩ := ht c.property
    have hcd : d=c := Subtype.ext he
    change IsOfFinOrder d at hd
    exact hcd ▸ hd)
  exact Set.toFinite _
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement
namespace CriticalPercolation
variable (G : Type*) [Group G]
theorem z553 [Group.FG G] [Finite (lowerFactor G 0)] (n : ℕ) :
    Finite (lowerFactor G n) := by
  induction n with
  | zero => infer_instance
  | succ n ih =>
    let N := (⊤ : Subgroup G).lowerCentralSeries (n+1)
    let M := (⊤ : Subgroup G).lowerCentralSeries (n+2)
    let π := QuotientGroup.mk' M
    let σ := QuotientGroup.mk' N
    have hMN : M≤N := (⊤ : Subgroup G).lowerCentralSeries_antitone (by omega)
    let q : (G ⧸ M) →* (G ⧸ N) := QuotientGroup.lift M σ (by
      rw [QuotientGroup.ker_mk']; exact hMN)
    have hq (g : G) : q (π g)=σ g := rfl
    let H := ((⊤ : Subgroup G).lowerCentralSeries n).map π
    let f : H →* lowerFactor G n := {
      toFun := fun h => ⟨q h.val,by
        obtain ⟨g,hg,he⟩ := h.property
        exact ⟨g,hg,by change σ g=q h.val; rw [←he,hq]⟩⟩
      map_one' := by apply Subtype.ext; exact q.map_one
      map_mul' := by intros; apply Subtype.ext; exact q.map_mul _ _ }
    have hf : Surjective f := by
      rintro ⟨x,g,hg,rfl⟩
      exact ⟨⟨π g,⟨g,hg,rfl⟩⟩,rfl⟩
    have hker : f.ker.map H.subtype≤Subgroup.center (G ⧸ M) := by
      rintro x ⟨h,hh,rfl⟩
      obtain ⟨g,hg,he⟩ := h.property
      apply z22 G (n+1)
      refine ⟨g,?_,he⟩
      have heq : σ g=1 := by
        rw [←hq,he]
        exact congrArg Subtype.val hh
      change g∈N
      rw [←QuotientGroup.ker_mk' N]
      exact heq
    have hcomm : ⁅(⊤ : Subgroup (G ⧸ M)),H⁆=lowerFactor G (n+1) := by
      have hπ : (⊤ : Subgroup G).map π=⊤ :=
        Subgroup.map_top_of_surjective π QuotientGroup.mk_surjective
      change ⁅⊤,((⊤ : Subgroup G).lowerCentralSeries n).map π⁆=
        ((⊤ : Subgroup G).lowerCentralSeries (n+1)).map π
      rw [←hπ,←Subgroup.map_commutator,Subgroup.commutator_comm,
        ←Subgroup.lowerCentralSeries_succ]
    let _ := ih
    have hfin := z52 H f hf hker
      (hcomm ▸ z22 G (n+1))
    rw [hcomm] at hfin
    exact hfin.to_subtype
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical
namespace CriticalPercolation
theorem z147 (G : Type*) [Group G]
    [Group.IsNilpotent G] (hfin : ∀ n, Finite (lowerFactor G n)) : Finite G := by
  obtain ⟨c,hc⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp
    (inferInstance : Group.IsNilpotent G)
  let L := fun n => (⊤ : Subgroup G).lowerCentralSeries n
  have step (n : ℕ) (hn : Finite (L (n+1))) : Finite (L n) := by
    let F := lowerFactor G n
    let _ : Finite F := hfin n
    let q := QuotientGroup.mk' (L (n+1))
    let f : L n →* F := {
      toFun := fun x => ⟨q x.val,⟨x.val,x.property,rfl⟩⟩
      map_one' := by apply Subtype.ext; exact q.map_one
      map_mul' := by intros; apply Subtype.ext; exact q.map_mul _ _ }
    have hemem (x : L n) : x∈f.ker ↔ x.val∈L (n+1) := by
      change f x=1 ↔ _
      rw [Subtype.ext_iff]
      change q x.val=1 ↔ _
      exact QuotientGroup.eq_one_iff _
    let e : L (n+1) ≃ f.ker := {
      toFun := fun x => ⟨⟨x.val,
        (⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.le_succ n) x.property⟩,
        (hemem _).mpr x.property⟩
      invFun := fun x => ⟨x.val.val,(hemem _).mp x.property⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
    let _ : Finite f.ker := Finite.of_equiv _ e
    exact f.finite_iff_finite_ker_range.mpr ⟨inferInstance,inferInstance⟩
  have base : Finite (L c) := by
    change Finite ((⊤ : Subgroup G).lowerCentralSeries c)
    rw [hc]
    infer_instance
  have hall : ∀ k, Finite (L (c-k)) := by
    intro k
    induction k with
    | zero => simpa using base
    | succ k ih =>
      by_cases hk : k<c
      · have he : c-k=(c-(k+1))+1 := by omega
        rw [he] at ih
        exact step _ ih
      · simpa [Nat.sub_eq_zero_of_le (by omega : c≤k),
          Nat.sub_eq_zero_of_le (by omega : c≤k+1)] using ih
  have h : Finite (⊤ : Subgroup G) := by simpa [L] using hall c
  let _ := h
  exact Finite.of_equiv _ (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toEquiv
theorem z89 (G : Type*) [Group G]
    [Group.FG G] [Group.IsNilpotent G] [Finite (Abelianization G)] : Finite G := by
  have he : (⊤ : Subgroup G).lowerCentralSeries 1=commutator G :=
    Subgroup.top_lowerCentralSeries_one
  let _ : Finite (G ⧸ (⊤ : Subgroup G).lowerCentralSeries 1) := by
    rw [he]
    exact (inferInstance : Finite (Abelianization G))
  let _ : Finite (lowerFactor G 0) := inferInstance
  exact z147 G (z553 G)
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement
namespace CriticalPercolation
lemma z411 (G : Type*) [Group G] [Group.FG G] (n : ℕ)
    [Finite (lowerFactor G n)] : Finite (lowerFactor G (n+1)) := by
  let N := (⊤ : Subgroup G).lowerCentralSeries (n+1)
  let M := (⊤ : Subgroup G).lowerCentralSeries (n+2)
  let π := QuotientGroup.mk' M
  let σ := QuotientGroup.mk' N
  have hMN : M≤N := (⊤ : Subgroup G).lowerCentralSeries_antitone (by omega)
  let q : (G ⧸ M) →* (G ⧸ N) := QuotientGroup.lift M σ (by
    rw [QuotientGroup.ker_mk']; exact hMN)
  have hq (g : G) : q (π g)=σ g := rfl
  let H := ((⊤ : Subgroup G).lowerCentralSeries n).map π
  let f : H →* lowerFactor G n := {
    toFun := fun h => ⟨q h.val,by
      obtain ⟨g,hg,he⟩ := h.property
      exact ⟨g,hg,by change σ g=q h.val; rw [←he,hq]⟩⟩
    map_one' := by apply Subtype.ext; exact q.map_one
    map_mul' := by intros; apply Subtype.ext; exact q.map_mul _ _ }
  have hf : Surjective f := by
    rintro ⟨x,g,hg,rfl⟩
    exact ⟨⟨π g,⟨g,hg,rfl⟩⟩,rfl⟩
  have hker : f.ker.map H.subtype≤Subgroup.center (G ⧸ M) := by
    rintro x ⟨h,hh,rfl⟩
    obtain ⟨g,hg,he⟩ := h.property
    apply z22 G (n+1)
    refine ⟨g,?_,he⟩
    have heq : σ g=1 := by
      rw [←hq,he]
      exact congrArg Subtype.val hh
    change g∈N
    rw [←QuotientGroup.ker_mk' N]
    exact heq
  have hcomm : ⁅(⊤ : Subgroup (G ⧸ M)),H⁆=lowerFactor G (n+1) := by
    have hπ : (⊤ : Subgroup G).map π=⊤ :=
      Subgroup.map_top_of_surjective π QuotientGroup.mk_surjective
    change ⁅⊤,((⊤ : Subgroup G).lowerCentralSeries n).map π⁆=
      ((⊤ : Subgroup G).lowerCentralSeries (n+1)).map π
    rw [←hπ,←Subgroup.map_commutator,Subgroup.commutator_comm,
      ←Subgroup.lowerCentralSeries_succ]
  have hfin := z52 H f hf hker
    (hcomm ▸ z22 G (n+1))
  rw [hcomm] at hfin
  exact hfin.to_subtype
theorem z216 (G : Type*) [Group G]
    [Group.IsNilpotent G] (start : ℕ)
    (hfin : ∀ n, start≤n → Finite (lowerFactor G n)) :
    Finite ((⊤ : Subgroup G).lowerCentralSeries start) := by
  obtain ⟨c,hc⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp
    (inferInstance : Group.IsNilpotent G)
  let L := fun n => (⊤ : Subgroup G).lowerCentralSeries n
  have step (n : ℕ) (hsn : start≤n) (hn : Finite (L (n+1))) : Finite (L n) := by
    let F := lowerFactor G n
    let _ : Finite F := hfin n hsn
    let q := QuotientGroup.mk' (L (n+1))
    let f : L n →* F := {
      toFun := fun x => ⟨q x.val,⟨x.val,x.property,rfl⟩⟩
      map_one' := by apply Subtype.ext; exact q.map_one
      map_mul' := by intros; apply Subtype.ext; exact q.map_mul _ _ }
    have hemem (x : L n) : x∈f.ker ↔ x.val∈L (n+1) := by
      change f x=1 ↔ _
      rw [Subtype.ext_iff]
      change q x.val=1 ↔ _
      exact QuotientGroup.eq_one_iff _
    let e : L (n+1) ≃ f.ker := {
      toFun := fun x => ⟨⟨x.val,
        (⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.le_succ n) x.property⟩,
        (hemem _).mpr x.property⟩
      invFun := fun x => ⟨x.val.val,(hemem _).mp x.property⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
    let _ : Finite f.ker := Finite.of_equiv _ e
    exact f.finite_iff_finite_ker_range.mpr ⟨inferInstance,inferInstance⟩
  have hall : ∀ k n, c≤n+k → start≤n → Finite (L n) := by
    intro k
    induction k with
    | zero =>
      intro n hcn _
      have hn : L n=⊥ := by
        apply le_antisymm ?_ bot_le
        calc
          L n ≤ L c := (⊤ : Subgroup G).lowerCentralSeries_antitone (by omega)
          _ = ⊥ := hc
      rw [hn]
      infer_instance
    | succ k ih =>
      intro n hcn hsn
      exact step n hsn (ih (n+1) (by omega) (by omega))
  exact hall c start (by omega) le_rfl
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement
namespace CriticalPercolation
variable {G A : Type*} [Group G] [Group A]
def centralCommHom (hc : commutator G≤Subgroup.center G) (a : G) :
    G →* commutator G where
  toFun b := ⟨⁅a,b⁆,Subgroup.commutator_mem_commutator (by trivial) (by trivial)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' b d := by
    apply Subtype.ext
    change ⁅a,b*d⁆=⁅a,b⁆*⁅a,d⁆
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hd := hc (Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup G))
      (H₂ := ⊤) (by trivial) (by trivial) : ⁅a,d⁆∈commutator G)
    calc
      ⁅a,b⁆*b*⁅a,d⁆*b⁻¹ = ⁅a,b⁆*(b*⁅a,d⁆)*b⁻¹ := by group
      _ = ⁅a,b⁆*(⁅a,d⁆*b)*b⁻¹ := by rw [Subgroup.mem_center_iff.mp hd b]
      _ = _ := by group
theorem z65 [Group.FG G]
    (hc : commutator G≤Subgroup.center G) (ρ : G →* A)
    (hker : ρ.ker≤Subgroup.center G) (g : G)
    (hcyc : ∀ a : G, ∃ k : ℤ, IsOfFinOrder (ρ (a*g^(-k)))) :
    (commutator G : Set G).Finite := by
  let C := commutator G
  let _ : CommGroup C := {
    (inferInstance : Group C) with
    mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hc b.property) a.val) }
  let _ : Group.FG C := z414 hc
  let t := centralCommHom hc
  have ht (a b : G) (hb : IsOfFinOrder (ρ b)) : IsOfFinOrder (t a b) := by
    obtain ⟨m,hm,he⟩ := hb.exists_pow_eq_one
    have hpow : b^m∈ρ.ker := by change ρ (b^m)=1; rwa [map_pow]
    have hz := hker hpow
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨m,hm,?_⟩
    rw [←map_pow]
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz a)
  have hself : t g g=1 := by apply Subtype.ext; simp [t,centralCommHom,commutatorElement_def]
  have hga (a : G) : IsOfFinOrder (t g a) := by
    obtain ⟨k,hk⟩ := hcyc a
    have h := ht g (a*g^(-k)) hk
    simpa only [map_mul,map_zpow,hself,one_zpow,mul_one] using h
  have hag (a : G) : IsOfFinOrder (t a g) := by
    have he : t a g=(t g a)⁻¹ := by
      apply Subtype.ext
      exact (commutatorElement_inv g a).symm
    rw [he]
    exact (hga a).inv
  have hab (a b : G) : IsOfFinOrder (t a b) := by
    obtain ⟨k,hk⟩ := hcyc b
    have hw := ht a (b*g^(-k)) hk
    have hg : (t a g)^k∈CommGroup.torsion C :=
      (CommGroup.torsion C).zpow_mem (hag a) k
    have hh := (CommGroup.torsion C).mul_mem hw hg
    have he : t a (b*g^(-k))*(t a g)^k=t a b := by
      rw [map_mul,map_zpow,zpow_neg]
      group
    rw [he] at hh
    exact hh
  have hsub : C≤(CommGroup.torsion C).map C.subtype := by
    apply Subgroup.commutator_le.mpr
    intro a _ b _
    exact ⟨t a b,hab a b,rfl⟩
  let _ : Finite C := CommGroup.finite_of_fg_isMulTorsion C (fun c => by
    obtain ⟨d,hd,he⟩ := hsub c.property
    change IsOfFinOrder d at hd
    exact (show d=c from Subtype.ext he) ▸ hd)
  exact Set.toFinite _
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical
namespace CriticalPercolation
lemma z137 {G A : Type*} [Group G] [Group A]
    (ρ : G →* A) (hρ : Surjective ρ) (φ : A →* Multiplicative ℤ)
    (hφ : Surjective φ) (hk : (φ.ker : Set A).Finite) :
    ∃ g : G, ∀ a : G, ∃ k : ℤ, IsOfFinOrder (ρ (a*g^(-k))) := by
  obtain ⟨g,hg⟩ := hφ.comp hρ (Multiplicative.ofAdd (1 : ℤ))
  change φ (ρ g)=Multiplicative.ofAdd (1 : ℤ) at hg
  let _ := hk.to_subtype
  refine ⟨g,fun a => ?_⟩
  let k := (φ (ρ a)).toAdd
  refine ⟨k,?_⟩
  have he : ρ (a*g^(-k))∈φ.ker := by
    change φ (ρ (a*g^(-k)))=1
    rw [map_mul,map_zpow,map_mul,map_zpow,hg]
    change (φ (ρ a)).toAdd+(-k) • (1 : ℤ)=0
    simp [k]
  obtain ⟨m,hm,heq⟩ :=
    (isOfFinOrder_of_finite (⟨ρ (a*g^(-k)),he⟩ : φ.ker)).exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m,hm,congrArg Subtype.val heq⟩
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical commutatorElement
namespace CriticalPercolation
theorem z215 (G : Type*) [Group G] [Group.FG G]
    (φ : Abelianization G →* Multiplicative ℤ) (hφ : Surjective φ)
    (hk : (φ.ker : Set (Abelianization G)).Finite) : Finite (lowerFactor G 1) := by
  let M := (⊤ : Subgroup G).lowerCentralSeries 2
  let p := QuotientGroup.mk' M
  have hM : M≤commutator G := by
    rw [←Subgroup.top_lowerCentralSeries_one]
    exact (⊤ : Subgroup G).lowerCentralSeries_antitone (by omega)
  let ρ : (G ⧸ M) →* Abelianization G := QuotientGroup.lift M (Abelianization.of : G →* Abelianization G) (by
    rw [Abelianization.ker_of]; exact hM)
  have hρ : Surjective ρ := by
    intro a
    obtain ⟨g,rfl⟩ := (QuotientGroup.mk_surjective (s := commutator G)) a
    exact ⟨p g,rfl⟩
  have hcomm : commutator (G ⧸ M)=lowerFactor G 1 := by
    have hp : (⊤ : Subgroup G).map p=⊤ :=
      Subgroup.map_top_of_surjective p QuotientGroup.mk_surjective
    change ⁅⊤,⊤⁆=((⊤ : Subgroup G).lowerCentralSeries 1).map p
    rw [Subgroup.top_lowerCentralSeries_one,commutator,Subgroup.map_commutator,hp]
  have hc : commutator (G ⧸ M)≤Subgroup.center (G ⧸ M) := by
    rw [hcomm]
    exact z22 G 1
  have hker : ρ.ker≤Subgroup.center (G ⧸ M) := by
    intro x hx
    obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective x
    have hg : g∈commutator G := by
      change Abelianization.of g=1 at hx
      exact (QuotientGroup.eq_one_iff g).mp hx
    apply z22 G 1
    exact ⟨g,hg,rfl⟩
  obtain ⟨g,hg⟩ := z137 ρ hρ φ hφ hk
  have hf := z65 hc ρ hker g hg
  rw [hcomm] at hf
  exact hf.to_subtype
theorem z56 (G : Type*)
    [Group G] [Group.FG G] [Group.IsNilpotent G]
    (φ : Abelianization G →* Multiplicative ℤ) (hφ : Surjective φ)
    (hk : (φ.ker : Set (Abelianization G)).Finite) :
    (commutator G : Set G).Finite := by
  have hfirst := z215 G φ hφ hk
  have htail : ∀ n, 1≤n → Finite (lowerFactor G n) := by
    intro n hn
    induction n,hn using Nat.le_induction with
    | base => exact hfirst
    | succ n hn ih =>
      let _ := ih
      exact z411 G n
  have hf := z216 G 1 htail
  rw [Subgroup.top_lowerCentralSeries_one] at hf
  let _ := hf
  exact Set.toFinite _
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical DirectSum
namespace CriticalPercolation
theorem z241 (A : Type*) [AddCommGroup A] [AddGroup.FG A] :
    Finite A ∨
      (∃ φ : A →+ ℤ, Surjective φ ∧ (φ.ker : Set A).Finite) ∨
      (∃ φ : A →+ (ℤ×ℤ), Surjective φ) := by
  obtain ⟨n,ι,hι,p,hp,e,⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod A
  let _ := hι
  let _ : ∀ i : ι, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let T := ⨁ i : ι, ZMod (p i ^ e i)
  let _ : Finite T := Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  cases n with
  | zero =>
    exact Or.inl (Finite.of_equiv _ f.symm.toEquiv)
  | succ n =>
    cases n with
    | zero =>
      let φ := (Finsupp.applyAddHom (0 : Fin 1)).comp
        ((AddMonoidHom.fst (Fin 1 →₀ ℤ) T).comp f.toAddMonoidHom)
      have hs : Surjective φ := by
        intro z
        refine ⟨f.symm (Finsupp.single 0 z,0),?_⟩
        simp [φ]
      have hk : (φ.ker : Set A).Finite := by
        apply (Set.finite_singleton (0 : Fin 1 →₀ ℤ)).prod (Set.toFinite (Set.univ : Set T)) |>.preimage f.injective.injOn |>.subset
        intro x hx
        change (f x).1∈({0} : Set (Fin 1 →₀ ℤ)) ∧ (f x).2∈(Set.univ : Set T)
        refine ⟨?_,Set.mem_univ _⟩
        apply Finsupp.ext
        intro i
        have hi : i=(0 : Fin 1) := Fin.ext (by omega)
        subst i
        exact hx
      exact Or.inr (Or.inl ⟨φ,hs,hk⟩)
    | succ n =>
      let ev : (Fin (n+2) →₀ ℤ) →+ (ℤ×ℤ) :=
        (Finsupp.applyAddHom ⟨0,by omega⟩).prod (Finsupp.applyAddHom ⟨1,by omega⟩)
      let φ := ev.comp ((AddMonoidHom.fst (Fin (n+2) →₀ ℤ) T).comp f.toAddMonoidHom)
      refine Or.inr (Or.inr ⟨φ,?_⟩)
      intro z
      refine ⟨f.symm (Finsupp.single ⟨0,by omega⟩ z.1 +
        Finsupp.single ⟨1,by omega⟩ z.2,0),?_⟩
      simp [φ,ev]
theorem z496 (A : Type*) [CommGroup A] [Group.FG A] :
    Finite A ∨
      (∃ φ : A →* Multiplicative ℤ, Surjective φ ∧ (φ.ker : Set A).Finite) ∨
      (∃ φ : A →* Multiplicative (ℤ×ℤ), Surjective φ) := by
  rcases z241 (Additive A) with h | ⟨φ,hs,hk⟩ | ⟨φ,hs⟩
  · let _ := h
    exact Or.inl (Finite.of_equiv _ Additive.toMul)
  · refine Or.inr (Or.inl ⟨φ.toMultiplicativeRight,?_,?_⟩)
    · exact fun z => hs z.toAdd
    · exact hk
  · refine Or.inr (Or.inr ⟨φ.toMultiplicativeRight,?_⟩)
    exact fun z => hs z.toAdd
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical
namespace CriticalPercolation
universe u v
lemma z118 {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hk : (f.ker : Set G).Finite) (S : Set H) (hS : S.Finite) :
    (f ⁻¹' S).Finite := by
  let _ := hk.to_subtype
  have hfib : ∀ a : H, (f ⁻¹' {a}).Finite := by
    intro a
    by_cases ha : (f ⁻¹' {a}).Nonempty
    · obtain ⟨x,hx⟩ := ha
      change f x=a at hx
      rw [←hx]
      let _ := Finite.of_equiv _ (f.fiberEquivKer x).symm
      exact Set.toFinite _
    · rw [Set.not_nonempty_iff_eq_empty.mp ha]
      exact Set.finite_empty
  apply (hS.biUnion (fun a _ => hfib a)).subset
  exact fun x hx => Set.mem_iUnion₂.mpr ⟨f x,hx,rfl⟩
lemma z290 {G H K : Type*} [Group G] [Group H] [Group K]
    (f : G →* H) (g : H →* K)
    (hf : (f.ker : Set G).Finite) (hg : (g.ker : Set H).Finite) :
    ((g.comp f).ker : Set G).Finite :=
  z118 f hf g.ker hg
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical
namespace CriticalPercolation
theorem z447 (G : Type*) [Group G] [Group.FG G]
    [Group.IsNilpotent G] :
    Finite G ∨
      (∃ φ : G →* Multiplicative ℤ, Surjective φ ∧ (φ.ker : Set G).Finite) ∨
      (∃ φ : G →* Multiplicative (ℤ×ℤ), Surjective φ) := by
  let q : G →* Abelianization G := Abelianization.of
  have hq : Surjective q := QuotientGroup.mk_surjective
  let _ : Group.FG (Abelianization G) := Group.fg_of_surjective hq
  rcases z496 (Abelianization G) with h | ⟨φ,hφ,hk⟩ | ⟨φ,hφ⟩
  · let _ := h
    exact Or.inl (z89 G)
  · refine Or.inr (Or.inl ⟨φ.comp q,hφ.comp hq,?_⟩)
    apply z290 q φ ?_ hk
    have hf := z56 G φ hφ hk
    simpa only [q,Abelianization.ker_of] using hf
  · exact Or.inr (Or.inr ⟨φ.comp q,hφ.comp hq⟩)
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
universe u
section
section
noncomputable section
open Set Function
open scoped Classical DirectSum
namespace CriticalPercolation
inductive z6 : (G : Type u) → [Group G] → ℕ → Prop
  | finite (G : Type u) [Group G] [Finite G] : z6 G 0
  | cyclic (G : Type u) [Group G] (e : G ≃* Multiplicative ℤ) :
      z6 G 1
  | extension {G Q : Type u} [Group G] [Group Q] (f : G →* Q)
      (hf : Surjective f) {n m : ℕ}
      (hker : z6 f.ker n)
      (hquot : z6 Q m) : z6 G (n+m)
lemma z6.z442 {G Q : Type u} [Group G] [Group Q]
    {n : ℕ} (hQ : z6 Q n) (f : G →* Q)
    (hf : Surjective f) [Finite f.ker] : z6 G n := by
  simpa using z6.extension f hf (.finite f.ker) hQ
lemma z6.of_equiv {G Q : Type u} [Group G] [Group Q]
    {n : ℕ} (hQ : z6 Q n) (e : G ≃* Q) :
    z6 G n := by
  have he : e.toMonoidHom.ker=⊥ := e.toMonoidHom.ker_eq_bot e.injective
  let _ : Finite e.toMonoidHom.ker := he.symm ▸ (inferInstance : Finite (⊥ : Subgroup G))
  exact hQ.z442 e.toMonoidHom e.surjective
private lemma z120 (n : ℕ) :
    ∀ (A : Type u) [AddCommGroup A] [Module.Free ℤ A] [Module.Finite ℤ A],
      Module.finrank ℤ A=n → ∃ k≤n, z6 (Multiplicative A) k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A _ _ _ hrank
    let b : Module.Basis (Fin n) ℤ A := hrank ▸ Module.finBasis ℤ A
    let e := b.equivFun
    cases n with
    | zero =>
      let _ : Subsingleton A := ⟨fun x y => e.injective (funext fun i => Fin.elim0 i)⟩
      exact ⟨0,le_rfl,.finite _⟩
    | succ n =>
      let f : A →+ ULift.{u} ℤ := {
        toFun := fun a => ⟨e a 0⟩
        map_zero' := by apply ULift.ext; simp
        map_add' := by intros; apply ULift.ext; simp }
      have hf : Surjective f := by
        intro z
        exact ⟨e.symm (fun _ => z.down),by apply ULift.ext; simp [f]⟩
      let K := f.ker.toIntSubmodule
      have hzero (a : K) : e a.val 0=0 := congrArg ULift.down a.property
      let d : K →ₗ[ℤ] (Fin n → ℤ) := {
        toFun := fun a i => e a.val i.succ
        map_add' := by intros; ext i; simp
        map_smul' := by intros; ext i; simp }
      have hd : Injective d := by
        intro a a' haa
        apply Subtype.ext
        apply e.injective
        funext i
        exact Fin.cases ((hzero a).trans (hzero a').symm) (fun j => congrFun haa j) i
      have hr : Module.finrank ℤ K≤n := by
        simpa using d.finrank_le_finrank_of_injective hd
      obtain ⟨k,hk,hC⟩ := ih (Module.finrank ℤ K) (by omega) K rfl
      let ek : f.toMultiplicative.ker ≃* Multiplicative K := {
        toFun := fun a => Multiplicative.ofAdd ⟨a.val.toAdd,a.property⟩
        invFun := fun a => ⟨Multiplicative.ofAdd a.toAdd.val,a.toAdd.property⟩
        left_inv := by intro a; rfl
        right_inv := by intro a; rfl
        map_mul' := by intros; rfl }
      refine ⟨k+1,by omega,?_⟩
      exact z6.extension f.toMultiplicative (fun z => hf z.toAdd)
        (hC.of_equiv ek) (.cyclic _ AddEquiv.ulift.toMultiplicative)
theorem z189 (A : Type u) [AddCommGroup A]
    [Module.Free ℤ A] [Module.Finite ℤ A] :
    ∃ n, z6 (Multiplicative A) n := by
  obtain ⟨n,_,hn⟩ := z120 (Module.finrank ℤ A) A rfl
  exact ⟨n,hn⟩
theorem z156 (A : Type u) [CommGroup A] [Group.FG A] :
    ∃ n, z6 A n := by
  obtain ⟨n,ι,hι,p,hp,e,⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod (Additive A)
  let _ := hι
  let _ : ∀ i : ι, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let T := ⨁ i : ι, ZMod (p i ^ e i)
  let _ : Finite T := Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  let φ₀ := (AddMonoidHom.fst (Fin n →₀ ℤ) T).comp f.toAddMonoidHom
  let φ : Additive A →+ ULift.{u} (Fin n →₀ ℤ) := AddEquiv.ulift.symm.toAddMonoidHom.comp φ₀
  have hs : Surjective φ := by
    intro z
    refine ⟨f.symm (z.down,0),?_⟩
    change ULift.up (φ₀ (f.symm (z.down,0)))=z
    apply ULift.ext
    change φ₀ (f.symm (z.down,0))=z.down
    simp [φ₀]
  have hk : (φ.toMultiplicativeRight.ker : Set A).Finite := by
    apply ((Set.finite_singleton (0 : Fin n →₀ ℤ)).prod
      (Set.toFinite (Set.univ : Set T))).preimage f.injective.injOn |>.subset
    intro x hx
    exact ⟨congrArg (fun z : Multiplicative (ULift (Fin n →₀ ℤ)) => z.toAdd.down) hx,
      Set.mem_univ _⟩
  let _ := hk.to_subtype
  obtain ⟨k,hk⟩ := z189 (ULift.{u} (Fin n →₀ ℤ))
  exact ⟨k,hk.z442 φ.toMultiplicativeRight (fun z => hs z.toAdd)⟩
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical
namespace CriticalPercolation
theorem z74 (G : Type*) [Group G] [Group.FG G]
    [Group.IsNilpotent G] (J : Subgroup G) : ∃ k, z6 J k := by
  obtain ⟨c,hc⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp
    (inferInstance : Group.IsNilpotent G)
  let L := fun n => J ⊓ (⊤ : Subgroup G).lowerCentralSeries n
  have step (n : ℕ) (hn : ∃ k, z6 (L (n+1)) k) :
      ∃ k, z6 (L n) k := by
    let F := lowerFactor G n
    let _ : CommGroup F := {
      (inferInstance : Group F) with
      mul_comm := fun a b => Subtype.ext
        (Subgroup.mem_center_iff.mp (z22 G n b.property) a.val) }
    let _ : Group.FG F := lowerFactor_fg G n
    let q := QuotientGroup.mk' ((⊤ : Subgroup G).lowerCentralSeries (n+1))
    let f : L n →* F := {
      toFun := fun x => ⟨q x.val,⟨x.val,x.property.2,rfl⟩⟩
      map_one' := by apply Subtype.ext; exact q.map_one
      map_mul' := by intros; apply Subtype.ext; exact q.map_mul _ _ }
    let _ : Group.FG f.range := z311 f.range
    obtain ⟨k,hk⟩ := hn
    have hemem (x : L n) : x∈f.ker ↔ x.val∈(⊤ : Subgroup G).lowerCentralSeries (n+1) := by
      change f x=1 ↔ _
      rw [Subtype.ext_iff]
      change q x.val=1 ↔ _
      exact QuotientGroup.eq_one_iff _
    let e : L (n+1) ≃* f.ker := {
      toFun := fun x => ⟨⟨x.val,⟨x.property.1,
        (⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.le_succ n) x.property.2⟩⟩,
        (hemem _).mpr x.property.2⟩
      invFun := fun x => ⟨x.val.val,⟨x.val.property.1,(hemem _).mp x.property⟩⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_mul' := by intros; rfl }
    have hker := hk.of_equiv e.symm
    have he : f.rangeRestrict.ker=f.ker := by
      ext x
      change f.rangeRestrict x=1 ↔ f x=1
      exact Subtype.ext_iff
    have hker' : z6 f.rangeRestrict.ker k := he.symm ▸ hker
    obtain ⟨m,hm⟩ := z156 f.range
    exact ⟨k+m,z6.extension f.rangeRestrict
      f.rangeRestrict_surjective hker' hm⟩
  have base : ∃ k, z6 (L c) k := by
    have he : L c=⊥ := by simp [L,hc]
    rw [he]
    exact ⟨0,.finite _⟩
  have hall : ∀ k, ∃ m, z6 (L (c-k)) m := by
    intro k
    induction k with
    | zero => simpa using base
    | succ k ih =>
      by_cases hk : k<c
      · have he : c-k=(c-(k+1))+1 := by omega
        rw [he] at ih
        exact step _ ih
      · have he : c-k=c-(k+1) := by omega
        exact he ▸ ih
  have h := hall c
  have he : L (c-c)=J := by simp [L]
  exact he ▸ h
theorem z124 (G : Type*) [Group G] [Group.FG G]
    [Group.IsNilpotent G] : ∃ k, z6 G k := by
  obtain ⟨k,hk⟩ := z74 G ⊤
  exact ⟨k,hk.of_equiv Subgroup.topEquiv.symm⟩
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical Pointwise
namespace CriticalPercolation
theorem z90 {G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (hf : Surjective f) (J : Subgroup G)
    [(J.map f).FiniteIndex] [(J.subgroupOf f.ker).FiniteIndex] : J.FiniteIndex := by
  let S := J ⊔ f.ker
  have hS : S.FiniteIndex := by
    constructor
    have hn := (inferInstance : (J.map f).FiniteIndex).index_ne_zero
    rw [Subgroup.index_map,f.range_eq_top_of_surjective hf,Subgroup.index_top,mul_one] at hn
    exact hn
  let _ := hS
  let inc : f.ker →* S := {
    toFun := fun x => ⟨x.val,(le_sup_right : f.ker≤J⊔f.ker) x.property⟩
    map_one' := rfl
    map_mul' := by intros; rfl }
  let F : (f.ker ⧸ J.subgroupOf f.ker) → (S ⧸ J.subgroupOf S) :=
    Quotient.map inc (by
      intro a b hab
      apply (QuotientGroup.leftRel_apply (s := J.subgroupOf S)).mpr
      exact (QuotientGroup.leftRel_apply (s := J.subgroupOf f.ker)).mp hab)
  have hF : Surjective F := by
    intro y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk_surjective y
    have hx : x.val∈(f.ker : Set G)*(J : Set G) := by
      rw [←Subgroup.normal_mul, sup_comm]
      exact x.property
    obtain ⟨a,ha,b,hb,he⟩ := hx
    refine ⟨QuotientGroup.mk ⟨a,ha⟩,?_⟩
    apply Quotient.sound
    apply (QuotientGroup.leftRel_apply (s := J.subgroupOf S)).mpr
    change a⁻¹*x.val∈J
    rw [←he,inv_mul_cancel_left]
    exact hb
  let _ : Finite (S ⧸ J.subgroupOf S) := Finite.of_surjective F hF
  apply Subgroup.finiteIndex_iff_finite_quotient.mpr
  exact Finite.of_equiv _ (Subgroup.quotientEquivProdOfLE (le_sup_left : J≤S)).symm
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical
namespace CriticalPercolation
theorem z123 {G : Type*} [Group G]
    (e : G ≃* Multiplicative ℤ) (J : Subgroup G) [Infinite J] : J.FiniteIndex := by
  let a : Additive G ≃+ ℤ := e.toAdditive.trans (AddEquiv.additiveMultiplicative ℤ)
  let K := J.toAddSubgroup.map a.toAddMonoidHom
  obtain ⟨j,hj⟩ := exists_ne (1 : J)
  let z := a (Additive.ofMul j.val)
  have hz : z≠0 := by
    intro h
    have he : Additive.ofMul j.val=0 := a.injective (h.trans a.map_zero.symm)
    apply hj
    exact Subtype.ext he
  have hmem : z∈K := ⟨Additive.ofMul j.val,j.property,rfl⟩
  have hZ : (AddSubgroup.zmultiples z).FiniteIndex := by
    constructor
    rw [Int.index_zmultiples]
    exact Int.natAbs_ne_zero.mpr hz
  let _ := hZ
  have hK : K.FiniteIndex := AddSubgroup.finiteIndex_of_le (AddSubgroup.zmultiples_le.mpr hmem)
  constructor
  have hn := hK.index_ne_zero
  have he : K.index=J.index := by
    exact (AddSubgroup.index_map_equiv J.toAddSubgroup a).trans J.index_toAddSubgroup
  rwa [he] at hn
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
universe groupUniverse
section
section
noncomputable section
open Set Function
open scoped Classical
namespace CriticalPercolation
theorem z6.subgroup {G : Type groupUniverse} [Group G] {n : ℕ}
    (hG : z6 G n) :
    ∀ J : Subgroup G, ∃ m≤n, z6 J m ∧ (m=n → J.FiniteIndex) := by
  induction hG with
  | @finite G _ _ =>
    intro J
    exact ⟨0,le_rfl,.finite _,fun _ => inferInstance⟩
  | @cyclic G _ e =>
    intro J
    cases finite_or_infinite J with
    | inl h =>
      let _ := h
      exact ⟨0,by omega,.finite _,by omega⟩
    | inr h =>
      let _ := h
      let _ : IsCyclic G := isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
      exact ⟨1,le_rfl,.cyclic _ (intCyclicMulEquiv.symm),
        fun _ => z123 e J⟩
  | @extension G Q _ _ f hf n m hker hquot ihker ihquot =>
    intro J
    obtain ⟨k,hk,hK,hki⟩ := ihker (J.subgroupOf f.ker)
    obtain ⟨l,hl,hL,hli⟩ := ihquot (J.map f)
    let g : J →* J.map f := {
      toFun := fun j => ⟨f j.val,⟨j.val,j.property,rfl⟩⟩
      map_one' := by apply Subtype.ext; exact f.map_one
      map_mul' := by intros; apply Subtype.ext; exact f.map_mul _ _ }
    have hg : Surjective g := by
      rintro ⟨q,x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
    let e : g.ker ≃* J.subgroupOf f.ker := {
      toFun := fun a => ⟨⟨a.val.val,congrArg Subtype.val a.property⟩,a.val.property⟩
      invFun := fun a => ⟨⟨a.val.val,a.property⟩,Subtype.ext a.val.property⟩
      left_inv := by intro a; rfl
      right_inv := by intro a; rfl
      map_mul' := by intros; rfl }
    refine ⟨k+l,by omega,z6.extension g hg (hK.of_equiv e) hL,?_⟩
    intro he
    let _ := hki (by omega)
    let _ := hli (by omega)
    exact z90 f hf J
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function
open scoped Classical
namespace CriticalPercolation
private theorem z164 (n : ℕ) :
    ∀ (G : Type*) [Group G] [Group.FG G] [Group.IsNilpotent G],
      z6 G n → AlgebraicDescent G := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ _ _ hG
    rcases z447 G with h | ⟨φ,hφ,hk⟩ | ⟨φ,hφ⟩
    · let _ := h
      exact .finite G
    · exact .cyclic G φ hφ hk
    · apply AlgebraicDescent.plane G φ hφ
      intro J hJ
      obtain ⟨m,hm,hC,hi⟩ := hG.subgroup J
      have hlt : m<n := by
        by_contra! hge
        have he : m=n := by omega
        let _ := hi he
        have hker : φ.ker.FiniteIndex := Subgroup.finiteIndex_of_le hJ
        apply hker.index_ne_zero
        rw [Subgroup.index_ker,φ.range_eq_top_of_surjective hφ]
        rw [Nat.card_congr (Subgroup.topEquiv :
          (⊤ : Subgroup (Multiplicative (ℤ×ℤ))) ≃* Multiplicative (ℤ×ℤ)).toEquiv]
        exact Nat.card_eq_zero_of_infinite
      let _ : Group.FG J := z470 G J
      exact ih m hlt J hC
theorem z580 (G : Type*) [Group G] [Group.FG G] [Group.IsNilpotent G] :
    AlgebraicDescent G := by
  obtain ⟨n,hn⟩ := z124 G
  exact z164 n G hn
end CriticalPercolation
end
end
end
end OAI
end
section
namespace OAI
section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace CriticalPercolation.z2
theorem z134 [Fact (∀ V E : Type, CriticalPercolationLeaf.FiniteSizeCriterion V E)] {V E Λ N : Type}
    [Group Λ] [MulAction Λ V] [MulAction Λ E] [Group N] [Group.FG N] [Group.IsNilpotent N]
    (G : z2 V E) (hc : G.z7.Connected) (hl : G.LocallyFinite)
    (hg : G.SubexponentialGrowth) (ha : G.PreservesEnds (Λ := Λ))
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (ρ : Λ →* N) (hρ : Surjective ρ)
    (hker : ∀ v : V, (MulAction.orbit ρ.ker v).Finite)
    (hstab : ∀ v : V, ((MulAction.stabilizer Λ v).map ρ : Set N).Finite)
    (hpc : G.z3<1) : G.law G.z3 G.z12=0 :=
  z154 (z580 N) G hc hl hg ha S hS hcover
    ρ hρ hker hstab hpc
end CriticalPercolation.z2
end
end
end
end OAI
end
namespace OMA.P_arxiv_1902_03207
open Set MeasureTheory ProbabilityTheory OAI.CriticalPercolation OMA.S_arxiv_1902_03207
variable {d : ℕ}
def L (d : ℕ) : z2 (Vertex d) (Bond d) := ⟨ends⟩
abbrev u (i : Fin d) : Vertex d := Pi.single i 1
lemma ne_step (x : Vertex d) (i : Fin d) : x ≠ x + u i := by
  intro h
  have := congrFun h i
  simp at this
lemma adj_step (x : Vertex d) (i : Fin d) : (L d).z7.Adj x (x + u i) := by
  refine ⟨⟨(x, i), Set.mem_univ _, rfl⟩, ne_step x i⟩
lemma reach_line (x : Vertex d) (i : Fin d) (k : ℤ) :
    (L d).z7.Reachable x (x + k • u i) := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    refine ih.trans ?_
    have h := (adj_step (x + (k : ℤ) • u i) i).reachable
    convert h using 1
    rw [add_smul, one_smul, add_assoc]
  | pred k ih =>
    refine ih.trans ?_
    have h := (adj_step (x + (-(k : ℤ) - 1) • u i) i).reachable.symm
    convert h using 1
    rw [add_assoc, ← add_one_zsmul]
    congr 2
    ring
lemma reach_zero (x : Vertex d) : (L d).z7.Reachable 0 x := by
  have key : ∀ s : Finset (Fin d),
      (L d).z7.Reachable 0 (∑ i ∈ s, x i • u i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, add_comm]
      exact ih.trans (reach_line _ i (x i))
  convert key Finset.univ
  ext j
  simp [Finset.sum_apply, Pi.single_apply]
lemma connected (d : ℕ) : (L d).z7.Connected :=
  { preconnected := fun x y => (reach_zero x).symm.trans (reach_zero y)
    nonempty := ⟨0⟩ }
lemma locallyFinite (d : ℕ) : (L d).LocallyFinite := by
  intro v
  let near : Bool × Fin d → Bond d := fun b =>
    (if b.1 then v else v - Pi.single b.2 1, b.2)
  apply (Set.finite_range near).subset
  rintro ⟨x, i⟩ hx
  change v ∈ s(x, x + Pi.single i 1) at hx
  rcases Sym2.mem_iff.mp hx with h | h
  · exact ⟨(true, i), by simp [near, h]⟩
  · exact ⟨(false, i), by simp [near, h]⟩
lemma adj_coord {x y : Vertex d} (h : (L d).z7.Adj x y) (j : Fin d) :
    |y j - x j| ≤ 1 := by
  obtain ⟨⟨⟨b, i⟩, -, hb⟩, -⟩ := h
  change s(b, b + u i) = s(x, y) at hb
  have hj : |(u i : Vertex d) j| ≤ 1 := by
    by_cases hij : j = i
    · subst hij; simp
    · simp [Pi.single_apply, hij]
  rcases Sym2.eq_iff.mp hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simpa using hj
  · simpa [abs_neg] using hj
lemma ball_box (o : Vertex d) (n : ℕ) :
    (L d).z5 o n ⊆ {x | ∀ j, |x j - o j| ≤ n} := by
  induction n with
  | zero =>
    intro x hx j
    simp [z2.z5] at hx
    simp [hx]
  | succ n ih =>
    intro x hx j
    rcases hx with hx | hx
    · exact (ih hx j).trans (by push_cast; linarith)
    · obtain ⟨v, hv, hxv⟩ := Set.mem_iUnion₂.mp hx
      have h1 := ih hv j
      have h2 := adj_coord hxv j
      calc |x j - o j| = |(x j - v j) + (v j - o j)| := by ring_nf
        _ ≤ |x j - v j| + |v j - o j| := abs_add_le _ _
        _ ≤ 1 + n := add_le_add h2 h1
        _ = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
lemma ball_ncard (o : Vertex d) (n : ℕ) :
    ((L d).z5 o n).ncard ≤ (2 * n + 1) ^ d := by
  let T : Finset (Vertex d) :=
    Fintype.piFinset fun j => Finset.Icc (o j - n) (o j + n)
  have hsub : (L d).z5 o n ⊆ T := by
    intro x hx
    have h := ball_box o n hx
    simp only [T, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro j
    have := abs_le.mp (h j)
    constructor <;> linarith [this.1, this.2]
  calc ((L d).z5 o n).ncard ≤ (T : Set (Vertex d)).ncard :=
        Set.ncard_le_ncard hsub T.finite_toSet
    _ = T.card := Set.ncard_coe_finset T
    _ = (2 * n + 1) ^ d := by
        have hx : ∀ x : Fin d, (o x + n + 1 - (o x - n)).toNat = 2 * n + 1 := by
          intro x; omega
        simp only [T, Fintype.card_piFinset, Int.card_Icc]
        rw [Finset.prod_congr rfl (fun x _ => hx x)]
        simp
lemma growth (d : ℕ) : (L d).SubexponentialGrowth := by
  intro o ε hε
  have hlo := Real.isLittleO_log_id_atTop
  have hc : 0 < ε / (3 * (d + 1)) := by positivity
  have ht : Filter.Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1)) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_add_const_right
    exact Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop
  have hb := (ht.eventually (hlo.bound hc))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hb
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_of_max_le_right hn)
  have h := hN n (le_of_max_le_left hn)
  have hpos : (0 : ℝ) < 2 * n + 1 := by positivity
  have hlog0 : 0 ≤ Real.log (2 * n + 1) := Real.log_nonneg (by linarith)
  simp only [id, Real.norm_eq_abs, abs_of_nonneg hlog0, abs_of_pos hpos] at h
  calc Real.log (((L d).z5 o n).ncard : ℝ)
      ≤ Real.log (((2 * n + 1) ^ d : ℕ) : ℝ) := by
        apply Real.log_le_log
        · exact_mod_cast (L d).z288 (locallyFinite d) o n
        · exact_mod_cast ball_ncard o n
    _ = d * Real.log (2 * n + 1) := by push_cast; rw [Real.log_pow]
    _ ≤ d * (ε / (3 * (d + 1)) * (2 * n + 1)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ ε * n := by
        rw [← mul_assoc, mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [mul_nonneg hε.le (mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
          (sub_nonneg.mpr hn1)), mul_nonneg hε.le (by linarith : (0 : ℝ) ≤ n)]
abbrev T (d : ℕ) := Multiplicative (Vertex d)
instance actV : MulAction (T d) (Vertex d) where
  smul g x := Multiplicative.toAdd g + x
  one_smul x := zero_add x
  mul_smul g h x := add_assoc _ _ x
instance actE : MulAction (T d) (Bond d) where
  smul g b := (Multiplicative.toAdd g + b.1, b.2)
  one_smul b := by change (0 + b.1, b.2) = b; simp
  mul_smul g h b := by
    change (Multiplicative.toAdd g + Multiplicative.toAdd h + b.1, b.2) =
      (Multiplicative.toAdd g + (Multiplicative.toAdd h + b.1), b.2)
    rw [add_assoc]
lemma smulV (g : T d) (x : Vertex d) : g • x = Multiplicative.toAdd g + x := rfl
lemma preserves : (L d).PreservesEnds (Λ := T d) := by
  rintro g ⟨x, i⟩
  change s(Multiplicative.toAdd g + x, Multiplicative.toAdd g + x + u i) =
    s(Multiplicative.toAdd g + x, Multiplicative.toAdd g + (x + u i))
  rw [add_assoc]
instance fgT : Group.FG (T d) := by
  rw [← AddGroup.fg_iff_mul_fg]
  infer_instance
lemma no_perc [Fact (∀ V E : Type, CriticalPercolationLeaf.FiniteSizeCriterion V E)] (d : ℕ) (hpc : (L d).z3 < 1) :
    (L d).law (L d).z3 (L d).z12 = 0 := by
  refine z2.z134 (Λ := T d) (N := T d) (L d)
    (connected d) (locallyFinite d) (growth d) preserves {0} (Set.finite_singleton _)
    (fun v => ⟨0, rfl, Multiplicative.ofAdd v, by simp [smulV]⟩)
    (MonoidHom.id _) Function.surjective_id ?_ ?_ hpc
  · intro v
    apply (Set.finite_singleton v).subset
    rintro _ ⟨⟨g, hg⟩, rfl⟩
    have : g = 1 := hg
    subst this
    exact one_smul (T d) v
  · intro v
    apply (Set.finite_singleton (1 : T d)).subset
    rintro _ ⟨g, hg, rfl⟩
    have h : Multiplicative.toAdd g + v = v := hg
    have : Multiplicative.toAdd g = 0 := by simpa using h
    simpa using this
def tr (v : Vertex d) : (L d).Aut where
  vertex := Equiv.addRight v
  edge := (Equiv.addRight v).prodCongr (Equiv.refl _)
  preserves := by
    rintro ⟨x, i⟩
    change s(x + v, x + v + u i) = s(x + v, (x + u i) + v)
    rw [add_right_comm x v]
lemma rooted_iff (p : unitInterval) :
    0 < theta d p ↔ 0 < (L d).law p (L d).z12 := by
  change 0 < (L d).law p ((L d).z14 0) ↔ _
  constructor
  · intro h
    exact lt_of_lt_of_le h (measure_mono fun ω hω => ⟨0, hω⟩)
  · intro h
    rw [pos_iff_ne_zero] at h ⊢
    intro h0
    apply h
    rw [z2.z157]
    intro v
    have := z2.Aut.z227 (L d) (tr v) p 0
    change (L d).law p ((L d).z14 (0 + v)) = _ at this
    rw [zero_add] at this
    change (L d).law p ((L d).z14 v) = 0
    rw [this, h0]
lemma critical_eq : critical d = (L d).z3 := by
  unfold critical z2.z3
  congr 1
  ext p
  exact rooted_iff p
end OMA.P_arxiv_1902_03207
open OMA.S_arxiv_1902_03207 OMA.P_arxiv_1902_03207
theorem OMA.solution : OMA.R_arxiv_1902_03207_R1.H3 := by
  classical
  intro d _ hp hθ
  by_contra hn
  letI : Fact (∀ V E : Type, CriticalPercolationLeaf.FiniteSizeCriterion V E) := ⟨by
    intro V E f g F pc B hc hl hq h0 h1 hm
    exact hn ⟨V,E,f,hc,hl,hq,h0,h1,hm⟩⟩
  rw [critical_eq] at hθ hp
  have h := no_perc d hp
  exact (ne_of_gt ((rooted_iff _).mp hθ)) h
