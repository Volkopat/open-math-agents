import OMAStatements.S_wp_barnette_s_conjecture
import Mathlib
-- Credit: @my-other-github-account (port); original proof: OpenAI.
/- Adapted from openai/math@3344da59991ed94f9ba711217b29c1d760badfa6, Apache-2.0; topological drawing adapter added. -/
theorem ite_eq_left{c:Prop}{h:Decidable c}(hc:c){α:Sort _}{t e:α}:(if c then t else e)=t:=if_pos hc
theorem ite_eq_right{c:Prop}{h:Decidable c}(hc:¬c){α:Sort _}{t e:α}:(if c then t else e)=e:=if_neg hc
theorem ite_eq_left_of_eq_true{α:Sort _}{c:Prop}{x:Decidable c}(a b:α)(hc:c=True):(if c then a else b)=a:=if_pos (hc▸trivial)
theorem ite_eq_right_of_eq_false{α:Sort _}{c:Prop}{x:Decidable c}(a b:α)(hc:c=False):(if c then a else b)=b:=if_neg (hc▸id)
theorem dite_eq_left{c:Prop}{h:Decidable c}(hc:c){α:Sort _}{t:c→α}{e:¬c→α}:dite c t e=t hc:=dif_pos hc
theorem dite_eq_right{c:Prop}{h:Decidable c}(hc:¬c){α:Sort _}{t:c→α}{e:¬c→α}:dite c t e=e hc:=dif_neg hc

namespace OAI

namespace Barnette

universe u

/-- A topological plane drawing of a simple graph, with no crossings. -/
structure PlaneEmbedding {V : Type u} (G : SimpleGraph V) where
  point : V → ℝ × ℝ
  point_injective : Function.Injective point
  arc : ∀ (v w : V), G.Adj v w → Path (point v) (point w)
  arc_injective : ∀ (v w : V) (h : G.Adj v w),
    Function.Injective (arc v w h)
  arc_reverse : ∀ (v w : V) (h : G.Adj v w),
    arc w v h.symm = (arc v w h).symm
  arc_avoids_vertices : ∀ (v w : V) (h : G.Adj v w)
    (t : unitInterval) (z : V),
    arc v w h t = point z →
      (t = 0 ∧ z = v) ∨ (t = 1 ∧ z = w)
  interiors_disjoint : ∀ (v w x y : V) (h : G.Adj v w) (k : G.Adj x y)
    (t s : unitInterval),
    t ≠ 0 → t ≠ 1 → s ≠ 0 → s ≠ 1 →
    arc v w h t = arc x y k s →
      (v = x ∧ w = y) ∨ (v = y ∧ w = x)

/-- Planarity means existence of a crossing-free topological plane embedding. -/
def Planar {V : Type u} (G : SimpleGraph V) : Prop :=
  Nonempty (PlaneEmbedding G)

/-- Deleting any set of at most two vertices leaves a connected graph of order at least two. -/
def ThreeVertexConnected {V : Type u} [Fintype V] (G : SimpleGraph V) : Prop :=
  4 ≤ Fintype.card V ∧
    ∀ S : Finset V, S.card ≤ 2 → (G.induce {v | v ∉ S}).Connected

/-- A single spanning cycle, not a possibly disconnected spanning 2-factor. -/
def HasHamiltonianCycle {V : Type u} [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ v : V, ∃ p : G.Walk v v, p.IsHamiltonianCycle

/-- Cubic bipartite three-vertex-connected plane graphs have a Hamiltonian cycle. -/
def MainStatement : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj],
    G.IsRegularOfDegree 3 → G.IsBipartite → Planar G →
      ThreeVertexConnected G → HasHamiltonianCycle G

end Barnette

end OAI


namespace OAI

/-! Oriented finite networks, cycle and cut spaces, and graph realization. -/

namespace Barnette

structure Network (V E : Type*) where
  tail : E → V
  head : E → V

namespace Network
noncomputable section
variable {V E : Type*} (N : Network V E)

def graph : SimpleGraph V where
  Adj v w := v ≠ w ∧ ∃ e, (N.tail e = v ∧ N.head e = w) ∨
    (N.tail e = w ∧ N.head e = v)
  symm := ⟨by rintro v w ⟨h, e, hi⟩; exact ⟨h.symm, e, hi.symm⟩⟩
  loopless := ⟨fun v h => h.1 rfl⟩

theorem edge_reachable (e : E) : N.graph.Reachable (N.tail e) (N.head e) := by
  by_cases h : N.tail e = N.head e
  · rw [h]
  · exact (show N.graph.Adj (N.tail e) (N.head e) from
      ⟨h, e, Or.inl ⟨rfl, rfl⟩⟩).reachable

def gradient : (V → ℝ) →ₗ[ℝ] (E → ℝ) where
  toFun f e := f (N.head e) - f (N.tail e)
  map_add' f g := by ext e; dsimp; ring
  map_smul' c f := by ext e; dsimp; ring

@[simp] theorem gradient_apply (f : V → ℝ) (e : E) :
    N.gradient f e = f (N.head e) - f (N.tail e) := rfl

@[simp] theorem gradient_const (a : ℝ) : N.gradient (fun _ => a) = 0 := by
  ext e; simp

theorem gradient_eq_zero_iff (f : V → ℝ) :
    N.gradient f = 0 ↔ ∀ e, f (N.head e) = f (N.tail e) := by
  simp only [funext_iff, gradient_apply, Pi.zero_apply, sub_eq_zero]

theorem gradient_zero_adj {f : V → ℝ} (hf : N.gradient f = 0)
    {v w : V} (h : N.graph.Adj v w) : f v = f w := by
  obtain ⟨_, e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
  · exact ((N.gradient_eq_zero_iff f).mp hf e).symm
  · exact (N.gradient_eq_zero_iff f).mp hf e

theorem gradient_zero_reachable {f : V → ℝ} (hf : N.gradient f = 0)
    {v w : V} (h : N.graph.Reachable v w) : f v = f w := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons h p ih => exact (N.gradient_zero_adj hf h).trans ih

def constant : ℝ →ₗ[ℝ] (V → ℝ) where
  toFun a _ := a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ker_gradient (h : N.graph.Connected) :
    N.gradient.ker = (constant (V := V)).range := by
  obtain ⟨v⟩ := h.nonempty
  ext f
  constructor
  · intro hf
    refine ⟨f v, ?_⟩
    ext w
    exact N.gradient_zero_reachable hf (h v w)
  · rintro ⟨a, rfl⟩
    exact N.gradient_const a

variable [Fintype V] [Fintype E]
local instance : DecidableEq V := Classical.decEq _
local instance : DecidableEq E := Classical.decEq _

def incidence : Matrix V E ℝ := fun v e =>
  (if N.head e = v then 1 else 0) - (if N.tail e = v then 1 else 0)

def boundary : (E → ℝ) →ₗ[ℝ] (V → ℝ) := Matrix.toLin' N.incidence

omit [Fintype V] in
@[simp] theorem boundary_apply (x : E → ℝ) (v : V) :
    N.boundary x v = ∑ e, ((if N.head e = v then x e else 0) -
      (if N.tail e = v then x e else 0)) := by
  classical
  simp [boundary, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, incidence,
    sub_mul, ite_mul]

omit [Fintype E] in
theorem gradient_matrix : N.gradient = Matrix.toLin' N.incidence.transpose := by
  classical
  apply LinearMap.ext
  intro f
  ext e
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, incidence,
    sub_mul, ite_mul, Finset.sum_sub_distrib]

theorem sum_boundary (x : E → ℝ) : ∑ v, N.boundary x v = 0 := by
  classical
  simp only [boundary_apply]
  rw [Finset.sum_comm]
  simp [Finset.sum_sub_distrib]

omit [Fintype E] in
theorem rank_gradient (h : N.graph.Connected) :
    Module.finrank ℝ N.gradient.range + 1 = Fintype.card V := by
  obtain ⟨v⟩ := h.nonempty
  have hi : Function.Injective (constant (V := V)) := by
    intro a b hab
    exact congrFun hab v
  have hk : Module.finrank ℝ N.gradient.ker = 1 := by
    rw [N.ker_gradient h, LinearMap.finrank_range_of_inj hi]
    exact Module.finrank_self ℝ
  have hh := N.gradient.finrank_range_add_finrank_ker
  simpa only [hk, Module.finrank_pi] using hh

theorem rank_boundary (h : N.graph.Connected) :
    Module.finrank ℝ N.boundary.range + 1 = Fintype.card V := by
  have hh := N.rank_gradient h
  have he : Module.finrank ℝ N.boundary.range = Module.finrank ℝ N.gradient.range := by
    rw [N.gradient_matrix, boundary, Matrix.toLin'_apply', Matrix.toLin'_apply',
      ← Matrix.rank, ← Matrix.rank, Matrix.rank_transpose]
  rwa [he]

theorem dim_cycles (h : N.graph.Connected) :
    Module.finrank ℝ N.boundary.ker + Fintype.card V = Fintype.card E + 1 := by
  have hr := N.rank_boundary h
  have hk := N.boundary.finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at hk
  omega

theorem boundary_adjoint (x : E → ℝ) (f : V → ℝ) :
    ∑ v, N.boundary x v * f v = ∑ e, x e * N.gradient f e := by
  classical
  simp only [boundary_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp [sub_mul, ite_mul, Finset.sum_sub_distrib, mul_sub]

variable {F : Type*} [Fintype F] (D : Network F E)

theorem orthogonal_symm (h : ∀ f, N.boundary (D.gradient f) = 0) :
    ∀ f, D.boundary (N.gradient f) = 0 := by
  classical
  intro f
  ext y
  calc
    D.boundary (N.gradient f) y =
        ∑ z, D.boundary (N.gradient f) z * (fun z : F => if z = y then (1 : ℝ) else 0) z := by
          simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    _ = ∑ e, N.gradient f e * D.gradient ((fun z : F => if z = y then (1 : ℝ) else 0)) e :=
      D.boundary_adjoint _ _
    _ = ∑ e, D.gradient ((fun z : F => if z = y then (1 : ℝ) else 0)) e * N.gradient f e := by
      apply Finset.sum_congr rfl
      intro e _
      exact mul_comm _ _
    _ = ∑ v, N.boundary (D.gradient ((fun z : F => if z = y then (1 : ℝ) else 0))) v * f v :=
      (N.boundary_adjoint _ _).symm
    _ = 0 := by rw [h]; simp

structure Duality : Prop where
  connected : N.graph.Connected
  dual_connected : D.graph.Connected
  cycles_eq_cuts : N.boundary.ker = D.gradient.range
  dual_cycles_eq_cuts : D.boundary.ker = N.gradient.range

private theorem ker_eq_range_of_orth_card
    (hN : N.graph.Connected) (hD : D.graph.Connected)
    (hc : Fintype.card V + Fintype.card F = Fintype.card E + 2)
    (ho : ∀ f, N.boundary (D.gradient f) = 0) :
    N.boundary.ker = D.gradient.range := by
  have hle : D.gradient.range ≤ N.boundary.ker := by
    rintro _ ⟨f, rfl⟩
    exact ho f
  have hd₁ := N.dim_cycles hN
  have hd₂ := D.rank_gradient hD
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

theorem duality_of_orth_card
    (hN : N.graph.Connected) (hD : D.graph.Connected)
    (hc : Fintype.card V + Fintype.card F = Fintype.card E + 2)
    (ho : ∀ f, N.boundary (D.gradient f) = 0) : N.Duality D where
  connected := hN
  dual_connected := hD
  cycles_eq_cuts := N.ker_eq_range_of_orth_card D hN hD hc ho
  dual_cycles_eq_cuts := D.ker_eq_range_of_orth_card N hD hN (by omega)
    (N.orthogonal_symm D ho)

theorem Duality.euler (h : N.Duality D) :
    Fintype.card V + Fintype.card F = Fintype.card E + 2 := by
  have h₁ := N.dim_cycles h.connected
  rw [h.cycles_eq_cuts] at h₁
  have h₂ := D.rank_gradient h.dual_connected
  omega

end
end Network
end Barnette

namespace Barnette
noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma cubic_bipartite_order [Nonempty V] (hc : G.IsRegularOfDegree 3)
    (hb : G.IsBipartite) : 6 ≤ Fintype.card V := by
  obtain ⟨c⟩ := hb
  obtain ⟨v⟩ := ‹Nonempty V›
  have hp : (G.neighborFinset v).Nonempty := by
    apply Finset.card_pos.mp
    rw [G.card_neighborFinset_eq_degree, hc v]
    norm_num
  obtain ⟨w, hw⟩ := hp
  have hvw : G.Adj v w := (G.mem_neighborFinset v w).mp hw
  have hd : Disjoint (G.neighborFinset v) (G.neighborFinset w) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    have h₁ := c.valid hvw
    have h₂ := c.valid ((G.mem_neighborFinset v x).mp hx)
    have h₃ := c.valid ((G.mem_neighborFinset w x).mp hy)
    have hv := (c v).isLt
    have hw := (c w).isLt
    have hx := (c x).isLt
    have h₁' : (c v).val ≠ (c w).val := fun h => h₁ (Fin.ext h)
    have h₂' : (c v).val ≠ (c x).val := fun h => h₂ (Fin.ext h)
    have h₃' : (c w).val ≠ (c x).val := fun h => h₃ (Fin.ext h)
    omega
  have hle := Finset.card_le_card (Finset.subset_univ
    (G.neighborFinset v ∪ G.neighborFinset w))
  rw [Finset.card_union_of_disjoint hd, G.card_neighborFinset_eq_degree,
    G.card_neighborFinset_eq_degree, hc v, hc w, Finset.card_univ] at hle
  exact hle

omit [DecidableRel G.Adj] in

lemma boundary_cover_of_threeConnected (h : ThreeVertexConnected G)
    (A S : Finset V) (hS : S.card ≤ 2) (hSA : S ⊆ A)
    (hout : ∃ w, w ∉ A)
    (hboundary : ∀ v ∈ A, ∀ w, w ∉ A → G.Adj v w → v ∈ S) : A ⊆ S := by
  intro v hv
  by_contra hvS
  obtain ⟨w, hw⟩ := hout
  have hwS : w ∉ S := fun hs => hw (hSA hs)
  let H := G.induce {v | v ∉ S}
  have hr := (h.2 S hS) (⟨v,hvS⟩ : {v | v ∉ S}) ⟨w,hwS⟩
  obtain ⟨p⟩ := hr
  have hp : ∀ {a b : {v | v ∉ S}}, H.Walk a b → a.val ∈ A → b.val ∈ A := by
    intro a b p
    induction p with
    | nil => exact id
    | @cons a z b haz p ih =>
      intro ha
      apply ih
      by_contra hz
      exact a.property (hboundary a.val ha z.val hz haz)
  exact hw (hp p hv)

end
end Barnette

end OAI


namespace OAI

/-! Cuts, simplicity, and connectivity of finite oriented networks. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

def cut (A : Finset V) : Finset E := Finset.univ.filter fun e =>
  (N.tail e ∈ A ∧ N.head e ∉ A) ∨ (N.head e ∈ A ∧ N.tail e ∉ A)

omit [Fintype V] in
@[simp] lemma mem_cut (A : Finset V) (e : E) : e ∈ N.cut A ↔
    (N.tail e ∈ A ∧ N.head e ∉ A) ∨ (N.head e ∈ A ∧ N.tail e ∉ A) := by
  simp [cut]

@[simp] lemma cut_compl (A : Finset V) : N.cut Aᶜ = N.cut A := by
  ext e
  simp only [mem_cut, Finset.mem_compl]
  tauto

lemma region_card_le_cut (h : ThreeVertexConnected N.graph)
    (A : Finset V) (hout : ∃ w, w ∉ A) (hc : (N.cut A).card ≤ 2) :
    A.card ≤ (N.cut A).card := by
  let p : E → V := fun e => if N.tail e ∈ A then N.tail e else N.head e
  let S := (N.cut A).image p
  have hS : S.card ≤ 2 := (Finset.card_image_le).trans hc
  have hSA : S ⊆ A := by
    intro v hv
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
    rcases (N.mem_cut A e).mp he with ⟨ht,hh⟩ | ⟨hh,ht⟩
    · simpa only [p, ite_eq_left ht] using ht
    · simpa only [p, ite_eq_right ht] using hh
  have hsubset : A ⊆ S := by
    apply boundary_cover_of_threeConnected h A S hS hSA hout
    intro v hv w hw hvw
    obtain ⟨_, e, he⟩ := hvw
    apply Finset.mem_image.mpr
    rcases he with ⟨ht,hh⟩ | ⟨ht,hh⟩
    · refine ⟨e, (N.mem_cut A e).mpr (Or.inl ?_), ?_⟩
      · simpa only [ht,hh] using And.intro hv hw
      · simp only [p, ht, hv, ite_true]
    · refine ⟨e, (N.mem_cut A e).mpr (Or.inr ?_), ?_⟩
      · simpa only [ht,hh] using And.intro hv hw
      · simp only [p, ht, hh, hw, ite_false]
  exact (Finset.card_le_card hsubset).trans Finset.card_image_le

lemma cut_card_three (h : ThreeVertexConnected N.graph)
    (hV : 5 ≤ Fintype.card V) (A : Finset V) (hin : A.Nonempty)
    (hout : ∃ w, w ∉ A) : 3 ≤ (N.cut A).card := by
  by_contra hc
  have hc' : (N.cut A).card ≤ 2 := by omega
  have ha := N.region_card_le_cut h A hout hc'
  have hccompl : (N.cut Aᶜ).card ≤ 2 := by simpa only [cut_compl] using hc'
  have hb := N.region_card_le_cut h Aᶜ (by
    obtain ⟨v,hv⟩ := hin; exact ⟨v, by simpa only [Finset.mem_compl, not_not] using hv⟩) hccompl
  rw [cut_compl] at hb
  have he := Finset.card_add_card_compl A
  omega

lemma gradient_small_support (h : ThreeVertexConnected N.graph)
    (hV : 5 ≤ Fintype.card V) (f : V → ℝ) (s : Finset E) (hs : s.card ≤ 2)
    (hf : ∀ e, e ∉ s → N.gradient f e = 0) : N.gradient f = 0 := by
  ext e
  by_contra he
  have hne : f (N.head e) ≠ f (N.tail e) := by
    simpa only [gradient_apply, Pi.zero_apply, sub_eq_zero] using he
  let A := Finset.univ.filter fun v => f v = f (N.tail e)
  have hin : A.Nonempty := ⟨N.tail e, by simp [A]⟩
  have hout : ∃ w, w ∉ A := ⟨N.head e, by simp [A, hne]⟩
  have hsub : N.cut A ⊆ s := by
    intro k hk
    by_contra hks
    have hg : f (N.head k) = f (N.tail k) := sub_eq_zero.mp (hf k hks)
    rcases (N.mem_cut A k).mp hk with ⟨ht,hh⟩ | ⟨hh,ht⟩
    · apply hh; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      exact hg.trans ht
    · apply ht; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
      exact hg.symm.trans hh
  have h₁ := N.cut_card_three h hV A hin hout
  have h₂ := Finset.card_le_card hsub
  omega

end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} (N : Network V E)

structure Simple : Prop where
  loopless : ∀ e, N.tail e ≠ N.head e
  pair_injective : Function.Injective (fun e => s(N.tail e, N.head e))

def basisVec (e : E) : E → ℝ := fun k => if k = e then 1 else 0

variable [Fintype V] [Fintype E]
omit [Fintype V] in
lemma boundary_basis (e : E) : N.boundary (basisVec e) = fun v => N.incidence v e := by
  ext v
  rw [boundary_apply, Finset.sum_eq_single e]
  · simp [basisVec, incidence]
  · intro k _ hke; simp [basisVec, hke]
  · simp

variable {F : Type*} [Fintype F] (D : Network F E)

omit [Fintype F] in

theorem Duality.simple_dual (h : N.Duality D)
    (h3 : ThreeVertexConnected N.graph) (hV : 5 ≤ Fintype.card V) : D.Simple := by
  have lift_zero (x : E → ℝ) (hx : D.boundary x = 0)
      (s : Finset E) (hs : s.card ≤ 2) (hxs : ∀ e, e ∉ s → x e = 0) : x = 0 := by
    have hx' : x ∈ N.gradient.range := by rw [← h.dual_cycles_eq_cuts]; exact hx
    obtain ⟨f,hf⟩ := hx'
    rw [← hf]
    exact N.gradient_small_support h3 hV f s hs (by simpa only [hf] using hxs)
  refine ⟨?_, ?_⟩
  · intro e he
    have hz : D.boundary (basisVec e) = 0 := by
      rw [D.boundary_basis]
      ext v
      simp [incidence, he]
    have hzero := lift_zero (basisVec e) hz {e} (by simp) (by
      intro k hk; simp only [Finset.mem_singleton] at hk; simp [basisVec, hk])
    have hh := congrFun hzero e
    norm_num [basisVec] at hh
  · intro e f hef
    by_contra hne
    rcases Sym2.eq_iff.mp hef with ⟨ht,hh⟩ | ⟨ht,hh⟩
    · have hz : D.boundary (basisVec e - basisVec f) = 0 := by
        rw [map_sub, D.boundary_basis, D.boundary_basis]
        ext v
        simp [incidence, ht, hh]
      have hzero := lift_zero (basisVec e - basisVec f) hz {e,f}
        (by simpa using Finset.card_insert_le e ({f} : Finset E))
        (by intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
            simp [basisVec, hk.1, hk.2])
      have hv := congrFun hzero e
      norm_num [basisVec, hne] at hv
    · have hz : D.boundary (basisVec e + basisVec f) = 0 := by
        rw [map_add, D.boundary_basis, D.boundary_basis]
        ext v
        dsimp [incidence]
        rw [ht, hh]
        ring
      have hzero := lift_zero (basisVec e + basisVec f) hz {e,f}
        (by simpa using Finset.card_insert_le e ({f} : Finset E))
        (by intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
            simp [basisVec, hk.1, hk.2])
      have hv := congrFun hzero e
      norm_num [basisVec, hne] at hv

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] [Fintype E] in
def Incident (e : E) (v : V) : Prop := N.tail e = v ∨ N.head e = v

omit [Fintype V] [Fintype E] in
lemma incident_iff_mem_pair (e : E) (v : V) :
    N.Incident e v ↔ v ∈ s(N.tail e, N.head e) := by
  simp only [Incident, Sym2.mem_iff]
  tauto

omit [Fintype V] [Fintype E] in
lemma pair_eq_of_incident {e : E} {v w : V} (hne : v ≠ w)
    (hv : N.Incident e v) (hw : N.Incident e w) : s(N.tail e,N.head e) = s(v,w) := by
  rcases hv with ht | hh <;> rcases hw with ht' | hh'
  · exact (hne (ht.symm.trans ht')).elim
  · rw [ht,hh']
  · rw [ht',hh,Sym2.eq_swap]
  · exact (hne (hh.symm.trans hh')).elim

omit [Fintype V] [Fintype E] in
lemma Simple.incident_other (h : N.Simple) {e : E} {v : V} (hi : N.Incident e v) :
    ∃ w, v ≠ w ∧ s(N.tail e,N.head e) = s(v,w) := by
  rcases hi with ht | hh
  · exact ⟨N.head e, ht ▸ h.loopless e, by rw [ht]⟩
  · exact ⟨N.tail e, hh ▸ (h.loopless e).symm, by rw [hh,Sym2.eq_swap]⟩

def flowSupport (_N : Network V E) (x : E → ℝ) : Finset E := Finset.univ.filter fun e => x e ≠ 0

omit [Fintype V] in
@[simp] lemma mem_flowSupport (x : E → ℝ) (e : E) :
    e ∈ N.flowSupport x ↔ x e ≠ 0 := by simp [flowSupport]

omit [Fintype V] in

lemma flow_no_leaf (hN : N.Simple) (x : E → ℝ) (hx : N.boundary x = 0)
    {e : E} {v : V} (he : x e ≠ 0) (hev : N.Incident e v) :
    ∃ f, f ≠ e ∧ x f ≠ 0 ∧ N.Incident f v := by
  by_contra hn
  have other (f : E) (hfe : f ≠ e) :
      (if N.head f = v then x f else 0) - (if N.tail f = v then x f else 0) = 0 := by
    by_cases hxf : x f = 0
    · simp [hxf]
    · have hif : ¬N.Incident f v := fun hf => hn ⟨f,hfe,hxf,hf⟩
      have hh : N.head f ≠ v := fun h => hif (Or.inr h)
      have ht : N.tail f ≠ v := fun h => hif (Or.inl h)
      simp [hh,ht]
  have hz := congrFun hx v
  rw [boundary_apply, Finset.sum_eq_single e] at hz
  · rcases hev with ht | hh
    · have hh : N.head e ≠ v := fun hh => (hN.loopless e) (ht.trans hh.symm)
      simp only [hh, ht, ite_false, ite_true, zero_sub, Pi.zero_apply, neg_eq_zero] at hz
      exact he hz
    · have ht : N.tail e ≠ v := fun ht => (hN.loopless e) (ht.trans hh.symm)
      simp only [hh, ht, ite_false, ite_true, sub_zero, Pi.zero_apply] at hz
      exact he hz
  · intro f _ hfe; exact other f hfe
  · simp

structure Triangle (s : Finset E) where
  corner : Fin 3 → V
  corner_injective : Function.Injective corner
  edge : Fin 3 → E
  edge_injective : Function.Injective edge
  edge_range : Finset.univ.image edge = s
  edge_ends : ∀ i, s(N.tail (edge i), N.head (edge i)) = s(corner i, corner (i+1))

omit [Fintype V] in

theorem triangle_of_flow (hN : N.Simple) (x : E → ℝ) (hx : N.boundary x = 0)
    (hs : (N.flowSupport x).card = 3) : Nonempty (N.Triangle (N.flowSupport x)) := by
  let s := N.flowSupport x
  have hspos : s.Nonempty := Finset.card_pos.mp (by dsimp [s]; omega)
  obtain ⟨e,he⟩ := hspos
  have hxe : x e ≠ 0 := (N.mem_flowSupport x e).mp he
  let a := N.tail e
  let b := N.head e
  have hab : a ≠ b := hN.loopless e
  obtain ⟨f,hfe,hxf,hfa⟩ := N.flow_no_leaf hN x hx hxe (Or.inl rfl)
  have hf : f ∈ s := (N.mem_flowSupport x f).mpr hxf
  obtain ⟨c,hac,hfc⟩ := hN.incident_other N hfa
  have hbc : b ≠ c := by
    intro hbc
    have hef : e = f := hN.pair_injective (by dsimp [a,b] at hfc ⊢; rw [hfc, ← hbc])
    exact hfe hef.symm
  have hferase : f ∈ s.erase e := Finset.mem_erase.mpr ⟨hfe,hf⟩
  have hrest : ((s.erase e).erase f).card = 1 := by
    rw [Finset.card_erase_of_mem hferase, Finset.card_erase_of_mem he]
    dsimp [s]; omega
  obtain ⟨g,hg⟩ := Finset.card_eq_one.mp hrest
  have hsEq : s = {e,f,g} := by
    calc s = insert e (s.erase e) := (Finset.insert_erase he).symm
         _ = insert e (insert f ((s.erase e).erase f)) := by rw [Finset.insert_erase hferase]
         _ = _ := by rw [hg]
  have hgmem : g ∈ (s.erase e).erase f := by rw [hg]; simp
  obtain ⟨hgf,hge,hgs⟩ := by
    simpa only [Finset.mem_erase, and_assoc] using hgmem
  have fnotb : ¬N.Incident f b := by
    rw [N.incident_iff_mem_pair, hfc]
    simp only [Sym2.mem_iff]
    exact fun h => h.elim (fun h => hab h.symm) hbc
  have enotc : ¬N.Incident e c := by
    rw [N.incident_iff_mem_pair]
    show ¬(c ∈ s(a,b))
    simp only [Sym2.mem_iff]
    exact fun h => h.elim (fun h => hac h.symm) (fun h => hbc h.symm)
  have hgb : N.Incident g b := by
    obtain ⟨k,hke,hxk,hkb⟩ := N.flow_no_leaf hN x hx hxe (Or.inr rfl)
    have hk : k ∈ s := (N.mem_flowSupport x k).mpr hxk
    rw [hsEq] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact (hke rfl).elim
    · exact (fnotb hkb).elim
    · exact hkb
  have hgc : N.Incident g c := by
    have hfc' : N.Incident f c := (N.incident_iff_mem_pair f c).mpr (by rw [hfc]; simp)
    obtain ⟨k,hkf,hxk,hkc⟩ := N.flow_no_leaf hN x hx hxf hfc'
    have hk : k ∈ s := (N.mem_flowSupport x k).mpr hxk
    rw [hsEq] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact (enotc hkc).elim
    · exact (hkf rfl).elim
    · exact hkc
  have hgend := N.pair_eq_of_incident hbc hgb hgc
  refine ⟨{
    corner := ![a,b,c]
    corner_injective := ?_
    edge := ![e,g,f]
    edge_injective := ?_
    edge_range := ?_
    edge_ends := ?_ }⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> dsimp at hij <;> first | rfl | exact (hab hij).elim | exact (hab hij.symm).elim | exact (hac hij).elim | exact (hac hij.symm).elim | exact (hbc hij).elim | exact (hbc hij.symm).elim
  · intro i j hij
    fin_cases i <;> fin_cases j <;> dsimp at hij <;> first | rfl | exact (hge hij).elim | exact (hge hij.symm).elim | exact (hfe hij).elim | exact (hfe hij.symm).elim | exact (hgf hij).elim | exact (hgf hij.symm).elim
  · change Finset.univ.image ![e,g,f] = s
    rw [hsEq]
    ext k
    simp [Fin.exists_fin_succ]
    tauto
  · intro i
    fin_cases i
    · rfl
    · exact hgend
    · change s(N.tail f, N.head f) = s(c,a)
      exact hfc.trans Sym2.eq_swap

end
end Barnette.Network

end OAI


namespace OAI

/-! Minimal flow circuits, triangular faces, and simple cycle coordinates. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

structure FlowCircuit (x : E → ℝ) : Prop where
  conserved : N.boundary x = 0
  nonzero : x ≠ 0
  minimal : ∀ y, N.boundary y = 0 → N.flowSupport y ⊆ N.flowSupport x →
    y = 0 ∨ N.flowSupport y = N.flowSupport x

omit [Fintype V] in
lemma flowSupport_eq_empty_iff (x : E → ℝ) : N.flowSupport x = ∅ ↔ x = 0 := by
  simp only [Finset.eq_empty_iff_forall_notMem, mem_flowSupport, not_not,
    funext_iff, Pi.zero_apply]

omit [Fintype V] [Fintype F] in
lemma Duality.dual_conserved_gradient (h : N.Duality D) (f : V → ℝ) :
    D.boundary (N.gradient f) = 0 := by
  have hh : N.gradient f ∈ N.gradient.range := ⟨f,rfl⟩
  rwa [← h.dual_cycles_eq_cuts] at hh

omit [Fintype V] [Fintype F] in
lemma Duality.gradient_of_dual_conserved (h : N.Duality D) {x : E → ℝ}
    (hx : D.boundary x = 0) : ∃ f, N.gradient f = x := by
  have hh : x ∈ D.boundary.ker := hx
  rwa [h.dual_cycles_eq_cuts] at hh

omit [Fintype V] [Fintype F] in

theorem Duality.circuit_two_levels (h : N.Duality D) (x : E → ℝ)
    (hx : D.FlowCircuit x) (f : V → ℝ) (hf : N.gradient f = x)
    {e : E} (he : x e ≠ 0) :
    ∀ v, f v = f (N.tail e) ∨ f v = f (N.head e) := by
  have he' : f (N.head e) ≠ f (N.tail e) := by
    simpa only [← hf, gradient_apply, sub_ne_zero] using he
  intro v
  by_contra hv
  obtain ⟨hvt,hvh⟩ := not_or.mp hv
  let g : V → ℝ := fun w => if f w = f v then 1 else 0
  have hgsub : D.flowSupport (N.gradient g) ⊆ D.flowSupport x := by
    intro k hk
    apply (D.mem_flowSupport x k).mpr
    intro hxk
    have hfk : f (N.head k) = f (N.tail k) := by
      apply sub_eq_zero.mp
      simpa only [← hf, gradient_apply] using hxk
    have hgk : N.gradient g k = 0 := by simp only [gradient_apply, g, hfk, sub_self]
    exact (D.mem_flowSupport _ k).mp hk hgk
  have hg : N.gradient g ≠ 0 := by
    intro hg
    have hh := N.gradient_zero_reachable hg (h.connected v (N.tail e))
    have htv : f (N.tail e) ≠ f v := Ne.symm hvt
    norm_num [g,htv] at hh
  have hgs := (hx.minimal (N.gradient g) (h.dual_conserved_gradient N D g) hgsub).resolve_left hg
  have hek : N.gradient g e ≠ 0 := (D.mem_flowSupport _ e).mp (by
    rw [hgs]; exact (D.mem_flowSupport _ e).mpr he)
  have htv : f (N.tail e) ≠ f v := Ne.symm hvt
  have hhv : f (N.head e) ≠ f v := Ne.symm hvh
  exact hek (by simp [gradient_apply, g, htv, hhv])

omit [Fintype F] in

theorem Duality.circuit_cut (h : N.Duality D) (x : E → ℝ)
    (hx : D.FlowCircuit x) (root : V) :
    ∃ (A : Finset V) (c : ℝ), A.Nonempty ∧ root ∉ A ∧ c ≠ 0 ∧
      x = c • N.gradient (fun v => if v ∈ A then 1 else 0) ∧
      N.cut A = D.flowSupport x := by
  obtain ⟨f,hf⟩ := h.gradient_of_dual_conserved N D hx.conserved
  obtain ⟨e,he⟩ : ∃ e, x e ≠ 0 := by
    by_contra hn
    apply hx.nonzero
    ext e
    exact not_not.mp (fun he => hn ⟨e,he⟩)
  have he' : f (N.head e) ≠ f (N.tail e) := by
    simpa only [← hf, gradient_apply, sub_ne_zero] using he
  have hall := h.circuit_two_levels N D x hx f hf he
  let a := f root
  let b := if a = f (N.tail e) then f (N.head e) else f (N.tail e)
  have hab : b ≠ a := by
    dsimp [b,a]
    split_ifs with ha
    · rw [ha]; exact he'
    · exact Ne.symm ha
  have hlevels (v : V) : f v = a ∨ f v = b := by
    dsimp [b,a] at ⊢
    rcases hall root with ht | hh
    · rw [ite_eq_left ht,ht]; exact hall v
    · have ht : f root ≠ f (N.tail e) := hh ▸ he'
      rw [ite_eq_right ht,hh]
      exact (hall v).symm
  have hb : ∃ v, f v = b := by
    dsimp [b]
    split_ifs
    · exact ⟨N.head e,rfl⟩
    · exact ⟨N.tail e,rfl⟩
  let A := Finset.univ.filter fun v => f v = b
  have fform (v : V) : f v = a + (b-a) * (if v ∈ A then 1 else 0) := by
    rcases hlevels v with hv | hv
    · have hvA : v ∉ A := by simp [A,hv,Ne.symm hab]
      simp [hvA,hv]
    · have hvA : v ∈ A := by simp [A,hv]
      simp [hvA,hv]
  refine ⟨A,b-a,?_,?_,sub_ne_zero.mpr hab,?_,?_⟩
  · obtain ⟨v,hv⟩ := hb; exact ⟨v,by simp [A,hv]⟩
  · simp [A,show f root = a from rfl, Ne.symm hab]
  · rw [← hf]
    ext k
    simp only [gradient_apply, Pi.smul_apply, smul_eq_mul]
    rw [fform (N.head k), fform (N.tail k)]
    ring
  · ext k
    simp only [mem_cut, mem_flowSupport, ← hf, gradient_apply, sub_ne_zero]
    rw [fform (N.head k), fform (N.tail k)]
    by_cases ht : N.tail k ∈ A <;> by_cases hh : N.head k ∈ A <;>
      simp [ht,hh,hab,Ne.symm hab]

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] in
def star (v : V) : Finset E := Finset.univ.filter fun e => N.Incident e v

omit [Fintype V] in
@[simp] lemma mem_star (e : E) (v : V) : e ∈ N.star v ↔ N.Incident e v := by
  simp [star]

omit [Fintype V] in
def otherEnd (e : E) (v : V) : V := if N.tail e = v then N.head e else N.tail e

omit [Fintype V] [Fintype E] in
lemma otherEnd_spec (h : N.Simple) {e : E} {v : V} (hi : N.Incident e v) :
    v ≠ N.otherEnd e v ∧ s(N.tail e,N.head e) = s(v,N.otherEnd e v) := by
  rcases hi with ht | hh
  · rw [otherEnd,ite_eq_left ht]
    exact ⟨ht ▸ h.loopless e, by rw [ht]⟩
  · by_cases ht : N.tail e = v
    · exact (h.loopless e (ht.trans hh.symm)).elim
    · rw [otherEnd,ite_eq_right ht]
      exact ⟨hh ▸ (h.loopless e).symm, by rw [hh,Sym2.eq_swap]⟩

omit [Fintype V] [Fintype E] in
lemma otherEnd_adj (h : N.Simple) {e : E} {v : V} (hi : N.Incident e v) :
    N.graph.Adj v (N.otherEnd e v) := by
  obtain ⟨hne,he⟩ := N.otherEnd_spec h hi
  exact ⟨hne,e,Sym2.eq_iff.mp he⟩

lemma card_star (h : N.Simple) (v : V) : (N.star v).card = N.graph.degree v := by
  let f : {e // e ∈ N.star v} → N.graph.neighborSet v := fun e =>
    ⟨N.otherEnd e.val v, N.otherEnd_adj h ((N.mem_star _ _).mp e.property)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro e k hek
      apply Subtype.ext
      apply h.pair_injective
      change s(N.tail e.val, N.head e.val) = s(N.tail k.val, N.head k.val)
      rw [(N.otherEnd_spec h ((N.mem_star _ _).mp e.property)).2,
        (N.otherEnd_spec h ((N.mem_star _ _).mp k.property)).2]
      exact congrArg (fun w => s(v,w)) (congrArg Subtype.val hek)
    · intro w
      obtain ⟨hne,e,he⟩ := w.property
      have hi : N.Incident e v := he.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
      refine ⟨⟨e,(N.mem_star _ _).mpr hi⟩,Subtype.ext ?_⟩
      change N.otherEnd e v = w.val
      rcases he with ⟨ht,hh⟩ | ⟨ht,hh⟩
      · simp only [otherEnd,ht,ite_true,hh]
      · have ht' : N.tail e ≠ v := by rw [ht]; exact hne.symm
        rw [otherEnd,ite_eq_right ht',ht]
  have hh := Fintype.card_congr (Equiv.ofBijective f hf)
  simpa only [Fintype.card_coe, SimpleGraph.card_neighborSet_eq_degree] using hh

omit [Fintype V] [Fintype F] in
lemma gradient_indicator_support (h : N.Simple) (v : V) :
    D.flowSupport (N.gradient (fun w => if w = v then 1 else 0)) = N.star v := by
  ext e
  simp only [mem_flowSupport, mem_star, gradient_apply, Incident]
  have hne := h.loopless e
  by_cases ht : N.tail e = v <;> by_cases hh : N.head e = v <;> simp [ht,hh] at *

omit [Fintype F] in

theorem Duality.cubic_face_triangles (h : N.Duality D) (hN : N.Simple)
    (h3 : ThreeVertexConnected N.graph) (hV : 5 ≤ Fintype.card V)
    (hc : N.graph.IsRegularOfDegree 3) : ∀ v, Nonempty (D.Triangle (N.star v)) := by
  intro v
  have hD := h.simple_dual N D h3 hV
  have hx := h.dual_conserved_gradient N D (fun w => if w = v then 1 else 0)
  have hs : (D.flowSupport (N.gradient (fun w => if w = v then 1 else 0))).card = 3 := by
    rw [N.gradient_indicator_support D hN, N.card_star hN, hc v]
  simpa only [N.gradient_indicator_support D hN] using D.triangle_of_flow hD _ hx hs

end
end Barnette.Network
namespace Barnette

open Fin.NatCast

theorem cyclic_propagation {n : ℕ} [NeZero n] (P : Fin n → Prop)
    (hstep : ∀ i, P (i + 1) → P i) {q : Fin n} (hq : P q) : ∀ i, P i := by
  have h : ∀ k : ℕ, P (q - (k : Fin n)) := by
    intro k
    induction k with
    | zero => simpa using hq
    | succ k hk =>
      apply hstep (q - ((k + 1 : ℕ) : Fin n))
      simpa only [Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub, sub_add_cancel] using hk
  intro i
  simpa only [Fin.cast_val_eq_self, sub_sub_cancel] using h (q - i).val

theorem cyclic_one_ne_zero (n : ℕ) : (1 : Fin (n + 3)) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp at this

theorem cyclic_two_ne_zero (n : ℕ) : (2 : Fin (n + 3)) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp [Nat.mod_eq_of_lt (show 2 < n + 3 by omega)] at this

structure CycleCoordinates {V : Type*} (G : SimpleGraph V) where
  n : ℕ
  vertex : Fin (n + 3) ↪ V
  adjacent : ∀ i, G.Adj (vertex i) (vertex (i + 1))

namespace CycleCoordinates

variable {V : Type*} {G : SimpleGraph V} (C : CycleCoordinates G)

theorem edge_indices_unique (i j : Fin (C.n + 3))
    (h : (C.vertex i = C.vertex j ∧ C.vertex (i + 1) = C.vertex (j + 1)) ∨
      (C.vertex i = C.vertex (j + 1) ∧ C.vertex (i + 1) = C.vertex j)) : i = j := by
  rcases h with h | h
  · exact C.vertex.injective h.1
  · have hi := C.vertex.injective h.1
    have hj := C.vertex.injective h.2
    have hh : (2 : Fin (C.n + 3)) = 0 := by
      have : j + (1 + 1) = j + 0 := by simpa [hi, add_assoc] using hj
      simpa only [show (1 : Fin (C.n + 3)) + 1 = 2 by
        apply Fin.ext
        simp [Fin.val_add, Nat.mod_eq_of_lt (show 2 < C.n + 3 by omega)]] using (add_left_cancel this)
    exact (cyclic_two_ne_zero C.n hh).elim

theorem tail_orientation {A : Type*} (face : Fin (C.n + 3) ↪ A)
    (tail : A → V) (htail : Function.Injective tail)
    (hend : ∀ i, tail (face i) = C.vertex i ∨ tail (face i) = C.vertex (i + 1)) :
    (∀ i, tail (face i) = C.vertex i) ∨
      (∀ i, tail (face i) = C.vertex (i + 1)) := by
  classical
  by_cases h : ∃ q, tail (face q) = C.vertex q
  · obtain ⟨q, hq⟩ := h
    left
    apply cyclic_propagation (fun i => tail (face i) = C.vertex i) _ hq
    intro i hi
    rcases hend i with h | h
    · exact h
    · have heq : face i = face (i + 1) := htail (h.trans hi.symm)
      have hi1 := face.injective heq
      have hbad : (1 : Fin (C.n + 3)) = 0 := by
        exact add_left_cancel (by simpa using hi1.symm : i + 1 = i + 0)
      exact (cyclic_one_ne_zero C.n hbad).elim
  · right
    intro i
    exact (hend i).resolve_left (fun hi => h ⟨i, hi⟩)

end CycleCoordinates
end Barnette

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E]
  (N : Network V E) (C : Barnette.CycleCoordinates N.graph)

omit [Fintype V] [Fintype E] in
def cycleEdge (i : Fin (C.n+3)) : E := (C.adjacent i).2.choose

omit [Fintype V] [Fintype E] in
lemma cycleEdge_ends (i : Fin (C.n+3)) :
    s(N.tail (N.cycleEdge C i),N.head (N.cycleEdge C i)) = s(C.vertex i,C.vertex (i+1)) :=
  Sym2.eq_iff.mpr (C.adjacent i).2.choose_spec

omit [Fintype V] [Fintype E] in
lemma cycleEdge_injective : Function.Injective (N.cycleEdge C) := by
  intro i j hij
  apply C.edge_indices_unique i j
  apply Sym2.eq_iff.mp
  rw [← N.cycleEdge_ends C i, ← N.cycleEdge_ends C j, hij]

omit [Fintype V] [Fintype E] in
lemma cycleEdge_incident (i : Fin (C.n+3)) (v : V) :
    N.Incident (N.cycleEdge C i) v ↔ v = C.vertex i ∨ v = C.vertex (i+1) := by
  rw [N.incident_iff_mem_pair, N.cycleEdge_ends]
  exact Sym2.mem_iff

omit [Fintype V] [Fintype E] in
def cycleEdges : Finset E := Finset.univ.image (N.cycleEdge C)

omit [Fintype V] [Fintype E] in
@[simp] lemma mem_cycleEdges (e : E) : e ∈ N.cycleEdges C ↔ ∃ i, N.cycleEdge C i = e := by
  simp [cycleEdges]

omit [Fintype V] in

lemma cycle_support_minimal (hN : N.Simple) (y : E → ℝ) (hy : N.boundary y = 0)
    (hsub : N.flowSupport y ⊆ N.cycleEdges C) (hne : y ≠ 0) :
    N.flowSupport y = N.cycleEdges C := by
  have hs : (N.flowSupport y).Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    exact fun h => hne ((N.flowSupport_eq_empty_iff y).mp h))
  obtain ⟨e,he⟩ := hs
  obtain ⟨q,hq⟩ := (N.mem_cycleEdges C e).mp (hsub he)
  have hq' : y (N.cycleEdge C q) ≠ 0 := by rw [hq]; exact (N.mem_flowSupport _ _).mp he
  have hall : ∀ i, y (N.cycleEdge C i) ≠ 0 := by
    apply Barnette.cyclic_propagation (fun i => y (N.cycleEdge C i) ≠ 0) _ hq'
    intro i hi
    have hv : N.Incident (N.cycleEdge C (i+1)) (C.vertex (i+1)) :=
      (N.cycleEdge_incident C _ _).mpr (Or.inl rfl)
    obtain ⟨f,hfe,hyf,hfv⟩ := N.flow_no_leaf hN y hy hi hv
    obtain ⟨j,rfl⟩ := (N.mem_cycleEdges C f).mp (hsub ((N.mem_flowSupport y f).mpr hyf))
    rcases (N.cycleEdge_incident C j _).mp hfv with hj | hj
    · have hj' := C.vertex.injective hj
      exact (hfe (congrArg (N.cycleEdge C) hj'.symm)).elim
    · have hj' := add_right_cancel (C.vertex.injective hj)
      simpa only [← hj'] using hyf
  apply Finset.Subset.antisymm hsub
  intro e he
  obtain ⟨i,rfl⟩ := (N.mem_cycleEdges C e).mp he
  exact (N.mem_flowSupport y _).mpr (hall i)

omit [Fintype V] in
lemma flowCircuit_of_cycle (hN : N.Simple) (x : E → ℝ)
    (hx : N.boundary x = 0) (hs : N.flowSupport x = N.cycleEdges C) : N.FlowCircuit x := by
  have hcs : (N.cycleEdges C).Nonempty := ⟨N.cycleEdge C 0, by simp⟩
  refine ⟨hx,?_,?_⟩
  · intro hz; subst x
    have he := (N.flowSupport_eq_empty_iff 0).mpr rfl
    rw [he] at hs
    exact hcs.ne_empty hs.symm
  · intro y hy hsub
    by_cases hzero : y = 0
    · exact Or.inl hzero
    · right
      rw [hs] at hsub ⊢
      exact N.cycle_support_minimal C hN y hy hsub hzero

end
end Barnette.Network

end OAI


namespace OAI

/-! Cycle flows, minimal cuts, and connected shores. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E]
  (N : Network V E) (C : Barnette.CycleCoordinates N.graph)

omit [Fintype V] [Fintype E] in
def arcSign (e : E) (v : V) : ℝ := if N.tail e = v then 1 else -1

omit [Fintype V] [Fintype E] in
lemma arcSign_ne_zero (e : E) (v : V) : N.arcSign e v ≠ 0 := by
  simp only [arcSign]; split_ifs <;> norm_num

omit [Fintype V] in
lemma boundary_directed_unit {e : E} {v w : V} (hne : v ≠ w)
    (he : s(N.tail e,N.head e) = s(v,w)) :
    N.boundary (N.arcSign e v • basisVec e) =
      fun z => (if z = w then 1 else 0) - (if z = v then 1 else 0) := by
  rw [map_smul, N.boundary_basis]
  ext z
  rcases Sym2.eq_iff.mp he with ⟨ht,hh⟩ | ⟨ht,hh⟩
  · simp only [Pi.smul_apply, smul_eq_mul, incidence, arcSign, ht, hh, ite_true, one_mul]
    congr 1 <;> simp only [eq_comm]
  · have htv : N.tail e ≠ v := by rw [ht]; exact hne.symm
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [arcSign, ite_eq_right htv]
    simp only [incidence, ht, hh, neg_one_mul, neg_sub]
    congr 1 <;> simp only [eq_comm]

omit [Fintype V] [Fintype E] in
def cycleFlow : E → ℝ :=
  ∑ i, N.arcSign (N.cycleEdge C i) (C.vertex i) • basisVec (N.cycleEdge C i)

omit [Fintype V] in
lemma cycleFlow_conserved : N.boundary (N.cycleFlow C) = 0 := by
  rw [cycleFlow,map_sum]
  have hi (i : Fin (C.n+3)) :
      N.boundary (N.arcSign (N.cycleEdge C i) (C.vertex i) • basisVec (N.cycleEdge C i)) =
        fun z => (if z = C.vertex (i+1) then 1 else 0) - (if z = C.vertex i then 1 else 0) :=
    N.boundary_directed_unit (C.adjacent i).ne (N.cycleEdge_ends C i)
  simp_rw [hi]
  ext z
  simp only [Finset.sum_apply, Pi.zero_apply, Finset.sum_sub_distrib]
  apply sub_eq_zero.mpr
  exact Equiv.sum_comp (Equiv.addRight (1 : Fin (C.n+3))) (fun i => if z = C.vertex i then (1:ℝ) else 0)

omit [Fintype V] [Fintype E] in
lemma cycleFlow_apply_edge (i : Fin (C.n+3)) :
    N.cycleFlow C (N.cycleEdge C i) = N.arcSign (N.cycleEdge C i) (C.vertex i) := by
  simp only [cycleFlow, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, basisVec]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne : N.cycleEdge C i ≠ N.cycleEdge C j := fun h => hji ((N.cycleEdge_injective C h).symm)
    simp [hne]
  · simp

omit [Fintype V] [Fintype E] in
lemma cycleFlow_zero_outside {e : E} (he : e ∉ N.cycleEdges C) : N.cycleFlow C e = 0 := by
  have hi : ∀ i, e ≠ N.cycleEdge C i := by
    intro i h
    apply he
    exact (N.mem_cycleEdges C e).mpr ⟨i,h.symm⟩
  simp only [cycleFlow, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, basisVec, hi,
    ite_false, mul_zero, Finset.sum_const_zero]

omit [Fintype V] in
lemma cycleFlow_support : N.flowSupport (N.cycleFlow C) = N.cycleEdges C := by
  ext e
  constructor
  · intro he
    by_contra hn
    exact (N.mem_flowSupport _ _).mp he (N.cycleFlow_zero_outside C hn)
  · intro he
    obtain ⟨i,rfl⟩ := (N.mem_cycleEdges C e).mp he
    rw [mem_flowSupport, N.cycleFlow_apply_edge]
    exact N.arcSign_ne_zero _ _

omit [Fintype V] in
lemma cycleFlow_circuit (hN : N.Simple) : N.FlowCircuit (N.cycleFlow C) :=
  N.flowCircuit_of_cycle C hN _ (N.cycleFlow_conserved C) (N.cycleFlow_support C)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype F] in
lemma support_cut (A : Finset V) :
    D.flowSupport (N.gradient (fun v => if v ∈ A then 1 else 0)) = N.cut A := by
  ext e
  simp only [mem_flowSupport,mem_cut,gradient_apply]
  by_cases ht : N.tail e ∈ A <;> by_cases hh : N.head e ∈ A <;> simp [ht,hh]

structure Bond (A : Finset V) : Prop where
  nonempty : (N.cut A).Nonempty
  minimal : ∀ B, N.cut B ⊆ N.cut A → N.cut B = ∅ ∨ N.cut B = N.cut A

omit [Fintype V] [Fintype F] in
lemma Duality.bond_of_circuit (h : N.Duality D) (x : E → ℝ) (hx : D.FlowCircuit x)
    (A : Finset V) (hA : N.cut A = D.flowSupport x) : N.Bond A := by
  refine ⟨?_,?_⟩
  · rw [hA]
    apply Finset.nonempty_iff_ne_empty.mpr
    exact fun he => hx.nonzero ((D.flowSupport_eq_empty_iff x).mp he)
  · intro B hB
    let y := N.gradient (fun v => if v ∈ B then 1 else 0)
    have hy : D.flowSupport y = N.cut B := N.support_cut D B
    have hys : D.flowSupport y ⊆ D.flowSupport x := by rwa [hy,← hA]
    rcases hx.minimal y (h.dual_conserved_gradient N D _) hys with hzero | heq
    · left
      rw [← hy]
      exact (D.flowSupport_eq_empty_iff y).mpr hzero
    · right
      rwa [hy,← hA] at heq

omit [Fintype V] in
lemma cuts_equal_subset (h : N.graph.Connected) {A B : Finset V} (hBA : B ⊆ A)
    (hout : ∃ v, v ∉ A) (hc : N.cut B = N.cut A) : B = A := by
  let f : V → ℝ := fun v => (if v ∈ A then 1 else 0) - (if v ∈ B then 1 else 0)
  have hf : N.gradient f = 0 := by
    ext e
    have he := Finset.ext_iff.mp hc e
    simp only [mem_cut] at he
    have ht := hBA (x := N.tail e)
    have hh := hBA (x := N.head e)
    dsimp only [gradient_apply,f,Pi.zero_apply]
    by_cases hta : N.tail e ∈ A <;> by_cases hha : N.head e ∈ A <;>
      by_cases htb : N.tail e ∈ B <;> by_cases hhb : N.head e ∈ B <;>
      simp_all
  obtain ⟨r,hr⟩ := hout
  have hrB : r ∉ B := fun h => hr (hBA h)
  apply Finset.Subset.antisymm hBA
  intro v hv
  have hh := N.gradient_zero_reachable hf (h r v)
  by_contra hvB
  norm_num [f,hr,hrB,hv,hvB] at hh

omit [Fintype V] in
lemma cut_nonempty (h : N.graph.Connected) (A : Finset V) (hin : A.Nonempty)
    (hout : ∃ v, v ∉ A) : (N.cut A).Nonempty := by
  by_contra hc
  have hc' : N.cut A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hc
  have hf : N.gradient (fun v => if v ∈ A then (1:ℝ) else 0) = 0 := by
    apply (N.flowSupport_eq_empty_iff _).mp
    rwa [N.support_cut N A]
  obtain ⟨v,hv⟩ := hin
  obtain ⟨w,hw⟩ := hout
  have hh := N.gradient_zero_reachable hf (h v w)
  norm_num [hv,hw] at hh

omit [Fintype V] in

lemma Bond.connected_shore (h : N.graph.Connected) {A : Finset V} (hA : N.Bond A)
    (hin : A.Nonempty) (hout : ∃ v, v ∉ A) :
    (N.graph.induce {v | v ∈ A}).Connected := by
  obtain ⟨a,ha⟩ := hin
  let H := N.graph.induce {v | v ∈ A}
  let B := A.filter fun v => ∃ hv : v ∈ A, H.Reachable ⟨a,ha⟩ ⟨v,hv⟩
  have hBA : B ⊆ A := Finset.filter_subset _ _
  have haB : a ∈ B := Finset.mem_filter.mpr ⟨ha,ha,SimpleGraph.Reachable.refl _⟩
  have hsub : N.cut B ⊆ N.cut A := by
    intro e he
    have step {v w : V} (hv : v ∈ B) (hw : w ∈ A) (hvw : N.graph.Adj v w) : w ∈ B := by
      obtain ⟨hvA,hvR⟩ := Finset.mem_filter.mp hv
      obtain ⟨hv',hp⟩ := hvR
      exact Finset.mem_filter.mpr ⟨hw,hw,hp.trans (show H.Adj ⟨v,hv'⟩ ⟨w,hw⟩ from hvw).reachable⟩
    rcases (N.mem_cut B e).mp he with ⟨ht,hh⟩ | ⟨hh,ht⟩
    · apply (N.mem_cut A e).mpr
      refine Or.inl ⟨hBA ht,?_⟩
      intro hha
      have hne : N.tail e ≠ N.head e := fun heq => hh (heq ▸ ht)
      exact hh (step ht hha ⟨hne,e,Or.inl ⟨rfl,rfl⟩⟩)
    · apply (N.mem_cut A e).mpr
      refine Or.inr ⟨hBA hh,?_⟩
      intro hta
      have hne : N.head e ≠ N.tail e := fun heq => ht (heq ▸ hh)
      exact ht (step hh hta ⟨hne,e,Or.inr ⟨rfl,rfl⟩⟩)
  have hBout : ∃ v, v ∉ B := by
    obtain ⟨r,hr⟩ := hout
    exact ⟨r,fun h => hr (hBA h)⟩
  have hc := (hA.minimal B hsub).resolve_left (N.cut_nonempty h B ⟨a,haB⟩ hBout).ne_empty
  have hEq := N.cuts_equal_subset h hBA hout hc
  apply (SimpleGraph.connected_iff_exists_forall_reachable H).mpr
  refine ⟨⟨a,ha⟩,?_⟩
  intro v
  have hvB : v.val ∈ B := by rw [hEq]; exact v.property
  obtain ⟨_,hv,hp⟩ := Finset.mem_filter.mp hvB
  exact hp

lemma Bond.compl {A : Finset V} (hA : N.Bond A) : N.Bond Aᶜ where
  nonempty := by simpa only [cut_compl] using hA.nonempty
  minimal B hB := by
    rw [cut_compl] at hB ⊢
    exact hA.minimal B hB

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype E] [Fintype F] in
lemma Triangle.corner_iff_incident {s : Finset E} (t : D.Triangle s) (v : F) :
    v ∈ Set.range t.corner ↔ ∃ e ∈ s, D.Incident e v := by
  constructor
  · rintro ⟨i,rfl⟩
    refine ⟨t.edge i,?_,?_⟩
    · have hm : t.edge i ∈ Finset.univ.image t.edge := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
      rwa [t.edge_range] at hm
    · rw [D.incident_iff_mem_pair,t.edge_ends]; simp
  · rintro ⟨e,he,hv⟩
    rw [← t.edge_range] at he
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
    rw [D.incident_iff_mem_pair,t.edge_ends,Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · exact ⟨i,rfl⟩
    · exact ⟨i+1,rfl⟩

omit [Fintype E] [Fintype F] in
lemma Triangle.clique {s : Finset E} (t : D.Triangle s) {i j : Fin 3} (hij : i ≠ j) :
    D.graph.Adj (t.corner i) (t.corner j) := by
  have hne : t.corner i ≠ t.corner j := fun h => hij (t.corner_injective h)
  have hfin : ∀ i j : Fin 3, i ≠ j → j = i+1 ∨ i = j+1 := by decide
  have h := hfin i j hij
  rcases h with rfl | rfl
  · exact ⟨hne,t.edge i,Sym2.eq_iff.mp (t.edge_ends i)⟩
  · exact ⟨hne,t.edge j,(Sym2.eq_iff.mp (t.edge_ends j)).symm⟩

omit [Fintype E] [Fintype F] in
lemma Triangle.corner_avoiding {s : Finset E} (t : D.Triangle s) (z : F) :
    ∃ w, w ∈ Set.range t.corner ∧ w ≠ z := by
  by_cases h : t.corner 0 = z
  · refine ⟨t.corner 1,⟨1,rfl⟩,?_⟩
    intro hh
    have hi := t.corner_injective (h.trans hh.symm)
    norm_num at hi
  · exact ⟨t.corner 0,⟨0,rfl⟩,h⟩

omit [Fintype E] [Fintype F] in
lemma Triangle.reachable_avoiding {s : Finset E} (t : D.Triangle s) (z : F)
    {v w : F} (hv : v ∈ Set.range t.corner) (hw : w ∈ Set.range t.corner)
    (hvz : v ≠ z) (hwz : w ≠ z) :
    (D.graph.induce {v | v ≠ z}).Reachable ⟨v,hvz⟩ ⟨w,hwz⟩ := by
  obtain ⟨i,rfl⟩ := hv
  obtain ⟨j,rfl⟩ := hw
  by_cases hij : i = j
  · subst j; exact SimpleGraph.Reachable.refl _
  · exact (show (D.graph.induce {v | v ≠ z}).Adj ⟨t.corner i,hvz⟩ ⟨t.corner j,hwz⟩ from
      t.clique D hij).reachable

omit [Fintype V] [Fintype F] in

theorem faces_vertex_deleted_connected (hN : N.graph.Connected) (hD : D.graph.Connected)
    (sD : D.Simple) (face : ∀ v, D.Triangle (N.star v)) (z : F) :
    (D.graph.induce {v | v ≠ z}).Connected := by
  obtain ⟨v₀⟩ := hN.nonempty
  let : Nontrivial F := ⟨⟨(face v₀).corner 0,(face v₀).corner 1,by
    intro he; have hi := (face v₀).corner_injective he; norm_num at hi⟩⟩
  let H := D.graph.induce {v | v ≠ z}
  choose anchor ha hz using fun v => (face v).corner_avoiding D z
  let a (v : V) : {w : F | w ≠ z} := ⟨anchor v,hz v⟩
  have in_face (v : V) (e : E) (he : N.Incident e v) (w : F) (hw : D.Incident e w) :
      w ∈ Set.range (face v).corner :=
    ((face v).corner_iff_incident D w).mpr ⟨e,(N.mem_star e v).mpr he,hw⟩
  have step {v w : V} (hvw : N.graph.Adj v w) : H.Reachable (a v) (a w) := by
    obtain ⟨_,e,he⟩ := hvw
    have hv : N.Incident e v := he.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
    have hw : N.Incident e w := he.elim (fun h => Or.inr h.2) (fun h => Or.inl h.1)
    obtain ⟨u,hu,huz⟩ : ∃ u, D.Incident e u ∧ u ≠ z := by
      by_cases ht : D.tail e = z
      · exact ⟨D.head e,Or.inr rfl,fun hh => sD.loopless e (ht.trans hh.symm)⟩
      · exact ⟨D.tail e,Or.inl rfl,ht⟩
    have p := (face v).reachable_avoiding D z (ha v) (in_face v e hv u hu) (hz v) huz
    have q := (face w).reachable_avoiding D z (in_face w e hw u hu) (ha w) huz (hz w)
    exact p.trans q
  have all_faces {v w : V} : H.Reachable (a v) (a w) := by
    obtain ⟨p⟩ := hN v w
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | cons hvw p ih => exact (step hvw).trans ih
  apply (SimpleGraph.connected_iff_exists_forall_reachable H).mpr
  refine ⟨a v₀,?_⟩
  intro w
  obtain ⟨u,hu⟩ := hD.preconnected.exists_adj_of_nontrivial w.val
  obtain ⟨_,e,he⟩ := hu
  have hw : D.Incident e w.val := he.elim (fun he => Or.inl he.1) (fun he => Or.inr he.2)
  have hf := in_face (N.tail e) e (Or.inl rfl) w.val hw
  exact all_faces.trans ((face (N.tail e)).reachable_avoiding D z (ha _) hf (hz _) w.property)

end
end Barnette.Network

end OAI


namespace OAI

/-! Vertex quotients and connected fibers of incidence networks. -/

namespace Barnette.Network
noncomputable section
variable {V W E K : Type*}
open scoped Classical

def push [Fintype V] (q : V → W) : (V → ℝ) →ₗ[ℝ] (W → ℝ) where
  toFun x w := ∑ v, if q v = w then x v else 0
  map_add' x y := by
    ext w
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> simp
  map_smul' c x := by
    ext w
    simp [Finset.mul_sum, mul_ite]

def pull (q : V → W) : (W → ℝ) →ₗ[ℝ] (V → ℝ) :=
  LinearMap.funLeft ℝ ℝ q

@[simp] theorem pull_apply (q : V → W) (f : W → ℝ) (v : V) :
    pull q f v = f (q v) := rfl

@[simp] theorem push_apply [Fintype V] (q : V → W) (x : V → ℝ) (w : W) :
    push q x w = ∑ v, if q v = w then x v else 0 := rfl

def mapVertices (N : Network V E) (q : V → W) : Network W E :=
  ⟨q ∘ N.tail, q ∘ N.head⟩

def restrict (N : Network V E) (j : K → E) : Network V K :=
  ⟨N.tail ∘ j, N.head ∘ j⟩

@[simp] theorem gradient_mapVertices (N : Network V E) (q : V → W) (f : W → ℝ) :
    (N.mapVertices q).gradient f = N.gradient (pull q f) := rfl

@[simp] theorem gradient_restrict (N : Network V E) (j : K → E) (f : V → ℝ) :
    (N.restrict j).gradient f = pull j (N.gradient f) := rfl

variable [Fintype V] [Fintype W] [Fintype E] [Fintype K]

lemma push_adjoint (q : V → W) (x : V → ℝ) (f : W → ℝ) :
    ∑ w, push q x w * f w = ∑ v, x v * pull q f v := by
  classical
  simp only [push_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [ite_mul]

lemma push_surjective {q : V → W} (hq : Function.Surjective q) :
    Function.Surjective (push q) := by
  classical
  let r := Function.surjInv hq
  have hr : Function.RightInverse r q := Function.rightInverse_surjInv hq
  intro f
  refine ⟨fun v => if h : v ∈ Set.range r then f (q v) else 0, ?_⟩
  ext w
  simp only [push_apply]
  rw [Finset.sum_eq_single (r w)]
  · simp [hr w]
  · intro v _ hv
    by_cases h : v ∈ Set.range r
    · obtain ⟨z, rfl⟩ := h
      have hz : z ≠ w := fun he => hv (congrArg r he)
      simp [hr z, hz]
    · simp [h]
  · simp

omit [Fintype V] [Fintype W] in
lemma pull_injective {q : V → W} (hq : Function.Surjective q) :
    Function.Injective (pull q) := by
  intro f g h
  ext w
  obtain ⟨v, rfl⟩ := hq w
  exact congrFun h v

lemma eq_of_dot_eq (x y : V → ℝ)
    (h : ∀ f : V → ℝ, ∑ v, x v * f v = ∑ v, y v * f v) : x = y := by
  ext v
  have hh := h (fun w => if w = v then 1 else 0)
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] using hh

lemma boundary_mapVertices (N : Network V E) (q : V → W) (x : E → ℝ) :
    (N.mapVertices q).boundary x = push q (N.boundary x) := by
  apply eq_of_dot_eq
  intro f
  rw [(N.mapVertices q).boundary_adjoint, N.gradient_mapVertices,
    push_adjoint, N.boundary_adjoint]

lemma boundary_restrict (N : Network V E) (j : K → E) (x : K → ℝ) :
    (N.restrict j).boundary x = N.boundary (push j x) := by
  apply eq_of_dot_eq
  intro f
  rw [(N.restrict j).boundary_adjoint, N.gradient_restrict,
    N.boundary_adjoint, push_adjoint]

omit [Fintype E] in
lemma pull_push_injective {j : K → E} (hj : Function.Injective j) (x : K → ℝ) :
    pull j (push j x) = x := by
  classical
  ext k
  simp [hj.eq_iff]

omit [Fintype E] in
lemma push_eq_zero_outside {j : K → E} (x : K → ℝ) {e : E} (he : e ∉ Set.range j) :
    push j x e = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro k _
  have hk : j k ≠ e := fun h => he ⟨k, h⟩
  simp [hk]

lemma push_pull_subtype (s : Set E) (x : E → ℝ) :
    push (Subtype.val : s → E) (pull Subtype.val x) = fun e => if e ∈ s then x e else 0 := by
  classical
  ext e
  by_cases he : e ∈ s
  · change (pull Subtype.val (push Subtype.val (pull Subtype.val x))) ⟨e, he⟩ = _
    rw [pull_push_injective Subtype.val_injective]
    simp [he]
  · rw [push_eq_zero_outside _ (by simpa using he)]
    simp [he]

def internal (N : Network V E) (q : V → W) : Set E :=
  {e | q (N.tail e) = q (N.head e)}

lemma push_boundary_internal (N : Network V E) (q : V → W)
    (x : N.internal q → ℝ) :
    push q ((N.restrict Subtype.val).boundary x) = 0 := by
  apply eq_of_dot_eq
  intro f
  rw [push_adjoint, (N.restrict _).boundary_adjoint]
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  apply Finset.sum_eq_zero
  intro e _
  have he : (N.restrict (Subtype.val : N.internal q → E)).gradient (pull q f) e = 0 := by
    change f (q (N.head e.val)) - f (q (N.tail e.val)) = 0
    rw [e.property]
    exact sub_self _
  rw [he, mul_zero]

def ConnectedFibers (N : Network V E) (q : V → W) : Prop :=
  ∀ v w, q v = q w → (N.restrict (Subtype.val : N.internal q → E)).graph.Reachable v w

omit [Fintype V] [Fintype W] [Fintype E] in
lemma ker_internal_gradient (N : Network V E) {q : V → W}
    (hq : Function.Surjective q) (hc : N.ConnectedFibers q) :
    (N.restrict (Subtype.val : N.internal q → E)).gradient.ker = (pull q).range := by
  classical
  ext f
  constructor
  · intro hf
    let r := Function.surjInv hq
    have hr := Function.rightInverse_surjInv hq
    refine ⟨fun w => f (r w), ?_⟩
    ext v
    exact (N.restrict _).gradient_zero_reachable hf (hc _ _ (hr (q v)))
  · rintro ⟨f, rfl⟩
    apply (N.restrict _).gradient_eq_zero_iff _ |>.mpr
    intro e
    exact congrArg f e.property.symm

lemma range_internal_boundary (N : Network V E) {q : V → W}
    (hq : Function.Surjective q) (hc : N.ConnectedFibers q) :
    (N.restrict (Subtype.val : N.internal q → E)).boundary.range = (push q).ker := by
  classical
  let : DecidableEq (N.internal q) := Classical.decEq _
  let I := N.restrict (Subtype.val : N.internal q → E)
  have hle : I.boundary.range ≤ (push q).ker := by
    rintro _ ⟨x, rfl⟩
    exact N.push_boundary_internal q x
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hk : Module.finrank ℝ I.gradient.ker = Fintype.card W := by
    rw [show I.gradient.ker = (pull q).range from N.ker_internal_gradient hq hc,
      LinearMap.finrank_range_of_inj (pull_injective hq), Module.finrank_pi]
  have hgrad := I.gradient.finrank_range_add_finrank_ker
  have hpush := (push q).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (push_surjective hq), finrank_top,
    Module.finrank_pi, Module.finrank_pi] at hpush
  have hr : Module.finrank ℝ I.boundary.range = Module.finrank ℝ I.gradient.range := by
    rw [I.gradient_matrix, boundary, Matrix.toLin'_apply', Matrix.toLin'_apply',
      ← Matrix.rank, ← Matrix.rank, Matrix.rank_transpose]
  rw [Module.finrank_pi, hk] at hgrad
  omega

end
end Barnette.Network

end OAI


namespace OAI

/-! Connected face regions and the exact disk Euler formula. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

def regionEdges (A : Finset V) : Finset E :=
  Finset.univ.filter fun e => N.tail e ∈ A ∨ N.head e ∈ A

omit [Fintype V] in
@[simp] lemma mem_regionEdges (A : Finset V) (e : E) :
    e ∈ N.regionEdges A ↔ N.tail e ∈ A ∨ N.head e ∈ A := by
  simp [regionEdges]

def regionVertices (A : Finset V) : Finset F :=
  Finset.univ.filter fun z => ∃ e ∈ N.regionEdges A, D.Incident e z

omit [Fintype V] in
@[simp] lemma mem_regionVertices (A : Finset V) (z : F) :
    z ∈ N.regionVertices D A ↔ ∃ e ∈ N.regionEdges A, D.Incident e z := by
  simp [regionVertices]

def region (A : Finset V) : Network (N.regionVertices D A) (N.regionEdges A) where
  tail e := ⟨D.tail e.val, (N.mem_regionVertices D A _).mpr ⟨e.val,e.property,Or.inl rfl⟩⟩
  head e := ⟨D.head e.val, (N.mem_regionVertices D A _).mpr ⟨e.val,e.property,Or.inr rfl⟩⟩

omit [Fintype V] in
lemma region_map (A : Finset V) :
    (N.region D A).mapVertices Subtype.val = D.restrict (Subtype.val : N.regionEdges A → E) := rfl

omit [Fintype V] in
lemma region_boundary (A : Finset V) (x : N.regionEdges A → ℝ) :
    push (Subtype.val : N.regionVertices D A → F) ((N.region D A).boundary x) =
      D.boundary (push Subtype.val x) := by
  rw [← boundary_mapVertices, N.region_map, boundary_restrict]

omit [Fintype V] in
lemma push_subtype_apply (A : Finset V) (f : A → ℝ) (v : A) :
    push (Subtype.val : A → V) f v.val = f v := by
  have h := congrFun (pull_push_injective (E := V) Subtype.val_injective f) v
  exact h

omit [Fintype V] in
lemma push_subtype_outside (A : Finset V) (f : A → ℝ) {v : V} (hv : v ∉ A) :
    push (Subtype.val : A → V) f v = 0 :=
  push_eq_zero_outside f (by simpa using hv)

omit [Fintype V] in
lemma extend_gradient_outside (A : Finset V) (f : A → ℝ) {e : E}
    (he : e ∉ N.regionEdges A) : N.gradient (push (Subtype.val : A → V) f) e = 0 := by
  have hh : N.head e ∉ A := fun h => he ((N.mem_regionEdges A e).mpr (Or.inr h))
  have ht : N.tail e ∉ A := fun h => he ((N.mem_regionEdges A e).mpr (Or.inl h))
  simp only [gradient_apply, push_subtype_outside A f hh, push_subtype_outside A f ht, sub_self]

omit [Fintype V] in
lemma extend_restrict_gradient (A : Finset V) (f : A → ℝ) :
    push (Subtype.val : N.regionEdges A → E)
      (pull Subtype.val (N.gradient (push (Subtype.val : A → V) f))) =
        N.gradient (push (Subtype.val : A → V) f) := by
  ext e
  by_cases he : e ∈ N.regionEdges A
  · exact push_subtype_apply (N.regionEdges A) _ ⟨e,he⟩
  · rw [push_subtype_outside (N.regionEdges A) _ he]
    exact (N.extend_gradient_outside A f he).symm

omit [Fintype V] in

lemma region_connected (A : Finset V) (hA : (N.graph.induce {v | v ∈ A}).Connected)
    (sD : D.Simple) (face : ∀ v, D.Triangle (N.star v)) :
    (N.region D A).graph.Connected := by
  let R := N.region D A
  have in_face {v : V} (hv : v ∈ A) {z : F} (hz : z ∈ Set.range (face v).corner) :
      z ∈ N.regionVertices D A := by
    obtain ⟨e,he,hz⟩ := ((face v).corner_iff_incident D z).mp hz
    have hv' := (N.mem_star e v).mp he
    have heA : e ∈ N.regionEdges A := by
      apply (N.mem_regionEdges A e).mpr
      exact hv'.elim (fun he => Or.inl (he ▸ hv)) (fun he => Or.inr (he ▸ hv))
    exact (N.mem_regionVertices D A z).mpr ⟨e,heA,hz⟩
  let a (v : {v // v ∈ A}) : N.regionVertices D A :=
    ⟨(face v.val).corner 0,in_face v.property ⟨0,rfl⟩⟩
  have local_path {v : V} (hv : v ∈ A) {z w : N.regionVertices D A}
      (hz : z.val ∈ Set.range (face v).corner) (hw : w.val ∈ Set.range (face v).corner) :
      R.graph.Reachable z w := by
    obtain ⟨i,hi⟩ := hz
    obtain ⟨j,hj⟩ := hw
    by_cases hij : i = j
    · have he : z = w := Subtype.ext (hi.symm.trans (hij ▸ hj))
      rw [he]
    · have hadj := (face v).clique D hij
      rw [hi,hj] at hadj
      obtain ⟨hne,e,he⟩ := hadj
      have heface : e ∈ N.star v := by
        have hfin : ∀ i j : Fin 3, i ≠ j → j = i+1 ∨ i = j+1 := by decide
        rcases hfin i j hij with h | h
        · have ep : s(D.tail e,D.head e) = s(D.tail ((face v).edge i),D.head ((face v).edge i)) := by
            rw [(face v).edge_ends, ← h, hi, hj]
            exact Sym2.eq_iff.mpr he
          have ee := sD.pair_injective ep
          rw [ee]
          have hm : (face v).edge i ∈ Finset.univ.image (face v).edge :=
            Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
          rwa [(face v).edge_range] at hm
        · have ep : s(D.tail e,D.head e) = s(D.tail ((face v).edge j),D.head ((face v).edge j)) := by
            rw [(face v).edge_ends, ← h, hi, hj]
            exact Sym2.eq_iff.mpr he.symm
          rw [sD.pair_injective ep]
          have hm : (face v).edge j ∈ Finset.univ.image (face v).edge :=
            Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
          rwa [(face v).edge_range] at hm
      have heA : e ∈ N.regionEdges A := by
        rcases (N.mem_star e v).mp heface with h | h
        · exact (N.mem_regionEdges A e).mpr (Or.inl (h ▸ hv))
        · exact (N.mem_regionEdges A e).mpr (Or.inr (h ▸ hv))
      apply SimpleGraph.Adj.reachable
      refine ⟨fun h => hne (congrArg Subtype.val h),⟨e,heA⟩,?_⟩
      exact he.elim (fun h => Or.inl ⟨Subtype.ext h.1,Subtype.ext h.2⟩)
        (fun h => Or.inr ⟨Subtype.ext h.1,Subtype.ext h.2⟩)
  have step {v w : {v // v ∈ A}} (hvw : (N.graph.induce {v | v ∈ A}).Adj v w) :
      R.graph.Reachable (a v) (a w) := by
    obtain ⟨_,e,he⟩ := hvw
    have hv : N.Incident e v.val := he.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
    have hw : N.Incident e w.val := he.elim (fun h => Or.inr h.2) (fun h => Or.inl h.1)
    have hf (u : V) (hu : N.Incident e u) : D.tail e ∈ Set.range (face u).corner :=
      ((face u).corner_iff_incident D _).mpr ⟨e,(N.mem_star e u).mpr hu,Or.inl rfl⟩
    let z : N.regionVertices D A := ⟨D.tail e,in_face v.property (hf _ hv)⟩
    exact (local_path v.property ⟨0,rfl⟩ (hf _ hv)).trans
      (local_path w.property (z := z) (hf _ hw) ⟨0,rfl⟩)
  have all_faces {v w : {v // v ∈ A}} : R.graph.Reachable (a v) (a w) := by
    obtain ⟨p⟩ := hA v w
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | cons h p ih => exact (step h).trans ih
  obtain ⟨v₀⟩ := hA.nonempty
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨a v₀,?_⟩
  intro z
  obtain ⟨e,he,hz⟩ := (N.mem_regionVertices D A z.val).mp z.property
  rcases (N.mem_regionEdges A e).mp he with ht | hh
  · have hf := ((face (N.tail e)).corner_iff_incident D z.val).mpr
      ⟨e,(N.mem_star _ _).mpr (Or.inl rfl),hz⟩
    exact (all_faces (w := ⟨N.tail e,ht⟩)).trans (local_path ht ⟨0,rfl⟩ hf)
  · have hf := ((face (N.head e)).corner_iff_incident D z.val).mpr
      ⟨e,(N.mem_star _ _).mpr (Or.inr rfl),hz⟩
    exact (all_faces (w := ⟨N.head e,hh⟩)).trans (local_path hh ⟨0,rfl⟩ hf)

end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

def regionCycleMap (A : Finset V) : (A → ℝ) →ₗ[ℝ] (N.regionEdges A → ℝ) :=
  (pull (Subtype.val : N.regionEdges A → E)).comp
    (N.gradient.comp (push (Subtype.val : A → V)))

omit [Fintype V] in
lemma regionCycleMap_injective (hN : N.graph.Connected) (A : Finset V)
    (hout : ∃ v, v ∉ A) : Function.Injective (N.regionCycleMap A) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro f hf
  change f = 0
  have hz : N.regionCycleMap A f = 0 := hf
  have hg : N.gradient (push (Subtype.val : A → V) f) = 0 := by
    rw [← N.extend_restrict_gradient A f]
    change push (Subtype.val : N.regionEdges A → E) (N.regionCycleMap A f) = 0
    rw [hz,map_zero]
  obtain ⟨r,hr⟩ := hout
  ext v
  have he := N.gradient_zero_reachable hg (hN r v.val)
  rw [push_subtype_outside A f hr, push_subtype_apply A f v] at he
  exact he.symm

omit [Fintype V] in
lemma region_cycles_eq_range (h : N.Duality D) (A : Finset V)
    (hAc : (N.graph.induce {v | v ∉ A}).Connected) :
    (N.region D A).boundary.ker = (N.regionCycleMap A).range := by
  ext x
  constructor
  · intro hx
    have hx' : (N.region D A).boundary x = 0 := hx
    let y : E → ℝ := push (Subtype.val : N.regionEdges A → E) x
    have hy : D.boundary y = 0 := by
      rw [← N.region_boundary D A x, hx',map_zero]
    obtain ⟨f,hf⟩ : ∃ f, N.gradient f = y := by
      have hm : y ∈ D.boundary.ker := hy
      rw [h.dual_cycles_eq_cuts] at hm
      exact hm
    obtain ⟨r⟩ := hAc.nonempty
    have fstep {v w : {v // v ∉ A}}
        (hvw : (N.graph.induce {v | v ∉ A}).Adj v w) : f v.val = f w.val := by
      obtain ⟨_,e,he⟩ := hvw
      have heA : e ∉ N.regionEdges A := by
        rw [N.mem_regionEdges]
        exact he.elim (fun he => by rw [he.1,he.2]; exact not_or.mpr ⟨v.property,w.property⟩)
          (fun he => by rw [he.1,he.2]; exact not_or.mpr ⟨w.property,v.property⟩)
      have hy0 : y e = 0 := push_eq_zero_outside x (by simpa using heA)
      have heq := congrFun hf e
      rw [hy0,gradient_apply,sub_eq_zero] at heq
      exact he.elim (fun he => by rw [he.1,he.2] at heq; exact heq.symm)
        (fun he => by rwa [he.1,he.2] at heq)
    have fconstant (v : {v // v ∉ A}) : f v.val = f r.val := by
      obtain ⟨p⟩ := hAc v r
      induction p with
      | nil => rfl
      | cons h p ih => exact (fstep h).trans ih
    let u : A → ℝ := fun v => f v.val - f r.val
    have hext : push (Subtype.val : A → V) u = f - (fun _ => f r.val) := by
      ext v
      by_cases hv : v ∈ A
      · exact push_subtype_apply A u ⟨v,hv⟩
      · rw [push_subtype_outside A u hv]
        exact (sub_eq_zero.mpr (fconstant ⟨v,hv⟩)).symm
    refine ⟨u,?_⟩
    change pull (Subtype.val : N.regionEdges A → E) (N.gradient (push Subtype.val u)) = x
    rw [hext,map_sub,N.gradient_const,sub_zero,hf]
    exact pull_push_injective Subtype.val_injective x
  · rintro ⟨f,rfl⟩
    have hz : push (Subtype.val : N.regionVertices D A → F)
        ((N.region D A).boundary (N.regionCycleMap A f)) = 0 := by
      rw [N.region_boundary]
      change D.boundary (push (Subtype.val : N.regionEdges A → E)
        (pull Subtype.val (N.gradient (push (Subtype.val : A → V) f)))) = 0
      rw [N.extend_restrict_gradient]
      exact h.dual_conserved_gradient N D _
    have hh := congrArg (pull (Subtype.val : N.regionVertices D A → F)) hz
    rw [pull_push_injective Subtype.val_injective,map_zero] at hh
    exact hh

omit [Fintype V] in
lemma region_dim_cycles (h : N.Duality D) (A : Finset V)
    (hAc : (N.graph.induce {v | v ∉ A}).Connected) :
    Module.finrank ℝ (N.region D A).boundary.ker = A.card := by
  rw [N.region_cycles_eq_range D h A hAc,
    LinearMap.finrank_range_of_inj (N.regionCycleMap_injective h.connected A ?_),
    Module.finrank_pi,Fintype.card_coe]
  obtain ⟨v⟩ := hAc.nonempty
  exact ⟨v.val,v.property⟩

omit [Fintype V] in

theorem region_euler (h : N.Duality D) (A : Finset V)
    (hA : (N.graph.induce {v | v ∈ A}).Connected)
    (hAc : (N.graph.induce {v | v ∉ A}).Connected)
    (sD : D.Simple) (face : ∀ v, D.Triangle (N.star v)) :
    A.card + (N.regionVertices D A).card = (N.regionEdges A).card + 1 := by
  have hh := (N.region D A).dim_cycles (N.region_connected D A hA sD face)
  rwa [N.region_dim_cycles D h A hAc,Fintype.card_coe,Fintype.card_coe] at hh

end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] in
lemma sum_stars (hN : N.Simple) (A : Finset V) :
    ∑ v ∈ A, (N.star v).card =
      ∑ e, ((if N.tail e ∈ A then 1 else 0) + (if N.head e ∈ A then 1 else 0)) := by
  calc
    ∑ v ∈ A, (N.star v).card =
      ∑ v ∈ A, ∑ e, ((if N.tail e = v then 1 else 0) + (if N.head e = v then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro v _
        rw [star,Finset.card_filter]
        simp only [Incident]
        apply Finset.sum_congr rfl
        intro e _
        have hne := hN.loopless e
        by_cases ht : N.tail e = v <;> by_cases hh : N.head e = v <;> simp_all
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      simp [Finset.sum_add_distrib]

lemma cubic_region_count (hN : N.Simple) (hc : N.graph.IsRegularOfDegree 3) (A : Finset V) :
    3 * A.card + (N.cut A).card = 2 * (N.regionEdges A).card := by
  have hsum := N.sum_stars hN A
  have hv : (∑ v ∈ A, (N.star v).card) = 3 * A.card := by
    have hc' : ∀ v, N.graph.degree v = 3 := hc
    simp only [N.card_star hN,hc']
    simp [Nat.mul_comm]
  rw [hv] at hsum
  rw [hsum]
  simp only [cut,regionEdges,Finset.card_filter,
    ← Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases ht : N.tail e ∈ A <;> by_cases hh : N.head e ∈ A <;> simp [ht,hh]

lemma disk_euler_count (h : N.Duality D) (hN : N.Simple)
    (hc : N.graph.IsRegularOfDegree 3) (A : Finset V)
    (hA : (N.graph.induce {v | v ∈ A}).Connected)
    (hAc : (N.graph.induce {v | v ∉ A}).Connected)
    (sD : D.Simple) (face : ∀ v, D.Triangle (N.star v)) :
    (A.card : ℤ) = 2 * (N.regionVertices D A).card - (N.cut A).card - 2 := by
  have he := N.region_euler D h A hA hAc sD face
  have hc := N.cubic_region_count hN hc A
  omega

end
end Barnette.Network

end OAI


namespace OAI

/-! Minimal links, incidence states, and the signed disk identity. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype F] in
lemma Duality.symm (h : N.Duality D) : D.Duality N :=
  ⟨h.dual_connected,h.connected,h.dual_cycles_eq_cuts,h.cycles_eq_cuts⟩

omit [Fintype V] [Fintype F] in

lemma Duality.vertex_flow_circuit (h : N.Duality D) (z : F)
    (hz : (D.graph.induce {v | v ≠ z}).Connected) :
    N.FlowCircuit (D.gradient (fun w => if w = z then 1 else 0)) := by
  obtain ⟨r⟩ := hz.nonempty
  let x := D.gradient (fun w => if w = z then (1:ℝ) else 0)
  have hx : N.boundary x = 0 := (h.symm N D).dual_conserved_gradient D N _
  have hn : x ≠ 0 := by
    intro he
    have hh := D.gradient_zero_reachable he (h.dual_connected z r.val)
    norm_num at hh
    exact r.property hh
  refine ⟨hx,hn,?_⟩
  intro y hy hs
  by_cases hy0 : y = 0
  · exact Or.inl hy0
  right
  obtain ⟨f,hf⟩ := (h.symm N D).gradient_of_dual_conserved D N hy
  have fstep {v w : {v // v ≠ z}}
      (hvw : (D.graph.induce {v | v ≠ z}).Adj v w) : f v.val = f w.val := by
    obtain ⟨_,e,he⟩ := hvw
    have hxe : x e = 0 := by
      dsimp only [x,gradient_apply]
      rcases he with he | he <;> rw [he.1,he.2] <;> simp [v.property,w.property]
    have hye : y e = 0 := by
      by_contra he
      exact (N.mem_flowSupport x e).mp (hs ((N.mem_flowSupport y e).mpr he)) hxe
    have heq := congrFun hf e
    rw [hye,gradient_apply,sub_eq_zero] at heq
    exact he.elim (fun he => by rw [he.1,he.2] at heq; exact heq.symm)
      (fun he => by rwa [he.1,he.2] at heq)
  have fconstant (v : {v // v ≠ z}) : f v.val = f r.val := by
    obtain ⟨p⟩ := hz v r
    induction p with
    | nil => rfl
    | cons h p ih => exact (fstep h).trans ih
  have hne : f z ≠ f r.val := by
    intro he
    apply hy0
    rw [← hf]
    apply (D.gradient_eq_zero_iff f).mpr
    have hall (v : F) : f v = f r.val := by
      by_cases hv : v = z
      · rwa [hv]
      · exact fconstant ⟨v,hv⟩
    intro e
    exact (hall _).trans (hall _).symm
  apply Finset.Subset.antisymm hs
  intro e he
  apply (N.mem_flowSupport y e).mpr
  rw [← hf,gradient_apply]
  have hxe := (N.mem_flowSupport x e).mp he
  dsimp only [x,gradient_apply] at hxe
  by_cases ht : D.tail e = z <;> by_cases hh : D.head e = z
  · simp [ht,hh] at hxe
  · rw [ht,fconstant ⟨D.head e,hh⟩]
    exact sub_ne_zero.mpr hne.symm
  · rw [hh,fconstant ⟨D.tail e,ht⟩]
    exact sub_ne_zero.mpr hne
  · simp [ht,hh] at hxe

omit [Fintype V] in

lemma cut_restrict_conserved (x : E → ℝ) (hx : N.boundary x = 0) (A : Finset V)
    (hcut : ∀ e ∈ N.cut A, x e = 0) :
    N.boundary (fun e => if N.tail e ∈ A then x e else 0) = 0 := by
  ext v
  have hb : N.boundary (fun e => if N.tail e ∈ A then x e else 0) v =
      if v ∈ A then N.boundary x v else 0 := by
    simp only [boundary_apply]
    trans ∑ e, if v ∈ A then
      ((if N.head e = v then x e else 0) - (if N.tail e = v then x e else 0)) else 0
    swap
    · by_cases hv : v ∈ A <;> simp [hv]
    apply Finset.sum_congr rfl
    intro e _
    have hcross : N.tail e ∈ A ∨ N.head e ∈ A →
        ¬(N.tail e ∈ A ∧ N.head e ∈ A) → x e = 0 := by
      intro h1 h2
      apply hcut e
      rw [N.mem_cut]
      tauto
    by_cases ht : N.tail e = v <;> by_cases hh : N.head e = v <;>
      by_cases ha : N.tail e ∈ A <;> by_cases hb : N.head e ∈ A <;>
      by_cases hv : v ∈ A <;> simp_all
  rw [hb,hx]
  simp

omit [Fintype V] in

lemma FlowCircuit.no_split (x : E → ℝ) (hx : N.FlowCircuit x) (A : Finset V)
    (hcut : ∀ e ∈ N.cut A, x e = 0)
    {e : E} (he : x e ≠ 0) (heA : N.tail e ∈ A) :
    ∀ k, x k ≠ 0 → N.tail k ∈ A := by
  let y : E → ℝ := fun k => if N.tail k ∈ A then x k else 0
  have hy := N.cut_restrict_conserved x hx.conserved A hcut
  have hs : N.flowSupport y ⊆ N.flowSupport x := by
    intro k hk
    simp only [mem_flowSupport,y] at hk ⊢
    split_ifs at hk <;> tauto
  have hyn : y ≠ 0 := by
    intro hy0
    have hh := congrFun hy0 e
    apply he
    simpa [y,heA] using hh
  have hEq := (hx.minimal y hy hs).resolve_left hyn
  intro k hk
  have hyk := (N.mem_flowSupport y k).mp (by rw [hEq]; exact (N.mem_flowSupport x k).mpr hk)
  by_contra hn
  exact hyk (by simp [y,hn])

theorem mixed_corner_on_boundary (h : N.Duality D) (sD : D.Simple)
    (face : ∀ v, D.Triangle (N.star v)) (A : Finset V) {z : F}
    (hzin : z ∈ N.regionVertices D A) (hzout : z ∈ N.regionVertices D Aᶜ) :
    ∃ e ∈ N.cut A, D.Incident e z := by
  by_contra hn
  have hc := h.vertex_flow_circuit N D z
    (faces_vertex_deleted_connected N D h.connected h.dual_connected sD face z)
  let x := D.gradient (fun w => if w = z then (1:ℝ) else 0)
  have hs : N.flowSupport x = D.star z := D.gradient_indicator_support N sD z
  have hcut : ∀ e ∈ N.cut A, x e = 0 := by
    intro e he
    by_contra hx
    have hh : D.Incident e z := (D.mem_star e z).mp (by
      rw [← hs]; exact (N.mem_flowSupport x e).mpr hx)
    exact hn ⟨e,he,hh⟩
  obtain ⟨e,he,hez⟩ := (N.mem_regionVertices D A z).mp hzin
  have hex : x e ≠ 0 := (N.mem_flowSupport x e).mp (by rw [hs]; exact (D.mem_star e z).mpr hez)
  have heA : N.tail e ∈ A := by
    rcases (N.mem_regionEdges A e).mp he with ht | hh
    · exact ht
    · by_contra ht
      exact hex (hcut e ((N.mem_cut A e).mpr (Or.inr ⟨hh,ht⟩)))
  have hall := hc.no_split N x A hcut hex heA
  obtain ⟨k,hk,hkz⟩ := (N.mem_regionVertices D Aᶜ z).mp hzout
  have hkx : x k ≠ 0 := (N.mem_flowSupport x k).mp (by rw [hs]; exact (D.mem_star k z).mpr hkz)
  have hkA := hall k hkx
  rcases (N.mem_regionEdges Aᶜ k).mp hk with ht | hh
  · exact (Finset.mem_compl.mp ht) hkA
  · exact hkx (hcut k ((N.mem_cut A k).mpr (Or.inl ⟨hkA,Finset.mem_compl.mp hh⟩)))

end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype E] in
def cycleVertices (C : Barnette.CycleCoordinates D.graph) : Finset F :=
  Finset.univ.image C.vertex

omit [Fintype V] [Fintype E] [Fintype F] in
lemma mem_cycleVertices (C : Barnette.CycleCoordinates D.graph) (z : F) :
    z ∈ D.cycleVertices C ↔ ∃ i, C.vertex i = z := by
  simp [cycleVertices]

omit [Fintype V] [Fintype E] [Fintype F] in
lemma incident_cycle_iff (C : Barnette.CycleCoordinates D.graph) (z : F) :
    (∃ e ∈ D.cycleEdges C, D.Incident e z) ↔ z ∈ D.cycleVertices C := by
  constructor
  · rintro ⟨e,he,hz⟩
    obtain ⟨i,rfl⟩ := (D.mem_cycleEdges C e).mp he
    rw [D.incident_iff_mem_pair,D.cycleEdge_ends,Sym2.mem_iff] at hz
    rcases hz with rfl | rfl
    · exact (D.mem_cycleVertices C _).mpr ⟨i,rfl⟩
    · exact (D.mem_cycleVertices C _).mpr ⟨i+1,rfl⟩
  · intro hz
    obtain ⟨i,rfl⟩ := (D.mem_cycleVertices C z).mp hz
    refine ⟨D.cycleEdge C i,(D.mem_cycleEdges C _).mpr ⟨i,rfl⟩,?_⟩
    rw [D.incident_iff_mem_pair,D.cycleEdge_ends]; simp

omit [Fintype V] in
lemma regionVertices_iff_face (face : ∀ v, D.Triangle (N.star v))
    (A : Finset V) (z : F) :
    z ∈ N.regionVertices D A ↔ ∃ v ∈ A, z ∈ Set.range (face v).corner := by
  constructor
  · intro hz
    obtain ⟨e,he,hez⟩ := (N.mem_regionVertices D A z).mp hz
    rcases (N.mem_regionEdges A e).mp he with ht | hh
    · exact ⟨N.tail e,ht,((face _).corner_iff_incident D z).mpr
        ⟨e,(N.mem_star e _).mpr (Or.inl rfl),hez⟩⟩
    · exact ⟨N.head e,hh,((face _).corner_iff_incident D z).mpr
        ⟨e,(N.mem_star e _).mpr (Or.inr rfl),hez⟩⟩
  · rintro ⟨v,hv,hz⟩
    obtain ⟨e,he,hez⟩ := ((face v).corner_iff_incident D z).mp hz
    refine (N.mem_regionVertices D A z).mpr ⟨e,?_,hez⟩
    rcases (N.mem_star e v).mp he with ht | hh
    · exact (N.mem_regionEdges A e).mpr (Or.inl (ht ▸ hv))
    · exact (N.mem_regionEdges A e).mpr (Or.inr (hh ▸ hv))

omit [Fintype V] [Fintype E] [Fintype F] in
def blackEndpoint (black : V → Prop) (e : E) : V :=
  if black (N.tail e) then N.tail e else N.head e

omit [Fintype V] [Fintype E] [Fintype F] in
lemma blackEndpoint_spec (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (e : E) :
    black (N.blackEndpoint black e) ∧ N.Incident e (N.blackEndpoint black e) := by
  by_cases ht : black (N.tail e)
  · simp only [blackEndpoint,ite_eq_left ht]; exact ⟨ht,Or.inl rfl⟩
  · simp only [blackEndpoint,ite_eq_right ht]
    exact ⟨not_not.mp (fun hh => ht ((hc e).mpr hh)),Or.inr rfl⟩

omit [Fintype V] [Fintype E] [Fintype F] in
lemma blackEndpoint_eq (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    {e : E} {v : V} (hv : black v) (he : N.Incident e v) :
    N.blackEndpoint black e = v := by
  rcases he with ht | hh
  · simp [blackEndpoint,ht,hv]
  · have hnt : ¬black (N.tail e) := fun ht => (hc e).mp ht (hh ▸ hv)
    simp [blackEndpoint,hnt,hh]

omit [Fintype V] [Fintype F] in
def blackCut (black : V → Prop) (A : Finset V) : Finset E :=
  (N.cut A).filter fun e => N.blackEndpoint black e ∈ A

omit [Fintype F] in
lemma cubic_black_region_count (sN : N.Simple) (hdeg : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (A : Finset V) :
    3 * (A.filter black).card + (N.cut A).card =
      (N.regionEdges A).card + (N.blackCut black A).card := by
  have hs := N.sum_stars sN (A.filter black)
  have hd : ∀ v, N.graph.degree v = 3 := hdeg
  have hh : (∑ v ∈ A.filter black, (N.star v).card) = 3 * (A.filter black).card := by
    simp only [N.card_star sN,hd]
    simp [Nat.mul_comm]
  rw [hh] at hs
  rw [hs]
  simp only [cut,regionEdges,blackCut,Finset.card_filter,Finset.mem_filter,
    Finset.sum_filter,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hcol := hc e
  by_cases ht : N.tail e ∈ A <;> by_cases hh : N.head e ∈ A <;>
    by_cases hb : black (N.tail e) <;> by_cases hw : black (N.head e) <;>
    simp_all [blackEndpoint]

theorem state_disk_count (h : N.Duality D) (sD : D.Simple)
    (face : ∀ v, D.Triangle (N.star v)) (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (root : V)
    (m : V → F)
    (hm_inj : Set.InjOn m {v | black v ∧ v ≠ root})
    (hm_face : ∀ v, black v → v ≠ root → m v ∈ Set.range (face v).corner)
    (hm_range : ∀ z, z ∉ Set.range (face root).corner ↔
      ∃ v, black v ∧ v ≠ root ∧ m v = z)
    (C : Barnette.CycleCoordinates D.graph)
    (hchoice : ∀ i, N.blackEndpoint black (D.cycleEdge C i) ≠ root ∧
      m (N.blackEndpoint black (D.cycleEdge C i)) = C.vertex i)
    (A : Finset V) (hroot : root ∉ A) (hcut : N.cut A = D.cycleEdges C) :
    (A.filter black).card + (N.cut A).card =
      (N.regionVertices D A).card + (N.blackCut black A).card := by
  let U := N.regionVertices D A
  let Z := D.cycleVertices C
  let B := A.filter black
  let M := B.image m
  let J := Finset.univ.filter fun i : Fin (C.n+3) =>
    N.blackEndpoint black (D.cycleEdge C i) ∈ A
  have face_region {v : V} (hv : v ∈ A) {z : F}
      (hz : z ∈ Set.range (face v).corner) : z ∈ U :=
    (N.regionVertices_iff_face D face A z).mpr ⟨v,hv,hz⟩
  have hZroot : ∀ z ∈ Z, z ∉ Set.range (face root).corner := by
    intro z hz
    obtain ⟨i,rfl⟩ := (D.mem_cycleVertices C z).mp hz
    apply (hm_range _).mpr
    exact ⟨_,(N.blackEndpoint_spec black hc _).1,(hchoice i).1,(hchoice i).2⟩
  have hZU : Z ⊆ U := by
    intro z hz
    obtain ⟨e,he,hez⟩ := (D.incident_cycle_iff C z).mpr hz
    rw [← hcut] at he
    refine (N.mem_regionVertices D A z).mpr ⟨e,?_,hez⟩
    rcases (N.mem_cut A e).mp he with ht | hh
    · exact (N.mem_regionEdges A e).mpr (Or.inl ht.1)
    · exact (N.mem_regionEdges A e).mpr (Or.inr hh.1)
  have hUroot : ∀ z ∈ U, z ∉ Set.range (face root).corner := by
    intro z hz hr
    have hzout : z ∈ N.regionVertices D Aᶜ :=
      (N.regionVertices_iff_face D face Aᶜ z).mpr ⟨root,Finset.mem_compl.mpr hroot,hr⟩
    have hh := N.mixed_corner_on_boundary D h sD face A hz hzout
    rw [hcut] at hh
    exact hZroot z ((D.incident_cycle_iff C z).mp hh) hr
  have hMU : M ⊆ U := by
    intro z hz
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hvA,hvb⟩ := Finset.mem_filter.mp hv
    exact face_region hvA (hm_face v hvb (fun he => hroot (he ▸ hvA)))
  have h_union : M ∪ Z = U := by
    apply Finset.Subset.antisymm
    · exact Finset.union_subset hMU hZU
    · intro z hz
      by_cases hzZ : z ∈ Z
      · exact Finset.mem_union_right _ hzZ
      obtain ⟨v,hvb,hvr,hvz⟩ := (hm_range z).mp (hUroot z hz)
      have hvA : v ∈ A := by
        by_contra hvA
        have hzout : z ∈ N.regionVertices D Aᶜ :=
          (N.regionVertices_iff_face D face Aᶜ z).mpr
            ⟨v,Finset.mem_compl.mpr hvA,hvz ▸ hm_face v hvb hvr⟩
        have hh := N.mixed_corner_on_boundary D h sD face A hz hzout
        rw [hcut] at hh
        exact hzZ ((D.incident_cycle_iff C z).mp hh)
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨v,Finset.mem_filter.mpr ⟨hvA,hvb⟩,hvz⟩)
  have h_inter : M ∩ Z = J.image C.vertex := by
    ext z
    constructor
    · rintro hz
      obtain ⟨hzM,hzZ⟩ := Finset.mem_inter.mp hz
      obtain ⟨v,hv,hvz⟩ := Finset.mem_image.mp hzM
      obtain ⟨hvA,hvb⟩ := Finset.mem_filter.mp hv
      obtain ⟨i,hi⟩ := (D.mem_cycleVertices C z).mp hzZ
      have heq : v = N.blackEndpoint black (D.cycleEdge C i) :=
        hm_inj ⟨hvb,fun he => hroot (he ▸ hvA)⟩
          ⟨(N.blackEndpoint_spec black hc _).1,(hchoice i).1⟩
          (hvz.trans (hi.symm.trans (hchoice i).2.symm))
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,heq ▸ hvA⟩,hi⟩
    · rintro hz
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
      have hiA := (Finset.mem_filter.mp hi).2
      refine Finset.mem_inter.mpr ⟨?_,(D.mem_cycleVertices C _).mpr ⟨i,rfl⟩⟩
      exact Finset.mem_image.mpr ⟨_,Finset.mem_filter.mpr
        ⟨hiA,(N.blackEndpoint_spec black hc _).1⟩,(hchoice i).2⟩
  have hCJ : J.image (D.cycleEdge C) = N.blackCut black A := by
    ext e
    simp only [blackCut,Finset.mem_filter]
    constructor
    · intro he
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
      refine ⟨?_,(Finset.mem_filter.mp hi).2⟩
      rw [hcut]
      exact (D.mem_cycleEdges C _).mpr ⟨i,rfl⟩
    · rintro ⟨he,hb⟩
      rw [hcut] at he
      obtain ⟨i,rfl⟩ := (D.mem_cycleEdges C e).mp he
      exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩,rfl⟩
  have hMcard : M.card = B.card := Finset.card_image_iff.mpr (by
    intro v hv w hw he
    obtain ⟨hvA,hvb⟩ := Finset.mem_filter.mp hv
    obtain ⟨hwA,hwb⟩ := Finset.mem_filter.mp hw
    exact hm_inj ⟨hvb,fun he => hroot (he ▸ hvA)⟩
      ⟨hwb,fun he => hroot (he ▸ hwA)⟩ he)
  have hZcard : Z.card = (N.cut A).card := by
    rw [hcut]
    simp only [Z,cycleVertices,cycleEdges,Finset.card_image_of_injective _ C.vertex.injective,
      Finset.card_image_of_injective _ (D.cycleEdge_injective C)]
  have hIcard : (M ∩ Z).card = (N.blackCut black A).card := by
    rw [h_inter,← hCJ]
    rw [Finset.card_image_of_injective _ C.vertex.injective,
      Finset.card_image_of_injective _ (D.cycleEdge_injective C)]
  have hh := Finset.card_union_add_card_inter M Z
  rw [h_union,hMcard,hZcard,hIcard] at hh
  exact hh.symm

end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype E] [Fintype F] in
def blackDelta (black : V → Prop) (C : Barnette.CycleCoordinates D.graph) : ℝ :=
  ∑ i, N.gradient (fun v => if black v then 1 else 0) (D.cycleEdge C i) *
    D.arcSign (D.cycleEdge C i) (C.vertex i)

omit [Fintype V] [Fintype F] in
lemma blackDelta_cut (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (C : Barnette.CycleCoordinates D.graph) (A : Finset V) (c : ℝ)
    (hx : D.cycleFlow C = c • N.gradient (fun v => if v ∈ A then 1 else 0))
    (hcut : N.cut A = D.cycleEdges C) :
    N.blackDelta D black C = c * (2 * (N.blackCut black A).card - (N.cut A).card) := by
  have hsum : N.blackDelta D black C = ∑ e ∈ N.cut A,
      N.gradient (fun v => if black v then 1 else 0) e * D.cycleFlow C e := by
    rw [hcut,cycleEdges,Finset.sum_image (D.cycleEdge_injective C).injOn]
    simp only [blackDelta,D.cycleFlow_apply_edge]
  rw [hsum]
  simp only [hx,Pi.smul_apply,smul_eq_mul]
  have heq (e : E) (he : e ∈ N.cut A) :
      N.gradient (fun v => if black v then (1:ℝ) else 0) e *
        (c * N.gradient (fun v => if v ∈ A then 1 else 0) e) =
      c * (2 * (if N.blackEndpoint black e ∈ A then 1 else 0) - 1) := by
    have hcol := hc e
    have he' := (N.mem_cut A e).mp he
    by_cases ht : N.tail e ∈ A <;> by_cases hh : N.head e ∈ A <;>
      by_cases hb : black (N.tail e) <;> by_cases hw : black (N.head e) <;>
      simp_all [gradient_apply,blackEndpoint] <;> ring
  rw [Finset.sum_congr rfl heq,← Finset.mul_sum,Finset.sum_sub_distrib,
    ← Finset.mul_sum,Finset.sum_boole]
  simp [blackCut]

omit [Fintype V] [Fintype E] [Fintype F] in
lemma cycle_cut_scalar (C : Barnette.CycleCoordinates D.graph) (A : Finset V) (c : ℝ)
    (hx : D.cycleFlow C = c • N.gradient (fun v => if v ∈ A then 1 else 0)) :
    c = 1 ∨ c = -1 := by
  have hh := congrFun hx (D.cycleEdge C 0)
  rw [D.cycleFlow_apply_edge] at hh
  simp only [Pi.smul_apply,smul_eq_mul,gradient_apply] at hh
  by_cases ht : N.tail (D.cycleEdge C 0) ∈ A <;>
    by_cases hh' : N.head (D.cycleEdge C 0) ∈ A <;>
    by_cases hd : D.tail (D.cycleEdge C 0) = C.vertex 0 <;>
    simp [arcSign,ht,hh',hd] at hh <;>
    first | exact Or.inl (by linarith) | exact Or.inr (by linarith)

lemma disk_boundary_imbalance (h : N.Duality D) (sN : N.Simple)
    (hdeg : N.graph.IsRegularOfDegree 3) (sD : D.Simple)
    (face : ∀ v, D.Triangle (N.star v))
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (A : Finset V) (hA : (N.graph.induce {v | v ∈ A}).Connected)
    (hAc : (N.graph.induce {v | v ∉ A}).Connected)
    (hm : (A.filter black).card + (N.cut A).card =
      (N.regionVertices D A).card + (N.blackCut black A).card) :
    (N.cut A).card = 2 * (N.blackCut black A).card + 3 := by
  have he := N.region_euler D h A hA hAc sD face
  have ht := N.cubic_region_count sN hdeg A
  have hb := N.cubic_black_region_count sN hdeg black hc A
  omega

theorem state_disk_delta (h : N.Duality D) (sN : N.Simple)
    (hdeg : N.graph.IsRegularOfDegree 3) (sD : D.Simple)
    (face : ∀ v, D.Triangle (N.star v)) (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (root : V)
    (m : V → F)
    (hm_inj : Set.InjOn m {v | black v ∧ v ≠ root})
    (hm_face : ∀ v, black v → v ≠ root → m v ∈ Set.range (face v).corner)
    (hm_range : ∀ z, z ∉ Set.range (face root).corner ↔
      ∃ v, black v ∧ v ≠ root ∧ m v = z)
    (C : Barnette.CycleCoordinates D.graph)
    (hchoice : ∀ i, N.blackEndpoint black (D.cycleEdge C i) ≠ root ∧
      m (N.blackEndpoint black (D.cycleEdge C i)) = C.vertex i) :
    ∃ (A : Finset V) (c : ℝ), A.Nonempty ∧ root ∉ A ∧ (c = 1 ∨ c = -1) ∧
      D.cycleFlow C = c • N.gradient (fun v => if v ∈ A then 1 else 0) ∧
      N.cut A = D.cycleEdges C ∧
      (N.cut A).card = 2 * (N.blackCut black A).card + 3 ∧
      N.blackDelta D black C = -3*c := by
  have hx := D.cycleFlow_circuit C sD
  obtain ⟨A,c,ha,hr,_hc0,he,hcut⟩ := h.circuit_cut N D (D.cycleFlow C) hx root
  rw [D.cycleFlow_support] at hcut
  have hb : N.Bond A := h.bond_of_circuit N D (D.cycleFlow C) hx A (by
    rw [D.cycleFlow_support]; exact hcut)
  have hA := hb.connected_shore N h.connected ha ⟨root,hr⟩
  have hAc := hb.compl.connected_shore N h.connected
    (Finset.mem_compl.mpr hr |> fun hh => ⟨root,hh⟩) (by
      obtain ⟨v,hv⟩ := ha
      exact ⟨v,by simpa using hv⟩)
  have hsides : {v : V | v ∈ Aᶜ} = {v : V | v ∉ A} := by
    ext v
    exact Finset.mem_compl
  rw [hsides] at hAc
  have hm := N.state_disk_count D h sD face black hc root m hm_inj hm_face hm_range C hchoice A hr hcut
  have hcount := N.disk_boundary_imbalance D h sN hdeg sD face black hc A hA hAc hm
  refine ⟨A,c,ha,hr,N.cycle_cut_scalar D C A c he,he,hcut,hcount,?_⟩
  rw [N.blackDelta_cut D black hc C A c he hcut,hcount]
  push_cast
  ring

end
end Barnette.Network

end OAI


namespace OAI

/-! Oriented triangular faces and positive white-face charges. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] in

lemma FlowCircuit.proportional (x : E → ℝ) (hx : N.FlowCircuit x)
    (y : E → ℝ) (hy : N.boundary y = 0)
    (hs : N.flowSupport y ⊆ N.flowSupport x) : ∃ c : ℝ, y = c • x := by
  obtain ⟨e,he⟩ : ∃ e, x e ≠ 0 := by
    by_contra hn
    apply hx.nonzero
    ext e
    exact not_not.mp (fun he => hn ⟨e,he⟩)
  let c := y e / x e
  let z := y - c • x
  have hz : N.boundary z = 0 := by simp [z,map_sub,map_smul,hy,hx.conserved]
  have hzs : N.flowSupport z ⊆ N.flowSupport x := by
    intro k hk
    by_contra hn
    have hxk : x k = 0 := not_not.mp (by simpa only [mem_flowSupport] using hn)
    have hyk : y k = 0 := by
      by_contra hyk
      exact hn (hs ((N.mem_flowSupport y k).mpr hyk))
    exact (N.mem_flowSupport z k).mp hk (by simp [z,hxk,hyk])
  have hze : z e = 0 := by simp [z,c,div_mul_cancel₀ _ he]
  have hz0 : z = 0 := (hx.minimal z hz hzs).resolve_right (by
    intro hh
    have hem : e ∈ N.flowSupport z := hh ▸ (N.mem_flowSupport x e).mpr he
    exact (N.mem_flowSupport z e).mp hem hze)
  exact ⟨c,sub_eq_zero.mp hz0⟩

omit [Fintype V] [Fintype E] [Fintype F] in
def Triangle.coordinates {s : Finset E} (t : D.Triangle s) : Barnette.CycleCoordinates D.graph where
  n := 0
  vertex := ⟨t.corner,t.corner_injective⟩
  adjacent i := t.clique D (by
    intro hh
    have h1 : (1 : Fin 3) = 0 := add_left_cancel (by simpa using hh.symm : i+1=i+0)
    norm_num at h1)

omit [Fintype V] [Fintype E] [Fintype F] in
lemma Triangle.coordinates_edge (sD : D.Simple) {s : Finset E} (t : D.Triangle s) (i : Fin 3) :
    D.cycleEdge (t.coordinates D) i = t.edge i := by
  apply sD.pair_injective
  exact (D.cycleEdge_ends (t.coordinates D) i).trans (t.edge_ends i).symm

omit [Fintype V] [Fintype E] [Fintype F] in
lemma Triangle.coordinates_edges (sD : D.Simple) {s : Finset E} (t : D.Triangle s) :
    D.cycleEdges (t.coordinates D) = s := by
  have hf : D.cycleEdge (t.coordinates D) = t.edge := funext (t.coordinates_edge D sD)
  change Finset.univ.image (D.cycleEdge (t.coordinates D)) = s
  rw [hf]
  exact t.edge_range

omit [Fintype V] [Fintype E] [Fintype F] in
def Triangle.reverse {s : Finset E} (t : D.Triangle s) : D.Triangle s where
  corner i := t.corner (-i)
  corner_injective := t.corner_injective.comp neg_injective
  edge i := t.edge (-i-1)
  edge_injective := t.edge_injective.comp (by
    intro i j hh
    apply neg_injective
    simpa only [sub_add_cancel] using congrArg (fun k : Fin 3 => k+1) hh)
  edge_range := by
    have hh : Finset.univ.image (fun i : Fin 3 => t.edge (-i-1)) = Finset.univ.image t.edge := by
      ext e
      simp only [Finset.mem_image,Finset.mem_univ,true_and]
      constructor
      · rintro ⟨i,rfl⟩; exact ⟨-i-1,rfl⟩
      · rintro ⟨i,rfl⟩
        refine ⟨-i-1,?_⟩
        congr 1
        abel
    exact hh.trans t.edge_range
  edge_ends i := by
    rw [t.edge_ends]
    have h1 : -i-1+1 = -i := sub_add_cancel _ _
    have h2 : -(i+1) = -i-1 := by abel
    rw [h1,h2,Sym2.eq_swap]

omit [Fintype V] [Fintype E] [Fintype F] in
lemma arcSign_opposite {e : E} {v w : F}
    (hne : v ≠ w) (he : s(D.tail e,D.head e) = s(v,w)) :
    D.arcSign e w = - D.arcSign e v := by
  rcases Sym2.eq_iff.mp he with ⟨ht,hh⟩ | ⟨ht,hh⟩
  · simp [arcSign,ht,hne]
  · simp [arcSign,ht,hne.symm]

omit [Fintype V] [Fintype F] in

theorem oriented_face (h : N.Duality D) (sN : N.Simple) (sD : D.Simple)
    (v : V) (t : D.Triangle (N.star v)) :
    ∃ u : D.Triangle (N.star v), ∀ i,
      N.gradient (fun w => if w = v then 1 else 0) (u.edge i) =
        D.arcSign (u.edge i) (u.corner i) := by
  let x := D.cycleFlow (t.coordinates D)
  let y := N.gradient (fun w => if w = v then 1 else 0)
  have hx := D.cycleFlow_circuit (t.coordinates D) sD
  have hy := h.dual_conserved_gradient N D (fun w => if w = v then 1 else 0)
  have hs : D.flowSupport y = D.flowSupport x := by
    rw [D.cycleFlow_support,t.coordinates_edges D sD]
    exact N.gradient_indicator_support D sN v
  obtain ⟨c,hc⟩ := hx.proportional D x y hy hs.subset
  have hxi (i : Fin 3) : x (t.edge i) = D.arcSign (t.edge i) (t.corner i) := by
    have hh := D.cycleFlow_apply_edge (t.coordinates D) i
    change x (D.cycleEdge (t.coordinates D) i) = D.arcSign (D.cycleEdge (t.coordinates D) i) (t.corner i) at hh
    rw [t.coordinates_edge D sD i] at hh
    exact hh
  have hci (i : Fin 3) : y (t.edge i) = c * D.arcSign (t.edge i) (t.corner i) := by
    rw [hc,Pi.smul_apply,smul_eq_mul,hxi]
  have he : t.edge 0 ∈ N.star v := by
    have hh : t.edge 0 ∈ Finset.univ.image t.edge := Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩
    rwa [t.edge_range] at hh
  have hcv : c = 1 ∨ c = -1 := by
    have hh := hci 0
    have hne := sN.loopless (t.edge 0)
    rcases (N.mem_star _ _).mp he with ht | hh'
    · have hhead : N.head (t.edge 0) ≠ v := fun h => hne (ht.trans h.symm)
      simp only [y,gradient_apply,ht,hhead,ite_true,ite_false,zero_sub] at hh
      by_cases hd : D.tail (t.edge 0) = t.corner 0 <;> simp [arcSign,hd] at hh <;> first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
    · have htail : N.tail (t.edge 0) ≠ v := fun h => hne (h.trans hh'.symm)
      simp only [y,gradient_apply,hh',htail,ite_true,ite_false,sub_zero] at hh
      by_cases hd : D.tail (t.edge 0) = t.corner 0 <;> simp [arcSign,hd] at hh <;> first | exact Or.inl (by linarith) | exact Or.inr (by linarith)
  rcases hcv with rfl | rfl
  · exact ⟨t,fun i => by simpa only [one_mul] using hci i⟩
  · refine ⟨t.reverse D,?_⟩
    intro i
    change y (t.edge (-i-1)) = D.arcSign (t.edge (-i-1)) (t.corner (-i))
    have hh := hci (-i-1)
    have ha := D.arcSign_opposite ((t.coordinates D).adjacent (-i-1 : Fin 3)).ne (t.edge_ends (-i-1))
    change D.arcSign (t.edge (-i-1)) (t.corner (-i-1+1)) =
      - D.arcSign (t.edge (-i-1)) (t.corner (-i-1)) at ha
    rw [sub_add_cancel] at ha
    rw [ha]
    simpa only [neg_one_mul] using hh

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

lemma boundary_of_sum_zero (h : N.graph.Connected) (b : V → ℝ)
    (hb : ∑ v, b v = 0) : ∃ x, N.boundary x = b := by
  let q : V → Unit := fun _ => ()
  have hq : Function.Surjective q := by
    obtain ⟨v⟩ := h.nonempty
    intro u
    exact ⟨v,Subsingleton.elim _ _⟩
  have hg : (N.restrict (Subtype.val : N.internal q → E)).graph = N.graph := by
    ext v w
    constructor
    · rintro ⟨hne,e,he⟩
      exact ⟨hne,e.val,he⟩
    · rintro ⟨hne,e,he⟩
      exact ⟨hne,⟨e,rfl⟩,he⟩
  have hc : N.ConnectedFibers q := by
    intro v w _
    rw [hg]
    exact h v w
  have hz : push q b = 0 := by
    ext u
    cases u
    simpa [push,q] using hb
  have hm : b ∈ (N.restrict (Subtype.val : N.internal q → E)).boundary.range := by
    rw [N.range_internal_boundary hq hc]
    exact hz
  obtain ⟨x,hx⟩ := hm
  refine ⟨push (Subtype.val : N.internal q → E) x,?_⟩
  rw [← boundary_restrict,hx]

def whiteCharge (black : V → Prop) (root : V) : V → ℝ := fun v =>
  (if black v then 0 else 1) -
    (if v = root then ((Finset.univ.filter fun w => ¬black w).card : ℝ) else 0)

lemma whiteCharge_sum (black : V → Prop) (root : V) :
    ∑ v, whiteCharge black root v = 0 := by
  simp only [whiteCharge,Finset.sum_sub_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [show (fun v => if black v then (0:ℝ) else 1) =
    (fun v => if ¬black v then 1 else 0) by ext v; by_cases hv : black v <;> simp [hv]]
  rw [Finset.sum_boole,sub_self]

lemma whiteCharge_black (black : V → Prop) (root v : V)
    (hv : black v) (hvr : v ≠ root) : whiteCharge black root v = 0 := by
  simp [whiteCharge,hv,hvr]

lemma whiteCharge_inside (black : V → Prop) (root : V) (A : Finset V)
    (hr : root ∉ A) :
    ∑ v ∈ A, whiteCharge black root v = ((A.filter fun v => ¬black v).card : ℝ) := by
  trans ∑ v ∈ A, if ¬black v then (1:ℝ) else 0
  · apply Finset.sum_congr rfl
    intro v hv
    have hvr : v ≠ root := fun hh => hr (hh ▸ hv)
    by_cases hb : black v <;> simp [whiteCharge,hb,hvr]
  · exact Finset.sum_boole _ _

lemma whiteCharge_cut_integral (black : V → Prop) (root : V) (A : Finset V)
    (hr : root ∉ A) (α : E → ℝ) (hα : N.boundary α = whiteCharge black root)
    (c : ℝ) (x : E → ℝ)
    (hx : x = c • N.gradient (fun v => if v ∈ A then 1 else 0)) :
    ∑ e, α e * x e = c * ((A.filter fun v => ¬black v).card : ℝ) := by
  simp only [hx,Pi.smul_apply,smul_eq_mul]
  have hh : ∑ e, α e * (c * N.gradient (fun v => if v ∈ A then 1 else 0) e) =
      c * ∑ e, α e * N.gradient (fun v => if v ∈ A then 1 else 0) e := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hh,← N.boundary_adjoint,hα]
  congr 1
  simp only [mul_ite,mul_one,mul_zero]
  rw [← Finset.sum_filter]
  simpa only [Finset.filter_mem_eq_inter,Finset.univ_inter] using whiteCharge_inside black root A hr

omit [Fintype V] [Fintype F] in
lemma white_positive_of_boundary (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (A : Finset V)
    (hcount : (N.cut A).card = 2 * (N.blackCut black A).card + 3) :
    0 < (A.filter fun v => ¬black v).card := by
  by_contra hn
  have hz : (A.filter fun v => ¬black v) = ∅ := Finset.card_eq_zero.mp (by omega)
  have hb : ∀ v ∈ A, black v := by
    intro v hv
    by_contra hnv
    have hh : v ∈ A.filter (fun v => ¬black v) := Finset.mem_filter.mpr ⟨hv,hnv⟩
    rw [hz] at hh
    exact Finset.notMem_empty _ hh
  have hEq : N.blackCut black A = N.cut A := by
    apply Finset.filter_eq_self.mpr
    intro e he
    rcases (N.mem_cut A e).mp he with ht | hh
    · rw [N.blackEndpoint_eq black hc (hb _ ht.1) (Or.inl rfl)]
      exact ht.1
    · rw [N.blackEndpoint_eq black hc (hb _ hh.1) (Or.inr rfl)]
      exact hh.1
  rw [hEq] at hcount
  omega

end
end Barnette.Network

end OAI


namespace OAI

/-! Triangle incidence states, opposite graphs, and oriented potentials. -/

namespace Barnette

structure TriangleSystem (A V : Type*) where
  vertex : A → Fin 3 → V
  vertex_injective : ∀ t, Function.Injective (vertex t)
  edge_unique : ∀ t u i j k l, i ≠ j → k ≠ l →
    vertex t i = vertex u k → vertex t j = vertex u l → t = u

namespace TriangleSystem

variable {A V : Type*} (T : TriangleSystem A V)

def State (X : Set V) :=
  {c : A → Fin 3 // Function.Injective (fun t => T.vertex t (c t)) ∧
    Set.range (fun t => T.vertex t (c t)) = X}

namespace State

variable {T} {X : Set V}

def value (s : T.State X) (t : A) : V := T.vertex t (s.val t)

theorem value_injective (s : T.State X) : Function.Injective s.value := s.property.1

theorem value_range (s : T.State X) : Set.range s.value = X := s.property.2

theorem value_mem (s : T.State X) (t : A) : s.value t ∈ X := by
  exact (Set.ext_iff.mp s.value_range _).mp ⟨t, rfl⟩

noncomputable def toEquiv (s : T.State X) : A ≃ X :=
  Equiv.ofBijective (fun t => ⟨s.value t, s.value_mem t⟩) ⟨by
    intro t u h
    exact s.value_injective (congrArg Subtype.val h), by
    intro v
    obtain ⟨t, ht⟩ := (Set.ext_iff.mp s.value_range v.val).mpr v.property
    exact ⟨t, Subtype.ext ht⟩⟩

@[simp] theorem coe_toEquiv (s : T.State X) (t : A) : (s.toEquiv t : V) = s.value t := rfl

theorem value_eq_iff (r s : T.State X) (t : A) :
    r.value t = s.value t ↔ r.val t = s.val t := T.vertex_injective t |>.eq_iff

theorem ext {r s : T.State X} (h : ∀ t, r.value t = s.value t) : r = s := by
  apply Subtype.ext
  funext t
  exact (value_eq_iff r s t).mp (h t)

instance [Finite A] : Finite (T.State X) := inferInstanceAs (Finite (Subtype _))

noncomputable instance [Fintype A] : Fintype (T.State X) := Fintype.ofFinite _

end State

theorem state_nonempty_iff (X : Set V) :
    Nonempty (T.State X) ↔ ∃ r : A ≃ X, ∀ t, (r t : V) ∈ Set.range (T.vertex t) := by
  classical
  constructor
  · rintro ⟨s⟩
    exact ⟨s.toEquiv, fun t => ⟨s.val t, rfl⟩⟩
  · rintro ⟨r, hr⟩
    choose c hc using hr
    refine ⟨⟨c, ?_, ?_⟩⟩
    · intro t u h
      apply r.injective
      exact Subtype.ext (by simpa only [hc] using h)
    · ext v
      constructor
      · rintro ⟨t, rfl⟩
        change T.vertex t (c t) ∈ X
        rw [hc t]
        exact (r t).property
      · intro hv
        obtain ⟨t, ht⟩ := r.surjective ⟨v, hv⟩
        exact ⟨t, (hc t).trans (congrArg Subtype.val ht)⟩

def Partner {X : Set V} (r s : T.State X) : Prop := ∀ t, r.value t ≠ s.value t

def thirdIndex (i j : Fin 3) : Fin 3 := -(i + j)

theorem thirdIndex_distinct : ∀ i j : Fin 3, i ≠ j →
    thirdIndex i j ≠ i ∧ thirdIndex i j ≠ j := by decide

theorem thirdIndex_involution : ∀ i j : Fin 3, thirdIndex (thirdIndex i j) j = i := by
  decide

theorem other_corners : ∀ i j r s : Fin 3,
    i ≠ j → i ≠ s → j ≠ s → r ≠ s →
    (i = r ∧ j = thirdIndex r s) ∨ (j = r ∧ i = thirdIndex r s) := by decide

def indexDelta (i j : Fin 3) : ℤ := if i = j then 0 else if j = i + 1 then 1 else -1

theorem indexDelta_antisymm : ∀ i j : Fin 3, indexDelta i j = -indexDelta j i := by
  decide

theorem indexDelta_third : ∀ i j : Fin 3, i ≠ j →
    indexDelta (thirdIndex i j) j - indexDelta i j =
      2 * indexDelta i (thirdIndex i j) := by decide

def oppositeGraph {X : Set V} (s : T.State X) : SimpleGraph V where
  Adj v w := v ≠ w ∧ ∃ t i j, T.vertex t i = v ∧ T.vertex t j = w ∧
    i ≠ s.val t ∧ j ≠ s.val t
  symm := ⟨by
    rintro v w ⟨hvw, t, i, j, hi, hj, his, hjs⟩
    exact ⟨hvw.symm, t, j, i, hj, hi, hjs, his⟩⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

theorem oppositeGraph_adj_iff {X : Set V} {r s : T.State X} (hrs : T.Partner r s)
    (v w : V) : (T.oppositeGraph s).Adj v w ↔
    ∃ t, (v = r.value t ∧ w = T.vertex t (thirdIndex (r.val t) (s.val t))) ∨
      (w = r.value t ∧ v = T.vertex t (thirdIndex (r.val t) (s.val t))) := by
  constructor
  · rintro ⟨hvw, t, i, j, hi, hj, his, hjs⟩
    have hij : i ≠ j := fun h => hvw (hi.symm.trans (h ▸ hj))
    have hrs' : r.val t ≠ s.val t := fun h => hrs t ((State.value_eq_iff r s t).mpr h)
    refine ⟨t, ?_⟩
    rcases other_corners i j (r.val t) (s.val t) hij his hjs hrs' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hi.symm, hj.symm⟩
    · exact Or.inr ⟨hj.symm, hi.symm⟩
  · rintro ⟨t, h | h⟩
    all_goals
      have hrs' : r.val t ≠ s.val t := fun h => hrs t ((State.value_eq_iff r s t).mpr h)
      have hne := thirdIndex_distinct (r.val t) (s.val t) hrs'
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨fun heq => hne.1 (T.vertex_injective t heq.symm),
        t, r.val t, thirdIndex (r.val t) (s.val t), rfl, rfl, hrs', hne.2⟩
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨fun heq => hne.1 (T.vertex_injective t heq),
        t, thirdIndex (r.val t) (s.val t), r.val t, rfl, rfl, hne.2, hrs'⟩

end TriangleSystem
end Barnette
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype F] in
lemma Triangle.oriented_cycleFlow (sN : N.Simple) (sD : D.Simple)
    (v : V) (t : D.Triangle (N.star v))
    (ht : ∀ i, N.gradient (fun w => if w = v then 1 else 0) (t.edge i) =
      D.arcSign (t.edge i) (t.corner i)) :
    D.cycleFlow (t.coordinates D) = N.gradient (fun w => if w = v then 1 else 0) := by
  ext e
  by_cases he : e ∈ N.star v
  · have hh : e ∈ Finset.univ.image t.edge := t.edge_range.symm ▸ he
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hh
    have hflow := D.cycleFlow_apply_edge (t.coordinates D) i
    change D.cycleFlow (t.coordinates D) (D.cycleEdge (t.coordinates D) i) =
      D.arcSign (D.cycleEdge (t.coordinates D) i) (t.corner i) at hflow
    rw [t.coordinates_edge D sD i] at hflow
    exact hflow.trans (ht i).symm
  · have heC : e ∉ D.cycleEdges (t.coordinates D) := by
      rw [t.coordinates_edges D sD]; exact he
    rw [D.cycleFlow_zero_outside _ heC]
    have hy : e ∉ D.flowSupport (N.gradient (fun w => if w = v then 1 else 0)) := by
      rw [N.gradient_indicator_support D sN v]; exact he
    have hz : N.gradient (fun w => if w = v then 1 else 0) e = 0 := by
      simpa only [mem_flowSupport,not_not] using hy
    exact hz.symm

omit [Fintype V] [Fintype F] in
lemma cycle_integral (C : Barnette.CycleCoordinates D.graph) (α : E → ℝ) :
    ∑ e, α e * D.cycleFlow C e =
      ∑ i, α (D.cycleEdge C i) * D.arcSign (D.cycleEdge C i) (C.vertex i) := by
  simp only [cycleFlow,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [basisVec,mul_ite]

omit [Fintype F] in
lemma Triangle.oriented_integral (sN : N.Simple) (sD : D.Simple)
    (v : V) (t : D.Triangle (N.star v))
    (ht : ∀ i, N.gradient (fun w => if w = v then 1 else 0) (t.edge i) =
      D.arcSign (t.edge i) (t.corner i)) (α : E → ℝ) :
    ∑ i, α (t.edge i) * D.arcSign (t.edge i) (t.corner i) = N.boundary α v := by
  have hh := D.cycle_integral (t.coordinates D) α
  rw [t.oriented_cycleFlow N D sN sD v ht] at hh
  have hb := N.boundary_adjoint α (fun w => if w = v then 1 else 0)
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hb
  rw [← hb] at hh
  have hf : D.cycleEdge (t.coordinates D) = t.edge := funext (t.coordinates_edge D sD)
  rw [hf] at hh
  exact hh.symm

omit [Fintype V] [Fintype E] [Fintype F] in
def Triangle.potential {s : Finset E} (t : D.Triangle s) (α : E → ℝ) : Fin 3 → ℝ :=
  ![0, α (t.edge 0) * D.arcSign (t.edge 0) (t.corner 0),
    α (t.edge 0) * D.arcSign (t.edge 0) (t.corner 0) +
      α (t.edge 1) * D.arcSign (t.edge 1) (t.corner 1)]

omit [Fintype V] [Fintype E] [Fintype F] in
lemma Triangle.potential_step {s : Finset E} (t : D.Triangle s) (α : E → ℝ)
    (hα : ∑ i, α (t.edge i) * D.arcSign (t.edge i) (t.corner i) = 0) (i : Fin 3) :
    t.potential D α (i+1) - t.potential D α i =
      α (t.edge i) * D.arcSign (t.edge i) (t.corner i) := by
  have hs : α (t.edge 0) * D.arcSign (t.edge 0) (t.corner 0) +
      α (t.edge 1) * D.arcSign (t.edge 1) (t.corner 1) +
      α (t.edge 2) * D.arcSign (t.edge 2) (t.corner 2) = 0 := by
    simpa [Fin.sum_univ_succ,add_assoc] using hα
  fin_cases i
  · change t.potential D α 1 - t.potential D α 0 =
      α (t.edge 0) * D.arcSign (t.edge 0) (t.corner 0)
    simp [potential]
  · change t.potential D α 2 - t.potential D α 1 =
      α (t.edge 1) * D.arcSign (t.edge 1) (t.corner 1)
    simp [potential]
  · change t.potential D α 0 - t.potential D α 2 =
      α (t.edge 2) * D.arcSign (t.edge 2) (t.corner 2)
    simp [potential]
    linarith

omit [Fintype V] [Fintype E] [Fintype F] in
def Triangle.side {s : Finset E} (t : D.Triangle s) (i j : Fin 3) : E :=
  if j = i+1 then t.edge i else t.edge j

omit [Fintype V] [Fintype E] [Fintype F] in
lemma Triangle.side_mem {s : Finset E} (t : D.Triangle s) (i j : Fin 3) :
    t.side D i j ∈ s := by
  have hh (k : Fin 3) : t.edge k ∈ s := by
    have hm : t.edge k ∈ Finset.univ.image t.edge := Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩
    rwa [t.edge_range] at hm
  unfold side
  split_ifs <;> apply hh

omit [Fintype V] [Fintype E] [Fintype F] in
lemma Triangle.side_ends {s : Finset E} (t : D.Triangle s) {i j : Fin 3} (hij : i ≠ j) :
    s(D.tail (t.side D i j),D.head (t.side D i j)) = s(t.corner i,t.corner j) := by
  have hfin : ∀ i j : Fin 3, i ≠ j → j = i+1 ∨ i = j+1 := by decide
  rcases hfin i j hij with hj | hi
  · simp only [side,ite_eq_left hj]
    exact (t.edge_ends i).trans (by rw [hj])
  · have hj : j ≠ i+1 := by
      intro hh
      exact (by decide : ∀ i j : Fin 3, i = j+1 → j = i+1 → False) i j hi hh
    simp only [side,ite_eq_right hj]
    exact (t.edge_ends j).trans (by rw [hi,Sym2.eq_swap])

omit [Fintype V] [Fintype E] [Fintype F] in
lemma Triangle.side_unique (sD : D.Simple) {s : Finset E} (t : D.Triangle s)
    {i j : Fin 3} (hij : i ≠ j) {e : E}
    (he : s(D.tail e,D.head e) = s(t.corner i,t.corner j)) : e = t.side D i j :=
  sD.pair_injective (he.trans (t.side_ends D hij).symm)

omit [Fintype V] [Fintype E] [Fintype F] in
lemma Triangle.potential_side {s : Finset E} (t : D.Triangle s) (α : E → ℝ)
    (hα : ∑ i, α (t.edge i) * D.arcSign (t.edge i) (t.corner i) = 0)
    {i j : Fin 3} (hij : i ≠ j) :
    t.potential D α j - t.potential D α i =
      α (t.side D i j) * D.arcSign (t.side D i j) (t.corner i) := by
  have hfin : ∀ i j : Fin 3, i ≠ j → j = i+1 ∨ i = j+1 := by decide
  rcases hfin i j hij with hj | hi
  · simp only [side,ite_eq_left hj]
    rw [hj]
    exact t.potential_step D α hα i
  · have hj : j ≠ i+1 := by
      intro hh
      exact (by decide : ∀ i j : Fin 3, i = j+1 → j = i+1 → False) i j hi hh
    simp only [side,ite_eq_right hj]
    have hne : t.corner j ≠ t.corner i := fun h => hij (t.corner_injective h).symm
    have he : s(D.tail (t.edge j),D.head (t.edge j)) = s(t.corner j,t.corner i) := by
      rw [t.edge_ends,hi]
    rw [D.arcSign_opposite hne he]
    have hs := t.potential_step D α hα j
    rw [← hi] at hs
    linarith

omit [Fintype V] [Fintype E] [Fintype F] in
lemma blackGradient_face (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) {v : V}
    (hv : black v) {e : E} (he : N.Incident e v) :
    N.gradient (fun w => if black w then 1 else 0) e =
      N.gradient (fun w => if w = v then 1 else 0) e := by
  have hcol := hc e
  rcases he with ht | hh
  · have hhead : ¬black (N.head e) := (hc e).mp (ht ▸ hv)
    have hne : N.head e ≠ v := fun hh => hhead (hh ▸ hv)
    simp [gradient_apply,ht,hhead,hne,hv]
  · have htail : ¬black (N.tail e) := fun ht => (hc e).mp ht (hh ▸ hv)
    have hne : N.tail e ≠ v := fun ht => htail (ht ▸ hv)
    simp [gradient_apply,hh,htail,hne,hv]

omit [Fintype V] [Fintype F] in
lemma Triangle.index_delta (v : V) (t : D.Triangle (N.star v))
    (ht : ∀ i, N.gradient (fun w => if w = v then 1 else 0) (t.edge i) =
      D.arcSign (t.edge i) (t.corner i)) (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (hv : black v)
    {i j : Fin 3} (hij : i ≠ j) :
    (Barnette.TriangleSystem.indexDelta i j : ℝ) =
      N.gradient (fun w => if black w then 1 else 0) (t.side D i j) *
        D.arcSign (t.side D i j) (t.corner i) := by
  rw [N.blackGradient_face black hc hv ((N.mem_star _ _).mp (t.side_mem D i j))]
  have hfin : ∀ i j : Fin 3, i ≠ j → j = i+1 ∨ i = j+1 := by decide
  rcases hfin i j hij with hj | hi
  · simp only [TriangleSystem.indexDelta,ite_eq_right hij,Int.cast_one,side,ite_eq_left hj,ht]
    unfold arcSign
    split_ifs <;> norm_num
  · have hj : j ≠ i+1 := by
      intro hh
      exact (by decide : ∀ i j : Fin 3, i = j+1 → j = i+1 → False) i j hi hh
    simp only [TriangleSystem.indexDelta,ite_eq_right hij,ite_eq_right hj,Int.cast_neg,Int.cast_one,side,ht]
    have hne : t.corner j ≠ t.corner i := fun h => hij (t.corner_injective h).symm
    have he : s(D.tail (t.edge j),D.head (t.edge j)) = s(t.corner j,t.corner i) := by
      rw [t.edge_ends,hi]
    rw [D.arcSign_opposite hne he]
    unfold arcSign
    split_ifs <;> norm_num

end
end Barnette.Network

end OAI


namespace OAI

/-! Colored dual networks and signed directed state cycles. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

structure ColoredDual where
  duality : N.Duality D
  simple : N.Simple
  dual_simple : D.Simple
  cubic : N.graph.IsRegularOfDegree 3
  black : V → Prop
  coloring : ∀ e, black (N.tail e) ↔ ¬black (N.head e)
  face : ∀ v, D.Triangle (N.star v)
  oriented : ∀ v i, N.gradient (fun w => if w = v then 1 else 0) ((face v).edge i) =
    D.arcSign ((face v).edge i) ((face v).corner i)

namespace ColoredDual
variable {N D} (M : N.ColoredDual D)

abbrev Black (root : V) := {v : V // M.black v ∧ v ≠ root}

def system (root : V) : Barnette.TriangleSystem (M.Black root) F where
  vertex t := (M.face t.val).corner
  vertex_injective t := (M.face t.val).corner_injective
  edge_unique t u i j k l hij hkl hik hjl := by
    have he : (M.face t.val).side D i j = (M.face u.val).side D k l := by
      apply M.dual_simple.pair_injective
      dsimp only
      rw [(M.face t.val).side_ends D hij,(M.face u.val).side_ends D hkl,hik,hjl]
    have ht := N.blackEndpoint_eq M.black M.coloring t.property.1
      ((N.mem_star _ _).mp ((M.face t.val).side_mem D i j))
    have hu := N.blackEndpoint_eq M.black M.coloring u.property.1
      ((N.mem_star _ _).mp ((M.face u.val).side_mem D k l))
    apply Subtype.ext
    exact ht.symm.trans (he ▸ hu)

def nonroots (root : V) : Set F := (Set.range (M.face root).corner)ᶜ

abbrev State (root : V) := (M.system root).State (M.nonroots root)

def assignment {root : V} (s : M.State root) (v : V) : F :=
  if hv : M.black v ∧ v ≠ root then s.value ⟨v,hv⟩ else (M.face root).corner 0

omit [Fintype F] in
@[simp] lemma assignment_apply {root : V} (s : M.State root) (v : M.Black root) :
    M.assignment s v.val = s.value v := by simp [assignment,v.property]

omit [Fintype F] in
lemma assignment_inj {root : V} (s : M.State root) :
    Set.InjOn (M.assignment s) {v | M.black v ∧ v ≠ root} := by
  intro v hv w hw h
  have hh : s.value ⟨v,hv⟩ = s.value ⟨w,hw⟩ :=
    (M.assignment_apply s ⟨v,hv⟩).symm.trans (h.trans (M.assignment_apply s ⟨w,hw⟩))
  exact congrArg Subtype.val (s.value_injective hh)

omit [Fintype F] in
lemma assignment_face {root : V} (s : M.State root) (v : V)
    (hv : M.black v) (hr : v ≠ root) :
    M.assignment s v ∈ Set.range (M.face v).corner := by
  rw [M.assignment_apply s ⟨v,hv,hr⟩]
  exact ⟨s.val ⟨v,hv,hr⟩,rfl⟩

omit [Fintype F] in
lemma assignment_range {root : V} (s : M.State root) (z : F) :
    z ∉ Set.range (M.face root).corner ↔
      ∃ v, M.black v ∧ v ≠ root ∧ M.assignment s v = z := by
  constructor
  · intro hz
    have hm : z ∈ M.nonroots root := hz
    obtain ⟨t,ht⟩ := (Set.ext_iff.mp s.value_range z).mpr hm
    exact ⟨t.val,t.property.1,t.property.2,(M.assignment_apply s t).trans ht⟩
  · rintro ⟨v,hv,hr,rfl⟩
    rw [M.assignment_apply s ⟨v,hv,hr⟩]
    exact s.value_mem ⟨v,hv,hr⟩

lemma cycle_disk {root : V} (s : M.State root)
    (C : Barnette.CycleCoordinates D.graph)
    (t : Fin (C.n+3) → M.Black root)
    (he : ∀ i, D.cycleEdge C i ∈ N.star (t i).val)
    (hv : ∀ i, s.value (t i) = C.vertex i) :
    ∃ (A : Finset V) (c : ℝ), A.Nonempty ∧ root ∉ A ∧ (c = 1 ∨ c = -1) ∧
      D.cycleFlow C = c • N.gradient (fun v => if v ∈ A then 1 else 0) ∧
      N.cut A = D.cycleEdges C ∧
      (N.cut A).card = 2 * (N.blackCut M.black A).card + 3 ∧
      N.blackDelta D M.black C = -3*c := by
  apply N.state_disk_delta D M.duality M.simple M.cubic M.dual_simple M.face
    M.black M.coloring root (M.assignment s) (M.assignment_inj s)
    (M.assignment_face s) (M.assignment_range s) C
  intro i
  have hb := N.blackEndpoint_eq M.black M.coloring (t i).property.1
    ((N.mem_star _ _).mp (he i))
  rw [hb]
  exact ⟨(t i).property.2,(M.assignment_apply s (t i)).trans (hv i)⟩

def weights (α : E → ℝ) (root : V) (t : M.Black root) : Fin 3 → ℝ :=
  (M.face t.val).potential D α

omit [Fintype F] in
lemma weights_diff (root : V) (α : E → ℝ)
    (hα : N.boundary α = whiteCharge M.black root)
    (t : M.Black root) {i j : Fin 3} (hij : i ≠ j) :
    M.weights α root t j - M.weights α root t i =
      α ((M.face t.val).side D i j) *
        D.arcSign ((M.face t.val).side D i j) ((M.face t.val).corner i) := by
  apply (M.face t.val).potential_side D α _ hij
  rw [(M.face t.val).oriented_integral N D M.simple M.dual_simple t.val
    (M.oriented t.val) α,hα]
  exact whiteCharge_black M.black root t.val t.property.1 t.property.2

end ColoredDual
end
end Barnette.Network
namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D)

structure StateCycle {root : V} (s : M.State root) where
  cycle : Barnette.CycleCoordinates D.graph
  face : Fin (cycle.n+3) → M.Black root
  corner : Fin (cycle.n+3) → Fin 3
  left_eq : ∀ i, s.value (face i) = cycle.vertex i
  right_eq : ∀ i, (M.face (face i).val).corner (corner i) = cycle.vertex (i+1)

namespace StateCycle
variable {M} {root : V} {s : M.State root} (C : M.StateCycle s)

omit [Fintype F] in
lemma corner_ne (i : Fin (C.cycle.n+3)) : s.val (C.face i) ≠ C.corner i := by
  intro hh
  have hv : C.cycle.vertex i = C.cycle.vertex (i+1) :=
    (C.left_eq i).symm.trans ((congrArg (M.face (C.face i).val).corner hh).trans (C.right_eq i))
  exact (C.cycle.adjacent i).1 hv

omit [Fintype F] in
lemma cycleEdge_eq (i : Fin (C.cycle.n+3)) :
    D.cycleEdge C.cycle i = (M.face (C.face i).val).side D (s.val (C.face i)) (C.corner i) := by
  apply (M.face (C.face i).val).side_unique D M.dual_simple (C.corner_ne i)
  rw [D.cycleEdge_ends,C.right_eq]
  change s(C.cycle.vertex i,C.cycle.vertex (i+1)) =
    s(s.value (C.face i),C.cycle.vertex (i+1))
  rw [C.left_eq]

omit [Fintype F] in
lemma edge_mem (i : Fin (C.cycle.n+3)) : D.cycleEdge C.cycle i ∈ N.star (C.face i).val := by
  rw [C.cycleEdge_eq]
  exact (M.face (C.face i).val).side_mem D _ _

def delta : ℤ := ∑ i, Barnette.TriangleSystem.indexDelta (s.val (C.face i)) (C.corner i)

def slope (α : E → ℝ) : ℝ :=
  ∑ i, (M.weights α root (C.face i) (C.corner i) - M.weights α root (C.face i) (s.val (C.face i)))

omit [Fintype F] in
lemma delta_eq : (C.delta : ℝ) = N.blackDelta D M.black C.cycle := by
  simp only [delta,Int.cast_sum,blackDelta]
  apply Finset.sum_congr rfl
  intro i _
  rw [(M.face (C.face i).val).index_delta N D (C.face i).val (M.oriented _)
    M.black M.coloring (C.face i).property.1 (C.corner_ne i),← C.cycleEdge_eq]
  change _ * D.arcSign _ (s.value (C.face i)) = _
  rw [C.left_eq]

omit [Fintype F] in
lemma slope_eq (α : E → ℝ) (hα : N.boundary α = whiteCharge M.black root) :
    C.slope α = ∑ e, α e * D.cycleFlow C.cycle e := by
  rw [D.cycle_integral]
  unfold slope
  apply Finset.sum_congr rfl
  intro i _
  rw [M.weights_diff root α hα (C.face i) (C.corner_ne i),← C.cycleEdge_eq]
  change _ * D.arcSign _ (s.value (C.face i)) = _
  rw [C.left_eq]

theorem signed (α : E → ℝ) (hα : N.boundary α = whiteCharge M.black root) :
    (C.delta = -3 ∧ 0 < C.slope α) ∨ (C.delta = 3 ∧ C.slope α < 0) := by
  obtain ⟨A,c,_ha,hr,hc,hflow,_hcut,hcount,hd⟩ :=
    M.cycle_disk s C.cycle C.face C.edge_mem C.left_eq
  have hδ : (C.delta : ℝ) = -3*c := C.delta_eq.trans hd
  have hs : C.slope α = c * ((A.filter fun v => ¬M.black v).card : ℝ) := by
    rw [C.slope_eq α hα]
    exact N.whiteCharge_cut_integral M.black root A hr α hα c _ hflow
  have hpos : (0:ℝ) < (A.filter fun v => ¬M.black v).card := by
    exact_mod_cast N.white_positive_of_boundary M.black M.coloring A hcount
  rcases hc with rfl | rfl
  · left
    constructor
    · have hh : (C.delta : ℝ) = (-3:ℝ) := by simpa using hδ
      exact_mod_cast hh
    · simpa [hs] using hpos
  · right
    constructor
    · have hh : (C.delta : ℝ) = (3:ℝ) := by simpa using hδ
      exact_mod_cast hh
    · simpa [hs] using neg_neg_of_pos hpos

end StateCycle
end
end Barnette.Network.ColoredDual

end OAI


namespace OAI

/-! Reversal involutions on partners of a fixed incidence state. -/

namespace Barnette

open Fin.NatCast

variable {V : Type*} {G : SimpleGraph V}

theorem cycleCoordinates_of_not_acyclic (hG : ¬G.IsAcyclic) :
    Nonempty (CycleCoordinates G) := by
  classical
  simp only [SimpleGraph.IsAcyclic, not_forall, not_not] at hG
  obtain ⟨v, p, hp⟩ := hG
  have hlen : 3 ≤ p.length := hp.isCircuit.three_le_length
  obtain ⟨f⟩ := (SimpleGraph.cycleGraph_isContained_iff (show 2 < p.length by omega)).mpr
    ⟨v, p, hp, rfl⟩
  have heq : p.length = (p.length - 3) + 3 := by omega
  rw [heq] at f
  refine ⟨⟨p.length - 3, ⟨f.toHom, f.injective⟩, ?_⟩⟩
  intro i
  apply f.toHom.map_adj
  apply SimpleGraph.cycleGraph_adj'.mpr
  right
  simp

namespace TriangleSystem

variable {A : Type*} (T : TriangleSystem A V) {X : Set V}

theorem opposite_indices : ∀ i j k l s : Fin 3,
    i ≠ j → k ≠ l → i ≠ s → j ≠ s → k ≠ s → l ≠ s →
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by decide

structure OppositeCycle (s : T.State X) where
  cycle : CycleCoordinates (T.oppositeGraph s)
  face : Fin (cycle.n + 3) ↪ A
  leftCorner : Fin (cycle.n + 3) → Fin 3
  rightCorner : Fin (cycle.n + 3) → Fin 3
  left_eq : ∀ i, T.vertex (face i) (leftCorner i) = cycle.vertex i
  right_eq : ∀ i, T.vertex (face i) (rightCorner i) = cycle.vertex (i + 1)
  left_ne : ∀ i, leftCorner i ≠ s.val (face i)
  right_ne : ∀ i, rightCorner i ≠ s.val (face i)

theorem oppositeCycle_nonempty (s : T.State X) (hc : ¬(T.oppositeGraph s).IsAcyclic) :
    Nonempty (T.OppositeCycle s) := by
  classical
  obtain ⟨C⟩ := cycleCoordinates_of_not_acyclic hc
  choose face l r hl hr hls hrs using fun i => (C.adjacent i).2
  have hlr (i) : l i ≠ r i := by
    intro h
    have hh : C.vertex i = C.vertex (i + 1) := (hl i).symm.trans (h ▸ hr i)
    have heq := C.vertex.injective hh
    apply cyclic_one_ne_zero C.n
    exact add_left_cancel (by simpa using heq.symm : i + 1 = i + 0)
  have hface : Function.Injective face := by
    intro i j hij
    have hls' := hls j
    have hrs' := hrs j
    rw [← hij] at hls' hrs'
    have h := opposite_indices (l i) (r i) (l j) (r j) (s.val (face i))
      (hlr i) (hlr j) (hls i) (hrs i) hls' hrs'
    apply C.edge_indices_unique i j
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · left
      exact ⟨(hl i).symm.trans (by rw [hij, h₁, hl]),
        (hr i).symm.trans (by rw [hij, h₂, hr])⟩
    · right
      exact ⟨(hl i).symm.trans (by rw [hij, h₁, hr]),
        (hr i).symm.trans (by rw [hij, h₂, hl])⟩
  exact ⟨⟨C, ⟨face, hface⟩, l, r, hl, hr, hls, hrs⟩⟩

namespace OppositeCycle

variable {T} {s r : T.State X} (C : T.OppositeCycle s)

theorem corner_ne (i : Fin (C.cycle.n + 3)) : C.leftCorner i ≠ C.rightCorner i := by
  intro h
  have heq : C.cycle.vertex i = C.cycle.vertex (i + 1) :=
    (C.left_eq i).symm.trans (h ▸ C.right_eq i)
  apply cyclic_one_ne_zero C.cycle.n
  exact add_left_cancel (by simpa using (C.cycle.vertex.injective heq).symm : i + 1 = i + 0)

theorem partner_endpoints (hrs : T.Partner r s) (i : Fin (C.cycle.n + 3)) :
    (r.value (C.face i) = C.cycle.vertex i ∧
      T.vertex (C.face i) (thirdIndex (r.val (C.face i)) (s.val (C.face i))) =
        C.cycle.vertex (i + 1)) ∨
    (r.value (C.face i) = C.cycle.vertex (i + 1) ∧
      T.vertex (C.face i) (thirdIndex (r.val (C.face i)) (s.val (C.face i))) =
        C.cycle.vertex i) := by
  have hne : r.val (C.face i) ≠ s.val (C.face i) :=
    fun h => hrs _ ((State.value_eq_iff r s _).mpr h)
  have h := other_corners (C.leftCorner i) (C.rightCorner i)
    (r.val (C.face i)) (s.val (C.face i)) (C.corner_ne i) (C.left_ne i) (C.right_ne i) hne
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · left
    exact ⟨by change T.vertex _ _ = _; rw [← h₁, C.left_eq],
      by rw [← h₂, C.right_eq]⟩
  · right
    exact ⟨by change T.vertex _ _ = _; rw [← h₁, C.right_eq],
      by rw [← h₂, C.left_eq]⟩

theorem partner_orientation (hrs : T.Partner r s) :
    (∀ i, r.value (C.face i) = C.cycle.vertex i) ∨
      (∀ i, r.value (C.face i) = C.cycle.vertex (i + 1)) := by
  apply C.cycle.tail_orientation C.face r.value r.value_injective
  intro i
  exact (C.partner_endpoints hrs i).imp And.left And.left

end OppositeCycle
end TriangleSystem
end Barnette

namespace Barnette.TriangleSystem

open Fin.NatCast

variable {A V : Type*} {T : TriangleSystem A V} {X : Set V} {s : T.State X}

namespace OppositeCycle

variable (C : T.OppositeCycle s)

noncomputable def changedCorners (r : T.State X) (t : A) : Fin 3 := by
  classical
  exact if t ∈ Set.range C.face then thirdIndex (r.val t) (s.val t) else r.val t

@[simp] theorem changedCorners_image (r : T.State X) (i : Fin (C.cycle.n + 3)) :
    C.changedCorners r (C.face i) = thirdIndex (r.val (C.face i)) (s.val (C.face i)) := by
  classical
  simp [changedCorners]

theorem changed_assignment_permutation (r : T.State X) (hrs : T.Partner r s) :
    ∃ e : Equiv.Perm A, ∀ t, T.vertex t (C.changedCorners r t) = r.value (e t) := by
  classical
  let f := Equiv.ofInjective C.face C.face.injective
  rcases C.partner_orientation hrs with hforward | hbackward
  · let e := (Equiv.addRight (1 : Fin (C.cycle.n + 3))).extendDomain f
    refine ⟨e, ?_⟩
    intro t
    by_cases ht : t ∈ Set.range C.face
    · obtain ⟨i, rfl⟩ := ht
      have he : e (C.face i) = C.face (i + 1) := by
        exact (Equiv.Perm.extendDomain_apply_image _ f i)
      rw [C.changedCorners_image, he, hforward]
      rcases C.partner_endpoints hrs i with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact ((C.cycle.adjacent i).1 ((hforward i).symm.trans h)).elim
    · rw [changedCorners, ite_eq_right ht, Equiv.Perm.extendDomain_apply_not_subtype _ f ht]
      rfl
  · let e := (Equiv.addRight (-1 : Fin (C.cycle.n + 3))).extendDomain f
    refine ⟨e, ?_⟩
    intro t
    by_cases ht : t ∈ Set.range C.face
    · obtain ⟨i, rfl⟩ := ht
      have he : e (C.face i) = C.face (i - 1) := by
        calc
          e (C.face i) = C.face (i + (-1 : Fin (C.cycle.n + 3))) :=
            Equiv.Perm.extendDomain_apply_image _ f i
          _ = C.face (i - 1) := congrArg C.face (sub_eq_add_neg i 1).symm
      rw [C.changedCorners_image, he, hbackward, sub_add_cancel]
      rcases C.partner_endpoints hrs i with ⟨h, _⟩ | ⟨_, h⟩
      · exact ((C.cycle.adjacent i).1 (h.symm.trans (hbackward i))).elim
      · exact h
    · rw [changedCorners, ite_eq_right ht, Equiv.Perm.extendDomain_apply_not_subtype _ f ht]
      rfl

noncomputable def reverse (r : T.State X) (hrs : T.Partner r s) : T.State X := by
  let e := (C.changed_assignment_permutation r hrs).choose
  have he : ∀ t, T.vertex t (C.changedCorners r t) = r.value (e t) :=
    (C.changed_assignment_permutation r hrs).choose_spec
  refine ⟨C.changedCorners r, ?_, ?_⟩
  · intro t u h
    change T.vertex t (C.changedCorners r t) = T.vertex u (C.changedCorners r u) at h
    rw [he t, he u] at h
    exact e.injective (r.value_injective h)
  · calc
      Set.range (fun t => T.vertex t (C.changedCorners r t)) = Set.range r.value := by
        ext v
        constructor
        · rintro ⟨t, rfl⟩
          exact ⟨e t, (he t).symm⟩
        · rintro ⟨u, rfl⟩
          refine ⟨e.symm u, ?_⟩
          change T.vertex (e.symm u) (C.changedCorners r (e.symm u)) = r.value u
          rw [he, e.apply_symm_apply]
      _ = X := r.value_range

@[simp] theorem reverse_val (r : T.State X) (hrs : T.Partner r s) :
    (C.reverse r hrs).val = C.changedCorners r := rfl

theorem reverse_partner (r : T.State X) (hrs : T.Partner r s) :
    T.Partner (C.reverse r hrs) s := by
  classical
  intro t h
  have hi : C.changedCorners r t = s.val t :=
    T.vertex_injective t h
  by_cases ht : t ∈ Set.range C.face
  · rw [changedCorners, ite_eq_left ht] at hi
    have hne : r.val t ≠ s.val t := fun h => hrs t ((State.value_eq_iff r s t).mpr h)
    exact (thirdIndex_distinct _ _ hne).2 hi
  · rw [changedCorners, ite_eq_right ht] at hi
    exact hrs t ((State.value_eq_iff r s t).mpr hi)

@[simp] theorem reverse_reverse (r : T.State X) (hrs : T.Partner r s) :
    C.reverse (C.reverse r hrs) (C.reverse_partner r hrs) = r := by
  classical
  apply Subtype.ext
  funext t
  change C.changedCorners (C.reverse r hrs) t = r.val t
  by_cases ht : t ∈ Set.range C.face
  · simp only [changedCorners, ht, ite_true, reverse_val, thirdIndex_involution]
  · simp only [changedCorners, ht, ite_false, reverse_val]

theorem reverse_ne (r : T.State X) (hrs : T.Partner r s) : C.reverse r hrs ≠ r := by
  intro h
  have heq := congrFun (congrArg Subtype.val h) (C.face 0)
  change C.changedCorners r (C.face 0) = r.val (C.face 0) at heq
  rw [C.changedCorners_image] at heq
  have hne : r.val (C.face 0) ≠ s.val (C.face 0) :=
    fun h => hrs _ ((State.value_eq_iff r s _).mpr h)
  exact (thirdIndex_distinct _ _ hne).1 heq

end OppositeCycle

def Partners (s : T.State X) := {r : T.State X // T.Partner r s}

namespace OppositeCycle

variable (C : T.OppositeCycle s)

noncomputable def reversal (r : T.Partners s) : T.Partners s :=
  ⟨C.reverse r.val r.property, C.reverse_partner r.val r.property⟩

theorem reversal_involutive : Function.Involutive C.reversal := by
  intro r
  apply Subtype.ext
  exact C.reverse_reverse r.val r.property

theorem reversal_ne (r : T.Partners s) : C.reversal r ≠ r := by
  intro h
  exact C.reverse_ne r.val r.property (congrArg Subtype.val h)

end OppositeCycle
end Barnette.TriangleSystem

end OAI


namespace OAI

/-! Paired states, permutation cycle classes, and phase cancellation. -/

namespace Barnette

noncomputable def phase (n : ℤ) : ℂ := Complex.I ^ (n / 3)

theorem phase_add_six (n : ℤ) : phase (n + 6) = -phase n := by
  unfold phase
  have h : (n + 6) / 3 = n / 3 + 2 := by omega
  rw [h, zpow_add₀ Complex.I_ne_zero]
  norm_num

theorem phase_sub_six (n : ℤ) : phase (n - 6) = -phase n := by
  have h := phase_add_six (n - 6)
  rw [sub_add_cancel] at h
  exact neg_eq_iff_eq_neg.mp h.symm

theorem disk_count_identity {B W I h l : ℤ}
    (heuler : B + W = 2 * I + h - 2) (hsides : 3 * (B - W) = 2 * l - h)
    (hmatching : B = I + l) : 2 * l - h = -3 := by omega

namespace TriangleSystem

variable {A V : Type*} {T : TriangleSystem A V} {X : Set V}

def rawIndexSum [Fintype A] (r s : T.State X) : ℤ :=
  ∑ t, indexDelta (r.val t) (s.val t)

noncomputable instance [Fintype A] (s : T.State X) : Fintype (T.Partners s) :=
  Fintype.ofFinite {r : T.State X // T.Partner r s}

namespace OppositeCycle

variable {s : T.State X} (C : T.OppositeCycle s)

noncomputable def faceSet : Finset A := by
  classical
  exact Finset.univ.image C.face

@[simp] theorem mem_faceSet (t : A) : t ∈ C.faceSet ↔ t ∈ Set.range C.face := by
  classical
  simp [faceSet]

def cyclicDelta (r : T.State X) : ℤ :=
  ∑ i, indexDelta (r.val (C.face i)) (thirdIndex (r.val (C.face i)) (s.val (C.face i)))

theorem reverse_rawIndexSum_diff [Fintype A] (r : T.State X) (hrs : T.Partner r s) :
    rawIndexSum (C.reverse r hrs) s - rawIndexSum r s = 2 * C.cyclicDelta r := by
  classical
  rw [rawIndexSum, rawIndexSum, ← Finset.sum_sub_distrib]
  let h (t : A) := indexDelta ((C.reverse r hrs).val t) (s.val t) -
    indexDelta (r.val t) (s.val t)
  change ∑ t, h t = _
  calc
    ∑ t, h t = ∑ t ∈ C.faceSet, h t := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro t _ ht
      have hnot : t ∉ Set.range C.face := fun h => ht ((C.mem_faceSet t).mpr h)
      simp only [h, reverse_val, changedCorners, ite_eq_right hnot, sub_self]
    _ = ∑ t ∈ C.faceSet,
        2 * indexDelta (r.val t) (thirdIndex (r.val t) (s.val t)) := by
      apply Finset.sum_congr rfl
      intro t ht
      have hrst : r.val t ≠ s.val t := fun h => hrs t ((State.value_eq_iff r s t).mpr h)
      change indexDelta (C.changedCorners r t) (s.val t) -
        indexDelta (r.val t) (s.val t) = _
      rw [changedCorners, ite_eq_left ((C.mem_faceSet t).mp ht)]
      exact indexDelta_third _ _ hrst
    _ = ∑ i, 2 * indexDelta (r.val (C.face i))
        (thirdIndex (r.val (C.face i)) (s.val (C.face i))) := by
      unfold faceSet
      apply Finset.sum_image
      exact C.face.injective.injOn
    _ = 2 * C.cyclicDelta r := by rw [cyclicDelta, Finset.mul_sum]

theorem reverse_phase [Fintype A] (r : T.State X) (hrs : T.Partner r s)
    (hdisk : C.cyclicDelta r = 3 ∨ C.cyclicDelta r = -3) :
    phase (rawIndexSum (C.reverse r hrs) s) = -phase (rawIndexSum r s) := by
  have hdiff := C.reverse_rawIndexSum_diff r hrs
  rcases hdisk with h | h
  · have heq : rawIndexSum (C.reverse r hrs) s = rawIndexSum r s + 6 := by omega
    rw [heq, phase_add_six]
  · have heq : rawIndexSum (C.reverse r hrs) s = rawIndexSum r s - 6 := by omega
    rw [heq, phase_sub_six]

theorem fixed_second_state_cancels [Fintype A] {M : Type*} [AddCommGroup M] [Module ℂ M]
    (hdisk : ∀ r : T.Partners s, C.cyclicDelta r.val = 3 ∨ C.cyclicDelta r.val = -3)
    (weight : M) : (∑ r : T.Partners s, phase (rawIndexSum r.val s) • weight) = 0 := by
  classical
  apply Finset.sum_ninvolution C.reversal
  · intro r
    change phase (rawIndexSum r.val s) • weight +
      phase (rawIndexSum (C.reverse r.val r.property) s) • weight = 0
    rw [C.reverse_phase r.val r.property (hdisk r), neg_smul, add_neg_cancel]
  · intro r _
    exact C.reversal_ne r
  · intro r
    exact Finset.mem_univ _
  · intro r
    exact C.reversal_involutive r

end OppositeCycle
end TriangleSystem
end Barnette

namespace Barnette

variable {A : Type*}

def CycleClass (p : Equiv.Perm A) := Quotient (Equiv.Perm.SameCycle.setoid p)

def classOf (p : Equiv.Perm A) (a : A) : CycleClass p := Quotient.mk _ a

noncomputable instance [Finite A] (p : Equiv.Perm A) : Fintype (CycleClass p) :=
  Fintype.ofFinite (Quotient (Equiv.Perm.SameCycle.setoid p))

@[simp] theorem classOf_apply (p : Equiv.Perm A) (a : A) : classOf p (p a) = classOf p a := by
  apply Quotient.sound
  exact (Equiv.Perm.SameCycle.refl p a).apply_left

@[simp] theorem classOf_symm_apply (p : Equiv.Perm A) (a : A) :
    classOf p (p.symm a) = classOf p a := by
  have h := classOf_apply p (p.symm a)
  simpa using h.symm

theorem classOf_surjective (p : Equiv.Perm A) : Function.Surjective (classOf p) :=
  Quotient.mk_surjective

theorem classOf_eq_iff (p : Equiv.Perm A) (a b : A) :
    classOf p a = classOf p b ↔ p.SameCycle a b := Quotient.eq

theorem invariant_on_cycle [Finite A] {p : Equiv.Perm A} {B : Type*} (f : A → B)
    (hf : ∀ a, f (p a) = f a) {a b : A} (hab : p.SameCycle a b) : f a = f b := by
  obtain ⟨n, rfl⟩ := hab.exists_nat_pow_eq
  have hpow : ∀ n : ℕ, ∀ a, f ((p ^ n) a) = f a := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih =>
      intro a
      rw [pow_succ', Equiv.Perm.mul_apply, hf, ih]
  exact (hpow n a).symm

noncomputable def descendCycle [Finite A] {p : Equiv.Perm A} {B : Type*} (f : A → B)
    (hf : ∀ a, f (p a) = f a) : CycleClass p → B :=
  Quotient.lift f (fun _ _ h => invariant_on_cycle f hf h)

@[simp] theorem descendCycle_classOf [Finite A] {p : Equiv.Perm A} {B : Type*} (f : A → B)
    (hf : ∀ a, f (p a) = f a) (a : A) : descendCycle f hf (classOf p a) = f a := rfl

def partialPerm (p : Equiv.Perm A) (b : A → Bool) (hb : ∀ a, b (p a) = b a) : Equiv.Perm A where
  toFun a := if b a then p a else a
  invFun a := if b a then p.symm a else a
  left_inv a := by
    cases h : b a <;> simp [h, hb]
  right_inv a := by
    have hb' (a) : b (p.symm a) = b a := by simpa using (hb (p.symm a)).symm
    cases h : b a <;> simp [h, hb']

@[simp] theorem partialPerm_apply (p : Equiv.Perm A) (b : A → Bool)
    (hb : ∀ a, b (p a) = b a) (a : A) :
    partialPerm p b hb a = if b a then p a else a := rfl

end Barnette

namespace Barnette.TriangleSystem

variable {A V : Type*} {T : TriangleSystem A V} {X : Set V}

def State.ofPermutation (s : T.State X) (e : Equiv.Perm A) (c : A → Fin 3)
    (hc : ∀ t, T.vertex t (c t) = s.value (e t)) : T.State X :=
  ⟨c, by
    constructor
    · intro t u h
      exact e.injective (s.value_injective (by simpa only [hc] using h))
    · rw [← s.value_range]
      ext v
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨e t, (hc t).symm⟩
      · rintro ⟨t, rfl⟩
        exact ⟨e.symm t, (hc _).trans (congrArg s.value (e.apply_symm_apply t))⟩⟩

def Pair (X : Set V) := {rs : T.State X × T.State X // T.Partner rs.1 rs.2}

namespace Pair

def left (P : @Pair A V T X) : T.State X := P.val.1
def right (P : @Pair A V T X) : T.State X := P.val.2

theorem partner (P : @Pair A V T X) : T.Partner P.left P.right := P.property

theorem ext {P Q : @Pair A V T X} (hl : P.left = Q.left)
    (hr : P.right = Q.right) : P = Q := Subtype.ext (Prod.ext hl hr)

instance [Finite A] : Finite (@Pair A V T X) := inferInstanceAs (Finite (Subtype _))
noncomputable instance [Fintype A] : Fintype (@Pair A V T X) := Fintype.ofFinite _

noncomputable def next (P : @Pair A V T X) : Equiv.Perm A :=
  P.right.toEquiv.trans P.left.toEquiv.symm

@[simp] theorem value_next (P : @Pair A V T X) (t : A) :
    P.left.value (P.next t) = P.right.value t := by
  change (P.left.toEquiv (P.left.toEquiv.symm (P.right.toEquiv t)) : V) = _
  rw [Equiv.apply_symm_apply, State.coe_toEquiv]

@[simp] theorem value_prev (P : @Pair A V T X) (t : A) :
    P.right.value (P.next.symm t) = P.left.value t := by
  have h := P.value_next (P.next.symm t)
  simpa using h.symm

theorem next_ne (P : @Pair A V T X) (t : A) : P.next t ≠ t := by
  intro h
  exact P.partner t (by simpa only [h] using P.value_next t)

def third (P : @Pair A V T X) : A → Fin 3 :=
  fun t => thirdIndex (P.left.val t) (P.right.val t)

def Group (P : @Pair A V T X) := {Q : @Pair A V T X // Q.third = P.third}

noncomputable instance [Fintype A] (P : @Pair A V T X) : Fintype P.Group :=
  Fintype.ofFinite {Q : @Pair A V T X // Q.third = P.third}

def flipCorners (r s : T.State X) (b : A → Bool) : A → Fin 3 :=
  fun t => if b t then s.val t else r.val t

noncomputable def flipLeft (P : @Pair A V T X) (b : A → Bool)
    (hb : ∀ t, b (P.next t) = b t) : T.State X :=
  P.left.ofPermutation (partialPerm P.next b hb) (flipCorners P.left P.right b) (by
    intro t
    cases h : b t
    · simp [flipCorners, h, State.value]
    · simpa only [flipCorners, h, ↓reduceIte, partialPerm_apply, State.value] using
        (P.value_next t).symm)

noncomputable def flipRight (P : @Pair A V T X) (b : A → Bool)
    (hb : ∀ t, b (P.next t) = b t) : T.State X :=
  P.right.ofPermutation
    (partialPerm P.next.symm b (fun t => by simpa using (hb (P.next.symm t)).symm))
    (flipCorners P.right P.left b) (by
      intro t
      cases h : b t
      · simp [flipCorners, h, State.value]
      · simpa only [flipCorners, h, ↓reduceIte, partialPerm_apply, State.value] using
          (P.value_prev t).symm)

@[simp] theorem flipLeft_val (P : @Pair A V T X) (b : A → Bool)
    (hb : ∀ t, b (P.next t) = b t) :
    (P.flipLeft b hb).val = flipCorners P.left P.right b := rfl

@[simp] theorem flipRight_val (P : @Pair A V T X) (b : A → Bool)
    (hb : ∀ t, b (P.next t) = b t) :
    (P.flipRight b hb).val = flipCorners P.right P.left b := rfl

@[simp] theorem flipLeft_value (P : @Pair A V T X) (b : A → Bool)
    (hb : ∀ t, b (P.next t) = b t) (t : A) :
    (P.flipLeft b hb).value t = if b t then P.right.value t else P.left.value t := by
  cases h : b t <;> simp [State.value, flipLeft_val, flipCorners, h]

@[simp] theorem flipRight_value (P : @Pair A V T X) (b : A → Bool)
    (hb : ∀ t, b (P.next t) = b t) (t : A) :
    (P.flipRight b hb).value t = if b t then P.left.value t else P.right.value t := by
  cases h : b t <;> simp [State.value, flipRight_val, flipCorners, h]

noncomputable def flip (P : @Pair A V T X) (b : A → Bool)
    (hb : ∀ t, b (P.next t) = b t) : @Pair A V T X :=
  ⟨(P.flipLeft b hb, P.flipRight b hb), by
    intro t
    change (P.flipLeft b hb).value t ≠ (P.flipRight b hb).value t
    rw [flipLeft_value, flipRight_value]
    cases h : b t
    · simpa [h] using P.partner t
    · simpa [h] using (P.partner t).symm⟩

theorem flip_third (P : @Pair A V T X) (b : A → Bool)
    (hb : ∀ t, b (P.next t) = b t) : (P.flip b hb).third = P.third := by
  funext t
  change thirdIndex (flipCorners P.left P.right b t) (flipCorners P.right P.left b t) = _
  cases h : b t <;> simp [flipCorners, h, third, thirdIndex, add_comm]

noncomputable def orient (P : @Pair A V T X) (b : CycleClass P.next → Bool) : P.Group :=
  ⟨P.flip (fun t => b (classOf P.next t)) (fun t => by rw [classOf_apply]),
    P.flip_third _ _⟩

theorem same_third_corners : ∀ i j k l : Fin 3, i ≠ j → k ≠ l →
    thirdIndex i j = thirdIndex k l → (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by decide

theorem group_local (P : @Pair A V T X) (Q : P.Group) (t : A) :
    (Q.val.left.val t = P.left.val t ∧ Q.val.right.val t = P.right.val t) ∨
    (Q.val.left.val t = P.right.val t ∧ Q.val.right.val t = P.left.val t) := by
  apply same_third_corners
  · exact fun h => Q.val.partner t ((State.value_eq_iff _ _ _).mpr h)
  · exact fun h => P.partner t ((State.value_eq_iff _ _ _).mpr h)
  · exact congrFun Q.property t

noncomputable def bits (P : @Pair A V T X) (Q : P.Group) (t : A) : Bool :=
  decide (Q.val.left.val t = P.right.val t)

theorem group_values (P : @Pair A V T X) (Q : P.Group) (t : A) :
    Q.val.left.value t = (if P.bits Q t then P.right.value t else P.left.value t) ∧
    Q.val.right.value t = (if P.bits Q t then P.left.value t else P.right.value t) := by
  have hn : P.left.val t ≠ P.right.val t := fun h =>
    P.partner t ((State.value_eq_iff _ _ _).mpr h)
  rcases P.group_local Q t with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;>
    simp [bits, hl, hr, hn, State.value]

theorem bits_invariant (P : @Pair A V T X) (Q : P.Group) (t : A) :
    P.bits Q (P.next t) = P.bits Q t := by
  have h0 := P.group_values Q t
  have h1 := P.group_values Q (P.next t)
  cases ht : P.bits Q t <;> cases hn : P.bits Q (P.next t)
  · rfl
  · simp only [ht, hn, Bool.false_eq_true, ↓reduceIte] at h0 h1
    exact False.elim (P.next_ne t (Q.val.right.value_injective
      (h1.2.trans ((P.value_next t).trans h0.2.symm))))
  · simp only [ht, hn, Bool.false_eq_true, ↓reduceIte] at h0 h1
    exact False.elim (P.next_ne t (Q.val.left.value_injective
      (h1.1.trans ((P.value_next t).trans h0.1.symm))))
  · rfl

noncomputable def orientations [Finite A] (P : @Pair A V T X) (Q : P.Group) :
    CycleClass P.next → Bool := descendCycle (P.bits Q) (P.bits_invariant Q)

@[simp] theorem orient_orientations [Finite A] (P : @Pair A V T X) (Q : P.Group) :
    P.orient (P.orientations Q) = Q := by
  apply Subtype.ext
  apply Pair.ext
  · apply State.ext
    intro t
    change (P.flipLeft (fun t => P.orientations Q (classOf P.next t))
      (fun t => by rw [classOf_apply])).value t = _
    rw [flipLeft_value]
    dsimp [orientations, descendCycle, classOf]
    exact (P.group_values Q t).1.symm
  · apply State.ext
    intro t
    change (P.flipRight (fun t => P.orientations Q (classOf P.next t))
      (fun t => by rw [classOf_apply])).value t = _
    rw [flipRight_value]
    dsimp [orientations, descendCycle, classOf]
    exact (P.group_values Q t).2.symm

@[simp] theorem orientations_orient [Finite A] (P : @Pair A V T X)
    (b : CycleClass P.next → Bool) : P.orientations (P.orient b) = b := by
  funext c
  obtain ⟨t, rfl⟩ := classOf_surjective P.next c
  change P.bits (P.orient b) t = b (classOf P.next t)
  have hn : P.left.val t ≠ P.right.val t := fun h =>
    P.partner t ((State.value_eq_iff _ _ _).mpr h)
  change decide ((if b (classOf P.next t) then P.right.val t else P.left.val t) =
    P.right.val t) = b (classOf P.next t)
  cases b (classOf P.next t) <;> simp [hn]

noncomputable def groupEquiv [Finite A] (P : @Pair A V T X) :
    (CycleClass P.next → Bool) ≃ P.Group where
  toFun := P.orient
  invFun := P.orientations
  left_inv := P.orientations_orient
  right_inv := P.orient_orientations

end Pair
end Barnette.TriangleSystem

end OAI


namespace OAI

/-! First nonzero coefficients of paired-state polynomials. -/

namespace Barnette

open scoped BigOperators Polynomial
open Polynomial

theorem common_phase_sum_ne_zero {D : Type*} (s : Finset D) (hs : s.Nonempty)
    (c : D → ℕ) (p : D → ℂ[X]) (a : D → ℝ)
    (ha : ∀ d ∈ s, 0 < a d)
    (hp : ∀ d ∈ s, (p d).coeff 0 = (a d : ℂ)) :
    (∑ d ∈ s, C ((-Complex.I) ^ c d) * (X ^ c d * p d)) ≠ 0 := by
  classical
  obtain ⟨d₀, hd₀, hmin⟩ := s.exists_min_image c hs
  let m := c d₀
  let t := s.filter (fun d => c d = m)
  have ht : t.Nonempty := ⟨d₀, Finset.mem_filter.mpr ⟨hd₀, rfl⟩⟩
  have hpos : 0 < ∑ d ∈ t, a d := by
    exact Finset.sum_pos (fun d hd => ha d (Finset.mem_filter.mp hd).1) ht
  have hterm (d : D) (hd : d ∈ s) :
      (C ((-Complex.I) ^ c d) * (X ^ c d * p d)).coeff m =
        if c d = m then (-Complex.I) ^ m * (a d : ℂ) else 0 := by
    rw [coeff_C_mul, coeff_X_pow_mul']
    by_cases heq : c d = m
    · simp only [heq, le_refl, ite_true, Nat.sub_self, hp d hd]
    · have hlt : m < c d := lt_of_le_of_ne (hmin d hd) (Ne.symm heq)
      simp only [heq, not_le.mpr hlt, ite_false, mul_zero]
  have hcoeff :
      (∑ d ∈ s, C ((-Complex.I) ^ c d) * (X ^ c d * p d)).coeff m =
        (-Complex.I) ^ m * (∑ d ∈ t, a d : ℝ) := by
    rw [finsetSum_coeff]
    calc
      _ = ∑ d ∈ s, if c d = m then (-Complex.I) ^ m * (a d : ℂ) else 0 :=
        Finset.sum_congr rfl hterm
      _ = _ := by
        simp only [t, Finset.sum_filter, Complex.ofReal_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        split_ifs <;> simp only [Complex.ofReal_zero, mul_zero]
  intro hz
  have hnz : (-Complex.I) ^ m * ((∑ d ∈ t, a d : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero))
      (by exact_mod_cast ne_of_gt hpos)
  apply hnz
  rw [← hcoeff, hz, coeff_zero]

noncomputable def linearProduct {A R : Type*} [CommRing R] (s : Finset A) (a : A → R) : R[X] :=
  ∏ t ∈ s, (1 + C (a t) * X)

@[simp] theorem linearProduct_coeff_zero {A R : Type*} [CommRing R]
    (s : Finset A) (a : A → R) : (linearProduct s a).coeff 0 = 1 := by
  simp [linearProduct, coeff_zero_prod]

theorem linearProduct_coeff_one {A R : Type*} [CommRing R]
    (s : Finset A) (a : A → R) : (linearProduct s a).coeff 1 = ∑ t ∈ s, a t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [linearProduct, coeff_one]
  | @insert t s ht ih =>
    rw [linearProduct, Finset.prod_insert ht, mul_coeff_one]
    change (1 + C (a t) * X).coeff 0 * (linearProduct s a).coeff 1 +
      (1 + C (a t) * X).coeff 1 * (linearProduct s a).coeff 0 = _
    simp [ih, Finset.sum_insert ht, add_comm, coeff_one]

theorem cycle_difference_divX_coeff_zero {A R : Type*} [CommRing R]
    (s : Finset A) (a b : A → R) :
    (divX (linearProduct s a - linearProduct s b)).coeff 0 =
      (∑ t ∈ s, a t) - ∑ t ∈ s, b t := by
  rw [coeff_divX, zero_add, coeff_sub, linearProduct_coeff_one, linearProduct_coeff_one]

theorem cycle_difference_eq_X_mul_divX {A R : Type*} [CommRing R]
    (s : Finset A) (a b : A → R) :
    linearProduct s a - linearProduct s b =
      X * divX (linearProduct s a - linearProduct s b) := by
  have h := X_mul_divX_add (linearProduct s a - linearProduct s b)
  simpa using h.symm

theorem cycle_group_polynomials_ne_zero {D A : Type*}
    (s : Finset D) (hs : s.Nonempty) (cycles : D → Finset A)
    (q : D → A → ℂ[X]) (a : D → A → ℝ)
    (ha : ∀ d ∈ s, ∀ t ∈ cycles d, 0 < a d t)
    (hq : ∀ d ∈ s, ∀ t ∈ cycles d, (q d t).coeff 0 = (a d t : ℂ)) :
    (∑ d ∈ s, ∏ t ∈ cycles d, C (-Complex.I) * (X * q d t)) ≠ 0 := by
  have h := common_phase_sum_ne_zero s hs (fun d => (cycles d).card)
    (fun d => ∏ t ∈ cycles d, q d t) (fun d => ∏ t ∈ cycles d, a d t)
    (fun d hd => Finset.prod_pos (ha d hd)) (by
      intro d hd
      rw [coeff_zero_prod, Complex.ofReal_prod]
      exact Finset.prod_congr rfl (hq d hd))
  convert h using 1
  apply Finset.sum_congr rfl
  intro d _
  simp only [Finset.prod_mul_distrib, Finset.prod_const, ← map_pow]

end Barnette

namespace Barnette

open scoped BigOperators Polynomial
open Polynomial

theorem phase_sum {K : Type*} (s : Finset K) (a : K → ℤ)
    (ha : ∀ k ∈ s, 3 ∣ a k) : phase (∑ k ∈ s, a k) = ∏ k ∈ s, phase (a k) := by
  classical
  unfold phase
  rw [Int.sum_div ha]
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.prod_insert hk, zpow_add₀ Complex.I_ne_zero]
    congr 1
    exact ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))

@[simp] theorem phase_three : phase 3 = Complex.I := by norm_num [phase]
@[simp] theorem phase_neg_three : phase (-3) = -Complex.I := by norm_num [phase, Complex.inv_I]

theorem phase_neg_of_disk {n : ℤ} (hn : n = 3 ∨ n = -3) : phase (-n) = -phase n := by
  rcases hn with rfl | rfl <;> norm_num

namespace TriangleSystem.Pair

variable {A V : Type*} [Fintype A] {T : TriangleSystem A V} {X : Set V}

noncomputable def cycleFaces (P : @Pair A V T X) (c : CycleClass P.next) : Finset A := by
  classical
  exact Finset.univ.filter (fun t => classOf P.next t = c)

@[simp] theorem mem_cycleFaces (P : @Pair A V T X) (c : CycleClass P.next) (t : A) :
    t ∈ P.cycleFaces c ↔ classOf P.next t = c := by
  classical
  simp [cycleFaces]

noncomputable def cycleDelta (P : @Pair A V T X) (c : CycleClass P.next) : ℤ :=
  ∑ t ∈ P.cycleFaces c, indexDelta (P.left.val t) (P.right.val t)

omit [Fintype A] in
@[simp] theorem orient_left_val (P : @Pair A V T X) (b : CycleClass P.next → Bool) (t : A) :
    (P.orient b).val.left.val t =
      if b (classOf P.next t) then P.right.val t else P.left.val t := rfl

omit [Fintype A] in
@[simp] theorem orient_right_val (P : @Pair A V T X) (b : CycleClass P.next → Bool) (t : A) :
    (P.orient b).val.right.val t =
      if b (classOf P.next t) then P.left.val t else P.right.val t := rfl

theorem orient_delta_sum (P : @Pair A V T X) (b : CycleClass P.next → Bool)
    (c : CycleClass P.next) :
    (∑ t ∈ P.cycleFaces c, indexDelta ((P.orient b).val.left.val t)
        ((P.orient b).val.right.val t)) =
      if b c then -P.cycleDelta c else P.cycleDelta c := by
  classical
  rw [cycleDelta]
  cases hb : b c
  · simp only [Bool.false_eq_true, ↓reduceIte]
    apply Finset.sum_congr rfl
    intro t ht
    rw [orient_left_val, orient_right_val, (P.mem_cycleFaces c t).mp ht, hb]
    rfl
  · simp only [↓reduceIte, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    rw [orient_left_val, orient_right_val, (P.mem_cycleFaces c t).mp ht, hb]
    exact indexDelta_antisymm _ _

theorem orient_rawIndexSum (P : @Pair A V T X) (b : CycleClass P.next → Bool) :
    rawIndexSum (P.orient b).val.left (P.orient b).val.right =
      ∑ c, if b c then -P.cycleDelta c else P.cycleDelta c := by
  classical
  unfold rawIndexSum
  rw [← Finset.sum_fiberwise Finset.univ (classOf P.next)]
  apply Finset.sum_congr rfl
  intro c _
  exact P.orient_delta_sum b c

theorem orient_phase (P : @Pair A V T X)
    (hdisk : ∀ c, P.cycleDelta c = 3 ∨ P.cycleDelta c = -3)
    (b : CycleClass P.next → Bool) :
    phase (rawIndexSum (P.orient b).val.left (P.orient b).val.right) =
      ∏ c, if b c then -phase (P.cycleDelta c) else phase (P.cycleDelta c) := by
  classical
  rw [P.orient_rawIndexSum b, phase_sum]
  · apply Finset.prod_congr rfl
    intro c _
    cases hb : b c <;> simp [phase_neg_of_disk (hdisk c)]
  · intro c _
    rcases hdisk c with h | h <;> cases b c <;> simp [h]

noncomputable def stateWeight (w : A → Fin 3 → ℝ) (s : T.State X) : ℂ[X] :=
  linearProduct Finset.univ (fun t => (w t (s.val t) : ℂ))

noncomputable def cycleLeftWeight (P : @Pair A V T X) (w : A → Fin 3 → ℝ)
    (c : CycleClass P.next) : ℂ[X] :=
  linearProduct (P.cycleFaces c) (fun t => (w t (P.left.val t) : ℂ))

noncomputable def cycleRightWeight (P : @Pair A V T X) (w : A → Fin 3 → ℝ)
    (c : CycleClass P.next) : ℂ[X] :=
  linearProduct (P.cycleFaces c) (fun t => (w t (P.right.val t) : ℂ))

theorem orient_weight (P : @Pair A V T X) (w : A → Fin 3 → ℝ)
    (b : CycleClass P.next → Bool) : stateWeight w (P.orient b).val.right =
      ∏ c, if b c then P.cycleLeftWeight w c else P.cycleRightWeight w c := by
  classical
  unfold stateWeight linearProduct
  rw [← Finset.prod_fiberwise Finset.univ (classOf P.next)]
  apply Finset.prod_congr rfl
  intro c _
  change (∏ t ∈ P.cycleFaces c, _) = _
  cases hb : b c
  · simp only [Bool.false_eq_true, ↓reduceIte, cycleRightWeight, linearProduct]
    apply Finset.prod_congr rfl
    intro t ht
    rw [orient_right_val, (P.mem_cycleFaces c t).mp ht, hb]
    rfl
  · simp only [↓reduceIte, cycleLeftWeight, linearProduct]
    apply Finset.prod_congr rfl
    intro t ht
    rw [orient_right_val, (P.mem_cycleFaces c t).mp ht, hb]
    rfl

noncomputable def term (w : A → Fin 3 → ℝ) (P : @Pair A V T X) : ℂ[X] :=
  C (phase (rawIndexSum P.left P.right)) * stateWeight w P.right

theorem orient_term (P : @Pair A V T X) (w : A → Fin 3 → ℝ)
    (hdisk : ∀ c, P.cycleDelta c = 3 ∨ P.cycleDelta c = -3)
    (b : CycleClass P.next → Bool) : term w (P.orient b).val =
      ∏ c, if b c then -C (phase (P.cycleDelta c)) * P.cycleLeftWeight w c
        else C (phase (P.cycleDelta c)) * P.cycleRightWeight w c := by
  classical
  rw [term, P.orient_phase hdisk, P.orient_weight, map_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro c _
  cases b c <;> simp

theorem group_sum_product (P : @Pair A V T X) (w : A → Fin 3 → ℝ)
    (hdisk : ∀ c, P.cycleDelta c = 3 ∨ P.cycleDelta c = -3) :
    (∑ Q : P.Group, term w Q.val) =
      ∏ c, C (phase (P.cycleDelta c)) *
        (P.cycleRightWeight w c - P.cycleLeftWeight w c) := by
  classical
  rw [← Fintype.sum_equiv P.groupEquiv _ (fun Q : P.Group => term w Q.val)
    (fun _ => rfl)]
  calc
    _ = ∑ b : CycleClass P.next → Bool,
        ∏ c, if b c then -C (phase (P.cycleDelta c)) * P.cycleLeftWeight w c
          else C (phase (P.cycleDelta c)) * P.cycleRightWeight w c := by
      apply Finset.sum_congr rfl
      intro b _
      exact P.orient_term w hdisk b
    _ = ∏ c, ∑ b : Bool, if b then -C (phase (P.cycleDelta c)) * P.cycleLeftWeight w c
          else C (phase (P.cycleDelta c)) * P.cycleRightWeight w c :=
      (Fintype.prod_sum (ι := CycleClass P.next) (κ := fun _ => Bool)
        (fun c b => if b then -C (phase (P.cycleDelta c)) * P.cycleLeftWeight w c
          else C (phase (P.cycleDelta c)) * P.cycleRightWeight w c)).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro c _
      rw [Fintype.sum_bool]
      simp only [↓reduceIte, Bool.false_eq_true]
      ring

end TriangleSystem.Pair
end Barnette
namespace Barnette

open scoped BigOperators Polynomial
open Polynomial

namespace TriangleSystem.Pair

variable {A V : Type*} [Fintype A] {T : TriangleSystem A V} {X : Set V}

noncomputable def cycleSlope (P : @Pair A V T X) (w : A → Fin 3 → ℝ)
    (c : CycleClass P.next) : ℝ :=
  (∑ t ∈ P.cycleFaces c, w t (P.right.val t)) -
    ∑ t ∈ P.cycleFaces c, w t (P.left.val t)

theorem cycle_diff_coeff_one (P : @Pair A V T X) (w : A → Fin 3 → ℝ)
    (c : CycleClass P.next) :
    (divX (P.cycleRightWeight w c - P.cycleLeftWeight w c)).coeff 0 =
      (P.cycleSlope w c : ℂ) := by
  rw [cycleRightWeight, cycleLeftWeight, cycle_difference_divX_coeff_zero]
  simp only [cycleSlope, Complex.ofReal_sub, Complex.ofReal_sum]

theorem cycle_factor_witness (P : @Pair A V T X) (w : A → Fin 3 → ℝ)
    (c : CycleClass P.next)
    (hsign : (P.cycleDelta c = -3 ∧ 0 < P.cycleSlope w c) ∨
      (P.cycleDelta c = 3 ∧ P.cycleSlope w c < 0)) :
    ∃ (q : ℂ[X]) (a : ℝ), 0 < a ∧ q.coeff 0 = (a : ℂ) ∧
      C (phase (P.cycleDelta c)) * (P.cycleRightWeight w c - P.cycleLeftWeight w c) =
        C (-Complex.I) * (Polynomial.X * q) := by
  rcases hsign with ⟨hd, hs⟩ | ⟨hd, hs⟩
  · refine ⟨divX (P.cycleRightWeight w c - P.cycleLeftWeight w c),
      P.cycleSlope w c, hs, P.cycle_diff_coeff_one w c, ?_⟩
    rw [hd, phase_neg_three]
    congr 1
    exact cycle_difference_eq_X_mul_divX _ _ _
  · refine ⟨-divX (P.cycleRightWeight w c - P.cycleLeftWeight w c),
      -P.cycleSlope w c, neg_pos.mpr hs, ?_, ?_⟩
    · rw [coeff_neg, P.cycle_diff_coeff_one, Complex.ofReal_neg]
    · rw [hd, phase_three]
      have heq : P.cycleRightWeight w c - P.cycleLeftWeight w c =
          Polynomial.X * divX (P.cycleRightWeight w c - P.cycleLeftWeight w c) :=
        cycle_difference_eq_X_mul_divX _ _ _
      calc
        _ = C Complex.I * (Polynomial.X *
            divX (P.cycleRightWeight w c - P.cycleLeftWeight w c)) := congrArg _ heq
        _ = _ := by simp only [map_neg, mul_neg, neg_mul, neg_neg]

def GroupIndex : Type _ := Set.range (@third A V T X)

noncomputable instance : Fintype (@GroupIndex A V T X) :=
  Fintype.ofFinite (Set.range (@third A V T X))

noncomputable def GroupIndex.representative (d : @GroupIndex A V T X) : @Pair A V T X :=
  Classical.choose d.property

omit [Fintype A] in
theorem GroupIndex.representative_third (d : @GroupIndex A V T X) : d.representative.third = d.val :=
  Classical.choose_spec d.property

def groupIndex (P : @Pair A V T X) : @GroupIndex A V T X := ⟨P.third, P, rfl⟩

noncomputable def GroupIndex.fiberEquivGroup (d : @GroupIndex A V T X) :
    {P : @Pair A V T X // P.groupIndex = d} ≃ d.representative.Group :=
  Equiv.subtypeEquivRight (fun P => by
    constructor
    · intro h
      have hh := congrArg Subtype.val h
      change P.third = d.val at hh
      exact hh.trans d.representative_third.symm
    · intro h
      apply Subtype.ext
      exact h.trans d.representative_third)

theorem sum_groups (w : A → Fin 3 → ℝ) :
    (∑ P : @Pair A V T X, term w P) =
      ∑ d : @GroupIndex A V T X, ∑ Q : d.representative.Group, term w Q.val := by
  classical
  rw [← Fintype.sum_fiberwise groupIndex (term w)]
  apply Finset.sum_congr rfl
  intro d _
  exact Fintype.sum_equiv d.fiberEquivGroup _ _ (fun _ => rfl)

theorem total_sum_ne_zero (hex : Nonempty (@Pair A V T X)) (w : A → Fin 3 → ℝ)
    (hsign : ∀ (P : @Pair A V T X) c,
      (P.cycleDelta c = -3 ∧ 0 < P.cycleSlope w c) ∨
      (P.cycleDelta c = 3 ∧ P.cycleSlope w c < 0)) :
    (∑ P : @Pair A V T X, term w P) ≠ 0 := by
  classical
  let D := @GroupIndex A V T X
  have hnonempty : (Finset.univ : Finset D).Nonempty :=
    ⟨hex.some.groupIndex, Finset.mem_univ _⟩
  have hw : ∀ d : D, ∀ c : CycleClass d.representative.next,
      ∃ (q : ℂ[X]) (a : ℝ), 0 < a ∧ q.coeff 0 = (a : ℂ) ∧
        C (phase (d.representative.cycleDelta c)) *
          (d.representative.cycleRightWeight w c - d.representative.cycleLeftWeight w c) =
            C (-Complex.I) * (Polynomial.X * q) := by
    intro d c
    exact d.representative.cycle_factor_witness w c (hsign d.representative c)
  choose q a ha hq hf using hw
  have h := common_phase_sum_ne_zero Finset.univ hnonempty
    (fun d : D => Fintype.card (CycleClass d.representative.next))
    (fun d => ∏ c, q d c) (fun d => ∏ c, a d c)
    (fun d _ => Finset.prod_pos (fun c _ => ha d c)) (by
      intro d _
      rw [coeff_zero_prod, Complex.ofReal_prod]
      exact Finset.prod_congr rfl (fun c _ => hq d c))
  rw [sum_groups]
  convert h using 1
  apply Finset.sum_congr rfl
  intro d _
  rw [d.representative.group_sum_product w (fun c => by
    rcases hsign d.representative c with ⟨hd, _⟩ | ⟨hd, _⟩
    · exact Or.inr hd
    · exact Or.inl hd)]
  calc
    _ = ∏ c, C (-Complex.I) * (Polynomial.X * q d c) :=
      Finset.prod_congr rfl (fun c _ => hf d c)
    _ = _ := by simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      ← map_pow]

end TriangleSystem.Pair
end Barnette
namespace Barnette

open scoped BigOperators Polynomial
open Polynomial

namespace TriangleSystem.Pair

variable {A V : Type*} [Fintype A] {T : TriangleSystem A V} {X : Set V}

noncomputable def secondFiberEquiv (s : T.State X) :
    {P : @Pair A V T X // P.right = s} ≃ T.Partners s where
  toFun P := ⟨P.val.left,
    Eq.mp (congrArg (fun z => T.Partner P.val.left z) P.property) P.val.partner⟩
  invFun r := ⟨⟨(r.val, s), r.property⟩, rfl⟩
  left_inv P := by
    apply Subtype.ext
    apply Pair.ext
    · rfl
    · exact P.property.symm
  right_inv _ := rfl

theorem sum_second_states (w : A → Fin 3 → ℝ) :
    (∑ P : @Pair A V T X, term w P) =
      ∑ s : T.State X, ∑ r : T.Partners s,
        C (phase (rawIndexSum r.val s)) * stateWeight w s := by
  classical
  rw [← Fintype.sum_fiberwise right (term w)]
  apply Finset.sum_congr rfl
  intro s _
  apply Fintype.sum_equiv (secondFiberEquiv s)
  intro P
  change C (phase (rawIndexSum P.val.left P.val.right)) * stateWeight w P.val.right = _
  rw [P.property]
  rfl

theorem forest_pair_of_disk_circulation (hex : Nonempty (@Pair A V T X))
    (hdisk : ∀ (s : T.State X) (C : T.OppositeCycle s) (r : T.Partners s),
      C.cyclicDelta r.val = 3 ∨ C.cyclicDelta r.val = -3)
    (w : A → Fin 3 → ℝ)
    (hsign : ∀ (P : @Pair A V T X) c,
      (P.cycleDelta c = -3 ∧ 0 < P.cycleSlope w c) ∨
      (P.cycleDelta c = 3 ∧ P.cycleSlope w c < 0)) :
    ∃ P : @Pair A V T X, (T.oppositeGraph P.right).IsAcyclic := by
  classical
  by_contra hforest
  have hcyclic (P : @Pair A V T X) : ¬(T.oppositeGraph P.right).IsAcyclic :=
    fun h => hforest ⟨P, h⟩
  apply total_sum_ne_zero hex w hsign
  rw [sum_second_states]
  apply Finset.sum_eq_zero
  intro s _
  by_cases hp : Nonempty (T.Partners s)
  · let P : @Pair A V T X := ⟨(hp.some.val, s), hp.some.property⟩
    obtain ⟨C⟩ := T.oppositeCycle_nonempty s (hcyclic P)
    simpa only [Polynomial.smul_eq_C_mul] using
      C.fixed_second_state_cancels (hdisk s C) (stateWeight w s)
  · have : IsEmpty (T.Partners s) := not_nonempty_iff.mp hp
    exact Finset.sum_eq_zero (fun r _ => isEmptyElim r)

end TriangleSystem.Pair
end Barnette

end OAI


namespace OAI

/-! Common-phase nonvanishing and forest extraction from actual states. -/

namespace Barnette
noncomputable section
open scoped Classical

structure PermutationCoordinates {A : Type*} (p : Equiv.Perm A) (a : A) where
  n : ℕ
  face : Fin (n+3) ↪ A
  step : ∀ i, face (i+1) = p (face i)
  range_eq : Set.range face = {b | p.SameCycle a b}

lemma permutationCoordinates_exists {A : Type*} [Finite A] (p : Equiv.Perm A) (a : A)
    (h1 : p a ≠ a) (h2 : p (p a) ≠ a) : Nonempty (PermutationCoordinates p a) := by
  have hp : 0 < Function.minimalPeriod p a :=
    Function.minimalPeriod_pos_of_mem_periodicPts (p.injective.mem_periodicPts a)
  have hp1 : Function.minimalPeriod p a ≠ 1 := by
    intro hh
    have hh' := Function.iterate_minimalPeriod (f := (p : A → A)) (x := a)
    rw [hh] at hh'
    exact h1 (by simpa using hh')
  have hp2 : Function.minimalPeriod p a ≠ 2 := by
    intro hh
    have hh' := Function.iterate_minimalPeriod (f := (p : A → A)) (x := a)
    rw [hh] at hh'
    exact h2 (by simpa [Function.iterate_succ_apply] using hh')
  let n := Function.minimalPeriod p a - 3
  have hn : n+3 = Function.minimalPeriod p a := by omega
  let f : Fin (n+3) → A := fun i => (p : A → A)^[i.val] a
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact Function.iterate_injOn_Iio_minimalPeriod (by simpa only [← hn, Set.mem_Iio] using i.isLt)
      (by simpa only [← hn, Set.mem_Iio] using j.isLt) hij
  refine ⟨⟨n,⟨f,hf⟩,?_,?_⟩⟩
  · intro i
    change (p : A → A)^[(i+1).val] a = p ((p : A → A)^[i.val] a)
    have hval : (i+1).val = (i.val+1) % Function.minimalPeriod p a := by
      rw [Fin.val_add]
      simp only [Fin.val_one,hn]
    rw [hval,Function.iterate_mod_minimalPeriod_eq,Function.iterate_succ_apply']
  · ext b
    constructor
    · rintro ⟨i,rfl⟩
      change p.SameCycle a ((p : A → A)^[i.val] a)
      rw [← Equiv.Perm.coe_pow]
      exact (Equiv.Perm.SameCycle.refl p a).pow_right
    · intro hb
      obtain ⟨m,hm⟩ := hb.exists_nat_pow_eq
      refine ⟨⟨m % Function.minimalPeriod p a,by rw [hn]; exact Nat.mod_lt _ hp⟩,?_⟩
      change (p : A → A)^[m % Function.minimalPeriod p a] a = b
      rw [Function.iterate_mod_minimalPeriod_eq,← Equiv.Perm.coe_pow,hm]

namespace TriangleSystem.Pair
variable {A V : Type*} {T : TriangleSystem A V} {X : Set V}

lemma next_next_ne (P : @Pair A V T X) (t : A) : P.next (P.next t) ≠ t := by
  intro hh
  have hrt : P.left.val t ≠ P.right.val t := fun he =>
    P.partner t ((State.value_eq_iff _ _ _).mpr he)
  have hru : P.right.val (P.next t) ≠ P.left.val (P.next t) := fun he =>
    P.partner (P.next t) ((State.value_eq_iff _ _ _).mpr he.symm)
  have hx : T.vertex t (P.left.val t) = T.vertex (P.next t) (P.right.val (P.next t)) := by
    change P.left.value t = P.right.value (P.next t)
    rw [← P.value_next,hh]
  have hy : T.vertex t (P.right.val t) = T.vertex (P.next t) (P.left.val (P.next t)) :=
    (P.value_next t).symm
  exact P.next_ne t (T.edge_unique _ _ _ _ _ _ hrt hru hx hy).symm

variable [Fintype A]

def cycleCoordinates (P : @Pair A V T X) (a : A) : PermutationCoordinates P.next a :=
  (permutationCoordinates_exists P.next a (P.next_ne a) (P.next_next_ne a)).some

lemma cycleCoordinates_faces (P : @Pair A V T X) (c : CycleClass P.next) (a : A)
    (ha : classOf P.next a = c) :
    Finset.univ.image (P.cycleCoordinates a).face = P.cycleFaces c := by
  ext b
  simp only [Finset.mem_image,Finset.mem_univ,true_and,mem_cycleFaces]
  change b ∈ Set.range (P.cycleCoordinates a).face ↔ _
  rw [(P.cycleCoordinates a).range_eq]
  change P.next.SameCycle a b ↔ _
  rw [← classOf_eq_iff,ha]
  exact eq_comm

end TriangleSystem.Pair
end
end Barnette
namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
open Barnette.TriangleSystem
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

def pairedCycle (P : (M.system root).Pair (M.nonroots root)) (a : M.Black root) :
    M.StateCycle P.left where
  cycle :=
    { n := (P.cycleCoordinates a).n
      vertex := ⟨fun i => P.left.value ((P.cycleCoordinates a).face i),
        P.left.value_injective.comp (P.cycleCoordinates a).face.injective⟩
      adjacent := by
        intro i
        let t := (P.cycleCoordinates a).face i
        have ht : P.left.value ((P.cycleCoordinates a).face (i+1)) = P.right.value t := by
          rw [(P.cycleCoordinates a).step,P.value_next]
        change D.graph.Adj (P.left.value t) (P.left.value ((P.cycleCoordinates a).face (i+1)))
        rw [ht]
        have hij : P.left.val t ≠ P.right.val t := fun hh =>
          P.partner t ((State.value_eq_iff _ _ _).mpr hh)
        exact ⟨P.partner t,(M.face t.val).side D (P.left.val t) (P.right.val t),
          Sym2.eq_iff.mp ((M.face t.val).side_ends D hij)⟩ }
  face := (P.cycleCoordinates a).face
  corner i := P.right.val ((P.cycleCoordinates a).face i)
  left_eq _ := rfl
  right_eq i := by
    change P.right.value ((P.cycleCoordinates a).face i) =
      P.left.value ((P.cycleCoordinates a).face (i+1))
    rw [(P.cycleCoordinates a).step,P.value_next]

omit [Fintype F] in
lemma pairedCycle_delta (P : (M.system root).Pair (M.nonroots root))
    (c : Barnette.CycleClass P.next) (a : M.Black root) (ha : Barnette.classOf P.next a = c) :
    (M.pairedCycle P a).delta = P.cycleDelta c := by
  let : DecidableEq (M.Black root) := Classical.decEq _
  change (∑ i, indexDelta (P.left.val ((P.cycleCoordinates a).face i))
    (P.right.val ((P.cycleCoordinates a).face i))) =
      ∑ t ∈ P.cycleFaces c, indexDelta (P.left.val t) (P.right.val t)
  rw [← P.cycleCoordinates_faces c a ha]
  exact (Finset.sum_image (f := fun t => indexDelta (P.left.val t) (P.right.val t))
    (s := Finset.univ) (P.cycleCoordinates a).face.injective.injOn).symm

omit [Fintype F] in
lemma pairedCycle_slope (P : (M.system root).Pair (M.nonroots root))
    (c : Barnette.CycleClass P.next) (a : M.Black root) (ha : Barnette.classOf P.next a = c)
    (α : E → ℝ) :
    (M.pairedCycle P a).slope α = P.cycleSlope (M.weights α root) c := by
  let : DecidableEq (M.Black root) := Classical.decEq _
  change (∑ i, (M.weights α root ((P.cycleCoordinates a).face i)
    (P.right.val ((P.cycleCoordinates a).face i)) -
      M.weights α root ((P.cycleCoordinates a).face i)
        (P.left.val ((P.cycleCoordinates a).face i)))) =
      (∑ t ∈ P.cycleFaces c, M.weights α root t (P.right.val t)) -
        (∑ t ∈ P.cycleFaces c, M.weights α root t (P.left.val t))
  rw [← P.cycleCoordinates_faces c a ha,Finset.sum_sub_distrib]
  congr 1
  · exact (Finset.sum_image (f := fun t => M.weights α root t (P.right.val t))
      (s := Finset.univ) (P.cycleCoordinates a).face.injective.injOn).symm
  · exact (Finset.sum_image (f := fun t => M.weights α root t (P.left.val t))
      (s := Finset.univ) (P.cycleCoordinates a).face.injective.injOn).symm

lemma paired_sign (P : (M.system root).Pair (M.nonroots root))
    (c : Barnette.CycleClass P.next) (α : E → ℝ)
    (hα : N.boundary α = whiteCharge M.black root) :
    (P.cycleDelta c = -3 ∧ 0 < P.cycleSlope (M.weights α root) c) ∨
      (P.cycleDelta c = 3 ∧ P.cycleSlope (M.weights α root) c < 0) := by
  obtain ⟨a,ha⟩ := Barnette.classOf_surjective P.next c
  have hh := (M.pairedCycle P a).signed α hα
  rwa [M.pairedCycle_delta P c a ha,M.pairedCycle_slope P c a ha α] at hh

omit [Fintype F] in
lemma opposite_forward_end {s r : M.State root} (C : (M.system root).OppositeCycle s)
    (hrs : (M.system root).Partner r s)
    (hf : ∀ i, r.value (C.face i) = C.cycle.vertex i) (i : Fin (C.cycle.n+3)) :
    (M.system root).vertex (C.face i) (thirdIndex (r.val (C.face i)) (s.val (C.face i))) =
      C.cycle.vertex (i+1) := by
  rcases C.partner_endpoints hrs i with ⟨_,he⟩ | ⟨he,_⟩
  · exact he
  · exact ((C.cycle.adjacent i).1 ((hf i).symm.trans he)).elim

def oppositeForward {s r : M.State root} (C : (M.system root).OppositeCycle s)
    (hrs : (M.system root).Partner r s)
    (hf : ∀ i, r.value (C.face i) = C.cycle.vertex i) : M.StateCycle r where
  cycle :=
    { n := C.cycle.n
      vertex := C.cycle.vertex
      adjacent i := by
        have hij : r.val (C.face i) ≠ thirdIndex (r.val (C.face i)) (s.val (C.face i)) :=
          (thirdIndex_distinct _ _ (fun hh => hrs _ ((State.value_eq_iff _ _ _).mpr hh))).1.symm
        have he := (M.face (C.face i).val).side_ends D hij
        change s(D.tail _,D.head _) = s(r.value (C.face i),
          (M.system root).vertex (C.face i) (thirdIndex (r.val (C.face i)) (s.val (C.face i)))) at he
        rw [hf,M.opposite_forward_end C hrs hf] at he
        exact ⟨(C.cycle.adjacent i).1,_,Sym2.eq_iff.mp he⟩ }
  face := C.face
  corner i := thirdIndex (r.val (C.face i)) (s.val (C.face i))
  left_eq := hf
  right_eq := M.opposite_forward_end C hrs hf

omit [Fintype F] in
lemma oppositeForward_delta {s r : M.State root} (C : (M.system root).OppositeCycle s)
    (hrs : (M.system root).Partner r s)
    (hf : ∀ i, r.value (C.face i) = C.cycle.vertex i) :
    (M.oppositeForward C hrs hf).delta = C.cyclicDelta r := rfl

lemma opposite_disk {s : M.State root} (C : (M.system root).OppositeCycle s)
    (r : (M.system root).Partners s) (α : E → ℝ)
    (hα : N.boundary α = whiteCharge M.black root) :
    C.cyclicDelta r.val = 3 ∨ C.cyclicDelta r.val = -3 := by
  rcases C.partner_orientation r.property with hf | hb
  · have hs := (M.oppositeForward C r.property hf).signed α hα
    rw [M.oppositeForward_delta] at hs
    exact hs.elim (fun h => Or.inr h.1) (fun h => Or.inl h.1)
  · let r' := C.reverse r.val r.property
    have hrs' : (M.system root).Partner r' s := C.reverse_partner r.val r.property
    have hf : ∀ i, r'.value (C.face i) = C.cycle.vertex i := by
      intro i
      have hr : r'.value (C.face i) = (M.system root).vertex (C.face i)
          (thirdIndex (r.val.val (C.face i)) (s.val (C.face i))) := by
        change (M.system root).vertex _ (C.changedCorners r.val (C.face i)) = _
        rw [C.changedCorners_image]
      rw [hr]
      rcases C.partner_endpoints r.property i with ⟨he,_⟩ | ⟨_,he⟩
      · exact ((C.cycle.adjacent i).1 (he.symm.trans (hb i))).elim
      · exact he
    have hδ : C.cyclicDelta r' = -C.cyclicDelta r.val := by
      unfold OppositeCycle.cyclicDelta
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      change indexDelta (C.changedCorners r.val (C.face i))
        (thirdIndex (C.changedCorners r.val (C.face i)) (s.val (C.face i))) = _
      rw [C.changedCorners_image,thirdIndex_involution,indexDelta_antisymm]
    have hs := (M.oppositeForward C hrs' hf).signed α hα
    rw [M.oppositeForward_delta,hδ] at hs
    rcases hs with ⟨hs,_⟩ | ⟨hs,_⟩
    · left; omega
    · right; omega

theorem forest_pair (hex : Nonempty ((M.system root).Pair (M.nonroots root))) :
    ∃ P : (M.system root).Pair (M.nonroots root), ((M.system root).oppositeGraph P.right).IsAcyclic := by
  obtain ⟨α,hα⟩ := N.boundary_of_sum_zero M.duality.connected
    (whiteCharge M.black root) (whiteCharge_sum M.black root)
  exact Pair.forest_pair_of_disk_circulation hex
    (fun _ C r => M.opposite_disk C r α hα) (M.weights α root)
    (fun P c => M.paired_sign P c α hα)

end
end Barnette.Network.ColoredDual
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)
omit [Fintype V] [Fintype E] in
lemma connected_of_kernel_constants [Nonempty V]
    (hc : ∀ f : V → ℝ, N.gradient f = 0 → ∀ v w, f v = f w) : N.graph.Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, inferInstance⟩
  intro v w
  by_contra hw
  let f : V → ℝ := fun z => if N.graph.Reachable v z then 1 else 0
  have hf : N.gradient f = 0 := by
    apply (N.gradient_eq_zero_iff f).mpr
    intro e
    have he := N.edge_reachable e
    have hh : N.graph.Reachable v (N.head e) ↔ N.graph.Reachable v (N.tail e) :=
      ⟨fun h => h.trans he.symm, fun h => h.trans he⟩
    simp only [f, hh]
  have he := hc f hf v w
  simp [f, hw] at he

variable {F : Type*} [Fintype F]
abbrev Components (H : Network F E) := H.graph.ConnectedComponent

instance componentsFintype (H : Network F E) : Fintype H.Components := Fintype.ofFinite _

def componentMap (H : Network F E) : F → H.Components := H.graph.connectedComponentMk

omit [Fintype E] [Fintype F] in
lemma componentMap_surjective (H : Network F E) : Function.Surjective H.componentMap := by
  intro c
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h f => exact ⟨f, rfl⟩

omit [Fintype E] [Fintype F] in
lemma gradient_componentMap (H : Network F E) (f : H.Components → ℝ) :
    H.gradient (pull H.componentMap f) = 0 := by
  apply (H.gradient_eq_zero_iff _).mpr
  intro e
  exact congrArg f (SimpleGraph.ConnectedComponent.sound (H.edge_reachable e)).symm

omit [Fintype E] [Fintype F] in
lemma descends_components (H : Network F E) (g : F → ℝ) (hg : H.gradient g = 0) :
    ∃ f : H.Components → ℝ, pull H.componentMap f = g := by
  refine ⟨Quot.lift g (fun v w h => H.gradient_zero_reachable hg h), ?_⟩
  rfl

end
end Barnette.Network

end OAI


namespace OAI

/-! Contraction and deletion of finite oriented dual networks. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

def inducedEdges (U : Finset F) : Finset E :=
  Finset.univ.filter fun e => D.tail e ∈ U ∧ D.head e ∈ U

omit [Fintype F] in
@[simp] lemma mem_inducedEdges (U : Finset F) (e : E) :
    e ∈ D.inducedEdges U ↔ D.tail e ∈ U ∧ D.head e ∈ U := by
  simp [inducedEdges]

def inducedNetwork (U : Finset F) : Network U (D.inducedEdges U) where
  tail e := ⟨D.tail e.val,((D.mem_inducedEdges U e.val).mp e.property).1⟩
  head e := ⟨D.head e.val,((D.mem_inducedEdges U e.val).mp e.property).2⟩

omit [Fintype F] in
lemma inducedNetwork_map (U : Finset F) :
    (D.inducedNetwork U).mapVertices Subtype.val =
      D.restrict (Subtype.val : D.inducedEdges U → E) := rfl

lemma inducedNetwork_boundary (U : Finset F) (x : D.inducedEdges U → ℝ) :
    push (Subtype.val : U → F) ((D.inducedNetwork U).boundary x) =
      D.boundary (push Subtype.val x) := by
  rw [← boundary_mapVertices,D.inducedNetwork_map,boundary_restrict]

def regions (U : Finset F) : Network V {e // e ∉ D.inducedEdges U} :=
  N.restrict Subtype.val

abbrev Regions (U : Finset F) := (N.regions D U).Components

def regionQuotient (U : Finset F) : Network (N.Regions D U) (D.inducedEdges U) :=
  (N.mapVertices (N.regions D U).componentMap).restrict Subtype.val

omit [Fintype V] [Fintype F] in
lemma regionQuotient_connected (hN : N.graph.Connected) (U : Finset F) :
    (N.regionQuotient D U).graph.Connected := by
  let H := N.regions D U
  let q := H.componentMap
  let L := N.regionQuotient D U
  have : Nonempty V := hN.nonempty
  have : Nonempty H.Components := Nonempty.map q inferInstance
  apply L.connected_of_kernel_constants
  intro f hf a b
  obtain ⟨a',rfl⟩ := H.componentMap_surjective a
  obtain ⟨b',rfl⟩ := H.componentMap_surjective b
  apply N.gradient_zero_reachable (f := pull q f) _ (hN a' b')
  ext e
  by_cases he : e ∈ D.inducedEdges U
  · exact congrFun hf ⟨e,he⟩
  · exact congrFun (H.gradient_componentMap f) ⟨e,he⟩

omit [Fintype V] in

lemma induced_cycles_eq_regions (h : N.Duality D) (U : Finset F) :
    (D.inducedNetwork U).boundary.ker = (N.regionQuotient D U).gradient.range := by
  let H := N.regions D U
  let q := H.componentMap
  ext x
  constructor
  · intro hx
    have hx' : (D.inducedNetwork U).boundary x = 0 := hx
    have hz : D.boundary (push (Subtype.val : D.inducedEdges U → E) x) = 0 := by
      rw [← D.inducedNetwork_boundary,hx',map_zero]
    obtain ⟨g,hg⟩ : ∃ g, N.gradient g = push (Subtype.val : D.inducedEdges U → E) x := by
      have hh : push (Subtype.val : D.inducedEdges U → E) x ∈ D.boundary.ker := hz
      rw [h.dual_cycles_eq_cuts] at hh
      exact hh
    have hgH : H.gradient g = 0 := by
      ext e
      change N.gradient g e.val = 0
      rw [hg]
      exact push_eq_zero_outside x (by simpa using e.property)
    obtain ⟨f,hf⟩ := H.descends_components g hgH
    refine ⟨f,?_⟩
    change pull (Subtype.val : D.inducedEdges U → E) (N.gradient (pull q f)) = x
    rw [hf,hg,pull_push_injective Subtype.val_injective]
  · rintro ⟨f,rfl⟩
    have hext : push (Subtype.val : D.inducedEdges U → E)
        ((N.regionQuotient D U).gradient f) = N.gradient (pull q f) := by
      ext e
      by_cases he : e ∈ D.inducedEdges U
      · exact push_subtype_apply (D.inducedEdges U) _ ⟨e,he⟩
      · rw [push_eq_zero_outside _ (by simpa using he)]
        exact (congrFun (H.gradient_componentMap f) ⟨e,he⟩).symm
    have hz : push (Subtype.val : U → F)
        ((D.inducedNetwork U).boundary ((N.regionQuotient D U).gradient f)) = 0 := by
      rw [D.inducedNetwork_boundary,hext]
      exact h.dual_conserved_gradient N D _
    have hz' := congrArg (pull (Subtype.val : U → F)) hz
    rw [pull_push_injective Subtype.val_injective,map_zero] at hz'
    exact hz'

omit [Fintype F] in
lemma rank_boundary_le [Nonempty V] :
    Module.finrank ℝ N.boundary.range + 1 ≤ Fintype.card V := by
  have hle : (constant (V := V)).range ≤ N.gradient.ker := by
    rintro _ ⟨c,rfl⟩
    exact N.gradient_const c
  have hi : Function.Injective (constant (V := V)) := by
    intro a b hh
    exact congrFun hh (Classical.choice inferInstance)
  have hk : 1 ≤ Module.finrank ℝ N.gradient.ker := by
    have hh := Submodule.finrank_mono hle
    rwa [LinearMap.finrank_range_of_inj hi,Module.finrank_self] at hh
  have hr : Module.finrank ℝ N.boundary.range = Module.finrank ℝ N.gradient.range := by
    rw [N.gradient_matrix,boundary,Matrix.toLin'_apply',Matrix.toLin'_apply',
      ← Matrix.rank,← Matrix.rank,Matrix.rank_transpose]
  have hh := N.gradient.finrank_range_add_finrank_ker
  rw [Module.finrank_pi] at hh
  omega

lemma induced_euler_bound (h : N.Duality D) (U : Finset F) (hU : U.Nonempty) :
    (D.inducedEdges U).card + 2 ≤ U.card + Fintype.card (N.Regions D U) := by
  have : Nonempty U := by obtain ⟨u,hu⟩ := hU; exact ⟨⟨u,hu⟩⟩
  have hr := (D.inducedNetwork U).rank_boundary_le
  have hk := (D.inducedNetwork U).boundary.finrank_range_add_finrank_ker
  rw [Module.finrank_pi,Fintype.card_coe] at hk
  rw [N.induced_cycles_eq_regions D h U] at hk
  have ho := (N.regionQuotient D U).rank_gradient (N.regionQuotient_connected D h.connected U)
  simp only [Fintype.card_coe] at hr
  omega

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] in
lemma star_count (hN : N.Simple) (v : V) :
    (N.star v).card = ∑ e, ((if N.tail e = v then 1 else 0) +
      (if N.head e = v then 1 else 0)) := by
  rw [star,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro e _
  have hne := hN.loopless e
  by_cases ht : N.tail e = v <;> by_cases hh : N.head e = v <;> simp_all [Incident]

lemma weighted_stars (hN : N.Simple) (f : V → ℤ) :
    ∑ v, f v * (N.star v).card = ∑ e, (f (N.tail e) + f (N.head e)) := by
  simp only [N.star_count hN,Nat.cast_sum,Nat.cast_add,Nat.cast_ite,Nat.cast_one,
    Nat.cast_zero,Finset.mul_sum,mul_add,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp [Finset.sum_add_distrib,eq_comm]

def colorSign (black : V → Prop) (v : V) : ℤ := if black v then 1 else -1

omit [Fintype V] [Fintype E] in
lemma colorSign_add (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (e : E) :
    colorSign black (N.tail e) + colorSign black (N.head e) = 0 := by
  have he := hc e
  by_cases ht : black (N.tail e) <;> by_cases hh : black (N.head e) <;>
    simp_all [colorSign]

lemma colorSign_sum (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) :
    ∑ v, colorSign black v = 0 := by
  have hs := N.weighted_stars hN (colorSign black)
  have hv : ∀ v, (N.star v).card = 3 := fun v => (N.card_star hN v).trans (h3 v)
  simp only [hv,N.colorSign_add black hc,Finset.sum_const_zero,Nat.cast_ofNat,
    ← Finset.sum_mul] at hs
  omega

def regionShore (U : Finset F) (q : N.Regions D U) : Finset V :=
  Finset.univ.filter fun v => (N.regions D U).componentMap v = q

omit [Fintype F] in
@[simp] lemma mem_regionShore (U : Finset F) (q : N.Regions D U) (v : V) :
    v ∈ N.regionShore D U q ↔ (N.regions D U).componentMap v = q := by
  simp [regionShore]

omit [Fintype F] in
lemma regionShore_nonempty (U : Finset F) (q : N.Regions D U) :
    (N.regionShore D U q).Nonempty := by
  obtain ⟨v,hv⟩ := (N.regions D U).componentMap_surjective q
  exact ⟨v,(N.mem_regionShore D U q v).mpr hv⟩

omit [Fintype F] in
lemma regionShore_off_edge (U : Finset F) (q : N.Regions D U) {e : E}
    (he : e ∉ D.inducedEdges U) :
    N.tail e ∈ N.regionShore D U q ↔ N.head e ∈ N.regionShore D U q := by
  simp only [N.mem_regionShore]
  have hh : (N.regions D U).componentMap (N.tail e) =
      (N.regions D U).componentMap (N.head e) :=
    SimpleGraph.ConnectedComponent.sound ((N.regions D U).edge_reachable ⟨e,he⟩)
  rw [hh]

def rim (U : Finset F) (q : N.Regions D U) : ℕ :=
  ∑ e ∈ D.inducedEdges U, ((if N.tail e ∈ N.regionShore D U q then 1 else 0) +
    (if N.head e ∈ N.regionShore D U q then 1 else 0))

def blackRim (black : V → Prop) (U : Finset F) (q : N.Regions D U) : ℕ :=
  ∑ e ∈ D.inducedEdges U, ((if N.tail e ∈ N.regionShore D U q ∧ black (N.tail e) then 1 else 0) +
    (if N.head e ∈ N.regionShore D U q ∧ black (N.head e) then 1 else 0))

def regionBalance (black : V → Prop) (U : Finset F) (q : N.Regions D U) : ℤ :=
  ∑ v ∈ N.regionShore D U q, colorSign black v

omit [Fintype F] in
lemma blackRim_le (black : V → Prop) (U : Finset F) (q : N.Regions D U) :
    N.blackRim D black U q ≤ N.rim D U q := by
  apply Finset.sum_le_sum
  intro e _
  by_cases ht : N.tail e ∈ N.regionShore D U q <;>
    by_cases hh : N.head e ∈ N.regionShore D U q <;>
    by_cases bt : black (N.tail e) <;> by_cases bh : black (N.head e) <;> simp [ht,hh,bt,bh]

omit [Fintype F] in
lemma region_balance_rim (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (U : Finset F) (q : N.Regions D U) :
    3 * N.regionBalance D black U q = 2 * (N.blackRim D black U q : ℤ) - N.rim D U q := by
  let A := N.regionShore D U q
  let f : V → ℤ := fun v => if v ∈ A then colorSign black v else 0
  have hs := N.weighted_stars hN f
  have hv : ∀ v, (N.star v).card = 3 := fun v => (N.card_star hN v).trans (h3 v)
  have hleft : (∑ v, f v * (N.star v).card) = 3 * N.regionBalance D black U q := by
    simp only [hv,Nat.cast_ofNat,← Finset.sum_mul,f]
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,regionBalance,A,mul_comm]
  rw [hleft] at hs
  have hreduce : (∑ e, (f (N.tail e) + f (N.head e))) =
      ∑ e ∈ D.inducedEdges U, (f (N.tail e) + f (N.head e)) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he
    have heq := N.regionShore_off_edge D U q he
    simp only [f,A,heq]
    split_ifs
    · exact N.colorSign_add black hc e
    · rfl
  rw [hreduce] at hs
  rw [hs]
  simp only [blackRim,rim,Nat.cast_sum,Nat.cast_add,Nat.cast_ite,Nat.cast_one,
    Nat.cast_zero,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  simp only [f,A,colorSign]
  by_cases ht : N.tail e ∈ N.regionShore D U q <;>
    by_cases hh : N.head e ∈ N.regionShore D U q <;>
    by_cases bt : black (N.tail e) <;> by_cases bh : black (N.head e) <;> norm_num [ht,hh,bt,bh]

omit [Fintype F] in
lemma sum_rim (U : Finset F) :
    ∑ q : N.Regions D U, N.rim D U q = 2 * (D.inducedEdges U).card := by
  simp only [rim]
  rw [Finset.sum_comm]
  simp [N.mem_regionShore,Finset.sum_add_distrib,Nat.mul_comm]

omit [Fintype F] in
lemma sum_regionBalance (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (U : Finset F) : ∑ q : N.Regions D U, N.regionBalance D black U q = 0 := by
  simp only [regionBalance,regionShore,Finset.sum_filter]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  exact N.colorSign_sum hN h3 black hc

lemma rim_defect (b d : ℕ) (β : ℤ) (hb : b ≤ d) (hd : 4 ≤ d)
    (hβ : 3*β = 2*(b:ℤ) - d) : β ≤ (d:ℤ)-4 := by
  by_cases h4 : d = 4
  · subst d; omega
  by_cases h5 : d = 5
  · subst d; omega
  have h6 : (6:ℤ) ≤ d := by omega
  have hbd : (b:ℤ) ≤ d := by exact_mod_cast hb
  omega

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

def ThreeEdgeConnected : Prop := ∀ A : Finset V, A.Nonempty → Aᶜ.Nonempty → 3 ≤ (N.cut A).card

def TrivialThreeCuts : Prop := ∀ A : Finset V, (N.cut A).card = 3 → A.card = 1 ∨ Aᶜ.card = 1

omit [Fintype F] in
lemma region_cut_subset (U : Finset F) (q : N.Regions D U) :
    N.cut (N.regionShore D U q) ⊆ D.inducedEdges U := by
  intro e he
  by_contra hn
  have hh := N.regionShore_off_edge D U q hn
  have hc := (N.mem_cut _ _).mp he
  exact hc.elim (fun h => h.2 (hh.mp h.1)) (fun h => h.2 (hh.mpr h.1))

omit [Fintype F] in
lemma rim_cut_count (U : Finset F) (q : N.Regions D U) :
    N.rim D U q = (N.cut (N.regionShore D U q)).card +
      2 * ((D.inducedEdges U).filter fun e =>
        N.tail e ∈ N.regionShore D U q ∧ N.head e ∈ N.regionShore D U q).card := by
  have hcut : N.cut (N.regionShore D U q) =
      (D.inducedEdges U).filter fun e => e ∈ N.cut (N.regionShore D U q) := by
    ext e
    simp only [Finset.mem_filter]
    exact ⟨fun he => ⟨N.region_cut_subset D U q he,he⟩,And.right⟩
  rw [hcut]
  simp only [rim,Finset.card_filter,Finset.mul_sum,← Finset.sum_add_distrib,N.mem_cut]
  apply Finset.sum_congr rfl
  intro e _
  by_cases ht : N.tail e ∈ N.regionShore D U q <;>
    by_cases hh : N.head e ∈ N.regionShore D U q <;> simp [ht,hh]

omit [Fintype F] in
lemma cut_le_rim (U : Finset F) (q : N.Regions D U) :
    (N.cut (N.regionShore D U q)).card ≤ N.rim D U q := by
  rw [N.rim_cut_count]
  omega

omit [Fintype F] in
lemma rim_of_shore_univ (U : Finset F) (q : N.Regions D U)
    (hq : N.regionShore D U q = Finset.univ) :
    N.rim D U q = 2 * (D.inducedEdges U).card := by
  simp [rim,hq,Nat.mul_comm]

omit [Fintype F] in
lemma rim_ge_three (hN : N.ThreeEdgeConnected) (U : Finset F)
    (hm : 3 ≤ (D.inducedEdges U).card) (q : N.Regions D U) : 3 ≤ N.rim D U q := by
  by_cases hq : N.regionShore D U q = Finset.univ
  · rw [N.rim_of_shore_univ D U q hq]; omega
  · have hA := N.regionShore_nonempty D U q
    have hAc : (N.regionShore D U q)ᶜ.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro he
      exact hq ((Finset.compl_eq_empty_iff _).mp he)
    exact (hN _ hA hAc).trans (N.cut_le_rim D U q)

omit [Fintype F] in
lemma rim_three_cut (hN : N.ThreeEdgeConnected) (U : Finset F)
    (_hm : 3 ≤ (D.inducedEdges U).card) (q : N.Regions D U) (hq : N.rim D U q = 3) :
    (N.cut (N.regionShore D U q)).card = 3 := by
  have hproper : N.regionShore D U q ≠ Finset.univ := by
    intro he
    have hh := N.rim_of_shore_univ D U q he
    omega
  have hAc : (N.regionShore D U q)ᶜ.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    exact hproper ((Finset.compl_eq_empty_iff _).mp he)
  have hl := hN _ (N.regionShore_nonempty D U q) hAc
  have hu := N.cut_le_rim D U q
  omega

omit [Fintype F] in
lemma rim_three_no_internal (hN : N.ThreeEdgeConnected) (U : Finset F)
    (_hm : 3 ≤ (D.inducedEdges U).card) (q : N.Regions D U) (hq : N.rim D U q = 3)
    {e : E} (he : e ∈ D.inducedEdges U) :
    ¬(N.tail e ∈ N.regionShore D U q ∧ N.head e ∈ N.regionShore D U q) := by
  have hc := N.rim_three_cut D hN U _hm q hq
  have hh := N.rim_cut_count D U q
  have hz : ((D.inducedEdges U).filter fun e =>
      N.tail e ∈ N.regionShore D U q ∧ N.head e ∈ N.regionShore D U q) = ∅ :=
    Finset.card_eq_zero.mp (by omega)
  intro hi
  have hhmem : e ∈ (D.inducedEdges U).filter (fun e =>
      N.tail e ∈ N.regionShore D U q ∧ N.head e ∈ N.regionShore D U q) :=
    Finset.mem_filter.mpr ⟨he,hi⟩
  rw [hz] at hhmem
  exact Finset.notMem_empty _ hhmem

omit [Fintype F] in
lemma singleton_region_star (hN : N.Simple) (U : Finset F) (q : N.Regions D U)
    {v : V} (hq : N.regionShore D U q = {v}) : N.star v ⊆ D.inducedEdges U := by
  intro e he
  by_contra hn
  have hi := (N.mem_star e v).mp he
  have hh := N.regionShore_off_edge D U q hn
  rw [hq] at hh
  simp only [Finset.mem_singleton] at hh
  exact hN.loopless e (hi.elim (fun hv => hv.trans ((hh.mp hv).symm))
    (fun hv => (hh.mpr hv).trans hv.symm))

lemma star_subset_eq (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    {v w : V} (hvw : N.star v ⊆ N.star w) : v = w := by
  by_contra hne
  have hc : 1 < (N.star v).card := by rw [N.card_star hN,h3 v]; decide
  obtain ⟨e,he,f,hf,hef⟩ := Finset.one_lt_card.mp hc
  have ends {e : E} (he : e ∈ N.star v) : s(N.tail e,N.head e) = s(v,w) := by
    have hv := (N.mem_star e v).mp he
    have hw := (N.mem_star e w).mp (hvw he)
    apply Sym2.eq_iff.mpr
    rcases hv with hv | hv <;> rcases hw with hw | hw
    · exact (hne (hv.symm.trans hw)).elim
    · exact Or.inl ⟨hv,hw⟩
    · exact Or.inr ⟨hw,hv⟩
    · exact (hne (hv.symm.trans hw)).elim
  exact hef (hN.pair_injective ((ends he).trans (ends hf).symm))

omit [Fintype F] in
lemma complement_singleton_root (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (hcut : N.ThreeEdgeConnected) (U : Finset F) (root : V)
    (hr : N.star root ⊆ D.inducedEdges U) (q : N.Regions D U)
    (hq : N.rim D U q = 3) {v : V} (hv : (N.regionShore D U q)ᶜ = {v}) : v = root := by
  have hm : 3 ≤ (D.inducedEdges U).card := by
    have hh := Finset.card_le_card hr
    rwa [N.card_star hN,h3 root] at hh
  apply (N.star_subset_eq hN h3 (v := root) (w := v) ?_).symm
  intro e he
  have hn := N.rim_three_no_internal D hcut U hm q hq (hr he)
  rw [N.mem_star]
  have ht : N.tail e ∉ N.regionShore D U q ↔ N.tail e = v := by
    rw [← Finset.mem_compl,hv,Finset.mem_singleton]
  have hh : N.head e ∉ N.regionShore D U q ↔ N.head e = v := by
    rw [← Finset.mem_compl,hv,Finset.mem_singleton]
  rcases not_and_or.mp hn with ht' | hh'
  · exact Or.inl (ht.mp ht')
  · exact Or.inr (hh.mp hh')

end
end Barnette.Network

end OAI


namespace OAI

/-! Exact duality under finite network minors. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

def fullBlack (black : V → Prop) (U : Finset F) : Finset V :=
  Finset.univ.filter fun v => black v ∧ N.star v ⊆ D.inducedEdges U

def regionBlack (black : V → Prop) (U : Finset F) (q : N.Regions D U) : ℕ :=
  ((N.fullBlack D black U).filter fun v => v ∈ N.regionShore D U q).card

omit [Fintype F] in
lemma sum_regionBlack (black : V → Prop) (U : Finset F) :
    ∑ q : N.Regions D U, N.regionBlack D black U q = (N.fullBlack D black U).card := by
  simp only [regionBlack,Finset.card_filter,N.mem_regionShore]
  rw [Finset.sum_comm]
  simp

omit [Fintype F] in
lemma regionBalance_singleton (black : V → Prop) (U : Finset F) (q : N.Regions D U)
    {v : V} (hq : N.regionShore D U q = {v}) :
    N.regionBalance D black U q = colorSign black v := by
  simp [regionBalance,hq]

omit [Fintype F] in
lemma regionBalance_complement_singleton (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (U : Finset F) (q : N.Regions D U) {v : V} (hq : (N.regionShore D U q)ᶜ = {v}) :
    N.regionBalance D black U q = -colorSign black v := by
  have hh := Finset.sum_add_sum_compl (N.regionShore D U q) (colorSign black)
  rw [N.colorSign_sum hN h3 black hc,hq,Finset.sum_singleton] at hh
  change (∑ v ∈ N.regionShore D U q, colorSign black v) = _
  omega

omit [Fintype F] in
lemma singleton_regionBlack (hN : N.Simple) (black : V → Prop)
    (U : Finset F) (q : N.Regions D U) {v : V}
    (hq : N.regionShore D U q = {v}) (hv : black v) :
    1 ≤ N.regionBlack D black U q := by
  apply Finset.card_pos.mpr
  refine ⟨v,Finset.mem_filter.mpr ⟨?_,?_⟩⟩
  · simp only [fullBlack,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨hv,N.singleton_region_star D hN U q hq⟩
  · simp [hq]

omit [Fintype F] in

lemma region_density (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (hcut : N.ThreeEdgeConnected) (htr : N.TrivialThreeCuts)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (root : V) (hbroot : black root) (U : Finset F)
    (hr : N.star root ⊆ D.inducedEdges U) (q : N.Regions D U) :
    4 + N.regionBalance D black U q - 2*(N.regionBlack D black U q : ℤ) ≤ N.rim D U q := by
  have hm : 3 ≤ (D.inducedEdges U).card := by
    have hh := Finset.card_le_card hr
    rwa [N.card_star hN,h3 root] at hh
  have hd := N.rim_ge_three D hcut U hm q
  by_cases hd4 : 4 ≤ N.rim D U q
  · have hh := rim_defect (N.blackRim D black U q) (N.rim D U q)
      (N.regionBalance D black U q) (N.blackRim_le D black U q) hd4
      (N.region_balance_rim D hN h3 black hc U q)
    omega
  · have hd3 : N.rim D U q = 3 := by omega
    rcases htr _ (N.rim_three_cut D hcut U hm q hd3) with hsing | hsing
    · obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hsing
      have hβ := N.regionBalance_singleton D black U q hv
      by_cases hb : black v
      · have hB := N.singleton_regionBlack D hN black U q hv hb
        simp only [colorSign,hb,ite_true] at hβ
        omega
      · simp only [colorSign,hb,ite_false] at hβ
        omega
    · obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hsing
      have hvr := N.complement_singleton_root D hN h3 hcut U root hr q hd3 hv
      have hβ := N.regionBalance_complement_singleton D hN h3 black hc U q hv
      rw [hvr] at hβ
      simp only [colorSign,hbroot,ite_true] at hβ
      omega

theorem induced_density (h : N.Duality D) (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (hcut : N.ThreeEdgeConnected) (htr : N.TrivialThreeCuts)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (root : V) (hbroot : black root) (U : Finset F)
    (hr : N.star root ⊆ D.inducedEdges U) :
    ((D.inducedEdges U).card : ℤ) - (N.fullBlack D black U).card ≤ 2*(U.card : ℤ)-4 := by
  have hU : U.Nonempty := by
    have hstar : (N.star root).Nonempty := Finset.card_pos.mp (by rw [N.card_star hN,h3 root]; decide)
    obtain ⟨e,he⟩ := hstar
    exact ⟨D.tail e,((D.mem_inducedEdges U e).mp (hr he)).1⟩
  have heuler := N.induced_euler_bound D h U hU
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun q _ => N.region_density D hN h3 hcut htr black hc root hbroot U hr q)
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,← Finset.mul_sum,← Nat.cast_sum,
    N.sum_regionBalance D hN h3 black hc,N.sum_regionBlack,N.sum_rim] at hsum
  push_cast at hsum
  omega

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype V] [Fintype E] [Fintype F] in
lemma three_corner_count (p : Fin 3 → Prop) :
    ((min (2 : ℕ) ((Finset.univ.filter fun i => ¬p i).card) : ℕ) : ℤ) +
      (∑ i : Fin 3, if p i ∧ p (i+1) then (1 : ℤ) else 0) =
        2 + if ∀ i, p i then 1 else 0 := by
  have h11 : (1 : Fin 3) + 1 = 2 := by decide
  have h21 : (2 : Fin 3) + 1 = 0 := by decide
  by_cases h0 : p 0 <;> by_cases h1 : p 1 <;> by_cases h2 : p 2 <;>
    simp only [Finset.card_filter,Fin.sum_univ_succ,Fin.forall_fin_succ] <;>
    norm_num [h0,h1,h2,h11,h21]

omit [Fintype V] [Fintype F] in
lemma Triangle.edges_in_count {s : Finset E} (t : D.Triangle s) (U : Finset F) :
    ((s.filter fun e => e ∈ D.inducedEdges U).card : ℤ) =
      ∑ i : Fin 3, if t.corner i ∈ U ∧ t.corner (i+1) ∈ U then (1 : ℤ) else 0 := by
  conv_lhs => rw [← t.edge_range]
  rw [Finset.filter_image,Finset.card_image_of_injective _ t.edge_injective,
    Finset.card_filter,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he := t.edge_ends i
  have hh : t.edge i ∈ D.inducedEdges U ↔ t.corner i ∈ U ∧ t.corner (i+1) ∈ U := by
    rw [D.mem_inducedEdges]
    rcases Sym2.eq_iff.mp he with ⟨ht,hh⟩ | ⟨ht,hh⟩ <;> simp [ht,hh,and_comm]
  simp [hh]

omit [Fintype V] [Fintype F] in
lemma Triangle.all_corners {s : Finset E} (t : D.Triangle s) (U : Finset F) :
    s ⊆ D.inducedEdges U ↔ ∀ i, t.corner i ∈ U := by
  constructor
  · intro h i
    have hm : t.edge i ∈ s := by
      have hi : t.edge i ∈ Finset.univ.image t.edge := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
      simpa only [t.edge_range] using hi
    have he := (D.mem_inducedEdges U _).mp (h hm)
    rcases Sym2.eq_iff.mp (t.edge_ends i) with ⟨ht,hh⟩ | ⟨ht,hh⟩
    · exact ht ▸ he.1
    · exact hh ▸ he.2
  · intro h e he
    rw [← t.edge_range] at he
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
    apply (D.mem_inducedEdges U _).mpr
    rcases Sym2.eq_iff.mp (t.edge_ends i) with ⟨ht,hh⟩ | ⟨ht,hh⟩ <;> simp [ht,hh,h]

omit [Fintype F] in
lemma black_edge_partition (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (K : Finset E) :
    ∑ v ∈ Finset.univ.filter black, ((N.star v).filter fun e => e ∈ K).card = K.card := by
  have hstar : ∀ v, ((N.star v).filter fun e => e ∈ K) =
      K.filter fun e => N.Incident e v := by
    intro v; ext e; simp [star,and_comm]
  simp only [hstar,Finset.card_filter]
  rw [Finset.sum_comm]
  have he (e : E) : ∀ v, black v → (N.Incident e v ↔ N.blackEndpoint black e = v) := by
    intro v hv
    exact ⟨N.blackEndpoint_eq black hc hv,fun hh => hh ▸ (N.blackEndpoint_spec black hc e).2⟩
  conv_rhs => rw [Finset.card_eq_sum_ones]
  apply Finset.sum_congr rfl
  intro e _
  have hrewrite : ∀ v ∈ Finset.univ.filter black,
      (if N.Incident e v then 1 else 0 : ℕ) = if N.blackEndpoint black e = v then 1 else 0 := by
    intro v hv; rw [he e v ((Finset.mem_filter.mp hv).2)]
  rw [Finset.sum_congr rfl hrewrite]
  simp [(N.blackEndpoint_spec black hc e).1]

lemma black_dual_card (h : N.Duality D) (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) :
    Fintype.card F = (Finset.univ.filter black).card + 2 := by
  have hdeg : ∀ v, N.graph.degree v = 3 := h3
  have he := N.black_edge_partition black hc Finset.univ
  simp only [Finset.filter_true_of_mem (fun _ _ => Finset.mem_univ _),N.card_star hN,hdeg,
    Finset.sum_const,smul_eq_mul,Finset.card_univ] at he
  have hv := N.cubic_region_count hN h3 Finset.univ
  have hcut : N.cut Finset.univ = ∅ := by ext e; simp [cut]
  have hreg : N.regionEdges Finset.univ = Finset.univ := by ext e; simp [regionEdges]
  rw [hcut,hreg,Finset.card_empty,Finset.card_univ] at hv
  simp only [Finset.card_univ,add_zero] at hv
  have heu := h.euler N D
  omega

omit [Fintype F] in
lemma capacity_identity (face : ∀ v, D.Triangle (N.star v))
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (U : Finset F) :
    (∑ v ∈ Finset.univ.filter black,
      ((min (2 : ℕ) ((Finset.univ.filter fun i => (face v).corner i ∉ U).card) : ℕ) : ℤ)) +
        (D.inducedEdges U).card =
      2 * ((Finset.univ.filter black).card : ℤ) + (N.fullBlack D black U).card := by
  have he := N.black_edge_partition black hc (D.inducedEdges U)
  have hb : (∑ v ∈ Finset.univ.filter black,
      if N.star v ⊆ D.inducedEdges U then (1 : ℤ) else 0) = (N.fullBlack D black U).card := by
    simp only [fullBlack,Finset.card_filter,Nat.cast_sum,Finset.sum_filter,
      ite_and,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  calc
    _ = ∑ v ∈ Finset.univ.filter black,
        (((min (2 : ℕ) ((Finset.univ.filter fun i => (face v).corner i ∉ U).card) : ℕ) : ℤ) +
        ((N.star v).filter fun e => e ∈ D.inducedEdges U).card) := by
      simp only [Finset.sum_add_distrib,← Nat.cast_sum,he]
    _ = ∑ v ∈ Finset.univ.filter black,
        (2 + if N.star v ⊆ D.inducedEdges U then (1 : ℤ) else 0) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [(face v).edges_in_count D U]
      simp only [(face v).all_corners D U]
      convert three_corner_count (fun i => (face v).corner i ∈ U) using 1 <;> congr!
    _ = _ := by rw [Finset.sum_add_distrib,hb]; simp [mul_comm]

theorem capacity_full (h : N.Duality D) (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (hcut : N.ThreeEdgeConnected) (htr : N.TrivialThreeCuts)
    (face : ∀ v, D.Triangle (N.star v))
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (root : V) (hbroot : black root) (S : Finset F)
    (hr : ∀ i, (face root).corner i ∉ S) :
    2*S.card ≤ ∑ v ∈ Finset.univ.filter black,
      min 2 ((Finset.univ.filter fun i => (face v).corner i ∈ S).card) := by
  have hd := N.induced_density D h hN h3 hcut htr black hc root hbroot Sᶜ
    ((face root).all_corners D Sᶜ |>.mpr (by simpa using hr))
  have hi := N.capacity_identity D face black hc Sᶜ
  simp only [Finset.mem_compl,not_not] at hi
  have hu := Finset.card_add_card_compl S
  have hb := N.black_dual_card D h hN h3 black hc
  simp only [← Nat.cast_sum] at hi
  omega

end
end Barnette.Network

end OAI


namespace OAI

/-! Integral flows, capacitated matchings, and incidence-state pairs. -/

namespace Barnette.BMatching
noncomputable section
open scoped Classical
variable {A B : Type*} [Fintype A] [Fintype B]

lemma count_sum {C D : Type*} [Fintype C] [Fintype D] (p : C ⊕ D → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = (Finset.univ.filter fun c => p (.inl c)).card +
      (Finset.univ.filter fun d => p (.inr d)).card := by
  simp only [Finset.card_filter,Fintype.sum_sum_type]

lemma count_prod {C D : Type*} [Fintype C] [Fintype D] (p : C × D → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = ∑ c, (Finset.univ.filter fun d => p (c,d)).card := by
  simp only [Finset.card_filter,Fintype.sum_prod_type]

abbrev Inc (R : A → B → Prop) := {z : A × B // R z.1 z.2}
abbrev Left (R : A → B → Prop) := (A × Fin 2) ⊕ Inc R
abbrev Right (R : A → B → Prop) := (B × Fin 2) ⊕ Inc R

def gadget (R : A → B → Prop) : Left R → Right R → Prop
  | .inl (a,_), .inr e => e.val.1 = a
  | .inr e, .inl (b,_) => e.val.2 = b
  | .inr e, .inr f => e = f
  | _, _ => False

lemma incidence_fiber (R : A → B → Prop) (S : Finset A) (b : B) :
    ((Finset.univ.filter fun e : Inc R => e.val.1 ∈ S).filter
      fun e => e.val.2 = b).card = (S.filter fun a => R a b).card := by
  apply Finset.card_bij (fun e _ => e.val.1)
  · intro e he
    obtain ⟨he,hb⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).2,hb ▸ e.property⟩
  · intro e he f hf hh
    apply Subtype.ext
    exact Prod.ext hh ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm)
  · intro a ha
    obtain ⟨ha,hab⟩ := Finset.mem_filter.mp ha
    exact ⟨⟨(a,b),hab⟩,by simp [ha],rfl⟩

lemma gadget_hall (R : A → B → Prop)
    (hcap : ∀ S : Finset A, 2*S.card ≤ ∑ b, min 2 ((S.filter fun a => R a b).card))
    (L : Finset (Left R)) :
    L.card ≤ (Finset.univ.filter fun r : Right R => ∃ l ∈ L, gadget R l r).card := by
  let S := Finset.univ.filter fun a : A => ∃ k : Fin 2, Sum.inl (a,k) ∈ L
  let T := Finset.univ.filter fun e : Inc R => Sum.inr e ∈ L
  let I := Finset.univ.filter fun e : Inc R => e.val.1 ∈ S
  let Y := Finset.univ.filter fun b : B => ∃ e ∈ T, e.val.2 = b
  have hLc : L.card ≤ 2*S.card + T.card := by
    have hL : L = Finset.univ.filter (fun l => l ∈ L) := by ext; simp
    conv_lhs => rw [hL,count_sum (fun l : Left R => l ∈ L),count_prod]
    change (∑ a, (Finset.univ.filter fun k : Fin 2 => Sum.inl (a,k) ∈ L).card) +
      T.card ≤ _
    apply Nat.add_le_add_right
    calc
      _ ≤ ∑ a, if a ∈ S then 2 else 0 := by
        apply Finset.sum_le_sum
        intro a _
        by_cases ha : a ∈ S
        · simp only [ha,ite_true]
          exact le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (by simp)
        · have hn : ∀ k : Fin 2, Sum.inl (a,k) ∉ L := by simpa [S] using ha
          simp [ha,hn]
      _ = 2*S.card := by simp [mul_comm]
  have hY (b : B) (k : Fin 2) :
      (∃ l ∈ L, gadget R l (.inl (b,k))) ↔ b ∈ Y := by
    constructor
    · rintro ⟨l,hl,hg⟩
      cases l with
      | inl a => exact hg.elim
      | inr e => exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,e,by simp [T,hl],hg⟩
    · intro hb
      obtain ⟨e,he,hb⟩ := (Finset.mem_filter.mp hb).2
      exact ⟨.inr e,(Finset.mem_filter.mp he).2,hb⟩
  have hI (e : Inc R) : (∃ l ∈ L, gadget R l (.inr e)) ↔ e ∈ I ∪ T := by
    constructor
    · rintro ⟨l,hl,hg⟩
      cases l with
      | inl a =>
        apply Finset.mem_union_left
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.2,?_⟩⟩
        change e.val.1 = a.1 at hg
        simpa only [hg] using hl
      | inr f =>
        change f = e at hg
        exact Finset.mem_union_right _ (by simpa [T,← hg] using hl)
    · intro he
      rcases Finset.mem_union.mp he with he | he
      · obtain ⟨k,hk⟩ := (Finset.mem_filter.mp ((Finset.mem_filter.mp he).2)).2
        exact ⟨.inl (e.val.1,k),hk,rfl⟩
      · exact ⟨.inr e,(Finset.mem_filter.mp he).2,rfl⟩
  have hNc : (Finset.univ.filter fun r : Right R => ∃ l ∈ L, gadget R l r).card =
      2*Y.card + (I ∪ T).card := by
    rw [count_sum (fun r : Right R => ∃ l ∈ L, gadget R l r),count_prod]
    simp only [hY,hI]
    have hconst (b : B) : (Finset.univ.filter fun _ : Fin 2 => b ∈ Y).card =
        if b ∈ Y then 2 else 0 := by by_cases hb : b ∈ Y <;> simp [hb]
    have hfilter : (Finset.univ.filter fun e : Inc R => e ∈ I ∪ T) = I ∪ T := by ext; simp
    rw [hfilter]
    simp only [hconst]
    simp [mul_comm]
  have hcap' : 2*S.card ≤ 2*Y.card + (I \ T).card := by
    have hsum : ∑ b, min 2 ((S.filter fun a => R a b).card) ≤
        (∑ b, if b ∈ Y then 2 else 0) + ∑ b, ((I \ T).filter fun e => e.val.2 = b).card := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : b ∈ Y
      · simp only [hb,ite_true]
        exact le_trans (Nat.min_le_left _ _) (Nat.le_add_right _ _)
      · have hIT : (I \ T).filter (fun e => e.val.2 = b) = I.filter (fun e => e.val.2 = b) := by
          ext e
          simp only [Finset.mem_filter,Finset.mem_sdiff]
          constructor
          · exact fun ⟨⟨hi,_⟩,he⟩ => ⟨hi,he⟩
          · rintro ⟨hi,he⟩
            refine ⟨⟨hi,fun ht => hb (Finset.mem_filter.mpr ⟨Finset.mem_univ _,e,ht,he⟩)⟩,he⟩
        rw [hIT]
        dsimp only [I]
        rw [incidence_fiber]
        simp only [hb,ite_false,zero_add]
        exact Nat.min_le_right _ _
    have hcount : ∑ b, ((I \ T).filter fun e => e.val.2 = b).card = (I \ T).card := by
      simpa using Finset.sum_card_fiberwise_eq_card_filter (I \ T) Finset.univ (fun e => e.val.2)
    rw [hcount] at hsum
    have hycount : (∑ b, if b ∈ Y then 2 else 0 : ℕ) = 2*Y.card := by
      simp [mul_comm]
    rw [hycount] at hsum
    exact (hcap S).trans hsum
  rw [hNc,← Finset.card_sdiff_add_card]
  omega

theorem gadget_matching (R : A → B → Prop) (hcard : Fintype.card A = Fintype.card B)
    (hcap : ∀ S : Finset A, 2*S.card ≤ ∑ b, min 2 ((S.filter fun a => R a b).card)) :
    ∃ f : Left R ≃ Right R, ∀ l, gadget R l (f l) := by
  obtain ⟨f,hfi,hf⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective (gadget R)).mp
    (gadget_hall R hcap)
  have hb : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfi,by
    simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,hcard]⟩
  exact ⟨Equiv.ofBijective f hb,hf⟩

end
end Barnette.BMatching
namespace Barnette.BMatching
noncomputable section
open scoped Classical
variable {A B : Type*} [Fintype A] [Fintype B]

structure FactorData (R : A → B → Prop) where
  left : A × Fin 2 ↪ Inc R
  right : B × Fin 2 ↪ Inc R
  left_coord : ∀ a k, (left (a,k)).val.1 = a
  right_coord : ∀ b k, (right (b,k)).val.2 = b
  same_range : Set.range left = Set.range right

omit [Fintype A] [Fintype B] in
lemma data_of_gadget (R : A → B → Prop) (f : Left R ≃ Right R)
    (hf : ∀ l, gadget R l (f l)) : Nonempty (FactorData R) := by
  have hleft : ∀ ak : A × Fin 2, ∃ e : Inc R, f (.inl ak) = .inr e ∧ e.val.1 = ak.1 := by
    intro ak
    have h := hf (.inl ak)
    cases he : f (.inl ak) with
    | inl bk => rw [he] at h; exact h.elim
    | inr e => rw [he] at h; exact ⟨e,rfl,h⟩
  have hright : ∀ bk : B × Fin 2, ∃ e : Inc R, f (.inr e) = .inl bk ∧ e.val.2 = bk.1 := by
    intro bk
    obtain ⟨l,hl⟩ := f.surjective (.inl bk)
    have h := hf l
    rw [hl] at h
    cases l with
    | inl ak => exact h.elim
    | inr e => exact ⟨e,hl,h⟩
  choose l hl hlc using hleft
  choose r hr hrc using hright
  have hli : Function.Injective l := by
    intro a b h
    exact Sum.inl.inj (f.injective ((hl a).trans ((congrArg Sum.inr h).trans (hl b).symm)))
  have hri : Function.Injective r := by
    intro a b h
    exact Sum.inl.inj ((hr a).symm.trans ((congrArg (fun e => f (.inr e)) h).trans (hr b)))
  refine ⟨⟨⟨l,hli⟩,⟨r,hri⟩,fun a k => hlc (a,k),fun b k => hrc (b,k),?_⟩⟩
  ext e
  constructor
  · rintro ⟨ak,rfl⟩
    have h := hf (.inr (l ak))
    cases he : f (.inr (l ak)) with
    | inl bk =>
      exact ⟨bk,Sum.inr.inj (f.injective ((hr bk).trans he.symm))⟩
    | inr d =>
      rw [he] at h
      change l ak = d at h
      have hh : Sum.inl ak = Sum.inr (l ak) := f.injective ((hl ak).trans (by simpa [h] using he.symm))
      cases hh
  · rintro ⟨bk,rfl⟩
    obtain ⟨z,hz⟩ := f.surjective (.inr (r bk))
    have h := hf z
    rw [hz] at h
    cases z with
    | inl ak => exact ⟨ak,Sum.inr.inj ((hl ak).symm.trans hz)⟩
    | inr e =>
      change e = r bk at h
      subst e
      have hh := (hr bk).symm.trans hz
      cases hh

lemma two_image_count {C : Type*} [Fintype C] (f : Fin 2 → C) (hf : Function.Injective f) :
    (Finset.univ.filter fun c => ∃ k, f k = c).card = 2 := by
  have hs : (Finset.univ.filter fun c => ∃ k, f k = c) = Finset.univ.image f := by ext; simp
  rw [hs,Finset.card_image_of_injective _ hf]
  simp

lemma data_two_factor (R : A → B → Prop) (M : FactorData R) :
    ∃ Q : A → B → Prop, (∀ a b, Q a b → R a b) ∧
      (∀ a, (Finset.univ.filter (Q a)).card = 2) ∧
      (∀ b, (Finset.univ.filter fun a => Q a b).card = 2) := by
  classical
  let Q : A → B → Prop := fun a b => ∃ k, (M.left (a,k)).val.2 = b
  have hQright (a : A) (b : B) : Q a b ↔ ∃ k, (M.right (b,k)).val.1 = a := by
    constructor
    · rintro ⟨k,hk⟩
      have he : M.left (a,k) ∈ Set.range M.right := M.same_range ▸ Set.mem_range_self _
      obtain ⟨⟨c,j⟩,he⟩ := he
      have hc : c = b := (M.right_coord c j).symm.trans ((congrArg (fun e : Inc R => e.val.2) he).trans hk)
      subst c
      exact ⟨j,(congrArg (fun e : Inc R => e.val.1) he).trans (M.left_coord a k)⟩
    · rintro ⟨k,hk⟩
      have he : M.right (b,k) ∈ Set.range M.left := M.same_range.symm ▸ Set.mem_range_self _
      obtain ⟨⟨c,j⟩,he⟩ := he
      have hc : c = a := (M.left_coord c j).symm.trans ((congrArg (fun e : Inc R => e.val.1) he).trans hk)
      subst c
      exact ⟨j,(congrArg (fun e : Inc R => e.val.2) he).trans (M.right_coord b k)⟩
  refine ⟨Q,?_,?_,?_⟩
  · rintro a b ⟨k,rfl⟩
    have h := (M.left (a,k)).property
    rwa [M.left_coord] at h
  · intro a
    have hi : Function.Injective (fun k => (M.left (a,k)).val.2) := by
      intro i j hij
      have he : M.left (a,i) = M.left (a,j) := Subtype.ext (Prod.ext (by simp [M.left_coord]) hij)
      exact Prod.mk.inj (M.left.injective he) |>.2
    simpa only [Q] using two_image_count (fun k => (M.left (a,k)).val.2) hi
  · intro b
    simp only [hQright]
    apply two_image_count
    intro i j hij
    have he : M.right (b,i) = M.right (b,j) := Subtype.ext (Prod.ext hij (by simp [M.right_coord]))
    exact Prod.mk.inj (M.right.injective he) |>.2

lemma regular_hall (Q : A → B → Prop) (n : ℕ) (hn : 0 < n)
    (hrow : ∀ a, (Finset.univ.filter (Q a)).card = n)
    (hcol : ∀ b, (Finset.univ.filter fun a => Q a b).card = n)
    (S : Finset A) :
    S.card ≤ (Finset.univ.filter fun b => ∃ a ∈ S, Q a b).card := by
  let T := Finset.univ.filter fun b => ∃ a ∈ S, Q a b
  have hc : n*S.card = ∑ b, (S.filter fun a => Q a b).card := by
    calc
      _ = ∑ a ∈ S, (Finset.univ.filter (Q a)).card := by simp [hrow,mul_comm]
      _ = _ := by simp only [Finset.card_filter]; rw [Finset.sum_comm]
  have hl : ∑ b, (S.filter fun a => Q a b).card ≤ ∑ b, if b ∈ T then n else 0 := by
    apply Finset.sum_le_sum
    intro b _
    by_cases hb : b ∈ T
    · simp only [hb,ite_true]
      rw [← hcol b]
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
    · have hnone : ∀ a ∈ S, ¬Q a b := by simpa [T] using hb
      simp [hb,Finset.filter_false_of_mem hnone]
  have hr : (∑ b, if b ∈ T then n else 0) = n*T.card := by simp [mul_comm]
  rw [hr,← hc] at hl
  exact Nat.le_of_mul_le_mul_left hl hn

lemma regular_matching (Q : A → B → Prop) (hcard : Fintype.card A = Fintype.card B)
    (n : ℕ) (hn : 0 < n)
    (hrow : ∀ a, (Finset.univ.filter (Q a)).card = n)
    (hcol : ∀ b, (Finset.univ.filter fun a => Q a b).card = n) :
    ∃ f : A ≃ B, ∀ a, Q a (f a) := by
  obtain ⟨f,hfi,hf⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective Q).mp
    (regular_hall Q n hn hrow hcol)
  exact ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hfi,hcard⟩),hf⟩

theorem two_matchings (R : A → B → Prop) (hcard : Fintype.card A = Fintype.card B)
    (hcap : ∀ S : Finset A, 2*S.card ≤ ∑ b, min 2 ((S.filter fun a => R a b).card)) :
    ∃ f g : A ≃ B, (∀ a, R a (f a) ∧ R a (g a)) ∧ (∀ a, f a ≠ g a) := by
  classical
  obtain ⟨p,hp⟩ := gadget_matching R hcard hcap
  obtain ⟨M⟩ := data_of_gadget R p hp
  obtain ⟨Q,hQR,hrow,hcol⟩ := data_two_factor R M
  obtain ⟨f,hf⟩ := regular_matching Q hcard 2 (by decide) hrow hcol
  let Q' : A → B → Prop := fun a b => Q a b ∧ b ≠ f a
  have hr : ∀ a, (Finset.univ.filter (Q' a)).card = 1 := by
    intro a
    have he : Finset.univ.filter (Q' a) = (Finset.univ.filter (Q a)).erase (f a) := by
      ext b; simp [Q',and_comm]
    rw [he,Finset.card_erase_of_mem (by simp [hf a]),hrow]
  have hc : ∀ b, (Finset.univ.filter fun a => Q' a b).card = 1 := by
    intro b
    have he : (Finset.univ.filter fun a => Q' a b) =
        (Finset.univ.filter fun a => Q a b).erase (f.symm b) := by
      ext a
      simp only [Q',Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase]
      constructor
      · rintro ⟨hq,hne⟩
        exact ⟨fun he => hne (by rw [he,f.apply_symm_apply]),hq⟩
      · rintro ⟨hne,hq⟩
        exact ⟨hq,fun he => hne (f.injective (by simpa using he.symm))⟩
    rw [he,Finset.card_erase_of_mem (by simpa using hf (f.symm b)),hcol]
  obtain ⟨g,hg⟩ := regular_matching Q' hcard 1 (by decide) (by simpa only [Q'] using hr) (by simpa only [Q'] using hc)
  exact ⟨f,g,fun a => ⟨hQR _ _ (hf a),hQR _ _ (hg a).1⟩,fun a h => (hg a).2 h.symm⟩

end
end Barnette.BMatching
namespace Barnette.TriangleSystem.State
variable {A V : Type*} {T : TriangleSystem A V} {X : Set V}
lemma exists_value (r : A ≃ X) (hr : ∀ t, (r t : V) ∈ Set.range (T.vertex t)) :
    ∃ s : T.State X, ∀ t, s.value t = (r t : V) := by
  choose c hc using hr
  refine ⟨⟨c,?_,?_⟩,hc⟩
  · intro t u h
    exact r.injective (Subtype.ext (by simpa only [hc] using h))
  · ext v
    constructor
    · rintro ⟨t,rfl⟩
      change T.vertex t (c t) ∈ X
      rw [hc]; exact (r t).property
    · intro hv
      obtain ⟨t,ht⟩ := r.surjective ⟨v,hv⟩
      exact ⟨t,(hc t).trans (congrArg Subtype.val ht)⟩
end Barnette.TriangleSystem.State

namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D)

lemma nonroots_card (root : V) (hr : M.black root) :
    Fintype.card (M.nonroots root) = Fintype.card (M.Black root) := by
  have hf := N.black_dual_card D M.duality M.simple M.cubic M.black M.coloring
  have hc : Fintype.card (Set.range (M.face root).corner) = 3 := by
    rw [← Fintype.card_congr (Equiv.ofInjective _ (M.face root).corner_injective)]
    rfl
  have hn := Fintype.card_compl_set (Set.range (M.face root).corner)
  have hb : Fintype.card (M.Black root) = (Finset.univ.filter M.black).card - 1 := by
    rw [Fintype.card_subtype]
    have he : (Finset.univ.filter fun v => M.black v ∧ v ≠ root) =
        (Finset.univ.filter M.black).erase root := by ext; simp [and_comm]
    rw [he,Finset.card_erase_of_mem (by simp [hr])]
  have hnx : Fintype.card (M.nonroots root) =
      Fintype.card F - Fintype.card (Set.range (M.face root).corner) := by
    convert hn using 1
    congr!
  rw [hnx,hc,hb,hf]
  omega

omit [Fintype F] in
lemma corner_filter_card (root : V) (S : Finset (M.nonroots root)) (t : M.Black root) :
    (S.filter fun x => x.val ∈ Set.range (M.face t.val).corner).card =
      (Finset.univ.filter fun i => (M.face t.val).corner i ∈ S.image Subtype.val).card := by
  have he : (S.filter fun x => x.val ∈ Set.range (M.face t.val).corner).image Subtype.val =
      (Finset.univ.filter fun i => (M.face t.val).corner i ∈ S.image Subtype.val).image
        (M.face t.val).corner := by
    ext z
    simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,Set.mem_range]
    constructor
    · rintro ⟨x,⟨hx,i,hi⟩,rfl⟩
      exact ⟨i,⟨x,hx,hi.symm⟩,hi⟩
    · rintro ⟨i,⟨x,hx,hxi⟩,hi⟩
      exact ⟨x,⟨hx,i,hxi.symm⟩,hxi.trans hi⟩
  have hh := congrArg Finset.card he
  rwa [Finset.card_image_of_injective _ Subtype.val_injective,
    Finset.card_image_of_injective _ (M.face t.val).corner_injective] at hh

lemma state_capacity (hcut : N.ThreeEdgeConnected) (htr : N.TrivialThreeCuts)
    (root : V) (hr : M.black root) (S : Finset (M.nonroots root)) :
    2*S.card ≤ ∑ t : M.Black root,
      min 2 ((S.filter fun x => x.val ∈ Set.range (M.face t.val).corner).card) := by
  let U := S.image Subtype.val
  have hu : ∀ i, (M.face root).corner i ∉ U := by
    intro i hi
    obtain ⟨x,_,hx⟩ := Finset.mem_image.mp hi
    exact x.property ⟨i,hx.symm⟩
  have hcap := N.capacity_full D M.duality M.simple M.cubic hcut htr M.face M.black
    M.coloring root hr U hu
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hcap
  have hz : min 2 ((Finset.univ.filter fun i => (M.face root).corner i ∈ U).card) = 0 := by
    have hh : (Finset.univ.filter fun i => (M.face root).corner i ∈ U) = ∅ := by
      ext i; simp [hu]
    rw [hh]; simp
  have he : (∑ v ∈ Finset.univ.filter M.black,
        min 2 ((Finset.univ.filter fun i => (M.face v).corner i ∈ U).card)) =
      ∑ t : M.Black root, min 2 ((Finset.univ.filter fun i => (M.face t.val).corner i ∈ U).card) := by
    rw [← Finset.sum_erase_add _ _ (show root ∈ Finset.univ.filter M.black by simp [hr]),hz,add_zero]
    apply Finset.sum_subtype
    intro v; simp [and_comm]
  rw [he] at hcap
  simpa only [M.corner_filter_card root S] using hcap

theorem pair_nonempty (hcut : N.ThreeEdgeConnected) (htr : N.TrivialThreeCuts)
    (root : V) (hr : M.black root) : Nonempty ((M.system root).Pair (M.nonroots root)) := by
  obtain ⟨f,g,hfg,hne⟩ := Barnette.BMatching.two_matchings
    (fun (x : M.nonroots root) (t : M.Black root) => x.val ∈ Set.range (M.face t.val).corner)
    (M.nonroots_card root hr) (by
      intro S
      convert M.state_capacity hcut htr root hr S using 1; congr!)
  have hf : ∀ t : M.Black root, (f.symm t : F) ∈ Set.range ((M.system root).vertex t) := by
    intro t
    have h := (hfg (f.symm t)).1
    rw [f.apply_symm_apply] at h
    exact h
  have hg : ∀ t : M.Black root, (g.symm t : F) ∈ Set.range ((M.system root).vertex t) := by
    intro t
    have h := (hfg (g.symm t)).2
    rw [g.apply_symm_apply] at h
    exact h
  obtain ⟨r,hrv⟩ := Barnette.TriangleSystem.State.exists_value f.symm hf
  obtain ⟨s,hsv⟩ := Barnette.TriangleSystem.State.exists_value g.symm hg
  refine ⟨⟨(r,s),?_⟩⟩
  intro t he
  rw [hrv,hsv] at he
  have hh : f.symm t = g.symm t := Subtype.ext he
  apply hne (f.symm t)
  rw [f.apply_symm_apply,hh,g.apply_symm_apply]

end
end Barnette.Network.ColoredDual

end OAI


namespace OAI

/-! Disk and spoke signs and matching complements. -/

namespace Barnette.CycleCoordinates
variable {V : Type*} {G : SimpleGraph V} (C : Barnette.CycleCoordinates G)
include C in
lemma not_acyclic : ¬ G.IsAcyclic := by
  intro ha
  apply (SimpleGraph.isAcyclic_iff_free_cycleGraph.mp ha) (C.n+3) (by omega)
  refine ⟨⟨⟨C.vertex,?_⟩,C.vertex.injective⟩⟩
  intro i j hij
  rcases SimpleGraph.cycleGraph_adj.mp hij with hij | hij
  · have hi : i = j+1 := (sub_eq_iff_eq_add.mp hij).trans (add_comm _ _)
    rw [hi]; exact (C.adjacent j).symm
  · have hj : j = i+1 := (sub_eq_iff_eq_add.mp hij).trans (add_comm _ _)
    rw [hj]; exact C.adjacent i
end Barnette.CycleCoordinates

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

lemma acyclic_conserved_zero (hN : N.Simple) (ha : N.graph.IsAcyclic)
    (x : E → ℝ) (hx : N.boundary x = 0) : x = 0 := by
  ext e
  let K := N.graph.deleteEdges {s(N.tail e,N.head e)}
  have he : N.graph.Adj (N.tail e) (N.head e) := ⟨hN.loopless e,e,Or.inl ⟨rfl,rfl⟩⟩
  have hb : ¬K.Reachable (N.tail e) (N.head e) :=
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp ha he)
  let f : V → ℝ := fun v => if K.Reachable (N.tail e) v then 1 else 0
  have hg : N.gradient f e = -1 := by simp [gradient_apply,f,hb]
  have hk : ∀ k, k ≠ e → N.gradient f k = 0 := by
    intro k hke
    have hp : s(N.tail k,N.head k) ≠ s(N.tail e,N.head e) :=
      fun h => hke (hN.pair_injective h)
    have hadj : K.Adj (N.tail k) (N.head k) := by
      apply SimpleGraph.deleteEdges_adj.mpr
      exact ⟨⟨hN.loopless k,k,Or.inl ⟨rfl,rfl⟩⟩,by simpa only [Set.mem_singleton_iff] using hp⟩
    have hh : K.Reachable (N.tail e) (N.head k) ↔ K.Reachable (N.tail e) (N.tail k) :=
      ⟨fun h => h.trans hadj.reachable.symm,fun h => h.trans hadj.reachable⟩
    simp [gradient_apply,f,hh]
  have hi := N.boundary_adjoint x f
  rw [hx] at hi
  simp only [Pi.zero_apply,zero_mul,Finset.sum_const_zero] at hi
  rw [Finset.sum_eq_single e] at hi
  · simpa [hg] using hi.symm
  · intro k _ hke; rw [hk k hke,mul_zero]
  · simp

omit [Fintype V] [Fintype E] in
lemma Simple.restrict (hN : N.Simple) {K : Type*} (j : K → E) (hj : Function.Injective j) :
    (N.restrict j).Simple where
  loopless k := hN.loopless (j k)
  pair_injective _ _ h := hj (hN.pair_injective h)

omit [Fintype E] in
lemma extend_restriction (S : Finset E) (x : E → ℝ) (hx : ∀ e, e ∉ S → x e = 0) :
    push (Subtype.val : S → E) (fun e => x e.val) = x := by
  ext e
  by_cases he : e ∈ S
  · exact push_subtype_apply S (fun e => x e.val) ⟨e,he⟩
  · rw [push_subtype_outside S _ he,hx e he]

lemma conserved_supported_acyclic (hN : N.Simple) (S : Finset E)
    (ha : (N.restrict (Subtype.val : S → E)).graph.IsAcyclic)
    (x : E → ℝ) (hx : N.boundary x = 0) (hs : ∀ e, e ∉ S → x e = 0) : x = 0 := by
  have hz : (N.restrict (Subtype.val : S → E)).boundary (fun e => x e.val) = 0 := by
    rw [boundary_restrict,extend_restriction S x hs,hx]
  have hh := (N.restrict (Subtype.val : S → E)).acyclic_conserved_zero
    (hN.restrict N _ Subtype.val_injective) ha _ hz
  rw [← extend_restriction S x hs,hh,map_zero]

variable {F : Type*} [Fintype F] (D : Network F E)
omit [Fintype V] in
lemma Duality.complement_connected (h : N.Duality D) (hD : D.Simple) (S : Finset E)
    (ha : (D.restrict (Subtype.val : S → E)).graph.IsAcyclic) :
    (N.restrict (Subtype.val : ↥(Sᶜ) → E)).graph.Connected := by
  have : Nonempty V := h.connected.nonempty
  apply (N.restrict (Subtype.val : ↥(Sᶜ) → E)).connected_of_kernel_constants
  intro f hf v w
  have hz : D.boundary (N.gradient f) = 0 := by
    rw [← LinearMap.mem_ker,h.dual_cycles_eq_cuts]
    exact ⟨f,rfl⟩
  have hs : ∀ e, e ∉ S → N.gradient f e = 0 := by
    intro e he
    exact congrFun hf ⟨e,Finset.mem_compl.mpr he⟩
  exact N.gradient_zero_reachable (D.conserved_supported_acyclic hD S ha _ hz hs) (h.connected v w)

end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V A : Type*} (Q : Network V A)

def addSink (r : Fin 2 → V) (z : V) : Network V (A ⊕ Fin 2) where
  tail := Sum.elim Q.tail r
  head := Sum.elim Q.head (fun _ => z)

lemma addSink_tail_injective (ht : Function.Injective Q.tail) (r : Fin 2 → V)
    (hr : Function.Injective r) (hd : ∀ a i, Q.tail a ≠ r i) (z : V) :
    Function.Injective (Q.addSink r z).tail := by
  rintro (a|i) (b|j) h
  · exact congrArg Sum.inl (ht h)
  · exact (hd a j h).elim
  · exact (hd b i h.symm).elim
  · exact congrArg Sum.inr (hr h)

lemma addSink_acyclic (ha : Q.graph.IsAcyclic) (ht : Function.Injective Q.tail)
    (r : Fin 2 → V) (hr : Function.Injective r) (hd : ∀ a i, Q.tail a ≠ r i)
    (z : V) (hz : z ∉ Set.range (Q.addSink r z).tail) : (Q.addSink r z).graph.IsAcyclic := by
  classical
  by_contra hnot
  obtain ⟨C⟩ := Barnette.cycleCoordinates_of_not_acyclic hnot
  let L := Q.addSink r z
  let edge : Fin (C.n+3) ↪ A ⊕ Fin 2 := ⟨L.cycleEdge C,L.cycleEdge_injective C⟩
  have hend (i) : L.tail (edge i) = C.vertex i ∨ L.tail (edge i) = C.vertex (i+1) := by
    rcases Sym2.eq_iff.mp (L.cycleEdge_ends C i) with h|h
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hor := C.tail_orientation edge L.tail (Q.addSink_tail_injective ht r hr hd z) hend
  have hrange (i) : C.vertex i ∈ Set.range L.tail := by
    rcases hor with hf|hb
    · exact ⟨edge i,hf i⟩
    · refine ⟨edge (i-1),?_⟩
      simpa using hb (i-1)
  have hbase (i) : ∃ a, edge i = Sum.inl a := by
    cases he : edge i with
    | inl a => exact ⟨a,rfl⟩
    | inr j =>
      have hh : L.head (edge i) = z := by rw [he]; rfl
      rcases Sym2.eq_iff.mp (L.cycleEdge_ends C i) with h|h
      · exact (hz (hh ▸ (h.2 ▸ hrange (i+1)))).elim
      · exact (hz (hh ▸ (h.2 ▸ hrange i))).elim
  have hc : Nonempty (Barnette.CycleCoordinates Q.graph) := by
    refine ⟨⟨C.n,C.vertex,?_⟩⟩
    intro i
    obtain ⟨a,hea⟩ := hbase i
    refine ⟨(C.adjacent i).1,a,?_⟩
    have he := L.cycleEdge_ends C i
    change s(L.tail (edge i),L.head (edge i)) = _ at he
    rw [hea] at he
    exact Sym2.eq_iff.mp he
  exact hc.elim (fun C' => C'.not_acyclic ha)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

lemma boundary_injective_of_tree_card (hc : N.graph.Connected)
    (he : Fintype.card E + 1 = Fintype.card V) : Function.Injective N.boundary := by
  have hh := N.dim_cycles hc
  have hz : Module.finrank ℝ N.boundary.ker = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)

lemma boundary_restrict_injective (hi : Function.Injective N.boundary)
    {K : Type*} [Fintype K] (j : K → E) (hj : Function.Injective j) :
    Function.Injective (N.restrict j).boundary := by
  intro x y h
  rw [boundary_restrict,boundary_restrict] at h
  have hh := congrArg (pull j) (hi h)
  simpa only [pull_push_injective hj] using hh

omit [Fintype V] [Fintype E] in
lemma boundary_supported_vertices {K : Type*} [Fintype K] (j : K → E)
    (U : Finset V) (hU : ∀ k, N.tail (j k) ∈ U ∧ N.head (j k) ∈ U)
    (x : K → ℝ) {v : V} (hv : v ∉ U) : (N.restrict j).boundary x v = 0 := by
  rw [boundary_apply]
  apply Finset.sum_eq_zero
  intro k _
  have ht : (N.restrict j).tail k ≠ v := fun hh => hv (hh ▸ (hU k).1)
  have hh : (N.restrict j).head k ≠ v := fun hh => hv (hh ▸ (hU k).2)
  simp [ht,hh]

lemma independent_edges_bound (hi : Function.Injective N.boundary)
    (S : Finset E) (U : Finset V) (hne : U.Nonempty)
    (hU : ∀ e ∈ S, N.tail e ∈ U ∧ N.head e ∈ U) : S.card + 1 ≤ U.card := by
  obtain ⟨v,hv⟩ := hne
  let H := N.restrict (Subtype.val : S → E)
  let L : (S → ℝ) →ₗ[ℝ] (U.erase v → ℝ) := (pull Subtype.val).comp H.boundary
  have hL : Function.Injective L := by
    intro x y hxy
    apply N.boundary_restrict_injective hi Subtype.val Subtype.val_injective
    have hrow : ∀ w, w ≠ v → H.boundary x w = H.boundary y w := by
      intro w hw
      by_cases hwU : w ∈ U
      · exact congrFun hxy ⟨w,Finset.mem_erase.mpr ⟨hw,hwU⟩⟩
      · rw [N.boundary_supported_vertices Subtype.val U (fun e => hU e.val e.property) x hwU,
          N.boundary_supported_vertices Subtype.val U (fun e => hU e.val e.property) y hwU]
    ext w
    by_cases hw : w = v
    · subst w
      have hsx := H.sum_boundary x
      have hsy := H.sum_boundary y
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ v)] at hsx hsy
      have hh : (∑ w ∈ Finset.univ.erase v, H.boundary x w) =
          ∑ w ∈ Finset.univ.erase v, H.boundary y w := by
        apply Finset.sum_congr rfl
        intro w hw; exact hrow w (Finset.mem_erase.mp hw).1
      linarith
    · exact hrow w hw
  have hc := LinearMap.finrank_le_finrank_of_injective hL
  simp only [Module.finrank_pi,Fintype.card_coe] at hc
  rw [Finset.card_erase_of_mem hv] at hc
  have hvp : 0 < U.card := Finset.card_pos.mpr ⟨v,hv⟩
  omega

end
end Barnette.Network
namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
open Barnette.TriangleSystem
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

abbrev QNet (P : (M.system root).Pair (M.nonroots root)) : Network F (M.Black root) where
  tail t := P.left.value t
  head t := (M.face t.val).corner (thirdIndex (P.left.val t) (P.right.val t))

omit [Fintype F] in
lemma pair_val_ne (P : (M.system root).Pair (M.nonroots root)) (t : M.Black root) :
    P.left.val t ≠ P.right.val t := fun h => P.partner t ((State.value_eq_iff _ _ _).mpr h)

omit [Fintype F] in
lemma q_graph (P : (M.system root).Pair (M.nonroots root)) :
    (M.QNet P).graph = (M.system root).oppositeGraph P.right := by
  ext v w
  rw [(M.system root).oppositeGraph_adj_iff P.partner]
  constructor
  · rintro ⟨_,t,h|h⟩
    · exact ⟨t,Or.inl ⟨h.1.symm,h.2.symm⟩⟩
    · exact ⟨t,Or.inr ⟨h.1.symm,h.2.symm⟩⟩
  · rintro ⟨t,h|h⟩
    all_goals have hn := (thirdIndex_distinct _ _ (M.pair_val_ne P t)).1
    · exact ⟨fun he => hn ((M.face t.val).corner_injective (h.2.symm.trans (he.symm.trans h.1))),
        t,Or.inl ⟨h.1.symm,h.2.symm⟩⟩
    · exact ⟨fun he => hn ((M.face t.val).corner_injective (h.2.symm.trans (he.trans h.1))),
        t,Or.inr ⟨h.1.symm,h.2.symm⟩⟩

def qLabel (P : (M.system root).Pair (M.nonroots root)) (t : M.Black root) : E :=
  (M.face t.val).side D (P.left.val t) (thirdIndex (P.left.val t) (P.right.val t))

omit [Fintype F] in
lemma qLabel_ends (P : (M.system root).Pair (M.nonroots root)) (t : M.Black root) :
    s(D.tail (M.qLabel P t),D.head (M.qLabel P t)) =
      s((M.QNet P).tail t,(M.QNet P).head t) :=
  (M.face t.val).side_ends D (thirdIndex_distinct _ _ (M.pair_val_ne P t)).1.symm

omit [Fintype F] in
lemma qLabel_black (P : (M.system root).Pair (M.nonroots root)) (t : M.Black root) :
    N.blackEndpoint M.black (M.qLabel P t) = t.val :=
  N.blackEndpoint_eq M.black M.coloring t.property.1
    ((N.mem_star _ _).mp ((M.face t.val).side_mem D _ _))

omit [Fintype F] in
lemma qLabel_inj (P : (M.system root).Pair (M.nonroots root)) :
    Function.Injective (M.qLabel P) := by
  intro t u h
  apply Subtype.ext
  exact (M.qLabel_black P t).symm.trans ((congrArg (N.blackEndpoint M.black) h).trans (M.qLabel_black P u))

def rootStart (i : Fin 3) (j : Fin 2) : Fin 3 := i + j.castLE (by decide)

lemma rootStart_inj (i : Fin 3) : Function.Injective (rootStart i) := by revert i; decide
lemma rootStart_ne (i : Fin 3) (j : Fin 2) : rootStart i j ≠ i+2 := by revert i j; decide

abbrev augQ (P : (M.system root).Pair (M.nonroots root)) (i : Fin 3) :
    Network F (M.Black root ⊕ Fin 2) :=
  (M.QNet P).addSink (fun j => (M.face root).corner (rootStart i j)) ((M.face root).corner (i+2))

omit [Fintype F] in
lemma augQ_acyclic (P : (M.system root).Pair (M.nonroots root))
    (ha : ((M.system root).oppositeGraph P.right).IsAcyclic) (i : Fin 3) :
    (M.augQ P i).graph.IsAcyclic := by
  apply (M.QNet P).addSink_acyclic (M.q_graph P ▸ ha) P.left.value_injective _
    ((M.face root).corner_injective.comp (rootStart_inj i))
  · intro t j h
    exact P.left.value_mem t ⟨rootStart i j,h.symm⟩
  · rintro ⟨t|j,h⟩
    · exact P.left.value_mem t ⟨i+2,h.symm⟩
    · exact rootStart_ne i j ((M.face root).corner_injective h)

def augLabel (P : (M.system root).Pair (M.nonroots root)) (i : Fin 3) :
    M.Black root ⊕ Fin 2 → E :=
  Sum.elim (M.qLabel P) (fun j => (M.face root).side D (rootStart i j) (i+2))

omit [Fintype F] in
lemma augLabel_ends (P : (M.system root).Pair (M.nonroots root)) (i : Fin 3)
    (t : M.Black root ⊕ Fin 2) :
    s(D.tail (M.augLabel P i t),D.head (M.augLabel P i t)) =
      s((M.augQ P i).tail t,(M.augQ P i).head t) := by
  cases t with
  | inl t => exact M.qLabel_ends P t
  | inr j => exact (M.face root).side_ends D (rootStart_ne i j)

omit [Fintype F] in
lemma augLabel_inj (P : (M.system root).Pair (M.nonroots root)) (hr : M.black root)
    (i : Fin 3) : Function.Injective (M.augLabel P i) := by
  have hb (j : Fin 2) : N.blackEndpoint M.black (M.augLabel P i (.inr j)) = root :=
    N.blackEndpoint_eq M.black M.coloring hr ((N.mem_star _ _).mp ((M.face root).side_mem D _ _))
  rintro (t|j) (u|k) he
  · exact congrArg Sum.inl (M.qLabel_inj P he)
  · have hh := congrArg (N.blackEndpoint M.black) he
    change N.blackEndpoint M.black (M.qLabel P t) = _ at hh
    rw [M.qLabel_black P t,hb] at hh
    exact (t.property.2 hh).elim
  · have hh := congrArg (N.blackEndpoint M.black) he
    change _ = N.blackEndpoint M.black (M.qLabel P u) at hh
    rw [hb,M.qLabel_black P u] at hh
    exact (u.property.2 hh.symm).elim
  · have hh := (M.augLabel_ends P i (.inr j)).symm.trans
      ((congrArg (fun e => s(D.tail e,D.head e)) he).trans (M.augLabel_ends P i (.inr k)))
    rcases Sym2.eq_iff.mp hh with h|h
    · exact congrArg Sum.inr (rootStart_inj i ((M.face root).corner_injective h.1))
    · exact (rootStart_ne i j ((M.face root).corner_injective h.1)).elim

def removed (P : (M.system root).Pair (M.nonroots root)) (i : Fin 3) : Finset E :=
  Finset.univ.image (M.augLabel P i)

omit [Fintype F] in
lemma removed_acyclic (P : (M.system root).Pair (M.nonroots root))
    (ha : ((M.system root).oppositeGraph P.right).IsAcyclic) (i : Fin 3) :
    (D.restrict (Subtype.val : M.removed P i → E)).graph.IsAcyclic := by
  apply SimpleGraph.IsAcyclic.anti ?_ (M.augQ_acyclic P ha i)
  rintro v w ⟨hv,e,he⟩
  obtain ⟨k,_,hk⟩ := Finset.mem_image.mp e.property
  refine ⟨hv,k,?_⟩
  apply Sym2.eq_iff.mp
  have hh : s(D.tail e.val,D.head e.val) = s(v,w) := Sym2.eq_iff.mpr he
  rw [← hk,M.augLabel_ends] at hh
  exact hh

lemma remainder_connected (P : (M.system root).Pair (M.nonroots root))
    (ha : ((M.system root).oppositeGraph P.right).IsAcyclic) (i : Fin 3) :
    (N.restrict (Subtype.val : ↥((M.removed P i)ᶜ) → E)).graph.Connected :=
  M.duality.complement_connected N D M.dual_simple _ (M.removed_acyclic P ha i)

omit [Fintype F] in
lemma removed_card (P : (M.system root).Pair (M.nonroots root)) (hr : M.black root) (i : Fin 3) :
    (M.removed P i).card = (Finset.univ.filter M.black).card + 1 := by
  rw [removed,Finset.card_image_of_injective _ (M.augLabel_inj P hr i),Finset.card_univ,Fintype.card_sum]
  have hb : Fintype.card (M.Black root) + 1 = (Finset.univ.filter M.black).card := by
    rw [Fintype.card_subtype]
    have he : (Finset.univ.filter fun v => M.black v ∧ v ≠ root) =
        (Finset.univ.filter M.black).erase root := by ext; simp [and_comm]
    rw [he,Finset.card_erase_add_one (by simp [hr])]
  change Fintype.card (M.Black root) + 2 = _
  omega
end
end Barnette.Network.ColoredDual
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} (D : Network V E)

lemma Triangle.edge_incident {S : Finset E} (t : D.Triangle S) (i j : Fin 3) :
    D.Incident (t.edge i) (t.corner j) ↔ j = i ∨ j = i+1 := by
  rw [D.incident_iff_mem_pair,t.edge_ends,Sym2.mem_iff]
  exact or_congr t.corner_injective.eq_iff t.corner_injective.eq_iff

lemma Triangle.other_root_sides {S : Finset E} (t : D.Triangle S) (i : Fin 3) {e : E}
    (he : e ∈ S) :
    (∃ j : Fin 2, t.side D (ColoredDual.rootStart i j) (i+2) = e) ↔ e ≠ t.edge i := by
  have he' := he
  rw [← t.edge_range] at he'
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp he'
  have hh : ∀ i k : Fin 3,
      (∃ j : Fin 2, (if i+2 = ColoredDual.rootStart i j+1 then ColoredDual.rootStart i j else i+2) = k) ↔ k ≠ i := by decide
  have hs (a b : Fin 3) : t.side D a b = t.edge (if b = a+1 then a else b) := by
    unfold Triangle.side; split_ifs <;> rfl
  simp only [hs, ne_eq, t.edge_injective.eq_iff]
  exact hh i k

lemma Triangle.opposite_characteristic {S : Finset E} (t : D.Triangle S)
    {a b : Fin 3} (hab : a ≠ b) {e : E} (he : e ∈ S) :
    e ≠ t.side D a (Barnette.TriangleSystem.thirdIndex a b) ↔ D.Incident e (t.corner b) := by
  have he' := he
  rw [← t.edge_range] at he'
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp he'
  rw [t.edge_incident]
  have hh : ∀ a b k : Fin 3, a ≠ b →
      (k ≠ (if Barnette.TriangleSystem.thirdIndex a b = a+1 then a else Barnette.TriangleSystem.thirdIndex a b) ↔
        b = k ∨ b = k+1) := by decide
  have hs (a b : Fin 3) : t.side D a b = t.edge (if b = a+1 then a else b) := by
    unfold Triangle.side; split_ifs <;> rfl
  simp only [hs, ne_eq, t.edge_injective.eq_iff]
  exact hh a b k hab

end
end Barnette.Network

namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
open Barnette.TriangleSystem
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

omit [Fintype F] in
lemma removed_at_black (P : (M.system root).Pair (M.nonroots root)) (hr : M.black root)
    (i : Fin 3) (v : V) (hv : M.black v) {e : E} (he : e ∈ N.star v) :
    (e ∈ M.removed P i ↔
      if h : v = root then e ≠ (M.face root).edge i else e = M.qLabel P ⟨v,hv,h⟩) := by
  have hb : N.blackEndpoint M.black e = v := N.blackEndpoint_eq M.black M.coloring hv ((N.mem_star _ _).mp he)
  by_cases hh : v = root
  · clear hb
    subst v
    simp only
    have hb : N.blackEndpoint M.black e = root := N.blackEndpoint_eq M.black M.coloring hr ((N.mem_star _ _).mp he)
    constructor
    · intro hmem
      obtain ⟨t|j,_,ht⟩ := Finset.mem_image.mp hmem
      · have hbr : (t : V) = root := (M.qLabel_black P t).symm.trans ((congrArg (N.blackEndpoint M.black) ht).trans hb)
        exact (t.property.2 hbr).elim
      · exact ((M.face root).other_root_sides D i he).mp ⟨j,ht⟩
    · intro hne
      obtain ⟨j,hj⟩ := ((M.face root).other_root_sides D i he).mpr hne
      exact Finset.mem_image.mpr ⟨Sum.inr j,Finset.mem_univ _,hj⟩
  · simp only [dite_eq_right hh]
    constructor
    · intro hmem
      obtain ⟨t|j,_,ht⟩ := Finset.mem_image.mp hmem
      · have htv : t.val = v := (M.qLabel_black P t).symm.trans ((congrArg (N.blackEndpoint M.black) ht).trans hb)
        have ht' : t = ⟨v,hv,hh⟩ := Subtype.ext htv
        change M.qLabel P t = e at ht
        rw [ht'] at ht
        exact ht.symm
      · have hbr : N.blackEndpoint M.black (M.augLabel P i (.inr j)) = root :=
          N.blackEndpoint_eq M.black M.coloring hr ((N.mem_star _ _).mp ((M.face root).side_mem D _ _))
        exact (hh (hb.symm.trans ((congrArg (N.blackEndpoint M.black) ht).symm.trans hbr))).elim
    · intro heq
      exact Finset.mem_image.mpr ⟨Sum.inl ⟨v,hv,hh⟩,Finset.mem_univ _,heq.symm⟩

omit [Fintype F] in
lemma remainder_black_degree (P : (M.system root).Pair (M.nonroots root)) (hr : M.black root)
    (i : Fin 3) (v : V) (hv : M.black v) :
    ((N.star v).filter fun e => e ∈ (M.removed P i)ᶜ).card = if v = root then 1 else 2 := by
  by_cases hh : v = root
  · subst v
    rw [ite_eq_left rfl]
    have he : (N.star root).filter (fun e => e ∈ (M.removed P i)ᶜ) = {(M.face root).edge i} := by
      ext e
      simp only [Finset.mem_filter,Finset.mem_compl,Finset.mem_singleton]
      constructor
      · rintro ⟨he,hn⟩
        have hm := M.removed_at_black P hr i root hr he
        simpa using (not_congr hm).mp hn
      · intro heq; subst e
        have hm : (M.face root).edge i ∈ N.star root := by
          have hx : (M.face root).edge i ∈ Finset.univ.image (M.face root).edge := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
          simpa only [(M.face root).edge_range] using hx
        exact ⟨hm,by rw [M.removed_at_black P hr i root hr hm]; simp⟩
    rw [he,Finset.card_singleton]
  · rw [ite_eq_right hh]
    have he : (N.star v).filter (fun e => e ∈ (M.removed P i)ᶜ) =
        (N.star v).erase (M.qLabel P ⟨v,hv,hh⟩) := by
      ext e
      simp only [Finset.mem_filter,Finset.mem_compl,Finset.mem_erase]
      constructor
      · rintro ⟨he,hn⟩
        have hm := M.removed_at_black P hr i v hv he
        simp only [dite_eq_right hh] at hm
        exact ⟨(not_congr hm).mp hn,he⟩
      · rintro ⟨hn,he⟩
        exact ⟨he,by rw [M.removed_at_black P hr i v hv he]; simpa [hh]⟩
    rw [he,Finset.card_erase_of_mem (show M.qLabel P ⟨v,hv,hh⟩ ∈ N.star v from (M.face v).side_mem D _ _),N.card_star M.simple,M.cubic v]

lemma cubic_cards : Fintype.card E = 3*(Finset.univ.filter M.black).card ∧
    Fintype.card V = 2*(Finset.univ.filter M.black).card := by
  have hdeg : ∀ v, N.graph.degree v = 3 := M.cubic
  have he := N.black_edge_partition M.black M.coloring Finset.univ
  simp only [Finset.filter_true_of_mem (fun _ _ => Finset.mem_univ _),N.card_star M.simple,
    hdeg,Finset.sum_const,smul_eq_mul,Finset.card_univ] at he
  have hf := N.black_dual_card D M.duality M.simple M.cubic M.black M.coloring
  have heu := M.duality.euler N D
  constructor <;> omega

lemma remainder_independent (P : (M.system root).Pair (M.nonroots root)) (hr : M.black root)
    (ha : ((M.system root).oppositeGraph P.right).IsAcyclic) (i : Fin 3) :
    Function.Injective (N.restrict (Subtype.val : ↥((M.removed P i)ᶜ) → E)).boundary := by
  apply boundary_injective_of_tree_card _ (M.remainder_connected P ha i)
  rw [Fintype.card_coe]
  have hc := Finset.card_add_card_compl (M.removed P i)
  rw [M.removed_card P hr i] at hc
  have hE := M.cubic_cards.1
  have hV := M.cubic_cards.2
  omega

omit [Fintype F] in
lemma remainder_incident (P : (M.system root).Pair (M.nonroots root)) (hr : M.black root)
    (i : Fin 3) (t : M.Black root) {e : E} (he : e ∈ N.star t.val)
    (hm : e ∈ (M.removed P i)ᶜ) : D.Incident e (P.right.value t) := by
  have hn := (not_congr (M.removed_at_black P hr i t.val t.property.1 he)).mp (Finset.mem_compl.mp hm)
  simp only [dite_eq_right t.property.2] at hn
  exact ((M.face t.val).opposite_characteristic D (M.pair_val_ne P t) he).mp hn

end
end Barnette.Network.ColoredDual

end OAI


namespace OAI

/-! From opposite forests to connected spanning matching complements. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] [Fintype E] in
lemma complement_coloring (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) :
    ∀ e, ¬black (N.tail e) ↔ ¬¬black (N.head e) := fun e => not_congr (hc e)

omit [Fintype V] [Fintype E] in
lemma colored_endpoints (black : V → Prop)
    (_hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (e : E) :
    s(N.tail e,N.head e) = s(N.blackEndpoint black e,N.blackEndpoint (fun v => ¬black v) e) := by
  by_cases hb : black (N.tail e)
  · simp [blackEndpoint,hb]
  · simp [blackEndpoint,hb,Sym2.eq_swap]

lemma black_fiber_count (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (H : Finset E) (T : Finset V) (hT : ∀ v ∈ T, black v) :
    (H.filter fun e => N.blackEndpoint black e ∈ T).card =
      ∑ v ∈ T, ((N.star v).filter fun e => e ∈ H).card := by
  rw [← N.black_edge_partition black hc]
  have hf (v : V) (hv : black v) :
      (N.star v).filter (fun e => e ∈ H.filter (fun e => N.blackEndpoint black e ∈ T)) =
        if v ∈ T then (N.star v).filter (fun e => e ∈ H) else ∅ := by
    ext e
    by_cases ht : v ∈ T
    · simp only [ite_eq_left ht,Finset.mem_filter]
      constructor
      · tauto
      · rintro ⟨he,hh⟩
        exact ⟨he,hh,(N.blackEndpoint_eq black hc hv ((N.mem_star _ _).mp he)) ▸ ht⟩
    · simp only [ite_eq_right ht,Finset.notMem_empty,Finset.mem_filter,iff_false]
      rintro ⟨he,_,hbe⟩
      exact ht ((N.blackEndpoint_eq black hc hv ((N.mem_star _ _).mp he)) ▸ hbe)
  rw [Finset.sum_congr rfl (fun v hv => congrArg Finset.card (hf v (Finset.mem_filter.mp hv).2))]
  simp only [apply_ite Finset.card,Finset.card_empty,Finset.sum_ite_mem]
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext v
  simp only [Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨And.right,fun hv => ⟨hT v hv,hv⟩⟩

lemma tree_matching (black : V → Prop)
    (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (H : Finset E) (hi : Function.Injective (N.restrict (Subtype.val : H → E)).boundary)
    (root : V) (_hr : black root)
    (hd : ∀ v, black v → ((N.star v).filter (fun e => e ∈ H)).card = if v = root then 1 else 2)
    (hbal : Fintype.card {v // black v} = Fintype.card {v // ¬black v}) :
    ∃ P : Finset E, P ⊆ H ∧ ∀ v, ((N.star v).filter fun e => e ∈ P).card = 1 := by
  let B := {v // black v}
  let W := {v // ¬black v}
  let R : B → W → Prop := fun b w => ∃ e ∈ H,
    N.blackEndpoint black e = b.val ∧ N.blackEndpoint (fun v => ¬black v) e = w.val
  have hhall (S : Finset B) : S.card ≤ (Finset.univ.filter fun w : W => ∃ b ∈ S, R b w).card := by
    let Y := Finset.univ.filter fun w : W => ∃ b ∈ S, R b w
    let T := S.image Subtype.val
    let Z := Y.image Subtype.val
    let J := H.filter fun e => N.blackEndpoint black e ∈ T
    have hTc : T.card = S.card := Finset.card_image_of_injective _ Subtype.val_injective
    have hZc : Z.card = Y.card := Finset.card_image_of_injective _ Subtype.val_injective
    have hT : ∀ v ∈ T, black v := by
      intro v hv; obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hv; exact b.property
    have hZ : ∀ v ∈ Z, ¬black v := by
      intro v hv; obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hv; exact w.property
    have hdis : Disjoint T Z := Finset.disjoint_left.mpr (fun v ht hz => hZ v hz (hT v ht))
    by_cases hS : S.Nonempty
    · have hJc : 2*T.card ≤ J.card + 1 := by
        have he := N.black_fiber_count black hc H T hT
        have hd' : ∀ v ∈ T, ((N.star v).filter fun e => e ∈ H).card = 2 - if v = root then 1 else 0 := by
          intro v hv; rw [hd v (hT v hv)]; split_ifs <;> rfl
        have hn (v : V) : (2 - if v = root then 1 else 0 : ℕ) + (if v = root then 1 else 0) = 2 := by split_ifs <;> rfl
        have hh : J.card + ∑ v ∈ T, (if v = root then 1 else 0 : ℕ) = 2*T.card := by
          rw [he,Finset.sum_congr rfl hd',← Finset.sum_add_distrib]
          simp only [hn,Finset.sum_const,smul_eq_mul,mul_comm]
        have hx : (∑ v ∈ T, (if v = root then 1 else 0 : ℕ)) ≤ 1 := by simp; split_ifs <;> omega
        omega
      let J' : Finset H := Finset.univ.filter fun e => e.val ∈ J
      have hJ' : J'.card = J.card := by
        apply Finset.card_bij (fun e _ => e.val)
        · intro e he; exact (Finset.mem_filter.mp he).2
        · intro _ _ _ _ hh; exact Subtype.ext hh
        · intro e he; exact ⟨⟨e,(Finset.mem_filter.mp he).1⟩,by simp [J',he],rfl⟩
      have hn : (T ∪ Z).Nonempty := by obtain ⟨b,hb⟩ := hS; exact ⟨b.val,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b,hb,rfl⟩)⟩
      have hsupp : ∀ e ∈ J', (N.restrict (Subtype.val : H → E)).tail e ∈ T ∪ Z ∧
          (N.restrict (Subtype.val : H → E)).head e ∈ T ∪ Z := by
        intro e he
        have hJ : e.val ∈ J := (Finset.mem_filter.mp he).2
        have hb : N.blackEndpoint black e.val ∈ T := (Finset.mem_filter.mp hJ).2
        obtain ⟨b,hbS,hbe⟩ := Finset.mem_image.mp hb
        let w : W := ⟨N.blackEndpoint (fun v => ¬black v) e.val,
          (N.blackEndpoint_spec (fun v => ¬black v) (N.complement_coloring black hc) e.val).1⟩
        have hw : w ∈ Y := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,b,hbS,e.val,e.property,hbe.symm,rfl⟩
        have hz : N.blackEndpoint (fun v => ¬black v) e.val ∈ Z := Finset.mem_image.mpr ⟨w,hw,rfl⟩
        rcases Sym2.eq_iff.mp (N.colored_endpoints black hc e.val) with hh|hh
        · exact ⟨Finset.mem_union_left _ (hh.1 ▸ hb),Finset.mem_union_right _ (hh.2 ▸ hz)⟩
        · exact ⟨Finset.mem_union_right _ (hh.1 ▸ hz),Finset.mem_union_left _ (hh.2 ▸ hb)⟩
      have hb := (N.restrict (Subtype.val : H → E)).independent_edges_bound hi J' (T ∪ Z) hn hsupp
      rw [hJ',Finset.card_union_of_disjoint hdis,hTc,hZc] at hb
      rw [hTc] at hJc
      change S.card ≤ Y.card
      omega
    · have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      simp [hz]
  obtain ⟨f,hfi,hf⟩ := (Fintype.all_card_le_filter_rel_iff_exists_injective R).mp hhall
  have hfs : Function.Surjective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfi,hbal⟩ |>.2
  choose p hp hb hw using hf
  let P := Finset.univ.image p
  have hpP (b : B) : p b ∈ P := Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩
  have hsub : P ⊆ H := by intro e he; obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp he; exact hp b
  refine ⟨P,hsub,?_⟩
  intro v
  by_cases hv : black v
  · let b : B := ⟨v,hv⟩
    apply Finset.card_eq_one.mpr
    refine ⟨p b,?_⟩
    ext e
    simp only [Finset.mem_filter,Finset.mem_singleton]
    constructor
    · rintro ⟨he,hP⟩
      obtain ⟨b',_,rfl⟩ := Finset.mem_image.mp hP
      have hh : b' = b := Subtype.ext ((hb b').symm.trans (N.blackEndpoint_eq black hc hv ((N.mem_star _ _).mp he)))
      rw [hh]
    · rintro rfl
      have hh : N.blackEndpoint black (p b) = v := hb b
      exact ⟨(N.mem_star _ _).mpr (hh ▸ (N.blackEndpoint_spec black hc (p b)).2),hpP b⟩
  · obtain ⟨b,hbv⟩ := hfs ⟨v,hv⟩
    have hwv : N.blackEndpoint (fun v => ¬black v) (p b) = v := (hw b).trans (congrArg Subtype.val hbv)
    apply Finset.card_eq_one.mpr
    refine ⟨p b,?_⟩
    ext e
    simp only [Finset.mem_filter,Finset.mem_singleton]
    constructor
    · rintro ⟨he,hP⟩
      obtain ⟨b',_,rfl⟩ := Finset.mem_image.mp hP
      have hh : f b' = f b := Subtype.ext ((hw b').symm.trans
        ((N.blackEndpoint_eq (fun v => ¬black v) (N.complement_coloring black hc) hv ((N.mem_star _ _).mp he)).trans ((congrArg Subtype.val hbv).symm)))
      rw [hfi hh]
    · rintro rfl
      exact ⟨(N.mem_star _ _).mpr (hwv ▸ (N.blackEndpoint_spec (fun v => ¬black v) (N.complement_coloring black hc) (p b)).2),hpP b⟩
end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] in
lemma sum_substars (hN : N.Simple) (P : Finset E) (A : Finset V) :
    ∑ v ∈ A, ((N.star v).filter fun e => e ∈ P).card =
      ∑ e, if e ∈ P then ((if N.tail e ∈ A then 1 else 0) + (if N.head e ∈ A then 1 else 0)) else 0 := by
  calc
    _ = ∑ v ∈ A, ∑ e, if e ∈ P then ((if N.tail e = v then 1 else 0) + (if N.head e = v then 1 else 0)) else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      rw [star,Finset.filter_filter,Finset.card_filter]
      simp only [Incident]
      apply Finset.sum_congr rfl
      intro e _
      have hne := hN.loopless e
      by_cases hp : e ∈ P <;> by_cases ht : N.tail e = v <;> by_cases hh : N.head e = v <;> simp_all
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      by_cases hp : e ∈ P <;> simp [hp,Finset.sum_add_distrib]

lemma matching_cut_balance (hN : N.Simple) (h3 : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hc : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (P : Finset E) (hd : ∀ v, ((N.star v).filter fun e => e ∈ P).card = 1)
    (A : Finset V) (hcut : N.cut A ⊆ P) :
    (N.cut A).card = 2*(N.blackCut black A).card := by
  have hsum := N.sum_substars hN P A
  simp only [hd,Finset.sum_const,smul_eq_mul,mul_one] at hsum
  have htotal : A.card + (N.cut A).card = 2*((N.regionEdges A).filter fun e => e ∈ P).card := by
    rw [hsum]
    simp only [cut,regionEdges,Finset.card_filter,Finset.sum_filter,
      ← Finset.sum_add_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    have hh : (N.tail e ∈ A ∧ N.head e ∉ A ∨ N.head e ∈ A ∧ N.tail e ∉ A) → e ∈ P := by
      intro hh; apply hcut; simpa [cut] using hh
    by_cases ht : N.tail e ∈ A <;> by_cases hh' : N.head e ∈ A <;> by_cases hp : e ∈ P <;> simp_all
  have hbsum := N.sum_substars hN P (A.filter black)
  simp only [hd,Finset.sum_const,smul_eq_mul,mul_one] at hbsum
  have hblack : (A.filter black).card + (N.cut A).card =
      ((N.regionEdges A).filter fun e => e ∈ P).card + (N.blackCut black A).card := by
    rw [hbsum]
    simp only [cut,regionEdges,blackCut,Finset.card_filter,Finset.mem_filter,Finset.sum_filter,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    have hh : (N.tail e ∈ A ∧ N.head e ∉ A ∨ N.head e ∈ A ∧ N.tail e ∉ A) → e ∈ P := by
      intro hh; apply hcut; simpa [cut] using hh
    have hc' := hc e
    by_cases ht : N.tail e ∈ A <;> by_cases hh' : N.head e ∈ A <;>
      by_cases hp : e ∈ P <;> by_cases hb : black (N.tail e) <;> by_cases hw : black (N.head e) <;>
      simp_all [blackEndpoint]
  have hcub := N.cubic_region_count hN h3 A
  have hbcub := N.cubic_black_region_count hN h3 black hc A
  omega
end
end Barnette.Network

namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

lemma black_white_balance : Fintype.card {v // M.black v} = Fintype.card {v // ¬M.black v} := by
  have hc := M.cubic_cards.2
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_subtype]
  change (Finset.univ.filter M.black).card = Fintype.card V - (Finset.univ.filter M.black).card
  omega

lemma recovery_matching (P : (M.system root).Pair (M.nonroots root)) (hr : M.black root)
    (ha : ((M.system root).oppositeGraph P.right).IsAcyclic) (i : Fin 3) :
    ∃ S : Finset E, S ⊆ (M.removed P i)ᶜ ∧ ∀ v, ((N.star v).filter fun e => e ∈ S).card = 1 :=
  N.tree_matching M.black M.coloring _ (M.remainder_independent P hr ha i) root hr
    (M.remainder_black_degree P hr i) M.black_white_balance

end
end Barnette.Network.ColoredDual
namespace Barnette.CycleCoordinates
variable {V : Type*} {G : SimpleGraph V} (C : Barnette.CycleCoordinates G)
abbrev reverseCycle : Barnette.CycleCoordinates G where
  n := C.n
  vertex := ⟨fun i => C.vertex (-i),fun _ _ h => neg_injective (C.vertex.injective h)⟩
  adjacent i := by
    have hh := (C.adjacent (-i-1)).symm
    change G.Adj (C.vertex (-i)) (C.vertex (-(i+1)))
    rw [sub_add_cancel,show -i-1 = -(i+1) by abel] at hh
    exact hh
end Barnette.CycleCoordinates

namespace Barnette.Network
noncomputable section
variable {V E : Type*} (N : Network V E)
lemma directed_cycle_of_not_acyclic (ht : Function.Injective N.tail) (hn : ¬N.graph.IsAcyclic) :
    ∃ (C : Barnette.CycleCoordinates N.graph) (e : Fin (C.n+3) → E),
      ∀ i, N.tail (e i) = C.vertex i ∧ N.head (e i) = C.vertex (i+1) := by
  obtain ⟨C⟩ := Barnette.cycleCoordinates_of_not_acyclic hn
  let e : Fin (C.n+3) ↪ E := ⟨N.cycleEdge C,N.cycleEdge_injective C⟩
  have he (i) : (N.tail (e i) = C.vertex i ∧ N.head (e i) = C.vertex (i+1)) ∨
      (N.tail (e i) = C.vertex (i+1) ∧ N.head (e i) = C.vertex i) :=
    Sym2.eq_iff.mp (N.cycleEdge_ends C i)
  rcases C.tail_orientation e N.tail ht (fun i => (he i).elim (Or.inl ∘ And.left) (Or.inr ∘ And.left)) with hf|hb
  · refine ⟨C,e,fun i => ⟨hf i,?_⟩⟩
    rcases he i with h|h
    · exact h.2
    · exact ((C.adjacent i).1 ((hf i).symm.trans h.1)).elim
  · refine ⟨C.reverseCycle,fun i => e (-i-1),fun i => ?_⟩
    have hh : N.head (e (-i-1)) = C.vertex (-i-1) := by
      rcases he (-i-1) with h|h
      · exact ((C.adjacent (-i-1)).1 (h.1.symm.trans (hb (-i-1)))).elim
      · exact h.2
    constructor
    · change N.tail (e (-i-1)) = C.vertex (-i)
      simpa only [sub_add_cancel] using hb (-i-1)
    · change N.head (e (-i-1)) = C.vertex (-(i+1))
      exact hh.trans (congrArg C.vertex (show -i-1 = -(i+1) by abel))
end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype E] (N : Network V E)

def matchingEdge (P : Finset E) (hd : ∀ v, ((N.star v).filter fun e => e ∈ P).card = 1) (v : V) : E :=
  (Finset.card_eq_one.mp (hd v)).choose

lemma matchingEdge_spec (P : Finset E) (hd : ∀ v, ((N.star v).filter fun e => e ∈ P).card = 1) (v : V) :
    (N.star v).filter (fun e => e ∈ P) = {N.matchingEdge P hd v} :=
  (Finset.card_eq_one.mp (hd v)).choose_spec

lemma matchingEdge_mem (P : Finset E) (hd : ∀ v, ((N.star v).filter fun e => e ∈ P).card = 1) (v : V) :
    N.matchingEdge P hd v ∈ N.star v ∧ N.matchingEdge P hd v ∈ P := by
  exact Finset.mem_filter.mp (by rw [N.matchingEdge_spec P hd v]; exact Finset.mem_singleton_self _)

lemma matchingEdge_eq (P : Finset E) (hd : ∀ v, ((N.star v).filter fun e => e ∈ P).card = 1)
    {v : V} {e : E} (he : e ∈ N.star v) (hp : e ∈ P) : e = N.matchingEdge P hd v := by
  exact Finset.mem_singleton.mp ((N.matchingEdge_spec P hd v) ▸ Finset.mem_filter.mpr ⟨he,hp⟩)
end
end Barnette.Network

namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

abbrev selectNet (s : M.State root) (P : Finset E)
    (hd : ∀ v, ((N.star v).filter fun e => e ∈ P).card = 1) : Network F (M.Black root) where
  tail t := s.value t
  head t := D.otherEnd (N.matchingEdge P hd t.val) (s.value t)

lemma selectNet_forest (s : M.State root) (P : Finset E)
    (hd : ∀ v, ((N.star v).filter fun e => e ∈ P).card = 1)
    (hi : ∀ t : M.Black root, D.Incident (N.matchingEdge P hd t.val) (s.value t)) :
    (M.selectNet s P hd).graph.IsAcyclic := by
  by_contra hn
  obtain ⟨C,t,ht⟩ := (M.selectNet s P hd).directed_cycle_of_not_acyclic s.value_injective hn
  have he (i) : s(D.tail (N.matchingEdge P hd (t i).val),D.head (N.matchingEdge P hd (t i).val)) =
      s(C.vertex i,C.vertex (i+1)) := by
    rw [(D.otherEnd_spec M.dual_simple (hi (t i))).2]
    change s((M.selectNet s P hd).tail (t i),(M.selectNet s P hd).head (t i)) = _
    rw [(ht i).1,(ht i).2]
  let C' : Barnette.CycleCoordinates D.graph := {
    n := C.n
    vertex := C.vertex
    adjacent i := ⟨(C.adjacent i).1,N.matchingEdge P hd (t i).val,Sym2.eq_iff.mp (he i)⟩ }
  have hedge (i) : D.cycleEdge C' i = N.matchingEdge P hd (t i).val := by
    apply M.dual_simple.pair_injective
    dsimp only
    rw [D.cycleEdge_ends]
    exact (he i).symm
  obtain ⟨A,c,_,_,_,_,hcut,hcount,_⟩ := M.cycle_disk s C' t
    (fun i => hedge i ▸ (N.matchingEdge_mem P hd (t i).val).1) (fun i => (ht i).1)
  have hsub : N.cut A ⊆ P := by
    intro e he
    rw [hcut] at he
    obtain ⟨i,rfl⟩ := (D.mem_cycleEdges C' e).mp he
    rw [hedge]
    exact (N.matchingEdge_mem P hd (t i).val).2
  have hbal := N.matching_cut_balance M.simple M.cubic M.black M.coloring P hd A hsub
  omega

lemma selected_forest (s : M.State root) (P : Finset E)
    (hd : ∀ v, ((N.star v).filter fun e => e ∈ P).card = 1) (_hr : M.black root)
    (hi : ∀ t : M.Black root, D.Incident (N.matchingEdge P hd t.val) (s.value t))
    (i : Fin 3) (he0 : N.matchingEdge P hd root = (M.face root).edge i) :
    (D.restrict (Subtype.val : P → E)).graph.IsAcyclic := by
  let L := M.selectNet s P hd
  let K := L.addSink (fun j => (M.face root).corner (rootStart (i+2) j)) ((M.face root).corner (i+2+2))
  have hK : K.graph.IsAcyclic := by
    apply L.addSink_acyclic (M.selectNet_forest s P hd hi) s.value_injective _
      ((M.face root).corner_injective.comp (rootStart_inj (i+2)))
    · intro t j h
      exact s.value_mem t ⟨rootStart (i+2) j,h.symm⟩
    · rintro ⟨t|j,h⟩
      · exact s.value_mem t ⟨i+2+2,h.symm⟩
      · exact rootStart_ne (i+2) j ((M.face root).corner_injective h)
  apply SimpleGraph.IsAcyclic.anti ?_ hK
  intro v w ⟨hvw,e,he⟩
  let b := N.blackEndpoint M.black e.val
  have hb : M.black b := (N.blackEndpoint_spec M.black M.coloring e.val).1
  have heb : e.val ∈ N.star b := (N.mem_star _ _).mpr (N.blackEndpoint_spec M.black M.coloring e.val).2
  have hep : e.val = N.matchingEdge P hd b := N.matchingEdge_eq P hd heb e.property
  have hends : s(D.tail e.val,D.head e.val) = s(v,w) := Sym2.eq_iff.mpr he
  by_cases hbr : b = root
  · have hstart : rootStart (i+2) 1 = i := by fin_cases i <;> rfl
    have hend : i+2+2 = i+1 := by fin_cases i <;> rfl
    refine ⟨hvw,Sum.inr 1,?_⟩
    apply Sym2.eq_iff.mp
    change s((M.face root).corner (rootStart (i+2) 1),(M.face root).corner (i+2+2)) = s(v,w)
    rw [hstart,hend,← (M.face root).edge_ends i,← he0,← hbr,← hep]
    exact hends
  · let t : M.Black root := ⟨b,hb,hbr⟩
    refine ⟨hvw,Sum.inl t,?_⟩
    apply Sym2.eq_iff.mp
    change s(s.value t,D.otherEnd (N.matchingEdge P hd b) (s.value t)) = s(v,w)
    rw [← (D.otherEnd_spec M.dual_simple (hi t)).2,← hep]
    exact hends

lemma recover_connected_complement (Q : (M.system root).Pair (M.nonroots root))
    (hr : M.black root) (ha : ((M.system root).oppositeGraph Q.right).IsAcyclic) (i : Fin 3) :
    ∃ P : Finset E, (M.face root).edge i ∈ P ∧
      (∀ v, ((N.star v).filter fun e => e ∈ P).card = 1) ∧
      (N.restrict (Subtype.val : ↥(Pᶜ) → E)).graph.Connected := by
  obtain ⟨P,hsub,hd⟩ := M.recovery_matching Q hr ha i
  have hi (t : M.Black root) : D.Incident (N.matchingEdge P hd t.val) (Q.right.value t) :=
    M.remainder_incident Q hr i t (N.matchingEdge_mem P hd t.val).1
      (hsub (N.matchingEdge_mem P hd t.val).2)
  have he0 : N.matchingEdge P hd root = (M.face root).edge i := by
    have hmem := (N.matchingEdge_mem P hd root)
    have hm := M.removed_at_black Q hr i root hr hmem.1
    have hn := (not_congr hm).mp (Finset.mem_compl.mp (hsub hmem.2))
    simpa using hn
  refine ⟨P,he0 ▸ (N.matchingEdge_mem P hd root).2,hd,?_⟩
  exact M.duality.complement_connected N D M.dual_simple P
    (M.selected_forest Q.right P hd hr hi i he0)
end
end Barnette.Network.ColoredDual

end OAI


namespace OAI

/-! Three-edge cuts, capped graphs, and preservation of graph properties. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

lemma gradient_small_support_edge (h : N.ThreeEdgeConnected) (f : V → ℝ) (s : Finset E) (hs : s.card ≤ 2)
    (hf : ∀ e, e ∉ s → N.gradient f e = 0) : N.gradient f = 0 := by
  ext e
  by_contra he
  have hne : f (N.head e) ≠ f (N.tail e) := by
    simpa only [gradient_apply, Pi.zero_apply, sub_eq_zero] using he
  let A := Finset.univ.filter fun v => f v = f (N.tail e)
  have hin : A.Nonempty := ⟨N.tail e, by simp [A]⟩
  have hout : ∃ w, w ∉ A := ⟨N.head e, by simp [A, hne]⟩
  have hsub : N.cut A ⊆ s := by
    intro k hk
    by_contra hks
    have hg : f (N.head k) = f (N.tail k) := sub_eq_zero.mp (hf k hks)
    rcases (N.mem_cut A k).mp hk with ⟨ht,hh⟩ | ⟨hh,ht⟩
    · apply hh; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      exact hg.trans ht
    · apply ht; simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
      exact hg.symm.trans hh
  have h₁ := h A hin (by obtain ⟨w,hw⟩ := hout; exact ⟨w,Finset.mem_compl.mpr hw⟩)
  have h₂ := Finset.card_le_card hsub
  omega

variable {F : Type*} [Fintype F] (D : Network F E)

omit [Fintype F] in
theorem Duality.simple_dual_edge (h : N.Duality D)
    (h3 : N.ThreeEdgeConnected) : D.Simple := by
  have lift_zero (x : E → ℝ) (hx : D.boundary x = 0)
      (s : Finset E) (hs : s.card ≤ 2) (hxs : ∀ e, e ∉ s → x e = 0) : x = 0 := by
    have hx' : x ∈ N.gradient.range := by rw [← h.dual_cycles_eq_cuts]; exact hx
    obtain ⟨f,hf⟩ := hx'
    rw [← hf]
    exact N.gradient_small_support_edge h3 f s hs (by simpa only [hf] using hxs)
  refine ⟨?_, ?_⟩
  · intro e he
    have hz : D.boundary (basisVec e) = 0 := by
      rw [D.boundary_basis]
      ext v
      simp [incidence, he]
    have hzero := lift_zero (basisVec e) hz {e} (by simp) (by
      intro k hk; simp only [Finset.mem_singleton] at hk; simp [basisVec, hk])
    have hh := congrFun hzero e
    norm_num [basisVec] at hh
  · intro e f hef
    by_contra hne
    rcases Sym2.eq_iff.mp hef with ⟨ht,hh⟩ | ⟨ht,hh⟩
    · have hz : D.boundary (basisVec e - basisVec f) = 0 := by
        rw [map_sub, D.boundary_basis, D.boundary_basis]
        ext v
        simp [incidence, ht, hh]
      have hzero := lift_zero (basisVec e - basisVec f) hz {e,f}
        (by simpa using Finset.card_insert_le e ({f} : Finset E))
        (by intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
            simp [basisVec, hk.1, hk.2])
      have hv := congrFun hzero e
      norm_num [basisVec, hne] at hv
    · have hz : D.boundary (basisVec e + basisVec f) = 0 := by
        rw [map_add, D.boundary_basis, D.boundary_basis]
        ext v
        dsimp [incidence]
        rw [ht, hh]
        ring
      have hzero := lift_zero (basisVec e + basisVec f) hz {e,f}
        (by simpa using Finset.card_insert_le e ({f} : Finset E))
        (by intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
            simp [basisVec, hk.1, hk.2])
      have hv := congrFun hzero e
      norm_num [basisVec, hne] at hv

omit [Fintype F] in
theorem Duality.cubic_face_triangles_edge (h : N.Duality D) (hN : N.Simple)
    (h3 : N.ThreeEdgeConnected)
    (hc : N.graph.IsRegularOfDegree 3) : ∀ v, Nonempty (D.Triangle (N.star v)) := by
  intro v
  have hD := h.simple_dual_edge N D h3
  have hx := h.dual_conserved_gradient N D (fun w => if w = v then 1 else 0)
  have hs : (D.flowSupport (N.gradient (fun w => if w = v then 1 else 0))).card = 3 := by
    rw [N.gradient_indicator_support D hN, N.card_star hN, hc v]
  simpa only [N.gradient_indicator_support D hN] using D.triangle_of_flow hD _ hx hs

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

omit [Fintype F] in
lemma make_coloredDual (h : N.Duality D) (hN : N.Simple) (h3 : N.ThreeEdgeConnected)
    (hc : N.graph.IsRegularOfDegree 3) (black : V → Prop)
    (hb : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) : Nonempty (N.ColoredDual D) := by
  have hs := h.simple_dual_edge N D h3
  have ht := h.cubic_face_triangles_edge N D hN h3 hc
  choose t ho using fun v => N.oriented_face D h hN hs v (ht v).some
  exact ⟨⟨h,hN,hs,hc,black,hb,t,ho⟩⟩

lemma irreducible_matching (M : N.ColoredDual D)
    (h3 : N.ThreeEdgeConnected) (htr : N.TrivialThreeCuts) (e : E) :
    ∃ P : Finset E, e ∈ P ∧ (∀ v, ((N.star v).filter fun e => e ∈ P).card = 1) ∧
      (N.restrict (Subtype.val : ↥(Pᶜ) → E)).graph.Connected := by
  let root := N.blackEndpoint M.black e
  have hr := (N.blackEndpoint_spec M.black M.coloring e).1
  have he : e ∈ N.star root := (N.mem_star _ _).mpr (N.blackEndpoint_spec M.black M.coloring e).2
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp ((M.face root).edge_range.symm ▸ he)
  obtain ⟨Q,hQ⟩ := M.forest_pair (M.pair_nonempty h3 htr root hr)
  simpa only [hi] using M.recover_connected_complement Q hr hQ i
end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

def capMap (_N : Network V E) (A : Finset V) (v : V) : Option A := if h : v ∈ A then some ⟨v,h⟩ else none

omit [Fintype V] [Fintype E] in
@[simp] lemma capMap_some (A : Finset V) (v : A) : N.capMap A v.val = some v := by
  simp [capMap,v.property]
omit [Fintype V] [Fintype E] in
@[simp] lemma capMap_eq_none (A : Finset V) (v : V) : N.capMap A v = none ↔ v ∉ A := by
  simp [capMap]
omit [Fintype V] [Fintype E] in
@[simp] lemma capMap_eq_some (A : Finset V) (v : V) (w : A) :
    N.capMap A v = some w ↔ v = w.val := by
  by_cases h : v ∈ A
  · simp [capMap,h,Subtype.ext_iff]
  · simp only [capMap,dite_eq_right h,reduceCtorEq,false_iff]
    exact fun he => h (he ▸ w.property)

omit [Fintype E] in
lemma capMap_surjective (A : Finset V) (hA : Aᶜ.Nonempty) : Function.Surjective (N.capMap A) := by
  rintro (_|v)
  · obtain ⟨v,hv⟩ := hA
    exact ⟨v,(N.capMap_eq_none A v).mpr (Finset.mem_compl.mp hv)⟩
  · exact ⟨v.val,N.capMap_some A v⟩

abbrev cap (A : Finset V) : Network (Option A) (N.regionEdges A) :=
  (N.mapVertices (N.capMap A)).restrict Subtype.val

omit [Fintype V] in
lemma cap_loopless (hN : N.Simple) (A : Finset V) (e : N.regionEdges A) :
    (N.cap A).tail e ≠ (N.cap A).head e := by
  change N.capMap A (N.tail e.val) ≠ N.capMap A (N.head e.val)
  intro he
  rcases (N.mem_regionEdges A e.val).mp e.property with ht|hh
  · have ht' := N.capMap_some A ⟨N.tail e.val,ht⟩
    rw [ht'] at he
    exact hN.loopless e.val (((N.capMap_eq_some A _ _).mp he.symm).symm)
  · have hh' := N.capMap_some A ⟨N.head e.val,hh⟩
    rw [hh'] at he
    exact hN.loopless e.val ((N.capMap_eq_some A _ _).mp he)

omit [Fintype V] in
lemma cap_star_some (A : Finset V) (v : A) :
    ((N.cap A).star (some v)).image Subtype.val = N.star v.val := by
  ext e
  simp only [Finset.mem_image,mem_star,Incident]
  constructor
  · rintro ⟨k,hk,rfl⟩
    exact hk.elim (fun h => Or.inl ((N.capMap_eq_some A _ v).mp h))
      (fun h => Or.inr ((N.capMap_eq_some A _ v).mp h))
  · intro he
    have hm : e ∈ N.regionEdges A := (N.mem_regionEdges A e).mpr
      (he.elim (fun h => Or.inl (h ▸ v.property)) (fun h => Or.inr (h ▸ v.property)))
    refine ⟨⟨e,hm⟩,?_,rfl⟩
    exact he.elim (fun h => Or.inl ((N.capMap_eq_some A _ v).mpr h))
      (fun h => Or.inr ((N.capMap_eq_some A _ v).mpr h))

omit [Fintype V] in
lemma cap_star_none (A : Finset V) :
    ((N.cap A).star none).image Subtype.val = N.cut A := by
  ext e
  simp only [Finset.mem_image,mem_star,Incident,mem_cut]
  constructor
  · rintro ⟨k,hk,rfl⟩
    have hm := (N.mem_regionEdges A k.val).mp k.property
    change N.capMap A (N.tail k.val) = none ∨ N.capMap A (N.head k.val) = none at hk
    simp only [capMap_eq_none] at hk
    tauto
  · intro he
    have hm : e ∈ N.regionEdges A := (N.mem_regionEdges A e).mpr (he.elim (Or.inl ∘ And.left) (Or.inr ∘ And.left))
    refine ⟨⟨e,hm⟩,?_,rfl⟩
    change N.capMap A (N.tail e) = none ∨ N.capMap A (N.head e) = none
    simp only [capMap_eq_none]
    tauto

lemma cap_star_card (hN : N.Simple) (hc : N.graph.IsRegularOfDegree 3)
    (A : Finset V) (hA : (N.cut A).card = 3) (v : Option A) : ((N.cap A).star v).card = 3 := by
  rw [← Finset.card_image_of_injective _ Subtype.val_injective]
  cases v with
  | none => rw [N.cap_star_none,hA]
  | some v => rw [N.cap_star_some,N.card_star hN,hc v.val]

def capPreimage (A : Finset V) (B : Finset (Option A)) : Finset V :=
  Finset.univ.filter fun v => N.capMap A v ∈ B

omit [Fintype E] in
@[simp] lemma mem_capPreimage (A : Finset V) (B : Finset (Option A)) (v : V) :
    v ∈ N.capPreimage A B ↔ N.capMap A v ∈ B := by simp [capPreimage]

lemma cap_cut (A : Finset V) (B : Finset (Option A)) :
    ((N.cap A).cut B).image Subtype.val = N.cut (N.capPreimage A B) := by
  ext e
  simp only [Finset.mem_image,mem_cut,mem_capPreimage]
  constructor
  · rintro ⟨k,hk,rfl⟩
    exact hk
  · intro he
    have hm : e ∈ N.regionEdges A := by
      apply (N.mem_regionEdges A e).mpr
      by_contra hn
      have ht := (N.capMap_eq_none A (N.tail e)).mpr (not_or.mp hn).1
      have hh := (N.capMap_eq_none A (N.head e)).mpr (not_or.mp hn).2
      rw [ht,hh] at he
      tauto
    exact ⟨⟨e,hm⟩,he,rfl⟩

lemma cap_threeConnected (hN : N.ThreeEdgeConnected) (A : Finset V) (hA : Aᶜ.Nonempty) :
    (N.cap A).ThreeEdgeConnected := by
  intro B hB hBc
  rw [← Finset.card_image_of_injective _ Subtype.val_injective,N.cap_cut]
  apply hN
  · obtain ⟨v,hv⟩ := hB
    obtain ⟨w,rfl⟩ := N.capMap_surjective A hA v
    exact ⟨w,(N.mem_capPreimage A B w).mpr hv⟩
  · obtain ⟨v,hv⟩ := hBc
    obtain ⟨w,rfl⟩ := N.capMap_surjective A hA v
    exact ⟨w,by simpa only [Finset.mem_compl,mem_capPreimage] using hv⟩

lemma ThreeEdgeConnected.connected [Nonempty V] (h : N.ThreeEdgeConnected) : N.graph.Connected := by
  apply N.connected_of_kernel_constants
  intro f hf v w
  by_contra hn
  let A := Finset.univ.filter fun z => f z = f v
  have hA : (N.cut A).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    have hh := (N.gradient_eq_zero_iff f).mp hf e
    have hc := (N.mem_cut A e).mp he
    simp only [A,Finset.mem_filter,Finset.mem_univ,true_and,hh] at hc
    tauto
  have hc := h A ⟨v,by simp [A]⟩ ⟨w,by simp [A,Ne.symm hn]⟩
  omega

lemma threeCut_bond (h : N.ThreeEdgeConnected) (A : Finset V) (hA : (N.cut A).card = 3) : N.Bond A := by
  refine ⟨Finset.card_pos.mp (by omega),?_⟩
  intro B hB
  by_cases hn : (N.cut B).Nonempty
  · right
    obtain ⟨e,he⟩ := hn
    have hc := (N.mem_cut B e).mp he
    have hi : B.Nonempty := hc.elim (fun h => ⟨_,h.1⟩) (fun h => ⟨_,h.1⟩)
    have ho : Bᶜ.Nonempty := hc.elim (fun h => ⟨_,Finset.mem_compl.mpr h.2⟩) (fun h => ⟨_,Finset.mem_compl.mpr h.2⟩)
    exact Finset.eq_of_subset_of_card_le hB (by have hh := h B hi ho; omega)
  · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp hn)

omit [Fintype V] [Fintype E] in
lemma cap_connectedFibers (A : Finset V)
    (hc : (N.graph.induce {v | v ∉ A}).Connected) : N.ConnectedFibers (N.capMap A) := by
  intro v w he
  by_cases hv : v ∈ A
  · have hv' := N.capMap_some A ⟨v,hv⟩
    rw [hv'] at he
    have hh : w = v := (N.capMap_eq_some A _ _).mp he.symm
    subst w
    exact SimpleGraph.Reachable.refl v
  · have hw : w ∉ A := (N.capMap_eq_none A w).mp (he.symm.trans ((N.capMap_eq_none A v).mpr hv))
    let f : (N.graph.induce {v | v ∉ A}) →g (N.restrict (Subtype.val : N.internal (N.capMap A) → E)).graph := {
      toFun := Subtype.val
      map_rel' := by
        intro x y hxy
        obtain ⟨hne,e,hee⟩ := hxy
        change (N.tail e = x.val ∧ N.head e = y.val) ∨ (N.tail e = y.val ∧ N.head e = x.val) at hee
        have hm : e ∈ N.internal (N.capMap A) := by
          rcases hee with ⟨ht,hh⟩|⟨ht,hh⟩ <;>
            change N.capMap A (N.tail e) = N.capMap A (N.head e) <;>
            rw [ht,hh,(N.capMap_eq_none A _).mpr x.property,(N.capMap_eq_none A _).mpr y.property]
        exact ⟨hne,⟨e,hm⟩,hee⟩ }
    exact (hc ⟨v,hv⟩ ⟨w,hw⟩).map f
end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

lemma simple_of_cubic_stars (hl : ∀ e, N.tail e ≠ N.head e)
    (hc : ∀ v, (N.star v).card = 3) (h3 : N.ThreeEdgeConnected)
    (hV : 3 ≤ Fintype.card V) : N.Simple := by
  refine ⟨hl,?_⟩
  intro e f hef
  by_contra hne
  dsimp only at hef
  let a := N.tail e
  let b := N.head e
  have hab : a ≠ b := hl e
  have hfa : N.Incident f a := (N.incident_iff_mem_pair f a).mpr (by rw [← hef]; simp [a])
  have hfb : N.Incident f b := (N.incident_iff_mem_pair f b).mpr (by rw [← hef]; simp [b])
  have hsa : ({e,f} : Finset E) ⊆ N.star a := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl|hk
    · exact (N.mem_star _ _).mpr (Or.inl rfl)
    · have hk' := Finset.mem_singleton.mp hk
      subst k
      exact (N.mem_star _ _).mpr hfa
  have hsb : ({e,f} : Finset E) ⊆ N.star b := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl|hk
    · exact (N.mem_star _ _).mpr (Or.inr rfl)
    · have hk' := Finset.mem_singleton.mp hk
      subst k
      exact (N.mem_star _ _).mpr hfb
  have hein : e ∉ N.cut {a,b} := by simp [mem_cut,a,b]
  have hfin : f ∉ N.cut {a,b} := by
    have hh := Sym2.eq_iff.mp hef
    rcases hh with ⟨ht,hh⟩|⟨ht,hh⟩ <;> simp [mem_cut,← ht,← hh,a,b]
  have hsub : N.cut {a,b} ⊆ (N.star a \ {e,f}) ∪ (N.star b \ {e,f}) := by
    intro k hk
    have hke : k ∉ ({e,f} : Finset E) := by
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
      exact ⟨fun hh => hein (hh ▸ hk),fun hh => hfin (hh ▸ hk)⟩
    have hi : N.Incident k a ∨ N.Incident k b := by
      have hh := (N.mem_cut {a,b} k).mp hk
      simp only [Finset.mem_insert,Finset.mem_singleton] at hh
      simp only [Incident]
      tauto
    exact hi.elim (fun hi => Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨(N.mem_star _ _).mpr hi,hke⟩))
      (fun hi => Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨(N.mem_star _ _).mpr hi,hke⟩))
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [Finset.card_sdiff_of_subset hsa,Finset.card_sdiff_of_subset hsb,hc,hc] at hcard
  simp only [Finset.card_pair hne] at hcard
  have hout : ({a,b} : Finset V)ᶜ.Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_compl,Finset.card_pair hab]
    omega
  have hh := h3 {a,b} (by simp) hout
  omega

lemma cap_simple (hN : N.Simple) (hc : N.graph.IsRegularOfDegree 3) (h3 : N.ThreeEdgeConnected)
    (A : Finset V) (hcut : (N.cut A).card = 3) (hA : 2 ≤ A.card) (ho : Aᶜ.Nonempty) :
    (N.cap A).Simple := by
  apply (N.cap A).simple_of_cubic_stars (N.cap_loopless hN A)
    (N.cap_star_card hN hc A hcut) (N.cap_threeConnected h3 A ho)
  simp only [Fintype.card_option,Fintype.card_coe]
  omega

lemma cap_cubic (hN : N.Simple) (hc : N.graph.IsRegularOfDegree 3) (h3 : N.ThreeEdgeConnected)
    (A : Finset V) (hcut : (N.cut A).card = 3) (hA : 2 ≤ A.card) (ho : Aᶜ.Nonempty) :
    (N.cap A).graph.IsRegularOfDegree 3 := by
  intro v
  rw [← (N.cap A).card_star (N.cap_simple hN hc h3 A hcut hA ho)]
  exact N.cap_star_card hN hc A hcut v

lemma threeCut_black_card (hN : N.Simple) (hc : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hb : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (A : Finset V) (hA : (N.cut A).card = 3) :
    (N.blackCut black A).card = 0 ∨ (N.blackCut black A).card = 3 := by
  have h₁ := N.cubic_region_count hN hc A
  have h₂ := N.cubic_black_region_count hN hc black hb A
  have h₃ := Finset.card_le_card (Finset.filter_subset (fun e => N.blackEndpoint black e ∈ A) (N.cut A))
  change (N.blackCut black A).card ≤ (N.cut A).card at h₃
  omega

def capBlack (black : V → Prop) (A : Finset V) : Option A → Prop
  | none => (N.blackCut black A).card = 0
  | some v => black v.val

lemma cap_coloring (hN : N.Simple) (hc : N.graph.IsRegularOfDegree 3)
    (black : V → Prop) (hb : ∀ e, black (N.tail e) ↔ ¬black (N.head e))
    (A : Finset V) (hA : (N.cut A).card = 3) :
    ∀ e, N.capBlack black A ((N.cap A).tail e) ↔ ¬N.capBlack black A ((N.cap A).head e) := by
  intro e
  have hm := (N.mem_regionEdges A e.val).mp e.property
  have hcol := hb e.val
  have hboundary : e.val ∈ N.cut A →
      ((N.blackCut black A).card = 0 ↔ N.blackEndpoint black e.val ∉ A) := by
    intro he
    rcases N.threeCut_black_card hN hc black hb A hA with hz|hf
    · have hn : N.blackEndpoint black e.val ∉ A := by
        intro hh
        have hh' : e.val ∈ N.blackCut black A := Finset.mem_filter.mpr ⟨he,hh⟩
        rw [Finset.card_eq_zero.mp hz] at hh'
        exact Finset.notMem_empty _ hh'
      simp [hz,hn]
    · have heq : N.blackCut black A = N.cut A :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
      have hh := (Finset.mem_filter.mp (show e.val ∈ N.blackCut black A by rw [heq]; exact he)).2
      simp [hf,hh]
  change N.capBlack black A (N.capMap A (N.tail e.val)) ↔ ¬N.capBlack black A (N.capMap A (N.head e.val))
  by_cases ht : N.tail e.val ∈ A <;> by_cases hh : N.head e.val ∈ A
  · simpa only [capMap,dite_eq_left ht,dite_eq_left hh,capBlack] using hcol
  · have he : e.val ∈ N.cut A := (N.mem_cut A e.val).mpr (Or.inl ⟨ht,hh⟩)
    simp only [capMap,dite_eq_left ht,dite_eq_right hh,capBlack,hboundary he]
    by_cases hb' : black (N.tail e.val) <;> simp [blackEndpoint,hb',ht,hh]
  · have he : e.val ∈ N.cut A := (N.mem_cut A e.val).mpr (Or.inr ⟨hh,ht⟩)
    simp only [capMap,dite_eq_right ht,dite_eq_left hh,capBlack,hboundary he]
    by_cases hb' : black (N.tail e.val) <;> simp [blackEndpoint,hb',ht,hh] at hcol ⊢ <;> tauto
  · exact (hm.elim ht hh).elim
end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] in
lemma boundary_range_restrict (s : Set E) :
    (N.restrict (Subtype.val : s → E)).boundary.range =
      Submodule.span ℝ (N.incidence.col '' s) := by
  let : DecidableEq s := Classical.decEq _
  rw [boundary, Matrix.range_toLin']
  congr 1
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e.val, e.property, rfl⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨⟨e, he⟩, rfl⟩

omit [Fintype V] in

lemma exists_independent_restriction (s : Set E) :
    ∃ r ⊆ s,
      Function.Injective (N.restrict (Subtype.val : r → E)).boundary ∧
      (N.restrict (Subtype.val : r → E)).boundary.range =
        (N.restrict (Subtype.val : s → E)).boundary.range := by
  obtain ⟨r, hrs, _, hspan, hi⟩ := exists_linearIndepOn_extension
    (v := N.incidence.col) (linearIndepOn_empty ℝ _) (Set.empty_subset s)
  refine ⟨r, hrs, ?_, ?_⟩
  · exact Matrix.mulVec_injective_iff.mpr hi
  · rw [N.boundary_range_restrict, N.boundary_range_restrict]
    apply le_antisymm
    · exact Submodule.span_mono (Set.image_mono hrs)
    · exact Submodule.span_le.mpr hspan

variable {F : Type*} [Fintype F] (D : Network F E)

lemma duality_of_first_exact (hN : N.graph.Connected) (hD : D.graph.Connected)
    (he : N.boundary.ker = D.gradient.range) : N.Duality D := by
  have ho : ∀ f, N.boundary (D.gradient f) = 0 := by
    intro f
    change D.gradient f ∈ N.boundary.ker
    rw [he]
    exact ⟨f, rfl⟩
  have h₁ := N.dim_cycles hN
  rw [he] at h₁
  have h₂ := D.rank_gradient hD
  exact N.duality_of_orth_card D hN hD (by omega) ho

end
end Barnette.Network

end OAI


namespace OAI

/-! Exact duals of capped graphs and Hamiltonian walks in degree-two graphs. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
universe uF
variable {V E W K : Type*} {F : Type uF} [Fintype V] [Fintype E] [Fintype F]
  [Fintype W] [Fintype K]

omit [Fintype E] in
lemma push_pull_injective {j : K → E} (hj : Function.Injective j) (x : E → ℝ) :
    push j (pull j x) = fun e => if e ∈ Set.range j then x e else 0 := by
  ext e
  by_cases he : e ∈ Set.range j
  · obtain ⟨k, rfl⟩ := he
    have h := congrFun (pull_push_injective hj (pull j x)) k
    simpa only [pull_apply, Set.mem_range_self, ite_true] using h
  · rw [push_eq_zero_outside _ he]
    simp only [he, ite_false]

omit [Fintype K] in
lemma pull_push_disjoint {j : K → E} (r : Set E)
    (hr : ∀ k, j k ∉ r) (x : r → ℝ) :
    pull j (push (Subtype.val : r → E) x) = 0 := by
  ext k
  exact push_eq_zero_outside x (by simpa using hr k)

lemma split_support {j : K → E} (hj : Function.Injective j) (r : Set E)
    (hr : ∀ k, j k ∉ r) (x : E → ℝ)
    (hx : ∀ e, e ∉ r → e ∉ Set.range j → x e = 0) :
    x = push j (pull j x) + push (Subtype.val : r → E) (pull Subtype.val x) := by
  rw [push_pull_injective hj, push_pull_subtype]
  ext e
  by_cases he : e ∈ r
  · have hj' : e ∉ Set.range j := by
      rintro ⟨k, rfl⟩
      exact hr k he
    simp only [Pi.add_apply, he, hj', ite_true, ite_false, zero_add]
  · by_cases hj' : e ∈ Set.range j
    · simp only [Pi.add_apply, he, hj', ite_true, ite_false, add_zero]
    · simp only [Pi.add_apply, he, hj', ite_false, hx e he hj', zero_add]

lemma push_boundary_on_internal (N : Network V E) (q : V → W) (r : Set E)
    (hr : r ⊆ N.internal q) (x : r → ℝ) :
    push q ((N.restrict Subtype.val).boundary x) = 0 := by
  apply eq_of_dot_eq
  intro f
  rw [push_adjoint, (N.restrict _).boundary_adjoint]
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  apply Finset.sum_eq_zero
  intro e _
  have he : (N.restrict (Subtype.val : r → E)).gradient (pull q f) e = 0 := by
    change f (q (N.head e.val)) - f (q (N.tail e.val)) = 0
    rw [show q (N.tail e.val) = q (N.head e.val) from hr e.property]
    exact sub_self _
  rw [he, mul_zero]

theorem Duality.minor (N : Network V E) (D : Network F E) (h : N.Duality D)
    (q : V → W) (hq : Function.Surjective q) (hc : N.ConnectedFibers q)
    (j : K → E) (hj : Function.Injective j)
    (hjext : ∀ k, q (N.tail (j k)) ≠ q (N.head (j k)))
    (hM : ((N.mapVertices q).restrict j).graph.Connected) :
    ∃ (L : Type uF) (_ : Fintype L) (dual : Network L K),
      ((N.mapVertices q).restrict j).Duality dual := by
  obtain ⟨r, hr, hir, her⟩ := N.exists_independent_restriction (N.internal q)
  have hrj : ∀ k, j k ∉ r := fun k hk => hjext k (hr hk)
  let d : Set E := {e | e ∉ r ∧ e ∉ Set.range j}
  let H := D.restrict (Subtype.val : d → E)
  let qD := H.componentMap
  let L := (D.mapVertices qD).restrict j
  let M := (N.mapVertices q).restrict j
  have hqD : Function.Surjective qD := H.componentMap_surjective
  have zeroD (f : H.Components → ℝ) (e : E) (he : e ∈ d) :
      D.gradient (pull qD f) e = 0 := congrFun (H.gradient_componentMap f) ⟨e, he⟩
  have orth (f : F → ℝ) : N.boundary (D.gradient f) = 0 := by
    change D.gradient f ∈ N.boundary.ker
    rw [h.cycles_eq_cuts]
    exact ⟨f, rfl⟩
  have hle : L.gradient.range ≤ M.boundary.ker := by
    rintro _ ⟨f, rfl⟩
    have hs := split_support hj r hrj (D.gradient (pull qD f))
      (fun e he hej => zeroD f e ⟨he, hej⟩)
    have hz := congrArg (push q) (orth (pull qD f))
    rw [hs, map_add, map_add, map_zero,
      ← boundary_restrict, ← boundary_restrict,
      push_boundary_on_internal N q r hr, add_zero] at hz
    change M.boundary (L.gradient f) = 0
    rw [boundary_restrict, boundary_mapVertices]
    simpa only [boundary_restrict, L, gradient_restrict, gradient_mapVertices] using hz
  have hge : M.boundary.ker ≤ L.gradient.range := by
    intro x hx
    have hz : push q (N.boundary (push j x)) = 0 := by
      have he : M.boundary x = 0 := hx
      simpa only [M, boundary_restrict, boundary_mapVertices] using he
    have hy : N.boundary (push j x) ∈ (N.restrict (Subtype.val : r → E)).boundary.range := by
      rw [her, N.range_internal_boundary hq hc]
      exact hz
    obtain ⟨y, hy⟩ := hy
    let z := push j x - push (Subtype.val : r → E) y
    have hzb : N.boundary z = 0 := by
      rw [map_sub, ← N.boundary_restrict (Subtype.val : r → E) y, hy, sub_self]
    have hzg : z ∈ D.gradient.range := by rw [← h.cycles_eq_cuts]; exact hzb
    obtain ⟨g, hg⟩ := hzg
    have hgH : H.gradient g = 0 := by
      ext e
      change D.gradient g e.val = 0
      rw [hg]
      have he : e.val ∉ Set.range (Subtype.val : r → E) := by simpa using e.property.1
      simp only [z, Pi.sub_apply, push_eq_zero_outside x e.property.2,
        push_eq_zero_outside y he, sub_self]
    obtain ⟨f, hf⟩ := H.descends_components g hgH
    refine ⟨f, ?_⟩
    change pull j (D.gradient (pull qD f)) = x
    rw [hf, hg, map_sub, pull_push_injective hj, pull_push_disjoint r hrj, sub_zero]
  have hLc : L.graph.Connected := by
    have : Nonempty F := h.dual_connected.nonempty
    have : Nonempty H.Components := Nonempty.map qD inferInstance
    apply L.connected_of_kernel_constants
    intro f hf a b
    have hs := split_support hj r hrj (D.gradient (pull qD f))
      (fun e he hej => zeroD f e ⟨he, hej⟩)
    have hjzero : pull j (D.gradient (pull qD f)) = 0 := hf
    rw [hjzero, map_zero, zero_add] at hs
    have hz := orth (pull qD f)
    rw [hs, ← boundary_restrict] at hz
    have hrzero : pull (Subtype.val : r → E) (D.gradient (pull qD f)) = 0 := by
      apply hir
      simpa only [map_zero] using hz
    rw [hrzero, map_zero] at hs
    obtain ⟨a', rfl⟩ := hqD a
    obtain ⟨b', rfl⟩ := hqD b
    exact D.gradient_zero_reachable hs (h.dual_connected a' b')
  exact ⟨H.Components, inferInstance, L, M.duality_of_first_exact L hM hLc (le_antisymm hge hle)⟩

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
universe uF
variable {V E : Type*} {F : Type uF} [Fintype V] [Fintype E] [Fintype F]
  (N : Network V E) (D : Network F E)

lemma cap_duality (h : N.Duality D) (hN : N.Simple) (h3 : N.ThreeEdgeConnected)
    (A : Finset V) (hcut : (N.cut A).card = 3) (ha : A.Nonempty) (ho : Aᶜ.Nonempty) :
    ∃ (L : Type uF) (_ : Fintype L) (dual : Network L (N.regionEdges A)), (N.cap A).Duality dual := by
  have hshore : (N.graph.induce {v | v ∉ A}).Connected := by
    have hh := (N.threeCut_bond h3 A hcut).compl.connected_shore N h.connected ho
      (by obtain ⟨v,hv⟩ := ha; exact ⟨v,by simpa only [Finset.mem_compl,not_not] using hv⟩)
    change (N.graph.induce {v | v ∈ Aᶜ}).Connected at hh
    have heq : {v | v ∈ Aᶜ} = {v | v ∉ A} := by ext v; simp
    rw [heq] at hh
    exact hh
  exact h.minor N D (N.capMap A) (N.capMap_surjective A ho)
    (N.cap_connectedFibers A hshore) Subtype.val Subtype.val_injective
    (N.cap_loopless hN A) ((N.cap_threeConnected h3 A ho).connected (N.cap A))

lemma cap_card_lt (A : Finset V) (ho : 2 ≤ Aᶜ.card) : Fintype.card (Option A) < Fintype.card V := by
  simp only [Fintype.card_option,Fintype.card_coe]
  have hh := Finset.card_add_card_compl A
  omega

lemma nontrivial_threeCut (h : ¬N.TrivialThreeCuts) :
    ∃ A : Finset V, (N.cut A).card = 3 ∧ 2 ≤ A.card ∧ 2 ≤ Aᶜ.card := by
  unfold TrivialThreeCuts at h
  push Not at h
  obtain ⟨A,hcut,ha,ho⟩ := h
  have he : (N.cut A).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨e,he⟩ := he
  have hh := (N.mem_cut A e).mp he
  have hi : A.Nonempty := hh.elim (fun h => ⟨_,h.1⟩) (fun h => ⟨_,h.1⟩)
  have hout : Aᶜ.Nonempty := hh.elim (fun h => ⟨_,Finset.mem_compl.mpr h.2⟩) (fun h => ⟨_,Finset.mem_compl.mpr h.2⟩)
  have hi' := Finset.card_pos.mpr hi
  have ho' := Finset.card_pos.mpr hout
  exact ⟨A,hcut,by omega,by omega⟩
end
end Barnette.Network
namespace Barnette.SimpleCycle
noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

lemma cycle_at_of_connected_two [DecidableEq V] (hc : G.Connected) (hd : G.IsRegularOfDegree 2) (v : V) :
    ∃ p : G.Walk v v, p.IsHamiltonianCycle := by
  have hi : G.IsCycles := by
    intro w _
    rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
    exact hd w
  have hn : (G.neighborSet v).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    have hh : (G.neighborSet v).ncard = 2 := by
      rw [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
      exact hd v
    omega
  obtain ⟨p,hp,hs⟩ := hi.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (c := G.connectedComponentMk v) rfl hn
  refine ⟨p,hp,hp.isPath_tail.isHamiltonian_of_mem ?_⟩
  intro w
  by_cases hw : w = v
  · subst w
    exact p.tail.end_mem_support
  · have hm : w ∈ p.support := by
      rw [← p.mem_verts_toSubgraph, hs]
      exact SimpleGraph.ConnectedComponent.eq.mpr (hc w v)
    rw [← p.cons_support_tail hp.not_nil] at hm
    exact (List.mem_cons.mp hm).resolve_left hw

omit [Fintype V] in
lemma induced_support_connected {a b : V} (p : G.Walk a b) (s : Set V)
    (hs : ∀ v, v ∈ s ↔ v ∈ p.support) : (G.induce s).Connected := by
  have hw : ∀ v ∈ p.support, v ∈ s := fun v hv => (hs v).mpr hv
  let q := p.induce s hw
  have hq (v : s) : v ∈ q.support := by
    simp only [q, SimpleGraph.Walk.support_induce, List.mem_attachWith]
    exact (hs v).mp v.property
  let : Nonempty s := ⟨⟨a,hw a p.start_mem_support⟩⟩
  exact ⟨fun x y => ((q.takeUntil x (hq x)).reverse.append (q.takeUntil y (hq y))).reachable⟩

lemma delete_vertex_connected (hc : G.Connected) (hd : G.IsRegularOfDegree 2) (v : V) :
    (G.induce {w | w ≠ v}).Connected := by
  obtain ⟨p,hp⟩ := cycle_at_of_connected_two G hc hd v
  have hn : ¬p.tail.Nil := by
    intro hh
    have hl := hp.isCycle.three_le_length
    have ht := SimpleGraph.Walk.length_eq_zero_iff.mpr hh
    simp only [SimpleGraph.Walk.length_tail] at ht
    omega
  have heq := p.tail.support_dropLast_concat hn
  have hnmem : v ∉ p.tail.dropLast.support := by
    have hnd := hp.isHamiltonian_tail.isPath.support_nodup
    rw [← heq] at hnd
    intro hm
    exact (List.nodup_append.mp hnd).2.2 v hm v (by simp) rfl
  apply induced_support_connected G p.tail.dropLast
  intro w
  constructor
  · intro hw
    have hm := hp.isHamiltonian_tail.mem_support w
    rw [←heq, List.mem_append, List.mem_singleton] at hm
    exact hm.resolve_right hw
  · intro hw h
    subst w
    exact hnmem hw
end
end Barnette.SimpleCycle

end OAI


namespace OAI

/-! Compatible boundary matchings and strong induction over three-edge cuts. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)
local instance (priority := high) capMatchingEq (A : Finset V) :
    DecidableEq (N.regionEdges A) := Classical.decEq _

omit [Fintype V] in
lemma restrict_star_image (S : Finset E) (v : V) :
    ((N.restrict (Subtype.val : S → E)).star v).image Subtype.val =
      (N.star v).filter (· ∈ S) := by
  ext e
  simp only [Finset.mem_image,Finset.mem_filter,mem_star]
  constructor
  · rintro ⟨k,hk,rfl⟩
    exact ⟨hk,k.property⟩
  · rintro ⟨he,hs⟩
    exact ⟨⟨e,hs⟩,he,rfl⟩

lemma matching_complement_two (hN : N.Simple) (hc : N.graph.IsRegularOfDegree 3)
    (P : Finset E) (hP : ∀ v, ((N.star v).filter (· ∈ P)).card = 1) :
    (N.restrict (Subtype.val : ↥Pᶜ → E)).graph.IsRegularOfDegree 2 := by
  intro v
  rw [← card_star _ (hN.restrict N _ Subtype.val_injective),
    ← Finset.card_image_of_injective _ Subtype.val_injective,N.restrict_star_image]
  have he := Finset.card_filter_add_card_filter_not (s := N.star v) (p := fun e => e ∈ P)
  rw [hP v,N.card_star hN,hc v] at he
  simpa only [Finset.mem_compl] using (show ((N.star v).filter (fun e => e ∉ P)).card = 2 by omega)

omit [Fintype V] in
lemma cap_matching_some (A : Finset V) (P : Finset (N.regionEdges A)) (v : A) :
    (((N.cap A).star (some v)).filter (· ∈ P)).image Subtype.val =
      (N.star v.val).filter (· ∈ P.image Subtype.val) := by
  rw [Finset.filter_mem_eq_inter,Finset.image_inter _ _ Subtype.val_injective,
    N.cap_star_some,Finset.filter_mem_eq_inter]

omit [Fintype V] in
lemma cap_matching_none (A : Finset V) (P : Finset (N.regionEdges A)) :
    (((N.cap A).star none).filter (· ∈ P)).image Subtype.val =
      (N.cut A).filter (· ∈ P.image Subtype.val) := by
  rw [Finset.filter_mem_eq_inter,Finset.image_inter _ _ Subtype.val_injective,
    N.cap_star_none,Finset.filter_mem_eq_inter]

omit [Fintype V] in
lemma cap_matching_boundary (A : Finset V) (P : Finset (N.regionEdges A))
    (hP : ∀ v, (((N.cap A).star v).filter (· ∈ P)).card = 1) :
    ∃ c : E, c ∈ N.cut A ∧ c ∈ P.image Subtype.val ∧
      ∀ e ∈ N.cut A, e ∈ P.image Subtype.val ↔ e = c := by
  have hh := hP none
  rw [← Finset.card_image_of_injective _ Subtype.val_injective,N.cap_matching_none] at hh
  obtain ⟨c,hc⟩ := Finset.card_eq_one.mp hh
  have hmem : c ∈ (N.cut A).filter (· ∈ P.image Subtype.val) := by rw [hc]; simp
  refine ⟨c,(Finset.mem_filter.mp hmem).1,(Finset.mem_filter.mp hmem).2,?_⟩
  intro e he
  have heq : e ∈ (N.cut A).filter (· ∈ P.image Subtype.val) ↔ e = c := by rw [hc]; simp
  simpa only [Finset.mem_filter,he,true_and] using heq

omit [Fintype V] in
lemma cap_image_subset (A : Finset V) (P : Finset (N.regionEdges A)) :
    P.image Subtype.val ⊆ N.regionEdges A := by
  rintro e he
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp he
  exact k.property

lemma region_pair_inter (A : Finset V) (e : E) :
    e ∈ N.regionEdges A → e ∈ N.regionEdges Aᶜ → e ∈ N.cut A := by
  simp only [mem_regionEdges,mem_cut,Finset.mem_compl]
  tauto

lemma cap_glue_agrees (A : Finset V) (P : Finset (N.regionEdges A))
    (Q : Finset (N.regionEdges Aᶜ))
    (hcut : ∀ e ∈ N.cut A, e ∈ P.image Subtype.val ↔ e ∈ Q.image Subtype.val)
    (e : E) (he : e ∈ N.regionEdges A) :
    e ∈ P.image Subtype.val ∪ Q.image Subtype.val ↔ e ∈ P.image Subtype.val := by
  rw [Finset.mem_union,or_iff_left_iff_imp]
  intro hq
  exact (hcut e (N.region_pair_inter A e he (N.cap_image_subset Aᶜ Q hq))).mpr hq

lemma cap_glue_agrees_right (A : Finset V) (P : Finset (N.regionEdges A))
    (Q : Finset (N.regionEdges Aᶜ))
    (hcut : ∀ e ∈ N.cut A, e ∈ P.image Subtype.val ↔ e ∈ Q.image Subtype.val)
    (e : E) (he : e ∈ N.regionEdges Aᶜ) :
    e ∈ P.image Subtype.val ∪ Q.image Subtype.val ↔ e ∈ Q.image Subtype.val := by
  rw [Finset.mem_union,or_iff_right_iff_imp]
  intro hp
  exact (hcut e (N.region_pair_inter A e (N.cap_image_subset A P hp) he)).mp hp

lemma cap_glue_matching (A : Finset V) (P : Finset (N.regionEdges A))
    (Q : Finset (N.regionEdges Aᶜ))
    (hP : ∀ v, (((N.cap A).star v).filter (· ∈ P)).card = 1)
    (hQ : ∀ v, (((N.cap Aᶜ).star v).filter (· ∈ Q)).card = 1)
    (hcut : ∀ e ∈ N.cut A, e ∈ P.image Subtype.val ↔ e ∈ Q.image Subtype.val) :
    ∀ v, ((N.star v).filter (· ∈ P.image Subtype.val ∪ Q.image Subtype.val)).card = 1 := by
  have side (B : Finset V) (P : Finset (N.regionEdges B)) (R : Finset E)
      (hP : ∀ v, (((N.cap B).star v).filter (· ∈ P)).card = 1)
      (hR : ∀ e ∈ N.regionEdges B, e ∈ R ↔ e ∈ P.image Subtype.val)
      (v : B) : ((N.star v.val).filter (· ∈ R)).card = 1 := by
    have heq : (N.star v.val).filter (· ∈ R) = (N.star v.val).filter (· ∈ P.image Subtype.val) := by
      apply Finset.filter_congr
      intro e he
      apply hR e
      rcases (N.mem_star e v.val).mp he with ht|hh
      · exact (N.mem_regionEdges B e).mpr (Or.inl (ht ▸ v.property))
      · exact (N.mem_regionEdges B e).mpr (Or.inr (hh ▸ v.property))
    rw [heq,← N.cap_matching_some B P v,Finset.card_image_of_injective _ Subtype.val_injective]
    exact hP (some v)
  intro v
  by_cases hv : v ∈ A
  · exact side A P _ hP (N.cap_glue_agrees A P Q hcut) ⟨v,hv⟩
  · exact side Aᶜ Q _ hQ (N.cap_glue_agrees_right A P Q hcut) ⟨v,Finset.mem_compl.mpr hv⟩
end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)
local instance (priority := high) capReachableEq (A : Finset V) :
    DecidableEq (N.regionEdges A) := Classical.decEq _

omit [Fintype V] in
lemma cap_complement_reachable (A : Finset V) (P : Finset (N.regionEdges A))
    (R : Finset E)
    (hc : ((N.cap A).restrict (Subtype.val : ↥Pᶜ → N.regionEdges A)).graph.Connected)
    (hd : ((N.cap A).restrict (Subtype.val : ↥Pᶜ → N.regionEdges A)).graph.IsRegularOfDegree 2)
    (hR : ∀ e ∈ N.regionEdges A, e ∈ R ↔ e ∈ P.image Subtype.val)
    (v w : A) : (N.restrict (Subtype.val : ↥Rᶜ → E)).graph.Reachable v.val w.val := by
  let C := ((N.cap A).restrict (Subtype.val : ↥Pᶜ → N.regionEdges A)).graph
  have hC : (C.induce {x | x ≠ none}).Connected :=
    Barnette.SimpleCycle.delete_vertex_connected C hc hd none
  let f : (C.induce {x | x ≠ none}) →g (N.restrict (Subtype.val : ↥Rᶜ → E)).graph := {
    toFun := fun x => (x.val.getD v).val
    map_rel' := by
      rintro ⟨x,hx⟩ ⟨y,hy⟩ hxy
      cases x with
      | none => exact (hx rfl).elim
      | some x =>
        cases y with
        | none => exact (hy rfl).elim
        | some y =>
          obtain ⟨hne,k,hk⟩ := hxy
          have hxy' : x.val ≠ y.val := by
            intro hh
            have hh' : x = y := Subtype.ext hh
            subst y
            exact hne rfl
          have hk' : (N.tail k.val.val = x.val ∧ N.head k.val.val = y.val) ∨
              (N.tail k.val.val = y.val ∧ N.head k.val.val = x.val) := by
            change (N.capMap A (N.tail k.val.val) = some x ∧ N.capMap A (N.head k.val.val) = some y) ∨
              (N.capMap A (N.tail k.val.val) = some y ∧ N.capMap A (N.head k.val.val) = some x) at hk
            simpa only [capMap_eq_some] using hk
          have hnot : k.val.val ∉ P.image Subtype.val := by
            intro hm
            obtain ⟨e,he,hee⟩ := Finset.mem_image.mp hm
            have hee' : e = k.val := Subtype.ext hee
            exact (Finset.mem_compl.mp k.property) (hee' ▸ he)
          have hkR : k.val.val ∈ Rᶜ :=
            Finset.mem_compl.mpr (hnot ∘ (hR k.val.val k.val.property).mp)
          exact ⟨hxy',⟨k.val.val,hkR⟩,hk'⟩ }
  exact (hC ⟨some v,by simp⟩ ⟨some w,by simp⟩).map f

lemma cap_glue_connected (hN : N.Simple) (hc : N.graph.IsRegularOfDegree 3)
    (h3 : N.ThreeEdgeConnected) (A : Finset V) (hA : (N.cut A).card = 3)
    (ha : 2 ≤ A.card) (ho : 2 ≤ Aᶜ.card)
    (P : Finset (N.regionEdges A)) (Q : Finset (N.regionEdges Aᶜ))
    (hP : ∀ v, (((N.cap A).star v).filter (· ∈ P)).card = 1)
    (hQ : ∀ v, (((N.cap Aᶜ).star v).filter (· ∈ Q)).card = 1)
    (hPc : ((N.cap A).restrict (Subtype.val : ↥Pᶜ → N.regionEdges A)).graph.Connected)
    (hQc : ((N.cap Aᶜ).restrict (Subtype.val : ↥Qᶜ → N.regionEdges Aᶜ)).graph.Connected)
    (hcut : ∀ e ∈ N.cut A, e ∈ P.image Subtype.val ↔ e ∈ Q.image Subtype.val) :
    (N.restrict (Subtype.val : ↥(P.image Subtype.val ∪ Q.image Subtype.val)ᶜ → E)).graph.Connected := by
  have ha' : A.Nonempty := Finset.card_pos.mp (by omega)
  have ho' : Aᶜ.Nonempty := Finset.card_pos.mp (by omega)
  have hc' : (N.cut Aᶜ).card = 3 := by simpa only [cut_compl] using hA
  have ha'' : (Aᶜ)ᶜ.Nonempty := by simpa only [compl_compl] using ha'
  have hmP := (N.cap A).matching_complement_two (N.cap_simple hN hc h3 A hA ha ho')
    (N.cap_cubic hN hc h3 A hA ha ho') P hP
  have hmQ := (N.cap Aᶜ).matching_complement_two (N.cap_simple hN hc h3 Aᶜ hc' ho ha'')
    (N.cap_cubic hN hc h3 Aᶜ hc' ho ha'') Q hQ
  let R := P.image Subtype.val ∪ Q.image Subtype.val
  let H := (N.restrict (Subtype.val : ↥Rᶜ → E)).graph
  have rA (v w : A) : H.Reachable v.val w.val :=
    N.cap_complement_reachable A P R hPc hmP (N.cap_glue_agrees A P Q hcut) v w
  have rB (v w : ↥(Aᶜ)) : H.Reachable v.val w.val :=
    N.cap_complement_reachable Aᶜ Q R hQc hmQ (N.cap_glue_agrees_right A P Q hcut) v w
  obtain ⟨c,hcA,hcP,hcuniq⟩ := N.cap_matching_boundary A P hP
  have hdex : ((N.cut A).erase c).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hcA,hA]
    decide
  obtain ⟨d,hd⟩ := hdex
  obtain ⟨hdc,hdA⟩ := Finset.mem_erase.mp hd
  have hdP : d ∉ P.image Subtype.val := fun hh => hdc ((hcuniq d hdA).mp hh)
  have hdr : d ∈ N.regionEdges A := by
    have hh := (N.mem_cut A d).mp hdA
    exact (N.mem_regionEdges A d).mpr (hh.elim (Or.inl ∘ And.left) (Or.inr ∘ And.left))
  have hdR : d ∈ Rᶜ := Finset.mem_compl.mpr
    (hdP ∘ (N.cap_glue_agrees A P Q hcut d hdr).mp)
  have adj : H.Adj (N.tail d) (N.head d) := ⟨hN.loopless d,⟨d,hdR⟩,Or.inl ⟨rfl,rfl⟩⟩
  have cross (x y : V) (hx : x ∈ A) (hy : y ∉ A) (hxy : H.Adj x y) : H.Connected := by
    apply (SimpleGraph.connected_iff_exists_forall_reachable H).mpr
    refine ⟨x,?_⟩
    intro z
    by_cases hz : z ∈ A
    · exact rA ⟨x,hx⟩ ⟨z,hz⟩
    · exact hxy.reachable.trans (rB ⟨y,Finset.mem_compl.mpr hy⟩ ⟨z,Finset.mem_compl.mpr hz⟩)
  rcases (N.mem_cut A d).mp hdA with ⟨ht,hh⟩|⟨hh,ht⟩
  · exact cross _ _ ht hh adj
  · exact cross _ _ hh ht adj.symm
end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
universe uV uE uF
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] (N : Network V E)
local instance (priority := high) unrestrictedInductionEq (A : Finset V) :
    DecidableEq (N.regionEdges A) := Classical.decEq _

omit [Fintype V] in
lemma cap_matching_boundary_at (A : Finset V) (P : Finset (N.regionEdges A))
    (hP : ∀ v, (((N.cap A).star v).filter (· ∈ P)).card = 1)
    (c : E) (hc : c ∈ N.cut A) (hm : c ∈ P.image Subtype.val) :
    ∀ e ∈ N.cut A, e ∈ P.image Subtype.val ↔ e = c := by
  obtain ⟨d,_,_,hd⟩ := N.cap_matching_boundary A P hP
  have hh : c = d := (hd c hc).mp hm
  subst d
  exact hd

lemma nontrivial_threeCut_at (h : ¬N.TrivialThreeCuts) (e : E) :
    ∃ A : Finset V, (N.cut A).card = 3 ∧ 2 ≤ A.card ∧ 2 ≤ Aᶜ.card ∧ e ∈ N.regionEdges A := by
  obtain ⟨A,hA,ha,ho⟩ := N.nontrivial_threeCut h
  by_cases he : e ∈ N.regionEdges A
  · exact ⟨A,hA,ha,ho,he⟩
  · have ht : N.tail e ∉ A := fun hh => he ((N.mem_regionEdges A e).mpr (Or.inl hh))
    refine ⟨Aᶜ,by simpa only [cut_compl] using hA,ho,by simpa only [compl_compl] using ha,?_⟩
    exact (N.mem_regionEdges Aᶜ e).mpr (Or.inl (Finset.mem_compl.mpr ht))

private theorem matching_strong (n : ℕ) :
    ∀ {V : Type uV} {E : Type uE} {F : Type uF} [Fintype V] [Fintype E] [Fintype F]
      (N : Network V E) (D : Network F E), Fintype.card V = n →
      N.Duality D → N.Simple → N.graph.IsRegularOfDegree 3 → N.ThreeEdgeConnected →
      ∀ (black : V → Prop), (∀ e, black (N.tail e) ↔ ¬black (N.head e)) →
      ∀ e : E, ∃ P : Finset E, e ∈ P ∧ (∀ v, ((N.star v).filter (· ∈ P)).card = 1) ∧
        (N.restrict (Subtype.val : ↥Pᶜ → E)).graph.Connected := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V E F _ _ _ N D hn h hN hc h3 black hb e
    by_cases ht : N.TrivialThreeCuts
    · obtain ⟨M⟩ := N.make_coloredDual D h hN h3 hc black hb
      exact N.irreducible_matching D M h3 ht e
    · obtain ⟨A,hA,ha,ho,he⟩ := N.nontrivial_threeCut_at ht e
      have ha' : A.Nonempty := Finset.card_pos.mp (by omega)
      have ho' : Aᶜ.Nonempty := Finset.card_pos.mp (by omega)
      have hc' : (N.cut Aᶜ).card = 3 := by simpa only [cut_compl] using hA
      have ha'' : (Aᶜ)ᶜ.Nonempty := by simpa only [compl_compl] using ha'
      obtain ⟨F₁,f₁,D₁,h₁⟩ := N.cap_duality D h hN h3 A hA ha' ho'
      let : Fintype F₁ := f₁
      have hlt₁ : Fintype.card (Option A) < n := hn ▸ cap_card_lt A ho
      obtain ⟨P,heP,hP,hPc⟩ := ih _ hlt₁ (N.cap A) D₁ rfl h₁
        (N.cap_simple hN hc h3 A hA ha ho') (N.cap_cubic hN hc h3 A hA ha ho')
        (N.cap_threeConnected h3 A ho') (N.capBlack black A)
        (N.cap_coloring hN hc black hb A hA) ⟨e,he⟩
      obtain ⟨c,hca,hcp,hcu⟩ := N.cap_matching_boundary A P hP
      have hcb : c ∈ N.cut Aᶜ := by simpa only [cut_compl] using hca
      have hcr : c ∈ N.regionEdges Aᶜ := by
        have hh := (N.mem_cut Aᶜ c).mp hcb
        exact (N.mem_regionEdges Aᶜ c).mpr (hh.elim (Or.inl ∘ And.left) (Or.inr ∘ And.left))
      obtain ⟨F₂,f₂,D₂,h₂⟩ := N.cap_duality D h hN h3 Aᶜ hc' ho' ha''
      let : Fintype F₂ := f₂
      have hlt₂ : Fintype.card (Option ↥(Aᶜ)) < n := by
        rw [← hn]
        exact cap_card_lt Aᶜ (by simpa only [compl_compl] using ha)
      obtain ⟨Q,hcQ,hQ,hQc⟩ := ih _ hlt₂ (N.cap Aᶜ) D₂ rfl h₂
        (N.cap_simple hN hc h3 Aᶜ hc' ho ha'') (N.cap_cubic hN hc h3 Aᶜ hc' ho ha'')
        (N.cap_threeConnected h3 Aᶜ ha'') (N.capBlack black Aᶜ)
        (N.cap_coloring hN hc black hb Aᶜ hc') ⟨c,hcr⟩
      have hcQ' : c ∈ Q.image Subtype.val := Finset.mem_image.mpr ⟨⟨c,hcr⟩,hcQ,rfl⟩
      have hqcut : ∀ d ∈ N.cut A, d ∈ Q.image Subtype.val ↔ d = c := by
        simpa only [cut_compl] using N.cap_matching_boundary_at Aᶜ Q hQ c hcb hcQ'
      have hcut : ∀ d ∈ N.cut A, d ∈ P.image Subtype.val ↔ d ∈ Q.image Subtype.val :=
        fun d hd => (hcu d hd).trans (hqcut d hd).symm
      refine ⟨P.image Subtype.val ∪ Q.image Subtype.val,?_,N.cap_glue_matching A P Q hP hQ hcut,?_⟩
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨e,he⟩,heP,rfl⟩)
      · exact N.cap_glue_connected hN hc h3 A hA ha ho P Q hP hQ hPc hQc hcut

variable {F : Type uF} [Fintype F] (D : Network F E)

theorem Duality.connected_complement_matching (h : N.Duality D) (hN : N.Simple)
    (hc : N.graph.IsRegularOfDegree 3) (h3 : N.ThreeEdgeConnected)
    (black : V → Prop) (hb : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) (e : E) :
    ∃ P : Finset E, e ∈ P ∧ (∀ v, ((N.star v).filter (· ∈ P)).card = 1) ∧
      (N.restrict (Subtype.val : ↥Pᶜ → E)).graph.Connected :=
  matching_strong (Fintype.card V) N D rfl h hN hc h3 black hb e
end
end Barnette.Network

end OAI


namespace OAI

/-! Compact connected arc traces and uniform positive thickenings. -/

namespace Barnette.PlaneEmbedding

noncomputable section

variable {V : Type*} {G : SimpleGraph V} (E : PlaneEmbedding G)

def curve (d : G.Dart) : Path (E.point d.fst) (E.point d.snd) :=
  E.arc d.fst d.snd d.adj

@[simp] theorem curve_zero (d : G.Dart) : E.curve d 0 = E.point d.fst :=
  (E.curve d).source

@[simp] theorem curve_one (d : G.Dart) : E.curve d 1 = E.point d.snd :=
  (E.curve d).target

theorem curve_injective (d : G.Dart) : Function.Injective (E.curve d) :=
  E.arc_injective d.fst d.snd d.adj

theorem curve_symm (d : G.Dart) (t : unitInterval) :
    E.curve d.symm t = E.curve d (unitInterval.symm t) := by
  change E.arc d.snd d.fst d.adj.symm t = _
  rw [E.arc_reverse]
  rfl

theorem curve_eq_point_iff (d : G.Dart) (t : unitInterval) (v : V) :
    E.curve d t = E.point v ↔ (t = 0 ∧ v = d.fst) ∨ (t = 1 ∧ v = d.snd) := by
  constructor
  · exact E.arc_avoids_vertices d.fst d.snd d.adj t v
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

theorem curve_eq_curve_interior {d e : G.Dart} {t s : unitInterval}
    (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) (hs₀ : s ≠ 0) (hs₁ : s ≠ 1)
    (h : E.curve d t = E.curve e s) : d = e ∨ d = e.symm := by
  rcases E.interiors_disjoint d.fst d.snd e.fst e.snd d.adj e.adj
    t s ht₀ ht₁ hs₀ hs₁ h with h | h
  · exact Or.inl (SimpleGraph.Dart.ext _ _ (Prod.ext h.1 h.2))
  · exact Or.inr (SimpleGraph.Dart.ext _ _ (Prod.ext h.1 h.2))

private def third : unitInterval := ⟨1 / 3, by norm_num⟩
private def twoThirds : unitInterval := ⟨2 / 3, by norm_num⟩

def trace (d : G.Dart) (a b : unitInterval) : Set (ℝ × ℝ) :=
  (E.curve d) '' Set.Icc a b

theorem trace_compact (d : G.Dart) (a b : unitInterval) :
    IsCompact (E.trace d a b) :=
  isCompact_Icc.image (E.curve d).continuous

theorem trace_preconnected (d : G.Dart) (a b : unitInterval) :
    IsPreconnected (E.trace d a b) :=
  isPreconnected_Icc.image _ (E.curve d).continuous.continuousOn

def branch (v : V) : Set (ℝ × ℝ) :=
  {E.point v} ∪ ⋃ d : {d : G.Dart // d.fst = v}, E.trace d.val 0 third

def core (d : G.Dart) : Set (ℝ × ℝ) := E.trace d third twoThirds

theorem branch_point (v : V) : E.point v ∈ E.branch v :=
  Or.inl rfl

theorem branch_compact [Finite V] (v : V) : IsCompact (E.branch v) := by
  classical
  have : Finite G.Dart := Finite.of_injective SimpleGraph.Dart.toProd
    SimpleGraph.Dart.toProd_injective
  exact isCompact_singleton.union (isCompact_iUnion fun d => E.trace_compact d.val 0 third)

theorem core_compact (d : G.Dart) : IsCompact (E.core d) := E.trace_compact _ _ _

theorem core_preconnected (d : G.Dart) : IsPreconnected (E.core d) :=
  E.trace_preconnected _ _ _

private theorem initial_meeting {d e : G.Dart} {t s : unitInterval}
    (ht : (t : ℝ) ≤ 1 / 3) (hs : (s : ℝ) ≤ 1 / 3)
    (h : E.curve d t = E.curve e s) : d.fst = e.fst := by
  have ht₁ : t ≠ 1 := by intro heq; subst t; norm_num at ht
  have hs₁ : s ≠ 1 := by intro heq; subst s; norm_num at hs
  by_cases ht₀ : t = 0
  · subst t
    rw [E.curve_zero] at h
    rcases (E.curve_eq_point_iff e s d.fst).mp h.symm with h | h
    · exact h.2
    · exact (hs₁ h.1).elim
  by_cases hs₀ : s = 0
  · subst s
    rw [E.curve_zero] at h
    rcases (E.curve_eq_point_iff d t e.fst).mp h with h | h
    · exact h.2.symm
    · exact (ht₁ h.1).elim
  rcases E.curve_eq_curve_interior ht₀ ht₁ hs₀ hs₁ h with heq | heq
  · exact congrArg (fun d : G.Dart => d.fst) heq
  · subst d
    rw [E.curve_symm] at h
    have hp := congrArg Subtype.val (E.curve_injective e h)
    simp only [unitInterval.coe_symm_eq] at hp
    linarith

theorem branch_disjoint {v w : V} (hvw : v ≠ w) :
    Disjoint (E.branch v) (E.branch w) := by
  rw [Set.disjoint_left]
  intro p hp hq
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact hvw (E.point_injective (hp.symm.trans hq))
  · obtain ⟨⟨d, hd⟩, t, ht, heq⟩ := Set.mem_iUnion.mp hq
    have ha : E.curve d t = E.point v := heq.trans hp
    rcases (E.curve_eq_point_iff d t v).mp ha with ha | ha
    · exact hvw (ha.2.trans hd)
    · have : (1 : unitInterval) ≤ third := ha.1 ▸ ht.2
      change (1 : ℝ) ≤ 1 / 3 at this
      norm_num at this
  · obtain ⟨⟨d, hd⟩, t, ht, heq⟩ := Set.mem_iUnion.mp hp
    have ha : E.curve d t = E.point w := heq.trans hq
    rcases (E.curve_eq_point_iff d t w).mp ha with ha | ha
    · exact hvw (hd.symm.trans ha.2.symm)
    · have : (1 : unitInterval) ≤ third := ha.1 ▸ ht.2
      change (1 : ℝ) ≤ 1 / 3 at this
      norm_num at this
  · obtain ⟨⟨d, hd⟩, t, ht, heq⟩ := Set.mem_iUnion.mp hp
    obtain ⟨⟨e, he⟩, s, hs, heq'⟩ := Set.mem_iUnion.mp hq
    exact hvw (hd.symm.trans ((E.initial_meeting ht.2 hs.2 (heq.trans heq'.symm)).trans he))

private theorem middle_nonendpoint {t : unitInterval} (ht : t ∈ Set.Icc third twoThirds) :
    t ≠ 0 ∧ t ≠ 1 := by
  constructor
  · intro h
    have hh : (1 : ℝ) / 3 ≤ t := ht.1
    rw [h] at hh
    norm_num at hh
  · intro h
    have hh : (t : ℝ) ≤ 2 / 3 := ht.2
    rw [h] at hh
    norm_num at hh

theorem core_avoids_vertices (d : G.Dart) (v : V) : E.point v ∉ E.core d := by
  rintro ⟨t, ht, heq⟩
  have hn := middle_nonendpoint ht
  rcases (E.curve_eq_point_iff d t v).mp heq with h | h
  · exact hn.1 h.1
  · exact hn.2 h.1

theorem core_disjoint {d e : G.Dart} (hde : d.edge ≠ e.edge) :
    Disjoint (E.core d) (E.core e) := by
  rw [Set.disjoint_left]
  rintro p ⟨t, ht, heq⟩ ⟨s, hs, heq'⟩
  obtain ⟨ht₀, ht₁⟩ := middle_nonendpoint ht
  obtain ⟨hs₀, hs₁⟩ := middle_nonendpoint hs
  rcases E.curve_eq_curve_interior ht₀ ht₁ hs₀ hs₁ (heq.trans heq'.symm) with h | h
  · exact hde (congrArg SimpleGraph.Dart.edge h)
  · exact hde ((congrArg SimpleGraph.Dart.edge h).trans e.edge_symm)

theorem branch_core_disjoint {v : V} {e : G.Dart}
    (hv₁ : v ≠ e.fst) (hv₂ : v ≠ e.snd) : Disjoint (E.branch v) (E.core e) := by
  rw [Set.disjoint_left]
  intro p hp hq
  rcases hp with hp | hp
  · exact E.core_avoids_vertices e v (hp ▸ hq)
  obtain ⟨⟨d, hd⟩, t, ht, heq⟩ := Set.mem_iUnion.mp hp
  obtain ⟨s, hs, heq'⟩ := hq
  have h : E.curve d t = E.curve e s := heq.trans heq'.symm
  obtain ⟨hs₀, hs₁⟩ := middle_nonendpoint hs
  have ht₁ : t ≠ 1 := by
    intro heq
    have hh : (t : ℝ) ≤ 1 / 3 := ht.2
    rw [heq] at hh
    norm_num at hh
  by_cases ht₀ : t = 0
  · subst t
    rw [E.curve_zero] at h
    rcases (E.curve_eq_point_iff e s d.fst).mp h.symm with h | h
    · exact hs₀ h.1
    · exact hs₁ h.1
  rcases E.curve_eq_curve_interior ht₀ ht₁ hs₀ hs₁ h with h | h
  · exact hv₁ (hd.symm.trans (congrArg (fun d : G.Dart => d.fst) h))
  · exact hv₂ (hd.symm.trans (congrArg (fun d : G.Dart => d.fst) h))

theorem branch_preconnected (v : V) : IsPreconnected (E.branch v) := by
  apply isPreconnected_of_forall (E.point v)
  intro y hy
  rcases hy with hy | hy
  · exact ⟨{E.point v}, Set.subset_union_left, rfl, hy, isPreconnected_singleton⟩
  · obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hy
    refine ⟨E.trace d.val 0 third, ?_, ?_, hd, E.trace_preconnected _ _ _⟩
    · exact fun x hx => Or.inr (Set.mem_iUnion.mpr ⟨d, hx⟩)
    · refine ⟨0, ⟨le_rfl, ?_⟩, ?_⟩
      · change (0 : ℝ) ≤ 1 / 3
        norm_num
      · simpa only [E.curve_zero] using congrArg E.point d.property

theorem branch_connected (v : V) : IsConnected (E.branch v) :=
  ⟨⟨_, E.branch_point v⟩, E.branch_preconnected v⟩

private theorem third_le_twoThirds : third ≤ twoThirds := by
  change (1 : ℝ) / 3 ≤ 2 / 3
  norm_num

private theorem symm_third : unitInterval.symm third = twoThirds := by
  apply Subtype.ext
  change 1 - (1 : ℝ) / 3 = 2 / 3
  norm_num

theorem core_connected (d : G.Dart) : IsConnected (E.core d) :=
  ⟨⟨E.curve d third, third, ⟨le_rfl, third_le_twoThirds⟩, rfl⟩,
    E.core_preconnected d⟩

theorem branch_core_meets (d : G.Dart) :
    (E.branch d.fst ∩ E.core d).Nonempty ∧ (E.branch d.snd ∩ E.core d).Nonempty := by
  constructor
  · refine ⟨E.curve d third, ?_, third, ⟨le_rfl, third_le_twoThirds⟩, rfl⟩
    refine Or.inr (Set.mem_iUnion.mpr ⟨⟨d, rfl⟩, third, ⟨?_, le_rfl⟩, rfl⟩)
    change (0 : ℝ) ≤ 1 / 3
    norm_num
  · refine ⟨E.curve d twoThirds, ?_, twoThirds, ⟨third_le_twoThirds, le_rfl⟩, rfl⟩
    refine Or.inr (Set.mem_iUnion.mpr ⟨⟨d.symm, rfl⟩, third, ⟨?_, le_rfl⟩, ?_⟩)
    · change (0 : ℝ) ≤ 1 / 3
      norm_num
    · rw [E.curve_symm, symm_third]

theorem finite_positive_radius {ι : Type*} [Finite ι] (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) : ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ r i := by
  classical
  let _ := Fintype.ofFinite ι
  have aux (s : Finset ι) : ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, δ ≤ r i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert a s ha ih =>
      obtain ⟨δ, hδ, h⟩ := ih
      refine ⟨min δ (r a), lt_min hδ (hr a), ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (h i hi)
  obtain ⟨δ, hδ, h⟩ := aux Finset.univ
  exact ⟨δ, hδ, fun i => h i (Finset.mem_univ i)⟩

theorem uniform_thickening {ι : Type*} [Finite ι] (K : ι → Set (ℝ × ℝ))
    (hK : ∀ i, IsCompact (K i)) (R : ι → ι → Prop)
    (hR : ∀ i j, R i j → Disjoint (K i) (K j)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i j, R i j →
      Disjoint (Metric.thickening δ (K i)) (Metric.thickening δ (K j)) := by
  classical
  let I := {p : ι × ι // R p.1 p.2}
  have hex (p : I) : ∃ δ : ℝ, 0 < δ ∧
      Disjoint (Metric.thickening δ (K p.val.1)) (Metric.thickening δ (K p.val.2)) :=
    (hR _ _ p.property).exists_thickenings (hK _) (hK _).isClosed
  choose r hr hd using hex
  obtain ⟨δ, hδ, hle⟩ := finite_positive_radius r hr
  refine ⟨δ, hδ, ?_⟩
  intro i j hij
  let p : I := ⟨(i, j), hij⟩
  exact (hd p).mono (Metric.thickening_mono (hle p) _) (Metric.thickening_mono (hle p) _)

end
end Barnette.PlaneEmbedding

end OAI


namespace OAI

/-! Ordinary square cells and connected finite lattice corridors. -/

namespace Barnette.SquareGrid

noncomputable section

def graph : SimpleGraph (ℤ × ℤ) where
  Adj a b := ((a.1 + 1 = b.1 ∨ b.1 + 1 = a.1) ∧ a.2 = b.2) ∨
    ((a.2 + 1 = b.2 ∨ b.2 + 1 = a.2) ∧ a.1 = b.1)
  symm := ⟨by
    intro a b h
    rcases h with ⟨h, he⟩ | ⟨h, he⟩
    · exact Or.inl ⟨h.symm, he.symm⟩
    · exact Or.inr ⟨h.symm, he.symm⟩⟩
  loopless := ⟨by intro a h; rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> omega⟩

def cell (δ : ℝ) (z : ℤ × ℤ) : Set (ℝ × ℝ) :=
  Set.Icc (δ * z.1) (δ * ((z.1 : ℝ) + 1)) ×ˢ
    Set.Icc (δ * z.2) (δ * ((z.2 : ℝ) + 1))

def cells (δ : ℝ) (K : Set (ℝ × ℝ)) : Set (ℤ × ℤ) :=
  {z | (cell δ z ∩ K).Nonempty}

theorem cell_closed (δ : ℝ) (z : ℤ × ℤ) : IsClosed (cell δ z) :=
  isClosed_Icc.prod isClosed_Icc

theorem cell_compact (δ : ℝ) (z : ℤ × ℤ) : IsCompact (cell δ z) :=
  isCompact_Icc.prod isCompact_Icc

theorem cell_cover {δ : ℝ} (hδ : 0 < δ) (p : ℝ × ℝ) : ∃ z, p ∈ cell δ z := by
  refine ⟨(⌊p.1 / δ⌋, ⌊p.2 / δ⌋), ?_⟩
  constructor
  · constructor
    · have h := (le_div_iff₀ hδ).mp (Int.floor_le (p.1 / δ))
      simpa only [mul_comm] using h
    · have h := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (p.1 / δ))
      exact le_of_lt (by simpa only [mul_comm] using h)
  · constructor
    · have h := (le_div_iff₀ hδ).mp (Int.floor_le (p.2 / δ))
      simpa only [mul_comm] using h
    · have h := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (p.2 / δ))
      exact le_of_lt (by simpa only [mul_comm] using h)

theorem subset_union_cells {δ : ℝ} (hδ : 0 < δ) (K : Set (ℝ × ℝ)) :
    K ⊆ ⋃ z : cells δ K, cell δ z.val := by
  intro p hp
  obtain ⟨z, hz⟩ := cell_cover hδ p
  exact Set.mem_iUnion.mpr ⟨⟨z, p, hz, hp⟩, hz⟩

private theorem int_bound_of_cell {δ R : ℝ} (hδ : 0 < δ) {a : ℤ} {x : ℝ}
    (hx : -R ≤ x ∧ x ≤ R) (ha : δ * a ≤ x ∧ x ≤ δ * ((a : ℝ) + 1)) :
    -(R / δ + 1) ≤ (a : ℝ) ∧ (a : ℝ) ≤ R / δ + 1 := by
  have hu : (a : ℝ) ≤ R / δ :=
    (le_div_iff₀ hδ).mpr (by nlinarith [ha.1, hx.2])
  have hl : -R / δ ≤ (a : ℝ) + 1 :=
    (div_le_iff₀ hδ).mpr (by nlinarith [ha.2, hx.1])
  rw [neg_div] at hl
  constructor <;> linarith

theorem cells_finite {δ : ℝ} (hδ : 0 < δ) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) : (cells δ K).Finite := by
  obtain ⟨R, _, hR⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨N, hN⟩ := exists_int_ge (R / δ + 1)
  apply ((Set.finite_Icc (-N) N).prod (Set.finite_Icc (-N) N)).subset
  rintro z ⟨p, hp, hpK⟩
  have hp₁ : -R ≤ p.1 ∧ p.1 ≤ R := abs_le.mp ((norm_fst_le p).trans (hR p hpK))
  have hp₂ : -R ≤ p.2 ∧ p.2 ≤ R := abs_le.mp ((norm_snd_le p).trans (hR p hpK))
  obtain ⟨hz₁, hz₁'⟩ := int_bound_of_cell hδ hp₁ hp.1
  obtain ⟨hz₂, hz₂'⟩ := int_bound_of_cell hδ hp₂ hp.2
  have hb₁ : (-(N : ℝ)) ≤ z.1 ∧ (z.1 : ℝ) ≤ N := by constructor <;> linarith
  have hb₂ : (-(N : ℝ)) ≤ z.2 ∧ (z.2 : ℝ) ≤ N := by constructor <;> linarith
  exact ⟨⟨by exact_mod_cast hb₁.1, by exact_mod_cast hb₁.2⟩,
    ⟨by exact_mod_cast hb₂.1, by exact_mod_cast hb₂.2⟩⟩

theorem dist_le_of_mem_cell {δ : ℝ} {z : ℤ × ℤ} {p q : ℝ × ℝ}
    (hp : p ∈ cell δ z) (hq : q ∈ cell δ z) : dist p q ≤ δ := by
  rw [Prod.dist_eq, max_le_iff, Real.dist_eq, Real.dist_eq]
  constructor <;> rw [abs_le] <;> constructor <;>
    nlinarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2, hq.1.1, hq.1.2, hq.2.1, hq.2.2]

theorem cell_subset_thickening {δ ε : ℝ} (hδε : δ < ε) {K : Set (ℝ × ℝ)}
    {z : ℤ × ℤ} (hz : z ∈ cells δ K) : cell δ z ⊆ Metric.thickening ε K := by
  obtain ⟨q, hq, hqK⟩ := hz
  intro p hp
  exact Metric.mem_thickening_iff.mpr ⟨q, hqK, (dist_le_of_mem_cell hp hq).trans_lt hδε⟩

theorem cells_disjoint {δ ε : ℝ} (hδε : δ < ε)
    {K L : Set (ℝ × ℝ)}
    (hKL : Disjoint (Metric.thickening ε K) (Metric.thickening ε L)) :
    Disjoint (cells δ K) (cells δ L) := by
  rw [Set.disjoint_left] at hKL ⊢
  intro z hz hz'
  have hzp := hz
  obtain ⟨p, hp, _⟩ := hzp
  exact hKL (cell_subset_thickening hδε hz hp) (cell_subset_thickening hδε hz' hp)

end
end Barnette.SquareGrid
namespace Barnette.SquareGrid

noncomputable section

theorem finite_closed_cover_preconnected {ι α : Type*} [Finite ι] [TopologicalSpace α]
    (H : SimpleGraph ι) (K : Set α) (C : ι → Set α)
    (hK : IsPreconnected K) (hC : ∀ i, IsClosed (C i))
    (hcover : K ⊆ ⋃ i, C i) (hne : ∀ i, (K ∩ C i).Nonempty)
    (hjoin : ∀ p ∈ K, ∀ i j, p ∈ C i → p ∈ C j → H.Reachable i j) :
    H.Preconnected := by
  classical
  intro a b
  by_contra hab
  let U : Set α := ⋃ i : {i // H.Reachable a i}, C i.val
  let W : Set α := ⋃ i : {i // ¬H.Reachable a i}, C i.val
  have hU : IsClosed U := isClosed_iUnion_of_finite (fun i => hC i.val)
  have hW : IsClosed W := isClosed_iUnion_of_finite (fun i => hC i.val)
  have hUW : K ⊆ U ∪ W := by
    intro p hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hp)
    by_cases hai : H.Reachable a i
    · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨i, hai⟩, hi⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨i, hai⟩, hi⟩)
  have haU : (K ∩ U).Nonempty := by
    obtain ⟨p, hpK, hpa⟩ := hne a
    exact ⟨p, hpK, Set.mem_iUnion.mpr ⟨⟨a, .rfl⟩, hpa⟩⟩
  have hbW : (K ∩ W).Nonempty := by
    obtain ⟨p, hpK, hpb⟩ := hne b
    exact ⟨p, hpK, Set.mem_iUnion.mpr ⟨⟨b, hab⟩, hpb⟩⟩
  obtain ⟨p, hpK, hpU, hpW⟩ :=
    isPreconnected_closed_iff.mp hK U W hU hW hUW haU hbW
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpU
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hpW
  exact j.property (i.property.trans (hjoin p hpK i.val j.val hi hj))

private theorem coordinates_close {δ : ℝ} (hδ : 0 < δ) {a b : ℤ} {p : ℝ}
    (ha : δ * a ≤ p ∧ p ≤ δ * ((a : ℝ) + 1))
    (hb : δ * b ≤ p ∧ p ≤ δ * ((b : ℝ) + 1)) :
    a ≤ b + 1 ∧ b ≤ a + 1 := by
  have hab : (a : ℝ) ≤ (b : ℝ) + 1 := (mul_le_mul_iff_right₀ hδ).mp (ha.1.trans hb.2)
  have hba : (b : ℝ) ≤ (a : ℝ) + 1 := (mul_le_mul_iff_right₀ hδ).mp (hb.1.trans ha.2)
  exact ⟨by exact_mod_cast hab, by exact_mod_cast hba⟩

theorem reachable_of_common_point {δ : ℝ} (hδ : 0 < δ) {K : Set (ℝ × ℝ)}
    {p : ℝ × ℝ} (hp : p ∈ K) (a b : cells δ K)
    (ha : p ∈ cell δ a.val) (hb : p ∈ cell δ b.val) :
    (graph.induce (cells δ K)).Reachable a b := by
  obtain ⟨hx, hx'⟩ := coordinates_close hδ ha.1 hb.1
  obtain ⟨hy, hy'⟩ := coordinates_close hδ ha.2 hb.2
  let c : cells δ K := ⟨(b.val.1, a.val.2), p, ⟨hb.1, ha.2⟩, hp⟩
  have hac : (graph.induce (cells δ K)).Reachable a c := by
    by_cases h : a.val.1 = b.val.1
    · have heq : a = c := Subtype.ext (Prod.ext h rfl)
      rw [← heq]
    · apply SimpleGraph.Adj.reachable
      change graph.Adj a.val c.val
      exact Or.inl ⟨by dsimp [c]; omega, rfl⟩
  have hcb : (graph.induce (cells δ K)).Reachable c b := by
    by_cases h : a.val.2 = b.val.2
    · have heq : c = b := Subtype.ext (Prod.ext rfl h)
      rw [heq]
    · apply SimpleGraph.Adj.reachable
      change graph.Adj c.val b.val
      exact Or.inr ⟨by dsimp [c]; omega, rfl⟩
  exact hac.trans hcb

theorem cells_connected {δ : ℝ} (hδ : 0 < δ) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hc : IsConnected K) :
    (graph.induce (cells δ K)).Connected := by
  classical
  let _ : Fintype (cells δ K) := (cells_finite hδ hK).fintype
  have hone : Nonempty (cells δ K) := by
    obtain ⟨p, hp⟩ := hc.nonempty
    obtain ⟨z, hz⟩ := cell_cover hδ p
    exact ⟨⟨z, p, hz, hp⟩⟩
  refine ⟨finite_closed_cover_preconnected _ K (fun z : cells δ K => cell δ z.val)
    hc.isPreconnected (fun z => cell_closed _ _) (subset_union_cells hδ K) ?_ ?_⟩
  · intro z
    obtain ⟨p, hp, hpK⟩ := z.property
    exact ⟨p, hpK, hp⟩
  · intro p hp a b ha hb
    exact reachable_of_common_point hδ hp a b ha hb

end
end Barnette.SquareGrid

end OAI


namespace OAI

/-! Disjoint lattice corridors obtained from a crossing-free plane embedding. -/

namespace Barnette

structure CorridorModel {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) where
  branch : V → Set W
  corridor : G.Dart → Set W
  branch_finite : ∀ v, (branch v).Finite
  corridor_finite : ∀ d, (corridor d).Finite
  branch_connected : ∀ v, (H.induce (branch v)).Connected
  corridor_connected : ∀ d, (H.induce (corridor d)).Connected
  branches_disjoint : ∀ v w, v ≠ w → Disjoint (branch v) (branch w)
  corridors_disjoint : ∀ d e, d.edge ≠ e.edge → Disjoint (corridor d) (corridor e)
  nonincident_disjoint : ∀ v d, v ≠ d.fst → v ≠ d.snd →
    Disjoint (branch v) (corridor d)
  incident_meets : ∀ d, (branch d.fst ∩ corridor d).Nonempty ∧
    (branch d.snd ∩ corridor d).Nonempty

namespace PlaneEmbedding

noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj] (E : PlaneEmbedding G)

private def allSets : V ⊕ G.Dart → Set (ℝ × ℝ)
  | .inl v => E.branch v
  | .inr d => E.core d

private def apart : V ⊕ G.Dart → V ⊕ G.Dart → Prop
  | .inl v, .inl w => v ≠ w
  | .inl v, .inr d => v ≠ d.fst ∧ v ≠ d.snd
  | .inr d, .inl v => v ≠ d.fst ∧ v ≠ d.snd
  | .inr d, .inr e => d.edge ≠ e.edge

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem allSets_compact (i : V ⊕ G.Dart) : IsCompact (E.allSets i) := by
  cases i with
  | inl v => exact E.branch_compact v
  | inr d => exact E.core_compact d

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem allSets_disjoint (i j : V ⊕ G.Dart) (h : apart i j) :
    Disjoint (E.allSets i) (E.allSets j) := by
  cases i with
  | inl v =>
    cases j with
    | inl w => exact E.branch_disjoint h
    | inr d => exact E.branch_core_disjoint h.1 h.2
  | inr d =>
    cases j with
    | inl v => exact (E.branch_core_disjoint h.1 h.2).symm
    | inr e => exact E.core_disjoint h

omit [DecidableEq V] in
include E in

theorem exists_lattice_corridor_model : Nonempty (CorridorModel G SquareGrid.graph) := by
  classical
  obtain ⟨ε, hε, hsep⟩ := uniform_thickening E.allSets E.allSets_compact apart E.allSets_disjoint
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := half_pos hε
  have hδε : δ < ε := half_lt_self hε
  have hdis (i j : V ⊕ G.Dart) (h : apart i j) :
      Disjoint (SquareGrid.cells δ (E.allSets i)) (SquareGrid.cells δ (E.allSets j)) :=
    SquareGrid.cells_disjoint hδε (hsep i j h)
  refine ⟨{
    branch := fun v => SquareGrid.cells δ (E.branch v)
    corridor := fun d => SquareGrid.cells δ (E.core d)
    branch_finite := fun v => SquareGrid.cells_finite hδ (E.branch_compact v)
    corridor_finite := fun d => SquareGrid.cells_finite hδ (E.core_compact d)
    branch_connected := fun v => SquareGrid.cells_connected hδ (E.branch_compact v)
      (E.branch_connected v)
    corridor_connected := fun d => SquareGrid.cells_connected hδ (E.core_compact d)
      (E.core_connected d)
    branches_disjoint := fun v w h => hdis (.inl v) (.inl w) h
    corridors_disjoint := fun d e h => hdis (.inr d) (.inr e) h
    nonincident_disjoint := fun v d h₁ h₂ => hdis (.inl v) (.inr d) ⟨h₁, h₂⟩
    incident_meets := ?_
  }⟩
  intro d
  have meets {K L : Set (ℝ × ℝ)} (h : (K ∩ L).Nonempty) :
      (SquareGrid.cells δ K ∩ SquareGrid.cells δ L).Nonempty := by
    obtain ⟨p, hpK, hpL⟩ := h
    obtain ⟨z, hz⟩ := SquareGrid.cell_cover hδ p
    exact ⟨z, ⟨p, hz, hpK⟩, ⟨p, hz, hpL⟩⟩
  exact ⟨meets (E.branch_core_meets d).1, meets (E.branch_core_meets d).2⟩

end
end PlaneEmbedding
end Barnette

end OAI


namespace OAI

/-! Clean finite walks, disjoint grown branches, and lattice minors. -/

namespace Barnette

noncomputable section

structure MinorModel {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) where
  branch : V → Set W
  branch_finite : ∀ v, (branch v).Finite
  branch_connected : ∀ v, (H.induce (branch v)).Connected
  branches_disjoint : ∀ v w, v ≠ w → Disjoint (branch v) (branch w)
  adjacency : ∀ v w, G.Adj v w → ∃ a ∈ branch v, ∃ b ∈ branch w, H.Adj a b

namespace WalkSelection

variable {W : Type*} {H : SimpleGraph W}

theorem shortest_join {A B : Set W}
    (hex : ∃ a ∈ A, ∃ b ∈ B, H.Reachable a b) :
    ∃ (a : W) (_ha : a ∈ A) (b : W) (_hb : b ∈ B) (p : H.Walk a b),
      p.IsPath ∧ (∀ x ∈ p.support, x ∈ A → x = a) ∧
        (∀ x ∈ p.support, x ∈ B → x = b) := by
  classical
  let P : ℕ → Prop := fun n => ∃ a ∈ A, ∃ b ∈ B, ∃ p : H.Walk a b, p.length = n
  have hp : ∃ n, P n := by
    obtain ⟨a, ha, b, hb, ⟨p⟩⟩ := hex
    exact ⟨p.length, a, ha, b, hb, p, rfl⟩
  obtain ⟨a, ha, b, hb, p, hlen⟩ := Nat.find_spec hp
  have minimal {x y : W} (hx : x ∈ A) (hy : y ∈ B) (q : H.Walk x y) :
      p.length ≤ q.length := by
    rw [hlen]
    exact Nat.find_min' hp ⟨x, hx, y, hy, q, rfl⟩
  have hpath : p.IsPath := by
    obtain ⟨q, hq⟩ := p.reachable.exists_walk_length_eq_dist
    apply p.isPath_of_length_eq_dist
    exact le_antisymm (hq ▸ minimal ha hb q) (SimpleGraph.dist_le p)
  refine ⟨a, ha, b, hb, p, hpath, ?_, ?_⟩
  · intro x hx hxA
    by_contra hxa
    have hshort := p.length_dropUntil_lt_length hx hxa
    exact (not_lt_of_ge (minimal hxA hb (p.dropUntil x hx))) hshort
  · intro x hx hxB
    by_contra hxb
    have hshort := p.length_takeUntil_lt_length hx hxb
    exact (not_lt_of_ge (minimal ha hxB (p.takeUntil x hx))) hshort

structure CleanConnection (A B C : Set W) where
  start : W
  finish : W
  start_mem : start ∈ A
  finish_mem : finish ∈ B
  walk : H.Walk start finish
  isPath : walk.IsPath
  support_subset : ∀ x ∈ walk.support, x ∈ C
  clean_start : ∀ x ∈ walk.support, x ∈ A → x = start
  clean_finish : ∀ x ∈ walk.support, x ∈ B → x = finish

theorem exists_clean_connection {A B C : Set W}
    (hC : (H.induce C).Connected) (hA : (A ∩ C).Nonempty) (hB : (B ∩ C).Nonempty) :
    Nonempty (CleanConnection (H := H) A B C) := by
  classical
  obtain ⟨a, ha, haC⟩ := hA
  obtain ⟨b, hb, hbC⟩ := hB
  obtain ⟨u, hu, v, hv, p, hpath, hcleanA, hcleanB⟩ :=
    shortest_join (H := H.induce C) (A := {x | x.val ∈ A}) (B := {x | x.val ∈ B})
      ⟨⟨a, haC⟩, ha, ⟨b, hbC⟩, hb, hC _ _⟩
  let f : H.induce C →g H := ⟨Subtype.val, fun h => h⟩
  let q : H.Walk u.val v.val := p.map f
  have hs : q.support = p.support.map Subtype.val := p.support_map _
  refine ⟨{
    start := u.val
    finish := v.val
    start_mem := hu
    finish_mem := hv
    walk := q
    isPath := hpath.map Subtype.val_injective
    support_subset := ?_
    clean_start := ?_
    clean_finish := ?_
  }⟩
  · intro x hx
    rw [hs] at hx
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hx
    exact z.property
  · intro x hx hxA
    rw [hs] at hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact congrArg Subtype.val (hcleanA z hz hxA)
  · intro x hx hxB
    rw [hs] at hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    exact congrArg Subtype.val (hcleanB z hz hxB)

namespace CleanConnection
variable {A B C : Set W} (p : CleanConnection (H := H) A B C)

def leftSet : Set W := {x | x ∈ p.walk.dropLast.support}

theorem leftSet_finite : p.leftSet.Finite := p.walk.dropLast.support.finite_toSet

theorem leftSet_connected : (H.induce p.leftSet).Connected :=
  p.walk.dropLast.connected_induce_support

theorem start_mem_leftSet : p.start ∈ p.leftSet := p.walk.dropLast.start_mem_support

theorem leftSet_subset : p.leftSet ⊆ C := by
  intro x hx
  apply p.support_subset x
  exact (p.walk.isSubwalk_take _).support_subset hx

theorem leftSet_disjoint_finish (hAB : Disjoint A B) : Disjoint p.leftSet B := by
  have hne : p.start ≠ p.finish := by
    intro heq
    exact Set.disjoint_left.mp hAB p.start_mem (heq ▸ p.finish_mem)
  have hn : ¬p.walk.Nil := SimpleGraph.Walk.not_nil_of_ne hne
  have hd := p.isPath.support_nodup
  rw [← p.walk.support_dropLast_concat hn] at hd
  have hfinish : p.finish ∉ p.leftSet := by
    intro h
    exact hd.disjoint h (by simp)
  rw [Set.disjoint_left]
  intro x hx hxB
  have hs : x ∈ p.walk.support := (p.walk.isSubwalk_take _).support_subset hx
  have heq := p.clean_finish x hs hxB
  exact hfinish (heq ▸ hx)

theorem leftSet_adj_finish (hAB : Disjoint A B) :
    ∃ a ∈ p.leftSet, H.Adj a p.finish := by
  have hne : p.start ≠ p.finish := by
    intro heq
    exact Set.disjoint_left.mp hAB p.start_mem (heq ▸ p.finish_mem)
  exact ⟨p.walk.penultimate, p.walk.dropLast.end_mem_support,
    p.walk.adj_penultimate (SimpleGraph.Walk.not_nil_of_ne hne)⟩

end CleanConnection

end WalkSelection
end
end Barnette

namespace Barnette

namespace CorridorModel
noncomputable section
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

private theorem exists_edgeDart (e : G.edgeSet) : ∃ d : G.Dart, d.edge = e.val := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ a b => exact ⟨⟨(a, b), he⟩, rfl⟩

def edgeDart (e : G.edgeSet) : G.Dart := Classical.choose (exists_edgeDart e)

@[simp] theorem edgeDart_edge (e : G.edgeSet) : (edgeDart e).edge = e.val :=
  Classical.choose_spec (exists_edgeDart e)

variable (M : CorridorModel G H)

def connection (e : G.edgeSet) : WalkSelection.CleanConnection (H := H)
    (M.branch (edgeDart e).fst) (M.branch (edgeDart e).snd) (M.corridor (edgeDart e)) :=
  Classical.choice (WalkSelection.exists_clean_connection
    (M.corridor_connected _) (M.incident_meets _).1 (M.incident_meets _).2)

def extension (e : G.edgeSet) : Set W := (M.connection e).leftSet

theorem extension_finite (e : G.edgeSet) : (M.extension e).Finite :=
  (M.connection e).leftSet_finite

theorem extension_connected (e : G.edgeSet) : (H.induce (M.extension e)).Connected :=
  (M.connection e).leftSet_connected

theorem extension_subset (e : G.edgeSet) : M.extension e ⊆ M.corridor (edgeDart e) :=
  (M.connection e).leftSet_subset

theorem extension_disjoint_branch (e : G.edgeSet) (v : V) (hv : v ≠ (edgeDart e).fst) :
    Disjoint (M.extension e) (M.branch v) := by
  by_cases hs : v = (edgeDart e).snd
  · subst v
    exact (M.connection e).leftSet_disjoint_finish
      (M.branches_disjoint _ _ (edgeDart e).fst_ne_snd)
  · exact ((M.nonincident_disjoint _ _ hv hs).mono_right (M.extension_subset e)).symm

theorem extensions_disjoint (e f : G.edgeSet) (hef : e ≠ f) :
    Disjoint (M.extension e) (M.extension f) := by
  have hne : (edgeDart e).edge ≠ (edgeDart f).edge := by
    simpa only [edgeDart_edge] using (fun h => hef (Subtype.ext h) : e.val ≠ f.val)
  exact (M.corridors_disjoint _ _ hne).mono (M.extension_subset e) (M.extension_subset f)

def grownBranch (v : V) : Set W := M.branch v ∪
  ⋃ e : {e : G.edgeSet // (edgeDart e).fst = v}, M.extension e.val

theorem branch_subset_grown (v : V) : M.branch v ⊆ M.grownBranch v :=
  Set.subset_union_left

theorem extension_subset_grown (e : G.edgeSet) : M.extension e ⊆ M.grownBranch (edgeDart e).fst :=
  fun _ hx => Or.inr (Set.mem_iUnion.mpr ⟨⟨e, rfl⟩, hx⟩)

theorem grownBranch_connected (v : V) : (H.induce (M.grownBranch v)).Connected := by
  obtain ⟨⟨a, ha⟩⟩ := (M.branch_connected v).nonempty
  apply H.induce_connected_of_patches a (M.branch_subset_grown v ha)
  intro x hx
  rcases hx with hx | hx
  · exact ⟨M.branch v, M.branch_subset_grown v, ha, hx, M.branch_connected v _ _⟩
  · obtain ⟨⟨e, he⟩, hx⟩ := Set.mem_iUnion.mp hx
    have hext : M.extension e ⊆ M.grownBranch v := by
      simpa only [he] using M.extension_subset_grown e
    have hi : (M.branch v ∩ M.extension e).Nonempty := by
      refine ⟨(M.connection e).start, ?_, (M.connection e).start_mem_leftSet⟩
      simpa only [he] using (M.connection e).start_mem
    exact ⟨M.branch v ∪ M.extension e,
      Set.union_subset (M.branch_subset_grown v) hext, Or.inl ha, Or.inr hx,
      SimpleGraph.induce_union_connected (M.branch_connected v).preconnected
        (M.extension_connected e).preconnected hi _ _⟩

theorem grownBranches_disjoint (v w : V) (hvw : v ≠ w) :
    Disjoint (M.grownBranch v) (M.grownBranch w) := by
  rw [Set.disjoint_left]
  intro x hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact Set.disjoint_left.mp (M.branches_disjoint v w hvw) hx hy
  · obtain ⟨⟨e, he⟩, hy⟩ := Set.mem_iUnion.mp hy
    exact Set.disjoint_left.mp (M.extension_disjoint_branch e v (he ▸ hvw)) hy hx
  · obtain ⟨⟨e, he⟩, hx⟩ := Set.mem_iUnion.mp hx
    exact Set.disjoint_left.mp (M.extension_disjoint_branch e w (he ▸ hvw.symm)) hx hy
  · obtain ⟨⟨e, he⟩, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨⟨f, hf⟩, hy⟩ := Set.mem_iUnion.mp hy
    have hef : e ≠ f := by
      intro h
      subst f
      exact hvw (he.symm.trans hf)
    exact Set.disjoint_left.mp (M.extensions_disjoint e f hef) hx hy

theorem grownBranch_adjacency (v w : V) (hvw : G.Adj v w) :
    ∃ a ∈ M.grownBranch v, ∃ b ∈ M.grownBranch w, H.Adj a b := by
  let e : G.edgeSet := ⟨s(v, w), hvw⟩
  have hAB := M.branches_disjoint _ _ (edgeDart e).fst_ne_snd
  obtain ⟨a, ha, hadj⟩ := (M.connection e).leftSet_adj_finish hAB
  have ha' : a ∈ M.grownBranch (edgeDart e).fst := M.extension_subset_grown e ha
  have hb' : (M.connection e).finish ∈ M.grownBranch (edgeDart e).snd :=
    M.branch_subset_grown _ (M.connection e).finish_mem
  have hd : (edgeDart e).edge = s(v, w) := edgeDart_edge e
  rcases SimpleGraph.dart_edge_eq_mk'_iff'.mp hd with ⟨h₁, h₂⟩ | ⟨h₂, h₁⟩
  · exact ⟨a, h₁ ▸ ha', (M.connection e).finish, h₂ ▸ hb', hadj⟩
  · exact ⟨(M.connection e).finish, h₁ ▸ hb', a, h₂ ▸ ha', hadj.symm⟩

variable [Fintype V]

theorem grownBranch_finite (v : V) : (M.grownBranch v).Finite := by
  classical
  exact (M.branch_finite v).union (Set.finite_iUnion (fun e => M.extension_finite e.val))

def toMinorModel : MinorModel G H where
  branch := M.grownBranch
  branch_finite := M.grownBranch_finite
  branch_connected := M.grownBranch_connected
  branches_disjoint := M.grownBranches_disjoint
  adjacency := M.grownBranch_adjacency

end
end CorridorModel
end Barnette

namespace Barnette.PlaneEmbedding
noncomputable section
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem exists_lattice_minor_model (E : PlaneEmbedding G) :
    Nonempty (MinorModel G SquareGrid.graph) := by
  classical
  obtain ⟨M⟩ := E.exists_lattice_corridor_model
  exact ⟨M.toMinorModel⟩
end
end Barnette.PlaneEmbedding

end OAI


namespace OAI

/-! Extending disjoint connected branches to a connected vertex partition. -/

namespace Barnette
noncomputable section
open scoped Classical

namespace BranchPartition
variable {V W : Type*} [Fintype V] [Fintype W] [Nonempty V]
  (H : SimpleGraph W)

omit [Fintype W] in
lemma walk_crosses_boundary {S : Set W} {v w : W} (p : H.Walk v w)
    (hv : v ∈ S) (hw : w ∉ S) :
    ∃ a ∈ S, ∃ b ∉ S, H.Adj a b := by
  induction p with
  | nil => exact (hw hv).elim
  | @cons u z w h p ih =>
    by_cases hz : z ∈ S
    · exact ih hz hw
    · exact ⟨u, hv, z, hz, h⟩

theorem extend (hH : H.Connected) (B₀ : V → Set W)
    (hB₀ : ∀ v, (H.induce (B₀ v)).Connected)
    (hd₀ : ∀ v w, v ≠ w → Disjoint (B₀ v) (B₀ w)) :
    ∃ B : V → Set W,
      (∀ v, B₀ v ⊆ B v) ∧
      (∀ v, (H.induce (B v)).Connected) ∧
      (∀ v w, v ≠ w → Disjoint (B v) (B w)) ∧
      (∀ w, ∃ v, w ∈ B v) := by
  let S : Set (V → Set W) := {B | (∀ v, B₀ v ⊆ B v) ∧
    (∀ v, (H.induce (B v)).Connected) ∧
    (∀ v w, v ≠ w → Disjoint (B v) (B w))}
  let size (B : V → Set W) := (⋃ v, B v).ncard
  have hS : S.Nonempty := ⟨B₀, fun _ => Set.Subset.rfl, hB₀, hd₀⟩
  obtain ⟨B, hB, hmax⟩ := S.exists_max_image size (Set.toFinite _) hS
  refine ⟨B, hB.1, hB.2.1, hB.2.2, ?_⟩
  intro w
  by_contra hw
  have hwU : w ∉ ⋃ v, B v := by simpa only [Set.mem_iUnion] using hw
  obtain ⟨v₀⟩ := ‹Nonempty V›
  obtain ⟨a₀⟩ := (hB.2.1 v₀).nonempty
  obtain ⟨p⟩ := hH a₀.val w
  obtain ⟨a, ha, b, hb, hab⟩ := walk_crosses_boundary H p
    (Set.mem_iUnion.mpr ⟨v₀, a₀.property⟩) hwU
  obtain ⟨v, hv⟩ := Set.mem_iUnion.mp ha
  let B' : V → Set W := fun z => if z = v then insert b (B v) else B z
  have hle : ∀ z, B z ⊆ B' z := by
    intro z x hx
    by_cases hz : z = v
    · subst z; simp only [B', ite_true]; exact Set.mem_insert_of_mem _ hx
    · simpa only [B', hz, ite_false] using hx
  have hB' : B' ∈ S := by
    refine ⟨fun z => (hB.1 z).trans (hle z), ?_, ?_⟩
    · intro z
      by_cases hz : z = v
      · subst z
        have hsingle : (H.induce ({b} : Set W)).Preconnected := by
          intro x y
          have he : x = y := Subsingleton.elim _ _
          subst y
          exact .rfl
        have hh := SimpleGraph.connected_induce_union (hB.2.1 v).preconnected hsingle
          hv (show b ∈ ({b} : Set W) by simp) hab
        rw [show B' v = insert b (B v) by simp [B']]
        rw [Set.union_singleton] at hh
        exact hh
      · rw [show B' z = B z by simp [B', hz]]
        exact hB.2.1 z
    · intro z t hzt
      rw [Set.disjoint_left]
      intro x hxz hxt
      by_cases hz : z = v
      · subst z
        have ht : t ≠ v := Ne.symm hzt
        simp only [B', ite_true, Set.mem_insert_iff] at hxz
        rw [show B' t = B t by simp only [B', ht, ite_false]] at hxt
        rcases hxz with rfl | hxz
        · exact hb (Set.mem_iUnion.mpr ⟨t, hxt⟩)
        · exact Set.disjoint_left.mp (hB.2.2 v t hzt) hxz hxt
      · rw [show B' z = B z by simp only [B', hz, ite_false]] at hxz
        by_cases ht : t = v
        · subst t
          simp only [B', ite_true, Set.mem_insert_iff] at hxt
          rcases hxt with rfl | hxt
          · exact hb (Set.mem_iUnion.mpr ⟨z, hxz⟩)
          · exact Set.disjoint_left.mp (hB.2.2 z v hzt) hxz hxt
        · rw [show B' t = B t by simp only [B', ht, ite_false]] at hxt
          exact Set.disjoint_left.mp (hB.2.2 z t hzt) hxz hxt
  have hstrict : (⋃ z, B z) ⊂ ⋃ z, B' z := by
    refine ⟨Set.iUnion_mono hle, ?_⟩
    intro hh
    apply hb (hh ?_)
    exact Set.mem_iUnion.mpr ⟨v, by simp [B']⟩
  exact (not_lt_of_ge (hmax B' hB')) (Set.ncard_lt_ncard hstrict)

omit [Fintype V] [Fintype W] [Nonempty V] in

theorem quotient (B : V → Set W)
    (hB : ∀ v, (H.induce (B v)).Connected)
    (hd : ∀ v w, v ≠ w → Disjoint (B v) (B w))
    (hcover : ∀ w, ∃ v, w ∈ B v) :
    ∃ q : W → V, Function.Surjective q ∧ (∀ w v, q w = v ↔ w ∈ B v) := by
  choose q hq using hcover
  have he (w : W) (v : V) : q w = v ↔ w ∈ B v := by
    constructor
    · intro hv; exact hv ▸ hq w
    · intro hw
      by_contra hne
      exact Set.disjoint_left.mp (hd (q w) v hne) (hq w) hw
  refine ⟨q, ?_, he⟩
  intro v
  obtain ⟨w⟩ := (hB v).nonempty
  exact ⟨w.val, (he w.val v).mpr w.property⟩

end BranchPartition
end
end Barnette

end OAI


namespace OAI

/-! Rectangular primal and dual networks and finite lattice containment. -/

namespace Barnette.RectangularDual
noncomputable section

abbrev Vertex (n m : ℕ) := Fin (n + 1) × Fin (m + 1)
abbrev Edge (n m : ℕ) := (Fin n × Fin (m + 1)) ⊕ (Fin (n + 1) × Fin m)
abbrev Face (n m : ℕ) := Option (Fin n × Fin m)

def primal (n m : ℕ) : Network (Vertex n m) (Edge n m) where
  tail := Sum.elim (fun e => (e.1.castSucc, e.2)) (fun e => (e.1, e.2.castSucc))
  head := Sum.elim (fun e => (e.1.succ, e.2)) (fun e => (e.1, e.2.succ))

def lower {n : ℕ} : Fin (n + 1) → Option (Fin n) := Fin.cases none some
def upper {n : ℕ} : Fin (n + 1) → Option (Fin n) := Fin.lastCases none some

def dual (n m : ℕ) : Network (Face n m) (Edge n m) where
  tail := Sum.elim
    (fun e => (lower e.2).map (fun j => (e.1, j)))
    (fun e => (upper e.1).map (fun i => (i, e.2)))
  head := Sum.elim
    (fun e => (upper e.2).map (fun j => (e.1, j)))
    (fun e => (lower e.1).map (fun i => (i, e.2)))

def lowerValue {n : ℕ} (f : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.cases 0 f
def upperValue {n : ℕ} (f : Fin n → ℝ) : Fin (n + 1) → ℝ := Fin.lastCases 0 f

def stepCoeff {n : ℕ} (v : Fin (n + 1)) (e : Fin n) : ℝ :=
  (if e.succ = v then 1 else 0) - (if e.castSucc = v then 1 else 0)

lemma sum_succ {n : ℕ} (f : Fin n → ℝ) (v : Fin (n + 1)) :
    (∑ i, if i.succ = v then f i else 0) = lowerValue f v := by
  induction v using Fin.cases with
  | zero => simp [lowerValue]
  | succ v => simp [lowerValue]

lemma sum_castSucc {n : ℕ} (f : Fin n → ℝ) (v : Fin (n + 1)) :
    (∑ i, if i.castSucc = v then f i else 0) = upperValue f v := by
  induction v using Fin.lastCases with
  | last => simp [upperValue, Fin.castSucc_ne_last]
  | cast v => simp [upperValue]

lemma sum_stepCoeff {n : ℕ} (f : Fin n → ℝ) (v : Fin (n + 1)) :
    (∑ i, stepCoeff v i * f i) = lowerValue f v - upperValue f v := by
  simp only [stepCoeff, sub_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_sub_distrib, sum_succ, sum_castSucc]

lemma lower_eval {n : ℕ} (f : Fin n → ℝ) (v : Fin (n + 1)) :
    (lower v).elim 0 f = lowerValue f v := by
  induction v using Fin.cases <;> simp [lower, lowerValue]

lemma upper_eval {n : ℕ} (f : Fin n → ℝ) (v : Fin (n + 1)) :
    (upper v).elim 0 f = upperValue f v := by
  induction v using Fin.lastCases <;> simp [upper, upperValue]

def potential {n m : ℕ} (f : Fin n × Fin m → ℝ) : Face n m → ℝ :=
  fun z => z.elim 0 f

lemma eval_map {A B : Type*} (g : B → ℝ) (f : A → B) (z : Option A) :
    (z.map f).elim 0 g = z.elim 0 (g ∘ f) := by cases z <;> rfl

lemma dual_horizontal {n m : ℕ} (f : Fin n × Fin m → ℝ)
    (i : Fin n) (j : Fin (m + 1)) :
    (dual n m).gradient (potential f) (.inl (i, j)) =
      -∑ q, stepCoeff j q * f (i, q) := by
  change ((upper j).map _).elim 0 f - ((lower j).map _).elim 0 f = _
  rw [eval_map, eval_map, upper_eval, lower_eval, sum_stepCoeff]
  dsimp only [Function.comp_def]
  ring

lemma dual_vertical {n m : ℕ} (f : Fin n × Fin m → ℝ)
    (i : Fin (n + 1)) (j : Fin m) :
    (dual n m).gradient (potential f) (.inr (i, j)) =
      ∑ p, stepCoeff i p * f (p, j) := by
  change ((lower i).map _).elim 0 f - ((upper i).map _).elim 0 f = _
  rw [eval_map, eval_map, upper_eval, lower_eval, sum_stepCoeff]
  rfl

lemma boundary_formula {n m : ℕ} (x : Edge n m → ℝ) (i : Fin (n + 1))
    (j : Fin (m + 1)) :
    (primal n m).boundary x (i, j) =
      (∑ p, stepCoeff i p * x (.inl (p, j))) +
      (∑ q, stepCoeff j q * x (.inr (i, q))) := by
  classical
  rw [Network.boundary_apply, Fintype.sum_sum_type]
  simp only [primal, Sum.elim_inl, Sum.elim_inr, Prod.mk.injEq,
    Fintype.sum_prod_type, stepCoeff, sub_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_sub_distrib, ite_and]
  simp

lemma orthogonal_potential (n m : ℕ) (f : Fin n × Fin m → ℝ) :
    (primal n m).boundary ((dual n m).gradient (potential f)) = 0 := by
  ext ⟨i, j⟩
  rw [boundary_formula]
  simp only [dual_horizontal, dual_vertical, mul_neg, Finset.sum_neg_distrib,
    Finset.mul_sum]
  rw [Finset.sum_comm (f := fun q p => stepCoeff j q * (stepCoeff i p * f (p, q)))]
  have he : (∑ p, ∑ q, stepCoeff j q * (stepCoeff i p * f (p, q))) =
      ∑ p, ∑ q, stepCoeff i p * (stepCoeff j q * f (p, q)) := by
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [he]
  exact neg_add_cancel _

lemma orthogonal (n m : ℕ) (f : Face n m → ℝ) :
    (primal n m).boundary ((dual n m).gradient f) = 0 := by
  let g : Fin n × Fin m → ℝ := fun t => f (some t) - f none
  have hf : f = potential g + (fun _ => f none) := by
    ext z
    cases z <;> simp [potential, g]
  rw [hf, map_add, Network.gradient_const, add_zero]
  exact orthogonal_potential n m g

lemma horizontal_adj {n m : ℕ} (i : Fin n) (j : Fin (m + 1)) :
    (primal n m).graph.Adj (i.castSucc, j) (i.succ, j) := by
  refine ⟨?_, .inl (i, j), Or.inl ⟨rfl, rfl⟩⟩
  intro h
  have hh := congrArg (fun z : Vertex n m => z.1.val) h
  simp only [Fin.val_castSucc, Fin.val_succ] at hh
  omega

lemma vertical_adj {n m : ℕ} (i : Fin (n + 1)) (j : Fin m) :
    (primal n m).graph.Adj (i, j.castSucc) (i, j.succ) := by
  refine ⟨?_, .inr (i, j), Or.inl ⟨rfl, rfl⟩⟩
  intro h
  have hh := congrArg (fun z : Vertex n m => z.2.val) h
  simp only [Fin.val_castSucc, Fin.val_succ] at hh
  omega

lemma primal_connected (n m : ℕ) : (primal n m).graph.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨(0, 0), ?_⟩
  rintro ⟨i, j⟩
  have hv : (primal n m).graph.Reachable (0, 0) (0, j) := by
    induction j using Fin.induction with
    | zero => exact .rfl
    | succ j ih => exact ih.trans (vertical_adj (0 : Fin (n + 1)) j).reachable
  have hh : (primal n m).graph.Reachable (0, j) (i, j) := by
    induction i using Fin.induction with
    | zero => exact .rfl
    | succ i ih => exact ih.trans (horizontal_adj i j).reachable
  exact hv.trans hh

lemma dual_connected (n m : ℕ) : (dual n m).graph.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨none, ?_⟩
  intro z
  cases z with
  | none => exact .rfl
  | some z =>
    obtain ⟨i, j⟩ := z
    cases n with
    | zero => exact isEmptyElim i
    | succ n =>
      induction i using Fin.induction with
      | zero =>
        have h := ((dual (n + 1) m).edge_reachable (.inr (0, j))).symm
        have hu : upper (0 : Fin (n + 2)) = some (0 : Fin (n + 1)) := by
          change upper (0 : Fin (n + 1)).castSucc = _
          exact Fin.lastCases_castSucc _
        simpa only [dual, Sum.elim_inr, lower, Fin.cases_zero, hu,
          Option.map_none, Option.map_some] using h
      | succ i ih =>
        have h := ((dual (n + 1) m).edge_reachable (.inr (i.succ.castSucc, j))).symm
        have hl : lower i.succ.castSucc = some i.castSucc := by
          have he : i.succ.castSucc = i.castSucc.succ := by ext; rfl
          rw [he]
          simp [lower]
        have hu : upper i.succ.castSucc = some i.succ := Fin.lastCases_castSucc _
        exact ih.trans (by
          simpa only [dual, Sum.elim_inr, hl, hu, Option.map_some] using h)

theorem grid_duality (n m : ℕ) : (primal n m).Duality (dual n m) := by
  apply Network.duality_of_orth_card (primal n m) (dual n m)
    (primal_connected n m) (dual_connected n m)
  · simp only [Vertex, Face, Edge, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_option, Fintype.card_sum]
    ring
  · exact orthogonal n m

end
end Barnette.RectangularDual

namespace Barnette.MinorModel
noncomputable section
open scoped Classical
variable {V W U : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
  {J : SimpleGraph U} [Fintype U]

def pullHost (M : MinorModel G H) (f : J ↪g H)
    (hf : ∀ v, M.branch v ⊆ Set.range f) : MinorModel G J where
  branch v := f ⁻¹' M.branch v
  branch_finite _ := Set.toFinite _
  branch_connected v := by
    let g : {x // f x ∈ M.branch v} → M.branch v := fun x => ⟨f x.val, x.property⟩
    have hg : Function.Bijective g := by
      refine ⟨?_, ?_⟩
      · intro x y hxy
        apply Subtype.ext
        exact f.injective (congrArg Subtype.val hxy)
      · intro y
        obtain ⟨x, hx⟩ := hf v y.property
        refine ⟨⟨x, hx ▸ y.property⟩, ?_⟩
        exact Subtype.ext hx
    let e : J.induce (f ⁻¹' M.branch v) ≃g H.induce (M.branch v) :=
      { toEquiv := Equiv.ofBijective g hg
        map_rel_iff' := by intro x y; exact f.map_rel_iff }
    exact e.connected_iff.mpr (M.branch_connected v)
  branches_disjoint v w hvw := (M.branches_disjoint v w hvw).preimage f
  adjacency v w h := by
    obtain ⟨a, ha, b, hb, hab⟩ := M.adjacency v w h
    obtain ⟨a', rfl⟩ := hf v ha
    obtain ⟨b', rfl⟩ := hf w hb
    exact ⟨a', ha, b', hb, f.map_rel_iff.mp hab⟩
end
end Barnette.MinorModel

namespace Barnette.RectangularDual
noncomputable section
open scoped Classical

lemma primal_adj_iff {n m : ℕ} (p q : Vertex n m) :
    (primal n m).graph.Adj p q ↔
      ((p.1.val + 1 = q.1.val ∨ q.1.val + 1 = p.1.val) ∧ p.2 = q.2) ∨
      ((p.2.val + 1 = q.2.val ∨ q.2.val + 1 = p.2.val) ∧ p.1 = q.1) := by
  constructor
  · rintro ⟨_, e, he⟩
    rcases e with ⟨i, j⟩ | ⟨i, j⟩ <;>
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [primal]
  · have hx (a b : Vertex n m) (h : a.1.val + 1 = b.1.val) (hj : a.2 = b.2) :
        (primal n m).graph.Adj a b := by
      have hi : a.1.val < n := by have := b.1.isLt; omega
      refine ⟨?_, .inl (⟨a.1.val, hi⟩, a.2), Or.inl ⟨?_, ?_⟩⟩
      · intro he; have hh := congrArg (fun x : Vertex n m => x.1.val) he; omega
      · apply Prod.ext <;> rfl
      · apply Prod.ext
        · apply Fin.ext; exact h
        · exact hj
    have hy (a b : Vertex n m) (h : a.2.val + 1 = b.2.val) (hi : a.1 = b.1) :
        (primal n m).graph.Adj a b := by
      have hj : a.2.val < m := by have := b.2.isLt; omega
      refine ⟨?_, .inr (a.1, ⟨a.2.val, hj⟩), Or.inl ⟨?_, ?_⟩⟩
      · intro he; have hh := congrArg (fun x : Vertex n m => x.2.val) he; omega
      · apply Prod.ext <;> rfl
      · apply Prod.ext
        · exact hi
        · apply Fin.ext; exact h
    rintro (⟨h | h, hj⟩ | ⟨h | h, hi⟩)
    · exact hx p q h hj
    · exact (hx q p h hj.symm).symm
    · exact hy p q h hi
    · exact (hy q p h hi.symm).symm

def latticePoint (r : ℕ) (p : Vertex (2 * r) (2 * r)) : ℤ × ℤ :=
  ((p.1.val : ℤ) - r, (p.2.val : ℤ) - r)

lemma latticePoint_injective (r : ℕ) : Function.Injective (latticePoint r) := by
  intro p q h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp [latticePoint] at h₁ h₂
  apply Prod.ext <;> apply Fin.ext <;> omega

def latticeEmbedding (r : ℕ) : (primal (2 * r) (2 * r)).graph ↪g SquareGrid.graph where
  toFun := latticePoint r
  inj' := latticePoint_injective r
  map_rel_iff' := by
    intro p q
    rw [primal_adj_iff]
    change SquareGrid.graph.Adj (latticePoint r p) (latticePoint r q) ↔ _
    simp only [SquareGrid.graph, latticePoint, Fin.ext_iff]
    omega

lemma bounded_mem_range (r : ℕ) (z : ℤ × ℤ)
    (h₁ : z.1.natAbs ≤ r) (h₂ : z.2.natAbs ≤ r) :
    z ∈ Set.range (latticeEmbedding r) := by
  have ha : z.1 ≤ (z.1.natAbs : ℤ) := Int.le_natAbs
  have hb : -z.1 ≤ (z.1.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -z.1))
  have hc : z.2 ≤ (z.2.natAbs : ℤ) := Int.le_natAbs
  have hd : -z.2 ≤ (z.2.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -z.2))
  refine ⟨(⟨(z.1 + r).toNat, ?_⟩, ⟨(z.2 + r).toNat, ?_⟩), ?_⟩
  · omega
  · omega
  · apply Prod.ext <;> dsimp [latticeEmbedding, latticePoint] <;> omega

lemma finite_subset_box (s : Set (ℤ × ℤ)) (hs : s.Finite) :
    ∃ r : ℕ, s ⊆ Set.range (latticeEmbedding r) := by
  let r := ∑ z ∈ hs.toFinset, (z.1.natAbs + z.2.natAbs)
  refine ⟨r, ?_⟩
  intro z hz
  have hle : z.1.natAbs + z.2.natAbs ≤ r :=
    Finset.single_le_sum (f := fun z : ℤ × ℤ => z.1.natAbs + z.2.natAbs)
      (fun _ _ => Nat.zero_le _) (hs.mem_toFinset.mpr hz)
  exact bounded_mem_range r z (by omega) (by omega)

theorem lattice_minor_in_rectangle {V : Type*} [Fintype V] {G : SimpleGraph V}
    (M : MinorModel G SquareGrid.graph) :
    ∃ r : ℕ, Nonempty (MinorModel G (primal (2 * r) (2 * r)).graph) := by
  let s := ⋃ v, M.branch v
  have hs : s.Finite := Set.finite_iUnion M.branch_finite
  obtain ⟨r, hr⟩ := finite_subset_box s hs
  refine ⟨r, ⟨M.pullHost (latticeEmbedding r) ?_⟩⟩
  intro v z hz
  exact hr (Set.mem_iUnion.mpr ⟨v, hz⟩)

end
end Barnette.RectangularDual

end OAI


namespace OAI

/-! Graph realization and exact finite duality for topological plane embeddings. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V W E : Type*} [Fintype V] [Fintype W] [Fintype E]

def Realizes (G : SimpleGraph V) (M : Network V G.edgeSet) : Prop :=
  ∀ e, s(M.tail e, M.head e) = e.val

omit [Fintype V] in
lemma Realizes.graph_eq {G : SimpleGraph V} {M : Network V G.edgeSet}
    (h : M.Realizes G) : M.graph = G := by
  ext v w
  constructor
  · rintro ⟨_, e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact G.mem_edgeSet.mp ((h e).symm ▸ e.property)
    · exact (G.mem_edgeSet.mp ((h e).symm ▸ e.property)).symm
  · intro hvw
    let e : G.edgeSet := ⟨s(v,w), hvw⟩
    refine ⟨hvw.ne, e, ?_⟩
    have he := h e
    change s(M.tail e, M.head e) = s(v,w) at he
    exact Sym2.eq_iff.mp he

omit [Fintype V] in
lemma Realizes.loopless {G : SimpleGraph V} {M : Network V G.edgeSet}
    (h : M.Realizes G) (e : G.edgeSet) : M.tail e ≠ M.head e := by
  have he : G.Adj (M.tail e) (M.head e) := G.mem_edgeSet.mp ((h e).symm ▸ e.property)
  exact he.ne

omit [Fintype V] in
lemma exists_dart_for_edge (G : SimpleGraph V) (e : G.edgeSet) :
    ∃ d : G.Dart, d.edge = e.val := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.inductionOn with
  | hf x y => exact ⟨⟨(x,y), he⟩, rfl⟩

omit [Fintype V] [Fintype W] [Fintype E] in
lemma connectedFibers_of_partition (N : Network W E) (q : W → V)
    (B : V → Set W) (hB : ∀ v, (N.graph.induce (B v)).Connected)
    (hmem : ∀ w v, q w = v ↔ w ∈ B v) : N.ConnectedFibers q := by
  intro x y hxy
  let T := N.restrict (Subtype.val : N.internal q → E)
  let f : N.graph.induce (B (q x)) →g T.graph := {
    toFun := Subtype.val
    map_rel' := by
      intro a b hab
      rcases hab with ⟨hne, e, he⟩
      have ha : q a.val = q x := (hmem _ _).mpr a.property
      have hb : q b.val = q x := (hmem _ _).mpr b.property
      have hei : e ∈ N.internal q := by
        rcases he with ⟨ht, hh⟩ | ⟨ht, hh⟩
        · change q (N.tail e) = q (N.head e)
          rw [ht, hh]; exact ha.trans hb.symm
        · change q (N.tail e) = q (N.head e)
          rw [ht, hh]; exact hb.trans ha.symm
      exact ⟨hne, ⟨e, hei⟩, he⟩ }
  have hx : x ∈ B (q x) := (hmem x (q x)).mp rfl
  have hy : y ∈ B (q x) := (hmem y (q x)).mp hxy.symm
  exact ((hB (q x)) ⟨x,hx⟩ ⟨y,hy⟩).map f

omit [Fintype E] in

theorem minor_quotient {G : SimpleGraph V} (hG : G.Connected)
    (N : Network W E) (hN : N.graph.Connected) (M : MinorModel G N.graph) :
    ∃ (q : W → V) (j : G.edgeSet → E), Function.Surjective q ∧
      N.ConnectedFibers q ∧ Function.Injective j ∧
      ((N.mapVertices q).restrict j).Realizes G := by
  have : Nonempty V := hG.nonempty
  obtain ⟨B, hsub, hconn, hdisj, hcover⟩ := BranchPartition.extend N.graph hN
    M.branch M.branch_connected M.branches_disjoint
  obtain ⟨q, hq, hmem⟩ := BranchPartition.quotient N.graph B hconn hdisj hcover
  choose d hd using exists_dart_for_edge G
  have hex (e : G.edgeSet) : ∃ k : E, s(q (N.tail k), q (N.head k)) = e.val := by
    obtain ⟨a, ha, b, hb, _, k, hk⟩ := M.adjacency (d e).fst (d e).snd (d e).adj
    have ha' : q a = (d e).fst := (hmem _ _).mpr (hsub _ ha)
    have hb' : q b = (d e).snd := (hmem _ _).mpr (hsub _ hb)
    refine ⟨k, ?_⟩
    rcases hk with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · rw [ht, hh, ha', hb']; exact hd e
    · rw [ht, hh, ha', hb', Sym2.eq_swap]; exact hd e
  choose j hj using hex
  refine ⟨q, j, hq, N.connectedFibers_of_partition q B hconn hmem, ?_, hj⟩
  intro e f hef
  apply Subtype.ext
  exact (hj e).symm.trans ((congrArg (fun k => s(q (N.tail k), q (N.head k))) hef).trans (hj f))

universe uF
variable {F : Type uF} [Fintype F]

theorem Duality.graphMinor {G : SimpleGraph V} (hG : G.Connected)
    (N : Network W E) (D : Network F E) (h : N.Duality D)
    (M : MinorModel G N.graph) :
    ∃ (P : Network V G.edgeSet) (L : Type uF) (_ : Fintype L) (Q : Network L G.edgeSet),
      P.Realizes G ∧ P.Duality Q := by
  obtain ⟨q,j,hq,hc,hj,hreal⟩ := minor_quotient hG N h.connected M
  have he (e : G.edgeSet) : q (N.tail (j e)) ≠ q (N.head (j e)) := hreal.loopless e
  have hPc : ((N.mapVertices q).restrict j).graph.Connected := by
    rw [hreal.graph_eq]; exact hG
  obtain ⟨L, hL, Q, hQ⟩ := h.minor N D q hq hc j hj he hPc
  exact ⟨_, L, hL, Q, hreal, hQ⟩

end
end Barnette.Network

namespace Barnette.PlaneEmbedding
noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem exists_exact_dual (E : PlaneEmbedding G) (hG : G.Connected) :
    ∃ (P : Network V G.edgeSet) (F : Type) (_ : Fintype F) (D : Network F G.edgeSet),
      P.Realizes G ∧ P.Duality D := by
  obtain ⟨M⟩ := E.exists_lattice_minor_model
  obtain ⟨r, ⟨M'⟩⟩ := RectangularDual.lattice_minor_in_rectangle M
  exact (RectangularDual.grid_duality (2*r) (2*r)).graphMinor hG _ _ M'
end
end Barnette.PlaneEmbedding

end OAI


namespace OAI

/-! Hamiltonian cycles in cubic bipartite three-vertex-connected plane graphs. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] (N : Network V E) (D : Network F E)

theorem Duality.hamiltonian (h : N.Duality D) (hN : N.Simple)
    (hc : N.graph.IsRegularOfDegree 3) (h3 : N.ThreeEdgeConnected)
    (black : V → Prop) (hb : ∀ e, black (N.tail e) ↔ ¬black (N.head e)) :
    HasHamiltonianCycle N.graph := by
  obtain ⟨v⟩ := h.connected.nonempty
  have hs : (N.star v).Nonempty := by
    apply Finset.card_pos.mp
    rw [N.card_star hN,hc v]
    decide
  obtain ⟨e,_⟩ := hs
  obtain ⟨P,_,hP,hPc⟩ := h.connected_complement_matching N D hN hc h3 black hb e
  let H := (N.restrict (Subtype.val : ↥Pᶜ → E)).graph
  have hdeg : H.IsRegularOfDegree 2 := N.matching_complement_two hN hc P hP
  obtain ⟨p,hp⟩ := Barnette.SimpleCycle.cycle_at_of_connected_two H hPc hdeg v
  let f : H →g N.graph := {
    toFun := id
    map_rel' := by
      rintro a b ⟨hne,k,hk⟩
      exact ⟨hne,k.val,hk⟩ }
  exact ⟨v,p.map f,hp.map Function.bijective_id⟩
end
end Barnette.Network

namespace Barnette
universe u
noncomputable section
open scoped Classical
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

lemma ThreeVertexConnected.connected (h : ThreeVertexConnected G) : G.Connected := by
  let H := G.induce {v | v ∉ (∅ : Finset V)}
  let f : H →g G := { toFun := Subtype.val, map_rel' := fun h => h }
  exact (h.2 ∅ (by simp)).map f (fun v => ⟨⟨v,by simp⟩,rfl⟩)

theorem main : MainStatement.{u} := by
  intro V hV dV G dG hc hb hp h3
  have hdeq : dV = Classical.decEq V := Subsingleton.elim _ _
  subst dV
  have hdrel : dG = fun a b => Classical.propDecidable (G.Adj a b) := Subsingleton.elim _ _
  subst dG
  obtain ⟨E⟩ := hp
  have hconn := h3.connected
  let : Nonempty V := hconn.nonempty
  have horder := cubic_bipartite_order hc hb
  obtain ⟨N,F,f,D,hr,hd⟩ := E.exists_exact_dual hconn
  let : Fintype F := f
  have hN : N.Simple := by
    refine ⟨hr.loopless,?_⟩
    intro e f hef
    apply Subtype.ext
    rw [← hr e,← hr f]
    exact hef
  have hc' : N.graph.IsRegularOfDegree 3 := by rw [hr.graph_eq]; exact hc
  have h3' : ThreeVertexConnected N.graph := hr.graph_eq.symm ▸ h3
  have hec : N.ThreeEdgeConnected := by
    intro A ha ho
    obtain ⟨w,hw⟩ := ho
    exact N.cut_card_three h3' (by omega) A ha ⟨w,Finset.mem_compl.mp hw⟩
  obtain ⟨color⟩ := hb
  let black : V → Prop := fun v => color v = 0
  have hcolor (e : G.edgeSet) : black (N.tail e) ↔ ¬black (N.head e) := by
    have hne := color.valid (G.mem_edgeSet.mp ((hr e).symm ▸ e.property))
    have ht := (color (N.tail e)).isLt
    have hh := (color (N.head e)).isLt
    have hne' : (color (N.tail e)).val ≠ (color (N.head e)).val := fun h => hne (Fin.ext h)
    change color (N.tail e) = 0 ↔ ¬color (N.head e) = 0
    simp only [Fin.ext_iff,Fin.val_zero]
    omega
  have hh := hd.hamiltonian N D hN hc' hec black hcolor
  rwa [hr.graph_eq] at hh
end
end Barnette

end OAI

namespace Port9008
open OAI.Barnette OMA.S_wp_barnette_s_conjecture
open scoped unitInterval
private theorem bridge {V : Type} {G : SimpleGraph V} (hp : IsPlanar G) : Planar G := by
  classical
  obtain ⟨pos, A, hi, hinj, hend, hav, hdis⟩ := hp
  let e {v w : V} (h : G.Adj v w) : G.edgeSet := ⟨s(v,w), h⟩
  have rev {v w : V} (h : G.Adj v w) : e h.symm = e h := Subtype.ext (Sym2.eq_swap ..)
  have ends {v w : V} (h : G.Adj v w) :
      (pos v = A (e h) 0 ∧ pos w = A (e h) 1) ∨ (pos v = A (e h) 1 ∧ pos w = A (e h) 0) :=
    Sym2.eq_iff.mp (hend (e h))
  let f {v w : V} (h : G.Adj v w) : unitInterval → unitInterval :=
    if pos v = A (e h) 0 then id else unitInterval.symm
  let p {v w : V} (h : G.Adj v w) : Path (pos v) (pos w) := {
    toFun := fun t => A (e h) (f h t)
    continuous_toFun := (A (e h)).continuous.comp (by dsimp [f]; split <;> first | exact continuous_id | exact unitInterval.continuous_symm)
    source' := by
      rcases ends h with ⟨a,b⟩ | ⟨a,b⟩
      · simp [f,a]
      · have hn : pos v ≠ A (e h) 0 := fun he => h.ne (hi (he.trans b.symm))
        simp only [f,if_neg hn,unitInterval.symm_zero]; exact a.symm
    target' := by
      rcases ends h with ⟨a,b⟩ | ⟨a,b⟩
      · simp [f,a,b]
      · have hn : pos v ≠ A (e h) 0 := fun he => h.ne (hi (he.trans b.symm))
        simp [f,hn,b] }
  have interior {v w : V} (h : G.Adj v w) (t : unitInterval) (h0 : t ≠ 0) (h1 : t ≠ 1) : ((f h t : unitInterval) : ℝ) ∈ Set.Ioo 0 1 := by
    have a : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (fun he => h0 (Subtype.ext he.symm))
    have b : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 (fun he => h1 (Subtype.ext he))
    dsimp [f]; split
    · exact ⟨a,b⟩
    · exact ⟨by change 0 < 1 - (t : ℝ); linarith, by change 1 - (t : ℝ) < 1; linarith⟩
  refine ⟨⟨pos,hi,fun _ _ h => p h,?_,?_,?_,?_⟩⟩
  · intro v w h
    apply (hinj (e h)).comp
    dsimp [f]; split <;> first | exact Function.injective_id | exact unitInterval.symm_bijective.injective
  · intro v w h
    apply Path.ext; funext t
    change A (e h.symm) (f h.symm t) = A (e h) (f h (unitInterval.symm t))
    dsimp only [f]; rw [rev h]
    rcases ends h with ⟨a,b⟩ | ⟨a,b⟩
    · have hn : pos w ≠ A (e h) 0 := fun he => h.ne (hi (a.trans he.symm))
      simp [a,hn]
    · have hn : pos v ≠ A (e h) 0 := fun he => h.ne (hi (he.trans b.symm))
      simp [b,hn]
  · intro v w h t z he
    by_cases h0 : t = 0
    · subst t; exact Or.inl ⟨rfl,hi (he.symm.trans (p h).source)⟩
    by_cases h1 : t = 1
    · subst t; exact Or.inr ⟨rfl,hi (he.symm.trans (p h).target)⟩
    exact False.elim (hav _ _ (interior h t h0 h1) z he)
  · intro v w x y h k t s a b c d he
    apply Sym2.eq_iff.mp
    exact congrArg Subtype.val (show e h = e k from by by_contra hn; exact hdis _ _ hn _ _ (interior h t a b) (interior k s c d) he)
end Port9008
theorem OMA.solution : type_of% @OMA.S_wp_barnette_s_conjecture.main := by
  classical
  intro V hV dV G hc hb ht hp
  refine OAI.Barnette.main V G ?_ hb (Port9008.bridge hp) ⟨ht.1, fun X hX => ht.2 X (by omega)⟩
  intro v
  simpa [SimpleGraph.degree, SimpleGraph.neighborFinset, Set.ncard_eq_toFinset_card'] using hc v
