import OMAReductions.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1_H2_R1_H3_R1
import Mathlib

/-!
# Seven total colors for a regular multigraph with a perfect matching

A. V. Kostochka, Discrete Mathematics 162 (1996), 199–214, §§4–5.
Paper: https://kostochk.web.illinois.edu/docs/old/dm96.pdf

This file proves the transfer step in a reduction of the regular matched case.
Suppose a finite loopless 5-regular multigraph with a perfect matching has no
total coloring with seven colors. Either some multigraph of maximum degree two
on its vertices has no ordering into paths and cycles, or a pair of simple
graphs on unordered vertex pairs fails the required three-color palette lemma.

The proof at the end is by contradiction. `exists_matching_cut` chooses a
bipartition. `Rows.of_flat_rows` converts ordered components on either side
into the paths, cycles and squares of §4. In `physical_seven_from` these
pieces determine two edge factors and their exceptional pieces. The palette
lemma supplies three colors on each folded side. The local recolorings of
§5 extend these palettes, and the two triples and the seventh color
give the required coloring.

Parallel edges keep separate labels throughout the construction. In the
conclusion, the colors of all copies between two vertices form a finite set
whose cardinality is their multiplicity.
-/

section 

namespace MultFive
open Finset SimpleGraph

structure Multi (V : Type*) where
  count : V → V → ℕ
  symm : ∀ x y, count x y = count y x
  loopless : ∀ x, count x x = 0

namespace Multi
variable {V : Type*} (m : Multi V)

def degree [Fintype V] (v : V) : ℕ := ∑ w, m.count v w

def support : SimpleGraph V where
  Adj v w := 0 < m.count v w
  symm := ⟨fun v w h => by rwa [← m.symm v w]⟩
  loopless := ⟨fun x => by simp [m.loopless]⟩

instance : DecidableRel m.support.Adj := fun x y => inferInstanceAs (Decidable (0 < m.count x y))

structure Valid (vc : V → Fin 7) (ec : V → V → Finset (Fin 7)) : Prop where
  symmetric : ∀ x y, ec x y = ec y x
  size : ∀ x y, (ec x y).card = m.count x y
  vertices : ∀ x y, 0 < m.count x y → vc x ≠ vc y
  avoids : ∀ x y, vc x ∉ ec x y
  disjoint : ∀ x y z, y ≠ z → Disjoint (ec x y) (ec x z)

def Colorable : Prop := ∃ vc ec, m.Valid vc ec

end Multi

end MultFive

end

section 

namespace Kostochka.FiveRegular.Subdivision

open SimpleGraph Finset

variable {V E : Type*}

structure Family (V E : Type*) where
  left : E → V
  right : E → V

abbrev Node (V E : Type*) := V ⊕ (E ⊕ E)

private def base (v : V) : Node V E := .inl v
private def lmid (e : E) : Node V E := .inr (.inl e)
private def rmid (e : E) : Node V E := .inr (.inr e)

private def connectedPair (D : Family V E) : Node V E → Node V E → Prop
  | .inl v, .inr (.inl e) | .inr (.inl e), .inl v => v = D.left e
  | .inl v, .inr (.inr e) | .inr (.inr e), .inl v => v = D.right e
  | .inr (.inl e), .inr (.inr f) | .inr (.inr f), .inr (.inl e) => e = f
  | _, _ => False

def graph (D : Family V E) : SimpleGraph (Node V E) where
  Adj := connectedPair D
  symm.symm := by
    rintro (u|u|u) (v|v|v) <;> exact id
  loopless.irrefl := by
    rintro (v|e|e) <;> exact id

private def leftEdge (D : Family V E) (e : E) : (graph D).edgeSet :=
  ⟨s(base (D.left e), lmid e), by exact Eq.refl _⟩
private def midEdge (D : Family V E) (e : E) : (graph D).edgeSet :=
  ⟨s(lmid e, rmid e), by exact Eq.refl _⟩
private def rightEdge (D : Family V E) (e : E) : (graph D).edgeSet :=
  ⟨s(base (D.right e), rmid e), by exact Eq.refl _⟩

noncomputable def edgeEquiv (D : Family V E) : (E ⊕ (E ⊕ E)) ≃ (graph D).edgeSet := by
  classical
  let f : E ⊕ (E ⊕ E) → (graph D).edgeSet := Sum.elim (leftEdge D) (Sum.elim (midEdge D) (rightEdge D))
  apply Equiv.ofBijective f
  constructor
  · rintro (e|e|e) (e'|e'|e') h <;>
      have h' := congrArg Subtype.val h <;>
      simp_all [f, leftEdge, midEdge, rightEdge, base, lmid, rmid, Sym2.eq]
  · rintro ⟨⟨u,v⟩, hadj⟩
    have hh : (graph D).Adj u v := hadj
    rcases u with v₁ | e₁ | e₁ <;> rcases v with v₂ | e₂ | e₂ <;>
      simp only [graph, connectedPair] at hh <;> try contradiction
    · refine ⟨.inl e₂, Subtype.ext ?_⟩
      change s(base (D.left e₂),lmid e₂) = s(base v₁,lmid e₂)
      rw [hh]
    · refine ⟨.inr (.inr e₂), Subtype.ext ?_⟩
      change s(base (D.right e₂),rmid e₂) = s(base v₁,rmid e₂)
      rw [hh]
    · refine ⟨.inl e₁, Subtype.ext ?_⟩
      change s(base (D.left e₁),lmid e₁) = s(lmid e₁,base v₂)
      rw [hh, Sym2.eq_swap]
    · refine ⟨.inr (.inl e₁), Subtype.ext ?_⟩
      change s(lmid e₁,rmid e₁) = s(lmid e₁,rmid e₂)
      rw [hh]
    · refine ⟨.inr (.inr e₁), Subtype.ext ?_⟩
      change s(base (D.right e₁), rmid e₁) = s(rmid e₁, base v₂)
      rw [hh, Sym2.eq_swap]
    · refine ⟨.inr (.inl e₁), Subtype.ext ?_⟩
      change s(lmid e₁,rmid e₁) = s(rmid e₁,lmid e₂)
      rw [hh, Sym2.eq_swap]

@[simp] private theorem enum_left (D : Family V E) (e : E) :
    edgeEquiv D (.inl e) = leftEdge D e := rfl
@[simp] private theorem enum_mid (D : Family V E) (e : E) :
    edgeEquiv D (.inr (.inl e)) = midEdge D e := rfl
@[simp] private theorem enum_right (D : Family V E) (e : E) :
    edgeEquiv D (.inr (.inr e)) = rightEdge D e := rfl

instance (D : Family V E) [DecidableEq V] [DecidableEq E] : DecidableRel (graph D).Adj := by
  rintro (u|u|u) (v|v|v) <;> unfold graph <;> dsimp [connectedPair] <;> infer_instance

variable [Fintype E] [DecidableEq V] [DecidableEq E]

def coloredDegree (D : Family V E) (f : E → Bool) (v : V) (b : Bool) : ℕ :=
  (∑ e, if v = D.left e ∧ f e = b then 1 else 0) +
  (∑ e, if v = D.right e ∧ f e = b then 1 else 0)

variable [Fintype V]

def simpleDegree {W : Type*} [DecidableEq W] (G : SimpleGraph W) [Fintype G.edgeSet]
    (f : G.edgeSet → Bool) (v : W) (b : Bool) : ℕ :=
  ∑ e, if v ∈ e.val ∧ f e = b then 1 else 0

private theorem count_base (D : Family V E) (f : (graph D).edgeSet → Bool) (v : V) (b : Bool) :
    simpleDegree (graph D) f (base v) b =
      (∑ e, if v = D.left e ∧ f (leftEdge D e) = b then 1 else 0) +
      (∑ e, if v = D.right e ∧ f (rightEdge D e) = b then 1 else 0) := by
  unfold simpleDegree
  rw [← (edgeEquiv D).sum_comp, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [leftEdge, midEdge, rightEdge, Sym2.mem_iff, base, lmid, rmid, Finset.sum_boole]
  congr 1 <;> symm <;> apply Finset.sum_boole

private theorem count_lmid (D : Family V E) (f : (graph D).edgeSet → Bool) (e : E) (b : Bool) :
    simpleDegree (graph D) f (lmid e) b =
      (if f (leftEdge D e) = b then 1 else 0) + (if f (midEdge D e) = b then 1 else 0) := by
  unfold simpleDegree
  rw [← (edgeEquiv D).sum_comp, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [leftEdge, midEdge, rightEdge, Sym2.mem_iff, base, lmid, rmid, ite_and]
  congr 2

private theorem count_rmid (D : Family V E) (f : (graph D).edgeSet → Bool) (e : E) (b : Bool) :
    simpleDegree (graph D) f (rmid e) b =
      (if f (midEdge D e) = b then 1 else 0) + (if f (rightEdge D e) = b then 1 else 0) := by
  unfold simpleDegree
  rw [← (edgeEquiv D).sum_comp, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [leftEdge, midEdge, rightEdge, Sym2.mem_iff, base, lmid, rmid, ite_and]
  congr 2

theorem pullback_balanced (D : Family V E) (f : (graph D).edgeSet → Bool)
    (h : ∀ v, simpleDegree (graph D) f v true = simpleDegree (graph D) f v false) :
    ∃ g : E → Bool, ∀ v, coloredDegree D g v true = coloredDegree D g v false := by
  have agree (e : E) : f (leftEdge D e) = f (rightEdge D e) := by
    have h₁ := h (lmid e)
    have h₂ := h (rmid e)
    simp only [count_lmid, count_rmid] at h₁ h₂
    cases hl : f (leftEdge D e) <;> cases hm : f (midEdge D e) <;>
      cases hr : f (rightEdge D e) <;> simp [hl, hm, hr] at *
  refine ⟨fun e => f (leftEdge D e), fun v => ?_⟩
  simpa only [count_base, ← agree, coloredDegree] using h (base v)

def Joined (D : Family V E) (v w : V) : Prop :=
  ∃ e, (v = D.left e ∧ w = D.right e) ∨ (w = D.left e ∧ v = D.right e)

omit [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V] in
private theorem endpoint_reachable (D : Family V E) (e : E) :
    (graph D).Reachable (base (D.left e)) (base (D.right e)) := by
  have h₁ : (graph D).Adj (base (D.left e)) (lmid e) := rfl
  have h₂ : (graph D).Adj (lmid e) (rmid e) := rfl
  have h₃ : (graph D).Adj (rmid e) (base (D.right e)) := rfl
  exact h₁.reachable.trans (h₂.reachable.trans h₃.reachable)

omit [Fintype E] [Fintype V] [DecidableEq E] [DecidableEq V] in
theorem preconnected (D : Family V E)
    (h : ∀ v w, Relation.ReflTransGen (Joined D) v w) : (graph D).Preconnected := by
  have hbase (v w : V) : (graph D).Reachable (base v) (base w) := by
    induction h v w with
    | refl => exact .refl _
    | tail _ hw ih =>
      rcases hw with ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ih.trans (endpoint_reachable D e)
      · exact ih.trans (endpoint_reachable D e).symm
  have attach (x : Node V E) : ∃ v, (graph D).Reachable x (base v) := by
    rcases x with v|e|e
    · exact ⟨v, .refl _⟩
    · exact ⟨D.left e, (show (graph D).Adj (lmid e) (base (D.left e)) from rfl).reachable⟩
    · exact ⟨D.right e, (show (graph D).Adj (rmid e) (base (D.right e)) from rfl).reachable⟩
  intro x y
  obtain ⟨v, hv⟩ := attach x
  obtain ⟨w, hw⟩ := attach y
  exact hv.trans ((hbase v w).trans hw.symm)

theorem card_edges (D : Family V E) :
    Fintype.card (graph D).edgeSet = 3 * Fintype.card E := by
  rw [← Fintype.card_congr (edgeEquiv D)]
  simp [Fintype.card_sum]
  omega

private theorem simpleDegree_eq_subgraph_degree {W : Type*} [Fintype W] [DecidableEq W]
    (G H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] (hle : H ≤ G)
    (color : G.edgeSet → Bool) (b : Bool) (spec : ∀ e, color e = b ↔ e.val ∈ H.edgeSet)
    (v : W) : simpleDegree G color v b = H.degree v := by
  classical
  unfold simpleDegree
  rw [← H.card_incidenceSet_eq_degree, Finset.sum_boole, Nat.cast_id, ← Fintype.card_coe]
  apply Fintype.card_congr
  exact {
    toFun := fun e =>
      let hit := (Finset.mem_filter.mp e.property).2
      ⟨e.val.val, (spec _).mp hit.2, hit.1⟩
    invFun := fun e =>
      let edge : G.edgeSet := ⟨e.val, edgeSet_mono hle e.property.1⟩
      ⟨edge, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.property.2, (spec edge).mpr e.property.1⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem balanced_of_partition {W : Type*} [Fintype W] [DecidableEq W] (G H₁ H₂ : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H₁.Adj] [DecidableRel H₂.Adj]
    (cover : H₁ ⊔ H₂ = G) (disj : Disjoint H₁ H₂)
    (degrees : ∀ v, H₁.degree v = H₂.degree v) :
    ∃ f, ∀ v, simpleDegree G f v true = simpleDegree G f v false := by
  classical
  let f : G.edgeSet → Bool := fun e => decide (e.val ∈ H₁.edgeSet)
  have left_spec (e : G.edgeSet) : f e = true ↔ e.val ∈ H₁.edgeSet := by simp [f]
  have right_spec (e : G.edgeSet) : f e = false ↔ e.val ∈ H₂.edgeSet := by
    have hU : G.edgeSet ⊆ H₁.edgeSet ∪ H₂.edgeSet := by rw [← cover, edgeSet_sup]
    have hin : e.val ∈ H₁.edgeSet ∨ e.val ∈ H₂.edgeSet := hU e.property
    have hi : e.val ∈ H₁.edgeSet → e.val ∈ H₂.edgeSet → False :=
      fun h₁ h₂ => Set.disjoint_left.mp (disjoint_edgeSet.mpr disj) h₁ h₂
    simp only [f, decide_eq_false_iff_not]
    exact ⟨fun h => hin.resolve_left h, fun h h' => hi h' h⟩
  refine ⟨f, fun v => ?_⟩
  rw [simpleDegree_eq_subgraph_degree G H₁ (cover ▸ le_sup_left) f true left_spec,
      simpleDegree_eq_subgraph_degree G H₂ (cover ▸ le_sup_right) f false right_spec, degrees]

private theorem simpleDegree_const {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (v : W) : simpleDegree G (fun _ => true) v true = G.degree v := by
  apply simpleDegree_eq_subgraph_degree G G le_rfl
  exact fun e => ⟨fun _ => e.property, fun _ => rfl⟩

theorem even_degrees (D : Family V E)
    (h : ∀ v, Even (coloredDegree D (fun _ => true) v true)) :
    ∀ x, Even ((graph D).degree x) := by
  rintro (v|e|e) <;> rw [← simpleDegree_const]
  · change Even (simpleDegree (graph D) (fun _ => true) (base v) true)
    simpa [count_base, coloredDegree] using h v
  · change Even (simpleDegree (graph D) (fun _ => true) (lmid e) true)
    simp [count_lmid]
  · change Even (simpleDegree (graph D) (fun _ => true) (rmid e) true)
    simp [count_rmid]

end Kostochka.FiveRegular.Subdivision

end

section 

namespace Kostochka.FiveRegular

open Subdivision SimpleGraph

variable {V E : Type*}

def FamilyIncident (D : Family V E) (v : V) (e : E) : Prop :=
  v = D.left e ∨ v = D.right e

def FamilyMeet (D : Family V E) (e f : E) : Prop :=
  ∃ v, FamilyIncident D v e ∧ FamilyIncident D v f

inductive EdgePart where
  | matching
  | factor (side : Bool)
  | exceptional
  deriving DecidableEq

structure StageTwo (D : Family V E) (side : V → Bool) (part : E → EdgePart)
    (marked : V → Prop) (separate : Bool → E → E → Prop) where
  vertex : V → Fin 3
  edge : E → Fin 3
  properVertex : ∀ e, ¬marked (D.left e) → ¬marked (D.right e) →
    side (D.left e) = side (D.right e) → vertex (D.left e) ≠ vertex (D.right e)
  properEdge : ∀ b e f, part e = .factor b → part f = .factor b →
    e ≠ f → FamilyMeet D e f → edge e ≠ edge f
  properIncidence : ∀ b v e, side v = b → ¬marked v → part e = .factor b →
    FamilyIncident D v e → vertex v ≠ edge e
  properSpokes : ∀ b e f, separate b e f → edge e ≠ edge f

def contracted (D : Family V E) {Q : Type*} (q : V → Q) (part : E → EdgePart)
    (b : Bool) : Family Q {e : E // part e = .factor b} :=
  ⟨fun e => q (D.left e.val), fun e => q (D.right e.val)⟩

structure ContractedPalette (D : Family V E) (side : V → Bool) (part : E → EdgePart)
    (marked : V → Prop) (b : Bool) {Q : Type*} (q : V → Q) where
  vertex : V → Fin 3
  edge : {e : E // part e = .factor b} → Fin 3
  properVertex : ∀ e, side (D.left e) = b → side (D.right e) = b →
    ¬marked (D.left e) → ¬marked (D.right e) → vertex (D.left e) ≠ vertex (D.right e)
  properEdge : ∀ e f, e ≠ f → FamilyMeet (contracted D q part b) e f → edge e ≠ edge f
  properIncidence : ∀ v e, side v = b → ¬marked v →
    FamilyIncident (contracted D q part b) (q v) e → vertex v ≠ edge e

noncomputable def stageTwoOfContractions {D : Family V E} {side : V → Bool} {part : E → EdgePart}
    {marked : V → Prop} {separate : Bool → E → E → Prop} {Q : Bool → Type*}
    (q : (b : Bool) → V → Q b)
    (P : ∀ b, ContractedPalette D side part marked b (q b))
    (spokes : ∀ b e f, separate b e f → ∃ (he : part e = .factor b) (hf : part f = .factor b),
      e ≠ f ∧ FamilyMeet (contracted D (q b) part b) ⟨e, he⟩ ⟨f, hf⟩) :
    StageTwo D side part marked separate := by
  classical
  let vc (v : V) := (P (side v)).vertex v
  let ec (e : E) := match h : part e with
    | .factor b => (P b).edge ⟨e, h⟩
    | _ => 0
  have hcol (b : Bool) (e : E) (he : part e = .factor b) : ec e = (P b).edge ⟨e, he⟩ := by
    dsimp only [ec]
    split <;> rename_i h
    · have eq := EdgePart.factor.inj (h.symm.trans he)
      subst b
      rfl
    all_goals simp_all
  have incident (b : Bool) (v : V) (e : E) (he : part e = .factor b)
      (hv : FamilyIncident D v e) :
      FamilyIncident (contracted D (q b) part b) (q b v) ⟨e, he⟩ := by
    rcases hv with h | h
    · exact Or.inl (congrArg (q b) h)
    · exact Or.inr (congrArg (q b) h)
  refine ⟨vc, ec, ?_, ?_, ?_, ?_⟩
  · intro e hl hr hs
    intro hv
    apply (P (side (D.left e))).properVertex e rfl hs.symm hl hr
    exact hv.trans (congrArg (fun b => (P b).vertex (D.right e)) hs.symm)
  · intro b e f he hf hne hm
    obtain ⟨v, hve, hvf⟩ := hm
    rw [hcol b e he, hcol b f hf]
    exact (P b).properEdge _ _ (fun eq => hne (congrArg Subtype.val eq))
      ⟨q b v, incident _ _ _ _ hve, incident _ _ _ _ hvf⟩
  · intro b v e hs hfree he hv
    intro eq
    exact (P b).properIncidence v ⟨e, he⟩ hs hfree (incident _ _ _ _ hv)
      (((congrArg (fun d => (P d).vertex v) hs.symm).trans eq).trans (hcol b e he))
  · intro b e f h
    obtain ⟨he, hf, hn, hm⟩ := spokes b e f h
    rw [hcol b e he, hcol b f hf]
    exact (P b).properEdge _ _ (fun eq => hn (congrArg Subtype.val eq)) hm

structure CompletedLayers (D : Family V E) (side : V → Bool) (layer : E → Option Bool) where
  vertex : V → Fin 3
  edge : E → Fin 3
  properVertex : ∀ e, side (D.left e) = side (D.right e) →
    vertex (D.left e) ≠ vertex (D.right e)
  properEdge : ∀ b e f, layer e = some b → layer f = some b →
    e ≠ f → FamilyMeet D e f → edge e ≠ edge f
  properIncidence : ∀ v e, layer e = some (side v) → FamilyIncident D v e → vertex v ≠ edge e

private def palette (b : Bool) (c : Fin 3) : Fin 7 :=
  if b then ⟨c.val + 3, by omega⟩ else ⟨c.val, by omega⟩

private theorem palette_eq {b d : Bool} {c e : Fin 3} :
    palette b c = palette d e ↔ b = d ∧ c = e := by
  cases b <;> cases d <;> simp [palette, Fin.ext_iff] <;> omega

private theorem palette_ne_top (b : Bool) (c : Fin 3) : palette b c ≠ 6 := by
  cases b <;> simp [palette, Fin.ext_iff] <;> omega

def ProperTotal (D : Family V E) (vertex : V → Fin 7) (edge : E → Fin 7) : Prop :=
  (∀ e, vertex (D.left e) ≠ vertex (D.right e)) ∧
  (∀ e f, e ≠ f → FamilyMeet D e f → edge e ≠ edge f) ∧
  (∀ v e, FamilyIncident D v e → vertex v ≠ edge e)

theorem CompletedLayers.total {D : Family V E} {side : V → Bool} {layer : E → Option Bool}
    (P : CompletedLayers D side layer)
    (matching : ∀ e f, layer e = none → layer f = none → FamilyMeet D e f → e = f) :
    ∃ vertex edge, ProperTotal D vertex edge := by
  let ec e := match layer e with
    | some b => palette b (P.edge e)
    | none => 6
  refine ⟨fun v => palette (side v) (P.vertex v), ec, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨hs, hv⟩ := palette_eq.mp he
    exact P.properVertex e hs hv
  · intro e f hne hm he
    cases hl : layer e with
    | none =>
      cases hr : layer f with
      | none => exact hne (matching e f hl hr hm)
      | some d => exact palette_ne_top d _ (by simpa [ec, hl, hr] using he.symm)
    | some b =>
      cases hr : layer f with
      | none => exact palette_ne_top b _ (by simpa [ec, hl, hr] using he)
      | some d =>
        obtain ⟨rfl, h⟩ := palette_eq.mp (by simpa [ec, hl, hr] using he)
        exact P.properEdge b e f hl hr hne hm h
  · intro v e hm he
    cases hl : layer e with
    | none => exact palette_ne_top _ _ (by simpa [ec, hl] using he)
    | some b =>
      obtain ⟨h, h'⟩ := palette_eq.mp (by simpa [ec, hl] using he)
      exact P.properIncidence v e (h ▸ hl) hm h'

end Kostochka.FiveRegular

end

section 

namespace MultFive.Multi
open Finset SimpleGraph Kostochka.FiveRegular Subdivision
variable {V : Type*} (m : Multi V)

def copies : Sym2 V → ℕ := Sym2.lift ⟨m.count,m.symm⟩

abbrev Edge := Σ p : Sym2 V, Fin (m.copies p)

noncomputable def family : Family V m.Edge where
  left e := e.1.out.1
  right e := e.1.out.2

theorem family_pair (e : m.Edge) : s(m.family.left e, m.family.right e) = e.1 := e.1.out_eq

theorem family_incident_iff (v : V) (e : m.Edge) : FamilyIncident m.family v e ↔ v ∈ e.1 := by
  rw [← m.family_pair e, Sym2.mem_iff]; rfl

theorem family_loopless (e : m.Edge) : m.family.left e ≠ m.family.right e := by
  intro eq
  have h : 0 < m.copies e.1 := Nat.zero_lt_of_lt e.2.isLt
  rw [← m.family_pair e, eq] at h
  exact (m.loopless _ ▸ h : 0 < 0).false

private noncomputable def bag (ec : m.Edge → Fin 7) (p : Sym2 V) : Finset (Fin 7) :=
  univ.image (fun i : Fin (m.copies p) => ec ⟨p,i⟩)

theorem colorable_of_family (vc : V → Fin 7) (ec : m.Edge → Fin 7)
    (vertices : ∀ e, vc (m.family.left e) ≠ vc (m.family.right e))
    (edges : ∀ e f, e ≠ f → FamilyMeet m.family e f → ec e ≠ ec f)
    (avoids : ∀ v e, FamilyIncident m.family v e → vc v ≠ ec e) : m.Colorable := by
  classical
  refine ⟨vc, fun x y => m.bag ec s(x,y), ?_⟩
  constructor
  · intro x y; rw [Sym2.eq_swap]
  · intro x y
    unfold bag
    rw [card_image_of_injective]
    · exact Fintype.card_fin _
    · intro i j eq
      by_contra ne
      have diff : (⟨s(x,y),i⟩ : m.Edge) ≠ ⟨s(x,y),j⟩ := fun h => ne (by simpa using h)
      exact edges _ _ diff ⟨x, (m.family_incident_iff _ _).mpr (Sym2.mem_mk_left _ _),
        (m.family_incident_iff _ _).mpr (Sym2.mem_mk_left _ _)⟩ eq
  · intro x y hp
    let e : m.Edge := ⟨s(x,y), ⟨0, hp⟩⟩
    have h := vertices e
    obtain ⟨hx,hy⟩ | ⟨hy,hx⟩ := Sym2.eq_iff.mp (m.family_pair e)
    · simpa [hx,hy] using h
    · simpa [hx,hy] using h.symm
  · intro x y hx
    obtain ⟨i,_,hi⟩ := mem_image.mp hx
    exact avoids x ⟨s(x,y),i⟩ ((m.family_incident_iff _ _).mpr (Sym2.mem_mk_left _ _)) hi.symm
  · intro x y z ne
    apply Finset.disjoint_left.mpr
    intro hue h₁ h₂
    obtain ⟨i,_,e₁⟩ := Finset.mem_image.mp h₁
    obtain ⟨j,_,e₂⟩ := Finset.mem_image.mp h₂
    let e : m.Edge := ⟨s(x,y),i⟩
    let f : m.Edge := ⟨s(x,z),j⟩
    have diff : e ≠ f := by
      intro eq
      have pair : s(x,y) = s(x,z) := congrArg Sigma.fst eq
      rcases Sym2.eq_iff.mp pair with h | h <;> grind
    exact edges e f diff ⟨x, (m.family_incident_iff _ _).mpr (Sym2.mem_mk_left _ _),
      (m.family_incident_iff _ _).mpr (Sym2.mem_mk_left _ _)⟩ (e₁.trans e₂.symm)

end MultFive.Multi

namespace MultFive
open SimpleGraph

end MultFive

end

section 

namespace Kostochka.FiveRegular

theorem exists_third_color (a b : Fin 3) : ∃ c : Fin 3, c ≠ a ∧ c ≠ b := by
  fin_cases a <;> fin_cases b <;> decide

theorem color_upper_seam (left middle right : Fin 3) (h : left ≠ right) :
    ∃ x y : Fin 3, x ≠ left ∧ x ≠ middle ∧ y ≠ middle ∧ y ≠ right ∧ x ≠ y := by
  fin_cases left <;> fin_cases middle <;> fin_cases right <;> first | contradiction | decide

theorem color_lower_pair (previous forbidLeftSpoke forbidRightSpoke : Fin 3) :
    ∃ left right edge : Fin 3, left ≠ previous ∧ left ≠ right ∧
      right ≠ forbidLeftSpoke ∧ left ≠ forbidRightSpoke ∧ edge ≠ left ∧ edge ≠ right := by
  obtain ⟨left, hlp, hlr⟩ := exists_third_color previous forbidRightSpoke
  obtain ⟨right, hrl, hr⟩ := exists_third_color left forbidLeftSpoke
  obtain ⟨edge, hel, her⟩ := exists_third_color left right
  exact ⟨left, right, edge, hlp, hrl.symm, hr, hlr, hel, her⟩

theorem finish_lower_seam (left right outside : Fin 3) :
    ∃ vertex spoke : Fin 3, vertex ≠ left ∧ vertex ≠ right ∧
      spoke ≠ vertex ∧ spoke ≠ outside := by
  obtain ⟨vertex, hl, hr⟩ := exists_third_color left right
  obtain ⟨spoke, hv, hout⟩ := exists_third_color vertex outside
  exact ⟨vertex, spoke, hl, hr, hv, hout⟩

theorem color_bad_path (a b outside₃ outside₄ : Fin 3)
    (outside₂ : Fin 3 → Fin 3 → Fin 3) (upper₁ upper₂ upper₃ : Fin 3)
    (hu : upper₁ ≠ upper₃) :
    ∃ v₁ v₂ v₃ v₄ spoke₂ lower₃₄ upper₁₂ upper₂₃ : Fin 3,
      v₁ ≠ a ∧ v₁ ≠ b ∧ v₁ ≠ v₂ ∧ v₂ ≠ v₃ ∧ v₃ ≠ v₄ ∧ v₄ ≠ v₁ ∧
      spoke₂ ≠ v₂ ∧ spoke₂ ≠ outside₂ v₄ v₃ ∧ v₄ ≠ outside₃ ∧ v₃ ≠ outside₄ ∧
      lower₃₄ ≠ v₃ ∧ lower₃₄ ≠ v₄ ∧
      upper₁₂ ≠ upper₁ ∧ upper₁₂ ≠ upper₂ ∧ upper₂₃ ≠ upper₂ ∧
      upper₂₃ ≠ upper₃ ∧ upper₁₂ ≠ upper₂₃ := by
  obtain ⟨v₁, ha, hb⟩ := exists_third_color a b
  obtain ⟨v₄, v₃, e₃₄, h₄₁, h₄₃, h₃, h₄, he₄, he₃⟩ := color_lower_pair v₁ outside₄ outside₃
  obtain ⟨v₂, s₂, h₂₁, h₂₃, hs₂, hs⟩ := finish_lower_seam v₁ v₃ (outside₂ v₄ v₃)
  obtain ⟨e₁₂, e₂₃, hl, hml, hmr, hr, hlr⟩ := color_upper_seam _ _ _ hu
  exact ⟨v₁, v₂, v₃, v₄, s₂, e₃₄, e₁₂, e₂₃, ha, hb, h₂₁.symm, h₂₃, h₄₃.symm,
    h₄₁, hs₂, hs, h₄, h₃, he₃, he₄, hl, hml, hmr, hr, hlr⟩

private noncomputable def third (a b : Fin 3) := (exists_third_color a b).choose

private theorem third_ne_left (a b : Fin 3) : third a b ≠ a :=
  (exists_third_color a b).choose_spec.1
private theorem third_ne_right (a b : Fin 3) : third a b ≠ b :=
  (exists_third_color a b).choose_spec.2

abbrev SpokeNeighbor (n : ℕ) := Fin n → Fin n ⊕ Fin 3

private noncomputable def bodyColor {n : ℕ} (other : SpokeNeighbor n) (i : Fin n) : Fin 3 :=
  third (if h : 0 < i.val then bodyColor other ⟨i.val - 1, by omega⟩ else 0)
    (match other i with
     | .inr b => b
     | .inl j => if j < i then bodyColor other j else 0)
termination_by i.val
decreasing_by all_goals omega

theorem color_path_and_spokes {n : ℕ} (other : SpokeNeighbor n)
    (symm : ∀ i j, other i = .inl j → other j = .inl i)
    (loopless : ∀ i, other i ≠ .inl i) :
    ∃ f : Fin n → Fin 3,
      (∀ i j, i.val + 1 = j.val → f i ≠ f j) ∧
      (∀ i j, other i = .inl j → f i ≠ f j) ∧
      (∀ i b, other i = .inr b → f i ≠ b) := by
  refine ⟨bodyColor other, ?_, ?_, ?_⟩
  · intro i j h
    have hj : 0 < j.val := by omega
    have hij : (⟨j.val - 1, by omega⟩ : Fin n) = i := by
      apply Fin.ext
      change j.val - 1 = i.val
      omega
    rw [bodyColor.eq_def other j, dif_pos hj, hij]
    exact (third_ne_left _ _).symm
  · have prior (i j : Fin n) (hm : other i = .inl j) (hlt : j < i) :
        bodyColor other i ≠ bodyColor other j := by
      rw [bodyColor.eq_def other i]
      simpa only [hm, if_pos hlt] using @third_ne_right
        (if h : 0 < i.val then bodyColor other ⟨i.val - 1, by omega⟩ else 0) (bodyColor other j)
    intro i j h
    rcases lt_trichotomy i j with hlt | rfl | hlt
    · exact (prior j i (symm i j h) hlt).symm
    · exact (loopless i h).elim
    · exact prior i j h hlt
  · intro i b h
    rw [bodyColor.eq_def other i]
    simp only [h]
    exact third_ne_right _ _

def pairMate {t : ℕ} (i : Fin (2*t)) : Fin (2*t) :=
  if h : i.val % 2 = 0 then ⟨i.val+1, by have hi := i.isLt; omega⟩ else ⟨i.val-1, by have hi := i.isLt; omega⟩

private theorem pairMate_step {t : ℕ} (i : Fin (2*t)) :
    i.val+1 = (pairMate i).val ∨ (pairMate i).val+1 = i.val := by
  unfold pairMate
  split
  · exact Or.inl rfl
  · exact Or.inr (by change i.val - 1 + 1 = i.val; omega)

private theorem pairMate_val {t : ℕ} (i : Fin (2*t)) :
    (pairMate i).val = if i.val % 2 = 0 then i.val+1 else i.val-1 := by
  by_cases h : i.val % 2 = 0 <;> simp [pairMate, h]

@[simp] theorem pairMate_pairMate {t : ℕ} (i : Fin (2*t)) : pairMate (pairMate i) = i := by
  apply Fin.ext
  simp only [pairMate_val]
  split_ifs <;> omega

private theorem third_comm (a b : Fin 3) : third a b = third b a := by
  by_cases h : a = b
  · rw [h]
  · have uniq : ∀ x y c d : Fin 3, x ≠ y → c ≠ x → c ≠ y → d ≠ x → d ≠ y → c = d := by decide
    exact uniq a b _ _ h (third_ne_left a b) (third_ne_right a b) (third_ne_right b a) (third_ne_left b a)

theorem color_odd_cycle_lower {t : ℕ} (ht : 0 < t)
    (other : SpokeNeighbor (2*t))
    (symm : ∀ i j, other i = .inl j → other j = .inl i)
    (loopless : ∀ i, other i ≠ .inl i)
    (seamNeighbor : (Fin (2*t) → Fin 3) → Fin 3) :
    ∃ (vertex spoke edge : Fin (2*t) → Fin 3) (seam seamSpoke : Fin 3),
      (∀ i j, i.val+1 = j.val → vertex i ≠ vertex j) ∧
      (∀ i, spoke i ≠ vertex i ∧ edge i ≠ vertex i ∧ edge i ≠ spoke i ∧
        edge i = edge (pairMate i) ∧ spoke i = vertex (pairMate i)) ∧
      (∀ i j, other i = .inl j → spoke i ≠ spoke j) ∧
      (∀ i b, other i = .inr b → spoke i ≠ b) ∧
      seam ≠ vertex ⟨0, by omega⟩ ∧ seam ≠ vertex ⟨2*t-1, by omega⟩ ∧
      seamSpoke ≠ seam ∧ seamSpoke ≠ seamNeighbor spoke := by
  let conjugate : SpokeNeighbor (2*t) :=
    fun i => Sum.map pairMate id (other (pairMate i))
  have csymm (i j : Fin (2*t)) (h : conjugate i = .inl j) : conjugate j = .inl i := by
    cases h₁ : other (pairMate i) with
    | inr b => simp [conjugate, h₁] at h
    | inl k =>
      simp only [conjugate, h₁, Sum.map_inl, Sum.inl.injEq] at h
      subst j
      simp [conjugate, symm _ _ h₁]
  have cfree (i : Fin (2*t)) : conjugate i ≠ .inl i := by
    intro h
    cases h₁ : other (pairMate i) with
    | inr b => simp [conjugate, h₁] at h
    | inl k =>
      simp only [conjugate, h₁, Sum.map_inl, Sum.inl.injEq] at h
      have hk : k = pairMate i := by simpa using congrArg pairMate h
      exact loopless (pairMate i) (hk ▸ h₁)
  obtain ⟨c, hpath, hpair, hfixed⟩ := color_path_and_spokes conjugate csymm cfree
  let spoke : Fin (2*t) → Fin 3 := fun i => c (pairMate i)
  let edge : Fin (2*t) → Fin 3 := fun i => third (c i) (spoke i)
  obtain ⟨s, ss, hsl, hsr, hs, hsn⟩ := finish_lower_seam
    (c ⟨0, by omega⟩) (c ⟨2*t-1, by omega⟩) (seamNeighbor spoke)
  refine ⟨c, spoke, edge, s, ss, hpath, ?_, ?_, ?_, hsl, hsr, hs, hsn⟩
  · intro i
    have hne : spoke i ≠ c i := by
      rcases pairMate_step i with h | h
      · exact (hpath _ _ h).symm
      · exact hpath _ _ h
    refine ⟨hne, third_ne_left _ _, third_ne_right _ _, ?_, rfl⟩
    simpa only [edge, spoke, pairMate_pairMate] using third_comm (c i) (c (pairMate i))
  · intro i j h
    apply hpair
    simp [conjugate, h]
  · intro i b h
    apply hfixed
    simp [conjugate, h]

end Kostochka.FiveRegular

end

section 

namespace Kostochka.FiveRegular
open SimpleGraph

variable {I E : Type*}

def ProperLabels (G : SimpleGraph E) (c : E → Fin 3) : Prop :=
  ∀ e f, G.Adj e f → c e ≠ c f

theorem update_spokes (G : SimpleGraph E) (spoke : I ↪ E) (initial : E → Fin 3)
    (valid : ProperLabels G initial)
    (unique : ∀ i x y, G.Adj (spoke i) x → G.Adj (spoke i) y → x = y)
    (goal : (I → Fin 3) → Prop)
    (solve : ∀ other : I → I ⊕ Fin 3,
      (∀ i j, other i = .inl j → other j = .inl i) →
      (∀ i, other i ≠ .inl i) →
      ∃ color : I → Fin 3, goal color ∧
        (∀ i j, other i = .inl j → color i ≠ color j) ∧
        (∀ i b, other i = .inr b → color i ≠ b)) :
    ∃ c : E → Fin 3, ProperLabels G c ∧ goal (c ∘ spoke) ∧
      ∀ e, e ∉ Set.range spoke → c e = initial e := by
  classical
  let other (i : I) : I ⊕ Fin 3 :=
    if h : ∃ j, G.Adj (spoke i) (spoke j) then .inl h.choose
    else if hh : ∃ e, G.Adj (spoke i) e then .inr (initial hh.choose) else .inr 0
  have internal (i j : I) : other i = .inl j ↔ G.Adj (spoke i) (spoke j) := by
    by_cases h : ∃ j, G.Adj (spoke i) (spoke j)
    · simp only [other,dif_pos h,Sum.inl.injEq]
      exact ⟨fun eq => eq ▸ h.choose_spec, fun hit => spoke.injective (unique i _ _ h.choose_spec hit)⟩
    · constructor
      · intro he
        dsimp only [other] at he
        rw [dif_neg h] at he
        split at he <;> contradiction
      · exact fun he => (h ⟨j,he⟩).elim
  have external (i : I) (e : E) (outside : e ∉ Set.range spoke) (he : G.Adj (spoke i) e) :
      other i = .inr (initial e) := by
    have h : ¬ ∃ j, G.Adj (spoke i) (spoke j) := by
      rintro ⟨j,hj⟩
      exact outside ⟨j,unique _ _ _ hj he⟩
    have hh : ∃ x, G.Adj (spoke i) x := ⟨e,he⟩
    simp only [other,dif_neg h,dif_pos hh,Sum.inr.injEq]
    exact congrArg initial (unique _ _ _ hh.choose_spec he)
  obtain ⟨paint,ok,adj,ext⟩ := solve other
    (fun i j h => (internal j i).mpr ((internal i j).mp h).symm)
    (fun i h => ((internal i i).mp h).ne rfl)
  let c (e : E) := if h : e ∈ Set.range spoke then paint h.choose else initial e
  have inside (i : I) : c (spoke i) = paint i := by
    have hit : spoke i ∈ Set.range spoke := ⟨i,rfl⟩
    simp only [c,dif_pos hit]
    exact congrArg paint (spoke.injective hit.choose_spec)
  have unchanged (e : E) (h : e ∉ Set.range spoke) : c e = initial e := by
    dsimp only [c]
    rw [dif_neg h]
  refine ⟨c,?_,(show c ∘ spoke = paint from funext inside) ▸ ok,unchanged⟩
  intro e f h
  by_cases eIn : e ∈ Set.range spoke <;> by_cases fIn : f ∈ Set.range spoke
  · obtain ⟨i,rfl⟩ := eIn
    obtain ⟨j,rfl⟩ := fIn
    rw [inside,inside]
    exact adj i j ((internal _ _).mpr h)
  · obtain ⟨i,rfl⟩ := eIn
    rw [inside,unchanged f fIn]
    exact ext _ _ (external _ _ fIn h)
  · obtain ⟨j,rfl⟩ := fIn
    rw [unchanged e eIn,inside]
    exact (ext _ _ (external _ _ eIn h.symm)).symm
  · rw [unchanged _ eIn,unchanged _ fIn]
    exact valid _ _ h

def OddLowerDone {t : ℕ} (ht : 0 < t) (spoke : Option (Fin (2*t)) → Fin 3) : Prop :=
  ∃ (v edge : Fin (2*t) → Fin 3) (seam : Fin 3),
    (∀ i j, i.val+1 = j.val → v i ≠ v j) ∧
    (∀ i, spoke (some i) ≠ v i ∧ edge i ≠ v i ∧ edge i ≠ spoke (some i) ∧
      edge i = edge (pairMate i) ∧ spoke (some i) = v (pairMate i)) ∧
    seam ≠ v ⟨0,by omega⟩ ∧ seam ≠ v ⟨2*t-1,by omega⟩ ∧ spoke none ≠ seam

theorem update_odd_cycle {t : ℕ} (ht : 0 < t) (G : SimpleGraph E)
    (spoke : Option (Fin (2*t)) ↪ E) (c : E → Fin 3) (valid : ProperLabels G c)
    (unique : ∀ i x y, G.Adj (spoke i) x → G.Adj (spoke i) y → x = y) :
    ∃ f, ProperLabels G f ∧ OddLowerDone ht (f ∘ spoke) ∧
      ∀ e, e ∉ Set.range spoke → f e = c e := by
  apply update_spokes G spoke c valid unique
  intro other symm noloop
  let body (i : Fin (2*t)) : Fin (2*t) ⊕ Fin 3 := match other (some i) with
    | .inl (some j) => .inl j
    | .inr b => .inr b
    | .inl none => .inr 0
  have body_in (i j) : body i = .inl j ↔ other (some i) = .inl (some j) := by
    cases h : other (some i) with
    | inr b => simp [body,h]
    | inl u => cases u <;> simp [body,h]
  let outside (s : Fin (2*t) → Fin 3) := match other none with
    | .inl (some j) => s j
    | .inr b => b
    | .inl none => 0
  obtain ⟨v,s,e,z,ss,adj,within,links,fix,hL,hR,hs,hext⟩ :=
    color_odd_cycle_lower ht body (fun i j h => (body_in j i).mpr (symm _ _ ((body_in i j).mp h)))
      (fun i h => noloop _ ((body_in i i).mp h)) outside
  let recolor := fun (i : Option (Fin (2*t))) => i.elim ss s
  refine ⟨recolor, ⟨v,e,z,adj,within,hL,hR,hs⟩,?_,?_⟩
  · rintro (_|i) (_|j) hj
    · exact (noloop none hj).elim
    · simpa [recolor,outside,hj] using hext
    · have h' := symm _ _ hj
      exact (show ss ≠ s i by simpa [outside,h'] using hext).symm
    · exact links _ _ ((body_in _ _).mpr hj)
  · rintro (_|i) b h
    · simpa [outside,h,recolor] using hext
    · exact fix i b (by simp [body,h])

end Kostochka.FiveRegular

end

section 

namespace Kostochka.FiveRegular

open SimpleGraph

def patchLow (c : Fin 3) : Fin 7 := ⟨c.val, by omega⟩
def patchHigh (c : Fin 3) : Fin 7 := ⟨3+c.val, by omega⟩

private theorem body_nodup (v s e a b : Fin 3) (hs : s ≠ v)
    (hev : e ≠ v) (hes : e ≠ s) (hb : b ≠ a) :
    [patchLow v,patchLow s,patchLow e,patchHigh a,patchHigh b,6].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, ne_eq, Fin.ext_iff, patchLow, patchHigh] at *
  norm_num
  omega

private theorem seam_nodup (v s a b c : Fin 3) (hs : s ≠ v)
    (hba : b ≠ a) (hca : c ≠ a) (hbc : b ≠ c) :
    [patchLow v,patchLow s,patchHigh a,patchHigh b,patchHigh c,6].Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, ne_eq, Fin.ext_iff, patchLow, patchHigh] at *
  norm_num
  omega

def upperGap {t : ℕ} (i : Fin (2*t)) : Fin (t+1) :=
  ⟨(i.val+1)/2, by have hi := i.isLt; omega⟩

private theorem upper_edges {t : ℕ} (ht : 0 < t) (upper : Option (Fin (2*t)) → Fin 3)
    (sep : upper (some ⟨2*t-1,by omega⟩) ≠ upper (some ⟨0,by omega⟩)) :
    ∃ color : Fin (t+1) → Fin 3,
      (∀ i, color (upperGap i) ≠ upper (some i)) ∧
      color 0 ≠ upper none ∧ color (Fin.last t) ≠ upper none ∧ color 0 ≠ color (Fin.last t) := by
  classical
  obtain ⟨last,first,hLast,hLastSeam,hFirstSeam,hFirst,hDistinct⟩ :=
    color_upper_seam _ (upper none) _ sep
  let color (k : Fin (t+1)) : Fin 3 :=
    if h₀ : k.val = 0 then first
    else if hₜ : k.val = t then last
    else (exists_third_color (upper (some ⟨2*k.val-1,by have hk := k.isLt; omega⟩))
      (upper (some ⟨2*k.val,by have hk := k.isLt; omega⟩))).choose
  have first_eq : color 0 = first := by simp [color]
  have last_eq : color (Fin.last t) = last := by simp [color, Nat.ne_of_gt ht]
  refine ⟨color,?_,first_eq ▸ hFirstSeam,last_eq ▸ hLastSeam,?_⟩
  · intro i
    have hi := i.isLt
    by_cases hf : (upperGap i).val = 0
    · have hi₀ : i = ⟨0,by omega⟩ := by
        apply Fin.ext
        change (i.val+1)/2 = 0 at hf
        change i.val = 0
        omega
      dsimp only [color]
      rw [dif_pos hf,hi₀]
      exact hFirst
    by_cases hl : (upperGap i).val = t
    · have hiₜ : i = ⟨2*t-1,by omega⟩ := by
        apply Fin.ext
        change (i.val+1)/2 = t at hl
        change i.val = 2*t-1
        omega
      dsimp only [color]
      rw [dif_neg hf,dif_pos hl,hiₜ]
      exact hLast
    let k := upperGap i
    let left : Fin (2*t) := ⟨2*k.val-1,by have hk := k.isLt; change k.val ≠ t at hl; omega⟩
    let right : Fin (2*t) := ⟨2*k.val,by have hk := k.isLt; change k.val ≠ t at hl; omega⟩
    have hit : i = left ∨ i = right := by
      suffices i.val = 2*((i.val+1)/2)-1 ∨ i.val = 2*((i.val+1)/2) from
        this.imp Fin.ext Fin.ext
      omega
    dsimp only [color]
    rw [dif_neg hf, dif_neg hl]
    have avoid := (exists_third_color (upper (some left)) (upper (some right))).choose_spec
    exact hit.elim (fun h => (congrArg (fun z => upper (some z)) h).symm ▸ avoid.1)
      (fun h => (congrArg (fun z => upper (some z)) h).symm ▸ avoid.2)
  · rw [first_eq,last_eq]
    exact hDistinct.symm

def OddDone {t : ℕ} (ht : 0 < t) (upper low : Option (Fin (2*t)) → Fin 3) : Prop :=
  ∃ (vertex : Option (Fin (2*t)) → Fin 3) (lowEdge : Fin (2*t) → Fin 3) (cut : Fin (t+1) → Fin 3),
    (∀ i j : Fin (2*t), i.val+1 = j.val → vertex (some i) ≠ vertex (some j)) ∧
    vertex none ≠ vertex (some ⟨0,by omega⟩) ∧ vertex none ≠ vertex (some ⟨2*t-1,by omega⟩) ∧
    (∀ i, lowEdge i = lowEdge (pairMate i) ∧ low (some i) = vertex (some (pairMate i))) ∧
    (∀ i, [patchLow (vertex (some i)), patchLow (low (some i)), patchLow (lowEdge i),
      patchHigh (upper (some i)), patchHigh (cut (upperGap i)), 6].Nodup) ∧
    [patchLow (vertex none),patchLow (low none),patchHigh (upper none),
      patchHigh (cut 0),patchHigh (cut (Fin.last t)),6].Nodup

theorem finish_odd {t : ℕ} (ht : 0 < t) (upper low : Option (Fin (2*t)) → Fin 3)
    (sep : upper (some ⟨2*t-1,by omega⟩) ≠ upper (some ⟨0,by omega⟩))
    (done : OddLowerDone ht low) : OddDone ht upper low := by
  obtain ⟨v,e,s,adj,body,hf,hl,hs⟩ := done
  obtain ⟨cut,hcut,cf,cl,hfl⟩ := upper_edges ht upper sep
  refine ⟨fun i => i.elim s v,e,cut,adj,hf,hl,fun i => (body i).2.2.2,?_,?_⟩
  · intro i
    exact body_nodup _ _ _ _ _ (body i).1 (body i).2.1 (body i).2.2.1 (hcut i)
  · exact seam_nodup _ _ _ _ _ hs cf cl hfl

end Kostochka.FiveRegular

end

section 

namespace Kostochka.FiveRegular

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

private def high (c : Fin 3) : Fin 7 := ⟨3 + c.val, by omega⟩

def SquareCompatible (boundary : Fin 4 → Fin 3)
    (vertex spoke edge : Fin 4 → Fin 7) : Prop :=
  ∀ i, vertex i < 3 ∧ spoke i < 3 ∧ vertex i ≠ vertex (i + 1) ∧
    spoke i ≠ spoke (i + 2) ∧
    [vertex i, spoke i, edge i, edge (i + 3), high (boundary i), 6].Nodup

private def upperPath (w x y z : Fin 3) : Prop :=
  ∃ a b c : Fin 3, a ≠ w ∧ a ≠ x ∧ b ≠ x ∧ b ≠ y ∧ c ≠ y ∧ c ≠ z ∧ a ≠ b ∧ b ≠ c

set_option maxRecDepth 10000 in
set_option synthInstance.maxSize 10000 in
private theorem upperPath_rotation : ∀ w x y z : Fin 3, w ≠ y → x ≠ z →
    upperPath w x y z ∨ upperPath x y z w := by
  intro w x y z h₁ h₂
  unfold upperPath
  fin_cases w <;> fin_cases x <;> fin_cases y <;> fin_cases z <;> first | contradiction | decide

private theorem patch_upperPath (w x y z : Fin 3) (hp : upperPath w x y z) :
    ∃ vertex spoke edge, SquareCompatible ![w, x, y, z] vertex spoke edge := by
  obtain ⟨a, b, c, haw, hax, hbx, hby, hcy, hcz, hab, hbc⟩ := hp
  refine ⟨![1, 2, 1, 2], ![2, 0, 0, 1], ![high a, high b, high c, 0], ?_⟩
  intro i
  fin_cases i <;> dsimp <;> simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or, List.nodup_nil, and_true] <;> simp only [ne_eq, Fin.ext_iff] at * <;>
    norm_num [high, Fin.lt_def] <;> (repeat' constructor) <;> omega

private theorem rotate_back {B : Fin 4 → Fin 3} {v s e : Fin 4 → Fin 7}
    (h : SquareCompatible (fun i => B (i + 1)) v s e) :
    SquareCompatible B (fun i => v (i + 3)) (fun i => s (i + 3)) (fun i => e (i + 3)) := by
  intro i
  fin_cases i <;> first | exact h 3 | exact h 0 | exact h 1 | exact h 2

theorem color_exceptional_square (B : Fin 4 → Fin 3)
    (h₀₂ : B 0 ≠ B 2) (h₁₃ : B 1 ≠ B 3) :
    ∃ vertex spoke edge, SquareCompatible B vertex spoke edge := by
  rcases upperPath_rotation _ _ _ _ h₀₂ h₁₃ with h | h
  · have he : B = ![B 0, B 1, B 2, B 3] := by funext i; fin_cases i <;> rfl
    simpa only [← he] using patch_upperPath _ _ _ _ h
  · have he : (fun i : Fin 4 => B (i + 1)) = ![B 1, B 2, B 3, B 0] := by
      funext i
      fin_cases i <;> rfl
    obtain ⟨v, s, e, hp⟩ := patch_upperPath _ _ _ _ h
    rw [← he] at hp
    exact ⟨_, _, _, rotate_back hp⟩

end Kostochka.FiveRegular

end

section 

namespace Kostochka.FiveRegular

open SimpleGraph

variable {E : Type*}

def BadPathDone (a b : Fin 3) (upper : Fin 3 → Fin 3) (spoke : Fin 3 → Fin 3) : Prop :=
  ∃ v₁ v₂ v₃ v₄ lower₃₄ upper₁₂ upper₂₃ : Fin 3,
    v₁ ≠ a ∧ v₁ ≠ b ∧ v₁ ≠ v₂ ∧ v₂ ≠ v₃ ∧ v₃ ≠ v₄ ∧ v₄ ≠ v₁ ∧
    spoke 0 ≠ v₂ ∧ spoke 1 = v₄ ∧ spoke 2 = v₃ ∧
    lower₃₄ ≠ v₃ ∧ lower₃₄ ≠ v₄ ∧
    upper₁₂ ≠ upper 0 ∧ upper₁₂ ≠ upper 1 ∧ upper₂₃ ≠ upper 1 ∧
    upper₂₃ ≠ upper 2 ∧ upper₁₂ ≠ upper₂₃

theorem update_bad_path (G : SimpleGraph E) (spokes : Fin 3 ↪ E) (initial : E → Fin 3)
    (valid : ProperLabels G initial)
    (unique : ∀ i x y, G.Adj (spokes i) x → G.Adj (spokes i) y → x = y)
    (a b : Fin 3) (upper : Fin 3 → Fin 3) (hu : upper 0 ≠ upper 2) :
    ∃ f, ProperLabels G f ∧ BadPathDone a b upper (f ∘ spokes) ∧
      ∀ e, e ∉ Set.range spokes → f e = initial e := by
  apply update_spokes G spokes initial valid unique
  intro other symm noloop
  let outside (i : Fin 3) := (other i).elim (fun _ => (0 : Fin 3)) id
  let second (v₄ v₃ : Fin 3) := (other 0).elim (fun j => if j = 1 then v₄ else v₃) id
  obtain ⟨v₁,v₂,v₃,v₄,s₂,lower,hi₁,hi₂,ha,hb,h₁₂,h₂₃,h₃₄,h₄₁,hs₂,he₂,he₃,he₄,hL₃,hL₄,
    hu₁,hu₂,hu₃,hu₄,hu₅⟩ := color_bad_path a b (outside 1) (outside 2) second _ _ _ hu
  let col : Fin 3 → Fin 3 := ![s₂,v₄,v₃]
  have zero_one (h : other 0 = .inl 1) : s₂ ≠ v₄ := by simpa [second,h] using he₂
  have zero_two (h : other 0 = .inl 2) : s₂ ≠ v₃ := by simpa [second,h] using he₂
  refine ⟨col,⟨v₁,v₂,v₃,v₄,lower,hi₁,hi₂,ha,hb,h₁₂,h₂₃,h₃₄,h₄₁,hs₂,rfl,rfl,hL₃,hL₄,hu₁,hu₂,hu₃,hu₄,hu₅⟩,?_,?_⟩
  · intro i j h
    fin_cases i <;> fin_cases j
    · exact (noloop _ h).elim
    · exact zero_one h
    · exact zero_two h
    · exact (zero_one (symm _ _ h)).symm
    · exact (noloop _ h).elim
    · exact h₃₄.symm
    · exact (zero_two (symm _ _ h)).symm
    · exact h₃₄
    · exact (noloop _ h).elim
  · intro i c h
    fin_cases i
    · change other 0 = .inr c at h
      change s₂ ≠ c
      simpa [second,h] using he₂
    · change other 1 = .inr c at h
      change v₄ ≠ c
      simpa [outside,h] using he₃
    · change other 2 = .inr c at h
      change v₃ ≠ c
      simpa [outside,h] using he₄

def SquareDone (boundary : Fin 4 → Fin 3) (low : Fin 4 → Fin 3) : Prop :=
  ∃ vertex edge, SquareCompatible boundary vertex (fun i => (low i).castLE (by decide)) edge

theorem update_square (G : SimpleGraph E) (spokes : Fin 4 ↪ E) (initial : E → Fin 3)
    (valid : ProperLabels G initial)
    (opposite : ∀ i e, G.Adj (spokes i) e → e = spokes (i+2))
    (boundary : Fin 4 → Fin 3) (h₀₂ : boundary 0 ≠ boundary 2) (h₁₃ : boundary 1 ≠ boundary 3) :
    ∃ f, ProperLabels G f ∧ SquareDone boundary (f ∘ spokes) ∧
      ∀ e, e ∉ Set.range spokes → f e = initial e := by
  classical
  obtain ⟨vertex,sp,edge,sq⟩ := color_exceptional_square boundary h₀₂ h₁₃
  let values (i : Fin 4) : Fin 3 := ⟨(sp i).val,(sq i).2.1⟩
  let f (e : E) : Fin 3 := if h : e ∈ Set.range spokes then values h.choose else initial e
  have hin (i : Fin 4) : f (spokes i) = values i := by
    have h : spokes i ∈ Set.range spokes := ⟨i,rfl⟩
    simp only [f,dif_pos h]
    exact congrArg values (spokes.injective h.choose_spec)
  have hout (e : E) (h : e ∉ Set.range spokes) : f e = initial e := by
    dsimp only [f]; rw [dif_neg h]
  refine ⟨f,?_,⟨vertex,edge,?_⟩,hout⟩
  · intro e g h
    by_cases he : e ∈ Set.range spokes
    · obtain ⟨i,rfl⟩ := he
      rw [opposite i g h,hin,hin]
      exact fun eq => (sq i).2.2.2.1 (Fin.ext (congrArg (fun z : Fin 3 => z.val) eq))
    · have hg : g ∉ Set.range spokes := by
        rintro ⟨i,rfl⟩
        exact he ⟨i+2,(opposite i e h.symm).symm⟩
      rw [hout _ he,hout _ hg]; exact valid _ _ h
  · have eq : (fun i => ((f ∘ spokes) i).castLE (by decide : 3 ≤ 7)) = sp := by
      funext i; simp only [Function.comp_apply,hin]; rfl
    rw [eq]; exact sq

end Kostochka.FiveRegular

end

section 

namespace Kostochka.FiveRegular

open SimpleGraph

variable {E K J : Type*}

theorem update_components_outside [Fintype K] (G : SimpleGraph E)
    (spokes : K → Set E) (separate : Pairwise fun j k => Disjoint (spokes j) (spokes k))
    (goal : K → (E → Fin 3) → Prop)
    (locality : ∀ k f g, Set.EqOn f g (spokes k) → goal k f → goal k g)
    (step : ∀ k c, ProperLabels G c → ∃ f, ProperLabels G f ∧ goal k f ∧
      ∀ e, e ∉ spokes k → f e = c e)
    (initial : E → Fin 3) (valid : ProperLabels G initial) :
    ∃ f, ProperLabels G f ∧ (∀ k, goal k f) ∧ ∀ e, (∀ k, e ∉ spokes k) → f e = initial e := by
  classical
  suffices aux : ∀ S : Finset K, ∃ f, ProperLabels G f ∧ (∀ k ∈ S, goal k f) ∧
      ∀ e, (∀ k ∈ S, e ∉ spokes k) → f e = initial e by
    obtain ⟨f,hf,h,out⟩ := aux Finset.univ
    exact ⟨f,hf,fun k => h k (Finset.mem_univ _),fun e he => out e (fun k _ => he k)⟩
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨initial,valid,by simp,by simp⟩
  | @insert k S fresh ih =>
    obtain ⟨c,hc,done,hold⟩ := ih
    obtain ⟨f,hf,hk,unchanged⟩ := step k c hc
    refine ⟨f,hf,?_,?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | old
      · exact hk
      · apply locality j c f _ (done j old)
        intro e he
        exact (unchanged e (Set.disjoint_left.mp (separate (i := j) (j := k)
          (fun eq => fresh (eq ▸ old))) he)).symm
    · intro e he
      exact (unchanged e (he k (Finset.mem_insert_self _ _))).trans
        (hold e (fun j hj => he j (Finset.mem_insert_of_mem hj)))

def BadLowerDone (a b : Fin 3) (spoke : Fin 3 → Fin 3) : Prop :=
  ∃ v₁ v₂ v₃ v₄ lower₃₄ : Fin 3,
    v₁ ≠ a ∧ v₁ ≠ b ∧ v₁ ≠ v₂ ∧ v₂ ≠ v₃ ∧ v₃ ≠ v₄ ∧ v₄ ≠ v₁ ∧
    spoke 0 ≠ v₂ ∧ spoke 1 = v₄ ∧ spoke 2 = v₃ ∧ lower₃₄ ≠ v₃ ∧ lower₃₄ ≠ v₄

theorem finish_bad_path {a b : Fin 3} {spoke : Fin 3 → Fin 3} (h : BadLowerDone a b spoke)
    (upper : Fin 3 → Fin 3) (hs : upper 0 ≠ upper 2) : BadPathDone a b upper spoke := by
  obtain ⟨v₁,v₂,v₃,v₄,l,ha,hb,h₁₂,h₂₃,h₃₄,h₄₁,h₂,h₃,h₄,hl₃,hl₄⟩ := h
  obtain ⟨u₁,u₂,hu₁,hu₂,hu₃,hu₄,hu₅⟩ := color_upper_seam _ (upper 1) _ hs
  exact ⟨v₁,v₂,v₃,v₄,l,u₁,u₂,ha,hb,h₁₂,h₂₃,h₃₄,h₄₁,h₂,h₃,h₄,hl₃,hl₄,hu₁,hu₂,hu₃,hu₄,hu₅⟩

theorem update_bad_lower (G : SimpleGraph E) (spokes : Fin 3 ↪ E) (c : E → Fin 3)
    (valid : ProperLabels G c) (unique : ∀ i x y, G.Adj (spokes i) x → G.Adj (spokes i) y → x = y)
    (a b : Fin 3) : ∃ f, ProperLabels G f ∧ BadLowerDone a b (f ∘ spokes) ∧
      ∀ e, e ∉ Set.range spokes → f e = c e := by
  obtain ⟨f,ok,h,hold⟩ := update_bad_path G spokes c valid unique a b id (by decide)
  obtain ⟨v₁,v₂,v₃,v₄,l,_,_,ha,hb,h₁₂,h₂₃,h₃₄,h₄₁,h₂,h₃,h₄,hl₃,hl₄,_⟩ := h
  exact ⟨f,ok,⟨v₁,v₂,v₃,v₄,l,ha,hb,h₁₂,h₂₃,h₃₄,h₄₁,h₂,h₃,h₄,hl₃,hl₄⟩,hold⟩

inductive OpenException (E : Type*) where
  | odd (t : ℕ) (positive : 0 < t) (spoke : Option (Fin (2*t)) ↪ E) (upper : Option (Fin (2*t)) → E)
  | badPath (spoke : Fin 3 ↪ E) (upper : Fin 3 → E) (a b : E)

namespace OpenException

def spokes : OpenException E → Set E
  | .odd _ _ s _ => Set.range s
  | .badPath s _ _ _ => Set.range s

def valid (G : SimpleGraph E) : OpenException E → Prop
  | .odd t ht s u =>
    (∀ i x y, G.Adj (s i) x → G.Adj (s i) y → x = y) ∧
      G.Adj (u (some ⟨2*t-1,by omega⟩)) (u (some ⟨0,by omega⟩))
  | .badPath s u _ _ => (∀ i x y, G.Adj (s i) x → G.Adj (s i) y → x = y) ∧ G.Adj (u 0) (u 2)

def lower (initial f : E → Fin 3) : OpenException E → Prop
  | .odd _ ht s _ => OddLowerDone ht (f ∘ s)
  | .badPath s _ a b => BadLowerDone (initial a) (initial b) (f ∘ s)

def complete (f : E → Fin 3) : OpenException E → Prop
  | .odd _ ht s u => OddDone ht (f ∘ u) (f ∘ s)
  | .badPath s u a b => BadPathDone (f a) (f b) (f ∘ u) (f ∘ s)

def fixed : OpenException E → Set E
  | .odd .. => ∅
  | .badPath _ _ a b => {a,b}

theorem lower_local (P : OpenException E) (initial f g : E → Fin 3)
    (eq : Set.EqOn f g P.spokes) (done : P.lower initial f) : P.lower initial g := by
  cases P with
  | odd t ht s u =>
    change OddLowerDone ht (g ∘ s)
    rw [show g ∘ s = f ∘ s from funext (fun i => (eq ⟨i,rfl⟩).symm)]
    exact done
  | badPath s u a b =>
    change BadLowerDone (initial a) (initial b) (g ∘ s)
    rw [show g ∘ s = f ∘ s from funext (fun i => (eq ⟨i,rfl⟩).symm)]
    exact done

theorem settle (P : OpenException E) (G : SimpleGraph E) (ok : P.valid G) (initial c : E → Fin 3)
    (hc : ProperLabels G c) : ∃ f, ProperLabels G f ∧ P.lower initial f ∧
      ∀ e, e ∉ P.spokes → f e = c e := by
  cases P with
  | odd t ht s u => exact update_odd_cycle ht G s c hc ok.1
  | badPath s u a b => exact update_bad_lower G s c hc ok.1 (initial a) (initial b)

theorem finish (P : OpenException E) (G : SimpleGraph E) (ok : P.valid G) (initial f : E → Fin 3)
    (hf : ProperLabels G f) (done : P.lower initial f) (fixedEq : Set.EqOn f initial P.fixed) :
    P.complete f := by
  cases P with
  | odd t ht s u => exact finish_odd ht (f ∘ u) _ (hf _ _ ok.2) done
  | badPath s u a b =>
    have ea := fixedEq (show a ∈ fixed (.badPath s u a b) by simp [fixed])
    have eb := fixedEq (show b ∈ fixed (.badPath s u a b) by simp [fixed])
    change BadPathDone (f a) (f b) (f ∘ u) (f ∘ s)
    rw [ea,eb]
    exact finish_bad_path done _ (hf _ _ ok.2)

end OpenException

structure SquareSpokePatch (E : Type*) where
  spoke : Fin 4 ↪ E
  upper : Fin 4 → E

/- The local recolorings can be applied in succession once their affected spokes and
conflict neighborhoods satisfy the separation conditions. -/
theorem patch_all [Fintype K] [Fintype J] (G : SimpleGraph E)
    (P : K → OpenException E) (Q : J → SquareSpokePatch E)
    (openValid : ∀ k, (P k).valid G)
    (squareOpposite : ∀ j i e, G.Adj ((Q j).spoke i) e → e = (Q j).spoke (i+2))
    (squareApart : ∀ j, G.Adj ((Q j).upper 0) ((Q j).upper 2) ∧ G.Adj ((Q j).upper 1) ((Q j).upper 3))
    (pDisj : Pairwise fun i j => Disjoint (P i).spokes (P j).spokes)
    (qDisj : Pairwise fun i j => Disjoint (Set.range (Q i).spoke) (Set.range (Q j).spoke))
    (pqDisj : ∀ i j, Disjoint (P i).spokes (Set.range (Q j).spoke))
    (badFixedP : ∀ i j, Disjoint (P i).fixed (P j).spokes)
    (badFixedQ : ∀ i j, Disjoint (P i).fixed (Set.range (Q j).spoke))
    (squareUpper : ∀ i j, Disjoint (Set.range (Q i).upper) (Set.range (Q j).spoke))
    (initial : E → Fin 3) (valid : ProperLabels G initial) :
    ∃ f, ProperLabels G f ∧ (∀ k, (P k).complete f) ∧
      (∀ j, SquareDone (f ∘ (Q j).upper) (f ∘ (Q j).spoke)) ∧
      ∀ e, (∀ k, e ∉ (P k).spokes) → (∀ j, e ∉ Set.range (Q j).spoke) → f e = initial e := by
  obtain ⟨c,hc,lower,oldP⟩ := update_components_outside G (fun k => (P k).spokes) pDisj
    (fun k f => (P k).lower initial f) (fun k => (P k).lower_local initial)
    (fun k => (P k).settle G (openValid k) initial) initial valid
  obtain ⟨f,hf,squares,oldQ⟩ := update_components_outside G (fun j => Set.range (Q j).spoke) qDisj
    (fun j f => SquareDone (c ∘ (Q j).upper) (f ∘ (Q j).spoke)) (fun j f g eq done => by
      rwa [show g ∘ (Q j).spoke = f ∘ (Q j).spoke from funext (fun i => (eq ⟨i,rfl⟩).symm)])
    (fun j g hg => update_square G (Q j).spoke g hg (squareOpposite j) (c ∘ (Q j).upper)
      (hc _ _ (squareApart j).1) (hc _ _ (squareApart j).2)) c hc
  refine ⟨f,hf,?_,?_,fun e hp hq => (oldQ e hq).trans (oldP e hp)⟩
  · intro i
    apply (P i).finish G (openValid i) initial f hf
    · apply (P i).lower_local initial c f _ (lower i)
      exact fun e he => (oldQ e (fun j => Set.disjoint_left.mp (pqDisj i j) he)).symm
    · intro e he
      exact (oldQ e (fun j => Set.disjoint_left.mp (badFixedQ i j) he)).trans
        (oldP e (fun j => Set.disjoint_left.mp (badFixedP i j) he))
  · intro i
    rw [show f ∘ (Q i).upper = c ∘ (Q i).upper from funext (fun a => oldQ _ (fun j =>
      Set.disjoint_left.mp (squareUpper i j) ⟨a,rfl⟩))]
    exact squares i

end Kostochka.FiveRegular

end

section 

namespace Kostochka.FiveRegular
open Subdivision

variable {V E K : Type*}

structure CellColors (V E : Type*) where
  vertex : V → Fin 3
  edge : E → Bool × Fin 3

def cellLayer (part : E → EdgePart) (P : CellColors V E) (e : E) : Option Bool :=
  match part e with
  | .matching => none
  | .factor b => some b
  | .exceptional => some (P.edge e).1

def cellEdge (part : E → EdgePart) (shared : E → Fin 3) (P : CellColors V E) (e : E) : Fin 3 :=
  if part e = .exceptional then (P.edge e).2 else shared e

end Kostochka.FiveRegular

end

section 

namespace Kostochka.FiveRegular

open SimpleGraph Subdivision

variable {V E K : Type*}

def relativeColor (side : Bool) (layer : Option Bool) (c : Fin 3) : Fin 7 :=
  layer.elim 6 (fun b => if b = side then patchLow c else patchHigh c)

structure StarAt (D : Family V E) (v : V) (vertexColor : Fin 7) (edgeColor : E → Fin 7) where
  slots : Fin 5 → E
  covers : ∀ e, FamilyIncident D v e → ∃ i, slots i = e
  distinct : Function.Injective (Fin.cases vertexColor (edgeColor ∘ slots))

theorem StarAt.edges {D : Family V E} {v} {c : Fin 7} {edge : E → Fin 7}
    (S : StarAt D v c edge) {e f} (he : FamilyIncident D v e)
    (hf : FamilyIncident D v f) (hn : e ≠ f) : edge e ≠ edge f := by
  obtain ⟨i,rfl⟩ := S.covers e he
  obtain ⟨j,rfl⟩ := S.covers f hf
  intro eq
  have hit : i.succ = j.succ := S.distinct (by simpa only [Fin.cases_succ,Function.comp_apply] using eq)
  exact hn (congrArg S.slots (Fin.succ_inj.mp hit))

theorem StarAt.incidence {D : Family V E} {v} {c : Fin 7} {edge : E → Fin 7}
    (S : StarAt D v c edge) {e} (he : FamilyIncident D v e) : c ≠ edge e := by
  obtain ⟨i,rfl⟩ := S.covers e he
  intro eq
  have hit : (0 : Fin 6) = i.succ := S.distinct
    (by simpa only [Fin.cases_zero,Fin.cases_succ,Function.comp_apply] using eq)
  exact Fin.succ_ne_zero i hit.symm

structure RegionStars (D : Family V E) (side : V → Bool) (part : E → EdgePart)
    (region : V → Option K) (shared : E → Fin 3) where
  cell : K → CellColors V E
  neighboring : ∀ k e, side (D.left e) = side (D.right e) → region (D.left e) = some k →
    (cell k).vertex (D.left e) ≠ (cell k).vertex (D.right e)
  stars : ∀ k v, region v = some k → Nonempty (StarAt D v (patchLow ((cell k).vertex v))
    (fun e => relativeColor (side v) (cellLayer part (cell k) e) (cellEdge part shared (cell k) e)))

structure GluedLayers (D : Family V E) (side : V → Bool) (part : E → EdgePart) where
  layer : E → Option Bool
  colors : CompletedLayers D side layer
  matching : ∀ e, layer e = none ↔ part e = .matching
  factor : ∀ e b, part e = .factor b → layer e = some b

theorem layers_of_region_stars (D : Family V E) (side : V → Bool) (part : E → EdgePart)
    (region : V → Option K) (outside : V → Fin 3) (shared : E → Fin 3)
    (R : RegionStars D side part region shared)
    (closed : ∀ e, side (D.left e) = side (D.right e) → region (D.left e) = region (D.right e))
    (exc : ∀ e, part e = .exceptional → ∃ k, region (D.left e) = some k ∧ region (D.right e) = some k)
    (oldVertex : ∀ e, side (D.left e) = side (D.right e) → region (D.left e) = none →
      outside (D.left e) ≠ outside (D.right e))
    (oldEdge : ∀ b e f, part e = .factor b → part f = .factor b → e ≠ f →
      FamilyMeet D e f → shared e ≠ shared f)
    (oldInc : ∀ v e, region v = none → part e = .factor (side v) →
      FamilyIncident D v e → outside v ≠ shared e) : Nonempty (GluedLayers D side part) := by
  classical
  let atV (v : V) : CellColors V E :=
    (region v).elim ⟨fun _ => 0,fun _ => (false,0)⟩ R.cell
  let vertex (v : V) := (region v).elim (outside v) (fun k => (R.cell k).vertex v)
  let layer e := cellLayer part (atV (D.left e)) e
  let edge e := cellEdge part shared (atV (D.left e)) e
  have agree {v e} (h : FamilyIncident D v e) (ex : part e = .exceptional) :
      region v = region (D.left e) := by
    obtain ⟨k,hl,hr⟩ := exc e ex
    exact h.elim (congrArg region) (fun eq => (congrArg region eq).trans (hr.trans hl.symm))
  have localEdge {v e k} (h : FamilyIncident D v e) (reg : region v = some k) :
      layer e = cellLayer part (R.cell k) e ∧ edge e = cellEdge part shared (R.cell k) e := by
    cases hp : part e with
    | matching => simp [layer,edge,cellLayer,cellEdge,hp]
    | factor b => simp [layer,edge,cellLayer,cellEdge,hp]
    | exceptional => simp [layer,edge,atV,(agree h hp).symm.trans reg]
  have old {v e b} (h : FamilyIncident D v e) (reg : region v = none) (le : layer e = some b) :
      part e = .factor b ∧ edge e = shared e := by
    cases hp : part e with
    | matching => simp [layer,cellLayer,hp] at le
    | exceptional =>
      obtain ⟨k,hl,hr⟩ := exc e hp
      rw [← agree h hp,reg] at hl
      contradiction
    | factor j => simpa [layer,cellLayer,edge,cellEdge,hp] using le
  refine ⟨⟨layer,⟨vertex,edge,?_,?_,?_⟩,?_,?_⟩⟩
  · intro e hs
    have hr := closed e hs
    cases reg : region (D.left e) with
    | none => simpa [vertex,reg,hr.symm.trans reg] using oldVertex e hs reg
    | some k => simpa [vertex,reg,hr.symm.trans reg] using R.neighboring k e hs reg
  · rintro b e f he hf hn ⟨v,ve,vf⟩
    cases reg : region v with
    | none =>
      have a := old ve reg he
      have d := old vf reg hf
      rw [a.2,d.2]
      exact oldEdge b e f a.1 d.1 hn ⟨v,ve,vf⟩
    | some k =>
      obtain ⟨S⟩ := R.stars k v reg
      have a := localEdge ve reg
      have d := localEdge vf reg
      intro eq
      apply S.edges ve vf hn
      rw [← a.1,← d.1,← a.2,← d.2,he,hf,eq]
  · intro v e he ve
    cases reg : region v with
    | none =>
      have a := old ve reg he
      simpa [vertex,reg,a.2] using oldInc v e reg a.1 ve
    | some k =>
      obtain ⟨S⟩ := R.stars k v reg
      have a := localEdge ve reg
      intro eq
      apply S.incidence ve
      rw [← a.1,← a.2,he]
      simpa [vertex,reg,relativeColor] using congrArg patchLow eq
  · intro e
    cases hp : part e <;> simp [layer,cellLayer,hp]
  · intro e b hp
    simp [layer,cellLayer,hp]

end Kostochka.FiveRegular

end

section 

namespace Kostochka

open SimpleGraph Finset

section Eulerian

variable {W : Type*}

private lemma countP_edges_eq_card_filter [DecidableEq W] {H : SimpleGraph W} {u v : W}
    {p : H.Walk u v} (hp : p.IsTrail) (x : W) :
    p.edges.countP (fun e => x ∈ e) = (hp.edgesFinset.filter (fun e => x ∈ e)).card := by
  rw [← Multiset.coe_countP, Multiset.countP_eq_card_filter]
  rfl

private lemma degree_deleteEdges_walk_add_countP [Fintype W] [DecidableEq W] {H : SimpleGraph W}
    [DecidableRel H.Adj] {u v : W} {p : H.Walk u v}
    [DecidableRel (H.deleteEdges p.edgeSet).Adj] (hp : p.IsTrail) (x : W) :
    (H.deleteEdges p.edgeSet).degree x + p.edges.countP (fun e => x ∈ e) = H.degree x := by
  rw [countP_edges_eq_card_filter hp x, ← card_incidenceFinset_eq_degree,
    ← card_incidenceFinset_eq_degree]
  have h1 : (H.deleteEdges p.edgeSet).incidenceFinset x =
      (H.incidenceFinset x).filter (fun e => e ∉ hp.edgesFinset) := by
    ext e
    simp only [mem_incidenceFinset, mem_filter, incidenceSet, Set.mem_ofPred_eq,
      edgeSet_deleteEdges, Set.mem_sdiff, Walk.mem_edgeSet]
    tauto
  have h2 : hp.edgesFinset.filter (fun e => x ∈ e) =
      (H.incidenceFinset x).filter (fun e => e ∈ hp.edgesFinset) := by
    ext e
    simp only [mem_filter, mem_incidenceFinset, incidenceSet, Set.mem_ofPred_eq]
    exact ⟨fun ⟨he, hx⟩ => ⟨⟨p.edges_subset_edgeSet he, hx⟩, he⟩,
      fun ⟨⟨_, hx⟩, he⟩ => ⟨he, hx⟩⟩
  rw [h1, h2, add_comm]
  exact Finset.card_filter_add_card_filter_not (fun e => e ∈ hp.edgesFinset)

private lemma exists_nonempty_closed_isTrail_of_even_degree [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj]
    (heven : ∀ x : W, Even (H.degree x)) {w : W} (hw : 0 < H.degree w) :
    ∃ c : H.Walk w w, c.IsTrail ∧ 0 < c.length := by
  classical
  let S : Set ℕ := {n | ∃ (z : W) (t : H.Walk w z), t.IsTrail ∧ t.length = n}
  have hS_fin : S.Finite :=
    (Set.finite_le_nat H.edgeFinset.card).subset fun n ⟨_, _, ht, hn⟩ =>
      hn ▸ ht.length_le_card_edgeFinset
  have hS_ne : S.Nonempty := ⟨0, w, Walk.nil, Walk.IsTrail.nil, rfl⟩
  obtain ⟨m, ⟨z, t, ht, rfl⟩, hmax⟩ := hS_fin.exists_maximal hS_ne
  have ht_pos : 0 < t.length := by
    obtain ⟨w', hww'⟩ := (H.degree_pos_iff_exists_adj w).mp hw
    have h1 : 1 ∈ S := ⟨w', Walk.cons hww' Walk.nil, by simp, rfl⟩
    have hle : 1 ≤ t.length := by
      by_contra hlt
      have ht0 : t.length < 1 := Nat.lt_of_not_ge hlt
      exact absurd (hmax h1 ht0.le) (by omega)
    exact lt_of_lt_of_le Nat.zero_lt_one hle
  have hzw : z = w := by
    by_contra hne
    have hne' : w ≠ z := Ne.symm hne
    have hnotEven : ¬ Even (t.edges.countP (fun e => z ∈ e)) := by
      rw [ht.even_countP_edges_iff z]
      intro h
      exact (h hne').2 rfl
    have hdeg_eq := degree_deleteEdges_walk_add_countP ht z
    have hdel_pos : 0 < (H.deleteEdges t.edgeSet).degree z := by
      by_contra hzero
      have h0 : (H.deleteEdges t.edgeSet).degree z = 0 := Nat.eq_zero_of_not_pos hzero
      rw [h0, zero_add] at hdeg_eq
      exact hnotEven (hdeg_eq ▸ heven z)
    obtain ⟨z', hzz'⟩ := ((H.deleteEdges t.edgeSet).degree_pos_iff_exists_adj z).mp hdel_pos
    rw [deleteEdges_adj] at hzz'
    have hnotmem : s(z, z') ∉ t.edges := hzz'.2
    have hconcat_trail : (t.concat hzz'.1).IsTrail := by
      rw [Walk.concat_eq_append, Walk.isTrail_append]
      refine ⟨ht, by simp, ?_⟩
      intro e he1 he2
      simp only [Walk.edges_cons, Walk.edges_nil, List.mem_singleton] at he2
      exact hnotmem (he2 ▸ he1)
    have hmem : t.length + 1 ∈ S := ⟨z', t.concat hzz'.1, hconcat_trail, t.length_concat hzz'.1⟩
    exact absurd (hmax hmem (Nat.le_succ _)) (by omega)
  subst hzw
  exact ⟨t, ht, ht_pos⟩

theorem exists_closed_isEulerian [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hconn : H.Connected) (heven : ∀ x : W, Even (H.degree x)) :
    ∃ (r : W) (p : H.Walk r r), p.IsEulerian := by
  classical
  let S : Set ℕ := {n | ∃ (u : W) (p : H.Walk u u), p.IsTrail ∧ p.length = n}
  have hS_fin : S.Finite :=
    (Set.finite_le_nat H.edgeFinset.card).subset fun n ⟨_, _, hp, hn⟩ =>
      hn ▸ hp.length_le_card_edgeFinset
  obtain ⟨r₀⟩ := hconn.nonempty
  have hS_ne : S.Nonempty := ⟨0, r₀, Walk.nil, Walk.IsTrail.nil, rfl⟩
  obtain ⟨m, ⟨u, p, hp, rfl⟩, hmax⟩ := hS_fin.exists_maximal hS_ne
  refine ⟨u, p, hp.isEulerian_of_forall_mem fun e he => ?_⟩
  by_contra hnotmem
  let H' : SimpleGraph W := H.deleteEdges p.edgeSet
  have heven' : ∀ x : W, Even (H'.degree x) := by
    intro x
    have hsum := degree_deleteEdges_walk_add_countP hp x
    have hp_even : Even (p.edges.countP (fun e => x ∈ e)) :=
      (hp.even_countP_edges_iff x).mpr fun hne => (hne rfl).elim
    have hadd : Even (H'.degree x + p.edges.countP (fun e => x ∈ e)) := hsum ▸ heven x
    exact (Nat.even_add.mp hadd).mpr hp_even
  
  have hex_w : ∃ w ∈ p.support, 0 < H'.degree w := by
    induction e using Sym2.ind with
    | _ a b =>
      have hab : H.Adj a b := he
      have hab' : H'.Adj a b := by
        rw [deleteEdges_adj]
        exact ⟨hab, hnotmem⟩
      by_cases ha : a ∈ p.support
      · exact ⟨a, ha, hab'.degree_pos_left⟩
      · obtain ⟨q⟩ := hconn u a
        obtain ⟨d, _, hd_fst, hd_snd⟩ :=
          q.exists_boundary_dart {x | x ∈ p.support} p.start_mem_support ha
        have hd_notmem : s(d.fst, d.snd) ∉ p.edges := fun hmem =>
          hd_snd (p.snd_mem_support_of_mem_edges hmem)
        have hd_adj' : H'.Adj d.fst d.snd := by
          rw [deleteEdges_adj]
          exact ⟨d.adj, hd_notmem⟩
        exact ⟨d.fst, hd_fst, hd_adj'.degree_pos_left⟩
  obtain ⟨w, hw_supp, hw_pos⟩ := hex_w
  obtain ⟨c, hc_trail, hc_pos⟩ := exists_nonempty_closed_isTrail_of_even_degree heven' hw_pos
  let cH : H.Walk w w := c.mapLe (H.deleteEdges_le p.edgeSet)
  let p' : H.Walk w w := p.rotate w hw_supp
  have hcH_edges : cH.edges = c.edges := Walk.edges_mapLe_eq_edges _ _
  have hcH_trail : cH.IsTrail := by
    rw [Walk.isTrail_def, hcH_edges]
    exact hc_trail.edges_nodup
  have hp'_trail : p'.IsTrail := hp.rotate hw_supp
  have hdisj : p'.edges.Disjoint cH.edges := by
    intro e' he1 he2
    have he1' : e' ∈ p.edges := (p.rotate_edges w hw_supp).perm.mem_iff.mp he1
    rw [hcH_edges] at he2
    have he2' : e' ∈ H'.edgeSet := c.edges_subset_edgeSet he2
    rw [edgeSet_deleteEdges] at he2'
    exact he2'.2 he1'
  have hcomb_trail : (p'.append cH).IsTrail :=
    (Walk.isTrail_append p' cH).mpr ⟨hp'_trail, hcH_trail, hdisj⟩
  have hcomb_len : (p'.append cH).length = p.length + c.length := by
    rw [Walk.length_append, Walk.length_rotate, Walk.length_mapLe]
  have hmem : p.length + c.length ∈ S := ⟨w, p'.append cH, hcomb_trail, hcomb_len⟩
  have hle : p.length + c.length ≤ p.length := hmax hmem (Nat.le_add_right _ _)
  omega

lemma IsEulerian.length_eq_card_edgeFinset [Fintype W] [DecidableEq W] {H : SimpleGraph W}
    [DecidableRel H.Adj] {u v : W} {p : H.Walk u v} (hp : p.IsEulerian) :
    p.length = H.edgeFinset.card := by
  have h1 : p.edges.toFinset = H.edgeFinset := by
    ext e
    simp [hp.mem_edges_iff]
  rw [← h1, List.toFinset_card_of_nodup hp.isTrail.edges_nodup, p.length_edges]

end Eulerian

section AlternatingPartition

variable {W : Type*}

mutual

def evenEdges {H : SimpleGraph W} : ∀ {u v : W}, H.Walk u v → List (Sym2 W)
  | _, _, .nil => []
  | a, _, .cons (v := b) _ q => s(a, b) :: oddEdges q

def oddEdges {H : SimpleGraph W} : ∀ {u v : W}, H.Walk u v → List (Sym2 W)
  | _, _, .nil => []
  | _, _, .cons _ q => evenEdges q
end

private lemma perm_evenEdges_append_oddEdges {H : SimpleGraph W} {u v : W} (w : H.Walk u v) :
    (evenEdges w ++ oddEdges w).Perm w.edges := by
  induction w with
  | nil => simp [evenEdges, oddEdges]
  | cons h q ih =>
    simp only [evenEdges, oddEdges, Walk.edges_cons, List.cons_append]
    exact (List.perm_append_comm.trans ih).cons _

private lemma countP_evenEdges_sub_oddEdges [DecidableEq W] {H : SimpleGraph W} {u v : W}
    (w : H.Walk u v) (x : W) :
    ((evenEdges w).countP (fun e => x ∈ e) : ℤ) - ((oddEdges w).countP (fun e => x ∈ e) : ℤ) =
      (if x = u then 1 else 0) + (-1 : ℤ) ^ w.length * (if x = v then -1 else 0) := by
  induction w with
  | nil =>
    simp only [evenEdges, oddEdges, List.countP_nil, Nat.cast_zero, sub_self, Walk.length_nil,
      pow_zero, one_mul]
    split_ifs <;> ring
  | @cons a b c h q ih =>
    have hab : a ≠ b := h.ne
    have hmem : ((decide (x ∈ s(a, b))).toNat : ℤ) =
        (if x = a then 1 else 0) + (if x = b then 1 else 0) := by
      by_cases hxa : x = a <;> by_cases hxb : x = b
      · exact absurd (hxa.symm.trans hxb) hab
      · simp [Sym2.mem_iff, hxa, hab]
      · simp [Sym2.mem_iff, hxb, hab.symm]
      · simp [Sym2.mem_iff, hxa, hxb]
    simp only [evenEdges, oddEdges, List.countP_cons, Walk.length_cons, pow_succ']
    have hstep :
        (((oddEdges q).countP (fun e => x ∈ e) + (if decide (x ∈ s(a, b)) then 1 else 0) : ℕ) : ℤ) =
        ((oddEdges q).countP (fun e => x ∈ e) : ℤ) + ((decide (x ∈ s(a, b))).toNat : ℤ) := by
      cases decide (x ∈ s(a, b)) <;> simp
    rw [hstep, hmem]
    linarith

private lemma countP_evenEdges_eq_oddEdges [DecidableEq W] {H : SimpleGraph W} {r : W}
    (p : H.Walk r r) (hlen : Even p.length) (x : W) :
    (evenEdges p).countP (fun e => x ∈ e) = (oddEdges p).countP (fun e => x ∈ e) := by
  have h := countP_evenEdges_sub_oddEdges p x
  rw [hlen.neg_one_pow, one_mul] at h
  have hzero : ((evenEdges p).countP (fun e => x ∈ e) : ℤ) -
      ((oddEdges p).countP (fun e => x ∈ e) : ℤ) = 0 := by
    rw [h]
    split_ifs <;> ring
  omega

private def graphOfEdgeList {H : SimpleGraph W} (L : List (Sym2 W))
    (hL : ∀ e ∈ L, e ∈ H.edgeSet) : SimpleGraph W where
  Adj x y := s(x, y) ∈ L
  symm := ⟨fun _ _ h => by rwa [Sym2.eq_swap]⟩
  loopless := ⟨fun x h => H.loopless.irrefl x (hL s(x, x) h)⟩

private instance decRelGraphOfEdgeList [DecidableEq W] {H : SimpleGraph W} (L : List (Sym2 W))
    (hL : ∀ e ∈ L, e ∈ H.edgeSet) : DecidableRel (graphOfEdgeList L hL).Adj :=
  fun x y => inferInstanceAs (Decidable (s(x, y) ∈ L))

private lemma degree_graphOfEdgeList [Fintype W] [DecidableEq W] {H : SimpleGraph W}
    (L : List (Sym2 W)) (hL : ∀ e ∈ L, e ∈ H.edgeSet) (hnodup : L.Nodup) (x : W) :
    (graphOfEdgeList L hL).degree x = L.countP (fun e => x ∈ e) := by
  rw [← card_incidenceFinset_eq_degree]
  have hinc : (graphOfEdgeList L hL).incidenceFinset x = (L.filter (fun e => x ∈ e)).toFinset := by
    ext e
    rw [mem_incidenceFinset, List.mem_toFinset, List.mem_filter]
    induction e using Sym2.ind with
    | _ a b =>
      simp [incidenceSet, graphOfEdgeList]
  rw [hinc, List.toFinset_card_of_nodup (hnodup.filter _), List.countP_eq_length_filter]

theorem exists_half_degree_partition_of_closed_isEulerian [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {r : W} (p : H.Walk r r)
    (hp : p.IsEulerian) (hlen : Even p.length) :
    ∃ (H₁ H₂ : SimpleGraph W) (_ : DecidableRel H₁.Adj) (_ : DecidableRel H₂.Adj),
      H₁ ⊔ H₂ = H ∧ Disjoint H₁ H₂ ∧
      (∀ x : W, H₁.degree x = H₂.degree x) ∧
      (∀ x : W, 2 * H₁.degree x = H.degree x) ∧
      (∀ x : W, 2 * H₂.degree x = H.degree x) := by
  have hperm : (evenEdges p ++ oddEdges p).Perm p.edges := perm_evenEdges_append_oddEdges p
  have hnodup_all : (evenEdges p ++ oddEdges p).Nodup := hperm.nodup_iff.mpr hp.isTrail.edges_nodup
  rw [List.nodup_append'] at hnodup_all
  obtain ⟨hnodup₁, hnodup₂, hdisj_list⟩ := hnodup_all
  have hsub₁ : ∀ e ∈ evenEdges p, e ∈ H.edgeSet := fun e he =>
    p.edges_subset_edgeSet (hperm.mem_iff.mp (List.mem_append_left _ he))
  have hsub₂ : ∀ e ∈ oddEdges p, e ∈ H.edgeSet := fun e he =>
    p.edges_subset_edgeSet (hperm.mem_iff.mp (List.mem_append_right _ he))
  let H₁ := graphOfEdgeList (evenEdges p) hsub₁
  let H₂ := graphOfEdgeList (oddEdges p) hsub₂
  refine ⟨H₁, H₂, inferInstance, inferInstance, ?_, ?_, ?_, ?_, ?_⟩
  · ext x y
    simp only [sup_adj, H₁, H₂, graphOfEdgeList]
    rw [← List.mem_append, hperm.mem_iff, hp.mem_edges_iff, mem_edgeSet]
  · rw [disjoint_iff]
    ext x y
    simp only [inf_adj, bot_adj, H₁, H₂, graphOfEdgeList, iff_false, not_and]
    exact fun h1 h2 => hdisj_list h1 h2
  · intro x
    rw [degree_graphOfEdgeList _ _ hnodup₁, degree_graphOfEdgeList _ _ hnodup₂]
    exact countP_evenEdges_eq_oddEdges p hlen x
  · intro x
    have hdeg_eq : H₁.degree x = H₂.degree x := by
      rw [degree_graphOfEdgeList _ _ hnodup₁, degree_graphOfEdgeList _ _ hnodup₂]
      exact countP_evenEdges_eq_oddEdges p hlen x
    have hdeg_sum : H₁.degree x + H₂.degree x = H.degree x := by
      rw [degree_graphOfEdgeList _ _ hnodup₁, degree_graphOfEdgeList _ _ hnodup₂,
        ← List.countP_append, hperm.countP_eq, countP_edges_eq_card_filter hp.isTrail x,
        ← card_incidenceFinset_eq_degree, hp.edgesFinset_eq, H.incidenceFinset_eq_filter x]
    omega
  · intro x
    have hdeg_eq : H₁.degree x = H₂.degree x := by
      rw [degree_graphOfEdgeList _ _ hnodup₁, degree_graphOfEdgeList _ _ hnodup₂]
      exact countP_evenEdges_eq_oddEdges p hlen x
    have hdeg_sum : H₁.degree x + H₂.degree x = H.degree x := by
      rw [degree_graphOfEdgeList _ _ hnodup₁, degree_graphOfEdgeList _ _ hnodup₂,
        ← List.countP_append, hperm.countP_eq, countP_edges_eq_card_filter hp.isTrail x,
        ← card_incidenceFinset_eq_degree, hp.edgesFinset_eq, H.incidenceFinset_eq_filter x]
    omega

end AlternatingPartition

section SplitConstruction

variable {V : Type*}

end SplitConstruction

section MainTheorems

variable {V : Type*}

end MainTheorems

end Kostochka

end

section 

namespace Kostochka.FiveRegular.Subdivision

open SimpleGraph

theorem exists_balanced {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (D : Family V E) (connected : ∀ v w, Relation.ReflTransGen (Joined D) v w)
    (degrees : ∀ v, Even (coloredDegree D (fun _ => true) v true)) (edges : Even (Fintype.card E)) :
    ∃ color : E → Bool, ∀ v, coloredDegree D color v true = coloredDegree D color v false := by
  cases isEmpty_or_nonempty V with
  | inl h => exact ⟨fun _ => false, fun v => (h.false v).elim⟩
  | inr h =>
    have hconn : (graph D).Connected := ⟨preconnected D connected⟩
    obtain ⟨_, p, hp⟩ := Kostochka.exists_closed_isEulerian (graph D) hconn (even_degrees D degrees)
    have heven : Even p.length := by
      rw [Kostochka.IsEulerian.length_eq_card_edgeFinset hp]
      rw [SimpleGraph.edgeFinset, Set.toFinset_card, card_edges]
      exact edges.mul_left _
    obtain ⟨H₁, H₂, _, _, cover, disj, eq, _, _⟩ :=
      Kostochka.exists_half_degree_partition_of_closed_isEulerian (graph D) p hp heven
    obtain ⟨f, hf⟩ := balanced_of_partition (graph D) H₁ H₂ cover disj eq
    exact pullback_balanced D f hf

end Kostochka.FiveRegular.Subdivision

end

section 

namespace Kostochka.FiveRegular.Auxiliary
open Finset Subdivision
variable {V E S T : Type*}
abbrev Nodes (V T : Type*) := V ⊕ T
abbrev Edges (E S T : Type*) := E ⊕ (S ⊕ (T ⊕ T))

def aux (D : Family V E) (A : Family V S) (B : Family V T) : Family (Nodes V T) (Edges E S T) where
  left
    | .inl e => .inl (D.left e)
    | .inr (.inl s) => .inl (A.left s)
    | .inr (.inr (.inl t)) => .inl (B.left t)
    | .inr (.inr (.inr t)) => .inr t
  right
    | .inl e => .inl (D.right e)
    | .inr (.inl s) => .inl (A.right s)
    | .inr (.inr (.inl t)) => .inr t
    | .inr (.inr (.inr t)) => .inl (B.right t)

private theorem connected (D : Family V E) (A : Family V S) (B : Family V T)
    (conn : ∀ x y, Relation.ReflTransGen (Joined D) x y) :
    ∀ x y, Relation.ReflTransGen (Joined (aux D A B)) x y := by
  have base (v w) : Relation.ReflTransGen (Joined (aux D A B)) (.inl v) (.inl w) := by
    induction conn v w with
    | refl => exact .refl
    | tail _ h ih =>
      obtain ⟨e,h|h⟩ := h
      · exact ih.tail ⟨.inl e,Or.inl ⟨congrArg Sum.inl h.1, congrArg Sum.inl h.2⟩⟩
      · exact ih.tail ⟨.inl e,Or.inr ⟨congrArg Sum.inl h.1, congrArg Sum.inl h.2⟩⟩
  have lead (t) : Joined (aux D A B) (.inl (B.left t)) (.inr t) :=
    ⟨.inr (.inr (.inl t)),Or.inl ⟨rfl,rfl⟩⟩
  have back (t) : Joined (aux D A B) (.inr t) (.inl (B.left t)) :=
    ⟨.inr (.inr (.inl t)),Or.inr ⟨rfl,rfl⟩⟩
  rintro (v|t) (w|s)
  · exact base v w
  · exact (base v (B.left s)).tail (lead s)
  · exact (base (B.left t) w).head (back t)
  · exact ((base (B.left t) (B.left s)).tail (lead s)).head (back t)

variable [DecidableEq V] [DecidableEq T] [Fintype E] [Fintype S] [Fintype T]

def endCount (B : Family V T) (l r : T → Bool) (v : V) (b : Bool) : ℕ :=
  (∑ t, if v = B.left t ∧ l t = b then 1 else 0) + (∑ t, if v = B.right t ∧ r t = b then 1 else 0)

private theorem at_base (D : Family V E) (A : Family V S) (B : Family V T) (f : Edges E S T → Bool)
    (v : V) (b : Bool) :
    coloredDegree (aux D A B) f (.inl v) b =
      coloredDegree D (fun e => f (.inl e)) v b +
      coloredDegree A (fun s => f (.inr (.inl s))) v b +
      endCount B (fun t => f (.inr (.inr (.inl t)))) (fun t => f (.inr (.inr (.inr t)))) v b := by
  simp only [coloredDegree,endCount,Fintype.sum_sum_type,aux,Sum.inl.injEq,reduceCtorEq,
    false_and,if_false,sum_const_zero]
  omega

private theorem at_aux (D : Family V E) (A : Family V S) (B : Family V T) (f : Edges E S T → Bool)
    (t : T) (b : Bool) : coloredDegree (aux D A B) f (.inr t) b =
    (if f (.inr (.inr (.inl t))) = b then 1 else 0) + (if f (.inr (.inr (.inr t))) = b then 1 else 0) := by
  classical
  simp only [coloredDegree,Fintype.sum_sum_type,aux,Sum.inr.injEq,reduceCtorEq,false_and,if_false,sum_const_zero,
    zero_add,add_zero]
  have term (func : T → Bool) : (∑ s, if t = s ∧ func s = b then 1 else 0) = (if func t = b then 1 else 0 : ℕ) := by
    have id (s : T) : (if t = s ∧ func s = b then 1 else 0 : ℕ) = if s = t then (if func t = b then 1 else 0) else 0 := by
      by_cases h : s = t <;> simp [h,Ne.symm]
    simp [id]
  rw [term,term,add_comm]

theorem partition [Fintype V] [DecidableEq E] [DecidableEq S]
    (D : Family V E) (A : Family V S) (B : Family V T)
    (conn : ∀ v w, Relation.ReflTransGen (Joined D) v w)
    (evenVertices : ∀ v, Even (coloredDegree D (fun _ => true) v true +
      coloredDegree A (fun _ => true) v true + coloredDegree B (fun _ => true) v true))
    (evenEdges : Even (Fintype.card E + Fintype.card S)) :
    ∃ (f : E → Bool) (g : S → Bool) (k : T → Bool), ∀ v,
      coloredDegree D f v true + coloredDegree A g v true + endCount B k (fun t => !(k t)) v true =
      coloredDegree D f v false + coloredDegree A g v false + endCount B k (fun t => !(k t)) v false := by
  classical
  have deg (x) : Even (coloredDegree (aux D A B) (fun _ => true) x true) := by
    cases x with
    | inl v => rw [at_base]; exact evenVertices v
    | inr t => rw [at_aux]; decide
  have ed : Even (Fintype.card (Edges E S T)) := by
    obtain ⟨n,hn⟩ := evenEdges
    simp only [Edges, Fintype.card_sum]
    exact ⟨n + Fintype.card T,by omega⟩
  obtain ⟨f,balance⟩ := exists_balanced (aux D A B) (connected D A B conn) deg ed
  have opposite (t : T) : f (.inr (.inr (.inr t))) = !(f (.inr (.inr (.inl t)))) := by
    have e := balance (.inr t)
    rw [at_aux,at_aux] at e
    cases h : f (.inr (.inr (.inl t))) <;> cases h' : f (.inr (.inr (.inr t))) <;> simp_all
  refine ⟨(fun e => f (.inl e)), (fun s => f (.inr (.inl s))),
    (fun t => f (.inr (.inr (.inl t)))), fun v => ?_⟩
  have e := balance (.inl v)
  simpa only [at_base,opposite] using e

end Kostochka.FiveRegular.Auxiliary

end

section 

namespace Kostochka.FiveRegular.Restoration
open Finset Subdivision

/- Section 4. A shape records the ordered corners and edges used when putting paths and
cycles back into the two factors. It distinguishes alternating matching squares and
squares diverted to the exceptional subgraph. -/
inductive Shape where
  | isolated
  | path (n : ℕ)
  | evenCycle (n : ℕ)
  | markedPath
  | badPath
  | markedOdd (n : ℕ)
  | badOdd (n : ℕ)
  | divertedSquare
  | alternatingSquare
  deriving DecidableEq, Repr

inductive Role where
  | factor (b : Bool)
  | third
  | matching
  deriving DecidableEq, Repr

namespace Shape

def edges : Shape → ℕ
  | .isolated => 0
  | .path n => n + 1
  | .evenCycle n => 2 * (n + 1)
  | .markedPath | .badPath => 3
  | .markedOdd n | .badOdd n => 2 * n + 3
  | .divertedSquare | .alternatingSquare => 4

def cyclic : Shape → Bool
  | .isolated | .path _ | .markedPath | .badPath => false
  | _ => true

def vertices (t : Shape) := if t.cyclic then t.edges else t.edges + 1

def alt (first : Bool) (i : ℕ) : Bool := if i % 2 = 0 then first else !first

def role (t : Shape) (first second : Bool) (i : ℕ) : Role :=
  match t with
  | .isolated | .badPath | .badOdd _ | .divertedSquare => .third
  | .path _ | .evenCycle _ | .markedPath | .markedOdd _ => .factor (alt first i)
  | .alternatingSquare =>
    if first = second then
      if i = 0 then .factor first else if i = 2 then .factor (!first) else .matching
    else
      if i = 3 then .factor first else if i = 1 then .factor (!first) else .matching

theorem vertices_pos (t : Shape) : 0 < t.vertices := by
  cases t <;> simp [vertices,edges,cyclic]

theorem edges_le_vertices (t : Shape) : t.edges ≤ t.vertices := by
  unfold vertices
  split <;> omega

def family (t : Shape) : Family (Fin t.vertices) (Fin t.edges) where
  left e := ⟨e.val,lt_of_lt_of_le e.isLt t.edges_le_vertices⟩
  right e := if h : e.val + 1 < t.vertices then ⟨_,h⟩ else ⟨0,t.vertices_pos⟩

def inc (t : Shape) (selected : ℕ → Bool) (v : ℕ) : ℕ :=
  (if v < t.edges ∧ selected v = true then 1 else 0) +
  (if v = 0 then
    (if t.cyclic = true ∧ selected (t.edges - 1) = true then 1 else 0)
  else if selected (v - 1) = true then 1 else 0)

def factorDegree (t : Shape) (first second : Bool) (v : ℕ) (b : Bool) : ℕ :=
  t.inc (fun i => decide (t.role first second i = .factor b)) v

def thirdDegree (t : Shape) (first second : Bool) (v : ℕ) : ℕ :=
  t.inc (fun i => decide (t.role first second i = .third)) v

def matchingDegree (t : Shape) (first second : Bool) (v : ℕ) : ℕ :=
  t.inc (fun i => decide (t.role first second i = .matching)) v

def one (b c : Bool) : ℕ := if b = c then 1 else 0

def port (v atVertex : ℕ) (b color : Bool) : ℕ := if v = atVertex then one color b else 0

def portDegree (t : Shape) (first second : Bool) (v : ℕ) (b : Bool) : ℕ :=
  match t with
  | .path n => port v 0 b first + port v (n+1) b (alt first n)
  | .markedPath => port v 0 b first + port v 3 b first
  | .badPath => port v 0 b first + port v 3 b (!first)
  | .markedOdd _ => port v 0 b first + port v 0 b first
  | .alternatingSquare =>
    port v 0 b first + port v 2 b (!first) + port v 1 b second + port v 3 b (!second)
  | _ => 0

def lostPort (t : Shape) (first : Bool) (v : ℕ) (b : Bool) : ℕ :=
  if t = .badPath then port v 0 b first + port v 3 b (!first) else 0

def pairs (t : Shape) (v : ℕ) : ℕ :=
  match t with
  | .path n => if 0 < v ∧ v < n+1 then 1 else 0
  | .markedPath => if 0 < v ∧ v < 3 then 1 else 0
  | .evenCycle _ => 1
  | .markedOdd _ => if v = 0 then 0 else 1
  | _ => 0

private theorem alt_next (b : Bool) (i : ℕ) : alt b (i+1) = !alt b i := by
  unfold alt
  split <;> split <;> simp_all <;> omega

private theorem one_pair (a b : Bool) : one (!a) b + one a b = 1 := by cases a <;> cases b <;> decide

private theorem pathRule (first b : Bool) (n : ℕ) (v : ℕ) (hv : v < n+2) :
    (Shape.path n).factorDegree first false v b =
    port v 0 b first + port v (n+1) b (alt first n) + (if 0 < v ∧ v < n+1 then 1 else 0) := by
  cases v with
  | zero => simp [factorDegree,inc,role,edges,cyclic,alt,port,one]
  | succ k =>
    by_cases eq : k = n
    · subst k; simp [factorDegree,inc,role,edges,port,one]
    · have lt : k+1 < n+1 := by omega
      simpa [factorDegree,inc,role,edges,cyclic,lt,eq,alt_next,port,one] using one_pair (alt first k) b

private theorem cycleRule (t : Shape) (n : ℕ) (p q b : Bool) (v : ℕ)
    (cy : t.cyclic = true) (en : t.edges = n+1)
    (paint : ∀ i, t.role p q i = .factor (alt p i)) (hv : v < n+1) :
    t.factorDegree p q v b = if v = 0 then one p b + one (alt p n) b else 1 := by
  cases v with
  | zero =>
    by_cases h : alt p n = b <;> simp [factorDegree,inc,paint,en,cy,one,h,show alt p 0 = p by rfl]
  | succ k =>
    simpa [factorDegree,inc,paint,en,hv,cy,alt_next,one] using one_pair (alt p k) b

private theorem alt_even (p : Bool) (n : ℕ) : alt p (2*n+2) = p := by simp [alt]
private theorem alt_odd (p : Bool) (n : ℕ) : alt p (2*n+1) = !p := by simp [alt]

theorem restoreFactors (t : Shape) (first second : Bool) (v : Fin t.vertices) (b : Bool) :
    t.factorDegree first second v.val b + t.lostPort first v.val b =
      t.portDegree first second v.val b + t.pairs v.val := by
  cases t with
  | isolated =>
    have h : v.val = 0 := by have := v.isLt; simpa [vertices,cyclic,edges] using this
    simp [factorDegree,inc,role,edges,cyclic,portDegree,pairs,lostPort,h]
  | path n =>
    simpa [factorDegree,inc,role,portDegree,pairs,lostPort] using pathRule first b n v.val v.isLt
  | evenCycle n =>
    have k := cycleRule (.evenCycle n) (2*n+1) first second b v.val rfl
      (by simp [edges]; omega) (fun _ => rfl) (by have := v.isLt; simp [vertices,edges,cyclic] at this; omega)
    rw [alt_odd] at k
    by_cases hz : v.val = 0
    · simp only [hz] at k
      simp [portDegree,pairs,lostPort,hz,k,add_comm (one first b),one_pair] 
    · simpa [portDegree,pairs,lostPort,hz] using k
  | markedPath =>
    have k := pathRule first b 2 v.val v.isLt
    simpa [factorDegree,inc,role,cyclic,edges,portDegree,pairs,lostPort,alt] using k
  | markedOdd n =>
    have k := cycleRule (.markedOdd n) (2*n+2) first second b v.val rfl rfl (fun _ => rfl) v.isLt
    rw [alt_even] at k
    by_cases hz : v.val = 0 <;> simpa [portDegree,pairs,lostPort,port,hz] using k
  | badPath =>
    simp [factorDegree,inc,role,edges,cyclic,portDegree,pairs,lostPort]
  | badOdd n =>
    simp [factorDegree,inc,role,edges,cyclic,portDegree,pairs,lostPort]
  | divertedSquare =>
    simp [factorDegree,inc,role,edges,cyclic,portDegree,pairs,lostPort]
  | alternatingSquare =>
    change Fin 4 at v
    fin_cases v <;> cases first <;> cases second <;> cases b <;> decide

theorem restoreMatching (t : Shape) (first second : Bool) (v : Fin t.vertices) :
    t.matchingDegree first second v.val = if t = .alternatingSquare then 1 else 0 := by
  cases t <;> try simp [matchingDegree,inc,role,edges,cyclic]
  change Fin 4 at v
  fin_cases v <;> cases first <;> cases second <;> decide

private theorem left_iff (t : Shape) (v : Fin t.vertices) (e : Fin t.edges) :
    v = t.family.left e ↔ v.val = e.val := Fin.ext_iff

private theorem right_iff (t : Shape) (v : Fin t.vertices) (e : Fin t.edges) :
    v = t.family.right e ↔ if v.val = 0 then t.cyclic = true ∧ t.edges - 1 = e.val
      else v.val - 1 = e.val := by
  have ev := e.isLt
  have vv := v.isLt
  have ve := t.edges_le_vertices
  by_cases h : e.val+1 < t.vertices
  · have value : (t.family.right e).val = e.val+1 := by simp [family,h]
    rw [Fin.ext_iff,value]
    by_cases hz : v.val = 0
    · rw [if_pos hz]
      by_cases cy : t.cyclic = true
      · have sz : t.vertices = t.edges := by simp [vertices,cy]
        simp [cy]; omega
      · simp [cy]; omega
    · rw [if_neg hz]; omega
  · have value : (t.family.right e).val = 0 := by simp [family,h]
    rw [Fin.ext_iff,value]
    have cy : t.cyclic = true := by
      by_contra hn
      have sz : t.vertices = t.edges+1 := by simp [vertices,hn]
      omega
    have sz : t.vertices = t.edges := by simp [vertices,cy]
    by_cases hz : v.val = 0 <;> simp [hz,cy] <;> omega

private theorem sumPosition (n k : ℕ) (selected : ℕ → Bool) :
    (∑ e : Fin n, if k = e.val ∧ selected e.val = true then (1 : ℕ) else 0) =
    if k < n ∧ selected k = true then 1 else 0 := by
  by_cases hk : k < n
  · let j : Fin n := ⟨k,hk⟩
    have eq (e : Fin n) : k = e.val ↔ e = j := by simp [j,Fin.ext_iff,eq_comm]
    simp_rw [eq,ite_and]
    simp [j,hk]
  · have ne (e : Fin n) : k ≠ e.val := by have := e.isLt; omega
    simp [hk,ne]

theorem coloredDegree_family (t : Shape) (f : ℕ → Bool) (v : Fin t.vertices) :
    coloredDegree t.family (fun e => f e.val) v true = t.inc f v.val := by
  unfold coloredDegree inc
  simp_rw [left_iff,right_iff]
  rw [sumPosition]
  congr 1
  by_cases hz : v.val = 0
  · simp only [hz,if_true,eq_self]
    by_cases cy : t.cyclic = true
    · have pos : 0 < t.edges := by have := t.vertices_pos; simpa [vertices,cy] using this
      have lt : t.edges - 1 < t.edges := by omega
      simp only [cy,true_and,sumPosition,lt]
    · simp [cy]
  · simp only [if_neg hz]
    rw [sumPosition]
    have vv := v.isLt
    have vmax : t.vertices ≤ t.edges+1 := by unfold vertices; split <;> omega
    have lt : v.val - 1 < t.edges := by omega
    simp [lt]

theorem third_iff (t : Shape) (p q : Bool) (e : Fin t.edges) :
    t.role p q e.val = .third ↔
    t = .badPath ∨ (∃ n, t = .badOdd n) ∨ t = .divertedSquare := by
  cases t <;> simp [role,edges] at *
  · exact Fin.elim0 e
  · split_ifs <;> simp

theorem thirdStructure (t : Shape) (p q : Bool) (v : Fin t.vertices) :
    t.thirdDegree p q v.val = match t with
      | .badPath => if v.val = 0 ∨ v.val = 3 then 1 else 2
      | .badOdd _ | .divertedSquare => 2
      | _ => 0 := by
  have hv := v.isLt
  cases t with
  | badPath | divertedSquare =>
    change Fin 4 at v
    fin_cases v <;> rfl
  | badOdd n =>
    change v.val < 2*n+3 at hv
    by_cases h : v.val = 0 <;> simp [thirdDegree,inc,role,edges,cyclic,h,hv]
  | alternatingSquare =>
    change Fin 4 at v
    fin_cases v <;> cases p <;> cases q <;> decide
  | isolated =>
    have h : v.val = 0 := by simpa [vertices,cyclic,edges] using hv
    simp [thirdDegree,inc,role,edges,cyclic,h]
  | _ => simp [thirdDegree,inc,role,edges,cyclic]

theorem inside_at_most_one (t : Shape) (p q side : Bool) (v : Fin t.vertices)
    (normalized : (∃ n, t = .markedOdd n) → p ≠ side) : t.factorDegree p q v.val side ≤ 1 := by
  have eq := restoreFactors t p q v side
  cases t with
  | path n =>
    simp only [lostPort,reduceCtorEq,if_false,add_zero,portDegree,pairs] at eq
    rw [eq]
    by_cases l : v.val = 0 <;> by_cases r : v.val = n+1 <;>
      simp [port,one,l,r] <;> split_ifs <;> omega
  | markedPath =>
    change Fin 4 at v
    fin_cases v <;> cases p <;> cases side <;> cases q <;> decide
  | evenCycle n =>
    simpa [lostPort,portDegree,pairs] using eq.le
  | markedOdd n =>
    have ne := normalized ⟨n,rfl⟩
    simp only [lostPort,reduceCtorEq,if_false,add_zero] at eq
    rw [eq]
    by_cases l : v.val = 0 <;> simp [portDegree,pairs,port,one,l,ne]
  | alternatingSquare =>
    change Fin 4 at v
    fin_cases v <;> cases p <;> cases q <;> cases side <;> decide
  | _ => simp [factorDegree,inc,role,cyclic]

theorem partition_incidence (t : Shape) (p q : Bool) (v : Fin t.vertices) :
    t.factorDegree p q v.val false + t.factorDegree p q v.val true +
      t.thirdDegree p q v.val + t.matchingDegree p q v.val = t.inc (fun _ => true) v.val := by
  let on (flag : Bool) (x r : Role) : ℕ := if flag = true ∧ x = r then 1 else 0
  have all (flag : Bool) (x : Role) :
      on flag x (.factor false) + on flag x (.factor true) + on flag x .third +
      on flag x .matching = if flag then 1 else 0 := by
    cases flag
    · simp [on]
    · cases x with
      | factor c => cases c <;> decide
      | _ => decide
  let out := decide (v.val < t.edges)
  let inp := decide (v.val ≠ 0 ∨ t.cyclic = true)
  let pred := if v.val = 0 then t.edges-1 else v.val-1
  let c := t.role p q v.val
  let d := t.role p q pred
  have count (r : Role) : t.inc (fun i => decide (t.role p q i = r)) v.val =
      on out c r + on inp d r := by
    by_cases h : v.val = 0 <;> simp [inc,on,out,inp,pred,c,d,h]
  have active : t.inc (fun _ => true) v.val = (if out then 1 else 0) + (if inp then 1 else 0) := by
    by_cases h : v.val = 0 <;> simp [inc,out,inp,h]
  unfold factorDegree thirdDegree matchingDegree
  simp only [count,active]
  have ho := all out c
  have hi := all inp d
  omega

theorem lostPort_le_one (t : Shape) (p b : Bool) (v : ℕ) : t.lostPort p v b ≤ 1 := by
  by_cases h : t = .badPath
  · subst t
    by_cases h₀ : v = 0 <;> by_cases h₃ : v = 3 <;>
      simp [lostPort,port,h₀,h₃,one] <;> split_ifs <;> omega
  · simp [lostPort,h]

theorem restoredDegrees (t : Shape) (p q : Bool) (v : Fin t.vertices) (outside : Bool → ℕ)
    (eqAux : outside false + t.portDegree p q v false = outside true + t.portDegree p q v true)
    (regular : outside false + outside true + t.inc (fun _ => true) v.val =
      4 + t.matchingDegree p q v.val) :
    let f b := outside b + t.factorDegree p q v.val b
    f false ≤ 2 ∧ f true ≤ 2 ∧ (t.thirdDegree p q v.val = 2 → f false = 1 ∧ f true = 1) ∧
      f false + t.lostPort p v.val false = f true + t.lostPort p v.val true := by
  have full := t.partition_incidence p q v
  have lf := t.restoreFactors p q v false
  have rt := t.restoreFactors p q v true
  have al := t.lostPort_le_one p false v
  have ar := t.lostPort_le_one p true v
  dsimp only
  omega

theorem badPathEndpoints (p q : Bool) (v : Fin Shape.badPath.vertices) (outside : Bool → ℕ)
    (eqAux : outside false + Shape.badPath.portDegree p q v false =
      outside true + Shape.badPath.portDegree p q v true)
    (regular : outside false + outside true + Shape.badPath.inc (fun _ => true) v.val = 4) :
    let f b := outside b + Shape.badPath.factorDegree p q v.val b
    (v.val = 0 → f p = 1 ∧ f (!p) = 2) ∧ (v.val = 3 → f p = 2 ∧ f (!p) = 1) := by
  have pair := Shape.badPath.restoreMatching p q v
  simp only [reduceCtorEq,if_false] at pair
  have aligned := Shape.badPath.restoredDegrees p q v outside eqAux (by simpa [pair] using regular)
  have size := Shape.badPath.partition_incidence p q v
  have th := Shape.badPath.thirdStructure p q v
  let f b := outside b + Shape.badPath.factorDegree p q v.val b
  have full : f false + f true + Shape.badPath.thirdDegree p q v.val = 4 := by dsimp [f]; omega
  have bal : f false + Shape.badPath.lostPort p v.val false =
      f true + Shape.badPath.lostPort p v.val true := aligned.2.2.2
  change (v.val = 0 → f p = 1 ∧ f (!p) = 2) ∧ (v.val = 3 → f p = 2 ∧ f (!p) = 1)
  have permute : f p + f (!p) + Shape.badPath.thirdDegree p q v.val = 4 := by
    cases p
    · exact full
    · simpa only [Bool.not_true,add_comm (f true) (f false)] using full
  have ord : f p + Shape.badPath.lostPort p v.val p =
      f (!p) + Shape.badPath.lostPort p v.val (!p) := by
    cases p
    · exact bal
    · exact bal.symm
  constructor <;> intro h
  · have unit : Shape.badPath.thirdDegree p q v.val = 1 := th.trans (by simp [h])
    have a : Shape.badPath.lostPort p v.val p = 1 := by cases p <;> simp [lostPort,port,one,h]
    have b : Shape.badPath.lostPort p v.val (!p) = 0 := by cases p <;> simp [lostPort,port,one,h]
    omega
  · have unit : Shape.badPath.thirdDegree p q v.val = 1 := th.trans (by simp [h])
    have a : Shape.badPath.lostPort p v.val p = 0 := by cases p <;> simp [lostPort,port,one,h]
    have b : Shape.badPath.lostPort p v.val (!p) = 1 := by cases p <;> simp [lostPort,port,one,h]
    omega

end Shape
end Kostochka.FiveRegular.Restoration

end

section 

namespace Kostochka.FiveRegular

open SimpleGraph Subdivision Finset

variable {V E : Type*}

def familyPair (D : Family V E) (e : E) := s(D.left e, D.right e)

def support (D : Family V E) : SimpleGraph V := fromEdgeSet (Set.range (familyPair D))

def Loopless (D : Family V E) : Prop := ∀ e, D.left e ≠ D.right e

def AtMostTwo (D : Family V E) : Prop := ∀ v e f g, FamilyIncident D v e →
  FamilyIncident D v f → FamilyIncident D v g → e = f ∨ e = g ∨ f = g

def supportEdge (D : Family V E) (hl : Loopless D) (e : E) : (support D).edgeSet :=
  ⟨familyPair D e, show (support D).Adj (D.left e) (D.right e) from ⟨⟨e,rfl⟩, hl e⟩⟩

theorem mem_supportEdge (D : Family V E) (hl : Loopless D) (v : V) (e : E) :
    v ∈ (supportEdge D hl e).val ↔ FamilyIncident D v e := Sym2.mem_iff

private theorem supportEdge_surj (D : Family V E) (hl : Loopless D) :
    Function.Surjective (supportEdge D hl) := by
  rintro ⟨⟨x,y⟩, h⟩
  have hh : (support D).Adj x y := h
  obtain ⟨e, he⟩ := hh.1
  exact ⟨e, Subtype.ext he⟩

theorem degree_support_le_two [Fintype V] (D : Family V E)
    [DecidableRel (support D).Adj] (bound : AtMostTwo D) : ∀ v, (support D).degree v ≤ 2 := by
  classical
  intro v
  by_contra! h
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ :=
    two_lt_card_iff.mp (show 2 < ((support D).neighborFinset v).card by simpa using h)
  have find (w : V) (hw : w ∈ (support D).neighborFinset v) :
      ∃ e, familyPair D e = s(v,w) ∧ FamilyIncident D v e := by
    obtain ⟨e, he⟩ := (((support D).mem_neighborFinset v w).mp hw).1
    refine ⟨e,he,Sym2.mem_iff.mp ?_⟩
    change v ∈ familyPair D e
    rw [he]
    simp
  obtain ⟨e, he, hi⟩ := find a ha
  obtain ⟨f, hf, hj⟩ := find b hb
  obtain ⟨g, hg, hk⟩ := find c hc
  have cancel {x y : V} (eq : s(v,x) = s(v,y)) : x = y := by
    rcases Sym2.eq_iff.mp eq with h | h
    · exact h.2
    · exact h.2.trans h.1
  rcases bound v e f g hi hj hk with rfl | rfl | rfl
  · exact hab (cancel (he.symm.trans hf))
  · exact hac (cancel (he.symm.trans hg))
  · exact hbc (cancel (hf.symm.trans hg))

structure SimpleEdgePalette (G : SimpleGraph V) (paint : V → Option (Fin 3)) where
  edge : G.edgeSet → Fin 3
  proper : ∀ e f, e ≠ f → (∃ v : V, v ∈ e.val ∧ v ∈ f.val) → edge e ≠ edge f
  incident : ∀ v e b, paint v = some b → v ∈ e.val → edge e ≠ b

def ParallelCompatible (D : Family V E) (paint : V → Option (Fin 3)) : Prop :=
  ∀ e f, e ≠ f → familyPair D e = familyPair D f →
    ∀ v w a b, FamilyIncident D v e → FamilyIncident D w e →
      paint v = some a → paint w = some b → a = b

theorem color_labeled_of_support (D : Family V E) (hl : Loopless D) (bound : AtMostTwo D)
    (paint : V → Option (Fin 3)) (hpar : ParallelCompatible D paint)
    (P : SimpleEdgePalette (support D) paint) :
    ∃ color : E → Fin 3,
      (∀ e f, e ≠ f → FamilyMeet D e f → color e ≠ color f) ∧
      (∀ v e b, paint v = some b → FamilyIncident D v e → color e ≠ b) := by
  classical
  let π := supportEdge D hl
  let rep (k : (support D).edgeSet) := (supportEdge_surj D hl k).choose
  have rep_spec (k : (support D).edgeSet) : π (rep k) = k := (supportEdge_surj D hl k).choose_spec
  let hasColor (k : (support D).edgeSet) (a : Fin 3) := ∃ v : V, v ∈ k.val ∧ paint v = some a
  let forbidden (k : (support D).edgeSet) : Fin 3 :=
    if h : ∃ a, hasColor k a then h.choose else 0
  let alt (k : (support D).edgeSet) := (exists_third_color (P.edge k) (forbidden k)).choose
  have alt_spec k : alt k ≠ P.edge k ∧ alt k ≠ forbidden k :=
    (exists_third_color (P.edge k) (forbidden k)).choose_spec
  let color e := if e = rep (π e) then P.edge (π e) else alt (π e)
  have localRep {e f} (h : π e ≠ π f) (hm : FamilyMeet D e f) : e = rep (π e) := by
    obtain ⟨v, he, hf⟩ := hm
    have hit := (mem_supportEdge D hl v e).mpr he
    have hrep : FamilyIncident D v (rep (π e)) := (mem_supportEdge D hl v _).mp (by
      change v ∈ (π (rep (π e))).val
      rw [rep_spec]
      exact hit)
    rcases bound v e f (rep (π e)) he hf hrep with eq | eq | eq
    · exact (h (congrArg π eq)).elim
    · exact eq
    · exact (h ((congrArg π eq).trans (rep_spec _)).symm).elim
  refine ⟨color, ?_, ?_⟩
  · intro e f hn hm
    by_cases hk : π e = π f
    · by_cases hr : e = rep (π e)
      · have hr' : f ≠ rep (π f) := fun h => hn (hr.trans ((congrArg rep hk).trans h.symm))
        simpa only [color, if_pos hr, if_neg hr', hk] using (alt_spec (π f)).1.symm
      · have hr' : f = rep (π f) := by
          obtain ⟨v,he,hf⟩ := hm
          have hit := (mem_supportEdge D hl v f).mpr hf
          have hex : FamilyIncident D v (rep (π f)) := (mem_supportEdge D hl v _).mp (by
            change v ∈ (π (rep (π f))).val
            rwa [rep_spec])
          rcases bound v e f (rep (π f)) he hf hex with h | h | h
          · exact (hn h).elim
          · exact (hr (h.trans (congrArg rep hk.symm))).elim
          · exact h
        simpa only [color, if_neg hr, if_pos hr', hk] using (alt_spec (π f)).1
    · obtain ⟨v, he, hf⟩ := hm
      have h₁ := localRep hk ⟨v, he, hf⟩
      have h₂ := localRep (Ne.symm hk) ⟨v, hf, he⟩
      simp only [color, if_pos h₁, if_pos h₂]
      exact P.proper _ _ hk ⟨v, (mem_supportEdge D hl v e).mpr he, (mem_supportEdge D hl v f).mpr hf⟩
  · intro v e b hv he
    by_cases hr : e = rep (π e)
    · simpa only [color, if_pos hr] using P.incident v (π e) b hv ((mem_supportEdge D hl v e).mpr he)
    · have heq : familyPair D e = familyPair D (rep (π e)) := congrArg Subtype.val (rep_spec (π e)).symm
      have hb : hasColor (π e) b := ⟨v, (mem_supportEdge D hl v e).mpr he, hv⟩
      have hex : ∃ a, hasColor (π e) a := ⟨b,hb⟩
      obtain ⟨w,hw,hwc⟩ := hex.choose_spec
      have eq := hpar e _ hr heq v w b hex.choose he ((mem_supportEdge D hl w e).mp hw) hv hwc
      simpa only [color, if_neg hr, forbidden, dif_pos hex, eq] using (alt_spec (π e)).2

end Kostochka.FiveRegular

end

section 

namespace Kostochka.FiveRegular.Auxiliary
open Finset Subdivision
variable {V E S T C : Type*}

def Balanced [Fintype E] [Fintype S] [Fintype T] [DecidableEq V]
    (D : Family V E) (A : Family V S) (B : Family V T)
    (f : E → Bool) (g : S → Bool) (k : T → Bool) : Prop := ∀ v,
    coloredDegree D f v true + coloredDegree A g v true + endCount B k (fun t => !(k t)) v true =
    coloredDegree D f v false + coloredDegree A g v false + endCount B k (fun t => !(k t)) v false

theorem Balanced.flip [Fintype E] [Fintype S] [Fintype T] [DecidableEq V]
    {D : Family V E} {A : Family V S} {B : Family V T} {f g k}
    (h : Balanced D A B f g k) : Balanced D A B (fun e => !f e) (fun s => !g s) (fun t => !k t) := by
  intro v
  simpa [coloredDegree,endCount,Bool.not_eq_true',Bool.not_eq_false'] using (h v).symm

theorem partition_with_mark [Fintype V] [Fintype E] [Fintype S] [Fintype T]
    [DecidableEq V] [DecidableEq E] [DecidableEq S] [DecidableEq T]
    (D : Family V E) (A : Family V S) (B : Family V T)
    (conn : ∀ v w, Relation.ReflTransGen (Joined D) v w)
    (dv : ∀ v, Even (coloredDegree D (fun _ => true) v true +
      coloredDegree A (fun _ => true) v true + coloredDegree B (fun _ => true) v true))
    (de : Even (Fintype.card E + Fintype.card S)) (mark : Option (S × Bool)) :
    ∃ f g k, Balanced D A B f g k ∧ ∀ s b, mark = some (s,b) → g s = b := by
  obtain ⟨f,g,k,h⟩ := partition D A B conn dv de
  have hb : Balanced D A B f g k := h
  cases mark with
  | none => exact ⟨f,g,k,hb,by simp⟩
  | some pair =>
    obtain ⟨s,b⟩ := pair
    by_cases good : g s = b
    · exact ⟨f,g,k,hb,by intro x y he; cases he; exact good⟩
    · exact ⟨_,_,_,hb.flip,by intro x y he; cases he; cases hv : g s <;> cases b <;> simp_all⟩

def fiber (D : Family V E) (home : V → C) (within : ∀ e, home (D.left e) = home (D.right e))
    (c : C) : Family {v // home v = c} {e // home (D.left e) = c} where
  left e := ⟨D.left e.val,e.property⟩
  right e := ⟨D.right e.val,(within e.val).symm.trans e.property⟩

def assemble (D : Family V E) (home : V → C)
    (pick : (c : C) → {e // home (D.left e) = c} → Bool) (e : E) : Bool :=
  pick (home (D.left e)) ⟨e,rfl⟩

private theorem assemble_at (D : Family V E) (home : V → C) (pick) {c e} (he : home (D.left e) = c) :
    assemble D home pick e = pick c ⟨e,he⟩ := by subst c; rfl

private theorem restrict_sum [Fintype E] [DecidableEq C] (group : E → C) (c : C) (f : E → ℕ)
    (zero : ∀ e, group e ≠ c → f e = 0) : (∑ e : {e // group e = c}, f e.val) = ∑ e : E, f e := by
  classical
  rw [← Finset.sum_subtype (univ.filter (fun e => group e = c)) (fun e => by simp) f]
  apply sum_subset (filter_subset _ _)
  intro e _ hn
  exact zero e (fun eq => hn (mem_filter.mpr ⟨mem_univ _,eq⟩))

private theorem count_at [Fintype E] [DecidableEq C] [DecidableEq V]
    (D : Family V E) (home : V → C) (within : ∀ e, home (D.left e) = home (D.right e))
    (left right : (c : C) → {e // home (D.left e) = c} → Bool) (v : V) (b : Bool) :
    endCount (fiber D home within (home v)) (left _) (right _) ⟨v,rfl⟩ b =
      endCount D (assemble D home left) (assemble D home right) v b := by
  classical
  unfold endCount
  apply congrArg₂ (· + ·)
  · rw [← restrict_sum (fun e => home (D.left e)) (home v)
        (fun e => if v = D.left e ∧ assemble D home left e = b then 1 else 0)
        (fun e hn => by have ne : v ≠ D.left e := fun eq => hn (congrArg home eq.symm); simp [ne])]
    apply sum_congr rfl
    rintro ⟨e,he⟩ _
    simp only [fiber,Subtype.mk.injEq,assemble_at D home left he]
  · rw [← restrict_sum (fun e => home (D.left e)) (home v)
        (fun e => if v = D.right e ∧ assemble D home right e = b then 1 else 0)
        (fun e hn => by have ne : v ≠ D.right e := fun eq => hn ((within e).trans (congrArg home eq.symm)); simp [ne])]
    apply sum_congr rfl
    rintro ⟨e,he⟩ _
    simp only [fiber,Subtype.mk.injEq,assemble_at D home right he]

theorem degree_at_component [Fintype E] [DecidableEq C] [DecidableEq V]
    (D : Family V E) (home : V → C) (within : ∀ e, home (D.left e) = home (D.right e))
    (pick : (c : C) → {e // home (D.left e) = c} → Bool) {v : V} {c : C} (hv : home v = c) (b : Bool) :
    coloredDegree (fiber D home within c) (pick c) ⟨v,hv⟩ b = coloredDegree D (assemble D home pick) v b := by
  subst c
  exact count_at D home within pick pick v b

end Kostochka.FiveRegular.Auxiliary

end

section 

namespace Kostochka.FiveRegular.Auxiliary
open Finset Subdivision Restoration

def direct : Shape → Bool
  | .path n => decide (n % 2 = 0)
  | .markedOdd _ | .markedPath => true
  | _ => false

def opposites : Shape → ℕ
  | .path n => n % 2
  | .badPath => 1
  | .alternatingSquare => 2
  | _ => 0

def directRight : Shape → ℕ
  | .path n => n + 1
  | .markedPath => 3
  | _ => 0

def oppositeEnd (t : Shape) (j : ℕ) : ℕ × ℕ :=
  match t with
  | .path n => (0,n+1)
  | .badPath => (0,3)
  | .alternatingSquare => (j,j+2)
  | _ => (0,0)

def unmarkedBad : Shape → Bool
  | .badOdd _ | .badPath => true
  | _ => false

def residualCount (s : Shape) : ℕ := if s = .alternatingSquare then 2 else s.edges

theorem edge_parity (s : Shape) :
    residualCount s % 2 = ((if direct s then 1 else 0) + (if unmarkedBad s then 1 else 0)) % 2 := by
  cases s <;> simp [residualCount,Shape.edges,direct,unmarkedBad]
  split <;> omega

def vertexAt (s : Shape) (i : ℕ) : Fin s.vertices := ⟨i % s.vertices, Nat.mod_lt _ s.vertices_pos⟩

variable {I V : Type*} (shape : I → Shape) (place : ∀ i, Fin (shape i).vertices → V)

abbrev DirectEdges := {i : I // direct (shape i) = true}
abbrev OppositeEdges := Σ i : I, Fin (opposites (shape i))

def directFamily : Family V (DirectEdges shape) where
  left e := place e.val (vertexAt (shape e.val) 0)
  right e := place e.val (vertexAt (shape e.val) (directRight (shape e.val)))

def oppositeFamily : Family V (OppositeEdges shape) where
  left e := place e.1 (vertexAt (shape e.1) (oppositeEnd (shape e.1) e.2.val).1)
  right e := place e.1 (vertexAt (shape e.1) (oppositeEnd (shape e.1) e.2.val).2)

theorem even_direct_edges [Fintype I] (external : ℕ)
    (allEven : Even (external + ∑ i, residualCount (shape i)))
    (badEven : Even (∑ i, (if unmarkedBad (shape i) then 1 else 0 : ℕ))) :
    Even (external + Fintype.card (DirectEdges shape)) := by
  classical
  have localEq (i) : residualCount (shape i) % 2 =
    ((if direct (shape i) then 1 else 0) + (if unmarkedBad (shape i) then 1 else 0)) % 2 := edge_parity _
  have aux (s : Finset I) : (∑ i ∈ s, residualCount (shape i)) % 2 =
      ((∑ i ∈ s, if direct (shape i) then 1 else 0) +
       (∑ i ∈ s, if unmarkedBad (shape i) then 1 else 0)) % 2 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp only [sum_insert hi]
      have e := localEq i
      omega
  have cnt : Fintype.card (DirectEdges shape) = ∑ i, (if direct (shape i) then 1 else 0 : ℕ) := by
    rw [Fintype.card_subtype]
    simp
  have a := aux univ
  rw [Nat.even_iff] at allEven badEven ⊢
  rw [cnt]; omega

def oldDegree (s : Shape) (v : ℕ) : ℕ :=
  s.inc (fun e => decide (s ≠ .alternatingSquare ∨ e % 2 = 0)) v

def connectorDegree (s : Shape) (v : ℕ) : ℕ :=
  (if direct s then (if v = 0 then 1 else 0) + (if v = directRight s then 1 else 0) else 0) +
    ∑ j ∈ Finset.range (opposites s), ((if v = (oppositeEnd s j).1 then 1 else 0) +
                              (if v = (oppositeEnd s j).2 then 1 else 0))

theorem degree_parity (s : Shape) (v : Fin s.vertices) :
    oldDegree s v % 2 = connectorDegree s v % 2 := by
  have hv := v.isLt
  cases s with
  | path n =>
    change v.val < n+2 at hv
    have old : oldDegree (.path n) v = (if v.val < n+1 then 1 else 0) + (if v.val = 0 then 0 else 1) := by
      simp [oldDegree,Shape.inc,Shape.cyclic,Shape.edges]
    have conn : connectorDegree (.path n) v = (if v.val = 0 then 1 else 0) + (if v.val = n+1 then 1 else 0) := by
      by_cases h : n % 2 = 0
      · simp [connectorDegree,direct,directRight,opposites,h]
        rfl
      · have odd : n % 2 = 1 := by omega
        simp [connectorDegree,direct,opposites,oppositeEnd,odd]
        rfl
    rw [old,conn]
    split_ifs <;> omega
  | evenCycle n =>
    change v.val < 2*(n+1) at hv
    simp [oldDegree,Shape.inc,Shape.cyclic,Shape.edges,connectorDegree,direct,opposites,hv]
  | markedOdd n =>
    change v.val < 2*n+3 at hv
    by_cases hz : v.val = 0 <;> simp [oldDegree,Shape.inc,Shape.cyclic,Shape.edges,connectorDegree,direct,opposites,directRight,hv,hz]
  | badOdd n =>
    change v.val < 2*n+3 at hv
    simp [oldDegree,Shape.inc,Shape.cyclic,Shape.edges,connectorDegree,direct,opposites,hv]
  | isolated | markedPath | badPath | alternatingSquare | divertedSquare =>
    revert v
    decide

end Kostochka.FiveRegular.Auxiliary

end

section 

namespace Kostochka.FiveRegular.Auxiliary
open Finset Subdivision Restoration

variable {I V : Type*} [Fintype I] [DecidableEq V]
variable (shape : I → Shape) (pos : (Σ i, Fin (shape i).vertices) ≃ V)

def directColor (g : DirectEdges shape → Bool) (i : I) : Bool :=
  if h : direct (shape i) = true then g ⟨i,h⟩ else false

def oppositeColor (k : OppositeEdges shape → Bool) (i : I) (j : ℕ) : Bool :=
  if h : j < opposites (shape i) then k ⟨i,⟨j,h⟩⟩ else false

def firstPort (g : DirectEdges shape → Bool) (k : OppositeEdges shape → Bool) (i : I) : Bool :=
  if direct (shape i) then directColor shape g i else oppositeColor shape k i 0

def secondPort (k : OppositeEdges shape → Bool) (i : I) : Bool := oppositeColor shape k i 1

private theorem directAt (g : DirectEdges shape → Bool) (i : I) (v : Fin (shape i).vertices)
    (b : Bool) (atPos : ∀ e : DirectEdges shape, Fin (shape e.val).vertices) :
    (∑ e : DirectEdges shape, if pos ⟨i,v⟩ = pos ⟨e.val,atPos e⟩ ∧ g e = b then 1 else 0) =
      if h : direct (shape i) = true then
        (if v = atPos ⟨i,h⟩ ∧ g ⟨i,h⟩ = b then 1 else 0 : ℕ) else 0 := by
  classical
  by_cases h : direct (shape i) = true
  · rw [dif_pos h,Finset.sum_eq_single (⟨i,h⟩ : DirectEdges shape)]
    · simp
    · intro e _ ne
      have neq : pos ⟨i,v⟩ ≠ pos ⟨e.val,atPos e⟩ :=
        fun eq => ne (Subtype.ext (congrArg Sigma.fst (pos.injective eq)).symm)
      simp [neq]
    · simp
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro e _
    have neq : pos ⟨i,v⟩ ≠ pos ⟨e.val,atPos e⟩ := by
      intro eq
      have hi : i = e.val := congrArg Sigma.fst (pos.injective eq)
      exact h (hi.symm ▸ e.property)
    simp [neq]

private theorem oppositeAt (k : OppositeEdges shape → Bool) (i : I) (v : Fin (shape i).vertices)
    (b : Bool) (atPos : ∀ i, Fin (opposites (shape i)) → Fin (shape i).vertices) :
    (∑ e : OppositeEdges shape, if pos ⟨i,v⟩ = pos ⟨e.1,atPos e.1 e.2⟩ ∧ k e = b then 1 else 0) =
      ∑ j : Fin (opposites (shape i)), (if v = atPos i j ∧ k ⟨i,j⟩ = b then 1 else 0 : ℕ) := by
  classical
  rw [Fintype.sum_sigma,Finset.sum_eq_single i]
  · simp
  · intro a _ ne
    apply Finset.sum_eq_zero
    intro e _
    have neq : pos ⟨i,v⟩ ≠ pos ⟨a,atPos a e⟩ :=
      fun eq => ne (congrArg Sigma.fst (pos.injective eq)).symm
    simp [neq]
  · simp

theorem directRight_lt (s : Shape) : directRight s < s.vertices := by
  cases s <;> simp [directRight,Shape.vertices,Shape.edges,Shape.cyclic]

theorem oppositeEnd_lt (s : Shape) (j : Fin (opposites s)) :
    (oppositeEnd s j).1 < s.vertices ∧ (oppositeEnd s j).2 < s.vertices := by
  have hj := j.isLt
  cases s <;> simp [opposites,oppositeEnd,Shape.vertices,Shape.edges,Shape.cyclic] at hj ⊢
  omega

def portSum (s : Shape) (d : Bool) (k : ℕ → Bool) (v : ℕ) (b : Bool) : ℕ :=
  (if direct s then Shape.port v 0 b d + Shape.port v (directRight s) b d else 0) +
  ∑ j ∈ Finset.range (opposites s),
    (Shape.port v (oppositeEnd s j).1 b (k j) + Shape.port v (oppositeEnd s j).2 b (!(k j)))

theorem portSum_eq (s : Shape) (d : Bool) (k : ℕ → Bool) (v : ℕ) (b : Bool) :
    portSum s d k v b = s.portDegree (if direct s then d else k 0) (k 1) v b := by
  cases s with
  | path n =>
    by_cases even : n % 2 = 0
    · simp [portSum,direct,opposites,directRight,Shape.portDegree,Shape.alt,even]
    · have odd : n % 2 = 1 := by omega
      simp [portSum,direct,opposites,oppositeEnd,Shape.portDegree,Shape.alt,odd]
  | alternatingSquare =>
    simp [portSum,direct,opposites,oppositeEnd,Shape.portDegree,Finset.sum_range_succ]
    omega
  | isolated | evenCycle _ | markedPath | badPath | markedOdd _ | badOdd _ | divertedSquare =>
    simp [portSum,direct,opposites,directRight,oppositeEnd,Shape.portDegree]

private theorem count_pos (s : Shape) (v : Fin s.vertices) (j : ℕ) (hj : j < s.vertices) (c b : Bool) :
    (if v = vertexAt s j ∧ c = b then 1 else 0) = Shape.port v.val j b c := by
  have eq : v = vertexAt s j ↔ v.val = j := by simp [Fin.ext_iff,vertexAt,Nat.mod_eq_of_lt hj]
  by_cases hv : v.val = j <;> simp [Shape.port,Shape.one,eq,hv]

theorem ports_at (g : DirectEdges shape → Bool) (k : OppositeEdges shape → Bool)
    (i : I) (v : Fin (shape i).vertices) (b : Bool) :
    coloredDegree (directFamily shape (fun a x => pos ⟨a,x⟩)) g (pos ⟨i,v⟩) b +
      endCount (oppositeFamily shape (fun a x => pos ⟨a,x⟩)) k (fun e => !k e) (pos ⟨i,v⟩) b =
      (shape i).portDegree (firstPort shape g k i) (secondPort shape k i) v.val b := by
  classical
  let s := shape i
  rw [show (shape i).portDegree (firstPort shape g k i) (secondPort shape k i) v.val b =
    portSum (shape i) (directColor shape g i) (oppositeColor shape k i) v.val b from (portSum_eq ..).symm]
  unfold coloredDegree endCount
  simp only [directFamily,oppositeFamily]
  erw [directAt shape pos g i v b (fun e => vertexAt (shape e.val) 0),
    directAt shape pos g i v b (fun e => vertexAt (shape e.val) (directRight (shape e.val))),
    oppositeAt shape pos k i v b (fun j u => vertexAt (shape j) (oppositeEnd (shape j) u).1),
    oppositeAt shape pos (fun e => !k e) i v b (fun j u => vertexAt (shape j) (oppositeEnd (shape j) u).2)]
  let f (j : ℕ) := Shape.port v.val (oppositeEnd s j).1 b (oppositeColor shape k i j)
  let r (j : ℕ) := Shape.port v.val (oppositeEnd s j).2 b (!(oppositeColor shape k i j))
  have hleft (j : Fin (opposites (shape i))) :
      (if v = vertexAt (shape i) (oppositeEnd (shape i) j).1 ∧ k ⟨i,j⟩ = b then 1 else 0) = f j := by
    simpa [f,s,oppositeColor,j.isLt] using count_pos _ v _ (oppositeEnd_lt _ j).1 (k ⟨i,j⟩) b
  have hright (j : Fin (opposites (shape i))) :
      (if v = vertexAt (shape i) (oppositeEnd (shape i) j).2 ∧ (!k ⟨i,j⟩) = b then 1 else 0) = r j := by
    simpa [r,s,oppositeColor,j.isLt] using count_pos _ v _ (oppositeEnd_lt _ j).2 (!k ⟨i,j⟩) b
  simp only [hleft,hright,Fin.sum_univ_eq_sum_range]
  unfold portSum
  rw [Finset.sum_add_distrib]
  have ez := (shape i).vertices_pos
  by_cases hd : direct (shape i) = true
  · simp only [hd,dif_pos,if_true,directColor]
    rw [count_pos _ _ _ ez,count_pos _ _ _ (directRight_lt _)]
  · simp [hd]
    rfl

end Kostochka.FiveRegular.Auxiliary

end

section 

namespace Kostochka.FiveRegular.Auxiliary
open Finset Subdivision Restoration
variable {I V E S T : Type*}

private theorem count_split {X : Type*} [Fintype X] (p : X → Prop) [DecidablePred p] (f : X → Bool) :
    (∑ x, if p x ∧ f x = true then 1 else 0) + (∑ x, if p x ∧ f x = false then 1 else 0) =
      ∑ x, (if p x then 1 else 0 : ℕ) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  cases f x <;> by_cases hp : p x <;> simp [hp]

theorem end_split [Fintype E] [DecidableEq V] (D : Family V E) (l r : E → Bool) (v : V) :
    endCount D l r v true + endCount D l r v false = coloredDegree D (fun _ => true) v true := by
  unfold endCount coloredDegree
  simp only [eq_self, and_true]
  have h₁ := count_split (fun e => v = D.left e) l
  have h₂ := count_split (fun e => v = D.right e) r
  omega

theorem degree_split [Fintype E] [DecidableEq V] (D : Family V E) (f : E → Bool) (v : V) :
    coloredDegree D f v true + coloredDegree D f v false = coloredDegree D (fun _ => true) v true :=
  end_split D f f v

private theorem port_split (v w : ℕ) (f : Bool) :
    Shape.port v w true f + Shape.port v w false f = if v = w then 1 else 0 := by
  by_cases h : v = w <;> cases f <;> simp [Shape.port,Shape.one,h]

theorem all_ports (s : Shape) (d : Bool) (k : ℕ → Bool) (v : ℕ) :
    portSum s d k v true + portSum s d k v false = connectorDegree s v := by
  unfold portSum connectorDegree
  have haux : ∀ j : ℕ,
      (Shape.port v (oppositeEnd s j).1 true (k j) + Shape.port v (oppositeEnd s j).2 true (!(k j))) +
      (Shape.port v (oppositeEnd s j).1 false (k j) + Shape.port v (oppositeEnd s j).2 false (!(k j))) =
      (if v = (oppositeEnd s j).1 then 1 else 0) + (if v = (oppositeEnd s j).2 then 1 else 0) := by
    intro j
    have a := port_split v (oppositeEnd s j).1 (k j)
    have c := port_split v (oppositeEnd s j).2 (!(k j))
    omega
  have sum := Finset.sum_congr (s₁ := range (opposites s)) rfl (fun j _ => haux j)
  rw [Finset.sum_add_distrib] at sum
  have a := port_split v 0 d
  have c := port_split v (directRight s) d
  split <;> omega

variable [Fintype I] [DecidableEq V] [Fintype E]
variable (shape : I → Shape) (pos : (Σ i, Fin (shape i).vertices) ≃ V) (D : Family V E)

theorem all_ports_at (i : I) (v : Fin (shape i).vertices) :
    coloredDegree (directFamily shape (fun a x => pos ⟨a,x⟩)) (fun _ => true) (pos ⟨i,v⟩) true +
    coloredDegree (oppositeFamily shape (fun a x => pos ⟨a,x⟩)) (fun _ => true) (pos ⟨i,v⟩) true =
    connectorDegree (shape i) v := by
  let A := directFamily shape (fun a x => pos ⟨a,x⟩)
  let B := oppositeFamily shape (fun a x => pos ⟨a,x⟩)
  let g : DirectEdges shape → Bool := fun _ => false
  let k : OppositeEdges shape → Bool := fun _ => false
  have left := degree_split A g (pos ⟨i,v⟩)
  have right := end_split B k (fun e => !(k e)) (pos ⟨i,v⟩)
  have atb (b : Bool) : coloredDegree A g (pos ⟨i,v⟩) b + endCount B k (fun e => !(k e)) (pos ⟨i,v⟩) b =
    portSum (shape i) (directColor shape g i) (oppositeColor shape k i) v.val b :=
    (ports_at shape pos g k i v b).trans (portSum_eq ..).symm
  change coloredDegree A _ _ _ + coloredDegree B _ _ _ = _
  have t := atb true
  have f := atb false
  have both := all_ports (shape i) (directColor shape g i) (oppositeColor shape k i) v.val
  omega

theorem partition_pieces [Fintype V] [DecidableEq I] [DecidableEq E]
    (conn : ∀ v w, Relation.ReflTransGen (Joined D) v w)
    (regular : ∀ i (v : Fin (shape i).vertices), coloredDegree D (fun _ => true) (pos ⟨i,v⟩) true +
      oldDegree (shape i) v.val = 4)
    (edgeEven : Even (Fintype.card E + ∑ i, residualCount (shape i)))
    (badEven : Even (∑ i, (if unmarkedBad (shape i) then 1 else 0 : ℕ)))
    (mark : Option (DirectEdges shape × Bool)) :
    ∃ (f : E → Bool) (p q : I → Bool),
      (∀ i (v : Fin (shape i).vertices), let w := pos ⟨i,v⟩
        coloredDegree D f w false + (shape i).portDegree (p i) (q i) v.val false =
        coloredDegree D f w true + (shape i).portDegree (p i) (q i) v.val true) ∧
      (∀ i b, mark = some (i,b) → p i.val = b) := by
  let A := directFamily shape (fun a x => pos ⟨a,x⟩)
  let B := oppositeFamily shape (fun a x => pos ⟨a,x⟩)
  have dv (w : V) : Even (coloredDegree D (fun _ => true) w true +
      coloredDegree A (fun _ => true) w true + coloredDegree B (fun _ => true) w true) := by
    obtain ⟨⟨i,v⟩,rfl⟩ := pos.surjective w
    have d := regular i v
    have par := degree_parity (shape i) v
    have eq := all_ports_at shape pos i v
    change coloredDegree A _ _ true + coloredDegree B _ _ true = _ at eq
    rw [Nat.even_iff]
    omega
  obtain ⟨f,g,k,bal,hm⟩ := partition_with_mark D A B conn dv (even_direct_edges shape _ edgeEven badEven) mark
  refine ⟨f,firstPort shape g k,secondPort shape k,?_,?_⟩
  · intro i v
    have e := bal (pos ⟨i,v⟩)
    have h (b) : coloredDegree A g (pos ⟨i,v⟩) b + endCount B k (fun e => !(k e)) (pos ⟨i,v⟩) b =
      (shape i).portDegree (firstPort shape g k i) (secondPort shape k i) v.val b := ports_at shape pos g k i v b
    dsimp only
    have h₁ := h true
    have h₂ := h false
    omega
  · rintro ⟨i,hi⟩ b m
    simpa [firstPort,directColor,hi] using hm ⟨i,hi⟩ b m

end Kostochka.FiveRegular.Auxiliary

end

section 

namespace Kostochka.FiveRegular.Restoration
open Finset Subdivision

variable {V E I X K : Type*}

/- The two equivalences identify the abstract corners and edges of the shapes with actual
vertices and edge labels. The remaining edge labels are outside edges or untouched
matching edges. -/
structure Atlas (D : Family V E) (I X K : Type*) where
  shape : I → Shape
  places : (Σ i, Fin (shape i).vertices) ≃ V
  labels : X ⊕ (K ⊕ (Σ i, Fin (shape i).edges)) ≃ E
  endpoints : ∀ i (e : Fin (shape i).edges),
    s(D.left (labels (.inr (.inr ⟨i,e⟩))),D.right (labels (.inr (.inr ⟨i,e⟩)))) =
      s(places ⟨i,(shape i).family.left e⟩,places ⟨i,(shape i).family.right e⟩)

namespace Atlas
variable {D : Family V E} (A : Atlas D I X K)

def outside : Family V X :=
  ⟨fun x => D.left (A.labels (.inl x)),fun x => D.right (A.labels (.inl x))⟩

def untouched : Family V K :=
  ⟨fun k => D.left (A.labels (.inr (.inl k))),fun k => D.right (A.labels (.inr (.inl k)))⟩

def localLabel (i : I) (e : Fin (A.shape i).edges) : E := A.labels (.inr (.inr ⟨i,e⟩))

def priorLocal (s : Shape) (e : ℕ) : Bool := decide (s = .alternatingSquare ∧ e % 2 = 1)

def oldMatching (e : E) : Bool :=
  match A.labels.symm e with
  | .inl _ => false
  | .inr (.inl _) => true
  | .inr (.inr ⟨i,k⟩) => priorLocal (A.shape i) k.val

def asPart : Role → EdgePart
  | .factor b => .factor b
  | .third => .exceptional
  | .matching => .matching

def part (f : X → Bool) (p q : I → Bool) (e : E) : EdgePart :=
  match A.labels.symm e with
  | .inl x => .factor (f x)
  | .inr (.inl _) => .matching
  | .inr (.inr ⟨i,k⟩) => asPart ((A.shape i).role (p i) (q i) k.val)

private def contribution {Z : Type*} [DecidableEq Z] (v x y : Z) (color : Bool) : ℕ :=
  (if v = x ∧ color = true then 1 else 0) + (if v = y ∧ color = true then 1 else 0)

private theorem contribution_same {Z : Type*} [DecidableEq Z] (v x y a b : Z) (f : Bool)
    (eq : s(x,y) = s(a,b)) : contribution v x y f = contribution v a b f := by
  rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rfl
  · exact Nat.add_comm _ _

variable [Fintype I] [Fintype X] [Fintype K] [Fintype E] [DecidableEq V]

private theorem sumDegree {Z H : Type*} [DecidableEq Z] [Fintype H] (F : Family Z H)
    (f : H → Bool) (v : Z) : coloredDegree F f v true =
      ∑ e, contribution v (F.left e) (F.right e) (f e) := by
  simp [coloredDegree,contribution,sum_add_distrib]

theorem splitDegree (f : E → Bool) (i : I) (v : Fin (A.shape i).vertices) :
    coloredDegree D f (A.places ⟨i,v⟩) true =
    coloredDegree A.outside (fun x => f (A.labels (.inl x))) (A.places ⟨i,v⟩) true +
    coloredDegree A.untouched (fun x => f (A.labels (.inr (.inl x)))) (A.places ⟨i,v⟩) true +
    coloredDegree (A.shape i).family (fun e => f (A.localLabel i e)) v true := by
  classical
  let w := A.places ⟨i,v⟩
  let sumAt j (e : Fin (A.shape j).edges) :=
    contribution w (A.places ⟨j,(A.shape j).family.left e⟩) (A.places ⟨j,(A.shape j).family.right e⟩)
      (f (A.localLabel j e))
  have eh (j) (e : Fin (A.shape j).edges) :
      contribution w (D.left (A.localLabel j e)) (D.right (A.localLabel j e)) (f (A.localLabel j e)) =
      sumAt j e := contribution_same _ _ _ _ _ _ (A.endpoints j e)
  have atI (e) : sumAt i e = contribution v ((A.shape i).family.left e) ((A.shape i).family.right e)
      (f (A.localLabel i e)) := by simp [sumAt,w,contribution]
  have localSum : (∑ j, ∑ e, sumAt j e) = ∑ e, sumAt i e := by
    apply sum_eq_single i
    · intro j _ ne
      simp [sumAt,w,contribution,ne.symm]
    · simp
  change coloredDegree D f w true = _
  simp only [sumDegree]
  rw [← A.labels.sum_comp (fun e => contribution w (D.left e) (D.right e) (f e))]
  simp only [Fintype.sum_sum_type,Fintype.sum_sigma]
  change _ + (_ + ∑ j, ∑ e, contribution w (D.left (A.localLabel j e)) (D.right (A.localLabel j e)) (f (A.localLabel j e))) = _
  simp_rw [eh]
  rw [localSum]
  simp only [atI,add_assoc]
  rfl

omit [Fintype I] [Fintype X] [Fintype K] [Fintype E] [DecidableEq V] in
@[simp] theorem part_local (f : X → Bool) (p q : I → Bool) (i : I) (k : Fin (A.shape i).edges) :
    A.part f p q (A.localLabel i k) = asPart ((A.shape i).role (p i) (q i) k.val) := by simp [part,localLabel]

omit [Fintype I] [Fintype X] [Fintype K] [Fintype E] [DecidableEq V] in
@[simp] theorem part_external (f : X → Bool) (p q : I → Bool) (x : X) :
    A.part f p q (A.labels (.inl x)) = .factor (f x) := by simp [part]

omit [Fintype I] [Fintype X] [Fintype K] [Fintype E] [DecidableEq V] in
@[simp] theorem part_untouched (f : X → Bool) (p q : I → Bool) (k : K) :
    A.part f p q (A.labels (.inr (.inl k))) = .matching := by simp [part]

@[simp] private theorem asPart_match (r : Role) : asPart r = .matching ↔ r = .matching := by cases r <;> simp [asPart]
@[simp] private theorem asPart_except (r : Role) : asPart r = .exceptional ↔ r = .third := by cases r <;> simp [asPart]
@[simp] private theorem asPart_factor (r : Role) (b) : asPart r = .factor b ↔ r = .factor b := by cases r <;> simp [asPart]

private theorem degree_false {Z H : Type*} [DecidableEq Z] [Fintype H] (F : Family Z H) (v : Z) :
    coloredDegree F (fun _ => false) v true = 0 := by simp [coloredDegree]

private theorem boolDegree {Z H : Type*} [DecidableEq Z] [Fintype H] (F : Family Z H) (h : H → Bool) (v : Z) (b : Bool) :
    coloredDegree F (fun e => decide (h e = b)) v true = coloredDegree F h v b := by simp [coloredDegree]

theorem factorDegree (f : X → Bool) (p q : I → Bool) (i : I) (v : Fin (A.shape i).vertices) (b : Bool) :
    coloredDegree D (fun e => decide (A.part f p q e = .factor b)) (A.places ⟨i,v⟩) true =
      coloredDegree A.outside f (A.places ⟨i,v⟩) b + (A.shape i).factorDegree (p i) (q i) v.val b := by
  rw [A.splitDegree]
  simp [boolDegree,degree_false,Shape.factorDegree]
  exact (A.shape i).coloredDegree_family (fun j => decide ((A.shape i).role (p i) (q i) j = .factor b)) v

theorem exceptionalDegree (f : X → Bool) (p q : I → Bool) (i : I) (v : Fin (A.shape i).vertices) :
    coloredDegree D (fun e => decide (A.part f p q e = .exceptional)) (A.places ⟨i,v⟩) true =
      (A.shape i).thirdDegree (p i) (q i) v.val := by
  rw [A.splitDegree]
  simp [degree_false,Shape.thirdDegree]
  exact (A.shape i).coloredDegree_family (fun j => decide ((A.shape i).role (p i) (q i) j = .third)) v

private theorem prior_degree (s : Shape) (v : Fin s.vertices) : s.inc (priorLocal s) v.val =
    if s = .alternatingSquare then 1 else 0 := by
  cases s <;> try simp [Shape.inc,priorLocal,Shape.cyclic]
  change Fin 4 at v
  fin_cases v <;> decide

theorem matchingDegree (f : X → Bool) (p q : I → Bool) (w : V) :
    coloredDegree D (fun e => decide (A.part f p q e = .matching)) w true =
      coloredDegree D A.oldMatching w true := by
  obtain ⟨⟨i,v⟩,rfl⟩ := A.places.surjective w
  rw [A.splitDegree,A.splitDegree]
  simp only [part,asPart_match,oldMatching,localLabel,
    Equiv.symm_apply_apply,reduceCtorEq,decide_false,eq_self,decide_true,degree_false,zero_add]
  congr 1
  rw [(A.shape i).coloredDegree_family (fun j => decide ((A.shape i).role (p i) (q i) j = .matching)),
    (A.shape i).coloredDegree_family (priorLocal (A.shape i))]
  exact ((A.shape i).restoreMatching (p i) (q i) v).trans (prior_degree _ v).symm

section Unique
variable {Z H : Type*} [Fintype H] [DecidableEq Z]

theorem unique_iff_degree (F : Family Z H) (loop : Loopless F) (sel : H → Bool) (w : Z) :
    (∃! e, sel e = true ∧ FamilyIncident F w e) ↔ coloredDegree F sel w true = 1 := by
  classical
  let S := univ.filter (fun e => sel e = true ∧ FamilyIncident F w e)
  have mem (e) : e ∈ S ↔ sel e = true ∧ FamilyIncident F w e := by simp [S]
  have card : S.card = coloredDegree F sel w true := by
    calc
      _ = ∑ e, if sel e = true ∧ FamilyIncident F w e then (1 : ℕ) else 0 := by simp [S]
      _ = ∑ e, contribution w (F.left e) (F.right e) (sel e) := by
        apply sum_congr rfl
        intro e _
        have h := loop e
        by_cases hl : w = F.left e <;> by_cases hr : w = F.right e <;> cases c : sel e <;>
          simp_all [FamilyIncident,contribution]
      _ = _ := (sumDegree F sel w).symm
  rw [←card,card_eq_one]
  constructor
  · rintro ⟨e,he,unique⟩
    refine ⟨e,?_⟩
    ext j
    simp only [mem_singleton,mem]
    exact ⟨unique j,fun eq => eq ▸ he⟩
  · rintro ⟨e,he⟩
    refine ⟨e,(mem e).mp (by simp [he]),fun j hj => ?_⟩
    exact mem_singleton.mp (he ▸ (mem j).mpr hj)

end Unique

theorem perfectMatching (f : X → Bool) (p q : I → Bool) (loop : Loopless D)
    (old : ∀ w, ∃! e, A.oldMatching e = true ∧ FamilyIncident D w e) :
    ∀ w, ∃! e, A.part f p q e = .matching ∧ FamilyIncident D w e := by
  intro w
  have eq := A.matchingDegree f p q w
  have hu := (unique_iff_degree D loop _ w).mp (old w)
  have h := (unique_iff_degree D loop _ w).mpr (eq.trans hu)
  simpa only [decide_eq_true_eq] using h

theorem matching_disjoint (f : X → Bool) (p q : I → Bool) (loop : Loopless D)
    (old : ∀ w, ∃! e, A.oldMatching e = true ∧ FamilyIncident D w e)
    (e g : E) (he : A.part f p q e = .matching) (hg : A.part f p q g = .matching)
    (meet : FamilyMeet D e g) : e = g := by
  obtain ⟨w,hw,hv⟩ := meet
  exact (A.perfectMatching f p q loop old w).unique ⟨he,hw⟩ ⟨hg,hv⟩

section Classification
omit [Fintype I] [Fintype X] [Fintype K] [Fintype E] [DecidableEq V]

theorem exceptional_iff (f : X → Bool) (p q : I → Bool) (e : E) :
    A.part f p q e = .exceptional ↔ ∃ i, ∃ k : Fin (A.shape i).edges, A.localLabel i k = e ∧
      (A.shape i = .badPath ∨ (∃ n, A.shape i = .badOdd n) ∨ A.shape i = .divertedSquare) := by
  constructor
  · obtain ⟨x,rfl⟩ := A.labels.surjective e
    rcases x with x | k | ⟨i,k⟩
    · simp
    · simp
    · intro h
      exact ⟨i,k,rfl,((A.shape i).third_iff (p i) (q i) k).mp (by simpa [part] using h)⟩
  · rintro ⟨i,k,rfl,h⟩
    simpa using ((A.shape i).third_iff (p i) (q i) k).mpr h

theorem localLabel_injective : Function.Injective (fun z : Σ i, Fin (A.shape i).edges => A.localLabel z.1 z.2) :=
  fun _ _ h => Sum.inr.inj (Sum.inr.inj (A.labels.injective h))

theorem localIncident (i) (e : Fin (A.shape i).edges) (w : V) :
    FamilyIncident D w (A.localLabel i e) ↔ w = A.places ⟨i,(A.shape i).family.left e⟩ ∨
      w = A.places ⟨i,(A.shape i).family.right e⟩ := by
  change w = D.left _ ∨ w = D.right _ ↔ _
  have h := A.endpoints i e
  rcases Sym2.eq_iff.mp h with ⟨l,r⟩ | ⟨l,r⟩ <;> change D.left (A.localLabel i e) = _ at l <;>
    change D.right (A.localLabel i e) = _ at r <;> simp [l,r,or_comm]

theorem samePieceOfIncident {i j} {v : Fin (A.shape i).vertices} {e : Fin (A.shape j).edges}
    (hit : FamilyIncident D (A.places ⟨i,v⟩) (A.localLabel j e)) : i = j := by
  rcases (A.localIncident j e _).mp hit with h | h <;> exact congrArg Sigma.fst (A.places.injective h)

theorem sameLocalIncident (i) (v : Fin (A.shape i).vertices) (e : Fin (A.shape i).edges) :
    FamilyIncident D (A.places ⟨i,v⟩) (A.localLabel i e) ↔ FamilyIncident (A.shape i).family v e := by
  rw [A.localIncident]
  simp [FamilyIncident]

theorem incident_exceptional_iff (f : X → Bool) (p q : I → Bool) (i) (v : Fin (A.shape i).vertices) (e : E) :
    A.part f p q e = .exceptional ∧ FamilyIncident D (A.places ⟨i,v⟩) e ↔
      (A.shape i = .badPath ∨ (∃ n, A.shape i = .badOdd n) ∨ A.shape i = .divertedSquare) ∧
      ∃ k, A.localLabel i k = e ∧ FamilyIncident (A.shape i).family v k := by
  constructor
  · rintro ⟨he,hit⟩
    obtain ⟨j,k,rfl,hj⟩ := (A.exceptional_iff f p q e).mp he
    obtain rfl := A.samePieceOfIncident hit
    exact ⟨hj,k,rfl,(A.sameLocalIncident i v k).mp hit⟩
  · rintro ⟨hs,k,rfl,hk⟩
    exact ⟨(A.exceptional_iff f p q _).mpr ⟨i,k,rfl,hs⟩,(A.sameLocalIncident i v k).mpr hk⟩

end Classification

private theorem originalCount (s : Shape) (v : Fin s.vertices) (p q : Bool) :
    Auxiliary.oldDegree s v.val + s.matchingDegree p q v.val = s.inc (fun _ => true) v.val := by
  rw [s.restoreMatching]
  by_cases sq : s = .alternatingSquare
  · subst s
    change Fin 4 at v
    fin_cases v <;> decide
  · simp [Auxiliary.oldDegree,sq]

omit [Fintype I] [Fintype K] [Fintype E] in
private theorem fourEdgesAt (f : X → Bool) (p q : I → Bool) (i) (v : Fin (A.shape i).vertices)
    (base : coloredDegree A.outside (fun _ => true) (A.places ⟨i,v⟩) true +
      Auxiliary.oldDegree (A.shape i) v.val = 4) :
    coloredDegree A.outside f (A.places ⟨i,v⟩) false + coloredDegree A.outside f (A.places ⟨i,v⟩) true +
    (A.shape i).inc (fun _ => true) v.val = 4 + (A.shape i).matchingDegree (p i) (q i) v.val := by
  have h := Auxiliary.degree_split A.outside f (A.places ⟨i,v⟩)
  have a := originalCount (A.shape i) v (p i) (q i)
  omega

theorem actualDegrees (f : X → Bool) (p q : I → Bool) (i) (v : Fin (A.shape i).vertices)
    (base : coloredDegree A.outside (fun _ => true) (A.places ⟨i,v⟩) true +
      Auxiliary.oldDegree (A.shape i) v.val = 4)
    (aux : coloredDegree A.outside f (A.places ⟨i,v⟩) false + (A.shape i).portDegree (p i) (q i) v false =
      coloredDegree A.outside f (A.places ⟨i,v⟩) true + (A.shape i).portDegree (p i) (q i) v true) :
    let d b := coloredDegree D (fun e => decide (A.part f p q e = .factor b)) (A.places ⟨i,v⟩) true
    d false ≤ 2 ∧ d true ≤ 2 ∧ ((A.shape i).thirdDegree (p i) (q i) v.val = 2 → d false = 1 ∧ d true = 1) := by
  have h := (A.shape i).restoredDegrees (p i) (q i) v
    (fun b => coloredDegree A.outside f (A.places ⟨i,v⟩) b) aux (A.fourEdgesAt f p q i v base)
  simpa only [A.factorDegree] using And.intro h.1 (And.intro h.2.1 h.2.2.1)

theorem uniqueSpoke (f : X → Bool) (p q : I → Bool) (i) (v : Fin (A.shape i).vertices) (b : Bool)
    (loop : Loopless D)
    (base : coloredDegree A.outside (fun _ => true) (A.places ⟨i,v⟩) true +
      Auxiliary.oldDegree (A.shape i) v.val = 4)
    (aux : coloredDegree A.outside f (A.places ⟨i,v⟩) false + (A.shape i).portDegree (p i) (q i) v false =
      coloredDegree A.outside f (A.places ⟨i,v⟩) true + (A.shape i).portDegree (p i) (q i) v true)
    (two : (A.shape i).thirdDegree (p i) (q i) v.val = 2) :
    ∃! e, A.part f p q e = .factor b ∧ FamilyIncident D (A.places ⟨i,v⟩) e := by
  have h := (A.actualDegrees f p q i v base aux).2.2 two
  have eq : coloredDegree D (fun e => decide (A.part f p q e = .factor b)) (A.places ⟨i,v⟩) true = 1 :=
    by cases b; exact h.1; exact h.2
  simpa using (unique_iff_degree D loop _ _).mpr eq

end Atlas
end Kostochka.FiveRegular.Restoration

end

section 

namespace MultFive.Multi
open Kostochka.FiveRegular Subdivision Restoration

variable {V I X K : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype X] [Fintype K]

theorem colorable_of_restored_layers (m : Multi V) (A : Atlas m.family I X K) (side : V → Bool)
    (exterior : X → Bool) (first second : I → Bool)
    (old : ∀ v, ∃! e, A.oldMatching e = true ∧ FamilyIncident m.family v e)
    (layers : Nonempty (GluedLayers m.family side (A.part exterior first second))) : m.Colorable := by
  obtain ⟨L⟩ := layers
  obtain ⟨vertex,edge,hv,he,hi⟩ := L.colors.total (fun e f em fm meet =>
    A.matching_disjoint exterior first second m.family_loopless old e f
      ((L.matching e).mp em) ((L.matching f).mp fm) meet)
  exact m.colorable_of_family vertex edge hv he hi

end MultFive.Multi

end

section 

namespace Kostochka.FiveRegular

open SimpleGraph Finset

variable {V : Type*} [Fintype V]

def crossGraph (G : SimpleGraph V) (p : V → Bool) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ p x ≠ p y
  symm.symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless.irrefl _ h := h.2 rfl

omit [Fintype V] in

theorem crossing_reachable_of_maximal (G : SimpleGraph V) (p : V → Bool)
    (maximal : ∀ q, crossGraph G p ≤ crossGraph G q → crossGraph G q ≤ crossGraph G p) {u v : V} (huv : G.Adj u v) :
    (crossGraph G p).Reachable u v := by
  classical
  by_contra hdis
  let q := fun x => if (crossGraph G p).Reachable u x then !(p x) else p x
  have keep {x y : V} (h : (crossGraph G p).Adj x y) : (crossGraph G q).Adj x y := by
    have hab : (crossGraph G p).Reachable u x ↔ (crossGraph G p).Reachable u y :=
      ⟨fun hx => hx.trans h.reachable, fun hy => hy.trans h.symm.reachable⟩
    refine ⟨h.1, ?_⟩
    have hxy := h.2
    by_cases hx : (crossGraph G p).Reachable u x
    · simpa [q, hx, hab.mp hx] using hxy
    · have hy := mt hab.mpr hx
      simpa [q, hx, hy] using hxy
  have hsame : p u = p v := by
    by_contra hne
    exact hdis (show (crossGraph G p).Adj u v from ⟨huv, hne⟩).reachable
  have gained : (crossGraph G q).Adj u v := by
    refine ⟨huv, ?_⟩
    simp [q, hdis, hsame]
  exact hdis ((maximal q (fun _ _ h => keep h)) gained).reachable

noncomputable def insideDegree (G : SimpleGraph V) (p : V → Bool) (u : V) : ℕ := by
  classical
  exact (univ.filter (fun v => G.Adj u v ∧ p u = p v)).card

end Kostochka.FiveRegular

end

section 

namespace MultFive.Multi
open SimpleGraph Finset
open Kostochka.FiveRegular (crossGraph crossing_reachable_of_maximal)
variable {V : Type*} [Fintype V]

noncomputable def residual (m : Multi V) (M : m.support.Subgraph) : Multi V := by
  classical
  exact {
    count := fun x y => m.count x y - if M.Adj x y then 1 else 0
    symm := fun x y => by rw [m.symm x y]; congr 2; exact propext ⟨fun h => h.symm,fun h => h.symm⟩
    loopless := fun x => by simp [m.loopless] }

noncomputable def insideDegree (m : Multi V) (p : V → Bool) (u : V) : ℕ :=
  ∑ v, if p v = p u then m.count u v else 0

private def cutPair (m : Multi V) (p : V → Bool) (x y : V) : ℤ :=
  if p x = p y then 0 else m.count x y

private def gainPair (m : Multi V) (p : V → Bool) (u v : V) : ℤ :=
  if p u = p v then m.count u v else -(m.count u v : ℤ)

private def score (m : Multi V) (p : V → Bool) : ℤ := ∑ x, ∑ y, cutPair m p x y
private def gain (m : Multi V) (p : V → Bool) (u : V) : ℤ := ∑ v, gainPair m p u v

private noncomputable def flip (p : V → Bool) (u : V) : V → Bool := by
  classical exact fun v => if v = u then !(p v) else p v

omit [Fintype V] in
private theorem delta [DecidableEq V] (m : Multi V) (p : V → Bool) (u x y : V) :
    cutPair m (flip p u) x y - cutPair m p x y =
    (if x = u then gainPair m p u y else 0) + (if y = u then gainPair m p u x else 0) := by
  classical
  by_cases hx : x = u <;> by_cases hy : y = u
  · subst x; subst y; simp [cutPair, gainPair, m.loopless]
  · subst x; cases a : p u <;> cases b : p y <;> simp [cutPair, gainPair, flip, hy, a, b]
  · subst y; cases a : p u <;> cases b : p x <;> simp [cutPair, gainPair, flip, hx, a, b, m.symm x u]
  · simp [cutPair, flip, hx, hy]

private theorem flip_score (m : Multi V) (p : V → Bool) (u : V) :
    score m (flip p u) - score m p = 2 * gain m p u := by
  classical
  unfold gain score
  simp only [← sum_sub_distrib, delta, sum_add_distrib]
  simp [sum_ite_irrel, two_mul]

private theorem gain_eq (m : Multi V) (p : V → Bool) (u : V) :
    gain m p u = 2 * (m.insideDegree p u : ℤ) - m.degree u := by
  have t (v) : gainPair m p u v = 2 * ((if p v = p u then m.count u v else 0 : ℕ) : ℤ) - m.count u v := by
    by_cases e : p u = p v <;> (simp [gainPair, e, Ne.symm] <;> omega)
  simp only [gain, t, insideDegree, degree, Nat.cast_sum, sum_sub_distrib, ← mul_sum]

private theorem flip_other (m : Multi V) (p : V → Bool) {u v : V} (opp : p u ≠ p v) :
    gain m (flip p u) v = gain m p v + 2 * m.count u v := by
  classical
  have vu : v ≠ u := fun e => opp (congrArg p e.symm)
  have aux (x : V) : gainPair m (flip p u) v x = gainPair m p v x +
      (if x = u then 2 * (m.count u v : ℤ) else 0) := by
    by_cases hxu : x = u
    · subst x
      cases hu : p u <;> cases hv : p v <;> simp_all [gainPair, flip, m.symm v u] <;> omega
    · simp [gainPair, flip, vu, hxu]
  simp [gain, aux, Finset.sum_add_distrib]

private theorem crossing_reachable (m : Multi V) (p : V → Bool)
    (maximal : ∀ q, score m q ≤ score m p) (u v : V) (adj : m.support.Adj u v) :
    (crossGraph m.support p).Reachable u v := by
  apply crossing_reachable_of_maximal m.support p _ adj
  intro q keeps x y gained
  by_contra no
  have mono (i j : V) : cutPair m p i j ≤ cutPair m q i j := by
    by_cases h : 0 < m.count i j
    · by_cases hp : p i = p j
      · simp [cutPair,hp]; split <;> positivity
      · have hq := (keeps (show (crossGraph m.support p).Adj i j from ⟨h,hp⟩)).2
        simp [cutPair,hp,hq]
    · have zero : m.count i j = 0 := Nat.eq_zero_of_not_pos h
      simp [cutPair,zero]
  have pos : 0 < m.count x y := gained.1
  have same : p x = p y := by_contra fun n => no ⟨pos,n⟩
  have strict : cutPair m p x y < cutPair m q x y := by simp [cutPair,same,gained.2,pos]
  exact (maximal q).not_gt (sum_lt_sum (fun i _ => sum_le_sum (fun j _ => mono i j))
    ⟨x,mem_univ _,sum_lt_sum (fun j _ => mono x j) ⟨y,mem_univ _,strict⟩⟩)

private theorem lex_cut (m h : Multi V) :
    ∃ p : V → Bool, (∀ q, score h q ≤ score h p) ∧
      ∀ q, score h q = score h p → score m q ≤ score m p := by
  classical
  obtain ⟨p, _, hp⟩ := univ.exists_max_image (score h) univ_nonempty
  let tied := univ.filter (fun q => score h q = score h p)
  obtain ⟨r, hr, top⟩ := tied.exists_max_image (score m) (show tied.Nonempty from ⟨p, by simp [tied]⟩)
  have eqn := (mem_filter.mp hr).2
  exact ⟨r, fun q => eqn ▸ hp q (mem_univ _), fun q e => top q (by simp [tied,e,eqn])⟩

private theorem remove_matching (m : Multi V) (M : m.support.Subgraph) (hm : M.IsPerfectMatching)
    (p : V → Bool) (v : V) :
    m.degree v = (m.residual M).degree v + 1 ∧ gain m p v ≤ gain (m.residual M) p v + 1 := by
  classical
  obtain ⟨w, hw, unique⟩ := hm.1 (hm.2 v)
  have h (u : V) : M.Adj v u ↔ u = w := ⟨unique u,fun e => e ▸ hw⟩
  have deq (u : V) : m.count v u = (m.residual M).count v u + (if u = w then 1 else 0) := by
    by_cases e : u = w
    · subst u
      have pos : 0 < m.count v w := M.adj_sub hw
      simp [residual,hw]; omega
    · simp [residual,h u,e]
  have geq (u : V) : gainPair m p v u ≤ gainPair (m.residual M) p v u +
      ((if u = w then 1 else 0 : ℕ) : ℤ) := by
    have hh := deq u
    unfold gainPair
    split <;> split_ifs at hh ⊢ <;> omega
  constructor
  · unfold degree
    simpa only [sum_add_distrib, sum_ite_eq',mem_univ,if_true] using sum_congr (s₁ := univ) rfl (fun u _ => deq u)
  · simpa [gain,sum_add_distrib] using sum_le_sum (s := univ) (fun u _ => geq u)

/- Choose a cut by maximizing the number of crossing residual edges, breaking ties with the
original multigraph. A vertex flip bounds the inside degree by two. A two-vertex flip
gives the last exclusion. -/
theorem exists_matching_cut (m : Multi V) (reg : ∀ v, m.degree v = 5)
    (M : m.support.Subgraph) (hm : M.IsPerfectMatching) :
    let h := m.residual M
    ∃ p : V → Bool, (∀ v, m.insideDegree p v ≤ 2) ∧
      (∀ u v, 0 < h.count u v → (crossGraph h.support p).Reachable u v) ∧
      (∀ u v, p u ≠ p v → h.insideDegree p u = 2 → h.insideDegree p v = 2 → h.count u v = 0) := by
  let h := m.residual M
  obtain ⟨p,maximal,tie⟩ := lex_cut m h
  have deg (u) : h.degree u = 4 := by
    have e := (remove_matching m M hm p u).1
    change m.degree u = h.degree u + 1 at e
    rw [reg] at e; omega
  refine ⟨p,?_,crossing_reachable h p maximal,?_⟩
  · intro u
    have ge := gain_eq m p u
    have hi := (remove_matching m M hm p u).2
    change gain m p u ≤ gain h p u + 1 at hi
    have mh := maximal (flip p u)
    have fs := flip_score h p u
    have fm := flip_score m p u
    rw [reg] at ge
    by_contra! large
    have equality : score h (flip p u) = score h p := by omega
    have := tie (flip p u) equality
    omega
  · intro u v opp hu hv
    change h.count u v = 0
    have gu : gain h p u = 0 := by rw [gain_eq,deg,hu]; decide
    have gv : gain h p v = 0 := by rw [gain_eq,deg,hv]; decide
    have first := flip_score h p u
    have second := flip_score h (flip p u) v
    have oth := flip_other h p opp
    have largest := maximal (flip (flip p u) v)
    omega

end MultFive.Multi

end

section 

namespace MultFive.Multi
open Finset SimpleGraph
section BasicHelpers

variable {V : Type*}

def monoMulti (m : Multi V) (side : V → Bool) : Multi V where
  count x y := if side x = side y then m.count x y else 0
  symm x y := by
    by_cases h : side x = side y
    · simp [h, m.symm x y]
    · have h' : side y ≠ side x := Ne.symm h
      simp [h, h']
  loopless x := by simp [m.loopless]

@[simp]
theorem monoMulti_count (m : Multi V) (side : V → Bool) (x y : V) :
    (m.monoMulti side).count x y = if side x = side y then m.count x y else 0 := rfl

theorem monoMulti_degree [Fintype V] (m : Multi V) (side : V → Bool) (u : V) :
    (m.monoMulti side).degree u = m.insideDegree side u := by
  unfold Multi.degree Multi.insideDegree
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : side u = side v
  · simp [monoMulti, h]
  · have h' : side v ≠ side u := Ne.symm h
    simp [monoMulti, h, h']

theorem residual_count_le (m : Multi V) (M : m.support.Subgraph) (x y : V) :
    (m.residual M).count x y ≤ m.count x y := by
  classical
  simp only [residual]
  exact Nat.sub_le _ _

theorem residual_count_eq_sub (m : Multi V) (M : m.support.Subgraph) (x y : V)
    [Decidable (M.Adj x y)] :
    (m.residual M).count x y = m.count x y - if M.Adj x y then 1 else 0 := by
  classical
  unfold residual
  dsimp only
  congr 1
  by_cases h : M.Adj x y <;> simp [h]

theorem residual_count_of_adj (m : Multi V) (M : m.support.Subgraph) {x y : V} (h : M.Adj x y) :
    (m.residual M).count x y = m.count x y - 1 := by
  classical
  simpa [h] using residual_count_eq_sub m M x y

theorem residual_count_of_not_adj (m : Multi V) (M : m.support.Subgraph) {x y : V}
    (h : ¬ M.Adj x y) :
    (m.residual M).count x y = m.count x y := by
  classical
  simpa [h] using residual_count_eq_sub m M x y

theorem residual_count_add_matching (m : Multi V) (M : m.support.Subgraph) (x y : V)
    [Decidable (M.Adj x y)] :
    m.count x y = (m.residual M).count x y + if M.Adj x y then 1 else 0 := by
  rw [residual_count_eq_sub]
  by_cases h : M.Adj x y
  · have hpos : 0 < m.count x y := M.adj_sub h
    simp [h]
    omega
  · simp [h]

theorem degree_residual [Fintype V] (m : Multi V) (M : m.support.Subgraph)
    (hm : M.IsPerfectMatching) (u : V) :
    m.degree u = (m.residual M).degree u + 1 := by
  classical
  obtain ⟨w, hw, huniq⟩ := hm.1 (hm.2 u)
  have hiff : ∀ v, M.Adj u v ↔ v = w := fun v => ⟨huniq v, fun e => e ▸ hw⟩
  have deq : ∀ v, m.count u v = (m.residual M).count u v + if v = w then 1 else 0 := fun v => by
    have := residual_count_add_matching m M u v
    simpa [hiff v] using this
  unfold Multi.degree
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] using
    Finset.sum_congr (s₁ := Finset.univ) rfl (fun v _ => deq v)

theorem degree_residual_eq_four [Fintype V] (m : Multi V) (reg : ∀ v, m.degree v = 5)
    (M : m.support.Subgraph) (hm : M.IsPerfectMatching) (u : V) :
    (m.residual M).degree u = 4 := by
  have h := degree_residual m M hm u
  rw [reg u] at h
  omega

theorem insideDegree_residual_le [Fintype V] (m : Multi V) (M : m.support.Subgraph)
    (side : V → Bool) (u : V) :
    (m.residual M).insideDegree side u ≤ m.insideDegree side u := by
  unfold insideDegree
  refine Finset.sum_le_sum fun v _ => ?_
  split_ifs
  · exact residual_count_le m M u v
  · exact le_rfl

theorem matching_crossing_of_residual_insideDeg_two [Fintype V] (m : Multi V)
    (M : m.support.Subgraph) (side : V → Bool)
    (h_in : ∀ v, m.insideDegree side v ≤ 2) {u w : V}
    (hu : (m.residual M).insideDegree side u = 2) (hw : M.Adj u w) :
    side w ≠ side u := by
  classical
  intro hsame
  have hle : (m.residual M).insideDegree side u + 1 ≤ m.insideDegree side u := by
    unfold insideDegree
    have h1 := Finset.add_sum_erase Finset.univ
      (fun v => if side v = side u then m.count u v else 0) (Finset.mem_univ w)
    have h2 := Finset.add_sum_erase Finset.univ
      (fun v => if side v = side u then (m.residual M).count u v else 0) (Finset.mem_univ w)
    rw [← h1, ← h2]
    have hrest : ∑ v ∈ Finset.univ.erase w,
        (if side v = side u then (m.residual M).count u v else 0) ≤
        ∑ v ∈ Finset.univ.erase w, (if side v = side u then m.count u v else 0) := by
      refine Finset.sum_le_sum fun v _ => ?_
      split_ifs
      · exact residual_count_le m M u v
      · exact le_rfl
    have hmw : m.count u w = (m.residual M).count u w + 1 := by
      simpa [hw] using residual_count_add_matching m M u w
    simp only [hsame, ↓reduceIte, hmw]
    omega
  have := h_in u
  omega

end BasicHelpers

section CanonicalEdges

variable {V : Type*}

def isMatchingPair {m : Multi V} (M : m.support.Subgraph) : Sym2 V → Prop :=
  Sym2.lift ⟨M.Adj, fun _ _ => propext ⟨fun h => h.symm, fun h => h.symm⟩⟩

def isMatchingEdge (m : Multi V) (M : m.support.Subgraph) (e : m.Edge) : Prop :=
  isMatchingPair M e.1 ∧ e.2.1 = 0

theorem copies_pos_of_isMatchingPair {m : Multi V} {M : m.support.Subgraph} {p : Sym2 V}
    (h : isMatchingPair M p) : 0 < m.copies p := by
  induction p using Sym2.ind with
  | _ u v => exact M.adj_sub h

theorem copies_residual_of_mem (m : Multi V) (M : m.support.Subgraph) {p : Sym2 V}
    (h : isMatchingPair M p) :
    (m.residual M).copies p = m.copies p - 1 := by
  induction p using Sym2.ind with
  | _ u v => exact residual_count_of_adj m M h

theorem copies_residual_of_not_mem (m : Multi V) (M : m.support.Subgraph) {p : Sym2 V}
    (h : ¬ isMatchingPair M p) :
    (m.residual M).copies p = m.copies p := by
  induction p using Sym2.ind with
  | _ u v => exact residual_count_of_not_adj m M h

noncomputable def residualEdgeEquiv (m : Multi V) (M : m.support.Subgraph) :
    (m.residual M).Edge ≃ {e : m.Edge // ¬ isMatchingEdge m M e} := by
  classical
  let jump (p : Sym2 V) : ℕ := if isMatchingPair M p then 1 else 0
  have sz (p : Sym2 V) : (m.residual M).copies p + jump p = m.copies p := by
    by_cases hp : isMatchingPair M p
    · have ne := copies_pos_of_isMatchingPair hp
      simp [copies_residual_of_mem m M hp,jump,hp]; omega
    · simp [copies_residual_of_not_mem m M hp,jump,hp]
  have low (e : {e : m.Edge // ¬isMatchingEdge m M e}) : jump e.val.1 ≤ e.val.2.val := by
    by_cases hp : isMatchingPair M e.val.1
    · have hn : e.val.2.val ≠ 0 := fun eq => e.property ⟨hp,eq⟩
      simp [jump,hp]; omega
    · simp [jump,hp]
  refine {
    toFun := fun e => ⟨⟨e.1,⟨e.2.val + jump e.1,by have := sz e.1; have := e.2.isLt; omega⟩⟩,?_⟩
    invFun := fun e => ⟨e.val.1,⟨e.val.2.val-jump e.val.1,by have := sz e.val.1; have := e.val.2.isLt; have := low e; omega⟩⟩
    left_inv := ?_
    right_inv := ?_ }
  · rintro ⟨hp,hz⟩
    have one : jump e.1 = 1 := if_pos hp
    change e.2.val + jump e.1 = 0 at hz
    omega
  · rintro ⟨p,k⟩
    apply congrArg (Sigma.mk p)
    apply Fin.ext
    exact Nat.add_sub_cancel _ _
  · rintro a
    apply Subtype.ext
    apply congrArg (Sigma.mk a.val.1)
    apply Fin.ext
    exact Nat.sub_add_cancel (low a)

@[simp]
theorem residualEdgeEquiv_fst (m : Multi V) (M : m.support.Subgraph)
    (e : (m.residual M).Edge) : (residualEdgeEquiv m M e).1.1 = e.1 := rfl

noncomputable def resEdgeOfPos (m : Multi V) (M : m.support.Subgraph)
    {u w : V} (k : ℕ) (hk : k < (m.residual M).count u w) : m.Edge :=
  (residualEdgeEquiv m M ⟨s(u, w), ⟨k, hk⟩⟩).1

@[simp]
theorem resEdgeOfPos_fst (m : Multi V) (M : m.support.Subgraph)
    {u w : V} (k : ℕ) (hk : k < (m.residual M).count u w) :
    (resEdgeOfPos m M k hk).1 = s(u, w) :=
  residualEdgeEquiv_fst m M _

theorem resEdgeOfPos_not_matching (m : Multi V) (M : m.support.Subgraph)
    {u w : V} (k : ℕ) (hk : k < (m.residual M).count u w) :
    ¬ isMatchingEdge m M (resEdgeOfPos m M k hk) :=
  (residualEdgeEquiv m M ⟨s(u, w), ⟨k, hk⟩⟩).2

theorem resEdgeOfPos_inj (m : Multi V) (M : m.support.Subgraph)
    {u₁ w₁ u₂ w₂ : V} {k₁ k₂ : ℕ}
    {hk₁ : k₁ < (m.residual M).count u₁ w₁} {hk₂ : k₂ < (m.residual M).count u₂ w₂}
    (heq : resEdgeOfPos m M k₁ hk₁ = resEdgeOfPos m M k₂ hk₂) :
    s(u₁, w₁) = s(u₂, w₂) ∧ k₁ = k₂ := by
  have hsub : residualEdgeEquiv m M ⟨s(u₁, w₁), ⟨k₁, hk₁⟩⟩ =
      residualEdgeEquiv m M ⟨s(u₂, w₂), ⟨k₂, hk₂⟩⟩ := Subtype.ext heq
  have hsig := (residualEdgeEquiv m M).injective hsub
  have hp : s(u₁, w₁) = s(u₂, w₂) := congrArg Sigma.fst hsig
  refine ⟨hp, ?_⟩
  have hval : (⟨s(u₁, w₁), ⟨k₁, hk₁⟩⟩ : (m.residual M).Edge).2.1 =
      (⟨s(u₂, w₂), ⟨k₂, hk₂⟩⟩ : (m.residual M).Edge).2.1 := by
    rw [hsig]
  exact hval

theorem matching_edge_unique (m : Multi V) (M : m.support.Subgraph) (hm : M.IsPerfectMatching)
    (v : V) : ∃! e : m.Edge, isMatchingEdge m M e ∧ v ∈ e.1 := by
  obtain ⟨w, hw, huniq⟩ := hm.1 (hm.2 v)
  have hpos : 0 < m.copies s(v, w) := M.adj_sub hw
  refine ⟨⟨s(v, w), ⟨0, hpos⟩⟩, ⟨⟨hw, rfl⟩, Sym2.mem_mk_left v w⟩, ?_⟩
  rintro ⟨p, ⟨i, hi⟩⟩ ⟨⟨hp, h0⟩, hv⟩
  obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.mp hv
  have hu : u = w := huniq u hp
  subst hu
  simp only [Sigma.mk.inj_iff, heq_eq_eq, Fin.mk.injEq, true_and]
  exact h0

end CanonicalEdges
end MultFive.Multi

namespace MultFive.Multi
open Finset SimpleGraph
section DegTwoMulti

variable {W : Type*}

def listPathAdj (L : List W) (u v : W) : Prop :=
  ∃ (i : ℕ) (hi : i + 1 < L.length),
    s(u, v) = s(L[i]'(by omega), L[i + 1]'hi)

def listCycleAdj (L : List W) (u v : W) : Prop :=
  ∃ (i : Fin L.length),
    s(u, v) = s(L[i.1]'i.2, L[(i.1 + 1) % L.length]'(Nat.mod_lt _ (Fin.pos i)))

instance instDecidableListPathAdj [DecidableEq W] (L : List W) (u v : W) :
    Decidable (listPathAdj L u v) :=
  decidable_of_iff
    (∃ i : Fin (L.length - 1), s(u, v) = s(L[i.1]'(by omega), L[i.1 + 1]'(by omega)))
    ⟨fun ⟨i, hi⟩ => ⟨i.1, by omega, hi⟩, fun ⟨i, hi, heq⟩ => ⟨⟨i, by omega⟩, heq⟩⟩

instance instDecidableListCycleAdj [DecidableEq W] (L : List W) (u v : W) :
    Decidable (listCycleAdj L u v) :=
  Fintype.decidableExistsFintype

theorem listPathAdj_symm {L : List W} {u v : W} (h : listPathAdj L u v) :
    listPathAdj L v u := by
  rcases h with ⟨i, hi, heq⟩
  exact ⟨i, hi, by rwa [Sym2.eq_swap]⟩

theorem listCycleAdj_symm {L : List W} {u v : W} (h : listCycleAdj L u v) :
    listCycleAdj L v u := by
  rcases h with ⟨i, heq⟩
  exact ⟨i, by rwa [Sym2.eq_swap]⟩

theorem listPathAdj_mem {L : List W} {u v : W} (h : listPathAdj L u v) : u ∈ L ∧ v ∈ L := by
  rcases h with ⟨i, hi, heq⟩
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨List.getElem_mem _, List.getElem_mem _⟩

theorem listCycleAdj_mem {L : List W} {u v : W} (h : listCycleAdj L u v) : u ∈ L ∧ v ∈ L := by
  rcases h with ⟨i, heq⟩
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨List.getElem_mem _, List.getElem_mem _⟩

theorem listPathAdj_singleton (x u v : W) : ¬ listPathAdj [x] u v := by
  rintro ⟨i, hi, _⟩; simp at hi

theorem listPathAdj_cons_cons (x y : W) (rest : List W) (u v : W) :
    listPathAdj (x :: y :: rest) u v ↔ s(u, v) = s(x, y) ∨ listPathAdj (y :: rest) u v := by
  constructor
  · rintro ⟨i, hi, heq⟩
    cases i with
    | zero => left; simpa using heq
    | succ j => right; exact ⟨j, by simpa using hi, by simpa using heq⟩
  · rintro (heq | ⟨j, hj, heq⟩)
    · exact ⟨0, by simp, by simpa using heq⟩
    · exact ⟨j + 1, by simpa using hj, by simpa using heq⟩

theorem getElem_inj {L : List W} (h : L.Nodup) {i j : ℕ}
    {hi : i < L.length} {hj : j < L.length} (heq : L[i]'hi = L[j]'hj) : i = j :=
  congrArg Fin.val (List.nodup_iff_injective_getElem.mp h (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) heq)

theorem listPath_pair_inj {L : List W} (h : L.Nodup) {i j : ℕ}
    {hi : i + 1 < L.length} {hj : j + 1 < L.length}
    (heq : s(L[i]'(by omega), L[i + 1]'hi) = s(L[j]'(by omega), L[j + 1]'hj)) : i = j := by
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact getElem_inj h h1
  · have e1 := getElem_inj h h1
    have e2 := getElem_inj h h2
    omega

theorem listCycle_pair_inj {L : List W} (h : L.Nodup) (hlen : 3 ≤ L.length)
    {i j : Fin L.length}
    (heq : s(L[i.1]'i.2, L[(i.1 + 1) % L.length]'(Nat.mod_lt _ (Fin.pos i))) =
           s(L[j.1]'j.2, L[(j.1 + 1) % L.length]'(Nat.mod_lt _ (Fin.pos j)))) : i = j := by
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact Fin.ext (getElem_inj h h1)
  · have e1 := getElem_inj h h1
    have e2 := getElem_inj h h2
    have hi := i.2
    have hj := j.2
    by_cases h1' : j.1 + 1 < L.length <;> by_cases h2' : i.1 + 1 < L.length
    · rw [Nat.mod_eq_of_lt h1'] at e1; rw [Nat.mod_eq_of_lt h2'] at e2; omega
    · rw [Nat.mod_eq_of_lt h1'] at e1
      have : i.1 + 1 = L.length := by omega
      rw [this, Nat.mod_self] at e2; omega
    · have : j.1 + 1 = L.length := by omega
      rw [this, Nat.mod_self] at e1; rw [Nat.mod_eq_of_lt h2'] at e2; omega
    · have : j.1 + 1 = L.length := by omega
      have : i.1 + 1 = L.length := by omega
      omega

theorem degree_eq_of_listPathAdj_count [Fintype W] [DecidableEq W] {K : Multi W}
    {L : List W} (hnodup : L.Nodup)
    (hcount : ∀ u ∈ L, ∀ w : W, K.count u w = if listPathAdj L u w then 1 else 0)
    (k : ℕ) (hk : k < L.length) :
    K.degree (L[k]'hk) =
      (if 0 < k then 1 else 0) + (if k + 1 < L.length then 1 else 0) := by
  classical
  unfold Multi.degree
  have hmem := List.getElem_mem hk
  simp_rw [hcount (L[k]'hk) hmem, Finset.sum_boole, Nat.cast_id]
  have hiff : ∀ w : W, listPathAdj L (L[k]'hk) w ↔
      (∃ hk0 : 0 < k, w = L[k - 1]'(by omega)) ∨
      (∃ hk1 : k + 1 < L.length, w = L[k + 1]'hk1) := by
    intro w
    constructor
    · rintro ⟨i, hi, heq⟩
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
      · have hik : k = i := getElem_inj hnodup h1
        subst hik; exact Or.inr ⟨hi, rfl⟩
      · have hik : k = i + 1 := getElem_inj hnodup h1
        left; refine ⟨by omega, ?_⟩; congr 1; omega
    · rintro (⟨hk0, rfl⟩ | ⟨hk1, rfl⟩)
      · refine ⟨k - 1, by omega, ?_⟩
        have hsub : k - 1 + 1 = k := by omega
        simp only [hsub]; exact Sym2.eq_swap
      · exact ⟨k, hk1, rfl⟩
  by_cases hk0 : 0 < k <;> by_cases hk1 : k + 1 < L.length
  · have hne : L[k - 1]'(by omega) ≠ L[k + 1]'hk1 := fun heq => by
      have := getElem_inj hnodup heq; omega
    have hset : Finset.univ.filter (fun w => listPathAdj L (L[k]'hk) w) =
        {L[k - 1]'(by omega), L[k + 1]'hk1} := by
      ext w; simp [hiff, hk0, hk1]
    rw [hset, Finset.card_pair hne]; simp [hk0, hk1]
  · have hset : Finset.univ.filter (fun w => listPathAdj L (L[k]'hk) w) =
        {L[k - 1]'(by omega)} := by
      ext w; simp [hiff, hk0, hk1]
    rw [hset, Finset.card_singleton]; simp [hk0, hk1]
  · have hset : Finset.univ.filter (fun w => listPathAdj L (L[k]'hk) w) =
        {L[k + 1]'hk1} := by
      ext w; simp [hiff, hk0, hk1]
    rw [hset, Finset.card_singleton]; simp [hk0, hk1]
  · have hset : Finset.univ.filter (fun w => listPathAdj L (L[k]'hk) w) = ∅ := by
      ext w; simp [hiff, hk0, hk1]
    rw [hset, Finset.card_empty]; simp [hk0, hk1]

private theorem cycle_neighbors {k : ℕ} (hk : 3 ≤ k) (vert : Fin k → W)
    (hinj : Function.Injective vert) (i : Fin k) :
    let next (j : Fin k) : Fin k := ⟨(j.val+1)%k,Nat.mod_lt _ (by omega)⟩
    ∃ a, a ≠ next i ∧ next a = i ∧ ∀ w,
      (∃ j, s(vert i,w) = s(vert j,vert (next j))) ↔ w = vert a ∨ w = vert (next i) := by
  let : NeZero k := ⟨by omega⟩
  let next (j : Fin k) : Fin k := ⟨(j.val+1)%k,Nat.mod_lt _ (by omega)⟩
  have add (j : Fin k) : next j = j+1 := by
    apply Fin.ext
    simp [next,Fin.val_add,Nat.mod_eq_of_lt (by omega : 1 < k)]
  have ne : i-1 ≠ next i := by
    rw [add]
    intro h
    have z : (0 : Fin k) = 1+1 := by
      apply add_left_cancel (a := i)
      calc i+0 = i-1+1 := by simp
           _ = i+(1+1) := by rw [h,add_assoc]
    have bad := congrArg Fin.val z
    simp [Fin.val_add,Nat.mod_eq_of_lt (by omega : 1 < k),
      Nat.mod_eq_of_lt (by omega : 2 < k)] at bad
  have back : next (i-1) = i := by rw [add,sub_add_cancel]
  refine ⟨i-1,ne,back,?_⟩
  intro w
  change (∃ j, s(vert i,w) = s(vert j,vert (next j))) ↔ w = vert (i-1) ∨ w = vert (next i)
  constructor
  · rintro ⟨j,eq⟩
    rcases Sym2.eq_iff.mp eq with ⟨hj,hw⟩|⟨hj,hw⟩
    · exact Or.inr (hw.trans (congrArg (fun x => vert (next x)) (hinj hj).symm))
    · refine Or.inl (hw.trans (congrArg vert ?_))
      rw [hinj hj,add,add_sub_cancel_right]
  · rintro (rfl|rfl)
    · exact ⟨i-1,by rw [back]; exact Sym2.eq_swap⟩
    · exact ⟨i,rfl⟩

theorem degree_eq_two_of_listCycleAdj_count [Fintype W] [DecidableEq W] {K : Multi W}
    {L : List W} (hnodup : L.Nodup) (hlen : 3 ≤ L.length)
    (hcount : ∀ u ∈ L, ∀ w : W, K.count u w = if listCycleAdj L u w then 1 else 0)
    (k : ℕ) (hk : k < L.length) : K.degree (L[k]'hk) = 2 := by
  classical
  let vert (i : Fin L.length) := L[i.val]
  have inj : Function.Injective vert := fun _ _ h => Fin.ext (getElem_inj hnodup h)
  let i : Fin L.length := ⟨k,hk⟩
  let j : Fin L.length := ⟨(k+1)%L.length,Nat.mod_lt _ (by omega)⟩
  obtain ⟨a,diff,_,rim⟩ := cycle_neighbors hlen vert inj i
  have eq : (Finset.univ.filter (fun w => listCycleAdj L L[k] w)) = {vert a,vert j} := by
    ext w
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
    simpa [listCycleAdj,vert,i,j] using rim w
  unfold Multi.degree
  simp_rw [hcount _ (List.getElem_mem hk), Finset.sum_boole, Nat.cast_id]
  rw [eq,Finset.card_pair (inj.ne diff)]

end DegTwoMulti
end MultFive.Multi

namespace MultFive.Multi
open Finset SimpleGraph
section MonoDecomposition

variable {V : Type*}

theorem cycle_count_eq_of_inside_le_two [Fintype V] [DecidableEq V]
    (m : Multi V) (side : V → Bool) (h_in : ∀ v, m.insideDegree side v ≤ 2)
    {k : ℕ} (hk : 3 ≤ k) {vert : Fin k → V} (hinj : Function.Injective vert)
    (hcyc : ∀ i : Fin k, 0 < (m.monoMulti side).count (vert i)
      (vert ⟨(i.1 + 1) % k, Nat.mod_lt _ (by omega)⟩))
    (i : Fin k) (w : V) :
    (m.monoMulti side).count (vert i) w =
      if ∃ j : Fin k, s(vert i, w) =
          s(vert j, vert ⟨(j.1 + 1) % k, Nat.mod_lt _ (by omega)⟩)
      then 1 else 0 := by
  classical
  let g := m.monoMulti side
  let next (j : Fin k) : Fin k := ⟨(j.val+1)%k,Nat.mod_lt _ (by omega)⟩
  obtain ⟨a,ne,back,rim⟩ := cycle_neighbors hk vert hinj i
  change next a = i at back
  have diff : vert a ≠ vert (next i) := hinj.ne ne
  have p : 0 < g.count (vert i) (vert a) := by
    rw [g.symm]
    have h : 0 < g.count (vert a) (vert (next a)) := hcyc a
    rwa [back] at h
  have q := hcyc i
  have ub := h_in (vert i)
  rw [← monoMulti_degree] at ub
  change g.degree (vert i) ≤ 2 at ub
  have bound (T : Finset V) : ∑ v ∈ T, g.count (vert i) v ≤ g.degree (vert i) :=
    sum_le_sum_of_subset (subset_univ _)
  have two := bound {vert a,vert (next i)}
  rw [sum_pair diff] at two
  change 0 < g.count (vert i) (vert (next i)) at q
  rw [if_congr (rim w) rfl rfl]
  change g.count (vert i) w = if w = vert a ∨ w = vert (next i) then 1 else 0
  split
  · rename_i h
    rcases h with rfl|rfl <;> omega
  · rename_i h
    push Not at h
    have three := bound {w,vert a,vert (next i)}
    rw [sum_insert (by simp [h.1,h.2]),sum_pair diff] at three
    omega

end MonoDecomposition
end MultFive.Multi

namespace MultFive.Multi
open Finset SimpleGraph
section PathSplitting

variable {V : Type*}

end PathSplitting
end MultFive.Multi

namespace MultFive.Multi
open Finset SimpleGraph
section PieceTemplates

variable {V : Type*}

structure TwoBadQuad (m : Multi V) (M : m.support.Subgraph) (side : V → Bool) where
  b : Bool
  v1 : V
  v2 : V
  v3 : V
  v4 : V
  nodup : [v1, v2, v3, v4].Nodup
  side_v1 : side v1 = b
  side_v2 : side v2 = b
  side_v3 : side v3 = b
  side_v4 : side v4 = b
  match14 : M.Adj v1 v4
  match23 : M.Adj v2 v3
  m_count14 : m.count v1 v4 = 1
  m_count23 : m.count v2 v3 = 1
  not_match12 : ¬ M.Adj v1 v2
  not_match34 : ¬ M.Adj v3 v4
  res_count12 : (m.residual M).count v1 v2 = 1
  res_count34 : (m.residual M).count v3 v4 = 1
  same_comp : (m.residual M).support.Reachable v1 v3

namespace TwoBadQuad

variable {m : Multi V} {M : m.support.Subgraph} {side : V → Bool}

def vertsList (q : TwoBadQuad m M side) : List V := [q.v1, q.v2, q.v3, q.v4]

def verts [DecidableEq V] (q : TwoBadQuad m M side) : Finset V := {q.v1, q.v2, q.v3, q.v4}

def edgeMult [DecidableEq V] (q : TwoBadQuad m M side) (u w : V) : ℕ :=
  (if s(u, w) = s(q.v1, q.v2) then 1 else 0) + (if s(u, w) = s(q.v3, q.v4) then 1 else 0)

theorem all_reachable [DecidableEq V] (q : TwoBadQuad m M side) {u w : V}
    (hu : u ∈ q.verts) (hw : w ∈ q.verts) :
    (m.residual M).support.Reachable u w := by
  have h12 : (m.residual M).support.Reachable q.v1 q.v2 :=
    (show (m.residual M).support.Adj q.v1 q.v2 from by change 0 < _; rw [q.res_count12]; omega).reachable
  have h34 : (m.residual M).support.Reachable q.v3 q.v4 :=
    (show (m.residual M).support.Adj q.v3 q.v4 from by change 0 < _; rw [q.res_count34]; omega).reachable
  have h1 : ∀ x ∈ q.verts, (m.residual M).support.Reachable q.v1 x := by
    intro x hx
    simp only [verts, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Reachable.refl _
    · exact h12
    · exact q.same_comp
    · exact q.same_comp.trans h34
  exact (h1 u hu).symm.trans (h1 w hw)

end TwoBadQuad

structure MultiBadPath (m : Multi V) (M : m.support.Subgraph) (side : V → Bool) where
  b : Bool
  v1 : V
  v2 : V
  v3 : V
  v4 : V
  nodup : [v1, v2, v3, v4].Nodup
  side_v1 : side v1 = b
  side_v2 : side v2 = b
  side_v3 : side v3 = b
  side_v4 : side v4 = b
  match14 : M.Adj v1 v4
  m_count14 : m.count v1 v4 = 1
  not_match12 : ¬ M.Adj v1 v2
  not_match23 : ¬ M.Adj v2 v3
  not_match34 : ¬ M.Adj v3 v4
  res_count12 : (m.residual M).count v1 v2 = 1
  res_count23 : (m.residual M).count v2 v3 = 1
  res_count34 : (m.residual M).count v3 v4 = 1

namespace MultiBadPath

variable {m : Multi V} {M : m.support.Subgraph} {side : V → Bool}

def vertsList (p : MultiBadPath m M side) : List V := [p.v1, p.v2, p.v3, p.v4]

def verts [DecidableEq V] (p : MultiBadPath m M side) : Finset V := {p.v1, p.v2, p.v3, p.v4}

def edgeMult [DecidableEq V] (p : MultiBadPath m M side) (u w : V) : ℕ :=
  if s(u, w) = s(p.v1, p.v2) ∨ s(u, w) = s(p.v2, p.v3) ∨ s(u, w) = s(p.v3, p.v4) then 1 else 0

end MultiBadPath

structure OrdinaryPath (m : Multi V) (M : m.support.Subgraph) (side : V → Bool) where
  b : Bool
  vertsList : List V
  nodup : vertsList.Nodup
  hlen : 2 ≤ vertsList.length
  side_mem : ∀ v ∈ vertsList, side v = b
  res_count_edge : ∀ (i : ℕ) (hi : i + 1 < vertsList.length),
    (m.residual M).count (vertsList[i]'(by omega)) (vertsList[i + 1]'hi) = 1
  not_bad_path : ∀ h4 : vertsList.length = 4,
    ¬ M.Adj (vertsList[0]'(by omega)) (vertsList[3]'(by omega))
  not_same_comp_two_bad : ∀ (h2 : vertsList.length = 2) (v3 v4 : V),
    [vertsList[0]'(by omega), vertsList[1]'(by omega), v3, v4].Nodup →
    side v3 = b → side v4 = b →
    M.Adj (vertsList[0]'(by omega)) v4 → M.Adj (vertsList[1]'(by omega)) v3 →
    0 < (m.residual M).count v3 v4 →
    ¬ (m.residual M).support.Reachable (vertsList[0]'(by omega)) v3

namespace OrdinaryPath

variable {m : Multi V} {M : m.support.Subgraph} {side : V → Bool}

def first (p : OrdinaryPath m M side) : V := p.vertsList[0]'(by have := p.hlen; omega)

def last (p : OrdinaryPath m M side) : V :=
  p.vertsList[p.vertsList.length - 1]'(by have := p.hlen; omega)

def verts [DecidableEq V] (p : OrdinaryPath m M side) : Finset V := p.vertsList.toFinset

def edgeMult [DecidableEq V] (p : OrdinaryPath m M side) (u w : V) : ℕ :=
  if listPathAdj p.vertsList u w then 1 else 0

end OrdinaryPath

structure MultiBadOddCycle (m : Multi V) (M : m.support.Subgraph) (side : V → Bool) where
  b : Bool
  t : ℕ
  ht : 1 ≤ t
  vertsList : List V
  nodup : vertsList.Nodup
  hlen : vertsList.length = 2 * t + 1
  side_mem : ∀ v ∈ vertsList, side v = b
  not_match_edge : ∀ i : Fin vertsList.length,
    ¬ M.Adj (vertsList[i.1]'i.2)
      (vertsList[(i.1 + 1) % vertsList.length]'(Nat.mod_lt _ (Fin.pos i)))
  res_count_edge : ∀ i : Fin vertsList.length,
    (m.residual M).count (vertsList[i.1]'i.2)
      (vertsList[(i.1 + 1) % vertsList.length]'(Nat.mod_lt _ (Fin.pos i))) = 1

namespace MultiBadOddCycle

variable {m : Multi V} {M : m.support.Subgraph} {side : V → Bool}

def verts [DecidableEq V] (c : MultiBadOddCycle m M side) : Finset V := c.vertsList.toFinset

def edgeMult [DecidableEq V] (c : MultiBadOddCycle m M side) (u w : V) : ℕ :=
  if listCycleAdj c.vertsList u w then 1 else 0

end MultiBadOddCycle

structure ZeroBadSquare (m : Multi V) (M : m.support.Subgraph) (side : V → Bool) where
  b : Bool
  v1 : V
  v2 : V
  v3 : V
  v4 : V
  nodup : [v1, v2, v3, v4].Nodup
  side_v1 : side v1 = b
  side_v2 : side v2 = b
  side_v3 : side v3 = b
  side_v4 : side v4 = b
  not_match12 : ¬ M.Adj v1 v2
  not_match23 : ¬ M.Adj v2 v3
  not_match34 : ¬ M.Adj v3 v4
  not_match41 : ¬ M.Adj v4 v1
  res_count12 : (m.residual M).count v1 v2 = 1
  res_count23 : (m.residual M).count v2 v3 = 1
  res_count34 : (m.residual M).count v3 v4 = 1
  res_count41 : (m.residual M).count v4 v1 = 1

namespace ZeroBadSquare

variable {m : Multi V} {M : m.support.Subgraph} {side : V → Bool}

def vertsList (q : ZeroBadSquare m M side) : List V := [q.v1, q.v2, q.v3, q.v4]

def verts [DecidableEq V] (q : ZeroBadSquare m M side) : Finset V := {q.v1, q.v2, q.v3, q.v4}

def edgeMult [DecidableEq V] (q : ZeroBadSquare m M side) (u w : V) : ℕ :=
  if s(u, w) = s(q.v1, q.v2) ∨ s(u, w) = s(q.v2, q.v3) ∨
     s(u, w) = s(q.v3, q.v4) ∨ s(u, w) = s(q.v4, q.v1) then 1 else 0

end ZeroBadSquare

structure LongEvenCycle (m : Multi V) (M : m.support.Subgraph) (side : V → Bool) where
  b : Bool
  t : ℕ
  ht : 3 ≤ t
  vertsList : List V
  nodup : vertsList.Nodup
  hlen : vertsList.length = 2 * t
  side_mem : ∀ v ∈ vertsList, side v = b
  not_match_edge : ∀ i : Fin vertsList.length,
    ¬ M.Adj (vertsList[i.1]'i.2)
      (vertsList[(i.1 + 1) % vertsList.length]'(Nat.mod_lt _ (Fin.pos i)))
  res_count_edge : ∀ i : Fin vertsList.length,
    (m.residual M).count (vertsList[i.1]'i.2)
      (vertsList[(i.1 + 1) % vertsList.length]'(Nat.mod_lt _ (Fin.pos i))) = 1

namespace LongEvenCycle

variable {m : Multi V} {M : m.support.Subgraph} {side : V → Bool}

def verts [DecidableEq V] (c : LongEvenCycle m M side) : Finset V := c.vertsList.toFinset

def edgeMult [DecidableEq V] (c : LongEvenCycle m M side) (u w : V) : ℕ :=
  if listCycleAdj c.vertsList u w then 1 else 0

end LongEvenCycle

structure DoubledEdge (m : Multi V) (M : m.support.Subgraph) (side : V → Bool) where
  b : Bool
  u : V
  v : V
  hne : u ≠ v
  side_u : side u = b
  side_v : side v = b
  not_match : ¬ M.Adj u v
  res_count : (m.residual M).count u v = 2

namespace DoubledEdge

variable {m : Multi V} {M : m.support.Subgraph} {side : V → Bool}

def vertsList (d : DoubledEdge m M side) : List V := [d.u, d.v]

def verts [DecidableEq V] (d : DoubledEdge m M side) : Finset V := {d.u, d.v}

def edgeMult [DecidableEq V] (d : DoubledEdge m M side) (x y : V) : ℕ :=
  if s(x, y) = s(d.u, d.v) then 2 else 0

end DoubledEdge

inductive ResidualPiece [Fintype V] (m : Multi V) (M : m.support.Subgraph) (side : V → Bool) where
  | isolated (v : V) (hdeg : (m.residual M).insideDegree side v = 0)
  | twoBadQuad (q : TwoBadQuad m M side)
  | badPath (p : MultiBadPath m M side) (marked : Bool)
  | ordinaryPath (p : OrdinaryPath m M side)
  | badOddCycle (c : MultiBadOddCycle m M side) (marked : Bool)
  | zeroBadSquare (q : ZeroBadSquare m M side)
  | evenCycle (c : LongEvenCycle m M side)
  | doubledEdge (d : DoubledEdge m M side)

namespace ResidualPiece

variable [Fintype V] {m : Multi V} {M : m.support.Subgraph} {side : V → Bool}

def sideOf : ResidualPiece m M side → Bool
  | .isolated v _ => side v
  | .twoBadQuad q => q.b
  | .badPath p _ => p.b
  | .ordinaryPath p => p.b
  | .badOddCycle c _ => c.b
  | .zeroBadSquare q => q.b
  | .evenCycle c => c.b
  | .doubledEdge d => d.b

def vertsList : ResidualPiece m M side → List V
  | .isolated v _ => [v]
  | .twoBadQuad q => q.vertsList
  | .badPath p _ => p.vertsList
  | .ordinaryPath p => p.vertsList
  | .badOddCycle c _ => c.vertsList
  | .zeroBadSquare q => q.vertsList
  | .evenCycle c => c.vertsList
  | .doubledEdge d => d.vertsList

def verts [DecidableEq V] (P : ResidualPiece m M side) : Finset V :=
  P.vertsList.toFinset

def rep : ResidualPiece m M side → V
  | .isolated v _ => v
  | .twoBadQuad q => q.v1
  | .badPath p _ => p.v1
  | .ordinaryPath p => p.first
  | .badOddCycle c _ => c.vertsList[0]'(by have := c.ht; have := c.hlen; omega)
  | .zeroBadSquare q => q.v1
  | .evenCycle c => c.vertsList[0]'(by have := c.ht; have := c.hlen; omega)
  | .doubledEdge d => d.u

def isBad : ResidualPiece m M side → Bool
  | .badPath _ _ => true
  | .badOddCycle _ _ => true
  | _ => false

def isMarked : ResidualPiece m M side → Bool
  | .badPath _ flag => flag
  | .badOddCycle _ flag => flag
  | _ => false

def isUnmarkedBad (P : ResidualPiece m M side) : Bool :=
  P.isBad && !P.isMarked

def setMarked (flag : Bool) : ResidualPiece m M side → ResidualPiece m M side
  | .badPath p _ => .badPath p flag
  | .badOddCycle c _ => .badOddCycle c flag
  | P => P

def edgeMult [DecidableEq V] : ResidualPiece m M side → V → V → ℕ
  | .isolated _ _, _, _ => 0
  | .twoBadQuad q, u, w => q.edgeMult u w
  | .badPath p _, u, w => p.edgeMult u w
  | .ordinaryPath p, u, w => p.edgeMult u w
  | .badOddCycle c _, u, w => c.edgeMult u w
  | .zeroBadSquare q, u, w => q.edgeMult u w
  | .evenCycle c, u, w => c.edgeMult u w
  | .doubledEdge d, u, w => d.edgeMult u w

def edgeCount : ResidualPiece m M side → ℕ
  | .isolated _ _ => 0
  | .twoBadQuad _ => 2
  | .badPath _ _ => 3
  | .ordinaryPath p => p.vertsList.length - 1
  | .badOddCycle c _ => c.vertsList.length
  | .zeroBadSquare _ => 4
  | .evenCycle c => c.vertsList.length
  | .doubledEdge _ => 2

def expectedInsideDeg [DecidableEq V] : ResidualPiece m M side → V → ℕ
  | .isolated _ _, _ => 0
  | .twoBadQuad _, _ => 1
  | .badPath p _, v => if v = p.v1 ∨ v = p.v4 then 1 else 2
  | .ordinaryPath p, v => if v = p.first ∨ v = p.last then 1 else 2
  | .badOddCycle _ _, _ => 2
  | .zeroBadSquare _, _ => 2
  | .evenCycle _, _ => 2
  | .doubledEdge _, _ => 2

noncomputable def canonicalResEdges : ResidualPiece m M side → List m.Edge
  | .isolated _ _ => []
  | .twoBadQuad q =>
    [resEdgeOfPos m M 0 (by rw [q.res_count12]; omega),
     resEdgeOfPos m M 0 (by rw [q.res_count34]; omega)]
  | .badPath p _ =>
    [resEdgeOfPos m M 0 (by rw [p.res_count12]; omega),
     resEdgeOfPos m M 0 (by rw [p.res_count23]; omega),
     resEdgeOfPos m M 0 (by rw [p.res_count34]; omega)]
  | .ordinaryPath p =>
    (List.finRange (p.vertsList.length - 1)).map fun i =>
      resEdgeOfPos m M (u := p.vertsList[i.1]'(by omega))
        (w := p.vertsList[i.1 + 1]'(by omega)) 0 (by
        rw [p.res_count_edge i.1 (by omega)]; omega)
  | .badOddCycle c _ =>
    (List.finRange c.vertsList.length).map fun i =>
      resEdgeOfPos m M (u := c.vertsList[i.1]'i.2)
        (w := c.vertsList[(i.1 + 1) % c.vertsList.length]'(Nat.mod_lt _ (Fin.pos i))) 0 (by
        rw [c.res_count_edge i]; omega)
  | .zeroBadSquare q =>
    [resEdgeOfPos m M 0 (by rw [q.res_count12]; omega),
     resEdgeOfPos m M 0 (by rw [q.res_count23]; omega),
     resEdgeOfPos m M 0 (by rw [q.res_count34]; omega),
     resEdgeOfPos m M 0 (by rw [q.res_count41]; omega)]
  | .evenCycle c =>
    (List.finRange c.vertsList.length).map fun i =>
      resEdgeOfPos m M (u := c.vertsList[i.1]'i.2)
        (w := c.vertsList[(i.1 + 1) % c.vertsList.length]'(Nat.mod_lt _ (Fin.pos i))) 0 (by
        rw [c.res_count_edge i]; omega)
  | .doubledEdge d =>
    [resEdgeOfPos m M 0 (by rw [d.res_count]; omega),
     resEdgeOfPos m M 1 (by rw [d.res_count]; omega)]

theorem vertsList_nodup (P : ResidualPiece m M side) : P.vertsList.Nodup := by
  cases P with
  | isolated v _ => simp [vertsList]
  | twoBadQuad q => exact q.nodup
  | badPath p _ => exact p.nodup
  | ordinaryPath p => exact p.nodup
  | badOddCycle c _ => exact c.nodup
  | zeroBadSquare q => exact q.nodup
  | evenCycle c => exact c.nodup
  | doubledEdge d => simp [vertsList, DoubledEdge.vertsList, d.hne]

theorem rep_mem_verts [DecidableEq V] (P : ResidualPiece m M side) : P.rep ∈ P.verts := by
  rw [verts, List.mem_toFinset]
  cases P with
  | isolated v _ => simp [rep, vertsList]
  | twoBadQuad q => simp [rep, vertsList, TwoBadQuad.vertsList]
  | badPath p _ => simp [rep, vertsList, MultiBadPath.vertsList]
  | ordinaryPath p => exact List.getElem_mem _
  | badOddCycle c _ => exact List.getElem_mem _
  | zeroBadSquare q => simp [rep, vertsList, ZeroBadSquare.vertsList]
  | evenCycle c => exact List.getElem_mem _
  | doubledEdge d => simp [rep, vertsList, DoubledEdge.vertsList]

theorem side_of_mem [DecidableEq V] (P : ResidualPiece m M side) {v : V} (hv : v ∈ P.verts) :
    side v = P.sideOf := by
  rw [verts, List.mem_toFinset] at hv
  cases P with
  | isolated x _ =>
    simp only [vertsList, List.mem_singleton] at hv
    subst hv; rfl
  | twoBadQuad q =>
    simp only [vertsList, TwoBadQuad.vertsList, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact q.side_v1
    · exact q.side_v2
    · exact q.side_v3
    · exact q.side_v4
  | badPath p _ =>
    simp only [vertsList, MultiBadPath.vertsList, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact p.side_v1
    · exact p.side_v2
    · exact p.side_v3
    · exact p.side_v4
  | ordinaryPath p => exact p.side_mem v hv
  | badOddCycle c _ => exact c.side_mem v hv
  | zeroBadSquare q =>
    simp only [vertsList, ZeroBadSquare.vertsList, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact q.side_v1
    · exact q.side_v2
    · exact q.side_v3
    · exact q.side_v4
  | evenCycle c => exact c.side_mem v hv
  | doubledEdge d =>
    simp only [vertsList, DoubledEdge.vertsList, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact d.side_u
    · exact d.side_v

theorem edgeMult_pos_mem [DecidableEq V] (P : ResidualPiece m M side) {u w : V}
    (h : 0 < P.edgeMult u w) : u ∈ P.verts ∧ w ∈ P.verts := by
  rw [verts, List.mem_toFinset, List.mem_toFinset]
  cases P with
  | isolated _ _ => simp [edgeMult] at h
  | twoBadQuad q =>
    simp only [edgeMult, TwoBadQuad.edgeMult] at h
    have hor : s(u, w) = s(q.v1, q.v2) ∨ s(u, w) = s(q.v3, q.v4) := by
      by_contra hn; push Not at hn; simp [hn.1, hn.2] at h
    rcases hor with hs | hs <;> rw [Sym2.eq_iff] at hs <;>
      rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [vertsList, TwoBadQuad.vertsList]
  | badPath p _ =>
    simp only [edgeMult, MultiBadPath.edgeMult] at h
    by_cases hor : s(u, w) = s(p.v1, p.v2) ∨ s(u, w) = s(p.v2, p.v3) ∨ s(u, w) = s(p.v3, p.v4)
    · rcases hor with hs | hs | hs <;> rw [Sym2.eq_iff] at hs <;>
        rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [vertsList, MultiBadPath.vertsList]
    · rw [if_neg hor] at h; omega
  | ordinaryPath p =>
    simp only [edgeMult, OrdinaryPath.edgeMult] at h
    by_cases hpa : listPathAdj p.vertsList u w
    · exact listPathAdj_mem hpa
    · rw [if_neg hpa] at h; omega
  | badOddCycle c _ =>
    simp only [edgeMult, MultiBadOddCycle.edgeMult] at h
    by_cases hca : listCycleAdj c.vertsList u w
    · exact listCycleAdj_mem hca
    · rw [if_neg hca] at h; omega
  | zeroBadSquare q =>
    simp only [edgeMult, ZeroBadSquare.edgeMult] at h
    by_cases hor : s(u, w) = s(q.v1, q.v2) ∨ s(u, w) = s(q.v2, q.v3) ∨
        s(u, w) = s(q.v3, q.v4) ∨ s(u, w) = s(q.v4, q.v1)
    · rcases hor with hs | hs | hs | hs <;> rw [Sym2.eq_iff] at hs <;>
        rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [vertsList, ZeroBadSquare.vertsList]
    · rw [if_neg hor] at h; omega
  | evenCycle c =>
    simp only [edgeMult, LongEvenCycle.edgeMult] at h
    by_cases hca : listCycleAdj c.vertsList u w
    · exact listCycleAdj_mem hca
    · rw [if_neg hca] at h; omega
  | doubledEdge d =>
    simp only [edgeMult, DoubledEdge.edgeMult] at h
    by_cases hs : s(u, w) = s(d.u, d.v)
    · rw [Sym2.eq_iff] at hs
      rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [vertsList, DoubledEdge.vertsList]
    · rw [if_neg hs] at h; omega

theorem edgeMult_eq_zero_of_not_mem [DecidableEq V] (P : ResidualPiece m M side) {u w : V}
    (hu : u ∉ P.verts) : P.edgeMult u w = 0 := by
  by_contra hne
  exact hu (P.edgeMult_pos_mem (Nat.pos_of_ne_zero hne)).1

theorem canonicalResEdges_length (P : ResidualPiece m M side) :
    P.canonicalResEdges.length = P.edgeCount := by
  cases P <;> simp [canonicalResEdges, edgeCount]

theorem canonicalResEdges_nodup (P : ResidualPiece m M side) :
    P.canonicalResEdges.Nodup := by
  cases P with
  | isolated _ _ => simp [canonicalResEdges]
  | twoBadQuad q | zeroBadSquare q | badPath q flag =>
    have nd := q.nodup
    simp only [canonicalResEdges,List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,
      not_or,List.nodup_nil,not_false_eq_true,and_true] at nd ⊢
    repeat' apply And.intro
    all_goals intro eq; have eq' := Sym2.eq_iff.mp (resEdgeOfPos_inj m M eq).1; grind only
  | ordinaryPath p =>
    exact (List.nodup_finRange _).map fun i j eq =>
      Fin.ext (listPath_pair_inj p.nodup (resEdgeOfPos_inj m M eq).1)
  | badOddCycle c flag | evenCycle c =>
    exact (List.nodup_finRange _).map fun i j eq =>
      listCycle_pair_inj c.nodup (by have := c.ht; have := c.hlen; omega)
        (resEdgeOfPos_inj m M eq).1
  | doubledEdge d =>
    simp only [canonicalResEdges,List.nodup_cons,List.mem_singleton,List.not_mem_nil,
      List.nodup_nil,not_false_eq_true,and_true]
    exact fun eq => (by decide : (0 : ℕ) ≠ 1) (resEdgeOfPos_inj m M eq).2

theorem canonicalResEdges_mem_props [DecidableEq V] (P : ResidualPiece m M side) {e : m.Edge}
    (he : e ∈ P.canonicalResEdges) :
    ¬ isMatchingEdge m M e ∧
    (∀ v ∈ e.1, v ∈ P.verts) ∧
    (∀ u w, e.1 = s(u, w) → 0 < P.edgeMult u w) := by
  have hmem_of_pair : ∀ {u w : V} {k : ℕ} {hk : k < (m.residual M).count u w},
      e = resEdgeOfPos m M k hk → 0 < P.edgeMult u w →
      ¬ isMatchingEdge m M e ∧ (∀ v ∈ e.1, v ∈ P.verts) ∧
        (∀ x y, e.1 = s(x, y) → 0 < P.edgeMult x y) := by
    intro u w k hk rfl hpos
    refine ⟨resEdgeOfPos_not_matching m M k hk, ?_, ?_⟩
    · intro v hv
      rw [resEdgeOfPos_fst, Sym2.mem_iff] at hv
      obtain ⟨hu, hw⟩ := P.edgeMult_pos_mem hpos
      rcases hv with rfl | rfl <;> assumption
    · intro x y hxy
      rw [resEdgeOfPos_fst] at hxy
      rw [Sym2.eq_iff] at hxy
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hpos
      · cases P with
        | ordinaryPath p =>
          simpa only [edgeMult,OrdinaryPath.edgeMult,
            if_congr ⟨@listPathAdj_symm _ p.vertsList _ _,@listPathAdj_symm _ p.vertsList _ _⟩ rfl rfl] using hpos
        | badOddCycle c flag | evenCycle c =>
          simp only [edgeMult,MultiBadOddCycle.edgeMult,LongEvenCycle.edgeMult] at hpos ⊢
          rw [if_congr ⟨listCycleAdj_symm,listCycleAdj_symm⟩ rfl rfl]
          exact hpos
        | _ => simpa [edgeMult,TwoBadQuad.edgeMult,MultiBadPath.edgeMult,ZeroBadSquare.edgeMult,
                    DoubledEdge.edgeMult,Sym2.eq_swap] using hpos
  cases P with
  | isolated _ _ => simp [canonicalResEdges] at he
  | twoBadQuad q =>
    simp only [canonicalResEdges,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl <;> exact hmem_of_pair rfl (by simp [edgeMult,TwoBadQuad.edgeMult])
  | badPath q flag =>
    simp only [canonicalResEdges,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl <;> exact hmem_of_pair rfl (by simp [edgeMult,MultiBadPath.edgeMult])
  | zeroBadSquare q =>
    simp only [canonicalResEdges,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> exact hmem_of_pair rfl (by simp [edgeMult,ZeroBadSquare.edgeMult])
  | doubledEdge q =>
    simp only [canonicalResEdges,List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl <;> exact hmem_of_pair rfl (by simp [edgeMult,DoubledEdge.edgeMult])
  | ordinaryPath p =>
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
    apply hmem_of_pair rfl
    exact (show 0 < (if listPathAdj p.vertsList _ _ then 1 else 0) by
      rw [if_pos ⟨i.val,by omega,rfl⟩]; decide)
  | badOddCycle c flag | evenCycle c =>
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
    apply hmem_of_pair rfl
    exact (show 0 < (if listCycleAdj c.vertsList _ _ then 1 else 0) by
      rw [if_pos ⟨i,rfl⟩]; decide)

theorem mem_canonicalResEdges_of_edgeMult_pos [DecidableEq V] (P : ResidualPiece m M side)
    {e : m.Edge} (he : ¬ isMatchingEdge m M e) {u w : V} (hp : e.1 = s(u, w))
    (hpos : 0 < P.edgeMult u w) :
    e ∈ P.canonicalResEdges := by
  
  let re := (residualEdgeEquiv m M).symm ⟨e, he⟩
  have hre : (residualEdgeEquiv m M re).1 = e :=
    congrArg Subtype.val ((residualEdgeEquiv m M).apply_symm_apply ⟨e, he⟩)
  have hre_fst : re.1 = s(u, w) := by
    have := residualEdgeEquiv_fst m M re
    rw [hre] at this
    exact this.symm.trans hp
  have hre_eq_of : ∀ {a b : V} (k : ℕ) (hk : k < (m.residual M).count a b),
      s(u, w) = s(a, b) → re.2.1 = k → e = resEdgeOfPos m M k hk := by
    intro a b k hk hab hkeq
    rw [← hre]
    unfold resEdgeOfPos
    congr 1
    apply congrArg (residualEdgeEquiv m M)
    rcases hre_def : re with ⟨p', i'⟩
    have hp' : p' = s(a, b) := by
      have : p' = re.1 := by rw [hre_def]
      exact this.trans (hre_fst.trans hab)
    have hval' : i'.1 = k := by
      have : i'.1 = re.2.1 := by rw [hre_def]
      exact this.trans hkeq
    subst hp'
    exact Sigma.ext rfl (heq_of_eq (Fin.ext hval'))
  have hlt_uw : re.2.1 < (m.residual M).count u w := by
    rcases hre_def : re with ⟨p', i'⟩
    have hp' : p' = s(u, w) := by
      have : p' = re.1 := by rw [hre_def]
      exact this.trans hre_fst
    subst hp'
    exact i'.2
  have count {a b : V} (h : s(u,w) = s(a,b)) :
      (m.residual M).count u w = (m.residual M).count a b :=
    (Sym2.eq_iff.mp h).elim (fun ⟨hx,hy⟩ => hx ▸ hy ▸ rfl) (fun ⟨hx,hy⟩ => hx ▸ hy ▸ (m.residual M).symm _ _)
  have one {a b : V} (h : s(u,w) = s(a,b)) (h1 : (m.residual M).count a b = 1) :
      e = resEdgeOfPos m M 0 (by omega : 0 < (m.residual M).count a b) := by
    have := count h
    exact hre_eq_of 0 _ h (by omega)
  have pos {p : Prop} [Decidable p] {n : ℕ} (h : 0 < if p then n else 0) : p := by
    by_contra no; simp [no] at h
  cases P with
  | isolated _ _ => simp [edgeMult] at hpos
  | twoBadQuad q =>
    simp only [edgeMult,TwoBadQuad.edgeMult] at hpos
    simp only [canonicalResEdges,List.mem_cons,List.not_mem_nil,or_false]
    by_cases h : s(u,w) = s(q.v1,q.v2)
    · exact Or.inl (one h q.res_count12)
    · rw [if_neg h,zero_add] at hpos
      exact Or.inr (one (pos hpos) q.res_count34)
  | badPath q flag =>
    simp only [edgeMult,MultiBadPath.edgeMult] at hpos
    simp only [canonicalResEdges,List.mem_cons,List.not_mem_nil,or_false]
    rcases pos hpos with h | h | h
    · exact Or.inl (one h q.res_count12)
    · exact Or.inr (Or.inl (one h q.res_count23))
    · exact Or.inr (Or.inr (one h q.res_count34))
  | zeroBadSquare q =>
    simp only [edgeMult,ZeroBadSquare.edgeMult] at hpos
    simp only [canonicalResEdges,List.mem_cons,List.not_mem_nil,or_false]
    rcases pos hpos with h | h | h | h
    · exact Or.inl (one h q.res_count12)
    · exact Or.inr (Or.inl (one h q.res_count23))
    · exact Or.inr (Or.inr (Or.inl (one h q.res_count34)))
    · exact Or.inr (Or.inr (Or.inr (one h q.res_count41)))
  | ordinaryPath p =>
    obtain ⟨i,hi,h⟩ := pos (p := listPathAdj p.vertsList u w) hpos
    exact List.mem_map.mpr ⟨⟨i,by omega⟩,List.mem_finRange _,(one h (p.res_count_edge i hi)).symm⟩
  | badOddCycle c flag | evenCycle c =>
    obtain ⟨i,h⟩ := pos (p := listCycleAdj c.vertsList u w) hpos
    exact List.mem_map.mpr ⟨i,List.mem_finRange _,(one h (c.res_count_edge i)).symm⟩
  | doubledEdge d =>
    have hs := pos (p := s(u,w) = s(d.u,d.v)) hpos
    have := count hs
    have := d.res_count
    simp only [canonicalResEdges,List.mem_cons,List.not_mem_nil,or_false]
    rcases (show re.2.1 = 0 ∨ re.2.1 = 1 by omega) with h|h
    · exact Or.inl (hre_eq_of 0 _ hs h)
    · exact Or.inr (hre_eq_of 1 _ hs h)

@[simp] theorem setMarked_verts [DecidableEq V] (P : ResidualPiece m M side) (mk : Bool) :
    (P.setMarked mk).verts = P.verts := by cases P <;> rfl

@[simp] theorem setMarked_rep (P : ResidualPiece m M side) (mk : Bool) :
    (P.setMarked mk).rep = P.rep := by cases P <;> rfl

@[simp] theorem setMarked_isBad (P : ResidualPiece m M side) (mk : Bool) :
    (P.setMarked mk).isBad = P.isBad := by cases P <;> rfl

@[simp] theorem setMarked_isMarked (P : ResidualPiece m M side) (mk : Bool) :
    (P.setMarked mk).isMarked = (P.isBad && mk) := by cases P <;> simp [setMarked, isMarked, isBad]

@[simp] theorem setMarked_edgeMult [DecidableEq V] (P : ResidualPiece m M side) (mk : Bool)
    (u w : V) : (P.setMarked mk).edgeMult u w = P.edgeMult u w := by cases P <;> rfl

@[simp] theorem setMarked_expectedInsideDeg [DecidableEq V] (P : ResidualPiece m M side)
    (mk : Bool) (v : V) : (P.setMarked mk).expectedInsideDeg v = P.expectedInsideDeg v := by
  cases P <;> rfl

end ResidualPiece

end PieceTemplates
end MultFive.Multi

namespace MultFive.Multi
open Finset SimpleGraph
section SplitMono

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem nodup_four_ne {α : Type*} {v1 v2 v3 v4 : α} (h : [v1, v2, v3, v4].Nodup) :
    v1 ≠ v2 ∧ v1 ≠ v3 ∧ v1 ≠ v4 ∧ v2 ≠ v3 ∧ v2 ≠ v4 ∧ v3 ≠ v4 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at h
  exact ⟨h.1.1, h.1.2.1, h.1.2.2, h.2.1.1, h.2.1.2, h.2.2⟩

theorem disjoint_getElem_of_pairwise_map {α β : Type*} [DecidableEq β]
    {L : List α} {f : α → Finset β} (hpw : (L.map f).Pairwise Disjoint)
    {i j : ℕ} (hi : i < L.length) (hj : j < L.length) (hne : i ≠ j) :
    Disjoint (f (L[i]'hi)) (f (L[j]'hj)) := by
  have hpw' := List.pairwise_iff_getElem.mp (List.pairwise_map.mp hpw)
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · exact hpw' i j hi hj hlt
  · exact (hpw' j i hj hi hgt).symm

omit [Fintype V] [DecidableEq V] in
theorem list_eq_four_of_length {L : List V} (h : L.length = 4) :
    L = [L[0]'(by omega), L[1]'(by omega), L[2]'(by omega), L[3]'(by omega)] := by
  match L with
  | [a, b, c, d] => rfl
  | [] | [_] | [_, _] | [_, _, _] | _ :: _ :: _ :: _ :: _ :: _ => simp at h

omit [Fintype V] [DecidableEq V] in
theorem listCycleAdj_four (v1 v2 v3 v4 u w : V) :
    listCycleAdj [v1, v2, v3, v4] u w ↔
      s(u, w) = s(v1, v2) ∨ s(u, w) = s(v2, v3) ∨
      s(u, w) = s(v3, v4) ∨ s(u, w) = s(v4, v1) := by
  constructor
  · rintro ⟨⟨i, hi⟩, heq⟩
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i
    · left; simpa using heq
    · right; left; simpa using heq
    · right; right; left; simpa using heq
    · right; right; right; simpa using heq
  · rintro (h | h | h | h)
    · exact ⟨⟨0, by simp⟩, by simpa using h⟩
    · exact ⟨⟨1, by simp⟩, by simpa using h⟩
    · exact ⟨⟨2, by simp⟩, by simpa using h⟩
    · exact ⟨⟨3, by simp⟩, by simpa using h⟩

end SplitMono
end MultFive.Multi

namespace MultFive.Multi
open Finset SimpleGraph
section MainDecomposition

variable {V : Type*}

/- A decomposition covers every vertex, reconstructs the multiplicities of internal residual
edges, and records the marked pieces and the special four-vertex configurations. -/
structure PieceDecomposition [Fintype V] [DecidableEq V]
    (m : Multi V) (M : m.support.Subgraph) (side : V → Bool) where
  pieces : List (ResidualPiece m M side)
  
  disjoint : (pieces.map (·.verts)).Pairwise Disjoint
  
  cover_verts : ∀ v : V, ∃ P ∈ pieces, v ∈ P.verts

  cover_edgeMult : ∀ u w : V,
    (pieces.map (fun P => P.edgeMult u w)).sum =
      if side u = side w then (m.residual M).count u w else 0
  
  local_insideDeg : ∀ P ∈ pieces, ∀ v ∈ P.verts,
    (m.residual M).insideDegree side v = P.expectedInsideDeg v

  marked_per_comp : ∀ (r : V) [DecidablePred ((m.residual M).support.Reachable r)],
    (pieces.filter (fun P =>
      P.isMarked && decide ((m.residual M).support.Reachable r P.rep))).length =
    if Odd (pieces.filter (fun P =>
      P.isBad && decide ((m.residual M).support.Reachable r P.rep))).length
    then 1 else 0

  complete_twoBadQuad : ∀ (b : Bool) (v1 v2 v3 v4 : V),
    [v1, v2, v3, v4].Nodup →
    side v1 = b → side v2 = b → side v3 = b → side v4 = b →
    M.Adj v1 v4 → M.Adj v2 v3 →
    0 < (m.residual M).count v1 v2 → 0 < (m.residual M).count v3 v4 →
    (m.residual M).support.Reachable v1 v3 →
    ∃ q : TwoBadQuad m M side, ResidualPiece.twoBadQuad q ∈ pieces ∧
      v1 ∈ (ResidualPiece.twoBadQuad q).verts

  complete_badPath : ∀ (b : Bool) (v1 v2 v3 v4 : V),
    [v1, v2, v3, v4].Nodup →
    side v1 = b → side v2 = b → side v3 = b → side v4 = b →
    M.Adj v1 v4 →
    0 < (m.residual M).count v1 v2 →
    0 < (m.residual M).count v2 v3 →
    0 < (m.residual M).count v3 v4 →
    ∃ (p : MultiBadPath m M side) (flag : Bool), ResidualPiece.badPath p flag ∈ pieces ∧
      ((p.v1 = v1 ∧ p.v2 = v2 ∧ p.v3 = v3 ∧ p.v4 = v4) ∨
       (p.v1 = v4 ∧ p.v2 = v3 ∧ p.v3 = v2 ∧ p.v4 = v1))

  complete_zeroBadSquare : ∀ (b : Bool) (v1 v2 v3 v4 : V),
    [v1, v2, v3, v4].Nodup →
    side v1 = b → side v2 = b → side v3 = b → side v4 = b →
    0 < (m.residual M).count v1 v2 →
    0 < (m.residual M).count v2 v3 →
    0 < (m.residual M).count v3 v4 →
    0 < (m.residual M).count v4 v1 →
    ∃ q : ZeroBadSquare m M side, ResidualPiece.zeroBadSquare q ∈ pieces ∧
      q.verts = {v1, v2, v3, v4} ∧
      ({s(q.v1, q.v3), s(q.v2, q.v4)} : Finset (Sym2 V)) = {s(v1, v3), s(v2, v4)} ∧
      (∀ u w, q.edgeMult u w = 1 ↔
        s(u, w) = s(v1, v2) ∨ s(u, w) = s(v2, v3) ∨
        s(u, w) = s(v3, v4) ∨ s(u, w) = s(v4, v1))

theorem list_sum_eq_single_of_zero {α : Type*} (L : List α) (f : α → ℕ)
    (i : ℕ) (hi : i < L.length) (h0 : ∀ (j : ℕ) (hj : j < L.length), j ≠ i → f (L[j]'hj) = 0) :
    (L.map f).sum = f (L[i]'hi) := by
  induction L generalizing i with
  | nil => simp at hi
  | cons a rest ih =>
    cases i with
    | zero =>
      simp only [List.map_cons, List.sum_cons, List.getElem_cons_zero]
      have hrest : (rest.map f).sum = 0 := by
        rw [List.sum_eq_zero_iff]
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
        exact h0 (j + 1) (by simpa using hj) (by omega)
      omega
    | succ k =>
      simp only [List.map_cons, List.sum_cons, List.getElem_cons_succ]
      have ha : f a = 0 := h0 0 (by simp) (by omega)
      have hrest := ih k (by simpa using hi) (fun j hj hne => h0 (j + 1) (by simpa using hj) (by omega))
      omega

theorem piece_reachable_in_resMono [Fintype V] [DecidableEq V]
    {m : Multi V} {M : m.support.Subgraph} {side : V → Bool}
    {P : ResidualPiece m M side}
    (hnotQuad : ∀ q, P ≠ .twoBadQuad q)
    (hedge : ∀ u ∈ P.verts, ∀ w : V, P.edgeMult u w = ((m.residual M).monoMulti side).count u w)
    {u w : V} (hu : u ∈ P.verts) (hw : w ∈ P.verts) :
    ((m.residual M).monoMulti side).support.Reachable u w := by
  classical
  have positive (x y : V) (adj : listPathAdj P.vertsList x y) : 0 < P.edgeMult x y := by
    have cyclic {l : List V} (h : listPathAdj l x y) : listCycleAdj l x y := by
      obtain ⟨i,k,e⟩ := h
      exact ⟨⟨i,by omega⟩,by simpa [Nat.mod_eq_of_lt k] using e⟩
    cases P with
    | isolated v h => exact (listPathAdj_singleton _ _ _ adj).elim
    | twoBadQuad q => exact (hnotQuad q rfl).elim
    | ordinaryPath p =>
      change listPathAdj p.vertsList x y at adj
      exact (show 0 < (if listPathAdj p.vertsList x y then 1 else 0) by rw [if_pos adj]; decide)
    | badOddCycle p flag | evenCycle p =>
      change listPathAdj p.vertsList x y at adj
      exact (show 0 < (if listCycleAdj p.vertsList x y then 1 else 0) by rw [if_pos (cyclic adj)]; decide)
    | badPath p flag | zeroBadSquare p =>
      change listPathAdj [p.v1,p.v2,p.v3,p.v4] x y at adj
      simp only [listPathAdj_cons_cons,listPathAdj_singleton,or_false] at adj
      simp only [ResidualPiece.edgeMult,MultiBadPath.edgeMult,ZeroBadSquare.edgeMult]
      rw [if_pos (by rcases adj with h|h|h <;> tauto)]; decide
    | doubledEdge d =>
      change listPathAdj [d.u,d.v] x y at adj
      simp only [listPathAdj_cons_cons,listPathAdj_singleton,or_false] at adj
      change 0 < if s(x,y) = s(d.u,d.v) then 2 else 0
      rw [if_pos adj]; decide
  let l := P.vertsList
  have from_zero (k : ℕ) (hk : k < l.length) : ((m.residual M).monoMulti side).support.Reachable l[0] l[k] := by
    induction k with
    | zero => exact Reachable.refl _
    | succ j ih =>
      have e : listPathAdj l l[j] l[j+1] := ⟨j,hk,rfl⟩
      have pos := positive _ _ e
      rw [hedge _ (List.mem_toFinset.mpr (List.getElem_mem _)) _] at pos
      exact (ih (by omega)).trans (show ((m.residual M).monoMulti side).support.Adj l[j] l[j+1] from pos).reachable
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hu)
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hw)
  exact (from_zero i hi).symm.trans (from_zero j hj)

theorem piece_subset_of_closed [Fintype V] [DecidableEq V]
    {m : Multi V} {M : m.support.Subgraph} {side : V → Bool}
    {P : ResidualPiece m M side} {S : Finset V} {v₀ : V}
    (hnotQuad : ∀ q, P ≠ .twoBadQuad q)
    (hedge : ∀ u ∈ P.verts, ∀ w : V, P.edgeMult u w = ((m.residual M).monoMulti side).count u w)
    (hv₀P : v₀ ∈ P.verts) (hv₀S : v₀ ∈ S)
    (hclosed : ∀ x ∈ S, ∀ w : V, ((m.residual M).monoMulti side).support.Adj x w → w ∈ S) :
    P.verts ⊆ S := by
  intro x hx
  obtain ⟨w⟩ := piece_reachable_in_resMono hnotQuad hedge hv₀P hx
  have hwalk : ∀ {a d : V} (q : ((m.residual M).monoMulti side).support.Walk a d), a ∈ S → d ∈ S := by
    intro a d q; induction q with
    | nil => exact id
    | cons hadj _ ih => intro ha; exact ih (hclosed _ ha _ hadj)
  exact hwalk w hv₀S

theorem four_cycle_diag_iff {α : Type*} [DecidableEq α] {a b c d : α}
    (hnd : [a, b, c, d].Nodup) {x y : α}
    (hx : x ∈ ({a, b, c, d} : Finset α)) (hy : y ∈ ({a, b, c, d} : Finset α)) (hne : x ≠ y) :
    (s(x, y) = s(a, c) ∨ s(x, y) = s(b, d)) ↔
      ¬ (s(x, y) = s(a, b) ∨ s(x, y) = s(b, c) ∨ s(x, y) = s(c, d) ∨ s(x, y) = s(d, a)) := by
  obtain ⟨h12, h13, h14, h23, h24, h34⟩ := nodup_four_ne hnd
  simp only [mem_insert, mem_singleton] at hx hy
  rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
    try exact absurd rfl hne
  all_goals
    simp only [Sym2.eq_iff]
    grind

section shortPathOrder
variable [DecidableEq V]

private theorem steps_in_list {l : List V} (nd : l.Nodup) {a b : V}
    (h : listPathAdj l a b) : l.idxOf a + 1 = l.idxOf b ∨ l.idxOf b + 1 = l.idxOf a := by
  obtain ⟨i,hi,e⟩ := h
  rcases Sym2.eq_iff.mp e with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
    simp [nd.idxOf_getElem]

private theorem path_end_length {l : List V} {a b c d : V} (nd : l.Nodup)
    (h : [a,b,c,d].Nodup) (ab : listPathAdj l a b) (bc : listPathAdj l b c) (cd : listPathAdj l c d)
    (ea : l.idxOf a = 0 ∨ l.idxOf a+1 = l.length)
    (ed : l.idxOf d = 0 ∨ l.idxOf d+1 = l.length) : l.length = 4 := by
  have mem := listPathAdj_mem ab
  have mem' := listPathAdj_mem cd
  have inj (u v : V) (hu : u ∈ l) (hv : v ∈ l) : l.idxOf u = l.idxOf v → u = v := by
    intro e
    rw [← List.getElem_idxOf (List.idxOf_lt_length_of_mem hu),← List.getElem_idxOf (List.idxOf_lt_length_of_mem hv)]
    congr
  obtain ⟨_,ac,ad,_,bd,_⟩ := nodup_four_ne h
  have n₁ := mt (inj a c mem.1 mem'.1) ac
  have n₂ := mt (inj a d mem.1 mem'.2) ad
  have n₃ := mt (inj b d mem.2 mem'.2) bd
  have s₁ := steps_in_list nd ab; have s₂ := steps_in_list nd bc; have s₃ := steps_in_list nd cd
  omega

private theorem ordered_four_path (a b c d x y z w : V) (d1 : [a,b,c,d].Nodup) (d2 : [x,y,z,w].Nodup)
    (ea : a=x ∨ a=w) (ed : d=x ∨ d=w)
    (ab : s(a,b)=s(x,y) ∨ s(a,b)=s(y,z) ∨ s(a,b)=s(z,w))
    (cd : s(c,d)=s(x,y) ∨ s(c,d)=s(y,z) ∨ s(c,d)=s(z,w)) :
    (x=a ∧ y=b ∧ z=c ∧ w=d) ∨ (x=d ∧ y=c ∧ z=b ∧ w=a) := by
  obtain ⟨_,_,_,_,_,_⟩ := nodup_four_ne d1
  obtain ⟨_,_,_,_,_,_⟩ := nodup_four_ne d2
  simp only [Sym2.eq_iff] at ab cd
  grind

private theorem ends_of_degree_ne_two {x a b : V} (h : (if x=a ∨ x=b then 1 else 2 : ℕ) ≠ 2) : x=a ∨ x=b := by
  by_contra no
  simp [no] at h

end shortPathOrder

theorem complete_badPath_of_pieces [Fintype V] [DecidableEq V]
    (m : Multi V) (M : m.support.Subgraph) (hm : M.IsPerfectMatching)
    (side : V → Bool) (h_in : ∀ v, m.insideDegree side v ≤ 2)
    (pieces : List (ResidualPiece m M side))
    (hcov : ∀ v : V, ∃ P ∈ pieces, v ∈ P.verts)
    (hedge : ∀ P ∈ pieces, ∀ u ∈ P.verts, ∀ w : V,
      P.edgeMult u w = ((m.residual M).monoMulti side).count u w)
    (hdeg : ∀ P ∈ pieces, ∀ v ∈ P.verts,
      (m.residual M).insideDegree side v = P.expectedInsideDeg v)
    (b : Bool) (v1 v2 v3 v4 : V) (hnd : [v1, v2, v3, v4].Nodup)
    (hs1 : side v1 = b) (hs2 : side v2 = b) (hs3 : side v3 = b) (hs4 : side v4 = b)
    (hM14 : M.Adj v1 v4)
    (hr12 : 0 < (m.residual M).count v1 v2)
    (hr23 : 0 < (m.residual M).count v2 v3)
    (hr34 : 0 < (m.residual M).count v3 v4) :
    ∃ (p : MultiBadPath m M side) (flag : Bool), ResidualPiece.badPath p flag ∈ pieces ∧
      ((p.v1 = v1 ∧ p.v2 = v2 ∧ p.v3 = v3 ∧ p.v4 = v4) ∨
       (p.v1 = v4 ∧ p.v2 = v3 ∧ p.v3 = v2 ∧ p.v4 = v1)) := by
  classical
  obtain ⟨neab,neac,nead,nebc,nebd,necd⟩ := nodup_four_ne hnd
  let k := (m.residual M).monoMulti side
  have ab : 0 < k.count v1 v2 := by simpa [k,hs1,hs2] using hr12
  have bc : 0 < k.count v2 v3 := by simpa [k,hs2,hs3] using hr23
  have cd : 0 < k.count v3 v4 := by simpa [k,hs3,hs4] using hr34
  obtain ⟨P,hP,ha⟩ := hcov v1
  have ab' : 0 < P.edgeMult v1 v2 := by rw [hedge P hP v1 ha]; exact ab
  have hb := (P.edgeMult_pos_mem ab').2
  have bc' : 0 < P.edgeMult v2 v3 := by rw [hedge P hP v2 hb]; exact bc
  have hc := (P.edgeMult_pos_mem bc').2
  have cd' : 0 < P.edgeMult v3 v4 := by rw [hedge P hP v3 hc]; exact cd
  have hd := (P.edgeMult_pos_mem cd').2
  have end1 : P.expectedInsideDeg v1 ≠ 2 := fun h =>
    matching_crossing_of_residual_insideDeg_two m M side h_in ((hdeg P hP v1 ha).trans h) hM14 (hs4.trans hs1.symm)
  have end4 : P.expectedInsideDeg v4 ≠ 2 := fun h =>
    matching_crossing_of_residual_insideDeg_two m M side h_in ((hdeg P hP v4 hd).trans h) hM14.symm (hs1.trans hs4.symm)
  have ib : 2 ≤ P.expectedInsideDeg v2 := by
    have ba : 0 < k.count v2 v1 := k.symm v2 v1 ▸ ab
    have e := sum_le_sum_of_subset (f := k.count v2) (subset_univ ({v1,v3} : Finset V))
    change ∑ z ∈ ({v1,v3} : Finset V), k.count v2 z ≤ k.degree v2 at e
    rw [sum_pair neac] at e
    have eq : k.degree v2 = P.expectedInsideDeg v2 := (monoMulti_degree ..).trans (hdeg P hP v2 hb)
    omega
  cases P with
  | isolated | twoBadQuad => simp [ResidualPiece.expectedInsideDeg] at ib
  | badOddCycle | zeroBadSquare | evenCycle | doubledEdge => exact (end1 rfl).elim
  | ordinaryPath p =>
    have read {x y : V} (h : 0 < (ResidualPiece.ordinaryPath p).edgeMult x y) : listPathAdj p.vertsList x y := by
      by_contra n; simp [ResidualPiece.edgeMult,OrdinaryPath.edgeMult,n] at h
    have ends {x} (h : x=p.first ∨ x=p.last) : p.vertsList.idxOf x = 0 ∨ p.vertsList.idxOf x+1 = p.vertsList.length := by
      obtain rfl | rfl := h
      · left; simp [OrdinaryPath.first,p.nodup.idxOf_getElem]
      · right; simp [OrdinaryPath.last,p.nodup.idxOf_getElem]; have := p.hlen; omega
    have a := ends_of_degree_ne_two (show (if v1=p.first ∨ v1=p.last then 1 else 2 : ℕ) ≠ 2 from end1)
    have d := ends_of_degree_ne_two (show (if v4=p.first ∨ v4=p.last then 1 else 2 : ℕ) ≠ 2 from end4)
    have size := path_end_length p.nodup hnd (read ab') (read bc') (read cd') (ends a) (ends d)
    have last : p.vertsList[3]'(by omega) = p.last := by unfold OrdinaryPath.last; congr 1; omega
    have bm : ¬M.Adj p.first p.last := by
      rw [← last]
      exact p.not_bad_path size
    rcases a with rfl | rfl <;> rcases d with d | d <;> rw [d] at hM14 nead
    · exact (nead rfl).elim
    · exact (bm hM14).elim
    · exact (bm hM14.symm).elim
    · exact (nead rfl).elim
  | badPath p flag =>
    have edge {x y} (h : 0 < (ResidualPiece.badPath p flag).edgeMult x y) :
      s(x,y)=s(p.v1,p.v2) ∨ s(x,y)=s(p.v2,p.v3) ∨ s(x,y)=s(p.v3,p.v4) := by
      by_contra no; simp only [ResidualPiece.edgeMult,MultiBadPath.edgeMult,if_neg no,lt_self_iff_false] at h
    exact ⟨p,flag,hP,ordered_four_path _ _ _ _ _ _ _ _ hnd p.nodup (ends_of_degree_ne_two end1) (ends_of_degree_ne_two end4) (edge ab') (edge cd')⟩

private theorem square_diag {V : Type*} [DecidableEq V] {a b c d : V} (nd : [a,b,c,d].Nodup) (x y : V) :
    s(x,y) ∈ ({s(a,c),s(b,d)} : Finset (Sym2 V)) ↔ x ∈ ({a,b,c,d} : Finset V) ∧
      y ∈ ({a,b,c,d} : Finset V) ∧ x ≠ y ∧ ¬ (s(x,y) = s(a,b) ∨ s(x,y) = s(b,c) ∨ s(x,y) = s(c,d) ∨ s(x,y) = s(d,a)) := by
  rw [Finset.mem_insert,Finset.mem_singleton]
  constructor
  · intro h
    have hx : x ∈ ({a,b,c,d} : Finset V) := by rcases h with h|h <;> rcases Sym2.eq_iff.mp h with ⟨rfl,_⟩|⟨rfl,_⟩ <;> simp
    have hy : y ∈ ({a,b,c,d} : Finset V) := by rcases h with h|h <;> rcases Sym2.eq_iff.mp h with ⟨_,rfl⟩|⟨_,rfl⟩ <;> simp
    have ne : x ≠ y := by
      obtain ⟨ab,ac,ad,bc,bd,cd⟩ := nodup_four_ne nd
      rcases h with h|h <;> rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> grind
    exact ⟨hx,hy,ne,(four_cycle_diag_iff nd hx hy ne).mp h⟩
  · rintro ⟨hx,hy,ne,h⟩; exact (four_cycle_diag_iff nd hx hy ne).mpr h

theorem complete_zeroBadSquare_of_pieces [Fintype V] [DecidableEq V]
    (m : Multi V) (M : m.support.Subgraph)
    (side : V → Bool) (h_in : ∀ v, m.insideDegree side v ≤ 2)
    (pieces : List (ResidualPiece m M side))
    (hcov : ∀ v : V, ∃ P ∈ pieces, v ∈ P.verts)
    (hedge : ∀ P ∈ pieces, ∀ u ∈ P.verts, ∀ w : V,
      P.edgeMult u w = ((m.residual M).monoMulti side).count u w)
    (hdeg : ∀ P ∈ pieces, ∀ v ∈ P.verts,
      (m.residual M).insideDegree side v = P.expectedInsideDeg v)
    (b : Bool) (v1 v2 v3 v4 : V) (hnd : [v1, v2, v3, v4].Nodup)
    (hs1 : side v1 = b) (hs2 : side v2 = b) (hs3 : side v3 = b) (hs4 : side v4 = b)
    (hr12 : 0 < (m.residual M).count v1 v2) (hr23 : 0 < (m.residual M).count v2 v3)
    (hr34 : 0 < (m.residual M).count v3 v4) (hr41 : 0 < (m.residual M).count v4 v1) :
    ∃ q : ZeroBadSquare m M side, ResidualPiece.zeroBadSquare q ∈ pieces ∧
      q.verts = {v1, v2, v3, v4} ∧
      ({s(q.v1, q.v3), s(q.v2, q.v4)} : Finset (Sym2 V)) = {s(v1, v3), s(v2, v4)} ∧
      (∀ u w, q.edgeMult u w = 1 ↔
        s(u, w) = s(v1, v2) ∨ s(u, w) = s(v2, v3) ∨
        s(u, w) = s(v3, v4) ∨ s(u, w) = s(v4, v1)) := by
  classical
  let L := [v1,v2,v3,v4]
  let vert (i : Fin 4) := L[i.val]'(by simpa [L] using i.isLt)
  have inj : Function.Injective vert := fun i j h => Fin.ext (getElem_inj hnd h)
  have mono (i : Fin 4) : side (vert i) = b := by fin_cases i <;> assumption
  have next (i : Fin 4) : 0 < (m.residual M).count (vert i) (vert (i+1)) := by
    fin_cases i <;> assumption
  have cycle (i : Fin 4) : 0 < ((m.residual M).monoMulti side).count (vert i) (vert (i+1)) := by
    simpa [monoMulti_count,mono] using next i
  have hres_eq (x) (hx : x ∈ ({v1,v2,v3,v4} : Finset V)) (w : V) :
      ((m.residual M).monoMulti side).count x w = if s(x,w) = s(v1,v2) ∨ s(x,w) = s(v2,v3) ∨
        s(x,w) = s(v3,v4) ∨ s(x,w) = s(v4,v1) then 1 else 0 := by
    have mem : x ∈ L := by simpa [L] using hx
    obtain ⟨k,hk,rfl⟩ := List.getElem_of_mem mem
    let i : Fin 4 := ⟨k,by simpa [L] using hk⟩
    change ((m.residual M).monoMulti side).count (vert i) w = _
    rw [cycle_count_eq_of_inside_le_two (m.residual M) side
      (fun x => (insideDegree_residual_le m M side x).trans (h_in x)) (by decide : 3 ≤ 4) inj cycle i w]
    congr 1
    simp [Fin.exists_fin_succ,vert,L,i]
  let S : Finset V := {v1, v2, v3, v4}
  have hcard_S : S.card = 4 := by
    have : S = ([v1, v2, v3, v4] : List V).toFinset := by ext; simp [S]
    rw [this, List.toFinset_card_of_nodup hnd]; rfl
  have hdeg2_S : ∀ x ∈ S, (m.residual M).insideDegree side x = 2 := by
    intro x hx; rw [← monoMulti_degree]
    have hcount_L : ∀ u ∈ ([v1, v2, v3, v4] : List V), ∀ w : V,
        ((m.residual M).monoMulti side).count u w = if listCycleAdj [v1, v2, v3, v4] u w then 1 else 0 := by
      intro u hu w
      rw [if_congr (listCycleAdj_four v1 v2 v3 v4 u w) rfl rfl]
      exact hres_eq u (by simpa [S] using hu) w
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (show x ∈ ([v1, v2, v3, v4] : List V) by simpa [S] using hx)
    exact degree_eq_two_of_listCycleAdj_count hnd (by simp) hcount_L k hk
  have hS_closed : ∀ x ∈ S, ∀ w : V,
      ((m.residual M).monoMulti side).support.Adj x w → w ∈ S := by
    intro x hx w hadj
    have hpos : 0 < ((m.residual M).monoMulti side).count x w := hadj
    rw [hres_eq x hx w] at hpos
    have hor : s(x, w) = s(v1, v2) ∨ s(x, w) = s(v2, v3) ∨
        s(x, w) = s(v3, v4) ∨ s(x, w) = s(v4, v1) := by by_contra hn; rw [if_neg hn] at hpos; omega
    rcases hor with hs | hs | hs | hs <;> rw [Sym2.eq_iff] at hs <;>
      rcases hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [S]
  obtain ⟨P, hP, hv1P⟩ := hcov v1
  have hP_edge := hedge P hP
  have hP_deg := hdeg P hP
  have hv2P : v2 ∈ P.verts := by
    have hpos : 0 < P.edgeMult v1 v2 := by rw [hP_edge v1 hv1P v2, hres_eq v1 (by simp) v2]; simp
    exact (P.edgeMult_pos_mem hpos).2
  have hv3P : v3 ∈ P.verts := by
    have hpos : 0 < P.edgeMult v2 v3 := by rw [hP_edge v2 hv2P v3, hres_eq v2 (by simp) v3]; simp
    exact (P.edgeMult_pos_mem hpos).2
  have hv4P : v4 ∈ P.verts := by
    have hpos : 0 < P.edgeMult v3 v4 := by rw [hP_edge v3 hv3P v4, hres_eq v3 (by simp) v4]; simp
    exact (P.edgeMult_pos_mem hpos).2
  have hS_sub : S ⊆ P.verts := by
    intro x hx; simp only [S, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have hP_not_quad : ∀ q, P ≠ .twoBadQuad q := fun q hEq => by
    have h1 := hP_deg v1 hv1P; rw [hEq] at h1
    have h2 := hdeg2_S v1 (by simp [S])
    simp [ResidualPiece.expectedInsideDeg] at h1; omega
  have hP_eq_S : P.verts = S :=
    Finset.Subset.antisymm (piece_subset_of_closed hP_not_quad hP_edge hv1P (by simp [S]) hS_closed) hS_sub
  have size : P.vertsList.length = 4 := by
    rw [← List.toFinset_card_of_nodup P.vertsList_nodup]; exact (congrArg Finset.card hP_eq_S).trans hcard_S
  have rep := (hP_deg P.rep P.rep_mem_verts).symm.trans (hdeg2_S P.rep (hP_eq_S ▸ P.rep_mem_verts))
  cases hP_eq : P with
  | isolated v hv | twoBadQuad v | badPath v flag | ordinaryPath v =>
    rw [hP_eq] at rep; simp [ResidualPiece.rep,ResidualPiece.expectedInsideDeg] at rep
  | doubledEdge d => rw [hP_eq] at size; simp [ResidualPiece.vertsList,DoubledEdge.vertsList] at size
  | badOddCycle c flag => rw [hP_eq] at size; change c.vertsList.length = 4 at size; have := c.hlen; omega
  | evenCycle c => rw [hP_eq] at size; change c.vertsList.length = 4 at size; have := c.hlen; have := c.ht; omega
  | zeroBadSquare q =>
    subst hP_eq
    have vs : (ResidualPiece.zeroBadSquare q).verts = q.verts := by
      simp [ResidualPiece.verts,ResidualPiece.vertsList,ZeroBadSquare.verts,ZeroBadSquare.vertsList]
    have eq : q.verts = S := vs.symm.trans hP_eq_S
    have rim (x y : V) : q.edgeMult x y = 1 ↔ s(x,y) = s(v1,v2) ∨ s(x,y) = s(v2,v3) ∨
        s(x,y) = s(v3,v4) ∨ s(x,y) = s(v4,v1) := by
      by_cases hx : x ∈ q.verts
      · have count := hP_edge x (vs.symm ▸ hx) y
        change q.edgeMult x y = _ at count
        rw [count,hres_eq x (show x ∈ S from eq ▸ hx) y]
        split_ifs with h
        · exact iff_of_true rfl h
        · exact iff_of_false (by decide) h
      · rw [show q.edgeMult x y = 0 from (ResidualPiece.zeroBadSquare q).edgeMult_eq_zero_of_not_mem (by rwa [vs])]
        rw [eq] at hx
        simp [S] at hx
        simp [Sym2.eq_iff,hx.1,hx.2.1,hx.2.2.1,hx.2.2.2]
    refine ⟨q,hP,eq,?_,rim⟩
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      rw [square_diag q.nodup, square_diag hnd]
      change (_ ∈ q.verts ∧ _ ∈ q.verts ∧ _ ∧ _) ↔ _
      rw [eq]
      have corners := rim x y
      simp only [ZeroBadSquare.edgeMult] at corners
      have present (p : Prop) [Decidable p] : ((if p then 1 else 0 : ℕ) = 1) ↔ p := by split <;> simp_all only [zero_ne_one,false_iff,iff_false,true_iff,iff_true]
      rw [present] at corners
      exact and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => not_congr corners

namespace PieceDecomposition

variable [Fintype V] [DecidableEq V] {m : Multi V} {M : m.support.Subgraph} {side : V → Bool}

theorem edgeMult_eq_of_mem (D : PieceDecomposition m M side) {P : ResidualPiece m M side}
    (hP : P ∈ D.pieces) {u : V} (hu : u ∈ P.verts) (w : V) :
    P.edgeMult u w = if side u = side w then (m.residual M).count u w else 0 := by
  rw [← D.cover_edgeMult u w]
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hP
  symm
  refine list_sum_eq_single_of_zero D.pieces (fun Q => Q.edgeMult u w) i hi ?_
  intro j hj hne
  exact (D.pieces[j]'hj).edgeMult_eq_zero_of_not_mem
    (Finset.disjoint_left.mp (disjoint_getElem_of_pairwise_map D.disjoint hi hj hne.symm) hu)

theorem at_most_one_marked_per_comp (D : PieceDecomposition m M side)
    (r : V) [DecidablePred ((m.residual M).support.Reachable r)] :
    (D.pieces.filter (fun P =>
      P.isMarked && decide ((m.residual M).support.Reachable r P.rep))).length ≤ 1 := by
  rw [D.marked_per_comp r]
  split_ifs <;> omega

theorem even_unmarked_bad_per_comp (D : PieceDecomposition m M side)
    (r : V) [DecidablePred ((m.residual M).support.Reachable r)] :
    Even (D.pieces.filter (fun P =>
      P.isUnmarkedBad && decide ((m.residual M).support.Reachable r P.rep))).length := by
  have hsplit : ∀ (L : List (ResidualPiece m M side)),
      (L.filter (fun P => P.isBad && decide ((m.residual M).support.Reachable r P.rep))).length =
      (L.filter (fun P => P.isMarked && decide ((m.residual M).support.Reachable r P.rep))).length +
      (L.filter (fun P => P.isUnmarkedBad && decide ((m.residual M).support.Reachable r P.rep))).length := by
    intro L
    induction L with
    | nil => simp
    | cons P rest ih =>
      simp only [List.filter_cons]
      have hbad_mk : P.isMarked = true → P.isBad = true := by
        cases P <;> simp [ResidualPiece.isMarked, ResidualPiece.isBad]
      by_cases hreach : (m.residual M).support.Reachable r P.rep
      · cases hmk : P.isMarked <;> cases hbad : P.isBad
        · simp [ResidualPiece.isUnmarkedBad, hmk, hbad, hreach, ih]
        · simp [ResidualPiece.isUnmarkedBad, hmk, hbad, hreach, ih]; omega
        · exact absurd (hbad_mk hmk) (by simp [hbad])
        · simp [ResidualPiece.isUnmarkedBad, hmk, hbad, hreach, ih]; omega
      · simp [hreach, ih]
  have hlen := hsplit D.pieces
  have hmk := D.marked_per_comp r
  by_cases hodd : Odd (D.pieces.filter (fun P =>
      P.isBad && decide ((m.residual M).support.Reachable r P.rep))).length
  · rw [if_pos hodd] at hmk
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩
  · rw [if_neg hodd] at hmk
    obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp hodd
    exact ⟨k, by omega⟩

theorem canonical_edges_mem_iff (D : PieceDecomposition m M side) (e : m.Edge) :
    e ∈ (D.pieces.map (·.canonicalResEdges)).flatten ↔
      ¬ isMatchingEdge m M e ∧ side (m.family.left e) = side (m.family.right e) := by
  constructor
  · intro he
    obtain ⟨es, hes, he'⟩ := List.mem_flatten.mp he
    obtain ⟨P, _, rfl⟩ := List.mem_map.mp hes
    obtain ⟨hnotM, hverts, _⟩ := P.canonicalResEdges_mem_props he'
    refine ⟨hnotM, ?_⟩
    have hl : m.family.left e ∈ P.verts :=
      hverts _ ((m.family_incident_iff _ _).mp (Or.inl rfl))
    have hr : m.family.right e ∈ P.verts :=
      hverts _ ((m.family_incident_iff _ _).mp (Or.inr rfl))
    rw [P.side_of_mem hl, P.side_of_mem hr]
  · rintro ⟨hnotM, hsame⟩
    let u := m.family.left e
    let w := m.family.right e
    have hpair : e.1 = s(u, w) := (m.family_pair e).symm
    obtain ⟨P, hP, huP⟩ := D.cover_verts u
    refine List.mem_flatten.mpr ⟨P.canonicalResEdges, List.mem_map.mpr ⟨P, hP, rfl⟩, ?_⟩
    apply P.mem_canonicalResEdges_of_edgeMult_pos hnotM hpair
    rw [D.edgeMult_eq_of_mem hP huP w, if_pos hsame]
    let re := (residualEdgeEquiv m M).symm ⟨e, hnotM⟩
    have hre : (residualEdgeEquiv m M re).1 = e :=
      congrArg Subtype.val ((residualEdgeEquiv m M).apply_symm_apply ⟨e, hnotM⟩)
    have hre_fst : re.1 = s(u, w) := by
      have := residualEdgeEquiv_fst m M re
      rw [hre] at this
      exact this.symm.trans hpair
    rcases hre_def : re with ⟨p', i'⟩
    have hp' : p' = s(u, w) := by
      have : p' = re.1 := by rw [hre_def]
      exact this.trans hre_fst
    subst hp'
    exact Nat.zero_lt_of_lt i'.2

end PieceDecomposition

end MainDecomposition
end MultFive.Multi

end

section 

namespace Kostochka.FiveRegular.Auxiliary
open Finset Subdivision Restoration
variable {V E I : Type*}

theorem sum_coloredDegree [Fintype V] [DecidableEq V] [Fintype E]
    (D : Family V E) (f : E → Bool) (b : Bool) :
    ∑ v, coloredDegree D f v b = 2 * ∑ e, (if f e = b then 1 else 0 : ℕ) := by
  classical
  unfold coloredDegree
  rw [Finset.sum_add_distrib]
  conv_lhs => lhs; rw [Finset.sum_comm]
  conv_lhs => rhs; rw [Finset.sum_comm]
  have calcEnd (p : E → V) (e : E) :
      (∑ v, (if v = p e ∧ f e = b then 1 else 0 : ℕ)) = if f e = b then 1 else 0 := by
    by_cases h : f e = b <;> simp [h]
  simp_rw [calcEnd]
  omega

theorem sum_oldDegree (s : Shape) : ∑ v : Fin s.vertices, oldDegree s v.val = 2 * residualCount s := by
  let keep (j : ℕ) := decide (s ≠ .alternatingSquare ∨ j % 2 = 0)
  have e := sum_coloredDegree s.family (fun i => keep i.val) true
  simp_rw [Shape.coloredDegree_family] at e
  change ∑ v : Fin s.vertices, s.inc keep v.val = _
  rw [e]
  congr 1
  by_cases hs : s = .alternatingSquare
  · subst s
    decide
  · simp [keep,hs,residualCount]

theorem even_pieces_of_regular [Fintype V] [Fintype I] [Fintype E] [DecidableEq V]
    (shape : I → Shape) (pos : (Σ i, Fin (shape i).vertices) ≃ V) (D : Family V E)
    (regular : ∀ i (v : Fin (shape i).vertices), coloredDegree D (fun _ => true) (pos ⟨i,v⟩) true +
      oldDegree (shape i) v.val = 4) :
    Even (Fintype.card E + ∑ i, residualCount (shape i)) := by
  classical
  let outside (iv : Σ i, Fin (shape i).vertices) := coloredDegree D (fun _ => true) (pos iv) true
  let inside (iv : Σ i, Fin (shape i).vertices) := oldDegree (shape iv.1) iv.2.val
  have hw : ∑ iv, (outside iv + inside iv) = ∑ _ : (Σ i, Fin (shape i).vertices), (4 : ℕ) := by
    apply Finset.sum_congr rfl
    rintro ⟨i,v⟩ _
    exact regular i v
  have outer : ∑ iv, outside iv = 2 * Fintype.card E := by
    change ∑ iv, (fun w => coloredDegree D (fun _ => true) w true) (pos iv) = _
    rw [pos.sum_comp (fun w => coloredDegree D (fun _ => true) w true), sum_coloredDegree]
    simp
  have inner : ∑ iv, inside iv = 2 * ∑ i, residualCount (shape i) := by
    rw [Fintype.sum_sigma, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => sum_oldDegree (shape i)
  rw [Finset.sum_add_distrib,outer,inner] at hw
  simp only [Finset.sum_const,card_univ,nsmul_eq_mul] at hw
  change 2 * Fintype.card E + 2 * (∑ i, residualCount (shape i)) = Fintype.card (Σ i, Fin (shape i).vertices) * 4 at hw
  exact ⟨Fintype.card (Σ i, Fin (shape i).vertices), by omega⟩

end Kostochka.FiveRegular.Auxiliary

end

section 

namespace Kostochka.FiveRegular.Auxiliary
open Finset Subdivision Restoration
variable {V E I C : Type*}

noncomputable def fiberPositions (shape : I → Shape) (pos : (Σ i, Fin (shape i).vertices) ≃ V)
    (group : I → C) (home : V → C) (within : ∀ i v, home (pos ⟨i,v⟩) = group i) (c : C) :
    (Σ i : {i // group i = c}, Fin (shape i.val).vertices) ≃ {v // home v = c} :=
  Equiv.ofBijective (fun x => ⟨pos ⟨x.1.val,x.2⟩,(within _ _).trans x.1.property⟩) (by
    constructor
    · rintro ⟨⟨i,hi⟩,v⟩ ⟨⟨j,hj⟩,w⟩ he
      have e : (Sigma.mk i v) = ⟨j,w⟩ := pos.injective (congrArg Subtype.val he)
      cases e
      rfl
    · rintro ⟨w,hw⟩
      obtain ⟨⟨i,v⟩,rfl⟩ := pos.surjective w
      exact ⟨⟨⟨i,(within _ _).symm.trans hw⟩,v⟩,rfl⟩)

variable [Fintype V] [Fintype E] [Fintype I] [DecidableEq V] [DecidableEq E] [DecidableEq I]

private theorem partition_marked (shape : I → Shape) (pos : (Σ i, Fin (shape i).vertices) ≃ V) (D : Family V E)
    (conn : ∀ v w, Relation.ReflTransGen (Joined D) v w)
    (regular : ∀ i (v : Fin (shape i).vertices), coloredDegree D (fun _ => true) (pos ⟨i,v⟩) true +
      oldDegree (shape i) v.val = 4)
    (badEven : Even (∑ i, (if unmarkedBad (shape i) then 1 else 0 : ℕ)))
    (request : I → Option Bool) (isDirect : ∀ i b, request i = some b → direct (shape i) = true)
    (unique : ∀ i j b d, request i = some b → request j = some d → i = j) :
    ∃ (f : E → Bool) (p q : I → Bool),
      (∀ i (v : Fin (shape i).vertices), let w := pos ⟨i,v⟩
        coloredDegree D f w false + (shape i).portDegree (p i) (q i) v.val false =
        coloredDegree D f w true + (shape i).portDegree (p i) (q i) v.val true) ∧
      (∀ i b, request i = some b → p i = b) := by
  classical
  have de := even_pieces_of_regular shape pos D regular
  by_cases has : ∃ z : DirectEdges shape × Bool, request z.1.val = some z.2
  · obtain ⟨⟨j,d⟩,hj⟩ := has
    obtain ⟨f,p,q,h,hm⟩ := partition_pieces shape pos D conn regular de badEven (some (j,d))
    refine ⟨f,p,q,h,?_⟩
    intro i b hi
    obtain rfl := unique _ _ _ _ hi hj
    have eq := Option.some.inj (hi.symm.trans hj)
    exact (hm j d rfl).trans eq.symm
  · obtain ⟨f,p,q,h,_⟩ := partition_pieces shape pos D conn regular de badEven none
    exact ⟨f,p,q,h,fun i b hi => False.elim (has ⟨(⟨i,isDirect i b hi⟩,b),hi⟩)⟩

theorem partition_atlas [DecidableEq C] (shape : I → Shape) (pos : (Σ i, Fin (shape i).vertices) ≃ V)
    (D : Family V E) (group : I → C) (home : V → C)
    (wi : ∀ i v, home (pos ⟨i,v⟩) = group i) (we : ∀ e, home (D.left e) = home (D.right e))
    (conn : ∀ c v w, Relation.ReflTransGen (Joined (fiber D home we c)) v w)
    (regular : ∀ i (v : Fin (shape i).vertices), coloredDegree D (fun _ => true) (pos ⟨i,v⟩) true +
      oldDegree (shape i) v.val = 4)
    (badEven : ∀ c, Even (∑ i : {i // group i = c}, (if unmarkedBad (shape i.val) then 1 else 0 : ℕ)))
    (request : I → Option Bool) (isDirect : ∀ i b, request i = some b → direct (shape i) = true)
    (unique : ∀ i j b d, group i = group j → request i = some b → request j = some d → i = j) :
    ∃ (f : E → Bool) (p q : I → Bool),
      (∀ i (v : Fin (shape i).vertices), let w := pos ⟨i,v⟩
        coloredDegree D f w false + (shape i).portDegree (p i) (q i) v.val false =
        coloredDegree D f w true + (shape i).portDegree (p i) (q i) v.val true) ∧
      (∀ i b, request i = some b → p i = b) := by
  classical
  let sc (c : C) (i : {i // group i = c}) := shape i.val
  let pc := fiberPositions shape pos group home wi
  have each (c : C) := by
    apply partition_marked (sc c) (pc c) (fiber D home we c) (conn c) _ (badEven c)
      (fun i => request i.val) (fun i b h => isDirect i.val b h)
    · intro i j b d hi hj
      exact Subtype.ext (unique _ _ _ _ (i.property.trans j.property.symm) hi hj)
    · intro i v
      have e := degree_at_component D home we (fun _ _ => true) ((wi i.val v).trans i.property) true
      exact (congrArg (· + oldDegree (shape i.val) v.val) e).trans (regular i.val v)
  choose f p q bal hm using each
  let first (i : I) := p (group i) ⟨i,rfl⟩
  let second (i : I) := q (group i) ⟨i,rfl⟩
  refine ⟨assemble D home f,first,second,?_,fun i b h => hm (group i) ⟨i,rfl⟩ b h⟩
  intro i v
  have h := bal (group i) ⟨i,rfl⟩ v
  have deg (b : Bool) := degree_at_component D home we f (wi i v) b
  change coloredDegree (fiber D home we (group i)) (f _) ⟨pos ⟨i,v⟩,wi i v⟩ false + _ =
    coloredDegree (fiber D home we (group i)) (f _) ⟨pos ⟨i,v⟩,wi i v⟩ true + _ at h
  rw [deg false,deg true] at h
  exact h

end Kostochka.FiveRegular.Auxiliary

end

section 

namespace Kostochka.FiveRegular.Auxiliary
open Finset Restoration
variable {I V C : Type*}

noncomputable def rowPositions (shape : I → Shape) (row : I → List V)
    (length : ∀ i, (shape i).vertices = (row i).length)
    (nodup : ∀ i, (row i).Nodup) (cover : ∀ v, ∃ i, v ∈ row i)
    (owner : ∀ i j v, v ∈ row i → v ∈ row j → i = j) :
    (Σ i, Fin (shape i).vertices) ≃ V := by
  let read (x : Σ i, Fin (shape i).vertices) := (row x.1).get (Fin.cast (length x.1) x.2)
  apply Equiv.ofBijective read
  constructor
  · rintro ⟨i,k⟩ ⟨j,l⟩ eq
    have hi := (row i).get_mem (Fin.cast (length i) k)
    have hj := (row j).get_mem (Fin.cast (length j) l)
    have he : (row i).get (Fin.cast (length i) k) = (row j).get (Fin.cast (length j) l) := eq
    have same : i = j := owner i j _ hi (he.symm ▸ hj)
    subst j
    apply congrArg (Sigma.mk i)
    apply Fin.ext
    exact ((nodup i).getElem_inj_iff).mp he
  · intro v
    obtain ⟨i,hi⟩ := cover v
    obtain ⟨k,hk⟩ := List.mem_iff_get.mp hi
    exact ⟨⟨i,Fin.cast (length i).symm k⟩,hk⟩

theorem sum_selected {Z : Type*} (items : List Z) (chosen : Z → Bool) :
    (∑ i : Fin items.length, if chosen (items.get i) then 1 else 0 : ℕ) = (items.filter chosen).length := by
  induction items with
  | nil => simp
  | cons x xs ih =>
    change (∑ i : Fin (xs.length+1), if chosen ((x :: xs).get i) then 1 else 0 : ℕ) = _
    rw [Fin.sum_univ_succ]
    change (if chosen x then 1 else 0) + (∑ i, if chosen (xs.get i) then 1 else 0) = _
    rw [ih]
    cases h : chosen x <;> simp [h, Nat.add_comm]

theorem selected_in_group {Z : Type*} [DecidableEq C] (items : List Z) (group : Z → C)
    (c : C) (chosen : Z → Bool) :
    (∑ i : {i : Fin items.length // group (items.get i) = c}, (if chosen (items.get i.val) then 1 else 0 : ℕ)) =
    (items.filter (fun z => chosen z && decide (group z = c))).length := by
  classical
  rw [← sum_selected]
  rw [← Finset.sum_subtype (s := univ.filter (fun i : Fin items.length => group (items.get i) = c))
       (fun i => by simp) (fun i => if chosen (items.get i) then 1 else 0)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : group items[i.val] = c <;> simp [h]

theorem unique_selected {Z : Type*} (items : List Z) (chosen : Z → Bool)
    (bound : (items.filter chosen).length ≤ 1) (i j : Fin items.length)
    (hi : chosen (items.get i) = true) (hj : chosen (items.get j) = true) : i = j := by
  classical
  let S := univ.filter (fun k : Fin items.length => chosen (items.get k) = true)
  have card : S.card = (items.filter chosen).length := by
    rw [← sum_selected]
    simp [S]
  exact Finset.card_le_one.mp (card ▸ bound) i (mem_filter.mpr ⟨mem_univ _,hi⟩) j (mem_filter.mpr ⟨mem_univ _,hj⟩)

end Kostochka.FiveRegular.Auxiliary

end

section 

namespace MultFive.Multi
open Finset SimpleGraph Kostochka.FiveRegular Subdivision
variable {V : Type*} (m : Multi V)

noncomputable def incidentEquiv (v : V) : (Σ w : V, Fin (m.count v w)) ≃ {e : m.Edge // v ∈ e.1} := by
  classical
  let pack (q : Σ w : V, Fin (m.count v w)) : {e : m.Edge // v ∈ e.1} :=
    ⟨⟨s(v,q.1),q.2⟩,Sym2.mem_mk_left _ _⟩
  apply Equiv.ofBijective pack
  constructor
  · rintro ⟨a,i⟩ ⟨b,j⟩ eqn
    have hp : s(v,a) = s(v,b) := congrArg (fun h : {e : m.Edge // v ∈ e.1} => h.val.1) eqn
    have hab : a = b := by rcases Sym2.eq_iff.mp hp with h | h <;> grind
    subst b
    have hi : i.val = j.val := congrArg (fun h : {e : m.Edge // v ∈ e.1} => h.val.2.val) eqn
    exact congrArg (Sigma.mk a) (Fin.ext hi)
  · rintro ⟨⟨p,i⟩,vp⟩
    obtain ⟨w,rfl⟩ := Sym2.mem_iff_exists.mp vp
    exact ⟨⟨w,i⟩,rfl⟩

theorem card_incident_labels [Fintype V] [DecidableEq V] (v : V) :
    Fintype.card {e : m.Edge // v ∈ e.1} = m.degree v := by
  rw [← Fintype.card_congr (m.incidentEquiv v), Fintype.card_sigma]
  simp [degree]

theorem family_degree [Fintype V] [DecidableEq V] (v : V) :
    coloredDegree m.family (fun _ => true) v true = m.degree v := by
  classical
  rw [← m.card_incident_labels, Fintype.card_subtype]
  have row : (∑ e : m.Edge, if v ∈ e.1 then 1 else 0 : ℕ) = (univ.filter (fun e : m.Edge => v ∈ e.1)).card := by simp
  rw [← row]
  simp only [coloredDegree, and_true, ← sum_add_distrib]
  apply sum_congr rfl
  intro e _
  have hne := m.family_loopless e
  have iffinc := m.family_incident_iff v e
  change (v = m.family.left e ∨ v = m.family.right e) ↔ _ at iffinc
  split_ifs <;> grind

theorem joined_iff (v w : V) : Joined m.family v w ↔ 0 < m.count v w := by
  constructor
  · rintro ⟨e,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
    · have h : 0 < m.copies e.1 := Nat.zero_lt_of_lt e.2.isLt
      rwa [← m.family_pair e] at h
    · have h : 0 < m.copies e.1 := Nat.zero_lt_of_lt e.2.isLt
      rw [← m.family_pair e] at h
      exact (m.symm _ _ ▸ (show 0 < m.count (m.family.left e) (m.family.right e) from h))
  · intro hp
    let e : m.Edge := ⟨s(v,w),⟨0,hp⟩⟩
    refine ⟨e,?_⟩
    obtain ⟨hl, hr⟩ | ⟨hr,hl⟩ := Sym2.eq_iff.mp (m.family_pair e)
    · exact Or.inl ⟨hl.symm, hr.symm⟩
    · exact Or.inr ⟨hr.symm, hl.symm⟩

end MultFive.Multi

end

section 

namespace MultFive.Multi
open Finset SimpleGraph Kostochka.FiveRegular Subdivision Auxiliary
variable {V : Type*} (m : Multi V) (side : V → Bool)

def crossMulti : Multi V where
  count v w := if side v ≠ side w then m.count v w else 0
  symm v w := by by_cases h : side v = side w <;> simp [h,Ne.symm,m.symm v w]
  loopless v := by simp

theorem cross_support (u v : V) : (m.crossMulti side).support.Adj u v ↔ (crossGraph m.support side).Adj u v := by
  change 0 < (if side u ≠ side v then m.count u v else 0) ↔ 0 < m.count u v ∧ side u ≠ side v
  by_cases h : side u = side v <;> simp [h]

theorem degree_cross_add_inside [Fintype V] (v : V) :
    (m.crossMulti side).degree v + m.insideDegree side v = m.degree v := by
  unfold degree insideDegree crossMulti
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro w _
  by_cases eq : side v = side w <;> simp [eq,Ne.symm]

noncomputable def crossLabelEquiv :
    (m.crossMulti side).Edge ≃ {e : m.Edge // side (m.family.left e) ≠ side (m.family.right e)} := by
  classical
  have pair (p : Sym2 V) : (m.crossMulti side).copies p =
    if side p.out.1 ≠ side p.out.2 then m.copies p else 0 := by
    have hx : s(p.out.1,p.out.2) = p := p.out_eq
    have lhs : (m.crossMulti side).copies p = (m.crossMulti side).count p.out.1 p.out.2 :=
      congrArg (m.crossMulti side).copies hx.symm
    have rhs : m.copies p = m.count p.out.1 p.out.2 := congrArg m.copies hx.symm
    rw [lhs,rhs]
    rfl
  have cross (e : (m.crossMulti side).Edge) : side e.1.out.1 ≠ side e.1.out.2 := by
    intro he
    have h : 0 < (m.crossMulti side).copies e.1 := Nat.zero_lt_of_lt e.2.isLt
    rw [pair,if_neg (not_not_intro he)] at h
    omega
  let pack (e : (m.crossMulti side).Edge) : {e : m.Edge // side (m.family.left e) ≠ side (m.family.right e)} :=
    ⟨⟨e.1,⟨e.2.val,by
      have hc := (pair e.1).trans (if_pos (cross e))
      exact lt_of_lt_of_eq e.2.isLt hc⟩⟩,cross e⟩
  let unpack (e : {e : m.Edge // side (m.family.left e) ≠ side (m.family.right e)}) : (m.crossMulti side).Edge :=
    ⟨e.val.1,⟨e.val.2.val,by
      have hp : side e.val.1.out.1 ≠ side e.val.1.out.2 := e.property
      exact lt_of_lt_of_eq e.val.2.isLt ((pair e.val.1).trans (if_pos hp)).symm⟩⟩
  exact ⟨pack,unpack,fun _ => rfl,fun _ => rfl⟩

theorem crossLabelEquiv_pair (e : (m.crossMulti side).Edge) :
    ((m.crossLabelEquiv side) e).val.1 = e.1 := rfl

theorem cross_ends (e : (m.crossMulti side).Edge) :
    m.support.connectedComponentMk ((m.crossMulti side).family.left e) =
    m.support.connectedComponentMk ((m.crossMulti side).family.right e) := by
  apply SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
  exact ((m.cross_support side _ _).mp (((m.crossMulti side).joined_iff _ _).mp ⟨e,Or.inl ⟨rfl,rfl⟩⟩)).1

private theorem lift_chain {E C : Type*} (D : Family V E) (home : V → C)
    (we : ∀ e, home (D.left e) = home (D.right e)) {c u v} (hu : home u = c)
    (chain : Relation.ReflTransGen (Joined D) u v) : ∀ hv : home v = c,
    Relation.ReflTransGen (Joined (fiber D home we c)) ⟨u,hu⟩ ⟨v,hv⟩ := by
  induction chain with
  | refl => intro; exact .refl
  | @tail w x _ step ih =>
    intro hx
    rcases step with ⟨e,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
    · have hw := (we e).trans hx
      exact (ih hw).tail ⟨⟨e,hw⟩,Or.inl ⟨rfl,rfl⟩⟩
    · have hw := (we e).symm.trans hx
      exact (ih hw).tail ⟨⟨e,hx⟩,Or.inr ⟨rfl,rfl⟩⟩

theorem cross_fiber_connected
    (maxcut : ∀ u v, 0 < m.count u v → (crossGraph m.support side).Reachable u v)
    (c : m.support.ConnectedComponent) :
    ∀ u v, Relation.ReflTransGen (Joined (fiber (m.crossMulti side).family m.support.connectedComponentMk
        (m.cross_ends side) c)) u v := by
  rintro ⟨u,hu⟩ ⟨v,hv⟩
  have reachable : m.support.Reachable u v := SimpleGraph.ConnectedComponent.exact (hu.trans hv.symm)
  have reachCross {a b : V} (h : Relation.ReflTransGen m.support.Adj a b) : (crossGraph m.support side).Reachable a b := by
    induction h with
    | refl => exact SimpleGraph.Reachable.refl _
    | tail _ e ih => exact ih.trans (maxcut _ _ e)
  have cross := reachCross ((m.support.reachable_iff_reflTransGen u v).mp reachable)
  apply lift_chain _ _ (m.cross_ends side) hu _ hv
  apply Relation.ReflTransGen.mono (fun _ _ h => ((m.crossMulti side).joined_iff _ _).mpr ((m.cross_support side _ _).mpr h))
  exact ((crossGraph m.support side).reachable_iff_reflTransGen u v).mp cross

end MultFive.Multi

end

section 

namespace Kostochka.FiveRegular.Restoration.Atlas
open Finset Subdivision Auxiliary

variable {I V E X K C : Type*} [Fintype I] [Fintype E] [Fintype X] [Fintype K] [DecidableEq V]
variable {D : Family V E} (A : Atlas D I X K)

def markedShape : Shape → Bool
  | .markedOdd _ | .markedPath => true
  | _ => false

theorem marked_direct (s : Shape) (h : markedShape s = true) : direct s = true := by
  cases s <;> simp_all [markedShape,direct]

theorem residualIncidence (i : I) (v : Fin (A.shape i).vertices) :
    coloredDegree D (fun e => !(A.oldMatching e)) (A.places ⟨i,v⟩) true =
      coloredDegree A.outside (fun _ => true) (A.places ⟨i,v⟩) true + oldDegree (A.shape i) v.val := by
  rw [A.splitDegree]
  have small (s : Shape) (j : ℕ) : (!priorLocal s j) = decide (s ≠ .alternatingSquare ∨ j % 2 = 0) := by
    by_cases hs : s = .alternatingSquare <;> by_cases parity : j % 2 = 0 <;> simp [priorLocal,hs,parity]
    omega
  simp only [oldMatching,Equiv.symm_apply_apply,Bool.not_false,Bool.not_true]
  have zero : coloredDegree A.untouched (fun _ => false) (A.places ⟨i,v⟩) true = 0 := by
    simp [coloredDegree]
  rw [zero,add_zero]
  unfold localLabel
  simp only [Equiv.symm_apply_apply]
  apply congrArg (fun z => coloredDegree A.outside (fun _ => true) (A.places ⟨i,v⟩) true + z)
  rw [Shape.coloredDegree_family _ (fun j => !priorLocal (A.shape i) j) v]
  unfold oldDegree
  apply congrArg (fun sel => (A.shape i).inc sel v.val)
  funext j
  exact small _ _

theorem outside_regular (total : ∀ w, coloredDegree D (fun _ => true) w true = 5)
    (matchDegree : ∀ w, coloredDegree D A.oldMatching w true = 1)
    (i : I) (v : Fin (A.shape i).vertices) :
    coloredDegree A.outside (fun _ => true) (A.places ⟨i,v⟩) true + oldDegree (A.shape i) v.val = 4 := by
  rw [← A.residualIncidence]
  have a := degree_split D A.oldMatching (A.places ⟨i,v⟩)
  rw [total,matchDegree] at a
  have flip : coloredDegree D (fun e => !A.oldMatching e) (A.places ⟨i,v⟩) true =
      coloredDegree D A.oldMatching (A.places ⟨i,v⟩) false := by simp [coloredDegree]
  omega

structure PartitionColors (A : Atlas D I X K) (side : V → Bool) where
  exterior : X → Bool
  first : I → Bool
  second : I → Bool
  balanced : ∀ i (v : Fin (A.shape i).vertices),
    coloredDegree A.outside exterior (A.places ⟨i,v⟩) false + (A.shape i).portDegree (first i) (second i) v.val false =
    coloredDegree A.outside exterior (A.places ⟨i,v⟩) true + (A.shape i).portDegree (first i) (second i) v.val true
  normalized : ∀ i, markedShape (A.shape i) = true → first i = !(side (A.places ⟨i,vertexAt (A.shape i) 0⟩))

theorem exists_partitionColors [Fintype V] [DecidableEq X] [DecidableEq I] [DecidableEq C]
    (side : V → Bool) (group : I → C) (home : V → C) (wi : ∀ i v, home (A.places ⟨i,v⟩) = group i)
    (we : ∀ e, home (A.outside.left e) = home (A.outside.right e))
    (conn : ∀ c v w, Relation.ReflTransGen (Joined (fiber A.outside home we c)) v w)
    (total : ∀ w, coloredDegree D (fun _ => true) w true = 5)
    (matchDegree : ∀ w, coloredDegree D A.oldMatching w true = 1)
    (badEven : ∀ c, Even (∑ i : {i // group i = c}, (if unmarkedBad (A.shape i.val) then 1 else 0 : ℕ)))
    (unique : ∀ i j, group i = group j → markedShape (A.shape i) = true → markedShape (A.shape j) = true → i = j) :
    Nonempty (PartitionColors A side) := by
  classical
  let request (i : I) := if markedShape (A.shape i) then some (!(side (A.places ⟨i,vertexAt (A.shape i) 0⟩))) else none
  have marked (i b) (h : request i = some b) : markedShape (A.shape i) = true := by
    by_contra hm
    simp [request,hm] at h
  obtain ⟨f,p,q,h,hn⟩ := partition_atlas A.shape A.places A.outside group home wi we conn
    (A.outside_regular total matchDegree) badEven request (fun i b hb => marked_direct _ (marked i b hb))
    (fun i j b d same hi hj => unique i j same (marked i b hi) (marked j d hj))
  exact ⟨⟨f,p,q,h,fun i hi => hn i _ (by simp [request,hi])⟩⟩

end Kostochka.FiveRegular.Restoration.Atlas

end

section 

namespace MultFive.Multi
open SimpleGraph Kostochka.FiveRegular Auxiliary Restoration
variable {V : Type*} [Fintype V] [DecidableEq V] {m : Multi V} {M : m.support.Subgraph} {side : V → Bool}

namespace ResidualPiece

def baseShape : ResidualPiece m M side → Shape
  | .isolated _ _ => .isolated
  | .twoBadQuad _ => .alternatingSquare
  | .badPath _ true => .markedPath
  | .badPath _ false => .badPath
  | .ordinaryPath p => .path (p.vertsList.length-2)
  | .badOddCycle c true => .markedOdd (c.t-1)
  | .badOddCycle c false => .badOdd (c.t-1)
  | .zeroBadSquare _ => .evenCycle 1
  | .evenCycle c => .evenCycle (c.t-1)
  | .doubledEdge _ => .evenCycle 0

omit [DecidableEq V] in
theorem baseShape_size (P : ResidualPiece m M side) : P.baseShape.vertices = P.vertsList.length := by
  cases P with
  | isolated | twoBadQuad | zeroBadSquare | doubledEdge => rfl
  | badPath p b => cases b <;> rfl
  | ordinaryPath p => have := p.hlen; change p.vertsList.length-2+1+1 = p.vertsList.length; omega
  | badOddCycle c b =>
    have := c.ht
    cases b <;> change 2*(c.t-1)+3 = c.vertsList.length <;> rw [c.hlen] <;> omega
  | evenCycle c =>
    have := c.ht
    change 2*(c.t-1+1) = c.vertsList.length
    rw [c.hlen]; omega

omit [DecidableEq V] in
theorem baseShape_mark (P : ResidualPiece m M side) : Atlas.markedShape P.baseShape = P.isMarked := by
  cases P <;> try rfl
  all_goals rename_i b; cases b <;> rfl

omit [DecidableEq V] in
theorem baseShape_bad (P : ResidualPiece m M side) : unmarkedBad P.baseShape = P.isUnmarkedBad := by
  cases P <;> try rfl
  all_goals rename_i b; cases b <;> rfl

end ResidualPiece

namespace PieceDecomposition
variable (D : PieceDecomposition m M side)
abbrev Index := Fin D.pieces.length
def raw (i : D.Index) := D.pieces.get i
def rawShape (i : D.Index) := (D.raw i).baseShape
noncomputable def group (i : D.Index) := (m.residual M).support.connectedComponentMk (D.raw i).rep

private theorem disjoint_index {i j : D.Index} (ne : i ≠ j) : Disjoint (D.raw i).verts (D.raw j).verts := by
  have forward {a b : D.Index} (lt : a.val < b.val) : Disjoint (D.raw a).verts (D.raw b).verts :=
    List.pairwise_iff_getElem.mp (List.pairwise_map.mp D.disjoint) a.val b.val a.isLt b.isLt lt
  rcases lt_or_gt_of_ne ne with lt | gt
  · exact forward lt
  · exact (forward gt).symm

noncomputable def positions : (Σ i : D.Index, Fin (D.rawShape i).vertices) ≃ V :=
  rowPositions D.rawShape (fun i => (D.raw i).vertsList) (fun i => (D.raw i).baseShape_size)
    (fun i => (D.raw i).vertsList_nodup)
    (fun v => by
      obtain ⟨P,hP,hv⟩ := D.cover_verts v
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp hP
      exact ⟨i,by change v ∈ (D.pieces.get i).vertsList; rw [hi]; exact List.mem_toFinset.mp hv⟩)
    (fun i j v hi hj => by
      by_contra ne
      exact Finset.disjoint_left.mp (D.disjoint_index ne)
        (List.mem_toFinset.mpr hi) (List.mem_toFinset.mpr hj))

theorem position_formula (i : D.Index) (v : Fin (D.rawShape i).vertices) :
    D.positions ⟨i,v⟩ = (D.raw i).vertsList.get (Fin.cast (D.raw i).baseShape_size v) := rfl

theorem position_mem (i : D.Index) (v : Fin (D.rawShape i).vertices) :
    D.positions ⟨i,v⟩ ∈ (D.raw i).verts :=
  List.mem_toFinset.mpr ((D.raw i).vertsList.get_mem _)

theorem position_home (i : D.Index) (v : Fin (D.rawShape i).vertices) :
    (m.residual M).support.connectedComponentMk (D.positions ⟨i,v⟩) = D.group i := by
  classical
  apply ConnectedComponent.sound
  have hu := D.position_mem i v
  have hw := (D.raw i).rep_mem_verts
  by_cases quad : ∃ q, D.raw i = .twoBadQuad q
  · obtain ⟨q,eq⟩ := quad
    have verts : (ResidualPiece.twoBadQuad q).verts = q.verts := by
      ext x
      simp [ResidualPiece.verts, ResidualPiece.vertsList, TwoBadQuad.vertsList, TwoBadQuad.verts]
    rw [eq,verts] at hu
    rw [eq,verts] at hw
    change (m.residual M).support.Reachable _ (D.raw i).rep
    rw [eq]
    exact q.all_reachable hu hw
  · have small : ((m.residual M).monoMulti side).support ≤ (m.residual M).support := by
      intro x y e
      change 0 < ((m.residual M).monoMulti side).count x y at e
      rw [monoMulti_count] at e
      split at e
      · exact e
      · omega
    apply SimpleGraph.Reachable.mono small
    apply piece_reachable_in_resMono (P := D.raw i) (fun q h => quad ⟨q,h⟩) _ hu hw
    intro x hx y
    exact D.edgeMult_eq_of_mem (List.get_mem D.pieces i) hx y

theorem position_side (i : D.Index) (v : Fin (D.rawShape i).vertices) :
    side (D.positions ⟨i,v⟩) = (D.raw i).sideOf := (D.raw i).side_of_mem (D.position_mem i v)

theorem bad_parity (c : (m.residual M).support.ConnectedComponent) [DecidableEq (m.residual M).support.ConnectedComponent] :
    Even (∑ i : {i // D.group i = c}, (if unmarkedBad (D.rawShape i.val) then 1 else 0 : ℕ)) := by
  classical
  induction c using ConnectedComponent.ind with
  | h r =>
    let home (P : ResidualPiece m M side) := (m.residual M).support.connectedComponentMk P.rep
    have e := selected_in_group D.pieces home ((m.residual M).support.connectedComponentMk r) ResidualPiece.isUnmarkedBad
    simp only [rawShape,ResidualPiece.baseShape_bad]
    rw [show (∑ i : {i // D.group i = (m.residual M).support.connectedComponentMk r},
        (if (D.raw i.val).isUnmarkedBad then 1 else 0 : ℕ)) = _ from e]
    have pred (P : ResidualPiece m M side) :
        (home P = (m.residual M).support.connectedComponentMk r) ↔ (m.residual M).support.Reachable r P.rep :=
      ⟨fun eq => ConnectedComponent.exact eq.symm,fun hr => (ConnectedComponent.sound hr).symm⟩
    simp_rw [pred]
    exact D.even_unmarked_bad_per_comp r

theorem mark_unique (i j : D.Index) (c : D.group i = D.group j)
    (mi : Atlas.markedShape (D.rawShape i) = true) (mj : Atlas.markedShape (D.rawShape j) = true) : i = j := by
  classical
  let r := (D.raw i).rep
  let chosen (P : ResidualPiece m M side) := P.isMarked && decide ((m.residual M).support.Reachable r P.rep)
  have h := D.at_most_one_marked_per_comp r
  apply unique_selected D.pieces chosen h i j
  · have hm := ((D.raw i).baseShape_mark).symm.trans mi
    simp only [chosen,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨hm,SimpleGraph.Reachable.refl _⟩
  · have hm := ((D.raw j).baseShape_mark).symm.trans mj
    simp only [chosen,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨hm,ConnectedComponent.exact c⟩

end PieceDecomposition
end MultFive.Multi

end

section 

namespace Kostochka.FiveRegular.Restoration.Atlas
open Subdivision

variable {V E I X : Type*} {D : Family V E}

def Leftover {S : Type*} (external : X ↪ E) (localEdges : S ↪ E) :=
  {e : E // (∀ x, external x ≠ e) ∧ ∀ s, localEdges s ≠ e}

private def labelMap {S : Type*} (ex : X ↪ E) (le : S ↪ E) :
    X ⊕ (Leftover ex le ⊕ S) → E
  | .inl x => ex x
  | .inr (.inl k) => k.val
  | .inr (.inr s) => le s

private theorem labelMap_bijective {S : Type*} (ex : X ↪ E) (le : S ↪ E)
    (disjoint : ∀ x t, ex x ≠ le t) : Function.Bijective (labelMap ex le) := by
  classical
  constructor
  · rintro (x | k | s) (y | j | t) h
    · exact congrArg Sum.inl (ex.injective h)
    · exact (j.property.1 x h).elim
    · exact (disjoint x t h).elim
    · exact (k.property.1 y h.symm).elim
    · exact congrArg _ (congrArg Sum.inl (Subtype.ext h))
    · exact (k.property.2 t h.symm).elim
    · exact (disjoint y s h.symm).elim
    · exact (j.property.2 s h).elim
    · exact congrArg _ (congrArg Sum.inr (le.injective h))
  · intro e
    by_cases hx : ∃ x, ex x = e
    · obtain ⟨x,h⟩ := hx; exact ⟨.inl x,h⟩
    by_cases hl : ∃ s, le s = e
    · obtain ⟨s,h⟩ := hl; exact ⟨.inr (.inr s),h⟩
    exact ⟨.inr (.inl ⟨e,not_exists.mp hx,not_exists.mp hl⟩),rfl⟩

noncomputable def ofEmbeddings (shape : I → Shape) (place : (Σ i, Fin (shape i).vertices) ≃ V)
    (ex : X ↪ E) (le : (Σ i, Fin (shape i).edges) ↪ E) (disjoint : ∀ x t, ex x ≠ le t)
    (agree : ∀ i (e : Fin (shape i).edges),
      s(D.left (le ⟨i,e⟩),D.right (le ⟨i,e⟩)) =
      s(place ⟨i,(shape i).family.left e⟩,place ⟨i,(shape i).family.right e⟩)) :
    Atlas D I X (Leftover ex le) where
  shape := shape
  places := place
  labels := Equiv.ofBijective (labelMap ex le) (labelMap_bijective ex le disjoint)
  endpoints := agree

theorem oldMatching_ofEmbeddings (shape : I → Shape) (place : (Σ i, Fin (shape i).vertices) ≃ V)
    (ex : X ↪ E) (le : (Σ i, Fin (shape i).edges) ↪ E) (disjoint : ∀ x t, ex x ≠ le t)
    (agree : ∀ i (e : Fin (shape i).edges), s(D.left (le ⟨i,e⟩),D.right (le ⟨i,e⟩)) =
      s(place ⟨i,(shape i).family.left e⟩,place ⟨i,(shape i).family.right e⟩))
    (matched : E → Prop) (exFree : ∀ x, ¬ matched (ex x))
    (tagged : ∀ i (e : Fin (shape i).edges), priorLocal (shape i) e.val = true ↔ matched (le ⟨i,e⟩))
    (cover : ∀ e, ¬matched e → (∃ x, ex x = e) ∨ ∃ s, le s = e)
    (e : E) : (ofEmbeddings shape place ex le disjoint agree).oldMatching e = true ↔ matched e := by
  classical
  let A := ofEmbeddings shape place ex le disjoint agree
  change A.oldMatching e = true ↔ matched e
  obtain ⟨u,rfl⟩ := A.labels.surjective e
  rw [oldMatching,A.labels.symm_apply_apply]
  rcases u with x | k | ⟨i,j⟩
  · exact ⟨fun h => by contradiction,fun h => (exFree x h).elim⟩
  · refine ⟨fun _ => ?_,fun _ => rfl⟩
    by_contra h
    rcases cover k.val h with ⟨x,hx⟩ | ⟨s,hs⟩
    · exact k.property.1 x hx
    · exact k.property.2 s hs
  · exact tagged i j

end Kostochka.FiveRegular.Restoration.Atlas

end

section 

namespace Kostochka.FiveRegular.Restoration
open Subdivision Auxiliary

def residueIndex (s : Shape) (e : Fin s.edges) (old : Atlas.priorLocal s e.val = false) :
    Fin (residualCount s) := by
  by_cases sq : s = .alternatingSquare
  · subst s
    exact ⟨e.val/2,by have k : e.val < 4 := e.isLt; change e.val/2 < 2; omega⟩
  · exact ⟨e.val,by simp [residualCount,sq]⟩

theorem residueIndex_surjective (s : Shape) (j : Fin (residualCount s)) :
    ∃ (e : Fin s.edges) (hn : Atlas.priorLocal s e = false), residueIndex s e hn = j := by
  by_cases sq : s = .alternatingSquare
  · subst s
    change Fin 2 at j
    fin_cases j
    · exact ⟨⟨0,by decide⟩,rfl,rfl⟩
    · exact ⟨⟨2,by decide⟩,rfl,rfl⟩
  · have l : j.val < s.edges := by simpa [residualCount,sq] using j.isLt
    exact ⟨⟨j.val,l⟩,by simp [Atlas.priorLocal,sq],by apply Fin.ext; simp [residueIndex,sq]⟩

theorem residueIndex_injective (s : Shape) {e k : Fin s.edges} (he : Atlas.priorLocal s e.val = false)
    (hk : Atlas.priorLocal s k.val = false) (eq : residueIndex s e he = residueIndex s k hk) : e = k := by
  apply Fin.ext
  have vals := congrArg Fin.val eq
  by_cases sq : s = .alternatingSquare
  · subst s
    have heven : e.val % 2 ≠ 1 := by simpa [Atlas.priorLocal] using he
    have keven : k.val % 2 ≠ 1 := by simpa [Atlas.priorLocal] using hk
    have same : e.val / 2 = k.val / 2 := by simpa [residueIndex] using vals
    omega
  · simpa [residueIndex,sq] using vals

theorem square_old_distinct (e k : Fin Shape.alternatingSquare.edges)
    (h : s(Shape.alternatingSquare.family.left e, Shape.alternatingSquare.family.right e) =
         s(Shape.alternatingSquare.family.left k, Shape.alternatingSquare.family.right k)) : e = k := by
  revert e k
  change ∀ (e k : Fin 4), _ → e = k
  decide

theorem right_index (s : Shape) (e : Fin s.edges) :
    (s.family.right e).val = (e.val + 1) % s.vertices := by
  have le : e.val + 1 ≤ s.vertices := le_trans e.isLt s.edges_le_vertices
  by_cases h : e.val + 1 < s.vertices
  · simp [Shape.family,h,Nat.mod_eq_of_lt h]
  · have eq : e.val + 1 = s.vertices := by omega
    simp [Shape.family,eq]

variable {I V : Type*} (shape : I → Shape) (places : (Σ i, Fin (shape i).vertices) ≃ V)
def gapPair (i : I) (k : Fin (shape i).edges) : Sym2 V :=
  s(places ⟨i,(shape i).family.left k⟩, places ⟨i,(shape i).family.right k⟩)

theorem oldGap_injective {a b : Σ i, Fin (shape i).edges}
    (ha : Atlas.priorLocal (shape a.1) a.2 = true)
    (eq : gapPair shape places a.1 a.2 = gapPair shape places b.1 b.2) : a = b := by
  obtain ⟨i,k⟩ := a
  obtain ⟨j,l⟩ := b
  have same : i = j := by
    rcases Sym2.eq_iff.mp eq with ⟨h,_⟩ | ⟨h,_⟩
    all_goals exact congrArg Sigma.fst (places.injective h)
  subst j
  apply congrArg (Sigma.mk i)
  have sq : shape i = .alternatingSquare := (of_decide_eq_true ha).1
  have localEq :
      s((shape i).family.left k,(shape i).family.right k) =
      s((shape i).family.left l,(shape i).family.right l) := by
    rcases Sym2.eq_iff.mp eq with ⟨h,t⟩ | ⟨h,t⟩
    · exact Sym2.eq_iff.mpr (Or.inl ⟨eq_of_heq (Sigma.ext_iff.mp (places.injective h)).2,
        eq_of_heq (Sigma.ext_iff.mp (places.injective t)).2⟩)
    · exact Sym2.eq_iff.mpr (Or.inr ⟨eq_of_heq (Sigma.ext_iff.mp (places.injective h)).2,
        eq_of_heq (Sigma.ext_iff.mp (places.injective t)).2⟩)
  have simple (s : Shape) (hs : s = .alternatingSquare) (a b : Fin s.edges) :
      s(s.family.left a,s.family.right a) = s(s.family.left b,s.family.right b) → a = b := by
    subst s
    exact square_old_distinct a b
  exact simple _ sq _ _ localEq

end Kostochka.FiveRegular.Restoration

end

section 

namespace Kostochka.FiveRegular.Restoration
open Subdivision Auxiliary
variable {I V E : Type*}
variable (shape : I → Shape) (places : (Σ i, Fin (shape i).vertices) ≃ V)

abbrev Gap := Σ i : I, Fin (shape i).edges

structure OrderedLabels (shape : I → Shape) (E : Type*) where
  residual : I → List E
  length : ∀ i, residualCount (shape i) = (residual i).length
  distinct : ∀ i, (residual i).Nodup
  old : ∀ (i : I) (e : Fin (shape i).edges), Atlas.priorLocal (shape i) e = true → E

namespace OrderedLabels
variable {shape} (L : OrderedLabels shape E)
def fromRow (i : I) (e : Fin (shape i).edges) (hn : Atlas.priorLocal (shape i) e = false) : E :=
  (L.residual i).get (Fin.cast (L.length i) (residueIndex (shape i) e hn))

def label (a : Gap shape) : E :=
  if h : Atlas.priorLocal (shape a.1) a.2 = true then L.old a.1 a.2 h
  else L.fromRow a.1 a.2 (Bool.eq_false_iff.mpr h)

theorem label_of_old (i : I) (e : Fin (shape i).edges) (h : Atlas.priorLocal (shape i) e = true) :
    L.label ⟨i,e⟩ = L.old i e h := by
  simp [label,h]

theorem label_of_residual (i : I) (e : Fin (shape i).edges) (h : Atlas.priorLocal (shape i) e = false) :
    L.label ⟨i,e⟩ = L.fromRow i e h := by
  simp [label,h]

theorem residual_represented (i : I) (e : E) (mem : e ∈ L.residual i) :
    ∃ a : Gap shape, L.label a = e := by
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp mem
  obtain ⟨k,hn,eq⟩ := residueIndex_surjective (shape i) (Fin.cast (L.length i).symm j)
  refine ⟨⟨i,k⟩,?_⟩
  rw [L.label_of_residual _ _ hn]
  unfold fromRow
  rw [eq]
  rfl

theorem tag_iff (matched : E → Prop) (oldTag : ∀ i e h, matched (L.old i e h))
    (freeTag : ∀ i e, e ∈ L.residual i → ¬matched e) (a : Gap shape) :
    Atlas.priorLocal (shape a.1) a.2 = true ↔ matched (L.label a) := by
  obtain ⟨i,e⟩ := a
  cases h : Atlas.priorLocal (shape i) e with
  | false =>
    rw [L.label_of_residual _ _ h]
    exact ⟨by simp,fun ha => False.elim (freeTag _ _ ((L.residual i).get_mem _) ha)⟩
  | true => rw [L.label_of_old _ _ h]; exact ⟨fun _ => oldTag _ _ _, fun _ => rfl⟩

theorem label_injective (matched : E → Prop) (tag : ∀ a : Gap shape, Atlas.priorLocal (shape a.1) a.2 = true ↔ matched (L.label a))
    (pair : E → Sym2 V) (agree : ∀ i e, pair (L.label ⟨i,e⟩) = gapPair shape places i e) :
    Function.Injective L.label := by
  rintro ⟨i,k⟩ ⟨j,l⟩ he
  have pairs : gapPair shape places i k = gapPair shape places j l :=
    (agree _ _).symm.trans ((congrArg pair he).trans (agree _ _))
  by_cases hi : Atlas.priorLocal (shape i) k = true
  · exact oldGap_injective shape places hi pairs
  have hj : Atlas.priorLocal (shape j) l = false :=
    Bool.eq_false_iff.mpr (fun old => hi ((tag ⟨i,k⟩).mpr ((congrArg matched he).mpr ((tag ⟨j,l⟩).mp old))))
  have same : i = j := by
    rcases Sym2.eq_iff.mp pairs with ⟨a,_⟩ | ⟨a,_⟩
    all_goals exact congrArg Sigma.fst (places.injective a)
  subst j
  have hn := Bool.eq_false_iff.mpr hi
  rw [L.label_of_residual _ _ hn,L.label_of_residual _ _ hj] at he
  have ix := (L.distinct i).get_inj_iff.mp he
  apply congrArg (Sigma.mk i)
  apply residueIndex_injective _ hn hj
  exact Fin.ext (congrArg (fun t : Fin (L.residual i).length => t.val) ix)

end OrderedLabels
end Kostochka.FiveRegular.Restoration

end

section 

namespace MultFive.Multi.ResidualPiece
open Kostochka.FiveRegular Restoration Auxiliary
variable {V : Type*} [Fintype V] [DecidableEq V] {m : Multi V} {M : m.support.Subgraph} {side : V → Bool}

def atVertex (P : ResidualPiece m M side) (v : Fin P.baseShape.vertices) : V :=
  P.vertsList.get (Fin.cast P.baseShape_size v)

def atPair (P : ResidualPiece m M side) (e : Fin P.baseShape.edges) : Sym2 V :=
  s(P.atVertex (P.baseShape.family.left e), P.atVertex (P.baseShape.family.right e))

omit [DecidableEq V] in
theorem residual_size (P : ResidualPiece m M side) : residualCount P.baseShape = P.canonicalResEdges.length := by
  rw [canonicalResEdges_length]
  cases P with
  | isolated | twoBadQuad | zeroBadSquare | doubledEdge => rfl
  | badPath p b => cases b <;> rfl
  | ordinaryPath p =>
    have := p.hlen
    change p.vertsList.length-2+1 = p.vertsList.length-1; omega
  | badOddCycle c b =>
    have := c.ht
    cases b <;> change 2*(c.t-1)+3 = c.vertsList.length <;> rw [c.hlen] <;> omega
  | evenCycle c =>
    have := c.ht
    change 2*(c.t-1+1) = c.vertsList.length
    rw [c.hlen]; omega

noncomputable def residualGap (P : ResidualPiece m M side) (e : Fin P.baseShape.edges)
    (hn : Atlas.priorLocal P.baseShape e = false) : m.Edge :=
  P.canonicalResEdges.get (Fin.cast P.residual_size (residueIndex P.baseShape e hn))

omit [DecidableEq V] in
theorem oldPair (P : ResidualPiece m M side) (e : Fin P.baseShape.edges)
    (h : Atlas.priorLocal P.baseShape e = true) : isMatchingPair M (P.atPair e) := by
  have hs : P.baseShape = .alternatingSquare := (of_decide_eq_true h).1
  cases P with
  | isolated => contradiction
  | ordinaryPath p => contradiction
  | badOddCycle c b => cases b <;> contradiction
  | evenCycle c => contradiction
  | zeroBadSquare q => contradiction
  | doubledEdge d => contradiction
  | badPath p b => cases b <;> contradiction
  | twoBadQuad q =>
    change Fin 4 at e
    fin_cases e
    · norm_num [Atlas.priorLocal,baseShape] at h
    · exact q.match23
    · norm_num [Atlas.priorLocal,baseShape] at h
    · exact q.match14.symm

noncomputable def oldGap (P : ResidualPiece m M side) (e : Fin P.baseShape.edges)
    (h : Atlas.priorLocal P.baseShape e = true) : m.Edge := ⟨P.atPair e,⟨0,copies_pos_of_isMatchingPair (P.oldPair e h)⟩⟩

omit [DecidableEq V] in

theorem atPair_get (P : ResidualPiece m M side) (e : Fin P.baseShape.edges) :
    P.atPair e = s(P.vertsList[e.val]'(lt_of_lt_of_le e.isLt (P.baseShape_size ▸ P.baseShape.edges_le_vertices)),
      P.vertsList[(e.val+1)%P.vertsList.length]'(Nat.mod_lt _ (P.baseShape_size ▸ P.baseShape.vertices_pos))) := by
  apply congrArg₂ Sym2.mk
  · rfl
  · unfold atVertex
    apply congrArg P.vertsList.get
    apply Fin.ext
    simpa only [Fin.val_cast,← P.baseShape_size] using right_index P.baseShape e

omit [DecidableEq V] in
theorem residualGap_pair (P : ResidualPiece m M side) (e : Fin P.baseShape.edges)
    (hn : Atlas.priorLocal P.baseShape e = false) : (P.residualGap e hn).1 = P.atPair e := by
  rw [atPair_get]
  cases P with
  | isolated v hz => exact Fin.elim0 e
  | twoBadQuad q =>
    change Fin 4 at e
    fin_cases e <;> first | exact resEdgeOfPos_fst .. | norm_num [Atlas.priorLocal,baseShape] at hn
  | badPath p b =>
    cases b <;> change Fin 3 at e <;> fin_cases e <;> exact resEdgeOfPos_fst ..
  | zeroBadSquare q =>
    change Fin 4 at e
    fin_cases e <;> norm_num [residualGap,baseShape,canonicalResEdges,vertsList,ZeroBadSquare.vertsList,residueIndex] <;> exact resEdgeOfPos_fst ..
  | doubledEdge d =>
    change Fin 2 at e
    fin_cases e
    · exact resEdgeOfPos_fst ..
    · norm_num [residualGap,canonicalResEdges,baseShape,vertsList,DoubledEdge.vertsList,residueIndex,Sym2.eq_swap]
      exact resEdgeOfPos_fst ..
  | ordinaryPath p =>
    have hz := p.hlen
    have en : e.val < p.vertsList.length-2+1 := e.isLt
    have lt : e.val+1 < p.vertsList.length := by omega
    simp [residualGap,canonicalResEdges,vertsList,baseShape,residueIndex,List.get_eq_getElem,Nat.mod_eq_of_lt lt]
    exact Or.inl ⟨rfl,rfl⟩
  | badOddCycle c b =>
    cases b <;> simp [residualGap,canonicalResEdges,vertsList,baseShape,residueIndex,List.get_eq_getElem] <;> exact Or.inl ⟨rfl,rfl⟩
  | evenCycle c =>
    simp [residualGap,canonicalResEdges,vertsList,baseShape,residueIndex,List.get_eq_getElem]
    exact Or.inl ⟨rfl,rfl⟩

end MultFive.Multi.ResidualPiece

end

section 

namespace MultFive.Multi.PieceDecomposition
open Finset SimpleGraph Kostochka.FiveRegular Subdivision Restoration Auxiliary
variable {V : Type*} [Fintype V] [DecidableEq V] {m : Multi V} {M : m.support.Subgraph} {side : V → Bool}
variable (D : PieceDecomposition m M side)

structure LabelCoverage (D : PieceDecomposition m M side) : Prop where
  nodup : ∀ i : D.Index, (D.raw i).canonicalResEdges.Nodup
  free : ∀ (i : D.Index) e, e ∈ (D.raw i).canonicalResEdges → ¬isMatchingEdge m M e
  complete : ∀ e, ¬isMatchingEdge m M e → side (m.family.left e) = side (m.family.right e) →
    ∃ i : D.Index, e ∈ (D.raw i).canonicalResEdges

variable (L : LabelCoverage D)
noncomputable def ordered : OrderedLabels D.rawShape m.Edge where
  residual i := (D.raw i).canonicalResEdges
  length i := (D.raw i).residual_size
  distinct := L.nodup
  old i e h := (D.raw i).oldGap e h

theorem label_tag (a : Gap D.rawShape) :
    Atlas.priorLocal (D.rawShape a.1) a.2 = true ↔ isMatchingEdge m M ((D.ordered L).label a) :=
  (D.ordered L).tag_iff (isMatchingEdge m M) (fun i e h => ⟨(D.raw i).oldPair e h,rfl⟩) L.free a

theorem label_pair (i : D.Index) (e : Fin (D.rawShape i).edges) :
    ((D.ordered L).label ⟨i,e⟩).1 = gapPair D.rawShape D.positions i e := by
  cases h : Atlas.priorLocal (D.rawShape i) e.val with
  | false =>
    rw [(D.ordered L).label_of_residual _ _ h]
    exact (D.raw i).residualGap_pair e h
  | true =>
    rw [(D.ordered L).label_of_old _ _ h]
    rfl

noncomputable def insideLabels : Gap D.rawShape ↪ m.Edge :=
  ⟨(D.ordered L).label,(D.ordered L).label_injective D.positions (isMatchingEdge m M) (D.label_tag L)
    Sigma.fst (D.label_pair L)⟩

abbrev Exterior (m : Multi V) (M : m.support.Subgraph) (side : V → Bool) :=
  ((m.residual M).crossMulti side).Edge

noncomputable def outsideLabels (m : Multi V) (M : m.support.Subgraph) (side : V → Bool) :
    Exterior m M side ↪ m.Edge :=
  (((m.residual M).crossLabelEquiv side).toEmbedding.trans (Function.Embedding.subtype _)).trans
    ((residualEdgeEquiv m M).toEmbedding.trans (Function.Embedding.subtype _))

omit [Fintype V] [DecidableEq V] in
theorem exterior_pair (x : Exterior m M side) : (outsideLabels m M side x).1 = x.1 :=
  (residualEdgeEquiv_fst _ _ _).trans ((m.residual M).crossLabelEquiv_pair side x)

omit [Fintype V] [DecidableEq V] in
theorem exterior_free (x : Exterior m M side) : ¬ isMatchingEdge m M (outsideLabels m M side x) :=
  (residualEdgeEquiv m M (((m.residual M).crossLabelEquiv side) x).val).property

omit [Fintype V] [DecidableEq V] in
theorem exterior_crosses (x : Exterior m M side) :
    side (m.family.left (outsideLabels m M side x)) ≠ side (m.family.right (outsideLabels m M side x)) := by
  have e := (((m.residual M).crossLabelEquiv side) x).property
  change side (outsideLabels m M side x).1.out.1 ≠ side (outsideLabels m M side x).1.out.2
  rw [exterior_pair]
  change side ((((m.residual M).crossLabelEquiv side) x).val.1.out.1) ≠
    side ((((m.residual M).crossLabelEquiv side) x).val.1.out.2) at e
  rwa [(m.residual M).crossLabelEquiv_pair] at e

omit [Fintype V] [DecidableEq V] in
theorem exterior_covers (e : m.Edge) (free : ¬isMatchingEdge m M e)
    (cross : side (m.family.left e) ≠ side (m.family.right e)) : ∃ x, outsideLabels m M side x = e := by
  let h := m.residual M
  let r := (residualEdgeEquiv m M).symm ⟨e,free⟩
  have er : (residualEdgeEquiv m M r).val = e := congrArg Subtype.val ((residualEdgeEquiv m M).apply_symm_apply ⟨e,free⟩)
  have pair : r.1 = e.1 := (residualEdgeEquiv_fst _ _ r).symm.trans (congrArg Sigma.fst er)
  have cr : side (h.family.left r) ≠ side (h.family.right r) := by
    change side r.1.out.1 ≠ side r.1.out.2
    rw [pair]
    exact cross
  obtain ⟨x,hx⟩ := (h.crossLabelEquiv side).surjective ⟨r,cr⟩
  refine ⟨x,?_⟩
  change (residualEdgeEquiv m M ((h.crossLabelEquiv side x).val)).val = e
  rw [hx]
  exact er

theorem interior_agrees (i : D.Index) (e : Fin (D.rawShape i).edges) :
    s(m.family.left (D.insideLabels L ⟨i,e⟩),m.family.right (D.insideLabels L ⟨i,e⟩)) =
      s(D.positions ⟨i,(D.rawShape i).family.left e⟩,D.positions ⟨i,(D.rawShape i).family.right e⟩) :=
  (m.family_pair _).trans (D.label_pair L i e)

theorem interior_same_side (i : D.Index) (e : Fin (D.rawShape i).edges) :
    side (m.family.left (D.insideLabels L ⟨i,e⟩)) = side (m.family.right (D.insideLabels L ⟨i,e⟩)) := by
  have same := (D.position_side i ((D.rawShape i).family.left e)).trans
    (D.position_side i ((D.rawShape i).family.right e)).symm
  rcases Sym2.eq_iff.mp (D.interior_agrees L i e) with ⟨a,b⟩ | ⟨a,b⟩ <;> rw [a,b] <;> first | exact same | exact same.symm

theorem apart (x : Exterior m M side) (t : Gap D.rawShape) : outsideLabels m M side x ≠ D.insideLabels L t := by
  rintro eq
  exact exterior_crosses x (eq ▸ D.interior_same_side L t.1 t.2)

noncomputable abbrev Remaining := Atlas.Leftover (outsideLabels m M side) (D.insideLabels L)

noncomputable instance remainingFintype : Fintype (D.Remaining L) := by
  classical
  unfold Remaining Atlas.Leftover
  infer_instance

noncomputable def physical : Atlas m.family D.Index (Exterior m M side) (D.Remaining L) :=
  Atlas.ofEmbeddings D.rawShape D.positions (outsideLabels m M side) (D.insideLabels L)
    (D.apart L) (D.interior_agrees L)

theorem physical_tag (e : m.Edge) : (D.physical L).oldMatching e = true ↔ isMatchingEdge m M e := by
  apply Atlas.oldMatching_ofEmbeddings D.rawShape D.positions (outsideLabels m M side) (D.insideLabels L)
    (D.apart L) (D.interior_agrees L) (isMatchingEdge m M) exterior_free (fun i j => D.label_tag L ⟨i,j⟩)
  intro g free
  by_cases same : side (m.family.left g) = side (m.family.right g)
  · obtain ⟨i,hi⟩ := L.complete g free same
    exact Or.inr ((D.ordered L).residual_represented i g hi)
  · exact Or.inl (exterior_covers g free same)

theorem physical_outside : (D.physical L).outside = ((m.residual M).crossMulti side).family := by
  apply congrArg₂ Family.mk <;> funext e
  · exact congrArg (fun p : Sym2 V => p.out.1) (exterior_pair e)
  · exact congrArg (fun p : Sym2 V => p.out.2) (exterior_pair e)

end MultFive.Multi.PieceDecomposition

end

section 

namespace Kostochka.FiveRegular.Restoration.Atlas
open Finset Subdivision Auxiliary
variable {I V E X K : Type*} [Fintype I] [Fintype E] [Fintype X] [Fintype K] [DecidableEq V]
variable {D : Family V E} (A : Atlas D I X K) {side : V → Bool} (C : PartitionColors A side)

private theorem local_total (s : Shape) (p q : Bool) (v : Fin s.vertices) :
    s.inc (fun _ => true) v.val = oldDegree s v.val + s.matchingDegree p q v.val := by
  rw [s.restoreMatching]
  by_cases eq : s = .alternatingSquare
  · subst s
    change Fin 4 at v
    fin_cases v <;> decide
  · simp [oldDegree,eq]

theorem factor_constraints
    (regular : ∀ i (v : Fin (A.shape i).vertices), coloredDegree A.outside (fun _ => true) (A.places ⟨i,v⟩) true +
      oldDegree (A.shape i) v.val = 4) (w : V) :
    let deg (b : Bool) := coloredDegree D (fun e => decide (A.part C.exterior C.first C.second e = .factor b)) w true
    let exc := coloredDegree D (fun e => decide (A.part C.exterior C.first C.second e = .exceptional)) w true
    deg false ≤ 2 ∧ deg true ≤ 2 ∧ (exc = 2 → deg false = 1 ∧ deg true = 1) := by
  obtain ⟨⟨i,v⟩,rfl⟩ := A.places.surjective w
  let outside := coloredDegree A.outside C.exterior (A.places ⟨i,v⟩)
  have d := degree_split A.outside C.exterior (A.places ⟨i,v⟩)
  have r := regular i v
  have tot := local_total (A.shape i) (C.first i) (C.second i) v
  have all : outside false + outside true + (A.shape i).inc (fun _ => true) v.val =
      4 + (A.shape i).matchingDegree (C.first i) (C.second i) v.val := by dsimp [outside]; omega
  have f := (A.shape i).restoredDegrees (C.first i) (C.second i) v outside (C.balanced i v) all
  dsimp only
  simp only [A.factorDegree,A.exceptionalDegree]
  exact ⟨f.1,f.2.1,f.2.2.1⟩

theorem endpoint_constraints
    (regular : ∀ i (v : Fin (A.shape i).vertices), coloredDegree A.outside (fun _ => true) (A.places ⟨i,v⟩) true +
      oldDegree (A.shape i) v.val = 4)
    (i : I) (bad : A.shape i = .badPath) (v : Fin (A.shape i).vertices) :
    let w := A.places ⟨i,v⟩
    let deg (b : Bool) := coloredDegree D (fun e => decide (A.part C.exterior C.first C.second e = .factor b)) w true
    (v.val = 0 → deg (C.first i) = 1 ∧ deg (!(C.first i)) = 2) ∧
    (v.val = 3 → deg (C.first i) = 2 ∧ deg (!(C.first i)) = 1) := by
  let outside := coloredDegree A.outside C.exterior (A.places ⟨i,v⟩)
  let j : Fin Shape.badPath.vertices := ⟨v.val,bad ▸ v.isLt⟩
  have ba := C.balanced i v
  have reg := regular i v
  have dj := degree_split A.outside C.exterior (A.places ⟨i,v⟩)
  change outside true + outside false = _ at dj
  have eq : outside false + Shape.badPath.portDegree (C.first i) (C.second i) j.val false =
      outside true + Shape.badPath.portDegree (C.first i) (C.second i) j.val true := by
    simpa only [← bad] using ba
  have deg : outside false + outside true + Shape.badPath.inc (fun _ => true) j.val = 4 := by
    have hj : oldDegree (A.shape i) v.val = Shape.badPath.inc (fun _ => true) j.val := by simp [bad,oldDegree,j]
    omega
  dsimp only
  simp only [A.factorDegree]
  have res := Shape.badPathEndpoints (C.first i) (C.second i) j outside eq deg
  simpa only [← bad] using res

end Kostochka.FiveRegular.Restoration.Atlas

end

section 

namespace MultFive.Multi.PieceDecomposition
open Finset SimpleGraph Kostochka.FiveRegular Subdivision Restoration Auxiliary
variable {V : Type*} [Fintype V] [DecidableEq V] {m : Multi V} {M : m.support.Subgraph} {side : V → Bool}
variable (D : PieceDecomposition m M side) (L : D.LabelCoverage)

theorem labelCoverage : D.LabelCoverage where
  nodup i := (D.raw i).canonicalResEdges_nodup
  free i _ he := ((D.raw i).canonicalResEdges_mem_props he).1
  complete e nt same := by
    have mem := (D.canonical_edges_mem_iff e).mpr ⟨nt,same⟩
    obtain ⟨labels,hl,he⟩ := List.mem_flatten.mp mem
    obtain ⟨P,hP,rfl⟩ := List.mem_map.mp hl
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hP
    exact ⟨i,by change e ∈ (D.pieces.get i).canonicalResEdges; rwa [hi]⟩

theorem physical_matchDegree (hm : M.IsPerfectMatching) (w : V) :
    coloredDegree m.family (D.physical L).oldMatching w true = 1 := by
  apply (Atlas.unique_iff_degree m.family m.family_loopless _ w).mp
  simpa only [D.physical_tag L,m.family_incident_iff] using matching_edge_unique m M hm w

theorem physical_regular (reg : ∀ w, m.degree w = 5) (hm : M.IsPerfectMatching) (i : D.Index)
    (v : Fin (D.rawShape i).vertices) :
    coloredDegree (D.physical L).outside (fun _ => true) (D.positions ⟨i,v⟩) true +
      oldDegree (D.rawShape i) v.val = 4 :=
  (D.physical L).outside_regular (fun w => (m.family_degree w).trans (reg w)) (D.physical_matchDegree L hm) i v

include L in
theorem inside_identity (reg : ∀ w, m.degree w = 5) (hm : M.IsPerfectMatching) (i : D.Index)
    (v : Fin (D.rawShape i).vertices) : oldDegree (D.rawShape i) v.val =
      (m.residual M).insideDegree side (D.positions ⟨i,v⟩) := by
  have r := D.physical_regular L reg hm i v
  rw [D.physical_outside L, family_degree] at r
  have s := (m.residual M).degree_cross_add_inside side (D.positions ⟨i,v⟩)
  rw [degree_residual_eq_four m reg M hm] at s
  omega

theorem physical_colors (reg : ∀ w, m.degree w = 5) (hm : M.IsPerfectMatching)
    (maxcut : ∀ u v, 0 < (m.residual M).count u v → (crossGraph (m.residual M).support side).Reachable u v) :
    Nonempty ((D.physical L).PartitionColors side) := by
  classical
  let h := m.residual M
  let home := h.support.connectedComponentMk
  have ends (e) : home ((D.physical L).outside.left e) = home ((D.physical L).outside.right e) := by
    rw [D.physical_outside L]
    exact h.cross_ends side e
  apply (D.physical L).exists_partitionColors side D.group home D.position_home ends _
    (fun w => (m.family_degree w).trans (reg w)) (D.physical_matchDegree L hm) (fun c => D.bad_parity c) D.mark_unique
  intro c
  generalize he : (D.physical L).outside = outside at ends ⊢
  have eq := (D.physical_outside L).symm.trans he
  subst outside
  exact h.cross_fiber_connected side maxcut c

omit [Fintype V] [DecidableEq V] in
theorem residual_adj_of_free (e : m.Edge) (free : ¬isMatchingEdge m M e) :
    0 < (m.residual M).count (m.family.left e) (m.family.right e) := by
  let r := (residualEdgeEquiv m M).symm ⟨e,free⟩
  have er : (residualEdgeEquiv m M r).val = e := congrArg Subtype.val ((residualEdgeEquiv m M).apply_symm_apply ⟨e,free⟩)
  have same := (residualEdgeEquiv_fst _ _ r).symm.trans (congrArg Sigma.fst er)
  have pos : 0 < (m.residual M).copies r.1 := Nat.zero_lt_of_lt r.2.isLt
  rw [same,← m.family_pair e] at pos
  exact pos

theorem not_both_saturated
    (cut : ∀ u v, side u ≠ side v → (m.residual M).insideDegree side u = 2 →
      (m.residual M).insideDegree side v = 2 → (m.residual M).count u v = 0)
    (e : m.Edge) (nt : (D.physical L).oldMatching e = false) (cross : side (m.family.left e) ≠ side (m.family.right e)) :
    ¬((m.residual M).insideDegree side (m.family.left e) = 2 ∧ (m.residual M).insideDegree side (m.family.right e) = 2) := by
  rintro ⟨a,b⟩
  have hn : ¬isMatchingEdge m M e := fun he => Bool.noConfusion (nt.symm.trans ((D.physical_tag L e).mpr he))
  exact (Nat.ne_of_gt (residual_adj_of_free e hn)) (cut _ _ cross a b)

end MultFive.Multi.PieceDecomposition

end

section 

namespace Kostochka.FiveRegular.Restoration

open Subdivision Auxiliary

namespace Shape

def afterSquare (s : Shape) (divert : Bool) : Shape :=
  if s = .evenCycle 1 ∧ divert = true then .divertedSquare else s

@[simp] theorem afterSquare_vertices (s : Shape) (d : Bool) : (s.afterSquare d).vertices = s.vertices := by
  unfold afterSquare; split <;> simp_all [vertices,cyclic,edges]

@[simp] theorem afterSquare_edges (s : Shape) (d : Bool) : (s.afterSquare d).edges = s.edges := by
  unfold afterSquare; split <;> simp_all [edges]

@[simp] theorem afterSquare_ports (s : Shape) (d p q b : Bool) (v : ℕ) :
    (s.afterSquare d).portDegree p q v b = s.portDegree p q v b := by
  unfold afterSquare; split <;> simp_all [portDegree]

@[simp] theorem afterSquare_marked (s : Shape) (d : Bool) :
    Atlas.markedShape (s.afterSquare d) = Atlas.markedShape s := by
  unfold afterSquare; split <;> simp_all [Atlas.markedShape]

@[simp] theorem afterSquare_prior (s : Shape) (d : Bool) (j : ℕ) :
    Atlas.priorLocal (s.afterSquare d) j = Atlas.priorLocal s j := by
  unfold afterSquare; split <;> simp_all [Atlas.priorLocal]

private theorem cast_left (s : Shape) (d : Bool) (e : Fin (s.afterSquare d).edges) :
    Fin.cast (s.afterSquare_vertices d) ((s.afterSquare d).family.left e) =
      s.family.left (Fin.cast (s.afterSquare_edges d) e) := Fin.ext rfl

private theorem cast_right (s : Shape) (d : Bool) (e : Fin (s.afterSquare d).edges) :
    Fin.cast (s.afterSquare_vertices d) ((s.afterSquare d).family.right e) =
      s.family.right (Fin.cast (s.afterSquare_edges d) e) := by
  apply Fin.ext
  by_cases h : e.val+1 < s.vertices <;> simp [family,h]

end Shape

namespace Atlas
variable {V E I X K : Type*} {D : Family V E} (A : Atlas D I X K)

private def recastLabels (d : I → Bool) :=
  Equiv.sumCongr (Equiv.refl X) (Equiv.sumCongr (Equiv.refl K) (Equiv.sigmaCongrRight
    (fun i => finCongr ((A.shape i).afterSquare_edges (d i)))))

def afterSquareDecision (d : I → Bool) : Atlas D I X K where
  shape i := (A.shape i).afterSquare (d i)
  places := (Equiv.sigmaCongrRight (fun i => finCongr ((A.shape i).afterSquare_vertices (d i)))).trans A.places
  labels := (A.recastLabels d).trans A.labels
  endpoints := by
    intro i e
    change s(D.left (A.localLabel i (Fin.cast ((A.shape i).afterSquare_edges (d i)) e)),D.right (A.localLabel i (Fin.cast ((A.shape i).afterSquare_edges (d i)) e))) =
      s(A.places ⟨i,Fin.cast ((A.shape i).afterSquare_vertices (d i)) (((A.shape i).afterSquare (d i)).family.left e)⟩,
        A.places ⟨i,Fin.cast ((A.shape i).afterSquare_vertices (d i)) (((A.shape i).afterSquare (d i)).family.right e)⟩)
    rw [Shape.cast_left,Shape.cast_right]
    exact A.endpoints i _

@[simp] theorem afterSquare_shape (d : I → Bool) (i) :
    (A.afterSquareDecision d).shape i = (A.shape i).afterSquare (d i) := rfl

@[simp] theorem afterSquare_outside (d : I → Bool) : (A.afterSquareDecision d).outside = A.outside := rfl

theorem afterSquare_old (d : I → Bool) (e : E) : (A.afterSquareDecision d).oldMatching e = A.oldMatching e := by
  obtain ⟨z,rfl⟩ := (A.afterSquareDecision d).labels.surjective e
  rw [oldMatching,Equiv.symm_apply_apply]
  rcases z with x | k | ⟨i,j⟩
  · change false = A.oldMatching (A.labels (.inl x))
    simp [oldMatching]
  · change true = A.oldMatching (A.labels (.inr (.inl k)))
    simp [oldMatching]
  · change priorLocal ((A.shape i).afterSquare (d i)) j.val = A.oldMatching
      (A.labels (.inr (.inr ⟨i,Fin.cast ((A.shape i).afterSquare_edges (d i)) j⟩)))
    simp [oldMatching]
    rfl

variable [Fintype X] [DecidableEq V]

def afterSquareColors (d : I → Bool) (side : V → Bool) (P : A.PartitionColors side) :
    (A.afterSquareDecision d).PartitionColors side where
  exterior := P.exterior
  first := P.first
  second := P.second
  balanced i v := by
    let u := Fin.cast ((A.shape i).afterSquare_vertices (d i)) v
    change coloredDegree A.outside P.exterior (A.places ⟨i,u⟩) false +
        ((A.shape i).afterSquare (d i)).portDegree (P.first i) (P.second i) v.val false =
      coloredDegree A.outside P.exterior (A.places ⟨i,u⟩) true +
        ((A.shape i).afterSquare (d i)).portDegree (P.first i) (P.second i) v.val true
    rw [Shape.afterSquare_ports,Shape.afterSquare_ports]
    exact P.balanced i u
  normalized i h := by
    have old := P.normalized i (by simpa using h)
    have eq : Fin.cast ((A.shape i).afterSquare_vertices (d i))
        (vertexAt ((A.shape i).afterSquare (d i)) 0) = vertexAt (A.shape i) 0 := by
      apply Fin.ext; simp [vertexAt]
    change P.first i = !(side (A.places ⟨i,Fin.cast ((A.shape i).afterSquare_vertices (d i))
      (vertexAt ((A.shape i).afterSquare (d i)) 0)⟩))
    rw [eq]
    exact old

end Atlas
end Kostochka.FiveRegular.Restoration

end

section 

namespace Kostochka.Four.PathCover

open SimpleGraph FiveRegular FiveRegular.Subdivision

variable {V : Type} [Fintype V] [DecidableEq V] (F : SimpleGraph V) [DecidableRel F.Adj]

omit [DecidableEq V] in
theorem degree_map_le_two {W : Type} [Fintype W] [DecidableEq W] (f : V ↪ W)
    (S : SimpleGraph V) [DecidableRel S.Adj] (sd : ∀ v, S.degree v ≤ 2)
    [dec : DecidableRel (S.map f).Adj] (w : W) : (S.map f).degree w ≤ 2 := by
  classical
  rw [← card_neighborFinset_eq_degree]
  by_cases h : ∃ v, f v = w
  · obtain ⟨v,rfl⟩ := h
    have sub : (S.map f).neighborFinset (f v) ⊆ (S.neighborFinset v).map f := by
      intro z hz
      obtain ⟨u,t,hadj,hu,ht⟩ := (map_adj f S _ _).mp (((S.map f).mem_neighborFinset _ _).mp hz)
      exact Finset.mem_map.mpr ⟨t,(S.mem_neighborFinset _ _).mpr ((f.injective hu) ▸ hadj),ht⟩
    exact (Finset.card_le_card sub).trans (by simpa using sd v)
  · have empty : (S.map f).neighborFinset w = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨u,t,_,hu,_⟩ := (map_adj f S _ _).mp (((S.map f).mem_neighborFinset _ _).mp hz)
      exact h ⟨u,hu⟩
    simp [empty]

variable {F} {bound : ∀ v, F.degree v ≤ 2} {mark : V → Bool}

def sidePalette (S : SimpleGraph V) (F : SimpleGraph V) (mark : V → Bool) : Prop :=
  ∃ c : V → Fin 3, (∀ x y, S.Adj x y → c x ≠ c y) ∧
    Nonempty (SimpleEdgePalette F (fun v => if mark v then some (c v) else none))

omit [Fintype V] [DecidableEq V] in

theorem labeled_palette_of_compatible {E : Type} (T : Family V E) (hl : Loopless T)
    (two : AtMostTwo T) (S : SimpleGraph V) (mark : V → Bool)
    (compatible : ∀ c : V → Fin 3, ParallelCompatible T (fun v => if mark v then some (c v) else none))
    (palette : sidePalette S (support T) mark) :
    ∃ (vc : V → Fin 3) (ec : E → Fin 3), (∀ x y, S.Adj x y → vc x ≠ vc y) ∧
      (∀ e f, e ≠ f → FamilyMeet T e f → ec e ≠ ec f) ∧
      ∀ v e, mark v = true → FamilyIncident T v e → vc v ≠ ec e := by
  obtain ⟨vc,hvc,⟨P⟩⟩ := palette
  let c (v : V) : Option (Fin 3) := if mark v then some (vc v) else none
  obtain ⟨ec,he,hi⟩ := color_labeled_of_support T hl two c (compatible vc) P
  exact ⟨vc,ec,hvc,he,fun v e hm hv => (hi v e (vc v) (by simp [c,hm]) hv).symm⟩

omit [Fintype V] [DecidableEq V] in

theorem contractedPalette_of_sidePalette {E Q : Type} (D : Family V E) (q : V → Q)
    (side : V → Bool) (part : E → EdgePart) (exc : V → Prop) (b : Bool)
    (S : SimpleGraph Q) (mark : Q → Bool)
    (covers : ∀ e, side (D.left e) = b → side (D.right e) = b → ¬exc (D.left e) →
      ¬exc (D.right e) → S.Adj (q (D.left e)) (q (D.right e)))
    (ordinary : ∀ v, side v = b → ¬exc v → mark (q v) = true)
    (hl : Loopless (contracted D q part b)) (two : AtMostTwo (contracted D q part b))
    (compatible : ∀ c : Q → Fin 3, ParallelCompatible (contracted D q part b)
      (fun v => if mark v then some (c v) else none))
    (P : sidePalette S (support (contracted D q part b)) mark) :
    Nonempty (ContractedPalette D side part exc b q) := by
  obtain ⟨vc,ec,hs,he,hi⟩ := labeled_palette_of_compatible _ hl two S mark compatible P
  exact ⟨⟨vc ∘ q,ec,fun e hx hy hu hw => hs _ _ (covers e hx hy hu hw),he,
    fun v e hs ho hv => hi (q v) e (ordinary v hs ho) hv⟩⟩

end Kostochka.Four.PathCover

end

section 

namespace Kostochka.FiveRegular

open Subdivision

variable {V E : Type*}

def folded (partner : V → V) (u : V) : Sym2 V := s(u, partner u)

theorem folded_eq {partner : V → V} (hinv : Function.Involutive partner) (u v : V) :
    folded partner u = folded partner v ↔ u = v ∨ u = partner v := by
  constructor
  · intro h
    exact (Sym2.eq_iff.mp h).imp And.left And.left
  · rintro (rfl | rfl)
    · rfl
    · exact Sym2.eq_iff.mpr (Or.inr ⟨rfl,hinv _⟩)

def foldFamily (D : Family V E) (partner : V → V) : Family (Sym2 V) E :=
  ⟨fun e => folded partner (D.left e), fun e => folded partner (D.right e)⟩

private theorem original_or_partner (D : Family V E) {partner : V → V} (hi : Function.Involutive partner)
    (v : V) (e : E) : FamilyIncident (foldFamily D partner) (folded partner v) e ↔
      FamilyIncident D v e ∨ FamilyIncident D (partner v) e := by
  simp only [FamilyIncident, foldFamily, folded_eq hi]
  have heq (w : V) : v = partner w ↔ partner v = w :=
    ⟨fun h => (congrArg partner h).trans (hi w), fun h => (hi v).symm.trans (congrArg partner h)⟩
  rw [heq, heq]
  tauto

theorem atMostTwo_foldFamily (D : Family V E) {partner : V → V}
    (hi : Function.Involutive partner) (bd : AtMostTwo D)
    (one : ∀ v, partner v ≠ v → ∀ e f, FamilyIncident D v e → FamilyIncident D v f → e = f) :
    AtMostTwo (foldFamily D partner) := by
  intro k e f g he hf hg
  obtain ⟨v, hv⟩ : ∃ v, k = folded partner v := by
    rcases he with hv | hv
    · exact ⟨D.left e, hv⟩
    · exact ⟨D.right e, hv⟩
  subst k
  rw [original_or_partner D hi] at he hf hg
  by_cases h : partner v = v
  · rw [h, or_self] at he hf hg
    exact bd v e f g he hf hg
  · have h' : partner (partner v) ≠ partner v := by rwa [hi, ne_comm]
    rcases he with he | he <;> rcases hf with hf | hf <;> rcases hg with hg | hg
    all_goals first
      | exact Or.inl (one _ h _ _ he hf)
      | exact Or.inr (Or.inl (one _ h _ _ he hg))
      | exact Or.inr (Or.inr (one _ h _ _ hf hg))
      | exact Or.inl (one _ h' _ _ he hf)
      | exact Or.inr (Or.inl (one _ h' _ _ he hg))
      | exact Or.inr (Or.inr (one _ h' _ _ hf hg))

theorem loopless_foldFamily (D : Family V E) {partner : V → V} (hi : Function.Involutive partner)
    (orig : Loopless D) (apart : ∀ e, D.left e ≠ partner (D.right e)) :
    Loopless (foldFamily D partner) := by
  intro e h
  exact ((folded_eq hi _ _).mp h).elim (orig e) (apart e)

theorem parallelCompatible_foldFamily (D : Family V E) {partner : V → V}
    (hi : Function.Involutive partner) (ordinary : V → Prop) (paint : Sym2 V → Option (Fin 3))
    (prescribed : ∀ k b, paint k = some b → ∃ u, k = folded partner u ∧ ordinary u ∧ partner u = u)
    (internal : ∀ u v, ordinary u → ordinary v → u ≠ v → ∀ e f,
      FamilyIncident D u e → FamilyIncident D v e → FamilyIncident D u f → FamilyIncident D v f → e = f) :
    ParallelCompatible (foldFamily D partner) paint := by
  intro e f hne heq x y a b hxe hye hxa hyb
  obtain ⟨u, rfl, huo, hu⟩ := prescribed _ _ hxa
  obtain ⟨v, rfl, hvo, hv⟩ := prescribed _ _ hyb
  by_cases huv : u = v
  · subst v
    exact Option.some.inj (hxa.symm.trans hyb)
  · have pull (w : V) (hw : partner w = w) (g : E) :
        FamilyIncident (foldFamily D partner) (folded partner w) g → FamilyIncident D w g := by
      rw [original_or_partner D hi, hw, or_self]
      exact id
    have transfer (w : Sym2 V) (hit : FamilyIncident (foldFamily D partner) w e) :
        FamilyIncident (foldFamily D partner) w f := by
      have hm : w ∈ familyPair (foldFamily D partner) e := Sym2.mem_iff.mpr hit
      rw [heq] at hm
      exact Sym2.mem_iff.mp hm
    exact (hne (internal _ _ huo hvo huv _ _ (pull u hu e hxe) (pull v hv e hye)
      (pull u hu f (transfer _ hxe)) (pull v hv f (transfer _ hye)))).elim

end Kostochka.FiveRegular

end

section 

namespace Kostochka.FiveRegular

theorem equal_before_fold {V : Type*} (partner : V → V) (hi : Function.Involutive partner)
    (saturated : V → Prop) (pairSat : ∀ w, partner w ≠ w → saturated w ∨ saturated (partner w))
    {u v : V} (hf : folded partner u = folded partner v)
    (hu : ¬ saturated u) (hv : ¬ saturated v) : u = v := by
  rcases (folded_eq hi _ _).mp hf with he | he
  · exact he
  · rw [he] at hu ⊢
    by_contra hn
    exact (pairSat v hn).elim hv hu

end Kostochka.FiveRegular

end

section 

namespace Kostochka.FiveRegular
open SimpleGraph Four Four.PathCover

variable {V : Type} [Fintype V] [DecidableEq V]

def NoOrdinarySquare (S F : SimpleGraph V) (mark : V → Bool) : Prop :=
  ∀ s : Fin 4 ↪ V, (∀ i, mark (s i) = true) → (∀ i, S.Adj (s i) (s (i+1))) →
    (∀ i, F.Adj (s i) (s (i+1)) ∨ F.Adj (s i) (s (i+3))) →
    ∀ x y, mark x = false → mark y = false →
    F.Adj (s 0) x → F.Adj (s 2) x → F.Adj (s 1) y → F.Adj (s 3) y → False

end Kostochka.FiveRegular

end

section 

namespace Kostochka.Four.PathCover

open SimpleGraph FiveRegular FiveRegular.Subdivision

variable {V E : Type}

def diagonal (V : Type) : V ↪ Sym2 V := ⟨Sym2.diag,Sym2.diag_injective⟩

def foldedSide (S : SimpleGraph V) : SimpleGraph (Sym2 V) := S.map (diagonal V)

noncomputable def ordinaryMark (mark : V → Bool) (w : Sym2 V) : Bool :=
  @decide (∃ v, w = Sym2.diag v ∧ mark v = true) (Classical.propDecidable _)

theorem ordinaryMark_iff (mark : V → Bool) (w : Sym2 V) :
    ordinaryMark mark w = true ↔ ∃ v, w = Sym2.diag v ∧ mark v = true := by
  simp only [ordinaryMark,decide_eq_true_eq]

theorem fold_eq_diag_iff (p : V → V) (x y : V) :
    folded p x = Sym2.diag y ↔ x = y ∧ p x = y := by
  rw [folded,Sym2.diag,Sym2.eq_iff]; tauto

theorem fold_fixed (p : V → V) {x : V} (h : p x = x) : folded p x = Sym2.diag x :=
  (fold_eq_diag_iff p x x).mpr ⟨rfl,h⟩

theorem ordinaryMark_fold (mark : V → Bool) (p : V → V)
    (fixed : ∀ x, mark x = true → p x = x) (v : V) :
    ordinaryMark mark (folded p v) = true ↔ mark v = true := by
  rw [ordinaryMark_iff]
  constructor
  · rintro ⟨u,eq,hm⟩
    exact ((fold_eq_diag_iff _ _ _).mp eq).1 ▸ hm
  · exact fun h => ⟨v,fold_fixed _ (fixed v h),h⟩

theorem degree_foldedSide [Fintype V] [DecidableEq V] (S : SimpleGraph V) [DecidableRel S.Adj]
    (bound : ∀ v, S.degree v ≤ 2) [dec : DecidableRel (foldedSide S).Adj] (k : Sym2 V) :
    (foldedSide S).degree k ≤ 2 := degree_map_le_two (diagonal V) S bound (dec := dec) k

theorem support_unfold (T : Family V E) (p : V → V) {x y : V}
    (h : (support (foldFamily T p)).Adj (Sym2.diag x) (Sym2.diag y)) : (support T).Adj x y := by
  obtain ⟨e,he⟩ := h.1
  change s(folded p (T.left e),folded p (T.right e)) = s(Sym2.diag x,Sym2.diag y) at he
  refine ⟨⟨e,?_⟩,fun eq => h.ne (congrArg Sym2.diag eq)⟩
  rcases Sym2.eq_iff.mp he with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · exact Sym2.eq_iff.mpr (.inl ⟨((fold_eq_diag_iff _ _ _).mp hx).1,((fold_eq_diag_iff _ _ _).mp hy).1⟩)
  · exact Sym2.eq_iff.mpr (.inr ⟨((fold_eq_diag_iff _ _ _).mp hx).1,((fold_eq_diag_iff _ _ _).mp hy).1⟩)

theorem fold_inside (T : Family V E) (p : V → V) (S : SimpleGraph V) (mark : V → Bool)
    (cover : ∀ x y, (support T).Adj x y → mark x = true → mark y = true → S.Adj x y) :
    ∀ x y, (support (foldFamily T p)).Adj x y → ordinaryMark mark x = true →
      ordinaryMark mark y = true → (foldedSide S).Adj x y := by
  intro x y h hx hy
  obtain ⟨u,rfl,hu⟩ := (ordinaryMark_iff _ _).mp hx
  obtain ⟨v,rfl,hv⟩ := (ordinaryMark_iff _ _).mp hy
  exact map_adj_apply.mpr (cover _ _ (support_unfold _ _ h) hu hv)

theorem fold_no_three (T : Family V E) (p : V → V) (mark : V → Bool)
    (single : ∀ x y z, mark x = true → mark y = true → mark z = true →
      (support T).Adj x y → (support T).Adj y z → x = z) :
    ∀ x y z, x ≠ z → (support (foldFamily T p)).Adj x y → (support (foldFamily T p)).Adj y z →
      ¬ (ordinaryMark mark x = true ∧ ordinaryMark mark y = true ∧ ordinaryMark mark z = true) := by
  rintro x y z hn hxy hyz ⟨hx,hy,hz⟩
  obtain ⟨u,rfl,hu⟩ := (ordinaryMark_iff _ _).mp hx
  obtain ⟨v,rfl,hv⟩ := (ordinaryMark_iff _ _).mp hy
  obtain ⟨w,rfl,hw⟩ := (ordinaryMark_iff _ _).mp hz
  exact hn (congrArg Sym2.diag (single u v w hu hv hw (support_unfold _ _ hxy) (support_unfold _ _ hyz)))

theorem compatibility_fixed (T : Family V E) (p : V → V) (hi : Function.Involutive p) (mark : V → Bool)
    (fixed : ∀ x, mark x = true → p x = x)
    (unique : ∀ u v, mark u = true → mark v = true → u ≠ v → ∀ e f,
      FamilyIncident T u e → FamilyIncident T v e → FamilyIncident T u f → FamilyIncident T v f → e = f)
    (c : Sym2 V → Fin 3) : ParallelCompatible (foldFamily T p)
      (fun v => if ordinaryMark mark v then some (c v) else none) := by
  apply parallelCompatible_foldFamily T hi (fun v => mark v = true) _ _ unique
  intro k b hb
  by_cases h : ordinaryMark mark k = true
  · obtain ⟨v,rfl,hv⟩ := (ordinaryMark_iff _ _).mp h
    exact ⟨v,(fold_fixed _ (fixed v hv)).symm,hv,fixed v hv⟩
  · simp [h] at hb

end Kostochka.Four.PathCover

end

section 

namespace Kostochka.FiveRegular
open SimpleGraph Subdivision Four.PathCover

variable {V E : Type}

private theorem unfold_one_end (T : Family V E) (p : V → V) {v : V} {k : Sym2 V}
    (adj : (support (foldFamily T p)).Adj (Sym2.diag v) k) :
    ∃ w : V, k = folded p w ∧ (support T).Adj v w := by
  obtain ⟨e,he⟩ := adj.1
  change s(folded p (T.left e),folded p (T.right e)) = s(Sym2.diag v,k) at he
  rcases Sym2.eq_iff.mp he with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · obtain ⟨eq,hp⟩ := (fold_eq_diag_iff _ _ _).mp hl
    refine ⟨T.right e,hr.symm,⟨e,?_⟩,?_⟩
    · rw [familyPair,eq]
    · intro ident
      exact adj.ne (hl.symm.trans ((congrArg (folded p) (eq.trans ident)).trans hr))
  · obtain ⟨eq,hp⟩ := (fold_eq_diag_iff _ _ _).mp hr
    refine ⟨T.left e,hl.symm,⟨e,?_⟩,?_⟩
    · rw [familyPair,eq,Sym2.eq_swap]
    · intro ident
      exact adj.ne (hr.symm.trans ((congrArg (folded p) (eq.trans ident)).trans hl))

theorem reachable_through_fold (D : Family V E) (p : V → V) (hi : Function.Involutive p)
    (residual : SimpleGraph V) (sub : support D ≤ residual)
    (connectedPairs : ∀ v, residual.Reachable v (p v)) {u v : V} {k : Sym2 V}
    (a : (support (foldFamily D p)).Adj (Sym2.diag u) k)
    (b : (support (foldFamily D p)).Adj (Sym2.diag v) k) : residual.Reachable u v := by
  obtain ⟨x,hx,hux⟩ := unfold_one_end D p a
  obtain ⟨y,hy,hvy⟩ := unfold_one_end D p b
  have mid : residual.Reachable x y := by
    rcases (folded_eq hi x y).mp (hx.symm.trans hy) with eq | eq
    · exact eq ▸ Reachable.refl x
    · exact eq ▸ (connectedPairs y).symm
  exact (sub hux).reachable.trans (mid.trans (sub hvy).symm.reachable)

/- Section 5. After folding the prescribed pairs of vertices, checking the ordinary-square
obstruction is essential before applying the palette lemma. -/
theorem no_ordinary_square_fold (T : Family V E) (p : V → V) (hi : Function.Involutive p)
    (S : SimpleGraph V) (mark : V → Bool) (fixed : ∀ v, mark v = true → p v = v)
    (saturated : V → Prop) (pairs : ∀ v, p v ≠ v → saturated v ∨ saturated (p v))
    (residual : SimpleGraph V) (sub : support T ≤ residual)
    (connectedPairs : ∀ v, residual.Reachable v (p v))
    (avoid : NoOrdinarySquare S (support T) mark)
    (unsat : ∀ s : Fin 4 ↪ V, (∀ i, mark (s i) = true) → (∀ i, S.Adj (s i) (s (i+1))) →
      (∀ i, (support T).Adj (s i) (s (i+1)) ∨ (support T).Adj (s i) (s (i+3))) →
      residual.Reachable (s 0) (s 2) → residual.Reachable (s 1) (s 3) →
      ∀ i w, mark w = false → (support T).Adj (s i) w → ¬ saturated w) :
    NoOrdinarySquare (foldedSide S) (support (foldFamily T p)) (ordinaryMark mark) := by
  classical
  intro s hm hs hf x y mx my e₀ e₂ e₁ e₃
  choose v hv hvmark using fun i => (ordinaryMark_iff _ _).mp (hm i)
  let a : Fin 4 ↪ V := ⟨v,fun i j eq => s.injective ((hv i).trans ((congrArg Sym2.diag eq).trans (hv j).symm))⟩
  have cycle (i : Fin 4) : S.Adj (a i) (a (i+1)) := map_adj_apply.mp (hv i ▸ hv (i+1) ▸ hs i)
  have cov (i : Fin 4) : (support T).Adj (a i) (a (i+1)) ∨ (support T).Adj (a i) (a (i+3)) := by
    have hit (j : Fin 4) (h : (support (foldFamily T p)).Adj (s i) (s j)) :
        (support T).Adj (a i) (a j) := support_unfold T p (hv i ▸ hv j ▸ h)
    exact (hf i).imp (hit _) (hit _)
  have r₀ : residual.Reachable (a 0) (a 2) := reachable_through_fold T p hi residual sub connectedPairs
    (hv 0 ▸ e₀) (hv 2 ▸ e₂)
  have r₁ : residual.Reachable (a 1) (a 3) := reachable_through_fold T p hi residual sub connectedPairs
    (hv 1 ▸ e₁) (hv 3 ▸ e₃)
  have unfoldspoke (i : Fin 4) (k : Sym2 V) (h : (support (foldFamily T p)).Adj (s i) k)
      (m : ordinaryMark mark k = false) :
      ∃ w, k = folded p w ∧ (support T).Adj (a i) w ∧ mark w = false ∧ ¬ saturated w := by
    obtain ⟨w,eq,adj⟩ := unfold_one_end T p (hv i ▸ h)
    have bad : mark w = false := by
      by_contra! hm'
      have htrue := (ordinaryMark_fold mark p fixed w).mpr (Bool.eq_true_of_not_eq_false hm')
      rw [← eq,m] at htrue
      contradiction
    exact ⟨w,eq,adj,bad,unsat a hvmark cycle cov r₀ r₁ _ _ bad adj⟩
  obtain ⟨w₀,h₀,b₀,m₀,n₀⟩ := unfoldspoke 0 x e₀ mx
  obtain ⟨w₂,h₂,b₂,m₂,n₂⟩ := unfoldspoke 2 x e₂ mx
  obtain ⟨w₁,h₁,b₁,m₁,n₁⟩ := unfoldspoke 1 y e₁ my
  obtain ⟨w₃,h₃,b₃,m₃,n₃⟩ := unfoldspoke 3 y e₃ my
  have eq₀ := equal_before_fold p hi saturated pairs (h₀.symm.trans h₂) n₀ n₂
  have eq₁ := equal_before_fold p hi saturated pairs (h₁.symm.trans h₃) n₁ n₃
  exact avoid a hvmark cycle cov w₀ w₁ m₀ m₁ b₀ (eq₀ ▸ b₂) b₁ (eq₁ ▸ b₃)

end Kostochka.FiveRegular

end

section 

namespace Kostochka.FiveRegular

open Subdivision SimpleGraph
variable {V E : Type*}

def restrictFamily (D : Family V E) (keep : E → Prop) : Family V {e // keep e} :=
  ⟨fun e => D.left e, fun e => D.right e⟩

theorem support_restrict (D : Family V E) (keep : E → Prop) {v w : V} :
    (support (restrictFamily D keep)).Adj v w ↔
      (∃ e, keep e ∧ familyPair D e = s(v,w)) ∧ v ≠ w := by
  constructor
  · rintro ⟨⟨e,he⟩,ne⟩
    exact ⟨⟨e,e.property,he⟩,ne⟩
  · rintro ⟨⟨e,h,he⟩,ne⟩
    exact ⟨⟨⟨e,h⟩,he⟩,ne⟩

end Kostochka.FiveRegular

end

section 

namespace Kostochka.FiveRegular.Restoration.Atlas
open Subdivision Auxiliary

variable {V E I X K : Type*} {D : Family V E} (A : Atlas D I X K)

def vertex (i : I) (k : ℕ) : V := A.places ⟨i,vertexAt (A.shape i) k⟩

def InPiece (i : I) (v : V) : Prop := ∃ k : Fin (A.shape i).vertices, v = A.places ⟨i,k⟩

def CrossingLink (f : X → Bool) (b : Bool) (v w : V) : Prop :=
  ∃ x : X, f x = b ∧ familyPair A.outside x = s(v,w)

def JoinedOpposite (f : X → Bool) (b : Bool) (i : I) (pair : Sym2 V) : Prop :=
  ∃ w, ¬ A.InPiece i w ∧ ∀ v ∈ pair, A.CrossingLink f b v w

def ShouldDivert (f : X → Bool) (side : V → Bool) (i : I) : Prop :=
  A.JoinedOpposite f (side (A.vertex i 0)) i s(A.vertex i 0,A.vertex i 2) ∧
  A.JoinedOpposite f (side (A.vertex i 0)) i s(A.vertex i 1,A.vertex i 3)

noncomputable def squareDecision (f : X → Bool) (side : V → Bool) (i : I) : Bool := by
  classical exact decide (A.ShouldDivert f side i)

@[simp] theorem squareDecision_iff (f : X → Bool) (side : V → Bool) (i : I) :
    A.squareDecision f side i = true ↔ A.ShouldDivert f side i := by
  classical simp [squareDecision]

@[simp] theorem afterSquare_inPiece (d : I → Bool) (i : I) (v : V) :
    (A.afterSquareDecision d).InPiece i v ↔ A.InPiece i v := by
  constructor
  · rintro ⟨k,rfl⟩
    exact ⟨Fin.cast ((A.shape i).afterSquare_vertices (d i)) k,rfl⟩
  · rintro ⟨k,rfl⟩
    exact ⟨Fin.cast ((A.shape i).afterSquare_vertices (d i)).symm k,rfl⟩

private theorem pairIncident {e : E} {v w : V} (h : familyPair D e = s(v,w)) :
    FamilyIncident D v e ∧ FamilyIncident D w e := by
  change s(D.left e,D.right e) = _ at h
  rcases Sym2.eq_iff.mp h with ⟨l,r⟩ | ⟨l,r⟩ <;> simp [FamilyIncident,l,r]

theorem crossing_of_factor (f : X → Bool) (p q : I → Bool) (i : I) {v w : V} {e : E} {b : Bool}
    (inside : A.InPiece i v) (outside : ¬ A.InPiece i w)
    (factor : A.part f p q e = .factor b) (pair : familyPair D e = s(v,w)) :
    A.CrossingLink f b v w := by
  obtain ⟨k,rfl⟩ := inside
  obtain ⟨t,rfl⟩ := A.labels.surjective e
  rcases t with x | t | ⟨j,t⟩
  · exact ⟨x,by simpa using factor,pair⟩
  · simp at factor
  · have ⟨l,r⟩ := pairIncident pair
    obtain rfl := A.samePieceOfIncident l
    rcases (A.localIncident i t w).mp r with h | h <;> exact (outside ⟨_,h⟩).elim

theorem divert_of_factor_spokes [DecidableEq V]
    (f : X → Bool) (p q : I → Bool) (side : V → Bool) (d : I → Bool)
    (i : I) (v : Fin 4 → V) (b : Bool)
    (mono : side (A.vertex i 0) = b)
    (inside : ∀ k, A.InPiece i (v k))
    (diagonals : ({s(A.vertex i 0,A.vertex i 2),s(A.vertex i 1,A.vertex i 3)} : Finset (Sym2 V)) =
      {s(v 0,v 2),s(v 1,v 3)})
    (w : Fin 2 → V) (exterior : ∀ k, ¬ A.InPiece i (w k))
    (spokes : ∀ k : Fin 4, ∃ e, (A.afterSquareDecision d).part f p q e = .factor b ∧
      familyPair D e = s(v k, w ⟨k.val % 2,by omega⟩)) :
    A.squareDecision f side i = true := by
  rw [squareDecision_iff]
  have link (k : Fin 4) : A.CrossingLink f b (v k) (w ⟨k.val % 2,by omega⟩) := by
    obtain ⟨e,he,pair⟩ := spokes k
    exact (A.afterSquareDecision d).crossing_of_factor f p q i
      (by simpa using inside k) (by simpa using exterior _) he pair
  have join (P : Sym2 V) (h : P ∈ ({s(v 0,v 2),s(v 1,v 3)} : Finset (Sym2 V))) :
      A.JoinedOpposite f b i P := by
    rcases Finset.mem_insert.mp h with rfl | h
    · exact ⟨w 0,exterior 0,fun u hu => (Sym2.mem_iff.mp hu).elim (fun h => h ▸ link 0) (fun h => h ▸ link 2)⟩
    · obtain rfl := Finset.mem_singleton.mp h
      exact ⟨w 1,exterior 1,fun u hu => (Sym2.mem_iff.mp hu).elim (fun h => h ▸ link 1) (fun h => h ▸ link 3)⟩
  unfold ShouldDivert
  rw [mono]
  exact ⟨join _ (diagonals ▸ Finset.mem_insert_self ..),join _ (diagonals ▸ by simp)⟩

theorem exceptional_of_spoke_decision (f : X → Bool) (p q : I → Bool) (side : V → Bool)
    (i : I) (shape : A.shape i = .evenCycle 1) (decision : A.squareDecision f side i = true)
    (e : Fin ((A.afterSquareDecision (A.squareDecision f side)).shape i).edges) :
    (A.afterSquareDecision (A.squareDecision f side)).part f p q
      ((A.afterSquareDecision (A.squareDecision f side)).localLabel i e) = .exceptional := by
  apply ((A.afterSquareDecision _).exceptional_iff f p q _).mpr
  exact ⟨i,e,rfl,Or.inr (Or.inr (by simp [Shape.afterSquare,shape,decision]))⟩

end Kostochka.FiveRegular.Restoration.Atlas

end

section 

namespace Kostochka.Four.PathCover

open SimpleGraph FiveRegular FiveRegular.Subdivision Finset

variable {V : Type}

def ordinaryGraph (G : SimpleGraph V) (mark : V → Bool) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ mark x = true ∧ mark y = true
  symm.symm _ _ h := ⟨h.1.symm,h.2.2,h.2.1⟩
  loopless.irrefl _ h := h.1.ne rfl

variable [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem ordinary_degree (G : SimpleGraph V) (side mark : V → Bool) (b : Bool)
    (hm : ∀ x, mark x = true → side x = b)
    (bounded : ∀ x, insideDegree G side x ≤ 2)
    [DecidableRel (ordinaryGraph G mark).Adj] (x : V) : (ordinaryGraph G mark).degree x ≤ 2 := by
  classical
  rw [← card_neighborFinset_eq_degree]
  apply (Finset.card_le_card (t := Finset.univ.filter fun y => G.Adj x y ∧ side x = side y) _).trans (bounded x)
  intro y hy
  obtain ⟨a,hx,hy'⟩ := ((ordinaryGraph G mark).mem_neighborFinset _ _).mp hy
  exact mem_filter.mpr ⟨mem_univ _,a,(hm _ hx).trans (hm _ hy').symm⟩

end Kostochka.Four.PathCover

end

section 

namespace Kostochka.FiveRegular

open Subdivision SimpleGraph Four.PathCover

section Basic
variable {V E : Type*}

abbrev factorFamily (D : Family V E) (part : E → EdgePart) (b : Bool) :=
  contracted D id part b

noncomputable def ordinaryAt (side : V → Bool) (exc : V → Prop) (b : Bool) (v : V) : Bool :=
  @decide (side v = b ∧ ¬exc v) (Classical.propDecidable _)

@[simp] theorem ordinaryAt_iff (side : V → Bool) (exc : V → Prop) (b : Bool) (v : V) :
    ordinaryAt side exc b v = true ↔ side v = b ∧ ¬exc v := by simp [ordinaryAt]

def InternalMatching (T : Family V E) (mark : V → Bool) : Prop :=
  ∀ v, mark v = true → ∀ e f, FamilyIncident T v e → FamilyIncident T v f →
    mark (T.left e) = true → mark (T.right e) = true →
    mark (T.left f) = true → mark (T.right f) = true → e = f

theorem factor_support_le (D : Family V E) (part : E → EdgePart) (b : Bool) :
    support (factorFamily D part b) ≤ support D := by
  rintro x y ⟨⟨e,he⟩,hn⟩
  exact ⟨⟨e.val,he⟩,hn⟩

end Basic

variable {V E : Type} [Fintype V] [DecidableEq V]

end Kostochka.FiveRegular

end

section 

namespace Kostochka.FiveRegular.Restoration

open Subdivision Auxiliary SimpleGraph

namespace Shape

def exceptionalShape : Shape → Prop
  | .badPath | .badOdd _ | .divertedSquare => True
  | _ => False

def partnerCoordinate (s : Shape) (first target : Bool) : Fin s.vertices → Fin s.vertices :=
  match s with
  | .badOdd n => Equiv.swap (⟨0,by simp [vertices,cyclic,edges]⟩ : Fin (Shape.badOdd n).vertices)
      ⟨2,by simp [vertices,cyclic,edges]⟩
  | .badPath => if first = target then Equiv.swap (0 : Fin 4) 2 else Equiv.swap (3 : Fin 4) 1
  | .divertedSquare => fun j : Fin 4 => (j+(2 : Fin 4) : Fin 4)
  | _ => id

theorem partnerCoordinate_involutive (s : Shape) (first b : Bool) :
    Function.Involutive (s.partnerCoordinate first b) := by
  cases s with
  | badPath =>
    cases first <;> cases b <;> intro v <;> exact Equiv.swap_apply_self _ _ v
  | badOdd n => exact Equiv.swap_apply_self _ _
  | divertedSquare =>
    change ∀ v : Fin 4, (v+2)+2=v
    decide
  | _ => exact fun _ => rfl

theorem partnerCoordinate_exceptional (s : Shape) (first b : Bool) (v : Fin s.vertices)
    (moved : s.partnerCoordinate first b v ≠ v) : s.exceptionalShape := by
  cases s <;> trivial

theorem partnerCoordinate_saturated (s : Shape) (first b : Bool) (v : Fin s.vertices)
    (moved : s.partnerCoordinate first b v ≠ v) :
    oldDegree s v.val = 2 ∨ oldDegree s (s.partnerCoordinate first b v).val = 2 := by
  have exception := partnerCoordinate_exceptional s first b v moved
  cases s <;> try contradiction
  case badPath =>
    change Fin 4 at v
    cases first <;> cases b <;> fin_cases v <;> first | exact (moved rfl).elim | decide
  case badOdd n =>
    left
    have ht : v.val < 2*n+3 := v.isLt
    simp [oldDegree,inc,cyclic,edges,ht]
  case divertedSquare =>
    left
    change Fin 4 at v
    fin_cases v <;> decide

theorem partnerCoordinate_shortage (s : Shape) (first second b : Bool) (v : Fin s.vertices)
    (moved : s.partnerCoordinate first b v ≠ v) :
    s.thirdDegree first second v.val = 2 ∨ s = .badPath ∧
      ((v.val = 0 ∧ first = b) ∨ (v.val = 3 ∧ (!first) = b)) := by
  have exception := partnerCoordinate_exceptional s first b v moved
  cases s <;> try contradiction
  case badPath =>
    change Fin 4 at v
    cases first <;> cases second <;> cases b <;> fin_cases v <;> first | exact (moved rfl).elim | decide
  case badOdd n =>
    left
    have ht : v.val < 2*n+3 := v.isLt
    simp [thirdDegree,inc,cyclic,edges,role,ht]
  case divertedSquare =>
    left
    change Fin 4 at v
    fin_cases v <;> rfl

end Shape

namespace Atlas

variable {V E I X K : Type*} {D : Family V E} (A : Atlas D I X K)

def pieceOf (v : V) : I := (A.places.symm v).1
def exceptionalAt (v : V) : Prop := (A.shape (A.pieceOf v)).exceptionalShape
def Saturated (v : V) : Prop :=
  oldDegree (A.shape (A.places.symm v).1) (A.places.symm v).2.val = 2

def pieceSide (side : V → Bool) (i : I) : Bool := side (A.vertex i 0)

def partner (side : V → Bool) (first : I → Bool) (b : Bool) (v : V) : V :=
  let z := A.places.symm v
  if A.pieceSide side z.1 = b then v else A.places ⟨z.1,(A.shape z.1).partnerCoordinate (first z.1) b z.2⟩

@[simp] theorem partner_at (side : V → Bool) (first : I → Bool) (b : Bool) (i : I)
    (v : Fin (A.shape i).vertices) :
    A.partner side first b (A.places ⟨i,v⟩) = if A.pieceSide side i = b then A.places ⟨i,v⟩
    else A.places ⟨i,(A.shape i).partnerCoordinate (first i) b v⟩ := by rw [partner,A.places.symm_apply_apply]

theorem partner_involutive (side : V → Bool) (first : I → Bool) (b : Bool) :
    Function.Involutive (A.partner side first b) := by
  intro w
  obtain ⟨⟨i,v⟩,rfl⟩ := A.places.surjective w
  by_cases h : A.pieceSide side i = b
  · simp [h]
  · simp [h,(A.shape i).partnerCoordinate_involutive (first i) b v]

theorem partner_fixed (side : V → Bool) (first : I → Bool) (b : Bool)
    (mono : ∀ i (v : Fin (A.shape i).vertices), side (A.places ⟨i,v⟩) = A.pieceSide side i)
    {v : V} (hv : side v = b) : A.partner side first b v = v := by
  obtain ⟨⟨i,j⟩,rfl⟩ := A.places.surjective v
  simp [(mono i j).symm.trans hv]

theorem partner_saturated (side : V → Bool) (first : I → Bool) (b : Bool) (v : V)
    (h : A.partner side first b v ≠ v) : A.Saturated v ∨ A.Saturated (A.partner side first b v) := by
  obtain ⟨⟨i,j⟩,rfl⟩ := A.places.surjective v
  by_cases hs : A.pieceSide side i = b
  · simp [hs] at h
  · simp only [partner_at,if_neg hs] at h ⊢
    have mv : (A.shape i).partnerCoordinate (first i) b j ≠ j := fun eq => h (congrArg (fun u => A.places ⟨i,u⟩) eq)
    simp only [Saturated]
    rw [A.places.symm_apply_apply,A.places.symm_apply_apply]
    exact (A.shape i).partnerCoordinate_saturated (first i) b j mv

theorem partner_reachable (side : V → Bool) (first : I → Bool) (b : Bool) (H : SimpleGraph V)
    (home : ∀ i (v w : Fin (A.shape i).vertices), H.Reachable (A.places ⟨i,v⟩) (A.places ⟨i,w⟩))
    (v : V) : H.Reachable v (A.partner side first b v) := by
  obtain ⟨⟨i,j⟩,rfl⟩ := A.places.surjective v
  by_cases h : A.pieceSide side i = b
  · simpa only [partner_at,if_pos h] using SimpleGraph.Reachable.refl (G := H) (A.places ⟨i,j⟩)
  · simpa only [partner_at,if_neg h] using home i j ((A.shape i).partnerCoordinate (first i) b j)

variable [Fintype I] [Fintype E] [Fintype X] [Fintype K] [DecidableEq V]

theorem partner_unique {side : V → Bool} (C : A.PartitionColors side) (b : Bool)
    (loop : Loopless D)
    (reg : ∀ i (v : Fin (A.shape i).vertices), coloredDegree A.outside (fun _ => true) (A.places ⟨i,v⟩) true +
      oldDegree (A.shape i) v.val = 4) (w : V) (mv : A.partner side C.first b w ≠ w) :
    ∃! e, A.part C.exterior C.first C.second e = .factor b ∧ FamilyIncident D w e := by
  obtain ⟨⟨i,v⟩,rfl⟩ := A.places.surjective w
  by_cases hs : A.pieceSide side i = b
  · simp [hs] at mv
  simp only [partner_at,if_neg hs] at mv
  have moved : (A.shape i).partnerCoordinate (C.first i) b v ≠ v := fun eq => mv (congrArg (fun u => A.places ⟨i,u⟩) eq)
  rcases (A.shape i).partnerCoordinate_shortage (C.first i) (C.second i) b v moved with two | ⟨bad,h⟩
  · exact A.uniqueSpoke _ _ _ i v b loop (reg i v) (C.balanced i v) two
  · have ends := A.endpoint_constraints C reg i bad v
    have deg : coloredDegree D (fun e => decide (A.part C.exterior C.first C.second e = .factor b))
        (A.places ⟨i,v⟩) true = 1 := by
      rcases h with ⟨h,rfl⟩|⟨h,rfl⟩
      · exact (ends.1 h).1
      · exact (ends.2 h).2
    simpa only [decide_eq_true_eq] using (unique_iff_degree D loop _ _).mpr deg

end Atlas
end Kostochka.FiveRegular.Restoration

end

section 

namespace MultFive.Multi.PieceDecomposition
open Finset SimpleGraph Kostochka.FiveRegular Subdivision Restoration Auxiliary
variable {V : Type*} [Fintype V] [DecidableEq V] {m : Multi V} {M : m.support.Subgraph} {side : V → Bool}
variable (D : PieceDecomposition m M side) (L : D.LabelCoverage) (d : D.Index → Bool)

private theorem square_residualDegree (s : Shape) (divert : Bool) (v : ℕ) :
    oldDegree (s.afterSquare divert) v = oldDegree s v := by
  unfold Shape.afterSquare
  split
  next eq => rw [eq.1]; rfl
  next => rfl

theorem final_saturated (reg : ∀ w, m.degree w = 5) (hm : M.IsPerfectMatching) (w : V) :
    ((D.physical L).afterSquareDecision d).Saturated w ↔ (m.residual M).insideDegree side w = 2 := by
  let A := D.physical L
  let F := A.afterSquareDecision d
  obtain ⟨⟨i,v⟩,rfl⟩ := F.places.surjective w
  have hi := D.inside_identity L reg hm i (Fin.cast ((A.shape i).afterSquare_vertices (d i)) v)
  change oldDegree (F.shape (F.places.symm (F.places ⟨i,v⟩)).1) (F.places.symm (F.places ⟨i,v⟩)).2.val = 2 ↔ _
  have zz := congrArg (fun z : Σ j, Fin (F.shape j).vertices => oldDegree (F.shape z.1) z.2.val) (F.places.symm_apply_apply ⟨i,v⟩)
  rw [show oldDegree (F.shape (F.places.symm (F.places ⟨i,v⟩)).1) (F.places.symm (F.places ⟨i,v⟩)).2.val = oldDegree (F.shape i) v.val from zz]
  change oldDegree ((A.shape i).afterSquare (d i)) v.val = 2 ↔ _
  rw [square_residualDegree]
  exact iff_of_eq (congrArg (· = 2) hi)

theorem final_no_balanced (reg : ∀ w, m.degree w = 5) (hm : M.IsPerfectMatching)
    (cut : ∀ u v, side u ≠ side v → (m.residual M).insideDegree side u = 2 →
      (m.residual M).insideDegree side v = 2 → (m.residual M).count u v = 0)
    (e : m.Edge) (free : ((D.physical L).afterSquareDecision d).oldMatching e = false)
    (cross : side (m.family.left e) ≠ side (m.family.right e)) :
    ¬(((D.physical L).afterSquareDecision d).Saturated (m.family.left e) ∧
      ((D.physical L).afterSquareDecision d).Saturated (m.family.right e)) := by
  simp_rw [D.final_saturated L d reg hm]
  exact D.not_both_saturated L cut e (by simpa only [Atlas.afterSquare_old] using free) cross

theorem final_monochromatic (i : D.Index) (v : Fin (((D.physical L).afterSquareDecision d).shape i).vertices) :
    side (((D.physical L).afterSquareDecision d).places ⟨i,v⟩) = (D.raw i).sideOf :=
  D.position_side i (Fin.cast ((D.rawShape i).afterSquare_vertices (d i)) v)

theorem final_component (i : D.Index) (v : Fin (((D.physical L).afterSquareDecision d).shape i).vertices) :
    (m.residual M).support.connectedComponentMk (((D.physical L).afterSquareDecision d).places ⟨i,v⟩) = D.group i :=
  D.position_home i (Fin.cast ((D.rawShape i).afterSquare_vertices (d i)) v)

theorem final_regular (reg : ∀ w, m.degree w = 5) (hm : M.IsPerfectMatching) (i : D.Index)
    (v : Fin (((D.physical L).afterSquareDecision d).shape i).vertices) :
    let A := (D.physical L).afterSquareDecision d
    coloredDegree A.outside (fun _ => true) (A.places ⟨i,v⟩) true + oldDegree (A.shape i) v.val = 4 := by
  dsimp only
  rw [show oldDegree (((D.physical L).afterSquareDecision d).shape i) v.val = oldDegree (D.rawShape i) v.val from square_residualDegree _ _ _]
  exact D.physical_regular L reg hm i (Fin.cast ((D.rawShape i).afterSquare_vertices (d i)) v)

end MultFive.Multi.PieceDecomposition

end

section 

namespace Kostochka.FiveRegular.Restoration
open Subdivision Auxiliary

variable {V E I X K : Type*} {D : Family V E}

structure RawSquare (D : Family V E) (side : V → Bool) (b : Bool) where
  v : Fin 4 ↪ V
  e : Fin 4 → E
  mono : ∀ k, side (v k) = b
  ends : ∀ k, familyPair D (e k) = s(v k,v (k+1))

namespace RawSquare
variable {side : V → Bool} {b : Bool} (S : RawSquare D side b)

def Internal (D : Family V E) (side : V → Bool) (e : E) : Prop := side (D.left e) = side (D.right e)

theorem internal (k : Fin 4) : Internal D side (S.e k) := by
  rcases Sym2.eq_iff.mp (S.ends k) with ⟨l,r⟩ | ⟨l,r⟩ <;> simp [Internal,l,r,S.mono]

theorem injective : Function.Injective S.e := by
  intro k l h
  have he := (S.ends k).symm.trans ((congrArg (familyPair D) h).trans (S.ends l))
  rcases Sym2.eq_iff.mp he with ⟨a,_⟩ | ⟨a,c⟩
  · exact S.v.injective a
  · have := S.v.injective a
    have := S.v.injective c
    omega

theorem incident (k : Fin 4) (e : E) :
    FamilyIncident D (S.v k) e ↔ S.v k ∈ familyPair D e := Sym2.mem_iff.symm

theorem atCorner (bound : AtMostTwo (restrictFamily D (Internal D side)))
    (k : Fin 4) (e : E) (ie : Internal D side e) (h : FamilyIncident D (S.v k) e) :
    e = S.e k ∨ e = S.e (k+3) := by
  have num : (k+3)+1 = k := by omega
  let a : {e // Internal D side e} := ⟨S.e k,S.internal k⟩
  let c : {e // Internal D side e} := ⟨S.e (k+3),S.internal _⟩
  have ha : FamilyIncident D (S.v k) (S.e k) := (S.incident ..).mpr (by rw [S.ends]; simp)
  have hc : FamilyIncident D (S.v k) (S.e (k+3)) := (S.incident ..).mpr (by rw [S.ends,num]; simp)
  rcases bound (S.v k) ⟨e,ie⟩ a c h ha hc with eq | eq | eq
  · exact Or.inl (congrArg Subtype.val eq)
  · exact Or.inr (congrArg Subtype.val eq)
  · have := S.injective (congrArg Subtype.val eq : S.e k = S.e (k+3))
    omega

theorem labels_unique (bound : AtMostTwo (restrictFamily D (Internal D side))) (k : Fin 4)
    {e : E} (pair : familyPair D e = s(S.v k,S.v (k+1))) : e = S.e k := by
  have ie : Internal D side e := by
    rcases Sym2.eq_iff.mp pair with ⟨l,r⟩ | ⟨l,r⟩ <;> simp [Internal,l,r,S.mono]
  rcases S.atCorner bound k e ie ((S.incident ..).mpr (by rw [pair]; simp)) with eq | eq
  · exact eq
  · have := (pair.symm.trans ((congrArg (familyPair D) eq).trans (S.ends (k+3))))
    rcases Sym2.eq_iff.mp this with ⟨h,_⟩ | ⟨_,h⟩ <;> have := S.v.injective h <;> omega

theorem next_in_square (bound : AtMostTwo (restrictFamily D (Internal D side)))
    (T : RawSquare D side b) (j : Fin 4) (start : ∃ k, T.v j = S.v k) :
    (∃ k, T.e j = S.e k) ∧ ∃ k, T.v (j+1) = S.v k := by
  obtain ⟨k,hk⟩ := start
  have touch : FamilyIncident D (S.v k) (T.e j) := by
    rw [← hk,T.incident,T.ends]; simp
  obtain ⟨k',edge⟩ : ∃ k', T.e j = S.e k' := (S.atCorner bound k _ (T.internal j) touch).elim
    (fun h => ⟨_,h⟩) (fun h => ⟨_,h⟩)
  refine ⟨⟨k',edge⟩,?_⟩
  have pair := (T.ends j).symm.trans ((congrArg (familyPair D) edge).trans (S.ends k'))
  rcases Sym2.eq_iff.mp pair with ⟨_,r⟩ | ⟨_,r⟩ <;> exact ⟨_,r⟩

theorem coincident (bound : AtMostTwo (restrictFamily D (Internal D side)))
    (T : RawSquare D side b) (meet : ∃ j k, T.v j = S.v k) :
    ∀ l, ∃ k, T.e l = S.e k := by
  obtain ⟨j,k,hk⟩ := meet
  have a := S.next_in_square bound T j ⟨k,hk⟩
  have c := S.next_in_square bound T (j+1) a.2
  have d := S.next_in_square bound T ((j+1)+1) c.2
  have u := S.next_in_square bound T (((j+1)+1)+1) d.2
  intro l
  have enum : ∀ j l : Fin 4, l = j ∨ l = j+1 ∨ l = (j+1)+1 ∨ l = ((j+1)+1)+1 := by decide
  rcases enum j l with rfl | rfl | rfl | rfl
  · exact a.1
  · exact c.1
  · exact d.1
  · exact u.1

end RawSquare

namespace Atlas
variable (A : Atlas D I X K)

theorem residual_reachable (f : X → Bool) (p q : I → Bool) (H : SimpleGraph V)
    (cross : ∀ x, H.Reachable (A.outside.left x) (A.outside.right x))
    (home : ∀ i (k l : Fin (A.shape i).vertices), H.Reachable (A.places ⟨i,k⟩) (A.places ⟨i,l⟩))
    {v w : V} (reach : (support (restrictFamily D (fun e => A.part f p q e ≠ .matching))).Reachable v w) :
    H.Reachable v w := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at reach
  induction reach with
  | refl => exact .refl _
  | tail _ edge ih =>
    apply ih.trans
    obtain ⟨⟨e,hm,pair⟩,_⟩ := (support_restrict ..).mp edge
    obtain ⟨z,rfl⟩ := A.labels.surjective e
    rcases z with x | t | ⟨i,k⟩
    · rcases Sym2.eq_iff.mp pair with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact cross x
      · exact (cross x).symm
    · simp at hm
    · have h := (A.endpoints i k).symm.trans pair
      rcases Sym2.eq_iff.mp h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> exact home _ _ _

end Atlas
end Kostochka.FiveRegular.Restoration

end

section 

namespace MultFive.Multi
open scoped Classical
open Finset Kostochka.FiveRegular Subdivision Restoration
variable {V : Type*} (m : Multi V)

private theorem internal_pair (side : V → Bool) {e : m.Edge} {u v : V} (h : e.1 = s(u,v)) :
    RawSquare.Internal m.family side e ↔ side u = side v := by
  rcases Sym2.eq_iff.mp ((m.family_pair e).trans h) with ⟨l,r⟩ | ⟨l,r⟩ <;> simp [RawSquare.Internal,l,r,eq_comm]

theorem card_inside_labels [Fintype V] [DecidableEq V] (side : V → Bool) (v : V) :
    Fintype.card {e : m.Edge // v ∈ e.1 ∧ RawSquare.Internal m.family side e} = m.insideDegree side v := by
  classical
  let L := Σ w : {w : V // side w = side v}, Fin (m.count v w)
  let pack (z : L) : {e : m.Edge // v ∈ e.1 ∧ RawSquare.Internal m.family side e} :=
    ⟨⟨s(v,z.1.val),z.2⟩,Sym2.mem_mk_left ..,(m.internal_pair side rfl).mpr z.1.property.symm⟩
  have bij : Function.Bijective pack := by
    constructor
    · rintro ⟨⟨a,ha⟩,j⟩ ⟨⟨b,hb⟩,k⟩ eq
      have pair : s(v,a) = s(v,b) := congrArg (fun t => t.val.1) eq
      have same : a = b := by rcases Sym2.eq_iff.mp pair with h|h <;> grind
      subst b
      have key : j.val = k.val := congrArg (fun t => t.val.2.val) eq
      exact congrArg (Sigma.mk _) (Fin.ext key)
    · rintro ⟨⟨z,k⟩,hv,hm⟩
      obtain ⟨w,rfl⟩ := Sym2.mem_iff_exists.mp hv
      have same : side v = side w := (m.internal_pair side rfl).mp hm
      exact ⟨⟨⟨w,same.symm⟩,k⟩,rfl⟩
  rw [← Fintype.card_congr (Equiv.ofBijective pack bij)]
  simp only [L,Fintype.card_sigma,Fintype.card_fin]
  rw [← Finset.sum_subtype (univ.filter fun w : V => side w = side v) (fun _ => by simp) (m.count v),Finset.sum_filter]
  rfl

theorem internal_atMostTwo [Fintype V] [DecidableEq V] (side : V → Bool) (bd : ∀ v, m.insideDegree side v ≤ 2) :
    AtMostTwo (restrictFamily m.family (RawSquare.Internal m.family side)) := by
  classical
  intro v e f g eh fh gh
  let L := {e : m.Edge // v ∈ e.1 ∧ RawSquare.Internal m.family side e}
  have hi : Fintype.card L ≤ 2 := (m.card_inside_labels side v) ▸ bd v
  have card : (Finset.univ : Finset L).card ≤ 2 := hi
  let mk (a : {e : m.Edge // RawSquare.Internal m.family side e}) (h : FamilyIncident m.family v a.val) : L :=
    ⟨a.val,(m.family_incident_iff v a.val).mp h,a.property⟩
  have eq {a b} {h k} (hab : mk a h = mk b k) : a = b := Subtype.ext (congrArg (fun x : L => x.val) hab)
  by_contra! ne
  exact (not_lt.mpr card) (Finset.two_lt_card_iff.mpr ⟨mk e eh,mk f fh,mk g gh,by simp,by simp,by simp,
    fun h => ne.1 (eq (h := eh) (k := fh) h),fun h => ne.2.1 (eq (h := eh) (k := gh) h),fun h => ne.2.2 (eq (h := fh) (k := gh) h)⟩)

end MultFive.Multi

end

section 

namespace Kostochka.FiveRegular.Restoration
open Subdivision Auxiliary

variable {V E I X K : Type*} {D : Family V E}
namespace Atlas
variable (A : Atlas D I X K)

theorem gap_ends (i : I) (k : Fin (A.shape i).edges) :
    familyPair D (A.localLabel i k) = s(A.vertex i k.val,A.vertex i (k.val+1)) := by
  rw [show familyPair D (A.localLabel i k) = _ from A.endpoints i k]
  have hk : k.val < (A.shape i).vertices := lt_of_lt_of_le k.isLt (A.shape i).edges_le_vertices
  have l : (A.shape i).family.left k = vertexAt (A.shape i) k.val := by
    apply Fin.ext; simp [Shape.family,vertexAt,Nat.mod_eq_of_lt hk]
  have r : (A.shape i).family.right k = vertexAt (A.shape i) (k.val+1) := by
    apply Fin.ext
    by_cases under : k.val+1 < (A.shape i).vertices
    · simp [Shape.family,vertexAt,under,Nat.mod_eq_of_lt under]
    · have atEnd : k.val+1 = (A.shape i).vertices := by omega
      simp [Shape.family,vertexAt,atEnd]
  rw [l,r]; rfl

def localSquare (side : V → Bool) (b : Bool) (i : I)
    (hv : (A.shape i).vertices = 4) (he : (A.shape i).edges = 4)
    (same : ∀ k : Fin 4, side (A.vertex i k.val) = b) : RawSquare D side b where
  v := ⟨fun k => A.vertex i k.val,by
    intro j k eq
    have hh := A.places.injective eq
    have hh' : vertexAt (A.shape i) j.val = vertexAt (A.shape i) k.val := eq_of_heq (Sigma.ext_iff.mp hh).2
    have val := congrArg Fin.val hh'
    exact Fin.ext (by simpa [vertexAt,hv,Nat.mod_eq_of_lt j.isLt,Nat.mod_eq_of_lt k.isLt] using val)⟩
  e k := A.localLabel i (Fin.cast he.symm k)
  mono := same
  ends k := by
    rw [A.gap_ends]
    change s(A.vertex i k.val,A.vertex i (k.val+1)) = _
    congr 1
    change A.places ⟨i,vertexAt (A.shape i) (k.val+1)⟩ = A.places ⟨i,vertexAt (A.shape i) (k+1 : Fin 4).val⟩
    congr 2
    apply Fin.ext
    simp [vertexAt,hv,Fin.val_add]

private theorem soleFactor (a c b : Bool) (j k : Fin 4) :
    asPart (Shape.alternatingSquare.role a c j.val) = .factor b →
    asPart (Shape.alternatingSquare.role a c k.val) = .factor b → j = k := by
  revert a c b j k
  decide

theorem covered_avoids_alternating (f : X → Bool) (p q : I → Bool) {side : V → Bool} {b : Bool}
    (S : RawSquare D side b) (bound : AtMostTwo (restrictFamily D (RawSquare.Internal D side)))
    (sides : ∀ i (k l : Fin (A.shape i).vertices), side (A.places ⟨i,k⟩) = side (A.places ⟨i,l⟩))
    (cover : ∀ j, A.part f p q (S.e j) = .factor b ∨ A.part f p q (S.e (j+3)) = .factor b)
    (i : I) (sq : A.shape i = .alternatingSquare) (a : Fin 4) : ¬ A.InPiece i (S.v a) := by
  rintro ⟨u,hu⟩
  have hv : (A.shape i).vertices = 4 := by rw [sq]; rfl
  have he : (A.shape i).edges = 4 := by rw [sq]; rfl
  have mono (k : Fin 4) : side (A.vertex i k.val) = b := (sides i _ u).trans (hu ▸ S.mono a)
  let T := A.localSquare side b i hv he mono
  have eq : T.v (Fin.cast hv u) = S.v a := by
    rw [hu]
    change A.places ⟨i,vertexAt (A.shape i) u.val⟩ = _
    congr 2
    apply Fin.ext; exact Nat.mod_eq_of_lt u.isLt
  have common := T.coincident bound S ⟨a,Fin.cast hv u,eq.symm⟩
  have only (j k : Fin 4) (jhit : A.part f p q (S.e j) = .factor b) (khit : A.part f p q (S.e k) = .factor b) : j = k := by
    obtain ⟨t,ht⟩ := common j
    obtain ⟨l,hl⟩ := common k
    rw [ht] at jhit
    rw [hl] at khit
    change A.part f p q (A.localLabel i (Fin.cast he.symm t)) = .factor b at jhit
    change A.part f p q (A.localLabel i (Fin.cast he.symm l)) = .factor b at khit
    rw [A.part_local] at jhit khit
    change asPart ((A.shape i).role (p i) (q i) t.val) = .factor b at jhit
    change asPart ((A.shape i).role (p i) (q i) l.val) = .factor b at khit
    rw [sq] at jhit khit
    have h := soleFactor (p i) (q i) b t l jhit khit
    exact S.injective (ht.trans (h ▸ hl.symm))
  rcases cover 0 with h | h <;> rcases cover 2 with c | c <;> have := only _ _ h c <;> contradiction

theorem matching_iff_old_at (f : X → Bool) (p q : I → Bool) {e : E} {v : V}
    (hit : FamilyIncident D v e) (avoid : ∀ i, A.shape i = .alternatingSquare → ¬ A.InPiece i v) :
    A.part f p q e = .matching ↔ A.oldMatching e = true := by
  obtain ⟨z,rfl⟩ := A.labels.surjective e
  rcases z with x | k | ⟨i,k⟩
  · simp [oldMatching]
  · simp [oldMatching]
  · have h : A.shape i ≠ .alternatingSquare := by
      intro hs
      rcases (A.localIncident i k v).mp hit with l | r <;> exact avoid i hs ⟨_,‹_›⟩
    change A.part f p q (A.localLabel i k) = .matching ↔ _
    rw [A.part_local]
    simp only [oldMatching,Equiv.symm_apply_apply,priorLocal,h,false_and,decide_false,Bool.false_eq_true,iff_false]
    have nom (s : Shape) (k : ℕ) (hs : s ≠ .alternatingSquare) :
        asPart (s.role (p i) (q i) k) ≠ .matching := by cases s <;> simp_all [Shape.role,asPart]
    exact nom _ _ h

end Atlas
end Kostochka.FiveRegular.Restoration

end

section 

namespace Kostochka.FiveRegular.Restoration
open Subdivision Auxiliary
variable {V E I X K : Type*} {D : Family V E}

namespace RawSquare
variable {side : V → Bool} {b : Bool}
def rotate (S : RawSquare D side b) (a : Fin 4) : RawSquare D side b where
  v := ⟨fun k => S.v (a+k),fun _ _ h => add_left_cancel (S.v.injective h)⟩
  e k := S.e (a+k)
  mono _ := S.mono _
  ends k := by
    change familyPair D (S.e (a+k)) = s(S.v (a+k),S.v (a+(k+1)))
    simpa [add_assoc] using S.ends (a+k)
end RawSquare

namespace Atlas
variable (A : Atlas D I X K)

structure SquareCatalog [DecidableEq V] (H : SimpleGraph V) (side : V → Bool) : Prop where
  bound : AtMostTwo (restrictFamily D (RawSquare.Internal D side))
  sides : ∀ i (k l : Fin (A.shape i).vertices), side (A.places ⟨i,k⟩) = side (A.places ⟨i,l⟩)
  two : ∀ {b} (S : RawSquare D side b), A.oldMatching (S.e 3) = true → A.oldMatching (S.e 1) = true →
    A.oldMatching (S.e 0) = false → A.oldMatching (S.e 2) = false → H.Reachable (S.v 0) (S.v 2) →
    ∃ i, A.shape i = .alternatingSquare ∧ A.InPiece i (S.v 0)
  one : ∀ {b} (S : RawSquare D side b), A.oldMatching (S.e 3) = true → A.oldMatching (S.e 0) = false →
    A.oldMatching (S.e 1) = false → A.oldMatching (S.e 2) = false →
    ∃ i, (A.shape i = .markedPath ∨ A.shape i = .badPath) ∧
      ((A.vertex i 0 = S.v 0 ∧ A.vertex i 1 = S.v 1 ∧ A.vertex i 2 = S.v 2 ∧ A.vertex i 3 = S.v 3) ∨
       (A.vertex i 0 = S.v 3 ∧ A.vertex i 1 = S.v 2 ∧ A.vertex i 2 = S.v 1 ∧ A.vertex i 3 = S.v 0))
  zero : ∀ {b} (S : RawSquare D side b), (∀ k, A.oldMatching (S.e k) = false) →
    ∃ i, A.shape i = .evenCycle 1 ∧ (∀ w, A.InPiece i w ↔ ∃ k, w = S.v k) ∧
      ({s(A.vertex i 0,A.vertex i 2),s(A.vertex i 1,A.vertex i 3)} : Finset (Sym2 V)) =
       {s(S.v 0,S.v 2),s(S.v 1,S.v 3)}

@[simp] theorem afterSquare_vertex (d : I → Bool) (i : I) (k : ℕ) :
    (A.afterSquareDecision d).vertex i k = A.vertex i k := by
  change A.places ⟨i,Fin.cast ((A.shape i).afterSquare_vertices (d i)) (vertexAt ((A.shape i).afterSquare (d i)) k)⟩ = _
  unfold vertex
  congr 2
  apply Fin.ext; simp [vertexAt]

private theorem pathNotFactor {s : Shape} (hs : s = .markedPath ∨ s = .badPath) (p q b : Bool) (j : ℕ)
    (hj : j = 0 ∨ j = 2) (norm : s = .markedPath → p = !b) : asPart (s.role p q j) ≠ .factor b := by
  rcases hs with rfl | rfl <;> rcases hj with rfl | rfl <;> simp_all [Shape.role,Shape.alt,asPart]

private theorem closing_not_matching [DecidableEq V] {H : SimpleGraph V} {side : V → Bool} {b : Bool}
    (C : A.SquareCatalog H side) (d : I → Bool) (f : X → Bool) (p q : I → Bool)
    (norm : ∀ i, A.shape i = .markedPath → p i = !(side (A.vertex i 0))) (S : RawSquare D side b)
    (cover : ∀ j, (A.afterSquareDecision d).part f p q (S.e j) = .factor b ∨
      (A.afterSquareDecision d).part f p q (S.e (j+3)) = .factor b)
    (reach : H.Reachable (S.v 0) (S.v 2)) : A.oldMatching (S.e 3) = false := by
  let B := A.afterSquareDecision d
  have commonSide i (k l : Fin (B.shape i).vertices) : side (B.places ⟨i,k⟩) = side (B.places ⟨i,l⟩) := C.sides i _ _
  have avoid i (hi : B.shape i = .alternatingSquare) (j : Fin 4) : ¬ B.InPiece i (S.v j) :=
    B.covered_avoids_alternating f p q S C.bound commonSide cover i hi j
  have matching j : B.part f p q (S.e j) = .matching ↔ A.oldMatching (S.e j) = true := by
    rw [← A.afterSquare_old d]
    exact B.matching_iff_old_at f p q ((S.incident j _).mpr (by rw [S.ends]; simp)) (fun i hi => avoid i hi j)
  by_contra! h3
  have h3 : A.oldMatching (S.e 3) = true := by simpa using h3
  have m3 := (matching 3).mpr h3
  have b0 : B.part f p q (S.e 0) = .factor b := (cover 0).resolve_right (by change B.part f p q (S.e 3) ≠ _; rw [m3]; simp)
  have b2 : B.part f p q (S.e 2) = .factor b := (cover 3).resolve_left (by rw [show (A.afterSquareDecision d).part f p q (S.e 3) = _ from m3]; simp)
  have notOld (j) (hj : B.part f p q (S.e j) = .factor b) : A.oldMatching (S.e j) = false := by
    by_contra! h
    rw [(matching j).mpr (by simpa using h)] at hj
    cases hj
  cases h1 : A.oldMatching (S.e 1) with
  | true =>
    obtain ⟨i,h,hv⟩ := C.two S h3 h1 (notOld 0 b0) (notOld 2 b2) reach
    exact avoid i (by simp [B,Shape.afterSquare,h]) 0 ((A.afterSquare_inPiece ..).mpr hv)
  | false =>
    obtain ⟨i,sh,align⟩ := C.one S h3 (notOld 0 b0) h1 (notOld 2 b2)
    have hs : B.shape i = A.shape i := by
      rcases sh with h|h <;> simp [B,Shape.afterSquare,h]
    have edges : 3 = (B.shape i).edges := by rw [hs]; rcases sh with h|h <;> rw [h] <;> rfl
    have ends (k : Fin 3) : familyPair D (B.localLabel i (Fin.cast edges k)) =
        s(A.vertex i k.val,A.vertex i (k.val+1)) := by
      rw [B.gap_ends]
      change s((A.afterSquareDecision d).vertex i k.val,(A.afterSquareDecision d).vertex i (k.val+1)) = _
      rw [A.afterSquare_vertex,A.afterSquare_vertex]
    have other (k : Fin 3) (out : k.val = 0 ∨ k.val = 2)
        (corner : side (A.vertex i 0) = b) : B.part f p q (B.localLabel i (Fin.cast edges k)) ≠ .factor b := by
      rw [B.part_local]
      change asPart ((B.shape i).role (p i) (q i) k.val) ≠ _
      rw [hs]
      exact pathNotFactor sh _ _ b _ out (fun h => by rw [norm i h,corner])
    rcases align with ⟨a,l,_,_⟩ | ⟨a,_,l,r⟩
    · have eq : B.localLabel i (Fin.cast edges 0) = S.e 0 := S.labels_unique C.bound 0 (by simpa [a,l] using ends 0)
      exact other 0 (Or.inl rfl) (a ▸ S.mono 0) (eq ▸ b0)
    · have eq : B.localLabel i (Fin.cast edges 2) = S.e 0 := S.labels_unique C.bound 0 (by
        have h := ends 2
        change familyPair D _ = s(A.vertex i 2,A.vertex i 3) at h
        rw [l,r,Sym2.eq_swap] at h
        exact h)
      exact other 2 (Or.inr rfl) (a ▸ S.mono 3) (eq ▸ b0)

theorem no_old_matching_on_covered_square [DecidableEq V] {H : SimpleGraph V} {side : V → Bool} {b : Bool}
    (C : A.SquareCatalog H side) (d : I → Bool) (f : X → Bool) (p q : I → Bool)
    (norm : ∀ i, A.shape i = .markedPath → p i = !(side (A.vertex i 0))) (S : RawSquare D side b)
    (cover : ∀ j, (A.afterSquareDecision d).part f p q (S.e j) = .factor b ∨
      (A.afterSquareDecision d).part f p q (S.e (j+3)) = .factor b)
    (reach : ∀ j, H.Reachable (S.v j) (S.v (j+2))) :
    ∀ j, A.oldMatching (S.e j) = false := by
  intro j
  let a := j+1
  have h := A.closing_not_matching C d f p q norm (S.rotate a)
    (fun k => by simpa [RawSquare.rotate,add_assoc] using cover (a+k)) (by change H.Reachable (S.v (a+0)) (S.v (a+2)); simpa using reach a)
  change A.oldMatching (S.e ((j+1)+3)) = false at h
  exact (show (j+1)+3 = j by omega) ▸ h

end Atlas
end Kostochka.FiveRegular.Restoration

end

section 

namespace Kostochka.FiveRegular.Restoration
open Subdivision Auxiliary
variable {V E I X K : Type*} {D : Family V E}

namespace RawSquare
variable {side : V → Bool} {b : Bool}

noncomputable def ofSupport (v : Fin 4 ↪ V) (hs : ∀ j, side (v j) = b)
    (cycle : ∀ j, (support D).Adj (v j) (v (j+1))) : RawSquare D side b where
  v := v
  e j := (cycle j).1.choose
  mono := hs
  ends j := (cycle j).1.choose_spec

theorem cover_of_support (S : RawSquare D side b)
    (bound : AtMostTwo (restrictFamily D (Internal D side))) (keep : E → Prop)
    (cover : ∀ j, (support (restrictFamily D keep)).Adj (S.v j) (S.v (j+1)) ∨
      (support (restrictFamily D keep)).Adj (S.v j) (S.v (j+3))) :
    ∀ j, keep (S.e j) ∨ keep (S.e (j+3)) := by
  intro j
  rcases cover j with ha | ha
  · obtain ⟨⟨e,he,eq⟩,_⟩ := (support_restrict ..).mp ha
    exact Or.inl ((S.labels_unique bound j eq) ▸ he)
  · obtain ⟨⟨e,he,eq⟩,_⟩ := (support_restrict ..).mp ha
    have h : ((j+3)+1) = j := by omega
    have pair : familyPair D e = s(S.v (j+3),S.v ((j+3)+1)) := by rw [eq,h,Sym2.eq_swap]
    exact Or.inr ((S.labels_unique bound (j+3) pair) ▸ he)

end RawSquare

namespace Atlas
variable (A : Atlas D I X K)

theorem exceptional_corner [DecidableEq V] {H : SimpleGraph V} {side : V → Bool} {b : Bool}
    (C : A.SquareCatalog H side) (f : X → Bool) (p q : I → Bool)
    (norm : ∀ i, A.shape i = .markedPath → p i = !(side (A.vertex i 0))) (S : RawSquare D side b)
    (cover : ∀ j, (A.afterSquareDecision (A.squareDecision f side)).part f p q (S.e j) = .factor b ∨
      (A.afterSquareDecision (A.squareDecision f side)).part f p q (S.e (j+3)) = .factor b)
    (reach : ∀ j, H.Reachable (S.v j) (S.v (j+2)))
    (w : Fin 2 → V) (outside : ∀ t j, w t ≠ S.v j)
    (spokes : ∀ k : Fin 4, ∃ e, (A.afterSquareDecision (A.squareDecision f side)).part f p q e = .factor b ∧
      familyPair D e = s(S.v k,w ⟨k.val % 2,by omega⟩)) :
    ∃ j e, (A.afterSquareDecision (A.squareDecision f side)).part f p q e = .exceptional ∧
      FamilyIncident D (S.v j) e := by
  let d := A.squareDecision f side
  let B := A.afterSquareDecision d
  have all := A.no_old_matching_on_covered_square C d f p q norm S cover reach
  obtain ⟨i,sh,verts,diag⟩ := C.zero S all
  have hin (j : Fin 4) := (verts (S.v j)).mpr ⟨j,rfl⟩
  have own : A.InPiece i (A.vertex i 0) := ⟨_,rfl⟩
  obtain ⟨a,eq⟩ := (verts _).mp own
  have test := A.divert_of_factor_spokes f p q side d i S.v b (eq ▸ S.mono a) hin diag w
    (fun t h => by obtain ⟨j,e⟩ := (verts _).mp h; exact outside t j e) spokes
  have n : 0 < (B.shape i).edges := by simp [B,d,sh,test,Shape.afterSquare,Shape.edges]
  let k : Fin (B.shape i).edges := ⟨0,n⟩
  refine ⟨a,B.localLabel i k,A.exceptional_of_spoke_decision f p q side i sh test k,?_⟩
  apply (S.incident a _).mpr
  rw [B.gap_ends]
  change S.v a ∈ s(B.vertex i 0,B.vertex i 1)
  rw [show B.vertex i 0 = A.vertex i 0 from A.afterSquare_vertex d i 0,eq]; simp

theorem no_ordinary_square {V : Type} {D : Family V E} (A : Atlas D I X K)
    [DecidableEq V] {H : SimpleGraph V} {side : V → Bool} (b : Bool)
    (C : A.SquareCatalog H side) (f : X → Bool) (p q : I → Bool)
    (norm : ∀ i, A.shape i = .markedPath → p i = !(side (A.vertex i 0)))
    (G : SimpleGraph V) (base : G ≤ support D) (mark : V → Bool)
    (mono : ∀ v, mark v = true → side v = b)
    (ordinary : ∀ v, mark v = true → ∀ e, FamilyIncident D v e →
      (A.afterSquareDecision (A.squareDecision f side)).part f p q e ≠ .exceptional)
    (connected : ∀ u v, (support (restrictFamily D (fun e =>
      (A.afterSquareDecision (A.squareDecision f side)).part f p q e = .factor b))).Adj u v → H.Reachable u v) :
    NoOrdinarySquare G (support (restrictFamily D (fun e =>
      (A.afterSquareDecision (A.squareDecision f side)).part f p q e = .factor b))) mark := by
  intro v hm cy cov x y hx hy e0 e2 e1 e3
  let B := A.afterSquareDecision (A.squareDecision f side)
  let S := RawSquare.ofSupport v (fun j => mono _ (hm j)) (fun j => base (cy j))
  let w : Fin 2 → V := ![x,y]
  have out (j : Fin 2) (k : Fin 4) : w j ≠ S.v k := by
    have hn : mark (w j) = false := by fin_cases j <;> first | exact hx | exact hy
    exact fun eq => Bool.noConfusion (hn.symm.trans (eq ▸ hm k))
  have pairs (k : Fin 4) : (support (restrictFamily D (fun e => B.part f p q e = .factor b))).Adj
      (S.v k) (w ⟨k.val % 2,by omega⟩) := by
    fin_cases k <;> first | exact e0 | exact e1 | exact e2 | exact e3
  have reach (k : Fin 4) : H.Reachable (S.v k) (S.v (k+2)) := by
    have zero := (connected _ _ e0).trans (connected _ _ e2).symm
    have one := (connected _ _ e1).trans (connected _ _ e3).symm
    fin_cases k <;> first | exact zero | exact one | exact zero.symm | exact one.symm
  have ⟨j,e,exc,hit⟩ := A.exceptional_corner C f p q norm S
    (S.cover_of_support C.bound (fun e => B.part f p q e = .factor b) cov) reach w out
    (fun k => ((support_restrict ..).mp (pairs k)).1)
  exact ordinary _ (hm j) e hit exc

end Atlas
end Kostochka.FiveRegular.Restoration

end

section 

namespace MultFive.Multi.PieceDecomposition
open Finset SimpleGraph Kostochka.FiveRegular Subdivision Restoration Auxiliary Kostochka.Four.PathCover
variable {V : Type*} [Fintype V] [DecidableEq V] {m : Multi V} {M : m.support.Subgraph} {side : V → Bool}
variable (D : PieceDecomposition m M side) (L : D.LabelCoverage)

theorem physical_inPiece (i : D.Index) (v : V) : (D.physical L).InPiece i v ↔ v ∈ (D.raw i).verts := by
  constructor
  · rintro ⟨k,rfl⟩
    exact D.position_mem i k
  · intro h
    obtain ⟨k,hk⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp h)
    exact ⟨Fin.cast (D.raw i).baseShape_size.symm k,hk.symm⟩

theorem physical_vertex_of_get (i : D.Index) (k : ℕ) {v : V}
    (h : (D.raw i).vertsList[k]? = some v) : (D.physical L).vertex i k = v := by
  obtain ⟨hk,eq⟩ := List.getElem?_eq_some_iff.mp h
  change D.positions ⟨i,vertexAt (D.rawShape i) k⟩ = _
  rw [D.position_formula]
  have under : k < (D.rawShape i).vertices := by change k < (D.raw i).baseShape.vertices; rwa [(D.raw i).baseShape_size]
  change (D.raw i).vertsList[k % (D.rawShape i).vertices]'(by rwa [Nat.mod_eq_of_lt under]) = v
  simpa [Nat.mod_eq_of_lt under] using eq

private theorem oldPair {b : Bool} (S : RawSquare m.family side b) (j : Fin 4)
    (h : (D.physical L).oldMatching (S.e j) = true) : M.Adj (S.v j) (S.v (j+1)) := by
  have hp := ((D.physical_tag L _).mp h).1
  have he : (S.e j).1 = s(S.v j,S.v (j+1)) := (m.family_pair _).symm.trans (S.ends j)
  rwa [he] at hp

private theorem freePair {b : Bool} (S : RawSquare m.family side b) (j : Fin 4)
    (h : (D.physical L).oldMatching (S.e j) = false) : 0 < (m.residual M).count (S.v j) (S.v (j+1)) := by
  have free : ¬ isMatchingEdge m M (S.e j) := fun k => Bool.noConfusion ((h.symm.trans ((D.physical_tag L _).mpr k)))
  let r := (residualEdgeEquiv m M).symm ⟨S.e j,free⟩
  have label : (residualEdgeEquiv m M r).val = S.e j := congrArg Subtype.val ((residualEdgeEquiv m M).apply_symm_apply ⟨_,free⟩)
  have pair : r.1 = s(S.v j,S.v (j+1)) := (residualEdgeEquiv_fst m M r).symm.trans
    ((congrArg Sigma.fst label).trans ((m.family_pair _).symm.trans (S.ends j)))
  have positive := Nat.zero_lt_of_lt r.2.isLt
  rwa [pair] at positive

theorem badPath_closing (d : D.Index → Bool) (i : D.Index)
    (bad : ((D.physical L).afterSquareDecision d).shape i = .badPath) :
    ∃ e, familyPair m.family e =
      s(((D.physical L).afterSquareDecision d).vertex i 0,((D.physical L).afterSquareDecision d).vertex i 3) := by
  rw [Atlas.afterSquare_vertex,Atlas.afterSquare_vertex]
  have shape : (D.raw i).baseShape = .badPath := by
    change ((D.raw i).baseShape.afterSquare (d i)) = _ at bad
    unfold Shape.afterSquare at bad
    split at bad
    · contradiction
    · exact bad
  have raw : ∃ q, D.raw i = .badPath q false := by
    cases h : D.raw i with
    | badPath q flag => cases flag <;> first | exact ⟨_,rfl⟩ | simp [h,ResidualPiece.baseShape] at shape
    | badOddCycle q flag => cases flag <;> simp [h,ResidualPiece.baseShape] at shape
    | _ => simp [h,ResidualPiece.baseShape] at shape
  obtain ⟨q,raw⟩ := raw
  have a : (D.physical L).vertex i 0 = q.v1 := D.physical_vertex_of_get L i 0 (by rw [raw]; rfl)
  have b : (D.physical L).vertex i 3 = q.v4 := D.physical_vertex_of_get L i 3 (by rw [raw]; rfl)
  rw [a,b]
  exact ⟨⟨s(q.v1,q.v4),⟨0,M.adj_sub q.match14⟩⟩,m.family_pair _⟩

theorem squareCatalog (bound : ∀ v, m.insideDegree side v ≤ 2) :
    (D.physical L).SquareCatalog (m.residual M).support side := by
  classical
  constructor
  · exact m.internal_atMostTwo side bound
  · intro i k l
    exact (D.position_side i k).trans (D.position_side i l).symm
  · intro b S h3 h1 h0 h2 reach
    have nn : ([0,1,2,3] : List (Fin 4)).Nodup := by decide
    obtain ⟨q,mem,corner⟩ := D.complete_twoBadQuad b (S.v 0) (S.v 1) (S.v 2) (S.v 3) (nn.map S.v.injective)
      (S.mono 0) (S.mono 1) (S.mono 2) (S.mono 3) (D.oldPair L S 3 h3).symm (D.oldPair L S 1 h1)
      (D.freePair L S 0 h0) (D.freePair L S 2 h2) reach
    obtain ⟨i,raw⟩ := List.mem_iff_get.mp mem
    change D.raw i = _ at raw
    refine ⟨i,?_,(D.physical_inPiece L i _).mpr ?_⟩
    · change (D.raw i).baseShape = _; rw [raw]; rfl
    · rwa [raw]
  · intro b S h3 h0 h1 h2
    have nn : ([0,1,2,3] : List (Fin 4)).Nodup := by decide
    obtain ⟨p,mk,mem,order⟩ := D.complete_badPath b (S.v 0) (S.v 1) (S.v 2) (S.v 3) (nn.map S.v.injective)
      (S.mono 0) (S.mono 1) (S.mono 2) (S.mono 3) (D.oldPair L S 3 h3).symm
      (D.freePair L S 0 h0) (D.freePair L S 1 h1) (D.freePair L S 2 h2)
    obtain ⟨i,raw⟩ := List.mem_iff_get.mp mem
    change D.raw i = _ at raw
    have vertex (k : ℕ) (v : V) (get : [p.v1,p.v2,p.v3,p.v4][k]? = some v) :
        (D.physical L).vertex i k = v := D.physical_vertex_of_get L i k (by rw [raw]; exact get)
    refine ⟨i,?_,?_⟩
    · change (D.raw i).baseShape = _ ∨ (D.raw i).baseShape = _
      rw [raw]; cases mk <;> exact (by first | exact Or.inl rfl | exact Or.inr rfl)
    · simpa only [vertex 0 _ rfl,vertex 1 _ rfl,vertex 2 _ rfl,vertex 3 _ rfl] using order
  · intro b S hs
    have nn : ([0,1,2,3] : List (Fin 4)).Nodup := by decide
    obtain ⟨q,mem,verts,diag,_⟩ := D.complete_zeroBadSquare b (S.v 0) (S.v 1) (S.v 2) (S.v 3) (nn.map S.v.injective)
      (S.mono 0) (S.mono 1) (S.mono 2) (S.mono 3) (D.freePair L S 0 (hs 0)) (D.freePair L S 1 (hs 1))
      (D.freePair L S 2 (hs 2)) (D.freePair L S 3 (hs 3))
    obtain ⟨i,raw⟩ := List.mem_iff_get.mp mem
    change D.raw i = _ at raw
    have vertex (k : ℕ) (v : V) (get : [q.v1,q.v2,q.v3,q.v4][k]? = some v) :
        (D.physical L).vertex i k = v := D.physical_vertex_of_get L i k (by rw [raw]; exact get)
    refine ⟨i,?_,?_,?_⟩
    · change (D.raw i).baseShape = _; rw [raw]; rfl
    · intro w
      rw [D.physical_inPiece,raw]
      have set : (ResidualPiece.zeroBadSquare q).verts = q.verts := by
        ext t; simp [ZeroBadSquare.verts,ResidualPiece.verts,ResidualPiece.vertsList,ZeroBadSquare.vertsList]
      rw [set,verts]
      simp only [Finset.mem_insert,Finset.mem_singleton]
      constructor
      · rintro (h|h|h|h)
        · exact ⟨0,h⟩
        · exact ⟨1,h⟩
        · exact ⟨2,h⟩
        · exact ⟨3,h⟩
      · rintro ⟨k,rfl⟩; fin_cases k <;> simp
    · simpa only [vertex 0 _ rfl,vertex 1 _ rfl,vertex 2 _ rfl,vertex 3 _ rfl] using diag

theorem restored_reachable (d : D.Index → Bool) (f : Exterior m M side → Bool) (p q : D.Index → Bool)
    {u v : V} (h : (Kostochka.FiveRegular.support (restrictFamily m.family (fun e =>
      ((D.physical L).afterSquareDecision d).part f p q e ≠ .matching))).Reachable u v) :
    (m.residual M).support.Reachable u v := by
  apply ((D.physical L).afterSquareDecision d).residual_reachable f p q _ _ _ h
  · intro x
    rw [Atlas.afterSquare_outside,D.physical_outside]
    exact ConnectedComponent.exact ((m.residual M).cross_ends side x)
  · intro i k l
    change (m.residual M).support.Reachable (D.positions ⟨i,_⟩) (D.positions ⟨i,_⟩)
    exact ConnectedComponent.exact ((D.position_home i _).trans (D.position_home i _).symm)

theorem restored_factor_within (d : D.Index → Bool) (f : Exterior m M side → Bool) (p q : D.Index → Bool)
    (b : Bool) {u v : V} (h : (Kostochka.FiveRegular.support (factorFamily m.family
      (((D.physical L).afterSquareDecision d).part f p q) b)).Adj u v) :
    (m.residual M).support.Reachable u v := by
  apply D.restored_reachable L d f p q
  apply Adj.reachable
  obtain ⟨⟨e,eq⟩,ne⟩ := h
  apply (support_restrict ..).mpr
  exact ⟨⟨e.val,by rw [e.property]; simp,eq⟩,ne⟩

theorem physical_no_ordinary_square {V : Type} [Fintype V] [DecidableEq V]
    {m : Multi V} {M : m.support.Subgraph} {side : V → Bool} (D : PieceDecomposition m M side) (L : D.LabelCoverage)
    (P : (D.physical L).PartitionColors side) (bound : ∀ v, m.insideDegree side v ≤ 2) (b : Bool) :
    let A := D.physical L
    let part := (A.afterSquareDecision (A.squareDecision P.exterior side)).part P.exterior P.first P.second
    let mark := ordinaryAt side (fun v => ∃ e, part e = .exceptional ∧ FamilyIncident m.family v e) b
    NoOrdinarySquare (ordinaryGraph (Kostochka.FiveRegular.support m.family) mark) (Kostochka.FiveRegular.support (factorFamily m.family part b)) mark := by
  dsimp only
  apply (D.physical L).no_ordinary_square b (D.squareCatalog L bound) P.exterior P.first P.second
  · intro i hi; apply P.normalized; simp [hi,Atlas.markedShape]
  · exact fun _ _ h => h.1
  · exact fun v hv => ((ordinaryAt_iff ..).mp hv).1
  · intro v hv e hit eq
    exact ((ordinaryAt_iff ..).mp hv).2 ⟨e,eq,hit⟩
  · exact fun u v h => D.restored_factor_within L _ _ _ _ b h

end MultFive.Multi.PieceDecomposition

end

section 

namespace Kostochka.FiveRegular.Restoration

open SimpleGraph Finset Subdivision Auxiliary Four.PathCover

variable {V E I X K : Type*} {D : Family V E}

section Count
variable [Fintype E] [DecidableEq V]

noncomputable def selectedSet (D : Family V E) (sel : E → Bool) (v : V) : Finset E := by
  classical exact univ.filter (fun e => sel e = true ∧ FamilyIncident D v e)

omit [DecidableEq V] in
@[simp] theorem selectedSet_mem (D : Family V E) (sel : E → Bool) (v : V) (e : E) :
    e ∈ selectedSet D sel v ↔ sel e = true ∧ FamilyIncident D v e := by classical simp [selectedSet]

theorem selectedSet_card_le (D : Family V E) (sel : E → Bool) (v : V) :
    (selectedSet D sel v).card ≤ coloredDegree D sel v true := by
  classical
  let L := univ.filter (fun e => v = D.left e ∧ sel e = true)
  let R := univ.filter (fun e => v = D.right e ∧ sel e = true)
  have cover : selectedSet D sel v ⊆ L ∪ R := by
    intro e he
    obtain ⟨s,h|h⟩ := (selectedSet_mem _ _ _ _).mp he
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,h,s⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,h,s⟩)
  exact (card_le_card cover).trans ((card_union_le _ _).trans (by simp [L,R,coloredDegree]))

theorem atMostTwo_selected (D : Family V E) (keep : E → Prop) [DecidablePred keep]
    (hd : ∀ v, coloredDegree D (fun e => decide (keep e)) v true ≤ 2) : AtMostTwo (restrictFamily D keep) := by
  classical
  intro v e f g ie jf kg
  have hit (x : {e // keep e}) (h : FamilyIncident D v x.val) :
      x.val ∈ selectedSet D (fun e => decide (keep e)) v := (selectedSet_mem ..).mpr ⟨by simp [x.property],h⟩
  by_contra! hn
  have gt := two_lt_card_iff.mpr ⟨e.val,f.val,g.val,hit e ie,hit f jf,hit g kg,
    fun eq => hn.1 (Subtype.ext eq),fun eq => hn.2.1 (Subtype.ext eq),fun eq => hn.2.2 (Subtype.ext eq)⟩
  exact (not_lt.mpr ((selectedSet_card_le ..).trans (hd v))) gt
end Count

namespace Atlas
variable (A : Atlas D I X K)

theorem local_mono (side : V → Bool) (mono : ∀ i (v : Fin (A.shape i).vertices),
    side (A.places ⟨i,v⟩) = A.pieceSide side i) (i : I) (k : Fin (A.shape i).edges) :
    RawSquare.Internal D side (A.localLabel i k) := by
  rcases Sym2.eq_iff.mp (A.endpoints i k) with ⟨a,b⟩|⟨a,b⟩ <;> exact (congrArg side a).trans
    ((mono _ _).trans ((mono _ _).symm.trans (congrArg side b).symm))

theorem crossing_old (side : V → Bool) (mono : ∀ i (v : Fin (A.shape i).vertices),
    side (A.places ⟨i,v⟩) = A.pieceSide side i) (f : X → Bool) (p q : I → Bool)
    {e : E} {b} (he : A.part f p q e = .factor b) (cross : ¬ RawSquare.Internal D side e) :
    A.oldMatching e = false := by
  obtain ⟨z,rfl⟩ := A.labels.surjective e
  rcases z with x|k|⟨i,j⟩
  · simp [oldMatching]
  · simp at he
  · exact (cross (A.local_mono side mono i j)).elim

theorem local_of_internal (side : V → Bool) (cross : ∀ x, side (A.outside.left x) ≠ side (A.outside.right x))
    {e : E} (internal : RawSquare.Internal D side e) (untouched : ∀ k, e ≠ A.labels (.inr (.inl k)))
    {i : I} {v : Fin (A.shape i).vertices} (hit : FamilyIncident D (A.places ⟨i,v⟩) e) :
    ∃ r, e = A.localLabel i r := by
  obtain ⟨z,rfl⟩ := A.labels.surjective e
  rcases z with x|k|⟨j,r⟩
  · exact (cross x internal).elim
  · exact (untouched k rfl).elim
  · obtain rfl := A.samePieceOfIncident hit
    exact ⟨r,rfl⟩

theorem partner_apart (side : V → Bool) (f : X → Bool) (p q : I → Bool) (b : Bool)
    (loop : Loopless D)
    (mono : ∀ i (v : Fin (A.shape i).vertices), side (A.places ⟨i,v⟩) = A.pieceSide side i)
    (cross : ∀ x, side (A.outside.left x) ≠ side (A.outside.right x))
    (e : {e // A.part f p q e = .factor b}) :
    D.left e.val ≠ A.partner side p b (D.right e.val) := by
  intro eq
  obtain ⟨⟨i,v⟩,hv⟩ := A.places.surjective (D.right e.val)
  rw [← hv,A.partner_at] at eq
  by_cases hs : A.pieceSide side i = b
  · exact loop e.val ((if_pos hs ▸ eq).trans hv)
  rw [if_neg hs] at eq
  have mv : (A.shape i).partnerCoordinate (p i) b v ≠ v := fun h => loop e.val ((h ▸ eq).trans hv)
  have exc := (A.shape i).partnerCoordinate_exceptional _ _ _ mv
  have internal : RawSquare.Internal D side e.val := (congrArg side eq).trans
    ((mono i _).trans ((mono i v).symm.trans (congrArg side hv)))
  obtain ⟨r,hr⟩ := A.local_of_internal _ cross internal (fun k h => by
    have g := e.property; rw [h,A.part_untouched] at g; contradiction) (Or.inr hv : FamilyIncident D (A.places ⟨i,v⟩) e.val)
  have bad : A.part f p q (A.localLabel i r) = .exceptional := by
    apply (A.exceptional_iff ..).mpr
    refine ⟨i,r,rfl,?_⟩
    cases h : A.shape i <;> simp_all [Shape.exceptionalShape]
  have good := e.property
  rw [hr,bad] at good
  contradiction

theorem saturated_of_old_edges (side : V → Bool)
    (cross : ∀ x, side (A.outside.left x) ≠ side (A.outside.right x))
    {v : V} {e f : E} (ne : e ≠ f) (he : A.oldMatching e = false) (hf : A.oldMatching f = false)
    (ie : RawSquare.Internal D side e) (jf : RawSquare.Internal D side f)
    (ve : FamilyIncident D v e) (vf : FamilyIncident D v f) : A.Saturated v := by
  classical
  obtain ⟨⟨i,v⟩,rfl⟩ := A.places.surjective v
  obtain ⟨r,rfl⟩ := A.local_of_internal _ cross ie (fun k h => by simp [h,oldMatching] at he) ve
  obtain ⟨s,rfl⟩ := A.local_of_internal _ cross jf (fun k h => by simp [h,oldMatching] at hf) vf
  let sh := A.shape i
  let select (k : Fin sh.edges) := decide (sh ≠ .alternatingSquare ∨ k.val % 2 = 0)
  have mem (k : Fin sh.edges) (h : A.oldMatching (A.localLabel i k) = false)
      (inc : FamilyIncident D (A.places ⟨i,v⟩) (A.localLabel i k)) :
      k ∈ selectedSet sh.family select v := by
    apply (selectedSet_mem ..).mpr
    refine ⟨?_,(A.sameLocalIncident _ _ _).mp inc⟩
    simp only [oldMatching,localLabel,Equiv.symm_apply_apply,priorLocal,decide_eq_false_iff_not] at h
    by_cases different : sh ≠ .alternatingSquare
    · simp [select,different]
    · have same : A.shape i = .alternatingSquare := not_ne_iff.mp different
      simp [same] at h
      simp [select,sh,same]; omega
  have lo : 1 < (selectedSet sh.family select v).card :=
    one_lt_card.mpr ⟨r,mem r he ve,s,mem s hf vf,fun eq => ne (congrArg _ eq)⟩
  have lb := lo.trans_le (selectedSet_card_le sh.family select v)
  have exactDegree : coloredDegree sh.family select v true = oldDegree sh v.val :=
    sh.coloredDegree_family (fun k => decide (sh ≠ .alternatingSquare ∨ k % 2 = 0)) v
  have ub : oldDegree sh v.val ≤ 2 := by unfold oldDegree Shape.inc; split_ifs <;> omega
  unfold Saturated
  rw [A.places.symm_apply_apply]
  change oldDegree sh v.val = 2
  omega

variable [DecidableEq V] [Fintype I] [Fintype X] [Fintype K] [Fintype E]

omit [Fintype I] [Fintype E] [Fintype K] in
theorem atlas_internal_matching {side : V → Bool} (C : A.PartitionColors side) (exc : V → Prop) (b : Bool)
    (mono : ∀ i (v : Fin (A.shape i).vertices), side (A.places ⟨i,v⟩) = A.pieceSide side i)
    (cross : ∀ x, side (A.outside.left x) ≠ side (A.outside.right x)) :
    InternalMatching (factorFamily D (A.part C.exterior C.first C.second) b) (ordinaryAt side exc b) := by
  classical
  intro w hm e f he hf hel her hfl hfr
  obtain ⟨⟨i,v⟩,rfl⟩ := A.places.surjective w
  have loc (z : {z // A.part C.exterior C.first C.second z = .factor b})
      (hit : FamilyIncident D (A.places ⟨i,v⟩) z.val)
      (l : ordinaryAt side exc b (D.left z.val) = true) (r : ordinaryAt side exc b (D.right z.val) = true) :
      ∃ j, z.val = A.localLabel i j := A.local_of_internal _ cross
        (((ordinaryAt_iff ..).mp l).1.trans ((ordinaryAt_iff ..).mp r).1.symm)
        (fun k h => by have g := z.property; rw [h,A.part_untouched] at g; contradiction) hit
  obtain ⟨r,hr⟩ := loc e he hel her
  obtain ⟨s,hs⟩ := loc f hf hfl hfr
  let sh := A.shape i
  let sel (j : Fin sh.edges) := decide (sh.role (C.first i) (C.second i) j.val = .factor b)
  have good (z : {z // A.part C.exterior C.first C.second z = .factor b}) (j : Fin sh.edges)
      (h : z.val = A.localLabel i j) (touch : FamilyIncident D (A.places ⟨i,v⟩) z.val) :
      j ∈ selectedSet sh.family sel v := by
    have g := z.property
    rw [h,A.part_local] at g
    have role : (sh.role (C.first i) (C.second i) j.val) = .factor b := by
      cases t : sh.role (C.first i) (C.second i) j.val <;> simpa [← t] using g
    exact (selectedSet_mem ..).mpr ⟨by simp [sel,role],(A.sameLocalIncident ..).mp (h ▸ touch)⟩
  have same : A.pieceSide side i = b := (mono i v).symm.trans (((ordinaryAt_iff ..).mp hm).1)
  have bounded := sh.inside_at_most_one (C.first i) (C.second i) b v (fun ⟨n,hn⟩ => by
    have norm := C.normalized i (by change markedShape sh = true; rw [hn]; rfl)
    change C.first i = !(A.pieceSide side i) at norm
    rw [norm,same]; exact Bool.not_ne_self _)
  have cnt := selectedSet_card_le sh.family sel v
  have eq : coloredDegree sh.family sel v true = sh.factorDegree (C.first i) (C.second i) v.val b :=
    sh.coloredDegree_family (fun j => decide (sh.role (C.first i) (C.second i) j = .factor b)) v
  have pairs := card_le_one.mp (cnt.trans (eq ▸ bounded)) _ (good e r hr he) _ (good f s hs hf)
  exact Subtype.ext (hr.trans ((congrArg (A.localLabel i) pairs).trans hs.symm))

end Atlas
end Kostochka.FiveRegular.Restoration

end

section 

namespace Kostochka.FiveRegular.Restoration

open SimpleGraph Finset Subdivision Auxiliary Four.PathCover

variable {V E I X K : Type*} {D : Family V E}

def componentClosure (H : SimpleGraph V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ H.Reachable x y
  symm.symm _ _ h := ⟨h.1.symm,h.2.symm⟩
  loopless.irrefl _ h := h.1 rfl

theorem closure_reachable (H : SimpleGraph V) {x y : V} :
    (componentClosure H).Reachable x y ↔ H.Reachable x y := by
  constructor
  · intro h
    rw [reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact .refl _
    | tail _ e ih => exact ih.trans e.2
  · intro h
    by_cases eq : x = y
    · exact eq ▸ Reachable.refl x
    · exact (show (componentClosure H).Adj x y from ⟨eq,h⟩).reachable

theorem inside_support_bound [Fintype V] [DecidableEq V] (D : Family V E) (side : V → Bool)
    (bound : AtMostTwo (restrictFamily D (RawSquare.Internal D side))) (v : V) :
    insideDegree (support D) side v ≤ 2 := by
  classical
  let S := support (restrictFamily D (RawSquare.Internal D side))
  change (univ.filter (fun w => (support D).Adj v w ∧ side v = side w)).card ≤ 2
  apply (card_le_card (t := S.neighborFinset v) _).trans (by simpa using degree_support_le_two _ bound v)
  intro w hw
  obtain ⟨⟨⟨e,eq⟩,ne⟩,same⟩ := (mem_filter.mp hw).2
  apply (S.mem_neighborFinset ..).mpr
  apply (support_restrict ..).mpr
  refine ⟨⟨e,?_,eq⟩,ne⟩
  rcases Sym2.eq_iff.mp eq with ⟨h,j⟩|⟨h,j⟩ <;> simp_all [RawSquare.Internal]

namespace Atlas
variable (A : Atlas D I X K)

theorem factor_reachable (f : X → Bool) (p q : I → Bool) (b : Bool) (H : SimpleGraph V)
    (cross : ∀ x, H.Reachable (A.outside.left x) (A.outside.right x))
    (home : ∀ i (v w : Fin (A.shape i).vertices), H.Reachable (A.places ⟨i,v⟩) (A.places ⟨i,w⟩))
    {u v : V} (ad : (support (factorFamily D (A.part f p q) b)).Adj u v) : H.Reachable u v := by
  obtain ⟨⟨e,he,pair⟩,hn⟩ := (support_restrict D (fun e => A.part f p q e = .factor b)).mp ad
  have r : (support (restrictFamily D (fun e => A.part f p q e ≠ .matching))).Adj u v :=
    (support_restrict ..).mpr ⟨⟨e,by rw [he]; simp,pair⟩,hn⟩
  exact A.residual_reachable f p q H cross home r.reachable

theorem exceptional_of_incidence (f : X → Bool) (p q : I → Bool) {v : V} {e : E}
    (hit : FamilyIncident D v e) (ep : A.part f p q e = .exceptional) : A.exceptionalAt v := by
  obtain ⟨⟨i,k⟩,rfl⟩ := A.places.surjective v
  have sh := ((A.incident_exceptional_iff f p q i k e).mp ⟨ep,hit⟩).1
  unfold exceptionalAt pieceOf
  rw [A.places.symm_apply_apply]
  rcases sh with s|⟨n,s⟩|s <;> simp [s,Shape.exceptionalShape]

theorem square_factor_neighbor (side : V → Bool) (f : X → Bool) (p q : I → Bool) (b : Bool)
    (mono : ∀ i (v : Fin (A.shape i).vertices), side (A.places ⟨i,v⟩) = A.pieceSide side i)
    (cross : ∀ x, side (A.outside.left x) ≠ side (A.outside.right x))
    (bound : AtMostTwo (restrictFamily D (RawSquare.Internal D side)))
    (cut : ∀ e, A.oldMatching e = false → ¬ RawSquare.Internal D side e →
      ¬ (A.Saturated (D.left e) ∧ A.Saturated (D.right e)))
    (S : RawSquare D side b) (old : ∀ j, A.oldMatching (S.e j) = false)
    (i : Fin 4) (w : V) (out : ∀ j, w ≠ S.v j)
    (a : (support (factorFamily D (A.part f p q) b)).Adj (S.v i) w) : ¬ A.Saturated w := by
  obtain ⟨⟨e,he,pair⟩,_⟩ := (support_restrict D (fun e => A.part f p q e = .factor b)).mp a
  have inc : FamilyIncident D (S.v i) e := (S.incident i e).mpr (by rw [pair]; simp)
  have outer : w ∈ familyPair D e := by rw [pair]; simp
  have ext : ¬ RawSquare.Internal D side e := by
    intro inside
    have never (j : Fin 4) : e ≠ S.e j := by
      intro eq
      rw [eq,S.ends] at outer
      exact (Sym2.mem_iff.mp outer).elim (out _) (out _)
    exact (S.atCorner bound i e inside inc).elim (never _) (never _)
  have back : (i+3)+1 = i := by omega
  have sat := A.saturated_of_old_edges side cross (S.injective.ne (show i ≠ i+3 by omega)) (old i) (old (i+3))
    (S.internal _) (S.internal _) ((S.incident i _).mpr (by rw [S.ends]; simp))
    ((S.incident i _).mpr (by rw [S.ends,back]; simp))
  have fail := cut e (A.crossing_old side mono f p q he ext) ext
  intro ws
  rcases Sym2.eq_iff.mp pair with ⟨h,j⟩|⟨h,j⟩ <;> simp_all

variable {V E : Type} {D : Family V E} (A : Atlas D I X K)
variable [Fintype V] [Fintype E] [Fintype I] [Fintype X] [Fintype K] [DecidableEq V]

end Atlas
end Kostochka.FiveRegular.Restoration

end

section 

namespace Kostochka.FiveRegular

open SimpleGraph Subdivision
variable {V E I : Type*}

def labelConflicts (D : Family V E) : SimpleGraph E where
  Adj e f := e ≠ f ∧ FamilyMeet D e f
  symm.symm _ _ h := ⟨h.1.symm,by obtain ⟨v,hv,hw⟩ := h.2; exact ⟨v,hw,hv⟩⟩
  loopless.irrefl _ h := h.1 rfl

def UniqueAt (D : Family V E) (v : V) : Prop :=
  ∀ e f, FamilyIncident D v e → FamilyIncident D v f → e = f

theorem sole_neighbor_of_unique_end (D : Family V E) (bound : AtMostTwo D)
    {e : E} {v : V} (inc : FamilyIncident D v e) (one : UniqueAt D v)
    {f g : E} (hf : (labelConflicts D).Adj e f) (hg : (labelConflicts D).Adj e g) : f = g := by
  obtain ⟨x,xe,xf⟩ := hf.2
  obtain ⟨y,ye,yg⟩ := hg.2
  have offx : x ≠ v := fun eq => hf.1 (one _ _ inc (eq ▸ xf))
  have offy : y ≠ v := fun eq => hg.1 (one _ _ inc (eq ▸ yg))
  have same : x = y := by
    unfold FamilyIncident at inc xe ye
    grind
  have tri := bound x e f g xe xf (same ▸ yg)
  exact (tri.resolve_left hf.1).resolve_left hg.1

theorem incident_fold_fixed (D : Family V E) {p : V → V} {v : V} (fixed : p v = v) (e : E) :
    FamilyIncident (foldFamily D p) (folded p v) e ↔ FamilyIncident D v e := by
  have endpoint (w : V) : folded p v = folded p w ↔ v = w := by
    constructor
    · intro h
      rcases Sym2.eq_iff.mp h with h | h
      · exact h.1
      · exact fixed ▸ h.2
    · rintro rfl; rfl
  exact or_congr (endpoint _) (endpoint _)

theorem unique_fold_fixed (D : Family V E) {p : V → V} {v : V} (fixed : p v = v)
    (one : UniqueAt D v) : UniqueAt (foldFamily D p) (folded p v) := by
  intro e f he hf
  exact one e f ((incident_fold_fixed D fixed e).mp he) ((incident_fold_fixed D fixed f).mp hf)

theorem mutable_spoke_unique (D : Family V E) (p : V → V) (two : AtMostTwo (foldFamily D p))
    {v : V} {e : E} (fixed : p v = v) (one : UniqueAt D v) (hit : FamilyIncident D v e)
    {f g : E} (hf : (labelConflicts (foldFamily D p)).Adj e f)
    (hg : (labelConflicts (foldFamily D p)).Adj e g) : f = g :=
  sole_neighbor_of_unique_end _ two ((incident_fold_fixed D fixed e).mpr hit)
    (unique_fold_fixed D fixed one) hf hg

theorem crossing_same_end (D : Family V E) (side : V → Bool) {e : E}
    (cross : side (D.left e) ≠ side (D.right e)) {v w : V}
    (hv : FamilyIncident D v e) (hw : FamilyIncident D w e) (s : side v = side w) : v = w := by
  rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
  all_goals first | rfl | exact (cross s).elim | exact (cross s.symm).elim

end Kostochka.FiveRegular

end

section 

namespace Kostochka.FiveRegular.Restoration.Atlas
open Finset Subdivision Auxiliary
open scoped Classical
variable {V E I X K : Type*} {D : Family V E} (A : Atlas D I X K)

theorem exceptional_spoke_is_external (f : X → Bool) (p q : I → Bool)
    {i : I} {v : Fin (A.shape i).vertices} (exc : (A.shape i).exceptionalShape) {e : E} {b : Bool}
    (he : A.part f p q e = .factor b) (hit : FamilyIncident D (A.places ⟨i,v⟩) e) :
    ∃ x, e = A.labels (.inl x) ∧ f x = b := by
  obtain ⟨z,rfl⟩ := A.labels.surjective e
  rcases z with x | k | ⟨j,k⟩
  · exact ⟨x,rfl,by simpa using he⟩
  · simp at he
  · obtain rfl := A.samePieceOfIncident hit
    have mark (s : Shape) (hm : s.exceptionalShape) : s = .badPath ∨ (∃ n, s = .badOdd n) ∨ s = .divertedSquare := by
      cases s <;> simp_all [Shape.exceptionalShape]
    have hh := (A.exceptional_iff f p q _).mpr ⟨_,k,rfl,mark _ exc⟩
    change A.part f p q (A.localLabel i k) = _ at he
    rw [he] at hh
    cases hh

structure Spoke (part : E → EdgePart) (b : Bool) (w : V) where
  edge : E
  factor : part edge = .factor b
  incident : FamilyIncident D w edge

theorem spoke_injective {W : Type*} (f : X → Bool) (p q : I → Bool) (side : V → Bool)
    (cross : ∀ x, side (A.outside.left x) ≠ side (A.outside.right x))
    (i : I) (exc : (A.shape i).exceptionalShape) (b : Bool) (u : W ↪ Fin (A.shape i).vertices)
    (same : ∀ a c, side (A.places ⟨i,u a⟩) = side (A.places ⟨i,u c⟩))
    (select : ∀ a, Spoke (D := D) (A.part f p q) b (A.places ⟨i,u a⟩)) :
    Function.Injective (fun a => (select a).edge) := by
  intro a c eq
  obtain ⟨x,hx,_⟩ := A.exceptional_spoke_is_external f p q exc (select a).factor (select a).incident
  have inc := (select a).incident
  have inc' := (select c).incident
  change (select a).edge = (select c).edge at eq
  rw [← eq] at inc'
  rw [hx] at inc inc'
  have cp := crossing_same_end D side (cross x) inc inc' (same a c)
  exact u.injective (eq_of_heq (Sigma.ext_iff.mp (A.places.injective cp)).2)

section Counting
variable [Fintype E] [DecidableEq V]

private theorem count_incident (sel : E → Bool) (loop : Loopless D) (v : V) :
    coloredDegree D sel v true =
      (univ.filter (fun e => sel e = true ∧ FamilyIncident D v e)).card := by
  classical
  rw [Finset.card_filter]
  simp only [coloredDegree,← sum_add_distrib]
  apply sum_congr rfl
  intro e _
  have ne := loop e
  unfold FamilyIncident
  split_ifs <;> grind

theorem exist_two_spokes (part : E → EdgePart) (b : Bool) (v : V) (loop : Loopless D)
    (two : coloredDegree D (fun e => decide (part e = .factor b)) v true = 2) :
    ∃ s t : Spoke (D := D) part b v, s.edge ≠ t.edge := by
  classical
  rw [count_incident _ loop] at two
  have gt := Finset.one_lt_card.mp (two ▸ (by decide : 1 < 2))
  obtain ⟨e,em,g,gm,ne⟩ := gt
  have l := (Finset.mem_filter.mp em).2
  have r := (Finset.mem_filter.mp gm).2
  exact ⟨⟨e,of_decide_eq_true l.1,l.2⟩,⟨g,of_decide_eq_true r.1,r.2⟩,ne⟩
end Counting
end Kostochka.FiveRegular.Restoration.Atlas

end

section 

namespace Kostochka.FiveRegular

variable {W R E : Type*}

inductive StarSlot (R E : Type*) where
  | lower (e : E)
  | upper (e : E)
  | rim (r : R)
  | matching

def StarSlot.read (shared : E → Fin 3) (rim : R → Fin 7) : StarSlot R E → Fin 7
  | .lower e => patchLow (shared e)
  | .upper e => patchHigh (shared e)
  | .rim r => rim r
  | .matching => 6

structure StarScheme (W R E : Type*) where
  adjacent : W → W → Prop
  slots : W → Fin 5 → StarSlot R E

structure LocalPaint (S : StarScheme W R E) (shared : E → Fin 3) where
  vertex : W → Fin 3
  rim : R → Fin 7
  noMatching : ∀ r, rim r ≠ 6
  proper : ∀ x y, S.adjacent x y → vertex x ≠ vertex y
  distinct : ∀ w, Function.Injective (Fin.cases (patchLow (vertex w))
    (StarSlot.read shared rim ∘ S.slots w))

private theorem low_ne_seven (x : Fin 3) : patchLow x ≠ 6 := by
  simp [patchLow,Fin.ext_iff]; omega
private theorem high_ne_seven (x : Fin 3) : patchHigh x ≠ 6 := by
  simp [patchHigh,Fin.ext_iff]; omega

def squareRimAdj (i j : Fin 4) : Prop := j = i+1 ∨ i = j+1

def squareScheme (s : SquareSpokePatch E) : StarScheme (Fin 4) (Fin 4) E where
  adjacent := squareRimAdj
  slots i := ![.lower (s.spoke i),.rim i,.rim (i+3),.upper (s.upper i),.matching]

theorem local_square (s : SquareSpokePatch E) (f : E → Fin 3)
    (done : SquareDone (f ∘ s.upper) (f ∘ s.spoke)) : Nonempty (LocalPaint (squareScheme s) f) := by
  obtain ⟨v,e,P⟩ := done
  let w (i : Fin 4) : Fin 3 := ⟨(v i).val, (P i).1⟩
  have wv i : patchLow (w i) = v i := rfl
  refine ⟨⟨w,e,?_,?_,?_⟩⟩
  · intro i
    have star := (P i).2.2.2.2
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, or_false, and_true,
      List.nodup_nil] at star
    tauto
  · intro i j ad eq
    have h : v i = v j := congrArg patchLow eq
    rcases ad with rfl|rfl
    · exact (P i).2.2.1 h
    · exact (P j).2.2.1 h.symm
  · intro i
    apply List.nodup_ofFn.mp
    exact (P i).2.2.2.2

def badScheme (s : Fin 3 ↪ E) (u : Fin 3 → E) (a b : E) (lastHigh : Fin 2 → E) :
    StarScheme (Fin 4) (Fin 3) E where
  adjacent := squareRimAdj
  slots := ![![.lower a,.lower b,.upper (u 0),.rim 0,.matching],
    ![.lower (s 0),.upper (u 1),.rim 0,.rim 1,.matching],
    ![.lower (s 1),.rim 2,.upper (u 2),.rim 1,.matching],
    ![.lower (s 2),.rim 2,.upper (lastHigh 0),.upper (lastHigh 1),.matching]]

private theorem low3_high2 (v s e a b : Fin 3) (hs : s ≠ v) (hev : e ≠ v) (hes : e ≠ s) (hb : b ≠ a) :
    [patchLow v,patchLow s,patchLow e,patchHigh a,patchHigh b,6].Nodup := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,
    List.nodup_nil,and_true,ne_eq,Fin.ext_iff,patchLow,patchHigh] at *
  norm_num
  omega

private theorem low2_high3 (v s a b c : Fin 3) (hs : s ≠ v) (hba : b ≠ a) (hca : c ≠ a) (hbc : b ≠ c) :
    [patchLow v,patchLow s,patchHigh a,patchHigh b,patchHigh c,6].Nodup := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,
    List.nodup_nil,and_true,ne_eq,Fin.ext_iff,patchLow,patchHigh] at *
  norm_num
  omega

theorem local_bad_path (s : Fin 3 ↪ E) (u : Fin 3 → E) (a b : E) (lastHigh : Fin 2 → E)
    (f : E → Fin 3) (done : BadPathDone (f a) (f b) (f ∘ u) (f ∘ s))
    (fixedLow : f a ≠ f b) (fixedHigh : f (lastHigh 0) ≠ f (lastHigh 1)) :
    Nonempty (LocalPaint (badScheme s u a b lastHigh) f) := by
  obtain ⟨v₁,v₂,v₃,v₄,l,h₁,h₂,ha,hb,h₁₂,h₂₃,h₃₄,h₄₁,hv₂,hv₃,hv₄,hl₃,hl₄,hu₁,hu₂,hu₃,hu₄,hu₅⟩ := done
  let v := ![v₁,v₂,v₃,v₄]
  let rim := ![patchHigh h₁,patchHigh h₂,patchLow l]
  have next (i : Fin 4) : v i ≠ v (i+1) := by
    fin_cases i <;> first | exact h₁₂ | exact h₂₃ | exact h₃₄ | exact h₄₁
  refine ⟨⟨v,rim,?_,?_,?_⟩⟩
  · intro r
    fin_cases r <;> first | exact high_ne_seven _ | exact low_ne_seven _
  · intro i j h
    rcases h with rfl|rfl
    · exact next i
    · exact (next j).symm
  · intro i
    apply List.nodup_ofFn.mp
    change f (s 1) = v₄ at hv₃
    change f (s 2) = v₃ at hv₄
    fin_cases i
    · exact low3_high2 _ _ _ _ _ ha.symm hb.symm fixedLow.symm hu₁
    · exact low2_high3 _ _ _ _ _ hv₂ hu₂ hu₃ hu₅
    · exact low3_high2 _ _ _ _ _ (hv₃ ▸ h₃₄.symm) hl₃ (hv₃ ▸ hl₄) hu₄
    · exact low3_high2 _ _ _ _ _ (hv₄ ▸ h₃₄) hl₄ (hv₄ ▸ hl₃) fixedHigh.symm

def oddForward {t : ℕ} (_positive : 0 < t) : Option (Fin (2*t)) → Option (Fin (2*t)) → Prop
  | none, some j => j.val = 0
  | some i, some j => i.val+1 = j.val
  | some i, none => i.val = 2*t-1
  | none,none => False

def lowerPair {t : ℕ} (i : Fin (2*t)) : Fin t := ⟨i.val/2,by have h := i.isLt; omega⟩

def oddScheme {t : ℕ} (ht : 0 < t) (s : Option (Fin (2*t)) ↪ E) (u : Option (Fin (2*t)) → E) :
    StarScheme (Option (Fin (2*t))) (Fin t ⊕ Fin (t+1)) E where
  adjacent := fun x y => oddForward ht x y ∨ oddForward ht y x
  slots
    | none => ![.lower (s none),.upper (u none),.rim (.inr 0),.rim (.inr (Fin.last t)),.matching]
    | some i => ![.lower (s (some i)),.rim (.inl (lowerPair i)),.upper (u (some i)),
        .rim (.inr (upperGap i)),.matching]

theorem local_odd {t : ℕ} (ht : 0 < t) (s : Option (Fin (2*t)) ↪ E) (u : Option (Fin (2*t)) → E)
    (f : E → Fin 3) (done : OddDone ht (f ∘ u) (f ∘ s)) : Nonempty (LocalPaint (oddScheme ht s u) f) := by
  obtain ⟨v,low,cut,adj,first,last,mate,body,seam⟩ := done
  let even (i : Fin t) : Fin (2*t) := ⟨2*i.val,by have h := i.isLt; omega⟩
  let rim : Fin t ⊕ Fin (t+1) → Fin 7 := Sum.elim (fun i => patchLow (low (even i))) (fun j => patchHigh (cut j))
  have edge (i : Fin (2*t)) : even (lowerPair i) = i ∨ even (lowerPair i) = pairMate i := by
    by_cases h : i.val % 2 = 0
    · left; apply Fin.ext; change 2*(i.val/2) = i.val; omega
    · right; apply Fin.ext; simp only [pairMate,dif_neg h]; change 2*(i.val/2) = i.val-1; omega
  have eq (i : Fin (2*t)) : low (even (lowerPair i)) = low i := by
    rcases edge i with h|h
    · rw [h]
    · rw [h,(mate i).1]
  have next (x y) (h : oddForward ht x y) : v x ≠ v y := by
    cases x with
    | none => cases y with
      | none => exact h.elim
      | some j => exact (show j = ⟨0,by omega⟩ from Fin.ext h) ▸ first
    | some i => cases y with
      | none => exact (show i = ⟨2*t-1,by omega⟩ from Fin.ext h) ▸ last.symm
      | some j => exact adj i j h
  refine ⟨⟨v,rim,?_,fun x y h => h.elim (next x y) (fun h => (next y x h).symm),?_⟩⟩
  · rintro (i|j)
    · exact low_ne_seven _
    · exact high_ne_seven _
  · rintro (_|i)
    · exact List.nodup_ofFn.mp seam
    · apply List.nodup_ofFn.mp
      change [_,_,patchLow (low (even (lowerPair i))),_,_,_].Nodup
      rw [eq]
      exact body i

end Kostochka.FiveRegular

end

section 

namespace Kostochka.FiveRegular

open Subdivision

variable {V E K W R : Type*}

def StarSlot.label (rim : R → E) (matched : E) : StarSlot R E → E
  | .lower e | .upper e => e
  | .rim r => rim r
  | .matching => matched

def StarSlot.part (base : Bool) : StarSlot R E → EdgePart
  | .lower _ => .factor base
  | .upper _ => .factor (!base)
  | .rim _ => .exceptional
  | .matching => .matching

structure PlacedScheme (S : StarScheme W R E) (D : Family V E) (side : V → Bool)
    (part : E → EdgePart) (region : V → Option K) (k : K) where
  base : Bool
  vertex : W ↪ V
  rim : R ↪ E
  matched : W → E
  region_iff : ∀ v, region v = some k ↔ v ∈ Set.range vertex
  side_eq : ∀ w, side (vertex w) = base
  adjacent : ∀ e x y, D.left e = vertex x → D.right e = vertex y → S.adjacent x y
  incident : ∀ w i, FamilyIncident D (vertex w) ((S.slots w i).label rim (matched w))
  roles : ∀ w i, part ((S.slots w i).label rim (matched w)) = (S.slots w i).part base

def absoluteRim (base : Bool) (c : Fin 7) : Bool × Fin 3 :=
  if h : c.val < 3 then (base,⟨c.val,h⟩) else (!base,⟨(c.val-3)%3,Nat.mod_lt _ (by decide)⟩)

theorem relative_rim (base : Bool) (c : Fin 7) (hn : c ≠ 6) :
    relativeColor base (some (absoluteRim base c).1) (absoluteRim base c).2 = c := by
  cases base <;> fin_cases c <;> first | contradiction | rfl

private noncomputable def extendPaint {A B C : Type*} (place : A ↪ B) (paint : A → C)
    (defaultColor : C) (v : B) : C := by
  classical
  exact if h : v ∈ Set.range place then paint h.choose else defaultColor

private theorem extendPaint_at {A B C : Type*} (place : A ↪ B) (paint : A → C)
    (fallback : C) (a : A) : extendPaint place paint fallback (place a) = paint a := by
  have h : place a ∈ Set.range place := ⟨a,rfl⟩
  simp only [extendPaint,dif_pos h]
  exact congrArg paint (place.injective h.choose_spec)

namespace PlacedScheme

variable {S : StarScheme W R E} {D : Family V E} {side : V → Bool} {part : E → EdgePart}
    {region : V → Option K} {k : K}

noncomputable def cell (A : PlacedScheme S D side part region k) {f : E → Fin 3}
    (P : LocalPaint S f) : CellColors V E where
  vertex := extendPaint A.vertex P.vertex 0
  edge := extendPaint A.rim (fun r => absoluteRim A.base (P.rim r)) (false,0)

theorem vertex_at (A : PlacedScheme S D side part region k) {f : E → Fin 3} (P : LocalPaint S f) (w : W) :
    (A.cell P).vertex (A.vertex w) = P.vertex w := extendPaint_at _ _ _ _

theorem rim_at (A : PlacedScheme S D side part region k) {f : E → Fin 3} (P : LocalPaint S f) (r : R) :
    (A.cell P).edge (A.rim r) = absoluteRim A.base (P.rim r) :=
  extendPaint_at A.rim (fun j => absoluteRim A.base (P.rim j)) (false,0) r

theorem slot_color (A : PlacedScheme S D side part region k) {f : E → Fin 3} (P : LocalPaint S f)
    (w : W) (i : Fin 5) :
    let slot := S.slots w i
    let e := slot.label A.rim (A.matched w)
    relativeColor (side (A.vertex w)) (cellLayer part (A.cell P) e) (cellEdge part f (A.cell P) e) =
      slot.read f P.rim := by
  dsimp only
  have role := A.roles w i
  rw [A.side_eq]
  cases s : S.slots w i with
  | lower e => simp only [s, StarSlot.label,StarSlot.part] at role
               simp [StarSlot.label,cellLayer,cellEdge,role,StarSlot.read,relativeColor]
  | upper e => simp only [s, StarSlot.label,StarSlot.part] at role
               simp [StarSlot.label,cellLayer,cellEdge,role,StarSlot.read,relativeColor]
  | rim r => simp only [s, StarSlot.label,StarSlot.part] at role
             simpa [StarSlot.label,cellLayer,cellEdge,role,rim_at,StarSlot.read] using
               relative_rim A.base (P.rim r) (P.noMatching r)
  | matching => simp only [s, StarSlot.label,StarSlot.part] at role
                simp [StarSlot.label,cellLayer,cellEdge,role,StarSlot.read,relativeColor]

theorem star (A : PlacedScheme S D side part region k) {f : E → Fin 3} (P : LocalPaint S f)
    (exhaust : ∀ v (s : Fin 5 → E), Function.Injective s → (∀ i, FamilyIncident D v (s i)) →
      ∀ e, FamilyIncident D v e → ∃ i, s i = e) (w : W) :
    Nonempty (StarAt D (A.vertex w) (patchLow ((A.cell P).vertex (A.vertex w)))
      (fun e => relativeColor (side (A.vertex w)) (cellLayer part (A.cell P) e) (cellEdge part f (A.cell P) e))) := by
  let slots (i : Fin 5) := (S.slots w i).label A.rim (A.matched w)
  let value (e : E) := relativeColor (side (A.vertex w)) (cellLayer part (A.cell P) e) (cellEdge part f (A.cell P) e)
  have eq : value ∘ slots = StarSlot.read f P.rim ∘ S.slots w := funext (A.slot_color P w)
  have inj : Function.Injective (Fin.cases (patchLow ((A.cell P).vertex (A.vertex w))) (value ∘ slots)) := by
    rw [eq,A.vertex_at]
    exact P.distinct w
  have es : Function.Injective slots := by
    intro i j he
    apply Fin.succ_inj.mp
    apply inj
    simpa only [Fin.cases_succ,Function.comp_apply] using congrArg value he
  exact ⟨⟨slots,exhaust _ slots es (A.incident w),inj⟩⟩

end PlacedScheme

theorem region_stars_of_schemes {X T : K → Type*} (schemes : ∀ k, StarScheme (X k) (T k) E)
    (D : Family V E) (side : V → Bool) (part : E → EdgePart) (region : V → Option K)
    (placed : ∀ k, PlacedScheme (schemes k) D side part region k) (f : E → Fin 3)
    (paint : ∀ k, Nonempty (LocalPaint (schemes k) f))
    (closed : ∀ e, side (D.left e) = side (D.right e) → region (D.left e) = region (D.right e))
    (exhaust : ∀ v (s : Fin 5 → E), Function.Injective s → (∀ i, FamilyIncident D v (s i)) →
      ∀ e, FamilyIncident D v e → ∃ i, s i = e) : Nonempty (RegionStars D side part region f) := by
  let P (k) := Classical.choice (paint k)
  refine ⟨⟨fun k => (placed k).cell (P k),?_,?_⟩⟩
  · intro k e same hk
    obtain ⟨x,hx⟩ := ((placed k).region_iff _).mp hk
    obtain ⟨y,hy⟩ := ((placed k).region_iff _).mp ((closed e same).symm.trans hk)
    rw [← hx,← hy,PlacedScheme.vertex_at,PlacedScheme.vertex_at]
    exact (P k).proper x y ((placed k).adjacent e x y hx.symm hy.symm)
  · intro k v hv
    obtain ⟨x,rfl⟩ := ((placed k).region_iff _).mp hv
    exact (placed k).star (P k) exhaust x

end Kostochka.FiveRegular

end

section 

namespace Kostochka.FiveRegular.Restoration
open Subdivision Auxiliary
variable {V E I X K : Type*} {D : Family V E}

structure FourRow (D : Family V E) (side : V → Bool) (b : Bool) where
  corner : Fin 4 ↪ V
  gap : Fin 3 ↪ E
  side_eq : ∀ j, side (corner j) = b
  pair : ∀ j, familyPair D (gap j) = s(corner j.castSucc,corner j.succ)

namespace FourRow
variable {side : V → Bool} {b : Bool} (R : FourRow D side b)

theorem incident {j : Fin 4} {k : Fin 3} (h : j = k.castSucc ∨ j = k.succ) :
    FamilyIncident D (R.corner j) (R.gap k) := by
  apply Sym2.mem_iff.mp
  change R.corner j ∈ familyPair D (R.gap k)
  rw [R.pair]; rcases h with rfl|rfl <;> simp

private theorem inside (k : Fin 3) : RawSquare.Internal D side (R.gap k) := by
  rcases Sym2.eq_iff.mp (R.pair k) with ⟨l,r⟩|⟨l,r⟩ <;> simp [RawSquare.Internal,l,r,R.side_eq]

theorem adjacent (bd : AtMostTwo (restrictFamily D (RawSquare.Internal D side))) (loop : Loopless D)
    (e : E) (x y : Fin 4) (l : D.left e = R.corner x) (r : D.right e = R.corner y) : squareRimAdj x y := by
  have xy : x ≠ y := fun h => loop e (l.trans ((congrArg R.corner h).trans r.symm))
  have ie : RawSquare.Internal D side e := by simp [RawSquare.Internal,l,r,R.side_eq]
  have middle (a c : Fin 4) (u v : Fin 3) (ne : u ≠ v) (hit : FamilyIncident D (R.corner a) e)
      (other : FamilyIncident D (R.corner c) e)
      (hu : a = u.castSucc ∨ a = u.succ) (hv : a = v.castSucc ∨ a = v.succ) :
      c = u.castSucc ∨ c = u.succ ∨ c = v.castSucc ∨ c = v.succ := by
    let ku : {e // RawSquare.Internal D side e} := ⟨R.gap u,R.inside u⟩
    let kv : {e // RawSquare.Internal D side e} := ⟨R.gap v,R.inside v⟩
    have pair (k : Fin 3) (h : e = R.gap k) : c = k.castSucc ∨ c = k.succ := by
      have f : R.corner c ∈ familyPair D e := Sym2.mem_iff.mpr other
      rw [h,R.pair] at f
      rcases Sym2.mem_iff.mp f with h|h
      · exact Or.inl (R.corner.injective h)
      · exact Or.inr (R.corner.injective h)
    rcases bd (R.corner a) ⟨e,ie⟩ ku kv hit (R.incident hu) (R.incident hv) with h|h|h
    · rcases pair u (congrArg Subtype.val h) with h|h <;> tauto
    · exact .inr (.inr (pair v (congrArg Subtype.val h)))
    · exact (ne (R.gap.injective (congrArg Subtype.val h))).elim
  have hx : FamilyIncident D (R.corner x) e := .inl l.symm
  have hy : FamilyIncident D (R.corner y) e := .inr r.symm
  by_contra bad
  have test : ∀ x y : Fin 4, x ≠ y → ¬squareRimAdj x y →
      (x=1 ∧ y=3) ∨ (x=3 ∧ y=1) ∨ (x=0 ∧ y=2) ∨ (x=2 ∧ y=0) := by
    unfold squareRimAdj; decide
  rcases test x y xy bad with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · have z := middle 1 3 0 1 (by decide) hx hy (Or.inr rfl) (Or.inl rfl)
    revert z; decide
  · have z := middle 1 3 0 1 (by decide) hy hx (Or.inr rfl) (Or.inl rfl)
    revert z; decide
  · have z := middle 2 0 1 2 (by decide) hy hx (Or.inr rfl) (Or.inl rfl)
    revert z; decide
  · have z := middle 2 0 1 2 (by decide) hx hy (Or.inr rfl) (Or.inl rfl)
    revert z; decide

end FourRow

namespace Atlas
variable (A : Atlas D I X K) [Fintype I] [Fintype E] [Fintype X] [Fintype K] [DecidableEq V]
variable {side : V → Bool} (P : A.PartitionColors side)

structure ChartContext (A : Atlas D I X K) {side : V → Bool} (P : A.PartitionColors side) : Prop where
  loop : Loopless D
  bound : AtMostTwo (restrictFamily D (RawSquare.Internal D side))
  regular : ∀ i (v : Fin (A.shape i).vertices), coloredDegree A.outside (fun _ => true) (A.places ⟨i,v⟩) true +
    oldDegree (A.shape i) v.val = 4
  mono : ∀ i (v : Fin (A.shape i).vertices), side (A.places ⟨i,v⟩) = A.pieceSide side i
  crosses : ∀ x, side (A.outside.left x) ≠ side (A.outside.right x)
  matching : ∀ w, ∃ e, A.part P.exterior P.first P.second e = .matching ∧ FamilyIncident D w e

namespace ChartContext
variable {A} {P} (C : ChartContext A P)

noncomputable def selected (w : V) : E := (C.matching w).choose
omit [Fintype I] [Fintype E] [Fintype K] in
theorem selected_role (w : V) : A.part P.exterior P.first P.second (C.selected w) = .matching := (C.matching w).choose_spec.1
omit [Fintype I] [Fintype E] [Fintype K] in
theorem selected_hit (w : V) : FamilyIncident D w (C.selected w) := (C.matching w).choose_spec.2
end ChartContext
end Atlas
end Kostochka.FiveRegular.Restoration

end

section 

namespace Kostochka.FiveRegular.Restoration.Atlas
open Subdivision Auxiliary
variable {V E I X K T : Type*} {D : Family V E}

def indexOrientation (n : ℕ) (reverse : Bool) : Fin n ≃ Fin n :=
  if reverse then Fin.revPerm else Equiv.refl _

def coordinate (A : Atlas D I X K) (i : I) {n : ℕ} (len : (A.shape i).vertices = n)
    (rev : Bool) : Fin n ≃ Fin (A.shape i).vertices := (indexOrientation n rev).trans (finCongr len.symm)

def corners (A : Atlas D I X K) (i : I) {n : ℕ} (len : (A.shape i).vertices = n)
    (rev : Bool) : Fin n ↪ V :=
  (A.coordinate i len rev).toEmbedding.trans ⟨fun j => A.places ⟨i,j⟩,fun _ _ h => eq_of_heq (Sigma.ext_iff.mp (A.places.injective h)).2⟩

theorem corner_vertex (A : Atlas D I X K) (i : I) {n} (len : (A.shape i).vertices = n) (rev : Bool) (j : Fin n) :
    A.corners i len rev j = A.vertex i ((indexOrientation n rev) j).val := by
  let t := (indexOrientation n rev) j
  change A.places ⟨i,Fin.cast len.symm t⟩ = A.places ⟨i,vertexAt (A.shape i) t.val⟩
  congr 2
  apply Fin.ext; exact (Nat.mod_eq_of_lt (len ▸ t.isLt)).symm

theorem corners_range (A : Atlas D I X K) (i : I) {n} (len : (A.shape i).vertices = n) (rev : Bool) (v : V) :
    A.InPiece i v ↔ v ∈ Set.range (A.corners i len rev) := by
  constructor
  · rintro ⟨k,rfl⟩
    obtain ⟨j,rfl⟩ := (A.coordinate i len rev).surjective k
    exact ⟨j,rfl⟩
  · rintro ⟨j,rfl⟩; exact ⟨_,rfl⟩

def gaps (A : Atlas D I X K) (i : I) {n : ℕ} (len : (A.shape i).edges = n) (rev : Bool) : Fin n ↪ E :=
  ((indexOrientation n rev).trans (finCongr len.symm)).toEmbedding.trans
    ⟨A.localLabel i,fun a b h => eq_of_heq (Sigma.ext_iff.mp (A.localLabel_injective (a₁ := ⟨i,a⟩) (a₂ := ⟨i,b⟩) h)).2⟩

structure PathChart (D : Family V E) (side : V → Bool) (part : E → EdgePart) (b : Bool) where
  row : FourRow D side b
  low : ∀ j : Fin 3, Spoke (D := D) part b (row.corner j.succ)
  high : ∀ j : Fin 3, Spoke (D := D) part (!b) (row.corner j.castSucc)
  fixed : Fin 2 → Spoke (D := D) part b (row.corner 0)
  last : Fin 2 → Spoke (D := D) part (!b) (row.corner 3)
  lowInj : Function.Injective (fun j => (low j).edge)
  fixedNe : (fixed 0).edge ≠ (fixed 1).edge
  lastNe : (last 0).edge ≠ (last 1).edge
  exceptional : ∀ j, part (row.gap j) = .exceptional

namespace PathChart
variable {side : V → Bool} {part : E → EdgePart} {b : Bool} (H : PathChart D side part b)
def lowEdges : Fin 3 ↪ E := ⟨_,H.lowInj⟩
def patch : OpenException E := .badPath H.lowEdges (fun j => (H.high j).edge) (H.fixed 0).edge (H.fixed 1).edge
def scheme := badScheme H.lowEdges (fun j => (H.high j).edge) (H.fixed 0).edge (H.fixed 1).edge (fun j => (H.last j).edge)

def place (region : V → Option T) (key : T) (mem : ∀ v, region v = some key ↔ v ∈ Set.range H.row.corner)
    (bound : AtMostTwo (restrictFamily D (RawSquare.Internal D side))) (loop : Loopless D)
    (matchAt : V → E) (matchHit : ∀ v, FamilyIncident D v (matchAt v)) (matchPart : ∀ v, part (matchAt v) = .matching) :
    PlacedScheme H.scheme D side part region key := by
  refine ⟨b,H.row.corner,H.row.gap,matchAt ∘ H.row.corner,mem,H.row.side_eq,H.row.adjacent bound loop,?_,?_⟩
  · intro w i
    have lo (j : Fin 3) := (H.low j).incident
    have hi (j : Fin 3) := (H.high j).incident
    have fx (j : Fin 2) := (H.fixed j).incident
    have ls (j : Fin 2) := (H.last j).incident
    fin_cases w <;> fin_cases i <;> first
      | exact fx 0 | exact fx 1 | exact ls 0 | exact ls 1 | exact lo 0 | exact lo 1 | exact lo 2
      | exact hi 0 | exact hi 1 | exact hi 2 | exact matchHit _
      | (apply H.row.incident; decide)
  · intro w i
    fin_cases w <;> fin_cases i <;> first
      | exact (H.fixed 0).factor | exact (H.fixed 1).factor | exact (H.last 0).factor | exact (H.last 1).factor
      | exact (H.low 0).factor | exact (H.low 1).factor | exact (H.low 2).factor
      | exact (H.high 0).factor | exact (H.high 1).factor | exact (H.high 2).factor
      | exact matchPart _ | exact H.exceptional _
end PathChart

structure SquareChart (D : Family V E) (side : V → Bool) (part : E → EdgePart) (b : Bool) where
  square : RawSquare D side b
  low : ∀ j : Fin 4, Spoke (D := D) part b (square.v j)
  high : ∀ j : Fin 4, Spoke (D := D) part (!b) (square.v j)
  lowInj : Function.Injective (fun j => (low j).edge)
  outside : Fin 2 → V
  outsideHit : ∀ j : Fin 4, FamilyIncident D (outside ⟨j.val % 2,by omega⟩) (low j).edge
  outsideSide : ∀ j, side (outside j) ≠ b
  exceptional : ∀ j, part (square.e j) = .exceptional

namespace SquareChart
variable {side : V → Bool} {part : E → EdgePart} {b : Bool} (Q : SquareChart D side part b)
def patch : SquareSpokePatch E := ⟨⟨_,Q.lowInj⟩,fun j => (Q.high j).edge⟩
def row : FourRow D side b where
  corner := Q.square.v
  gap := Fin.castSuccEmb.trans ⟨Q.square.e,Q.square.injective⟩
  side_eq := Q.square.mono
  pair j := by
    change familyPair D (Q.square.e j.castSucc) = _
    rw [Q.square.ends]
    congr 2
    exact Fin.ext (Nat.mod_eq_of_lt j.succ.isLt)

def place (region : V → Option T) (key : T) (mem : ∀ v, region v = some key ↔ v ∈ Set.range Q.square.v)
    (bound : AtMostTwo (restrictFamily D (RawSquare.Internal D side))) (loop : Loopless D)
    (matchAt : V → E) (matchHit : ∀ v, FamilyIncident D v (matchAt v)) (matchPart : ∀ v, part (matchAt v) = .matching) :
    PlacedScheme (squareScheme Q.patch) D side part region key := by
  refine ⟨b,Q.square.v,⟨Q.square.e,Q.square.injective⟩,matchAt ∘ Q.square.v,mem,Q.square.mono,Q.row.adjacent bound loop,?_,?_⟩
  · intro w i
    fin_cases i
    · exact (Q.low w).incident
    · change FamilyIncident D (Q.square.v w) (Q.square.e w)
      apply (Q.square.incident ..).mpr
      rw [Q.square.ends]; simp
    · change FamilyIncident D (Q.square.v w) (Q.square.e (w+3))
      apply (Q.square.incident ..).mpr
      rw [Q.square.ends,show (w+3)+1 = w by omega]; simp
    · exact (Q.high w).incident
    · exact matchHit _
  · intro w i
    fin_cases i <;> first | exact (Q.low w).factor | exact Q.exceptional _ | exact (Q.high w).factor | exact matchPart _
end SquareChart

end Kostochka.FiveRegular.Restoration.Atlas

end

section 

namespace Kostochka.FiveRegular.Restoration.Atlas
open Subdivision Auxiliary
variable {V E I X K : Type*} {D : Family V E} (A : Atlas D I X K)
variable [Fintype I] [Fintype E] [Fintype X] [Fintype K] [DecidableEq V]
variable {side : V → Bool} (P : A.PartitionColors side) (C : ChartContext A P)

def pathFlip (i : I) : Bool := decide (P.first i = A.pieceSide side i)

def pathCoord (i : I) (sh : A.shape i = .badPath) := A.coordinate i (n := 4) (by rw [sh]; rfl) (A.pathFlip P i)
def pathGap (i : I) (sh : A.shape i = .badPath) := A.gaps i (n := 3) (by rw [sh]; rfl) (A.pathFlip P i)

def pathRow (i : I) (sh : A.shape i = .badPath) : FourRow D side (A.pieceSide side i) where
  corner := A.corners i (n := 4) (by rw [sh]; rfl) (A.pathFlip P i)
  gap := A.pathGap P i sh
  side_eq j := C.mono i _
  pair j := by
    change familyPair D (A.localLabel i (Fin.cast (by rw [sh]; rfl) (indexOrientation 3 (A.pathFlip P i) j))) = _
    rw [A.gap_ends,A.corner_vertex,A.corner_vertex]
    change s(A.vertex i ((indexOrientation 3 (A.pathFlip P i)) j).val,A.vertex i (((indexOrientation 3 (A.pathFlip P i)) j).val+1)) = _
    cases h : A.pathFlip P i <;> fin_cases j <;> first | rfl | exact Sym2.eq_swap

abbrev degreeAt (b : Bool) (v : V) :=
  coloredDegree D (fun e => decide (A.part P.exterior P.first P.second e = .factor b)) v true

theorem path_degrees (i : I) (sh : A.shape i = .badPath) (j : Fin 4) :
    A.degreeAt P (A.pieceSide side i) ((A.pathRow P C i sh).corner j) = (if j = 0 then 2 else 1) ∧
    A.degreeAt P (!(A.pieceSide side i)) ((A.pathRow P C i sh).corner j) = (if j = 3 then 2 else 1) := by
  let k := A.pathCoord P i sh j
  let b := A.pieceSide side i
  change A.degreeAt P b (A.places ⟨i,k⟩) = _ ∧ A.degreeAt P (!b) (A.places ⟨i,k⟩) = _
  have ends := A.endpoint_constraints P C.regular i sh k
  have inner (t : k.val = 1 ∨ k.val = 2) :
      A.degreeAt P b (A.places ⟨i,k⟩) = 1 ∧ A.degreeAt P (!b) (A.places ⟨i,k⟩) = 1 := by
    have three : (A.shape i).thirdDegree (P.first i) (P.second i) k.val = 2 := by
      have id (s : Shape) (h : s = .badPath) (r : ℕ) (hr : r = 1 ∨ r = 2) :
          s.thirdDegree (P.first i) (P.second i) r = 2 := by rcases hr with rfl|rfl <;> rw [h] <;> rfl
      exact id _ sh _ t
    have h := (A.actualDegrees P.exterior P.first P.second i k (C.regular i k) (P.balanced i k)).2.2 three
    cases b <;> first | exact h | exact h.symm
  have key : k.val = ((indexOrientation 4 (decide (P.first i = b))) j).val := rfl
  by_cases flip : P.first i = b
  · simp only [flip,decide_true] at key
    fin_cases j
    · exact ⟨by simpa [flip] using (ends.2 key).1,by simpa [flip] using (ends.2 key).2⟩
    · exact inner (Or.inr key)
    · exact inner (Or.inl key)
    · exact ⟨by simpa [flip] using (ends.1 key).1,by simpa [flip] using (ends.1 key).2⟩
  · have nf : P.first i = !b := (show ∀ a b : Bool, a ≠ b → a = !b by decide) _ _ flip
    simp only [flip,decide_false] at key
    fin_cases j
    · exact ⟨by simpa [nf] using (ends.1 key).2,by simpa [nf] using (ends.1 key).1⟩
    · exact inner (Or.inl key)
    · exact inner (Or.inr key)
    · exact ⟨by simpa [nf] using (ends.2 key).2,by simpa [nf] using (ends.2 key).1⟩

omit [Fintype I] [Fintype K] in
private theorem hasSpoke (b : Bool) (v : V) (loop : Loopless D) (one : A.degreeAt P b v = 1) :
    ∃! e, A.part P.exterior P.first P.second e = .factor b ∧ FamilyIncident D v e := by
  simpa using (unique_iff_degree D loop (fun e => decide (A.part P.exterior P.first P.second e = .factor b)) v).mpr one

noncomputable def single (b : Bool) (v : V) (one : A.degreeAt P b v = 1) :
    Spoke (D := D) (A.part P.exterior P.first P.second) b v :=
  let e := A.hasSpoke P b v C.loop one
  ⟨e.choose,e.choose_spec.1.1,e.choose_spec.1.2⟩

noncomputable def two (b : Bool) (v : V) (two : A.degreeAt P b v = 2) :
    Fin 2 → Spoke (D := D) (A.part P.exterior P.first P.second) b v :=
  let h := exist_two_spokes _ b v C.loop two
  ![h.choose,h.choose_spec.choose]

omit [Fintype I] [Fintype K] in
theorem two_distinct (b : Bool) (v : V) (two : A.degreeAt P b v = 2) :
    (A.two P C b v two 0).edge ≠ (A.two P C b v two 1).edge :=
  (exist_two_spokes _ b v C.loop two).choose_spec.choose_spec

noncomputable def pathChart (i : I) (sh : A.shape i = .badPath) :
    PathChart D side (A.part P.exterior P.first P.second) (A.pieceSide side i) := by
  let R := A.pathRow P C i sh
  let b := A.pieceSide side i
  have deg := A.path_degrees P C i sh
  let lo (j : Fin 3) := A.single P C b (R.corner j.succ) (by simpa [R,b] using (deg j.succ).1)
  let hi (j : Fin 3) := A.single P C (!b) (R.corner j.castSucc) (by
    have n : j.castSucc ≠ (3:Fin 4) := by fin_cases j <;> decide
    simpa [R,b,n] using (deg j.castSucc).2)
  let fixed := A.two P C b (R.corner 0) (by simpa using (deg 0).1)
  let last := A.two P C (!b) (R.corner 3) (by simpa using (deg 3).2)
  refine ⟨R,lo,hi,fixed,last,?_,A.two_distinct P C _ _ _,A.two_distinct P C _ _ _,?_⟩
  · let u := (Fin.succEmb 3).trans (A.pathCoord P i sh).toEmbedding
    exact A.spoke_injective P.exterior P.first P.second side C.crosses i (by simp [sh,Shape.exceptionalShape]) b u
      (fun a c => (C.mono i _).trans (C.mono i _).symm) lo
  · intro j
    apply (A.exceptional_iff ..).mpr
    exact ⟨i,_,rfl,Or.inl sh⟩

end Kostochka.FiveRegular.Restoration.Atlas

end

section 

namespace Kostochka.FiveRegular.Restoration.Atlas
open Subdivision Auxiliary SimpleGraph
variable {V E I X K : Type*} {D : Family V E} (A : Atlas D I X K)

structure SquareWitness (f : X → Bool) (b : Bool) (i : I) where
  outside : Fin 2 → V
  cross : ∀ k : Fin 4, A.CrossingLink f b (A.vertex i k.val) (outside ⟨k.val%2,by omega⟩)

noncomputable def squareWitness_of_decision (side : V → Bool) (f : X → Bool) (i : I)
    (test : A.squareDecision f side i = true) :
    (A.afterSquareDecision (A.squareDecision f side)).SquareWitness f (A.pieceSide side i) i := by
  have hit := (A.squareDecision_iff f side i).mp test
  let w (j : Fin 2) := ![hit.1.choose,hit.2.choose] j
  refine ⟨w,?_⟩
  intro k
  rw [A.afterSquare_vertex]
  change A.CrossingLink f (A.pieceSide side i) (A.vertex i k.val) (w ⟨k.val%2,by omega⟩)
  fin_cases k
  · exact hit.1.choose_spec.2 _ (Sym2.mem_mk_left ..)
  · exact hit.2.choose_spec.2 _ (Sym2.mem_mk_left ..)
  · exact hit.1.choose_spec.2 _ (Sym2.mem_mk_right ..)
  · exact hit.2.choose_spec.2 _ (Sym2.mem_mk_right ..)

variable [Fintype I] [Fintype E] [Fintype X] [Fintype K] [DecidableEq V]
variable {side : V → Bool} (P : A.PartitionColors side) (C : ChartContext A P)

def squareRow (i : I) (sh : A.shape i = .divertedSquare) : RawSquare D side (A.pieceSide side i) :=
  A.localSquare side (A.pieceSide side i) i (by rw [sh]; rfl) (by rw [sh]; rfl) (fun j => C.mono i _)

theorem square_degrees (i : I) (sh : A.shape i = .divertedSquare) (j : Fin 4) (b : Bool) :
    A.degreeAt P b ((A.squareRow P C i sh).v j) = 1 := by
  let k := vertexAt (A.shape i) j.val
  have h : (A.shape i).thirdDegree (P.first i) (P.second i) k.val = 2 := by
    have th (s : Shape) (h : s = .divertedSquare) (v : Fin s.vertices) : s.thirdDegree (P.first i) (P.second i) v.val = 2 := by
      subst s
      change Fin 4 at v
      fin_cases v <;> rfl
    exact th _ sh k
  have one := (A.actualDegrees P.exterior P.first P.second i k (C.regular i k) (P.balanced i k)).2.2 h
  cases b <;> first | exact one.1 | exact one.2

noncomputable def squareChart (i : I) (sh : A.shape i = .divertedSquare)
    (w : A.SquareWitness P.exterior (A.pieceSide side i) i) :
    SquareChart D side (A.part P.exterior P.first P.second) (A.pieceSide side i) := by
  let b := A.pieceSide side i
  let R := A.squareRow P C i sh
  let x (j : Fin 4) := (w.cross j).choose
  have pair (j : Fin 4) : familyPair D (A.labels (.inl (x j))) = s(R.v j, w.outside ⟨j.val%2,by omega⟩) :=
    (w.cross j).choose_spec.2
  have hits (j : Fin 4) : FamilyIncident D (R.v j) (A.labels (.inl (x j))) ∧
      FamilyIncident D (w.outside ⟨j.val%2,by omega⟩) (A.labels (.inl (x j))) := by
    constructor <;> apply Sym2.mem_iff.mp <;> change _ ∈ familyPair D _ <;> rw [pair] <;> simp
  let low (j : Fin 4) : Spoke (D := D) (A.part P.exterior P.first P.second) b (R.v j) :=
    ⟨A.labels (.inl (x j)),by rw [A.part_external,(w.cross j).choose_spec.1],(hits j).1⟩
  let high (j : Fin 4) := A.single P C (!b) (R.v j) (A.square_degrees P C i sh j (!b))
  refine ⟨R,low,high,?_,w.outside,fun j => (hits j).2,?_,?_⟩
  · intro j k eq
    change A.labels (.inl (x j)) = A.labels (.inl (x k)) at eq
    have hk := (hits k).1
    rw [← eq] at hk
    exact R.v.injective (crossing_same_end D side (C.crosses (x j)) (hits j).1 hk ((R.mono j).trans (R.mono k).symm))
  · intro t
    let j : Fin 4 := t.castLE (by decide)
    have div : (⟨j.val%2,by omega⟩ : Fin 2) = t := Fin.ext (Nat.mod_eq_of_lt t.isLt)
    intro same
    have colors : side (R.v j) = side (w.outside ⟨j.val%2,by omega⟩) := by rw [div]; exact (R.mono j).trans same.symm
    rcases Sym2.eq_iff.mp (pair j) with ⟨l,r⟩|⟨l,r⟩
    · exact C.crosses (x j) ((congrArg side l).trans (colors.trans (congrArg side r).symm))
    · exact C.crosses (x j) ((congrArg side l).trans (colors.symm.trans (congrArg side r).symm))
  · intro j
    apply (A.exceptional_iff ..).mpr
    exact ⟨i,_,rfl,Or.inr (Or.inr sh)⟩

end Kostochka.FiveRegular.Restoration.Atlas

end

section 

namespace Kostochka.FiveRegular

open Subdivision

variable {V E R : Type*}

def OwnsSpoke (D : Family V E) (side : V → Bool) (part : E → EdgePart) (tag : V → R)
    (r : R) (e : E) : Prop :=
  ∃ v, tag v = r ∧ FamilyIncident D v e ∧ part e = .factor (side v) ∧
    side (D.left e) ≠ side (D.right e)

theorem ownsSpoke_unique (D : Family V E) (side : V → Bool) (part : E → EdgePart) (tag : V → R)
    {a b : R} {e : E} (ha : OwnsSpoke D side part tag a e) (hb : OwnsSpoke D side part tag b e) : a = b := by
  obtain ⟨u,hu,eu,pu,cu⟩ := ha
  obtain ⟨v,hv,ev,pv,_⟩ := hb
  exact hu.symm.trans ((congrArg tag (crossing_same_end D side cu eu ev (EdgePart.factor.inj (pu.symm.trans pv)))).trans hv)

theorem disjoint_owned_sets (D : Family V E) (side : V → Bool) (part : E → EdgePart) (tag : V → R)
    {A B : Set E} {r s : R} (diff : r ≠ s) (a : ∀ e ∈ A, OwnsSpoke D side part tag r e)
    (b : ∀ e ∈ B, OwnsSpoke D side part tag s e) : Disjoint A B :=
  Set.disjoint_left.mpr (fun _ he hf => diff (ownsSpoke_unique D side part tag (a _ he) (b _ hf)))

def UpperSpoke (D : Family V E) (side : V → Bool) (part : E → EdgePart) (e : E) : Prop :=
  ∃ v, FamilyIncident D v e ∧ part e = .factor (!side v) ∧
    ∀ f, part f = part e → FamilyIncident D v f → e = f

def DoubledSpoke (D : Family V E) (side : V → Bool) (part : E → EdgePart) (e : E) : Prop :=
  ∃ u w f, FamilyIncident D u e ∧ FamilyIncident D w e ∧ FamilyIncident D w f ∧
    e ≠ f ∧ side u ≠ side w ∧ part e = .factor (side u) ∧ part f = part e

theorem upper_ne_doubled (D : Family V E) (side : V → Bool) (part : E → EdgePart) {e f : E}
    (hu : UpperSpoke D side part e) (hd : DoubledSpoke D side part f) : e ≠ f := by
  rintro rfl
  obtain ⟨v,ve,upper,unique⟩ := hu
  obtain ⟨u,w,g,ue,we,wg,ng,cross,low,same⟩ := hd
  have vu : v ≠ u := by
    intro eq
    have no := EdgePart.factor.inj (upper.symm.trans low)
    rw [eq] at no
    cases hh : side u <;> simp [hh] at no
  have uw : u ≠ w := fun eq => cross (congrArg side eq)
  have vw : v = w := by
    unfold FamilyIncident at ve ue we
    grind
  exact ng (unique _ same (vw ▸ wg))

end Kostochka.FiveRegular

end

section 

namespace Kostochka.FiveRegular
open Subdivision SimpleGraph

variable {V E K J : Type*} [Fintype K] [Fintype J]

theorem patch_from_spoke_geometry (D : Family V E) (side : V → Bool) (part : E → EdgePart)
    (conflicts : SimpleGraph E) (P : K → OpenException E) (Q : J → SquareSpokePatch E)
    (tag : V → Option ((K ⊕ J) × Bool))
    (openValid : ∀ k, (P k).valid conflicts)
    (squareOpposite : ∀ j i e, conflicts.Adj ((Q j).spoke i) e → e = (Q j).spoke (i+2))
    (squareApart : ∀ j, conflicts.Adj ((Q j).upper 0) ((Q j).upper 2) ∧ conflicts.Adj ((Q j).upper 1) ((Q j).upper 3))
    (openOwn : ∀ k e, e ∈ (P k).spokes → OwnsSpoke D side part tag (some (.inl k,false)) e)
    (squareOwn : ∀ k e, e ∈ Set.range (Q k).spoke → OwnsSpoke D side part tag (some (.inr k,false)) e)
    (fixedOwn : ∀ k e, e ∈ (P k).fixed → OwnsSpoke D side part tag (some (.inl k,true)) e)
    (upper : ∀ k i, UpperSpoke D side part ((Q k).upper i))
    (doubled : ∀ k i, DoubledSpoke D side part ((Q k).spoke i))
    (initial : E → Fin 3) (valid : ProperLabels conflicts initial) :
    ∃ f, ProperLabels conflicts f ∧ (∀ k, (P k).complete f) ∧
      (∀ j, SquareDone (f ∘ (Q j).upper) (f ∘ (Q j).spoke)) ∧
      ∀ e, (∀ k, e ∉ (P k).spokes) → (∀ j, e ∉ Set.range (Q j).spoke) → f e = initial e := by
  refine patch_all conflicts P Q openValid squareOpposite squareApart ?_ ?_ ?_ ?_ ?_ ?_ initial valid
  · intro i j ne
    exact disjoint_owned_sets D side part tag (by simpa using ne) (openOwn i) (openOwn j)
  · intro i j ne
    exact disjoint_owned_sets D side part tag (by simpa using ne) (squareOwn i) (squareOwn j)
  · intro i j
    exact disjoint_owned_sets D side part tag (by simp) (openOwn i) (squareOwn j)
  · intro i j
    exact disjoint_owned_sets D side part tag (by simp) (fixedOwn i) (openOwn j)
  · intro i j
    exact disjoint_owned_sets D side part tag (by simp) (fixedOwn i) (squareOwn j)
  · intro i j
    rw [Set.disjoint_left]
    rintro e ⟨x,rfl⟩ ⟨y,eq⟩
    exact upper_ne_doubled D side part (upper i x) (doubled j y) eq.symm

end Kostochka.FiveRegular

end

section 

namespace Kostochka.FiveRegular.Restoration.Atlas
open SimpleGraph Subdivision Auxiliary

variable {V E I X K : Type*} {D : Family V E} (A : Atlas D I X K)

abbrev OddKey := {i : I // ∃ n, A.shape i = .badOdd n}
abbrev BadKey := {i : I // A.shape i = .badPath}
abbrev SquareKey := {i : I // A.shape i = .divertedSquare}
abbrev OpenKey := A.OddKey ⊕ A.BadKey
abbrev PatchKey := A.OpenKey ⊕ A.SquareKey

def patchIndex : A.PatchKey → I
  | .inl (.inl i) | .inl (.inr i) | .inr i => i.val

theorem patchIndex_injective : Function.Injective A.patchIndex := by
  rintro ((i|i)|i) ((j|j)|j) eq
  all_goals change i.val = j.val at eq
  all_goals try first | exact congrArg _ (congrArg _ (Subtype.ext eq)) | exact congrArg _ (Subtype.ext eq)
  all_goals
    have hi := i.property
    have hj := j.property
    first | obtain ⟨n,hi⟩ := hi | obtain ⟨n,hj⟩ := hj | skip
    rw [eq,hj] at hi
    contradiction

theorem inPiece_iff (i : I) (v : V) : A.InPiece i v ↔ A.pieceOf v = i := by
  constructor
  · rintro ⟨k,rfl⟩
    simp [pieceOf]
  · intro h
    obtain ⟨⟨j,k⟩,rfl⟩ := A.places.surjective v
    have eq : j = i := by simpa [pieceOf] using h
    exact eq ▸ ⟨k,rfl⟩

noncomputable def patchRegion (v : V) : Option A.PatchKey := by
  classical
  exact if h : ∃ k, A.patchIndex k = A.pieceOf v then some h.choose else none

theorem patchRegion_eq (v : V) (k : A.PatchKey) :
    A.patchRegion v = some k ↔ A.InPiece (A.patchIndex k) v := by
  classical
  rw [A.inPiece_iff]
  by_cases h : ∃ j, A.patchIndex j = A.pieceOf v
  · simp only [patchRegion,dif_pos h,Option.some.injEq]
    exact ⟨fun eq => eq ▸ h.choose_spec.symm,fun eq => A.patchIndex_injective (h.choose_spec.trans eq)⟩
  · simp only [patchRegion,dif_neg h,reduceCtorEq,false_iff]
    exact fun eq => h ⟨k,eq.symm⟩

theorem key_shape (k : A.PatchKey) : (A.shape (A.patchIndex k)).exceptionalShape := by
  rcases k with (k|k)|k
  · obtain ⟨n,h⟩ := k.property
    simp [patchIndex,h,Shape.exceptionalShape]
  · simp [patchIndex,k.property,Shape.exceptionalShape]
  · simp [patchIndex,k.property,Shape.exceptionalShape]

theorem exists_key (i : I) (h : (A.shape i).exceptionalShape) : ∃ k, A.patchIndex k = i := by
  cases eq : A.shape i with
  | badPath => exact ⟨.inl (.inr ⟨i,eq⟩),rfl⟩
  | badOdd n => exact ⟨.inl (.inl ⟨i,n,eq⟩),rfl⟩
  | divertedSquare => exact ⟨.inr ⟨i,eq⟩,rfl⟩
  | _ => simp [eq,Shape.exceptionalShape] at h

theorem region_none_not_exception (f : X → Bool) (p q : I → Bool) {v : V} (h : A.patchRegion v = none) :
    ¬ ∃ e, A.part f p q e = .exceptional ∧ FamilyIncident D v e := by
  rintro ⟨e,he,hv⟩
  obtain ⟨k,hk⟩ := A.exists_key _ (A.exceptional_of_incidence f p q hv he)
  have eq := (A.patchRegion_eq v k).mpr ((A.inPiece_iff _ _).mpr hk.symm)
  rw [h] at eq
  contradiction

def pathFirst (side : V → Bool) (first : I → Bool) (i : I) : V :=
  A.vertex i (if first i = !(A.pieceSide side i) then 0 else 3)

noncomputable def patchTag (side : V → Bool) (first : I → Bool) (v : V) : Option (A.PatchKey × Bool) := by
  classical
  exact (A.patchRegion v).map fun k => (k,match k with
    | .inl (.inr i) => decide (v = A.pathFirst side first i.val)
    | _ => false)

theorem tag_odd (side : V → Bool) (first : I → Bool) (k : A.OddKey) {v : V} (h : A.InPiece k.val v) :
    A.patchTag side first v = some (.inl (.inl k),false) := by
  simp [patchTag,(A.patchRegion_eq _ (.inl (.inl k))).mpr h]

theorem tag_bad [DecidableEq V] (side : V → Bool) (first : I → Bool) (k : A.BadKey) {v : V} (h : A.InPiece k.val v) :
    A.patchTag side first v = some (.inl (.inr k),decide (v = A.pathFirst side first k.val)) := by
  simp [patchTag,(A.patchRegion_eq _ (.inl (.inr k))).mpr h]

theorem tag_square (side : V → Bool) (first : I → Bool) (k : A.SquareKey) {v : V} (h : A.InPiece k.val v) :
    A.patchTag side first v = some (.inr k,false) := by
  simp [patchTag,(A.patchRegion_eq _ (.inr k)).mpr h]

theorem shared_exception (f : X → Bool) (p q : I → Bool) (e : E) (he : A.part f p q e = .exceptional) :
    ∃ k, A.patchRegion (D.left e) = some k ∧ A.patchRegion (D.right e) = some k := by
  obtain ⟨i,j,rfl,sh⟩ := (A.exceptional_iff f p q e).mp he
  have h : (A.shape i).exceptionalShape := by
    rcases sh with h|⟨n,h⟩|h <;> simp [h,Shape.exceptionalShape]
  obtain ⟨k,hk⟩ := A.exists_key i h
  have own (v) (hv : FamilyIncident D v (A.localLabel i j)) : A.patchRegion v = some k := by
    apply (A.patchRegion_eq ..).mpr
    rw [hk]
    rcases (A.localIncident _ _ _).mp hv with h|h <;> exact ⟨_,h⟩
  exact ⟨k,own _ (Or.inl rfl),own _ (Or.inr rfl)⟩

end Kostochka.FiveRegular.Restoration.Atlas

end

section 

namespace Kostochka.FiveRegular
open SimpleGraph Subdivision
variable {V E : Type*}

def factorJoined (D : Family V E) (part : E → EdgePart) (p : Bool → V → V) (b : Bool) (e f : E) : Prop :=
  ∃ (a : part e = .factor b) (c : part f = .factor b), e ≠ f ∧
    FamilyMeet (contracted D (folded (p b)) part b) ⟨e,a⟩ ⟨f,c⟩

/- Two factor edges conflict if they must remain different when a local piece is recolored.
This records both ordinary incidence and conflicts introduced by folding. -/
def globalConflict (D : Family V E) (part : E → EdgePart) (p : Bool → V → V) : SimpleGraph E where
  Adj e f := ∃ b, factorJoined D part p b e f
  symm.symm _ _ := by rintro ⟨b,a,c,n,v,h,g⟩; exact ⟨b,c,a,Ne.symm n,v,g,h⟩
  loopless.irrefl _ := by rintro ⟨_,_,_,ne,_⟩; exact ne rfl

theorem globalConflict_of_join {D : Family V E} {part : E → EdgePart} {p : Bool → V → V}
    {b : Bool} {x y : V} {e f : E} (he : part e = .factor b) (hf : part f = .factor b)
    (ne : e ≠ f) (ie : FamilyIncident D x e) (jf : FamilyIncident D y f)
    (eq : folded (p b) x = folded (p b) y) : (globalConflict D part p).Adj e f := by
  have lift {v g} (h : part g = .factor b) (hit : FamilyIncident D v g) :
      FamilyIncident (contracted D (folded (p b)) part b) (folded (p b) v) ⟨g,h⟩ :=
    hit.imp (congrArg (folded (p b))) (congrArg (folded (p b)))
  exact ⟨b,he,hf,ne,folded (p b) x,lift he ie,by rw [eq]; exact lift hf jf⟩

theorem globalConflict_of_meet {D : Family V E} {part : E → EdgePart} {p : Bool → V → V}
    {b : Bool} {e f : E} (he : part e = .factor b) (hf : part f = .factor b)
    (ne : e ≠ f) (meet : FamilyMeet D e f) : (globalConflict D part p).Adj e f := by
  obtain ⟨v,x,y⟩ := meet
  exact globalConflict_of_join he hf ne x y rfl

theorem globalConflict_of_partner {D : Family V E} {part : E → EdgePart} {p : Bool → V → V}
    {b : Bool} {x y : V} {e f : E} (he : part e = .factor b) (hf : part f = .factor b) (ne : e ≠ f)
    (ie : FamilyIncident D x e) (jf : FamilyIncident D y f) (hi : Function.Involutive (p b))
    (sw : p b x = y) : (globalConflict D part p).Adj e f :=
  globalConflict_of_join he hf ne ie jf ((folded_eq hi x y).mpr (.inr ((congrArg (p b) sw).symm.trans (hi x)).symm))

theorem globalConflict_sole {D : Family V E} {part : E → EdgePart} {p : Bool → V → V}
    {b : Bool} {v : V} {e : E} (he : part e = .factor b) (ie : FamilyIncident D v e)
    (fixed : p b v = v)
    (one : ∀ k, part k = .factor b → FamilyIncident D v k → k = e)
    (two : AtMostTwo (foldFamily (factorFamily D part b) (p b))) {f g : E}
    (ef : (globalConflict D part p).Adj e f) (eg : (globalConflict D part p).Adj e g) : f = g := by
  have pull {u : E} (a : (globalConflict D part p).Adj e u) :
      ∃ h : part u = .factor b, (labelConflicts (foldFamily (factorFamily D part b) (p b))).Adj ⟨e,he⟩ ⟨u,h⟩ := by
    obtain ⟨d,de,du,n,m⟩ := a
    obtain rfl := EdgePart.factor.inj (de.symm.trans he)
    exact ⟨du,fun eq => n (congrArg Subtype.val eq),m⟩
  obtain ⟨f',lf⟩ := pull ef
  obtain ⟨g',lg⟩ := pull eg
  have atv : UniqueAt (factorFamily D part b) v := fun k h ki hi =>
    Subtype.ext ((one _ k.property ki).trans (one _ h.property hi).symm)
  exact congrArg Subtype.val (mutable_spoke_unique _ _ two fixed atv (e := ⟨e,he⟩) ie lf lg)

noncomputable def labeledStageTwo {D : Family V E} {part : E → EdgePart} {p : Bool → V → V}
    {side : V → Bool} {exc : V → Prop} (c : ∀ b, Nonempty (ContractedPalette D side part exc b (folded (p b)))) :
    StageTwo D side part exc (factorJoined D part p) :=
  stageTwoOfContractions (fun b => folded (p b)) (fun b => Classical.choice (c b)) (fun _ _ _ h => h)

theorem stageTwo_global_proper {D : Family V E} {part : E → EdgePart} {p : Bool → V → V}
    {side : V → Bool} {exc : V → Prop} (P : StageTwo D side part exc (factorJoined D part p)) :
    ProperLabels (globalConflict D part p) P.edge := by
  rintro e f ⟨b,h⟩
  exact P.properSpokes b e f h

namespace Restoration.Atlas
open Auxiliary
variable {I X K : Type*} (A : Atlas D I X K) [Fintype E] [Fintype I] [Fintype X] [Fintype K] [DecidableEq V]

theorem folded_bounds {D : Family V E} (A : Atlas D I X K) {side : V → Bool}
    (C : A.PartitionColors side) (loop : Loopless D)
    (reg : ∀ i (v : Fin (A.shape i).vertices), coloredDegree A.outside (fun _ => true) (A.places ⟨i,v⟩) true +
      oldDegree (A.shape i) v.val = 4) (b : Bool) :
    AtMostTwo (foldFamily (factorFamily D (A.part C.exterior C.first C.second) b) (A.partner side C.first b)) := by
  apply atMostTwo_foldFamily _ (A.partner_involutive side C.first b)
  · apply atMostTwo_selected
    intro v
    have h := A.factor_constraints C reg v
    cases b
    · exact h.1
    · exact h.2.1
  · intro v moved e f x y
    exact Subtype.ext ((A.partner_unique C b loop reg v moved).unique ⟨e.property,x⟩ ⟨f.property,y⟩)
end Restoration.Atlas
end Kostochka.FiveRegular

end

section 

namespace Kostochka.FiveRegular.Restoration.Atlas
open Subdivision Auxiliary SimpleGraph
variable {V E I X K : Type*} {D : Family V E} (A : Atlas D I X K)
variable [Fintype I] [Fintype X] [Fintype E] [Fintype K] [DecidableEq V]
variable {side : V → Bool} (P : A.PartitionColors side) (C : ChartContext A P)

abbrev finalPart := A.part P.exterior P.first P.second
abbrev conflicts := globalConflict D (A.finalPart P) (A.partner side P.first)

include C

omit [Fintype I] [Fintype K] in
theorem spoke_unique_at {v : V} {b : Bool} (s : Spoke (D := D) (A.finalPart P) b v) (deg : A.degreeAt P b v = 1)
    (k : E) (h : A.finalPart P k = .factor b) (hit : FamilyIncident D v k) : k = s.edge := by
  have one : ∃! e, A.finalPart P e = .factor b ∧ FamilyIncident D v e := by
    simpa using (unique_iff_degree D C.loop (fun e => decide (A.finalPart P e = .factor b)) v).mpr deg
  exact one.unique ⟨h,hit⟩ ⟨s.factor,s.incident⟩

theorem spoke_sole_at {v : V} {b : Bool} (s : Spoke (D := D) (A.finalPart P) b v) (same : side v = b)
    (deg : A.degreeAt P b v = 1) {f g : E} (hf : (A.conflicts P).Adj s.edge f) (hg : (A.conflicts P).Adj s.edge g) : f = g :=
  globalConflict_sole s.factor s.incident (A.partner_fixed side P.first b C.mono same) (A.spoke_unique_at P C s deg)
    (A.folded_bounds P C.loop C.regular b) hf hg

omit [Fintype I] [Fintype E] [Fintype K] in
theorem spoke_owns {R : Type*} {i : I} (exc : (A.shape i).exceptionalShape) {v : V} (inside : A.InPiece i v)
    {b : Bool} (s : Spoke (D := D) (A.finalPart P) b v) (sv : side v = b) (tag : V → R) (r : R) (hr : tag v = r) :
    OwnsSpoke D side (A.finalPart P) tag r s.edge := by
  refine ⟨v,hr,s.incident,s.factor.trans (congrArg EdgePart.factor sv.symm),?_⟩
  rcases inside with ⟨k,rfl⟩
  obtain ⟨t,ht,_⟩ := A.exceptional_spoke_is_external _ _ _ exc s.factor s.incident
  exact ht ▸ C.crosses t

omit [Fintype I] [Fintype E] [Fintype K] in
theorem spoke_separate {i : I} (exc : (A.shape i).exceptionalShape) {v w : V} (inside : A.InPiece i v)
    {b : Bool} (s : Spoke (D := D) (A.finalPart P) b v) (t : Spoke (D := D) (A.finalPart P) b w)
    (same : side v = side w) (ne : v ≠ w) : s.edge ≠ t.edge := by
  obtain ⟨k,rfl⟩ := inside
  obtain ⟨x,hx,_⟩ := A.exceptional_spoke_is_external _ _ _ exc s.factor s.incident
  intro eq
  have a := s.incident
  have c := t.incident
  rw [← eq,hx] at c
  rw [hx] at a
  exact ne (crossing_same_end D side (C.crosses x) a c same)

theorem pathChart_range (k : A.BadKey) (v : V) : A.InPiece k.val v ↔ v ∈ Set.range (A.pathChart P C k k.property).row.corner :=
  A.corners_range _ _ _ _

theorem pathChart_first (k : A.BadKey) : (A.pathChart P C k k.property).row.corner 0 = A.pathFirst side P.first k := by
  change A.corners k _ (A.pathFlip P k) 0 = _
  rw [A.corner_vertex]
  unfold pathFirst pathFlip
  cases h : P.first k <;> cases t : A.pieceSide side k <;> rfl

omit C in
private theorem path_move {s : Shape} (sh : s = .badPath) (f b : Bool) (j : Fin 4) :
    let c := (indexOrientation 4 (decide (f = b))).trans (finCongr (show 4 = s.vertices by rw [sh]; rfl))
    j = 0 → s.partnerCoordinate f (!b) (c j) = c 2 := by
  subst s; intro c h; subst j; cases f <;> cases b <;> decide

theorem pathChart_partner (k : A.BadKey) :
    let H := A.pathChart P C k k.property
    (A.partner side P.first (!(A.pieceSide side k))) (H.row.corner 0) = H.row.corner 2 := by
  dsimp only
  change A.partner side P.first _ (A.places ⟨k,A.pathCoord P k k.property 0⟩) = A.places ⟨k,A.pathCoord P k k.property 2⟩
  rw [A.partner_at,if_neg (show A.pieceSide side k ≠ !(A.pieceSide side k) by cases A.pieceSide side k <;> decide)]
  exact congrArg (fun j => A.places ⟨k.val,j⟩) (path_move k.property (P.first k) (A.pieceSide side k) 0 rfl)

theorem path_valid (k : A.BadKey) : (A.pathChart P C k k.property).patch.valid (A.conflicts P) := by
  let H := A.pathChart P C k k.property
  let b := A.pieceSide side k
  constructor
  · intro j x y ef eg
    exact A.spoke_sole_at P C (H.low j) (H.row.side_eq _) (by
      change A.degreeAt P _ ((A.pathRow P C k k.property).corner j.succ) = 1
      simpa using (A.path_degrees P C k k.property j.succ).1) ef eg
  · have ne : (H.high 0).edge ≠ (H.high 2).edge := A.spoke_separate P C (i := k.val) (by simp [k.property,Shape.exceptionalShape])
      ⟨_,rfl⟩ (H.high 0) (H.high 2) ((H.row.side_eq _).trans (H.row.side_eq _).symm) (H.row.corner.injective.ne (by decide))
    exact globalConflict_of_partner (H.high 0).factor (H.high 2).factor ne (H.high 0).incident (H.high 2).incident
      (A.partner_involutive _ _ _) (A.pathChart_partner P C k)

theorem path_fixed_conflict (k : A.BadKey) :
    let H := A.pathChart P C k k.property
    (A.conflicts P).Adj (H.fixed 0).edge (H.fixed 1).edge := by
  let H := A.pathChart P C k k.property
  exact globalConflict_of_meet (H.fixed 0).factor (H.fixed 1).factor H.fixedNe ⟨_,(H.fixed 0).incident,(H.fixed 1).incident⟩

theorem path_last_conflict (k : A.BadKey) :
    let H := A.pathChart P C k k.property
    (A.conflicts P).Adj (H.last 0).edge (H.last 1).edge := by
  let H := A.pathChart P C k k.property
  exact globalConflict_of_meet (H.last 0).factor (H.last 1).factor H.lastNe ⟨_,(H.last 0).incident,(H.last 1).incident⟩

theorem path_mutable_owner (k : A.BadKey) (e : E) (he : e ∈ (A.pathChart P C k k.property).patch.spokes) :
    OwnsSpoke D side (A.finalPart P) (A.patchTag side P.first) (some (.inl (.inr k),false)) e := by
  let H := A.pathChart P C k k.property
  obtain ⟨j,rfl⟩ := he
  have inside : A.InPiece k.val (H.row.corner j.succ) := ⟨_,rfl⟩
  have nf : H.row.corner j.succ ≠ A.pathFirst side P.first k := by
    rw [← A.pathChart_first P C k]; exact H.row.corner.injective.ne (Fin.succ_ne_zero _)
  exact A.spoke_owns P C (by simp [k.property,Shape.exceptionalShape]) inside (H.low j) (H.row.side_eq _) _ _
    (by simpa [nf] using A.tag_bad side P.first k inside)

theorem path_fixed_owner (k : A.BadKey) (e : E) (he : e ∈ (A.pathChart P C k k.property).patch.fixed) :
    OwnsSpoke D side (A.finalPart P) (A.patchTag side P.first) (some (.inl (.inr k),true)) e := by
  let H := A.pathChart P C k k.property
  have inside : A.InPiece k.val (H.row.corner 0) := ⟨_,rfl⟩
  have fix (j : Fin 2) := A.spoke_owns P C (by simp [k.property,Shape.exceptionalShape]) inside (H.fixed j)
    (H.row.side_eq _) (A.patchTag side P.first) (some (.inl (.inr k),true)) (by
      have h := A.tag_bad side P.first k inside
      simpa [show H.row.corner 0 = A.pathFirst side P.first k from A.pathChart_first P C k] using h)
  change e = (H.fixed 0).edge ∨ e = (H.fixed 1).edge at he
  rcases he with rfl|rfl
  · exact fix 0
  · exact fix 1
end Kostochka.FiveRegular.Restoration.Atlas

end

section 

namespace Kostochka.FiveRegular.Restoration.Atlas
open Subdivision Auxiliary SimpleGraph
variable {V E I X K : Type*} {D : Family V E} (A : Atlas D I X K)
variable [Fintype I] [Fintype X] [Fintype E] [Fintype K] [DecidableEq V]
variable {side : V → Bool} (P : A.PartitionColors side) (C : ChartContext A P)
variable (k : A.SquareKey) (W : A.SquareWitness P.exterior (A.pieceSide side k) k)

private noncomputable abbrev Q := A.squareChart P C k k.property W

theorem square_range (v : V) : A.InPiece k.val v ↔ v ∈ Set.range (Q A P C k W).square.v := by
  constructor
  · rintro ⟨j,rfl⟩
    have len : (A.shape k.val).vertices = 4 := by rw [k.property]; rfl
    refine ⟨Fin.cast len j,?_⟩
    change A.places ⟨k.val,vertexAt (A.shape k.val) j.val⟩ = _
    congr 2; apply Fin.ext; exact Nat.mod_eq_of_lt j.isLt
  · rintro ⟨j,rfl⟩; exact ⟨_,rfl⟩

theorem square_mutable_owner (e : E) (he : e ∈ Set.range (Q A P C k W).patch.spoke) :
    OwnsSpoke D side (A.finalPart P) (A.patchTag side P.first) (some (.inr k,false)) e := by
  let S := Q A P C k W
  obtain ⟨j,rfl⟩ := he
  have inside : A.InPiece k.val (S.square.v j) := ⟨_,rfl⟩
  exact A.spoke_owns P C (by simp [k.property,Shape.exceptionalShape]) inside (S.low j) (S.square.mono j) _ _
    (A.tag_square side P.first k inside)

theorem square_upper (j : Fin 4) : UpperSpoke D side (A.finalPart P) ((Q A P C k W).patch.upper j) := by
  let S := Q A P C k W
  refine ⟨S.square.v j,(S.high j).incident,(S.high j).factor.trans (congrArg (EdgePart.factor ∘ Bool.not) (S.square.mono j).symm),?_⟩
  intro e hp inc
  exact (A.spoke_unique_at P C (S.high j) (A.square_degrees P C k k.property j _) e
    (hp.trans (S.high j).factor) inc).symm

private theorem oppositeHit (j : Fin 4) (S := Q A P C k W) :
    FamilyIncident D (S.outside ⟨j.val%2,by omega⟩) (S.low (j+2)).edge := by
  have num : (⟨(j+2 : Fin 4).val%2,by omega⟩ : Fin 2) = ⟨j.val%2,by omega⟩ := by fin_cases j <;> rfl
  rw [← num]
  exact S.outsideHit (j+2)

theorem square_doubled (j : Fin 4) : DoubledSpoke D side (A.finalPart P) ((Q A P C k W).patch.spoke j) := by
  let S := Q A P C k W
  refine ⟨S.square.v j,S.outside ⟨j.val%2,by omega⟩,(S.low (j+2)).edge,(S.low j).incident,S.outsideHit j,
    A.oppositeHit P C k W j (S := S),?_,?_,?_,?_⟩
  · exact S.lowInj.ne (by omega : j ≠ j+2)
  · rw [S.square.mono]
    exact (S.outsideSide _).symm
  · exact (S.low j).factor.trans (congrArg EdgePart.factor (S.square.mono j).symm)
  · exact (S.low (j+2)).factor.trans (S.low j).factor.symm

theorem square_opposite (j : Fin 4) (e : E) (he : (A.conflicts P).Adj ((Q A P C k W).patch.spoke j) e) :
    e = (Q A P C k W).patch.spoke (j+2) := by
  let S := Q A P C k W
  have conflict : (A.conflicts P).Adj (S.low j).edge (S.low (j+2)).edge :=
    globalConflict_of_meet (S.low j).factor (S.low (j+2)).factor (S.lowInj.ne (by omega : j ≠ j+2))
      ⟨_,S.outsideHit j,A.oppositeHit P C k W j (S := S)⟩
  exact A.spoke_sole_at P C (S.low j) (S.square.mono j) (A.square_degrees P C k k.property j _) he conflict

private theorem square_swap {s : Shape} (sh : s = .divertedSquare) (first b : Bool) (j : Fin 4) :
    s.partnerCoordinate first (!b) (vertexAt s j.val) = vertexAt s (j+2 : Fin 4).val := by
  subst s; fin_cases j <;> rfl

theorem square_apart :
    (A.conflicts P).Adj ((Q A P C k W).patch.upper 0) ((Q A P C k W).patch.upper 2) ∧
    (A.conflicts P).Adj ((Q A P C k W).patch.upper 1) ((Q A P C k W).patch.upper 3) := by
  let S := Q A P C k W
  let b := A.pieceSide side k
  have move (j : Fin 4) : A.partner side P.first (!b) (S.square.v j) = S.square.v (j+2) := by
    change A.partner side P.first (!b) (A.places ⟨k.val,vertexAt (A.shape k) j.val⟩) = A.places ⟨k.val,vertexAt (A.shape k) (j+2 : Fin 4).val⟩
    rw [A.partner_at,if_neg (show A.pieceSide side k ≠ !b by change b ≠ !b; cases b <;> decide)]
    exact congrArg (fun r => A.places ⟨k.val,r⟩) (square_swap k.property (P.first k) b j)
  have pair (j : Fin 4) : (A.conflicts P).Adj (S.high j).edge (S.high (j+2)).edge := by
    have ne := A.spoke_separate P C (i := k.val) (by simp [k.property,Shape.exceptionalShape]) ⟨_,rfl⟩
      (S.high j) (S.high (j+2)) ((S.square.mono j).trans (S.square.mono _).symm) (S.square.v.injective.ne (by omega : j ≠ j+2))
    exact globalConflict_of_partner (S.high j).factor (S.high (j+2)).factor ne (S.high j).incident (S.high (j+2)).incident
      (A.partner_involutive _ _ _) (move j)
  exact ⟨pair 0,pair 1⟩

end Kostochka.FiveRegular.Restoration.Atlas

end

section 

namespace MultFive.Multi.PieceDecomposition
open Finset SimpleGraph Kostochka.FiveRegular Subdivision Restoration Auxiliary
variable {V : Type*} [Fintype V] [DecidableEq V] {m : Multi V} {M : m.support.Subgraph} {side : V → Bool}
variable (D : PieceDecomposition m M side) (L : D.LabelCoverage) (P : (D.physical L).PartitionColors side)

theorem final_chartContext (d : D.Index → Bool) (reg : ∀ w, m.degree w = 5) (hm : M.IsPerfectMatching)
    (bound : ∀ v, m.insideDegree side v ≤ 2) :
    ((D.physical L).afterSquareDecision d).ChartContext ((D.physical L).afterSquareColors d side P) := by
  let A := D.physical L
  let F := A.afterSquareDecision d
  refine ⟨m.family_loopless,m.internal_atMostTwo side bound,D.final_regular L d reg hm,?_,?_,?_⟩
  · intro i v
    exact (D.final_monochromatic L d i v).trans (D.final_monochromatic L d i (vertexAt (F.shape i) 0)).symm
  · intro x
    exact exterior_crosses x
  · intro w
    have old (u : V) : ∃! e, F.oldMatching e = true ∧ FamilyIncident m.family u e := by
      simp only [F,A,Atlas.afterSquare_old]
      exact (Atlas.unique_iff_degree _ m.family_loopless _ _).mpr (D.physical_matchDegree L hm u)
    exact (F.perfectMatching _ _ _ m.family_loopless old w).exists

noncomputable def final_squareWitness
    (k : ((D.physical L).afterSquareDecision ((D.physical L).squareDecision P.exterior side)).SquareKey) :
    let F := (D.physical L).afterSquareDecision ((D.physical L).squareDecision P.exterior side)
    F.SquareWitness P.exterior (F.pieceSide side k.val) k.val := by
  let A := D.physical L
  let d := A.squareDecision P.exterior side
  have fresh (z : ResidualPiece m M side) : z.baseShape ≠ .divertedSquare := by
    cases z with
    | badPath _ flag | badOddCycle _ flag => cases flag <;> simp [ResidualPiece.baseShape]
    | _ => simp [ResidualPiece.baseShape]
  have test : d k.val = true := by
    have h := k.property
    change ((D.raw k.val).baseShape).afterSquare (d k.val) = .divertedSquare at h
    unfold Shape.afterSquare at h
    split at h
    next => exact (show (D.raw k.val).baseShape = .evenCycle 1 ∧ d k.val = true from by assumption).2
    next => exact (fresh _ h).elim
  have color : (A.afterSquareDecision d).pieceSide side k.val = A.pieceSide side k.val := by simp [Atlas.pieceSide]
  change (A.afterSquareDecision d).SquareWitness P.exterior ((A.afterSquareDecision d).pieceSide side k.val) k.val
  rw [color]
  exact A.squareWitness_of_decision side P.exterior k.val test

end MultFive.Multi.PieceDecomposition

end

section 

namespace Kostochka.FiveRegular.Restoration

open SimpleGraph Subdivision Auxiliary

private def forward {n : ℕ} (positive : 0 < n) (j : Fin n) : Fin n :=
  if h : j.val+1 < n then ⟨j.val+1,h⟩ else ⟨0,positive⟩
private def back {n : ℕ} (positive : 0 < n) (j : Fin n) : Fin n :=
  if j.val = 0 then ⟨n-1,by omega⟩ else ⟨j.val-1,by have h := j.isLt; omega⟩

private theorem forward_back {n : ℕ} (positive : 0 < n) (j : Fin n) :
    forward positive (back positive j) = j := by
  apply Fin.ext
  have h := j.isLt
  have fv (x : Fin n) : (forward positive x).val = if x.val+1 < n then x.val+1 else 0 := by
    by_cases q : x.val+1 < n <;> simp [forward,q]
  have bv : (back positive j).val = if j.val = 0 then n-1 else j.val-1 := by
    by_cases q : j.val = 0 <;> simp [back,q]
  rw [fv,bv]
  split_ifs <;> omega

private theorem separate_next {n : ℕ} (n3 : 3 ≤ n) (j : Fin n) :
    forward (by omega) j ≠ back (by omega) j := by
  intro eq
  have h := j.isLt
  have val := congrArg Fin.val eq
  simp only [forward,back] at val
  split_ifs at val <;> dsimp at * <;> omega

namespace Atlas
variable {V E I X K : Type*} {D : Family V E} (A : Atlas D I X K)

private theorem at_pos (i : I) (v : Fin (A.shape i).vertices) : A.vertex i v.val = A.places ⟨i,v⟩ := by
  have eq : vertexAt (A.shape i) v.val = v := Fin.ext (Nat.mod_eq_of_lt v.isLt)
  exact congrArg (fun u => A.places ⟨i,u⟩) eq

private theorem rim_label (i : I) (exc : (A.shape i).exceptionalShape)
    (closePath : A.shape i = .badPath → ∃ e, familyPair D e = s(A.vertex i 0,A.vertex i 3))
    (v : Fin (A.shape i).vertices) :
    ∃ e, familyPair D e = s(A.places ⟨i,v⟩,A.places ⟨i,forward (A.shape i).vertices_pos v⟩) := by
  have wrap : vertexAt (A.shape i) (v.val+1) = forward (A.shape i).vertices_pos v := by
    apply Fin.ext
    have h := v.isLt
    by_cases lt : v.val+1 < (A.shape i).vertices
    · simp [vertexAt,forward,lt,Nat.mod_eq_of_lt]
    · have eq : v.val+1 = (A.shape i).vertices := by omega
      simp [vertexAt,forward,eq]
  by_cases valid : v.val < (A.shape i).edges
  · let r : Fin (A.shape i).edges := ⟨v.val,valid⟩
    refine ⟨A.localLabel i r,?_⟩
    rw [A.gap_ends]
    change s(A.vertex i v.val,A.places ⟨i,vertexAt (A.shape i) (v.val+1)⟩) = _
    rw [A.at_pos,wrap]
  have shape : A.shape i = .badPath := by
    have h := v.isLt
    cases sh : A.shape i <;> simp_all [Shape.exceptionalShape,Shape.vertices,Shape.cyclic,Shape.edges] <;> omega
  have hv : v.val = 3 := by
    have h := v.isLt
    simp only [shape] at h valid
    change v.val < 4 at h
    change ¬ v.val < 3 at valid
    omega
  have right : (forward (A.shape i).vertices_pos v).val = 0 := by
    have hn : (A.shape i).vertices = 4 := by rw [shape]; rfl
    simp [forward,hv,hn]
  obtain ⟨e,eq⟩ := closePath shape
  refine ⟨e,?_⟩
  rw [← A.at_pos i v,← A.at_pos i (forward _ v),hv,right,eq,Sym2.eq_swap]

theorem patch_closed (side : V → Bool) (mono : ∀ i (v : Fin (A.shape i).vertices),
    side (A.places ⟨i,v⟩) = A.pieceSide side i)
    (bound : AtMostTwo (restrictFamily D (RawSquare.Internal D side)))
    (closePath : ∀ i, A.shape i = .badPath → ∃ e, familyPair D e = s(A.vertex i 0,A.vertex i 3))
    (e : E) (same : side (D.left e) = side (D.right e)) :
    A.patchRegion (D.left e) = A.patchRegion (D.right e) := by
  have both (k : A.PatchKey) {w : V} (inc : FamilyIncident D w e) (hk : A.patchRegion w = some k) :
      A.patchRegion (D.left e) = some k ∧ A.patchRegion (D.right e) = some k := by
    let i := A.patchIndex k
    let sh := A.shape i
    have shp : sh.exceptionalShape := A.key_shape k
    obtain ⟨j,rfl⟩ := (A.patchRegion_eq w k).mp hk
    let pos : Fin sh.vertices ↪ V := ⟨fun x => A.places ⟨i,x⟩,by intro x y h; simpa using A.places.injective h⟩
    have n3 : 3 ≤ sh.vertices := by cases eq : sh <;> simp_all [Shape.exceptionalShape,Shape.vertices,Shape.cyclic,Shape.edges]
    let prev := back sh.vertices_pos j
    let next := forward sh.vertices_pos j
    obtain ⟨f,hf⟩ := A.rim_label i shp (closePath i) j
    obtain ⟨g,hg⟩ := A.rim_label i shp (closePath i) prev
    rw [show forward sh.vertices_pos prev = j from forward_back _ _] at hg
    have differ : f ≠ g := by
      intro eq
      have pairs := hf.symm.trans (eq ▸ hg)
      rcases Sym2.eq_iff.mp pairs with h|h
      · have a := pos.injective h.1
        have b := pos.injective h.2
        exact separate_next n3 j (b.trans a)
      · exact separate_next n3 j (pos.injective h.2)
    have endData (a c : Fin sh.vertices) (x : E) (p : familyPair D x = s(pos a,pos c)) :
        RawSquare.Internal D side x ∧ FamilyIncident D (pos a) x ∧ FamilyIncident D (pos c) x ∧
        A.patchRegion (D.left x) = some k ∧ A.patchRegion (D.right x) = some k := by
      have ra := (A.patchRegion_eq _ k).mpr (show A.InPiece i (pos a) from ⟨a,rfl⟩)
      have rc := (A.patchRegion_eq _ k).mpr (show A.InPiece i (pos c) from ⟨c,rfl⟩)
      have sc : side (pos a) = side (pos c) := (mono i a).trans (mono i c).symm
      rcases Sym2.eq_iff.mp p with ⟨l,r⟩|⟨l,r⟩ <;>
        simp [RawSquare.Internal,FamilyIncident,l,r,ra,rc,sc]
    have fInfo := endData j next f hf
    have gInfo := endData prev j g hg
    let ce : {x // RawSquare.Internal D side x} := ⟨e,same⟩
    let cf : {x // RawSquare.Internal D side x} := ⟨f,fInfo.1⟩
    let cg : {x // RawSquare.Internal D side x} := ⟨g,gInfo.1⟩
    rcases bound (pos j) ce cf cg inc fInfo.2.1 gInfo.2.2.1 with h|h|h
    · exact (show e = f from congrArg Subtype.val h) ▸ fInfo.2.2.2
    · exact (show e = g from congrArg Subtype.val h) ▸ gInfo.2.2.2
    · exact (differ (congrArg Subtype.val h)).elim
  cases l : A.patchRegion (D.left e) with
  | some k => exact (both k (Or.inl rfl) l).2.symm
  | none =>
    cases r : A.patchRegion (D.right e) with
    | none => rfl
    | some k => rw [← (both k (Or.inr rfl) r).1,l]

end Atlas
end Kostochka.FiveRegular.Restoration

end

section 

namespace Kostochka.FiveRegular
open SimpleGraph Subdivision Finset Four.PathCover
variable {V E : Type*} [Fintype E]

noncomputable def incidentSet (D : Family V E) (v : V) : Finset E := by
  classical
  exact univ.filter (FamilyIncident D v)

theorem incidentSet_mem (D : Family V E) (v : V) (e : E) :
    e ∈ incidentSet D v ↔ FamilyIncident D v e := by classical simp [incidentSet]

theorem covers_of_five (D : Family V E) (v : V) (bound : (incidentSet D v).card ≤ 5)
    (s : Fin 5 → E) (inj : Function.Injective s) (hits : ∀ i, FamilyIncident D v (s i))
    (e : E) (h : FamilyIncident D v e) : ∃ i, s i = e := by
  classical
  have eq : univ.image s = incidentSet D v := by
    apply eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i,_,rfl⟩ := mem_image.mp hx
      exact (incidentSet_mem _ _ _).mpr (hits i)
    · simpa [card_image_of_injective _ inj] using bound
  have mem : e ∈ univ.image s := eq ▸ (incidentSet_mem _ _ _).mpr h
  simpa using mem

theorem incidentSet_le_degree [DecidableEq V] (D : Family V E) (v : V) :
    (incidentSet D v).card ≤ coloredDegree D (fun _ => true) v true := by
  classical
  have cover : incidentSet D v ⊆ (univ.filter fun e => v = D.left e) ∪ (univ.filter fun e => v = D.right e) := by
    intro e he
    simpa only [mem_union,mem_filter,mem_univ,true_and,FamilyIncident] using (incidentSet_mem _ _ _).mp he
  exact (card_le_card cover).trans ((card_union_le _ _).trans (by simp [coloredDegree]))

theorem covers_of_regular_degree [DecidableEq V] (D : Family V E)
    (reg : ∀ v, coloredDegree D (fun _ => true) v true ≤ 5) (v : V) (s : Fin 5 → E)
    (inj : Function.Injective s) (hits : ∀ i, FamilyIncident D v (s i)) (e : E)
    (h : FamilyIncident D v e) : ∃ i, s i = e :=
  covers_of_five D v ((incidentSet_le_degree D v).trans (reg v)) s inj hits e h

end Kostochka.FiveRegular

end

section 

namespace Kostochka.FiveRegular.Restoration.Atlas
open SimpleGraph Subdivision Auxiliary

variable {V E I X K : Type} {D : Family V E} (A : Atlas D I X K)

structure PaintedSite (side : V → Bool) (part : E → EdgePart) (k : A.PatchKey) (f : E → Fin 3) where
  W : Type
  R : Type
  scheme : StarScheme W R E
  placement : PlacedScheme scheme D side part A.patchRegion k
  painted : Nonempty (LocalPaint scheme f)

structure OpenSite (side : V → Bool) (first : I → Bool) (part : E → EdgePart) (k : A.OpenKey) where
  patch : OpenException E
  valid : patch.valid (globalConflict D part (A.partner side first))
  mutableOwner : ∀ e, e ∈ patch.spokes →
    OwnsSpoke D side part (A.patchTag side first) (some (.inl k,false)) e
  fixedOwner : ∀ e, e ∈ patch.fixed →
    OwnsSpoke D side part (A.patchTag side first) (some (.inl k,true)) e
  paint : ∀ f, ProperLabels (globalConflict D part (A.partner side first)) f → patch.complete f →
    Nonempty (A.PaintedSite side part (.inl k) f)

structure SquareSite (side : V → Bool) (first : I → Bool) (part : E → EdgePart) (k : A.SquareKey) where
  patch : SquareSpokePatch E
  opposite : ∀ i e, (globalConflict D part (A.partner side first)).Adj (patch.spoke i) e → e = patch.spoke (i+2)
  apart : (globalConflict D part (A.partner side first)).Adj (patch.upper 0) (patch.upper 2) ∧
    (globalConflict D part (A.partner side first)).Adj (patch.upper 1) (patch.upper 3)
  mutableOwner : ∀ e, e ∈ Set.range patch.spoke →
    OwnsSpoke D side part (A.patchTag side first) (some (.inr k,false)) e
  upper : ∀ i, UpperSpoke D side part (patch.upper i)
  doubled : ∀ i, DoubledSpoke D side part (patch.spoke i)
  paint : ∀ f, SquareDone (f ∘ patch.upper) (f ∘ patch.spoke) →
    Nonempty (A.PaintedSite side part (.inr k) f)

variable [Fintype E] [Fintype I] [DecidableEq V]

theorem complete_regions (side : V → Bool) (exterior : X → Bool) (first second : I → Bool)
    (mono : ∀ i (v : Fin (A.shape i).vertices), side (A.places ⟨i,v⟩) = A.pieceSide side i)
    (inside : AtMostTwo (restrictFamily D (RawSquare.Internal D side)))
    (closePath : ∀ i, A.shape i = .badPath → ∃ e, familyPair D e = s(A.vertex i 0,A.vertex i 3))
    (reg : ∀ v, coloredDegree D (fun _ => true) v true ≤ 5)
    (initial : ∀ b, Nonempty (ContractedPalette D side (A.part exterior first second)
      (fun v => ∃ e, A.part exterior first second e = .exceptional ∧ FamilyIncident D v e)
      b (folded (A.partner side first b))))
    (openSites : ∀ k, Nonempty (A.OpenSite side first (A.part exterior first second) k))
    (squareSites : ∀ k, Nonempty (A.SquareSite side first (A.part exterior first second) k)) :
    Nonempty (GluedLayers D side (A.part exterior first second)) := by
  classical
  let part := A.part exterior first second
  let op (k) := Classical.choice (openSites k)
  let sq (k) := Classical.choice (squareSites k)
  let S := labeledStageTwo initial
  obtain ⟨f,valid,openDone,squareDone,hold⟩ := patch_from_spoke_geometry D side part
    (globalConflict D part (A.partner side first)) (fun k => (op k).patch) (fun k => (sq k).patch)
    (A.patchTag side first) (fun k => (op k).valid) (fun k => (sq k).opposite) (fun k => (sq k).apart)
    (fun k => (op k).mutableOwner) (fun k => (sq k).mutableOwner) (fun k => (op k).fixedOwner)
    (fun k => (sq k).upper) (fun k => (sq k).doubled) S.edge (stageTwo_global_proper S)
  have paint : ∀ k : A.PatchKey, Nonempty (A.PaintedSite side part k f) := by
    rintro (k|k)
    · exact (op k).paint f valid (openDone k)
    · exact (sq k).paint f (squareDone k)
  let site k := Classical.choice (paint k)
  have close := A.patch_closed side mono inside closePath
  obtain ⟨stars⟩ := region_stars_of_schemes (fun k => (site k).scheme) D side part A.patchRegion
    (fun k => (site k).placement) f (fun k => (site k).painted) close (covers_of_regular_degree D reg)
  apply layers_of_region_stars D side part A.patchRegion S.vertex f stars close (A.shared_exception exterior first second)
  · intro e same free
    exact S.properVertex e (A.region_none_not_exception _ _ _ free)
      (A.region_none_not_exception _ _ _ ((close e same).symm.trans free)) same
  · exact fun _ _ _ he hf ne meet => valid _ _ (globalConflict_of_meet he hf ne meet)
  · intro v e free he inc
    have no (k : A.PatchKey) (flag : Bool) : ¬ OwnsSpoke D side part (A.patchTag side first) (some (k,flag)) e := by
      rintro ⟨u,owned,hit,ep,cross⟩
      have same := crossing_same_end D side cross inc hit (EdgePart.factor.inj (he.symm.trans ep))
      have empty : A.patchTag side first v = none := by simp [patchTag,free]
      rw [same,owned] at empty
      contradiction
    rw [hold e (fun k h => no _ _ ((op k).mutableOwner _ h))
      (fun k h => no _ _ ((sq k).mutableOwner _ h))]
    exact S.properIncidence _ v e rfl (A.region_none_not_exception _ _ _ free) he inc

end Kostochka.FiveRegular.Restoration.Atlas

end

section 

namespace Kostochka.FiveRegular.Restoration.Atlas
open Subdivision Auxiliary
variable {V E I X K : Type} {D : Family V E} (A : Atlas D I X K)
variable [Fintype E] [Fintype I] [Fintype X] [Fintype K] [DecidableEq V]
variable {side : V → Bool} (P : A.PartitionColors side) (C : A.ChartContext P)

include C in
theorem bad_site (k : A.BadKey) : Nonempty (A.OpenSite side P.first (A.finalPart P) (.inr k)) := by
  let H := A.pathChart P C k k.property
  refine ⟨⟨H.patch,A.path_valid P C k,A.path_mutable_owner P C k,A.path_fixed_owner P C k,?_⟩⟩
  intro f proper done
  refine ⟨⟨_,_,_,H.place A.patchRegion (.inl (.inr k)) (fun v => (A.patchRegion_eq v _).trans (A.pathChart_range P C k v))
      C.bound C.loop C.selected C.selected_hit C.selected_role,?_⟩⟩
  exact local_bad_path _ _ _ _ _ f done (proper _ _ (A.path_fixed_conflict P C k)) (proper _ _ (A.path_last_conflict P C k))

include C in
theorem square_site (k : A.SquareKey) (W : A.SquareWitness P.exterior (A.pieceSide side k.val) k.val) :
    Nonempty (A.SquareSite side P.first (A.finalPart P) k) := by
  let Q := A.squareChart P C k.val k.property W
  refine ⟨⟨Q.patch,A.square_opposite P C k W,A.square_apart P C k W,A.square_mutable_owner P C k W,
    A.square_upper P C k W,A.square_doubled P C k W,?_⟩⟩
  intro f done
  exact ⟨⟨_,_,_,Q.place A.patchRegion (.inr k) (fun v => (A.patchRegion_eq v _).trans (A.square_range P C k W v))
    C.bound C.loop C.selected C.selected_hit C.selected_role,local_square _ f done⟩⟩

end Kostochka.FiveRegular.Restoration.Atlas

end

section 

namespace Kostochka.FiveRegular
open SimpleGraph

def ringNext {n : ℕ} (i : Fin n) : Fin n :=
  if h : i.val+1 < n then ⟨i.val+1,h⟩ else ⟨0,by have := i.isLt; omega⟩

def ringPrev {n : ℕ} (i : Fin n) : Fin n :=
  if i.val = 0 then ⟨n-1,by have := i.isLt; omega⟩ else ⟨i.val-1,by have := i.isLt; omega⟩

theorem ringNext_val {n : ℕ} (i : Fin n) :
    (ringNext i).val = if i.val+1 < n then i.val+1 else 0 := by
  by_cases h : i.val+1 < n <;> simp [ringNext,h]

theorem ringPrev_val {n : ℕ} (i : Fin n) :
    (ringPrev i).val = if i.val = 0 then n-1 else i.val-1 := by
  by_cases h : i.val = 0 <;> simp [ringPrev,h]

@[simp] theorem ringNext_prev {n : ℕ} (i : Fin n) : ringNext (ringPrev i) = i := by
  apply Fin.ext
  simp only [ringNext_val,ringPrev_val]
  have h := i.isLt
  split_ifs <;> first | contradiction | (simp_all only [iff_false]; omega) | omega

@[simp] theorem ringPrev_next {n : ℕ} (i : Fin n) : ringPrev (ringNext i) = i := by
  apply Fin.ext
  simp only [ringPrev_val,ringNext_val]
  have h := i.isLt
  split_ifs <;> first | contradiction | (simp_all only [iff_false]; omega) | omega

theorem ringNext_injective {n : ℕ} : Function.Injective (ringNext (n := n)) :=
  fun _ _ h => by simpa using congrArg ringPrev h

theorem ringNext_ne_prev {n : ℕ} (width : 3 ≤ n) (i : Fin n) : ringNext i ≠ ringPrev i := by
  intro h
  have same := congrArg Fin.val h
  simp only [ringNext_val,ringPrev_val] at same
  have hi := i.isLt
  split_ifs at same <;> omega

def logicalOdd {t : ℕ} : Option (Fin (2*t)) ≃ Fin (2*t+1) where
  toFun := Option.elim' 0 Fin.succ
  invFun := Fin.cases none some
  left_inv := by rintro (_|i) <;> rfl
  right_inv := by intro i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem oddForward_iff {t : ℕ} (ht : 0 < t) (x y : Option (Fin (2*t))) :
    oddForward ht x y ↔ ringNext (logicalOdd x) = logicalOdd y := by
  have one : 0+1 < 2*t+1 := by omega
  rw [Fin.ext_iff,ringNext_val]
  cases x with
  | none =>
    cases y with
    | none =>
      change False ↔ (if 0+1 < 2*t+1 then 0+1 else 0) = 0
      rw [if_pos one]; decide
    | some j =>
      change j.val = 0 ↔ (if 0+1 < 2*t+1 then 0+1 else 0) = j.val+1
      rw [if_pos one]; omega
  | some i =>
    have h := i.isLt
    cases y with
    | none =>
      change i.val = 2*t-1 ↔ (if i.val+1+1 < 2*t+1 then i.val+1+1 else 0) = 0
      split_ifs <;> first | contradiction | (simp_all only [iff_false]; omega) | omega
    | some j =>
      change i.val+1 = j.val ↔ (if i.val+1+1 < 2*t+1 then i.val+1+1 else 0) = j.val+1
      have := j.isLt
      split_ifs <;> first | contradiction | (simp_all only [iff_false]; omega) | omega

def oddGapIndex {t : ℕ} : (Fin t ⊕ Fin (t+1)) ↪ Fin (2*t+1) where
  toFun
    | .inl k => ⟨2*k.val+1,by have := k.isLt; omega⟩
    | .inr j => ⟨2*j.val,by have := j.isLt; omega⟩
  inj' := by
    rintro (k|j) (k'|j') eq <;> have h := congrArg Fin.val eq <;> dsimp only at h
    · congr 1; apply Fin.ext; omega
    · omega
    · omega
    · congr 1; apply Fin.ext; omega

theorem odd_rim_lower {t : ℕ} (i : Fin (2*t)) :
    logicalOdd (some i) = oddGapIndex (.inl (lowerPair i)) ∨
    logicalOdd (some i) = ringNext (oddGapIndex (.inl (lowerPair i))) := by
  simp only [Fin.ext_iff,ringNext_val]
  change i.val+1 = 2*(i.val/2)+1 ∨ i.val+1 = if 2*(i.val/2)+1+1 < 2*t+1 then 2*(i.val/2)+1+1 else 0
  have h := i.isLt
  split_ifs <;> first | contradiction | (simp_all only [iff_false]; omega) | omega

theorem odd_rim_upper {t : ℕ} (i : Fin (2*t)) :
    logicalOdd (some i) = oddGapIndex (.inr (upperGap i)) ∨
    logicalOdd (some i) = ringNext (oddGapIndex (.inr (upperGap i))) := by
  simp only [Fin.ext_iff,ringNext_val]
  change i.val+1 = 2*((i.val+1)/2) ∨ i.val+1 = if 2*((i.val+1)/2)+1 < 2*t+1 then 2*((i.val+1)/2)+1 else 0
  have h := i.isLt
  split_ifs <;> first | contradiction | (simp_all only [iff_false]; omega) | omega

theorem odd_rim_seam {t : ℕ} : logicalOdd (t := t) none = oddGapIndex (.inr 0) ∧
    logicalOdd (t := t) none = ringNext (oddGapIndex (.inr (Fin.last t))) := by
  refine ⟨rfl,?_⟩
  apply Fin.ext
  rw [ringNext_val]; change 0 = if 2*t+1 < 2*t+1 then _ else 0
  simp

end Kostochka.FiveRegular

end

section 

namespace Kostochka.FiveRegular.Restoration.Atlas
open SimpleGraph Subdivision Auxiliary Finset
variable {V E I X K : Type} {D : Family V E} (A : Atlas D I X K)

structure OddRing (D : Family V E) (t : ℕ) where
  corner : Fin (2*t+1) ↪ V
  edge : Fin (2*t+1) ↪ E
  ends : ∀ j, familyPair D (edge j) = s(corner j,corner (ringNext j))

def oddRing (i : I) (n : ℕ) (hs : A.shape i = .badOdd n) : OddRing D (n+1) := by
  have lv : 2*(n+1)+1 = (A.shape i).vertices := by rw [hs]; simp [Shape.vertices,Shape.cyclic,Shape.edges]; omega
  have le : 2*(n+1)+1 = (A.shape i).edges := by rw [hs]; simp [Shape.edges]; omega
  let v : Fin (2*(n+1)+1) ↪ V := ⟨fun k => A.places ⟨i,Fin.cast lv k⟩,fun a b eq => by
    have he := eq_of_heq (Sigma.ext_iff.mp (A.places.injective eq)).2
    exact Fin.ext (congrArg (fun z : Fin (A.shape i).vertices => z.val) he)⟩
  let e : Fin (2*(n+1)+1) ↪ E := ⟨fun k => A.localLabel i (Fin.cast le k),fun a b eq => by
    have same := A.localLabel_injective (a₁ := ⟨i,Fin.cast le a⟩) (a₂ := ⟨i,Fin.cast le b⟩) (show A.localLabel i (Fin.cast le a) = A.localLabel i (Fin.cast le b) from eq)
    exact Fin.ext (congrArg (fun z : Fin (A.shape i).edges => z.val) (eq_of_heq (Sigma.ext_iff.mp same).2))⟩
  refine ⟨v,e,fun j => ?_⟩
  have left : (A.shape i).family.left (Fin.cast le j) = Fin.cast lv j := Fin.ext rfl
  have right : (A.shape i).family.right (Fin.cast le j) = Fin.cast lv (ringNext j) := by
    apply Fin.ext
    simp only [Shape.family,Fin.val_cast,ringNext_val]
    split_ifs <;> simp_all <;> omega
  exact (A.endpoints i (Fin.cast le j)).trans (by rw [left,right]; rfl)

theorem oddRing_corner (i : I) (n) (hs : A.shape i = .badOdd n) (j) :
    (A.oddRing i n hs).corner j = A.places ⟨i,⟨j.val,by have h := j.isLt; simpa [hs,Shape.vertices,Shape.cyclic,Shape.edges,Nat.mul_add,Nat.add_assoc] using h⟩⟩ := rfl

theorem oddRing_range (i : I) (n) (hs : A.shape i = .badOdd n) (v : V) :
    A.InPiece i v ↔ v ∈ Set.range (A.oddRing i n hs).corner := by
  constructor
  · rintro ⟨k,rfl⟩
    have lv : (A.shape i).vertices = 2*(n+1)+1 := by rw [hs]; simp [Shape.vertices,Shape.cyclic,Shape.edges]; omega
    exact ⟨Fin.cast lv k,rfl⟩
  · rintro ⟨j,rfl⟩
    exact ⟨_,A.oddRing_corner i n hs j⟩

theorem oddRing_role [Fintype X] [DecidableEq V] (C : A.PartitionColors side) (i : I) (n) (hs : A.shape i = .badOdd n) (j) :
    A.part C.exterior C.first C.second ((A.oddRing i n hs).edge j) = .exceptional := by
  change A.part _ _ _ (A.localLabel i _) = _
  rw [A.part_local]; simp [hs,Shape.role,asPart]

namespace OddRing
variable {A} {t : ℕ} (B : OddRing D t)

def position (w : Option (Fin (2*t))) : Fin (2*t+1) := ringNext (logicalOdd w)

def body : Option (Fin (2*t)) ↪ V := ⟨fun w => B.corner (position w),fun _ _ h =>
  logicalOdd.injective (ringNext_injective (B.corner.injective h))⟩

theorem body_range (v : V) : v ∈ Set.range B.corner ↔ v ∈ Set.range B.body := by
  constructor
  · rintro ⟨j,rfl⟩
    refine ⟨logicalOdd.symm (ringPrev j),?_⟩
    change B.corner (ringNext (logicalOdd (logicalOdd.symm (ringPrev j)))) = _
    simp
  · rintro ⟨w,rfl⟩; exact ⟨position w,rfl⟩

def rim : (Fin t ⊕ Fin (t+1)) ↪ E := oddGapIndex.trans
  ((⟨ringNext,ringNext_injective⟩ : Fin (2*t+1) ↪ _).trans B.edge)

theorem incident {w : Option (Fin (2*t))} {j : Fin t ⊕ Fin (t+1)}
    (h : logicalOdd w = oddGapIndex j ∨ logicalOdd w = ringNext (oddGapIndex j)) :
    FamilyIncident D (B.body w) (B.rim j) := by
  apply Sym2.mem_iff.mp
  change B.corner (ringNext (logicalOdd w)) ∈ familyPair D (B.edge (ringNext (oddGapIndex j)))
  rw [B.ends]
  rcases h with h|h <;> rw [h] <;> simp

theorem support_adj (ht : 0 < t) (i : Fin (2*t+1)) : (support D).Adj (B.corner i) (B.corner (ringNext i)) := by
  refine ⟨⟨B.edge i,B.ends i⟩,B.corner.injective.ne ?_⟩
  intro eq
  have h := congrArg Fin.val eq
  rw [ringNext_val] at h
  have hi := i.isLt
  split_ifs at h <;> omega

theorem neighbors [Fintype V] [DecidableEq V] (side : V → Bool) (ht : 0 < t)
    (bound : AtMostTwo (restrictFamily D (RawSquare.Internal D side))) (loop : Loopless D)
    (same : ∀ j k, side (B.corner j) = side (B.corner k)) (e : E) {x y}
    (hx : D.left e = B.body x) (hy : D.right e = B.body y) : oddForward ht x y ∨ oddForward ht y x := by
  classical
  let i := position x
  let j := position y
  have adj : (support D).Adj (B.corner i) (B.corner j) := by
    exact ⟨⟨e,congrArg₂ (fun a b => s(a,b)) hx hy⟩,fun eq => loop e (hx.trans (eq.trans hy.symm))⟩
  have get : ringNext i = j ∨ ringNext j = i := by
    by_cases h : ringNext i = j
    · exact .inl h
    by_cases p : ringPrev i = j
    · exact .inr (p ▸ ringNext_prev i)
    have prev : (support D).Adj (B.corner i) (B.corner (ringPrev i)) := by simpa using (B.support_adj ht (ringPrev i)).symm
    have mem (k : Fin (2*t+1)) (a : (support D).Adj (B.corner i) (B.corner k)) :
        B.corner k ∈ univ.filter (fun w => (support D).Adj (B.corner i) w ∧ side (B.corner i) = side w) :=
      mem_filter.mpr ⟨mem_univ _,a,same _ _⟩
    apply False.elim
    apply not_lt.mpr (inside_support_bound D side bound (B.corner i))
    exact two_lt_card_iff.mpr ⟨_,_,_,mem _ (B.support_adj ht i),mem _ prev,mem _ adj,
      B.corner.injective.ne (ringNext_ne_prev (by omega) i),B.corner.injective.ne h,B.corner.injective.ne p⟩
  exact get.imp (fun h => (oddForward_iff ht x y).mpr (ringNext_injective h))
    (fun h => (oddForward_iff ht y x).mpr (ringNext_injective h))

end OddRing
end Kostochka.FiveRegular.Restoration.Atlas

end

section 

namespace Kostochka.FiveRegular.Restoration.Atlas
open SimpleGraph Subdivision Auxiliary Finset
variable {V E I X K : Type} {D : Family V E} (A : Atlas D I X K)

structure LabeledOddChart (D : Family V E) (side : V → Bool) (part : E → EdgePart)
    (p : Bool → V → V) (home : V → Prop) (t : ℕ) where
  positive : 0 < t
  low : Option (Fin (2*t)) ↪ E
  upper : Option (Fin (2*t)) → E
  valid : (OpenException.odd t positive low upper).valid (globalConflict D part p)
  owned : ∀ j, ∃ v, home v ∧ FamilyIncident D v (low j) ∧ part (low j) = .factor (side v) ∧
    side (D.left (low j)) ≠ side (D.right (low j))
  place : ∀ {R : Type} (region : V → Option R) (k : R), (∀ v, region v = some k ↔ home v) →
    PlacedScheme (oddScheme positive low upper) D side part region k

def LabeledOddChart.patch {side : V → Bool} {part : E → EdgePart} {p : Bool → V → V} {home : V → Prop} {t}
    (c : LabeledOddChart D side part p home t) : OpenException E := .odd t c.positive c.low c.upper

def oddCoord (i : I) (n : ℕ) (hs : A.shape i = .badOdd n) : Option (Fin (2*(n+1))) ↪ Fin (A.shape i).vertices := by
  have len : 2*(n+1)+1 = (A.shape i).vertices := by rw [hs]; simp [Shape.vertices,Shape.cyclic,Shape.edges]; omega
  exact logicalOdd.toEmbedding.trans ((⟨ringNext,ringNext_injective⟩ : Fin (2*(n+1)+1) ↪ _).trans (finCongr len).toEmbedding)

theorem odd_body_at (i : I) (n) (hs : A.shape i = .badOdd n) (w) :
    (A.oddRing i n hs).body w = A.places ⟨i,(A.oddCoord i n hs) w⟩ := rfl

private theorem swap_odd_coord (s : Shape) (n : ℕ) (h : s = .badOdd n) (a b : Fin s.vertices)
    (ha : a.val = 0) (hb : b.val = 2) (p q : Bool) : s.partnerCoordinate p q a = b := by
  subst s
  have first : a = ⟨0,by simp [Shape.vertices,Shape.cyclic,Shape.edges]⟩ := Fin.ext ha
  have third : b = ⟨2,by simp [Shape.vertices,Shape.cyclic,Shape.edges]⟩ := Fin.ext hb
  subst a; subst b
  exact Equiv.swap_apply_left _ _

private theorem odd_partner (side : V → Bool) (p : I → Bool) (i : I) (n) (hs : A.shape i = .badOdd n) :
    let B := A.oddRing i n hs
    let b := A.pieceSide side i
    A.partner side p (!b) (B.body (some ⟨2*(n+1)-1,by omega⟩)) = B.body (some ⟨0,by omega⟩) := by
  dsimp only
  rw [A.odd_body_at,A.odd_body_at,A.partner_at,if_neg (by cases A.pieceSide side i <;> decide)]
  apply congrArg (fun j => A.places ⟨i,j⟩)
  apply swap_odd_coord (A.shape i) n hs
  · change (ringNext (logicalOdd (some ⟨2*(n+1)-1,by omega⟩))).val = 0
    rw [ringNext_val]; change (if 2*(n+1)-1+1+1<2*(n+1)+1 then _ else 0) = 0
    rw [if_neg (by omega)]
  · change (ringNext (logicalOdd (some ⟨0,by omega⟩))).val = 2
    rw [ringNext_val]; change (if 0+1+1<2*(n+1)+1 then _ else 0) = 2
    rw [if_pos (by omega)]
    rfl

private theorem odd_third (s : Shape) (n) (hs : s = .badOdd n) (a b : Bool) (v : Fin s.vertices) :
    s.thirdDegree a b v.val = 2 := by
  subst s; exact (Shape.badOdd n).thirdStructure a b v

variable [Fintype V] [Fintype E] [Fintype I] [Fintype X] [Fintype K] [DecidableEq V]

noncomputable def labeledOddChart {side : V → Bool} (C : A.PartitionColors side) (loop : Loopless D)
    (mono : ∀ i (v : Fin (A.shape i).vertices), side (A.places ⟨i,v⟩) = A.pieceSide side i)
    (cross : ∀ x, side (A.outside.left x) ≠ side (A.outside.right x))
    (reg : ∀ i (v : Fin (A.shape i).vertices), coloredDegree A.outside (fun _ => true) (A.places ⟨i,v⟩) true + oldDegree (A.shape i) v.val = 4)
    (bound : AtMostTwo (restrictFamily D (RawSquare.Internal D side)))
    (matchAt : ∀ v, ∃ e, A.part C.exterior C.first C.second e = .matching ∧ FamilyIncident D v e)
    (i : I) (n : ℕ) (hs : A.shape i = .badOdd n) :
    LabeledOddChart D side (A.part C.exterior C.first C.second) (A.partner side C.first) (A.InPiece i) (n+1) := by
  classical
  let B := A.oddRing i n hs
  let v := B.body
  let b := A.pieceSide side i
  let part := A.part C.exterior C.first C.second
  have exc : (A.shape i).exceptionalShape := by simp [hs,Shape.exceptionalShape]
  have cv (j) : v j = A.places ⟨i,(A.oddCoord i n hs) j⟩ := A.odd_body_at i n hs j
  have inPiece (j) : A.InPiece i (v j) := ⟨_,cv j⟩
  have same (j) : side (v j) = b := (congrArg side (cv j)).trans (mono i _)
  have monoRing (j) : side (B.corner j) = b := (congrArg side (A.oddRing_corner i n hs j)).trans (mono i _)
  have one (j) (k : Bool) : ∃! e, part e = .factor k ∧ FamilyIncident D (v j) e := by
    rw [cv]
    apply A.uniqueSpoke _ _ _ i _ k loop (reg i _) (C.balanced i _)
    exact odd_third _ _ hs _ _ _
  let s (k : Bool) (j) : Spoke (D := D) part k (v j) := ⟨(one j k).exists.choose,
    (one j k).exists.choose_spec.1,(one j k).exists.choose_spec.2⟩
  have inj (c : Bool) : Function.Injective (fun j => (s c j).edge) := by
    intro x y eq
    change (s c x).edge = (s c y).edge at eq
    have inc := Eq.mp (congrArg (fun w => FamilyIncident D w (s c x).edge) (cv x)) (s c x).incident
    obtain ⟨z,hz,_⟩ := A.exceptional_spoke_is_external C.exterior C.first C.second exc (s c x).factor inc
    have e₀ := (s c x).incident
    have e₁ := (s c y).incident
    rw [← eq] at e₁
    rw [hz] at e₀ e₁
    exact v.injective (crossing_same_end D side (cross z) e₀ e₁ ((same x).trans (same y).symm))
  let low : Option (Fin (2*(n+1))) ↪ E := ⟨fun j => (s b j).edge,inj b⟩
  let upper := fun j => (s (!b) j).edge
  have valid : (OpenException.odd (n+1) (by omega) low upper).valid (globalConflict D part (A.partner side C.first)) := by
    constructor
    · intro j f g hf hg
      have fixed : A.partner side C.first b (v j) = v j := A.partner_fixed side C.first b mono (same j)
      exact globalConflict_sole (s b j).factor (s b j).incident fixed
        (fun k pk hk => (one j b).unique ⟨pk,hk⟩ ⟨(s b j).factor,(s b j).incident⟩)
        (A.folded_bounds C loop reg b) hf hg
    · let last : Option (Fin (2*(n+1))) := some ⟨2*(n+1)-1,by omega⟩
      let first : Option (Fin (2*(n+1))) := some ⟨0,by omega⟩
      have diff : last ≠ first := by intro eq; have ij := congrArg Fin.val (Option.some.inj eq); change 2*(n+1)-1=0 at ij; omega
      exact globalConflict_of_partner (s (!b) last).factor (s (!b) first).factor ((inj (!b)).ne diff)
        (s (!b) last).incident (s (!b) first).incident (A.partner_involutive side C.first _)
        (A.odd_partner side C.first i n hs)
  refine ⟨by omega,low,upper,valid,?_,?_⟩
  · intro j
    have inc := Eq.mp (congrArg (fun w => FamilyIncident D w (s b j).edge) (cv j)) (s b j).incident
    obtain ⟨z,eq,_⟩ := A.exceptional_spoke_is_external C.exterior C.first C.second exc (s b j).factor inc
    refine ⟨v j,inPiece j,(s b j).incident,(s b j).factor.trans (congrArg EdgePart.factor (same j).symm),?_⟩
    change side (D.left (s b j).edge) ≠ side (D.right (s b j).edge)
    rw [eq]; exact cross z
  · intro R region k membership
    let matchE w := (matchAt (v w)).choose
    have matchHit w := (matchAt (v w)).choose_spec.2
    have matchRole w := (matchAt (v w)).choose_spec.1
    have rimRole (j) : part (B.rim j) = .exceptional := A.oddRing_role C i n hs _
    refine ⟨b,v,B.rim,matchE,fun x => (membership x).trans ((A.oddRing_range i n hs x).trans (B.body_range x)),
      same,fun e x y l r => B.neighbors side (by omega) bound loop (fun _ _ => (monoRing _).trans (monoRing _).symm) e l r,?_,?_⟩
    · intro w j
      cases w with
      | none =>
        fin_cases j
        · exact (s b none).incident
        · exact (s (!b) none).incident
        · exact B.incident (.inl odd_rim_seam.1)
        · exact B.incident (.inr odd_rim_seam.2)
        · exact matchHit _
      | some w =>
        fin_cases j
        · exact (s b (some w)).incident
        · exact B.incident (odd_rim_lower w)
        · exact (s (!b) (some w)).incident
        · exact B.incident (odd_rim_upper w)
        · exact matchHit _
    · intro w j
      cases w with
      | none => fin_cases j <;> first | exact (s b none).factor | exact (s (!b) none).factor | exact rimRole _ | exact matchRole _
      | some w => fin_cases j <;> first | exact (s b (some w)).factor | exact (s (!b) (some w)).factor | exact rimRole _ | exact matchRole _

end Kostochka.FiveRegular.Restoration.Atlas

end

section 

namespace Kostochka.FiveRegular.Restoration.Atlas
open Subdivision Auxiliary
variable {V E I X K : Type} {D : Family V E} (A : Atlas D I X K)
variable [Fintype V] [Fintype E] [Fintype I] [Fintype X] [Fintype K] [DecidableEq V]

theorem odd_site {side : V → Bool} (P : A.PartitionColors side) (C : A.ChartContext P) (k : A.OddKey) :
    Nonempty (A.OpenSite side P.first (A.part P.exterior P.first P.second) (.inl k)) := by
  obtain ⟨n,h⟩ := k.property
  let T := A.labeledOddChart P C.loop C.mono C.crosses C.regular C.bound C.matching k.val n h
  refine ⟨⟨T.patch,T.valid,?_,?_,?_⟩⟩
  · intro e he
    obtain ⟨j,rfl⟩ := he
    obtain ⟨v,home,hit,part,cross⟩ := T.owned j
    exact ⟨v,A.tag_odd side P.first k home,hit,part,cross⟩
  · intro e impossible
    exact impossible.elim
  · intro f _ done
    refine ⟨⟨_,_,_,T.place A.patchRegion (.inl (.inl k)) (fun v => A.patchRegion_eq v _),?_⟩⟩
    exact local_odd T.positive T.low T.upper f done

end Kostochka.FiveRegular.Restoration.Atlas

end

section 

namespace Kostochka.FiveRegular.Restoration.Atlas
open Subdivision Auxiliary

variable {V E I X K : Type} {D : Family V E} (A : Atlas D I X K)
variable [Fintype V] [Fintype E] [Fintype I] [Fintype X] [Fintype K] [DecidableEq V]
variable {side : V → Bool}

theorem layers_of_charts (P : A.PartitionColors side) (C : A.ChartContext P)
    (closePath : ∀ i, A.shape i = .badPath → ∃ e, familyPair D e = s(A.vertex i 0,A.vertex i 3))
    (reg : ∀ v, coloredDegree D (fun _ => true) v true ≤ 5)
    (initial : ∀ b, Nonempty (ContractedPalette D side (A.finalPart P)
      (fun v => ∃ e, A.finalPart P e = .exceptional ∧ FamilyIncident D v e)
      b (folded (A.partner side P.first b))))
    (witnesses : ∀ k : A.SquareKey, Nonempty (A.SquareWitness P.exterior (A.pieceSide side k.val) k.val)) :
    Nonempty (GluedLayers D side (A.finalPart P)) := by
  apply A.complete_regions side P.exterior P.first P.second C.mono C.bound closePath reg initial
  · rintro (i|i)
    · exact A.odd_site P C i
    · exact A.bad_site P C i
  · intro k
    obtain ⟨W⟩ := witnesses k
    exact A.square_site P C k W

end Kostochka.FiveRegular.Restoration.Atlas

end

section

namespace MultFive.Multi.Rows
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
    (m : Multi V) (M : m.support.Subgraph) (s : V → Bool)

def joins (u v : V) : Prop :=
  M.Adj u v ∧ ∃ x y : V, [u,v,x,y].Nodup ∧
    s u = s v ∧ s u = s x ∧ s u = s y ∧ M.Adj x y ∧
    0 < (m.residual M).count v x ∧ 0 < (m.residual M).count u y ∧
    (m.residual M).support.Reachable u x

omit [Fintype V] [DecidableEq V] in
private theorem joins_swap {u v : V} (h : joins m M s u v) : joins m M s v u := by
  obtain ⟨uv,x,y,nd,a,b,c,xy,vx,uy,reach⟩ := h
  refine ⟨uv.symm,y,x,?_,a.symm,a.symm.trans c,a.symm.trans b,xy.symm,uy,vx,?_⟩
  · simp_all [List.nodup_cons,ne_comm]
  · exact (show (m.residual M).support.Adj v x from vx).reachable.trans
      (reach.symm.trans (show (m.residual M).support.Adj u y from uy).reachable)

noncomputable def joined : Multi V := by
  classical
  exact {
    count := fun u v => if s u = s v then (m.residual M).count u v + if joins m M s u v then 1 else 0 else 0
    symm := fun u v => by
      rw [(m.residual M).symm u v]
      simp only [propext (show joins m M s u v ↔ joins m M s v u from ⟨joins_swap m M s,joins_swap m M s⟩)]
      by_cases e : s u = s v
      · rw [if_pos e,if_pos e.symm]
      · rw [if_neg e,if_neg (Ne.symm e)]
    loopless := fun u => by
      have na : ¬joins m M s u u := fun h => (m.support.loopless.irrefl u) (M.adj_sub h.1)
      simp [na,(m.residual M).loopless] }

theorem degree_bound (bound : ∀ v, m.insideDegree s v ≤ 2) (u : V) : (joined m M s).degree u ≤ 2 := by
  classical
  apply le_trans _ (bound u)
  apply sum_le_sum
  intro v _
  change (if s u = s v then (m.residual M).count u v + (if joins m M s u v then 1 else 0) else 0)
    ≤ (if s v = s u then m.count u v else 0)
  by_cases h : s u = s v
  · rw [if_pos h,if_pos h.symm]
    by_cases yes : joins m M s u v
    · have hp : 0 < m.count u v := M.adj_sub yes.1
      simp [residual,yes,yes.1]; omega
    · simp [yes,residual]
  · simp [h,Ne.symm h]

end MultFive.Multi.Rows
end

section

namespace MultFive.Multi.Rows
open SimpleGraph Finset
variable {V : Type*} [DecidableEq V]

def neighbors (l : List V) (circle : Bool) (x y : V) : Prop :=
  ∃ i : Fin l.length, (circle = true ∨ i.val + 1 < l.length) ∧
    s(x,y) = s(l[i.val],l[(i.val + 1) % l.length]'(Nat.mod_lt _ (Fin.pos i)))

noncomputable def weight (l : List V) (circle : Bool) (x y : V) : ℕ := by
  classical
  exact if neighbors l circle x y then (if circle = true ∧ l.length = 2 then 2 else 1) else 0

end MultFive.Multi.Rows
end

section

namespace MultFive.Multi.Rows
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
   (m : Multi V) (M : m.support.Subgraph) (s : V → Bool)

theorem only_two (g : Multi V) (u a b : V) (bound : g.degree u ≤ 2)
    (distinct : a ≠ b) (ha : 0 < g.count u a) (hb : 0 < g.count u b)
    {v} (hv : 0 < g.count u v) : v = a ∨ v = b := by
  classical
  by_contra! hn
  have L := sum_le_sum_of_subset (f := g.count u) (subset_univ ({a,b,v} : Finset V))
  change ∑ z ∈ ({a,b,v} : Finset V), g.count u z ≤ g.degree u at L
  simp [distinct,Ne.symm hn.1,Ne.symm hn.2] at L
  omega

end MultFive.Multi.Rows
end

section

namespace MultFive.Multi.Rows
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
   (m : Multi V) (M : m.support.Subgraph) (s : V → Bool)

theorem one_on_rim (u v a : V) (bound : m.insideDegree s u ≤ 2)
    (mono : s u = s v) (otherSide : s u = s a) (ne : v ≠ a)
    (p : 0 < m.count u v) (q : 0 < m.count u a) : m.count u v = 1 := by
  let g := m.monoMulti s
  have h := sum_le_sum_of_subset (f := g.count u) (subset_univ ({v,a} : Finset V))
  have hu : g.degree u ≤ 2 := by simpa [g,monoMulti_degree] using bound
  change ∑ z ∈ ({v,a} : Finset V), g.count u z ≤ g.degree u at h
  have e1 : g.count u v = m.count u v := if_pos mono
  have e2 : g.count u a = m.count u a := if_pos otherSide
  rw [sum_pair ne,e1,e2] at h
  omega

theorem joined_quad (hm : M.IsPerfectMatching) (bound : ∀ v, m.insideDegree s v ≤ 2)
    {l : List V} {u v : V} (_ : u ∈ l)
    (component : ∀ y,y ∈ l ↔ (joined m M s).support.Reachable u y) (j : joins m M s u v) :
    ∃ q : TwoBadQuad m M s, q.verts = l.toFinset := by
  classical
  have original := j
  obtain ⟨uv,x,y,nd,ab,ac,ad,xy,vx,uy,rx⟩ := j
  have distinct := nd
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,List.nodup_nil,and_true] at distinct
  have unique {a b c : V} (h : M.Adj a b) (k : M.Adj a c) : b = c := by
    obtain ⟨z,_,hz⟩ := hm.1 (hm.2 a)
    exact (hz _ h).trans (hz _ k).symm
  have noUY : ¬M.Adj u y := fun h => distinct.2.1.2 (unique uv h)
  have noXV : ¬M.Adj x v := fun h => (Ne.symm distinct.2.1.2) (unique xy h)
  have noVX : ¬M.Adj v x := fun h => noXV h.symm
  have posuy : 0 < m.count u y := by simpa [residual,noUY] using uy
  have posvx : 0 < m.count v x := by simpa [residual,noVX] using vx
  have count14 := one_on_rim m s u v y (bound u) ab ad distinct.2.1.2 (M.adj_sub uv) posuy
  have count23 := one_on_rim m s x y v (bound x) (ac.symm.trans ad) (ac.symm.trans ab)
    (Ne.symm distinct.2.1.2) (M.adj_sub xy) (m.symm x v ▸ posvx)
  have count12 := one_on_rim m s u y v (bound u) ad ab (Ne.symm distinct.2.1.2) posuy (M.adj_sub uv)
  have count34 := one_on_rim m s v x u (bound v) (ab.symm.trans ac) ab.symm
    (Ne.symm distinct.1.2.1) posvx (M.adj_sub uv.symm)
  let q : TwoBadQuad m M s :=
    ⟨s u,u,y,x,v,by simp_all [List.nodup_cons,ne_comm],rfl,ad.symm,ac.symm,ab.symm,uv,xy.symm,
      count14,(m.symm y x).trans count23,noUY,noXV,by simpa [residual,noUY] using count12,
      by simpa [residual,noXV,m.symm x v] using count34,rx⟩
  let k := joined m M s
  have kept {a b : V} (same : s a = s b) (edge : 0 < (m.residual M).count a b ∨ joins m M s a b) :
      k.support.Adj a b := by
    change 0 < (if s a = s b then _ + (if joins m M s a b then 1 else 0) else 0)
    rw [if_pos same]
    rcases edge with h | h
    · omega
    · simp [h]
  have rotated : joins m M s x y := by
    refine ⟨xy,u,v,?_,ac.symm.trans ad,ac.symm,ac.symm.trans ab,uv,?_,?_,rx.symm⟩
    · simpa [List.nodup_cons,ne_comm,and_comm,and_left_comm,and_assoc] using nd
    · rwa [(m.residual M).symm]
    · rwa [(m.residual M).symm]
  have uv' := kept ab (.inr original)
  have vx' := kept (ab.symm.trans ac) (.inl vx)
  have xy' := kept (ac.symm.trans ad) (.inr rotated)
  have uy' := kept ad (.inl uy)
  have near {a b c z : V} (ne : b ≠ c) (left : k.support.Adj a b) (right : k.support.Adj a c)
      (e : k.support.Adj a z) : z = b ∨ z = c :=
    only_two k a b c (degree_bound m M s bound a) ne left right e
  have closed {a z : V} (ha : a ∈ q.verts) (e : k.support.Adj a z) : z ∈ q.verts := by
    change a ∈ ({u,y,x,v} : Finset V) at ha
    change z ∈ ({u,y,x,v} : Finset V)
    simp only [mem_insert,mem_singleton] at ha ⊢
    rcases ha with rfl | rfl | rfl | rfl
    · have := near distinct.2.1.2 uv' uy' e; grind
    · have := near distinct.1.2.1 uy'.symm xy'.symm e; grind
    · have := near distinct.2.1.2 vx'.symm xy' e; grind
    · have := near distinct.1.2.1 uv'.symm vx' e; grind
  refine ⟨q,?_⟩
  ext w
  rw [List.mem_toFinset,component]
  constructor
  · intro h
    change w ∈ ({u,y,x,v} : Finset V) at h
    simp only [mem_insert,mem_singleton] at h
    rcases h with rfl|rfl|rfl|rfl
    exacts [Reachable.refl _,uy'.reachable,uv'.reachable.trans vx'.reachable,uv'.reachable]
  · intro h
    have tr := (reachable_iff_reflTransGen _ _).mp h
    clear h
    induction tr with
    | refl => change u ∈ ({u,y,x,v} : Finset V); simp
    | tail _ e ih => exact closed ih e
end MultFive.Multi.Rows
end

section

namespace MultFive.Multi.Rows
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (m : Multi V) (M : m.support.Subgraph) (s : V → Bool)

def Decoded (l : List V) : Prop :=
  ∃ P : ResidualPiece m M s, P.verts = l.toFinset ∧
    (∀ u ∈ l, ∀ w, P.edgeMult u w = ((m.residual M).monoMulti s).count u w) ∧
    (∀ v ∈ l, (m.residual M).insideDegree s v = P.expectedInsideDeg v) ∧ P.isMarked = false

private theorem open_weight (l : List V) (u v : V) : weight l false u v = if listPathAdj l u v then 1 else 0 := by
  classical
  have eq : neighbors l false u v ↔ listPathAdj l u v := by
    constructor
    · rintro ⟨i,h,eq⟩
      have k := h.resolve_left (by decide)
      exact ⟨i.val,k,by simpa [Nat.mod_eq_of_lt k] using eq⟩
    · rintro ⟨i,h,eq⟩
      exact ⟨⟨i,by omega⟩,Or.inr h,by simpa [Nat.mod_eq_of_lt h] using eq⟩
  simp [weight,eq]

private theorem cycle_weight (l : List V) (hl : l.length ≠ 2) (u v : V) :
    weight l true u v = if listCycleAdj l u v then 1 else 0 := by
  classical
  simp [weight,neighbors,listCycleAdj,hl]

private theorem row_side (l : List V) (c : Bool) (ne : l ≠ [])
    (cov : ∀ x ∈ l, ∀ y, (joined m M s).count x y = weight l c x y) :
    ∃ b, ∀ v ∈ l, s v = b := by
  have pos := List.length_pos_iff.mpr ne
  refine ⟨s l[0],?_⟩
  intro v hv
  obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hv
  induction i with
  | zero => rfl
  | succ i ih =>
    have h : neighbors l c l[i] l[i+1] :=
      ⟨⟨i,by omega⟩,Or.inr hi,by simp [Nat.mod_eq_of_lt hi]⟩
    have adj : (joined m M s).support.Adj l[i] l[i+1] := by
      change 0 < _
      rw [cov _ (List.getElem_mem _) _,weight,if_pos h]
      split <;> decide
    have sideEq : s l[i] = s l[i+1] := by
      by_contra h
      change 0 < (if s l[i] = s l[i+1] then _ else 0) at adj
      simp [h] at adj
    exact sideEq.symm.trans (ih (by omega) (List.getElem_mem _))

private theorem edge_nomatch (bound : ∀ v, m.insideDegree s v ≤ 2) {u : V}
    (sat : (m.residual M).insideDegree s u = 2) {v : V} (same : s u = s v) : ¬ M.Adj u v := by
  intro hit
  exact (matching_crossing_of_residual_insideDeg_two m M s bound sat hit) same.symm

private theorem residual_row (l : List V) (c : Bool)
    (cov : ∀ x ∈ l, ∀ y, (joined m M s).count x y = weight l c x y)
    (no : ∀ u ∈ l, ∀ v, ¬joins m M s u v) (x : V) (hx : x ∈ l) (y : V) :
    ((m.residual M).monoMulti s).count x y = weight l c x y := by
  rw [← cov x hx y]
  simp [monoMulti,joined,no x hx y]

private theorem decode_cycle (l : List V) (nd : l.Nodup) (len : 3 ≤ l.length)
    (bound : ∀ v, m.insideDegree s v ≤ 2) (b : Bool) (same : ∀ v ∈ l, s v = b)
    (cov : ∀ u ∈ l, ∀ w, ((m.residual M).monoMulti s).count u w = weight l true u w) :
    Decoded m M s l := by
  classical
  have edges (u) (hu : u ∈ l) (w) := (cov u hu w).trans (cycle_weight l (by omega) u w)
  have sat (u) (hu : u ∈ l) : (m.residual M).insideDegree s u = 2 := by
    obtain ⟨k,hk,rfl⟩ := List.getElem_of_mem hu
    rw [← monoMulti_degree]; exact degree_eq_two_of_listCycleAdj_count nd len edges k hk
  have avoid (i : Fin l.length) : ¬M.Adj l[i.val] (l[(i.val+1)%l.length]'(Nat.mod_lt _ (Fin.pos i))) :=
    edge_nomatch m M s bound (sat _ (List.getElem_mem _)) ((same _ (List.getElem_mem _)).trans (same _ (List.getElem_mem _)).symm)
  have rim (i : Fin l.length) : (m.residual M).count l[i.val] (l[(i.val+1)%l.length]'(Nat.mod_lt _ (Fin.pos i))) = 1 := by
    have e : listCycleAdj l l[i.val] (l[(i.val+1)%l.length]'(Nat.mod_lt _ (Fin.pos i))) := ⟨i,rfl⟩
    simpa [monoMulti_count,same _ (List.getElem_mem _),e] using edges _ (List.getElem_mem i.isLt) (l[(i.val+1)%l.length]'(Nat.mod_lt _ (Fin.pos i)))
  by_cases odd : Odd l.length
  · obtain ⟨t,ht⟩ := odd
    let c : MultiBadOddCycle m M s := ⟨b,t,by omega,l,nd,by omega,same,avoid,rim⟩
    exact ⟨.badOddCycle c false,rfl,fun u hu w => (edges u hu w).symm,sat,rfl⟩
  · by_cases four : l.length = 4
    · obtain ⟨a,c,d,e,rfl⟩ : ∃ a c d e : V, l = [a,c,d,e] := ⟨_,_,_,_,list_eq_four_of_length four⟩
      let q : ZeroBadSquare m M s := ⟨b,a,c,d,e,nd,same a (by simp),same c (by simp),
        same d (by simp),same e (by simp),avoid 0,avoid 1,avoid 2,(by simpa using avoid ⟨3, by simp⟩),rim 0,rim 1,rim 2,(by simpa using rim ⟨3, by simp⟩)⟩
      refine ⟨.zeroBadSquare q,rfl,?_,sat,rfl⟩
      intro u hu w
      rw [edges u hu w,if_congr (listCycleAdj_four a c d e u w) rfl rfl]
      rfl
    · obtain ⟨t,ht⟩ := Nat.not_odd_iff_even.mp odd
      let c : LongEvenCycle m M s := ⟨b,t,by omega,l,nd,by omega,same,avoid,rim⟩
      exact ⟨.evenCycle c,rfl,fun u hu w => (edges u hu w).symm,sat,rfl⟩

private theorem path_degree (l : List V) (nd : l.Nodup) (len : 2 ≤ l.length)
    (edges : ∀ u ∈ l, ∀ w, ((m.residual M).monoMulti s).count u w = if listPathAdj l u w then 1 else 0)
    (v) (hv : v ∈ l) : (m.residual M).insideDegree s v =
      if v = l[0] ∨ v = l[l.length - 1] then 1 else 2 := by
  classical
  obtain ⟨k,hk,rfl⟩ := List.getElem_of_mem hv
  rw [← monoMulti_degree,degree_eq_of_listPathAdj_count nd edges k hk]
  by_cases h0 : k = 0
  · subst k; simp [show 1 < l.length by omega]
  · by_cases last : k = l.length - 1
    · subst k; simp [show 0 < l.length - 1 by omega,show ¬ l.length - 1 + 1 < l.length by omega]
    · have a : l[k] ≠ l[0] := fun e => h0 (getElem_inj nd e)
      have b : l[k] ≠ l[l.length-1] := fun e => last (getElem_inj nd e)
      simp [a,b,show 0 < k by omega,show k+1 < l.length by omega]

private theorem decode_closed_path (a b c d : V) (side : Bool) (sa : s a = side) (sb : s b = side)
    (sc : s c = side) (sd : s d = side) (nd : [a,b,c,d].Nodup) (close : M.Adj a d)
    (bound : ∀ v, m.insideDegree s v ≤ 2)
    (edges : ∀ u ∈ [a,b,c,d], ∀ w, ((m.residual M).monoMulti s).count u w = if listPathAdj [a,b,c,d] u w then 1 else 0) :
    Decoded m M s [a,b,c,d] := by
  classical
  have listAdj (u w : V) : listPathAdj [a,b,c,d] u w ↔
      s(u,w) = s(a,b) ∨ s(u,w) = s(b,c) ∨ s(u,w) = s(c,d) := by
    simp [listPathAdj_cons_cons,listPathAdj_singleton]
  obtain ⟨ab,ac,ad,bc,bd,cd⟩ := nodup_four_ne nd
  have res (u : V) (hu : u ∈ [a,b,c,d]) (w : V) (hs : s u = s w) := by
    simpa only [monoMulti_count,if_pos hs,List.mem_cons,List.not_mem_nil,or_false] using (edges u hu w).trans (if_congr (listAdj u w) rfl rfl)
  have degree := path_degree m M s [a,b,c,d] nd (by simp) edges
  have middleB : (m.residual M).insideDegree s b = 2 := by simpa [ab.symm,bd] using degree b (by simp)
  have middleC : (m.residual M).insideDegree s c = 2 := by simpa [ac.symm,cd] using degree c (by simp)
  have am : m.count a d = 1 := by
    rw [m.residual_count_add_matching M a d,if_pos close,res a (by simp) d (sa.trans sd.symm)]
    simp [Sym2.eq_iff,ab,ab.symm,ac,ac.symm,ad,ad.symm,bc,bc.symm,bd,bd.symm,cd,cd.symm]
  let q : MultiBadPath m M s := ⟨side,a,b,c,d,nd,sa,sb,sc,sd,close,am,
    (fun e => edge_nomatch m M s bound middleB (sb.trans sa.symm) e.symm),
    edge_nomatch m M s bound middleB (sb.trans sc.symm),edge_nomatch m M s bound middleC (sc.trans sd.symm),
    by simp [res a (by simp) b (sa.trans sb.symm)], by simp [res b (by simp) c (sb.trans sc.symm)],
    by simp [res c (by simp) d (sc.trans sd.symm)]⟩
  refine ⟨.badPath q false,rfl,?_,degree,rfl⟩
  intro u hu w
  rw [edges u hu w,if_congr (listAdj u w) rfl rfl]
  rfl

private theorem decode_path (l : List V) (nd : l.Nodup) (ne : l ≠ []) (bound : ∀ v, m.insideDegree s v ≤ 2)
    (b : Bool) (same : ∀ v ∈ l, s v = b) (no : ∀ u ∈ l, ∀ w, ¬ joins m M s u w)
    (cov : ∀ u ∈ l, ∀ w, ((m.residual M).monoMulti s).count u w = weight l false u w) : Decoded m M s l := by
  classical
  have edges (u) (hu : u ∈ l) (w) := (cov u hu w).trans (open_weight l u w)
  by_cases len : 2 ≤ l.length
  · by_cases bad : ∃ h : l.length = 4, M.Adj (l[0]'(by omega)) (l[3]'(by omega))
    · obtain ⟨h,adj⟩ := bad
      have eq := list_eq_four_of_length h
      let a := l[0]'(by omega); let c := l[1]'(by omega); let d := l[2]'(by omega); let e := l[3]'(by omega)
      change l = [a,c,d,e] at eq
      rw [eq]; apply decode_closed_path m M s a c d e b (same a (List.getElem_mem _)) (same c (List.getElem_mem _))
        (same d (List.getElem_mem _)) (same e (List.getElem_mem _)) (eq ▸ nd) adj bound (eq ▸ edges)
    · have res (i : ℕ) (hi : i+1 < l.length) : (m.residual M).count l[i] l[i+1] = 1 := by
        have a : listPathAdj l l[i] l[i+1] := ⟨i,hi,rfl⟩
        have z := edges l[i] (List.getElem_mem _) l[i+1]
        simpa [monoMulti_count,same _ (List.getElem_mem _),a] using z
      let p : OrdinaryPath m M s := {
        b := b
        vertsList := l
        nodup := nd
        hlen := len
        side_mem := same
        res_count_edge := res
        not_bad_path := fun h e => bad ⟨h,e⟩
        not_same_comp_two_bad := by
          intro ht x y hn sx sy ml mr xy reach
          have hi : 1 < l.length := by omega
          apply no l[0] (List.getElem_mem _) y
          refine ⟨ml,x,l[1],?_,(same _ (List.getElem_mem _)).trans sy.symm,(same _ (List.getElem_mem _)).trans sx.symm,
            (same _ (List.getElem_mem _)).trans (same _ (List.getElem_mem _)).symm,mr.symm,?_,?_,reach⟩
          · simpa [List.nodup_cons,ne_comm,and_comm,and_left_comm,and_assoc] using hn
          · rwa [(m.residual M).symm]
          · rw [res 0 hi]; decide }
      refine ⟨.ordinaryPath p,rfl,fun u hu w => (edges u hu w).symm,?_,rfl⟩
      exact path_degree m M s l nd len edges
  · obtain ⟨x,rfl⟩ := List.length_eq_one_iff.mp (show l.length = 1 by have := List.length_pos_iff.mpr ne; omega)
    have ed (u) (hu : u ∈ [x]) (w) : ((m.residual M).monoMulti s).count u w = 0 := by simpa [listPathAdj_singleton] using edges u hu w
    have z : (m.residual M).insideDegree s x = 0 := by
      rw [← monoMulti_degree,degree]; exact Finset.sum_eq_zero fun w _ => ed x (by simp) w
    refine ⟨.isolated x z,rfl,fun u hu w => (ed u hu w).symm,?_,rfl⟩
    intro v hv; obtain rfl := List.mem_singleton.mp hv; exact z

private theorem single_neighbor (f : V → ℕ) (v : V) (one : f v = 1) (bounded : ∑ w, f w ≤ 1) (w : V) :
    f w = if w = v then 1 else 0 := by
  classical
  by_cases eq : w = v
  · simpa [eq] using one
  · rw [if_neg eq]
    by_contra! pos
    have le (x : V) : (if x = v then 1 else 0) ≤ f x := by split <;> grind
    have lt := Finset.sum_lt_sum (s := (univ : Finset V)) (fun x _ => le x)
      ⟨w,mem_univ _,by simp [eq]; omega⟩
    simp at lt
    omega

private theorem one_at (bound : ∀ v, m.insideDegree s v ≤ 2) {u v z : V} (hit : M.Adj u v)
    (uv : s u = s v) (uz : s u = s z) (edge : (m.residual M).count u z = 1) :
    (m.residual M).insideDegree s u = 1 ∧
    ∀ w, ((m.residual M).monoMulti s).count u w = if w = z then 1 else 0 := by
  classical
  let r := (m.residual M).monoMulti s
  have one : r.count u z = 1 := by simp [r,monoMulti_count,uz,edge]
  have le := (insideDegree_residual_le m M s u).trans (bound u)
  have lt : (m.residual M).insideDegree s u ≠ 2 := fun eq => edge_nomatch m M s bound eq uv hit
  have bd : ∑ w, r.count u w ≤ 1 := by change r.degree u ≤ 1; rw [show r = (m.residual M).monoMulti s from rfl,monoMulti_degree]; omega
  have formula := single_neighbor (r.count u) z one bd
  exact ⟨by rw [← monoMulti_degree]; change (∑ w,r.count u w) = 1; simp [formula],formula⟩

private theorem alternate_at (bound : ∀ v, m.insideDegree s v ≤ 2) (l : List V)
    (q : TwoBadQuad m M s) (verts : q.verts = l.toFinset) :
    let P := ResidualPiece.twoBadQuad q
    P.verts = l.toFinset ∧
    (∀ u ∈ l, ∀ w, P.edgeMult u w = ((m.residual M).monoMulti s).count u w) ∧
    (∀ v ∈ l, (m.residual M).insideDegree s v = P.expectedInsideDeg v) ∧ P.isMarked = false := by
  classical
  have a := one_at m M s bound q.match14 (q.side_v1.trans q.side_v4.symm) (q.side_v1.trans q.side_v2.symm) q.res_count12
  have b := one_at m M s bound q.match23 (q.side_v2.trans q.side_v3.symm) (q.side_v2.trans q.side_v1.symm)
    (by rw [(m.residual M).symm]; exact q.res_count12)
  have c := one_at m M s bound q.match23.symm (q.side_v3.trans q.side_v2.symm) (q.side_v3.trans q.side_v4.symm) q.res_count34
  have d := one_at m M s bound q.match14.symm (q.side_v4.trans q.side_v1.symm) (q.side_v4.trans q.side_v3.symm)
    (by rw [(m.residual M).symm]; exact q.res_count34)
  obtain ⟨ab,ac,ad,bc,bd,cd⟩ := nodup_four_ne q.nodup
  have corners (u : V) (hu : u ∈ l) : u = q.v1 ∨ u = q.v2 ∨ u = q.v3 ∨ u = q.v4 := by
    have mem := verts.symm ▸ List.mem_toFinset.mpr hu
    simpa only [TwoBadQuad.verts,mem_insert,mem_singleton] using mem
  refine ⟨?_,?_,?_,rfl⟩
  · simpa [ResidualPiece.verts,ResidualPiece.vertsList,TwoBadQuad.vertsList,TwoBadQuad.verts] using verts
  · intro u hu w
    change (if s(u,w) = s(q.v1,q.v2) then 1 else 0) + (if s(u,w) = s(q.v3,q.v4) then 1 else 0) = _
    rcases corners u hu with rfl | rfl | rfl | rfl
    all_goals first | rw [a.2] | rw [b.2] | rw [c.2] | rw [d.2]
    all_goals simp only [Sym2.eq_iff,ab,ac,ad,bc,bd,cd,ab.symm,ac.symm,ad.symm,bc.symm,bd.symm,cd.symm,
      and_false,false_and,or_false,false_or,true_and,eq_self,ite_false,Nat.add_zero,Nat.zero_add]
  · intro u hu
    rcases corners u hu with rfl | rfl | rfl | rfl
    exacts [a.1,b.1,c.1,d.1]

private theorem decode_double (a b : V) (ab : a ≠ b) (side : Bool) (sa : s a = side) (sb : s b = side)
    (bound : ∀ v, m.insideDegree s v ≤ 2)
    (cov : ∀ u ∈ [a,b], ∀ w, ((m.residual M).monoMulti s).count u w = weight [a,b] true u w) :
    Decoded m M s [a,b] := by
  classical
  have pair (u w : V) : neighbors [a,b] true u w ↔ s(u,w) = s(a,b) := by
    constructor
    · rintro ⟨i,h,e⟩; have hi : i.val < 2 := i.isLt
      rcases (show i.val = 0 ∨ i.val = 1 by omega) with k|k <;> simpa [k,Sym2.eq_swap] using e
    · intro e; exact ⟨0,by simp,by simpa using e⟩
  have ed (u) (hu : u ∈ [a,b]) (w) : ((m.residual M).monoMulti s).count u w = if s(u,w) = s(a,b) then 2 else 0 := by
    simpa [weight,pair] using cov u hu w
  have deg (u) (hu : u ∈ [a,b]) : (m.residual M).insideDegree s u = 2 := by
    rw [← monoMulti_degree,degree]
    rw [Finset.sum_congr rfl fun w _ => ed u hu w]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl|rfl <;> simp [Sym2.eq_iff,ab,ab.symm]
  let d : DoubledEdge m M s := ⟨side,a,b,ab,sa,sb,edge_nomatch m M s bound (deg a (by simp)) (sa.trans sb.symm),
    by simpa [monoMulti_count,sa,sb] using ed a (by simp) b⟩
  exact ⟨.doubledEdge d,rfl,fun u hu w => (ed u hu w).symm,deg,rfl⟩

theorem decode_unjoined (bound : ∀ v, m.insideDegree s v ≤ 2)
    (l : List V) (c : Bool) (nd : l.Nodup) (ne : l ≠ [])
    (cov : ∀ x ∈ l, ∀ y, (joined m M s).count x y = weight l c x y)
    (has : ∀ u ∈ l, ∀ v, ¬joins m M s u v) : Decoded m M s l := by
  classical
  obtain ⟨side,same⟩ := row_side m M s l c ne cov
  have ed := residual_row m M s l c cov has
  cases c with
  | false => exact decode_path m M s l nd ne bound side same has ed
  | true =>
    by_cases long : 3 ≤ l.length
    · exact decode_cycle m M s l nd long bound side same ed
    · cases l with
      | nil => exact False.elim (ne rfl)
      | cons a t => cases t with
        | nil =>
          have h := ed a (by simp) a
          have loop : neighbors [a] true a a := ⟨0,by simp,by simp⟩
          simp [weight,loop,monoMulti_count,(m.residual M).loopless] at h
        | cons b t =>
          have sz : t.length = 0 := by change ¬ 3 ≤ (t.length + 1) + 1 at long; omega
          have nil := List.eq_nil_of_length_eq_zero sz
          subst t
          exact decode_double m M s a b (by simpa using nd) side (same _ (by simp)) (same _ (by simp)) bound ed

end MultFive.Multi.Rows
end

section

namespace MultFive.Multi.Rows
open SimpleGraph
variable {V : Type*} [DecidableEq V]

theorem component_of_weight (k : Multi V) {l : List V} {c : Bool}
    (cov : ∀ a ∈ l, ∀ b, k.count a b = weight l c a b) {u : V} (hu : u ∈ l) (y : V) :
    y ∈ l ↔ k.support.Reachable u y := by
  classical
  have ne : 0 < l.length := List.length_pos_of_mem hu
  have step (i : ℕ) (hi : i+1 < l.length) : k.support.Adj l[i] l[i+1] := by
    have hits : neighbors l c l[i] l[i+1] := ⟨⟨i,by omega⟩,Or.inr hi,by simp [Nat.mod_eq_of_lt hi]⟩
    change 0 < k.count _ _
    rw [cov _ (List.getElem_mem _) _,weight,if_pos hits]
    split <;> decide
  have path (i : ℕ) (hi : i < l.length) : k.support.Reachable l[0] l[i] := by
    induction i with
    | zero => exact Reachable.refl _
    | succ j ih => exact (ih (by omega)).trans (step j hi).reachable
  constructor
  · intro hy
    obtain ⟨i,hi,rfl⟩ := List.getElem_of_mem hu
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hy
    exact (path i hi).symm.trans (path j hj)
  · intro h
    have walk := (k.support.reachable_iff_reflTransGen _ _).mp h
    clear h
    induction walk with
    | refl => exact hu
    | @tail a b _ ab inside =>
      have pos : 0 < weight l c a b := (cov a inside b) ▸ (show 0 < k.count a b from ab)
      have hits : neighbors l c a b := by by_contra hn; simp [weight,hn] at pos
      obtain ⟨i,_,e⟩ := hits
      rcases Sym2.eq_iff.mp e with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> exact List.getElem_mem _

end MultFive.Multi.Rows
end

section

namespace MultFive.Multi.Rows
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem of_decoded_rows (m : Multi V) (M : m.support.Subgraph) (hm : M.IsPerfectMatching)
    (side : V → Bool) (h_in : ∀ v, m.insideDegree side v ≤ 2)
    (rows : List (List V × Bool)) (apart : (rows.map (fun p => p.1.toFinset)).Pairwise Disjoint)
    (cover : ∀ v, ∃ p ∈ rows, v ∈ p.1)
    (decode : ∀ p ∈ rows, ∃ c : ResidualPiece m M side, c.verts = p.1.toFinset ∧
      (∀ u ∈ p.1, ∀ w, c.edgeMult u w = ((m.residual M).monoMulti side).count u w) ∧
      (∀ v ∈ p.1, (m.residual M).insideDegree side v = c.expectedInsideDeg v) ∧ c.isMarked = false ∧
      (∀ u ∈ p.1, ∀ v, joins m M side u v → ∃ q, c = .twoBadQuad q)) :
    Nonempty (PieceDecomposition m M side) := by
  classical
  let h := m.residual M
  let pick (z : {p // p ∈ rows}) := (decode z.val z.property).choose
  have spec (z : {p // p ∈ rows}) := (decode z.val z.property).choose_spec
  let raw := rows.attach.map pick
  have hraw_disj : (raw.map (·.verts)).Pairwise Disjoint := by
    have eq : raw.map (·.verts) = rows.map (fun p => p.1.toFinset) := by
      rw [show raw.map (·.verts) = rows.attach.map (fun z => z.val.1.toFinset) from by
        simp only [raw,List.map_map]; exact List.map_congr_left fun z _ => (spec z).1]
      exact List.attach_map_val (l := rows) (f := fun p : List V × Bool => p.1.toFinset)
    exact eq ▸ apart
  have hraw_cov : ∀ v : V, ∃ P ∈ raw, v ∈ P.verts := by
    intro v
    obtain ⟨p,hp,hv⟩ := cover v
    let z : {p // p ∈ rows} := ⟨p,hp⟩
    exact ⟨pick z,List.mem_map_of_mem (List.mem_attach rows z), (spec z).1 ▸ List.mem_toFinset.mpr hv⟩
  have hraw_edge : ∀ P ∈ raw, ∀ u ∈ P.verts, ∀ w : V,
      P.edgeMult u w = ((m.residual M).monoMulti side).count u w := by
    rintro P hp u hu w
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp hp
    exact (spec z).2.1 u (List.mem_toFinset.mp ((spec z).1 ▸ hu)) w
  have hraw_deg : ∀ P ∈ raw, ∀ v ∈ P.verts,
      (m.residual M).insideDegree side v = P.expectedInsideDeg v := by
    rintro P hp v hv
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp hp
    exact (spec z).2.2.1 v (List.mem_toFinset.mp ((spec z).1 ▸ hv))
  
  let badInComp (c : h.support.ConnectedComponent) : List (ResidualPiece m M side) :=
    raw.filter fun P => P.isBad && decide (h.support.connectedComponentMk P.rep = c)
  let chosenRep (c : h.support.ConnectedComponent) : Option V :=
    if Odd (badInComp c).length then (badInComp c).head?.map (·.rep) else none
  let markPiece (P : ResidualPiece m M side) : ResidualPiece m M side :=
    P.setMarked (decide (chosenRep (h.support.connectedComponentMk P.rep) = some P.rep))
  let pieces : List (ResidualPiece m M side) := raw.map markPiece
  have hpieces_disj : (pieces.map (·.verts)).Pairwise Disjoint := by
    have hmap : pieces.map (·.verts) = raw.map (·.verts) := by
      simp only [pieces, List.map_map]
      exact List.map_congr_left fun P _ => ResidualPiece.setMarked_verts P _
    rw [hmap]; exact hraw_disj
  have hpieces_cov : ∀ v : V, ∃ P ∈ pieces, v ∈ P.verts := by
    intro v
    obtain ⟨P, hP, hvP⟩ := hraw_cov v
    exact ⟨markPiece P, List.mem_map.mpr ⟨P, hP, rfl⟩, by simpa [markPiece] using hvP⟩
  have hpieces_edge : ∀ P ∈ pieces, ∀ u ∈ P.verts, ∀ w : V,
      P.edgeMult u w = ((m.residual M).monoMulti side).count u w := by
    intro P hP u hu w
    obtain ⟨P₀, hP₀, rfl⟩ := List.mem_map.mp hP
    simp only [markPiece, ResidualPiece.setMarked_verts, ResidualPiece.setMarked_edgeMult] at hu ⊢
    exact hraw_edge P₀ hP₀ u hu w
  have hpieces_deg : ∀ P ∈ pieces, ∀ v ∈ P.verts,
      (m.residual M).insideDegree side v = P.expectedInsideDeg v := by
    intro P hP v hv
    obtain ⟨P₀, hP₀, rfl⟩ := List.mem_map.mp hP
    simp only [markPiece, ResidualPiece.setMarked_verts, ResidualPiece.setMarked_expectedInsideDeg] at hv ⊢
    exact hraw_deg P₀ hP₀ v hv
  have hraw_rep_nodup : (raw.map (·.rep)).Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro ⟨i, hi⟩ ⟨j, hj⟩ heq
    simp only [List.length_map] at hi hj
    simp only [List.getElem_map] at heq
    apply Fin.ext
    by_contra hne
    have hdisj := disjoint_getElem_of_pairwise_map hraw_disj hi hj hne
    exact Finset.disjoint_left.mp hdisj (raw[i]'hi).rep_mem_verts (heq ▸ (raw[j]'hj).rep_mem_verts)
  have hcover_mult : ∀ u w : V,
      (pieces.map (fun P => P.edgeMult u w)).sum =
        if side u = side w then (m.residual M).count u w else 0 := by
    intro u w
    obtain ⟨P, hP, huP⟩ := hpieces_cov u
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hP
    rw [list_sum_eq_single_of_zero pieces (fun Q => Q.edgeMult u w) i hi]
    · exact hpieces_edge (pieces[i]'hi) (List.getElem_mem hi) u huP w
    · intro j hj hne
      have hdisj := disjoint_getElem_of_pairwise_map hpieces_disj hi hj hne.symm
      exact (pieces[j]'hj).edgeMult_eq_zero_of_not_mem (Finset.disjoint_left.mp hdisj huP)
  have hmarked_per_comp : ∀ (r : V) [DecidablePred ((m.residual M).support.Reachable r)],
      (pieces.filter (fun P =>
        P.isMarked && decide ((m.residual M).support.Reachable r P.rep))).length =
      if Odd (pieces.filter (fun P =>
        P.isBad && decide ((m.residual M).support.Reachable r P.rep))).length
      then 1 else 0 := by
    intro r _
    let c := h.support.connectedComponentMk r
    have hreach_eq : ∀ v : V, ((m.residual M).support.Reachable r v) ↔ h.support.connectedComponentMk v = c :=
      fun v => ⟨fun hr => (SimpleGraph.ConnectedComponent.sound hr).symm,
        fun heq => SimpleGraph.ConnectedComponent.exact heq.symm⟩
    have hbad_eq : (pieces.filter (fun P =>
        P.isBad && decide ((m.residual M).support.Reachable r P.rep))).length = (badInComp c).length := by
      simp only [pieces, List.filter_map, List.length_map, badInComp]
      congr 1
      refine List.filter_congr fun P _ => ?_
      simp only [Function.comp_apply, markPiece, ResidualPiece.setMarked_isBad,
        ResidualPiece.setMarked_rep]
      congr 1
      exact decide_eq_decide.mpr (hreach_eq P.rep)
    rw [hbad_eq]
    have hmk_eq : (pieces.filter (fun P =>
        P.isMarked && decide ((m.residual M).support.Reachable r P.rep))).length =
        ((badInComp c).filter (fun P => decide (chosenRep c = some P.rep))).length := by
      simp only [pieces, List.filter_map, List.length_map, badInComp, List.filter_filter]
      congr 1
      refine List.filter_congr fun P _ => ?_
      simp only [Function.comp_apply, markPiece, ResidualPiece.setMarked_isMarked,
        ResidualPiece.setMarked_rep]
      by_cases hreach : (m.residual M).support.Reachable r P.rep
      · have hc_eq : h.support.connectedComponentMk P.rep = c := (hreach_eq P.rep).mp hreach
        simp [hreach, hc_eq, Bool.and_comm]
      · have hc_ne : h.support.connectedComponentMk P.rep ≠ c :=
          fun e => hreach ((hreach_eq P.rep).mpr e)
        simp [hreach, hc_ne]
    rw [hmk_eq]
    by_cases hodd : Odd (badInComp c).length
    · rw [if_pos hodd]
      have hne : badInComp c ≠ [] := by intro hnil; rw [hnil] at hodd; simp at hodd
      cases hbc : badInComp c with
      | nil => exact absurd hbc hne
      | cons P₀ rest =>
        have hch : chosenRep c = some P₀.rep := by
          dsimp only [chosenRep]; rw [if_pos hodd, hbc]; rfl
        have hsub_nd : ((badInComp c).map (·.rep)).Nodup :=
          hraw_rep_nodup.sublist ((List.filter_sublist).map _)
        rw [hbc, List.map_cons, List.nodup_cons] at hsub_nd
        simp only [hch, List.filter_cons, decide_true, ↓reduceIte, List.length_cons]
        have hrest_nil : rest.filter (fun P => decide (some P₀.rep = some P.rep)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro P hP
          simp only [Option.some.injEq, decide_eq_true_eq]
          intro heq
          exact hsub_nd.1 (List.mem_map.mpr ⟨P, hP, heq.symm⟩)
        rw [hrest_nil]; rfl
    · rw [if_neg hodd]
      have hch : chosenRep c = none := by simp [chosenRep, hodd]
      simp [hch]
  refine Nonempty.intro ?_
  exact
    { pieces := pieces
      disjoint := hpieces_disj
      cover_verts := hpieces_cov
      cover_edgeMult := hcover_mult
      local_insideDeg := hpieces_deg
      marked_per_comp := hmarked_per_comp
      complete_twoBadQuad := by
        intro b a v c d distinct sa sv sc sd ad vc av cd reach
        have j : joins m M side a d := by
          refine ⟨ad,c,v,?_,sa.trans sd.symm,sa.trans sc.symm,sa.trans sv.symm,vc.symm,?_,av,reach⟩
          · simpa [List.nodup_cons,ne_comm,and_comm,and_left_comm,and_assoc] using distinct
          · rwa [(m.residual M).symm]
        obtain ⟨p,hp,ha⟩ := cover a
        let z : {p // p ∈ rows} := ⟨p,hp⟩
        obtain ⟨q,hq⟩ := (spec z).2.2.2.2 a ha d j
        change pick z = .twoBadQuad q at hq
        have found : (.twoBadQuad q : ResidualPiece m M side) ∈ pieces := by
          have mem : pick z ∈ raw := List.mem_map_of_mem (List.mem_attach rows z)
          have marked := List.mem_map_of_mem (f := markPiece) mem
          rwa [hq] at marked
        have mem : a ∈ (pick z).verts := (spec z).1 ▸ List.mem_toFinset.mpr ha
        exact ⟨q,found,hq ▸ mem⟩
      complete_badPath := complete_badPath_of_pieces m M hm side h_in pieces
        hpieces_cov hpieces_edge hpieces_deg
      complete_zeroBadSquare := complete_zeroBadSquare_of_pieces m M side h_in pieces
        hpieces_cov hpieces_edge hpieces_deg }

end MultFive.Multi.Rows
end

section

namespace MultFive.Multi.Rows
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/- Decode the components supplied by the row lemma. A retained matching edge singles out an
alternating square. The remaining components are classified by whether the row is open or
cyclic and by its length. -/
theorem of_flat_rows (m : Multi V) (M : m.support.Subgraph) (hm : M.IsPerfectMatching)
    (s : V → Bool) (bound : ∀ v, m.insideDegree s v ≤ 2)
    (rows : List (List V × Bool)) (apart : (rows.map (fun p => p.1.toFinset)).Pairwise Disjoint)
    (cover : ∀ v, ∃ p ∈ rows, v ∈ p.1)
    (shape : ∀ p ∈ rows,p.1.Nodup ∧ p.1 ≠ [] ∧ ∀ x ∈ p.1, ∀ y,
      (joined m M s).count x y = weight p.1 p.2 x y) : Nonempty (PieceDecomposition m M s) := by
  classical
  apply of_decoded_rows m M hm s bound rows apart cover
  intro p hp
  obtain ⟨nd,ne,cov⟩ := shape p hp
  by_cases anyJoin : ∃ u ∈ p.1, ∃ v, joins m M s u v
  · obtain ⟨u,hu,v,j⟩ := anyJoin
    obtain ⟨q,hq⟩ := joined_quad m M s hm bound hu (fun y => component_of_weight _ cov hu y) j
    obtain ⟨eq,edge,deg,mark⟩ := alternate_at m M s bound p.1 q hq
    exact ⟨.twoBadQuad q,eq,edge,deg,mark,fun _ _ _ _ => ⟨q,rfl⟩⟩
  · have absent (u) (hu : u ∈ p.1) (v) : ¬joins m M s u v := fun j => anyJoin ⟨u,hu,v,j⟩
    obtain ⟨P,eq,edge,deg,mark⟩ := decode_unjoined m M s bound p.1 p.2 nd ne cov absent
    exact ⟨P,eq,edge,deg,mark,fun u hu v j => (absent u hu v j).elim⟩

end MultFive.Multi.Rows
end

section
namespace Kostochka.FiveRegular
open SimpleGraph Four.PathCover

/- The palette lemma colors vertices of the first simple graph and edges of the second with
the same three colors. Its marked-incidence and square conditions are verified on the
folded factors. -/
def FactorPaint (U : Type) [Fintype U] : Prop :=
  ∀ (S F : SimpleGraph U) [DecidableRel S.Adj] [DecidableRel F.Adj],
    (∀ v, S.degree v ≤ 2) → (∀ v, F.degree v ≤ 2) → ∀ t : U → Bool,
    (∀ x y, F.Adj x y → t x = true → t y = true → S.Adj x y) →
    (∀ x y z, x ≠ z → F.Adj x y → F.Adj y z → ¬ (t x = true ∧ t y = true ∧ t z = true)) →
    NoOrdinarySquare S F t → sidePalette S F t

end Kostochka.FiveRegular
namespace Kostochka.FiveRegular

open Subdivision SimpleGraph Four.PathCover

section Basic
variable {V E : Type*}

private theorem marked_ends (T : Family V E) (mark : V → Bool) (e : E)
    {v w : V} (hn : v ≠ w) (hv : mark v = true) (hw : mark w = true)
    (iv : FamilyIncident T v e) (iw : FamilyIncident T w e) :
    mark (T.left e) = true ∧ mark (T.right e) = true := by
  rcases iv with h|h <;> rcases iw with k|k
  · exact (hn (h.trans k.symm)).elim
  · exact ⟨h ▸ hv,k ▸ hw⟩
  · exact ⟨k ▸ hw,h ▸ hv⟩
  · exact (hn (h.trans k.symm)).elim

private theorem equal_internal (T : Family V E) (mark : V → Bool)
    (intern : InternalMatching T mark) {v x y : V} (hn : v ≠ x) (hn' : v ≠ y)
    (hv : mark v = true) (hx : mark x = true) (hy : mark y = true)
    {e f : E} (iv : FamilyIncident T v e) (ix : FamilyIncident T x e)
    (jv : FamilyIncident T v f) (jy : FamilyIncident T y f) : e = f := by
  have h := marked_ends T mark e hn hv hx iv ix
  have k := marked_ends T mark f hn' hv hy jv jy
  exact intern v hv e f iv jv h.1 h.2 k.1 k.2

private theorem internal_neighbors (T : Family V E) (mark : V → Bool)
    (intern : InternalMatching T mark) (x y z : V) (hx : mark x = true)
    (hy : mark y = true) (hz : mark z = true) (hxy : (support T).Adj x y)
    (hyz : (support T).Adj y z) : x = z := by
  obtain ⟨e,he⟩ := hxy.symm.1
  obtain ⟨f,hf⟩ := hyz.1
  have inc (g : E) (v w : V) (h : familyPair T g = s(v,w)) :
      FamilyIncident T v g ∧ FamilyIncident T w g := by
    have eq : ∀ u, FamilyIncident T u g ↔ u ∈ s(v,w) :=
      fun u => (show FamilyIncident T u g ↔ u ∈ familyPair T g from Sym2.mem_iff.symm).trans
        (congrArg (u ∈ ·) h).to_iff
    exact ⟨(eq v).mpr (by simp),(eq w).mpr (by simp)⟩
  have i := inc _ _ _ he
  have j := inc _ _ _ hf
  have eq := equal_internal T mark intern hxy.ne.symm hyz.ne hy hx hz i.1 i.2 j.1 j.2
  have hit := Sym2.eq_iff.mp (he.symm.trans (eq ▸ hf))
  rcases hit with a|a
  · exact a.2
  · exact a.2.trans a.1

end Basic

variable {V E : Type} [Fintype V] [DecidableEq V]

theorem contracted_family_palette_from (paint : FactorPaint (Sym2 V)) (D : Family V E) (hl : Loopless D)
    (side : V → Bool) (part : E → EdgePart) (exc : V → Prop) (b : Bool) (p : V → V)
    (hi : Function.Involutive p) (fixed : ∀ v, ordinaryAt side exc b v = true → p v = v)
    (bound : ∀ v, insideDegree (support D) side v ≤ 2)
    (two : AtMostTwo (factorFamily D part b))
    (internal : InternalMatching (factorFamily D part b) (ordinaryAt side exc b))
    (single : ∀ v, p v ≠ v → ∀ e f, FamilyIncident (factorFamily D part b) v e →
      FamilyIncident (factorFamily D part b) v f → e = f)
    (apart : ∀ e, (factorFamily D part b).left e ≠ p ((factorFamily D part b).right e))
    (noSquare : NoOrdinarySquare (foldedSide (ordinaryGraph (support D) (ordinaryAt side exc b)))
        (support (foldFamily (factorFamily D part b) p)) (ordinaryMark (ordinaryAt side exc b))) :
    Nonempty (ContractedPalette D side part exc b (folded p)) := by
  classical
  let T := factorFamily D part b
  let mark := ordinaryAt side exc b
  let S := ordinaryGraph (support D) mark
  have two' := atMostTwo_foldFamily T hi two single
  have sd := ordinary_degree (support D) side mark b (fun x h => ((ordinaryAt_iff _ _ _ _).mp h).1) bound
  have covers (x y) (h : (support T).Adj x y) (hx : mark x = true) (hy : mark y = true) :
      S.Adj x y := ⟨factor_support_le D part b h,hx,hy⟩
  have palette := paint (foldedSide S) (support (foldFamily T p))
    (degree_foldedSide S sd) (degree_support_le_two _ two') (ordinaryMark mark)
    (fold_inside T p S mark covers) (fold_no_three T p mark (internal_neighbors T mark internal)) noSquare
  apply contractedPalette_of_sidePalette D (folded p) side part exc b (foldedSide S) (ordinaryMark mark)
  · intro e l r el er
    have ml : mark (D.left e) = true := (ordinaryAt_iff _ _ _ _).mpr ⟨l,el⟩
    have mr : mark (D.right e) = true := (ordinaryAt_iff _ _ _ _).mpr ⟨r,er⟩
    rw [fold_fixed p (fixed _ ml),fold_fixed p (fixed _ mr)]
    exact map_adj_apply.mpr ⟨⟨⟨e,rfl⟩,hl e⟩,ml,mr⟩
  · exact fun v h ho => (ordinaryMark_fold mark p fixed v).mpr ((ordinaryAt_iff _ _ _ _).mpr ⟨h,ho⟩)
  · exact loopless_foldFamily T hi (fun e => hl e.val) apart
  · exact two'
  · apply compatibility_fixed T p hi mark fixed
    exact fun u v hu hv hn e f i j k l => equal_internal T mark internal hn hn hu hv hv i j k l
  · exact palette

end Kostochka.FiveRegular
namespace Kostochka.FiveRegular.Restoration

open SimpleGraph Finset Subdivision Auxiliary Four.PathCover

variable {V E I X K : Type*} {D : Family V E}

namespace Atlas
variable (A : Atlas D I X K)
variable {V E : Type} {D : Family V E} (A : Atlas D I X K)
variable [Fintype V] [Fintype E] [Fintype I] [Fintype X] [Fintype K] [DecidableEq V]

theorem atlas_contracted_palette_from (paint : FactorPaint (Sym2 V)) {side : V → Bool} (C : A.PartitionColors side) (b : Bool) (exc : V → Prop) (loop : Loopless D)
    (mono : ∀ i (v : Fin (A.shape i).vertices), side (A.places ⟨i,v⟩) = A.pieceSide side i)
    (cross : ∀ x, side (A.outside.left x) ≠ side (A.outside.right x))
    (H : SimpleGraph V) (crossH : ∀ x, H.Reachable (A.outside.left x) (A.outside.right x))
    (home : ∀ i (v w : Fin (A.shape i).vertices), H.Reachable (A.places ⟨i,v⟩) (A.places ⟨i,w⟩))
    (bound : AtMostTwo (restrictFamily D (RawSquare.Internal D side)))
    (reg : ∀ i (v : Fin (A.shape i).vertices), coloredDegree A.outside (fun _ => true) (A.places ⟨i,v⟩) true +
      oldDegree (A.shape i) v.val = 4)
    (cut : ∀ e, A.oldMatching e = false → ¬ RawSquare.Internal D side e →
      ¬ (A.Saturated (D.left e) ∧ A.Saturated (D.right e)))
    (avoid : NoOrdinarySquare (ordinaryGraph (support D) (ordinaryAt side exc b))
      (support (factorFamily D (A.part C.exterior C.first C.second) b)) (ordinaryAt side exc b))
    (oldSquare : ∀ S : RawSquare D side b,
      (∀ j, A.part C.exterior C.first C.second (S.e j) = .factor b ∨
        A.part C.exterior C.first C.second (S.e (j+3)) = .factor b) →
      (∀ j, H.Reachable (S.v j) (S.v (j+2))) → ∀ j, A.oldMatching (S.e j) = false) :
    Nonempty (ContractedPalette D side (A.part C.exterior C.first C.second) exc b
      (folded (A.partner side C.first b))) := by
  classical
  let part := A.part C.exterior C.first C.second
  let T := factorFamily D part b
  let p := A.partner side C.first b
  let mark := ordinaryAt side exc b
  let S := ordinaryGraph (support D) mark
  have two : AtMostTwo T := atMostTwo_selected D (fun e => part e = .factor b) (by
    intro v
    have h := A.factor_constraints C reg v
    cases b <;> first | exact h.1 | exact h.2.1)
  have own (v) (h : mark v = true) : side v = b := ((ordinaryAt_iff ..).mp h).1
  have fix (v) (h : mark v = true) : p v = v := A.partner_fixed _ _ _ mono (own _ h)
  apply contracted_family_palette_from paint D loop side part exc b p (A.partner_involutive side C.first b) fix
    (inside_support_bound D side bound) two (A.atlas_internal_matching C _ b mono cross)
  · intro v mv e f he hf
    obtain ⟨x,hx,uniq⟩ := A.partner_unique C b loop reg v mv
    exact Subtype.ext ((uniq _ ⟨e.property,he⟩).trans (uniq _ ⟨f.property,hf⟩).symm)
  · exact A.partner_apart side _ _ _ b loop mono cross
  · apply no_ordinary_square_fold T p (A.partner_involutive side C.first b) S mark fix A.Saturated
      (A.partner_saturated side C.first b) (componentClosure H)
    · exact fun x y h => ⟨h.ne,A.factor_reachable _ _ _ b H crossH home h⟩
    · exact fun v => (closure_reachable H).mpr (A.partner_reachable _ _ _ H home v)
    · exact avoid
    · intro corners allMarked cycle cov reach02 reach13 i w notMarked adj
      let sq := RawSquare.ofSupport corners (fun k => own _ (allMarked k)) (fun k => (cycle k).1)
      have reach (k : Fin 4) : H.Reachable (sq.v k) (sq.v (k+2)) := by
        have r := (closure_reachable H).mp reach02
        have s := (closure_reachable H).mp reach13
        fin_cases k <;> first | exact r | exact s | exact r.symm | exact s.symm
      have old := oldSquare sq (sq.cover_of_support bound _ cov) reach
      apply A.square_factor_neighbor side _ _ _ b mono cross bound cut sq old i w _ adj
      intro j eq
      exact Bool.noConfusion (notMarked.symm.trans (eq ▸ allMarked j))

end Atlas
end Kostochka.FiveRegular.Restoration
namespace MultFive.Multi.PieceDecomposition

open SimpleGraph Kostochka.FiveRegular Subdivision Restoration Auxiliary

variable {V : Type} [Fintype V] [DecidableEq V] {m : Multi V}
    {M : m.support.Subgraph} {side : V → Bool} (D : PieceDecomposition m M side) (L : D.LabelCoverage)

theorem physical_contracted_palette_from (paint : FactorPaint (Sym2 V)) (P : (D.physical L).PartitionColors side)
    (regular : ∀ w, m.degree w = 5) (matching : M.IsPerfectMatching)
    (bound : ∀ w, m.insideDegree side w ≤ 2)
    (cut : ∀ u v, side u ≠ side v → (m.residual M).insideDegree side u = 2 →
      (m.residual M).insideDegree side v = 2 → (m.residual M).count u v = 0) (b : Bool) :
    let A := D.physical L
    let B := A.afterSquareDecision (A.squareDecision P.exterior side)
    let part := B.part P.exterior P.first P.second
    let exc v := ∃ e, part e = .exceptional ∧ FamilyIncident m.family v e
    Nonempty (ContractedPalette m.family side part exc b (folded (B.partner side P.first b))) := by
  classical
  let A := D.physical L
  let d := A.squareDecision P.exterior side
  let B := A.afterSquareDecision d
  let C := A.afterSquareColors d side P
  dsimp only
  refine B.atlas_contracted_palette_from paint C b _ m.family_loopless ?_ ?_ (m.residual M).support ?_ ?_
    (m.internal_atMostTwo side bound) (D.final_regular L d regular matching)
    (D.final_no_balanced L d regular matching cut) (D.physical_no_ordinary_square L P bound b) ?_
  · intro i v
    exact (D.final_monochromatic L d i v).trans (D.final_monochromatic L d i (vertexAt (B.shape i) 0)).symm
  · intro x
    rw [show B.outside = ((m.residual M).crossMulti side).family from D.physical_outside L]
    have cross := (((m.residual M).crossLabelEquiv side) x).property
    change side (((m.residual M).crossLabelEquiv side x).val.1.out.1) ≠
      side (((m.residual M).crossLabelEquiv side x).val.1.out.2) at cross
    rwa [(m.residual M).crossLabelEquiv_pair] at cross
  · intro x
    rw [show B.outside = ((m.residual M).crossMulti side).family from D.physical_outside L]
    exact ConnectedComponent.exact ((m.residual M).cross_ends side x)
  · intro i v w
    exact ConnectedComponent.exact ((D.final_component L d i v).trans (D.final_component L d i w).symm)
  · intro S covered reached j
    rw [Atlas.afterSquare_old]
    apply A.no_old_matching_on_covered_square (D.squareCatalog L bound) d P.exterior P.first P.second _ S covered reached j
    intro i shape
    exact P.normalized i (by change Atlas.markedShape (A.shape i) = true; rw [shape]; rfl)

end MultFive.Multi.PieceDecomposition
namespace MultFive.Multi.PieceDecomposition
open Kostochka.FiveRegular Subdivision Restoration Auxiliary

variable {V : Type} [Fintype V] [DecidableEq V] {m : Multi V} {M : m.support.Subgraph} {side : V → Bool}

/- Combine the §4 partition, the choices for four-cycles, the two folded palettes and the §5
local recolorings, and translate the labeled result back to sets of colors for parallel
edges. -/
theorem physical_seven_from (paint : FactorPaint (Sym2 V)) (D : PieceDecomposition m M side) (L : D.LabelCoverage) (regular : ∀ v, m.degree v = 5)
    (hm : M.IsPerfectMatching) (bound : ∀ v, m.insideDegree side v ≤ 2)
    (connected : ∀ u v, 0 < (m.residual M).count u v → (crossGraph (m.residual M).support side).Reachable u v)
    (balanced : ∀ u v, side u ≠ side v → (m.residual M).insideDegree side u = 2 →
      (m.residual M).insideDegree side v = 2 → (m.residual M).count u v = 0) : m.Colorable := by
  classical
  obtain ⟨P⟩ := D.physical_colors L regular hm connected
  let A := D.physical L
  let d := A.squareDecision P.exterior side
  let B := A.afterSquareDecision d
  let Q := A.afterSquareColors d side P
  apply m.colorable_of_restored_layers B side Q.exterior Q.first Q.second
  · intro v
    simpa only [B,Atlas.afterSquare_old,A,D.physical_tag L,m.family_incident_iff] using
      Multi.matching_edge_unique m M hm v
  · exact B.layers_of_charts Q (D.final_chartContext L P d regular hm bound)
      (D.badPath_closing L d) (fun v => ((m.family_degree v).trans (regular v)).le)
      (D.physical_contracted_palette_from L paint P regular hm bound balanced) (fun k => ⟨D.final_squareWitness L P k⟩)

end MultFive.Multi.PieceDecomposition
open MultFive SimpleGraph Kostochka.FiveRegular Kostochka.Four.PathCover
open scoped Classical
end
open MultFive SimpleGraph Kostochka.FiveRegular Kostochka.Four.PathCover
open scoped Classical

theorem OMA.solution : OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1_H2_R1_H3_R1.H3 := by
  classical
  intro W _ A mult sy zero regular support matching bad
  by_contra no
  have paint : FactorPaint (Sym2 W) := by
    intro S F decS decF sd fd marked inside three square
    have hs : decS = fun x y => Classical.propDecidable (S.Adj x y) := Subsingleton.elim _ _
    have hf : decF = fun x y => Classical.propDecidable (F.Adj x y) := Subsingleton.elim _ _
    subst decS
    subst decF
    by_contra missing
    apply no
    right
    refine ⟨S,F,marked,sd,fd,inside,three,square,?_⟩
    rintro ⟨c,e,vc,proper,avoids⟩
    apply missing
    refine ⟨c,vc,⟨⟨e,proper,?_⟩⟩⟩
    intro v f b h inc
    cases flag : marked v
    · simp [flag] at h
    · have eq := Option.some.inj (by simpa [flag] using h : some (c v) = some b)
      exact eq ▸ avoids v f flag inc

  let m : Multi W := ⟨mult,sy,zero⟩
  have same : A = m.support := by ext x y; exact support x y
  subst A
  obtain ⟨M,hm⟩ := matching
  obtain ⟨s,bound,connect,balanced⟩ := m.exists_matching_cut regular M hm
  let k := Multi.Rows.joined m M s
  have existsRows : ∃ rows : List (List W × Bool),
      (rows.map (fun p => p.1.toFinset)).Pairwise Disjoint ∧
      (∀ x, ∃ p ∈ rows, x ∈ p.1) ∧ ∀ p ∈ rows, p.1.Nodup ∧ p.1 ≠ [] ∧
      ∀ x ∈ p.1, ∀ y, k.count x y = Multi.Rows.weight p.1 p.2 x y := by
    by_contra missing
    apply no
    left
    refine ⟨k.count,k.symm,k.loopless,Multi.Rows.degree_bound m M s bound,?_⟩
    rintro ⟨rows,apart,cover,description⟩
    apply missing
    refine ⟨rows,apart,cover,?_⟩
    intro p hp
    obtain ⟨nd,ne,weights⟩ := description p hp
    refine ⟨nd,ne,?_⟩
    intro x hx y
    simpa [Multi.Rows.weight,Multi.Rows.neighbors] using weights x hx y
  obtain ⟨rows,apart,cover,description⟩ := existsRows
  obtain ⟨D⟩ := Multi.Rows.of_flat_rows m M hm s bound rows apart cover description
  obtain ⟨vc,ec,P⟩ := Multi.PieceDecomposition.physical_seven_from paint D D.labelCoverage regular hm bound connect balanced
  exact bad ⟨vc,ec,P.symmetric,P.size,P.vertices,P.avoids,P.disjoint⟩
