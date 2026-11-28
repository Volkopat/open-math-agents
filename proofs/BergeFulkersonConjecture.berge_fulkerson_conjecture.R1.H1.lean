import OMAReductions.R_BergeFulkersonConjecture_berge_fulkerson_conjecture_R1
import Mathlib

/-! A cubic graph with a proper 3-edge-colouring: at each vertex the three edges get distinct
colours, so each colour class is a perfect matching; taking each class twice gives six perfect
matchings covering every edge exactly twice. -/

open SimpleGraph BergeFulkersonConjecture

namespace BFH1

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The edges of colour `j`. -/
def cls (c : G.lineGraph.Coloring (Fin 3)) (j : Fin 3) : G.Subgraph where
  verts := Set.univ
  Adj u v := ∃ h : G.Adj u v, c ⟨s(u, v), h⟩ = j
  adj_sub := fun ⟨h, _⟩ => h
  edge_vert := fun _ => Set.mem_univ _
  symm := ⟨fun u v ⟨h, hc⟩ => ⟨h.symm, by rw [← hc]; congr 1; exact Subtype.ext Sym2.eq_swap⟩⟩

lemma cls_adj {c : G.lineGraph.Coloring (Fin 3)} {j : Fin 3} {u v : V} :
    (cls c j).Adj u v ↔ ∃ h : G.Adj u v, c ⟨s(u, v), h⟩ = j := Iff.rfl

lemma cls_verts {c : G.lineGraph.Coloring (Fin 3)} {j : Fin 3} (v : V) : v ∈ (cls c j).verts :=
  Set.mem_univ v

lemma mem_cls {c : G.lineGraph.Coloring (Fin 3)} {j : Fin 3} {e : Sym2 V} (he : e ∈ G.edgeSet) :
    e ∈ (cls c j).edgeSet ↔ c ⟨e, he⟩ = j := by
  induction e using Sym2.ind with
  | h u v =>
    rw [Subgraph.mem_edgeSet, cls_adj]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨he, h⟩⟩

lemma cls_perfect (hc : IsCubic G) (c : G.lineGraph.Coloring (Fin 3)) (j : Fin 3) :
    (cls c j).IsPerfectMatching := by
  refine ⟨fun v _ => ?_, fun v => cls_verts v⟩
  -- the colour map on the three edges at `v` is injective, hence onto `Fin 3`
  let col : V → Fin 3 := fun w => if h : G.Adj v w then c ⟨s(v, w), h⟩ else 0
  have inj : Set.InjOn col (G.neighborFinset v : Set V) := by
    intro w hw w' hw' heq
    by_contra hne
    simp only [Finset.mem_coe, mem_neighborFinset] at hw hw'
    simp only [col, dif_pos hw, dif_pos hw'] at heq
    refine c.valid ?_ heq
    rw [lineGraph_adj_iff_exists]
    refine ⟨fun h => hne ?_, v, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
    have := congrArg Subtype.val h
    simp only [Sym2.eq_iff] at this
    rcases this with ⟨-, h⟩ | ⟨rfl, rfl⟩
    · exact h
    · rfl
  have himg : (G.neighborFinset v).image col = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn inj, card_neighborFinset_eq_degree, hc v]
    rfl
  obtain ⟨w, hw, hwj⟩ := Finset.mem_image.mp (himg ▸ Finset.mem_univ j)
  have hw' : G.Adj v w := (mem_neighborFinset _ _ _).mp hw
  refine ⟨w, cls_adj.mpr ⟨hw', by simpa [col, hw'] using hwj⟩, fun w' hw'' => ?_⟩
  obtain ⟨h', hc'⟩ := cls_adj.mp hw''
  exact inj ((mem_neighborFinset _ _ _).mpr h') hw (by simp [col, h', hc', ← hwj, hw'])

end BFH1

open BFH1 in
theorem OMA.solution : OMA.R_BergeFulkersonConjecture_berge_fulkerson_conjecture_R1.H1 := by
  intro V _ _ G _ hc hcol
  obtain ⟨c⟩ := hcol
  refine ⟨fun i => cls c ⟨i.val % 3, Nat.mod_lt _ (by norm_num)⟩, fun i => cls_perfect hc c _,
    fun e he => ?_⟩
  simp only [mem_cls he]
  generalize c ⟨e, he⟩ = j
  fin_cases j <;> decide
