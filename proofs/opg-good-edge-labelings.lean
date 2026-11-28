import OMAStatements.S_opg_good_edge_labelings

-- Problem: Good Edge Labelings
-- Credit: @sobrien032

/- Disproof of Conjecture 36 of Júlio Araújo, Nathann Cohen, Frédéric Giroire
   and Frédéric Havet, Good edge-labelling of graphs (2012).
   The odd rim with two subdivided chords across each interval of three
   edges comes from the August 17, 2026 GPT-5.5 xhigh construction at
   https://probxiv.com/problems/good-edge-labelling-of-graphs-2 .

   We take an inclusion-minimal bad subgraph. Every subgraph has average
   degree at most 10/3. For each proposed order bound, a sufficiently long
   odd rim is bad while every subgraph within that order bound maps locally
   injectively into a fixed good template. The template certificate is
   closed under prepending one edge and distinguishes walks by their ends.
-/

namespace GEL

abbrev V (n : ℕ) := Fin 3 × Fin n

def shift {n : ℕ} [NeZero n] (i : Fin n) (s : ℕ) : Fin n :=
  i + Fin.ofNat n s

theorem shift_val {n : ℕ} [NeZero n] (i : Fin n) (s : ℕ) :
    (shift i s).val = (i.val + s) % n := by
  simp [shift, Fin.val_add, Fin.ofNat]

theorem shift_shift {n : ℕ} [NeZero n] (i : Fin n) (a b : ℕ) :
    shift (shift i a) b = shift i (a+b) := by
  apply Fin.ext
  simp only [shift_val, Nat.mod_add_mod, Nat.add_assoc]

theorem shift_injective {n : ℕ} [NeZero n] (s : ℕ) :
    Function.Injective (fun i : Fin n => shift i s) := by
  intro i j h
  exact add_right_cancel h

/- Tag zero denotes a rim vertex. Each of the two other vertices in a column
   joins the rim vertices in that column and three columns ahead. -/
def arc {n : ℕ} [NeZero n] (u v : V n) : Prop :=
  (u.1 = 0 ∧ v.1 = 0 ∧ v.2 = shift u.2 1) ∨
  (u.1 ≠ 0 ∧ v.1 = 0 ∧ (v.2 = u.2 ∨ v.2 = shift u.2 3))

instance {n : ℕ} [NeZero n] (u v : V n) : Decidable (arc u v) := by
  unfold arc
  infer_instance

def graph (n : ℕ) [NeZero n] : SimpleGraph (V n) where
  Adj u v := u ≠ v ∧ (arc u v ∨ arc v u)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1,h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance {n : ℕ} [NeZero n] : DecidableRel (graph n).Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ (arc u v ∨ arc v u)))

end GEL

namespace GEL
open OMA.S_opg_good_edge_labelings

private def walkTwo {W : Type*} {G : SimpleGraph W} {a b c : W}
    (ab : G.Adj a b) (bc : G.Adj b c) : G.Walk a c :=
  .cons ab (.cons bc .nil)

private theorem walkTwo_path {W : Type*} {G : SimpleGraph W} {a b c : W}
    (ab : G.Adj a b) (bc : G.Adj b c) (ac : a ≠ c) :
    (walkTwo ab bc).IsPath := by
  simp [walkTwo, SimpleGraph.Walk.isPath_def, ab.ne, bc.ne, ac]

private theorem consecutive_distinct {W : Type*} {G : SimpleGraph W} {a b c : W}
    {L : Sym2 W → ℝ} (h : IsGoodEdgeLabeling G L)
    (ab : G.Adj a b) (bc : G.Adj b c) (ac : a ≠ c) : L s(a,b) ≠ L s(b,c) := by
  intro eq
  have he := h.1 (show s(a,b) ∈ G.edgeSet from ab) (show s(b,c) ∈ G.edgeSet from bc) eq
  rcases Sym2.eq_iff.mp he with h | h
  · exact ab.ne h.1
  · exact ac h.1

private theorem two_detours {W : Type*} {G : SimpleGraph W} {a d p q : W}
    {L : Sym2 W → ℝ} (good : IsGoodEdgeLabeling G L) (ad : a ≠ d) (pq : p ≠ q)
    (ap : G.Adj a p) (pd : G.Adj p d) (aq : G.Adj a q) (qd : G.Adj q d)
    (r : G.Walk a d) (hr : r.IsPath) (hlen : r.length = 3)
    (hinc : (r.edges.map L).IsChain (· < ·)) : False := by
  have backwards {b : W} (ab : G.Adj a b) (bd : G.Adj b d) :
      L s(d,b) < L s(b,a) := by
    have hn : ¬ L s(a,b) < L s(b,d) := by
      intro h
      have he := good.2 a d ad r (walkTwo ab bd) hr (walkTwo_path ab bd ad) hinc
        (by simpa [walkTwo] using h)
      have he' := congrArg SimpleGraph.Walk.length he
      change r.length = 2 at he'
      omega
    rw [@Sym2.eq_swap _ d b, @Sym2.eq_swap _ b a]
    exact lt_of_le_of_ne (le_of_not_gt hn) (consecutive_distinct good ab bd ad).symm
  have he := good.2 d a ad.symm (walkTwo pd.symm ap.symm) (walkTwo qd.symm aq.symm)
    (walkTwo_path _ _ ad.symm) (walkTwo_path _ _ ad.symm)
    (by simpa [walkTwo] using backwards ap pd)
    (by simpa [walkTwo] using backwards aq qd)
  exact pq (congrArg (fun (w : G.Walk d a) => w.getVert 1) he)

private def rimAt (n j : ℕ) [NeZero n] : V n :=
  (0, ⟨j % n, Nat.mod_lt _ (NeZero.pos n)⟩)

private theorem rim_shift {n j s : ℕ} [NeZero n] :
    (rimAt n (j+s)).2 = shift (rimAt n j).2 s := by
  apply Fin.ext
  rw [shift_val]
  exact (Nat.mod_add_mod j n s).symm

private theorem rim_distinct {n : ℕ} [NeZero n] (j a b : ℕ) (ha : a < b) (hb : b < n) :
    rimAt n (j+a) ≠ rimAt n (j+b) := by
  intro he
  have h : j+a ≡ j+b [MOD n] := congrArg (fun (v : V n) => v.2.val) he
  have h' := (Nat.ModEq.add_left_cancel' j h).eq_of_lt_of_lt (by omega) hb
  omega

private theorem rim_adj {n : ℕ} [NeZero n] (hn : 9 ≤ n) (j : ℕ) :
    (graph n).Adj (rimAt n j) (rimAt n (j+1)) := by
  refine ⟨?_, Or.inl (Or.inl ⟨rfl, rfl, rim_shift⟩)⟩
  simpa using rim_distinct (n := n) j 0 1 (by decide) (by omega)

private theorem rim_period {n : ℕ} [NeZero n] (j : ℕ) : rimAt n (n+j) = rimAt n j := by
  simp [rimAt]

theorem bad_rim (n : ℕ) [NeZero n] (hn : 9 ≤ n) (ho : Odd n) :
    ¬ HasGoodEdgeLabeling (graph n) := by
  rintro ⟨L, good⟩
  let E (j : ℕ) := L s(rimAt n j,rimAt n (j+1))
  have nxt (j : ℕ) : E j ≠ E (j+1) := by
    apply consecutive_distinct good (rim_adj hn j) (rim_adj hn (j+1))
    simpa using rim_distinct (n := n) j 0 2 (by decide) (by omega)
  have turn (j : ℕ) : (E (j+1) < E (j+2)) ↔ ¬ (E j < E (j+1)) := by
    let a := rimAt n j
    let b := rimAt n (j+1)
    let c := rimAt n (j+2)
    let d := rimAt n (j+3)
    let p : V n := (1, a.2)
    let q : V n := (2, a.2)
    have ab : (graph n).Adj a b := rim_adj hn j
    have bc : (graph n).Adj b c := rim_adj hn (j+1)
    have cd : (graph n).Adj c d := rim_adj hn (j+2)
    have ac : a ≠ c := by simpa [a,c] using rim_distinct (n := n) j 0 2 (by decide) (by omega)
    have ad : a ≠ d := by simpa [a,d] using rim_distinct (n := n) j 0 3 (by decide) (by omega)
    have bd : b ≠ d := rim_distinct j 1 3 (by decide) (by omega)
    have pq : p ≠ q := by
      intro h
      exact (by decide : (1 : Fin 3) ≠ 2) (congrArg Prod.fst h)
    have spoke {t : Fin 3} (ht : t ≠ 0) :
        (graph n).Adj (t, a.2) a ∧ (graph n).Adj (t, a.2) d := by
      have h1 : (t, a.2) ≠ a := fun h => ht (congrArg Prod.fst h)
      have h2 : (t, a.2) ≠ d := fun h => ht (congrArg Prod.fst h)
      exact ⟨⟨h1, Or.inl (Or.inr ⟨ht, rfl, Or.inl rfl⟩)⟩,
        ⟨h2, Or.inl (Or.inr ⟨ht, rfl, Or.inr rim_shift⟩)⟩⟩
    obtain ⟨pa, pd⟩ := spoke (t := 1) (by decide)
    obtain ⟨qa, qd⟩ := spoke (t := 2) (by decide)
    constructor
    · intro h2 h1
      let r : (graph n).Walk a d := .cons ab (.cons bc (.cons cd .nil))
      apply two_detours good ad pq pa.symm pd qa.symm qd r
      · simp [r, SimpleGraph.Walk.isPath_def, ab.ne, bc.ne, cd.ne, ac, ad, bd]
      · rfl
      · simp only [r, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.map_cons,
          List.map_nil, List.isChain_cons_cons, List.isChain_singleton, and_true]
        exact ⟨h1,h2⟩
    · intro h1
      by_contra h2
      have hba : E (j+1) < E j := lt_of_le_of_ne (le_of_not_gt h1) (nxt j).symm
      have hcb : E (j+2) < E (j+1) := lt_of_le_of_ne (le_of_not_gt h2) (nxt (j+1)).symm
      let r : (graph n).Walk d a := .cons cd.symm (.cons bc.symm (.cons ab.symm .nil))
      apply two_detours good ad.symm pq pd.symm pa qd.symm qa r
      · simp [r, SimpleGraph.Walk.isPath_def, ab.ne.symm, bc.ne.symm, cd.ne.symm,
          ac.symm, ad.symm, bd.symm]
      · rfl
      · simp only [r, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.map_cons,
          List.map_nil, List.isChain_cons_cons, List.isChain_singleton, and_true]
        rw [@Sym2.eq_swap _ d c, @Sym2.eq_swap _ c b, @Sym2.eq_swap _ b a]
        exact ⟨hcb,hba⟩
  let up (j : ℕ) := E j < E (j+1)
  have step (j : ℕ) : up (j+1) ↔ ¬ up j := turn j
  have ev (k : ℕ) : up (2*k) ↔ up 0 := by
    induction k with
    | zero => rfl
    | succ k ih =>
      change up (2*k+1+1) ↔ up 0
      rw [step (2*k+1),step (2*k),not_not,ih]
  have period (j : ℕ) : E (n+j) = E j := by
    dsimp only [E]
    rw [Nat.add_assoc,rim_period,rim_period]
  have cyc : up n ↔ up 0 := by
    change (E n < E (n+1)) ↔ _
    have h0 : E n = E 0 := by simpa using period 0
    rw [h0,period 1]
  obtain ⟨k, hk⟩ := ho
  rw [hk, step, ev] at cyc
  tauto

end GEL

open SimpleGraph
open OMA.S_opg_good_edge_labelings

namespace GEL

private theorem good_of_hom {U W : Type*} {P : SimpleGraph U} {Q : SimpleGraph W}
    (f : P →g Q) (hf : Function.Injective f) (h : HasGoodEdgeLabeling Q) :
    HasGoodEdgeLabeling P := by
  obtain ⟨l, hinj, hpaths⟩ := h
  refine ⟨l ∘ Sym2.map f, ?_, ?_⟩
  · intro e he e' he' heq
    exact Sym2.map.injective hf (hinj (f.map_mem_edgeSet he) (f.map_mem_edgeSet he') heq)
  · intro u v huv p q hp hq hpinc hqinc
    apply Walk.map_injective_of_injective hf u v
    apply hpaths (f u) (f v) (fun h => huv (hf h)) (p.map f) (q.map f)
    · exact (Walk.isPath_map_iff_of_injective hf).mpr hp
    · exact (Walk.isPath_map_iff_of_injective hf).mpr hq
    · simpa only [Walk.edges_map, List.map_map] using hpinc
    · simpa only [Walk.edges_map, List.map_map] using hqinc

theorem critical_inside {W : Type*} [Finite W] {Q : SimpleGraph W}
    (hbad : ¬ HasGoodEdgeLabeling Q) : ∃ H : Q.Subgraph, IsGELCritical H.coe := by
  classical
  let bad : Q.Subgraph → Prop := fun H => ¬ HasGoodEdgeLabeling H.coe
  have htop : bad ⊤ := fun h => hbad (good_of_hom (Subgraph.topIso.symm).toHom
      (Subgraph.topIso.symm).injective h)
  obtain ⟨H, hH⟩ := (Set.toFinite {H | bad H}).exists_minimal ⟨⊤, htop⟩
  refine ⟨H, hH.1, ?_⟩
  intro K hK
  by_contra hb
  let f : K.coe →g (H.coeSubgraph K).coe :=
    { toFun := fun x => ⟨x.val.val, ⟨x.val, x.property, rfl⟩⟩
      map_rel' := fun {x y} h => (Subgraph.coeSubgraph_adj K _ _).mpr
        ⟨x.val.property, y.val.property, h⟩ }
  have hinj : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z => (z.val : W)) h))
  have heq : H.coeSubgraph K = H := le_antisymm (Subgraph.coeSubgraph_le K)
    (hH.2 (show bad (H.coeSubgraph K) from fun hg => hb (good_of_hom f hinj hg))
      (Subgraph.coeSubgraph_le K))
  apply hK
  apply Subgraph.coeSubgraph_injective H
  exact heq.trans (Subgraph.map_hom_top H).symm

private def coreEdge {n : ℕ} [NeZero n] (u : V n) : Sym2 (V n) :=
  s(u, (0, shift u.2 1))

private def fromAux {n : ℕ} [NeZero n] (p : V n × Bool) : Sym2 (V n) :=
  s(p.1, (0, if p.2 then shift p.1.2 3 else p.1.2))

private def toCore {n : ℕ} [NeZero n] (p : V n × Fin 4) : Sym2 (V n) :=
  s(((if p.2.val < 2 then 1 else 2),
     (if p.2.val % 2 = 0 then p.1.2 else p.1.2 - (3 : Fin n))), p.1)

private theorem cover_arc {n : ℕ} [NeZero n] (H : (graph n).Subgraph)
    (u v : V n) (hu : u ∈ H.verts) (hv : v ∈ H.verts) (ha : arc u v) :
    let C := H.verts ∩ {w | w.1 = 0}
    let A := H.verts \ {w | w.1 = 0}
    s(u,v) ∈ (coreEdge '' C) ∪ (fromAux '' (A ×ˢ Set.univ)) ∧
    s(u,v) ∈ (coreEdge '' C) ∪ (toCore '' (C ×ˢ Set.univ)) := by
  rcases u with ⟨r,i⟩
  rcases v with ⟨t,j⟩
  rcases ha with ⟨hr,ht,hj⟩ | ⟨hr,ht,hj⟩
  · change r = 0 at hr
    change t = 0 at ht
    change j = shift i 1 at hj
    subst r t j
    exact ⟨Or.inl ⟨_, ⟨hu,rfl⟩,rfl⟩, Or.inl ⟨_, ⟨hu,rfl⟩,rfl⟩⟩
  · change r ≠ 0 at hr
    change t = 0 at ht
    change j = i ∨ j = shift i 3 at hj
    have hr' : r = 1 ∨ r = 2 := by fin_cases r <;> simp_all
    subst t
    rcases hj with hj | hj <;> subst j
    · refine ⟨Or.inr ⟨((r,i),false), ⟨⟨hu,hr⟩,trivial⟩,rfl⟩, ?_⟩
      rcases hr' with rfl | rfl
      · exact Or.inr ⟨((0,i),0), ⟨⟨hv,rfl⟩,trivial⟩,rfl⟩
      · exact Or.inr ⟨((0,i),2), ⟨⟨hv,rfl⟩,trivial⟩, by norm_num [toCore]⟩
    · have hi : shift i 3 - (3 : Fin n) = i := by simp [shift]
      refine ⟨Or.inr ⟨((r,i),true), ⟨⟨hu,hr⟩,trivial⟩,rfl⟩, ?_⟩
      rcases hr' with rfl | rfl
      · refine Or.inr ⟨((0,shift i 3),1), ⟨⟨hv,rfl⟩,trivial⟩, ?_⟩
        change s(((1 : Fin 3), shift i 3 - (3 : Fin n)), ((0 : Fin 3), shift i 3)) = _
        rw [hi]
      · refine Or.inr ⟨((0,shift i 3),3), ⟨⟨hv,rfl⟩,trivial⟩, ?_⟩
        norm_num [toCore, hi]

theorem sparse (n : ℕ) [NeZero n] (_hn : 9 ≤ n) (H : (graph n).Subgraph) :
    2 * (H.coe.edgeSet.ncard : ℝ) / Nat.card H.verts < 7 / 2 := by
  classical
  let C : Set (V n) := H.verts ∩ {w | w.1 = 0}
  let A : Set (V n) := H.verts \ {w | w.1 = 0}
  let R := coreEdge '' C
  let U := fromAux '' (A ×ˢ Set.univ)
  let T := toCore '' (C ×ˢ Set.univ)
  have hcov : H.edgeSet ⊆ (R ∪ U) ∩ (R ∪ T) := by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
      intro he
      change H.Adj u v at he
      rcases (H.adj_sub he).2 with ha | ha
      · exact cover_arc H u v (H.edge_vert he) (H.edge_vert he.symm) ha
      · rw [Sym2.eq_swap]
        exact cover_arc H v u (H.edge_vert he.symm) (H.edge_vert he) ha
  have hr : R.ncard ≤ C.ncard := Set.ncard_image_le
  have hu : U.ncard ≤ A.ncard * 2 := by
    simpa [U, Set.ncard_prod] using (Set.ncard_image_le (s := A ×ˢ Set.univ) (f := fromAux))
  have ht : T.ncard ≤ C.ncard * 4 := by
    simpa [Set.ncard_prod] using (Set.ncard_image_le (s := C ×ˢ Set.univ) (f := toCore))
  have e₁ := (Set.ncard_le_ncard (hcov.trans Set.inter_subset_left)).trans
    (Set.ncard_union_le R U)
  have e₂ := (Set.ncard_le_ncard (hcov.trans Set.inter_subset_right)).trans
    (Set.ncard_union_le R T)
  have hv : C.ncard + A.ncard = Nat.card H.verts := by
    exact Set.ncard_inter_add_ncard_sdiff_eq_ncard H.verts {w | w.1 = 0}
  have hed : H.coe.edgeSet.ncard = H.edgeSet.ncard := by
    rw [← H.image_coe_edgeSet_coe, Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]
  have hn : 3 * H.coe.edgeSet.ncard ≤ 5 * Nat.card H.verts := by rw [hed]; omega
  by_cases hz : Nat.card H.verts = 0
  · rw [hz]
    norm_num
  · have hp : (0 : ℝ) < Nat.card H.verts := by exact_mod_cast Nat.pos_of_ne_zero hz
    apply (div_lt_iff₀ hp).mpr
    have hr' : 3 * (H.coe.edgeSet.ncard : ℝ) ≤ 5 * (Nat.card H.verts : ℝ) := by exact_mod_cast hn
    linarith

end GEL

namespace GEL

open OMA.S_opg_good_edge_labelings
open SimpleGraph

private def vertexCode (v : V 16) : ℕ := 16 * v.1.val + v.2.val

private lemma vertexCode_injective : Function.Injective vertexCode := by
  rintro ⟨a,i⟩ ⟨b,j⟩ h
  have hi := i.isLt
  have hj := j.isLt
  change 16 * a.val + i.val = 16 * b.val + j.val at h
  apply Prod.ext
  · apply Fin.ext
    change a.val = b.val
    omega
  · apply Fin.ext
    change i.val = j.val
    omega

/-- Alternating rim colors are 2 and 4. Each two-edge detour uses 1 and 5. -/
private def orientedColor (a b : ℕ) : ℕ :=
  if a / 16 = 0 then
    if b / 16 = 0 ∧ b % 16 = (a + 1) % 16 then
      if a % 2 = 0 then 2 else 4
    else 0
  else if b / 16 = 0 then
    if (a / 16 == 1) == (a % 16 == b % 16) then 1 else 5
  else 0

private def stepColor (a b : ℕ) : ℕ := max (orientedColor a b) (orientedColor b a)

private def mayPrepend (u : ℕ) : List ℕ → Bool
  | w :: z :: _ => decide (u ≠ z ∧ stepColor u w ≤ stepColor w z)
  | _ => true

/-- Each row contains full vertex lists, starting with the trivial walk.
The following certificates check closure under every legal prepend and uniqueness of endpoints. -/
private def pathsFrom : ℕ → List (List ℕ)
  | 0 => [[0], [0, 1], [0, 1, 2], [0, 1, 2, 31], [0, 1, 2, 34], [0, 1, 30], [0, 1, 33], [0, 15], [0, 15, 28], [0, 15, 47], [0, 16], [0, 16, 3], [0, 16, 3, 35], [0, 29], [0, 32], [0, 45], [0, 45, 13], [0, 45, 13, 26]]
  | 1 => [[1], [1, 0], [1, 0, 15], [1, 0, 15, 28], [1, 0, 15, 47], [1, 0, 29], [1, 0, 32], [1, 2], [1, 2, 31], [1, 2, 34], [1, 17], [1, 17, 4], [1, 17, 4, 36], [1, 30], [1, 33], [1, 46], [1, 46, 14], [1, 46, 14, 27]]
  | 2 => [[2], [2, 1], [2, 1, 30], [2, 1, 33], [2, 3], [2, 3, 4], [2, 3, 4, 17], [2, 3, 4, 36], [2, 3, 16], [2, 3, 35], [2, 18], [2, 18, 5], [2, 18, 5, 37], [2, 31], [2, 34], [2, 47], [2, 47, 15], [2, 47, 15, 28]]
  | 3 => [[3], [3, 2], [3, 2, 1], [3, 2, 1, 30], [3, 2, 1, 33], [3, 2, 31], [3, 2, 34], [3, 4], [3, 4, 17], [3, 4, 36], [3, 16], [3, 19], [3, 19, 6], [3, 19, 6, 38], [3, 32], [3, 32, 0], [3, 32, 0, 29], [3, 35]]
  | 4 => [[4], [4, 3], [4, 3, 16], [4, 3, 35], [4, 5], [4, 5, 6], [4, 5, 6, 19], [4, 5, 6, 38], [4, 5, 18], [4, 5, 37], [4, 17], [4, 20], [4, 20, 7], [4, 20, 7, 39], [4, 33], [4, 33, 1], [4, 33, 1, 30], [4, 36]]
  | 5 => [[5], [5, 4], [5, 4, 3], [5, 4, 3, 16], [5, 4, 3, 35], [5, 4, 17], [5, 4, 36], [5, 6], [5, 6, 19], [5, 6, 38], [5, 18], [5, 21], [5, 21, 8], [5, 21, 8, 40], [5, 34], [5, 34, 2], [5, 34, 2, 31], [5, 37]]
  | 6 => [[6], [6, 5], [6, 5, 18], [6, 5, 37], [6, 7], [6, 7, 8], [6, 7, 8, 21], [6, 7, 8, 40], [6, 7, 20], [6, 7, 39], [6, 19], [6, 22], [6, 22, 9], [6, 22, 9, 41], [6, 35], [6, 35, 3], [6, 35, 3, 16], [6, 38]]
  | 7 => [[7], [7, 6], [7, 6, 5], [7, 6, 5, 18], [7, 6, 5, 37], [7, 6, 19], [7, 6, 38], [7, 8], [7, 8, 21], [7, 8, 40], [7, 20], [7, 23], [7, 23, 10], [7, 23, 10, 42], [7, 36], [7, 36, 4], [7, 36, 4, 17], [7, 39]]
  | 8 => [[8], [8, 7], [8, 7, 20], [8, 7, 39], [8, 9], [8, 9, 10], [8, 9, 10, 23], [8, 9, 10, 42], [8, 9, 22], [8, 9, 41], [8, 21], [8, 24], [8, 24, 11], [8, 24, 11, 43], [8, 37], [8, 37, 5], [8, 37, 5, 18], [8, 40]]
  | 9 => [[9], [9, 8], [9, 8, 7], [9, 8, 7, 20], [9, 8, 7, 39], [9, 8, 21], [9, 8, 40], [9, 10], [9, 10, 23], [9, 10, 42], [9, 22], [9, 25], [9, 25, 12], [9, 25, 12, 44], [9, 38], [9, 38, 6], [9, 38, 6, 19], [9, 41]]
  | 10 => [[10], [10, 9], [10, 9, 22], [10, 9, 41], [10, 11], [10, 11, 12], [10, 11, 12, 25], [10, 11, 12, 44], [10, 11, 24], [10, 11, 43], [10, 23], [10, 26], [10, 26, 13], [10, 26, 13, 45], [10, 39], [10, 39, 7], [10, 39, 7, 20], [10, 42]]
  | 11 => [[11], [11, 10], [11, 10, 9], [11, 10, 9, 22], [11, 10, 9, 41], [11, 10, 23], [11, 10, 42], [11, 12], [11, 12, 25], [11, 12, 44], [11, 24], [11, 27], [11, 27, 14], [11, 27, 14, 46], [11, 40], [11, 40, 8], [11, 40, 8, 21], [11, 43]]
  | 12 => [[12], [12, 11], [12, 11, 24], [12, 11, 43], [12, 13], [12, 13, 14], [12, 13, 14, 27], [12, 13, 14, 46], [12, 13, 26], [12, 13, 45], [12, 25], [12, 28], [12, 28, 15], [12, 28, 15, 47], [12, 41], [12, 41, 9], [12, 41, 9, 22], [12, 44]]
  | 13 => [[13], [13, 12], [13, 12, 11], [13, 12, 11, 24], [13, 12, 11, 43], [13, 12, 25], [13, 12, 44], [13, 14], [13, 14, 27], [13, 14, 46], [13, 26], [13, 29], [13, 29, 0], [13, 29, 0, 32], [13, 42], [13, 42, 10], [13, 42, 10, 23], [13, 45]]
  | 14 => [[14], [14, 13], [14, 13, 26], [14, 13, 45], [14, 15], [14, 15, 0], [14, 15, 0, 29], [14, 15, 0, 32], [14, 15, 28], [14, 15, 47], [14, 27], [14, 30], [14, 30, 1], [14, 30, 1, 33], [14, 43], [14, 43, 11], [14, 43, 11, 24], [14, 46]]
  | 15 => [[15], [15, 0], [15, 0, 29], [15, 0, 32], [15, 14], [15, 14, 13], [15, 14, 13, 26], [15, 14, 13, 45], [15, 14, 27], [15, 14, 46], [15, 28], [15, 31], [15, 31, 2], [15, 31, 2, 34], [15, 44], [15, 44, 12], [15, 44, 12, 25], [15, 47]]
  | 16 => [[16], [16, 0], [16, 0, 1], [16, 0, 1, 2], [16, 0, 1, 2, 31], [16, 0, 1, 2, 34], [16, 0, 1, 30], [16, 0, 1, 33], [16, 0, 15], [16, 0, 15, 28], [16, 0, 15, 47], [16, 0, 29], [16, 0, 32], [16, 0, 45], [16, 0, 45, 13], [16, 0, 45, 13, 26], [16, 3], [16, 3, 35]]
  | 17 => [[17], [17, 1], [17, 1, 0], [17, 1, 0, 15], [17, 1, 0, 15, 28], [17, 1, 0, 15, 47], [17, 1, 0, 29], [17, 1, 0, 32], [17, 1, 2], [17, 1, 2, 31], [17, 1, 2, 34], [17, 1, 30], [17, 1, 33], [17, 1, 46], [17, 1, 46, 14], [17, 1, 46, 14, 27], [17, 4], [17, 4, 36]]
  | 18 => [[18], [18, 2], [18, 2, 1], [18, 2, 1, 30], [18, 2, 1, 33], [18, 2, 3], [18, 2, 3, 4], [18, 2, 3, 4, 17], [18, 2, 3, 4, 36], [18, 2, 3, 16], [18, 2, 3, 35], [18, 2, 31], [18, 2, 34], [18, 2, 47], [18, 2, 47, 15], [18, 2, 47, 15, 28], [18, 5], [18, 5, 37]]
  | 19 => [[19], [19, 3], [19, 3, 2], [19, 3, 2, 1], [19, 3, 2, 1, 30], [19, 3, 2, 1, 33], [19, 3, 2, 31], [19, 3, 2, 34], [19, 3, 4], [19, 3, 4, 17], [19, 3, 4, 36], [19, 3, 16], [19, 3, 32], [19, 3, 32, 0], [19, 3, 32, 0, 29], [19, 3, 35], [19, 6], [19, 6, 38]]
  | 20 => [[20], [20, 4], [20, 4, 3], [20, 4, 3, 16], [20, 4, 3, 35], [20, 4, 5], [20, 4, 5, 6], [20, 4, 5, 6, 19], [20, 4, 5, 6, 38], [20, 4, 5, 18], [20, 4, 5, 37], [20, 4, 17], [20, 4, 33], [20, 4, 33, 1], [20, 4, 33, 1, 30], [20, 4, 36], [20, 7], [20, 7, 39]]
  | 21 => [[21], [21, 5], [21, 5, 4], [21, 5, 4, 3], [21, 5, 4, 3, 16], [21, 5, 4, 3, 35], [21, 5, 4, 17], [21, 5, 4, 36], [21, 5, 6], [21, 5, 6, 19], [21, 5, 6, 38], [21, 5, 18], [21, 5, 34], [21, 5, 34, 2], [21, 5, 34, 2, 31], [21, 5, 37], [21, 8], [21, 8, 40]]
  | 22 => [[22], [22, 6], [22, 6, 5], [22, 6, 5, 18], [22, 6, 5, 37], [22, 6, 7], [22, 6, 7, 8], [22, 6, 7, 8, 21], [22, 6, 7, 8, 40], [22, 6, 7, 20], [22, 6, 7, 39], [22, 6, 19], [22, 6, 35], [22, 6, 35, 3], [22, 6, 35, 3, 16], [22, 6, 38], [22, 9], [22, 9, 41]]
  | 23 => [[23], [23, 7], [23, 7, 6], [23, 7, 6, 5], [23, 7, 6, 5, 18], [23, 7, 6, 5, 37], [23, 7, 6, 19], [23, 7, 6, 38], [23, 7, 8], [23, 7, 8, 21], [23, 7, 8, 40], [23, 7, 20], [23, 7, 36], [23, 7, 36, 4], [23, 7, 36, 4, 17], [23, 7, 39], [23, 10], [23, 10, 42]]
  | 24 => [[24], [24, 8], [24, 8, 7], [24, 8, 7, 20], [24, 8, 7, 39], [24, 8, 9], [24, 8, 9, 10], [24, 8, 9, 10, 23], [24, 8, 9, 10, 42], [24, 8, 9, 22], [24, 8, 9, 41], [24, 8, 21], [24, 8, 37], [24, 8, 37, 5], [24, 8, 37, 5, 18], [24, 8, 40], [24, 11], [24, 11, 43]]
  | 25 => [[25], [25, 9], [25, 9, 8], [25, 9, 8, 7], [25, 9, 8, 7, 20], [25, 9, 8, 7, 39], [25, 9, 8, 21], [25, 9, 8, 40], [25, 9, 10], [25, 9, 10, 23], [25, 9, 10, 42], [25, 9, 22], [25, 9, 38], [25, 9, 38, 6], [25, 9, 38, 6, 19], [25, 9, 41], [25, 12], [25, 12, 44]]
  | 26 => [[26], [26, 10], [26, 10, 9], [26, 10, 9, 22], [26, 10, 9, 41], [26, 10, 11], [26, 10, 11, 12], [26, 10, 11, 12, 25], [26, 10, 11, 12, 44], [26, 10, 11, 24], [26, 10, 11, 43], [26, 10, 23], [26, 10, 39], [26, 10, 39, 7], [26, 10, 39, 7, 20], [26, 10, 42], [26, 13], [26, 13, 45]]
  | 27 => [[27], [27, 11], [27, 11, 10], [27, 11, 10, 9], [27, 11, 10, 9, 22], [27, 11, 10, 9, 41], [27, 11, 10, 23], [27, 11, 10, 42], [27, 11, 12], [27, 11, 12, 25], [27, 11, 12, 44], [27, 11, 24], [27, 11, 40], [27, 11, 40, 8], [27, 11, 40, 8, 21], [27, 11, 43], [27, 14], [27, 14, 46]]
  | 28 => [[28], [28, 12], [28, 12, 11], [28, 12, 11, 24], [28, 12, 11, 43], [28, 12, 13], [28, 12, 13, 14], [28, 12, 13, 14, 27], [28, 12, 13, 14, 46], [28, 12, 13, 26], [28, 12, 13, 45], [28, 12, 25], [28, 12, 41], [28, 12, 41, 9], [28, 12, 41, 9, 22], [28, 12, 44], [28, 15], [28, 15, 47]]
  | 29 => [[29], [29, 0], [29, 0, 32], [29, 13], [29, 13, 12], [29, 13, 12, 11], [29, 13, 12, 11, 24], [29, 13, 12, 11, 43], [29, 13, 12, 25], [29, 13, 12, 44], [29, 13, 14], [29, 13, 14, 27], [29, 13, 14, 46], [29, 13, 26], [29, 13, 42], [29, 13, 42, 10], [29, 13, 42, 10, 23], [29, 13, 45]]
  | 30 => [[30], [30, 1], [30, 1, 33], [30, 14], [30, 14, 13], [30, 14, 13, 26], [30, 14, 13, 45], [30, 14, 15], [30, 14, 15, 0], [30, 14, 15, 0, 29], [30, 14, 15, 0, 32], [30, 14, 15, 28], [30, 14, 15, 47], [30, 14, 27], [30, 14, 43], [30, 14, 43, 11], [30, 14, 43, 11, 24], [30, 14, 46]]
  | 31 => [[31], [31, 2], [31, 2, 34], [31, 15], [31, 15, 0], [31, 15, 0, 29], [31, 15, 0, 32], [31, 15, 14], [31, 15, 14, 13], [31, 15, 14, 13, 26], [31, 15, 14, 13, 45], [31, 15, 14, 27], [31, 15, 14, 46], [31, 15, 28], [31, 15, 44], [31, 15, 44, 12], [31, 15, 44, 12, 25], [31, 15, 47]]
  | 32 => [[32], [32, 0], [32, 0, 29], [32, 3], [32, 3, 2], [32, 3, 2, 1], [32, 3, 2, 1, 30], [32, 3, 2, 1, 33], [32, 3, 2, 31], [32, 3, 2, 34], [32, 3, 4], [32, 3, 4, 17], [32, 3, 4, 36], [32, 3, 16], [32, 3, 19], [32, 3, 19, 6], [32, 3, 19, 6, 38], [32, 3, 35]]
  | 33 => [[33], [33, 1], [33, 1, 30], [33, 4], [33, 4, 3], [33, 4, 3, 16], [33, 4, 3, 35], [33, 4, 5], [33, 4, 5, 6], [33, 4, 5, 6, 19], [33, 4, 5, 6, 38], [33, 4, 5, 18], [33, 4, 5, 37], [33, 4, 17], [33, 4, 20], [33, 4, 20, 7], [33, 4, 20, 7, 39], [33, 4, 36]]
  | 34 => [[34], [34, 2], [34, 2, 31], [34, 5], [34, 5, 4], [34, 5, 4, 3], [34, 5, 4, 3, 16], [34, 5, 4, 3, 35], [34, 5, 4, 17], [34, 5, 4, 36], [34, 5, 6], [34, 5, 6, 19], [34, 5, 6, 38], [34, 5, 18], [34, 5, 21], [34, 5, 21, 8], [34, 5, 21, 8, 40], [34, 5, 37]]
  | 35 => [[35], [35, 3], [35, 3, 16], [35, 6], [35, 6, 5], [35, 6, 5, 18], [35, 6, 5, 37], [35, 6, 7], [35, 6, 7, 8], [35, 6, 7, 8, 21], [35, 6, 7, 8, 40], [35, 6, 7, 20], [35, 6, 7, 39], [35, 6, 19], [35, 6, 22], [35, 6, 22, 9], [35, 6, 22, 9, 41], [35, 6, 38]]
  | 36 => [[36], [36, 4], [36, 4, 17], [36, 7], [36, 7, 6], [36, 7, 6, 5], [36, 7, 6, 5, 18], [36, 7, 6, 5, 37], [36, 7, 6, 19], [36, 7, 6, 38], [36, 7, 8], [36, 7, 8, 21], [36, 7, 8, 40], [36, 7, 20], [36, 7, 23], [36, 7, 23, 10], [36, 7, 23, 10, 42], [36, 7, 39]]
  | 37 => [[37], [37, 5], [37, 5, 18], [37, 8], [37, 8, 7], [37, 8, 7, 20], [37, 8, 7, 39], [37, 8, 9], [37, 8, 9, 10], [37, 8, 9, 10, 23], [37, 8, 9, 10, 42], [37, 8, 9, 22], [37, 8, 9, 41], [37, 8, 21], [37, 8, 24], [37, 8, 24, 11], [37, 8, 24, 11, 43], [37, 8, 40]]
  | 38 => [[38], [38, 6], [38, 6, 19], [38, 9], [38, 9, 8], [38, 9, 8, 7], [38, 9, 8, 7, 20], [38, 9, 8, 7, 39], [38, 9, 8, 21], [38, 9, 8, 40], [38, 9, 10], [38, 9, 10, 23], [38, 9, 10, 42], [38, 9, 22], [38, 9, 25], [38, 9, 25, 12], [38, 9, 25, 12, 44], [38, 9, 41]]
  | 39 => [[39], [39, 7], [39, 7, 20], [39, 10], [39, 10, 9], [39, 10, 9, 22], [39, 10, 9, 41], [39, 10, 11], [39, 10, 11, 12], [39, 10, 11, 12, 25], [39, 10, 11, 12, 44], [39, 10, 11, 24], [39, 10, 11, 43], [39, 10, 23], [39, 10, 26], [39, 10, 26, 13], [39, 10, 26, 13, 45], [39, 10, 42]]
  | 40 => [[40], [40, 8], [40, 8, 21], [40, 11], [40, 11, 10], [40, 11, 10, 9], [40, 11, 10, 9, 22], [40, 11, 10, 9, 41], [40, 11, 10, 23], [40, 11, 10, 42], [40, 11, 12], [40, 11, 12, 25], [40, 11, 12, 44], [40, 11, 24], [40, 11, 27], [40, 11, 27, 14], [40, 11, 27, 14, 46], [40, 11, 43]]
  | 41 => [[41], [41, 9], [41, 9, 22], [41, 12], [41, 12, 11], [41, 12, 11, 24], [41, 12, 11, 43], [41, 12, 13], [41, 12, 13, 14], [41, 12, 13, 14, 27], [41, 12, 13, 14, 46], [41, 12, 13, 26], [41, 12, 13, 45], [41, 12, 25], [41, 12, 28], [41, 12, 28, 15], [41, 12, 28, 15, 47], [41, 12, 44]]
  | 42 => [[42], [42, 10], [42, 10, 23], [42, 13], [42, 13, 12], [42, 13, 12, 11], [42, 13, 12, 11, 24], [42, 13, 12, 11, 43], [42, 13, 12, 25], [42, 13, 12, 44], [42, 13, 14], [42, 13, 14, 27], [42, 13, 14, 46], [42, 13, 26], [42, 13, 29], [42, 13, 29, 0], [42, 13, 29, 0, 32], [42, 13, 45]]
  | 43 => [[43], [43, 11], [43, 11, 24], [43, 14], [43, 14, 13], [43, 14, 13, 26], [43, 14, 13, 45], [43, 14, 15], [43, 14, 15, 0], [43, 14, 15, 0, 29], [43, 14, 15, 0, 32], [43, 14, 15, 28], [43, 14, 15, 47], [43, 14, 27], [43, 14, 30], [43, 14, 30, 1], [43, 14, 30, 1, 33], [43, 14, 46]]
  | 44 => [[44], [44, 12], [44, 12, 25], [44, 15], [44, 15, 0], [44, 15, 0, 29], [44, 15, 0, 32], [44, 15, 14], [44, 15, 14, 13], [44, 15, 14, 13, 26], [44, 15, 14, 13, 45], [44, 15, 14, 27], [44, 15, 14, 46], [44, 15, 28], [44, 15, 31], [44, 15, 31, 2], [44, 15, 31, 2, 34], [44, 15, 47]]
  | 45 => [[45], [45, 0], [45, 0, 1], [45, 0, 1, 2], [45, 0, 1, 2, 31], [45, 0, 1, 2, 34], [45, 0, 1, 30], [45, 0, 1, 33], [45, 0, 15], [45, 0, 15, 28], [45, 0, 15, 47], [45, 0, 16], [45, 0, 16, 3], [45, 0, 16, 3, 35], [45, 0, 29], [45, 0, 32], [45, 13], [45, 13, 26]]
  | 46 => [[46], [46, 1], [46, 1, 0], [46, 1, 0, 15], [46, 1, 0, 15, 28], [46, 1, 0, 15, 47], [46, 1, 0, 29], [46, 1, 0, 32], [46, 1, 2], [46, 1, 2, 31], [46, 1, 2, 34], [46, 1, 17], [46, 1, 17, 4], [46, 1, 17, 4, 36], [46, 1, 30], [46, 1, 33], [46, 14], [46, 14, 27]]
  | 47 => [[47], [47, 2], [47, 2, 1], [47, 2, 1, 30], [47, 2, 1, 33], [47, 2, 3], [47, 2, 3, 4], [47, 2, 3, 4, 17], [47, 2, 3, 4, 36], [47, 2, 3, 16], [47, 2, 3, 35], [47, 2, 18], [47, 2, 18, 5], [47, 2, 18, 5, 37], [47, 2, 31], [47, 2, 34], [47, 15], [47, 15, 28]]
  | _ => []

private def closureCheck (a b : V 16) : Bool :=
  (pathsFrom (vertexCode b)).all fun l =>
    !(mayPrepend (vertexCode a) l) || decide (vertexCode a :: l ∈ pathsFrom (vertexCode a))

private def endCheck (a : V 16) : Bool :=
  (pathsFrom (vertexCode a)).all fun l => (pathsFrom (vertexCode a)).all fun m =>
    decide (l.getLast? = m.getLast? → l = m)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1200000 in
private theorem pathsCertificates : ∀ t : Fin 3, ∀ i : Fin 16,
    [vertexCode (t,i)] ∈ pathsFrom (vertexCode (t,i)) ∧ endCheck (t,i) = true := by
  intro t
  fin_cases t <;> decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2400000 in
private theorem prependCertificate : ∀ t s : Fin 3, ∀ i j : Fin 16,
    (graph 16).Adj (t,i) (s,j) → closureCheck (t,i) (s,j) = true := by
  intro t s
  fin_cases t <;> fin_cases s <;> decide +kernel

private lemma paths_closed {u w : V 16} {l : List ℕ}
    (h : (graph 16).Adj u w) (hl : l ∈ pathsFrom (vertexCode w))
    (ok : mayPrepend (vertexCode u) l = true) :
    vertexCode u :: l ∈ pathsFrom (vertexCode u) := by
  obtain ⟨t,i⟩ := u
  obtain ⟨s,j⟩ := w
  have eqn := (List.all_eq_true.mp (prependCertificate t s i j h)) l hl
  simpa [ok] using eqn

private lemma paths_end_unique {u : V 16} {l m : List ℕ}
    (hl : l ∈ pathsFrom (vertexCode u)) (hm : m ∈ pathsFrom (vertexCode u))
    (he : l.getLast? = m.getLast?) : l = m := by
  obtain ⟨t,i⟩ := u
  have outer := List.all_eq_true.mp (pathsCertificates t i).2 l hl
  exact (of_decide_eq_true (List.all_eq_true.mp outer m hm)) he

private lemma mapped_support_head {W : Type} {H : SimpleGraph W} {u v : W}
    (p : H.Walk u v) (g : W → ℕ) : (p.support.map g).head? = some (g u) := by
  cases p <;> rfl

private lemma mapped_support_last {W : Type} {H : SimpleGraph W} {u v : W}
    (p : H.Walk u v) (g : W → ℕ) : (p.support.map g).getLast? = some (g v) := by
  simp [List.getLast?_eq_getLast_of_ne_nil p.support_ne_nil]

private lemma lift_support {W : Type} {H : SimpleGraph W} (f : H →g graph 16)
    (hf : ∀ u, Set.InjOn f (H.neighborSet u)) {u v : W} (p : H.Walk u v) :
    ∀ {w : W} (q : H.Walk u w),
      p.support.map (vertexCode ∘ f) = q.support.map (vertexCode ∘ f) →
        p.support = q.support := by
  induction p with
  | nil =>
    intro w q eqn
    cases q with
    | nil => rfl
    | cons edge tail =>
      simp only [Walk.support_nil, Walk.support_cons, List.map_cons, List.map_nil,
        List.cons.injEq, true_and, eq_comm (a := [])] at eqn
      exact False.elim (tail.support_ne_nil (List.map_eq_nil_iff.mp eqn))
  | @cons u a v edge p ih =>
    intro w q eqn
    cases q with
    | nil =>
      simp only [Walk.support_nil, Walk.support_cons, List.map_cons, List.map_nil,
        List.cons.injEq, true_and] at eqn
      exact False.elim (p.support_ne_nil (List.map_eq_nil_iff.mp eqn))
    | @cons _ b _ edge' q =>
      have ht := (List.cons.inj eqn).2
      have hh := congrArg List.head? ht
      rw [mapped_support_head, mapped_support_head] at hh
      have hab : a = b := hf u edge edge' (vertexCode_injective (Option.some.inj hh))
      subst b
      exact congrArg (u :: ·) (ih q ht)

private lemma mapped_path_mem {W : Type} {H : SimpleGraph W} (f : H →g graph 16)
    (hf : ∀ u, Set.InjOn f (H.neighborSet u)) (lab : Sym2 W → ℝ)
    (hcolor : ∀ a b c : W, lab s(a,b) < lab s(b,c) →
      stepColor (vertexCode (f a)) (vertexCode (f b)) ≤
        stepColor (vertexCode (f b)) (vertexCode (f c)))
    {u v : W} (p : H.Walk u v) (hp : p.IsPath)
    (hinc : (p.edges.map lab).IsChain (· < ·)) :
    p.support.map (vertexCode ∘ f) ∈ pathsFrom (vertexCode (f u)) := by
  induction p with
  | nil => exact (pathsCertificates _ _).1
  | @cons a b v edge p ih =>
    have ht : (p.edges.map lab).IsChain (· < ·) := hinc.tail
    apply paths_closed (f.map_adj edge) (ih hp.of_cons ht)
    cases p with
    | nil => rfl
    | @cons _ c _ edge' r =>
      have hn : a ≠ c := by
        intro e
        apply (Walk.cons_isPath_iff _ _).mp hp |>.2
        simp [e]
      have hne : vertexCode (f a) ≠ vertexCode (f c) := by
        intro hx
        exact hn (hf b edge.symm edge' (vertexCode_injective hx))
      have hx : lab s(a,b) < lab s(b,c) := (List.isChain_cons_cons.mp hinc).1
      change mayPrepend _ (_ :: r.support.map _) = true
      rw [← r.cons_tail_support]
      exact decide_eq_true ⟨hne, hcolor a b c hx⟩

private def domainColor {W : Type} {H : SimpleGraph W} (f : H →g graph 16) : Sym2 W → ℕ :=
  Sym2.lift ⟨fun a b => stepColor (vertexCode (f a)) (vertexCode (f b)),
    fun _ _ => max_comm _ _⟩

/-- A locally injective hom into the even template gives an injective good labeling.
The integer part orders the four colors; the remainder distinguishes every domain edge. -/
theorem good_of_local {W : Type} [Fintype W] (H : SimpleGraph W) (f : H →g graph 16)
    (hf : ∀ u, Set.InjOn f (H.neighborSet u)) : HasGoodEdgeLabeling H := by
  classical
  let enc := Fintype.equivFin (Sym2 W)
  let m := Fintype.card (Sym2 W) + 1
  let num (e : Sym2 W) := (enc e).val + m * domainColor f e
  let lab (e : Sym2 W) : ℝ := (num e : ℕ)
  have enc_lt (e : Sym2 W) : (enc e).val < m := Nat.lt_succ_of_lt (enc e).isLt
  have residue (e : Sym2 W) : num e % m = (enc e).val := by
    simp [num, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (enc_lt e)]
  refine ⟨lab, ?_, ?_⟩
  · intro a _ b _ eqn
    change (num a : ℝ) = (num b : ℝ) at eqn
    have he : num a = num b := by exact_mod_cast eqn
    apply enc.injective
    apply Fin.ext
    rw [← residue, ← residue, he]
  · intro u v _ p q hp hq hip hiq
    have hc (a b c : W) (hl : lab s(a,b) < lab s(b,c)) :
        stepColor (vertexCode (f a)) (vertexCode (f b)) ≤
          stepColor (vertexCode (f b)) (vertexCode (f c)) := by
      change domainColor f s(a,b) ≤ domainColor f s(b,c)
      change (num s(a,b) : ℝ) < (num s(b,c) : ℝ) at hl
      have hh : num s(a,b) < num s(b,c) := by exact_mod_cast hl
      by_contra! h
      have hle := Nat.mul_le_mul_left m h
      have hib := enc_lt s(b,c)
      change m * (domainColor f s(b,c) + 1) ≤ _ at hle
      rw [Nat.mul_add, Nat.mul_one] at hle
      dsimp only [num] at hh
      omega
    apply Walk.ext_support
    apply lift_support f hf p q
    apply paths_end_unique (mapped_path_mem f hf lab hc p hp hip)
      (mapped_path_mem f hf lab hc q hq hiq)
    rw [mapped_support_last, mapped_support_last]

end GEL

namespace GEL

/- An empty block of four columns allows the odd rim to be cut. On the
   two sides of the cut the column maps differ by one, making the wrap
   around a rim of length 1 modulo 16 agree with the template. -/
private abbrev rimLength (N : ℕ) := 16 * (N + 1) + 1

private def cutColumn {N : ℕ} (a : ℕ) (i : Fin (rimLength N)) : Fin 16 :=
  Fin.ofNat 16 (if i.val < a then i.val + 1 else i.val)

private theorem cut_shift {N a s : ℕ} {i j : Fin (rimLength N)} (hs : s ≤ 3)
    (ha : a + 4 ≤ rimLength N) (_hi : i.val < a ∨ a + 4 ≤ i.val)
    (hj : j.val < a ∨ a + 4 ≤ j.val) (h : j = shift i s) :
    cutColumn a j = shift (cutColumn a i) s := by
  have hij : j.val = (i.val+s) % rimLength N := by rw [h,shift_val]
  apply Fin.ext
  rw [shift_val]
  simp only [cutColumn, Fin.ofNat, Nat.mod_add_mod]
  have hN := i.isLt
  have hJ := j.isLt
  by_cases hsmall : i.val+s < rimLength N
  · rw [Nat.mod_eq_of_lt hsmall] at hij
    split <;> split <;> omega
  · have hh : i.val+s-rimLength N < rimLength N := by dsimp [rimLength] at *; omega
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hh] at hij
    dsimp [rimLength] at *
    split <;> split <;> omega

private theorem arc_steps {n : ℕ} [NeZero n] {u v : V n} (h : arc u v) :
    ∃ s ≤ 3, v.2 = shift u.2 s := by
  rcases h with ⟨_,_,h⟩ | ⟨_,_,h|h⟩
  · exact ⟨1,by decide,h⟩
  · exact ⟨0,by decide,by simpa [shift] using h⟩
  · exact ⟨3,by decide,h⟩

private theorem shift_ne_one (i : Fin 16) : i ≠ shift i 1 := by
  intro h
  have hv := congrArg Fin.val h
  rw [shift_val] at hv
  omega

theorem local_template (N : ℕ) (H : (graph (rimLength N)).Subgraph)
    (hcard : Nat.card H.verts ≤ N) :
    ∃ f : H.coe →g graph 16, ∀ u, Set.InjOn f (H.coe.neighborSet u) := by
  classical
  let _ := Fintype.ofFinite H.verts
  let used := (Finset.univ : Finset H.verts).image fun u => u.val.2.val / 4
  have hused : used.card ≤ N := by
    calc used.card ≤ (Finset.univ : Finset H.verts).card := Finset.card_image_le
         _ = Nat.card H.verts := by rw [Finset.card_univ,Nat.card_eq_fintype_card]
         _ ≤ N := hcard
  obtain ⟨b,hbr,hb⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show used.card < (Finset.range (N+1)).card by simpa using Nat.lt_succ_of_le hused)
  have hbN := Finset.mem_range.mp hbr
  let a := 4*b
  have ha : a+4 ≤ rimLength N := by dsimp [a,rimLength]; omega
  have away (u : H.verts) : u.val.2.val < a ∨ a + 4 ≤ u.val.2.val := by
    have hn : u.val.2.val / 4 ≠ b := by
      intro he
      exact hb (he ▸ Finset.mem_image_of_mem (fun w : H.verts => w.val.2.val / 4)
        (Finset.mem_univ u))
    dsimp [a]; omega
  let F (u : H.verts) : V 16 := (u.val.1,cutColumn a u.val.2)
  have mapShift (u v : H.verts) (s : ℕ) (hs : s ≤ 3)
      (h : v.val.2 = shift u.val.2 s) : (F v).2 = shift (F u).2 s :=
    cut_shift hs ha (away u) (away v) h
  have mapArc (u v : H.verts) (h : arc u.val v.val) : F u ≠ F v ∧ arc (F u) (F v) := by
    rcases h with ⟨hu,hv,h⟩ | ⟨hu,hv,h⟩
    · have hs := mapShift u v 1 (by decide) h
      exact ⟨fun he => shift_ne_one _ ((congrArg Prod.snd he).trans hs),
        Or.inl ⟨hu,hv,hs⟩⟩
    · have hne : F u ≠ F v := fun he => hu ((congrArg Prod.fst he).trans hv)
      refine ⟨hne,Or.inr ⟨hu,hv,?_⟩⟩
      exact h.elim (fun e => Or.inl (congrArg (cutColumn a) e))
        (fun e => Or.inr (mapShift u v 3 (by decide) e))
  let f : H.coe →g graph 16 := {
    toFun := F
    map_rel' := by
      intro u v huv
      rcases (H.coe_adj_sub u v huv).2 with h|h
      · exact ⟨(mapArc u v h).1,Or.inl (mapArc u v h).2⟩
      · exact ⟨(mapArc v u h).1.symm,Or.inr (mapArc v u h).2⟩ }
  refine ⟨f,?_⟩
  have offsets (u v : H.verts) (h : H.coe.Adj u v) :
      ∃ q ≤ 6, shift v.val.2 3 = shift u.val.2 q ∧
        shift (F v).2 3 = shift (F u).2 q := by
    rcases (H.coe_adj_sub u v h).2 with h|h
    · obtain ⟨s,hs,he⟩ := arc_steps h
      have hF := mapShift u v s hs he
      exact ⟨s+3,by omega,by rw [he,shift_shift],by rw [hF,shift_shift]⟩
    · obtain ⟨s,hs,he⟩ := arc_steps h
      have hF := mapShift v u s hs he
      have hsum : s + (3-s) = 3 := by omega
      exact ⟨3-s,by omega,by rw [he,shift_shift,hsum],by rw [hF,shift_shift,hsum]⟩
  intro u v hv w hw he
  change F v = F w at he
  obtain ⟨q,hq,hnq,hfq⟩ := offsets u v hv
  obtain ⟨s,hs,hns,hfs⟩ := offsets u w hw
  rw [he,hfs] at hfq
  have heqs := congrArg Fin.val hfq
  simp only [shift_val] at heqs
  have hsq : s = q := by omega
  have hsecond := shift_injective 3 (hnq.trans (hsq ▸ hns).symm)
  exact Subtype.ext (Prod.ext (congrArg (Prod.fst : V 16 → Fin 3) he) hsecond)

end GEL

theorem OMA.disproof : ¬ (type_of% @OMA.S_opg_good_edge_labelings.main) := by
  classical
  intro h
  obtain ⟨N,hN⟩ := h (7/2) (by norm_num)
  let n := 16 * (N+1) + 1
  have hn : 9 ≤ n := by dsimp [n]; omega
  have hodd : Odd n := ⟨8*(N+1),by dsimp [n]; omega⟩
  obtain ⟨H,hcrit⟩ := GEL.critical_inside (GEL.bad_rim n hn hodd)
  let _ := Fintype.ofFinite H.verts
  have hsize : Nat.card H.verts ≤ N := by
    rw [Nat.card_eq_fintype_card]
    apply hN H.verts H.coe hcrit
    simpa only [Nat.card_eq_fintype_card] using GEL.sparse n hn H
  obtain ⟨f,hf⟩ := GEL.local_template N H hsize
  exact hcrit.1 (GEL.good_of_local H.coe f hf)
