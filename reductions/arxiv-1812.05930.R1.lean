import OMAStatements.S_arxiv_1812_05930

-- Credit: @ryansolves
namespace OMA.R_arxiv_1812_05930_R1
open OMA.S_arxiv_1812_05930

/-- Regular density outside the single-edge and small odd-cycle-transversal cases. -/
def H1 : Prop :=
  ∀ (n d : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    0 < d → (∀ v, G.degree v = d) → 5*d < 2*n →
    (∀ A B : Finset (Fin n), Disjoint A B → G.IsIndepSet A → G.IsIndepSet B →
      n < 10*(A ∪ B)ᶜ.card) →
    ∃ M, inducedMatching G M ∧ 2*n ≤ 5*d*M.card

/-- Mixed incidence widths, excluding bipartitions with a side of degree at most 5Δ/8. -/
def H2 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∃ e ∈ edges G, ∃ f ∈ edges G, (incidentBlock G e).card ≠ (incidentBlock G f).card) →
    (∀ A B : Finset (Fin n), G.IsBipartiteWith A B →
      ∃ u ∈ A, 5*degreeBound G < 8*G.degree u) →
    ∀ x, feasible G x → ∃ M, inducedMatching G M ∧
      (∑ e ∈ edges G, x e) ≤ ((5/8 : ℝ)*degreeBound G+C)*M.card

/-- The uniform polynomial-time integer approximation, independent of fractional weights. -/
def H3 : Prop :=
  ∃ (C : ℝ) (algorithm : List Bool → List Bool), 0 ≤ C ∧
    Nonempty (Turing.TM2ComputableInPolyTime id id algorithm) ∧
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)), ∃ M, inducedMatching G M ∧
      algorithm (graphBits G) = matchingBits M ∧
      ∀ N, inducedMatching G N → (N.card : ℝ) ≤ ((5/8 : ℝ)*degreeBound G+C)*M.card

theorem transpose_sum {α : Type*} [DecidableEq α]
    (E : Finset α) (F : α → Finset α) (k : ℕ)
    (sub : ∀ i ∈ E, F i ⊆ E)
    (sym : ∀ i ∈ E, ∀ j ∈ E, j ∈ F i ↔ i ∈ F j)
    (card : ∀ i ∈ E, (F i).card = k) (x : α → ℝ) :
    (∑ i ∈ E, ∑ j ∈ F i, x j) = (k : ℝ) * ∑ j ∈ E, x j := by
  classical
  have filt (i) (hi : i ∈ E) : E.filter (· ∈ F i) = F i := by
    ext j
    exact Finset.mem_filter.trans ⟨And.right, fun hj => ⟨sub i hi hj,hj⟩⟩
  calc
    _ = ∑ i ∈ E, ∑ j ∈ E, if j ∈ F i then x j else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_filter, filt i hi]
    _ = ∑ j ∈ E, ∑ i ∈ E, if j ∈ F i then x j else 0 := Finset.sum_comm
    _ = ∑ j ∈ E, (k : ℝ) * x j := by
      apply Finset.sum_congr rfl
      intro j hj
      calc
        _ = ∑ i ∈ E, if i ∈ F j then x j else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [sym i hi j hj]
        _ = _ := by rw [← Finset.sum_filter, filt j hj]; simp [card j hj]
    _ = _ := (Finset.mul_sum ..).symm

private theorem degree_le_width {n k} (G : SimpleGraph (Fin n))
    (width : ∀ e ∈ edges G, (incidentBlock G e).card = k) : degreeBound G ≤ k := by
  classical
  unfold degreeBound
  apply G.maxDegree_le_of_forall_degree_le
  intro v
  by_cases pos : 0 < G.degree v
  · obtain ⟨w,adj⟩ := (G.degree_pos_iff_exists_adj v).mp pos
    have edge : s(v,w) ∈ edges G := by simpa [edges] using adj
    have sub : G.incidenceFinset v ⊆ incidentBlock G s(v,w) := by
      intro f hf
      rw [G.incidenceFinset_eq_filter] at hf
      obtain ⟨ef,vf⟩ := Finset.mem_filter.mp hf
      apply Finset.mem_filter.mpr
      refine ⟨by simpa [edges] using ef,Finset.nonempty_iff_ne_empty.mp ⟨v,?_⟩⟩
      exact Finset.mem_inter.mpr ⟨Sym2.mem_toFinset.mpr (Sym2.mem_mk_left ..),Sym2.mem_toFinset.mpr vf⟩
    simpa only [G.card_incidenceFinset_eq_degree,width _ edge] using Finset.card_le_card sub
  · omega

private theorem width_positive {n k} {G : SimpleGraph (Fin n)}
    (nonempty : (edges G).Nonempty) (width : ∀ e ∈ edges G, (incidentBlock G e).card = k) : 0 < k := by
  obtain ⟨e,he⟩ := nonempty
  rw [← width e he, Finset.card_pos]
  exact ⟨e, Finset.mem_filter.mpr ⟨he, by simp⟩⟩

private theorem width_bound {n k} {G : SimpleGraph (Fin n)}
    (width : ∀ e ∈ edges G, (incidentBlock G e).card = k) (x) (hx : feasible G x) :
    (k : ℝ)*(∑ e ∈ edges G, x e) ≤ (edges G).card := by
  classical
  have sub : ∀ i ∈ edges G, incidentBlock G i ⊆ edges G := fun _ _ => Finset.filter_subset ..
  have sym : ∀ i ∈ edges G, ∀ j ∈ edges G, j ∈ incidentBlock G i ↔ i ∈ incidentBlock G j := by
    intro i hi j hj
    simp [incidentBlock, hi, hj, Finset.inter_comm]
  have eqn := transpose_sum (edges G) (incidentBlock G) k sub sym width x
  have bound := Finset.sum_le_sum (fun i (hi : i ∈ edges G) => hx.2 i hi)
  rw [eqn] at bound
  simpa using bound

private theorem in_block {n} {G : SimpleGraph (Fin n)} {e f : Sym2 (Fin n)} :
    f ∈ incidentBlock G e ↔ f ∈ edges G ∧ ∃ u, u ∈ e ∧ u ∈ f := by
  classical
  simp only [incidentBlock, Finset.mem_filter, ← Finset.nonempty_iff_ne_empty,
    Finset.Nonempty, Finset.mem_inter, Sym2.mem_toFinset]

private theorem has_mate {n} {G : SimpleGraph (Fin n)} {f : Sym2 (Fin n)}
    (hf : f ∈ edges G) {x} (hx : x ∈ f) : ∃ y ∈ f, G.Adj x y := by
  obtain ⟨y,rfl⟩ := Sym2.mem_iff_exists.mp hx
  exact ⟨y,Sym2.mem_mk_right .., by simpa [edges] using hf⟩

theorem induced_iff_endpoints {n} {G : SimpleGraph (Fin n)} {M : Finset (Sym2 (Fin n))} :
    inducedMatching G M ↔ M ⊆ edges G ∧
    ∀ e ∈ M, ∀ f ∈ M, ∀ a ∈ e, ∀ b ∈ f, G.Adj a b → e = f := by
  classical
  constructor
  · rintro ⟨sub,one⟩
    refine ⟨sub,?_⟩
    intro e he f hf a ha b hb hab
    apply Finset.card_le_one_iff.mp (one s(a,b) (by simpa [edges] using hab))
    · exact Finset.mem_inter.mpr ⟨in_block.mpr ⟨sub he,a,Sym2.mem_mk_left ..,ha⟩,he⟩
    · exact Finset.mem_inter.mpr ⟨in_block.mpr ⟨sub hf,b,Sym2.mem_mk_right ..,hb⟩,hf⟩
  · rintro ⟨sub,noCross⟩
    refine ⟨sub,?_⟩
    intro c hc
    induction c using Sym2.inductionOn with
    | _ u v =>
      have uv : G.Adj u v := by simpa [edges] using hc
      apply Finset.card_le_one_iff.mpr
      intro e f he hf
      obtain ⟨eb,em⟩ := Finset.mem_inter.mp he
      obtain ⟨fb,fm⟩ := Finset.mem_inter.mp hf
      obtain ⟨_,a,ac,ae⟩ := in_block.mp eb
      obtain ⟨_,b,bc,bf⟩ := in_block.mp fb
      by_cases same : a = b
      · subst b
        obtain ⟨z,zf,az⟩ := has_mate (sub fm) bf
        exact noCross e em f fm a ae z zf az
      · have ab : G.Adj a b := by
          rcases Sym2.mem_iff.mp ac with rfl|rfl <;> rcases Sym2.mem_iff.mp bc with rfl|rfl <;> tauto
        exact noCross e em f fm a ae b bf ab

/-- Mapping vertices through any map that preserves and reflects adjacency
preserves both an induced matching and its cardinality. -/
theorem project_induced_matching {n m} {G : SimpleGraph (Fin n)} {H : SimpleGraph (Fin m)}
    (p : Fin n → Fin m) (cover : ∀ u v, G.Adj u v ↔ H.Adj (p u) (p v))
    (M : Finset (Sym2 (Fin n))) (hm : inducedMatching G M) :
    inducedMatching H (M.image (Sym2.map p)) ∧ (M.image (Sym2.map p)).card = M.card := by
  classical
  obtain ⟨sub,noCross⟩ := induced_iff_endpoints.mp hm
  refine ⟨induced_iff_endpoints.mpr ⟨?_,?_⟩,?_⟩
  · intro f hf
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hf
    have valid := sub he
    induction e using Sym2.inductionOn with
    | _ a b =>
      simpa [edges] using (cover a b).mp (by simpa [edges] using valid)
  · intro e he f hf a ha b hb hab
    obtain ⟨e',em,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨f',fm,rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨x,xe,rfl⟩ := Sym2.mem_map.mp ha
    obtain ⟨y,yf,rfl⟩ := Sym2.mem_map.mp hb
    exact congrArg _ (noCross e' em f' fm x xe y yf ((cover x y).mpr hab))
  · apply Finset.card_image_of_injOn
    intro e he f hf eqn
    induction e using Sym2.inductionOn with
    | _ u v =>
      have uv : G.Adj u v := by simpa [edges] using sub he
      have pv : p v ∈ Sym2.map p f := eqn ▸ (Sym2.mem_map.mpr ⟨v,Sym2.mem_mk_right ..,rfl⟩)
      obtain ⟨w,wf,hw⟩ := Sym2.mem_map.mp pv
      apply noCross _ he f hf u (Sym2.mem_mk_left ..) w wf
      exact (cover u w).mpr (hw ▸ (cover u v).mp uv)

/-- An inclusion-minimal cover of B by neighborhoods of A gives a private
neighbor for each selected vertex, hence an induced matching of equal size. -/
theorem induced_bipartite_private_cover {n r : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (apart : Disjoint A B)
    (left : ∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v)
    (right : ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v)
    (live : ∀ v ∈ B, ∃ u ∈ A, G.Adj u v) (cap : ∀ u ∈ A, G.degree u ≤ r) :
    ∃ M, inducedMatching G M ∧ B.card ≤ r*M.card := by
  classical
  let Covers (S : Finset (Fin n)) := ∀ v ∈ B, ∃ u ∈ S, G.Adj u v
  let F := A.powerset.filter Covers
  have mem (S) : S ∈ F ↔ S ⊆ A ∧ Covers S := by simp [F]
  obtain ⟨S,hS,minS⟩ := F.exists_min_image Finset.card ⟨A,(mem _).mpr ⟨Finset.Subset.rfl,live⟩⟩
  obtain ⟨sub,cover⟩ := (mem S).mp hS
  have private_nbr (a : S) : ∃ v ∈ B, G.Adj a.val v ∧ ∀ u ∈ S, G.Adj u v → u = a.val := by
    have indispensable : ¬Covers (S.erase a.val) := by
      intro good
      have small := minS _ ((mem _).mpr ⟨(Finset.erase_subset _ _).trans sub,good⟩)
      exact (Finset.card_erase_lt_of_mem a.property).not_ge small
    change ¬ ∀ v ∈ B, ∃ u ∈ S.erase a.val, G.Adj u v at indispensable
    push Not at indispensable
    obtain ⟨v,vb,excl⟩ := indispensable
    have unique {u} (h : u ∈ S) (adj : G.Adj u v) : u = a.val := by
      by_contra hne
      exact excl u (Finset.mem_erase.mpr ⟨hne,h⟩) adj
    obtain ⟨u,hu,uv⟩ := cover v vb
    exact ⟨v,vb,(unique hu uv) ▸ uv,fun _ h adj => unique h adj⟩
  choose y yB reaches priv using private_nbr
  let edge (a : S) : Sym2 (Fin n) := s(a.val,y a)
  let M := Finset.univ.image edge
  have aA (a : S) : a.val ∈ A := sub a.property
  have sep := Finset.disjoint_left.mp apart
  have inj : Function.Injective edge := by
    intro a b he
    have hb : a.val ∈ edge b := he ▸ Sym2.mem_mk_left ..
    rcases Sym2.mem_iff.mp hb with eq|eq
    · exact Subtype.ext eq
    · exact (sep (aA a) (eq ▸ yB b)).elim
  have card : M.card = S.card := by simp [M,Finset.card_image_of_injective _ inj]
  have induced : inducedMatching G M := by
    apply induced_iff_endpoints.mpr
    constructor
    · intro e he
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp he
      simpa [edge,edges] using reaches a
    · intro e he f hf u ue v vf adj
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hf
      apply congrArg edge
      apply Subtype.ext
      rcases Sym2.mem_iff.mp ue with rfl|rfl <;> rcases Sym2.mem_iff.mp vf with rfl|rfl
      · exact (left _ (aA a) _ (aA b) adj).elim
      · exact priv b a.val a.property adj
      · exact (priv a b.val b.property adj.symm).symm
      · exact (right _ (yB a) _ (yB b) adj).elim
  have includes : B ⊆ S.biUnion (fun a => G.neighborFinset a) := by
    intro v hv
    obtain ⟨a,ha,adj⟩ := cover v hv
    exact Finset.mem_biUnion.mpr ⟨_,ha,(G.mem_neighborFinset a v).mpr adj⟩
  refine ⟨M,induced,?_⟩
  rw [card,Nat.mul_comm]
  apply (Finset.card_le_card includes).trans
  exact Finset.card_biUnion_le_card_mul _ _ _ (fun a ha => by simpa using cap a (sub ha))

theorem induced_bipartite_order {n d : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (apart : Disjoint A B)
    (left : ∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v)
    (right : ∀ u ∈ B, ∀ v ∈ B, ¬ G.Adj u v)
    (liveA : ∀ u ∈ A, ∃ v ∈ B, G.Adj v u)
    (liveB : ∀ v ∈ B, ∃ u ∈ A, G.Adj u v) (cap : ∀ v, G.degree v ≤ d) :
    ∃ M, inducedMatching G M ∧ A.card+B.card ≤ 2*d*M.card := by
  by_cases h : A.card ≤ B.card
  · obtain ⟨M,hm,cert⟩ := induced_bipartite_private_cover G A B apart left right liveB (fun u _ => cap u)
    exact ⟨M,hm,by nlinarith only [h,cert]⟩
  · obtain ⟨M,hm,cert⟩ := induced_bipartite_private_cover G B A apart.symm right left liveA (fun u _ => cap u)
    exact ⟨M,hm,by nlinarith only [Nat.le_of_not_ge h,cert]⟩

/-- Deleting t vertices to make a regular graph bipartite leaves an
induced matching M with n ≤ 2d|M| + 2t. -/
theorem bipartite_deletion_bound {n d : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pos : 0 < d) (reg : ∀ v, G.degree v = d)
    (A B : Finset (Fin n)) (apart : Disjoint A B)
    (left : G.IsIndepSet (A : Set (Fin n))) (right : G.IsIndepSet (B : Set (Fin n))) :
    ∃ M, inducedMatching G M ∧ n ≤ 2*d*M.card + 2*(A ∪ B)ᶜ.card := by
  classical
  let S := A ∪ B
  let L := S.filter (fun v => ∃ u ∈ S, G.Adj u v)
  let I := S \ L
  let X := Sᶜ
  have live (v) : v ∈ L ↔ v ∈ S ∧ ∃ u ∈ S, G.Adj u v := Finset.mem_filter
  have outside {u v} (hu : u ∈ I) (adj : G.Adj u v) : v ∈ X := by
    obtain ⟨hs,hl⟩ := Finset.mem_sdiff.mp hu
    exact Finset.mem_compl.mpr (fun hv => hl ((live u).mpr ⟨hs,v,hv,adj.symm⟩))
  have many (u) (hu : u ∈ I) : d ≤ (X.bipartiteAbove G.Adj u).card := by
    have eq : X.bipartiteAbove G.Adj u = G.neighborFinset u := by
      ext v
      simp only [Finset.mem_bipartiteAbove,G.mem_neighborFinset]
      exact ⟨And.right,fun h => ⟨outside hu h,h⟩⟩
    simp [eq,reg]
  have few (v) (_ : v ∈ X) : (I.bipartiteBelow G.Adj v).card ≤ d := by
    have sub : I.bipartiteBelow G.Adj v ⊆ G.neighborFinset v := by
      intro u hu
      exact (G.mem_neighborFinset v u).mpr (Finset.mem_filter.mp hu).2.symm
    simpa [reg] using Finset.card_le_card sub
  have isolated := Nat.le_of_mul_le_mul_right (Finset.card_mul_le_card_mul G.Adj many few) pos
  have left' {u v} (hu : u ∈ A) (hv : v ∈ A) (h : G.Adj u v) : False :=
    (G.isIndepSet_iff.mp left) hu hv h.ne h
  have right' {u v} (hu : u ∈ B) (hv : v ∈ B) (h : G.Adj u v) : False :=
    (G.isIndepSet_iff.mp right) hu hv h.ne h
  have partner {u v} (hu : u ∈ S) (hv : v ∈ L) (adj : G.Adj u v) : u ∈ L :=
    (live _).mpr ⟨hu,v,((live _).mp hv).1,adj.symm⟩
  have inA (v) (hv : v ∈ B ∩ L) : ∃ u ∈ A ∩ L, G.Adj u v := by
    obtain ⟨hb,hl⟩ := Finset.mem_inter.mp hv
    obtain ⟨_,u,hu,adj⟩ := (live _).mp hl
    exact ⟨u,Finset.mem_inter.mpr ⟨(Finset.mem_union.mp hu).resolve_right
      (fun h => right' h hb adj),partner hu hl adj⟩,adj⟩
  have inB (u) (hu : u ∈ A ∩ L) : ∃ v ∈ B ∩ L, G.Adj v u := by
    obtain ⟨ha,hl⟩ := Finset.mem_inter.mp hu
    obtain ⟨_,v,hv,adj⟩ := (live _).mp hl
    exact ⟨v,Finset.mem_inter.mpr ⟨(Finset.mem_union.mp hv).resolve_left
      (fun h => left' h ha adj),partner hv hl adj⟩,adj⟩
  have sep : Disjoint (A ∩ L) (B ∩ L) :=
    apart.mono (Finset.inter_subset_left) (Finset.inter_subset_left)
  obtain ⟨M,hm,bound⟩ := induced_bipartite_order G (A ∩ L) (B ∩ L) sep
    (fun _ hu _ hv => left' (Finset.mem_inter.mp hu).1 (Finset.mem_inter.mp hv).1)
    (fun _ hu _ hv => right' (Finset.mem_inter.mp hu).1 (Finset.mem_inter.mp hv).1)
    inB inA (fun v => (reg v).le)
  have split : (A ∩ L) ∪ (B ∩ L) = L := by
    rw [← Finset.union_inter_distrib_right]
    exact Finset.inter_eq_right.mpr (Finset.filter_subset ..)
  have active := Finset.card_union_of_disjoint sep
  rw [split] at active
  have sizes : I.card + L.card = S.card := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset ..)
  have total : X.card + S.card = n := by simp [X]
  exact ⟨M,hm,by change n ≤ 2*d*M.card+2*X.card; omega⟩

private theorem touches_right {n} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n))
    (cross : ∀ u v, G.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A))
    (e) (he : e ∈ edges G) : ∃ b ∈ B, b ∈ e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    rcases cross u v (by simpa [edges] using he) with h|h
    · exact ⟨v,h.2,Sym2.mem_mk_right ..⟩
    · exact ⟨u,h.1,Sym2.mem_mk_left ..⟩

/-- A low-degree side controls the LP gap even when the block sizes vary. -/
theorem bipartite_side_gap {n r} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (apart : Disjoint A B)
    (cross : ∀ u v, G.Adj u v → (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A))
    (live : ∀ v ∈ B, ∃ u ∈ A, G.Adj u v) (cap : ∀ u ∈ A, G.degree u ≤ r)
    (x) (hx : feasible G x) :
    ∃ M, inducedMatching G M ∧ (∑ e ∈ edges G, x e) ≤ (r:ℝ)*M.card := by
  classical
  obtain ⟨M,hm,bound⟩ := induced_bipartite_private_cover G A B apart
    (fun u hu v hv adj => (cross u v adj).elim
      (fun q => Finset.disjoint_left.mp apart hv q.2) (fun q => Finset.disjoint_left.mp apart hu q.1))
    (fun u hu v hv adj => (cross u v adj).elim
      (fun q => Finset.disjoint_left.mp apart q.1 hu) (fun q => Finset.disjoint_left.mp apart q.2 hv))
    live cap
  refine ⟨M,hm,le_trans ?_ (by exact_mod_cast bound : (B.card:ℝ) ≤ (r:ℝ)*M.card)⟩
  have load (b) (hb : b ∈ B) : ∑ e ∈ G.incidenceFinset b, x e ≤ 1 := by
    obtain ⟨a,_,adj⟩ := live b hb
    have sub : G.incidenceFinset b ⊆ incidentBlock G s(b,a) := by
      intro f hf
      rw [G.incidenceFinset_eq_filter] at hf
      obtain ⟨ef,bf⟩ := Finset.mem_filter.mp hf
      exact Finset.mem_filter.mpr ⟨by simpa [edges] using ef,
        Finset.nonempty_iff_ne_empty.mp ⟨b,Finset.mem_inter.mpr
          ⟨Sym2.mem_toFinset.mpr (Sym2.mem_mk_left ..),Sym2.mem_toFinset.mpr bf⟩⟩⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg sub
      (fun e he _ => hx.1 _ (Finset.mem_filter.mp he).1)).trans
      (hx.2 _ (by simpa [edges] using adj.symm))
  calc
    _ ≤ ∑ e ∈ edges G, ∑ b ∈ B, if b ∈ e then x e else 0 := by
      apply Finset.sum_le_sum
      intro e he
      obtain ⟨b,hb,be⟩ := touches_right G A B cross e he
      have nn (v) (_ : v ∈ B) : 0 ≤ (if v ∈ e then x e else 0) := by
        split <;> simp_all [hx.1 e he]
      simpa only [if_pos be] using Finset.single_le_sum nn hb
    _ = ∑ b ∈ B, ∑ e ∈ edges G, if b ∈ e then x e else 0 := Finset.sum_comm
    _ ≤ ∑ _b ∈ B,(1:ℝ) := by
      apply Finset.sum_le_sum
      intro b hb
      have star : (edges G).filter (fun e => b ∈ e) = G.incidenceFinset b := by
        ext e
        simp [G.incidenceFinset_eq_filter,edges]
      rw [← Finset.sum_filter,star]
      exact load b hb
    _ = _ := by simp

theorem single_edge_density {n d : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pos : 0 < d) (reg : ∀ v, G.degree v = d) (small : 2*n ≤ 5*d) :
    ∃ M, inducedMatching G M ∧ 2*n ≤ 5*d*M.card := by
  classical
  by_cases hz : n = 0
  · exact ⟨∅,by simp [inducedMatching],by simp [hz]⟩
  let v : Fin n := ⟨0,Nat.pos_of_ne_zero hz⟩
  obtain ⟨u,adj⟩ := (G.degree_pos_iff_exists_adj v).mp (by simpa [reg] using pos)
  have edge : s(v,u) ∈ edges G := by simpa [edges] using adj
  refine ⟨{s(v,u)},induced_iff_endpoints.mpr ⟨by simpa using edge,?_⟩,by simpa using small⟩
  intros e he f hf a ha b hb _
  exact (Finset.mem_singleton.mp he).trans (Finset.mem_singleton.mp hf).symm

theorem near_bipartite_density {n d : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pos : 0 < d) (reg : ∀ v, G.degree v = d)
    (A B : Finset (Fin n)) (apart : Disjoint A B)
    (left : G.IsIndepSet (A : Set (Fin n))) (right : G.IsIndepSet (B : Set (Fin n)))
    (nearby : 10*(A ∪ B)ᶜ.card ≤ n) :
    ∃ M, inducedMatching G M ∧ 2*n ≤ 5*d*M.card := by
  obtain ⟨M,hm,h⟩ := bipartite_deletion_bound G pos reg A B apart left right
  exact ⟨M,hm,by nlinarith only [h,nearby]⟩

theorem low_side_gap {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (part : G.IsBipartiteWith A B)
    (low : ∀ u ∈ A, 8*G.degree u ≤ 5*degreeBound G) (x) (hx : feasible G x) :
    ∃ M, inducedMatching G M ∧
      (∑ e ∈ edges G, x e) ≤ ((5/8 : ℝ)*degreeBound G)*M.card := by
  classical
  let T := B.filter (fun v => 0 < G.degree v)
  have live {u v} (h : G.Adj u v) (hv : v ∈ B) : v ∈ T :=
    Finset.mem_filter.mpr ⟨hv,(G.degree_pos_iff_exists_adj _).mpr ⟨u,h.symm⟩⟩
  have cross (u v) (h : G.Adj u v) :
      (u ∈ A ∧ v ∈ T) ∨ (u ∈ T ∧ v ∈ A) := by
    rcases part.mem_of_adj h with q|q
    · exact Or.inl ⟨q.1,live h q.2⟩
    · exact Or.inr ⟨live h.symm q.1,q.2⟩
  have partner (v) (hv : v ∈ T) : ∃ u ∈ A, G.Adj u v := by
    obtain ⟨hb,hp⟩ := Finset.mem_filter.mp hv
    obtain ⟨u,adj⟩ := (G.degree_pos_iff_exists_adj v).mp hp
    exact ⟨u,part.symm.mem_of_mem_adj hb adj,adj.symm⟩
  let r := (5*degreeBound G)/8
  have cap (u) (hu : u ∈ A) : G.degree u ≤ r := by
    dsimp [r]
    exact (Nat.le_div_iff_mul_le (by decide)).mpr (by simpa [Nat.mul_comm] using low u hu)
  have apart : Disjoint A T := by
    apply Finset.disjoint_left.mpr
    intro v ha ht
    exact Set.disjoint_left.mp part.disjoint ha (Finset.mem_filter.mp ht).1
  obtain ⟨M,hm,bound⟩ := bipartite_side_gap G A T apart cross partner cap x hx
  have coeff : r*8 ≤ 5*degreeBound G := Nat.div_mul_le_self .. 
  have realcoeff : (r:ℝ)*8 ≤ 5*(degreeBound G:ℝ) := by exact_mod_cast coeff
  refine ⟨M,hm,bound.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))⟩
  linarith

private theorem regular_from_remaining (density : H1) (n d : ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (pos : 0 < d) (reg : ∀ v, G.degree v = d) :
    ∃ M, inducedMatching G M ∧ 2*n ≤ 5*d*M.card := by
  classical
  by_cases dense : 2*n ≤ 5*d
  · exact single_edge_density G pos reg dense
  by_cases far : ∀ A B : Finset (Fin n), Disjoint A B → G.IsIndepSet A → G.IsIndepSet B →
      n < 10*(A ∪ B)ᶜ.card
  · exact density n d G pos reg (by omega) far
  · push Not at far
    obtain ⟨A,B,sep,hA,hB,nearby⟩ := far
    exact near_bipartite_density G pos reg A B sep hA hB nearby

/-- If every surviving clone sees total neighboring multiplicity R, the
regular-graph density estimate transfers to the original graph. Zero fibers
are allowed, including isolated vertices. -/
theorem weighted_regular_transfer
    (density : H1)
    {n R : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (w : Fin n → ℕ)
    (pos : 0 < R) (rows : ∀ v, 0 < w v → ∑ u : G.neighborSet v, w u.val = R) :
    ∃ M, inducedMatching G M ∧ 2*(∑ v, w v) ≤ 5*R*M.card := by
  classical
  let V := Σ v : Fin n, Fin (w v)
  let N := Fintype.card V
  let code : V ≃ Fin N := Fintype.equivFin V
  let p (v : Fin N) : Fin n := (code.symm v).1
  let H := G.comap p
  have reg (v : Fin N) : H.degree v = R := by
    let iso : H.neighborSet v ≃ (Σ u : G.neighborSet (p v), Fin (w u.val)) := {
      toFun := fun z => ⟨⟨p z.val,z.property⟩,(code.symm z.val).2⟩
      invFun := fun z => ⟨code ⟨z.1.val,z.2⟩, by
        change G.Adj (p v) ((code.symm (code ⟨z.1.val,z.2⟩)).1)
        rw [code.symm_apply_apply]
        exact z.1.property⟩
      left_inv := fun z => Subtype.ext (code.apply_symm_apply z.val)
      right_inv := by
        rintro ⟨⟨z,hz⟩,i⟩
        simp [p]
        exact (Sigma.ext_iff.mp (code.symm_apply_apply (⟨z,i⟩ : V))).2
    }
    have eq := Fintype.card_congr iso
    simp only [Fintype.card_sigma,Fintype.card_fin,SimpleGraph.card_neighborSet_eq_degree] at eq
    exact eq.trans (rows _ (Nat.zero_lt_of_lt (code.symm v).2.isLt))
  obtain ⟨M,hm,cert⟩ := regular_from_remaining density N R H pos reg
  obtain ⟨inside,size⟩ := project_induced_matching p (fun _ _ => Iff.rfl) M hm
  refine ⟨_,inside,?_⟩
  rw [size]
  have order : N = ∑ v, w v := by simp [N,V,Fintype.card_sigma]
  simpa only [order] using cert

theorem incident_card_succ {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {a b} (adj : G.Adj a b) :
    (incidentBlock G s(a,b)).card + 1 = G.degree a + G.degree b := by
  classical
  have row : incidentBlock G s(a,b) = G.incidenceFinset a ∪ G.incidenceFinset b := by
    ext f
    simp only [incidentBlock, edges, Finset.mem_filter, ← Finset.nonempty_iff_ne_empty,
      Finset.Nonempty, Finset.mem_inter, Sym2.mem_toFinset, Sym2.mem_iff, Finset.mem_union,
      G.incidenceFinset_eq_filter, SimpleGraph.mem_edgeFinset]
    grind
  have common : G.incidenceFinset a ∩ G.incidenceFinset b = {s(a,b)} := by
    ext f
    simp only [G.incidenceFinset_eq_filter, Finset.mem_inter, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro h
      exact (Sym2.mem_and_mem_iff adj.ne).mp ⟨h.1.2,h.2.2⟩
    · rintro rfl
      have edge : s(a,b) ∈ G.edgeFinset := by simpa using adj
      exact ⟨⟨edge,Sym2.mem_mk_left ..⟩,⟨edge,Sym2.mem_mk_right ..⟩⟩
  have tot := Finset.card_union_add_card_inter (G.incidenceFinset a) (G.incidenceFinset b)
  simpa only [row,common,Finset.card_singleton,G.card_incidenceFinset_eq_degree] using tot

/-- Constant edge incidence width reduces to ordinary regular graphs, even
with isolated vertices and components of distinct degree pairs. -/
theorem width_of_regular
    (density : H1)
    {n k : ℕ} (G : SimpleGraph (Fin n))
    (width : ∀ e ∈ edges G, (incidentBlock G e).card = k) :
    ∃ M, inducedMatching G M ∧ 8*(edges G).card ≤ 5*degreeBound G*(k+1)*M.card := by
  classical
  let R := n.factorial
  let w (v : Fin n) := if G.degree v = 0 then 0 else R / (k+1-G.degree v)
  have adjSum {u v : Fin n} (h : G.Adj u v) : G.degree u + G.degree v = k+1 := by
    rw [← incident_card_succ G h,width _ (by simpa [edges] using h)]
  have divisor (v : Fin n) (h : 0 < G.degree v) : G.degree v ∣ R :=
    Nat.dvd_factorial h (by simpa using (G.degree_lt_card_verts v).le)
  have weight {u v : Fin n} (adj : G.Adj u v) : w u = R / G.degree v := by
    have hu := (G.degree_pos_iff_exists_adj u).mpr ⟨v,adj⟩
    have eq := adjSum adj
    simp [w,hu.ne',show k+1-G.degree u = G.degree v by omega]
  have rows (v) (hv : 0 < w v) : ∑ u : G.neighborSet v, w u.val = R := by
    have pos : 0 < G.degree v := by by_contra! hz; simp [w, Nat.eq_zero_of_le_zero hz] at hv
    have fixed (u : G.neighborSet v) : w u.val = R / G.degree v := weight u.property.symm
    simp only [fixed,Finset.sum_const,Finset.card_univ,SimpleGraph.card_neighborSet_eq_degree,nsmul_eq_mul]
    exact Nat.mul_div_cancel' (divisor v pos)
  obtain ⟨M,hm,limit⟩ := weighted_regular_transfer density G w (Nat.factorial_pos n) rows
  have vertex (v : Fin n) : 2*R*G.degree v ≤ (degreeBound G*(k+1))*w v := by
    by_cases zero : G.degree v = 0
    · simp [zero]
    obtain ⟨u,adj⟩ := (G.degree_pos_iff_exists_adj v).mp (Nat.pos_of_ne_zero zero)
    have prod : G.degree u * w v = R := by
      rw [weight adj]
      exact Nat.mul_div_cancel' (divisor u ((G.degree_pos_iff_exists_adj u).mpr ⟨v,adj.symm⟩))
    have du : G.degree u ≤ degreeBound G := by simpa [degreeBound] using G.degree_le_maxDegree u
    have dv : G.degree v ≤ degreeBound G := by simpa [degreeBound] using G.degree_le_maxDegree v
    have ab : 2*G.degree v*G.degree u ≤ degreeBound G*(k+1) := by
      rw [← adjSum adj]
      nlinarith only [Nat.mul_le_mul_right (G.degree v) du,Nat.mul_le_mul_right (G.degree u) dv]
    calc 2*R*G.degree v = (2*G.degree v*G.degree u)*w v := by rw [← prod]; ring
         _ ≤ _ := Nat.mul_le_mul_right _ ab
  have total := Finset.sum_le_sum (s := Finset.univ) (fun v _ => vertex v)
  rw [← Finset.mul_sum, ← Finset.mul_sum] at total
  have hand := G.sum_degrees_eq_twice_card_edges
  have ed : edges G = G.edgeFinset := by ext; simp [edges]
  rw [← ed] at hand
  rw [hand] at total
  refine ⟨M,hm,Nat.le_of_mul_le_mul_right ?_ (Nat.factorial_pos n)⟩
  nlinarith only [total,Nat.mul_le_mul_left (degreeBound G*(k+1)) limit]

private theorem constant_width_gap (density : H1) {n k} {G : SimpleGraph (Fin n)}
    (nonempty : (edges G).Nonempty) (width : ∀ e ∈ edges G, (incidentBlock G e).card = k)
    (x) (hx : feasible G x) : ∃ M, inducedMatching G M ∧
    (∑ e ∈ edges G, x e) ≤ ((5/8 : ℝ)*degreeBound G + 5/8)*M.card := by
  obtain ⟨M,hm,cert⟩ := width_of_regular density G width
  refine ⟨M,hm,?_⟩
  have den : (0:ℝ) < k := by exact_mod_cast width_positive nonempty width
  have degree : (degreeBound G : ℝ) ≤ k := by exact_mod_cast degree_le_width G width
  have cert' : 8*((edges G).card:ℝ) ≤ 5*degreeBound G*((k:ℝ)+1)*M.card := by exact_mod_cast cert
  apply le_of_mul_le_mul_left (a := (k:ℝ)) _ den
  nlinarith only [width_bound width x hx,cert',mul_le_mul_of_nonneg_right degree (Nat.cast_nonneg (α := ℝ) M.card)]

theorem main : H1 → H2 → H3 → type_of% @OMA.S_arxiv_1812_05930.main := by
  classical
  rintro density ⟨C,hC,mixed⟩ ⟨D,alg,_,hpoly,algorithm⟩
  let B := max (max C D) (5/8 : ℝ)
  have cB : C ≤ B := (le_max_left C D).trans (le_max_left ..)
  have dB : D ≤ B := (le_max_right C D).trans (le_max_left ..)
  have small : (5/8 : ℝ) ≤ B := le_max_right .. 
  refine ⟨B,alg,hC.trans cB,hpoly,?_⟩
  intro n G
  dsimp only
  have grow (z : ℝ) (hz : z ≤ B) (k : ℕ) :
      ((5/8 : ℝ)*degreeBound G+z)*k ≤ ((5/8 : ℝ)*degreeBound G+B)*k :=
    mul_le_mul_of_nonneg_right (add_le_add_right hz _) (Nat.cast_nonneg _)
  constructor
  · intro x hx
    by_cases nonempty : (edges G).Nonempty
    · obtain ⟨e,he⟩ := nonempty
      by_cases width : ∀ f ∈ edges G, (incidentBlock G f).card = (incidentBlock G e).card
      · obtain ⟨M,hm,bound⟩ := constant_width_gap density ⟨e,he⟩ width x hx
        exact ⟨M,hm,bound.trans (grow _ small _)⟩
      · push Not at width
        obtain ⟨f,hf,diff⟩ := width
        by_cases hard : ∀ A T : Finset (Fin n), G.IsBipartiteWith A T →
            ∃ u ∈ A, 5*degreeBound G < 8*G.degree u
        · obtain ⟨M,hm,bound⟩ := mixed n G ⟨f,hf,e,he,diff⟩ hard x hx
          exact ⟨M,hm,bound.trans (grow _ cB _)⟩
        · push Not at hard
          obtain ⟨A,T,part,low⟩ := hard
          obtain ⟨M,hm,bound⟩ := low_side_gap G A T part low x hx
          exact ⟨M,hm,bound.trans (by simpa using grow 0 (hC.trans cB) M.card)⟩
    · have empty := Finset.not_nonempty_iff_eq_empty.mp nonempty
      exact ⟨∅,by simp [inducedMatching,empty],by simp [empty]⟩
  · obtain ⟨M,hm,out,opt⟩ := algorithm n G
    exact ⟨M,hm,out,fun N hn => (opt N hn).trans (grow _ dB _)⟩

end OMA.R_arxiv_1812_05930_R1
