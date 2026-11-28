import OMAReductions.R_Erdos595_erdos_595_R2
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Filter.Ultrafilter.Defs
import Mathlib.SetTheory.Cardinal.Continuum

-- Credit: @wispiANt
namespace OMA.R_Erdos595_erdos_595_R2_H1_R1

open SimpleGraph Filter

/-- In a product of finite edge sets, call a triple a triangle if it is a
triangle at every coordinate beyond some finite set. Seek a product in
which every countable colouring makes one of these triangles monochromatic. -/
def H1 : Prop :=
  ∃ (I : Type) (n : Finset I → ℕ) (G : (s : Finset I) → SimpleGraph (Fin (n s))),
    (∀ s, (G s).CliqueFree 4) ∧
    ∀ d : ((s : Finset I) → (G s).edgeSet) → ℕ,
      ∃ a b c, d a = d b ∧ d a = d c ∧ ∀ᶠ s in (atTop : Filter (Finset I)),
        ∃ x y z : Fin (n s), (a s : Sym2 _) = s(x,y) ∧
          (b s : Sym2 _) = s(y,z) ∧ (c s : Sym2 _) = s(z,x)

/-- Every finite family of eventual triangle constraints in a product
admits a single evaluation preserving all the constraints at once. -/
def H2 : Prop :=
  ∀ (I X : Type) (P : Finset I → X → X → X → Prop) (S : Finset X),
    ∃ s : Finset I, ∀ a b c : S,
      (∀ᶠ t in (atTop : Filter (Finset I)), P t a b c) → P s a b c

theorem common_coordinate : H2 := by
  classical
  intro I X P S
  apply Filter.Eventually.exists (f := (atTop : Filter (Finset I)))
  apply eventually_all.mpr
  intro a
  apply eventually_all.mpr
  intro b
  apply eventually_all.mpr
  intro c
  by_cases h : ∀ᶠ t in (atTop : Filter (Finset I)), P t a b c
  · exact h.mono fun _ hp _ => hp
  · exact .of_forall fun _ hf => (h hf).elim

theorem main : H1 → H2 → OMA.R_Erdos595_erdos_595_R2.H1 := by
  classical
  rintro ⟨I,n,G,free,hard⟩ simultaneous
  let X := (s : Finset I) → (G s).edgeSet
  let P := fun (s : Finset I) (a b c : X) =>
    ∃ x y z : Fin (n s), (a s : Sym2 _) = s(x,y) ∧ (b s : Sym2 _) = s(y,z) ∧
      (c s : Sym2 _) = s(z,x)
  let T := fun a b c => ∀ᶠ s in (atTop : Filter (Finset I)), P s a b c
  refine ⟨X,T,?_,?_⟩
  · intro d
    obtain ⟨a,b,c,e,f,t⟩ := hard d
    exact ⟨a,b,c,t,e,f⟩
  · intro S
    obtain ⟨s,hs⟩ := simultaneous I X P S
    exact ⟨n s,G s,free s,fun a => a.val s,hs⟩

/-- Anchor every finite realization at one label to obtain a default edge.
Each label is eventually present, so all its triangle constraints survive. -/
theorem from_finite_realizations : OMA.R_Erdos595_erdos_595_R2.H1 → H1 := by
  classical
  rintro ⟨X,T,hard,localize⟩
  obtain ⟨anchor,_,_,_⟩ := hard (fun _ => 0)
  choose n G free e realizes using fun s : Finset X => localize (insert anchor s)
  let label (a : X) (s : Finset X) : (G s).edgeSet :=
    e s (if h : a ∈ insert anchor s then ⟨a,h⟩ else ⟨anchor,Finset.mem_insert_self _ _⟩)
  refine ⟨X,n,G,free,?_⟩
  intro d
  obtain ⟨a,b,c,t,ab,ac⟩ := hard fun x => d (label x)
  refine ⟨label a,label b,label c,ab,ac,?_⟩
  filter_upwards [Filter.eventually_finset_mem_atTop a, Filter.eventually_finset_mem_atTop b,
    Filter.eventually_finset_mem_atTop c] with s ha hb hc
  have ua := Finset.mem_insert_of_mem (b := anchor) ha
  have ub := Finset.mem_insert_of_mem (b := anchor) hb
  have uc := Finset.mem_insert_of_mem (b := anchor) hc
  simpa only [label,dif_pos ua,dif_pos ub,dif_pos uc] using
    realizes s ⟨a,ua⟩ ⟨b,ub⟩ ⟨c,uc⟩ t

/-- Uniformly bounded palettes on even a cofinal selection of factors colour
the eventual product. Consequently, in a hard product, for every fixed k
all sufficiently late factors already force a monochromatic k-colour test. -/
theorem bounded_palette {I : Type} {A : Finset I → Type}
    (R : (s : Finset I) → A s → A s → A s → Prop) (k : ℕ)
    (cofinal : ∀ t : Finset I, ∃ s, t ⊆ s ∧ ∃ p : A s → Fin k,
      ∀ a b c, R s a b c → p a = p b → p a = p c → False) :
    ∃ d : ((s : Finset I) → A s) → Fin k, ∀ a b c,
      (∀ᶠ s in (atTop : Filter (Finset I)), R s (a s) (b s) (c s)) →
      d a = d b → d a = d c → False := by
  classical
  choose next ext p good using cofinal
  let U := Ultrafilter.of (atTop : Filter (Finset I))
  have pick (a : (s : Finset I) → A s) :
      ∃ i : Fin k, ∀ᶠ t : Finset I in U, p t (a (next t)) = i := by
    by_contra! h
    obtain ⟨t,miss⟩ := (eventually_all.mpr h).exists
    exact miss _ rfl
  choose d selected using pick
  refine ⟨d,?_⟩
  intro a b c tri ab ac
  obtain ⟨base,tail⟩ := Filter.eventually_atTop.mp tri
  have late : ∀ᶠ t : Finset I in U, base ≤ t :=
    Ultrafilter.of_le _ (Filter.eventually_ge_atTop base)
  obtain ⟨t,ht,ha,hb,hc⟩ := (late.and ((selected a).and ((selected b).and (selected c)))).exists
  exact good t _ _ _ (tail _ (ht.trans (ext t)))
    (ha.trans (ab.trans hb.symm)) (ha.trans (ac.trans hc.symm))


private theorem free_of_top_hom {V : Type} {G : SimpleGraph V} (free : G.CliqueFree 4)
    (f : Fin 4 → V) (edges : ∀ i j, i ≠ j → G.Adj (f i) (f j)) : False := by
  let hom : completeGraph (Fin 4) →g G := ⟨f,fun {i j} h => edges i j h⟩
  have inj : Function.Injective f := fun i j eq => by
    by_contra ne
    exact (edges i j ne).ne eq
  exact (cliqueFree_iff.mp free).false (hom.toCopy inj)

/-- One finite universal host for each size: take the disjoint union of
all four-clique-free graphs on the prescribed number of vertices. -/
theorem universal_factors_with_positions :
    ∃ (u : ℕ → ℕ) (U : (m : ℕ) → SimpleGraph (Fin (u m))),
      (∀ m, (U m).CliqueFree 4) ∧ (∀ m (K : SimpleGraph (Fin (2*(m+1)))),
        K.CliqueFree 4 → Nonempty (K ↪g U m)) ∧
      ∀ m, ∃ (tag : Fin (u m) → {K : SimpleGraph (Fin (2*(m+1))) // K.CliqueFree 4})
        (pos : Fin (u m) → Fin (2*(m+1))), ∀ x y, (U m).Adj x y →
          tag x = tag y ∧ (tag x).val.Adj (pos x) (pos y) := by
  classical
  suffices h : ∀ m : ℕ, ∃ (n : ℕ) (G : SimpleGraph (Fin n)), G.CliqueFree 4 ∧
      (∀ K : SimpleGraph (Fin (2*(m+1))), K.CliqueFree 4 → Nonempty (K ↪g G)) ∧
      ∃ (tag : Fin n → {K : SimpleGraph (Fin (2*(m+1))) // K.CliqueFree 4})
        (pos : Fin n → Fin (2*(m+1))), ∀ x y, G.Adj x y →
          tag x = tag y ∧ (tag x).val.Adj (pos x) (pos y) by
    choose u U free inc labels using h
    exact ⟨u,U,free,inc,labels⟩
  intro m
  let B := Fin (2*(m+1))
  let W := {K : SimpleGraph B // K.CliqueFree 4} × B
  let num := Fintype.equivFin W
  let G : SimpleGraph W := {
    Adj := fun a b => a.1 = b.1 ∧ a.1.val.Adj a.2 b.2
    symm := ⟨fun {a b} e => ⟨e.1.symm,e.1 ▸ e.2.symm⟩⟩
    loopless := ⟨fun _ e => e.2.ne rfl⟩ }
  refine ⟨_, G.comap num.symm,?_,?_,?_⟩
  · rw [cliqueFree_iff,isEmpty_iff]
    intro copy
    let v (i : Fin 4) : W := num.symm (copy i)
    have adj (i j : Fin 4) (ne : i ≠ j) : G.Adj (v i) (v j) := copy.toHom.map_adj ne
    have tag (i : Fin 4) : (v 0).1 = (v i).1 := by
      by_cases eq : 0 = i
      · rw [eq]
      · exact (adj _ _ eq).1
    apply free_of_top_hom (v 0).1.property (fun i => (v i).2)
    intro i j ne
    rw [tag i]
    exact (adj i j ne).2
  · intro K free
    let add (i : B) : W := (⟨K,free⟩,i)
    refine ⟨{ toFun := fun i => num (add i)
              inj' := fun i j eq => congrArg Prod.snd (num.injective eq)
              map_rel_iff' := ?_ }⟩
    intro i j
    change G.Adj (num.symm (num (add i))) (num.symm (num (add j))) ↔ K.Adj i j
    simp [G,add]

  · exact ⟨fun x => (num.symm x).1,fun x => (num.symm x).2,fun _ _ h => h⟩

/-- One finite universal host for each size: take the disjoint union of
all four-clique-free graphs on the prescribed number of vertices. -/
theorem universal_factors :
    ∃ (u : ℕ → ℕ) (U : (m : ℕ) → SimpleGraph (Fin (u m))),
      (∀ m, (U m).CliqueFree 4) ∧ ∀ m (K : SimpleGraph (Fin (2*(m+1)))),
        K.CliqueFree 4 → Nonempty (K ↪g U m) := by
  obtain ⟨u,U,free,inc,_⟩ := universal_factors_with_positions
  exact ⟨u,U,free,inc⟩

/-- Any such fixed family works if the finite-realization step holds.
Only the index set varies. At a coordinate of size m at most m+1 labels
(including a default edge) contribute endpoints. -/
theorem fixed_factors_iff (u : ℕ → ℕ) (U : (m : ℕ) → SimpleGraph (Fin (u m)))
    (free : ∀ m, (U m).CliqueFree 4)
    (inc : ∀ m (K : SimpleGraph (Fin (2*(m+1)))), K.CliqueFree 4 → Nonempty (K ↪g U m)) :
    OMA.R_Erdos595_erdos_595_R2.H1 ↔
      ∃ I : Type, ∀ d : ((s : Finset I) → (U s.card).edgeSet) → ℕ,
        ∃ a b c, d a = d b ∧ d a = d c ∧ ∀ᶠ s in (atTop : Filter (Finset I)),
          ∃ x y z : Fin (u s.card), (a s : Sym2 _) = s(x,y) ∧
            (b s : Sym2 _) = s(y,z) ∧ (c s : Sym2 _) = s(z,x) := by
  classical
  constructor
  · rintro ⟨X,T,hard,localize⟩
    obtain ⟨anchor,_,_,_⟩ := hard (fun _ => 0)
    have atSize (s : Finset X) :
        ∃ e : ↥(insert anchor s : Finset X) → (U s.card).edgeSet,
          ∀ a b c, T a.val b.val c.val →
            ∃ x y z : Fin (u s.card), (e a : Sym2 (Fin (u s.card))) = s(x,y) ∧ (e b : Sym2 (Fin (u s.card))) = s(y,z) ∧ (e c : Sym2 (Fin (u s.card))) = s(z,x) := by
      let L := insert anchor s
      obtain ⟨n,G,legal,e,test⟩ := localize L
      let B := Fin (2*(s.card+1))
      have size : Fintype.card (↥L × Bool) ≤ Fintype.card B := by
        simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_coe,Fintype.card_fin,B]
        have := Finset.card_insert_le anchor s
        dsimp [L]
        omega
      obtain ⟨slot⟩ := Function.Embedding.nonempty_of_card_le size
      let endpoint (p : ↥L × Bool) := if p.2 then (e p.1).val.out.2 else (e p.1).val.out.1
      let : Nonempty (↥L × Bool) := ⟨⟨⟨anchor,Finset.mem_insert_self _ _⟩,false⟩⟩
      let pt (b : B) := endpoint (Function.invFun slot b)
      have hit (p : ↥L × Bool) : pt (slot p) = endpoint p :=
        congrArg endpoint (Function.leftInverse_invFun slot.injective p)
      let code (i : Fin n) : B := if h : ∃ b, pt b = i then h.choose else 0
      have decode (p : ↥L × Bool) : pt (code (endpoint p)) = endpoint p := by
        have h : ∃ b, pt b = endpoint p := ⟨_,hit p⟩
        simpa only [code,dif_pos h] using h.choose_spec
      let K := G.comap pt
      have kfree : K.CliqueFree 4 := by
        rw [cliqueFree_iff,isEmpty_iff]
        intro f
        exact free_of_top_hom legal (fun i => pt (f i)) (fun _ _ ne => f.toHom.map_adj ne)
      let embed := (inc s.card K kfree).some
      let v := fun i => embed (code i)
      have edge (a : ↥L) : Sym2.map v (e a).val ∈ (U s.card).edgeSet := by
        let r := (e a).val.out
        have eq : s(r.1,r.2) = (e a).val := (e a).val.out_eq
        rw [← eq]
        apply embed.map_rel_iff.mpr
        change G.Adj (pt (code r.1)) (pt (code r.2))
        rw [show pt (code r.1) = r.1 from decode (a,false),
            show pt (code r.2) = r.2 from decode (a,true), ← SimpleGraph.mem_edgeSet,eq]
        exact (e a).property
      refine ⟨fun a => ⟨_,edge a⟩,?_⟩
      intro a b c h
      obtain ⟨x,y,z,ab,bc,ca⟩ := test a b c h
      exact ⟨v x,v y,v z,congrArg (Sym2.map v) ab,congrArg (Sym2.map v) bc,congrArg (Sym2.map v) ca⟩
    choose e test using atSize
    let label (a : X) (s : Finset X) := e s
      (if h : a ∈ insert anchor s then ⟨a,h⟩ else ⟨anchor,Finset.mem_insert_self _ _⟩)
    refine ⟨X,?_⟩
    intro d
    obtain ⟨a,b,c,h,ab,ac⟩ := hard fun x => d (label x)
    refine ⟨label a,label b,label c,ab,ac,?_⟩
    filter_upwards [Filter.eventually_finset_mem_atTop a, Filter.eventually_finset_mem_atTop b,
      Filter.eventually_finset_mem_atTop c] with s ha hb hc
    have ma := Finset.mem_insert_of_mem (b := anchor) ha
    have mb := Finset.mem_insert_of_mem (b := anchor) hb
    have mc := Finset.mem_insert_of_mem (b := anchor) hc
    simpa only [label,dif_pos ma,dif_pos mb,dif_pos mc] using test s ⟨a,ma⟩ ⟨b,mb⟩ ⟨c,mc⟩ h
  · rintro ⟨I,h⟩
    exact main ⟨I,fun s => u s.card,fun s => U s.card,fun s => free s.card,h⟩ common_coordinate


/-- A binary cut on the ultrafilter classes of a finite list of vertex
sequences agrees, at almost every coordinate, with an actual vertex cut. -/
private theorem realize_cut {J : Type} (U : Ultrafilter J)
    (bit : (J → ℕ) → Bool)
    (same : ∀ f g, (f =ᶠ[U] g) → bit f = bit g) (S : Finset (J → ℕ)) :
    ∀ᶠ j in U, ∃ cut : ℕ → Bool, ∀ f ∈ S, cut (f j) = bit f := by
  classical
  have pair (f g : J → ℕ) : ∀ᶠ j in U, f j = g j → bit f = bit g := by
    by_cases eq : bit f = bit g
    · exact .of_forall fun _ _ => eq
    · have ne : ¬ f =ᶠ[U] g := fun h => eq (same f g h)
      exact (Ultrafilter.eventually_not.mpr ne).mono fun _ hn he => (hn he).elim
  have all : ∀ᶠ j in U, ∀ f ∈ S, ∀ g ∈ S, f j = g j → bit f = bit g :=
    S.eventually_all.mpr fun f _ => S.eventually_all.mpr fun g _ => pair f g
  filter_upwards [all] with j ok
  refine ⟨fun v => decide (∃ g ∈ S, g j = v ∧ bit g = true),?_⟩
  intro f hf
  cases h : bit f with
  | false =>
    apply decide_eq_false
    rintro ⟨g,hg,e,b⟩
    exact Bool.noConfusion (b.symm.trans ((ok g hg f hf e).trans h))
  | true => exact decide_eq_true ⟨f,hf,rfl,h⟩

/-- A binary code on vertex classes only has to separate adjacent pairs. -/
theorem adjacent_codes {J : Type} (l : Filter J) (U : Ultrafilter J) (below : (U : Filter J) ≤ l)
    (n : J → ℕ) (code : ((j : J) → Fin (n j)) → ℕ → Bool)
    (stable : ∀ f g, (∀ᶠ j in U, f j = g j) → code f = code g)
    (G : (j : J) → SimpleGraph (Fin (n j)))
    (separates : ∀ f g, (∀ᶠ j in U, (G j).Adj (f j) (g j)) → code f ≠ code g) :
    ∃ d : ((j : J) → (G j).edgeSet) → ℕ, ∀ a b c, d a = d b → d a = d c →
      ¬ ∀ᶠ j in l, ∃ x y z : Fin (n j), (a j : Sym2 _) = s(x,y) ∧
        (b j : Sym2 _) = s(y,z) ∧ (c j : Sym2 _) = s(z,x) := by
  classical
  let E := (j : J) → (G j).edgeSet
  let L (a : E) (j : J) := ((a j).val.out.1 : ℕ)
  let R (a : E) (j : J) := ((a j).val.out.2 : ℕ)
  by_cases empty : IsEmpty E
  · exact ⟨fun _ => 0,fun a => (empty.false a).elim⟩
  obtain ⟨base⟩ := not_isEmpty_iff.mp empty
  let clamp (f : J → ℕ) (j : J) : Fin (n j) :=
    if h : f j < n j then ⟨f j,h⟩ else (base j).val.out.1
  have left (a : E) (j : J) : clamp (L a) j = (a j).val.out.1 := dif_pos (a j).val.out.1.isLt
  have right (a : E) (j : J) : clamp (R a) j = (a j).val.out.2 := dif_pos (a j).val.out.2.isLt
  have sep (a : E) : ∃ k, code (clamp (L a)) k ≠ code (clamp (R a)) k := by
    by_contra! h
    apply separates _ _ _ (funext h)
    apply Filter.Eventually.of_forall
    intro j
    rw [left,right]
    have edge := (a j).property
    rwa [← (a j).val.out_eq] at edge
  choose index diff using sep
  refine ⟨index,?_⟩
  intro a b c ab ac tri
  let bit (v : J → ℕ) := code (clamp v) (index a)
  have opposite (p : E) (k : index p = index a) : bit (L p) ≠ bit (R p) := by
    simpa only [bit,← k] using diff p
  let S : Finset (J → ℕ) := {L a,R a,L b,R b,L c,R c}
  have realize := realize_cut U bit (fun f g h => congrFun
    (stable _ _ (h.mono fun j eq => by simp only [clamp,eq])) _) S
  obtain ⟨j,⟨cut,hcut⟩,x,y,z,xy,yz,zx⟩ := (realize.and (below tri)).exists
  have side (p : E) (hl : L p ∈ S) (hr : R p ∈ S) (k : index p = index a)
      (v w : Fin (n j)) (edge : (p j).val = s(v,w)) : cut v ≠ cut w := by
    have ne : cut (L p j) ≠ cut (R p j) := by rw [hcut _ hl,hcut _ hr]; exact opposite p k
    have oriented : s((p j).val.out.1,(p j).val.out.2) = s(v,w) := (p j).val.out_eq.trans edge
    rcases Sym2.eq_iff.mp oriented with h | h
    · simpa only [L,R,h.1,h.2] using ne
    · simpa only [L,R,h.1,h.2] using ne.symm
  have A := side a (by simp [S]) (by simp [S]) rfl x y xy
  have B := side b (by simp [S]) (by simp [S]) ab.symm y z yz
  have C := side c (by simp [S]) (by simp [S]) ac.symm z x zx
  revert A B C
  cases cut x <;> cases cut y <;> cases cut z <;> decide

/-- Only bounded vertex positions need binary codes. Equality of their codes
must agree with equality on the chosen ultrafilter extending the filter. -/
theorem coded_positions {J : Type} (l : Filter J) (U : Ultrafilter J) (below : (U : Filter J) ≤ l)
    (n : J → ℕ) (code : ((j : J) → Fin (n j)) → ℕ → Bool)
    (faithful : ∀ f g, code f = code g ↔ ∀ᶠ j in U, f j = g j)
    (G : (j : J) → SimpleGraph (Fin (n j))) :
    ∃ d : ((j : J) → (G j).edgeSet) → ℕ, ∀ a b c, d a = d b → d a = d c →
      ¬ ∀ᶠ j in l, ∃ x y z : Fin (n j), (a j : Sym2 _) = s(x,y) ∧
        (b j : Sym2 _) = s(y,z) ∧ (c j : Sym2 _) = s(z,x) := by
  apply adjacent_codes l U below n code (fun f g h => (faithful f g).mpr h) G
  intro f g edges eq
  obtain ⟨j,adj,same⟩ := (edges.and ((faithful f g).mp eq)).exists
  exact adj.ne same

/-- A continuum-sized space of vertex sequences gives enough binary cuts for all edges. -/
theorem coded_coordinates {J : Type} (code : (J → ℕ) ↪ (ℕ → Bool)) (l : Filter J) [NeBot l]
    (n : J → ℕ) (G : (j : J) → SimpleGraph (Fin (n j))) :
    ∃ d : ((j : J) → (G j).edgeSet) → ℕ, ∀ a b c, d a = d b → d a = d c →
      ¬ ∀ᶠ j in l, ∃ x y z : Fin (n j), (a j : Sym2 _) = s(x,y) ∧
        (b j : Sym2 _) = s(y,z) ∧ (c j : Sym2 _) = s(z,x) := by
  classical
  let U := Ultrafilter.of l
  let rel : Setoid (J → ℕ) := {
    r := EventuallyEq U
    iseqv := ⟨EventuallyEq.refl _, EventuallyEq.symm, EventuallyEq.trans⟩ }
  let rep (f : J → ℕ) : J → ℕ := (Quotient.mk rel f).out
  have sound (f : J → ℕ) : rep f =ᶠ[U] f :=
    Quotient.exact (Quotient.out_eq (Quotient.mk rel f))
  have stable {f g : J → ℕ} (h : f =ᶠ[U] g) : rep f = rep g :=
    congrArg Quotient.out (Quotient.sound (s := rel) h)
  let vals (f : (j : J) → Fin (n j)) (j : J) := (f j).val
  apply coded_positions l U (Ultrafilter.of_le l) n (fun f => code (rep (vals f))) _ G
  intro f g
  constructor
  · intro eq
    have same := code.injective eq
    exact ((sound (vals f)).symm.trans (same ▸ sound (vals g))).mono fun _ h => Fin.ext h
  · intro eq
    exact congrArg code (stable (eq.mono fun _ h => congrArg Fin.val h))

/-- Countably many coordinates admit a countable colouring avoiding every
eventual triangle, even for an arbitrary proper filter and arbitrary factors
on finite ordinal vertex sets. Thus finite Ramsey strength is insufficient
on a countable index set in the fixed-factor criterion. -/
theorem countable_coordinates {J : Type} [Countable J] (l : Filter J) [NeBot l]
    (n : J → ℕ) (G : (j : J) → SimpleGraph (Fin (n j))) :
    ∃ d : ((j : J) → (G j).edgeSet) → ℕ, ∀ a b c, d a = d b → d a = d c →
      ¬ ∀ᶠ j in l, ∃ x y z : Fin (n j), (a j : Sym2 _) = s(x,y) ∧
        (b j : Sym2 _) = s(y,z) ∧ (c j : Sym2 _) = s(z,x) := by
  classical
  obtain ⟨num,inj⟩ := Countable.exists_injective_nat (J × ℕ)
  let bits (f : J → ℕ) (k : ℕ) := decide (∃ j, num (j,f j) = k)
  have inject : Function.Injective bits := by
    intro f g h
    funext j
    have atBit := congrFun h (num (j,f j))
    have known : bits f (num (j,f j)) = true := decide_eq_true ⟨j,rfl⟩
    obtain ⟨i,eq⟩ : ∃ i, num (i,g i) = num (j,f j) := of_decide_eq_true (atBit.symm.trans known)
    obtain ⟨rfl,hval⟩ := Prod.mk.inj (inj eq)
    exact hval.symm
  exact coded_coordinates ⟨bits,inject⟩ l n G

/-- Every witness in the product reduction requires an uncountable index set. -/
theorem uncountable_index {I : Type} (n : Finset I → ℕ)
    (G : (s : Finset I) → SimpleGraph (Fin (n s)))
    (hard : ∀ d : ((s : Finset I) → (G s).edgeSet) → ℕ,
      ∃ a b c, d a = d b ∧ d a = d c ∧ ∀ᶠ s in (atTop : Filter (Finset I)),
        ∃ x y z : Fin (n s), (a s : Sym2 _) = s(x,y) ∧
          (b s : Sym2 _) = s(y,z) ∧ (c s : Sym2 _) = s(z,x)) : ¬ Countable I := by
  intro small
  let _ : Countable I := small
  obtain ⟨d,avoids⟩ := countable_coordinates atTop n G
  obtain ⟨a,b,c,ab,ac,triangle⟩ := hard d
  exact avoids a b c ab ac triangle


/-- The trace on a finite coordinate uses at most two to the power of its
size many values. Distinct subsets have different traces on an entire tail. -/
theorem finite_traces (I : Type) :
    ∃ t : Set I → Finset I → ℕ, (∀ A s, t A s < 2 ^ s.card) ∧
      ∀ A B, A ≠ B → ∀ᶠ s in (atTop : Filter (Finset I)), t A s ≠ t B s := by
  classical
  let word (A : Set I) (s : Finset I) (i : ↥s) := decide (i.val ∈ A)
  let num (s : Finset I) := Fintype.equivFin (↥s → Bool)
  refine ⟨fun A s => (num s (word A s)).val,?_,?_⟩
  · intro A s
    simpa using (num s (word A s)).isLt
  · intro A B ne
    have differs : ∃ i, ¬ (i ∈ A ↔ i ∈ B) := by
      by_contra! h
      exact ne (Set.ext h)
    obtain ⟨i,hi⟩ := differs
    filter_upwards [Filter.eventually_finset_mem_atTop i] with s hs
    intro eq
    have bits := congrFun ((num s).injective (Fin.ext eq)) (⟨i,hs⟩ : ↥s)
    exact hi (by simpa only [word,decide_eq_decide] using bits)

open Cardinal in
private theorem binary_sequence_capacity {I : Type} [Infinite I] :
    Cardinal.mk (Finset I → ℕ) = 2 ^ Cardinal.mk I := by
  rw [Cardinal.mk_arrow,Cardinal.lift_id,Cardinal.lift_id,Cardinal.mk_nat,
    Cardinal.mk_finset_of_infinite]
  exact Cardinal.power_eq_two_power (Cardinal.aleph0_le_mk I)
    (Cardinal.natCast_le_aleph0 (n := 2)) (Cardinal.aleph0_le_mk I)

open Cardinal in
/-- Exact whole-space coding test: for any ultrafilter extending the tails,
its natural-valued germs can be separated by countably many binary cuts
exactly when the power set of the index fits into the continuum. -/
theorem germ_coding_iff {I : Type} [Infinite I] (U : Ultrafilter (Finset I))
    (tails : (U : Filter (Finset I)) ≤ atTop) :
    (∃ c : (Finset I → ℕ) → (ℕ → Bool), ∀ f g, c f = c g ↔ f =ᶠ[U] g) ↔
      2 ^ Cardinal.mk I ≤ 𝔠 := by
  classical
  have bits : Cardinal.mk (ℕ → Bool) = 𝔠 := by simp
  constructor
  · rintro ⟨c,faithful⟩
    obtain ⟨t,_,separate⟩ := finite_traces I
    have inj : Function.Injective (fun A => c (t A)) := by
      intro A B eq
      by_contra ne
      have agree := (faithful _ _).mp eq
      obtain ⟨s,h,k⟩ := (agree.and (tails (separate A B ne))).exists
      exact k h
    have bound := Cardinal.mk_le_of_injective inj
    rwa [Cardinal.mk_set,bits] at bound
  · intro h
    obtain ⟨e⟩ : Nonempty ((Finset I → ℕ) ↪ (ℕ → Bool)) := by
      change Cardinal.mk (Finset I → ℕ) ≤ Cardinal.mk (ℕ → Bool)
      rwa [binary_sequence_capacity,bits]
    let r : Setoid (Finset I → ℕ) := {
      r := EventuallyEq U
      iseqv := ⟨EventuallyEq.refl _,EventuallyEq.symm,EventuallyEq.trans⟩ }
    refine ⟨fun f => e (Quotient.mk r f).out,fun f g => ⟨?_,?_⟩⟩
    · intro eq
      apply Quotient.exact (s := r)
      rw [← (Quotient.mk r f).out_eq, ← (Quotient.mk r g).out_eq]
      exact congrArg (Quotient.mk r) (e.injective eq)
    · intro eq
      exact congrArg (fun q : Quotient r => e q.out) (Quotient.sound eq)

open Cardinal in
private theorem sequence_code {I : Type} [Infinite I] (h : 2 ^ Cardinal.mk I ≤ 𝔠) :
    Nonempty ((Finset I → ℕ) ↪ (ℕ → Bool)) := by
  change Cardinal.mk (Finset I → ℕ) ≤ Cardinal.mk (ℕ → Bool)
  rwa [binary_sequence_capacity,show Cardinal.mk (ℕ → Bool) = 𝔠 by simp]

open Cardinal in
/-- Under equality of the powers at aleph-zero and aleph-one the first
uncountable index still admits an avoiding colouring, for every family. -/
theorem aleph_one_plateau {I : Type} [Infinite I] (size : Cardinal.mk I = ℵ₁)
    (plateau : (2 : Cardinal.{0}) ^ ℵ₁ = 𝔠) (n : Finset I → ℕ)
    (G : (s : Finset I) → SimpleGraph (Fin (n s))) :
    ∃ d : ((s : Finset I) → (G s).edgeSet) → ℕ, ∀ a b c, d a = d b → d a = d c →
      ¬ ∀ᶠ s in (atTop : Filter (Finset I)), ∃ x y z : Fin (n s),
        (a s : Sym2 _) = s(x,y) ∧ (b s : Sym2 _) = s(y,z) ∧ (c s : Sym2 _) = s(z,x) := by
  obtain ⟨e⟩ := sequence_code (I := I) (by rw [size,plateau])
  exact coded_coordinates e atTop n G

open Cardinal in
/-- A hard product on an infinite index set requires strictly more subsets
of that set than real numbers. In particular an aleph-one index is ruled
out whenever its power set has size continuum. -/
theorem hard_index_power {I : Type} [Infinite I] (n : Finset I → ℕ)
    (G : (s : Finset I) → SimpleGraph (Fin (n s)))
    (hard : ∀ d : ((s : Finset I) → (G s).edgeSet) → ℕ,
      ∃ a b c, d a = d b ∧ d a = d c ∧ ∀ᶠ s in (atTop : Filter (Finset I)),
        ∃ x y z : Fin (n s), (a s : Sym2 _) = s(x,y) ∧
          (b s : Sym2 _) = s(y,z) ∧ (c s : Sym2 _) = s(z,x)) :
    𝔠 < 2 ^ Cardinal.mk I := by
  by_contra! h
  obtain ⟨e⟩ := sequence_code h
  obtain ⟨d,avoids⟩ := coded_coordinates e atTop n G
  obtain ⟨a,b,c,ab,ac,t⟩ := hard d
  exact avoids a b c ab ac t


/-- An eventual triangle lives in one component modulo eventual equality.
If all single-component products admitted avoiding colourings, use one
such colouring on each equivalence class to colour the full product. -/
theorem single_component {J : Type} (l : Filter J) (n width : J → ℕ)
    (G : (j : J) → SimpleGraph (Fin (n j)))
    (tag : (j : J) → Fin (n j) → SimpleGraph (Fin (width j)))
    (pos : (j : J) → Fin (n j) → Fin (width j))
    (inside : ∀ j x y, (G j).Adj x y → tag j x = tag j y ∧ (tag j x).Adj (pos j x) (pos j y))
    (hard : ∀ d : ((j : J) → (G j).edgeSet) → ℕ, ∃ a b c, d a = d b ∧ d a = d c ∧
      ∀ᶠ j in l, ∃ x y z : Fin (n j), (a j : Sym2 _) = s(x,y) ∧
        (b j : Sym2 _) = s(y,z) ∧ (c j : Sym2 _) = s(z,x)) :
    ∃ v : (j : J) → Fin (n j), ∀ d : ((j : J) → (tag j (v j)).edgeSet) → ℕ,
      ∃ a b c, d a = d b ∧ d a = d c ∧ ∀ᶠ j in l, ∃ x y z : Fin (width j),
        (a j : Sym2 _) = s(x,y) ∧ (b j : Sym2 _) = s(y,z) ∧ (c j : Sym2 _) = s(z,x) := by
  classical
  let E := (j : J) → (G j).edgeSet
  let vertex (a : E) (j : J) := (a j).val.out.1
  let T (a : E) (j : J) := tag j (vertex a j)
  let raw (a : E) (j : J) := Sym2.map (pos j) (a j).val
  have law (a : E) (j : J) :
      tag j (a j).val.out.1 = tag j (a j).val.out.2 ∧ raw a j ∈ (T a j).edgeSet := by
    have e := (a j).property
    rw [← (a j).val.out_eq] at e
    obtain ⟨eq,adj⟩ := inside _ _ _ e
    refine ⟨eq,?_⟩
    change Sym2.map (pos j) (a j).val ∈ (tag j (a j).val.out.1).edgeSet
    have hr : Sym2.map (pos j) (a j).val = s(pos j (a j).val.out.1,pos j (a j).val.out.2) :=
      congrArg (Sym2.map (pos j)) (a j).val.out_eq.symm
    rw [hr]
    exact adj
  have ends (a : E) (j : J) {x y} (h : (a j).val = s(x,y)) :
      T a j = tag j x ∧ T a j = tag j y := by
    have pair : s((a j).val.out.1,(a j).val.out.2) = s(x,y) := (a j).val.out_eq.trans h
    change tag j (a j).val.out.1 = _ ∧ tag j (a j).val.out.1 = _
    rcases Sym2.eq_iff.mp pair with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨rfl,(law a j).1⟩
    · exact ⟨(law a j).1,rfl⟩
  let rel : Setoid E := {
    r := fun a b => ∀ᶠ j in l, T a j = T b j
    iseqv := ⟨fun _ => .of_forall fun _ => rfl,fun {_ _} h => h.mono fun _ eq => eq.symm,
      fun {_ _ _} h k => (h.and k).mono fun _ eq => eq.1.trans eq.2⟩ }
  let q := Quotient.mk rel
  let proj (r : Quotient rel) (a : E) (j : J) : (T r.out j).edgeSet :=
    if h : T a j = T r.out j then ⟨raw a j,h ▸ (law a j).2⟩ else ⟨_,(law r.out j).2⟩
  by_contra fail
  have avoid (r : Quotient rel) : ∃ d : ((j : J) → (T r.out j).edgeSet) → ℕ,
      ∀ a b c, d a = d b → d a = d c → ¬ ∀ᶠ j in l, ∃ x y z : Fin (width j),
        (a j : Sym2 _) = s(x,y) ∧ (b j : Sym2 _) = s(y,z) ∧ (c j : Sym2 _) = s(z,x) := by
    by_contra! all
    apply fail
    exact ⟨vertex r.out,fun d => by simpa using all d⟩
  choose d avoids using avoid
  obtain ⟨a,b,c,ab,ac,tri⟩ := hard fun e => d (q e) (proj (q e) e)
  have tags : ∀ᶠ j in l, T a j = T b j ∧ T a j = T c j := by
    filter_upwards [tri] with j h
    obtain ⟨x,y,z,A,B,C⟩ := h
    exact ⟨(ends a j A).2.trans (ends b j B).1.symm,(ends a j A).1.trans (ends c j C).2.symm⟩
  have qb : q b = q a := Quotient.sound (s := rel) (tags.mono fun _ h => h.1.symm)
  have qc : q c = q a := Quotient.sound (s := rel) (tags.mono fun _ h => h.2.symm)
  rw [qb] at ab
  rw [qc] at ac
  apply avoids (q a) _ _ _ ab ac
  have rep : ∀ᶠ j in l, T (q a).out j = T a j := Quotient.exact (q a).out_eq
  filter_upwards [tri,tags,rep] with j h agree same
  obtain ⟨x,y,z,A,B,C⟩ := h
  refine ⟨pos j x,pos j y,pos j z,?_,?_,?_⟩
  · simpa only [proj,dif_pos same.symm,raw,Sym2.map_mk] using congrArg (Sym2.map (pos j)) A
  · simpa only [proj,dif_pos (same.trans agree.1).symm,raw,Sym2.map_mk] using congrArg (Sym2.map (pos j)) B
  · simpa only [proj,dif_pos (same.trans agree.2).symm,raw,Sym2.map_mk] using congrArg (Sym2.map (pos j)) C

/-- The hard step is equivalent to a product whose coordinate of size m has
just 2(m+1) vertices. The selected graph may vary with the coordinate. -/
theorem linear_factors_iff :
    OMA.R_Erdos595_erdos_595_R2.H1 ↔
      ∃ (I : Type) (G : (s : Finset I) → SimpleGraph (Fin (2*(s.card+1)))),
        (∀ s, (G s).CliqueFree 4) ∧
        ∀ d : ((s : Finset I) → (G s).edgeSet) → ℕ, ∃ a b c, d a = d b ∧ d a = d c ∧
          ∀ᶠ s in (atTop : Filter (Finset I)), ∃ x y z : Fin (2*(s.card+1)),
            (a s : Sym2 _) = s(x,y) ∧ (b s : Sym2 _) = s(y,z) ∧ (c s : Sym2 _) = s(z,x) := by
  constructor
  · intro h
    obtain ⟨u,U,free,inc,labels⟩ := universal_factors_with_positions
    obtain ⟨I,hard⟩ := (fixed_factors_iff u U free inc).mp h
    choose tag pos inside using labels
    obtain ⟨v,localHard⟩ := single_component (atTop : Filter (Finset I))
      (fun s => u s.card) (fun s => 2*(s.card+1)) (fun s => U s.card)
      (fun s x => (tag s.card x).val) (fun s => pos s.card)
      (fun s x y h => ⟨congrArg Subtype.val (inside _ x y h).1,(inside _ x y h).2⟩) hard
    exact ⟨I,_,fun s => (tag s.card (v s)).property,localHard⟩
  · rintro ⟨I,G,free,hard⟩
    exact main ⟨I,fun s => 2*(s.card+1),G,free,hard⟩ common_coordinate

/-- Every I-indexed list of bounded position sequences misses one even
modulo eventual equality: at s avoid the at most |s| listed values. -/
theorem diagonal_position {I : Type}
    (f : I → (s : Finset I) → Fin (2*(s.card+1))) :
    ∃ g : (s : Finset I) → Fin (2*(s.card+1)),
      ∀ i, ∀ᶠ s in (atTop : Filter (Finset I)), g s ≠ f i s := by
  classical
  have missing (s : Finset I) : ∃ k : Fin (2*(s.card+1)), k ∉ s.image (fun i => f i s) := by
    by_contra! all
    have eq := Finset.eq_univ_of_forall all
    have bound := Finset.card_image_le (s := s) (f := fun i => f i s)
    rw [eq,Finset.card_univ,Fintype.card_fin] at bound
    omega
  choose g fresh using missing
  refine ⟨g,fun i => ?_⟩
  filter_upwards [Filter.eventually_finset_mem_atTop i] with s hi
  exact fun eq => fresh s (eq ▸ Finset.mem_image_of_mem (fun j => f j s) hi)

/-- At or above the continuum even linear-size position germs cannot all
be distinguished by countably many binary cuts. This applies at aleph-one
under CH; separation of just the adjacent pairs is a weaker condition. -/
theorem no_faithful_position_code {I : Type} (index : (ℕ → Bool) ↪ I)
    (U : Filter (Finset I)) [NeBot U] (tails : U ≤ atTop) :
    ¬ ∃ c : ((s : Finset I) → Fin (2*(s.card+1))) → (ℕ → Bool),
      ∀ f g, c f = c g → ∀ᶠ s in U, f s = g s := by
  classical
  rintro ⟨c,faithful⟩
  let list (i : I) : (s : Finset I) → Fin (2*(s.card+1)) :=
    if h : ∃ g, index (c g) = i then h.choose else fun _ => 0
  obtain ⟨g,avoids⟩ := diagonal_position list
  let i := index (c g)
  have hit : ∃ h, index (c h) = i := ⟨g,rfl⟩
  have eq : c (list i) = c g := by
    apply index.injective
    simpa only [list,dif_pos hit] using hit.choose_spec
  obtain ⟨s,h,k⟩ := ((faithful _ _ eq).and (tails (avoids i))).exists
  exact k h.symm


/-- Increasing pairs, joined when they concatenate, form a triangle-free
graph needing more vertex colours than any prescribed palette C.
An incoming-colour set separates every two points of the underlying order. -/
private theorem shift_obstruction (C A : Type) [LinearOrder A]
    (large : ∀ f : A → Set C, ¬ Function.Injective f) :
    ∃ (I : Type) (H : SimpleGraph I), H.CliqueFree 3 ∧
      ∀ d : I → C, ∃ x y, H.Adj x y ∧ d x = d y := by
  classical
  let I := {p : A × A // p.1 < p.2}
  let H : SimpleGraph I := {
    Adj := fun x y => x.val.2 = y.val.1 ∨ y.val.2 = x.val.1
    symm := ⟨fun _ _ h => h.symm⟩
    loopless := ⟨fun x h => x.property.ne (h.elim Eq.symm Eq.symm)⟩ }
  refine ⟨I,H,?_,?_⟩
  · intro t triangle
    obtain ⟨x,y,z,xy,xz,yz,_⟩ := is3Clique_iff.mp triangle
    have hx := x.property
    have hy := y.property
    have hz := z.property
    rcases xy with h | h <;> rcases xz with k | k <;> rcases yz with g | g <;> grind
  · intro d
    by_contra! proper
    let incoming (y : A) : Set C := {k | ∃ (x : A) (h : x < y), d ⟨(x,y),h⟩ = k}
    have distinct {x y : A} (h : x < y) : incoming x ≠ incoming y := by
      intro eq
      let k := d ⟨(x,y),h⟩
      have hy : k ∈ incoming y := ⟨x,h,rfl⟩
      obtain ⟨w,wx,same⟩ := (show k ∈ incoming x from eq ▸ hy)
      exact proper ⟨(w,x),wx⟩ ⟨(x,y),h⟩ (Or.inl rfl) same
    apply large incoming
    intro x y eq
    rcases lt_trichotomy x y with h | h | h
    · exact (distinct h eq).elim
    · exact h
    · exact (distinct h eq.symm).elim

/-- The linear factor bound allows persistent adjacency from a graph of
arbitrarily high vertex chromatic number even if every factor is triangle-free.
In particular adjacent-only binary tests can fail in a product whose triangle
tests are all avoided by the constant edge colouring. -/
theorem triangle_free_position_obstruction (C : Type) [Nonempty C] :
    ∃ (I : Type) (G : (s : Finset I) → SimpleGraph (Fin (2*(s.card+1)))),
      (∀ s, (G s).CliqueFree 3) ∧ Nonempty ((s : Finset I) → (G s).edgeSet) ∧
      ∀ d : ((s : Finset I) → Fin (2*(s.card+1))) → C,
        ∃ f g, d f = d g ∧ ∀ᶠ s in (atTop : Filter (Finset I)), (G s).Adj (f s) (g s) := by
  classical
  obtain ⟨I,H,free,collision⟩ :=
    @shift_obstruction C (Set (Set C)) (linearOrderOfSTO WellOrderingRel) Function.cantor_injective
  obtain ⟨p,q,pq,_⟩ := collision (fun _ => Classical.arbitrary C)
  let L (s : Finset I) := insert p (insert q s)
  have fits (s : Finset I) : Nonempty (↥(L s) ↪ Fin (2*(s.card+1))) := by
    apply Function.Embedding.nonempty_of_card_le
    simp only [Fintype.card_coe,Fintype.card_fin]
    have h := Finset.card_insert_le p (insert q s)
    have k := Finset.card_insert_le q s
    dsimp [L]
    omega
  let slot (s : Finset I) := (fits s).some
  let label (x : I) (s : Finset I) := if h : x ∈ L s then slot s ⟨x,h⟩ else slot s ⟨p,by simp [L]⟩
  let read (s : Finset I) (i : Fin (2*(s.card+1))) : I :=
    if h : ∃ v, slot s v = i then h.choose.val else p
  have decode {x : I} {s : Finset I} (hx : x ∈ L s) : read s (label x s) = x := by
    let v : ↥(L s) := ⟨x,hx⟩
    have h : ∃ w, slot s w = slot s v := ⟨v,rfl⟩
    simp only [label,dif_pos hx,read]
    change (if hh : ∃ w, slot s w = slot s v then hh.choose.val else p) = v.val
    rw [dif_pos h]
    exact congrArg Subtype.val ((slot s).injective h.choose_spec)
  let G (s : Finset I) := H.comap (read s)
  refine ⟨I,G,?_,?_,?_⟩
  · intro s t clique
    obtain ⟨x,y,z,xy,xz,yz,_⟩ := is3Clique_iff.mp clique
    exact free _ (is3Clique_triple_iff.mpr ⟨xy,xz,yz⟩)
  · refine ⟨fun s => ⟨s(label p s,label q s),?_⟩⟩
    change H.Adj (read s (label p s)) (read s (label q s))
    rwa [decode (by simp [L]),decode (by simp [L])]
  · intro d
    obtain ⟨x,y,xy,same⟩ := collision (fun x => d (label x))
    refine ⟨label x,label y,same,?_⟩
    filter_upwards [Filter.eventually_finset_mem_atTop x,Filter.eventually_finset_mem_atTop y] with s hx hy
    change H.Adj (read s (label x s)) (read s (label y s))
    rwa [decode (by simp [L,hx]),decode (by simp [L,hy])]

/-- For the countable-cut palette the failure of every adjacent-endpoint code
coexists with an avoiding one-colour edge colouring, on the same product. -/
theorem cuts_fail_without_eventual_triangles :
    ∃ (I : Type) (G : (s : Finset I) → SimpleGraph (Fin (2*(s.card+1)))),
      (∀ s, (G s).CliqueFree 3) ∧ Nonempty ((s : Finset I) → (G s).edgeSet) ∧
      (∀ d : ((s : Finset I) → Fin (2*(s.card+1))) → (ℕ → Bool),
        ∃ f g, d f = d g ∧ ∀ᶠ s in (atTop : Filter (Finset I)), (G s).Adj (f s) (g s)) ∧
      ∀ a b c : (s : Finset I) → (G s).edgeSet,
        ¬ ∀ᶠ s in (atTop : Filter (Finset I)), ∃ x y z : Fin (2*(s.card+1)),
          (a s : Sym2 _) = s(x,y) ∧ (b s : Sym2 _) = s(y,z) ∧ (c s : Sym2 _) = s(z,x) := by
  classical
  obtain ⟨I,G,free,nonempty,collide⟩ := triangle_free_position_obstruction (ℕ → Bool)
  refine ⟨I,G,free,nonempty,collide,?_⟩
  intro a b c eventual
  obtain ⟨s,x,y,z,A,B,C⟩ := eventual.exists
  have edge {e : (G s).edgeSet} {v w} (h : e.val = s(v,w)) : (G s).Adj v w :=
    show s(v,w) ∈ (G s).edgeSet from h ▸ e.property
  exact free s _ (is3Clique_triple_iff.mpr ⟨edge A,(edge C).symm,edge B⟩)

end OMA.R_Erdos595_erdos_595_R2_H1_R1
