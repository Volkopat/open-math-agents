import OMAReductions.R_Erdos595_erdos_595_R3
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Filter.Ultrafilter.Defs

-- Credit: @wispiANt
namespace OMA.R_Erdos595_erdos_595_R3_H1_R1

open SimpleGraph Filter

/-- Construct a triple system of decisions with no countable weak colouring.
Each finite set of decisions needs simultaneous models only on its own
endpoints. Models are allowed to differ above a shared decision's stage. -/
def H1 : Prop :=
  ∃ (I : Type) (_ : LinearOrder I) (_ : WellFoundedLT I) (_ : Infinite I)
    (X : Type) (lo hi : X → I) (T : X → X → X → Prop),
    (∀ d : X → ℕ, ∃ x y z, T x y z ∧ d x = d y ∧ d x = d z) ∧
    (∀ x y z, T x y z → lo x < hi x ∧ hi x < hi z ∧
      lo y = lo x ∧ hi y = hi z ∧ lo z = hi x) ∧
    ∀ S : Finset X, ∃ g : X → SimpleGraph I,
      (∀ x ∈ S, (g x).CliqueFree 4 ∧ ∀ i j, (g x).Adj i j →
        (∃ w ∈ S, i = lo w ∨ i = hi w) ∧ (∃ w ∈ S, j = lo w ∨ j = hi w)) ∧
      ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, T x y z →
        (g z).Adj (lo x) (hi x) ∧ (g z).Adj (lo x) (hi z) ∧ (g z).Adj (hi x) (hi z) ∧
        (∀ i ≤ hi x, ∀ j ≤ hi x, (g x).Adj i j ↔ (g z).Adj i j) ∧
        (∀ i ≤ hi y, ∀ j ≤ hi y, (g y).Adj i j ↔ (g z).Adj i j)

/-- Compactness for simultaneous graph models on a fixed ordered horizon.
Agreement below a stage includes absent as well as present edges. -/
def H2 : Prop :=
  ∀ (I X : Type) [LinearOrder I] (lo hi : X → I) (T : X → X → X → Prop),
    let fits := fun (g : X → SimpleGraph I) (x y z : X) =>
      (g z).Adj (lo x) (hi x) ∧ (g z).Adj (lo x) (hi z) ∧ (g z).Adj (hi x) (hi z) ∧
      (∀ i ≤ hi x, ∀ j ≤ hi x, (g x).Adj i j ↔ (g z).Adj i j) ∧
      (∀ i ≤ hi y, ∀ j ≤ hi y, (g y).Adj i j ↔ (g z).Adj i j)
    (∀ S : Finset X, ∃ g : X → SimpleGraph I, (∀ x ∈ S, (g x).CliqueFree 4) ∧
      ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, T x y z → fits g x y z) →
    ∃ g : X → SimpleGraph I, (∀ x, (g x).CliqueFree 4) ∧ ∀ x y z, T x y z → fits g x y z

theorem compact_models : H2 := by
  classical
  intro I X _ lo hi T fits localModels
  choose model legal tests using localModels
  let U := Ultrafilter.of (Filter.atTop : Filter (Finset X))
  have fine (x : X) : ∀ᶠ S : Finset X in U, x ∈ S :=
    Ultrafilter.of_le _ (Filter.eventually_finset_mem_atTop x)
  let G (x : X) : SimpleGraph I := {
    Adj := fun i j => ∀ᶠ S : Finset X in U, (model S x).Adj i j
    symm := ⟨fun _ _ h => h.mono fun _ e => e.symm⟩
    loopless := ⟨fun i h => by obtain ⟨_,e⟩ := h.exists; exact e.ne rfl⟩ }
  refine ⟨G,?_,?_⟩
  · intro x s clique
    have together : ∀ᶠ S : Finset X in U, ∀ i ∈ s, ∀ j ∈ s, i ≠ j → (model S x).Adj i j := by
      apply s.eventually_all.mpr
      intro i hi'
      apply s.eventually_all.mpr
      intro j hj
      by_cases ne : i = j
      · exact Filter.Eventually.of_forall fun _ h => (h ne).elim
      · exact (show ∀ᶠ S : Finset X in U, (model S x).Adj i j from clique.isClique hi' hj ne).mono
          fun _ edge _ => edge
    obtain ⟨S,mem,edges⟩ := ((fine x).and together).exists
    exact legal S x mem s ⟨fun i hi' j hj ne => edges i hi' j hj ne,clique.card_eq⟩
  · intro x y z t
    have ok : ∀ᶠ S : Finset X in U, fits (model S) x y z :=
      ((fine x).and ((fine y).and (fine z))).mono fun S h => tests S x h.1 y h.2.1 z h.2.2 t
    refine ⟨ok.mono (fun _ h => h.1),ok.mono (fun _ h => h.2.1),ok.mono (fun _ h => h.2.2.1),?_,?_⟩
    · intro i a j b
      exact Filter.eventually_congr (ok.mono fun _ h => h.2.2.2.1 i a j b)
    · intro i a j b
      exact Filter.eventually_congr (ok.mono fun _ h => h.2.2.2.2 i a j b)

theorem main : H1 → H2 → OMA.R_Erdos595_erdos_595_R3.H1 := by
  classical
  rintro ⟨I,order,wf,inf,X,lo,hi,T,hard,shape,finite⟩ compact
  let : LinearOrder I := order
  obtain ⟨g,legal,test⟩ := compact I X lo hi T (by
    intro S
    obtain ⟨g,ok,t⟩ := finite S
    exact ⟨g,fun x hx => (ok x hx).1,t⟩)
  refine ⟨I,order,wf,inf,?_⟩
  intro paint
  let past (G : SimpleGraph I) (k : I) := {p : I × I | p.1 ≤ k ∧ p.2 ≤ k ∧ G.Adj p.1 p.2}
  let d (x : X) := paint (hi x) (past (g x) (hi x)) (lo x)
  obtain ⟨x,y,z,t,xy,xz⟩ := hard d
  obtain ⟨ab,bc,ly,hy,lz⟩ := shape x y z t
  obtain ⟨eab,eac,ebc,hx,hy'⟩ := test x y z t
  have same (u : X) (h : ∀ i ≤ hi u, ∀ j ≤ hi u, (g u).Adj i j ↔ (g z).Adj i j) :
      past (g u) (hi u) = past (g z) (hi u) := by
    ext p
    exact ⟨fun w => ⟨w.1,w.2.1,(h _ w.1 _ w.2.1).mp w.2.2⟩,
      fun w => ⟨w.1,w.2.1,(h _ w.1 _ w.2.1).mpr w.2.2⟩⟩
  refine ⟨g z,legal z,lo x,hi x,hi z,ab,bc,eab,eac,ebc,?_⟩
  dsimp only [d] at xy xz
  rw [same x hx,same y hy',ly,hy] at xy
  rw [same x hx,lz] at xz
  exact ⟨xy,xz⟩

/-- Conversely, actual losing plays generate such a decision system. For a
finite test keep only the endpoints of its labels. This pruning is shared
by every model, so all the required prefix agreements survive. -/
theorem from_painter : OMA.R_Erdos595_erdos_595_R3.H1 → H1 := by
  classical
  rintro ⟨I,order,wf,inf,lose⟩
  let : LinearOrder I := order
  let X := I × Set (I × I) × I
  let past (G : SimpleGraph I) (k : I) := {p : I × I | p.1 ≤ k ∧ p.2 ≤ k ∧ G.Adj p.1 p.2}
  let T (x y z : X) := x.2.2 < x.1 ∧ x.1 < z.1 ∧ y.2.2 = x.2.2 ∧ y.1 = z.1 ∧ z.2.2 = x.1 ∧
    ∃ G : SimpleGraph I, G.CliqueFree 4 ∧ G.Adj x.2.2 x.1 ∧ G.Adj x.2.2 z.1 ∧ G.Adj x.1 z.1 ∧
      past G x.1 = x.2.1 ∧ past G y.1 = y.2.1 ∧ past G z.1 = z.2.1
  refine ⟨I,order,wf,inf,X,fun x => x.2.2,Prod.fst,T,?_,?_,?_⟩
  · intro d
    obtain ⟨G,legal,a,b,c,ab,bc,eab,eac,ebc,mono⟩ := lose (fun j s i => d (j,s,i))
    exact ⟨(b,past G b,a),(c,past G c,a),(c,past G c,b),
      ⟨ab,bc,rfl,rfl,rfl,G,legal,eab,eac,ebc,rfl,rfl,rfl⟩,mono⟩
  · rintro x y z ⟨ab,bc,ly,hy,lz,_⟩
    exact ⟨ab,bc,ly,hy,lz⟩
  · intro S
    let models (x : X) (G : SimpleGraph I) := G.CliqueFree 4 ∧ past G x.1 = x.2.1
    let rep (x : X) : SimpleGraph I := if h : ∃ G, models x G then h.choose else ⊥
    have legal (x : X) : (rep x).CliqueFree 4 := by
      by_cases h : ∃ G, models x G
      · simpa only [rep,dif_pos h] using h.choose_spec.1
      · simpa only [rep,dif_neg h] using (cliqueFree_bot (by decide : 2 ≤ 4) : (⊥ : SimpleGraph I).CliqueFree 4)
    have agrees (x : X) (G : SimpleGraph I) (ok : models x G) (i j : I) (hi : i ≤ x.1) (hj : j ≤ x.1) :
        (rep x).Adj i j ↔ G.Adj i j := by
      have h : ∃ F, models x F := ⟨G,ok⟩
      have eq : past (rep x) x.1 = past G x.1 := by
        simpa only [rep,dif_pos h] using h.choose_spec.2.trans ok.2.symm
      have atEdge := Set.ext_iff.mp eq (i,j)
      simpa [past,hi,hj] using atEdge
    let V (i : I) := ∃ w ∈ S, i = w.2.2 ∨ i = w.1
    let g (x : X) : SimpleGraph I := {
      Adj := fun i j => (rep x).Adj i j ∧ V i ∧ V j
      symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
      loopless := ⟨fun _ h => h.1.ne rfl⟩ }
    refine ⟨g,fun x _ => ⟨CliqueFree.anti (fun _ _ h => h.1 : g x ≤ rep x) (legal x),
      fun _ _ h => h.2⟩,?_⟩
    intro x hx y _ z hz t
    obtain ⟨ab,bc,_,hy,_,G,free,eab,eac,ebc,px,py,pz⟩ := t
    have vx : V x.2.2 := ⟨x,hx,Or.inl rfl⟩
    have vb : V x.1 := ⟨x,hx,Or.inr rfl⟩
    have vc : V z.1 := ⟨z,hz,Or.inr rfl⟩
    have same := agrees z G ⟨free,pz⟩
    refine ⟨⟨(same _ _ (ab.trans bc).le bc.le).mpr eab,vx,vb⟩,
      ⟨(same _ _ (ab.trans bc).le le_rfl).mpr eac,vx,vc⟩,
      ⟨(same _ _ bc.le le_rfl).mpr ebc,vb,vc⟩,?_,?_⟩
    · intro i hi j hj
      exact and_congr_left (fun _ => (agrees x G ⟨free,px⟩ i j hi hj).trans
        (same i j (hi.trans bc.le) (hj.trans bc.le)).symm)
    · intro i hi j hj
      exact and_congr_left (fun _ => (agrees y G ⟨free,py⟩ i j hi hj).trans
        (same i j (hi.trans hy.le) (hj.trans hy.le)).symm)


/-- On a finite set of tests one can dispense with the search over graph
families. For each endpoint pair separately, propagate the three required
triangle edges along the prefix agreements. This gives the least compatible
family. Its four-cliques are precisely the obstructions to realization. -/
theorem finite_forced_edges {I X : Type} [LinearOrder I] (lo hi : X → I)
    (T : X → X → X → Prop) (S : Finset X)
    (shape : ∀ x y z, T x y z → lo x < hi x ∧ hi x < hi z) :
    let test := fun x y z => x ∈ S ∧ y ∈ S ∧ z ∈ S ∧ T x y z
    let seed := fun i j z => ∃ x y, test x y z ∧
      ((i = lo x ∧ j = hi x) ∨ (i = lo x ∧ j = hi z) ∨ (i = hi x ∧ j = hi z))
    let link := fun i j q z => ∃ x y, test x y z ∧ (q = x ∨ q = y) ∧ i ≤ hi q ∧ j ≤ hi q
    let forced := fun i j q => ∃ z, seed i j z ∧ Relation.EqvGen (link i j) z q
    let fits := fun (g : X → SimpleGraph I) => ∀ x y z, test x y z →
      (g z).Adj (lo x) (hi x) ∧ (g z).Adj (lo x) (hi z) ∧ (g z).Adj (hi x) (hi z) ∧
      (∀ i ≤ hi x, ∀ j ≤ hi x, (g x).Adj i j ↔ (g z).Adj i j) ∧
      (∀ i ≤ hi y, ∀ j ≤ hi y, (g y).Adj i j ↔ (g z).Adj i j)
    ∃ g : X → SimpleGraph I,
      (∀ q i j, (g q).Adj i j ↔ forced i j q ∨ forced j i q) ∧ fits g ∧
      (∀ q i j, (g q).Adj i j →
        (∃ w ∈ S, i = lo w ∨ i = hi w) ∧ (∃ w ∈ S, j = lo w ∨ j = hi w)) ∧
      (∀ h, fits h → ∀ q, g q ≤ h q) ∧
      ((∀ q ∈ S, (g q).CliqueFree 4) ↔
        ∃ h, fits h ∧ ∀ q ∈ S, (h q).CliqueFree 4) := by
  classical
  intro test seed link forced fits
  have endpoints {i j q} (f : forced i j q) :
      i < j ∧ (∃ w ∈ S, i = lo w ∨ i = hi w) ∧ (∃ w ∈ S, j = lo w ∨ j = hi w) := by
    obtain ⟨z,⟨x,y,⟨xs,_,zs,t⟩,e⟩,_⟩ := f
    obtain ⟨ab,bc⟩ := shape x y z t
    rcases e with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨ab,⟨x,xs,Or.inl rfl⟩,⟨x,xs,Or.inr rfl⟩⟩
    · exact ⟨ab.trans bc,⟨x,xs,Or.inl rfl⟩,⟨z,zs,Or.inr rfl⟩⟩
    · exact ⟨bc,⟨x,xs,Or.inr rfl⟩,⟨z,zs,Or.inr rfl⟩⟩
  let g (q : X) : SimpleGraph I := {
    Adj := fun i j => forced i j q ∨ forced j i q
    symm := ⟨fun _ _ e => e.symm⟩
    loopless := ⟨fun _ e => (endpoints (e.elim id id)).1.false⟩ }
  have moveEdge {i j q z} (l : link i j q z) : forced i j q ↔ forced i j z := by
    have r := Relation.EqvGen.rel q z l
    constructor
    · rintro ⟨a,s,p⟩; exact ⟨a,s,p.trans _ _ _ r⟩
    · rintro ⟨a,s,p⟩; exact ⟨a,s,p.trans _ _ _ (r.symm _ _)⟩
  have gf : fits g := by
    intro x y z t
    have edge {i j} (s : seed i j z) : (g z).Adj i j :=
      Or.inl ⟨z,s,Relation.EqvGen.refl z⟩
    have same (q) (hq : q = x ∨ q = y) (i) (a : i ≤ hi q) (j) (b : j ≤ hi q) :
        (g q).Adj i j ↔ (g z).Adj i j :=
      or_congr (moveEdge ⟨x,y,t,hq,a,b⟩) (moveEdge ⟨x,y,t,hq,b,a⟩)
    exact ⟨edge ⟨x,y,t,Or.inl ⟨rfl,rfl⟩⟩,edge ⟨x,y,t,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩,
      edge ⟨x,y,t,Or.inr (Or.inr ⟨rfl,rfl⟩)⟩,same x (Or.inl rfl),same y (Or.inr rfl)⟩
  have least (h : X → SimpleGraph I) (ok : fits h) (q) : g q ≤ h q := by
    have transport {i j a b} (p : Relation.EqvGen (link i j) a b) :
        (h a).Adj i j ↔ (h b).Adj i j := by
      induction p with
      | rel a b l =>
        obtain ⟨x,y,t,rfl | rfl,ai,aj⟩ := l
        · exact (ok _ _ _ t).2.2.2.1 _ ai _ aj
        · exact (ok _ _ _ t).2.2.2.2 _ ai _ aj
      | refl => exact Iff.rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih ij => exact ih.trans ij
    have incl {i j} (f : forced i j q) : (h q).Adj i j := by
      obtain ⟨z,⟨x,y,t,e⟩,p⟩ := f
      apply (transport p).mp
      rcases e with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact (ok _ _ _ t).1
      · exact (ok _ _ _ t).2.1
      · exact (ok _ _ _ t).2.2.1
    intro i j e
    exact e.elim incl (fun f => (incl f).symm)
  refine ⟨g,fun _ _ _ => Iff.rfl,gf,?_,least,?_,?_⟩
  · intro q i j e
    exact e.elim (fun f => (endpoints f).2) (fun f => (endpoints f).2.symm)
  · exact fun free => ⟨g,gf,free⟩
  · rintro ⟨h,ok,free⟩ q hq
    exact (free q hq).anti (least h ok q)

end OMA.R_Erdos595_erdos_595_R3_H1_R1
