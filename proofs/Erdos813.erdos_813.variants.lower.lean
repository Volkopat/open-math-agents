import FormalConjectures.ErdosProblems.«813»

/-! # A power improvement for Erdős problem 813

This proof specializes the neighbourhood expansion in Section 2.1 of Matija Bučić and
Benny Sudakov, *Large independent sets from local considerations* (2023), to seven
vertices. Its explicit estimate is n ≤ 1000 k⁵ if the largest clique has size ≤ k².
No external Lean dependency is used.
-/

/- # Independent-set expansion for the seven-vertex problem

We specialize the neighbourhood-expansion argument of Bučić and Sudakov,
*Large independent sets from local considerations*, Theorem 1.2, to k=4.
-/

namespace OMA.Core813

open Finset
variable {V : Type*}

private noncomputable def reach (G : SimpleGraph V) (T S : Finset V) : Finset V := by
  classical
  exact T.filter fun z => ∃ y ∈ S, G.Adj y z

private theorem mem_reach {G : SimpleGraph V} {T S : Finset V} {z : V} :
    z ∈ reach G T S ↔ z ∈ T ∧ ∃ y ∈ S, G.Adj y z := by classical simp [reach]

private def Expands (G : SimpleGraph V) (T : Finset V) (d : ℕ) : Prop :=
  ∀ S ⊆ T, G.IsIndepSet S → d*S.card ≤ (reach G T S).card

/-- Remove one independent set with too few neighbours and its neighbourhood.
Maximality forces every independent set that remains to expand. -/
private theorem prune (G : SimpleGraph V) (T : Finset V) (b d : ℕ)
    (ind : ∀ S : Finset V, G.IsIndepSet S → S.card ≤ b) :
    ∃ X ⊆ T, T.card ≤ X.card + (d+1)*b ∧ Expands G X d := by
  classical
  let F := T.powerset.filter fun (S : Finset V) => G.IsIndepSet S ∧ (reach G T S).card ≤ d*S.card
  have empty : ∅ ∈ F := by simp [F, reach,SimpleGraph.isIndepSet_iff]
  obtain ⟨B, hB, maxB⟩ := F.exists_max_image card ⟨∅,empty⟩
  obtain ⟨bt, hbi, few⟩ := mem_filter.mp hB
  have bT := mem_powerset.mp bt
  let X := T \ (B ∪ reach G T B)
  have xT : X ⊆ T := sdiff_subset
  refine ⟨X,xT,?_,?_⟩
  · have h : T.card ≤ X.card + (B ∪ reach G T B).card := card_le_card_sdiff_add_card
    have hb := ind B hbi
    have hm := Nat.mul_le_mul_left d hb
    have hu := card_union_le B (reach G T B)
    nlinarith
  · intro S sx si
    by_contra! small
    have no (y) (hy : y ∈ S) : y ∉ B ∧ y ∉ reach G T B := by
      exact not_or.mp (fun h => (mem_sdiff.mp (sx hy)).2 (mem_union.mpr h))
    have cross {y z} (hy : y∈S) (hz : z∈B) : ¬ G.Adj z y := fun h =>
      (no y hy).2 (mem_reach.mpr ⟨xT (sx hy),z,hz,h⟩)
    have iu : G.IsIndepSet (B ∪ S : Finset V) := by
      intro y hy z hz ne
      rcases mem_union.mp hy with yb|ys <;> rcases mem_union.mp hz with zb|zs
      · exact hbi yb zb ne
      · exact cross zs yb
      · exact fun h => cross ys zb h.symm
      · exact si ys zs ne
    have sub : reach G T (B ∪ S) ⊆ reach G T B ∪ reach G X S := by
      intro z hz
      obtain ⟨zt,y,hy,adj⟩ := mem_reach.mp hz
      by_cases old : z∈reach G T B
      · exact mem_union_left _ old
      rcases mem_union.mp hy with yb|ys
      · exact False.elim (old (mem_reach.mpr ⟨zt,y,yb,adj⟩))
      apply mem_union_right
      exact mem_reach.mpr ⟨mem_sdiff.mpr ⟨zt, fun e => (mem_union.mp e).elim
        (fun zb => cross ys zb adj.symm) old⟩, y, ys, adj⟩
    have dis : Disjoint B S := Finset.disjoint_left.mpr fun _ h₁ h₂ => (no _ h₂).1 h₁
    have eqc := card_union_of_disjoint dis
    have cr := (card_le_card sub).trans (card_union_le _ _)
    have good : B ∪ S ∈ F := mem_filter.mpr ⟨mem_powerset.mpr (union_subset bT (sx.trans xT)),iu,
      by rw [eqc,mul_add]; omega⟩
    have maxc := maxB _ good
    change (B∪S).card ≤ B.card at maxc
    rw [eqc] at maxc
    have : S.card = 0 := by omega
    simp [this] at small

private theorem single {G : SimpleGraph V} [DecidableRel G.Adj] {T : Finset V} {d : ℕ} (exp : Expands G T d)
    {v : V} (hv : v ∈ T) : d ≤ (T.filter (G.Adj v)).card := by
  classical
  have := exp {v} (singleton_subset_iff.mpr hv) (by simp [SimpleGraph.isIndepSet_iff])
  simpa [reach] using this

theorem core [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 1 ≤ k)
    (ind : ∀ S : Finset V, G.IsIndepSet S → S.card ≤ k^2)
    (common : ∀ {v w : V}, G.Adj v w → G.IsIndepSet {u | G.Adj v u ∧ G.Adj w u})
    (hit : ∀ v, ∃ Z : Finset V, Z.card ≤ 3*k^2+1 ∧ ∀ u w z,
      G.Adj v u → G.Adj v w → G.Adj u w → G.Adj u z → G.Adj w z →
        u∈Z ∨ w∈Z ∨ z∈Z) :
    Fintype.card V ≤ 1000*k^5 := by
  classical
  by_contra! big
  have pow23 : k^2 ≤ k^3 := Nat.pow_le_pow_right hk (by decide)
  have pow25 : k^2 ≤ k^5 := Nat.pow_le_pow_right hk (by decide)
  have pos : 0 < k^3 := by positivity
  obtain ⟨Y, _, yLarge, yExp⟩ := prune G univ (k^2) (100*k^3) ind
  rw [card_univ] at yLarge
  have half : Fintype.card V < 2*Y.card := by nlinarith only [yLarge,big,pow25]
  let N (u : V) := univ.filter (G.Adj u)
  choose X sub sz exp using fun u : V => prune G (N u) (k^2) (4*k) ind
  have member {u z : V} (h : z ∈ X u) : G.Adj u z := (mem_filter.mp (sub u h)).2
  have richness (u : V) (hu : u ∈ Y) : 90*k^3 ≤ (X u).card := by
    have large := (single yExp hu).trans (card_le_card (t := N u) (fun z hz =>
      mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hz).2⟩))
    nlinarith only [large,sz u,pow23]
  obtain ⟨v,hv⟩ : ∃ v : V, 40*k^3 < (Y.filter fun u => v ∈ X u).card := by
    by_contra! none
    have edges := Finset.card_mul_le_card_mul (r := fun u v => v ∈ X u) (s := Y) (t := univ)
      (m := 90*k^3) (n := 40*k^3) (fun u hu => by
        simpa [bipartiteAbove] using richness u hu) (fun v _ => none v)
    rw [card_univ] at edges
    have : (2*Y.card)*(40*k^3) ≤ (Fintype.card V)*(40*k^3) := by
      refine le_trans ?_ edges
      nlinarith [Nat.zero_le (Y.card*k^3)]
    exact (Nat.mul_lt_mul_of_pos_right half (by positivity : 0<40*k^3)).not_ge this
  let U := Y.filter fun u => v ∈ X u
  obtain ⟨Z,zSmall,cover⟩ := hit v
  let S := U \ Z
  let D (u : V) := (X u).filter (G.Adj v)
  have vat {u} (hu : u ∈ U) : v ∈ X u := (mem_filter.mp hu).2
  have vu {u} (hu : u ∈ U) : G.Adj v u := (member (vat hu)).symm
  have many (u : V) (hu : u∈S) : 3*k ≤ (Z.filter fun w => w ∈ D u).card := by
    have uU := (mem_sdiff.mp hu).1
    have uz := (mem_sdiff.mp hu).2
    have dLarge : 4*k ≤ (D u).card := single (exp u) (vat uU)
    let R := D u \ Z
    have rx : R ⊆ X u := fun w hw => (mem_filter.mp (mem_sdiff.mp hw).1).1
    have ri : G.IsIndepSet R := by
      apply (common (vu uU)).mono
      intro w hw
      exact ⟨(mem_filter.mp (mem_sdiff.mp hw).1).2,member (rx hw)⟩
    have into : reach G (X u) R ⊆ Z := by
      intro z hz
      obtain ⟨zx,w,wr,wz⟩ := mem_reach.mp hz
      have wd := (mem_filter.mp (mem_sdiff.mp wr).1).2
      exact ((cover u w z (vu uU) wd (member (rx wr)) (member zx) wz).resolve_left uz).resolve_left
        (mem_sdiff.mp wr).2
    have short := (exp u R rx ri).trans (card_le_card into)
    have zk : Z.card ≤ 4*k^2 := by nlinarith [show 0<k^2 by positivity]
    have lr : R.card ≤ k := by
      by_contra! h
      have bad := Nat.mul_lt_mul_of_pos_left h (show 0 < 4*k by positivity)
      nlinarith only [bad,short,zk]
    have counts := card_sdiff_add_card_inter (D u) Z
    have eqn : Z.filter (fun w => w ∈ D u) = D u ∩ Z := by ext w; simp [and_comm]
    rw [eqn]
    dsimp [R] at lr
    omega
  have few (w : V) (hw : w∈Z) : (S.filter fun u => w∈D u).card ≤ k^2 := by
    apply ind
    by_cases vw : G.Adj v w
    · apply (common vw).mono
      intro u hu
      obtain ⟨uS,wd⟩ := mem_filter.mp hu
      exact ⟨vu (mem_sdiff.mp uS).1, (member (mem_filter.mp wd).1).symm⟩
    · have e : (S.filter fun u => w∈D u) = ∅ := eq_empty_iff_forall_notMem.mpr
          (fun u h => vw (mem_filter.mp (mem_filter.mp h).2).2)
      simp [e,SimpleGraph.isIndepSet_iff]
  have edges := Finset.card_mul_le_card_mul (r := fun u w => w∈D u) (s := S) (t := Z)
    (m := 3*k) (n := k^2) many few
  have su : U.card ≤ S.card + Z.card := card_le_card_sdiff_add_card
  change 40*k^3 < U.card at hv
  have zc : Z.card ≤ 4*k^2 := by nlinarith [show 0<k^2 by positivity]
  have sc : 30*k^3 < S.card := by omega
  have bad := Nat.mul_lt_mul_of_pos_right sc (show 0 < 3*k by positivity)
  have cap := Nat.mul_le_mul_right (k^2) zc
  nlinarith only [bad,edges,cap,Nat.zero_le (k^4)]

end OMA.Core813

/- The local seven-vertex obstruction in the complement graph, following
Bucić and Sudakov, *Large independent sets from local considerations*, §2.1. -/

open Finset

namespace OMA.Local813

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def Seven (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, S.card=7 → ∃ t⊆S, t.card=3 ∧ G.IsIndepSet (t : Set V)

private theorem triangle {a b c : V} (ab : G.Adj a b) (ac : G.Adj a c) (bc : G.Adj b c) :
    G.IsClique (({a,b,c} : Finset V) : Set V) := by
  intro x hx y hy ne
  simp only [Finset.mem_coe, mem_insert, mem_singleton] at hx hy
  rcases hx with rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl <;>
    first | contradiction | assumption | exact SimpleGraph.Adj.symm (by assumption)

private theorem overlap {t A : Finset V} (ht : G.IsIndepSet (t : Set V))
    (ha : G.IsClique (A : Set V)) : (t∩A).card≤1 := by
  apply card_le_one.mpr
  intro x hx y hy
  by_contra ne
  exact ht (mem_inter.mp hx).1 (mem_inter.mp hy).1 ne (ha (mem_inter.mp hx).2 (mem_inter.mp hy).2 ne)

private theorem two_cliques {t A B : Finset V} (ht : G.IsIndepSet (t : Set V))
    (ac : G.IsClique (A : Set V)) (bc : G.IsClique (B : Set V)) (sub : t⊆A∪B) :
    t.card≤2 := by
  have h : t ⊆ (t∩A)∪(t∩B) := by
    intro x hx
    obtain ha|hb := mem_union.mp (sub hx)
    · exact mem_union_left _ (mem_inter.mpr ⟨hx,ha⟩)
    · exact mem_union_right _ (mem_inter.mpr ⟨hx,hb⟩)
  have a := card_le_card h
  have b := card_union_le (t∩A) (t∩B)
  have c := overlap ht ac
  have d := overlap ht bc
  omega

private def Anchored (G : SimpleGraph V) (v : V) (A : Finset V) : Prop :=
  A.card=3 ∧ v∉A ∧ G.IsClique (A:Set V) ∧ ∃ z∈A, ∀u∈A,u≠z → G.Adj v u

private theorem tips {v a b : V} {A B : Finset V} (seven : Seven G)
    (ha : Anchored G v A) (hb : Anchored G v B) (disj : Disjoint A B)
    (aN : ∀x∈A,x≠a → G.Adj v x)
    (bN : ∀x∈B,x≠b → G.Adj v x) : ¬G.Adj a b := by
  intro ab
  have vs : v∉A∪B := by simp [ha.2.1,hb.2.1]
  obtain ⟨t,ts,tc,ti⟩ := seven (insert v (A∪B)) (by
    rw [card_insert_of_notMem vs,card_union_of_disjoint disj,ha.1,hb.1])
  have vt : v∈t := by
    by_contra hn
    have sub : t⊆A∪B := by
      intro x hx
      exact (mem_insert.mp (ts hx)).resolve_left (fun e => hn (e ▸ hx))
    have := two_cliques ti ha.2.2.1 hb.2.2.1 sub
    omega
  have sub : t⊆{v,a,b} := by
    intro x hx
    obtain rfl|hxab := mem_insert.mp (ts hx)
    · simp
    obtain hxa|hxb := mem_union.mp hxab
    · by_cases xa : x=a
      · simp [xa]
      · exact False.elim (ti vt hx (aN x hxa xa).ne (aN x hxa xa))
    · by_cases xb : x=b
      · simp [xb]
      · exact False.elim (ti vt hx (bN x hxb xb).ne (bN x hxb xb))
  have eq : t={v,a,b} := eq_of_subset_of_card_le sub (by
    have a' := card_insert_le v ({a,b}:Finset V)
    have b' := card_insert_le a ({b}:Finset V)
    simp only [card_singleton] at b'
    omega)
  exact ti (show a∈t by simp [eq]) (show b∈t by simp [eq]) ab.ne ab

variable [Fintype V]

theorem blockers (seven : Seven G) (k : ℕ)
    (ind : ∀s:Finset V,G.IsIndepSet (s:Set V) → s.card≤k^2) (v : V) :
    ∃ Z:Finset V, Z.card≤3*k^2+1 ∧ ∀u w z,G.Adj v u → G.Adj v w →
      G.Adj u w → G.Adj u z → G.Adj w z → u∈Z ∨ w∈Z ∨ z∈Z := by
  classical
  let F := (univ : Finset (Finset V)).filter (Anchored G v)
  let pd := fun (M:Finset (Finset V)) => ∀A∈M,∀B∈M,A≠B → Disjoint A B
  let C := F.powerset.filter pd
  have emp : ∅∈C := mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),by simp [pd]⟩
  obtain ⟨M,hm,maximal⟩ := exists_max_image C Finset.card ⟨_,emp⟩
  obtain ⟨ms,md⟩ := mem_filter.mp hm
  have allA (A) (hA:A∈M) : Anchored G v A := (mem_filter.mp (mem_powerset.mp ms hA)).2
  let tip (A : Finset V) := if h:A∈M then (allA A h).2.2.2.choose else v
  have pick (A) (h:A∈M) : tip A∈A ∧ ∀u∈A,u≠tip A → G.Adj v u := by
    simpa only [tip,dif_pos h] using (allA A h).2.2.2.choose_spec
  have inj : (M:Set (Finset V)).InjOn tip := by
    intro A ha B hb eq
    by_contra ne
    exact disjoint_left.mp (md A ha B hb ne) (pick A ha).1 (eq ▸ (pick B hb).1)
  have independent : G.IsIndepSet ((M.image tip : Finset V):Set V) := by
    intro x hx y hy ne
    obtain ⟨A,ha,rfl⟩ := mem_image.mp hx
    obtain ⟨B,hb,rfl⟩ := mem_image.mp hy
    exact tips seven (allA A ha) (allA B hb) (md A ha B hb (fun h => ne (congrArg tip h)))
      (pick A ha).2 (pick B hb).2
  have mc := ind _ independent
  rw [card_image_of_injOn inj] at mc
  let Z := insert v (M.biUnion id)
  refine ⟨Z,?_,?_⟩
  · have ub := card_biUnion_le (s:=M) (t:=id)
    have ue : (∑ A∈M,A.card)=M.card*3 := sum_const_nat (fun A h => (allA A h).1)
    have zi := card_insert_le v (M.biUnion id)
    change (M.biUnion id).card≤∑ A∈M,A.card at ub
    change (insert v (M.biUnion id)).card ≤ _
    omega
  · intro u w z vu vw uw uz wz
    by_contra! miss
    obtain ⟨nu,nw,nz⟩ := miss
    have vz : v≠z := by rintro rfl; exact nz (mem_insert_self _ _)
    let a : Finset V := {u,w,z}
    have aa : Anchored G v a := by
      refine ⟨by simp [a,uw.ne,uz.ne,wz.ne],by simp [a,vu.ne,vw.ne,vz],triangle uw uz wz,
        z,by simp [a],?_⟩
      intro x hx ne
      simp only [a,mem_insert,mem_singleton] at hx
      rcases hx with rfl|rfl|rfl <;> first | assumption | contradiction
    have disj (A) (ha:A∈M) : Disjoint a A := by
      apply disjoint_left.mpr
      intro x hx hA
      have xz : x∈Z := mem_insert_of_mem (mem_biUnion.mpr ⟨A,ha,hA⟩)
      simp only [a,mem_insert,mem_singleton] at hx
      rcases hx with rfl|rfl|rfl <;> contradiction
    have am : a∉M := by
      intro ha
      exact disjoint_left.mp (disj a ha) (show z∈a by simp [a]) (by simp [a])
    have ext : insert a M∈C := by
      refine mem_filter.mpr ⟨mem_powerset.mpr (insert_subset (mem_filter.mpr ⟨mem_univ _,aa⟩)
        (mem_powerset.mp ms)),?_⟩
      intro A hA B hB ne
      obtain rfl|hA := mem_insert.mp hA <;> obtain rfl|hB := mem_insert.mp hB
      · contradiction
      · exact disj _ hB
      · exact (disj _ hA).symm
      · exact md _ hA _ hB ne
    have bad := maximal _ ext
    rw [card_insert_of_notMem am] at bad
    omega

omit [Fintype V] in
private theorem common_of_no_four
    (free : ¬∃Q:Finset V,Q.card=4 ∧ G.IsClique (Q:Set V)) {v w:V} (vw:G.Adj v w) :
    G.IsIndepSet {u | G.Adj v u ∧ G.Adj w u} := by
  intro x hx y hy xy e
  obtain ⟨vx,wx⟩ := hx
  obtain ⟨vy,wy⟩ := hy
  apply free
  refine ⟨{v,w,x,y},by simp [vw.ne,vx.ne,vy.ne,wx.ne,wy.ne,xy],?_⟩
  intro a ha b hb ne
  simp only [Finset.mem_coe,mem_insert,mem_singleton] at ha hb
  rcases ha with rfl|rfl|rfl|rfl <;> rcases hb with rfl|rfl|rfl|rfl <;>
    first | contradiction | assumption | exact SimpleGraph.Adj.symm (by assumption)

private theorem four_small (seven : Seven G) (k:ℕ) (hk:1≤k)
    (ind : ∀s:Finset V,G.IsIndepSet (s:Set V) → s.card≤k^2)
    {Q:Finset V} (qc:Q.card=4) (qg:G.IsClique (Q:Set V)) :
    Fintype.card V≤1000*k^5 := by
  classical
  let P := (univ:Finset V) \ Q
  let nb (x:V) := P.filter fun y => G.Adj x y
  have low (x) (xp:x∈P) : (nb x).card≤k^2 := by
    apply ind
    intro u hu w hw ne uw
    obtain ⟨up,xu⟩ := mem_filter.mp hu
    obtain ⟨wp,xw⟩ := mem_filter.mp hw
    let T : Finset V := {x,u,w}
    have disj : Disjoint Q T := by
      apply disjoint_right.mpr
      intro y hy
      simp only [T,mem_insert,mem_singleton] at hy
      rcases hy with rfl|rfl|rfl
      · exact (mem_sdiff.mp xp).2
      · exact (mem_sdiff.mp up).2
      · exact (mem_sdiff.mp wp).2
    obtain ⟨t,ts,tc,ti⟩ := seven (Q∪T) (by
      rw [card_union_of_disjoint disj,qc]
      simp [T,xu.ne,xw.ne,ne])
    have := two_cliques ti qg (triangle xu xw uw) ts
    omega
  let I := P.powerset.filter fun s : Finset V => G.IsIndepSet (s : Set V)
  have emp : ∅∈I := mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),by simp⟩
  obtain ⟨S,hs,maximal⟩ := exists_max_image I Finset.card ⟨_,emp⟩
  obtain ⟨sp,si⟩ := mem_filter.mp hs
  have sub : P⊆S.biUnion (fun w => insert w (nb w)) := by
    intro x hx
    by_contra no
    have xs : x∉S := fun h => no (mem_biUnion.mpr ⟨x,h,mem_insert_self _ _⟩)
    have allw (w) (hw:w∈S) : ¬G.Adj w x := fun e =>
      no (mem_biUnion.mpr ⟨w,hw,mem_insert_of_mem (mem_filter.mpr ⟨hx,e⟩)⟩)
    have ext : insert x S∈I := by
      refine mem_filter.mpr ⟨mem_powerset.mpr (insert_subset hx (mem_powerset.mp sp)),?_⟩
      intro a ha b hb ne
      obtain ax|hA := mem_insert.mp ha
      · subst a
        have hB := (mem_insert.mp hb).resolve_left (Ne.symm ne)
        exact fun e => allw _ hB e.symm
      · obtain bx|hB := mem_insert.mp hb
        · subst b
          exact allw _ hA
        · exact si hA hB ne
    have := maximal _ ext
    rw [card_insert_of_notMem xs] at this
    omega
  have pbound : P.card ≤ k^2*(k^2+1) := calc
    P.card ≤ _ := card_le_card sub
    _ ≤ ∑w∈S, (insert w (nb w)).card := card_biUnion_le
    _ ≤ ∑_w∈S, (k^2+1) := sum_le_sum fun w hw => (card_insert_le _ _).trans
      (Nat.add_le_add_right (low w (mem_powerset.mp sp hw)) 1)
    _ = S.card*(k^2+1) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (ind S si)
  have ncard : P.card + Q.card = Fintype.card V := by
    simpa [P] using card_sdiff_add_card_eq_card (subset_univ Q)
  have two := Nat.pow_le_pow_right hk (show 2≤5 by decide)
  have four := Nat.pow_le_pow_right hk (show 4≤5 by decide)
  have one : 1≤k^5 := one_le_pow₀ hk
  nlinarith only [ncard,qc,pbound,two,four,one]

theorem finite (core : ∀ (n:ℕ) (G:SimpleGraph (Fin n)) (k:ℕ), 1≤k →
    (∀s:Finset (Fin n),G.IsIndepSet (s:Set (Fin n)) → s.card≤k^2) →
    (∀ {v w}, G.Adj v w → G.IsIndepSet {u | G.Adj v u ∧ G.Adj w u}) →
    (∀v, ∃Z:Finset (Fin n), Z.card≤3*k^2+1 ∧ ∀u w z, G.Adj v u → G.Adj v w →
      G.Adj u w → G.Adj u z → G.Adj w z → u∈Z ∨ w∈Z ∨ z∈Z) →
    Fintype.card (Fin n) ≤ 1000*k^5) (n k:ℕ) (hk:1≤k) (ha:Erdos813.h n≤k^2) :
    n≤1000*k^5 := by
  classical
  obtain ⟨H,sevenH,hnum⟩ := Nat.sInf_mem
    (s:={m:ℕ | ∃H:SimpleGraph (Fin n),Erdos813.EverySevenHasTriangle H ∧ H.cliqueNum=m})
    ⟨_,⊤,Erdos813.everySevenHasTriangle_top n,rfl⟩
  let G := Hᶜ
  have seven : Seven G := by
    intro S c
    obtain ⟨t,ts,tc⟩ := sevenH S c
    exact ⟨t,ts,tc.card_eq,by simpa [G] using tc.isClique⟩
  have ind (s:Finset (Fin n)) (si:G.IsIndepSet (s:Set _)) : s.card≤k^2 := by
    have cl : H.IsClique (s:Set _) := by simpa [G] using si
    exact cl.card_le_cliqueNum.trans (hnum ▸ ha)
  by_cases contains : ∃Q:Finset (Fin n), Q.card=4 ∧ G.IsClique (Q:Set _)
  · obtain ⟨Q,qc,qg⟩ := contains
    simpa using four_small seven k hk ind qc qg
  · simpa using core n G k hk ind (fun h => common_of_no_four contains h) (blockers seven k ind)

end OMA.Local813

/- # Converting the finite obstruction into an exponent -/

open Filter Asymptotics Erdos813

namespace OMA.End813

theorem lower (finite_bound : ∀ n k : ℕ, 1 ≤ k → h n ≤ k^2 → n ≤ 1000*k^5) :
    ∃ c > (0 : ℝ), (fun n : ℕ => (n:ℝ)^(1/3+c:ℝ)) =O[atTop] (fun n => (h n:ℝ)) := by
  refine ⟨1/15, by norm_num, (isBigO_iff).mpr ⟨1000, ?_⟩⟩
  filter_upwards [eventually_gt_atTop 1000] with n hn
  have pos : 0 < h n := by
    by_contra! hz
    have := finite_bound n 1 (by decide) (by omega)
    norm_num at this
    omega
  let k := (h n).sqrt+1
  have hk : n ≤ 1000*k^5 :=
    finite_bound n k (by dsimp [k]; omega) (Nat.lt_succ_sqrt' _).le
  have hs := Nat.sqrt_pos.mpr pos
  have twice : k ≤ 2*(h n).sqrt := by dsimp [k]; omega
  have ksq : k^2 ≤ 4*h n := by
    calc
      k^2 ≤ (2*(h n).sqrt)^2 := by gcongr
      _ = 4*(h n).sqrt^2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.sqrt_le' _)
  have powNat : n^2 ≤ (1000*h n)^5 := by
    calc
      n^2 ≤ (1000*k^5)^2 := by gcongr
      _ = 1000000*(k^2)^5 := by ring
      _ ≤ 1000000*(4*h n)^5 := by gcongr
      _ ≤ (1000*h n)^5 := by ring_nf; omega
  have powers : (n:ℝ)^2 ≤ (1000*(h n:ℝ))^5 := by exact_mod_cast powNat
  have main : (n:ℝ)^(2/5:ℝ) ≤ 1000*(h n:ℝ) := by
    apply (Real.rpow_le_rpow_iff (by positivity) (by positivity) (z := (5:ℝ)) (by norm_num)).mp
    rw [← Real.rpow_mul (by positivity)]
    norm_num
    exact powers
  change ‖(n:ℝ)^(1/3+1/15:ℝ)‖ ≤ 1000*‖(h n:ℝ)‖
  rw [show (1/3+1/15:ℝ) = 2/5 by norm_num, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (by positivity)]
  exact main

end OMA.End813

theorem OMA.solution : type_of% @Erdos813.erdos_813.variants.lower :=
  OMA.End813.lower (OMA.Local813.finite (fun _ => OMA.Core813.core))
