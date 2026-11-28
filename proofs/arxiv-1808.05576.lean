import OMAStatements.S_arxiv_1808_05576


/-!
# A sharp bound for domination counts in a graph and its complement

This is Conjecture 1.2 of Lauren Keough and David Shane (arXiv:1808.05576).
They checked the small orders. Sanh proved the bipartite case; a November 19
research note by mxym (mxym/math#137) treated all orders from 160. The OMA
statement is due to pyaf.

Separate dominating subsets by whether they meet both parts of a disjoint
union. For graphs connected in both colors, Seinsche's characterization
supplies an induced path. For each subset of a chosen five- or six-vertex
extension, the eligible vertex with the largest exterior neighborhood gives
a lower bound for the number of failures with that trace. Summing over
disjoint traces and checking the bounded degree offsets proves the result.
The finite inequalities are certified by ordinary kernel computation.
-/


section

open Finset
open OMA.S_arxiv_1808_05576

namespace KeoughShane

private def positiveSubs {V : Type} [DecidableEq V] (A : Finset V) : Finset (Finset V) :=
  A.powerset.erase ∅

private lemma mem_positiveSubs {V : Type} [DecidableEq V] {A S : Finset V} :
    S ∈ positiveSubs A ↔ S ≠ ∅ ∧ S ⊆ A := by
  simp [positiveSubs]

private lemma positiveSubs_card {V : Type} [DecidableEq V] (A : Finset V) :
    (positiveSubs A).card = 2 ^ A.card - 1 := by
  classical
  rw [positiveSubs, card_erase_of_mem (by simp), card_powerset]

private def internallyDom {V : Type} (G : SimpleGraph V) (A S : Finset V) : Prop :=
  ∀ v ∈ A, v ∈ S ∨ ∃ u ∈ S, G.Adj v u

private noncomputable def domPart {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (A : Finset V) : Finset (Finset V) := by
  classical
  exact (positiveSubs A).filter (internallyDom G A)

private lemma mem_domPart {V : Type} [DecidableEq V] {G : SimpleGraph V}
    {A S : Finset V} :
    S ∈ domPart G A ↔ (S ≠ ∅ ∧ S ⊆ A) ∧ internallyDom G A S := by
  classical
  simp [domPart,mem_positiveSubs]

private lemma domPart_le {V : Type} [DecidableEq V] (G : SimpleGraph V) (A : Finset V) :
    (domPart G A).card ≤ 2 ^ A.card - 1 := by
  classical
  rw [← positiveSubs_card]
  exact Finset.card_le_card (Finset.filter_subset ..)

private def cliquePart {V : Type} (G : SimpleGraph V) (A : Finset V) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ≠ y → G.Adj x y

private lemma domPart_compl_clique {V : Type} [DecidableEq V] {G : SimpleGraph V}
    {A : Finset V} (h : cliquePart G A) : (domPart Gᶜ A).card ≤ 1 := by
  classical
  have hs : domPart Gᶜ A ⊆ {A} := by
    intro S hS
    rcases mem_domPart.mp hS with ⟨⟨_, hsub⟩, hdom⟩
    apply Finset.mem_singleton.mpr
    apply Finset.Subset.antisymm hsub
    intro x hx
    rcases hdom x hx with hxS | ⟨y,hy,hxy⟩
    · exact hxS
    · exact False.elim (hxy.2 (h x hx y (hsub hy) hxy.1))
  simpa using Finset.card_le_card hs

private lemma domPart_nonclique {V : Type} [DecidableEq V] {G : SimpleGraph V}
    {A : Finset V} (h : ¬cliquePart G A) :
    (domPart G A).card + 2 ≤ 2 ^ A.card - 1 := by
  classical
  unfold cliquePart at h
  push Not at h
  obtain ⟨x,hx,y,hy,hne,hna⟩ := h
  have h1 : ({x} : Finset V) ∈ positiveSubs A := mem_positiveSubs.mpr ⟨by simp, by simpa⟩
  have h2 : ({y} : Finset V) ∈ (positiveSubs A).erase {x} := by
    apply Finset.mem_erase.mpr
    exact ⟨by simpa using hne.symm, mem_positiveSubs.mpr ⟨by simp, by simpa⟩⟩
  have hs : domPart G A ⊆ ((positiveSubs A).erase {x}).erase {y} := by
    intro S hS
    obtain ⟨hpos, hdom⟩ := mem_domPart.mp hS
    apply Finset.mem_erase.mpr
    refine ⟨?_,Finset.mem_erase.mpr ⟨?_,mem_positiveSubs.mpr hpos⟩⟩
    · rintro rfl
      simpa [internallyDom, hne, hna] using hdom x hx
    · rintro rfl
      simpa [internallyDom, Ne.symm hne, mt SimpleGraph.Adj.symm hna] using hdom y hy
  have hh := Finset.card_le_card hs
  rw [Finset.card_erase_of_mem h2, Finset.card_erase_of_mem h1, positiveSubs_card] at hh
  have hh2 := Finset.card_pos.mpr ⟨_,h2⟩
  rw [Finset.card_erase_of_mem h1,positiveSubs_card] at hh2
  omega

private noncomputable def merged {V : Type} [DecidableEq V] (X Y : Finset (Finset V)) :
    Finset (Finset V) := (X ×ˢ Y).image (fun p => p.1 ∪ p.2)

private lemma merged_le {V : Type} [DecidableEq V] (X Y : Finset (Finset V)) :
    (merged X Y).card ≤ X.card * Y.card := by
  classical
  simpa [merged] using (Finset.card_image_le (s := X ×ˢ Y) (f := fun p => p.1 ∪ p.2))

private lemma mem_merged {V : Type} [DecidableEq V] {X Y : Finset (Finset V)}
    {A B : Finset V} (hA : A ∈ X) (hB : B ∈ Y) : A ∪ B ∈ merged X Y := by
  exact Finset.mem_image.mpr ⟨(A,B),Finset.mem_product.mpr ⟨hA,hB⟩,rfl⟩


private lemma restrictDom {n : ℕ} {G : SimpleGraph (Fin n)} {A B S : Finset (Fin n)}
    (ha : A.Nonempty) (hu : A ∪ B = univ) (hc : ∀ x ∈ A, ∀ y ∈ B, ¬G.Adj x y)
    (hs : ∀ x, x ∈ S ∨ ∃ y ∈ S, G.Adj x y) : S ∩ A ∈ domPart G A := by
  classical
  have core : internallyDom G A (S ∩ A) := by
    intro x hx
    rcases hs x with h | ⟨y,hy,hxy⟩
    · exact Or.inl (mem_inter.mpr ⟨h,hx⟩)
    · apply Or.inr
      refine ⟨y,mem_inter.mpr ⟨hy,?_⟩,hxy⟩
      have hyu : y ∈ A ∪ B := hu ▸ mem_univ y
      exact (mem_union.mp hyu).resolve_right (fun hB => hc x hx y hB hxy)
  apply mem_domPart.mpr
  refine ⟨⟨?_,Finset.inter_subset_right⟩,core⟩
  obtain ⟨x,hx⟩ := ha
  rcases core x hx with hm | ⟨_,hm,_⟩
  all_goals exact Finset.nonempty_iff_ne_empty.mp ⟨_,hm⟩

private lemma dom_join_counts {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (ha : A.Nonempty) (hb : B.Nonempty)
    (hu : A ∪ B = univ) (hc : ∀ x ∈ A, ∀ y ∈ B, ¬G.Adj x y) :
    numDom G ≤ (domPart G A).card * (domPart G B).card ∧
    numDom Gᶜ ≤ (2^A.card-1)*(2^B.card-1)+(domPart Gᶜ A).card+(domPart Gᶜ B).card := by
  classical
  have cover (S : Finset (Fin n)) : S ∩ A ∪ S ∩ B = S := by
    rw [← inter_union_distrib_left,hu,inter_univ]
  constructor
  · apply le_trans (Finset.card_le_card (t := merged (domPart G A) (domPart G B)) ?_) (merged_le ..)
    intro S hS
    have hs := (Finset.mem_filter.mp hS).2
    rw [← cover S]
    apply mem_merged
    · exact restrictDom ha hu hc hs
    · exact restrictDom hb (by rwa [union_comm]) (fun _ hB _ hA hxy => hc _ hA _ hB hxy.symm) hs
  · let M := merged (positiveSubs A) (positiveSubs B)
    have hM : M.card ≤ (2^A.card-1)*(2^B.card-1) := by
      simpa only [M,positiveSubs_card] using (merged_le (positiveSubs A) (positiveSubs B))
    have pure (S X : Finset (Fin n)) (hn : S ≠ ∅) (hSX : S ⊆ X)
        (hs : ∀ x, x ∈ S ∨ ∃ y ∈ S, Gᶜ.Adj x y) : S ∈ domPart Gᶜ X :=
      mem_domPart.mpr ⟨⟨hn,hSX⟩,fun x _ => hs x⟩
    have bound : numDom Gᶜ ≤ ((M ∪ domPart Gᶜ A) ∪ domPart Gᶜ B).card := by
      apply Finset.card_le_card
      intro S hS
      have hs := (Finset.mem_filter.mp hS).2
      have hn : S ≠ ∅ := by
        obtain ⟨x,_⟩ := ha
        rcases hs x with hm | ⟨_,hm,_⟩
        all_goals exact Finset.nonempty_iff_ne_empty.mp ⟨_,hm⟩
      by_cases hA : S ∩ A = ∅
      · apply mem_union_right
        apply pure _ _ hn _ hs
        have he := cover S
        rw [hA,empty_union] at he
        exact he ▸ Finset.inter_subset_right
      by_cases hB : S ∩ B = ∅
      · apply mem_union_left
        apply mem_union_right
        apply pure _ _ hn _ hs
        have he := cover S
        rw [hB,union_empty] at he
        exact he ▸ Finset.inter_subset_right
      apply mem_union_left
      apply mem_union_left
      rw [← cover S]
      apply mem_merged
      · exact mem_positiveSubs.mpr ⟨hA,Finset.inter_subset_right⟩
      · exact mem_positiveSubs.mpr ⟨hB,Finset.inter_subset_right⟩
    exact bound.trans <| (card_union_le ..).trans <| Nat.add_le_add_right
      ((card_union_le ..).trans (Nat.add_le_add_right hM _)) _

private theorem sumPowEdge (u v : ℕ) :
    2^u + 2^v ≤ 1+2^(u+v) := by
  have hu : 1 ≤ 2^u := Nat.one_le_two_pow
  have hv : 1 ≤ 2^v := Nat.one_le_two_pow
  rw [pow_add]
  obtain ⟨x,hx⟩ := Nat.exists_eq_add_of_le hu
  obtain ⟨y,hy⟩ := Nat.exists_eq_add_of_le hv
  rw [hx,hy]
  nlinarith

private theorem balancedPowerSum (a b : ℕ) :
    2 ^ ((a+b)/2) + 2 ^ (a+b-(a+b)/2) ≤ 2^a+2^b := by
  have base (j : ℕ) : 2^(j/2)+2^(j-j/2) ≤ 1+2^j := by
    have h := sumPowEdge (j/2) (j-j/2)
    rwa [show j/2+(j-j/2)=j by omega] at h
  induction a generalizing b with
  | zero => simpa only [Nat.zero_add, pow_zero] using base b
  | succ a ih =>
    cases b with
    | zero => simpa only [Nat.add_zero,pow_zero,Nat.add_comm 1] using base (a+1)
    | succ b =>
      have h1 : (a+1+(b+1))/2=(a+b)/2+1 := by omega
      have h2 : a+1+(b+1)-(a+1+(b+1))/2=(a+b-(a+b)/2)+1 := by omega
      rw [h2,h1]
      simp only [pow_succ]
      have hh := ih b
      omega


private lemma predPowProduct (a b : ℕ) :
    (2^a-1)*(2^b-1)+(2^a+2^b) = 2^(a+b)+1 := by
  have ha : 2^a-1+1=2^a := Nat.sub_add_cancel Nat.one_le_two_pow
  have hb : 2^b-1+1=2^b := Nat.sub_add_cancel Nat.one_le_two_pow
  calc
    _ = (2^a-1+1)*(2^b-1+1)+1 := by nlinarith only [ha,hb]
    _ = _ := by rw [ha,hb,pow_add]

private lemma powBalancing (a b n : ℕ) (hn : a+b=n) :
    let A := 2^a-1
    let B := 2^b-1
    let C := 2^(n/2)-1
    let D := 2^(n-n/2)-1
    A*B ≤ C*D ∧ 2*(A*B)+A+1 ≤ 2*(C*D)+2+2*B := by
  dsimp only
  have e1 := predPowProduct a b
  have e2 := predPowProduct (n/2) (n-n/2)
  rw [hn] at e1
  rw [show n/2+(n-n/2)=n by omega] at e2
  have h1 := balancedPowerSum a b
  rw [hn] at h1
  have h2 := balancedPowerSum a (b+2)
  rw [show a+(b+2)-(a+(b+2))/2=(n-n/2)+1 by omega,
    show (a+(b+2))/2=n/2+1 by omega,show b+2=(b+1)+1 by omega] at h2
  simp only [pow_succ] at h2
  have ha : 1 ≤ 2^a := Nat.one_le_two_pow
  have hb : 1 ≤ 2^b := Nat.one_le_two_pow
  omega

private lemma distinctLoss (a b p q : ℕ) (hp : p+2 ≤ a) (hq : q+2 ≤ b) :
    p*q+a+b ≤ a*b+1 := by
  obtain ⟨i,hi⟩ := Nat.exists_eq_add_of_le (show 1 ≤ a by omega)
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le (show 1 ≤ b by omega)
  have pq : p*q ≤ i*j := Nat.mul_le_mul (by omega) (by omega)
  rw [hi,hj]
  nlinarith only [pq]

private lemma oneLoss (a b p q : ℕ) (hp : p+2 ≤ a) (hq : q ≤ b) :
    p*q+2*b ≤ a*b := by
  calc
    _ ≤ p*b + 2*b := by gcongr
    _ = (p+2)*b := by ring
    _ ≤ _ := Nat.mul_le_mul_right b hp

theorem disconnected_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B : Finset (Fin n)) (ha : A.Nonempty) (hb : B.Nonempty)
    (hd : Disjoint A B) (hu : A ∪ B = univ) (hc : ∀ x ∈ A, ∀ y ∈ B, ¬G.Adj x y) :
    numDom G + numDom Gᶜ ≤ 2*(2^(n/2)-1)*(2^(n-n/2)-1)+2 := by
  classical
  have hab : A.card+B.card=n := by
    rw [← Finset.card_union_of_disjoint hd,hu,card_univ,Fintype.card_fin]
  obtain ⟨hr,hb'⟩ := dom_join_counts G A B ha hb hu hc
  have pa := domPart_le G A
  have pb := domPart_le G B
  have qa := domPart_le Gᶜ A
  have qb := domPart_le Gᶜ B
  obtain ⟨hprod,hone⟩ := powBalancing A.card B.card n hab
  rw [Nat.mul_assoc]
  by_cases ca : cliquePart G A
  · have qa' := domPart_compl_clique ca
    by_cases cb : cliquePart G B
    · have qb' := domPart_compl_clique cb
      have pq := Nat.mul_le_mul pa pb
      omega
    · have pb' := domPart_nonclique cb
      have hh := oneLoss _ _ _ _ pb' pa
      obtain ⟨_,hs⟩ := powBalancing B.card A.card n (by omega)
      rw [Nat.mul_comm (domPart G B).card, Nat.mul_comm (2^B.card-1)] at hh
      rw [Nat.mul_comm (2^B.card-1)] at hs
      omega
  · have pa' := domPart_nonclique ca
    by_cases cb : cliquePart G B
    · have qb' := domPart_compl_clique cb
      have hh := oneLoss _ _ _ _ pa' pb
      omega
    · have pb' := domPart_nonclique cb
      have hh := distinctLoss _ _ _ _ pa' pb'
      omega

theorem not_connected_bound {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hg : ¬G.Connected) :
    numDom G + numDom Gᶜ ≤ 2*(2^(n/2)-1)*(2^(n-n/2)-1)+2 := by
  classical
  have non : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hpre : ¬ G.Preconnected := fun h => hg (G.connected_iff.mpr ⟨h,non⟩)
  change ¬ ∀ x y, G.Reachable x y at hpre
  push Not at hpre
  obtain ⟨x,y,hxy⟩ := hpre
  let A := univ.filter (G.Reachable x)
  apply disconnected_bound G A Aᶜ ⟨x,by simp [A]⟩ ⟨y,by simpa [A] using hxy⟩ disjoint_compl_right (by simp)
  intro i hi j hj hij
  have hxi : G.Reachable x i := (mem_filter.mp hi).2
  exact (mem_compl.mp hj) (mem_filter.mpr ⟨mem_univ _,hxi.trans hij.reachable⟩)

end KeoughShane

end

section

/-! Seinsche's characterization of finite graphs without an induced four-vertex path.
We take a largest induced subgraph admitting a nontrivial edge-free cut. -/

namespace OMA
open Finset SimpleGraph

private def ksCut {V : Type*} (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∃ p : V → Prop, (∃ a ∈ s, p a) ∧ (∃ b ∈ s, ¬p b) ∧
    ∀ a ∈ s, ∀ b ∈ s, p a → ¬p b → ¬G.Adj a b

private theorem ksCross {V : Type*} {G : SimpleGraph V}
    (h : G.Connected) (p : V → Prop) {a b : V} (ha : p a) (hb : ¬p b) :
    ∃ z w, p z ∧ ¬p w ∧ G.Adj z w := by
  obtain ⟨walk⟩ := h a b
  obtain ⟨d, _, hz, hw⟩ := walk.exists_boundary_dart {z | p z} ha hb
  exact ⟨d.toProd.1, d.toProd.2, hz, hw, d.adj⟩

private theorem ksCutPath {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {s : Finset V} {x y : V} (hx : x ∉ s) (hy : y ∈ s) (hxy : ¬G.Adj x y)
    (noCut : ¬ksCut G (insert x s))
    (p : V → Prop) (py : p y) (pb : ∃ b ∈ s, ¬p b)
    (sep : ∀ a ∈ s, ∀ b ∈ s, p a → ¬p b → ¬G.Adj a b) :
    ∃ a b c d : V, a ≠ c ∧ a ≠ d ∧ b ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b d := by
  classical
  obtain ⟨v, hv, hpv⟩ := pb
  have hb : ∃ d ∈ s, ¬p d ∧ G.Adj x d := by
    by_contra! hn
    apply noCut
    refine ⟨fun z => z = x ∨ p z, ⟨x, mem_insert_self .., Or.inl rfl⟩,
      ⟨v, mem_insert_of_mem hv, ?_⟩, ?_⟩
    · exact fun h => h.elim (fun h => hx (h ▸ hv)) hpv
    intro a ha b hb hpa hpb
    have bne : b ≠ x := fun he => hpb (Or.inl he)
    have bs : b ∈ s := (mem_insert.mp hb).resolve_left bne
    have nb : ¬p b := fun h => hpb (Or.inr h)
    rcases eq_or_ne a x with rfl|hne
    · exact hn b bs nb
    · exact sep a ((mem_insert.mp ha).resolve_left hne) b bs (hpa.resolve_left hne) nb
  obtain ⟨d, ds, nd, hxd⟩ := hb
  have hab : ∃ a ∈ s, ∃ b ∈ s, p a ∧ p b ∧ ¬G.Adj x a ∧ G.Adj x b ∧ G.Adj a b := by
    by_contra! h
    apply noCut
    refine ⟨fun a => a ∈ s ∧ p a ∧ ¬G.Adj x a,
      ⟨y, mem_insert_of_mem hy, hy, py, hxy⟩,
      ⟨x, mem_insert_self .., fun h => hx h.1⟩, ?_⟩
    rintro a _ b hbin ⟨ha, pa, nxa⟩ nb
    rcases mem_insert.mp hbin with rfl|hb
    · exact fun e => nxa e.symm
    by_cases pb : p b
    · by_cases xb : G.Adj x b
      · exact h a ha b hb pa pb nxa xb
      · exact False.elim (nb ⟨hb,pb,xb⟩)
    · exact sep a ha b hb pa pb
  obtain ⟨a, ha, b, hb, pa, pb, nxa, xb, ab⟩ := hab
  exact ⟨a,b,x,d,fun e => hx (e ▸ ha),fun e => nd (e ▸ pa),fun e => nd (e ▸ pb),
    ab,xb.symm,hxd,fun e => nxa e.symm,sep a ha d ds pa nd,sep b hb d ds pb nd⟩

private theorem ksVecPath {V : Type*} {G : SimpleGraph V} {a b c d : V}
    (ac : a ≠ c) (ad : a ≠ d) (bd : b ≠ d)
    (ab : G.Adj a b) (bc : G.Adj b c) (cd : G.Adj c d)
    (nac : ¬G.Adj a c) (nad : ¬G.Adj a d) (nbd : ¬G.Adj b d) :
    ∃ f : Fin 4 ↪ V, ∀ i j, G.Adj (f i) (f j) ↔
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  let f : Fin 4 → V := ![a,b,c,d]
  have eqs : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f, ab.ne, bc.ne, cd.ne]
  refine ⟨⟨f,eqs⟩, ?_⟩
  intro i j
  change G.Adj (f i) (f j) ↔ _
  fin_cases i <;> fin_cases j <;> simp_all [f, G.adj_comm]

/-- Seinsche's induced-path theorem for a connected and co-connected finite graph. -/
theorem ksSeinsche {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n))
    (hG : G.Connected) (hB : Gᶜ.Connected) :
    ∃ f : Fin 4 ↪ Fin n, ∀ i j, G.Adj (f i) (f j) ↔
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  classical
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨u⟩ := hG.nonempty
  obtain ⟨v, hv⟩ := hB.preconnected.exists_adj_of_nontrivial u
  obtain ⟨uv, nuv⟩ := (G.compl_adj u v).mp hv
  let cuts := (univ : Finset (Finset (Fin n))).filter (ksCut G)
  have init : ksCut G {u,v} := by
    refine ⟨(· = u), ⟨u, by simp, rfl⟩, ⟨v, by simp, uv.symm⟩, ?_⟩
    rintro a _ b hb rfl nb
    simp only [mem_insert, mem_singleton] at hb
    exact (hb.resolve_left nb) ▸ nuv
  obtain ⟨s, hs, maxS⟩ := exists_max_image cuts card
    ⟨{u,v}, mem_filter.mpr ⟨mem_univ _, init⟩⟩
  have sep := (mem_filter.mp hs).2
  obtain ⟨p, ⟨a,ha,pa⟩, ⟨b,hb,npb⟩, sep⟩ := sep
  have outside : ∃ b, b ∉ s := by
    by_contra! hall
    obtain ⟨z,w,pz,nw,zw⟩ := ksCross hG p pa npb
    exact sep z (hall z) w (hall w) pz nw zw
  obtain ⟨t,ht⟩ := outside
  obtain ⟨y,x,hy,hx,yx⟩ := ksCross hB (· ∈ s) ha ht
  have hxy := ((G.compl_adj x y).mp yx.symm).2
  have noCut : ¬ksCut G (insert x s) := by
    intro h
    have hh := maxS (insert x s) (mem_filter.mpr ⟨mem_univ _,h⟩)
    rw [card_insert_of_notMem hx] at hh
    omega
  have getPath : ∃ a b c d : Fin n, a ≠ c ∧ a ≠ d ∧ b ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b d := by
    by_cases py : p y
    · exact ksCutPath hx hy hxy noCut p py ⟨b,hb,npb⟩ sep
    · apply ksCutPath hx hy hxy noCut (fun z => ¬p z) py ⟨a,ha,not_not_intro pa⟩
      intro z hz w hw nz nw e
      exact sep w hw z hz (not_not.mp nw) nz e.symm
  obtain ⟨u₀,u₁,u₂,u₃,ac,ad,bd,ab,bc,cd,nac,nad,nbd⟩ := getPath
  exact ksVecPath ac ad bd ab bc cd nac nad nbd

end OMA

end

section

namespace KeoughShane

open Finset

def traceScore {m : ℕ} (r : Fin m → Finset (Fin m)) (a : Fin m → ℕ) : ℕ :=
  ∑ T : Finset (Fin m), univ.sup (fun i : Fin m =>
    if T ⊆ r i then 2^(5 + a i - (r i).card) else 0)

def otherRows {m : ℕ} (r : Fin m → Finset (Fin m)) (i : Fin m) : Finset (Fin m) :=
  (univ.erase i) \ r i

end KeoughShane

end

section

namespace KeoughShane

open Finset OMA.S_arxiv_1808_05576

def restrictSet {n m : ℕ} (f : Fin m ↪ Fin n) (S : Finset (Fin n)) : Finset (Fin m) :=
  univ.filter (fun i => f i ∈ S)

noncomputable def graphRows {n m : ℕ} (G : SimpleGraph (Fin n)) (f : Fin m ↪ Fin n)
    (i : Fin m) : Finset (Fin m) := by
  classical
  exact restrictSet f (G.neighborFinset (f i))

noncomputable def failures {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Finset (Fin n)) := by
  classical
  exact univ.filter (fun S => ∃ x, S ⊆ G.neighborFinset x)

theorem mem_failures {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    S ∈ failures G ↔ ∃ x, ∀ y ∈ S, G.Adj x y := by
  classical
  simp only [failures,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨x,fun y hy => (G.mem_neighborFinset x y).mp (hx hy)⟩
  · rintro ⟨x,hx⟩
    exact ⟨x,fun y hy => (G.mem_neighborFinset x y).mpr (hx y hy)⟩

theorem count_complement {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    numDom G + (failures Gᶜ).card = 2^n := by
  classical
  let P (S : Finset (Fin n)) := ∀ v, v ∈ S ∨ ∃ u ∈ S, G.Adj v u
  have h : failures Gᶜ = univ.filter (fun S => ¬ P S) := by
    ext S
    simp only [mem_failures,mem_filter,mem_univ,true_and, P,not_forall, not_or, not_exists]
    constructor
    · rintro ⟨x,hx⟩
      refine ⟨x,fun h => (Gᶜ.loopless.irrefl x) (hx x h), ?_⟩
      intro u hu
      exact (hx u hu.1).2 hu.2
    · rintro ⟨x,hx,ha⟩
      exact ⟨x,fun y hy => ⟨fun e => hx (e ▸ hy),fun had => ha y ⟨hy,had⟩⟩⟩
  rw [h]
  change (univ.filter P).card + _ = _
  rw [card_filter_add_card_filter_not]
  simp

theorem graphRows_compl {n m : ℕ} (G : SimpleGraph (Fin n)) (f : Fin m ↪ Fin n) :
    graphRows Gᶜ f = otherRows (graphRows G f) := by
  classical
  funext i
  ext j
  simp [graphRows,otherRows,restrictSet,ne_comm]

theorem trace_inside {n m : ℕ} (f : Fin m ↪ Fin n) (N : Finset (Fin n)) :
    (restrictSet f N).map f = (univ.map f) ∩ N := by
  ext y
  simp only [restrictSet,mem_map,mem_filter,mem_univ,true_and,mem_inter]
  constructor
  · rintro ⟨x,h,rfl⟩
    exact ⟨⟨x,rfl⟩,h⟩
  · rintro ⟨⟨x,rfl⟩,h⟩
    exact ⟨x,h,rfl⟩

theorem trace_fiber_card {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (f : Fin m ↪ Fin n)
    (i : Fin m) (T : Finset (Fin m)) (ht : T ⊆ graphRows G f i) :
    2^((G.degree (f i)) - (graphRows G f i).card) ≤
      ((failures G).filter (fun S => restrictSet f S = T)).card := by
  classical
  let N := G.neighborFinset (f i)
  let extN := N \ (univ.map f)
  let send (A : Finset (Fin n)) := T.map f ∪ A
  have card_ext : extN.card = G.degree (f i) - (graphRows G f i).card := by
    have eqrows : graphRows G f i = restrictSet f N := by
      ext j
      simp [graphRows,restrictSet,N]
    rw [eqrows,←Finset.card_map f]
    simp [extN,Finset.card_sdiff,trace_inside,inter_comm,N]
  rw [←card_ext,←Finset.card_powerset]
  apply Finset.card_le_card_of_injOn send
  · intro A hA
    have hsub := mem_powerset.mp hA
    have hin : A ⊆ N := fun y hy => (mem_sdiff.mp (hsub hy)).1
    refine mem_filter.mpr ⟨(mem_failures _ _).mpr ⟨f i,?_⟩,?_⟩
    · intro y hy
      rcases mem_union.mp hy with h | h
      · obtain ⟨j,hj,rfl⟩ := mem_map.mp h
        have hv := ht hj
        simpa [graphRows,restrictSet] using hv
      · exact (G.mem_neighborFinset _ _).mp (hin h)
    · ext j
      simp only [restrictSet,mem_filter,mem_univ,true_and,send,mem_union] 
      constructor
      · rintro (h|h)
        · obtain ⟨x,hx,he⟩ := mem_map.mp h
          exact f.injective he ▸ hx
        · exact False.elim ((mem_sdiff.mp (hsub h)).2 (mem_map.mpr ⟨j,mem_univ _,rfl⟩))
      · exact fun h => Or.inl (mem_map.mpr ⟨j,h,rfl⟩)
  · intro A hA B hB he
    have remove (C : Finset (Fin n)) (hc : C ∈ extN.powerset) :
        send C \ univ.map f = C := by
      ext y
      simp only [send,mem_sdiff,mem_union]
      constructor
      · rintro ⟨h | h,hy⟩
        · obtain ⟨j,_,rfl⟩ := mem_map.mp h
          exact False.elim (hy (mem_map.mpr ⟨j,mem_univ _,rfl⟩))
        · exact h
      · exact fun h => ⟨Or.inr h,(mem_sdiff.mp ((mem_powerset.mp hc) h)).2⟩
    simpa only [remove A hA,remove B hB] using congrArg (fun C : Finset (Fin n) => C \ univ.map f) he

theorem singleton_failure {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (i : Fin n) : 2^(G.degree i) ≤ (failures G).card := by
  classical
  have h : (G.neighborFinset i).powerset ⊆ failures G := by
    intro S hS
    exact (mem_failures G S).mpr ⟨i,fun j hj => (G.mem_neighborFinset _ _).mp (mem_powerset.mp hS hj)⟩
  simpa using Finset.card_le_card h

theorem graph_trace_score {n m : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : Fin m ↪ Fin n) (a : Fin m → ℕ) {k : ℕ} (hm : m ≤ 6)
    (hd : ∀ i, 7+G.degree (f i) = k+5+a i) :
    2^k * traceScore (graphRows G f) a ≤ 128*(failures G).card := by
  classical
  have hsum : (failures G).card =
      ∑ T : Finset (Fin m), ((failures G).filter (fun S => restrictSet f S = T)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  rw [hsum,traceScore,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro T _
  let v (i : Fin m) : ℕ := if T ⊆ graphRows G f i then 2^(5+a i-(graphRows G f i).card) else 0
  change 2^k * univ.sup v ≤ _
  rcases (univ : Finset (Fin m)).eq_empty_or_nonempty with h|h
  · simp [h]
  obtain ⟨i,_,he⟩ := univ.exists_mem_eq_sup h v
  rw [he]
  dsimp [v]
  split_ifs with ht
  · have hii : i ∉ graphRows G f i := by simp [graphRows,restrictSet]
    have hrow : (graphRows G f i).card < m := by simpa using Finset.card_lt_univ_of_notMem hii
    have hr : (graphRows G f i).card ≤ G.degree (f i) := by
      let N := G.neighborFinset (f i)
      have eqrows : graphRows G f i = restrictSet f N := by
        ext j
        simp [graphRows,restrictSet,N]
      have eqm := trace_inside f N
      have cardle := card_le_card (show (restrictSet f N).map f ⊆ N by rw [eqm]; exact inter_subset_right)
      simpa [eqrows,N] using cardle
    have ex : k+(5+a i-(graphRows G f i).card) = 7+(G.degree (f i)-(graphRows G f i).card) := by
      have := hd i
      omega
    rw [←Nat.pow_add,ex,Nat.pow_add]
    exact Nat.mul_le_mul_left (2^7) (trace_fiber_card G f i T ht)
  · simp

end KeoughShane

end

section

namespace KeoughShane
open Finset

def extensionRow (m fifth sixth : ℕ) (i : Fin m) : Finset (Fin m) := univ.filter fun j =>
  i.val ≠ j.val ∧ (if max i.val j.val < 4 then i.val + 1 = j.val ∨ j.val + 1 = i.val
    else if max i.val j.val = 4 then fifth.testBit (min i.val j.val) = true
    else sixth.testBit (min i.val j.val) = true)

private theorem ksBits4 : ∀ f : Fin 4 → Bool, ∃ a : Fin 16, ∀ i : Fin 4,
    a.val.testBit i.val = f i := by decide +kernel
private theorem ksBits5 : ∀ f : Fin 5 → Bool, ∃ a : Fin 32, ∀ i : Fin 5,
    a.val.testBit i.val = f i := by decide +kernel

private theorem extensionRow_eq {m : ℕ} (r : Fin m → Finset (Fin m))
    (hdiag : ∀ i, i ∉ r i) (hsym : ∀ i j, j ∈ r i ↔ i ∈ r j)
    (hp : ∀ i j : Fin m, i.val < 4 → j.val < 4 →
      (j ∈ r i ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val))
    (hm : m ≤ 6) (fifth sixth : ℕ)
    (h4 : ∀ i j : Fin m, i.val < 4 → j.val = 4 → (fifth.testBit i.val = true ↔ j ∈ r i))
    (h5 : ∀ i j : Fin m, i.val < 5 → j.val = 5 → (sixth.testBit i.val = true ↔ j ∈ r i)) :
    r = extensionRow m fifth sixth := by
  have upper (i j : Fin m) (h : i.val < j.val) :
      j ∈ r i ↔ j ∈ extensionRow m fifth sixth i := by
    simp only [extensionRow, mem_filter, mem_univ, true_and, and_iff_right (ne_of_lt h),
      max_eq_right h.le, min_eq_left h.le]
    split_ifs with hlt heq
    · exact hp i j (by omega) hlt
    · exact (h4 i j (by omega) heq).symm
    · exact (h5 i j (by omega) (by have := j.isLt; omega)).symm
  funext i
  ext j
  rcases lt_trichotomy i.val j.val with h|h|h
  · exact upper i j h
  · obtain rfl := Fin.ext h
    simp [extensionRow, hdiag]
  · rw [hsym i j, upper j i h]
    simp [extensionRow, max_comm, min_comm, ne_comm, or_comm, and_comm]

theorem extensionFive (r : Fin 5 → Finset (Fin 5)) (hdiag : ∀ i, i ∉ r i)
    (hsym : ∀ i j, j ∈ r i ↔ i ∈ r j)
    (hp : ∀ i j : Fin 5, i.val < 4 → j.val < 4 →
      (j ∈ r i ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val)) :
    ∃ a : Fin 16, r = extensionRow 5 a.val 0 := by
  obtain ⟨a,ha⟩ := ksBits4 (fun i => decide ((4 : Fin 5) ∈ r i.castSucc))
  refine ⟨a,extensionRow_eq r hdiag hsym hp (by decide) _ _ ?_ ?_⟩
  · intro i j hi hj
    have h := ha ⟨i.val, hi⟩
    have he : (⟨i.val,hi⟩ : Fin 4).castSucc = i := Fin.ext rfl
    have je : j = 4 := Fin.ext hj
    simpa [he, je] using congrArg (· = true) h
  · intro i j _ hj
    have := j.isLt
    omega

theorem extensionSix (r : Fin 6 → Finset (Fin 6)) (hdiag : ∀ i, i ∉ r i)
    (hsym : ∀ i j, j ∈ r i ↔ i ∈ r j)
    (hp : ∀ i j : Fin 6, i.val < 4 → j.val < 4 →
      (j ∈ r i ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val)) :
    ∃ a : Fin 16, ∃ b : Fin 32, r = extensionRow 6 a.val b.val := by
  obtain ⟨a,ha⟩ := ksBits4 (fun i => decide ((4 : Fin 6) ∈ r i.castSucc.castSucc))
  obtain ⟨b,hb⟩ := ksBits5 (fun i => decide ((5 : Fin 6) ∈ r i.castSucc))
  refine ⟨a,b,extensionRow_eq r hdiag hsym hp (by decide) _ _ ?_ ?_⟩
  · intro i j hi hj
    have he : (⟨i.val,hi⟩ : Fin 4).castSucc.castSucc = i := Fin.ext rfl
    have je : j = 4 := Fin.ext hj
    simpa [he, je] using congrArg (· = true) (ha ⟨i.val,hi⟩)
  · intro i j hi hj
    have he : (⟨i.val,hi⟩ : Fin 5).castSucc = i := Fin.ext rfl
    have je : j = 5 := Fin.ext hj
    simpa [he, je] using congrArg (· = true) (hb ⟨i.val,hi⟩)

end KeoughShane

end

section

namespace KeoughShane
open Finset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksTypes {m : ℕ} (r : Fin m → Finset (Fin m)) : Multiset (Finset (Fin m)) :=
  (univ : Finset (Finset (Fin m))).val.map (fun T => univ.filter (fun i => T ⊆ r i))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksExpand {m : ℕ} (r : Fin m → Finset (Fin m)) (a : Fin m → ℕ) :
    traceScore r a = ((ksTypes r).map (fun t => t.sup (fun i => 2^(5 + a i - (r i).card)))).sum := by
  rw [traceScore, Finset.sum_eq_multiset_sum, ksTypes, Multiset.map_map]
  congr 1
  refine congrArg (fun f => Multiset.map f _) ?_
  funext T
  rw [Finset.sup_ite]
  simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_r0 : ksTypes (extensionRow 5 0 0) =
    (([{0,1,2,3,4},{1},{1},{0,2},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{1,3},{2},{2}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_r0 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (2 * w1) + (max w0 w2) + (max w1 w3) + (2 * w2)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_r0 (a : Fin 5 → ℕ) : traceScore (extensionRow 5 0 0) a =
    ksForm_r0 (2 ^ (5 + a 0 - 1)) (2 ^ (5 + a 1 - 2)) (2 ^ (5 + a 2 - 2)) (2 ^ (5 + a 3 - 1)) (2 ^ (5 + a 4 - 0)) := by
  rw [ksExpand, ksTypes_r0]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_r0, show ((extensionRow 5 0 0) 0).card = 1 by decide +kernel, show ((extensionRow 5 0 0) 1).card = 2 by decide +kernel, show ((extensionRow 5 0 0) 2).card = 2 by decide +kernel, show ((extensionRow 5 0 0) 3).card = 1 by decide +kernel, show ((extensionRow 5 0 0) 4).card = 0 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_b0 : ksTypes (otherRows (extensionRow 5 0 0)) =
    (([{0,1,2,3,4},{2,3,4},{3,4},{3,4},{0,4},{0,4},{4},{4},{4},{4},{4},{4},{4},{4},{4},{0,1,4},{0,1,2,3},{2,3},{3},{3},{0},{0},∅,∅,∅,∅,∅,∅,∅,∅,∅,{0,1}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_b0 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (max w2 (max w3 w4)) + (2 * (max w3 w4)) + (2 * (max w0 w4)) + (9 * w4) + (max w0 (max w1 w4)) + (max w0 (max w1 (max w2 w3))) + (max w2 w3) + (2 * w3) + (2 * w0) + (max w0 w1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_b0 (a : Fin 5 → ℕ) : traceScore (otherRows (extensionRow 5 0 0)) a =
    ksForm_b0 (2 ^ (5 + a 0 - 3)) (2 ^ (5 + a 1 - 2)) (2 ^ (5 + a 2 - 2)) (2 ^ (5 + a 3 - 3)) (2 ^ (5 + a 4 - 4)) := by
  rw [ksExpand, ksTypes_b0]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_b0, show ((otherRows (extensionRow 5 0 0)) 0).card = 3 by decide +kernel, show ((otherRows (extensionRow 5 0 0)) 1).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 0 0)) 2).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 0 0)) 3).card = 3 by decide +kernel, show ((otherRows (extensionRow 5 0 0)) 4).card = 4 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_0_0 : ∀ d0 d1 d2 d3 d4 : Fin 4,
  512 ≤ ksForm_r0 (2 ^ (5 + d0.val - 1)) (2 ^ (5 + d1.val - 2)) (2 ^ (5 + d2.val - 2)) (2 ^ (5 + d3.val - 1)) (2 ^ (5 + d4.val - 0)) + ksForm_b0 (2 ^ (5 + (3 - d0.val) - 3)) (2 ^ (5 + (3 - d1.val) - 2)) (2 ^ (5 + (3 - d2.val) - 2)) (2 ^ (5 + (3 - d3.val) - 3)) (2 ^ (5 + (3 - d4.val) - 4)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_0_1 : ∀ d0 d1 d2 d3 d4 : Fin 5,
  (d0.val = 2 ∧ d1.val = 2 ∧ d2.val = 2 ∧ d3.val = 2 ∧ d4.val = 2) ∨ 768 ≤ ksForm_r0 (2 ^ (5 + d0.val - 1)) (2 ^ (5 + d1.val - 2)) (2 ^ (5 + d2.val - 2)) (2 ^ (5 + d3.val - 1)) (2 ^ (5 + d4.val - 0)) + ksForm_b0 (2 ^ (5 + (4 - d0.val) - 3)) (2 ^ (5 + (4 - d1.val) - 2)) (2 ^ (5 + (4 - d2.val) - 2)) (2 ^ (5 + (4 - d3.val) - 3)) (2 ^ (5 + (4 - d4.val) - 4)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFive_0 (a : Fin 5 → ℕ) (e : ℕ) (he : e ≤ 1)
    (hd : ∀ i, a i ≤ 3 + e) (hn : e = 0 ∨ ∃ i, a i ≠ 2) :
    128 * (4 + 2 * e) ≤ traceScore (extensionRow 5 0 0) a +
    traceScore (otherRows (extensionRow 5 0 0)) (fun i => 3+e-a i) := by
  have D0 := hd 0
  have D1 := hd 1
  have D2 := hd 2
  have D3 := hd 3
  have D4 := hd 4
  rw [ksFormEq_r0, ksFormEq_b0]
  rcases (show e = 0 ∨ e = 1 by omega) with rfl|rfl
  · exact ksCheck_0_0 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩
  · have hm : ¬(a 0 = 2 ∧ a 1 = 2 ∧ a 2 = 2 ∧ a 3 = 2 ∧ a 4 = 2) := by
      obtain ⟨i,hi⟩ := hn.resolve_left (by decide)
      intro h
      fin_cases i <;> simp_all
    exact (ksCheck_0_1 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩).resolve_left hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_r1 : ksTypes (extensionRow 5 1 0) =
    (([{0,1,2,3,4},{1,4},{0,2},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{1,3},{1},{2},{2},{0},{0}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_r1 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (max w1 w4) + (max w0 w2) + (max w1 w3) + w1 + (2 * w2) + (2 * w0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_r1 (a : Fin 5 → ℕ) : traceScore (extensionRow 5 1 0) a =
    ksForm_r1 (2 ^ (5 + a 0 - 2)) (2 ^ (5 + a 1 - 2)) (2 ^ (5 + a 2 - 2)) (2 ^ (5 + a 3 - 1)) (2 ^ (5 + a 4 - 1)) := by
  rw [ksExpand, ksTypes_r1]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_r1, show ((extensionRow 5 1 0) 0).card = 2 by decide +kernel, show ((extensionRow 5 1 0) 1).card = 2 by decide +kernel, show ((extensionRow 5 1 0) 2).card = 2 by decide +kernel, show ((extensionRow 5 1 0) 3).card = 1 by decide +kernel, show ((extensionRow 5 1 0) 4).card = 1 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_b1 : ksTypes (otherRows (extensionRow 5 1 0)) =
    (([{0,1,2,3,4},{2,3},{2,3},{3,4},{3},{3},{3},{0,4},{0,4},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{4},{4},{4},{0,1,4},{1,2,3},{1}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_b1 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (2 * (max w2 w3)) + (max w3 w4) + (3 * w3) + (2 * (max w0 w4)) + (3 * w4) + (max w0 (max w1 w4)) + (max w1 (max w2 w3)) + w1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_b1 (a : Fin 5 → ℕ) : traceScore (otherRows (extensionRow 5 1 0)) a =
    ksForm_b1 (2 ^ (5 + a 0 - 2)) (2 ^ (5 + a 1 - 2)) (2 ^ (5 + a 2 - 2)) (2 ^ (5 + a 3 - 3)) (2 ^ (5 + a 4 - 3)) := by
  rw [ksExpand, ksTypes_b1]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_b1, show ((otherRows (extensionRow 5 1 0)) 0).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 1 0)) 1).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 1 0)) 2).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 1 0)) 3).card = 3 by decide +kernel, show ((otherRows (extensionRow 5 1 0)) 4).card = 3 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_1_0 : ∀ d0 d1 d2 d3 d4 : Fin 4,
  512 ≤ ksForm_r1 (2 ^ (5 + d0.val - 2)) (2 ^ (5 + d1.val - 2)) (2 ^ (5 + d2.val - 2)) (2 ^ (5 + d3.val - 1)) (2 ^ (5 + d4.val - 1)) + ksForm_b1 (2 ^ (5 + (3 - d0.val) - 2)) (2 ^ (5 + (3 - d1.val) - 2)) (2 ^ (5 + (3 - d2.val) - 2)) (2 ^ (5 + (3 - d3.val) - 3)) (2 ^ (5 + (3 - d4.val) - 3)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_1_1 : ∀ d0 d1 d2 d3 d4 : Fin 5,
  (d0.val = 2 ∧ d1.val = 2 ∧ d2.val = 2 ∧ d3.val = 2 ∧ d4.val = 2) ∨ 768 ≤ ksForm_r1 (2 ^ (5 + d0.val - 2)) (2 ^ (5 + d1.val - 2)) (2 ^ (5 + d2.val - 2)) (2 ^ (5 + d3.val - 1)) (2 ^ (5 + d4.val - 1)) + ksForm_b1 (2 ^ (5 + (4 - d0.val) - 2)) (2 ^ (5 + (4 - d1.val) - 2)) (2 ^ (5 + (4 - d2.val) - 2)) (2 ^ (5 + (4 - d3.val) - 3)) (2 ^ (5 + (4 - d4.val) - 3)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFive_1 (a : Fin 5 → ℕ) (e : ℕ) (he : e ≤ 1)
    (hd : ∀ i, a i ≤ 3 + e) (hn : e = 0 ∨ ∃ i, a i ≠ 2) :
    128 * (4 + 2 * e) ≤ traceScore (extensionRow 5 1 0) a +
    traceScore (otherRows (extensionRow 5 1 0)) (fun i => 3+e-a i) := by
  have D0 := hd 0
  have D1 := hd 1
  have D2 := hd 2
  have D3 := hd 3
  have D4 := hd 4
  rw [ksFormEq_r1, ksFormEq_b1]
  rcases (show e = 0 ∨ e = 1 by omega) with rfl|rfl
  · exact ksCheck_1_0 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩
  · have hm : ¬(a 0 = 2 ∧ a 1 = 2 ∧ a 2 = 2 ∧ a 3 = 2 ∧ a 4 = 2) := by
      obtain ⟨i,hi⟩ := hn.resolve_left (by decide)
      intro h
      fin_cases i <;> simp_all
    exact (ksCheck_1_1 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩).resolve_left hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_r2 : ksTypes (extensionRow 5 2 0) =
    (([{0,1,2,3,4},{1},{1},{1},{1},{1},{1},{0,2,4},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{1,3},{2},{2}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_r2 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (6 * w1) + (max w0 (max w2 w4)) + (max w1 w3) + (2 * w2)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_r2 (a : Fin 5 → ℕ) : traceScore (extensionRow 5 2 0) a =
    ksForm_r2 (2 ^ (5 + a 0 - 1)) (2 ^ (5 + a 1 - 3)) (2 ^ (5 + a 2 - 2)) (2 ^ (5 + a 3 - 1)) (2 ^ (5 + a 4 - 1)) := by
  rw [ksExpand, ksTypes_r2]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_r2, show ((extensionRow 5 2 0) 0).card = 1 by decide +kernel, show ((extensionRow 5 2 0) 1).card = 3 by decide +kernel, show ((extensionRow 5 2 0) 2).card = 2 by decide +kernel, show ((extensionRow 5 2 0) 3).card = 1 by decide +kernel, show ((extensionRow 5 2 0) 4).card = 1 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_b2 : ksTypes (otherRows (extensionRow 5 2 0)) =
    (([{0,1,2,3,4},{2,3,4},{3},{3},{3},{3},{0,4},{0,4},{4},{4},{4},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{0,1,4},{0,2,3},{2,3},{0},{0},{0}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_b2 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (max w2 (max w3 w4)) + (4 * w3) + (2 * (max w0 w4)) + (3 * w4) + (max w0 (max w1 w4)) + (max w0 (max w2 w3)) + (max w2 w3) + (3 * w0)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_b2 (a : Fin 5 → ℕ) : traceScore (otherRows (extensionRow 5 2 0)) a =
    ksForm_b2 (2 ^ (5 + a 0 - 3)) (2 ^ (5 + a 1 - 1)) (2 ^ (5 + a 2 - 2)) (2 ^ (5 + a 3 - 3)) (2 ^ (5 + a 4 - 3)) := by
  rw [ksExpand, ksTypes_b2]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_b2, show ((otherRows (extensionRow 5 2 0)) 0).card = 3 by decide +kernel, show ((otherRows (extensionRow 5 2 0)) 1).card = 1 by decide +kernel, show ((otherRows (extensionRow 5 2 0)) 2).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 2 0)) 3).card = 3 by decide +kernel, show ((otherRows (extensionRow 5 2 0)) 4).card = 3 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_2_0 : ∀ d0 d1 d2 d3 d4 : Fin 4,
  512 ≤ ksForm_r2 (2 ^ (5 + d0.val - 1)) (2 ^ (5 + d1.val - 3)) (2 ^ (5 + d2.val - 2)) (2 ^ (5 + d3.val - 1)) (2 ^ (5 + d4.val - 1)) + ksForm_b2 (2 ^ (5 + (3 - d0.val) - 3)) (2 ^ (5 + (3 - d1.val) - 1)) (2 ^ (5 + (3 - d2.val) - 2)) (2 ^ (5 + (3 - d3.val) - 3)) (2 ^ (5 + (3 - d4.val) - 3)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_2_1 : ∀ d0 d1 d2 d3 d4 : Fin 5,
  (d0.val = 2 ∧ d1.val = 2 ∧ d2.val = 2 ∧ d3.val = 2 ∧ d4.val = 2) ∨ 768 ≤ ksForm_r2 (2 ^ (5 + d0.val - 1)) (2 ^ (5 + d1.val - 3)) (2 ^ (5 + d2.val - 2)) (2 ^ (5 + d3.val - 1)) (2 ^ (5 + d4.val - 1)) + ksForm_b2 (2 ^ (5 + (4 - d0.val) - 3)) (2 ^ (5 + (4 - d1.val) - 1)) (2 ^ (5 + (4 - d2.val) - 2)) (2 ^ (5 + (4 - d3.val) - 3)) (2 ^ (5 + (4 - d4.val) - 3)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFive_2 (a : Fin 5 → ℕ) (e : ℕ) (he : e ≤ 1)
    (hd : ∀ i, a i ≤ 3 + e) (hn : e = 0 ∨ ∃ i, a i ≠ 2) :
    128 * (4 + 2 * e) ≤ traceScore (extensionRow 5 2 0) a +
    traceScore (otherRows (extensionRow 5 2 0)) (fun i => 3+e-a i) := by
  have D0 := hd 0
  have D1 := hd 1
  have D2 := hd 2
  have D3 := hd 3
  have D4 := hd 4
  rw [ksFormEq_r2, ksFormEq_b2]
  rcases (show e = 0 ∨ e = 1 by omega) with rfl|rfl
  · exact ksCheck_2_0 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩
  · have hm : ¬(a 0 = 2 ∧ a 1 = 2 ∧ a 2 = 2 ∧ a 3 = 2 ∧ a 4 = 2) := by
      obtain ⟨i,hi⟩ := hn.resolve_left (by decide)
      intro h
      fin_cases i <;> simp_all
    exact (ksCheck_2_1 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩).resolve_left hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_r3 : ksTypes (extensionRow 5 3 0) =
    (([{0,1,2,3,4},{1,4},{0,2,4},{4},{1,3},{1},{1},{1},{1},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{2},{2},{0,1},{0}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_r3 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (max w1 w4) + (max w0 (max w2 w4)) + w4 + (max w1 w3) + (4 * w1) + (2 * w2) + (max w0 w1) + w0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_r3 (a : Fin 5 → ℕ) : traceScore (extensionRow 5 3 0) a =
    ksForm_r3 (2 ^ (5 + a 0 - 2)) (2 ^ (5 + a 1 - 3)) (2 ^ (5 + a 2 - 2)) (2 ^ (5 + a 3 - 1)) (2 ^ (5 + a 4 - 2)) := by
  rw [ksExpand, ksTypes_r3]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_r3, show ((extensionRow 5 3 0) 0).card = 2 by decide +kernel, show ((extensionRow 5 3 0) 1).card = 3 by decide +kernel, show ((extensionRow 5 3 0) 2).card = 2 by decide +kernel, show ((extensionRow 5 3 0) 3).card = 1 by decide +kernel, show ((extensionRow 5 3 0) 4).card = 2 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_b3 : ksTypes (otherRows (extensionRow 5 3 0)) =
    (([{0,1,2,3,4},{2,3},{2,3},{2,3},{3},{3},{3},{3},{0,4},{0,4},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{0,1,4}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_b3 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (3 * (max w2 w3)) + (4 * w3) + (2 * (max w0 w4)) + (max w0 (max w1 w4))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_b3 (a : Fin 5 → ℕ) : traceScore (otherRows (extensionRow 5 3 0)) a =
    ksForm_b3 (2 ^ (5 + a 0 - 2)) (2 ^ (5 + a 1 - 1)) (2 ^ (5 + a 2 - 2)) (2 ^ (5 + a 3 - 3)) (2 ^ (5 + a 4 - 2)) := by
  rw [ksExpand, ksTypes_b3]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_b3, show ((otherRows (extensionRow 5 3 0)) 0).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 3 0)) 1).card = 1 by decide +kernel, show ((otherRows (extensionRow 5 3 0)) 2).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 3 0)) 3).card = 3 by decide +kernel, show ((otherRows (extensionRow 5 3 0)) 4).card = 2 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_3_0 : ∀ d0 d1 d2 d3 d4 : Fin 4,
  512 ≤ ksForm_r3 (2 ^ (5 + d0.val - 2)) (2 ^ (5 + d1.val - 3)) (2 ^ (5 + d2.val - 2)) (2 ^ (5 + d3.val - 1)) (2 ^ (5 + d4.val - 2)) + ksForm_b3 (2 ^ (5 + (3 - d0.val) - 2)) (2 ^ (5 + (3 - d1.val) - 1)) (2 ^ (5 + (3 - d2.val) - 2)) (2 ^ (5 + (3 - d3.val) - 3)) (2 ^ (5 + (3 - d4.val) - 2)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_3_1 : ∀ d0 d1 d2 d3 d4 : Fin 5,
  (d0.val = 2 ∧ d1.val = 2 ∧ d2.val = 2 ∧ d3.val = 2 ∧ d4.val = 2) ∨ 768 ≤ ksForm_r3 (2 ^ (5 + d0.val - 2)) (2 ^ (5 + d1.val - 3)) (2 ^ (5 + d2.val - 2)) (2 ^ (5 + d3.val - 1)) (2 ^ (5 + d4.val - 2)) + ksForm_b3 (2 ^ (5 + (4 - d0.val) - 2)) (2 ^ (5 + (4 - d1.val) - 1)) (2 ^ (5 + (4 - d2.val) - 2)) (2 ^ (5 + (4 - d3.val) - 3)) (2 ^ (5 + (4 - d4.val) - 2)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFive_3 (a : Fin 5 → ℕ) (e : ℕ) (he : e ≤ 1)
    (hd : ∀ i, a i ≤ 3 + e) (hn : e = 0 ∨ ∃ i, a i ≠ 2) :
    128 * (4 + 2 * e) ≤ traceScore (extensionRow 5 3 0) a +
    traceScore (otherRows (extensionRow 5 3 0)) (fun i => 3+e-a i) := by
  have D0 := hd 0
  have D1 := hd 1
  have D2 := hd 2
  have D3 := hd 3
  have D4 := hd 4
  rw [ksFormEq_r3, ksFormEq_b3]
  rcases (show e = 0 ∨ e = 1 by omega) with rfl|rfl
  · exact ksCheck_3_0 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩
  · have hm : ¬(a 0 = 2 ∧ a 1 = 2 ∧ a 2 = 2 ∧ a 3 = 2 ∧ a 4 = 2) := by
      obtain ⟨i,hi⟩ := hn.resolve_left (by decide)
      intro h
      fin_cases i <;> simp_all
    exact (ksCheck_3_1 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩).resolve_left hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_r4 : ksTypes (extensionRow 5 4 0) =
    (([{0,1,2,3,4},{1},{1},{0,2},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{1,3,4},{2},{2},{2},{2},{2},{2}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_r4 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (2 * w1) + (max w0 w2) + (max w1 (max w3 w4)) + (6 * w2)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_r4 (a : Fin 5 → ℕ) : traceScore (extensionRow 5 4 0) a =
    ksForm_r4 (2 ^ (5 + a 0 - 1)) (2 ^ (5 + a 1 - 2)) (2 ^ (5 + a 2 - 3)) (2 ^ (5 + a 3 - 1)) (2 ^ (5 + a 4 - 1)) := by
  rw [ksExpand, ksTypes_r4]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_r4, show ((extensionRow 5 4 0) 0).card = 1 by decide +kernel, show ((extensionRow 5 4 0) 1).card = 2 by decide +kernel, show ((extensionRow 5 4 0) 2).card = 3 by decide +kernel, show ((extensionRow 5 4 0) 3).card = 1 by decide +kernel, show ((extensionRow 5 4 0) 4).card = 1 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_b4 : ksTypes (otherRows (extensionRow 5 4 0)) =
    (([{0,1,2,3,4},{2,3,4},{3,4},{3,4},{0},{0},{0},{0},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{0,1,4},{4},{4},{4},{0,1,3},{3},{3},{3},{0,1}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_b4 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (max w2 (max w3 w4)) + (2 * (max w3 w4)) + (4 * w0) + (max w0 (max w1 w4)) + (3 * w4) + (max w0 (max w1 w3)) + (3 * w3) + (max w0 w1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_b4 (a : Fin 5 → ℕ) : traceScore (otherRows (extensionRow 5 4 0)) a =
    ksForm_b4 (2 ^ (5 + a 0 - 3)) (2 ^ (5 + a 1 - 2)) (2 ^ (5 + a 2 - 1)) (2 ^ (5 + a 3 - 3)) (2 ^ (5 + a 4 - 3)) := by
  rw [ksExpand, ksTypes_b4]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_b4, show ((otherRows (extensionRow 5 4 0)) 0).card = 3 by decide +kernel, show ((otherRows (extensionRow 5 4 0)) 1).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 4 0)) 2).card = 1 by decide +kernel, show ((otherRows (extensionRow 5 4 0)) 3).card = 3 by decide +kernel, show ((otherRows (extensionRow 5 4 0)) 4).card = 3 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_4_0 : ∀ d0 d1 d2 d3 d4 : Fin 4,
  512 ≤ ksForm_r4 (2 ^ (5 + d0.val - 1)) (2 ^ (5 + d1.val - 2)) (2 ^ (5 + d2.val - 3)) (2 ^ (5 + d3.val - 1)) (2 ^ (5 + d4.val - 1)) + ksForm_b4 (2 ^ (5 + (3 - d0.val) - 3)) (2 ^ (5 + (3 - d1.val) - 2)) (2 ^ (5 + (3 - d2.val) - 1)) (2 ^ (5 + (3 - d3.val) - 3)) (2 ^ (5 + (3 - d4.val) - 3)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_4_1 : ∀ d0 d1 d2 d3 d4 : Fin 5,
  (d0.val = 2 ∧ d1.val = 2 ∧ d2.val = 2 ∧ d3.val = 2 ∧ d4.val = 2) ∨ 768 ≤ ksForm_r4 (2 ^ (5 + d0.val - 1)) (2 ^ (5 + d1.val - 2)) (2 ^ (5 + d2.val - 3)) (2 ^ (5 + d3.val - 1)) (2 ^ (5 + d4.val - 1)) + ksForm_b4 (2 ^ (5 + (4 - d0.val) - 3)) (2 ^ (5 + (4 - d1.val) - 2)) (2 ^ (5 + (4 - d2.val) - 1)) (2 ^ (5 + (4 - d3.val) - 3)) (2 ^ (5 + (4 - d4.val) - 3)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFive_4 (a : Fin 5 → ℕ) (e : ℕ) (he : e ≤ 1)
    (hd : ∀ i, a i ≤ 3 + e) (hn : e = 0 ∨ ∃ i, a i ≠ 2) :
    128 * (4 + 2 * e) ≤ traceScore (extensionRow 5 4 0) a +
    traceScore (otherRows (extensionRow 5 4 0)) (fun i => 3+e-a i) := by
  have D0 := hd 0
  have D1 := hd 1
  have D2 := hd 2
  have D3 := hd 3
  have D4 := hd 4
  rw [ksFormEq_r4, ksFormEq_b4]
  rcases (show e = 0 ∨ e = 1 by omega) with rfl|rfl
  · exact ksCheck_4_0 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩
  · have hm : ¬(a 0 = 2 ∧ a 1 = 2 ∧ a 2 = 2 ∧ a 3 = 2 ∧ a 4 = 2) := by
      obtain ⟨i,hi⟩ := hn.resolve_left (by decide)
      intro h
      fin_cases i <;> simp_all
    exact (ksCheck_4_1 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩).resolve_left hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_r5 : ksTypes (extensionRow 5 5 0) =
    (([{0,1,2,3,4},{1,4},{1,4},{0,2},{0,2},{0,2},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{1,3,4},{2},{2},{2},{2}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_r5 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (2 * (max w1 w4)) + (3 * (max w0 w2)) + (max w1 (max w3 w4)) + (4 * w2)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_r5 (a : Fin 5 → ℕ) : traceScore (extensionRow 5 5 0) a =
    ksForm_r5 (2 ^ (5 + a 0 - 2)) (2 ^ (5 + a 1 - 2)) (2 ^ (5 + a 2 - 3)) (2 ^ (5 + a 3 - 1)) (2 ^ (5 + a 4 - 2)) := by
  rw [ksExpand, ksTypes_r5]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_r5, show ((extensionRow 5 5 0) 0).card = 2 by decide +kernel, show ((extensionRow 5 5 0) 1).card = 2 by decide +kernel, show ((extensionRow 5 5 0) 2).card = 3 by decide +kernel, show ((extensionRow 5 5 0) 3).card = 1 by decide +kernel, show ((extensionRow 5 5 0) 4).card = 2 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_b5 : ksTypes (otherRows (extensionRow 5 5 0)) =
    (([{0,1,2,3,4},{2,3},{3,4},{3},{3},{3},{3},{0},{0},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{0,1,4},{4},{1,3},{1}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_b5 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (max w2 w3) + (max w3 w4) + (4 * w3) + (2 * w0) + (max w0 (max w1 w4)) + w4 + (max w1 w3) + w1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_b5 (a : Fin 5 → ℕ) : traceScore (otherRows (extensionRow 5 5 0)) a =
    ksForm_b5 (2 ^ (5 + a 0 - 2)) (2 ^ (5 + a 1 - 2)) (2 ^ (5 + a 2 - 1)) (2 ^ (5 + a 3 - 3)) (2 ^ (5 + a 4 - 2)) := by
  rw [ksExpand, ksTypes_b5]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_b5, show ((otherRows (extensionRow 5 5 0)) 0).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 5 0)) 1).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 5 0)) 2).card = 1 by decide +kernel, show ((otherRows (extensionRow 5 5 0)) 3).card = 3 by decide +kernel, show ((otherRows (extensionRow 5 5 0)) 4).card = 2 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_5_0 : ∀ d0 d1 d2 d3 d4 : Fin 4,
  512 ≤ ksForm_r5 (2 ^ (5 + d0.val - 2)) (2 ^ (5 + d1.val - 2)) (2 ^ (5 + d2.val - 3)) (2 ^ (5 + d3.val - 1)) (2 ^ (5 + d4.val - 2)) + ksForm_b5 (2 ^ (5 + (3 - d0.val) - 2)) (2 ^ (5 + (3 - d1.val) - 2)) (2 ^ (5 + (3 - d2.val) - 1)) (2 ^ (5 + (3 - d3.val) - 3)) (2 ^ (5 + (3 - d4.val) - 2)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_5_1 : ∀ d0 d1 d2 d3 d4 : Fin 5,
  (d0.val = 2 ∧ d1.val = 2 ∧ d2.val = 2 ∧ d3.val = 2 ∧ d4.val = 2) ∨ 768 ≤ ksForm_r5 (2 ^ (5 + d0.val - 2)) (2 ^ (5 + d1.val - 2)) (2 ^ (5 + d2.val - 3)) (2 ^ (5 + d3.val - 1)) (2 ^ (5 + d4.val - 2)) + ksForm_b5 (2 ^ (5 + (4 - d0.val) - 2)) (2 ^ (5 + (4 - d1.val) - 2)) (2 ^ (5 + (4 - d2.val) - 1)) (2 ^ (5 + (4 - d3.val) - 3)) (2 ^ (5 + (4 - d4.val) - 2)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFive_5 (a : Fin 5 → ℕ) (e : ℕ) (he : e ≤ 1)
    (hd : ∀ i, a i ≤ 3 + e) (hn : e = 0 ∨ ∃ i, a i ≠ 2) :
    128 * (4 + 2 * e) ≤ traceScore (extensionRow 5 5 0) a +
    traceScore (otherRows (extensionRow 5 5 0)) (fun i => 3+e-a i) := by
  have D0 := hd 0
  have D1 := hd 1
  have D2 := hd 2
  have D3 := hd 3
  have D4 := hd 4
  rw [ksFormEq_r5, ksFormEq_b5]
  rcases (show e = 0 ∨ e = 1 by omega) with rfl|rfl
  · exact ksCheck_5_0 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩
  · have hm : ¬(a 0 = 2 ∧ a 1 = 2 ∧ a 2 = 2 ∧ a 3 = 2 ∧ a 4 = 2) := by
      obtain ⟨i,hi⟩ := hn.resolve_left (by decide)
      intro h
      fin_cases i <;> simp_all
    exact (ksCheck_5_1 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩).resolve_left hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_r6 : ksTypes (extensionRow 5 6 0) =
    (([{0,1,2,3,4},{1},{1},{1},{1},{1},{0,2,4},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{1,3,4},{4},{2},{2},{2},{2},{2},{1,2}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_r6 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (5 * w1) + (max w0 (max w2 w4)) + (max w1 (max w3 w4)) + w4 + (5 * w2) + (max w1 w2)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_r6 (a : Fin 5 → ℕ) : traceScore (extensionRow 5 6 0) a =
    ksForm_r6 (2 ^ (5 + a 0 - 1)) (2 ^ (5 + a 1 - 3)) (2 ^ (5 + a 2 - 3)) (2 ^ (5 + a 3 - 1)) (2 ^ (5 + a 4 - 2)) := by
  rw [ksExpand, ksTypes_r6]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_r6, show ((extensionRow 5 6 0) 0).card = 1 by decide +kernel, show ((extensionRow 5 6 0) 1).card = 3 by decide +kernel, show ((extensionRow 5 6 0) 2).card = 3 by decide +kernel, show ((extensionRow 5 6 0) 3).card = 1 by decide +kernel, show ((extensionRow 5 6 0) 4).card = 2 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_b6 : ksTypes (otherRows (extensionRow 5 6 0)) =
    (([{0,1,2,3,4},{2,3,4},{3},{3},{3},{3},{3},{0},{0},{0},{0},{0},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{0,1,4},{4},{0,3}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_b6 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (max w2 (max w3 w4)) + (5 * w3) + (5 * w0) + (max w0 (max w1 w4)) + w4 + (max w0 w3)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_b6 (a : Fin 5 → ℕ) : traceScore (otherRows (extensionRow 5 6 0)) a =
    ksForm_b6 (2 ^ (5 + a 0 - 3)) (2 ^ (5 + a 1 - 1)) (2 ^ (5 + a 2 - 1)) (2 ^ (5 + a 3 - 3)) (2 ^ (5 + a 4 - 2)) := by
  rw [ksExpand, ksTypes_b6]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_b6, show ((otherRows (extensionRow 5 6 0)) 0).card = 3 by decide +kernel, show ((otherRows (extensionRow 5 6 0)) 1).card = 1 by decide +kernel, show ((otherRows (extensionRow 5 6 0)) 2).card = 1 by decide +kernel, show ((otherRows (extensionRow 5 6 0)) 3).card = 3 by decide +kernel, show ((otherRows (extensionRow 5 6 0)) 4).card = 2 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_6_0 : ∀ d0 d1 d2 d3 d4 : Fin 4,
  512 ≤ ksForm_r6 (2 ^ (5 + d0.val - 1)) (2 ^ (5 + d1.val - 3)) (2 ^ (5 + d2.val - 3)) (2 ^ (5 + d3.val - 1)) (2 ^ (5 + d4.val - 2)) + ksForm_b6 (2 ^ (5 + (3 - d0.val) - 3)) (2 ^ (5 + (3 - d1.val) - 1)) (2 ^ (5 + (3 - d2.val) - 1)) (2 ^ (5 + (3 - d3.val) - 3)) (2 ^ (5 + (3 - d4.val) - 2)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_6_1 : ∀ d0 d1 d2 d3 d4 : Fin 5,
  (d0.val = 2 ∧ d1.val = 2 ∧ d2.val = 2 ∧ d3.val = 2 ∧ d4.val = 2) ∨ 768 ≤ ksForm_r6 (2 ^ (5 + d0.val - 1)) (2 ^ (5 + d1.val - 3)) (2 ^ (5 + d2.val - 3)) (2 ^ (5 + d3.val - 1)) (2 ^ (5 + d4.val - 2)) + ksForm_b6 (2 ^ (5 + (4 - d0.val) - 3)) (2 ^ (5 + (4 - d1.val) - 1)) (2 ^ (5 + (4 - d2.val) - 1)) (2 ^ (5 + (4 - d3.val) - 3)) (2 ^ (5 + (4 - d4.val) - 2)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFive_6 (a : Fin 5 → ℕ) (e : ℕ) (he : e ≤ 1)
    (hd : ∀ i, a i ≤ 3 + e) (hn : e = 0 ∨ ∃ i, a i ≠ 2) :
    128 * (4 + 2 * e) ≤ traceScore (extensionRow 5 6 0) a +
    traceScore (otherRows (extensionRow 5 6 0)) (fun i => 3+e-a i) := by
  have D0 := hd 0
  have D1 := hd 1
  have D2 := hd 2
  have D3 := hd 3
  have D4 := hd 4
  rw [ksFormEq_r6, ksFormEq_b6]
  rcases (show e = 0 ∨ e = 1 by omega) with rfl|rfl
  · exact ksCheck_6_0 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩
  · have hm : ¬(a 0 = 2 ∧ a 1 = 2 ∧ a 2 = 2 ∧ a 3 = 2 ∧ a 4 = 2) := by
      obtain ⟨i,hi⟩ := hn.resolve_left (by decide)
      intro h
      fin_cases i <;> simp_all
    exact (ksCheck_6_1 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩).resolve_left hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_r7 : ksTypes (extensionRow 5 7 0) =
    (([{0,1,2,3,4},{1,4},{1,4},{0,2,4},{4},{4},{4},{1,3,4},{2},{2},{2},{2},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{0,1,2},{1},{1},{1},{0,2}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_r7 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (2 * (max w1 w4)) + (max w0 (max w2 w4)) + (3 * w4) + (max w1 (max w3 w4)) + (4 * w2) + (max w0 (max w1 w2)) + (3 * w1) + (max w0 w2)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_r7 (a : Fin 5 → ℕ) : traceScore (extensionRow 5 7 0) a =
    ksForm_r7 (2 ^ (5 + a 0 - 2)) (2 ^ (5 + a 1 - 3)) (2 ^ (5 + a 2 - 3)) (2 ^ (5 + a 3 - 1)) (2 ^ (5 + a 4 - 3)) := by
  rw [ksExpand, ksTypes_r7]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_r7, show ((extensionRow 5 7 0) 0).card = 2 by decide +kernel, show ((extensionRow 5 7 0) 1).card = 3 by decide +kernel, show ((extensionRow 5 7 0) 2).card = 3 by decide +kernel, show ((extensionRow 5 7 0) 3).card = 1 by decide +kernel, show ((extensionRow 5 7 0) 4).card = 3 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_b7 : ksTypes (otherRows (extensionRow 5 7 0)) =
    (([{0,1,2,3,4},{2,3},{3},{3},{3},{3},{3},{3},{0},{0},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{0,1,4}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_b7 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (max w2 w3) + (6 * w3) + (2 * w0) + (max w0 (max w1 w4))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_b7 (a : Fin 5 → ℕ) : traceScore (otherRows (extensionRow 5 7 0)) a =
    ksForm_b7 (2 ^ (5 + a 0 - 2)) (2 ^ (5 + a 1 - 1)) (2 ^ (5 + a 2 - 1)) (2 ^ (5 + a 3 - 3)) (2 ^ (5 + a 4 - 1)) := by
  rw [ksExpand, ksTypes_b7]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_b7, show ((otherRows (extensionRow 5 7 0)) 0).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 7 0)) 1).card = 1 by decide +kernel, show ((otherRows (extensionRow 5 7 0)) 2).card = 1 by decide +kernel, show ((otherRows (extensionRow 5 7 0)) 3).card = 3 by decide +kernel, show ((otherRows (extensionRow 5 7 0)) 4).card = 1 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_7_0 : ∀ d0 d1 d2 d3 d4 : Fin 4,
  512 ≤ ksForm_r7 (2 ^ (5 + d0.val - 2)) (2 ^ (5 + d1.val - 3)) (2 ^ (5 + d2.val - 3)) (2 ^ (5 + d3.val - 1)) (2 ^ (5 + d4.val - 3)) + ksForm_b7 (2 ^ (5 + (3 - d0.val) - 2)) (2 ^ (5 + (3 - d1.val) - 1)) (2 ^ (5 + (3 - d2.val) - 1)) (2 ^ (5 + (3 - d3.val) - 3)) (2 ^ (5 + (3 - d4.val) - 1)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_7_1 : ∀ d0 d1 d2 d3 d4 : Fin 5,
  (d0.val = 2 ∧ d1.val = 2 ∧ d2.val = 2 ∧ d3.val = 2 ∧ d4.val = 2) ∨ 768 ≤ ksForm_r7 (2 ^ (5 + d0.val - 2)) (2 ^ (5 + d1.val - 3)) (2 ^ (5 + d2.val - 3)) (2 ^ (5 + d3.val - 1)) (2 ^ (5 + d4.val - 3)) + ksForm_b7 (2 ^ (5 + (4 - d0.val) - 2)) (2 ^ (5 + (4 - d1.val) - 1)) (2 ^ (5 + (4 - d2.val) - 1)) (2 ^ (5 + (4 - d3.val) - 3)) (2 ^ (5 + (4 - d4.val) - 1)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFive_7 (a : Fin 5 → ℕ) (e : ℕ) (he : e ≤ 1)
    (hd : ∀ i, a i ≤ 3 + e) (hn : e = 0 ∨ ∃ i, a i ≠ 2) :
    128 * (4 + 2 * e) ≤ traceScore (extensionRow 5 7 0) a +
    traceScore (otherRows (extensionRow 5 7 0)) (fun i => 3+e-a i) := by
  have D0 := hd 0
  have D1 := hd 1
  have D2 := hd 2
  have D3 := hd 3
  have D4 := hd 4
  rw [ksFormEq_r7, ksFormEq_b7]
  rcases (show e = 0 ∨ e = 1 by omega) with rfl|rfl
  · exact ksCheck_7_0 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩
  · have hm : ¬(a 0 = 2 ∧ a 1 = 2 ∧ a 2 = 2 ∧ a 3 = 2 ∧ a 4 = 2) := by
      obtain ⟨i,hi⟩ := hn.resolve_left (by decide)
      intro h
      fin_cases i <;> simp_all
    exact (ksCheck_7_1 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩).resolve_left hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_r8 : ksTypes (extensionRow 5 8 0) =
    (([{0,1,2,3,4},{1},{1},{0,2},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{1,3},{2,4},{2},{3},{3}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_r8 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (2 * w1) + (max w0 w2) + (max w1 w3) + (max w2 w4) + w2 + (2 * w3)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_r8 (a : Fin 5 → ℕ) : traceScore (extensionRow 5 8 0) a =
    ksForm_r8 (2 ^ (5 + a 0 - 1)) (2 ^ (5 + a 1 - 2)) (2 ^ (5 + a 2 - 2)) (2 ^ (5 + a 3 - 2)) (2 ^ (5 + a 4 - 1)) := by
  rw [ksExpand, ksTypes_r8]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_r8, show ((extensionRow 5 8 0) 0).card = 1 by decide +kernel, show ((extensionRow 5 8 0) 1).card = 2 by decide +kernel, show ((extensionRow 5 8 0) 2).card = 2 by decide +kernel, show ((extensionRow 5 8 0) 3).card = 2 by decide +kernel, show ((extensionRow 5 8 0) 4).card = 1 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_b8 : ksTypes (otherRows (extensionRow 5 8 0)) =
    (([{0,1,2,3,4},{2,3,4},{3,4},{3,4},{0,4},{4},{4},{4},{0,1},{0,1},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{0},{0},{0},{0,1,2},{2}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_b8 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (max w2 (max w3 w4)) + (2 * (max w3 w4)) + (max w0 w4) + (3 * w4) + (2 * (max w0 w1)) + (3 * w0) + (max w0 (max w1 w2)) + w2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_b8 (a : Fin 5 → ℕ) : traceScore (otherRows (extensionRow 5 8 0)) a =
    ksForm_b8 (2 ^ (5 + a 0 - 3)) (2 ^ (5 + a 1 - 2)) (2 ^ (5 + a 2 - 2)) (2 ^ (5 + a 3 - 2)) (2 ^ (5 + a 4 - 3)) := by
  rw [ksExpand, ksTypes_b8]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_b8, show ((otherRows (extensionRow 5 8 0)) 0).card = 3 by decide +kernel, show ((otherRows (extensionRow 5 8 0)) 1).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 8 0)) 2).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 8 0)) 3).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 8 0)) 4).card = 3 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_8_0 : ∀ d0 d1 d2 d3 d4 : Fin 4,
  512 ≤ ksForm_r8 (2 ^ (5 + d0.val - 1)) (2 ^ (5 + d1.val - 2)) (2 ^ (5 + d2.val - 2)) (2 ^ (5 + d3.val - 2)) (2 ^ (5 + d4.val - 1)) + ksForm_b8 (2 ^ (5 + (3 - d0.val) - 3)) (2 ^ (5 + (3 - d1.val) - 2)) (2 ^ (5 + (3 - d2.val) - 2)) (2 ^ (5 + (3 - d3.val) - 2)) (2 ^ (5 + (3 - d4.val) - 3)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_8_1 : ∀ d0 d1 d2 d3 d4 : Fin 5,
  (d0.val = 2 ∧ d1.val = 2 ∧ d2.val = 2 ∧ d3.val = 2 ∧ d4.val = 2) ∨ 768 ≤ ksForm_r8 (2 ^ (5 + d0.val - 1)) (2 ^ (5 + d1.val - 2)) (2 ^ (5 + d2.val - 2)) (2 ^ (5 + d3.val - 2)) (2 ^ (5 + d4.val - 1)) + ksForm_b8 (2 ^ (5 + (4 - d0.val) - 3)) (2 ^ (5 + (4 - d1.val) - 2)) (2 ^ (5 + (4 - d2.val) - 2)) (2 ^ (5 + (4 - d3.val) - 2)) (2 ^ (5 + (4 - d4.val) - 3)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFive_8 (a : Fin 5 → ℕ) (e : ℕ) (he : e ≤ 1)
    (hd : ∀ i, a i ≤ 3 + e) (hn : e = 0 ∨ ∃ i, a i ≠ 2) :
    128 * (4 + 2 * e) ≤ traceScore (extensionRow 5 8 0) a +
    traceScore (otherRows (extensionRow 5 8 0)) (fun i => 3+e-a i) := by
  have D0 := hd 0
  have D1 := hd 1
  have D2 := hd 2
  have D3 := hd 3
  have D4 := hd 4
  rw [ksFormEq_r8, ksFormEq_b8]
  rcases (show e = 0 ∨ e = 1 by omega) with rfl|rfl
  · exact ksCheck_8_0 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩
  · have hm : ¬(a 0 = 2 ∧ a 1 = 2 ∧ a 2 = 2 ∧ a 3 = 2 ∧ a 4 = 2) := by
      obtain ⟨i,hi⟩ := hn.resolve_left (by decide)
      intro h
      fin_cases i <;> simp_all
    exact (ksCheck_8_1 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩).resolve_left hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_r9 : ksTypes (extensionRow 5 9 0) =
    (([{0,1,2,3,4},{1,4},{0,2},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{1,3},{1},{2,4},{4},{2},{0,3},{0},{3}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_r9 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (max w1 w4) + (max w0 w2) + (max w1 w3) + w1 + (max w2 w4) + w4 + w2 + (max w0 w3) + w0 + w3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_r9 (a : Fin 5 → ℕ) : traceScore (extensionRow 5 9 0) a =
    ksForm_r9 (2 ^ (5 + a 0 - 2)) (2 ^ (5 + a 1 - 2)) (2 ^ (5 + a 2 - 2)) (2 ^ (5 + a 3 - 2)) (2 ^ (5 + a 4 - 2)) := by
  rw [ksExpand, ksTypes_r9]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_r9, show ((extensionRow 5 9 0) 0).card = 2 by decide +kernel, show ((extensionRow 5 9 0) 1).card = 2 by decide +kernel, show ((extensionRow 5 9 0) 2).card = 2 by decide +kernel, show ((extensionRow 5 9 0) 3).card = 2 by decide +kernel, show ((extensionRow 5 9 0) 4).card = 2 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_b9 : ksTypes (otherRows (extensionRow 5 9 0)) =
    (([{0,1,2,3,4},{2,3},{3,4},{3},{0,4},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{4},{0,1},{0},{1,2},{2},{1}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_b9 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (max w2 w3) + (max w3 w4) + w3 + (max w0 w4) + w4 + (max w0 w1) + w0 + (max w1 w2) + w2 + w1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_b9 (a : Fin 5 → ℕ) : traceScore (otherRows (extensionRow 5 9 0)) a =
    ksForm_b9 (2 ^ (5 + a 0 - 2)) (2 ^ (5 + a 1 - 2)) (2 ^ (5 + a 2 - 2)) (2 ^ (5 + a 3 - 2)) (2 ^ (5 + a 4 - 2)) := by
  rw [ksExpand, ksTypes_b9]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_b9, show ((otherRows (extensionRow 5 9 0)) 0).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 9 0)) 1).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 9 0)) 2).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 9 0)) 3).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 9 0)) 4).card = 2 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_9_0 : ∀ d0 d1 d2 d3 d4 : Fin 4,
  512 ≤ ksForm_r9 (2 ^ (5 + d0.val - 2)) (2 ^ (5 + d1.val - 2)) (2 ^ (5 + d2.val - 2)) (2 ^ (5 + d3.val - 2)) (2 ^ (5 + d4.val - 2)) + ksForm_b9 (2 ^ (5 + (3 - d0.val) - 2)) (2 ^ (5 + (3 - d1.val) - 2)) (2 ^ (5 + (3 - d2.val) - 2)) (2 ^ (5 + (3 - d3.val) - 2)) (2 ^ (5 + (3 - d4.val) - 2)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_9_1 : ∀ d0 d1 d2 d3 d4 : Fin 5,
  (d0.val = 2 ∧ d1.val = 2 ∧ d2.val = 2 ∧ d3.val = 2 ∧ d4.val = 2) ∨ 768 ≤ ksForm_r9 (2 ^ (5 + d0.val - 2)) (2 ^ (5 + d1.val - 2)) (2 ^ (5 + d2.val - 2)) (2 ^ (5 + d3.val - 2)) (2 ^ (5 + d4.val - 2)) + ksForm_b9 (2 ^ (5 + (4 - d0.val) - 2)) (2 ^ (5 + (4 - d1.val) - 2)) (2 ^ (5 + (4 - d2.val) - 2)) (2 ^ (5 + (4 - d3.val) - 2)) (2 ^ (5 + (4 - d4.val) - 2)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFive_9 (a : Fin 5 → ℕ) (e : ℕ) (he : e ≤ 1)
    (hd : ∀ i, a i ≤ 3 + e) (hn : e = 0 ∨ ∃ i, a i ≠ 2) :
    128 * (4 + 2 * e) ≤ traceScore (extensionRow 5 9 0) a +
    traceScore (otherRows (extensionRow 5 9 0)) (fun i => 3+e-a i) := by
  have D0 := hd 0
  have D1 := hd 1
  have D2 := hd 2
  have D3 := hd 3
  have D4 := hd 4
  rw [ksFormEq_r9, ksFormEq_b9]
  rcases (show e = 0 ∨ e = 1 by omega) with rfl|rfl
  · exact ksCheck_9_0 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩
  · have hm : ¬(a 0 = 2 ∧ a 1 = 2 ∧ a 2 = 2 ∧ a 3 = 2 ∧ a 4 = 2) := by
      obtain ⟨i,hi⟩ := hn.resolve_left (by decide)
      intro h
      fin_cases i <;> simp_all
    exact (ksCheck_9_1 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩).resolve_left hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_r10 : ksTypes (extensionRow 5 10 0) =
    (([{0,1,2,3,4},{1},{1},{1},{1},{0,2,4},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{1,3},{1,3},{1,3},{2,4},{2,4}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_r10 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (4 * w1) + (max w0 (max w2 w4)) + (3 * (max w1 w3)) + (2 * (max w2 w4))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_r10 (a : Fin 5 → ℕ) : traceScore (extensionRow 5 10 0) a =
    ksForm_r10 (2 ^ (5 + a 0 - 1)) (2 ^ (5 + a 1 - 3)) (2 ^ (5 + a 2 - 2)) (2 ^ (5 + a 3 - 2)) (2 ^ (5 + a 4 - 2)) := by
  rw [ksExpand, ksTypes_r10]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_r10, show ((extensionRow 5 10 0) 0).card = 1 by decide +kernel, show ((extensionRow 5 10 0) 1).card = 3 by decide +kernel, show ((extensionRow 5 10 0) 2).card = 2 by decide +kernel, show ((extensionRow 5 10 0) 3).card = 2 by decide +kernel, show ((extensionRow 5 10 0) 4).card = 2 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_b10 : ksTypes (otherRows (extensionRow 5 10 0)) =
    (([{0,1,2,3,4},{2,3,4},{3},{3},{0,4},{4},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{0,1},{0},{0},{0},{0},{0,2},{2}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_b10 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (max w2 (max w3 w4)) + (2 * w3) + (max w0 w4) + w4 + (max w0 w1) + (4 * w0) + (max w0 w2) + w2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_b10 (a : Fin 5 → ℕ) : traceScore (otherRows (extensionRow 5 10 0)) a =
    ksForm_b10 (2 ^ (5 + a 0 - 3)) (2 ^ (5 + a 1 - 1)) (2 ^ (5 + a 2 - 2)) (2 ^ (5 + a 3 - 2)) (2 ^ (5 + a 4 - 2)) := by
  rw [ksExpand, ksTypes_b10]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_b10, show ((otherRows (extensionRow 5 10 0)) 0).card = 3 by decide +kernel, show ((otherRows (extensionRow 5 10 0)) 1).card = 1 by decide +kernel, show ((otherRows (extensionRow 5 10 0)) 2).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 10 0)) 3).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 10 0)) 4).card = 2 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_10_0 : ∀ d0 d1 d2 d3 d4 : Fin 4,
  512 ≤ ksForm_r10 (2 ^ (5 + d0.val - 1)) (2 ^ (5 + d1.val - 3)) (2 ^ (5 + d2.val - 2)) (2 ^ (5 + d3.val - 2)) (2 ^ (5 + d4.val - 2)) + ksForm_b10 (2 ^ (5 + (3 - d0.val) - 3)) (2 ^ (5 + (3 - d1.val) - 1)) (2 ^ (5 + (3 - d2.val) - 2)) (2 ^ (5 + (3 - d3.val) - 2)) (2 ^ (5 + (3 - d4.val) - 2)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_10_1 : ∀ d0 d1 d2 d3 d4 : Fin 5,
  (d0.val = 2 ∧ d1.val = 2 ∧ d2.val = 2 ∧ d3.val = 2 ∧ d4.val = 2) ∨ 768 ≤ ksForm_r10 (2 ^ (5 + d0.val - 1)) (2 ^ (5 + d1.val - 3)) (2 ^ (5 + d2.val - 2)) (2 ^ (5 + d3.val - 2)) (2 ^ (5 + d4.val - 2)) + ksForm_b10 (2 ^ (5 + (4 - d0.val) - 3)) (2 ^ (5 + (4 - d1.val) - 1)) (2 ^ (5 + (4 - d2.val) - 2)) (2 ^ (5 + (4 - d3.val) - 2)) (2 ^ (5 + (4 - d4.val) - 2)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFive_10 (a : Fin 5 → ℕ) (e : ℕ) (he : e ≤ 1)
    (hd : ∀ i, a i ≤ 3 + e) (hn : e = 0 ∨ ∃ i, a i ≠ 2) :
    128 * (4 + 2 * e) ≤ traceScore (extensionRow 5 10 0) a +
    traceScore (otherRows (extensionRow 5 10 0)) (fun i => 3+e-a i) := by
  have D0 := hd 0
  have D1 := hd 1
  have D2 := hd 2
  have D3 := hd 3
  have D4 := hd 4
  rw [ksFormEq_r10, ksFormEq_b10]
  rcases (show e = 0 ∨ e = 1 by omega) with rfl|rfl
  · exact ksCheck_10_0 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩
  · have hm : ¬(a 0 = 2 ∧ a 1 = 2 ∧ a 2 = 2 ∧ a 3 = 2 ∧ a 4 = 2) := by
      obtain ⟨i,hi⟩ := hn.resolve_left (by decide)
      intro h
      fin_cases i <;> simp_all
    exact (ksCheck_10_1 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩).resolve_left hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_r11 : ksTypes (extensionRow 5 11 0) =
    (([{0,1,2,3,4},{1,4},{0,2,4},{4},{4},{4},{1,3},{1,3},{1},{1},{1},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{2,4},{2,4},{0,1,3},{0}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_r11 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (max w1 w4) + (max w0 (max w2 w4)) + (3 * w4) + (2 * (max w1 w3)) + (3 * w1) + (2 * (max w2 w4)) + (max w0 (max w1 w3)) + w0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_r11 (a : Fin 5 → ℕ) : traceScore (extensionRow 5 11 0) a =
    ksForm_r11 (2 ^ (5 + a 0 - 2)) (2 ^ (5 + a 1 - 3)) (2 ^ (5 + a 2 - 2)) (2 ^ (5 + a 3 - 2)) (2 ^ (5 + a 4 - 3)) := by
  rw [ksExpand, ksTypes_r11]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_r11, show ((extensionRow 5 11 0) 0).card = 2 by decide +kernel, show ((extensionRow 5 11 0) 1).card = 3 by decide +kernel, show ((extensionRow 5 11 0) 2).card = 2 by decide +kernel, show ((extensionRow 5 11 0) 3).card = 2 by decide +kernel, show ((extensionRow 5 11 0) 4).card = 3 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_b11 : ksTypes (otherRows (extensionRow 5 11 0)) =
    (([{0,1,2,3,4},{2,3},{3},{3},{0,4},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{0,1},{0},{2},{2}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_b11 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (max w2 w3) + (2 * w3) + (max w0 w4) + (max w0 w1) + w0 + (2 * w2)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_b11 (a : Fin 5 → ℕ) : traceScore (otherRows (extensionRow 5 11 0)) a =
    ksForm_b11 (2 ^ (5 + a 0 - 2)) (2 ^ (5 + a 1 - 1)) (2 ^ (5 + a 2 - 2)) (2 ^ (5 + a 3 - 2)) (2 ^ (5 + a 4 - 1)) := by
  rw [ksExpand, ksTypes_b11]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_b11, show ((otherRows (extensionRow 5 11 0)) 0).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 11 0)) 1).card = 1 by decide +kernel, show ((otherRows (extensionRow 5 11 0)) 2).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 11 0)) 3).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 11 0)) 4).card = 1 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_11_0 : ∀ d0 d1 d2 d3 d4 : Fin 4,
  512 ≤ ksForm_r11 (2 ^ (5 + d0.val - 2)) (2 ^ (5 + d1.val - 3)) (2 ^ (5 + d2.val - 2)) (2 ^ (5 + d3.val - 2)) (2 ^ (5 + d4.val - 3)) + ksForm_b11 (2 ^ (5 + (3 - d0.val) - 2)) (2 ^ (5 + (3 - d1.val) - 1)) (2 ^ (5 + (3 - d2.val) - 2)) (2 ^ (5 + (3 - d3.val) - 2)) (2 ^ (5 + (3 - d4.val) - 1)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_11_1 : ∀ d0 d1 d2 d3 d4 : Fin 5,
  (d0.val = 2 ∧ d1.val = 2 ∧ d2.val = 2 ∧ d3.val = 2 ∧ d4.val = 2) ∨ 768 ≤ ksForm_r11 (2 ^ (5 + d0.val - 2)) (2 ^ (5 + d1.val - 3)) (2 ^ (5 + d2.val - 2)) (2 ^ (5 + d3.val - 2)) (2 ^ (5 + d4.val - 3)) + ksForm_b11 (2 ^ (5 + (4 - d0.val) - 2)) (2 ^ (5 + (4 - d1.val) - 1)) (2 ^ (5 + (4 - d2.val) - 2)) (2 ^ (5 + (4 - d3.val) - 2)) (2 ^ (5 + (4 - d4.val) - 1)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFive_11 (a : Fin 5 → ℕ) (e : ℕ) (he : e ≤ 1)
    (hd : ∀ i, a i ≤ 3 + e) (hn : e = 0 ∨ ∃ i, a i ≠ 2) :
    128 * (4 + 2 * e) ≤ traceScore (extensionRow 5 11 0) a +
    traceScore (otherRows (extensionRow 5 11 0)) (fun i => 3+e-a i) := by
  have D0 := hd 0
  have D1 := hd 1
  have D2 := hd 2
  have D3 := hd 3
  have D4 := hd 4
  rw [ksFormEq_r11, ksFormEq_b11]
  rcases (show e = 0 ∨ e = 1 by omega) with rfl|rfl
  · exact ksCheck_11_0 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩
  · have hm : ¬(a 0 = 2 ∧ a 1 = 2 ∧ a 2 = 2 ∧ a 3 = 2 ∧ a 4 = 2) := by
      obtain ⟨i,hi⟩ := hn.resolve_left (by decide)
      intro h
      fin_cases i <;> simp_all
    exact (ksCheck_11_1 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩).resolve_left hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_r12 : ksTypes (extensionRow 5 12 0) =
    (([{0,1,2,3,4},{1},{1},{0,2},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{1,3,4},{2,4},{2},{2},{2},{2},{4},{2,3},{3}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_r12 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (2 * w1) + (max w0 w2) + (max w1 (max w3 w4)) + (max w2 w4) + (4 * w2) + w4 + (max w2 w3) + w3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_r12 (a : Fin 5 → ℕ) : traceScore (extensionRow 5 12 0) a =
    ksForm_r12 (2 ^ (5 + a 0 - 1)) (2 ^ (5 + a 1 - 2)) (2 ^ (5 + a 2 - 3)) (2 ^ (5 + a 3 - 2)) (2 ^ (5 + a 4 - 2)) := by
  rw [ksExpand, ksTypes_r12]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_r12, show ((extensionRow 5 12 0) 0).card = 1 by decide +kernel, show ((extensionRow 5 12 0) 1).card = 2 by decide +kernel, show ((extensionRow 5 12 0) 2).card = 3 by decide +kernel, show ((extensionRow 5 12 0) 3).card = 2 by decide +kernel, show ((extensionRow 5 12 0) 4).card = 2 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_b12 : ksTypes (otherRows (extensionRow 5 12 0)) =
    (([{0,1,2,3,4},{2,3,4},{3,4},{3,4},{0},{0},{0},{0},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{0,1},{0,1},{0,1}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_b12 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (max w2 (max w3 w4)) + (2 * (max w3 w4)) + (4 * w0) + (3 * (max w0 w1))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_b12 (a : Fin 5 → ℕ) : traceScore (otherRows (extensionRow 5 12 0)) a =
    ksForm_b12 (2 ^ (5 + a 0 - 3)) (2 ^ (5 + a 1 - 2)) (2 ^ (5 + a 2 - 1)) (2 ^ (5 + a 3 - 2)) (2 ^ (5 + a 4 - 2)) := by
  rw [ksExpand, ksTypes_b12]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_b12, show ((otherRows (extensionRow 5 12 0)) 0).card = 3 by decide +kernel, show ((otherRows (extensionRow 5 12 0)) 1).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 12 0)) 2).card = 1 by decide +kernel, show ((otherRows (extensionRow 5 12 0)) 3).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 12 0)) 4).card = 2 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_12_0 : ∀ d0 d1 d2 d3 d4 : Fin 4,
  512 ≤ ksForm_r12 (2 ^ (5 + d0.val - 1)) (2 ^ (5 + d1.val - 2)) (2 ^ (5 + d2.val - 3)) (2 ^ (5 + d3.val - 2)) (2 ^ (5 + d4.val - 2)) + ksForm_b12 (2 ^ (5 + (3 - d0.val) - 3)) (2 ^ (5 + (3 - d1.val) - 2)) (2 ^ (5 + (3 - d2.val) - 1)) (2 ^ (5 + (3 - d3.val) - 2)) (2 ^ (5 + (3 - d4.val) - 2)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_12_1 : ∀ d0 d1 d2 d3 d4 : Fin 5,
  (d0.val = 2 ∧ d1.val = 2 ∧ d2.val = 2 ∧ d3.val = 2 ∧ d4.val = 2) ∨ 768 ≤ ksForm_r12 (2 ^ (5 + d0.val - 1)) (2 ^ (5 + d1.val - 2)) (2 ^ (5 + d2.val - 3)) (2 ^ (5 + d3.val - 2)) (2 ^ (5 + d4.val - 2)) + ksForm_b12 (2 ^ (5 + (4 - d0.val) - 3)) (2 ^ (5 + (4 - d1.val) - 2)) (2 ^ (5 + (4 - d2.val) - 1)) (2 ^ (5 + (4 - d3.val) - 2)) (2 ^ (5 + (4 - d4.val) - 2)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFive_12 (a : Fin 5 → ℕ) (e : ℕ) (he : e ≤ 1)
    (hd : ∀ i, a i ≤ 3 + e) (hn : e = 0 ∨ ∃ i, a i ≠ 2) :
    128 * (4 + 2 * e) ≤ traceScore (extensionRow 5 12 0) a +
    traceScore (otherRows (extensionRow 5 12 0)) (fun i => 3+e-a i) := by
  have D0 := hd 0
  have D1 := hd 1
  have D2 := hd 2
  have D3 := hd 3
  have D4 := hd 4
  rw [ksFormEq_r12, ksFormEq_b12]
  rcases (show e = 0 ∨ e = 1 by omega) with rfl|rfl
  · exact ksCheck_12_0 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩
  · have hm : ¬(a 0 = 2 ∧ a 1 = 2 ∧ a 2 = 2 ∧ a 3 = 2 ∧ a 4 = 2) := by
      obtain ⟨i,hi⟩ := hn.resolve_left (by decide)
      intro h
      fin_cases i <;> simp_all
    exact (ksCheck_12_1 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩).resolve_left hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_r13 : ksTypes (extensionRow 5 13 0) =
    (([{0,1,2,3,4},{1,4},{1,4},{0,2},{0,2},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{1,3,4},{2,4},{4},{4},{4},{2},{2},{2},{0,2,3},{3}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_r13 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (2 * (max w1 w4)) + (2 * (max w0 w2)) + (max w1 (max w3 w4)) + (max w2 w4) + (3 * w4) + (3 * w2) + (max w0 (max w2 w3)) + w3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_r13 (a : Fin 5 → ℕ) : traceScore (extensionRow 5 13 0) a =
    ksForm_r13 (2 ^ (5 + a 0 - 2)) (2 ^ (5 + a 1 - 2)) (2 ^ (5 + a 2 - 3)) (2 ^ (5 + a 3 - 2)) (2 ^ (5 + a 4 - 3)) := by
  rw [ksExpand, ksTypes_r13]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_r13, show ((extensionRow 5 13 0) 0).card = 2 by decide +kernel, show ((extensionRow 5 13 0) 1).card = 2 by decide +kernel, show ((extensionRow 5 13 0) 2).card = 3 by decide +kernel, show ((extensionRow 5 13 0) 3).card = 2 by decide +kernel, show ((extensionRow 5 13 0) 4).card = 3 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_b13 : ksTypes (otherRows (extensionRow 5 13 0)) =
    (([{0,1,2,3,4},{2,3},{3,4},{3},{0},{0},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{0,1},{1},{1}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_b13 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (max w2 w3) + (max w3 w4) + w3 + (2 * w0) + (max w0 w1) + (2 * w1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_b13 (a : Fin 5 → ℕ) : traceScore (otherRows (extensionRow 5 13 0)) a =
    ksForm_b13 (2 ^ (5 + a 0 - 2)) (2 ^ (5 + a 1 - 2)) (2 ^ (5 + a 2 - 1)) (2 ^ (5 + a 3 - 2)) (2 ^ (5 + a 4 - 1)) := by
  rw [ksExpand, ksTypes_b13]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_b13, show ((otherRows (extensionRow 5 13 0)) 0).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 13 0)) 1).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 13 0)) 2).card = 1 by decide +kernel, show ((otherRows (extensionRow 5 13 0)) 3).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 13 0)) 4).card = 1 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_13_0 : ∀ d0 d1 d2 d3 d4 : Fin 4,
  512 ≤ ksForm_r13 (2 ^ (5 + d0.val - 2)) (2 ^ (5 + d1.val - 2)) (2 ^ (5 + d2.val - 3)) (2 ^ (5 + d3.val - 2)) (2 ^ (5 + d4.val - 3)) + ksForm_b13 (2 ^ (5 + (3 - d0.val) - 2)) (2 ^ (5 + (3 - d1.val) - 2)) (2 ^ (5 + (3 - d2.val) - 1)) (2 ^ (5 + (3 - d3.val) - 2)) (2 ^ (5 + (3 - d4.val) - 1)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_13_1 : ∀ d0 d1 d2 d3 d4 : Fin 5,
  (d0.val = 2 ∧ d1.val = 2 ∧ d2.val = 2 ∧ d3.val = 2 ∧ d4.val = 2) ∨ 768 ≤ ksForm_r13 (2 ^ (5 + d0.val - 2)) (2 ^ (5 + d1.val - 2)) (2 ^ (5 + d2.val - 3)) (2 ^ (5 + d3.val - 2)) (2 ^ (5 + d4.val - 3)) + ksForm_b13 (2 ^ (5 + (4 - d0.val) - 2)) (2 ^ (5 + (4 - d1.val) - 2)) (2 ^ (5 + (4 - d2.val) - 1)) (2 ^ (5 + (4 - d3.val) - 2)) (2 ^ (5 + (4 - d4.val) - 1)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFive_13 (a : Fin 5 → ℕ) (e : ℕ) (he : e ≤ 1)
    (hd : ∀ i, a i ≤ 3 + e) (hn : e = 0 ∨ ∃ i, a i ≠ 2) :
    128 * (4 + 2 * e) ≤ traceScore (extensionRow 5 13 0) a +
    traceScore (otherRows (extensionRow 5 13 0)) (fun i => 3+e-a i) := by
  have D0 := hd 0
  have D1 := hd 1
  have D2 := hd 2
  have D3 := hd 3
  have D4 := hd 4
  rw [ksFormEq_r13, ksFormEq_b13]
  rcases (show e = 0 ∨ e = 1 by omega) with rfl|rfl
  · exact ksCheck_13_0 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩
  · have hm : ¬(a 0 = 2 ∧ a 1 = 2 ∧ a 2 = 2 ∧ a 3 = 2 ∧ a 4 = 2) := by
      obtain ⟨i,hi⟩ := hn.resolve_left (by decide)
      intro h
      fin_cases i <;> simp_all
    exact (ksCheck_13_1 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩).resolve_left hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_r14 : ksTypes (extensionRow 5 14 0) =
    (([{0,1,2,3,4},{1},{1},{1},{1},{0,2,4},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{1,3,4},{4},{4},{4},{2,4},{2,4},{1,2,3},{2},{2},{2},{1,3}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_r14 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (4 * w1) + (max w0 (max w2 w4)) + (max w1 (max w3 w4)) + (3 * w4) + (2 * (max w2 w4)) + (max w1 (max w2 w3)) + (3 * w2) + (max w1 w3)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_r14 (a : Fin 5 → ℕ) : traceScore (extensionRow 5 14 0) a =
    ksForm_r14 (2 ^ (5 + a 0 - 1)) (2 ^ (5 + a 1 - 3)) (2 ^ (5 + a 2 - 3)) (2 ^ (5 + a 3 - 2)) (2 ^ (5 + a 4 - 3)) := by
  rw [ksExpand, ksTypes_r14]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_r14, show ((extensionRow 5 14 0) 0).card = 1 by decide +kernel, show ((extensionRow 5 14 0) 1).card = 3 by decide +kernel, show ((extensionRow 5 14 0) 2).card = 3 by decide +kernel, show ((extensionRow 5 14 0) 3).card = 2 by decide +kernel, show ((extensionRow 5 14 0) 4).card = 3 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_b14 : ksTypes (otherRows (extensionRow 5 14 0)) =
    (([{0,1,2,3,4},{2,3,4},{3},{3},{0},{0},{0},{0},{0},{0},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{0,1}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_b14 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (max w2 (max w3 w4)) + (2 * w3) + (6 * w0) + (max w0 w1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_b14 (a : Fin 5 → ℕ) : traceScore (otherRows (extensionRow 5 14 0)) a =
    ksForm_b14 (2 ^ (5 + a 0 - 3)) (2 ^ (5 + a 1 - 1)) (2 ^ (5 + a 2 - 1)) (2 ^ (5 + a 3 - 2)) (2 ^ (5 + a 4 - 1)) := by
  rw [ksExpand, ksTypes_b14]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_b14, show ((otherRows (extensionRow 5 14 0)) 0).card = 3 by decide +kernel, show ((otherRows (extensionRow 5 14 0)) 1).card = 1 by decide +kernel, show ((otherRows (extensionRow 5 14 0)) 2).card = 1 by decide +kernel, show ((otherRows (extensionRow 5 14 0)) 3).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 14 0)) 4).card = 1 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_14_0 : ∀ d0 d1 d2 d3 d4 : Fin 4,
  512 ≤ ksForm_r14 (2 ^ (5 + d0.val - 1)) (2 ^ (5 + d1.val - 3)) (2 ^ (5 + d2.val - 3)) (2 ^ (5 + d3.val - 2)) (2 ^ (5 + d4.val - 3)) + ksForm_b14 (2 ^ (5 + (3 - d0.val) - 3)) (2 ^ (5 + (3 - d1.val) - 1)) (2 ^ (5 + (3 - d2.val) - 1)) (2 ^ (5 + (3 - d3.val) - 2)) (2 ^ (5 + (3 - d4.val) - 1)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_14_1 : ∀ d0 d1 d2 d3 d4 : Fin 5,
  (d0.val = 2 ∧ d1.val = 2 ∧ d2.val = 2 ∧ d3.val = 2 ∧ d4.val = 2) ∨ 768 ≤ ksForm_r14 (2 ^ (5 + d0.val - 1)) (2 ^ (5 + d1.val - 3)) (2 ^ (5 + d2.val - 3)) (2 ^ (5 + d3.val - 2)) (2 ^ (5 + d4.val - 3)) + ksForm_b14 (2 ^ (5 + (4 - d0.val) - 3)) (2 ^ (5 + (4 - d1.val) - 1)) (2 ^ (5 + (4 - d2.val) - 1)) (2 ^ (5 + (4 - d3.val) - 2)) (2 ^ (5 + (4 - d4.val) - 1)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFive_14 (a : Fin 5 → ℕ) (e : ℕ) (he : e ≤ 1)
    (hd : ∀ i, a i ≤ 3 + e) (hn : e = 0 ∨ ∃ i, a i ≠ 2) :
    128 * (4 + 2 * e) ≤ traceScore (extensionRow 5 14 0) a +
    traceScore (otherRows (extensionRow 5 14 0)) (fun i => 3+e-a i) := by
  have D0 := hd 0
  have D1 := hd 1
  have D2 := hd 2
  have D3 := hd 3
  have D4 := hd 4
  rw [ksFormEq_r14, ksFormEq_b14]
  rcases (show e = 0 ∨ e = 1 by omega) with rfl|rfl
  · exact ksCheck_14_0 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩
  · have hm : ¬(a 0 = 2 ∧ a 1 = 2 ∧ a 2 = 2 ∧ a 3 = 2 ∧ a 4 = 2) := by
      obtain ⟨i,hi⟩ := hn.resolve_left (by decide)
      intro h
      fin_cases i <;> simp_all
    exact (ksCheck_14_1 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩).resolve_left hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_r15 : ksTypes (extensionRow 5 15 0) =
    (([{0,1,2,3,4},{1,4},{1,4},{0,2,4},{4},{4},{4},{4},{4},{4},{4},{4},{4},{1,3,4},{2,4},{2,4},{0,1,2,3},{1},{1},{0,2},∅,∅,∅,∅,∅,∅,∅,∅,∅,{1,3},{2},{2}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_r15 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (2 * (max w1 w4)) + (max w0 (max w2 w4)) + (9 * w4) + (max w1 (max w3 w4)) + (2 * (max w2 w4)) + (max w0 (max w1 (max w2 w3))) + (2 * w1) + (max w0 w2) + (max w1 w3) + (2 * w2)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_r15 (a : Fin 5 → ℕ) : traceScore (extensionRow 5 15 0) a =
    ksForm_r15 (2 ^ (5 + a 0 - 2)) (2 ^ (5 + a 1 - 3)) (2 ^ (5 + a 2 - 3)) (2 ^ (5 + a 3 - 2)) (2 ^ (5 + a 4 - 4)) := by
  rw [ksExpand, ksTypes_r15]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_r15, show ((extensionRow 5 15 0) 0).card = 2 by decide +kernel, show ((extensionRow 5 15 0) 1).card = 3 by decide +kernel, show ((extensionRow 5 15 0) 2).card = 3 by decide +kernel, show ((extensionRow 5 15 0) 3).card = 2 by decide +kernel, show ((extensionRow 5 15 0) 4).card = 4 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksTypes_b15 : ksTypes (otherRows (extensionRow 5 15 0)) =
    (([{0,1,2,3,4},{2,3},{3},{3},{0},{0},∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,∅,{0,1}] : List (Finset (Fin 5))) : Multiset (Finset (Fin 5))) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def ksForm_b15 (w0 w1 w2 w3 w4 : ℕ) : ℕ :=
  (max w0 (max w1 (max w2 (max w3 w4)))) + (max w2 w3) + (2 * w3) + (2 * w0) + (max w0 w1)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFormEq_b15 (a : Fin 5 → ℕ) : traceScore (otherRows (extensionRow 5 15 0)) a =
    ksForm_b15 (2 ^ (5 + a 0 - 2)) (2 ^ (5 + a 1 - 1)) (2 ^ (5 + a 2 - 1)) (2 ^ (5 + a 3 - 2)) (2 ^ (5 + a 4 - 0)) := by
  rw [ksExpand, ksTypes_b15]
  simp only [Multiset.map_coe, Multiset.sum_coe, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Finset.sup_insert, Finset.sup_singleton, Finset.sup_empty, Nat.bot_eq_zero]
  simp only [ksForm_b15, show ((otherRows (extensionRow 5 15 0)) 0).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 15 0)) 1).card = 1 by decide +kernel, show ((otherRows (extensionRow 5 15 0)) 2).card = 1 by decide +kernel, show ((otherRows (extensionRow 5 15 0)) 3).card = 2 by decide +kernel, show ((otherRows (extensionRow 5 15 0)) 4).card = 0 by decide +kernel]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_15_0 : ∀ d0 d1 d2 d3 d4 : Fin 4,
  512 ≤ ksForm_r15 (2 ^ (5 + d0.val - 2)) (2 ^ (5 + d1.val - 3)) (2 ^ (5 + d2.val - 3)) (2 ^ (5 + d3.val - 2)) (2 ^ (5 + d4.val - 4)) + ksForm_b15 (2 ^ (5 + (3 - d0.val) - 2)) (2 ^ (5 + (3 - d1.val) - 1)) (2 ^ (5 + (3 - d2.val) - 1)) (2 ^ (5 + (3 - d3.val) - 2)) (2 ^ (5 + (3 - d4.val) - 0)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksCheck_15_1 : ∀ d0 d1 d2 d3 d4 : Fin 5,
  (d0.val = 2 ∧ d1.val = 2 ∧ d2.val = 2 ∧ d3.val = 2 ∧ d4.val = 2) ∨ 768 ≤ ksForm_r15 (2 ^ (5 + d0.val - 2)) (2 ^ (5 + d1.val - 3)) (2 ^ (5 + d2.val - 3)) (2 ^ (5 + d3.val - 2)) (2 ^ (5 + d4.val - 4)) + ksForm_b15 (2 ^ (5 + (4 - d0.val) - 2)) (2 ^ (5 + (4 - d1.val) - 1)) (2 ^ (5 + (4 - d2.val) - 1)) (2 ^ (5 + (4 - d3.val) - 2)) (2 ^ (5 + (4 - d4.val) - 0)) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksFive_15 (a : Fin 5 → ℕ) (e : ℕ) (he : e ≤ 1)
    (hd : ∀ i, a i ≤ 3 + e) (hn : e = 0 ∨ ∃ i, a i ≠ 2) :
    128 * (4 + 2 * e) ≤ traceScore (extensionRow 5 15 0) a +
    traceScore (otherRows (extensionRow 5 15 0)) (fun i => 3+e-a i) := by
  have D0 := hd 0
  have D1 := hd 1
  have D2 := hd 2
  have D3 := hd 3
  have D4 := hd 4
  rw [ksFormEq_r15, ksFormEq_b15]
  rcases (show e = 0 ∨ e = 1 by omega) with rfl|rfl
  · exact ksCheck_15_0 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩
  · have hm : ¬(a 0 = 2 ∧ a 1 = 2 ∧ a 2 = 2 ∧ a 3 = 2 ∧ a 4 = 2) := by
      obtain ⟨i,hi⟩ := hn.resolve_left (by decide)
      intro h
      fin_cases i <;> simp_all
    exact (ksCheck_15_1 ⟨a 0,by omega⟩ ⟨a 1,by omega⟩ ⟨a 2,by omega⟩ ⟨a 3,by omega⟩ ⟨a 4,by omega⟩).resolve_left hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem traceFive (r : Fin 5 → Finset (Fin 5)) (a : Fin 5 → ℕ) (e : ℕ)
    (he : e ≤ 1) (hd : ∀ i, a i ≤ 3+e) (hn : e = 0 ∨ ∃ i, a i ≠ 2)
    (hdiag : ∀ i, i ∉ r i) (hsym : ∀ i j, j ∈ r i ↔ i ∈ r j)
    (hp : ∀ i j : Fin 5, i.val < 4 → j.val < 4 →
      (j ∈ r i ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val)) :
    128 * (4 + 2 * e) ≤ traceScore r a + traceScore (otherRows r) (fun i => 3+e-a i) := by
  obtain ⟨s,rfl⟩ := extensionFive r hdiag hsym hp
  fin_cases s
  · exact ksFive_0 a e he hd hn
  · exact ksFive_1 a e he hd hn
  · exact ksFive_2 a e he hd hn
  · exact ksFive_3 a e he hd hn
  · exact ksFive_4 a e he hd hn
  · exact ksFive_5 a e he hd hn
  · exact ksFive_6 a e he hd hn
  · exact ksFive_7 a e he hd hn
  · exact ksFive_8 a e he hd hn
  · exact ksFive_9 a e he hd hn
  · exact ksFive_10 a e he hd hn
  · exact ksFive_11 a e he hd hn
  · exact ksFive_12 a e he hd hn
  · exact ksFive_13 a e he hd hn
  · exact ksFive_14 a e he hd hn
  · exact ksFive_15 a e he hd hn
end KeoughShane

end

section

namespace KeoughShane
open Finset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def maskSet6 (t : Fin 64) : Finset (Fin 6) :=
  univ.filter fun i => t.val.testBit i.val = true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem maskSet6_inj : ∀ s t, maskSet6 s = maskSet6 t → s = t := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem maskSet6_onto : ∀ s : Finset (Fin 6), ∃ t, maskSet6 t = s := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem maskSet6_subset : ∀ s t, maskSet6 s ⊆ maskSet6 t ↔ s.val &&& t.val = s.val := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def weight6 (t : Fin 64) : ℕ := (105570068798314395538251903218480757014590774532022492153390641249815059870575305637624477384559100637675102450772684398750976904354333826321509867602048 >>> (8*t.val)) &&& 255
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem weight6_spec : ∀ t, 2^(5 + 2 - (maskSet6 t).card) = weight6 t := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def rawRed6 (a b i : ℕ) : ℕ :=
  if i = 5 then b else (if b.testBit i then 32 else 0) +
  (if i = 4 then a else (if a.testBit i then 16 else 0) +
    (if i = 0 then 2 else if i = 1 then 5 else if i = 2 then 10 else 4))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def packed6 (a : Fin 16) (b : Fin 32) (blue : Bool) (i : Fin 6) : Fin 64 :=
  let red := rawRed6 a.val b.val i.val
  let v := if blue then (63 ^^^ (1 <<< i.val)) ^^^ red else red
  ⟨v % 64, Nat.mod_lt _ (by decide)⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem packed6_red : ∀ (a : Fin 16) (b : Fin 32) (i : Fin 6),
    extensionRow 6 a.val b.val i = maskSet6 (packed6 a b false i) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem packed6_blue : ∀ (a : Fin 16) (b : Fin 32) (i : Fin 6),
    otherRows (extensionRow 6 a.val b.val) i = maskSet6 (packed6 a b true i) := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def packedScore6 (p : Fin 6 → Fin 64) : ℕ :=
  ∑ t : Fin 64, univ.sup fun i : Fin 6 => if t.val &&& (p i).val = t.val then weight6 (p i) else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem packedScore6_spec (r : Fin 6 → Finset (Fin 6)) (p : Fin 6 → Fin 64)
    (rp : ∀ i, r i = maskSet6 (p i)) : traceScore r (fun _ => 2) = packedScore6 p := by
  let E := Equiv.ofBijective maskSet6 ⟨fun _ _ => maskSet6_inj _ _,maskSet6_onto⟩
  unfold traceScore packedScore6
  rw [← E.sum_comp]
  refine sum_congr rfl fun t _ => Finset.sup_congr rfl fun i _ => ?_
  change (if maskSet6 t ⊆ r i then 2^(5+2-(r i).card) else 0) = _
  simp only [rp i, maskSet6_subset, weight6_spec]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def packedSixCheck (a : Fin 16) : Prop := ∀ b : Fin 32,
    768 ≤ packedScore6 (packed6 a b false) + packedScore6 (packed6 a b true)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksPacked_0 : packedSixCheck 0 := by unfold packedSixCheck; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksPacked_1 : packedSixCheck 1 := by unfold packedSixCheck; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksPacked_2 : packedSixCheck 2 := by unfold packedSixCheck; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksPacked_3 : packedSixCheck 3 := by unfold packedSixCheck; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksPacked_4 : packedSixCheck 4 := by unfold packedSixCheck; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksPacked_5 : packedSixCheck 5 := by unfold packedSixCheck; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksPacked_6 : packedSixCheck 6 := by unfold packedSixCheck; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksPacked_7 : packedSixCheck 7 := by unfold packedSixCheck; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksPacked_8 : packedSixCheck 8 := by unfold packedSixCheck; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksPacked_9 : packedSixCheck 9 := by unfold packedSixCheck; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksPacked_10 : packedSixCheck 10 := by unfold packedSixCheck; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksPacked_11 : packedSixCheck 11 := by unfold packedSixCheck; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksPacked_12 : packedSixCheck 12 := by unfold packedSixCheck; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksPacked_13 : packedSixCheck 13 := by unfold packedSixCheck; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksPacked_14 : packedSixCheck 14 := by unfold packedSixCheck; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem ksPacked_15 : packedSixCheck 15 := by unfold packedSixCheck; decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem packedSixChecks (a : Fin 16) : packedSixCheck a := by
  fin_cases a
  · exact ksPacked_0
  · exact ksPacked_1
  · exact ksPacked_2
  · exact ksPacked_3
  · exact ksPacked_4
  · exact ksPacked_5
  · exact ksPacked_6
  · exact ksPacked_7
  · exact ksPacked_8
  · exact ksPacked_9
  · exact ksPacked_10
  · exact ksPacked_11
  · exact ksPacked_12
  · exact ksPacked_13
  · exact ksPacked_14
  · exact ksPacked_15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem traceSix (r : Fin 6 → Finset (Fin 6)) (hdiag : ∀ i, i ∉ r i)
    (hsym : ∀ i j, j ∈ r i ↔ i ∈ r j)
    (hp : ∀ i j : Fin 6, i.val < 4 → j.val < 4 →
      (j ∈ r i ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val)) :
    768 ≤ traceScore r (fun _ => 2) + traceScore (otherRows r) (fun _ => 2) := by
  obtain ⟨a,b,rfl⟩ := extensionSix r hdiag hsym hp
  rw [packedScore6_spec _ _ (packed6_red a b),packedScore6_spec _ _ (packed6_blue a b)]
  exact packedSixChecks a b

end KeoughShane

end

section

open OMA.S_arxiv_1808_05576
namespace KeoughShane
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def smallIdx : ℕ → ℕ → Fin 10
  | 0, 1 => 0
  | 0, 2 => 1
  | 0, 3 => 2
  | 0, 4 => 3
  | 1, 2 => 4
  | 1, 3 => 5
  | 1, 4 => 6
  | 2, 3 => 7
  | 2, 4 => 8
  | 3, 4 => 9
  | _, _ => 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def smallEdgePair : Fin 10 → ℕ × ℕ :=
  ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma smallPairIdx {i j : ℕ} (hj : j < 5) (hij : i < j) :
    smallEdgePair (smallIdx i j) = (i,j) := by
  have hi : i < 5 := by omega
  interval_cases i <;> interval_cases j <;> first | omega | decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def smallGraph (n : ℕ) (bits : Fin 10 → Bool) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ bits (smallIdx (min i.val j.val) (max i.val j.val))
  symm := ⟨fun i j h => by
    exact ⟨h.1.symm, by simpa only [min_comm j.val i.val,max_comm j.val i.val] using h.2⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

private instance (n : ℕ) (bits : Fin 10 → Bool) : DecidableRel (smallGraph n bits).Adj :=
  fun i j => inferInstanceAs (Decidable (i ≠ j ∧ bits (smallIdx (min i.val j.val) (max i.val j.val))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def getSmallBit {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pair : ℕ × ℕ) : Bool :=
  if h : pair.1 < n ∧ pair.2 < n then decide (G.Adj ⟨_,h.1⟩ ⟨_,h.2⟩) else false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma smallGraph_encodes {n : ℕ} (hn : n ≤ 5) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    smallGraph n (fun k => getSmallBit G (smallEdgePair k)) = G := by
  ext i j
  change (i ≠ j ∧ getSmallBit G (smallEdgePair (smallIdx _ _)) = true) ↔ _
  rcases lt_trichotomy i j with h | h | h
  · have hii : i.val < j.val := h
    rw [min_eq_left hii.le, max_eq_right hii.le, smallPairIdx (lt_of_lt_of_le j.isLt hn) hii]
    simp [getSmallBit,i.isLt,j.isLt,ne_of_lt h]
  · subst j
    simp
  · have hji : j.val < i.val := h
    rw [min_eq_right hji.le, max_eq_left hji.le, smallPairIdx (lt_of_lt_of_le i.isLt hn) hji]
    simp [getSmallBit,i.isLt,j.isLt,ne_of_gt h,G.adj_comm j i]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private def checkSmall (n : ℕ) (bits : Fin 10 → Bool) : Prop :=
    numDom (smallGraph n bits) + numDom (smallGraph n bits)ᶜ ≤
      2*(2^(n/2)-1)*(2^(n-n/2)-1)+2

private instance (n : ℕ) (bits : Fin 10 → Bool) : Decidable (checkSmall n bits) :=
  inferInstanceAs (Decidable (_ ≤ _ : Prop))


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma numDom_equiv {n : ℕ} (H G : SimpleGraph (Fin n))
    [DecidableRel H.Adj] [DecidableRel G.Adj] (e : Fin n ≃ Fin n)
    (he : ∀ i j, H.Adj i j ↔ G.Adj (e i) (e j)) : numDom H=numDom G := by
  classical
  apply Finset.card_bijective e.finsetCongr e.finsetCongr.bijective
  intro S
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro h x
    obtain ⟨i,rfl⟩ := e.surjective x
    rcases h i with hi | ⟨j,hj,hadj⟩
    · exact Or.inl (by simpa)
    · exact Or.inr ⟨e j,by simpa using hj,(he i j).mp hadj⟩
  · intro h i
    rcases h (e i) with hi | ⟨y,hy,hadj⟩
    · exact Or.inl (by simpa using hi)
    · obtain ⟨j,rfl⟩ := e.surjective y
      exact Or.inr ⟨j,by simpa using hy,(he i j).mpr hadj⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma smallPattern : ∀ (a b c d : Bool) (n : Fin 6),
    checkSmall n ![true,false,false,a,true,false,b,true,c,d] := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma smallLabelled {n : ℕ} (lo : 4 ≤ n) (hn : n ≤ 5)
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hp : ∀ i j : Fin n, i.val<4 → j.val<4 →
      (H.Adj i j ↔ i.val+1=j.val ∨ j.val+1=i.val)) :
    numDom H + numDom Hᶜ ≤ 2*(2^(n/2)-1)*(2^(n-n/2)-1)+2 := by
  let bits := fun k => getSmallBit H (smallEdgePair k)
  have bitP (i j : ℕ) (h1 : i < 4) (h2 : j < 4) :
      getSmallBit H (i,j) = decide (i+1=j ∨ j+1=i) := by
    have hi : i < n := by omega
    have hj : j < n := by omega
    simp only [getSmallBit,hi,hj, and_self, dite_true]
    simp only [hp ⟨i,hi⟩ ⟨j,hj⟩ h1 h2]
  have he : ![true,false,false,bits 3,true,false,bits 6,true,bits 8,bits 9] = bits := by
    funext k
    fin_cases k <;> first | rfl | (change _ = getSmallBit H (_,_); rw [bitP _ _ (by decide) (by decide)]; rfl)
  have hh := smallPattern (bits 3) (bits 6) (bits 8) (bits 9) (⟨n,by omega⟩ : Fin 6)
  rw [he] at hh
  change numDom (smallGraph n bits) + numDom (smallGraph n bits)ᶜ ≤ _ at hh
  convert hh using 1 <;> simp [bits,smallGraph_encodes hn H]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma smallWithPerm {n : ℕ} (lo : 4 ≤ n) (hn : n ≤ 5)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (f : Fin n ↪ Fin n)
    (hp : ∀ i j : Fin n, i.val<4 → j.val<4 →
      (G.Adj (f i) (f j) ↔ i.val+1=j.val ∨ j.val+1=i.val)) :
    numDom G + numDom Gᶜ ≤ 2*(2^(n/2)-1)*(2^(n-n/2)-1)+2 := by
  classical
  let e := Equiv.ofBijective f (Finite.injective_iff_bijective.mp f.injective)
  let H := G.comap f
  have he : ∀ i j, H.Adj i j ↔ G.Adj (e i) (e j) := fun _ _ => Iff.rfl
  have hb : ∀ i j, Hᶜ.Adj i j ↔ Gᶜ.Adj (e i) (e j) := by
    intro i j
    simp only [SimpleGraph.compl_adj, e.injective.ne_iff, he]
  rw [←numDom_equiv H G e he, ←numDom_equiv Hᶜ Gᶜ e hb]
  exact smallLabelled lo hn H hp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem small_bound {n : ℕ} (hn : n ≤ 5) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    numDom G + numDom Gᶜ ≤ 2*(2^(n/2)-1)*(2^(n-n/2)-1)+2 := by
  classical
  by_cases h2 : 2 ≤ n
  · by_cases hg : G.Connected
    · by_cases hb : Gᶜ.Connected
      · obtain ⟨f,hf⟩ := OMA.ksSeinsche h2 G hg hb
        have hlo := Fintype.card_le_of_injective f f.injective
        simp only [Fintype.card_fin] at hlo
        interval_cases n
        · exact smallWithPerm (by decide) (by decide) G f (fun i j _ _ => hf i j)
        · obtain ⟨v,hv⟩ : ∃ v : Fin 5, v ∉ Set.range f := by
            by_contra! hh
            have hs : Function.Surjective f := hh
            have hc := Fintype.card_le_of_surjective f hs
            simp at hc
          apply smallWithPerm (by decide) (by decide) G (Fin.Embedding.snoc f hv)
          intro i j hi hj
          let a : Fin 4 := ⟨i.val,hi⟩
          let b : Fin 4 := ⟨j.val,hj⟩
          have ha : i=a.castSucc := Fin.ext rfl
          have hb' : j=b.castSucc := Fin.ext rfl
          rw [ha,hb',Fin.Embedding.snoc_castSucc,Fin.Embedding.snoc_castSucc]
          exact hf a b
      · simpa only [compl_compl,Nat.add_comm (numDom Gᶜ) (numDom G)] using
          not_connected_bound (by omega) Gᶜ hb
    · exact not_connected_bound (by omega) G hg
  · have hn' : n ≤ 1 := by omega
    haveI : Subsingleton (Fin n) := Fin.subsingleton_iff_le_one.mpr hn'
    let b : Fin 10 → Bool := ![true,false,false,false,true,false,false,true,false,false]
    have he : smallGraph n b = G := Subsingleton.elim _ _
    have hw := smallPattern false false false false (⟨n,by omega⟩ : Fin 6)
    change numDom (smallGraph n b) + numDom (smallGraph n b)ᶜ ≤ _ at hw
    convert hw using 1 <;> simp [he]
end KeoughShane

end

section

namespace KeoughShane

open Finset OMA.S_arxiv_1808_05576

private def startsPath {n m : ℕ} (G : SimpleGraph (Fin n)) (f : Fin m ↪ Fin n) : Prop :=
  ∀ i j : Fin m, i.val < 4 → j.val < 4 →
    (G.Adj (f i) (f j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val)

private theorem extendPath {n m : ℕ} {G : SimpleGraph (Fin n)} {f : Fin m ↪ Fin n}
    (hm : 4 ≤ m) (hp : startsPath G f) {x : Fin n} (hx : x ∉ Set.range f) :
    startsPath G (Fin.Embedding.snoc f hx) := by
  intro i j hi hj
  let a : Fin m := ⟨i.val,by omega⟩
  let b : Fin m := ⟨j.val,by omega⟩
  have ha : i = a.castSucc := Fin.ext rfl
  have hb : j = b.castSucc := Fin.ext rfl
  rw [ha,hb,Fin.Embedding.snoc_castSucc,Fin.Embedding.snoc_castSucc]
  exact hp a b hi hj

private theorem existsOutside {m n : ℕ} (f : Fin m ↪ Fin n) (h : m < n) :
    ∃ x : Fin n, x ∉ Set.range f := by
  by_contra! hall
  have hs : Function.Surjective f := hall
  have := Fintype.card_le_of_surjective f hs
  simp at this
  omega

private theorem chooseFive {n : ℕ} {G : SimpleGraph (Fin n)}
    {f : Fin 4 ↪ Fin n} (hp : startsPath G f) (hn : 5 ≤ n) (P : Fin n → Prop) :
    ∃ g : Fin 5 ↪ Fin n, startsPath G g ∧ ((∃ x, P x) → ∃ i, P (g i)) := by
  classical
  obtain ⟨outside,hout⟩ := existsOutside f (by omega)
  by_cases already : ∃ i, P (f i)
  · obtain ⟨i,hi⟩ := already
    exact ⟨Fin.Embedding.snoc f hout,extendPath (by decide) hp hout,fun _ =>
      ⟨i.castSucc, by simpa only [Fin.Embedding.snoc_castSucc] using hi⟩⟩
  by_cases any : ∃ x, P x
  · obtain ⟨x,hx⟩ := any
    have outside : x ∉ Set.range f := by
      rintro ⟨i,rfl⟩
      exact already ⟨i,hx⟩
    exact ⟨Fin.Embedding.snoc f outside,extendPath (by decide) hp outside,fun _ =>
      ⟨Fin.last 4, by simpa only [Fin.Embedding.snoc_last] using hx⟩⟩
  exact ⟨Fin.Embedding.snoc f hout,extendPath (by decide) hp hout,fun h => (any h).elim⟩

private theorem finishLoss {n k e x y p q : ℕ}
    (hn : n = k+k+e) (he : e ≤ 1)
    (hx : x+p = 2^n) (hy : y+q = 2^n) (h : (4+2*e)*2^k ≤ p+q) :
    x+y ≤ 2*(2^(n/2)-1)*(2^(n-n/2)-1)+2 := by
  have hk : 0 < 2^k := by positivity
  have hA : 2^k-1+1 = 2^k := by omega
  have hB : 2^k*2-1+1 = 2^k*2 := by omega
  have hdiv : n/2 = k := by omega
  rw [hdiv]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he with rfl|rfl
  · rw [show n-k=k by omega]
    rw [show n=k+k by omega, pow_add] at hx hy
    norm_num at h
    nlinarith only [hx,hy,h,hA,congrArg (fun t : ℕ => t*t) hA]
  · rw [show n-k=k+1 by omega,pow_succ]
    rw [hn,pow_succ,pow_add] at hx hy
    norm_num at h
    nlinarith only [hx,hy,h,hA,hB,congrArg₂ Nat.mul hA hB]

private theorem degreeAndComplement {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (i : Fin n) : G.degree i + Gᶜ.degree i + 1 = n := by
  classical
  have hi := G.degree_lt_card_verts i
  simp only [Fintype.card_fin] at hi
  rw [SimpleGraph.degree_compl,Fintype.card_fin]
  omega

private theorem oneLarge {n k e} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (he : e ≤ 1)
    (i : Fin n) (hi : k + 2 + e ≤ G.degree i) : (4+2*e)*2^k ≤ (failures G).card := by
  apply le_trans _ (singleton_failure G i)
  apply le_trans _ (Nat.pow_le_pow_right (by decide : 0 < 2) hi)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp he with rfl|rfl <;>
    simp [pow_add] <;> omega

private theorem rowProps {n m} {G : SimpleGraph (Fin n)} {f : Fin m ↪ Fin n}
    (hp : startsPath G f) :
    (∀ i, i ∉ graphRows G f i) ∧
    (∀ i j, j ∈ graphRows G f i ↔ i ∈ graphRows G f j) ∧
    (∀ i j : Fin m, i.val < 4 → j.val < 4 →
       (j ∈ graphRows G f i ↔ i.val+1 = j.val ∨ j.val+1 = i.val)) := by
  classical
  simp only [graphRows,restrictSet,mem_filter,mem_univ,true_and,SimpleGraph.mem_neighborFinset]
  exact ⟨by simp,fun _ _ => G.adj_comm _ _,hp⟩

private theorem fromLocal {n m k e} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : Fin m ↪ Fin n) (a b : Fin m → ℕ) (hm : m ≤ 6)
    (ha : ∀ i, 7+G.degree (f i) = k+5+a i)
    (hb : ∀ i, 7+Gᶜ.degree (f i) = k+5+b i)
    (hs : 128*(4+2*e) ≤ traceScore (graphRows G f) a + traceScore (otherRows (graphRows G f)) b) :
    (4+2*e)*2^k ≤ (failures G).card+(failures Gᶜ).card := by
  have hr := graph_trace_score G f a hm ha
  have hc := graph_trace_score Gᶜ f b hm hb
  rw [graphRows_compl] at hc
  have hw := Nat.mul_le_mul_left (2^k) hs
  rw [Nat.mul_add] at hw
  nlinarith only [hr,hc,hw]

def FiveBound : Prop :=
  ∀ (r : Fin 5 → Finset (Fin 5)) (a : Fin 5 → ℕ) (e : ℕ), e ≤ 1 →
  (∀ i, a i ≤ 3+e) → (e=0 ∨ ∃ i, a i ≠ 2) →
  (∀ i, i ∉ r i) → (∀ i j, j ∈ r i ↔ i ∈ r j) →
  (∀ i j : Fin 5, i.val < 4 → j.val < 4 → (j ∈ r i ↔ i.val+1=j.val ∨ j.val+1=i.val)) →
  128*(4+2*e) ≤ traceScore r a + traceScore (otherRows r) (fun i => 3+e-a i)

def SixBound : Prop :=
  ∀ (r : Fin 6 → Finset (Fin 6)), (∀ i, i ∉ r i) → (∀ i j, j ∈ r i ↔ i ∈ r j) →
  (∀ i j : Fin 6, i.val < 4 → j.val < 4 → (j ∈ r i ↔ i.val+1=j.val ∨ j.val+1=i.val)) →
  768 ≤ traceScore r (fun _ => 2) + traceScore (otherRows r) (fun _ => 2)

private theorem connectedLoss (five : FiveBound) (six : SixBound)
    {n k e : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hn : 6 ≤ n) (hke : n = k+k+e) (he : e ≤ 1)
    (hr : G.Connected) (hb : Gᶜ.Connected) :
    (4+2*e)*2^k ≤ (failures G).card+(failures Gᶜ).card := by
  classical
  by_cases bigR : ∃ i, k+2+e ≤ G.degree i
  · obtain ⟨i,hi⟩ := bigR
    have := oneLarge G he i hi
    omega
  by_cases bigB : ∃ i, k+2+e ≤ Gᶜ.degree i
  · obtain ⟨i,hi⟩ := bigB
    have := oneLarge Gᶜ he i hi
    omega
  push Not at bigR bigB
  obtain ⟨p,hp⟩ := OMA.ksSeinsche (by omega) G hr hb
  have hpp : startsPath G p := fun i j _ _ => hp i j
  obtain ⟨f,hf,hw⟩ := chooseFive hpp (by omega) (fun x => G.degree x ≠ k)
  by_cases hcase : e=0 ∨ ∃ x, G.degree x ≠ k
  · let a (i : Fin 5) := G.degree (f i)+2-k
    have all (i : Fin 5) := degreeAndComplement G (f i)
    have bound (i : Fin 5) : a i ≤ 3+e := by
      dsimp [a]
      have := bigR (f i)
      omega
    have notMiddle : e=0 ∨ ∃ i, a i ≠ 2 := by
      rcases hcase with he0|h
      · exact Or.inl he0
      obtain ⟨i,hi⟩ := hw h
      refine Or.inr ⟨i,?_⟩
      dsimp [a]
      have := all i
      have := bigB (f i)
      omega
    obtain ⟨hd,hs,hp'⟩ := rowProps hf
    apply fromLocal G f a (fun i => 3+e-a i) (by decide) _ _
      (five _ a e he bound notMiddle hd hs hp')
    · intro i
      dsimp [a]
      have := all i
      have := bigB (f i)
      omega
    · intro i
      dsimp [a]
      have := all i
      have := bigB (f i)
      have := bigR (f i)
      omega
  · push Not at hcase
    have heq : e=1 := by omega
    obtain ⟨x,hx⟩ := existsOutside f (by omega)
    let g : Fin 6 ↪ Fin n := Fin.Embedding.snoc f hx
    have hg : startsPath G g := extendPath (by decide) hf hx
    obtain ⟨hd,hs,hp'⟩ := rowProps hg
    have hscore := six _ hd hs hp'
    apply fromLocal G g (fun _ => 2) (fun _ => 2) (by decide) _ _ (by simpa [heq] using hscore)
    · intro i
      have := hcase.2 (g i)
      omega
    · intro i
      have := hcase.2 (g i)
      have := degreeAndComplement G (g i)
      omega

theorem assembly (five : FiveBound) (six : SixBound)
    (small : ∀ {n}, n ≤ 5 → ∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj],
      numDom G+numDom Gᶜ ≤ 2*(2^(n/2)-1)*(2^(n-n/2)-1)+2)
    : type_of% @OMA.S_arxiv_1808_05576.main := by
  intro n G _
  classical
  by_cases hn : n ≤ 5
  · exact small hn G
  by_cases hr : G.Connected
  · by_cases hb : Gᶜ.Connected
    · let k := n/2
      let e := n%2
      have he : e ≤ 1 := by dsimp [e]; omega
      have hke : n=k+k+e := by dsimp [k,e]; omega
      have h := connectedLoss five six G (by omega) hke he hr hb
      have h1 := count_complement G
      have h2 := count_complement Gᶜ
      simp only [compl_compl] at h2
      apply finishLoss hke he h1 h2
      omega
    · have h := not_connected_bound (by omega) Gᶜ hb
      simpa only [compl_compl,add_comm (numDom Gᶜ) (numDom G)] using h
  · exact not_connected_bound (by omega) G hr

end KeoughShane

end

/-- The conjectured extremal inequality in every finite order. -/
theorem OMA.solution : type_of% @OMA.S_arxiv_1808_05576.main :=
  KeoughShane.assembly KeoughShane.traceFive KeoughShane.traceSix
    (@KeoughShane.small_bound)
