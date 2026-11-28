import OMAReductions.R_Erdos827_erdos_827_variants_n_five_le_R2
import Mathlib

/-!
# Matchings and monochromatic four-point systems in circumradius fans

The marked vertex and the three rich radii come from the parent reduction.
For a fixed radius, the pairs opposite the vertex form a graph of maximum degree two.
Three pairwise intersecting edges must form a triangle. Its three circumcenters
lie on the same circle around the marked vertex. Reflection in the midpoint of each
shared chord shows that the three outer vertices also have this circumradius.

For such a four-point set every chord already has its two possible completions.
Each of its vertices spoils at most 33 of the 528 outside pairs, leaving at least
396 pairs that avoid its radius at every vertex. Otherwise the conflict graph
of each marked fan has maximum degree two and no triangle. An independent set
of at least two fifths of its vertices gives the disjoint pairs in the second case.
-/
open EuclideanGeometry Erdos827 Finset
open scoped Classical
namespace OMA.CircumradiusFanPacking

/-- The two centers of circles with equal radius through a common chord are
exchanged by the half-turn around the midpoint of the chord. -/
theorem centers_sum {a b u v : ℝ²} {r : ℝ} (ab : a ≠ b) (uv : u ≠ v)
    (ua : dist u a = r) (ub : dist u b = r) (va : dist v a = r) (vb : dist v b = r) :
    u + v = a + b := by
  have refl (x : ℝ²) (xa : dist x a = r) (xb : dist x b = r) :
      a + b - x = u ∨ a + b - x = v := by
    apply eq_of_dist_eq_of_dist_eq_of_finrank_eq_two (by simp) ab uv ua va _ ub vb
    · rw [dist_eq_norm, show a+b-x-b=a-x by abel, ←dist_eq_norm, dist_comm, xa]
    · rw [dist_eq_norm, show a+b-x-a=b-x by abel, ←dist_eq_norm, dist_comm, xb]
  rcases refl u ua ub with hu | hu
  · rcases refl v va vb with hv | hv
    · rw [← hv]; abel
    · exfalso
      apply uv
      have h : (2:ℝ) • u = (2:ℝ) • v := by
        rw [two_smul,two_smul]
        calc u+u = a+b := by nth_rw 1 [← hu]; abel
             _ = v+v := by nth_rw 1 [← hv]; abel
      simpa using (smul_right_injective (M := ℝ²) (by norm_num : (2:ℝ) ≠ 0)) h
  · rw [← hu]; abel

/-- For three different centers on the circle about a, the three second
intersections of the corresponding equal-radius circles themselves lie on
a circle of this radius. -/
theorem fourth_radius {a b c d u v w : ℝ²} {r : ℝ}
    (ab : a ≠ b) (ac : a ≠ c) (ad : a ≠ d)
    (uv : u ≠ v) (uw : u ≠ w) (vw : v ≠ w)
    (ua : dist u a = r) (va : dist v a = r) (wa : dist w a = r)
    (ub : dist u b = r) (vb : dist v b = r)
    (uc : dist u c = r) (wc : dist w c = r)
    (vd : dist v d = r) (wd : dist w d = r) :
    OnCircleOfRadius {b,c,d} r := by
  have hb := centers_sum ab uv ua ub va vb
  have hc := centers_sum ac uw ua uc wa wc
  have hd := centers_sum ad vw va vd wa wd
  have b' : b = u + v - a := by rw [hb]; abel
  have c' : c = u + w - a := by rw [hc]; abel
  have d' : d = v + w - a := by rw [hd]; abel
  refine ⟨u + v + w - a - a, ?_⟩
  intro x hx
  simp only [mem_insert,mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · rw [dist_comm,dist_eq_norm,b',show u+v+w-a-a-(u+v-a)=w-a by abel,←dist_eq_norm,wa]
  · rw [dist_comm,dist_eq_norm,c',show u+v+w-a-a-(u+w-a)=v-a by abel,←dist_eq_norm,va]
  · rw [dist_comm,dist_eq_norm,d',show u+v+w-a-a-(v+w-a)=u-a by abel,←dist_eq_norm,ua]
end OMA.CircumradiusFanPacking


/- Packing in a triangle-free graph of maximum degree two. -/
open Finset
open scoped Classical

namespace OMA.CircumradiusFanPacking
variable {α : Type*} [DecidableEq α]

theorem independent_packing (R : α → α → Prop) [DecidableRel R]
    (symm : ∀ ⦃x y⦄, R x y → R y x) (irr : ∀ x, ¬ R x x)
    (S : Finset α) (deg : ∀ x ∈ S, (S.filter (R x)).card ≤ 2)
    (tri : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, R x y → R x z → ¬R y z) :
    ∃ M ⊆ S, (∀ x ∈ M, ∀ y ∈ M, ¬ R x y) ∧ 2 * S.card ≤ 5 * M.card := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases empty : S = ∅
    · subst S; exact ⟨∅, Subset.rfl, by simp, by simp⟩
    obtain ⟨v,vs⟩ := nonempty_iff_ne_empty.mpr empty
    let N (x : α) := insert x (S.filter (R x))
    have nmem {x y} (hy : y ∈ S) (h : R x y) : y ∈ N x :=
      mem_insert_of_mem (mem_filter.mpr ⟨hy,h⟩)
    have nsub {x} (hx : x ∈ S) : N x ⊆ S := insert_subset hx (filter_subset ..)
    have ncard {x} (hx : x ∈ S) : (N x).card ≤ 3 :=
      (card_insert_le ..).trans (by have := deg x hx; omega)
    have step (P D : Finset α) (ps : P ⊆ S) (pd : P ⊆ D) (dp : D ⊆ S)
        (pn : P.Nonempty) (pi : ∀ x ∈ P, ∀ y ∈ P, ¬ R x y)
        (cl : ∀ x ∈ P, N x ⊆ D) (sz : 2 * D.card ≤ 5 * P.card) :
        ∃ M ⊆ S, (∀ x ∈ M, ∀ y ∈ M, ¬ R x y) ∧ 2 * S.card ≤ 5 * M.card := by
      let T := S \ D
      have ts : T ⊆ S := sdiff_subset
      have lt : T ⊂ S := by
        refine ssubset_iff_of_subset ts |>.mpr ?_
        obtain ⟨x,hx⟩ := pn
        exact ⟨x,ps hx, fun h => (mem_sdiff.mp h).2 (pd hx)⟩
      have dg (x) (hx : x ∈ T) : (T.filter (R x)).card ≤ 2 :=
        (card_le_card (filter_subset_filter _ ts)).trans (deg x (ts hx))
      obtain ⟨M,ms,mi,mb⟩ := ih T lt dg (fun x hx y hy z hz => tri x (ts hx) y (ts hy) z (ts hz))
      have pm : Disjoint P M := disjoint_left.mpr (fun _ hx hy => (mem_sdiff.mp (ms hy)).2 (pd hx))
      have cross {x y} (hx : x ∈ P) (hy : y ∈ M) : ¬ R x y := fun hr =>
        (mem_sdiff.mp (ms hy)).2 (cl x hx (nmem (ts (ms hy)) hr))
      refine ⟨P ∪ M, union_subset ps (ms.trans ts), ?_, ?_⟩
      · intro x hx y hy
        rcases mem_union.mp hx with hx|hx <;> rcases mem_union.mp hy with hy|hy
        · exact pi _ hx _ hy
        · exact cross hx hy
        · exact fun h => cross hy hx (symm h)
        · exact mi _ hx _ hy
      · have diff : T.card = S.card - D.card := card_sdiff_of_subset dp
        have le := card_le_card dp
        rw [card_union_of_disjoint pm]
        omega
    by_cases low : ∃ x ∈ S, (S.filter (R x)).card ≤ 1
    · obtain ⟨x,hx,l⟩ := low
      apply step {x} (N x) (singleton_subset_iff.mpr hx)
        (singleton_subset_iff.mpr (mem_insert_self ..)) (nsub hx) (singleton_nonempty _)
      · simpa using irr x
      · simp
      · have n := card_insert_le x (S.filter (R x))
        simp only [card_singleton]; change 2 * (insert x (S.filter (R x))).card ≤ _
        omega
    · have dv : (S.filter (R v)).card = 2 := by
        have := deg v vs
        have : ¬ (S.filter (R v)).card ≤ 1 := fun h => low ⟨v,vs,h⟩
        omega
      obtain ⟨x,y,xy,eq⟩ := card_eq_two.mp dv
      have xn : x ∈ S.filter (R v) := eq ▸ (by simp)
      have yn : y ∈ S.filter (R v) := eq ▸ (by simp)
      obtain ⟨xs,vx⟩ := mem_filter.mp xn
      obtain ⟨ys,vy⟩ := mem_filter.mp yn
      have nxy := tri v vs x xs y ys vx vy
      have ins : v ∈ N x ∩ N y := mem_inter.mpr ⟨nmem vs (symm vx),nmem vs (symm vy)⟩
      apply step {x,y} (N x ∪ N y) (insert_subset xs (singleton_subset_iff.mpr ys))
        (insert_subset (mem_union_left _ (mem_insert_self ..)) (singleton_subset_iff.mpr (mem_union_right _ (mem_insert_self ..)))) (union_subset (nsub xs) (nsub ys)) (insert_nonempty ..)
      · simp [irr,nxy,show ¬ R y x from fun h => nxy (symm h)]
      · simp [subset_union_left,subset_union_right]
      · have hn := card_union_add_card_inter (N x) (N y)
        have nx := ncard xs; have ny := ncard ys
        have i := card_pos.mpr ⟨v,ins⟩
        rw [card_pair xy]; omega
end OMA.CircumradiusFanPacking


/- Edge incidence in a fan and conflicts between its edges. -/
open Finset EuclideanGeometry Erdos827
open scoped Classical
namespace OMA.CircumradiusFanPacking
variable {α : Type*} [DecidableEq α]


lemma pair_through {B : Finset α} {x : α} (bx : x ∈ B) (s : B.card = 2) :
    ∃ y, x ≠ y ∧ B = {x,y} := by
  have one : (B.erase x).card = 1 := by rw [card_erase_of_mem bx,s]
  obtain ⟨y,he⟩ := card_eq_one.mp one
  have xy : x ≠ y := by
    intro h
    have : x ∈ B.erase x := by rw [he]; simpa using h
    exact notMem_erase x B this
  exact ⟨y,xy, by rw [←he,insert_erase bx]⟩

lemma conflict_degree (L : Finset (Finset α)) (pairs : ∀ B ∈ L, B.card = 2)
    (deg : ∀ x, (L.filter (x ∈ ·)).card ≤ 2) {B} (hb : B ∈ L) :
    (L.filter (fun E => B ≠ E ∧ ¬ Disjoint B E)).card ≤ 2 := by
  classical
  obtain ⟨x,y,xy,eq⟩ := card_eq_two.mp (pairs B hb)
  let N (z : α) := (L.filter (z ∈ ·)).erase B
  have small {z} (hz : z ∈ B) : (N z).card ≤ 1 := by
    dsimp [N]
    rw [card_erase_of_mem (mem_filter.mpr ⟨hb,hz⟩)]
    have := deg z
    omega
  have sub : L.filter (fun E => B ≠ E ∧ ¬ Disjoint B E) ⊆ N x ∪ N y := by
    intro E he
    obtain ⟨hE,ne,meet⟩ := mem_filter.mp he
    obtain ⟨z,zB,zE⟩ := not_disjoint_iff.mp meet
    rcases (show z=x ∨ z=y by simpa [eq] using zB) with rfl|rfl
    · exact mem_union_left _ (mem_erase.mpr ⟨ne.symm, mem_filter.mpr ⟨hE,zE⟩⟩)
    · exact mem_union_right _ (mem_erase.mpr ⟨ne.symm, mem_filter.mpr ⟨hE,zE⟩⟩)
  have h := (card_le_card sub).trans (card_union_le ..)
  have sx := small (show x ∈ B by simp [eq])
  have sy := small (show y ∈ B by simp [eq])
  omega

lemma triangle_edges {L : Finset (Finset α)} (pairs : ∀ B ∈ L, B.card = 2)
    (deg : ∀ x, (L.filter (x ∈ ·)).card ≤ 2)
    {B C E} (b : B ∈ L) (c : C ∈ L) (e : E ∈ L)
    (bc : (B ≠ C ∧ ¬ Disjoint B C)) (be : (B ≠ E ∧ ¬ Disjoint B E)) (ce : (C ≠ E ∧ ¬ Disjoint C E)) :
    ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ B={x,y} ∧ C={x,z} ∧ E={y,z} := by
  classical
  obtain ⟨x,xb,xc⟩ := not_disjoint_iff.mp bc.2
  obtain ⟨y,xy,eqb⟩ := pair_through xb (pairs _ b)
  obtain ⟨z,xz,eqc⟩ := pair_through xc (pairs _ c)
  have yz : y ≠ z := fun h => bc.1 (by rw [eqb,eqc,h])
  have xe : x ∉ E := by
    intro h
    have sub : ({B,C,E} : Finset _) ⊆ L.filter (x ∈ ·) :=
      insert_subset (mem_filter.mpr ⟨b,xb⟩) (insert_subset (mem_filter.mpr ⟨c,xc⟩)
        (singleton_subset_iff.mpr (mem_filter.mpr ⟨e,h⟩)))
    have le := (card_le_card sub).trans (deg x)
    simp [bc.1, be.1, ce.1] at le
  have mem {t} (h : ¬ Disjoint ({x,t} : Finset _) E) : t ∈ E := by
    obtain ⟨p,hp,pe⟩ := not_disjoint_iff.mp h
    rcases (show p=x ∨ p=t by simpa using hp) with rfl|rfl
    · exact (xe pe).elim
    · exact pe
  exact ⟨x,y,z,xy,xz,yz,eqb,eqc,
    (eq_of_subset_of_card_le (insert_subset (mem (eqb ▸ be.2))
      (singleton_subset_iff.mpr (mem (eqc ▸ ce.2)))) (by rw [pairs _ e,card_pair yz])).symm⟩


lemma fan_degree {X : Finset ℝ²} (gp : InGeneralPosition (X : Set ℝ²)) {a : ℝ²}
    (ha : a ∈ X) (r : ℝ) (b : ℝ²) : (((((X.erase a).powersetCard 2).filter (fun B => OnCircleOfRadius (insert a B) r))).filter (b ∈ ·)).card ≤ 2 := by
  classical
  obtain ⟨c,track,edges⟩ := OMA.CircumradiusOverlap.radius_coloring X gp
  by_cases hb : b ∈ X.erase a
  · have ba : b ≠ a := (mem_erase.mp hb).1
    let P : Finset ℝ² := {a,b}
    have sz : P.card = 2 := card_pair ba.symm
    have hP : P ⊆ X := insert_subset ha (singleton_subset_iff.mpr (mem_erase.mp hb).2)
    let T := (X\P).filter fun z => c (insert z P) = r
    have sub : ((((X.erase a).powersetCard 2).filter (fun B => OnCircleOfRadius (insert a B) r))).filter (b ∈ ·) ⊆ T.image (fun z => ({b,z} : Finset ℝ²)) := by
      intro B h
      obtain ⟨hB,bB⟩ := mem_filter.mp h
      obtain ⟨pair,circ⟩ := mem_filter.mp hB
      obtain ⟨inV,szB⟩ := mem_powersetCard.mp pair
      obtain ⟨z,bz,eq⟩ := pair_through bB szB
      have zB : z ∈ B := by simp [eq]
      obtain ⟨za,zX⟩ := mem_erase.mp (inV zB)
      have zP : z ∉ P := by simp [P,za,bz.symm]
      have ep : insert z P = insert a B := by ext t; simp [P,eq]; tauto
      have hcol := (track (insert z P) (insert_subset zX hP)
        (by rw [card_insert_of_notMem zP,sz]) r).mpr (ep ▸ circ)
      exact mem_image.mpr ⟨z,mem_filter.mpr ⟨mem_sdiff.mpr ⟨zX,zP⟩,hcol⟩,eq.symm⟩
    exact (card_le_card sub).trans (card_image_le.trans (edges P hP sz r))
  · have eq : ((((X.erase a).powersetCard 2).filter (fun B => OnCircleOfRadius (insert a B) r))).filter (b ∈ ·) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro B h
      obtain ⟨hB,bB⟩ := mem_filter.mp h
      exact hb ((mem_powersetCard.mp (mem_filter.mp hB).1).1 bB)
    simp [eq]
end OMA.CircumradiusFanPacking

namespace OMA.CircumradiusFanPacking
open Finset EuclideanGeometry Erdos827
open scoped Classical

lemma no_center_four {X : Finset ℝ²} (gp : InGeneralPosition (X : Set ℝ²))
    {a b c d u : ℝ²} {r : ℝ}
    (sa : a ∈ X) (sb : b ∈ X) (sc : c ∈ X) (sd : d ∈ X)
    (ab : a ≠ b) (ac : a ≠ c) (ad : a ≠ d) (bc : b ≠ c) (bd : b ≠ d) (cd : c ≠ d)
    (ha : dist a u = r) (hb : dist b u = r) (hc : dist c u = r) (hd : dist d u = r) : False := by
  let Q : Finset ℝ² := {a,b,c,d}
  apply gp.2 (Q : Set ℝ²)
  · intro z hz
    rcases (show z=a ∨ z=b ∨ z=c ∨ z=d by simpa [Q] using hz) with rfl|rfl|rfl|rfl <;> assumption
  · simp [Q,ab,ac,ad,bc,bd,cd]
  · refine ⟨u,r,?_⟩
    intro z hz
    rcases (show z=a ∨ z=b ∨ z=c ∨ z=d by simpa [Q] using hz) with rfl|rfl|rfl|rfl <;> assumption

lemma complete_triangle {X : Finset ℝ²} (gp : InGeneralPosition (X : Set ℝ²))
    {a : ℝ²} (ha : a ∈ X) {r : ℝ} {B C E : Finset ℝ²}
    (b : B ∈ (((X.erase a).powersetCard 2).filter (fun B => OnCircleOfRadius (insert a B) r))) (c : C ∈ (((X.erase a).powersetCard 2).filter (fun B => OnCircleOfRadius (insert a B) r))) (e : E ∈ (((X.erase a).powersetCard 2).filter (fun B => OnCircleOfRadius (insert a B) r)))
    (bc : (B ≠ C ∧ ¬ Disjoint B C)) (be : (B ≠ E ∧ ¬ Disjoint B E)) (ce : (C ≠ E ∧ ¬ Disjoint C E)) :
    ∃ Q ⊆ X, Q.card = 4 ∧ a ∈ Q ∧ ∀ T ∈ Q.powersetCard 3, OnCircleOfRadius T r := by
  have pairs (Z) (hz : Z ∈ (((X.erase a).powersetCard 2).filter (fun B => OnCircleOfRadius (insert a B) r))) : Z.card=2 := (mem_powersetCard.mp (mem_filter.mp hz).1).2
  obtain ⟨x,y,z,xy,xz,yz,rfl,rfl,rfl⟩ := triangle_edges pairs (fan_degree gp ha r) b c e bc be ce
  have xV := (mem_powersetCard.mp (mem_filter.mp b).1).1 (by simp : x ∈ ({x,y}:Finset _))
  have yV := (mem_powersetCard.mp (mem_filter.mp b).1).1 (by simp : y ∈ ({x,y}:Finset _))
  have zV := (mem_powersetCard.mp (mem_filter.mp c).1).1 (by simp : z ∈ ({x,z}:Finset _))
  obtain ⟨xa,sx⟩ := mem_erase.mp xV
  obtain ⟨ya,sy⟩ := mem_erase.mp yV
  obtain ⟨za,sz⟩ := mem_erase.mp zV
  have h₁ := (mem_filter.mp b).2
  have h₂ := (mem_filter.mp c).2
  have h₃ := (mem_filter.mp e).2
  obtain ⟨u,hu⟩ := h₁
  obtain ⟨v,hv⟩ := h₂
  obtain ⟨w,hw⟩ := h₃
  have uv : u ≠ v := by
    rintro rfl
    exact no_center_four gp ha sx sy sz xa.symm ya.symm za.symm xy xz yz
      (hu a (by simp)) (hu x (by simp)) (hu y (by simp)) (hv z (by simp))
  have uw : u ≠ w := by
    rintro rfl
    exact no_center_four gp ha sx sy sz xa.symm ya.symm za.symm xy xz yz
      (hu a (by simp)) (hu x (by simp)) (hu y (by simp)) (hw z (by simp))
  have vw : v ≠ w := by
    rintro rfl
    exact no_center_four gp ha sx sy sz xa.symm ya.symm za.symm xy xz yz
      (hv a (by simp)) (hv x (by simp)) (hw y (by simp)) (hv z (by simp))
  have outer := fourth_radius xa.symm ya.symm za.symm uv uw vw
    ((dist_comm ..).trans (hu a (by simp))) ((dist_comm ..).trans (hv a (by simp)))
    ((dist_comm ..).trans (hw a (by simp))) ((dist_comm ..).trans (hu x (by simp)))
    ((dist_comm ..).trans (hv x (by simp))) ((dist_comm ..).trans (hu y (by simp)))
    ((dist_comm ..).trans (hw y (by simp))) ((dist_comm ..).trans (hv z (by simp)))
    ((dist_comm ..).trans (hw z (by simp)))
  refine ⟨{a,x,y,z}, insert_subset ha (insert_subset sx (insert_subset sy (singleton_subset_iff.mpr sz))),
    by simp [xa.symm,ya.symm,za.symm,xy,xz,yz], by simp, ?_⟩
  intro T ht
  have del := card_sdiff_of_subset (mem_powersetCard.mp ht).1
  have szQ : ({a,x,y,z} : Finset _).card=4 := by simp [xa.symm,ya.symm,za.symm,xy,xz,yz]
  rw [szQ,(mem_powersetCard.mp ht).2] at del
  obtain ⟨p,ep⟩ := card_eq_one.mp del
  have pp : p ∈ ({a,x,y,z}:Finset _) \ T := by rw [ep]; simp
  have formula : T = ({a,x,y,z}:Finset _) \ {p} := by
    rw [←ep,Finset.sdiff_sdiff_eq_self (mem_powersetCard.mp ht).1]
  rcases (show p=a ∨ p=x ∨ p=y ∨ p=z by simpa using (mem_sdiff.mp pp).1) with rfl|rfl|rfl|rfl
  · have eqT : T = {x,y,z} := by
      rw [formula]; ext t
      by_cases h : t = p
      · subst t; simp [xa.symm,ya.symm,za.symm]
      · simp [h]
    exact eqT ▸ outer
  · have eqT : T = {a,y,z} := by
      rw [formula]; ext t
      by_cases h : t = p
      · subst t; simp [xa,xy,xz]
      · simp [h]
    exact eqT ▸ (mem_filter.mp e).2
  · have eqT : T = {a,x,z} := by
      rw [formula]; ext t
      by_cases h : t = p
      · subst t; simp [ya,xy.symm,yz]
      · simp [h]
    exact eqT ▸ (mem_filter.mp c).2
  · have eqT : T = {a,x,y} := by
      rw [formula]; ext t
      by_cases h : t = p
      · subst t; simp [za,xz.symm,yz.symm]
      · simp [h]
    exact eqT ▸ (mem_filter.mp b).2
end OMA.CircumradiusFanPacking

namespace OMA.CircumradiusFanPacking
open Finset EuclideanGeometry Erdos827
open scoped Classical

lemma outside_pairs {X Q : Finset ℝ²} (gp : InGeneralPosition (X : Set ℝ²))
    (n : X.card = 37) (qs : Q ⊆ X) (q4 : Q.card=4) (r : ℝ) :
    396 ≤ (((X \ Q).powersetCard 2).filter
      (fun P => ∀ b ∈ Q, ¬ OnCircleOfRadius (insert b P) r)).card := by
  classical
  let W := X \ Q
  let S := W.powersetCard 2
  let bad (b : ℝ²) := S.filter (fun P => OnCircleOfRadius (insert b P) r)
  have wcard : W.card=33 := by rw [card_sdiff_of_subset qs,n,q4]
  have limited (b) (hb : b ∈ Q) : (bad b).card ≤ 33 := by
    have bx := qs hb
    have lin : bad b ⊆ (((X.erase b).powersetCard 2).filter (fun B => OnCircleOfRadius (insert b B) r)) := by
      intro P h
      obtain ⟨inS,rad⟩ := mem_filter.mp h
      obtain ⟨pw,p2⟩ := mem_powersetCard.mp inS
      refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨?_,p2⟩,rad⟩
      intro x hx
      obtain ⟨xx,xq⟩ := mem_sdiff.mp (pw hx)
      exact mem_erase.mpr ⟨fun eq => xq (eq ▸ hb),xx⟩
    have lo (P) (hp : P ∈ bad b) : 2 ≤ (W.filter (· ∈ P)).card := by
      obtain ⟨sub,p2⟩ := mem_powersetCard.mp (mem_filter.mp hp).1
      have eq : W.filter (· ∈ P) = P := by ext x; simp only [mem_filter]; exact ⟨And.right,fun h => ⟨sub h,h⟩⟩
      rw [eq,p2]
    have hi (x) (_ : x ∈ W) : ((bad b).filter (x ∈ ·)).card ≤ 2 :=
      (card_le_card (filter_subset_filter _ lin)).trans (fan_degree gp bx r x)
    have h := card_nsmul_le_card_nsmul (r := fun (P : Finset ℝ²) x => x ∈ P)
      (s := bad b) (t := W) lo hi
    change (bad b).card * 2 ≤ W.card * 2 at h
    omega
  have cover : (Q.biUnion bad).card ≤ 132 := by
    calc _ ≤ ∑ b ∈ Q, (bad b).card := card_biUnion_le
         _ ≤ ∑ _b ∈ Q, 33 := sum_le_sum limited
         _ = _ := by simp [q4]
  have eq : S.filter (fun P => ∀ b ∈ Q, ¬ OnCircleOfRadius (insert b P) r) = S \ Q.biUnion bad := by
    ext P; simp [bad]; tauto
  change 396 ≤ (S.filter _).card
  rw [eq]
  have bound := le_card_sdiff (Q.biUnion bad) S
  have sc : S.card=528 := by rw [card_powersetCard,wcard]; decide
  omega

lemma saturated_chords {X Q : Finset ℝ²} (gp : InGeneralPosition (X : Set ℝ²))
    (qs : Q ⊆ X) (q4 : Q.card = 4) {r : ℝ}
    (mono : ∀ T ∈ Q.powersetCard 3, OnCircleOfRadius T r)
    (B : Finset ℝ²) (hb : B ∈ Q.powersetCard 2) (z : ℝ²) (hz : z ∈ X \ Q) :
    ¬ OnCircleOfRadius (insert z B) r := by
  classical
  obtain ⟨c,track,edges⟩ := OMA.CircumradiusOverlap.radius_coloring X gp
  obtain ⟨bq,b2⟩ := mem_powersetCard.mp hb
  let U := (X \ B).filter (fun x => c (insert x B) = r)
  have bX := bq.trans qs
  have one (x) (hx : x ∈ X) (xb : x ∉ B) (h : OnCircleOfRadius (insert x B) r) : x ∈ U :=
    mem_filter.mpr ⟨mem_sdiff.mpr ⟨hx,xb⟩, (track _ (insert_subset hx bX)
      (by rw [card_insert_of_notMem xb,b2]) r).mpr h⟩
  have sub : Q \ B ⊆ U := by
    intro x hx
    obtain ⟨xq,xb⟩ := mem_sdiff.mp hx
    exact one _ (qs xq) xb (mono _ (mem_powersetCard.mpr ⟨insert_subset xq bq,
      by rw [card_insert_of_notMem xb,b2]⟩))
  have eq := eq_of_subset_of_card_le sub (show U.card ≤ (Q \ B).card by
    rw [card_sdiff_of_subset bq,q4,b2]; exact edges B bX b2 r)
  intro circ
  have zu := one z (mem_sdiff.mp hz).1 (fun h => (mem_sdiff.mp hz).2 (bq h)) circ
  exact (mem_sdiff.mp hz).2 (mem_sdiff.mp (by simpa only [eq] using zu : z ∈ Q \ B)).1
end OMA.CircumradiusFanPacking

namespace OMA.R_Erdos827_erdos_827_variants_n_five_le_R2_H1_R1
open Finset EuclideanGeometry Erdos827 OMA.CircumradiusFanPacking
open scoped Classical

/-- An equal-radius four-set through the marked vertex saturates all six
chords. At least 396 outside pairs also avoid the marked radius at every
vertex of the four-set. -/
def H1 : Prop := ∀ (X : Finset ℝ²), X.card = 37 → InGeneralPosition (X : Set ℝ²) →
  ∀ a ∈ X, let F (r : ℝ) := (((X.erase a).powersetCard 2).filter (fun B => OnCircleOfRadius (insert a B) r))
  ∀ (s : ℝ), 13 ≤ (F s).card → ∀ D ∈ (X.erase a).powersetCard 2, ∀ C : Finset ℝ, C.card = 3 →
  (∀ r ∈ C, 9 ≤ (F r).card ∧ D ⊆ (F r).biUnion id) →
  (∃ r ∈ C, OnCircleOfRadius (insert a D) r) →
  ∀ r ∈ insert s C, ∀ Q ⊆ X, Q.card = 4 → a ∈ Q →
  (∀ T ∈ Q.powersetCard 3, OnCircleOfRadius T r) →
  (∀ B ∈ Q.powersetCard 2, ∀ z ∈ X \ Q, ¬OnCircleOfRadius (insert z B) r) →
  396 ≤ (((X \ Q).powersetCard 2).filter (fun P => ∀ b ∈ Q, ¬ OnCircleOfRadius (insert b P) r)).card →
  ∃ Y ⊆ X, Y.card = 5 ∧ HasDistinctCircumradii Y

/-- Each marked radius has a matching containing at least two fifths
of its entire fan. This supplies six disjoint pairs at the radius with
thirteen triangles, and four disjoint pairs at each of the other rich radii. -/
def H2 : Prop := ∀ (X : Finset ℝ²), X.card = 37 → InGeneralPosition (X : Set ℝ²) →
  ∀ a ∈ X, let F (r : ℝ) := (((X.erase a).powersetCard 2).filter (fun B => OnCircleOfRadius (insert a B) r))
  ∀ (s : ℝ), 13 ≤ (F s).card → ∀ D ∈ (X.erase a).powersetCard 2, ∀ C : Finset ℝ, C.card = 3 →
  (∀ r ∈ C, 9 ≤ (F r).card ∧ D ⊆ (F r).biUnion id) →
  (∃ r ∈ C, OnCircleOfRadius (insert a D) r) →
  (∀ r ∈ insert s C, ¬ ∃ Q ⊆ X, Q.card = 4 ∧ a ∈ Q ∧ ∀ T ∈ Q.powersetCard 3, OnCircleOfRadius T r) →
  (∀ r ∈ insert s C, ∃ M ⊆ F r, (M : Set (Finset ℝ²)).PairwiseDisjoint id ∧ 2*(F r).card ≤ 5*M.card) →
  ∃ Y ⊆ X, Y.card = 5 ∧ HasDistinctCircumradii Y

theorem main : H1 → H2 → OMA.R_Erdos827_erdos_827_variants_n_five_le_R2.H1 := by
  classical
  intro tetra pack X n gp a ha
  dsimp only
  intro hs D hd C hc rich base
  obtain ⟨s,hs⟩ := hs
  by_cases mono : ∃ r ∈ insert s C, ∃ Q ⊆ X, Q.card=4 ∧ a ∈ Q ∧ ∀ T ∈ Q.powersetCard 3, OnCircleOfRadius T r
  · obtain ⟨r,hr,Q,qs,q4,aq,complete⟩ := mono
    exact tetra X n gp a ha s hs D hd C hc rich base r hr Q qs q4 aq complete
      (saturated_chords gp qs q4 complete) (outside_pairs gp n qs q4 r)
  · have none (r) (hr : r ∈ insert s C) := fun h => mono ⟨r,hr,h⟩
    apply pack X n gp a ha s hs D hd C hc rich base none
    intro r hr
    let L := (((X.erase a).powersetCard 2).filter (fun B => OnCircleOfRadius (insert a B) r))
    have sz (B) (hb : B ∈ L) : B.card = 2 := (mem_powersetCard.mp (mem_filter.mp hb).1).2
    obtain ⟨M,sub,ind,le⟩ := independent_packing (fun (B E : Finset ℝ²) => B ≠ E ∧ ¬ Disjoint B E)
      (fun _ _ h => ⟨h.1.symm,fun d => h.2 d.symm⟩) (fun x h => h.1 rfl)
      L (fun B hb => conflict_degree L sz (fan_degree gp ha r) hb)
      (fun B b E e P p h k l => none r hr (complete_triangle gp ha b e p h k l))
    exact ⟨M,sub,fun B b E e ne => by
      by_contra h
      exact ind B b E e ⟨ne,h⟩,le⟩
end OMA.R_Erdos827_erdos_827_variants_n_five_le_R2_H1_R1
