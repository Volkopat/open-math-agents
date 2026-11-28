import OMAReductions.R_Erdos827_erdos_827_variants_n_five_le_R1
import Mathlib

-- Reduction Erdos827.erdos_827.variants.n_five_le.R1.H3.R2 of step Erdos827.erdos_827.variants.n_five_le.R1.H3
-- Credit: @lettucrisp

/-! # Erdős 827, dense case: one dense vertex link is absorbed by counting

The count below is the merged proof of `n_five_le.R1.H2` by Marcus Buffett (#4926), with one
change. That proof bounds each vertex link by `2|L{a}| ≤ 630 * 11`, using at most twelve
equal-radius triangles per vertex and radius. Here one pair `(a₀, r₀)` may be dense. Its radius
class still has at most 36 triangles, because every point lies on at most two of them (the
fixed-chord bound, `fan_degree` and `radius_coloring`, copied from `n_five_le.R1.H3.R1`). A weighted link budget then gives
`2|L{a₀}| ≤ 630 * 11 + 24 * 36`. The final count still leaves room: bad five-sets ≤
`25d + 46620 + 128637 - 2d ≤ 435663 < 435897 = C(37,5)`.

What remains is the case of two distinct dense pairs, at one vertex (H1) or at two (H2). -/

/- A second count corrects the overlap among five-sets containing bad four-sets.
If there are d bad four-sets, at most 25*d+46620 five-sets contain one.
The remaining bad five-sets and twice the bad four-sets use at most 128205
vertex-link collisions. The pair-link bound gives d ≤ 11322, leaving at least
666 rainbow five-sets among the 435897 five-sets. -/

-- The radius coloring below is copied from the merged reduction n_five_le.R1.H3.R1
-- (fixed-chord bound by @ivillar, #4882, reusing @Genbox, #1550).
open Erdos827 EuclideanGeometry Finset

namespace OMA.Erdos827FiveH1

private theorem two_distances {a b c d e : ℝ²} {r s : ℝ}
    (hab : a ≠ b) (hcd : c ≠ d)
    (ha : dist c a = r) (hb : dist d a = r) (he : dist e a = r)
    (ha' : dist c b = s) (hb' : dist d b = s) (he' : dist e b = s) :
    e = c ∨ e = d :=
  eq_of_dist_eq_of_dist_eq_of_finrank_eq_two (by simp) hab hcd ha hb he ha' hb' he'

private theorem radius_unique_at_insert {E : Finset ℝ²} (hE : E.card = 2)
    {x : ℝ²} (hx : x ∉ E) {r s : ℝ}
    (h₁ : OnCircleOfRadius (insert x E) r) (h₂ : OnCircleOfRadius (insert x E) s) :
    r = s := by
  classical
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hE
  obtain ⟨c, hc⟩ := h₁
  obtain ⟨d, hd⟩ := h₂
  have hax : a ∈ (insert x {a, b} : Finset ℝ²) := by simp
  have hbx : b ∈ (insert x {a, b} : Finset ℝ²) := by simp
  have hxx : x ∈ (insert x {a, b} : Finset ℝ²) := by simp
  by_cases he : c = d
  · exact (hc x hxx).symm.trans (he ▸ hd x hxx)
  · exact False.elim (hx (by
      rcases two_distances he hab (hc a hax) (hc b hbx) (hc x hxx)
        (hd a hax) (hd b hbx) (hd x hxx) with h | h <;> simp [h]))

private theorem three_insert_impossible {X E : Finset ℝ²}
    (hX : NoFourConcyclic (X : Set ℝ²)) (hEX : E ⊆ X) (hE : E.card = 2)
    {x y z : ℝ²} (hxX : x ∈ X) (hyX : y ∈ X) (hzX : z ∈ X)
    (hx : x ∉ E) (hy : y ∉ E) (hz : z ∉ E)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {r : ℝ}
    (h₁ : OnCircleOfRadius (insert x E) r) (h₂ : OnCircleOfRadius (insert y E) r)
    (h₃ : OnCircleOfRadius (insert z E) r) : False := by
  classical
  have centers_ne {u v c : ℝ²} (huX : u ∈ X) (hvX : v ∈ X)
      (hu : u ∉ E) (hv : v ∉ E) (huv : u ≠ v)
      (huc : ∀ w ∈ insert u E, dist w c = r)
      (hvc : ∀ w ∈ insert v E, dist w c = r) : False := by
    apply hX (↑(insert u (insert v E)) : Set ℝ²)
    · intro w hw
      obtain rfl | hw := Finset.mem_insert.mp (Finset.mem_coe.mp hw)
      · exact huX
      · obtain rfl | hw := Finset.mem_insert.mp hw
        · exact hvX
        · exact hEX hw
    · rw [Set.ncard_coe_finset, Finset.card_insert_of_notMem (by simp [huv, hu]),
        Finset.card_insert_of_notMem hv, hE]
    · refine ⟨c, r, ?_⟩
      intro w hw
      obtain rfl | hw := Finset.mem_insert.mp (Finset.mem_coe.mp hw)
      · exact huc _ (Finset.mem_insert_self ..)
      · exact hvc w hw
  obtain ⟨c, hc⟩ := h₁
  obtain ⟨d, hd⟩ := h₂
  obtain ⟨e, he⟩ := h₃
  have hcd : c ≠ d := fun hh => centers_ne hxX hyX hx hy hxy hc (hh ▸ hd)
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hE
  have ha (w : ℝ²) : a ∈ (insert w {a, b} : Finset ℝ²) := by simp
  have hb (w : ℝ²) : b ∈ (insert w {a, b} : Finset ℝ²) := by simp
  obtain h | h := two_distances hab hcd
    ((dist_comm _ _).trans (hc a (ha x))) ((dist_comm _ _).trans (hd a (ha y)))
    ((dist_comm _ _).trans (he a (ha z))) ((dist_comm _ _).trans (hc b (hb x)))
    ((dist_comm _ _).trans (hd b (hb y))) ((dist_comm _ _).trans (he b (hb z)))
  · exact centers_ne hxX hzX hx hz hxz hc (h ▸ he)
  · exact centers_ne hyX hzX hy hz hyz hd (h ▸ he)

private theorem radius_unique {T : Finset ℝ²} (hT : T.card = 3) {r s : ℝ}
    (hr : OnCircleOfRadius T r) (hs : OnCircleOfRadius T s) : r = s := by
  classical
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  have hE : (T.erase p).card = 2 := by
    have := Finset.card_erase_add_one hp
    omega
  exact radius_unique_at_insert hE (notMem_erase p T)
    (by simpa [insert_erase hp] using hr) (by simpa [insert_erase hp] using hs)

private theorem exists_radius {X : Finset ℝ²} (hX : NonTrilinear (X : Set ℝ²)) {T : Finset ℝ²}
    (hT : T ⊆ X) (h3 : T.card = 3) : ∃ r, OnCircleOfRadius T r := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp h3
  have hcol : ¬ Collinear ℝ ({a, b, c} : Set ℝ²) :=
    hX (hT (by simp)) (hT (by simp)) (hT (by simp)) hab hbc hac
  have hind : AffineIndependent ℝ ![a, b, c] := affineIndependent_iff_not_collinear_set.mpr hcol
  obtain ⟨cs, ⟨_, hcs⟩, _⟩ := hind.existsUnique_dist_eq
  refine ⟨cs.radius, cs.center, fun p hp => ?_⟩
  have hp' : p ∈ Set.range ![a, b, c] := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  exact EuclideanGeometry.mem_sphere.mp (hcs hp')

end OMA.Erdos827FiveH1

open Erdos827 EuclideanGeometry Finset OMA.Erdos827FiveH1 in
theorem Erdos827Fan.radius_coloring : ∀ X : Finset ℝ², InGeneralPosition (X:Set ℝ²) →
  ∃ c : Finset ℝ²→ℝ, (∀ T⊆X,T.card=3 → ∀ r, c T=r ↔ OnCircleOfRadius T r) ∧
    ∀ B⊆X,B.card=2 → ∀ r, ((X\B).filter (fun z => c (insert z B)=r)).card≤2 := by
  intro X hX
  obtain ⟨hNT, hNF⟩ := hX
  classical
  let c : Finset ℝ² → ℝ := fun T => if h : ∃ r, OnCircleOfRadius T r then h.choose else 0
  have hc : ∀ T ⊆ X, T.card = 3 → OnCircleOfRadius T (c T) := by
    intro T hT h3
    have h := exists_radius hNT hT h3
    simp only [c, dif_pos h]
    exact h.choose_spec
  refine ⟨c, ?_, ?_⟩
  · intro T hT h3 r
    constructor
    · rintro rfl
      exact hc T hT h3
    · intro hr
      exact radius_unique h3 (hc T hT h3) hr
  · intro B hB h2 r
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.mp hlt
    rw [Finset.mem_filter, Finset.mem_sdiff] at hx hy hz
    have hins (w : ℝ²) (hw : w ∈ X) (hwB : w ∉ B) :
        OnCircleOfRadius (insert w B) (c (insert w B)) :=
      hc _ (Finset.insert_subset hw hB) (by rw [Finset.card_insert_of_notMem hwB, h2])
    have ox := hins x hx.1.1 hx.1.2
    have oy := hins y hy.1.1 hy.1.2
    have oz := hins z hz.1.1 hz.1.2
    rw [hx.2] at ox
    rw [hy.2] at oy
    rw [hz.2] at oz
    exact three_insert_impossible hNF hB h2 hx.1.1 hy.1.1 hz.1.1 hx.1.2 hy.1.2 hz.1.2
      hxy hxz hyz ox oy oz


namespace OMA.DenseOnce
open Finset
open scoped Classical
variable {α : Type*} [DecidableEq α]

lemma exchange {β γ : Type*} (S : Finset β) (T : Finset γ) (R : β → γ → Prop) [∀ a b, Decidable (R a b)] :
    (∑ a ∈ S, (T.filter (R a)).card) = ∑ b ∈ T, (S.filter fun a => R a b).card := by
  simp only [card_filter]
  exact sum_comm

lemma restrict_below (X d : Finset α) (sub : d⊆X) (k : ℕ) :
    ((X.powersetCard k).filter (· ⊆ d)) = d.powersetCard k := by
  ext z
  simp only [mem_filter,mem_powersetCard]
  exact ⟨fun h => ⟨h.2,h.1.2⟩, fun h => ⟨⟨h.1.trans sub,h.2⟩,h.1⟩⟩

lemma choose_sum {β γ : Type*} (S : Finset β) (D : Finset γ) (R : β → γ → Prop) [∀ a b, Decidable (R a b)] :
    (∑ a ∈ S, ((D.filter (R a)).card).choose 2) =
    ∑ Q ∈ D.powersetCard 2, (S.filter fun a => ∀ d ∈ Q, R a d).card := by
  have one (a : β) : (D.filter (R a)).powersetCard 2 =
      (D.powersetCard 2).filter (fun Q => ∀ d ∈ Q, R a d) := by
    ext Q
    simp only [mem_filter,mem_powersetCard]
    constructor
    · intro h
      exact ⟨⟨h.1.trans (filter_subset _ _),h.2⟩,fun d hd => (mem_filter.mp (h.1 hd)).2⟩
    · rintro ⟨⟨sub,sz⟩,rel⟩
      exact ⟨fun d hd => mem_filter.mpr ⟨sub hd,rel d hd⟩,sz⟩
  calc _ = ∑ a ∈ S, ((D.powersetCard 2).filter (fun Q => ∀ d ∈ Q, R a d)).card :=
         sum_congr rfl fun a _ => (card_powersetCard 2 (D.filter (R a))).symm.trans (congrArg Finset.card (one a))
       _ = _ := exchange _ _ _

lemma pair_shadow (X : Finset α) (D : Finset (Finset α)) (hd : D ⊆ X.powersetCard 4) :
    (∑ B ∈ X.powersetCard 3, ((D.filter (B ⊆ ·)).card).choose 2) ≤
    ∑ Y ∈ X.powersetCard 5, ((D.filter (· ⊆ Y)).card).choose 2 := by
  rw [choose_sum (X.powersetCard 3) D (fun B d => B⊆d),
      choose_sum (X.powersetCard 5) D (fun Y d => d⊆Y)]
  apply sum_le_sum
  intro Q hQ
  obtain ⟨sub,sz⟩ := mem_powersetCard.mp hQ
  obtain ⟨d,e,ne,rfl⟩ := card_eq_two.mp sz
  have ds := mem_powersetCard.mp (hd (sub (by simp : d ∈ ({d,e} : Finset _))))
  have es := mem_powersetCard.mp (hd (sub (by simp : e ∈ ({d,e} : Finset _))))
  have hlt : (d∩e).card < 4 := by
    by_contra! h
    have one := eq_of_subset_of_card_le (inter_subset_left (s₁ := d) (s₂ := e)) (ds.2 ▸ h)
    have two := eq_of_subset_of_card_le (inter_subset_right (s₁ := d) (s₂ := e)) (es.2 ▸ h)
    exact ne (one.symm.trans two)
  by_cases haveB : ∃ B ∈ X.powersetCard 3, B⊆d ∧ B⊆e
  · obtain ⟨B,hB,hBd,hBe⟩ := haveB
    have z := card_le_card (subset_inter hBd hBe)
    have sb := (mem_powersetCard.mp hB).2
    have hi : (d∩e).card=3 := by omega
    have un := card_union_add_card_inter d e
    have hu : d∪e ∈ X.powersetCard 5 :=
      mem_powersetCard.mpr ⟨union_subset ds.1 es.1,by omega⟩
    have small : ((X.powersetCard 3).filter (fun a => ∀ b ∈ ({d,e}:Finset _), a⊆b)).card ≤ 1 := by
      apply card_le_one.mpr
      intro a ha b hb
      have ident (z) (hz : z ∈ (X.powersetCard 3).filter (fun a => ∀ b ∈ ({d,e}:Finset _), a⊆b)) :
          z=d∩e := by
        obtain ⟨hz,holds⟩ := mem_filter.mp hz
        apply eq_of_subset_of_card_le (subset_inter (holds d (by simp)) (holds e (by simp)))
        rw [hi,(mem_powersetCard.mp hz).2]
      exact (ident a ha).trans (ident b hb).symm
    apply small.trans
    apply card_pos.mpr
    exact ⟨d∪e,mem_filter.mpr ⟨hu,by simp⟩⟩
  · have no : ((X.powersetCard 3).filter (fun a => ∀ b ∈ ({d,e}:Finset _), a⊆b)) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro a ha
      obtain ⟨ha,ok⟩ := mem_filter.mp ha
      exact haveB ⟨a,ha,ok d (by simp),ok e (by simp)⟩
    rw [no,card_empty]
    exact Nat.zero_le _

lemma shadow_budget (X : Finset α) (D : Finset (Finset α)) (hX : X.card=37)
    (hd : D ⊆ X.powersetCard 4) :
    ((X.powersetCard 5).filter fun Y => ∃ d ∈ D, d⊆Y).card ≤ 25*D.card + 46620 := by
  let A := X.powersetCard 3
  let Z := X.powersetCard 5
  let n (B : Finset α) := (D.filter (B ⊆ ·)).card
  let k (Y : Finset α) := (D.filter (· ⊆ Y)).card
  have na : (∑ B ∈ A, n B) = 4*D.card := by
    change (∑ B ∈ A, (D.filter (B⊆·)).card) = _
    rw [exchange A D (fun B d => B⊆d)]
    have one (d) (h : d∈D) : (A.filter (·⊆d)).card=4 := by
      obtain ⟨s,sz⟩ := mem_powersetCard.mp (hd h)
      dsimp only [A]
      rw [restrict_below _ _ s,card_powersetCard,sz]; decide
    simpa [mul_comm] using sum_congr rfl one
  have kz : (∑ Y ∈ Z, k Y) = 33*D.card := by
    change (∑ Y ∈ Z, (D.filter (·⊆Y)).card) = _
    rw [exchange Z D (fun Y d => d⊆Y)]
    have one (d) (h : d∈D) : (Z.filter (d⊆·)).card=33 := by
      obtain ⟨s,sz⟩ := mem_powersetCard.mp (hd h)
      dsimp only [Z]
      rw [card_filter_powersetCard_subset _ _ _ s (by omega),sz,hX]; decide
    simpa [mul_comm] using sum_congr rfl one
  have choose_low (a : ℕ) : 5*a ≤ a.choose 2 + 15 := by
    induction a with
    | zero => decide
    | succ a ih =>
      by_cases h : a<5
      · interval_cases a <;> decide
      · have iden : (a+1).choose 2 = a + a.choose 2 := by simpa only [Nat.choose_one_right] using Nat.choose_succ_succ a 1
        omega
  have countA : A.card=7770 := by dsimp only [A]; rw [card_powersetCard,hX]; decide
  have lo := sum_le_sum (s := A) (fun B _ => choose_low (n B))
  simp only [←mul_sum,sum_add_distrib,sum_const,smul_eq_mul,countA,na] at lo
  have common := pair_shadow X D hd
  change (∑ B ∈ A, (n B).choose 2) ≤ ∑ Y ∈ Z, (k Y).choose 2 at common
  have upper (Y) (hY : Y∈Z) : 2*(k Y).choose 2 + 5*(if 0<k Y then 1 else 0) ≤ 5*k Y := by
    have h : D.filter (·⊆Y) ⊆ Y.powersetCard 4 := fun d h => mem_powersetCard.mpr
      ⟨(mem_filter.mp h).2,(mem_powersetCard.mp (hd (mem_filter.mp h).1)).2⟩
    have bound := card_le_card h
    rw [card_powersetCard,(mem_powersetCard.mp hY).2] at bound
    change k Y ≤ 5 at bound
    generalize e : k Y = a at *
    interval_cases a <;> decide
  have up := sum_le_sum upper
  simp only [sum_add_distrib,←mul_sum,kz] at up
  have c : ((X.powersetCard 5).filter fun Y => ∃ d ∈ D,d⊆Y).card =
      ∑ Y ∈ Z, if 0<k Y then 1 else 0 := by
    rw [card_filter]
    apply sum_congr rfl
    intro Y _
    have iff : (∃ d ∈ D,d⊆Y) ↔ 0<k Y := by simp only [k,card_pos,filter_nonempty_iff]
    simp only [iff]
  rw [c]
  omega

end OMA.DenseOnce


namespace OMA.DenseOnce
open Finset
open scoped Classical
variable {α : Type*} [DecidableEq α]

lemma link_budget (S : Finset (Finset α)) (c : Finset α → ℝ) (F : Finset (Finset α))
    (p q : Finset α → Finset α) (k : ℕ)
    (pair : ∀ Y∈F, p Y∈S ∧ q Y∈S ∧ p Y ≠ q Y ∧ c (p Y)=c (q Y) ∧ p Y ∪ q Y=Y)
    (cap : ∀ r, (S.filter fun T => c T=r).card ≤ k+1) : 2*F.card ≤ S.card*k := by
  classical
  let R (Y T : Finset α) := T=p Y ∨ T=q Y
  have low (Y) (h : Y∈F) : 2 ≤ (S.filter (R Y)).card := by
    obtain ⟨hp,hq,ne,_,_⟩ := pair Y h
    have eq : S.filter (R Y)={p Y,q Y} := by ext T; simp [R]; aesop
    simp [eq,ne]
  have high (T) (hT : T ∈ S) : (F.filter (fun Y => R Y T)).card ≤ k := by
    let other (Y : Finset α) := if T=p Y then q Y else p Y
    have info {Y} (h : Y ∈ F.filter (fun Y => R Y T)) :
        other Y ∈ S ∧ other Y ≠ T ∧ c (other Y) = c T ∧ T ∪ other Y=Y := by
      obtain ⟨hY,rel⟩ := mem_filter.mp h
      obtain ⟨hp,hq,ne,col,un⟩ := pair Y hY
      rcases rel with e|e
      · simp only [other,e,ite_true]
        exact ⟨hq,ne.symm,col.symm,un⟩
      · simp only [other,e,if_neg ne.symm]
        exact ⟨hp,ne,col,(union_comm _ _).trans un⟩
    have cmp : (F.filter (fun Y => R Y T)).card ≤ ((S.filter fun U => c U=c T).erase T).card := by
      apply card_le_card_of_injOn other
      · intro Y h
        obtain ⟨hs,hn,hc,_⟩ := info h
        exact mem_erase.mpr ⟨hn,mem_filter.mpr ⟨hs,hc⟩⟩
      · intro Y hY Z hZ eq
        rw [←(info hY).2.2.2,←(info hZ).2.2.2,eq]
    have del := card_erase_add_one (mem_filter.mpr ⟨hT,rfl⟩ : T∈S.filter fun U => c U=c T)
    have lim := cap (c T)
    omega
  have e : F.card • (2:ℕ) ≤ S.card • k :=
    card_nsmul_le_card_nsmul (r := R) (s := F) (t := S) low high
  simpa only [smul_eq_mul,mul_comm F.card] using e

lemma vertex_fiber (X : Finset α) (c : Finset α → ℝ) (a : α) (r : ℝ) (k : ℕ)
    (cap : (((X.erase a).powersetCard 2).filter (fun B => c (insert a B)=r)).card ≤ k) :
    (((X.powersetCard 3).filter ({a} ⊆ ·)).filter (fun T => c T=r)).card ≤ k := by
  apply le_trans _ cap
  apply card_le_card_of_injOn (fun T : Finset α => T.erase a)
  · intro T hT
    obtain ⟨hT,col⟩ := mem_filter.mp hT
    obtain ⟨hT,contains⟩ := mem_filter.mp hT
    obtain ⟨sub,sz⟩ := mem_powersetCard.mp hT
    have ha := singleton_subset_iff.mp contains
    apply mem_filter.mpr
    refine ⟨mem_powersetCard.mpr ⟨erase_subset_erase _ sub,?_⟩,?_⟩
    · rw [card_erase_of_mem ha,sz]
    · simpa only [insert_erase ha] using col
  · intro T hT U hU eq
    have h (V) (hv : V ∈ ((X.powersetCard 3).filter ({a} ⊆ ·)).filter (fun T => c T=r)) :
        a∈V := singleton_subset_iff.mp (mem_filter.mp (mem_filter.mp hv).1).2
    exact (insert_erase (h _ hT)).symm.trans ((congrArg (insert a) eq).trans (insert_erase (h _ hU)))

lemma edge_fiber (X B : Finset α) (c : Finset α → ℝ) (r : ℝ) (sb : B.card=2)
    (cap : ((X\B).filter fun z => c (insert z B)=r).card ≤ 2) :
    (((X.powersetCard 3).filter (B ⊆ ·)).filter (fun T => c T=r)).card ≤ 2 := by
  let S := ((X.powersetCard 3).filter (B ⊆ ·)).filter fun T => c T=r
  let Z := (X\B).filter fun z => c (insert z B)=r
  have sub : S ⊆ Z.image (fun z => insert z B) := by
    intro T h
    obtain ⟨hT,col⟩ := mem_filter.mp h
    obtain ⟨hT,contains⟩ := mem_filter.mp hT
    obtain ⟨tx,st⟩ := mem_powersetCard.mp hT
    have cs : (T\B).card=1 := by rw [card_sdiff_of_subset contains,st,sb]
    obtain ⟨z,hz⟩ := card_eq_one.mp cs
    have inD : z∈T\B := by rw [hz]; simp
    have eq : insert z B=T := by
      rw [←singleton_union,←hz,sdiff_union_of_subset contains]
    exact mem_image.mpr ⟨z,mem_filter.mpr ⟨mem_sdiff.mpr
      ⟨tx (mem_sdiff.mp inD).1,(mem_sdiff.mp inD).2⟩,eq ▸ col⟩,eq⟩
  exact (card_le_card sub).trans (card_image_le.trans cap)

theorem fan_degree' {α : Type*} [DecidableEq α] (X : Finset α) (c : Finset α → ℝ)
    (edges : ∀ B⊆X, B.card=2 → ∀ r, ((X\B).filter fun z => c (insert z B)=r).card≤2)
    {a : α} (ha : a ∈ X) (r : ℝ) (b : α) :
    let L := ((X.erase a).powersetCard 2).filter fun B => c (insert a B)=r
    (L.filter (b ∈ ·)).card ≤ 2 := by
  dsimp only
  let L := ((X.erase a).powersetCard 2).filter fun B => c (insert a B)=r
  let U := L.biUnion id
  have support : U ⊆ X.erase a := by
    intro x hx
    obtain ⟨B,hB,mem⟩ := mem_biUnion.mp hx
    exact (mem_powersetCard.mp (mem_filter.mp hB).1).1 mem
  change (L.filter (b ∈ ·)).card ≤ 2
  by_cases inU : b ∈ U
  ·
    have hb : b ∈ X.erase a := support inU
    have ba : b ≠ a := (mem_erase.mp hb).1
    let P : Finset α := {a,b}
    have sz : P.card = 2 := card_pair ba.symm
    have hP : P ⊆ X := insert_subset ha (singleton_subset_iff.mpr (mem_erase.mp hb).2)
    let T := (X\P).filter fun z => c (insert z P) = r
    have sub : L.filter (b ∈ ·) ⊆ T.image (fun z => ({b,z} : Finset α)) := by
      intro B h
      obtain ⟨hB,bB⟩ := mem_filter.mp h
      obtain ⟨hB,col⟩ := mem_filter.mp hB
      obtain ⟨inV,szB⟩ := mem_powersetCard.mp hB
      obtain ⟨z,ne,w,eq⟩ := Finset.card_eq_two.mp szB
      rcases (show b = z ∨ b = ne by simpa [eq] using bB) with e|e
      · subst z
        have hn := mem_erase.mp (inV (show ne∈B by simp [eq]))
        exact mem_image.mpr ⟨ne,mem_filter.mpr ⟨mem_sdiff.mpr ⟨hn.2,by simp [P,hn.1,w.symm]⟩,
          by convert col using 2; ext x; simp [P,eq]; tauto⟩,eq.symm⟩
      · subst ne
        have hn := mem_erase.mp (inV (show z∈B by simp [eq]))
        exact mem_image.mpr ⟨z,mem_filter.mpr ⟨mem_sdiff.mpr ⟨hn.2,by simp [P,hn.1,w]⟩,
          by convert col using 2; ext x; simp [P,eq]; tauto⟩,by rw [eq,pair_comm]⟩
    exact (card_le_card sub).trans (card_image_le.trans (edges P hP sz r))
  · have empty : L.filter (b ∈ ·) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro B h
      obtain ⟨hB,hb⟩ := mem_filter.mp h
      exact inU (mem_biUnion.mpr ⟨B,hB,hb⟩)
    simp [empty]



/-- Weighted form of `link_budget`: each triple `T` pairs with at most `w T` others. -/
lemma link_budget_w (S : Finset (Finset α)) (c : Finset α → ℝ) (F : Finset (Finset α))
    (p q : Finset α → Finset α) (w : Finset α → ℕ)
    (pair : ∀ Y∈F, p Y∈S ∧ q Y∈S ∧ p Y ≠ q Y ∧ c (p Y)=c (q Y) ∧ p Y ∪ q Y=Y)
    (cap : ∀ T ∈ S, (S.filter fun U => c U=c T).card ≤ w T+1) : 2*F.card ≤ ∑ T ∈ S, w T := by
  classical
  let R (Y T : Finset α) := T=p Y ∨ T=q Y
  have low (Y) (h : Y∈F) : 2 ≤ (S.filter (R Y)).card := by
    obtain ⟨hp,hq,ne,_,_⟩ := pair Y h
    have eq : S.filter (R Y)={p Y,q Y} := by ext T; simp [R]; aesop
    simp [eq,ne]
  have high (T) (hT : T ∈ S) : (F.filter (fun Y => R Y T)).card ≤ w T := by
    let other (Y : Finset α) := if T=p Y then q Y else p Y
    have info {Y} (h : Y ∈ F.filter (fun Y => R Y T)) :
        other Y ∈ S ∧ other Y ≠ T ∧ c (other Y) = c T ∧ T ∪ other Y=Y := by
      obtain ⟨hY,rel⟩ := mem_filter.mp h
      obtain ⟨hp,hq,ne,col,un⟩ := pair Y hY
      rcases rel with e|e
      · simp only [other,e,ite_true]
        exact ⟨hq,ne.symm,col.symm,un⟩
      · simp only [other,e,if_neg ne.symm]
        exact ⟨hp,ne,col,(union_comm _ _).trans un⟩
    have cmp : (F.filter (fun Y => R Y T)).card ≤ ((S.filter fun U => c U=c T).erase T).card := by
      apply card_le_card_of_injOn other
      · intro Y h
        obtain ⟨hs,hn,hc,_⟩ := info h
        exact mem_erase.mpr ⟨hn,mem_filter.mpr ⟨hs,hc⟩⟩
      · intro Y hY Z hZ eq
        rw [←(info hY).2.2.2,←(info hZ).2.2.2,eq]
    have del := card_erase_add_one (mem_filter.mpr ⟨hT,rfl⟩ : T∈S.filter fun U => c U=c T)
    have lim := cap T hT
    omega
  have two : 2*F.card ≤ ∑ Y ∈ F, (S.filter (R Y)).card := by
    rw [mul_comm, ← smul_eq_mul, ← sum_const]; exact sum_le_sum low
  calc 2*F.card ≤ ∑ Y ∈ F, (S.filter (R Y)).card := two
    _ = ∑ T ∈ S, (F.filter (fun Y => R Y T)).card := exchange F S R
    _ ≤ ∑ T ∈ S, w T := sum_le_sum high

/-- A vertex link has at most 36 edges: every point lies on at most two of them. -/
lemma fan_le (X : Finset α) (c : Finset α → ℝ) (hX : X.card=37)
    (edges : ∀ B⊆X, B.card=2 → ∀ r, ((X\B).filter fun z => c (insert z B)=r).card≤2)
    {a : α} (ha : a ∈ X) (r : ℝ) :
    (((X.erase a).powersetCard 2).filter fun B => c (insert a B)=r).card ≤ 36 := by
  classical
  set L := ((X.erase a).powersetCard 2).filter fun B => c (insert a B)=r with hL
  have deg (b : α) : (L.filter (b ∈ ·)).card ≤ 2 := fan_degree' X c edges ha r b
  have ex := exchange (X.erase a) L (fun b B => b ∈ B)
  have each (B) (hB : B ∈ L) : ((X.erase a).filter (· ∈ B)).card = 2 := by
    obtain ⟨sub,sz⟩ := mem_powersetCard.mp (mem_filter.mp hB).1
    rw [← sz]; congr 1; ext x; simp only [mem_filter]; exact ⟨And.right,fun h => ⟨sub h,h⟩⟩
  rw [sum_congr rfl each, sum_const, smul_eq_mul] at ex
  have up : ∑ b ∈ X.erase a, (L.filter (b ∈ ·)).card ≤ ∑ b ∈ X.erase a, 2 := sum_le_sum fun b _ => deg b
  rw [sum_const, smul_eq_mul, card_erase_of_mem ha, hX] at up
  omega

end OMA.DenseOnce


namespace OMA.DenseOnce
open Finset
open scoped Classical
variable {α : Type*} [DecidableEq α]

theorem rainbow_five (X : Finset α) (c : Finset α → ℝ) (hX : X.card=37)
    (edges : ∀ B⊆X, B.card=2 → ∀ r, ((X\B).filter (fun z => c (insert z B)=r)).card≤2)
    (a₀ : α) (ha₀ : a₀ ∈ X) (r₀ : ℝ)
    (vertices : ∀ a∈X,∀ r, (a ≠ a₀ ∨ r ≠ r₀) →
      (((X.erase a).powersetCard 2).filter (fun B => c (insert a B)=r)).card≤12) :
    ∃ Y⊆X, Y.card=5 ∧ Set.InjOn c (Y.powersetCard 3 : Set (Finset α)) := by
  classical
  by_contra! no
  let bad (Y : Finset α) := ¬ Set.InjOn c (Y.powersetCard 3 : Set (Finset α))
  let D := (X.powersetCard 4).filter bad
  let E := (X.powersetCard 5).filter fun Y => ¬ ∃ d∈D,d⊆Y
  let F := D∪E
  have fd : D ⊆ F := subset_union_left
  have fe : E ⊆ F := subset_union_right
  have dX : D ⊆ X.powersetCard 4 := filter_subset _ _
  have eX : E ⊆ X.powersetCard 5 := filter_subset _ _
  have points {Y : Finset α} (hY : Y ∈ F) : Y⊆X := by
    rcases mem_union.mp hY with h|h
    · exact (mem_powersetCard.mp (dX h)).1
    · exact (mem_powersetCard.mp (eX h)).1
  have de : Disjoint D E := disjoint_left.mpr fun Y hd he => by
    have four := (mem_powersetCard.mp (dX hd)).2
    have five := (mem_powersetCard.mp (eX he)).2
    omega
  have pick (Y : Finset α) (hY : Y∈F) :
      ∃ p q : Finset α, p ∈ X.powersetCard 3 ∧ q ∈ X.powersetCard 3 ∧
        p≠q ∧ c p=c q ∧ p∪q=Y := by
    have hb : bad Y := by
      rcases mem_union.mp hY with h|h
      · exact (mem_filter.mp h).2
      · exact no Y (points hY) (mem_powersetCard.mp (eX h)).2
    change ¬ Set.InjOn _ _ at hb
    simp only [Set.InjOn,not_forall] at hb
    push Not at hb
    obtain ⟨p,hp,q,hq,col,ne⟩ := hb
    obtain ⟨py,sp⟩ := mem_powersetCard.mp hp
    obtain ⟨qy,sq⟩ := mem_powersetCard.mp hq
    have un : p∪q ⊆ Y := union_subset py qy
    have more : 3 < (p∪q).card := by
      by_contra! le
      have ep := eq_of_subset_of_card_le (subset_union_left (s₂ := q)) (show (p∪q).card ≤ p.card by omega)
      have eq := eq_of_subset_of_card_le (subset_union_right (s₁ := p)) (show (p∪q).card ≤ q.card by omega)
      exact ne (ep.trans eq.symm)
    refine ⟨p,q,mem_powersetCard.mpr ⟨py.trans (points hY),sp⟩,
      mem_powersetCard.mpr ⟨qy.trans (points hY),sq⟩,ne,col,?_⟩
    apply eq_of_subset_of_card_le un
    rcases mem_union.mp hY with hd|he
    · rw [(mem_powersetCard.mp (dX hd)).2]; omega
    · have sz := (mem_powersetCard.mp (eX he)).2
      by_contra! lt
      have su : (p∪q).card=4 := by omega
      apply (mem_filter.mp he).2
      refine ⟨p∪q,mem_filter.mpr ⟨mem_powersetCard.mpr ⟨un.trans (points hY),su⟩,?_⟩,un⟩
      intro injective
      exact ne (injective (mem_powersetCard.mpr ⟨subset_union_left,sp⟩)
        (mem_powersetCard.mpr ⟨subset_union_right,sq⟩) col)
  choose! p q pair using pick
  let I (Y : Finset α) := p Y ∩ q Y
  have iX (Y) (hy : Y∈F) : I Y ⊆ X :=
    inter_subset_left.trans (mem_powersetCard.mp (pair Y hy).1).1
  have ic (Y) (hy : Y∈F) : Y.card+(I Y).card=6 := by
    obtain ⟨hp,hq,_,_,un⟩ := pair Y hy
    simpa only [I,un,(mem_powersetCard.mp hp).2,(mem_powersetCard.mp hq).2] using card_union_add_card_inter (p Y) (q Y)
  let S (B : Finset α) := (X.powersetCard 3).filter (B⊆·)
  let L (B : Finset α) := F.filter fun Y => B⊆I Y
  have bound (B : Finset α) (k : ℕ) (lim : ∀ r, ((S B).filter fun T => c T=r).card ≤ k+1) :
      2*(L B).card ≤ (S B).card*k := by
    apply link_budget (S B) c (L B) p q k _ lim
    intro Y hy
    obtain ⟨yf,bi⟩ := mem_filter.mp hy
    obtain ⟨hp,hq,ne,col,un⟩ := pair Y yf
    exact ⟨mem_filter.mpr ⟨hp,bi.trans inter_subset_left⟩,mem_filter.mpr ⟨hq,bi.trans inter_subset_right⟩,ne,col,un⟩
  have degree (a : α) (ha : a∈X) : 2*((L {a}).card) ≤ 6930 + (if a = a₀ then 864 else 0) := by
    have k : (S {a}).card=630 := by
      dsimp only [S]; rw [card_filter_powersetCard_subset _ _ _ (singleton_subset_iff.mpr ha) (by simp),hX,card_singleton]; decide
    by_cases e : a = a₀
    · subst e
      rw [if_pos rfl]
      have fib (r : ℝ) : ((S {a}).filter fun T => c T=r).card ≤ 36 :=
        vertex_fiber X c a r 36 (fan_le X c hX edges ha r)
      have b := link_budget_w (S {a}) c (L {a}) p q (fun T => 11 + if c T = r₀ then 24 else 0)
        (by
          intro Y hy
          obtain ⟨yf,bi⟩ := mem_filter.mp hy
          obtain ⟨hp,hq,ne,col,un⟩ := pair Y yf
          exact ⟨mem_filter.mpr ⟨hp,bi.trans inter_subset_left⟩,
            mem_filter.mpr ⟨hq,bi.trans inter_subset_right⟩,ne,col,un⟩)
        (by
          intro T _
          by_cases hc : c T = r₀
          · rw [if_pos hc]; have := fib (c T); omega
          · rw [if_neg hc]
            have := vertex_fiber X c a (c T) 12 (vertices a ha (c T) (Or.inr hc)); omega)
      rw [sum_add_distrib, sum_const, smul_eq_mul, k, sum_ite, sum_const_zero, sum_const,
        smul_eq_mul] at b
      have := fib r₀
      omega
    · rw [if_neg e]
      have b := bound {a} 11 (fun r => vertex_fiber X c a r 12 (vertices a ha r (Or.inl e)))
      omega
  have countV : (∑ a ∈ X, (L {a}).card)=2*D.card+E.card := by
    change (∑ a ∈ X, (F.filter (fun Y => {a}⊆I Y)).card)=_
    rw [exchange X F (fun a Y => {a}⊆I Y)]
    have each (Y) (hy : Y∈F) : (X.filter fun a => {a}⊆I Y).card = (I Y).card := by
      congr 1; ext a
      simp only [mem_filter,singleton_subset_iff]
      exact ⟨And.right,fun ha => ⟨iX Y hy ha,ha⟩⟩
    rw [sum_congr rfl each]
    change (∑ Y ∈ D∪E, (I Y).card)=_
    rw [sum_union de]
    have dcount (Y) (hy : Y∈D) : (I Y).card=2 := by
      have := ic Y (fd hy); have := (mem_powersetCard.mp (dX hy)).2; omega
    have ecount (Y) (hy : Y∈E) : (I Y).card=1 := by
      have := ic Y (fe hy); have := (mem_powersetCard.mp (eX hy)).2; omega
    rw [sum_congr rfl dcount,sum_congr rfl ecount]
    simp [mul_comm]
  have many := sum_le_sum degree
  rw [sum_add_distrib, sum_ite_eq' X a₀ (fun _ => 864), if_pos ha₀, sum_const, smul_eq_mul, hX,
    ← mul_sum, countV] at many
  have per (B) (hB : B ∈ X.powersetCard 2) : (L B).card ≤ 17 := by
    obtain ⟨bx,sb⟩ := mem_powersetCard.mp hB
    have b := bound B 1 (fun r => edge_fiber X B c r sb (edges B bx sb r))
    have s : (S B).card=35 := by
      dsimp only [S]; rw [card_filter_powersetCard_subset _ _ _ bx (by omega),sb,hX]; decide
    omega
  have dBound : D.card ≤ 11322 := by
    have sub (Y) (h : Y∈D) : I Y ∈ X.powersetCard 2 := by
      refine mem_powersetCard.mpr ⟨iX Y (fd h),?_⟩
      have := ic Y (fd h); have := (mem_powersetCard.mp (dX h)).2; omega
    have inequality : D.card ≤ ∑ B ∈ X.powersetCard 2, (L B).card := by
      calc D.card = ∑ Y ∈ D, (1:ℕ) := by simp
           _ ≤ ∑ Y ∈ D, ((X.powersetCard 2).filter (·⊆I Y)).card := sum_le_sum (fun Y h =>
                  card_pos.mpr ⟨I Y,mem_filter.mpr ⟨sub Y h,Subset.rfl⟩⟩)
           _ ≤ _ := by
             rw [exchange D (X.powersetCard 2) (fun Y B => B ⊆ I Y)]
             exact sum_le_sum fun B _ => card_le_card (filter_subset_filter _ fd)
    have b := sum_le_sum per
    rw [sum_const,smul_eq_mul,card_powersetCard,hX] at b
    rw [show Nat.choose 37 2 = 666 by decide] at b
    omega
  have shadow := shadow_budget X D hX dX
  have parts := card_filter_add_card_filter_not (s := X.powersetCard 5) (fun Y => ∃ d∈D,d⊆Y)
  change _ + E.card = _ at parts
  rw [card_powersetCard,hX] at parts
  rw [show Nat.choose 37 5 = 435897 by decide] at parts
  omega
end OMA.DenseOnce



namespace OMA.R_Erdos827_erdos_827_variants_n_five_le_R1_H3_R2
open Finset EuclideanGeometry Erdos827
open scoped Classical

/-- Two distinct radii are dense at the same vertex. -/
def H1 : Prop := ∀ (X : Finset ℝ²), X.card = 37 → InGeneralPosition (X : Set ℝ²) →
  ∀ a ∈ X, ∀ r s : ℝ, r ≠ s →
    13 ≤ (((X.erase a).powersetCard 2).filter (fun B => OnCircleOfRadius (insert a B) r)).card →
    13 ≤ (((X.erase a).powersetCard 2).filter (fun B => OnCircleOfRadius (insert a B) s)).card →
  ∃ Y ⊆ X, Y.card = 5 ∧ HasDistinctCircumradii Y

/-- Dense radii at two distinct vertices. -/
def H2 : Prop := ∀ (X : Finset ℝ²), X.card = 37 → InGeneralPosition (X : Set ℝ²) →
  ∀ a ∈ X, ∀ b ∈ X, a ≠ b → ∀ r s : ℝ,
    13 ≤ (((X.erase a).powersetCard 2).filter (fun B => OnCircleOfRadius (insert a B) r)).card →
    13 ≤ (((X.erase b).powersetCard 2).filter (fun B => OnCircleOfRadius (insert b B) s)).card →
  ∃ Y ⊆ X, Y.card = 5 ∧ HasDistinctCircumradii Y

theorem main : H1 → H2 → OMA.R_Erdos827_erdos_827_variants_n_five_le_R1.H3 := by
  intro same apart X size gp a ha r rich
  classical
  obtain ⟨c,track,cap⟩ := Erdos827Fan.radius_coloring X gp
  have colors (v : ℝ²) (hv : v ∈ X) (s : ℝ) :
      (((X.erase v).powersetCard 2).filter (fun B => OnCircleOfRadius (insert v B) s)).card =
      (((X.erase v).powersetCard 2).filter (fun B => c (insert v B) = s)).card := by
    congr 1
    apply filter_congr
    intro B h
    obtain ⟨sub,sz⟩ := mem_powersetCard.mp h
    have an : v ∉ B := fun h => notMem_erase v X (sub h)
    exact (track _ (insert_subset hv (sub.trans (erase_subset ..))) (by simp [an,sz]) s).symm
  by_cases two : ∃ b ∈ X, ∃ s : ℝ, (b ≠ a ∨ s ≠ r) ∧
      13 ≤ (((X.erase b).powersetCard 2).filter (fun B => c (insert b B) = s)).card
  · obtain ⟨b,hb,s,ne,dense⟩ := two
    rw [← colors b hb s] at dense
    by_cases e : b = a
    · subst e
      exact same X size gp b hb r s (fun h => (ne.resolve_left (not_not.mpr rfl)) h.symm) rich dense
    · exact apart X size gp a ha b hb (fun h => e h.symm) r s rich dense
  · push Not at two
    obtain ⟨Y,yx,sy,injective⟩ := OMA.DenseOnce.rainbow_five X c size cap a ha r
      (fun b hb s ne => by have := two b hb s ne; omega)
    refine ⟨Y,yx,sy,?_⟩
    intro T ty U uy st su ne s hr hs
    apply ne
    exact injective (mem_powersetCard.mpr ⟨ty,st⟩) (mem_powersetCard.mpr ⟨uy,su⟩)
      (((track T (Subset.trans ty yx) st s).mpr hr).trans
        ((track U (Subset.trans uy yx) su s).mpr hs).symm)

end OMA.R_Erdos827_erdos_827_variants_n_five_le_R1_H3_R2
