import OMAReductions.R_Erdos827_erdos_827_variants_n_five_le_R1
import Mathlib

/-!
# Equal-radius blocks or a six-edge matching at a dense vertex in Erdős 827

The fixed-chord bound and radius coloring below are from @ivillar (#4882),
reusing @Genbox (#1550). The endpoint injection for the link degree is from
the earlier disjoint-fan argument. The central-reflection identity closes
a triangle in a radius link to a monochromatic four-point block. In its
absence two independent edges can be chosen while removing at most five
edges, so thirteen edges contain a matching of size six.
-/
namespace Erdos827Fan
open EuclideanGeometry Erdos827 Finset
open scoped Classical

private theorem reflected_dist (p q x : ℝ²) :
    dist (p + q - x) p = dist x q := by
  rw [dist_comm x q, dist_eq_norm, dist_eq_norm]
  congr 1
  abel

/-- Two distinct intersections of two distinct circles of the same radius are
interchanged by the central reflection that interchanges the centers. -/
theorem chord_sum {a b p q : ℝ²} {r : ℝ} (hab : a ≠ b) (hpq : p ≠ q)
    (hap : dist a p = r) (haq : dist a q = r)
    (hbp : dist b p = r) (hbq : dist b q = r) : a + b = p + q := by
  have swap (x : ℝ²) (hx : dist x p = r) (hy : dist x q = r) :
      p + q - x = a ∨ p + q - x = b := by
    apply eq_of_dist_eq_of_dist_eq_of_finrank_eq_two (by simp) hpq hab hap hbp
      ((reflected_dist p q x).trans hy) haq hbq
    rw [add_comm p q, reflected_dist, hx]
  rcases swap a hap haq with h | h
  · rcases swap b hbp hbq with k | k
    · exact (hab (by rw [← sub_right_inj (a := p+q)]; exact h.trans k.symm)).elim
    · exfalso
      apply hab
      ext i
      have H := congrArg (fun z : ℝ² => z i) h
      have K := congrArg (fun z : ℝ² => z i) k
      change p i + q i - a i = a i at H
      change p i + q i - b i = b i at K
      linarith
  · rw [sub_eq_iff_eq_add] at h
    rw [h, add_comm]

/-- A center and the vertex not on its chord determine the only candidate for the
fourth vertex when three faces have the given radius. -/
theorem third_face_forces_fourth {a b c d o p q : ℝ²} {r : ℝ}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hop : o ≠ p) (hoq : o ≠ q) (hpq : p ≠ q)
    (ao : dist a o = r) (bo : dist b o = r) (co : dist c o = r)
    (ap : dist a p = r) (bp : dist b p = r) (dp : dist d p = r)
    (aq : dist a q = r) (cq : dist c q = r) (dq : dist d q = r) :
    d = a + b + c - (o + o) ∧ OnCircleOfRadius {b,c,d} r := by
  have ab := chord_sum hab hop ao ap bo bp
  have ac := chord_sum hac hoq ao aq co cq
  have ad := chord_sum had hpq ap aq dp dq
  have P : p = a+b-o := by rw [ab]; abel
  have Q : q = a+c-o := by rw [ac]; abel
  have D : d = a+b+c-(o+o) := by
    calc d = (a+d)-a := by abel
         _ = _ := by rw [ad,P,Q]; abel
  refine ⟨D, b+c-o, ?_⟩
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx <;> subst x
  · rw [dist_comm, reflected_dist, dist_comm, co]
  · rw [dist_comm, add_comm b c, reflected_dist, dist_comm, bo]
  · rw [D, dist_eq_norm]
    convert ao using 1
    rw [dist_eq_norm]; congr 1; abel

end Erdos827Fan
namespace Erdos827Fan
open Finset
open scoped Classical

variable {α : Type*} [DecidableEq α]
private theorem closedNb_le (F : Finset (Finset α))
    (deg : ∀ x, (F.filter (x ∈ ·)).card ≤ 2)
    {e : Finset α} (he : e ∈ F) (sz : e.card = 2) : ((F.filter fun nb => ¬ Disjoint e nb)).card ≤ 3 := by
  obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp sz
  let A := F.filter (x ∈ ·)
  let B := F.filter (y ∈ ·)
  have eq : (F.filter fun nb => ¬ Disjoint {x,y} nb) = A ∪ B := by
    ext f
    constructor
    · intro h
      obtain ⟨hf,nd⟩ := mem_filter.mp h
      obtain ⟨z,hz,zf⟩ := Finset.not_disjoint_iff.mp nd
      rcases (show z = x ∨ z = y by simpa using hz) with h | h
      · exact mem_union_left _ (mem_filter.mpr ⟨hf,h ▸ zf⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨hf,h ▸ zf⟩)
    · intro h
      rcases mem_union.mp h with h | h
      · obtain ⟨hf,xf⟩ := mem_filter.mp h
        exact mem_filter.mpr ⟨hf,Finset.not_disjoint_iff.mpr ⟨x,by simp,xf⟩⟩
      · obtain ⟨hf,yf⟩ := mem_filter.mp h
        exact mem_filter.mpr ⟨hf,Finset.not_disjoint_iff.mpr ⟨y,by simp,yf⟩⟩
  have common : ({x,y} : Finset α) ∈ A ∩ B := mem_inter.mpr
    ⟨mem_filter.mpr ⟨he,by simp⟩,mem_filter.mpr ⟨he,by simp⟩⟩
  have pos := card_pos.mpr ⟨_,common⟩
  have h := card_union_add_card_inter A B
  have ha : A.card ≤ 2 := deg x
  have hb : B.card ≤ 2 := deg y
  rw [eq]; omega

/-- From at least three edges, choose two independent edges whose closed
neighborhoods together cost at most five. Two neighbors of an edge share that
edge in their closed neighborhoods. If every neighborhood has size at most
two, two disjoint edges cost at most four. -/
private theorem cheap_pair (F : Finset (Finset α)) (size : 3 ≤ F.card)
    (sz : ∀ e ∈ F, e.card = 2) (deg : ∀ x, (F.filter (x ∈ ·)).card ≤ 2)
    (free : ∀ e ∈ F, ∀ f ∈ F, ∀ g ∈ F, e ≠ f → e ≠ g → f ≠ g →
      ¬ Disjoint e f → ¬ Disjoint e g → Disjoint f g) :
    ∃ e ∈ F, ∃ f ∈ F, Disjoint e f ∧
      ((F.filter fun nb => ¬ Disjoint e nb) ∪ (F.filter fun nb => ¬ Disjoint f nb)).card ≤ 5 := by
  classical
  by_cases rich : ∃ c ∈ F, 3 ≤ ((F.filter fun nb => ¬ Disjoint c nb)).card
  · obtain ⟨c,hc,h⟩ := rich
    have h' := card_erase_add_one (a := c) (s := (F.filter fun nb => ¬ Disjoint c nb))
    have selfmem : c ∈ (F.filter fun nb => ¬ Disjoint c nb) := mem_filter.mpr ⟨hc,by
      simpa [Finset.disjoint_self_iff_empty] using (card_pos.mp (by rw [sz c hc]; decide)).ne_empty⟩
    obtain ⟨e,he,f,hf,hef⟩ := Finset.one_lt_card.mp
      (show 1 < (((F.filter fun nb => ¬ Disjoint c nb)).erase c).card by have := h' selfmem; omega)
    obtain ⟨hec,he⟩ := mem_erase.mp he
    obtain ⟨hfc,hf⟩ := mem_erase.mp hf
    obtain ⟨he,ce⟩ := mem_filter.mp he
    obtain ⟨hf,cf⟩ := mem_filter.mp hf
    refine ⟨e,he,f,hf,free c hc e he f hf hec.symm hfc.symm hef ce cf,?_⟩
    have common : c ∈ (F.filter fun nb => ¬ Disjoint e nb) ∩ (F.filter fun nb => ¬ Disjoint f nb) := mem_inter.mpr
      ⟨mem_filter.mpr ⟨hc,fun d => ce d.symm⟩,mem_filter.mpr ⟨hc,fun d => cf d.symm⟩⟩
    have pos := card_pos.mpr ⟨_,common⟩
    have h₁ := closedNb_le F deg he (sz e he)
    have h₂ := closedNb_le F deg hf (sz f hf)
    have := card_union_add_card_inter ((F.filter fun nb => ¬ Disjoint e nb)) ((F.filter fun nb => ¬ Disjoint f nb))
    omega
  · push Not at rich
    obtain ⟨e,he⟩ := card_pos.mp (show 0 < F.card by omega)
    have ne : ¬ F ⊆ (F.filter fun nb => ¬ Disjoint e nb) := fun hh => by
      have := card_le_card hh; have := rich e he; omega
    obtain ⟨f,hf,away⟩ := Finset.not_subset.mp ne
    have dis : Disjoint e f := by simpa [hf] using away
    refine ⟨e,he,f,hf,dis,?_⟩
    have := card_union_le ((F.filter fun nb => ¬ Disjoint e nb)) ((F.filter fun nb => ¬ Disjoint f nb))
    have := rich e he; have := rich f hf; omega

/-- Each two matching edges cost at most five edges, with only three edges
needed to find the final pair. -/
theorem matching_pairs (k : ℕ) (F : Finset (Finset α))
    (size : 5*k ≤ F.card+2) (sz : ∀ e ∈ F, e.card = 2)
    (deg : ∀ x, (F.filter (x ∈ ·)).card ≤ 2)
    (free : ∀ e ∈ F, ∀ f ∈ F, ∀ g ∈ F, e ≠ f → e ≠ g → f ≠ g →
      ¬ Disjoint e f → ¬ Disjoint e g → Disjoint f g) :
    ∃ M ⊆ F, M.card = 2*k ∧ (M : Set (Finset α)).Pairwise Disjoint := by
  classical
  induction k generalizing F with
  | zero => exact ⟨∅,empty_subset _,by simp,by simp⟩
  | succ k ih =>
    obtain ⟨e,he,f,hf,dis,cap⟩ := cheap_pair F (by omega) sz deg free
    let U := (F.filter fun nb => ¬ Disjoint e nb) ∪ (F.filter fun nb => ¬ Disjoint f nb)
    let G := F \ U
    have hG : G ⊆ F := sdiff_subset
    have hU : U ⊆ F := union_subset (filter_subset ..) (filter_subset ..)
    have budget : 5*k ≤ G.card+2 := by
      change 5*k ≤ (F\U).card+2
      rw [card_sdiff_of_subset hU]
      change U.card ≤ 5 at cap
      omega
    obtain ⟨M,hM,szM,ind⟩ := ih G budget (fun x hx => sz x (hG hx))
      (fun x => (card_le_card (filter_subset_filter _ hG)).trans (deg x))
      (fun _ h₁ _ h₂ _ h₃ => free _ (hG h₁) _ (hG h₂) _ (hG h₃))
    have clear (x) (hx : x ∈ M) : Disjoint e x ∧ Disjoint f x := by
      have hs := mem_sdiff.mp (hM hx)
      simpa [U, hs.1] using hs.2
    have selfne (u) (hu : u ∈ F) : ¬ Disjoint u u := by
      simpa [Finset.disjoint_self_iff_empty] using (card_pos.mp (by rw [sz u hu]; decide)).ne_empty
    have ef : e ≠ f := fun eq => selfne f hf (eq ▸ dis)
    have en : e ∉ M := fun h => selfne e he (clear e h).1
    have fn' : f ∉ M := fun h => selfne f hf (clear f h).2
    refine ⟨insert e (insert f M), insert_subset he (insert_subset hf (hM.trans hG)),?_,?_⟩
    · rw [card_insert_of_notMem (by simp [ef,en]), card_insert_of_notMem fn',szM]; omega
    · intro u hu v hv hne
      simp only [coe_insert, Set.mem_insert_iff, mem_coe] at hu hv
      rcases hu with rfl|rfl|hu <;> rcases hv with rfl|rfl|hv
      all_goals first | exact (hne rfl).elim | exact dis | exact dis.symm |
        exact (clear _ hv).1 | exact (clear _ hv).2 | exact (clear _ hu).1.symm |
        exact (clear _ hu).2.symm | exact ind hu hv hne

/-- In a link of maximum degree two, one matching edge costs at most three
edges including itself. In particular ten edges give four disjoint pairs. -/
theorem greedy_matching (k : ℕ) (F : Finset (Finset α))
    (budget : 3*k ≤ F.card+2) (sz : ∀ e ∈ F, e.card = 2)
    (deg : ∀ x, (F.filter (x ∈ ·)).card ≤ 2) :
    ∃ M ⊆ F, M.card = k ∧ (M : Set (Finset α)).Pairwise Disjoint := by
  classical
  induction k generalizing F with
  | zero => exact ⟨∅,empty_subset _,by simp,by simp⟩
  | succ k ih =>
    obtain ⟨e,he⟩ := card_pos.mp (show 0 < F.card by omega)
    let N := F.filter fun f => ¬ Disjoint e f
    let G := F \ N
    have cost : N.card ≤ 3 := closedNb_le F deg he (sz e he)
    have hG : G ⊆ F := sdiff_subset
    have enough : 3*k ≤ G.card+2 := by
      change 3*k ≤ (F\N).card+2
      rw [card_sdiff_of_subset (show N ⊆ F from filter_subset ..)]
      omega
    obtain ⟨M,sub,ms,ind⟩ := ih G enough (fun u hu => sz u (hG hu))
      (fun x => (card_le_card (filter_subset_filter _ hG)).trans (deg x))
    have away (u) (hu : u ∈ M) : Disjoint e u := by
      have h := mem_sdiff.mp (sub hu)
      simpa [N,h.1] using h.2
    have en : e ∉ M := fun h => (card_pos.mp (show 0 < e.card by rw [sz e he]; decide)).ne_empty
      ((disjoint_self_iff_empty e).mp (away e h))
    refine ⟨insert e M,insert_subset he (sub.trans hG),by simp [en,ms],?_⟩
    intro u hu v hv hne
    simp only [coe_insert, Set.mem_insert_iff, mem_coe] at hu hv
    rcases hu with rfl|hu <;> rcases hv with rfl|hv
    all_goals first | exact (hne rfl).elim | exact away _ hv | exact (away _ hu).symm | exact ind hu hv hne

end Erdos827Fan
namespace Erdos827Fan
open EuclideanGeometry Erdos827 Finset
open scoped Classical

private theorem intersecting_triple {α : Type*} [DecidableEq α] {F : Finset (Finset α)}
    (sz : ∀ e ∈ F, e.card = 2) (deg : ∀ x, (F.filter (x ∈ ·)).card ≤ 2)
    {e f g : Finset α} (he : e ∈ F) (hf : f ∈ F) (hg : g ∈ F)
    (ef : e ≠ f) (eg : e ≠ g) (fg : f ≠ g)
    (i : ¬ Disjoint e f) (j : ¬ Disjoint e g) (k : ¬ Disjoint f g) :
    ∃ x y z : α, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ {x,y} ∈ F ∧ {x,z} ∈ F ∧ {y,z} ∈ F := by
  obtain ⟨x,xe,xf⟩ := Finset.not_disjoint_iff.mp i
  obtain ⟨y,ye,yg⟩ := Finset.not_disjoint_iff.mp j
  obtain ⟨z,zf,zg⟩ := Finset.not_disjoint_iff.mp k
  have no (t : α) (te : t ∈ e) (tf : t ∈ f) (tg : t ∈ g) : False := by
    have h : 2 < (F.filter (t ∈ ·)).card := Finset.two_lt_card_iff.mpr
      ⟨e,f,g,mem_filter.mpr ⟨he,te⟩,mem_filter.mpr ⟨hf,tf⟩,mem_filter.mpr ⟨hg,tg⟩,ef,eg,fg⟩
    exact (Nat.not_lt_of_ge (deg t)) h
  have xy : x ≠ y := fun h => no y ye (h ▸ xf) yg
  have xz : x ≠ z := fun h => no z (h ▸ xe) zf zg
  have yz : y ≠ z := fun h => no z (h ▸ ye) zf zg
  have identify {u v : α} {E : Finset α} (ne : u ≠ v) (uE : u ∈ E) (vE : v ∈ E)
      (hE : E ∈ F) : ({u,v} : Finset α) ∈ F := by
    have eq : ({u,v} : Finset α) = E := eq_of_subset_of_card_le
      (insert_subset uE (singleton_subset_iff.mpr vE)) (by rw [card_pair ne, sz E hE])
    exact eq.symm ▸ hE
  exact ⟨x,y,z,xy,xz,yz,identify xy xe ye he,identify xz xf zf hf,identify yz yg zg hg⟩

private theorem four_not_on_one {X : Finset ℝ²} (gp : InGeneralPosition (X : Set ℝ²))
    {a b c d : ℝ²} (m : ({a,b,c,d} : Finset ℝ²) ⊆ X)
    (ab : a ≠ b) (ac : a ≠ c) (ad : a ≠ d) (bc : b ≠ c) (bd : b ≠ d) (cd : c ≠ d)
    (o : ℝ²) (r : ℝ) (ao : dist a o = r) (bo : dist b o = r)
    (co : dist c o = r) (do' : dist d o = r) : False := by
  apply gp.2 (({a,b,c,d} : Finset ℝ²) : Set ℝ²) m
  · simp [ab,ac,ad,bc,bd,cd]
  · refine ⟨o,r,?_⟩
    intro x hx
    simp only [mem_coe, mem_insert, mem_singleton] at hx
    rcases hx with rfl|rfl|rfl|rfl <;> assumption

/-- A triangle in the link completes to four equal-radius faces. -/
theorem complete_block {X : Finset ℝ²} (gp : InGeneralPosition (X : Set ℝ²))
    {a b c d : ℝ²} (m : ({a,b,c,d} : Finset ℝ²) ⊆ X)
    (ab : a ≠ b) (ac : a ≠ c) (ad : a ≠ d) (bc : b ≠ c) (bd : b ≠ d) (cd : c ≠ d)
    {r : ℝ} (abc : OnCircleOfRadius {a,b,c} r)
    (abd : OnCircleOfRadius {a,b,d} r) (acd : OnCircleOfRadius {a,c,d} r) :
    OnCircleOfRadius {b,c,d} r := by
  obtain ⟨o,ho⟩ := abc
  obtain ⟨p,hp⟩ := abd
  obtain ⟨q,hq⟩ := acd
  have ao := ho a (by simp); have bo := ho b (by simp); have co := ho c (by simp)
  have ap := hp a (by simp); have bp := hp b (by simp); have dp := hp d (by simp)
  have aq := hq a (by simp); have cq := hq c (by simp); have dq := hq d (by simp)
  have distinct := four_not_on_one gp m ab ac ad bc bd cd
  have op : o ≠ p := fun h => distinct o r ao bo co (h ▸ dp)
  have oq : o ≠ q := fun h => distinct o r ao bo co (h ▸ dq)
  have pq : p ≠ q := fun h => distinct p r ap bp (h ▸ cq) dp
  exact (third_face_forces_fourth ab ac ad op oq pq ao bo co ap bp dp aq cq dq).2

end Erdos827Fan
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

namespace Erdos827Fan
open EuclideanGeometry Erdos827 Finset
open scoped Classical
private theorem fan_degree {α : Type*} [DecidableEq α] (X : Finset α) (c : Finset α → ℝ)
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


end Erdos827Fan
namespace OMA.R_Erdos827_erdos_827_variants_n_five_le_R1_H3_R1
open EuclideanGeometry Erdos827 Finset Erdos827Fan
open scoped Classical

private theorem saturated {X K : Finset ℝ²} (gp : InGeneralPosition (X : Set ℝ²))
    (KX : K ⊆ X) (cardK : K.card = 4) {r : ℝ}
    (faces : ∀ T ⊆ K, T.card = 3 → OnCircleOfRadius T r)
    (B : Finset ℝ²) (BK : B ⊆ K) (cardB : B.card = 2) (z : ℝ²) (hz : z ∈ X \ K) :
    ¬ OnCircleOfRadius (insert z B) r := by
  intro zrad
  obtain ⟨c,track,cap⟩ := radius_coloring X gp
  have gap : 1 < (K \ B).card := by rw [card_sdiff_of_subset BK, cardK, cardB]; decide
  obtain ⟨u,hu,v,hv,uv⟩ := one_lt_card.mp gap
  obtain ⟨uK,un⟩ := mem_sdiff.mp hu
  obtain ⟨vK,vn⟩ := mem_sdiff.mp hv
  obtain ⟨zX,zn⟩ := mem_sdiff.mp hz
  have Bx := BK.trans KX
  let S := (X \ B).filter fun w => c (insert w B) = r
  have en (w : ℝ²) (hw : w ∈ X) (hn : w ∉ B) (hr : OnCircleOfRadius (insert w B) r) : w ∈ S :=
    mem_filter.mpr ⟨mem_sdiff.mpr ⟨hw,hn⟩,(track _ (insert_subset hw Bx) (by simp [hn,cardB]) r).mpr hr⟩
  have uS := en u (KX uK) un (faces _ (insert_subset uK BK) (by simp [un,cardB]))
  have vS := en v (KX vK) vn (faces _ (insert_subset vK BK) (by simp [vn,cardB]))
  have zS := en z zX (fun h => zn (BK h)) zrad
  have too_many : 2 < S.card := two_lt_card_iff.mpr
    ⟨u,v,z,uS,vS,zS,uv,fun h => zn (h ▸ uK),fun h => zn (h ▸ vK)⟩
  exact (Nat.not_lt_of_ge (cap B Bx cardB r)) too_many

private theorem external_matching {X K : Finset ℝ²} {a : ℝ²} {r : ℝ}
    {F : Finset (Finset ℝ²)} (rich : 13 ≤ F.card)
    (members : ∀ {B}, B ∈ F → B ⊆ X.erase a ∧ B.card = 2)
    (radii : ∀ B ∈ F, OnCircleOfRadius (insert a B) r)
    (deg : ∀ x, (F.filter (x ∈ ·)).card ≤ 2) (aK : a ∈ K) (cardK : K.card = 4)
    (sat : ∀ B ⊆ K, B.card = 2 → ∀ z ∈ X \ K, ¬ OnCircleOfRadius (insert z B) r) :
    ∃ M ⊆ F, M.card = 4 ∧ (M : Set (Finset ℝ²)).Pairwise Disjoint ∧
      ∀ B ∈ M, Disjoint B K := by
  classical
  let innerPairs := (K.erase a).powersetCard 2
  have three : innerPairs.card = 3 := by
    have remove := card_erase_add_one aK
    have h : (K.erase a).card = 3 := by omega
    change ((K.erase a).powersetCard 2).card = 3
    rw [card_powersetCard,h]; decide
  let G := F \ innerPairs
  have enough : 3*4 ≤ G.card+2 := by
    have loss := card_sdiff_add_card_inter F innerPairs
    have cap' : (F ∩ innerPairs).card ≤ innerPairs.card := card_le_card inter_subset_right
    change 3*4 ≤ (F \ innerPairs).card+2
    omega
  have hG : G ⊆ F := sdiff_subset
  obtain ⟨M,subM,ms,ind⟩ := greedy_matching 4 G enough (fun E h => (members (hG h)).2)
    (fun x => (card_le_card (filter_subset_filter _ hG)).trans (deg x))
  have outside (B : Finset ℝ²) (hB : B ∈ M) : Disjoint B K := by
    obtain ⟨hF,hn⟩ := mem_sdiff.mp (subM hB)
    obtain ⟨BX,cardB⟩ := members hF
    obtain ⟨u,v,uv,hpair⟩ := card_eq_two.mp cardB
    subst B
    have un := (mem_erase.mp (BX (show u ∈ ({u,v} : Finset ℝ²) by simp))).1
    have vn := (mem_erase.mp (BX (show v ∈ ({u,v} : Finset ℝ²) by simp))).1
    have uX := (mem_erase.mp (BX (show u ∈ ({u,v} : Finset ℝ²) by simp))).2
    have vX := (mem_erase.mp (BX (show v ∈ ({u,v} : Finset ℝ²) by simp))).2
    have rad := radii _ hF
    have both (hu : u ∈ K) (hv : v ∈ K) : False := hn (mem_powersetCard.mpr
      ⟨insert_subset (mem_erase.mpr ⟨un,hu⟩) (singleton_subset_iff.mpr (mem_erase.mpr ⟨vn,hv⟩)),cardB⟩)
    have ban (i j : ℝ²) (ine : i ≠ a) (iK : i ∈ K) (jX : j ∈ X) (jK : j ∉ K)
        (rad' : OnCircleOfRadius (insert j {a,i}) r) : False :=
      sat _ (insert_subset aK (singleton_subset_iff.mpr iK)) (card_pair ine.symm) j (mem_sdiff.mpr ⟨jX,jK⟩) rad'
    have noU : u ∉ K := fun hu => ban u v un hu vX (both hu)
      (by
        have eq : insert v ({a,u} : Finset ℝ²) = insert a {u,v} := by
          ext t; simp [or_comm,or_left_comm]
        rw [eq]; exact rad)
    have noV : v ∉ K := fun hv => ban v u vn hv uX noU
      (by
        have eq : insert u ({a,v} : Finset ℝ²) = insert a {u,v} := insert_comm ..
        rw [eq]; exact rad)
    exact Finset.disjoint_left.mpr fun t ht => by
      rcases (show t = u ∨ t = v by simpa using ht) with h|h
      · exact h ▸ noU
      · exact h ▸ noV
  exact ⟨M,subM.trans hG,ms,ind,outside⟩

/-- A four-point block through the dense vertex. All four of its faces have
radius r, and no external vertex completes any of its six edges at radius r. Four disjoint link edges lie outside it. -/
def H1 : Prop := ∀ (X : Finset ℝ²), X.card = 37 → InGeneralPosition (X : Set ℝ²) →
  ∀ a ∈ X, ∀ r, 13 ≤ (((X.erase a).powersetCard 2).filter
    (fun B => OnCircleOfRadius (insert a B) r)).card →
  ∀ K ⊆ X, a ∈ K → K.card = 4 →
    (∀ T ⊆ K, T.card = 3 → OnCircleOfRadius T r) →
    (∀ B ⊆ K, B.card = 2 → ∀ z ∈ X \ K, ¬ OnCircleOfRadius (insert z B) r) →
  ∀ M ⊆ (((X.erase a).powersetCard 2).filter (fun B => OnCircleOfRadius (insert a B) r)),
    M.card = 4 → (M : Set (Finset ℝ²)).Pairwise Disjoint → (∀ B ∈ M, Disjoint B K) →
  ∃ Y ⊆ X, Y.card = 5 ∧ HasDistinctCircumradii Y

/-- A triangle-free radius link with six disjoint edges, marking twelve
distinct points in addition to the dense vertex. -/
def H2 : Prop := ∀ (X : Finset ℝ²), X.card = 37 → InGeneralPosition (X : Set ℝ²) →
  ∀ a ∈ X, ∀ r : ℝ,
  let F := ((X.erase a).powersetCard 2).filter (fun B => OnCircleOfRadius (insert a B) r)
  13 ≤ F.card →
  (∀ b c d : ℝ², b ≠ c → b ≠ d → c ≠ d → {b,c} ∈ F → {b,d} ∈ F → {c,d} ∉ F) →
  ∀ M ⊆ F, M.card = 6 → (M : Set (Finset ℝ²)).Pairwise Disjoint →
  ∃ Y ⊆ X, Y.card = 5 ∧ HasDistinctCircumradii Y

theorem main : H1 → H2 → OMA.R_Erdos827_erdos_827_variants_n_five_le_R1.H3 := by
  intro block matching X size gp a ha r rich
  classical
  let F := ((X.erase a).powersetCard 2).filter fun B => OnCircleOfRadius (insert a B) r
  change 13 ≤ F.card at rich
  have members {B} (h : B ∈ F) : B ⊆ X.erase a ∧ B.card = 2 :=
    mem_powersetCard.mp (mem_filter.mp h).1
  obtain ⟨c,track,cap⟩ := radius_coloring X gp
  have colors : F = ((X.erase a).powersetCard 2).filter (fun B => c (insert a B) = r) := by
    apply filter_congr
    intro B h
    obtain ⟨sub,sz⟩ := mem_powersetCard.mp h
    have an : a ∉ B := fun h => notMem_erase a X (sub h)
    exact (track _ (insert_subset ha (sub.trans (erase_subset ..))) (by simp [an,sz]) r).symm
  have deg (x : ℝ²) : (F.filter (x ∈ ·)).card ≤ 2 := by
    rw [colors]; exact Erdos827Fan.fan_degree X c cap ha r x
  by_cases tri : ∃ b c d : ℝ², b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      {b,c} ∈ F ∧ {b,d} ∈ F ∧ {c,d} ∈ F
  · obtain ⟨b,c,d,bc,bd,cd,e,f,g⟩ := tri
    have bm := mem_erase.mp ((members e).1 (show b ∈ ({b,c} : Finset ℝ²) by simp))
    have cm := mem_erase.mp ((members e).1 (show c ∈ ({b,c} : Finset ℝ²) by simp))
    have dm := mem_erase.mp ((members f).1 (show d ∈ ({b,d} : Finset ℝ²) by simp))
    let K : Finset ℝ² := {a,b,c,d}
    have KX : K ⊆ X := insert_subset ha (insert_subset bm.2 (insert_subset cm.2 (singleton_subset_iff.mpr dm.2)))
    have cardK : K.card = 4 := by simp [K,bm.1.symm,cm.1.symm,dm.1.symm,bc,bd,cd]
    have abc := (mem_filter.mp e).2
    have abd := (mem_filter.mp f).2
    have acd := (mem_filter.mp g).2
    have bcd := complete_block gp KX bm.1.symm cm.1.symm dm.1.symm bc bd cd abc abd acd
    have faces (T : Finset ℝ²) (hT : T ⊆ K) (sT : T.card = 3) : OnCircleOfRadius T r := by
      have gap : (K \ T).card = 1 := by rw [card_sdiff_of_subset hT,cardK,sT]
      obtain ⟨x,hx⟩ := card_eq_one.mp gap
      have xT := mem_sdiff.mp (show x ∈ K \ T by rw [hx]; simp)
      have id : T = K.erase x := by
        ext y
        constructor
        · intro hy; exact mem_erase.mpr ⟨fun h => xT.2 (h ▸ hy), hT hy⟩
        · intro hy
          obtain ⟨ne,yK⟩ := mem_erase.mp hy
          by_contra yn
          have bad : y ∈ K \ T := mem_sdiff.mpr ⟨yK,yn⟩
          rw [hx] at bad
          exact ne (mem_singleton.mp bad)
      rw [id]
      have opt : x = a ∨ x = b ∨ x = c ∨ x = d := by simpa [K] using xT.1
      rcases opt with hk|hk|hk|hk <;> subst x
      · simpa only [K,Finset.erase_insert (show a ∉ ({b,c,d} : Finset ℝ²) by
          simp [bm.1.symm,cm.1.symm,dm.1.symm])] using bcd
      · simpa only [K,Finset.erase_insert_of_ne bm.1.symm,Finset.erase_insert (show b ∉ ({c,d} : Finset ℝ²) by
          simp [bc,bd])] using acd
      · simpa only [K,Finset.erase_insert_of_ne cm.1.symm,Finset.erase_insert_of_ne bc,
          Finset.erase_insert (show c ∉ ({d} : Finset ℝ²) by simp [cd])] using abd
      · simpa only [K,Finset.erase_insert_of_ne dm.1.symm,Finset.erase_insert_of_ne bd,
          Finset.erase_insert_of_ne cd,Finset.erase_singleton,Finset.insert_empty] using abc
    have aK : a ∈ K := by simp [K]
    have sat := saturated gp KX cardK faces
    obtain ⟨M,subM,ms,ind,outside⟩ := external_matching rich
      (fun h => members h) (fun _ h => (mem_filter.mp h).2) deg aK cardK sat
    exact block X size gp a ha r rich K KX aK cardK faces sat M subM ms ind outside
  · have free b c d (bc : b ≠ c) (bd : b ≠ d) (cd : c ≠ d) (e : {b,c} ∈ F) (f : {b,d} ∈ F)
        (g : {c,d} ∈ F) := tri ⟨b,c,d,bc,bd,cd,e,f,g⟩
    obtain ⟨M,sub,sM,ind⟩ := matching_pairs 3 F (by omega) (fun E h => (members h).2) deg
      (by
        intro e he f hf g hg ef eg fg i j
        by_contra k
        exact tri (intersecting_triple (fun E h => (members h).2) deg he hf hg ef eg fg i j k))
    exact matching X size gp a ha r rich free M sub sM ind
end OMA.R_Erdos827_erdos_827_variants_n_five_le_R1_H3_R1
