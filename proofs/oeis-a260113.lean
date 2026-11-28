import OMAStatements.S_oeis_a260113
import Mathlib

/-!
# Queens attacking at most one other queen

The upper bound counts occupied rows and columns. For the lower bound we use
Alexander Healy's product-and-paste construction and his finite coordinate
tables from appendices A and C of *Queens that attack at most one other, or
exactly one other* (August 2026), https://www.alexhealy.net/papers/queens.pdf.
The product uses the toroidal placement (i, 2i mod b). The finite placement
checks below are all computed by the Lean kernel.
-/

namespace OMA.Queens
open OMA.S_oeis_a260113 Finset

def line {α β : Type} [DecidableEq β] (s : Finset α) (f : α → β) (b : β) :=
  s.filter (fun x => f x = b)

lemma score_bound {α β : Type} [DecidableEq β] [Fintype β] (s : Finset α) (f : α → β) :
    (∑ x ∈ s, (3 - (line s f (f x)).card)) ≤ 2 * Fintype.card β := by
  classical
  calc
    _ = ∑ b : β, ∑ x ∈ line s f b, (3 - (line s f (f x)).card) := by
      symm
      exact sum_fiberwise_of_maps_to (fun x _ => mem_univ (f x)) _
    _ ≤ ∑ _b : β, 2 := by
      apply sum_le_sum
      intro b _
      calc
        _ = ∑ _x ∈ line s f b, (3 - (line s f b).card) := by
          exact sum_congr rfl fun x hx => by rw [(mem_filter.mp hx).2]
        _ = (line s f b).card * (3 - (line s f b).card) := by simp
        _ ≤ 2 := by
          generalize (line s f b).card = k
          rcases le_or_gt k 2 with h | h
          · interval_cases k <;> decide
          · simp [show 3-k=0 by omega]
    _ = _ := by simp [mul_comm]

lemma line_sizes {n : ℕ} {s : Finset (Fin n × Fin n)} (hs : valid s) {p} (hp : p ∈ s) :
    (line s Prod.fst p.1).card + (line s Prod.snd p.2).card ≤ 3 := by
  classical
  let neighbors := s.filter (attacks p)
  have hn : neighbors.card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    obtain ⟨has, hpa⟩ := mem_filter.mp ha
    obtain ⟨hbs, hpb⟩ := mem_filter.mp hb
    exact hs p hp a has b hbs hpa hpb
  let row := line s Prod.fst p.1
  let col := line s Prod.snd p.2
  have hu : row ∪ col ⊆ insert p neighbors := by
    intro q hq
    by_cases he : p = q
    · simp [he]
    apply mem_insert_of_mem
    rcases mem_union.mp hq with hr | hc
    · obtain ⟨hq,hrow⟩ := mem_filter.mp hr
      exact mem_filter.mpr ⟨hq,he,Or.inl hrow.symm⟩
    · obtain ⟨hq,hcol⟩ := mem_filter.mp hc
      exact mem_filter.mpr ⟨hq,he,Or.inr (Or.inl hcol.symm)⟩
  have hi : row ∩ col ⊆ {p} := by
    intro q hq
    obtain ⟨hr,hc⟩ := mem_inter.mp hq
    exact mem_singleton.mpr (Prod.ext (mem_filter.mp hr).2 (mem_filter.mp hc).2)
  have h1 := card_le_card hu
  have h2 := card_le_card hi
  have h3 := card_insert_le p neighbors
  have h4 := card_union_add_card_inter row col
  change row.card + col.card ≤ 3
  simp only [card_singleton] at h2
  omega

lemma upper {n : ℕ} {s : Finset (Fin n × Fin n)} (hs : valid s) :
    s.card ≤ 4*n/3 := by
  have h : ∑ _p ∈ s, (3 : ℕ) ≤ ∑ p ∈ s, ((3 - (line s Prod.fst p.1).card) +
      (3 - (line s Prod.snd p.2).card)) :=
    sum_le_sum fun p hp => by have := line_sizes hs hp; omega
  simp only [sum_const, nsmul_eq_mul, Nat.cast_id, sum_add_distrib] at h
  have hr := score_bound s Prod.fst
  have hc := score_bound s Prod.snd
  simp only [Fintype.card_fin] at hr hc
  omega

end OMA.Queens

namespace OMA.QueenConstruction
open Finset
abbrev Cell := ℕ × ℕ

def aligned (p q : Cell) : Prop :=
  p.1 = q.1 ∨ p.2 = q.2 ∨ p.1 + q.2 = q.1 + p.2 ∨ p.1 + p.2 = q.1 + q.2

instance (p q : Cell) : Decidable (aligned p q) := by unfold aligned; infer_instance

def legal (s : Finset Cell) : Prop :=
  ∀ p ∈ s, ∀ q ∈ s, ∀ r ∈ s, p ≠ q → p ≠ r → aligned p q → aligned p r → q = r

def fits (s : Finset Cell) (n : ℕ) : Prop := ∀ p ∈ s, p.1 < n ∧ p.2 < n

def reaches (n : ℕ) : Prop := ∃ s, legal s ∧ fits s n ∧ s.card = 4*n/3

lemma realize {n} (h : reaches n) :
    ∃ s : Finset (Fin n × Fin n), OMA.S_oeis_a260113.valid s ∧ s.card = 4*n/3 := by
  obtain ⟨s,hl,hf,hc⟩ := h
  let f (p : { x // x ∈ s }) : Fin n × Fin n :=
    (⟨p.val.1,(hf p p.property).1⟩, ⟨p.val.2,(hf p p.property).2⟩)
  have hi : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact Prod.ext (congrArg (fun p : Fin n × Fin n => p.1.val) hab)
      (congrArg (fun p : Fin n × Fin n => p.2.val) hab)
  let e : { x // x ∈ s } ↪ Fin n × Fin n := ⟨f,hi⟩
  refine ⟨s.attach.map e, ?_, by simpa using hc⟩
  have att {a b : { x // x ∈ s }} (h : OMA.S_oeis_a260113.attacks (e a) (e b)) :
      a.val ≠ b.val ∧ aligned a.val b.val := by
    refine ⟨fun he => h.1 (congrArg e (Subtype.ext he)), ?_⟩
    rcases h.2 with hr|hc|hd
    · exact Or.inl (congrArg Fin.val hr)
    · exact Or.inr (Or.inl (congrArg Fin.val hc))
    · change Nat.dist a.val.1 b.val.1 = Nat.dist a.val.2 b.val.2 at hd
      simp only [Nat.dist] at hd
      unfold aligned
      omega
  intro p hp q hq r hr h1 h2
  obtain ⟨a,_,rfl⟩ := mem_map.mp hp
  obtain ⟨b,_,rfl⟩ := mem_map.mp hq
  obtain ⟨c,_,rfl⟩ := mem_map.mp hr
  have ab := att h1
  have ac := att h2
  exact congrArg e (Subtype.ext (hl a a.property b b.property c c.property ab.1 ac.1 ab.2 ac.2))

def shift (k : ℕ) (p : Cell) : Cell := (k+p.1,k+p.2)

lemma shift_inj (k : ℕ) : Function.Injective (shift k) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  simpa [shift] using h

lemma shift_aligned {k p q} : aligned (shift k p) (shift k q) ↔ aligned p q := by
  simp only [aligned,shift]
  omega

lemma aligned_symm {p q} : aligned p q → aligned q p := by unfold aligned; omega

lemma legal_union {s t : Finset Cell} (hs : legal s) (ht : legal t)
    (hc : ∀ p ∈ s, ∀ q ∈ t, ¬ aligned p q) : legal (s ∪ t) := by
  intro p hp q hq r hr hn hm h1 h2
  rcases mem_union.mp hp with hp|hp
  · exact hs p hp q ((mem_union.mp hq).resolve_right (fun h => hc p hp q h h1))
      r ((mem_union.mp hr).resolve_right (fun h => hc p hp r h h2)) hn hm h1 h2
  · exact ht p hp q ((mem_union.mp hq).resolve_left (fun h => hc q h p hp (aligned_symm h1)))
      r ((mem_union.mp hr).resolve_left (fun h => hc r h p hp (aligned_symm h2))) hn hm h1 h2

lemma legal_image {s : Finset Cell} (hs : legal s) (f : Cell → Cell)
    (ha : ∀ p q, aligned (f p) (f q) → aligned p q) : legal (s.image f) := by
  rintro p hp q hq r hr hn hm h1 h2
  obtain ⟨a,ha',rfl⟩ := mem_image.mp hp
  obtain ⟨b,hb',rfl⟩ := mem_image.mp hq
  obtain ⟨c,hc',rfl⟩ := mem_image.mp hr
  exact congrArg f (hs a ha' b hb' c hc' (fun h => hn (congrArg f h))
    (fun h => hm (congrArg f h)) (ha _ _ h1) (ha _ _ h2))

end OMA.QueenConstruction

namespace OMA.QueenConstruction
open Finset

def band (s : Finset Cell) (w : ℕ) : Prop :=
  ∀ p ∈ s, p.1 ≤ p.2+w ∧ p.2 ≤ p.1+w

def gap (s : Finset Cell) (d : ℕ) : Prop :=
  ∀ p ∈ s, p.1+d ≤ p.2 ∨ p.2+d ≤ p.1

def paste (b : ℕ) (s t : Finset Cell) := s ∪ t.image (shift b)

lemma paste_spec {s t b m w} (hs : legal s) (ht : legal t)
    (fs : fits s b) (ft : fits t m) (gs : gap s (w+1)) (bt : band t w) :
    legal (paste b s t) ∧ fits (paste b s t) (b+m) ∧
    (paste b s t).card = s.card + t.card := by
  have cross : ∀ p ∈ s, ∀ q ∈ t.image (shift b), ¬ aligned p q := by
    intro p hp q hq
    obtain ⟨q,htq,rfl⟩ := mem_image.mp hq
    have := fs p hp
    have := gs p hp
    have := bt q htq
    simp only [aligned,shift]
    omega
  refine ⟨legal_union hs (legal_image ht _ fun _ _ => shift_aligned.mp) cross, ?_, ?_⟩
  · intro p hp
    rcases mem_union.mp hp with h|h
    · have := fs p h
      omega
    · obtain ⟨q,hq,rfl⟩ := mem_image.mp h
      have := ft q hq
      simp only [shift]
      omega
  · have hd : Disjoint s (t.image (shift b)) := by
      apply disjoint_left.mpr
      intro p hp hq
      exact cross p hp p hq (Or.inl rfl)
    rw [paste, card_union_of_disjoint hd, card_image_of_injective _ (shift_inj _)]

def expand (s : ℕ) (p : Cell) (i : ℕ) : Cell :=
  (s*p.1+i, s*p.2+(2*i)%s)

lemma expand_inj {s i j p q} (hi : i < s) (hj : j < s)
    (h : expand s p i = expand s q j) : p = q ∧ i = j := by
  obtain ⟨h1,h2⟩ := Prod.mk.inj h
  have hij : i = j := by
    have := congrArg (· % s) h1
    simpa [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using this
  subst j
  refine ⟨Prod.ext ?_ ?_,rfl⟩
  · exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < s) (Nat.add_right_cancel h1)
  · exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < s) (Nat.add_right_cancel h2)

lemma expand_aligned_same {s p q i} (hs : 0 < s) :
    aligned (expand s p i) (expand s q i) → aligned p q := by
  simp only [aligned, expand]
  intro h
  rcases h with h|h|h|h
  · exact Or.inl (Nat.eq_of_mul_eq_mul_left hs (Nat.add_right_cancel h))
  · exact Or.inr (Or.inl (Nat.eq_of_mul_eq_mul_left hs (Nat.add_right_cancel h)))
  · right; right; left
    apply Nat.eq_of_mul_eq_mul_left hs
    rw [Nat.mul_add, Nat.mul_add]
    omega
  · right; right; right
    apply Nat.eq_of_mul_eq_mul_left hs
    rw [Nat.mul_add, Nat.mul_add]
    omega

lemma expand_index {s p q i j} (hi : i < s) (hj : j < s)
    (h2 : s.gcd 2 = 1) (h3 : s.gcd 3 = 1)
    (h : aligned (expand s p i) (expand s q j)) : i = j := by
  have row (a k : ℕ) : s*a+k ≡ k [MOD s] := by simp [Nat.ModEq]
  have col (a k : ℕ) : s*a+ (2*k)%s ≡ 2*k [MOD s] := by simp [Nat.ModEq]
  apply Nat.ModEq.eq_of_lt_of_lt _ hi hj
  rcases h with hr|hc|hd|ha
  · exact (row p.1 i).symm.trans ((congrArg (· % s) hr : Nat.ModEq s _ _).trans (row q.1 j))
  · apply Nat.ModEq.cancel_left_of_coprime h2
    exact (col p.2 i).symm.trans ((congrArg (· % s) hc : Nat.ModEq s _ _).trans (col q.2 j))
  · have he : i+2*j ≡ j+2*i [MOD s] := ((row p.1 i).add (col q.2 j)).symm.trans
        ((congrArg (· % s) hd : Nat.ModEq s _ _).trans ((row q.1 j).add (col p.2 i)))
    have he' : (i+j)+j ≡ (i+j)+i [MOD s] := by convert he using 1 <;> omega
    exact (Nat.ModEq.add_left_cancel' _ he').symm
  · apply Nat.ModEq.cancel_left_of_coprime h3
    have he : i+2*i ≡ j+2*j [MOD s] := ((row p.1 i).add (col p.2 i)).symm.trans
        ((congrArg (· % s) ha : Nat.ModEq s _ _).trans ((row q.1 j).add (col q.2 j)))
    convert he using 1 <;> omega

end OMA.QueenConstruction

namespace OMA.QueenConstruction
open Finset

def product (s : Finset Cell) (b : ℕ) : Finset Cell :=
  (s ×ˢ range b).image (fun x => expand b x.1 x.2)

lemma product_spec {s n b} (hl : legal s) (hf : fits s n) (hb : 0 < b)
    (h2 : b.gcd 2 = 1) (h3 : b.gcd 3 = 1) :
    legal (product s b) ∧ fits (product s b) (b*n) ∧ (product s b).card = s.card*b := by
  refine ⟨?_,?_,?_⟩
  · intro p hp q hq r hr hn hm h1 h2'
    obtain ⟨⟨a,i⟩,hai,rfl⟩ := mem_image.mp hp
    obtain ⟨⟨c,j⟩,hcj,rfl⟩ := mem_image.mp hq
    obtain ⟨⟨d,k⟩,hdk,rfl⟩ := mem_image.mp hr
    simp only [mem_product,mem_range] at hai hcj hdk
    obtain rfl := expand_index hai.2 hcj.2 h2 h3 h1
    obtain rfl := expand_index hai.2 hdk.2 h2 h3 h2'
    have hcd := hl _ hai.1 _ hcj.1 _ hdk.1 (fun he => hn (he ▸ rfl)) (fun he => hm (he ▸ rfl))
      (expand_aligned_same hb h1) (expand_aligned_same hb h2')
    exact congrArg (fun x => expand b x i) hcd
  · intro p hp
    obtain ⟨⟨a,i⟩,hai,rfl⟩ := mem_image.mp hp
    simp only [mem_product,mem_range] at hai
    obtain ⟨hx,hy⟩ := hf a hai.1
    have row := Nat.mul_le_mul_left b (show a.1 + 1 ≤ n from hx)
    have col := Nat.mul_le_mul_left b (show a.2 + 1 ≤ n from hy)
    have hi' := Nat.mod_lt (2*i) hb
    simp only [Nat.mul_add, Nat.mul_one] at row col
    simp only [expand]
    omega
  · rw [product, card_image_of_injOn, card_product, card_range]
    rintro ⟨a,i⟩ hai ⟨c,j⟩ hcj h
    simp only [mem_coe,mem_product,mem_range] at hai hcj
    obtain ⟨h1,h2'⟩ := expand_inj hai.2 hcj.2 h
    exact Prod.ext h1 h2'

lemma fine_offset {i b : ℕ} (hi : i < b) :
    (2*i)%b ≤ i+b/2 ∧ i ≤ (2*i)%b+b/2 := by
  by_cases h : 2*i < b
  · rw [Nat.mod_eq_of_lt h]
    omega
  · rw [Nat.mod_eq_sub_mod (by omega : b ≤ 2*i), Nat.mod_eq_of_lt (by omega : 2*i-b < b)]
    omega

lemma product_gap {s d b} (hg : gap s d) : gap (product s b) (b*d-b/2) := by
  intro p hp
  obtain ⟨⟨a,i⟩,hai,rfl⟩ := mem_image.mp hp
  simp only [mem_product,mem_range] at hai
  have := fine_offset hai.2
  simp only [expand]
  by_cases hbd : b/2 ≤ b*d
  swap
  · rw [Nat.sub_eq_zero_of_le (by omega : b*d ≤ b/2)]
    simpa using le_total (b*a.1+i) (b*a.2+2*i%b)
  rcases hg a hai.1 with h|h
  · left; have hh := Nat.mul_le_mul_left b h; rw [Nat.mul_add] at hh; omega
  · right; have hh := Nat.mul_le_mul_left b h; rw [Nat.mul_add] at hh; omega

end OMA.QueenConstruction

namespace OMA.QueenConstruction
open Finset

/-- A board of the stated size and cardinality with upper and lower diagonal bounds. -/
def config (n k w d : ℕ) : Prop :=
  ∃ s, legal s ∧ fits s n ∧ s.card = k ∧ band s w ∧ gap s d

theorem config_product {n k w d b} (hc : config n k w d) (hb : 0 < b := by decide)
    (h2 : b.gcd 2 = 1 := by decide) (h3 : b.gcd 3 = 1 := by decide) :
    config (b*n) (k*b) (b*w+b/2) (b*d-b/2) := by
  obtain ⟨s,hl,hf,hc,hw,hd⟩ := hc
  obtain ⟨hl',hf',hc'⟩ := product_spec hl hf hb h2 h3
  refine ⟨product s b,hl',hf',hc'.trans (congrArg (· * b) hc),?_,product_gap hd⟩
  intro p hp
  obtain ⟨⟨a,i⟩,hai,rfl⟩ := mem_image.mp hp
  simp only [mem_product,mem_range] at hai
  obtain ⟨h1,h2'⟩ := hw a hai.1
  have h1' := Nat.mul_le_mul_left b h1
  have h2'' := Nat.mul_le_mul_left b h2'
  rw [Nat.mul_add] at h1' h2''
  have := fine_offset hai.2
  simp only [expand]
  omega

theorem config_paste {n k w d m l v e} (hs : config n k w d) (ht : config m l v e)
    (h : v < d := by decide) : config (n+m) (k+l) (max w v) (min d e) := by
  obtain ⟨s,hl,hf,hc,hw,hd⟩ := hs
  obtain ⟨t,tl,tf,tc,tw,td⟩ := ht
  have gs : gap s (v+1) := by
    intro p hp
    have := hd p hp
    omega
  obtain ⟨hL,hF,hC⟩ := paste_spec hl tl hf tf gs tw
  refine ⟨paste n s t,hL,hF,by simpa [hc,tc] using hC,?_,?_⟩
  · intro p hp
    rcases mem_union.mp hp with h|h
    · have := hw p h
      omega
    · obtain ⟨q,hq,rfl⟩ := mem_image.mp h
      have := tw q hq
      simp only [shift]
      omega
  · intro p hp
    rcases mem_union.mp hp with h|h
    · have := hd p h
      omega
    · obtain ⟨q,hq,rfl⟩ := mem_image.mp h
      have := td q hq
      simp only [shift]
      omega

lemma config_reaches {n k w d} (h : config n k w d) (hk : k = 4*n/3 := by decide) : reaches n := by
  obtain ⟨s,hl,hf,hc,_,_⟩ := h
  exact ⟨s,hl,hf,hc.trans hk⟩

def tested (s : Finset Cell) : Prop :=
  ∀ p ∈ s, (s.filter (fun q => p ≠ q ∧ aligned p q)).card ≤ 1

instance (s : Finset Cell) : Decidable (tested s) := by unfold tested; infer_instance
instance (s : Finset Cell) (n : ℕ) : Decidable (fits s n) := by unfold fits; infer_instance
instance (s : Finset Cell) (w : ℕ) : Decidable (band s w) := by unfold band; infer_instance
instance (s : Finset Cell) (d : ℕ) : Decidable (gap s d) := by unfold gap; infer_instance

lemma config_of_test (s : Finset Cell) {n k w d}
    (h : tested s ∧ fits s n ∧ s.card = k ∧ band s w ∧ gap s d) : config n k w d := by
  refine ⟨s,?_,h.2⟩
  intro p hp q hq r hr hn hm h1 h2
  exact card_le_one.mp (h.1 p hp) q (mem_filter.mpr ⟨hq,hn,h1⟩) r (mem_filter.mpr ⟨hr,hm,h2⟩)

end OMA.QueenConstruction

namespace OMA.QueenConstruction
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner6 : config 6 8 4 1 :=
  config_of_test ([(0,3), (0,4), (1,0), (2,0), (3,5), (4,5), (5,1), (5,2)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner7 : config 7 9 5 0 :=
  config_of_test ([(0,2), (0,5), (1,0), (2,6), (3,3), (4,0), (5,6), (6,1), (6,4)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner8 : config 8 10 4 0 :=
  config_of_test ([(0,0), (1,2), (1,3), (2,6), (3,6), (4,1), (5,1), (6,4), (6,5), (7,7)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner9 : config 9 12 6 0 :=
  config_of_test ([(0,3), (0,4), (1,0), (2,0), (3,5), (3,8), (4,1), (5,1), (6,6), (6,7), (7,2), (8,2)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner10 : config 10 13 6 0 :=
  config_of_test ([(0,1), (0,5), (1,7), (2,2), (3,0), (4,3), (4,6), (5,8), (5,9), (6,0), (7,2), (8,4), (9,7)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner11 : config 11 14 6 0 :=
  config_of_test ([(0,1), (0,6), (1,4), (2,0), (2,2), (3,8), (4,9), (5,4), (6,10), (7,3), (8,10), (9,3), (10,5), (10,7)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner12 : config 12 16 8 1 :=
  config_of_test ([(0,4), (0,6), (1,2), (1,8), (2,0), (3,11), (4,1), (5,10), (6,1), (7,10), (8,0), (9,11), (10,3), (10,9), (11,5), (11,7)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner13 : config 13 17 9 0 :=
  config_of_test ([(0,7), (0,9), (1,2), (1,4), (2,0), (3,11), (4,0), (5,11), (6,6), (7,1), (8,12), (9,1), (10,12), (11,8), (11,10), (12,3), (12,5)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner14 : config 14 18 8 0 :=
  config_of_test ([(0,2), (1,6), (2,1), (3,10), (3,11), (4,5), (4,8), (5,3), (6,0), (6,12), (7,3), (8,7), (9,2), (10,13), (11,6), (12,4), (12,9), (13,13)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner15 : config 15 20 10 1 :=
  config_of_test ([(0,7), (1,9), (1,10), (2,1), (3,13), (4,0), (5,3), (5,8), (6,0), (7,2), (7,12), (8,14), (9,6), (9,11), (10,14), (11,1), (12,13), (13,4), (13,5), (14,7)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner16 : config 16 21 12 1 :=
  config_of_test ([(0,8), (0,12), (1,6), (2,4), (2,9), (3,1), (3,13), (4,10), (5,0), (6,15), (7,3), (8,11), (9,0), (10,3), (11,15), (12,6), (13,2), (13,14), (14,11), (15,5), (15,7)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner17 : config 17 22 13 1 :=
  config_of_test ([(0,7), (0,10), (1,12), (1,14), (2,0), (3,15), (4,8), (5,0), (6,3), (6,5), (7,1), (9,15), (10,11), (10,13), (11,16), (12,8), (13,1), (14,16), (15,2), (15,4), (16,6), (16,9)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner18 : config 18 24 14 1 :=
  config_of_test ([(0,9), (0,11), (1,4), (1,15), (2,1), (3,10), (4,16), (5,10), (6,0), (7,3), (7,5), (8,0), (9,17), (10,12), (10,14), (11,17), (12,7), (13,1), (14,7), (15,16), (16,2), (16,13), (17,6), (17,8)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner19 : config 19 25 14 0 :=
  config_of_test ([(0,14), (1,7), (1,10), (2,5), (2,15), (3,2), (4,0), (4,12), (5,16), (6,4), (7,17), (8,1), (9,9), (10,17), (11,1), (12,14), (13,2), (14,6), (14,18), (15,16), (16,3), (16,13), (17,8), (17,11), (18,4)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner20 : config 20 26 15 1 :=
  config_of_test ([(0,13), (0,14), (1,2), (1,4), (2,8), (2,9), (3,18), (4,16), (5,1), (6,16), (7,12), (8,0), (9,0), (10,19), (11,19), (12,7), (13,3), (14,18), (15,3), (16,1), (17,10), (17,11), (18,15), (18,17), (19,5), (19,6)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner21 : config 21 28 18 1 :=
  config_of_test ([(0,6), (0,18), (1,8), (1,11), (2,3), (3,5), (3,7), (4,17), (5,20), (6,20), (7,10), (8,16), (9,4), (10,1), (10,19), (11,16), (12,4), (13,10), (14,0), (15,0), (16,3), (17,13), (17,15), (18,17), (19,9), (19,12), (20,2), (20,14)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner22 : config 22 29 14 0 :=
  config_of_test ([(0,0), (1,6), (2,11), (2,13), (3,16), (4,18), (5,7), (5,15), (6,18), (7,3), (7,10), (8,0), (9,16), (10,1), (11,5), (11,17), (12,20), (13,1), (14,9), (15,12), (16,2), (16,14), (17,4), (17,21), (18,8), (18,19), (19,12), (20,9), (21,20)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner23 : config 23 30 16 1 :=
  config_of_test ([(0,9), (0,14), (1,5), (2,5), (3,15), (4,19), (5,6), (5,10), (6,22), (7,18), (7,20), (8,0), (9,15), (10,3), (11,1), (11,21), (12,19), (13,7), (14,22), (15,2), (15,4), (16,0), (17,12), (17,16), (18,3), (19,7), (20,17), (21,17), (22,8), (22,13)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner24 : config 24 32 18 1 :=
  config_of_test ([(0,8), (0,14), (1,19), (2,4), (3,7), (3,13), (4,1), (4,21), (5,6), (6,12), (6,18), (7,20), (8,23), (9,0), (10,3), (11,6), (12,17), (13,20), (14,23), (15,0), (16,3), (17,5), (17,11), (18,17), (19,2), (19,22), (20,10), (20,16), (21,19), (22,4), (23,9), (23,15)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner25 : config 25 33 16 0 :=
  config_of_test ([(0,10), (1,10), (2,6), (3,9), (4,5), (5,16), (5,20), (6,11), (6,22), (7,15), (8,5), (9,7), (9,21), (10,23), (10,24), (11,18), (12,12), (13,6), (14,0), (14,1), (15,3), (15,17), (16,19), (17,9), (18,2), (18,13), (19,4), (19,8), (20,19), (21,15), (22,18), (23,14), (24,14)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner26 : config 26 34 18 0 :=
  config_of_test ([(0,7), (0,16), (1,12), (1,18), (2,0), (3,11), (3,21), (4,1), (4,19), (5,5), (6,20), (7,10), (8,10), (9,2), (10,15), (10,22), (11,24), (12,0), (13,2), (14,8), (15,25), (16,25), (17,3), (18,3), (19,20), (20,24), (21,8), (22,5), (23,13), (23,14), (24,6), (24,23), (25,9), (25,17)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner27 : config 27 36 18 1 :=
  config_of_test ([(0,3), (0,11), (1,19), (2,6), (2,14), (3,19), (4,13), (5,4), (5,10), (6,21), (7,5), (8,25), (9,1), (10,24), (11,17), (11,18), (12,2), (13,0), (13,26), (14,24), (15,8), (15,9), (16,2), (17,25), (18,1), (19,21), (20,5), (21,16), (21,22), (22,13), (23,7), (24,12), (24,20), (25,7), (26,15), (26,23)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner28 : config 28 37 18 0 :=
  config_of_test ([(0,13), (0,15), (1,6), (1,8), (2,2), (3,5), (4,12), (4,22), (5,19), (6,23), (7,3), (8,3), (9,21), (9,25), (10,4), (11,14), (11,20), (12,10), (13,24), (14,24), (15,4), (16,7), (17,0), (17,1), (18,17), (19,23), (20,7), (21,18), (21,27), (22,10), (23,5), (24,9), (24,16), (25,11), (25,26), (26,19), (27,17)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner29 : config 29 38 18 0 :=
  config_of_test ([(0,14), (1,7), (1,12), (2,18), (3,8), (4,0), (4,2), (5,17), (5,22), (6,3), (7,25), (8,15), (8,23), (9,9), (10,20), (11,10), (12,4), (13,4), (14,1), (14,27), (15,24), (16,24), (17,18), (18,8), (19,19), (20,5), (20,13), (21,3), (22,25), (23,6), (23,11), (24,26), (24,28), (25,20), (26,10), (27,16), (27,21), (28,14)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner30 : config 30 40 22 1 :=
  config_of_test ([(0,10), (0,12), (1,21), (2,13), (2,23), (3,4), (3,18), (4,26), (5,8), (6,2), (7,20), (8,1), (8,24), (9,7), (9,15), (10,29), (11,3), (12,29), (13,27), (14,9), (15,20), (16,2), (17,0), (18,26), (19,0), (20,14), (20,22), (21,5), (21,28), (22,9), (23,27), (24,21), (25,3), (26,11), (26,25), (27,6), (27,16), (28,8), (29,17), (29,19)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner31 : config 31 41 23 0 :=
  config_of_test ([(0,11), (0,13), (1,8), (2,25), (3,9), (3,23), (4,16), (4,18), (5,2), (5,10), (6,22), (7,3), (8,6), (8,29), (9,27), (10,25), (11,30), (12,4), (13,30), (14,4), (15,15), (16,26), (17,0), (18,26), (19,0), (20,5), (21,3), (22,1), (22,24), (23,27), (24,8), (25,20), (25,28), (26,12), (26,14), (27,7), (27,21), (28,5), (29,22), (30,17), (30,19)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner32 : config 32 42 21 1 :=
  config_of_test ([(0,14), (0,18), (1,11), (1,20), (2,8), (3,23), (4,3), (4,25), (5,12), (6,21), (7,8), (8,1), (9,13), (10,23), (11,0), (11,19), (12,4), (12,29), (13,22), (14,10), (15,31), (16,21), (17,15), (18,5), (18,30), (19,1), (20,31), (21,7), (21,24), (22,12), (23,2), (23,17), (24,15), (25,6), (25,27), (26,10), (27,22), (28,16), (29,9), (29,26), (30,13), (31,16)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner33 : config 33 44 22 1 :=
  config_of_test ([(0,1), (1,5), (1,8), (2,14), (2,19), (3,12), (4,6), (4,7), (5,20), (6,16), (7,23), (8,28), (8,30), (9,15), (9,22), (10,31), (11,3), (12,23), (13,32), (14,32), (15,29), (16,11), (16,21), (17,3), (18,0), (19,0), (20,9), (21,29), (22,1), (23,10), (23,17), (24,2), (24,4), (25,9), (26,16), (27,12), (28,25), (28,26), (29,20), (30,13), (30,18), (31,24), (31,27), (32,31)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner34 : config 34 45 26 0 :=
  config_of_test ([(0,5), (1,10), (1,13), (2,20), (2,22), (3,16), (3,27), (4,2), (5,5), (6,3), (7,24), (7,29), (8,9), (9,23), (10,33), (11,1), (11,7), (12,33), (13,2), (14,9), (15,18), (15,19), (16,4), (17,32), (18,11), (18,28), (19,25), (20,31), (21,0), (22,3), (23,31), (24,4), (25,32), (26,0), (27,12), (27,26), (28,14), (28,30), (29,6), (29,21), (30,17), (31,25), (32,23), (33,8), (33,15)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner35 : config 35 46 23 1 :=
  config_of_test ([(0,22), (1,15), (2,5), (2,25), (3,7), (4,14), (4,16), (5,6), (5,26), (6,17), (7,22), (8,0), (9,0), (10,3), (10,23), (11,27), (12,30), (12,32), (13,19), (14,33), (15,10), (15,13), (16,33), (18,1), (19,21), (19,24), (20,1), (21,15), (22,2), (22,4), (23,7), (24,11), (24,31), (25,34), (26,34), (27,12), (28,17), (29,8), (29,28), (30,18), (30,20), (31,27), (32,9), (32,29), (33,19), (34,12)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner36 : config 36 48 24 1 :=
  config_of_test ([(0,6), (1,15), (1,24), (2,21), (3,23), (3,27), (4,7), (4,16), (5,10), (6,2), (7,25), (8,6), (9,0), (9,30), (10,32), (11,18), (11,26), (12,1), (13,21), (14,4), (14,13), (15,2), (16,32), (17,34), (18,1), (19,3), (20,33), (21,22), (21,31), (22,14), (23,34), (24,9), (24,17), (25,3), (26,5), (26,35), (27,29), (28,10), (29,33), (30,25), (31,19), (31,28), (32,8), (32,12), (33,14), (34,11), (34,20), (35,29)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner37 : config 37 49 24 0 :=
  config_of_test ([(0,1), (0,8), (1,12), (1,17), (2,21), (3,21), (4,6), (5,14), (6,16), (6,23), (7,2), (8,4), (8,31), (9,33), (10,30), (11,33), (12,9), (12,25), (13,34), (14,0), (15,0), (16,22), (17,10), (17,29), (18,18), (19,7), (19,26), (20,14), (21,36), (22,36), (23,2), (24,11), (24,27), (25,3), (26,6), (27,3), (28,5), (28,32), (29,34), (30,13), (30,20), (31,22), (32,30), (33,15), (34,15), (35,19), (35,24), (36,28), (36,35)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner38 : config 38 50 26 0 :=
  config_of_test ([(0,1), (1,11), (2,15), (2,27), (3,11), (4,7), (4,21), (5,0), (6,20), (6,29), (7,9), (7,14), (8,34), (9,13), (9,25), (10,34), (11,2), (11,32), (12,6), (13,33), (14,36), (15,0), (16,4), (17,6), (18,18), (19,19), (20,31), (21,33), (22,37), (23,1), (24,4), (25,31), (26,5), (26,35), (27,3), (28,12), (28,24), (29,3), (30,23), (30,28), (31,8), (31,17), (32,37), (33,16), (33,30), (34,26), (35,10), (35,22), (36,26), (37,36)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner39 : config 39 52 26 1 :=
  config_of_test ([(0,2), (0,10), (1,17), (1,22), (2,19), (3,26), (4,5), (5,11), (5,14), (6,20), (7,15), (7,32), (8,26), (9,4), (9,31), (10,25), (11,37), (12,5), (13,1), (14,38), (15,18), (16,29), (16,35), (17,13), (18,38), (19,8), (19,30), (20,0), (21,25), (22,3), (22,9), (23,20), (24,0), (25,37), (26,33), (27,1), (28,13), (29,7), (29,34), (30,12), (31,6), (31,23), (32,18), (33,24), (33,27), (34,33), (35,12), (36,19), (37,16), (37,21), (38,28), (38,36)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner40 : config 40 53 30 0 :=
  config_of_test ([(0,1), (1,7), (2,21), (2,23), (3,15), (3,26), (4,8), (4,24), (5,30), (5,31), (6,34), (7,10), (7,17), (8,38), (9,1), (10,27), (11,0), (12,3), (12,20), (13,13), (13,37), (14,2), (15,5), (16,11), (16,32), (17,39), (18,33), (19,12), (20,34), (21,39), (22,0), (23,19), (23,36), (24,29), (25,27), (26,7), (27,38), (28,2), (29,5), (30,14), (31,14), (32,29), (33,6), (34,4), (34,28), (35,33), (36,22), (36,35), (37,12), (38,9), (38,25), (39,16), (39,18)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner41 : config 41 54 26 0 :=
  config_of_test ([(0,20), (1,18), (2,5), (2,13), (3,3), (4,0), (5,29), (6,8), (6,25), (7,17), (7,19), (8,1), (8,24), (9,34), (10,28), (10,31), (11,34), (12,38), (13,4), (14,22), (15,10), (15,14), (16,2), (17,11), (18,40), (19,4), (20,7), (20,33), (21,36), (22,0), (23,29), (24,38), (25,26), (25,30), (26,18), (27,36), (28,2), (29,6), (30,9), (30,12), (31,6), (32,16), (32,39), (33,21), (33,23), (34,15), (34,32), (35,11), (36,40), (37,37), (38,27), (38,35), (39,22), (40,20)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem host12 : config 12 16 9 2 :=
  config_of_test ([(0,5), (0,7), (1,3), (1,9), (2,11), (3,0), (4,10), (5,1), (6,10), (7,1), (8,11), (9,0), (10,2), (10,8), (11,4), (11,6)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem host15 : config 15 20 13 2 :=
  config_of_test ([(0,3), (0,7), (1,14), (2,11), (2,12), (3,5), (3,9), (4,1), (5,13), (6,0), (7,2), (8,13), (9,1), (10,14), (11,0), (12,8), (12,10), (13,4), (13,6), (14,2)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem host18 : config 18 24 13 2 :=
  config_of_test ([(0,11), (1,4), (1,5), (2,7), (2,14), (3,9), (3,16), (4,6), (5,15), (6,15), (7,0), (8,0), (9,17), (10,17), (11,2), (12,2), (13,11), (14,1), (14,8), (15,3), (15,10), (16,12), (16,13), (17,6)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem host24 : config 24 32 19 3 :=
  config_of_test ([(0,5), (0,19), (1,13), (1,14), (2,16), (2,20), (3,6), (4,8), (4,12), (5,21), (6,23), (7,1), (8,17), (9,2), (10,0), (11,22), (12,1), (13,23), (14,21), (15,6), (16,22), (17,0), (18,2), (19,11), (19,15), (20,17), (21,3), (21,7), (22,9), (22,10), (23,4), (23,18)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem host45 : config 45 60 39 5 :=
  config_of_test ([(0,15), (0,33), (1,20), (1,28), (2,41), (3,19), (3,23), (4,27), (4,30), (5,12), (5,13), (6,35), (7,35), (8,44), (9,18), (9,39), (10,4), (11,1), (12,44), (13,38), (14,2), (15,4), (16,34), (16,37), (17,22), (18,42), (19,6), (20,3), (21,43), (22,8), (22,36), (23,1), (24,41), (25,38), (26,2), (27,22), (28,7), (28,10), (29,40), (30,42), (31,6), (32,0), (33,43), (34,40), (35,5), (35,26), (36,0), (37,9), (38,9), (39,31), (39,32), (40,14), (40,17), (41,21), (41,25), (42,3), (43,16), (43,24), (44,11), (44,29)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem host48 : config 48 64 40 7 :=
  config_of_test ([(0,18), (0,36), (1,13), (1,33), (2,17), (2,24), (3,12), (3,38), (4,25), (4,28), (5,45), (6,37), (6,43), (7,20), (7,26), (8,15), (8,16), (9,39), (10,44), (11,44), (12,1), (13,39), (14,42), (15,42), (16,6), (17,46), (18,41), (19,2), (20,0), (21,7), (22,47), (23,7), (24,40), (25,0), (26,40), (27,47), (28,45), (29,6), (30,1), (31,41), (32,5), (33,5), (34,8), (35,46), (36,3), (37,3), (38,8), (39,31), (39,32), (40,21), (40,27), (41,4), (41,10), (42,2), (43,19), (43,22), (44,9), (44,35), (45,23), (45,30), (46,14), (46,34), (47,11), (47,29)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem host63 : config 63 84 50 1 :=
  config_of_test ([(0,43), (0,47), (1,40), (1,41), (2,13), (2,52), (3,0), (3,36), (4,45), (5,11), (5,25), (6,28), (7,5), (8,44), (9,23), (9,35), (10,18), (11,56), (12,7), (13,12), (13,32), (14,45), (15,3), (16,34), (17,46), (17,61), (18,42), (18,53), (19,4), (20,4), (21,8), (22,54), (23,14), (23,33), (24,7), (25,2), (26,60), (27,31), (28,56), (29,59), (30,5), (31,24), (31,38), (32,57), (33,3), (34,6), (35,31), (36,2), (37,60), (38,55), (39,29), (39,48), (40,8), (41,54), (42,58), (43,58), (44,9), (44,20), (45,1), (45,16), (46,28), (47,59), (48,17), (49,30), (49,50), (50,55), (51,6), (52,44), (53,27), (53,39), (54,18), (55,57), (56,34), (57,37), (57,51), (58,17), (59,26), (59,62), (60,10), (60,49), (61,21), (61,22), (62,15), (62,19)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem host6 : config 6 8 4 1 :=
  config_of_test ([(0,1), (0,2), (1,5), (2,5), (3,0), (4,0), (5,3), (5,4)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner1 : config 1 1 0 0 :=
  config_of_test ([(0,0)] : List Cell).toFinset (by decide +kernel)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem corner2 : config 2 2 0 0 :=
  config_of_test ([(0,0), (1,1)] : List Cell).toFinset (by decide +kernel)

end OMA.QueenConstruction

namespace OMA.QueenConstruction
lemma config_weaken {n k w d w' d'} (hc : config n k w d) (hw : w ≤ w' := by decide) (hd : d' ≤ d := by decide) :
    config n k w' d' := by
  obtain ⟨s,hl,hf,hc,wb,db⟩ := hc
  refine ⟨s,hl,hf,hc,?_,?_⟩
  · intro p hp
    have := wb p hp
    omega
  · intro p hp
    have := db p hp
    omega
end OMA.QueenConstruction


namespace OMA.QueenConstruction

theorem small_boards {n : ℕ} (h : 6 ≤ n) (h' : n < 216) : reaches n := by
  interval_cases n
  · exact config_reaches corner6
  · exact config_reaches (config_paste (config_product (b := 1) host6) corner1)
  · exact config_reaches corner8
  · exact config_reaches corner9
  · exact config_reaches corner10
  · exact config_reaches corner11
  · exact config_reaches host12
  · exact config_reaches corner13
  · exact config_reaches corner14
  · exact config_reaches host15
  · exact config_reaches corner16
  · exact config_reaches corner17
  · exact config_reaches host18
  · exact config_reaches (config_paste (config_product (b := 1) host18) corner1)
  · exact config_reaches corner20
  · exact config_reaches corner21
  · exact config_reaches corner22
  · exact config_reaches corner23
  · exact config_reaches host24
  · exact config_reaches corner25
  · exact config_reaches corner26
  · exact config_reaches corner27
  · exact config_reaches corner28
  · exact config_reaches corner29
  · exact config_reaches (config_product (b := 5) host6)
  · exact config_reaches (config_paste (config_product (b := 5) host6) corner1)
  · exact config_reaches corner32
  · exact config_reaches corner33
  · exact config_reaches corner34
  · exact config_reaches corner35
  · exact config_reaches corner36
  · exact config_reaches corner37
  · exact config_reaches corner38
  · exact config_reaches corner39
  · exact config_reaches corner40
  · exact config_reaches corner41
  · exact config_reaches (config_product (b := 7) host6)
  · exact config_reaches (config_paste (config_product (b := 7) host6) corner1)
  · exact config_reaches (config_paste (config_product (b := 7) host6) corner2)
  · exact config_reaches host45
  · exact config_reaches (config_paste (config_product (b := 1) host45) corner1)
  · exact config_reaches (config_paste (config_product (b := 1) host45) corner2)
  · exact config_reaches host48
  · exact config_reaches (config_paste (config_product (b := 1) host48) corner1)
  · exact config_reaches (config_paste (config_product (b := 1) host48) corner2)
  · exact config_reaches (config_paste (config_product (b := 1) host45) corner6)
  · exact config_reaches (config_paste (config_product (b := 1) host45) (config_paste (config_product (b := 1) host6) corner1))
  · exact config_reaches (config_paste (config_product (b := 1) host45) corner8)
  · exact config_reaches (config_paste (config_product (b := 1) host48) corner6)
  · exact config_reaches (config_paste (config_product (b := 1) host48) corner7)
  · exact config_reaches (config_paste (config_product (b := 1) host48) corner8)
  · exact config_reaches (config_paste (config_product (b := 1) host48) corner9)
  · exact config_reaches (config_paste (config_product (b := 1) host48) corner10)
  · exact config_reaches (config_paste (config_product (b := 1) host48) corner11)
  · exact config_reaches (config_product (b := 5) host12)
  · exact config_reaches (config_paste (config_product (b := 5) host12) corner1)
  · exact config_reaches (config_paste (config_product (b := 5) host12) corner2)
  · exact config_reaches host63
  · exact config_reaches (config_paste (config_product (b := 1) host63) corner1)
  · exact config_reaches (config_paste (config_product (b := 1) host63) corner2)
  · exact config_reaches (config_product (b := 11) host6)
  · exact config_reaches (config_paste (config_product (b := 5) host12) corner7)
  · exact config_reaches (config_paste (config_product (b := 5) host12) corner8)
  · exact config_reaches (config_paste (config_product (b := 5) host12) corner9)
  · exact config_reaches (config_paste (config_product (b := 5) host12) corner10)
  · exact config_reaches (config_paste (config_product (b := 5) host12) corner11)
  · exact config_reaches (config_paste (config_product (b := 11) host6) corner6)
  · exact config_reaches (config_paste (config_product (b := 11) host6) corner7)
  · exact config_reaches (config_paste (config_product (b := 11) host6) corner8)
  · exact config_reaches (config_product (b := 5) host15)
  · exact config_reaches (config_paste (config_product (b := 5) host15) corner1)
  · exact config_reaches (config_paste (config_product (b := 5) host15) corner2)
  · exact config_reaches (config_product (b := 13) host6)
  · exact config_reaches (config_paste (config_product (b := 13) host6) corner1)
  · exact config_reaches (config_paste (config_product (b := 13) host6) corner2)
  · exact config_reaches (config_paste (config_product (b := 5) host15) corner6)
  · exact config_reaches (config_paste (config_product (b := 5) host15) corner7)
  · exact config_reaches (config_paste (config_product (b := 5) host15) corner8)
  · exact config_reaches (config_product (b := 7) host12)
  · exact config_reaches (config_paste (config_product (b := 13) host6) corner7)
  · exact config_reaches (config_paste (config_product (b := 13) host6) corner8)
  · exact config_reaches (config_paste (config_product (b := 13) host6) corner9)
  · exact config_reaches (config_paste (config_product (b := 13) host6) corner10)
  · exact config_reaches (config_paste (config_product (b := 13) host6) corner11)
  · exact config_reaches (config_product (b := 5) host18)
  · exact config_reaches (config_paste (config_product (b := 7) host12) corner7)
  · exact config_reaches (config_paste (config_product (b := 7) host12) corner8)
  · exact config_reaches (config_paste (config_product (b := 7) host12) corner9)
  · exact config_reaches (config_paste (config_product (b := 7) host12) corner10)
  · exact config_reaches (config_paste (config_product (b := 7) host12) corner11)
  · exact config_reaches (config_paste (config_product (b := 7) host12) host12)
  · exact config_reaches (config_paste (config_product (b := 7) host12) corner13)
  · exact config_reaches (config_paste (config_product (b := 7) host12) corner14)
  · exact config_reaches (config_paste (config_product (b := 7) host12) corner15)
  · exact config_reaches (config_paste (config_product (b := 5) host18) corner10)
  · exact config_reaches (config_paste (config_product (b := 5) host18) corner11)
  · exact config_reaches (config_product (b := 17) host6)
  · exact config_reaches (config_paste (config_product (b := 17) host6) corner1)
  · exact config_reaches (config_paste (config_product (b := 17) host6) corner2)
  · exact config_reaches (config_product (b := 7) host15)
  · exact config_reaches (config_paste (config_product (b := 7) host15) corner1)
  · exact config_reaches (config_paste (config_product (b := 7) host15) corner2)
  · exact config_reaches (config_paste (config_product (b := 17) host6) corner6)
  · exact config_reaches (config_paste (config_product (b := 17) host6) corner7)
  · exact config_reaches (config_paste (config_product (b := 17) host6) corner8)
  · exact config_reaches (config_paste (config_product (b := 7) host15) corner6)
  · exact config_reaches (config_paste (config_product (b := 17) host6) corner10)
  · exact config_reaches (config_paste (config_product (b := 17) host6) corner11)
  · exact config_reaches (config_product (b := 19) host6)
  · exact config_reaches (config_paste (config_product (b := 19) host6) corner1)
  · exact config_reaches (config_paste (config_product (b := 17) host6) corner14)
  · exact config_reaches (config_paste (config_product (b := 7) host15) host12)
  · exact config_reaches (config_paste (config_product (b := 7) host15) corner13)
  · exact config_reaches (config_paste (config_product (b := 7) host15) corner14)
  · exact config_reaches (config_product (b := 5) host24)
  · exact config_reaches (config_paste (config_product (b := 19) host6) corner7)
  · exact config_reaches (config_paste (config_product (b := 19) host6) corner8)
  · exact config_reaches (config_paste (config_product (b := 19) host6) corner9)
  · exact config_reaches (config_paste (config_product (b := 19) host6) corner10)
  · exact config_reaches (config_paste (config_product (b := 19) host6) corner11)
  · exact config_reaches (config_product (b := 7) host18)
  · exact config_reaches (config_paste (config_product (b := 19) host6) corner13)
  · exact config_reaches (config_paste (config_product (b := 19) host6) corner14)
  · exact config_reaches (config_paste (config_product (b := 5) host24) corner9)
  · exact config_reaches (config_paste (config_product (b := 5) host24) corner10)
  · exact config_reaches (config_paste (config_product (b := 5) host24) corner11)
  · exact config_reaches (config_product (b := 11) host12)
  · exact config_reaches (config_paste (config_product (b := 7) host18) corner7)
  · exact config_reaches (config_paste (config_product (b := 7) host18) corner8)
  · exact config_reaches (config_paste (config_product (b := 5) host24) corner15)
  · exact config_reaches (config_paste (config_product (b := 5) host24) corner16)
  · exact config_reaches (config_paste (config_product (b := 7) host18) corner11)
  · exact config_reaches (config_product (b := 23) host6)
  · exact config_reaches (config_paste (config_product (b := 7) host18) corner13)
  · exact config_reaches (config_paste (config_product (b := 7) host18) corner14)
  · exact config_reaches (config_paste (config_product (b := 7) host18) corner15)
  · exact config_reaches (config_paste (config_product (b := 11) host12) corner10)
  · exact config_reaches (config_paste (config_product (b := 11) host12) corner11)
  · exact config_reaches (config_paste (config_product (b := 11) host12) host12)
  · exact config_reaches (config_paste (config_product (b := 23) host6) corner7)
  · exact config_reaches (config_paste (config_product (b := 23) host6) corner8)
  · exact config_reaches (config_paste (config_product (b := 11) host12) host15)
  · exact config_reaches (config_paste (config_product (b := 11) host12) corner16)
  · exact config_reaches (config_paste (config_product (b := 11) host12) corner17)
  · exact config_reaches (config_product (b := 25) host6)
  · exact config_reaches (config_paste (config_product (b := 23) host6) corner13)
  · exact config_reaches (config_paste (config_product (b := 11) host12) corner20)
  · exact config_reaches (config_paste (config_product (b := 23) host6) corner15)
  · exact config_reaches (config_paste (config_product (b := 11) host12) corner22)
  · exact config_reaches (config_paste (config_product (b := 11) host12) corner23)
  · exact config_reaches (config_product (b := 13) host12)
  · exact config_reaches (config_paste (config_product (b := 11) host12) corner25)
  · exact config_reaches (config_paste (config_product (b := 25) host6) corner8)
  · exact config_reaches (config_paste (config_product (b := 25) host6) corner9)
  · exact config_reaches (config_paste (config_product (b := 25) host6) corner10)
  · exact config_reaches (config_paste (config_product (b := 25) host6) corner11)
  · exact config_reaches (config_paste (config_product (b := 25) host6) host12)
  · exact config_reaches (config_paste (config_product (b := 25) host6) corner13)
  · exact config_reaches (config_paste (config_product (b := 25) host6) corner14)
  · exact config_reaches (config_product (b := 11) host15)
  · exact config_reaches (config_paste (config_product (b := 25) host6) corner16)
  · exact config_reaches (config_paste (config_product (b := 13) host12) corner11)
  · exact config_reaches (config_product (b := 7) host24)
  · exact config_reaches (config_paste (config_product (b := 13) host12) corner13)
  · exact config_reaches (config_paste (config_product (b := 13) host12) corner14)
  · exact config_reaches (config_paste (config_product (b := 13) host12) host15)
  · exact config_reaches (config_paste (config_product (b := 13) host12) corner16)
  · exact config_reaches (config_paste (config_product (b := 13) host12) corner17)
  · exact config_reaches (config_product (b := 29) host6)
  · exact config_reaches (config_paste (config_product (b := 13) host12) corner19)
  · exact config_reaches (config_paste (config_product (b := 13) host12) corner20)
  · exact config_reaches (config_paste (config_product (b := 11) host15) host12)
  · exact config_reaches (config_paste (config_product (b := 13) host12) corner22)
  · exact config_reaches (config_paste (config_product (b := 13) host12) corner23)
  · exact config_reaches (config_paste (config_product (b := 13) host12) host24)
  · exact config_reaches (config_paste (config_product (b := 11) host15) corner16)
  · exact config_reaches (config_paste (config_product (b := 11) host15) corner17)
  · exact config_reaches (config_paste (config_product (b := 7) host24) host15)
  · exact config_reaches (config_paste (config_product (b := 7) host24) corner16)
  · exact config_reaches (config_paste (config_product (b := 7) host24) corner17)
  · exact config_reaches (config_product (b := 31) host6)
  · exact config_reaches (config_paste (config_product (b := 29) host6) corner13)
  · exact config_reaches (config_paste (config_product (b := 7) host24) corner20)
  · exact config_reaches (config_paste (config_product (b := 29) host6) host15)
  · exact config_reaches (config_paste (config_product (b := 29) host6) corner16)
  · exact config_reaches (config_paste (config_product (b := 29) host6) corner17)
  · exact config_reaches (config_paste (config_product (b := 29) host6) host18)
  · exact config_reaches (config_paste (config_product (b := 29) host6) corner19)
  · exact config_reaches (config_paste (config_product (b := 31) host6) corner8)
  · exact config_reaches (config_product (b := 13) host15)
  · exact config_reaches (config_paste (config_product (b := 29) host6) corner22)
  · exact config_reaches (config_paste (config_product (b := 31) host6) corner11)
  · exact config_reaches (config_product (b := 11) host18)
  · exact config_reaches (config_paste (config_product (b := 31) host6) corner13)
  · exact config_reaches (config_paste (config_product (b := 31) host6) corner14)
  · exact config_reaches (config_paste (config_product (b := 31) host6) host15)
  · exact config_reaches (config_paste (config_product (b := 31) host6) corner16)
  · exact config_reaches (config_paste (config_product (b := 31) host6) corner17)
  · exact config_reaches (config_product (b := 17) host12)
  · exact config_reaches (config_paste (config_product (b := 31) host6) corner19)
  · exact config_reaches (config_paste (config_product (b := 31) host6) corner20)
  · exact config_reaches (config_paste (config_product (b := 13) host15) host12)
  · exact config_reaches (config_paste (config_product (b := 31) host6) corner22)
  · exact config_reaches (config_paste (config_product (b := 11) host18) corner11)
  · exact config_reaches (config_product (b := 35) host6)
  · exact config_reaches (config_paste (config_product (b := 13) host15) corner16)
  · exact config_reaches (config_paste (config_product (b := 13) host15) corner17)
  · exact config_reaches (config_paste (config_product (b := 11) host18) host15)
  · exact config_reaches (config_paste (config_product (b := 11) host18) corner16)
  · exact config_reaches (config_paste (config_product (b := 11) host18) corner17)

theorem corners17 {m : ℕ} (h : 6 ≤ m) (h' : m ≤ 17) : config m (4*m/3) 13 0 := by
  interval_cases m
  · exact config_weaken corner6
  · exact config_weaken corner7
  · exact config_weaken corner8
  · exact config_weaken corner9
  · exact config_weaken corner10
  · exact config_weaken corner11
  · exact config_weaken corner12
  · exact config_weaken corner13
  · exact config_weaken corner14
  · exact config_weaken corner15
  · exact config_weaken corner16
  · exact config_weaken corner17

theorem corners29 {m : ℕ} (h : 6 ≤ m) (h' : m ≤ 29) : config m (4*m/3) 18 0 := by
  interval_cases m
  · exact config_weaken corner6
  · exact config_weaken corner7
  · exact config_weaken corner8
  · exact config_weaken corner9
  · exact config_weaken corner10
  · exact config_weaken corner11
  · exact config_weaken corner12
  · exact config_weaken corner13
  · exact config_weaken corner14
  · exact config_weaken corner15
  · exact config_weaken corner16
  · exact config_weaken corner17
  · exact config_weaken corner18
  · exact config_weaken corner19
  · exact config_weaken corner20
  · exact config_weaken corner21
  · exact config_weaken corner22
  · exact config_weaken corner23
  · exact config_weaken corner24
  · exact config_weaken corner25
  · exact config_weaken corner26
  · exact config_weaken corner27
  · exact config_weaken corner28
  · exact config_weaken corner29

end OMA.QueenConstruction

namespace OMA.QueenConstruction

private theorem outer_paste (seed : config 6 8 4 1) {b m w d n} (h : config m (4*m/3) w d)
    (hb : 0 < b) (h2 : b.gcd 2 = 1) (h3 : b.gcd 3 = 1)
    (hgap : w < b-b/2) (hn : n=b*6+m) : reaches n := by
  have host := config_product (b := b) seed hb h2 h3
  have hjoin := config_paste host h (by simpa using hgap)
  subst n
  exact config_reaches hjoin (by omega)

theorem large_boards_using (seed : config 6 8 4 1)
    (corners17 : ∀ {m}, 6 ≤ m → m ≤ 17 → config m (4*m/3) 13 0)
    (corners29 : ∀ {m}, 6 ≤ m → m ≤ 29 → config m (4*m/3) 18 0)
    {n : ℕ} (hn : 216 ≤ n) : reaches n := by
  let t := n/36
  let r := n%36
  have hs : n = 36*t+r := by dsimp [t,r]; omega
  have ht : 6 ≤ t := by dsimp [t]; omega
  have hr : r < 36 := Nat.mod_lt _ (by decide)
  by_cases split : r < 12
  · let b := 6*t-1
    have h2 : b.gcd 2 = 1 := by rw [Nat.gcd_comm b 2, Nat.gcd_rec, show b%2=1 by dsimp [b]; omega]; decide
    have h3 : b.gcd 3 = 1 := by rw [Nat.gcd_comm b 3, Nat.gcd_rec, show b%3=2 by dsimp [b]; omega]; decide
    exact outer_paste seed (corners17 (m := r+6) (by omega) (by omega)) (by dsimp [b]; omega)
      h2 h3 (by dsimp [b]; omega) (by dsimp [b]; omega)
  · let b := 6*t+1
    have h2 : b.gcd 2 = 1 := by rw [Nat.gcd_comm b 2, Nat.gcd_rec, show b%2=1 by dsimp [b]; omega]; decide
    have h3 : b.gcd 3 = 1 := by rw [Nat.gcd_comm b 3, Nat.gcd_rec, show b%3=1 by dsimp [b]; omega]; decide
    exact outer_paste seed (corners29 (m := r-6) (by omega) (by omega)) (by dsimp [b]; omega)
      h2 h3 (by dsimp [b]; omega) (by dsimp [b]; omega)

end OMA.QueenConstruction

open OMA.QueenConstruction in
theorem OMA.solution : type_of% @OMA.S_oeis_a260113.main := by
  intro n hn
  constructor
  · apply realize
    rcases lt_or_ge n 216 with h|h
    · exact small_boards hn h
    · exact large_boards_using host6 corners17 corners29 h
  · rintro k ⟨s,hs,rfl⟩
    exact OMA.Queens.upper hs
