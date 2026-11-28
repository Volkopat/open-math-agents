import OMAReductions.R_Erdos617_erdos_617_R1_H3_R1
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Step Erdos617.erdos_617.R1.H3.R1.H1: the r = 6 single-graph statement on 37 vertices.
Greedy (Furedi-type) partition by minimum-degree vertices, stability of the 6m-vertex
extremal structures, and a degree-sum bound.
The induced-neighbourhood framework (rel, homogeneous, bound, part, arcs and their lemmas,
fromBool, edge_account) is reused from the merged proof of the sibling step
Erdos617.erdos_617.R1.H1 (r = 4) by MakisChristou, as extended in our proof of
Erdos617.erdos_617.R1.H2 (r = 5). Written with Claude Code (AI-assisted). -/
namespace Graph617c
namespace Graph617n
def capT (d : ℕ) : ℕ :=
  if d ≤ 5 then d * (d - 1) else if d = 6 then 20 else if d = 7 then 32 else d * (d - 1)
def f1 (n : ℕ) : ℕ := if n ≤ 6 then n * (n - 1) else 10000
def f2 (n : ℕ) : ℕ := if 13 ≤ n then 10000 else
  [0, 0, 0, 2, 4, 8, 12, 18, 24, 32, 40, 50, 60].getD n 0
def f3 (n : ℕ) : ℕ :=
  [0, 0, 0, 0, 2, 4, 6, 10, 14, 18, 24, 30, 36, 44, 52, 60, 70, 80, 90, 134, 144, 168, 198, 230, 264, 300, 338, 378, 420, 464, 510, 558, 608, 660, 714, 770, 828].getD n 0
def f4 (n : ℕ) : ℕ :=
  [0, 0, 0, 0, 0, 2, 4, 6, 8, 12, 16, 20, 24, 30, 36, 42, 48, 56, 64, 72, 80, 90, 100, 110, 120, 164, 174, 196, 210, 232, 240, 270, 288, 320, 340, 374, 396].getD n 0
def f5 (n : ℕ) : ℕ :=
  [0, 0, 0, 0, 0, 0, 2, 4, 6, 8, 10, 14, 18, 22, 26, 30, 36, 42, 48, 54, 60, 68, 76, 84, 92, 100, 110, 120, 130, 140, 150, 194, 204, 226, 240, 260, 270].getD n 0
abbrev chk (g f : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ d < n, f n ≤ d * n ∨ f n + capT d ≤ 2 * (d * d) + g (n - 1 - d)
abbrev frc (g : ℕ → ℕ) (n a : ℕ) (p : ℕ → Prop) : Prop :=
  ∀ d < n, d * n ≤ a → g (n - 1 - d) + 2 * (d * d) ≤ a + capT d → p d
theorem chk2 : ∀ n < 13, chk f1 f2 n := by decide
theorem chk3 : ∀ n < 37, n ≠ 19 → n ≠ 20 → chk f2 f3 n := by decide
theorem chk4 : ∀ n < 37, n ≠ 25 → chk f3 f4 n := by decide
theorem chk5 : ∀ n < 37, n ≠ 31 → chk f4 f5 n := by decide
theorem frcT3 : frc f2 19 132 (fun d => d = 6) := by decide
theorem frcU3 : frc f2 20 143 (fun d => d = 7) := by decide
theorem frcS3 : frc f2 18 110 (fun d => d = 5 ∨ d = 6) := by decide
theorem frcT4 : frc f3 25 163 (fun d => d = 6) := by decide
theorem frcS4 : frc f3 24 140 (fun d => d = 5) := by decide
theorem frcT5 : frc f4 31 193 (fun d => d = 6) := by decide
theorem frcS5 : frc f4 30 170 (fun d => d = 5) := by decide
theorem frcT6 : frc f5 37 222 (fun d => d = 6) := by decide
end Graph617n
open Finset
abbrev V := Fin 37
abbrev Vertices := Finset V
variable (G : SimpleGraph V)
open scoped Classical
noncomputable section


private def rel (b : Bool) (x y : V) : Prop := if b then G.Adj x y else ¬ G.Adj x y
private lemma rel_sym {b x y} (h : rel G b x y) : rel G b y x := by
  cases b <;> simp_all [rel, G.adj_comm]
private def homogeneous (b : Bool) (S : Vertices) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → rel G b x y
private def bound (b : Bool) (S : Vertices) (k : ℕ) : Prop :=
  ∀ T ⊆ S, homogeneous G b T → T.card ≤ k
private def part (b : Bool) (S : Vertices) (x : V) : Vertices :=
  S.filter (fun y => y ≠ x ∧ rel G b x y)
private lemma in_part {b S x y} :
    y ∈ part G b S x ↔ y ∈ S ∧ y ≠ x ∧ rel G b x y := mem_filter
private lemma part_sub (b S x) : part G b S x ⊆ S := filter_subset _ _
private lemma self_out (b S x) : x ∉ part G b S x := by simp [part]
private lemma bound_mono {b S T k} (h : bound G b S k) (ht : T ⊆ S) :
    bound G b T k := fun U hu => h U (hu.trans ht)
private lemma homog_mono {b S T} (h : homogeneous G b S) (ht : T ⊆ S) :
    homogeneous G b T := fun x hx y hy => h x (ht hx) y (ht hy)
private lemma homog_insert {b S x} (h : homogeneous G b S) (hx : ∀ y ∈ S, rel G b x y) :
    homogeneous G b (insert x S) := by
  intro u hu v hv hn
  rcases mem_insert.mp hu with rfl | huS <;> rcases mem_insert.mp hv with rfl | hvS
  · exact (hn rfl).elim
  · exact hx v hvS
  · exact rel_sym G (hx u huS)
  · exact h u huS v hvS hn
private lemma bound_part {b S k x} (h : bound G b S (k+1)) (hx : x ∈ S) :
    bound G b (part G b S x) k := by
  intro T ht hh
  have hs : x ∉ T := fun hxt => self_out G b S x (ht hxt)
  have h₁ := h (insert x T) (insert_subset hx (ht.trans (part_sub G b S x)))
    (homog_insert G hh (fun y hy => (in_part G |>.mp (ht hy)).2.2))
  rw [card_insert_of_notMem hs] at h₁
  omega
private lemma homog_of_bound_one {b S} (h : bound G (!b) S 1) : homogeneous G b S := by
  intro x hx y hy hn
  by_contra hf
  have h' : rel G (!b) x y := by cases b <;> simp_all [rel]
  have hs : homogeneous G (!b) {y} := by
    intro i hi j hj hij
    simp only [mem_singleton] at hi hj
    exact (hij (hi.trans hj.symm)).elim
  have hh := h {x,y} (insert_subset hx (singleton_subset_iff.mpr hy))
    (homog_insert G hs (by simpa using h'))
  simp [hn] at hh
private lemma part_sizes {S x} (hx : x ∈ S) :
    (part G true S x).card + (part G false S x).card + 1 = S.card := by
  have hdis : Disjoint (part G true S x) (part G false S x) := by
    rw [disjoint_left]
    intro y h₁ h₂
    exact ((in_part G |>.mp h₂).2.2 : ¬ G.Adj x y) ((in_part G |>.mp h₁).2.2)
  have hu : part G true S x ∪ part G false S x = S.erase x := by
    ext y
    simp only [mem_union, in_part, mem_erase, rel, Bool.false_eq_true, if_false, if_true]
    tauto
  rw [← card_union_of_disjoint hdis, hu, card_erase_of_mem hx]
  have := card_pos.mpr (show S.Nonempty from ⟨x,hx⟩)
  omega
private def arcs (S T : Vertices) : ℕ := ∑ x ∈ S, (part G true T x).card
private lemma part_true_eq (T x) : part G true T x = T.filter (G.Adj x) := by
  ext y
  simp only [in_part, mem_filter, rel, if_true]
  exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,h.2.ne.symm,h.2⟩⟩
private lemma arcs_sum (S T) :
    arcs G S T = ∑ x ∈ S, ∑ y ∈ T, if G.Adj x y then 1 else 0 := by
  simp only [arcs, part_true_eq, card_eq_sum_ones, sum_filter]
private lemma arcs_sym (S T) : arcs G S T = arcs G T S := by
  rw [arcs_sum, arcs_sum, sum_comm]
  simp only [G.adj_comm]
private lemma arcs_add_left {S T : Vertices} (h : Disjoint S T) (U) :
    arcs G (S ∪ T) U = arcs G S U + arcs G T U := sum_union h
private lemma arcs_add_right {S T : Vertices} (h : Disjoint S T) (U) :
    arcs G U (S ∪ T) = arcs G U S + arcs G U T := by
  rw [arcs_sym, arcs_add_left G h, arcs_sym G S, arcs_sym G T]
private lemma arcs_floor {S T : Vertices} {k : ℕ}
    (h : ∀ x ∈ S, k ≤ (part G true T x).card) : S.card * k ≤ arcs G S T := by
  simpa [arcs] using (sum_le_sum h)
private lemma arcs_ceiling {S T : Vertices} {k : ℕ}
    (h : ∀ x ∈ S, (part G true T x).card ≤ k) : arcs G S T ≤ S.card * k := by
  simpa [arcs] using (sum_le_sum h)
private lemma arcs_card (S T) :
    arcs G S T = ((S ×ˢ T).filter (fun p => G.Adj p.1 p.2)).card := by
  rw [arcs_sum, card_eq_sum_ones, sum_filter, sum_product]
private lemma arcs_even (S) : Even (arcs G S S) := by
  have H := (G.induce (↑S : Set V)).two_mul_card_edgeFinset
  rw [arcs_card]
  let f : ((↑S : Set V) × (↑S : Set V)) → (V × V) := fun p => (p.1.1, p.2.1)
  have hcard : (univ.filter (fun p : (↑S : Set V) × (↑S : Set V) =>
      (G.induce (↑S : Set V)).Adj p.1 p.2)).card =
      ((S ×ˢ S).filter (fun p => G.Adj p.1 p.2)).card := by
    apply card_bij (fun p _ => f p)
    · intro p hp
      exact mem_filter.mpr ⟨mem_product.mpr ⟨p.1.2,p.2.2⟩,(mem_filter.mp hp).2⟩
    · intro p hp q hq h
      exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
    · rintro ⟨x,y⟩ h
      obtain ⟨hm,ha⟩ := mem_filter.mp h
      obtain ⟨hx,hy⟩ := mem_product.mp hm
      exact ⟨(⟨x,hx⟩,⟨y,hy⟩),mem_filter.mpr ⟨mem_univ _,ha⟩,rfl⟩
  rw [← hcard, ← H]
  exact even_two_mul _

private lemma part_mono {S T} (h : S ⊆ T) (b x) : part G b S x ⊆ part G b T x := by
  intro y hy
  obtain ⟨hy,hn,hr⟩ := (in_part G).mp hy
  exact (in_part G).mpr ⟨h hy,hn,hr⟩
private lemma part_sizes_out {S x} (hx : x ∉ S) :
    (part G true S x).card + (part G false S x).card = S.card := by
  have he (b) : part G b (insert x S) x = part G b S x := by
    ext y
    simp only [in_part, mem_insert]
    tauto
  have h := part_sizes G (mem_insert_self x S)
  rw [he, he, card_insert_of_notMem hx] at h
  omega
private lemma clique_arcs {S} (hs : homogeneous G true S) :
    arcs G S S = S.card * (S.card - 1) := by
  unfold arcs
  calc
    _ = ∑ _ ∈ S, (S.card - 1) := by
      apply sum_congr rfl
      intro x hx
      have h : part G true S x = S.erase x := by
        ext y
        constructor
        · intro hy
          obtain ⟨hm, hn, _⟩ := (in_part G).mp hy
          exact mem_erase.mpr ⟨hn,hm⟩
        · intro hy
          obtain ⟨hn,hm⟩ := mem_erase.mp hy
          exact (in_part G).mpr ⟨hm,hn,hs x hx y hm hn.symm⟩
      rw [h,card_erase_of_mem hx]
    _ = _ := by simp
private lemma arcs_singleton (x T) : arcs G {x} T = (part G true T x).card := by simp [arcs]
private lemma arcs_diag_single (x) : arcs G {x} {x} = 0 := by simp [arcs_singleton,part]
private lemma arcs_partition {S T : Vertices} (h : Disjoint S T) :
    arcs G (S ∪ T) (S ∪ T) = arcs G S S + arcs G T T + 2 * arcs G S T := by
  rw [arcs_add_left G h,arcs_add_right G h,arcs_add_right G h,arcs_sym G T S]
  omega
private lemma partition (S : Vertices) {x} (hx : x ∈ S) :
    Disjoint (insert x (part G true S x)) (part G false S x) ∧
      insert x (part G true S x) ∪ part G false S x = S := by
  constructor
  · rw [disjoint_left]
    intro y hy hy'
    obtain ⟨_,hn,hna⟩ := (in_part G).mp hy'
    rcases mem_insert.mp hy with rfl | hm
    · exact hn rfl
    · exact hna ((in_part G).mp hm).2.2
  · ext y
    simp only [mem_union,mem_insert,in_part,rel,if_true,Bool.false_eq_true,if_false]
    by_cases he : y = x
    · subst y
      simp [hx]
    · tauto

private lemma parts_disj (S x) : Disjoint (part G true S x) (part G false S x) := by
  rw [disjoint_left]
  intro y hy hz
  exact ((in_part G).mp hz).2.2 ((in_part G).mp hy).2.2
private lemma whole_edges {A B S : Vertices} (h : Disjoint A B) (hu : A ∪ B = S) :
    arcs G A S + arcs G B B ≤ arcs G S S := by
  subst S
  rw [arcs_partition G h, arcs_add_right G h]
  omega
private lemma cap_add (S x) : (insert x (part G true S x)).card = (part G true S x).card+1 :=
  card_insert_of_notMem (self_out G true S x)
private lemma star_count (S x) :
    arcs G {x} (part G true S x) = (part G true S x).card := by
  rw [arcs_singleton]
  congr 1
  ext y
  simp only [in_part]
  tauto
private lemma splits_at {S x} (hx : x ∈ S) :
    arcs G S S =
      (2 * (part G true S x).card + arcs G (part G true S x) (part G true S x)) +
      arcs G (part G false S x) (part G false S x) +
      2 * arcs G (part G true S x) (part G false S x) := by
  obtain ⟨hd,he⟩ := partition G S hx
  have hdis : Disjoint {x} (part G true S x) := disjoint_singleton_left.mpr (self_out G true S x)
  have hz : arcs G {x} (part G false S x) = 0 := by
    rw [arcs_singleton]
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    obtain ⟨hm,_,ha⟩ := (in_part G).mp hy
    exact ((in_part G).mp hm).2.2 ha
  have h := arcs_partition G hd
  rw [he, ← singleton_union, arcs_partition G hdis, arcs_add_left G hdis,
      arcs_diag_single, star_count, hz] at h
  omega
private lemma row_split {S x} (hx : x ∈ S) :
    arcs G (part G true S x) S = (part G true S x).card +
      arcs G (part G true S x) (part G true S x) +
      arcs G (part G true S x) (part G false S x) := by
  obtain ⟨hd,he⟩ := partition G S hx
  have h := arcs_add_right G hd (part G true S x)
  have hdis : Disjoint {x} (part G true S x) := disjoint_singleton_left.mpr (self_out G true S x)
  rw [he, ← singleton_union, arcs_add_right G hdis, arcs_sym G _ {x},star_count] at h
  omega
private lemma extract {b S k} (h : ¬ bound G b S k) :
    ∃ T ⊆ S, T.card = k+1 ∧ homogeneous G b T := by
  unfold bound at h
  push Not at h
  obtain ⟨U,hu,hh,hn⟩ := h
  obtain ⟨T,ht,htn⟩ := exists_subset_card_eq (show k+1 ≤ U.card by omega)
  exact ⟨T,ht.trans hu,htn,homog_mono G hh ht⟩
private lemma row_le {S T x} (hx : x ∈ S) : (part G true T x).card ≤ arcs G S T :=
  single_le_sum (f := fun z => (part G true T z).card) (fun _ _ => Nat.zero_le _) hx
private lemma no_cross {S T} (h : arcs G S T = 0) {x y} (hx : x ∈ S) (hy : y ∈ T) :
    ¬ G.Adj x y := by
  intro ha
  have hh : y ∈ part G true T x := (in_part G).mpr ⟨hy,ha.ne.symm,ha⟩
  have := card_pos.mpr (show (part G true T x).Nonempty from ⟨y,hh⟩)
  have := row_le G (T := T) hx
  omega
private lemma anti_union {S T} (hs : homogeneous G false S) (ht : homogeneous G false T)
    (h : ∀ x ∈ S, ∀ y ∈ T, ¬G.Adj x y) : homogeneous G false (S ∪ T) := by
  intro x hx y hy hn
  rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
  · exact hs x hx y hy hn
  · exact h x hx y hy
  · exact fun ha => h y hy x hx ha.symm
  · exact ht x hx y hy hn

private lemma homog_singleton (b) (y : V) : homogeneous G b {y} := by
  intro i hi j hj hij
  simp only [mem_singleton] at hi hj
  exact (hij (hi.trans hj.symm)).elim

private lemma indep_pair {u w : V} (h : ¬ G.Adj u w) : homogeneous G false {u, w} :=
  homog_insert G (homog_singleton G false w)
    (fun y hy => by rw [mem_singleton.mp hy]; exact h)

private lemma part_union_card {b} {P Q : Vertices} (h : Disjoint P Q) (u) :
    (part G b (P ∪ Q) u).card = (part G b P u).card + (part G b Q u).card := by
  unfold part
  rw [filter_union, card_union_of_disjoint (disjoint_filter_filter h)]

private lemma deg_split {S x u} (hx : x ∈ S) (hu : u ∈ part G true S x) :
    (part G true S u).card = (part G true (part G true S x) u).card +
      (part G true (part G false S x) u).card + 1 := by
  obtain ⟨hd, he⟩ := partition G S hx
  have h1 := part_union_card G (b := true) hd u
  rw [he] at h1
  have hxu : G.Adj x u := ((in_part G).mp hu).2.2
  have hadj : G.Adj u x := (G.adj_comm x u).mp hxu
  have h2 : (part G true (insert x (part G true S x)) u).card =
      (part G true (part G true S x) u).card + 1 := by
    have : part G true (insert x (part G true S x)) u =
        insert x (part G true (part G true S x) u) := by
      ext y
      simp only [in_part, mem_insert]
      constructor
      · rintro ⟨hy | hy, hne, hr⟩
        · left; exact hy
        · right; exact ⟨hy, hne, hr⟩
      · rintro (hy | ⟨hy, hne, hr⟩)
        · rw [hy]; exact ⟨Or.inl rfl, ((in_part G).mp hu).2.1.symm, hadj⟩
        · exact ⟨Or.inr hy, hne, hr⟩
    rw [this, card_insert_of_notMem]
    intro hmem
    exact self_out G true S x (part_sub G _ _ _ hmem)
  omega

private lemma quad {a b p q : V} (hab : ¬G.Adj a b) (hpq : ¬G.Adj p q) (hap : ¬G.Adj a p)
    (haq : ¬G.Adj a q) (hbp : ¬G.Adj b p) (hbq : ¬G.Adj b q) :
    homogeneous G false {p, q, a, b} := by
  refine homog_insert G (homog_insert G (indep_pair G hab) ?_) ?_
  · intro y hy
    rcases mem_insert.mp hy with h | h
    · rw [h]; exact fun h' => haq ((G.adj_comm _ _).mp h')
    · rw [mem_singleton.mp h]; exact fun h' => hbq ((G.adj_comm _ _).mp h')
  · intro y hy
    rcases mem_insert.mp hy with h | h
    · rw [h]; exact hpq
    rcases mem_insert.mp h with h | h
    · rw [h]; exact fun h' => hap ((G.adj_comm _ _).mp h')
    · rw [mem_singleton.mp h]; exact fun h' => hbp ((G.adj_comm _ _).mp h')

private lemma quad_card {a b p q : V} (hab : a ≠ b) (hpq : p ≠ q) (hpa : p ≠ a) (hpb : p ≠ b)
    (hqa : q ≠ a) (hqb : q ≠ b) : ({p, q, a, b} : Vertices).card = 4 := by
  rw [card_insert_of_notMem (by simp [hpq, hpa, hpb]),
    card_insert_of_notMem (by simp [hqa, hqb]), card_pair hab]

private lemma two_le_arcs {N A : Vertices} {a b : V} (ha : a ∈ N) (hb : b ∈ N) (hne : a ≠ b) :
    (part G true A a).card + (part G true A b).card ≤ arcs G N A := by
  have h : ∑ z ∈ ({a, b} : Vertices), (part G true A z).card ≤ arcs G N A := by
    unfold arcs
    apply sum_le_sum_of_subset
    intro z hz
    rcases mem_insert.mp hz with h | h
    · rw [h]; exact ha
    · rw [mem_singleton.mp h]; exact hb
  rwa [sum_pair hne] at h
private lemma sum_parts (N : Vertices) {t} (ht : t ∈ N) (f : V → ℕ) :
    ∑ z ∈ N, f z = f t + ∑ z ∈ part G true N t, f z + ∑ z ∈ part G false N t, f z := by
  obtain ⟨hd, he⟩ := partition G N ht
  have := sum_union (f := f) hd
  rw [he, sum_insert (self_out G true N t)] at this
  omega

private lemma all_eq_of_le {s : Vertices} {f : V → ℕ} {n : ℕ} (hle : ∀ z ∈ s, f z ≤ n)
    (hs : s.card * n ≤ ∑ z ∈ s, f z) : ∀ z ∈ s, f z = n := by
  intro z hz
  by_contra hne
  have hlt : f z < n := lt_of_le_of_ne (hle z hz) hne
  have := sum_lt_sum hle ⟨z, hz, hlt⟩
  simp only [sum_const, smul_eq_mul] at this
  omega

private lemma all_eq_of_ge {s : Vertices} {f : V → ℕ} {n : ℕ} (hge : ∀ z ∈ s, n ≤ f z)
    (hs : ∑ z ∈ s, f z ≤ s.card * n) : ∀ z ∈ s, f z = n := by
  intro z hz
  by_contra hne
  have hlt : n < f z := lt_of_le_of_ne (hge z hz) (fun h => hne h.symm)
  have := sum_lt_sum hge ⟨z, hz, hlt⟩
  simp only [sum_const, smul_eq_mul] at this
  omega

private lemma deg_split_false {S x y} (hx : x ∈ S) (hy : y ∈ part G false S x) :
    (part G true S y).card = (part G true (part G true S x) y).card +
      (part G true (part G false S x) y).card := by
  obtain ⟨hd, he⟩ := partition G S hx
  have h1 := part_union_card G (b := true) hd y
  rw [he] at h1
  have hxy : ¬G.Adj x y := ((in_part G).mp hy).2.2
  have : part G true (insert x (part G true S x)) y = part G true (part G true S x) y := by
    ext z
    simp only [in_part, mem_insert]
    constructor
    · rintro ⟨hz | hz, hne, hr⟩
      · exfalso
        rw [hz] at hr
        have hr' : G.Adj y x := hr
        exact hxy ((G.adj_comm _ _).mp hr')
      · exact ⟨hz, hne, hr⟩
    · rintro ⟨hz, hne, hr⟩
      exact ⟨Or.inr hz, hne, hr⟩
  rw [this] at h1
  exact h1

private lemma clique_deg {K} (hcl : homogeneous G true K) {y} (hy : y ∈ K) :
    (part G true K y).card = K.card - 1 := by
  have h : part G true K y = K.erase y := by
    ext z
    constructor
    · intro hz
      obtain ⟨hm, hn, _⟩ := (in_part G).mp hz
      exact mem_erase.mpr ⟨hn, hm⟩
    · intro hz
      obtain ⟨hn, hm⟩ := mem_erase.mp hz
      exact (in_part G).mpr ⟨hm, hn, hcl y hy z hm hn.symm⟩
  rw [h, card_erase_of_mem hy]

/-- ordered-pair count of a 7-set is at most 32, i.e. every 7 vertices span at most 16 edges. -/
private def sparse : Prop := ∀ S : Vertices, S.card = 7 → arcs G S S ≤ 32

private def K6 (Q : Vertices) : Prop := Q.card = 6 ∧ homogeneous G true Q

private lemma clique_le_six (hf : sparse G) {S} (h : homogeneous G true S) : S.card ≤ 6 := by
  by_contra! hn
  obtain ⟨Y,hy,hY⟩ := exists_subset_card_eq (show 7 ≤ S.card by omega)
  have := hf Y hY
  rw [clique_arcs G (homog_mono G h hy), hY] at this
  omega

private lemma k6_exit (hf : sparse G) {Q} (hQ : K6 G Q) {x} (hx : x ∉ Q) :
    (part G true Q x).card ≤ 1 := by
  obtain ⟨hQ, hcl⟩ := hQ
  have hdis : Disjoint {x} Q := disjoint_singleton_left.mpr hx
  have hsize : ({x} ∪ Q).card = 7 := by rw [card_union_of_disjoint hdis, card_singleton, hQ]
  have h := hf _ hsize
  rw [arcs_partition G hdis, arcs_diag_single, arcs_singleton, clique_arcs G hcl, hQ] at h
  omega

/-- the complement graph: `part G false` is `part Gᶜ true`, so all `arcs` lemmas apply to
non-adjacency counts. -/
private lemma part_compl (T : Vertices) (x : V) : part Gᶜ true T x = part G false T x := by
  ext y
  simp only [in_part, rel, if_true, Bool.false_eq_true, if_false, SimpleGraph.compl_adj]
  constructor
  · rintro ⟨h1, h2, _, h4⟩; exact ⟨h1, h2, h4⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun e => h2 e.symm, h3⟩

/-- non-adjacent ordered pairs inside a 7-set: at least 10. -/
private lemma sparse_compl (hf : sparse G) {S : Vertices} (hS : S.card = 7) :
    10 ≤ arcs Gᶜ S S := by
  have h := hf S hS
  have e : arcs G S S + arcs Gᶜ S S = S.card * (S.card - 1) := by
    unfold arcs
    rw [← sum_add_distrib]
    calc _ = ∑ _x ∈ S, (S.card - 1) := by
          apply sum_congr rfl
          intro x hx
          rw [part_compl]
          have := part_sizes G hx
          omega
      _ = _ := by simp
  rw [hS] at e
  omega

/- Level 2 (second formalizer): B2, G2, G4. All helpers are prefixed `L2_`. -/

private lemma L2_arcsc (A B : Vertices) :
    arcs Gᶜ A B = ∑ x ∈ A, (part G false B x).card := by
  unfold arcs
  exact sum_congr rfl (fun x _ => by rw [part_compl])

private lemma L2_compl_sum (S : Vertices) :
    arcs G S S + arcs Gᶜ S S = S.card * (S.card - 1) := by
  unfold arcs
  rw [← sum_add_distrib]
  calc _ = ∑ _x ∈ S, (S.card - 1) := by
        apply sum_congr rfl
        intro x hx
        rw [part_compl]
        have := part_sizes G hx
        omega
    _ = _ := by simp

private lemma L2_clique_c {K : Vertices} (h : homogeneous G true K) : arcs Gᶜ K K = 0 := by
  have h1 := L2_compl_sum G K
  rw [clique_arcs G h] at h1
  omega

private lemma L2_nadj {T : Vertices} {x y : V} (h : y ∈ part G false T x) : ¬ G.Adj x y :=
  ((in_part G).mp h).2.2

private lemma L2_clique_part {K : Vertices} (h : homogeneous G true K) {x : V} (hx : x ∈ K) :
    part G false K x = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  obtain ⟨hm, hn, _⟩ := (in_part G).mp hy
  exact L2_nadj G hy (h x hx y hm hn.symm)

private lemma L2_card_sdiff {A S : Vertices} (h : A ⊆ S) : A.card + (S \ A).card = S.card := by
  rw [← card_union_of_disjoint disjoint_sdiff, union_sdiff_of_subset h]

private lemma L2_tri {S : Vertices} (hi : bound G false S 2) {x y z : V} (hx : x ∈ S)
    (hy : y ∈ S) (hz : z ∈ S) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (h1 : ¬ G.Adj x y)
    (h2 : ¬ G.Adj x z) (h3 : ¬ G.Adj y z) : False := by
  have hh : homogeneous G false {x, y, z} := by
    refine homog_insert G (indep_pair G h3) ?_
    intro w hw
    rcases mem_insert.mp hw with h | h
    · rw [h]; exact h1
    · rw [mem_singleton.mp h]; exact h2
  have hs : ({x, y, z} : Vertices) ⊆ S := by
    intro w hw
    rcases mem_insert.mp hw with h | h
    · rw [h]; exact hx
    rcases mem_insert.mp h with h | h
    · rw [h]; exact hy
    · rw [mem_singleton.mp h]; exact hz
  have hc : ({x, y, z} : Vertices).card = 3 := by
    rw [card_insert_of_notMem (by simp [hxy, hxz]), card_pair hyz]
  have := hi _ hs hh
  omega

/-- two non-adjacent vertices have no common non-neighbour (no independent triple). -/
private lemma L2_disj {S I : Vertices} (hi : bound G false S 2) (hI : I ⊆ S) {x y : V}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y) (hna : ¬ G.Adj x y) :
    (part G false I x).card + (part G false I y).card ≤ I.card := by
  have hd : Disjoint (part G false I x) (part G false I y) := by
    rw [disjoint_left]
    intro z hz1 hz2
    obtain ⟨hm, hn1, _⟩ := (in_part G).mp hz1
    obtain ⟨_, hn2, _⟩ := (in_part G).mp hz2
    exact L2_tri G hi hx hy (hI hm) hxy (Ne.symm hn1) (Ne.symm hn2) hna (L2_nadj G hz1)
      (L2_nadj G hz2)
  rw [← card_union_of_disjoint hd]
  exact card_le_card (union_subset (part_sub G _ _ _) (part_sub G _ _ _))

private lemma L2_nbr_clique {S : Vertices} (hi : bound G false S 2) {x : V} (hx : x ∈ S) :
    homogeneous G true (part G false S x) :=
  homog_of_bound_one G (b := true) (bound_part G hi hx)

private lemma L2_deg {S : Vertices} {k : ℕ} (hi : bound G false S 2) (hb : bound G true S k)
    {x : V} (hx : x ∈ S) : (part G false S x).card ≤ k :=
  hb _ (part_sub G _ _ _) (L2_nbr_clique G hi hx)

private lemma L2_small {S : Vertices} {k : ℕ} (hi : bound G false S 2) (hb : bound G true S k) :
    arcs Gᶜ S S ≤ S.card * k :=
  arcs_ceiling Gᶜ (fun x hx => by rw [part_compl]; exact L2_deg G hi hb hx)

private lemma L2_noK6 {S : Vertices} (hK : ∀ Q ⊆ S, Q.card = 6 → ¬ homogeneous G true Q) :
    bound G true S 5 := by
  intro T hT hh
  by_contra hn
  obtain ⟨Q, hQ, hQc⟩ := exists_subset_card_eq (show 6 ≤ T.card by omega)
  exact hK Q (hQ.trans hT) hQc (homog_mono G hh hQ)

private lemma L2_r33 {N : Vertices} (hi : bound G false N 2) (hb : bound G true N 2) :
    N.card ≤ 5 := by
  rcases N.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · rw [h]; simp
  · have h1 := part_sizes G hx
    have h2 := L2_deg G hi hb hx
    have h3 : homogeneous G false (part G true N x) :=
      homog_of_bound_one G (b := false) (bound_part G hb hx)
    have h4 := hi _ (part_sub G _ _ _) h3
    omega

private lemma L2_ramsey {S : Vertices} (hi : bound G false S 2) (hb : bound G true S 3) :
    S.card ≤ 9 := by
  rcases S.eq_empty_or_nonempty with h | ⟨x, hx⟩
  · rw [h]; simp
  · have h1 := part_sizes G hx
    have h2 := L2_deg G hi hb hx
    have h3 := L2_r33 G (bound_mono G hi (part_sub G true S x)) (bound_part G hb hx)
    omega

/-- outside a K6 everything is pairwise adjacent. -/
private lemma L2_k6 (hf : sparse G) {S Q : Vertices} (hi : bound G false S 2) (hQS : Q ⊆ S)
    (hQ : K6 G Q) : homogeneous G true (S \ Q) := by
  intro u hu w hw hne
  obtain ⟨huS, huQ⟩ := mem_sdiff.mp hu
  obtain ⟨hwS, hwQ⟩ := mem_sdiff.mp hw
  show G.Adj u w
  by_contra hna
  have h1 := L2_disj G hi hQS huS hwS hne hna
  have h2 := part_sizes_out G (S := Q) huQ
  have h3 := part_sizes_out G (S := Q) hwQ
  have h4 := k6_exit G hf hQ huQ
  have h5 := k6_exit G hf hQ hwQ
  have h6 := hQ.1
  omega

/-- 7-set `I + u + w` around a 5-clique `I`. -/
private lemma L2_pair (hf : sparse G) {I : Vertices} (hI : homogeneous G true I) (hc : I.card = 5)
    {u w : V} (hu : u ∉ I) (hw : w ∉ I) (huw : u ≠ w) :
    (part G true I u).card + (part G true I w).card ≤ 6 ∧
    (G.Adj u w → (part G true I u).card + (part G true I w).card ≤ 5) := by
  have hd : Disjoint ({u, w} : Vertices) I := by
    rw [disjoint_left]
    intro z hz hzI
    rcases mem_insert.mp hz with h | h
    · rw [h] at hzI; exact hu hzI
    · rw [mem_singleton.mp h] at hzI; exact hw hzI
  have hsize : (({u, w} : Vertices) ∪ I).card = 7 := by
    rw [card_union_of_disjoint hd, card_pair huw, hc]
  have h := hf _ hsize
  rw [arcs_partition G hd, clique_arcs G hI, hc] at h
  have e : arcs G {u, w} I = (part G true I u).card + (part G true I w).card := by
    unfold arcs; rw [sum_pair huw]
  rw [e] at h
  refine ⟨by omega, fun ha => ?_⟩
  have e2 : arcs G {u, w} {u, w} =
      (part G true {u, w} u).card + (part G true {u, w} w).card := by
    unfold arcs; rw [sum_pair huw]
  have p1 : w ∈ part G true {u, w} u := (in_part G).mpr ⟨by simp, huw.symm, ha⟩
  have p2 : u ∈ part G true {u, w} w := (in_part G).mpr ⟨by simp, huw, ha.symm⟩
  have q1 := card_pos.mpr ⟨w, p1⟩
  have q2 := card_pos.mpr ⟨u, p2⟩
  omega

private def L2_low (S I : Vertices) : Vertices :=
  (S \ I).filter (fun v => 3 ≤ (part G true I v).card)
private def L2_high (S I : Vertices) : Vertices :=
  (S \ I).filter (fun v => (part G true I v).card ≤ 2)

private lemma L2_mem_low {S I : Vertices} {v : V} :
    v ∈ L2_low G S I ↔ (v ∈ S ∧ v ∉ I) ∧ 3 ≤ (part G true I v).card := by
  unfold L2_low; rw [mem_filter, mem_sdiff]
private lemma L2_mem_high {S I : Vertices} {v : V} :
    v ∈ L2_high G S I ↔ (v ∈ S ∧ v ∉ I) ∧ (part G true I v).card ≤ 2 := by
  unfold L2_high; rw [mem_filter, mem_sdiff]
private lemma L2_low_sub (S I : Vertices) : L2_low G S I ⊆ S :=
  fun _ h => ((L2_mem_low G).mp h).1.1
private lemma L2_high_sub (S I : Vertices) : L2_high G S I ⊆ S :=
  fun _ h => ((L2_mem_high G).mp h).1.1

private lemma L2_split (S I : Vertices) :
    (L2_low G S I).card + (L2_high G S I).card = (S \ I).card := by
  have hd : Disjoint (L2_low G S I) (L2_high G S I) := by
    rw [disjoint_left]
    intro v h1 h2
    have := ((L2_mem_low G).mp h1).2
    have := ((L2_mem_high G).mp h2).2
    omega
  have hu : L2_low G S I ∪ L2_high G S I = S \ I := by
    ext v
    rw [mem_union, L2_mem_low, L2_mem_high, mem_sdiff]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      by_cases h3 : 3 ≤ (part G true I v).card
      · exact Or.inl ⟨h, h3⟩
      · exact Or.inr ⟨h, by omega⟩
  rw [← card_union_of_disjoint hd, hu]

private lemma L2_low_key (hf : sparse G) {S I : Vertices} (hI : homogeneous G true I)
    (hc : I.card = 5) {u w : V} (hu : u ∈ L2_low G S I) (hw : w ∈ L2_low G S I) (hne : u ≠ w) :
    ¬ G.Adj u w ∧ (part G true I u).card = 3 := by
  obtain ⟨⟨_, hu2⟩, hu3⟩ := (L2_mem_low G).mp hu
  obtain ⟨⟨_, hw2⟩, hw3⟩ := (L2_mem_low G).mp hw
  obtain ⟨p1, p2⟩ := L2_pair G hf hI hc hu2 hw2 hne
  refine ⟨fun ha => ?_, by omega⟩
  have := p2 ha
  omega

private lemma L2_low_indep (hf : sparse G) {S I : Vertices} (hI : homogeneous G true I)
    (hc : I.card = 5) : homogeneous G false (L2_low G S I) :=
  fun _ hu _ hw hne => (L2_low_key G hf hI hc hu hw hne).1

private lemma L2_high_clique {S I : Vertices} (hi : bound G false S 2) (hIS : I ⊆ S)
    (hc : I.card = 5) : homogeneous G true (L2_high G S I) := by
  intro u hu w hw hne
  obtain ⟨⟨hu1, hu2⟩, hu3⟩ := (L2_mem_high G).mp hu
  obtain ⟨⟨hw1, hw2⟩, hw3⟩ := (L2_mem_high G).mp hw
  show G.Adj u w
  by_contra hna
  have h1 := L2_disj G hi hIS hu1 hw1 hne hna
  have h2 := part_sizes_out G (S := I) hu2
  have h3 := part_sizes_out G (S := I) hw2
  omega

private lemma L2_high_disj (S I : Vertices) : Disjoint I (L2_high G S I) := by
  rw [disjoint_left]
  intro z hz hzJ
  exact ((L2_mem_high G).mp hzJ).1.2 hz

/-- `S = J + I + a + b`, `I` a 5-clique, `J` a clique, `a`, `b` non-adjacent with two
non-neighbours each in `I`. -/
private lemma L2_two {S I J : Vertices} {a b : V} (hi : bound G false S 2)
    (hb : bound G true S 5) (hI : homogeneous G true I) (hc : I.card = 5)
    (hJ : homogeneous G true J) (hdIJ : Disjoint I J) (haI : a ∉ I) (hbI : b ∉ I) (haJ : a ∉ J)
    (hbJ : b ∉ J) (hab : a ≠ b) (hna : ¬ G.Adj a b) (hS : S = J ∪ (I ∪ {a, b}))
    (hda : (part G false I a).card = 2) (hdb : (part G false I b).card = 2) :
    arcs Gᶜ S S + 2 * arcs Gᶜ {a, b} J ≤ 10 * J.card + 10 := by
  have hdIP : Disjoint I ({a, b} : Vertices) := by
    rw [disjoint_right]
    intro z hz hzI
    rcases mem_insert.mp hz with h | h
    · rw [h] at hzI; exact haI hzI
    · rw [mem_singleton.mp h] at hzI; exact hbI hzI
  have hdJP : Disjoint J ({a, b} : Vertices) := by
    rw [disjoint_right]
    intro z hz hzJ
    rcases mem_insert.mp hz with h | h
    · rw [h] at hzJ; exact haJ hzJ
    · rw [mem_singleton.mp h] at hzJ; exact hbJ hzJ
  have hdJT : Disjoint J (I ∪ {a, b}) := by
    rw [disjoint_union_right]; exact ⟨hdIJ.symm, hdJP⟩
  have hJS : J ⊆ S := by rw [hS]; exact subset_union_left
  have hTS : I ∪ {a, b} ⊆ S := by rw [hS]; exact subset_union_right
  have haS : a ∈ S := hTS (mem_union_right _ (by simp))
  have hbS : b ∈ S := hTS (mem_union_right _ (by simp))
  have hTc : (I ∪ {a, b}).card = 7 := by rw [card_union_of_disjoint hdIP, hc, card_pair hab]
  have e1 : arcs Gᶜ S S = arcs Gᶜ J J + arcs Gᶜ (I ∪ {a, b}) (I ∪ {a, b}) +
      2 * arcs Gᶜ J (I ∪ {a, b}) := by
    rw [hS]; exact arcs_partition Gᶜ hdJT
  have e2 := arcs_partition Gᶜ hdIP
  have e3 := arcs_add_right Gᶜ hdIP J
  have zI := L2_clique_c G hI
  have zJ := L2_clique_c G hJ
  have pp : arcs Gᶜ {a, b} {a, b} ≤ 2 := by
    have h := arcs_ceiling Gᶜ (S := {a, b}) (T := {a, b}) (k := 1) (fun x hx => by
      have h1 := part_sizes Gᶜ hx
      rw [card_pair hab] at h1
      omega)
    rw [card_pair hab] at h
    omega
  have ip : arcs Gᶜ I {a, b} = 4 := by
    rw [arcs_sym, L2_arcsc, sum_pair hab, hda, hdb]
  have sJ : arcs Gᶜ {a, b} J = arcs Gᶜ J {a, b} := arcs_sym Gᶜ _ _
  have dTa : 3 ≤ (part G false (I ∪ {a, b}) a).card := by
    rw [part_union_card G hdIP, hda]
    have h1 : b ∈ part G false {a, b} a := (in_part G).mpr ⟨by simp, hab.symm, hna⟩
    have h2 := card_pos.mpr ⟨b, h1⟩
    omega
  have dTb : 3 ≤ (part G false (I ∪ {a, b}) b).card := by
    rw [part_union_card G hdIP, hdb]
    have h1 : a ∈ part G false {a, b} b :=
      (in_part G).mpr ⟨by simp, hab, fun e => hna e.symm⟩
    have h2 := card_pos.mpr ⟨a, h1⟩
    omega
  have per : ∀ h ∈ J,
      (part G false (I ∪ {a, b}) h).card + (part G false {a, b} h).card ≤ 5 := by
    intro h hhJ
    have hhS := hJS hhJ
    have hha : h ≠ a := ne_of_mem_of_not_mem hhJ haJ
    have hhb : h ≠ b := ne_of_mem_of_not_mem hhJ hbJ
    have hbd := L2_deg G hi hb hhS
    have hmono := card_le_card (part_mono G hTS false h)
    by_cases h1 : G.Adj h a
    · by_cases h2 : G.Adj h b
      · have he : part G false {a, b} h = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro z hz
          have hr := L2_nadj G hz
          rcases mem_insert.mp ((in_part G).mp hz).1 with e | e
          · rw [e] at hr; exact hr h1
          · rw [mem_singleton.mp e] at hr; exact hr h2
        rw [he, card_empty]; omega
      · have q := L2_disj G hi hTS hhS hbS hhb h2
        have hsub : part G false {a, b} h ⊆ {b} := by
          intro z hz
          have hr := L2_nadj G hz
          rcases mem_insert.mp ((in_part G).mp hz).1 with e | e
          · rw [e] at hr; exact (hr h1).elim
          · exact e
        have h3 := card_le_card hsub
        rw [card_singleton] at h3
        omega
    · by_cases h2 : G.Adj h b
      · have q := L2_disj G hi hTS hhS haS hha h1
        have hsub : part G false {a, b} h ⊆ {a} := by
          intro z hz
          have hr := L2_nadj G hz
          rcases mem_insert.mp ((in_part G).mp hz).1 with e | e
          · exact mem_singleton.mpr e
          · rw [mem_singleton.mp e] at hr; exact (hr h2).elim
        have h3 := card_le_card hsub
        rw [card_singleton] at h3
        omega
      · exact (L2_tri G hi hhS haS hbS hha hhb hab h1 h2 hna).elim
  have sm : arcs Gᶜ J (I ∪ {a, b}) + arcs Gᶜ J {a, b} ≤ J.card * 5 := by
    rw [L2_arcsc, L2_arcsc, ← sum_add_distrib]
    calc _ ≤ ∑ _h ∈ J, 5 := sum_le_sum per
      _ = J.card * 5 := by simp
  omega

/-- `S = J + I + a` with `I`, `J` disjoint 5-cliques. -/
private lemma L2_one {S I J : Vertices} {a : V} (hi : bound G false S 2) (hb : bound G true S 5)
    (hI : homogeneous G true I) (hc : I.card = 5) (hJ : homogeneous G true J) (hJc : J.card = 5)
    (hdIJ : Disjoint I J) (haI : a ∉ I) (haJ : a ∉ J) (hS : S = J ∪ (I ∪ {a})) :
    arcs Gᶜ S S ≤ 52 := by
  have hdIa : Disjoint I ({a} : Vertices) := disjoint_singleton_right.mpr haI
  have hdJT : Disjoint J (I ∪ {a}) := by
    rw [disjoint_union_right]; exact ⟨hdIJ.symm, disjoint_singleton_right.mpr haJ⟩
  have hJS : J ⊆ S := by rw [hS]; exact subset_union_left
  have hTS : I ∪ {a} ⊆ S := by rw [hS]; exact subset_union_right
  have hIS : I ⊆ S := subset_union_left.trans hTS
  have haS : a ∈ S := hTS (mem_union_right _ (mem_singleton_self a))
  have e1 : arcs Gᶜ S S = arcs Gᶜ J J + arcs Gᶜ (I ∪ {a}) (I ∪ {a}) +
      2 * arcs Gᶜ J (I ∪ {a}) := by
    rw [hS]; exact arcs_partition Gᶜ hdJT
  have e2 := arcs_partition Gᶜ hdIa
  have e3 := arcs_add_right Gᶜ hdIa J
  have zI := L2_clique_c G hI
  have zJ := L2_clique_c G hJ
  have za : arcs Gᶜ {a} {a} = 0 := arcs_diag_single Gᶜ a
  have b1 : arcs Gᶜ I S ≤ I.card * 5 :=
    arcs_ceiling Gᶜ (fun x hx => by rw [part_compl]; exact L2_deg G hi hb (hIS hx))
  have b2 : arcs Gᶜ I S = arcs Gᶜ I J + (arcs Gᶜ I I + arcs Gᶜ I {a}) := by
    rw [hS, arcs_add_right Gᶜ hdJT, arcs_add_right Gᶜ hdIa]
  have s1 : arcs Gᶜ I J = arcs Gᶜ J I := arcs_sym Gᶜ I J
  have d2 : arcs Gᶜ J {a} = (part G false J a).card := by
    rw [arcs_sym, arcs_singleton, part_compl]
  by_cases hex : ∃ h ∈ J, ¬ G.Adj h a
  · obtain ⟨h, hhJ, hha⟩ := hex
    have hhS := hJS hhJ
    have hne : h ≠ a := ne_of_mem_of_not_mem hhJ haJ
    have q1 := L2_disj G hi hIS hhS haS hne hha
    have q2 : (part G false S h).card ≤ (part G false I h).card + 1 := by
      rw [hS, part_union_card G hdJT, part_union_card G hdIa, L2_clique_part G hJ hhJ,
        card_empty]
      have h3 := card_le_card (part_sub G false {a} h)
      rw [card_singleton] at h3
      omega
    have q3 : arcs Gᶜ J S ≤ (part G false S h).card + 20 := by
      have h4 : arcs Gᶜ J S = (part G false S h).card + arcs Gᶜ (J.erase h) S := by
        rw [L2_arcsc, L2_arcsc]
        exact (add_sum_erase J _ hhJ).symm
      have h5 : arcs Gᶜ (J.erase h) S ≤ (J.erase h).card * 5 :=
        arcs_ceiling Gᶜ (fun x hx => by
          rw [part_compl]; exact L2_deg G hi hb (hJS (mem_of_mem_erase hx)))
      rw [card_erase_of_mem hhJ, hJc] at h5
      omega
    have q4 : arcs Gᶜ J S = arcs Gᶜ J J + (arcs Gᶜ J I + arcs Gᶜ J {a}) := by
      rw [hS, arcs_add_right Gᶜ hdJT, arcs_add_right Gᶜ hdIa]
    have q5 : arcs Gᶜ I {a} = (part G false I a).card := by
      rw [arcs_sym, arcs_singleton, part_compl]
    omega
  · have hall : ∀ h ∈ J, G.Adj h a := fun h hh => by
      by_contra hc'
      exact hex ⟨h, hh, hc'⟩
    have h0 : (part G false J a).card = 0 := by
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact L2_nadj G hz (hall z ((in_part G).mp hz).1).symm
    omega

private lemma L2_case2 (hf : sparse G) {S I : Vertices} (hi : bound G false S 2)
    (hb : bound G true S 5) (hIS : I ⊆ S) (hI : homogeneous G true I) (hc : I.card = 5)
    (hL : (L2_low G S I).card = 2) : arcs Gᶜ S S ≤ 52 := by
  obtain ⟨a, b, hab, hLe⟩ := card_eq_two.mp hL
  have haL : a ∈ L2_low G S I := by rw [hLe]; simp
  have hbL : b ∈ L2_low G S I := by rw [hLe]; simp
  obtain ⟨⟨haS, haI⟩, _⟩ := (L2_mem_low G).mp haL
  obtain ⟨⟨hbS, hbI⟩, _⟩ := (L2_mem_low G).mp hbL
  obtain ⟨hna, hga⟩ := L2_low_key G hf hI hc haL hbL hab
  obtain ⟨_, hgb⟩ := L2_low_key G hf hI hc hbL haL hab.symm
  have hda : (part G false I a).card = 2 := by
    have := part_sizes_out G (S := I) haI
    omega
  have hdb : (part G false I b).card = 2 := by
    have := part_sizes_out G (S := I) hbI
    omega
  have hJcl : homogeneous G true (L2_high G S I) := L2_high_clique G hi hIS hc
  have haJ : a ∉ L2_high G S I := fun h => by
    have := ((L2_mem_high G).mp h).2
    omega
  have hbJ : b ∉ L2_high G S I := fun h => by
    have := ((L2_mem_high G).mp h).2
    omega
  have hS : S = L2_high G S I ∪ (I ∪ {a, b}) := by
    ext z
    simp only [mem_union, mem_insert, mem_singleton]
    constructor
    · intro hz
      by_cases hzI : z ∈ I
      · exact Or.inr (Or.inl hzI)
      · by_cases h3 : 3 ≤ (part G true I z).card
        · have hzL : z ∈ L2_low G S I := (L2_mem_low G).mpr ⟨⟨hz, hzI⟩, h3⟩
          rw [hLe] at hzL
          rcases mem_insert.mp hzL with e | e
          · exact Or.inr (Or.inr (Or.inl e))
          · exact Or.inr (Or.inr (Or.inr (mem_singleton.mp e)))
        · exact Or.inl ((L2_mem_high G).mpr ⟨⟨hz, hzI⟩, by omega⟩)
    · rintro (h | h | h | h)
      · exact ((L2_mem_high G).mp h).1.1
      · exact hIS h
      · rw [h]; exact haS
      · rw [h]; exact hbS
  have hJc : (L2_high G S I).card ≤ 5 := hb _ (L2_high_sub G S I) hJcl
  have main := L2_two G hi hb hI hc hJcl (L2_high_disj G S I) haI hbI haJ hbJ hab hna hS hda hdb
  by_cases h5 : (L2_high G S I).card = 5
  · obtain ⟨p1, _⟩ := L2_pair G hf hJcl h5 haJ hbJ hab
    have e : arcs Gᶜ {a, b} (L2_high G S I) =
        (part G false (L2_high G S I) a).card + (part G false (L2_high G S I) b).card := by
      rw [L2_arcsc, sum_pair hab]
    have r1 := part_sizes_out G (S := L2_high G S I) haJ
    have r2 := part_sizes_out G (S := L2_high G S I) hbJ
    omega
  · omega

private lemma L2_case1 {S I : Vertices} (hi : bound G false S 2)
    (hb : bound G true S 5) (hIS : I ⊆ S) (hI : homogeneous G true I) (hc : I.card = 5)
    (hL : (L2_low G S I).card = 1) (hH : (L2_high G S I).card = 5) : arcs Gᶜ S S ≤ 52 := by
  obtain ⟨a, hLe⟩ := card_eq_one.mp hL
  have haL : a ∈ L2_low G S I := by rw [hLe]; exact mem_singleton_self a
  obtain ⟨⟨haS, haI⟩, ha3⟩ := (L2_mem_low G).mp haL
  have haJ : a ∉ L2_high G S I := fun h => by
    have := ((L2_mem_high G).mp h).2
    omega
  have hS : S = L2_high G S I ∪ (I ∪ {a}) := by
    ext z
    simp only [mem_union, mem_singleton]
    constructor
    · intro hz
      by_cases hzI : z ∈ I
      · exact Or.inr (Or.inl hzI)
      · by_cases h3 : 3 ≤ (part G true I z).card
        · have hzL : z ∈ L2_low G S I := (L2_mem_low G).mpr ⟨⟨hz, hzI⟩, h3⟩
          rw [hLe] at hzL
          exact Or.inr (Or.inr (mem_singleton.mp hzL))
        · exact Or.inl ((L2_mem_high G).mpr ⟨⟨hz, hzI⟩, by omega⟩)
    · rintro (h | h | h)
      · exact ((L2_mem_high G).mp h).1.1
      · exact hIS h
      · rw [h]; exact haS
  exact L2_one G hi hb hI hc (L2_high_clique G hi hIS hc) hH (L2_high_disj G S I) haI haJ hS

private lemma L2_five (hf : sparse G) {S I : Vertices} (hi : bound G false S 2)
    (hb : bound G true S 5) (hIS : I ⊆ S) (hI : homogeneous G true I) (hc : I.card = 5)
    (hn : 11 ≤ S.card) : arcs Gᶜ S S ≤ 52 := by
  have h1 := L2_split G S I
  have h2 := L2_card_sdiff hIS
  have h3 := hi _ (L2_low_sub G S I) (L2_low_indep G hf hI hc)
  have h4 := hb _ (L2_high_sub G S I) (L2_high_clique G hi hIS hc)
  by_cases hL : (L2_low G S I).card = 2
  · exact L2_case2 G hf hi hb hIS hI hc hL
  · exact L2_case1 G hi hb hIS hI hc (by omega) (by omega)

/-- 4-clique `I` in a 13-set without 5-cliques: two adjacent outside vertices cannot both have
exactly one non-neighbour in `I` (sum over the 7-sets `I + u + v + w`). -/
private lemma L2_four_pair (hf : sparse G) {S I : Vertices} (hi : bound G false S 2)
    (hb : bound G true S 4) (hn : S.card = 13) (hIS : I ⊆ S) (hI : homogeneous G true I)
    (hc : I.card = 4) {u v : V} (huS : u ∈ S) (hvS : v ∈ S) (huI : u ∉ I) (hvI : v ∉ I)
    (huv : u ≠ v) (ha : G.Adj u v) (hdu : (part G false I u).card = 1)
    (hdv : (part G false I v).card = 1) : False := by
  have hdIP : Disjoint I ({u, v} : Vertices) := by
    rw [disjoint_right]
    intro z hz hzI
    rcases mem_insert.mp hz with h | h
    · rw [h] at hzI; exact huI hzI
    · rw [mem_singleton.mp h] at hzI; exact hvI hzI
  have hPS : ({u, v} : Vertices) ⊆ S := by
    intro z hz
    rcases mem_insert.mp hz with h | h
    · rw [h]; exact huS
    · rw [mem_singleton.mp h]; exact hvS
  have hYS : I ∪ {u, v} ⊆ S := union_subset hIS hPS
  have hYc : (I ∪ {u, v}).card = 6 := by rw [card_union_of_disjoint hdIP, hc, card_pair huv]
  have hOc := L2_card_sdiff hYS
  have hSe : (I ∪ {u, v}) ∪ (S \ (I ∪ {u, v})) = S := union_sdiff_of_subset hYS
  have hdYO : Disjoint (I ∪ {u, v}) (S \ (I ∪ {u, v})) := disjoint_sdiff
  have hP : homogeneous G true {u, v} :=
    homog_insert G (homog_singleton G true v) (fun y hy => by
      rw [mem_singleton.mp hy]; exact ha)
  have zI := L2_clique_c G hI
  have zP := L2_clique_c G hP
  have ip : arcs Gᶜ {u, v} I = 2 := by rw [L2_arcsc, sum_pair huv, hdu, hdv]
  have sIP := arcs_sym Gᶜ I {u, v}
  have yy : arcs Gᶜ (I ∪ {u, v}) (I ∪ {u, v}) = 4 := by
    rw [arcs_partition Gᶜ hdIP]; omega
  have per : ∀ w ∈ S \ (I ∪ {u, v}), 3 ≤ (part Gᶜ true (I ∪ {u, v}) w).card := by
    intro w hw
    have hwY : w ∉ I ∪ {u, v} := (mem_sdiff.mp hw).2
    have hd : Disjoint (I ∪ {u, v}) ({w} : Vertices) := disjoint_singleton_right.mpr hwY
    have hsz : ((I ∪ {u, v}) ∪ {w}).card = 7 := by
      rw [card_union_of_disjoint hd, hYc, card_singleton]
    have h := sparse_compl G hf hsz
    rw [arcs_partition Gᶜ hd, yy, arcs_diag_single, arcs_sym, arcs_singleton] at h
    omega
  have fl := arcs_floor Gᶜ per
  have s1 := arcs_sym Gᶜ (S \ (I ∪ {u, v})) (I ∪ {u, v})
  have s2 := arcs_add_left Gᶜ hdIP (S \ (I ∪ {u, v}))
  have i1 : arcs Gᶜ I S ≤ I.card * 4 :=
    arcs_ceiling Gᶜ (fun x hx => by rw [part_compl]; exact L2_deg G hi hb (hIS hx))
  have i2 : arcs Gᶜ I S = arcs Gᶜ I I + arcs Gᶜ I {u, v} +
      arcs Gᶜ I (S \ (I ∪ {u, v})) := by
    have h := arcs_add_right Gᶜ hdYO I
    rw [hSe, arcs_add_right Gᶜ hdIP] at h
    exact h
  have p1 : arcs Gᶜ {u, v} S ≤ ({u, v} : Vertices).card * 4 :=
    arcs_ceiling Gᶜ (fun x hx => by rw [part_compl]; exact L2_deg G hi hb (hPS hx))
  have p2 : arcs Gᶜ {u, v} S = arcs Gᶜ {u, v} I + arcs Gᶜ {u, v} {u, v} +
      arcs Gᶜ {u, v} (S \ (I ∪ {u, v})) := by
    have h := arcs_add_right Gᶜ hdYO {u, v}
    rw [hSe, arcs_add_right Gᶜ hdIP] at h
    exact h
  rw [card_pair huv] at p1
  omega

private lemma L2_count {O : Vertices} {f : V → ℕ} (hO : O.card = 9) (hge : ∀ v ∈ O, 1 ≤ f v)
    (hsum : ∑ v ∈ O, f v ≤ 16) (hT : (O.filter (fun v => f v = 1)).card ≤ 2) :
    ∑ v ∈ O, f v = 16 ∧ ∀ v ∈ O, f v ≤ 2 := by
  obtain ⟨T, hTd⟩ : ∃ T, T = O.filter (fun v => f v = 1) := ⟨_, rfl⟩
  rw [← hTd] at hT
  have hsub : T ⊆ O := by rw [hTd]; exact filter_subset _ _
  have hRc := L2_card_sdiff hsub
  have hsplit := sum_sdiff (f := f) hsub
  have hT1 : ∑ v ∈ T, f v = T.card := by
    rw [card_eq_sum_ones]
    apply sum_congr rfl
    intro v hv
    rw [hTd] at hv
    exact (mem_filter.mp hv).2
  have hR2 : ∀ v ∈ O \ T, 2 ≤ f v := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := mem_sdiff.mp hv
    have h1 := hge v hv1
    have h2 : f v ≠ 1 := fun e => hv2 (by rw [hTd]; exact mem_filter.mpr ⟨hv1, e⟩)
    omega
  have hRs : (O \ T).card * 2 ≤ ∑ v ∈ O \ T, f v := by
    calc (O \ T).card * 2 = ∑ _v ∈ O \ T, 2 := by simp
      _ ≤ _ := sum_le_sum hR2
  have hall := all_eq_of_ge (s := O \ T) (f := f) (n := 2) hR2 (by omega)
  refine ⟨by omega, fun v hv => ?_⟩
  by_cases hvT : v ∈ T
  · rw [hTd] at hvT
    have := (mem_filter.mp hvT).2
    omega
  · have := hall v (mem_sdiff.mpr ⟨hv, hvT⟩)
    omega

private lemma L2_four_main (hf : sparse G) {S I : Vertices} (hi : bound G false S 2)
    (hb : bound G true S 4) (hn : S.card = 13) (hIS : I ⊆ S) (hI : homogeneous G true I)
    (hc : I.card = 4) :
    (∀ v ∈ S \ I, (part G false I v).card ≤ 2) ∧ ∀ i ∈ I, (part G false S i).card = 4 := by
  have hOc := L2_card_sdiff hIS
  have hSe : I ∪ (S \ I) = S := union_sdiff_of_subset hIS
  have hge : ∀ v ∈ S \ I, 1 ≤ (part G false I v).card := by
    intro v hv
    obtain ⟨hvS, hvI⟩ := mem_sdiff.mp hv
    by_contra h0
    have he : part G false I v = ∅ := card_eq_zero.mp (by omega)
    have hall : ∀ y ∈ I, rel G true v y := by
      intro y hy
      show G.Adj v y
      by_contra hna
      have hy' : y ∈ part G false I v :=
        (in_part G).mpr ⟨hy, ne_of_mem_of_not_mem hy hvI, hna⟩
      rw [he] at hy'
      exact (notMem_empty y) hy'
    have h5 := hb _ (insert_subset hvS hIS) (homog_insert G hI hall)
    rw [card_insert_of_notMem hvI] at h5
    omega
  have i1 : arcs Gᶜ I S ≤ I.card * 4 :=
    arcs_ceiling Gᶜ (fun x hx => by rw [part_compl]; exact L2_deg G hi hb (hIS hx))
  have i2 : arcs Gᶜ I S = arcs Gᶜ I I + arcs Gᶜ I (S \ I) := by
    have h := arcs_add_right Gᶜ (disjoint_sdiff : Disjoint I (S \ I)) I
    rw [hSe] at h
    exact h
  have zI := L2_clique_c G hI
  have s1 : arcs Gᶜ I (S \ I) = ∑ v ∈ S \ I, (part G false I v).card := by
    rw [arcs_sym, L2_arcsc]
  have hT1 : ((S \ I).filter (fun v => (part G false I v).card = 1)).card ≤ 2 := by
    apply hi _ ((filter_subset _ _).trans sdiff_subset)
    intro u hu v hv huv
    show ¬ G.Adj u v
    intro ha
    obtain ⟨hu1, hu2⟩ := mem_filter.mp hu
    obtain ⟨hv1, hv2⟩ := mem_filter.mp hv
    exact L2_four_pair G hf hi hb hn hIS hI hc (mem_sdiff.mp hu1).1 (mem_sdiff.mp hv1).1
      (mem_sdiff.mp hu1).2 (mem_sdiff.mp hv1).2 huv ha hu2 hv2
  obtain ⟨hs16, hle⟩ := L2_count (f := fun v => (part G false I v).card) (by omega) hge
    (by rw [← s1]; omega) hT1
  refine ⟨hle, ?_⟩
  have e : ∑ i ∈ I, (part G false S i).card = arcs Gᶜ I S := (L2_arcsc G I S).symm
  have hsum16 : I.card * 4 ≤ ∑ i ∈ I, (part G false S i).card := by omega
  exact all_eq_of_le (s := I) (f := fun i => (part G false S i).card) (n := 4)
    (fun z hz => L2_deg G hi hb (hIS hz)) hsum16

private lemma L2_four_final (hf : sparse G) {S I : Vertices} (hi : bound G false S 2)
    (hb : bound G true S 4) (hn : S.card = 13) (hIS : I ⊆ S) (hI : homogeneous G true I)
    (hc : I.card = 4) : False := by
  obtain ⟨i, hiI⟩ := card_pos.mp (by omega : 0 < I.card)
  have hiS := hIS hiI
  have h4 := (L2_four_main G hf hi hb hn hIS hI hc).2 i hiI
  have hcl := L2_nbr_clique G hi hiS
  have hsub := part_sub G false S i
  have hmem : i ∈ S \ part G false S i := mem_sdiff.mpr ⟨hiS, self_out G false S i⟩
  have h2 := (L2_four_main G hf hi hb hn hsub hcl h4).1 i hmem
  have hsub2 : part G false S i ⊆ part G false (part G false S i) i := by
    intro y hy
    exact (in_part G).mpr ⟨hy, ((in_part G).mp hy).2.1, ((in_part G).mp hy).2.2⟩
  have h3 := card_le_card hsub2
  omega

private lemma L2_thirteen (hf : sparse G) {S : Vertices} (hi : bound G false S 2)
    (hn : S.card = 13) : False := by
  by_cases h5 : bound G true S 5
  · by_cases h4 : bound G true S 4
    · by_cases h3 : bound G true S 3
      · have := L2_ramsey G hi h3
        omega
      · obtain ⟨I, hIS, hc, hI⟩ := extract G h3
        exact L2_four_final G hf hi h4 hn hIS hI hc
    · obtain ⟨I, hIS, hc, hI⟩ := extract G h4
      have h1 := L2_split G S I
      have h2 := L2_card_sdiff hIS
      have h3 := hi _ (L2_low_sub G S I) (L2_low_indep G hf hI hc)
      have h6 := h5 _ (L2_high_sub G S I) (L2_high_clique G hi hIS hc)
      omega
  · obtain ⟨Q, hQS, hc, hQ⟩ := extract G h5
    have h1 := clique_le_six G hf (L2_k6 G hf hi hQS ⟨hc, hQ⟩)
    have h2 := L2_card_sdiff hQS
    omega

/-- (B2) a good vertex set with independence number at most 2 has at most 12 vertices. -/
private theorem B2 (hf : sparse G) {S : Vertices} (hi : bound G false S 2) : S.card ≤ 12 := by
  by_contra hn
  obtain ⟨S', hS', hc⟩ := exists_subset_card_eq (show 13 ≤ S.card by omega)
  exact L2_thirteen G hf (bound_mono G hi hS') hc

/-- (G2) 12 vertices, independence number at most 2, no K6: at least 40 edges. -/
private theorem G2 (hf : sparse G) {S : Vertices} (hi : bound G false S 2) (hn : S.card = 12)
    (hK : ∀ Q ⊆ S, Q.card = 6 → ¬ homogeneous G true Q) : 80 ≤ arcs G S S := by
  have hb := L2_noK6 G hK
  have hs := L2_compl_sum G S
  rw [hn] at hs
  have key : arcs Gᶜ S S ≤ 52 := by
    by_cases h4 : bound G true S 4
    · have := L2_small G hi h4
      omega
    · obtain ⟨I, hIS, hc, hI⟩ := extract G h4
      exact L2_five G hf hi hb hIS hI hc (by omega)
  omega

/-- (G4) 11 vertices, independence number at most 2, no K6: at least 29 edges. -/
private theorem G4 (hf : sparse G) {S : Vertices} (hi : bound G false S 2) (hn : S.card = 11)
    (hK : ∀ Q ⊆ S, Q.card = 6 → ¬ homogeneous G true Q) : 58 ≤ arcs G S S := by
  have hb := L2_noK6 G hK
  have hs := L2_compl_sum G S
  rw [hn] at hs
  have key : arcs Gᶜ S S ≤ 52 := by
    by_cases h4 : bound G true S 4
    · have := L2_small G hi h4
      omega
    · obtain ⟨I, hIS, hc, hI⟩ := extract G h4
      exact L2_five G hf hi hb hIS hI hc (by omega)
  omega

open Graph617n

private lemma nbr_cap (hf : sparse G) (S x) :
    arcs G (part G true S x) (part G true S x) ≤ capT (part G true S x).card := by
  have triv : arcs G (part G true S x) (part G true S x) ≤
      (part G true S x).card * ((part G true S x).card - 1) := by
    apply arcs_ceiling
    intro z hz
    have hsub : part G true (part G true S x) z ⊆ (part G true S x).erase z := by
      intro y hy
      obtain ⟨hm, hn, _⟩ := (in_part G).mp hy
      exact mem_erase.mpr ⟨hn, hm⟩
    have := card_le_card hsub
    rw [card_erase_of_mem hz] at this
    exact this
  unfold capT
  split_ifs with h5 h6 h7
  · exact triv
  · have hd : Disjoint {x} (part G true S x) :=
      disjoint_singleton_left.mpr (self_out G true S x)
    have he : ({x} ∪ part G true S x).card = 7 := by
      rw [card_union_of_disjoint hd, card_singleton, h6]
    have h := hf _ he
    rw [arcs_partition G hd, arcs_diag_single, star_count, h6] at h
    omega
  · exact hf _ h7
  · exact triv

private lemma desc (hf : sparse G) {S : Vertices} {k : ℕ} (hi : bound G false S (k+1))
    (hne : S.Nonempty) :
    ∃ x ∈ S, (∀ z ∈ S, (part G true S x).card ≤ (part G true S z).card) ∧
      bound G false (part G false S x) k ∧
      (part G true S x).card + (part G false S x).card + 1 = S.card ∧
      S.card * (part G true S x).card ≤ arcs G S S ∧
      2 * ((part G true S x).card * (part G true S x).card) +
          arcs G (part G false S x) (part G false S x) ≤
        arcs G S S + arcs G (part G true S x) (part G true S x) ∧
      arcs G (part G true S x) (part G true S x) ≤ capT (part G true S x).card := by
  obtain ⟨x, hx, hmin⟩ := exists_min_image S (fun z => (part G true S z).card) hne
  refine ⟨x, hx, hmin, bound_part G hi hx, part_sizes G hx, arcs_floor G hmin, ?_,
    nbr_cap G hf S x⟩
  have hNS : (part G true S x).card * (part G true S x).card ≤ arcs G (part G true S x) S :=
    arcs_floor G (fun z hz => hmin z (part_sub G true S x hz))
  have hrow := row_split G hx
  have hall := splits_at G hx
  generalize (part G true S x).card * (part G true S x).card = q at *
  omega

private lemma pick {Q U : Vertices} (hU : arcs G U Q < Q.card) :
    ∃ y ∈ Q, ∀ u ∈ U, ¬ G.Adj u y := by
  obtain ⟨y, hy, hny⟩ := exists_mem_notMem_of_card_lt_card
    (show (U.biUnion (fun u => part G true Q u)).card < Q.card from
      lt_of_le_of_lt card_biUnion_le hU)
  exact ⟨y, hy, fun u hu ha =>
    hny (mem_biUnion.mpr ⟨u, hu, (in_part G).mpr ⟨hy, ha.ne.symm, ha⟩⟩)⟩

private lemma grow (hf : sparse G) : ∀ (qs : List Vertices) (I : Vertices),
    homogeneous G false I →
    (∀ Q ∈ qs, K6 G Q ∧ Disjoint I Q ∧ arcs G I Q + qs.length ≤ 6) →
    qs.Pairwise Disjoint →
    ∃ J, I ⊆ J ∧ homogeneous G false J ∧ J.card = I.card + qs.length ∧
      ∀ z ∈ J, z ∈ I ∨ ∃ Q ∈ qs, z ∈ Q
  | [], I, hI, _, _ => ⟨I, Subset.rfl, hI, by simp, fun z hz => Or.inl hz⟩
  | Q :: qs, I, hI, hq, hp => by
      obtain ⟨hQ6, hQd, hQa⟩ := hq Q (by simp)
      rw [List.length_cons] at hQa
      obtain ⟨y, hy, hn⟩ := pick G (show arcs G I Q < Q.card by rw [hQ6.1]; omega)
      have hyI : y ∉ I := fun h => disjoint_left.mp hQd h hy
      have hh : homogeneous G false (insert y I) :=
        homog_insert G hI (fun u hu ha => hn u hu ((G.adj_comm y u).mp ha))
      have hp' := List.pairwise_cons.mp hp
      obtain ⟨J, hIJ, hJ, hJc, hJm⟩ := grow hf qs (insert y I) hh
        (fun Q' hQ' => by
          obtain ⟨a, b, c⟩ := hq Q' (List.mem_cons_of_mem _ hQ')
          have hyQ' : y ∉ Q' := fun hyQ' => disjoint_left.mp (hp'.1 Q' hQ') hy hyQ'
          refine ⟨a, ?_, ?_⟩
          · rw [disjoint_insert_left]; exact ⟨hyQ', b⟩
          · have e : arcs G (insert y I) Q' = (part G true Q' y).card + arcs G I Q' := by
              unfold arcs; rw [sum_insert hyI]
            have := k6_exit G hf a hyQ'
            rw [List.length_cons] at c
            omega)
        hp'.2
      refine ⟨J, (subset_insert y I).trans hIJ, hJ, ?_, ?_⟩
      · rw [hJc, card_insert_of_notMem hyI, List.length_cons]; omega
      · intro z hz
        rcases hJm z hz with h | ⟨Q', hQ', hz'⟩
        · rcases mem_insert.mp h with h | h
          · exact Or.inr ⟨Q, by simp, h ▸ hy⟩
          · exact Or.inl h
        · exact Or.inr ⟨Q', List.mem_cons_of_mem _ hQ', hz'⟩

private lemma F4 (hf : sparse G) {u w : V} (hne : u ≠ w) (hna : ¬ G.Adj u w)
    (qs : List Vertices) (hlen : qs.length ≤ 4) (hq : ∀ Q ∈ qs, K6 G Q ∧ u ∉ Q ∧ w ∉ Q)
    (hp : qs.Pairwise Disjoint) :
    ∃ J, homogeneous G false J ∧ J.card = 2 + qs.length ∧
      ∀ z ∈ J, z = u ∨ z = w ∨ ∃ Q ∈ qs, z ∈ Q := by
  obtain ⟨J, -, hJ, hJc, hJm⟩ := grow G hf qs {u, w} (indep_pair G hna)
    (fun Q hQ => by
      obtain ⟨a, b, c⟩ := hq Q hQ
      refine ⟨a, ?_, ?_⟩
      · rw [disjoint_left]
        intro z hz hzQ
        rcases mem_insert.mp hz with h | h
        · exact b (h ▸ hzQ)
        · exact c (mem_singleton.mp h ▸ hzQ)
      · have e : arcs G {u, w} Q = (part G true Q u).card + (part G true Q w).card := by
          unfold arcs; rw [sum_pair hne]
        have := k6_exit G hf a b
        have := k6_exit G hf a c
        omega) hp
  refine ⟨J, hJ, by rw [hJc, card_pair hne], ?_⟩
  intro z hz
  rcases hJm z hz with h | h
  · rcases mem_insert.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (mem_singleton.mp h))
  · exact Or.inr (Or.inr h)

private lemma not_clique {S : Vertices} (h : ¬ homogeneous G true S) :
    ∃ u ∈ S, ∃ w ∈ S, u ≠ w ∧ ¬ G.Adj u w := by
  unfold homogeneous at h
  push Not at h
  obtain ⟨p, hp, q, hq, hne, hna⟩ := h
  exact ⟨p, hp, q, hq, hne, fun h => hna h⟩

private lemma lower_step (hf : sparse G) (g f : ℕ → ℕ) (k : ℕ)
    (hprev : ∀ A : Vertices, bound G false A k → g A.card ≤ arcs G A A)
    {S : Vertices} (hi : bound G false S (k+1))
    (hchk : chk g f S.card) (h0 : f 0 = 0) : f S.card ≤ arcs G S S := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp [h0]
  obtain ⟨x, hx, -, hb, hsz, hdeg, hacc, hcap⟩ := desc G hf hi hne
  have hg := hprev _ hb
  generalize hd : (part G true S x).card = d at *
  have hA : (part G false S x).card = S.card - 1 - d := by omega
  rw [hA] at hg
  rcases hchk d (by omega) with h | h
  · rw [Nat.mul_comm] at h; omega
  · omega

/-- the minimum-degree vertex with all the greedy data, and the numeric constraint on it. -/
private lemma forced (hf : sparse G) (g : ℕ → ℕ) (k : ℕ)
    (hprev : ∀ A : Vertices, bound G false A k → g A.card ≤ arcs G A A)
    {S : Vertices} (hi : bound G false S (k+1)) (hne : S.Nonempty) {a : ℕ}
    (ha : arcs G S S ≤ a) (p : ℕ → Prop) (hfrc : frc g S.card a p) :
    ∃ x ∈ S, (∀ z ∈ S, (part G true S x).card ≤ (part G true S z).card) ∧
      bound G false (part G false S x) k ∧
      (part G true S x).card + (part G false S x).card + 1 = S.card ∧
      2 * ((part G true S x).card * (part G true S x).card) +
          arcs G (part G false S x) (part G false S x) ≤
        arcs G S S + arcs G (part G true S x) (part G true S x) ∧
      arcs G (part G true S x) (part G true S x) ≤ capT (part G true S x).card ∧
      p (part G true S x).card := by
  obtain ⟨x, hx, hmin, hb, hsz, hdeg, hacc, hcap⟩ := desc G hf hi hne
  refine ⟨x, hx, hmin, hb, hsz, hacc, hcap, ?_⟩
  have hg := hprev _ hb
  generalize hd : (part G true S x).card = d at *
  have hA : (part G false S x).card = S.card - 1 - d := by omega
  rw [hA] at hg
  exact hfrc d (by omega) (by rw [Nat.mul_comm]; omega) (by omega)

private lemma lower1 (hf : sparse G) (A : Vertices) (hi : bound G false A 1) :
    f1 A.card ≤ arcs G A A := by
  have hcl : homogeneous G true A := homog_of_bound_one G (b := true) hi
  have h6 := clique_le_six G hf hcl
  unfold f1
  rw [if_pos h6, clique_arcs G hcl]

private lemma lower2 (hf : sparse G) (A : Vertices) (hi : bound G false A 2) :
    f2 A.card ≤ arcs G A A := by
  have h12 := B2 G hf hi
  exact lower_step G hf f1 f2 1 (lower1 G hf) hi (chk2 _ (by omega)) (by decide)

private lemma two_k6 (hf : sparse G) {S Q : Vertices} (hi : bound G false S 2)
    (hn : S.card = 12) (hQ : K6 G Q) (hQS : Q ⊆ S) : K6 G (S \ Q) := by
  refine ⟨by rw [card_sdiff_of_subset hQS, hn, hQ.1], ?_⟩
  by_contra hcl
  obtain ⟨u, hu, w, hw, hne, hna⟩ := not_clique G hcl
  obtain ⟨J, hJ, hJc, hJm⟩ := F4 G hf hne hna [Q] (by simp)
    (by
      intro Q' hQ'
      rw [List.mem_singleton] at hQ'
      rw [hQ']
      exact ⟨hQ, (mem_sdiff.mp hu).2, (mem_sdiff.mp hw).2⟩)
    (List.pairwise_singleton _ _)
  have hsub : J ⊆ S := by
    intro z hz
    rcases hJm z hz with h | h | ⟨Q', hQ', hz'⟩
    · rw [h]; exact (mem_sdiff.mp hu).1
    · rw [h]; exact (mem_sdiff.mp hw).1
    · rw [List.mem_singleton] at hQ'
      rw [hQ'] at hz'
      exact hQS hz'
  have := hi J hsub hJ
  simp at hJc
  omega

private lemma U3 (hf : sparse G) {S : Vertices} (hi : bound G false S 3) (hn : S.card = 20) :
    144 ≤ arcs G S S := by
  by_contra hlt
  obtain ⟨x, hx, -, hb, hsz, hacc, hcap, hd⟩ := forced G hf f2 2 (lower2 G hf) hi
    (card_pos.mp (by omega)) (show arcs G S S ≤ 143 by omega) (fun d => d = 7)
    (by rw [hn]; exact frcU3)
  rw [hd] at hsz hacc hcap
  have hc7 : capT 7 = 32 := by decide
  rw [hc7] at hcap
  have hA12 : (part G false S x).card = 12 := by omega
  have hK : ¬ ∀ Q ⊆ part G false S x, Q.card = 6 → ¬ homogeneous G true Q := by
    intro hK
    have := G2 G hf hb hA12 hK
    omega
  push Not at hK
  obtain ⟨Q, hQA, hQ6, hQcl⟩ := hK
  have hQ : K6 G Q := ⟨hQ6, hQcl⟩
  have hQ' := two_k6 G hf hb hA12 hQ hQA
  have hNcl : ¬ homogeneous G true (part G true S x) := by
    intro h
    have := clique_le_six G hf h
    omega
  obtain ⟨u, hu, w, hw, hne, hna⟩ := not_clique G hNcl
  have hout : ∀ {z}, z ∈ part G true S x → ∀ {Q'}, Q' ⊆ part G false S x → z ∉ Q' :=
    fun hz _ hQ' h => disjoint_left.mp (parts_disj G S x) hz (hQ' h)
  obtain ⟨J, hJ, hJc, hJm⟩ := F4 G hf hne hna [Q, part G false S x \ Q] (by simp)
    (by
      intro Q' hQ'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ'
      rcases hQ' with h | h
      · rw [h]; exact ⟨hQ, hout hu hQA, hout hw hQA⟩
      · rw [h]; exact ⟨hQ', hout hu sdiff_subset, hout hw sdiff_subset⟩)
    (by simp [disjoint_sdiff])
  have hsub : J ⊆ S := by
    intro z hz
    rcases hJm z hz with h | h | ⟨Q', hQ', hz'⟩
    · rw [h]; exact part_sub G _ _ _ hu
    · rw [h]; exact part_sub G _ _ _ hw
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ'
      rcases hQ' with h | h
      · rw [h] at hz'; exact part_sub G _ _ _ (hQA hz')
      · rw [h] at hz'; exact part_sub G _ _ _ ((mem_sdiff.mp hz').1)
  have := hi J hsub hJ
  simp at hJc
  omega
private lemma four_set {S : Vertices} {x a b p q : V} (ha : a ∈ part G true S x)
    (hb : b ∈ part G true S x) (hp : p ∈ part G false S x) (hq : q ∈ part G false S x)
    (hab : a ≠ b) (hpq : p ≠ q) (nab : ¬G.Adj a b) (npq : ¬G.Adj p q) (nap : ¬G.Adj a p)
    (naq : ¬G.Adj a q) (nbp : ¬G.Adj b p) (nbq : ¬G.Adj b q) :
    ∃ J : Vertices, J ⊆ S ∧ homogeneous G false J ∧ J.card = 4 ∧
      ∀ z ∈ J, z = a ∨ z = b ∨ z = p ∨ z = q := by
  have hdj := parts_disj G S x
  have hne : ∀ {c e : V}, c ∈ part G false S x → e ∈ part G true S x → c ≠ e :=
    fun hc he h => disjoint_left.mp hdj he (h ▸ hc)
  refine ⟨{p, q, a, b}, ?_, quad G nab npq nap naq nbp nbq,
    quad_card hab hpq (hne hp ha) (hne hp hb) (hne hq ha) (hne hq hb), ?_⟩
  · intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with h | h | h | h <;> rw [h]
    · exact part_sub G _ _ _ hp
    · exact part_sub G _ _ _ hq
    · exact part_sub G _ _ _ ha
    · exact part_sub G _ _ _ hb
  · intro z hz
    simp only [mem_insert, mem_singleton] at hz
    tauto


private lemma arcs_le_full (S : Vertices) : arcs G S S ≤ S.card * (S.card - 1) := by
  apply arcs_ceiling
  intro z hz
  have hsub : part G true S z ⊆ S.erase z := by
    intro y hy
    obtain ⟨hm, hn, _⟩ := (in_part G).mp hy
    exact mem_erase.mpr ⟨hn, hm⟩
  have := card_le_card hsub
  rwa [card_erase_of_mem hz] at this

private lemma full_clique {S : Vertices} (h : S.card * (S.card - 1) ≤ arcs G S S) :
    homogeneous G true S := by
  have hsub : ∀ z, part G true S z ⊆ S.erase z := by
    intro z y hy
    obtain ⟨hm, hn, _⟩ := (in_part G).mp hy
    exact mem_erase.mpr ⟨hn, hm⟩
  have hle : ∀ z ∈ S, (part G true S z).card ≤ S.card - 1 := by
    intro z hz
    have := card_le_card (hsub z)
    rwa [card_erase_of_mem hz] at this
  unfold arcs at h
  have heq := all_eq_of_le hle h
  intro x hx y hy hne
  have e : part G true S x = S.erase x :=
    eq_of_subset_of_card_le (hsub x) (by rw [card_erase_of_mem hx, heq x hx])
  have hy' : y ∈ part G true S x := by rw [e]; exact mem_erase.mpr ⟨hne.symm, hy⟩
  exact ((in_part G).mp hy').2.2

private lemma arcs_mono_left {S T : Vertices} (h : S ⊆ T) (U : Vertices) :
    arcs G S U ≤ arcs G T U := by
  unfold arcs
  exact sum_le_sum_of_subset h

private lemma arcs_mono_right {S T : Vertices} (h : S ⊆ T) (U : Vertices) :
    arcs G U S ≤ arcs G U T := by
  rw [arcs_sym G U S, arcs_sym G U T]
  exact arcs_mono_left G h U

private lemma arcs_compl (S : Vertices) :
    arcs G S S + arcs Gᶜ S S = S.card * (S.card - 1) := by
  unfold arcs
  rw [← sum_add_distrib]
  calc _ = ∑ _x ∈ S, (S.card - 1) := by
        apply sum_congr rfl
        intro x hx
        rw [part_compl]
        have := part_sizes G hx
        omega
    _ = _ := by simp

private lemma iso_k6 {Q A : Vertices} (hQ : K6 G Q) (hQA : Q ⊆ A) {z : V} (hz : z ∈ Q)
    (hdeg : (part G true A z).card = 5) {p : V} (hp : p ∈ A) (hpQ : p ∉ Q) : ¬ G.Adj z p := by
  intro ha
  have hsub := part_mono G hQA true z
  have hc := clique_deg G hQ.2 hz
  have heq : part G true Q z = part G true A z :=
    eq_of_subset_of_card_le hsub (by rw [hdeg, hc, hQ.1])
  have hm : p ∈ part G true A z := (in_part G).mpr ⟨hp, ha.ne.symm, ha⟩
  rw [← heq] at hm
  exact hpQ ((in_part G).mp hm).1

private lemma free_of {A : Vertices} {u w z : V}
    (hz : z ∈ A \ (part G true A u ∪ part G true A w)) :
    z ∈ A ∧ ¬ G.Adj u z ∧ ¬ G.Adj w z := by
  obtain ⟨hzA, hzD⟩ := mem_sdiff.mp hz
  refine ⟨hzA, fun h => hzD (mem_union_left _ ((in_part G).mpr ⟨hzA, h.ne.symm, h⟩)),
    fun h => hzD (mem_union_right _ ((in_part G).mpr ⟨hzA, h.ne.symm, h⟩))⟩

private lemma free_card (A : Vertices) (u w : V) :
    A.card ≤ (A \ (part G true A u ∪ part G true A w)).card +
      ((part G true A u).card + (part G true A w).card) := by
  have h1 := card_sdiff_of_subset (union_subset (part_sub G true A u) (part_sub G true A w))
  have h2 := card_union_le (part G true A u) (part G true A w)
  omega

/-- for a non-adjacent pair u, w in the neighbourhood of x, the common non-neighbours below
form a clique when there is no independent 4-set. -/
private lemma coedge_clique {S : Vertices} {x u w : V} (hi : bound G false S 3)
    (hu : u ∈ part G true S x) (hw : w ∈ part G true S x) (hne : u ≠ w) (hna : ¬ G.Adj u w) :
    homogeneous G true (part G false S x \
      (part G true (part G false S x) u ∪ part G true (part G false S x) w)) := by
  by_contra hcl
  obtain ⟨p, hp, q, hq, hpq, npq⟩ := not_clique G hcl
  obtain ⟨hpA, nup, nwp⟩ := free_of G hp
  obtain ⟨hqA, nuq, nwq⟩ := free_of G hq
  obtain ⟨J, hJS, hJ, hJc, -⟩ := four_set G hu hw hpA hqA hne hpq hna npq nup nuq nwp nwq
  have := hi J hJS hJ
  omega

private lemma big_clique {R : Vertices} (h : homogeneous G true R) (h6 : 6 ≤ R.card) :
    ∃ Q ⊆ R, Q.card = 6 ∧ homogeneous G true Q := by
  obtain ⟨Q, hQ, hQ6⟩ := exists_subset_card_eq h6
  exact ⟨Q, hQ, hQ6, homog_mono G h hQ⟩

private lemma codeg_pair {N : Vertices} {u w : V} (hu : u ∈ N) (hw : w ∈ N) (hne : u ≠ w)
    (h10 : arcs Gᶜ N N ≤ 10) :
    (part G false N u).card + (part G false N w).card ≤ 6 := by
  have hsub : ({u, w} : Vertices) ⊆ N := by
    intro z hz
    rcases mem_insert.mp hz with h | h
    · rw [h]; exact hu
    · rw [mem_singleton.mp h]; exact hw
  have hd : Disjoint ({u, w} : Vertices) (N \ {u, w}) := disjoint_sdiff
  have hU : ({u, w} : Vertices) ∪ (N \ {u, w}) = N := union_sdiff_of_subset hsub
  have h1 := arcs_partition Gᶜ hd
  have h2 := arcs_add_right Gᶜ hd ({u, w} : Vertices)
  rw [hU] at h1 h2
  have h3 : arcs Gᶜ {u, w} N = (part G false N u).card + (part G false N w).card := by
    unfold arcs
    rw [sum_pair hne, part_compl, part_compl]
  have h4 := arcs_le_full Gᶜ ({u, w} : Vertices)
  rw [card_pair hne] at h4
  omega

private def Ppart (A : Vertices) (m : ℕ) : Prop :=
  ∃ qs : List Vertices, qs.length = m ∧ (∀ Q ∈ qs, K6 G Q ∧ Q ⊆ A) ∧ qs.Pairwise Disjoint ∧
    ∀ z ∈ A, ∃ Q ∈ qs, z ∈ Q

private def Xtype (A : Vertices) (m : ℕ) : Prop :=
  arcs G A A = 30 * m + 20 ∧ ∃ (qs : List Vertices) (E : Vertices), qs.length + 2 = m ∧
    E ⊆ A ∧ E.card = 12 ∧
    (∀ Q ∈ qs, K6 G Q ∧ Q ⊆ A ∧ Disjoint Q E ∧ ∀ z ∈ Q, (part G true A z).card = 5) ∧
    qs.Pairwise Disjoint ∧ (∀ Q ⊆ E, Q.card = 6 → ¬ homogeneous G true Q) ∧
    ∀ z ∈ A, z ∈ E ∨ ∃ Q ∈ qs, z ∈ Q

private def St (m : ℕ) : Prop :=
  ∀ A : Vertices, bound G false A m → A.card = 6 * m → arcs G A A ≤ 30 * m + 20 →
    Ppart G A m ∨ Xtype G A m

private lemma St1 : St G 1 := by
  intro A hi hn _
  left
  have hcl : homogeneous G true A := homog_of_bound_one G (b := true) hi
  exact ⟨[A], rfl, fun Q hQ => by
    rw [List.mem_singleton.mp hQ]; exact ⟨⟨by omega, hcl⟩, Subset.rfl⟩,
    List.pairwise_singleton _ _, fun z hz => ⟨A, by simp, hz⟩⟩

private lemma St2 (hf : sparse G) : St G 2 := by
  intro A hi hn he
  by_cases hK : ∀ Q ⊆ A, Q.card = 6 → ¬ homogeneous G true Q
  · right
    have := G2 G hf hi (by omega) hK
    exact ⟨by omega, [], A, rfl, Subset.rfl, by omega, by simp, List.Pairwise.nil, hK,
      fun z hz => Or.inl hz⟩
  · left
    push Not at hK
    obtain ⟨Q, hQA, hQ6, hQcl⟩ := hK
    have hQ : K6 G Q := ⟨hQ6, hQcl⟩
    have hQ' := two_k6 G hf hi (by omega) hQ hQA
    refine ⟨[Q, A \ Q], rfl, ?_, by simp [disjoint_sdiff], ?_⟩
    · intro Q' h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h
      · rw [h]; exact ⟨hQ, hQA⟩
      · rw [h]; exact ⟨hQ', sdiff_subset⟩
    · intro z hz
      by_cases hzQ : z ∈ Q
      · exact ⟨Q, by simp, hzQ⟩
      · exact ⟨A \ Q, by simp, mem_sdiff.mpr ⟨hz, hzQ⟩⟩

/-- F4 applied to a K6-partition of the non-neighbours: too large an independent set. -/
private lemma T_P (hf : sparse G) {m : ℕ} (hm : m ≤ 4) {S : Vertices} {x u w : V}
    (hi : bound G false S (m+1)) (hu : u ∈ part G true S x) (hw : w ∈ part G true S x)
    (hne : u ≠ w) (hna : ¬ G.Adj u w) (hP : Ppart G (part G false S x) m) : False := by
  obtain ⟨qs, hlen, hq, hp, -⟩ := hP
  have hout : ∀ {z}, z ∈ part G true S x → ∀ {Q'}, Q' ⊆ part G false S x → z ∉ Q' :=
    fun hz _ hQ' h => disjoint_left.mp (parts_disj G S x) hz (hQ' h)
  obtain ⟨J, hJ, hJc, hJm⟩ := F4 G hf hne hna qs (by omega)
    (fun Q hQ => ⟨(hq Q hQ).1, hout hu (hq Q hQ).2, hout hw (hq Q hQ).2⟩) hp
  have hsub : J ⊆ S := by
    intro z hz
    rcases hJm z hz with h | h | ⟨Q', hQ', hz'⟩
    · rw [h]; exact part_sub G _ _ _ hu
    · rw [h]; exact part_sub G _ _ _ hw
    · exact part_sub G _ _ _ ((hq Q' hQ').2 hz')
  have := hi J hsub hJ
  omega

private lemma St_d5 (hf : sparse G) {m : ℕ} (hm : m ≤ 4) (hSt : St G m) {A : Vertices}
    {y : V} (hi : bound G false A (m+1)) (hy : y ∈ A)
    (hb : bound G false (part G false A y) m) (hd : (part G true A y).card = 5)
    (hn : A.card = 6 * (m+1)) (he : arcs G A A ≤ 30 * (m+1) + 20)
    (hacc : 2 * ((part G true A y).card * (part G true A y).card) +
          arcs G (part G false A y) (part G false A y) ≤
        arcs G A A + arcs G (part G true A y) (part G true A y)) :
    Ppart G A (m+1) ∨ Xtype G A (m+1) := by
  have hsz := part_sizes G hy
  have hNN := arcs_le_full G (part G true A y)
  rw [hd] at hsz hacc hNN
  obtain ⟨hdBA, hBA⟩ := partition G A hy
  have hNy6 : (insert y (part G true A y)).card = 6 := by rw [cap_add, hd]
  have hNyA : insert y (part G true A y) ⊆ A := insert_subset hy (part_sub G _ _ _)
  have hin : ∀ z ∈ A, z ∉ part G false A y → z ∈ insert y (part G true A y) := by
    intro z hz hzB
    have : z ∈ insert y (part G true A y) ∪ part G false A y := by rw [hBA]; exact hz
    exact (mem_union.mp this).resolve_right hzB
  rcases hSt _ hb (by omega) (by omega) with hP | ⟨hBB, qs, E, hlen, hEB, hE12, hq, hp, hEK, hcov⟩
  · left
    have hNcl : homogeneous G true (part G true A y) := by
      by_contra hcl
      obtain ⟨u, hu, w, hw, hne, hna⟩ := not_clique G hcl
      exact T_P G hf hm hi hu hw hne hna hP
    obtain ⟨qs, hlen, hq, hp, hcov⟩ := hP
    have hK : K6 G (insert y (part G true A y)) :=
      ⟨hNy6, homog_insert G hNcl (fun z hz => ((in_part G).mp hz).2.2)⟩
    refine ⟨insert y (part G true A y) :: qs, by simp [hlen], ?_, ?_, ?_⟩
    · intro Q hQ
      rcases List.mem_cons.mp hQ with h | h
      · rw [h]; exact ⟨hK, hNyA⟩
      · exact ⟨(hq Q h).1, (hq Q h).2.trans (part_sub G _ _ _)⟩
    · exact List.pairwise_cons.mpr ⟨fun Q hQ => hdBA.mono_right (hq Q hQ).2, hp⟩
    · intro z hz
      by_cases hzB : z ∈ part G false A y
      · obtain ⟨Q, hQ, hzQ⟩ := hcov z hzB
        exact ⟨Q, List.mem_cons_of_mem _ hQ, hzQ⟩
      · exact ⟨_, by simp, hin z hz hzB⟩
  · right
    have hall := splits_at G hy
    rw [hd] at hall
    have hAA : arcs G A A = 30 * (m+1) + 20 := by omega
    have hNN20 : arcs G (part G true A y) (part G true A y) = 20 := by omega
    have hNB : arcs G (part G true A y) (part G false A y) = 0 := by omega
    have hNcl : homogeneous G true (part G true A y) := full_clique G (by rw [hd, hNN20])
    have hK : K6 G (insert y (part G true A y)) :=
      ⟨hNy6, homog_insert G hNcl (fun z hz => ((in_part G).mp hz).2.2)⟩
    have hcross : ∀ a ∈ insert y (part G true A y), ∀ b ∈ part G false A y, ¬ G.Adj a b := by
      intro a ha b hb'
      rcases mem_insert.mp ha with h | h
      · rw [h]; exact ((in_part G).mp hb').2.2
      · exact no_cross G hNB h hb'
    refine ⟨hAA, insert y (part G true A y) :: qs, E, by simp; omega,
      hEB.trans (part_sub G _ _ _), hE12, ?_, ?_, hEK, ?_⟩
    · intro Q hQ
      rcases List.mem_cons.mp hQ with h | h
      · rw [h]
        refine ⟨hK, hNyA, hdBA.mono_right hEB, ?_⟩
        intro z hz
        have h1 := part_union_card G (b := true) hdBA z
        rw [hBA] at h1
        have h2 := clique_deg G hK.2 hz
        have h3 : (part G true (part G false A y) z).card = 0 := by
          apply card_eq_zero.mpr
          apply eq_empty_iff_forall_notMem.mpr
          intro t ht
          exact hcross z hz t ((in_part G).mp ht).1 ((in_part G).mp ht).2.2
        omega
      · obtain ⟨a, b, c, d⟩ := hq Q h
        refine ⟨a, b.trans (part_sub G _ _ _), c, ?_⟩
        intro z hz
        have h1 := part_union_card G (b := true) hdBA z
        rw [hBA] at h1
        have h3 : (part G true (insert y (part G true A y)) z).card = 0 := by
          apply card_eq_zero.mpr
          apply eq_empty_iff_forall_notMem.mpr
          intro t ht
          exact hcross t ((in_part G).mp ht).1 z (b hz)
            ((G.adj_comm _ _).mp ((in_part G).mp ht).2.2)
        have := d z hz
        omega
    · exact List.pairwise_cons.mpr ⟨fun Q hQ => hdBA.mono_right (hq Q hQ).2.1, hp⟩
    · intro z hz
      by_cases hzB : z ∈ part G false A y
      · rcases hcov z hzB with h | ⟨Q, hQ, hzQ⟩
        · exact Or.inl h
        · exact Or.inr ⟨Q, List.mem_cons_of_mem _ hQ, hzQ⟩
      · exact Or.inr ⟨_, by simp, hin z hz hzB⟩

private lemma T_core {m : ℕ} (hSt : St G m) {S : Vertices} {x : V}
    (hx : x ∈ S) (hmin : ∀ z ∈ S, (part G true S x).card ≤ (part G true S z).card)
    (hb : bound G false (part G false S x) m) (hd : (part G true S x).card = 6)
    (hn : S.card = 6 * m + 7) (he : arcs G S S ≤ 30 * m + 72)
    (hacc : 2 * ((part G true S x).card * (part G true S x).card) +
          arcs G (part G false S x) (part G false S x) ≤
        arcs G S S + arcs G (part G true S x) (part G true S x))
    (hcap : arcs G (part G true S x) (part G true S x) ≤ capT (part G true S x).card) :
    (∃ u ∈ part G true S x, ∃ w ∈ part G true S x, u ≠ w ∧ ¬ G.Adj u w) ∧
    (Ppart G (part G false S x) m ∨ (Xtype G (part G false S x) m ∧
      arcs G (part G true S x) (part G false S x) = 10 ∧
      arcs G (part G true S x) (part G true S x) = 20 ∧
      ∀ u ∈ part G true S x, (part G true S u).card = 6)) := by
  have hsz := part_sizes G hx
  have hmin6 : ∀ z ∈ S, 6 ≤ (part G true S z).card := fun z hz => hd ▸ hmin z hz
  rw [hd] at hsz hacc hcap
  have hc6 : capT 6 = 20 := by decide
  rw [hc6] at hcap
  constructor
  · apply not_clique
    intro h
    have := clique_arcs G h
    rw [hd] at this
    omega
  rcases hSt _ hb (by omega) (by omega) with hP | hX
  · exact Or.inl hP
  · right
    have hAA := hX.1
    have hall := splits_at G hx
    have hrow := row_split G hx
    rw [hd] at hall hrow
    have hNN : arcs G (part G true S x) (part G true S x) = 20 := by omega
    have hNA : arcs G (part G true S x) (part G false S x) = 10 := by omega
    refine ⟨hX, hNA, hNN, ?_⟩
    apply all_eq_of_ge (fun z hz => hmin6 z (part_sub G _ _ _ hz))
    show arcs G (part G true S x) S ≤ (part G true S x).card * 6
    rw [hrow, hd]
    omega

private lemma iso_arcs {S : Vertices} {x : V} (hx : x ∈ S)
    (hmin6 : ∀ z ∈ S, 6 ≤ (part G true S z).card) {Q : Vertices}
    (hQA : Q ⊆ part G false S x)
    (hQ5 : ∀ z ∈ Q, (part G true (part G false S x) z).card = 5) (hQ6 : Q.card = 6) :
    6 ≤ arcs G Q (part G true S x) := by
  have := arcs_floor G (S := Q) (T := part G true S x) (k := 1) (fun z hz => by
    have e := deg_split_false G hx (hQA hz)
    have := hmin6 z (part_sub G _ _ _ (hQA hz))
    have := hQ5 z hz
    omega)
  omega

private lemma T_X2 {S : Vertices} {x : V} (hx : x ∈ S)
    (hmin6 : ∀ z ∈ S, 6 ≤ (part G true S z).card) {Q1 Q2 : Vertices}
    (h1 : Q1 ⊆ part G false S x) (h2 : Q2 ⊆ part G false S x)
    (d1 : ∀ z ∈ Q1, (part G true (part G false S x) z).card = 5)
    (d2 : ∀ z ∈ Q2, (part G true (part G false S x) z).card = 5)
    (c1 : Q1.card = 6) (c2 : Q2.card = 6) (hdis : Disjoint Q1 Q2)
    (hNA : arcs G (part G true S x) (part G false S x) = 10) : False := by
  have e := arcs_add_left G hdis (part G true S x)
  have hsub := arcs_mono_left G (union_subset h1 h2) (part G true S x)
  rw [arcs_sym G (part G false S x)] at hsub
  have := iso_arcs G hx hmin6 h1 d1 c1
  have := iso_arcs G hx hmin6 h2 d2 c2
  omega

private lemma LE_eq (hf : sparse G) {A : Vertices} {y : V} (hi : bound G false A 3)
    (hn : A.card = 18) (hdeg : ∀ v ∈ A, 6 ≤ (part G true A v).card)
    (he : arcs G A A ≤ 110) (hy : y ∈ A) (hd : (part G true A y).card = 6)
    (hK : ∀ Q ⊆ part G false A y, Q.card = 6 → ¬ homogeneous G true Q) :
    arcs G (part G true A y) (part G true A y) = 20 ∧
      ∀ u ∈ part G true A y, (part G true A u).card = 6 := by
  have hsz := part_sizes G hy
  have hb : bound G false (part G false A y) 2 := bound_part G hi hy
  have h58 := G4 G hf hb (by omega) hK
  have hcap := nbr_cap G hf A y
  have hall := splits_at G hy
  have hrow := row_split G hy
  have hfl : (part G true A y).card * 6 ≤ arcs G (part G true A y) A :=
    arcs_floor G (fun z hz => hdeg z (part_sub G _ _ _ hz))
  rw [hd] at hcap hall hrow hfl
  have hc6 : capT 6 = 20 := by decide
  rw [hc6] at hcap
  refine ⟨by omega, ?_⟩
  apply all_eq_of_ge (fun z hz => hdeg z (part_sub G _ _ _ hz))
  show arcs G (part G true A y) A ≤ (part G true A y).card * 6
  rw [hrow, hd]
  omega

private lemma LE_k6 (hf : sparse G) {A : Vertices} (hi : bound G false A 3)
    (hn : A.card = 18) (hdeg : ∀ v ∈ A, 6 ≤ (part G true A v).card)
    (he : arcs G A A ≤ 110) : ∃ Q ⊆ A, K6 G Q := by
  have hy : ∃ y ∈ A, (part G true A y).card = 6 := by
    by_contra hno
    push Not at hno
    have := arcs_floor G (S := A) (T := A) (k := 7) (fun z hz => by
      have := hdeg z hz
      have := hno z hz
      omega)
    omega
  obtain ⟨y, hy, hd⟩ := hy
  by_cases hK : ∀ Q ⊆ part G false A y, Q.card = 6 → ¬ homogeneous G true Q
  swap
  · push Not at hK
    obtain ⟨Q, hQ, h6, hcl⟩ := hK
    exact ⟨Q, hQ.trans (part_sub G _ _ _), h6, hcl⟩
  obtain ⟨hNN, hN6⟩ := LE_eq G hf hi hn hdeg he hy hd hK
  have hsz := part_sizes G hy
  have hc : ∀ u ∈ part G true A y, (part G true (part G false A y) u).card =
      (part G false (part G true A y) u).card := by
    intro u hu
    have := deg_split G hy hu
    have := hN6 u hu
    have := part_sizes G hu
    omega
  have hsum : ∑ z ∈ part G true A y, (part G false (part G true A y) z).card = 10 := by
    have h1 := arcs_compl G (part G true A y)
    have h2 : arcs Gᶜ (part G true A y) (part G true A y) =
        ∑ z ∈ part G true A y, (part G false (part G true A y) z).card := by
      unfold arcs
      exact sum_congr rfl (fun z _ => by rw [part_compl])
    rw [hd] at h1
    omega
  have key : ∀ u ∈ part G true A y, ∀ w ∈ part G true A y, u ≠ w → ¬ G.Adj u w →
      6 ≤ (part G false (part G true A y) u).card +
        (part G false (part G true A y) w).card := by
    intro u hu w hw hne hna
    have hR := coedge_clique G hi hu hw hne hna
    have hfc := free_card G (part G false A y) u w
    rw [← hc u hu, ← hc w hw]
    by_contra hlt
    obtain ⟨Q, hQR, hQ6, hQcl⟩ := big_clique G hR (by omega)
    exact hK Q (hQR.trans sdiff_subset) hQ6 hQcl
  have hNcl : ¬ homogeneous G true (part G true A y) := by
    intro h
    have := clique_arcs G h
    rw [hd] at this
    omega
  obtain ⟨u0, hu0, w0, hw0, hne0, hna0⟩ := not_clique G hNcl
  obtain ⟨u, hu, h3⟩ : ∃ u ∈ part G true A y,
      3 ≤ (part G false (part G true A y) u).card := by
    have := key u0 hu0 w0 hw0 hne0 hna0
    by_cases h : 3 ≤ (part G false (part G true A y) u0).card
    · exact ⟨u0, hu0, h⟩
    · exact ⟨w0, hw0, by omega⟩
  have hszu := part_sizes G hu
  have hsp := sum_parts G (part G true A y) hu
    (fun z => (part G false (part G true A y) z).card)
  have hCk : ∀ z ∈ part G false (part G true A y) u,
      6 - (part G false (part G true A y) u).card ≤
        (part G false (part G true A y) z).card := by
    intro z hz
    obtain ⟨hzN, hzu, hzna⟩ := (in_part G).mp hz
    have := key u hu z hzN hzu.symm hzna
    omega
  have hCs := sum_le_sum hCk
  simp only [sum_const, smul_eq_mul] at hCs
  have h5 : (part G false (part G true A y) u).card = 5 := by
    generalize (part G false (part G true A y) u).card = t at *
    have ht : t ≤ 5 := by omega
    interval_cases t <;> omega
  rw [h5] at hCs hCk hsp
  have h1 : ∀ z ∈ part G false (part G true A y) u,
      (part G false (part G true A y) z).card = 1 :=
    all_eq_of_ge (fun z hz => by have := hCk z hz; omega) (by rw [h5]; omega)
  have hCN := part_sub G false (part G true A y) u
  have hCcl : homogeneous G true (part G false (part G true A y) u) := by
    intro z1 hz1 z2 hz2 hne
    by_contra hna
    have hna' : ¬ G.Adj z1 z2 := fun h => hna h
    obtain ⟨_, hz1u, hz1na⟩ := (in_part G).mp hz1
    have hsub : ({u, z2} : Vertices) ⊆ part G false (part G true A y) z1 := by
      intro z hz
      rcases mem_insert.mp hz with h | h
      · rw [h]
        exact (in_part G).mpr ⟨hu, hz1u.symm, fun h' => hz1na ((G.adj_comm _ _).mp h')⟩
      · rw [mem_singleton.mp h]
        exact (in_part G).mpr ⟨hCN hz2, hne.symm, hna'⟩
    have := card_le_card hsub
    rw [card_pair ((in_part G).mp hz2).2.1.symm, h1 z1 hz1] at this
    omega
  refine ⟨insert y (part G false (part G true A y) u),
    insert_subset hy (hCN.trans (part_sub G _ _ _)), ?_,
    homog_insert G hCcl (fun z hz => ((in_part G).mp (hCN hz)).2.2)⟩
  rw [card_insert_of_notMem (fun h => self_out G true A y (hCN h)), h5]

private lemma LE (hf : sparse G) {A : Vertices} (hi : bound G false A 3)
    (hn : A.card = 18) (hdeg : ∀ v ∈ A, 6 ≤ (part G true A v).card)
    (he : arcs G A A ≤ 110) : Ppart G A 3 := by
  obtain ⟨Q, hQA, hQ⟩ := LE_k6 G hf hi hn hdeg he
  have hy : ∃ y ∈ Q, (part G true A y).card = 6 := by
    by_contra hno
    push Not at hno
    have h1 := arcs_floor G (S := Q) (T := A) (k := 7) (fun z hz => by
      have := hdeg z (hQA hz)
      have := hno z hz
      omega)
    have h2 := arcs_floor G (S := A \ Q) (T := A) (k := 6)
      (fun z hz => hdeg z (mem_sdiff.mp hz).1)
    have h3 := arcs_add_left G (disjoint_sdiff (s := Q) (t := A)) A
    rw [union_sdiff_of_subset hQA] at h3
    have := card_sdiff_of_subset hQA
    have := hQ.1
    omega
  obtain ⟨y, hyQ, hd⟩ := hy
  have hy := hQA hyQ
  have hBQ : ∀ z ∈ part G false A y, z ∉ Q := by
    intro z hz hzQ
    obtain ⟨_, hne, hna⟩ := (in_part G).mp hz
    exact hna (hQ.2 y hyQ z hzQ hne.symm)
  have hsz := part_sizes G hy
  by_cases hK : ∀ Q' ⊆ part G false A y, Q'.card = 6 → ¬ homogeneous G true Q'
  swap
  · push Not at hK
    obtain ⟨Q', hQ'B, h6, hcl⟩ := hK
    have hQ' : K6 G Q' := ⟨h6, hcl⟩
    have hQ'A := hQ'B.trans (part_sub G _ _ _)
    have hdis : Disjoint Q Q' := by
      rw [disjoint_left]
      intro z hz hz'
      exact hBQ z (hQ'B hz') hz
    have hRc : (A \ (Q ∪ Q')).card = 6 := by
      rw [card_sdiff_of_subset (union_subset hQA hQ'A), card_union_of_disjoint hdis, hn,
        hQ.1, h6]
    have hRcl : homogeneous G true (A \ (Q ∪ Q')) := by
      by_contra hcl'
      obtain ⟨u, hu, w, hw, hne, hna⟩ := not_clique G hcl'
      have hu' := mem_sdiff.mp hu
      have hw' := mem_sdiff.mp hw
      obtain ⟨J, hJ, hJc, hJm⟩ := F4 G hf hne hna [Q, Q'] (by simp) (by
          intro Q0 h0
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h0
          rcases h0 with h | h
          · rw [h]
            exact ⟨hQ, fun h => hu'.2 (mem_union_left _ h), fun h => hw'.2 (mem_union_left _ h)⟩
          · rw [h]
            exact ⟨hQ', fun h => hu'.2 (mem_union_right _ h),
              fun h => hw'.2 (mem_union_right _ h)⟩)
        (by simp [hdis])
      have hsub : J ⊆ A := by
        intro z hz
        rcases hJm z hz with h | h | ⟨Q0, h0, hz'⟩
        · rw [h]; exact hu'.1
        · rw [h]; exact hw'.1
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at h0
          rcases h0 with h | h
          · rw [h] at hz'; exact hQA hz'
          · rw [h] at hz'; exact hQ'A hz'
      have := hi J hsub hJ
      simp at hJc
      omega
    refine ⟨[Q, Q', A \ (Q ∪ Q')], rfl, ?_, ?_, ?_⟩
    · intro Q0 h0
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h0
      rcases h0 with h | h | h
      · rw [h]; exact ⟨hQ, hQA⟩
      · rw [h]; exact ⟨hQ', hQ'A⟩
      · rw [h]; exact ⟨⟨hRc, hRcl⟩, sdiff_subset⟩
    · have d1 : Disjoint Q (A \ (Q ∪ Q')) := disjoint_sdiff.mono_left subset_union_left
      have d2 : Disjoint Q' (A \ (Q ∪ Q')) := disjoint_sdiff.mono_left subset_union_right
      simp [hdis, d1, d2]
    · intro z hz
      by_cases h1 : z ∈ Q
      · exact ⟨Q, by simp, h1⟩
      by_cases h2 : z ∈ Q'
      · exact ⟨Q', by simp, h2⟩
      · exact ⟨A \ (Q ∪ Q'), by simp,
          mem_sdiff.mpr ⟨hz, fun h => (mem_union.mp h).elim h1 h2⟩⟩
  exfalso
  obtain ⟨hNN, hN6⟩ := LE_eq G hf hi hn hdeg he hy hd hK
  have hQN : Q.erase y ⊆ part G true A y := by
    intro z hz
    obtain ⟨hne, hzQ⟩ := mem_erase.mp hz
    exact (in_part G).mpr ⟨hQA hzQ, hne, hQ.2 y hyQ z hzQ hne.symm⟩
  have hQ5 : (Q.erase y).card = 5 := by rw [card_erase_of_mem hyQ, hQ.1]
  have hT1 : (part G true A y \ Q.erase y).card = 1 := by
    rw [card_sdiff_of_subset hQN, hd, hQ5]
  obtain ⟨t, ht⟩ := card_eq_one.mp hT1
  have htm : t ∈ part G true A y \ Q.erase y := by rw [ht]; exact mem_singleton_self t
  obtain ⟨htN, htQ⟩ := mem_sdiff.mp htm
  have hdj : Disjoint ({t} : Vertices) (Q.erase y) := disjoint_singleton_left.mpr htQ
  have hU : ({t} : Vertices) ∪ Q.erase y = part G true A y := by
    rw [← ht]; exact sdiff_union_of_subset hQN
  have hQcl : homogeneous G true (Q.erase y) := homog_mono G hQ.2 (erase_subset _ _)
  have h1 := arcs_partition G hdj
  rw [hU, arcs_diag_single, clique_arcs G hQcl, hQ5, hNN] at h1
  have htQ0 : arcs G {t} (Q.erase y) = 0 := by omega
  have hdt : (part G true (part G false A y) t).card ≤ 5 := by
    have := deg_split G hy htN
    have := hN6 t htN
    omega
  have hWc := card_sdiff_of_subset (part_sub G true (part G false A y) t)
  have hWcl : homogeneous G true
      (part G false A y \ part G true (part G false A y) t) := by
    by_contra hcl
    obtain ⟨a, ha, b, hb, hab, nab⟩ := not_clique G hcl
    obtain ⟨haB, haT⟩ := mem_sdiff.mp ha
    obtain ⟨hbB, hbT⟩ := mem_sdiff.mp hb
    have nta : ¬ G.Adj t a := fun h => haT ((in_part G).mpr ⟨haB, h.ne.symm, h⟩)
    have ntb : ¬ G.Adj t b := fun h => hbT ((in_part G).mpr ⟨hbB, h.ne.symm, h⟩)
    obtain ⟨q, hq, hqn⟩ := pick G (Q := Q.erase y) (U := {a, b}) (by
      have e : arcs G {a, b} Q = (part G true Q a).card + (part G true Q b).card := by
        unfold arcs; rw [sum_pair hab]
      have := arcs_mono_right G (erase_subset y Q) ({a, b} : Vertices)
      have := k6_exit G hf hQ (hBQ a haB)
      have := k6_exit G hf hQ (hBQ b hbB)
      omega)
    have naq : ¬ G.Adj a q := hqn a (by simp)
    have nbq : ¬ G.Adj b q := hqn b (by simp)
    have ntq : ¬ G.Adj t q := no_cross G htQ0 (mem_singleton_self t) hq
    obtain ⟨J, hJS, hJ, hJc, -⟩ := four_set G htN (hQN hq) haB hbB
      (fun e => htQ (e ▸ hq)) hab ntq nab nta ntb
      (fun h => naq ((G.adj_comm _ _).mp h)) (fun h => nbq ((G.adj_comm _ _).mp h))
    have := hi J hJS hJ
    omega
  obtain ⟨Q0, hQ0, hQ06, hQ0cl⟩ := big_clique G hWcl (by omega)
  exact hK Q0 (hQ0.trans sdiff_subset) hQ06 hQ0cl

private lemma T3 (hf : sparse G) {S : Vertices} (hi : bound G false S 3) (hn : S.card = 19) :
    134 ≤ arcs G S S := by
  by_contra hlt
  have he : arcs G S S ≤ 132 := by
    obtain ⟨r, hr⟩ := arcs_even G S
    omega
  obtain ⟨x, hx, hmin, hb, hsz, hacc, hcap, hd⟩ := forced G hf f2 2 (lower2 G hf) hi
    (card_pos.mp (by omega)) he (fun d => d = 6) (by rw [hn]; exact frcT3)
  have hd : (part G true S x).card = 6 := hd
  obtain ⟨⟨u, hu, w, hw, hne, hna⟩, hP | ⟨hX, -, hNN, hdeg⟩⟩ :=
    T_core G (St2 G hf) hx hmin hb hd (by omega) (by omega) hacc hcap
  · exact T_P G hf (by omega) hi hu hw hne hna hP
  obtain ⟨-, qs, E, hlen, -, -, -, -, hEK, hcov⟩ := hX
  have hnil : qs = [] := List.length_eq_zero_iff.mp (by omega)
  subst hnil
  have hAE : part G false S x ⊆ E :=
    fun z hz => (hcov z hz).elim id (fun ⟨_, h, _⟩ => by simp at h)
  have hcu : ∀ v ∈ part G true S x, (part G true (part G false S x) v).card =
      (part G false (part G true S x) v).card := by
    intro v hv
    have := deg_split G hx hv
    have := hdeg v hv
    have := part_sizes G hv
    omega
  have hco : arcs Gᶜ (part G true S x) (part G true S x) ≤ 10 := by
    have := arcs_compl G (part G true S x)
    rw [hd] at this
    omega
  have h6 := codeg_pair G hu hw hne hco
  rw [← hcu u hu, ← hcu w hw] at h6
  have hR := coedge_clique G hi hu hw hne hna
  have hfc := free_card G (part G false S x) u w
  obtain ⟨Q, hQR, hQ6, hQcl⟩ := big_clique G hR (by omega)
  exact hEK Q ((hQR.trans sdiff_subset).trans hAE) hQ6 hQcl

private lemma lower3 (hf : sparse G) (A : Vertices) (hi : bound G false A 3) :
    f3 A.card ≤ arcs G A A := by
  by_cases h19 : A.card = 19
  · have := T3 G hf hi h19
    have e : f3 19 = 134 := by decide
    rw [h19, e]; exact this
  by_cases h20 : A.card = 20
  · have := U3 G hf hi h20
    have e : f3 20 = 144 := by decide
    rw [h20, e]; exact this
  have h37 : A.card ≤ 37 := by simpa using card_le_univ A
  by_cases hlt : A.card < 37
  · exact lower_step G hf f2 f3 2 (lower2 G hf) hi (chk3 _ hlt h19 h20) (by decide)
  · have e : A.card = 37 := by omega
    have e' : f3 37 = 0 := by decide
    rw [e, e']; exact Nat.zero_le _

private lemma St3 (hf : sparse G) : St G 3 := by
  intro A hi hn he
  obtain ⟨y, hy, hmin, hb, hsz, hacc, hcap, hd⟩ := forced G hf f2 2 (lower2 G hf) hi
    (card_pos.mp (by omega)) (show arcs G A A ≤ 110 by omega) (fun d => d = 5 ∨ d = 6)
    (by rw [hn]; exact frcS3)
  rcases (hd : (part G true A y).card = 5 ∨ (part G true A y).card = 6) with h5 | h6
  · exact St_d5 G hf (by omega) (St2 G hf) hi hy hb h5 (by omega) (by omega) hacc
  · exact Or.inl (LE G hf hi (by omega) (fun v hv => h6 ▸ hmin v hv) (by omega))

private lemma T4 (hf : sparse G) {S : Vertices} (hi : bound G false S 4) (hn : S.card = 25) :
    164 ≤ arcs G S S := by
  by_contra hlt
  have he : arcs G S S ≤ 162 := by
    obtain ⟨r, hr⟩ := arcs_even G S
    omega
  obtain ⟨x, hx, hmin, hb, hsz, hacc, hcap, hd⟩ := forced G hf f3 3 (lower3 G hf) hi
    (card_pos.mp (by omega)) (show arcs G S S ≤ 163 by omega) (fun d => d = 6)
    (by rw [hn]; exact frcT4)
  have hd : (part G true S x).card = 6 := hd
  have hmin6 : ∀ z ∈ S, 6 ≤ (part G true S z).card := fun z hz => hd ▸ hmin z hz
  obtain ⟨⟨u, hu, w, hw, hne, hna⟩, hP | ⟨hX, hNA, -, -⟩⟩ :=
    T_core G (St3 G hf) hx hmin hb hd (by omega) (by omega) hacc hcap
  · exact T_P G hf (by omega) hi hu hw hne hna hP
  obtain ⟨-, qs, E, hlen, hEA, hE12, hq, -, -, -⟩ := hX
  obtain ⟨Q, rfl⟩ := List.length_eq_one_iff.mp (show qs.length = 1 by omega)
  obtain ⟨hQ, hQA, hQE, hQ5⟩ := hq Q (by simp)
  have h6 := iso_arcs G hx hmin6 hQA hQ5 hQ.1
  have hNE : arcs G (part G true S x) E ≤ 4 := by
    have h1 := arcs_add_right G hQE (part G true S x)
    have h2 := arcs_mono_right G (union_subset hQA hEA) (part G true S x)
    rw [arcs_sym G Q] at h6
    omega
  have h2 := two_le_arcs G (A := E) hu hw hne
  have hfc := free_card G E u w
  have hRn : ¬ homogeneous G true (E \ (part G true E u ∪ part G true E w)) := by
    intro h
    have := clique_le_six G hf h
    omega
  obtain ⟨p, hp, p', hp', hpp, npp⟩ := not_clique G hRn
  obtain ⟨hpE, nup, nwp⟩ := free_of G hp
  obtain ⟨hpE', nup', nwp'⟩ := free_of G hp'
  have huQ : u ∉ Q := fun h => disjoint_left.mp (parts_disj G S x) hu (hQA h)
  have hwQ : w ∉ Q := fun h => disjoint_left.mp (parts_disj G S x) hw (hQA h)
  obtain ⟨q, hqQ, hqn⟩ := pick G (Q := Q) (U := {u, w}) (by
    have e : arcs G {u, w} Q = (part G true Q u).card + (part G true Q w).card := by
      unfold arcs; rw [sum_pair hne]
    have := k6_exit G hf hQ huQ
    have := k6_exit G hf hQ hwQ
    rw [hQ.1]
    omega)
  have nuq : ¬ G.Adj u q := hqn u (by simp)
  have nwq : ¬ G.Adj w q := hqn w (by simp)
  have hpQ : p ∉ Q := fun h => disjoint_left.mp hQE h hpE
  have hpQ' : p' ∉ Q := fun h => disjoint_left.mp hQE h hpE'
  have nqp := iso_k6 G hQ hQA hqQ (hQ5 q hqQ) (hEA hpE) hpQ
  have nqp' := iso_k6 G hQ hQA hqQ (hQ5 q hqQ) (hEA hpE') hpQ'
  obtain ⟨J, hJS, hJ, hJc, hJm⟩ := four_set G hu hw (hEA hpE) (hEA hpE') hne hpp hna npp
    nup nup' nwp nwp'
  have hqJ : q ∉ J := by
    intro h
    rcases hJm q h with e | e | e | e
    · exact huQ (e ▸ hqQ)
    · exact hwQ (e ▸ hqQ)
    · exact hpQ (e ▸ hqQ)
    · exact hpQ' (e ▸ hqQ)
  have hJ' : homogeneous G false (insert q J) := homog_insert G hJ (by
    intro z hz
    rcases hJm z hz with e | e | e | e
    · rw [e]; exact fun h => nuq ((G.adj_comm _ _).mp h)
    · rw [e]; exact fun h => nwq ((G.adj_comm _ _).mp h)
    · rw [e]; exact nqp
    · rw [e]; exact nqp')
  have := hi (insert q J) (insert_subset (part_sub G _ _ _ (hQA hqQ)) hJS) hJ'
  rw [card_insert_of_notMem hqJ] at this
  omega

private lemma lower4 (hf : sparse G) (A : Vertices) (hi : bound G false A 4) :
    f4 A.card ≤ arcs G A A := by
  by_cases h25 : A.card = 25
  · have := T4 G hf hi h25
    have e : f4 25 = 164 := by decide
    rw [h25, e]; exact this
  have h37 : A.card ≤ 37 := by simpa using card_le_univ A
  by_cases hlt : A.card < 37
  · exact lower_step G hf f3 f4 3 (lower3 G hf) hi (chk4 _ hlt h25) (by decide)
  · have e : A.card = 37 := by omega
    have e' : f4 37 = 0 := by decide
    rw [e, e']; exact Nat.zero_le _

private lemma St4 (hf : sparse G) : St G 4 := by
  intro A hi hn he
  obtain ⟨y, hy, hmin, hb, hsz, hacc, hcap, hd⟩ := forced G hf f3 3 (lower3 G hf) hi
    (card_pos.mp (by omega)) (show arcs G A A ≤ 140 by omega) (fun d => d = 5)
    (by rw [hn]; exact frcS4)
  exact St_d5 G hf (by omega) (St3 G hf) hi hy hb hd (by omega) (by omega) hacc

private lemma T5 (hf : sparse G) {S : Vertices} (hi : bound G false S 5) (hn : S.card = 31) :
    194 ≤ arcs G S S := by
  by_contra hlt
  have he : arcs G S S ≤ 192 := by
    obtain ⟨r, hr⟩ := arcs_even G S
    omega
  obtain ⟨x, hx, hmin, hb, hsz, hacc, hcap, hd⟩ := forced G hf f4 4 (lower4 G hf) hi
    (card_pos.mp (by omega)) (show arcs G S S ≤ 193 by omega) (fun d => d = 6)
    (by rw [hn]; exact frcT5)
  have hd : (part G true S x).card = 6 := hd
  have hmin6 : ∀ z ∈ S, 6 ≤ (part G true S z).card := fun z hz => hd ▸ hmin z hz
  obtain ⟨⟨u, hu, w, hw, hne, hna⟩, hP | ⟨hX, hNA, -, -⟩⟩ :=
    T_core G (St4 G hf) hx hmin hb hd (by omega) (by omega) hacc hcap
  · exact T_P G hf (by omega) hi hu hw hne hna hP
  obtain ⟨-, qs, E, hlen, -, -, hq, hp, -, -⟩ := hX
  obtain ⟨Q1, Q2, rfl⟩ := List.length_eq_two.mp (show qs.length = 2 by omega)
  obtain ⟨k1, a1, -, b1⟩ := hq Q1 (by simp)
  obtain ⟨k2, a2, -, b2⟩ := hq Q2 (by simp)
  exact T_X2 G hx hmin6 a1 a2 b1 b2 k1.1 k2.1 ((List.pairwise_cons.mp hp).1 Q2 (by simp)) hNA

private lemma lower5 (hf : sparse G) (A : Vertices) (hi : bound G false A 5) :
    f5 A.card ≤ arcs G A A := by
  by_cases h31 : A.card = 31
  · have := T5 G hf hi h31
    have e : f5 31 = 194 := by decide
    rw [h31, e]; exact this
  have h37 : A.card ≤ 37 := by simpa using card_le_univ A
  by_cases hlt : A.card < 37
  · exact lower_step G hf f4 f5 4 (lower4 G hf) hi (chk5 _ hlt h31) (by decide)
  · have e : A.card = 37 := by omega
    have e' : f5 37 = 0 := by decide
    rw [e, e']; exact Nat.zero_le _

private lemma St5 (hf : sparse G) : St G 5 := by
  intro A hi hn he
  obtain ⟨y, hy, hmin, hb, hsz, hacc, hcap, hd⟩ := forced G hf f4 4 (lower4 G hf) hi
    (card_pos.mp (by omega)) (show arcs G A A ≤ 170 by omega) (fun d => d = 5)
    (by rw [hn]; exact frcS5)
  exact St_d5 G hf (by omega) (St4 G hf) hi hy hb hd (by omega) (by omega) hacc

/-- F4 for five K6's when every degree is 6: weighted greedy. -/
private lemma T6_P (hf : sparse G) {S : Vertices} {x u w : V} (hi : bound G false S 6)
    (hn : S.card = 37) (hx : x ∈ S) (hall6 : ∀ z ∈ S, (part G true S z).card = 6)
    (hu : u ∈ part G true S x) (hw : w ∈ part G true S x) (hne : u ≠ w)
    (hna : ¬ G.Adj u w) (hP : Ppart G (part G false S x) 5) : False := by
  obtain ⟨qs, hlen, hq, hp, hcov⟩ := hP
  have hsz := part_sizes G hx
  have hdx := hall6 x hx
  have hdu : (part G true (part G false S x) u).card ≤ 5 := by
    have := deg_split G hx hu
    have := hall6 u (part_sub G _ _ _ hu)
    omega
  have hdw : (part G true (part G false S x) w).card ≤ 5 := by
    have := deg_split G hx hw
    have := hall6 w (part_sub G _ _ _ hw)
    omega
  have hfc := free_card G (part G false S x) u w
  obtain ⟨f, hf'⟩ : (part G false S x \ (part G true (part G false S x) u ∪
      part G true (part G false S x) w)).Nonempty := card_pos.mp (by omega)
  obtain ⟨hfA, nuf, nwf⟩ := free_of G hf'
  have hdf : (part G true (part G false S x) f).card ≤ 6 := by
    have := card_le_card (part_mono G (part_sub G false S x) true f)
    have := hall6 f (part_sub G _ _ _ hfA)
    omega
  obtain ⟨Qi, hQi, hfQi⟩ := hcov f hfA
  have hnd : qs.Nodup := List.Pairwise.imp_of_mem (fun ha _ hab e => by
    subst e
    have := (hq _ ha).1.1
    rw [(disjoint_self_iff_empty _).mp hab] at this
    simp at this) hp
  have hpd : ∀ Q ∈ qs, ∀ Q' ∈ qs, Q ≠ Q' → Disjoint Q Q' := by
    intro Q hQ Q' hQ' hne'
    have : Std.Symm (Disjoint : Vertices → Vertices → Prop) := ⟨fun _ _ h => h.symm⟩
    exact hp.forall hQ hQ' hne'
  have hout : ∀ {z}, z ∈ part G true S x → ∀ {Q'}, Q' ⊆ part G false S x → z ∉ Q' :=
    fun hz _ hQ' h => disjoint_left.mp (parts_disj G S x) hz (hQ' h)
  obtain ⟨hQi6, hQiA⟩ := hq Qi hQi
  have hdi := clique_deg G hQi6.2 hfQi
  have hlen' : (qs.erase Qi).length = 4 := by rw [List.length_erase_of_mem hQi]; omega
  have hmem' : ∀ Q, Q ∈ qs.erase Qi ↔ Q ≠ Qi ∧ Q ∈ qs := fun Q => hnd.mem_erase_iff
  have hZ : ∃ Qj ∈ qs.erase Qi, ∀ t ∈ part G false S x, G.Adj f t → t ∉ Qi → t ∈ Qj := by
    by_cases hg : ∃ g ∈ part G false S x, G.Adj f g ∧ g ∉ Qi
    · obtain ⟨g, hgA, hfg, hgQi⟩ := hg
      obtain ⟨Qj, hQj, hgQj⟩ := hcov g hgA
      refine ⟨Qj, (hmem' Qj).mpr ⟨fun e => hgQi (e ▸ hgQj), hQj⟩, ?_⟩
      intro t htA hft htQi
      by_contra htQj
      have htg : t ≠ g := fun e => htQj (e ▸ hgQj)
      have hsub : insert g (insert t (part G true Qi f)) ⊆
          part G true (part G false S x) f := by
        intro z hz
        rcases mem_insert.mp hz with h | h
        · rw [h]; exact (in_part G).mpr ⟨hgA, hfg.ne.symm, hfg⟩
        rcases mem_insert.mp h with h | h
        · rw [h]; exact (in_part G).mpr ⟨htA, hft.ne.symm, hft⟩
        · exact part_mono G hQiA true f h
      have hc := card_le_card hsub
      rw [card_insert_of_notMem (by
            simp only [mem_insert, not_or]
            exact ⟨fun e => htg e.symm, fun h => hgQi (part_sub G _ _ _ h)⟩),
          card_insert_of_notMem (fun h => htQi (part_sub G _ _ _ h))] at hc
      have := hQi6.1
      omega
    · obtain ⟨Qj, hQj⟩ := List.exists_mem_of_length_pos
        (show 0 < (qs.erase Qi).length by omega)
      exact ⟨Qj, hQj, fun t htA hft htQi => (hg ⟨t, htA, hft, htQi⟩).elim⟩
  obtain ⟨Qj, hQj, hZ⟩ := hZ
  obtain ⟨hQjne, hQjqs⟩ := (hmem' Qj).mp hQj
  obtain ⟨hQj6, hQjA⟩ := hq Qj hQjqs
  have hfuw : f ∉ ({u, w} : Vertices) := by
    intro h
    rcases mem_insert.mp h with e | e
    · exact hout hu Subset.rfl (e ▸ hfA)
    · exact hout hw Subset.rfl (mem_singleton.mp e ▸ hfA)
  have hfQ : ∀ Q ∈ qs, Q ≠ Qi → f ∉ Q :=
    fun Q hQ hne' h => disjoint_left.mp (hpd Q hQ Qi hQi hne') h hfQi
  have hI0a : ∀ Q ∈ qs, Q ≠ Qi →
      arcs G (insert f {u, w}) Q ≤ (part G true Q f).card + 2 := by
    intro Q hQ _
    have e : arcs G (insert f {u, w}) Q =
        (part G true Q f).card + ((part G true Q u).card + (part G true Q w).card) := by
      unfold arcs
      rw [sum_insert hfuw, sum_pair hne]
    have := k6_exit G hf (hq Q hQ).1 (hout hu (hq Q hQ).2)
    have := k6_exit G hf (hq Q hQ).1 (hout hw (hq Q hQ).2)
    omega
  have hI0 : homogeneous G false (insert f {u, w}) := homog_insert G (indep_pair G hna) (by
    intro z hz
    rcases mem_insert.mp hz with e | e
    · rw [e]; exact fun h => nuf ((G.adj_comm _ _).mp h)
    · rw [mem_singleton.mp e]; exact fun h => nwf ((G.adj_comm _ _).mp h))
  have hI0S : insert f ({u, w} : Vertices) ⊆ S := by
    intro z hz
    rcases mem_insert.mp hz with e | e
    · rw [e]; exact part_sub G _ _ _ hfA
    rcases mem_insert.mp e with e | e
    · rw [e]; exact part_sub G _ _ _ hu
    · rw [mem_singleton.mp e]; exact part_sub G _ _ _ hw
  have hI0Q : ∀ Q ∈ qs, Q ≠ Qi → Disjoint (insert f ({u, w} : Vertices)) Q := by
    intro Q hQ hne'
    rw [disjoint_left]
    intro z hz hzQ
    rcases mem_insert.mp hz with e | e
    · exact hfQ Q hQ hne' (e ▸ hzQ)
    rcases mem_insert.mp e with e | e
    · exact hout hu (hq Q hQ).2 (e ▸ hzQ)
    · exact hout hw (hq Q hQ).2 (mem_singleton.mp e ▸ hzQ)
  obtain ⟨y, hyQj, hyn⟩ := pick G (Q := Qj) (U := insert f {u, w}) (by
    have := hI0a Qj hQjqs hQjne
    have := k6_exit G hf hQj6 (hfQ Qj hQjqs hQjne)
    rw [hQj6.1]
    omega)
  have hyI : y ∉ insert f ({u, w} : Vertices) :=
    fun h => disjoint_left.mp (hI0Q Qj hQjqs hQjne) h hyQj
  have hI1 : homogeneous G false (insert y (insert f {u, w})) :=
    homog_insert G hI0 (fun z hz ha => hyn z hz ((G.adj_comm y z).mp ha))
  have hnd' : (qs.erase Qi).Nodup := hnd.erase Qi
  have hmem'' : ∀ Q, Q ∈ (qs.erase Qi).erase Qj ↔ Q ≠ Qj ∧ Q ≠ Qi ∧ Q ∈ qs := by
    intro Q
    rw [hnd'.mem_erase_iff, hmem']
  have hlen'' : ((qs.erase Qi).erase Qj).length = 3 := by
    rw [List.length_erase_of_mem hQj]; omega
  obtain ⟨J, hIJ, hJ, hJc, hJm⟩ := grow G hf ((qs.erase Qi).erase Qj)
    (insert y (insert f {u, w})) hI1
    (by
      intro Q hQ
      obtain ⟨hQQj, hQQi, hQqs⟩ := (hmem'' Q).mp hQ
      have hyQ : y ∉ Q := fun h => disjoint_left.mp (hpd Qj hQjqs Q hQqs (Ne.symm hQQj)) hyQj h
      refine ⟨(hq Q hQqs).1, ?_, ?_⟩
      · rw [disjoint_insert_left]
        exact ⟨hyQ, hI0Q Q hQqs hQQi⟩
      · have e : arcs G (insert y (insert f {u, w})) Q =
            (part G true Q y).card + arcs G (insert f {u, w}) Q := by
          unfold arcs; rw [sum_insert hyI]
        have := k6_exit G hf (hq Q hQqs).1 hyQ
        have := hI0a Q hQqs hQQi
        have h0 : (part G true Q f).card = 0 := by
          apply card_eq_zero.mpr
          apply eq_empty_iff_forall_notMem.mpr
          intro t ht
          obtain ⟨htQ, _, hft⟩ := (in_part G).mp ht
          have htQj := hZ t ((hq Q hQqs).2 htQ) hft
            (fun h => disjoint_left.mp (hpd Q hQqs Qi hQi hQQi) htQ h)
          exact disjoint_left.mp (hpd Q hQqs Qj hQjqs hQQj) htQ htQj
        rw [hlen'']
        omega)
    (hp.sublist ((List.erase_sublist).trans (List.erase_sublist)))
  have hsub : J ⊆ S := by
    intro z hz
    rcases hJm z hz with h | ⟨Q, hQ, hzQ⟩
    · rcases mem_insert.mp h with e | e
      · rw [e]; exact part_sub G _ _ _ (hQjA hyQj)
      · exact hI0S e
    · exact part_sub G _ _ _ ((hq Q ((hmem'' Q).mp hQ).2.2).2 hzQ)
  have := hi J hsub hJ
  rw [hJc, card_insert_of_notMem hyI, card_insert_of_notMem hfuw, card_pair hne, hlen''] at this
  omega

private lemma graph_result (hf : sparse G) (hi : bound G false univ 6)
    (edges : arcs G univ univ ≤ 222) : False := by
  have hn : (univ : Vertices).card = 37 := by simp
  obtain ⟨x, hx, hmin, hb, hsz, hacc, hcap, hd⟩ := forced G hf f5 5 (lower5 G hf) hi
    ⟨0, mem_univ _⟩ edges (fun d => d = 6) (by rw [hn]; exact frcT6)
  have hd : (part G true univ x).card = 6 := hd
  have hmin6 : ∀ z ∈ (univ : Vertices), 6 ≤ (part G true univ z).card :=
    fun z hz => hd ▸ hmin z hz
  obtain ⟨⟨u, hu, w, hw, hne, hna⟩, hP | ⟨hX, hNA, -, -⟩⟩ :=
    T_core G (St5 G hf) hx hmin hb hd (by omega) (by omega) hacc hcap
  · have hall6 : ∀ z ∈ (univ : Vertices), (part G true univ z).card = 6 :=
      all_eq_of_ge hmin6 (by
        show arcs G univ univ ≤ (univ : Vertices).card * 6
        rw [hn]; omega)
    exact T6_P G hf hi hn hx hall6 hu hw hne hna hP
  obtain ⟨-, qs, E, hlen, -, -, hq, hp, -, -⟩ := hX
  obtain ⟨Q1, Q2, Q3, rfl⟩ := List.length_eq_three.mp (show qs.length = 3 by omega)
  obtain ⟨k1, a1, -, b1⟩ := hq Q1 (by simp)
  obtain ⟨k2, a2, -, b2⟩ := hq Q2 (by simp)
  exact T_X2 G hx hmin6 a1 a2 b1 b2 k1.1 k2.1 ((List.pairwise_cons.mp hp).1 Q2 (by simp)) hNA
private def fromBool (adj : Sym2 V → Bool) : SimpleGraph V where
  Adj x y := x ≠ y ∧ adj s(x,y) = true
  symm := ⟨fun x y h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private lemma edge_account (adj : Sym2 V → Bool) (S : Vertices) :
    arcs (fromBool adj) S S +
      ((S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ adj s(p.1,p.2) = false)).card =
        S.card * S.card - S.card := by
  have h := card_filter_add_card_filter_not (s := S.offDiag)
    (fun p : V × V => adj s(p.1,p.2) = true)
  have h₁ : S.offDiag.filter (fun p => adj s(p.1,p.2) = true) =
      (S ×ˢ S).filter (fun p => (fromBool adj).Adj p.1 p.2) := by
    ext p
    rw [mem_filter, mem_filter, mem_offDiag, mem_product]
    change (_ ∧ _) ↔ _ ∧ p.1 ≠ p.2 ∧ adj s(p.1,p.2) = true
    tauto
  have h₂ : S.offDiag.filter (fun p => ¬ adj s(p.1,p.2) = true) =
      (S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ adj s(p.1,p.2) = false) := by
    ext p
    simp only [mem_filter, mem_offDiag, mem_product, Bool.not_eq_true]
    tauto
  rw [h₁,h₂,offDiag_card] at h
  rwa [arcs_card]

private theorem completeGraphLemma : OMA.R_Erdos617_erdos_617_R1_H3_R1.H1 := by
  intro adj hedges
  let G := fromBool adj
  by_contra hbad
  have avoid (S : Vertices) (hn : S.card = 7) :
      ¬ ((∀ x ∈ S, ∀ y ∈ S, x ≠ y → adj s(x,y) = false) ∨
       ((S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ adj s(p.1,p.2) = false)).card < 10) :=
    fun h => hbad ⟨S,hn,h⟩
  have hi : bound G false univ 6 := by
    by_contra h
    obtain ⟨S,_,hn,hh⟩ := extract G h
    apply avoid S hn
    left
    intro x hx y hy hne
    have ha : ¬ (x ≠ y ∧ adj s(x,y) = true) := hh x hx y hy hne
    cases he : adj s(x,y)
    · rfl
    · exact (ha ⟨hne,he⟩).elim
  have hf : sparse G := by
    intro S hn
    have h₁ := edge_account adj S
    change arcs G S S + _ = _ at h₁
    rw [hn] at h₁
    have h₂ : 10 ≤ ((S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ adj s(p.1,p.2) = false)).card :=
      Nat.le_of_not_gt (fun h => avoid S hn (Or.inr h))
    omega
  apply graph_result G hf hi
  rw [arcs_card]
  rw [univ_product_univ]
  have heq : (univ.filter (fun p : V × V => G.Adj p.1 p.2)) =
      (univ.filter (fun p : V × V => p.1 ≠ p.2 ∧ adj s(p.1,p.2) = true)) := by
    ext p
    rw [mem_filter, mem_filter]
    rfl
  rwa [heq]

end
end Graph617c

theorem OMA.solution : OMA.R_Erdos617_erdos_617_R1_H3_R1.H1 := Graph617c.completeGraphLemma
