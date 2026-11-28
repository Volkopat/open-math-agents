import OMAReductions.R_Erdos617_erdos_617_R1
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! Step Erdos617.erdos_617.R1.H2 (reduction by capioryadi-collab): the r = 5 extremal statement
on 26 vertices, the Main Lemma of Xia and Szeider, arXiv:2610.24484.

The first part of this file (rel .. edge_account) is the induced-neighbourhood framework of the
merged proof of Erdos617.erdos_617.R1.H1 by MakisChristou, moved from Fin 17 to Fin 26.
The argument is a greedy partition after Erdős and Gyárfás (1999), Lemma 2, and Füredi's
stability proof. Written with Claude Code (AI-assisted). -/
namespace Graph617b
/-- Cap on the ordered adjacent pairs inside a neighbourhood of size `d`. -/
def capT (d : ℕ) : ℕ := if d = 5 then 12 else d * (d - 1)
/-- Numeric closure of a level with independence number at most 3. -/
def Num3 (n a : ℕ) : Prop :=
  ∀ d < n, d * n ≤ a →
    (11 ≤ n - 1 - d ∧ a + capT d - 2 * (d * d) < (n - 1 - d) * (n - 1 - d - 5)) ∨
    (n - 1 - d = 10 ∧ 5 ≤ d ∧ a + capT d - 2 * (d * d) < 50)
/-- Numeric closure of a level with independence number at most 4. -/
def Num4 (n a : ℕ) : Prop :=
  ∀ d < n, d * n ≤ a → 0 < n - 1 - d ∧ Num3 (n - 1 - d) (a + capT d - 2 * (d * d))
def c3 (n a d : ℕ) : Bool :=
  decide (11 ≤ n - 1 - d ∧ a + capT d - 2 * (d * d) < (n - 1 - d) * (n - 1 - d - 5)) ||
  decide (n - 1 - d = 10 ∧ 5 ≤ d ∧ a + capT d - 2 * (d * d) < 50)
def b3 (n a : ℕ) : Bool := (List.range n).all (fun d => !decide (d * n ≤ a) || c3 n a d)
def b4 (n a : ℕ) : Bool := (List.range n).all (fun d => !decide (d * n ≤ a) ||
  (decide (0 < n - 1 - d) && b3 (n - 1 - d) (a + capT d - 2 * (d * d))))
lemma num3_of {n a : ℕ} (h : b3 n a = true) : Num3 n a := by
  intro d hd hle
  have := List.all_eq_true.mp h d (List.mem_range.mpr hd)
  simpa [c3, hle] using this
lemma num4_of {n a : ℕ} (h : b4 n a = true) : Num4 n a := by
  intro d hd hle
  have := List.all_eq_true.mp h d (List.mem_range.mpr hd)
  simp only [hle, decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    decide_eq_true_eq] at this
  exact ⟨this.1, num3_of this.2⟩
lemma num25 : Num4 25 130 := num4_of (by decide)
lemma num24 : Num4 24 128 := num4_of (by decide)
lemma num23 : Num4 23 124 := num4_of (by decide)
lemma num22 : Num4 22 118 := num4_of (by decide)
lemma n3a : Num3 17 98 := num3_of (by decide)
lemma n3b : Num3 18 104 := num3_of (by decide)
lemma n3c : Num3 19 108 := num3_of (by decide)
lemma n3d : Num3 20 110 := num3_of (by decide)
lemma n3e : Num3 16 80 := num3_of (by decide)
lemma n3f : Num3 17 86 := num3_of (by decide)
lemma n3g : Num3 18 90 := num3_of (by decide)
lemma n3h : Num3 19 92 := num3_of (by decide)
open Finset
abbrev V := Fin 26
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


private def sparse : Prop := ∀ S : Vertices, S.card = 6 → arcs G S S ≤ 22

private lemma clique_le_five (hf : sparse G) {S} (h : homogeneous G true S) : S.card ≤ 5 := by
  by_contra! hn
  obtain ⟨Y,hy,hY⟩ := exists_subset_card_eq (show 6 ≤ S.card by omega)
  have := hf Y hY
  rw [clique_arcs G (homog_mono G h hy), hY] at this
  omega
private lemma k5_exit (hf : sparse G) {Q} (hQ : Q.card = 5) (hcl : homogeneous G true Q) {x}
    (hx : x ∉ Q) : (part G true Q x).card ≤ 1 := by
  have hdis : Disjoint {x} Q := disjoint_singleton_left.mpr hx
  have hsize : ({x} ∪ Q).card = 6 := by rw [card_union_of_disjoint hdis, card_singleton, hQ]
  have h := hf _ hsize
  rw [arcs_partition G hdis,arcs_diag_single,arcs_singleton,clique_arcs G hcl,hQ] at h
  omega
private lemma pick (hf : sparse G) {Q U : Vertices} (hQ : Q.card = 5)
    (hcl : homogeneous G true Q) (hU : U.card ≤ 4) (hdis : Disjoint U Q) :
    ∃ y ∈ Q, ∀ u ∈ U, ¬ G.Adj u y := by
  have hc : (U.biUnion (fun u => part G true Q u)).card ≤ 4 := by
    refine le_trans card_biUnion_le ?_
    calc ∑ u ∈ U, (part G true Q u).card ≤ ∑ _u ∈ U, 1 :=
          sum_le_sum (fun u hu => k5_exit G hf hQ hcl (disjoint_left.mp hdis hu))
      _ ≤ 4 := by simpa using hU
  obtain ⟨y, hy, hny⟩ := exists_mem_notMem_of_card_lt_card
    (show (U.biUnion (fun u => part G true Q u)).card < Q.card by omega)
  exact ⟨y, hy, fun u hu ha =>
    hny (mem_biUnion.mpr ⟨u, hu, (in_part G).mpr ⟨hy, ha.ne.symm, ha⟩⟩)⟩
private lemma single_indep (w : V) : homogeneous G false {w} := by
  intro i hi j hj hij
  simp only [mem_singleton] at hi hj
  exact (hij (hi.trans hj.symm)).elim
private lemma pair_indep {u w : V} (h : ¬ G.Adj u w) : homogeneous G false (insert u {w}) :=
  homog_insert G (single_indep G w) (fun y hy => by rw [mem_singleton.mp hy]; exact h)
private lemma not_clique {S} (h : ¬ homogeneous G true S) :
    ∃ u ∈ S, ∃ w ∈ S, u ≠ w ∧ ¬ G.Adj u w := by
  by_contra hc
  apply h
  intro u hu w hw hne
  by_contra ha
  exact hc ⟨u,hu,w,hw,hne,ha⟩
private lemma closed_clique {S x} (hN : homogeneous G true (part G true S x)) :
    homogeneous G true (insert x (part G true S x)) :=
  homog_insert G hN (fun _ hy => ((in_part G).mp hy).2.2)
/-- Extend an independent set by a vertex of a 5-clique. -/
private lemma ext_step (hf : sparse G) {S Q I : Vertices} (hQ : Q.card = 5)
    (hcl : homogeneous G true Q) (hQS : Q ⊆ S) (hI : homogeneous G false I) (hIS : I ⊆ S)
    (hc : I.card ≤ 4) (hdis : Disjoint I Q) :
    ∃ J : Vertices, homogeneous G false J ∧ J ⊆ S ∧ J.card = I.card + 1 ∧ J ⊆ I ∪ Q := by
  obtain ⟨y, hy, hn⟩ := pick G hf hQ hcl hc hdis
  have hyI : y ∉ I := fun h => disjoint_left.mp hdis h hy
  refine ⟨insert y I, homog_insert G hI (fun u hu ha => hn u hu ha.symm),
    insert_subset (hQS hy) hIS, card_insert_of_notMem hyI, ?_⟩
  exact insert_subset (mem_union_right _ hy) subset_union_left
private lemma two_clique (hf : sparse G) {S x} (hi : bound G false S 2) (hx : x ∈ S) :
    homogeneous G true (part G false S x) ∧ (part G false S x).card ≤ 5 := by
  have h := homog_of_bound_one G (b := true) (bound_part G hi hx)
  exact ⟨h, clique_le_five G hf h⟩
/-- A non-adjacent pair among the neighbours of `x` in `S`. -/
private lemma bad_pair {S x} (hn : ¬ homogeneous G true (insert x (part G true S x))) :
    ∃ I : Vertices, homogeneous G false I ∧ I ⊆ part G true S x ∧ I.card = 2 := by
  have hn' : ¬ homogeneous G true (part G true S x) := fun h => hn (closed_clique G h)
  obtain ⟨u,hu,w,hw,hne,ha⟩ := not_clique G hn'
  exact ⟨insert u {w}, pair_indep G ha, insert_subset hu (singleton_subset_iff.mpr hw),
    card_pair hne⟩
private lemma R1 (hf : sparse G) {S x} (hi : bound G false S 2) (hx : x ∈ S)
    (hA : (part G false S x).card = 5) : homogeneous G true (insert x (part G true S x)) := by
  have hcl := (two_clique G hf hi hx).1
  by_contra hn
  obtain ⟨I,hI,hIN,hIc⟩ := bad_pair G hn
  obtain ⟨J,hJ,hJS,hJc,-⟩ := ext_step G hf hA hcl (part_sub G false S x) hI
    (hIN.trans (part_sub G true S x)) (by omega) ((parts_disj G S x).mono_left hIN)
  have := hi J hJS hJ
  omega
private lemma R2 (hf : sparse G) {S x} {Q1 Q2 : Vertices} (hi : bound G false S 3)
    (h1 : Q1 ⊆ part G false S x) (h2 : Q2 ⊆ part G false S x) (hd : Disjoint Q1 Q2)
    (c1 : Q1.card = 5) (c2 : Q2.card = 5) (k1 : homogeneous G true Q1)
    (k2 : homogeneous G true Q2) : homogeneous G true (insert x (part G true S x)) := by
  by_contra hn
  obtain ⟨I,hI,hIN,hIc⟩ := bad_pair G hn
  have hA := part_sub G false S x
  have hdA : Disjoint I (part G false S x) := (parts_disj G S x).mono_left hIN
  obtain ⟨J,hJ,hJS,hJc,hJs⟩ := ext_step G hf c1 k1 (h1.trans hA) hI
    (hIN.trans (part_sub G true S x)) (by omega) (hdA.mono_right h1)
  obtain ⟨K,hK,hKS,hKc,-⟩ := ext_step G hf c2 k2 (h2.trans hA) hJ hJS (by omega)
    (disjoint_of_subset_left hJs (disjoint_union_left.mpr ⟨hdA.mono_right h2, hd⟩))
  have := hi K hKS hK
  omega
private lemma R3 (hf : sparse G) {S x} {Q1 Q2 Q3 : Vertices} (hi : bound G false S 4)
    (h1 : Q1 ⊆ part G false S x) (h2 : Q2 ⊆ part G false S x) (h3 : Q3 ⊆ part G false S x)
    (hd12 : Disjoint Q1 Q2) (hd13 : Disjoint Q1 Q3) (hd23 : Disjoint Q2 Q3)
    (c1 : Q1.card = 5) (c2 : Q2.card = 5) (c3 : Q3.card = 5) (k1 : homogeneous G true Q1)
    (k2 : homogeneous G true Q2) (k3 : homogeneous G true Q3) :
    homogeneous G true (insert x (part G true S x)) := by
  by_contra hn
  obtain ⟨I,hI,hIN,hIc⟩ := bad_pair G hn
  have hA := part_sub G false S x
  have hdA : Disjoint I (part G false S x) := (parts_disj G S x).mono_left hIN
  obtain ⟨J,hJ,hJS,hJc,hJs⟩ := ext_step G hf c1 k1 (h1.trans hA) hI
    (hIN.trans (part_sub G true S x)) (by omega) (hdA.mono_right h1)
  obtain ⟨K,hK,hKS,hKc,hKs⟩ := ext_step G hf c2 k2 (h2.trans hA) hJ hJS (by omega)
    (disjoint_of_subset_left hJs (disjoint_union_left.mpr ⟨hdA.mono_right h2, hd12⟩))
  have hJ3 : Disjoint J Q3 :=
    disjoint_of_subset_left hJs (disjoint_union_left.mpr ⟨hdA.mono_right h3, hd13⟩)
  obtain ⟨L,hL,hLS,hLc,-⟩ := ext_step G hf c3 k3 (h3.trans hA) hK hKS (by omega)
    (disjoint_of_subset_left hKs (disjoint_union_left.mpr ⟨hJ3, hd23⟩))
  have := hi L hLS hL
  omega

/-- The greedy step: a vertex of minimum degree inside `S`. -/
private lemma desc (hf : sparse G) {S : Vertices} {k : ℕ} (hi : bound G false S (k+1))
    (hne : S.Nonempty) :
    ∃ x ∈ S, (∀ z ∈ S, (part G true S x).card ≤ (part G true S z).card) ∧
      bound G false (part G false S x) k ∧
      (part G true S x).card + (part G false S x).card + 1 = S.card ∧
      S.card * (part G true S x).card ≤ arcs G S S ∧
      2 * ((part G true S x).card * (part G true S x).card) +
        arcs G (part G false S x) (part G false S x)
        ≤ arcs G S S + arcs G (part G true S x) (part G true S x) ∧
      arcs G (part G true S x) (part G true S x) ≤ capT (part G true S x).card := by
  obtain ⟨x,hx,hm⟩ := exists_min_image S (fun z => (part G true S z).card) hne
  refine ⟨x,hx,hm,bound_part G hi hx,part_sizes G hx,arcs_floor G hm,?_,?_⟩
  · have hNS : (part G true S x).card * (part G true S x).card ≤ arcs G (part G true S x) S :=
      arcs_floor G (fun z hz => hm z (part_sub G true S x hz))
    have hrow := row_split G hx
    have hall := splits_at G hx
    generalize (part G true S x).card * (part G true S x).card = q at *
    omega
  · unfold capT
    split_ifs with h5
    · have hd : Disjoint {x} (part G true S x) :=
        disjoint_singleton_left.mpr (self_out G true S x)
      have he : ({x} ∪ part G true S x).card = 6 := by
        rw [card_union_of_disjoint hd,card_singleton,h5]
      have h := hf _ he
      rw [arcs_partition G hd,arcs_diag_single,star_count,h5] at h
      omega
    · exact arcs_ceiling G (fun z hz => by have := part_sizes G hz; omega)

private lemma L2big (hf : sparse G) {S} (hi : bound G false S 2) (h11 : 11 ≤ S.card)
    (ha : arcs G S S < S.card * (S.card - 5)) : False := by
  obtain ⟨x,hx,-,-,hsz,hdeg,-,-⟩ := desc G hf hi (card_pos.mp (by omega))
  obtain ⟨-,hA5⟩ := two_clique G hf hi hx
  by_cases h5 : (part G false S x).card = 5
  · have := clique_le_five G hf (R1 G hf hi hx h5)
    rw [cap_add] at this
    omega
  · have h : S.card - 5 ≤ (part G true S x).card := by omega
    have := Nat.mul_le_mul_left S.card h
    omega
private lemma L2ten (hf : sparse G) {S} (hi : bound G false S 2) (h10 : S.card = 10) :
    (∃ Q1 Q2 : Vertices, Q1 ∪ Q2 = S ∧ Disjoint Q1 Q2 ∧ Q1.card = 5 ∧ Q2.card = 5 ∧
      homogeneous G true Q1 ∧ homogeneous G true Q2) ∨ 50 ≤ arcs G S S := by
  obtain ⟨x,hx,-,-,hsz,hdeg,-,-⟩ := desc G hf hi (card_pos.mp (by omega))
  obtain ⟨hcl,hA5⟩ := two_clique G hf hi hx
  by_cases h5 : (part G false S x).card = 5
  · left
    obtain ⟨hd, hu⟩ := partition G S hx
    exact ⟨_, _, hu, hd, by rw [cap_add]; omega, h5, R1 G hf hi hx h5, hcl⟩
  · right
    have h : 5 ≤ (part G true S x).card := by omega
    have := Nat.mul_le_mul_left S.card h
    omega

private lemma level3 (hf : sparse G) {S} {n a : ℕ} (hi : bound G false S 3) (hn : S.card = n)
    (ha : arcs G S S ≤ a) (hnum : Num3 n a) (hpos : 0 < n) : False := by
  obtain ⟨x,hx,-,hb,hsz,hdeg,hacc,hcap⟩ := desc G hf hi (card_pos.mp (by omega))
  generalize hd : (part G true S x).card = d at *
  have h1 : d < n := by omega
  have h2 : d * n ≤ a := by rw [hn] at hdeg; rw [Nat.mul_comm]; omega
  have hA : arcs G (part G false S x) (part G false S x) ≤ a + capT d - 2 * (d * d) := by
    omega
  rcases hnum d h1 h2 with ⟨h11, hlt⟩ | ⟨h10, h5, hlt⟩
  · have hc : (part G false S x).card = n - 1 - d := by omega
    exact L2big G hf hb (by omega) (by rw [hc]; omega)
  · have hc : (part G false S x).card = 10 := by omega
    rcases L2ten G hf hb hc with ⟨Q1,Q2,hu,hdj,c1,c2,k1,k2⟩ | h50
    · have hB := R2 G hf (S := S) (x := x) hi (by rw [← hu]; exact subset_union_left)
        (by rw [← hu]; exact subset_union_right) hdj c1 c2 k1 k2
      have := clique_le_five G hf hB
      rw [cap_add] at this
      omega
    · omega
private lemma level4 (hf : sparse G) {S} {n a : ℕ} (hi : bound G false S 4) (hn : S.card = n)
    (ha : arcs G S S ≤ a) (hnum : Num4 n a) (hpos : 0 < n) : False := by
  obtain ⟨x,hx,-,hb,hsz,hdeg,hacc,hcap⟩ := desc G hf hi (card_pos.mp (by omega))
  generalize hd : (part G true S x).card = d at *
  have h1 : d < n := by omega
  have h2 : d * n ≤ a := by rw [hn] at hdeg; rw [Nat.mul_comm]; omega
  have hA : arcs G (part G false S x) (part G false S x) ≤ a + capT d - 2 * (d * d) := by
    omega
  obtain ⟨hp, h3⟩ := hnum d h1 h2
  exact level3 G hf hb (by omega) hA h3 hp

private lemma add_two {I : Vertices} {p q : V} (hI : homogeneous G false I)
    (hpq : ¬ G.Adj p q) (hp : ∀ u ∈ I, ¬ G.Adj p u) (hq : ∀ u ∈ I, ¬ G.Adj q u) :
    homogeneous G false (insert p (insert q I)) :=
  homog_insert G (homog_insert G hI hq) (fun y hy => by
    rcases mem_insert.mp hy with h | h
    · rw [h]; exact hpq
    · exact hp y h)
/-- Two more independent vertices from a set that `I` hardly sees. -/
private lemma free_pair (hf : sparse G) {A I : Vertices} (hI : homogeneous G false I)
    (hdis : Disjoint I A) (hcnt : arcs G I A + 6 ≤ A.card) :
    ∃ J : Vertices, homogeneous G false J ∧ J ⊆ I ∪ A ∧ J.card = I.card + 2 := by
  have hD : (I.biUnion (fun u => part G true A u)).card ≤ arcs G I A := card_biUnion_le
  have hDA : I.biUnion (fun u => part G true A u) ⊆ A :=
    biUnion_subset.mpr (fun u _ => part_sub G true A u)
  have hR : 6 ≤ (A \ I.biUnion (fun u => part G true A u)).card := by
    rw [card_sdiff_of_subset hDA]; omega
  have hnc : ¬ homogeneous G true (A \ I.biUnion (fun u => part G true A u)) := fun h => by
    have := clique_le_five G hf h; omega
  obtain ⟨p,hp,q,hq,hne,ha⟩ := not_clique G hnc
  have key : ∀ r ∈ A \ I.biUnion (fun u => part G true A u), ∀ u ∈ I, ¬ G.Adj r u := by
    intro r hr u hu had
    obtain ⟨hrA, hrD⟩ := mem_sdiff.mp hr
    exact hrD (mem_biUnion.mpr ⟨u, hu, (in_part G).mpr ⟨hrA, had.ne, had.symm⟩⟩)
  have hpA := (mem_sdiff.mp hp).1
  have hqA := (mem_sdiff.mp hq).1
  have hpI : p ∉ I := fun h => disjoint_left.mp hdis h hpA
  have hqI : q ∉ I := fun h => disjoint_left.mp hdis h hqA
  refine ⟨insert p (insert q I), add_two G hI ha (key p hp) (key q hq), ?_, ?_⟩
  · exact insert_subset (mem_union_right _ hpA)
      (insert_subset (mem_union_right _ hqA) subset_union_left)
  · rw [card_insert_of_notMem, card_insert_of_notMem hqI]
    intro h
    rcases mem_insert.mp h with h | h
    · exact hne h
    · exact hpI h


private lemma pick' {Q U : Vertices} (hQ : Q.card = 5) (h : arcs G U Q ≤ 4) :
    ∃ y ∈ Q, ∀ u ∈ U, ¬ G.Adj u y := by
  have hc : (U.biUnion (fun u => part G true Q u)).card ≤ arcs G U Q := card_biUnion_le
  obtain ⟨y, hy, hny⟩ := exists_mem_notMem_of_card_lt_card
    (show (U.biUnion (fun u => part G true Q u)).card < Q.card by omega)
  exact ⟨y, hy, fun u hu ha =>
    hny (mem_biUnion.mpr ⟨u, hu, (in_part G).mpr ⟨hy, ha.ne.symm, ha⟩⟩)⟩
private lemma ext2 (hf : sparse G) {Q I Qd : Vertices} {e : ℕ} (hQ : Q.card = 5)
    (hcl : homogeneous G true Q) (hI : homogeneous G false I) (hc : I.card ≤ 4)
    (hdis : Disjoint I Q) (he : ∀ y ∈ Q, (part G true Qd y).card ≤ e) :
    ∃ J : Vertices, homogeneous G false J ∧ J.card = I.card + 1 ∧ J ⊆ I ∪ Q ∧
      arcs G J Qd ≤ arcs G I Qd + e := by
  obtain ⟨y, hy, hn⟩ := pick G hf hQ hcl hc hdis
  have hyI : y ∉ I := fun h => disjoint_left.mp hdis h hy
  refine ⟨insert y I, homog_insert G hI (fun u hu ha => hn u hu ha.symm),
    card_insert_of_notMem hyI, insert_subset (mem_union_right _ hy) subset_union_left, ?_⟩
  rw [insert_eq, arcs_add_left G (disjoint_singleton_left.mpr hyI), arcs_singleton]
  have := he y hy
  omega
private lemma fin4 (hf : sparse G) (hi : bound G false univ 5) {I Qa Qb Qc Qd : Vertices}
    {e : ℕ} (hI : homogeneous G false I) (cI : I.card = 2)
    (ia : Disjoint I Qa) (ib : Disjoint I Qb) (ic : Disjoint I Qc) (id : Disjoint I Qd)
    (ab : Disjoint Qa Qb) (ac : Disjoint Qa Qc) (ad : Disjoint Qa Qd) (bc : Disjoint Qb Qc)
    (bd : Disjoint Qb Qd) (cd : Disjoint Qc Qd)
    (ca : Qa.card = 5) (cb : Qb.card = 5) (cc : Qc.card = 5) (cdd : Qd.card = 5)
    (ka : homogeneous G true Qa) (kb : homogeneous G true Qb) (kc : homogeneous G true Qc)
    (he : ∀ y, y ∈ Qa ∪ Qb ∪ Qc → (part G true Qd y).card ≤ e)
    (hsum : arcs G I Qd + 3 * e ≤ 4) : False := by
  obtain ⟨J,hJ,cJ,sJ,aJ⟩ := ext2 G hf (Qd := Qd) ca ka hI (by omega) ia
    (fun y hy => he y (mem_union_left _ (mem_union_left _ hy)))
  obtain ⟨K,hK,cK,sK,aK⟩ := ext2 G hf (Qd := Qd) cb kb hJ (by omega)
    (disjoint_of_subset_left sJ (disjoint_union_left.mpr ⟨ib, ab⟩))
    (fun y hy => he y (mem_union_left _ (mem_union_right _ hy)))
  have dKc : Disjoint K Qc := disjoint_of_subset_left sK (disjoint_union_left.mpr
    ⟨disjoint_of_subset_left sJ (disjoint_union_left.mpr ⟨ic, ac⟩), bc⟩)
  obtain ⟨L,hL,cL,sL,aL⟩ := ext2 G hf (Qd := Qd) cc kc hK (by omega) dKc
    (fun y hy => he y (mem_union_right _ hy))
  have dLd : Disjoint L Qd := disjoint_of_subset_left sL (disjoint_union_left.mpr
    ⟨disjoint_of_subset_left sK (disjoint_union_left.mpr
      ⟨disjoint_of_subset_left sJ (disjoint_union_left.mpr ⟨id, ad⟩), bd⟩), cd⟩)
  obtain ⟨y,hy,hn⟩ := pick' G cdd (show arcs G L Qd ≤ 4 by omega)
  have hyL : y ∉ L := fun h => disjoint_left.mp dLd h hy
  have hM := homog_insert G hL (fun u hu ha => hn u hu ha.symm)
  have := hi _ (subset_univ _) hM
  rw [card_insert_of_notMem hyL] at this
  omega
private lemma deg_union {X Y : Vertices} (d : Disjoint X Y) (v : V) :
    (part G true (X ∪ Y) v).card = (part G true X v).card + (part G true Y v).card := by
  have := arcs_add_right G d {v}
  simpa [arcs_singleton] using this
private lemma deg_le (X : Vertices) (v : V) :
    (part G true X v).card ≤ (part G true univ v).card :=
  card_le_card (part_mono G (subset_univ X) true v)
private lemma clique_deg {Q} (h : homogeneous G true Q) {q} (hq : q ∈ Q) :
    (part G true Q q).card + 1 = Q.card := by
  have hs := part_sizes G hq
  have h0 : (part G false Q q).card = 0 := card_eq_zero.mpr (eq_empty_iff_forall_notMem.mpr
    (fun v hv => ((in_part G).mp hv).2.2 (h q hq v ((in_part G).mp hv).1
      ((in_part G).mp hv).2.1.symm)))
  omega
private lemma pair_arcs {u a : V} (hne : u ≠ a) (T : Vertices) :
    arcs G (insert u {a}) T = (part G true T u).card + (part G true T a).card := by
  rw [insert_eq, arcs_add_left G (disjoint_singleton.mpr hne), arcs_singleton, arcs_singleton]


private lemma Zcore (hf : sparse G) {S N K : Vertices} {x : V} (hi : bound G false S 2)
    (hmin : ∀ z ∈ S, 6 ≤ (part G true S z).card) (hNS : N ⊆ S) (hKS : K ⊆ S)
    (hd : Disjoint (insert x N) K) (hu : insert x N ∪ K = S) (hxN : ∀ u ∈ N, G.Adj x u)
    (hxK : ∀ k ∈ K, ¬ G.Adj x k) (hxn : x ∉ N) (cN : N.card = 6) (cK : K.card = 4)
    (kK : homogeneous G true K) (hbud : arcs G N N + 2 * arcs G N K ≤ 46) : False := by
  have hNK : Disjoint N K := hd.mono_left (subset_insert x N)
  have hxnK : x ∉ K := fun h => disjoint_left.mp hd (mem_insert_self x N) h
  have hA : ∀ u ∈ N, 5 ≤ (part G true N u).card + (part G true K u).card := by
    intro u hu'
    have h1 := deg_union G hd u
    rw [hu] at h1
    have h2 := hmin u (hNS hu')
    have h3 : (part G true (insert x N) u).card ≤ (part G true N u).card + 1 := by
      have hsub : part G true (insert x N) u ⊆ insert x (part G true N u) := by
        intro v hv
        obtain ⟨h1,h2,h3⟩ := (in_part G).mp hv
        rcases mem_insert.mp h1 with h | h
        · rw [h]; exact mem_insert_self _ _
        · exact mem_insert_of_mem ((in_part G).mpr ⟨h,h2,h3⟩)
      exact (card_le_card hsub).trans (card_insert_le _ _)
    omega
  have hB : ∀ y ∈ K, 3 ≤ (part G true N y).card := by
    intro y hy
    have h1 := deg_union G hd y
    rw [hu] at h1
    have h2 := hmin y (hKS hy)
    have h3 := clique_deg G kK hy
    have h4 : (part G true (insert x N) y).card ≤ (part G true N y).card := by
      apply card_le_card
      intro v hv
      obtain ⟨h1,h2,h3⟩ := (in_part G).mp hv
      rcases mem_insert.mp h1 with h | h
      · rw [h] at h3
        exact (hxK y hy h3.symm).elim
      · exact (in_part G).mpr ⟨h,h2,h3⟩
    omega
  have hC : ∀ u ∈ N, ∀ w ∈ N, u ≠ w →
      (part G true K u).card + (part G true K w).card ≤ 5 ∧
      (G.Adj u w → (part G true K u).card + (part G true K w).card ≤ 4) := by
    intro u hu' w hw huw
    have hIN : insert u ({w} : Vertices) ⊆ N := insert_subset hu' (singleton_subset_iff.mpr hw)
    have dIK : Disjoint (insert u ({w} : Vertices)) K := hNK.mono_left hIN
    have hc6 : (insert u ({w} : Vertices) ∪ K).card = 6 := by
      rw [card_union_of_disjoint dIK, card_pair huw, cK]
    have h := hf _ hc6
    rw [arcs_partition G dIK, clique_arcs G kK, cK, pair_arcs G huw K] at h
    refine ⟨by omega, fun hadj => ?_⟩
    have p := pair_arcs G huw (insert u ({w} : Vertices))
    have h1 : 0 < (part G true (insert u ({w} : Vertices)) u).card := card_pos.mpr
      ⟨w, (in_part G).mpr ⟨mem_insert_of_mem (mem_singleton_self w), huw.symm, hadj⟩⟩
    have h2 : 0 < (part G true (insert u ({w} : Vertices)) w).card := card_pos.mpr
      ⟨u, (in_part G).mpr ⟨mem_insert_self u _, huw, hadj.symm⟩⟩
    omega
  have hD : ∀ v ∈ N, arcs G N N ≤ 12 + 2 * (part G true N v).card := by
    intro v hv
    have hxe : x ∉ N.erase v := fun h => hxn (mem_of_mem_erase h)
    have hd1 : Disjoint {x} (N.erase v) := disjoint_singleton_left.mpr hxe
    have hc6 : ({x} ∪ N.erase v).card = 6 := by
      rw [card_union_of_disjoint hd1, card_singleton, card_erase_of_mem hv, cN]
    have h := hf _ hc6
    have hstar : 5 ≤ (part G true (N.erase v) x).card := by
      have hsub : N.erase v ⊆ part G true (N.erase v) x := fun w hw =>
        (in_part G).mpr ⟨hw, fun e => hxe (e ▸ hw), hxN w (mem_of_mem_erase hw)⟩
      have := card_le_card hsub
      rw [card_erase_of_mem hv, cN] at this
      omega
    rw [arcs_partition G hd1, arcs_diag_single, arcs_singleton] at h
    have hd2 : Disjoint {v} (N.erase v) := disjoint_singleton_left.mpr (notMem_erase v N)
    have h2 := arcs_partition G hd2
    rw [← insert_eq, insert_erase hv, arcs_diag_single, arcs_singleton] at h2
    have h3 := card_le_card (part_mono G (erase_subset v N) true v)
    omega
  have ha : arcs G N N = ∑ v ∈ N, (part G true N v).card := rfl
  have hX : arcs G N K = ∑ v ∈ N, (part G true K v).card := rfl
  have hE : ∀ v ∈ N, 3 ≤ (part G true N v).card := by
    intro v hv
    by_contra hlt
    have h1 := hA v hv
    have h2 : ∀ w ∈ N.erase v, 3 ≤ (part G true N w).card := by
      intro w hw
      have hwN := mem_of_mem_erase hw
      have := (hC v hv w hwN (ne_of_mem_erase hw).symm).1
      have := hA w hwN
      omega
    have h3 := card_nsmul_le_sum _ _ _ h2
    rw [card_erase_of_mem hv, cN, smul_eq_mul] at h3
    have h4 := add_sum_erase N (fun v => (part G true N v).card) hv
    have h5 := hD v hv
    omega
  have h18 := card_nsmul_le_sum _ _ _ hE
  rw [cN, smul_eq_mul] at h18
  have hne : N.Nonempty := card_pos.mp (by omega)
  obtain ⟨v0, hv0, hmin0⟩ := exists_min_image N (fun v => (part G true N v).card) hne
  have h6 := card_nsmul_le_sum _ _ _ hmin0
  rw [cN, smul_eq_mul] at h6
  have hD0 := hD v0 hv0
  have ha18 : arcs G N N = 18 := by omega
  have hs3 : ∀ v ∈ N, (part G true N v).card = 3 := by
    intro v hv
    have h2 : ∀ w ∈ N.erase v, 3 ≤ (part G true N w).card :=
      fun w hw => hE w (mem_of_mem_erase hw)
    have h3 := card_nsmul_le_sum _ _ _ h2
    rw [card_erase_of_mem hv, cN, smul_eq_mul] at h3
    have h4 := add_sum_erase N (fun v => (part G true N v).card) hv
    have := hE v hv
    omega
  have hn2 : ∀ v ∈ N, (part G true K v).card = 2 := by
    intro v hv
    have h1 := hA v hv
    have h2 := hs3 v hv
    by_contra hne2
    obtain ⟨w, hw⟩ := card_pos.mp (show 0 < (part G true N v).card by omega)
    obtain ⟨hwN, hwv, hadj⟩ := (in_part G).mp hw
    have := (hC v hv w hwN hwv.symm).2 hadj
    have := hA w hwN
    have := hs3 w hwN
    omega
  have hX12 : arcs G N K = 12 := by
    rw [hX, sum_congr rfl hn2, sum_const, cN, smul_eq_mul]
  have hKN : ∑ y ∈ K, (part G true N y).card = 12 := by
    have := arcs_sym G K N
    rw [hX12] at this
    exact this
  have hy3 : ∀ y ∈ K, (part G true N y).card = 3 := by
    intro y hy
    have h2 : ∀ w ∈ K.erase y, 3 ≤ (part G true N w).card :=
      fun w hw => hB w (mem_of_mem_erase hw)
    have h3 := card_nsmul_le_sum _ _ _ h2
    rw [card_erase_of_mem hy, cK, smul_eq_mul] at h3
    have h4 := add_sum_erase K (fun v => (part G true N v).card) hy
    have := hB y hy
    omega
  have dom : ∀ u ∈ N, ∀ w ∈ N, u ≠ w → ¬ G.Adj u w →
      K ⊆ part G true K u ∪ part G true K w := by
    intro u hu' w hw huw hna k hk
    by_contra hnot
    have hku : ¬ G.Adj k u := fun h =>
      hnot (mem_union_left _ ((in_part G).mpr ⟨hk, h.ne, h.symm⟩))
    have hkw : ¬ G.Adj k w := fun h =>
      hnot (mem_union_right _ ((in_part G).mpr ⟨hk, h.ne, h.symm⟩))
    have hIN : insert u ({w} : Vertices) ⊆ N := insert_subset hu' (singleton_subset_iff.mpr hw)
    have hkI : k ∉ insert u ({w} : Vertices) := fun h => disjoint_left.mp hNK (hIN h) hk
    have hM := homog_insert G (pair_indep G hna) (fun r hr => by
      rcases mem_insert.mp hr with h | h
      · rw [h]; exact hku
      · rw [mem_singleton.mp h]; exact hkw)
    have := hi _ (insert_subset (hKS hk) (hIN.trans hNS)) hM
    rw [card_insert_of_notMem hkI, card_pair huw] at this
    omega
  obtain ⟨y, hy⟩ := card_pos.mp (show 0 < K.card by omega)
  have hyN : y ∉ N := fun h => disjoint_left.mp hNK h hy
  have hUN := part_sub G true N y
  have cU := hy3 y hy
  have dUW : Disjoint (part G true N y) (N \ part G true N y) := disjoint_sdiff_self_right
  have hUW : part G true N y ∪ (N \ part G true N y) = N := union_sdiff_of_subset hUN
  have cW : (N \ part G true N y).card = 3 := by
    rw [card_sdiff_of_subset hUN, cN, cU]
  have hWcl : homogeneous G true (N \ part G true N y) := by
    refine homog_mono G (two_clique G hf hi (hKS hy)).1 ?_
    intro v hv
    obtain ⟨hvN, hvU⟩ := mem_sdiff.mp hv
    have hvy : v ≠ y := fun e => hyN (e ▸ hvN)
    exact (in_part G).mpr ⟨hNS hvN, hvy, fun hadj => hvU ((in_part G).mpr ⟨hvN, hvy, hadj⟩)⟩
  have hWU : ∀ w ∈ N \ part G true N y, (part G true (part G true N y) w).card = 1 := by
    intro w hw
    have h1 := clique_deg G hWcl hw
    have h2 := deg_union G dUW w
    rw [hUW, hs3 w (mem_sdiff.mp hw).1] at h2
    omega
  have hWUs : arcs G (N \ part G true N y) (part G true N y) = 3 := by
    change ∑ w ∈ N \ part G true N y, (part G true (part G true N y) w).card = 3
    rw [sum_congr rfl hWU, sum_const, cW, smul_eq_mul]
  have hUU : arcs G (part G true N y) (part G true N y) = 6 := by
    have h := arcs_partition G dUW
    rw [hUW, ha18, clique_arcs G hWcl, cW, arcs_sym G _ (N \ part G true N y), hWUs] at h
    omega
  have hUd : ∀ u ∈ part G true N y, (part G true (part G true N y) u).card = 2 := by
    intro u hu'
    have hle : ∀ w ∈ part G true N y, (part G true (part G true N y) w).card ≤ 2 := by
      intro w hw
      have := part_sizes G hw
      omega
    have h3 := sum_le_card_nsmul ((part G true N y).erase u)
      (fun v => (part G true (part G true N y) v).card) 2
      (fun w hw => hle w (mem_of_mem_erase hw))
    rw [card_erase_of_mem hu', cU, smul_eq_mul] at h3
    have h4 := add_sum_erase (part G true N y)
      (fun v => (part G true (part G true N y) v).card) hu'
    have h5 : arcs G (part G true N y) (part G true N y) =
        ∑ v ∈ part G true N y, (part G true (part G true N y) v).card := rfl
    have := hle u hu'
    omega
  have hUcl : homogeneous G true (part G true N y) := by
    intro u hu' w hw huw
    by_contra hna
    have hmem : w ∈ part G false (part G true N y) u := (in_part G).mpr ⟨hw, huw.symm, hna⟩
    have := card_pos.mpr (show (part G false (part G true N y) u).Nonempty from ⟨w, hmem⟩)
    have := part_sizes G hu'
    have := hUd u hu'
    omega
  have hUW1 : ∀ u ∈ part G true N y, (part G true (N \ part G true N y) u).card = 1 := by
    intro u hu'
    have h2 := deg_union G dUW u
    rw [hUW, hs3 u (hUN hu'), hUd u hu'] at h2
    omega
  have same : ∀ u1 ∈ part G true N y, ∀ u2 ∈ part G true N y,
      part G true K u1 = part G true K u2 := by
    intro u1 h1 u2 h2
    have hw : ∃ w ∈ N \ part G true N y, w ∉ part G true (N \ part G true N y) u1 ∧
        w ∉ part G true (N \ part G true N y) u2 := by
      by_contra hno
      have hsub : N \ part G true N y ⊆ part G true (N \ part G true N y) u1 ∪
          part G true (N \ part G true N y) u2 := by
        intro w hw
        by_contra hn
        exact hno ⟨w, hw, fun h => hn (mem_union_left _ h), fun h => hn (mem_union_right _ h)⟩
      have := (card_le_card hsub).trans (card_union_le _ _)
      have := hUW1 u1 h1
      have := hUW1 u2 h2
      omega
    obtain ⟨w, hw, hw1, hw2⟩ := hw
    have hwN := (mem_sdiff.mp hw).1
    have key : ∀ u ∈ part G true N y, w ∉ part G true (N \ part G true N y) u →
        part G true K u = K \ part G true K w := by
      intro u hu' hwu
      have hne : u ≠ w := fun e => (mem_sdiff.mp hw).2 (e ▸ hu')
      have hna : ¬ G.Adj u w := fun hadj => hwu ((in_part G).mpr ⟨hw, hne.symm, hadj⟩)
      have hdom := dom u (hUN hu') w hwN hne hna
      have hc := card_le_card hdom
      have hci := card_union_add_card_inter (part G true K u) (part G true K w)
      have hnu := hn2 u (hUN hu')
      have hnw := hn2 w hwN
      have hint : (part G true K u ∩ part G true K w).card = 0 := by omega
      apply eq_of_subset_of_card_le
      · intro k hk
        refine mem_sdiff.mpr ⟨part_sub G true K u hk, fun hk' => ?_⟩
        have := card_pos.mpr (show (part G true K u ∩ part G true K w).Nonempty from
          ⟨k, mem_inter.mpr ⟨hk, hk'⟩⟩)
        omega
      · rw [card_sdiff_of_subset (part_sub G true K w), cK, hnw, hnu]
    rw [key u1 h1 hw1, key u2 h2 hw2]
  obtain ⟨u1, hu1⟩ := card_pos.mp (show 0 < (part G true N y).card by omega)
  have hyu : ∀ u ∈ part G true N y, G.Adj y u := fun u hu' => ((in_part G).mp hu').2.2
  have hyK1 : y ∈ part G true K u1 :=
    (in_part G).mpr ⟨hy, (hyu u1 hu1).ne, (hyu u1 hu1).symm⟩
  obtain ⟨y', hy'⟩ := card_pos.mp (show 0 < ((part G true K u1).erase y).card by
    rw [card_erase_of_mem hyK1, hn2 u1 (hUN hu1)]; omega)
  obtain ⟨hy'ne, hy'K1⟩ := mem_erase.mp hy'
  have hy'K : y' ∈ K := part_sub G true K u1 hy'K1
  have hy'u : ∀ u ∈ part G true N y, G.Adj y' u := by
    intro u hu'
    have : y' ∈ part G true K u := by rw [same u hu' u1 hu1]; exact hy'K1
    exact (((in_part G).mp this).2.2 : G.Adj u y').symm
  have hy'N : y' ∉ N := fun h => disjoint_left.mp hNK h hy'K
  have hQ1 : homogeneous G true (insert y (part G true N y)) :=
    homog_insert G hUcl (fun u hu' => hyu u hu')
  have hQ2 : homogeneous G true (insert y' (insert y (part G true N y))) :=
    homog_insert G hQ1 (fun r hr => by
      rcases mem_insert.mp hr with h | h
      · rw [h]; exact kK y' hy'K y hy hy'ne
      · exact hy'u r h)
  have hyU : y ∉ part G true N y := fun h => hyN (hUN h)
  have hy'Q : y' ∉ insert y (part G true N y) := fun h => by
    rcases mem_insert.mp h with h | h
    · exact hy'ne h
    · exact hy'N (hUN h)
  have hQc : (insert y' (insert y (part G true N y))).card = 5 := by
    rw [card_insert_of_notMem hy'Q, card_insert_of_notMem hyU, cU]
  have hxQ : x ∉ insert y' (insert y (part G true N y)) := fun h => by
    rcases mem_insert.mp h with h | h
    · exact hxnK (h ▸ hy'K)
    rcases mem_insert.mp h with h | h
    · exact hxnK (h ▸ hy)
    · exact hxn (hUN h)
  have hex := k5_exit G hf hQc hQ2 hxQ
  have hsub : part G true N y ⊆ part G true (insert y' (insert y (part G true N y))) x :=
    fun u hu' => (in_part G).mpr ⟨mem_insert_of_mem (mem_insert_of_mem hu'),
      fun e => hxn (e ▸ hUN hu'), hxN u (hUN hu')⟩
  have := card_le_card hsub
  omega

private lemma Zlem (hf : sparse G) {S} (hi : bound G false S 2) (h11 : S.card = 11)
    (ha : arcs G S S ≤ 70) : False := by
  obtain ⟨x,hx,hm,hb,hsz,hdeg,hacc,hcap⟩ := desc G hf hi (card_pos.mp (by omega))
  obtain ⟨hKcl,hA5⟩ := two_clique G hf hi hx
  have hd6 : (part G true S x).card = 6 := by
    by_contra hne
    by_cases h5 : (part G false S x).card = 5
    · have := clique_le_five G hf (R1 G hf hi hx h5)
      rw [cap_add] at this
      omega
    · have h7 : 7 ≤ (part G true S x).card := by omega
      have := Nat.mul_le_mul_left S.card h7
      omega
  have hK4 : (part G false S x).card = 4 := by omega
  obtain ⟨hd, hu⟩ := partition G S hx
  have hall := splits_at G hx
  rw [hd6, clique_arcs G hKcl, hK4] at hall
  exact Zcore G hf hi (fun z hz => by have := hm z hz; omega) (part_sub G true S x)
    (part_sub G false S x) hd hu (fun u hu' => ((in_part G).mp hu').2.2)
    (fun k hk => ((in_part G).mp hk).2.2) (self_out G true S x) hd6 hK4 hKcl (by omega)

private lemma K5pair (hf : sparse G) {A R : Vertices} (hA2 : bound G false A 2) (hRA : R ⊆ A)
    (cR : R.card = 5) (kR : homogeneous G true R) : homogeneous G true (A \ R) := by
  by_contra hn
  obtain ⟨p,hp,q,hq,hne,ha⟩ := not_clique G hn
  have hI := pair_indep G ha
  have hIs : insert p ({q} : Vertices) ⊆ A \ R :=
    insert_subset hp (singleton_subset_iff.mpr hq)
  obtain ⟨J,hJ,hJS,hJc,-⟩ := ext_step G hf cR kR hRA hI (hIs.trans sdiff_subset)
    (by rw [card_pair hne]; omega) (disjoint_sdiff_self_left.mono_left hIs)
  have := hA2 J hJS hJ
  rw [hJc, card_pair hne] at this
  omega

private lemma tail (hf : sparse G) {T A : Vertices} {x} (hx : x ∈ T)
    (h5 : (part G true T x).card = 5) (hmin : ∀ z ∈ T, 5 ≤ (part G true T z).card)
    (hAC : A ⊆ part G false T x) (hA10 : A.card = 10) (hA2 : bound G false A 2)
    (hbud : arcs G T T ≤ arcs G (part G false T x) (part G false T x) + 40)
    (hind : ∀ J : Vertices, homogeneous G false J → J ⊆ part G true T x ∪ A → J.card ≤ 3) :
    False := by
  have hpart := partition G T hx
  have hNC : Disjoint (part G true T x) (part G false T x) := parts_disj G T x
  have hNA : Disjoint (part G true T x) A := hNC.mono_right hAC
  have hNT := part_sub G true T x
  have F1 : ∀ u ∈ part G true T x, (part G false (part G true T x) u).card ≤
      (part G true (part G false T x) u).card := by
    intro u hu
    have h1 := deg_union G hpart.1 u
    rw [hpart.2] at h1
    have h2 := hmin u (hNT hu)
    have h3 : (part G true (insert x (part G true T x)) u).card ≤
        (part G true (part G true T x) u).card + 1 := by
      have hsub : part G true (insert x (part G true T x)) u ⊆
          insert x (part G true (part G true T x) u) := by
        intro v hv
        obtain ⟨h1,h2,h3⟩ := (in_part G).mp hv
        rcases mem_insert.mp h1 with h | h
        · rw [h]; exact mem_insert_self _ _
        · exact mem_insert_of_mem ((in_part G).mpr ⟨h,h2,h3⟩)
      exact (card_le_card hsub).trans (card_insert_le _ _)
    have h4 := part_sizes G hu
    omega
  have hM : arcs G (part G true T x) (part G true T x) +
      ∑ v ∈ part G true T x, (part G false (part G true T x) v).card = 20 := by
    have h : ∑ v ∈ part G true T x, ((part G true (part G true T x) v).card +
        (part G false (part G true T x) v).card + 1) = ∑ _v ∈ part G true T x, 5 :=
      sum_congr rfl (fun v hv => by rw [part_sizes G hv, h5])
    simp only [sum_add_distrib, sum_const, smul_eq_mul, h5] at h
    change (∑ v ∈ part G true T x, (part G true (part G true T x) v).card) + _ = 20
    omega
  have hbM : ∑ v ∈ part G true T x, (part G false (part G true T x) v).card ≤
      arcs G (part G true T x) (part G false T x) := sum_le_sum F1
  have hall := splits_at G hx
  rw [h5] at hall
  have hcapN : arcs G (part G true T x) (part G true T x) ≤ 12 := by
    have hd : Disjoint {x} (part G true T x) :=
      disjoint_singleton_left.mpr (self_out G true T x)
    have he : ({x} ∪ part G true T x).card = 6 := by
      rw [card_union_of_disjoint hd,card_singleton,h5]
    have h := hf _ he
    rw [arcs_partition G hd,arcs_diag_single,star_count,h5] at h
    omega
  obtain ⟨k,hk⟩ := arcs_even G (part G true T x)
  -- two non-adjacent neighbours of x see at least six vertices of A
  have pairR : ∀ u ∈ part G true T x, ∀ w ∈ part G true T x, u ≠ w → ¬ G.Adj u w →
      homogeneous G true (A \ (part G true A u ∪ part G true A w)) := by
    intro u hu w hw huw hna
    by_contra hn
    obtain ⟨p,hp,q,hq,hpq,ha⟩ := not_clique G hn
    obtain ⟨hpA,hpD⟩ := mem_sdiff.mp hp
    obtain ⟨hqA,hqD⟩ := mem_sdiff.mp hq
    have np : ∀ v, v ∈ A → v ∉ part G true A u ∪ part G true A w →
        ∀ r ∈ insert u ({w} : Vertices), ¬ G.Adj v r := by
      intro v hvA hvD r hr hadj
      rcases mem_insert.mp hr with h | h
      · rw [h] at hadj
        exact hvD (mem_union_left _ ((in_part G).mpr ⟨hvA, hadj.ne, hadj.symm⟩))
      · rw [mem_singleton.mp h] at hadj
        exact hvD (mem_union_right _ ((in_part G).mpr ⟨hvA, hadj.ne, hadj.symm⟩))
    have hJ := add_two G (pair_indep G hna) ha (np p hpA hpD) (np q hqA hqD)
    have hIN : insert u ({w} : Vertices) ⊆ part G true T x :=
      insert_subset hu (singleton_subset_iff.mpr hw)
    have hpI : p ∉ insert u ({w} : Vertices) := fun h => disjoint_left.mp hNA (hIN h) hpA
    have hqI : q ∉ insert u ({w} : Vertices) := fun h => disjoint_left.mp hNA (hIN h) hqA
    have hc : (insert p (insert q (insert u ({w} : Vertices)))).card = 4 := by
      rw [card_insert_of_notMem, card_insert_of_notMem hqI, card_pair huw]
      intro h
      rcases mem_insert.mp h with h | h
      · exact hpq h
      · exact hpI h
    have := hind _ hJ (insert_subset (mem_union_right _ hpA)
      (insert_subset (mem_union_right _ hqA) (hIN.trans subset_union_left)))
    omega
  have pair6 : ∀ u ∈ part G true T x, ∀ w ∈ part G true T x, u ≠ w → ¬ G.Adj u w →
      6 ≤ (part G true A u).card + (part G true A w).card := by
    intro u hu w hw huw hna
    by_contra hlt
    have hR := pairR u hu w hw huw hna
    have hDA : part G true A u ∪ part G true A w ⊆ A :=
      union_subset (part_sub G true A u) (part_sub G true A w)
    have hDc := card_union_le (part G true A u) (part G true A w)
    have hRc : (A \ (part G true A u ∪ part G true A w)).card =
        10 - (part G true A u ∪ part G true A w).card := by
      rw [card_sdiff_of_subset hDA, hA10]
    have hR5 := clique_le_five G hf hR
    have hD5 : (part G true A u ∪ part G true A w).card = 5 := by omega
    have hRc5 : (A \ (part G true A u ∪ part G true A w)).card = 5 := by omega
    have hDk := K5pair G hf hA2 sdiff_subset hRc5 hR
    rw [Finset.sdiff_sdiff_eq_self hDA] at hDk
    have huD : u ∉ part G true A u ∪ part G true A w :=
      fun h => disjoint_left.mp hNA hu (hDA h)
    have hwD : w ∉ part G true A u ∪ part G true A w :=
      fun h => disjoint_left.mp hNA hw (hDA h)
    have h1 := k5_exit G hf hD5 hDk huD
    have h2 := k5_exit G hf hD5 hDk hwD
    have s1 : part G true A u ⊆ part G true (part G true A u ∪ part G true A w) u :=
      fun v hv => (in_part G).mpr ⟨mem_union_left _ hv, ((in_part G).mp hv).2⟩
    have s2 : part G true A w ⊆ part G true (part G true A u ∪ part G true A w) w :=
      fun v hv => (in_part G).mpr ⟨mem_union_right _ hv, ((in_part G).mp hv).2⟩
    have := card_le_card s1
    have := card_le_card s2
    omega
  have cAle : ∀ u, (part G true A u).card ≤ (part G true (part G false T x) u).card :=
    fun u => card_le_card (part_mono G hAC true u)
  -- pair bound in terms of non-neighbour counts
  have PB : ∀ u ∈ part G true T x, ∀ w ∈ part G true T x, u ≠ w → ¬ G.Adj u w →
      (∑ v ∈ part G true T x, (part G false (part G true T x) v).card) + 2 ≤
        2 * ((part G false (part G true T x) u).card +
          (part G false (part G true T x) w).card) := by
    intro u hu w hw huw hna
    have h6 := pair6 u hu w hw huw hna
    have hw' : w ∈ (part G true T x).erase u := mem_erase.mpr ⟨huw.symm, hw⟩
    have e1 := add_sum_erase (part G true T x)
      (fun v => (part G true (part G false T x) v).card) hu
    have e2 := add_sum_erase ((part G true T x).erase u)
      (fun v => (part G true (part G false T x) v).card) hw'
    have e3 := add_sum_erase (part G true T x)
      (fun v => (part G false (part G true T x) v).card) hu
    have e4 := add_sum_erase ((part G true T x).erase u)
      (fun v => (part G false (part G true T x) v).card) hw'
    have e5 : ∑ v ∈ ((part G true T x).erase u).erase w,
        (part G false (part G true T x) v).card ≤
        ∑ v ∈ ((part G true T x).erase u).erase w,
          (part G true (part G false T x) v).card :=
      sum_le_sum (fun v hv => F1 v (mem_of_mem_erase (mem_of_mem_erase hv)))
    have hb : arcs G (part G true T x) (part G false T x) =
        ∑ v ∈ part G true T x, (part G true (part G false T x) v).card := rfl
    have := cAle u
    have := cAle w
    omega
  have hne : (part G true T x).Nonempty := card_pos.mp (by omega)
  obtain ⟨t, ht, hmax⟩ := exists_max_image (part G true T x)
    (fun v => (part G false (part G true T x) v).card) hne
  have hsz := part_sizes G ht
  have havg : ∑ v ∈ part G true T x, (part G false (part G true T x) v).card ≤
      (part G true T x).card • (part G false (part G true T x) t).card :=
    sum_le_card_nsmul _ _ _ hmax
  rw [h5, smul_eq_mul] at havg
  have hPsub : insert t (part G false (part G true T x) t) ⊆ part G true T x :=
    insert_subset ht (part_sub G false _ t)
  have hPsum := sum_le_sum_of_subset (f := fun v => (part G false (part G true T x) v).card)
    hPsub
  rw [sum_insert (self_out G false _ t)] at hPsum
  have hPB : ∀ v ∈ part G false (part G true T x) t,
      (∑ v ∈ part G true T x, (part G false (part G true T x) v).card) + 2 ≤
        2 * ((part G false (part G true T x) t).card +
          (part G false (part G true T x) v).card) := by
    intro v hv
    obtain ⟨hvN, hvt, hvn⟩ := (in_part G).mp hv
    exact PB t ht v hvN hvt.symm hvn
  have hPne : (part G false (part G true T x) t).Nonempty := card_pos.mp (by omega)
  obtain ⟨v0, hv0⟩ := hPne
  have hv0b := hPB v0 hv0
  have hv0m := hmax v0 (part_sub G false _ t hv0)
  -- the sum of non-neighbour counts is 8 and t misses everybody
  have hlow : ∀ c : ℕ, (∀ v ∈ part G false (part G true T x) t,
      c ≤ (part G false (part G true T x) v).card) →
      (part G false (part G true T x) t).card * c ≤
        ∑ v ∈ part G false (part G true T x) t, (part G false (part G true T x) v).card := by
    intro c hc
    have := card_nsmul_le_sum _ _ _ hc
    rwa [smul_eq_mul] at this
  have hM8 : ∑ v ∈ part G true T x, (part G false (part G true T x) v).card = 8 ∧
      (part G false (part G true T x) t).card = 4 := by
    have hl := hlow ((∑ v ∈ part G true T x, (part G false (part G true T x) v).card) / 2 + 1 -
      (part G false (part G true T x) t).card) (fun v hv => by have := hPB v hv; omega)
    generalize (∑ v ∈ part G true T x, (part G false (part G true T x) v).card) = M at *
    generalize (part G false (part G true T x) t).card = mt at *
    have hmt : mt ≤ 4 := by omega
    have hM' : M = 8 ∨ M = 10 := by omega
    rcases hM' with h | h
    · subst h
      interval_cases mt <;> omega
    · subst h
      interval_cases mt <;> omega
  obtain ⟨hM8a, hmt4⟩ := hM8
  have hP1 : ∀ v ∈ part G false (part G true T x) t,
      1 ≤ (part G false (part G true T x) v).card := by
    intro v hv
    have := hPB v hv
    omega
  -- neighbour counts in the lower part
  have hcc := sum_le_sum_of_subset (f := fun v => (part G true (part G false T x) v).card)
    hPsub
  rw [sum_insert (self_out G false _ t)] at hcc
  have hb : arcs G (part G true T x) (part G false T x) =
      ∑ v ∈ part G true T x, (part G true (part G false T x) v).card := rfl
  have hc6 : ∀ v ∈ part G false (part G true T x) t,
      6 ≤ (part G true A t).card + (part G true A v).card := by
    intro v hv
    obtain ⟨hvN, hvt, hvn⟩ := (in_part G).mp hv
    exact pair6 t ht v hvN hvt.symm hvn
  have hcl1 : ∀ v ∈ part G false (part G true T x) t,
      1 ≤ (part G true (part G false T x) v).card :=
    fun v hv => (hP1 v hv).trans (F1 v (part_sub G false _ t hv))
  have hs1 := card_nsmul_le_sum _ _ _ hcl1
  have hs2 := card_nsmul_le_sum (part G false (part G true T x) t)
    (fun v => (part G true (part G false T x) v).card)
    (6 - (part G true (part G false T x) t).card)
    (fun v hv => by have := hc6 v hv; have := cAle t; have := cAle v; omega)
  rw [hmt4, smul_eq_mul] at hs1 hs2
  have hct5 : (part G true (part G false T x) t).card = 5 := by omega
  have hcv1 : ∀ v ∈ part G false (part G true T x) t,
      (part G true (part G false T x) v).card ≤ 1 := by
    intro v hv
    have e := add_sum_erase (part G false (part G true T x) t)
      (fun v => (part G true (part G false T x) v).card) hv
    have hs3 := card_nsmul_le_sum ((part G false (part G true T x) t).erase v)
      (fun v => (part G true (part G false T x) v).card) 1
      (fun w hw => hcl1 w (mem_of_mem_erase hw))
    rw [card_erase_of_mem hv, hmt4, smul_eq_mul] at hs3
    omega
  have hAt5 : (part G true A t).card = 5 := by
    have := hc6 v0 hv0
    have := cAle t
    have := cAle v0
    have := hcv1 v0 hv0
    omega
  have hAv1 : ∀ v ∈ part G false (part G true T x) t, (part G true A v).card ≤ 1 :=
    fun v hv => (cAle v).trans (hcv1 v hv)
  -- the four other neighbours of x form a 5-clique with x
  have hPcl : homogeneous G true (part G false (part G true T x) t) := by
    intro l hl l' hl' hne
    by_contra hna
    have := pair6 l (part_sub G false _ t hl) l' (part_sub G false _ t hl') hne hna
    have := hAv1 l hl
    have := hAv1 l' hl'
    omega
  have hQcl : homogeneous G true (insert x (part G false (part G true T x) t)) :=
    homog_insert G hPcl (fun l hl => ((in_part G).mp (part_sub G false _ t hl)).2.2)
  have hxP : x ∉ part G false (part G true T x) t :=
    fun h => self_out G true T x (part_sub G false _ t h)
  have hQc : (insert x (part G false (part G true T x) t)).card = 5 := by
    rw [card_insert_of_notMem hxP, hmt4]
  have hQB : insert x (part G false (part G true T x) t) ⊆ insert x (part G true T x) :=
    insert_subset_insert _ (part_sub G false _ t)
  have hFc : (A \ part G true A t).card = 5 := by
    rw [card_sdiff_of_subset (part_sub G true A t), hA10, hAt5]
  by_cases hF : homogeneous G true (A \ part G true A t)
  · have hDk := K5pair G hf hA2 sdiff_subset hFc hF
    rw [Finset.sdiff_sdiff_eq_self (part_sub G true A t)] at hDk
    have h6 := clique_le_five G hf
      (homog_insert G hDk (fun v hv => ((in_part G).mp hv).2.2))
    rw [card_insert_of_notMem (self_out G true A t), hAt5] at h6
    omega
  · obtain ⟨p,hp,q,hq,hpq,hna⟩ := not_clique G hF
    obtain ⟨hpA,hpt⟩ := mem_sdiff.mp hp
    obtain ⟨hqA,hqt⟩ := mem_sdiff.mp hq
    have cover : part G false (part G true T x) t ⊆
        part G true (part G false (part G true T x) t) p ∪
          part G true (part G false (part G true T x) t) q := by
      intro l hl
      obtain ⟨hlN, hlt, hln⟩ := (in_part G).mp hl
      have hR := pairR t ht l hlN hlt.symm hln
      by_cases hpl : p ∈ part G true A l
      · have hadj : G.Adj l p := ((in_part G).mp hpl).2.2
        exact mem_union_left _ ((in_part G).mpr ⟨hl, hadj.ne, hadj.symm⟩)
      · by_cases hql : q ∈ part G true A l
        · have hadj : G.Adj l q := ((in_part G).mp hql).2.2
          exact mem_union_right _ ((in_part G).mpr ⟨hl, hadj.ne, hadj.symm⟩)
        · exfalso
          have hp' : p ∈ A \ (part G true A t ∪ part G true A l) := mem_sdiff.mpr
            ⟨hpA, fun h => (mem_union.mp h).elim hpt hpl⟩
          have hq' : q ∈ A \ (part G true A t ∪ part G true A l) := mem_sdiff.mpr
            ⟨hqA, fun h => (mem_union.mp h).elim hqt hql⟩
          exact hna (hR p hp' q hq' hpq)
    have hcov := (card_le_card cover).trans (card_union_le _ _)
    have hpQ : p ∉ insert x (part G false (part G true T x) t) :=
      fun h => disjoint_left.mp hpart.1 (hQB h) (hAC hpA)
    have hqQ : q ∉ insert x (part G false (part G true T x) t) :=
      fun h => disjoint_left.mp hpart.1 (hQB h) (hAC hqA)
    have h1 := k5_exit G hf hQc hQcl hpQ
    have h2 := k5_exit G hf hQc hQcl hqQ
    have h3 := card_le_card (part_mono G (subset_insert x
      (part G false (part G true T x) t)) true p)
    have h4 := card_le_card (part_mono G (subset_insert x
      (part G false (part G true T x) t)) true q)
    omega
private lemma reg_cov (hf : sparse G) (hi : bound G false univ 5)
    (reg : ∀ z, (part G true univ z).card = 5) {x} {Q1 Q2 Q3 Q4 : Vertices}
    (s1 : Q1 ⊆ part G false univ x) (s2 : Q2 ⊆ part G false univ x)
    (s3 : Q3 ⊆ part G false univ x) (s4 : Q4 ⊆ part G false univ x)
    (d12 : Disjoint Q1 Q2) (d13 : Disjoint Q1 Q3) (d14 : Disjoint Q1 Q4)
    (d23 : Disjoint Q2 Q3) (d24 : Disjoint Q2 Q4) (d34 : Disjoint Q3 Q4)
    (c1 : Q1.card = 5) (c2 : Q2.card = 5) (c3 : Q3.card = 5) (c4 : Q4.card = 5)
    (k1 : homogeneous G true Q1) (k2 : homogeneous G true Q2) (k3 : homogeneous G true Q3)
    (k4 : homogeneous G true Q4) : False := by
  have hN5 := reg x
  have hNA : Disjoint (part G true univ x) (part G false univ x) := parts_disj G univ x
  have hBA : Disjoint (insert x (part G true univ x)) (part G false univ x) :=
    (partition G univ (mem_univ x)).1
  have e1 : ∀ y, y ∉ Q1 → (part G true Q1 y).card ≤ 1 := fun y hy => k5_exit G hf c1 k1 hy
  have e2 : ∀ y, y ∉ Q2 → (part G true Q2 y).card ≤ 1 := fun y hy => k5_exit G hf c2 k2 hy
  have e3 : ∀ y, y ∉ Q3 → (part G true Q3 y).card ≤ 1 := fun y hy => k5_exit G hf c3 k3 hy
  have e4 : ∀ y, y ∉ Q4 → (part G true Q4 y).card ≤ 1 := fun y hy => k5_exit G hf c4 k4 hy
  -- degree count at a neighbour of x
  have key : ∀ u ∈ part G true univ x,
      (part G true (part G true univ x) u).card + 1 + (part G true Q1 u).card +
        (part G true Q2 u).card + (part G true Q3 u).card + (part G true Q4 u).card ≤ 5 := by
    intro u hu
    obtain ⟨-, hux, hadj⟩ := (in_part G).mp hu
    have hB : (part G true (part G true univ x) u).card + 1 ≤
        (part G true (insert x (part G true univ x)) u).card := by
      have hsub : insert x (part G true (part G true univ x) u) ⊆
          part G true (insert x (part G true univ x)) u := by
        intro v hv
        rcases mem_insert.mp hv with h | h
        · rw [h]
          exact (in_part G).mpr ⟨mem_insert_self _ _, hux.symm, hadj.symm⟩
        · obtain ⟨h1,h2,h3⟩ := (in_part G).mp h
          exact (in_part G).mpr ⟨mem_insert_of_mem h1, h2, h3⟩
      have hxn : x ∉ part G true (part G true univ x) u :=
        fun h => self_out G true univ x (part_sub G true _ u h)
      calc _ = (insert x (part G true (part G true univ x) u)).card :=
            (card_insert_of_notMem hxn).symm
        _ ≤ _ := card_le_card hsub
    have h1 := deg_union G (hBA.mono_right s1) u
    have h2 := deg_union G (disjoint_union_left.mpr ⟨hBA.mono_right s2, d12⟩) u
    have h3 := deg_union G (disjoint_union_left.mpr
      ⟨disjoint_union_left.mpr ⟨hBA.mono_right s3, d13⟩, d23⟩) u
    have h4 := deg_union G (disjoint_union_left.mpr ⟨disjoint_union_left.mpr
      ⟨disjoint_union_left.mpr ⟨hBA.mono_right s4, d14⟩, d24⟩, d34⟩) u
    have h5 := deg_le G (insert x (part G true univ x) ∪ Q1 ∪ Q2 ∪ Q3 ∪ Q4) u
    rw [reg u] at h5
    omega
  have hnc : ¬ homogeneous G true (insert x (part G true univ x)) := fun h => by
    have := clique_le_five G hf h
    rw [cap_add] at this
    omega
  have hnc' : ¬ homogeneous G true (part G true univ x) := fun h => hnc (closed_clique G h)
  have dI : ∀ u ∈ part G true univ x, ∀ a ∈ part G true univ x, ∀ Q : Vertices,
      Q ⊆ part G false univ x → Disjoint (insert u ({a} : Vertices)) Q := fun u hu a ha Q hQ =>
    (hNA.mono_right hQ).mono_left (insert_subset hu (singleton_subset_iff.mpr ha))
  have out : ∀ y, ∀ Q Q' : Vertices, Disjoint Q Q' → y ∈ Q → y ∉ Q' :=
    fun y Q Q' d hy h => disjoint_left.mp d hy h
  by_cases hex : ∃ a ∈ part G true univ x, 1 ≤ (part G true (part G true univ x) a).card
  · -- a non-adjacent pair with few neighbours in the cliques
    have good : ∃ u ∈ part G true univ x, ∃ a ∈ part G true univ x, u ≠ a ∧ ¬ G.Adj u a ∧
        1 ≤ (part G true (part G true univ x) u).card +
          (part G true (part G true univ x) a).card := by
      obtain ⟨a, ha, hsa⟩ := hex
      obtain ⟨u,hu,w,hw,huw,hna⟩ := not_clique G hnc'
      by_cases hua : u = a
      · exact ⟨u,hu,w,hw,huw,hna, by rw [hua]; omega⟩
      by_cases hadj : G.Adj u a
      · have : a ∈ part G true (part G true univ x) u := (in_part G).mpr ⟨ha, fun h => hua h.symm, hadj⟩
        have := card_pos.mpr (show (part G true (part G true univ x) u).Nonempty from ⟨a,this⟩)
        exact ⟨u,hu,w,hw,huw,hna, by omega⟩
      · exact ⟨u,hu,a,ha,hua,hadj, by omega⟩
    obtain ⟨u,hu,a,ha,hua,hna,hs⟩ := good
    have ku := key u hu
    have ka := key a ha
    have hI := pair_indep G hna
    have cI : (insert u ({a} : Vertices)).card = 2 := card_pair hua
    have p1 := pair_arcs G hua Q1
    have p2 := pair_arcs G hua Q2
    have p3 := pair_arcs G hua Q3
    have p4 := pair_arcs G hua Q4
    have hcases : arcs G (insert u {a}) Q1 ≤ 1 ∨ arcs G (insert u {a}) Q2 ≤ 1 ∨
        arcs G (insert u {a}) Q3 ≤ 1 ∨ arcs G (insert u {a}) Q4 ≤ 1 := by omega
    rcases hcases with h | h | h | h
    · exact fin4 G hf hi (e := 1) hI cI (dI u hu a ha Q2 s2) (dI u hu a ha Q3 s3)
        (dI u hu a ha Q4 s4) (dI u hu a ha Q1 s1) d23 d24 d12.symm d34 d13.symm d14.symm
        c2 c3 c4 c1 k2 k3 k4 (fun y hy => e1 y (by
          rcases mem_union.mp hy with hy | hy
          · rcases mem_union.mp hy with hy | hy
            · exact out y Q2 Q1 d12.symm hy
            · exact out y Q3 Q1 d13.symm hy
          · exact out y Q4 Q1 d14.symm hy)) (by omega)
    · exact fin4 G hf hi (e := 1) hI cI (dI u hu a ha Q1 s1) (dI u hu a ha Q3 s3)
        (dI u hu a ha Q4 s4) (dI u hu a ha Q2 s2) d13 d14 d12 d34 d23.symm d24.symm
        c1 c3 c4 c2 k1 k3 k4 (fun y hy => e2 y (by
          rcases mem_union.mp hy with hy | hy
          · rcases mem_union.mp hy with hy | hy
            · exact out y Q1 Q2 d12 hy
            · exact out y Q3 Q2 d23.symm hy
          · exact out y Q4 Q2 d24.symm hy)) (by omega)
    · exact fin4 G hf hi (e := 1) hI cI (dI u hu a ha Q1 s1) (dI u hu a ha Q2 s2)
        (dI u hu a ha Q4 s4) (dI u hu a ha Q3 s3) d12 d14 d13 d24 d23 d34.symm
        c1 c2 c4 c3 k1 k2 k4 (fun y hy => e3 y (by
          rcases mem_union.mp hy with hy | hy
          · rcases mem_union.mp hy with hy | hy
            · exact out y Q1 Q3 d13 hy
            · exact out y Q2 Q3 d23 hy
          · exact out y Q4 Q3 d34.symm hy)) (by omega)
    · exact fin4 G hf hi (e := 1) hI cI (dI u hu a ha Q1 s1) (dI u hu a ha Q2 s2)
        (dI u hu a ha Q3 s3) (dI u hu a ha Q4 s4) d12 d13 d14 d23 d24 d34
        c1 c2 c3 c4 k1 k2 k3 (fun y hy => e4 y (by
          rcases mem_union.mp hy with hy | hy
          · rcases mem_union.mp hy with hy | hy
            · exact out y Q1 Q4 d14 hy
            · exact out y Q2 Q4 d24 hy
          · exact out y Q3 Q4 d34 hy)) (by omega)
  · -- the neighbourhood of x is independent
    have hind : homogeneous G false (part G true univ x) := by
      intro u hu w hw huw hadj
      exact hex ⟨u, hu, card_pos.mpr ⟨w, (in_part G).mpr ⟨hw, huw.symm, hadj⟩⟩⟩
    have seen : ∀ y ∈ part G false univ x, 1 ≤ (part G true (part G true univ x) y).card := by
      intro y hy
      by_contra h0
      have hyN : y ∉ part G true univ x := fun h => disjoint_left.mp hNA h hy
      have hM := homog_insert G hind (fun u hu hadj => h0 (card_pos.mpr
        ⟨u, (in_part G).mpr ⟨hu, fun h => hyN (h ▸ hu), hadj⟩⟩))
      have := hi _ (subset_univ _) hM
      rw [card_insert_of_notMem hyN, hN5] at this
      omega
    have zero : ∀ Q : Vertices, Q ⊆ part G false univ x → Q.card = 5 → homogeneous G true Q →
        Disjoint Q Q4 → ∀ y ∈ Q, (part G true Q4 y).card ≤ 0 := by
      intro Q sQ cQ kQ dQ y hy
      have h1 := clique_deg G kQ hy
      have h2 := seen y (sQ hy)
      have h3 := deg_union G (hNA.mono_right sQ).symm y
      have h4 := deg_union G (disjoint_union_left.mpr ⟨dQ, hNA.mono_right s4⟩) y
      have h5 := deg_le G (Q ∪ part G true univ x ∪ Q4) y
      rw [reg y] at h5
      omega
    obtain ⟨I, hIs, cI⟩ := exists_subset_card_eq (show 2 ≤ (part G true univ x).card by omega)
    have dIQ : ∀ Q : Vertices, Q ⊆ part G false univ x → Disjoint I Q :=
      fun Q hQ => (hNA.mono_right hQ).mono_left hIs
    have hI4 : arcs G I Q4 ≤ I.card * 1 := arcs_ceiling G (fun u hu =>
      e4 u (fun h => disjoint_left.mp (dIQ Q4 s4) hu h))
    exact fin4 G hf hi (e := 0) (homog_mono G hind hIs) cI (dIQ Q1 s1) (dIQ Q2 s2) (dIQ Q3 s3)
      (dIQ Q4 s4) d12 d13 d14 d23 d24 d34 c1 c2 c3 c4 k1 k2 k3 (fun y hy => by
        rcases mem_union.mp hy with hy | hy
        · rcases mem_union.mp hy with hy | hy
          · exact zero Q1 s1 c1 k1 d14 y hy
          · exact zero Q2 s2 c2 k2 d24 y hy
        · exact zero Q3 s3 c3 k3 d34 y hy) (by omega)

private lemma reg_w (hf : sparse G) (hi : bound G false univ 5)
    (reg : ∀ z, (part G true univ z).card = 5) {x y : V} {N2 B3 A3 : Vertices}
    (hyA : y ∈ part G false univ x) (hN2 : N2 ⊆ part G false univ x)
    (hyN : ∀ u ∈ N2, G.Adj y u) (cN2 : N2.card = 4) (hy2 : y ∉ N2)
    (hB3s : B3 ⊆ part G false univ x) (hB3 : homogeneous G true B3) (cB3 : B3.card = 5)
    (hA3s : A3 ⊆ part G false univ x) (c10 : A3.card = 10) (h50 : 50 ≤ arcs G A3 A3)
    (dNB : Disjoint (insert y N2) B3) (dNA : Disjoint (insert y N2) A3)
    (dBA : Disjoint B3 A3) : False := by
  have hdeg : arcs G A3 univ = A3.card * 5 :=
    le_antisymm (arcs_ceiling G (fun q _ => (reg q).le)) (arcs_floor G (fun q _ => (reg q).ge))
  have hdj : Disjoint A3 (univ \ A3) := disjoint_sdiff_self_right
  have hun : A3 ∪ (univ \ A3) = univ := by
    ext v
    simp only [mem_union, mem_sdiff, mem_univ, true_and, iff_true]
    exact Classical.em _
  have hsp := arcs_add_right G hdj A3
  rw [hun, hdeg, c10] at hsp
  have h0 : arcs G A3 (univ \ A3) = 0 := by omega
  have hout : ∀ q ∈ A3, ∀ u, u ∉ A3 → ¬ G.Adj q u := fun q hq u hu =>
    no_cross G h0 hq (mem_sdiff.mpr ⟨mem_univ _, hu⟩)
  have hnc : ¬ homogeneous G true A3 := fun h => by
    have := clique_le_five G hf h
    omega
  obtain ⟨p,hp,q,hq,hne,hpq⟩ := not_clique G hnc
  have addpq : ∀ K : Vertices, homogeneous G false K → Disjoint K A3 →
      homogeneous G false (insert p (insert q K)) ∧
        (insert p (insert q K)).card = K.card + 2 := by
    intro K hK hd
    have hpK : p ∉ K := fun h => disjoint_left.mp hd h hp
    have hqK : q ∉ K := fun h => disjoint_left.mp hd h hq
    refine ⟨add_two G hK hpq (fun u hu => hout p hp u (disjoint_left.mp hd hu))
      (fun u hu => hout q hq u (disjoint_left.mp hd hu)), ?_⟩
    rw [card_insert_of_notMem, card_insert_of_notMem hqK]
    intro h
    rcases mem_insert.mp h with h | h
    · exact hne h
    · exact hpK h
  have hx : ∀ u ∈ part G false univ x, ¬ G.Adj x u := fun u hu => ((in_part G).mp hu).2.2
  have hxA : x ∉ part G false univ x := self_out G false univ x
  have hB2s : insert y N2 ⊆ part G false univ x := insert_subset hyA hN2
  have hN2c : homogeneous G true (insert y N2) := by
    by_contra hn
    have hn' : ¬ homogeneous G true N2 := fun h => hn (homog_insert G h (fun u hu => hyN u hu))
    obtain ⟨u,hu,w,hw,huw,ha⟩ := not_clique G hn'
    have hI := pair_indep G ha
    have hIs : insert u ({w} : Vertices) ⊆ insert y N2 :=
      insert_subset (mem_insert_of_mem hu) (singleton_subset_iff.mpr (mem_insert_of_mem hw))
    obtain ⟨J,hJ,-,hJc,hJs⟩ := ext_step G hf cB3 hB3 (subset_univ _) hI (subset_univ _)
      (by rw [card_pair huw]; omega) (dNB.mono_left hIs)
    have hJA : Disjoint J A3 :=
      disjoint_of_subset_left hJs (disjoint_union_left.mpr ⟨dNA.mono_left hIs, dBA⟩)
    obtain ⟨hL, hLc⟩ := addpq J hJ hJA
    have hLs : insert p (insert q J) ⊆ part G false univ x :=
      insert_subset (hA3s hp) (insert_subset (hA3s hq)
        (hJs.trans (union_subset (hIs.trans hB2s) hB3s)))
    have hM := homog_insert G hL (fun u hu => hx u (hLs hu))
    have := hi _ (subset_univ _) hM
    rw [card_insert_of_notMem (fun h => hxA (hLs h)), hLc, hJc, card_pair huw] at this
    omega
  have hB1 : ¬ homogeneous G true (insert x (part G true univ x)) := fun h => by
    have := clique_le_five G hf h
    rw [cap_add, reg x] at this
    omega
  obtain ⟨I,hI,hIN,hIc⟩ := bad_pair G hB1
  have hdA : Disjoint I (part G false univ x) := (parts_disj G univ x).mono_left hIN
  have cB2 : (insert y N2).card = 5 := by rw [card_insert_of_notMem hy2, cN2]
  obtain ⟨J,hJ,-,hJc,hJs⟩ := ext_step G hf cB2 hN2c (subset_univ _) hI (subset_univ _)
    (by omega) (hdA.mono_right hB2s)
  obtain ⟨K,hK,-,hKc,hKs⟩ := ext_step G hf cB3 hB3 (subset_univ _) hJ (subset_univ _)
    (by omega) (disjoint_of_subset_left hJs (disjoint_union_left.mpr ⟨hdA.mono_right hB3s, dNB⟩))
  have hKA : Disjoint K A3 := disjoint_of_subset_left hKs (disjoint_union_left.mpr
    ⟨disjoint_of_subset_left hJs (disjoint_union_left.mpr ⟨hdA.mono_right hA3s, dNA⟩), dBA⟩)
  obtain ⟨hL, hLc⟩ := addpq K hK hKA
  have := hi _ (subset_univ _) hL
  omega
private lemma L3_15 (hf : sparse G) {S} (hi : bound G false S 3) (hn : S.card = 15)
    (ha : arcs G S S ≤ 72) :
    (∃ Q1 Q2 Q3 : Vertices, Q1 ∪ Q2 ∪ Q3 = S ∧ Disjoint Q1 Q2 ∧ Disjoint Q1 Q3 ∧
      Disjoint Q2 Q3 ∧ Q1.card = 5 ∧ Q2.card = 5 ∧ Q3.card = 5 ∧ homogeneous G true Q1 ∧
      homogeneous G true Q2 ∧ homogeneous G true Q3) ∨
    (∃ x ∈ S, (part G false S x).card = 10 ∧ bound G false (part G false S x) 2 ∧
      50 ≤ arcs G (part G false S x) (part G false S x) ∧ 70 ≤ arcs G S S ∧
      homogeneous G true (insert x (part G true S x)) ∧
      (insert x (part G true S x)).card = 5) := by
  obtain ⟨x,hx,-,hb,hsz,hdeg,hacc,hcap⟩ := desc G hf hi (card_pos.mp (by omega))
  generalize hd : (part G true S x).card = d at *
  have hd5 : d ≤ 4 := by rw [hn] at hdeg; omega
  have hL2 : d ≤ 3 → False := by
    intro h3
    refine L2big G hf hb (by omega) ?_
    have hc : (part G false S x).card = 14 - d := by omega
    rw [hc]
    interval_cases d <;> norm_num [capT] at hcap ⊢ <;> omega
  have h4 : d = 4 := by
    by_contra h
    exact hL2 (by omega)
  subst h4
  have hc : (part G false S x).card = 10 := by omega
  have hcap' : arcs G (part G true S x) (part G true S x) ≤ 12 := by
    norm_num [capT] at hcap; omega
  rcases L2ten G hf hb hc with ⟨Q1,Q2,hu,hdj,c1,c2,k1,k2⟩ | h50
  · left
    have h1 : Q1 ⊆ part G false S x := by rw [← hu]; exact subset_union_left
    have h2 : Q2 ⊆ part G false S x := by rw [← hu]; exact subset_union_right
    have hB := R2 G hf hi h1 h2 hdj c1 c2 k1 k2
    obtain ⟨hd', hu'⟩ := partition G S hx
    refine ⟨insert x (part G true S x), Q1, Q2, ?_, hd'.mono_right h1, hd'.mono_right h2, hdj,
      by rw [cap_add]; omega, c1, c2, hB, k1, k2⟩
    rw [union_assoc, hu, hu']
  · right
    refine ⟨x, hx, hc, hb, h50, by omega, ?_, by rw [cap_add]; omega⟩
    by_contra hnc
    obtain ⟨I,hI,hIN,hIc⟩ := bad_pair G hnc
    have hall := splits_at G hx
    have hsub : arcs G I (part G false S x) ≤ arcs G (part G true S x) (part G false S x) :=
      sum_le_sum_of_subset hIN
    obtain ⟨J,hJ,hJs,hJc⟩ := free_pair G hf hI ((parts_disj G S x).mono_left hIN) (by omega)
    have := hi J (hJs.trans (union_subset (hIN.trans (part_sub G _ _ _)) (part_sub G _ _ _))) hJ
    omega

private lemma L3_16 (hf : sparse G) {S} (hi : bound G false S 3) (hn : S.card = 16)
    (ha : arcs G S S ≤ 90) : False := by
  obtain ⟨x,hx,hm,hb,hsz,hdeg,hacc,hcap⟩ := desc G hf hi (card_pos.mp (by omega))
  generalize hd : (part G true S x).card = d at *
  have hd5 : d ≤ 5 := by rw [hn] at hdeg; omega
  have hL2 : d ≤ 3 → False := by
    intro h3
    refine L2big G hf hb (by omega) ?_
    have hc : (part G false S x).card = 15 - d := by omega
    rw [hc]
    interval_cases d <;> norm_num [capT] at hcap ⊢ <;> omega
  have h45 : d = 4 ∨ d = 5 := by
    by_contra h
    exact hL2 (by omega)
  rcases h45 with h4 | h5
  · subst h4
    exact Zlem G hf hb (by omega) (by norm_num [capT] at hcap; omega)
  · subst h5
    have hc : (part G false S x).card = 10 := by omega
    have hcap' : arcs G (part G true S x) (part G true S x) ≤ 12 := by
      norm_num [capT] at hcap; omega
    rcases L2ten G hf hb hc with ⟨Q1,Q2,hu,hdj,c1,c2,k1,k2⟩ | h50
    · have h1 : Q1 ⊆ part G false S x := by rw [← hu]; exact subset_union_left
      have h2 : Q2 ⊆ part G false S x := by rw [← hu]; exact subset_union_right
      have := clique_le_five G hf (R2 G hf hi h1 h2 hdj c1 c2 k1 k2)
      rw [cap_add] at this
      omega
    · exact tail G hf hx hd hm subset_rfl hc hb (by omega) (fun J hJ hJs =>
        hi J (hJs.trans (union_subset (part_sub G _ _ _) (part_sub G _ _ _))) hJ)

private lemma L4_21 (hf : sparse G) {S} (hi : bound G false S 4) (hn : S.card = 21)
    (ha : arcs G S S ≤ 110) : False := by
  obtain ⟨x,hx,hm,hb,hsz,hdeg,hacc,hcap⟩ := desc G hf hi (card_pos.mp (by omega))
  generalize hd : (part G true S x).card = d at *
  have hd5 : d ≤ 5 := by rw [hn] at hdeg; omega
  interval_cases d
  · exact level3 G hf hb (n := 20) (a := 110) (by omega)
      (by norm_num [capT] at hcap; omega) n3d (by omega)
  · exact level3 G hf hb (n := 19) (a := 108) (by omega)
      (by norm_num [capT] at hcap; omega) n3c (by omega)
  · exact level3 G hf hb (n := 18) (a := 104) (by omega)
      (by norm_num [capT] at hcap; omega) n3b (by omega)
  · exact level3 G hf hb (n := 17) (a := 98) (by omega)
      (by norm_num [capT] at hcap; omega) n3a (by omega)
  · exact L3_16 G hf hb (by omega) (by norm_num [capT] at hcap; omega)
  · have hA15 : (part G false S x).card = 15 := by omega
    have hA72 : arcs G (part G false S x) (part G false S x) ≤ 72 := by
      norm_num [capT] at hcap; omega
    rcases L3_15 G hf hb hA15 hA72 with
      ⟨Q1,Q2,Q3,hu,d12,d13,d23,c1,c2,c3,k1,k2,k3⟩ | ⟨y,hy,hc10,hb2,h50,h70,hBy,hBc⟩
    · have h1 : Q1 ⊆ part G false S x := by
        rw [← hu]; exact subset_union_left.trans subset_union_left
      have h2 : Q2 ⊆ part G false S x := by
        rw [← hu]; exact subset_union_right.trans subset_union_left
      have h3 : Q3 ⊆ part G false S x := by rw [← hu]; exact subset_union_right
      have := clique_le_five G hf (R3 G hf hi h1 h2 h3 d12 d13 d23 c1 c2 c3 k1 k2 k3)
      rw [cap_add] at this
      omega
    · refine tail G hf hx hd hm (part_sub G false _ y) hc10 hb2 (by omega) ?_
      intro J hJ hJs
      by_contra hJc
      obtain ⟨J4, hJ4s, hJ4c⟩ := exists_subset_card_eq (show 4 ≤ J.card by omega)
      have hJ4 := homog_mono G hJ hJ4s
      have hA2S := part_sub G false S x
      have hByA : insert y (part G true (part G false S x) y) ⊆ part G false S x :=
        insert_subset hy (part_sub G true _ y)
      have hJS : J ⊆ S := hJs.trans (union_subset (part_sub G true S x)
        ((part_sub G false _ y).trans hA2S))
      have hdis : Disjoint J (insert y (part G true (part G false S x) y)) := by
        refine disjoint_of_subset_left hJs (disjoint_union_left.mpr ⟨?_, ?_⟩)
        · exact (parts_disj G S x).mono_right hByA
        · exact (partition G _ hy).1.symm
      obtain ⟨K,hK,hKS,hKc,-⟩ := ext_step G hf hBc hBy (hByA.trans hA2S) hJ4
        (hJ4s.trans hJS) (by omega) (hdis.mono_left hJ4s)
      have := hi K hKS hK
      omega

private lemma regular_case (hf : sparse G) (hi : bound G false univ 5)
    (reg : ∀ z, (part G true univ z).card = 5) (x : V)
    (hA : (part G false univ x).card = 20)
    (ha : arcs G (part G false univ x) (part G false univ x) ≤ 92) : False := by
  have hb1 : bound G false (part G false univ x) 4 := bound_part G hi (mem_univ x)
  obtain ⟨y,hy,hm,hb,hsz,hdeg,hacc,hcap⟩ := desc G hf hb1 (card_pos.mp (by omega))
  generalize hd : (part G true (part G false univ x) y).card = d at *
  have hd5 : d ≤ 4 := by rw [hA] at hdeg; omega
  interval_cases d
  · exact level3 G hf hb (n := 19) (a := 92) (by omega)
      (by norm_num [capT] at hcap; omega) n3h (by omega)
  · exact level3 G hf hb (n := 18) (a := 90) (by omega)
      (by norm_num [capT] at hcap; omega) n3g (by omega)
  · exact level3 G hf hb (n := 17) (a := 86) (by omega)
      (by norm_num [capT] at hcap; omega) n3f (by omega)
  · exact level3 G hf hb (n := 16) (a := 80) (by omega)
      (by norm_num [capT] at hcap; omega) n3e (by omega)
  · have hA15 : (part G false (part G false univ x) y).card = 15 := by omega
    have hA72 : arcs G (part G false (part G false univ x) y)
        (part G false (part G false univ x) y) ≤ 72 := by
      norm_num [capT] at hcap; omega
    have hA2 := part_sub G false (part G false univ x) y
    rcases L3_15 G hf hb hA15 hA72 with
      ⟨Q1,Q2,Q3,hu,d12,d13,d23,c1,c2,c3,k1,k2,k3⟩ | ⟨z,hz,hc10,hb2,h50,h70,hBz,hBc⟩
    · have h1 : Q1 ⊆ part G false (part G false univ x) y := by
        rw [← hu]; exact subset_union_left.trans subset_union_left
      have h2 : Q2 ⊆ part G false (part G false univ x) y := by
        rw [← hu]; exact subset_union_right.trans subset_union_left
      have h3 : Q3 ⊆ part G false (part G false univ x) y := by
        rw [← hu]; exact subset_union_right
      have hB := R3 G hf hb1 h1 h2 h3 d12 d13 d23 c1 c2 c3 k1 k2 k3
      have hdB := (partition G _ hy).1
      exact reg_cov G hf hi reg (x := x) (insert_subset hy (part_sub G true _ y))
        (h1.trans hA2) (h2.trans hA2) (h3.trans hA2) (hdB.mono_right h1) (hdB.mono_right h2)
        (hdB.mono_right h3) d12 d13 d23 (by rw [cap_add]; omega) c1 c2 c3 hB k1 k2 k3
    · have dB := (partition G _ hy).1
      exact reg_w G hf hi reg hy (part_sub G true _ y) (fun u hu => ((in_part G).mp hu).2.2) hd
        (self_out G true _ y) (insert_subset (hA2 hz) ((part_sub G true _ z).trans hA2)) hBz hBc
        ((part_sub G false _ z).trans hA2) hc10 h50
        (dB.mono_right (insert_subset hz (part_sub G true _ z)))
        (dB.mono_right (part_sub G false _ z)) (partition G _ hz).1

private lemma graph_result (hf : sparse G) (hi : bound G false univ 5)
    (edges : arcs G univ univ ≤ 130) : False := by
  obtain ⟨x,hx,hm,hb,hsz,hdeg,hacc,hcap⟩ := desc G hf hi ⟨0, mem_univ _⟩
  have hcu : (univ : Vertices).card = 26 := by simp
  rw [hcu] at hsz hdeg
  by_cases hlow : (part G true univ x).card ≤ 4
  · generalize hd : (part G true univ x).card = d at *
    interval_cases d
    · exact level4 G hf hb (n := 25) (a := 130) (by omega)
        (by norm_num [capT] at hcap; omega) num25 (by omega)
    · exact level4 G hf hb (n := 24) (a := 128) (by omega)
        (by norm_num [capT] at hcap; omega) num24 (by omega)
    · exact level4 G hf hb (n := 23) (a := 124) (by omega)
        (by norm_num [capT] at hcap; omega) num23 (by omega)
    · exact level4 G hf hb (n := 22) (a := 118) (by omega)
        (by norm_num [capT] at hcap; omega) num22 (by omega)
    · exact L4_21 G hf hb (by omega) (by norm_num [capT] at hcap; omega)
  · have hmin (z : V) (_ : z ∈ univ) : 5 ≤ (part G true univ z).card := by
      have := hm z (mem_univ z)
      omega
    have reg (z : V) : (part G true univ z).card = 5 := by
      by_contra hn
      have hz := hmin z (mem_univ _)
      have h := sum_lt_sum hmin ⟨z, mem_univ _, (show 5 < (part G true univ z).card by omega)⟩
      change (∑ _ ∈ (univ : Vertices), 5) < arcs G univ univ at h
      simp only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul] at h
      omega
    have h5 := reg x
    rw [h5] at hsz hacc hcap
    exact regular_case G hf hi reg x (by omega) (by norm_num [capT] at hcap; omega)

private theorem mainLemma : OMA.R_Erdos617_erdos_617_R1.H2 := by
  intro adj hedges
  let G := fromBool adj
  by_contra hbad
  have avoid (S : Vertices) (hn : S.card = 6) :
      ¬ ((∀ x ∈ S, ∀ y ∈ S, x ≠ y → adj s(x,y) = false) ∨
       ((S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ adj s(p.1,p.2) = false)).card < 8) :=
    fun h => hbad ⟨S,hn,h⟩
  have hi : bound G false univ 5 := by
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
    have h₂ : 8 ≤ ((S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ adj s(p.1,p.2) = false)).card :=
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
end Graph617b

theorem OMA.solution : OMA.R_Erdos617_erdos_617_R1.H2 := Graph617b.mainLemma
