import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H1_R1_H2_R1_H2_R1_H2_R1

/-! For the five sparse weight-16 cases of Carter's order-ten plane search,
replace 95 labeled exterior incidence columns by an unordered packing of
partitions of the support. The canonical labels and the secants indexed by
uncovered pairs come from open-math-agents #2606, #3640, #4195, and #4185. -/

namespace E723Packing
open Finset

/-- Distinct exterior columns determine different blocks of lines.  Each block
partitions the support, and two blocks use the same line at most once. -/
theorem packing {P R : Type} [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
    (S : Finset P) (M : R → P → Bool) (rows : R → Finset P)
    (onS : ∀ l p, p ∈ S → (M l p = true ↔ p ∈ rows l))
    (unique : ∀ p ∈ S, ∀ q, p ≠ q → ∃! l, M l p = true ∧ M l q = true)
    (meet : ∀ l m : R, l ≠ m → ∃! p, M l p = true ∧ M m p = true)
    (linear : ∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l=m)
    (size : P → ℕ) (degree : ∀ p ∉ S, (univ.filter (fun l => M l p = true)).card = size p)
    (lower : ∀ p ∉ S, 2 ≤ size p) :
    ∃ F : Finset (Finset R),
      F.card = (univ \ S).card ∧
      (∀ t ∈ F, ∀ s ∈ S, ∃! l, l ∈ t ∧ s ∈ rows l) ∧
      (∀ t ∈ F, ∀ u ∈ F, t ≠ u → (t ∩ u).card ≤ 1) ∧
      (∀ l m, l ≠ m → Disjoint (rows l) (rows m) → ∃! t, t ∈ F ∧ l ∈ t ∧ m ∈ t) ∧
      ∀ n, (F.filter (fun t => t.card = n)).card =
        ((univ \ S).filter (fun p => size p = n)).card := by
  classical
  let col (p : P) := univ.filter (fun l => M l p = true)
  let outside := univ \ S
  have out {p : P} : p ∈ outside ↔ p ∉ S := by simp [outside]
  have hit (p : P) (l : R) : l ∈ col p ↔ M l p = true := by simp [col]
  have compat (p q : P) (ne : p ≠ q) : (col p ∩ col q).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro l hl m hm
    obtain ⟨lp,lq⟩ := mem_inter.mp hl
    obtain ⟨mp,mq⟩ := mem_inter.mp hm
    exact linear p q ne l m ((hit p l).mp lp) ((hit q l).mp lq)
      ((hit p m).mp mp) ((hit q m).mp mq)
  have inj : Set.InjOn col (outside : Set P) := by
    intro p hp q _ eq
    by_contra ne
    have small := compat p q ne
    rw [←eq,inter_self] at small
    have h := degree p (out.mp hp)
    change (col p).card = size p at h
    have := lower p (out.mp hp)
    omega
  refine ⟨outside.image col,card_image_of_injOn inj,?_,?_,?_,?_⟩
  · intro t ht s hs
    obtain ⟨p,hp,rfl⟩ := mem_image.mp ht
    obtain ⟨l,⟨ls,lp⟩,uniq⟩ := unique s hs p (fun eq => out.mp hp (eq ▸ hs))
    exact ⟨l,⟨(hit p l).mpr lp,(onS l s hs).mp ls⟩,fun m hm =>
      uniq m ⟨(onS m s hs).mpr hm.2,(hit p m).mp hm.1⟩⟩
  · intro t ht u hu ne
    obtain ⟨p,_,rfl⟩ := mem_image.mp ht
    obtain ⟨q,_,rfl⟩ := mem_image.mp hu
    exact compat p q (fun eq => ne (congrArg col eq))
  · intro l m ne dis
    obtain ⟨p,⟨lp,mp⟩,only⟩ := meet l m ne
    have ho : p ∈ outside := out.mpr (fun hp =>
      Finset.disjoint_left.mp dis ((onS l p hp).mp lp) ((onS m p hp).mp mp))
    refine ⟨col p,⟨mem_image_of_mem _ ho,(hit p l).mpr lp,(hit p m).mpr mp⟩,?_⟩
    rintro t ⟨ht,hl,hm⟩
    obtain ⟨q,_,rfl⟩ := mem_image.mp ht
    exact congrArg col (only q ⟨(hit q l).mp hl,(hit q m).mp hm⟩)
  · intro n
    rw [Finset.filter_image]
    rw [Finset.card_image_of_injOn (inj.mono (by
      intro p hp
      exact (mem_filter.mp hp).1))]
    congr 1
    ext p
    by_cases hp : p ∈ outside
    · have h := degree p (out.mp hp)
      change (col p).card = size p at h
      simp [hp,h,outside] at *
    · simp [hp,outside] at *

end E723Packing

/- Column sizes for the three canonical types of exterior points. -/
namespace E723Patterns

open Finset
open scoped Classical

theorem column_hist {E : Type*} [Fintype E] :
    let Q := {q : Fin 8 × Fin 8 // q.1 < q.2}
    let P := (Q ⊕ (Fin 8 × Fin 4)) ⊕ Fin 51
    ∀ (S : Finset P) (A : Fin 8 → P → Bool) (B : E → P → Bool),
      S.card = 16 →
      (∀ a (q : Q), A a (.inl (.inl q)) = decide (a = q.val.1 ∨ a = q.val.2)) →
      (∀ a b i, A a (.inl (.inr (b,i))) = decide (a = b)) →
      (∀ a i, A a (.inr i) = false) →
      let c (p : P) := (univ.filter (fun a => A a p = true)).card
      (∀ p ∈ S, c p = 2) →
      (∀ p ∉ S, 2*c p + (univ.filter (fun b => B b p = true)).card = 8) →
      (∀ p ∉ S, (univ.filter (fun l => Sum.elim A B l p = true)).card = 8 - c p) ∧
      (∀ p ∉ S, 2 ≤ 8 - c p) ∧
      ((univ \ S).filter (fun p => 8 - c p = 6)).card = 12 ∧
      ((univ \ S).filter (fun p => 8 - c p = 7)).card = 32 ∧
      ((univ \ S).filter (fun p => 8 - c p = 8)).card = 51 := by
  intro Q P S A B size paired single hidden c inside outside
  classical
  have degrees (p : P) : (univ.filter (fun l => Sum.elim A B l p = true)).card =
      c p + (univ.filter (fun b => B b p = true)).card := by
    rw [← Finset.card_disjSum]
    congr 1
    ext l
    cases l <;> simp
  let tag : P → ℕ := Sum.elim (Sum.elim (fun _ => 6) (fun _ => 7)) (fun _ => 8)
  have code (p : P) : 8-c p = tag p := by
    rcases p with ((q | ⟨b,i⟩) | j)
    · have s : univ.filter (fun a => A a (.inl (.inl q)) = true) = {q.val.1,q.val.2} := by
        ext a
        simp [paired]
      change 8-(univ.filter _).card = 6
      rw [s]
      simp [q.property.ne]
    · have s : univ.filter (fun a => A a (.inl (.inr (b,i))) = true) = {b} := by
        ext a
        simp [single]
      change 8-(univ.filter _).card = 7
      rw [s]
      rfl
    · change 8-(univ.filter _).card = 8
      simp [hidden]
  have total : (univ.filter (fun p : P => tag p = 6)).card = 28 ∧
      (univ.filter (fun p : P => tag p = 7)).card = 32 ∧
      (univ.filter (fun p : P => tag p = 8)).card = 51 := by
    dsimp only [tag,P,Q]
    decide +kernel
  have selected (p : P) (hp : p ∈ S) : tag p = 6 := by rw [← code,inside p hp]
  have sub : S ⊆ univ.filter (fun p : P => tag p = 6) := fun p hp => mem_filter.mpr ⟨mem_univ _,selected p hp⟩
  have erase6 : (univ \ S).filter (fun p => 8-c p = 6) = (univ.filter (fun p => tag p = 6)) \ S := by
    ext p
    simp [code,and_comm]
  have other (n : ℕ) (hn : n ≠ 6) :
      (univ \ S).filter (fun p => 8 - c p = n) = univ.filter (fun p : P => tag p = n) := by
    ext p
    simp only [mem_filter,mem_sdiff,mem_univ,true_and,code,and_iff_right_iff_imp]
    intro eq hp
    exact hn (eq.symm.trans (selected p hp))
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro p hp
    rw [degrees]
    have := outside p hp
    omega
  · intro p hp
    have := outside p hp
    omega
  · rw [erase6,card_sdiff_of_subset sub,size,total.1]
  · rw [other 7 (by decide),total.2.1]
  · rw [other 8 (by decide),total.2.2]

end E723Patterns

/- Recover the weight-sixteen support from the parent’s exact twenty-eight-bit word. -/

namespace E723Support

open Finset
open scoped Classical

-- The two bit lemmas adapt @avivorly's bit-mask proof in OMA PR #2606.
private lemma foldr_or_testBit (words : List Nat) (i : Nat) :
    (words.foldr Nat.lor 0).testBit i = true ↔ ∃ n ∈ words, n.testBit i = true := by
  induction words with
  | nil => simp
  | cons word words ih =>
      change (word ||| words.foldr Nat.lor 0).testBit i = true ↔ _
      simp only [Nat.testBit_lor, Bool.or_eq_true, ih, List.mem_cons]
      constructor
      · intro h
        rcases h with bit | ⟨n, hn, bit⟩
        · exact ⟨word, Or.inl rfl, bit⟩
        · exact ⟨n, Or.inr hn, bit⟩
      · rintro ⟨n, h, bit⟩
        rcases h with rfl | mem
        · exact Or.inl bit
        · exact Or.inr ⟨n, mem, bit⟩

private theorem mask_bits {α : Type*} (xs : List α) (chosen : α → Bool) (i : Nat) :
    ((xs.zipIdx.map fun (x,j) => if chosen x then 2^j else 0).foldr Nat.lor 0).testBit i = true ↔
      ∃ x, xs[i]? = some x ∧ chosen x = true := by
  rw [foldr_or_testBit]
  constructor
  · rintro ⟨n, member, set⟩
    obtain ⟨⟨x,j⟩, hxj, rfl⟩ := List.mem_map.mp member
    cases hx : chosen x with
    | false => simp [hx] at set
    | true =>
      have ji : j = i := by simpa [hx, Nat.testBit_two_pow] using set
      subst j
      exact ⟨x, List.mk_mem_zipIdx_iff_getElem?.mp hxj, hx⟩
  · rintro ⟨x, hx, chosen_x⟩
    refine ⟨2^i, ?_, Nat.testBit_two_pow_self⟩
    apply List.mem_map.mpr
    exact ⟨(x,i), List.mk_mem_zipIdx_iff_getElem?.mpr hx, by simp [chosen_x]⟩

theorem reconstruct :
    let Q := {q : Fin 8 × Fin 8 // q.1 < q.2}
    let P := (Q ⊕ (Fin 8 × Fin 4)) ⊕ Fin 51
    ∀ (S : Finset P) (A : Fin 8 → P → Bool),
    (∀ a (q : Q), A a (.inl (.inl q)) = decide (a = q.val.1 ∨ a = q.val.2)) →
    (∀ a b i, A a (.inl (.inr (b,i))) = decide (a = b)) →
    (∀ a i, A a (.inr i) = false) →
    (∀ p ∈ S, (Finset.univ.filter fun a => A a p = true).card = 2) →
    let G (a b : Fin 8) := decide (b ≠ a ∧ ∃ p ∉ S, A a p = true ∧ A b p = true)
    let pairs : List (Fin 8 × Fin 8) := [(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (2,3), (2,4), (2,5), (2,6), (2,7), (3,4), (3,5), (3,6), (3,7), (4,5), (4,6), (4,7), (5,6), (5,7), (6,7)]
    let word := (pairs.zipIdx.map fun ((a,b),i) => if G a b then 2^i else 0).foldr Nat.lor 0
    let pos (q : Q) := q.val.1.val*(15-q.val.1.val)/2 + q.val.2.val - q.val.1.val - 1
    (∀ q : Q, (.inl (.inl q) : P) ∈ S ↔ word.testBit (pos q) = false) ∧
    S = ((univ : Finset Q).filter (fun q => word.testBit (pos q) = false)).image
      (fun q : Q => (Sum.inl (Sum.inl q) : P)) ∧
    A = (fun a => Sum.elim (Sum.elim (fun q : Q => decide (a = q.val.1 ∨ a = q.val.2))
      (fun z : Fin 8 × Fin 4 => decide (a = z.1))) (fun _ : Fin 51 => false)) := by
  intro Q P S A paired priv hidden inside G pairs word pos
  let A0 (a : Fin 8) : P → Bool := Sum.elim (Sum.elim
    (fun q : Q => decide (a = q.val.1 ∨ a = q.val.2))
    (fun z : Fin 8 × Fin 4 => decide (a = z.1))) (fun _ : Fin 51 => false)
  have ae : A = A0 := by
    funext a p
    rcases p with (q | ⟨b,j⟩) | j
    · exact paired a q
    · exact priv a b j
    · exact hidden a j
  have pos_spec : ∀ q : Q, pairs[pos q]? = some q.val := by
    dsimp +zetaDelta only [Q, pairs, pos]
    decide +kernel
  have bit (q : Q) : word.testBit (pos q) = true ↔ G q.val.1 q.val.2 = true := by
    have h := mask_bits pairs (fun z => G z.1 z.2) (pos q)
    rw [pos_spec q] at h
    simpa using h
  have unique : ∀ (q : Q) (x : P), A0 q.val.1 x = true ∧ A0 q.val.2 x = true ↔
      x = (.inl (.inl q) : P) := by
    dsimp +zetaDelta only [P, Q, A0]
    decide +kernel
  have outside (q : Q) : G q.val.1 q.val.2 = true ↔ (Sum.inl (Sum.inl q) : P) ∉ S := by
    change decide _ = true ↔ _
    rw [decide_eq_true_eq]
    constructor
    · rintro ⟨_, x, nx, hits⟩
      rw [ae] at hits
      simpa only [(unique q x).mp hits] using nx
    · intro nx
      refine ⟨q.property.ne.symm, _, nx, ?_⟩
      rw [ae]
      exact (unique q _).mpr rfl
  have support (q : Q) : (.inl (.inl q) : P) ∈ S ↔ word.testBit (pos q) = false := by
    have t := (bit q).trans (outside q)
    constructor
    · intro hx
      cases h : word.testBit (pos q) with
      | false => rfl
      | true => exact ((t.mp h) hx).elim
    · intro h
      by_contra nx
      have := t.mpr nx
      simp [h] at this
  refine ⟨support, ?_, ae⟩
  ext p
  constructor
  · intro hp
    have hex : ∃ q : Q, p = (.inl (.inl q) : P) := by
      have hc := inside p hp
      rcases p with (q | ⟨b,j⟩) | j
      · exact ⟨q, rfl⟩
      · have one : (univ.filter fun a : Fin 8 => a = b) = {b} := by ext x; simp
        simp [priv, one] at hc
      · simp [hidden] at hc
    obtain ⟨q, rfl⟩ := hex
    exact mem_image.mpr ⟨q, mem_filter.mpr ⟨mem_univ _, (support q).mp hp⟩, rfl⟩
  · intro hp
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    exact (support q).mpr (mem_filter.mp hq).2

end E723Support

/- Matchings on the selected points induced by each outside point. -/
namespace E723Patterns

open Finset
open scoped Classical

theorem point_matching {P H : Type*} [DecidableEq P] [Fintype H]
    (S : Finset P) (C : Finset (Finset P)) (A : H → P → Bool) (B : ↥C → P → Bool)
    (sub : ∀ b : ↥C, b.val ⊆ S)
    (sec : ∀ b p, p ∈ S → (B b p = true ↔ p ∈ b.val))
    (unique : ∀ s ∈ S, ∀ x, s ≠ x → ∃! l, Sum.elim A B l s = true ∧ Sum.elim A B l x = true)
    (x : P) (outside : x ∉ S) :
    let T := univ.filter (fun b : ↥C => B b x = true)
    let R := S.filter (fun s => ∀ a, A a x = true → A a s = false)
    (∀ b ∈ T, b.val ⊆ R) ∧ (∀ s ∈ R, ∃! b : ↥C, b ∈ T ∧ s ∈ b.val) := by
  classical
  dsimp only
  constructor
  · intro b hb s hs
    have hsin := sub b hs
    have hne : s ≠ x := fun eq => outside (eq ▸ hsin)
    have bx := (mem_filter.mp hb).2
    have bs := (sec b s hsin).mpr hs
    refine mem_filter.mpr ⟨hsin,?_⟩
    intro a ax
    cases e : A a s with
    | false => rfl
    | true =>
      have impossible : (Sum.inl a : H ⊕ ↥C) = Sum.inr b :=
        (unique s hsin x hne).unique (show Sum.elim A B (Sum.inl a) s = true ∧ _ from ⟨e,ax⟩)
          (show Sum.elim A B (Sum.inr b) s = true ∧ _ from ⟨bs,bx⟩)
      contradiction
  · intro s hs
    obtain ⟨hsin,free⟩ := mem_filter.mp hs
    have hne : s ≠ x := fun eq => outside (eq ▸ hsin)
    obtain ⟨l,hl,unq⟩ := unique s hsin x hne
    cases l with
    | inl a =>
      obtain ⟨ha,hx⟩ := hl
      have no : false = true := (free a hx).symm.trans ha
      contradiction
    | inr b =>
      refine ⟨b,⟨mem_filter.mpr ⟨mem_univ _,hl.2⟩,(sec b s hsin).mp hl.1⟩,?_⟩
      intro d hd
      exact Sum.inr.inj (unq (Sum.inr d) ⟨(sec d s hsin).mpr hd.2,(mem_filter.mp hd.1).2⟩)

end E723Patterns

/- A marked intersection of two heavy lines determines a four-pair matching
on the eight selected edges avoiding both lines. The alternatives below use the
ascending lexicographic order of those eight edges. -/

namespace E723Marked
open Finset

lemma checked (word : Nat) (a b : Fin 8) (solutions : List (Finset (Fin 8 × Fin 8))) (M : Finset (Fin 8 × Fin 8)) :
    let pairs : List (Fin 8 × Fin 8) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]
    let edges := (pairs.zipIdx.filter (fun z =>
      !(word.testBit z.2) && z.1.1 != a && z.1.1 != b && z.1.2 != a && z.1.2 != b)).map Prod.fst
    let edge (i : Fin 8) := edges.getD i.val (0,0)
    let compatible (q : Fin 8 × Fin 8) := q.1 < q.2 ∧
      (edge q.1).1 ≠ (edge q.2).1 ∧ (edge q.1).1 ≠ (edge q.2).2 ∧
      (edge q.1).2 ≠ (edge q.2).1 ∧ (edge q.1).2 ≠ (edge q.2).2
    let allowed := pairs.filter fun q => decide (compatible q)
    ((allowed.sublistsLen 4).all (fun l =>
      !((List.finRange 8).all fun i => l.any fun q => q.1==i || q.2==i) ||
      decide (l.toFinset ∈ solutions))) = true →
    M.card = 4 → (∀ q ∈ M, compatible q) →
    (∀ i : Fin 8, ∃ q ∈ M, q.1 = i ∨ q.2 = i) → M ∈ solutions := by
  intro pairs edges edge compatible allowed h card comp cover
  have sorted : ∀ q : Fin 8 × Fin 8, q.1 < q.2 → q ∈ pairs := by decide +kernel
  have pn : pairs.Nodup := by decide +kernel
  let chosen := allowed.filter fun q => decide (q ∈ M)
  have eq : chosen.toFinset = M := by
    ext q
    simp only [chosen,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
    constructor
    · exact fun hq => hq.2
    · intro hq
      exact ⟨List.mem_filter.mpr ⟨sorted q (comp q hq).1,decide_eq_true (comp q hq)⟩,hq⟩
  have sub : List.Sublist chosen allowed := List.filter_sublist
  have nd : chosen.Nodup := (pn.filter _).filter _
  have size : chosen.length=4 := by rw [←List.toFinset_card_of_nodup nd,eq,card]
  have hcheck := List.all_eq_true.mp h chosen (List.mem_sublistsLen.mpr ⟨sub,size⟩)
  have total : ((List.finRange 8).all fun i => chosen.any fun q => q.1==i || q.2==i)=true := by
    apply List.all_eq_true.mpr
    intro i _
    obtain ⟨q,hq,he⟩ := cover i
    apply List.any_eq_true.mpr
    have member : q ∈ chosen := List.mem_toFinset.mp (eq.symm ▸ hq)
    exact ⟨q,member,by rcases he with h|h <;> simp [h]⟩
  simpa only [total,Bool.not_true,Bool.false_or,eq,decide_eq_true_eq] using hcheck

set_option maxRecDepth 16384 in
set_option maxHeartbeats 10000000 in
theorem mark_1da9807 (M : Finset (Fin 8 × Fin 8)) :
    let word : Nat := 0x1da9807
    let a : Fin 8 := 0
    let b : Fin 8 := 1
    let pairs : List (Fin 8 × Fin 8) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]
    let edges := (pairs.zipIdx.filter (fun z =>
      !(word.testBit z.2) && z.1.1 != a && z.1.1 != b && z.1.2 != a && z.1.2 != b)).map Prod.fst
    let edge (i : Fin 8) := edges.getD i.val (0,0)
    let compatible (q : Fin 8 × Fin 8) := q.1 < q.2 ∧
      (edge q.1).1 ≠ (edge q.2).1 ∧ (edge q.1).1 ≠ (edge q.2).2 ∧
      (edge q.1).2 ≠ (edge q.2).1 ∧ (edge q.1).2 ≠ (edge q.2).2
    let solutions : List (Finset (Fin 8 × Fin 8)) := [
      {(0,5),(1,4),(2,6),(3,7)},
      {(0,5),(1,6),(2,4),(3,7)},
      {(0,5),(1,7),(2,4),(3,6)},
      {(0,6),(1,5),(2,4),(3,7)},
      {(0,6),(1,7),(2,3),(4,5)},
      {(0,6),(1,7),(2,4),(3,5)},
      {(0,7),(1,4),(2,6),(3,5)},
      {(0,7),(1,5),(2,4),(3,6)},
      {(0,7),(1,6),(2,3),(4,5)},
      {(0,7),(1,6),(2,4),(3,5)}]
    M.card = 4 → (∀ q ∈ M, compatible q) →
    (∀ i : Fin 8, ∃ q ∈ M, q.1 = i ∨ q.2 = i) → M ∈ solutions := by
  intro word a b pairs edges edge compatible solutions
  apply checked word a b solutions M
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 10000000 in
theorem mark_2e69807 (M : Finset (Fin 8 × Fin 8)) :
    let word : Nat := 0x2e69807
    let a : Fin 8 := 4
    let b : Fin 8 := 5
    let pairs : List (Fin 8 × Fin 8) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]
    let edges := (pairs.zipIdx.filter (fun z =>
      !(word.testBit z.2) && z.1.1 != a && z.1.1 != b && z.1.2 != a && z.1.2 != b)).map Prod.fst
    let edge (i : Fin 8) := edges.getD i.val (0,0)
    let compatible (q : Fin 8 × Fin 8) := q.1 < q.2 ∧
      (edge q.1).1 ≠ (edge q.2).1 ∧ (edge q.1).1 ≠ (edge q.2).2 ∧
      (edge q.1).2 ≠ (edge q.2).1 ∧ (edge q.1).2 ≠ (edge q.2).2
    let solutions : List (Finset (Fin 8 × Fin 8)) := [
      {(0,2),(1,6),(3,5),(4,7)},
      {(0,3),(1,5),(2,6),(4,7)},
      {(0,4),(1,5),(2,6),(3,7)},
      {(0,4),(1,6),(2,7),(3,5)}]
    M.card = 4 → (∀ q ∈ M, compatible q) →
    (∀ i : Fin 8, ∃ q ∈ M, q.1 = i ∨ q.2 = i) → M ∈ solutions := by
  intro word a b pairs edges edge compatible solutions
  apply checked word a b solutions M
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 10000000 in
theorem mark_3569807 (M : Finset (Fin 8 × Fin 8)) :
    let word : Nat := 0x3569807
    let a : Fin 8 := 0
    let b : Fin 8 := 2
    let pairs : List (Fin 8 × Fin 8) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]
    let edges := (pairs.zipIdx.filter (fun z =>
      !(word.testBit z.2) && z.1.1 != a && z.1.1 != b && z.1.2 != a && z.1.2 != b)).map Prod.fst
    let edge (i : Fin 8) := edges.getD i.val (0,0)
    let compatible (q : Fin 8 × Fin 8) := q.1 < q.2 ∧
      (edge q.1).1 ≠ (edge q.2).1 ∧ (edge q.1).1 ≠ (edge q.2).2 ∧
      (edge q.1).2 ≠ (edge q.2).1 ∧ (edge q.1).2 ≠ (edge q.2).2
    let solutions : List (Finset (Fin 8 × Fin 8)) := [
      {(0,5),(1,6),(2,4),(3,7)},
      {(0,6),(1,3),(2,7),(4,5)},
      {(0,6),(1,4),(2,5),(3,7)},
      {(0,6),(1,4),(2,7),(3,5)},
      {(0,6),(1,7),(2,4),(3,5)},
      {(0,7),(1,3),(2,4),(5,6)},
      {(0,7),(1,6),(2,4),(3,5)}]
    M.card = 4 → (∀ q ∈ M, compatible q) →
    (∀ i : Fin 8, ∃ q ∈ M, q.1 = i ∨ q.2 = i) → M ∈ solutions := by
  intro word a b pairs edges edge compatible solutions
  apply checked word a b solutions M
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 10000000 in
theorem mark_35a5807 (M : Finset (Fin 8 × Fin 8)) :
    let word : Nat := 0x35a5807
    let a : Fin 8 := 2
    let b : Fin 8 := 4
    let pairs : List (Fin 8 × Fin 8) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]
    let edges := (pairs.zipIdx.filter (fun z =>
      !(word.testBit z.2) && z.1.1 != a && z.1.1 != b && z.1.2 != a && z.1.2 != b)).map Prod.fst
    let edge (i : Fin 8) := edges.getD i.val (0,0)
    let compatible (q : Fin 8 × Fin 8) := q.1 < q.2 ∧
      (edge q.1).1 ≠ (edge q.2).1 ∧ (edge q.1).1 ≠ (edge q.2).2 ∧
      (edge q.1).2 ≠ (edge q.2).1 ∧ (edge q.1).2 ≠ (edge q.2).2
    let solutions : List (Finset (Fin 8 × Fin 8)) := [
      {(0,5),(1,6),(2,3),(4,7)},
      {(0,5),(1,6),(2,4),(3,7)},
      {(0,7),(1,5),(2,4),(3,6)},
      {(0,7),(1,6),(2,3),(4,5)}]
    M.card = 4 → (∀ q ∈ M, compatible q) →
    (∀ i : Fin 8, ∃ q ∈ M, q.1 = i ∨ q.2 = i) → M ∈ solutions := by
  intro word a b pairs edges edge compatible solutions
  apply checked word a b solutions M
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 10000000 in
theorem mark_fc02187 (M : Finset (Fin 8 × Fin 8)) :
    let word : Nat := 0xfc02187
    let a : Fin 8 := 0
    let b : Fin 8 := 1
    let pairs : List (Fin 8 × Fin 8) := [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,3),(2,4),(2,5),(2,6),(2,7),(3,4),(3,5),(3,6),(3,7),(4,5),(4,6),(4,7),(5,6),(5,7),(6,7)]
    let edges := (pairs.zipIdx.filter (fun z =>
      !(word.testBit z.2) && z.1.1 != a && z.1.1 != b && z.1.2 != a && z.1.2 != b)).map Prod.fst
    let edge (i : Fin 8) := edges.getD i.val (0,0)
    let compatible (q : Fin 8 × Fin 8) := q.1 < q.2 ∧
      (edge q.1).1 ≠ (edge q.2).1 ∧ (edge q.1).1 ≠ (edge q.2).2 ∧
      (edge q.1).2 ≠ (edge q.2).1 ∧ (edge q.1).2 ≠ (edge q.2).2
    let solutions : List (Finset (Fin 8 × Fin 8)) := [
      {(0,5),(1,4),(2,7),(3,6)},
      {(0,5),(1,6),(2,7),(3,4)},
      {(0,5),(1,7),(2,4),(3,6)},
      {(0,6),(1,4),(2,7),(3,5)},
      {(0,6),(1,7),(2,4),(3,5)},
      {(0,6),(1,7),(2,5),(3,4)},
      {(0,7),(1,4),(2,5),(3,6)},
      {(0,7),(1,6),(2,4),(3,5)},
      {(0,7),(1,6),(2,5),(3,4)}]
    M.card = 4 → (∀ q ∈ M, compatible q) →
    (∀ i : Fin 8, ∃ q ∈ M, q.1 = i ∨ q.2 = i) → M ∈ solutions := by
  intro word a b pairs edges edge compatible solutions
  apply checked word a b solutions M
  decide +kernel

end E723Marked

/- Counts for the support traces of heavy lines and secants. -/
namespace E723Patterns
open Finset

set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem trace_census (w : ℕ) (hw : w ∈ ([0x1da9807,0x2e69807,0x3569807,0x35a5807,0xfc02187] : List ℕ)) :
    let Q := {e : Fin 8 × Fin 8 // e.1 < e.2}
    let P := (Q ⊕ (Fin 8 × Fin 4)) ⊕ Fin 51
    let S := ((univ : Finset Q).filter (fun e => w.testBit (e.1.1.val*(15-e.1.1.val)/2+e.1.2.val-e.1.1.val-1) = false)).image
      (fun e : Q => (Sum.inl (Sum.inl e) : P))
    let A : Fin 8 → P → Bool := fun a => Sum.elim (Sum.elim
      (fun e : Q => decide (a = e.1.1 ∨ a = e.1.2))
      (fun t : Fin 8 × Fin 4 => decide (a = t.1))) (fun _ => false)
    let star (a : Fin 8) := S.filter (fun p => A a p = true)
    let C := S.powersetCard 2 \ (univ : Finset (Fin 8)).biUnion (fun a => (star a).powersetCard 2)
    let heavy := (univ : Finset (Fin 8)).image star
    let lines := heavy ∪ C
    let ordered := ∑ l ∈ lines, ((lines.erase l).filter fun m => Disjoint l m).card
    heavy.card = 8 ∧ C.card = 72 ∧ lines.card = 80 ∧
      80*79/2 - ordered/2 = 880 ∧ ordered/2 = 2280 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

end E723Patterns

namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H1_R1_H2_R1_H2_R1_H2_R1_H2_R1

open Finset

open scoped Classical

/-- The four connected cubic graph representatives. -/
def H1 : Prop :=
  ∀ w ∈ ([0x1da9807,0x2e69807,0x3569807,0x35a5807] : List ℕ),
    let Q := {e : Fin 8 × Fin 8 // e.1 < e.2}
    let P := (Q ⊕ (Fin 8 × Fin 4)) ⊕ Fin 51
    let S := ((univ : Finset Q).filter (fun e => w.testBit (e.1.1.val*(15-e.1.1.val)/2+e.1.2.val-e.1.1.val-1) = false)).image
      (fun e : Q => (Sum.inl (Sum.inl e) : P))
    let A : Fin 8 → P → Bool := fun a => Sum.elim (Sum.elim
      (fun e : Q => decide (a = e.1.1 ∨ a = e.1.2))
      (fun t : Fin 8 × Fin 4 => decide (a = t.1))) (fun _ => false)
    let star (a : Fin 8) := S.filter (fun p => A a p = true)
    let C := S.powersetCard 2 \ (univ : Finset (Fin 8)).biUnion (fun a => (star a).powersetCard 2)
    let row : Fin 8 ⊕ ↥C → Finset P := Sum.elim star (fun b => b.1)
    ¬ ∃ F : Finset (Finset (Fin 8 ⊕ ↥C)), F.card = 95 ∧
      (∀ t ∈ F, ∀ s ∈ S, ∃! l, l ∈ t ∧ s ∈ row l) ∧
      (∀ t ∈ F, ∀ u ∈ F, t ≠ u → (t ∩ u).card ≤ 1) ∧
      (∀ l m, l ≠ m → Disjoint (row l) (row m) → ∃! t, t ∈ F ∧ l ∈ t ∧ m ∈ t) ∧
      (F.filter (fun t => t.card = 6)).card = 12 ∧
      (F.filter (fun t => t.card = 7)).card = 32 ∧
      (F.filter (fun t => t.card = 8)).card = 51

/-- The two disjoint tetrahedra. -/
def H2 : Prop :=
  ∀ w ∈ ([0xfc02187] : List ℕ),
    let Q := {e : Fin 8 × Fin 8 // e.1 < e.2}
    let P := (Q ⊕ (Fin 8 × Fin 4)) ⊕ Fin 51
    let S := ((univ : Finset Q).filter (fun e => w.testBit (e.1.1.val*(15-e.1.1.val)/2+e.1.2.val-e.1.1.val-1) = false)).image
      (fun e : Q => (Sum.inl (Sum.inl e) : P))
    let A : Fin 8 → P → Bool := fun a => Sum.elim (Sum.elim
      (fun e : Q => decide (a = e.1.1 ∨ a = e.1.2))
      (fun t : Fin 8 × Fin 4 => decide (a = t.1))) (fun _ => false)
    let star (a : Fin 8) := S.filter (fun p => A a p = true)
    let C := S.powersetCard 2 \ (univ : Finset (Fin 8)).biUnion (fun a => (star a).powersetCard 2)
    let row : Fin 8 ⊕ ↥C → Finset P := Sum.elim star (fun b => b.1)
    ¬ ∃ F : Finset (Finset (Fin 8 ⊕ ↥C)), F.card = 95 ∧
      (∀ t ∈ F, ∀ s ∈ S, ∃! l, l ∈ t ∧ s ∈ row l) ∧
      (∀ t ∈ F, ∀ u ∈ F, t ≠ u → (t ∩ u).card ≤ 1) ∧
      (∀ l m, l ≠ m → Disjoint (row l) (row m) → ∃! t, t ∈ F ∧ l ∈ t ∧ m ∈ t) ∧
      (F.filter (fun t => t.card = 6)).card = 12 ∧
      (F.filter (fun t => t.card = 7)).card = 32 ∧
      (F.filter (fun t => t.card = 8)).card = 51

theorem main : H1 → H2 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H1_R1_H2_R1_H2_R1_H2_R1.H2 := by
  classical
  intro hc hd
  let Q := {e : Fin 8 × Fin 8 // e.1 < e.2}
  let P := (Q ⊕ (Fin 8 × Fin 4)) ⊕ Fin 51
  let mkSupport (w : ℕ) : Finset P := ((univ : Finset Q).filter (fun e => w.testBit (e.1.1.val*(15-e.1.1.val)/2+e.1.2.val-e.1.1.val-1) = false)).image
      (fun e : Q => (Sum.inl (Sum.inl e) : P))
  let canon : Fin 8 → P → Bool := fun a => Sum.elim (Sum.elim
      (fun e : Q => decide (a = e.1.1 ∨ a = e.1.2))
      (fun t : Fin 8 × Fin 4 => decide (a = t.1))) (fun _ => false)
  let packingExists (S : Finset P) (A : Fin 8 → P → Bool) : Prop :=
    let star (a : Fin 8) := S.filter (fun p => A a p = true)
    let C := S.powersetCard 2 \ (univ : Finset (Fin 8)).biUnion (fun a => (star a).powersetCard 2)
    let row : Fin 8 ⊕ ↥C → Finset P := Sum.elim star (fun b => b.1)
    ∃ F : Finset (Finset (Fin 8 ⊕ ↥C)), F.card = 95 ∧
      (∀ t ∈ F, ∀ s ∈ S, ∃! l, l ∈ t ∧ s ∈ row l) ∧
      (∀ t ∈ F, ∀ u ∈ F, t ≠ u → (t ∩ u).card ≤ 1) ∧
      (∀ l m, l ≠ m → Disjoint (row l) (row m) → ∃! t, t ∈ F ∧ l ∈ t ∧ m ∈ t) ∧
      (F.filter (fun t => t.card = 6)).card = 12 ∧
      (F.filter (fun t => t.card = 7)).card = 32 ∧
      (F.filter (fun t => t.card = 8)).card = 51
  rintro ⟨S,A,sCard,heavy,paired,private_,hidden,B,lines,sec,inside,outside,linePair,colPair,codePair,seen⟩
  let star (a : Fin 8) := S.filter (fun p => A a p = true)
  let C := S.powersetCard 2 \ (univ : Finset (Fin 8)).biUnion (fun a => (star a).powersetCard 2)
  let M := Sum.elim A B
  let row : Fin 8 ⊕ ↥C → Finset P := Sum.elim star (fun b => b.1)
  let size (p : P) := 8 - (univ.filter fun a => A a p = true).card
  have onS (l : Fin 8 ⊕ ↥C) (p : P) (hp : p ∈ S) : M l p = true ↔ p ∈ row l := by
    cases l with
    | inl a =>
      change A a p = true ↔ p ∈ S.filter _
      simp [hp]
    | inr b => exact sec b p hp
  obtain ⟨degree,lower,n6,n7,n8⟩ := E723Patterns.column_hist S A B sCard paired private_ hidden (fun p hp => (inside p hp).1) outside
  obtain ⟨F,order,partition,compat,cover,hist⟩ :=
    E723Packing.packing S M row onS codePair linePair colPair size degree lower
  have count : (univ \ S).card = 95 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S),sCard]
    change Fintype.card P - 16 = 95
    decide +kernel
  have packed : packingExists S A :=
    ⟨F,order.trans count,partition,compat,cover,(hist 6).trans n6,(hist 7).trans n7,(hist 8).trans n8⟩
  let G (a b : Fin 8) := decide (b ≠ a ∧ ∃ p ∉ S, A a p = true ∧ A b p = true)
  let pairs : List (Fin 8 × Fin 8) := [(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (2,3), (2,4), (2,5), (2,6), (2,7), (3,4), (3,5), (3,6), (3,7), (4,5), (4,6), (4,7), (5,6), (5,7), (6,7)]
  let w := (pairs.zipIdx.map fun ((a,b),i) => if G a b then 2^i else 0).foldr Nat.lor 0
  change w ∈ ([0x1da9807,0x2e69807,0x3569807,0x35a5807,0xfc02187] : List ℕ) at seen
  obtain ⟨_,hS,hA⟩ := E723Support.reconstruct S A paired private_ hidden (fun p hp => (inside p hp).1)
  change S = mkSupport w at hS
  change A = canon at hA
  have impossible : ¬ packingExists (mkSupport w) canon := by
    by_cases tetra : w = 0xfc02187
    · exact hd w (by simp [tetra])
    · apply hc w
      simpa only [List.mem_cons,List.not_mem_nil,or_false,tetra] using seen
  exact impossible (hS ▸ hA ▸ packed)


end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H1_R1_H2_R1_H2_R1_H2_R1_H2_R1
