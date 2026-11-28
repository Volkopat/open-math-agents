import OMAReductions.R_BranchingVAS_reachability_decidable_R1
import Mathlib

namespace OMA.BVASH1

open scoped BigOperators

/- ### Part 1: Primitive-recursive integer and list primitives -/

private lemma encode_int_ofNat (m : ℕ) : Encodable.encode (Int.ofNat m) = 2 * m := rfl
private lemma encode_int_negSucc (n : ℕ) : Encodable.encode (Int.negSucc n) = 2 * n + 1 := rfl

private lemma bodd_two_mul (k : ℕ) : (2 * k).bodd = false := by
  rw [Nat.bodd_mul]; rfl

private lemma bodd_two_mul_add_one (k : ℕ) : (2 * k + 1).bodd = true := by
  rw [Nat.bodd_succ, bodd_two_mul]; rfl

private lemma div2_two_mul (k : ℕ) : (2 * k).div2 = k := by
  rw [Nat.div2_val]; omega

private lemma div2_two_mul_add_one (k : ℕ) : (2 * k + 1).div2 = k := by
  rw [Nat.div2_val]; omega

private lemma primrec_int_ofNat : Primrec (Int.ofNat : ℕ → ℤ) := by
  rw [← Primrec.encode_iff]
  exact Primrec.nat_double.of_eq fun _ => rfl

private lemma primrec_int_natCast : Primrec (Nat.cast : ℕ → ℤ) :=
  primrec_int_ofNat.of_eq fun _ => rfl

private lemma primrec_int_natAbs : Primrec Int.natAbs := by
  have h : Primrec (fun z : ℤ =>
      cond (Encodable.encode z).bodd ((Encodable.encode z).div2 + 1) (Encodable.encode z).div2) :=
    Primrec.cond (Primrec.nat_bodd.comp Primrec.encode)
      (Primrec.succ.comp (Primrec.nat_div2.comp Primrec.encode))
      (Primrec.nat_div2.comp Primrec.encode)
  refine h.of_eq fun z => ?_
  cases z with
  | ofNat m =>
    rw [encode_int_ofNat, bodd_two_mul, div2_two_mul]
    rfl
  | negSucc n =>
    rw [encode_int_negSucc, bodd_two_mul_add_one, div2_two_mul_add_one]
    rfl

private lemma primrec_int_nonneg : Primrec (fun z : ℤ => decide ((0 : ℤ) ≤ z)) := by
  have h : ∀ z : ℤ, decide ((0 : ℤ) ≤ z) = !(Encodable.encode z).bodd := by
    rintro (m | n)
    · rw [encode_int_ofNat, bodd_two_mul]
      simp [Int.ofNat_eq_natCast]
    · rw [encode_int_negSucc, bodd_two_mul_add_one]
      simp [show ¬ ((0 : ℤ) ≤ Int.negSucc n) by omega]
  exact (Primrec.not.comp (Primrec.nat_bodd.comp Primrec.encode)).of_eq fun z => (h z).symm

private lemma primrec_int_lt_zero : Primrec (fun z : ℤ => decide (z < (0 : ℤ))) := by
  have h : ∀ z : ℤ, decide (z < (0 : ℤ)) = (Encodable.encode z).bodd := by
    rintro (m | n)
    · rw [encode_int_ofNat, bodd_two_mul]
      simp [Int.ofNat_eq_natCast]
    · rw [encode_int_negSucc, bodd_two_mul_add_one]
      simp [show Int.negSucc n < (0 : ℤ) by omega]
  exact (Primrec.nat_bodd.comp Primrec.encode).of_eq fun z => (h z).symm

private lemma primrec_int_le_zero : Primrec (fun z : ℤ => decide (z ≤ (0 : ℤ))) := by
  have h : ∀ z : ℤ, decide (z ≤ (0 : ℤ)) = ((Encodable.encode z).bodd || decide (Encodable.encode z = 0)) := by
    rintro (m | n)
    · rw [encode_int_ofNat, bodd_two_mul]
      cases m <;> simp [Int.ofNat_eq_natCast]
    · rw [encode_int_negSucc, bodd_two_mul_add_one]
      simp [show Int.negSucc n ≤ (0 : ℤ) by omega]
  exact (Primrec.or.comp (Primrec.nat_bodd.comp Primrec.encode)
    (Primrec.eq.decide.comp Primrec.encode (Primrec.const 0))).of_eq fun z => (h z).symm

private lemma primrec_int_gt_zero : Primrec (fun z : ℤ => decide ((0 : ℤ) < z)) := by
  have h : ∀ z : ℤ, decide ((0 : ℤ) < z) = !(decide (z ≤ (0 : ℤ))) := by
    intro z
    by_cases hz : (0 : ℤ) < z
    · simp [hz, show ¬ (z ≤ 0) by omega]
    · simp [hz, show z ≤ 0 by omega]
  exact (Primrec.not.comp primrec_int_le_zero).of_eq fun z => (h z).symm

private lemma primrec_int_neg : Primrec (fun z : ℤ => -z) := by
  rw [← Primrec.encode_iff]
  have h : Primrec (fun z : ℤ =>
      if Encodable.encode z = 0 then 0
      else cond (Encodable.encode z).bodd
        (2 * ((Encodable.encode z).div2 + 1))
        (2 * ((Encodable.encode z).div2 - 1) + 1)) :=
    Primrec.ite (Primrec.eq.comp Primrec.encode (Primrec.const 0)) (Primrec.const 0)
      (Primrec.cond (Primrec.nat_bodd.comp Primrec.encode)
        (Primrec.nat_double.comp (Primrec.succ.comp (Primrec.nat_div2.comp Primrec.encode)))
        (Primrec.nat_double_succ.comp (Primrec.pred.comp (Primrec.nat_div2.comp Primrec.encode))))
  refine h.of_eq fun z => ?_
  cases z with
  | ofNat m =>
    cases m with
    | zero =>
      change (if Encodable.encode (Int.ofNat 0) = 0 then 0 else _) = Encodable.encode (Int.ofNat 0)
      rw [encode_int_ofNat]
      simp
    | succ k =>
      have hne : 2 * (k + 1) ≠ 0 := by omega
      have hneg : -(Int.ofNat (k + 1)) = Int.negSucc k := rfl
      rw [hneg, encode_int_ofNat, encode_int_negSucc, if_neg hne, bodd_two_mul, div2_two_mul]
      simp
  | negSucc n =>
    have hne : 2 * n + 1 ≠ 0 := by omega
    have hneg : -(Int.negSucc n) = Int.ofNat (n + 1) := rfl
    rw [hneg, encode_int_negSucc, encode_int_ofNat, if_neg hne, bodd_two_mul_add_one,
      div2_two_mul_add_one]
    simp

private lemma primrec_int_add : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ) := by
  rw [Primrec₂, ← Primrec.encode_iff]
  let e1 : ℤ × ℤ → ℕ := fun p => Encodable.encode p.1
  let e2 : ℤ × ℤ → ℕ := fun p => Encodable.encode p.2
  let b1 : ℤ × ℤ → Bool := fun p => (e1 p).bodd
  let b2 : ℤ × ℤ → Bool := fun p => (e2 p).bodd
  let x1 : ℤ × ℤ → ℕ := fun p => (e1 p).div2
  let x2 : ℤ × ℤ → ℕ := fun p => (e2 p).div2
  have he1 : Primrec e1 := Primrec.encode.comp Primrec.fst
  have he2 : Primrec e2 := Primrec.encode.comp Primrec.snd
  have hb1 : Primrec b1 := Primrec.nat_bodd.comp he1
  have hb2 : Primrec b2 := Primrec.nat_bodd.comp he2
  have hx1 : Primrec x1 := Primrec.nat_div2.comp he1
  have hx2 : Primrec x2 := Primrec.nat_div2.comp he2
  have hff : Primrec (fun p => 2 * (x1 p + x2 p)) :=
    Primrec.nat_double.comp (Primrec.nat_add.comp hx1 hx2)
  have htt : Primrec (fun p => 2 * (x1 p + x2 p + 1) + 1) :=
    Primrec.nat_double_succ.comp (Primrec.succ.comp (Primrec.nat_add.comp hx1 hx2))
  have hft : Primrec (fun p => if x2 p < x1 p then 2 * (x1 p - (x2 p + 1)) else 2 * (x2 p - x1 p) + 1) :=
    Primrec.ite (Primrec.nat_lt.comp hx2 hx1)
      (Primrec.nat_double.comp (Primrec.nat_sub.comp hx1 (Primrec.succ.comp hx2)))
      (Primrec.nat_double_succ.comp (Primrec.nat_sub.comp hx2 hx1))
  have htf : Primrec (fun p => if x1 p < x2 p then 2 * (x2 p - (x1 p + 1)) else 2 * (x1 p - x2 p) + 1) :=
    Primrec.ite (Primrec.nat_lt.comp hx1 hx2)
      (Primrec.nat_double.comp (Primrec.nat_sub.comp hx2 (Primrec.succ.comp hx1)))
      (Primrec.nat_double_succ.comp (Primrec.nat_sub.comp hx1 hx2))
  have hcomb : Primrec (fun p : ℤ × ℤ =>
      cond (b1 p) (cond (b2 p) (2 * (x1 p + x2 p + 1) + 1)
                               (if x1 p < x2 p then 2 * (x2 p - (x1 p + 1)) else 2 * (x1 p - x2 p) + 1))
                  (cond (b2 p) (if x2 p < x1 p then 2 * (x1 p - (x2 p + 1)) else 2 * (x2 p - x1 p) + 1)
                               (2 * (x1 p + x2 p)))) :=
    Primrec.cond hb1 (Primrec.cond hb2 htt htf) (Primrec.cond hb2 hft hff)
  refine hcomb.of_eq fun ⟨z1, z2⟩ => ?_
  cases z1 with
  | ofNat m1 =>
    cases z2 with
    | ofNat m2 =>
      have heq : Int.ofNat m1 + Int.ofNat m2 = Int.ofNat (m1 + m2) := rfl
      rw [heq]
      simp only [b1, b2, x1, x2, e1, e2, encode_int_ofNat, bodd_two_mul, div2_two_mul, Bool.cond_false]
    | negSucc n2 =>
      simp only [b1, b2, x1, x2, e1, e2, encode_int_ofNat, encode_int_negSucc,
        bodd_two_mul, bodd_two_mul_add_one, div2_two_mul, div2_two_mul_add_one,
        Bool.cond_false, Bool.cond_true]
      split_ifs with h
      · have heq : Int.ofNat m1 + Int.negSucc n2 = Int.ofNat (m1 - (n2 + 1)) := by
          simp only [Int.ofNat_eq_natCast]; omega
        rw [heq, encode_int_ofNat]
      · have heq : Int.ofNat m1 + Int.negSucc n2 = Int.negSucc (n2 - m1) := by
          simp only [Int.ofNat_eq_natCast]; omega
        rw [heq, encode_int_negSucc]
  | negSucc n1 =>
    cases z2 with
    | ofNat m2 =>
      simp only [b1, b2, x1, x2, e1, e2, encode_int_ofNat, encode_int_negSucc,
        bodd_two_mul, bodd_two_mul_add_one, div2_two_mul, div2_two_mul_add_one,
        Bool.cond_false, Bool.cond_true]
      split_ifs with h
      · have heq : Int.negSucc n1 + Int.ofNat m2 = Int.ofNat (m2 - (n1 + 1)) := by
          simp only [Int.ofNat_eq_natCast]; omega
        rw [heq, encode_int_ofNat]
      · have heq : Int.negSucc n1 + Int.ofNat m2 = Int.negSucc (n1 - m2) := by
          simp only [Int.ofNat_eq_natCast]; omega
        rw [heq, encode_int_negSucc]
    | negSucc n2 =>
      have heq : Int.negSucc n1 + Int.negSucc n2 = Int.negSucc (n1 + n2 + 1) := by omega
      rw [heq]
      simp only [b1, b2, x1, x2, e1, e2, encode_int_negSucc,
        bodd_two_mul_add_one, div2_two_mul_add_one, Bool.cond_true]

private lemma primrec_int_sub : Primrec₂ ((· - ·) : ℤ → ℤ → ℤ) :=
  (primrec_int_add.comp Primrec.fst (primrec_int_neg.comp Primrec.snd)).of_eq fun _ => rfl

private lemma primrec_int_mul : Primrec₂ ((· * ·) : ℤ → ℤ → ℤ) := by
  have hm : Primrec (fun p : ℤ × ℤ => Int.ofNat (p.1.natAbs * p.2.natAbs)) :=
    primrec_int_ofNat.comp (Primrec.nat_mul.comp (primrec_int_natAbs.comp Primrec.fst)
      (primrec_int_natAbs.comp Primrec.snd))
  have h : Primrec (fun p : ℤ × ℤ =>
      cond (decide (p.1 < 0))
        (cond (decide (p.2 < 0)) (Int.ofNat (p.1.natAbs * p.2.natAbs))
          (-(Int.ofNat (p.1.natAbs * p.2.natAbs))))
        (cond (decide (p.2 < 0)) (-(Int.ofNat (p.1.natAbs * p.2.natAbs)))
          (Int.ofNat (p.1.natAbs * p.2.natAbs)))) :=
    Primrec.cond (primrec_int_lt_zero.comp Primrec.fst)
      (Primrec.cond (primrec_int_lt_zero.comp Primrec.snd) hm (primrec_int_neg.comp hm))
      (Primrec.cond (primrec_int_lt_zero.comp Primrec.snd) (primrec_int_neg.comp hm) hm)
  refine h.of_eq fun ⟨a, b⟩ => ?_
  dsimp only
  cases a with
  | ofNat m1 =>
    have h1 : decide (Int.ofNat m1 < 0) = false := decide_eq_false (by simp [Int.ofNat_eq_natCast])
    cases b with
    | ofNat m2 =>
      have h2 : decide (Int.ofNat m2 < 0) = false := decide_eq_false (by simp [Int.ofNat_eq_natCast])
      rw [h1, h2]
      simp only [Bool.cond_false, Int.ofNat_eq_natCast, Int.natAbs_natCast, Nat.cast_mul]
    | negSucc n2 =>
      have h2 : decide (Int.negSucc n2 < 0) = true := decide_eq_true (by omega)
      rw [h1, h2, Int.natAbs_negSucc]
      simp only [Bool.cond_false, Bool.cond_true, Int.ofNat_eq_natCast, Int.natAbs_natCast,
        Int.negSucc_eq, Nat.cast_mul, Nat.cast_succ]
      ring
  | negSucc n1 =>
    have h1 : decide (Int.negSucc n1 < 0) = true := decide_eq_true (by omega)
    cases b with
    | ofNat m2 =>
      have h2 : decide (Int.ofNat m2 < 0) = false := decide_eq_false (by simp [Int.ofNat_eq_natCast])
      rw [h1, h2, Int.natAbs_negSucc]
      simp only [Bool.cond_false, Bool.cond_true, Int.ofNat_eq_natCast, Int.natAbs_natCast,
        Int.negSucc_eq, Nat.cast_mul, Nat.cast_succ]
      ring
    | negSucc n2 =>
      have h2 : decide (Int.negSucc n2 < 0) = true := decide_eq_true (by omega)
      rw [h1, h2, Int.natAbs_negSucc, Int.natAbs_negSucc]
      simp only [Bool.cond_true, Int.ofNat_eq_natCast, Int.negSucc_eq,
        Nat.cast_mul, Nat.cast_succ]
      ring

private lemma primrec_list_headD_zero : Primrec (fun l : List ℤ => l.headD 0) :=
  ((Primrec.list_getD (0 : ℤ)).comp Primrec.id (Primrec.const 0)).of_eq fun l => by
    cases l <;> rfl

private def listAll {α : Type*} (p : α → Bool) (l : List α) : Bool :=
  l.foldr (fun x acc => p x && acc) true

private def listAny {α : Type*} (p : α → Bool) (l : List α) : Bool :=
  l.foldr (fun x acc => p x || acc) false

private lemma listAll_eq_true {α : Type*} (p : α → Bool) (l : List α) :
    listAll p l = true ↔ ∀ x ∈ l, p x = true := by
  induction l with
  | nil => simp [listAll]
  | cons a tl ih =>
    simp only [listAll, List.foldr_cons, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
    exact and_congr_right fun _ => ih

private lemma listAny_eq_true {α : Type*} (p : α → Bool) (l : List α) :
    listAny p l = true ↔ ∃ x ∈ l, p x = true := by
  induction l with
  | nil => simp [listAny]
  | cons a tl ih =>
    simp only [listAny, List.foldr_cons, Bool.or_eq_true, List.mem_cons, exists_eq_or_imp]
    exact or_congr_right ih

private lemma primrec_listAll {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun a => listAll (p a) (f a)) := by
  unfold listAll
  have hstep : Primrec₂ (fun (a : α) (bs : β × Bool) => p a bs.1 && bs.2) :=
    (Primrec.and.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr hf (Primrec.const true) hstep

private lemma primrec_listAny {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun a => listAny (p a) (f a)) := by
  unfold listAny
  have hstep : Primrec₂ (fun (a : α) (bs : β × Bool) => p a bs.1 || bs.2) :=
    (Primrec.or.comp (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr hf (Primrec.const false) hstep

/- ### Part 2: Linear forms, Atoms, Conjunctions, and DNF -/

private abbrev Atom := Bool × ℕ × List ℤ × ℤ
private abbrev Conj := List Atom
private abbrev DNF := List Conj

private def dot : List ℤ → List ℤ → ℤ
  | [], _ => 0
  | a :: as, ρ => a * ρ.headD 0 + dot as ρ.tail

private lemma dot_nil_left (ρ : List ℤ) : dot [] ρ = 0 := rfl

private lemma dot_nil_right (a : List ℤ) : dot a [] = 0 := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [dot, ih]

private lemma dot_cons_cons (a0 : ℤ) (as : List ℤ) (x : ℤ) (ρ : List ℤ) :
    dot (a0 :: as) (x :: ρ) = a0 * x + dot as ρ := rfl

private lemma dot_head_tail (a : List ℤ) (x : ℤ) (ρ : List ℤ) :
    dot a (x :: ρ) = a.headD 0 * x + dot a.tail ρ := by
  cases a with
  | nil => simp [dot]
  | cons a0 as => rfl

private lemma dot_eq_sum_range (a ρ : List ℤ) :
    dot a ρ = ∑ i ∈ Finset.range a.length, a.getD i 0 * ρ.getD i 0 := by
  induction a generalizing ρ with
  | nil => simp [dot]
  | cons a0 as ih =>
    rw [dot, List.length_cons, Finset.sum_range_succ']
    have h0 : (a0 :: as).getD 0 0 * ρ.getD 0 0 = a0 * ρ.headD 0 := by
      cases ρ <;> rfl
    have htail : ∀ i, (a0 :: as).getD (i + 1) 0 * ρ.getD (i + 1) 0 =
        as.getD i 0 * ρ.tail.getD i 0 := by
      intro i
      cases ρ with
      | nil => simp [List.getD]
      | cons y ys => simp [List.getD]
    simp_rw [htail]
    rw [← ih ρ.tail, h0, add_comm]

private lemma dot_eq_sum_range_ge {a ρ : List ℤ} {n : ℕ} (hn : a.length ≤ n) :
    dot a ρ = ∑ i ∈ Finset.range n, a.getD i 0 * ρ.getD i 0 := by
  rw [dot_eq_sum_range]
  refine Finset.sum_subset (Finset.range_mono hn) fun i _ hnot => ?_
  have hge : a.length ≤ i := by
    simp only [Finset.mem_range] at hnot; omega
  have hget : a.getD i 0 = 0 := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
  rw [hget, zero_mul]

private lemma dot_append {a b xs ρ : List ℤ} (h : a.length = xs.length) :
    dot (a ++ b) (xs ++ ρ) = dot a xs + dot b ρ := by
  induction a generalizing xs with
  | nil =>
    cases xs with
    | nil => simp [dot]
    | cons _ _ => simp at h
  | cons a0 as ih =>
    cases xs with
    | nil => simp at h
    | cons x0 xs' =>
      simp only [List.length_cons, Nat.succ.injEq] at h
      simp only [List.cons_append, dot_cons_cons, ih h, add_assoc]

private def scaleList (k : ℤ) (a : List ℤ) : List ℤ :=
  a.map (fun x => k * x)

private lemma primrec_scaleList : Primrec₂ scaleList :=
  Primrec.list_map Primrec.snd (primrec_int_mul.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)

private lemma dot_scaleList (k : ℤ) (a ρ : List ℤ) :
    dot (scaleList k a) ρ = k * dot a ρ := by
  induction a generalizing ρ with
  | nil => simp [scaleList, dot]
  | cons a0 as ih =>
    rw [scaleList, List.map_cons, dot, ← scaleList, ih ρ.tail, dot]
    ring

private def addList (a b : List ℤ) : List ℤ :=
  (List.range (max a.length b.length)).map (fun i => a.getD i 0 + b.getD i 0)

private lemma primrec_addList : Primrec₂ addList := by
  unfold addList
  refine Primrec.list_map
    (Primrec.list_range.comp (Primrec.nat_max.comp
      (Primrec.list_length.comp Primrec.fst) (Primrec.list_length.comp Primrec.snd))) ?_
  have h1 : Primrec₂ (fun (p : List ℤ × List ℤ) (i : ℕ) => p.1.getD i 0) :=
    (Primrec.list_getD (0 : ℤ)).comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right
  have h2 : Primrec₂ (fun (p : List ℤ × List ℤ) (i : ℕ) => p.2.getD i 0) :=
    (Primrec.list_getD (0 : ℤ)).comp₂ (Primrec.snd.comp₂ Primrec₂.left) Primrec₂.right
  exact primrec_int_add.comp₂ h1 h2

private lemma dot_addList (a b ρ : List ℤ) :
    dot (addList a b) ρ = dot a ρ + dot b ρ := by
  let n := max a.length b.length
  have ha : dot a ρ = ∑ i ∈ Finset.range n, a.getD i 0 * ρ.getD i 0 :=
    dot_eq_sum_range_ge (le_max_left _ _)
  have hb : dot b ρ = ∑ i ∈ Finset.range n, b.getD i 0 * ρ.getD i 0 :=
    dot_eq_sum_range_ge (le_max_right _ _)
  rw [dot_eq_sum_range, ha, hb, ← Finset.sum_add_distrib]
  have hlen : (addList a b).length = n := by simp [addList, n]
  rw [hlen]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i < n := Finset.mem_range.mp hi
  have hget : (addList a b).getD i 0 = a.getD i 0 + b.getD i 0 := by
    simp [addList, List.getD_eq_getElem?_getD, hin, n]
  rw [hget, add_mul]

private def unitVec (k : ℕ) (v : ℤ) : List ℤ :=
  (List.range (k + 1)).map (fun i => if i = k then v else 0)

private lemma primrec_unitVec : Primrec₂ unitVec := by
  unfold unitVec
  refine Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.fst)) ?_
  exact (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.fst.comp Primrec.fst))
    (Primrec.snd.comp Primrec.fst) (Primrec.const (0 : ℤ))).to₂

private lemma dot_unitVec (k : ℕ) (v : ℤ) (ρ : List ℤ) :
    dot (unitVec k v) ρ = v * ρ.getD k 0 := by
  rw [dot_eq_sum_range]
  have hlen : (unitVec k v).length = k + 1 := by simp [unitVec]
  rw [hlen, Finset.sum_eq_single k]
  · have hget : (unitVec k v).getD k 0 = v := by
      simp [unitVec, List.getD_eq_getElem?_getD]
    rw [hget]
  · intro i hi hne
    have hik : i < k + 1 := Finset.mem_range.mp hi
    have hget : (unitVec k v).getD i 0 = 0 := by
      simp [unitVec, List.getD_eq_getElem?_getD, hik, hne]
    rw [hget, zero_mul]
  · intro hnot
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self k)) hnot

private def evalAtom (ρ : List ℤ) (at_ : Atom) : Prop :=
  if at_.1 then ((max at_.2.1 1 : ℕ) : ℤ) ∣ (dot at_.2.2.1 ρ + at_.2.2.2)
  else dot at_.2.2.1 ρ + at_.2.2.2 ≤ 0

private def evalConj (ρ : List ℤ) (C : Conj) : Prop :=
  ∀ at_ ∈ C, evalAtom ρ at_

private def evalDNF (ρ : List ℤ) (D : DNF) : Prop :=
  ∃ C ∈ D, evalConj ρ C

private def evalClosedAtom (at_ : Atom) : Bool :=
  cond at_.1 (decide (at_.2.2.2.natAbs % max at_.2.1 1 = 0)) (decide (at_.2.2.2 ≤ 0))

private def evalClosedConj (C : Conj) : Bool :=
  listAll evalClosedAtom C

private def evalClosedDNF (D : DNF) : Bool :=
  listAny evalClosedConj D

private lemma evalClosedAtom_iff (at_ : Atom) :
    evalClosedAtom at_ = true ↔ evalAtom [] at_ := by
  rcases at_ with ⟨isDvd, m, a, c⟩
  cases isDvd with
  | false =>
    simp [evalClosedAtom, evalAtom, dot_nil_right]
  | true =>
    simp only [evalClosedAtom, Bool.cond_true, decide_eq_true_eq, evalAtom, ↓reduceIte,
      dot_nil_right, zero_add]
    rw [Int.natCast_dvd, Nat.dvd_iff_mod_eq_zero]

private lemma evalClosedConj_iff (C : Conj) :
    evalClosedConj C = true ↔ evalConj [] C := by
  rw [evalClosedConj, listAll_eq_true, evalConj]
  exact forall_congr' fun at_ => imp_congr_right fun _ => evalClosedAtom_iff at_

private lemma evalClosedDNF_iff (D : DNF) :
    evalClosedDNF D = true ↔ evalDNF [] D := by
  rw [evalClosedDNF, listAny_eq_true, evalDNF]
  exact exists_congr fun C => and_congr_right fun _ => evalClosedConj_iff C

private lemma primrec_evalClosedAtom : Primrec evalClosedAtom := by
  unfold evalClosedAtom
  have hb : Primrec (fun at_ : Atom => at_.1) := Primrec.fst
  have hm : Primrec (fun at_ : Atom => max at_.2.1 1) :=
    Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)
  have hc : Primrec (fun at_ : Atom => at_.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hdvd : Primrec (fun at_ : Atom => decide (at_.2.2.2.natAbs % max at_.2.1 1 = 0)) :=
    Primrec.eq.decide.comp (Primrec.nat_mod.comp (primrec_int_natAbs.comp hc) hm) (Primrec.const 0)
  have hle : Primrec (fun at_ : Atom => decide (at_.2.2.2 ≤ 0)) :=
    primrec_int_le_zero.comp hc
  exact Primrec.cond hb hdvd hle

private lemma primrec_evalClosedConj : Primrec evalClosedConj :=
  primrec_listAll (Primrec.id (α := Conj)) (primrec_evalClosedAtom.comp Primrec.snd).to₂

private lemma primrec_evalClosedDNF : Primrec evalClosedDNF :=
  primrec_listAny (Primrec.id (α := DNF)) (primrec_evalClosedConj.comp Primrec.snd).to₂

/- ### Part 3: Boolean operations on DNF (`andDNF`, `negDNF`) -/

private def andDNF (D1 D2 : DNF) : DNF :=
  D1.flatMap fun c1 => D2.map fun c2 => c1 ++ c2

private lemma evalDNF_andDNF (ρ : List ℤ) (D1 D2 : DNF) :
    evalDNF ρ (andDNF D1 D2) ↔ evalDNF ρ D1 ∧ evalDNF ρ D2 := by
  simp only [andDNF, evalDNF, evalConj, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨_, ⟨c1, hc1, c2, hc2, rfl⟩, hall⟩
    exact ⟨⟨c1, hc1, fun a ha => hall a (List.mem_append_left c2 ha)⟩,
      ⟨c2, hc2, fun a ha => hall a (List.mem_append_right c1 ha)⟩⟩
  · rintro ⟨⟨c1, hc1, h1⟩, ⟨c2, hc2, h2⟩⟩
    refine ⟨c1 ++ c2, ⟨c1, hc1, c2, hc2, rfl⟩, fun a ha => ?_⟩
    rcases List.mem_append.mp ha with ha | ha
    · exact h1 a ha
    · exact h2 a ha

private lemma primrec_andDNF : Primrec₂ andDNF := by
  change Primrec (fun p : DNF × DNF => andDNF p.1 p.2)
  unfold andDNF
  refine Primrec.list_flatMap (Primrec.fst (α := DNF) (β := DNF)) ?_
  have hD2 : Primrec (fun q : (DNF × DNF) × Conj => q.1.2) := Primrec.snd.comp Primrec.fst
  have hmap : Primrec₂ (fun (q : (DNF × DNF) × Conj) (c2 : Conj) => q.2 ++ c2) :=
    (Primrec.list_append.comp (Primrec.snd.comp (Primrec.fst (α := (DNF × DNF) × Conj) (β := Conj)))
      (Primrec.snd (α := (DNF × DNF) × Conj) (β := Conj))).to₂
  exact (Primrec.list_map hD2 hmap).to₂

private def negAtom (at_ : Atom) : DNF :=
  if at_.1 then
    let m' := max at_.2.1 1
    (List.range (m' - 1)).map fun r =>
      [(true, m', at_.2.2.1, at_.2.2.2 + ((r + 1 : ℕ) : ℤ))]
  else
    [[(false, 0, scaleList (-1) at_.2.2.1, -at_.2.2.2 + 1)]]

private lemma evalDNF_negAtom (ρ : List ℤ) (at_ : Atom) :
    evalDNF ρ (negAtom at_) ↔ ¬ evalAtom ρ at_ := by
  rcases at_ with ⟨isDvd, m, a, c⟩
  cases isDvd with
  | false =>
    simp only [negAtom, Bool.false_eq_true, ↓reduceIte, evalDNF, evalConj, evalAtom,
      List.mem_singleton, exists_eq_left, forall_eq, dot_scaleList]
    omega
  | true =>
    set m' := max m 1
    have hm' : 1 ≤ m' := le_max_right m 1
    have hm'_pos : (0 : ℤ) < (m' : ℤ) := by omega
    simp only [negAtom, ↓reduceIte, evalDNF, evalConj, evalAtom, List.mem_map, List.mem_range]
    have hmax : max m' 1 = m' := max_eq_left hm'
    set t := dot a ρ + c
    constructor
    · rintro ⟨_, ⟨r, hr, rfl⟩, hall⟩
      have hd := hall _ (List.mem_singleton_self _)
      simp only [↓reduceIte] at hd
      change ((max m' 1 : ℕ) : ℤ) ∣ dot a ρ + (c + ((r + 1 : ℕ) : ℤ)) at hd
      rw [hmax] at hd
      intro ht
      have hr_dvd : (m' : ℤ) ∣ ((r + 1 : ℕ) : ℤ) := by
        have hdiff : ((r + 1 : ℕ) : ℤ) = (dot a ρ + (c + ((r + 1 : ℕ) : ℤ))) - t := by
          dsimp [t]; ring
        rw [hdiff]
        exact dvd_sub hd ht
      have hr_nat : m' ∣ r + 1 := Int.natCast_dvd_natCast.mp hr_dvd
      have hle := Nat.le_of_dvd (Nat.succ_pos r) hr_nat
      omega
    · intro hndvd
      have hmod_ne : t % (m' : ℤ) ≠ 0 := fun h0 => hndvd (Int.dvd_of_emod_eq_zero h0)
      have hmod_nonneg : 0 ≤ t % (m' : ℤ) := Int.emod_nonneg t (ne_of_gt hm'_pos)
      have hmod_lt : t % (m' : ℤ) < (m' : ℤ) := Int.emod_lt_of_pos t hm'_pos
      set rem : ℕ := m' - (t % (m' : ℤ)).toNat
      have hrem_pos : 1 ≤ rem ∧ rem < m' := by omega
      have hrem_z : (rem : ℤ) = (m' : ℤ) - t % (m' : ℤ) := by omega
      refine ⟨[(true, m', a, c + (rem : ℤ))], ⟨rem - 1, by omega, ?_⟩, ?_⟩
      · have h1 : rem - 1 + 1 = rem := by omega
        rw [h1]
      · intro x hx
        rw [List.mem_singleton.mp hx]
        simp only [evalAtom, ↓reduceIte, hmax]
        have heq : dot a ρ + (c + (rem : ℤ)) = t + (rem : ℤ) := by dsimp [t]; ring
        rw [heq]
        have hdiv : (m' : ℤ) * (t / (m' : ℤ)) + t % (m' : ℤ) = t := Int.mul_ediv_add_emod t m'
        refine ⟨t / (m' : ℤ) + 1, ?_⟩
        linarith

private lemma primrec_negAtom : Primrec negAtom := by
  unfold negAtom
  have hb : Primrec (fun at_ : Atom => at_.1) := Primrec.fst
  have hm' : Primrec (fun at_ : Atom => max at_.2.1 1) :=
    Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)
  have ha : Primrec (fun at_ : Atom => at_.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hc : Primrec (fun at_ : Atom => at_.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have htrue : Primrec (fun at_ : Atom =>
      (List.range (max at_.2.1 1 - 1)).map fun r =>
        [(true, max at_.2.1 1, at_.2.2.1, at_.2.2.2 + ((r + 1 : ℕ) : ℤ))]) := by
    refine Primrec.list_map (Primrec.list_range.comp (Primrec.pred.comp hm')) ?_
    have hatom : Primrec (fun q : Atom × ℕ =>
        (true, max q.1.2.1 1, q.1.2.2.1, q.1.2.2.2 + ((q.2 + 1 : ℕ) : ℤ))) :=
      Primrec.pair (Primrec.const true)
        (Primrec.pair (hm'.comp Primrec.fst)
          (Primrec.pair (ha.comp Primrec.fst)
            (primrec_int_add.comp (hc.comp Primrec.fst)
              (primrec_int_natCast.comp (Primrec.succ.comp Primrec.snd)))))
    exact (Primrec.list_cons.comp hatom (Primrec.const ([] : Conj))).to₂
  have hfalse : Primrec (fun at_ : Atom =>
      [[(false, 0, scaleList (-1) at_.2.2.1, -at_.2.2.2 + 1)]]) := by
    have hatom : Primrec (fun at_ : Atom =>
        (false, 0, scaleList (-1) at_.2.2.1, -at_.2.2.2 + 1)) :=
      Primrec.pair (Primrec.const false)
        (Primrec.pair (Primrec.const 0)
          (Primrec.pair (primrec_scaleList.comp (Primrec.const (-1 : ℤ)) ha)
            (primrec_int_add.comp (primrec_int_neg.comp hc) (Primrec.const (1 : ℤ)))))
    have hconj : Primrec (fun at_ : Atom => [(false, 0, scaleList (-1) at_.2.2.1, -at_.2.2.2 + 1)]) :=
      Primrec.list_cons.comp hatom (Primrec.const ([] : Conj))
    exact Primrec.list_cons.comp hconj (Primrec.const ([] : DNF))
  exact (Primrec.cond hb htrue hfalse).of_eq fun at_ => by
    cases at_.1 <;> rfl

private def negConj (C : Conj) : DNF :=
  C.flatMap negAtom

private lemma evalDNF_negConj (ρ : List ℤ) (C : Conj) :
    evalDNF ρ (negConj C) ↔ ¬ evalConj ρ C := by
  simp only [negConj, evalDNF, evalConj, List.mem_flatMap]
  constructor
  · rintro ⟨c, ⟨a, ha, hc⟩, hev⟩ hall
    exact (evalDNF_negAtom ρ a).mp ⟨c, hc, hev⟩ (hall a ha)
  · intro hnot
    push Not at hnot
    obtain ⟨a, ha, hna⟩ := hnot
    obtain ⟨c, hc, hev⟩ := (evalDNF_negAtom ρ a).mpr hna
    exact ⟨c, ⟨a, ha, hc⟩, hev⟩

private lemma primrec_negConj : Primrec negConj :=
  Primrec.list_flatMap (Primrec.id (α := Conj)) (primrec_negAtom.comp Primrec.snd).to₂

private def negDNF (D : DNF) : DNF :=
  D.foldr (fun C acc => andDNF (negConj C) acc) [[]]

private lemma evalDNF_negDNF (ρ : List ℤ) (D : DNF) :
    evalDNF ρ (negDNF D) ↔ ¬ evalDNF ρ D := by
  induction D with
  | nil =>
    simp [negDNF, evalDNF, evalConj]
  | cons C tl ih =>
    have hstep : negDNF (C :: tl) = andDNF (negConj C) (negDNF tl) := rfl
    rw [hstep, evalDNF_andDNF, evalDNF_negConj, ih]
    simp only [evalDNF, List.mem_cons, exists_eq_or_imp, not_or]

private lemma primrec_negDNF : Primrec negDNF := by
  unfold negDNF
  have hstep : Primrec₂ (fun (_ : DNF) (bs : Conj × DNF) => andDNF (negConj bs.1) bs.2) :=
    (primrec_andDNF.comp (primrec_negConj.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr (Primrec.id (α := DNF)) (Primrec.const ([[]] : DNF)) hstep

/- ### Part 4: Cooper's Quantifier Elimination on a single conjunction -/

private def coeffProd (C : Conj) : ℕ :=
  C.foldr (fun at_ acc => max (at_.2.2.1.headD 0).natAbs 1 * acc) 1

private lemma coeffProd_pos (C : Conj) : 1 ≤ coeffProd C := by
  induction C with
  | nil => simp [coeffProd]
  | cons a tl ih =>
    simp only [coeffProd, List.foldr_cons]
    have h1 : 1 ≤ max (a.2.2.1.headD 0).natAbs 1 := le_max_right _ _
    exact Nat.mul_pos h1 ih

private lemma dvd_coeffProd {C : Conj} {at_ : Atom} (hmem : at_ ∈ C) (hne : at_.2.2.1.headD 0 ≠ 0) :
    (at_.2.2.1.headD 0).natAbs ∣ coeffProd C := by
  induction C with
  | nil => cases hmem
  | cons a tl ih =>
    simp only [coeffProd, List.foldr_cons]
    rcases List.mem_cons.mp hmem with rfl | htl
    · have hpos : 1 ≤ (at_.2.2.1.headD 0).natAbs := Int.natAbs_pos.mpr hne
      rw [max_eq_left hpos]
      exact dvd_mul_right _ _
    · exact dvd_mul_of_dvd_right (ih htl) _

private lemma primrec_coeffProd : Primrec coeffProd := by
  unfold coeffProd
  have h1 : Primrec (fun q : Conj × (Atom × ℕ) =>
      max (q.2.1.2.2.1.headD 0).natAbs 1) :=
    Primrec.nat_max.comp
      (primrec_int_natAbs.comp (primrec_list_headD_zero.comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))))
      (Primrec.const 1)
  have hstep : Primrec₂ (fun (_ : Conj) (q : Atom × ℕ) => max (q.1.2.2.1.headD 0).natAbs 1 * q.2) :=
    (Primrec.nat_mul.comp h1 (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.list_foldr (Primrec.id (α := Conj)) (Primrec.const 1) hstep

private def scaleAtomForX (L : ℕ) (at_ : Atom) : Atom :=
  let a0 := at_.2.2.1.headD 0
  let tl := at_.2.2.1.tail
  if a0 = 0 then
    (at_.1, at_.2.1, 0 :: tl, at_.2.2.2)
  else
    let k := L / a0.natAbs
    if at_.1 then
      if 0 < a0 then
        (true, max at_.2.1 1 * k, 1 :: scaleList (k : ℤ) tl, (k : ℤ) * at_.2.2.2)
      else
        (true, max at_.2.1 1 * k, 1 :: scaleList (-(k : ℤ)) tl, (-(k : ℤ)) * at_.2.2.2)
    else
      if 0 < a0 then
        (false, 0, 1 :: scaleList (k : ℤ) tl, (k : ℤ) * at_.2.2.2)
      else
        (false, 0, (-1) :: scaleList (k : ℤ) tl, (k : ℤ) * at_.2.2.2)

private lemma primrec_scaleAtomForX : Primrec₂ scaleAtomForX := by
  change Primrec (fun q : ℕ × Atom => scaleAtomForX q.1 q.2)
  have hL : Primrec (fun q : ℕ × Atom => q.1) := Primrec.fst
  have hb : Primrec (fun q : ℕ × Atom => q.2.1) := Primrec.fst.comp Primrec.snd
  have hm : Primrec (fun q : ℕ × Atom => max q.2.2.1 1) :=
    Primrec.nat_max.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const 1)
  have hmraw : Primrec (fun q : ℕ × Atom => q.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ha : Primrec (fun q : ℕ × Atom => q.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hc : Primrec (fun q : ℕ × Atom => q.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have ha0 : Primrec (fun q : ℕ × Atom => q.2.2.2.1.headD 0) :=
    primrec_list_headD_zero.comp ha
  have htl : Primrec (fun q : ℕ × Atom => q.2.2.2.1.tail) :=
    Primrec.list_tail.comp ha
  have hk : Primrec (fun q : ℕ × Atom => q.1 / (q.2.2.2.1.headD 0).natAbs) :=
    Primrec.nat_div.comp hL (primrec_int_natAbs.comp ha0)
  have hkz : Primrec (fun q : ℕ × Atom => ((q.1 / (q.2.2.2.1.headD 0).natAbs : ℕ) : ℤ)) :=
    primrec_int_natCast.comp hk
  have hnkz : Primrec (fun q : ℕ × Atom => -((q.1 / (q.2.2.2.1.headD 0).natAbs : ℕ) : ℤ)) :=
    primrec_int_neg.comp hkz
  have hzero : Primrec (fun q : ℕ × Atom => (q.2.1, q.2.2.1, (0 : ℤ) :: q.2.2.2.1.tail, q.2.2.2.2)) :=
    Primrec.pair hb (Primrec.pair hmraw
      (Primrec.pair (Primrec.list_cons.comp (Primrec.const (0 : ℤ)) htl) hc))
  have hdp : Primrec (fun q : ℕ × Atom =>
      (true, max q.2.2.1 1 * (q.1 / (q.2.2.2.1.headD 0).natAbs),
        (1 : ℤ) :: scaleList ((q.1 / (q.2.2.2.1.headD 0).natAbs : ℕ) : ℤ) q.2.2.2.1.tail,
        ((q.1 / (q.2.2.2.1.headD 0).natAbs : ℕ) : ℤ) * q.2.2.2.2)) :=
    Primrec.pair (Primrec.const true)
      (Primrec.pair (Primrec.nat_mul.comp hm hk)
        (Primrec.pair (Primrec.list_cons.comp (Primrec.const (1 : ℤ)) (primrec_scaleList.comp hkz htl))
          (primrec_int_mul.comp hkz hc)))
  have hdn : Primrec (fun q : ℕ × Atom =>
      (true, max q.2.2.1 1 * (q.1 / (q.2.2.2.1.headD 0).natAbs),
        (1 : ℤ) :: scaleList (-((q.1 / (q.2.2.2.1.headD 0).natAbs : ℕ) : ℤ)) q.2.2.2.1.tail,
        (-((q.1 / (q.2.2.2.1.headD 0).natAbs : ℕ) : ℤ)) * q.2.2.2.2)) :=
    Primrec.pair (Primrec.const true)
      (Primrec.pair (Primrec.nat_mul.comp hm hk)
        (Primrec.pair (Primrec.list_cons.comp (Primrec.const (1 : ℤ)) (primrec_scaleList.comp hnkz htl))
          (primrec_int_mul.comp hnkz hc)))
  have hlp : Primrec (fun q : ℕ × Atom =>
      (false, 0,
        (1 : ℤ) :: scaleList ((q.1 / (q.2.2.2.1.headD 0).natAbs : ℕ) : ℤ) q.2.2.2.1.tail,
        ((q.1 / (q.2.2.2.1.headD 0).natAbs : ℕ) : ℤ) * q.2.2.2.2)) :=
    Primrec.pair (Primrec.const false)
      (Primrec.pair (Primrec.const 0)
        (Primrec.pair (Primrec.list_cons.comp (Primrec.const (1 : ℤ)) (primrec_scaleList.comp hkz htl))
          (primrec_int_mul.comp hkz hc)))
  have hln : Primrec (fun q : ℕ × Atom =>
      (false, 0,
        (-1 : ℤ) :: scaleList ((q.1 / (q.2.2.2.1.headD 0).natAbs : ℕ) : ℤ) q.2.2.2.1.tail,
        ((q.1 / (q.2.2.2.1.headD 0).natAbs : ℕ) : ℤ) * q.2.2.2.2)) :=
    Primrec.pair (Primrec.const false)
      (Primrec.pair (Primrec.const 0)
        (Primrec.pair (Primrec.list_cons.comp (Primrec.const (-1 : ℤ)) (primrec_scaleList.comp hkz htl))
          (primrec_int_mul.comp hkz hc)))
  have hgt : Primrec (fun q : ℕ × Atom => decide ((0 : ℤ) < q.2.2.2.1.headD 0)) :=
    primrec_int_gt_zero.comp ha0
  have hnz := Primrec.cond hb (Primrec.cond hgt hdp hdn) (Primrec.cond hgt hlp hln)
  have hfull := Primrec.ite (Primrec.eq.comp ha0 (Primrec.const (0 : ℤ))) hzero hnz
  refine hfull.of_eq fun ⟨L, at_⟩ => ?_
  dsimp only [scaleAtomForX]
  by_cases h0 : at_.2.2.1.headD 0 = 0
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0]
    rcases at_ with ⟨b, m, a, c⟩
    cases b
    · rw [if_neg Bool.false_ne_true]
      by_cases hpos : (0 : ℤ) < a.headD 0
      · rw [decide_eq_true hpos, if_pos hpos]; rfl
      · rw [decide_eq_false hpos, if_neg hpos]; rfl
    · rw [if_pos rfl]
      by_cases hpos : (0 : ℤ) < a.headD 0
      · rw [decide_eq_true hpos, if_pos hpos]; rfl
      · rw [decide_eq_false hpos, if_neg hpos]; rfl

private lemma scaleAtomForX_norm (L : ℕ) (at_ : Atom) :
    let at' := scaleAtomForX L at_
    (at'.1 = true → at'.2.2.1.headD 0 = 0 ∨ at'.2.2.1.headD 0 = 1) ∧
    (at'.1 = false → at'.2.2.1.headD 0 = 0 ∨ at'.2.2.1.headD 0 = 1 ∨ at'.2.2.1.headD 0 = -1) := by
  unfold scaleAtomForX
  dsimp only
  split_ifs <;> simp

private lemma evalAtom_scaleAtomForX {L : ℕ} (hL : 1 ≤ L) {at_ : Atom}
    (hdvd : at_.2.2.1.headD 0 ≠ 0 → (at_.2.2.1.headD 0).natAbs ∣ L) (x : ℤ) (ρ : List ℤ) :
    evalAtom ((L : ℤ) * x :: ρ) (scaleAtomForX L at_) ↔ evalAtom (x :: ρ) at_ := by
  rcases at_ with ⟨isDvd, m, a, c⟩
  unfold scaleAtomForX
  dsimp only
  set a0 := a.headD 0
  set tl := a.tail
  by_cases ha0 : a0 = 0
  · rw [if_pos ha0]
    cases isDvd <;> simp only [evalAtom, Bool.false_eq_true, ↓reduceIte, dot_cons_cons,
      dot_head_tail a x ρ, show a.headD 0 = 0 from ha0, zero_mul, zero_add] <;> rfl
  · rw [if_neg ha0]
    have hdiv : a0.natAbs ∣ L := hdvd ha0
    set k := L / a0.natAbs
    have hk_mul : a0.natAbs * k = L := Nat.mul_div_cancel' hdiv
    have hk_zmul : (a0.natAbs : ℤ) * (k : ℤ) = (L : ℤ) := by exact_mod_cast hk_mul
    have hk_pos : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk0, Nat.mul_zero] at hk_mul; omega
      · exact hkpos
    have hk_zpos : (0 : ℤ) < (k : ℤ) := by omega
    have hmk_pos : 1 ≤ max m 1 * k := Nat.mul_pos (le_max_right m 1) hk_pos
    have hmax_mk : max (max m 1 * k) 1 = max m 1 * k := max_eq_left hmk_pos
    cases isDvd with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hpos : 0 < a0
      · rw [if_pos hpos]
        have hka0 : (L : ℤ) = (k : ℤ) * a0 := by
          have : (a0.natAbs : ℤ) = a0 := Int.natAbs_of_nonneg hpos.le
          rw [this] at hk_zmul; linarith
        simp only [evalAtom, Bool.false_eq_true, ↓reduceIte]
        rw [dot_cons_cons, dot_scaleList, dot_head_tail a x ρ]
        have hrew : 1 * ((L : ℤ) * x) + (k : ℤ) * dot tl ρ + (k : ℤ) * c =
            (k : ℤ) * (a0 * x + dot tl ρ + c) := by
          rw [hka0]; ring
        rw [hrew]
        constructor <;> intro h <;> nlinarith
      · rw [if_neg hpos]
        have hneg : a0 < 0 := by omega
        have hka0 : (L : ℤ) = -(k : ℤ) * a0 := by
          have : (a0.natAbs : ℤ) = -a0 := Int.ofNat_natAbs_of_nonpos hneg.le
          rw [this] at hk_zmul; linarith
        simp only [evalAtom, Bool.false_eq_true, ↓reduceIte]
        rw [dot_cons_cons, dot_scaleList, dot_head_tail a x ρ]
        have hrew : -1 * ((L : ℤ) * x) + (k : ℤ) * dot tl ρ + (k : ℤ) * c =
            (k : ℤ) * (a0 * x + dot tl ρ + c) := by
          rw [hka0]; ring
        rw [hrew]
        constructor <;> intro h <;> nlinarith
    | true =>
      simp only [↓reduceIte]
      by_cases hpos : 0 < a0
      · rw [if_pos hpos]
        have hka0 : (L : ℤ) = (k : ℤ) * a0 := by
          have : (a0.natAbs : ℤ) = a0 := Int.natAbs_of_nonneg hpos.le
          rw [this] at hk_zmul; linarith
        simp only [evalAtom, ↓reduceIte, hmax_mk, Nat.cast_mul]
        rw [dot_cons_cons, dot_scaleList, dot_head_tail a x ρ]
        have hrew : 1 * ((L : ℤ) * x) + (k : ℤ) * dot tl ρ + (k : ℤ) * c =
            (a0 * x + dot tl ρ + c) * (k : ℤ) := by
          rw [hka0]; ring
        rw [hrew]
        exact mul_dvd_mul_iff_right (ne_of_gt hk_zpos)
      · rw [if_neg hpos]
        have hneg : a0 < 0 := by omega
        have hka0 : (L : ℤ) = -(k : ℤ) * a0 := by
          have : (a0.natAbs : ℤ) = -a0 := Int.ofNat_natAbs_of_nonpos hneg.le
          rw [this] at hk_zmul; linarith
        simp only [evalAtom, ↓reduceIte, hmax_mk, Nat.cast_mul]
        rw [dot_cons_cons, dot_scaleList, dot_head_tail a x ρ]
        have hrew : 1 * ((L : ℤ) * x) + -(k : ℤ) * dot tl ρ + -(k : ℤ) * c =
            (-(a0 * x + dot tl ρ + c)) * (k : ℤ) := by
          rw [hka0]; ring
        rw [hrew, mul_dvd_mul_iff_right (ne_of_gt hk_zpos), dvd_neg]

private def normalizeConj (C : Conj) : Conj :=
  let L := coeffProd C
  (true, L, [1], 0) :: C.map (scaleAtomForX L)

private lemma primrec_normalizeConj : Primrec normalizeConj := by
  unfold normalizeConj
  have hhead : Primrec (fun C : Conj => (true, coeffProd C, [(1 : ℤ)], (0 : ℤ))) :=
    Primrec.pair (Primrec.const true)
      (Primrec.pair primrec_coeffProd
        (Primrec.pair (Primrec.const ([(1 : ℤ)] : List ℤ)) (Primrec.const (0 : ℤ))))
  have hmap : Primrec (fun C : Conj => C.map (scaleAtomForX (coeffProd C))) :=
    Primrec.list_map (Primrec.id (α := Conj))
      (primrec_scaleAtomForX.comp (primrec_coeffProd.comp Primrec.fst) Primrec.snd).to₂
  exact Primrec.list_cons.comp hhead hmap

private lemma exists_normalizeConj (C : Conj) (ρ : List ℤ) :
    (∃ x : ℤ, evalConj (x :: ρ) C) ↔ (∃ x' : ℤ, evalConj (x' :: ρ) (normalizeConj C)) := by
  set L := coeffProd C
  have hL : 1 ≤ L := coeffProd_pos C
  have hmaxL : max L 1 = L := max_eq_left hL
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨(L : ℤ) * x, ?_⟩
    intro at' hat'
    simp only [normalizeConj, List.mem_cons, List.mem_map] at hat'
    rcases hat' with rfl | ⟨at_, hat_, rfl⟩
    · simp only [evalAtom, ↓reduceIte, dot_cons_cons, dot_nil_left, one_mul, add_zero]
      rw [hmaxL]
      exact dvd_mul_right _ _
    · exact (evalAtom_scaleAtomForX hL (fun hne => dvd_coeffProd hat_ hne) x ρ).mpr (hx at_ hat_)
  · rintro ⟨x', hx'⟩
    have hdvdL : (L : ℤ) ∣ x' := by
      have h0 := hx' (true, L, [1], 0) List.mem_cons_self
      simp only [evalAtom, ↓reduceIte, dot_cons_cons, dot_nil_left, one_mul, add_zero] at h0
      rwa [hmaxL] at h0
    obtain ⟨x, rfl⟩ := hdvdL
    refine ⟨x, fun at_ hat_ => ?_⟩
    have h1 := hx' (scaleAtomForX L at_)
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨at_, hat_, rfl⟩))
    exact (evalAtom_scaleAtomForX hL (fun hne => dvd_coeffProd hat_ hne) x ρ).mp h1

private def dvdPeriod (C' : Conj) : ℕ :=
  C'.foldr (fun at_ acc =>
    if at_.1 && decide (at_.2.2.1.headD 0 = 1) then max at_.2.1 1 * acc else acc) 1

private lemma dvdPeriod_pos (C' : Conj) : 1 ≤ dvdPeriod C' := by
  induction C' with
  | nil => simp [dvdPeriod]
  | cons a tl ih =>
    simp only [dvdPeriod, List.foldr_cons]
    split_ifs
    · exact Nat.mul_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)) ih
    · exact ih

private lemma dvd_dvdPeriod {C' : Conj} {at_ : Atom} (hmem : at_ ∈ C')
    (hdvd : at_.1 = true) (h1 : at_.2.2.1.headD 0 = 1) :
    max at_.2.1 1 ∣ dvdPeriod C' := by
  induction C' with
  | nil => cases hmem
  | cons a tl ih =>
    have hstep : dvdPeriod (a :: tl) =
        if (a.1 && decide (a.2.2.1.headD 0 = 1)) = true then max a.2.1 1 * dvdPeriod tl
        else dvdPeriod tl := rfl
    rw [hstep]
    rcases List.mem_cons.mp hmem with rfl | htl
    · rw [if_pos (by rw [hdvd, h1]; rfl)]
      exact dvd_mul_right _ _
    · split_ifs
      · exact dvd_mul_of_dvd_right (ih htl) _
      · exact ih htl

private lemma primrec_dvdPeriod : Primrec dvdPeriod := by
  unfold dvdPeriod
  have hcond : Primrec (fun q : Conj × (Atom × ℕ) =>
      q.2.1.1 && decide (q.2.1.2.2.1.headD 0 = 1)) :=
    Primrec.and.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.eq.decide.comp
        (primrec_list_headD_zero.comp
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))))
        (Primrec.const (1 : ℤ)))
  have hmul : Primrec (fun q : Conj × (Atom × ℕ) =>
      max q.2.1.2.1 1 * q.2.2) :=
    Primrec.nat_mul.comp
      (Primrec.nat_max.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.const 1))
      (Primrec.snd.comp Primrec.snd)
  have hstep : Primrec₂ (fun (_ : Conj) (q : Atom × ℕ) =>
      if (q.1.1 && decide (q.1.2.2.1.headD 0 = 1)) = true then max q.1.2.1 1 * q.2 else q.2) := by
    change Primrec (fun p : Conj × (Atom × ℕ) =>
      if (p.2.1.1 && decide (p.2.1.2.2.1.headD 0 = 1)) = true then max p.2.1.2.1 1 * p.2.2 else p.2.2)
    refine (Primrec.cond hcond hmul (Primrec.snd.comp Primrec.snd)).of_eq fun p => ?_
    cases (p.2.1.1 && decide (p.2.1.2.2.1.headD 0 = 1)) <;> rfl
  exact Primrec.list_foldr (Primrec.id (α := Conj)) (Primrec.const 1) hstep

private def lowerBounds (C' : Conj) : List (List ℤ × ℤ) :=
  C'.foldr (fun at_ acc =>
    if !at_.1 && decide (at_.2.2.1.headD 0 = -1) then (at_.2.2.1.tail, at_.2.2.2) :: acc
    else acc) []

private lemma mem_lowerBounds_iff (C' : Conj) (lb : List ℤ × ℤ) :
    lb ∈ lowerBounds C' ↔
      ∃ at_ ∈ C', at_.1 = false ∧ at_.2.2.1.headD 0 = -1 ∧ lb = (at_.2.2.1.tail, at_.2.2.2) := by
  induction C' with
  | nil => simp [lowerBounds]
  | cons a tl ih =>
    have hstep : lowerBounds (a :: tl) =
        if (!a.1 && decide (a.2.2.1.headD 0 = -1)) = true then
          (a.2.2.1.tail, a.2.2.2) :: lowerBounds tl
        else lowerBounds tl := rfl
    rw [hstep]
    by_cases hcond : (!a.1 && decide (a.2.2.1.headD 0 = -1)) = true
    · rw [if_pos hcond, List.mem_cons, ih]
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hcond
      constructor
      · rintro (rfl | ⟨at_, hat_, h1, h2, rfl⟩)
        · exact ⟨a, List.mem_cons_self, hcond.1, hcond.2, rfl⟩
        · exact ⟨at_, List.mem_cons_of_mem _ hat_, h1, h2, rfl⟩
      · rintro ⟨at_, hat_, h1, h2, rfl⟩
        rcases List.mem_cons.mp hat_ with rfl | htl
        · exact Or.inl rfl
        · exact Or.inr ⟨at_, htl, h1, h2, rfl⟩
    · rw [if_neg hcond, ih]
      constructor
      · rintro ⟨at_, hat_, h1, h2, rfl⟩
        exact ⟨at_, List.mem_cons_of_mem _ hat_, h1, h2, rfl⟩
      · rintro ⟨at_, hat_, h1, h2, rfl⟩
        rcases List.mem_cons.mp hat_ with rfl | htl
        · exfalso; apply hcond; rw [h1, h2]; rfl
        · exact ⟨at_, htl, h1, h2, rfl⟩

private lemma primrec_lowerBounds : Primrec lowerBounds := by
  unfold lowerBounds
  have hat_ : Primrec (fun q : Conj × (Atom × List (List ℤ × ℤ)) => q.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hcond : Primrec (fun q : Conj × (Atom × List (List ℤ × ℤ)) =>
      !q.2.1.1 && decide (q.2.1.2.2.1.headD 0 = -1)) :=
    Primrec.and.comp (Primrec.not.comp (Primrec.fst.comp hat_))
      (Primrec.eq.decide.comp
        (primrec_list_headD_zero.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hat_))))
        (Primrec.const (-1 : ℤ)))
  have hpair : Primrec (fun q : Conj × (Atom × List (List ℤ × ℤ)) =>
      (q.2.1.2.2.1.tail, q.2.1.2.2.2)) :=
    Primrec.pair (Primrec.list_tail.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hat_))))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hat_)))
  have hcons := Primrec.list_cons.comp hpair (Primrec.snd.comp Primrec.snd)
  have hstep : Primrec₂ (fun (_ : Conj) (q : Atom × List (List ℤ × ℤ)) =>
      if (!q.1.1 && decide (q.1.2.2.1.headD 0 = -1)) = true then
        (q.1.2.2.1.tail, q.1.2.2.2) :: q.2
      else q.2) := by
    change Primrec (fun p : Conj × (Atom × List (List ℤ × ℤ)) =>
      if (!p.2.1.1 && decide (p.2.1.2.2.1.headD 0 = -1)) = true then
        (p.2.1.2.2.1.tail, p.2.1.2.2.2) :: p.2.2
      else p.2.2)
    refine (Primrec.cond hcond hcons (Primrec.snd.comp Primrec.snd)).of_eq fun p => ?_
    cases (!p.2.1.1 && decide (p.2.1.2.2.1.headD 0 = -1)) <;> rfl
  exact Primrec.list_foldr (Primrec.id (α := Conj)) (Primrec.const ([] : List (List ℤ × ℤ))) hstep

private def substAtom (la : List ℤ) (lc : ℤ) (j : ℕ) (at_ : Atom) : Atom :=
  let a0 := at_.2.2.1.headD 0
  let tl := at_.2.2.1.tail
  (at_.1, at_.2.1, addList (scaleList a0 la) tl, a0 * (lc + (j : ℤ)) + at_.2.2.2)

private lemma evalAtom_substAtom (la : List ℤ) (lc : ℤ) (j : ℕ) (at_ : Atom) (ρ : List ℤ) :
    evalAtom ρ (substAtom la lc j at_) ↔ evalAtom ((dot la ρ + lc + (j : ℤ)) :: ρ) at_ := by
  rcases at_ with ⟨isDvd, m, a, c⟩
  simp only [substAtom, evalAtom, dot_addList, dot_scaleList, dot_head_tail]
  have hrew : a.headD 0 * dot la ρ + dot a.tail ρ + (a.headD 0 * (lc + ↑j) + c) =
      a.headD 0 * (dot la ρ + lc + ↑j) + dot a.tail ρ + c := by ring
  rw [hrew]

private lemma primrec_substAtom :
    Primrec (fun q : ((List ℤ × ℤ) × ℕ) × Atom => substAtom q.1.1.1 q.1.1.2 q.1.2 q.2) := by
  unfold substAtom
  have hla : Primrec (fun q : ((List ℤ × ℤ) × ℕ) × Atom => q.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hlc : Primrec (fun q : ((List ℤ × ℤ) × ℕ) × Atom => q.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hj : Primrec (fun q : ((List ℤ × ℤ) × ℕ) × Atom => ((q.1.2 : ℕ) : ℤ)) :=
    primrec_int_natCast.comp (Primrec.snd.comp Primrec.fst)
  have hb : Primrec (fun q : ((List ℤ × ℤ) × ℕ) × Atom => q.2.1) := Primrec.fst.comp Primrec.snd
  have hm : Primrec (fun q : ((List ℤ × ℤ) × ℕ) × Atom => q.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ha : Primrec (fun q : ((List ℤ × ℤ) × ℕ) × Atom => q.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hc : Primrec (fun q : ((List ℤ × ℤ) × ℕ) × Atom => q.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have ha0 := primrec_list_headD_zero.comp ha
  have htl := Primrec.list_tail.comp ha
  exact Primrec.pair hb (Primrec.pair hm
    (Primrec.pair (primrec_addList.comp (primrec_scaleList.comp ha0 hla) htl)
      (primrec_int_add.comp (primrec_int_mul.comp ha0 (primrec_int_add.comp hlc hj)) hc)))

private def substMinusInfAtom (j : ℕ) (at_ : Atom) : Atom :=
  if !at_.1 && decide (at_.2.2.1.headD 0 = 1) then
    (false, 0, [], 0)
  else
    substAtom [] 0 j at_

private lemma primrec_substMinusInfAtom : Primrec₂ substMinusInfAtom := by
  change Primrec (fun q : ℕ × Atom => substMinusInfAtom q.1 q.2)
  have hcond : Primrec (fun q : ℕ × Atom => !q.2.1 && decide (q.2.2.2.1.headD 0 = 1)) :=
    Primrec.and.comp (Primrec.not.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.eq.decide.comp
        (primrec_list_headD_zero.comp
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
        (Primrec.const (1 : ℤ)))
  have hsub : Primrec (fun q : ℕ × Atom => substAtom [] 0 q.1 q.2) :=
    primrec_substAtom.comp
      (Primrec.pair (Primrec.pair (Primrec.const (([] : List ℤ), (0 : ℤ))) Primrec.fst) Primrec.snd)
  refine (Primrec.cond hcond (Primrec.const (false, 0, ([] : List ℤ), (0 : ℤ))) hsub).of_eq fun q => ?_
  dsimp only [substMinusInfAtom]
  cases (!q.2.1 && decide (q.2.2.2.1.headD 0 = 1)) <;> rfl

private def elimOneNorm (C' : Conj) : DNF :=
  let D := dvdPeriod C'
  let B := lowerBounds C'
  if B.isEmpty then
    (List.range D).map fun j => C'.map (substMinusInfAtom j)
  else
    B.flatMap fun lb => (List.range D).map fun j => C'.map (substAtom lb.1 lb.2 j)

private lemma primrec_elimOneNorm : Primrec elimOneNorm := by
  have hD : Primrec (fun C' : Conj => List.range (dvdPeriod C')) :=
    Primrec.list_range.comp primrec_dvdPeriod
  have hB := primrec_lowerBounds
  have hisEmpty : Primrec (fun C' : Conj => (lowerBounds C').isEmpty) :=
    (Primrec.eq.decide.comp (Primrec.list_length.comp hB) (Primrec.const 0)).of_eq fun C' => by
      cases lowerBounds C' <;> simp
  have htrue : Primrec (fun C' : Conj =>
      (List.range (dvdPeriod C')).map fun j => C'.map (substMinusInfAtom j)) := by
    refine Primrec.list_map hD ?_
    have hmap : Primrec (fun q : Conj × ℕ => q.1.map (substMinusInfAtom q.2)) :=
      Primrec.list_map Primrec.fst
        (primrec_substMinusInfAtom.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
    exact hmap.to₂
  have hfalse : Primrec (fun C' : Conj =>
      (lowerBounds C').flatMap fun lb =>
        (List.range (dvdPeriod C')).map fun j => C'.map (substAtom lb.1 lb.2 j)) := by
    refine Primrec.list_flatMap hB ?_
    have hD1 : Primrec (fun q : Conj × (List ℤ × ℤ) => List.range (dvdPeriod q.1)) :=
      hD.comp Primrec.fst
    have hinner : Primrec₂ (fun (q : Conj × (List ℤ × ℤ)) (j : ℕ) =>
        q.1.map (substAtom q.2.1 q.2.2 j)) := by
      have hC' : Primrec (fun r : (Conj × (List ℤ × ℤ)) × ℕ => r.1.1) :=
        Primrec.fst.comp Primrec.fst
      have hsub : Primrec₂ (fun (r : (Conj × (List ℤ × ℤ)) × ℕ) (at_ : Atom) =>
          substAtom r.1.2.1 r.1.2.2 r.2 at_) :=
        (primrec_substAtom.comp
          (Primrec.pair
            (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
              (Primrec.snd.comp Primrec.fst))
            Primrec.snd)).to₂
      exact (Primrec.list_map hC' hsub).to₂
    exact (Primrec.list_map hD1 hinner).to₂
  refine (Primrec.cond hisEmpty htrue hfalse).of_eq fun C' => ?_
  dsimp only [elimOneNorm]
  cases (lowerBounds C').isEmpty <;> rfl

private lemma evalDNF_elimOneNorm {C' : Conj}
    (hnorm : ∀ at_ ∈ C',
      (at_.1 = true → at_.2.2.1.headD 0 = 0 ∨ at_.2.2.1.headD 0 = 1) ∧
      (at_.1 = false → at_.2.2.1.headD 0 = 0 ∨ at_.2.2.1.headD 0 = 1 ∨ at_.2.2.1.headD 0 = -1))
    (ρ : List ℤ) :
    evalDNF ρ (elimOneNorm C') ↔ ∃ x : ℤ, evalConj (x :: ρ) C' := by
  set D := dvdPeriod C'
  have hDpos : 1 ≤ D := dvdPeriod_pos C'
  have hDzpos : (0 : ℤ) < (D : ℤ) := by omega
  set B := lowerBounds C'
  unfold elimOneNorm
  dsimp only
  change evalDNF ρ (if B.isEmpty then (List.range D).map (fun j => C'.map (substMinusInfAtom j))
    else B.flatMap (fun lb => (List.range D).map (fun j => C'.map (substAtom lb.1 lb.2 j)))) ↔ _
  by_cases hB : B.isEmpty = true
  · rw [if_pos hB]
    have hnoLB : ∀ at_ ∈ C', at_.1 = false → at_.2.2.1.headD 0 ≠ -1 := by
      intro at_ hat_ hle hm1
      have hmemB : (at_.2.2.1.tail, at_.2.2.2) ∈ B :=
        (mem_lowerBounds_iff C' _).mpr ⟨at_, hat_, hle, hm1, rfl⟩
      cases hBeq : B with
      | nil => rw [hBeq] at hmemB; cases hmemB
      | cons _ _ => rw [hBeq] at hB; simp at hB
    constructor
    · rintro ⟨_, hmem, hall⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hmem
      have hbound : ∃ M : ℤ, ∀ at_ ∈ C', at_.1 = false → at_.2.2.1.headD 0 = 1 →
          M ≤ -(dot at_.2.2.1.tail ρ + at_.2.2.2) := by
        have haux : ∀ L : Conj, ∀ at_ ∈ L,
            L.foldr (fun at_ acc => min acc (-(dot at_.2.2.1.tail ρ + at_.2.2.2))) 0 ≤
              -(dot at_.2.2.1.tail ρ + at_.2.2.2) := by
          intro L
          induction L with
          | nil => intro _ h; cases h
          | cons a tl ih =>
            intro at_ hat_
            simp only [List.foldr_cons]
            rcases List.mem_cons.mp hat_ with rfl | htl
            · exact min_le_right _ _
            · exact (min_le_left _ _).trans (ih at_ htl)
        exact ⟨_, fun at_ hat_ _ _ => haux C' at_ hat_⟩
      obtain ⟨M, hM⟩ := hbound
      set K : ℤ := max 0 ((j : ℤ) - M)
      refine ⟨(j : ℤ) - K * (D : ℤ), fun at_ hat_ => ?_⟩
      have hsub := hall (substMinusInfAtom j at_) (List.mem_map.mpr ⟨at_, hat_, rfl⟩)
      rcases hnorm at_ hat_ with ⟨hd_norm, hl_norm⟩
      cases his : at_.1 with
      | false =>
        rcases hl_norm his with h0 | h1 | hm1
        · have hne1 : at_.2.2.1.headD 0 ≠ 1 := by omega
          have hsub' : substMinusInfAtom j at_ = substAtom [] 0 j at_ := by
            unfold substMinusInfAtom; rw [his, decide_eq_false hne1]; rfl
          rw [hsub', evalAtom_substAtom] at hsub
          simp only [evalAtom, his, Bool.false_eq_true, ↓reduceIte, dot_head_tail, h0, zero_mul,
            zero_add] at hsub ⊢
          exact hsub
        · have hleM := hM at_ hat_ his h1
          have hKD : K * (D : ℤ) ≥ (j : ℤ) - M := by
            have hK0 : 0 ≤ K := le_max_left _ _
            have hK1 : (j : ℤ) - M ≤ K := le_max_right _ _
            nlinarith
          simp only [evalAtom, his, Bool.false_eq_true, ↓reduceIte, dot_head_tail, h1, one_mul]
          linarith
        · exact absurd hm1 (hnoLB at_ hat_ his)
      | true =>
        have hsub' : substMinusInfAtom j at_ = substAtom [] 0 j at_ := by
          unfold substMinusInfAtom; rw [his]; rfl
        rw [hsub', evalAtom_substAtom] at hsub
        rcases hd_norm his with h0 | h1
        · simp only [evalAtom, his, ↓reduceIte, dot_head_tail, h0, zero_mul, zero_add] at hsub ⊢
          exact hsub
        · have hdivD : ((max at_.2.1 1 : ℕ) : ℤ) ∣ (D : ℤ) :=
            Int.natCast_dvd_natCast.mpr (dvd_dvdPeriod hat_ his h1)
          simp only [evalAtom, his, ↓reduceIte, dot_head_tail, h1, one_mul, dot_nil_left,
            zero_add] at hsub ⊢
          have hrew : ((j : ℤ) - K * (D : ℤ)) + dot at_.2.2.1.tail ρ + at_.2.2.2 =
              ((j : ℤ) + dot at_.2.2.1.tail ρ + at_.2.2.2) - K * (D : ℤ) := by ring
          rw [hrew]
          exact dvd_sub hsub (dvd_mul_of_dvd_right hdivD K)
    · rintro ⟨x, hx⟩
      set j : ℕ := (x % (D : ℤ)).toNat
      have hj_lt : j < D := by
        have h1 : 0 ≤ x % (D : ℤ) := Int.emod_nonneg x (ne_of_gt hDzpos)
        have h2 : x % (D : ℤ) < (D : ℤ) := Int.emod_lt_of_pos x hDzpos
        omega
      have hj_eq : (j : ℤ) = x % (D : ℤ) := by
        have h1 : 0 ≤ x % (D : ℤ) := Int.emod_nonneg x (ne_of_gt hDzpos)
        omega
      refine ⟨C'.map (substMinusInfAtom j), List.mem_map.mpr ⟨j, List.mem_range.mpr hj_lt, rfl⟩, ?_⟩
      intro y hy
      obtain ⟨at_, hat_, rfl⟩ := List.mem_map.mp hy
      have hat_ev := hx at_ hat_
      rcases hnorm at_ hat_ with ⟨hd_norm, hl_norm⟩
      cases his : at_.1 with
      | false =>
        rcases hl_norm his with h0 | h1 | hm1
        · have hne1 : at_.2.2.1.headD 0 ≠ 1 := by omega
          have hsub' : substMinusInfAtom j at_ = substAtom [] 0 j at_ := by
            unfold substMinusInfAtom; rw [his, decide_eq_false hne1]; rfl
          rw [hsub', evalAtom_substAtom]
          simp only [evalAtom, his, Bool.false_eq_true, ↓reduceIte, dot_head_tail, h0, zero_mul,
            zero_add] at hat_ev ⊢
          exact hat_ev
        · have hsub' : substMinusInfAtom j at_ = (false, 0, [], 0) := by
            unfold substMinusInfAtom; rw [his, decide_eq_true h1]; rfl
          rw [hsub']
          simp [evalAtom, dot_nil_left]
        · exact absurd hm1 (hnoLB at_ hat_ his)
      | true =>
        have hsub' : substMinusInfAtom j at_ = substAtom [] 0 j at_ := by
          unfold substMinusInfAtom; rw [his]; rfl
        rw [hsub', evalAtom_substAtom]
        rcases hd_norm his with h0 | h1
        · simp only [evalAtom, his, ↓reduceIte, dot_head_tail, h0, zero_mul, zero_add] at hat_ev ⊢
          exact hat_ev
        · have hdivD : ((max at_.2.1 1 : ℕ) : ℤ) ∣ (D : ℤ) :=
            Int.natCast_dvd_natCast.mpr (dvd_dvdPeriod hat_ his h1)
          simp only [evalAtom, his, ↓reduceIte, dot_head_tail, h1, one_mul, dot_nil_left,
            zero_add] at hat_ev ⊢
          have hmod : (D : ℤ) * (x / (D : ℤ)) + (j : ℤ) = x := by
            rw [hj_eq]; exact Int.mul_ediv_add_emod x D
          have hrew : (j : ℤ) + dot at_.2.2.1.tail ρ + at_.2.2.2 =
              (x + dot at_.2.2.1.tail ρ + at_.2.2.2) - (D : ℤ) * (x / (D : ℤ)) := by linarith
          rw [hrew]
          exact dvd_sub hat_ev (dvd_mul_of_dvd_left hdivD _)
  · rw [if_neg hB]
    have hBne : B ≠ [] := by
      intro hnil; rw [hnil] at hB; simp at hB
    constructor
    · rintro ⟨_, hmem, hall⟩
      simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hmem
      obtain ⟨lb, _, j, _, rfl⟩ := hmem
      refine ⟨dot lb.1 ρ + lb.2 + (j : ℤ), fun at_ hat_ => ?_⟩
      have hsub := hall (substAtom lb.1 lb.2 j at_) (List.mem_map.mpr ⟨at_, hat_, rfl⟩)
      exact (evalAtom_substAtom lb.1 lb.2 j at_ ρ).mp hsub
    · rintro ⟨x, hx⟩
      have hmaxB : ∃ lb0 ∈ B, ∀ lb ∈ B, dot lb.1 ρ + lb.2 ≤ dot lb0.1 ρ + lb0.2 := by
        have haux : ∀ L : List (List ℤ × ℤ), L ≠ [] →
            ∃ lb0 ∈ L, ∀ lb ∈ L, dot lb.1 ρ + lb.2 ≤ dot lb0.1 ρ + lb0.2 := by
          intro L
          induction L with
          | nil => intro h; exact absurd rfl h
          | cons b tl ih =>
            intro _
            cases tl with
            | nil =>
              exact ⟨b, List.mem_cons_self, fun lb hlb => by rw [List.mem_singleton.mp hlb]⟩
            | cons b2 tl2 =>
              obtain ⟨m, hm_mem, hm_max⟩ := ih (by simp)
              by_cases hcmp : dot m.1 ρ + m.2 ≤ dot b.1 ρ + b.2
              · refine ⟨b, List.mem_cons_self, fun lb hlb => ?_⟩
                rcases List.mem_cons.mp hlb with rfl | htl
                · exact le_rfl
                · exact (hm_max lb htl).trans hcmp
              · refine ⟨m, List.mem_cons_of_mem _ hm_mem, fun lb hlb => ?_⟩
                rcases List.mem_cons.mp hlb with rfl | htl
                · omega
                · exact hm_max lb htl
        exact haux B hBne
      obtain ⟨lb0, hlb0_mem, hlb0_max⟩ := hmaxB
      set l0 := dot lb0.1 ρ + lb0.2
      have hl0_le_x : l0 ≤ x := by
        obtain ⟨at0, hat0_mem, hat0_le, hat0_m1, hlb0_eq⟩ := (mem_lowerBounds_iff C' lb0).mp hlb0_mem
        have h0 := hx at0 hat0_mem
        simp only [evalAtom, hat0_le, Bool.false_eq_true, ↓reduceIte, dot_head_tail, hat0_m1] at h0
        have hl0_eq : l0 = dot at0.2.2.1.tail ρ + at0.2.2.2 := by
          dsimp only [l0]; rw [hlb0_eq]
        linarith
      set q := (x - l0) / (D : ℤ)
      set j : ℕ := ((x - l0) % (D : ℤ)).toNat
      have hj_lt : j < D := by
        have h1 : 0 ≤ (x - l0) % (D : ℤ) := Int.emod_nonneg (x - l0) (ne_of_gt hDzpos)
        have h2 : (x - l0) % (D : ℤ) < (D : ℤ) := Int.emod_lt_of_pos (x - l0) hDzpos
        omega
      have hj_eq : (j : ℤ) = (x - l0) % (D : ℤ) := by
        have h1 : 0 ≤ (x - l0) % (D : ℤ) := Int.emod_nonneg (x - l0) (ne_of_gt hDzpos)
        omega
      have hq_nonneg : 0 ≤ q := Int.ediv_nonneg (by omega) (le_of_lt hDzpos)
      set y := l0 + (j : ℤ)
      have hy_eq : y = x - (D : ℤ) * q := by
        have hmod := Int.mul_ediv_add_emod (x - l0) (D : ℤ)
        dsimp only [y, q]; linarith
      have hy_le_x : y ≤ x := by nlinarith
      refine ⟨C'.map (substAtom lb0.1 lb0.2 j), ?_, ?_⟩
      · simp only [List.mem_flatMap, List.mem_map, List.mem_range]
        exact ⟨lb0, hlb0_mem, j, hj_lt, rfl⟩
      · intro z hz
        obtain ⟨at_, hat_, rfl⟩ := List.mem_map.mp hz
        rw [evalAtom_substAtom]
        change evalAtom (y :: ρ) at_
        have hat_ev := hx at_ hat_
        rcases hnorm at_ hat_ with ⟨hd_norm, hl_norm⟩
        cases his : at_.1 with
        | false =>
          rcases hl_norm his with h0 | h1 | hm1
          · simp only [evalAtom, his, Bool.false_eq_true, ↓reduceIte, dot_head_tail, h0, zero_mul,
              zero_add] at hat_ev ⊢
            exact hat_ev
          · simp only [evalAtom, his, Bool.false_eq_true, ↓reduceIte, dot_head_tail, h1, one_mul] at hat_ev ⊢
            linarith
          · have hmemB : (at_.2.2.1.tail, at_.2.2.2) ∈ B :=
              (mem_lowerBounds_iff C' _).mpr ⟨at_, hat_, his, hm1, rfl⟩
            have hle_l0 := hlb0_max _ hmemB
            simp only [evalAtom, his, Bool.false_eq_true, ↓reduceIte, dot_head_tail, hm1]
            dsimp only [y, l0] at *; linarith
        | true =>
          rcases hd_norm his with h0 | h1
          · simp only [evalAtom, his, ↓reduceIte, dot_head_tail, h0, zero_mul, zero_add] at hat_ev ⊢
            exact hat_ev
          · have hdivD : ((max at_.2.1 1 : ℕ) : ℤ) ∣ (D : ℤ) :=
              Int.natCast_dvd_natCast.mpr (dvd_dvdPeriod hat_ his h1)
            simp only [evalAtom, his, ↓reduceIte, dot_head_tail, h1, one_mul] at hat_ev ⊢
            have hrew : y + dot at_.2.2.1.tail ρ + at_.2.2.2 =
                (x + dot at_.2.2.1.tail ρ + at_.2.2.2) - (D : ℤ) * q := by linarith
            rw [hrew]
            exact dvd_sub hat_ev (dvd_mul_of_dvd_left hdivD q)

private def elimOneConj (C : Conj) : DNF :=
  elimOneNorm (normalizeConj C)

private lemma evalDNF_elimOneConj (C : Conj) (ρ : List ℤ) :
    evalDNF ρ (elimOneConj C) ↔ ∃ x : ℤ, evalConj (x :: ρ) C := by
  rw [elimOneConj, evalDNF_elimOneNorm, ← exists_normalizeConj]
  intro at' hat'
  simp only [normalizeConj, List.mem_cons, List.mem_map] at hat'
  rcases hat' with rfl | ⟨at_, _, rfl⟩
  · simp
  · exact scaleAtomForX_norm _ _

private def elimOneDNF (D : DNF) : DNF :=
  D.flatMap elimOneConj

private lemma evalDNF_elimOneDNF (D : DNF) (ρ : List ℤ) :
    evalDNF ρ (elimOneDNF D) ↔ ∃ x : ℤ, evalDNF (x :: ρ) D := by
  simp only [elimOneDNF, evalDNF, List.mem_flatMap]
  constructor
  · rintro ⟨c, ⟨C, hC, hc⟩, hev⟩
    obtain ⟨x, hx⟩ := (evalDNF_elimOneConj C ρ).mp ⟨c, hc, hev⟩
    exact ⟨x, C, hC, hx⟩
  · rintro ⟨x, C, hC, hx⟩
    obtain ⟨c, hc, hev⟩ := (evalDNF_elimOneConj C ρ).mpr ⟨x, hx⟩
    exact ⟨c, ⟨C, hC, hc⟩, hev⟩

private lemma primrec_elimOneDNF : Primrec elimOneDNF :=
  Primrec.list_flatMap (Primrec.id (α := DNF))
    ((primrec_elimOneNorm.comp primrec_normalizeConj).comp Primrec.snd).to₂

private def elimMany : ℕ → DNF → DNF
  | 0, D => D
  | k + 1, D => elimOneDNF (elimMany k D)

private lemma evalDNF_elimMany (k : ℕ) (D : DNF) (ρ : List ℤ) :
    evalDNF ρ (elimMany k D) ↔ ∃ xs : List ℤ, xs.length = k ∧ evalDNF (xs ++ ρ) D := by
  induction k generalizing ρ with
  | zero =>
    simp only [elimMany, List.length_eq_zero_iff, exists_eq_left, List.nil_append]
  | succ k ih =>
    rw [elimMany, evalDNF_elimOneDNF]
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨xs, hlen, hxs⟩ := (ih (x :: ρ)).mp hx
      refine ⟨xs ++ [x], by simp [hlen], ?_⟩
      simpa [List.append_assoc] using hxs
    · rintro ⟨ys, hlen, hys⟩
      have hne : ys ≠ [] := by intro h; simp [h] at hlen
      set xs := ys.dropLast
      set x := ys.getLast hne
      have hys_eq : ys = xs ++ [x] := (List.dropLast_append_getLast hne).symm
      have hlen_xs : xs.length = k := by
        have := congrArg List.length hys_eq
        simp at this; omega
      refine ⟨x, (ih (x :: ρ)).mpr ⟨xs, hlen_xs, ?_⟩⟩
      rw [hys_eq, List.append_assoc] at hys
      simpa using hys

private lemma primrec_elimMany : Primrec₂ elimMany := by
  change Primrec (fun p : ℕ × DNF => elimMany p.1 p.2)
  have hrec : Primrec (fun p : ℕ × DNF =>
      Nat.rec (motive := fun _ => DNF) p.2 (fun _ acc => elimOneDNF acc) p.1) :=
    Primrec.nat_rec' Primrec.fst Primrec.snd
      (primrec_elimOneDNF.comp (Primrec.snd.comp Primrec.snd)).to₂
  refine hrec.of_eq fun ⟨k, D⟩ => ?_
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg elimOneDNF ih

/- ### Part 5: Encoding the 4 BVAS semilinear invariant clauses -/

private abbrev LinPair := List ℕ × List (List ℕ)
private abbrev RawBVAS := (ℕ × List (List ℤ) × List (List ℤ) × List (List ℤ) × List ℤ) × List LinPair

private def nonnegList (l : List ℤ) : Bool :=
  listAll (fun z => decide ((0 : ℤ) ≤ z)) l

private lemma nonnegList_eq_true_iff (l : List ℤ) :
    nonnegList l = true ↔ ∀ z ∈ l, (0 : ℤ) ≤ z := by
  simpa [nonnegList] using listAll_eq_true (fun z : ℤ => decide ((0 : ℤ) ≤ z)) l

private lemma primrec_nonnegList : Primrec nonnegList :=
  primrec_listAll (Primrec.id (α := List ℤ)) (primrec_int_nonneg.comp Primrec.snd).to₂

private def nonnegVars (m : ℕ) : Conj :=
  (List.range m).map fun j => (false, 0, unitVec j (-1), 0)

private lemma primrec_nonnegVars : Primrec nonnegVars := by
  unfold nonnegVars
  refine Primrec.list_map Primrec.list_range ?_
  exact (Primrec.pair (Primrec.const false)
    (Primrec.pair (Primrec.const 0)
      (Primrec.pair (primrec_unitVec.comp Primrec.snd (Primrec.const (-1 : ℤ)))
        (Primrec.const (0 : ℤ))))).to₂

private lemma evalConj_nonnegVars (m : ℕ) (xs ρ : List ℤ) (hlen : xs.length = m) :
    evalConj (xs ++ ρ) (nonnegVars m) ↔ ∀ j : Fin m, (0 : ℤ) ≤ xs.getD j.1 0 := by
  simp only [nonnegVars, evalConj, List.mem_map, List.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, evalAtom, Bool.false_eq_true, ↓reduceIte, dot_unitVec, add_zero]
  constructor
  · intro h j
    have hj := h j.1 j.2
    have hget : (xs ++ ρ).getD j.1 0 = xs.getD j.1 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : j.1 < xs.length)]
    rw [hget] at hj; omega
  · intro h j hj
    have hget : (xs ++ ρ).getD j 0 = xs.getD j 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : j < xs.length)]
    rw [hget]
    have hfin : (0 : ℤ) ≤ xs.getD j 0 := h ⟨j, hj⟩
    omega

private lemma evalConj_nonnegVars_nil (m : ℕ) (xs : List ℤ) (hlen : xs.length = m) :
    evalConj xs (nonnegVars m) ↔ ∀ j : Fin m, (0 : ℤ) ≤ xs.getD j.1 0 := by
  simpa using evalConj_nonnegVars m xs [] hlen

private def periodCoeffs (ps : List (List ℕ)) (i : ℕ) : List ℤ :=
  ps.map fun per => ((per.getD i 0 : ℕ) : ℤ)

private lemma primrec_periodCoeffs : Primrec₂ periodCoeffs := by
  change Primrec (fun p : List (List ℕ) × ℕ => periodCoeffs p.1 p.2)
  unfold periodCoeffs
  refine Primrec.list_map (Primrec.fst (α := List (List ℕ)) (β := ℕ)) ?_
  exact (primrec_int_natCast.comp
    ((Primrec.list_getD (0 : ℕ)).comp Primrec.snd (Primrec.snd.comp Primrec.fst))).to₂

private lemma dot_periodCoeffs (ps : List (List ℕ)) (i : ℕ) (xs : List ℤ) :
    dot (periodCoeffs ps i) xs =
      ∑ j : Fin ps.length, xs.getD j.1 0 * (((ps[j]).getD i 0 : ℕ) : ℤ) := by
  rw [dot_eq_sum_range]
  have hlen' : (periodCoeffs ps i).length = ps.length := by simp [periodCoeffs]
  rw [hlen', ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hget : (periodCoeffs ps i).getD j.1 0 = (((ps[j]).getD i 0 : ℕ) : ℤ) := by
    simp [periodCoeffs, List.getD_eq_getElem?_getD]
  rw [hget, mul_comm]

private def eqAtomPair (a : List ℤ) (c : ℤ) : Conj :=
  [(false, 0, a, c), (false, 0, scaleList (-1) a, -c)]

private lemma evalConj_eqAtomPair (ρ a : List ℤ) (c : ℤ) :
    evalConj ρ (eqAtomPair a c) ↔ dot a ρ + c = 0 := by
  simp only [eqAtomPair, evalConj, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, evalAtom, Bool.false_eq_true, ↓reduceIte, dot_scaleList]
  omega

private lemma primrec_eqAtomPair : Primrec₂ eqAtomPair := by
  change Primrec (fun q : List ℤ × ℤ => eqAtomPair q.1 q.2)
  unfold eqAtomPair
  have h1 : Primrec (fun q : List ℤ × ℤ => (false, 0, q.1, q.2)) :=
    Primrec.pair (Primrec.const false) (Primrec.pair (Primrec.const 0) (Primrec.id (α := List ℤ × ℤ)))
  have h2 : Primrec (fun q : List ℤ × ℤ => (false, 0, scaleList (-1) q.1, -q.2)) :=
    Primrec.pair (Primrec.const false) (Primrec.pair (Primrec.const 0)
      (Primrec.pair (primrec_scaleList.comp (Primrec.const (-1 : ℤ)) (Primrec.fst (α := List ℤ) (β := ℤ)))
        (primrec_int_neg.comp (Primrec.snd (α := List ℤ) (β := ℤ)))))
  exact Primrec.list_cons.comp h1 (Primrec.list_cons.comp h2 (Primrec.const ([] : Conj)))

/- #### Clause 1 & 4: `checkMem d S v` -/

private def memConj (d : ℕ) (v : List ℤ) (bp : LinPair) : Conj :=
  nonnegVars bp.2.length ++
    (List.range d).flatMap fun i =>
      eqAtomPair (periodCoeffs bp.2 i) (((bp.1.getD i 0 : ℕ) : ℤ) - v.getD i 0)

private lemma primrec_memConj :
    Primrec (fun q : (ℕ × List ℤ) × LinPair => memConj q.1.1 q.1.2 q.2) := by
  unfold memConj
  have hnn : Primrec (fun q : (ℕ × List ℤ) × LinPair => nonnegVars q.2.2.length) :=
    primrec_nonnegVars.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))
  have hrange : Primrec (fun q : (ℕ × List ℤ) × LinPair => List.range q.1.1) :=
    Primrec.list_range.comp (Primrec.fst.comp Primrec.fst)
  have hflat : Primrec (fun q : (ℕ × List ℤ) × LinPair =>
      (List.range q.1.1).flatMap fun i =>
        eqAtomPair (periodCoeffs q.2.2 i) (((q.2.1.getD i 0 : ℕ) : ℤ) - q.1.2.getD i 0)) := by
    refine Primrec.list_flatMap hrange ?_
    have hcoeff : Primrec (fun r : ((ℕ × List ℤ) × LinPair) × ℕ => periodCoeffs r.1.2.2 r.2) :=
      primrec_periodCoeffs.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
    have hconst : Primrec (fun r : ((ℕ × List ℤ) × LinPair) × ℕ =>
        ((r.1.2.1.getD r.2 0 : ℕ) : ℤ) - r.1.1.2.getD r.2 0) :=
      primrec_int_sub.comp
        (primrec_int_natCast.comp ((Primrec.list_getD (0 : ℕ)).comp
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))
        ((Primrec.list_getD (0 : ℤ)).comp
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
    exact (primrec_eqAtomPair.comp hcoeff hconst).to₂
  exact Primrec.list_append.comp hnn hflat

private def checkMem (d : ℕ) (S : List LinPair) (v : List ℤ) : Bool :=
  listAny (fun bp => evalClosedDNF (elimMany bp.2.length [memConj d v bp])) S

private lemma primrec_checkMem :
    Primrec (fun q : ℕ × List LinPair × List ℤ => checkMem q.1 q.2.1 q.2.2) := by
  unfold checkMem
  have hS : Primrec (fun q : ℕ × List LinPair × List ℤ => q.2.1) :=
    Primrec.fst.comp Primrec.snd
  refine primrec_listAny hS ?_
  have hlen : Primrec (fun r : (ℕ × List LinPair × List ℤ) × LinPair => r.2.2.length) :=
    Primrec.list_length.comp (Primrec.snd.comp Primrec.snd)
  have hconj : Primrec (fun r : (ℕ × List LinPair × List ℤ) × LinPair =>
      [memConj r.1.1 r.1.2.2 r.2]) :=
    Primrec.list_cons.comp
      (primrec_memConj.comp
        (Primrec.pair (Primrec.pair (Primrec.fst.comp Primrec.fst)
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd))
      (Primrec.const ([] : DNF))
  exact (primrec_evalClosedDNF.comp (primrec_elimMany.comp hlen hconj)).to₂

private lemma checkMem_iff (d : ℕ) (S : List LinPair) (v : List ℤ) :
    checkMem d S v = true ↔
      ∃ bp ∈ S, ∃ c : Fin bp.2.length → ℕ,
        ∀ i : Fin d, v.getD i.1 0 = (bp.1.getD i.1 0 : ℤ) +
          ∑ j : Fin bp.2.length, (c j : ℤ) * (((bp.2[j]).getD i.1 0 : ℕ) : ℤ) := by
  rw [checkMem, listAny_eq_true]
  refine exists_congr fun bp => and_congr_right fun _ => ?_
  rw [evalClosedDNF_iff, evalDNF_elimMany]
  simp only [evalDNF, List.mem_singleton, exists_eq_left, List.append_nil]
  constructor
  · rintro ⟨xs, hlen, hxs⟩
    have hnn : ∀ j : Fin bp.2.length, (0 : ℤ) ≤ xs.getD j.1 0 :=
      (evalConj_nonnegVars_nil bp.2.length xs hlen).mp fun a ha =>
        hxs a (List.mem_append_left _ ha)
    refine ⟨fun j => (xs.getD j.1 0).toNat, fun i => ?_⟩
    have heq0 : dot (periodCoeffs bp.2 i.1) xs + (((bp.1.getD i.1 0 : ℕ) : ℤ) - v.getD i.1 0) = 0 := by
      refine (evalConj_eqAtomPair xs _ _).mp fun a ha =>
        hxs a (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i.1, List.mem_range.mpr i.2, ha⟩))
    rw [dot_periodCoeffs bp.2 i.1 xs] at heq0
    have hcast : ∀ j : Fin bp.2.length, (((xs.getD j.1 0).toNat : ℕ) : ℤ) = xs.getD j.1 0 :=
      fun j => Int.toNat_of_nonneg (hnn j)
    simp_rw [hcast]
    linarith
  · rintro ⟨c, hc⟩
    set xs : List ℤ := List.ofFn (fun j : Fin bp.2.length => (c j : ℤ))
    have hlen : xs.length = bp.2.length := by simp [xs]
    have hget : ∀ j : Fin bp.2.length, xs.getD j.1 0 = (c j : ℤ) := by
      intro j; simp [xs, List.getD_eq_getElem?_getD]
    refine ⟨xs, hlen, fun a ha => ?_⟩
    rcases List.mem_append.mp ha with h1 | h2
    · exact ((evalConj_nonnegVars_nil bp.2.length xs hlen).mpr fun j => by
        rw [hget j]; exact Int.natCast_nonneg _) a h1
    · obtain ⟨i, hi, ha_eq⟩ := List.mem_flatMap.mp h2
      have hi' := List.mem_range.mp hi
      refine ((evalConj_eqAtomPair xs _ _).mpr ?_) a ha_eq
      rw [dot_periodCoeffs bp.2 i xs]
      simp_rw [hget]
      have hci := hc ⟨i, hi'⟩
      linarith

/- #### Clause 2: Unary closure -/

private def unaryMatchConj (d : ℕ) (bp1 : LinPair) (r : List ℤ) (bp2 : LinPair) : Conj :=
  nonnegVars bp2.2.length ++
    (List.range d).flatMap fun i =>
      eqAtomPair (periodCoeffs bp2.2 i ++ scaleList (-1) (periodCoeffs bp1.2 i))
        (((bp2.1.getD i 0 : ℕ) : ℤ) - ((bp1.1.getD i 0 : ℕ) : ℤ) - r.getD i 0)

private lemma primrec_unaryMatchConj :
    Primrec (fun q : ((ℕ × LinPair) × List ℤ) × LinPair =>
      unaryMatchConj q.1.1.1 q.1.1.2 q.1.2 q.2) := by
  unfold unaryMatchConj
  have hnn : Primrec (fun q : ((ℕ × LinPair) × List ℤ) × LinPair => nonnegVars q.2.2.length) :=
    primrec_nonnegVars.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))
  have hrange : Primrec (fun q : ((ℕ × LinPair) × List ℤ) × LinPair => List.range q.1.1.1) :=
    Primrec.list_range.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hflat : Primrec (fun q : ((ℕ × LinPair) × List ℤ) × LinPair =>
      (List.range q.1.1.1).flatMap fun i =>
        eqAtomPair (periodCoeffs q.2.2 i ++ scaleList (-1) (periodCoeffs q.1.1.2.2 i))
          (((q.2.1.getD i 0 : ℕ) : ℤ) - ((q.1.1.2.1.getD i 0 : ℕ) : ℤ) - q.1.2.getD i 0)) := by
    refine Primrec.list_flatMap hrange ?_
    have hc2 : Primrec (fun t : (((ℕ × LinPair) × List ℤ) × LinPair) × ℕ =>
        periodCoeffs t.1.2.2 t.2) :=
      primrec_periodCoeffs.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
    have hc1 : Primrec (fun t : (((ℕ × LinPair) × List ℤ) × LinPair) × ℕ =>
        scaleList (-1) (periodCoeffs t.1.1.1.2.2 t.2)) :=
      primrec_scaleList.comp (Primrec.const (-1 : ℤ))
        (primrec_periodCoeffs.comp
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
          Primrec.snd)
    have hcoeff := Primrec.list_append.comp hc2 hc1
    have hb2 : Primrec (fun t : (((ℕ × LinPair) × List ℤ) × LinPair) × ℕ =>
        ((t.1.2.1.getD t.2 0 : ℕ) : ℤ)) :=
      primrec_int_natCast.comp ((Primrec.list_getD (0 : ℕ)).comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
    have hb1 : Primrec (fun t : (((ℕ × LinPair) × List ℤ) × LinPair) × ℕ =>
        ((t.1.1.1.2.1.getD t.2 0 : ℕ) : ℤ)) :=
      primrec_int_natCast.comp ((Primrec.list_getD (0 : ℕ)).comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
        Primrec.snd)
    have hr : Primrec (fun t : (((ℕ × LinPair) × List ℤ) × LinPair) × ℕ => t.1.1.2.getD t.2 0) :=
      (Primrec.list_getD (0 : ℤ)).comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
    have hconst := primrec_int_sub.comp (primrec_int_sub.comp hb2 hb1) hr
    exact (primrec_eqAtomPair.comp hcoeff hconst).to₂
  exact Primrec.list_append.comp hnn hflat

private def unaryLhsConj (d : ℕ) (bp1 : LinPair) (r : List ℤ) : Conj :=
  nonnegVars bp1.2.length ++
    (List.range d).map fun i =>
      (false, 0, scaleList (-1) (periodCoeffs bp1.2 i),
        -((bp1.1.getD i 0 : ℕ) : ℤ) - r.getD i 0)

private lemma primrec_unaryLhsConj :
    Primrec (fun q : (ℕ × LinPair) × List ℤ => unaryLhsConj q.1.1 q.1.2 q.2) := by
  unfold unaryLhsConj
  have hnn : Primrec (fun q : (ℕ × LinPair) × List ℤ => nonnegVars q.1.2.2.length) :=
    primrec_nonnegVars.comp
      (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hrange : Primrec (fun q : (ℕ × LinPair) × List ℤ => List.range q.1.1) :=
    Primrec.list_range.comp (Primrec.fst.comp Primrec.fst)
  have hmap : Primrec (fun q : (ℕ × LinPair) × List ℤ =>
      (List.range q.1.1).map fun i =>
        (false, 0, scaleList (-1) (periodCoeffs q.1.2.2 i),
          -((q.1.2.1.getD i 0 : ℕ) : ℤ) - q.2.getD i 0)) := by
    refine Primrec.list_map hrange ?_
    have hc1 : Primrec (fun t : ((ℕ × LinPair) × List ℤ) × ℕ =>
        scaleList (-1) (periodCoeffs t.1.1.2.2 t.2)) :=
      primrec_scaleList.comp (Primrec.const (-1 : ℤ))
        (primrec_periodCoeffs.comp
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd)
    have hb1 : Primrec (fun t : ((ℕ × LinPair) × List ℤ) × ℕ =>
        -((t.1.1.2.1.getD t.2 0 : ℕ) : ℤ)) :=
      primrec_int_neg.comp (primrec_int_natCast.comp
        ((Primrec.list_getD (0 : ℕ)).comp
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd))
    have hr : Primrec (fun t : ((ℕ × LinPair) × List ℤ) × ℕ => t.1.2.getD t.2 0) :=
      (Primrec.list_getD (0 : ℤ)).comp (Primrec.snd.comp Primrec.fst) Primrec.snd
    exact (Primrec.pair (Primrec.const false)
      (Primrec.pair (Primrec.const 0)
        (Primrec.pair hc1 (primrec_int_sub.comp hb1 hr)))).to₂
  exact Primrec.list_append.comp hnn hmap

private def checkUnaryPair (d : ℕ) (S : List LinPair) (bp1 : LinPair) (r : List ℤ) : Bool :=
  let rhs := S.flatMap fun bp2 => elimMany bp2.2.length [unaryMatchConj d bp1 r bp2]
  !evalClosedDNF (elimMany bp1.2.length (andDNF [unaryLhsConj d bp1 r] (negDNF rhs)))

private lemma primrec_checkUnaryPair :
    Primrec (fun q : (ℕ × List LinPair) × (LinPair × List ℤ) =>
      checkUnaryPair q.1.1 q.1.2 q.2.1 q.2.2) := by
  unfold checkUnaryPair
  have hS : Primrec (fun q : (ℕ × List LinPair) × (LinPair × List ℤ) => q.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hrhs : Primrec (fun q : (ℕ × List LinPair) × (LinPair × List ℤ) =>
      q.1.2.flatMap fun bp2 => elimMany bp2.2.length [unaryMatchConj q.1.1 q.2.1 q.2.2 bp2]) := by
    refine Primrec.list_flatMap hS ?_
    have hlen : Primrec (fun t : ((ℕ × List LinPair) × (LinPair × List ℤ)) × LinPair =>
        t.2.2.length) :=
      Primrec.list_length.comp (Primrec.snd.comp Primrec.snd)
    have hconj : Primrec (fun t : ((ℕ × List LinPair) × (LinPair × List ℤ)) × LinPair =>
        [unaryMatchConj t.1.1.1 t.1.2.1 t.1.2.2 t.2]) :=
      Primrec.list_cons.comp
        (primrec_unaryMatchConj.comp
          (Primrec.pair
            (Primrec.pair (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
              (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
              (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
            Primrec.snd))
        (Primrec.const ([] : DNF))
    exact (primrec_elimMany.comp hlen hconj).to₂
  have hlhs : Primrec (fun q : (ℕ × List LinPair) × (LinPair × List ℤ) =>
      [unaryLhsConj q.1.1 q.2.1 q.2.2]) :=
    Primrec.list_cons.comp
      (primrec_unaryLhsConj.comp
        (Primrec.pair (Primrec.pair (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.snd)))
      (Primrec.const ([] : DNF))
  have hm1 : Primrec (fun q : (ℕ × List LinPair) × (LinPair × List ℤ) => q.2.1.2.length) :=
    Primrec.list_length.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  exact Primrec.not.comp (primrec_evalClosedDNF.comp
    (primrec_elimMany.comp hm1 (primrec_andDNF.comp hlhs (primrec_negDNF.comp hrhs))))

private lemma checkUnaryPair_iff (d : ℕ) (S : List LinPair) (bp1 : LinPair) (r : List ℤ) :
    checkUnaryPair d S bp1 r = true ↔
      ∀ c1 : Fin bp1.2.length → ℕ,
        let v : Fin d → ℤ := fun i =>
          (bp1.1.getD i.1 0 : ℤ) +
            ∑ j : Fin bp1.2.length, (c1 j : ℤ) * (((bp1.2[j]).getD i.1 0 : ℕ) : ℤ)
        (∀ i : Fin d, 0 ≤ v i + r.getD i.1 0) →
        ∃ bp2 ∈ S, ∃ c2 : Fin bp2.2.length → ℕ,
          ∀ i : Fin d, v i + r.getD i.1 0 = (bp2.1.getD i.1 0 : ℤ) +
            ∑ j : Fin bp2.2.length, (c2 j : ℤ) * (((bp2.2[j]).getD i.1 0 : ℕ) : ℤ) := by
  unfold checkUnaryPair
  simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, evalClosedDNF_iff, evalDNF_elimMany,
    List.append_nil, evalDNF_andDNF, evalDNF_negDNF]
  have hrhs_iff : ∀ xs1 : List ℤ, xs1.length = bp1.2.length →
      (evalDNF xs1 (S.flatMap fun bp2 => elimMany bp2.2.length [unaryMatchConj d bp1 r bp2]) ↔
        ∃ bp2 ∈ S, ∃ c2 : Fin bp2.2.length → ℕ,
          ∀ i : Fin d,
            (bp1.1.getD i.1 0 : ℤ) +
              (∑ j : Fin bp1.2.length, xs1.getD j.1 0 * (((bp1.2[j]).getD i.1 0 : ℕ) : ℤ)) +
              r.getD i.1 0 =
            (bp2.1.getD i.1 0 : ℤ) +
              ∑ j : Fin bp2.2.length, (c2 j : ℤ) * (((bp2.2[j]).getD i.1 0 : ℕ) : ℤ)) := by
    intro xs1 _
    simp only [evalDNF, List.mem_flatMap]
    constructor
    · rintro ⟨c, ⟨bp2, hbp2, hc⟩, hev⟩
      obtain ⟨xs2, hlen2, hxs2⟩ :=
        (evalDNF_elimMany bp2.2.length [unaryMatchConj d bp1 r bp2] xs1).mp ⟨c, hc, hev⟩
      simp only [evalDNF, List.mem_singleton, exists_eq_left] at hxs2
      have hnn2 : ∀ j : Fin bp2.2.length, (0 : ℤ) ≤ xs2.getD j.1 0 :=
        (evalConj_nonnegVars bp2.2.length xs2 xs1 hlen2).mp fun a ha =>
          hxs2 a (List.mem_append_left _ ha)
      refine ⟨bp2, hbp2, fun j => (xs2.getD j.1 0).toNat, fun i => ?_⟩
      have heq0 : dot (periodCoeffs bp2.2 i.1 ++ scaleList (-1) (periodCoeffs bp1.2 i.1)) (xs2 ++ xs1) +
          (((bp2.1.getD i.1 0 : ℕ) : ℤ) - ((bp1.1.getD i.1 0 : ℕ) : ℤ) - r.getD i.1 0) = 0 :=
        (evalConj_eqAtomPair (xs2 ++ xs1) _ _).mp fun a ha =>
          hxs2 a (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i.1, List.mem_range.mpr i.2, ha⟩))
      have hplen2 : (periodCoeffs bp2.2 i.1).length = xs2.length := by simp [periodCoeffs, hlen2]
      rw [dot_append hplen2, dot_scaleList, dot_periodCoeffs bp2.2 i.1 xs2,
        dot_periodCoeffs bp1.2 i.1 xs1] at heq0
      have hcast : ∀ j : Fin bp2.2.length, (((xs2.getD j.1 0).toNat : ℕ) : ℤ) = xs2.getD j.1 0 :=
        fun j => Int.toNat_of_nonneg (hnn2 j)
      simp_rw [hcast]
      linarith
    · rintro ⟨bp2, hbp2, c2, hc2⟩
      set xs2 : List ℤ := List.ofFn (fun j : Fin bp2.2.length => (c2 j : ℤ))
      have hlen2 : xs2.length = bp2.2.length := by simp [xs2]
      have hget2 : ∀ j : Fin bp2.2.length, xs2.getD j.1 0 = (c2 j : ℤ) := by
        intro j; simp [xs2, List.getD_eq_getElem?_getD]
      have hsat : evalDNF xs1 (elimMany bp2.2.length [unaryMatchConj d bp1 r bp2]) := by
        rw [evalDNF_elimMany]
        refine ⟨xs2, hlen2, unaryMatchConj d bp1 r bp2, List.mem_singleton_self _, fun a ha => ?_⟩
        rcases List.mem_append.mp ha with h1 | h2
        · exact ((evalConj_nonnegVars bp2.2.length xs2 xs1 hlen2).mpr fun j => by
            rw [hget2 j]; exact Int.natCast_nonneg _) a h1
        · obtain ⟨i, hi, ha_eq⟩ := List.mem_flatMap.mp h2
          have hi' := List.mem_range.mp hi
          refine ((evalConj_eqAtomPair (xs2 ++ xs1) _ _).mpr ?_) a ha_eq
          have hplen2 : (periodCoeffs bp2.2 i).length = xs2.length := by simp [periodCoeffs, hlen2]
          rw [dot_append hplen2, dot_scaleList, dot_periodCoeffs bp2.2 i xs2,
            dot_periodCoeffs bp1.2 i xs1]
          simp_rw [hget2]
          have hci := hc2 ⟨i, hi'⟩
          linarith
      obtain ⟨c, hc, hev⟩ := hsat
      exact ⟨c, ⟨bp2, hbp2, hc⟩, hev⟩
  have hlhs_iff : ∀ xs1 : List ℤ, xs1.length = bp1.2.length →
      (evalDNF xs1 [unaryLhsConj d bp1 r] ↔
        (∀ j : Fin bp1.2.length, (0 : ℤ) ≤ xs1.getD j.1 0) ∧
        (∀ i : Fin d, 0 ≤ (bp1.1.getD i.1 0 : ℤ) +
          (∑ j : Fin bp1.2.length, xs1.getD j.1 0 * (((bp1.2[j]).getD i.1 0 : ℕ) : ℤ)) +
          r.getD i.1 0)) := by
    intro xs1 hlen1
    simp only [evalDNF, List.mem_singleton, exists_eq_left, unaryLhsConj]
    constructor
    · intro h
      refine ⟨(evalConj_nonnegVars_nil bp1.2.length xs1 hlen1).mp fun a ha =>
          h a (List.mem_append_left _ ha), fun i => ?_⟩
      have hi := h _ (List.mem_append_right _ (List.mem_map.mpr ⟨i.1, List.mem_range.mpr i.2, rfl⟩))
      simp only [evalAtom, Bool.false_eq_true, ↓reduceIte, dot_scaleList,
        dot_periodCoeffs bp1.2 i.1 xs1] at hi
      linarith
    · rintro ⟨hnn, hpos⟩ a ha
      rcases List.mem_append.mp ha with h1 | h2
      · exact ((evalConj_nonnegVars_nil bp1.2.length xs1 hlen1).mpr hnn) a h1
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h2
        have hi' := List.mem_range.mp hi
        simp only [evalAtom, Bool.false_eq_true, ↓reduceIte, dot_scaleList,
          dot_periodCoeffs bp1.2 i xs1]
        have := hpos ⟨i, hi'⟩
        linarith
  constructor
  · intro hnot c1 hpos
    set xs1 : List ℤ := List.ofFn (fun j : Fin bp1.2.length => (c1 j : ℤ))
    have hlen1 : xs1.length = bp1.2.length := by simp [xs1]
    have hget1 : ∀ j : Fin bp1.2.length, xs1.getD j.1 0 = (c1 j : ℤ) := by
      intro j; simp [xs1, List.getD_eq_getElem?_getD]
    have hlhs : evalDNF xs1 [unaryLhsConj d bp1 r] := by
      rw [hlhs_iff xs1 hlen1]
      refine ⟨fun j => by rw [hget1 j]; exact Int.natCast_nonneg _, fun i => ?_⟩
      simp_rw [hget1]; exact hpos i
    have hrhs : evalDNF xs1 (S.flatMap fun bp2 => elimMany bp2.2.length [unaryMatchConj d bp1 r bp2]) := by
      by_contra hnr
      exact hnot ⟨xs1, hlen1, hlhs, hnr⟩
    obtain ⟨bp2, hbp2, c2, hc2⟩ := (hrhs_iff xs1 hlen1).mp hrhs
    refine ⟨bp2, hbp2, c2, fun i => ?_⟩
    have := hc2 i; simp_rw [hget1] at this; exact this
  · intro hall
    rintro ⟨xs1, hlen1, hlhs, hnr⟩
    obtain ⟨hnn1, hpos1⟩ := (hlhs_iff xs1 hlen1).mp hlhs
    have hcast1 : ∀ j : Fin bp1.2.length, (((xs1.getD j.1 0).toNat : ℕ) : ℤ) = xs1.getD j.1 0 :=
      fun j => Int.toNat_of_nonneg (hnn1 j)
    have hpos' : ∀ i : Fin d, 0 ≤ (bp1.1.getD i.1 0 : ℤ) +
        (∑ j : Fin bp1.2.length, (((xs1.getD j.1 0).toNat : ℕ) : ℤ) * (((bp1.2[j]).getD i.1 0 : ℕ) : ℤ)) +
        r.getD i.1 0 := by
      intro i; simp_rw [hcast1]; exact hpos1 i
    obtain ⟨bp2, hbp2, c2, hc2⟩ := hall (fun j => (xs1.getD j.1 0).toNat) hpos'
    apply hnr
    rw [hrhs_iff xs1 hlen1]
    refine ⟨bp2, hbp2, c2, fun i => ?_⟩
    have := hc2 i; simp_rw [hcast1] at this; exact this

/- #### Clause 3: Binary closure -/

private def binaryMatchConj (d : ℕ) (bp1 bp2 : LinPair) (r : List ℤ) (bp3 : LinPair) : Conj :=
  nonnegVars bp3.2.length ++
    (List.range d).flatMap fun i =>
      eqAtomPair
        (periodCoeffs bp3.2 i ++
          (scaleList (-1) (periodCoeffs bp1.2 i) ++ scaleList (-1) (periodCoeffs bp2.2 i)))
        (((bp3.1.getD i 0 : ℕ) : ℤ) - ((bp1.1.getD i 0 : ℕ) : ℤ) -
          ((bp2.1.getD i 0 : ℕ) : ℤ) - r.getD i 0)

private lemma primrec_binaryMatchConj :
    Primrec (fun q : (((ℕ × LinPair) × LinPair) × List ℤ) × LinPair =>
      binaryMatchConj q.1.1.1.1 q.1.1.1.2 q.1.1.2 q.1.2 q.2) := by
  unfold binaryMatchConj
  have hnn : Primrec (fun q : (((ℕ × LinPair) × LinPair) × List ℤ) × LinPair =>
      nonnegVars q.2.2.length) :=
    primrec_nonnegVars.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))
  have hrange : Primrec (fun q : (((ℕ × LinPair) × LinPair) × List ℤ) × LinPair =>
      List.range q.1.1.1.1) :=
    Primrec.list_range.comp
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  have hflat : Primrec (fun q : (((ℕ × LinPair) × LinPair) × List ℤ) × LinPair =>
      (List.range q.1.1.1.1).flatMap fun i =>
        eqAtomPair
          (periodCoeffs q.2.2 i ++
            (scaleList (-1) (periodCoeffs q.1.1.1.2.2 i) ++ scaleList (-1) (periodCoeffs q.1.1.2.2 i)))
          (((q.2.1.getD i 0 : ℕ) : ℤ) - ((q.1.1.1.2.1.getD i 0 : ℕ) : ℤ) -
            ((q.1.1.2.1.getD i 0 : ℕ) : ℤ) - q.1.2.getD i 0)) := by
    refine Primrec.list_flatMap hrange ?_
    have hc3 : Primrec (fun t : ((((ℕ × LinPair) × LinPair) × List ℤ) × LinPair) × ℕ =>
        periodCoeffs t.1.2.2 t.2) :=
      primrec_periodCoeffs.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
    have hc1 : Primrec (fun t : ((((ℕ × LinPair) × LinPair) × List ℤ) × LinPair) × ℕ =>
        scaleList (-1) (periodCoeffs t.1.1.1.1.2.2 t.2)) :=
      primrec_scaleList.comp (Primrec.const (-1 : ℤ))
        (primrec_periodCoeffs.comp
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))))
          Primrec.snd)
    have hc2 : Primrec (fun t : ((((ℕ × LinPair) × LinPair) × List ℤ) × LinPair) × ℕ =>
        scaleList (-1) (periodCoeffs t.1.1.1.2.2 t.2)) :=
      primrec_scaleList.comp (Primrec.const (-1 : ℤ))
        (primrec_periodCoeffs.comp
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
          Primrec.snd)
    have hcoeff := Primrec.list_append.comp hc3 (Primrec.list_append.comp hc1 hc2)
    have hb3 : Primrec (fun t : ((((ℕ × LinPair) × LinPair) × List ℤ) × LinPair) × ℕ =>
        ((t.1.2.1.getD t.2 0 : ℕ) : ℤ)) :=
      primrec_int_natCast.comp ((Primrec.list_getD (0 : ℕ)).comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
    have hb1 : Primrec (fun t : ((((ℕ × LinPair) × LinPair) × List ℤ) × LinPair) × ℕ =>
        ((t.1.1.1.1.2.1.getD t.2 0 : ℕ) : ℤ)) :=
      primrec_int_natCast.comp ((Primrec.list_getD (0 : ℕ)).comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))))
        Primrec.snd)
    have hb2 : Primrec (fun t : ((((ℕ × LinPair) × LinPair) × List ℤ) × LinPair) × ℕ =>
        ((t.1.1.1.2.1.getD t.2 0 : ℕ) : ℤ)) :=
      primrec_int_natCast.comp ((Primrec.list_getD (0 : ℕ)).comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
        Primrec.snd)
    have hr : Primrec (fun t : ((((ℕ × LinPair) × LinPair) × List ℤ) × LinPair) × ℕ =>
        t.1.1.2.getD t.2 0) :=
      (Primrec.list_getD (0 : ℤ)).comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
    have hconst := primrec_int_sub.comp (primrec_int_sub.comp (primrec_int_sub.comp hb3 hb1) hb2) hr
    exact (primrec_eqAtomPair.comp hcoeff hconst).to₂
  exact Primrec.list_append.comp hnn hflat

private def binaryLhsConj (d : ℕ) (bp1 bp2 : LinPair) (r : List ℤ) : Conj :=
  nonnegVars (bp1.2.length + bp2.2.length) ++
    (List.range d).map fun i =>
      (false, 0,
        scaleList (-1) (periodCoeffs bp1.2 i) ++ scaleList (-1) (periodCoeffs bp2.2 i),
        -((bp1.1.getD i 0 : ℕ) : ℤ) - ((bp2.1.getD i 0 : ℕ) : ℤ) - r.getD i 0)

private lemma primrec_binaryLhsConj :
    Primrec (fun q : ((ℕ × LinPair) × LinPair) × List ℤ =>
      binaryLhsConj q.1.1.1 q.1.1.2 q.1.2 q.2) := by
  unfold binaryLhsConj
  have hnn : Primrec (fun q : ((ℕ × LinPair) × LinPair) × List ℤ =>
      nonnegVars (q.1.1.2.2.length + q.1.2.2.length)) :=
    primrec_nonnegVars.comp
      (Primrec.nat_add.comp
        (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
        (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  have hrange : Primrec (fun q : ((ℕ × LinPair) × LinPair) × List ℤ => List.range q.1.1.1) :=
    Primrec.list_range.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hmap : Primrec (fun q : ((ℕ × LinPair) × LinPair) × List ℤ =>
      (List.range q.1.1.1).map fun i =>
        (false, 0,
          scaleList (-1) (periodCoeffs q.1.1.2.2 i) ++ scaleList (-1) (periodCoeffs q.1.2.2 i),
          -((q.1.1.2.1.getD i 0 : ℕ) : ℤ) - ((q.1.2.1.getD i 0 : ℕ) : ℤ) - q.2.getD i 0)) := by
    refine Primrec.list_map hrange ?_
    have hc1 : Primrec (fun t : (((ℕ × LinPair) × LinPair) × List ℤ) × ℕ =>
        scaleList (-1) (periodCoeffs t.1.1.1.2.2 t.2)) :=
      primrec_scaleList.comp (Primrec.const (-1 : ℤ))
        (primrec_periodCoeffs.comp
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
          Primrec.snd)
    have hc2 : Primrec (fun t : (((ℕ × LinPair) × LinPair) × List ℤ) × ℕ =>
        scaleList (-1) (periodCoeffs t.1.1.2.2 t.2)) :=
      primrec_scaleList.comp (Primrec.const (-1 : ℤ))
        (primrec_periodCoeffs.comp
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd)
    have hb1 : Primrec (fun t : (((ℕ × LinPair) × LinPair) × List ℤ) × ℕ =>
        -((t.1.1.1.2.1.getD t.2 0 : ℕ) : ℤ)) :=
      primrec_int_neg.comp (primrec_int_natCast.comp
        ((Primrec.list_getD (0 : ℕ)).comp
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
          Primrec.snd))
    have hb2 : Primrec (fun t : (((ℕ × LinPair) × LinPair) × List ℤ) × ℕ =>
        ((t.1.1.2.1.getD t.2 0 : ℕ) : ℤ)) :=
      primrec_int_natCast.comp
        ((Primrec.list_getD (0 : ℕ)).comp
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd)
    have hr : Primrec (fun t : (((ℕ × LinPair) × LinPair) × List ℤ) × ℕ => t.1.2.getD t.2 0) :=
      (Primrec.list_getD (0 : ℤ)).comp (Primrec.snd.comp Primrec.fst) Primrec.snd
    exact (Primrec.pair (Primrec.const false)
      (Primrec.pair (Primrec.const 0)
        (Primrec.pair (Primrec.list_append.comp hc1 hc2)
          (primrec_int_sub.comp (primrec_int_sub.comp hb1 hb2) hr)))).to₂
  exact Primrec.list_append.comp hnn hmap

private def checkBinaryTriple (d : ℕ) (S : List LinPair) (bp1 bp2 : LinPair) (r : List ℤ) : Bool :=
  let rhs := S.flatMap fun bp3 => elimMany bp3.2.length [binaryMatchConj d bp1 bp2 r bp3]
  !evalClosedDNF (elimMany (bp1.2.length + bp2.2.length)
    (andDNF [binaryLhsConj d bp1 bp2 r] (negDNF rhs)))

private lemma primrec_checkBinaryTriple :
    Primrec (fun q : (ℕ × List LinPair) × ((LinPair × LinPair) × List ℤ) =>
      checkBinaryTriple q.1.1 q.1.2 q.2.1.1 q.2.1.2 q.2.2) := by
  unfold checkBinaryTriple
  have hS : Primrec (fun q : (ℕ × List LinPair) × ((LinPair × LinPair) × List ℤ) => q.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hrhs : Primrec (fun q : (ℕ × List LinPair) × ((LinPair × LinPair) × List ℤ) =>
      q.1.2.flatMap fun bp3 => elimMany bp3.2.length [binaryMatchConj q.1.1 q.2.1.1 q.2.1.2 q.2.2 bp3]) := by
    refine Primrec.list_flatMap hS ?_
    have hlen : Primrec (fun t : ((ℕ × List LinPair) × ((LinPair × LinPair) × List ℤ)) × LinPair =>
        t.2.2.length) :=
      Primrec.list_length.comp (Primrec.snd.comp Primrec.snd)
    have hconj : Primrec (fun t : ((ℕ × List LinPair) × ((LinPair × LinPair) × List ℤ)) × LinPair =>
        [binaryMatchConj t.1.1.1 t.1.2.1.1 t.1.2.1.2 t.1.2.2 t.2]) :=
      Primrec.list_cons.comp
        (primrec_binaryMatchConj.comp
          (Primrec.pair
            (Primrec.pair
              (Primrec.pair
                (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
                  (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))
                (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))
              (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
            Primrec.snd))
        (Primrec.const ([] : DNF))
    exact (primrec_elimMany.comp hlen hconj).to₂
  have hlhs : Primrec (fun q : (ℕ × List LinPair) × ((LinPair × LinPair) × List ℤ) =>
      [binaryLhsConj q.1.1 q.2.1.1 q.2.1.2 q.2.2]) :=
    Primrec.list_cons.comp
      (primrec_binaryLhsConj.comp
        (Primrec.pair
          (Primrec.pair
            (Primrec.pair (Primrec.fst.comp Primrec.fst)
              (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
            (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
          (Primrec.snd.comp Primrec.snd)))
      (Primrec.const ([] : DNF))
  have hm12 : Primrec (fun q : (ℕ × List LinPair) × ((LinPair × LinPair) × List ℤ) =>
      q.2.1.1.2.length + q.2.1.2.2.length) :=
    Primrec.nat_add.comp
      (Primrec.list_length.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))))
      (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
  exact Primrec.not.comp (primrec_evalClosedDNF.comp
    (primrec_elimMany.comp hm12 (primrec_andDNF.comp hlhs (primrec_negDNF.comp hrhs))))

private lemma checkBinaryTriple_iff (d : ℕ) (S : List LinPair) (bp1 bp2 : LinPair) (r : List ℤ) :
    checkBinaryTriple d S bp1 bp2 r = true ↔
      ∀ (c1 : Fin bp1.2.length → ℕ) (c2 : Fin bp2.2.length → ℕ),
        let v1 : Fin d → ℤ := fun i =>
          (bp1.1.getD i.1 0 : ℤ) +
            ∑ j : Fin bp1.2.length, (c1 j : ℤ) * (((bp1.2[j]).getD i.1 0 : ℕ) : ℤ)
        let v2 : Fin d → ℤ := fun i =>
          (bp2.1.getD i.1 0 : ℤ) +
            ∑ j : Fin bp2.2.length, (c2 j : ℤ) * (((bp2.2[j]).getD i.1 0 : ℕ) : ℤ)
        (∀ i : Fin d, 0 ≤ v1 i + v2 i + r.getD i.1 0) →
        ∃ bp3 ∈ S, ∃ c3 : Fin bp3.2.length → ℕ,
          ∀ i : Fin d, v1 i + v2 i + r.getD i.1 0 = (bp3.1.getD i.1 0 : ℤ) +
            ∑ j : Fin bp3.2.length, (c3 j : ℤ) * (((bp3.2[j]).getD i.1 0 : ℕ) : ℤ) := by
  unfold checkBinaryTriple
  simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, evalClosedDNF_iff, evalDNF_elimMany,
    List.append_nil, evalDNF_andDNF, evalDNF_negDNF]
  have hsplit : ∀ xs : List ℤ, xs.length = bp1.2.length + bp2.2.length →
      ∃ xs1 xs2 : List ℤ, xs = xs1 ++ xs2 ∧ xs1.length = bp1.2.length ∧ xs2.length = bp2.2.length := by
    intro xs hlen
    exact ⟨xs.take bp1.2.length, xs.drop bp1.2.length, (List.take_append_drop _ _).symm,
      by simp [hlen], by simp [hlen]⟩
  have hrhs_iff : ∀ xs1 xs2 : List ℤ, xs1.length = bp1.2.length → xs2.length = bp2.2.length →
      (evalDNF (xs1 ++ xs2) (S.flatMap fun bp3 => elimMany bp3.2.length [binaryMatchConj d bp1 bp2 r bp3]) ↔
        ∃ bp3 ∈ S, ∃ c3 : Fin bp3.2.length → ℕ,
          ∀ i : Fin d,
            ((bp1.1.getD i.1 0 : ℤ) +
              ∑ j : Fin bp1.2.length, xs1.getD j.1 0 * (((bp1.2[j]).getD i.1 0 : ℕ) : ℤ)) +
            ((bp2.1.getD i.1 0 : ℤ) +
              ∑ j : Fin bp2.2.length, xs2.getD j.1 0 * (((bp2.2[j]).getD i.1 0 : ℕ) : ℤ)) +
            r.getD i.1 0 =
            (bp3.1.getD i.1 0 : ℤ) +
              ∑ j : Fin bp3.2.length, (c3 j : ℤ) * (((bp3.2[j]).getD i.1 0 : ℕ) : ℤ)) := by
    intro xs1 xs2 hlen1 _
    simp only [evalDNF, List.mem_flatMap]
    constructor
    · rintro ⟨c, ⟨bp3, hbp3, hc⟩, hev⟩
      obtain ⟨xs3, hlen3, hxs3⟩ :=
        (evalDNF_elimMany bp3.2.length [binaryMatchConj d bp1 bp2 r bp3] (xs1 ++ xs2)).mp ⟨c, hc, hev⟩
      simp only [evalDNF, List.mem_singleton, exists_eq_left] at hxs3
      have hnn3 : ∀ j : Fin bp3.2.length, (0 : ℤ) ≤ xs3.getD j.1 0 :=
        (evalConj_nonnegVars bp3.2.length xs3 (xs1 ++ xs2) hlen3).mp fun a ha =>
          hxs3 a (List.mem_append_left _ ha)
      refine ⟨bp3, hbp3, fun j => (xs3.getD j.1 0).toNat, fun i => ?_⟩
      have heq0 : dot (periodCoeffs bp3.2 i.1 ++
          (scaleList (-1) (periodCoeffs bp1.2 i.1) ++ scaleList (-1) (periodCoeffs bp2.2 i.1)))
          (xs3 ++ (xs1 ++ xs2)) +
          (((bp3.1.getD i.1 0 : ℕ) : ℤ) - ((bp1.1.getD i.1 0 : ℕ) : ℤ) -
            ((bp2.1.getD i.1 0 : ℕ) : ℤ) - r.getD i.1 0) = 0 :=
        (evalConj_eqAtomPair (xs3 ++ (xs1 ++ xs2)) _ _).mp fun a ha =>
          hxs3 a (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i.1, List.mem_range.mpr i.2, ha⟩))
      have hp3 : (periodCoeffs bp3.2 i.1).length = xs3.length := by simp [periodCoeffs, hlen3]
      have hp1 : (scaleList (-1) (periodCoeffs bp1.2 i.1)).length = xs1.length := by
        simp [scaleList, periodCoeffs, hlen1]
      rw [dot_append hp3, dot_append hp1, dot_scaleList, dot_scaleList,
        dot_periodCoeffs bp3.2 i.1 xs3, dot_periodCoeffs bp1.2 i.1 xs1,
        dot_periodCoeffs bp2.2 i.1 xs2] at heq0
      have hcast : ∀ j : Fin bp3.2.length, (((xs3.getD j.1 0).toNat : ℕ) : ℤ) = xs3.getD j.1 0 :=
        fun j => Int.toNat_of_nonneg (hnn3 j)
      simp_rw [hcast]
      linarith
    · rintro ⟨bp3, hbp3, c3, hc3⟩
      set xs3 : List ℤ := List.ofFn (fun j : Fin bp3.2.length => (c3 j : ℤ))
      have hlen3 : xs3.length = bp3.2.length := by simp [xs3]
      have hget3 : ∀ j : Fin bp3.2.length, xs3.getD j.1 0 = (c3 j : ℤ) := by
        intro j; simp [xs3, List.getD_eq_getElem?_getD]
      have hsat : evalDNF (xs1 ++ xs2) (elimMany bp3.2.length [binaryMatchConj d bp1 bp2 r bp3]) := by
        rw [evalDNF_elimMany]
        refine ⟨xs3, hlen3, binaryMatchConj d bp1 bp2 r bp3, List.mem_singleton_self _, fun a ha => ?_⟩
        rcases List.mem_append.mp ha with h1 | h2
        · exact ((evalConj_nonnegVars bp3.2.length xs3 (xs1 ++ xs2) hlen3).mpr fun j => by
            rw [hget3 j]; exact Int.natCast_nonneg _) a h1
        · obtain ⟨i, hi, ha_eq⟩ := List.mem_flatMap.mp h2
          have hi' := List.mem_range.mp hi
          refine ((evalConj_eqAtomPair (xs3 ++ (xs1 ++ xs2)) _ _).mpr ?_) a ha_eq
          have hp3 : (periodCoeffs bp3.2 i).length = xs3.length := by simp [periodCoeffs, hlen3]
          have hp1 : (scaleList (-1) (periodCoeffs bp1.2 i)).length = xs1.length := by
            simp [scaleList, periodCoeffs, hlen1]
          rw [dot_append hp3, dot_append hp1, dot_scaleList, dot_scaleList,
            dot_periodCoeffs bp3.2 i xs3, dot_periodCoeffs bp1.2 i xs1,
            dot_periodCoeffs bp2.2 i xs2]
          simp_rw [hget3]
          have hci := hc3 ⟨i, hi'⟩
          linarith
      obtain ⟨c, hc, hev⟩ := hsat
      exact ⟨c, ⟨bp3, hbp3, hc⟩, hev⟩
  have hlhs_iff : ∀ xs1 xs2 : List ℤ, xs1.length = bp1.2.length → xs2.length = bp2.2.length →
      (evalDNF (xs1 ++ xs2) [binaryLhsConj d bp1 bp2 r] ↔
        (∀ j : Fin bp1.2.length, (0 : ℤ) ≤ xs1.getD j.1 0) ∧
        (∀ j : Fin bp2.2.length, (0 : ℤ) ≤ xs2.getD j.1 0) ∧
        (∀ i : Fin d, 0 ≤
          ((bp1.1.getD i.1 0 : ℤ) +
            ∑ j : Fin bp1.2.length, xs1.getD j.1 0 * (((bp1.2[j]).getD i.1 0 : ℕ) : ℤ)) +
          ((bp2.1.getD i.1 0 : ℤ) +
            ∑ j : Fin bp2.2.length, xs2.getD j.1 0 * (((bp2.2[j]).getD i.1 0 : ℕ) : ℤ)) +
          r.getD i.1 0)) := by
    intro xs1 xs2 hlen1 hlen2
    have hlen12 : (xs1 ++ xs2).length = bp1.2.length + bp2.2.length := by simp [hlen1, hlen2]
    simp only [evalDNF, List.mem_singleton, exists_eq_left, binaryLhsConj]
    constructor
    · intro h
      have hnn := (evalConj_nonnegVars_nil _ (xs1 ++ xs2) hlen12).mp fun a ha =>
        h a (List.mem_append_left _ ha)
      refine ⟨fun j => ?_, fun j => ?_, fun i => ?_⟩
      · have hj := hnn ⟨j.1, by omega⟩
        have hget : (xs1 ++ xs2).getD j.1 0 = xs1.getD j.1 0 := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : j.1 < xs1.length)]
        rwa [hget] at hj
      · have hj := hnn ⟨bp1.2.length + j.1, by omega⟩
        have hget : (xs1 ++ xs2).getD (bp1.2.length + j.1) 0 = xs2.getD j.1 0 := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : xs1.length ≤ bp1.2.length + j.1),
            hlen1]
        rwa [hget] at hj
      · have hi := h _ (List.mem_append_right _ (List.mem_map.mpr ⟨i.1, List.mem_range.mpr i.2, rfl⟩))
        have hp1 : (scaleList (-1) (periodCoeffs bp1.2 i.1)).length = xs1.length := by
          simp [scaleList, periodCoeffs, hlen1]
        simp only [evalAtom, Bool.false_eq_true, ↓reduceIte, dot_append hp1, dot_scaleList,
          dot_periodCoeffs bp1.2 i.1 xs1, dot_periodCoeffs bp2.2 i.1 xs2] at hi
        linarith
    · rintro ⟨hnn1, hnn2, hpos⟩ a ha
      rcases List.mem_append.mp ha with h1 | h2
      · refine ((evalConj_nonnegVars_nil _ (xs1 ++ xs2) hlen12).mpr fun j => ?_) a h1
        by_cases hj : j.1 < bp1.2.length
        · have hget : (xs1 ++ xs2).getD j.1 0 = xs1.getD j.1 0 := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : j.1 < xs1.length)]
          rw [hget]; exact hnn1 ⟨j.1, hj⟩
        · have hget : (xs1 ++ xs2).getD j.1 0 = xs2.getD (j.1 - bp1.2.length) 0 := by
            simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : xs1.length ≤ j.1), hlen1]
          rw [hget]; exact hnn2 ⟨j.1 - bp1.2.length, by omega⟩
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h2
        have hi' := List.mem_range.mp hi
        have hp1 : (scaleList (-1) (periodCoeffs bp1.2 i)).length = xs1.length := by
          simp [scaleList, periodCoeffs, hlen1]
        simp only [evalAtom, Bool.false_eq_true, ↓reduceIte, dot_append hp1, dot_scaleList,
          dot_periodCoeffs bp1.2 i xs1, dot_periodCoeffs bp2.2 i xs2]
        have := hpos ⟨i, hi'⟩
        linarith
  constructor
  · intro hnot c1 c2 hpos
    set xs1 : List ℤ := List.ofFn (fun j : Fin bp1.2.length => (c1 j : ℤ))
    set xs2 : List ℤ := List.ofFn (fun j : Fin bp2.2.length => (c2 j : ℤ))
    have hlen1 : xs1.length = bp1.2.length := by simp [xs1]
    have hlen2 : xs2.length = bp2.2.length := by simp [xs2]
    have hget1 : ∀ j : Fin bp1.2.length, xs1.getD j.1 0 = (c1 j : ℤ) := by
      intro j; simp [xs1, List.getD_eq_getElem?_getD]
    have hget2 : ∀ j : Fin bp2.2.length, xs2.getD j.1 0 = (c2 j : ℤ) := by
      intro j; simp [xs2, List.getD_eq_getElem?_getD]
    have hlhs : evalDNF (xs1 ++ xs2) [binaryLhsConj d bp1 bp2 r] := by
      rw [hlhs_iff xs1 xs2 hlen1 hlen2]
      refine ⟨fun j => by rw [hget1 j]; exact Int.natCast_nonneg _,
        fun j => by rw [hget2 j]; exact Int.natCast_nonneg _, fun i => ?_⟩
      simp_rw [hget1, hget2]; exact hpos i
    have hrhs : evalDNF (xs1 ++ xs2)
        (S.flatMap fun bp3 => elimMany bp3.2.length [binaryMatchConj d bp1 bp2 r bp3]) := by
      by_contra hnr
      exact hnot ⟨xs1 ++ xs2, by simp [hlen1, hlen2], hlhs, hnr⟩
    obtain ⟨bp3, hbp3, c3, hc3⟩ := (hrhs_iff xs1 xs2 hlen1 hlen2).mp hrhs
    refine ⟨bp3, hbp3, c3, fun i => ?_⟩
    have := hc3 i; simp_rw [hget1, hget2] at this; exact this
  · intro hall
    rintro ⟨xs, hlen, hlhs, hnr⟩
    obtain ⟨xs1, xs2, rfl, hlen1, hlen2⟩ := hsplit xs hlen
    obtain ⟨hnn1, hnn2, hpos12⟩ := (hlhs_iff xs1 xs2 hlen1 hlen2).mp hlhs
    have hcast1 : ∀ j : Fin bp1.2.length, (((xs1.getD j.1 0).toNat : ℕ) : ℤ) = xs1.getD j.1 0 :=
      fun j => Int.toNat_of_nonneg (hnn1 j)
    have hcast2 : ∀ j : Fin bp2.2.length, (((xs2.getD j.1 0).toNat : ℕ) : ℤ) = xs2.getD j.1 0 :=
      fun j => Int.toNat_of_nonneg (hnn2 j)
    have hpos' : ∀ i : Fin d, 0 ≤
        ((bp1.1.getD i.1 0 : ℤ) +
          ∑ j : Fin bp1.2.length, (((xs1.getD j.1 0).toNat : ℕ) : ℤ) * (((bp1.2[j]).getD i.1 0 : ℕ) : ℤ)) +
        ((bp2.1.getD i.1 0 : ℤ) +
          ∑ j : Fin bp2.2.length, (((xs2.getD j.1 0).toNat : ℕ) : ℤ) * (((bp2.2[j]).getD i.1 0 : ℕ) : ℤ)) +
        r.getD i.1 0 := by
      intro i; simp_rw [hcast1, hcast2]; exact hpos12 i
    obtain ⟨bp3, hbp3, c3, hc3⟩ :=
      hall (fun j => (xs1.getD j.1 0).toNat) (fun j => (xs2.getD j.1 0).toNat) hpos'
    apply hnr
    rw [hrhs_iff xs1 xs2 hlen1 hlen2]
    refine ⟨bp3, hbp3, c3, fun i => ?_⟩
    have := hc3 i; simp_rw [hcast1, hcast2] at this; exact this

/- ### Part 6: Combined BVAS invariant checker and `Primrec` proof -/

private def checkUnaryForBP (d : ℕ) (S : List LinPair) (U : List (List ℤ)) (bp1 : LinPair) : Bool :=
  listAll (fun r => checkUnaryPair d S bp1 r) U

private lemma primrec_checkUnaryForBP :
    Primrec (fun q : ((ℕ × List LinPair) × List (List ℤ)) × LinPair =>
      checkUnaryForBP q.1.1.1 q.1.1.2 q.1.2 q.2) := by
  unfold checkUnaryForBP
  have hU : Primrec (fun q : ((ℕ × List LinPair) × List (List ℤ)) × LinPair => q.1.2) :=
    Primrec.snd.comp Primrec.fst
  refine primrec_listAll hU ?_
  have harg : Primrec (fun t : (((ℕ × List LinPair) × List (List ℤ)) × LinPair) × List ℤ =>
      ((t.1.1.1.1, t.1.1.1.2), (t.1.2, t.2))) :=
    Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
  exact (primrec_checkUnaryPair.comp harg).to₂

private def checkUnaryAll (d : ℕ) (S : List LinPair) (U : List (List ℤ)) : Bool :=
  listAll (fun bp1 => checkUnaryForBP d S U bp1) S

private lemma primrec_checkUnaryAll :
    Primrec (fun q : (ℕ × List LinPair) × List (List ℤ) => checkUnaryAll q.1.1 q.1.2 q.2) := by
  unfold checkUnaryAll
  have hS : Primrec (fun q : (ℕ × List LinPair) × List (List ℤ) => q.1.2) :=
    Primrec.snd.comp Primrec.fst
  exact primrec_listAll hS primrec_checkUnaryForBP.to₂

private def checkBinaryForBP2 (d : ℕ) (S : List LinPair) (B : List (List ℤ)) (bp1 bp2 : LinPair) : Bool :=
  listAll (fun r => checkBinaryTriple d S bp1 bp2 r) B

private lemma primrec_checkBinaryForBP2 :
    Primrec (fun q : (((ℕ × List LinPair) × List (List ℤ)) × LinPair) × LinPair =>
      checkBinaryForBP2 q.1.1.1.1 q.1.1.1.2 q.1.1.2 q.1.2 q.2) := by
  unfold checkBinaryForBP2
  have hB : Primrec (fun q : (((ℕ × List LinPair) × List (List ℤ)) × LinPair) × LinPair => q.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  refine primrec_listAll hB ?_
  have harg : Primrec (fun t : ((((ℕ × List LinPair) × List (List ℤ)) × LinPair) × LinPair) × List ℤ =>
      ((t.1.1.1.1.1, t.1.1.1.1.2), ((t.1.1.2, t.1.2), t.2))) :=
    Primrec.pair (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.pair (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst)) Primrec.snd)
  exact (primrec_checkBinaryTriple.comp harg).to₂

private def checkBinaryForBP1 (d : ℕ) (S : List LinPair) (B : List (List ℤ)) (bp1 : LinPair) : Bool :=
  listAll (fun bp2 => checkBinaryForBP2 d S B bp1 bp2) S

private lemma primrec_checkBinaryForBP1 :
    Primrec (fun q : ((ℕ × List LinPair) × List (List ℤ)) × LinPair =>
      checkBinaryForBP1 q.1.1.1 q.1.1.2 q.1.2 q.2) := by
  unfold checkBinaryForBP1
  have hS : Primrec (fun q : ((ℕ × List LinPair) × List (List ℤ)) × LinPair => q.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  exact primrec_listAll hS primrec_checkBinaryForBP2.to₂

private def checkBinaryAll (d : ℕ) (S : List LinPair) (B : List (List ℤ)) : Bool :=
  listAll (fun bp1 => checkBinaryForBP1 d S B bp1) S

private lemma primrec_checkBinaryAll :
    Primrec (fun q : (ℕ × List LinPair) × List (List ℤ) => checkBinaryAll q.1.1 q.1.2 q.2) := by
  unfold checkBinaryAll
  have hS : Primrec (fun q : (ℕ × List LinPair) × List (List ℤ) => q.1.2) :=
    Primrec.snd.comp Primrec.fst
  exact primrec_listAll hS primrec_checkBinaryForBP1.to₂

private def checkClause1 (q : RawBVAS) : Bool :=
  listAll (fun v => !nonnegList v || checkMem q.1.1 q.2 v) q.1.2.1

private def checkClause2 (q : RawBVAS) : Bool :=
  checkUnaryAll q.1.1 q.2 q.1.2.2.1

private def checkClause3 (q : RawBVAS) : Bool :=
  checkBinaryAll q.1.1 q.2 q.1.2.2.2.1

private def checkClause4 (q : RawBVAS) : Bool :=
  !checkMem q.1.1 q.2 q.1.2.2.2.2

private lemma primrec_checkClause1 : Primrec checkClause1 := by
  unfold checkClause1
  have hd : Primrec (fun q : RawBVAS => q.1.1) := Primrec.fst.comp Primrec.fst
  have hA : Primrec (fun q : RawBVAS => q.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hS : Primrec (fun q : RawBVAS => q.2) := Primrec.snd
  refine primrec_listAll hA ?_
  exact (Primrec.or.comp (Primrec.not.comp (primrec_nonnegList.comp Primrec.snd))
    (primrec_checkMem.comp
      (Primrec.pair (hd.comp Primrec.fst) (Primrec.pair (hS.comp Primrec.fst) Primrec.snd)))).to₂

private lemma primrec_raw_d : Primrec (fun q : RawBVAS => q.1.1) :=
  Primrec.fst.comp Primrec.fst

private lemma primrec_raw_rest1 :
    Primrec (fun q : RawBVAS => q.1.2) :=
  Primrec.snd.comp Primrec.fst

private lemma primrec_raw_rest2 :
    Primrec (fun q : RawBVAS => q.1.2.2) :=
  Primrec.snd.comp primrec_raw_rest1

private lemma primrec_raw_rest3 :
    Primrec (fun q : RawBVAS => q.1.2.2.2) :=
  Primrec.snd.comp primrec_raw_rest2

private lemma primrec_checkClause2 : Primrec checkClause2 := by
  have hd : Primrec (fun q : RawBVAS => q.1.1) := primrec_raw_d
  have hU : Primrec (fun q : RawBVAS => q.1.2.2.1) := Primrec.fst.comp primrec_raw_rest2
  have hS : Primrec (fun q : RawBVAS => q.2) := Primrec.snd
  exact (primrec_checkUnaryAll.comp (Primrec.pair (Primrec.pair hd hS) hU)).of_eq fun _ => rfl

private lemma primrec_checkClause3 : Primrec checkClause3 := by
  have hd : Primrec (fun q : RawBVAS => q.1.1) := primrec_raw_d
  have hB : Primrec (fun q : RawBVAS => q.1.2.2.2.1) := Primrec.fst.comp primrec_raw_rest3
  have hS : Primrec (fun q : RawBVAS => q.2) := Primrec.snd
  exact (primrec_checkBinaryAll.comp (Primrec.pair (Primrec.pair hd hS) hB)).of_eq fun _ => rfl

private lemma primrec_checkClause4 : Primrec checkClause4 := by
  have hd : Primrec (fun q : RawBVAS => q.1.1) := primrec_raw_d
  have htv : Primrec (fun q : RawBVAS => q.1.2.2.2.2) := Primrec.snd.comp primrec_raw_rest3
  have hS : Primrec (fun q : RawBVAS => q.2) := Primrec.snd
  exact (Primrec.not.comp (primrec_checkMem.comp (Primrec.pair hd (Primrec.pair hS htv)))).of_eq
    fun _ => rfl

private def checkRaw (q : RawBVAS) : Bool :=
  checkClause1 q && checkClause2 q && checkClause3 q && checkClause4 q

private lemma primrec_checkRaw : Primrec checkRaw :=
  Primrec.and.comp
    (Primrec.and.comp (Primrec.and.comp primrec_checkClause1 primrec_checkClause2)
      primrec_checkClause3)
    primrec_checkClause4


/- ### Part 7: Connecting `checkRaw` to `OMA.R_BranchingVAS_reachability_decidable_R1.H1` -/

open BranchingVAS

private abbrev BVASInput := Σ d : ℕ, Bvas d × (Fin d → ℤ)

private def encodeBVAS (p : BVASInput) :
    ℕ × List (List ℤ) × List (List ℤ) × List (List ℤ) × List ℤ :=
  (p.1, p.2.1.1.map List.ofFn, p.2.1.unaryRules.map List.ofFn,
    p.2.1.binaryRules.map List.ofFn, List.ofFn p.2.2)

private lemma primrec_encodeBVAS : Primrec encodeBVAS :=
  Primrec.encode_iff.mp Primrec.encode

private def decideBVAS (x : BVASInput × List LinPair) : Bool :=
  checkRaw (encodeBVAS x.1, x.2)

private lemma primrec_decideBVAS : Primrec decideBVAS :=
  (primrec_checkRaw.comp (Primrec.pair (primrec_encodeBVAS.comp Primrec.fst) Primrec.snd)).of_eq
    fun _ => rfl

private lemma nonnegList_ofFn_iff {d : ℕ} (v : Fin d → ℤ) :
    nonnegList (List.ofFn v) = true ↔ 0 ≤ v := by
  rw [nonnegList_eq_true_iff]
  constructor
  · intro h i
    exact h (v i) (by simp)
  · intro h z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact h i

private lemma getD_ofFn {d : ℕ} (v : Fin d → ℤ) (i : Fin d) :
    (List.ofFn v).getD i.1 0 = v i := by
  simp [List.getD_eq_getElem?_getD]

private lemma checkMem_ofFn_iff {d : ℕ} (S : List LinPair) (v : Fin d → ℤ) :
    checkMem d S (List.ofFn v) = true ↔
      ∃ bp ∈ S, ∃ c : Fin bp.2.length → ℕ,
        ∀ i : Fin d, v i = (bp.1.getD i.1 0 : ℤ) +
          ∑ j : Fin bp.2.length, (c j : ℤ) * (((bp.2[j]).getD i.1 0 : ℕ) : ℤ) := by
  rw [checkMem_iff]
  simp_rw [getD_ofFn]

private lemma decideBVAS_eq_true_iff (x : BVASInput × List LinPair) :
    decideBVAS x = true ↔
      let d := x.1.1
      let b := x.1.2.1
      let t := x.1.2.2
      let mem : (Fin d → ℤ) → Prop := fun v =>
        ∃ bp ∈ x.2, ∃ c : Fin bp.2.length → ℕ,
          ∀ i : Fin d, v i = (bp.1.getD i.1 0 : ℤ) +
            ∑ j : Fin bp.2.length, (c j : ℤ) * (((bp.2[j]).getD i.1 0 : ℕ) : ℤ)
      (∀ v ∈ b.1, 0 ≤ v → mem v) ∧
      (∀ v r, mem v → r ∈ b.unaryRules → 0 ≤ v + r → mem (v + r)) ∧
      (∀ v₁ v₂ r, mem v₁ → mem v₂ → r ∈ b.binaryRules → 0 ≤ v₁ + v₂ + r → mem (v₁ + v₂ + r)) ∧
      ¬ mem t := by
  rcases x with ⟨⟨d, b, t⟩, S⟩
  dsimp only [decideBVAS, checkRaw, encodeBVAS]
  simp only [Bool.and_eq_true]
  have hc1 : checkClause1 ((d, b.1.map List.ofFn, b.unaryRules.map List.ofFn,
      b.binaryRules.map List.ofFn, List.ofFn t), S) = true ↔
      ∀ v ∈ b.1, 0 ≤ v →
        ∃ bp ∈ S, ∃ c : Fin bp.2.length → ℕ,
          ∀ i : Fin d, v i = (bp.1.getD i.1 0 : ℤ) +
            ∑ j : Fin bp.2.length, (c j : ℤ) * (((bp.2[j]).getD i.1 0 : ℕ) : ℤ) := by
    have hlhs : checkClause1 ((d, b.1.map List.ofFn, b.unaryRules.map List.ofFn,
        b.binaryRules.map List.ofFn, List.ofFn t), S) = true ↔
        ∀ v ∈ b.1, ¬ (0 ≤ v) ∨ checkMem d S (List.ofFn v) = true := by
      unfold checkClause1
      rw [listAll_eq_true]
      simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
        Bool.or_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, nonnegList_ofFn_iff]
    rw [hlhs]
    refine forall_congr' fun v => imp_congr_right fun _ => ?_
    rw [checkMem_ofFn_iff]
    tauto
  have hc2 : checkClause2 ((d, b.1.map List.ofFn, b.unaryRules.map List.ofFn,
      b.binaryRules.map List.ofFn, List.ofFn t), S) = true ↔
      ∀ v r,
        (∃ bp ∈ S, ∃ c : Fin bp.2.length → ℕ,
          ∀ i : Fin d, v i = (bp.1.getD i.1 0 : ℤ) +
            ∑ j : Fin bp.2.length, (c j : ℤ) * (((bp.2[j]).getD i.1 0 : ℕ) : ℤ)) →
        r ∈ b.unaryRules → 0 ≤ v + r →
        ∃ bp ∈ S, ∃ c : Fin bp.2.length → ℕ,
          ∀ i : Fin d, (v + r) i = (bp.1.getD i.1 0 : ℤ) +
            ∑ j : Fin bp.2.length, (c j : ℤ) * (((bp.2[j]).getD i.1 0 : ℕ) : ℤ) := by
    have hlhs : checkClause2 ((d, b.1.map List.ofFn, b.unaryRules.map List.ofFn,
        b.binaryRules.map List.ofFn, List.ofFn t), S) = true ↔
        ∀ bp1 ∈ S, ∀ r ∈ b.unaryRules,
          ∀ c1 : Fin bp1.2.length → ℕ,
            (∀ i : Fin d, 0 ≤ ((bp1.1.getD i.1 0 : ℤ) +
              ∑ j : Fin bp1.2.length, (c1 j : ℤ) * (((bp1.2[j]).getD i.1 0 : ℕ) : ℤ)) + r i) →
            ∃ bp2 ∈ S, ∃ c2 : Fin bp2.2.length → ℕ,
              ∀ i : Fin d, ((bp1.1.getD i.1 0 : ℤ) +
                ∑ j : Fin bp1.2.length, (c1 j : ℤ) * (((bp1.2[j]).getD i.1 0 : ℕ) : ℤ)) + r i =
                (bp2.1.getD i.1 0 : ℤ) +
                  ∑ j : Fin bp2.2.length, (c2 j : ℤ) * (((bp2.2[j]).getD i.1 0 : ℕ) : ℤ) := by
      unfold checkClause2 checkUnaryAll checkUnaryForBP
      rw [listAll_eq_true]
      simp_rw [listAll_eq_true, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, checkUnaryPair_iff, getD_ofFn]
    rw [hlhs]
    constructor
    · intro h v r hmem hr hnn
      obtain ⟨bp1, hbp1, c1, hv⟩ := hmem
      have hpos : ∀ i : Fin d, 0 ≤
          ((bp1.1.getD i.1 0 : ℤ) +
            ∑ j : Fin bp1.2.length, (c1 j : ℤ) * (((bp1.2[j]).getD i.1 0 : ℕ) : ℤ)) + r i := by
        intro i; rw [← hv i]; exact hnn i
      obtain ⟨bp2, hbp2, c2, hc2⟩ := h bp1 hbp1 r hr c1 hpos
      refine ⟨bp2, hbp2, c2, fun i => ?_⟩
      change v i + r i = _
      rw [hv i]; exact hc2 i
    · intro h bp1 hbp1 r hr c1 hpos
      let v : Fin d → ℤ := fun i =>
        (bp1.1.getD i.1 0 : ℤ) +
          ∑ j : Fin bp1.2.length, (c1 j : ℤ) * (((bp1.2[j]).getD i.1 0 : ℕ) : ℤ)
      exact h v r ⟨bp1, hbp1, c1, fun _ => rfl⟩ hr (fun i => hpos i)
  have hc3 : checkClause3 ((d, b.1.map List.ofFn, b.unaryRules.map List.ofFn,
      b.binaryRules.map List.ofFn, List.ofFn t), S) = true ↔
      ∀ v₁ v₂ r,
        (∃ bp ∈ S, ∃ c : Fin bp.2.length → ℕ,
          ∀ i : Fin d, v₁ i = (bp.1.getD i.1 0 : ℤ) +
            ∑ j : Fin bp.2.length, (c j : ℤ) * (((bp.2[j]).getD i.1 0 : ℕ) : ℤ)) →
        (∃ bp ∈ S, ∃ c : Fin bp.2.length → ℕ,
          ∀ i : Fin d, v₂ i = (bp.1.getD i.1 0 : ℤ) +
            ∑ j : Fin bp.2.length, (c j : ℤ) * (((bp.2[j]).getD i.1 0 : ℕ) : ℤ)) →
        r ∈ b.binaryRules → 0 ≤ v₁ + v₂ + r →
        ∃ bp ∈ S, ∃ c : Fin bp.2.length → ℕ,
          ∀ i : Fin d, (v₁ + v₂ + r) i = (bp.1.getD i.1 0 : ℤ) +
            ∑ j : Fin bp.2.length, (c j : ℤ) * (((bp.2[j]).getD i.1 0 : ℕ) : ℤ) := by
    have hlhs : checkClause3 ((d, b.1.map List.ofFn, b.unaryRules.map List.ofFn,
        b.binaryRules.map List.ofFn, List.ofFn t), S) = true ↔
        ∀ bp1 ∈ S, ∀ bp2 ∈ S, ∀ r ∈ b.binaryRules,
          ∀ (c1 : Fin bp1.2.length → ℕ) (c2 : Fin bp2.2.length → ℕ),
            (∀ i : Fin d, 0 ≤
              ((bp1.1.getD i.1 0 : ℤ) +
                ∑ j : Fin bp1.2.length, (c1 j : ℤ) * (((bp1.2[j]).getD i.1 0 : ℕ) : ℤ)) +
              ((bp2.1.getD i.1 0 : ℤ) +
                ∑ j : Fin bp2.2.length, (c2 j : ℤ) * (((bp2.2[j]).getD i.1 0 : ℕ) : ℤ)) + r i) →
            ∃ bp3 ∈ S, ∃ c3 : Fin bp3.2.length → ℕ,
              ∀ i : Fin d,
                ((bp1.1.getD i.1 0 : ℤ) +
                  ∑ j : Fin bp1.2.length, (c1 j : ℤ) * (((bp1.2[j]).getD i.1 0 : ℕ) : ℤ)) +
                ((bp2.1.getD i.1 0 : ℤ) +
                  ∑ j : Fin bp2.2.length, (c2 j : ℤ) * (((bp2.2[j]).getD i.1 0 : ℕ) : ℤ)) + r i =
                (bp3.1.getD i.1 0 : ℤ) +
                  ∑ j : Fin bp3.2.length, (c3 j : ℤ) * (((bp3.2[j]).getD i.1 0 : ℕ) : ℤ) := by
      unfold checkClause3 checkBinaryAll checkBinaryForBP1 checkBinaryForBP2
      rw [listAll_eq_true]
      simp_rw [listAll_eq_true, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, checkBinaryTriple_iff, getD_ofFn]
    rw [hlhs]
    constructor
    · intro h v₁ v₂ r hmem1 hmem2 hr hnn
      obtain ⟨bp1, hbp1, c1, hv1⟩ := hmem1
      obtain ⟨bp2, hbp2, c2, hv2⟩ := hmem2
      have hpos : ∀ i : Fin d, 0 ≤
          ((bp1.1.getD i.1 0 : ℤ) +
            ∑ j : Fin bp1.2.length, (c1 j : ℤ) * (((bp1.2[j]).getD i.1 0 : ℕ) : ℤ)) +
          ((bp2.1.getD i.1 0 : ℤ) +
            ∑ j : Fin bp2.2.length, (c2 j : ℤ) * (((bp2.2[j]).getD i.1 0 : ℕ) : ℤ)) + r i := by
        intro i; rw [← hv1 i, ← hv2 i]; exact hnn i
      obtain ⟨bp3, hbp3, c3, hc3⟩ := h bp1 hbp1 bp2 hbp2 r hr c1 c2 hpos
      refine ⟨bp3, hbp3, c3, fun i => ?_⟩
      change v₁ i + v₂ i + r i = _
      rw [hv1 i, hv2 i]; exact hc3 i
    · intro h bp1 hbp1 bp2 hbp2 r hr c1 c2 hpos
      let v₁ : Fin d → ℤ := fun i =>
        (bp1.1.getD i.1 0 : ℤ) +
          ∑ j : Fin bp1.2.length, (c1 j : ℤ) * (((bp1.2[j]).getD i.1 0 : ℕ) : ℤ)
      let v₂ : Fin d → ℤ := fun i =>
        (bp2.1.getD i.1 0 : ℤ) +
          ∑ j : Fin bp2.2.length, (c2 j : ℤ) * (((bp2.2[j]).getD i.1 0 : ℕ) : ℤ)
      exact h v₁ v₂ r ⟨bp1, hbp1, c1, fun _ => rfl⟩ ⟨bp2, hbp2, c2, fun _ => rfl⟩ hr (fun i => hpos i)
  have hc4 : checkClause4 ((d, b.1.map List.ofFn, b.unaryRules.map List.ofFn,
      b.binaryRules.map List.ofFn, List.ofFn t), S) = true ↔
      ¬ ∃ bp ∈ S, ∃ c : Fin bp.2.length → ℕ,
        ∀ i : Fin d, t i = (bp.1.getD i.1 0 : ℤ) +
          ∑ j : Fin bp.2.length, (c j : ℤ) * (((bp.2[j]).getD i.1 0 : ℕ) : ℤ) := by
    unfold checkClause4
    simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, checkMem_ofFn_iff]
  rw [hc1, hc2, hc3, hc4]
  tauto

end OMA.BVASH1

theorem OMA.solution : OMA.R_BranchingVAS_reachability_decidable_R1.H1 := by
  unfold OMA.R_BranchingVAS_reachability_decidable_R1.H1
  rw [ComputablePred.computable_iff]
  refine ⟨OMA.BVASH1.decideBVAS, OMA.BVASH1.primrec_decideBVAS.to_comp, ?_⟩
  funext x
  exact propext (OMA.BVASH1.decideBVAS_eq_true_iff x).symm
