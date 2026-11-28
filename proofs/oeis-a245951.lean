import OMAStatements.S_oeis_a245951

/-!
# OEIS A245951

Source: https://oeis.org/A245951
The generating function and parity formulas are attributed there to Colin Barker.
The formal statement credits @clementtrecourt. Proof by @grp06.
-/

namespace OMA.S_oeis_a245951

open scoped BigOperators

private noncomputable def cnt {α : Type*} (P : α → Prop) : ℕ :=
  Nat.card {x // P x}

private theorem cnt_filter {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    cnt P = (Finset.univ.filter P).card := by
  rw [cnt, Nat.card_eq_fintype_card, Fintype.card_subtype]

private theorem cnt_congr {α : Type*} {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) :
    cnt P = cnt Q :=
  Nat.card_congr (Equiv.subtypeEquivRight h)

private theorem cnt_equiv {α β : Type*} {P : α → Prop} {Q : β → Prop}
    (e : α ≃ β) (h : ∀ x, P x ↔ Q (e x)) : cnt P = cnt Q :=
  Nat.card_congr (e.subtypeEquiv h)

private theorem cnt_split {α : Type*} [Fintype α] (P Q : α → Prop) :
    cnt (fun x => P x ∧ Q x) + cnt (fun x => P x ∧ ¬ Q x) = cnt P := by
  classical
  simpa only [cnt_filter, Finset.filter_filter] using
    (Finset.card_filter_add_card_filter_not (s := Finset.univ.filter P) Q)

private theorem cnt_disj {α : Type*} [Fintype α] (P Q : α → Prop)
    (h : ∀ x, P x → ¬ Q x) :
    cnt (fun x => P x ∨ Q x) = cnt P + cnt Q := by
  have h₁ : cnt (fun x => (P x ∨ Q x) ∧ P x) = cnt P :=
    cnt_congr fun _ => ⟨And.right, fun hp => ⟨Or.inl hp, hp⟩⟩
  have h₂ : cnt (fun x => (P x ∨ Q x) ∧ ¬ P x) = cnt Q :=
    cnt_congr fun x => ⟨fun ⟨hpq, hnp⟩ => hpq.resolve_left hnp,
      fun hq => ⟨Or.inr hq, fun hp => h x hp hq⟩⟩
  simpa only [h₁, h₂] using (cnt_split (fun x => P x ∨ Q x) P).symm

private theorem cnt_partition {α β : Type*} [Fintype α] [Fintype β]
    (P : α → Prop) (f : α → β) :
    (∑ b : β, cnt (fun x => P x ∧ f x = b)) = cnt P := by
  classical
  simpa only [cnt_filter, Finset.filter_filter, Finset.mem_univ, and_true] using
    (Finset.sum_card_fiberwise_eq_card_filter (Finset.univ.filter P) Finset.univ f)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
private theorem cnt_prod {α β : Type*} [Fintype α] [Fintype β]
    (P : α → Prop) (Q : α → β → Prop) (k : ℕ)
    (h : ∀ x, P x → cnt (Q x) = k) :
    cnt (fun x : α × β => P x.1 ∧ Q x.1 x.2) = cnt P * k := by
  classical
  rw [← cnt_partition (fun x : α × β => P x.1 ∧ Q x.1 x.2) Prod.fst]
  have hf (x : α) :
      cnt (fun z : α × β => (P z.1 ∧ Q z.1 z.2) ∧ z.1 = x) =
        if P x then k else 0 := by
    rw [cnt_filter]
    by_cases hx : P x
    · rw [if_pos hx, ← h x hx, cnt_filter]
      have hset : (Finset.univ.filter
            (fun z : α × β => (P z.1 ∧ Q z.1 z.2) ∧ z.1 = x)) =
          ({x} : Finset α) ×ˢ (Finset.univ.filter (Q x)) := by
        ext z
        rcases z with ⟨y, z⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
          Finset.mem_singleton]
        constructor
        · rintro ⟨⟨_, hz⟩, rfl⟩
          exact ⟨rfl, hz⟩
        · rintro ⟨rfl, hz⟩
          exact ⟨⟨hx, hz⟩, rfl⟩
      rw [hset, Finset.card_product, Finset.card_singleton, one_mul]
    · rw [if_neg hx]
      apply Finset.card_eq_zero.mpr
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨⟨hp, _⟩, he⟩
      exact hx (he ▸ hp)
  simp_rw [hf]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Nat.nsmul_eq_mul,
    cnt_filter]

private theorem cnt_notMem {α : Type*} [Fintype α] [DecidableEq α] (s : Finset α) :
    cnt (fun x => x ∉ s) = Fintype.card α - s.card := by
  rw [cnt_filter]
  have h : (Finset.univ.filter (fun x => x ∉ s)) = Finset.univ \ s := by
    ext x
    simp
  rw [h, Finset.card_sdiff_of_subset (Finset.subset_univ s)] <;> rfl

private abbrev Triple (α : Type*) := α × α × α

private def rotate {α : Type*} : Triple α ≃ Triple α where
  toFun t := (t.2.1, t.2.2, t.1)
  invFun t := (t.2.2, t.1, t.2.1)
  left_inv := by rintro ⟨x, y, z⟩; rfl
  right_inv := by rintro ⟨x, y, z⟩; rfl

private def badThree {α : Type*} (c : α → α) (t : Triple α) : Prop :=
  c t.1 ≠ t.2.1 ∧ c t.2.1 ≠ t.2.2 ∧ c t.2.2 ≠ t.1

private def distinctThree {α : Type*} (t : Triple α) : Prop :=
  t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.2.2 ≠ t.1

private def same {α : Type*} (t : Triple α) : Prop :=
  t.1 = t.2.1 ∧ t.2.1 = t.2.2

private def repeatFirst {α : Type*} (t : Triple α) : Prop :=
  t.1 = t.2.1 ∧ t.2.1 ≠ t.2.2

private def repeatSecond {α : Type*} (t : Triple α) : Prop :=
  repeatFirst (rotate t)

private def repeatThird {α : Type*} (t : Triple α) : Prop :=
  repeatSecond (rotate t)

private def nextBad {α : Type*} (c : α → α) (t : Triple α) (w : α) : Prop :=
  w ≠ c t.1 ∧ w ≠ c t.2.1 ∧ w ≠ c t.2.2

private theorem comp_swap {α : Type*} {c : α → α} (hc : Function.Involutive c)
    (x y : α) : c x = y ↔ c y = x := by
  constructor
  · intro h
    rw [← h, hc x]
  · intro h
    rw [← h, hc y]

section Counting

variable {α : Type*} [Fintype α] (c : α → α) (hc : Function.Involutive c)

private theorem cnt_two_letters :
    cnt (fun p : α × α => c p.1 ≠ p.1 ∧ (p.2 ≠ p.1 ∧ p.2 ≠ c p.1)) =
      cnt (fun x => c x ≠ x) * (Fintype.card α - 2) := by
  classical
  refine cnt_prod (fun x : α => c x ≠ x) (fun x y => y ≠ x ∧ y ≠ c x)
    (Fintype.card α - 2) ?_
  intro x hx
  calc
    _ = cnt (fun y => y ∉ ({x, c x} : Finset α)) := by
      exact cnt_congr fun y => by simp [not_or]
    _ = _ := by rw [cnt_notMem, Finset.card_pair_eq_two_iff.mpr (Ne.symm hx)]

private theorem cnt_same :
    cnt (fun t => badThree c t ∧ same t) = cnt (fun x => c x ≠ x) := by
  apply Nat.card_congr
  refine
    { toFun := fun x => ⟨x.val.1, x.property.1.1.trans_eq x.property.2.1.symm⟩
      invFun := fun x => ⟨(x.val, x.val, x.val), ⟨x.property, x.property, x.property⟩, rfl, rfl⟩
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨⟨x, y, z⟩, _, hxy, hyz⟩
    change x = y at hxy
    subst y
    change x = z at hyz
    subst z
    rfl
  · intro x
    rfl

include hc in
private theorem cnt_repeat :
    cnt (fun t => badThree c t ∧ repeatFirst t) =
      cnt (fun x => c x ≠ x) * (Fintype.card α - 2) := by
  classical
  rw [← cnt_two_letters c]
  apply Nat.card_congr
  refine
    { toFun := fun t => ⟨(t.val.1, t.val.2.2), by
        have he : t.val.1 = t.val.2.1 := t.property.2.1
        have h₁ : c t.val.1 ≠ t.val.2.1 := t.property.1.1
        have h₂ : c t.val.2.1 ≠ t.val.2.2 := t.property.1.2.1
        have h₃ : t.val.2.1 ≠ t.val.2.2 := t.property.2.2
        exact ⟨h₁.trans_eq he.symm, Ne.symm (he.trans_ne h₃),
          Ne.symm ((congrArg c he).trans_ne h₂)⟩⟩
      invFun := fun p => ⟨(p.val.1, p.val.1, p.val.2), by
        have hx : c p.val.1 ≠ p.val.1 := p.property.1
        have hz : p.val.2 ≠ p.val.1 := p.property.2.1
        have hcz : c p.val.1 ≠ p.val.2 := Ne.symm p.property.2.2
        exact ⟨⟨hx, hcz, fun h => hcz ((comp_swap hc _ _).mp h)⟩, rfl, Ne.symm hz⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro t
    apply Subtype.ext
    change (t.val.1, t.val.1, t.val.2.2) = t.val
    rcases t with ⟨⟨x, y, z⟩, ht⟩
    have he : x = y := ht.2.1
    subst y
    rfl
  · rintro ⟨⟨x, z⟩, _⟩
    rfl

private theorem cnt_rotate (P : Triple α → Prop) :
    cnt (fun t => badThree c t ∧ P (rotate t)) = cnt (fun t => badThree c t ∧ P t) := by
  apply cnt_equiv rotate
  rintro ⟨x, y, z⟩
  change ((c x ≠ y ∧ c y ≠ z ∧ c z ≠ x) ∧ P (y, z, x)) ↔
    ((c y ≠ z ∧ c z ≠ x ∧ c x ≠ y) ∧ P (y, z, x))
  tauto

private theorem cnt_distinct_all :
    cnt (distinctThree : Triple α → Prop) = Fintype.card α * (Fintype.card α - 1) *
      (Fintype.card α - 2) := by
  classical
  have hp : cnt (fun p : α × α => p.1 ≠ p.2) =
      Fintype.card α * (Fintype.card α - 1) := by
    calc
      _ = cnt (fun p : α × α => True ∧ p.2 ∉ ({p.1} : Finset α)) := by
        apply cnt_congr
        intro p
        simp [ne_comm]
      _ = cnt (fun _ : α => True) * (Fintype.card α - 1) := by
        refine cnt_prod (fun _ : α => True) (fun x y => y ∉ ({x} : Finset α))
          (Fintype.card α - 1) ?_
        intro x _
        rw [cnt_notMem, Finset.card_singleton]
      _ = _ := by simp [cnt_filter]
  calc
    _ = cnt (fun p : (α × α) × α =>
          p.1.1 ≠ p.1.2 ∧ p.2 ∉ ({p.1.1, p.1.2} : Finset α)) := by
        apply cnt_equiv (Equiv.prodAssoc α α α).symm
        rintro ⟨x, y, z⟩
        change (x ≠ y ∧ y ≠ z ∧ z ≠ x) ↔ x ≠ y ∧ z ∉ ({x, y} : Finset α)
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        constructor
        · rintro ⟨hxy, hyz, hzx⟩
          exact ⟨hxy, hzx, Ne.symm hyz⟩
        · rintro ⟨hxy, hzx, hzy⟩
          exact ⟨hxy, Ne.symm hzy, hzx⟩
    _ = cnt (fun p : α × α => p.1 ≠ p.2) * (Fintype.card α - 2) := by
        refine cnt_prod (fun p : α × α => p.1 ≠ p.2)
          (fun p y => y ∉ ({p.1, p.2} : Finset α)) (Fintype.card α - 2) ?_
        intro p h
        rw [cnt_notMem, Finset.card_pair_eq_two_iff.mpr h]
    _ = _ := by rw [hp]

private def edgeFirst {α : Type*} (c : α → α) (t : Triple α) : Prop :=
  distinctThree t ∧ c t.1 = t.2.1

private def edgeSecond {α : Type*} (c : α → α) (t : Triple α) : Prop :=
  edgeFirst c (rotate t)

private def edgeThird {α : Type*} (c : α → α) (t : Triple α) : Prop :=
  edgeSecond c (rotate t)

private theorem cnt_edge :
    cnt (edgeFirst c) = cnt (fun x => c x ≠ x) * (Fintype.card α - 2) := by
  classical
  rw [← cnt_two_letters c]
  apply Nat.card_congr
  refine
    { toFun := fun t => ⟨(t.val.1, t.val.2.2), by
        have he : c t.val.1 = t.val.2.1 := t.property.2
        have hxy : t.val.1 ≠ t.val.2.1 := t.property.1.1
        have hyz : t.val.2.1 ≠ t.val.2.2 := t.property.1.2.1
        have hzx : t.val.2.2 ≠ t.val.1 := t.property.1.2.2
        exact ⟨Ne.symm (hxy.trans_eq he.symm), hzx, Ne.symm (he.trans_ne hyz)⟩⟩
      invFun := fun p => ⟨(p.val.1, c p.val.1, p.val.2),
        ⟨⟨Ne.symm p.property.1, Ne.symm p.property.2.2, p.property.2.1⟩, rfl⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro t
    apply Subtype.ext
    change (t.val.1, c t.val.1, t.val.2.2) = t.val
    rcases t with ⟨⟨x, y, z⟩, ht⟩
    have he : c x = y := ht.2
    subst y
    rfl
  · rintro ⟨⟨x, z⟩, _⟩
    rfl

include hc in
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
private theorem cnt_distinct_bad :
    cnt (fun t => badThree c t ∧ distinctThree t) +
      3 * (cnt (fun x => c x ≠ x) * (Fintype.card α - 2)) =
        Fintype.card α * (Fintype.card α - 1) * (Fintype.card α - 2) := by
  have h₁ : ∀ t, edgeFirst c t → ¬ edgeSecond c t := by
    rintro ⟨x, y, z⟩ ⟨⟨_, _, hzx⟩, hxy⟩ ⟨_, hyz⟩
    have hz : z = x := calc
      z = c y := hyz.symm
      _ = c (c x) := congrArg c hxy.symm
      _ = x := hc x
    exact hzx hz
  have h₂ : ∀ t, edgeSecond c t → ¬ edgeThird c t :=
    fun t => h₁ (rotate t)
  have h₃ : ∀ t, edgeThird c t → ¬ edgeFirst c t := by
    rintro ⟨x, y, z⟩ ⟨⟨_, _, hyz⟩, hzx⟩ ⟨_, hxy⟩
    change y ≠ z at hyz
    have he : y = z := calc
      y = c x := hxy.symm
      _ = c (c z) := congrArg c hzx.symm
      _ = z := hc z
    exact hyz he
  have hd := cnt_disj _ _ h₁
  have hd' := cnt_disj (fun t => edgeFirst c t ∨ edgeSecond c t) (edgeThird c)
    (fun t h ht => h.elim (h₃ t ht) (fun hs => h₂ t hs ht))
  have he₂ : cnt (edgeSecond c) = cnt (edgeFirst c) := cnt_equiv rotate (fun _ => Iff.rfl)
  have he₃ : cnt (edgeThird c) = cnt (edgeSecond c) := cnt_equiv rotate (fun _ => Iff.rfl)
  have hs := cnt_split (distinctThree : Triple α → Prop) (badThree c)
  have ha : cnt (fun t => distinctThree t ∧ badThree c t) =
      cnt (fun t => badThree c t ∧ distinctThree t) :=
    cnt_congr (fun _ => and_comm)
  have hb : cnt (fun t => distinctThree t ∧ ¬ badThree c t) =
      cnt (fun t => (edgeFirst c t ∨ edgeSecond c t) ∨ edgeThird c t) := by
    apply cnt_congr
    rintro ⟨x, y, z⟩
    change ((x ≠ y ∧ y ≠ z ∧ z ≠ x) ∧ ¬ (c x ≠ y ∧ c y ≠ z ∧ c z ≠ x)) ↔
      (((x ≠ y ∧ y ≠ z ∧ z ≠ x) ∧ c x = y) ∨
       ((y ≠ z ∧ z ≠ x ∧ x ≠ y) ∧ c y = z)) ∨
       ((z ≠ x ∧ x ≠ y ∧ y ≠ z) ∧ c z = x)
    classical
    tauto
  rw [ha, hb, hd', hd, he₃, he₂, cnt_edge c, cnt_distinct_all] at hs
  omega

end Counting

private noncomputable def shape {α : Type*} (t : Triple α) : Fin 5 := by
  classical
  exact if t.1 = t.2.1 then (if t.2.1 = t.2.2 then 0 else 1)
    else if t.2.1 = t.2.2 then 2 else if t.2.2 = t.1 then 3 else 4

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
private theorem shape_spec {α : Type*} (t : Triple α) :
    (shape t = 0 ↔ same t) ∧
    (shape t = 1 ↔ repeatFirst t) ∧
    (shape t = 2 ↔ repeatSecond t) ∧
    (shape t = 3 ↔ repeatThird t) ∧
    (shape t = 4 ↔ distinctThree t) := by
  classical
  rcases t with ⟨x, y, z⟩
  by_cases hxy : x = y <;> by_cases hyz : y = z <;> by_cases hzx : z = x <;>
    simp_all [shape, same, repeatFirst, repeatSecond, repeatThird, rotate, distinctThree, eq_comm]

private noncomputable def tripleSize {α : Type*} (t : Triple α) : ℕ :=
  if shape t = 0 then 1 else if shape t = 4 then 3 else 2

private theorem cnt_next {α : Type*} [Fintype α] (c : α → α)
    (hc : Function.Involutive c) (t : Triple α) :
    cnt (nextBad c t) = Fintype.card α - tripleSize t := by
  classical
  rcases t with ⟨x, y, z⟩
  have h₁ : cnt (nextBad c (x, y, z)) =
      cnt (fun w => w ∉ ({x, y, z} : Finset α).image c) := by
    apply cnt_congr
    intro w
    simp [nextBad, Finset.image_insert, Finset.image_singleton, not_or]
  rw [h₁, cnt_notMem, Finset.card_image_of_injective _ hc.injective]
  congr 1
  simp only [tripleSize, (shape_spec (x, y, z)).1, (shape_spec (x, y, z)).2.2.2.2,
    same, distinctThree]
  by_cases hxy : x = y
  · subst y
    by_cases hxz : x = z
    · subst z
      simp
    · simp [hxz, Finset.card_pair hxz]
  · by_cases hyz : y = z
    · subst z
      simp [hxy, Finset.card_pair hxy]
    · by_cases hzx : z = x
      · subst z
        rw [Finset.insert_comm x y ({x} : Finset α)]
        simp [hxy, Finset.card_pair hyz]
      · have hcard : ({x, y, z} : Finset α).card = 3 :=
          Finset.card_triple_eq_three_iff.mpr ⟨hxy, Ne.symm hzx, hyz⟩
        simp [hcard, hxy, hyz, hzx]

private def badFour {α : Type*} (c : α → α) (p : Triple α × α) : Prop :=
  badThree c p.1 ∧ nextBad c p.1 p.2

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
private theorem cnt_four_bad {α : Type*} [Fintype α] (c : α → α)
    (hc : Function.Involutive c) :
    cnt (badFour c) =
      cnt (fun x => c x ≠ x) * (Fintype.card α - 1) +
      3 * (cnt (fun x => c x ≠ x) * (Fintype.card α - 2)) * (Fintype.card α - 2) +
      cnt (fun t => badThree c t ∧ distinctThree t) * (Fintype.card α - 3) := by
  classical
  have hf (k : Fin 5) (P : Triple α → Prop) (hP : ∀ t, shape t = k ↔ P t) :
      cnt (fun p : Triple α × α => badFour c p ∧ shape p.1 = k) =
        cnt (fun t => badThree c t ∧ P t) *
          (Fintype.card α - (if k = 0 then 1 else if k = 4 then 3 else 2)) := by
    calc
      _ = cnt (fun p : Triple α × α => (badThree c p.1 ∧ P p.1) ∧ nextBad c p.1 p.2) := by
        apply cnt_congr
        intro p
        rw [hP]
        unfold badFour
        tauto
      _ = _ := by
        refine cnt_prod (fun t : Triple α => badThree c t ∧ P t) (nextBad c)
          (Fintype.card α - (if k = 0 then 1 else if k = 4 then 3 else 2)) ?_
        intro t ht
        have hk : shape t = k := (hP t).mpr ht.2
        rw [cnt_next c hc, tripleSize, hk]
  have hsum (F : Fin 5 → ℕ) :
      (∑ k : Fin 5, F k) = F 0 + (F 1 + (F 2 + (F 3 + F 4))) := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] <;> rfl
  have h := cnt_partition (badFour c) (fun p => shape p.1)
  rw [hsum,
    hf 0 same (fun t => (shape_spec t).1),
    hf 1 repeatFirst (fun t => (shape_spec t).2.1),
    hf 2 repeatSecond (fun t => (shape_spec t).2.2.1),
    hf 3 repeatThird (fun t => (shape_spec t).2.2.2.1),
    hf 4 distinctThree (fun t => (shape_spec t).2.2.2.2)] at h
  have h₂ : cnt (fun t => badThree c t ∧ repeatSecond t) =
      cnt (fun t => badThree c t ∧ repeatFirst t) := cnt_rotate c repeatFirst
  have h₃ : cnt (fun t => badThree c t ∧ repeatThird t) =
      cnt (fun t => badThree c t ∧ repeatSecond t) := cnt_rotate c repeatSecond
  rw [h₃, h₂, cnt_same c, cnt_repeat c hc] at h
  simp only [if_true,
    if_neg (by decide : (1 : Fin 5) ≠ 0), if_neg (by decide : (1 : Fin 5) ≠ 4),
    if_neg (by decide : (2 : Fin 5) ≠ 0), if_neg (by decide : (2 : Fin 5) ≠ 4),
    if_neg (by decide : (3 : Fin 5) ≠ 0), if_neg (by decide : (3 : Fin 5) ≠ 4),
    if_neg (by decide : (4 : Fin 5) ≠ 0)] at h
  rw [← h]
  ring

private def complement {n : ℕ} (x : Fin (n + 1)) : Fin (n + 1) :=
  ⟨n - x.val, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩

private theorem complement_involutive (n : ℕ) :
    Function.Involutive (@complement n) := by
  intro x
  apply Fin.ext
  change n - (n - x.val) = x.val
  have hx := x.isLt
  omega

private theorem complement_iff {n : ℕ} (x y : Fin (n + 1)) :
    complement x = y ↔ (x : ℕ) + (y : ℕ) = n := by
  rw [← Fin.val_inj]
  change n - x.val = y.val ↔ x.val + y.val = n
  have hx := x.isLt
  omega

private def fixedCount (n : ℕ) : ℕ := if n % 2 = 0 then 1 else 0

private theorem cnt_unfixed (n : ℕ) :
    cnt (fun x : Fin (n + 1) => complement x ≠ x) = n + 1 - fixedCount n := by
  classical
  have ht := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (n + 1)))) (fun x => complement x = x)
  have hp : (Finset.univ.filter (fun x : Fin (n + 1) => complement x = x)).card =
      fixedCount n := by
    by_cases hn : n % 2 = 0
    · let m : Fin (n + 1) := ⟨n / 2, by omega⟩
      have he : (Finset.univ.filter (fun x : Fin (n + 1) => complement x = x)) =
          {m} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        rw [complement_iff x x, ← Fin.val_inj]
        change x.val + x.val = n ↔ x.val = n / 2
        omega
      rw [he, Finset.card_singleton]
      simp [fixedCount, hn]
    · have he : (Finset.univ.filter (fun x : Fin (n + 1) => complement x = x)) =
          ∅ := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, complement_iff,
          Finset.notMem_empty, iff_false]
        omega
      rw [he, Finset.card_empty]
      simp [fixedCount, hn]
  have hu : (Finset.univ : Finset (Fin (n + 1))).card = n + 1 := by simp
  have htotal : fixedCount n + cnt (fun x : Fin (n + 1) => complement x ≠ x) = n + 1 := by
    calc
      _ = (Finset.univ.filter (fun x : Fin (n + 1) => complement x = x)).card +
          (Finset.univ.filter (fun x : Fin (n + 1) => complement x ≠ x)).card := by
        rw [hp, cnt_filter (fun x : Fin (n + 1) => complement x ≠ x)]
      _ = (Finset.univ : Finset (Fin (n + 1))).card := ht
      _ = n + 1 := hu
  omega

private def arrayEquiv (n : ℕ) :
    (Fin 4 → Fin (n + 1)) ≃ Triple (Fin (n + 1)) × Fin (n + 1) where
  toFun x := ((x 0, x 1, x 2), x 3)
  invFun p := ![p.1.1, p.1.2.1, p.1.2.2, p.2]
  left_inv := by intro x; funext i; fin_cases i <;> rfl
  right_inv := by rintro ⟨⟨x, y, z⟩, w⟩; rfl

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
private theorem good_iff_pairs {n : ℕ} (x : Fin 4 → Fin (n + 1)) :
    good x = true ↔
      (x 0 : ℕ) + (x 1 : ℕ) = n ∨ (x 0 : ℕ) + (x 2 : ℕ) = n ∨
      (x 0 : ℕ) + (x 3 : ℕ) = n ∨ (x 1 : ℕ) + (x 2 : ℕ) = n ∨
      (x 1 : ℕ) + (x 3 : ℕ) = n ∨ (x 2 : ℕ) + (x 3 : ℕ) = n := by
  unfold good
  rw [decide_eq_true_eq]
  have hget (i : Fin 4) : get x (0 + i.val) = (x i : ℕ) := by
    simp [get, i.isLt]
  constructor
  · intro h
    have hp (i j : Fin 4) (hij : i < j) (h : (x i : ℕ) + (x j : ℕ) = n) :
        (x 0 : ℕ) + (x 1 : ℕ) = n ∨ (x 0 : ℕ) + (x 2 : ℕ) = n ∨
        (x 0 : ℕ) + (x 3 : ℕ) = n ∨ (x 1 : ℕ) + (x 2 : ℕ) = n ∨
        (x 1 : ℕ) + (x 3 : ℕ) = n ∨ (x 2 : ℕ) + (x 3 : ℕ) = n := by
      fin_cases i <;> fin_cases j <;> norm_num [Fin.lt_def] at hij <;>
        first
        | exact Or.inl h
        | exact Or.inr (Or.inl h)
        | exact Or.inr (Or.inr (Or.inl h))
        | exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

    obtain ⟨s, hs, t, ht, hst, he⟩ := h 0 (by omega)
    let i : Fin 4 := ⟨s, hs⟩
    let j : Fin 4 := ⟨t, ht⟩
    change get x (0 + i.val) + get x (0 + j.val) = n at he
    rw [hget i, hget j] at he
    exact hp i j hst he
  · intro h u hu
    have hu₀ : u = 0 := by omega
    subst u
    have hp (i j : Fin 4) (hij : i < j) (he : (x i : ℕ) + (x j : ℕ) = n) :
        ∃ s < (4 : ℕ), ∃ t < (4 : ℕ), s < t ∧ get x (0 + s) + get x (0 + t) = n := by
      exact ⟨i.val, i.isLt, j.val, j.isLt, hij, by rw [hget i, hget j]; exact he⟩
    rcases h with h | h | h | h | h | h
    · exact hp 0 1 (by decide) h
    · exact hp 0 2 (by decide) h
    · exact hp 0 3 (by decide) h
    · exact hp 1 2 (by decide) h
    · exact hp 1 3 (by decide) h
    · exact hp 2 3 (by decide) h

private theorem cnt_good_add_bad (n : ℕ) :
    cnt (fun x : Fin 4 → Fin (n + 1) => good x = true) +
      cnt (badFour (@complement n)) = (n + 1) ^ 4 := by
  classical
  have hb : cnt (fun x : Fin 4 → Fin (n + 1) => ¬ good x = true) =
      cnt (badFour (@complement n)) := by
    apply cnt_equiv (arrayEquiv n)
    intro x
    rw [good_iff_pairs]
    change ¬ _ ↔
      (complement (x 0) ≠ x 1 ∧ complement (x 1) ≠ x 2 ∧ complement (x 2) ≠ x 0) ∧
      (x 3 ≠ complement (x 0) ∧ x 3 ≠ complement (x 1) ∧ x 3 ≠ complement (x 2))
    have h₀ : x 3 ≠ complement (x 0) ↔ ¬ ((x 0 : ℕ) + (x 3 : ℕ) = n) :=
      ne_comm.trans (not_congr (complement_iff _ _))
    have h₁ : x 3 ≠ complement (x 1) ↔ ¬ ((x 1 : ℕ) + (x 3 : ℕ) = n) :=
      ne_comm.trans (not_congr (complement_iff _ _))
    have h₂ : x 3 ≠ complement (x 2) ↔ ¬ ((x 2 : ℕ) + (x 3 : ℕ) = n) :=
      ne_comm.trans (not_congr (complement_iff _ _))
    simp only [h₀, h₁, h₂, Ne, complement_iff, Nat.add_comm (x 2 : ℕ) (x 0 : ℕ)]
    tauto
  rw [← hb]
  simp only [cnt_filter]
  rw [Finset.card_filter_add_card_filter_not]
  simp

private theorem a_as_count (n : ℕ) :
    (a n : ℚ) = (cnt (fun x : Fin 4 → Fin (n + 1) => good x = true) : ℚ) := by
  have hf : (Finset.univ.filter (fun x : Fin 4 → Fin (n + 1) => good x)) =
      (Finset.univ.filter (fun x : Fin 4 → Fin (n + 1) => good x = true)) :=
    Finset.filter_congr (fun _ _ => Iff.rfl)
  rw [cnt_filter, a, Int.cast_natCast, hf]

private def value (n : ℕ) : ℚ :=
  (if n % 2 = 0 then 1 + 5 * (n : ℚ) else 4 + (n : ℚ)) +
    3 * (n : ℚ) ^ 2 + 6 * (n : ℚ) ^ 3

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
private theorem a_value (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = value n := by
  let q := n + 1
  let r := q - fixedCount n
  let b := cnt (fun t => badThree (@complement n) t ∧ distinctThree t)
  let g := cnt (fun x : Fin 4 → Fin (n + 1) => good x = true)
  have h₁ : g + (r * (q - 1) + 3 * (r * (q - 2)) * (q - 2) + b * (q - 3)) = q ^ 4 := by
    simpa only [cnt_four_bad _ (complement_involutive n), cnt_unfixed, Fintype.card_fin] using
      cnt_good_add_bad n
  have h₂ : b + 3 * (r * (q - 2)) = q * (q - 1) * (q - 2) := by
    simpa only [cnt_unfixed, Fintype.card_fin] using
      cnt_distinct_bad (@complement n) (complement_involutive n)
  by_cases hs : n = 1
  · subst n
    norm_num [q, r, fixedCount] at h₁
    have hg : g = 14 := by omega
    rw [a_as_count]
    change (g : ℚ) = value 1
    rw [hg]
    norm_num [value]
  · have hq₁ : 1 ≤ q := by dsimp [q]; omega
    have hq₂ : 2 ≤ q := by dsimp [q]; omega
    have hq₃ : 3 ≤ q := by dsimp [q]; omega
    have hf : fixedCount n ≤ q := by
      unfold fixedCount
      split_ifs <;> omega
    have hq : (q : ℚ) = (n : ℚ) + 1 := by simp [q]
    have hr : (r : ℚ) = (n : ℚ) + 1 - (fixedCount n : ℚ) := by
      change ((q - fixedCount n : ℕ) : ℚ) = _
      rw [Nat.cast_sub hf, hq]
    have h₁q := congrArg (fun m : ℕ => (m : ℚ)) h₁
    have h₂q := congrArg (fun m : ℕ => (m : ℚ)) h₂
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hq₁,
      Nat.cast_sub hq₂, Nat.cast_sub hq₃, Nat.cast_ofNat, Nat.cast_one, hq, hr] at h₁q h₂q
    rw [a_as_count]
    change (g : ℚ) = value n
    by_cases he : n % 2 = 0
    · norm_num [fixedCount, value, he] at h₁q h₂q ⊢
      linear_combination h₁q - ((n : ℚ) + 1 - 3) * h₂q
    · norm_num [fixedCount, value, he] at h₁q h₂q ⊢
      linear_combination h₁q - ((n : ℚ) + 1 - 3) * h₂q

open PowerSeries

private def seriesValues (n : ℕ) : ℚ := if n < 1 then 0 else value n

private def shift (n k : ℕ) : ℚ := if k ≤ n then seriesValues (n - k) else 0

private theorem denominator_coeff (n : ℕ) :
    coeff n (mk seriesValues * ((1 - X) ^ 4 * (1 + X) ^ 2 : PowerSeries ℚ)) =
      seriesValues n - 2 * shift n 1 - shift n 2 + 4 * shift n 3 -
        shift n 4 - 2 * shift n 5 + shift n 6 := by
  let A : PowerSeries ℚ := mk seriesValues
  have he : A * ((1 - X) ^ 4 * (1 + X) ^ 2) =
      A - C 2 * (A * X ^ 1) - A * X ^ 2 + C 4 * (A * X ^ 3) -
        A * X ^ 4 - C 2 * (A * X ^ 5) + A * X ^ 6 := by
    simp only [map_ofNat]
    ring
  change coeff n (A * ((1 - X) ^ 4 * (1 + X) ^ 2)) = _
  rw [he]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', A, coeff_mk, shift]

private theorem numerator_coeff (n : ℕ) :
    coeff n (X * (14 + 43 * X + 40 * X ^ 2 + 46 * X ^ 3 + 2 * X ^ 4 - X ^ 5) :
      PowerSeries ℚ) =
      (if n = 1 then 14 else 0) + (if n = 2 then 43 else 0) +
      (if n = 3 then 40 else 0) + (if n = 4 then 46 else 0) +
      (if n = 5 then 2 else 0) - (if n = 6 then 1 else 0) := by
  have he : X * (14 + 43 * X + 40 * X ^ 2 + 46 * X ^ 3 + 2 * X ^ 4 - X ^ 5) =
      (C 14 * X ^ 1 + C 43 * X ^ 2 + C 40 * X ^ 3 + C 46 * X ^ 4 +
        C 2 * X ^ 5 - C 1 * X ^ 6 : PowerSeries ℚ) := by
    simp only [map_ofNat, map_one]
    ring
  rw [he]
  simp only [map_add, map_sub, coeff_C_mul_X_pow]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
private theorem recurrence (n : ℕ) :
    seriesValues n - 2 * shift n 1 - shift n 2 + 4 * shift n 3 -
        shift n 4 - 2 * shift n 5 + shift n 6 =
      (if n = 1 then 14 else 0) + (if n = 2 then 43 else 0) +
      (if n = 3 then 40 else 0) + (if n = 4 then 46 else 0) +
      (if n = 5 then 2 else 0) - (if n = 6 then 1 else 0) := by
  by_cases hn : n ≤ 6
  · interval_cases n <;> norm_num [seriesValues, shift, value]
  · have hs (k : ℕ) (hk : k ≤ 6) : shift n k = value (n - k) := by
      simp [shift, seriesValues, show k ≤ n by omega, show ¬ n - k < 1 by omega]
    have hv : seriesValues n = value n := by simp [seriesValues, show ¬ n < 1 by omega]
    have hc (k : ℕ) (hk : k ≤ 6) : ((n - k : ℕ) : ℚ) = (n : ℚ) - (k : ℚ) :=
      Nat.cast_sub (by omega)
    have hd (k : ℕ) (hk : k ≤ 6) : n ≠ k := by omega
    rw [hv, hs 1 (by decide), hs 2 (by decide), hs 3 (by decide), hs 4 (by decide),
      hs 5 (by decide), hs 6 (by decide)]
    simp only [if_neg (hd 1 (by decide)), if_neg (hd 2 (by decide)),
      if_neg (hd 3 (by decide)), if_neg (hd 4 (by decide)), if_neg (hd 5 (by decide)),
      if_neg (hd 6 (by decide))]
    by_cases hp : n % 2 = 0
    · have h₁ : (n - 1) % 2 ≠ 0 := by omega
      have h₂ : (n - 2) % 2 = 0 := by omega
      have h₃ : (n - 3) % 2 ≠ 0 := by omega
      have h₄ : (n - 4) % 2 = 0 := by omega
      have h₅ : (n - 5) % 2 ≠ 0 := by omega
      have h₆ : (n - 6) % 2 = 0 := by omega
      simp only [value, if_pos hp, if_neg h₁, if_pos h₂, if_neg h₃, if_pos h₄,
        if_neg h₅, if_pos h₆, hc 1 (by decide), hc 2 (by decide), hc 3 (by decide),
        hc 4 (by decide), hc 5 (by decide), hc 6 (by decide), Nat.cast_ofNat, Nat.cast_one]
      ring
    · have h₁ : (n - 1) % 2 = 0 := by omega
      have h₂ : (n - 2) % 2 ≠ 0 := by omega
      have h₃ : (n - 3) % 2 = 0 := by omega
      have h₄ : (n - 4) % 2 ≠ 0 := by omega
      have h₅ : (n - 5) % 2 = 0 := by omega
      have h₆ : (n - 6) % 2 ≠ 0 := by omega
      simp only [value, if_neg hp, if_pos h₁, if_neg h₂, if_pos h₃, if_neg h₄,
        if_pos h₅, if_neg h₆, hc 1 (by decide), hc 2 (by decide), hc 3 (by decide),
        hc 4 (by decide), hc 5 (by decide), hc 6 (by decide), Nat.cast_ofNat, Nat.cast_one]
      ring

private theorem generating :
    (mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 4 * (1 + X) ^ 2 :
      PowerSeries ℚ)) = X * (14 + 43 * X + 40 * X ^ 2 + 46 * X ^ 3 + 2 * X ^ 4 - X ^ 5) := by
  have hv : (fun n => if n < 1 then 0 else (a n : ℚ)) = seriesValues := by
    funext n
    unfold seriesValues
    by_cases hn : n < 1
    · simp [hn]
    · simp [hn, a_value n (by omega)]
  rw [hv]
  apply PowerSeries.ext
  intro n
  rw [denominator_coeff, numerator_coeff]
  exact recurrence n

theorem parityAndGeneratingFunction : type_of% @OMA.S_oeis_a245951.main := by
  refine ⟨generating, ?_, ?_⟩
  · intro n hn he
    rw [a_value n hn]
    simp [value, Nat.even_iff.mp he]
  · intro n hn ho
    have h : n % 2 ≠ 0 := by have hh := Nat.odd_iff.mp ho; omega
    rw [a_value n hn]
    simp [value, h]

end OMA.S_oeis_a245951

theorem OMA.solution : type_of% @OMA.S_oeis_a245951.main :=
  OMA.S_oeis_a245951.parityAndGeneratingFunction
