import OMAStatements.S_oeis_a249713
import Mathlib

namespace OMA.Ties249713
open OMA.S_oeis_a249713 Finset PowerSeries

private def lower {W : ℕ} (y : Fin W → ℕ) (v : ℕ) := univ.filter (fun i => y i < v)
private def upto {W : ℕ} (y : Fin W → ℕ) (v : ℕ) := univ.filter (fun i => y i ≤ v)
private def cross {W : ℕ} (y : Fin W → ℕ) (k v : ℕ) := (lower y v).card < k ∧ k < (upto y v).card

/-- A tie at the cut means fewer than k entries are strictly below v and more than k are at most v. -/
private theorem tie_iff {W k v : ℕ} (y : Fin W → ℕ) :
    (∃ S : Finset (Fin W), S.card = k ∧ (∀ i ∈ S, y i ≤ v) ∧ (∃ i ∈ S, y i = v) ∧
      (∀ i ∉ S, v ≤ y i) ∧ (∃ i ∉ S, y i = v)) ↔ cross y k v := by
  have il (i) : i ∈ lower y v ↔ y i < v := by simp [lower]
  have iu (i) : i ∈ upto y v ↔ y i ≤ v := by simp [upto]
  constructor
  · rintro ⟨S,hS,hlo,⟨i,hi,ei⟩,hhi,⟨j,hj,ej⟩⟩
    have hls : lower y v ⊆ S := by
      intro a ha
      by_contra hn
      exact ((il a).mp ha).not_ge (hhi a hn)
    have hsu : S ⊆ upto y v := fun a ha => (iu a).mpr (hlo a ha)
    rw [← hS]
    refine ⟨card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hls,?_⟩),
      card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsu,?_⟩)⟩
    · intro e
      have hh := (il i).mp (e.symm ▸ hi)
      omega
    · intro e
      exact hj (e.symm ▸ (iu j).mpr ej.le)
  · rintro ⟨hl,hu⟩
    have sub : lower y v ⊆ upto y v := fun i hi => (iu i).mpr ((il i).mp hi).le
    obtain ⟨S,hls,hsu,hs⟩ := exists_subsuperset_card_eq sub hl.le hu.le
    have lo : ∃ i ∈ S, i ∉ lower y v := by
      by_contra! h
      have := card_le_card (show S ⊆ lower y v from h)
      omega
    have hi : ∃ j ∈ upto y v, j ∉ S := by
      by_contra! h
      have := card_le_card (show upto y v ⊆ S from h)
      omega
    obtain ⟨i,hi',hni⟩ := lo
    obtain ⟨j,hj,hnj⟩ := hi
    refine ⟨S,hs,fun a ha => (iu a).mp (hsu ha),⟨i,hi',?_⟩,?_,⟨j,hnj,?_⟩⟩
    · exact le_antisymm ((iu i).mp (hsu hi')) (le_of_not_gt (fun h => hni ((il i).mpr h)))
    · intro a ha
      exact le_of_not_gt (fun h => ha (hls ((il a).mpr h)))
    · exact le_antisymm ((iu j).mp hj) (le_of_not_gt (fun h => hnj (hls ((il j).mpr h))))

private def win {W : ℕ} (f : ℕ → ℕ) (i : ℕ) (t : Fin W) := f (i+t.val)
private theorem lower_sum {W : ℕ} (y : Fin W → ℕ) (v : ℕ) :
    (lower y v).card = ∑ t : Fin W, if y t < v then 1 else 0 := by simp [lower]
private theorem upto_sum {W : ℕ} (y : Fin W → ℕ) (v : ℕ) :
    (upto y v).card = ∑ t : Fin W, if y t ≤ v then 1 else 0 := by simp [upto]

/-- Sliding the window loses at most one of the entries counted at the lower threshold. -/
private theorem compareAdjacent (f : ℕ → ℕ) (i d v w : ℕ) (h : v < w) :
    (upto (win (W:=d+1) f i) v).card ≤ (lower (win (W:=d+1) f (i+1)) w).card + 1 ∧
    (upto (win (W:=d+1) f (i+1)) v).card ≤ (lower (win (W:=d+1) f i) w).card + 1 := by
  have shared : (∑ j : Fin d, if f (i+1+j.val) ≤ v then 1 else 0) ≤
      ∑ j : Fin d, if f (i+1+j.val) < w then 1 else 0 := by
    apply sum_le_sum
    intro j _
    split <;> split <;> omega
  have ind (p : Prop) [Decidable p] : (if p then 1 else 0 : ℕ) ≤ 1 := by split <;> decide
  simp only [upto_sum,lower_sum]
  constructor
  · rw [Fin.sum_univ_succ,Fin.sum_univ_castSucc]
    simp only [win,Fin.val_succ,Fin.val_castSucc,Fin.val_zero,Nat.add_zero,
      Nat.succ_add,Nat.add_succ] at shared ⊢
    have hh := Nat.add_le_add (ind (f i ≤ v)) shared
    exact hh.trans (by omega)
  · rw [Fin.sum_univ_castSucc,Fin.sum_univ_succ]
    simp only [win,Fin.val_succ,Fin.val_castSucc,Fin.val_zero,Nat.add_zero,
      Nat.succ_add,Nat.add_succ] at shared ⊢
    have hh := Nat.add_le_add shared (ind (f (i+(Fin.last d).val).succ ≤ v))
    exact hh.trans (Nat.succ_le_succ (Nat.le_add_left _ _))

private theorem adjacent {f : ℕ → ℕ} {i d k v w : ℕ}
    (hv : cross (win (W:=d+1) f i) k v) (hw : cross (win (W:=d+1) f (i+1)) k w) :
    v=w := by
  unfold cross at hv hw
  rcases lt_trichotomy v w with h | h | h
  · have := (compareAdjacent f i d v w h).1; omega
  · exact h
  · have := (compareAdjacent f i d w v h).2; omega

private theorem uniqueCut {W : ℕ} {y : Fin W → ℕ} {k v w : ℕ}
    (hv : cross y k v) (hw : cross y k w) : v=w := by
  have cmp (a b : ℕ) (h : a < b) : (upto y a).card ≤ (lower y b).card :=
    card_le_card (by
      intro i hi
      have hy : y i ≤ a := by simpa [upto] using hi
      simpa [lower] using (hy.trans_lt h))
  unfold cross at hv hw
  rcases lt_trichotomy v w with h | h | h
  · have := cmp _ _ h; omega
  · exact h
  · have := cmp _ _ h; omega


private abbrev Word (n : ℕ) := Fin 10 → Fin (n+1)
private abbrev Tag := Fin 3
private def tag (v x : ℕ) : Tag := if x < v then 0 else if x = v then 1 else 2
private def colors {n : ℕ} (v : Fin (n+1)) (x : Word n) : Fin 10 → Tag :=
  fun i => tag v.val (x i).val

private def bounds (c : Fin 10 → Tag) (i : Fin 7) : Prop :=
  let y (t : Fin 4) := c ⟨i.val+t.val,by omega⟩
  (∑ t, if y t = 0 then 1 else 0 : ℕ) < 2 ∧ 2 < (∑ t, if y t ≠ 2 then 1 else 0 : ℕ)

private def allowed (c : Fin 10 → Tag) := ∀ i, bounds c i
private instance (c : Fin 10 → Tag) : Decidable (allowed c) := by unfold allowed bounds; infer_instance

private theorem colored {n : ℕ} (v : Fin (n+1)) (x : Word n) (i : Fin 7) :
    bounds (colors v x) i ↔ cross (win (W:=4) (get x) i.val) 2 v.val := by
  have hzero (a : ℕ) : tag v.val a = 0 ↔ a < v.val := by
    unfold tag; split <;> (try split) <;> simp_all
  have htwo (a : ℕ) : tag v.val a ≠ 2 ↔ a ≤ v.val := by
    unfold tag; split <;> simp_all <;> omega
  have bound (t : Fin 4) : i.val+t.val < 10 := by omega
  simp only [bounds,colors,cross,lower_sum,upto_sum,win,hzero,htwo,OMA.S_oeis_a249713.get,
    dif_pos (bound _)]

private theorem witnesses {n : ℕ} (x : Word n) :
    good x = true ↔ ∀ i : Fin 7, ∃ v : Fin (n+1), cross (win (W:=4) (get x) i.val) 2 v.val := by
  simp only [good,decide_eq_true_eq,mem_powersetCard,subset_univ,true_and]
  constructor
  · intro h i
    obtain ⟨s,hs,v,hv,g⟩ := h i.val i.isLt
    exact ⟨⟨v,hv⟩,(tie_iff _).mp ⟨s,hs,g⟩⟩
  · intro h i hi
    obtain ⟨v,hv⟩ := h ⟨i,hi⟩
    obtain ⟨s,hs,g⟩ := (tie_iff _).mpr hv
    exact ⟨s,hs,v.val,v.isLt,g⟩

private theorem characterize {n : ℕ} (x : Word n) :
    good x = true ↔ ∃ v : Fin (n+1), allowed (colors v x) := by
  rw [witnesses]
  constructor
  · intro h
    obtain ⟨v,hv⟩ := h 0
    have same : ∀ i : Fin 7, ∀ w : Fin (n+1), cross (win (W:=4) (get x) i.val) 2 w.val → v = w := by
      intro i
      induction i using Fin.induction with
      | zero => intro w hw; exact Fin.ext (uniqueCut hv hw)
      | succ j ih =>
        intro w hw
        obtain ⟨u,hu⟩ := h j.castSucc
        exact (ih u hu).trans (Fin.ext (adjacent hu hw))
    refine ⟨v,fun i => (colored _ _ _).mpr ?_⟩
    obtain ⟨w,hw⟩ := h i
    exact same i w hw ▸ hw
  · rintro ⟨v,h⟩ i
    exact ⟨v,(colored _ _ _).mp (h i)⟩

private theorem uniqueValue {n : ℕ} {x : Word n} {v w : Fin (n+1)}
    (h : allowed (colors v x)) (g : allowed (colors w x)) : v = w :=
  Fin.ext (uniqueCut ((colored _ _ 0).mp (h 0)) ((colored _ _ 0).mp (g 0)))


private def weight (l h : ℕ) (c : Tag) := if c = 0 then l else if c = 1 then 1 else h
private theorem weightCard {n : ℕ} (v : Fin (n+1)) (c : Tag) :
    Fintype.card {x : Fin (n+1) // tag v.val x.val = c} = weight v.val (n-v.val) c := by
  rw [Fintype.card_subtype]
  fin_cases c
  · have eqset : univ.filter (fun x : Fin (n+1) => tag v.val x.val = 0) = Iio v := by
      ext x
      simp only [mem_filter,mem_univ,true_and,mem_Iio]
      change _ ↔ x.val < v.val
      unfold tag
      split <;> (try split) <;> simp_all
    exact (congrArg Finset.card eqset).trans (Fin.card_Iio _)
  · have eqset : univ.filter (fun x : Fin (n+1) => tag v.val x.val = 1) = {v} := by
      ext x
      simp only [mem_filter,mem_univ,true_and,mem_singleton,← Fin.val_inj]
      unfold tag
      split <;> (try split) <;> simp_all
      omega
    exact (congrArg Finset.card eqset).trans (card_singleton _)
  · have eqset : univ.filter (fun x : Fin (n+1) => tag v.val x.val = 2) = Ioi v := by
      ext x
      simp only [mem_filter,mem_univ,true_and,mem_Ioi]
      change _ ↔ v.val < x.val
      unfold tag
      split <;> (try split) <;> simp_all <;> omega
    exact (congrArg Finset.card eqset).trans (Fin.card_Ioi _)

private abbrev Paint (n : ℕ) (v : Fin (n+1)) (c : Fin 10 → Tag) :=
  (i : Fin 10) → {x : Fin (n+1) // tag v.val x.val = c i}

private abbrev Shape := {c : Fin 10 → Tag // allowed c}

private def forget {n : ℕ} (z : Σ v : Fin (n+1), Σ c : Shape, Paint n v c.val) :
    {x : Word n // good x = true} :=
  let x := fun i => (z.2.2 i).val
  have hc : colors z.1 x = z.2.1.val := funext (fun i => (z.2.2 i).property)
  ⟨x,(characterize x).mpr ⟨z.1,hc ▸ z.2.1.property⟩⟩

private theorem forget_bij (n : ℕ) : Function.Bijective (@forget n) := by
  constructor
  · rintro ⟨v,⟨c,hc⟩,x⟩ ⟨w,⟨d,hd⟩,y⟩ hh
    have eqxy : (fun i => (x i).val) = (fun i => (y i).val) := congrArg Subtype.val hh
    have colx : colors v (fun i => (x i).val) = c := funext fun i => (x i).property
    have coly : colors w (fun i => (y i).val) = d := funext fun i => (y i).property
    have h1 : allowed (colors v (fun i => (x i).val)) := by rw [colx]; exact hc
    have h2 : allowed (colors w (fun i => (x i).val)) := by rw [eqxy,coly]; exact hd
    have hv : v=w := uniqueValue h1 h2
    subst w
    have hcd : c=d := colx.symm.trans ((congrArg (colors v) eqxy).trans coly)
    subst d
    have : x=y := funext (fun i => Subtype.ext (congrFun eqxy i))
    subst y
    rfl
  · rintro ⟨x,hx⟩
    obtain ⟨v,hv⟩ := (characterize _).mp hx
    exact ⟨⟨v,⟨colors v x,hv⟩,fun i => ⟨x i,rfl⟩⟩,rfl⟩

private def total (l h : ℕ) : ℕ := ∑ c : Shape, ∏ i, weight l h (c.val i)

private theorem arrayCount (n : ℕ) : (a n : ℚ) =
    ∑ j ∈ range (n+1), (total j (n-j) : ℚ) := by
  classical
  have e := Fintype.card_congr (Equiv.ofBijective (fun z => @forget n z) (forget_bij n))
  rw [Fintype.card_subtype] at e
  unfold a
  push_cast
  rw [← e,Fintype.card_sigma,Nat.cast_sum,← Fin.sum_univ_eq_sum_range]
  apply Fintype.sum_congr
  intro v
  simp only [Fintype.card_sigma,Fintype.card_pi,weightCard,total]


private def patterns : (m : ℕ) → List (Fin m → Tag)
  | 0 => [Fin.elim0]
  | m+1 => (patterns m).map (Fin.cons 0) ++ (patterns m).map (Fin.cons 1) ++
      (patterns m).map (Fin.cons 2)

private theorem sumPatterns (m : ℕ) (f : (Fin m → Tag) → ℕ) :
    ∑ c, f c = ((patterns m).map f).sum := by
  induction m with
  | zero => simp [patterns,Unique.eq_default (Fin.elim0 : Fin 0 → Tag)]
  | succ m ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (m+1) => Tag)).sum_comp f,Fintype.sum_prod_type]
    simp only [Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero,
      patterns,List.map_append,List.sum_append,List.map_map]
    rw [← ih,← ih,← ih,add_assoc]
    rfl

private def cnt (c : Fin 10 → Tag) (x : Tag) : ℕ := ∑ i, if c i = x then 1 else 0
private def exps (c : Fin 10 → Tag) : ℕ × ℕ := (cnt c 0,cnt c 2)
private def eval (l h : ℕ) (p : ℕ × ℕ) := l^p.1*h^p.2

private theorem product (c : Fin 10 → Tag) (l h : ℕ) :
    ∏ i, weight l h (c i) = eval l h (exps c) := by
  have w (a : Tag) : weight l h a = l^(if a=0 then 1 else 0 : ℕ)*h^(if a=2 then 1 else 0 : ℕ) := by
    fin_cases a <;> simp [weight]
  simp only [w,prod_mul_distrib,prod_pow_eq_pow_sum,eval,exps,cnt]

private abbrev Hist := List ((ℕ × ℕ) × ℕ)
private def bump (key : ℕ × ℕ) : Hist → Hist
  | [] => [(key,1)]
  | (p,k)::xs => if key=p then (p,k+1)::xs else (p,k)::bump key xs

/-- Each exponent pair records how many positions take a lower or a higher value. -/
private def tally (xs : List (ℕ × ℕ)) : Hist := xs.foldr bump []
private def weighted (l h : ℕ) (xs : Hist) := (xs.map (fun p => p.2*eval l h p.1)).sum

private theorem bumpWeight (key : ℕ × ℕ) (l h : ℕ) (xs : Hist) :
    weighted l h (bump key xs) = eval l h key + weighted l h xs := by
  induction xs with
  | nil => simp [weighted,bump]
  | cons p xs ih =>
    rcases p with ⟨p,k⟩
    by_cases he : key=p
    · subst key
      simp [bump,weighted,Nat.add_mul]
      omega
    · simp [bump,he,weighted] at ih ⊢
      omega

private theorem tallyWeight (l h : ℕ) (xs : List (ℕ × ℕ)) :
    weighted l h (tally xs) = (xs.map (eval l h)).sum := by
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    change weighted l h (bump p (tally xs)) = _
    rw [bumpWeight,ih,List.map_cons,List.sum_cons]


private def fastAllowed (c : Fin 10 → Tag) : Prop :=
  ((((if c 0 = 0 then 1 else 0 : ℕ) + ((if c 1 = 0 then 1 else 0 : ℕ) + ((if c 2 = 0 then 1 else 0 : ℕ) + (if c 3 = 0 then 1 else 0 : ℕ)))) < 2 ∧ 2 < ((if c 0 ≠ 2 then 1 else 0 : ℕ) + ((if c 1 ≠ 2 then 1 else 0 : ℕ) + ((if c 2 ≠ 2 then 1 else 0 : ℕ) + (if c 3 ≠ 2 then 1 else 0 : ℕ))))) ∧ ((((if c 1 = 0 then 1 else 0 : ℕ) + ((if c 2 = 0 then 1 else 0 : ℕ) + ((if c 3 = 0 then 1 else 0 : ℕ) + (if c 4 = 0 then 1 else 0 : ℕ)))) < 2 ∧ 2 < ((if c 1 ≠ 2 then 1 else 0 : ℕ) + ((if c 2 ≠ 2 then 1 else 0 : ℕ) + ((if c 3 ≠ 2 then 1 else 0 : ℕ) + (if c 4 ≠ 2 then 1 else 0 : ℕ))))) ∧ ((((if c 2 = 0 then 1 else 0 : ℕ) + ((if c 3 = 0 then 1 else 0 : ℕ) + ((if c 4 = 0 then 1 else 0 : ℕ) + (if c 5 = 0 then 1 else 0 : ℕ)))) < 2 ∧ 2 < ((if c 2 ≠ 2 then 1 else 0 : ℕ) + ((if c 3 ≠ 2 then 1 else 0 : ℕ) + ((if c 4 ≠ 2 then 1 else 0 : ℕ) + (if c 5 ≠ 2 then 1 else 0 : ℕ))))) ∧ ((((if c 3 = 0 then 1 else 0 : ℕ) + ((if c 4 = 0 then 1 else 0 : ℕ) + ((if c 5 = 0 then 1 else 0 : ℕ) + (if c 6 = 0 then 1 else 0 : ℕ)))) < 2 ∧ 2 < ((if c 3 ≠ 2 then 1 else 0 : ℕ) + ((if c 4 ≠ 2 then 1 else 0 : ℕ) + ((if c 5 ≠ 2 then 1 else 0 : ℕ) + (if c 6 ≠ 2 then 1 else 0 : ℕ))))) ∧ ((((if c 4 = 0 then 1 else 0 : ℕ) + ((if c 5 = 0 then 1 else 0 : ℕ) + ((if c 6 = 0 then 1 else 0 : ℕ) + (if c 7 = 0 then 1 else 0 : ℕ)))) < 2 ∧ 2 < ((if c 4 ≠ 2 then 1 else 0 : ℕ) + ((if c 5 ≠ 2 then 1 else 0 : ℕ) + ((if c 6 ≠ 2 then 1 else 0 : ℕ) + (if c 7 ≠ 2 then 1 else 0 : ℕ))))) ∧ ((((if c 5 = 0 then 1 else 0 : ℕ) + ((if c 6 = 0 then 1 else 0 : ℕ) + ((if c 7 = 0 then 1 else 0 : ℕ) + (if c 8 = 0 then 1 else 0 : ℕ)))) < 2 ∧ 2 < ((if c 5 ≠ 2 then 1 else 0 : ℕ) + ((if c 6 ≠ 2 then 1 else 0 : ℕ) + ((if c 7 ≠ 2 then 1 else 0 : ℕ) + (if c 8 ≠ 2 then 1 else 0 : ℕ))))) ∧ (((if c 6 = 0 then 1 else 0 : ℕ) + ((if c 7 = 0 then 1 else 0 : ℕ) + ((if c 8 = 0 then 1 else 0 : ℕ) + (if c 9 = 0 then 1 else 0 : ℕ)))) < 2 ∧ 2 < ((if c 6 ≠ 2 then 1 else 0 : ℕ) + ((if c 7 ≠ 2 then 1 else 0 : ℕ) + ((if c 8 ≠ 2 then 1 else 0 : ℕ) + (if c 9 ≠ 2 then 1 else 0 : ℕ)))))))))))

private instance (c : Fin 10 → Tag) : Decidable (fastAllowed c) := by unfold fastAllowed; infer_instance

private theorem fastAllowed_iff (c : Fin 10 → Tag) : allowed c ↔ fastAllowed c := by
  simp only [allowed,bounds,fastAllowed,Fin.forall_fin_succ,Fin.sum_univ_succ,
    Finset.univ_eq_empty,Finset.sum_empty,add_zero,Fin.forall_fin_zero,and_true]
  rfl

private def fastExps (c : Fin 10 → Tag) : ℕ × ℕ :=
  (((if c 0 = 0 then 1 else 0 : ℕ) + ((if c 1 = 0 then 1 else 0 : ℕ) + ((if c 2 = 0 then 1 else 0 : ℕ) + ((if c 3 = 0 then 1 else 0 : ℕ) + ((if c 4 = 0 then 1 else 0 : ℕ) + ((if c 5 = 0 then 1 else 0 : ℕ) + ((if c 6 = 0 then 1 else 0 : ℕ) + ((if c 7 = 0 then 1 else 0 : ℕ) + ((if c 8 = 0 then 1 else 0 : ℕ) + (if c 9 = 0 then 1 else 0 : ℕ)))))))))), ((if c 0 = 2 then 1 else 0 : ℕ) + ((if c 1 = 2 then 1 else 0 : ℕ) + ((if c 2 = 2 then 1 else 0 : ℕ) + ((if c 3 = 2 then 1 else 0 : ℕ) + ((if c 4 = 2 then 1 else 0 : ℕ) + ((if c 5 = 2 then 1 else 0 : ℕ) + ((if c 6 = 2 then 1 else 0 : ℕ) + ((if c 7 = 2 then 1 else 0 : ℕ) + ((if c 8 = 2 then 1 else 0 : ℕ) + (if c 9 = 2 then 1 else 0 : ℕ)))))))))))

private theorem fastExps_eq (c : Fin 10 → Tag) : exps c = fastExps c := by
  simp only [exps,cnt,fastExps,Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero]
  rfl
private def sectionKeys {m : ℕ} (e : (Fin m → Tag) → (Fin 10 → Tag)) :=
  ((patterns m).filter (fun c => decide (fastAllowed (e c)))).map (fun c => fastExps (e c))

private def part {m : ℕ} (e : (Fin m → Tag) → (Fin 10 → Tag)) (l h : ℕ) :=
  ∑ c, if allowed (e c) then eval l h (exps (e c)) else 0

private theorem rootPart (l h : ℕ) : total l h = part id l h := by
  unfold part total
  rw [← Finset.sum_subtype (univ.filter allowed) (by simp) (fun c : Fin 10 → Tag => ∏ i, weight l h (c i))]
  simp only [Finset.sum_filter,product,id_eq]

private theorem splitPart {m : ℕ} (e : (Fin (m+1) → Tag) → (Fin 10 → Tag)) (l h : ℕ) :
    part e l h = part (fun c => e (Fin.cons 0 c)) l h +
      (part (fun c => e (Fin.cons 1 c)) l h + part (fun c => e (Fin.cons 2 c)) l h) := by
  unfold part
  rw [← (Fin.consEquiv (fun _ : Fin (m+1) => Tag)).sum_comp,Fintype.sum_prod_type]
  simp only [Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero]
  rfl

private theorem leafPart {m : ℕ} (e : (Fin m → Tag) → (Fin 10 → Tag)) (l h : ℕ) :
    part e l h = weighted l h (tally (sectionKeys e)) := by
  rw [part,sumPatterns,tallyWeight]
  unfold sectionKeys
  simp only [← fastAllowed_iff,← fastExps_eq]
  simp only [List.map_map,Function.comp_def]
  generalize patterns m = xs
  induction xs with
  | nil => rfl
  | cons x xs ih => by_cases h : allowed (e x) <;> simp [h,ih]

section

private theorem part00 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 10 → Tag from (Fin.cons 0 (Fin.cons 0 c)))) l h = 0 := by
  have forbid (c : Fin 8 → Tag) : ¬ allowed ((fun c : Fin 8 → Tag => (show Fin 10 → Tag from (Fin.cons 0 (Fin.cons 0 c)))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : (1 + (1 + ((if c 0 = 0 then 1 else 0 : ℕ) + (if c 1 = 0 then 1 else 0 : ℕ)))) < 2 := fast.1.1

    omega
  simp [part,forbid]

private theorem part010 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 0 (Fin.cons 1 (Fin.cons 0 c))))) l h = 0 := by
  have forbid (c : Fin 7 → Tag) : ¬ allowed ((fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 0 (Fin.cons 1 (Fin.cons 0 c))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : (1 + (0 + (1 + (if c 0 = 0 then 1 else 0 : ℕ)))) < 2 := fast.1.1

    omega
  simp [part,forbid]

private theorem table011 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 0 (Fin.cons 1 (Fin.cons 1 c)))))) =
    [((1,2),6), ((2,2),27), ((1,1),7), ((2,1),36), ((3,2),8), ((3,1),15), ((1,0),1), ((2,0),6), ((3,0),3)] := by decide +kernel

private theorem part011 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 0 (Fin.cons 1 (Fin.cons 1 c))))) l h =
    l + 7*l*h + 6*l*h^2 + 6*l^2 + 36*l^2*h + 27*l^2*h^2 + 3*l^3 + 15*l^3*h + 8*l^3*h^2 := by
  rw [leafPart,table011]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem table012 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 0 (Fin.cons 1 (Fin.cons 2 c)))))) =
    [((1,2),4), ((2,2),20), ((1,1),1), ((2,1),6), ((3,2),9), ((3,1),3)] := by decide +kernel

private theorem part012 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 0 (Fin.cons 1 (Fin.cons 2 c))))) l h =
    l*h + 4*l*h^2 + 6*l^2*h + 20*l^2*h^2 + 3*l^3*h + 9*l^3*h^2 := by
  rw [leafPart,table012]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem part01 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 10 → Tag from (Fin.cons 0 (Fin.cons 1 c)))) l h =
    l + 8*l*h + 10*l*h^2 + 6*l^2 + 42*l^2*h + 47*l^2*h^2 + 3*l^3 + 18*l^3*h + 17*l^3*h^2 := by
  rw [splitPart,part010,part011,part012]
  ring

private theorem part020 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 0 (Fin.cons 2 (Fin.cons 0 c))))) l h = 0 := by
  have forbid (c : Fin 7 → Tag) : ¬ allowed ((fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 0 (Fin.cons 2 (Fin.cons 0 c))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : (1 + (0 + (1 + (if c 0 = 0 then 1 else 0 : ℕ)))) < 2 := fast.1.1

    omega
  simp [part,forbid]

private theorem table021 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 0 (Fin.cons 2 (Fin.cons 1 c)))))) =
    [((1,3),1), ((1,2),5), ((2,2),25), ((2,3),4), ((1,1),1), ((2,1),6), ((3,2),11), ((3,1),3), ((3,3),1)] := by decide +kernel

private theorem part021 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 0 (Fin.cons 2 (Fin.cons 1 c))))) l h =
    l*h + 5*l*h^2 + l*h^3 + 6*l^2*h + 25*l^2*h^2 + 4*l^2*h^3 + 3*l^3*h + 11*l^3*h^2 + l^3*h^3 := by
  rw [leafPart,table021]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem part022 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 0 (Fin.cons 2 (Fin.cons 2 c))))) l h = 0 := by
  have forbid (c : Fin 7 → Tag) : ¬ allowed ((fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 0 (Fin.cons 2 (Fin.cons 2 c))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : 2 < (1 + (0 + (0 + (if c 0 ≠ 2 then 1 else 0 : ℕ)))) := fast.1.2
    have b0 : (if c 0 ≠ 2 then 1 else 0 : ℕ) ≤ 1 := by split <;> decide
    omega
  simp [part,forbid]

private theorem part02 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 10 → Tag from (Fin.cons 0 (Fin.cons 2 c)))) l h =
    l*h + 5*l*h^2 + l*h^3 + 6*l^2*h + 25*l^2*h^2 + 4*l^2*h^3 + 3*l^3*h + 11*l^3*h^2 + l^3*h^3 := by
  rw [splitPart,part020,part021,part022]
  ring

private theorem part0 (l h : ℕ) : part (fun c : Fin 9 → Tag => (show Fin 10 → Tag from (Fin.cons 0 c))) l h =
    l + 9*l*h + 15*l*h^2 + l*h^3 + 6*l^2 + 48*l^2*h + 72*l^2*h^2 + 4*l^2*h^3 + 3*l^3 + 21*l^3*h + 28*l^3*h^2 + l^3*h^3 := by
  rw [splitPart,part00,part01,part02]
  ring

private theorem part100 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 1 (Fin.cons 0 (Fin.cons 0 c))))) l h = 0 := by
  have forbid (c : Fin 7 → Tag) : ¬ allowed ((fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 1 (Fin.cons 0 (Fin.cons 0 c))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : (0 + (1 + (1 + (if c 0 = 0 then 1 else 0 : ℕ)))) < 2 := fast.1.1

    omega
  simp [part,forbid]

private theorem table101 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 1 (Fin.cons 0 (Fin.cons 1 c)))))) =
    [((1,2),6), ((2,2),23), ((1,1),7), ((2,1),30), ((3,2),3), ((3,1),5), ((1,0),1), ((2,0),5), ((3,0),1)] := by decide +kernel

private theorem part101 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 1 (Fin.cons 0 (Fin.cons 1 c))))) l h =
    l + 7*l*h + 6*l*h^2 + 5*l^2 + 30*l^2*h + 23*l^2*h^2 + l^3 + 5*l^3*h + 3*l^3*h^2 := by
  rw [leafPart,table101]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem table102 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 1 (Fin.cons 0 (Fin.cons 2 c)))))) =
    [((1,2),4), ((2,2),16), ((1,1),1), ((2,1),5), ((3,2),3), ((3,1),1)] := by decide +kernel

private theorem part102 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 1 (Fin.cons 0 (Fin.cons 2 c))))) l h =
    l*h + 4*l*h^2 + 5*l^2*h + 16*l^2*h^2 + l^3*h + 3*l^3*h^2 := by
  rw [leafPart,table102]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem part10 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 10 → Tag from (Fin.cons 1 (Fin.cons 0 c)))) l h =
    l + 8*l*h + 10*l*h^2 + 5*l^2 + 35*l^2*h + 39*l^2*h^2 + l^3 + 6*l^3*h + 6*l^3*h^2 := by
  rw [splitPart,part100,part101,part102]
  ring

private theorem table110 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 1 (Fin.cons 1 (Fin.cons 0 c)))))) =
    [((1,2),6), ((2,2),18), ((1,1),7), ((2,1),24), ((1,0),1), ((2,0),4)] := by decide +kernel

private theorem part110 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 1 (Fin.cons 1 (Fin.cons 0 c))))) l h =
    l + 7*l*h + 6*l*h^2 + 4*l^2 + 24*l^2*h + 18*l^2*h^2 := by
  rw [leafPart,table110]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem table111 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 1 (Fin.cons 1 (Fin.cons 1 c)))))) =
    [((0,2),6), ((1,2),30), ((0,1),7), ((1,1),42), ((2,2),14), ((2,1),30), ((0,0),1), ((1,0),7), ((2,0),6)] := by decide +kernel

private theorem part111 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 1 (Fin.cons 1 (Fin.cons 1 c))))) l h =
    1 + 7*h + 6*h^2 + 7*l + 42*l*h + 30*l*h^2 + 6*l^2 + 30*l^2*h + 14*l^2*h^2 := by
  rw [leafPart,table111]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem table112 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 1 (Fin.cons 1 (Fin.cons 2 c)))))) =
    [((0,2),4), ((1,2),24), ((0,1),1), ((1,1),7), ((2,2),18), ((2,1),6)] := by decide +kernel

private theorem part112 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 1 (Fin.cons 1 (Fin.cons 2 c))))) l h =
    h + 4*h^2 + 7*l*h + 24*l*h^2 + 6*l^2*h + 18*l^2*h^2 := by
  rw [leafPart,table112]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem part11 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 10 → Tag from (Fin.cons 1 (Fin.cons 1 c)))) l h =
    1 + 8*h + 10*h^2 + 8*l + 56*l*h + 60*l*h^2 + 10*l^2 + 60*l^2*h + 50*l^2*h^2 := by
  rw [splitPart,part110,part111,part112]
  ring

private theorem table120 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 1 (Fin.cons 2 (Fin.cons 0 c)))))) =
    [((1,3),1), ((1,2),5), ((2,2),16), ((2,3),3), ((1,1),1), ((2,1),4)] := by decide +kernel

private theorem part120 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 1 (Fin.cons 2 (Fin.cons 0 c))))) l h =
    l*h + 5*l*h^2 + l*h^3 + 4*l^2*h + 16*l^2*h^2 + 3*l^2*h^3 := by
  rw [leafPart,table120]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem table121 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 1 (Fin.cons 2 (Fin.cons 1 c)))))) =
    [((0,3),1), ((0,2),5), ((1,2),30), ((1,3),5), ((0,1),1), ((1,1),7), ((2,2),23), ((2,1),6), ((2,3),3)] := by decide +kernel

private theorem part121 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 1 (Fin.cons 2 (Fin.cons 1 c))))) l h =
    h + 5*h^2 + h^3 + 7*l*h + 30*l*h^2 + 5*l*h^3 + 6*l^2*h + 23*l^2*h^2 + 3*l^2*h^3 := by
  rw [leafPart,table121]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem part122 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 1 (Fin.cons 2 (Fin.cons 2 c))))) l h = 0 := by
  have forbid (c : Fin 7 → Tag) : ¬ allowed ((fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 1 (Fin.cons 2 (Fin.cons 2 c))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : 2 < (1 + (0 + (0 + (if c 0 ≠ 2 then 1 else 0 : ℕ)))) := fast.1.2
    have b0 : (if c 0 ≠ 2 then 1 else 0 : ℕ) ≤ 1 := by split <;> decide
    omega
  simp [part,forbid]

private theorem part12 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 10 → Tag from (Fin.cons 1 (Fin.cons 2 c)))) l h =
    h + 5*h^2 + h^3 + 8*l*h + 35*l*h^2 + 6*l*h^3 + 10*l^2*h + 39*l^2*h^2 + 6*l^2*h^3 := by
  rw [splitPart,part120,part121,part122]
  ring

private theorem part1 (l h : ℕ) : part (fun c : Fin 9 → Tag => (show Fin 10 → Tag from (Fin.cons 1 c))) l h =
    1 + 9*h + 15*h^2 + h^3 + 9*l + 72*l*h + 105*l*h^2 + 6*l*h^3 + 15*l^2 + 105*l^2*h + 128*l^2*h^2 + 6*l^2*h^3 + l^3 + 6*l^3*h + 6*l^3*h^2 := by
  rw [splitPart,part10,part11,part12]
  ring

private theorem part200 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 2 (Fin.cons 0 (Fin.cons 0 c))))) l h = 0 := by
  have forbid (c : Fin 7 → Tag) : ¬ allowed ((fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 2 (Fin.cons 0 (Fin.cons 0 c))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : (0 + (1 + (1 + (if c 0 = 0 then 1 else 0 : ℕ)))) < 2 := fast.1.1

    omega
  simp [part,forbid]

private theorem table201 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 2 (Fin.cons 0 (Fin.cons 1 c)))))) =
    [((1,3),3), ((2,3),11), ((1,2),6), ((2,2),25), ((3,3),1), ((3,2),4), ((1,1),1), ((2,1),5), ((3,1),1)] := by decide +kernel

private theorem part201 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 2 (Fin.cons 0 (Fin.cons 1 c))))) l h =
    l*h + 6*l*h^2 + 3*l*h^3 + 5*l^2*h + 25*l^2*h^2 + 11*l^2*h^3 + l^3*h + 4*l^3*h^2 + l^3*h^3 := by
  rw [leafPart,table201]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem part202 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 2 (Fin.cons 0 (Fin.cons 2 c))))) l h = 0 := by
  have forbid (c : Fin 7 → Tag) : ¬ allowed ((fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 2 (Fin.cons 0 (Fin.cons 2 c))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : 2 < (0 + (1 + (0 + (if c 0 ≠ 2 then 1 else 0 : ℕ)))) := fast.1.2
    have b0 : (if c 0 ≠ 2 then 1 else 0 : ℕ) ≤ 1 := by split <;> decide
    omega
  simp [part,forbid]

private theorem part20 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 10 → Tag from (Fin.cons 2 (Fin.cons 0 c)))) l h =
    l*h + 6*l*h^2 + 3*l*h^3 + 5*l^2*h + 25*l^2*h^2 + 11*l^2*h^3 + l^3*h + 4*l^3*h^2 + l^3*h^3 := by
  rw [splitPart,part200,part201,part202]
  ring

private theorem table210 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 2 (Fin.cons 1 (Fin.cons 0 c)))))) =
    [((1,3),3), ((2,3),9), ((1,2),6), ((2,2),20), ((1,1),1), ((2,1),4)] := by decide +kernel

private theorem part210 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 2 (Fin.cons 1 (Fin.cons 0 c))))) l h =
    l*h + 6*l*h^2 + 3*l*h^3 + 4*l^2*h + 20*l^2*h^2 + 9*l^2*h^3 := by
  rw [leafPart,table210]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem table211 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 2 (Fin.cons 1 (Fin.cons 1 c)))))) =
    [((0,3),3), ((1,3),15), ((0,2),6), ((1,2),36), ((2,3),8), ((2,2),27), ((0,1),1), ((1,1),7), ((2,1),6)] := by decide +kernel

private theorem part211 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 2 (Fin.cons 1 (Fin.cons 1 c))))) l h =
    h + 6*h^2 + 3*h^3 + 7*l*h + 36*l*h^2 + 15*l*h^3 + 6*l^2*h + 27*l^2*h^2 + 8*l^2*h^3 := by
  rw [leafPart,table211]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem part212 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 2 (Fin.cons 1 (Fin.cons 2 c))))) l h = 0 := by
  have forbid (c : Fin 7 → Tag) : ¬ allowed ((fun c : Fin 7 → Tag => (show Fin 10 → Tag from (Fin.cons 2 (Fin.cons 1 (Fin.cons 2 c))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : 2 < (0 + (1 + (0 + (if c 0 ≠ 2 then 1 else 0 : ℕ)))) := fast.1.2
    have b0 : (if c 0 ≠ 2 then 1 else 0 : ℕ) ≤ 1 := by split <;> decide
    omega
  simp [part,forbid]

private theorem part21 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 10 → Tag from (Fin.cons 2 (Fin.cons 1 c)))) l h =
    h + 6*h^2 + 3*h^3 + 8*l*h + 42*l*h^2 + 18*l*h^3 + 10*l^2*h + 47*l^2*h^2 + 17*l^2*h^3 := by
  rw [splitPart,part210,part211,part212]
  ring

private theorem part22 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 10 → Tag from (Fin.cons 2 (Fin.cons 2 c)))) l h = 0 := by
  have forbid (c : Fin 8 → Tag) : ¬ allowed ((fun c : Fin 8 → Tag => (show Fin 10 → Tag from (Fin.cons 2 (Fin.cons 2 c)))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : 2 < (0 + (0 + ((if c 0 ≠ 2 then 1 else 0 : ℕ) + (if c 1 ≠ 2 then 1 else 0 : ℕ)))) := fast.1.2
    have b0 : (if c 0 ≠ 2 then 1 else 0 : ℕ) ≤ 1 := by split <;> decide
    have b1 : (if c 1 ≠ 2 then 1 else 0 : ℕ) ≤ 1 := by split <;> decide
    omega
  simp [part,forbid]

private theorem part2 (l h : ℕ) : part (fun c : Fin 9 → Tag => (show Fin 10 → Tag from (Fin.cons 2 c))) l h =
    h + 6*h^2 + 3*h^3 + 9*l*h + 48*l*h^2 + 21*l*h^3 + 15*l^2*h + 72*l^2*h^2 + 28*l^2*h^3 + l^3*h + 4*l^3*h^2 + l^3*h^3 := by
  rw [splitPart,part20,part21,part22]
  ring

private theorem partAll (l h : ℕ) : part (fun c : Fin 10 → Tag => (show Fin 10 → Tag from c)) l h =
    1 + 10*h + 21*h^2 + 4*h^3 + 10*l + 90*l*h + 168*l*h^2 + 28*l*h^3 + 21*l^2 + 168*l^2*h + 272*l^2*h^2 + 38*l^2*h^3 + 4*l^3 + 28*l^3*h + 38*l^3*h^2 + 2*l^3*h^3 := by
  rw [splitPart,part0,part1,part2]
  ring

end

private def expression (l h : ℕ) : ℕ :=
  2*h^3*l^3 + 38*h^3*l^2 + 28*h^3*l + 4*h^3 + 38*h^2*l^3 + 272*h^2*l^2 + 168*h^2*l + 21*h^2 + 28*h*l^3 + 168*h*l^2 + 90*h*l + 10*h + 4*l^3 + 21*l^2 + 10*l + 1

private theorem totalValue (l h : ℕ) : total l h = expression l h := by
  rw [rootPart]
  exact (partAll l h).trans (by unfold expression; ring)

private def H (n t : ℚ) : ℚ :=
  (t*(n*(n*(-770*n - 5348) - 8666) + t*(n*(n*(-945*n - 7350) - 1365) + t*(n*(n*(2450*n + 20720) + 37100) + t*(n*(n*(105*n - 3360) - 26145) + t*(n*(966 - 252*n) + t*(210*n - 60*t + 210) + 8862) - 22680) + 11830) + 5040) - 2992))/210

private def P (n : ℚ) : ℚ :=
  (n*(n*(n*(n*(n*(n*(3*n + 266) + 2492) + 6300) + 5957) + 784) - 892) + 210)/210

private theorem partialSum (n b : ℕ) (hb : b ≤ n+1) :
    ∑ j ∈ range b, (total j (n-j) : ℚ) = H n b := by
  induction b with
  | zero => simp only [range_zero,sum_empty,Nat.cast_zero,H,zero_mul,zero_div]
  | succ b ih =>
    rw [sum_range_succ,ih (by omega),totalValue]
    unfold expression H
    push_cast [Nat.cast_sub (show b ≤ n by omega)]
    ring

private theorem value (n : ℕ) : (a n : ℚ) = P n := by
  rw [arrayCount,partialSum n (n+1) le_rfl]
  unfold H P
  push_cast
  ring

private theorem recurrence (n : ℕ) (hn : 9 ≤ n) :
    (a n : ℚ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  obtain ⟨m,rfl⟩ : ∃ m, n=m+9 := ⟨n-9,by omega⟩
  simp only [show m+9-1 = m+8 by omega,show m+9-2 = m+7 by omega,show m+9-3 = m+6 by omega,show m+9-4 = m+5 by omega,show m+9-5 = m+4 by omega,show m+9-6 = m+3 by omega,show m+9-7 = m+2 by omega,show m+9-8 = m+1 by omega,value,P]
  push_cast
  ring

private theorem generating :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 8 : PowerSeries ℚ) = X * (72 + 601 * X - 344 * X ^ 2 - 411 * X ^ 3 + 152 * X ^ 4 - 5 * X ^ 5 + 8 * X ^ 6 - X ^ 7) := by
  let S := mk (fun n => if n < 1 then 0 else (a n : ℚ))
  change S * _ = _
  have lhs : S*(1-X)^8 = S - (8:ℕ) • (S*X^1) + (28:ℕ) • (S*X^2) - (56:ℕ) • (S*X^3) + (70:ℕ) • (S*X^4) - (56:ℕ) • (S*X^5) + (28:ℕ) • (S*X^6) - (8:ℕ) • (S*X^7) + (S*X^8) := by simp only [nsmul_eq_mul]; ring
  have rhs : (X * (72 + 601 * X - 344 * X ^ 2 - 411 * X ^ 3 + 152 * X ^ 4 - 5 * X ^ 5 + 8 * X ^ 6 - X ^ 7) : PowerSeries ℚ) = (72:ℕ) • X^1 + (601:ℕ) • X^2 - (344:ℕ) • X^3 - (411:ℕ) • X^4 + (152:ℕ) • X^5 - (5:ℕ) • X^6 + (8:ℕ) • X^7 - X^8 := by simp only [nsmul_eq_mul]; ring
  rw [lhs,rhs]
  ext n
  simp only [map_add,map_sub,map_nsmul,coeff_mul_X_pow',coeff_X_pow,S,coeff_mk]
  by_cases h : 9 ≤ n
  · have recn := recurrence n h
    simp only [nsmul_eq_mul,if_pos (show 1 ≤ n by omega),
      if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega),
      if_pos (show 4 ≤ n by omega),
      if_pos (show 5 ≤ n by omega),
      if_pos (show 6 ≤ n by omega),
      if_pos (show 7 ≤ n by omega),
      if_pos (show 8 ≤ n by omega),
      if_neg (show ¬ n < 1 by omega),
      if_neg (show ¬ n-1 < 1 by omega),
      if_neg (show ¬ n-2 < 1 by omega),
      if_neg (show ¬ n-3 < 1 by omega),
      if_neg (show ¬ n-4 < 1 by omega),
      if_neg (show ¬ n-5 < 1 by omega),
      if_neg (show ¬ n-6 < 1 by omega),
      if_neg (show ¬ n-7 < 1 by omega),
      if_neg (show ¬ n-8 < 1 by omega),
      if_neg (show n ≠ 1 by omega),
      if_neg (show n ≠ 2 by omega),
      if_neg (show n ≠ 3 by omega),
      if_neg (show n ≠ 4 by omega),
      if_neg (show n ≠ 5 by omega),
      if_neg (show n ≠ 6 by omega),
      if_neg (show n ≠ 7 by omega),
      if_neg (show n ≠ 8 by omega)]
    norm_num
    linarith
  · interval_cases n <;> norm_num [value,P]

theorem result : type_of% @OMA.S_oeis_a249713.main := ⟨generating,recurrence⟩

end OMA.Ties249713

theorem OMA.solution : type_of% @OMA.S_oeis_a249713.main := OMA.Ties249713.result
