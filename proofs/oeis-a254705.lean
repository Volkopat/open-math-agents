import OMAStatements.S_oeis_a254705
import Mathlib

namespace OMA.Ties254705
open OMA.S_oeis_a254705 Finset PowerSeries

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


private abbrev Word (n : ℕ) := Fin 11 → Fin (n+1)
private abbrev Tag := Fin 3
private def tag (v x : ℕ) : Tag := if x < v then 0 else if x = v then 1 else 2
private def colors {n : ℕ} (v : Fin (n+1)) (x : Word n) : Fin 11 → Tag :=
  fun i => tag v.val (x i).val

private def bounds (c : Fin 11 → Tag) (i : Fin 7) : Prop :=
  let y (t : Fin 5) := c ⟨i.val+t.val,by omega⟩
  (∑ t, if y t = 0 then 1 else 0 : ℕ) < 2 ∧ 2 < (∑ t, if y t ≠ 2 then 1 else 0 : ℕ)

private def allowed (c : Fin 11 → Tag) := ∀ i, bounds c i
private instance (c : Fin 11 → Tag) : Decidable (allowed c) := by unfold allowed bounds; infer_instance

private theorem colored {n : ℕ} (v : Fin (n+1)) (x : Word n) (i : Fin 7) :
    bounds (colors v x) i ↔ cross (win (W:=5) (get x) i.val) 2 v.val := by
  have hzero (a : ℕ) : tag v.val a = 0 ↔ a < v.val := by
    unfold tag; split <;> (try split) <;> simp_all
  have htwo (a : ℕ) : tag v.val a ≠ 2 ↔ a ≤ v.val := by
    unfold tag; split <;> simp_all <;> omega
  have bound (t : Fin 5) : i.val+t.val < 11 := by omega
  simp only [bounds,colors,cross,lower_sum,upto_sum,win,hzero,htwo,OMA.S_oeis_a254705.get,
    dif_pos (bound _)]

private theorem witnesses {n : ℕ} (x : Word n) :
    good x = true ↔ ∀ i : Fin 7, ∃ v : Fin (n+1), cross (win (W:=5) (get x) i.val) 2 v.val := by
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
    have same : ∀ i : Fin 7, ∀ w : Fin (n+1), cross (win (W:=5) (get x) i.val) 2 w.val → v = w := by
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

private abbrev Paint (n : ℕ) (v : Fin (n+1)) (c : Fin 11 → Tag) :=
  (i : Fin 11) → {x : Fin (n+1) // tag v.val x.val = c i}

private abbrev Shape := {c : Fin 11 → Tag // allowed c}

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

private def cnt (c : Fin 11 → Tag) (x : Tag) : ℕ := ∑ i, if c i = x then 1 else 0
private def exps (c : Fin 11 → Tag) : ℕ × ℕ := (cnt c 0,cnt c 2)
private def eval (l h : ℕ) (p : ℕ × ℕ) := l^p.1*h^p.2

private theorem product (c : Fin 11 → Tag) (l h : ℕ) :
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


private def fastAllowed (c : Fin 11 → Tag) : Prop :=
  ((((if c 0 = 0 then 1 else 0 : ℕ) + ((if c 1 = 0 then 1 else 0 : ℕ) + ((if c 2 = 0 then 1 else 0 : ℕ) + ((if c 3 = 0 then 1 else 0 : ℕ) + (if c 4 = 0 then 1 else 0 : ℕ))))) < 2 ∧ 2 < ((if c 0 ≠ 2 then 1 else 0 : ℕ) + ((if c 1 ≠ 2 then 1 else 0 : ℕ) + ((if c 2 ≠ 2 then 1 else 0 : ℕ) + ((if c 3 ≠ 2 then 1 else 0 : ℕ) + (if c 4 ≠ 2 then 1 else 0 : ℕ)))))) ∧ ((((if c 1 = 0 then 1 else 0 : ℕ) + ((if c 2 = 0 then 1 else 0 : ℕ) + ((if c 3 = 0 then 1 else 0 : ℕ) + ((if c 4 = 0 then 1 else 0 : ℕ) + (if c 5 = 0 then 1 else 0 : ℕ))))) < 2 ∧ 2 < ((if c 1 ≠ 2 then 1 else 0 : ℕ) + ((if c 2 ≠ 2 then 1 else 0 : ℕ) + ((if c 3 ≠ 2 then 1 else 0 : ℕ) + ((if c 4 ≠ 2 then 1 else 0 : ℕ) + (if c 5 ≠ 2 then 1 else 0 : ℕ)))))) ∧ ((((if c 2 = 0 then 1 else 0 : ℕ) + ((if c 3 = 0 then 1 else 0 : ℕ) + ((if c 4 = 0 then 1 else 0 : ℕ) + ((if c 5 = 0 then 1 else 0 : ℕ) + (if c 6 = 0 then 1 else 0 : ℕ))))) < 2 ∧ 2 < ((if c 2 ≠ 2 then 1 else 0 : ℕ) + ((if c 3 ≠ 2 then 1 else 0 : ℕ) + ((if c 4 ≠ 2 then 1 else 0 : ℕ) + ((if c 5 ≠ 2 then 1 else 0 : ℕ) + (if c 6 ≠ 2 then 1 else 0 : ℕ)))))) ∧ ((((if c 3 = 0 then 1 else 0 : ℕ) + ((if c 4 = 0 then 1 else 0 : ℕ) + ((if c 5 = 0 then 1 else 0 : ℕ) + ((if c 6 = 0 then 1 else 0 : ℕ) + (if c 7 = 0 then 1 else 0 : ℕ))))) < 2 ∧ 2 < ((if c 3 ≠ 2 then 1 else 0 : ℕ) + ((if c 4 ≠ 2 then 1 else 0 : ℕ) + ((if c 5 ≠ 2 then 1 else 0 : ℕ) + ((if c 6 ≠ 2 then 1 else 0 : ℕ) + (if c 7 ≠ 2 then 1 else 0 : ℕ)))))) ∧ ((((if c 4 = 0 then 1 else 0 : ℕ) + ((if c 5 = 0 then 1 else 0 : ℕ) + ((if c 6 = 0 then 1 else 0 : ℕ) + ((if c 7 = 0 then 1 else 0 : ℕ) + (if c 8 = 0 then 1 else 0 : ℕ))))) < 2 ∧ 2 < ((if c 4 ≠ 2 then 1 else 0 : ℕ) + ((if c 5 ≠ 2 then 1 else 0 : ℕ) + ((if c 6 ≠ 2 then 1 else 0 : ℕ) + ((if c 7 ≠ 2 then 1 else 0 : ℕ) + (if c 8 ≠ 2 then 1 else 0 : ℕ)))))) ∧ ((((if c 5 = 0 then 1 else 0 : ℕ) + ((if c 6 = 0 then 1 else 0 : ℕ) + ((if c 7 = 0 then 1 else 0 : ℕ) + ((if c 8 = 0 then 1 else 0 : ℕ) + (if c 9 = 0 then 1 else 0 : ℕ))))) < 2 ∧ 2 < ((if c 5 ≠ 2 then 1 else 0 : ℕ) + ((if c 6 ≠ 2 then 1 else 0 : ℕ) + ((if c 7 ≠ 2 then 1 else 0 : ℕ) + ((if c 8 ≠ 2 then 1 else 0 : ℕ) + (if c 9 ≠ 2 then 1 else 0 : ℕ)))))) ∧ (((if c 6 = 0 then 1 else 0 : ℕ) + ((if c 7 = 0 then 1 else 0 : ℕ) + ((if c 8 = 0 then 1 else 0 : ℕ) + ((if c 9 = 0 then 1 else 0 : ℕ) + (if c 10 = 0 then 1 else 0 : ℕ))))) < 2 ∧ 2 < ((if c 6 ≠ 2 then 1 else 0 : ℕ) + ((if c 7 ≠ 2 then 1 else 0 : ℕ) + ((if c 8 ≠ 2 then 1 else 0 : ℕ) + ((if c 9 ≠ 2 then 1 else 0 : ℕ) + (if c 10 ≠ 2 then 1 else 0 : ℕ))))))))))))

private instance (c : Fin 11 → Tag) : Decidable (fastAllowed c) := by unfold fastAllowed; infer_instance

private theorem fastAllowed_iff (c : Fin 11 → Tag) : allowed c ↔ fastAllowed c := by
  simp only [allowed,bounds,fastAllowed,Fin.forall_fin_succ,Fin.sum_univ_succ,
    Finset.univ_eq_empty,Finset.sum_empty,add_zero,Fin.forall_fin_zero,and_true]
  rfl

private def fastExps (c : Fin 11 → Tag) : ℕ × ℕ :=
  (((if c 0 = 0 then 1 else 0 : ℕ) + ((if c 1 = 0 then 1 else 0 : ℕ) + ((if c 2 = 0 then 1 else 0 : ℕ) + ((if c 3 = 0 then 1 else 0 : ℕ) + ((if c 4 = 0 then 1 else 0 : ℕ) + ((if c 5 = 0 then 1 else 0 : ℕ) + ((if c 6 = 0 then 1 else 0 : ℕ) + ((if c 7 = 0 then 1 else 0 : ℕ) + ((if c 8 = 0 then 1 else 0 : ℕ) + ((if c 9 = 0 then 1 else 0 : ℕ) + (if c 10 = 0 then 1 else 0 : ℕ))))))))))), ((if c 0 = 2 then 1 else 0 : ℕ) + ((if c 1 = 2 then 1 else 0 : ℕ) + ((if c 2 = 2 then 1 else 0 : ℕ) + ((if c 3 = 2 then 1 else 0 : ℕ) + ((if c 4 = 2 then 1 else 0 : ℕ) + ((if c 5 = 2 then 1 else 0 : ℕ) + ((if c 6 = 2 then 1 else 0 : ℕ) + ((if c 7 = 2 then 1 else 0 : ℕ) + ((if c 8 = 2 then 1 else 0 : ℕ) + ((if c 9 = 2 then 1 else 0 : ℕ) + (if c 10 = 2 then 1 else 0 : ℕ))))))))))))

private theorem fastExps_eq (c : Fin 11 → Tag) : exps c = fastExps c := by
  simp only [exps,cnt,fastExps,Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero]
  rfl
private def sectionKeys {m : ℕ} (e : (Fin m → Tag) → (Fin 11 → Tag)) :=
  ((patterns m).filter (fun c => decide (fastAllowed (e c)))).map (fun c => fastExps (e c))

private def part {m : ℕ} (e : (Fin m → Tag) → (Fin 11 → Tag)) (l h : ℕ) :=
  ∑ c, if allowed (e c) then eval l h (exps (e c)) else 0

private theorem rootPart (l h : ℕ) : total l h = part id l h := by
  unfold part total
  rw [← Finset.sum_subtype (univ.filter allowed) (by simp) (fun c : Fin 11 → Tag => ∏ i, weight l h (c i))]
  simp only [Finset.sum_filter,product,id_eq]

private theorem splitPart {m : ℕ} (e : (Fin (m+1) → Tag) → (Fin 11 → Tag)) (l h : ℕ) :
    part e l h = part (fun c => e (Fin.cons 0 c)) l h +
      (part (fun c => e (Fin.cons 1 c)) l h + part (fun c => e (Fin.cons 2 c)) l h) := by
  unfold part
  rw [← (Fin.consEquiv (fun _ : Fin (m+1) => Tag)).sum_comp,Fintype.sum_prod_type]
  simp only [Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero]
  rfl

private theorem leafPart {m : ℕ} (e : (Fin m → Tag) → (Fin 11 → Tag)) (l h : ℕ) :
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

private theorem part00 (l h : ℕ) : part (fun c : Fin 9 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 0 c)))) l h = 0 := by
  have forbid (c : Fin 9 → Tag) : ¬ allowed ((fun c : Fin 9 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 0 c)))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : (1 + (1 + ((if c 0 = 0 then 1 else 0 : ℕ) + ((if c 1 = 0 then 1 else 0 : ℕ) + (if c 2 = 0 then 1 else 0 : ℕ))))) < 2 := fast.1.1

    omega
  simp [part,forbid]

private theorem part010 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 1 (Fin.cons 0 c))))) l h = 0 := by
  have forbid (c : Fin 8 → Tag) : ¬ allowed ((fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 1 (Fin.cons 0 c))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : (1 + (0 + (1 + ((if c 0 = 0 then 1 else 0 : ℕ) + (if c 1 = 0 then 1 else 0 : ℕ))))) < 2 := fast.1.1

    omega
  simp [part,forbid]

private theorem part0110 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 1 (Fin.cons 1 (Fin.cons 0 c)))))) l h = 0 := by
  have forbid (c : Fin 7 → Tag) : ¬ allowed ((fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 1 (Fin.cons 1 (Fin.cons 0 c)))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : (1 + (0 + (0 + (1 + (if c 0 = 0 then 1 else 0 : ℕ))))) < 2 := fast.1.1

    omega
  simp [part,forbid]

private theorem table0111 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 1 (Fin.cons 1 (Fin.cons 1 c))))))) =
    [((1,4),1), ((1,3),13), ((2,3),48), ((1,2),21), ((2,2),90), ((2,4),3), ((1,1),7), ((2,1),36), ((3,3),3), ((3,2),10), ((3,1),5), ((1,0),1), ((2,0),6), ((3,0),1)] := by decide +kernel

private theorem part0111 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 1 (Fin.cons 1 (Fin.cons 1 c)))))) l h =
    l + 7*l*h + 21*l*h^2 + 13*l*h^3 + l*h^4 + 6*l^2 + 36*l^2*h + 90*l^2*h^2 + 48*l^2*h^3 + 3*l^2*h^4 + l^3 + 5*l^3*h + 10*l^3*h^2 + 3*l^3*h^3 := by
  rw [leafPart,table0111]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem table0112 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 1 (Fin.cons 1 (Fin.cons 2 c))))))) =
    [((1,4),5), ((2,4),18), ((1,3),15), ((2,3),63), ((1,2),7), ((2,2),36), ((3,4),1), ((3,3),7), ((3,2),5), ((1,1),1), ((2,1),6), ((3,1),1)] := by decide +kernel

private theorem part0112 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 1 (Fin.cons 1 (Fin.cons 2 c)))))) l h =
    l*h + 7*l*h^2 + 15*l*h^3 + 5*l*h^4 + 6*l^2*h + 36*l^2*h^2 + 63*l^2*h^3 + 18*l^2*h^4 + l^3*h + 5*l^3*h^2 + 7*l^3*h^3 + l^3*h^4 := by
  rw [leafPart,table0112]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem part011 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 1 (Fin.cons 1 c))))) l h =
    l + 8*l*h + 28*l*h^2 + 28*l*h^3 + 6*l*h^4 + 6*l^2 + 42*l^2*h + 126*l^2*h^2 + 111*l^2*h^3 + 21*l^2*h^4 + l^3 + 6*l^3*h + 15*l^3*h^2 + 10*l^3*h^3 + l^3*h^4 := by
  rw [splitPart,part0110,part0111,part0112]
  ring

private theorem part0120 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 1 (Fin.cons 2 (Fin.cons 0 c)))))) l h = 0 := by
  have forbid (c : Fin 7 → Tag) : ¬ allowed ((fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 1 (Fin.cons 2 (Fin.cons 0 c)))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : (1 + (0 + (0 + (1 + (if c 0 = 0 then 1 else 0 : ℕ))))) < 2 := fast.1.1

    omega
  simp [part,forbid]

private theorem table0121 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 1 (Fin.cons 2 (Fin.cons 1 c))))))) =
    [((1,4),8), ((2,4),29), ((1,3),18), ((2,3),76), ((1,2),7), ((2,2),36), ((3,4),2), ((3,3),9), ((3,2),5), ((1,1),1), ((2,1),6), ((3,1),1)] := by decide +kernel

private theorem part0121 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 1 (Fin.cons 2 (Fin.cons 1 c)))))) l h =
    l*h + 7*l*h^2 + 18*l*h^3 + 8*l*h^4 + 6*l^2*h + 36*l^2*h^2 + 76*l^2*h^3 + 29*l^2*h^4 + l^3*h + 5*l^3*h^2 + 9*l^3*h^3 + 2*l^3*h^4 := by
  rw [leafPart,table0121]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem table0122 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 1 (Fin.cons 2 (Fin.cons 2 c))))))) =
    [((1,4),6), ((2,4),24), ((1,3),4), ((2,3),20), ((1,2),1), ((2,2),6), ((3,4),3), ((3,3),3), ((3,2),1)] := by decide +kernel

private theorem part0122 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 1 (Fin.cons 2 (Fin.cons 2 c)))))) l h =
    l*h^2 + 4*l*h^3 + 6*l*h^4 + 6*l^2*h^2 + 20*l^2*h^3 + 24*l^2*h^4 + l^3*h^2 + 3*l^3*h^3 + 3*l^3*h^4 := by
  rw [leafPart,table0122]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem part012 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 1 (Fin.cons 2 c))))) l h =
    l*h + 8*l*h^2 + 22*l*h^3 + 14*l*h^4 + 6*l^2*h + 42*l^2*h^2 + 96*l^2*h^3 + 53*l^2*h^4 + l^3*h + 6*l^3*h^2 + 12*l^3*h^3 + 5*l^3*h^4 := by
  rw [splitPart,part0120,part0121,part0122]
  ring

private theorem part01 (l h : ℕ) : part (fun c : Fin 9 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 1 c)))) l h =
    l + 9*l*h + 36*l*h^2 + 50*l*h^3 + 20*l*h^4 + 6*l^2 + 48*l^2*h + 168*l^2*h^2 + 207*l^2*h^3 + 74*l^2*h^4 + l^3 + 7*l^3*h + 21*l^3*h^2 + 22*l^3*h^3 + 6*l^3*h^4 := by
  rw [splitPart,part010,part011,part012]
  ring

private theorem part020 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 2 (Fin.cons 0 c))))) l h = 0 := by
  have forbid (c : Fin 8 → Tag) : ¬ allowed ((fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 2 (Fin.cons 0 c))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : (1 + (0 + (1 + ((if c 0 = 0 then 1 else 0 : ℕ) + (if c 1 = 0 then 1 else 0 : ℕ))))) < 2 := fast.1.1

    omega
  simp [part,forbid]

private theorem part0210 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 2 (Fin.cons 1 (Fin.cons 0 c)))))) l h = 0 := by
  have forbid (c : Fin 7 → Tag) : ¬ allowed ((fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 2 (Fin.cons 1 (Fin.cons 0 c)))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : (1 + (0 + (0 + (1 + (if c 0 = 0 then 1 else 0 : ℕ))))) < 2 := fast.1.1

    omega
  simp [part,forbid]

private theorem table0211 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 2 (Fin.cons 1 (Fin.cons 1 c))))))) =
    [((1,4),11), ((2,4),40), ((1,3),20), ((2,3),85), ((1,2),7), ((2,2),36), ((3,4),3), ((3,3),10), ((3,2),5), ((1,1),1), ((2,1),6), ((3,1),1)] := by decide +kernel

private theorem part0211 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 2 (Fin.cons 1 (Fin.cons 1 c)))))) l h =
    l*h + 7*l*h^2 + 20*l*h^3 + 11*l*h^4 + 6*l^2*h + 36*l^2*h^2 + 85*l^2*h^3 + 40*l^2*h^4 + l^3*h + 5*l^3*h^2 + 10*l^3*h^3 + 3*l^3*h^4 := by
  rw [leafPart,table0211]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem table0212 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 2 (Fin.cons 1 (Fin.cons 2 c))))))) =
    [((1,4),9), ((2,4),36), ((1,3),5), ((2,3),25), ((1,2),1), ((2,2),6), ((3,4),5), ((3,3),4), ((3,2),1)] := by decide +kernel

private theorem part0212 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 2 (Fin.cons 1 (Fin.cons 2 c)))))) l h =
    l*h^2 + 5*l*h^3 + 9*l*h^4 + 6*l^2*h^2 + 25*l^2*h^3 + 36*l^2*h^4 + l^3*h^2 + 4*l^3*h^3 + 5*l^3*h^4 := by
  rw [leafPart,table0212]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem part021 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 2 (Fin.cons 1 c))))) l h =
    l*h + 8*l*h^2 + 25*l*h^3 + 20*l*h^4 + 6*l^2*h + 42*l^2*h^2 + 110*l^2*h^3 + 76*l^2*h^4 + l^3*h + 6*l^3*h^2 + 14*l^3*h^3 + 8*l^3*h^4 := by
  rw [splitPart,part0210,part0211,part0212]
  ring

private theorem part0220 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 2 (Fin.cons 2 (Fin.cons 0 c)))))) l h = 0 := by
  have forbid (c : Fin 7 → Tag) : ¬ allowed ((fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 2 (Fin.cons 2 (Fin.cons 0 c)))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : (1 + (0 + (0 + (1 + (if c 0 = 0 then 1 else 0 : ℕ))))) < 2 := fast.1.1

    omega
  simp [part,forbid]

private theorem table0221 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 2 (Fin.cons 2 (Fin.cons 1 c))))))) =
    [((1,4),10), ((2,4),40), ((1,3),5), ((2,3),25), ((1,2),1), ((2,2),6), ((3,4),6), ((3,3),4), ((3,2),1)] := by decide +kernel

private theorem part0221 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 2 (Fin.cons 2 (Fin.cons 1 c)))))) l h =
    l*h^2 + 5*l*h^3 + 10*l*h^4 + 6*l^2*h^2 + 25*l^2*h^3 + 40*l^2*h^4 + l^3*h^2 + 4*l^3*h^3 + 6*l^3*h^4 := by
  rw [leafPart,table0221]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem part0222 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 2 (Fin.cons 2 (Fin.cons 2 c)))))) l h = 0 := by
  have forbid (c : Fin 7 → Tag) : ¬ allowed ((fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 2 (Fin.cons 2 (Fin.cons 2 c)))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : 2 < (1 + (0 + (0 + (0 + (if c 0 ≠ 2 then 1 else 0 : ℕ))))) := fast.1.2
    have b0 : (if c 0 ≠ 2 then 1 else 0 : ℕ) ≤ 1 := by split <;> decide
    omega
  simp [part,forbid]

private theorem part022 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 2 (Fin.cons 2 c))))) l h =
    l*h^2 + 5*l*h^3 + 10*l*h^4 + 6*l^2*h^2 + 25*l^2*h^3 + 40*l^2*h^4 + l^3*h^2 + 4*l^3*h^3 + 6*l^3*h^4 := by
  rw [splitPart,part0220,part0221,part0222]
  ring

private theorem part02 (l h : ℕ) : part (fun c : Fin 9 → Tag => (show Fin 11 → Tag from (Fin.cons 0 (Fin.cons 2 c)))) l h =
    l*h + 9*l*h^2 + 30*l*h^3 + 30*l*h^4 + 6*l^2*h + 48*l^2*h^2 + 135*l^2*h^3 + 116*l^2*h^4 + l^3*h + 7*l^3*h^2 + 18*l^3*h^3 + 14*l^3*h^4 := by
  rw [splitPart,part020,part021,part022]
  ring

private theorem part0 (l h : ℕ) : part (fun c : Fin 10 → Tag => (show Fin 11 → Tag from (Fin.cons 0 c))) l h =
    l + 10*l*h + 45*l*h^2 + 80*l*h^3 + 50*l*h^4 + 6*l^2 + 54*l^2*h + 216*l^2*h^2 + 342*l^2*h^3 + 190*l^2*h^4 + l^3 + 8*l^3*h + 28*l^3*h^2 + 40*l^3*h^3 + 20*l^3*h^4 := by
  rw [splitPart,part00,part01,part02]
  ring

private theorem part100 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 0 (Fin.cons 0 c))))) l h = 0 := by
  have forbid (c : Fin 8 → Tag) : ¬ allowed ((fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 0 (Fin.cons 0 c))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : (0 + (1 + (1 + ((if c 0 = 0 then 1 else 0 : ℕ) + (if c 1 = 0 then 1 else 0 : ℕ))))) < 2 := fast.1.1

    omega
  simp [part,forbid]

private theorem part1010 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 0 (Fin.cons 1 (Fin.cons 0 c)))))) l h = 0 := by
  have forbid (c : Fin 7 → Tag) : ¬ allowed ((fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 0 (Fin.cons 1 (Fin.cons 0 c)))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : (0 + (1 + (0 + (1 + (if c 0 = 0 then 1 else 0 : ℕ))))) < 2 := fast.1.1

    omega
  simp [part,forbid]

private theorem table1011 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 0 (Fin.cons 1 (Fin.cons 1 c))))))) =
    [((1,4),1), ((1,3),13), ((2,3),41), ((1,2),21), ((2,2),75), ((2,4),3), ((1,1),7), ((2,1),30), ((1,0),1), ((2,0),5)] := by decide +kernel

private theorem part1011 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 0 (Fin.cons 1 (Fin.cons 1 c)))))) l h =
    l + 7*l*h + 21*l*h^2 + 13*l*h^3 + l*h^4 + 5*l^2 + 30*l^2*h + 75*l^2*h^2 + 41*l^2*h^3 + 3*l^2*h^4 := by
  rw [leafPart,table1011]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem table1012 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 0 (Fin.cons 1 (Fin.cons 2 c))))))) =
    [((1,4),5), ((2,4),15), ((1,3),15), ((2,3),51), ((1,2),7), ((2,2),30), ((1,1),1), ((2,1),5)] := by decide +kernel

private theorem part1012 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 0 (Fin.cons 1 (Fin.cons 2 c)))))) l h =
    l*h + 7*l*h^2 + 15*l*h^3 + 5*l*h^4 + 5*l^2*h + 30*l^2*h^2 + 51*l^2*h^3 + 15*l^2*h^4 := by
  rw [leafPart,table1012]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem part101 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 0 (Fin.cons 1 c))))) l h =
    l + 8*l*h + 28*l*h^2 + 28*l*h^3 + 6*l*h^4 + 5*l^2 + 35*l^2*h + 105*l^2*h^2 + 92*l^2*h^3 + 18*l^2*h^4 := by
  rw [splitPart,part1010,part1011,part1012]
  ring

private theorem part1020 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 0 (Fin.cons 2 (Fin.cons 0 c)))))) l h = 0 := by
  have forbid (c : Fin 7 → Tag) : ¬ allowed ((fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 0 (Fin.cons 2 (Fin.cons 0 c)))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : (0 + (1 + (0 + (1 + (if c 0 = 0 then 1 else 0 : ℕ))))) < 2 := fast.1.1

    omega
  simp [part,forbid]

private theorem table1021 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 0 (Fin.cons 2 (Fin.cons 1 c))))))) =
    [((1,4),8), ((2,4),24), ((1,3),18), ((2,3),62), ((1,2),7), ((2,2),30), ((1,1),1), ((2,1),5)] := by decide +kernel

private theorem part1021 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 0 (Fin.cons 2 (Fin.cons 1 c)))))) l h =
    l*h + 7*l*h^2 + 18*l*h^3 + 8*l*h^4 + 5*l^2*h + 30*l^2*h^2 + 62*l^2*h^3 + 24*l^2*h^4 := by
  rw [leafPart,table1021]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem table1022 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 0 (Fin.cons 2 (Fin.cons 2 c))))))) =
    [((1,4),6), ((2,4),18), ((1,3),4), ((2,3),16), ((1,2),1), ((2,2),5)] := by decide +kernel

private theorem part1022 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 0 (Fin.cons 2 (Fin.cons 2 c)))))) l h =
    l*h^2 + 4*l*h^3 + 6*l*h^4 + 5*l^2*h^2 + 16*l^2*h^3 + 18*l^2*h^4 := by
  rw [leafPart,table1022]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem part102 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 0 (Fin.cons 2 c))))) l h =
    l*h + 8*l*h^2 + 22*l*h^3 + 14*l*h^4 + 5*l^2*h + 35*l^2*h^2 + 78*l^2*h^3 + 42*l^2*h^4 := by
  rw [splitPart,part1020,part1021,part1022]
  ring

private theorem part10 (l h : ℕ) : part (fun c : Fin 9 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 0 c)))) l h =
    l + 9*l*h + 36*l*h^2 + 50*l*h^3 + 20*l*h^4 + 5*l^2 + 40*l^2*h + 140*l^2*h^2 + 170*l^2*h^3 + 60*l^2*h^4 := by
  rw [splitPart,part100,part101,part102]
  ring

private theorem part1100 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 1 (Fin.cons 0 (Fin.cons 0 c)))))) l h = 0 := by
  have forbid (c : Fin 7 → Tag) : ¬ allowed ((fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 1 (Fin.cons 0 (Fin.cons 0 c)))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : (0 + (0 + (1 + (1 + (if c 0 = 0 then 1 else 0 : ℕ))))) < 2 := fast.1.1

    omega
  simp [part,forbid]

private theorem table1101 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 1 (Fin.cons 0 (Fin.cons 1 c))))))) =
    [((1,4),1), ((1,3),13), ((2,3),31), ((1,2),21), ((2,2),60), ((2,4),2), ((1,1),7), ((2,1),24), ((1,0),1), ((2,0),4)] := by decide +kernel

private theorem part1101 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 1 (Fin.cons 0 (Fin.cons 1 c)))))) l h =
    l + 7*l*h + 21*l*h^2 + 13*l*h^3 + l*h^4 + 4*l^2 + 24*l^2*h + 60*l^2*h^2 + 31*l^2*h^3 + 2*l^2*h^4 := by
  rw [leafPart,table1101]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem table1102 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 1 (Fin.cons 0 (Fin.cons 2 c))))))) =
    [((1,4),5), ((2,4),10), ((1,3),15), ((2,3),39), ((1,2),7), ((2,2),24), ((1,1),1), ((2,1),4)] := by decide +kernel

private theorem part1102 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 1 (Fin.cons 0 (Fin.cons 2 c)))))) l h =
    l*h + 7*l*h^2 + 15*l*h^3 + 5*l*h^4 + 4*l^2*h + 24*l^2*h^2 + 39*l^2*h^3 + 10*l^2*h^4 := by
  rw [leafPart,table1102]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem part110 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 1 (Fin.cons 0 c))))) l h =
    l + 8*l*h + 28*l*h^2 + 28*l*h^3 + 6*l*h^4 + 4*l^2 + 28*l^2*h + 84*l^2*h^2 + 70*l^2*h^3 + 12*l^2*h^4 := by
  rw [splitPart,part1100,part1101,part1102]
  ring

private theorem table1110 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 1 (Fin.cons 1 (Fin.cons 0 c))))))) =
    [((1,4),1), ((1,3),13), ((2,3),21), ((1,2),21), ((2,2),45), ((2,4),1), ((1,1),7), ((2,1),18), ((1,0),1), ((2,0),3)] := by decide +kernel

private theorem part1110 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 1 (Fin.cons 1 (Fin.cons 0 c)))))) l h =
    l + 7*l*h + 21*l*h^2 + 13*l*h^3 + l*h^4 + 3*l^2 + 18*l^2*h + 45*l^2*h^2 + 21*l^2*h^3 + l^2*h^4 := by
  rw [leafPart,table1110]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem table1111 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 1 (Fin.cons 1 (Fin.cons 1 c))))))) =
    [((0,4),1), ((0,3),13), ((1,3),52), ((0,2),21), ((1,2),105), ((1,4),3), ((0,1),7), ((1,1),42), ((2,3),6), ((2,2),30), ((2,1),15), ((0,0),1), ((1,0),7), ((2,0),3)] := by decide +kernel

private theorem part1111 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 1 (Fin.cons 1 (Fin.cons 1 c)))))) l h =
    1 + 7*h + 21*h^2 + 13*h^3 + h^4 + 7*l + 42*l*h + 105*l*h^2 + 52*l*h^3 + 3*l*h^4 + 3*l^2 + 15*l^2*h + 30*l^2*h^2 + 6*l^2*h^3 := by
  rw [leafPart,table1111]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem table1112 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 1 (Fin.cons 1 (Fin.cons 2 c))))))) =
    [((0,4),5), ((1,4),20), ((0,3),15), ((1,3),75), ((0,2),7), ((1,2),42), ((2,4),2), ((2,3),21), ((2,2),15), ((0,1),1), ((1,1),7), ((2,1),3)] := by decide +kernel

private theorem part1112 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 1 (Fin.cons 1 (Fin.cons 2 c)))))) l h =
    h + 7*h^2 + 15*h^3 + 5*h^4 + 7*l*h + 42*l*h^2 + 75*l*h^3 + 20*l*h^4 + 3*l^2*h + 15*l^2*h^2 + 21*l^2*h^3 + 2*l^2*h^4 := by
  rw [leafPart,table1112]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem part111 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 1 (Fin.cons 1 c))))) l h =
    1 + 8*h + 28*h^2 + 28*h^3 + 6*h^4 + 8*l + 56*l*h + 168*l*h^2 + 140*l*h^3 + 24*l*h^4 + 6*l^2 + 36*l^2*h + 90*l^2*h^2 + 48*l^2*h^3 + 3*l^2*h^4 := by
  rw [splitPart,part1110,part1111,part1112]
  ring

private theorem table1120 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 1 (Fin.cons 2 (Fin.cons 0 c))))))) =
    [((1,4),8), ((2,4),11), ((1,3),18), ((2,3),36), ((1,2),7), ((2,2),18), ((1,1),1), ((2,1),3)] := by decide +kernel

private theorem part1120 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 1 (Fin.cons 2 (Fin.cons 0 c)))))) l h =
    l*h + 7*l*h^2 + 18*l*h^3 + 8*l*h^4 + 3*l^2*h + 18*l^2*h^2 + 36*l^2*h^3 + 11*l^2*h^4 := by
  rw [leafPart,table1120]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem table1121 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 1 (Fin.cons 2 (Fin.cons 1 c))))))) =
    [((0,4),8), ((1,4),32), ((0,3),18), ((1,3),90), ((0,2),7), ((1,2),42), ((2,4),4), ((2,3),27), ((2,2),15), ((0,1),1), ((1,1),7), ((2,1),3)] := by decide +kernel

private theorem part1121 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 1 (Fin.cons 2 (Fin.cons 1 c)))))) l h =
    h + 7*h^2 + 18*h^3 + 8*h^4 + 7*l*h + 42*l*h^2 + 90*l*h^3 + 32*l*h^4 + 3*l^2*h + 15*l^2*h^2 + 27*l^2*h^3 + 4*l^2*h^4 := by
  rw [leafPart,table1121]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem table1122 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 1 (Fin.cons 2 (Fin.cons 2 c))))))) =
    [((0,4),6), ((1,4),30), ((0,3),4), ((1,3),24), ((0,2),1), ((1,2),7), ((2,4),9), ((2,3),9), ((2,2),3)] := by decide +kernel

private theorem part1122 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 1 (Fin.cons 2 (Fin.cons 2 c)))))) l h =
    h^2 + 4*h^3 + 6*h^4 + 7*l*h^2 + 24*l*h^3 + 30*l*h^4 + 3*l^2*h^2 + 9*l^2*h^3 + 9*l^2*h^4 := by
  rw [leafPart,table1122]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem part112 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 1 (Fin.cons 2 c))))) l h =
    h + 8*h^2 + 22*h^3 + 14*h^4 + 8*l*h + 56*l*h^2 + 132*l*h^3 + 70*l*h^4 + 6*l^2*h + 36*l^2*h^2 + 72*l^2*h^3 + 24*l^2*h^4 := by
  rw [splitPart,part1120,part1121,part1122]
  ring

private theorem part11 (l h : ℕ) : part (fun c : Fin 9 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 1 c)))) l h =
    1 + 9*h + 36*h^2 + 50*h^3 + 20*h^4 + 9*l + 72*l*h + 252*l*h^2 + 300*l*h^3 + 100*l*h^4 + 10*l^2 + 70*l^2*h + 210*l^2*h^2 + 190*l^2*h^3 + 39*l^2*h^4 := by
  rw [splitPart,part110,part111,part112]
  ring

private theorem part1200 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 2 (Fin.cons 0 (Fin.cons 0 c)))))) l h = 0 := by
  have forbid (c : Fin 7 → Tag) : ¬ allowed ((fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 2 (Fin.cons 0 (Fin.cons 0 c)))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : (0 + (0 + (1 + (1 + (if c 0 = 0 then 1 else 0 : ℕ))))) < 2 := fast.1.1

    omega
  simp [part,forbid]

private theorem table1201 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 2 (Fin.cons 0 (Fin.cons 1 c))))))) =
    [((1,4),11), ((2,4),25), ((1,3),20), ((2,3),56), ((1,2),7), ((2,2),24), ((1,1),1), ((2,1),4)] := by decide +kernel

private theorem part1201 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 2 (Fin.cons 0 (Fin.cons 1 c)))))) l h =
    l*h + 7*l*h^2 + 20*l*h^3 + 11*l*h^4 + 4*l^2*h + 24*l^2*h^2 + 56*l^2*h^3 + 25*l^2*h^4 := by
  rw [leafPart,table1201]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem table1202 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 2 (Fin.cons 0 (Fin.cons 2 c))))))) =
    [((1,4),9), ((2,4),21), ((1,3),5), ((2,3),16), ((1,2),1), ((2,2),4)] := by decide +kernel

private theorem part1202 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 2 (Fin.cons 0 (Fin.cons 2 c)))))) l h =
    l*h^2 + 5*l*h^3 + 9*l*h^4 + 4*l^2*h^2 + 16*l^2*h^3 + 21*l^2*h^4 := by
  rw [leafPart,table1202]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem part120 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 2 (Fin.cons 0 c))))) l h =
    l*h + 8*l*h^2 + 25*l*h^3 + 20*l*h^4 + 4*l^2*h + 28*l^2*h^2 + 72*l^2*h^3 + 46*l^2*h^4 := by
  rw [splitPart,part1200,part1201,part1202]
  ring

private theorem table1210 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 2 (Fin.cons 1 (Fin.cons 0 c))))))) =
    [((1,4),11), ((2,4),17), ((1,3),20), ((2,3),42), ((1,2),7), ((2,2),18), ((1,1),1), ((2,1),3)] := by decide +kernel

private theorem part1210 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 2 (Fin.cons 1 (Fin.cons 0 c)))))) l h =
    l*h + 7*l*h^2 + 20*l*h^3 + 11*l*h^4 + 3*l^2*h + 18*l^2*h^2 + 42*l^2*h^3 + 17*l^2*h^4 := by
  rw [leafPart,table1210]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem table1211 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 2 (Fin.cons 1 (Fin.cons 1 c))))))) =
    [((0,4),11), ((1,4),44), ((0,3),20), ((1,3),100), ((0,2),7), ((1,2),42), ((2,4),6), ((2,3),30), ((2,2),15), ((0,1),1), ((1,1),7), ((2,1),3)] := by decide +kernel

private theorem part1211 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 2 (Fin.cons 1 (Fin.cons 1 c)))))) l h =
    h + 7*h^2 + 20*h^3 + 11*h^4 + 7*l*h + 42*l*h^2 + 100*l*h^3 + 44*l*h^4 + 3*l^2*h + 15*l^2*h^2 + 30*l^2*h^3 + 6*l^2*h^4 := by
  rw [leafPart,table1211]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem table1212 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 2 (Fin.cons 1 (Fin.cons 2 c))))))) =
    [((0,4),9), ((1,4),45), ((0,3),5), ((1,3),30), ((0,2),1), ((1,2),7), ((2,4),15), ((2,3),12), ((2,2),3)] := by decide +kernel

private theorem part1212 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 2 (Fin.cons 1 (Fin.cons 2 c)))))) l h =
    h^2 + 5*h^3 + 9*h^4 + 7*l*h^2 + 30*l*h^3 + 45*l*h^4 + 3*l^2*h^2 + 12*l^2*h^3 + 15*l^2*h^4 := by
  rw [leafPart,table1212]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem part121 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 2 (Fin.cons 1 c))))) l h =
    h + 8*h^2 + 25*h^3 + 20*h^4 + 8*l*h + 56*l*h^2 + 150*l*h^3 + 100*l*h^4 + 6*l^2*h + 36*l^2*h^2 + 84*l^2*h^3 + 38*l^2*h^4 := by
  rw [splitPart,part1210,part1211,part1212]
  ring

private theorem table1220 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 2 (Fin.cons 2 (Fin.cons 0 c))))))) =
    [((1,4),10), ((2,4),18), ((1,3),5), ((2,3),12), ((1,2),1), ((2,2),3)] := by decide +kernel

private theorem part1220 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 2 (Fin.cons 2 (Fin.cons 0 c)))))) l h =
    l*h^2 + 5*l*h^3 + 10*l*h^4 + 3*l^2*h^2 + 12*l^2*h^3 + 18*l^2*h^4 := by
  rw [leafPart,table1220]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem table1221 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 2 (Fin.cons 2 (Fin.cons 1 c))))))) =
    [((0,4),10), ((1,4),50), ((0,3),5), ((1,3),30), ((0,2),1), ((1,2),7), ((2,4),18), ((2,3),12), ((2,2),3)] := by decide +kernel

private theorem part1221 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 2 (Fin.cons 2 (Fin.cons 1 c)))))) l h =
    h^2 + 5*h^3 + 10*h^4 + 7*l*h^2 + 30*l*h^3 + 50*l*h^4 + 3*l^2*h^2 + 12*l^2*h^3 + 18*l^2*h^4 := by
  rw [leafPart,table1221]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem part1222 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 2 (Fin.cons 2 (Fin.cons 2 c)))))) l h = 0 := by
  have forbid (c : Fin 7 → Tag) : ¬ allowed ((fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 2 (Fin.cons 2 (Fin.cons 2 c)))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : 2 < (1 + (0 + (0 + (0 + (if c 0 ≠ 2 then 1 else 0 : ℕ))))) := fast.1.2
    have b0 : (if c 0 ≠ 2 then 1 else 0 : ℕ) ≤ 1 := by split <;> decide
    omega
  simp [part,forbid]

private theorem part122 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 2 (Fin.cons 2 c))))) l h =
    h^2 + 5*h^3 + 10*h^4 + 8*l*h^2 + 35*l*h^3 + 60*l*h^4 + 6*l^2*h^2 + 24*l^2*h^3 + 36*l^2*h^4 := by
  rw [splitPart,part1220,part1221,part1222]
  ring

private theorem part12 (l h : ℕ) : part (fun c : Fin 9 → Tag => (show Fin 11 → Tag from (Fin.cons 1 (Fin.cons 2 c)))) l h =
    h + 9*h^2 + 30*h^3 + 30*h^4 + 9*l*h + 72*l*h^2 + 210*l*h^3 + 180*l*h^4 + 10*l^2*h + 70*l^2*h^2 + 180*l^2*h^3 + 120*l^2*h^4 := by
  rw [splitPart,part120,part121,part122]
  ring

private theorem part1 (l h : ℕ) : part (fun c : Fin 10 → Tag => (show Fin 11 → Tag from (Fin.cons 1 c))) l h =
    1 + 10*h + 45*h^2 + 80*h^3 + 50*h^4 + 10*l + 90*l*h + 360*l*h^2 + 560*l*h^3 + 300*l*h^4 + 15*l^2 + 120*l^2*h + 420*l^2*h^2 + 540*l^2*h^3 + 219*l^2*h^4 := by
  rw [splitPart,part10,part11,part12]
  ring

private theorem part200 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 0 (Fin.cons 0 c))))) l h = 0 := by
  have forbid (c : Fin 8 → Tag) : ¬ allowed ((fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 0 (Fin.cons 0 c))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : (0 + (1 + (1 + ((if c 0 = 0 then 1 else 0 : ℕ) + (if c 1 = 0 then 1 else 0 : ℕ))))) < 2 := fast.1.1

    omega
  simp [part,forbid]

private theorem part2010 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 0 (Fin.cons 1 (Fin.cons 0 c)))))) l h = 0 := by
  have forbid (c : Fin 7 → Tag) : ¬ allowed ((fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 0 (Fin.cons 1 (Fin.cons 0 c)))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : (0 + (1 + (0 + (1 + (if c 0 = 0 then 1 else 0 : ℕ))))) < 2 := fast.1.1

    omega
  simp [part,forbid]

private theorem table2011 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 0 (Fin.cons 1 (Fin.cons 1 c))))))) =
    [((1,5),1), ((1,4),13), ((2,4),41), ((1,3),21), ((2,3),75), ((2,5),3), ((1,2),7), ((2,2),30), ((1,1),1), ((2,1),5)] := by decide +kernel

private theorem part2011 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 0 (Fin.cons 1 (Fin.cons 1 c)))))) l h =
    l*h + 7*l*h^2 + 21*l*h^3 + 13*l*h^4 + l*h^5 + 5*l^2*h + 30*l^2*h^2 + 75*l^2*h^3 + 41*l^2*h^4 + 3*l^2*h^5 := by
  rw [leafPart,table2011]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem table2012 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 0 (Fin.cons 1 (Fin.cons 2 c))))))) =
    [((1,5),2), ((1,4),12), ((2,4),39), ((2,5),6), ((1,3),6), ((2,3),25), ((1,2),1), ((2,2),5)] := by decide +kernel

private theorem part2012 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 0 (Fin.cons 1 (Fin.cons 2 c)))))) l h =
    l*h^2 + 6*l*h^3 + 12*l*h^4 + 2*l*h^5 + 5*l^2*h^2 + 25*l^2*h^3 + 39*l^2*h^4 + 6*l^2*h^5 := by
  rw [leafPart,table2012]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem part201 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 0 (Fin.cons 1 c))))) l h =
    l*h + 8*l*h^2 + 27*l*h^3 + 25*l*h^4 + 3*l*h^5 + 5*l^2*h + 35*l^2*h^2 + 100*l^2*h^3 + 80*l^2*h^4 + 9*l^2*h^5 := by
  rw [splitPart,part2010,part2011,part2012]
  ring

private theorem part2020 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 0 (Fin.cons 2 (Fin.cons 0 c)))))) l h = 0 := by
  have forbid (c : Fin 7 → Tag) : ¬ allowed ((fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 0 (Fin.cons 2 (Fin.cons 0 c)))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : (0 + (1 + (0 + (1 + (if c 0 = 0 then 1 else 0 : ℕ))))) < 2 := fast.1.1

    omega
  simp [part,forbid]

private theorem table2021 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 0 (Fin.cons 2 (Fin.cons 1 c))))))) =
    [((1,5),3), ((1,4),14), ((2,4),46), ((2,5),9), ((1,3),6), ((2,3),25), ((1,2),1), ((2,2),5)] := by decide +kernel

private theorem part2021 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 0 (Fin.cons 2 (Fin.cons 1 c)))))) l h =
    l*h^2 + 6*l*h^3 + 14*l*h^4 + 3*l*h^5 + 5*l^2*h^2 + 25*l^2*h^3 + 46*l^2*h^4 + 9*l^2*h^5 := by
  rw [leafPart,table2021]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem part2022 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 0 (Fin.cons 2 (Fin.cons 2 c)))))) l h = 0 := by
  have forbid (c : Fin 7 → Tag) : ¬ allowed ((fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 0 (Fin.cons 2 (Fin.cons 2 c)))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : 2 < (0 + (1 + (0 + (0 + (if c 0 ≠ 2 then 1 else 0 : ℕ))))) := fast.1.2
    have b0 : (if c 0 ≠ 2 then 1 else 0 : ℕ) ≤ 1 := by split <;> decide
    omega
  simp [part,forbid]

private theorem part202 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 0 (Fin.cons 2 c))))) l h =
    l*h^2 + 6*l*h^3 + 14*l*h^4 + 3*l*h^5 + 5*l^2*h^2 + 25*l^2*h^3 + 46*l^2*h^4 + 9*l^2*h^5 := by
  rw [splitPart,part2020,part2021,part2022]
  ring

private theorem part20 (l h : ℕ) : part (fun c : Fin 9 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 0 c)))) l h =
    l*h + 9*l*h^2 + 33*l*h^3 + 39*l*h^4 + 6*l*h^5 + 5*l^2*h + 40*l^2*h^2 + 125*l^2*h^3 + 126*l^2*h^4 + 18*l^2*h^5 := by
  rw [splitPart,part200,part201,part202]
  ring

private theorem part2100 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 1 (Fin.cons 0 (Fin.cons 0 c)))))) l h = 0 := by
  have forbid (c : Fin 7 → Tag) : ¬ allowed ((fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 1 (Fin.cons 0 (Fin.cons 0 c)))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : (0 + (0 + (1 + (1 + (if c 0 = 0 then 1 else 0 : ℕ))))) < 2 := fast.1.1

    omega
  simp [part,forbid]

private theorem table2101 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 1 (Fin.cons 0 (Fin.cons 1 c))))))) =
    [((1,5),1), ((1,4),13), ((2,4),31), ((1,3),21), ((2,3),60), ((2,5),2), ((1,2),7), ((2,2),24), ((1,1),1), ((2,1),4)] := by decide +kernel

private theorem part2101 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 1 (Fin.cons 0 (Fin.cons 1 c)))))) l h =
    l*h + 7*l*h^2 + 21*l*h^3 + 13*l*h^4 + l*h^5 + 4*l^2*h + 24*l^2*h^2 + 60*l^2*h^3 + 31*l^2*h^4 + 2*l^2*h^5 := by
  rw [leafPart,table2101]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem table2102 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 1 (Fin.cons 0 (Fin.cons 2 c))))))) =
    [((1,5),2), ((1,4),12), ((2,4),30), ((2,5),4), ((1,3),6), ((2,3),20), ((1,2),1), ((2,2),4)] := by decide +kernel

private theorem part2102 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 1 (Fin.cons 0 (Fin.cons 2 c)))))) l h =
    l*h^2 + 6*l*h^3 + 12*l*h^4 + 2*l*h^5 + 4*l^2*h^2 + 20*l^2*h^3 + 30*l^2*h^4 + 4*l^2*h^5 := by
  rw [leafPart,table2102]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem part210 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 1 (Fin.cons 0 c))))) l h =
    l*h + 8*l*h^2 + 27*l*h^3 + 25*l*h^4 + 3*l*h^5 + 4*l^2*h + 28*l^2*h^2 + 80*l^2*h^3 + 61*l^2*h^4 + 6*l^2*h^5 := by
  rw [splitPart,part2100,part2101,part2102]
  ring

private theorem table2110 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 1 (Fin.cons 1 (Fin.cons 0 c))))))) =
    [((1,5),1), ((1,4),13), ((2,4),21), ((1,3),21), ((2,3),45), ((2,5),1), ((1,2),7), ((2,2),18), ((1,1),1), ((2,1),3)] := by decide +kernel

private theorem part2110 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 1 (Fin.cons 1 (Fin.cons 0 c)))))) l h =
    l*h + 7*l*h^2 + 21*l*h^3 + 13*l*h^4 + l*h^5 + 3*l^2*h + 18*l^2*h^2 + 45*l^2*h^3 + 21*l^2*h^4 + l^2*h^5 := by
  rw [leafPart,table2110]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem table2111 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 1 (Fin.cons 1 (Fin.cons 1 c))))))) =
    [((0,5),1), ((0,4),13), ((1,4),52), ((0,3),21), ((1,3),105), ((1,5),3), ((0,2),7), ((1,2),42), ((2,4),6), ((2,3),30), ((2,2),15), ((0,1),1), ((1,1),7), ((2,1),3)] := by decide +kernel

private theorem part2111 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 1 (Fin.cons 1 (Fin.cons 1 c)))))) l h =
    h + 7*h^2 + 21*h^3 + 13*h^4 + h^5 + 7*l*h + 42*l*h^2 + 105*l*h^3 + 52*l*h^4 + 3*l*h^5 + 3*l^2*h + 15*l^2*h^2 + 30*l^2*h^3 + 6*l^2*h^4 := by
  rw [leafPart,table2111]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem table2112 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 1 (Fin.cons 1 (Fin.cons 2 c))))))) =
    [((0,5),2), ((0,4),12), ((1,4),60), ((1,5),8), ((0,3),6), ((1,3),36), ((0,2),1), ((1,2),7), ((2,4),19), ((2,3),14), ((2,2),3), ((2,5),1)] := by decide +kernel

private theorem part2112 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 1 (Fin.cons 1 (Fin.cons 2 c)))))) l h =
    h^2 + 6*h^3 + 12*h^4 + 2*h^5 + 7*l*h^2 + 36*l*h^3 + 60*l*h^4 + 8*l*h^5 + 3*l^2*h^2 + 14*l^2*h^3 + 19*l^2*h^4 + l^2*h^5 := by
  rw [leafPart,table2112]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem part211 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 1 (Fin.cons 1 c))))) l h =
    h + 8*h^2 + 27*h^3 + 25*h^4 + 3*h^5 + 8*l*h + 56*l*h^2 + 162*l*h^3 + 125*l*h^4 + 12*l*h^5 + 6*l^2*h + 36*l^2*h^2 + 89*l^2*h^3 + 46*l^2*h^4 + 2*l^2*h^5 := by
  rw [splitPart,part2110,part2111,part2112]
  ring

private theorem table2120 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 1 (Fin.cons 2 (Fin.cons 0 c))))))) =
    [((1,5),3), ((1,4),14), ((2,4),27), ((2,5),4), ((1,3),6), ((2,3),15), ((1,2),1), ((2,2),3)] := by decide +kernel

private theorem part2120 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 1 (Fin.cons 2 (Fin.cons 0 c)))))) l h =
    l*h^2 + 6*l*h^3 + 14*l*h^4 + 3*l*h^5 + 3*l^2*h^2 + 15*l^2*h^3 + 27*l^2*h^4 + 4*l^2*h^5 := by
  rw [leafPart,table2120]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem table2121 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 1 (Fin.cons 2 (Fin.cons 1 c))))))) =
    [((0,5),3), ((0,4),14), ((1,4),70), ((1,5),12), ((0,3),6), ((1,3),36), ((0,2),1), ((1,2),7), ((2,4),24), ((2,3),14), ((2,2),3), ((2,5),2)] := by decide +kernel

private theorem part2121 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 1 (Fin.cons 2 (Fin.cons 1 c)))))) l h =
    h^2 + 6*h^3 + 14*h^4 + 3*h^5 + 7*l*h^2 + 36*l*h^3 + 70*l*h^4 + 12*l*h^5 + 3*l^2*h^2 + 14*l^2*h^3 + 24*l^2*h^4 + 2*l^2*h^5 := by
  rw [leafPart,table2121]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem part2122 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 1 (Fin.cons 2 (Fin.cons 2 c)))))) l h = 0 := by
  have forbid (c : Fin 7 → Tag) : ¬ allowed ((fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 1 (Fin.cons 2 (Fin.cons 2 c)))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : 2 < (0 + (1 + (0 + (0 + (if c 0 ≠ 2 then 1 else 0 : ℕ))))) := fast.1.2
    have b0 : (if c 0 ≠ 2 then 1 else 0 : ℕ) ≤ 1 := by split <;> decide
    omega
  simp [part,forbid]

private theorem part212 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 1 (Fin.cons 2 c))))) l h =
    h^2 + 6*h^3 + 14*h^4 + 3*h^5 + 8*l*h^2 + 42*l*h^3 + 84*l*h^4 + 15*l*h^5 + 6*l^2*h^2 + 29*l^2*h^3 + 51*l^2*h^4 + 6*l^2*h^5 := by
  rw [splitPart,part2120,part2121,part2122]
  ring

private theorem part21 (l h : ℕ) : part (fun c : Fin 9 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 1 c)))) l h =
    h + 9*h^2 + 33*h^3 + 39*h^4 + 6*h^5 + 9*l*h + 72*l*h^2 + 231*l*h^3 + 234*l*h^4 + 30*l*h^5 + 10*l^2*h + 70*l^2*h^2 + 198*l^2*h^3 + 158*l^2*h^4 + 14*l^2*h^5 := by
  rw [splitPart,part210,part211,part212]
  ring

private theorem part2200 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 2 (Fin.cons 0 (Fin.cons 0 c)))))) l h = 0 := by
  have forbid (c : Fin 7 → Tag) : ¬ allowed ((fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 2 (Fin.cons 0 (Fin.cons 0 c)))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : (0 + (0 + (1 + (1 + (if c 0 = 0 then 1 else 0 : ℕ))))) < 2 := fast.1.1

    omega
  simp [part,forbid]

private theorem table2201 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 2 (Fin.cons 0 (Fin.cons 1 c))))))) =
    [((1,5),4), ((1,4),15), ((2,4),40), ((2,5),9), ((1,3),6), ((2,3),20), ((1,2),1), ((2,2),4)] := by decide +kernel

private theorem part2201 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 2 (Fin.cons 0 (Fin.cons 1 c)))))) l h =
    l*h^2 + 6*l*h^3 + 15*l*h^4 + 4*l*h^5 + 4*l^2*h^2 + 20*l^2*h^3 + 40*l^2*h^4 + 9*l^2*h^5 := by
  rw [leafPart,table2201]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem part2202 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 2 (Fin.cons 0 (Fin.cons 2 c)))))) l h = 0 := by
  have forbid (c : Fin 7 → Tag) : ¬ allowed ((fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 2 (Fin.cons 0 (Fin.cons 2 c)))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : 2 < (0 + (0 + (1 + (0 + (if c 0 ≠ 2 then 1 else 0 : ℕ))))) := fast.1.2
    have b0 : (if c 0 ≠ 2 then 1 else 0 : ℕ) ≤ 1 := by split <;> decide
    omega
  simp [part,forbid]

private theorem part220 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 2 (Fin.cons 0 c))))) l h =
    l*h^2 + 6*l*h^3 + 15*l*h^4 + 4*l*h^5 + 4*l^2*h^2 + 20*l^2*h^3 + 40*l^2*h^4 + 9*l^2*h^5 := by
  rw [splitPart,part2200,part2201,part2202]
  ring

private theorem table2210 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 2 (Fin.cons 1 (Fin.cons 0 c))))))) =
    [((1,5),4), ((1,4),15), ((2,4),30), ((2,5),6), ((1,3),6), ((2,3),15), ((1,2),1), ((2,2),3)] := by decide +kernel

private theorem part2210 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 2 (Fin.cons 1 (Fin.cons 0 c)))))) l h =
    l*h^2 + 6*l*h^3 + 15*l*h^4 + 4*l*h^5 + 3*l^2*h^2 + 15*l^2*h^3 + 30*l^2*h^4 + 6*l^2*h^5 := by
  rw [leafPart,table2210]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem table2211 : tally (sectionKeys (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 2 (Fin.cons 1 (Fin.cons 1 c))))))) =
    [((0,5),4), ((0,4),15), ((1,4),75), ((1,5),16), ((0,3),6), ((1,3),36), ((0,2),1), ((1,2),7), ((2,4),26), ((2,3),14), ((2,2),3), ((2,5),3)] := by decide +kernel

private theorem part2211 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 2 (Fin.cons 1 (Fin.cons 1 c)))))) l h =
    h^2 + 6*h^3 + 15*h^4 + 4*h^5 + 7*l*h^2 + 36*l*h^3 + 75*l*h^4 + 16*l*h^5 + 3*l^2*h^2 + 14*l^2*h^3 + 26*l^2*h^4 + 3*l^2*h^5 := by
  rw [leafPart,table2211]
  simp only [weighted,eval,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  ring

private theorem part2212 (l h : ℕ) : part (fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 2 (Fin.cons 1 (Fin.cons 2 c)))))) l h = 0 := by
  have forbid (c : Fin 7 → Tag) : ¬ allowed ((fun c : Fin 7 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 2 (Fin.cons 1 (Fin.cons 2 c)))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : 2 < (0 + (0 + (1 + (0 + (if c 0 ≠ 2 then 1 else 0 : ℕ))))) := fast.1.2
    have b0 : (if c 0 ≠ 2 then 1 else 0 : ℕ) ≤ 1 := by split <;> decide
    omega
  simp [part,forbid]

private theorem part221 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 2 (Fin.cons 1 c))))) l h =
    h^2 + 6*h^3 + 15*h^4 + 4*h^5 + 8*l*h^2 + 42*l*h^3 + 90*l*h^4 + 20*l*h^5 + 6*l^2*h^2 + 29*l^2*h^3 + 56*l^2*h^4 + 9*l^2*h^5 := by
  rw [splitPart,part2210,part2211,part2212]
  ring

private theorem part222 (l h : ℕ) : part (fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 2 (Fin.cons 2 c))))) l h = 0 := by
  have forbid (c : Fin 8 → Tag) : ¬ allowed ((fun c : Fin 8 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 2 (Fin.cons 2 c))))) c) := by
    intro hc
    have fast := (fastAllowed_iff _).mp hc
    have hw : 2 < (0 + (0 + (0 + ((if c 0 ≠ 2 then 1 else 0 : ℕ) + (if c 1 ≠ 2 then 1 else 0 : ℕ))))) := fast.1.2
    have b0 : (if c 0 ≠ 2 then 1 else 0 : ℕ) ≤ 1 := by split <;> decide
    have b1 : (if c 1 ≠ 2 then 1 else 0 : ℕ) ≤ 1 := by split <;> decide
    omega
  simp [part,forbid]

private theorem part22 (l h : ℕ) : part (fun c : Fin 9 → Tag => (show Fin 11 → Tag from (Fin.cons 2 (Fin.cons 2 c)))) l h =
    h^2 + 6*h^3 + 15*h^4 + 4*h^5 + 9*l*h^2 + 48*l*h^3 + 105*l*h^4 + 24*l*h^5 + 10*l^2*h^2 + 49*l^2*h^3 + 96*l^2*h^4 + 18*l^2*h^5 := by
  rw [splitPart,part220,part221,part222]
  ring

private theorem part2 (l h : ℕ) : part (fun c : Fin 10 → Tag => (show Fin 11 → Tag from (Fin.cons 2 c))) l h =
    h + 10*h^2 + 39*h^3 + 54*h^4 + 10*h^5 + 10*l*h + 90*l*h^2 + 312*l*h^3 + 378*l*h^4 + 60*l*h^5 + 15*l^2*h + 120*l^2*h^2 + 372*l^2*h^3 + 380*l^2*h^4 + 50*l^2*h^5 := by
  rw [splitPart,part20,part21,part22]
  ring

private theorem partAll (l h : ℕ) : part (fun c : Fin 11 → Tag => (show Fin 11 → Tag from c)) l h =
    1 + 11*h + 55*h^2 + 119*h^3 + 104*h^4 + 10*h^5 + 11*l + 110*l*h + 495*l*h^2 + 952*l*h^3 + 728*l*h^4 + 60*l*h^5 + 21*l^2 + 189*l^2*h + 756*l^2*h^2 + 1254*l^2*h^3 + 789*l^2*h^4 + 50*l^2*h^5 + l^3 + 8*l^3*h + 28*l^3*h^2 + 40*l^3*h^3 + 20*l^3*h^4 := by
  rw [splitPart,part0,part1,part2]
  ring

end

private def expression (l h : ℕ) : ℕ :=
  50*h^5*l^2 + 60*h^5*l + 10*h^5 + 20*h^4*l^3 + 789*h^4*l^2 + 728*h^4*l + 104*h^4 + 40*h^3*l^3 + 1254*h^3*l^2 + 952*h^3*l + 119*h^3 + 28*h^2*l^3 + 756*h^2*l^2 + 495*h^2*l + 55*h^2 + 8*h*l^3 + 189*h*l^2 + 110*h*l + 11*h + l^3 + 21*l^2 + 11*l + 1

private theorem totalValue (l h : ℕ) : total l h = expression l h := by
  rw [rootPart]
  exact (partAll l h).trans (by unfold expression; ring)

private def H (n t : ℚ) : ℚ :=
  (t*(n*(n*(n*(n*(-4900*n - 64470) - 177520) - 165396) - 36576) + t*(n*(n*(n*(n*(2100*n + 15540) + 175560) + 408310) + 287280) + t*(n*(n*(n*(n*(7000*n + 116760) + 369040) + 243180) - 152460) + t*(n*(n*(n*(-24150*n - 352380) - 853370) - 557760) + t*(n*(n*(35280*n + 416976) + 681156) + t*(n*(-26600*n - 227220) + t*(10200*n - 1575*t + 47640) - 187600) + 242970) - 44485) - 106470) + 43610) + 6330))/420

private def P (n : ℚ) : ℚ :=
  (n*(n*(n*(n*(n*(n*(n*(155*n + 3876) + 19866) + 39480) + 33845) + 15834) + 15854) + 10950) + 420)/420

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

private theorem recurrence (n : ℕ) (hn : 10 ≤ n) :
    (a n : ℚ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  obtain ⟨m,rfl⟩ : ∃ m, n=m+10 := ⟨n-10,by omega⟩
  simp only [show m+10-1 = m+9 by omega,show m+10-2 = m+8 by omega,show m+10-3 = m+7 by omega,show m+10-4 = m+6 by omega,show m+10-5 = m+5 by omega,show m+10-6 = m+4 by omega,show m+10-7 = m+3 by omega,show m+10-8 = m+2 by omega,show m+10-9 = m+1 by omega,value,P]
  push_cast
  ring

private theorem generating :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 9 : PowerSeries ℚ) = X * (334 + 6100 * X + 17962 * X ^ 2 - 2133 * X ^ 3 - 6817 * X ^ 4 - 614 * X ^ 5 + 56 * X ^ 6 - 9 * X ^ 7 + X ^ 8) := by
  let S := mk (fun n => if n < 1 then 0 else (a n : ℚ))
  change S * _ = _
  have lhs : S*(1-X)^9 = S - (9:ℕ) • (S*X^1) + (36:ℕ) • (S*X^2) - (84:ℕ) • (S*X^3) + (126:ℕ) • (S*X^4) - (126:ℕ) • (S*X^5) + (84:ℕ) • (S*X^6) - (36:ℕ) • (S*X^7) + (9:ℕ) • (S*X^8) - (S*X^9) := by simp only [nsmul_eq_mul]; ring
  have rhs : (X * (334 + 6100 * X + 17962 * X ^ 2 - 2133 * X ^ 3 - 6817 * X ^ 4 - 614 * X ^ 5 + 56 * X ^ 6 - 9 * X ^ 7 + X ^ 8) : PowerSeries ℚ) = (334:ℕ) • X^1 + (6100:ℕ) • X^2 + (17962:ℕ) • X^3 - (2133:ℕ) • X^4 - (6817:ℕ) • X^5 - (614:ℕ) • X^6 + (56:ℕ) • X^7 - (9:ℕ) • X^8 + X^9 := by simp only [nsmul_eq_mul]; ring
  rw [lhs,rhs]
  ext n
  simp only [map_add,map_sub,map_nsmul,coeff_mul_X_pow',coeff_X_pow,S,coeff_mk]
  by_cases h : 10 ≤ n
  · have recn := recurrence n h
    simp only [nsmul_eq_mul,if_pos (show 1 ≤ n by omega),
      if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega),
      if_pos (show 4 ≤ n by omega),
      if_pos (show 5 ≤ n by omega),
      if_pos (show 6 ≤ n by omega),
      if_pos (show 7 ≤ n by omega),
      if_pos (show 8 ≤ n by omega),
      if_pos (show 9 ≤ n by omega),
      if_neg (show ¬ n < 1 by omega),
      if_neg (show ¬ n-1 < 1 by omega),
      if_neg (show ¬ n-2 < 1 by omega),
      if_neg (show ¬ n-3 < 1 by omega),
      if_neg (show ¬ n-4 < 1 by omega),
      if_neg (show ¬ n-5 < 1 by omega),
      if_neg (show ¬ n-6 < 1 by omega),
      if_neg (show ¬ n-7 < 1 by omega),
      if_neg (show ¬ n-8 < 1 by omega),
      if_neg (show ¬ n-9 < 1 by omega),
      if_neg (show n ≠ 1 by omega),
      if_neg (show n ≠ 2 by omega),
      if_neg (show n ≠ 3 by omega),
      if_neg (show n ≠ 4 by omega),
      if_neg (show n ≠ 5 by omega),
      if_neg (show n ≠ 6 by omega),
      if_neg (show n ≠ 7 by omega),
      if_neg (show n ≠ 8 by omega),
      if_neg (show n ≠ 9 by omega)]
    norm_num
    linarith
  · interval_cases n <;> norm_num [value,P]

theorem result : type_of% @OMA.S_oeis_a254705.main := ⟨generating,recurrence⟩

end OMA.Ties254705

theorem OMA.solution : type_of% @OMA.S_oeis_a254705.main := OMA.Ties254705.result
