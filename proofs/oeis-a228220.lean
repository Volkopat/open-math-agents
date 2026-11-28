import OMAStatements.S_oeis_a228220
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-! R. H. Hardin's second-difference arrays and Colin Barker's formulas.
Two rows have the same second differences exactly when their difference is affine.
We normalize the minimum to zero, and count one representative per feasible slope
by deleting those with an immediate predecessor. -/

namespace OMA.SecondDiff
open Finset

private abbrev Row (d : ℕ) := Fin (d+2) → ℤ
private def diff {d : ℕ} (w : Row d) (i : Fin d) :=
  w ⟨i.val,by omega⟩ - 2*w ⟨i.val+1,by omega⟩ + w ⟨i.val+2,by omega⟩
private def slope {d : ℕ} (w : Row d) := w 1 - w 0
private def moved {d : ℕ} (w : Row d) (t c : ℤ) : Row d := fun i => w i + t*i.val+c

private theorem slope_moved {d : ℕ} (w : Row d) (t c : ℤ) :
    slope (moved w t c) = slope w + t := by
  change (w 1 + t*1+c) - (w 0 + t*0+c) = _
  unfold slope; ring

private theorem diff_moved {d : ℕ} (w : Row d) (t c : ℤ) : diff (moved w t c) = diff w := by
  funext i; simp [diff,moved]; ring

private theorem affine {d : ℕ} {w v : Row d} (h : diff v = diff w) :
    v = moved w (slope v - slope w) (v 0-w 0) := by
  have aux (k : ℕ) (hk : k < d+2) : v ⟨k,hk⟩ =
      w ⟨k,hk⟩ + (slope v-slope w)*(k:ℤ) + (v 0-w 0) := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      match k, hk with
      | 0, _ => simp
      | 1, _ =>
        change v 1 = w 1 + (slope v-slope w)*(1:ℤ)+(v 0-w 0)
        simp [slope]; ring
      | j+2, hj =>
        have h0 := ih j (by omega) (by omega)
        have h1 := ih (j+1) (by omega) (by omega)
        have he := congrFun h ⟨j,by omega⟩
        simp only [diff] at he
        push_cast at h1 ⊢
        linarith
  funext i; exact aux i i.isLt

private def cube (d n : ℕ) (lo : ℤ) : Finset (Row d) :=
  Fintype.piFinset fun _ => Icc lo (n:ℤ)
private def norm (d n : ℕ) := cube d n 0 \ cube d n 1
private theorem mem_cube {d n lo} {w : Row d} : w ∈ cube d n lo ↔
    ∀ i, lo ≤ w i ∧ w i ≤ n := by simp [cube,Fintype.mem_piFinset]
private theorem mem_norm {d n} {w : Row d} : w ∈ norm d n ↔
    (∀ i, 0 ≤ w i ∧ w i ≤ n) ∧ ∃ i, w i = 0 := by
  simp only [norm,mem_sdiff,mem_cube]
  constructor
  · rintro ⟨hw,h⟩; refine ⟨hw,?_⟩
    by_contra! hn; apply h; intro i; have := hw i; have := hn i; omega
  · rintro ⟨hw,i,hi⟩; exact ⟨hw,fun h => by have := h i; omega⟩

private theorem moved_zero_unique {d n} {x : Row d} {t c e : ℤ}
    (h : moved x t c ∈ norm d n) (h' : moved x t e ∈ norm d n) : c=e := by
  obtain ⟨hw,i,hi⟩ := mem_norm.mp h
  obtain ⟨hv,j,hj⟩ := mem_norm.mp h'
  have h1 := (hv i).1; have h2 := (hw j).1
  simp only [moved] at *; omega

private theorem normalized {d n : ℕ} {w : Row d} (h : ∀ i j, w i - w j ≤ (n:ℤ)) :
    ∃ c : ℤ, moved w 0 c ∈ norm d n := by
  obtain ⟨j,_,hj⟩ := univ.exists_min_image w univ_nonempty
  refine ⟨-w j, mem_norm.mpr ⟨?_, j, by simp [moved]⟩⟩
  intro i; have := h i j; have := hj i (mem_univ _); simp [moved]; omega

private def rect (d n : ℕ) (b lo yl : ℤ) : Finset (Row d) :=
  Fintype.piFinset fun i => Icc (max lo ((i.val:ℤ)-b+yl)) (min (n:ℤ) (n+i.val-b))
private def edge (d n : ℕ) (b : Fin (d+2)) :=
  rect d n b.val 0 0 \ (rect d n b.val 1 0 ∪ rect d n b.val 0 1)
private theorem mem_rect {d n b lo yl} {w : Row d} : w ∈ rect d n b lo yl ↔
    (∀ i, lo ≤ w i ∧ w i ≤ n) ∧ (∀ i, yl ≤ moved w (-1) b i ∧ moved w (-1) b i ≤ n) := by
  simp only [rect,Fintype.mem_piFinset,mem_Icc, max_le_iff,le_min_iff,moved,neg_one_mul]
  constructor
  · intro h; constructor <;> intro i <;> have := h i <;> omega
  · rintro ⟨h,g⟩ i; have := h i; have := g i; omega
private theorem mem_edge {d n b} {w : Row d} : w ∈ edge d n b ↔
    w ∈ norm d n ∧ moved w (-1) b.val ∈ norm d n := by
  simp only [edge,mem_sdiff,mem_union,mem_rect,norm,mem_sdiff,mem_cube]; tauto

private def edges (d n : ℕ) := univ.biUnion (edge d n)
private theorem mem_edges {d n} {w : Row d} : w ∈ edges d n ↔
    ∃ b : Fin (d+2), w ∈ edge d n b := by simp [edges]
private theorem prev {d n} {w v : Row d} (hw : w ∈ norm d n) (hv : v ∈ norm d n)
    (h : diff v = diff w) (hl : slope v < slope w) : w ∈ edges d n := by
  let f : Row d := fun i => w i - (i.val:ℤ)
  have he := affine h
  have span (i j : Fin (d+2)) : f i - f j ≤ n := by
    obtain ⟨bw,_⟩ := mem_norm.mp hw; obtain ⟨bv,_⟩ := mem_norm.mp hv
    have hwi := bw i; have hwj := bw j; have hvi := bv i; have hvj := bv j
    have ei := congrFun he i; have ej := congrFun he j
    dsimp only [f,moved] at *
    by_cases hij : (j.val:ℤ) ≤ i.val
    · omega
    · have hmul := mul_nonneg (show 0 ≤ slope w - slope v-1 by omega)
          (show 0 ≤ (j.val:ℤ)-i.val by omega)
      nlinarith
  obtain ⟨c,hc⟩ := normalized span
  have eq : moved f 0 c = moved w (-1) c := by funext i; simp [f,moved,sub_eq_add_neg]
  rw [eq] at hc
  obtain ⟨cw,j,hj⟩ := mem_norm.mp hw; obtain ⟨cv,i,hi⟩ := mem_norm.mp hc
  have hj' := (cv j).1; have hi' := (cw i).1; have hib := i.isLt
  simp only [moved,neg_one_mul] at hj' hi
  have h0 : 0 ≤ c := by omega
  have hm : c.toNat < d+2 := by omega
  exact mem_edges.mpr ⟨⟨c.toNat,hm⟩, mem_edge.mpr ⟨hw,by simpa [Int.toNat_of_nonneg h0] using hc⟩⟩

private def good (d n : ℕ) := norm d n \ edges d n
private theorem card_diff (d n : ℕ) : ((cube d n 0).image diff).card = (good d n).card := by
  classical
  have rep {w : Row d} (hw : w ∈ cube d n 0) : ∃ v ∈ good d n, diff v = diff w := by
    have bound := mem_cube.mp hw
    obtain ⟨c,hc⟩ := normalized (w:=w) (n:=n) (fun i j => by have := bound i; have := bound j; omega)
    let s := (norm d n).filter (fun v => diff v = diff w)
    have hs : s.Nonempty := ⟨moved w 0 c,mem_filter.mpr ⟨hc,diff_moved ..⟩⟩
    obtain ⟨v,hv,hmin⟩ := s.exists_min_image slope hs
    obtain ⟨hn,he⟩ := mem_filter.mp hv
    refine ⟨v,mem_sdiff.mpr ⟨hn,?_⟩,he⟩
    intro bad; obtain ⟨b,hb⟩ := mem_edges.mp bad
    have hp : moved v (-1) b.val ∈ s := mem_filter.mpr ⟨(mem_edge.mp hb).2,(diff_moved ..).trans he⟩
    have := hmin _ hp; rw [slope_moved] at this; omega
  have eq : (cube d n 0).image diff = (good d n).image diff := by
    ext y; simp only [mem_image]; constructor
    · rintro ⟨w,hw,rfl⟩; exact rep hw
    · rintro ⟨w,hw,rfl⟩; exact ⟨w,(mem_sdiff.mp (mem_sdiff.mp hw).1).1,rfl⟩
  rw [eq]; apply card_image_of_injOn
  intro w hw v hv h
  obtain ⟨wn,wb⟩ := mem_sdiff.mp hw; obtain ⟨vn,vb⟩ := mem_sdiff.mp hv
  rcases lt_trichotomy (slope w) (slope v) with lt | eq | gt
  · exact False.elim (vb (prev vn wn h lt))
  · have e := affine h
    rw [eq,sub_self] at e
    have eid : moved v 0 0 = v := by funext i; simp [moved]
    have h0 : moved v 0 0 ∈ norm d n := eid.symm ▸ vn
    have hc := moved_zero_unique (e ▸ wn) h0
    simpa only [hc,eid] using e
  · exact False.elim (wb (prev wn vn h.symm gt))

private theorem rect_le {d n b l t l' t'} (hl : l ≤ l') (ht : t ≤ t') :
    rect d n b l' t' ⊆ rect d n b l t := by
  intro x hx; obtain ⟨h1,h2⟩ := mem_rect.mp hx
  exact mem_rect.mpr ⟨fun i => ⟨hl.trans (h1 i).1,(h1 i).2⟩,fun i => ⟨ht.trans (h2 i).1,(h2 i).2⟩⟩
private theorem card_edge (d n : ℕ) (b : Fin (d+2)) :
    ((edge d n b).card : ℤ) = (rect d n b.val 0 0).card - (rect d n b.val 1 0).card
      - (rect d n b.val 0 1).card + (rect d n b.val 1 1).card := by
  have h : rect d n b.val 1 0 ∩ rect d n b.val 0 1 = rect d n b.val 1 1 := by
    ext x; simp only [mem_inter,mem_rect]; constructor
    · rintro ⟨⟨a,_⟩,⟨_,c⟩⟩; exact ⟨a,c⟩
    · intro hx; exact ⟨mem_rect.mp (rect_le (by decide : (1:ℤ) ≤ 1) (by decide : (0:ℤ) ≤ 1) (mem_rect.mpr hx)),
          mem_rect.mp (rect_le (by decide : (0:ℤ) ≤ 1) (by decide : (1:ℤ) ≤ 1) (mem_rect.mpr hx))⟩
  have hcard := card_union_add_card_inter (rect d n b.val 1 0) (rect d n b.val 0 1)
  rw [h] at hcard
  have sub : rect d n b.val 1 0 ∪ rect d n b.val 0 1 ⊆ rect d n b.val 0 0 :=
    union_subset (rect_le (by decide) (by decide)) (rect_le (by decide) (by decide))
  have hd := card_sdiff_add_card_eq_card sub
  change ((rect d n b.val 0 0 \ _).card : ℤ) = _; omega

private def boxCount (d n : ℕ) (b : Fin (d+2)) (l t : ℤ) : ℤ :=
  ∏ i : Fin (d+2), (((min (n:ℤ) (n+i.val-b.val) + 1 - max l ((i.val:ℤ)-b.val+t)).toNat : ℕ) : ℤ)
private theorem count_rect (d n : ℕ) (b : Fin (d+2)) (l t : ℤ) :
    ((rect d n b.val l t).card : ℤ) = boxCount d n b l t := by
  simp [rect,boxCount,Fintype.card_piFinset,Int.card_Icc,sub_add_comm,Nat.cast_prod]
private theorem count (d n : ℕ) : (((cube d n 0).image diff).card : ℤ) =
    ((n:ℤ)+1)^(d+2) - (n:ℤ)^(d+2) - ∑ b : Fin (d+2),
      (boxCount d n b 0 0 - boxCount d n b 1 0 - boxCount d n b 0 1 + boxCount d n b 1 1) := by
  classical
  have hn : cube d n 1 ⊆ cube d n 0 := by
    intro x hx; exact mem_cube.mpr (fun i => ⟨by have := (mem_cube.mp hx i).1; omega,(mem_cube.mp hx i).2⟩)
  have he : edges d n ⊆ norm d n := by
    intro x hx; obtain ⟨b,hb⟩ := mem_edges.mp hx; exact (mem_edge.mp hb).1
  have hdis : ((univ : Finset (Fin (d+2))) : Set (Fin (d+2))).PairwiseDisjoint (edge d n) := by
    intro i _ j _ hij; apply Finset.disjoint_left.mpr; intro x hx hy
    have e := moved_zero_unique (mem_edge.mp hx).2 (mem_edge.mp hy).2
    exact hij (Fin.ext (by exact_mod_cast e))
  have hed : ((edges d n).card : ℤ) = ∑ b : Fin (d+2),
      (boxCount d n b 0 0 - boxCount d n b 1 0 - boxCount d n b 0 1 + boxCount d n b 1 1) := by
    rw [edges,card_biUnion hdis,Nat.cast_sum]; apply sum_congr rfl
    intro b _; rw [card_edge]; simp only [count_rect]
  have c0 : ((cube d n 0).card : ℤ) = ((n:ℤ)+1)^(d+2) := by simp [cube,Fintype.card_piFinset,Int.card_Icc]
  have c1 : ((cube d n 1).card : ℤ) = (n:ℤ)^(d+2) := by simp [cube,Fintype.card_piFinset,Int.card_Icc]
  have hs := card_sdiff_add_card_eq_card hn; have ht := card_sdiff_add_card_eq_card he
  change (norm d n).card + _ = _ at hs; change (good d n).card + _ = _ at ht
  rw [card_diff]; omega

private def liftRow {d n : ℕ} (w : Fin (d+2) → Fin (n+1)) : Row d := fun i => (w i).val
private theorem lift_univ (d n : ℕ) :
    (univ : Finset (Fin (d+2) → Fin (n+1))).image liftRow = cube d n 0 := by
  ext x; constructor
  · intro h; obtain ⟨w,_,rfl⟩ := mem_image.mp h
    exact mem_cube.mpr (fun i => ⟨by simp [liftRow], by have := (w i).isLt; simp [liftRow]; omega⟩)
  · intro h; have hc := mem_cube.mp h
    let w (i : Fin (d+2)) : Fin (n+1) := ⟨(x i).toNat,by have := hc i; omega⟩
    exact mem_image.mpr ⟨w,mem_univ _,by funext i; simpa [liftRow,w] using Int.toNat_of_nonneg (hc i).1⟩

private theorem box_large {d n : ℕ} (hn : d+2 ≤ n) (b : Fin (d+2)) (l t : ℤ)
    (hl : 0 ≤ l ∧ l ≤ 1) (ht : 0 ≤ t ∧ t ≤ 1) :
    boxCount d n b l t = ∏ i : Fin (d+2), ((n:ℤ)+1 + min 0 ((i.val:ℤ)-b.val)
          - max l ((i.val:ℤ)-b.val+t)) := by
  unfold boxCount; apply prod_congr rfl; intro i _
  have hi := i.isLt; have hb := b.isLt
  have hp : 0 ≤ min (n:ℤ) (n+i.val-b.val)+1-max l ((i.val:ℤ)-b.val+t) := by
    simp only [min_def,max_def]; split_ifs <;> omega
  rw [Int.toNat_of_nonneg hp]
  simp only [min_def]; split_ifs <;> omega

open OMA.S_oeis_a228220 PowerSeries

private def polynomial (z : ℤ) : ℤ := (1)*z^0 + (1)*z^1 + (9)*z^2 + (20)*z^3

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem a_eq (n : ℕ) : (a n : ℤ) = polynomial n := by
  have bridge : a n = ((cube 3 n 0).image diff).card := by
    rw [← lift_univ, Finset.image_image]
    rfl
  rw [bridge,count]
  by_cases hn : 5 ≤ n
  · simp only [box_large (d:=3) hn _ 0 0 (by decide) (by decide), box_large (d:=3) hn _ 1 0 (by decide) (by decide), box_large (d:=3) hn _ 0 1 (by decide) (by decide), box_large (d:=3) hn _ 1 1 (by decide) (by decide)]
    norm_num [Fin.sum_univ_succ,Fin.prod_univ_succ,polynomial]
    ring
  · interval_cases n <;> decide

private theorem a_poly (n : ℕ) : (a n : ℚ) = (1)*(n:ℚ)^0 + (1)*(n:ℚ)^1 + (9)*(n:ℚ)^2 + (20)*(n:ℚ)^3 := by
  have h := a_eq n
  unfold polynomial at h
  exact_mod_cast h

private theorem recurrence : ∀ n : ℕ, 4 < n → (a n : ℚ) = 4*(a (n-1):ℚ) - 6*(a (n-2):ℚ) + 4*(a (n-3):ℚ) - (a (n-4):ℚ) := by
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k, n=k+5 := ⟨n-5,by omega⟩
  simp only [show k+5-1=k+4 by omega,show k+5-2=k+3 by omega,show k+5-3=k+2 by omega,show k+5-4=k+1 by omega, a_poly]
  push_cast
  ring

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem generating_function : ordinary * (1-X)^4 = X*(31 + 75*X + 15*X^2 - X^3) := by
  have e1 : ordinary * (1-X)^4 = ordinary  - C (4 : ℚ) * (ordinary * X^1)  + C (6 : ℚ) * (ordinary * X^2)  - C (4 : ℚ) * (ordinary * X^3)  + C (1 : ℚ) * (ordinary * X^4) := by simp only [map_ofNat,map_one]; ring
  have e2 : (X*(31 + 75*X + 15*X^2 - X^3) : ℚ⟦X⟧) = X^1 * C (31 : ℚ)  + X^2 * C (75 : ℚ)  + X^3 * C (15 : ℚ)  - X^4 * C (1 : ℚ) := by simp only [map_ofNat,map_one]; ring
  rw [e1,e2]
  ext n
  simp only [map_sub,map_add,coeff_mul_C,coeff_C_mul,coeff_mul_X_pow',coeff_X_pow,ordinary,coeff_mk]
  by_cases hn : n ≤ 4
  · interval_cases n <;> simp only [Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, le_refl, if_true, if_false, a_poly] <;> norm_num
  · simp only [show ¬ (n=0) by omega, show ¬ (n=1) by omega, show ¬ (n=2) by omega, show ¬ (n=3) by omega, show ¬ (n=4) by omega, show 1 ≤ n by omega, show ¬ (n-1=0) by omega, show 2 ≤ n by omega, show ¬ (n-2=0) by omega, show 3 ≤ n by omega, show ¬ (n-3=0) by omega, show 4 ≤ n by omega, show ¬ (n-4=0) by omega,if_true,if_false]
    linarith [recurrence n (by omega)]

private theorem result : type_of% @OMA.S_oeis_a228220.main := ⟨generating_function,recurrence⟩
end OMA.SecondDiff

theorem OMA.solution : type_of% @OMA.S_oeis_a228220.main := OMA.SecondDiff.result
