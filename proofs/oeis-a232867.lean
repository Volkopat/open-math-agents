import OMAStatements.S_oeis_a232867

/-! The list is built one distance layer at a time. The distance is the
Manhattan distance plus the number of quarter-turns needed for the quadrant. -/

namespace A232867Proof

open OMA.S_oeis_a232867

private def pt (x y : ℤ) : GaussianInt := ⟨x, y⟩

private theorem pt_add_one (x y : ℤ) : pt x y + 1 = pt (x+1) y := by
  apply Zsqrtd.ext <;> simp [pt, Zsqrtd.re_add, Zsqrtd.im_add]

private theorem rotate (x y : ℤ) : iu * pt x y = pt (-y) x := by
  apply Zsqrtd.ext <;> simp [iu, pt, Zsqrtd.re_mul, Zsqrtd.im_mul]

private theorem pt_eq {a b c d : ℤ} : pt a b = pt c d ↔ a=c ∧ b=d := by
  constructor
  · intro h
    exact ⟨congrArg Zsqrtd.re h, congrArg Zsqrtd.im h⟩
  · rintro ⟨rfl,rfl⟩
    rfl

private def distance (z : GaussianInt) : ℤ :=
  if z.im < 0 then 3 + |z.re| - z.im
  else if z.re < 0 then 2 - z.re + z.im
  else if z.im = 0 then z.re
  else 1 + z.re + z.im

private theorem lower (z : GaussianInt) : 0 ≤ distance z := by
  simp only [distance]
  split_ifs <;> try omega
  have := abs_nonneg z.re
  omega

private theorem zero_iff (z : GaussianInt) : distance z = 0 ↔ z = 0 := by
  obtain ⟨x,y⟩ := z
  change distance (pt x y) = 0 ↔ pt x y = pt 0 0
  simp only [distance, pt, Zsqrtd.mk.injEq]
  split_ifs <;> try omega
  have := abs_nonneg x
  omega

private theorem step_add_bound (z : GaussianInt) : distance (z + 1) ≤ distance z + 1 := by
  obtain ⟨x,y⟩ := z
  change distance (pt x y + 1) ≤ distance (pt x y) + 1
  rw [pt_add_one]
  simp only [distance, pt]
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, abs_of_nonneg (by omega : 0 ≤ x + 1)]
    split_ifs <;> omega
  · rw [abs_of_nonpos (by omega : x ≤ 0), abs_of_nonpos (by omega : x+1 ≤ 0)]
    split_ifs <;> omega

private theorem step_rotate_bound (z : GaussianInt) : distance (iu * z) ≤ distance z + 1 := by
  obtain ⟨x,y⟩ := z
  change distance (iu * pt x y) ≤ distance (pt x y) + 1
  rw [rotate]
  simp only [distance, pt, abs_neg]
  rcases le_or_gt 0 x with hx|hx <;> rcases le_or_gt 0 y with hy|hy
  all_goals (
    simp only [abs_of_nonneg, abs_of_nonpos, hx, hy, le_of_lt]
    try rw [abs_of_nonpos hx.le]
    try rw [abs_of_nonpos hy.le]
    split_ifs <;> omega)

private theorem predecessor (z : GaussianInt) (hz : 0 < distance z) :
    ∃ w, distance w + 1 = distance z ∧ (w + 1 = z ∨ iu*w = z) := by
  obtain ⟨x,y⟩ := z
  change 0 < distance (pt x y) at hz
  change ∃ w, distance w + 1 = distance (pt x y) ∧
    (w + 1 = pt x y ∨ iu*w = pt x y)
  have addCase (hp : 0 < x) :
      ∃ w, distance w+1 = distance (pt x y) ∧ (w+1=pt x y ∨ iu*w=pt x y) := by
    refine ⟨pt (x-1) y, ?_, Or.inl ?_⟩
    · simp only [distance, pt, abs_of_nonneg (by omega : 0 ≤ x-1), abs_of_nonneg hp.le]
      split_ifs <;> omega
    · rw [pt_add_one, pt_eq]
      omega
  by_cases hp : 0 < x
  · exact addCase hp
  have hnot : x ≠ 0 ∨ y ≠ 0 := by
    by_contra! hc
    have h0 : distance (pt x y) = 0 := (zero_iff _).2 (by rw [hc.1,hc.2];rfl)
    omega
  refine ⟨pt y (-x), ?_, Or.inr ?_⟩
  · simp only [distance, pt, abs_of_nonpos (show x ≤ 0 by omega)]
    by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy]
      split_ifs <;> omega
    · rw [abs_of_nonpos (by omega : y ≤ 0)]
      split_ifs <;> omega
  · rw [rotate, pt_eq]
    omega

private theorem mem_lst (n : ℕ) (z : GaussianInt) : z ∈ Lst n ↔ distance z ≤ n := by
  induction n generalizing z with
  | zero =>
    rw [Lst, List.mem_singleton, Nat.cast_zero, ← zero_iff]
    exact ⟨le_of_eq, fun h => le_antisymm h (lower z)⟩
  | succ n ih =>
    simp only [Lst, step, List.mem_eraseDups, List.mem_flatMap,
      List.mem_cons, List.not_mem_nil, or_false, Nat.cast_succ]
    constructor
    · rintro ⟨w,hw,hzw | hzw | hzw⟩ <;> subst z
      · linarith [(ih w).1 hw]
      · linarith [(ih w).1 hw, step_add_bound w]
      · linarith [(ih w).1 hw, step_rotate_bound w]
    · intro hz
      by_cases h : distance z ≤ n
      · exact ⟨z, (ih z).2 h, Or.inl rfl⟩
      have hp : 0 < distance z := by omega
      obtain ⟨w, hw, hs | hs⟩ := predecessor z hp
      · exact ⟨w, (ih w).2 (by omega), Or.inr (Or.inl hs.symm)⟩
      · exact ⟨w, (ih w).2 (by omega), Or.inr (Or.inr hs.symm)⟩


private theorem eraseDups_of_nodup {α : Type} [BEq α] [LawfulBEq α]
    (l : List α) (h : l.Nodup) : l.eraseDups = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨hn, hl⟩ := List.nodup_cons.mp h
    rw [List.eraseDups_cons, List.filter_eq_self.mpr _, ih hl]
    intro b hb
    simp only [Bool.not_eq_true', beq_eq_false_iff_ne]
    intro he
    subst b
    exact hn hb

private theorem nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] (l : List α) :
    l.eraseDups.Nodup := by
  match l with
  | [] => simp
  | a :: l =>
    rw [List.eraseDups_cons, List.nodup_cons]
    constructor
    · simp [List.mem_filter]
    · exact nodup_eraseDups _
termination_by l.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

private def fourPoints (t : ℕ) : List GaussianInt :=
  [pt (t+1) 0, pt 0 t, pt 1 ((t:ℤ)-1), pt (1-(t:ℤ)) 0]

private theorem four_nodup (t : ℕ) (ht : 2 ≤ t) : (fourPoints t).Nodup := by
  have ht' : (2:ℤ) ≤ t := by exact_mod_cast ht
  simp only [fourPoints, List.nodup_cons, List.nodup_nil, and_true,
    List.mem_cons, List.not_mem_nil, or_false, pt_eq, not_false_eq_true]
  simp only [not_or, not_and]
  omega

private theorem frontier_step (t : ℕ) (ht : 2 ≤ t)
    (hpre : ∃ s, Lst t = Lst (t-1) ++ pt t 0 :: pt 0 ((t:ℤ)-1) :: s) :
    ∃ s, Lst (t+1) = Lst t ++ fourPoints t ++ s := by
  obtain ⟨s, hs⟩ := hpre
  let neighbors := fun x : GaussianInt => [x,x+1,iu*x]
  let raw := (Lst (t-1)).flatMap neighbors
  have hraw : raw.eraseDups = Lst t := by
    change step (Lst (t-1)) = Lst t
    rw [← Lst, show (t-1).succ = t by omega]
  have hmem (z : GaussianInt) : raw.contains z = true ↔ distance z ≤ t := by
    rw [List.contains_iff_mem, ← List.mem_eraseDups, hraw, mem_lst]
  have ht' : (2:ℤ) ≤ t := by exact_mod_cast ht
  have holdA : raw.contains (pt t 0) = true := (hmem _).2 (by simp [distance, pt]; omega)
  have holdB : raw.contains (pt 0 ((t:ℤ)-1)) = true := (hmem _).2 (by simp [distance, pt]; omega)
  have hnew (z : GaussianInt) (hz : (t:ℤ) < distance z) : raw.contains z = false := by
    cases h : raw.contains z
    · rfl
    · exact False.elim (not_le_of_gt hz ((hmem z).1 h))
  have h0 := hnew (pt ((t:ℤ)+1) 0) (by simp [distance, pt]; omega)
  have h1 := hnew (pt 0 t) (by simp [distance, pt]; omega)
  have h2 := hnew (pt 1 ((t:ℤ)-1)) (by simp [distance, pt]; omega)
  have h3 := hnew (pt (1-(t:ℤ)) 0) (by simp [distance, pt]; omega)
  have hseg :
      (pt t 0 :: pt 0 ((t:ℤ)-1) :: s).flatMap neighbors =
      [pt t 0, pt ((t:ℤ)+1) 0, pt 0 t, pt 0 ((t:ℤ)-1),
        pt 1 ((t:ℤ)-1), pt (1-(t:ℤ)) 0] ++ s.flatMap neighbors := by
    simp [neighbors, pt_add_one, rotate, neg_sub]
  have hrm :
      ((pt t 0 :: pt 0 ((t:ℤ)-1) :: s).flatMap neighbors).removeAll raw =
        fourPoints t ++ (s.flatMap neighbors).removeAll raw := by
    rw [hseg]
    simp only [fourPoints, List.removeAll, List.cons_append, List.nil_append,
      List.filter_cons, h0,h1,h2,h3,holdA,holdB, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, if_false, if_true]
  let suffix := ((s.flatMap neighbors).removeAll raw).removeAll (fourPoints t)
  refine ⟨suffix.eraseDups, ?_⟩
  calc
    Lst (t+1) = (raw ++ (pt t 0 :: pt 0 ((t:ℤ)-1) :: s).flatMap neighbors).eraseDups := by
      change ((Lst t).flatMap neighbors).eraseDups = _
      rw [hs, List.flatMap_append]
    _ = Lst t ++ (fourPoints t ++ (s.flatMap neighbors).removeAll raw).eraseDups := by
      rw [List.eraseDups_append, hraw, hrm]
    _ = _ := by
      rw [List.eraseDups_append, eraseDups_of_nodup _ (four_nodup t ht), List.append_assoc]

private theorem frontier (t : ℕ) (ht : 2 ≤ t) :
    ∃ s, Lst (t+1) = Lst t ++ fourPoints t ++ s := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le ht
  induction m with
  | zero =>
    exact ⟨[], by decide⟩
  | succ m ih =>
    obtain ⟨s,hs⟩ := ih (by omega)
    apply frontier_step _ (by omega)
    refine ⟨pt 1 ((2+(m:ℤ))-1) :: pt (1-(2+(m:ℤ))) 0 :: s, ?_⟩
    simpa [fourPoints, Nat.cast_add, Nat.cast_succ, show 2 + (m+1) - 1 = 2+m by omega,
      add_assoc, show (2:ℤ) + ((m:ℤ)+1) - 1 = 2+(m:ℤ) by ring] using hs


private def shellPoint (t i : ℤ) : GaussianInt :=
  if i = 0 then pt (t+1) 0
  else if i ≤ t then pt (i-1) (t-i+1)
  else if i ≤ 2*t-1 then pt (t-i) (2*t-1-i)
  else if i ≤ 3*t-3 then pt (i-2*t) (i-3*t+2)
  else pt (3*t-3-i) (i-4*t+5)

private theorem shell_point_dist (t i : ℤ) (ht : 3 ≤ t) (hi : i ∈ Finset.Ico 0 (4*t-5)) :
    distance (shellPoint t i) = t+1 := by
  have ⟨hi0,hi1⟩ := Finset.mem_Ico.mp hi
  unfold shellPoint
  split_ifs <;>
    simp (disch := omega) [distance, pt, abs_of_nonneg, abs_of_nonpos] <;> omega

private theorem shell_injective (t : ℤ) (_ht : 3 ≤ t) :
    Set.InjOn (shellPoint t) (↑(Finset.Ico 0 (4*t-5)) : Set ℤ) := by
  intro i hi j hj h
  have ⟨hi0,hi1⟩ := Finset.mem_Ico.mp (Finset.mem_coe.mp hi)
  have ⟨hj0,hj1⟩ := Finset.mem_Ico.mp (Finset.mem_coe.mp hj)
  unfold shellPoint at h
  split_ifs at h <;> rw [pt_eq] at h <;> omega

private theorem mem_shell (t : ℤ) (ht : 3 ≤ t) (z : GaussianInt) :
    z ∈ (Finset.Ico 0 (4*t-5)).image (shellPoint t) ↔ distance z = t+1 := by
  constructor
  · intro h
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp h
    exact shell_point_dist t i ht hi
  · intro h
    obtain ⟨x,y⟩ := z
    change (if y < 0 then 3 + |x| - y
      else if x < 0 then 2 - x + y
      else if y = 0 then x else 1 + x + y) = t+1 at h
    apply Finset.mem_image.mpr
    have mk (i : ℤ) (hi : 0 ≤ i) (hj : i < 4*t-5) (he : shellPoint t i = pt x y) :
        ∃ i ∈ Finset.Ico 0 (4*t-5), shellPoint t i = pt x y :=
      ⟨i, Finset.mem_Ico.mpr ⟨hi,hj⟩, he⟩
    rcases le_or_gt 0 y with hy|hy
    · rcases le_or_gt 0 x with hx|hx
      · by_cases hy0 : y = 0
        · apply mk 0 (by omega) (by omega)
          rw [if_neg (not_lt.mpr hy), if_neg (not_lt.mpr hx), if_pos hy0] at h
          simp [shellPoint, hy0, h]
        · rw [if_neg (not_lt.mpr hy), if_neg (not_lt.mpr hx), if_neg hy0] at h
          apply mk (x+1) (by omega) (by omega)
          unfold shellPoint
          split_ifs <;> rw [pt_eq] <;> omega
      · rw [if_neg (not_lt.mpr hy), if_pos hx] at h
        apply mk (t-x) (by omega) (by omega)
        unfold shellPoint
        split_ifs <;> rw [pt_eq] <;> omega
    · rcases le_or_gt 0 x with hx|hx
      · rw [if_pos hy, abs_of_nonneg hx] at h
        apply mk (x+2*t) (by omega) (by omega)
        unfold shellPoint
        split_ifs <;> rw [pt_eq] <;> omega
      · rw [if_pos hy, abs_of_nonpos hx.le] at h
        apply mk (3*t-3-x) (by omega) (by omega)
        unfold shellPoint
        split_ifs <;> rw [pt_eq] <;> omega

private theorem lst_nodup (t : ℕ) : (Lst t).Nodup := by
  cases t with
  | zero => simp [Lst]
  | succ t => exact nodup_eraseDups _

private theorem length_step (t : ℕ) (ht : 3 ≤ t) :
    (Lst (t+1)).length = (Lst t).length + (4*t-5) := by
  let older := (Lst t).toFinset
  let newer := (Lst (t+1)).toFinset
  have ht' : (3:ℤ) ≤ t := by exact_mod_cast ht
  have hs : older ⊆ newer := by
    intro z hz
    simp only [older, newer, List.mem_toFinset, mem_lst, Nat.cast_add, Nat.cast_one] at hz ⊢
    omega
  have he : newer \ older = (Finset.Ico (0:ℤ) (4*(t:ℤ)-5)).image (shellPoint t) := by
    ext z
    simp only [older, newer, Finset.mem_sdiff, List.mem_toFinset, mem_lst, mem_shell _ ht',
      Nat.cast_add, Nat.cast_one]
    omega
  have hc := Finset.card_sdiff_add_card_eq_card hs
  rw [he, Finset.card_image_of_injOn (shell_injective _ ht'), Int.card_Ico] at hc
  have htcast : (4*(t:ℤ)-5).toNat = 4*t-5 := by omega
  rw [sub_zero, htcast] at hc
  simpa [older,newer,List.toFinset_card_of_nodup (lst_nodup t),
    List.toFinset_card_of_nodup (lst_nodup (t+1)), add_comm] using hc.symm

private theorem lst_length (t : ℕ) (ht : 3 ≤ t) :
    ((Lst t).length : ℤ) = 2*(t:ℤ)^2 - 7*t + 11 := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le ht
  induction m with
  | zero => decide
  | succ m ih =>
    rw [show 3+m.succ = (3+m)+1 by omega, length_step _ (by omega)]
    push_cast [Nat.cast_sub (show 5 ≤ 4*(3+m) by omega)]
    have h := ih (by omega)
    push_cast at h
    linarith [show (2 : ℤ)*((3+(m:ℤ))+1)^2 =
      2*(3+(m:ℤ))^2+4*(3+(m:ℤ))+2 by ring]


private theorem formula (n : ℕ) (hn : 1 ≤ n) :
    a (n+1) = 2*n^2+n+9 := by
  let t := n+2
  have ht : 3 ≤ t := by dsimp [t]; omega
  have ht' : (3:ℤ) ≤ t := by exact_mod_cast ht
  let w := pt (1-(t:ℤ)) 0
  have hw : w = -(((n+1 : ℕ) : ℤ) : GaussianInt) := by
    apply Zsqrtd.ext <;> simp [w,pt,t,Zsqrtd.re_neg,Zsqrtd.im_neg]
    omega
  have hnmem : w ∉ Lst t := by
    rw [mem_lst]
    have hneg : (1:ℤ) - (t:ℤ) < 0 := by omega
    simp only [w,distance,pt,Int.reduceLT,if_false,if_pos hneg]
    omega
  obtain ⟨s, hs⟩ := frontier t (by omega)
  have hind : (fourPoints t ++ s).idxOf w = 3 := by
    change (pt ((t:ℤ)+1) 0 :: pt 0 t :: pt 1 ((t:ℤ)-1) :: w :: s).idxOf w = 3
    have h0 : pt ((t:ℤ)+1) 0 ≠ w := by
      rw [ne_eq, show w = pt (1-(t:ℤ)) 0 by rfl, pt_eq]
      omega
    have h1 : pt 0 t ≠ w := by
      rw [ne_eq, show w = pt (1-(t:ℤ)) 0 by rfl, pt_eq]
      omega
    have h2 : pt 1 ((t:ℤ)-1) ≠ w := by
      rw [ne_eq, show w = pt (1-(t:ℤ)) 0 by rfl, pt_eq]
      omega
    rw [List.idxOf_cons_ne _ h0, List.idxOf_cons_ne _ h1,
      List.idxOf_cons_ne _ h2, List.idxOf_cons_self]
  have hLen := lst_length t ht
  have hwlen : a (n+1) = (Lst t).length + 4 := by
    unfold a
    change (Lst (t+1)).idxOf (-(((n+1 : ℕ) : ℤ) : GaussianInt)) + 1 = _
    rw [← hw, hs, List.append_assoc, List.idxOf_append_of_notMem hnmem, hind]
  rw [hwlen]
  have he : ((Lst t).length : ℤ) + 4 = (2 : ℤ)*(n:ℤ)^2+n+9 := by
    rw [hLen]
    simp only [t,Nat.cast_add,Nat.cast_ofNat]
    ring
  exact_mod_cast he

private theorem aOne : a 1 = 8 := by decide

private theorem closed (n : ℕ) (hn : 2 ≤ n) :
    (a n : ℤ) = 2*(n:ℤ)^2-3*n+10 := by
  have h := formula (n-1) (by omega)
  rw [show n-1+1=n by omega] at h
  rw [h]
  push_cast [Nat.cast_sub (show 1 ≤ n by omega)]
  ring

private theorem recurrence (n : ℕ) (hn : 5 ≤ n) :
    (a n : ℤ) = 3*a (n-1) - 3*a (n-2) + a (n-3) := by
  rw [closed n (by omega), closed (n-1) (by omega), closed (n-2) (by omega),
    closed (n-3) (by omega)]
  push_cast [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega),
    Nat.cast_sub (show 3 ≤ n by omega)]
  ring

private theorem generating :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) * (PowerSeries.X - 1) ^ 3 =
      PowerSeries.X * (-8 + 12 * PowerSeries.X - 7 * PowerSeries.X ^ 2 - PowerSeries.X ^ 3) := by
  let F : PowerSeries ℤ := PowerSeries.mk fun n => if n = 0 then 0 else a n
  let X : PowerSeries ℤ := PowerSeries.X
  change F * (X-1)^3 = X * (-8 + 12*X - 7*X^2 - X^3)
  rw [show F * (X-1)^3 = X^3*F - PowerSeries.C 3*(X^2*F) +
      PowerSeries.C 3*(X^1*F) - F by simp only [map_ofNat]; ring]
  rw [show X*(-8+12*X-7*X^2-X^3) =
      PowerSeries.C (-8)*X^1 + PowerSeries.C 12*X^2 - PowerSeries.C 7*X^3 - X^4 by
    simp only [map_ofNat, map_neg]
    ring]
  apply PowerSeries.ext
  intro n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow, F, PowerSeries.coeff_mk, X]
  by_cases hn : 5 ≤ n
  · have hne (j : ℕ) (hj : j ≤ 4) : n ≠ j := by omega
    have hns (j : ℕ) (hj : j ≤ 4) : n-j ≠ 0 := by omega
    simp only [if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega), if_neg (hne 0 (by decide)), if_neg (hne 1 (by decide)),
      if_neg (hne 2 (by decide)), if_neg (hne 3 (by decide)), if_neg (hne 4 (by decide)),
      if_neg (hns 1 (by decide)), if_neg (hns 2 (by decide)), if_neg (hns 3 (by decide))]
    linarith [recurrence n hn]
  · have ha2 : a 2 = 12 := by simpa using formula 1 (by decide)
    have ha3 : a 3 = 19 := by simpa using formula 2 (by decide)
    have ha4 : a 4 = 30 := by simpa using formula 3 (by decide)
    interval_cases n <;> norm_num [aOne,ha2,ha3,ha4]

end A232867Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a232867.main := by
  exact ⟨A232867Proof.formula, A232867Proof.generating, A232867Proof.recurrence⟩
