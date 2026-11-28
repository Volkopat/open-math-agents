import OMAStatements.S_oeis_a288663
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Ring.GeomSum

namespace OMA.A288663

private def tag (k d s : Int) : Option Bool :=
  if s < 0 then some (decide (s % 2 = 1))
  else if d = 0 then some (decide (s % 2 = 0 ∧ (0 < s ∨ k = 0)))
  else if d = 1 then some true
  else if d = 2 then some (if k % 2 = 1 ∧ 0 < s then decide (s % 2 = 0) else decide (s % 2 = 1))
  else if d = 3 then some (decide (k % 2 = 1 ∨ 0 < s))
  else none

private def fits (o : Option Bool) (b : Bool) : Prop := o = none ∨ o = some b

private instance decFits (o : Option Bool) (b : Bool) : Decidable (fits o b) := by
  unfold fits
  infer_instance

private def upd (c e w n s : Bool) : Bool :=
  (493 : Nat).testBit (c.toNat + 2 * (e.toNat + w.toNat + n.toNat + s.toNat))

private def east (k d s : Int) :=
  if d = 0 then tag k 1 (s-2) else tag (k+1) (d-1) s
private def west (k d s : Int) :=
  if k = 0 then east k d s else tag (k-1) (d+1) s
private def south (k d s : Int) :=
  if d = 0 then west k d s else tag k (d-1) (s+2)

private def legal (k d s : Int) : Prop := ∀ c e w n a : Bool,
  fits (tag k d s) c → fits (east k d s) e → fits (west k d s) w →
  fits (tag k (d+1) (s-2)) n → fits (south k d s) a → fits (tag k d (s+1)) (upd c e w n a)

private def allBool (P : Bool → Prop) (inst : ∀ b, Decidable (P b)) : Decidable (∀ v, P v) := by
  letI : Decidable (P false) := inst false
  letI : Decidable (P true) := inst true
  exact decidable_of_iff (P false ∧ P true) (by
    constructor
    · intro h v; cases v
      · exact h.1
      · exact h.2
    · intro h; exact ⟨h false, h true⟩)

private instance decLegal (k d s : Int) : Decidable (legal k d s) := by
  unfold legal
  apply @allBool
  intro c
  apply @allBool
  intro e
  apply @allBool
  intro w
  apply @allBool
  intro n
  apply @allBool
  intro a
  infer_instance

private def kc (k : Int) := if k < 2 then k else 2 + k % 2
private def dc (d : Int) := min d 5
private def sc (s : Int) := if 5 < s then 4 + s % 2 else if s < -5 then -4 - s % 2 else s

private theorem sameTag (k d s i j w : Int) (hi : -1 ≤ i ∧ i ≤ 1)
    (hj : -1 ≤ j ∧ j ≤ 1) (hw : -2 ≤ w ∧ w ≤ 2) :
    tag (k+i) (d+j) (s+w) = tag (kc k+i) (dc d+j) (sc s+w) := by
  have hk0 : (k+i = 0) = (kc k+i = 0) := by unfold kc; split <;> apply propext <;> omega
  have hkp : (k+i)%2 = (kc k+i)%2 := by unfold kc; split <;> omega
  have hd (v : Int) (hv : 0 ≤ v ∧ v ≤ 3) : (d+j=v) = (dc d+j=v) := by
    unfold dc; rw [Int.min_def]; split <;> apply propext <;> omega
  have hsp : (s+w)%2 = (sc s+w)%2 := by unfold sc; split <;> (try split) <;> omega
  have hsneg : (s+w<0) = (sc s+w<0) := by unfold sc; split <;> (try split) <;> apply propext <;> omega
  have hspos : (0<s+w) = (0<sc s+w) := by unfold sc; split <;> (try split) <;> apply propext <;> omega
  unfold tag
  simp only [hk0,hkp,hd 0 (by decide),hd 1 (by decide),hd 2 (by decide),hd 3 (by decide),hsp,hsneg,hspos]

private theorem localCheck : ∀ k : Fin 4, ∀ d : Fin 6, ∀ a : Fin 11,
  ¬ (k.val = 0 ∧ d.val = 0 ∧ a.val = 4) →
  legal (k.val : Int) (d.val : Int) ((a.val : Int) - 5) := by
  decide +kernel

private theorem localAll (k d s : Int) (hk : 0 ≤ k) (hd : 0 ≤ d)
    (ht : 0 ≤ 2*(k+d)+s) : legal k d s := by
  have k0 : (k=0) = (kc k=0) := by unfold kc; split <;> apply propext <;> omega
  have d0 : (d=0) = (dc d=0) := by unfold dc; rw [Int.min_def]; split <;> apply propext <;> omega
  have t0 := sameTag k d s 0 0 0 (by decide) (by decide) (by decide)
  have ta := sameTag k d s 0 0 1 (by decide) (by decide) (by decide)
  have tn := sameTag k d s 0 1 (-2) (by decide) (by decide) (by decide)
  have te := sameTag k d s 1 (-1) 0 (by decide) (by decide) (by decide)
  have tw := sameTag k d s (-1) 1 0 (by decide) (by decide) (by decide)
  have ts := sameTag k d s 0 (-1) 2 (by decide) (by decide) (by decide)
  simp only [Int.add_zero, Int.add_neg_one] at t0 ta tn te tw ts
  have tminus (b : Int) : b + (-2) = b-2 := by omega
  simp only [tminus] at tn
  have de : east k d s = east (kc k) (dc d) (sc s) := by
    unfold east
    by_cases z : d = 0
    · have zz := Eq.mp d0 z
      simp only [if_pos z, if_pos zz]
      simpa only [z, show dc 0 = 0 by decide, Int.zero_add] using tn
    · have zz : dc d ≠ 0 := fun h => z (Eq.mpr d0 h)
      simp only [if_neg z, if_neg zz, te]
  have dw : west k d s = west (kc k) (dc d) (sc s) := by
    unfold west
    simp only [k0,de,tw]
  have ds : south k d s = south (kc k) (dc d) (sc s) := by
    unfold south
    simp only [d0,dw,ts]
  unfold legal
  rw [t0,ta,de,dw,ds,tn]
  have kb : 0 ≤ kc k ∧ kc k < 4 := by unfold kc; split <;> omega
  have db : 0 ≤ dc d ∧ dc d < 6 := by unfold dc; rw [Int.min_def]; split <;> omega
  have sb : 0 ≤ sc s+5 ∧ sc s+5 < 11 := by unfold sc; split <;> (try split) <;> omega
  let K : Fin 4 := ⟨(kc k).toNat, by omega⟩
  let D : Fin 6 := ⟨(dc d).toNat, by omega⟩
  let A : Fin 11 := ⟨(sc s+5).toNat, by omega⟩
  have check := localCheck K D A (by
    dsimp [K,D,A]; intro h
    have : k=0 := by rw [k0]; omega
    have : d=0 := by rw [d0]; omega
    unfold sc at h; split at h <;> (try split at h) <;> omega)
  dsimp [K,D,A] at check
  have cK : (((kc k).toNat : Nat) : Int) = kc k := by omega
  have cD : (((dc d).toNat : Nat) : Int) = dc d := by omega
  have cA : (((sc s+5).toNat : Nat) : Int) - 5 = sc s := by omega
  rw [cK,cD,cA] at check
  exact check


open OMA.S_oeis_a288663

private theorem flipCell (t : Nat) (x y : Int) : cell 493 t (-x) y = cell 493 t x y := by
  induction t generalizing x y with
  | zero =>
    simp only [cell]
    congr 1
    apply propext
    omega
  | succ t ih =>
    simp only [cell, show -x+1 = -(x-1) by omega, show -x-1 = -(x+1) by omega, ih]
    congr 1 <;> omega

private theorem swapCell (t : Nat) (x y : Int) : cell 493 t y x = cell 493 t x y := by
  induction t generalizing x y with
  | zero => simp [cell, and_comm]
  | succ t ih =>
    have a := ih x y
    have b := ih x (y+1)
    have c := ih x (y-1)
    have d := ih (x+1) y
    have e := ih (x-1) y
    simp only [cell]
    rw [a,b,c,d,e]
    congr 1 <;> omega

private theorem sector (t : Nat) (k d : Int) (hk : 0 ≤ k) (hd : 0 ≤ d) :
    fits (tag k d ((t:Int)-2*(k+d))) (cell 493 t k (k+d)) := by
  induction t generalizing k d with
  | zero =>
    by_cases z : k+d=0
    · have k0 : k=0 := by omega
      have d0 : d=0 := by omega
      subst k; subst d
      decide
    · have neg : (0:Int)-2*(k+d)<0 := by omega
      change fits (tag k d ((0:Int)-2*(k+d))) (cell 493 0 k (k+d))
      unfold fits tag
      rw [if_pos neg]
      simp [cell,z]
  | succ t ih =>
    let s : Int := (t:Int)-2*(k+d)
    let X : Int → Int → Bool := cell 493 t
    have c : fits (tag k d s) (X k (k+d)) := ih k d hk hd
    have e : fits (east k d s) (X (k+1) (k+d)) := by
      unfold east
      by_cases dz : d=0
      · subst d
        have he := ih k 1 hk (by decide)
        change fits (tag k 1 (s-2)) (cell 493 t (k+1) (k+0))
        rw [Int.add_zero, swapCell t k (k+1)]
        rwa [show s-2 = (t:Int)-2*(k+1) by dsimp [s]; omega]
      · rw [if_neg dz]
        have he := ih (k+1) (d-1) (by omega) (by omega)
        rwa [show (k+1)+(d-1) = k+d by omega] at he
    have w : fits (west k d s) (X (k-1) (k+d)) := by
      unfold west
      by_cases kz : k=0
      · rw [if_pos kz]
        subst k
        have r := flipCell t 1 ((0:Int)+d)
        change fits (east 0 d s) (cell 493 t (0-1) (0+d))
        exact r.symm ▸ e
      · rw [if_neg kz]
        have hw := ih (k-1) (d+1) (by omega) (by omega)
        rwa [show (k-1)+(d+1) = k+d by omega] at hw
    have n : fits (tag k (d+1) (s-2)) (X k ((k+d)+1)) := by
      have hn := ih k (d+1) hk (by omega)
      rw [show k+(d+1)=(k+d)+1 by omega, show (t:Int)-2*((k+d)+1)=s-2 by dsimp [s]; omega] at hn
      exact hn
    have a : fits (south k d s) (X k ((k+d)-1)) := by
      unfold south
      by_cases dz : d=0
      · rw [if_pos dz]
        subst d
        simp only [Int.add_zero] at w ⊢
        change fits (west k 0 s) (cell 493 t k (k-1))
        rw [swapCell t (k-1) k]
        exact w
      · rw [if_neg dz]
        have ha := ih k (d-1) hk (by omega)
        rw [show k+(d-1)=(k+d)-1 by omega, show (t:Int)-2*((k+d)-1)=s+2 by dsimp [s]; omega] at ha
        exact ha
    have h := localAll k d s hk hd (by dsimp [s]; omega) _ _ _ _ _ c e w n a
    change fits (tag k d (((t+1:Nat):Int)-2*(k+d))) (upd _ _ _ _ _)
    rw [show (((t+1:Nat):Int)-2*(k+d))=s+1 by dsimp [s]; omega]
    exact h

theorem diagonal (t j : Nat) : OMA.S_oeis_a288663.cell 493 t (j : Int) (j : Int) = true ↔
    ((t < 2*j ∧ t % 2 = 1) ∨ (2*j ≤ t ∧ t % 2 = 0 ∧ (2*j < t ∨ j = 0))) := by
  have h := sector t (j:Int) 0 (by omega) (by omega)
  simp only [Int.add_zero] at h
  unfold fits tag at h
  by_cases ht : (t:Int)-2*(j:Int)<0
  · simp only [if_pos ht, Option.some.injEq, Option.some_ne_none, false_or] at h
    rw [←h]
    simp only [decide_eq_true_eq]
    omega
  · simp only [if_neg ht, if_true, Option.some.injEq, Option.some_ne_none, false_or] at h
    rw [←h]
    simp only [decide_eq_true_eq]
    omega

end OMA.A288663

open OMA.S_oeis_a288663

namespace OMA.A288663

lemma a_as_diagonal (t : ℕ) :
    a t = ∑ j ∈ Finset.range (t + 1),
      if cell 493 t (j : ℤ) (j : ℤ) then (2 : ℤ) ^ j else 0 := by
  unfold a
  rw [← Finset.sum_range_reflect (fun j : ℕ =>
    if cell 493 t (j : ℤ) (j : ℤ) then (2 : ℤ) ^ j else 0)]
  apply Finset.sum_congr rfl
  intro j hj
  have hle : j ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  simp only [Nat.add_sub_cancel, Nat.cast_sub hle]

lemma two_sum (n : ℕ) : (∑ i ∈ Finset.range n, (2 : ℤ) ^ i) = 2 ^ n - 1 := by
  simpa using geom_sum_mul (2 : ℤ) n

lemma prefix_sum (N m : ℕ) (h : m ≤ N) :
    (∑ i ∈ Finset.range N, if i < m then (2 : ℤ) ^ i else 0) = 2 ^ m - 1 := by
  have hf : (Finset.range N).filter (fun i => i < m) = Finset.range m := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.sum_filter, hf, two_sum]

lemma suffix_sum (N m : ℕ) (h : m ≤ N) :
    (∑ i ∈ Finset.range N, if m ≤ i then (2 : ℤ) ^ i else 0) = 2 ^ N - 2 ^ m := by
  have splitSum : ∀ i : ℕ, (if m ≤ i then (2 : ℤ) ^ i else 0) =
      2 ^ i - (if i < m then 2 ^ i else 0) := by
    intro i
    by_cases hi : i < m
    · simp [hi, Nat.not_le_of_lt hi]
    · simp [hi, Nat.le_of_not_gt hi]
  simp only [splitSum, Finset.sum_sub_distrib, two_sum, prefix_sum N m h]
  ring

lemma closed493 (hd : ∀ t j : ℕ, cell 493 t (j : ℤ) (j : ℤ) = true ↔
    ((t < 2*j ∧ t % 2 = 1) ∨ (2*j ≤ t ∧ t % 2 = 0 ∧ (2*j < t ∨ j = 0)))) :
    a 0 = 1 ∧ (∀ m : ℕ, 1 ≤ m → a (2*m) = (2:ℤ)^m - 1) ∧
    (∀ m : ℕ, a (2*m+1) = (4:ℤ)^(m+1) - (2:ℤ)^(m+1)) := by
  refine ⟨by decide, ?_, ?_⟩
  · intro m hm
    rw [a_as_diagonal]
    have hh (i : ℕ) : cell 493 (2*m) (i : ℤ) (i : ℤ) = true ↔ i < m := (hd _ _).trans (by omega)
    simp only [hh]
    exact prefix_sum _ _ (by omega)
  · intro m
    rw [a_as_diagonal]
    have hh (i : ℕ) : cell 493 (2*m+1) (i : ℤ) (i : ℤ) = true ↔ m + 1 ≤ i := (hd _ _).trans (by omega)
    simp only [hh]
    rw [suffix_sum _ _ (by omega), show 2*m+1+1 = 2*(m+1) by omega, pow_mul]
    norm_num

end OMA.A288663

open OMA.S_oeis_a288663

namespace OMA.A288663

lemma recurrence493
    (he : ∀ m : ℕ, 1 ≤ m → a (2 * m) = (2 : ℤ) ^ m - 1)
    (ho : ∀ m : ℕ, a (2 * m + 1) = (4 : ℤ) ^ (m + 1) - (2 : ℤ) ^ (m + 1))
    (n : ℕ) (hn : 7 ≤ n) :
    (a n : ℚ) = 7 * a (n - 2) - 14 * a (n - 4) + 8 * a (n - 6) := by
  by_cases hh : n % 2 = 0
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * (k + 4) := ⟨n / 2 - 4, by omega⟩
    rw [show 2 * (k + 4) - 2 = 2 * (k + 3) by omega,
      show 2 * (k + 4) - 4 = 2 * (k + 2) by omega,
      show 2 * (k + 4) - 6 = 2 * (k + 1) by omega,
      he _ (by omega), he _ (by omega), he _ (by omega), he _ (by omega)]
    push_cast
    simp only [pow_add]
    ring
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * (k + 3) + 1 := ⟨n / 2 - 3, by omega⟩
    rw [show 2 * (k + 3) + 1 - 2 = 2 * (k + 2) + 1 by omega,
      show 2 * (k + 3) + 1 - 4 = 2 * (k + 1) + 1 by omega,
      show 2 * (k + 3) + 1 - 6 = 2 * k + 1 by omega, ho, ho, ho, ho]
    push_cast
    simp only [pow_add]
    ring

open PowerSeries in
lemma algebra (ha0 : a 0 = 1)
    (heven : ∀ m : ℕ, 1 ≤ m → a (2 * m) = (2 : ℤ) ^ m - 1)
    (hodd : ∀ m : ℕ, a (2 * m + 1) = (4 : ℤ) ^ (m + 1) - (2 : ℤ) ^ (m + 1)) :
    type_of% @OMA.S_oeis_a288663.main := by
  have hrec := recurrence493 heven hodd
  refine ⟨?_, hrec⟩
  let s := PowerSeries.mk (fun n => (a n : ℚ))
  change s * _ = _
  have left : s * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X) * (1 - 2 * X ^ 2)) =
      s - 7 • (s * X ^ 2) + 14 • (s * X ^ 4) - 8 • (s * X ^ 6) := by
    simp only [nsmul_eq_mul]
    ring
  have right : (1 + 2 * X - 6 * X ^ 2 - 2 * X ^ 3 + 10 * X ^ 4 - 8 * X ^ 6 : PowerSeries ℚ) =
      1 + 2 • X - 6 • X ^ 2 - 2 • X ^ 3 + 10 • X ^ 4 - 8 • X ^ 6 := by
    simp only [nsmul_eq_mul, Nat.cast_ofNat]
  rw [left, right]
  apply PowerSeries.ext
  intro n
  simp only [map_add, map_sub, map_nsmul, coeff_mul_X_pow', coeff_X_pow, coeff_X, coeff_one,
    s, coeff_mk]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  by_cases h : 7 ≤ n
  · simp only [if_pos (show 2 ≤ n by omega), if_pos (show 4 ≤ n by omega),
      if_pos (show 6 ≤ n by omega), if_neg (show n ≠ 0 by omega),
      if_neg (show n ≠ 1 by omega), if_neg (show n ≠ 2 by omega),
      if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 4 by omega),
      if_neg (show n ≠ 6 by omega)]
    linarith [hrec n h]
  · have h1 : a 1 = 2 := by simpa using hodd 0
    have h2 : a 2 = 1 := by simpa using heven 1 (by decide)
    have h3 : a 3 = 12 := by convert hodd 1 using 1; norm_num
    have h4 : a 4 = 3 := by convert heven 2 (by decide) using 1; norm_num
    have h5 : a 5 = 56 := by convert hodd 2 using 1; norm_num
    have h6 : a 6 = 7 := by convert heven 3 (by decide) using 1; norm_num
    have hn : n ≤ 6 := by omega
    interval_cases n <;> norm_num [ha0, h1, h2, h3, h4, h5, h6]


theorem of_diagonal (hd : ∀ t j : ℕ, cell 493 t (j : ℤ) (j : ℤ) = true ↔
    ((t < 2*j ∧ t % 2 = 1) ∨ (2*j ≤ t ∧ t % 2 = 0 ∧ (2*j < t ∨ j = 0)))) :
    type_of% @OMA.S_oeis_a288663.main := by
  obtain ⟨h0, he, ho⟩ := closed493 hd
  exact algebra h0 he ho

end OMA.A288663

theorem OMA.solution : type_of% @OMA.S_oeis_a288663.main :=
  OMA.A288663.of_diagonal OMA.A288663.diagonal
