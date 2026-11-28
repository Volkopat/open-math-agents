import OMAStatements.S_oeis_a282606

/-!
The Rule 489 strip certificate and its local transition proof are adapted
from @Aryan-Poonacha’s A282607 proof (c11caa024). The left-to-origin readout
places the cells nearest the origin at the lowest decimal powers. Increasing
the stage by four shifts the periodic suffix by four places. After that
suffix cancels, the correction depends on five digits and repeats every two
stages, giving the recurrence. The first fourteen coefficients complete
the generating-function identity.
-/
namespace Rule489
open OMA.S_oeis_a282606

private def cap (a x : ℤ) := if x ≤ a then x else a+1+(x-a-1)%4
private def shiftCap (a b d : ℤ) := if d < a then a-1-(a-1-d)%4 else cap b d

/-- 0 or 1 fixes the cell, 2 permits either state. The three coordinates are
the horizontal distance, the time minus that distance, and the vertical distance. -/
private def stripTable : Array Nat := #[19001776979789333773698604348575562294322086246413638366172177378221491904054613,19023487997815408077496785340327143477967504368450764604248682714629178740002816,18994539973780642339099210684658376061779080539420773359486815671485402550633813,19609835666528871988041067738086712369127950093562689030514635913074996036325376,19725656032222656392547770242258529115913969814755008049235943957154020005512533,19689462167943348766139425709706852520629875126087883838016704366596129406930944,19689462167943348766139425709706852520624365225289146061173203506055106732754261,19725656032222656392547770236273688854078224912920036328014699678047341139808256,19725656032222656392547770242261454973684017032511177535473315422183604636091733,19689462167943348766139425709706852520629875126087883838016704366596129406930944,19689462167943348766139425709706852520624365225289146061173203506055106732754261]

private def label (x d y : ℤ) : Nat :=
  ((stripTable[(cap 6 x).toNat]?.getD 0) >>> (2*((shiftCap (-1) 12 d+5).toNat*6+(min 5 y).toNat))) % 4 % 3

private def allows (v : Nat) (b : Bool) : Prop := v=2 ∨ v=b.toNat
private instance (v : Nat) (b : Bool) : Decidable (allows v b) := inferInstanceAs (Decidable (_ ∨ _))

private def nextCell (c l r u v : Bool) : Bool :=
  (489:ℕ).testBit (c.toNat + 2*(l.toNat+r.toNat+u.toNat+v.toNat))

private def near (x : ℤ) := if x=0 then 1 else x-1
private def delta (x : ℤ) := if x=0 then -1 else 1

private def stepOK (x d y : ℤ) : Prop := ∀ c l r u v : Bool,
  allows (label x d y) c → allows (label (near x) (d+delta x) y) l →
  allows (label (x+1) (d-1) y) r → allows (label x d (near y)) u →
  allows (label x d (y+1)) v → allows (label x (d+1) y) (nextCell c l r u v)

private def boolForall (p : Bool → Prop) (hp : DecidablePred p) : Decidable (∀ b, p b) :=
  letI := hp
  decidable_of_iff (p false ∧ p true) ⟨fun h b => by cases b <;> tauto, fun h => ⟨h _, h _⟩⟩

private instance (x d y : ℤ) : Decidable (stepOK x d y) :=
  by
    unfold stepOK
    apply @boolForall; intro c
    apply @boolForall; intro l
    apply @boolForall; intro r
    apply @boolForall; intro u
    apply @boolForall; intro v
    infer_instance

private def transfer (a b c d e : ℕ) : ℕ :=
  (133194604801850076402949083861815871495061513718398638310242570360897160783941316322978270979596523682139925718852639281804229701520985106104363297 >>> (2*(a+3*(b+3*(c+3*(d+3*e)))))) % 4

private def transferSpec (a b c d e : Fin 3) : Prop := ∀ p q r s t : Bool,
  allows a p → allows b q → allows c r → allows d s → allows e t →
    allows (transfer a b c d e) (nextCell p q r s t)
private instance (a b c d e : Fin 3) : Decidable (transferSpec a b c d e) := by
  unfold transferSpec
  apply @boolForall; intro p
  apply @boolForall; intro q
  apply @boolForall; intro r
  apply @boolForall; intro s
  apply @boolForall; intro t
  infer_instance

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem transfer_sound : ∀ a b c d e : Fin 3, transferSpec a b c d e := by decide +kernel

private def stepTest (x d y : ℤ) : Prop :=
  label x (d+1) y = 2 ∨ label x (d+1) y =
    transfer (label x d y) (label (near x) (d+delta x) y) (label (x+1) (d-1) y)
      (label x d (near y)) (label x d (y+1))

private instance (x d y : ℤ) : Decidable (stepTest x d y) := inferInstanceAs (Decidable (_ ∨ _))

private def validBox : Prop :=
  ∀ x : Fin 12, ∀ b : Fin 24, ∀ y : Fin 7,
    x.val≠0 ∨ b.val≠5 → stepTest (x:ℕ) ((b:ℕ)-6:ℤ) (y:ℕ)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
private theorem boxCheck : validBox := by unfold validBox; decide +kernel

private theorem certificate (x : Fin 12) (b : Fin 24) (y : Fin 7)
    (h : x.val≠0 ∨ b.val≠5) : stepOK (x:ℕ) ((b:ℕ)-6:ℤ) (y:ℕ) := by
  have bound (i j k : ℤ) : label i j k < 3 := Nat.mod_lt _ (by decide)
  obtain hu | he := boxCheck x b y h
  · intro p q r s t _ _ _ _ _
    exact Or.inl hu
  · intro p q r s t hp hq hr hs ht
    have hspec := transfer_sound ⟨_,bound _ _ _⟩ ⟨_,bound _ _ _⟩ ⟨_,bound _ _ _⟩
      ⟨_,bound _ _ _⟩ ⟨_,bound _ _ _⟩ p q r s t hp hq hr hs ht
    rw [he]
    exact hspec

private theorem cap_step (x s : ℤ) (hs : -1 ≤ s ∧ s≤1) :
    cap 6 (cap 7 x+s) = cap 6 (x+s) := by
  unfold cap; split_ifs <;> omega
private theorem dcap_step (d s : ℤ) (hs : -1 ≤ s ∧ s≤1) :
    shiftCap (-1) 12 (shiftCap (-2) 13 d+s) = shiftCap (-1) 12 (d+s) := by
  unfold shiftCap cap; split_ifs <;> omega
private theorem height_step (y s : ℤ) (hs : -1 ≤ s ∧ s≤1) :
    min 5 (min 6 y+s) = min 5 (y+s) := by omega

private theorem loc (x d y a b c : ℤ) (ha : -1≤a ∧ a≤1) (hb : -1≤b ∧ b≤1)
    (hc : -1≤c ∧ c≤1) :
    label (cap 7 x+a) (shiftCap (-2) 13 d+b) (min 6 y+c) =
      label (x+a) (d+b) (y+c) := by
  unfold label; rw [cap_step x a ha,dcap_step d b hb,height_step y c hc]

private theorem local_step {x y d : ℤ} (hx : 0≤x) (hy : 0≤y) (ht : 0≤x+d) :
    stepOK x d y := by
  let X := cap 7 x
  let D := shiftCap (-2) 13 d
  let Y := min 6 y
  have hX : 0≤X ∧ X<12 := by dsimp [X,cap]; split <;> omega
  have hD : -6≤D ∧ D<18 := by dsimp [D,shiftCap,cap]; split_ifs <;> omega
  have hY : 0≤Y ∧ Y<7 := by dsimp [Y]; omega
  have xzero : X=0 ↔ x=0 := by dsimp [X,cap]; split <;> omega
  have yzero : Y=0 ↔ y=0 := by dsimp [Y]; omega
  have dz : D=(-1) ↔ d=(-1) := by dsimp [D,shiftCap,cap]; split_ifs <;> omega
  have hcert := certificate ⟨X.toNat,by omega⟩ ⟨(D+6).toNat,by omega⟩ ⟨Y.toNat,by omega⟩ (by change X.toNat≠0 ∨ (D+6).toNat≠5; omega)
  simp only [Int.toNat_of_nonneg hX.1, Int.toNat_of_nonneg hY.1,
    Int.toNat_of_nonneg (show 0≤D+6 by omega),add_sub_cancel_right] at hcert
  have l (a b c : ℤ) (ha : -1≤a ∧ a≤1) (hb : -1≤b ∧ b≤1) (hc : -1≤c ∧ c≤1) :
      label (X+a) (D+b) (Y+c) = label (x+a) (d+b) (y+c) := loc x d y a b c ha hb hc
  have h0 := l 0 0 0 (by decide) (by decide) (by decide)
  have h1 := l 0 1 0 (by decide) (by decide) (by decide)
  have hr := l 1 (-1) 0 (by decide) (by decide) (by decide)
  have hv := l 0 0 1 (by decide) (by decide) (by decide)
  have hl : label (near X) (D+delta X) Y = label (near x) (d+delta x) y := by
    by_cases h : x=0
    · simpa [near,delta,h,xzero.mpr h] using l 1 (-1) 0 (by decide) (by decide) (by decide)
    · simpa [near,delta,h,mt xzero.mp h,sub_eq_add_neg] using l (-1) 1 0 (by decide) (by decide) (by decide)
  have hu : label X D (near Y) = label x d (near y) := by
    by_cases h : y=0
    · simpa [near,h,yzero.mpr h] using l 0 0 1 (by decide) (by decide) (by decide)
    · simpa [near,h,mt yzero.mp h,sub_eq_add_neg] using l 0 0 (-1) (by decide) (by decide) (by decide)
  simp only [add_zero,← sub_eq_add_neg] at h0 h1 hr hv
  unfold stepOK at *
  simpa only [h0,h1,hr,hv,hl,hu] using hcert

end Rule489
namespace Rule489
open OMA.S_oeis_a282606

private def initialBox : Prop :=
  ∀ X : Fin 12, ∀ b : Fin 24, ∀ Y : Fin 7,
    ((X:ℕ)=0 ∧ (b:ℕ)=6 ∨ 0<(X:ℕ) ∧ (b:ℕ)<6 ∧ ((X:ℕ)+(b:ℕ))%2=0) →
    allows (label (X:ℕ) ((b:ℕ)-6:ℤ) (Y:ℕ)) (decide ((X:ℕ)=0 ∧ (Y:ℕ)=0))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 2000000 in
private theorem initial_cert : initialBox := by unfold initialBox; decide +kernel

set_option maxRecDepth 10000 in
private theorem initial_spec (x y : ℤ) (hx : 0≤x) (hy : 0≤y) :
    allows (label x (-x) y) (decide (x=0 ∧ y=0)) := by
  let X := cap 7 x
  let D := shiftCap (-2) 13 (-x)
  let Y := min 6 y
  have hX : 0≤X ∧ X<12 := by dsimp [X,cap]; split <;> omega
  have hD : -6≤D ∧ D<18 := by dsimp [D,shiftCap,cap]; split_ifs <;> omega
  have hY : 0≤Y ∧ Y<7 := by dsimp [Y]; omega
  have xzero : X=0 ↔ x=0 := by dsimp [X,cap]; split <;> omega
  have yzero : Y=0 ↔ y=0 := by dsimp [Y]; omega
  have hcon : X=0 ∧ D=0 ∨ 0<X ∧ D<0 ∧ (X+D+6)%2=0 := by
    dsimp [X,D,cap,shiftCap]; split_ifs <;> omega
  have hc := initial_cert ⟨X.toNat,by omega⟩ ⟨(D+6).toNat,by omega⟩ ⟨Y.toNat,by omega⟩ (by
    change X.toNat=0 ∧ (D+6).toNat=6 ∨ 0<X.toNat ∧ (D+6).toNat<6 ∧ (X.toNat+(D+6).toNat)%2=0
    omega)
  have he := loc x (-x) y 0 0 0 (by decide) (by decide) (by decide)
  simp only [add_zero] at he
  change label X D Y = label x (-x) y at he
  have hz : X.toNat=0 ↔ x=0 := by omega
  have hzy : Y.toNat=0 ↔ y=0 := by omega
  simpa only [Int.toNat_of_nonneg hX.1,Int.toNat_of_nonneg hY.1,
    Int.toNat_of_nonneg (show 0≤D+6 by omega),add_sub_cancel_right,he,hz,hzy] using hc

private def back (z : ℤ) := if z<0 then z+1 else z-1
private def away (z : ℤ) := if z<0 then z-1 else z+1
private theorem near_abs (z : ℤ) : |back z|=near |z| := by
  unfold back near; simp only [abs_eq_max_neg]; split_ifs <;> omega
private theorem away_abs (z : ℤ) : |away z|=|z|+1 := by
  unfold away; simp only [abs_eq_max_neg]; split_ifs <;> omega
private theorem near_offset (z : ℤ) : near |z|=|z|-delta |z| := by
  unfold near delta; split_ifs <;> omega

private theorem cell_step (t : ℕ) (i j : ℤ) :
    cell 489 (t+1) i j = nextCell (cell 489 t i j) (cell 489 t (back i) j)
      (cell 489 t (away i) j) (cell 489 t i (back j)) (cell 489 t i (away j)) := by
  simp only [cell,nextCell,back,away]
  split_ifs <;> congr 3 <;> omega

private theorem invariant (t : ℕ) (i j : ℤ) :
    allows (label |i| ((t:ℤ)-|i|) |j|) (cell 489 t i j) := by
  induction t generalizing i j with
  | zero =>
    simpa [cell] using initial_spec |i| |j| (abs_nonneg _) (abs_nonneg _)
  | succ t ih =>
    have ht := local_step (x:=|i|) (y:=|j|) (d:=(t:ℤ)-|i|) (abs_nonneg _) (abs_nonneg _) (by omega)
    have l := ih (back i) j
    have r := ih (away i) j
    have u := ih i (back j)
    have v := ih i (away j)
    rw [near_abs] at l u
    rw [away_abs] at r v
    rw [show (t:ℤ)-near |i| = t-|i|+delta |i| by rw [near_offset]; ring] at l
    rw [show (t:ℤ)-(|i|+1)=t-|i|-1 by ring] at r
    rw [cell_step]
    push_cast
    rw [show (t:ℤ)+1-|i|=t-|i|+1 by ring]
    exact ht _ _ _ _ _ (ih i j) l r u v

end Rule489
namespace Rule489
open OMA.S_oeis_a282606

private def digit (x d : ℕ) : ℤ := label x d 0
private def axisBox : Prop := ∀ x : Fin 11, ∀ d : Fin 17,
    digit x d < 2 ∧ (8≤(d:ℕ) → digit x (d+2:ℕ) = digit x d) ∧
      (1≤(x:ℕ) → digit (x+4:ℕ) d = digit x d)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem axis_cert : axisBox := by unfold axisBox; decide +kernel

private theorem axis_prop (x d : ℕ) :
    digit x d < 2 ∧ (8≤d → digit x (d+2) = digit x d) ∧
      (1≤x → digit (x+4) d = digit x d) := by
  let X := (cap 6 (x:ℤ)).toNat
  let D := (cap 12 (d:ℤ)).toNat
  have hx : X<11 := by dsimp [X,cap]; split <;> omega
  have hd : D<17 := by dsimp [D,cap]; split <;> omega
  have h8 : 8≤D ↔ 8≤d := by dsimp [D,cap]; split <;> omega
  have h1 : 1≤X ↔ 1≤x := by dsimp [X,cap]; split <;> omega
  have h (i j : ℕ) : digit (X+i) (D+j) = digit (x+i) (d+j) := by
    unfold digit label
    have a : cap 6 ((X+i:ℕ):ℤ) = cap 6 ((x+i:ℕ):ℤ) := by
      dsimp [X,cap]; split_ifs <;> omega
    have b : shiftCap (-1) 12 ((D+j:ℕ):ℤ) = shiftCap (-1) 12 ((d+j:ℕ):ℤ) := by
      dsimp [D,shiftCap,cap]; split_ifs <;> omega
    rw [a,b]
  have h00 := h 0 0
  have h02 := h 0 2
  have h40 := h 4 0
  simp only [Nat.add_zero] at h00 h02 h40
  have hc := axis_cert ⟨X,hx⟩ ⟨D,hd⟩
  change digit X D < 2 ∧ (8≤D → digit X (D+2) = digit X D) ∧
    (1≤X → digit (X+4) D = digit X D) at hc
  simpa only [h00,h02,h40,h8,h1] using hc

private theorem cell_digit (x d : ℕ) : (cell 489 (x+d) (-(x:ℤ)) 0).toNat = digit x d := by
  have hv := invariant (x+d) (-(x:ℤ)) 0
  simp [abs_of_nonneg, allows] at hv
  have hh := (axis_prop x d).1
  unfold digit at *
  omega

private def value (x : ℕ) : ℕ → ℤ
  | 0 => digit x 0
  | d+1 => digit x (d+1) + 10 * value (x+1) d

private theorem val_period (x d : ℕ) (hx : 1 ≤ x) : value (x+4) d = value x d := by
  induction d generalizing x with
  | zero => exact (axis_prop x 0).2.2 hx
  | succ d ih =>
    rw [value, value, (axis_prop x (d+1)).2.2 hx, show x+4+1=x+1+4 by omega, ih (x+1) (by omega)]

private theorem residual_formula (d : ℕ) :
    value 0 (d+1+4) - 10000 * value 0 (d+1) =
      digit 0 (d+5) + 10 * digit 1 (d+4) + 100 * digit 2 (d+3) +
        1000 * digit 3 (d+2) + 10000 * (digit 4 (d+1) - digit 0 (d+1)) := by
  change digit 0 (d+5) + 10 * (digit 1 (d+4) + 10 * (digit 2 (d+3) +
    10 * (digit 3 (d+2) + 10 * (digit 4 (d+1) + 10 * value 5 d)))) -
    10000 * (digit 0 (d+1) + 10 * value 1 d) = _
  rw [val_period 1 d (by omega)]
  ring

private theorem residual_period (d : ℕ) (hd : 8 ≤ d) :
    value 0 (d+2+4) - 10000 * value 0 (d+2) =
      value 0 (d+4) - 10000 * value 0 d := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
  change value 0 ((e+2)+1+4) - 10000 * value 0 ((e+2)+1) =
    value 0 (e+1+4) - 10000 * value 0 (e+1)
  rw [residual_formula (e+2), residual_formula e]
  have time (x k : ℕ) (hk : 8 ≤ k) := (axis_prop x k).2.1 hk
  simp only [show ∀ k : ℕ, e+2+k=e+k+2 by intro k; omega,
    time 0 (e+5) (by omega), time 1 (e+4) (by omega), time 2 (e+3) (by omega),
    time 3 (e+2) (by omega), time 4 (e+1) (by omega), time 0 (e+1) (by omega)]

private theorem sum_value (x d : ℕ) :
    (∑ i ∈ Finset.range (d+1), digit (x+i) (d-i) * (10:ℤ)^i) = value x d := by
  induction d generalizing x with
  | zero => simp [value]
  | succ d ih =>
    rw [Finset.sum_range_succ', value, ← ih, Finset.mul_sum, add_comm]
    simp only [Nat.add_zero, Nat.sub_zero, pow_zero, mul_one, Nat.succ_sub_succ_eq_sub]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [show x+(i+1)=x+1+i by omega, pow_succ]
    ring

private theorem a_value (n : ℕ) : a n = value 0 n := by
  unfold a
  rw [← sum_value]
  calc
    _ = ∑ k ∈ Finset.range (n+1),
        if cell 489 n (-((n-k:ℕ):ℤ)) 0 then (10:ℤ)^(n-k) else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      have h : (k:ℤ) - n = -((n-k:ℕ):ℤ) := by
        have := Finset.mem_range.mp hk
        omega
      rw [h]
    _ = ∑ i ∈ Finset.range (n+1), if cell 489 n (-(i:ℤ)) 0 then (10:ℤ)^i else 0 := by
      simpa only [Nat.add_sub_cancel] using
        Finset.sum_range_reflect (fun i => if cell 489 n (-(i:ℤ)) 0 then (10:ℤ)^i else 0) (n+1)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      have h := cell_digit i (n-i)
      rw [show i+(n-i)=n by have := Finset.mem_range.mp hi; omega] at h
      simp only [Nat.zero_add, ← h]
      cases cell 489 n (-(i:ℤ)) 0 <;> simp

private theorem rec_int (n : ℕ) (hn : 14 ≤ n) :
    a n = a (n-2) + 10000*a (n-4) - 10000*a (n-6) := by
  have h := residual_period (n-6) (by omega)
  rw [show n-6+2+4=n by omega, show n-6+2=n-4 by omega, show n-6+4=n-2 by omega] at h
  simp only [← a_value] at h
  linarith

private theorem rec_rat (n : ℕ) (hn : 14 ≤ n) :
    (a n:ℚ) = a (n-2) + 10000*a (n-4) - 10000*a (n-6) := by
  exact_mod_cast rec_int n hn

open PowerSeries

private noncomputable def series : PowerSeries ℚ := mk fun n => (a n : ℚ)

private theorem shifted (n k : ℕ) :
    coeff n (series * X^k) = if k ≤ n then (a (n-k):ℚ) else 0 := by
  simp only [coeff_mul_X_pow', series, coeff_mk]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem gf :
    series * (10000 * X ^ 6 - 10000 * X ^ 4 - X ^ 2 + 1) =
      C (10000:ℚ) * X ^ 13 - C (10010:ℚ) * X ^ 9 + C (990:ℚ) * X ^ 8 - C (100:ℚ) * X ^ 7 -
      C (1000:ℚ) * X ^ 6 + C (11010:ℚ) * X ^ 5 + C (900:ℚ) * X ^ 4 + C (100:ℚ) * X ^ 3 +
      C (110:ℚ) * X ^ 2 + 1 := by
  have expand : series * (10000 * X ^ 6 - 10000 * X ^ 4 - X ^ 2 + 1) =
      C (10000:ℚ) * (series * X^6) - C (10000:ℚ) * (series * X^4) - (series * X^2) + series := by
    simp only [map_ofNat]
    ring
  rw [expand]
  apply PowerSeries.ext
  intro n
  simp only [map_add, map_sub, coeff_C_mul, shifted, coeff_X_pow, coeff_one]
  simp only [series, coeff_mk]
  by_cases h : n < 14
  · simp only [a_value]
    interval_cases n <;> decide +kernel
  · have hrec := rec_rat n (by omega)
    simp only [if_pos (show 6 ≤ n by omega), if_pos (show 4 ≤ n by omega), if_pos (show 2 ≤ n by omega),
      if_neg (show n ≠ 13 by omega), if_neg (show n ≠ 9 by omega), if_neg (show n ≠ 8 by omega),
      if_neg (show n ≠ 7 by omega), if_neg (show n ≠ 6 by omega), if_neg (show n ≠ 5 by omega),
      if_neg (show n ≠ 4 by omega), if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 2 by omega),
      if_neg (show n ≠ 0 by omega), mul_zero, sub_zero, add_zero]
    linarith

end Rule489

theorem OMA.solution : type_of% @OMA.S_oeis_a282606.main := by
  refine ⟨Rule489.rec_rat, ?_⟩
  simpa only [map_ofNat, Rule489.series] using Rule489.gf
