import OMAStatements.S_oeis_a282263
import Mathlib

/-!
I prove Chai Wah Wu’s May 2024 recurrence and generating function for
the left horizontal binary word of the two-dimensional Rule 446 automaton.
A finite inductive certificate uses the same three-valued strip method as
my Rule 489 proof (https://github.com/lefttosolve2/open-math-agents/pull/29123).
The transition table, axial phases, reading direction and binary weights
are specific to Rule 446.

Source: https://oeis.org/A282263
Credit: @Aryan-Poonacha
-/

namespace Rule446
open OMA.S_oeis_a282263

private def cap (a x : ℤ) := if x ≤ a then x else a+1+(x-a-1)%8
private def shiftCap (a b d : ℤ) := if d < a then a-1-(a-1-d)%8 else cap b d

/-- 0 or 1 fixes the cell, 2 permits either state. The three coordinates are
the horizontal distance, the time minus that distance, and the vertical distance. -/
private def stripTable : Array Nat := #[2764673736127742537509684407739893149946080623813477552527971896797889994442680881553647996162335150110968131708820160801830617634649376584205621929977435619272025967011188128612352,2765991513774843811718984812929506613884141092472258364086807590880156095141766222944410888215562521694038882651885193971610991078660502324833232844390463946174897843016366076985344,2766319968846143424829266044552010162027842037023217056237200407687670734106192854623284264167924868676726536310196773056298270175434634443729450010421951455547624200470051191521280,2766319968846143424829266044552010162027842037023258862865494645374005356743343325787936247313202180976018785900910674443993229609724183501994243343957503502434388700556402349834240,2766244780332390246595747473396479911867510886196259093763459113436502444703541408051396376323240744055299371234591394262835806709810487435861372755746995521061078267341760066748416,2766244780332390246595747473396479911867510886196267411730729531820316764069020429390338876118077373498673332777731957555301801445403814885896786271208547421838977061960434870910976,2766323926136340960525767021981248596246806834435218953902175555705014691093806839559586425052244586081008220884860341868588654244981017916823204425284426556799737151104837310480384,2766319968846143424829266044552010162027842037023276365441642754683674175126165642397035288831452992851145021551595587911713567916757392155189943984647848000912654839737132318195712,2766319968846143424829266044552010162027842037023276322118678945397195809381611186556926968979086919424714851633682999566209626603733056439659938523487089607094552638863724431540224,2766339755297131103311770931698202333122666024083010774290337614338687578495825664900809774865921364102078036418174687530618745164647067948366999092618597988955029360419738289700864,2766319968846143424829266044552010162027842037023275975534306124838777202517815570500092157656682925351474872026750691965416888277444221230962884633570750691061064498197009306484736,2766319968846143424829266044552010162027842037023275498981495706600425567457930752802938309735799732105817139533803034073148872836505959350976802503462223883567661758406471001833472,2766244780332390246595747473396479911867510886196284741014980607333144078036614270954738503646261759470058977365347201577182187713940009191954825279854773324715108800353208994103296,2766244780332390246595747473396479911867510886196284047846730585481551785075867847647765239313101074053161746481258556938385111057007010607414908039174146865068447084937929384001536,2766323926136340960525767021981248596246806834435223112910683176130919429278327040674440864036195151557356640416991541746709107235426770290231009684508944481817752017812186292289536]

private def label (x d y : ℤ) : Nat :=
  ((stripTable[(cap 6 x).toNat]?.getD 0) >>> (2*((shiftCap (-1) 12 d+9).toNat*10+(min 9 y).toNat))) % 4 % 3

private def allows (v : Nat) (b : Bool) : Prop := v=2 ∨ v=b.toNat
private instance (v : Nat) (b : Bool) : Decidable (allows v b) := inferInstanceAs (Decidable (_ ∨ _))

private def nextCell (c l r u v : Bool) : Bool :=
  (446:ℕ).testBit (c.toNat + 2*(l.toNat+r.toNat+u.toNat+v.toNat))

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
  (133191556219099654397996627944086306414008205872563467930688055374891009205958653307000778241369485480542900330988869598333581249946121860057294180 >>> (2*(a+3*(b+3*(c+3*(d+3*e)))))) % 4

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
  ∀ x : Fin 16, ∀ b : Fin 32, ∀ y : Fin 11,
    x.val≠0 ∨ b.val≠9 → stepTest (x:ℕ) ((b:ℕ)-10:ℤ) (y:ℕ)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
private theorem boxCheck : validBox := by unfold validBox; decide +kernel

private theorem certificate (x : Fin 16) (b : Fin 32) (y : Fin 11)
    (h : x.val≠0 ∨ b.val≠9) : stepOK (x:ℕ) ((b:ℕ)-10:ℤ) (y:ℕ) := by
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
    min 9 (min 10 y+s) = min 9 (y+s) := by omega

private theorem loc (x d y a b c : ℤ) (ha : -1≤a ∧ a≤1) (hb : -1≤b ∧ b≤1)
    (hc : -1≤c ∧ c≤1) :
    label (cap 7 x+a) (shiftCap (-2) 13 d+b) (min 10 y+c) =
      label (x+a) (d+b) (y+c) := by
  unfold label; rw [cap_step x a ha,dcap_step d b hb,height_step y c hc]

private theorem local_step {x y d : ℤ} (hx : 0≤x) (hy : 0≤y) (ht : 0≤x+d) :
    stepOK x d y := by
  let X := cap 7 x
  let D := shiftCap (-2) 13 d
  let Y := min 10 y
  have hX : 0≤X ∧ X<16 := by dsimp [X,cap]; split <;> omega
  have hD : -10≤D ∧ D<22 := by dsimp [D,shiftCap,cap]; split_ifs <;> omega
  have hY : 0≤Y ∧ Y<11 := by dsimp [Y]; omega
  have xzero : X=0 ↔ x=0 := by dsimp [X,cap]; split <;> omega
  have yzero : Y=0 ↔ y=0 := by dsimp [Y]; omega
  have dz : D=(-1) ↔ d=(-1) := by dsimp [D,shiftCap,cap]; split_ifs <;> omega
  have hcert := certificate ⟨X.toNat,by omega⟩ ⟨(D+10).toNat,by omega⟩ ⟨Y.toNat,by omega⟩ (by change X.toNat≠0 ∨ (D+10).toNat≠9; omega)
  simp only [Int.toNat_of_nonneg hX.1, Int.toNat_of_nonneg hY.1,
    Int.toNat_of_nonneg (show 0≤D+10 by omega),add_sub_cancel_right] at hcert
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

end Rule446
namespace Rule446
open OMA.S_oeis_a282263

private def initialBox : Prop :=
  ∀ X : Fin 16, ∀ b : Fin 32, ∀ Y : Fin 11,
    ((X:ℕ)=0 ∧ (b:ℕ)=10 ∨ 0<(X:ℕ) ∧ (b:ℕ)<10 ∧ ((X:ℕ)+(b:ℕ))%2=0) →
    allows (label (X:ℕ) ((b:ℕ)-10:ℤ) (Y:ℕ)) (decide ((X:ℕ)=0 ∧ (Y:ℕ)=0))

set_option maxRecDepth 30000 in
set_option maxHeartbeats 2000000 in
private theorem initial_cert : initialBox := by unfold initialBox; decide +kernel

set_option maxRecDepth 10000 in
private theorem initial_spec (x y : ℤ) (hx : 0≤x) (hy : 0≤y) :
    allows (label x (-x) y) (decide (x=0 ∧ y=0)) := by
  let X := cap 7 x
  let D := shiftCap (-2) 13 (-x)
  let Y := min 10 y
  have hX : 0≤X ∧ X<16 := by dsimp [X,cap]; split <;> omega
  have hD : -10≤D ∧ D<22 := by dsimp [D,shiftCap,cap]; split_ifs <;> omega
  have hY : 0≤Y ∧ Y<11 := by dsimp [Y]; omega
  have xzero : X=0 ↔ x=0 := by dsimp [X,cap]; split <;> omega
  have yzero : Y=0 ↔ y=0 := by dsimp [Y]; omega
  have hcon : X=0 ∧ D=0 ∨ 0<X ∧ D<0 ∧ (X+D+10)%2=0 := by
    dsimp [X,D,cap,shiftCap]; split_ifs <;> omega
  have hc := initial_cert ⟨X.toNat,by omega⟩ ⟨(D+10).toNat,by omega⟩ ⟨Y.toNat,by omega⟩ (by
    change X.toNat=0 ∧ (D+10).toNat=10 ∨ 0<X.toNat ∧ (D+10).toNat<10 ∧ (X.toNat+(D+10).toNat)%2=0
    omega)
  have he := loc x (-x) y 0 0 0 (by decide) (by decide) (by decide)
  simp only [add_zero] at he
  change label X D Y = label x (-x) y at he
  have hz : X.toNat=0 ↔ x=0 := by omega
  have hzy : Y.toNat=0 ↔ y=0 := by omega
  simpa only [Int.toNat_of_nonneg hX.1,Int.toNat_of_nonneg hY.1,
    Int.toNat_of_nonneg (show 0≤D+10 by omega),add_sub_cancel_right,he,hz,hzy] using hc

private def back (z : ℤ) := if z<0 then z+1 else z-1
private def away (z : ℤ) := if z<0 then z-1 else z+1
private theorem near_abs (z : ℤ) : |back z|=near |z| := by
  unfold back near; simp only [abs_eq_max_neg]; split_ifs <;> omega
private theorem away_abs (z : ℤ) : |away z|=|z|+1 := by
  unfold away; simp only [abs_eq_max_neg]; split_ifs <;> omega
private theorem near_offset (z : ℤ) : near |z|=|z|-delta |z| := by
  unfold near delta; split_ifs <;> omega

private theorem cell_step (t : ℕ) (i j : ℤ) :
    cell 446 (t+1) i j = nextCell (cell 446 t i j) (cell 446 t (back i) j)
      (cell 446 t (away i) j) (cell 446 t i (back j)) (cell 446 t i (away j)) := by
  simp only [cell,nextCell,back,away]
  split_ifs <;> congr 3 <;> omega

private theorem invariant (t : ℕ) (i j : ℤ) :
    allows (label |i| ((t:ℤ)-|i|) |j|) (cell 446 t i j) := by
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

end Rule446
namespace Rule446
open OMA.S_oeis_a282263

private def digit (x d : ℕ) : ℤ := label x d 0
private def axisBox : Prop := ∀ x : Fin 15, ∀ d : Fin 21,
    digit x d < 2 ∧ (11≤(d:ℕ) → digit x (d+2:ℕ) = digit x d) ∧
      (1≤(x:ℕ) → digit (x+8:ℕ) d = digit x d)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem axis_cert : axisBox := by unfold axisBox; decide +kernel

private theorem axis_prop (x d : ℕ) :
    digit x d < 2 ∧ (11≤d → digit x (d+2) = digit x d) ∧
      (1≤x → digit (x+8) d = digit x d) := by
  let X := (cap 6 (x:ℤ)).toNat
  let D := (cap 12 (d:ℤ)).toNat
  have hx : X<15 := by dsimp [X,cap]; split <;> omega
  have hd : D<21 := by dsimp [D,cap]; split <;> omega
  have h11 : 11≤D ↔ 11≤d := by dsimp [D,cap]; split <;> omega
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
  have h80 := h 8 0
  simp only [Nat.add_zero] at h00 h02 h80
  have hc := axis_cert ⟨X,hx⟩ ⟨D,hd⟩
  change digit X D < 2 ∧ (11≤D → digit X (D+2) = digit X D) ∧
    (1≤X → digit (X+8) D = digit X D) at hc
  simpa only [h00,h02,h80,h11,h1] using hc


private theorem cell_digit (x d : ℕ) : (cell 446 (x+d) (-(x:ℤ)) 0).toNat = digit x d := by
  have hv := invariant (x+d) (-(x:ℤ)) 0
  simp [abs_of_nonneg,allows] at hv
  have hh := (axis_prop x d).1
  unfold digit at *
  omega

private def value (x : ℕ) : ℕ → ℤ
  | 0 => digit x 0
  | d+1 => digit x (d+1) + 2*value (x+1) d

private theorem sum_value (x d : ℕ) :
    (∑ i ∈ Finset.range (d+1), digit (x+i) (d-i)*(2:ℤ)^i) = value x d := by
  induction d generalizing x with
  | zero => simp [value]
  | succ d ih =>
    rw [Finset.sum_range_succ',value,add_comm,← ih,Finset.mul_sum]
    simp only [Nat.add_zero,Nat.sub_zero,pow_zero,mul_one]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [show x+(i+1)=x+1+i by omega,Nat.succ_sub_succ_eq_sub,pow_succ]
    ring

private theorem a_value (n : ℕ) : a n = value 0 n := by
  unfold a
  rw [← sum_value]
  have reflection := Finset.sum_range_reflect (fun i : ℕ => digit i (n-i)*(2:ℤ)^i) (n+1)
  simp only [Nat.add_sub_cancel,Nat.zero_add] at reflection ⊢
  rw [← reflection]
  apply Finset.sum_congr rfl
  intro i hi
  have hle : i ≤ n := by simpa using hi
  have h := cell_digit (n-i) i
  rw [Nat.sub_add_cancel hle] at h
  rw [show n-(n-i)=i by omega, ← h, show (i:ℤ)-n = -((n-i : ℕ):ℤ) by omega]
  cases cell 446 n (-((n-i : ℕ):ℤ)) 0 <;> simp

private theorem val_period (x d : ℕ) (hx : 1≤x) : value (x+8) d = value x d := by
  induction d generalizing x with
  | zero => exact (axis_prop x 0).2.2 hx
  | succ d ih =>
    rw [value,value,(axis_prop x (d+1)).2.2 hx,show x+8+1=x+1+8 by omega,ih (x+1) (by omega)]

private def diff (x d : ℕ) : ℤ := value x (d+2) - value x d
private theorem diff_skip (x d : ℕ) (h : 10≤d) : diff x (d+1) = 2*diff (x+1) d := by
  unfold diff
  rw [show d+1+2=(d+2)+1 by omega,
      show value x ((d+2)+1) = digit x ((d+2)+1)+2*value (x+1) (d+2) from rfl,
      show value x (d+1) = digit x (d+1)+2*value (x+1) d from rfl,
      (axis_prop x (d+1)).2.1 (by omega)]
  ring

private theorem shifts (j x m : ℕ) :
    diff x (j+11+m) = 2^m * diff (x+m) (j+11) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [show j+11+(m+1)=j+11+m+1 by omega,diff_skip _ _ (by omega),ih,pow_succ,
      show x+1+m=x+(m+1) by omega]
    ring

set_option maxRecDepth 10000 in
private theorem rec_nat (n : ℕ) (hn : 18≤n) :
    a n = a (n-2)+256*a (n-8)-256*a (n-10) := by
  by_cases hlt : n<22
  · simp only [a_value]
    interval_cases n <;> decide +kernel
  have hn' : 22≤n := by omega
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hn'
  have h1 := shifts j 0 9
  have h2 := shifts j 0 1
  have he : diff 9 (j+11) = diff 1 (j+11) := by
    unfold diff; rw [val_period 1 _ (by omega), val_period 1 _ (by omega)]
  change diff 0 (j+20) = _ * diff 9 (j+11) at h1
  change diff 0 (j+12) = _ * diff 1 (j+11) at h2
  rw [he] at h1
  have hh : diff 0 (j+20) = 256 * diff 0 (j+12) := by rw [h1,h2]; ring
  unfold diff at hh
  simp only [a_value]
  rw [show 22+j=j+20+2 by omega,show j+20+2-2=j+20 by omega,
      show j+20+2-8=j+12+2 by omega,show j+20+2-10=j+12 by omega]
  linarith

end Rule446
namespace Rule446
open OMA.S_oeis_a282263 PowerSeries
private noncomputable def series : PowerSeries ℚ := mk fun n => (a n : ℚ)
private theorem shifted (n k : ℕ) :
    coeff n (series * X^k) = if k≤n then (a (n-k):ℚ) else 0 := by
  simp only [coeff_mul_X_pow',series,coeff_mk]

private theorem rec_rat (n : ℕ) (hn : 18≤n) :
    (a n:ℚ) = a (n-2)+256*a (n-8)-256*a (n-10) := by exact_mod_cast rec_nat n hn

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private theorem gf :
    series * (256*X^10-256*X^8-X^2+1) =
    C (32:ℚ)*X^17 - C (256:ℚ)*X^15 + C (96:ℚ)*X^14 - C (172:ℚ)*X^13 - C (152:ℚ)*X^12 + C (124:ℚ)*X^11 + C (40:ℚ)*X^10 - C (124:ℚ)*X^9 + C (24:ℚ)*X^8 + C (199:ℚ)*X^7 + C (82:ℚ)*X^6 + C (41:ℚ)*X^5 + C (18:ℚ)*X^4 + C (12:ℚ)*X^3 + C (5:ℚ)*X^2 + C (3:ℚ)*X^1 + 1 := by
  have expand : series * (256*X^10-256*X^8-X^2+1) =
      C (256:ℚ)*(series*X^10) - C (256:ℚ)*(series*X^8) - (series*X^2) + series := by
    simp only [map_ofNat]; ring
  rw [expand]
  apply PowerSeries.ext
  intro n
  simp only [map_add,map_sub,coeff_C_mul,shifted,coeff_X_pow,coeff_one]
  simp only [series,coeff_mk]
  by_cases h : n<18
  · simp only [a_value]
    interval_cases n <;> decide +kernel
  · have hh := rec_rat n (by omega)
    simp only [if_pos (show 10≤n by omega), if_pos (show 8≤n by omega), if_pos (show 2≤n by omega), if_neg (show n≠17 by omega), if_neg (show n≠15 by omega), if_neg (show n≠14 by omega), if_neg (show n≠13 by omega), if_neg (show n≠12 by omega), if_neg (show n≠11 by omega), if_neg (show n≠10 by omega), if_neg (show n≠9 by omega), if_neg (show n≠8 by omega), if_neg (show n≠7 by omega), if_neg (show n≠6 by omega), if_neg (show n≠5 by omega), if_neg (show n≠4 by omega), if_neg (show n≠3 by omega), if_neg (show n≠2 by omega), if_neg (show n≠1 by omega), if_neg (show n≠0 by omega), mul_zero, sub_zero, add_zero]
    linarith

end Rule446

theorem OMA.solution : type_of% @OMA.S_oeis_a282263.main := by
  refine ⟨Rule446.rec_rat,?_⟩
  simpa only [map_ofNat,pow_one,Rule446.series] using Rule446.gf
