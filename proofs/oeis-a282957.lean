import OMAStatements.S_oeis_a282957
import Mathlib

/-!
I prove Chai Wah Wu’s May 2024 recurrence and rational generating function
for the horizontal binary word of Rule 533 (https://oeis.org/A282957).
The invariant folds each configuration into the wedge x ≥ y ≥ 0. Its finite
table indexes the distance from the diagonal, the distance from the axis,
and the number of time steps elapsed since the light cone reached the cell.
Unknown cells may carry either bit. On a symmetry line the neighbors shared
by reflection carry the same bit. The kernel verifies all allowed updates.
Credit: @Aryan-Poonacha
-/
namespace Rule533
open OMA.S_oeis_a282957

private def cap (a x : ℤ) := if x ≤ a then x else a+1+(x-a-1)%4
private def table : Array Nat := #[3103908012996919220621484959503193833725113809342100452835730741793762932373850880917110440933841609605292107136967612112780069645364178909278668015031608186307617363370170049562660636648172441666,3103672649843856123726299170967502177556412352601220363397652724965010921134043444589146534675932771196145113382243930038714143661805557296725991497604673120539610729338409320006901024353086932033,3103676269995233910509274451692557172565884044080091851042359654587676764370349181235112188021204748678131542988598854727283691630103422687371288182273236529342750502552932088501991380918017790017,3103690528441590396734055464692658698808898052559545498879727718643515305634479170599007192492070880283278127784444576416364803884439218075573901150570479685801647101853341771089292782525396042817,3107311756010444613680273265164008431633809974583598906658138271913303410573071841667927183336682783001202114656109981651590935767470167429381956469831797297579098409255468884286444239246230573121,3103676048039239545850500696043824017973153365325152618990262443784192842461382298743871191973821586863255315896069514405637116922864281743513430356253168185112289684829539631498333065863775716417,3107326236412795469629154655982023970028646292302763741353736263500857659040960556250689179841305960699346577167398842115400721570075749297883861042301347622263257815642982575261864473387450044481,3114458378405104504918926874680879288115088308234960808023479012126528359551333107040566754642622160315813923024973295414875092780753336649519621073901852021191102705236140723550537755553771570241,3112744134646221827211090040589174468578925561764640619792465531778329594669606740211899065241973137655794504087889996331306096132880883114932022063045490731965321238011173382126746297972141609025,3107329564940069818558141766335490887328834921588943557378946287342481987020184593835530475546059323806910116252916370959751231354246080069017925739735416293446796225903939922466594656332360516673,3112744134646221827211090040589174468578925561764640619792465531778329594669604218483502495995303551797228092876230823313236325042787436479043441390725070659651460217216741992800304977004595318849]
private def label (u v e : ℤ) : ℕ :=
  if e<0 then 1 else
    (((table[(cap 6 u).toNat]?.getD 0) >>> (2*((cap 8 v).toNat*25+(cap 20 e).toNat))) % 4 % 3)

private def allows (a : ℕ) (b : Bool) : Prop := a=2  ∨  a=b.toNat
private instance (a : ℕ) (b : Bool) : Decidable (allows a b) := inferInstanceAs (Decidable (_  ∨  _))
private def out (c l r b h : Bool) :=
  (533:ℕ).testBit (c.toNat+2*(l.toNat+r.toNat+b.toNat+h.toNat))
private def tag (u v : ℤ) : ℕ := if u=0 then (if v=0 then 3 else 2) else if v=0 then 1 else 0
private def upd (z : ℕ) (c l r b h : Bool) : Bool :=
  if z=3 then out c r r r r else if z=2 then out c b r b r else
    if z=1 then out c l r h h else out c l r b h
private def tables : Array Nat := #[133188507624716962499699643609092704097580872737436994349614972339458395005878703234100208714937617900539701581830588821670933101245302747445991521,133188507624716962499699664267091806954993451201962986190518714801892159078940463411353520231122385679943466951993043541498727038274884461438310497,133194604813067000376110264253927031904569545672369251453011340827888818455634564918594386353123345916281213907610097248170756043150302148213217377,133194532228044637319623746436254368927567744212075381115264820328780515923852367640673975685354056677756254820560235436632418811086837121989875809]
private def transfer (z a b c d e : ℕ) : ℕ :=
  ((tables[z]?.getD 0) >>> (2*(a+3*(b+3*(c+3*(d+3*e)))))) % 4
private def boolForall (p : Bool → Prop) (hp : DecidablePred p) : Decidable (∀ b, p b) :=
  letI := hp
  decidable_of_iff (p false ∧ p true) ⟨fun h b => by cases b <;> tauto, fun h => ⟨h _, h _⟩⟩
private def transferSpec (z : Fin 4) (a b c d e : Fin 3) : Prop := ∀ p q r s t : Bool,
  allows a p → allows b q → allows c r → allows d s → allows e t →
  allows (transfer z a b c d e) (upd z p q r s t)
private instance (z : Fin 4) (a b c d e : Fin 3) : Decidable (transferSpec z a b c d e) := by
  unfold transferSpec
  apply @boolForall; intro p
  apply @boolForall; intro q
  apply @boolForall; intro r
  apply @boolForall; intro s
  apply @boolForall; intro t
  infer_instance

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem transfer_ok : ∀ z : Fin 4, ∀ a b c d e : Fin 3, transferSpec z a b c d e := by
  decide +kernel

private def ok (u v e : ℤ) : Prop :=
  label u v (e+1)=2  ∨  label u v (e+1) =
  transfer (tag u v) (label u v e) (label (u-1) v (e+1)) (label (u+1) v (e-1))
    (label (u+1) (v-1) (e+1)) (label (u-1) (v+1) (e-1))
private instance (u v e : ℤ) : Decidable (ok u v e) := inferInstanceAs (Decidable (_  ∨  _))
private def box := ∀ u : Fin 12, ∀ v : Fin 14, ∀ e : Fin 28,
  (e:ℕ)<1  ∨  (1:ℤ) ≤ (u:ℕ)+2*(v:ℕ)+((e:ℕ)-2) →
    ok (u:ℕ) (v:ℕ) ((e:ℕ)-2)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
private theorem box_ok : box := by unfold box; decide +kernel

private theorem cap_step (a x s : ℤ) (hs : -1 ≤ s ∧ s ≤ 1) :
    cap a (cap (a+1) x+s)=cap a (x+s) := by unfold cap; split_ifs <;> omega
private theorem loc (u v e i j k : ℤ) (hi : -1 ≤ i ∧ i ≤ 1) (hj : -1 ≤ j ∧ j ≤ 1) (hk : -1 ≤ k ∧ k ≤ 1) :
    label (cap 7 u+i) (cap 9 v+j) (max (-2) (cap 21 e)+k) = label (u+i) (v+j) (e+k) := by
  unfold label
  have hu := cap_step 6 u i hi
  have hv := cap_step 8 v j hj
  have he := cap_step 20 e k hk
  change cap 6 (cap 7 u+i) = _ at hu
  change cap 8 (cap 9 v+j) = _ at hv
  change cap 20 (cap 21 e+k) = _ at he
  rw [hu,hv]
  by_cases h : e < -2
  · have hh : cap 21 e=e := if_pos (by omega)
    rw [hh,max_eq_left (by omega)]
    simp [show (-2:ℤ)+k<0 by omega,show e+k<0 by omega]
  · have hl : -2 ≤ cap 21 e := by unfold cap; split <;> omega
    rw [max_eq_right hl]
    by_cases hn : e+k<0
    · have : cap 21 e+k<0 := by unfold cap; split <;> omega
      simp [hn,this]
    · have : ¬ cap 21 e+k<0 := by unfold cap; split <;> omega
      simp [hn,this,he]

private theorem local_ok (u v e : ℤ) (hu : 0 ≤ u) (hv : 0 ≤ v) (ht : 1 ≤ u+2*v+e) : ok u v e := by
  let U := cap 7 u
  let V := cap 9 v
  let E := max (-2) (cap 21 e)
  have hU : 0 ≤ U ∧ U<12 := by dsimp [U,cap]; split <;> omega
  have hV : 0 ≤ V ∧ V<14 := by dsimp [V,cap]; split <;> omega
  have hE : -2 ≤ E ∧ E<26 := by dsimp [E,cap]; split <;> omega
  have hc := box_ok ⟨U.toNat,by omega⟩ ⟨V.toNat,by omega⟩ ⟨(E+2).toNat,by omega⟩ (by
    change (E+2).toNat<1  ∨  1 ≤ (U.toNat:ℤ)+2*V.toNat+((E+2).toNat-2)
    dsimp [U,V,E,cap]; split_ifs <;> omega)
  have htag : tag U V = tag u v := by dsimp [U,V,cap,tag]; split_ifs <;> omega
  simp only [Int.toNat_of_nonneg hU.1, Int.toNat_of_nonneg hV.1,Int.toNat_of_nonneg (show 0 ≤ E+2 by omega),add_sub_cancel_right] at hc
  have h (i j k : ℤ) (hi : -1 ≤ i ∧ i ≤ 1) (hj : -1 ≤ j ∧ j ≤ 1) (hk : -1 ≤ k ∧ k ≤ 1) :
    label (U+i) (V+j) (E+k)=label (u+i) (v+j) (e+k) := loc u v e i j k hi hj hk
  have c := h 0 0 0 (by decide) (by decide) (by decide)
  have l := h (-1) 0 1 (by decide) (by decide) (by decide)
  have r := h 1 0 (-1) (by decide) (by decide) (by decide)
  have b := h 1 (-1) 1 (by decide) (by decide) (by decide)
  have a := h (-1) 1 (-1) (by decide) (by decide) (by decide)
  have f := h 0 0 1 (by decide) (by decide) (by decide)
  simp only [add_zero,←sub_eq_add_neg] at c l r b a f
  unfold ok at *
  simpa only [htag,c,l,r,b,a,f] using hc

private theorem swap (t : ℕ) (i j : ℤ) : cell 533 t i j=cell 533 t j i := by
  induction t generalizing i j with
  | zero => simp [cell,and_comm]
  | succ t ih =>
    simp only [cell]
    rw [ih i j,ih (i+1) j,ih (i-1) j,ih i (j+1),ih i (j-1)]
    congr 3 <;> omega

private theorem reflectY (t : ℕ) (i j : ℤ) : cell 533 t i (-j)=cell 533 t i j := by
  induction t generalizing i j with
  | zero => simp [cell]
  | succ t ih =>
    simp only [cell]
    rw [show -j+1=-(j-1) by omega,show -j-1=-(j+1) by omega,ih i j,ih (i+1) j,ih (i-1) j, ih i (j-1),ih i (j+1)]
    congr 3 <;> omega

private def state (t : ℕ) (u v : ℤ) : Bool :=
  if u<0  ∨  v<0 then decide (label u v ((t:ℤ)-u-2*v)=1) else cell 533 t (u+v) v

private theorem state_step (t : ℕ) (u v : ℤ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    state (t+1) u v = upd (tag u v) (state t u v) (state t (u-1) v)
      (state t (u+1) v) (state t (u+1) (v-1)) (state t (u-1) (v+1)) := by
  by_cases uz : u=0 <;> by_cases vz : v=0
  · subst u; subst v
    have sr := reflectY t 0 1
    have hs := swap t (-1) 0
    have hr := swap t 0 1
    simp (disch := omega) [state,tag,upd,out,cell,hs,sr,hr]
  · subst u
    have hl := swap t (v-1) v
    have hr := swap t v (v+1)
    simp (disch := omega) [state,tag,upd,out,cell,vz,show 1+v=v+1 by omega,show 1+(v-1)=v by omega,hl,hr]
    split_ifs <;> first | omega | (congr 1 <;> omega)
  · subst v
    have hr := reflectY t u 1
    simp (disch := omega) [state,tag,upd,out,cell,uz,hr]
    split_ifs <;> first | omega | (congr 1 <;> omega)
  · simp (disch := omega) [state,tag,upd,out,cell,uz,vz,show u-1+v=u+v-1 by omega,
      show u+1+v=u+v+1 by omega,show u+1+(v-1)=u+v by omega,show u-1+(v+1)=u+v by omega]
    split_ifs <;> first | omega | (congr 1 <;> omega)

private theorem bound (u v e : ℤ) : label u v e<3 := by
  unfold label
  split
  · decide
  · exact Nat.mod_lt _ (by decide)

private theorem dummy (k : ℕ) (h : k<3) : allows k (decide (k=1)) := by
  interval_cases k <;> decide

private theorem start (u v : ℤ) : allows (label u v (1-u-2*v)) (state 1 u v) := by
  by_cases h : u<0 ∨ v<0
  · simpa [state,h] using dummy _ (bound u v (1-u-2*v))
  have hu : 0≤u := by omega
  have hv : 0≤v := by omega
  by_cases hl : u+2*v≤1
  · have vz : v=0 := by omega
    subst v
    have : u≤1 := by omega
    interval_cases u <;> decide +kernel
  have guard : 1-u-2*v<0 := by omega
  rw [show label u v (1-u-2*v)=1 by simp only [label,if_pos guard],state,if_neg h]
  simp only [allows,cell,show ¬(u+v=0 ∧ v=0) by omega,
    show ¬(u+v+1=0 ∧ v=0) by omega,show ¬(u+v-1=0 ∧ v=0) by omega,
    show ¬(u+v=0 ∧ v+1=0) by omega, show ¬(u+v=0 ∧ v-1=0) by omega,decide_false]
  decide +kernel

private theorem invariant (n : ℕ) (u v : ℤ) :
    allows (label u v (((n+1:ℕ):ℤ)-u-2*v)) (state (n+1) u v) := by
  induction n generalizing u v with
  | zero => exact start u v
  | succ n ih =>
    by_cases hz : u<0 ∨ v<0
    · simpa [state,hz] using dummy _ (bound u v (((n+1+1:ℕ):ℤ)-u-2*v))
    let e : ℤ := ((n+1:ℕ):ℤ)-u-2*v
    have hu : 0≤u := by omega
    have hv : 0≤v := by omega
    have h1 : 1≤u+2*v+e := by dsimp [e]; omega
    have he : (((n+1+1:ℕ):ℤ)-u-2*v) = e+1 := by dsimp [e]; omega
    rw [he,state_step _ u v hu hv]
    obtain h | h := local_ok u v e hu hv h1
    · exact Or.inl h
    rw [h]
    have tl : ((n+1:ℕ):ℤ)-(u-1)-2*v=e+1 := by dsimp [e]; ring
    have tr : ((n+1:ℕ):ℤ)-(u+1)-2*v=e-1 := by dsimp [e]; ring
    have tb : ((n+1:ℕ):ℤ)-(u+1)-2*(v-1)=e+1 := by dsimp [e]; ring
    have th : ((n+1:ℕ):ℤ)-(u-1)-2*(v+1)=e-1 := by dsimp [e]; ring
    have hh : tag u v<4 := by unfold tag; split_ifs <;> decide
    apply transfer_ok ⟨_,hh⟩ ⟨_,bound u v e⟩ ⟨_,bound (u-1) v (e+1)⟩ ⟨_,bound (u+1) v (e-1)⟩
      ⟨_,bound (u+1) (v-1) (e+1)⟩ ⟨_,bound (u-1) (v+1) (e-1)⟩
    · exact ih u v
    · simpa only [tl] using ih (u-1) v
    · simpa only [tr] using ih (u+1) v
    · simpa only [tb] using ih (u+1) (v-1)
    · simpa only [th] using ih (u-1) (v+1)

private def digit (x d : ℕ) : ℤ :=
  if x=0 ∧ d=0 then 1 else label x 0 d

private def axisBox := ∀ x : Fin 11, ∀ d : Fin 25, digit x d<2
set_option maxRecDepth 20000 in
private theorem axis_box : axisBox := by unfold axisBox; decide +kernel

private theorem digit_bit (x d : ℕ) : digit x d<2 := by
  let X := cap 6 (x:ℤ)
  let D := cap 20 (d:ℤ)
  have hx : 0≤X ∧ X<11 := by dsimp [X,cap]; split <;> omega
  have hd : 0≤D ∧ D<25 := by dsimp [D,cap]; split <;> omega
  have h := axis_box ⟨X.toNat,by omega⟩ ⟨D.toNat,by omega⟩
  change digit X.toNat D.toNat<2 at h
  have hz : X.toNat=0 ↔ x=0 := by dsimp [X,cap]; split <;> omega
  have dz : D.toNat=0 ↔ d=0 := by dsimp [D,cap]; split <;> omega
  unfold digit label at *
  simp only [hz,dz,Int.toNat_of_nonneg hx.1,Int.toNat_of_nonneg hd.1,if_neg (by omega : ¬D<0),if_neg (by omega : ¬(d:ℤ)<0)] at *
  have xx : cap 6 X=X := by dsimp [X,cap]; split_ifs <;> omega
  have dd : cap 20 D=D := by dsimp [D,cap]; split_ifs <;> omega
  simpa only [xx,dd] using h

private theorem period_d (x d : ℕ) (hd : 21≤d) : digit x (d+4)=digit x d := by
  have he : cap 20 ((d+4:ℕ):ℤ)=cap 20 (d:ℤ) := by unfold cap; split_ifs <;> omega
  simp (disch := omega) only [digit,if_neg (show ¬ (x=0 ∧ d+4=0) by omega),if_neg (show ¬ (x=0 ∧ d=0) by omega),label,if_neg (show ¬ ((d+4:ℕ):ℤ)<0 by omega),if_neg (show ¬ (d:ℤ)<0 by omega),he]
private theorem period_x (x d : ℕ) (hx : 7≤x) : digit (x+4) d=digit x d := by
  have he : cap 6 ((x+4:ℕ):ℤ)=cap 6 (x:ℤ) := by unfold cap; split_ifs <;> omega
  simp only [digit,if_neg (show ¬ (x+4=0 ∧ d=0) by omega),if_neg (show ¬ (x=0 ∧ d=0) by omega),label,he]

private theorem cell_digit (x d : ℕ) : (cell 533 (x+d) x 0).toNat=digit x d := by
  by_cases hz : x=0 ∧ d=0
  · rcases hz with ⟨rfl,rfl⟩; decide +kernel
  have ht : 1≤x+d := by omega
  obtain ⟨k,he⟩ := Nat.exists_eq_add_of_le ht
  have h := invariant k (x:ℤ) 0
  simp only [state,if_neg (show ¬((x:ℤ)<0 ∨ (0:ℤ)<0) by omega),add_zero] at h
  rw [show k+1=x+d by omega] at h
  have hb := digit_bit x d
  unfold digit at hb ⊢
  rw [if_neg hz] at hb ⊢
  simp only [allows,Nat.cast_add,Nat.cast_zero,mul_zero,sub_zero,add_sub_cancel_left] at h
  omega
private def value (x : ℕ) : ℕ → ℤ
  | 0 => digit x 0
  | d+1 => digit x (d+1)*2^(d+1) + value (x+1) d

private theorem sum_value (x d : ℕ) :
    (∑ i ∈ Finset.range (d+1), digit (x+i) (d-i)*(2:ℤ)^(d-i)) = value x d := by
  induction d generalizing x with
  | zero => simp [value]
  | succ d ih =>
    rw [Finset.sum_range_succ',value,add_comm,← ih]
    simp only [Nat.add_zero,Nat.sub_zero,Nat.succ_sub_succ_eq_sub]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [show x+(i+1)=x+1+i by omega]

private theorem a_value (n : ℕ) : a n = value 0 n := by
  unfold a
  rw [← sum_value]
  apply Finset.sum_congr rfl
  intro i hi
  have h := cell_digit i (n-i)
  rw [show i+(n-i)=n by have := Finset.mem_range.mp hi; omega] at h
  simp only [Nat.zero_add,← h]
  cases cell 533 n i 0 <;> simp

private theorem val_period (x d : ℕ) (hx : 7≤x) : value (x+4) d = value x d := by
  induction d generalizing x with
  | zero => exact period_x x 0 hx
  | succ d ih =>
    rw [value,value,period_x x (d+1) hx,show x+4+1=x+1+4 by omega,ih (x+1) (by omega)]

private def diff (x d : ℕ) : ℤ := value x (d+4) - 16*value x d
private theorem diff_skip (x d : ℕ) (hd : 20≤d) : diff x (d+1) = diff (x+1) d := by
  unfold diff
  rw [show d+1+4=(d+4)+1 by omega,
    show value x ((d+4)+1) = digit x ((d+4)+1)*2^((d+4)+1)+value (x+1) (d+4) from rfl,
    show value x (d+1) = digit x (d+1)*2^(d+1)+value (x+1) d from rfl,
    period_d x (d+1) (by omega)]
  simp only [pow_succ]
  ring

private theorem shift (x j m : ℕ) : diff x (j+21+m)=diff (x+m) (j+21) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [show j+21+(m+1) = j+21+m+1 by omega,diff_skip _ _ (by omega),ih,show x+1+m=x+(m+1) by omega]

set_option maxRecDepth 20000 in
private theorem rec_nat (n : ℕ) (hn : 25≤n) : a n = 17*a (n-4)-16*a (n-8) := by
  by_cases hl : n<36
  · simp only [a_value]
    interval_cases n <;> decide +kernel
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (show 36≤n by omega)
  have h := shift 0 j 11
  have g := shift 0 j 7
  change diff 0 (j+32)=diff 11 (j+21) at h
  change diff 0 (j+28)=diff 7 (j+21) at g
  have eqd : diff 11 (j+21)=diff 7 (j+21) := by
    unfold diff
    rw [val_period 7 _ (by decide),val_period 7 _ (by decide)]
  rw [eqd,←g] at h
  unfold diff at h
  simp only [a_value]
  rw [show 36+j=j+32+4 by omega,show j+32+4-4=j+32 by omega,show j+32+4-8=j+28 by omega]
  change value 0 (j+32+4)-16*value 0 (j+32)=value 0 (j+32)-16*value 0 (j+28) at h
  linarith

end Rule533
namespace Rule533
open OMA.S_oeis_a282957 PowerSeries
private noncomputable def series : PowerSeries ℚ := mk fun n => (a n : ℚ)
private theorem shifted (n k : ℕ) :
    coeff n (series * X^k) = if k≤n then (a (n-k):ℚ) else 0 := by
  simp only [coeff_mul_X_pow',series,coeff_mk]

private theorem rec_rat (n : ℕ) (hn : 25≤n) :
    (a n:ℚ) = 17*a (n-4)-16*a (n-8) := by exact_mod_cast rec_nat n hn

set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
private theorem gf :
    series * (16*X^8-17*X^4+1) =
    -(C (98304:ℚ)*X^24) - C (81920:ℚ)*X^23 + C (65536:ℚ)*X^22 + C (24576:ℚ)*X^21 + C (122880:ℚ)*X^20 + C (65536:ℚ)*X^19 - C (65536:ℚ)*X^18 - C (28160:ℚ)*X^17 + C (5632:ℚ)*X^16 + C (4096:ℚ)*X^15 + C (3072:ℚ)*X^13 - C (1536:ℚ)*X^12 - C (1024:ℚ)*X^11 - C (256:ℚ)*X^10 + C (640:ℚ)*X^9 - C (32:ℚ)*X^8 - C (16:ℚ)*X^7 + C (88:ℚ)*X^6 - C (8:ℚ)*X^5 - C (8:ℚ)*X^4 + C (9:ℚ)*X^3 + C (1:ℚ)*X^2 + C (1:ℚ)*X^1 + 1 := by
  have expand : series * (16*X^8-17*X^4+1) = C (16:ℚ)*(series*X^8)-C (17:ℚ)*(series*X^4)+series := by
    simp only [map_ofNat]; ring
  rw [expand]
  apply PowerSeries.ext
  intro n
  simp only [map_add,map_sub,map_neg,coeff_C_mul,shifted,coeff_X_pow,coeff_one]
  simp only [series,coeff_mk]
  by_cases h : n<25
  · simp only [a_value]
    interval_cases n <;> decide +kernel
  · have hh := rec_rat n (by omega)
    simp only [if_pos (show 8≤n by omega), if_pos (show 4≤n by omega), if_neg (show n≠24 by omega), if_neg (show n≠23 by omega), if_neg (show n≠22 by omega), if_neg (show n≠21 by omega), if_neg (show n≠20 by omega), if_neg (show n≠19 by omega), if_neg (show n≠18 by omega), if_neg (show n≠17 by omega), if_neg (show n≠16 by omega), if_neg (show n≠15 by omega), if_neg (show n≠13 by omega), if_neg (show n≠12 by omega), if_neg (show n≠11 by omega), if_neg (show n≠10 by omega), if_neg (show n≠9 by omega), if_neg (show n≠8 by omega), if_neg (show n≠7 by omega), if_neg (show n≠6 by omega), if_neg (show n≠5 by omega), if_neg (show n≠4 by omega), if_neg (show n≠3 by omega), if_neg (show n≠2 by omega), if_neg (show n≠1 by omega), if_neg (show n≠0 by omega), mul_zero, neg_zero, sub_zero, add_zero]
    linarith

end Rule533

theorem OMA.solution : type_of% @OMA.S_oeis_a282957.main := by
  refine ⟨Rule533.rec_rat,?_⟩
  simpa only [map_ofNat,map_one,one_mul,pow_one,Rule533.series,neg_mul] using Rule533.gf
