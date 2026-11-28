import OMAStatements.S_oeis_a270166
import Mathlib

/-!
# Square shells in the two-dimensional Rule 107 automaton

We prove the cumulative formulas in https://oeis.org/A270166 by describing
the entire infinite configuration after time seven. On even steps the active
cells form a checkerboard square with the origin removed. On odd steps the
background is active and the finite complement splits into two square shells.
The two local transitions follow by lattice symmetries and the rule table.
Counting the checkerboards gives the two stage polynomials. Summation and
formal power-series coefficients yield the five conjectures.
-/

namespace Rule107

def radius (x y : ℤ) : ℤ := max |x| |y|

def E (h x y : ℤ) : Bool := decide
  (radius x y ≤ h ∧ (x+y)%2=0 ∧ 0 < radius x y)

def O (h x y : ℤ) : Bool := decide
  ((x+y)%2=0 ∨ radius x y ≤ 1 ∨ radius x y=h ∨ h+1<radius x y)

def step (f : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  (107 : ℕ).testBit ((f x y).toNat + 2*((f (x+1) y).toNat +
    (f (x-1) y).toNat + (f x (y+1)).toNat + (f x (y-1)).toNat))

end Rule107

namespace Rule107

theorem mirrorE (h x y : ℤ) : E h (-x) y = E h x y := by
  simp only [E,radius,abs_neg]
  congr 1
  apply propext
  omega
theorem mirrorO (h x y : ℤ) : O h (-x) y = O h x y := by
  simp only [O,radius,abs_neg]
  congr 1
  apply propext
  omega
theorem swapE (h x y : ℤ) : E h y x = E h x y := by
  simp [E,radius,max_comm,add_comm]
theorem swapO (h x y : ℤ) : O h y x = O h x y := by
  simp [O,radius,max_comm,add_comm]

theorem mirrorStep {f : ℤ → ℤ → Bool} (hm : ∀ x y, f (-x) y=f x y)
    (x y : ℤ) : step f (-x) y = step f x y := by
  simp only [step,show -x+1 = -(x-1) by omega, show -x-1 = -(x+1) by omega,hm]
  ac_rfl

theorem swapStep {f : ℤ → ℤ → Bool} (hs : ∀ x y, f y x=f x y)
    (x y : ℤ) : step f y x = step f x y := by
  unfold step
  rw [hs x y, hs x (y+1), hs x (y-1), hs (x+1) y, hs (x-1) y]
  ac_rfl

theorem quadrant {P : ℤ → ℤ → Prop}
    (sw : ∀ x y, P y x ↔ P x y) (neg : ∀ x y, P (-x) y ↔ P x y)
    (sector : ∀ x y, 0≤y → y≤x → P x y) (x y : ℤ) : P x y := by
  have pos (u v : ℤ) (hu : 0≤u) (hv : 0≤v) : P u v := by
    rcases le_total v u with h|h
    · exact sector u v hv h
    · exact (sw u v).mp (sector v u hu h)
  have left (u v : ℤ) (hv : 0≤v) : P u v := by
    by_cases hu : 0≤u
    · exact pos u v hu hv
    · exact (neg u v).mp (pos (-u) v (by omega) hv)
  by_cases hy : 0≤y
  · exact left x y hy
  · exact (sw x y).mp ((neg y x).mp ((sw (-y) x).mp (left x (-y) (by omega))))

private theorem front_sector {h x y : ℤ} (hh : 4≤h) (hhx : h≤x) (hy : 0≤y) (hyx : y≤x) :
    step (E h) x y = O h x y ∧ step (O h) x y = E (h+1) x y := by
  have hx : 0≤x := by omega
  have r0 : radius x y = x := by
    simp [radius,abs_of_nonneg hx,abs_of_nonneg hy,max_eq_left hyx]
  have rxp : radius (x+1) y = x+1 := by
    simp [radius,abs_of_nonneg (show 0≤x+1 by omega),abs_of_nonneg hy,max_eq_left (show y≤x+1 by omega)]
  have rym : radius x (y-1) = x := by
    simp only [radius,abs_of_nonneg hx]
    exact max_eq_left (abs_le.mpr (by omega))
  rcases lt_or_eq_of_le hyx with hs|hs
  · have rxm : radius (x-1) y = x-1 := by
      simp [radius,abs_of_nonneg (show 0≤x-1 by omega),abs_of_nonneg hy,max_eq_left (show y≤x-1 by omega)]
    have ryp : radius x (y+1) = x := by
      simp [radius,abs_of_nonneg hx,abs_of_nonneg (show 0≤y+1 by omega),max_eq_left (show y+1≤x by omega)]
    by_cases par : (x+y)%2=0 <;>
      rcases (show x=h ∨ x=h+1 ∨ x=h+2 ∨ h+3≤x by omega) with hh0|hh1|hh2|hh3 <;>
      simp (disch := omega) only [step,E,O,r0,rxp,rxm,ryp,rym,decide_eq_true,decide_eq_false] <;> decide
  · have rxm : radius (x-1) y = x := by
      simp [radius,abs_of_nonneg (show 0≤x-1 by omega),abs_of_nonneg hx,hs]
    have ryp : radius x (y+1) = x+1 := by
      simp [radius,abs_of_nonneg hx,abs_of_nonneg (show 0≤x+1 by omega),hs]
    rcases (show x=h ∨ x=h+1 ∨ x=h+2 ∨ h+3≤x by omega) with hh0|hh1|hh2|hh3 <;>
      simp (disch := omega) only [step,E,O,r0,rxp,rxm,ryp,rym,decide_eq_true,decide_eq_false] <;> decide

private theorem front_transitions {h x y : ℤ} (hh : 4≤h) (hm : h≤radius x y) :
    step (E h) x y = O h x y ∧ step (O h) x y = E (h+1) x y := by
  let P (u v : ℤ) := h≤radius u v →
    step (E h) u v = O h u v ∧ step (O h) u v = E (h+1) u v
  have sw (u v : ℤ) : P v u ↔ P u v := by
    simp only [P,swapStep (swapE h) u v,swapStep (swapO h) u v,swapO h u v,swapE (h+1) u v,
      radius,max_comm |v| |u|]
  have neg (u v : ℤ) : P (-u) v ↔ P u v := by
    simp only [P,mirrorStep (mirrorE h),mirrorStep (mirrorO h),mirrorE,mirrorO,radius,abs_neg]
  have sector (u v : ℤ) (hv : 0≤v) (hvu : v≤u) : P u v := by
    intro hl
    rw [show radius u v=u by simp [radius,abs_of_nonneg (show 0≤u by omega),abs_of_nonneg hv,max_eq_left hvu]] at hl
    exact front_sector hh hl hv hvu
  exact quadrant sw neg sector x y hm

theorem outerEO {h x y : ℤ} (hh : 4≤h) (hm : h≤radius x y) :
    step (E h) x y = O h x y := (front_transitions hh hm).1

theorem outerOE {h x y : ℤ} (hh : 4≤h) (hm : h≤radius x y) :
    step (O h) x y = E (h+1) x y := (front_transitions hh hm).2

end Rule107

namespace Rule107

set_option maxHeartbeats 800000 in
private theorem inner_sector {h x y : ℤ} (hh : 4≤h) (hhx : x<h) (hy : 0≤y) (hyx : y≤x) :
    step (E h) x y = O h x y ∧ step (O h) x y = E (h+1) x y := by
  by_cases hz : x=0
  · subst x
    have hy0 : y=0 := by omega
    subst y
    have r0 : radius 0 0=0 := by decide
    have rxp : radius (0+1) 0=1 := by decide
    have rxm : radius (0-1) 0=1 := by decide
    have ryp : radius 0 (0+1)=1 := by decide
    have rym : radius 0 (0-1)=1 := by decide
    simp (disch := omega) only [step,E,O,r0,rxp,rxm,ryp,rym,decide_eq_true,decide_eq_false]
    decide
  have hx : 0≤x := by omega
  have r0 : radius x y = x := by
    simp [radius,abs_of_nonneg hx,abs_of_nonneg hy,max_eq_left hyx]
  have rxp : radius (x+1) y = x+1 := by
    simp [radius,abs_of_nonneg (show 0≤x+1 by omega),abs_of_nonneg hy,max_eq_left (show y≤x+1 by omega)]
  have rym : radius x (y-1) = x := by
    simp only [radius,abs_of_nonneg hx]
    exact max_eq_left (abs_le.mpr (by omega))
  rcases lt_or_eq_of_le hyx with hs|hs
  · have rxm : radius (x-1) y = x-1 := by
      simp [radius,abs_of_nonneg (show 0≤x-1 by omega),abs_of_nonneg hy,max_eq_left (show y≤x-1 by omega)]
    have ryp : radius x (y+1) = x := by
      simp [radius,abs_of_nonneg hx,abs_of_nonneg (show 0≤y+1 by omega),max_eq_left (show y+1≤x by omega)]
    by_cases par : (x+y)%2=0 <;>
      rcases (show x=1 ∨ x=2 ∨ x=h-1 ∨ (2<x ∧ x<h-1) by omega) with hh0|hh1|hh2|hh3 <;>
      first | (exfalso; omega) | (simp (disch := omega) only [step,E,O,r0,rxp,rxm,ryp,rym,decide_eq_true,decide_eq_false]; decide)
  · have rxm : radius (x-1) y = x := by
      simp [radius,abs_of_nonneg (show 0≤x-1 by omega),abs_of_nonneg hx,hs]
    have ryp : radius x (y+1) = x+1 := by
      simp [radius,abs_of_nonneg hx,abs_of_nonneg (show 0≤x+1 by omega),hs]
    rcases (show x=1 ∨ x=2 ∨ x=h-1 ∨ (2<x ∧ x<h-1) by omega) with hh0|hh1|hh2|hh3 <;>
      (simp (disch := omega) only [step,E,O,r0,rxp,rxm,ryp,rym,decide_eq_true,decide_eq_false]; decide)

private theorem inner_transitions {h x y : ℤ} (hh : 4≤h) (hm : radius x y<h) :
    step (E h) x y = O h x y ∧ step (O h) x y = E (h+1) x y := by
  let P (u v : ℤ) := radius u v<h →
    step (E h) u v = O h u v ∧ step (O h) u v = E (h+1) u v
  have sw (u v : ℤ) : P v u ↔ P u v := by
    simp only [P,swapStep (swapE h) u v,swapStep (swapO h) u v,swapO h u v,swapE (h+1) u v,
      radius,max_comm |v| |u|]
  have neg (u v : ℤ) : P (-u) v ↔ P u v := by
    simp only [P,mirrorStep (mirrorE h),mirrorStep (mirrorO h),mirrorE,mirrorO,radius,abs_neg]
  have sector (u v : ℤ) (hv : 0≤v) (hvu : v≤u) : P u v := by
    intro hl
    rw [show radius u v=u by simp [radius,abs_of_nonneg (show 0≤u by omega),abs_of_nonneg hv,max_eq_left hvu]] at hl
    exact inner_sector hh hl hv hvu
  exact quadrant sw neg sector x y hm

theorem innerEO {h x y : ℤ} (hh : 4≤h) (hm : radius x y<h) :
    step (E h) x y = O h x y := (inner_transitions hh hm).1

theorem innerOE {h x y : ℤ} (hh : 4≤h) (hm : radius x y<h) :
    step (O h) x y = E (h+1) x y := (inner_transitions hh hm).2

end Rule107

namespace Rule107
open OMA.S_oeis_a270166

private theorem cone_le {u v k : ℤ} :
    radius u v ≤ k ↔ (-k≤u ∧ u≤k) ∧ (-k≤v ∧ v≤k) := by
  simp only [radius,max_le_iff,abs_le]

/-- Beyond the reachable square, the update acts on a spatially constant
configuration, switching it between OFF and ON at successive times. -/
theorem outside (t : ℕ) (x y : ℤ) (hr : (t : ℤ)<radius x y) :
    cell 107 t x y = decide (t%2=1) := by
  induction t generalizing x y with
  | zero =>
    change decide (x=0 ∧ y=0) = false
    apply decide_eq_false
    rintro ⟨rfl,rfl⟩
    simp [radius] at hr
  | succ t ih =>
    have extend (u v : ℤ) (hu : x-1≤u ∧ u≤x+1) (hv : y-1≤v ∧ v≤y+1) :
        (t : ℤ)<radius u v := by
      by_contra! h
      have hl := cone_le.mp h
      have h' : radius x y ≤ (t.succ : ℤ) := cone_le.mpr (by push_cast; omega)
      omega
    simp only [cell]
    rw [ih x y (extend _ _ (by omega) (by omega)),
      ih (x+1) y (extend _ _ (by omega) (by omega)),
      ih (x-1) y (extend _ _ (by omega) (by omega)),
      ih x (y+1) (extend _ _ (by omega) (by omega)),
      ih x (y-1) (extend _ _ (by omega) (by omega))]
    by_cases hd : t%2=1
    · have hs : ¬t.succ%2=1 := by omega
      simp only [hd,hs,decide_true,decide_false]
      decide
    · have hs : t.succ%2=1 := by omega
      simp only [hd,hs,decide_true,decide_false]
      decide

theorem eight_outside (x y : ℤ) (hr : 8 < radius x y) : cell 107 8 x y = E 4 x y := by
  rw [outside 8 x y hr]
  change false = decide _
  exact (decide_eq_false (by omega)).symm

end Rule107

namespace Rule107
open OMA.S_oeis_a270166 Finset

private def preview (t : ℕ) (x y : ℤ) : Bool :=
  if t=0 then decide (x=0 ∧ y=0)
  else if x.natAbs ≤ 8 ∧ y.natAbs ≤ 8 then
    (0x15050541414ffffffffffafbbfbebfb800000000000140404003ffffffffffffafbfffee00000000000000140404fffffffffffffffbfbff800000000000000001007fffffffffffffffffbfa00000000000000000001 : ℕ).testBit (81*t+9*x.natAbs+y.natAbs)
  else decide (t%2=1)

private theorem inspect_square (r : ℕ) (P : ℤ → ℤ → Prop)
    (check : ∀ i j : Fin (2*r+1), P ((i:ℤ)-r) ((j:ℤ)-r)) (x y : ℤ)
    (h : radius x y ≤ (r:ℤ)) : P x y := by
  simp only [radius,max_le_iff,abs_le] at h
  let i : Fin (2*r+1) := ⟨(x+r).toNat,by omega⟩
  let j : Fin (2*r+1) := ⟨(y+r).toNat,by omega⟩
  have hx : (i:ℤ)-r=x := by dsimp [i]; omega
  have hy : (j:ℤ)-r=y := by dsimp [j]; omega
  simpa only [hx,hy] using check i j

private theorem preview_step (t : Fin 8) (x y : ℤ) (hw : radius x y ≤ 16) :
    step (preview t) x y = preview (t.val+1) x y := by
  apply inspect_square 16 (fun u v => step (preview t) u v = preview (t.val+1) u v) _ x y hw
  have verified (q : Fin 8) (i : Fin 33) : ∀ j : Fin 33,
      step (preview q) ((i:ℤ)-16) ((j:ℤ)-16) =
        preview (q.val+1) ((i:ℤ)-16) ((j:ℤ)-16) := by
    fin_cases q <;> fin_cases i <;> decide +kernel
  exact verified t

private theorem cell_preview (t : ℕ) (ht : t ≤ 8) (x y : ℤ) (h : radius x y ≤ 16-(t:ℤ)) :
    cell 107 t x y = preview t x y := by
  induction t generalizing x y with
  | zero => rfl
  | succ t ih =>
    have hx := h
    simp only [radius,max_le_iff,abs_le] at hx
    have atp (u v : ℤ) (ha : x-1 ≤ u) (hb : u ≤ x+1) (hc : y-1 ≤ v) (hd : v ≤ y+1) :
        cell 107 t u v = preview t u v := by
      apply ih (by omega)
      simp only [radius,max_le_iff,abs_le]
      omega
    have eqn := preview_step (⟨t,by omega⟩ : Fin 8) x y (by omega)
    rw [cell]
    simpa only [step,atp x y (by omega) (by omega) (by omega) (by omega),
      atp (x+1) y (by omega) (by omega) (by omega) (by omega),
      atp (x-1) y (by omega) (by omega) (by omega) (by omega),
      atp x (y+1) (by omega) (by omega) (by omega) (by omega),
      atp x (y-1) (by omega) (by omega) (by omega) (by omega)] using eqn

theorem eight_inside (x y : ℤ) (hr : radius x y ≤ 8) : cell 107 8 x y = E 4 x y := by
  rw [cell_preview 8 (by decide) x y (by omega)]
  apply inspect_square 8 (fun u v => preview 8 u v = E 4 u v) _ x y hr
  decide +kernel

theorem stage_small (t : Fin 8) : onCount 107 t =
    (![1,5,5,41,12,109,16,197] : Fin 8 → ℕ) t := by
  have hsum : onCount 107 t =
      ∑ i ∈ range (2*t.val+1), ∑ j ∈ range (2*t.val+1),
        if preview t ((i:ℤ)-t) ((j:ℤ)-t) then 1 else 0 := by
    apply sum_congr rfl; intro i hi
    apply sum_congr rfl; intro j hj
    simp only [mem_range] at hi hj
    rw [cell_preview _ (by omega)]
    simp only [radius,max_le_iff,abs_le]
    omega
  rw [hsum]
  fin_cases t <;> decide +kernel

end Rule107

namespace Rule107
open Finset OMA.S_oeis_a270166

noncomputable def box (r : ℕ) : Finset (ℤ×ℤ) := Icc (-(r:ℤ)) r ×ˢ Icc (-(r:ℤ)) r

noncomputable def oddBox (r : ℕ) := (box r).filter fun p => (p.1+p.2)%2=1

theorem mem_box {r : ℕ} {p : ℤ×ℤ} : p∈box r ↔ radius p.1 p.2 ≤ (r:ℤ) := by
  simp only [box,mem_product,mem_Icc,radius,max_le_iff,abs_le]

theorem mem_oddBox {r : ℕ} {p : ℤ×ℤ} :
    p∈oddBox r ↔ radius p.1 p.2 ≤ (r:ℤ) ∧ (p.1+p.2)%2=1 := by
  simp only [oddBox,mem_filter,mem_box]

theorem box_card (r : ℕ) : (box r).card = (2*r+1)^2 := by
  rw [box,card_product,Int.card_Icc]
  have h : ((r:ℤ)+1 - (-(r:ℤ))).toNat = 2*r+1 := by omega
  rw [h,pow_two]

private theorem center_sum (r : ℕ) (f : ℤ → ℕ) :
    (∑ i ∈ range (2*r+1), f ((i:ℤ)-r)) = ∑ x ∈ Icc (-(r:ℤ)) r, f x := by
  apply sum_bij (fun (i : ℕ) _ => (i:ℤ)-r)
  · intro i hi; simp only [mem_Icc]; have := mem_range.mp hi; omega
  · intro i _ j _ h; omega
  · intro x hx
    obtain ⟨h1,h2⟩ := mem_Icc.mp hx
    exact ⟨(x+r).toNat,mem_range.mpr (by omega),by omega⟩
  · intros; rfl

theorem onCount_filter (t : ℕ) : onCount 107 t =
    ((box t).filter (fun p => cell 107 t p.1 p.2)).card := by
  rw [onCount,card_filter,box,sum_product]
  rw [←center_sum]
  apply sum_congr rfl; intro i _
  exact center_sum t (fun y => if cell 107 t ((i:ℤ)-t) y then 1 else 0)

private theorem parity_range (r : ℕ) (z : ℤ) :
    (∑ i ∈ range (2*r), if (z+(i:ℤ))%2=1 then 1 else 0) = r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show 2*(r+1)=2*r+1+1 by omega,sum_range_succ,sum_range_succ,ih]
    push_cast
    split_ifs <;> omega

private theorem parity_full (r : ℕ) (z : ℤ) :
    (∑ i ∈ range (2*r+1), if (z+(i:ℤ))%2=1 then 1 else 0) =
      r+(if z%2=1 then 1 else 0) := by
  rw [sum_range_succ,parity_range]
  push_cast
  split_ifs <;> omega

theorem oddBox_card (r : ℕ) : (oddBox r).card = 2*r*(r+1) := by
  rw [oddBox,card_filter,box,sum_product,←center_sum]
  have row (i : ℕ) : (∑ y ∈ Icc (-(r:ℤ)) (r:ℤ),
      if ((i:ℤ)-r+y)%2=1 then 1 else 0) = r+(if (i:ℤ)%2=1 then 1 else 0) := by
    rw [←center_sum]
    simpa only [show ∀ j : ℕ, (((i:ℤ)-r+((j:ℤ)-r))%2=1) ↔ (((i:ℤ)+j)%2=1) by
      intro j; omega] using parity_full r i
  simp_rw [row]
  rw [sum_add_distrib]
  have p := parity_full r 0
  simp only [zero_add] at p
  simp only [Int.zero_emod,show (0:ℤ) ≠ 1 by decide,if_false,add_zero] at p
  rw [p]
  simp
  ring

theorem oddBox_mono {a b : ℕ} (h : a ≤ b) : oddBox a ⊆ oddBox b := by
  intro p hP
  rw [mem_oddBox] at *
  exact ⟨by omega,hP.2⟩

end Rule107

namespace Rule107
open OMA.S_oeis_a270166 Finset

private theorem radius_pos_iff (p : ℤ×ℤ) : 0 < radius p.1 p.2 ↔ p ≠ (0,0) := by
  rcases p with ⟨x,y⟩
  simp [radius,abs_pos,Prod.mk.injEq]
  tauto

theorem stage_even (h : ℕ) (hh : 4 ≤ h)
    (shape : ∀ x y, cell 107 (2*h) x y = E h x y) :
    onCount 107 (2*h) = 2*h*(h+1) := by
  rw [onCount_filter]
  have seteq : (box (2*h)).filter (fun p => cell 107 (2*h) p.1 p.2) =
      ((box h) \ (oddBox h)).erase (0,0) := by
    ext p
    simp only [mem_filter,mem_box,mem_erase,mem_sdiff,mem_oddBox,shape,E,decide_eq_true_eq]
    rw [←radius_pos_iff]
    push_cast
    omega
  have inside : (0,0) ∈ box h \ oddBox h := by
    simp [mem_sdiff,mem_box,mem_oddBox,radius]
  have sub : oddBox h ⊆ box h := by exact filter_subset _ _
  rw [seteq,card_erase_of_mem inside,card_sdiff_of_subset sub,box_card,oddBox_card]
  have hh' : (2*h+1)^2 = 2*h*(h+1)+2*h*(h+1)+1 := by ring
  omega

theorem stage_odd (h : ℕ) (hh : 4 ≤ h)
    (shape : ∀ x y, cell 107 (2*h+1) x y = O h x y) :
    onCount 107 (2*h+1) = 14*h^2+22*h+9 := by
  obtain ⟨q,hq⟩ : ∃ q, h=q+4 := ⟨h-4,by omega⟩
  subst h
  let U := oddBox (q+3) \ oddBox 1
  let V := oddBox (q+5) \ oddBox (q+4)
  let T := 2*(q+4)+1
  have splitting : (box T).filter (fun p => cell 107 T p.1 p.2) = box T \ (U ∪ V) := by
    ext p
    simp only [T,U,V,mem_filter,mem_box,mem_sdiff,mem_union,mem_oddBox,shape,O,decide_eq_true_eq]
    push_cast
    omega
  have disj : Disjoint U V := by
    apply disjoint_left.mpr
    intro p hu hv
    simp only [U,V,mem_sdiff,mem_oddBox] at hu hv
    push_cast at *
    omega
  have contain : U ∪ V ⊆ box T := by
    intro p hp
    simp only [T,U,V,mem_sdiff,mem_union,mem_oddBox,mem_box] at *
    push_cast at *
    omega
  have small : oddBox 1 ⊆ oddBox (q+3) := oddBox_mono (by omega)
  have large : oddBox (q+4) ⊆ oddBox (q+5) := oddBox_mono (by omega)
  rw [onCount_filter,splitting,card_sdiff_of_subset contain,card_union_of_disjoint disj]
  simp only [U,V,T,card_sdiff_of_subset small,card_sdiff_of_subset large,oddBox_card,box_card]
  have h1 : 2*(q+3)*(q+3+1)=4+(2*q^2+14*q+20) := by ring
  have h2 : 2*(q+5)*(q+5+1)=2*(q+4)*(q+4+1)+(4*q+20) := by ring
  have h3 : (2*(2*(q+4)+1)+1)^2=(2*q^2+14*q+20)+(4*q+20)+(14*(q+4)^2+22*(q+4)+9) := by ring
  omega

end Rule107

namespace Rule107
open OMA.S_oeis_a270166

theorem cell_step (n : ℕ) : cell 107 (n+1) = step (cell 107 n) := rfl

theorem phases
    (base : cell 107 8 = E 4)
    (eo : ∀ h : ℤ, 4≤h → step (E h) = O h)
    (oe : ∀ h : ℤ, 4≤h → step (O h) = E (h+1))
    (h : ℕ) (hh : 4≤h) :
    cell 107 (2*h) = E h ∧ cell 107 (2*h+1) = O h := by
  have advance (k : ℕ) (hk : 4≤k) (he : cell 107 (2*k) = E k) :
      cell 107 (2*k+1) = O k := by
    rw [cell_step, he, eo k (by exact_mod_cast hk)]
  induction h, hh using Nat.le_induction with
  | base => exact ⟨base, advance 4 (by decide) base⟩
  | succ k hk ih =>
    have he : cell 107 (2*(k+1)) = E (k+1 : ℕ) := by
      rw [show 2*(k+1)=2*k+1+1 by omega,cell_step,ih.2,oe k (by exact_mod_cast hk)]
      simp
    exact ⟨he, advance _ (by omega) he⟩

end Rule107

namespace Rule107
open OMA.S_oeis_a270166 PowerSeries

def evenPoly (x : ℚ) : ℚ := (4*x^3+9*x^2+5*x-108)/6
def oddPoly (x : ℚ) : ℚ := (4*x^3+18*x^2+23*x-99)/6
def smallValues : List ℚ := [1,6,11,52,64,173,189]

def model (n : ℕ) : ℚ := if n < 7 then smallValues[n]?.getD 0 else
  if n%2=0 then evenPoly n else oddPoly n

theorem cum_step (n : ℕ) : a (n+1) = a n + onCount 107 (n+1) := by
  simp only [a, Finset.sum_range_succ]

private theorem initial : ∀ t : Fin 7, model t + ((![1,5,5,41,12,109,16,197] : Fin 8 → ℕ)
    ⟨t.val+1, by omega⟩ : ℚ) = model (t.val+1) := by decide +kernel

theorem values
    (hs : ∀ t : Fin 8, onCount 107 t = (![1,5,5,41,12,109,16,197] : Fin 8 → ℕ) t)
    (he : ∀ h : ℕ, 4≤h → onCount 107 (2*h) = 2*h*(h+1))
    (ho : ∀ h : ℕ, 4≤h → onCount 107 (2*h+1) = 14*h^2+22*h+9)
    (n : ℕ) : (a n : ℚ) = model n := by
  induction n with
  | zero =>
    have e := hs 0
    norm_num at e
    simp [a, e, model, smallValues]
  | succ n ih =>
    rw [cum_step, Int.cast_add, ih, Int.cast_natCast]
    by_cases hn : n < 7
    · have e := hs ⟨n+1, by omega⟩
      change onCount 107 (n+1) = _ at e
      rw [e]
      exact initial ⟨n, hn⟩
    · let h := (n+1)/2
      have hh : 4≤h := by dsimp [h]; omega
      by_cases hp : (n+1)%2=0
      · have eq : n+1=2*h := by dsimp [h]; omega
        have stage := he h hh
        rw [← eq] at stage
        rw [stage]
        have eq' : (n : ℚ)+1=2*(h:ℚ) := by exact_mod_cast eq
        simp (disch := omega) only [model, if_neg, if_pos, evenPoly, oddPoly, Nat.cast_succ, Nat.cast_mul]
        rw [show (n:ℚ)=2*h-1 by linarith]
        ring
      · have eq : n+1=2*h+1 := by dsimp [h]; omega
        have stage := ho h hh
        rw [← eq] at stage
        rw [stage]
        have eq' : (n : ℚ)=2*(h:ℚ) := by exact_mod_cast (show n=2*h by omega)
        simp (disch := omega) only [model, if_neg, if_pos, evenPoly, oddPoly, Nat.cast_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, eq']
        ring

theorem model_rec (n : ℕ) (hn : 14≤n) :
    model n = model (n-1) + 3*model (n-2) - 3*model (n-3) - 3*model (n-4) +
      3*model (n-5) + model (n-6) - model (n-7) := by
  by_cases hp : n%2=0 <;>
    simp (disch := omega) only [model, if_neg, if_pos, evenPoly, oddPoly, Nat.cast_sub, Nat.cast_ofNat, Nat.cast_one] <;> ring

def gen : PowerSeries ℚ := PowerSeries.mk model

theorem model_gf :
    gen * ((1-X)^4 * (1+X)^3) = 1 + 5*X + 2*X^2 + 26*X^3 + X^5 -
      6*X^6 - 12*X^7 + 23*X^8 + 16*X^9 - 24*X^10 - 12*X^11 + 8*X^12 + 4*X^13 := by
  have expand : gen * ((1-X)^4*(1+X)^3) =
      gen - gen*X^1 - C 3*(gen*X^2) + C 3*(gen*X^3) + C 3*(gen*X^4) -
      C 3*(gen*X^5) - gen*X^6 + gen*X^7 := by simp only [map_ofNat]; ring
  have numer : (1 + 5*X + 2*X^2 + 26*X^3 + X^5 - 6*X^6 - 12*X^7 + 23*X^8 +
      16*X^9 - 24*X^10 - 12*X^11 + 8*X^12 + 4*X^13 : PowerSeries ℚ) =
      C 1 + C 5*X^1 + C 2*X^2 + C 26*X^3 + X^5 - C 6*X^6 - C 12*X^7 +
      C 23*X^8 + C 16*X^9 - C 24*X^10 - C 12*X^11 + C 8*X^12 + C 4*X^13 := by
    simp only [map_ofNat,map_one,pow_one]
  rw [expand, numer]
  ext n
  simp only [map_sub,map_add,coeff_C_mul,coeff_mul_X_pow',coeff_X_pow,coeff_C,gen,coeff_mk]
  by_cases h : n<14
  · interval_cases n <;> norm_num [model, smallValues, evenPoly, oddPoly]
  · simp (disch := omega) only [if_pos,if_neg, add_zero,sub_zero]
    linarith only [model_rec n (by omega)]

theorem algebra_solution (av : ∀ n, (a n : ℚ) = model n) :
    type_of% @OMA.S_oeis_a270166.main := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    rw [av]
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hp : (-1:ℚ)^n=1 := (show Even n from ⟨k,hk⟩).neg_one_pow
      rw [hp]
      simp (disch := omega) only [model, if_neg, if_pos, evenPoly]
      ring
    · have hp : (-1:ℚ)^n=(-1) := (show Odd n from ⟨k,hk⟩).neg_one_pow
      rw [hp]
      simp (disch := omega) only [model, if_neg, oddPoly]
      ring
  · rintro n hn ⟨k,hk⟩
    rw [av]
    simp (disch := omega) only [model, if_neg, if_pos, evenPoly]
  · rintro n hn ⟨k,hk⟩
    rw [av]
    simp (disch := omega) only [model, if_neg, oddPoly]
  · intro n hn
    simpa only [av] using model_rec n hn
  · simpa only [av, gen] using model_gf

end Rule107

open Rule107 OMA.S_oeis_a270166 in
theorem OMA.solution : type_of% @OMA.S_oeis_a270166.main := by
  have base : cell 107 8 = E 4 := by
    funext x y
    rcases le_or_gt (radius x y) 8 with hl | hg
    · exact eight_inside x y hl
    · exact eight_outside x y hg
  have eo (h : ℤ) (hh : 4≤h) : step (E h) = O h := by
    funext x y
    rcases lt_or_ge (radius x y) h with hl | hg
    · exact innerEO hh hl
    · exact outerEO hh hg
  have oe (h : ℤ) (hh : 4≤h) : step (O h) = E (h+1) := by
    funext x y
    rcases lt_or_ge (radius x y) h with hl | hg
    · exact innerOE hh hl
    · exact outerOE hh hg
  apply algebra_solution
  apply values stage_small
  · intro h hh
    apply stage_even h hh
    intro x y
    rw [(phases base eo oe h hh).1]
  · intro h hh
    apply stage_odd h hh
    intro x y
    rw [(phases base eo oe h hh).2]
