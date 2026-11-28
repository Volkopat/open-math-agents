import OMAStatements.S_oeis_a278899
import Mathlib

/-!
# Decimal digits along the Rule 107 half-axis

This proves Colin Barker's recurrence and generating function for Robert
Price's A278899 (https://oeis.org/A278899). The local square-shell proof
and finite base for the identical automaton are adapted from A270166,
https://github.com/lefttosolve2/open-math-agents/pull/31826.

Even stages give a finite geometric progression of active digits. On odd
stages we subtract the finite progression of missing digits from a string
of ones. Both progressions have ratio 100 when read toward the origin.
A shift of four stages consequently gives a combination of two exponentials
and a constant. The recurrence and all numerator coefficients follow.
-/

/-! The Rule 107 planar phase description and its verification below are adapted from
    the proof of OEIS A270166, open-math-agents PR #31826. -/

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
open OMA.S_oeis_a278899

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
open OMA.S_oeis_a278899 Finset

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

theorem early_values (t : Fin 8) : a t =
    (![1,10,100,1111,100,111011,0,11101111] : Fin 8 → ℤ) t := by
  have hsum : a t =
      ∑ k ∈ range (t.val+1), if preview t k 0 then (10 : ℤ)^(t.val-k) else 0 := by
    apply sum_congr rfl
    intro k hk
    simp only [mem_range] at hk
    rw [cell_preview _ (by omega)]
    simp only [radius,max_le_iff,abs_le]
    omega
  rw [hsum]
  fin_cases t <;> decide +kernel

end Rule107

namespace Rule107
open OMA.S_oeis_a278899

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

theorem native_phases (h : ℕ) (hh : 4≤h) :
    cell 107 (2*h) = E h ∧ cell 107 (2*h+1) = O h := by
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
  exact phases base eo oe h hh

end Rule107

namespace Axis107
open Finset

/-- The decimal value of a block of ones at positions b,b+2,..., counted
from the most significant digit of an (n+1)-digit word. -/
theorem spaced_sum (n b len : ℕ) (hb : b+2*len ≤ n+2) :
    99 * (∑ k ∈ range (n+1), if b≤k ∧ k < b+2*len ∧ k%2=b%2
      then (10:ℚ)^(n-k) else 0) =
    (10:ℚ)^(n+2-b) - (10:ℚ)^(n+2-b-2*len) := by
  induction len with
  | zero =>
    simp only [Nat.mul_zero,Nat.add_zero,Nat.sub_zero,sub_self]
    rw [sum_eq_zero (fun k _ => if_neg (by omega)),mul_zero]
  | succ len ih =>
    have last : b+2*len < n+1 := by omega
    have split (k : ℕ) :
        (if b≤k ∧ k < b+2*(len+1) ∧ k%2=b%2 then (10:ℚ)^(n-k) else 0) =
          (if b≤k ∧ k < b+2*len ∧ k%2=b%2 then (10:ℚ)^(n-k) else 0) +
          (if k=b+2*len then (10:ℚ)^(n-k) else 0) := by
      split_ifs <;> first | omega | simp
    simp_rw [split]
    rw [sum_add_distrib,mul_add,ih (by omega),sum_ite_eq',if_pos (mem_range.mpr last)]
    rw [show n+2-b-2*len=(n-(b+2*len))+2 by omega,pow_add,
      show n+2-b-2*(len+1)=n-(b+2*len) by omega]
    ring

end Axis107

namespace Axis107
open OMA.S_oeis_a278899 Finset

theorem even_value (h : ℕ) (hh : 4≤h) (eq : cell 107 (2*h) = Rule107.E h) :
    99*(a (2*h):ℚ) = (10:ℚ)^(2*h) - (10:ℚ)^(h+h%2) := by
  have ea (k : ℕ) : cell 107 (2*h) k 0 = true ↔
      2 ≤ k ∧ k < 2+2*(h/2) ∧ k%2=2%2 := by
    rw [eq]
    simp only [Rule107.E,decide_eq_true_eq,Rule107.radius,abs_of_nonneg (Int.natCast_nonneg k),
      abs_zero,max_eq_left (Int.natCast_nonneg k),add_zero]
    omega
  have ha : (a (2*h):ℚ) = ∑ k ∈ range (2*h+1),
      if 2 ≤ k ∧ k < 2+2*(h/2) ∧ k%2=2%2 then (10:ℚ)^(2*h-k) else 0 := by
    simp only [a,Int.cast_sum,Int.cast_ite,Int.cast_pow,Int.cast_ofNat,Int.cast_zero,ea]
  rw [ha,spaced_sum (2*h) 2 (h/2) (by omega),
    show 2*h+2-2=2*h by omega,show 2*h-2*(h/2)=h+h%2 by omega]

end Axis107

namespace Axis107

open OMA.S_oeis_a278899 Finset

private theorem all_digits (n : ℕ) :
    99 * (∑ k ∈ range (n+1), (10:ℚ)^(n-k)) = 11*(10^(n+1)-1) := by
  have reflect := sum_range_reflect (fun k => (10:ℚ)^k) (n+1)
  simp only [Nat.add_sub_cancel] at reflect
  rw [reflect]
  have geom := geom_sum_mul (10:ℚ) (n+1)
  linarith

/-- Away from the four initial half-stages, the odd axis word has a block
of missing alternating digits starting at the fourth position. -/
theorem odd_value (h : ℕ) (hh : 4 ≤ h) (eq : cell 107 (2*h+1) = Rule107.O h) :
    99*(a (2*h+1):ℚ) = 11*((10:ℚ)^(2*h+2)-1) - 10^(2*h) + 10^(h+3*(h%2)) := by
  let n := 2*h+1
  let len := h/2-h%2
  have off (k : ℕ) : Rule107.O h k 0 = false ↔
      3≤k ∧ k<3+2*len ∧ k%2=3%2 := by
    simp [Rule107.O, Rule107.radius, abs_of_nonneg (Int.natCast_nonneg k), len]
    omega
  have partition : (a n : ℚ) +
      (∑ k ∈ range (n+1), if 3≤k ∧ k<3+2*len ∧ k%2=3%2 then (10:ℚ)^(n-k) else 0) =
      ∑ k ∈ range (n+1), (10:ℚ)^(n-k) := by
    unfold a
    push_cast
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro k _
    have hv : cell 107 n k 0 = Rule107.O h k 0 := congrFun (congrFun eq (k:ℤ)) 0
    rw [hv]
    cases bit : Rule107.O h k 0 with
    | false => simp [(off k).mp bit]
    | true =>
      have skip : ¬ (3≤k ∧ k<3+2*len ∧ k%2=3%2) := fun contra => by
        have bad := (off k).mpr contra
        simp [bit] at bad
      simp [skip]
  have geom := all_digits n
  have missing := spaced_sum n 3 len (by dsimp [n,len]; omega)
  have htop : n+2-3 = 2*h := by dsimp [n]; omega
  have hlow : n+2-3-2*len = h+3*(h%2) := by dsimp [n,len]; omega
  rw [hlow,htop] at missing
  change 99*(a n:ℚ) = 11*(10^(n+1)-1) - 10^(2*h) + 10^(h+3*(h%2))
  linarith

end Axis107

namespace Axis107
open OMA.S_oeis_a278899 PowerSeries

def initialTerms : Fin 8 → ℤ := ![1,10,100,1111,100,111011,0,11101111]

/-- The two geometric sums, with the scale factors from a four-step time shift. -/
def tailValue (P Q : ℚ) (n : ℕ) : ℚ :=
  let h := n/2
  if n%2=0 then (P*10^(2*h) - Q*10^(h+h%2))/99
  else (11*(P*10^(2*h+2)-1)-P*10^(2*h)+Q*10^(h+3*(h%2)))/99

def value (n : ℕ) : ℚ := if h : n<8 then (initialTerms ⟨n,h⟩ : ℚ) else tailValue 1 1 n

theorem values
    (hs : ∀ i : Fin 8, a i = initialTerms i)
    (he : ∀ h : ℕ, 4≤h → 99*(a (2*h):ℚ) = (10:ℚ)^(2*h) - 10^(h+h%2))
    (ho : ∀ h : ℕ, 4≤h → 99*(a (2*h+1):ℚ) =
       11*((10:ℚ)^(2*h+2)-1) - 10^(2*h) + 10^(h+3*(h%2)))
    (n : ℕ) : (a n : ℚ)=value n := by
  by_cases hn : n<8
  · rw [value,dif_pos hn]
    exact_mod_cast hs ⟨n,hn⟩
  · rw [value,dif_neg hn]
    let h := n/2
    have hh : 4≤h := by dsimp [h]; omega
    by_cases hp : n%2=0
    · have eq : n=2*h := by dsimp [h]; omega
      have hx := he h hh
      rw [←eq] at hx
      simp only [tailValue,if_pos hp,one_mul]
      change (a n:ℚ)=((10:ℚ)^(2*h)-10^(h+h%2))/99
      rw [eq] at hx ⊢
      linarith
    · have eq : n=2*h+1 := by dsimp [h]; omega
      have hx := ho h hh
      simp only [tailValue,if_neg hp,one_mul]
      change (a n:ℚ)=(11*((10:ℚ)^(2*h+2)-1)-10^(2*h)+10^(h+3*(h%2)))/99
      rw [eq]
      linarith

theorem shift (q j : ℕ) (hj : 8≤j) :
    value (4*q+j)=tailValue (10^(4*q)) (10^(2*q)) j := by
  have half : (4*q+j)/2=2*q+j/2 := by omega
  have par : (4*q+j)%2=j%2 := by omega
  have hpar : (2*q+j/2)%2=(j/2)%2 := by omega
  simp only [value,dif_neg (by omega : ¬4*q+j<8),tailValue,half,par,hpar,one_mul]
  rw [show 2*(2*q+j/2)=4*q+2*(j/2) by omega,
      show 4*q+2*(j/2)+2=4*q+(2*(j/2)+2) by omega,
      show 2*q+j/2+(j/2)%2=2*q+(j/2+(j/2)%2) by omega,
      show 2*q+j/2+3*((j/2)%2)=2*q+(j/2+3*((j/2)%2)) by omega]
  simp only [pow_add]

theorem recurrence (n : ℕ) (hn : 16≤n) :
    value n = 101*value (n-2) - 10100*value (n-6) + 10000*value (n-8) := by
  let q := (n-16)/4
  have cases : n=4*q+16 ∨ n=4*q+17 ∨ n=4*q+18 ∨ n=4*q+19 := by dsimp [q]; omega
  rcases cases with eq | eq | eq | eq <;> rw [eq] <;>
    simp (disch := omega) only [Nat.add_sub_assoc,shift] <;> norm_num [tailValue] <;> ring

def gen : PowerSeries ℚ := PowerSeries.mk value

theorem gf : gen * ((1-X)*(1+X)*(1-10*X)*(1+10*X)*(1-10*X^2)*(1+10*X^2)) =
    1+10*X-X^2+101*X^3-10000*X^4-1200*X^5-10000*X^7+2010000*X^8+10000*X^9-
    1000000*X^10+1000000*X^11-101000000*X^12-101000000*X^13+100000000*X^14+100000000*X^15 := by
  have den : gen * ((1-X)*(1+X)*(1-10*X)*(1+10*X)*(1-10*X^2)*(1+10*X^2)) =
      gen - C 101*(gen*X^2) + C 10100*(gen*X^6) - C 10000*(gen*X^8) := by
    simp only [map_ofNat]; ring
  have num : (1+10*X-X^2+101*X^3-10000*X^4-1200*X^5-10000*X^7+2010000*X^8+10000*X^9-
      1000000*X^10+1000000*X^11-101000000*X^12-101000000*X^13+100000000*X^14+100000000*X^15 : PowerSeries ℚ) =
      C 1+C 10*X^1-X^2+C 101*X^3-C 10000*X^4-C 1200*X^5-C 10000*X^7+C 2010000*X^8+C 10000*X^9-
      C 1000000*X^10+C 1000000*X^11-C 101000000*X^12-C 101000000*X^13+C 100000000*X^14+C 100000000*X^15 := by
    simp only [map_ofNat,map_one,pow_one]
  rw [den,num]
  ext n
  simp only [map_add,map_sub,coeff_C_mul,coeff_mul_X_pow',coeff_X_pow,coeff_C,gen,coeff_mk]
  by_cases h : n<16
  · interval_cases n <;> decide +kernel
  · simp (disch := omega) only [if_pos,if_neg,add_zero,sub_zero]
    linarith only [recurrence n (by omega)]

theorem solution_of_values (av : ∀ n, (a n : ℚ)=value n) : type_of% @OMA.S_oeis_a278899.main := by
  constructor
  · intro n hn
    simpa only [av] using recurrence n hn
  · simpa only [av,gen] using gf

end Axis107

open Axis107 Rule107 in
theorem OMA.solution : type_of% @OMA.S_oeis_a278899.main := by
  apply solution_of_values
  apply values early_values
  · exact fun h hh => even_value h hh (native_phases h hh).1
  · exact fun h hh => odd_value h hh (native_phases h hh).2
