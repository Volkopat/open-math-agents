import OMAStatements.S_oeis_a279030
import Mathlib

/-!
# The left half-axis in Rule 129

For the conjectures of Colin Barker in https://oeis.org/A279030, Robert
Price's observation window reads the half-axis from its left endpoint to
the origin. Mario C. Enriquez related the digits to A000975, and N. J. A.
Sloane pointed out the bisection A002450.

Two Rule 129 steps on a doubled lattice induce the Ulam-Warburton growth
rule, discussed by Applegate, Pol and Sloane in §6 of arXiv:1004.3036.
We verify this for arbitrary starting configurations on that sublattice.
The coarse process advances one site along the axis per step. The resulting
alternating binary weights give the closed form, recurrence, and series.
-/

namespace Axis129

def seed (x y : ℤ) : Bool := decide (x=0 ∧ y=0)

def inflate (f : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  if x%2=0 ∧ y%2=0 then f (x/2) (y/2) else false

def step (f : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  (129 : ℕ).testBit ((f x y).toNat + 2*((f (x+1) y).toNat +
    (f (x-1) y).toNat + (f x (y+1)).toNat + (f x (y-1)).toNat))

def grow (f : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  f x y || decide ((f (x+1) y).toNat + (f (x-1) y).toNat +
    (f x (y+1)).toNat + (f x (y-1)).toNat = 1)

def coarse : ℕ → ℤ → ℤ → Bool
  | 0 => seed
  | t+1 => grow (coarse t)

end Axis129

namespace Axis129

private theorem evenXY (f : ℤ → ℤ → Bool) (x y : ℤ) :
    inflate f (2*x) (2*y) = f x y := by
  simp (disch := omega) [inflate, show 2*x/2=x by omega, show 2*y/2=y by omega]

private theorem oddX (f : ℤ → ℤ → Bool) (x y : ℤ) :
    inflate f (2*x+1) y = false := by
  simp (disch := omega) [inflate, show (2*x+1)%2=1 by omega]

private theorem oddY (f : ℤ → ℤ → Bool) (x y : ℤ) :
    inflate f x (2*y+1) = false := by
  simp (disch := omega) [inflate, show (2*y+1)%2=1 by omega]

private theorem prior (x : ℤ) : 2*x-1=2*(x-1)+1 := by omega
private theorem next (x : ℤ) : 2*x+1+1=2*(x+1) := by omega

theorem halfEE (f : ℤ → ℤ → Bool) (x y : ℤ) :
    step (inflate f) (2*x) (2*y) = !(f x y) := by
  rw [step]
  simp only [prior, oddX, oddY, evenXY]
  cases f x y <;> decide

theorem halfOE (f : ℤ → ℤ → Bool) (x y : ℤ) :
    step (inflate f) (2*x+1) (2*y) = !(f x y || f (x+1) y) := by
  rw [step]
  simp only [next,add_sub_cancel_right,prior,oddX,evenXY]
  cases f x y <;> cases f (x+1) y <;> decide

theorem halfEO (f : ℤ → ℤ → Bool) (x y : ℤ) :
    step (inflate f) (2*x) (2*y+1) = !(f x y || f x (y+1)) := by
  rw [step]
  simp only [next,add_sub_cancel_right,prior,oddY,evenXY]
  cases f x y <;> cases f x (y+1) <;> decide

theorem halfOO (f : ℤ → ℤ → Bool) (x y : ℤ) :
    step (inflate f) (2*x+1) (2*y+1) = true := by
  rw [step]
  simp only [oddX,oddY]
  decide

private theorem twoEE (f : ℤ → ℤ → Bool) (x y : ℤ) :
    step (step (inflate f)) (2*x) (2*y) = inflate (grow f) (2*x) (2*y) := by
  rw [step]
  simp only [prior,evenXY,halfEE,halfOE,halfEO,sub_add_cancel,grow]
  cases f x y <;> cases f (x+1) y <;> cases f (x-1) y <;>
    cases f x (y+1) <;> cases f x (y-1) <;> decide

private theorem twoOE (f : ℤ → ℤ → Bool) (x y : ℤ) :
    step (step (inflate f)) (2*x+1) (2*y) = inflate (grow f) (2*x+1) (2*y) := by
  rw [step]
  simp only [next,add_sub_cancel_right,prior,oddX,halfEE,halfOE,halfOO]
  cases f x y <;> cases f (x+1) y <;> decide

private theorem twoEO (f : ℤ → ℤ → Bool) (x y : ℤ) :
    step (step (inflate f)) (2*x) (2*y+1) = inflate (grow f) (2*x) (2*y+1) := by
  rw [step]
  simp only [next,add_sub_cancel_right,prior,oddY,halfEE,halfEO,halfOO]
  cases f x y <;> cases f x (y+1) <;> decide

private theorem twoOO (f : ℤ → ℤ → Bool) (x y : ℤ) :
    step (step (inflate f)) (2*x+1) (2*y+1) = inflate (grow f) (2*x+1) (2*y+1) := by
  rw [step]
  simp only [next,add_sub_cancel_right,oddX,halfOO,halfOE,halfEO]
  cases f x y <;> cases f (x+1) y <;>
    cases f x (y+1) <;> cases f (x+1) (y+1) <;> decide

/-- After two updates, the only occupied sites are at even-even coordinates. Their evolution
retains every existing site and adds those with exactly one occupied neighbor. -/
theorem double_step (f : ℤ → ℤ → Bool) : step (step (inflate f)) = inflate (grow f) := by
  funext x y
  have parity (z : ℤ) : z=2*(z/2) ∨ z=2*(z/2)+1 := by omega
  rcases parity x with hx|hx <;> rcases parity y with hy|hy
  · exact hx.symm ▸ hy.symm ▸ twoEE f (x/2) (y/2)
  · exact hx.symm ▸ hy.symm ▸ twoEO f (x/2) (y/2)
  · exact hx.symm ▸ hy.symm ▸ twoOE f (x/2) (y/2)
  · exact hx.symm ▸ hy.symm ▸ twoOO f (x/2) (y/2)

end Axis129

namespace Axis129

private theorem adjacent_abs (u v : ℤ) (hl : u-1≤v) (hr : v≤u+1) : |u| ≤ |v|+1 := by
  have hv := abs_le.mp (le_refl |v|)
  exact abs_le.mpr (by omega)

/-- Live sites stay within Manhattan distance t of the initial site. -/
theorem coarse_outside (t : ℕ) (x y : ℤ) (ho : (t:ℤ) < |x| + |y|) :
    coarse t x y = false := by
  induction t generalizing x y with
  | zero =>
    change decide (x=0 ∧ y=0) = false
    apply decide_eq_false
    rintro ⟨rfl,rfl⟩
    simp at ho
  | succ t ih =>
    have xp := adjacent_abs x (x+1) (by omega) (by omega)
    have xm := adjacent_abs x (x-1) (by omega) (by omega)
    have yp := adjacent_abs y (y+1) (by omega) (by omega)
    have ym := adjacent_abs y (y-1) (by omega) (by omega)
    simp [coarse,grow,ih x y (by omega),ih (x+1) y (by omega),ih (x-1) y (by omega),
      ih x (y+1) (by omega),ih x (y-1) (by omega)]

/-- At the new left endpoint the right neighbor is the only live neighbor
at the previous time. All earlier axis sites stay live. -/
theorem coarse_axis (t : ℕ) (x : ℤ) (hl : -(t:ℤ)≤x) (hr : x≤0) : coarse t x 0 = true := by
  induction t generalizing x with
  | zero =>
    have h : x=0 := by omega
    subst x
    decide
  | succ t ih =>
    by_cases hi : -(t:ℤ)≤x
    · simp [coarse,grow,ih x hi hr]
    · have endpt : x = -(t:ℤ)-1 := by omega
      have ox : |x| = -x := abs_of_nonpos hr
      have om : |x-1| = -(x-1) := abs_of_nonpos (by omega)
      have hc := coarse_outside t x 0 (by rw [ox,abs_zero]; omega)
      have hp := ih (x+1) (by omega) (by omega)
      have hm := coarse_outside t (x-1) 0 (by rw [om,abs_zero]; omega)
      have hu := coarse_outside t x 1 (by rw [ox,abs_one]; omega)
      have hd := coarse_outside t x (-1) (by rw [ox,abs_neg,abs_one]; omega)
      simp [coarse,grow,hc,hp,hm,hu,hd]

end Axis129

namespace Axis129
open OMA.S_oeis_a279030

theorem native_step (t : ℕ) : cell 129 (t+1) = step (cell 129 t) := rfl

theorem phase (h : ℕ) : cell 129 (2*h) = inflate (coarse h) := by
  induction h with
  | zero =>
    funext x y
    change decide (x=0 ∧ y=0) = (if x%2=0 ∧ y%2=0 then decide (x/2=0 ∧ y/2=0) else false)
    by_cases hz : x=0 ∧ y=0
    · rcases hz with ⟨rfl,rfl⟩
      decide
    · split_ifs with hp
      · have hf : ¬(x/2=0 ∧ y/2=0) := by omega
        simp [hz,hf]
      · simp [hz]
  | succ h ih =>
    rw [show 2*(h+1)=2*h+1+1 by omega, native_step, native_step, ih, double_step]
    rfl

theorem even_bits (h k : ℕ) (hk : k≤2*h) :
    cell 129 (2*h) ((k:ℤ)-(2*h:ℕ)) 0 = decide (k%2=0) := by
  rw [phase]
  by_cases he : k%2=0
  · simp (disch := omega) only [inflate,Nat.cast_mul,Nat.cast_ofNat,Int.zero_emod,
      and_true,if_pos,Int.zero_ediv,decide_eq_true]
    exact coarse_axis _ _ (by omega) (by omega)
  · simp (disch := omega) only [inflate,Nat.cast_mul,Nat.cast_ofNat,Int.zero_emod,
      and_true,if_neg,decide_eq_false]

theorem odd_bits (h k : ℕ) (hk : k≤2*h+1) :
    cell 129 (2*h+1) ((k:ℤ)-(2*h+1:ℕ)) 0 = false := by
  rw [native_step, phase]
  let x : ℤ := (k:ℤ)-(2*h+1:ℕ)
  change step (inflate (coarse h)) x 0 = false
  have lo : -(2*(h:ℤ)+1) ≤ x := by dsimp [x]; omega
  have hi : x ≤ 0 := by dsimp [x]; omega
  by_cases he : x%2=0
  · have eq : x=2*(x/2) := by omega
    have hc := coarse_axis h (x/2) (by omega) (by omega)
    calc
      step (inflate (coarse h)) x 0 = step (inflate (coarse h)) (2*(x/2)) (2*0) := by
        congr 1
      _ = !(coarse h (x/2) 0) := halfEE _ _ _
      _ = false := by simp [hc]
  · have eq : x=2*(x/2)+1 := by omega
    have hc := coarse_axis h (x/2+1) (by omega) (by omega)
    calc
      step (inflate (coarse h)) x 0 = step (inflate (coarse h)) (2*(x/2)+1) (2*0) := by
        congr 1
      _ = !(coarse h (x/2) 0 || coarse h (x/2+1) 0) := halfOE _ _ _
      _ = false := by simp [hc]
end Axis129

namespace Axis129
open OMA.S_oeis_a279030 Finset

private theorem even_geometric (h : ℕ) :
    3 * (∑ k ∈ range (2*h+1), if k%2=0 then (2:ℤ)^k else 0) + 1 = 2^(2+2*h) := by
  induction h with
  | zero => norm_num
  | succ h ih =>
    rw [show 2*(h+1)+1=(2*h+1)+1+1 by omega,sum_range_succ,sum_range_succ,
      if_neg (show ¬(2*h+1)%2=0 by omega),if_pos (show (2*h+1+1)%2=0 by omega),add_zero,
      show 2*h+1+1=2+2*h by omega,show 2+2*(h+1)=(2+2*h)+2 by omega,pow_add (2:ℤ) (2+2*h) 2]
    linarith

theorem even_value (h : ℕ)
    (hp : ∀ k : ℕ, k ≤ 2*h → cell 129 (2*h) ((k:ℤ)-(2*h:ℕ)) 0 = decide (k%2=0)) :
    (a (2*h) : ℚ) = ((2:ℚ)^(2+2*h)-1)/3 := by
  have hs : a (2*h) = ∑ k ∈ range (2*h+1), if k%2=0 then (2:ℤ)^k else 0 := by
    rw [a,←sum_range_reflect (fun k => if k%2=0 then (2:ℤ)^k else 0) (2*h+1)]
    apply sum_congr rfl
    intro k hk
    have b := mem_range.mp hk
    simp only [hp k (by omega),decide_eq_true_eq,show 2*h+1-1=2*h by omega,
      show (2*h-k)%2=0 ↔ k%2=0 by omega]
  have z := even_geometric h
  rw [←hs] at z
  have q : 3 * (a (2*h):ℚ) + 1 = 2^(2+2*h) := by exact_mod_cast z
  linarith

theorem odd_value (h : ℕ)
    (hp : ∀ k : ℕ, k ≤ 2*h+1 → cell 129 (2*h+1) ((k:ℤ)-(2*h+1:ℕ)) 0 = false) :
    (a (2*h+1):ℚ)=0 := by
  suffices a (2*h+1) = 0 by exact_mod_cast this
  rw [a]
  apply sum_eq_zero
  intro k hk
  rw [hp k (by have := mem_range.mp hk; omega)]
  simp

end Axis129

namespace Axis129
open OMA.S_oeis_a279030 PowerSeries

def value (n : ℕ) : ℚ := if n%2=0 then ((2:ℚ)^(2+n)-1)/3 else 0

theorem value_rec (n : ℕ) (hn : 4≤n) :
    value n = 5*value (n-2)-4*value (n-4) := by
  obtain ⟨k,rfl⟩ : ∃ k, n=k+4 := ⟨n-4,by omega⟩
  rw [show k+4-2=k+2 by omega,show k+4-4=k by omega]
  by_cases he : k%2=0
  · simp (disch := omega) only [value,if_pos]
    rw [show 2+(k+4)=(2+k)+4 by omega,show 2+(k+2)=(2+k)+2 by omega,pow_add,pow_add]
    ring
  · simp (disch := omega) only [value,if_neg,mul_zero,sub_zero]

def gen : PowerSeries ℚ := PowerSeries.mk value

theorem value_gf : gen*((1-X)*(1+X)*(1-2*X)*(1+2*X))=1 := by
  have expand : gen*((1-X)*(1+X)*(1-2*X)*(1+2*X)) =
      gen - C 5*(gen*X^2) + C 4*(gen*X^4) := by simp only [map_ofNat]; ring
  rw [expand]
  ext n
  simp only [map_add,map_sub,coeff_C_mul,coeff_mul_X_pow',coeff_one,gen,coeff_mk]
  by_cases h : n<4
  · interval_cases n <;> norm_num [value]
  · simp (disch := omega) only [if_pos,if_neg]
    linarith only [value_rec n (by omega)]

theorem sequence (ev : ∀ h : ℕ, (a (2*h) : ℚ) = ((2:ℚ)^(2+2*h)-1)/3)
    (od : ∀ h : ℕ, (a (2*h+1) : ℚ) = 0) : type_of% @OMA.S_oeis_a279030.main := by
  have av (n : ℕ) : (a n : ℚ) = value n := by
    rcases Nat.even_or_odd n with ⟨h,hh⟩ | ⟨h,hh⟩
    · rw [show n=2*h by omega, ev]
      simp [value]
    · rw [hh, od]
      simp (disch := omega) only [value,if_neg]
  refine ⟨?_, ?_, ?_⟩
  · intro n
    rw [av]
    rcases Nat.even_or_odd n with ⟨k,hk⟩ | ⟨k,hk⟩
    · rw [(show Even n from ⟨k,hk⟩).neg_one_pow]
      simp (disch := omega) only [value,if_pos]
      ring
    · rw [(show Odd n from ⟨k,hk⟩).neg_one_pow]
      simp (disch := omega) only [value,if_neg]
      ring
  · intro n hn
    simpa only [av] using value_rec n hn
  · simpa only [av,gen] using value_gf

end Axis129

open Axis129 in
theorem OMA.solution : type_of% @OMA.S_oeis_a279030.main :=
  sequence (fun h => even_value h (even_bits h)) (fun h => odd_value h (odd_bits h))
