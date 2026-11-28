import OMAStatements.S_oeis_a281741
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Chai Wah Wu's recurrence for Robert Price's A281741 fails at step 366.
The same step was previously used by @ppleskov for the reverse reading of
the axis, A281742 (PR 31230). Here the bits are placed in left-to-origin
order and the recurrence has coefficients 1, 256, and -256. -/

namespace OMA.Rule393Left
open OMA.S_oeis_a281741

private def pos (x y : ℤ) : ℕ := (380 - x + 1120*(370+y)).toNat
private def mask : ℕ := 2^840000 - 1

/-- Update the whole window at once. A live cell survives an odd number
of live neighbours, and a dead cell turns on when all four neighbours agree. -/
private def advance (s : ℕ) : ℕ :=
  let l := s >>> 1
  let r := s <<< 1
  let u := s >>> 1120
  let d := s <<< 1120
  let equalNeighbours := (mask ^^^ (l ^^^ r)) &&& (mask ^^^ (r ^^^ u)) &&& (mask ^^^ (u ^^^ d))
  ((s &&& (l ^^^ r ^^^ u ^^^ d)) ||| ((mask ^^^ s) &&& equalNeighbours)) &&& mask

private def grid : ℕ → ℕ
  | 0 => 2^(pos 0 0)
  | t+1 => advance (grid t)

private theorem rule_bit (c l r u d : Bool) :
    ((c && (l ^^ r ^^ u ^^ d)) || ((!c) && ((!(l ^^ r)) && (!(r ^^ u)) && (!(u ^^ d))))) =
      (393:ℕ).testBit (c.toNat + 2*(r.toNat+l.toNat+u.toNat+d.toNat)) := by
  cases c <;> cases l <;> cases r <;> cases u <;> cases d <;> decide

/-- The verified interior shrinks by one cell on each side at each step.
All cells read at the four specified times lie inside this interior. -/
private theorem read_grid (t : ℕ) (x y : ℤ)
    (hx : -740 + (t:ℤ) ≤ x ∧ x ≤ 375 - t)
    (hy : -368 + (t:ℤ) ≤ y ∧ y ≤ 368 - t) :
    (grid t).testBit (pos x y) = cell 393 t x y := by
  induction t generalizing x y with
  | zero =>
    simp only [grid, Nat.testBit_two_pow,cell]; congr 1
    unfold pos; simp only [Nat.cast_zero] at hx hy
    apply propext
    constructor
    · intro h
      have : 380 - x + 1120*(370+y) = 380 + 1120*370 := by omega
      constructor <;> omega
    · rintro ⟨rfl,rfl⟩; rfl
  | succ t ih =>
    push_cast at hx hy
    let i := pos x y
    have i0 : 1120 ≤ i := by dsimp [i,pos]; omega
    have im : i < 840000 := by dsimp [i,pos]; omega
    have mask_on : mask.testBit i = true := by simp only [mask,Nat.testBit_two_pow_sub_one,decide_eq_true im]
    have left : 1+i = pos (x-1) y := by dsimp [i,pos]; omega
    have right : i-1 = pos (x+1) y := by dsimp [i,pos]; omega
    have up : 1120+i = pos x (y+1) := by dsimp [i,pos]; omega
    have down : i-1120 = pos x (y-1) := by dsimp [i,pos]; omega
    change (advance (grid t)).testBit i = _
    simp only [advance,Nat.testBit_and,Nat.testBit_or,Nat.testBit_xor,Nat.testBit_shiftLeft,
      Nat.testBit_shiftRight,mask_on,decide_eq_true (show 1 ≤ i by omega),decide_eq_true i0,
      Bool.true_and,Bool.and_true,Bool.true_xor,left,right,up,down]
    rw [rule_bit]
    change _ = (393:ℕ).testBit _
    rw [ih x y (by constructor <;> omega) (by constructor <;> omega),
      ih (x-1) y (by constructor <;> omega) (by constructor <;> omega),
      ih (x+1) y (by constructor <;> omega) (by constructor <;> omega),
      ih x (y+1) (by constructor <;> omega) (by constructor <;> omega),
      ih x (y-1) (by constructor <;> omega) (by constructor <;> omega)]

private def axis (t g : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (t+1), if g.testBit (pos 0 0 + (t-k)) then 2^(t-k) else 0

private theorem read_axis (t : ℕ) (ht : t ≤ 366) : a t = (axis t (grid t) : ℤ) := by
  unfold a axis
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have hr := read_grid t ((k:ℤ)-t) 0 (by constructor <;> omega) (by constructor <;> omega)
  have hp : pos ((k:ℤ)-t) 0 = pos 0 0 + (t-k) := by unfold pos; omega
  rw [← hr,hp]

private theorem fails (t : ℕ) (ht : t ≤ 366)
    (hn : axis t (grid t) + 256*axis (t-10) (grid (t-10)) ≠
      axis (t-2) (grid (t-2)) + 256*axis (t-8) (grid (t-8))) :
    ¬ ((a t : ℚ) = a (t-2) + 256*a (t-8) - 256*a (t-10)) := by
  intro h
  rw [read_axis t ht,read_axis (t-2) (by omega),read_axis (t-8) (by omega),
    read_axis (t-10) (by omega)] at h
  apply hn
  exact_mod_cast (show ((axis t (grid t):ℚ) + 256*axis (t-10) (grid (t-10))) =
      (axis (t-2) (grid (t-2)):ℚ) + 256*axis (t-8) (grid (t-8)) by
        push_cast at h; linarith)

end OMA.Rule393Left

open OMA.Rule393Left in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a281741.main) := by
  rintro ⟨h,_⟩
  exact fails 366 (by decide) (by decide +kernel) (h 366 (by decide))
