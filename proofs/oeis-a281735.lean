import OMAStatements.S_oeis_a281735


/-!
# The eventual Rule 390 axis digits

Chai Wah Wu conjectured the two-step recurrence and generating function in
Robert Price's A281735, https://oeis.org/A281735. We prove the stronger
statement that, from stage 24, each even half-axis word has just its first
digit on, and each odd word has precisely its first three digits on.

The finite leading-edge band evolves autonomously in moving coordinates.
Its periodic orbit, the finite startup, and the elementary blank-interval
induction on the symmetric axis are all checked against the native rule.
The decimal value and its formal generating function then follow.
-/

namespace Rule390
open OMA.S_oeis_a281735

def step (f : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  (390 : ℕ).testBit ((f x y).toNat + 2*((f (x+1) y).toNat +
    (f (x-1) y).toNat + (f x (y+1)).toNat + (f x (y-1)).toNat))

theorem cell_step (t : ℕ) : cell 390 (t+1) = step (cell 390 t) := rfl

end Rule390

namespace Rule390
open OMA.S_oeis_a281735

theorem mirrorX (t : ℕ) (x y : ℤ) : cell 390 t (-x) y = cell 390 t x y := by
  induction t generalizing x y with
  | zero => simp only [cell,neg_eq_zero]
  | succ t ih =>
    simp only [cell,show -x+1 = -(x-1) by omega, show -x-1 = -(x+1) by omega,ih]
    ac_rfl

theorem mirrorY (t : ℕ) (x y : ℤ) : cell 390 t x (-y) = cell 390 t x y := by
  induction t generalizing x y with
  | zero => simp only [cell,neg_eq_zero]
  | succ t ih =>
    simp only [cell,show -y+1 = -(y-1) by omega, show -y-1 = -(y+1) by omega,ih]
    ac_rfl

private theorem adjacent_abs (u v : ℤ) (hl : u-1≤v) (hr : v≤u+1) : |u| ≤ |v|+1 := by
  have hv := abs_le.mp (le_refl |v|)
  exact abs_le.mpr (by omega)

theorem outside (t : ℕ) (x y : ℤ) (h : (t:ℤ) < |x| + |y|) :
    cell 390 t x y = false := by
  induction t generalizing x y with
  | zero =>
    change decide (x=0 ∧ y=0) = false
    apply decide_eq_false
    rintro ⟨rfl,rfl⟩
    simp at h
  | succ t ih =>
    have xp := adjacent_abs x (x+1) (by omega) (by omega)
    have xm := adjacent_abs x (x-1) (by omega) (by omega)
    have yp := adjacent_abs y (y+1) (by omega) (by omega)
    have ym := adjacent_abs y (y-1) (by omega) (by omega)
    simp only [cell,ih x y (by omega),ih (x+1) y (by omega),ih (x-1) y (by omega),
      ih x (y+1) (by omega),ih x (y-1) (by omega)]
    decide

end Rule390

namespace Rule390

open OMA.S_oeis_a281735

/-- A blank horizontal triple stays blank at its center if the two vertical
bits coincide. The center then has either zero or two live neighbors. -/
theorem axis_blank (t : ℕ) (x : ℤ)
    (hcenter : cell 390 t x 0 = false)
    (hright : cell 390 t (x+1) 0 = false) (hleft : cell 390 t (x-1) 0 = false)
    (hvertical : cell 390 t x 1 = cell 390 t x (-1)) :
    cell 390 (t+1) x 0 = false := by
  simp only [cell, hcenter, hright, hleft, zero_add, zero_sub, hvertical]
  cases cell 390 t x (-1) <;> decide

/-- A blank open interval on a reflection-symmetric axis loses at most one
position at each end in one generation. -/
theorem axis_blank_interval (t : ℕ) (r : ℤ)
    (haxis : ∀ x : ℤ, |x| < r → cell 390 t x 0 = false)
    (href : ∀ x : ℤ, cell 390 t x 1 = cell 390 t x (-1)) :
    ∀ x : ℤ, |x| < r-1 → cell 390 (t+1) x 0 = false := by
  intro x hx
  have xb := abs_lt.mp hx
  apply axis_blank t x
  · exact haxis _ (by omega)
  · exact haxis _ (abs_lt.mpr (by omega))
  · exact haxis _ (abs_lt.mpr (by omega))
  · exact href x

/-- Two edge strips, together with the blank interval from the preceding
even stage, determine both successive complete axis words. -/
theorem axis_patterns_step (t : ℕ)
    (sym : ∀ (s : ℕ) (x : ℤ), cell 390 s x 1 = cell 390 s x (-1))
    (base : ∀ x : ℤ, |x| ≤ (t:ℤ) → cell 390 t x 0 = decide (|x|=(t:ℤ)))
    (edgeOdd : ∀ x : ℤ, (t:ℤ)-1 ≤ |x| → |x| ≤ (t:ℤ)+1 →
      cell 390 (t+1) x 0 = true)
    (edgeEven : ∀ x : ℤ, (t:ℤ)-2 ≤ |x| → |x| ≤ (t:ℤ)+2 →
      cell 390 (t+2) x 0 = decide (|x|=(t:ℤ)+2)) :
    (∀ x : ℤ, |x| ≤ (t:ℤ)+1 → cell 390 (t+1) x 0 = decide ((t:ℤ)-1 ≤ |x|)) ∧
    (∀ x : ℤ, |x| ≤ (t:ℤ)+2 → cell 390 (t+2) x 0 = decide (|x|=(t:ℤ)+2)) := by
  have hblank : ∀ x : ℤ, |x| < (t:ℤ) → cell 390 t x 0 = false := by
    intro x hx
    simp [base x hx.le, ne_of_lt hx]
  have hfirst := axis_blank_interval t t hblank (sym t)
  have hsecond := axis_blank_interval (t+1) ((t:ℤ)-1) hfirst (sym (t+1))
  constructor
  · intro x hx
    by_cases he : (t:ℤ)-1 ≤ |x|
    · simpa [he] using edgeOdd x he hx
    · simpa [he] using hfirst x (by omega)
  · intro x hx
    by_cases he : (t:ℤ)-2 ≤ |x|
    · exact edgeEven x he hx
    · have hne : |x| ≠ (t:ℤ)+2 := by omega
      simpa [hne] using hsecond x (by omega)

end Rule390

namespace Rule390
open OMA.S_oeis_a281735

/-- In the left-moving frame, the first twelve stages are followed by an eight-cycle. -/
private def edgePhase (t : ℕ) : ℕ := if t < 12 then t else 12 + (t-12)%8

private def edgeRow (s : ℕ) (u y : ℤ) : Bool :=
  if u < 0 ∨ y < -6 ∨ 6 < y then false
  else if s=0 then decide (u=0 ∧ y=0)
  else (0xc0820e0a0c08004000040004c0a0c0808302104000400001ace8a0e0a0c0c00440004000483a2c0808302000100400001040820e0a0c08404000040004e8a0c0808302044000400001a2e0a0e0a0c0c100400040004b392c0808302001110400001020c28e0a0c08000040040004000000008302000000000001 : ℕ).testBit
    (49*s + 7*u.toNat + y.natAbs)

private def edgeUpdate (s : ℕ) (u y : ℤ) : Bool :=
  (390 : ℕ).testBit ((edgeRow s (u-1) y).toNat + 2*((edgeRow s u y).toNat +
    (edgeRow s (u-2) y).toNat + (edgeRow s (u-1) (y+1)).toNat +
    (edgeRow s (u-1) (y-1)).toNat))

private theorem edge_transition (s : Fin 20) (u y : ℤ) (hu : u ≤ 6) :
    edgeUpdate s u y = edgeRow (if s.val=19 then 12 else s.val+1) u y := by
  by_cases inner : 0 ≤ u ∧ -7 ≤ y ∧ y ≤ 7
  · let i : Fin 7 := ⟨u.toNat,by omega⟩
    let j : Fin 15 := ⟨(y+7).toNat,by omega⟩
    have hi : (i:ℤ) = u := by dsimp [i]; omega
    have hj : (j:ℤ)-7 = y := by dsimp [j]; omega
    have checked (q : Fin 20) (v : Fin 7) : ∀ w : Fin 15,
        edgeUpdate q v ((w:ℤ)-7) = edgeRow (if q.val=19 then 12 else q.val+1) v ((w:ℤ)-7) := by
      fin_cases q <;> fin_cases v <;> decide +kernel
    simpa only [hi,hj] using checked s i j
  · have off (q : ℕ) (v z : ℤ) (h : v < 0 ∨ z < -6 ∨ 6 < z) : edgeRow q v z = false := if_pos h
    simp only [edgeUpdate, off _ _ _ (show u-1<0 ∨ y < -6 ∨ 6<y by omega),
      off _ _ _ (show u<0 ∨ y < -6 ∨ 6<y by omega),
      off _ _ _ (show u-2<0 ∨ y < -6 ∨ 6<y by omega),
      off _ _ _ (show u-1<0 ∨ y+1 < -6 ∨ 6<y+1 by omega),
      off _ _ _ (show u-1<0 ∨ y-1 < -6 ∨ 6<y-1 by omega)]
    rfl

private theorem edge_live (t : ℕ) (u y : ℤ) (hu : u ≤ 6) :
    cell 390 t (u-(t:ℤ)) y = edgeRow (edgePhase t) u y := by
  induction t generalizing u y with
  | zero =>
    simp only [edgePhase,show 0<12 by decide,if_true,edgeRow,Nat.cast_zero,sub_zero,cell]
    split_ifs with h
    · simp only [decide_eq_false_iff_not]; omega
    · rfl
  | succ t ih =>
    have hbound : edgePhase t < 20 := by unfold edgePhase; split <;> omega
    have hnext : edgePhase (t+1) = if edgePhase t=19 then 12 else edgePhase t+1 := by
      simp only [edgePhase]; split_ifs <;> omega
    rw [hnext,cell]
    dsimp only
    have ab : u-((t+1:ℕ):ℤ) = (u-1)-(t:ℤ) := by omega
    have ar : u-((t+1:ℕ):ℤ)+1 = u-(t:ℤ) := by omega
    have al : u-((t+1:ℕ):ℤ)-1 = (u-2)-(t:ℤ) := by omega
    rw [ar,al,ab,ih (u-1) y (by omega),ih u y hu,ih (u-2) y (by omega),
      ih (u-1) (y+1) (by omega),ih (u-1) (y-1) (by omega)]
    exact edge_transition ⟨_,hbound⟩ u y hu

/-- The outside cell is lit on even stages, and the first three cells are lit on odd stages. -/
theorem edge_axis (t : ℕ) (u : ℤ) (ht : 24 ≤ t) (hu0 : 0 ≤ u) (hu6 : u ≤ 6) :
    cell 390 t (u-(t:ℤ)) 0 = decide (u=0 ∨ (t%2=1 ∧ u≤2)) := by
  rw [edge_live t u 0 hu6]
  have hphase : edgePhase t = 12 + (t-12)%8 := if_neg (by omega)
  let s : Fin 8 := ⟨(t-12)%8,by omega⟩
  let i : Fin 7 := ⟨u.toNat,by omega⟩
  have hi : (i:ℤ)=u := by dsimp [i]; omega
  have hs : s.val%2=t%2 := by dsimp [s]; omega
  have checked : ∀ (a : Fin 8) (j : Fin 7), edgeRow (12+a.val) j 0 =
      decide ((j:ℤ)=0 ∨ (a.val%2=1 ∧ (j:ℤ)≤2)) := by decide +kernel
  simpa only [hphase,hi,hs] using checked s i

end Rule390

namespace Rule390
open OMA.S_oeis_a281735 Finset

/-- One quadrant per time step, with consecutive bits indexed by the y-coordinate. -/
private def table : ℕ → ℕ
  | 0 => 0x1
  | 1 => 0x4000003
  | 2 => 0x10000000000004
  | 3 => 0x4000003000001400000e
  | 4 => 0x100000000000000000008000011
  | 5 => 0x400000300000040000020000058000039
  | 6 => 0x1000000000000400000000000100000000000041
  | 7 => 0x4000003000001400000e000005000003800001440000e3
  | 8 => 0x10000000000000000000800000000000200000010000080000104
  | 9 => 0x40000030000004000002000001800000a000007400002b00005d400038e
  | 10 => 0x1000000000000400000000000000000008000004000000800011400000a8000401
  | 11 => 0x4000003000001400000e0000010000002000000800000c000044800039400015a8000e01
  | 12 => 0x1000000000000000000080000100000000000000000002000010000000880000040000828001001
  | 13 => 0x40000030000004000002000005800003a000004000000800004700003aa00005c80002240005c68003801
  | 14 => 0x10000000000004000000000001000000080000400000008000100000000000041000000000010040000a08004001
  | 15 => 0x4000003000001400000e000005000003a00001580000e000005180003820001440000e380005050003a8c0015b0800e001
  | 16 => 0x1000000000000000000080000000000020000004000008000000000002200000100000808000040000222800040000080a8010001
  | 17 => 0x40000030000004000002000001800000a000006000002600001d00000a800007300002b20001d58000a6800066680026a0005d1a8038001
  | 18 => 0x1000000000000400000000000000000008000000000000000000000000000000400000000000140000008000001000000080100000008028040001
  | 19 => 0x4000003000001400000e00000100000020000018000002000000000000000001000000e00000400000340000048000001a004005803a008015c0680e0001
  | 20 => 0x1000000000000000000080000100000000000000000002800000000000080000400000000000050000008000054000002a801010000080a0000000008a088100001
  | 21 => 0x40000030000004000002000005800003a000004000000a000006800000800001180000e200000400000d80001480000d4a00412a803a302005c5b002080a05db1d8380001
  | 22 => 0x1000000000000400000000000100000008000040000000000000000000a0000040000000000014000000080004040000088011450000828004004000080001001040080a00400001
  | 23 => 0x4000003000001400000e000005000003a00001580000e2000010000002800000b00000c800004000003620001508000e2c004408803967a01597800e0040051c5103a210e15c1b14e00003
  | 24 => 0x100000000000000000008000000000002000000400000880001000000028000000000022800001000000a8000114000082001040000080000000000082028001404022a88004041008aa089000000
  | 25 => 0x40000030000004000002000001800000a000006000002400005c80003a80000468000080000072800009000005e800019c004082003ac08005d00002280a01c20680a9c24066bd9024041a5caa19b800000
  | _ => 0

private def preview (t : ℕ) (x y : ℤ) : Bool :=
  if t=0 then decide (x=0 ∧ y=0)
  else if (t:ℤ) < |x|+|y| then false
  else (table t).testBit (26*x.natAbs+y.natAbs)

private theorem checked (t : Fin 25) (i : Fin 26) : ∀ j : Fin 26,
    step (preview t) i j = preview (t.val+1) i j := by
  fin_cases t <;> fin_cases i <;> decide +kernel

private theorem cell_abs (t : ℕ) (x y : ℤ) : cell 390 t |x| |y| = cell 390 t x y := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy <;>
    simp only [abs_of_nonneg,abs_of_nonpos,hx,hy,mirrorX,mirrorY]

private theorem preview_abs (t : ℕ) (x y : ℤ) : preview t |x| |y| = preview t x y := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy <;>
    simp [preview,abs_of_nonneg,abs_of_nonpos,hx,hy]

private theorem cell_preview (t : ℕ) (ht : t≤25) : cell 390 t = preview t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext x y
    rw [← cell_abs (t+1) x y,← preview_abs (t+1) x y]
    by_cases h : ((t+1:ℕ):ℤ) < |x|+|y|
    · rw [outside (t+1) _ _ (by simpa only [abs_abs] using h)]
      simp only [preview,Nat.succ_ne_zero,if_false,abs_abs,h,if_true]
    · have hx : x.natAbs < 26 := by
        have he := Int.natCast_natAbs x
        have hp := abs_nonneg y
        omega
      have hy : y.natAbs < 26 := by
        have he := Int.natCast_natAbs y
        have hp := abs_nonneg x
        omega
      rw [cell_step,ih (by omega)]
      simpa only [Int.natCast_natAbs] using
        checked ⟨t,by omega⟩ ⟨x.natAbs,hx⟩ ⟨y.natAbs,hy⟩

theorem base24 (x : ℤ) (hx : |x| < 24) : cell 390 24 x 0 = false := by
  rw [←cell_abs 24 x 0,abs_zero,cell_preview 24 (by decide)]
  have h : ∀ i : Fin 24, preview 24 i 0 = false := by decide +kernel
  have hi : x.natAbs < 24 := by have := Int.natCast_natAbs x; omega
  simpa only [Int.natCast_natAbs] using h ⟨x.natAbs,hi⟩

theorem axis24 (x : ℤ) (hx : |x| ≤ 24) : cell 390 24 x 0 = decide (|x|=24) := by
  rw [←cell_abs 24 x 0,abs_zero,cell_preview 24 (by decide)]
  have h : ∀ i : Fin 25, preview 24 i 0 = decide ((i:ℤ)=24) := by decide +kernel
  have hi : x.natAbs < 25 := by have := Int.natCast_natAbs x; omega
  simpa only [Int.natCast_natAbs] using h ⟨x.natAbs,hi⟩

theorem early_values (t : Fin 26) : a t =
    (![1,11,100,1110,10001,111001,1000001,11100011,100000100,1110001110,10000000001,111000000001,1000000000001,11100000000001,100000000000001,1110000000000001,10000000000000001,111000000000000001,1000000000000000001,11100000000000000001,100000000000000000001,1110000000000000000001,10000000000000000000001,111000000000000000000011,1000000000000000000000000,11100000000000000000000000] : Fin 26 → ℤ) t := by
  unfold a
  rw [cell_preview _ (by omega)]
  fin_cases t <;> decide +kernel

end Rule390

namespace Rule390

open OMA.S_oeis_a281735

/-- Reconstruct both axis words from a blank interior at stage 24 and the
moving edge strip through depth six at all subsequent times. -/
theorem axis_words_of
    (seed : ∀ x : ℤ, |x| < 24 → cell 390 24 x 0 = false)
    (edge : ∀ (t : ℕ) (u : ℤ), 24 ≤ t → 0 ≤ u → u ≤ 6 →
      cell 390 t (u-(t:ℤ)) 0 = decide (u=0 ∨ (t%2=1 ∧ u≤2))) :
    (∀ (h : ℕ), 12 ≤ h → ∀ k : ℕ, k ≤ 2*h →
      cell 390 (2*h) ((k:ℤ)-(2*h:ℕ)) 0 = decide (k=0)) ∧
    (∀ (h : ℕ), 12 ≤ h → ∀ k : ℕ, k ≤ 2*h+1 →
      cell 390 (2*h+1) ((k:ℤ)-(2*h+1:ℕ)) 0 = decide (k≤2)) := by
  have edgeAbs (t : ℕ) (ht : 24 ≤ t) (x : ℤ) (lo : (t:ℤ)-6 ≤ |x|) (hi : |x| ≤ (t:ℤ)) :
      cell 390 t x 0 = decide (|x|=(t:ℤ) ∨ (t%2=1 ∧ (t:ℤ)-2 ≤ |x|)) := by
    have sym : cell 390 t x 0 = cell 390 t (-|x|) 0 := by
      rcases le_total x 0 with hx | hx
      · simp [abs_of_nonpos hx]
      · rw [abs_of_nonneg hx, mirrorX]
    have h := edge t ((t:ℤ)-|x|) ht (by omega) (by omega)
    rw [sym, show -|x| = (t:ℤ)-|x|-t by ring, h]
    rw [decide_eq_decide]
    omega
  have symY (t : ℕ) (x : ℤ) : cell 390 t x 1 = cell 390 t x (-1) :=
    (mirrorY t x 1).symm
  let E (t : ℕ) := ∀ x : ℤ, |x| ≤ (t:ℤ) → cell 390 t x 0 = decide (|x|=(t:ℤ))
  have stepBoth (h : ℕ) (hh : 12 ≤ h) (base : E (2*h)) :
      (∀ x : ℤ, |x| ≤ (2*h+1:ℕ) → cell 390 (2*h+1) x 0 = decide ((2*h:ℕ)-1 ≤ |x|)) ∧
      E (2*h+2) := by
    have advance := axis_patterns_step (2*h) symY base
    have ho (x : ℤ) (lo : (2*h:ℕ)-1 ≤ |x|) (hi : |x| ≤ (2*h:ℕ)+1) :
        cell 390 (2*h+1) x 0 = true := by
      rw [edgeAbs (2*h+1) (by omega) x (by push_cast; omega) (by push_cast; omega)]
      apply decide_eq_true
      right
      constructor <;> push_cast <;> omega
    have he (x : ℤ) (lo : (2*h:ℕ)-2 ≤ |x|) (hi : |x| ≤ (2*h:ℕ)+2) :
        cell 390 (2*h+2) x 0 = decide (|x|=(2*h:ℕ)+2) := by
      have v := edgeAbs (2*h+2) (by omega) x (by push_cast; omega) (by push_cast; omega)
      simpa [show (2*h+2)%2 ≠ 1 by omega] using v
    specialize advance ho he
    dsimp only [E]
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using advance
  have ev (h : ℕ) (hh : 12 ≤ h) : E (2*h) := by
    induction h, hh using Nat.le_induction with
    | base =>
      intro x hx
      by_cases he : |x|=(24:ℤ)
      · have hv := edgeAbs 24 (by decide) x (by omega) (by omega)
        simpa [he] using hv
      · have hv := seed x (by change |x| ≤ 24 at hx; omega)
        simpa [he] using hv
    | succ h hh ih =>
      simpa only [Nat.mul_succ] using (stepBoth h hh ih).2
  constructor
  · intro h hh k hk
    have hneg : (k:ℤ)-(2*h:ℕ) ≤ 0 := sub_nonpos.mpr (by exact_mod_cast hk)
    have hhx : |(k:ℤ)-(2*h:ℕ)| ≤ (2*h:ℕ) := by rw [abs_of_nonpos hneg]; omega
    rw [ev h hh _ hhx, abs_of_nonpos hneg]
    rw [decide_eq_decide]
    omega
  · intro h hh k hk
    have hneg : (k:ℤ)-(2*h+1:ℕ) ≤ 0 := sub_nonpos.mpr (by exact_mod_cast hk)
    have hhx : |(k:ℤ)-(2*h+1:ℕ)| ≤ (2*h+1:ℕ) := by rw [abs_of_nonpos hneg]; omega
    rw [(stepBoth h hh (ev h hh)).1 _ hhx, abs_of_nonpos hneg]
    rw [decide_eq_decide]
    push_cast
    omega

end Rule390

namespace Rule390

open OMA.S_oeis_a281735

theorem axis_even (h : ℕ) (hh : 12 ≤ h) (k : ℕ) (hk : k ≤ 2*h) :
    cell 390 (2*h) ((k:ℤ)-(2*h:ℕ)) 0 = decide (k=0) :=
  (axis_words_of base24 edge_axis).1 h hh k hk

theorem axis_odd (h : ℕ) (hh : 12 ≤ h) (k : ℕ) (hk : k ≤ 2*h+1) :
    cell 390 (2*h+1) ((k:ℤ)-(2*h+1:ℕ)) 0 = decide (k≤2) :=
  (axis_words_of base24 edge_axis).2 h hh k hk

end Rule390

namespace Rule390
open OMA.S_oeis_a281735 PowerSeries Finset

def firstTerms : Fin 26 → ℤ := ![1, 11, 100, 1110, 10001, 111001, 1000001, 11100011, 100000100, 1110001110, 10000000001, 111000000001, 1000000000001, 11100000000001, 100000000000001, 1110000000000001, 10000000000000001, 111000000000000001, 1000000000000000001, 11100000000000000001, 100000000000000000001, 1110000000000000000001, 10000000000000000000001, 111000000000000000000011, 1000000000000000000000000, 11100000000000000000000000]

def value (n : ℕ) : ℤ := if hn : n<24 then firstTerms ⟨n,by omega⟩
  else if n%2=0 then 10^n else 111*10^(n-2)

theorem isolated_digit (n : ℕ)
    (bits : ∀ k : ℕ, k≤n → cell 390 n ((k:ℤ)-n) 0=decide (k=0)) :
    a n = (10:ℤ)^n := by
  calc
    a n = ∑ k ∈ range (n+1), if k=0 then (10:ℤ)^n else 0 := by
      apply sum_congr rfl
      intro k hk
      rw [bits k (by simpa using mem_range.mp hk)]
      by_cases h : k=0 <;> simp [h]
    _ = _ := by simp

theorem three_digits (n : ℕ) (hn : 2≤n)
    (bits : ∀ k : ℕ, k≤n → cell 390 n ((k:ℤ)-n) 0=decide (k≤2)) :
    a n = 111*(10:ℤ)^(n-2) := by
  have eqn : a n = (∑ k ∈ range (n+1), if k=0 then (10:ℤ)^n else 0) +
      (∑ k ∈ range (n+1), if k=1 then (10:ℤ)^(n-1) else 0) +
      (∑ k ∈ range (n+1), if k=2 then (10:ℤ)^(n-2) else 0) := by
    simp only [←sum_add_distrib]
    apply sum_congr rfl
    intro k hk
    rw [bits k (by simpa using mem_range.mp hk)]
    by_cases h : k≤2
    · interval_cases k <;> simp
    · simp (disch := omega) only [decide_eq_false, Bool.false_eq_true,if_false,if_neg,add_zero]
  rw [eqn]
  simp (disch := omega) only [sum_ite_eq',mem_range,if_pos]
  obtain ⟨q,rfl⟩ : ∃ q, n=q+2 := ⟨n-2,by omega⟩
  rw [show q+2-1=q+1 by omega,show q+2-2=q by omega,pow_add,pow_succ]
  ring

theorem value_rec (n : ℕ) (hn : 26≤n) : value n = 100*value (n-2) := by
  obtain ⟨q,rfl⟩ : ∃ q, n=q+26 := ⟨n-26,by omega⟩
  rw [show q+26-2=q+24 by omega]
  by_cases h : q%2=0
  · simp (disch := omega) only [value,dif_neg,if_pos]
    rw [show q+26=(q+24)+2 by omega,pow_add]
    ring
  · simp (disch := omega) only [value,dif_neg,if_neg]
    rw [show q+26-2=(q+24-2)+2 by omega,pow_add]
    ring

theorem all_values (hs : ∀ t : Fin 26, a t=firstTerms t)
    (he : ∀ h : ℕ, 12≤h → a (2*h)=(10:ℤ)^(2*h))
    (ho : ∀ h : ℕ, 12≤h → a (2*h+1)=111*(10:ℤ)^(2*h+1-2))
    (n : ℕ) : a n=value n := by
  by_cases hn : n<24
  · rw [value,dif_pos hn]
    exact hs ⟨n,by omega⟩
  · rw [value,dif_neg hn]
    rcases Nat.even_or_odd n with ⟨h,hh⟩ | ⟨h,hh⟩
    · rw [if_pos (by omega)]
      simpa only [show n=2*h by omega] using he h (by omega)
    · rw [if_neg (by omega),hh]
      exact ho h (by omega)

def gen : PowerSeries ℚ := PowerSeries.mk (fun n => (value n : ℚ))

theorem value_gf : gen*(100*X^2-1) = 1100 * X ^ 25 + 100 * X ^ 24 + 89 * X ^ 23 + 99 * X ^ 22 + 99 * X ^ 21 + 99 * X ^ 20 + 99 * X ^ 19 + 99 * X ^ 18 + 99 * X ^ 17 + 99 * X ^ 16 + 99 * X ^ 15 + 99 * X ^ 14 + 99 * X ^ 13 + 99 * X ^ 12 + 110999 * X ^ 11 + 9999 * X ^ 10 - 10 * X ^ 9 + 89 * X ^ 7 + 99 * X ^ 6 - X ^ 5 - X ^ 4 - 10 * X ^ 3 - 11 * X - 1 := by
  have den : gen*(100*X^2-1) = C 100*(gen*X^2)-gen := by simp only [map_ofNat]; ring
  have num : (1100 * X ^ 25 + 100 * X ^ 24 + 89 * X ^ 23 + 99 * X ^ 22 + 99 * X ^ 21 + 99 * X ^ 20 + 99 * X ^ 19 + 99 * X ^ 18 + 99 * X ^ 17 + 99 * X ^ 16 + 99 * X ^ 15 + 99 * X ^ 14 + 99 * X ^ 13 + 99 * X ^ 12 + 110999 * X ^ 11 + 9999 * X ^ 10 - 10 * X ^ 9 + 89 * X ^ 7 + 99 * X ^ 6 - X ^ 5 - X ^ 4 - 10 * X ^ 3 - 11 * X - 1 : PowerSeries ℚ) = C 1100 * X ^ 25 + C 100 * X ^ 24 + C 89 * X ^ 23 + C 99 * X ^ 22 + C 99 * X ^ 21 + C 99 * X ^ 20 + C 99 * X ^ 19 + C 99 * X ^ 18 + C 99 * X ^ 17 + C 99 * X ^ 16 + C 99 * X ^ 15 + C 99 * X ^ 14 + C 99 * X ^ 13 + C 99 * X ^ 12 + C 110999 * X ^ 11 + C 9999 * X ^ 10 - C 10 * X ^ 9 + C 89 * X ^ 7 + C 99 * X ^ 6 - X ^ 5 - X ^ 4 - C 10 * X ^ 3 - C 11 * X ^ 1 - C 1 := by
    simp only [map_ofNat,map_one,pow_one]
  rw [den,num]
  ext n
  simp only [map_sub,map_add,coeff_C_mul,coeff_mul_X_pow',coeff_C,coeff_X_pow,gen,coeff_mk]
  by_cases h : n<26
  · interval_cases n <;> decide +kernel
  · simp (disch := omega) only [if_pos,if_neg,add_zero,sub_zero]
    have hv : (value n : ℚ)=100*(value (n-2):ℚ) := by exact_mod_cast value_rec n (by omega)
    linarith only [hv]

theorem solve (av : ∀ n, a n=value n) : type_of% @OMA.S_oeis_a281735.main := by
  constructor
  · intro n hn
    simp only [av]
    exact_mod_cast value_rec n hn
  · simpa only [av,gen] using value_gf

end Rule390

open Rule390 in
theorem OMA.solution : type_of% @OMA.S_oeis_a281735.main := by
  apply solve
  apply all_values early_values
  · intro h hh
    exact isolated_digit _ (axis_even h hh)
  · intro h hh
    exact three_digits _ (by omega) (axis_odd h hh)
