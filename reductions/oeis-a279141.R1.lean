import OMAStatements.S_oeis_a279141

/-!
# Rule 137 and the decimal axis sequence A279141

Robert Price's sequence (https://oeis.org/A279141) records the horizontal
axis digits from the left edge to the origin, with the origin in the units place. Chai Wah Wu conjectured a linear
recurrence and a corresponding rational generating function.

The two remaining assertions concern the row immediately above the axis.
In the interior, one moving residue class must be dark at every stage.
At odd stages five classes modulo 24 must be lit. These are 21 of 144
space-time classes for the six-stage, 24-column interior pattern.

The diagonal alternates forever. A lit site of odd coordinate sum forces
all four neighbors to be lit. The entire strip at most fifteen cells behind
the advancing front repeats after sixteen stages, and its axis after eight.
These claims, the initial stages, and the transition from the sparse row
conditions to both decimal formulas are proved below.
-/

namespace OMA.R_oeis_a279141_R1
open OMA.S_oeis_a279141 Finset PowerSeries

/-- On each stage one residue of the row just above the horizontal axis is off. -/
def H1 : Prop := ∀ (t : ℕ) (x : ℤ), 24 ≤ t → 3 ≤ x → x+15 ≤ (t:ℤ) →
  (x+8*(t:ℤ)+1)%24=0 → cell 137 t x 1=false

/-- At odd stages five residues modulo twenty-four specify lit neighbors. -/
def H2 : Prop := ∀ (t : ℕ) (x : ℤ), 24 ≤ t → 3 ≤ x → x+15 ≤ (t:ℤ) → t%2=1 →
  (x%8=3 ∨ (x+8*(t:ℤ)+1)%24=2 ∨ (x+8*(t:ℤ)+1)%24=22) → cell 137 t x 1=true

theorem mirrorX (t : ℕ) (x y : ℤ) : cell 137 t (-x) y = cell 137 t x y := by
  induction t generalizing x y with
  | zero => simp only [cell,neg_eq_zero]
  | succ t ih =>
    simp only [cell,show -x+1 = -(x-1) by omega, show -x-1 = -(x+1) by omega,ih]
    ac_rfl

theorem mirrorY (t : ℕ) (x y : ℤ) : cell 137 t x (-y) = cell 137 t x y := by
  induction t generalizing x y with
  | zero => simp only [cell,neg_eq_zero]
  | succ t ih =>
    simp only [cell,show -y+1 = -(y-1) by omega, show -y-1 = -(y+1) by omega,ih]
    ac_rfl

theorem swap (t : ℕ) (x y : ℤ) : cell 137 t x y = cell 137 t y x := by
  induction t generalizing x y with
  | zero => simp only [cell,and_comm]
  | succ t ih =>
    simp only [cell]
    rw [ih x y,ih (x+1) y,ih (x-1) y,ih x (y+1),ih x (y-1)]
    ac_rfl

private theorem adjacent_abs (u v : ℤ) (hl : u-1≤v) (hr : v≤u+1) : |u| ≤ |v|+1 := by
  have hv := abs_le.mp (le_refl |v|)
  exact abs_le.mpr (by omega)

theorem outside (t : ℕ) (x y : ℤ) (h : (t:ℤ) < |x| + |y|) :
    cell 137 t x y = decide (t%2=1) := by
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
    rcases show t%2=0 ∨ t%2=1 by omega with h | h
    · simp [h,show (t+1)%2=1 by omega]
    · simp [h,show (t+1)%2=0 by omega]; decide

set_option maxHeartbeats 1800000 in
set_option maxRecDepth 8192 in
theorem local_rules :
    (∀ (t : ℕ) (x y : ℤ), (x+y)%2=1 → cell 137 t x y=true →
      cell 137 t (x+1) y=true ∧ cell 137 t (x-1) y=true ∧
      cell 137 t x (y+1)=true ∧ cell 137 t x (y-1)=true) ∧
    (∀ (t : ℕ) (x : ℤ), cell 137 t x x =
      if x=0 then decide (t%2=0) else decide (t%2=1)) ∧
    (∀ t : ℕ, cell 137 t 1 0 = false) ∧
    (∀ (t : ℕ) (x : ℤ), cell 137 (t+1) x 0 =
      if x%2=0 then !cell 137 t x 0 || (cell 137 t (x-1) 0 ^^ cell 137 t (x+1) 0)
      else !(cell 137 t (x-1) 0 || cell 137 t (x+1) 0 || cell 137 t x 1)) := by
  let step (f : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
    (137 : ℕ).testBit ((f x y).toNat + 2*((f (x+1) y).toNat +
      (f (x-1) y).toNat + (f x (y+1)).toNat + (f x (y-1)).toNat))

  have cell_step (t : ℕ) : cell 137 (t+1) = step (cell 137 t) := rfl

  /- A live odd site forces all of its even neighbors to be live. -/
  let dominated (f : ℤ → ℤ → Bool) : Prop :=
    ∀ x y : ℤ, (x+y)%2=1 → f x y=true →
      f (x+1) y=true ∧ f (x-1) y=true ∧ f x (y+1)=true ∧ f x (y-1)=true

  have dark_even_neighbors {f : ℤ → ℤ → Bool} (h : dominated f) (x y : ℤ)
      (hp : (x+y)%2=0) (hc : f x y=false) :
      f (x+1) y=false ∧ f (x-1) y=false ∧ f x (y+1)=false ∧ f x (y-1)=false := by
    have ea := h (x+1) y (by omega)
    have we := h (x-1) y (by omega)
    have no := h x (y+1) (by omega)
    have so := h x (y-1) (by omega)
    simp only [add_sub_cancel_right,sub_add_cancel,hc] at ea we no so
    grind

  have dark_even_birth {f : ℤ → ℤ → Bool} (h : dominated f) (x y : ℤ)
      (hp : (x+y)%2=0) (hc : f x y=false) : step f x y=true := by
    obtain ⟨e,w,n,s⟩ := dark_even_neighbors h x y hp hc
    simp only [step,hc,e,w,n,s]
    decide

  have odd_birth_neighbors {f : ℤ → ℤ → Bool} (h : dominated f) (x y : ℤ)
      (hp : (x+y)%2=1) : step f x y=true ↔
        f (x+1) y=false ∧ f (x-1) y=false ∧ f x (y+1)=false ∧ f x (y-1)=false := by
    cases hc : f x y with
    | false =>
      unfold step
      rw [hc]
      cases f (x+1) y <;> cases f (x-1) y <;> cases f x (y+1) <;> cases f x (y-1) <;> decide
    | true =>
      obtain ⟨e,w,n,s⟩ := h x y hp hc
      simp only [step,hc,e,w,n,s]
      decide

  have domination_preserved {f : ℤ → ℤ → Bool} (h : dominated f) : dominated (step f) := by
    intro x y hp hc
    obtain ⟨e,w,n,s⟩ := (odd_birth_neighbors h x y hp).mp hc
    exact ⟨dark_even_birth h _ _ (by omega) e,dark_even_birth h _ _ (by omega) w,
      dark_even_birth h _ _ (by omega) n,dark_even_birth h _ _ (by omega) s⟩

  have cell_dominated (t : ℕ) : dominated (cell 137 t) := by
    induction t with
    | zero =>
      intro x y hp on
      change decide (x=0 ∧ y=0)=true at on
      obtain ⟨rfl,rfl⟩ := of_decide_eq_true on
      norm_num at hp
    | succ t ih => exact domination_preserved ih

  /- On a diagonal the four neighbors occur in equal pairs, so no live cell survives. -/
  have diagonal_flip (t : ℕ) (x : ℤ) : cell 137 (t+1) x x = !cell 137 t x x := by
    rw [cell_step]
    cases h : cell 137 t x x with
    | false => exact dark_even_birth (cell_dominated t) x x (by omega) h
    | true =>
      unfold step
      rw [h,swap t (x+1) x,swap t (x-1) x]
      cases cell 137 t x (x+1) <;> cases cell 137 t x (x-1) <;> decide

  have diagonal_phase (t : ℕ) (x : ℤ) :
      cell 137 t x x = if x=0 then decide (t%2=0) else decide (t%2=1) := by
    induction t with
    | zero => by_cases h : x=0 <;> simp [cell,h]
    | succ t ih =>
      rw [diagonal_flip,ih]
      by_cases hx : x=0 <;> rcases show t%2=0 ∨ t%2=1 by omega with hp|hp <;>
        simp [hx,hp,show (t+1)%2=1-t%2 by omega]

  have first_axis_off (t : ℕ) : cell 137 t 1 0 = false := by
    cases h : cell 137 t 1 0 with
    | false => rfl
    | true =>
      obtain ⟨_,w,n,_⟩ := cell_dominated t 1 0 (by decide) h
      change cell 137 t 0 0 = true at w
      change cell 137 t 1 1 = true at n
      rw [diagonal_phase] at w n
      simp at w n
      omega

  let axisNext (x : ℤ) (c l r u : Bool) : Bool :=
    if x%2=0 then !c || (l ^^ r) else !(l || r || u)

  /- Reflection cancels the two transverse contributions in the parity test for survival. -/
  have native_axis_update (t : ℕ) (x : ℤ) :
      cell 137 (t+1) x 0 = axisNext x (cell 137 t x 0) (cell 137 t (x-1) 0)
        (cell 137 t (x+1) 0) (cell 137 t x 1) := by
    rw [cell_step]
    unfold axisNext
    by_cases hp : x%2=0
    · rw [if_pos hp]
      cases hc : cell 137 t x 0 with
      | false => simpa using dark_even_birth (cell_dominated t) x 0 (by simpa using hp) hc
      | true =>
        unfold step
        simp only [hc,zero_add,zero_sub,mirrorY t x 1]
        cases cell 137 t (x-1) 0 <;> cases cell 137 t (x+1) 0 <;> cases cell 137 t x 1 <;> decide
    · rw [if_neg hp]
      apply Bool.eq_iff_iff.mpr
      rw [odd_birth_neighbors (cell_dominated t) x 0 (by omega)]
      simp [mirrorY t x 1,and_comm,and_left_comm]
  exact ⟨cell_dominated, diagonal_phase, first_axis_off, native_axis_update⟩

private theorem seed_cell_abs (t : ℕ) (x y : ℤ) : cell 137 t |x| |y| = cell 137 t x y := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy <;>
    simp only [abs_of_nonneg,abs_of_nonpos,hx,hy,mirrorX,mirrorY]


set_option maxRecDepth 8192 in
set_option maxHeartbeats 2800000 in
theorem initial_certificate :
    (
      let bandMask (p r : ℕ) : ℕ :=
        match p, r with
        | 0, 0 => 68507093 | 0, 1 => 33718400 | 0, _ => 89608273
        | 1, 0 => 29360448 | 1, 1 => 11152042 | 1, _ => 329476
        | 2, 0 => 89510933 | 2, 1 => 41976320 | 2, _ => 122705233
        | 3, 0 => 82368 | 3, 1 => 36350122 | 3, _ => 84344836
        | 4, 0 => 97785173 | 4, 1 => 8520320 | 4, _ => 5592913
        | _, 0 => 21086208 | _, 1 => 44608042 | _, _ => 117441796

      let bandCol (x : ℤ) : ℕ :=
        (if |x| < 3 then |x| else 3+(|x|-3)%24).toNat

      let band (t : ℕ) (x y : ℤ) : Bool :=
        (bandMask (t%6) y.natAbs).testBit (bandCol x)
      ∀ (t : ℕ), 24 ≤ t → t ≤ 28 → ∀ (x y : ℤ), 0 ≤ x → 0 ≤ y → y ≤ 2 →
        x+14 ≤ (t:ℤ) → cell 137 t x y = band t x y) ∧
    (∀ n : ℕ, n<16 → a n = ([1,0,101,0,10101,0,1010101,0,
  101011101,10100,10101000001,11100,1010111010101,101000000,
  101010000010101,111000000] : List ℤ).getD n 0) ∧
    (∀ n : ℕ, 16 ≤ n → n ≤ 35 → a n = -a (n-1) + a (n-3) + a (n-4) + 100000000*a (n-8) +
    100000000*a (n-9) - 100000000*a (n-11) - 100000000*a (n-12)) := by
  let step (f : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
    (137 : ℕ).testBit ((f x y).toNat + 2*((f (x+1) y).toNat +
    (f (x-1) y).toNat + (f x (y+1)).toNat + (f x (y-1)).toNat))
  have cell_step (t : ℕ) : cell 137 (t+1) = step (cell 137 t) := rfl
  let table (t : ℕ) : ℕ := match t with
    | 0 => 0x1
    | 1 => 0x0
    | 2 => 0x1000000000000000005
    | 3 => 0x2000000000
    | 4 => 0x1000000000000000001000000000000000015
    | 5 => 0x600000000c00000000a000000000
    | 6 => 0x1000000000000000005000000002000000011000000008000000055
    | 7 => 0x2000000000000000008000000004000000022000000000
    | 8 => 0x100000000000000000100000000000000000500000000300000001100000000800000015d
    | 9 => 0x600000000c00000001a00000003100000006a0000000c50000000aa000000014
    | 10 => 0x1000000000000000005000000002000000001000000000000000004000000000000000110000000080000000541
    | 11 => 0x200000000000000001800000003c00000007a0000000f10000000eb00000004700000022e00000001c
    | 12 => 0x10000000000000000010000000000000000150000000030000000050000000000000001050000000000000001510000000800000015d5
    | 13 => 0x600000000c00000000a00000000100000006a0000000f10000000fa0000000700000006aa000000c04000000aaa000000140
    | 14 => 0x1000000000000000005000000002000000011000000008000000054000000000000000104000000008000000505000000220000001151000000800000005415
    | 15 => 0x20000000000000000080000000040000000220000000010000000ab0000000710000002e200000005000000088a0000004040000022aa0000001c0
    | 16 => 0x1000000000000000001000000000000000005000000003000000011000000008000000055000000022000000115000000088000000545000000220000001151000000880000015d55
    | 17 => 0x600000000c00000001a00000003100000006a0000000c50000001a2000000300000000688000000c40000001a2200000301000000688a00000c40400000aa2a000001400
    | 18 => 0x10000000000000000050000000020000000010000000000000000040000000000000000100000000080000000550000000230000001150000000880000005450000002200000111510000080800000541d5
    | 19 => 0x200000000000000001800000003c00000007a0000000f10000001eb0000003c70000007a2000000f01000001e8a000003c41000007a2200000f01000000e88a000004404000022eaa000001d40
    | 20 => 0x100000000000000000100000000000000001500000000300000000500000000000000000500000000000000001500000000a00000005400000002000000011400000008800001054500000022000001555100000820000015d415
    | 21 => 0x600000000c00000000a00000000100000006a0000000f10000001fa0000003f00000007ea000000fc0000001fa0000003f01000007e8b00000fc4100000fa2200000701000006a88a0000c00040000aa8aa0000141c0
    | 22 => 0x100000000000000000500000000200000001100000000800000005400000000000000000400000000800000000500000000000000001500000000e000000055000000022000010115000000088000050545000022220000115751000080280000541555
    | 23 => 0x20000000000000000080000000040000000220000000010000001ab0000003f10000007e2000000ff0000001fea000003fc4000007faa00000ff0400000fe88000007c4000002fa22000005010000088a8a00004050400022aa2a00001c000
    | 24 => 0x100000000000000000100000000000000000500000000300000001100000000800000015500000002200000005500000002800000001500000000000000001100000000000001005100000002300001411500000a0880000555450000220200001150510000880800015d55d5
    | 25 => 0x600000000c00000001a00000003100000006a0000000c50000000a2000000000000000688000000f00000001f82000003fc0000007fea00000ffc400000ffae000007f0500006be8a0000c1c410001a0a22000300010000688a8a000c40704000aa2aaa000140140
    | 26 => 0x100000000000000000500000000200000000100000000000000000400000000000000011000000008800000055500000002300000007500000003800000001500000002000001001500000000a00005005400002002000001411400000e88800005754500002222000111555100080820000541d415
    | 27 => 0x200000000000000001800000003c00000007a0000000f10000000eb000000047000000222000000001000001aaa000003f41000007f8a00000ffd000000ff8a000007fc000002ffa0000007f0100018be8b0003c54410007a8222000f01010000e8a88a0004400040022ea8aa0001d41c0
    | 28 => 0x100000000000000000100000000000000001500000000300000000500000000000000010500000000000000015500000008a0000015540000002000000004140000000200000100450000000a000001405500000800e000150055000020822000051515000002888001054545000020220001555751000820280015d41555
    | 29 => 0x600000000c00000000a00000000100000006a0000000f10000000fa0000000700000006aa000000c00000000a200000000010000068ab00000f1c100000fb8a000007f1000006be0a0000c1f040000a3faa00000770400068e288000f04040000fa8222000701010006a8aa8a00c00050400aa8aa2a00141c000
    | 30 => 0x100000000000000000500000000200000001100000000800000005400000000000000010400000000800000050500000022000000115500000088e0000055550000002820000104550000000200000504450000202e0000115051000088880000550051000028a23001055d150000828880050545450022200200115750510080280800541555d5
    | 31 => 0x20000000000000000080000000040000000220000000010000000ab0000000710000002e200000005000000088a00000040400000222a00000000400000a82800000710000002fb8a00000715000008a8aa00004054400022222e000007505000a8288a000701441002e28a220005010100088aaa8a004050704022aa2aaa001c00140
    | 32 => 0x10000000000000000010000000000000000050000000030000000110000000080000000550000000220000001150000000880000005450000002200000011510000008800000055d1000002283000010555000008aa000005050500002220000011501500008a88a00055505400023a22000115411400088208800545454500220022001150555100880820015d55d415
    | 33 => 0x600000000c00000001a00000003100000006a0000000c50000001a2000000300000000688000000c40000001a2200000301000000688a00000c40400001a2ae0000301450000688aa0000c50010001a200a0003050500006888ea000c40540001a202200030105010068a888b00c411c4101a228a220301010100688aa88a0c40700040aa2aa8aa0140141c0
    | 34 => 0x100000000000000000500000000200000000100000000000000000400000000000000001000000000800000005500000002300000011500000008800000054500000022000000115500000080a000005414000002200000010754000008fa00000507450000222a000011705500008f88e000547055000202a22001145515000882888005454545002220220111555751080820280541d41555
    | 35 => 0x200000000000000001800000003c00000007a0000000f10000001eb0000003c70000007a2000000f01000001e8a000003c41000007a2200000f01000001e88a00003c40000007a2a00000f01c10001e8aab0003c50010007a288a000f05010001e8aa0a003c40504007a28a2a00f01050401e8ba08803c41004007a2282220f01010100e888aa8a04400050422ea8aa2a01d41c000
    | _ => 0
  let preview (t : ℕ) (x y : ℤ) : Bool :=
    if t=0 then decide (x=0 ∧ y=0)
    else if (t:ℤ) < |x|+|y| then decide (t%2=1)
    else (table t).testBit (36*x.natAbs+y.natAbs)
  have checked (t : Fin 35) (i : Fin 36) : ∀ j : Fin 36,
      step (preview t) i j = preview (t.val+1) i j := by
    fin_cases t <;> fin_cases i <;> decide +kernel
  have preview_abs (t : ℕ) (x y : ℤ) : preview t |x| |y| = preview t x y := by
    rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy <;>
      simp [preview,abs_of_nonneg,abs_of_nonpos,hx,hy]

  have cell_preview (t : ℕ) (ht : t≤35) : cell 137 t = preview t := by
    induction t with
    | zero => rfl
    | succ t ih =>
      funext x y
      rw [← seed_cell_abs (t+1) x y,← preview_abs (t+1) x y]
      by_cases h : ((t+1:ℕ):ℤ) < |x|+|y|
      · rw [outside (t+1) _ _ (by simpa only [abs_abs] using h)]
        simp only [preview,Nat.succ_ne_zero,if_false,abs_abs,h,if_true]
      · have hx : x.natAbs < 36 := by
          have he := Int.natCast_natAbs x
          have hp := abs_nonneg y
          omega
        have hy : y.natAbs < 36 := by
          have he := Int.natCast_natAbs y
          have hp := abs_nonneg x
          omega
        rw [cell_step,ih (by omega)]
        simpa only [Int.natCast_natAbs] using
          checked ⟨t,by omega⟩ ⟨x.natAbs,hx⟩ ⟨y.natAbs,hy⟩

  have early_values (t : Fin 36) : a t = (![1,0,101,0,10101,0,1010101,0,101011101,10100,10101000001,11100,1010111010101,101000000,101010000010101,111000000,10101110101010101,1010000000000,1010100000111010101,1110101000000,101011101010000010101,10100000111000000,10101000001010101010101,11100000000000000,1010111010101010111010101,101000000000101000000,101010000011101010000010101,111010100000111000000,10101110101000001010101010101,1010000011100000000000000,1010100000101010101010111010101,1110000000000000101000000,101011101010101011101010000010101,10100000000010100000111000000,10101000001110101000001010101010101,11101010000011100000000000000] : Fin 36 → ℤ) t := by
    unfold a
    rw [cell_preview _ (by omega)]
    fin_cases t <;> decide +kernel
  refine ⟨?_,?_,?_⟩
  · intro bandMask bandCol band t ht he x y hx0 hy0 hy2 hx
    have check (s : Fin 5) : ∀ (i : Fin 15) (j : Fin 3), i.val+14 ≤ s.val+24 →
        preview (s.val+24) i j = band (s.val+24) i j := by
      fin_cases s <;> decide +kernel
    let i : Fin 15 := ⟨x.toNat,by omega⟩
    let j : Fin 3 := ⟨y.toNat,by omega⟩
    have hi : (i:ℤ) = x := by dsimp [i]; omega
    have hj : (j:ℤ) = y := by dsimp [j]; omega
    have hs : t-24+24=t := by omega
    have v := check ⟨t-24,by omega⟩ i j (by dsimp [i]; omega)
    rw [cell_preview _ (by omega)]
    simpa only [hs,hi,hj] using v
  · intro n hn
    have eq := early_values ⟨n,by omega⟩
    change a n = _ at eq
    rw [eq]
    interval_cases n <;> rfl
  · intro n hl hu
    have eq (i : ℕ) (h : i < 36) : a i = _ := early_values ⟨i,h⟩
    simp (disch := omega) only [eq]
    interval_cases n <;> rfl

theorem edge_certificate :
    (let bandMask (p r : ℕ) : ℕ :=
       match p, r with
       | 0, 0 => 68507093 | 0, 1 => 33718400 | 0, _ => 89608273
       | 1, 0 => 29360448 | 1, 1 => 11152042 | 1, _ => 329476
       | 2, 0 => 89510933 | 2, 1 => 41976320 | 2, _ => 122705233
       | 3, 0 => 82368 | 3, 1 => 36350122 | 3, _ => 84344836
       | 4, 0 => 97785173 | 4, 1 => 8520320 | 4, _ => 5592913
       | _, 0 => 21086208 | _, 1 => 44608042 | _, _ => 117441796
     let bandCol (x : ℤ) : ℕ :=
       (if |x| < 3 then |x| else 3+(|x|-3)%24).toNat
     let band (t : ℕ) (x y : ℤ) : Bool :=
       (bandMask (t%6) y.natAbs).testBit (bandCol x)
     ∀ (t : ℕ) (u y : ℤ), 24 ≤ t → (14 ≤ u ∧ u ≤ 15) → (0 ≤ y ∧ y ≤ 2) →
       cell 137 t ((t:ℤ)-u) y = band t ((t:ℤ)-u) y) ∧
    (∀ (t : ℕ) (u : ℤ), 16 ≤ t → (0 ≤ u ∧ u ≤ 15) →
      cell 137 (t+8) (((t+8:ℕ):ℤ)-u) 0 = cell 137 t ((t:ℤ)-u) 0) ∧
    (∀ (t : ℕ) (u y : ℤ), 16 ≤ t → u ≤ 15 →
      cell 137 (t+16) (((t+16:ℕ):ℤ)-u) y = cell 137 t ((t:ℤ)-u) y) := by
  let bandMask (p r : ℕ) : ℕ :=
    match p, r with
    | 0, 0 => 68507093 | 0, 1 => 33718400 | 0, _ => 89608273
    | 1, 0 => 29360448 | 1, 1 => 11152042 | 1, _ => 329476
    | 2, 0 => 89510933 | 2, 1 => 41976320 | 2, _ => 122705233
    | 3, 0 => 82368 | 3, 1 => 36350122 | 3, _ => 84344836
    | 4, 0 => 97785173 | 4, 1 => 8520320 | 4, _ => 5592913
    | _, 0 => 21086208 | _, 1 => 44608042 | _, _ => 117441796
  let bandCol (x : ℤ) : ℕ :=
    (if |x| < 3 then |x| else 3+(|x|-3)%24).toNat
  let band (t : ℕ) (x y : ℤ) : Bool :=
    (bandMask (t%6) y.natAbs).testBit (bandCol x)
  have band_congr {s t : ℕ} {u v : ℤ} (y : ℤ) (st : s%6=t%6) (hu : 3≤u)
      (hv : 3≤v) (uv : u%24=v%24) : band s u y = band t v y := by
    have ab : (u-3)%24=(v-3)%24 := by omega
    simp [band,bandCol,st, abs_of_nonneg (by omega : 0≤u), abs_of_nonneg (by omega : 0≤v),
      not_lt.mpr hu,not_lt.mpr hv,ab]
  let edgePhase (t : ℕ) : ℕ := if t < 16 then t else 16 + (t-16)%16
  let edgeFrames : Array ℕ := #[
    0x1,
    0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffcfffe,
    0x10000000500000001,
    0xfffffffffffffffffffffffffffffffffffffffefffcfffafff0fffafffcfffe,
    0x100000001000000150000000100000001,
    0xfffffffffffffffffffffffefffcfffefffcffeaffc0ffeafffcfffefffcfffe,
    0x1000000050002001100080055000800110002000500000001,
    0xfffffffefffcfffafff0ffe8ffc4ffa2ff00ffa2ffc4ffe8fff0fffafffcfffe,
    0x100000005000300110008015d00080011000300050000000100000001,
    0xfffcfffafff1ffeaffc5feaafc14feaaffc5ffeafff1fffafffcfffefffcfffe,
    0x400000110008005410080011000000004000000010002000500000001,
    0xfff1feebfc47fa2ef01cfa2efc47feebfff1fffafffcfff8fff0fffafffcfffe,
    0x151008015d5008001510000010500000005000300150000000100000001,
    0xfc04eaaac140eaaafc04feaafc70fefafff1ffeaffc1ffeafffcfffefffcfffe,
    0x800541508001151022005050008010400000054000800110002000500000001,
    0x1c0a2aac404e88af050fae2fc71feabff01ffa2ffc4ffe8fff0fffafffcfffe,
    0x880115102200545008801150022005500080011000300050000000100000001,
    0xc404e88af010fa22fc40fe88ff00ffa2ffc5ffeafff1fffafffcfffefffcfffe,
    0x220054500880115002300550008001000000004000000010002000500000001,
    0xf010fa22fc41fe8aff01ffa2ffc7ffebfff1fffafffcfff8fff0fffafffcfffe,
    0x88011400200054000a00150000000500000005000300150000000100000001,
    0xfc41fe8bff01ffa0ffc0ffeafff0fffafff1ffeaffc1ffeafffcfffefffcfffe,
    0x220055000e0015000000050008000400000054000800110002000500000001,
    0xff04ffaaffc4ffeafff0ffe2fff1ffabff01ffa2ffc4ffe8fff0fffafffcfffe,
    0x1100000015002800550022015500080011000300050000000100000001,
    0xffc4ffeaffc0ff82ff00fe88fc00fea2ffc5ffeafff1fffafffcfffefffcfffe,
    0x20001500380075002305550088011000000004000000010002000500000001,
    0xffd0ff8aff41faaaf001fa22fc47feebfff1fffafffcfff8fff0fffafffcfffe,
    0x20041402001554008a01550000010500000005000300150000000100000001,
    0xf1c1e8abc001ea20fc00feaafc70fefafff1ffeaffc1ffeafffcfffefffcfffe,
    0x2825555088e1155022005050008010400000054000800110002000500000001,
    0x4a22ac404e88af050fae2fc71feabff01ffa2ffc4ffe8fff0fffafffcfffe]
  let edgeRow (s : ℕ) (u y : ℤ) : Bool :=
    if u < 0 ∨ y < -15 ∨ 15 < y then decide (s%2=1)
    else if s=0 then decide (u=0 ∧ y=0)
    else edgeFrames[s]!.testBit (16*u.toNat + y.natAbs)
  let edgeUpdate (s : ℕ) (u y : ℤ) : Bool :=
    (137 : ℕ).testBit ((edgeRow s (u-1) y).toNat + 2*((edgeRow s (u-2) y).toNat +
      (edgeRow s u y).toNat + (edgeRow s (u-1) (y+1)).toNat +
      (edgeRow s (u-1) (y-1)).toNat))
  have edge_transition (s : Fin 32) (u y : ℤ) (hu : u ≤ 15) :
      edgeUpdate s u y = edgeRow (if s.val=31 then 16 else s.val+1) u y := by
    by_cases inner : 0 ≤ u ∧ -16 ≤ y ∧ y ≤ 16
    · let i : Fin 16 := ⟨u.toNat,by omega⟩
      let j : Fin 33 := ⟨(y+16).toNat,by omega⟩
      have hi : (i:ℤ) = u := by dsimp [i]; omega
      have hj : (j:ℤ)-16 = y := by dsimp [j]; omega
      have checked (q : Fin 32) : ∀ (v : Fin 16) (w : Fin 33),
          edgeUpdate q v ((w:ℤ)-16) = edgeRow (if q.val=31 then 16 else q.val+1) v ((w:ℤ)-16) := by
        fin_cases q <;> decide +kernel
      simpa only [hi,hj] using checked s i j
    · have off (q : ℕ) (v z : ℤ) (h : v < 0 ∨ z < -15 ∨ 15 < z) : edgeRow q v z = decide (q%2=1) := if_pos h
      simp only [edgeUpdate, off _ _ _ (show u-1<0 ∨ y < -15 ∨ 15<y by omega),
        off _ _ _ (show u<0 ∨ y < -15 ∨ 15<y by omega),
        off _ _ _ (show u-2<0 ∨ y < -15 ∨ 15<y by omega),
        off _ _ _ (show u-1<0 ∨ y+1 < -15 ∨ 15<y+1 by omega),
        off _ _ _ (show u-1<0 ∨ y-1 < -15 ∨ 15<y-1 by omega)]
      fin_cases s <;> decide
  have edge_live (t : ℕ) (u y : ℤ) (hu : u ≤ 15) :
      cell 137 t ((t:ℤ)-u) y = edgeRow (edgePhase t) u y := by
    induction t generalizing u y with
    | zero =>
      simp only [edgePhase,show 0<16 by decide,if_true,edgeRow,Nat.cast_zero,zero_sub,cell,neg_eq_zero]
      split_ifs with h
      · change decide (_ = 0 ∧ _ = 0) = false
        apply decide_eq_false; omega
      · rfl
    | succ t ih =>
      have hbound : edgePhase t < 32 := by unfold edgePhase; split <;> omega
      have hnext : edgePhase (t+1) = if edgePhase t=31 then 16 else edgePhase t+1 := by
        simp only [edgePhase]; split_ifs <;> omega
      rw [hnext,cell]
      dsimp only
      have ab : ((t+1:ℕ):ℤ)-u = (t:ℤ)-(u-1) := by omega
      have ar : ((t+1:ℕ):ℤ)-u+1 = (t:ℤ)-(u-2) := by omega
      have al : ((t+1:ℕ):ℤ)-u-1 = (t:ℤ)-u := by omega
      rw [ar,al,ab,ih (u-1) y (by omega),ih u y hu,ih (u-2) y (by omega),
        ih (u-1) (y+1) (by omega),ih (u-1) (y-1) (by omega)]
      exact edge_transition ⟨_,hbound⟩ u y hu
  have front_move (t : ℕ) (u : ℤ) (ht : 16≤t) (hu : 0≤u ∧ u≤15) :
      cell 137 (t+8) (((t+8:ℕ):ℤ)-u) 0 = cell 137 t ((t:ℤ)-u) 0 := by
    rw [edge_live (t+8) u 0 hu.2,edge_live t u 0 hu.2]
    let v : Fin 16 := ⟨u.toNat,by omega⟩
    let q : Fin 16 := ⟨(t-16)%16,by omega⟩
    have hv : (v:ℤ) = u := by dsimp [v]; omega
    have h1 : edgePhase t = 16+q.val := if_neg (by omega)
    have h2 : edgePhase (t+8) = 16+(q.val+8)%16 := by
      unfold edgePhase
      rw [if_neg (by omega)]
      dsimp [q]; omega
    have checked : ∀ (p j : Fin 16), edgeRow (16+(p.val+8)%16) j 0 = edgeRow (16+p.val) j 0 := by
      decide +kernel
    simpa only [h1,h2,hv] using checked q v
  have edge_band (t : ℕ) (u y : ℤ) (ht : 24 ≤ t) (hu : 14 ≤ u ∧ u ≤ 15)
      (hy : 0 ≤ y ∧ y ≤ 2) :
      cell 137 t ((t:ℤ)-u) y = band t ((t:ℤ)-u) y := by
    rw [edge_live t u y (by omega)]
    let p : Fin 48 := ⟨(t-24)%48,by omega⟩
    let i : Fin 2 := ⟨(u-14).toNat,by omega⟩
    let j : Fin 3 := ⟨y.toNat,by omega⟩
    have hi : 14+(i:ℤ)=u := by dsimp [i]; omega
    have hj : (j:ℤ)=y := by dsimp [j]; omega
    have he : edgePhase t=edgePhase (24+p.val) := by unfold edgePhase; dsimp [p]; split_ifs <;> omega
    have test : ∀ (a : Fin 48) (v : Fin 2) (z : Fin 3),
        edgeRow (edgePhase (24+a.val)) (14+(v:ℤ)) z =
          band (24+a.val) (((24+a.val:ℕ):ℤ)-(14+(v:ℤ))) z := by decide +kernel
    calc
      _ = band (24+p.val) (((24+p.val:ℕ):ℤ)-u) y := by simpa only [he,hi,hj] using test p i j
      _ = _ := by
        have hrep : t = (24+p.val)+48*((t-24)/48) := by dsimp [p]; omega
        have hc : (t:ℤ) = ((24+p.val:ℕ):ℤ)+48*((((t-24)/48:ℕ):ℤ)) := by exact_mod_cast hrep
        apply band_congr y <;> omega
  refine ⟨edge_band,front_move,?_⟩
  intro t u y ht hu
  rw [edge_live (t+16) u y hu,edge_live t u y hu]
  congr 1
  unfold edgePhase
  split_ifs <;> omega

set_option maxHeartbeats 1800000 in
set_option maxRecDepth 8192 in
theorem central_model (off : H1) (on : H2)
    (seed_band : (
    /- Time runs through six phases. Each mask encodes the three central positions
    and one spatial period of 24 positions. -/
    let bandMask (p r : ℕ) : ℕ :=
      match p, r with
      | 0, 0 => 68507093 | 0, 1 => 33718400 | 0, _ => 89608273
      | 1, 0 => 29360448 | 1, 1 => 11152042 | 1, _ => 329476
      | 2, 0 => 89510933 | 2, 1 => 41976320 | 2, _ => 122705233
      | 3, 0 => 82368 | 3, 1 => 36350122 | 3, _ => 84344836
      | 4, 0 => 97785173 | 4, 1 => 8520320 | 4, _ => 5592913
      | _, 0 => 21086208 | _, 1 => 44608042 | _, _ => 117441796

    let bandCol (x : ℤ) : ℕ :=
      (if |x| < 3 then |x| else 3+(|x|-3)%24).toNat

    let band (t : ℕ) (x y : ℤ) : Bool :=
      (bandMask (t%6) y.natAbs).testBit (bandCol x)
    ∀ (t : ℕ), 24 ≤ t → t ≤ 28 → ∀ (x y : ℤ), 0 ≤ x → 0 ≤ y → y ≤ 2 → x+14 ≤ (t:ℤ) → cell 137 t x y = band t x y))
    (edge_band : (
    /- Time runs through six phases. Each mask encodes the three central positions
    and one spatial period of 24 positions. -/
    let bandMask (p r : ℕ) : ℕ :=
      match p, r with
      | 0, 0 => 68507093 | 0, 1 => 33718400 | 0, _ => 89608273
      | 1, 0 => 29360448 | 1, 1 => 11152042 | 1, _ => 329476
      | 2, 0 => 89510933 | 2, 1 => 41976320 | 2, _ => 122705233
      | 3, 0 => 82368 | 3, 1 => 36350122 | 3, _ => 84344836
      | 4, 0 => 97785173 | 4, 1 => 8520320 | 4, _ => 5592913
      | _, 0 => 21086208 | _, 1 => 44608042 | _, _ => 117441796

    let bandCol (x : ℤ) : ℕ :=
      (if |x| < 3 then |x| else 3+(|x|-3)%24).toNat

    let band (t : ℕ) (x y : ℤ) : Bool :=
      (bandMask (t%6) y.natAbs).testBit (bandCol x)
    ∀ (t : ℕ) (u y : ℤ), 24 ≤ t → (14 ≤ u ∧ u ≤ 15) → (0 ≤ y ∧ y ≤ 2) → cell 137 t ((t:ℤ)-u) y = band t ((t:ℤ)-u) y)) :
    /- Time runs through six phases. Each mask encodes the three central positions
    and one spatial period of 24 positions. -/
    let bandMask (p r : ℕ) : ℕ :=
      match p, r with
      | 0, 0 => 68507093 | 0, 1 => 33718400 | 0, _ => 89608273
      | 1, 0 => 29360448 | 1, 1 => 11152042 | 1, _ => 329476
      | 2, 0 => 89510933 | 2, 1 => 41976320 | 2, _ => 122705233
      | 3, 0 => 82368 | 3, 1 => 36350122 | 3, _ => 84344836
      | 4, 0 => 97785173 | 4, 1 => 8520320 | 4, _ => 5592913
      | _, 0 => 21086208 | _, 1 => 44608042 | _, _ => 117441796

    let bandCol (x : ℤ) : ℕ :=
      (if |x| < 3 then |x| else 3+(|x|-3)%24).toNat

    let band (t : ℕ) (x y : ℤ) : Bool :=
      (bandMask (t%6) y.natAbs).testBit (bandCol x)
    ∀ (t : ℕ) (x : ℤ), 24≤t → |x|+14 ≤ (t:ℤ) → cell 137 t x 0 = band t x 0 := by
  intro bandMask bandCol band
  have diagonal_phase := local_rules.2.1
  have band_period (t : ℕ) (x y : ℤ) : band (t+6) x y = band t x y := by
    simp [band]

  have band_reflect (t : ℕ) (x y : ℤ) : band t (-x) y = band t x y := by
    simp [band,bandCol]

  have band_congr {s t : ℕ} {u v : ℤ} (y : ℤ) (st : s%6=t%6) (hu : 3≤u)
      (hv : 3≤v) (uv : u%24=v%24) : band s u y = band t v y := by
    have ab : (u-3)%24=(v-3)%24 := by omega
    simp [band,bandCol,st, abs_of_nonneg (by omega : 0≤u), abs_of_nonneg (by omega : 0≤v),
      not_lt.mpr hu,not_lt.mpr hv,ab]

  have band_move (t : ℕ) (x : ℤ) (hx : 1 ≤ x) : band (t+8) (x+8) 0 = band t x 0 := by
    let r : Fin 6 := ⟨t%6,by omega⟩
    let i : Fin 26 := ⟨(if x<3 then x-1 else 2+(x-3)%24).toNat,by split <;> omega⟩
    have val : ∀ (a : Fin 6) (b : Fin 26), band (a.val+8) ((b.val:ℤ)+1+8) 0 = band a.val ((b.val:ℤ)+1) 0 := by decide +kernel
    have congr₁ : band t x 0 = band r.val ((i.val:ℤ)+1) 0 := by
      by_cases h : x<3
      · have hx' : (i.val:ℤ)+1=x := by dsimp [i]; rw [if_pos h]; omega
        simp [hx',band,r]
      · apply band_congr <;> (try dsimp [i,r]) <;> (try simp only [if_neg h]) <;> omega
    have congr₂ : band (t+8) (x+8) 0 = band (r.val+8) ((i.val:ℤ)+1+8) 0 := by
      apply band_congr <;> (try dsimp [i,r]) <;> (try split_ifs) <;> omega
    exact congr₂.trans ((val r i).trans congr₁.symm)

  let axisNext (x : ℤ) (c l r u : Bool) : Bool :=
    if x%2=0 then !c || (l ^^ r) else !(l || r || u)
  have native_axis_update (t : ℕ) (x : ℤ) : cell 137 (t+1) x 0 =
      axisNext x (cell 137 t x 0) (cell 137 t (x-1) 0) (cell 137 t (x+1) 0)
      (cell 137 t x 1) := local_rules.2.2.2 t x
  have model_axis_update (t : ℕ) (x : ℤ) (hx : 0≤x) :
      band (t+1) x 0 = axisNext x (band t x 0) (band t (x-1) 0)
        (band t (x+1) 0) (band t x 1) := by
    let u : ℤ := if x≤3 then x else 4+(x-4)%24
    let r : Fin 6 := ⟨t%6,by omega⟩
    let i : Fin 28 := ⟨u.toNat,by dsimp [u]; split <;> omega⟩
    have hu : (i:ℤ) = u := by dsimp [i,u]; split <;> omega
    have aux (d y : ℤ) (s : ℕ) (hl : -1≤d) (hr : d≤1) :
        band (t+s) (x+d) y = band (r.val+s) ((i:ℤ)+d) y := by
      rw [hu]
      by_cases h : x≤3
      · simp [u,h,band,r,Nat.add_mod]
      · apply band_congr
        · dsimp [r]; omega
        · omega
        · dsimp [u]; rw [if_neg h]; omega
        · dsimp [u]; rw [if_neg h]; omega
    have P : x%2=(i:ℤ)%2 := by rw [hu]; dsimp [u]; split <;> omega
    have cert : ∀ (q : Fin 6) (v : Fin 28), band (q.val+1) v 0 =
        axisNext v (band q.val v 0) (band q.val ((v:ℤ)-1) 0)
          (band q.val ((v:ℤ)+1) 0) (band q.val v 1) := by decide +kernel
    have v := cert r i
    simp only [axisNext] at v ⊢
    rw [P]
    have e₁ := aux 0 0 1 (by decide) (by decide)
    have c := aux 0 0 0 (by decide) (by decide)
    have l := aux (-1) 0 0 (by decide) (by decide)
    have rr := aux 1 0 0 (by decide) (by decide)
    have up := aux 0 1 0 (by decide) (by decide)
    simp only [add_zero,←sub_eq_add_neg] at e₁ c l rr up
    rw [e₁,c,l,rr,up]
    exact v

  have stable_axis_sparse
      (cap : ∀ (t : ℕ) (x : ℤ), 24 ≤ t → 3 ≤ x → x+15 ≤ (t:ℤ) → x%2=1 →
        band t (x-1) 0=false → band t (x+1) 0=false → cell 137 t x 1=band t x 1)
      (t : ℕ) (x : ℤ) (ht : 24≤t) (hx : |x|+14≤(t:ℤ)) : cell 137 t x 0 = band t x 0 := by
    suffices H : ∀ (t : ℕ), 24 ≤ t → ∀ x : ℤ, |x|+14 ≤ (t:ℤ) → cell 137 t x 0 = band t x 0
        from H t ht x hx
    clear t x ht hx
    intro t
    induction t with
    | zero => omega
    | succ t ih =>
      intro ht x hx
      have pos (u : ℤ) (hu : 0≤u) (hw : u+14≤((t+1:ℕ):ℤ)) :
          cell 137 (t+1) u 0 = band (t+1) u 0 := by
        by_cases small : t+1≤28
        · exact seed_band _ ht small _ _ hu le_rfl (by decide) hw
        by_cases near : ((t+1:ℕ):ℤ)-u≤15
        · have he := edge_band (t+1) (((t+1:ℕ):ℤ)-u) 0 ht ⟨by omega,near⟩ ⟨le_rfl,by decide⟩
          simpa only [sub_sub_cancel] using he
        have h (j : ℤ) (h₁ : u-1≤j) (h₂ : j≤u+1) : cell 137 t j 0 = band t j 0 := by
          apply ih (by omega)
          have hj : |j| ≤ (t:ℤ)-14 := abs_le.mpr (by constructor <;> omega)
          omega
        rw [native_axis_update,model_axis_update t u hu,h _ (by omega) (by omega),
          h (u-1) (by omega) (by omega),h (u+1) (by omega) (by omega)]
        unfold axisNext
        split
        · rfl
        · rename_i hop
          cases hl : band t (u-1) 0 <;> cases hr : band t (u+1) 0 <;> simp only [Bool.or_false,Bool.false_or,Bool.true_or]
          apply congrArg Bool.not
          by_cases h3 : 3 ≤ u
          · exact cap t u (by omega) h3 (by omega) (by omega) hl hr
          · have one : u=1 := by omega
            subst u
            rw [diagonal_phase]
            have v : ∀ q : Fin 6, band q.val 1 1 = decide (q.val%2=1) := by decide +kernel
            simpa [band,show t%6%2=t%2 by omega] using (v ⟨t%6,by omega⟩).symm
      rcases le_total 0 x with hp|hn
      · apply pos x hp
        simpa only [abs_of_nonneg hp] using hx
      · rw [←mirrorX _ x 0,←band_reflect _ x 0]
        apply pos (-x) (by omega)
        simpa only [abs_of_nonpos hn] using hx

  /- Only 21 of 144 time/space residues read the northern neighbor.
  Six require an off cell and fifteen require an on cell. -/
  have sparse_cap_of_signs
      (off : ∀ (t : ℕ) (x : ℤ), 24 ≤ t → 3 ≤ x → x+15 ≤ (t:ℤ) →
        ((t%2=0 ∧ (x-4*(t:ℤ)+1)%24=0) ∨ (t%2=1 ∧ (x-4*(t:ℤ)+1)%24=12)) →
        cell 137 t x 1=false)
      (on : ∀ (t : ℕ) (x : ℤ), 24 ≤ t → 3 ≤ x → x+15 ≤ (t:ℤ) →
        t%2=1 → (x-4*(t:ℤ)+1)%24 ∈ ([0,8,10,14,16] : List ℤ) → cell 137 t x 1=true)
      (t : ℕ) (x : ℤ) (ht : 24 ≤ t) (hx : 3 ≤ x) (hd : x+15 ≤ (t:ℤ))
      (hp : x%2=1) (hl : band t (x-1) 0=false) (hr : band t (x+1) 0=false) :
      cell 137 t x 1=band t x 1 := by
    let u : ℤ := if x=3 then 3 else 4+(x-4)%24
    let r : Fin 6 := ⟨t%6,by omega⟩
    let i : Fin 28 := ⟨u.toNat,by dsimp [u]; split <;> omega⟩
    have hu : (i:ℤ) = u := by dsimp [i,u]; split <;> omega
    have aux (d y : ℤ) (lo : -1≤d) : band t (x+d) y = band r.val ((i:ℤ)+d) y := by
      rw [hu]
      by_cases h : x=3
      · simp [h,u,band,r]
      · apply band_congr
        · simp [r]
        · omega
        · dsimp [u]; rw [if_neg h]; omega
        · dsimp [u]; rw [if_neg h]; omega
    have tr : t%2=r.val%2 := by dsimp [r]; omega
    have ir : x%24=(i:ℤ)%24 := by rw [hu]; dsimp [u]; split <;> omega
    have z : (x-4*(t:ℤ)+1)%24 = ((i:ℤ)-4*(r.val:ℤ)+1)%24 := by dsimp [r]; omega
    have li := aux (-1) 0 (by decide)
    have ri := aux 1 0 (by decide)
    have ui := aux 0 1 (by decide)
    simp only [add_zero,←sub_eq_add_neg] at li ri ui
    rw [li] at hl
    rw [ri] at hr
    rw [ui]
    have cert : ∀ (p : Fin 6) (v : Fin 28), 3≤v.val → v.val%2=1 →
        band p.val ((v:ℤ)-1) 0=false → band p.val ((v:ℤ)+1) 0=false →
        (let s := ((v:ℤ)-4*(p.val:ℤ)+1)%24
         (((p.val%2=0 ∧ s=0) ∨ (p.val%2=1 ∧ s=12)) ∧ band p.val v 1=false) ∨
         ((p.val%2=1 ∧ s∈([0,8,10,14,16] : List ℤ)) ∧ band p.val v 1=true)) := by
      decide +kernel
    have imin : 3 ≤ i.val := by dsimp [i,u]; split <;> omega
    rcases cert r i imin (by omega) hl hr with ⟨cond,v⟩ | ⟨⟨p,cond⟩,v⟩
    · rw [v]; apply off t x ht hx hd; simpa only [z,tr] using cond
    · rw [v]; apply on t x ht hx hd (tr.trans p); simpa only [z] using cond

  /- One moving off residue and three moving on residues suffice for the axis. -/
  have sparse_cap_of_residues
      (off : ∀ (t : ℕ) (x : ℤ), 24 ≤ t → 3 ≤ x → x+15 ≤ (t:ℤ) →
        (x+8*(t:ℤ)+1)%24=0 → cell 137 t x 1=false)
      (on : ∀ (t : ℕ) (x : ℤ), 24 ≤ t → 3 ≤ x → x+15 ≤ (t:ℤ) → t%2=1 →
        (x%8=3 ∨ (x+8*(t:ℤ)+1)%24=2 ∨ (x+8*(t:ℤ)+1)%24=22) → cell 137 t x 1=true)
      (t : ℕ) (x : ℤ) (ht : 24 ≤ t) (hx : 3 ≤ x) (hd : x+15 ≤ (t:ℤ))
      (hp : x%2=1) (hl : band t (x-1) 0=false) (hr : band t (x+1) 0=false) :
      cell 137 t x 1=band t x 1 := by
    apply sparse_cap_of_signs _ _ t x ht hx hd hp hl hr
    · intro s u hs hu hb h
      exact off s u hs hu hb (by omega)
    · intro s u hs hu hb ho h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      exact on s u hs hu hb ho (by omega)
  exact stable_axis_sparse (sparse_cap_of_residues off on)

set_option maxHeartbeats 1800000 in
set_option maxRecDepth 8192 in
theorem decimal_consequence
    (stable : (
    /- Time runs through six phases. Each mask encodes the three central positions
    and one spatial period of 24 positions. -/
    let bandMask (p r : ℕ) : ℕ :=
      match p, r with
      | 0, 0 => 68507093 | 0, 1 => 33718400 | 0, _ => 89608273
      | 1, 0 => 29360448 | 1, 1 => 11152042 | 1, _ => 329476
      | 2, 0 => 89510933 | 2, 1 => 41976320 | 2, _ => 122705233
      | 3, 0 => 82368 | 3, 1 => 36350122 | 3, _ => 84344836
      | 4, 0 => 97785173 | 4, 1 => 8520320 | 4, _ => 5592913
      | _, 0 => 21086208 | _, 1 => 44608042 | _, _ => 117441796

    let bandCol (x : ℤ) : ℕ :=
      (if |x| < 3 then |x| else 3+(|x|-3)%24).toNat

    let band (t : ℕ) (x y : ℤ) : Bool :=
      (bandMask (t%6) y.natAbs).testBit (bandCol x)
    ∀ (t : ℕ) (x : ℤ), 24≤t → |x|+14 ≤ (t:ℤ) → cell 137 t x 0 = band t x 0))
    (front_move : ∀ (t : ℕ) (u : ℤ), 16≤t → (0≤u ∧ u≤15) → cell 137 (t+8) (((t+8:ℕ):ℤ)-u) 0=cell 137 t ((t:ℤ)-u) 0)
    (initial_checked : ∀ n : ℕ, n<16 → a n = ([1,0,101,0,10101,0,1010101,0,
  101011101,10100,10101000001,11100,1010111010101,101000000,
  101010000010101,111000000] : List ℤ).getD n 0)
    (relation_checked : ∀ n : ℕ, 16≤n → n≤35 → a n = -a (n-1) + a (n-3) + a (n-4) + 100000000*a (n-8) +
    100000000*a (n-9) - 100000000*a (n-11) - 100000000*a (n-12)) :
    type_of% @OMA.S_oeis_a279141.main := by
  /- Time runs through six phases. Each mask encodes the three central positions
  and one spatial period of 24 positions. -/
  let bandMask (p r : ℕ) : ℕ :=
    match p, r with
    | 0, 0 => 68507093 | 0, 1 => 33718400 | 0, _ => 89608273
    | 1, 0 => 29360448 | 1, 1 => 11152042 | 1, _ => 329476
    | 2, 0 => 89510933 | 2, 1 => 41976320 | 2, _ => 122705233
    | 3, 0 => 82368 | 3, 1 => 36350122 | 3, _ => 84344836
    | 4, 0 => 97785173 | 4, 1 => 8520320 | 4, _ => 5592913
    | _, 0 => 21086208 | _, 1 => 44608042 | _, _ => 117441796

  let bandCol (x : ℤ) : ℕ :=
    (if |x| < 3 then |x| else 3+(|x|-3)%24).toNat

  let band (t : ℕ) (x y : ℤ) : Bool :=
    (bandMask (t%6) y.natAbs).testBit (bandCol x)

  have band_period (t : ℕ) (x y : ℤ) : band (t+6) x y = band t x y := by
    simp [band]

  have band_reflect (t : ℕ) (x y : ℤ) : band t (-x) y = band t x y := by
    simp [band,bandCol]

  have band_congr {s t : ℕ} {u v : ℤ} (y : ℤ) (st : s%6=t%6) (hu : 3≤u)
      (hv : 3≤v) (uv : u%24=v%24) : band s u y = band t v y := by
    have ab : (u-3)%24=(v-3)%24 := by omega
    simp [band,bandCol,st, abs_of_nonneg (by omega : 0≤u), abs_of_nonneg (by omega : 0≤v),
      not_lt.mpr hu,not_lt.mpr hv,ab]

  have band_move (t : ℕ) (x : ℤ) (hx : 1 ≤ x) : band (t+8) (x+8) 0 = band t x 0 := by
    let r : Fin 6 := ⟨t%6,by omega⟩
    let i : Fin 26 := ⟨(if x<3 then x-1 else 2+(x-3)%24).toNat,by split <;> omega⟩
    have val : ∀ (a : Fin 6) (b : Fin 26), band (a.val+8) ((b.val:ℤ)+1+8) 0 = band a.val ((b.val:ℤ)+1) 0 := by decide +kernel
    have congr₁ : band t x 0 = band r.val ((i.val:ℤ)+1) 0 := by
      by_cases h : x<3
      · have hx' : (i.val:ℤ)+1=x := by dsimp [i]; rw [if_pos h]; omega
        simp [hx',band,r]
      · apply band_congr <;> (try dsimp [i,r]) <;> (try simp only [if_neg h]) <;> omega
    have congr₂ : band (t+8) (x+8) 0 = band (r.val+8) ((i.val:ℤ)+1+8) 0 := by
      apply band_congr <;> (try dsimp [i,r]) <;> (try split_ifs) <;> omega
    exact congr₂.trans ((val r i).trans congr₁.symm)

  let initial (n : ℕ) : ℤ := ([1,0,101,0,10101,0,1010101,0,
    101011101,10100,10101000001,11100,1010111010101,101000000,
    101010000010101,111000000] : List ℤ).getD n 0

  let relation (n : ℕ) : Prop :=
    a n = -a (n-1) + a (n-3) + a (n-4) + 100000000*a (n-8) +
      100000000*a (n-9) - 100000000*a (n-11) - 100000000*a (n-12)

  let d (n : ℕ) : ℤ := a (n+8)-100000000*a n

  have recurrence_of_difference (B : ℕ)
      (small : ∀ n : ℕ, 16 ≤ n → n < B+12 → relation n)
      (late : ∀ n : ℕ, B ≤ n → d (n+4)+d (n+3)-d (n+1)-d n = 0) :
      ∀ n : ℕ, 16 ≤ n → relation n := by
    intro n hn
    by_cases h : n < B+12
    · exact small n hn h
    · obtain ⟨k,rfl⟩ : ∃ k, n=k+12 := ⟨n-12,by omega⟩
      have eq := late k (by omega)
      unfold d at eq
      unfold relation
      simp only [show k+12-1=k+11 by omega, show k+12-3=k+9 by omega,
        show k+12-4=k+8 by omega,show k+12-8=k+4 by omega,
        show k+12-9=k+3 by omega,show k+12-11=k+1 by omega,
        show k+12-12=k by omega]
      linarith only [eq]

  have finish (early : ∀ n : ℕ, n<16 → a n=initial n)
      (rec : ∀ n : ℕ, 16 ≤ n → relation n) : type_of% @OMA.S_oeis_a279141.main := by
    have recur (n : ℕ) (hn : 16 ≤ n) :
        (a n:ℚ) = -(a (n-1):ℚ) + a (n-3) + a (n-4) + 100000000*a (n-8) +
          100000000*a (n-9) - 100000000*a (n-11) - 100000000*a (n-12) := by
      exact_mod_cast rec n hn
    refine ⟨?_,?_⟩
    · intro n hn
      exact_mod_cast rec n hn
    · let F : PowerSeries ℚ := mk (fun n => (a n : ℚ))
      have den : F*(100000000*X^12 + 100000000*X^11 - 100000000*X^9 -
          100000000*X^8 - X^4 - X^3 + X + 1) =
          C 100000000*(F*X^12) + C 100000000*(F*X^11) -
          C 100000000*(F*X^9) - C 100000000*(F*X^8) - F*X^4 - F*X^3 + F*X^1 + F := by
        simp only [map_ofNat,pow_one]
        ring
      have num : (-11100*X^15 - 1000*X^14 + 111000000*X^13 + 10000000*X^12 +
          11100*X^9 + 1001000*X^8 + 1000000*X^7 + 1010000*X^6 +
          10000*X^5 + 10100*X^4 + 100*X^3 + 101*X^2 + X + 1 : PowerSeries ℚ) =
          C (-11100)*X^15 - C 1000*X^14 + C 111000000*X^13 + C 10000000*X^12 +
          C 11100*X^9 + C 1001000*X^8 + C 1000000*X^7 + C 1010000*X^6 +
          C 10000*X^5 + C 10100*X^4 + C 100*X^3 + C 101*X^2 + C 1*X^1 + C 1 := by
        simp only [map_neg,map_ofNat,map_one,pow_one,one_mul]
      change F*_ = _
      rw [den,num]
      ext n
      simp only [map_add,map_sub,coeff_C_mul,coeff_mul_X_pow',coeff_C,F,coeff_mk]
      by_cases hn : n<16
      · interval_cases n <;> norm_num [early,initial]
      · simp (disch := omega) only [if_pos,if_neg,sub_zero,add_zero]
        linarith only [recur n (by omega)]

  /- The low nine decimal places come from a six-stage cycle near the center. -/
  let centralBit (t k : ℕ) : Bool := ([469,320,21,448,341,0] : List ℕ)[t%6]!.testBit k

  let correction (t : ℕ) : ℤ :=
    (∑ k ∈ range 9, if centralBit (t+8) k then (10:ℤ)^k else 0) -
    100000000*(if centralBit t 0 then 1 else 0)

  have corr_period (n : ℕ) : correction n = correction (n%6) := by
    have h : (n+8)%6=(n%6+8)%6 := by omega
    unfold correction centralBit
    rw [h,Nat.mod_mod]

  have correction_rec (n : ℕ) :
      correction (n+4)+correction (n+3)-correction (n+1)-correction n = 0 := by
    have chk : ∀ p : Fin 6,
        correction ((p.val+4)%6)+correction ((p.val+3)%6)-correction ((p.val+1)%6)-correction p.val = 0 := by
      decide +kernel
    rw [corr_period (n+4),corr_period (n+3),corr_period (n+1),corr_period n]
    simpa only [show (n%6+4)%6=(n+4)%6 by omega,show (n%6+3)%6=(n+3)%6 by omega,
      show (n%6+1)%6=(n+1)%6 by omega] using chk ⟨n%6,by omega⟩

  let digit (t k : ℕ) : ℤ := if cell 137 t k 0 then 10^k else 0

  have axis_sum (n : ℕ) : a n = ∑ k ∈ range (n+1), digit n k := by
    rw [a,←sum_range_reflect (digit n) (n+1)]
    apply sum_congr rfl
    intro k hk
    have hk' : k ≤ n := Nat.le_of_lt_succ (mem_range.mp hk)
    have eq : (k:ℤ)-n = -((n-k:ℕ):ℤ) := by omega
    rw [eq,mirrorX]
    simp only [Nat.add_sub_cancel,digit]

  /- When positive positions translate eight cells in eight stages, all the
  high decimal weights cancel, leaving just the two central contributions. -/
  have word_step (t : ℕ)
      (shift : ∀ k : ℕ, 1 ≤ k → k ≤ t → cell 137 (t+8) ((k:ℤ)+8) 0 = cell 137 t k 0)
      (old : cell 137 t 0 0 = centralBit t 0)
      (low : ∀ k : ℕ, k<9 → cell 137 (t+8) k 0 = centralBit (t+8) k) :
      d t = correction t := by
    have eq : ∀ k ∈ range t, digit (t+8) (9+k) = 100000000*digit t (1+k) := by
      intro k hk
      have hs := shift (1+k) (by omega) (by have := mem_range.mp hk; omega)
      have pos : (((9+k : ℕ):ℤ)) = ((1+k:ℕ):ℤ)+8 := by omega
      simp only [digit,pos,hs]
      split_ifs
      · rw [show 9+k = (1+k)+8 by omega,pow_add]; ring
      · ring
    have small : (∑ k ∈ range 9, digit (t+8) k) =
        ∑ k ∈ range 9, if centralBit (t+8) k then (10:ℤ)^k else 0 := by
      apply sum_congr rfl
      intro k hk
      simp only [digit,low k (mem_range.mp hk)]
    unfold d
    rw [axis_sum,axis_sum,show t+8+1=9+t by omega,show t+1=1+t by omega,
      sum_range_add,sum_range_add,small,sum_congr rfl eq,←mul_sum]
    simp only [sum_range_one,digit,Nat.cast_zero,old,pow_zero,correction]
    ring
  have centers (t k : ℕ) (ht : 24≤t) (hk : k<9) : cell 137 t k 0 = centralBit t k := by
    rw [stable t k ht (by rw [abs_of_nonneg (Int.natCast_nonneg k)]; omega)]
    have h : ∀ (p : Fin 6) (j : Fin 9), band p j 0 = centralBit p j := by decide +kernel
    simpa only [centralBit,band,Nat.mod_mod] using h ⟨t%6,by omega⟩ ⟨k,hk⟩
  have d_eq (t : ℕ) (ht : 24≤t) : d t = correction t := by
    apply word_step
    · intro k hpos hk
      by_cases inside : k+14≤t
      · have h1 : |(k:ℤ)|=(k:ℤ) := abs_of_nonneg (by positivity)
        have h2 : |(k:ℤ)+8|=(k:ℤ)+8 := abs_of_nonneg (by positivity)
        rw [stable (t+8) _ (by omega) (by rw [h2]; omega),
          stable t _ ht (by rw [h1]; omega)]
        exact band_move t (k:ℤ) (by omega)
      · have he := front_move t ((t:ℤ)-k) (by omega) ⟨by omega,by omega⟩
        simpa only [show ((t+8:ℕ):ℤ)-((t:ℤ)-k)=(k:ℤ)+8 by omega,
          sub_sub_cancel] using he
    · simpa only [Nat.cast_zero] using centers t 0 ht (by decide)
    · exact fun k hk => centers (t+8) k (by omega) hk
  apply finish initial_checked
  apply recurrence_of_difference 24
  · exact fun n lo hi => relation_checked n lo (by omega)
  · intro n hn
    rw [d_eq (n+4) (by omega),d_eq (n+3) (by omega),d_eq (n+1) (by omega),d_eq n hn]
    exact correction_rec n

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a279141.main := by
  intro off on
  obtain ⟨seed, small, early⟩ := initial_certificate
  obtain ⟨edge, shift, _⟩ := edge_certificate
  exact decimal_consequence (central_model off on seed edge) shift small early

end OMA.R_oeis_a279141_R1
