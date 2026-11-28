import OMAStatements.S_oeis_a281284


/-!
# Rule 350 and the four-step evolution of its binary axis

Chai Wah Wu proposed the recurrence and generating function in Robert
Price's A281284, https://oeis.org/A281284. We certify a time-periodic band
on the first three rows, with six exceptional central columns and a
period-four spatial continuation. A finite band in moving coordinates also
enters a four-cycle. On comparing binary words four stages apart, the
settled prefix cancels against sixteen times its earlier value. The
remaining low bits are periodic, which yields the conjectured recurrence.
The initial values and both bands are checked against the native rule.
-/

namespace Rule350
open OMA.S_oeis_a281284

def step (f : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  (350 : ℕ).testBit ((f x y).toNat + 2*((f (x+1) y).toNat +
    (f (x-1) y).toNat + (f x (y+1)).toNat + (f x (y-1)).toNat))

theorem cell_step (t : ℕ) : cell 350 (t+1) = step (cell 350 t) := rfl

end Rule350

namespace Rule350
open OMA.S_oeis_a281284

theorem mirrorX (t : ℕ) (x y : ℤ) : cell 350 t (-x) y = cell 350 t x y := by
  induction t generalizing x y with
  | zero => simp only [cell,neg_eq_zero]
  | succ t ih =>
    simp only [cell,show -x+1 = -(x-1) by omega, show -x-1 = -(x+1) by omega,ih]
    ac_rfl

theorem mirrorY (t : ℕ) (x y : ℤ) : cell 350 t x (-y) = cell 350 t x y := by
  induction t generalizing x y with
  | zero => simp only [cell,neg_eq_zero]
  | succ t ih =>
    simp only [cell,show -y+1 = -(y-1) by omega, show -y-1 = -(y+1) by omega,ih]
    ac_rfl

theorem swap (t : ℕ) (x y : ℤ) : cell 350 t x y = cell 350 t y x := by
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
    cell 350 t x y = false := by
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

end Rule350

namespace Rule350
open OMA.S_oeis_a281284 Finset

/-- One quadrant per time step, with consecutive bits indexed by the y-coordinate. -/
private def table : ℕ → ℕ
  | 0 => 0x1
  | 1 => 0x20000000003
  | 2 => 0x400000000060000000006
  | 3 => 0x8000000000c0000000008000000000d
  | 4 => 0x1000000000180000000018000000001e000000001b
  | 5 => 0x2000000000300000000020000000002400000000200000000034
  | 6 => 0x40000000006000000000600000000078000000007c000000007a000000006e
  | 7 => 0x8000000000c00000000080000000009000000000800000000080000000008600000000d3
  | 8 => 0x1000000000180000000018000000001e000000001f000000001c800000001cc00000001e800000001bc
  | 9 => 0x2000000000300000000020000000002400000000200000000020000000002300000000238000000021e0000000342
  | 10 => 0x40000000006000000000600000000078000000007c0000000072000000007600000000748000000074400000007a000000006ed
  | 11 => 0x8000000000c00000000080000000009000000000800000000080000000008e000000008f000000008f800000008ec000000087a0000000d3f
  | 12 => 0x1000000000180000000018000000001e000000001f000000001c800000001dc00000001d000000001d000000001d000000001d100000001e840000001bc0
  | 13 => 0x2000000000300000000020000000002400000000200000000020000000002300000000230000000023e0000000238000000023a000000023b8000000214e0000003422
  | 14 => 0x40000000006000000000600000000078000000007c0000000072000000007600000000758000000074c000000074000000007470000000747000000074640000007bb00000006ed5
  | 15 => 0x8000000000c00000000080000000009000000000800000000080000000008e000000008d000000008e000000008f000000008ee00000008e800000008e880000008f9c000000844a000000d32f
  | 16 => 0x1000000000180000000018000000001e000000001f000000001c800000001dc00000001d000000001d300000001d180000001d0c0000001d100000001d1f0000001d1f8000001d060000001ebb4000001bdd8
  | 17 => 0x2000000000300000000020000000002400000000200000000020000000002300000000230000000023e000000023c000000023a000000023b000000023be00000023a000000023b000000023f9c000002144e0000034226
  | 18 => 0x40000000006000000000600000000078000000007c0000000072000000007600000000758000000074c0000000740000000074300000007450000000744c0000007460000000747f000000744b80000074060000007bbb0000006ed59
  | 19 => 0x8000000000c00000000080000000009000000000800000000080000000008e000000008d000000008e000000008f000000008e600000008ec00000008ee80000008ef00000008e9e0000008ec00000008ef40000008f79c000008444a00000d32a7
  | 20 => 0x1000000000180000000018000000001e000000001f000000001c800000001dc00000001d000000001d300000001d180000001d0c0000001d1c0000001d130000001d118000001d18c000001d1e0000001d12f000001d10f800001d086000001ebfb400001bddd8
  | 21 => 0x2000000000300000000020000000002400000000200000000020000000002300000000230000000023e000000023c000000023a000000023b000000023b200000023bc00000023ba00000023a500000023b3e0000023bf00000023b900000023f79c000021404e0000342226
  | 22 => 0x40000000006000000000600000000078000000007c0000000072000000007600000000758000000074c0000000740000000074300000007450000000744c000000744e00000074430000007465000000747ac00000744c0000007440f000007446b8000074086000007bbfb000006ed759
  | 23 => 0x8000000000c00000000080000000009000000000800000000080000000008e000000008d000000008e000000008f000000008e600000008ec00000008ee80000008ef00000008ef80000008eec0000008e9e8000008ec70000008ef3e000008eef8000008effc000008f7f9c000084404a0000d328a7
  | 24 => 0x1000000000180000000018000000001e000000001f000000001c800000001dc00000001d000000001d300000001d180000001d0c0000001d1c0000001d130000001d118000001d10c000001d104000001d193000001d1e1800001d128c00001d10c000001d110700001d100380001d080600001ebffb40001bdddd8
  | 25 => 0x2000000000300000000020000000002400000000200000000020000000002300000000230000000023e000000023c000000023a000000023b000000023b200000023bc00000023ba00000023b900000023baa0000023a7c0000023b3a0000023bfd0000023bbae000023bbe8000023b88c000023f7f9c000214004e0003422226
  | 26 => 0x40000000006000000000600000000078000000007c0000000072000000007600000000758000000074c0000000740000000074300000007450000000744c000000744e000000744300000074450000007446c0000074676000007478300000744c50000074402c0000744470000074463f000074477b800074080600007bbffb00006ed7759
  | 27 => 0x8000000000c00000000080000000009000000000800000000080000000008e000000008d000000008e000000008f000000008e600000008ec00000008ee80000008ef00000008ef80000008eec0000008eee8000008ee90000008e9c8000008ec7c000008ef2e800008eeed000008eee8e00008ee9c000008efcc400008f7ff9c000844004a000d3288a7
  | 28 => 0x1000000000180000000018000000001e000000001f000000001c800000001dc00000001d000000001d300000001d180000001d0c0000001d1c0000001d130000001d118000001d10c000001d104000001d113000001d119800001d19ec00001d1e3400001d128300001d10f180001d113ac0001d119f00001d11e2f0001d1033f8001d080060001ebfffb4001bddddd8
  | 29 => 0x2000000000300000000020000000002400000000200000000020000000002300000000230000000023e000000023c000000023a000000023b000000023b200000023bc00000023ba00000023b900000023baa0000023bbc0000023ba60000023a710000023b3ca000023bffc000023bb8e000023bbc7000023ba60e00023bb1d000023b8ce000023f7ff9c002140004e0034222226
  | 30 => 0x40000000006000000000600000000078000000007c0000000072000000007600000000758000000074c0000000740000000074300000007450000000744c000000744e000000744300000074450000007446c000007447600000744630000074679000007478ac0000744c36000074400300007444710000744628c00074479b00007446a3f000744731b80074080060007bbfffb0006ed77759
  | 31 => 0x8000000000c00000000080000000009000000000800000000080000000008e000000008d000000008e000000008f000000008e600000008ec00000008ee80000008ef00000008ef80000008eec0000008eee8000008ee90000008ee88000008ee9c000008e9ce800008ec7f000008ef26800008eeefc00008eee8a80008ee95f00008ee8ece0008ee9fc00008efcea40008f7fff9c008440004a00d32888a7
  | 32 => 0x1000000000180000000018000000001e000000001f000000001c800000001dc00000001d000000001d300000001d180000001d0c0000001d1c0000001d130000001d118000001d10c000001d104000001d113000001d119800001d11ec00001d11f400001d19e300001d1e3180001d1280c0001d10f940001d113830001d119f58001d11ea0c001d11f130001d11e02f001d10315f801d080006001ebffffb401bdddddd8
  | 33 => 0x2000000000300000000020000000002400000000200000000020000000002300000000230000000023e000000023c000000023a000000023b000000023b200000023bc00000023ba00000023b900000023baa0000023bbc0000023ba60000023ba10000023ba0a000023a71c000023b3ca000023bffb000023bb8fa00023bbc6c00023ba61e00023ba1df00023ba0fee0023bb1af00023b8cbe00023f7fff9c021400004e0342222226
  | 34 => 0x40000000006000000000600000000078000000007c0000000072000000007600000000758000000074c0000000740000000074300000007450000000744c000000744e000000744300000074450000007446c0000074476000007446300000744790000074472c000074673600007478a30000744c3d0000744004c0007444706000744629300074479a10007447220c0074473010007446ad0f007447341b8074080006007bbffffb006ed777759
  | 35 => 0x8000000000c00000000080000000009000000000800000000080000000008e000000008d000000008e000000008f000000008e600000008ec00000008ee80000008ef00000008ef80000008eec0000008eee8000008ee90000008ee88000008ee9c000008ee8e800008ee8f000008e9ce800008ec7fc00008ef26680008eeeff00008eee8a80008ee95fc0008ee8efa8008ee8ff30008ee8eb3e008ee9f7b0008efceeb4008f7ffff9c084400004a0d328888a7
  | 36 => 0x1000000000180000000018000000001e000000001f000000001c800000001dc00000001d000000001d300000001d180000001d0c0000001d1c0000001d130000001d118000001d10c000001d104000001d113000001d119800001d11ec00001d11f400001d11e300001d11d180001d19d0c0001d1e3140001d128030001d10f998001d11380c001d119f54001d11ea03001d11d105801d11d00cc01d11f14c001d11e084f01d103114f81d080000601ebfffffb41bddddddd8
  | 37 => 0x2000000000300000000020000000002400000000200000000020000000002300000000230000000023e000000023c000000023a000000023b000000023b200000023bc00000023ba00000023b900000023baa0000023bbc0000023ba60000023ba10000023ba0a000023ba1c000023ba3a000023a73b000023b3dba00023bffbc00023bb8fe00023bbc6f00023ba61fa0023ba1dac0023ba3f9e0023ba3a970023ba1bf3e023bb1bef0023b8cbff0023f7ffff9c214000004e3422222226
  | 38 => 0x40000000006000000000600000000078000000007c0000000072000000007600000000758000000074c0000000740000000074300000007450000000744c000000744e000000744300000074450000007446c0000074476000007446300000744790000074472c00007447360000744763000074674500007478c4c000744c246000744004300074447010007446290c0074479a06007447625300744740610074474578c07447240c007446a410f074473400b874080000607bbfffffb06ed7777759
  | 39 => 0x8000000000c00000000080000000009000000000800000000080000000008e000000008d000000008e000000008f000000008e600000008ec00000008ee80000008ef00000008ef80000008eec0000008eee8000008ee90000008ee88000008ee9c000008ee8e800008ee8f000008ee8e800008ee8fc00008e9cfe80008ec72f00008ef27e80008eeefe40008eee8a28008ee95f90008ee86fa8008ee8bffc008ee8fb9a808ee8efc5008ee8feb3e08ee9fe3f808efcee09c08f7fffff9c844000004ad3288888a7
  | 40 => 0x1000000000180000000018000000001e000000001f000000001c800000001dc00000001d000000001d300000001d180000001d0c0000001d1c0000001d130000001d118000001d10c000001d104000001d113000001d119800001d11ec00001d11f400001d11e300001d11d180001d11d0c0001d11d140001d19d030001d1e3818001d129d0c001d10f814001d11381b001d119f55801d11fa0ec01d11d907401d11dc00301d11d046581d11d102ac1d11f01cc01d11e016071d10311f639d080000061ebffffffb5bdddddddd8
  | _ => 0

def preview (t : ℕ) (x y : ℤ) : Bool :=
  if t=0 then decide (x=0 ∧ y=0)
  else if (t:ℤ) < |x|+|y| then false
  else (table t).testBit (41*x.natAbs+y.natAbs)

set_option maxHeartbeats 1400000 in
private theorem checked (t : Fin 40) (i : Fin 41) : ∀ j : Fin 41,
    step (preview t) i j = preview (t.val+1) i j := by
  fin_cases t <;> fin_cases i <;> decide +kernel

private theorem cell_abs (t : ℕ) (x y : ℤ) : cell 350 t |x| |y| = cell 350 t x y := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy <;>
    simp only [abs_of_nonneg,abs_of_nonpos,hx,hy,mirrorX,mirrorY]

private theorem preview_abs (t : ℕ) (x y : ℤ) : preview t |x| |y| = preview t x y := by
  rcases le_total 0 x with hx | hx <;> rcases le_total 0 y with hy | hy <;>
    simp [preview,abs_of_nonneg,abs_of_nonpos,hx,hy]

theorem cell_preview (t : ℕ) (ht : t≤40) : cell 350 t = preview t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext x y
    rw [← cell_abs (t+1) x y,← preview_abs (t+1) x y]
    by_cases h : ((t+1:ℕ):ℤ) < |x|+|y|
    · rw [outside (t+1) _ _ (by simpa only [abs_abs] using h)]
      simp only [preview,Nat.succ_ne_zero,if_false,abs_abs,h,if_true]
    · have hx : x.natAbs < 41 := by
        have he := Int.natCast_natAbs x
        have hp := abs_nonneg y
        omega
      have hy : y.natAbs < 41 := by
        have he := Int.natCast_natAbs y
        have hp := abs_nonneg x
        omega
      rw [cell_step,ih (by omega)]
      simpa only [Int.natCast_natAbs] using
        checked ⟨t,by omega⟩ ⟨x.natAbs,hx⟩ ⟨y.natAbs,hy⟩

theorem early_values (t : Fin 41) : a t =
    (![1,3,3,11,27,11,59,203,123,267,1467,4043,123,4363,21947,62667,14203,102667,316859,939211,227195,1642763,5076411,15013067,3635067,26284299,81229243,240194763,58161019,420548875,1299674555,3843101899,930576251,6728782091,20794799547,61489616075,14889219963,107660513547,332716799419,983833842891,238227519355] : Fin 41 → ℤ) t := by
  unfold a
  rw [cell_preview _ (by omega)]
  fin_cases t <;> decide +kernel

end Rule350

namespace Rule350
open OMA.S_oeis_a281284

/-- In the right-moving frame, the first 33 stages are followed by a four-cycle. -/
def edgePhase (t : ℕ) : ℕ := if t < 33 then t else 33 + (t-33)%4

/-- Each entry packs an entire finite frame, with rows indexed by distance from the edge. -/
private def edgeFrames : Array ℕ := #[
  0x1,
  0x40000600001,
  0x1000018000180000600001,
  0x40000600004000068000100000600001,
  0x1000018000180001e0001b000078000180000600001,
  0x40000600004000048000400006800010000048000100000600001,
  0x1000018000180001e0001f0001e8001b80007a0001f000078000180000600001,
  0x400006000040000480004000040000430006980010c0004000010000048000100000600001,
  0x1000018000180001e0001f0001c8001cc001e8001bc0007a0001cc000720001f000078000180000600001,
  0x400006000040000480004000040000460004700043c006840010f000470001180004000010000048000100000600001,
  0x1000018000180001e0001f0001c8001d8001d2001d1001e8001bb4007a0001d1000748001d8000720001f000078000180000600001,
  0x40000480004000040000470004780047c004760043d0069f8010f4004760011f0004780011c0004000010000048000100000600001,
  0x1f0001c8001dc001d0001d0001d0001d1001e8401bc0007a1001d1000740001d0000740001dc000720001f000078000180000600001,
  0x460004600047c00470004740047700429c06844010a7004770011d0004700011f000460001180004000010000048000100000600001,
  0x1d3001d0001d1c01d1c01d1901eec01bb5407bb001d1900747001d1c00740001d3000758001d8000720001f000078000180000600001,
  0x47700474004744047ce0422506997810894047ce011d1004740011dc004780011c0004680011c0004000010000048000100000600001,
  0x1d1f01d1f81d0601ebb41bdd807aed01d0600747e01d1f00744001d0c00746001d3000740001dc000720001f000078000180000600001,
  0x4760047f384289c6844c10a27047f3811d8004740011df004760011d0004780011f000460001180004000010000048000100000600001,
  0x1d0181eeec1bb5647bbb01d0180744b81d1fc0746001d1300745001d0c00740001d3000758001d8000720001f000078000180000600001,
  0x422256995390889447bce11de804760011d3c04778011dd004760011cc004780011c0004680011c0004000010000048000100000600001,
  0x1bddd87afed1d08607443e1d12f0747801d18c0744601d1300747001d0c00746001d3000740001dc000720001f000078000180000600001,
  0x10a02747ef391dc80477e011d9f0474a011dd004778011d9004760011d0004780011f000460001180004000010000048000100000600001,
  0x1d02187446b9d103c744c01d1eb0746501d10c0744e01d1300745001d0c00740001d3000758001d8000720001f000078000180000600001,
  0x11dff84777c11de7c4763811d3d04776011df004778011dd004760011cc004780011c0004680011c0004000010000048000100000600001,
  0x1d1107744301d128c747861d1930744101d10c0744601d1300747001d0c00746001d3000740001dc000720001f000078000180000600001,
  0x11ddd7477fa11d9d0474f811dd504772011dd004778011d9004760011d0004780011f000460001180004000010000048000100000600001,
  0x1d100b744c51d1e0c746761d11b0744501d10c0744e01d1300745001d0c00740001d3000758001d8000720001f000078000180000600001,
  0x11de5d4763e11d3904774811ddd04776011df004778011dd004760011cc004780011c0004680011c0004000010000048000100000600001,
  0x1d12837478d1d19ec744661d1130744101d10c0744601d1300747001d0c00746001d3000740001dc000720001f000078000180000600001,
  0x11d9e5474e211dd304777811dd504772011dd004778011d9004760011d0004780011f000460001180004000010000048000100000600001,
  0x1d1e2b746791d118c744761d11b0744501d10c0744e01d1300745001d0c00740001d3000758001d8000720001f000078000180000600001,
  0x11d39d4774e11dd104774811ddd04776011df004778011dd004760011cc004780011c0004680011c0004000010000048000100000600001,
  0x1d19e37447d1d11ec744661d1130744101d10c0744601d1300747001d0c00746001d3000740001dc000720001f000078000180000600001,
  0x11dd054774211dd304777811dd504772011dd004778011d9004760011d0004780011f000460001180004000010000048000100000600001,
  0x1d11cb744791d118c744761d11b0744501d10c0744e01d1300745001d0c00740001d3000758001d8000720001f000078000180000600001,
  0x11dd1d4774e11dd104774811ddd04776011df004778011dd004760011cc004780011c0004680011c0004000010000048000100000600001,
  0x1d11e37447d1d11ec744661d1130744101d10c0744601d1300747001d0c00746001d3000740001dc000720001f000078000180000600001]

def edgeRow (s : ℕ) (u y : ℤ) : Bool :=
  if u < 0 ∨ y < -20 ∨ 20 < y then false
  else if s=0 then decide (u=0 ∧ y=0)
  else edgeFrames[s]!.testBit (21*u.toNat + y.natAbs)

private def edgeUpdate (s : ℕ) (u y : ℤ) : Bool :=
  (350 : ℕ).testBit ((edgeRow s (u-1) y).toNat + 2*((edgeRow s (u-2) y).toNat +
    (edgeRow s u y).toNat + (edgeRow s (u-1) (y+1)).toNat +
    (edgeRow s (u-1) (y-1)).toNat))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
private theorem edge_transition (s : Fin 37) (u y : ℤ) (hu : u ≤ 20) :
    edgeUpdate s u y = edgeRow (if s.val=36 then 33 else s.val+1) u y := by
  by_cases inner : 0 ≤ u ∧ -21 ≤ y ∧ y ≤ 21
  · let i : Fin 21 := ⟨u.toNat,by omega⟩
    let j : Fin 43 := ⟨(y+21).toNat,by omega⟩
    have hi : (i:ℤ) = u := by dsimp [i]; omega
    have hj : (j:ℤ)-21 = y := by dsimp [j]; omega
    have checked (q : Fin 37) : ∀ (v : Fin 21) (w : Fin 43),
        edgeUpdate q v ((w:ℤ)-21) = edgeRow (if q.val=36 then 33 else q.val+1) v ((w:ℤ)-21) := by
      fin_cases q <;> decide +kernel
    simpa only [hi,hj] using checked s i j
  · have off (q : ℕ) (v z : ℤ) (h : v < 0 ∨ z < -20 ∨ 20 < z) : edgeRow q v z = false := if_pos h
    simp only [edgeUpdate, off _ _ _ (show u-1<0 ∨ y < -20 ∨ 20<y by omega),
      off _ _ _ (show u<0 ∨ y < -20 ∨ 20<y by omega),
      off _ _ _ (show u-2<0 ∨ y < -20 ∨ 20<y by omega),
      off _ _ _ (show u-1<0 ∨ y+1 < -20 ∨ 20<y+1 by omega),
      off _ _ _ (show u-1<0 ∨ y-1 < -20 ∨ 20<y-1 by omega)]
    rfl

theorem edge_live (t : ℕ) (u y : ℤ) (hu : u ≤ 20) :
    cell 350 t ((t:ℤ)-u) y = edgeRow (edgePhase t) u y := by
  induction t generalizing u y with
  | zero =>
    simp only [edgePhase,show 0<33 by decide,if_true,edgeRow,Nat.cast_zero,zero_sub,cell,neg_eq_zero]
    split_ifs with h
    · simp only [decide_eq_false_iff_not]; omega
    · rfl
  | succ t ih =>
    have hbound : edgePhase t < 37 := by unfold edgePhase; split <;> omega
    have hnext : edgePhase (t+1) = if edgePhase t=36 then 33 else edgePhase t+1 := by
      simp only [edgePhase]; split_ifs <;> omega
    rw [hnext,cell]
    dsimp only
    have ab : ((t+1:ℕ):ℤ)-u = (t:ℤ)-(u-1) := by omega
    have ar : ((t+1:ℕ):ℤ)-u+1 = (t:ℤ)-(u-2) := by omega
    have al : ((t+1:ℕ):ℤ)-u-1 = (t:ℤ)-u := by omega
    rw [ar,al,ab,ih (u-1) y (by omega),ih u y hu,ih (u-2) y (by omega),
      ih (u-1) (y+1) (by omega),ih (u-1) (y-1) (by omega)]
    exact edge_transition ⟨_,hbound⟩ u y hu

/-- The low binary places of the native rightward reading, indexed by the stage mod four. -/
def edgeBits (t : ℕ) : ℕ := [1537915,1118475,1537467,1119435][t%4]!

theorem edge_axis (t : ℕ) (u : Fin 21) (ht : 33≤t) :
    cell 350 t ((t:ℤ)-(u:ℤ)) 0 = (edgeBits t).testBit u.val := by
  rw [edge_live t u 0 (by omega)]
  let z : Fin 4 := ⟨(t-33)%4,by omega⟩
  have hphase : edgePhase t = 33+z.val := if_neg (by omega)
  have hz : (33+z.val)%4=t%4 := by dsimp [z]; omega
  have checked : ∀ (q : Fin 4) (j : Fin 21), edgeRow (33+q.val) j 0 =
      (edgeBits (33+q.val)).testBit j.val := by decide +kernel
  simpa only [hphase,edgeBits,hz] using checked z u

end Rule350

namespace Rule350

/-- Twelve masks for the four time phases and three rows. Bits zero to
five give the central cells, followed by one spatial period of four. -/
def bandMask (p r : ℕ) : ℕ :=
  match p, r with
  | 0, 0 => 472 | 0, 1 => 986 | 0, _ => 24
  | 1, 0 => 550 | 1, 1 => 39 | 1, _ => 999
  | 2, 0 => 857 | 2, 1 => 984 | 2, _ => 24
  | _, 0 => 167 | _, 1 => 37 | _, _ => 999

def bandCol (x : ℤ) : ℕ :=
  (if |x| < 6 then |x| else 6+(|x|-6)%4).toNat

def band (t : ℕ) (x y : ℤ) : Bool :=
  (bandMask (t%4) y.natAbs).testBit (bandCol x)

theorem band_period (t : ℕ) (x y : ℤ) : band (t+4) x y = band t x y := by
  simp [band]

theorem band_reflect (t : ℕ) (x y : ℤ) : band t (-x) y = band t x y := by
  simp [band,bandCol]

theorem band_congr {s t : ℕ} {u v : ℤ} (y : ℤ) (st : s%4=t%4) (hu : 6≤u)
    (hv : 6≤v) (uv : u%4=v%4) : band s u y = band t v y := by
  have ab : (u-6)%4=(v-6)%4 := by omega
  simp [band,bandCol,st, abs_of_nonneg (by omega : 0≤u), abs_of_nonneg (by omega : 0≤v),
    not_lt.mpr hu,not_lt.mpr hv,ab]

end Rule350

namespace Rule350

/-- Complete the three rows at their northern boundary using reflection
in the diagonal near the center and one arbitrary neighbor elsewhere. -/
private def bandFrame (t : ℕ) (outside : Bool) (x y : ℤ) : Bool :=
  if y=3 then (if x≤2 then band t 3 x else outside) else band t x y

private theorem tabulated (t : Fin 4) (i : Fin 11) (j : Fin 3) (outside : Bool) :
    step (bandFrame t.val outside) i.val j.val = band (t.val+1) i.val j.val := by
  have h : ∀ (r : Fin 4) (x : Fin 11) (y : Fin 3) (b : Bool),
      step (bandFrame r.val b) x.val y.val = band (r.val+1) x.val y.val := by decide +kernel
  exact h t i j outside

private theorem frame_period (t : ℕ) (b : Bool) (x y : ℤ) (hx : 6≤x) :
    bandFrame t b (x+4) y = bandFrame t b x y := by
  have perm := band_congr (s:=t) (t:=t) (u:=x+4) (v:=x) y rfl (by omega) hx (by omega)
  simp [bandFrame, show ¬ x+4 ≤ 2 by omega, show ¬ x ≤ 2 by omega, perm]

private theorem checked_step (t n : ℕ) (j : Fin 3) (b : Bool) :
    step (bandFrame t b) n j.val = band (t+1) n j.val := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n<11
    · have fin := tabulated ⟨t%4,by omega⟩ ⟨n,hn⟩ j b
      have modt : (t%4+1)%4=(t+1)%4 := by omega
      simpa only [step,bandFrame,band,Nat.mod_mod,modt] using fin
    · let x : ℤ := (n-4:ℕ)
      have hx : 7≤x := by dsimp [x]; omega
      have hn' : (n:ℤ)=x+4 := by dsimp [x]; omega
      have h₀ := ih (n-4) (by omega)
      change step (bandFrame t b) x j.val = band (t+1) x j.val at h₀
      rw [hn']
      have center := frame_period t b x (j.val:ℤ) (by omega)
      have xp := frame_period t b (x+1) (j.val:ℤ) (by omega)
      have xm := frame_period t b (x-1) (j.val:ℤ) (by omega)
      have yp := frame_period t b x ((j.val:ℤ)+1) (by omega)
      have ym := frame_period t b x ((j.val:ℤ)-1) (by omega)
      have trans : step (bandFrame t b) (x+4) j.val = step (bandFrame t b) x j.val := by
        simp only [step,show x+4+1=x+1+4 by ring,show x+4-1=x-1+4 by ring,
          center,xp,xm,yp,ym]
      rw [trans,h₀]
      exact band_congr (u:=x) (v:=x+4) _ rfl (by omega) (by omega) (by omega)

theorem band_local (f : ℤ → ℤ → Bool) (t : ℕ) (x y : ℤ) (hx : 0≤x)
    (hy0 : 0≤y) (hy2 : y≤2)
    (main : ∀ u v : ℤ, x-1≤u → u≤x+1 → 0≤v → v≤2 → f u v = band t u v)
    (neg : f x (-1)=f x 1) (upper : x≤2 → f x 3 = band t 3 x) :
    step f x y = band (t+1) x y := by
  let g := bandFrame t (f x 3)
  have inner (u v : ℤ) (lo : x-1≤u) (hi : u≤x+1) (vl : 0≤v) (vh : v≤2) :
      f u v = g u v := by
    simpa [g,bandFrame,show v≠3 by omega] using main u v lo hi vl vh
  have vertical (v : ℤ) (vl : -1≤v) (vh : v≤3) : f x v = g x v := by
    by_cases mid : 0≤v ∧ v≤2
    · exact inner _ _ (by omega) (by omega) mid.1 mid.2
    · rcases show v = -1 ∨ v = 3 by omega with rfl | rfl
      · simpa [g,bandFrame,band] using neg.trans (main _ _ (by omega) (by omega) (by decide) (by decide))
      · by_cases small : x ≤ 2 <;> simp [g,bandFrame,small,upper]
  have actual : step f x y = step g x y := by
    simp only [step,inner x y (by omega) (by omega) hy0 hy2,
      inner (x+1) y (by omega) (by omega) hy0 hy2, inner (x-1) y (by omega) (by omega) hy0 hy2,
      vertical (y+1) (by omega) (by omega),vertical (y-1) (by omega) (by omega)]
  rw [actual]
  have val := checked_step t x.toNat ⟨y.toNat,by omega⟩ (f x 3)
  simpa only [Int.toNat_of_nonneg hx,Int.toNat_of_nonneg hy0] using val

end Rule350

namespace Rule350
open OMA.S_oeis_a281284

theorem edge_band (t : ℕ) (u y : ℤ) (ht : 16≤t) (hu : 14≤u ∧ u≤15) (hy : 0≤y ∧ y≤2) :
    cell 350 t ((t:ℤ)-u) y = band t ((t:ℤ)-u) y := by
  rw [edge_live t u y (by omega)]
  have hbound : 16≤edgePhase t ∧ edgePhase t≤36 := by unfold edgePhase; split <;> omega
  let a : Fin 21 := ⟨edgePhase t-16,by omega⟩
  let i : Fin 2 := ⟨(u-14).toNat,by omega⟩
  let j : Fin 3 := ⟨y.toNat,by omega⟩
  have ha : 16+a.val=edgePhase t := by dsimp [a]; omega
  have hi : 14+(i:ℤ)=u := by dsimp [i]; omega
  have hj : (j:ℤ)=y := by dsimp [j]; omega
  have checked : ∀ (s : Fin 21) (v : Fin 2) (z : Fin 3), edgeRow (16+s.val) (14+(v:ℤ)) z =
      band (16+s.val) (((16+s.val:ℕ):ℤ)-(14+(v:ℤ))) z := by decide +kernel
  calc
    edgeRow (edgePhase t) u y = band (edgePhase t) (((edgePhase t : ℕ):ℤ)-u) y := by
      simpa only [ha,hi,hj] using checked a i j
    _ = band t ((t:ℤ)-u) y := by
      by_cases small : t<33
      · rw [show edgePhase t=t by exact if_pos small]
      · have hp : edgePhase t=33+(t-33)%4 := if_neg small
        apply band_congr y <;> omega

end Rule350

namespace Rule350
open OMA.S_oeis_a281284

theorem front_period (t u : ℕ) (ht : 27≤t) (hu : u≤17) :
    cell 350 (t+4) (((t+4:ℕ):ℤ)-(u:ℤ)) 0 = cell 350 t ((t:ℤ)-(u:ℤ)) 0 := by
  rw [edge_live (t+4) u 0 (by omega), edge_live t u 0 (by omega)]
  by_cases h : 33≤t
  · have he : edgePhase (t+4) = edgePhase t := by unfold edgePhase; split_ifs <;> omega
    rw [he]
  · let i : Fin 6 := ⟨t-27,by omega⟩
    let j : Fin 18 := ⟨u,by omega⟩
    have hi : 27+i.val=t := by dsimp [i]; omega
    have checked : ∀ (a : Fin 6) (b : Fin 18),
        edgeRow (edgePhase ((27+a.val)+4)) b 0 = edgeRow (edgePhase (27+a.val)) b 0 := by decide +kernel
    simpa only [hi] using checked i j

end Rule350

namespace Rule350
open OMA.S_oeis_a281284

theorem seed_band (t : ℕ) (ht : 16 ≤ t) (he : t ≤ 20) (x y : ℤ)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hy2 : y ≤ 2) (hx : x+14 ≤ (t:ℤ)) :
    cell 350 t x y = band t x y := by
  have check (s : Fin 5) : ∀ (i : Fin 7) (j : Fin 3), i.val+14 ≤ s.val+16 →
      preview (s.val+16) i j = band (s.val+16) i j := by
    fin_cases s <;> decide +kernel
  let i : Fin 7 := ⟨x.toNat,by omega⟩
  let j : Fin 3 := ⟨y.toNat,by omega⟩
  have hi : (i:ℤ) = x := by dsimp [i]; omega
  have hj : (j:ℤ) = y := by dsimp [j]; omega
  have hs : t-16+16=t := by omega
  have v := check ⟨t-16,by omega⟩ i j (by dsimp [i]; omega)
  rw [cell_preview _ (by omega)]
  simpa only [hs,hi,hj] using v

end Rule350

namespace Rule350
open OMA.S_oeis_a281284

/-- Three rows next to the axis follow a fixed four-phase pattern at depths at least 14. -/
theorem stable (t : ℕ) (x y : ℤ) (ht : 16≤t) (hy0 : 0≤y) (hy2 : y≤2)
    (hx : |x|+14≤(t:ℤ)) : cell 350 t x y = band t x y := by
  suffices H : ∀ (t : ℕ), 16≤t → ∀ x y : ℤ, 0≤y → y≤2 → |x|+14≤(t:ℤ) →
      cell 350 t x y = band t x y from H t ht x y hy0 hy2 hx
  clear t x y ht hy0 hy2 hx
  intro t
  induction t with
  | zero => omega
  | succ t ih =>
    intro ht x y hy0 hy2 hx
    have pos (u : ℤ) (hu : 0≤u) (hw : u+14≤((t+1:ℕ):ℤ)) :
        cell 350 (t+1) u y = band (t+1) u y := by
      by_cases small : t+1 ≤ 20
      · exact seed_band _ ht small _ _ hu hy0 hy2 hw
      by_cases near : ((t+1:ℕ):ℤ)-u ≤ 15
      · have he := edge_band (t+1) (((t+1:ℕ):ℤ)-u) y ht ⟨by omega,near⟩ ⟨hy0,hy2⟩
        simpa only [sub_sub_cancel] using he
      rw [cell_step]
      apply band_local _ t u y hu hy0 hy2
      · intro v w hv1 hv2 hw0 hw2
        apply ih (by omega) v w hw0 hw2
        have h : |v| ≤ (t:ℤ)-14 := abs_le.mpr (by constructor <;> omega)
        omega
      · exact mirrorY t u 1
      · intro huu
        rw [swap t u 3]
        exact ih (by omega) 3 u hu huu (by norm_num; omega)
    rcases le_total 0 x with hp | hn
    · apply pos x hp
      simpa only [abs_of_nonneg hp] using hx
    · rw [←mirrorX _ x y,←band_reflect _ x y]
      apply pos (-x) (by omega)
      simpa only [abs_of_nonpos hn] using hx

end Rule350

namespace Rule350
open OMA.S_oeis_a281284 Finset

/-- Binary value of the last L positions, counted from the moving right edge. -/
def tailWord (n L : ℕ) : ℤ :=
  ∑ u ∈ range L, if cell 350 n ((n:ℤ)-u) 0 then (2:ℤ)^u else 0

theorem cut_word (m L : ℕ) :
    a (m+L) =
      (∑ k ∈ range (m+1), if cell 350 (m+L) k 0 then (2:ℤ)^(m+L-k) else 0) +
        tailWord (m+L) L := by
  rw [a,show m+L+1=m+1+L by omega,sum_range_add]
  congr 1
  rw [tailWord,←sum_range_reflect (fun u : ℕ => if cell 350 (m+L) ((m+L:ℕ)- (u:ℤ)) 0 then (2:ℤ)^u else 0) L]
  apply sum_congr rfl
  intro j hj
  have hl := mem_range.mp hj
  rw [show ((m+1+j:ℕ):ℤ)=((m+L:ℕ):ℤ)-(L-1-j:ℕ) by omega,
      show m+L-(m+1+j)=L-1-j by omega]

theorem tail_period
    (edge : ∀ (t u : ℕ), 33≤t → u≤17 →
      cell 350 (t+4) (((t+4:ℕ):ℤ)-u) 0=cell 350 t ((t:ℤ)-u) 0)
    (t L : ℕ) (ht : 33≤t) (hL : L≤18) : tailWord (t+4) L=tailWord t L := by
  apply sum_congr rfl
  intro u hu
  rw [edge t u ht (by have := mem_range.mp hu; omega)]

/-- The settled prefix cancels against sixteen times its value four stages earlier. -/
theorem increment
    (inside : ∀ (t k : ℕ), 33≤t → k+14≤t → cell 350 (t+4) k 0=cell 350 t k 0)
    (t : ℕ) (ht : 33≤t) :
    a (t+4) - 16*a t = tailWord (t+4) 18 - 16*tailWord t 14 := by
  obtain ⟨m,rfl⟩ : ∃ m, t=m+14 := ⟨t-14,by omega⟩
  have pref :
      (∑ k ∈ range (m+1), if cell 350 (m+18) k 0 then (2:ℤ)^(m+18-k) else 0) =
      16*(∑ k ∈ range (m+1), if cell 350 (m+14) k 0 then (2:ℤ)^(m+14-k) else 0) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k hk
    have hb := mem_range.mp hk
    have hs := inside (m+14) k ht (by omega)
    rw [show m+14+4=m+18 by omega] at hs
    rw [hs,show m+18-k=(m+14-k)+4 by omega,pow_add]
    split_ifs <;> ring
  rw [show m+14+4=m+18 by omega,cut_word m 18,cut_word m 14,pref]
  ring

theorem large_rec
    (inside : ∀ (t k : ℕ), 33≤t → k+14≤t → cell 350 (t+4) k 0=cell 350 t k 0)
    (edge : ∀ (t u : ℕ), 33≤t → u≤17 →
      cell 350 (t+4) (((t+4:ℕ):ℤ)-u) 0=cell 350 t ((t:ℤ)-u) 0)
    (n : ℕ) (hn : 41≤n) :
    a n=17*a (n-4)-16*a (n-8) := by
  obtain ⟨t,rfl⟩ : ∃ t, n=t+8 := ⟨n-8,by omega⟩
  have h1 := increment inside t (by omega)
  have h2 := increment inside (t+4) (by omega)
  rw [tail_period edge (t+4) 18 (by omega) (by decide),
      tail_period edge t 14 (by omega) (by decide)] at h2
  rw [show t+4+4=t+8 by omega] at h2
  rw [show t+8-4=t+4 by omega,show t+8-8=t by omega]
  linarith

end Rule350

namespace Rule350
open OMA.S_oeis_a281284 PowerSeries

def observations : Fin 41 → ℤ := ![1, 3, 3, 11, 27, 11, 59, 203, 123, 267, 1467, 4043, 123, 4363, 21947, 62667, 14203, 102667, 316859, 939211, 227195, 1642763, 5076411, 15013067, 3635067, 26284299, 81229243, 240194763, 58161019, 420548875, 1299674555, 3843101899, 930576251, 6728782091, 20794799547, 61489616075, 14889219963, 107660513547, 332716799419, 983833842891, 238227519355]

private theorem finite_rec : ∀ i : Fin 17, observations ⟨i.val+24,by omega⟩ =
    17*observations ⟨i.val+20,by omega⟩-16*observations ⟨i.val+16,by omega⟩ := by decide +kernel

theorem recurrence (init : ∀ i : Fin 41, a i = observations i)
    (large : ∀ n, 41≤n → a n = 17*a (n-4)-16*a (n-8))
    (n : ℕ) (hn : 24≤n) : (a n:ℚ)=17*a (n-4)-16*a (n-8) := by
  by_cases hl : n<41
  · obtain ⟨k,rfl⟩ : ∃ k, n=k+24 := ⟨n-24,by omega⟩
    have e (j : ℕ) (hj : j<41) : a j=observations ⟨j,hj⟩ := init ⟨j,hj⟩
    rw [show k+24-4=k+20 by omega,show k+24-8=k+16 by omega,e _ hl,e _ (by omega),e _ (by omega)]
    exact_mod_cast finite_rec ⟨k,by omega⟩
  · exact_mod_cast large n (by omega)

def gen : PowerSeries ℚ := mk (fun n => (a n:ℚ))

theorem solve (init : ∀ i : Fin 41, a i=observations i)
    (large : ∀ n, 41≤n → a n=17*a (n-4)-16*a (n-8)) :
    type_of% @OMA.S_oeis_a281284.main := by
  have rr := recurrence init large
  refine ⟨rr,?_⟩
  have den : gen*(16*X^8-17*X^4+1) = C 16*(gen*X^8)-C 17*(gen*X^4)+gen := by
    simp only [map_ofNat]; ring
  have num : (49152 * X ^ 23 + 40960 * X ^ 22 - 32768 * X ^ 21 - 12288 * X ^ 20 - 61440 * X ^ 19 - 32768 * X ^ 18 + 32768 * X ^ 17 + 14080 * X ^ 16 - 2816 * X ^ 15 - 2048 * X ^ 14 - 1536 * X ^ 12 + 768 * X ^ 11 + 512 * X ^ 10 + 128 * X ^ 9 - 320 * X ^ 8 + 16 * X ^ 7 + 8 * X ^ 6 - 40 * X ^ 5 + 10 * X ^ 4 + 11 * X ^ 3 + 3 * X ^ 2 + 3 * X + 1 : PowerSeries ℚ) =
      C 49152 * X ^ 23 + C 40960 * X ^ 22 - C 32768 * X ^ 21 - C 12288 * X ^ 20 - C 61440 * X ^ 19 - C 32768 * X ^ 18 + C 32768 * X ^ 17 + C 14080 * X ^ 16 - C 2816 * X ^ 15 - C 2048 * X ^ 14 - C 1536 * X ^ 12 + C 768 * X ^ 11 + C 512 * X ^ 10 + C 128 * X ^ 9 - C 320 * X ^ 8 + C 16 * X ^ 7 + C 8 * X ^ 6 - C 40 * X ^ 5 + C 10 * X ^ 4 + C 11 * X ^ 3 + C 3 * X ^ 2 + C 3 * X ^ 1 + C 1 := by simp only [map_ofNat,map_one,pow_one]
  change gen*_ = _
  rw [den,num]
  ext n
  simp only [map_add,map_sub,coeff_C_mul,coeff_mul_X_pow',coeff_C,gen,coeff_mk]
  by_cases h : n<24
  · have e (k : ℕ) (hk : k<41) : a k=observations ⟨k,hk⟩ := init ⟨k,hk⟩
    interval_cases n <;> norm_num [e,observations]
  · simp (disch := omega) only [if_pos,if_neg,add_zero,sub_zero]
    linarith only [rr n (by omega)]

end Rule350

open Rule350 in
theorem OMA.solution : type_of% @OMA.S_oeis_a281284.main := by
  apply solve early_values
  apply large_rec
  · intro t k ht hk
    have h : |(k:ℤ)|+14 ≤ t := by
      rw [abs_of_nonneg (Int.natCast_nonneg k)]
      exact_mod_cast hk
    rw [stable (t+4) k 0 (by omega) (by decide) (by decide) (by omega),
      stable t k 0 (by omega) (by decide) (by decide) h,band_period]
  · exact fun t u ht hu => front_period t u (by omega) hu
