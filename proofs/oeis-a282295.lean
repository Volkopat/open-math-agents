import OMAStatements.S_oeis_a282295

open OMA.S_oeis_a282295 PowerSeries

namespace AxisWitness

/- Each bit in a table row represents one cell in the nonnegative quadrant.
The finite check verifies the initial cell and every local transition through stage 26. -/
abbrev R := Fin 2

def rule (k : R) : ℕ := if k = 0 then 451 else 193

def rowTable (i : ℕ) : ℕ :=
  ((if i < 736 then (if i < 352 then (if i < 160 then (if i < 64 then (if i < 32 then 0xffffffffffffffffffffffffffeffffffa00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001 else 0x10000002000001fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) else (if i < 96 then 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffff9fffffe3fffff80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else (if i < 128 then 0x100000020000004000001800001ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffff9ffffff3fffffe7ffffe0fffff8000000000000000000000000000000000000000000000000))) else (if i < 256 then (if i < 192 then 0xfffff81ffffe03ffff800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000200000140000028000019000000600001fffffffffffffff else (if i < 224 then 0x200000040000018000007000001e000007c00001f80001ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffff9fffffe3fffff87ffffe0 else 0xffffffffffffffffffffffffffeffffff9ffffff3fffffe7fffff8fffffe1fffff83ffffe07fffe00ffff80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001)) else (if i < 288 then 0x10000002000001400000280000010000006000001c000007800019f000007e0001fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else (if i < 320 then 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffff9fffffe3fffff87fffff0ffffff1fffffe3fffff87fffe60ffff801fffe003fff8000000000000000000000000000000000000000000000000000000000000000 else 0xfff800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000200000040000018000017000002e000000c0000018000187000001e000067c0001ff8001ffffffffffffffffffffffffffffff)))) else (if i < 544 then (if i < 448 then (if i < 384 then 0x200001f94000007800199f000061e001fe7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffff9ffffff3fffffe7ffffe8fffff81fffff03fffff57fffe7affff861ffff983fffe007ffe060 else (if i < 416 then 0xfffff81ffffe03ffff817fffe02ffff805fffe00bfff8017ffe002fff8001ffe07e3ff800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000002000001400000280000110000026000015c00002a8000190 else 0x200000040000018000007000001e000007c00001e800007800001f000007e00001fc00007f80001ff00007814001e01801fe07ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffff9fffffe3fffff87ffffe0)) else (if i < 480 then 0xffffffffffffffffffffffffffeffffff9ffffff3fffffe7fffff8fffffe1fffff83ffffe17ffff82ffffe15ffff82ffffe05ffff80bfffe017fff87cbffe0037fe07fcff801e000000000000000000000000000000000000000000000000000000000000000000000000001 else (if i < 512 then 0x10000002000001400000280000010000006000001c00000680000180000060000018400007180001e200007c4000180c000600801980000061e201fe66fffffffffffffffffffffffffffffffffffffffff else 0x1820006000001e00081fe003fffffffffffffffffffffffffffffffffffffffffffffffffffffeffffff9fffffe3fffff87fffff0ffffff1fffffe3fffff97ffffe2fffff85ffffe1bffff967fffe29ffff853fffe727fff80cffe61fcff8061dfe07813f800780000000))) else (if i < 640 then (if i < 576 then 0xffffedfffffaffffffbfffe79f7ff861d7ff9875ffe19f77e01ffcf801ff000000000000000000000000000000000000000000000001000000200000040000018000017000002e000000c0000008000000000001000000600000080000000000010000000000000000018608 else (if i < 608 then 0x320000024000005800005a00001a000002400001f80018688000011001f9e78001e3c819801100798221ffe03ffffffffffffffffffffffffffffffffffffffffeffffff9ffffff3fffffe7ffffe8fffff81fffff03fffff47fffffcfffffedfffff8fffffe1fffffc7 else 0xfffff81ffffe03ffff807ffff00fffff01fffff03fffff07ffffa1ffffe03ffff817fffe23ffe7807ff86207fe06087f80000fe00000f800709e0007038007f800000000000000000000000000000000010000002000001400000280000110000026000015c00002b8000013)) else (if i < 672 then 0x200000040000018000007000001e000007c00001f800017f00002fe00000fc00000f800004e0000098000016000005900181560000560006756001e156007e7dc01ff8f407fe4d41ff9859ffe007ffffffffffffffffffffffffffeffffff9fffffe3fffff87ffffe0 else (if i < 704 then 0x7f8613ffe003fffffffffffffeffffff9ffffff3fffffe7fffff8fffffe1fffff83ffffe07fffe80ffff801ffff003ffff407ffff81ffffe13ffffc27ffff90ffe7ed0ff87bc1ff98f47fe01f1ff80579fe00543f80609fe00007600004c80079f000000000000000000001 else 0x80000010000002000001400000280000010000006000001c000007800011f000027e00015fc0002bf800013e000026800005800000a00018024000026c01fe87800003a0019890007ed0001f8f0007e08199fe781))))) else (if i < 1088 then (if i < 896 then (if i < 800 then (if i < 768 then 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 else 0x8000001000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) else (if i < 832 then 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffcffffff1fffffc00000000000000000000000000000000000000000000000000000000000000000000 else (if i < 864 then 0x80000010000002000000c00000fffffffffffffffffffffffffffffffffff else 0xa000001400000c800000300000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffcffffff9ffffff3fffff07ffffc0))) else (if i < 992 then (if i < 928 then 0xffffffffffffffffffff7fffffcffffff1fffffc3fffff07ffffc0fffff01ffffc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000001 else (if i < 960 then 0x80000010000002000000c000003800000f000003e00000fc0000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff else 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffcffffff9ffffff3fffffc7fffff0fffffc1fffff03ffff007fffc00000000000000000000000000000000000000000000000000000000000000000000000000000000000)) else (if i < 1024 then 0x8000001000000a00000140000008000003000000e000003c0000cf800003f0000ffffffffffffffffffffffffffffffffffffffffffffffffff else (if i < 1056 then 0x33e0000ffc000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffcffffff1fffffc3fffff87fffff8ffffff1fffffc3ffff307fffc00ffff001fffc0000000000000000 else 0xfffff81fffffabffff3d7fffc30ffffcc1ffff003fff0307ffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000010000002000000c00000b80000170000006000000c0000c3800000f)))) else (if i < 1280 then (if i < 1184 then (if i < 1120 then 0xa0000014000008800001300000ae00001540000c800000100000fca000003c000ccf800030f000ff3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffcffffff9ffffff3fffff47ffffc0 else (if i < 1152 then 0xffffffffffffffffffff7fffffcffffff1fffffc3fffff07ffffc0fffff01ffffc0bffff017fffc02ffff005fffc00bfff0017ffc000fff03f1ffc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000001 else 0x80000010000002000000c000003800000f000003e00000f400003c00000f800003f00000fe00003fc0000ff80003c0a000f00c00ff03fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) else (if i < 1216 then 0xff337fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffcffffff9ffffff3fffffc7fffff0fffffc1fffff0bffffc17ffff0affffc17ffff02ffffc05ffff00bfffc3e5fff000bff03fe7fc00f0000000000000000000000000000 else (if i < 1248 then 0xffff393fffc067ff30fe7fc030eff03c09fc003c00000000000000000000000000000000000000000000000000000000000008000001000000a00000140000008000003000000e000003400000c000003000000c2000038c0000f100003e20000c06000300400cc0000030f1 else 0x30000004000000000000800000000000000000c3040000c10003000000f00040ff001ffffffffffffffffffffffffffffffffffffffffffffffffffffff7fffffcffffff1fffffc3fffff87fffff8ffffff1fffffcbfffff17ffffc2fffff0dffffcb3ffff14ffffc29))) else (if i < 1376 then (if i < 1312 then 0xfffff81fffffa3fffffe7fffff6fffffc7fffff0fffffe3fffff6fffffc7fffffdffff3cfbffc30e3ffcc38fff0cfbbf00ffe7c00ff80000000000000000000000000000000000000000000000080000010000002000000c00000b8000017000000600000040000000000008 else (if i < 1344 then 0xa0000014000008800001300000ae000015c00000980000190000012000002c00002d00000d000001200000fc000c344000008800fcf1c000f1c40cc008803cc110fff01fffffffffffffffffffffffffffffffffffffffff7fffffcffffff9ffffff3fffff47ffffc0 else 0xffffffffffffffffffff7fffffcffffff1fffffc3fffff07ffffc0fffff01ffffc03ffff807ffff80fffff81fffff83ffffd0fffff01ffffc0bffff11fff3c03ffc3103ff03043fc00007f000007c00384f000381c003fc00000000000000000000000000000000008000001)) else (if i < 1408 then 0xfc0304bf00003b0000224003cf80000000000000000000080000010000002000000c000003800000f000003e00000fc0000bf800017f000007e000007c000027000004c00000b000002c800c08b00002b000338b000f0a3003f3ee00ffc7a03ff2620ffcc2cfff003fffffff else (if i < 1440 then 0xff03c000001000cc08003f00000fc28003f0408cff3c083fc309fff000ffffffffffffff7fffffcffffff9ffffff3fffffc7fffff0fffffc1fffff03ffff407fffc00ffff801ffffa03ffffc0fffff09ffffe13ffffc87ff3f287fc3ce0ffcc2a3ff00e8ffc02bcff002a1 else 0x8000001000000a00000140000008000003000000e000003c00008f800013f0000afe00015fc00009f000013400002c0000050000c0020000006)))))) >>> (27*(i%32))) % 2^27


def prev (n : ℕ) : ℕ := if n=0 then 1 else n-1

def localRule (r : ℕ) (c l h d u : Bool) : Bool :=
  r.testBit (c.toNat + 2*(l.toNat+h.toNat+d.toNat+u.toNat))

lemma neighbors (x : ℤ) :
    ((x-1).natAbs = prev x.natAbs ∧ (x+1).natAbs = x.natAbs+1) ∨
    ((x+1).natAbs = prev x.natAbs ∧ (x-1).natAbs = x.natAbs+1) := by
  rcases lt_trichotomy x 0 with h | rfl | h
  · right
    have a := Int.ofNat_natAbs_of_nonpos (show x ≤ 0 by omega)
    have b := Int.ofNat_natAbs_of_nonpos (show x+1 ≤ 0 by omega)
    have c := Int.ofNat_natAbs_of_nonpos (show x-1 ≤ 0 by omega)
    unfold prev; split <;> omega
  · decide
  · left
    have a := Int.natAbs_of_nonneg (show 0 ≤ x by omega)
    have b := Int.natAbs_of_nonneg (show 0 ≤ x+1 by omega)
    have c := Int.natAbs_of_nonneg (show 0 ≤ x-1 by omega)
    unfold prev; split <;> omega


def background (r : ℕ) : ℕ → Bool
  | 0 => false
  | n+1 => r.testBit (9*(background r n).toNat)

lemma outside (r t : ℕ) (x y : ℤ) (h : (t : ℤ) < |x| ∨ (t : ℤ) < |y|) :
    state r t x y = background r t := by
  induction t generalizing x y with
  | zero =>
    simp only [state, background, decide_eq_false_iff_not]
    rintro ⟨rfl,rfl⟩
    simp at h
  | succ t ih =>
    simp only [Nat.cast_succ, lt_abs] at h
    simp only [state, background]
    rw [ih x y (by simp only [lt_abs]; omega),
        ih (x-1) y (by simp only [lt_abs]; omega),
        ih (x+1) y (by simp only [lt_abs]; omega),
        ih x (y-1) (by simp only [lt_abs]; omega),
        ih x (y+1) (by simp only [lt_abs]; omega)]
    cases background r t <;> rfl


def px (k : R) (t x y : ℕ) : Bool :=
  if x ≤ t ∧ y ≤ t then (rowTable ((k.val*27+t)*27+y)).testBit x else t%2==1

lemma seed : ∀ k : R, px k 0 0 0 = true := by decide +kernel

def agrees (k : R) (t : ℕ) : Prop := ∀ x y : Fin (t+2),
  px k (t+1) x y = localRule (rule k) (px k t x y) (px k t (prev x) y)
    (px k t (x.val+1) y) (px k t x (prev y)) (px k t x (y.val+1))

instance (k : R) (t : ℕ) : Decidable (agrees k t) := by unfold agrees; infer_instance

set_option maxRecDepth 8000 in
lemma table_valid : ∀ k : R, ∀ t : Fin 26, agrees k t.val := by decide +kernel

lemma flips (k : R) (b : Bool) : (rule k).testBit (9*b.toNat) = !b := by
  fin_cases k <;> cases b <;> decide

lemma bg_eq (k : R) (t : ℕ) : background (rule k) t = (t%2==1) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [background,ih,flips]
    rcases (show t%2=0 ∧ (t+1)%2=1 ∨ t%2=1 ∧ (t+1)%2=0 by omega) with ⟨h,j⟩ | ⟨h,j⟩ <;> simp [h,j]

lemma actual (k : R) (t : ℕ) (ht : t ≤ 26) (x y : ℤ) :
    state (rule k) t x y = px k t x.natAbs y.natAbs := by
  induction t generalizing x y with
  | zero =>
    by_cases hx : x=0 <;> by_cases hy : y=0
    · subst_vars; simpa [state] using (seed k).symm
    all_goals simp [state,px,hx,hy]
  | succ t ih =>
    by_cases h : ((t+1:ℕ):ℤ) < |x| ∨ ((t+1:ℕ):ℤ) < |y|
    · rw [outside _ _ _ _ h, bg_eq]
      have hn : ¬(x.natAbs ≤ t+1 ∧ y.natAbs ≤ t+1) := by
        rintro ⟨a,b⟩
        have ax : |x| ≤ ((t+1:ℕ):ℤ) := by simpa using (show (x.natAbs:ℤ) ≤ ↑(t+1) from by exact_mod_cast a)
        have ay : |y| ≤ ((t+1:ℕ):ℤ) := by simpa using (show (y.natAbs:ℤ) ≤ ↑(t+1) from by exact_mod_cast b)
        omega
      simp [px,hn]
    push Not at h
    have hx : x.natAbs ≤ t+1 := by exact_mod_cast (show (x.natAbs:ℤ) ≤ ↑(t+1) by simpa using h.1)
    have hy : y.natAbs ≤ t+1 := by exact_mod_cast (show (y.natAbs:ℤ) ≤ ↑(t+1) by simpa using h.2)
    have upd := table_valid k ⟨t,by omega⟩ ⟨x.natAbs,Nat.lt_succ_of_le hx⟩ ⟨y.natAbs,Nat.lt_succ_of_le hy⟩
    change px k (t+1) x.natAbs y.natAbs =
      localRule (rule k) (px k t x.natAbs y.natAbs) (px k t (prev x.natAbs) y.natAbs)
        (px k t (x.natAbs+1) y.natAbs) (px k t x.natAbs (prev y.natAbs))
        (px k t x.natAbs (y.natAbs+1)) at upd
    simp only [state,ih (by omega)]
    rw [upd]
    unfold localRule
    rcases neighbors x with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> rcases neighbors y with ⟨h3,h4⟩ | ⟨h3,h4⟩ <;>
      rw [h1,h2,h3,h4] <;> ac_rfl

lemma sample (k : R) : digits (rule k) 26 = if k=0 then 111111111111000000000001111 else 111111111111000000000000111 := by
  unfold digits
  simp only [actual k 26 (by decide)]
  fin_cases k <;> decide +kernel

end AxisWitness

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a282295.main) := by
  intro allStages
  have h := allStages 26 (by decide)
  have hl : a 26 = 111111111111000000000001111 := AxisWitness.sample 0
  have hr : A279720 26 = 111111111111000000000000111 := AxisWitness.sample 1
  rw [hl, hr] at h
  norm_num at h
