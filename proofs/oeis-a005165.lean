import OMAStatements.S_oeis_a005165
import Mathlib

namespace AlternatingResidues

private def modulus : ℕ := 3612703

private def step (k v : ℕ) : ℕ := (modulus + 1 - (k * v) % modulus) % modulus

private def evaluate (v base : ℕ) : (fuel : ℕ) → ℕ
  | 0 => v
  | fuel + 1 =>
    match step (base + fuel + 2) v with
    | 0 => evaluate 0 base fuel
    | w + 1 => evaluate (w + 1) base fuel


open OMA.S_oeis_a005165

private theorem step_cast (k v : ℕ) :
    (step k v : ZMod modulus) = 1 - (k : ZMod modulus) * v := by
  have hlt := Nat.mod_lt (k * v) (by decide : 0 < modulus)
  unfold step
  rw [ZMod.natCast_mod, Nat.cast_sub (by omega)]
  push_cast
  rw [ZMod.natCast_mod, ZMod.natCast_self, Nat.cast_mul, zero_add]

private theorem evaluate_succ (v base f : ℕ) :
    evaluate v base (f + 1) = evaluate (step (base + f + 2) v) base f := by
  rw [evaluate]
  cases step (base + f + 2) v <;> rfl

private theorem evaluate_split (v base m n : ℕ) :
    evaluate v base (m + n) = evaluate (evaluate v (base + n) m) base n := by
  induction m generalizing v with
  | zero => rw [Nat.zero_add, evaluate]
  | succ m ih =>
    rw [show m + 1 + n = m + n + 1 by omega, evaluate_succ, evaluate_succ, ih]
    rw [show base + (m + n) + 2 = base + n + m + 2 by omega]

private theorem a_le_factorial (j : ℕ) : a j ≤ j.factorial := by
  cases j with
  | zero => simp [a]
  | succ j => exact Nat.sub_le _ _

private theorem a_succ_cast (j : ℕ) :
    (a (j + 1) : ZMod modulus) = ((j + 1).factorial : ZMod modulus) - a j := by
  change (↑((j + 1).factorial - a j) : ZMod modulus) = _
  exact Nat.cast_sub ((a_le_factorial j).trans (Nat.factorial_le (by omega)))

private def invariant (k v : ℕ) : ZMod modulus :=
  (-1) ^ k * ((a (k - 1) : ZMod modulus) - (k.factorial : ZMod modulus) * v)

private theorem evaluate_cast (v f : ℕ) :
    (evaluate v 0 f : ZMod modulus) = invariant (f + 1) v := by
  induction f generalizing v with
  | zero => simp [evaluate, invariant, a]
  | succ f ih =>
    rw [evaluate_succ, ih]
    simp only [invariant, Nat.add_sub_cancel, Nat.zero_add]
    rw [step_cast, a_succ_cast f, Nat.factorial_succ (f + 1), Nat.cast_mul,
      pow_succ (-1 : ZMod modulus) (f + 1)]
    ring

private theorem from_residue (ev : evaluate 1 0 (modulus - 1) = 0) :
    (a modulus : ZMod modulus) = 0 := by
  have h := evaluate_cast 1 (modulus - 1)
  rw [ev, show modulus - 1 + 1 = modulus by decide, Nat.cast_zero] at h
  have hodd : Odd modulus := ⟨1806351, by decide⟩
  simp only [invariant, hodd.neg_one_pow, Nat.cast_one, mul_one] at h
  have ha := a_succ_cast (modulus - 1)
  rw [show modulus - 1 + 1 = modulus by decide] at ha
  calc
    (a modulus : ZMod modulus) = (modulus.factorial : ZMod modulus) - a (modulus - 1) := ha
    _ = (-1 : ZMod modulus) * ((a (modulus - 1) : ZMod modulus) - modulus.factorial) := by ring
    _ = 0 := h.symm

private theorem refute (ev : evaluate 1 0 (modulus - 1) = 0) :
    ¬ (type_of% @OMA.S_oeis_a005165.main) := by
  intro h
  have hd : modulus ∣ a modulus := (ZMod.natCast_eq_zero_iff _ _).mp (from_residue ev)
  exact (not_lt_of_ge (Nat.minFac_le_of_dvd (by decide) hd)) (h modulus (by decide))


private theorem compose {input output base count tail : ℕ}
    (h : evaluate input (base + tail) count = output)
    (hrest : evaluate output base tail = 0) :
    evaluate input base (count + tail) = 0 :=
  (evaluate_split input base count tail).trans
    ((congrArg (fun v => evaluate v base tail) h).trans hrest)

private theorem remainder_0 : evaluate 0 0 0 = 0 := rfl

set_option maxHeartbeats 0 in
private theorem block_12702 : evaluate 602332 0 12702 = 0 := by
  decide +kernel

private theorem remainder_12702 : evaluate 602332 0 12702 = 0 :=
  compose (base := 0) (tail := 0) block_12702 remainder_0

set_option maxHeartbeats 0 in
private theorem block_62702 : evaluate 743121 12702 50000 = 602332 := by
  decide +kernel

private theorem remainder_62702 : evaluate 743121 0 62702 = 0 :=
  compose (base := 0) (tail := 12702) block_62702 remainder_12702

set_option maxHeartbeats 0 in
private theorem block_112702 : evaluate 3158315 62702 50000 = 743121 := by
  decide +kernel

private theorem remainder_112702 : evaluate 3158315 0 112702 = 0 :=
  compose (base := 0) (tail := 62702) block_112702 remainder_62702

set_option maxHeartbeats 0 in
private theorem block_162702 : evaluate 3425305 112702 50000 = 3158315 := by
  decide +kernel

private theorem remainder_162702 : evaluate 3425305 0 162702 = 0 :=
  compose (base := 0) (tail := 112702) block_162702 remainder_112702

set_option maxHeartbeats 0 in
private theorem block_212702 : evaluate 1108578 162702 50000 = 3425305 := by
  decide +kernel

private theorem remainder_212702 : evaluate 1108578 0 212702 = 0 :=
  compose (base := 0) (tail := 162702) block_212702 remainder_162702

set_option maxHeartbeats 0 in
private theorem block_262702 : evaluate 2422330 212702 50000 = 1108578 := by
  decide +kernel

private theorem remainder_262702 : evaluate 2422330 0 262702 = 0 :=
  compose (base := 0) (tail := 212702) block_262702 remainder_212702

set_option maxHeartbeats 0 in
private theorem block_312702 : evaluate 2912578 262702 50000 = 2422330 := by
  decide +kernel

private theorem remainder_312702 : evaluate 2912578 0 312702 = 0 :=
  compose (base := 0) (tail := 262702) block_312702 remainder_262702

set_option maxHeartbeats 0 in
private theorem block_362702 : evaluate 1385851 312702 50000 = 2912578 := by
  decide +kernel

private theorem remainder_362702 : evaluate 1385851 0 362702 = 0 :=
  compose (base := 0) (tail := 312702) block_362702 remainder_312702

set_option maxHeartbeats 0 in
private theorem block_412702 : evaluate 1881747 362702 50000 = 1385851 := by
  decide +kernel

private theorem remainder_412702 : evaluate 1881747 0 412702 = 0 :=
  compose (base := 0) (tail := 362702) block_412702 remainder_362702

set_option maxHeartbeats 0 in
private theorem block_462702 : evaluate 1721435 412702 50000 = 1881747 := by
  decide +kernel

private theorem remainder_462702 : evaluate 1721435 0 462702 = 0 :=
  compose (base := 0) (tail := 412702) block_462702 remainder_412702

set_option maxHeartbeats 0 in
private theorem block_512702 : evaluate 1807051 462702 50000 = 1721435 := by
  decide +kernel

private theorem remainder_512702 : evaluate 1807051 0 512702 = 0 :=
  compose (base := 0) (tail := 462702) block_512702 remainder_462702

set_option maxHeartbeats 0 in
private theorem block_562702 : evaluate 2092369 512702 50000 = 1807051 := by
  decide +kernel

private theorem remainder_562702 : evaluate 2092369 0 562702 = 0 :=
  compose (base := 0) (tail := 512702) block_562702 remainder_512702

set_option maxHeartbeats 0 in
private theorem block_612702 : evaluate 926012 562702 50000 = 2092369 := by
  decide +kernel

private theorem remainder_612702 : evaluate 926012 0 612702 = 0 :=
  compose (base := 0) (tail := 562702) block_612702 remainder_562702

set_option maxHeartbeats 0 in
private theorem block_662702 : evaluate 2907352 612702 50000 = 926012 := by
  decide +kernel

private theorem remainder_662702 : evaluate 2907352 0 662702 = 0 :=
  compose (base := 0) (tail := 612702) block_662702 remainder_612702

set_option maxHeartbeats 0 in
private theorem block_712702 : evaluate 3507888 662702 50000 = 2907352 := by
  decide +kernel

private theorem remainder_712702 : evaluate 3507888 0 712702 = 0 :=
  compose (base := 0) (tail := 662702) block_712702 remainder_662702

set_option maxHeartbeats 0 in
private theorem block_762702 : evaluate 2423164 712702 50000 = 3507888 := by
  decide +kernel

private theorem remainder_762702 : evaluate 2423164 0 762702 = 0 :=
  compose (base := 0) (tail := 712702) block_762702 remainder_712702

set_option maxHeartbeats 0 in
private theorem block_812702 : evaluate 811174 762702 50000 = 2423164 := by
  decide +kernel

private theorem remainder_812702 : evaluate 811174 0 812702 = 0 :=
  compose (base := 0) (tail := 762702) block_812702 remainder_762702

set_option maxHeartbeats 0 in
private theorem block_862702 : evaluate 2261307 812702 50000 = 811174 := by
  decide +kernel

private theorem remainder_862702 : evaluate 2261307 0 862702 = 0 :=
  compose (base := 0) (tail := 812702) block_862702 remainder_812702

set_option maxHeartbeats 0 in
private theorem block_912702 : evaluate 1597096 862702 50000 = 2261307 := by
  decide +kernel

private theorem remainder_912702 : evaluate 1597096 0 912702 = 0 :=
  compose (base := 0) (tail := 862702) block_912702 remainder_862702

set_option maxHeartbeats 0 in
private theorem block_962702 : evaluate 671210 912702 50000 = 1597096 := by
  decide +kernel

private theorem remainder_962702 : evaluate 671210 0 962702 = 0 :=
  compose (base := 0) (tail := 912702) block_962702 remainder_912702

set_option maxHeartbeats 0 in
private theorem block_1012702 : evaluate 1662583 962702 50000 = 671210 := by
  decide +kernel

private theorem remainder_1012702 : evaluate 1662583 0 1012702 = 0 :=
  compose (base := 0) (tail := 962702) block_1012702 remainder_962702

set_option maxHeartbeats 0 in
private theorem block_1062702 : evaluate 3212234 1012702 50000 = 1662583 := by
  decide +kernel

private theorem remainder_1062702 : evaluate 3212234 0 1062702 = 0 :=
  compose (base := 0) (tail := 1012702) block_1062702 remainder_1012702

set_option maxHeartbeats 0 in
private theorem block_1112702 : evaluate 2576823 1062702 50000 = 3212234 := by
  decide +kernel

private theorem remainder_1112702 : evaluate 2576823 0 1112702 = 0 :=
  compose (base := 0) (tail := 1062702) block_1112702 remainder_1062702

set_option maxHeartbeats 0 in
private theorem block_1162702 : evaluate 3325340 1112702 50000 = 2576823 := by
  decide +kernel

private theorem remainder_1162702 : evaluate 3325340 0 1162702 = 0 :=
  compose (base := 0) (tail := 1112702) block_1162702 remainder_1112702

set_option maxHeartbeats 0 in
private theorem block_1212702 : evaluate 2338223 1162702 50000 = 3325340 := by
  decide +kernel

private theorem remainder_1212702 : evaluate 2338223 0 1212702 = 0 :=
  compose (base := 0) (tail := 1162702) block_1212702 remainder_1162702

set_option maxHeartbeats 0 in
private theorem block_1262702 : evaluate 2588043 1212702 50000 = 2338223 := by
  decide +kernel

private theorem remainder_1262702 : evaluate 2588043 0 1262702 = 0 :=
  compose (base := 0) (tail := 1212702) block_1262702 remainder_1212702

set_option maxHeartbeats 0 in
private theorem block_1312702 : evaluate 2591483 1262702 50000 = 2588043 := by
  decide +kernel

private theorem remainder_1312702 : evaluate 2591483 0 1312702 = 0 :=
  compose (base := 0) (tail := 1262702) block_1312702 remainder_1262702

set_option maxHeartbeats 0 in
private theorem block_1362702 : evaluate 1314351 1312702 50000 = 2591483 := by
  decide +kernel

private theorem remainder_1362702 : evaluate 1314351 0 1362702 = 0 :=
  compose (base := 0) (tail := 1312702) block_1362702 remainder_1312702

set_option maxHeartbeats 0 in
private theorem block_1412702 : evaluate 740722 1362702 50000 = 1314351 := by
  decide +kernel

private theorem remainder_1412702 : evaluate 740722 0 1412702 = 0 :=
  compose (base := 0) (tail := 1362702) block_1412702 remainder_1362702

set_option maxHeartbeats 0 in
private theorem block_1462702 : evaluate 2265690 1412702 50000 = 740722 := by
  decide +kernel

private theorem remainder_1462702 : evaluate 2265690 0 1462702 = 0 :=
  compose (base := 0) (tail := 1412702) block_1462702 remainder_1412702

set_option maxHeartbeats 0 in
private theorem block_1512702 : evaluate 3260106 1462702 50000 = 2265690 := by
  decide +kernel

private theorem remainder_1512702 : evaluate 3260106 0 1512702 = 0 :=
  compose (base := 0) (tail := 1462702) block_1512702 remainder_1462702

set_option maxHeartbeats 0 in
private theorem block_1562702 : evaluate 1379499 1512702 50000 = 3260106 := by
  decide +kernel

private theorem remainder_1562702 : evaluate 1379499 0 1562702 = 0 :=
  compose (base := 0) (tail := 1512702) block_1562702 remainder_1512702

set_option maxHeartbeats 0 in
private theorem block_1612702 : evaluate 2697019 1562702 50000 = 1379499 := by
  decide +kernel

private theorem remainder_1612702 : evaluate 2697019 0 1612702 = 0 :=
  compose (base := 0) (tail := 1562702) block_1612702 remainder_1562702

set_option maxHeartbeats 0 in
private theorem block_1662702 : evaluate 2265100 1612702 50000 = 2697019 := by
  decide +kernel

private theorem remainder_1662702 : evaluate 2265100 0 1662702 = 0 :=
  compose (base := 0) (tail := 1612702) block_1662702 remainder_1612702

set_option maxHeartbeats 0 in
private theorem block_1712702 : evaluate 2341968 1662702 50000 = 2265100 := by
  decide +kernel

private theorem remainder_1712702 : evaluate 2341968 0 1712702 = 0 :=
  compose (base := 0) (tail := 1662702) block_1712702 remainder_1662702

set_option maxHeartbeats 0 in
private theorem block_1762702 : evaluate 2461441 1712702 50000 = 2341968 := by
  decide +kernel

private theorem remainder_1762702 : evaluate 2461441 0 1762702 = 0 :=
  compose (base := 0) (tail := 1712702) block_1762702 remainder_1712702

set_option maxHeartbeats 0 in
private theorem block_1812702 : evaluate 809558 1762702 50000 = 2461441 := by
  decide +kernel

private theorem remainder_1812702 : evaluate 809558 0 1812702 = 0 :=
  compose (base := 0) (tail := 1762702) block_1812702 remainder_1762702

set_option maxHeartbeats 0 in
private theorem block_1862702 : evaluate 313986 1812702 50000 = 809558 := by
  decide +kernel

private theorem remainder_1862702 : evaluate 313986 0 1862702 = 0 :=
  compose (base := 0) (tail := 1812702) block_1862702 remainder_1812702

set_option maxHeartbeats 0 in
private theorem block_1912702 : evaluate 1853625 1862702 50000 = 313986 := by
  decide +kernel

private theorem remainder_1912702 : evaluate 1853625 0 1912702 = 0 :=
  compose (base := 0) (tail := 1862702) block_1912702 remainder_1862702

set_option maxHeartbeats 0 in
private theorem block_1962702 : evaluate 2656233 1912702 50000 = 1853625 := by
  decide +kernel

private theorem remainder_1962702 : evaluate 2656233 0 1962702 = 0 :=
  compose (base := 0) (tail := 1912702) block_1962702 remainder_1912702

set_option maxHeartbeats 0 in
private theorem block_2012702 : evaluate 2170859 1962702 50000 = 2656233 := by
  decide +kernel

private theorem remainder_2012702 : evaluate 2170859 0 2012702 = 0 :=
  compose (base := 0) (tail := 1962702) block_2012702 remainder_1962702

set_option maxHeartbeats 0 in
private theorem block_2062702 : evaluate 2787881 2012702 50000 = 2170859 := by
  decide +kernel

private theorem remainder_2062702 : evaluate 2787881 0 2062702 = 0 :=
  compose (base := 0) (tail := 2012702) block_2062702 remainder_2012702

set_option maxHeartbeats 0 in
private theorem block_2112702 : evaluate 1811066 2062702 50000 = 2787881 := by
  decide +kernel

private theorem remainder_2112702 : evaluate 1811066 0 2112702 = 0 :=
  compose (base := 0) (tail := 2062702) block_2112702 remainder_2062702

set_option maxHeartbeats 0 in
private theorem block_2162702 : evaluate 1598311 2112702 50000 = 1811066 := by
  decide +kernel

private theorem remainder_2162702 : evaluate 1598311 0 2162702 = 0 :=
  compose (base := 0) (tail := 2112702) block_2162702 remainder_2112702

set_option maxHeartbeats 0 in
private theorem block_2212702 : evaluate 2387298 2162702 50000 = 1598311 := by
  decide +kernel

private theorem remainder_2212702 : evaluate 2387298 0 2212702 = 0 :=
  compose (base := 0) (tail := 2162702) block_2212702 remainder_2162702

set_option maxHeartbeats 0 in
private theorem block_2262702 : evaluate 849901 2212702 50000 = 2387298 := by
  decide +kernel

private theorem remainder_2262702 : evaluate 849901 0 2262702 = 0 :=
  compose (base := 0) (tail := 2212702) block_2262702 remainder_2212702

set_option maxHeartbeats 0 in
private theorem block_2312702 : evaluate 2386054 2262702 50000 = 849901 := by
  decide +kernel

private theorem remainder_2312702 : evaluate 2386054 0 2312702 = 0 :=
  compose (base := 0) (tail := 2262702) block_2312702 remainder_2262702

set_option maxHeartbeats 0 in
private theorem block_2362702 : evaluate 1571400 2312702 50000 = 2386054 := by
  decide +kernel

private theorem remainder_2362702 : evaluate 1571400 0 2362702 = 0 :=
  compose (base := 0) (tail := 2312702) block_2362702 remainder_2312702

set_option maxHeartbeats 0 in
private theorem block_2412702 : evaluate 972864 2362702 50000 = 1571400 := by
  decide +kernel

private theorem remainder_2412702 : evaluate 972864 0 2412702 = 0 :=
  compose (base := 0) (tail := 2362702) block_2412702 remainder_2362702

set_option maxHeartbeats 0 in
private theorem block_2462702 : evaluate 1577488 2412702 50000 = 972864 := by
  decide +kernel

private theorem remainder_2462702 : evaluate 1577488 0 2462702 = 0 :=
  compose (base := 0) (tail := 2412702) block_2462702 remainder_2412702

set_option maxHeartbeats 0 in
private theorem block_2512702 : evaluate 3192777 2462702 50000 = 1577488 := by
  decide +kernel

private theorem remainder_2512702 : evaluate 3192777 0 2512702 = 0 :=
  compose (base := 0) (tail := 2462702) block_2512702 remainder_2462702

set_option maxHeartbeats 0 in
private theorem block_2562702 : evaluate 1203930 2512702 50000 = 3192777 := by
  decide +kernel

private theorem remainder_2562702 : evaluate 1203930 0 2562702 = 0 :=
  compose (base := 0) (tail := 2512702) block_2562702 remainder_2512702

set_option maxHeartbeats 0 in
private theorem block_2612702 : evaluate 2236892 2562702 50000 = 1203930 := by
  decide +kernel

private theorem remainder_2612702 : evaluate 2236892 0 2612702 = 0 :=
  compose (base := 0) (tail := 2562702) block_2612702 remainder_2562702

set_option maxHeartbeats 0 in
private theorem block_2662702 : evaluate 3372313 2612702 50000 = 2236892 := by
  decide +kernel

private theorem remainder_2662702 : evaluate 3372313 0 2662702 = 0 :=
  compose (base := 0) (tail := 2612702) block_2662702 remainder_2612702

set_option maxHeartbeats 0 in
private theorem block_2712702 : evaluate 2689206 2662702 50000 = 3372313 := by
  decide +kernel

private theorem remainder_2712702 : evaluate 2689206 0 2712702 = 0 :=
  compose (base := 0) (tail := 2662702) block_2712702 remainder_2662702

set_option maxHeartbeats 0 in
private theorem block_2762702 : evaluate 1273736 2712702 50000 = 2689206 := by
  decide +kernel

private theorem remainder_2762702 : evaluate 1273736 0 2762702 = 0 :=
  compose (base := 0) (tail := 2712702) block_2762702 remainder_2712702

set_option maxHeartbeats 0 in
private theorem block_2812702 : evaluate 3081987 2762702 50000 = 1273736 := by
  decide +kernel

private theorem remainder_2812702 : evaluate 3081987 0 2812702 = 0 :=
  compose (base := 0) (tail := 2762702) block_2812702 remainder_2762702

set_option maxHeartbeats 0 in
private theorem block_2862702 : evaluate 3228749 2812702 50000 = 3081987 := by
  decide +kernel

private theorem remainder_2862702 : evaluate 3228749 0 2862702 = 0 :=
  compose (base := 0) (tail := 2812702) block_2862702 remainder_2812702

set_option maxHeartbeats 0 in
private theorem block_2912702 : evaluate 901423 2862702 50000 = 3228749 := by
  decide +kernel

private theorem remainder_2912702 : evaluate 901423 0 2912702 = 0 :=
  compose (base := 0) (tail := 2862702) block_2912702 remainder_2862702

set_option maxHeartbeats 0 in
private theorem block_2962702 : evaluate 1633654 2912702 50000 = 901423 := by
  decide +kernel

private theorem remainder_2962702 : evaluate 1633654 0 2962702 = 0 :=
  compose (base := 0) (tail := 2912702) block_2962702 remainder_2912702

set_option maxHeartbeats 0 in
private theorem block_3012702 : evaluate 972626 2962702 50000 = 1633654 := by
  decide +kernel

private theorem remainder_3012702 : evaluate 972626 0 3012702 = 0 :=
  compose (base := 0) (tail := 2962702) block_3012702 remainder_2962702

set_option maxHeartbeats 0 in
private theorem block_3062702 : evaluate 1051338 3012702 50000 = 972626 := by
  decide +kernel

private theorem remainder_3062702 : evaluate 1051338 0 3062702 = 0 :=
  compose (base := 0) (tail := 3012702) block_3062702 remainder_3012702

set_option maxHeartbeats 0 in
private theorem block_3112702 : evaluate 3031386 3062702 50000 = 1051338 := by
  decide +kernel

private theorem remainder_3112702 : evaluate 3031386 0 3112702 = 0 :=
  compose (base := 0) (tail := 3062702) block_3112702 remainder_3062702

set_option maxHeartbeats 0 in
private theorem block_3162702 : evaluate 1429791 3112702 50000 = 3031386 := by
  decide +kernel

private theorem remainder_3162702 : evaluate 1429791 0 3162702 = 0 :=
  compose (base := 0) (tail := 3112702) block_3162702 remainder_3112702

set_option maxHeartbeats 0 in
private theorem block_3212702 : evaluate 2235859 3162702 50000 = 1429791 := by
  decide +kernel

private theorem remainder_3212702 : evaluate 2235859 0 3212702 = 0 :=
  compose (base := 0) (tail := 3162702) block_3212702 remainder_3162702

set_option maxHeartbeats 0 in
private theorem block_3262702 : evaluate 2475002 3212702 50000 = 2235859 := by
  decide +kernel

private theorem remainder_3262702 : evaluate 2475002 0 3262702 = 0 :=
  compose (base := 0) (tail := 3212702) block_3262702 remainder_3212702

set_option maxHeartbeats 0 in
private theorem block_3312702 : evaluate 1692390 3262702 50000 = 2475002 := by
  decide +kernel

private theorem remainder_3312702 : evaluate 1692390 0 3312702 = 0 :=
  compose (base := 0) (tail := 3262702) block_3312702 remainder_3262702

set_option maxHeartbeats 0 in
private theorem block_3362702 : evaluate 844050 3312702 50000 = 1692390 := by
  decide +kernel

private theorem remainder_3362702 : evaluate 844050 0 3362702 = 0 :=
  compose (base := 0) (tail := 3312702) block_3362702 remainder_3312702

set_option maxHeartbeats 0 in
private theorem block_3412702 : evaluate 435762 3362702 50000 = 844050 := by
  decide +kernel

private theorem remainder_3412702 : evaluate 435762 0 3412702 = 0 :=
  compose (base := 0) (tail := 3362702) block_3412702 remainder_3362702

set_option maxHeartbeats 0 in
private theorem block_3462702 : evaluate 261957 3412702 50000 = 435762 := by
  decide +kernel

private theorem remainder_3462702 : evaluate 261957 0 3462702 = 0 :=
  compose (base := 0) (tail := 3412702) block_3462702 remainder_3412702

set_option maxHeartbeats 0 in
private theorem block_3512702 : evaluate 3562654 3462702 50000 = 261957 := by
  decide +kernel

private theorem remainder_3512702 : evaluate 3562654 0 3512702 = 0 :=
  compose (base := 0) (tail := 3462702) block_3512702 remainder_3462702

set_option maxHeartbeats 0 in
private theorem block_3562702 : evaluate 860584 3512702 50000 = 3562654 := by
  decide +kernel

private theorem remainder_3562702 : evaluate 860584 0 3562702 = 0 :=
  compose (base := 0) (tail := 3512702) block_3562702 remainder_3512702

set_option maxHeartbeats 0 in
private theorem block_3612702 : evaluate 1 3562702 50000 = 860584 := by
  decide +kernel

private theorem remainder_3612702 : evaluate 1 0 3612702 = 0 :=
  compose (base := 0) (tail := 3562702) block_3612702 remainder_3562702

end AlternatingResidues

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a005165.main) :=
  AlternatingResidues.refute AlternatingResidues.remainder_3612702