import OMAReductions.R_SierpinskiNumber_prime_sierpinski_problem_R1_H1_R1_H2_R1

namespace ModCertificates

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private def modularPower (m a : ℕ) : ℕ → ℕ :=
  Nat.binaryRec 1 (fun b _ x => (x * x * (if b then a else 1)) % m)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private def squareChain (m : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | t + 1, x => squareChain m t ((x * x) % m)

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem cast_mod {d m : ℕ} (hd : d ∣ m) (x : ℕ) :
    ((x % m : ℕ) : ZMod d) = x := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_mod_of_dvd _ hd]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem cast_modularPower {d m : ℕ} (hd : d ∣ m) (a k : ℕ) :
    ((modularPower m a k : ℕ) : ZMod d) = (a : ZMod d) ^ k := by
  induction k using Nat.binaryRec with
  | zero => simp [modularPower]
  | bit b n ih =>
    by_cases h : n = 0 ∧ b = false
    · obtain ⟨rfl, rfl⟩ := h
      simp [modularPower]
    · rw [modularPower, Nat.binaryRec_eq b n (Or.inr (by
        intro hn
        cases b <;> simp_all)), cast_mod hd]
      push_cast
      unfold modularPower at ih
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add, mul_assoc]

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem cast_squareChain {d m : ℕ} (hd : d ∣ m) (t x : ℕ) :
    ((squareChain m t x : ℕ) : ZMod d) = (x : ZMod d) ^ (2 ^ t) := by
  induction t generalizing x with
  | zero => simp [squareChain]
  | succ t ih =>
    rw [squareChain, ih, cast_mod hd, Nat.cast_mul, ← pow_two, ← pow_mul,
      pow_succ']

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_of_certificate (k t a : ℕ) (hk : 0 < k) (hsize : k < 2 ^ (t + 1))
    (hc : let m := k * 2 ^ (t + 1) + 1
          squareChain m t (modularPower m a k) + 1 = m) :
    (k * 2 ^ (t + 1) + 1).Prime := by
  let m := k * 2 ^ (t + 1) + 1
  change m.Prime
  change squareChain m t (modularPower m a k) + 1 = m at hc
  have hm : 0 < m := by dsimp [m]; omega
  have hm' : 1 < m := by
    dsimp [m]
    have hpos : 0 < k * 2 ^ (t + 1) := by positivity
    omega
  by_contra hn
  let d := m.minFac
  have hd : d.Prime := Nat.minFac_prime hm'.ne'
  have hdm : d ∣ m := Nat.minFac_dvd m
  have hmOdd : m % 2 = 1 := by
    dsimp [m]
    rw [pow_succ, ← Nat.mul_assoc]
    omega
  have hd2 : 2 < d := by
    refine lt_of_le_of_ne hd.two_le ?_
    intro h
    have h2m : 2 ∣ m := h ▸ hdm
    simp [Nat.dvd_iff_mod_eq_zero, hmOdd] at h2m
  let : Fact d.Prime := ⟨hd⟩
  let : Fact (2 < d) := ⟨hd2⟩
  let x : ZMod d := (a : ZMod d) ^ k
  have hneg : x ^ (2 ^ t) = -1 := by
    have h := congrArg (fun j : ℕ => (j : ZMod d)) hc
    push_cast at h
    rw [cast_squareChain hdm, cast_modularPower hdm,
      (ZMod.natCast_eq_zero_iff _ _).mpr hdm] at h
    exact eq_neg_of_add_eq_zero_left h
  have hx : x ^ (2 ^ (t + 1)) = 1 := by
    rw [pow_succ, pow_mul, hneg]
    norm_num
  have hx0 : x ≠ 0 := by
    rintro h
    simp [h] at hx
  have ho : orderOf x = 2 ^ (t + 1) := by
    apply orderOf_eq_of_pow_and_pow_div_prime (by positivity) hx
    intro p hp hpd
    have hp2 : p = 2 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpd)
    subst p
    rw [pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 2), hneg]
    exact ZMod.neg_one_ne_one
  have hle : 2 ^ (t + 1) ≤ d - 1 :=
    Nat.le_of_dvd (by omega) (ho ▸ ZMod.orderOf_dvd_card_sub_one hx0)
  have hs := Nat.minFac_sq_le_self hm hn
  change d ^ 2 ≤ m at hs
  have hstrict : m < d ^ 2 := by
    have hb : (2 ^ (t + 1) : ℕ) + 1 ≤ d := by omega
    have hsquare := Nat.mul_le_mul hb hb
    have hkbound : k * 2 ^ (t + 1) ≤ 2 ^ (t + 1) * 2 ^ (t + 1) :=
      Nat.mul_le_mul_right _ hsize.le
    dsimp [m]
    nlinarith
  omega



set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_4861 : (4861 * 2 ^ 2492 + 1).Prime := by
  apply prime_of_certificate 4861 2491 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_8929 : (8929 * 2 ^ 1966 + 1).Prime := by
  apply prime_of_certificate 8929 1965 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_9323 : (9323 * 2 ^ 3013 + 1).Prime := by
  apply prime_of_certificate 9323 3012 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_12527 : (12527 * 2 ^ 2435 + 1).Prime := by
  apply prime_of_certificate 12527 2434 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_13007 : (13007 * 2 ^ 1655 + 1).Prime := by
  apply prime_of_certificate 13007 1654 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_16519 : (16519 * 2 ^ 3434 + 1).Prime := by
  apply prime_of_certificate 16519 3433 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_16987 : (16987 * 2 ^ 2748 + 1).Prime := by
  apply prime_of_certificate 16987 2747 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_17597 : (17597 * 2 ^ 3799 + 1).Prime := by
  apply prime_of_certificate 17597 3798 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_22727 : (22727 * 2 ^ 1371 + 1).Prime := by
  apply prime_of_certificate 22727 1370 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_24151 : (24151 * 2 ^ 2508 + 1).Prime := by
  apply prime_of_certificate 24151 2507 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_25171 : (25171 * 2 ^ 2456 + 1).Prime := by
  apply prime_of_certificate 25171 2455 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_25343 : (25343 * 2 ^ 1989 + 1).Prime := by
  apply prime_of_certificate 25343 1988 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_29629 : (29629 * 2 ^ 1498 + 1).Prime := by
  apply prime_of_certificate 29629 1497 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_30091 : (30091 * 2 ^ 2184 + 1).Prime := by
  apply prime_of_certificate 30091 2183 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_41809 : (41809 * 2 ^ 1402 + 1).Prime := by
  apply prime_of_certificate 41809 1401 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_42257 : (42257 * 2 ^ 2667 + 1).Prime := by
  apply prime_of_certificate 42257 2666 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_42409 : (42409 * 2 ^ 1506 + 1).Prime := by
  apply prime_of_certificate 42409 1505 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_45737 : (45737 * 2 ^ 2375 + 1).Prime := by
  apply prime_of_certificate 45737 2374 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_48091 : (48091 * 2 ^ 1476 + 1).Prime := by
  apply prime_of_certificate 48091 1475 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_56543 : (56543 * 2 ^ 2501 + 1).Prime := by
  apply prime_of_certificate 56543 2500 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_57467 : (57467 * 2 ^ 1259 + 1).Prime := by
  apply prime_of_certificate 57467 1258 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_60737 : (60737 * 2 ^ 1411 + 1).Prime := by
  apply prime_of_certificate 60737 1410 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_61519 : (61519 * 2 ^ 1290 + 1).Prime := by
  apply prime_of_certificate 61519 1289 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_65539 : (65539 * 2 ^ 1822 + 1).Prime := by
  apply prime_of_certificate 65539 1821 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_73849 : (73849 * 2 ^ 1202 + 1).Prime := by
  apply prime_of_certificate 73849 1201 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_76261 : (76261 * 2 ^ 2156 + 1).Prime := by
  apply prime_of_certificate 76261 2155 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_77521 : (77521 * 2 ^ 3336 + 1).Prime := by
  apply prime_of_certificate 77521 3335 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_82267 : (82267 * 2 ^ 2904 + 1).Prime := by
  apply prime_of_certificate 82267 2903 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_88007 : (88007 * 2 ^ 2843 + 1).Prime := by
  apply prime_of_certificate 88007 2842 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_89003 : (89003 * 2 ^ 1285 + 1).Prime := by
  apply prime_of_certificate 89003 1284 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_89521 : (89521 * 2 ^ 1564 + 1).Prime := by
  apply prime_of_certificate 89521 1563 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_90019 : (90019 * 2 ^ 3470 + 1).Prime := by
  apply prime_of_certificate 90019 3469 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_90529 : (90529 * 2 ^ 2518 + 1).Prime := by
  apply prime_of_certificate 90529 2517 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_91291 : (91291 * 2 ^ 3432 + 1).Prime := by
  apply prime_of_certificate 91291 3431 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_98327 : (98327 * 2 ^ 2911 + 1).Prime := by
  apply prime_of_certificate 98327 2910 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_101363 : (101363 * 2 ^ 1953 + 1).Prime := by
  apply prime_of_certificate 101363 1952 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_104089 : (104089 * 2 ^ 3550 + 1).Prime := by
  apply prime_of_certificate 104089 3549 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_104207 : (104207 * 2 ^ 1371 + 1).Prime := by
  apply prime_of_certificate 104207 1370 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_106637 : (106637 * 2 ^ 1579 + 1).Prime := by
  apply prime_of_certificate 106637 1578 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_109639 : (109639 * 2 ^ 1426 + 1).Prime := by
  apply prime_of_certificate 109639 1425 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_111439 : (111439 * 2 ^ 1366 + 1).Prime := by
  apply prime_of_certificate 111439 1365 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_116731 : (116731 * 2 ^ 1736 + 1).Prime := by
  apply prime_of_certificate 116731 1735 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_124561 : (124561 * 2 ^ 3236 + 1).Prime := by
  apply prime_of_certificate 124561 3235 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_126743 : (126743 * 2 ^ 2117 + 1).Prime := by
  apply prime_of_certificate 126743 2116 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_127711 : (127711 * 2 ^ 1496 + 1).Prime := by
  apply prime_of_certificate 127711 1495 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_132887 : (132887 * 2 ^ 1363 + 1).Prime := by
  apply prime_of_certificate 132887 1362 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_136429 : (136429 * 2 ^ 1462 + 1).Prime := by
  apply prime_of_certificate 136429 1461 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_138143 : (138143 * 2 ^ 1225 + 1).Prime := by
  apply prime_of_certificate 138143 1224 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_143401 : (143401 * 2 ^ 1324 + 1).Prime := by
  apply prime_of_certificate 143401 1323 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_143629 : (143629 * 2 ^ 2082 + 1).Prime := by
  apply prime_of_certificate 143629 2081 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_145637 : (145637 * 2 ^ 1531 + 1).Prime := by
  apply prime_of_certificate 145637 1530 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_148669 : (148669 * 2 ^ 1718 + 1).Prime := by
  apply prime_of_certificate 148669 1717 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_149239 : (149239 * 2 ^ 1666 + 1).Prime := by
  apply prime_of_certificate 149239 1665 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_154823 : (154823 * 2 ^ 3725 + 1).Prime := by
  apply prime_of_certificate 154823 3724 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_156887 : (156887 * 2 ^ 3627 + 1).Prime := by
  apply prime_of_certificate 156887 3626 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_158507 : (158507 * 2 ^ 1651 + 1).Prime := by
  apply prime_of_certificate 158507 1650 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_160159 : (160159 * 2 ^ 1906 + 1).Prime := by
  apply prime_of_certificate 160159 1905 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_165931 : (165931 * 2 ^ 2204 + 1).Prime := by
  apply prime_of_certificate 165931 2203 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_168109 : (168109 * 2 ^ 1834 + 1).Prime := by
  apply prime_of_certificate 168109 1833 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_170267 : (170267 * 2 ^ 1595 + 1).Prime := by
  apply prime_of_certificate 170267 1594 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_172741 : (172741 * 2 ^ 1440 + 1).Prime := by
  apply prime_of_certificate 172741 1439 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_175759 : (175759 * 2 ^ 1482 + 1).Prime := by
  apply prime_of_certificate 175759 1481 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_182957 : (182957 * 2 ^ 1843 + 1).Prime := by
  apply prime_of_certificate 182957 1842 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_185177 : (185177 * 2 ^ 2279 + 1).Prime := by
  apply prime_of_certificate 185177 2278 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_186023 : (186023 * 2 ^ 4089 + 1).Prime := by
  apply prime_of_certificate 186023 4088 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_190283 : (190283 * 2 ^ 1857 + 1).Prime := by
  apply prime_of_certificate 190283 1856 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_191071 : (191071 * 2 ^ 2176 + 1).Prime := by
  apply prime_of_certificate 191071 2175 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_192013 : (192013 * 2 ^ 3768 + 1).Prime := by
  apply prime_of_certificate 192013 3767 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_195443 : (195443 * 2 ^ 2873 + 1).Prime := by
  apply prime_of_certificate 195443 2872 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_201709 : (201709 * 2 ^ 2726 + 1).Prime := by
  apply prime_of_certificate 201709 2725 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_201947 : (201947 * 2 ^ 1463 + 1).Prime := by
  apply prime_of_certificate 201947 1462 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_202219 : (202219 * 2 ^ 3110 + 1).Prime := by
  apply prime_of_certificate 202219 3109 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_204301 : (204301 * 2 ^ 2492 + 1).Prime := by
  apply prime_of_certificate 204301 2491 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_204623 : (204623 * 2 ^ 1909 + 1).Prime := by
  apply prime_of_certificate 204623 1908 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_205913 : (205913 * 2 ^ 3641 + 1).Prime := by
  apply prime_of_certificate 205913 3640 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_208729 : (208729 * 2 ^ 2426 + 1).Prime := by
  apply prime_of_certificate 208729 2425 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_209179 : (209179 * 2 ^ 1398 + 1).Prime := by
  apply prime_of_certificate 209179 1397 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_209371 : (209371 * 2 ^ 3540 + 1).Prime := by
  apply prime_of_certificate 209371 3539 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_212419 : (212419 * 2 ^ 2302 + 1).Prime := by
  apply prime_of_certificate 212419 2301 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_213859 : (213859 * 2 ^ 2246 + 1).Prime := by
  apply prime_of_certificate 213859 2245 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_213901 : (213901 * 2 ^ 2192 + 1).Prime := by
  apply prime_of_certificate 213901 2191 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_215417 : (215417 * 2 ^ 1271 + 1).Prime := by
  apply prime_of_certificate 215417 1270 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_216023 : (216023 * 2 ^ 2073 + 1).Prime := by
  apply prime_of_certificate 216023 2072 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_218521 : (218521 * 2 ^ 3668 + 1).Prime := by
  apply prime_of_certificate 218521 3667 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_220771 : (220771 * 2 ^ 2968 + 1).Prime := by
  apply prime_of_certificate 220771 2967 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_221251 : (221251 * 2 ^ 4064 + 1).Prime := by
  apply prime_of_certificate 221251 4063 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_226099 : (226099 * 2 ^ 2386 + 1).Prime := by
  apply prime_of_certificate 226099 2385 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_228233 : (228233 * 2 ^ 1597 + 1).Prime := by
  apply prime_of_certificate 228233 1596 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_229249 : (229249 * 2 ^ 3446 + 1).Prime := by
  apply prime_of_certificate 229249 3445 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_231799 : (231799 * 2 ^ 2102 + 1).Prime := by
  apply prime_of_certificate 231799 2101 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_234211 : (234211 * 2 ^ 2992 + 1).Prime := by
  apply prime_of_certificate 234211 2991 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_235577 : (235577 * 2 ^ 2351 + 1).Prime := by
  apply prime_of_certificate 235577 2350 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_238801 : (238801 * 2 ^ 1992 + 1).Prime := by
  apply prime_of_certificate 238801 1991 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_239431 : (239431 * 2 ^ 1716 + 1).Prime := by
  apply prime_of_certificate 239431 1715 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_239543 : (239543 * 2 ^ 1949 + 1).Prime := by
  apply prime_of_certificate 239543 1948 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_242357 : (242357 * 2 ^ 3507 + 1).Prime := by
  apply prime_of_certificate 242357 3506 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_243137 : (243137 * 2 ^ 1231 + 1).Prime := by
  apply prime_of_certificate 243137 1230 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_247609 : (247609 * 2 ^ 1438 + 1).Prime := by
  apply prime_of_certificate 247609 1437 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_248401 : (248401 * 2 ^ 2368 + 1).Prime := by
  apply prime_of_certificate 248401 2367 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_249079 : (249079 * 2 ^ 2842 + 1).Prime := by
  apply prime_of_certificate 249079 2841 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_249107 : (249107 * 2 ^ 2023 + 1).Prime := by
  apply prime_of_certificate 249107 2022 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_252983 : (252983 * 2 ^ 1913 + 1).Prime := by
  apply prime_of_certificate 252983 1912 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_253733 : (253733 * 2 ^ 1293 + 1).Prime := by
  apply prime_of_certificate 253733 1292 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_258173 : (258173 * 2 ^ 3161 + 1).Prime := by
  apply prime_of_certificate 258173 3160 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_258443 : (258443 * 2 ^ 3857 + 1).Prime := by
  apply prime_of_certificate 258443 3856 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_258691 : (258691 * 2 ^ 2180 + 1).Prime := by
  apply prime_of_certificate 258691 2179 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_260207 : (260207 * 2 ^ 1223 + 1).Prime := by
  apply prime_of_certificate 260207 1222 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_260363 : (260363 * 2 ^ 3621 + 1).Prime := by
  apply prime_of_certificate 260363 3620 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_261593 : (261593 * 2 ^ 1229 + 1).Prime := by
  apply prime_of_certificate 261593 1228 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_263387 : (263387 * 2 ^ 1419 + 1).Prime := by
  apply prime_of_certificate 263387 1418 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_266003 : (266003 * 2 ^ 4089 + 1).Prime := by
  apply prime_of_certificate 266003 4088 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_267511 : (267511 * 2 ^ 3748 + 1).Prime := by
  apply prime_of_certificate 267511 3747 3 (by decide) (by decide)
  decide +kernel

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
private theorem prime_270241 : (270241 * 2 ^ 1600 + 1).Prime := by
  apply prime_of_certificate 270241 1599 3 (by decide) (by decide)
  decide +kernel

end ModCertificates

open ModCertificates

set_option maxRecDepth 50000 in
set_option maxHeartbeats 400000000 in
theorem OMA.solution : OMA.R_SierpinskiNumber_prime_sierpinski_problem_R1_H1_R1_H2_R1.H1 := by
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2492, by decide, prime_4861⟩
  · exact ⟨1966, by decide, prime_8929⟩
  · exact ⟨3013, by decide, prime_9323⟩
  · exact ⟨2435, by decide, prime_12527⟩
  · exact ⟨1655, by decide, prime_13007⟩
  · exact ⟨3434, by decide, prime_16519⟩
  · exact ⟨2748, by decide, prime_16987⟩
  · exact ⟨3799, by decide, prime_17597⟩
  · exact ⟨1371, by decide, prime_22727⟩
  · exact ⟨2508, by decide, prime_24151⟩
  · exact ⟨2456, by decide, prime_25171⟩
  · exact ⟨1989, by decide, prime_25343⟩
  · exact ⟨1498, by decide, prime_29629⟩
  · exact ⟨2184, by decide, prime_30091⟩
  · exact ⟨1402, by decide, prime_41809⟩
  · exact ⟨2667, by decide, prime_42257⟩
  · exact ⟨1506, by decide, prime_42409⟩
  · exact ⟨2375, by decide, prime_45737⟩
  · exact ⟨1476, by decide, prime_48091⟩
  · exact ⟨2501, by decide, prime_56543⟩
  · exact ⟨1259, by decide, prime_57467⟩
  · exact ⟨1411, by decide, prime_60737⟩
  · exact ⟨1290, by decide, prime_61519⟩
  · exact ⟨1822, by decide, prime_65539⟩
  · exact ⟨1202, by decide, prime_73849⟩
  · exact ⟨2156, by decide, prime_76261⟩
  · exact ⟨3336, by decide, prime_77521⟩
  · exact ⟨2904, by decide, prime_82267⟩
  · exact ⟨2843, by decide, prime_88007⟩
  · exact ⟨1285, by decide, prime_89003⟩
  · exact ⟨1564, by decide, prime_89521⟩
  · exact ⟨3470, by decide, prime_90019⟩
  · exact ⟨2518, by decide, prime_90529⟩
  · exact ⟨3432, by decide, prime_91291⟩
  · exact ⟨2911, by decide, prime_98327⟩
  · exact ⟨1953, by decide, prime_101363⟩
  · exact ⟨3550, by decide, prime_104089⟩
  · exact ⟨1371, by decide, prime_104207⟩
  · exact ⟨1579, by decide, prime_106637⟩
  · exact ⟨1426, by decide, prime_109639⟩
  · exact ⟨1366, by decide, prime_111439⟩
  · exact ⟨1736, by decide, prime_116731⟩
  · exact ⟨3236, by decide, prime_124561⟩
  · exact ⟨2117, by decide, prime_126743⟩
  · exact ⟨1496, by decide, prime_127711⟩
  · exact ⟨1363, by decide, prime_132887⟩
  · exact ⟨1462, by decide, prime_136429⟩
  · exact ⟨1225, by decide, prime_138143⟩
  · exact ⟨1324, by decide, prime_143401⟩
  · exact ⟨2082, by decide, prime_143629⟩
  · exact ⟨1531, by decide, prime_145637⟩
  · exact ⟨1718, by decide, prime_148669⟩
  · exact ⟨1666, by decide, prime_149239⟩
  · exact ⟨3725, by decide, prime_154823⟩
  · exact ⟨3627, by decide, prime_156887⟩
  · exact ⟨1651, by decide, prime_158507⟩
  · exact ⟨1906, by decide, prime_160159⟩
  · exact ⟨2204, by decide, prime_165931⟩
  · exact ⟨1834, by decide, prime_168109⟩
  · exact ⟨1595, by decide, prime_170267⟩
  · exact ⟨1440, by decide, prime_172741⟩
  · exact ⟨1482, by decide, prime_175759⟩
  · exact ⟨1843, by decide, prime_182957⟩
  · exact ⟨2279, by decide, prime_185177⟩
  · exact ⟨4089, by decide, prime_186023⟩
  · exact ⟨1857, by decide, prime_190283⟩
  · exact ⟨2176, by decide, prime_191071⟩
  · exact ⟨3768, by decide, prime_192013⟩
  · exact ⟨2873, by decide, prime_195443⟩
  · exact ⟨2726, by decide, prime_201709⟩
  · exact ⟨1463, by decide, prime_201947⟩
  · exact ⟨3110, by decide, prime_202219⟩
  · exact ⟨2492, by decide, prime_204301⟩
  · exact ⟨1909, by decide, prime_204623⟩
  · exact ⟨3641, by decide, prime_205913⟩
  · exact ⟨2426, by decide, prime_208729⟩
  · exact ⟨1398, by decide, prime_209179⟩
  · exact ⟨3540, by decide, prime_209371⟩
  · exact ⟨2302, by decide, prime_212419⟩
  · exact ⟨2246, by decide, prime_213859⟩
  · exact ⟨2192, by decide, prime_213901⟩
  · exact ⟨1271, by decide, prime_215417⟩
  · exact ⟨2073, by decide, prime_216023⟩
  · exact ⟨3668, by decide, prime_218521⟩
  · exact ⟨2968, by decide, prime_220771⟩
  · exact ⟨4064, by decide, prime_221251⟩
  · exact ⟨2386, by decide, prime_226099⟩
  · exact ⟨1597, by decide, prime_228233⟩
  · exact ⟨3446, by decide, prime_229249⟩
  · exact ⟨2102, by decide, prime_231799⟩
  · exact ⟨2992, by decide, prime_234211⟩
  · exact ⟨2351, by decide, prime_235577⟩
  · exact ⟨1992, by decide, prime_238801⟩
  · exact ⟨1716, by decide, prime_239431⟩
  · exact ⟨1949, by decide, prime_239543⟩
  · exact ⟨3507, by decide, prime_242357⟩
  · exact ⟨1231, by decide, prime_243137⟩
  · exact ⟨1438, by decide, prime_247609⟩
  · exact ⟨2368, by decide, prime_248401⟩
  · exact ⟨2842, by decide, prime_249079⟩
  · exact ⟨2023, by decide, prime_249107⟩
  · exact ⟨1913, by decide, prime_252983⟩
  · exact ⟨1293, by decide, prime_253733⟩
  · exact ⟨3161, by decide, prime_258173⟩
  · exact ⟨3857, by decide, prime_258443⟩
  · exact ⟨2180, by decide, prime_258691⟩
  · exact ⟨1223, by decide, prime_260207⟩
  · exact ⟨3621, by decide, prime_260363⟩
  · exact ⟨1229, by decide, prime_261593⟩
  · exact ⟨1419, by decide, prime_263387⟩
  · exact ⟨4089, by decide, prime_266003⟩
  · exact ⟨3748, by decide, prime_267511⟩
  · exact ⟨1600, by decide, prime_270241⟩