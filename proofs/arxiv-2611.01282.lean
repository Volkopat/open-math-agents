import OMAStatements.S_arxiv_2611_01282

/-!
We verify Zhang's four published reduced certificates from the ancillary
residue lists of arXiv:2611.01282v1. A natural number packs the covered residue
classes into its bits. Doubling builds a spaced mask logarithmically in its
length, and the kernel checks the resulting bitwise unions.
-/

open OMA.S_arxiv_2611_01282

namespace OMA.CoveringCertificates

private def spread (d : ℕ) : ℕ → ℕ
  | 0 => 1
  | b + 1 =>
    let v := spread d b
    v ||| (v <<< (d * 2 ^ b))

private theorem shifted {v k i : ℕ} (h : (v <<< k).testBit i = true) :
    k ≤ i ∧ v.testBit (i - k) = true := by
  rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

private theorem spreadDvd (d b i : ℕ) (h : (spread d b).testBit i = true) : d ∣ i := by
  induction b generalizing i with
  | zero =>
    change (1 : ℕ).testBit i = true at h
    simp [Nat.testBit_one_eq_true_iff_self_eq_zero.mp h]
  | succ b ih =>
    rw [spread, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ih i h
    · obtain ⟨hk, hbit⟩ := shifted h
      have hd := ih (i - d * 2 ^ b) hbit
      rw [← Nat.sub_add_cancel hk]
      exact Nat.dvd_add hd (dvd_mul_right d _)

private def clause (L : ℕ) (c : ℕ × ℕ) : ℕ :=
  spread c.2 (Nat.log2 (L / c.2) + 1) <<< c.1

private def aggregate (L : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | c :: cs => clause L c ||| aggregate L cs

private theorem aggregateSound {L i : ℕ} (S : List (ℕ × ℕ))
    (h : (aggregate L S).testBit i = true) :
    ∃ c ∈ S, ∃ k : ℕ, i = c.1 + c.2 * k := by
  induction S with
  | nil => simp [aggregate] at h
  | cons c cs ih =>
    rw [aggregate, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨hle, hbit⟩ := shifted h
      obtain ⟨k, hk⟩ := spreadDvd _ _ _ hbit
      exact ⟨c, by simp, k, by omega⟩
    · obtain ⟨q, hq, k, hk⟩ := ih h
      exact ⟨q, by simp [hq], k, hk⟩

private def maskCheck (L : ℕ) (S : List (ℕ × ℕ)) : Prop :=
  (aggregate L S) % (2 ^ L) = 2 ^ L - 1

private theorem covers {L : ℕ} (S : List (ℕ × ℕ)) (hL : 0 < L)
    (hd : ∀ c ∈ S, c.2 ∣ L) (hm : maskCheck L S) (x : ℤ) :
    ∃ c ∈ S, x ≡ (c.1 : ℤ) [ZMOD (c.2 : ℤ)] := by
  let z := x % (L : ℤ)
  let i := z.toNat
  have hLZ : 0 < (L : ℤ) := by exact_mod_cast hL
  have hz : 0 ≤ z := Int.emod_nonneg _ hLZ.ne'
  have hzi : (i : ℤ) = z := Int.toNat_of_nonneg hz
  have hilt : i < L := by
    have h := Int.emod_lt_of_pos x hLZ
    exact_mod_cast (hzi.trans_lt h)
  have hb : (aggregate L S).testBit i = true := by
    have hb' : ((aggregate L S) % (2 ^ L)).testBit i = true := by
      rw [show (aggregate L S) % (2 ^ L) = 2 ^ L - 1 from hm,
        Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
      exact hilt
    simpa [Nat.testBit_mod_two_pow, hilt] using hb'
  obtain ⟨c, hc, k, hik⟩ := aggregateSound S hb
  have hx : x ≡ (i : ℤ) [ZMOD (L : ℤ)] := by
    rw [hzi]
    exact (Int.mod_modEq x (L : ℤ)).symm
  have hdZ : (c.2 : ℤ) ∣ (L : ℤ) := by exact_mod_cast hd c hc
  have hi : (i : ℤ) ≡ (c.1 : ℤ) [ZMOD (c.2 : ℤ)] := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨-(k : ℤ), ?_⟩
    have hk : (i : ℤ) = (c.1 : ℤ) + (c.2 : ℤ) * (k : ℤ) := by exact_mod_cast hik
    rw [hk]
    ring
  exact ⟨c, hc, (hx.of_dvd hdZ).trans hi⟩

private theorem build (S : List (ℕ × ℕ)) (m L : ℕ) (hm : 2 ≤ m) (hL : 0 < L)
    (hb : ∀ c ∈ S, m ≤ c.2 ∧ c.1 < c.2)
    (hn : ∀ c ∈ S, ∀ c' ∈ S, c.2 = c'.2 → c = c')
    (he : ∃ c ∈ S, c.2 = m)
    (hlcm : S.toFinset.lcm Prod.snd = L) (hcheck : maskCheck L S) :
    ∃ T, IsDistinctCoveringSystem T ∧ HasMinModulusAndLcm T m L := by
  have hd (c : ℕ × ℕ) (hc : c ∈ S) : c.2 ∣ L := by
    rw [← hlcm]
    exact Finset.dvd_lcm (List.mem_toFinset.mpr hc)
  obtain ⟨c, hc, hcm⟩ := he
  refine ⟨S.toFinset, ⟨?_, ?_, ?_⟩, ⟨⟨?_, ?_⟩, hlcm⟩⟩
  · intro u hu
    obtain ⟨hlo, hhi⟩ := hb u (List.mem_toFinset.mp hu)
    exact ⟨hm.trans hlo, hhi⟩
  · intro u hu v hv h
    exact hn u (List.mem_toFinset.mp hu) v (List.mem_toFinset.mp hv) h
  · intro x
    obtain ⟨u, hu, h⟩ := covers S hL hd hcheck x
    exact ⟨u, List.mem_toFinset.mpr hu, h⟩
  · exact ⟨c, List.mem_toFinset.mpr hc, hcm⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact (hb u (List.mem_toFinset.mp hu)).1

private def data8 : List (ℕ × ℕ) := [
  (3, 8), (8, 9), (6, 10), (1, 12), (2, 14), (3, 15), (7, 16),
  (2, 18), (0, 20), (19, 21), (9, 24), (10, 28), (12, 30), (15, 32),
  (34, 35), (29, 36), (10, 40), (22, 42), (23, 45), (21, 48), (46, 56),
  (24, 60), (28, 63), (63, 64), (14, 70), (41, 72), (77, 80), (4, 84),
  (32, 90), (45, 96), (13, 105), (52, 112), (30, 120), (112, 126), (54, 140),
  (5, 144), (61, 160), (136, 168), (104, 180), (159, 192), (202, 210), (95, 224),
  (189, 240), (70, 252), (74, 280), (77, 288), (239, 315), (287, 320), (220, 336),
  (230, 360), (414, 420), (415, 448), (285, 480), (466, 504), (18, 560), (479, 576),
  (448, 630), (127, 672), (365, 720), (790, 840), (95, 960), (298, 1008), (895, 1120),
  (952, 1260), (31, 1344), (509, 1440), (298, 1680), (1183, 2016), (671, 2240), (1642, 2520),
  (2399, 2880), (1631, 3360), (2527, 4032), (802, 5040), (2591, 6720), (7871, 10080), (6431, 20160)
]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private theorem check8 : ∃ T, IsDistinctCoveringSystem T ∧
    HasMinModulusAndLcm T 8 20160 := by
  apply build data8 8 20160 (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · unfold maskCheck
    decide +kernel

private def data9 : List (ℕ × ℕ) := [
  (2, 9), (0, 10), (1, 12), (7, 14), (6, 15), (3, 16), (14, 18),
  (12, 20), (15, 21), (7, 24), (24, 25), (26, 27), (13, 28), (16, 30),
  (3, 35), (5, 36), (2, 40), (9, 42), (13, 45), (43, 48), (4, 50),
  (44, 54), (55, 56), (48, 60), (54, 63), (45, 70), (23, 72), (19, 75),
  (62, 80), (81, 84), (88, 90), (64, 100), (24, 105), (17, 108), (27, 112),
  (22, 120), (33, 126), (116, 135), (18, 140), (59, 144), (84, 150), (39, 168),
  (69, 175), (28, 180), (8, 189), (114, 200), (87, 210), (71, 216), (184, 225),
  (102, 240), (201, 252), (8, 270), (98, 280), (34, 300), (138, 315), (123, 336),
  (294, 350), (118, 360), (89, 378), (214, 400), (258, 420), (395, 432), (34, 450),
  (327, 504), (219, 525), (89, 540), (58, 560), (214, 600), (305, 630), (494, 675),
  (58, 700), (658, 720), (737, 756), (798, 840), (784, 900), (332, 945), (75, 1008),
  (144, 1050), (414, 1200), (978, 1260), (1034, 1350), (198, 1400), (359, 1512), (1419, 1575),
  (538, 1680), (1278, 1800), (683, 1890), (618, 2100), (1142, 2160), (2458, 2520), (359, 2700),
  (338, 2800), (1115, 3024), (894, 3150), (978, 3600), (1817, 3780), (1038, 4200), (4679, 4725),
  (4618, 5040), (4814, 5400), (6078, 6300), (7487, 7560), (6498, 8400), (1439, 9450), (1979, 10800),
  (1878, 12600), (3707, 15120), (12239, 18900), (16578, 25200), (31679, 37800)
]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private theorem check9 : ∃ T, IsDistinctCoveringSystem T ∧
    HasMinModulusAndLcm T 9 75600 := by
  apply build data9 9 75600 (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · unfold maskCheck
    decide +kernel

private def data10 : List (ℕ × ℕ) := [
  (8, 10), (9, 12), (4, 14), (5, 15), (7, 16), (13, 18), (2, 20),
  (17, 21), (3, 24), (24, 25), (25, 27), (8, 28), (0, 30), (31, 32),
  (21, 35), (1, 36), (32, 40), (5, 42), (10, 45), (35, 48), (14, 50),
  (43, 54), (20, 56), (6, 60), (62, 63), (47, 64), (26, 70), (19, 72),
  (59, 75), (12, 80), (29, 84), (40, 90), (11, 96), (54, 100), (86, 105),
  (61, 108), (100, 112), (96, 120), (41, 126), (115, 135), (106, 140), (125, 144),
  (84, 150), (132, 160), (137, 168), (119, 175), (173, 180), (115, 189), (15, 192),
  (104, 200), (16, 210), (115, 216), (123, 224), (109, 225), (17, 240), (77, 252),
  (70, 270), (216, 280), (155, 288), (294, 300), (146, 315), (212, 320), (53, 336),
  (194, 350), (317, 360), (178, 378), (204, 400), (286, 420), (341, 432), (180, 448),
  (184, 450), (143, 480), (149, 504), (44, 525), (413, 540), (156, 560), (271, 576),
  (144, 600), (346, 630), (155, 672), (259, 675), (694, 700), (137, 720), (10, 756),
  (4, 800), (276, 840), (485, 864), (29, 900), (451, 945), (527, 960), (221, 1008),
  (394, 1050), (593, 1080), (532, 1120), (689, 1200), (986, 1260), (1103, 1344), (34, 1350),
  (944, 1400), (923, 1440), (665, 1512), (1469, 1575), (404, 1600), (1577, 1680), (655, 1728),
  (389, 1800), (136, 1890), (1115, 2016), (1294, 2100), (197, 2160), (52, 2240), (239, 2400),
  (1913, 2520), (629, 2700), (44, 2800), (1403, 2880), (1673, 3024), (94, 3150), (3227, 3360),
  (1289, 3600), (2656, 3780), (539, 4032), (444, 4200), (3977, 4320), (4294, 4725), (1679, 4800),
  (1901, 5040), (5129, 5400), (5204, 5600), (917, 6048), (1994, 6300), (911, 6720), (2939, 7200),
  (233, 7560), (7289, 8400), (6137, 8640), (7444, 9450), (1787, 10080), (2789, 10800), (1204, 11200),
  (9557, 12096), (3929, 12600), (629, 14400), (13979, 16800), (1144, 18900), (11573, 20160), (23069, 25200),
  (9557, 30240), (10319, 33600), (12329, 37800), (25979, 50400), (45017, 60480), (54089, 75600), (50939, 100800),
  (63989, 302400)
]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private theorem check10 : ∃ T, IsDistinctCoveringSystem T ∧
    HasMinModulusAndLcm T 10 302400 := by
  apply build data10 10 302400 (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · unfold maskCheck
    decide +kernel

private def data11 : List (ℕ × ℕ) := [
  (10, 11), (9, 12), (12, 14), (10, 15), (7, 16), (11, 18), (16, 20),
  (4, 21), (6, 22), (3, 24), (17, 25), (26, 27), (2, 28), (1, 30),
  (31, 32), (14, 33), (34, 35), (5, 36), (8, 40), (18, 42), (2, 44),
  (19, 45), (36, 48), (2, 50), (17, 54), (9, 55), (22, 56), (13, 60),
  (7, 63), (28, 64), (8, 66), (48, 70), (59, 72), (7, 75), (45, 77),
  (64, 80), (42, 84), (18, 88), (49, 90), (15, 96), (11, 99), (12, 100),
  (73, 105), (89, 108), (20, 110), (106, 112), (43, 120), (112, 126), (38, 132),
  (34, 135), (6, 140), (95, 144), (127, 150), (136, 154), (108, 160), (125, 165),
  (150, 168), (97, 175), (84, 176), (0, 180), (106, 189), (60, 192), (176, 198),
  (32, 200), (90, 210), (35, 216), (60, 220), (162, 224), (172, 225), (158, 231),
  (24, 240), (154, 252), (62, 264), (259, 270), (97, 275), (268, 280), (204, 288),
  (143, 297), (37, 300), (210, 308), (304, 315), (204, 320), (320, 330), (234, 336),
  (62, 350), (172, 352), (240, 360), (187, 378), (224, 385), (86, 396), (272, 400),
  (346, 420), (143, 432), (40, 440), (274, 448), (247, 450), (452, 462), (463, 480),
  (218, 495), (436, 504), (262, 525), (68, 528), (300, 540), (522, 550), (184, 560),
  (498, 576), (44, 594), (187, 600), (92, 616), (94, 630), (200, 660), (66, 672),
  (547, 675), (56, 693), (482, 700), (700, 704), (104, 720), (232, 756), (114, 770),
  (716, 792), (332, 800), (482, 825), (148, 840), (696, 864), (148, 880), (72, 900),
  (686, 924), (79, 945), (684, 960), (416, 990), (738, 1008), (472, 1050), (332, 1056),
  (120, 1080), (262, 1100), (946, 1120), (254, 1155), (1142, 1188), (1087, 1200), (386, 1232),
  (904, 1260), (764, 1320), (498, 1344), (97, 1350), (980, 1386), (1072, 1400), (300, 1440),
  (1043, 1485), (1148, 1540), (772, 1575), (200, 1584), (72, 1600), (632, 1650), (344, 1680),
  (1128, 1728), (1468, 1760), (1372, 1800), (1772, 1848), (394, 1890), (422, 1925), (1868, 1980),
  (402, 2016), (3, 2079), (2072, 2100), (1916, 2112), (480, 2160), (532, 2200), (498, 2240),
  (2174, 2310), (548, 2376), (562, 2400), (1170, 2464), (1672, 2475), (28, 2520), (104, 2640),
  (2172, 2700), (72, 2800), (562, 2880), (746, 2970), (24, 3024), (1624, 3080), (997, 3150),
  (1042, 3168), (2372, 3300), (274, 3360), (1767, 3465), (1202, 3520), (2172, 3600), (920, 3696),
  (1032, 3780), (1882, 3850), (3104, 3960), (3090, 4032), (3594, 4158), (672, 4200), (3720, 4320),
  (4072, 4400), (4412, 4620), (4497, 4725), (3432, 4752)
]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
private theorem check11 : ∃ T, IsDistinctCoveringSystem T ∧
    HasMinModulusAndLcm T 11 3326400 := by
  apply build data11 11 3326400 (by decide) (by decide)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · unfold maskCheck
    decide +kernel

end OMA.CoveringCertificates

theorem OMA.solution : type_of% @OMA.S_arxiv_2611_01282.main :=
  ⟨OMA.CoveringCertificates.check8, OMA.CoveringCertificates.check9,
    OMA.CoveringCertificates.check10, OMA.CoveringCertificates.check11⟩
