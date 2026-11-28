import OMAStatements.S_oeis_a321575

open OMA.S_oeis_a321575

private instance (k : ℕ) : Decidable (composite k) :=
  inferInstanceAs (Decidable (2 ≤ k ∧ ¬ k.Prime))

/-- The nonnegative representative n+(k-1) is n-1 modulo a positive k,
including at n=0. -/
private def test (n k : ℕ) : Bool :=
  n ^ k % k == ((n + (k-1))^k + 1) % k

private theorem test_iff {n k : ℕ} (hk : 0 < k) : test n k = true ↔ passes n k := by
  have hpred : ((n + (k-1) : ℕ) : ZMod k) = (n : ZMod k)-1 := by
    rw [Nat.cast_add, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one, ZMod.natCast_self]
    simp [sub_eq_add_neg]
  unfold test passes
  rw [beq_iff_eq, ← ZMod.natCast_eq_natCast_iff', Nat.cast_add, Nat.cast_one,
    Nat.cast_pow, Nat.cast_pow, hpred]

private theorem periodic {n k L : ℕ} (hk : k ∣ L) : passes (n % L) k ↔ passes n k := by
  have hcast : ((n % L : ℕ) : ZMod k) = n :=
    (ZMod.natCast_eq_natCast_iff' ..).mpr (Nat.mod_mod_of_dvd n hk)
  unfold passes
  rw [hcast]

private def covers (k L : ℕ) (ds : List ℕ) : Bool :=
  (List.range L).all fun r => !(test r k) || ds.any fun d => test r d

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
private theorem universal_bound (n : ℕ) : passes n 561 := by
  have h : (List.range 561).all (fun r => test r 561) = true := by decide
  apply (periodic (n := n) (k := 561) (L := 561) (by decide)).mp
  apply (test_iff (by decide)).mp
  exact List.all_eq_true.mp h _ (List.mem_range.mpr (Nat.mod_lt _ (by decide)))

private theorem least_of_checked (n k : ℕ) (hc : composite k) (hp : test n k = true)
    (hsmall : (List.range k).all (fun j => !(decide (composite j)) || !(test n j)) = true) :
    leastPretender n k := by
  refine ⟨⟨hc, (test_iff (by have := hc.1; omega)).mp hp⟩, ?_⟩
  intro j hj
  by_contra! hjk
  have h := List.all_eq_true.mp hsmall j (List.mem_range.mpr hjk)
  have hjt := (test_iff (by have := hj.1.1; omega)).mpr hj.2
  simp [hj.1,hjt] at h

private theorem attained4 : leastPretender 1 4 := least_of_checked 1 4 (by decide) (by decide) (by decide)
private theorem attained9 : leastPretender 0 9 := least_of_checked 0 9 (by decide) (by decide) (by decide)
private theorem attained49 : leastPretender 38 49 := least_of_checked 38 49 (by decide) (by decide) (by decide)
/-- L and the earlier composite moduli tested for each potentially excluded k. -/
private def row : ℕ → ℕ × List ℕ
  | 8 => (8, [4])
  | 12 => (12, [4])
  | 16 => (16, [4])
  | 18 => (18, [6])
  | 20 => (20, [4])
  | 24 => (24, [4])
  | 25 => (75, [15])
  | 27 => (27, [9])
  | 28 => (28, [4])
  | 32 => (32, [4])
  | 36 => (36, [4])
  | 40 => (40, [4])
  | 44 => (44, [4])
  | 45 => (45, [9])
  | 48 => (48, [4])
  | 50 => (50, [10])
  | 52 => (52, [4])
  | 54 => (54, [6])
  | 56 => (56, [4])
  | 60 => (60, [4])
  | 63 => (63, [9])
  | 64 => (64, [4])
  | 68 => (68, [4])
  | 72 => (72, [4])
  | 75 => (75, [15])
  | 76 => (76, [4])
  | 80 => (80, [4])
  | 81 => (81, [9])
  | 84 => (84, [4])
  | 88 => (88, [4])
  | 90 => (90, [6])
  | 92 => (92, [4])
  | 96 => (96, [4])
  | 98 => (98, [14])
  | 99 => (99, [9])
  | 100 => (100, [4])
  | 104 => (104, [4])
  | 108 => (108, [4])
  | 112 => (112, [4])
  | 116 => (116, [4])
  | 117 => (117, [9])
  | 120 => (120, [4])
  | 121 => (363, [33])
  | 124 => (124, [4])
  | 125 => (375, [15])
  | 126 => (126, [6])
  | 128 => (128, [4])
  | 132 => (132, [4])
  | 135 => (135, [9])
  | 136 => (136, [4])
  | 140 => (140, [4])
  | 144 => (144, [4])
  | 147 => (147, [21])
  | 148 => (148, [4])
  | 150 => (150, [6])
  | 152 => (152, [4])
  | 153 => (153, [9])
  | 156 => (156, [4])
  | 160 => (160, [4])
  | 162 => (162, [6])
  | 164 => (164, [4])
  | 168 => (168, [4])
  | 169 => (1183, [91])
  | 171 => (171, [9])
  | 172 => (172, [4])
  | 175 => (525, [15])
  | 176 => (176, [4])
  | 180 => (180, [4])
  | 184 => (184, [4])
  | 188 => (188, [4])
  | 189 => (189, [9])
  | 192 => (192, [4])
  | 196 => (196, [4])
  | 198 => (198, [6])
  | 200 => (200, [4])
  | 204 => (204, [4])
  | 207 => (207, [9])
  | 208 => (208, [4])
  | 212 => (212, [4])
  | 216 => (216, [4])
  | 220 => (220, [4])
  | 224 => (224, [4])
  | 225 => (225, [9])
  | 228 => (228, [4])
  | 232 => (232, [4])
  | 234 => (234, [6])
  | 236 => (236, [4])
  | 240 => (240, [4])
  | 242 => (242, [22])
  | 243 => (243, [9])
  | 244 => (244, [4])
  | 245 => (245, [49])
  | 248 => (248, [4])
  | 250 => (250, [10])
  | 252 => (252, [4])
  | 256 => (256, [4])
  | 260 => (260, [4])
  | 261 => (261, [9])
  | 264 => (264, [4])
  | 268 => (268, [4])
  | 270 => (270, [6])
  | 272 => (272, [4])
  | 275 => (825, [15])
  | 276 => (276, [4])
  | 279 => (279, [9])
  | 280 => (280, [4])
  | 284 => (284, [4])
  | 288 => (288, [4])
  | 289 => (867, [51])
  | 292 => (292, [4])
  | 294 => (294, [6])
  | 296 => (296, [4])
  | 297 => (297, [9])
  | 300 => (300, [4])
  | 304 => (304, [4])
  | 306 => (306, [6])
  | 308 => (308, [4])
  | 312 => (312, [4])
  | 315 => (315, [9])
  | 316 => (316, [4])
  | 320 => (320, [4])
  | 324 => (324, [4])
  | 325 => (975, [15])
  | 328 => (328, [4])
  | 332 => (332, [4])
  | 333 => (333, [9])
  | 336 => (336, [4])
  | 338 => (338, [26])
  | 340 => (340, [4])
  | 342 => (342, [6])
  | 343 => (343, [49])
  | 344 => (344, [4])
  | 348 => (348, [4])
  | 350 => (350, [10])
  | 351 => (351, [9])
  | 352 => (352, [4])
  | 356 => (356, [4])
  | 360 => (360, [4])
  | 361 => (7581, [21, 57, 133])
  | 363 => (363, [33])
  | 364 => (364, [4])
  | 368 => (368, [4])
  | 369 => (369, [9])
  | 372 => (372, [4])
  | 375 => (375, [15])
  | 376 => (376, [4])
  | 378 => (378, [6])
  | 380 => (380, [4])
  | 384 => (384, [4])
  | 387 => (387, [9])
  | 388 => (388, [4])
  | 392 => (392, [4])
  | 396 => (396, [4])
  | 400 => (400, [4])
  | 404 => (404, [4])
  | 405 => (405, [9])
  | 408 => (408, [4])
  | 412 => (412, [4])
  | 414 => (414, [6])
  | 416 => (416, [4])
  | 420 => (420, [4])
  | 423 => (423, [9])
  | 424 => (424, [4])
  | 425 => (1275, [15])
  | 428 => (428, [4])
  | 432 => (432, [4])
  | 436 => (436, [4])
  | 440 => (440, [4])
  | 441 => (441, [9])
  | 444 => (444, [4])
  | 448 => (448, [4])
  | 450 => (450, [6])
  | 452 => (452, [4])
  | 456 => (456, [4])
  | 459 => (459, [9])
  | 460 => (460, [4])
  | 464 => (464, [4])
  | 468 => (468, [4])
  | 472 => (472, [4])
  | 475 => (1425, [15])
  | 476 => (476, [4])
  | 477 => (477, [9])
  | 480 => (480, [4])
  | 484 => (484, [4])
  | 486 => (486, [6])
  | 488 => (488, [4])
  | 490 => (490, [10])
  | 492 => (492, [4])
  | 495 => (495, [9])
  | 496 => (496, [4])
  | 500 => (500, [4])
  | 504 => (504, [4])
  | 507 => (507, [39])
  | 508 => (508, [4])
  | 512 => (512, [4])
  | 513 => (513, [9])
  | 516 => (516, [4])
  | 520 => (520, [4])
  | 522 => (522, [6])
  | 524 => (524, [4])
  | 525 => (525, [15])
  | 528 => (528, [4])
  | 529 => (1587, [69])
  | 531 => (531, [9])
  | 532 => (532, [4])
  | 536 => (536, [4])
  | 539 => (1617, [33])
  | 540 => (540, [4])
  | 544 => (544, [4])
  | 548 => (548, [4])
  | 549 => (549, [9])
  | 550 => (550, [10])
  | 552 => (552, [4])
  | 556 => (556, [4])
  | 558 => (558, [6])
  | 560 => (560, [4])
  | _ => (0, [])

private def valid (k : ℕ) : Prop :=
  (row k).1 = 0 ∨
    (k ∣ (row k).1 ∧
    (∀ d ∈ (row k).2, composite d ∧ d < k ∧ d ∣ (row k).1) ∧
    covers k (row k).1 (row k).2 = true)

private instance (k : ℕ) : Decidable (valid k) := by unfold valid; infer_instance

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
private theorem has_row : ∀ k : Fin 562, composite k.val → (∃ a : Fin 24, 2 ≤ a.val ∧ a.val * a.val ∣ k.val) →
    k.val ≠ 4 → k.val ≠ 9 → k.val ≠ 49 → (row k.val).1 ≠ 0 := by decide

private theorem no_least {n k : ℕ} (hcomp : composite k) (hr : (row k).1 ≠ 0)
    (hv : valid k) (hp : passes n k) : ¬ leastPretender n k := by
  rcases hv with h | ⟨hdiv, hearli, hcov⟩
  · exact False.elim (hr h)
  · let L := (row k).1
    have hpos : 0 < L := Nat.pos_of_ne_zero hr
    let r := n % L
    have ht : test r k = true := (test_iff (by have := hcomp.1; omega)).mpr ((periodic hdiv).mpr hp)
    have hag := List.all_eq_true.mp hcov r (List.mem_range.mpr (Nat.mod_lt _ hpos))
    simp only [ht, Bool.not_true, Bool.false_or] at hag
    obtain ⟨d, hd, hdt⟩ := List.any_eq_true.mp hag
    obtain ⟨hdc,hdk,hdL⟩ := hearli d hd
    have hpd : passes n d := (periodic hdL).mp ((test_iff (by have := hdc.1; omega)).mp hdt)
    intro hl
    exact (Nat.not_le_of_lt hdk) (hl.2 d ⟨hdc,hpd⟩)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
private theorem table_valid : ∀ k : Fin 562, valid k.val := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 12000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a321575.main := by
  ext k
  change (¬ Squarefree k ∧ ∃ n, leastPretender n k) ↔ k ∈ ({4,9,49} : Set ℕ)
  constructor
  · rintro ⟨hns,n,hl⟩
    have hle : k ≤ 561 := hl.2 561 ⟨by decide, universal_bound n⟩
    by_contra h
    have hn4 : k ≠ 4 := by intro he; subst k; exact h (by simp)
    have hn9 : k ≠ 9 := by intro he; subst k; exact h (by simp)
    have hn49 : k ≠ 49 := by intro he; subst k; exact h (by simp)
    let i : Fin 562 := ⟨k,by omega⟩
    have hex : ∃ q : ℕ, q.Prime ∧ q*q ∣ k := by
      by_contra! hh
      exact hns (Nat.squarefree_iff_prime_squarefree.mpr hh)
    obtain ⟨q, hqprime, hqdiv⟩ := hex
    have hdivle : q*q ≤ k := Nat.le_of_dvd (by have := hl.1.1.1; omega) hqdiv
    have hqsmall : q < 24 := by
      by_contra! hh
      have := Nat.mul_le_mul hh hh
      omega
    have hr := has_row i hl.1.1 ⟨⟨q,hqsmall⟩,hqprime.two_le,hqdiv⟩ hn4 hn9 hn49
    exact no_least hl.1.1 hr (table_valid i) hl.1.2 hl
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl | rfl)
    · exact ⟨fun h => (Nat.squarefree_iff_prime_squarefree.mp h 2 (by decide)) (by decide),1,attained4⟩
    · exact ⟨fun h => (Nat.squarefree_iff_prime_squarefree.mp h 3 (by decide)) (by decide),0,attained9⟩
    · exact ⟨fun h => (Nat.squarefree_iff_prime_squarefree.mp h 7 (by decide)) (by decide),38,attained49⟩
