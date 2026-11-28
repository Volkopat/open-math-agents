import OMAStatements.S_oeis_a273145

-- Credit: @EmadY

private def radMod (r m : ℕ) : Bool :=
  if r = 0 then decide (m = 0)
  else if r = 1 then decide (m ≠ 0)
  else if r = 2 then decide (m = 2)
  else decide (m ≠ 2)

private def radState (t d : ℕ) : Bool :=
  if t = 0 then decide (d = 0)
  else if t ≤ d then true
  else radMod (t % 4) (d % 4)

private lemma rule597_testBit (c n1 n2 n3 n4 : Bool) :
    Nat.testBit 597 (c.toNat + 2 * (n1.toNat + n2.toNat + n3.toNat + n4.toNat)) =
      (c == (n1 && n2 && n3 && n4)) := by
  cases c <;> cases n1 <;> cases n2 <;> cases n3 <;> cases n4 <;> rfl

theorem state_succ (t : ℕ) (x y : ℤ) :
    OMA.S_oeis_a273145.state (t + 1) x y =
      (OMA.S_oeis_a273145.state t x y ==
        (OMA.S_oeis_a273145.state t (x - 1) y &&
         OMA.S_oeis_a273145.state t (x + 1) y &&
         OMA.S_oeis_a273145.state t x (y - 1) &&
         OMA.S_oeis_a273145.state t x (y + 1))) := by
  rw [OMA.S_oeis_a273145.state]
  exact rule597_testBit _ _ _ _ _

private lemma pair_neighbors_natAbs (f : ℕ → Bool) (z : ℤ) (a : ℕ) :
    (f ((z - 1).natAbs + a) && f ((z + 1).natAbs + a)) =
      if z = 0 then f (a + 1)
      else f (z.natAbs + a - 1) && f (z.natAbs + a + 1) := by
  by_cases hz : z = 0
  · subst hz
    simp [Nat.add_comm]
  · rw [if_neg hz]
    rcases lt_trichotomy z 0 with hlt | rfl | hgt
    · have h1 : (z - 1).natAbs + a = z.natAbs + a + 1 := by omega
      have h2 : (z + 1).natAbs + a = z.natAbs + a - 1 := by omega
      rw [h1, h2, Bool.and_comm]
    · exact absurd rfl hz
    · have h1 : (z - 1).natAbs + a = z.natAbs + a - 1 := by omega
      have h2 : (z + 1).natAbs + a = z.natAbs + a + 1 := by omega
      rw [h1, h2]

private lemma four_neighbors_natAbs (f : ℕ → Bool) (x y : ℤ) :
    (f ((x - 1).natAbs + y.natAbs) && f ((x + 1).natAbs + y.natAbs) &&
     f (x.natAbs + (y - 1).natAbs) && f (x.natAbs + (y + 1).natAbs)) =
      if x.natAbs + y.natAbs = 0 then f 1
      else f (x.natAbs + y.natAbs - 1) && f (x.natAbs + y.natAbs + 1) := by
  have hcomm1 : x.natAbs + (y - 1).natAbs = (y - 1).natAbs + x.natAbs := Nat.add_comm _ _
  have hcomm2 : x.natAbs + (y + 1).natAbs = (y + 1).natAbs + x.natAbs := Nat.add_comm _ _
  rw [Bool.and_assoc (f ((x - 1).natAbs + y.natAbs) && f ((x + 1).natAbs + y.natAbs)),
      hcomm1, hcomm2,
      pair_neighbors_natAbs f x y.natAbs, pair_neighbors_natAbs f y x.natAbs,
      Nat.add_comm y.natAbs x.natAbs]
  by_cases hx : x = 0 <;> by_cases hy : y = 0
  · subst hx; subst hy; simp
  · subst hx
    have hne : y.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hy
    simp [hy, hne]
  · subst hy
    have hne : x.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hx
    simp [hx, hne]
  · simp [hx, hy]

private lemma radMod_zero_step (r : ℕ) (hr : r < 4) :
    (radMod r 0 == radMod r 1) = radMod ((r + 1) % 4) 0 := by
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;> rfl

private lemma radMod_diag (r : ℕ) (hr : r < 4) :
    radMod ((r + 1) % 4) r = false := by
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;> rfl

private lemma radMod_sub_one_step (m : ℕ) (hm : m < 4) :
    (radMod ((m + 2) % 4) ((m + 1) % 4) == radMod ((m + 2) % 4) m) =
      radMod ((m + 3) % 4) ((m + 1) % 4) := by
  rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) with rfl | rfl | rfl | rfl <;> rfl

private lemma radMod_inner_step (r m : ℕ) (hr : r < 4) (hm : m < 4) :
    (radMod r ((m + 1) % 4) == (radMod r m && radMod r ((m + 2) % 4))) =
      radMod ((r + 1) % 4) ((m + 1) % 4) := by
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) with rfl | rfl | rfl | rfl <;>
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) with rfl | rfl | rfl | rfl <;> rfl

private lemma radState_succ (t d : ℕ) :
    (radState t d ==
      (if d = 0 then radState t 1 else radState t (d - 1) && radState t (d + 1))) =
      radState (t + 1) d := by
  rcases eq_or_ne t 0 with rfl | ht0
  · rcases eq_or_ne d 0 with rfl | hd0
    · rfl
    · have h1 : 1 ≤ d := by omega
      simp [radState, hd0, h1]
  · rcases eq_or_ne d 0 with rfl | hd0
    · rcases eq_or_ne t 1 with rfl | ht1
      · rfl
      · have h0t : ¬(t ≤ 0) := by omega
        have h1t : ¬(t ≤ 1) := by omega
        have h0t1 : ¬(t + 1 ≤ 0) := by omega
        have hr1 : (t + 1) % 4 = (t % 4 + 1) % 4 := Nat.add_mod t 1 4
        simp only [↓reduceIte, radState, ht0, Nat.add_eq_zero_iff, one_ne_zero, and_false,
          h0t, h1t, h0t1, Nat.zero_mod, Nat.one_mod, hr1]
        exact radMod_zero_step (t % 4) (Nat.mod_lt t (by omega))
    · rw [if_neg hd0]
      by_cases hge : t + 1 ≤ d
      · have h1 : t ≤ d := by omega
        have h2 : t ≤ d - 1 := by omega
        have h3 : t ≤ d + 1 := by omega
        simp [radState, ht0, hge, h1, h2, h3]
      · by_cases heq : d = t
        · subst heq
          have h1 : d ≤ d := le_rfl
          have h2 : ¬(d ≤ d - 1) := by omega
          have h3 : d ≤ d + 1 := by omega
          have h4 : ¬(d + 1 ≤ d) := by omega
          have hr1 : d % 4 = ((d - 1) % 4 + 1) % 4 := by omega
          have hr2 : (d + 1) % 4 = (((d - 1) % 4 + 1) % 4 + 1) % 4 := by omega
          simp only [radState, ht0, ↓reduceIte, h1, h2, h3, h4, Bool.and_true,
            Bool.true_beq, Nat.add_eq_zero_iff, one_ne_zero, and_false]
          rw [hr1, hr2, radMod_diag ((d - 1) % 4) (Nat.mod_lt _ (by omega)),
              radMod_diag (((d - 1) % 4 + 1) % 4) (Nat.mod_lt _ (by omega))]
        · by_cases heq1 : d + 1 = t
          · subst heq1
            have h1 : ¬(d + 1 ≤ d) := by omega
            have h2 : ¬(d + 1 ≤ d - 1) := by omega
            have h3 : d + 1 ≤ d + 1 := le_rfl
            have h4 : ¬(d + 1 + 1 ≤ d) := by omega
            have hm1 : d % 4 = ((d - 1) % 4 + 1) % 4 := by omega
            have hm2 : (d + 1) % 4 = ((d - 1) % 4 + 2) % 4 := by omega
            have hm3 : (d + 1 + 1) % 4 = ((d - 1) % 4 + 3) % 4 := by omega
            simp only [radState, ht0, ↓reduceIte, h1, h2, h3, h4, Bool.and_true,
              Nat.add_eq_zero_iff, one_ne_zero, and_false]
            rw [hm3, hm2, hm1]
            exact radMod_sub_one_step ((d - 1) % 4) (Nat.mod_lt _ (by omega))
          · have h1 : ¬(t ≤ d) := by omega
            have h2 : ¬(t ≤ d - 1) := by omega
            have h3 : ¬(t ≤ d + 1) := by omega
            have h4 : ¬(t + 1 ≤ d) := by omega
            have hr1 : (t + 1) % 4 = (t % 4 + 1) % 4 := by omega
            have hm1 : d % 4 = ((d - 1) % 4 + 1) % 4 := by omega
            have hm2 : (d + 1) % 4 = ((d - 1) % 4 + 2) % 4 := by omega
            simp only [radState, ht0, ↓reduceIte, h1, h2, h3, h4,
              Nat.add_eq_zero_iff, one_ne_zero, and_false]
            rw [hr1, hm2, hm1]
            exact radMod_inner_step (t % 4) ((d - 1) % 4)
              (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))

private lemma state_eq_radState (t : ℕ) (x y : ℤ) :
    OMA.S_oeis_a273145.state t x y = radState t (x.natAbs + y.natAbs) := by
  induction t generalizing x y with
  | zero =>
    simp [OMA.S_oeis_a273145.state, radState]
  | succ t ih =>
    rw [state_succ, ih, ih, ih, ih, ih,
        four_neighbors_natAbs (radState t) x y, radState_succ]

theorem state_one (x y : ℤ) :
    OMA.S_oeis_a273145.state 1 x y = !decide (x = 0 ∧ y = 0) := by
  rw [state_eq_radState]
  by_cases h : x.natAbs + y.natAbs = 0
  · have hx : x = 0 := Int.natAbs_eq_zero.mp (by omega)
    have hy : y = 0 := Int.natAbs_eq_zero.mp (by omega)
    subst hx; subst hy; rfl
  · have hxy : ¬(x = 0 ∧ y = 0) := by
      rintro ⟨rfl, rfl⟩
      exact h rfl
    have hge : 1 ≤ x.natAbs + y.natAbs := by omega
    simp [radState, hge, hxy]

theorem state_pow_sub_one {n : ℕ} (hn : 1 < n) (x y : ℤ) :
    OMA.S_oeis_a273145.state (2 ^ n - 1) x y =
      !decide (x.natAbs + y.natAbs < 2 ^ n ∧ (x.natAbs + y.natAbs) % 4 = 2) := by
  rw [state_eq_radState]
  have hdiv : 2 ^ n = 4 * 2 ^ (n - 2) := by
    conv_lhs => rw [show n = (n - 2) + 2 by omega]
    ring
  have hpos : 0 < 2 ^ (n - 2) := Nat.pos_of_ne_zero (by positivity)
  have ht0 : 2 ^ n - 1 ≠ 0 := by omega
  have htmod : (2 ^ n - 1) % 4 = 3 := by omega
  set d := x.natAbs + y.natAbs
  by_cases hle : 2 ^ n - 1 ≤ d
  · have hnot : ¬(d < 2 ^ n ∧ d % 4 = 2) := by omega
    simp [radState, ht0, hle, hnot]
  · have hdlt : d < 2 ^ n := by omega
    simp [radState, radMod, ht0, hle, htmod, hdlt]

section CACounting

private def ca_l1_pt (d s : ℕ) : ℤ × ℤ :=
  if s < d then
    (((d - s : ℕ) : ℤ), (s : ℤ))
  else if s < 2 * d then
    (-(((s - d : ℕ) : ℤ)), (((2 * d - s : ℕ) : ℤ)))
  else if s < 3 * d then
    (-(((3 * d - s : ℕ) : ℤ)), -(((s - 2 * d : ℕ) : ℤ)))
  else
    ((((s - 3 * d : ℕ) : ℤ)), -(((4 * d - s : ℕ) : ℤ)))

private theorem ca_l1_pt_natAbs {d s : ℕ} (hs : s < 4 * d) :
    (ca_l1_pt d s).1.natAbs + (ca_l1_pt d s).2.natAbs = d := by
  unfold ca_l1_pt
  split_ifs <;> simp <;> omega

private theorem ca_l1_pt_inj {d₁ s₁ d₂ s₂ : ℕ}
    (hs₁ : s₁ < 4 * d₁) (hs₂ : s₂ < 4 * d₂)
    (heq : ca_l1_pt d₁ s₁ = ca_l1_pt d₂ s₂) :
    d₁ = d₂ ∧ s₁ = s₂ := by
  have hd : d₁ = d₂ := by
    rw [← ca_l1_pt_natAbs hs₁, ← ca_l1_pt_natAbs hs₂, heq]
  subst hd
  refine ⟨rfl, ?_⟩
  unfold ca_l1_pt at heq
  split_ifs at heq <;> simp only [Prod.mk.injEq] at heq <;> omega

private theorem ca_l1_pt_surj {d : ℕ} (hd : 1 ≤ d) {x y : ℤ}
    (hxy : x.natAbs + y.natAbs = d) :
    ∃ s < 4 * d, ca_l1_pt d s = (x, y) := by
  by_cases h1 : 0 < x ∧ 0 ≤ y
  · have hs0 : y.natAbs < d := by omega
    refine ⟨y.natAbs, by omega, ?_⟩
    unfold ca_l1_pt
    rw [if_pos hs0]
    ext <;> dsimp <;> omega
  · by_cases h2 : x ≤ 0 ∧ 0 < y
    · have hs0 : ¬ d + x.natAbs < d := by omega
      have hs1 : d + x.natAbs < 2 * d := by omega
      refine ⟨d + x.natAbs, by omega, ?_⟩
      unfold ca_l1_pt
      rw [if_neg hs0, if_pos hs1]
      ext <;> dsimp <;> omega
    · by_cases h3 : x < 0 ∧ y ≤ 0
      · have hs0 : ¬ 2 * d + y.natAbs < d := by omega
        have hs1 : ¬ 2 * d + y.natAbs < 2 * d := by omega
        have hs2 : 2 * d + y.natAbs < 3 * d := by omega
        refine ⟨2 * d + y.natAbs, by omega, ?_⟩
        unfold ca_l1_pt
        rw [if_neg hs0, if_neg hs1, if_pos hs2]
        ext <;> dsimp <;> omega
      · have h4 : 0 ≤ x ∧ y < 0 := by omega
        have hs0 : ¬ 3 * d + x.natAbs < d := by omega
        have hs1 : ¬ 3 * d + x.natAbs < 2 * d := by omega
        have hs2 : ¬ 3 * d + x.natAbs < 3 * d := by omega
        refine ⟨3 * d + x.natAbs, by omega, ?_⟩
        unfold ca_l1_pt
        rw [if_neg hs0, if_neg hs1, if_neg hs2]
        ext <;> dsimp <;> omega

private theorem ca_sum_off_radii (M : ℕ) :
    ∑ k ∈ Finset.range M, 4 * (4 * k + 2) = 8 * M ^ 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    ring

private theorem ca_card_off_box (M : ℕ) (hM : 1 ≤ M) :
    ((Finset.Icc (-((4 * M - 1 : ℕ) : ℤ)) ((4 * M - 1 : ℕ) : ℤ) ×ˢ
      Finset.Icc (-((4 * M - 1 : ℕ) : ℤ)) ((4 * M - 1 : ℕ) : ℤ)).filter
      (fun p => p.1.natAbs + p.2.natAbs < 4 * M - 1 ∧
        (p.1.natAbs + p.2.natAbs) % 4 = 2)).card = 8 * M ^ 2 := by
  let S := (Finset.range M).sigma (fun k => Finset.range (4 * (4 * k + 2)))
  have hS_card : S.card = 8 * M ^ 2 := by
    simp only [S, Finset.card_sigma, Finset.card_range]
    exact ca_sum_off_radii M
  rw [← hS_card]
  symm
  refine Finset.card_bij (fun p _ => ca_l1_pt (4 * p.1 + 2) p.2) ?_ ?_ ?_
  · rintro ⟨k, s⟩ hks
    simp only [S, Finset.mem_sigma, Finset.mem_range] at hks
    rcases hks with ⟨hk, hs⟩
    have hd : (ca_l1_pt (4 * k + 2) s).1.natAbs + (ca_l1_pt (4 * k + 2) s).2.natAbs = 4 * k + 2 :=
      ca_l1_pt_natAbs hs
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_, ?_⟩ <;> omega
  · rintro ⟨k₁, s₁⟩ hk₁ ⟨k₂, s₂⟩ hk₂ heq
    simp only [S, Finset.mem_sigma, Finset.mem_range] at hk₁ hk₂
    rcases ca_l1_pt_inj hk₁.2 hk₂.2 heq with ⟨h4, rfl⟩
    have hk_eq : k₁ = k₂ := by omega
    subst hk_eq
    rfl
  · rintro ⟨x, y⟩ hxy
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hxy
    rcases hxy with ⟨_, hlt, hmod⟩
    let k := (x.natAbs + y.natAbs) / 4
    have hkM : k < M := by omega
    have hxy_eq : x.natAbs + y.natAbs = 4 * k + 2 := by omega
    obtain ⟨s, hs, hpt⟩ := ca_l1_pt_surj (by omega : 1 ≤ 4 * k + 2) hxy_eq
    refine ⟨⟨k, s⟩, ?_, hpt⟩
    simp only [S, Finset.mem_sigma, Finset.mem_range]
    exact ⟨hkM, hs⟩

theorem ca_a_zero : OMA.S_oeis_a273145.a 0 = 1 := by
  unfold OMA.S_oeis_a273145.a OMA.S_oeis_a273145.count
  change ((Finset.Icc (-(0 : ℤ)) (0 : ℤ) ×ˢ Finset.Icc (-(0 : ℤ)) (0 : ℤ)).filter
    (fun p => OMA.S_oeis_a273145.state 0 p.1 p.2 = true)).card = 1
  have h_eq : ((Finset.Icc (-(0 : ℤ)) (0 : ℤ) ×ˢ Finset.Icc (-(0 : ℤ)) (0 : ℤ)).filter
      (fun p => OMA.S_oeis_a273145.state 0 p.1 p.2 = true)) = {(0, 0)} := by
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_singleton, Prod.mk.injEq, OMA.S_oeis_a273145.state, decide_eq_true_eq]
    omega
  rw [h_eq, Finset.card_singleton]

theorem ca_a_one : OMA.S_oeis_a273145.a 1 = 8 := by
  unfold OMA.S_oeis_a273145.a OMA.S_oeis_a273145.count
  let B1 : Finset (ℤ × ℤ) := Finset.Icc (-(1 : ℤ)) (1 : ℤ) ×ˢ Finset.Icc (-(1 : ℤ)) (1 : ℤ)
  change (B1.filter (fun p => OMA.S_oeis_a273145.state 1 p.1 p.2 = true)).card = 8
  have h_eq : B1.filter (fun p => OMA.S_oeis_a273145.state 1 p.1 p.2 = true) = B1.erase (0, 0) := by
    ext ⟨x, y⟩
    simp only [B1, Finset.mem_filter, Finset.mem_erase, ne_eq, Prod.mk.injEq,
      Finset.mem_product, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hx, hy⟩, hst⟩
      refine ⟨?_, hx, hy⟩
      have hx3 : x = -1 ∨ x = 0 ∨ x = 1 := by omega
      have hy3 : y = -1 ∨ y = 0 ∨ y = 1 := by omega
      rcases hx3 with rfl | rfl | rfl <;> rcases hy3 with rfl | rfl | rfl <;>
        revert hst <;> decide +kernel
    · rintro ⟨hne, hx, hy⟩
      refine ⟨⟨hx, hy⟩, ?_⟩
      have hx3 : x = -1 ∨ x = 0 ∨ x = 1 := by omega
      have hy3 : y = -1 ∨ y = 0 ∨ y = 1 := by omega
      rcases hx3 with rfl | rfl | rfl <;> rcases hy3 with rfl | rfl | rfl <;>
        revert hne <;> decide +kernel
  have hmem : ((0 : ℤ), (0 : ℤ)) ∈ B1 := by
    simp [B1]
  have hcard : B1.card = 9 := by
    simp [B1, Finset.card_product, Int.card_Icc]
  rw [h_eq, Finset.card_erase_of_mem hmem, hcard]

theorem ca_blomberg_of_state
    (h_state : ∀ {n : ℕ}, 1 < n → ∀ x y : ℤ,
      OMA.S_oeis_a273145.state (2 ^ n - 1) x y =
        !decide (x.natAbs + y.natAbs < 2 ^ n ∧ (x.natAbs + y.natAbs) % 4 = 2)) :
    ∀ n : ℕ, 1 < n → (OMA.S_oeis_a273145.a n : ℤ) = 14 * 4 ^ (n - 1) - 4 * 2 ^ n + 1 := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 2 := ⟨n - 2, by omega⟩
  let M : ℕ := 2 ^ m
  have hM_pos : 1 ≤ M := Nat.one_le_two_pow
  have hpow : 2 ^ (m + 2) = 4 * M := by
    simp only [M]
    ring
  unfold OMA.S_oeis_a273145.a OMA.S_oeis_a273145.count
  let t : ℕ := 2 ^ (m + 2) - 1
  let B : Finset (ℤ × ℤ) := Finset.Icc (-(t : ℤ)) (t : ℤ) ×ˢ Finset.Icc (-(t : ℤ)) (t : ℤ)
  change ((B.filter (fun p => OMA.S_oeis_a273145.state t p.1 p.2 = true)).card : ℤ) =
    14 * 4 ^ (m + 2 - 1) - 4 * 2 ^ (m + 2) + 1
  have h_part := Finset.card_filter_add_card_filter_not
    (s := B) (fun p => OMA.S_oeis_a273145.state t p.1 p.2 = true)
  have ht_eq : t = 4 * M - 1 := by
    simp only [t, hpow]
  have h_neg_eq : B.filter (fun p => ¬ (OMA.S_oeis_a273145.state t p.1 p.2 = true)) =
      B.filter (fun p => p.1.natAbs + p.2.natAbs < t ∧ (p.1.natAbs + p.2.natAbs) % 4 = 2) := by
    refine Finset.filter_congr ?_
    rintro ⟨x, y⟩ _
    have hst := h_state (by omega : 1 < m + 2) x y
    change ¬ (OMA.S_oeis_a273145.state (2 ^ (m + 2) - 1) x y = true) ↔
      x.natAbs + y.natAbs < t ∧ (x.natAbs + y.natAbs) % 4 = 2
    rw [hst, ht_eq, hpow]
    simp only [Bool.not_eq_true, Bool.not_eq_false', decide_eq_true_eq]
    have hM1 : 1 ≤ M := hM_pos
    omega
  have h_off_card : (B.filter (fun p => ¬ (OMA.S_oeis_a273145.state t p.1 p.2 = true))).card =
      8 * M ^ 2 := by
    rw [h_neg_eq]
    simpa only [B, ht_eq] using ca_card_off_box M hM_pos
  have hB_card : B.card = (2 * t + 1) * (2 * t + 1) := by
    have hIcc : (Finset.Icc (-(t : ℤ)) (t : ℤ)).card = 2 * t + 1 := by
      rw [Int.card_Icc]
      omega
    simp only [B, Finset.card_product, hIcc]
  rw [h_off_card, hB_card] at h_part
  have h2t1 : 2 * t + 1 = 8 * M - 1 := by
    omega
  rw [h2t1] at h_part
  have h_part_z : ((B.filter (fun p => OMA.S_oeis_a273145.state t p.1 p.2 = true)).card : ℤ) +
      (8 * (M : ℤ) ^ 2) = (8 * (M : ℤ) - 1) * (8 * (M : ℤ) - 1) := by
    have h8M : (1 : ℕ) ≤ 8 * M := by omega
    zify [h8M] at h_part
    linarith
  have h4 : (4 : ℤ) ^ (m + 2 - 1) = 4 * ((2 : ℤ) ^ m) ^ 2 := by
    have hm1 : m + 2 - 1 = m + 1 := by omega
    rw [hm1, pow_succ', show (4 : ℤ) = 2 ^ 2 by norm_num, pow_right_comm]
  have h2 : (2 : ℤ) ^ (m + 2) = 4 * (2 : ℤ) ^ m := by ring
  have hM_cast : (M : ℤ) = (2 : ℤ) ^ m := by simp [M]
  rw [hM_cast] at h_part_z
  rw [h4, h2]
  linarith

theorem ca_barker_recurrence_of_blomberg
    (h_blomberg : ∀ n : ℕ, 1 < n →
      (OMA.S_oeis_a273145.a n : ℤ) = 14 * 4 ^ (n - 1) - 4 * 2 ^ n + 1) :
    ∀ n : ℕ, 4 < n →
      (OMA.S_oeis_a273145.a n : ℤ) =
        7 * OMA.S_oeis_a273145.a (n - 1) - 14 * OMA.S_oeis_a273145.a (n - 2) +
          8 * OMA.S_oeis_a273145.a (n - 3) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 5 := ⟨n - 5, by omega⟩
  have h0 := h_blomberg (m + 5) (by omega)
  have h1 := h_blomberg (m + 4) (by omega)
  have h2 := h_blomberg (m + 3) (by omega)
  have h3 := h_blomberg (m + 2) (by omega)
  have s1 : m + 5 - 1 = m + 4 := by omega
  have s2 : m + 5 - 2 = m + 3 := by omega
  have s3 : m + 5 - 3 = m + 2 := by omega
  have t1 : m + 4 - 1 = m + 3 := by omega
  have t2 : m + 3 - 1 = m + 2 := by omega
  have t3 : m + 2 - 1 = m + 1 := by omega
  rw [s1, s2, s3, h0, h1, h2, h3, s1, t1, t2, t3]
  ring

private theorem ca_gf_of_seq (f : ℕ → ℤ)
    (hf0 : f 0 = 1) (hf1 : f 1 = 8) (hf2 : f 2 = 41) (hf3 : f 3 = 193) (hf4 : f 4 = 833)
    (h_rec : ∀ n : ℕ, 4 < n → f n = 7 * f (n - 1) - 14 * f (n - 2) + 8 * f (n - 3)) :
    PowerSeries.mk f *
      ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 4 * PowerSeries.X)) =
      1 + PowerSeries.X - PowerSeries.X ^ 2 + 10 * PowerSeries.X ^ 3 - 8 * PowerSeries.X ^ 4 := by
  let A : PowerSeries ℤ := PowerSeries.mk f
  change A * ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 4 * PowerSeries.X)) =
    1 + PowerSeries.X - PowerSeries.X ^ 2 + 10 * PowerSeries.X ^ 3 - 8 * PowerSeries.X ^ 4
  have h_expand :
      A * ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 4 * PowerSeries.X)) =
        A - PowerSeries.C (7 : ℤ) * (A * PowerSeries.X ^ 1) +
          PowerSeries.C (14 : ℤ) * (A * PowerSeries.X ^ 2) -
          PowerSeries.C (8 : ℤ) * (A * PowerSeries.X ^ 3) := by
    simp only [map_ofNat]
    ring
  have h_rhs :
      (1 + PowerSeries.X - PowerSeries.X ^ 2 + 10 * PowerSeries.X ^ 3 -
        8 * PowerSeries.X ^ 4 : PowerSeries ℤ) =
        1 + PowerSeries.X ^ 1 - PowerSeries.X ^ 2 +
          PowerSeries.C (10 : ℤ) * (PowerSeries.X ^ 3) -
          PowerSeries.C (8 : ℤ) * (PowerSeries.X ^ 4) := by
    simp only [map_ofNat]
    ring
  rw [h_expand, h_rhs]
  ext n
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul]
  simp only [PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
    PowerSeries.coeff_one, PowerSeries.coeff_X_pow, A]
  by_cases hle : n ≤ 4
  · interval_cases n <;> (norm_num; linarith)
  · have hgt : 4 < n := by omega
    have hrm := h_rec n hgt
    have h1 : 1 ≤ n := by omega
    have h2 : 2 ≤ n := by omega
    have h3 : 3 ≤ n := by omega
    have ne0 : n ≠ 0 := by omega
    have ne1 : n ≠ 1 := by omega
    have ne2 : n ≠ 2 := by omega
    have ne3 : n ≠ 3 := by omega
    have ne4 : n ≠ 4 := by omega
    simp only [h1, h2, h3, ne0, ne1, ne2, ne3, ne4, ↓reduceIte]
    linarith

theorem ca_barker_gf_of_blomberg
    (h_blomberg : ∀ n : ℕ, 1 < n →
      (OMA.S_oeis_a273145.a n : ℤ) = 14 * 4 ^ (n - 1) - 4 * 2 ^ n + 1) :
    PowerSeries.mk (fun n => (OMA.S_oeis_a273145.a n : ℤ)) *
      ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 4 * PowerSeries.X)) =
      1 + PowerSeries.X - PowerSeries.X ^ 2 + 10 * PowerSeries.X ^ 3 - 8 * PowerSeries.X ^ 4 := by
  refine ca_gf_of_seq (fun n => (OMA.S_oeis_a273145.a n : ℤ)) ?_ ?_ ?_ ?_ ?_
    (ca_barker_recurrence_of_blomberg h_blomberg)
  · exact_mod_cast ca_a_zero
  · exact_mod_cast ca_a_one
  · rw [h_blomberg 2 (by omega)]; norm_num
  · rw [h_blomberg 3 (by omega)]; norm_num
  · rw [h_blomberg 4 (by omega)]; norm_num

theorem ca_counting_all
    (h_state : ∀ {n : ℕ}, 1 < n → ∀ x y : ℤ,
      OMA.S_oeis_a273145.state (2 ^ n - 1) x y =
        !decide (x.natAbs + y.natAbs < 2 ^ n ∧ (x.natAbs + y.natAbs) % 4 = 2)) :
    (∀ n : ℕ, 1 < n → (OMA.S_oeis_a273145.a n : ℤ) = 14 * 4 ^ (n - 1) - 4 * 2 ^ n + 1) ∧
    (∀ n : ℕ, 4 < n → (OMA.S_oeis_a273145.a n : ℤ) =
      7 * OMA.S_oeis_a273145.a (n - 1) - 14 * OMA.S_oeis_a273145.a (n - 2) +
        8 * OMA.S_oeis_a273145.a (n - 3)) ∧
    PowerSeries.mk (fun n => (OMA.S_oeis_a273145.a n : ℤ)) *
      ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 4 * PowerSeries.X)) =
      1 + PowerSeries.X - PowerSeries.X ^ 2 + 10 * PowerSeries.X ^ 3 - 8 * PowerSeries.X ^ 4 := by
  have h_blomberg := ca_blomberg_of_state h_state
  exact ⟨h_blomberg, ca_barker_recurrence_of_blomberg h_blomberg,
    ca_barker_gf_of_blomberg h_blomberg⟩

end CACounting

theorem OMA.solution : type_of% @OMA.S_oeis_a273145.main := by
  exact ca_counting_all state_pow_sub_one
