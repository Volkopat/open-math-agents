import OMAStatements.S_oeis_a234779

-- Problem: A234779: Number of (n+1) X (1+1) 0..3 arrays with no adjacent elements equal and with each 2 X 2 subblock having the number of clockwise edge increases equal to the number of counterclockwise edge increases.
-- Upstream: formal-conjectures statements/oeis-a234779.lean:0 (declaration OMA.S_oeis_a234779.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: c(m, p, q) counts the valid arrays with m+1 rows whose last row is (p, q). Removing
-- the last row (Fin.init, inverse Fin.snoc) shows that a valid array with m+2 rows is a valid
-- array t with m+1 rows followed by a row (p', q') in 0..3 with p' different from q', from the last
-- row (p, q) of t columnwise, and with the block condition for the rows (p, q), (p', q'). This
-- gives transfer equations c(m+1, .) = M c(m, .) for a 12 x 12 matrix M (16 x 16 with zero rows
-- and columns for p = q) with 1^T (M^2 - 7M + 4) = 0, so a(m+2) + 4 a(m) = 7 a(m+1) is a linear
-- consequence of the equations at two levels (omega). With a(0) = 12 and a(1) = 76 the g.f.
-- follows by comparing coefficients, and u(n) = (7 - s)^n (-17 + 3s) + (7 + s)^n (17 + 3s),
-- s = sqrt 33, satisfies u(n+2) = 14 u(n+1) - 16 u(n), which gives 2^(n-1) s a(n) = u(n).

/-- The arrays counted by A234779 (with m+1 rows). -/
def V234779 (m : ℕ) : Finset (Fin (m + 1) → Fin 2 → ℕ) :=
  (Fintype.piFinset fun _ : Fin (m + 1) => Fintype.piFinset fun _ : Fin 2 => Finset.range 4).filter
    (fun x => (∀ i : Fin (m + 1), x i 0 ≠ x i 1) ∧
      ∀ i : Fin m, x i.castSucc 0 ≠ x i.succ 0 ∧ x i.castSucc 1 ≠ x i.succ 1 ∧
        OMA.S_oeis_a234779.cw (x i.castSucc 0) (x i.castSucc 1) (x i.succ 0) (x i.succ 1) =
          OMA.S_oeis_a234779.cw (x i.castSucc 0) (x i.succ 0) (x i.castSucc 1) (x i.succ 1))

/-- The arrays of V234779 m whose last row is (p, q). -/
def C234779 (m p q : ℕ) : Finset (Fin (m + 1) → Fin 2 → ℕ) :=
  (V234779 m).filter (fun x => (x (Fin.last m) 0, x (Fin.last m) 1) = (p, q))

theorem vmem234779 (m : ℕ) (x : Fin (m + 1) → Fin 2 → ℕ) :
    x ∈ V234779 m ↔ (∀ i j, x i j < 4) ∧ (∀ i : Fin (m + 1), x i 0 ≠ x i 1) ∧
      ∀ i : Fin m, x i.castSucc 0 ≠ x i.succ 0 ∧ x i.castSucc 1 ≠ x i.succ 1 ∧
        OMA.S_oeis_a234779.cw (x i.castSucc 0) (x i.castSucc 1) (x i.succ 0) (x i.succ 1) =
          OMA.S_oeis_a234779.cw (x i.castSucc 0) (x i.succ 0) (x i.castSucc 1) (x i.succ 1) := by
  unfold V234779
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  simp only [Fintype.mem_piFinset, Finset.mem_range]

theorem smem234779 (m : ℕ) (t : Fin (m + 1) → Fin 2 → ℕ) (R : Fin 2 → ℕ) :
    (Fin.snoc t R : Fin (m + 1 + 1) → Fin 2 → ℕ) ∈ V234779 (m + 1) ↔
      t ∈ V234779 m ∧ (R 0 < 4 ∧ R 1 < 4) ∧ R 0 ≠ R 1 ∧
        (t (Fin.last m) 0 ≠ R 0 ∧ t (Fin.last m) 1 ≠ R 1 ∧
          OMA.S_oeis_a234779.cw (t (Fin.last m) 0) (t (Fin.last m) 1) (R 0) (R 1) =
            OMA.S_oeis_a234779.cw (t (Fin.last m) 0) (R 0) (t (Fin.last m) 1) (R 1)) := by
  rw [vmem234779, vmem234779]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨fun i j => ?_, fun i => ?_, fun i => ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
    · have h := h1 i.castSucc j
      rw [Fin.snoc_castSucc] at h
      exact h
    · have h := h2 i.castSucc
      rw [Fin.snoc_castSucc] at h
      exact h
    · have h := h3 i.castSucc
      rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc] at h
      exact h
    · have h := h1 (Fin.last (m + 1)) 0
      rw [Fin.snoc_last] at h
      exact h
    · have h := h1 (Fin.last (m + 1)) 1
      rw [Fin.snoc_last] at h
      exact h
    · have h := h2 (Fin.last (m + 1))
      rw [Fin.snoc_last] at h
      exact h
    · have h := h3 (Fin.last m)
      rw [show (Fin.last m).succ = Fin.last (m + 1) from Fin.succ_last m, Fin.snoc_last,
        Fin.snoc_castSucc] at h
      exact h
  · rintro ⟨⟨h1, h2, h3⟩, ⟨h4, h5⟩, h6, h7⟩
    have h8 : ∀ j : Fin 2, R j < 4 := Fin.forall_fin_two.2 ⟨h4, h5⟩
    refine ⟨fun i j => ?_, fun i => ?_, fun i => ?_⟩
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · rw [Fin.snoc_castSucc]
        exact h1 i' j
      · rw [Fin.snoc_last]
        exact h8 j
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · rw [Fin.snoc_castSucc]
        exact h2 i'
      · rw [Fin.snoc_last]
        exact h6
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact h3 i'
      · rw [show (Fin.last m).succ = Fin.last (m + 1) from Fin.succ_last m, Fin.snoc_last,
          Fin.snoc_castSucc]
        exact h7

/-- The block (p q / r s) read along the cycle p, q, s, r is a rotation of 0, 1, 2, 3 or of
3, 2, 1, 0. -/
abbrev mono234779 (p q r s : ℕ) : Prop :=
  (p = 0 ∧ q = 1 ∧ s = 2 ∧ r = 3) ∨ (p = 1 ∧ q = 2 ∧ s = 3 ∧ r = 0) ∨
    (p = 2 ∧ q = 3 ∧ s = 0 ∧ r = 1) ∨ (p = 3 ∧ q = 0 ∧ s = 1 ∧ r = 2) ∨
    (p = 3 ∧ q = 2 ∧ s = 1 ∧ r = 0) ∨ (p = 2 ∧ q = 1 ∧ s = 0 ∧ r = 3) ∨
    (p = 1 ∧ q = 0 ∧ s = 3 ∧ r = 2) ∨ (p = 0 ∧ q = 3 ∧ s = 2 ∧ r = 1)

/-- For entries in 0..3 and adjacent entries distinct, the block condition fails exactly for
the cyclically monotone blocks. -/
abbrev triff234779 (p q r s : ℕ) : Prop :=
  (p ≠ q ∧ r ≠ s ∧ p ≠ r ∧ q ≠ s ∧
      OMA.S_oeis_a234779.cw p q r s = OMA.S_oeis_a234779.cw p r q s) ↔
    (p ≠ q ∧ r ≠ s ∧ p ≠ r ∧ q ≠ s ∧ ¬ mono234779 p q r s)

theorem tr0_234779 (q r s : ℕ) (hq : q < 4) (hr : r < 4) (hs : s < 4) : triff234779 0 q r s := by
  interval_cases q <;> interval_cases r <;> interval_cases s <;> decide

theorem tr1_234779 (q r s : ℕ) (hq : q < 4) (hr : r < 4) (hs : s < 4) : triff234779 1 q r s := by
  interval_cases q <;> interval_cases r <;> interval_cases s <;> decide

theorem tr2_234779 (q r s : ℕ) (hq : q < 4) (hr : r < 4) (hs : s < 4) : triff234779 2 q r s := by
  interval_cases q <;> interval_cases r <;> interval_cases s <;> decide

theorem tr3_234779 (q r s : ℕ) (hq : q < 4) (hr : r < 4) (hs : s < 4) : triff234779 3 q r s := by
  interval_cases q <;> interval_cases r <;> interval_cases s <;> decide

theorem tr234779 (p q r s : ℕ) (hp : p < 4) (hq : q < 4) (hr : r < 4) (hs : s < 4) :
    (p ≠ q ∧ r ≠ s ∧ p ≠ r ∧ q ≠ s ∧
        OMA.S_oeis_a234779.cw p q r s = OMA.S_oeis_a234779.cw p r q s) ↔
      (p ≠ q ∧ r ≠ s ∧ p ≠ r ∧ q ≠ s ∧ ¬ mono234779 p q r s) := by
  interval_cases p
  · exact tr0_234779 q r s hq hr hs
  · exact tr1_234779 q r s hq hr hs
  · exact tr2_234779 q r s hq hr hs
  · exact tr3_234779 q r s hq hr hs

/-- One fibre of the last step. -/
theorem fib234779 (m p' q' p q : ℕ) :
    ((C234779 (m + 1) p' q').filter
        (fun x : Fin (m + 1 + 1) → Fin 2 → ℕ =>
          (Fin.init x (Fin.last m) 0, Fin.init x (Fin.last m) 1) = (p, q))).card =
      if p' < 4 ∧ q' < 4 ∧ p < 4 ∧ q < 4 ∧
        (p ≠ q ∧ p' ≠ q' ∧ p ≠ p' ∧ q ≠ q' ∧ ¬ mono234779 p q p' q') then
        (C234779 m p q).card else 0 := by
  split_ifs with h
  · obtain ⟨h1, h2, hp4, hq4, h5⟩ := h
    obtain ⟨-, h3, h4, h5, h6⟩ := (tr234779 p q p' q' hp4 hq4 h1 h2).2 h5
    obtain ⟨R, hR0, hR1⟩ : ∃ R : Fin 2 → ℕ, R 0 = p' ∧ R 1 = q' :=
      ⟨fun j => if j = 0 then p' else q', if_pos (rfl : (0 : Fin 2) = 0),
        if_neg (show ¬ ((1 : Fin 2) = 0) by decide)⟩
    symm
    apply Finset.card_nbij'
      (fun t : Fin (m + 1) → Fin 2 → ℕ => (Fin.snoc t R : Fin (m + 1 + 1) → Fin 2 → ℕ))
      (fun x : Fin (m + 1 + 1) → Fin 2 → ℕ => Fin.init x)
    · intro t ht
      simp only [Finset.mem_coe] at ht ⊢
      unfold C234779 at ht ⊢
      rw [Finset.mem_filter, Prod.mk.injEq] at ht
      obtain ⟨ht1, ht2, ht3⟩ := ht
      rw [Finset.mem_filter, Finset.mem_filter, smem234779, Fin.init_snoc, Fin.snoc_last, hR0,
        hR1, ht2, ht3]
      exact ⟨⟨⟨ht1, ⟨h1, h2⟩, h3, ⟨h4, h5, h6⟩⟩, rfl⟩, rfl⟩
    · intro x hx
      simp only [Finset.mem_coe] at hx ⊢
      unfold C234779 at hx ⊢
      simp only [Finset.mem_filter, Prod.mk.injEq] at hx
      obtain ⟨⟨hxV, -, -⟩, hp1, hp2⟩ := hx
      have e : x = (Fin.snoc (Fin.init x) (x (Fin.last (m + 1))) :
          Fin (m + 1 + 1) → Fin 2 → ℕ) := (Fin.snoc_init_self x).symm
      rw [e, smem234779] at hxV
      rw [Finset.mem_filter]
      exact ⟨hxV.1, Prod.mk_inj.2 ⟨hp1, hp2⟩⟩
    · intro t _
      simp only [Fin.init_snoc]
    · intro x hx
      simp only [Finset.mem_coe] at hx
      unfold C234779 at hx
      simp only [Finset.mem_filter, Prod.mk.injEq] at hx
      obtain ⟨⟨-, hq1, hq2⟩, -, -⟩ := hx
      show (Fin.snoc (Fin.init x) R : Fin (m + 1 + 1) → Fin 2 → ℕ) = x
      have hj : ∀ j : Fin 2, x (Fin.last (m + 1)) j = R j :=
        Fin.forall_fin_two.2 ⟨hq1.trans hR0.symm, hq2.trans hR1.symm⟩
      have hl : x (Fin.last (m + 1)) = R := funext hj
      rw [← hl]
      exact Fin.snoc_init_self x
  · rw [Finset.card_eq_zero]
    apply Finset.subset_empty.1
    intro x hx
    exfalso
    unfold C234779 at hx
    simp only [Finset.mem_filter, Prod.mk.injEq] at hx
    obtain ⟨⟨hxV, hq1, hq2⟩, hp1, hp2⟩ := hx
    have e : x = (Fin.snoc (Fin.init x) (x (Fin.last (m + 1))) :
        Fin (m + 1 + 1) → Fin 2 → ℕ) := (Fin.snoc_init_self x).symm
    rw [e, smem234779] at hxV
    obtain ⟨hV, ⟨b0, b1⟩, b2, ⟨d0, d1, d2⟩⟩ := hxV
    have hv := (vmem234779 m _).1 hV
    have c0 : Fin.init x (Fin.last m) 0 < 4 := hv.1 (Fin.last m) 0
    have c1 : Fin.init x (Fin.last m) 1 < 4 := hv.1 (Fin.last m) 1
    have c2 : Fin.init x (Fin.last m) 0 ≠ Fin.init x (Fin.last m) 1 := hv.2.1 (Fin.last m)
    have hb := (tr234779 _ _ _ _ c0 c1 b0 b1).1 ⟨c2, b2, d0, d1, d2⟩
    rw [hp1, hp2, hq1, hq2] at hb
    rw [hp1] at c0
    rw [hp2] at c1
    rw [hq1] at b0
    rw [hq2] at b1
    exact h ⟨b0, b1, c0, c1, hb⟩

/-- The transfer equations. -/
theorem step234779 (m p' q' : ℕ) :
    (C234779 (m + 1) p' q').card = ∑ p ∈ Finset.range 4, ∑ q ∈ Finset.range 4,
      if p' < 4 ∧ q' < 4 ∧ p < 4 ∧ q < 4 ∧
        (p ≠ q ∧ p' ≠ q' ∧ p ≠ p' ∧ q ≠ q' ∧ ¬ mono234779 p q p' q') then
        (C234779 m p q).card else 0 := by
  have H : ((C234779 (m + 1) p' q' : Finset (Fin (m + 1 + 1) → Fin 2 → ℕ)) :
      Set (Fin (m + 1 + 1) → Fin 2 → ℕ)).MapsTo
      (fun x : Fin (m + 1 + 1) → Fin 2 → ℕ =>
        (Fin.init x (Fin.last m) 0, Fin.init x (Fin.last m) 1))
      ((Finset.range 4 ×ˢ Finset.range 4 : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro x hx
    rw [Finset.mem_coe] at hx
    unfold C234779 at hx
    rw [Finset.mem_filter, vmem234779] at hx
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
    exact ⟨hx.1.1 (Fin.last m).castSucc 0, hx.1.1 (Fin.last m).castSucc 1⟩
  rw [Finset.card_eq_sum_card_fiberwise H, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  exact fib234779 m p' q' p q

theorem asum234779 (m : ℕ) :
    (V234779 m).card = ∑ p ∈ Finset.range 4, ∑ q ∈ Finset.range 4, (C234779 m p q).card := by
  have H : ((V234779 m : Finset (Fin (m + 1) → Fin 2 → ℕ)) : Set (Fin (m + 1) → Fin 2 → ℕ)).MapsTo
      (fun x : Fin (m + 1) → Fin 2 → ℕ => (x (Fin.last m) 0, x (Fin.last m) 1))
      ((Finset.range 4 ×ˢ Finset.range 4 : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro x hx
    rw [Finset.mem_coe, vmem234779] at hx
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
    exact ⟨hx.1 (Fin.last m) 0, hx.1 (Fin.last m) 1⟩
  rw [Finset.card_eq_sum_card_fiberwise H, Finset.sum_product]
  rfl

theorem base234779 (p q : ℕ) :
    (C234779 0 p q).card = ((Finset.range 4 ×ˢ Finset.range 4).filter
      (fun z : ℕ × ℕ => z.1 ≠ z.2 ∧ z = (p, q))).card := by
  apply Finset.card_nbij' (fun x : Fin (0 + 1) → Fin 2 → ℕ => (x 0 0, x 0 1))
    (fun z : ℕ × ℕ => fun _ => fun j => if j = 0 then z.1 else z.2)
  · intro x hx
    simp only [Finset.mem_coe] at hx ⊢
    unfold C234779 at hx
    rw [Finset.mem_filter, vmem234779] at hx
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    obtain ⟨⟨h1, h2, -⟩, h3⟩ := hx
    exact ⟨⟨h1 0 0, h1 0 1⟩, h2 0, h3⟩
  · intro z hz
    simp only [Finset.mem_coe] at hz ⊢
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hz
    obtain ⟨⟨hz1, hz2⟩, hz3, hz4⟩ := hz
    have e0 : (if (0 : Fin 2) = 0 then z.1 else z.2) = z.1 := if_pos rfl
    have e1 : (if (1 : Fin 2) = 0 then z.1 else z.2) = z.2 :=
      if_neg (show ¬ ((1 : Fin 2) = 0) by decide)
    unfold C234779
    rw [Finset.mem_filter, vmem234779]
    refine ⟨⟨fun _ j => ?_, fun _ => ?_, fun i => i.elim0⟩, ?_⟩
    · have hj : ∀ j : Fin 2, (if j = 0 then z.1 else z.2) < 4 :=
        Fin.forall_fin_two.2 ⟨e0.trans_lt hz1, e1.trans_lt hz2⟩
      exact hj j
    · show (if (0 : Fin 2) = 0 then z.1 else z.2) ≠ (if (1 : Fin 2) = 0 then z.1 else z.2)
      rw [e0, e1]
      exact hz3
    · show ((if (0 : Fin 2) = 0 then z.1 else z.2), (if (1 : Fin 2) = 0 then z.1 else z.2)) = (p, q)
      rw [e0, e1]
      exact hz4
  · intro x _
    funext i j
    have hi0 : i = 0 := Fin.fin_one_eq_zero i
    rw [hi0]
    have hj : ∀ j : Fin 2, (if j = 0 then x 0 0 else x 0 1) = x 0 j :=
      Fin.forall_fin_two.2 ⟨if_pos (rfl : (0 : Fin 2) = 0),
        if_neg (show ¬ ((1 : Fin 2) = 0) by decide)⟩
    exact hj j
  · intro z _
    show ((if (0 : Fin 2) = 0 then z.1 else z.2), (if (1 : Fin 2) = 0 then z.1 else z.2)) = z
    have e0 : (if (0 : Fin 2) = 0 then z.1 else z.2) = z.1 := if_pos rfl
    have e1 : (if (1 : Fin 2) = 0 then z.1 else z.2) = z.2 :=
      if_neg (show ¬ ((1 : Fin 2) = 0) by decide)
    exact (congrArg₂ Prod.mk e0 e1).trans Prod.mk.eta

theorem pcard234779 (p q : ℕ) :
    ((Finset.range 4 ×ˢ Finset.range 4).filter (fun z : ℕ × ℕ => z.1 ≠ z.2 ∧ z = (p, q))).card =
      if p < 4 ∧ q < 4 ∧ p ≠ q then 1 else 0 := by
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨(p, q), ?_⟩
    ext z
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range,
      Finset.mem_singleton]
    constructor
    · rintro ⟨-, -, hz⟩
      exact hz
    · rintro rfl
      exact ⟨⟨h.1, h.2.1⟩, h.2.2, rfl⟩
  · rw [Finset.card_eq_zero]
    apply Finset.subset_empty.1
    intro z hz
    exfalso
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hz
    obtain ⟨⟨h1, h2⟩, h3, rfl⟩ := hz
    exact h ⟨h1, h2, h3⟩

theorem t00_234779 (m : ℕ) :
    (C234779 (m + 1) 0 0).card = 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ → ℕ → ℕ, ∀ m p q, c m p q = (C234779 m p q).card :=
    ⟨_, fun _ _ _ => rfl⟩
  have h := step234779 m 0 0
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← hc] at h
  norm_num [mono234779] at h
  simp only [← hc]
  omega

theorem t01_234779 (m : ℕ) :
    (C234779 (m + 1) 0 1).card = (C234779 m 1 0).card + (C234779 m 1 2).card + (C234779 m 1 3).card + (C234779 m 2 0).card + (C234779 m 2 3).card + (C234779 m 3 0).card := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ → ℕ → ℕ, ∀ m p q, c m p q = (C234779 m p q).card :=
    ⟨_, fun _ _ _ => rfl⟩
  have h := step234779 m 0 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← hc] at h
  norm_num [mono234779] at h
  simp only [← hc]
  omega

theorem t02_234779 (m : ℕ) :
    (C234779 (m + 1) 0 2).card = (C234779 m 1 0).card + (C234779 m 1 3).card + (C234779 m 2 0).card + (C234779 m 2 1).card + (C234779 m 2 3).card + (C234779 m 3 0).card + (C234779 m 3 1).card := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ → ℕ → ℕ, ∀ m p q, c m p q = (C234779 m p q).card :=
    ⟨_, fun _ _ _ => rfl⟩
  have h := step234779 m 0 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← hc] at h
  norm_num [mono234779] at h
  simp only [← hc]
  omega

theorem t03_234779 (m : ℕ) :
    (C234779 (m + 1) 0 3).card = (C234779 m 1 0).card + (C234779 m 2 0).card + (C234779 m 2 1).card + (C234779 m 3 0).card + (C234779 m 3 1).card + (C234779 m 3 2).card := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ → ℕ → ℕ, ∀ m p q, c m p q = (C234779 m p q).card :=
    ⟨_, fun _ _ _ => rfl⟩
  have h := step234779 m 0 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← hc] at h
  norm_num [mono234779] at h
  simp only [← hc]
  omega

theorem t10_234779 (m : ℕ) :
    (C234779 (m + 1) 1 0).card = (C234779 m 0 1).card + (C234779 m 0 2).card + (C234779 m 0 3).card + (C234779 m 2 1).card + (C234779 m 3 1).card + (C234779 m 3 2).card := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ → ℕ → ℕ, ∀ m p q, c m p q = (C234779 m p q).card :=
    ⟨_, fun _ _ _ => rfl⟩
  have h := step234779 m 1 0
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← hc] at h
  norm_num [mono234779] at h
  simp only [← hc]
  omega

theorem t11_234779 (m : ℕ) :
    (C234779 (m + 1) 1 1).card = 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ → ℕ → ℕ, ∀ m p q, c m p q = (C234779 m p q).card :=
    ⟨_, fun _ _ _ => rfl⟩
  have h := step234779 m 1 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← hc] at h
  norm_num [mono234779] at h
  simp only [← hc]
  omega

theorem t12_234779 (m : ℕ) :
    (C234779 (m + 1) 1 2).card = (C234779 m 0 1).card + (C234779 m 2 0).card + (C234779 m 2 1).card + (C234779 m 2 3).card + (C234779 m 3 0).card + (C234779 m 3 1).card := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ → ℕ → ℕ, ∀ m p q, c m p q = (C234779 m p q).card :=
    ⟨_, fun _ _ _ => rfl⟩
  have h := step234779 m 1 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← hc] at h
  norm_num [mono234779] at h
  simp only [← hc]
  omega

theorem t13_234779 (m : ℕ) :
    (C234779 (m + 1) 1 3).card = (C234779 m 0 1).card + (C234779 m 0 2).card + (C234779 m 2 0).card + (C234779 m 2 1).card + (C234779 m 3 0).card + (C234779 m 3 1).card + (C234779 m 3 2).card := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ → ℕ → ℕ, ∀ m p q, c m p q = (C234779 m p q).card :=
    ⟨_, fun _ _ _ => rfl⟩
  have h := step234779 m 1 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← hc] at h
  norm_num [mono234779] at h
  simp only [← hc]
  omega

theorem t20_234779 (m : ℕ) :
    (C234779 (m + 1) 2 0).card = (C234779 m 0 1).card + (C234779 m 0 2).card + (C234779 m 0 3).card + (C234779 m 1 2).card + (C234779 m 1 3).card + (C234779 m 3 1).card + (C234779 m 3 2).card := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ → ℕ → ℕ, ∀ m p q, c m p q = (C234779 m p q).card :=
    ⟨_, fun _ _ _ => rfl⟩
  have h := step234779 m 2 0
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← hc] at h
  norm_num [mono234779] at h
  simp only [← hc]
  omega

theorem t21_234779 (m : ℕ) :
    (C234779 (m + 1) 2 1).card = (C234779 m 0 2).card + (C234779 m 0 3).card + (C234779 m 1 0).card + (C234779 m 1 2).card + (C234779 m 1 3).card + (C234779 m 3 2).card := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ → ℕ → ℕ, ∀ m p q, c m p q = (C234779 m p q).card :=
    ⟨_, fun _ _ _ => rfl⟩
  have h := step234779 m 2 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← hc] at h
  norm_num [mono234779] at h
  simp only [← hc]
  omega

theorem t22_234779 (m : ℕ) :
    (C234779 (m + 1) 2 2).card = 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ → ℕ → ℕ, ∀ m p q, c m p q = (C234779 m p q).card :=
    ⟨_, fun _ _ _ => rfl⟩
  have h := step234779 m 2 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← hc] at h
  norm_num [mono234779] at h
  simp only [← hc]
  omega

theorem t23_234779 (m : ℕ) :
    (C234779 (m + 1) 2 3).card = (C234779 m 0 1).card + (C234779 m 0 2).card + (C234779 m 1 2).card + (C234779 m 3 0).card + (C234779 m 3 1).card + (C234779 m 3 2).card := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ → ℕ → ℕ, ∀ m p q, c m p q = (C234779 m p q).card :=
    ⟨_, fun _ _ _ => rfl⟩
  have h := step234779 m 2 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← hc] at h
  norm_num [mono234779] at h
  simp only [← hc]
  omega

theorem t30_234779 (m : ℕ) :
    (C234779 (m + 1) 3 0).card = (C234779 m 0 1).card + (C234779 m 0 2).card + (C234779 m 0 3).card + (C234779 m 1 2).card + (C234779 m 1 3).card + (C234779 m 2 3).card := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ → ℕ → ℕ, ∀ m p q, c m p q = (C234779 m p q).card :=
    ⟨_, fun _ _ _ => rfl⟩
  have h := step234779 m 3 0
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← hc] at h
  norm_num [mono234779] at h
  simp only [← hc]
  omega

theorem t31_234779 (m : ℕ) :
    (C234779 (m + 1) 3 1).card = (C234779 m 0 2).card + (C234779 m 0 3).card + (C234779 m 1 0).card + (C234779 m 1 2).card + (C234779 m 1 3).card + (C234779 m 2 0).card + (C234779 m 2 3).card := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ → ℕ → ℕ, ∀ m p q, c m p q = (C234779 m p q).card :=
    ⟨_, fun _ _ _ => rfl⟩
  have h := step234779 m 3 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← hc] at h
  norm_num [mono234779] at h
  simp only [← hc]
  omega

theorem t32_234779 (m : ℕ) :
    (C234779 (m + 1) 3 2).card = (C234779 m 0 3).card + (C234779 m 1 0).card + (C234779 m 1 3).card + (C234779 m 2 0).card + (C234779 m 2 1).card + (C234779 m 2 3).card := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ → ℕ → ℕ, ∀ m p q, c m p q = (C234779 m p q).card :=
    ⟨_, fun _ _ _ => rfl⟩
  have h := step234779 m 3 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← hc] at h
  norm_num [mono234779] at h
  simp only [← hc]
  omega

theorem t33_234779 (m : ℕ) :
    (C234779 (m + 1) 3 3).card = 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ → ℕ → ℕ, ∀ m p q, c m p q = (C234779 m p q).card :=
    ⟨_, fun _ _ _ => rfl⟩
  have h := step234779 m 3 3
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← hc] at h
  norm_num [mono234779] at h
  simp only [← hc]
  omega

/-- The rows with p - q odd (A), with p - q = 2 or -2 (B), and the diagonal rows (Z). -/
def A234779 (m : ℕ) : ℕ :=
  (C234779 m 0 1).card + (C234779 m 0 3).card + (C234779 m 1 0).card + (C234779 m 1 2).card +
    (C234779 m 2 1).card + (C234779 m 2 3).card + (C234779 m 3 0).card + (C234779 m 3 2).card

def B234779 (m : ℕ) : ℕ :=
  (C234779 m 0 2).card + (C234779 m 1 3).card + (C234779 m 2 0).card + (C234779 m 3 1).card

def Z234779 (m : ℕ) : ℕ :=
  (C234779 m 0 0).card + (C234779 m 1 1).card + (C234779 m 2 2).card + (C234779 m 3 3).card

theorem cls234779 (m : ℕ) : A234779 (m + 1) = 4 * A234779 m + 4 * B234779 m ∧
    B234779 (m + 1) = 2 * A234779 m + 3 * B234779 m ∧ Z234779 (m + 1) = 0 := by
  unfold A234779 B234779 Z234779
  rw [t00_234779, t01_234779, t02_234779, t03_234779, t10_234779, t11_234779, t12_234779,
    t13_234779, t20_234779, t21_234779, t22_234779, t23_234779, t30_234779, t31_234779,
    t32_234779, t33_234779]
  omega

theorem cls0_234779 : A234779 0 = 8 ∧ B234779 0 = 4 ∧ Z234779 0 = 0 := by
  norm_num [A234779, B234779, Z234779, base234779, pcard234779]

theorem aval234779 (m : ℕ) :
    OMA.S_oeis_a234779.a m = A234779 m + B234779 m + Z234779 m := by
  have h := asum234779 m
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  rw [show OMA.S_oeis_a234779.a m = (V234779 m).card from rfl]
  unfold A234779 B234779 Z234779
  omega

open OMA.S_oeis_a234779 in
theorem OMA.solution : type_of% @OMA.S_oeis_a234779.main := by
  have hZ : ∀ m, Z234779 m = 0 := by
    intro m
    cases m with
    | zero => exact cls0_234779.2.2
    | succ k => exact (cls234779 k).2.2
  have hrec : ∀ m, a (m + 2) + 4 * a m = 7 * a (m + 1) := by
    intro m
    rw [aval234779 (m + 2), aval234779 (m + 1), aval234779 m, hZ (m + 2), hZ (m + 1), hZ m]
    obtain ⟨e1, e2, -⟩ : A234779 (m + 2) = 4 * A234779 (m + 1) + 4 * B234779 (m + 1) ∧
        B234779 (m + 2) = 2 * A234779 (m + 1) + 3 * B234779 (m + 1) ∧ Z234779 (m + 2) = 0 :=
      cls234779 (m + 1)
    obtain ⟨f1, f2, -⟩ := cls234779 m
    omega
  have v0 : a 0 = 12 := by
    rw [aval234779 0]
    obtain ⟨e1, e2, e3⟩ := cls0_234779
    omega
  have v1 : a 1 = 76 := by
    rw [aval234779 1]
    obtain ⟨e1, e2, e3⟩ : A234779 1 = 4 * A234779 0 + 4 * B234779 0 ∧
        B234779 1 = 2 * A234779 0 + 3 * B234779 0 ∧ Z234779 1 = 0 := cls234779 0
    obtain ⟨f1, f2, f3⟩ := cls0_234779
    omega
  have v2 : a 2 = 484 := by
    have h := hrec 0
    simp only [Nat.zero_add] at h
    omega
  refine ⟨?_, ?_⟩
  · obtain ⟨f, hf⟩ : ∃ f : ℕ → ℚ, ∀ n, f n = if n = 0 then (0 : ℚ) else (a n : ℚ) :=
      ⟨_, fun _ => rfl⟩
    have hfun : (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = f :=
      funext fun n => (hf n).symm
    have f0 : f 0 = 0 := by rw [hf, if_pos (rfl : (0 : ℕ) = 0)]
    have f1 : f 1 = 76 := by
      rw [hf, if_neg (show ¬ ((1 : ℕ) = 0) by norm_num)]
      exact_mod_cast v1
    have f2 : f 2 = 484 := by
      rw [hf, if_neg (show ¬ ((2 : ℕ) = 0) by norm_num)]
      exact_mod_cast v2
    have frec : ∀ k, f (k + 3) = 7 * f (k + 2) - 4 * f (k + 1) := by
      intro k
      rw [hf, hf, hf, if_neg (show ¬ (k + 3 = 0) by omega), if_neg (show ¬ (k + 2 = 0) by omega),
        if_neg (show ¬ (k + 1 = 0) by omega)]
      have e : (a (k + 3) : ℚ) + 4 * (a (k + 1) : ℚ) = 7 * (a (k + 2) : ℚ) := by
        exact_mod_cast hrec (k + 1)
      linarith
    rw [show PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = PowerSeries.mk f
      from congrArg PowerSeries.mk hfun]
    have e : PowerSeries.mk f * (1 - 7 * PowerSeries.X + 4 * PowerSeries.X ^ 2) =
        PowerSeries.mk f
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 7 * (PowerSeries.mk f * PowerSeries.X ^ 1)
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 * (PowerSeries.mk f * PowerSeries.X ^ 2) := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 7,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4]
      ring
    have e2 : (4 * PowerSeries.X * (19 - 12 * PowerSeries.X) : PowerSeries ℚ) =
        PowerSeries.X ^ 1 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 76
          - PowerSeries.X ^ 2 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 48 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 76,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 48]
      ring
    rw [e, e2]
    ext n
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C]
    rcases Nat.lt_or_ge n 3 with hn | hn
    · interval_cases n
      · norm_num [f0]
      · norm_num [f0, f1]
      · norm_num [f0, f1, f2]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
      rw [if_pos (show 1 ≤ k + 3 by omega), if_pos (show 2 ≤ k + 3 by omega),
        if_pos (show 1 ≤ k + 3 by omega), if_pos (show 2 ≤ k + 3 by omega),
        if_neg (show ¬ (k + 3 - 1 = 0) by omega), if_neg (show ¬ (k + 3 - 2 = 0) by omega),
        show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega, frec k]
      ring
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    obtain ⟨u, hu⟩ : ∃ u : ℕ → ℝ, ∀ j, u j = (7 - Real.sqrt 33) ^ j * (-17 + 3 * Real.sqrt 33) +
        (7 + Real.sqrt 33) ^ j * (17 + 3 * Real.sqrt 33) := ⟨_, fun _ => rfl⟩
    have hs : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
    have hs0 : 0 < Real.sqrt 33 := Real.sqrt_pos.2 (by norm_num)
    have urec : ∀ j, u (j + 2) = 14 * u (j + 1) - 16 * u j := by
      intro j
      rw [hu, hu, hu, pow_add (7 - Real.sqrt 33) j 2, pow_add (7 + Real.sqrt 33) j 2,
        pow_succ (7 - Real.sqrt 33) j, pow_succ (7 + Real.sqrt 33) j]
      linear_combination ((7 - Real.sqrt 33) ^ j * (-17 + 3 * Real.sqrt 33) +
        (7 + Real.sqrt 33) ^ j * (17 + 3 * Real.sqrt 33)) * hs
    have u1 : u 1 = 76 * Real.sqrt 33 := by
      rw [hu]
      ring
    have u2 : u 2 = 968 * Real.sqrt 33 := by
      rw [hu]
      linear_combination (6 * Real.sqrt 33) * hs
    have w1 : (a 1 : ℝ) = 76 := by exact_mod_cast v1
    have w2 : (a 2 : ℝ) = 484 := by exact_mod_cast v2
    have hmain : ∀ j, 2 ^ j * Real.sqrt 33 * (a (j + 1) : ℝ) = u (j + 1) ∧
        2 ^ (j + 1) * Real.sqrt 33 * (a (j + 2) : ℝ) = u (j + 2) := by
      intro j
      induction j with
      | zero =>
        show 2 ^ 0 * Real.sqrt 33 * (a 1 : ℝ) = u 1 ∧ 2 ^ 1 * Real.sqrt 33 * (a 2 : ℝ) = u 2
        rw [u1, u2, w1, w2]
        exact ⟨by ring, by ring⟩
      | succ i ih =>
        show 2 ^ (i + 1) * Real.sqrt 33 * (a (i + 2) : ℝ) = u (i + 2) ∧
          2 ^ (i + 2) * Real.sqrt 33 * (a (i + 3) : ℝ) = u (i + 3)
        have e : (a (i + 3) : ℝ) + 4 * (a (i + 1) : ℝ) = 7 * (a (i + 2) : ℝ) := by
          exact_mod_cast hrec (i + 1)
        have ur : u (i + 3) = 14 * u (i + 2) - 16 * u (i + 1) := urec (i + 1)
        refine ⟨ih.2, ?_⟩
        linear_combination (2 ^ (i + 2) * Real.sqrt 33) * e - 16 * ih.1 + 14 * ih.2 - ur
    have key := (hmain k).1
    have hz2 : (2 : ℝ) ^ (1 - ((k + 1 : ℕ) : ℤ)) = ((2 : ℝ) ^ k)⁻¹ := by
      rw [show (1 - ((k + 1 : ℕ) : ℤ)) = -((k : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
    rw [← hu (k + 1), hz2, eq_div_iff hs0.ne']
    obtain ⟨w, hw⟩ : ∃ w : ℝ, w = ((2 : ℝ) ^ k)⁻¹ := ⟨_, rfl⟩
    have h8 : (2 : ℝ) ^ k * w = 1 := by
      rw [hw]
      exact mul_inv_cancel₀ (by positivity)
    rw [← hw]
    linear_combination w * key - ((a (k + 1) : ℝ) * Real.sqrt 33) * h8
