import OMAStatements.S_oeis_a235877

-- Problem: A235877: Number of (n+1) X (1+1) 0..2 arrays with the minimum plus the upper median equal to the lower median plus the maximum in every 2 X 2 subblock.
-- Upstream: formal-conjectures statements/oeis-a235877.lean:0 (declaration OMA.S_oeis_a235877.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: for entries in 0..2 the block condition s0 + s2 = s1 + s3 holds iff the four entries
-- form two equal pairs (checked by decide on the 81 cases; in general s3 - s0 >= s2 - s1 with
-- equality iff s0 = s1 and s2 = s3). c(m, p, q) counts the arrays with m+1 rows whose last row is
-- (p, q); removing the last row (Fin.init, inverse Fin.snoc) gives c(m+1, y, y) = c(m,0,0) +
-- c(m,1,1) + c(m,2,2) and c(m+1, p, q) = c(m, p, q) + c(m, q, p) for p different from q. So the
-- diagonal part D triples and the rest O doubles: a(m) = D + O = 3 3^m + 6 2^m, and
-- a(m+2) + 6 a(m) = 5 a(m+1); the g.f. follows by comparing coefficients.

/-- The block condition of A235877 for the block with rows (p, q) above (r, s). -/
abbrev bc235877 (p q r s : ℕ) : Prop :=
  OMA.S_oeis_a235877.smin p q r s + OMA.S_oeis_a235877.umed p q r s =
    OMA.S_oeis_a235877.lmed p q r s + OMA.S_oeis_a235877.smax p q r s

theorem blk235877 (p q r s : ℕ) (hp : p < 3) (hq : q < 3) (hr : r < 3) (hs : s < 3) :
    bc235877 p q r s ↔ ((p = q ∧ r = s) ∨ (p = r ∧ q = s) ∨ (p = s ∧ q = r)) := by
  unfold bc235877
  interval_cases p <;> interval_cases q <;> interval_cases r <;> interval_cases s <;> decide

/-- The arrays counted by A235877 (with m+1 rows). -/
def V235877 (m : ℕ) : Finset (Fin (m + 1) → Fin 2 → ℕ) :=
  (Fintype.piFinset fun _ : Fin (m + 1) => Fintype.piFinset fun _ : Fin 2 => Finset.range 3).filter
    (fun x => ∀ i : Fin m,
      OMA.S_oeis_a235877.smin (x i.castSucc 0) (x i.castSucc 1) (x i.succ 0) (x i.succ 1) +
          OMA.S_oeis_a235877.umed (x i.castSucc 0) (x i.castSucc 1) (x i.succ 0) (x i.succ 1) =
        OMA.S_oeis_a235877.lmed (x i.castSucc 0) (x i.castSucc 1) (x i.succ 0) (x i.succ 1) +
          OMA.S_oeis_a235877.smax (x i.castSucc 0) (x i.castSucc 1) (x i.succ 0) (x i.succ 1))

/-- The arrays of V235877 m whose last row is (p, q). -/
def C235877 (m p q : ℕ) : Finset (Fin (m + 1) → Fin 2 → ℕ) :=
  (V235877 m).filter (fun x => (x (Fin.last m) 0, x (Fin.last m) 1) = (p, q))

theorem vmem235877 (m : ℕ) (x : Fin (m + 1) → Fin 2 → ℕ) :
    x ∈ V235877 m ↔ (∀ i j, x i j < 3) ∧
      ∀ i : Fin m, bc235877 (x i.castSucc 0) (x i.castSucc 1) (x i.succ 0) (x i.succ 1) := by
  unfold V235877
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  simp only [Fintype.mem_piFinset, Finset.mem_range]

theorem smem235877 (m : ℕ) (t : Fin (m + 1) → Fin 2 → ℕ) (R : Fin 2 → ℕ) :
    (Fin.snoc t R : Fin (m + 1 + 1) → Fin 2 → ℕ) ∈ V235877 (m + 1) ↔
      t ∈ V235877 m ∧ (R 0 < 3 ∧ R 1 < 3) ∧
        bc235877 (t (Fin.last m) 0) (t (Fin.last m) 1) (R 0) (R 1) := by
  rw [vmem235877, vmem235877]
  constructor
  · rintro ⟨h1, h3⟩
    refine ⟨⟨fun i j => ?_, fun i => ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · have h := h1 i.castSucc j
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
    · have h := h3 (Fin.last m)
      rw [show (Fin.last m).succ = Fin.last (m + 1) from Fin.succ_last m, Fin.snoc_last,
        Fin.snoc_castSucc] at h
      exact h
  · rintro ⟨⟨h1, h3⟩, ⟨h4, h5⟩, h7⟩
    have h8 : ∀ j : Fin 2, R j < 3 := Fin.forall_fin_two.2 ⟨h4, h5⟩
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · rw [Fin.snoc_castSucc]
        exact h1 i' j
      · rw [Fin.snoc_last]
        exact h8 j
    · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact h3 i'
      · rw [show (Fin.last m).succ = Fin.last (m + 1) from Fin.succ_last m, Fin.snoc_last,
          Fin.snoc_castSucc]
        exact h7

/-- One fibre of the last step. -/
theorem fib235877 (m p' q' p q : ℕ) :
    ((C235877 (m + 1) p' q').filter
        (fun x : Fin (m + 1 + 1) → Fin 2 → ℕ =>
          (Fin.init x (Fin.last m) 0, Fin.init x (Fin.last m) 1) = (p, q))).card =
      if p' < 3 ∧ q' < 3 ∧ p < 3 ∧ q < 3 ∧
        ((p = q ∧ p' = q') ∨ (p = p' ∧ q = q') ∨ (p = q' ∧ q = p')) then
        (C235877 m p q).card else 0 := by
  split_ifs with h
  · obtain ⟨h1, h2, h3, h4, h5⟩ := h
    obtain ⟨R, hR0, hR1⟩ : ∃ R : Fin 2 → ℕ, R 0 = p' ∧ R 1 = q' :=
      ⟨fun j => if j = 0 then p' else q', if_pos (rfl : (0 : Fin 2) = 0),
        if_neg (show ¬ ((1 : Fin 2) = 0) by decide)⟩
    have hb : bc235877 p q p' q' := (blk235877 p q p' q' h3 h4 h1 h2).2 h5
    symm
    apply Finset.card_nbij'
      (fun t : Fin (m + 1) → Fin 2 → ℕ => (Fin.snoc t R : Fin (m + 1 + 1) → Fin 2 → ℕ))
      (fun x : Fin (m + 1 + 1) → Fin 2 → ℕ => Fin.init x)
    · intro t ht
      simp only [Finset.mem_coe] at ht ⊢
      unfold C235877 at ht ⊢
      rw [Finset.mem_filter, Prod.mk.injEq] at ht
      obtain ⟨ht1, ht2, ht3⟩ := ht
      rw [Finset.mem_filter, Finset.mem_filter, smem235877, Fin.init_snoc, Fin.snoc_last, hR0,
        hR1, ht2, ht3]
      exact ⟨⟨⟨ht1, ⟨h1, h2⟩, hb⟩, rfl⟩, rfl⟩
    · intro x hx
      simp only [Finset.mem_coe] at hx ⊢
      unfold C235877 at hx ⊢
      simp only [Finset.mem_filter, Prod.mk.injEq] at hx
      obtain ⟨⟨hxV, -, -⟩, hp1, hp2⟩ := hx
      have e : x = (Fin.snoc (Fin.init x) (x (Fin.last (m + 1))) :
          Fin (m + 1 + 1) → Fin 2 → ℕ) := (Fin.snoc_init_self x).symm
      rw [e, smem235877] at hxV
      rw [Finset.mem_filter]
      exact ⟨hxV.1, Prod.mk_inj.2 ⟨hp1, hp2⟩⟩
    · intro t _
      simp only [Fin.init_snoc]
    · intro x hx
      simp only [Finset.mem_coe] at hx
      unfold C235877 at hx
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
    unfold C235877 at hx
    simp only [Finset.mem_filter, Prod.mk.injEq] at hx
    obtain ⟨⟨hxV, hq1, hq2⟩, hp1, hp2⟩ := hx
    have e : x = (Fin.snoc (Fin.init x) (x (Fin.last (m + 1))) :
        Fin (m + 1 + 1) → Fin 2 → ℕ) := (Fin.snoc_init_self x).symm
    rw [e, smem235877] at hxV
    obtain ⟨hV, ⟨b0, b1⟩, hb⟩ := hxV
    have c0 : Fin.init x (Fin.last m) 0 < 3 := ((vmem235877 m _).1 hV).1 (Fin.last m) 0
    have c1 : Fin.init x (Fin.last m) 1 < 3 := ((vmem235877 m _).1 hV).1 (Fin.last m) 1
    have hpair := (blk235877 _ _ _ _ c0 c1 b0 b1).1 hb
    rw [hp1, hp2, hq1, hq2] at hpair
    rw [hp1] at c0
    rw [hp2] at c1
    rw [hq1] at b0
    rw [hq2] at b1
    exact h ⟨b0, b1, c0, c1, hpair⟩

/-- The transfer equations. -/
theorem step235877 (m p' q' : ℕ) :
    (C235877 (m + 1) p' q').card = ∑ p ∈ Finset.range 3, ∑ q ∈ Finset.range 3,
      if p' < 3 ∧ q' < 3 ∧ p < 3 ∧ q < 3 ∧
        ((p = q ∧ p' = q') ∨ (p = p' ∧ q = q') ∨ (p = q' ∧ q = p')) then
        (C235877 m p q).card else 0 := by
  have H : ((C235877 (m + 1) p' q' : Finset (Fin (m + 1 + 1) → Fin 2 → ℕ)) :
      Set (Fin (m + 1 + 1) → Fin 2 → ℕ)).MapsTo
      (fun x : Fin (m + 1 + 1) → Fin 2 → ℕ =>
        (Fin.init x (Fin.last m) 0, Fin.init x (Fin.last m) 1))
      ((Finset.range 3 ×ˢ Finset.range 3 : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro x hx
    rw [Finset.mem_coe] at hx
    unfold C235877 at hx
    rw [Finset.mem_filter, vmem235877] at hx
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
    exact ⟨hx.1.1 (Fin.last m).castSucc 0, hx.1.1 (Fin.last m).castSucc 1⟩
  rw [Finset.card_eq_sum_card_fiberwise H, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  exact fib235877 m p' q' p q

theorem asum235877 (m : ℕ) :
    (V235877 m).card = ∑ p ∈ Finset.range 3, ∑ q ∈ Finset.range 3, (C235877 m p q).card := by
  have H : ((V235877 m : Finset (Fin (m + 1) → Fin 2 → ℕ)) : Set (Fin (m + 1) → Fin 2 → ℕ)).MapsTo
      (fun x : Fin (m + 1) → Fin 2 → ℕ => (x (Fin.last m) 0, x (Fin.last m) 1))
      ((Finset.range 3 ×ˢ Finset.range 3 : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
    intro x hx
    rw [Finset.mem_coe, vmem235877] at hx
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range]
    exact ⟨hx.1 (Fin.last m) 0, hx.1 (Fin.last m) 1⟩
  rw [Finset.card_eq_sum_card_fiberwise H, Finset.sum_product]
  rfl

theorem base235877 (p q : ℕ) :
    (C235877 0 p q).card = ((Finset.range 3 ×ˢ Finset.range 3).filter
      (fun z : ℕ × ℕ => z = (p, q))).card := by
  apply Finset.card_nbij' (fun x : Fin (0 + 1) → Fin 2 → ℕ => (x 0 0, x 0 1))
    (fun z : ℕ × ℕ => fun _ => fun j => if j = 0 then z.1 else z.2)
  · intro x hx
    simp only [Finset.mem_coe] at hx ⊢
    unfold C235877 at hx
    rw [Finset.mem_filter, vmem235877] at hx
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    obtain ⟨⟨h1, -⟩, h3⟩ := hx
    exact ⟨⟨h1 0 0, h1 0 1⟩, h3⟩
  · intro z hz
    simp only [Finset.mem_coe] at hz ⊢
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hz
    obtain ⟨⟨hz1, hz2⟩, hz4⟩ := hz
    have e0 : (if (0 : Fin 2) = 0 then z.1 else z.2) = z.1 := if_pos rfl
    have e1 : (if (1 : Fin 2) = 0 then z.1 else z.2) = z.2 :=
      if_neg (show ¬ ((1 : Fin 2) = 0) by decide)
    unfold C235877
    rw [Finset.mem_filter, vmem235877]
    refine ⟨⟨fun _ j => ?_, fun i => i.elim0⟩, ?_⟩
    · have hj : ∀ j : Fin 2, (if j = 0 then z.1 else z.2) < 3 :=
        Fin.forall_fin_two.2 ⟨e0.trans_lt hz1, e1.trans_lt hz2⟩
      exact hj j
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

theorem pcard235877 (p q : ℕ) :
    ((Finset.range 3 ×ˢ Finset.range 3).filter (fun z : ℕ × ℕ => z = (p, q))).card =
      if p < 3 ∧ q < 3 then 1 else 0 := by
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨(p, q), ?_⟩
    ext z
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range,
      Finset.mem_singleton]
    constructor
    · rintro ⟨-, hz⟩
      exact hz
    · rintro rfl
      exact ⟨⟨h.1, h.2⟩, rfl⟩
  · rw [Finset.card_eq_zero]
    apply Finset.subset_empty.1
    intro z hz
    exfalso
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hz
    obtain ⟨⟨h1, h2⟩, rfl⟩ := hz
    exact h ⟨h1, h2⟩

open OMA.S_oeis_a235877 in
theorem OMA.solution : type_of% @OMA.S_oeis_a235877.main := by
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ → ℕ → ℕ, ∀ m p q, c m p q = (C235877 m p q).card :=
    ⟨_, fun _ _ _ => rfl⟩
  have hr : ∀ m k, k = m + 1 →
      c k 0 0 = c m 0 0 + c m 1 1 + c m 2 2 ∧ c k 0 1 = c m 0 1 + c m 1 0 ∧
      c k 0 2 = c m 0 2 + c m 2 0 ∧ c k 1 0 = c m 0 1 + c m 1 0 ∧
      c k 1 1 = c m 0 0 + c m 1 1 + c m 2 2 ∧ c k 1 2 = c m 1 2 + c m 2 1 ∧
      c k 2 0 = c m 0 2 + c m 2 0 ∧ c k 2 1 = c m 1 2 + c m 2 1 ∧
      c k 2 2 = c m 0 0 + c m 1 1 + c m 2 2 := by
    intro m k hk
    subst hk
    have e00 : c (m + 1) 0 0 = c m 0 0 + c m 1 1 + c m 2 2 := by
      have h := step235877 m 0 0
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← hc] at h
      norm_num at h
      omega
    have e01 : c (m + 1) 0 1 = c m 0 1 + c m 1 0 := by
      have h := step235877 m 0 1
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← hc] at h
      norm_num at h
      omega
    have e02 : c (m + 1) 0 2 = c m 0 2 + c m 2 0 := by
      have h := step235877 m 0 2
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← hc] at h
      norm_num at h
      omega
    have e10 : c (m + 1) 1 0 = c m 0 1 + c m 1 0 := by
      have h := step235877 m 1 0
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← hc] at h
      norm_num at h
      omega
    have e11 : c (m + 1) 1 1 = c m 0 0 + c m 1 1 + c m 2 2 := by
      have h := step235877 m 1 1
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← hc] at h
      norm_num at h
      omega
    have e12 : c (m + 1) 1 2 = c m 1 2 + c m 2 1 := by
      have h := step235877 m 1 2
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← hc] at h
      norm_num at h
      omega
    have e20 : c (m + 1) 2 0 = c m 0 2 + c m 2 0 := by
      have h := step235877 m 2 0
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← hc] at h
      norm_num at h
      omega
    have e21 : c (m + 1) 2 1 = c m 1 2 + c m 2 1 := by
      have h := step235877 m 2 1
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← hc] at h
      norm_num at h
      omega
    have e22 : c (m + 1) 2 2 = c m 0 0 + c m 1 1 + c m 2 2 := by
      have h := step235877 m 2 2
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, ← hc] at h
      norm_num at h
      omega
    exact ⟨e00, e01, e02, e10, e11, e12, e20, e21, e22⟩
  have hz : ∀ p q, c 0 p q = if p < 3 ∧ q < 3 then 1 else 0 :=
    fun p q => ((hc 0 p q).trans (base235877 p q)).trans (pcard235877 p q)
  have z00 : c 0 0 0 = 1 := by norm_num [hz]
  have z01 : c 0 0 1 = 1 := by norm_num [hz]
  have z02 : c 0 0 2 = 1 := by norm_num [hz]
  have z10 : c 0 1 0 = 1 := by norm_num [hz]
  have z11 : c 0 1 1 = 1 := by norm_num [hz]
  have z12 : c 0 1 2 = 1 := by norm_num [hz]
  have z20 : c 0 2 0 = 1 := by norm_num [hz]
  have z21 : c 0 2 1 = 1 := by norm_num [hz]
  have z22 : c 0 2 2 = 1 := by norm_num [hz]
  have ha : ∀ m, a m = c m 0 0 + c m 0 1 + c m 0 2 + c m 1 0 + c m 1 1 + c m 1 2 +
      c m 2 0 + c m 2 1 + c m 2 2 := by
    intro m
    have h := asum235877 m
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, ← hc] at h
    rw [show a m = (V235877 m).card from rfl]
    omega
  have hdo : ∀ m, c m 0 0 + c m 1 1 + c m 2 2 = 3 * 3 ^ m ∧
      c m 0 1 + c m 0 2 + c m 1 0 + c m 1 2 + c m 2 0 + c m 2 1 = 6 * 2 ^ m := by
    intro m
    induction m with
    | zero =>
      rw [pow_zero, pow_zero]
      omega
    | succ k ih =>
      obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := hr k (k + 1) rfl
      rw [pow_succ, pow_succ]
      omega
  have hrec : ∀ m, a (m + 2) + 6 * a m = 5 * a (m + 1) := by
    intro m
    rw [ha (m + 2), ha (m + 1), ha m]
    obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩ := hr m (m + 1) rfl
    obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8⟩ := hr (m + 1) (m + 2) rfl
    omega
  have hcf : ∀ n, a n = 3 * 3 ^ n + 6 * 2 ^ n := by
    intro n
    rw [ha n]
    obtain ⟨d1, d2⟩ := hdo n
    omega
  have v1 : a 1 = 21 := by
    have h := hcf 1
    norm_num at h
    exact h
  have v2 : a 2 = 51 := by
    have h := hcf 2
    norm_num at h
    exact h
  refine ⟨?_, ?_⟩
  · obtain ⟨f, hf⟩ : ∃ f : ℕ → ℚ, ∀ n, f n = if n = 0 then (0 : ℚ) else (a n : ℚ) :=
      ⟨_, fun _ => rfl⟩
    have hfun : (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = f :=
      funext fun n => (hf n).symm
    have f0 : f 0 = 0 := by rw [hf, if_pos (rfl : (0 : ℕ) = 0)]
    have f1 : f 1 = 21 := by
      rw [hf, if_neg (show ¬ ((1 : ℕ) = 0) by norm_num)]
      exact_mod_cast v1
    have f2 : f 2 = 51 := by
      rw [hf, if_neg (show ¬ ((2 : ℕ) = 0) by norm_num)]
      exact_mod_cast v2
    have frec : ∀ k, f (k + 3) = 5 * f (k + 2) - 6 * f (k + 1) := by
      intro k
      rw [hf, hf, hf, if_neg (show ¬ (k + 3 = 0) by omega), if_neg (show ¬ (k + 2 = 0) by omega),
        if_neg (show ¬ (k + 1 = 0) by omega)]
      have e : (a (k + 3) : ℚ) + 6 * (a (k + 1) : ℚ) = 5 * (a (k + 2) : ℚ) := by
        exact_mod_cast hrec (k + 1)
      linarith
    rw [show PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = PowerSeries.mk f
      from congrArg PowerSeries.mk hfun]
    have e : PowerSeries.mk f * ((1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X)) =
        PowerSeries.mk f
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5 * (PowerSeries.mk f * PowerSeries.X ^ 1)
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6 * (PowerSeries.mk f * PowerSeries.X ^ 2) := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 5,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6]
      ring
    have e2 : (3 * PowerSeries.X * (7 - 18 * PowerSeries.X) : PowerSeries ℚ) =
        PowerSeries.X ^ 1 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 21
          - PowerSeries.X ^ 2 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 54 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 21,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 54]
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
  · intro n _
    rw [hcf n, pow_add, pow_one]
    ring
