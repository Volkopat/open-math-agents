import OMAStatements.S_oeis_a233099

-- Problem: A233099: Number of 2 X n 0..3 arrays with no element x(i,j) adjacent to value 3-x(i,j) horizontally or antidiagonally, top left element zero, and 1 appearing before 2 in row major order.
-- Upstream: formal-conjectures statements/oeis-a233099.lean:0 (declaration OMA.S_oeis_a233099.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: swapping the values 1 and 2 keeps the clash and top-left conditions, and exactly
-- one of x and its swap has 1 before 2 unless x uses neither 1 nor 2 (then both are x). So
-- 2 a(n) = T(n) + Z(n), where T counts the arrays without the order condition and Z those with
-- values in {0, 3} only. Both are counted by a transfer over the columns, split by whether the
-- last column has equal entries: for T, e' = 3e + 2f and f' = 6e + 2f with e = 1, f = 3 at one
-- column, so 7e = 10*6^m - 3(-1)^m and 7f = 15*6^m + 6(-1)^m at m+1 columns; for Z, e' = e and
-- f' = 0 with e = f = 1 at one column. Hence 14 a(k+2) = 25*6^(k+1) + 3(-1)^(k+1) + 7, a(1) = 3,
-- which gives both closed forms, and the g.f. follows by comparing coefficients. The weights of the transfer are checked by decide over the 16 column values.

open OMA.S_oeis_a233099

/-- The swap of the values 1 and 2. -/
def sw99 (v : Fin 4) : Fin 4 := if v = 1 then 2 else if v = 2 then 1 else v

theorem sw99_facts : (∀ v : Fin 4, sw99 (sw99 v) = v) ∧
    (∀ u v : Fin 4, ((sw99 u).val + (sw99 v).val = 3 ↔ u.val + v.val = 3)) ∧
    (∀ v : Fin 4, (sw99 v = 0 ↔ v = 0)) ∧ (∀ v : Fin 4, (sw99 v = 1 ↔ v = 2)) ∧
    (∀ v : Fin 4, (sw99 v = 2 ↔ v = 1)) ∧ (∀ v : Fin 4, v ≠ 1 → v ≠ 2 → sw99 v = v) := by
  decide

/-- The array with the values 1 and 2 swapped. -/
def swA99 (n : ℕ) (x : Fin n → Fin 2 → Fin 4) : Fin n → Fin 2 → Fin 4 := fun j i => sw99 (x j i)

theorem swA99_swA99 (n : ℕ) (x : Fin n → Fin 2 → Fin 4) : swA99 n (swA99 n x) = x := by
  funext j i
  exact sw99_facts.1 (x j i)

theorem sw99_ne (u v : Fin 4) : (sw99 u).val + (sw99 v).val ≠ 3 ↔ u.val + v.val ≠ 3 :=
  not_congr (sw99_facts.2.1 u v)

theorem noClash_swA99 (n : ℕ) (x : Fin n → Fin 2 → Fin 4) :
    noClash n (swA99 n x) ↔ noClash n x := by
  constructor
  · intro h j k hk
    obtain ⟨h1, h2, h3⟩ := h j k hk
    exact ⟨fun i => (sw99_ne (x j i) (x k i)).1 (h1 i), (sw99_ne (x j 0) (x k 1)).1 h2,
      (sw99_ne (x k 0) (x j 1)).1 h3⟩
  · intro h j k hk
    obtain ⟨h1, h2, h3⟩ := h j k hk
    exact ⟨fun i => (sw99_ne (x j i) (x k i)).2 (h1 i), (sw99_ne (x j 0) (x k 1)).2 h2,
      (sw99_ne (x k 0) (x j 1)).2 h3⟩

theorem topLeftZero_swA99 (n : ℕ) (x : Fin n → Fin 2 → Fin 4) :
    topLeftZero n (swA99 n x) ↔ topLeftZero n x := by
  constructor
  · intro h j hj
    exact (sw99_facts.2.2.1 (x j 0)).1 (h j hj)
  · intro h j hj
    exact (sw99_facts.2.2.1 (x j 0)).2 (h j hj)

theorem bef99_lt (n : ℕ) (i i' : Fin 2) (j j' : Fin n)
    (h : i'.val < i.val ∨ (i'.val = i.val ∧ j'.val < j.val)) :
    i'.val * n + j'.val < i.val * n + j.val := by
  have hi : i.val < 2 := i.isLt
  have hj' : j'.val < n := j'.isLt
  rcases h with h | ⟨h1, h2⟩
  · have e1 : i'.val = 0 := by omega
    have e2 : i.val = 1 := by omega
    rw [e1, e2, Nat.zero_mul, Nat.one_mul, Nat.zero_add]
    exact Nat.lt_of_lt_of_le hj' (Nat.le_add_right n _)
  · rw [h1]
    exact Nat.add_lt_add_left h2 _

theorem obt99_or (n : ℕ) (x : Fin n → Fin 2 → Fin 4) :
    oneBeforeTwo n x ∨ oneBeforeTwo n (swA99 n x) := by
  by_contra hc
  have h1 : ¬ oneBeforeTwo n x := fun h => hc (Or.inl h)
  have h2 : ¬ oneBeforeTwo n (swA99 n x) := fun h => hc (Or.inr h)
  have e1 : ∃ j : Fin n, ∃ i : Fin 2, x j i = 2 ∧ ∀ j' : Fin n, ∀ i' : Fin 2,
      (i'.val < i.val ∨ (i'.val = i.val ∧ j'.val < j.val)) → x j' i' ≠ 1 := by
    by_contra hh
    apply h1
    intro j i hx
    by_contra hne
    exact hh ⟨j, i, hx, fun j' i' hb hx' => hne ⟨j', i', hb, hx'⟩⟩
  have e2 : ∃ j : Fin n, ∃ i : Fin 2, x j i = 1 ∧ ∀ j' : Fin n, ∀ i' : Fin 2,
      (i'.val < i.val ∨ (i'.val = i.val ∧ j'.val < j.val)) → x j' i' ≠ 2 := by
    by_contra hh
    apply h2
    intro j i hx
    by_contra hne
    refine hh ⟨j, i, (sw99_facts.2.2.2.2.1 (x j i)).1 hx, fun j' i' hb hx' => hne ⟨j', i', hb, ?_⟩⟩
    exact (sw99_facts.2.2.2.1 (x j' i')).2 hx'
  obtain ⟨j, i, hx, hb⟩ := e1
  obtain ⟨j2, i2, hx2, hb2⟩ := e2
  rcases lt_trichotomy i.val i2.val with hlt | heq | hgt
  · exact hb2 j i (Or.inl hlt) hx
  · rcases lt_trichotomy j.val j2.val with hlt' | heq' | hgt'
    · exact hb2 j i (Or.inr ⟨heq, hlt'⟩) hx
    · have ei : i = i2 := Fin.ext heq
      have ej : j = j2 := Fin.ext heq'
      subst ei ej
      rw [hx] at hx2
      exact absurd hx2 (by decide)
    · exact hb j2 i2 (Or.inr ⟨heq.symm, hgt'⟩) hx2
  · exact hb j2 i2 (Or.inl hgt) hx2

theorem obt99_both (n : ℕ) (x : Fin n → Fin 2 → Fin 4) (h1 : oneBeforeTwo n x)
    (h2 : oneBeforeTwo n (swA99 n x)) : ∀ j : Fin n, ∀ i : Fin 2, x j i ≠ 1 ∧ x j i ≠ 2 := by
  have key : ∀ m : ℕ, ∀ j : Fin n, ∀ i : Fin 2, i.val * n + j.val < m →
      x j i ≠ 1 ∧ x j i ≠ 2 := by
    intro m
    induction m with
    | zero =>
      intro j i h
      exact absurd h (Nat.not_lt_zero _)
    | succ m ih =>
      intro j i hm
      constructor
      · intro hx
        obtain ⟨j', i', hb, hx'⟩ := h2 j i ((sw99_facts.2.2.2.2.1 (x j i)).2 hx)
        have hlt := bef99_lt n i i' j j' hb
        exact (ih j' i' (Nat.lt_of_lt_of_le hlt (Nat.le_of_lt_succ hm))).2
          ((sw99_facts.2.2.2.1 (x j' i')).1 hx')
      · intro hx
        obtain ⟨j', i', hb, hx'⟩ := h1 j i hx
        have hlt := bef99_lt n i i' j j' hb
        exact (ih j' i' (Nat.lt_of_lt_of_le hlt (Nat.le_of_lt_succ hm))).1 hx'
  intro j i
  exact key _ j i (Nat.lt_succ_self _)

/-- The arrays without the order condition. -/
def ST99 (n : ℕ) : Finset (Fin n → Fin 2 → Fin 4) :=
  Finset.univ.filter (fun x => noClash n x ∧ topLeftZero n x)

/-- Those of them with values in {0, 3} only. -/
def SZ99 (n : ℕ) : Finset (Fin n → Fin 2 → Fin 4) :=
  Finset.univ.filter (fun x => (noClash n x ∧ topLeftZero n x) ∧
    ∀ j : Fin n, ∀ i : Fin 2, x j i ≠ 1 ∧ x j i ≠ 2)

/-- The arrays counted by A233099. -/
def SA99 (n : ℕ) : Finset (Fin n → Fin 2 → Fin 4) :=
  Finset.univ.filter (fun x => noClash n x ∧ topLeftZero n x ∧ oneBeforeTwo n x)

theorem twice99 (n : ℕ) : 2 * a n = (ST99 n).card + (SZ99 n).card := by
  have hA : a n = (SA99 n).card := rfl
  have hinj : Function.Injective (swA99 n) := by
    intro x y hxy
    rw [← swA99_swA99 n x, hxy, swA99_swA99 n y]
  have hI : ((SA99 n).image (swA99 n)).card = (SA99 n).card :=
    Finset.card_image_of_injective _ hinj
  have memA : ∀ y, y ∈ SA99 n ↔ noClash n y ∧ topLeftZero n y ∧ oneBeforeTwo n y := by
    intro y
    unfold SA99
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have memI : ∀ y, y ∈ (SA99 n).image (swA99 n) ↔ swA99 n y ∈ SA99 n := by
    intro y
    rw [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [swA99_swA99]
      exact hx
    · intro h
      exact ⟨swA99 n y, h, swA99_swA99 n y⟩
  have hU : SA99 n ∪ (SA99 n).image (swA99 n) = ST99 n := by
    ext y
    rw [Finset.mem_union, memI, memA, memA, noClash_swA99, topLeftZero_swA99]
    unfold ST99
    rw [Finset.mem_filter]
    constructor
    · rintro (⟨h1, h2, -⟩ | ⟨h1, h2, -⟩)
      · exact ⟨Finset.mem_univ _, h1, h2⟩
      · exact ⟨Finset.mem_univ _, h1, h2⟩
    · rintro ⟨-, h1, h2⟩
      rcases obt99_or n y with h | h
      · exact Or.inl ⟨h1, h2, h⟩
      · exact Or.inr ⟨h1, h2, h⟩
  have hN : SA99 n ∩ (SA99 n).image (swA99 n) = SZ99 n := by
    ext y
    rw [Finset.mem_inter, memI, memA, memA, noClash_swA99, topLeftZero_swA99]
    unfold SZ99
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, -, -, h4⟩
      exact ⟨Finset.mem_univ _, ⟨h1, h2⟩, obt99_both n y h3 h4⟩
    · rintro ⟨-, ⟨h1, h2⟩, h3⟩
      have hb : oneBeforeTwo n y := fun j i hx => absurd hx (h3 j i).2
      have hs : swA99 n y = y := by
        funext j i
        exact sw99_facts.2.2.2.2.2 (y j i) (h3 j i).1 (h3 j i).2
      refine ⟨⟨h1, h2, hb⟩, h1, h2, ?_⟩
      rw [hs]
      exact hb
  have hc := Finset.card_union_add_card_inter (SA99 n) ((SA99 n).image (swA99 n))
  rw [hU, hN, hI] at hc
  omega

/-- Arrays of m+1 columns (each column a pair: top, bottom) whose first column satisfies F,
whose columns all satisfy K, and whose consecutive columns satisfy R. -/
def W99 (R : Fin 4 × Fin 4 → Fin 4 × Fin 4 → Bool) (F K : Fin 4 × Fin 4 → Bool) (m : ℕ) :
    Finset (Fin (m + 1) → Fin 4 × Fin 4) :=
  Finset.univ.filter (fun y => F (y ⟨0, Nat.succ_pos m⟩) = true ∧ (∀ j, K (y j) = true) ∧
    ∀ j : Fin m, R (y j.castSucc) (y j.succ) = true)

theorem memW99 (R : Fin 4 × Fin 4 → Fin 4 × Fin 4 → Bool) (F K : Fin 4 × Fin 4 → Bool) (m : ℕ)
    (y : Fin (m + 1) → Fin 4 × Fin 4) :
    y ∈ W99 R F K m ↔ F (y ⟨0, Nat.succ_pos m⟩) = true ∧ (∀ j, K (y j) = true) ∧
      ∀ j : Fin m, R (y j.castSucc) (y j.succ) = true := by
  unfold W99
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem memW99_snoc (R : Fin 4 × Fin 4 → Fin 4 × Fin 4 → Bool) (F K : Fin 4 × Fin 4 → Bool)
    (m : ℕ) (t : Fin (m + 1) → Fin 4 × Fin 4) (c : Fin 4 × Fin 4) :
    (Fin.snoc t c : Fin (m + 1 + 1) → Fin 4 × Fin 4) ∈ W99 R F K (m + 1) ↔
      t ∈ W99 R F K m ∧ K c = true ∧ R (t (Fin.last m)) c = true := by
  rw [memW99, memW99]
  have e : (⟨0, Nat.succ_pos (m + 1)⟩ : Fin (m + 1 + 1)) =
      Fin.castSucc (⟨0, Nat.succ_pos m⟩ : Fin (m + 1)) := Fin.ext rfl
  rw [e, Fin.snoc_castSucc]
  constructor
  · rintro ⟨hF, hK, hR⟩
    refine ⟨⟨hF, fun j => ?_, fun j => ?_⟩, ?_, ?_⟩
    · have h := hK j.castSucc
      rw [Fin.snoc_castSucc] at h
      exact h
    · have h := hR j.castSucc
      rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc] at h
      exact h
    · have h := hK (Fin.last (m + 1))
      rw [Fin.snoc_last] at h
      exact h
    · have h := hR (Fin.last m)
      rw [show (Fin.last m).succ = Fin.last (m + 1) from Fin.succ_last m, Fin.snoc_last,
        Fin.snoc_castSucc] at h
      exact h
  · rintro ⟨⟨hF, hK, hR⟩, hc, hl⟩
    refine ⟨hF, fun j => ?_, fun j => ?_⟩
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · rw [Fin.snoc_castSucc]
        exact hK j'
      · rw [Fin.snoc_last]
        exact hc
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact hR j'
      · rw [show (Fin.last m).succ = Fin.last (m + 1) from Fin.succ_last m, Fin.snoc_last,
          Fin.snoc_castSucc]
        exact hl

/-- One transfer step: remove the last column. -/
theorem stepW99 (R : Fin 4 × Fin 4 → Fin 4 × Fin 4 → Bool) (F K P : Fin 4 × Fin 4 → Bool)
    (m : ℕ) :
    ((W99 R F K (m + 1)).filter (fun y => P (y (Fin.last (m + 1))) = true)).card =
      ∑ t ∈ W99 R F K m, (Finset.univ.filter (fun c : Fin 4 × Fin 4 =>
        K c = true ∧ R (t (Fin.last m)) c = true ∧ P c = true)).card := by
  have H : (((W99 R F K (m + 1)).filter (fun y => P (y (Fin.last (m + 1))) = true) :
      Finset (Fin (m + 1 + 1) → Fin 4 × Fin 4)) : Set (Fin (m + 1 + 1) → Fin 4 × Fin 4)).MapsTo
      (fun y : Fin (m + 1 + 1) → Fin 4 × Fin 4 => Fin.init y)
      ((W99 R F K m : Finset (Fin (m + 1) → Fin 4 × Fin 4)) :
        Set (Fin (m + 1) → Fin 4 × Fin 4)) := by
    intro y hy
    have hy1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).1
    have e : y = (Fin.snoc (Fin.init y) (y (Fin.last (m + 1))) :
        Fin (m + 1 + 1) → Fin 4 × Fin 4) := (Fin.snoc_init_self y).symm
    rw [e, memW99_snoc] at hy1
    exact Finset.mem_coe.2 hy1.1
  rw [Finset.card_eq_sum_card_fiberwise H]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.card_nbij' (fun y : Fin (m + 1 + 1) → Fin 4 × Fin 4 => y (Fin.last (m + 1)))
    (fun c : Fin 4 × Fin 4 => (Fin.snoc t c : Fin (m + 1 + 1) → Fin 4 × Fin 4))
  · intro y hy
    have hy' := Finset.mem_filter.1 (Finset.mem_coe.1 hy)
    have hyW := (Finset.mem_filter.1 hy'.1).1
    have hP := (Finset.mem_filter.1 hy'.1).2
    have hyt : Fin.init y = t := hy'.2
    have e : y = (Fin.snoc (Fin.init y) (y (Fin.last (m + 1))) :
        Fin (m + 1 + 1) → Fin 4 × Fin 4) := (Fin.snoc_init_self y).symm
    rw [e, memW99_snoc] at hyW
    obtain ⟨-, hK, hR⟩ := hyW
    rw [hyt] at hR
    exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hK, hR, hP⟩)
  · intro c hc
    obtain ⟨hK, hR, hP⟩ := (Finset.mem_filter.1 (Finset.mem_coe.1 hc)).2
    have hW := (memW99_snoc R F K m t c).2 ⟨ht, hK, hR⟩
    have hP' : P ((Fin.snoc t c : Fin (m + 1 + 1) → Fin 4 × Fin 4) (Fin.last (m + 1))) = true := by
      rw [Fin.snoc_last]
      exact hP
    exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hW, hP'⟩, Fin.init_snoc _ _⟩)
  · intro y hy
    have hyt : Fin.init y = t := (Finset.mem_filter.1 (Finset.mem_coe.1 hy)).2
    show (Fin.snoc t (y (Fin.last (m + 1))) : Fin (m + 1 + 1) → Fin 4 × Fin 4) = y
    rw [← hyt]
    exact Fin.snoc_init_self y
  · intro c _
    show (Fin.snoc t c : Fin (m + 1 + 1) → Fin 4 × Fin 4) (Fin.last (m + 1)) = c
    rw [Fin.snoc_last]

/-- The arrays with one column. -/
theorem baseW99 (R : Fin 4 × Fin 4 → Fin 4 × Fin 4 → Bool) (F K P : Fin 4 × Fin 4 → Bool) :
    ((W99 R F K 0).filter (fun y => P (y (Fin.last 0)) = true)).card =
      (Finset.univ.filter (fun c : Fin 4 × Fin 4 => F c = true ∧ K c = true ∧ P c = true)).card := by
  apply Finset.card_nbij' (fun y : Fin (0 + 1) → Fin 4 × Fin 4 => y (Fin.last 0))
    (fun c : Fin 4 × Fin 4 => fun _ : Fin (0 + 1) => c)
  · intro y hy
    have hy' := Finset.mem_filter.1 (Finset.mem_coe.1 hy)
    obtain ⟨hF, hK, -⟩ := (memW99 R F K 0 y).1 hy'.1
    exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hF, hK _, hy'.2⟩)
  · intro c hc
    obtain ⟨hF, hK, hP⟩ := (Finset.mem_filter.1 (Finset.mem_coe.1 hc)).2
    exact Finset.mem_coe.2 (Finset.mem_filter.2
      ⟨(memW99 R F K 0 _).2 ⟨hF, fun _ => hK, fun j => j.elim0⟩, hP⟩)
  · intro y _
    funext j
    show y (Fin.last 0) = y j
    have hj : j = Fin.last 0 := Fin.ext (by have := j.isLt; rw [Fin.val_last]; omega)
    rw [hj]
  · intro c _
    rfl

/-- The transfer step when the weights depend only on whether Q holds at the last column. -/
theorem classStep99 (R : Fin 4 × Fin 4 → Fin 4 × Fin 4 → Bool) (F K P Q : Fin 4 × Fin 4 → Bool)
    (wa wb m : ℕ)
    (hw : ∀ d : Fin 4 × Fin 4, K d = true →
      (Finset.univ.filter (fun c : Fin 4 × Fin 4 => K c = true ∧ R d c = true ∧ P c = true)).card =
        if Q d = true then wa else wb) :
    ((W99 R F K (m + 1)).filter (fun y => P (y (Fin.last (m + 1))) = true)).card =
      ((W99 R F K m).filter (fun y => Q (y (Fin.last m)) = true)).card * wa +
        ((W99 R F K m).filter (fun y => ¬ (Q (y (Fin.last m)) = true))).card * wb := by
  rw [stepW99]
  have e : ∀ t ∈ W99 R F K m,
      (Finset.univ.filter (fun c : Fin 4 × Fin 4 =>
        K c = true ∧ R (t (Fin.last m)) c = true ∧ P c = true)).card =
        if Q (t (Fin.last m)) = true then wa else wb :=
    fun t ht => hw (t (Fin.last m)) (((memW99 R F K m t).1 ht).2.1 (Fin.last m))
  rw [Finset.sum_congr rfl e, Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul,
    smul_eq_mul]

/-- The columns of an array, as pairs (top, bottom). -/
def toP99 (n : ℕ) (x : Fin n → Fin 2 → Fin 4) : Fin n → Fin 4 × Fin 4 := fun j => (x j 0, x j 1)

theorem card_toP99 (n : ℕ) (S : Finset (Fin n → Fin 4 × Fin 4)) :
    (Finset.univ.filter (fun x : Fin n → Fin 2 → Fin 4 => toP99 n x ∈ S)).card = S.card := by
  apply Finset.card_nbij' (toP99 n)
    (fun y : Fin n → Fin 4 × Fin 4 => fun j i => if i = 0 then (y j).1 else (y j).2)
  · intro x hx
    exact Finset.mem_coe.2 (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
  · intro y hy
    have e : toP99 n (fun j i => if i = 0 then (y j).1 else (y j).2) = y := by
      funext j
      show ((if (0 : Fin 2) = 0 then (y j).1 else (y j).2),
        (if (1 : Fin 2) = 0 then (y j).1 else (y j).2)) = y j
      have e0 : (if (0 : Fin 2) = 0 then (y j).1 else (y j).2) = (y j).1 := if_pos rfl
      have e1 : (if (1 : Fin 2) = 0 then (y j).1 else (y j).2) = (y j).2 :=
        if_neg (show ¬ ((1 : Fin 2) = 0) by decide)
      exact (congrArg₂ Prod.mk e0 e1).trans Prod.mk.eta
    refine Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩)
    show toP99 n (fun j i => if i = 0 then (y j).1 else (y j).2) ∈ S
    rw [e]
    exact Finset.mem_coe.1 hy
  · intro x _
    funext j i
    show (if i = 0 then x j 0 else x j 1) = x j i
    have hj : ∀ i : Fin 2, (if i = 0 then x j 0 else x j 1) = x j i :=
      Fin.forall_fin_two.2 ⟨if_pos rfl, if_neg (show ¬ ((1 : Fin 2) = 0) by decide)⟩
    exact hj i
  · intro y _
    funext j
    show ((if (0 : Fin 2) = 0 then (y j).1 else (y j).2),
      (if (1 : Fin 2) = 0 then (y j).1 else (y j).2)) = y j
    have e0 : (if (0 : Fin 2) = 0 then (y j).1 else (y j).2) = (y j).1 := if_pos rfl
    have e1 : (if (1 : Fin 2) = 0 then (y j).1 else (y j).2) = (y j).2 :=
      if_neg (show ¬ ((1 : Fin 2) = 0) by decide)
    exact (congrArg₂ Prod.mk e0 e1).trans Prod.mk.eta

/-- The clash relation between consecutive columns d, c (as pairs). -/
def R99 (d c : Fin 4 × Fin 4) : Bool :=
  decide (d.1.val + c.1.val ≠ 3 ∧ d.2.val + c.2.val ≠ 3 ∧ d.1.val + c.2.val ≠ 3 ∧
    c.1.val + d.2.val ≠ 3)

/-- The first column has top element zero. -/
def F99 (c : Fin 4 × Fin 4) : Bool := decide (c.1 = 0)

/-- No condition on the columns. -/
def KT99 (_c : Fin 4 × Fin 4) : Bool := true

/-- The column has no entry 1 or 2. -/
def KZ99 (c : Fin 4 × Fin 4) : Bool := decide (c.1 ≠ 1 ∧ c.1 ≠ 2 ∧ c.2 ≠ 1 ∧ c.2 ≠ 2)

/-- The column has equal entries. -/
def QE99 (c : Fin 4 × Fin 4) : Bool := decide (c.1 = c.2)

/-- The column has different entries. -/
def QN99 (c : Fin 4 × Fin 4) : Bool := decide (c.1 ≠ c.2)

theorem nc_iff99 (m : ℕ) (x : Fin (m + 1) → Fin 2 → Fin 4) :
    noClash (m + 1) x ↔
      ∀ j : Fin m, R99 (toP99 (m + 1) x j.castSucc) (toP99 (m + 1) x j.succ) = true := by
  constructor
  · intro h j
    obtain ⟨h1, h2, h3⟩ := h j.castSucc j.succ rfl
    unfold R99
    exact decide_eq_true ⟨h1 0, h1 1, h2, h3⟩
  · intro h j k hk
    have hj : j.val < m := by
      have := k.isLt
      omega
    have e1 : (⟨j.val, hj⟩ : Fin m).castSucc = j := Fin.ext rfl
    have e2 : (⟨j.val, hj⟩ : Fin m).succ = k := Fin.ext (by rw [Fin.val_succ]; exact hk.symm)
    have h' := of_decide_eq_true (h ⟨j.val, hj⟩)
    rw [e1, e2] at h'
    obtain ⟨h1, h2, h3, h4⟩ := h'
    exact ⟨Fin.forall_fin_two.2 ⟨h1, h2⟩, h3, h4⟩

theorem tl_iff99 (m : ℕ) (x : Fin (m + 1) → Fin 2 → Fin 4) :
    topLeftZero (m + 1) x ↔ F99 (toP99 (m + 1) x ⟨0, Nat.succ_pos m⟩) = true := by
  constructor
  · intro h
    unfold F99
    exact decide_eq_true (h ⟨0, Nat.succ_pos m⟩ rfl)
  · intro h j hj
    have e : j = ⟨0, Nat.succ_pos m⟩ := Fin.ext hj
    rw [e]
    exact of_decide_eq_true h

theorem kz_iff99 (m : ℕ) (x : Fin (m + 1) → Fin 2 → Fin 4) :
    (∀ j : Fin (m + 1), ∀ i : Fin 2, x j i ≠ 1 ∧ x j i ≠ 2) ↔
      ∀ j, KZ99 (toP99 (m + 1) x j) = true := by
  constructor
  · intro h j
    unfold KZ99
    exact decide_eq_true ⟨(h j 0).1, (h j 0).2, (h j 1).1, (h j 1).2⟩
  · intro h j
    obtain ⟨h1, h2, h3, h4⟩ := of_decide_eq_true (h j)
    exact Fin.forall_fin_two.2 ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩

theorem bridgeT99 (m : ℕ) (x : Fin (m + 1) → Fin 2 → Fin 4) :
    (noClash (m + 1) x ∧ topLeftZero (m + 1) x) ↔ toP99 (m + 1) x ∈ W99 R99 F99 KT99 m := by
  rw [memW99, nc_iff99, tl_iff99]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2, fun _ => rfl, h1⟩
  · rintro ⟨h2, -, h1⟩
    exact ⟨h1, h2⟩

theorem bridgeZ99 (m : ℕ) (x : Fin (m + 1) → Fin 2 → Fin 4) :
    ((noClash (m + 1) x ∧ topLeftZero (m + 1) x) ∧
      ∀ j : Fin (m + 1), ∀ i : Fin 2, x j i ≠ 1 ∧ x j i ≠ 2) ↔
      toP99 (m + 1) x ∈ W99 R99 F99 KZ99 m := by
  rw [memW99, nc_iff99, tl_iff99, kz_iff99]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h2, h3, h1⟩
  · rintro ⟨h2, h3, h1⟩
    exact ⟨⟨h1, h2⟩, h3⟩

theorem cardST99 (m : ℕ) : (ST99 (m + 1)).card = (W99 R99 F99 KT99 m).card := by
  have e : ST99 (m + 1) = Finset.univ.filter
      (fun x : Fin (m + 1) → Fin 2 → Fin 4 => toP99 (m + 1) x ∈ W99 R99 F99 KT99 m) := by
    unfold ST99
    exact Finset.filter_congr (fun x _ => bridgeT99 m x)
  rw [e, card_toP99]

theorem cardSZ99 (m : ℕ) : (SZ99 (m + 1)).card = (W99 R99 F99 KZ99 m).card := by
  have e : SZ99 (m + 1) = Finset.univ.filter
      (fun x : Fin (m + 1) → Fin 2 → Fin 4 => toP99 (m + 1) x ∈ W99 R99 F99 KZ99 m) := by
    unfold SZ99
    exact Finset.filter_congr (fun x _ => bridgeZ99 m x)
  rw [e, card_toP99]

theorem wTe99 : ∀ d : Fin 4 × Fin 4, KT99 d = true →
    (Finset.univ.filter (fun c : Fin 4 × Fin 4 =>
      KT99 c = true ∧ R99 d c = true ∧ QE99 c = true)).card = if QE99 d = true then 3 else 2 := by
  decide +kernel

theorem wTn99 : ∀ d : Fin 4 × Fin 4, KT99 d = true →
    (Finset.univ.filter (fun c : Fin 4 × Fin 4 =>
      KT99 c = true ∧ R99 d c = true ∧ QN99 c = true)).card = if QE99 d = true then 6 else 2 := by
  decide +kernel

theorem wZe99 : ∀ d : Fin 4 × Fin 4, KZ99 d = true →
    (Finset.univ.filter (fun c : Fin 4 × Fin 4 =>
      KZ99 c = true ∧ R99 d c = true ∧ QE99 c = true)).card = if QE99 d = true then 1 else 0 := by
  decide +kernel

theorem wZn99 : ∀ d : Fin 4 × Fin 4, KZ99 d = true →
    (Finset.univ.filter (fun c : Fin 4 × Fin 4 =>
      KZ99 c = true ∧ R99 d c = true ∧ QN99 c = true)).card = if QE99 d = true then 0 else 0 := by
  decide +kernel

theorem bases99 :
    (Finset.univ.filter (fun c : Fin 4 × Fin 4 =>
      F99 c = true ∧ KT99 c = true ∧ QE99 c = true)).card = 1 ∧
    (Finset.univ.filter (fun c : Fin 4 × Fin 4 =>
      F99 c = true ∧ KT99 c = true ∧ QN99 c = true)).card = 3 ∧
    (Finset.univ.filter (fun c : Fin 4 × Fin 4 =>
      F99 c = true ∧ KZ99 c = true ∧ QE99 c = true)).card = 1 ∧
    (Finset.univ.filter (fun c : Fin 4 × Fin 4 =>
      F99 c = true ∧ KZ99 c = true ∧ QN99 c = true)).card = 1 := by
  decide +kernel

theorem qn99 : ∀ c : Fin 4 × Fin 4, QN99 c = true ↔ ¬ (QE99 c = true) := by
  decide

theorem filtNeg99 (K : Fin 4 × Fin 4 → Bool) (m : ℕ) :
    (W99 R99 F99 K m).filter (fun y => ¬ (QE99 (y (Fin.last m)) = true)) =
      (W99 R99 F99 K m).filter (fun y => QN99 (y (Fin.last m)) = true) :=
  Finset.filter_congr (fun y _ => (qn99 (y (Fin.last m))).symm)

theorem steps99 (K : Fin 4 × Fin 4 → Bool) (m : ℕ) (e1 e2 n1 n2 : ℕ)
    (hwe : ∀ d : Fin 4 × Fin 4, K d = true →
      (Finset.univ.filter (fun c : Fin 4 × Fin 4 =>
        K c = true ∧ R99 d c = true ∧ QE99 c = true)).card = if QE99 d = true then e1 else e2)
    (hwn : ∀ d : Fin 4 × Fin 4, K d = true →
      (Finset.univ.filter (fun c : Fin 4 × Fin 4 =>
        K c = true ∧ R99 d c = true ∧ QN99 c = true)).card = if QE99 d = true then n1 else n2) :
    ((W99 R99 F99 K (m + 1)).filter (fun y => QE99 (y (Fin.last (m + 1))) = true)).card =
      ((W99 R99 F99 K m).filter (fun y => QE99 (y (Fin.last m)) = true)).card * e1 +
        ((W99 R99 F99 K m).filter (fun y => ¬ (QE99 (y (Fin.last m)) = true))).card * e2 ∧
    ((W99 R99 F99 K (m + 1)).filter (fun y => ¬ (QE99 (y (Fin.last (m + 1))) = true))).card =
      ((W99 R99 F99 K m).filter (fun y => QE99 (y (Fin.last m)) = true)).card * n1 +
        ((W99 R99 F99 K m).filter (fun y => ¬ (QE99 (y (Fin.last m)) = true))).card * n2 := by
  refine ⟨classStep99 R99 F99 K QE99 QE99 e1 e2 m hwe, ?_⟩
  rw [filtNeg99 K (m + 1)]
  exact classStep99 R99 F99 K QN99 QE99 n1 n2 m hwn

theorem OMA.solution : type_of% @OMA.S_oeis_a233099.main := by
  obtain ⟨ce, hce⟩ : ∃ f : ℕ → ℕ, ∀ m, f m =
      ((W99 R99 F99 KT99 m).filter (fun y => QE99 (y (Fin.last m)) = true)).card :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨cn, hcn⟩ : ∃ f : ℕ → ℕ, ∀ m, f m =
      ((W99 R99 F99 KT99 m).filter (fun y => ¬ (QE99 (y (Fin.last m)) = true))).card :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨ze, hze⟩ : ∃ f : ℕ → ℕ, ∀ m, f m =
      ((W99 R99 F99 KZ99 m).filter (fun y => QE99 (y (Fin.last m)) = true)).card :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨zn, hzn⟩ : ∃ f : ℕ → ℕ, ∀ m, f m =
      ((W99 R99 F99 KZ99 m).filter (fun y => ¬ (QE99 (y (Fin.last m)) = true))).card :=
    ⟨_, fun _ => rfl⟩
  have rT : ∀ m, ce (m + 1) = ce m * 3 + cn m * 2 ∧ cn (m + 1) = ce m * 6 + cn m * 2 := by
    intro m
    rw [hce (m + 1), hcn (m + 1), hce m, hcn m]
    exact steps99 KT99 m 3 2 6 2 wTe99 wTn99
  have rZ : ∀ m, ze (m + 1) = ze m * 1 + zn m * 0 ∧ zn (m + 1) = ze m * 0 + zn m * 0 := by
    intro m
    rw [hze (m + 1), hzn (m + 1), hze m, hzn m]
    exact steps99 KZ99 m 1 0 0 0 wZe99 wZn99
  obtain ⟨b1, b2, b3, b4⟩ := bases99
  have ce0 : ce 0 = 1 := by
    rw [hce 0, baseW99 R99 F99 KT99 QE99]
    exact b1
  have cn0 : cn 0 = 3 := by
    rw [hcn 0, filtNeg99 KT99 0, baseW99 R99 F99 KT99 QN99]
    exact b2
  have ze0 : ze 0 = 1 := by
    rw [hze 0, baseW99 R99 F99 KZ99 QE99]
    exact b3
  have zn0 : zn 0 = 1 := by
    rw [hzn 0, filtNeg99 KZ99 0, baseW99 R99 F99 KZ99 QN99]
    exact b4
  have hT : ∀ m, 7 * (ce m : ℚ) = 10 * 6 ^ m - 3 * (-1) ^ m ∧
      7 * (cn m : ℚ) = 15 * 6 ^ m + 6 * (-1) ^ m := by
    intro m
    induction m with
    | zero =>
      rw [ce0, cn0]
      norm_num
    | succ m ih =>
      obtain ⟨r1, r2⟩ := rT m
      have r1' : (ce (m + 1) : ℚ) = (ce m : ℚ) * 3 + (cn m : ℚ) * 2 := by exact_mod_cast r1
      have r2' : (cn (m + 1) : ℚ) = (ce m : ℚ) * 6 + (cn m : ℚ) * 2 := by exact_mod_cast r2
      obtain ⟨i1, i2⟩ := ih
      constructor
      · linear_combination 7 * r1' + 3 * i1 + 2 * i2
      · linear_combination 7 * r2' + 6 * i1 + 2 * i2
  have hZ : ∀ k, ze (k + 1) = 1 ∧ zn (k + 1) = 0 := by
    intro k
    induction k with
    | zero =>
      obtain ⟨r1, r2⟩ := rZ 0
      omega
    | succ k ih =>
      obtain ⟨r1, r2⟩ := rZ (k + 1)
      obtain ⟨i1, i2⟩ := ih
      omega
  have htot : ∀ m, 2 * a (m + 1) = ce m + cn m + (ze m + zn m) := by
    intro m
    have h1 := twice99 (m + 1)
    have h2 := Finset.card_filter_add_card_filter_not (s := W99 R99 F99 KT99 m)
      (fun y => QE99 (y (Fin.last m)) = true)
    have h3 := Finset.card_filter_add_card_filter_not (s := W99 R99 F99 KZ99 m)
      (fun y => QE99 (y (Fin.last m)) = true)
    rw [cardST99 m, cardSZ99 m, ← h2, ← h3] at h1
    rw [hce m, hcn m, hze m, hzn m]
    omega
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℕ, ∀ n, a n = b n := ⟨a, fun _ => rfl⟩
  have htotb : ∀ m, 2 * b (m + 1) = ce m + cn m + (ze m + zn m) := by
    intro m
    rw [← hb]
    exact htot m
  have v1 : b 1 = 3 := by
    have h := htotb 0
    rw [show (0 : ℕ) + 1 = 1 from rfl] at h
    omega
  have hq : ∀ k, (14 : ℚ) * (b (k + 2) : ℚ) = 25 * 6 ^ (k + 1) + 3 * (-1) ^ (k + 1) + 7 := by
    intro k
    have h := htotb (k + 1)
    rw [show k + 1 + 1 = k + 2 by omega] at h
    obtain ⟨z1, z2⟩ := hZ k
    have h' : 2 * b (k + 2) = ce (k + 1) + cn (k + 1) + 1 := by omega
    have h2 : (2 : ℚ) * (b (k + 2) : ℚ) = (ce (k + 1) : ℚ) + (cn (k + 1) : ℚ) + 1 := by
      exact_mod_cast h'
    obtain ⟨t1, t2⟩ := hT (k + 1)
    linear_combination 7 * h2 + t1 + t2
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨f, hf⟩ : ∃ f : ℕ → ℚ, ∀ n, f n = if n = 0 then (0 : ℚ) else (a n : ℚ) :=
      ⟨_, fun _ => rfl⟩
    have hfun : (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = f :=
      funext fun n => (hf n).symm
    have f0 : f 0 = 0 := by rw [hf, if_pos (rfl : (0 : ℕ) = 0)]
    have f1 : f 1 = 3 := by
      rw [hf, if_neg (show ¬ ((1 : ℕ) = 0) by norm_num), hb]
      exact_mod_cast v1
    have f2 : f 2 = 11 := by
      rw [hf, if_neg (show ¬ ((2 : ℕ) = 0) by norm_num), hb]
      have h0 := hq 0
      rw [show (0 : ℕ) + 2 = 2 from rfl] at h0
      linear_combination (1 / 14 : ℚ) * h0
    have f3 : f 3 = 65 := by
      rw [hf, if_neg (show ¬ ((3 : ℕ) = 0) by norm_num), hb]
      have h0 := hq 1
      rw [show (1 : ℕ) + 2 = 3 from rfl] at h0
      linear_combination (1 / 14 : ℚ) * h0
    have f4 : f 4 = 386 := by
      rw [hf, if_neg (show ¬ ((4 : ℕ) = 0) by norm_num), hb]
      have h0 := hq 2
      rw [show (2 : ℕ) + 2 = 4 from rfl] at h0
      linear_combination (1 / 14 : ℚ) * h0
    have frec : ∀ k, f (k + 5) = 6 * f (k + 4) + f (k + 3) - 6 * f (k + 2) := by
      intro k
      rw [hf, hf, hf, hf, if_neg (show ¬ (k + 5 = 0) by omega),
        if_neg (show ¬ (k + 4 = 0) by omega), if_neg (show ¬ (k + 3 = 0) by omega),
        if_neg (show ¬ (k + 2 = 0) by omega)]
      simp only [hb]
      have q5 := hq (k + 3)
      have q4 := hq (k + 2)
      have q3 := hq (k + 1)
      have q2 := hq k
      rw [show k + 3 + 2 = k + 5 by omega] at q5
      rw [show k + 2 + 2 = k + 4 by omega] at q4
      rw [show k + 1 + 2 = k + 3 by omega] at q3
      linear_combination (1 / 14 : ℚ) * q5 - (6 / 14 : ℚ) * q4 - (1 / 14 : ℚ) * q3 +
        (6 / 14 : ℚ) * q2
    rw [show PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = PowerSeries.mk f
      from congrArg PowerSeries.mk hfun]
    have e : PowerSeries.mk f *
        ((1 - PowerSeries.X) * (1 + PowerSeries.X) * (1 - 6 * PowerSeries.X)) =
        PowerSeries.mk f
          - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6 * (PowerSeries.mk f * PowerSeries.X ^ 1)
          - PowerSeries.mk f * PowerSeries.X ^ 2
          + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6 * (PowerSeries.mk f * PowerSeries.X ^ 3) := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6]
      ring
    have e2 : (PowerSeries.X * (3 - 7 * PowerSeries.X - 4 * PowerSeries.X ^ 2 +
        3 * PowerSeries.X ^ 3) : PowerSeries ℚ) =
        PowerSeries.X ^ 1 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3
          - PowerSeries.X ^ 2 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 7
          - PowerSeries.X ^ 3 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4
          + PowerSeries.X ^ 4 * (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3 := by
      rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 7,
        map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4]
      ring
    rw [e, e2]
    ext n
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C]
    rcases Nat.lt_or_ge n 5 with hn | hn
    · interval_cases n
      · norm_num [f0]
      · norm_num [f0, f1]
      · norm_num [f0, f1, f2]
      · norm_num [f0, f1, f2, f3]
      · norm_num [f1, f2, f3, f4]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
      rw [if_pos (show 1 ≤ k + 5 by omega), if_pos (show 2 ≤ k + 5 by omega),
        if_pos (show 3 ≤ k + 5 by omega),
        if_pos (show 1 ≤ k + 5 by omega), if_pos (show 2 ≤ k + 5 by omega),
        if_pos (show 3 ≤ k + 5 by omega), if_pos (show 4 ≤ k + 5 by omega),
        if_neg (show ¬ (k + 5 - 1 = 0) by omega), if_neg (show ¬ (k + 5 - 2 = 0) by omega),
        if_neg (show ¬ (k + 5 - 3 = 0) by omega), if_neg (show ¬ (k + 5 - 4 = 0) by omega),
        show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
        show k + 5 - 3 = k + 2 by omega, frec k]
      ring
  · intro n hn hpar
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have h := hq k
    have hodd : Odd (k + 1) := Nat.odd_iff.2 (by omega)
    rw [hodd.neg_one_pow] at h
    rw [hb, eq_div_iff (by norm_num)]
    linear_combination 6 * h
  · intro n hn hpar
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have h := hq k
    have hev : Even (k + 1) := Nat.even_iff.2 (by omega)
    rw [hev.neg_one_pow] at h
    rw [hb, eq_div_iff (by norm_num)]
    linear_combination 6 * h
