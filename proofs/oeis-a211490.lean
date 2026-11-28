import OMAStatements.S_oeis_a211490

namespace OMA.P_oeis_a211490

open OMA.S_oeis_a211490

private abbrev IndSet (n : ℕ) :=
  {S : Fin (n + 1) → Bool // ∀ i : Fin n, ¬(S i.castSucc = true ∧ S i.succ = true)}

private def sgnRec (n : ℕ) (S : Fin (n + 1) → Bool) : (k : ℕ) → k ≤ n → ℤ
  | 0, _ => 1
  | k + 1, hk =>
    if S ⟨k, by omega⟩ || S ⟨k + 1, by omega⟩ then sgnRec n S k (by omega)
    else -sgnRec n S k (by omega)

private def sgnOf {n : ℕ} (S : Fin (n + 1) → Bool) (i : Fin (n + 1)) : ℤ :=
  sgnRec n S i.1 (Nat.le_of_lt_succ i.2)

private lemma sgnRec_cases (n : ℕ) (S : Fin (n + 1) → Bool) (k : ℕ) (hk : k ≤ n) :
    sgnRec n S k hk = 1 ∨ sgnRec n S k hk = -1 := by
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
    unfold sgnRec
    split_ifs
    · exact ih (by omega)
    · rcases ih (by omega) with h | h <;> simp [h]

private lemma sgnOf_cases {n : ℕ} (S : Fin (n + 1) → Bool) (i : Fin (n + 1)) :
    sgnOf S i = 1 ∨ sgnOf S i = -1 :=
  sgnRec_cases n S i.1 _

private lemma sgnOf_sq {n : ℕ} (S : Fin (n + 1) → Bool) (i : Fin (n + 1)) :
    sgnOf S i * sgnOf S i = 1 := by
  rcases sgnOf_cases S i with h | h <;> simp [h]

private lemma sgnOf_succ {n : ℕ} (S : Fin (n + 1) → Bool) (i : Fin n) :
    sgnOf S i.succ = if S i.castSucc || S i.succ then sgnOf S i.castSucc else -sgnOf S i.castSucc :=
  rfl

private def checker (n : ℕ) (v : ℤ) (i j : Fin (n + 1)) : ℤ :=
  if Even (i.1 + j.1) then v else -v

private def indMat (n : ℕ) (σ : Bool) (S : Fin (n + 1) → Bool) (i j : Fin (n + 1)) : ℤ :=
  (if σ then (1 : ℤ) else -1) * sgnOf S i * sgnOf S j * (if S i && S j then -3 else 1)

private lemma card_four_le_two {a b c d u w : ℤ}
    (ha : a = u ∨ a = w) (hb : b = u ∨ b = w) (hc : c = u ∨ c = w) (hd : d = u ∨ d = w) :
    ({a, b, c, d} : Finset ℤ).card ≤ 2 := by
  have hsub : ({a, b, c, d} : Finset ℤ) ⊆ {u, w} := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  exact le_trans (Finset.card_le_card hsub) Finset.card_le_two

private lemma checker_valid (n : ℕ) (v : ℤ) (hv : -4 ≤ v ∧ v ≤ 4) :
    isValid n (checker n v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j; unfold checker; split_ifs <;> omega
  · intro i j; unfold checker; rw [add_comm]
  · intro i j; unfold valid2x2 checker
    have h1 : Even (i.castSucc.1 + j.succ.1) ↔ ¬Even (i.castSucc.1 + j.castSucc.1) := by
      simp only [Nat.even_iff, Fin.val_castSucc, Fin.val_succ]; omega
    have h2 : Even (i.succ.1 + j.castSucc.1) ↔ ¬Even (i.castSucc.1 + j.castSucc.1) := by
      simp only [Nat.even_iff, Fin.val_castSucc, Fin.val_succ]; omega
    have h3 : Even (i.succ.1 + j.succ.1) ↔ Even (i.castSucc.1 + j.castSucc.1) := by
      simp only [Nat.even_iff, Fin.val_castSucc, Fin.val_succ]; omega
    by_cases he : Even (i.castSucc.1 + j.castSucc.1)
    · have h1' : ¬Even (i.castSucc.1 + j.succ.1) := fun h => h1.mp h he
      have h2' : ¬Even (i.succ.1 + j.castSucc.1) := fun h => h2.mp h he
      have h3' : Even (i.succ.1 + j.succ.1) := h3.mpr he
      simp only [he, h1', h2', h3', if_true, if_false]
      exact ⟨by ring, card_four_le_two (Or.inl rfl) (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)⟩
    · have h1' : Even (i.castSucc.1 + j.succ.1) := h1.mpr he
      have h2' : Even (i.succ.1 + j.castSucc.1) := h2.mpr he
      have h3' : ¬Even (i.succ.1 + j.succ.1) := fun h => he (h3.mp h)
      simp only [he, h1', h2', h3', if_true, if_false]
      exact ⟨by ring, card_four_le_two (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)⟩

private lemma valid2x2_mul (s : ℤ) {a b c d : ℤ} (h : valid2x2 a b c d) :
    valid2x2 (s * a) (s * b) (s * c) (s * d) := by
  refine ⟨by linear_combination s * h.1, ?_⟩
  have hImg : ({s * a, s * b, s * c, s * d} : Finset ℤ) = ({a, b, c, d} : Finset ℤ).image (fun x => s * x) := by
    ext x; simp
  rw [hImg]
  exact le_trans Finset.card_image_le h.2

private lemma indMat_unit_block (si si' sj sj' : Bool)
    (hi : ¬(si = true ∧ si' = true)) (hj : ¬(sj = true ∧ sj' = true)) :
    valid2x2
      (if si && sj then (-3 : ℤ) else 1)
      ((if sj || sj' then (1 : ℤ) else -1) * (if si && sj' then -3 else 1))
      ((if si || si' then (1 : ℤ) else -1) * (if si' && sj then -3 else 1))
      ((if si || si' then (1 : ℤ) else -1) * (if sj || sj' then (1 : ℤ) else -1) * (if si' && sj' then -3 else 1)) := by
  cases si <;> cases si' <;> cases sj <;> cases sj'
  all_goals first
    | (exfalso; exact hi ⟨rfl, rfl⟩)
    | (exfalso; exact hj ⟨rfl, rfl⟩)
    | (unfold valid2x2; decide)

private lemma indMat_valid (n : ℕ) (σ : Bool) (S : IndSet n) :
    isValid n (indMat n σ S.1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j; unfold indMat
    rcases sgnOf_cases S.1 i with hi | hi <;> rcases sgnOf_cases S.1 j with hj | hj <;>
      cases σ <;> cases S.1 i <;> cases S.1 j <;> simp [hi, hj]
  · intro i j; unfold indMat
    rw [Bool.and_comm]; ring
  · intro i j; unfold indMat
    rw [sgnOf_succ S.1 i, sgnOf_succ S.1 j]
    set u : ℤ := (if σ then (1 : ℤ) else -1) * sgnOf S.1 i.castSucc * sgnOf S.1 j.castSucc
    have hv := valid2x2_mul u (indMat_unit_block (S.1 i.castSucc) (S.1 i.succ) (S.1 j.castSucc) (S.1 j.succ) (S.2 i) (S.2 j))
    have h1 : (if σ = true then (1 : ℤ) else -1) * sgnOf S.1 i.castSucc * sgnOf S.1 j.castSucc *
        (if (S.1 i.castSucc && S.1 j.castSucc) = true then -3 else 1) =
        u * (if (S.1 i.castSucc && S.1 j.castSucc) = true then -3 else 1) := by rfl
    have h2 : (if σ = true then (1 : ℤ) else -1) * sgnOf S.1 i.castSucc *
        (if (S.1 j.castSucc || S.1 j.succ) = true then sgnOf S.1 j.castSucc else -sgnOf S.1 j.castSucc) *
        (if (S.1 i.castSucc && S.1 j.succ) = true then -3 else 1) =
        u * ((if (S.1 j.castSucc || S.1 j.succ) = true then (1 : ℤ) else -1) *
             (if (S.1 i.castSucc && S.1 j.succ) = true then -3 else 1)) := by
      cases (S.1 j.castSucc || S.1 j.succ) <;> (dsimp only [u]; simp only [Bool.false_eq_true, if_true, if_false]; ring)
    have h3 : (if σ = true then (1 : ℤ) else -1) *
        (if (S.1 i.castSucc || S.1 i.succ) = true then sgnOf S.1 i.castSucc else -sgnOf S.1 i.castSucc) *
        sgnOf S.1 j.castSucc * (if (S.1 i.succ && S.1 j.castSucc) = true then -3 else 1) =
        u * ((if (S.1 i.castSucc || S.1 i.succ) = true then (1 : ℤ) else -1) *
             (if (S.1 i.succ && S.1 j.castSucc) = true then -3 else 1)) := by
      cases (S.1 i.castSucc || S.1 i.succ) <;> (dsimp only [u]; simp only [Bool.false_eq_true, if_true, if_false]; ring)
    have h4 : (if σ = true then (1 : ℤ) else -1) *
        (if (S.1 i.castSucc || S.1 i.succ) = true then sgnOf S.1 i.castSucc else -sgnOf S.1 i.castSucc) *
        (if (S.1 j.castSucc || S.1 j.succ) = true then sgnOf S.1 j.castSucc else -sgnOf S.1 j.castSucc) *
        (if (S.1 i.succ && S.1 j.succ) = true then -3 else 1) =
        u * ((if (S.1 i.castSucc || S.1 i.succ) = true then (1 : ℤ) else -1) *
             (if (S.1 j.castSucc || S.1 j.succ) = true then (1 : ℤ) else -1) *
             (if (S.1 i.succ && S.1 j.succ) = true then -3 else 1)) := by
      cases (S.1 i.castSucc || S.1 i.succ) <;> cases (S.1 j.castSucc || S.1 j.succ) <;> (dsimp only [u]; simp only [Bool.false_eq_true, if_true, if_false]; ring)
    rw [h1, h2, h3, h4]
    exact hv

private lemma card_three_le_two {a b d : ℤ} (h : ({a, b, d} : Finset ℤ).card ≤ 2) :
    a = b ∨ a = d ∨ b = d := by
  by_contra hne
  push Not at hne
  rcases hne with ⟨hab, had, hbd⟩
  have hc : ({a, b, d} : Finset ℤ).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [hbd]
    · simp [hab, had]
  omega

private lemma valid2x2_sym_diag {a b d : ℤ}
    (ha : -4 ≤ a ∧ a ≤ 4) (hb : -4 ≤ b ∧ b ≤ 4) (hd : -4 ≤ d ∧ d ≤ 4)
    (hv : valid2x2 a b b d) :
    (a = d ∧ b = -a) ∨
    (a = -3 ∧ b = 1 ∧ d = 1) ∨ (a = 1 ∧ b = 1 ∧ d = -3) ∨
    (a = 3 ∧ b = -1 ∧ d = -1) ∨ (a = -1 ∧ b = -1 ∧ d = 3) := by
  rcases hv with ⟨hsum, hcard⟩
  have hsub : ({a, b, d} : Finset ℤ) ⊆ {a, b, b, d} := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; tauto
  have h3 := card_three_le_two (le_trans (Finset.card_le_card hsub) hcard)
  rcases h3 with rfl | rfl | rfl <;> omega

private lemma card_four_distinct {a b c d : ℤ}
    (h12 : a ≠ b) (h13 : a ≠ c) (h14 : a ≠ d) (h23 : b ≠ c) (h24 : b ≠ d) (h34 : c ≠ d) :
    ¬(({a, b, c, d} : Finset ℤ).card ≤ 2) := by
  have hc : ({a, b, c, d} : Finset ℤ).card = 4 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [h34]
    · simp [h23, h24]
    · simp [h12, h13, h14]
  omega

private lemma ext_unique {n : ℕ} {A B : Fin (n + 2) → Fin (n + 2) → ℤ}
    (hA : isValid (n + 1) A) (hB : isValid (n + 1) B)
    (htl : ∀ i j : Fin (n + 1), A i.castSucc j.castSucc = B i.castSucc j.castSucc)
    (hlast1 : A (Fin.last n).castSucc (Fin.last (n + 1)) = B (Fin.last n).castSucc (Fin.last (n + 1)))
    (hlast2 : A (Fin.last (n + 1)) (Fin.last (n + 1)) = B (Fin.last (n + 1)) (Fin.last (n + 1))) :
    A = B := by
  have hcol : ∀ k : ℕ, (hk : k ≤ n) →
      A ⟨n - k, by omega⟩ (Fin.last (n + 1)) = B ⟨n - k, by omega⟩ (Fin.last (n + 1)) := by
    intro k
    induction k with
    | zero => intro _; simpa [Fin.last] using hlast1
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hAblk := (hA.2.2 ⟨n - (k + 1), by omega⟩ (Fin.last n)).1
      have hBblk := (hB.2.2 ⟨n - (k + 1), by omega⟩ (Fin.last n)).1
      have htl1 := htl ⟨n - (k + 1), by omega⟩ (Fin.last n)
      have htl2 := htl ⟨n - k, by omega⟩ (Fin.last n)
      have h0 : (⟨n - (k + 1), by omega⟩ : Fin (n + 1)).castSucc = ⟨n - (k + 1), by omega⟩ := rfl
      have h1 : (⟨n - (k + 1), by omega⟩ : Fin (n + 1)).succ = ⟨n - k, by omega⟩ :=
        Fin.ext (by simp; omega)
      have h2 : (Fin.last n).succ = Fin.last (n + 1) := Fin.ext (by simp [Fin.last])
      have h3 : (⟨n - k, by omega⟩ : Fin (n + 1)).castSucc = ⟨n - k, by omega⟩ := rfl
      rw [h0, h1, h2] at hAblk hBblk
      rw [h0] at htl1
      rw [h3] at htl2
      linarith
  have hcol_all : ∀ i : Fin (n + 2), A i (Fin.last (n + 1)) = B i (Fin.last (n + 1)) := by
    intro i
    by_cases hi : i.1 = n + 1
    · have : i = Fin.last (n + 1) := Fin.ext hi
      rw [this]; exact hlast2
    · have hle : n - i.1 ≤ n := by omega
      have := hcol (n - i.1) hle
      have heq : (⟨n - (n - i.1), by omega⟩ : Fin (n + 2)) = i := Fin.ext (by dsimp; omega)
      rwa [heq] at this
  funext i j
  by_cases hj : j.1 = n + 1
  · have : j = Fin.last (n + 1) := Fin.ext hj
    rw [this]; exact hcol_all i
  · by_cases hi : i.1 = n + 1
    · have : i = Fin.last (n + 1) := Fin.ext hi
      rw [this, hA.2.1, hB.2.1]; exact hcol_all j
    · exact htl ⟨i.1, by omega⟩ ⟨j.1, by omega⟩

private def restrictMat {n : ℕ} (A : Fin (n + 2) → Fin (n + 2) → ℤ) :
    Fin (n + 1) → Fin (n + 1) → ℤ :=
  fun i j => A i.castSucc j.castSucc

private lemma restrictMat_valid {n : ℕ} {A : Fin (n + 2) → Fin (n + 2) → ℤ}
    (hA : isValid (n + 1) A) : isValid n (restrictMat A) :=
  ⟨fun i j => hA.1 i.castSucc j.castSucc,
   fun i j => hA.2.1 i.castSucc j.castSucc,
   fun i j => hA.2.2 i.castSucc j.castSucc⟩

private def extendS {n : ℕ} (S : Fin (n + 1) → Bool) (b : Bool) : Fin (n + 2) → Bool :=
  Fin.snoc S b

private lemma extendS_castSucc {n : ℕ} (S : Fin (n + 1) → Bool) (b : Bool) (i : Fin (n + 1)) :
    extendS S b i.castSucc = S i := by
  unfold extendS; simp

private lemma extendS_last {n : ℕ} (S : Fin (n + 1) → Bool) (b : Bool) :
    extendS S b (Fin.last (n + 1)) = b := by
  unfold extendS; simp

private lemma sgnRec_extendS {n : ℕ} (S : Fin (n + 1) → Bool) (b : Bool) (k : ℕ) (hk : k ≤ n) :
    sgnRec (n + 1) (extendS S b) k (by omega) = sgnRec n S k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold sgnRec
    have h1 : extendS S b ⟨k, by omega⟩ = S ⟨k, by omega⟩ :=
      extendS_castSucc S b ⟨k, by omega⟩
    have h2 : extendS S b ⟨k + 1, by omega⟩ = S ⟨k + 1, by omega⟩ :=
      extendS_castSucc S b ⟨k + 1, by omega⟩
    rw [h1, h2, ih (by omega)]

private lemma indMat_extend_tl {n : ℕ} (σ : Bool) (S : Fin (n + 1) → Bool) (b : Bool)
    (i j : Fin (n + 1)) :
    indMat (n + 1) σ (extendS S b) i.castSucc j.castSucc = indMat n σ S i j := by
  unfold indMat
  rw [extendS_castSucc, extendS_castSucc]
  unfold sgnOf
  simp only [Fin.val_castSucc]
  rw [sgnRec_extendS S b i.1 (Nat.le_of_lt_succ i.2),
      sgnRec_extendS S b j.1 (Nat.le_of_lt_succ j.2)]

private lemma classify (n : ℕ) : ∀ (_hn : 1 ≤ n) (A : Fin (n + 1) → Fin (n + 1) → ℤ), isValid n A →
    (∃ v : ℤ, -4 ≤ v ∧ v ≤ 4 ∧ v ≠ 1 ∧ v ≠ -1 ∧ A = checker n v) ∨
    (∃ (σ : Bool) (S : IndSet n), A = indMat n σ S.1) := by
  induction n with
  | zero => intro hn; omega
  | succ k ih =>
    intro _hn A hA
    cases k with
    | zero =>
      have hdiag := valid2x2_sym_diag (hA.1 0 0) (hA.1 0 1) (hA.1 1 1)
        (by simpa [hA.2.1 1 0] using hA.2.2 0 0)
      rcases hdiag with ⟨had, hba⟩ | ⟨ha, hb, hd⟩ | ⟨ha, hb, hd⟩ | ⟨ha, hb, hd⟩ | ⟨ha, hb, hd⟩
      · by_cases h1 : A 0 0 = 1
        · right; refine ⟨true, ⟨fun _ => false, by intro i; simp⟩, ?_⟩
          funext i j; fin_cases i <;> fin_cases j <;> simp [indMat, sgnOf, sgnRec, h1, hba, ← had, hA.2.1 1 0]
        · by_cases hm1 : A 0 0 = -1
          · right; refine ⟨false, ⟨fun _ => false, by intro i; simp⟩, ?_⟩
            funext i j; fin_cases i <;> fin_cases j <;> simp [indMat, sgnOf, sgnRec, hm1, hba, ← had, hA.2.1 1 0]
          · left; refine ⟨A 0 0, (hA.1 0 0).1, (hA.1 0 0).2, h1, hm1, ?_⟩
            funext i j; fin_cases i <;> fin_cases j <;> simp [checker, hba, ← had, hA.2.1 1 0]
      · right; refine ⟨true, ⟨fun i => decide (i.1 = 0), by intro i; fin_cases i; simp⟩, ?_⟩
        funext i j; fin_cases i <;> fin_cases j <;> simp [indMat, sgnOf, sgnRec, ha, hb, hd, hA.2.1 1 0]
      · right; refine ⟨true, ⟨fun i => decide (i.1 = 1), by intro i; fin_cases i; simp⟩, ?_⟩
        funext i j; fin_cases i <;> fin_cases j <;> simp [indMat, sgnOf, sgnRec, ha, hb, hd, hA.2.1 1 0]
      · right; refine ⟨false, ⟨fun i => decide (i.1 = 0), by intro i; fin_cases i; simp⟩, ?_⟩
        funext i j; fin_cases i <;> fin_cases j <;> simp [indMat, sgnOf, sgnRec, ha, hb, hd, hA.2.1 1 0]
      · right; refine ⟨false, ⟨fun i => decide (i.1 = 1), by intro i; fin_cases i; simp⟩, ?_⟩
        funext i j; fin_cases i <;> fin_cases j <;> simp [indMat, sgnOf, sgnRec, ha, hb, hd, hA.2.1 1 0]
    | succ k =>
      let m0 := k + 1
      have htl_res := ih (by omega) (restrictMat (n := m0) A) (restrictMat_valid (n := m0) hA)
      have hdiag := valid2x2_sym_diag
        (hA.1 (Fin.last m0).castSucc (Fin.last m0).castSucc)
        (hA.1 (Fin.last m0).castSucc (Fin.last (m0 + 1)))
        (hA.1 (Fin.last (m0 + 1)) (Fin.last (m0 + 1)))
        (by
          have := hA.2.2 (Fin.last m0) (Fin.last m0)
          have hl : (Fin.last m0).succ = Fin.last (m0 + 1) := Fin.ext (by simp [Fin.last])
          rw [hl, hA.2.1 (Fin.last (m0 + 1)) (Fin.last m0).castSucc] at this
          exact this)
      rcases htl_res with ⟨v, hv1, hv2, hvn1, hvnm1, hchk⟩ | ⟨σ, S, hind⟩
      · have htl_eq : ∀ i j : Fin (m0 + 1), A i.castSucc j.castSucc = checker m0 v i j := by
          intro i j; exact congrFun (congrFun hchk i) j
        have hann : A (Fin.last m0).castSucc (Fin.last m0).castSucc = v := by
          rw [htl_eq (Fin.last m0) (Fin.last m0)]
          unfold checker; simp [Fin.last]
        have hanm : A ⟨m0 - 1, by omega⟩ (Fin.last m0).castSucc = -v := by
          have := htl_eq ⟨m0 - 1, by omega⟩ (Fin.last m0)
          rw [show (⟨m0 - 1, by omega⟩ : Fin (m0 + 1)).castSucc = ⟨m0 - 1, by omega⟩ from rfl] at this
          rw [this]; unfold checker
          have hodd : ¬Even (m0 - 1 + m0) := by
            intro ⟨t, ht⟩; omega
          simp [Fin.last, hodd]
        rw [hann] at hdiag
        rcases hdiag with ⟨had, hba⟩ | ⟨ha, hb, hd⟩ | ⟨ha, hb, hd⟩ | ⟨ha, hb, hd⟩ | ⟨ha, hb, hd⟩
        · left; refine ⟨v, hv1, hv2, hvn1, hvnm1, ?_⟩
          apply ext_unique hA (checker_valid (m0 + 1) v ⟨hv1, hv2⟩)
          · intro i j; rw [htl_eq i j]; rfl
          · rw [hba]; unfold checker
            simp [Fin.last]
          · rw [← had]; unfold checker; simp [Fin.last]
        · exfalso
          have hblk := hA.2.2 ⟨m0 - 1, by omega⟩ (Fin.last m0)
          have h1 : (⟨m0 - 1, by omega⟩ : Fin (m0 + 1)).castSucc = ⟨m0 - 1, by omega⟩ := rfl
          have h2 : (⟨m0 - 1, by omega⟩ : Fin (m0 + 1)).succ = (Fin.last m0).castSucc := Fin.ext (by simp [Fin.last]; omega)
          have h3 : (Fin.last m0).succ = Fin.last (m0 + 1) := Fin.ext (by simp [Fin.last])
          rw [h1, h2, h3, hanm, hann, ha, hb] at hblk
          have hx : A ⟨m0 - 1, by omega⟩ (Fin.last (m0 + 1)) = -1 := by linarith [hblk.1]
          rw [hx] at hblk
          exact card_four_distinct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hblk.2
        · omega
        · exfalso
          have hblk := hA.2.2 ⟨m0 - 1, by omega⟩ (Fin.last m0)
          have h1 : (⟨m0 - 1, by omega⟩ : Fin (m0 + 1)).castSucc = ⟨m0 - 1, by omega⟩ := rfl
          have h2 : (⟨m0 - 1, by omega⟩ : Fin (m0 + 1)).succ = (Fin.last m0).castSucc := Fin.ext (by simp [Fin.last]; omega)
          have h3 : (Fin.last m0).succ = Fin.last (m0 + 1) := Fin.ext (by simp [Fin.last])
          rw [h1, h2, h3, hanm, hann, ha, hb] at hblk
          have hx : A ⟨m0 - 1, by omega⟩ (Fin.last (m0 + 1)) = 1 := by linarith [hblk.1]
          rw [hx] at hblk
          exact card_four_distinct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hblk.2
        · omega
      · have htl_eq : ∀ i j : Fin (m0 + 1), A i.castSucc j.castSucc = indMat m0 σ S.1 i j := by
          intro i j; exact congrFun (congrFun hind i) j
        have hann : A (Fin.last m0).castSucc (Fin.last m0).castSucc =
            (if σ then (1 : ℤ) else -1) * (if S.1 (Fin.last m0) then -3 else 1) := by
          rw [htl_eq (Fin.last m0) (Fin.last m0)]
          unfold indMat
          have hsq := sgnOf_sq S.1 (Fin.last m0)
          have : (if σ then (1 : ℤ) else -1) * sgnOf S.1 (Fin.last m0) * sgnOf S.1 (Fin.last m0) =
              (if σ then (1 : ℤ) else -1) := by linear_combination (if σ then (1 : ℤ) else -1) * hsq
          rw [this, Bool.and_self]
        cases hSn : S.1 (Fin.last m0)
        · rw [hSn] at hann
          let hexF : IndSet (m0 + 1) := ⟨extendS S.1 false, by
            intro i
            by_cases hi : i.1 < m0
            · have h1 : extendS S.1 false i.castSucc = S.1 ⟨i.1, by omega⟩ :=
                extendS_castSucc S.1 false ⟨i.1, by omega⟩
              have h2 : extendS S.1 false i.succ = S.1 ⟨i.1 + 1, by omega⟩ := by
                have : i.succ = (⟨i.1 + 1, by omega⟩ : Fin (m0 + 1)).castSucc := Fin.ext (by simp)
                rw [this]; exact extendS_castSucc S.1 false ⟨i.1 + 1, by omega⟩
              rw [h1, h2]; exact S.2 ⟨i.1, hi⟩
            · have hi' : i.succ = Fin.last (m0 + 1) := Fin.ext (by simp [Fin.last]; omega)
              rw [hi', extendS_last]; simp⟩
          let hexT : IndSet (m0 + 1) := ⟨extendS S.1 true, by
            intro i
            by_cases hi : i.1 < m0
            · have h1 : extendS S.1 true i.castSucc = S.1 ⟨i.1, by omega⟩ :=
                extendS_castSucc S.1 true ⟨i.1, by omega⟩
              have h2 : extendS S.1 true i.succ = S.1 ⟨i.1 + 1, by omega⟩ := by
                have : i.succ = (⟨i.1 + 1, by omega⟩ : Fin (m0 + 1)).castSucc := Fin.ext (by simp)
                rw [this]; exact extendS_castSucc S.1 true ⟨i.1 + 1, by omega⟩
              rw [h1, h2]; exact S.2 ⟨i.1, hi⟩
            · have hi' : i.castSucc = (Fin.last m0).castSucc := Fin.ext (by simp [Fin.last]; omega)
              rw [hi', extendS_castSucc, hSn]; simp⟩
          have hs_nF : sgnOf (extendS S.1 false) (Fin.last m0).castSucc = sgnOf S.1 (Fin.last m0) := by
            unfold sgnOf; exact sgnRec_extendS S.1 false m0 (le_refl m0)
          have hs_nT : sgnOf (extendS S.1 true) (Fin.last m0).castSucc = sgnOf S.1 (Fin.last m0) := by
            unfold sgnOf; exact sgnRec_extendS S.1 true m0 (le_refl m0)
          have hs_extF : sgnOf (extendS S.1 false) (Fin.last (m0 + 1)) = -sgnOf S.1 (Fin.last m0) := by
            have := sgnOf_succ (extendS S.1 false) (Fin.last m0)
            have hl : (Fin.last m0).succ = Fin.last (m0 + 1) := Fin.ext (by simp [Fin.last])
            rw [hl] at this; rw [this, extendS_castSucc, extendS_last, hSn, hs_nF]; simp
          have hs_extT : sgnOf (extendS S.1 true) (Fin.last (m0 + 1)) = sgnOf S.1 (Fin.last m0) := by
            have := sgnOf_succ (extendS S.1 true) (Fin.last m0)
            have hl : (Fin.last m0).succ = Fin.last (m0 + 1) := Fin.ext (by simp [Fin.last])
            rw [hl] at this; rw [this, extendS_last, hs_nT]; simp
          have hsq := sgnOf_sq S.1 (Fin.last m0)
          cases σ <;> simp at hann <;> rw [hann] at hdiag
          · rcases hdiag with ⟨had, hba⟩ | ⟨ha, hb, hd⟩ | ⟨ha, hb, hd⟩ | ⟨ha, hb, hd⟩ | ⟨ha, hb, hd⟩
            · right; refine ⟨false, hexF, ?_⟩
              apply ext_unique hA (indMat_valid (m0 + 1) false hexF)
              · intro i j; rw [htl_eq i j, indMat_extend_tl]
              · rw [hba]; unfold indMat; dsimp only [hexF]
                rw [hs_nF, hs_extF]; dsimp only [m0] at *; simp [extendS]
                nlinarith [hsq]
              · rw [← had]; unfold indMat; dsimp only [hexF]
                rw [hs_extF]; dsimp only [m0] at *; simp [extendS]
                nlinarith [hsq]
            · omega
            · omega
            · omega
            · right; refine ⟨false, hexT, ?_⟩
              apply ext_unique hA (indMat_valid (m0 + 1) false hexT)
              · intro i j; rw [htl_eq i j, indMat_extend_tl]
              · rw [hb]; unfold indMat; dsimp only [hexT]
                rw [hs_nT, hs_extT]; dsimp only [m0] at *
                have hSn' : S.1 (Fin.last (k + 1)) = false := hSn
                simp [extendS, hSn']
                nlinarith [hsq]
              · rw [hd]; unfold indMat; dsimp only [hexT]
                rw [hs_extT]; dsimp only [m0] at *; simp [extendS]
                nlinarith [hsq]
          · rcases hdiag with ⟨had, hba⟩ | ⟨ha, hb, hd⟩ | ⟨ha, hb, hd⟩ | ⟨ha, hb, hd⟩ | ⟨ha, hb, hd⟩
            · right; refine ⟨true, hexF, ?_⟩
              apply ext_unique hA (indMat_valid (m0 + 1) true hexF)
              · intro i j; rw [htl_eq i j, indMat_extend_tl]
              · rw [hba]; unfold indMat; dsimp only [hexF]
                rw [hs_nF, hs_extF]; dsimp only [m0] at *; simp [extendS]
                nlinarith [hsq]
              · rw [← had]; unfold indMat; dsimp only [hexF]
                rw [hs_extF]; dsimp only [m0] at *; simp [extendS]
                nlinarith [hsq]
            · omega
            · right; refine ⟨true, hexT, ?_⟩
              apply ext_unique hA (indMat_valid (m0 + 1) true hexT)
              · intro i j; rw [htl_eq i j, indMat_extend_tl]
              · rw [hb]; unfold indMat; dsimp only [hexT]
                rw [hs_nT, hs_extT]; dsimp only [m0] at *
                have hSn' : S.1 (Fin.last (k + 1)) = false := hSn
                simp [extendS, hSn']
                nlinarith [hsq]
              · rw [hd]; unfold indMat; dsimp only [hexT]
                rw [hs_extT]; dsimp only [m0] at *; simp [extendS]
                nlinarith [hsq]
            · omega
            · omega
        · rw [hSn] at hann
          have hSprev : S.1 ⟨m0 - 1, by omega⟩ = false := by
            have := S.2 ⟨m0 - 1, by omega⟩
            have h2 : (⟨m0 - 1, by omega⟩ : Fin m0).succ = Fin.last m0 := Fin.ext (by simp [Fin.last]; omega)
            rw [h2, hSn] at this
            cases h : S.1 ⟨m0 - 1, by omega⟩
            · rfl
            · exfalso; exact this ⟨h, rfl⟩
          have hsq := sgnOf_sq S.1 (Fin.last m0)
          have hsprev : sgnOf S.1 ⟨m0 - 1, by omega⟩ = sgnOf S.1 (Fin.last m0) := by
            have := sgnOf_succ S.1 ⟨m0 - 1, by omega⟩
            have h2 : (⟨m0 - 1, by omega⟩ : Fin m0).succ = Fin.last m0 := Fin.ext (by simp [Fin.last]; omega)
            rw [h2, hSn] at this
            simpa using this.symm
          have hanm : A ⟨m0 - 1, by omega⟩ (Fin.last m0).castSucc = (if σ then (1 : ℤ) else -1) := by
            have := htl_eq ⟨m0 - 1, by omega⟩ (Fin.last m0)
            rw [show (⟨m0 - 1, by omega⟩ : Fin (m0 + 1)).castSucc = ⟨m0 - 1, by omega⟩ from rfl] at this
            rw [this]; unfold indMat
            rw [hSprev, hsprev]
            simp only [Bool.false_and, Bool.false_eq_true, if_false, mul_one]
            linear_combination (if σ then (1 : ℤ) else -1) * hsq
          let hexF : IndSet (m0 + 1) := ⟨extendS S.1 false, by
            intro i
            by_cases hi : i.1 < m0
            · have h1 : extendS S.1 false i.castSucc = S.1 ⟨i.1, by omega⟩ :=
                extendS_castSucc S.1 false ⟨i.1, by omega⟩
              have h2 : extendS S.1 false i.succ = S.1 ⟨i.1 + 1, by omega⟩ := by
                have : i.succ = (⟨i.1 + 1, by omega⟩ : Fin (m0 + 1)).castSucc := Fin.ext (by simp)
                rw [this]; exact extendS_castSucc S.1 false ⟨i.1 + 1, by omega⟩
              rw [h1, h2]; exact S.2 ⟨i.1, hi⟩
            · have hi' : i.succ = Fin.last (m0 + 1) := Fin.ext (by simp [Fin.last]; omega)
              rw [hi', extendS_last]; simp⟩
          have hs_nF : sgnOf (extendS S.1 false) (Fin.last m0).castSucc = sgnOf S.1 (Fin.last m0) := by
            unfold sgnOf; exact sgnRec_extendS S.1 false m0 (le_refl m0)
          have hs_extF : sgnOf (extendS S.1 false) (Fin.last (m0 + 1)) = sgnOf S.1 (Fin.last m0) := by
            have := sgnOf_succ (extendS S.1 false) (Fin.last m0)
            have hl : (Fin.last m0).succ = Fin.last (m0 + 1) := Fin.ext (by simp [Fin.last])
            rw [hl] at this; rw [this, extendS_castSucc, hSn, hs_nF]; simp
          cases σ <;> simp at hann hanm <;> rw [hann] at hdiag
          · rcases hdiag with ⟨had, hba⟩ | ⟨ha, hb, hd⟩ | ⟨ha, hb, hd⟩ | ⟨ha, hb, hd⟩ | ⟨ha, hb, hd⟩
            · exfalso
              have hblk := hA.2.2 ⟨m0 - 1, by omega⟩ (Fin.last m0)
              have h1 : (⟨m0 - 1, by omega⟩ : Fin (m0 + 1)).castSucc = ⟨m0 - 1, by omega⟩ := rfl
              have h2 : (⟨m0 - 1, by omega⟩ : Fin (m0 + 1)).succ = (Fin.last m0).castSucc := Fin.ext (by simp [Fin.last]; omega)
              have h3 : (Fin.last m0).succ = Fin.last (m0 + 1) := Fin.ext (by simp [Fin.last])
              rw [h1, h2, h3, hanm, hann, hba] at hblk
              have hx : A ⟨m0 - 1, by omega⟩ (Fin.last (m0 + 1)) = 1 := by linarith [hblk.1]
              rw [hx] at hblk
              exact card_four_distinct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hblk.2
            · omega
            · omega
            · right; refine ⟨false, hexF, ?_⟩
              apply ext_unique hA (indMat_valid (m0 + 1) false hexF)
              · intro i j; rw [htl_eq i j, indMat_extend_tl]
              · rw [hb]; unfold indMat; dsimp only [hexF]
                rw [hs_nF, hs_extF]; dsimp only [m0] at *; simp [extendS]
                nlinarith [hsq]
              · rw [hd]; unfold indMat; dsimp only [hexF]
                rw [hs_extF]; dsimp only [m0] at *; simp [extendS]
                nlinarith [hsq]
            · omega
          · rcases hdiag with ⟨had, hba⟩ | ⟨ha, hb, hd⟩ | ⟨ha, hb, hd⟩ | ⟨ha, hb, hd⟩ | ⟨ha, hb, hd⟩
            · exfalso
              have hblk := hA.2.2 ⟨m0 - 1, by omega⟩ (Fin.last m0)
              have h1 : (⟨m0 - 1, by omega⟩ : Fin (m0 + 1)).castSucc = ⟨m0 - 1, by omega⟩ := rfl
              have h2 : (⟨m0 - 1, by omega⟩ : Fin (m0 + 1)).succ = (Fin.last m0).castSucc := Fin.ext (by simp [Fin.last]; omega)
              have h3 : (Fin.last m0).succ = Fin.last (m0 + 1) := Fin.ext (by simp [Fin.last])
              rw [h1, h2, h3, hanm, hann, hba] at hblk
              have hx : A ⟨m0 - 1, by omega⟩ (Fin.last (m0 + 1)) = -1 := by linarith [hblk.1]
              rw [hx] at hblk
              exact card_four_distinct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hblk.2
            · right; refine ⟨true, hexF, ?_⟩
              apply ext_unique hA (indMat_valid (m0 + 1) true hexF)
              · intro i j; rw [htl_eq i j, indMat_extend_tl]
              · rw [hb]; unfold indMat; dsimp only [hexF]
                rw [hs_nF, hs_extF]; dsimp only [m0] at *; simp [extendS]
                nlinarith [hsq]
              · rw [hd]; unfold indMat; dsimp only [hexF]
                rw [hs_extF]; dsimp only [m0] at *; simp [extendS]
                nlinarith [hsq]
            · omega
            · omega
            · omega

private def CheckVal := {v : ℤ // -4 ≤ v ∧ v ≤ 4 ∧ v ≠ 1 ∧ v ≠ -1}

private def checkValEquiv :
    CheckVal ≃ {v : Fin (2 * 4 + 1) // (v.1 : ℤ) - 4 ≠ 1 ∧ (v.1 : ℤ) - 4 ≠ -1} where
  toFun v := ⟨⟨(v.1 + 4).toNat, by have := v.2; omega⟩,
    by dsimp only; have := v.2; have h : ((v.1 + 4).toNat : ℤ) = v.1 + 4 := Int.toNat_of_nonneg (by omega); omega,
    by dsimp only; have := v.2; have h : ((v.1 + 4).toNat : ℤ) = v.1 + 4 := Int.toNat_of_nonneg (by omega); omega⟩
  invFun v := ⟨(v.1.1 : ℤ) - 4, by have := v.1.2; omega, by have := v.1.2; omega, v.2.1, v.2.2⟩
  left_inv v := Subtype.ext (by dsimp only; have := v.2; have h : ((v.1 + 4).toNat : ℤ) = v.1 + 4 := Int.toNat_of_nonneg (by omega); omega)
  right_inv v := Subtype.ext (Fin.ext (by dsimp only; have := v.1.2; omega))

private instance : Fintype CheckVal :=
  Fintype.ofEquiv _ checkValEquiv.symm

private lemma card_CheckVal : Fintype.card CheckVal = 7 := by
  rw [Fintype.card_congr checkValEquiv]
  decide

private lemma card_IndSet (n : ℕ) : Fintype.card (IndSet n) = Nat.fib (n + 3) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      have : Fintype.card (IndSet 0) = 2 := by unfold IndSet; decide
      exact this
    | 1 =>
      have : Fintype.card (IndSet 1) = 3 := by unfold IndSet; decide
      exact this
    | k + 2 =>
      let e : IndSet (k + 2) ≃ IndSet (k + 1) ⊕ IndSet k :=
        { toFun := fun S =>
            if h : S.1 (Fin.last (k + 2)) = false then
              Sum.inl ⟨fun i => S.1 i.castSucc, fun i => S.2 i.castSucc⟩
            else
              Sum.inr ⟨fun i => S.1 i.castSucc.castSucc, fun i => S.2 i.castSucc.castSucc⟩
          invFun := fun x =>
            match x with
            | Sum.inl S => ⟨extendS S.1 false, by
                intro i
                by_cases hi : i.1 < k + 1
                · have h1 : extendS S.1 false i.castSucc = S.1 ⟨i.1, by omega⟩ :=
                    extendS_castSucc S.1 false ⟨i.1, by omega⟩
                  have h2 : extendS S.1 false i.succ = S.1 ⟨i.1 + 1, by omega⟩ := by
                    have : i.succ = (⟨i.1 + 1, by omega⟩ : Fin (k + 2)).castSucc := Fin.ext (by simp)
                    rw [this]; exact extendS_castSucc S.1 false ⟨i.1 + 1, by omega⟩
                  rw [h1, h2]; exact S.2 ⟨i.1, hi⟩
                · have hi' : i.succ = Fin.last (k + 2) := Fin.ext (by simp [Fin.last]; omega)
                  rw [hi', extendS_last]; simp⟩
            | Sum.inr S => ⟨extendS (extendS S.1 false) true, by
                intro i
                by_cases hi : i.1 < k
                · have h1 : extendS (extendS S.1 false) true i.castSucc = S.1 ⟨i.1, by omega⟩ := by
                    have : i.castSucc = (⟨i.1, by omega⟩ : Fin (k + 1)).castSucc.castSucc := rfl
                    rw [this, extendS_castSucc, extendS_castSucc]
                  have h2 : extendS (extendS S.1 false) true i.succ = S.1 ⟨i.1 + 1, by omega⟩ := by
                    have : i.succ = (⟨i.1 + 1, by omega⟩ : Fin (k + 1)).castSucc.castSucc := Fin.ext (by simp)
                    rw [this, extendS_castSucc, extendS_castSucc]
                  rw [h1, h2]; exact S.2 ⟨i.1, hi⟩
                · by_cases hi1 : i.1 = k
                  · have h2 : i.succ = (Fin.last (k + 1)).castSucc := Fin.ext (by simp [Fin.last]; omega)
                    rw [h2]
                    have hf : extendS (extendS S.1 false) true (Fin.last (k + 1)).castSucc = false := by
                      rw [extendS_castSucc, extendS_last]
                    rw [hf]; simp
                  · have h1 : i.castSucc = (Fin.last (k + 1)).castSucc := Fin.ext (by simp [Fin.last]; omega)
                    rw [h1]
                    have hf : extendS (extendS S.1 false) true (Fin.last (k + 1)).castSucc = false := by
                      rw [extendS_castSucc, extendS_last]
                    rw [hf]; simp⟩
          left_inv := fun S => by
            dsimp only
            split_ifs with h
            · dsimp only
              apply Subtype.ext; funext i
              refine Fin.lastCases ?_ ?_ i
              · simp only [extendS_last, h]
              · intro j; simp only [extendS_castSucc]
            · dsimp only
              apply Subtype.ext; funext i
              have hT : S.1 (Fin.last (k + 2)) = true := by cases h' : S.1 (Fin.last (k + 2)) <;> simp_all
              have hF : S.1 (Fin.last (k + 1)).castSucc = false := by
                have := S.2 (Fin.last (k + 1))
                have hl : (Fin.last (k + 1)).succ = Fin.last (k + 2) := Fin.ext (by simp [Fin.last])
                rw [hl, hT] at this
                cases h' : S.1 (Fin.last (k + 1)).castSucc <;> simp_all
              refine Fin.lastCases ?_ ?_ i
              · simp only [extendS_last, hT]
              · intro j
                simp only [extendS_castSucc]
                refine Fin.lastCases ?_ ?_ j
                · simp only [extendS_last, hF]
                · intro r; simp only [extendS_castSucc]
          right_inv := fun x => by
            rcases x with S | S
            · dsimp only
              rw [dif_pos (extendS_last S.1 false)]
              congr 1; apply Subtype.ext; funext i; exact extendS_castSucc S.1 false i
            · dsimp only
              rw [dif_neg (by rw [extendS_last]; decide)]
              congr 1; apply Subtype.ext; funext i
              dsimp only
              simp only [extendS_castSucc] }
      rw [Fintype.card_congr e, Fintype.card_sum, ih (k + 1) (by omega), ih k (by omega)]
      have hfib : Nat.fib (k + 2 + 3) = Nat.fib (k + 3) + Nat.fib (k + 1 + 3) := by
        simpa [add_assoc] using Nat.fib_add_two (n := k + 3)
      omega

private lemma indMat_diag {n : ℕ} (σ : Bool) (S : Fin (n + 1) → Bool) (i : Fin (n + 1)) :
    indMat n σ S i i = (if σ then (1 : ℤ) else -1) * (if S i then -3 else 1) := by
  unfold indMat
  have hsq := sgnOf_sq S i
  rw [Bool.and_self]
  linear_combination (if σ then (1 : ℤ) else -1) * (if S i then -3 else 1) * hsq

private lemma indMat_inj {n : ℕ} (hn : 1 ≤ n) {σ1 σ2 : Bool} {S1 S2 : IndSet n}
    (h : indMat n σ1 S1.1 = indMat n σ2 S2.1) : σ1 = σ2 ∧ S1 = S2 := by
  have hd : ∀ i : Fin (n + 1),
      (if σ1 then (1 : ℤ) else -1) * (if S1.1 i then -3 else 1) =
      (if σ2 then (1 : ℤ) else -1) * (if S2.1 i then -3 else 1) := by
    intro i
    have := congrFun (congrFun h i) i
    rwa [indMat_diag, indMat_diag] at this
  have hσ : σ1 = σ2 := by
    have h0 := hd ⟨0, by omega⟩
    have h1 := hd ⟨1, by omega⟩
    have hS1 := S1.2 ⟨0, by omega⟩
    have hS2 := S2.2 ⟨0, by omega⟩
    have h0' : (⟨0, by omega⟩ : Fin n).castSucc = ⟨0, by omega⟩ := rfl
    have h1' : (⟨0, by omega⟩ : Fin n).succ = ⟨1, by omega⟩ := rfl
    rw [h0', h1'] at hS1 hS2
    cases σ1 <;> cases σ2 <;> cases h01 : S1.1 ⟨0, by omega⟩ <;> cases h11 : S1.1 ⟨1, by omega⟩ <;>
      cases h02 : S2.1 ⟨0, by omega⟩ <;> cases h12 : S2.1 ⟨1, by omega⟩ <;> simp_all
  refine ⟨hσ, Subtype.ext (funext fun i => ?_)⟩
  subst hσ
  have hi := hd i
  cases σ1 <;> cases h1 : S1.1 i <;> cases h2 : S2.1 i <;> simp_all

private lemma checker_ne_indMat {n : ℕ} (hn : 1 ≤ n) (v : CheckVal) (σ : Bool) (S : IndSet n) :
    checker n v.1 ≠ indMat n σ S.1 := by
  intro heq
  have h00 := congrFun (congrFun heq ⟨0, by omega⟩) ⟨0, by omega⟩
  have h01 := congrFun (congrFun heq ⟨0, by omega⟩) ⟨1, by omega⟩
  unfold checker at h00 h01
  simp only [show Even (0 + 0) by decide, show ¬Even (0 + 1) by decide, if_true, if_false] at h00 h01
  rw [indMat_diag] at h00
  have hS01 := S.2 ⟨0, by omega⟩
  have h0' : (⟨0, by omega⟩ : Fin n).castSucc = ⟨0, by omega⟩ := rfl
  have h1' : (⟨0, by omega⟩ : Fin n).succ = ⟨1, by omega⟩ := rfl
  rw [h0', h1'] at hS01
  unfold indMat at h01
  have hs0 : sgnOf S.1 ⟨0, by omega⟩ = 1 := rfl
  have hs1 : sgnOf S.1 ⟨1, by omega⟩ = if S.1 ⟨0, by omega⟩ || S.1 ⟨1, by omega⟩ then 1 else -1 := rfl
  rw [hs0, hs1] at h01
  rcases v with ⟨v, hv1, hv2, hvn1, hvnm1⟩
  cases σ <;> cases h0 : S.1 ⟨0, by omega⟩ <;> cases h1 : S.1 ⟨1, by omega⟩ <;> simp_all

private lemma a_eq (n : ℕ) (hn : 1 ≤ n) :
    a n = 7 + 2 * Nat.fib (n + 3) := by
  unfold a
  rw [if_neg (by omega)]
  let f : CheckVal ⊕ (Bool × IndSet n) → {A : Fin (n + 1) → Fin (n + 1) → ℤ // isValid n A} :=
    fun x => match x with
      | Sum.inl v => ⟨checker n v.1, checker_valid n v.1 ⟨v.2.1, v.2.2.1⟩⟩
      | Sum.inr ⟨σ, S⟩ => ⟨indMat n σ S.1, indMat_valid n σ S⟩
  have hbij : Function.Bijective f := by
    constructor
    · rintro (v1 | ⟨σ1, S1⟩) (v2 | ⟨σ2, S2⟩) h
      · have h00 := congrFun (congrFun (congrArg Subtype.val h) ⟨0, by omega⟩) ⟨0, by omega⟩
        simp only [f, checker, show Even (0 + 0) by decide, if_true] at h00
        exact congrArg Sum.inl (Subtype.ext h00)
      · exact False.elim (checker_ne_indMat hn v1 σ2 S2 (congrArg Subtype.val h))
      · exact False.elim (checker_ne_indMat hn v2 σ1 S1 (congrArg Subtype.val h).symm)
      · rcases indMat_inj hn (congrArg Subtype.val h) with ⟨rfl, rfl⟩
        rfl
    · rintro ⟨A, hA⟩
      rcases classify n hn A hA with ⟨v, hv1, hv2, hvn1, hvnm1, rfl⟩ | ⟨σ, S, rfl⟩
      · exact ⟨Sum.inl ⟨v, hv1, hv2, hvn1, hvnm1⟩, rfl⟩
      · exact ⟨Sum.inr ⟨σ, S⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hbij), Nat.card_eq_fintype_card,
      Fintype.card_sum, Fintype.card_prod, card_CheckVal, Fintype.card_bool, card_IndSet]

private lemma binet_fib (n : ℕ) :
    (2 * (Nat.fib (n + 3) : ℝ)) =
      ((2 : ℝ) ^ (1 - (n : ℤ)) *
        ((1 - Real.sqrt 5) ^ n * (-2 + Real.sqrt 5) +
         (1 + Real.sqrt 5) ^ n * (2 + Real.sqrt 5))) / Real.sqrt 5 := by
  have hs5 : Real.sqrt 5 ≠ 0 := by positivity
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [eq_div_iff hs5]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
      simp only [Nat.fib, Nat.cast_zero, sub_zero, zpow_one, pow_zero, one_mul]
      norm_num; ring
    | 1 =>
      have hfib4 : Nat.fib 4 = 3 := rfl
      simp only [hfib4, Nat.cast_one, sub_self, zpow_zero, pow_one, one_mul]
      push_cast; ring
    | k + 2 =>
      have h1 := ih (k + 1) (by omega)
      have h0 := ih k (by omega)
      have hfib_nat : Nat.fib (k + 2 + 3) = Nat.fib (k + 3) + Nat.fib (k + 1 + 3) := by
        simpa [add_assoc] using Nat.fib_add_two (n := k + 3)
      have hfib : (Nat.fib (k + 2 + 3) : ℝ) = (Nat.fib (k + 3) : ℝ) + (Nat.fib (k + 1 + 3) : ℝ) := by
        exact_mod_cast hfib_nat
      have hp1 : (2 : ℝ) ^ (1 - ((k + 2 : ℕ) : ℤ)) * 2 = (2 : ℝ) ^ (1 - ((k + 1 : ℕ) : ℤ)) := by
        rw [← zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0),
            show (1 - ((k + 2 : ℕ) : ℤ) + 1 : ℤ) = 1 - ((k + 1 : ℕ) : ℤ) by push_cast; ring]
      have hp0 : (2 : ℝ) ^ (1 - ((k + 2 : ℕ) : ℤ)) * 4 = (2 : ℝ) ^ (1 - (k : ℤ)) := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℤ) by norm_num,
            ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
            show (1 - ((k + 2 : ℕ) : ℤ) + 2 : ℤ) = 1 - (k : ℤ) by push_cast; ring]
      have hq1 : (1 - Real.sqrt 5) ^ (k + 2) =
          2 * (1 - Real.sqrt 5) ^ (k + 1) + 4 * (1 - Real.sqrt 5) ^ k := by
        have : (1 - Real.sqrt 5) ^ 2 = 2 * (1 - Real.sqrt 5) + 4 := by nlinarith [hsq]
        calc (1 - Real.sqrt 5) ^ (k + 2) = (1 - Real.sqrt 5) ^ k * (1 - Real.sqrt 5) ^ 2 := by ring
          _ = (1 - Real.sqrt 5) ^ k * (2 * (1 - Real.sqrt 5) + 4) := by rw [this]
          _ = 2 * (1 - Real.sqrt 5) ^ (k + 1) + 4 * (1 - Real.sqrt 5) ^ k := by ring
      have hq2 : (1 + Real.sqrt 5) ^ (k + 2) =
          2 * (1 + Real.sqrt 5) ^ (k + 1) + 4 * (1 + Real.sqrt 5) ^ k := by
        have : (1 + Real.sqrt 5) ^ 2 = 2 * (1 + Real.sqrt 5) + 4 := by nlinarith [hsq]
        calc (1 + Real.sqrt 5) ^ (k + 2) = (1 + Real.sqrt 5) ^ k * (1 + Real.sqrt 5) ^ 2 := by ring
          _ = (1 + Real.sqrt 5) ^ k * (2 * (1 + Real.sqrt 5) + 4) := by rw [this]
          _ = 2 * (1 + Real.sqrt 5) ^ (k + 1) + 4 * (1 + Real.sqrt 5) ^ k := by ring
      rw [hfib, hq1, hq2]
      calc 2 * ((Nat.fib (k + 3) : ℝ) + (Nat.fib (k + 1 + 3) : ℝ)) * Real.sqrt 5
          = 2 * (Nat.fib (k + 3) : ℝ) * Real.sqrt 5 + 2 * (Nat.fib (k + 1 + 3) : ℝ) * Real.sqrt 5 := by ring
        _ = (2 : ℝ) ^ (1 - (k : ℤ)) * ((1 - Real.sqrt 5) ^ k * (-2 + Real.sqrt 5) + (1 + Real.sqrt 5) ^ k * (2 + Real.sqrt 5)) +
            (2 : ℝ) ^ (1 - ((k + 1 : ℕ) : ℤ)) * ((1 - Real.sqrt 5) ^ (k + 1) * (-2 + Real.sqrt 5) + (1 + Real.sqrt 5) ^ (k + 1) * (2 + Real.sqrt 5)) := by
            rw [h0, h1]
        _ = (2 : ℝ) ^ (1 - ((k + 2 : ℕ) : ℤ)) * 4 * ((1 - Real.sqrt 5) ^ k * (-2 + Real.sqrt 5) + (1 + Real.sqrt 5) ^ k * (2 + Real.sqrt 5)) +
            (2 : ℝ) ^ (1 - ((k + 2 : ℕ) : ℤ)) * 2 * ((1 - Real.sqrt 5) ^ (k + 1) * (-2 + Real.sqrt 5) + (1 + Real.sqrt 5) ^ (k + 1) * (2 + Real.sqrt 5)) := by
            rw [hp0, hp1]
        _ = _ := by ring

private lemma coeff_X_pow_mul_eq (k : ℕ) (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X ^ k * f) =
      if k ≤ n then PowerSeries.coeff (n - k) f else 0 := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc]
    cases n with
    | zero => simp [PowerSeries.coeff_zero_X_mul]
    | succ m =>
      rw [PowerSeries.coeff_succ_X_mul, ih m]
      simp

private lemma main_proof :
    (PowerSeries.mk fun n => (a n : ℚ)) * ((1 - PowerSeries.X) * (1 - PowerSeries.X - PowerSeries.X ^ 2)) =
      PowerSeries.X * (13 - 9 * PowerSeries.X - 11 * PowerSeries.X ^ 2) ∧
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℝ) = 7 + ((2 : ℝ) ^ (1 - (n : ℤ)) *
        ((1 - Real.sqrt 5) ^ n * (-2 + Real.sqrt 5) +
         (1 + Real.sqrt 5) ^ n * (2 + Real.sqrt 5))) / Real.sqrt 5 := by
  constructor
  · set F : PowerSeries ℚ := PowerSeries.mk fun n => (a n : ℚ)
    have hlhs : F * ((1 - PowerSeries.X) * (1 - PowerSeries.X - PowerSeries.X ^ 2)) =
        F - PowerSeries.C (2 : ℚ) * (PowerSeries.X ^ 1 * F) + PowerSeries.X ^ 3 * F := by
      have h2 : PowerSeries.C (2 : ℚ) = (2 : PowerSeries ℚ) := rfl
      rw [h2, pow_one]; ring
    have hrhs : (PowerSeries.X * (13 - 9 * PowerSeries.X - 11 * PowerSeries.X ^ 2) : PowerSeries ℚ) =
        PowerSeries.C (13 : ℚ) * PowerSeries.X -
        PowerSeries.C (9 : ℚ) * PowerSeries.X ^ 2 -
        PowerSeries.C (11 : ℚ) * PowerSeries.X ^ 3 := by
      have h1 : PowerSeries.C (13 : ℚ) = (13 : PowerSeries ℚ) := rfl
      have h2 : PowerSeries.C (9 : ℚ) = (9 : PowerSeries ℚ) := rfl
      have h3 : PowerSeries.C (11 : ℚ) = (11 : PowerSeries ℚ) := rfl
      rw [h1, h2, h3]; ring
    rw [hlhs, hrhs]
    ext n
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq,
      PowerSeries.coeff_X_pow, PowerSeries.coeff_X]
    by_cases hn3 : n ≤ 3
    · have ha0 : a 0 = 0 := rfl
      have ha1 := a_eq 1 (by omega)
      have ha2 := a_eq 2 (by omega)
      have ha3 := a_eq 3 (by omega)
      interval_cases n
      · simp [F, ha0]
      · simp [F, ha0, ha1, Nat.fib]
      · simp [F, ha1, ha2, Nat.fib]; norm_num
      · simp [F, ha0, ha2, ha3, Nat.fib]; norm_num
    · have h0 := a_eq n (by omega)
      have h1 := a_eq (n - 1) (by omega)
      have h3 := a_eq (n - 3) (by omega)
      have hfib1 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
        simpa [show n + 3 = (n + 1) + 2 by omega] using Nat.fib_add_two (n := n + 1)
      have hfib2 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := by
        simpa [show n + 2 = n + 2 by omega] using Nat.fib_add_two (n := n)
      simp only [F, PowerSeries.coeff_mk, show n ≠ 1 by omega, show n ≠ 2 by omega,
        show n ≠ 3 by omega, show 1 ≤ n by omega, show 3 ≤ n by omega,
        ↓reduceIte, mul_zero, sub_zero, h0, h1, h3]
      have heq1 : n - 1 + 3 = n + 2 := by omega
      have heq3 : n - 3 + 3 = n := by omega
      rw [heq1, heq3]
      have hq1 : (Nat.fib (n + 3) : ℚ) = (Nat.fib (n + 1) : ℚ) + (Nat.fib (n + 2) : ℚ) := by
        exact_mod_cast hfib1
      have hq2 : (Nat.fib (n + 2) : ℚ) = (Nat.fib n : ℚ) + (Nat.fib (n + 1) : ℚ) := by
        exact_mod_cast hfib2
      push_cast; linarith
  · intro n hn
    rw [a_eq n hn]
    push_cast
    rw [binet_fib n]

end OMA.P_oeis_a211490

theorem OMA.solution : type_of% @OMA.S_oeis_a211490.main := OMA.P_oeis_a211490.main_proof
