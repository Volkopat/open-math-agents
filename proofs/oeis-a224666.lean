import OMAStatements.S_oeis_a224666

namespace OMA.P_oeis_a224666

open OMA.S_oeis_a224666

private lemma idempotent_spec {a b c d : ℕ} (h : isIdempotent2x2 a b c d) :
    a ≤ 1 ∧ d ≤ 1 ∧ b * c = 0 ∧ (b = 0 ∨ a + d = 1) ∧ (c = 0 ∨ a + d = 1) := by
  rcases h with ⟨ha, hb, hc, hd⟩
  have ha1 : a ≤ 1 := by nlinarith
  have hd1 : d ≤ 1 := by nlinarith
  have hbc : b * c = 0 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ha1 with rfl | rfl <;> omega
  have hb0 : b = 0 ∨ a + d = 1 := by
    by_cases hbn : b = 0
    · exact Or.inl hbn
    · right
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hbn) (by simpa using hb)
  have hc0 : c = 0 ∨ a + d = 1 := by
    by_cases hcn : c = 0
    · exact Or.inl hcn
    · right
      exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hcn) (by simpa using hc)
  exact ⟨ha1, hd1, hbc, hb0, hc0⟩

private lemma inner_le_one {n : ℕ} {A : Fin 4 → Fin 4 → Fin (n + 1)} (h : isValid n A)
    (i j : Fin 4) (h1 : ¬(i.1 = 0 ∧ j.1 = 3)) (h2 : ¬(i.1 = 3 ∧ j.1 = 0)) :
    (A i j).1 ≤ 1 := by
  by_cases hlt : i.1 < 3 ∧ j.1 < 3
  · have hsp := idempotent_spec (h ⟨i.1, hlt.1⟩ ⟨j.1, hlt.2⟩)
    exact hsp.1
  · have hpos : 0 < i.1 ∧ 0 < j.1 := by omega
    have hsp := idempotent_spec (h ⟨i.1 - 1, by omega⟩ ⟨j.1 - 1, by omega⟩)
    have hi : (⟨i.1 - 1, by omega⟩ : Fin 3).succ = i := Fin.ext (by simp; omega)
    have hj : (⟨j.1 - 1, by omega⟩ : Fin 3).succ = j := Fin.ext (by simp; omega)
    rw [hi, hj] at hsp
    exact hsp.2.1

private def b2n (b : Bool) : ℕ := if b then 1 else 0

private def bit (m : ℕ) (j : Fin 4) : Bool := decide ((m / 2 ^ j.1) % 2 = 1)

private def validBlock (a b c d : Bool) : Bool :=
  (a == d && !b && !c) || (a != d && (!b || !c))

private lemma validBlock_iff (a b c d : Bool) :
    validBlock a b c d = true ↔ isIdempotent2x2 (b2n a) (b2n b) (b2n c) (b2n d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp [validBlock, isIdempotent2x2, b2n]

private def adjRow (r0 r1 : Fin 16) : Bool :=
  (List.finRange 3).all fun j =>
    validBlock (bit r0.1 j.castSucc) (bit r0.1 j.succ) (bit r1.1 j.castSucc) (bit r1.1 j.succ)

private lemma adjRow_iff (r0 r1 : Fin 16) :
    adjRow r0 r1 = true ↔
      ∀ j : Fin 3,
        validBlock (bit r0.1 j.castSucc) (bit r0.1 j.succ) (bit r1.1 j.castSucc) (bit r1.1 j.succ) = true := by
  unfold adjRow
  rw [List.all_eq_true]
  constructor
  · intro h j; exact h j (List.mem_finRange j)
  · intro h j _; exact h j

private def trFree (r0 r1 : Fin 16) : Bool :=
  (bit r0.1 2 != bit r1.1 3) && !bit r1.1 2

private def blFree (r0 r1 : Fin 16) : Bool :=
  (bit r0.1 0 != bit r1.1 1) && !bit r0.1 1

private def isSkel (s : Fin 4 → Fin 16) : Bool :=
  !bit (s 0).1 3 && !bit (s 3).1 0 && adjRow (s 0) (s 1) && adjRow (s 1) (s 2) && adjRow (s 2) (s 3)

private lemma isSkel_iff (s : Fin 4 → Fin 16) :
    isSkel s = true ↔
      bit (s 0).1 3 = false ∧ bit (s 3).1 0 = false ∧
      ∀ i : Fin 3, adjRow (s i.castSucc) (s i.succ) = true := by
  unfold isSkel
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · tauto
    · tauto
    · intro i; fin_cases i <;> tauto
  · rintro ⟨h0, h1, ha⟩
    repeat' constructor
    all_goals first | exact h0 | exact h1 | exact ha 0 | exact ha 1 | exact ha 2

private def packRow (f : Fin 4 → Bool) : Fin 16 :=
  ⟨b2n (f 0) * 1 + b2n (f 1) * 2 + b2n (f 2) * 4 + b2n (f 3) * 8, by
    have h0 : b2n (f 0) ≤ 1 := by cases f 0 <;> simp [b2n]
    have h1 : b2n (f 1) ≤ 1 := by cases f 1 <;> simp [b2n]
    have h2 : b2n (f 2) ≤ 1 := by cases f 2 <;> simp [b2n]
    have h3 : b2n (f 3) ≤ 1 := by cases f 3 <;> simp [b2n]
    omega⟩

private lemma bit_sum (b0 b1 b2 b3 : ℕ) (h0 : b0 ≤ 1) (h1 : b1 ≤ 1) (h2 : b2 ≤ 1) (h3 : b3 ≤ 1) :
    ((b0 * 1 + b1 * 2 + b2 * 4 + b3 * 8) / 1) % 2 = b0 ∧ ((b0 * 1 + b1 * 2 + b2 * 4 + b3 * 8) / 2) % 2 = b1 ∧ ((b0 * 1 + b1 * 2 + b2 * 4 + b3 * 8) / 4) % 2 = b2 ∧ ((b0 * 1 + b1 * 2 + b2 * 4 + b3 * 8) / 8) % 2 = b3 := by
  omega

private lemma bit_packRow (f : Fin 4 → Bool) (j : Fin 4) :
    bit (packRow f).1 j = f j := by
  have h0 : b2n (f 0) ≤ 1 := by cases f 0 <;> simp [b2n]
  have h1 : b2n (f 1) ≤ 1 := by cases f 1 <;> simp [b2n]
  have h2 : b2n (f 2) ≤ 1 := by cases f 2 <;> simp [b2n]
  have h3 : b2n (f 3) ≤ 1 := by cases f 3 <;> simp [b2n]
  have hsum := bit_sum (b2n (f 0)) (b2n (f 1)) (b2n (f 2)) (b2n (f 3)) h0 h1 h2 h3
  fin_cases j
  · dsimp [bit, packRow]
    simp only [hsum.1]; cases f 0 <;> rfl
  · dsimp [bit, packRow]
    simp only [hsum.2.1]; cases f 1 <;> rfl
  · dsimp [bit, packRow]
    simp only [hsum.2.2.1]; cases f 2 <;> rfl
  · dsimp [bit, packRow]
    simp only [hsum.2.2.2]; cases f 3 <;> rfl

private lemma packRow_bit (r : Fin 16) : packRow (bit r.1) = r := by
  revert r; decide

private lemma tr_block_iff (a c d : Bool) (x : ℕ) :
    isIdempotent2x2 (b2n a) x (b2n c) (b2n d) ↔
      validBlock a false c d = true ∧ ((a != d && !c) = false → x = 0) := by
  constructor
  · intro h
    have hsp := idempotent_spec h
    cases a <;> cases c <;> cases d <;> simp [validBlock, b2n] at hsp ⊢ <;> omega
  · rintro ⟨hv, hx⟩
    cases a <;> cases c <;> cases d <;> simp [validBlock, b2n, isIdempotent2x2] at hv hx ⊢ <;> omega

private lemma bl_block_iff (a b d : Bool) (y : ℕ) :
    isIdempotent2x2 (b2n a) (b2n b) y (b2n d) ↔
      validBlock a b false d = true ∧ ((a != d && !b) = false → y = 0) := by
  constructor
  · intro h
    have hsp := idempotent_spec h
    cases a <;> cases b <;> cases d <;> simp [validBlock, b2n] at hsp ⊢ <;> omega
  · rintro ⟨hv, hy⟩
    cases a <;> cases b <;> cases d <;> simp [validBlock, b2n, isIdempotent2x2] at hv hy ⊢ <;> omega

private lemma b2n_decide_eq {x : ℕ} (hx : x ≤ 1) : b2n (decide (x = 1)) = x := by
  unfold b2n
  by_cases h : x = 1
  · simp [h]
  · simp [h]; omega

private def mkMat (n : ℕ) (hn : 1 ≤ n) (s : Fin 4 → Fin 16) (x y : Fin (n + 1)) :
    Fin 4 → Fin 4 → Fin (n + 1) := fun i j =>
  if i.1 = 0 ∧ j.1 = 3 then x
  else if i.1 = 3 ∧ j.1 = 0 then y
  else ⟨b2n (bit (s i).1 j), by
    have hb : b2n (bit (s i).1 j) ≤ 1 := by cases bit (s i).1 j <;> simp [b2n]
    omega⟩

private lemma mkMat_inner {n : ℕ} (hn : 1 ≤ n) (s : Fin 4 → Fin 16) (x y : Fin (n + 1))
    (i j : Fin 4) (h1 : ¬(i.1 = 0 ∧ j.1 = 3)) (h2 : ¬(i.1 = 3 ∧ j.1 = 0)) :
    (mkMat n hn s x y i j).1 = b2n (bit (s i).1 j) := by
  unfold mkMat
  rw [if_neg h1, if_neg h2]

private lemma mkMat_tr {n : ℕ} (hn : 1 ≤ n) (s : Fin 4 → Fin 16) (x y : Fin (n + 1)) :
    mkMat n hn s x y 0 3 = x := by
  unfold mkMat; rw [if_pos ⟨rfl, rfl⟩]

private lemma mkMat_bl {n : ℕ} (hn : 1 ≤ n) (s : Fin 4 → Fin 16) (x y : Fin (n + 1)) :
    mkMat n hn s x y 3 0 = y := by
  unfold mkMat; rw [if_neg (by decide), if_pos ⟨rfl, rfl⟩]

private def FlatValid (n : ℕ) :=
  {p : (Fin 4 → Fin 16) × Fin (n + 1) × Fin (n + 1) //
    isSkel p.1 = true ∧
    (trFree (p.1 0) (p.1 1) = false → p.2.1.1 = 0) ∧
    (blFree (p.1 2) (p.1 3) = false → p.2.2.1 = 0)}

private instance (n : ℕ) : Fintype (FlatValid n) := by
  unfold FlatValid; infer_instance

private def validFlatEquiv (n : ℕ) (hn : 1 ≤ n) :
    {A : Fin 4 → Fin 4 → Fin (n + 1) // isValid n A} ≃ FlatValid n where
  toFun A :=
    let s : Fin 4 → Fin 16 := fun i =>
      packRow fun j =>
        if (i.1 = 0 ∧ j.1 = 3) ∨ (i.1 = 3 ∧ j.1 = 0) then false
        else decide ((A.1 i j).1 = 1)
    have hs_bit : ∀ i j : Fin 4,
        bit (s i).1 j =
          if (i.1 = 0 ∧ j.1 = 3) ∨ (i.1 = 3 ∧ j.1 = 0) then false
          else decide ((A.1 i j).1 = 1) := fun i j => bit_packRow _ j
    have hs_inner : ∀ i j : Fin 4,
        ¬(i.1 = 0 ∧ j.1 = 3) → ¬(i.1 = 3 ∧ j.1 = 0) →
        b2n (bit (s i).1 j) = (A.1 i j).1 := by
      intro i j h1 h2
      rw [hs_bit i j, if_neg (by tauto)]
      exact b2n_decide_eq (inner_le_one A.2 i j h1 h2)
    have hs_valid : isSkel s = true := by
      rw [isSkel_iff]
      refine ⟨by rw [hs_bit]; simp, by rw [hs_bit]; simp, fun i => ?_⟩
      rw [adjRow_iff]; intro j
      have hblk := A.2 i j
      by_cases htr : i.1 = 0 ∧ j.1 = 2
      · have h0 : i.castSucc = 0 := Fin.ext htr.1
        have h1 : i.succ = 1 := Fin.ext (by simp [htr.1])
        have hj0 : j.castSucc = 2 := Fin.ext htr.2
        have hj1 : j.succ = 3 := Fin.ext (by simp [htr.2])
        rw [h0, h1, hj0, hj1] at hblk ⊢
        rw [← hs_inner 0 2 (by decide) (by decide),
            ← hs_inner 1 2 (by decide) (by decide),
            ← hs_inner 1 3 (by decide) (by decide)] at hblk
        have htr0 : bit (s 0).1 3 = false := by rw [hs_bit]; simp
        rw [htr0]
        exact (tr_block_iff _ _ _ _).mp hblk |>.1
      · by_cases hbl : i.1 = 2 ∧ j.1 = 0
        · have h0 : i.castSucc = 2 := Fin.ext hbl.1
          have h1 : i.succ = 3 := Fin.ext (by simp [hbl.1])
          have hj0 : j.castSucc = 0 := Fin.ext hbl.2
          have hj1 : j.succ = 1 := Fin.ext (by simp [hbl.2])
          rw [h0, h1, hj0, hj1] at hblk ⊢
          rw [← hs_inner 2 0 (by decide) (by decide),
              ← hs_inner 2 1 (by decide) (by decide),
              ← hs_inner 3 1 (by decide) (by decide)] at hblk
          have hbl0 : bit (s 3).1 0 = false := by rw [hs_bit]; simp
          rw [hbl0]
          exact (bl_block_iff _ _ _ _).mp hblk |>.1
        · rw [validBlock_iff,
              hs_inner i.castSucc j.castSucc (by rintro ⟨_, h⟩; exact absurd h (by have := j.2; simp; omega)) (by rintro ⟨h, _⟩; exact absurd h (by have := i.2; simp; omega)),
              hs_inner i.castSucc j.succ (by rintro ⟨h1, h2⟩; apply htr; exact ⟨by simpa using h1, by simp at h2; omega⟩) (by rintro ⟨h, _⟩; exact absurd h (by have := i.2; simp; omega)),
              hs_inner i.succ j.castSucc (by rintro ⟨h, _⟩; simp at h) (by rintro ⟨h1, h2⟩; apply hbl; exact ⟨by simp at h1; omega, by simpa using h2⟩),
              hs_inner i.succ j.succ (by rintro ⟨h, _⟩; simp at h) (by rintro ⟨_, h⟩; simp at h)]
          exact hblk
    have hx_valid : trFree (s 0) (s 1) = false → (A.1 0 3).1 = 0 := by
      have hblk := A.2 0 2
      have h0 : (0 : Fin 3).castSucc = 0 := rfl
      have h1 : (0 : Fin 3).succ = 1 := rfl
      have hj0 : (2 : Fin 3).castSucc = 2 := rfl
      have hj1 : (2 : Fin 3).succ = 3 := rfl
      rw [h0, h1, hj0, hj1] at hblk
      rw [← hs_inner 0 2 (by decide) (by decide),
          ← hs_inner 1 2 (by decide) (by decide),
          ← hs_inner 1 3 (by decide) (by decide)] at hblk
      exact (tr_block_iff _ _ _ _).mp hblk |>.2
    have hy_valid : blFree (s 2) (s 3) = false → (A.1 3 0).1 = 0 := by
      have hblk := A.2 2 0
      have h0 : (2 : Fin 3).castSucc = 2 := rfl
      have h1 : (2 : Fin 3).succ = 3 := rfl
      have hj0 : (0 : Fin 3).castSucc = 0 := rfl
      have hj1 : (0 : Fin 3).succ = 1 := rfl
      rw [h0, h1, hj0, hj1] at hblk
      rw [← hs_inner 2 0 (by decide) (by decide),
          ← hs_inner 2 1 (by decide) (by decide),
          ← hs_inner 3 1 (by decide) (by decide)] at hblk
      exact (bl_block_iff _ _ _ _).mp hblk |>.2
    ⟨(s, A.1 0 3, A.1 3 0), hs_valid, hx_valid, hy_valid⟩
  invFun := fun ⟨(s, x, y), hs, hx, hy⟩ =>
    have hsk := (isSkel_iff s).mp hs
    have hA_val : isValid n (mkMat n hn s x y) := by
      intro i j
      have hadj := (adjRow_iff (s i.castSucc) (s i.succ)).mp (hsk.2.2 i) j
      by_cases htr : i.1 = 0 ∧ j.1 = 2
      · have h0 : i.castSucc = 0 := Fin.ext htr.1
        have h1 : i.succ = 1 := Fin.ext (by simp [htr.1])
        have hj0 : j.castSucc = 2 := Fin.ext htr.2
        have hj1 : j.succ = 3 := Fin.ext (by simp [htr.2])
        rw [h0, h1, hj0, hj1] at hadj ⊢
        rw [hsk.1] at hadj
        rw [mkMat_tr,
            mkMat_inner hn s x y 0 2 (by decide) (by decide),
            mkMat_inner hn s x y 1 2 (by decide) (by decide),
            mkMat_inner hn s x y 1 3 (by decide) (by decide)]
        exact (tr_block_iff _ _ _ _).mpr ⟨hadj, hx⟩
      · by_cases hbl : i.1 = 2 ∧ j.1 = 0
        · have h0 : i.castSucc = 2 := Fin.ext hbl.1
          have h1 : i.succ = 3 := Fin.ext (by simp [hbl.1])
          have hj0 : j.castSucc = 0 := Fin.ext hbl.2
          have hj1 : j.succ = 1 := Fin.ext (by simp [hbl.2])
          rw [h0, h1, hj0, hj1] at hadj ⊢
          rw [hsk.2.1] at hadj
          rw [mkMat_bl,
              mkMat_inner hn s x y 2 0 (by decide) (by decide),
              mkMat_inner hn s x y 2 1 (by decide) (by decide),
              mkMat_inner hn s x y 3 1 (by decide) (by decide)]
          exact (bl_block_iff _ _ _ _).mpr ⟨hadj, hy⟩
        · rw [mkMat_inner hn s x y i.castSucc j.castSucc (by rintro ⟨_, h⟩; exact absurd h (by have := j.2; simp; omega)) (by rintro ⟨h, _⟩; exact absurd h (by have := i.2; simp; omega)),
              mkMat_inner hn s x y i.castSucc j.succ (by rintro ⟨h1, h2⟩; apply htr; exact ⟨by simpa using h1, by simp at h2; omega⟩) (by rintro ⟨h, _⟩; exact absurd h (by have := i.2; simp; omega)),
              mkMat_inner hn s x y i.succ j.castSucc (by rintro ⟨h, _⟩; simp at h) (by rintro ⟨h1, h2⟩; apply hbl; exact ⟨by simp at h1; omega, by simpa using h2⟩),
              mkMat_inner hn s x y i.succ j.succ (by rintro ⟨h, _⟩; simp at h) (by rintro ⟨_, h⟩; simp at h)]
          exact (validBlock_iff _ _ _ _).mp hadj
    ⟨mkMat n hn s x y, hA_val⟩
  left_inv := by
    intro ⟨A, hA⟩
    apply Subtype.ext; funext i j
    by_cases h1 : i.1 = 0 ∧ j.1 = 3
    · have hi : i = 0 := Fin.ext h1.1
      have hj : j = 3 := Fin.ext h1.2
      subst hi; subst hj; simp [mkMat]
    · by_cases h2 : i.1 = 3 ∧ j.1 = 0
      · have hi : i = 3 := Fin.ext h2.1
        have hj : j = 0 := Fin.ext h2.2
        subst hi; subst hj; simp [mkMat]
      · apply Fin.ext
        rw [mkMat_inner hn _ _ _ i j h1 h2, bit_packRow, if_neg (by tauto)]
        exact b2n_decide_eq (inner_le_one hA i j h1 h2)
  right_inv := by
    rintro ⟨⟨s, x, y⟩, hs, hx, hy⟩
    have hsk := (isSkel_iff s).mp hs
    apply Subtype.ext
    refine Prod.ext ?_ (Prod.ext (mkMat_tr hn s x y) (mkMat_bl hn s x y))
    funext i
    dsimp only
    conv_rhs => rw [← packRow_bit (s i)]
    congr 1; funext j
    by_cases h1 : i.1 = 0 ∧ j.1 = 3
    · have hi : i = 0 := Fin.ext h1.1
      have hj : j = 3 := Fin.ext h1.2
      subst hi; subst hj; simp [hsk.1]
    · by_cases h2 : i.1 = 3 ∧ j.1 = 0
      · have hi : i = 3 := Fin.ext h2.1
        have hj : j = 0 := Fin.ext h2.2
        subst hi; subst hj; simp [hsk.2.1]
      · have hne : ¬((i.1 = 0 ∧ j.1 = 3) ∨ (i.1 = 3 ∧ j.1 = 0)) := by tauto
        have hin := mkMat_inner hn s x y i j h1 h2
        simp only [hne, if_false, hin]
        cases bit (s i).1 j <;> simp [b2n]

private def flatSigmaEquiv (n : ℕ) :
    FlatValid n ≃
      Σ s : {s : Fin 4 → Fin 16 // isSkel s = true},
        {x : Fin (n + 1) // trFree (s.1 0) (s.1 1) = false → x.1 = 0} ×
        {y : Fin (n + 1) // blFree (s.1 2) (s.1 3) = false → y.1 = 0} where
  toFun p := ⟨⟨p.1.1, p.2.1⟩, ⟨p.1.2.1, p.2.2.1⟩, ⟨p.1.2.2, p.2.2.2⟩⟩
  invFun q := ⟨(q.1.1, q.2.1.1, q.2.2.1), q.1.2, q.2.1.2, q.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma card_fiber_bool (n : ℕ) (b : Bool) :
    Fintype.card {x : Fin (n + 1) // b = false → x.1 = 0} = if b then n + 1 else 1 := by
  cases b
  · simp only [Bool.false_eq_true, if_false]
    have h : Fintype.card {x : Fin (n + 1) // True → x.1 = 0} =
        Fintype.card (Fin 1) := by
      refine Fintype.card_congr ⟨fun _ => 0, fun _ => ⟨0, fun _ => rfl⟩, ?_, ?_⟩
      · rintro ⟨x, hx⟩; exact Subtype.ext (Fin.ext (hx trivial).symm)
      · intro i; fin_cases i; rfl
    rw [h, Fintype.card_fin]
  · simp only [if_true]
    have h : Fintype.card {x : Fin (n + 1) // Bool.true = false → x.1 = 0} =
        Fintype.card (Fin (n + 1)) := by
      refine Fintype.card_congr ⟨fun x => x.1, fun x => ⟨x, by simp⟩, fun _ => rfl, fun _ => rfl⟩
    rw [h, Fintype.card_fin]

private def w1 (r1 : Fin 16) (ft : Bool) : ℕ :=
  ((List.finRange 16).map fun r0 =>
    if !bit r0.1 3 && adjRow r0 r1 && (trFree r0 r1 == ft) then 1 else 0).sum
private def w2 (r : Fin 16) (ft : Bool) : ℕ :=
  ((List.finRange 16).map fun r0 =>
    if adjRow r0 r then w1 r0 ft else 0).sum
private def blCount (r0 : Fin 16) (fb : Bool) : ℕ :=
  ((List.finRange 16).map fun r1 =>
    if !bit r1.1 0 && adjRow r0 r1 && (blFree r0 r1 == fb) then 1 else 0).sum
private def wFinal (ft fb : Bool) : ℕ :=
  ((List.finRange 16).map fun r0 => w2 r0 ft * blCount r0 fb).sum

private def w1Tbl (r : Fin 16) (ft : Bool) : ℕ :=
  if ft then
    match r.1 with
    | 0 => 1
    | 8 => 3
    | 9 => 1
    | 10 => 1
    | _ => 0
  else
    match r.1 with
    | 0 => 3
    | 1 => 1
    | 2 => 1
    | 4 => 2
    | 5 => 1
    | 8 => 1
    | 12 => 3
    | 13 => 1
    | 14 => 2
    | 15 => 1
    | _ => 0
private def w2Tbl (r : Fin 16) (ft : Bool) : ℕ :=
  if ft then
    match r.1 with
    | 0 => 1
    | 8 => 5
    | 9 => 1
    | 10 => 1
    | 12 => 1
    | 14 => 1
    | 15 => 1
    | _ => 0
  else
    match r.1 with
    | 0 => 5
    | 1 => 1
    | 2 => 1
    | 4 => 3
    | 5 => 1
    | 8 => 5
    | 9 => 1
    | 10 => 1
    | 12 => 4
    | 13 => 1
    | 14 => 4
    | 15 => 3
    | _ => 0
private def blCountTbl (r0 : Fin 16) (fb : Bool) : ℕ :=
  if fb then
    match r0.1 with
    | 0 => 1
    | 1 => 3
    | 5 => 1
    | 9 => 1
    | _ => 0
  else
    match r0.1 with
    | 0 => 3
    | 1 => 1
    | 2 => 2
    | 3 => 3
    | 4 => 1
    | 7 => 2
    | 8 => 1
    | 10 => 1
    | 11 => 1
    | 15 => 1
    | _ => 0

private lemma w1_eq_tbl : ∀ r : Fin 16, ∀ ft : Bool, w1 r ft = w1Tbl r ft := by decide
private lemma w2_eq_tbl : ∀ r : Fin 16, ∀ ft : Bool, w2 r ft = w2Tbl r ft := by
  intro r ft; unfold w2
  have h : (fun r0 : Fin 16 => if adjRow r0 r then w1 r0 ft else 0) =
           (fun r0 : Fin 16 => if adjRow r0 r then w1Tbl r0 ft else 0) := by
    funext r0; rw [w1_eq_tbl]
  rw [h]; revert r ft; decide
private lemma blCount_eq_tbl : ∀ r0 : Fin 16, ∀ fb : Bool, blCount r0 fb = blCountTbl r0 fb := by decide
private lemma wFinal_vals :
    wFinal false false = 30 ∧ wFinal false true = 10 ∧
    wFinal true false = 10 ∧ wFinal true true = 2 := by
  have h : ∀ ft fb : Bool, wFinal ft fb = ((List.finRange 16).map fun r0 => w2Tbl r0 ft * blCountTbl r0 fb).sum := by
    intro ft fb; unfold wFinal
    have hfun : (fun r0 : Fin 16 => w2 r0 ft * blCount r0 fb) =
                (fun r0 : Fin 16 => w2Tbl r0 ft * blCountTbl r0 fb) := by
      funext r0; rw [w2_eq_tbl, blCount_eq_tbl]
    rw [hfun]
  simp only [h]; decide

private lemma sum_fin_eq_list {M : ℕ} (f : Fin M → ℕ) :
    (∑ i : Fin M, f i) = ((List.finRange M).map f).sum := by
  rw [Fin.sum_univ_def]

private lemma sum_if_and_const {α : Type*} [Fintype α] (P : Bool) (Q : α → Bool) (f : α → ℕ) :
    (∑ x : α, if (P && Q x) = true then f x else 0) =
      if P = true then ∑ x : α, if Q x = true then f x else 0 else 0 := by
  cases P <;> simp

private lemma sum_skel_eq_wFinal (ft fb : Bool) :
    (∑ s : Fin 4 → Fin 16,
      if (isSkel s && (trFree (s 0) (s 1) == ft) && (blFree (s 2) (s 3) == fb)) = true
      then 1 else 0) = wFinal ft fb := by
  let e : (Fin 4 → Fin 16) ≃ Fin 16 × Fin 16 × Fin 16 × Fin 16 :=
    { toFun := fun s => (s 3, s 2, s 1, s 0)
      invFun := fun (r3, r2, r1, r0) i => match i.1 with
      | 0 => r0
      | 1 => r1
      | 2 => r2
      | 3 => r3
      | _ => r0
      left_inv := fun s => by funext i; fin_cases i <;> rfl
      right_inv := fun (r3, r2, r1, r0) => rfl }
  trans (∑ p : Fin 16 × Fin 16 × Fin 16 × Fin 16,
    (fun (r3, r2, r1, r0) =>
      if (!bit r0.1 3 && !bit r3.1 0 && adjRow r0 r1 && adjRow r1 r2 && adjRow r2 r3 &&
        (trFree r0 r1 == ft) && (blFree r2 r3 == fb)) = true then 1 else 0) p)
  · exact Fintype.sum_equiv e _ _ (fun s => rfl)
  simp only [Fintype.sum_prod_type]
  have h1 : ∀ r3 r2 r1 : Fin 16,
      (∑ r0 : Fin 16, if (!bit r0.1 3 && !bit r3.1 0 && adjRow r0 r1 && adjRow r1 r2 && adjRow r2 r3 &&
        (trFree r0 r1 == ft) && (blFree r2 r3 == fb)) = true then 1 else 0) =
      if ((!bit r3.1 0 && adjRow r2 r3 && (blFree r2 r3 == fb)) && adjRow r1 r2) = true then w1 r1 ft else 0 := by
    intro r3 r2 r1
    trans (∑ r0 : Fin 16, if (((!bit r3.1 0 && adjRow r2 r3 && (blFree r2 r3 == fb)) && adjRow r1 r2) &&
      (!bit r0.1 3 && adjRow r0 r1 && (trFree r0 r1 == ft))) = true then 1 else 0)
    · congr 1; funext r0; congr 1; simp only [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
    · rw [sum_if_and_const, sum_fin_eq_list]; rfl
  have h2 : ∀ r3 r2 : Fin 16,
      (∑ r1 : Fin 16, if ((!bit r3.1 0 && adjRow r2 r3 && (blFree r2 r3 == fb)) && adjRow r1 r2) = true then w1 r1 ft else 0) =
      if (!bit r3.1 0 && adjRow r2 r3 && (blFree r2 r3 == fb)) = true then w2 r2 ft else 0 := by
    intro r3 r2
    rw [sum_if_and_const, sum_fin_eq_list]; rfl
  simp only [h1, h2]
  rw [Finset.sum_comm, sum_fin_eq_list]
  unfold wFinal
  have hfun : (fun r2 : Fin 16 => ∑ r3 : Fin 16, if (!bit r3.1 0 && adjRow r2 r3 && (blFree r2 r3 == fb)) = true then w2 r2 ft else 0) =
              (fun r2 : Fin 16 => w2 r2 ft * blCount r2 fb) := by
    funext r2
    have hmul : (∑ r3 : Fin 16, if (!bit r3.1 0 && adjRow r2 r3 && (blFree r2 r3 == fb)) = true then w2 r2 ft else 0) =
        w2 r2 ft * ∑ r3 : Fin 16, if (!bit r3.1 0 && adjRow r2 r3 && (blFree r2 r3 == fb)) = true then 1 else 0 := by
      rw [Finset.mul_sum]; congr 1; funext r3; split_ifs <;> simp
    rw [hmul, sum_fin_eq_list]; rfl
  rw [hfun]

private lemma card_formula (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card {A : Fin 4 → Fin 4 → Fin (n + 1) // isValid n A} =
      2 * n ^ 2 + 24 * n + 52 := by
  rw [Fintype.card_congr ((validFlatEquiv n hn).trans (flatSigmaEquiv n)), Fintype.card_sigma]
  simp only [Fintype.card_prod, card_fiber_bool]
  have hsub : (∑ s : {s : Fin 4 → Fin 16 // isSkel s = true},
      (if trFree (s.1 0) (s.1 1) = true then n + 1 else 1) *
      (if blFree (s.1 2) (s.1 3) = true then n + 1 else 1)) =
    ∑ s : Fin 4 → Fin 16,
      if isSkel s = true then
        (if trFree (s 0) (s 1) = true then n + 1 else 1) *
        (if blFree (s 2) (s 3) = true then n + 1 else 1)
      else 0 := by
    let g : (Fin 4 → Fin 16) → ℕ := fun s =>
      (if trFree (s 0) (s 1) = true then n + 1 else 1) *
      (if blFree (s 2) (s 3) = true then n + 1 else 1)
    have h1 : (∑ s ∈ Finset.univ.filter (fun s : Fin 4 → Fin 16 => isSkel s = true), g s) =
        ∑ s : {s : Fin 4 → Fin 16 // isSkel s = true}, g s.1 :=
      Finset.sum_subtype (Finset.univ.filter fun s : Fin 4 → Fin 16 => isSkel s = true) (by intro s; simp) g
    exact h1.symm.trans (Finset.sum_filter _ _)
  rw [hsub]
  have hsplit : ∀ s : Fin 4 → Fin 16,
      (if isSkel s = true then
        (if trFree (s 0) (s 1) = true then n + 1 else 1) *
        (if blFree (s 2) (s 3) = true then n + 1 else 1)
       else 0) =
      (if (isSkel s && (trFree (s 0) (s 1) == false) && (blFree (s 2) (s 3) == false)) = true then 1 else 0) +
      (if (isSkel s && (trFree (s 0) (s 1) == false) && (blFree (s 2) (s 3) == true)) = true then 1 else 0) * (n + 1) +
      (if (isSkel s && (trFree (s 0) (s 1) == true) && (blFree (s 2) (s 3) == false)) = true then 1 else 0) * (n + 1) +
      (if (isSkel s && (trFree (s 0) (s 1) == true) && (blFree (s 2) (s 3) == true)) = true then 1 else 0) * ((n + 1) * (n + 1)) := by
    intro s
    cases isSkel s <;> cases trFree (s 0) (s 1) <;> cases blFree (s 2) (s 3) <;> simp
  simp only [hsplit, Finset.sum_add_distrib, ← Finset.sum_mul, sum_skel_eq_wFinal]
  rcases wFinal_vals with ⟨h00, h01, h10, h11⟩
  rw [h00, h01, h10, h11]
  ring

private lemma a_eq (n : ℕ) (hn : 1 ≤ n) :
    a n = 2 * n ^ 2 + 24 * n + 52 := by
  unfold a
  rw [if_neg (by omega)]
  exact card_formula n hn

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
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 3 =
      2 * PowerSeries.X * (39 - 63 * PowerSeries.X + 26 * PowerSeries.X ^ 2) ∧
    ∀ n : ℕ, 3 < n →
      (a n : ℤ) = 3 * (a (n - 1) : ℤ) - 3 * (a (n - 2) : ℤ) + (a (n - 3) : ℤ) := by
  constructor
  · set F : PowerSeries ℚ := PowerSeries.mk fun n => (a n : ℚ)
    have hlhs : F * (1 - PowerSeries.X) ^ 3 =
        F - PowerSeries.C (3 : ℚ) * (PowerSeries.X ^ 1 * F) +
        PowerSeries.C (3 : ℚ) * (PowerSeries.X ^ 2 * F) -
        PowerSeries.X ^ 3 * F := by
      have h3 : PowerSeries.C (3 : ℚ) = (3 : PowerSeries ℚ) := rfl
      rw [h3, pow_one]; ring
    have hrhs : (2 * PowerSeries.X * (39 - 63 * PowerSeries.X + 26 * PowerSeries.X ^ 2) : PowerSeries ℚ) =
        PowerSeries.C (78 : ℚ) * PowerSeries.X -
        PowerSeries.C (126 : ℚ) * PowerSeries.X ^ 2 +
        PowerSeries.C (52 : ℚ) * PowerSeries.X ^ 3 := by
      have h1 : PowerSeries.C (78 : ℚ) = (78 : PowerSeries ℚ) := rfl
      have h2 : PowerSeries.C (126 : ℚ) = (126 : PowerSeries ℚ) := rfl
      have h3 : PowerSeries.C (52 : ℚ) = (52 : PowerSeries ℚ) := rfl
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
      · simp [F, ha0, ha1]
      · simp [F, ha0, ha1, ha2]; norm_num
      · simp [F, ha0, ha1, ha2, ha3]; norm_num
    · have h0 := a_eq n (by omega)
      have h1 := a_eq (n - 1) (by omega)
      have h2 := a_eq (n - 2) (by omega)
      have h3 := a_eq (n - 3) (by omega)
      simp only [F, PowerSeries.coeff_mk, show n ≠ 1 by omega, show n ≠ 2 by omega,
        show n ≠ 3 by omega, show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
        ↓reduceIte, mul_zero, sub_zero, add_zero, h0, h1, h2, h3]
      have hm1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      have hm2 : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := by
        rw [Nat.cast_sub (by omega)]; simp
      have hm3 : ((n - 3 : ℕ) : ℚ) = (n : ℚ) - 3 := by
        rw [Nat.cast_sub (by omega)]; simp
      push_cast [hm1, hm2, hm3]; ring
  · intro n hn
    have h0 := a_eq n (by omega)
    have h1 := a_eq (n - 1) (by omega)
    have h2 := a_eq (n - 2) (by omega)
    have h3 := a_eq (n - 3) (by omega)
    rw [h0, h1, h2, h3]
    have hm1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    have hm2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
    have hm3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := by omega
    push_cast [hm1, hm2, hm3]; ring

end OMA.P_oeis_a224666

theorem OMA.solution : type_of% @OMA.S_oeis_a224666.main := OMA.P_oeis_a224666.main_proof
