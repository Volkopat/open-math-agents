import OMAStatements.S_oeis_a224673

namespace OMA.P_oeis_a224673

open OMA.S_oeis_a224673

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

private lemma inner_le_one {n : ℕ} (hn : 1 ≤ n) {A : Fin (n + 1) → Fin 6 → Fin 3} (h : isValid n A)
    (i : Fin (n + 1)) (j : Fin 6) (h1 : ¬(i.1 = 0 ∧ j.1 = 5)) (h2 : ¬(i.1 = n ∧ j.1 = 0)) :
    (A i j).1 ≤ 1 := by
  by_cases hlt : i.1 < n ∧ j.1 < 5
  · have hsp := idempotent_spec (h ⟨i.1, hlt.1⟩ ⟨j.1, hlt.2⟩)
    exact hsp.1
  · have hpos : 0 < i.1 ∧ 0 < j.1 := by omega
    have hsp := idempotent_spec (h ⟨i.1 - 1, by omega⟩ ⟨j.1 - 1, by omega⟩)
    have hi : (⟨i.1 - 1, by omega⟩ : Fin n).succ = i := Fin.ext (by simp; omega)
    have hj : (⟨j.1 - 1, by omega⟩ : Fin 5).succ = j := Fin.ext (by simp; omega)
    rw [hi, hj] at hsp
    exact hsp.2.1

private def b2n (b : Bool) : ℕ := if b then 1 else 0

private def bit (m : ℕ) (j : Fin 6) : Bool := decide ((m / 2 ^ j.1) % 2 = 1)

private def validBlock (a b c d : Bool) : Bool :=
  (a == d && !b && !c) || (a != d && (!b || !c))

private lemma validBlock_iff (a b c d : Bool) :
    validBlock a b c d = true ↔ isIdempotent2x2 (b2n a) (b2n b) (b2n c) (b2n d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp [validBlock, isIdempotent2x2, b2n]

private def adjRow (r0 r1 : Fin 64) : Bool :=
  (List.finRange 5).all fun j =>
    validBlock (bit r0.1 j.castSucc) (bit r0.1 j.succ) (bit r1.1 j.castSucc) (bit r1.1 j.succ)

private lemma adjRow_iff (r0 r1 : Fin 64) :
    adjRow r0 r1 = true ↔
      ∀ j : Fin 5,
        validBlock (bit r0.1 j.castSucc) (bit r0.1 j.succ) (bit r1.1 j.castSucc) (bit r1.1 j.succ) = true := by
  unfold adjRow
  rw [List.all_eq_true]
  constructor
  · intro h j; exact h j (List.mem_finRange j)
  · intro h j _; exact h j

private def trFree (r0 r1 : Fin 64) : Bool :=
  (bit r0.1 4 != bit r1.1 5) && !bit r1.1 4

private def blFree (r0 r1 : Fin 64) : Bool :=
  (bit r0.1 0 != bit r1.1 1) && !bit r0.1 1

private def packRow (f : Fin 6 → Bool) : Fin 64 :=
  ⟨b2n (f 0) * 1 + b2n (f 1) * 2 + b2n (f 2) * 4 + b2n (f 3) * 8 + b2n (f 4) * 16 + b2n (f 5) * 32, by
    have h0 : b2n (f 0) ≤ 1 := by cases f 0 <;> simp [b2n]
    have h1 : b2n (f 1) ≤ 1 := by cases f 1 <;> simp [b2n]
    have h2 : b2n (f 2) ≤ 1 := by cases f 2 <;> simp [b2n]
    have h3 : b2n (f 3) ≤ 1 := by cases f 3 <;> simp [b2n]
    have h4 : b2n (f 4) ≤ 1 := by cases f 4 <;> simp [b2n]
    have h5 : b2n (f 5) ≤ 1 := by cases f 5 <;> simp [b2n]
    omega⟩

private lemma bit_sum (b0 b1 b2 b3 b4 b5 : ℕ) (h0 : b0 ≤ 1) (h1 : b1 ≤ 1) (h2 : b2 ≤ 1)
    (h3 : b3 ≤ 1) (h4 : b4 ≤ 1) (h5 : b5 ≤ 1) :
    ((b0 * 1 + b1 * 2 + b2 * 4 + b3 * 8 + b4 * 16 + b5 * 32) / 1) % 2 = b0 ∧
    ((b0 * 1 + b1 * 2 + b2 * 4 + b3 * 8 + b4 * 16 + b5 * 32) / 2) % 2 = b1 ∧
    ((b0 * 1 + b1 * 2 + b2 * 4 + b3 * 8 + b4 * 16 + b5 * 32) / 4) % 2 = b2 ∧
    ((b0 * 1 + b1 * 2 + b2 * 4 + b3 * 8 + b4 * 16 + b5 * 32) / 8) % 2 = b3 ∧
    ((b0 * 1 + b1 * 2 + b2 * 4 + b3 * 8 + b4 * 16 + b5 * 32) / 16) % 2 = b4 ∧
    ((b0 * 1 + b1 * 2 + b2 * 4 + b3 * 8 + b4 * 16 + b5 * 32) / 32) % 2 = b5 := by
  omega

private lemma bit_packRow (f : Fin 6 → Bool) (j : Fin 6) :
    bit (packRow f).1 j = f j := by
  have h0 : b2n (f 0) ≤ 1 := by cases f 0 <;> simp [b2n]
  have h1 : b2n (f 1) ≤ 1 := by cases f 1 <;> simp [b2n]
  have h2 : b2n (f 2) ≤ 1 := by cases f 2 <;> simp [b2n]
  have h3 : b2n (f 3) ≤ 1 := by cases f 3 <;> simp [b2n]
  have h4 : b2n (f 4) ≤ 1 := by cases f 4 <;> simp [b2n]
  have h5 : b2n (f 5) ≤ 1 := by cases f 5 <;> simp [b2n]
  have hsum := bit_sum (b2n (f 0)) (b2n (f 1)) (b2n (f 2)) (b2n (f 3)) (b2n (f 4)) (b2n (f 5)) h0 h1 h2 h3 h4 h5
  fin_cases j
  · dsimp [bit, packRow]; simp only [hsum.1]; cases f 0 <;> rfl
  · dsimp [bit, packRow]; simp only [hsum.2.1]; cases f 1 <;> rfl
  · dsimp [bit, packRow]; simp only [hsum.2.2.1]; cases f 2 <;> rfl
  · dsimp [bit, packRow]; simp only [hsum.2.2.2.1]; cases f 3 <;> rfl
  · dsimp [bit, packRow]; simp only [hsum.2.2.2.2.1]; cases f 4 <;> rfl
  · dsimp [bit, packRow]; simp only [hsum.2.2.2.2.2]; cases f 5 <;> rfl

private lemma packRow_bit (r : Fin 64) : packRow (bit r.1) = r := by
  fin_cases r <;> rfl

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

private def isSkel (n : ℕ) (s : Fin (n + 1) → Fin 64) : Prop :=
  bit (s 0).1 5 = false ∧ bit (s (Fin.last n)).1 0 = false ∧
  ∀ i : Fin n, adjRow (s i.castSucc) (s i.succ) = true

private instance (n : ℕ) (s : Fin (n + 1) → Fin 64) : Decidable (isSkel n s) := by
  unfold isSkel; infer_instance

private def mkMat (n : ℕ) (s : Fin (n + 1) → Fin 64) (x y : Fin 3) :
    Fin (n + 1) → Fin 6 → Fin 3 := fun i j =>
  if i.1 = 0 ∧ j.1 = 5 then x
  else if i.1 = n ∧ j.1 = 0 then y
  else ⟨b2n (bit (s i).1 j), by
    have hb : b2n (bit (s i).1 j) ≤ 1 := by cases bit (s i).1 j <;> simp [b2n]
    omega⟩

private lemma mkMat_inner {n : ℕ} (s : Fin (n + 1) → Fin 64) (x y : Fin 3)
    (i : Fin (n + 1)) (j : Fin 6) (h1 : ¬(i.1 = 0 ∧ j.1 = 5)) (h2 : ¬(i.1 = n ∧ j.1 = 0)) :
    (mkMat n s x y i j).1 = b2n (bit (s i).1 j) := by
  unfold mkMat; rw [if_neg h1, if_neg h2]

private lemma mkMat_tr {n : ℕ} (s : Fin (n + 1) → Fin 64) (x y : Fin 3) :
    mkMat n s x y 0 5 = x := by
  unfold mkMat; rw [if_pos ⟨rfl, rfl⟩]

private lemma mkMat_bl {n : ℕ} (_hn : 1 ≤ n) (s : Fin (n + 1) → Fin 64) (x y : Fin 3) :
    mkMat n s x y (Fin.last n) 0 = y := by
  unfold mkMat
  rw [if_neg (by simp), if_pos ⟨rfl, rfl⟩]

private abbrev FlatValid (n : ℕ) (hn : 1 ≤ n) :=
  {p : (Fin (n + 1) → Fin 64) × Fin 3 × Fin 3 //
    isSkel n p.1 ∧
    (trFree (p.1 0) (p.1 ⟨1, by omega⟩) = false → p.2.1.1 = 0) ∧
    (blFree (p.1 ⟨n - 1, by omega⟩) (p.1 (Fin.last n)) = false → p.2.2.1 = 0)}

private def validFlatEquiv (n : ℕ) (hn : 1 ≤ n) :
    {A : Fin (n + 1) → Fin 6 → Fin 3 // isValid n A} ≃ FlatValid n hn where
  toFun A :=
    let s : Fin (n + 1) → Fin 64 := fun i =>
      packRow fun j =>
        if (i.1 = 0 ∧ j.1 = 5) ∨ (i.1 = n ∧ j.1 = 0) then false
        else decide ((A.1 i j).1 = 1)
    have hs_bit : ∀ i j, bit (s i).1 j =
        if (i.1 = 0 ∧ j.1 = 5) ∨ (i.1 = n ∧ j.1 = 0) then false
        else decide ((A.1 i j).1 = 1) := fun i j => bit_packRow _ j
    have hs_inner : ∀ i j, ¬(i.1 = 0 ∧ j.1 = 5) → ¬(i.1 = n ∧ j.1 = 0) →
        b2n (bit (s i).1 j) = (A.1 i j).1 := by
      intro i j h1 h2
      rw [hs_bit i j, if_neg (by tauto)]
      exact b2n_decide_eq (inner_le_one hn A.2 i j h1 h2)
    have hs_valid : isSkel n s := by
      refine ⟨by rw [hs_bit]; simp, by rw [hs_bit]; simp [Fin.last], fun i => ?_⟩
      rw [adjRow_iff]; intro j
      have hblk := A.2 i j
      by_cases htr : i.1 = 0 ∧ j.1 = 4
      · have h0 : i.castSucc = 0 := Fin.ext htr.1
        have h1 : i.succ = ⟨1, by omega⟩ := Fin.ext (by simp [htr.1])
        have hj0 : j.castSucc = 4 := Fin.ext htr.2
        have hj1 : j.succ = 5 := Fin.ext (by simp [htr.2])
        rw [h0, h1, hj0, hj1] at hblk ⊢
        rw [← hs_inner 0 4 (by simp) (by simp),
            ← hs_inner ⟨1, by omega⟩ 4 (by simp) (by simp),
            ← hs_inner ⟨1, by omega⟩ 5 (by simp) (by simp)] at hblk
        have htr0 : bit (s 0).1 5 = false := by rw [hs_bit]; simp
        rw [htr0]
        exact (tr_block_iff _ _ _ _).mp hblk |>.1
      · by_cases hbl : i.1 = n - 1 ∧ j.1 = 0
        · have h0 : i.castSucc = ⟨n - 1, by omega⟩ := Fin.ext hbl.1
          have h1 : i.succ = Fin.last n := Fin.ext (by simp [Fin.last]; omega)
          have hj0 : j.castSucc = 0 := Fin.ext hbl.2
          have hj1 : j.succ = 1 := Fin.ext (by simp [hbl.2])
          rw [h0, h1, hj0, hj1] at hblk ⊢
          rw [← hs_inner ⟨n - 1, by omega⟩ 0 (by simp) (by simp; omega),
              ← hs_inner ⟨n - 1, by omega⟩ 1 (by simp) (by simp),
              ← hs_inner (Fin.last n) 1 (by simp) (by simp)] at hblk
          have hbl0 : bit (s (Fin.last n)).1 0 = false := by rw [hs_bit]; simp [Fin.last]
          rw [hbl0]
          exact (bl_block_iff _ _ _ _).mp hblk |>.1
        · rw [validBlock_iff,
              hs_inner i.castSucc j.castSucc (by rintro ⟨_, h⟩; have := j.2; simp at h; omega) (by rintro ⟨h, _⟩; have := i.2; simp at h; omega),
              hs_inner i.castSucc j.succ (by rintro ⟨h1, h2⟩; apply htr; exact ⟨by simpa using h1, by simp at h2; omega⟩) (by rintro ⟨h, _⟩; have := i.2; simp at h; omega),
              hs_inner i.succ j.castSucc (by rintro ⟨h, _⟩; simp at h) (by rintro ⟨h1, h2⟩; apply hbl; exact ⟨by simp at h1; omega, by simpa using h2⟩),
              hs_inner i.succ j.succ (by rintro ⟨h, _⟩; simp at h) (by rintro ⟨_, h⟩; simp at h)]
          exact hblk
    have hx_valid : trFree (s 0) (s ⟨1, by omega⟩) = false → (A.1 0 5).1 = 0 := by
      have hblk := A.2 ⟨0, by omega⟩ 4
      have h0 : (⟨0, by omega⟩ : Fin n).castSucc = 0 := rfl
      have h1 : (⟨0, by omega⟩ : Fin n).succ = ⟨1, by omega⟩ := rfl
      have hj0 : (4 : Fin 5).castSucc = 4 := rfl
      have hj1 : (4 : Fin 5).succ = 5 := rfl
      rw [h0, h1, hj0, hj1] at hblk
      rw [← hs_inner 0 4 (by simp) (by simp),
          ← hs_inner ⟨1, by omega⟩ 4 (by simp) (by simp),
          ← hs_inner ⟨1, by omega⟩ 5 (by simp) (by simp)] at hblk
      exact (tr_block_iff _ _ _ _).mp hblk |>.2
    have hy_valid : blFree (s ⟨n - 1, by omega⟩) (s (Fin.last n)) = false → (A.1 (Fin.last n) 0).1 = 0 := by
      have hblk := A.2 ⟨n - 1, by omega⟩ 0
      have h0 : (⟨n - 1, by omega⟩ : Fin n).castSucc = ⟨n - 1, by omega⟩ := rfl
      have h1 : (⟨n - 1, by omega⟩ : Fin n).succ = Fin.last n := Fin.ext (by simp [Fin.last]; omega)
      have hj0 : (0 : Fin 5).castSucc = 0 := rfl
      have hj1 : (0 : Fin 5).succ = 1 := rfl
      rw [h0, h1, hj0, hj1] at hblk
      rw [← hs_inner ⟨n - 1, by omega⟩ 0 (by simp) (by simp; omega),
          ← hs_inner ⟨n - 1, by omega⟩ 1 (by simp) (by simp),
          ← hs_inner (Fin.last n) 1 (by simp) (by simp)] at hblk
      exact (bl_block_iff _ _ _ _).mp hblk |>.2
    ⟨(s, A.1 0 5, A.1 (Fin.last n) 0), hs_valid, hx_valid, hy_valid⟩
  invFun := fun ⟨(s, x, y), hs, hx, hy⟩ =>
    have hA_val : isValid n (mkMat n s x y) := by
      intro i j
      have hadj := (adjRow_iff (s i.castSucc) (s i.succ)).mp (hs.2.2 i) j
      by_cases htr : i.1 = 0 ∧ j.1 = 4
      · have h0 : i.castSucc = 0 := Fin.ext htr.1
        have h1 : i.succ = ⟨1, by omega⟩ := Fin.ext (by simp [htr.1])
        have hj0 : j.castSucc = 4 := Fin.ext htr.2
        have hj1 : j.succ = 5 := Fin.ext (by simp [htr.2])
        rw [h0, h1, hj0, hj1] at hadj ⊢
        rw [hs.1] at hadj
        rw [mkMat_tr,
            mkMat_inner s x y 0 4 (by simp) (by simp),
            mkMat_inner s x y ⟨1, by omega⟩ 4 (by simp) (by simp),
            mkMat_inner s x y ⟨1, by omega⟩ 5 (by simp) (by simp)]
        exact (tr_block_iff _ _ _ _).mpr ⟨hadj, hx⟩
      · by_cases hbl : i.1 = n - 1 ∧ j.1 = 0
        · have h0 : i.castSucc = ⟨n - 1, by omega⟩ := Fin.ext hbl.1
          have h1 : i.succ = Fin.last n := Fin.ext (by simp [Fin.last]; omega)
          have hj0 : j.castSucc = 0 := Fin.ext hbl.2
          have hj1 : j.succ = 1 := Fin.ext (by simp [hbl.2])
          rw [h0, h1, hj0, hj1] at hadj ⊢
          rw [hs.2.1] at hadj
          rw [mkMat_bl hn,
              mkMat_inner s x y ⟨n - 1, by omega⟩ 0 (by simp) (by simp; omega),
              mkMat_inner s x y ⟨n - 1, by omega⟩ 1 (by simp) (by simp),
              mkMat_inner s x y (Fin.last n) 1 (by simp) (by simp)]
          exact (bl_block_iff _ _ _ _).mpr ⟨hadj, hy⟩
        · rw [mkMat_inner s x y i.castSucc j.castSucc (by rintro ⟨_, h⟩; have := j.2; simp at h; omega) (by rintro ⟨h, _⟩; have := i.2; simp at h; omega),
              mkMat_inner s x y i.castSucc j.succ (by rintro ⟨h1, h2⟩; apply htr; exact ⟨by simpa using h1, by simp at h2; omega⟩) (by rintro ⟨h, _⟩; have := i.2; simp at h; omega),
              mkMat_inner s x y i.succ j.castSucc (by rintro ⟨h, _⟩; simp at h) (by rintro ⟨h1, h2⟩; apply hbl; exact ⟨by simp at h1; omega, by simpa using h2⟩),
              mkMat_inner s x y i.succ j.succ (by rintro ⟨h, _⟩; simp at h) (by rintro ⟨_, h⟩; simp at h)]
          exact (validBlock_iff _ _ _ _).mp hadj
    ⟨mkMat n s x y, hA_val⟩
  left_inv := by
    intro ⟨A, hA⟩
    apply Subtype.ext; funext i j
    by_cases h1 : i.1 = 0 ∧ j.1 = 5
    · have hi : i = 0 := Fin.ext h1.1
      have hj : j = 5 := Fin.ext h1.2
      subst hi; subst hj; simp [mkMat]
    · by_cases h2 : i.1 = n ∧ j.1 = 0
      · have hi : i = Fin.last n := Fin.ext (by simp [Fin.last, h2.1])
        have hj : j = 0 := Fin.ext h2.2
        subst hi; subst hj; simp [mkMat, show n ≠ 0 by omega]
      · apply Fin.ext
        rw [mkMat_inner _ _ _ i j h1 h2, bit_packRow, if_neg (by tauto)]
        exact b2n_decide_eq (inner_le_one hn hA i j h1 h2)
  right_inv := by
    rintro ⟨⟨s, x, y⟩, hs, hx, hy⟩
    apply Subtype.ext
    refine Prod.ext ?_ (Prod.ext (mkMat_tr s x y) (mkMat_bl hn s x y))
    funext i; dsimp only
    conv_rhs => rw [← packRow_bit (s i)]
    congr 1; funext j
    by_cases h1 : i.1 = 0 ∧ j.1 = 5
    · have hi : i = 0 := Fin.ext h1.1
      have hj : j = 5 := Fin.ext h1.2
      subst hi; subst hj; simp [hs.1]
    · by_cases h2 : i.1 = n ∧ j.1 = 0
      · have hi : i = Fin.last n := Fin.ext (by simp [Fin.last, h2.1])
        have hj : j = 0 := Fin.ext h2.2
        subst hi; subst hj; simp [hs.2.1]
      · have hne : ¬((i.1 = 0 ∧ j.1 = 5) ∨ (i.1 = n ∧ j.1 = 0)) := by tauto
        have hin := mkMat_inner s x y i j h1 h2
        simp only [hne, if_false, hin]
        cases bit (s i).1 j <;> simp [b2n]

private lemma card_fiber_bool (b : Bool) :
    Fintype.card {x : Fin 3 // b = false → x.1 = 0} = if b then 3 else 1 := by
  cases b <;> decide

private lemma a_eq_sum (n : ℕ) (hn : 1 ≤ n) :
    a n = ∑ s : Fin (n + 1) → Fin 64,
      if isSkel n s then
        (if trFree (s 0) (s ⟨1, by omega⟩) = true then 3 else 1) *
        (if blFree (s ⟨n - 1, by omega⟩) (s (Fin.last n)) = true then 3 else 1)
      else 0 := by
  unfold a; rw [if_neg (by omega)]
  let flatSig : FlatValid n hn ≃
      Σ s : {s : Fin (n + 1) → Fin 64 // isSkel n s},
        {x : Fin 3 // trFree (s.1 0) (s.1 ⟨1, by omega⟩) = false → x.1 = 0} ×
        {y : Fin 3 // blFree (s.1 ⟨n - 1, by omega⟩) (s.1 (Fin.last n)) = false → y.1 = 0} :=
    { toFun := fun p => ⟨⟨p.1.1, p.2.1⟩, ⟨p.1.2.1, p.2.2.1⟩, ⟨p.1.2.2, p.2.2.2⟩⟩
      invFun := fun q => ⟨(q.1.1, q.2.1.1, q.2.2.1), q.1.2, q.2.1.2, q.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr ((validFlatEquiv n hn).trans flatSig), Fintype.card_sigma]
  simp only [Fintype.card_prod, card_fiber_bool]
  let g : (Fin (n + 1) → Fin 64) → ℕ := fun s =>
    (if trFree (s 0) (s ⟨1, by omega⟩) = true then 3 else 1) *
    (if blFree (s ⟨n - 1, by omega⟩) (s (Fin.last n)) = true then 3 else 1)
  have h1 : (∑ s ∈ Finset.univ.filter (fun s : Fin (n + 1) → Fin 64 => isSkel n s), g s) =
      ∑ s : {s : Fin (n + 1) → Fin 64 // isSkel n s}, g s.1 :=
    Finset.sum_subtype (Finset.univ.filter fun s : Fin (n + 1) → Fin 64 => isSkel n s) (by intro s; simp) g
  exact h1.symm.trans (Finset.sum_filter _ _)

private def dp : ℕ → Fin 64 → ℕ
  | 0, r1 => ((List.finRange 64).map fun r0 =>
      if !bit r0.1 5 && adjRow r0 r1 then (if trFree r0 r1 then 3 else 1) else 0).sum
  | m + 1, r' => ((List.finRange 64).map fun r => if adjRow r r' then dp m r else 0).sum

private def wEnd (r : Fin 64) : ℕ :=
  ((List.finRange 64).map fun r1 =>
    if !bit r1.1 0 && adjRow r r1 then (if blFree r r1 then 3 else 1) else 0).sum

private def dp0Tbl (r : Fin 64) : ℕ := (if r.1 < 32 then (if r.1 < 16 then (if r.1 < 8 then (if r.1 < 4 then (if r.1 < 2 then (if r.1 < 1 then 8 else 1) else (if r.1 < 3 then 1 else 0)) else (if r.1 < 6 then (if r.1 < 5 then 2 else 1) else 0)) else (if r.1 < 12 then (if r.1 < 10 then (if r.1 < 9 then 3 else 1) else (if r.1 < 11 then 1 else 0)) else 0)) else (if r.1 < 24 then (if r.1 < 20 then (if r.1 < 18 then (if r.1 < 17 then 4 else 1) else (if r.1 < 19 then 1 else 0)) else (if r.1 < 22 then (if r.1 < 21 then 2 else 1) else 0)) else 0)) else (if r.1 < 48 then (if r.1 < 40 then (if r.1 < 36 then (if r.1 < 34 then (if r.1 < 33 then 16 else 3) else (if r.1 < 35 then 3 else 0)) else (if r.1 < 38 then (if r.1 < 37 then 6 else 3) else 0)) else (if r.1 < 44 then (if r.1 < 42 then (if r.1 < 41 then 9 else 3) else (if r.1 < 43 then 3 else 0)) else 0)) else (if r.1 < 56 then (if r.1 < 52 then (if r.1 < 50 then (if r.1 < 49 then 5 else 1) else (if r.1 < 51 then 1 else 0)) else (if r.1 < 54 then (if r.1 < 53 then 2 else 1) else 0)) else (if r.1 < 60 then (if r.1 < 58 then (if r.1 < 57 then 4 else 1) else (if r.1 < 59 then 1 else 0)) else (if r.1 < 62 then (if r.1 < 61 then 3 else 1) else (if r.1 < 63 then 2 else 1))))))
private def dp1Tbl (r : Fin 64) : ℕ := (if r.1 < 32 then (if r.1 < 16 then (if r.1 < 8 then (if r.1 < 4 then (if r.1 < 2 then (if r.1 < 1 then 10 else 1) else (if r.1 < 3 then 1 else 0)) else (if r.1 < 6 then (if r.1 < 5 then 3 else 1) else 0)) else (if r.1 < 12 then (if r.1 < 10 then (if r.1 < 9 then 4 else 1) else (if r.1 < 11 then 1 else 0)) else 0)) else (if r.1 < 24 then (if r.1 < 20 then (if r.1 < 18 then (if r.1 < 17 then 5 else 1) else (if r.1 < 19 then 1 else 0)) else (if r.1 < 22 then (if r.1 < 21 then 3 else 1) else 0)) else 0)) else (if r.1 < 48 then (if r.1 < 40 then (if r.1 < 36 then (if r.1 < 34 then (if r.1 < 33 then 28 else 4) else (if r.1 < 35 then 4 else 0)) else (if r.1 < 38 then (if r.1 < 37 then 12 else 4) else 0)) else (if r.1 < 44 then (if r.1 < 42 then (if r.1 < 41 then 16 else 4) else (if r.1 < 43 then 4 else 0)) else 0)) else (if r.1 < 56 then (if r.1 < 52 then (if r.1 < 50 then (if r.1 < 49 then 9 else 1) else (if r.1 < 51 then 1 else 0)) else (if r.1 < 54 then (if r.1 < 53 then 3 else 1) else 0)) else (if r.1 < 60 then (if r.1 < 58 then (if r.1 < 57 then 9 else 1) else (if r.1 < 59 then 1 else 0)) else (if r.1 < 62 then (if r.1 < 61 then 9 else 1) else (if r.1 < 63 then 9 else 8))))))
private def dp2Tbl (r : Fin 64) : ℕ := (if r.1 < 32 then (if r.1 < 16 then (if r.1 < 8 then (if r.1 < 4 then (if r.1 < 2 then (if r.1 < 1 then 19 else 1) else (if r.1 < 3 then 1 else 0)) else (if r.1 < 6 then (if r.1 < 5 then 4 else 1) else 0)) else (if r.1 < 12 then (if r.1 < 10 then (if r.1 < 9 then 5 else 1) else (if r.1 < 11 then 1 else 0)) else 0)) else (if r.1 < 24 then (if r.1 < 20 then (if r.1 < 18 then (if r.1 < 17 then 6 else 1) else (if r.1 < 19 then 1 else 0)) else (if r.1 < 22 then (if r.1 < 21 then 4 else 1) else 0)) else 0)) else (if r.1 < 48 then (if r.1 < 40 then (if r.1 < 36 then (if r.1 < 34 then (if r.1 < 33 then 43 else 5) else (if r.1 < 35 then 5 else 0)) else (if r.1 < 38 then (if r.1 < 37 then 20 else 5) else 0)) else (if r.1 < 44 then (if r.1 < 42 then (if r.1 < 41 then 25 else 5) else (if r.1 < 43 then 5 else 0)) else 0)) else (if r.1 < 56 then (if r.1 < 52 then (if r.1 < 50 then (if r.1 < 49 then 11 else 1) else (if r.1 < 51 then 1 else 0)) else (if r.1 < 54 then (if r.1 < 53 then 4 else 1) else 0)) else (if r.1 < 60 then (if r.1 < 58 then (if r.1 < 57 then 11 else 1) else (if r.1 < 59 then 1 else 0)) else (if r.1 < 62 then (if r.1 < 61 then 11 else 1) else (if r.1 < 63 then 11 else 10))))))
private def dp3Tbl (r : Fin 64) : ℕ := (if r.1 < 32 then (if r.1 < 16 then (if r.1 < 8 then (if r.1 < 4 then (if r.1 < 2 then (if r.1 < 1 then 30 else 1) else (if r.1 < 3 then 1 else 0)) else (if r.1 < 6 then (if r.1 < 5 then 5 else 1) else 0)) else (if r.1 < 12 then (if r.1 < 10 then (if r.1 < 9 then 6 else 1) else (if r.1 < 11 then 1 else 0)) else 0)) else (if r.1 < 24 then (if r.1 < 20 then (if r.1 < 18 then (if r.1 < 17 then 7 else 1) else (if r.1 < 19 then 1 else 0)) else (if r.1 < 22 then (if r.1 < 21 then 5 else 1) else 0)) else 0)) else (if r.1 < 48 then (if r.1 < 40 then (if r.1 < 36 then (if r.1 < 34 then (if r.1 < 33 then 68 else 6) else (if r.1 < 35 then 6 else 0)) else (if r.1 < 38 then (if r.1 < 37 then 30 else 6) else 0)) else (if r.1 < 44 then (if r.1 < 42 then (if r.1 < 41 then 36 else 6) else (if r.1 < 43 then 6 else 0)) else 0)) else (if r.1 < 56 then (if r.1 < 52 then (if r.1 < 50 then (if r.1 < 49 then 20 else 1) else (if r.1 < 51 then 1 else 0)) else (if r.1 < 54 then (if r.1 < 53 then 5 else 1) else 0)) else (if r.1 < 60 then (if r.1 < 58 then (if r.1 < 57 then 20 else 1) else (if r.1 < 59 then 1 else 0)) else (if r.1 < 62 then (if r.1 < 61 then 20 else 1) else (if r.1 < 63 then 20 else 19))))))
private def dp4Tbl (r : Fin 64) : ℕ := (if r.1 < 32 then (if r.1 < 16 then (if r.1 < 8 then (if r.1 < 4 then (if r.1 < 2 then (if r.1 < 1 then 50 else 1) else (if r.1 < 3 then 1 else 0)) else (if r.1 < 6 then (if r.1 < 5 then 6 else 1) else 0)) else (if r.1 < 12 then (if r.1 < 10 then (if r.1 < 9 then 7 else 1) else (if r.1 < 11 then 1 else 0)) else 0)) else (if r.1 < 24 then (if r.1 < 20 then (if r.1 < 18 then (if r.1 < 17 then 8 else 1) else (if r.1 < 19 then 1 else 0)) else (if r.1 < 22 then (if r.1 < 21 then 6 else 1) else 0)) else 0)) else (if r.1 < 48 then (if r.1 < 40 then (if r.1 < 36 then (if r.1 < 34 then (if r.1 < 33 then 105 else 7) else (if r.1 < 35 then 7 else 0)) else (if r.1 < 38 then (if r.1 < 37 then 42 else 7) else 0)) else (if r.1 < 44 then (if r.1 < 42 then (if r.1 < 41 then 49 else 7) else (if r.1 < 43 then 7 else 0)) else 0)) else (if r.1 < 56 then (if r.1 < 52 then (if r.1 < 50 then (if r.1 < 49 then 31 else 1) else (if r.1 < 51 then 1 else 0)) else (if r.1 < 54 then (if r.1 < 53 then 6 else 1) else 0)) else (if r.1 < 60 then (if r.1 < 58 then (if r.1 < 57 then 31 else 1) else (if r.1 < 59 then 1 else 0)) else (if r.1 < 62 then (if r.1 < 61 then 31 else 1) else (if r.1 < 63 then 31 else 30))))))
private def dp5Tbl (r : Fin 64) : ℕ := (if r.1 < 32 then (if r.1 < 16 then (if r.1 < 8 then (if r.1 < 4 then (if r.1 < 2 then (if r.1 < 1 then 81 else 1) else (if r.1 < 3 then 1 else 0)) else (if r.1 < 6 then (if r.1 < 5 then 7 else 1) else 0)) else (if r.1 < 12 then (if r.1 < 10 then (if r.1 < 9 then 8 else 1) else (if r.1 < 11 then 1 else 0)) else 0)) else (if r.1 < 24 then (if r.1 < 20 then (if r.1 < 18 then (if r.1 < 17 then 9 else 1) else (if r.1 < 19 then 1 else 0)) else (if r.1 < 22 then (if r.1 < 21 then 7 else 1) else 0)) else 0)) else (if r.1 < 48 then (if r.1 < 40 then (if r.1 < 36 then (if r.1 < 34 then (if r.1 < 33 then 163 else 8) else (if r.1 < 35 then 8 else 0)) else (if r.1 < 38 then (if r.1 < 37 then 56 else 8) else 0)) else (if r.1 < 44 then (if r.1 < 42 then (if r.1 < 41 then 64 else 8) else (if r.1 < 43 then 8 else 0)) else 0)) else (if r.1 < 56 then (if r.1 < 52 then (if r.1 < 50 then (if r.1 < 49 then 51 else 1) else (if r.1 < 51 then 1 else 0)) else (if r.1 < 54 then (if r.1 < 53 then 7 else 1) else 0)) else (if r.1 < 60 then (if r.1 < 58 then (if r.1 < 57 then 51 else 1) else (if r.1 < 59 then 1 else 0)) else (if r.1 < 62 then (if r.1 < 61 then 51 else 1) else (if r.1 < 63 then 51 else 50))))))
private def dp6Tbl (r : Fin 64) : ℕ := (if r.1 < 32 then (if r.1 < 16 then (if r.1 < 8 then (if r.1 < 4 then (if r.1 < 2 then (if r.1 < 1 then 132 else 1) else (if r.1 < 3 then 1 else 0)) else (if r.1 < 6 then (if r.1 < 5 then 8 else 1) else 0)) else (if r.1 < 12 then (if r.1 < 10 then (if r.1 < 9 then 9 else 1) else (if r.1 < 11 then 1 else 0)) else 0)) else (if r.1 < 24 then (if r.1 < 20 then (if r.1 < 18 then (if r.1 < 17 then 10 else 1) else (if r.1 < 19 then 1 else 0)) else (if r.1 < 22 then (if r.1 < 21 then 8 else 1) else 0)) else 0)) else (if r.1 < 48 then (if r.1 < 40 then (if r.1 < 36 then (if r.1 < 34 then (if r.1 < 33 then 253 else 9) else (if r.1 < 35 then 9 else 0)) else (if r.1 < 38 then (if r.1 < 37 then 72 else 9) else 0)) else (if r.1 < 44 then (if r.1 < 42 then (if r.1 < 41 then 81 else 9) else (if r.1 < 43 then 9 else 0)) else 0)) else (if r.1 < 56 then (if r.1 < 52 then (if r.1 < 50 then (if r.1 < 49 then 82 else 1) else (if r.1 < 51 then 1 else 0)) else (if r.1 < 54 then (if r.1 < 53 then 8 else 1) else 0)) else (if r.1 < 60 then (if r.1 < 58 then (if r.1 < 57 then 82 else 1) else (if r.1 < 59 then 1 else 0)) else (if r.1 < 62 then (if r.1 < 61 then 82 else 1) else (if r.1 < 63 then 82 else 81))))))
private def wEndTbl (r : Fin 64) : ℕ := (if r.1 < 32 then (if r.1 < 16 then (if r.1 < 8 then (if r.1 < 4 then (if r.1 < 2 then (if r.1 < 1 then 8 else 16) else (if r.1 < 3 then 4 else 5)) else (if r.1 < 6 then (if r.1 < 5 then 3 else 9) else (if r.1 < 7 then 0 else 4))) else (if r.1 < 12 then (if r.1 < 10 then (if r.1 < 9 then 2 else 6) else 2) else (if r.1 < 14 then 0 else (if r.1 < 15 then 0 else 3)))) else (if r.1 < 24 then (if r.1 < 20 then (if r.1 < 18 then (if r.1 < 17 then 1 else 3) else 1) else (if r.1 < 22 then (if r.1 < 21 then 1 else 3) else (if r.1 < 23 then 0 else 1))) else (if r.1 < 28 then 0 else (if r.1 < 30 then 0 else (if r.1 < 31 then 0 else 2))))) else (if r.1 < 48 then (if r.1 < 40 then (if r.1 < 36 then (if r.1 < 34 then (if r.1 < 33 then 1 else 3) else 1) else (if r.1 < 38 then (if r.1 < 37 then 1 else 3) else (if r.1 < 39 then 0 else 1))) else (if r.1 < 44 then (if r.1 < 42 then (if r.1 < 41 then 1 else 3) else 1) else (if r.1 < 46 then 0 else (if r.1 < 47 then 0 else 1)))) else (if r.1 < 56 then 0 else (if r.1 < 60 then 0 else (if r.1 < 62 then 0 else (if r.1 < 63 then 0 else 1))))))

private lemma dp0_eq_tbl : ∀ r : Fin 64, dp 0 r = dp0Tbl r := by
  intro r; fin_cases r <;> rfl
private lemma dp1_eq_tbl : ∀ r : Fin 64, dp 1 r = dp1Tbl r := by
  intro r; unfold dp
  have h : (fun r0 : Fin 64 => if adjRow r0 r then dp 0 r0 else 0) =
           (fun r0 : Fin 64 => if adjRow r0 r then dp0Tbl r0 else 0) := by
    funext r0; rw [dp0_eq_tbl]
  rw [h]; fin_cases r <;> rfl
private lemma dp2_eq_tbl : ∀ r : Fin 64, dp 2 r = dp2Tbl r := by
  intro r; unfold dp
  have h : (fun r0 : Fin 64 => if adjRow r0 r then dp 1 r0 else 0) =
           (fun r0 : Fin 64 => if adjRow r0 r then dp1Tbl r0 else 0) := by
    funext r0; rw [dp1_eq_tbl]
  rw [h]; fin_cases r <;> rfl
private lemma dp3_eq_tbl : ∀ r : Fin 64, dp 3 r = dp3Tbl r := by
  intro r; unfold dp
  have h : (fun r0 : Fin 64 => if adjRow r0 r then dp 2 r0 else 0) =
           (fun r0 : Fin 64 => if adjRow r0 r then dp2Tbl r0 else 0) := by
    funext r0; rw [dp2_eq_tbl]
  rw [h]; fin_cases r <;> rfl
private lemma dp4_eq_tbl : ∀ r : Fin 64, dp 4 r = dp4Tbl r := by
  intro r; unfold dp
  have h : (fun r0 : Fin 64 => if adjRow r0 r then dp 3 r0 else 0) =
           (fun r0 : Fin 64 => if adjRow r0 r then dp3Tbl r0 else 0) := by
    funext r0; rw [dp3_eq_tbl]
  rw [h]; fin_cases r <;> rfl
private lemma dp5_eq_tbl : ∀ r : Fin 64, dp 5 r = dp5Tbl r := by
  intro r; unfold dp
  have h : (fun r0 : Fin 64 => if adjRow r0 r then dp 4 r0 else 0) =
           (fun r0 : Fin 64 => if adjRow r0 r then dp4Tbl r0 else 0) := by
    funext r0; rw [dp4_eq_tbl]
  rw [h]; fin_cases r <;> rfl
private lemma dp6_eq_tbl : ∀ r : Fin 64, dp 6 r = dp6Tbl r := by
  intro r; unfold dp
  have h : (fun r0 : Fin 64 => if adjRow r0 r then dp 5 r0 else 0) =
           (fun r0 : Fin 64 => if adjRow r0 r then dp5Tbl r0 else 0) := by
    funext r0; rw [dp5_eq_tbl]
  rw [h]; fin_cases r <;> rfl

private lemma wEnd_eq_tbl : ∀ r : Fin 64, wEnd r = wEndTbl r := by
  intro r; fin_cases r <;> rfl

private lemma dp_rec_base :
    ∀ r : Fin 64, dp 6 r + 5 * dp 4 r + dp 1 r = 4 * dp 5 r + dp 3 r + 2 * dp 2 r := by
  intro r
  rw [dp6_eq_tbl, dp5_eq_tbl, dp4_eq_tbl, dp3_eq_tbl, dp2_eq_tbl, dp1_eq_tbl]
  fin_cases r <;> rfl

private lemma dp_step_sum (m : ℕ) (r' : Fin 64) :
    dp (m + 1) r' = ∑ r : Fin 64, if adjRow r r' = true then dp m r else 0 := by
  rw [dp, Fin.sum_univ_def]

private lemma sum_lin6 (f6 f5 f4 f3 f2 f1 g : Fin 64 → ℕ)
    (h : ∀ r : Fin 64, f6 r + 5 * f4 r + f1 r = 4 * f5 r + f3 r + 2 * f2 r) :
    (∑ r : Fin 64, f6 r * g r) + 5 * (∑ r : Fin 64, f4 r * g r) + (∑ r : Fin 64, f1 r * g r) =
      4 * (∑ r : Fin 64, f5 r * g r) + (∑ r : Fin 64, f3 r * g r) + 2 * (∑ r : Fin 64, f2 r * g r) := by
  have hL : (∑ r : Fin 64, f6 r * g r) + 5 * (∑ r : Fin 64, f4 r * g r) + (∑ r : Fin 64, f1 r * g r) =
      ∑ r : Fin 64, (f6 r + 5 * f4 r + f1 r) * g r := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro r _; ring
  have hR : 4 * (∑ r : Fin 64, f5 r * g r) + (∑ r : Fin 64, f3 r * g r) + 2 * (∑ r : Fin 64, f2 r * g r) =
      ∑ r : Fin 64, (4 * f5 r + f3 r + 2 * f2 r) * g r := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro r _; ring
  rw [hL, hR]
  apply Finset.sum_congr rfl; intro r _; rw [h r]

private lemma dp_rec (m : ℕ) :
    ∀ r : Fin 64, dp (m + 6) r + 5 * dp (m + 4) r + dp (m + 1) r =
      4 * dp (m + 5) r + dp (m + 3) r + 2 * dp (m + 2) r := by
  induction m with
  | zero => exact dp_rec_base
  | succ k ih =>
    intro r'
    have hstep : ∀ t : ℕ, dp (t + 1) r' = ∑ r : Fin 64, dp t r * (if adjRow r r' = true then 1 else 0) := by
      intro t; rw [dp_step_sum]; apply Finset.sum_congr rfl; intro r _; split_ifs <;> simp
    rw [hstep (k + 6), hstep (k + 5), hstep (k + 4), hstep (k + 3), hstep (k + 2), hstep (k + 1)]
    exact sum_lin6 (dp (k + 6)) (dp (k + 5)) (dp (k + 4)) (dp (k + 3)) (dp (k + 2)) (dp (k + 1))
      (fun r => if adjRow r r' = true then 1 else 0) ih

private def prefixSum (m : ℕ) (rLast : Fin 64) : ℕ :=
  ∑ s : Fin (m + 2) → Fin 64,
    if bit (s 0).1 5 = false ∧ s (Fin.last (m + 1)) = rLast ∧
       ∀ i : Fin (m + 1), adjRow (s i.castSucc) (s i.succ) = true
    then (if trFree (s 0) (s ⟨1, by omega⟩) = true then 3 else 1) else 0

private lemma prefixSum_eq_dp (m : ℕ) : ∀ r : Fin 64, prefixSum m r = dp m r := by
  induction m with
  | zero =>
    intro r
    unfold prefixSum dp
    let e : (Fin 2 → Fin 64) ≃ Fin 64 × Fin 64 :=
      { toFun := fun s => (s 0, s 1)
        invFun := fun (r0, r1) i => if i.1 = 0 then r0 else r1
        left_inv := fun s => by funext i; fin_cases i <;> rfl
        right_inv := fun (_, _) => rfl }
    trans (∑ p : Fin 64 × Fin 64,
      if bit p.1.1 5 = false ∧ p.2 = r ∧ adjRow p.1 p.2 = true
      then (if trFree p.1 p.2 = true then 3 else 1) else 0)
    · exact Fintype.sum_equiv e _ _ (fun s => by
        have h : (∀ i : Fin 1, adjRow (s i.castSucc) (s i.succ) = true) ↔ adjRow (s 0) (s 1) = true := by
          constructor
          · intro h; exact h 0
          · intro h i; fin_cases i; exact h
        simp [e, Fin.last, h])
    · rw [Fintype.sum_prod_type, Fin.sum_univ_def]
      refine congrArg List.sum (List.map_congr_left fun r0 _ => ?_)
      rw [Finset.sum_eq_single r]
      · cases bit r0.1 5 <;> cases adjRow r0 r <;> simp
      · intro r1 _ hne; simp [hne]
      · intro h; exact absurd (Finset.mem_univ r) h
  | succ k ih =>
    intro r'
    unfold prefixSum
    rw [dp_step_sum]
    let e : (Fin (k + 3) → Fin 64) ≃ (Fin (k + 2) → Fin 64) × Fin 64 :=
      { toFun := fun s => (fun i => s i.castSucc, s (Fin.last (k + 2)))
        invFun := fun (t, r) => Fin.snoc t r
        left_inv := fun s => by funext i; refine Fin.lastCases ?_ ?_ i <;> simp
        right_inv := fun (t, r) => by ext <;> simp }
    trans (∑ p : (Fin (k + 2) → Fin 64) × Fin 64,
      if bit (p.1 0).1 5 = false ∧ p.2 = r' ∧
         (∀ i : Fin (k + 1), adjRow (p.1 i.castSucc) (p.1 i.succ) = true) ∧
         adjRow (p.1 (Fin.last (k + 1))) p.2 = true
      then (if trFree (p.1 0) (p.1 ⟨1, by omega⟩) = true then 3 else 1) else 0)
    · exact Fintype.sum_equiv e _ _ (fun s => by
        have hall : (∀ i : Fin (k + 2), adjRow (s i.castSucc) (s i.succ) = true) ↔
            (∀ i : Fin (k + 1), adjRow (s i.castSucc.castSucc) (s i.succ.castSucc) = true) ∧
            adjRow (s (Fin.last (k + 1)).castSucc) (s (Fin.last (k + 2))) = true := by
          constructor
          · intro h; exact ⟨fun i => h i.castSucc, by simpa [Fin.last] using h (Fin.last (k + 1))⟩
          · rintro ⟨h1, h2⟩ i
            refine Fin.lastCases ?_ ?_ i
            · simpa [Fin.last] using h2
            · intro j; exact h1 j
        simp only [e, hall]; rfl)
    · rw [Fintype.sum_prod_type]
      have hinner : ∀ t : Fin (k + 2) → Fin 64,
          (∑ r : Fin 64, if bit (t 0).1 5 = false ∧ r = r' ∧
            (∀ i : Fin (k + 1), adjRow (t i.castSucc) (t i.succ) = true) ∧
            adjRow (t (Fin.last (k + 1))) r = true
            then (if trFree (t 0) (t ⟨1, by omega⟩) = true then 3 else 1) else 0) =
          if bit (t 0).1 5 = false ∧ (∀ i : Fin (k + 1), adjRow (t i.castSucc) (t i.succ) = true) ∧
             adjRow (t (Fin.last (k + 1))) r' = true
          then (if trFree (t 0) (t ⟨1, by omega⟩) = true then 3 else 1) else 0 := by
        intro t
        rw [Finset.sum_eq_single r']
        · simp
        · intro r _ hne; simp [hne]
        · intro h; exact absurd (Finset.mem_univ r') h
      simp only [hinner]
      calc (∑ t : Fin (k + 2) → Fin 64,
              if bit (t 0).1 5 = false ∧ (∀ i : Fin (k + 1), adjRow (t i.castSucc) (t i.succ) = true) ∧
                 adjRow (t (Fin.last (k + 1))) r' = true
              then (if trFree (t 0) (t ⟨1, by omega⟩) = true then 3 else 1) else 0)
          = ∑ r : Fin 64, ∑ t : Fin (k + 2) → Fin 64,
              if t (Fin.last (k + 1)) = r ∧ bit (t 0).1 5 = false ∧
                 (∀ i : Fin (k + 1), adjRow (t i.castSucc) (t i.succ) = true) ∧
                 adjRow r r' = true
              then (if trFree (t 0) (t ⟨1, by omega⟩) = true then 3 else 1) else 0 := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro t _
            rw [Finset.sum_eq_single (t (Fin.last (k + 1)))]
            · simp
            · intro r _ hne; simp [hne.symm]
            · intro h; exact absurd (Finset.mem_univ _) h
        _ = ∑ r : Fin 64, if adjRow r r' = true then dp k r else 0 := by
            apply Finset.sum_congr rfl; intro r _
            rw [← ih r]; unfold prefixSum
            by_cases ha : adjRow r r' = true
            · simp only [ha, and_true, if_true]
              apply Finset.sum_congr rfl; intro t _; exact if_congr (by tauto) rfl rfl
            · simp [ha]

private lemma a_ge2_eq (m : ℕ) :
    a (m + 2) = ∑ r : Fin 64, dp m r * wEnd r := by
  rw [a_eq_sum (m + 2) (by omega)]
  let e : (Fin (m + 3) → Fin 64) ≃ (Fin (m + 2) → Fin 64) × Fin 64 :=
    { toFun := fun s => (fun i => s i.castSucc, s (Fin.last (m + 2)))
      invFun := fun (t, r) => Fin.snoc t r
      left_inv := fun s => by funext i; refine Fin.lastCases ?_ ?_ i <;> simp
      right_inv := fun (t, r) => by ext <;> simp }
  trans (∑ p : (Fin (m + 2) → Fin 64) × Fin 64,
    if bit (p.1 0).1 5 = false ∧ bit p.2.1 0 = false ∧
       (∀ i : Fin (m + 1), adjRow (p.1 i.castSucc) (p.1 i.succ) = true) ∧
       adjRow (p.1 (Fin.last (m + 1))) p.2 = true
    then (if trFree (p.1 0) (p.1 ⟨1, by omega⟩) = true then 3 else 1) *
         (if blFree (p.1 (Fin.last (m + 1))) p.2 = true then 3 else 1)
    else 0)
  · exact Fintype.sum_equiv e _ _ (fun s => by
      have hall : (∀ i : Fin (m + 2), adjRow (s i.castSucc) (s i.succ) = true) ↔
          (∀ i : Fin (m + 1), adjRow (s i.castSucc.castSucc) (s i.succ.castSucc) = true) ∧
          adjRow (s (Fin.last (m + 1)).castSucc) (s (Fin.last (m + 2))) = true := by
        constructor
        · intro h; exact ⟨fun i => h i.castSucc, by simpa [Fin.last] using h (Fin.last (m + 1))⟩
        · rintro ⟨h1, h2⟩ i
          refine Fin.lastCases ?_ ?_ i
          · simpa [Fin.last] using h2
          · intro j; exact h1 j
      have hprev : (⟨m + 2 - 1, by omega⟩ : Fin (m + 3)) = (Fin.last (m + 1)).castSucc :=
        Fin.ext (by simp [Fin.last])
      simp only [isSkel, e, hall, hprev]; rfl)
  · rw [Fintype.sum_prod_type]
    have hsplit : ∀ t : Fin (m + 2) → Fin 64,
        (∑ r1 : Fin 64, if bit (t 0).1 5 = false ∧ bit r1.1 0 = false ∧
          (∀ i : Fin (m + 1), adjRow (t i.castSucc) (t i.succ) = true) ∧
          adjRow (t (Fin.last (m + 1))) r1 = true
          then (if trFree (t 0) (t ⟨1, by omega⟩) = true then 3 else 1) *
               (if blFree (t (Fin.last (m + 1))) r1 = true then 3 else 1)
          else 0) =
        (if bit (t 0).1 5 = false ∧ (∀ i : Fin (m + 1), adjRow (t i.castSucc) (t i.succ) = true)
          then (if trFree (t 0) (t ⟨1, by omega⟩) = true then 3 else 1) else 0) *
        wEnd (t (Fin.last (m + 1))) := by
      intro t
      by_cases ht : bit (t 0).1 5 = false ∧ ∀ i : Fin (m + 1), adjRow (t i.castSucc) (t i.succ) = true
      · simp only [ht.1, ht.2, true_and]
        unfold wEnd; rw [← Fin.sum_univ_def, Finset.mul_sum]
        congr 1; funext r1
        cases bit r1.1 0 <;> cases adjRow (t (Fin.last (m + 1))) r1 <;> simp
      · simp only [ht, if_false, zero_mul]
        apply Finset.sum_eq_zero; intro r1 _
        rw [if_neg]; tauto
    simp only [hsplit]
    calc (∑ t : Fin (m + 2) → Fin 64,
            (if bit (t 0).1 5 = false ∧ ∀ i : Fin (m + 1), adjRow (t i.castSucc) (t i.succ) = true
             then (if trFree (t 0) (t ⟨1, by omega⟩) = true then 3 else 1) else 0) *
            wEnd (t (Fin.last (m + 1))))
        = ∑ r : Fin 64, ∑ t : Fin (m + 2) → Fin 64,
            (if bit (t 0).1 5 = false ∧ t (Fin.last (m + 1)) = r ∧
                ∀ i : Fin (m + 1), adjRow (t i.castSucc) (t i.succ) = true
             then (if trFree (t 0) (t ⟨1, by omega⟩) = true then 3 else 1) else 0) *
            wEnd r := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl; intro t _
          rw [Finset.sum_eq_single (t (Fin.last (m + 1)))]
          · simp
          · intro r _ hne; simp [hne.symm]
          · intro h; exact absurd (Finset.mem_univ _) h
      _ = ∑ r : Fin 64, dp m r * wEnd r := by
          apply Finset.sum_congr rfl; intro r _
          rw [← Finset.sum_mul, ← prefixSum_eq_dp m r]; rfl

private lemma a_rec (n : ℕ) (hn : 3 ≤ n) :
    a (n + 5) + 5 * a (n + 3) + a n = 4 * a (n + 4) + a (n + 2) + 2 * a (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have ha6 : a (m + 3 + 5) = ∑ r : Fin 64, dp (m + 6) r * wEnd r := by
    rw [show m + 3 + 5 = (m + 6) + 2 by omega]; exact a_ge2_eq (m + 6)
  have ha5 : a (m + 3 + 4) = ∑ r : Fin 64, dp (m + 5) r * wEnd r := by
    rw [show m + 3 + 4 = (m + 5) + 2 by omega]; exact a_ge2_eq (m + 5)
  have ha4 : a (m + 3 + 3) = ∑ r : Fin 64, dp (m + 4) r * wEnd r := by
    rw [show m + 3 + 3 = (m + 4) + 2 by omega]; exact a_ge2_eq (m + 4)
  have ha3 : a (m + 3 + 2) = ∑ r : Fin 64, dp (m + 3) r * wEnd r := by
    rw [show m + 3 + 2 = (m + 3) + 2 by omega]; exact a_ge2_eq (m + 3)
  have ha2 : a (m + 3 + 1) = ∑ r : Fin 64, dp (m + 2) r * wEnd r := by
    rw [show m + 3 + 1 = (m + 2) + 2 by omega]; exact a_ge2_eq (m + 2)
  have ha1 : a (m + 3) = ∑ r : Fin 64, dp (m + 1) r * wEnd r := by
    rw [show m + 3 = (m + 1) + 2 by omega]; exact a_ge2_eq (m + 1)
  rw [ha6, ha5, ha4, ha3, ha2, ha1]
  exact sum_lin6 (dp (m + 6)) (dp (m + 5)) (dp (m + 4)) (dp (m + 3)) (dp (m + 2)) (dp (m + 1)) wEnd (dp_rec m)

private lemma a_one : a 1 = 115 := by
  rw [a_eq_sum 1 (by omega)]
  let e : (Fin 2 → Fin 64) ≃ Fin 64 × Fin 64 :=
    { toFun := fun s => (s 0, s 1)
      invFun := fun (r0, r1) i => if i.1 = 0 then r0 else r1
      left_inv := fun s => by funext i; fin_cases i <;> rfl
      right_inv := fun (_, _) => rfl }
  trans (∑ p : Fin 64 × Fin 64,
    if bit p.1.1 5 = false ∧ bit p.2.1 0 = false ∧ adjRow p.1 p.2 = true
    then (if trFree p.1 p.2 = true then 3 else 1) * (if blFree p.1 p.2 = true then 3 else 1) else 0)
  · exact Fintype.sum_equiv e _ _ (fun s => by
      have h : (∀ i : Fin 1, adjRow (s i.castSucc) (s i.succ) = true) ↔ adjRow (s 0) (s 1) = true := by
        constructor
        · intro h; exact h 0
        · intro h i; fin_cases i; exact h
      simp [isSkel, e, Fin.last, h])
  · rw [Fintype.sum_prod_type]
    have hrow : ∀ r0 : Fin 64,
        (∑ r1 : Fin 64, if bit r0.1 5 = false ∧ bit r1.1 0 = false ∧ adjRow r0 r1 = true
         then (if trFree r0 r1 = true then 3 else 1) * (if blFree r0 r1 = true then 3 else 1) else 0) =
        ((List.finRange 64).map fun r1 =>
          if !bit r0.1 5 && !bit r1.1 0 && adjRow r0 r1
          then (if trFree r0 r1 then 3 else 1) * (if blFree r0 r1 then 3 else 1) else 0).sum := by
      intro r0; rw [Fin.sum_univ_def]
      congr 1; apply List.map_congr_left; intro r1 _
      cases bit r0.1 5 <;> cases bit r1.1 0 <;> cases adjRow r0 r1 <;> simp
    simp only [hrow]
    have hvals : ∀ r0 : Fin 64,
        ((List.finRange 64).map fun r1 =>
          if !bit r0.1 5 && !bit r1.1 0 && adjRow r0 r1
          then (if trFree r0 r1 then 3 else 1) * (if blFree r0 r1 then 3 else 1) else 0).sum =
        (if r0.1 < 32 then (if r0.1 < 16 then (if r0.1 < 8 then (if r0.1 < 4 then (if r0.1 < 2 then (if r0.1 < 1 then 10 else 22) else (if r0.1 < 3 then 6 else 7)) else (if r0.1 < 6 then (if r0.1 < 5 then 5 else 15) else (if r0.1 < 7 then 0 else 6))) else (if r0.1 < 12 then (if r0.1 < 10 then (if r0.1 < 9 then 4 else 12) else 4) else (if r0.1 < 14 then 0 else (if r0.1 < 15 then 0 else 5)))) else (if r0.1 < 24 then (if r0.1 < 20 then (if r0.1 < 18 then (if r0.1 < 17 then 1 else 3) else 1) else (if r0.1 < 22 then (if r0.1 < 21 then 1 else 3) else (if r0.1 < 23 then 0 else 1))) else (if r0.1 < 28 then 0 else (if r0.1 < 30 then 0 else (if r0.1 < 31 then 0 else 4))))) else 0) := by
      intro r0; fin_cases r0 <;> rfl
    simp only [hvals, Fin.sum_univ_def]
    rfl

private lemma a_small :
    a 2 = 191 ∧ a 3 = 257 ∧ a 4 = 381 ∧ a 5 = 542 ∧ a 6 = 793 ∧ a 7 = 1166 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [a_ge2_eq 0]; simp only [dp0_eq_tbl, wEnd_eq_tbl, Fin.sum_univ_def]; rfl
  · rw [a_ge2_eq 1]; simp only [dp1_eq_tbl, wEnd_eq_tbl, Fin.sum_univ_def]; rfl
  · rw [a_ge2_eq 2]; simp only [dp2_eq_tbl, wEnd_eq_tbl, Fin.sum_univ_def]; rfl
  · rw [a_ge2_eq 3]; simp only [dp3_eq_tbl, wEnd_eq_tbl, Fin.sum_univ_def]; rfl
  · rw [a_ge2_eq 4]; simp only [dp4_eq_tbl, wEnd_eq_tbl, Fin.sum_univ_def]; rfl
  · rw [a_ge2_eq 5]; simp only [dp5_eq_tbl, wEnd_eq_tbl, Fin.sum_univ_def]; rfl

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

private noncomputable def closedR (n : ℕ) : ℝ :=
  34 + ((2 : ℝ) ^ (-1 - (n : ℤ)) *
    ((1 - Real.sqrt 5) ^ n * (-11 + 53 * Real.sqrt 5) +
     (1 + Real.sqrt 5) ^ n * (11 + 53 * Real.sqrt 5))) / Real.sqrt 5 +
    14 * (1 + (n : ℝ)) + (5 / 2 : ℝ) * (1 + (n : ℝ)) * (2 + (n : ℝ))

private noncomputable def binetB (m : ℕ) : ℝ :=
  ((2 : ℝ) ^ (-1 - (m : ℤ)) *
    ((1 - Real.sqrt 5) ^ m * (-11 + 53 * Real.sqrt 5) +
     (1 + Real.sqrt 5) ^ m * (11 + 53 * Real.sqrt 5))) / Real.sqrt 5

private lemma binetB_rec (m : ℕ) : binetB (m + 2) = binetB (m + 1) + binetB m := by
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  unfold binetB
  rw [← add_div]
  congr 1
  have hp1 : (2 : ℝ) ^ (-1 - ((m + 2 : ℕ) : ℤ)) * 2 = (2 : ℝ) ^ (-1 - ((m + 1 : ℕ) : ℤ)) := by
    rw [← zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0),
        show (-1 - ((m + 2 : ℕ) : ℤ) + 1 : ℤ) = -1 - ((m + 1 : ℕ) : ℤ) by push_cast; ring]
  have hp0 : (2 : ℝ) ^ (-1 - ((m + 2 : ℕ) : ℤ)) * 4 = (2 : ℝ) ^ (-1 - (m : ℤ)) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℤ) by norm_num,
        ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
        show (-1 - ((m + 2 : ℕ) : ℤ) + 2 : ℤ) = -1 - (m : ℤ) by push_cast; ring]
  have hq1 : (1 - Real.sqrt 5) ^ (m + 2) =
      2 * (1 - Real.sqrt 5) ^ (m + 1) + 4 * (1 - Real.sqrt 5) ^ m := by
    have : (1 - Real.sqrt 5) ^ 2 = 2 * (1 - Real.sqrt 5) + 4 := by nlinarith [hsq]
    calc (1 - Real.sqrt 5) ^ (m + 2) = (1 - Real.sqrt 5) ^ m * (1 - Real.sqrt 5) ^ 2 := by ring
      _ = (1 - Real.sqrt 5) ^ m * (2 * (1 - Real.sqrt 5) + 4) := by rw [this]
      _ = 2 * (1 - Real.sqrt 5) ^ (m + 1) + 4 * (1 - Real.sqrt 5) ^ m := by ring
  have hq2 : (1 + Real.sqrt 5) ^ (m + 2) =
      2 * (1 + Real.sqrt 5) ^ (m + 1) + 4 * (1 + Real.sqrt 5) ^ m := by
    have : (1 + Real.sqrt 5) ^ 2 = 2 * (1 + Real.sqrt 5) + 4 := by nlinarith [hsq]
    calc (1 + Real.sqrt 5) ^ (m + 2) = (1 + Real.sqrt 5) ^ m * (1 + Real.sqrt 5) ^ 2 := by ring
      _ = (1 + Real.sqrt 5) ^ m * (2 * (1 + Real.sqrt 5) + 4) := by rw [this]
      _ = 2 * (1 + Real.sqrt 5) ^ (m + 1) + 4 * (1 + Real.sqrt 5) ^ m := by ring
  rw [hq1, hq2, ← hp1, ← hp0]; ring

private lemma closedR_eq (m : ℕ) :
    closedR m = 34 + binetB m + 14 * (1 + (m : ℝ)) + (5 / 2 : ℝ) * (1 + (m : ℝ)) * (2 + (m : ℝ)) :=
  rfl

private lemma closedR_rec (n : ℕ) :
    closedR (n + 5) + 5 * closedR (n + 3) + closedR n =
      4 * closedR (n + 4) + closedR (n + 2) + 2 * closedR (n + 1) := by
  have hB5 : binetB (n + 5) + 5 * binetB (n + 3) + binetB n =
      4 * binetB (n + 4) + binetB (n + 2) + 2 * binetB (n + 1) := by
    have h1 := binetB_rec (n + 3)
    have h2 := binetB_rec (n + 2)
    have h3 := binetB_rec (n + 1)
    have h4 := binetB_rec n
    linarith
  simp only [closedR_eq]
  push_cast
  linarith [hB5]

private lemma closedR_small :
    closedR 2 = 191 ∧ closedR 3 = 257 ∧ closedR 4 = 381 ∧ closedR 5 = 542 ∧ closedR 6 = 793 ∧ closedR 7 = 1166 := by
  have hs5 : Real.sqrt 5 ≠ 0 := by positivity
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hb0 : binetB 0 = 53 := by
    unfold binetB
    rw [div_eq_iff hs5]
    have : (2 : ℝ) ^ (-1 - ((0 : ℕ) : ℤ)) = 1 / 2 := by norm_num
    rw [this]; ring
  have hb1 : binetB 1 = 32 := by
    unfold binetB
    rw [div_eq_iff hs5]
    have : (2 : ℝ) ^ (-1 - ((1 : ℕ) : ℤ)) = 1 / 4 := by norm_num
    rw [this]; ring
  have hb2 : binetB 2 = 85 := by have := binetB_rec 0; linarith
  have hb3 : binetB 3 = 117 := by have := binetB_rec 1; linarith
  have hb4 : binetB 4 = 202 := by have := binetB_rec 2; linarith
  have hb5 : binetB 5 = 319 := by have := binetB_rec 3; linarith
  have hb6 : binetB 6 = 521 := by have := binetB_rec 4; linarith
  have hb7 : binetB 7 = 840 := by have := binetB_rec 5; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [closedR_eq, hb2]; push_cast; norm_num
  · rw [closedR_eq, hb3]; push_cast; norm_num
  · rw [closedR_eq, hb4]; push_cast; norm_num
  · rw [closedR_eq, hb5]; push_cast; norm_num
  · rw [closedR_eq, hb6]; push_cast; norm_num
  · rw [closedR_eq, hb7]; push_cast; norm_num

private lemma a_eq_closedR (n : ℕ) (hn : 1 < n) : (a n : ℝ) = closedR n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases a_small with ⟨ha2, ha3, ha4, ha5, ha6, ha7⟩
    rcases closedR_small with ⟨hc2, hc3, hc4, hc5, hc6, hc7⟩
    by_cases h7 : n ≤ 7
    · interval_cases n <;> simp_all
    · have hm : 3 ≤ n - 5 := by omega
      have hrec := a_rec (n - 5) hm
      have hcrec := closedR_rec (n - 5)
      have h5 : n - 5 + 5 = n := by omega
      have h4 : n - 5 + 4 = n - 1 := by omega
      have h3 : n - 5 + 3 = n - 2 := by omega
      have h2 : n - 5 + 2 = n - 3 := by omega
      have h1 : n - 5 + 1 = n - 4 := by omega
      rw [h5, h4, h3, h2, h1] at hrec hcrec
      have hr : (a n : ℝ) + 5 * (a (n - 2) : ℝ) + (a (n - 5) : ℝ) =
          4 * (a (n - 1) : ℝ) + (a (n - 3) : ℝ) + 2 * (a (n - 4) : ℝ) := by
        exact_mod_cast hrec
      rw [ih (n - 1) (by omega) (by omega), ih (n - 2) (by omega) (by omega),
          ih (n - 3) (by omega) (by omega), ih (n - 4) (by omega) (by omega),
          ih (n - 5) (by omega) (by omega)] at hr
      linarith

private lemma main_proof :
    (PowerSeries.mk fun n => (a n : ℚ)) * ((1 - PowerSeries.X) ^ 3 * (1 - PowerSeries.X - PowerSeries.X ^ 2)) =
      PowerSeries.X * (115 - 269 * PowerSeries.X + 68 * PowerSeries.X ^ 2 +
        193 * PowerSeries.X ^ 3 - 118 * PowerSeries.X ^ 4 + 6 * PowerSeries.X ^ 5) ∧
    ∀ n : ℕ, 1 < n →
      (a n : ℝ) = 34 + ((2 : ℝ) ^ (-1 - (n : ℤ)) *
        ((1 - Real.sqrt 5) ^ n * (-11 + 53 * Real.sqrt 5) +
         (1 + Real.sqrt 5) ^ n * (11 + 53 * Real.sqrt 5))) / Real.sqrt 5 +
        14 * (1 + (n : ℝ)) + (5 / 2 : ℝ) * (1 + (n : ℝ)) * (2 + (n : ℝ)) := by
  constructor
  · set F : PowerSeries ℚ := PowerSeries.mk fun n => (a n : ℚ)
    have hlhs : F * ((1 - PowerSeries.X) ^ 3 * (1 - PowerSeries.X - PowerSeries.X ^ 2)) =
        F - PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 1 * F) +
        PowerSeries.C (5 : ℚ) * (PowerSeries.X ^ 2 * F) -
        PowerSeries.X ^ 3 * F -
        PowerSeries.C (2 : ℚ) * (PowerSeries.X ^ 4 * F) +
        PowerSeries.X ^ 5 * F := by
      have h4 : PowerSeries.C (4 : ℚ) = (4 : PowerSeries ℚ) := rfl
      have h5 : PowerSeries.C (5 : ℚ) = (5 : PowerSeries ℚ) := rfl
      have h2 : PowerSeries.C (2 : ℚ) = (2 : PowerSeries ℚ) := rfl
      rw [h4, h5, h2, pow_one]; ring
    have hrhs : (PowerSeries.X * (115 - 269 * PowerSeries.X + 68 * PowerSeries.X ^ 2 +
          193 * PowerSeries.X ^ 3 - 118 * PowerSeries.X ^ 4 + 6 * PowerSeries.X ^ 5) : PowerSeries ℚ) =
        PowerSeries.C (115 : ℚ) * PowerSeries.X -
        PowerSeries.C (269 : ℚ) * PowerSeries.X ^ 2 +
        PowerSeries.C (68 : ℚ) * PowerSeries.X ^ 3 +
        PowerSeries.C (193 : ℚ) * PowerSeries.X ^ 4 -
        PowerSeries.C (118 : ℚ) * PowerSeries.X ^ 5 +
        PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 6 := by
      have h1 : PowerSeries.C (115 : ℚ) = (115 : PowerSeries ℚ) := rfl
      have h2 : PowerSeries.C (269 : ℚ) = (269 : PowerSeries ℚ) := rfl
      have h3 : PowerSeries.C (68 : ℚ) = (68 : PowerSeries ℚ) := rfl
      have h4 : PowerSeries.C (193 : ℚ) = (193 : PowerSeries ℚ) := rfl
      have h5 : PowerSeries.C (118 : ℚ) = (118 : PowerSeries ℚ) := rfl
      have h6 : PowerSeries.C (6 : ℚ) = (6 : PowerSeries ℚ) := rfl
      rw [h1, h2, h3, h4, h5, h6]; ring
    rw [hlhs, hrhs]
    ext n
    simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq,
      PowerSeries.coeff_X_pow, PowerSeries.coeff_X]
    have ha0 : a 0 = 0 := rfl
    have ha1 := a_one
    rcases a_small with ⟨ha2, ha3, ha4, ha5, ha6, ha7⟩
    by_cases hn7 : n ≤ 7
    · interval_cases n <;> simp [F, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7] <;> norm_num
    · have hrec := a_rec (n - 5) (by omega)
      have h5 : n - 5 + 5 = n := by omega
      have h4 : n - 5 + 4 = n - 1 := by omega
      have h3 : n - 5 + 3 = n - 2 := by omega
      have h2 : n - 5 + 2 = n - 3 := by omega
      have h1 : n - 5 + 1 = n - 4 := by omega
      rw [h5, h4, h3, h2, h1] at hrec
      have hq : (a n : ℚ) + 5 * (a (n - 2) : ℚ) + (a (n - 5) : ℚ) =
          4 * (a (n - 1) : ℚ) + (a (n - 3) : ℚ) + 2 * (a (n - 4) : ℚ) := by
        exact_mod_cast hrec
      simp only [F, PowerSeries.coeff_mk, show n ≠ 1 by omega, show n ≠ 2 by omega,
        show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega,
        show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
        show 4 ≤ n by omega, show 5 ≤ n by omega, ↓reduceIte, mul_zero, sub_zero, add_zero]
      linarith
  · exact a_eq_closedR

end OMA.P_oeis_a224673

theorem OMA.solution : type_of% @OMA.S_oeis_a224673.main := OMA.P_oeis_a224673.main_proof
