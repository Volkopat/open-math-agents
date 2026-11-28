import OMAStatements.S_oeis_a273389

-- Problem: A273389: Number of active (ON, black) cells at stage 2^n-1 of the two-dimensional cellular automaton defined by Rule 662
-- Credit: @Qwer2077 (the owner of the agent is credited as the solver)

open OMA.S_oeis_a273389

namespace OMA.Proof_oeis_a273389

private abbrev c (t : ℕ) (x y : ℤ) : Bool := cell 662 t x y

private lemma abs_le_abs_add_one (z : ℤ) : |z| ≤ |z + 1| + 1 := by
  have h : |(z + 1) - 1| ≤ |z + 1| + |(1 : ℤ)| := abs_sub (z + 1) 1
  have h1 : (z + 1) - 1 = z := by ring
  have h2 : |(1 : ℤ)| = 1 := by norm_num
  rw [h1, h2] at h
  exact h

private lemma abs_le_abs_sub_one (z : ℤ) : |z| ≤ |z - 1| + 1 := by
  have h : |(z - 1) + 1| ≤ |z - 1| + |(1 : ℤ)| := abs_add_le (z - 1) 1
  have h1 : (z - 1) + 1 = z := by ring
  have h2 : |(1 : ℤ)| = 1 := by norm_num
  rw [h1, h2] at h
  exact h

private lemma cell_zero_outside (t : ℕ) (x y : ℤ) (h : (t : ℤ) < |x| + |y|) :
    c t x y = false := by
  induction t generalizing x y with
  | zero =>
    simp only [c, cell, decide_eq_false_iff_not, not_and]
    intro hx hy
    subst hx; subst hy
    simp at h
  | succ t ih =>
    push_cast at h
    have h0 : (t : ℤ) < |x| + |y| := by omega
    have h1 : (t : ℤ) < |x + 1| + |y| := by linarith [abs_le_abs_add_one x]
    have h2 : (t : ℤ) < |x - 1| + |y| := by linarith [abs_le_abs_sub_one x]
    have h3 : (t : ℤ) < |x| + |y + 1| := by linarith [abs_le_abs_add_one y]
    have h4 : (t : ℤ) < |x| + |y - 1| := by linarith [abs_le_abs_sub_one y]
    dsimp only [c] at ih ⊢
    simp only [cell]
    rw [ih x y h0, ih (x + 1) y h1, ih (x - 1) y h2, ih x (y + 1) h3, ih x (y - 1) h4]
    decide

private lemma cell_neg_x (t : ℕ) (x y : ℤ) : c t (-x) y = c t x y := by
  induction t generalizing x y with
  | zero =>
    simp [c, cell]
  | succ t ih =>
    dsimp only [c] at ih ⊢
    simp only [cell]
    have h1 : -x + 1 = -(x - 1) := by ring
    have h2 : -x - 1 = -(x + 1) := by ring
    rw [h1, h2, ih x y, ih (x - 1) y, ih (x + 1) y, ih x (y + 1), ih x (y - 1)]
    congr 2
    omega

private lemma cell_neg_y (t : ℕ) (x y : ℤ) : c t x (-y) = c t x y := by
  induction t generalizing x y with
  | zero =>
    simp [c, cell]
  | succ t ih =>
    dsimp only [c] at ih ⊢
    simp only [cell]
    have h1 : -y + 1 = -(y - 1) := by ring
    have h2 : -y - 1 = -(y + 1) := by ring
    rw [h1, h2, ih x y, ih (x + 1) y, ih (x - 1) y, ih x (y - 1), ih x (y + 1)]
    congr 2
    omega

private lemma cell_swap (t : ℕ) (x y : ℤ) : c t y x = c t x y := by
  induction t generalizing x y with
  | zero =>
    simp [c, cell, and_comm]
  | succ t ih =>
    dsimp only [c] at ih ⊢
    simp only [cell]
    rw [ih x y, ih x (y + 1), ih x (y - 1), ih (x + 1) y, ih (x - 1) y]
    congr 2
    omega

private lemma cell_abs (t : ℕ) (x y : ℤ) : c t |x| |y| = c t x y := by
  rcases le_or_gt 0 x with hx | hx <;> rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hx, abs_of_nonneg hy]
  · rw [abs_of_nonneg hx, abs_of_neg hy, cell_neg_y]
  · rw [abs_of_neg hx, abs_of_nonneg hy, cell_neg_x]
  · rw [abs_of_neg hx, abs_of_neg hy, cell_neg_x, cell_neg_y]

private lemma cell_local {t1 t2 : ℕ} {x1 y1 x2 y2 : ℤ}
    (h0 : c t1 x1 y1 = c t2 x2 y2)
    (h1 : c t1 (x1 + 1) y1 = c t2 (x2 + 1) y2)
    (h2 : c t1 (x1 - 1) y1 = c t2 (x2 - 1) y2)
    (h3 : c t1 x1 (y1 + 1) = c t2 x2 (y2 + 1))
    (h4 : c t1 x1 (y1 - 1) = c t2 x2 (y2 - 1)) :
    c (t1 + 1) x1 y1 = c (t2 + 1) x2 y2 := by
  dsimp only [c] at h0 h1 h2 h3 h4 ⊢
  simp only [cell]
  rw [h0, h1, h2, h3, h4]

private lemma rule662_bit (b e w n s : Bool) :
    (662 : ℕ).testBit (b.toNat + 2 * (e.toNat + w.toNat + n.toNat + s.toNat)) =
      xor (xor b (xor (xor n s) (xor e w)))
          (xor (xor (n && s) (e && w)) ((xor n s) && (xor e w))) := by
  cases b <;> cases e <;> cases w <;> cases n <;> cases s <;> decide

private def getRow (rs : List ℕ) (y : ℕ) : ℕ := rs.getD y 0

private def stepRow (b n s : ℕ) : ℕ :=
  let e := b >>> 1
  let w := (b <<< 1) ||| ((b >>> 1) &&& 1)
  let u0 := n ^^^ s
  let u1 := n &&& s
  let v0 := e ^^^ w
  let v1 := e &&& w
  let b0 := u0 ^^^ v0
  let b1 := u1 ^^^ v1 ^^^ (u0 &&& v0)
  b ^^^ b0 ^^^ b1

private lemma stepRow_zero : stepRow 0 0 0 = 0 := by decide

private def stepRowsAux (prev : ℕ) : List ℕ → List ℕ
  | [] => [stepRow 0 0 prev]
  | b :: rest =>
    let n := rest.headD 0
    stepRow b n prev :: stepRowsAux b rest

private def stepRows : List ℕ → List ℕ
  | [] => []
  | r0 :: rest =>
    let r1 := rest.headD 0
    stepRow r0 r1 r1 :: stepRowsAux r0 rest

private lemma getRow_stepRowsAux (prev : ℕ) (xs : List ℕ) (k : ℕ) :
    getRow (stepRowsAux prev xs) k =
      stepRow (getRow xs k) (getRow xs (k + 1)) (if k = 0 then prev else getRow xs (k - 1)) := by
  induction xs generalizing prev k with
  | nil =>
    cases k with
    | zero => simp [stepRowsAux, getRow]
    | succ k => simp [stepRowsAux, getRow, stepRow_zero]
  | cons b rest ih =>
    cases k with
    | zero =>
      cases rest <;> simp [stepRowsAux, getRow]
    | succ k =>
      cases k with
      | zero => simpa [stepRowsAux, getRow] using ih b 0
      | succ k' => simpa [stepRowsAux, getRow] using ih b (k' + 1)

private lemma getRow_stepRows (r0 : ℕ) (rest : List ℕ) (y : ℕ) :
    getRow (stepRows (r0 :: rest)) y =
      stepRow (getRow (r0 :: rest) y) (getRow (r0 :: rest) (y + 1))
        (if y = 0 then getRow (r0 :: rest) 1 else getRow (r0 :: rest) (y - 1)) := by
  cases y with
  | zero => cases rest <;> simp [stepRows, getRow]
  | succ k =>
    cases k with
    | zero => simpa [stepRows, getRow] using getRow_stepRowsAux r0 rest 0
    | succ k' => simpa [stepRows, getRow] using getRow_stepRowsAux r0 rest (k' + 1)

private def rowsAt : ℕ → List ℕ
  | 0 => [1]
  | t + 1 => stepRows (rowsAt t)

private lemma rowsAt_ne_nil (t : ℕ) : rowsAt t ≠ [] := by
  induction t with
  | zero => simp [rowsAt]
  | succ t ih =>
    cases h : rowsAt t with
    | nil => exact (ih h).elim
    | cons a l => simp [rowsAt, h, stepRows]

private lemma testBit_stepRow (b n s x : ℕ) :
    (stepRow b n s).testBit x =
      (662 : ℕ).testBit ((b.testBit x).toNat + 2 * ((b.testBit (x + 1)).toNat +
        (if x = 0 then b.testBit 1 else b.testBit (x - 1)).toNat +
        (n.testBit x).toNat + (s.testBit x).toNat)) := by
  have he : (b >>> 1).testBit x = b.testBit (x + 1) := by
    rw [Nat.testBit_shiftRight, Nat.add_comm]
  have hw : ((b <<< 1) ||| ((b >>> 1) &&& 1)).testBit x =
      if x = 0 then b.testBit 1 else b.testBit (x - 1) := by
    rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
    cases x with
    | zero => simp
    | succ k =>
      have h1 : (1 : ℕ).testBit (k + 1) = false := by
        rw [Nat.testBit_eq_false_of_lt]
        have : 2 ≤ 2 ^ (k + 1) := by
          calc (2 : ℕ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      simp [h1]
  simp only [stepRow, Nat.testBit_xor, Nat.testBit_and, he, hw]
  exact (rule662_bit (b.testBit x) (b.testBit (x + 1))
    (if x = 0 then b.testBit 1 else b.testBit (x - 1)) (n.testBit x) (s.testBit x)).symm

private lemma cell_eq_rowsAt (t x y : ℕ) :
    c t (x : ℤ) (y : ℤ) = (getRow (rowsAt t) y).testBit x := by
  induction t generalizing x y with
  | zero =>
    cases y with
    | zero =>
      cases x with
      | zero => decide
      | succ k =>
        have h1 : (1 : ℕ).testBit (k + 1) = false := by
          rw [Nat.testBit_eq_false_of_lt]
          have : 2 ≤ 2 ^ (k + 1) := by
            calc (2 : ℕ) = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        simp [c, cell, rowsAt, getRow, h1]
        omega
    | succ y =>
      simp [c, cell, rowsAt, getRow]
      omega
  | succ t ih =>
    cases hr : rowsAt t with
    | nil => exact (rowsAt_ne_nil t hr).elim
    | cons r0 rest =>
      have hrow : getRow (rowsAt (t + 1)) y =
          stepRow (getRow (rowsAt t) y) (getRow (rowsAt t) (y + 1))
            (if y = 0 then getRow (rowsAt t) 1 else getRow (rowsAt t) (y - 1)) := by
        simp only [rowsAt, hr]
        exact getRow_stepRows r0 rest y
      rw [hrow, testBit_stepRow]
      dsimp only [c] at ih ⊢
      simp only [cell]
      have h0 : cell 662 t (x : ℤ) (y : ℤ) = (getRow (rowsAt t) y).testBit x := ih x y
      have he : cell 662 t ((x : ℤ) + 1) (y : ℤ) = (getRow (rowsAt t) y).testBit (x + 1) := by
        simpa [Nat.cast_add] using ih (x + 1) y
      have hw : cell 662 t ((x : ℤ) - 1) (y : ℤ) =
          if x = 0 then (getRow (rowsAt t) y).testBit 1 else (getRow (rowsAt t) y).testBit (x - 1) := by
        cases x with
        | zero =>
          have hneg : cell 662 t (-1 : ℤ) (y : ℤ) = cell 662 t (1 : ℤ) (y : ℤ) := by
            simpa using cell_neg_x t 1 (y : ℤ)
          simpa [hneg] using ih 1 y
        | succ k =>
          have hsub : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by push_cast; ring
          simpa [hsub] using ih k y
      have hn : cell 662 t (x : ℤ) ((y : ℤ) + 1) = (getRow (rowsAt t) (y + 1)).testBit x := by
        simpa [Nat.cast_add] using ih x (y + 1)
      have hs : cell 662 t (x : ℤ) ((y : ℤ) - 1) =
          (if y = 0 then getRow (rowsAt t) 1 else getRow (rowsAt t) (y - 1)).testBit x := by
        cases y with
        | zero =>
          have hneg : cell 662 t (x : ℤ) (-1 : ℤ) = cell 662 t (x : ℤ) (1 : ℤ) := by
            simpa using cell_neg_y t (x : ℤ) 1
          simpa [hneg] using ih x 1
        | succ k =>
          have hsub : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by push_cast; ring
          simpa [hsub] using ih x k
      rw [h0, he, hw, hn, hs]

private def hist : ℕ → List (List ℕ)
  | 0 => [[1]]
  | t + 1 =>
    match hist t with
    | [] => [[1]]
    | cur :: rest => stepRows cur :: cur :: rest

private lemma hist_head (t : ℕ) : ∃ rest, hist t = rowsAt t :: rest := by
  induction t with
  | zero => exact ⟨[], rfl⟩
  | succ t ih =>
    rcases ih with ⟨rest, h⟩
    exact ⟨rowsAt t :: rest, by simp [hist, h, rowsAt]⟩

private lemma hist_getD (N t : ℕ) (ht : t ≤ N) :
    (hist N).getD (N - t) [] = rowsAt t := by
  induction N with
  | zero =>
    have : t = 0 := by omega
    subst this; rfl
  | succ N ih =>
    rcases hist_head N with ⟨rest, hN⟩
    have hstep : hist (N + 1) = rowsAt (N + 1) :: hist N := by
      simp [hist, hN, rowsAt]
    by_cases heq : t = N + 1
    · subst heq; simp [hstep]
    · have htN : t ≤ N := by omega
      have hsub : N + 1 - t = (N - t) + 1 := by omega
      rw [hstep, hsub]
      simpa using ih htN

private def checkInt (r1 r2 : List ℕ) (t : ℕ) : Bool :=
  (List.range (t - 22 + 1)).all fun y =>
    let k := t - 22 - y + 1
    getRow r1 y % 2 ^ k == getRow r2 y % 2 ^ k

private def checkUp (r1 r2 : List ℕ) (t : ℕ) : Bool :=
  (List.range (t + 1)).all fun y =>
    if y < 11 then true else getRow r1 (y + 8) == getRow r2 y

private def checkVper (r : List ℕ) (t : ℕ) : Bool :=
  (List.range (t - 28 + 1)).all fun y =>
    if y < 10 then true else
      let k := t - 28 - y + 1
      getRow r (y + 8) % 2 ^ k == getRow r y % 2 ^ k

private def checkDper (r : List ℕ) (t : ℕ) : Bool :=
  (List.range (t + 1)).all fun y =>
    if y < 10 then true else
      (getRow r y >>> 18) == (getRow r (y + 8) >>> 10)

private def countBits (r : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => countBits r k + (if r.testBit k then 1 else 0)

private def countQuad (rs : List ℕ) (t : ℕ) : ℕ :=
  let rowWeight (y : ℕ) : ℕ :=
    let r := getRow rs y
    let c0 := if r.testBit 0 then 1 else 0
    let rest := countBits (r >>> 1) t
    c0 + 2 * rest
  rowWeight 0 + 2 * ((List.range t).map (fun k => rowWeight (k + 1))).sum

private def countSq11_18 (rs : List ℕ) : ℕ :=
  ((List.range 8).map fun dy =>
    countBits (getRow rs (11 + dy) >>> 11) 8).sum

private def checkEverything : Bool :=
  let h := hist 81
  let baseOk := (List.range 8).all fun i =>
    let t := 66 + i
    let rt := h.getD (81 - t) []
    let rt8 := h.getD (81 - (t + 8)) []
    checkInt rt8 rt t && checkUp rt8 rt t && checkVper rt t && checkDper rt t
  baseOk
    && (countQuad (h.getD (81 - 63) []) 63 == 5037)
    && (countQuad (h.getD (81 - 71) []) 71 == 6393)
    && (countQuad (h.getD (81 - 79) []) 79 == 7909)
    && (countSq11_18 (h.getD (81 - 71) []) == 40)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 20000 in
private lemma check_everything_ok : checkEverything = true := by decide

private def HInt (t : ℕ) : Prop :=
  ∀ x y : ℤ, |x| + |y| ≤ (t : ℤ) - 22 → c (t + 8) x y = c t x y

private def HUp (t : ℕ) : Prop :=
  ∀ x y : ℤ, 11 ≤ y → c (t + 8) x (y + 8) = c t x y

private def HVper (t : ℕ) : Prop :=
  ∀ x y : ℤ, 10 ≤ y → |x| + y + 8 ≤ (t : ℤ) - 20 → c t x (y + 8) = c t x y

private def HDper (t : ℕ) : Prop :=
  ∀ x y : ℤ, 10 ≤ x → 10 ≤ y → c t (x + 8) y = c t x (y + 8)

private lemma hRight_of_hUp {t : ℕ} (h : HUp t) (x y : ℤ) (hx : 11 ≤ x) :
    c (t + 8) (x + 8) y = c t x y := by
  rw [← cell_swap (t + 8) (x + 8) y, ← cell_swap t x y]
  exact h y x hx

private lemma hDown_of_hUp {t : ℕ} (h : HUp t) (x y : ℤ) (hy : y ≤ -11) :
    c (t + 8) x (y - 8) = c t x y := by
  have h1 : -(y - 8) = -y + 8 := by ring
  rw [← cell_neg_y (t + 8) x (y - 8), h1, ← cell_neg_y t x y]
  exact h x (-y) (by omega)

private lemma hLeft_of_hUp {t : ℕ} (h : HUp t) (x y : ℤ) (hx : x ≤ -11) :
    c (t + 8) (x - 8) y = c t x y := by
  have h1 : -(x - 8) = -x + 8 := by ring
  rw [← cell_neg_x (t + 8) (x - 8) y, h1, ← cell_neg_x t x y]
  exact hRight_of_hUp h (-x) y (by omega)

private lemma checkInt_sound {t : ℕ} (ht : 22 ≤ t)
    (h : checkInt (rowsAt (t + 8)) (rowsAt t) t = true) : HInt t := by
  intro x y hxy
  rw [← cell_abs (t + 8) x y, ← cell_abs t x y]
  lift |x| to ℕ using abs_nonneg x with nx hnx
  lift |y| to ℕ using abs_nonneg y with ny hny
  rw [cell_eq_rowsAt, cell_eq_rowsAt]
  have hny_lt : ny ∈ List.range (t - 22 + 1) := by
    rw [List.mem_range]; omega
  have hrow := List.all_eq_true.mp h ny hny_lt
  simp only [beq_iff_eq] at hrow
  have hkx : nx < t - 22 - ny + 1 := by omega
  have h1 : (getRow (rowsAt (t + 8)) ny % 2 ^ (t - 22 - ny + 1)).testBit nx =
      (getRow (rowsAt (t + 8)) ny).testBit nx := by
    rw [Nat.testBit_mod_two_pow]; simp [hkx]
  have h2 : (getRow (rowsAt t) ny % 2 ^ (t - 22 - ny + 1)).testBit nx =
      (getRow (rowsAt t) ny).testBit nx := by
    rw [Nat.testBit_mod_two_pow]; simp [hkx]
  rw [← h1, ← h2, hrow]

private lemma checkUp_sound {t : ℕ}
    (h : checkUp (rowsAt (t + 8)) (rowsAt t) t = true) : HUp t := by
  intro x y hy
  rw [← cell_abs (t + 8) x (y + 8), ← cell_abs t x y]
  have hy0 : 0 ≤ y := by omega
  have hy8 : 0 ≤ y + 8 := by omega
  rw [abs_of_nonneg hy8, abs_of_nonneg hy0]
  lift |x| to ℕ using abs_nonneg x with nx hnx
  lift y to ℕ using hy0 with ny hny
  by_cases hyt : ny ≤ t
  · have hmem : ny ∈ List.range (t + 1) := by rw [List.mem_range]; omega
    have hrow := List.all_eq_true.mp h ny hmem
    have hge : ¬ (ny < 11) := by omega
    simp only [hge, ↓reduceIte, beq_iff_eq] at hrow
    have hcast : ((ny : ℤ) + 8) = ((ny + 8 : ℕ) : ℤ) := by push_cast; ring
    rw [hcast, cell_eq_rowsAt, cell_eq_rowsAt, hrow]
  · have h1 : c (t + 8) (nx : ℤ) ((ny : ℤ) + 8) = false := by
      apply cell_zero_outside
      rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]
      omega
    have h2 : c t (nx : ℤ) (ny : ℤ) = false := by
      apply cell_zero_outside
      rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]
      omega
    rw [h1, h2]

private lemma checkVper_sound {t : ℕ} (ht : 28 ≤ t)
    (h : checkVper (rowsAt t) t = true) : HVper t := by
  intro x y hy hxy
  rw [← cell_abs t x (y + 8), ← cell_abs t x y]
  have hy0 : 0 ≤ y := by omega
  have hy8 : 0 ≤ y + 8 := by omega
  rw [abs_of_nonneg hy8, abs_of_nonneg hy0]
  lift |x| to ℕ using abs_nonneg x with nx hnx
  lift y to ℕ using hy0 with ny hny
  have hcast : ((ny : ℤ) + 8) = ((ny + 8 : ℕ) : ℤ) := by push_cast; ring
  rw [hcast, cell_eq_rowsAt, cell_eq_rowsAt]
  have hmem : ny ∈ List.range (t - 28 + 1) := by rw [List.mem_range]; omega
  have hrow := List.all_eq_true.mp h ny hmem
  have hge : ¬ (ny < 10) := by omega
  simp only [hge, ↓reduceIte, beq_iff_eq] at hrow
  have hkx : nx < t - 28 - ny + 1 := by omega
  have h1 : (getRow (rowsAt t) (ny + 8) % 2 ^ (t - 28 - ny + 1)).testBit nx =
      (getRow (rowsAt t) (ny + 8)).testBit nx := by
    rw [Nat.testBit_mod_two_pow]; simp [hkx]
  have h2 : (getRow (rowsAt t) ny % 2 ^ (t - 28 - ny + 1)).testBit nx =
      (getRow (rowsAt t) ny).testBit nx := by
    rw [Nat.testBit_mod_two_pow]; simp [hkx]
  rw [← h1, ← h2, hrow]

private lemma checkDper_sound {t : ℕ}
    (h : checkDper (rowsAt t) t = true) : HDper t := by
  intro x y hx hy
  lift x to ℕ using (by omega) with nx hnx
  lift y to ℕ using (by omega) with ny hny
  by_cases hyt : ny ≤ t
  · have hmem : ny ∈ List.range (t + 1) := by rw [List.mem_range]; omega
    have hrow := List.all_eq_true.mp h ny hmem
    have hge : ¬ (ny < 10) := by omega
    simp only [hge, ↓reduceIte, beq_iff_eq] at hrow
    obtain ⟨k, rfl⟩ : ∃ k, nx = k + 10 := ⟨nx - 10, by omega⟩
    have hc1 : ((k + 10 : ℕ) : ℤ) + 8 = ((k + 18 : ℕ) : ℤ) := by push_cast; ring
    have hc2 : (ny : ℤ) + 8 = ((ny + 8 : ℕ) : ℤ) := by push_cast; ring
    rw [hc1, hc2, cell_eq_rowsAt, cell_eq_rowsAt]
    have h1 : (getRow (rowsAt t) ny).testBit (k + 18) = (getRow (rowsAt t) ny >>> 18).testBit k := by
      rw [Nat.testBit_shiftRight, Nat.add_comm 18 k]
    have h2 : (getRow (rowsAt t) (ny + 8)).testBit (k + 10) =
        (getRow (rowsAt t) (ny + 8) >>> 10).testBit k := by
      rw [Nat.testBit_shiftRight, Nat.add_comm 10 k]
    rw [h1, h2, hrow]
  · have h1 : c t ((nx : ℤ) + 8) (ny : ℤ) = false := by
      apply cell_zero_outside
      rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]
      omega
    have h2 : c t (nx : ℤ) ((ny : ℤ) + 8) = false := by
      apply cell_zero_outside
      rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]
      omega
    rw [h1, h2]

private lemma base_invariants (t : ℕ) (ht1 : 66 ≤ t) (ht2 : t ≤ 73) :
    HInt t ∧ HUp t ∧ HVper t ∧ HDper t := by
  have hall := check_everything_ok
  simp only [checkEverything, Bool.and_eq_true] at hall
  have hbase := hall.1.1.1.1
  have hi : t - 66 ∈ List.range 8 := by rw [List.mem_range]; omega
  have hstep := List.all_eq_true.mp hbase (t - 66) hi
  have ht_eq : 66 + (t - 66) = t := by omega
  simp only [ht_eq, Bool.and_eq_true] at hstep
  rw [hist_getD 81 t (by omega), hist_getD 81 (t + 8) (by omega)] at hstep
  exact ⟨checkInt_sound (by omega) hstep.1.1.1,
         checkUp_sound hstep.1.1.2,
         checkVper_sound (by omega) hstep.1.2,
         checkDper_sound hstep.2⟩

private lemma all_invariants (t : ℕ) (ht : 66 ≤ t) :
    HInt t ∧ HUp t ∧ HVper t ∧ HDper t := by
  induction t using Nat.strong_induction_on with
  | h m ih =>
    by_cases hbase : m ≤ 73
    · exact base_invariants m ht hbase
    · obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
      have ht73 : 73 ≤ t := by omega
      obtain ⟨hInt_t, hUp_t, hVper_t, hDper_t⟩ := ih t (by omega) (by omega)
      obtain ⟨hInt_7, hUp_7, hVper_7, hDper_7⟩ := ih (t - 7) (by omega) (by omega)
      have h7_add : t - 7 + 8 = t + 1 := by omega
      have hInt7 : ∀ x y : ℤ, |x| + |y| ≤ ((t - 7 : ℕ) : ℤ) - 22 → c (t + 1) x y = c (t - 7) x y := by
        simpa [HInt, h7_add] using hInt_7
      have hUp7 : ∀ x y : ℤ, 11 ≤ y → c (t + 1) x (y + 8) = c (t - 7) x y := by
        simpa [HUp, h7_add] using hUp_7
      have hRight7 : ∀ x y : ℤ, 11 ≤ x → c (t + 1) (x + 8) y = c (t - 7) x y := by
        intro x y hx
        simpa [h7_add] using hRight_of_hUp hUp_7 x y hx
      -- 1. Prove HVper (t + 1)
      have hVper_next : HVper (t + 1) := by
        intro x y hy hxy
        rw [← cell_abs (t + 1) x (y + 8), ← cell_abs (t + 1) x y]
        rw [abs_of_nonneg (a := y + 8) (by omega), abs_of_nonneg (a := y) (by omega)]
        set ax := |x|
        have hax0 : 0 ≤ ax := abs_nonneg x
        by_cases hy19 : 19 ≤ y
        · rw [hUp7 ax y (by omega)]
          have h1 : c (t + 1) ax y = c (t - 7) ax (y - 8) := by
            have := hUp7 ax (y - 8) (by omega)
            rwa [show y - 8 + 8 = y by ring] at this
          rw [h1]
          have := hVper_7 ax (y - 8) (by omega) (by rw [abs_of_nonneg hax0]; omega)
          rwa [show y - 8 + 8 = y by ring] at this
        · by_cases hx19 : 19 ≤ ax
          · have h1 : c (t + 1) ax (y + 8) = c (t - 7) (ax - 8) (y + 8) := by
              have := hRight7 (ax - 8) (y + 8) (by omega)
              rwa [show ax - 8 + 8 = ax by ring] at this
            have h2 : c (t + 1) ax y = c (t - 7) (ax - 8) y := by
              have := hRight7 (ax - 8) y (by omega)
              rwa [show ax - 8 + 8 = ax by ring] at this
            rw [h1, h2]
            exact hVper_7 (ax - 8) y hy (by rw [abs_of_nonneg (by omega)]; omega)
          · rw [hInt7 ax (y + 8) (by rw [abs_of_nonneg hax0, abs_of_nonneg (by omega)]; omega)]
            rw [hInt7 ax y (by rw [abs_of_nonneg hax0, abs_of_nonneg (by omega)]; omega)]
            exact hVper_7 ax y hy (by rw [abs_of_nonneg hax0]; omega)
      -- 2. Prove HDper (t + 1)
      have hDper_next : HDper (t + 1) := by
        intro x y hx hy
        by_cases h11 : 11 ≤ x ∧ 11 ≤ y
        · rw [hRight7 x y h11.1, hUp7 x y h11.2]
        · by_cases hy19 : 19 ≤ y
          · have h1 : c (t + 1) (x + 8) y = c (t - 7) (x + 8) (y - 8) := by
              have := hUp7 (x + 8) (y - 8) (by omega)
              rwa [show y - 8 + 8 = y by ring] at this
            rw [h1, hUp7 x y (by omega)]
            have := hDper_7 x (y - 8) hx (by omega)
            rwa [show y - 8 + 8 = y by ring] at this
          · by_cases hx19 : 19 ≤ x
            · have h1 : c (t + 1) (x + 8) y = c (t - 7) x y := hRight7 x y (by omega)
              have h2 : c (t + 1) x (y + 8) = c (t - 7) (x - 8) (y + 8) := by
                have := hRight7 (x - 8) (y + 8) (by omega)
                rwa [show x - 8 + 8 = x by ring] at this
              rw [h1, h2]
              have := hDper_7 (x - 8) y (by omega) hy
              rwa [show x - 8 + 8 = x by ring] at this
            · rw [hInt7 (x + 8) y (by rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]; omega)]
              rw [hInt7 x (y + 8) (by rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)]; omega)]
              exact hDper_7 x y hx hy
      -- 3. Prove HInt (t + 1)
      have hInt_next : HInt (t + 1) := by
        intro x y hxy
        have hstep_pt : ∀ u v : ℤ, |u| + |v| ≤ (t : ℤ) - 20 → c (t + 8) u v = c t u v := by
          intro u v huv
          by_cases hin : |u| + |v| ≤ (t : ℤ) - 22
          · exact hInt_t u v hin
          · rw [← cell_abs (t + 8) u v, ← cell_abs t u v]
            set au := |u|
            set av := |v|
            have hau0 : 0 ≤ au := abs_nonneg u
            have hav0 : 0 ≤ av := abs_nonneg v
            by_cases hmax : au ≤ av
            · have hav19 : 19 ≤ av := by omega
              have h1 : c (t + 8) au av = c t au (av - 8) := by
                have := hUp_t au (av - 8) (by omega)
                rwa [show av - 8 + 8 = av by ring] at this
              have h2 : c t au av = c t au (av - 8) := by
                have := hVper_t au (av - 8) (by omega) (by rw [abs_of_nonneg hau0]; omega)
                rwa [show av - 8 + 8 = av by ring] at this
              rw [h1, h2]
            · have hau19 : 19 ≤ au := by omega
              rw [← cell_swap (t + 8) au av, ← cell_swap t au av]
              have h1 : c (t + 8) av au = c t av (au - 8) := by
                have := hUp_t av (au - 8) (by omega)
                rwa [show au - 8 + 8 = au by ring] at this
              have h2 : c t av au = c t av (au - 8) := by
                have := hVper_t av (au - 8) (by omega) (by rw [abs_of_nonneg hav0]; omega)
                rwa [show au - 8 + 8 = au by ring] at this
              rw [h1, h2]
        have hnbr : ∀ dx dy : ℤ, |dx| + |dy| ≤ 1 → |x + dx| + |y + dy| ≤ (t : ℤ) - 20 := by
          intro dx dy hd
          have h1 : |x + dx| ≤ |x| + |dx| := abs_add_le x dx
          have h2 : |y + dy| ≤ |y| + |dy| := abs_add_le y dy
          omega
        change c ((t + 8) + 1) x y = c (t + 1) x y
        exact cell_local
          (hstep_pt x y (by omega))
          (hstep_pt (x + 1) y (by simpa using hnbr 1 0 (by norm_num)))
          (hstep_pt (x - 1) y (by simpa [sub_eq_add_neg] using hnbr (-1) 0 (by norm_num)))
          (hstep_pt x (y + 1) (by simpa using hnbr 0 1 (by norm_num)))
          (hstep_pt x (y - 1) (by simpa [sub_eq_add_neg] using hnbr 0 (-1) (by norm_num)))
      -- 4. Prove HUp (t + 1)
      have hUp_next : HUp (t + 1) := by
        intro x y hy
        have hstep_pt : ∀ u v : ℤ, 10 ≤ v → c (t + 8) u (v + 8) = c t u v := by
          intro u v hv
          by_cases hv11 : 11 ≤ v
          · exact hUp_t u v hv11
          · have hv10 : v = 10 := by omega
            subst hv10
            rw [← cell_abs (t + 8) u (10 + 8), ← cell_abs t u 10]
            rw [abs_of_nonneg (a := (10 : ℤ) + 8) (by norm_num),
                abs_of_nonneg (a := (10 : ℤ)) (by norm_num)]
            set au := |u|
            have hau0 : 0 ≤ au := abs_nonneg u
            by_cases hau19 : 19 ≤ au
            · have h1 : c (t + 8) au (10 + 8) = c t (au - 8) (10 + 8) := by
                have := hRight_of_hUp hUp_t (au - 8) (10 + 8) (by omega)
                rwa [show au - 8 + 8 = au by ring] at this
              have h2 : c t au 10 = c t (au - 8) (10 + 8) := by
                have := hDper_t (au - 8) 10 (by omega) (by omega)
                rwa [show au - 8 + 8 = au by ring] at this
              rw [h1, h2]
            · rw [hInt_t au (10 + 8) (by rw [abs_of_nonneg hau0, abs_of_nonneg (by norm_num)]; omega)]
              exact hVper_t au 10 (by omega) (by rw [abs_of_nonneg hau0]; omega)
        change c ((t + 8) + 1) x (y + 8) = c (t + 1) x y
        exact cell_local
          (hstep_pt x y (by omega))
          (hstep_pt (x + 1) y (by omega))
          (hstep_pt (x - 1) y (by omega))
          (by simpa [add_assoc, add_comm, add_left_comm] using hstep_pt x (y + 1) (by omega))
          (by
            have := hstep_pt x (y - 1) (by omega)
            rwa [show y - 1 + 8 = y + 8 - 1 by ring] at this)
      exact ⟨hInt_next, hUp_next, hVper_next, hDper_next⟩

-- Counting infrastructure
private def ind (t : ℕ) (x y : ℤ) : ℕ := if c t x y then 1 else 0

private def rectSum (t : ℕ) (X Y : Finset ℤ) : ℕ :=
  ∑ x ∈ X, ∑ y ∈ Y, ind t x y

private lemma ind_zero_outside {t : ℕ} {x y : ℤ} (h : (t : ℤ) < |x| + |y|) :
    ind t x y = 0 := by
  simp [ind, cell_zero_outside t x y h]

private lemma ind_neg_x (t : ℕ) (x y : ℤ) : ind t (-x) y = ind t x y := by
  simp [ind, cell_neg_x]

private lemma ind_neg_y (t : ℕ) (x y : ℤ) : ind t x (-y) = ind t x y := by
  simp [ind, cell_neg_y]

private lemma sum_range_shift_eq_Icc (t : ℕ) (f : ℤ → ℕ) :
    (∑ i ∈ Finset.range (2 * t + 1), f ((i : ℤ) - (t : ℤ))) =
      ∑ x ∈ Finset.Icc (-(t : ℤ)) (t : ℤ), f x := by
  refine Finset.sum_bij (fun i _ => (i : ℤ) - (t : ℤ)) ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [Finset.mem_Icc]
    omega
  · intro i1 _ i2 _ h
    omega
  · intro x hx
    rw [Finset.mem_Icc] at hx
    exact ⟨(x + t).toNat, by rw [Finset.mem_range]; omega, by omega⟩
  · intro _ _; rfl

private lemma onCount_eq_rectSum (t : ℕ) :
    onCount 662 t = rectSum t (Finset.Icc (-(t : ℤ)) (t : ℤ)) (Finset.Icc (-(t : ℤ)) (t : ℤ)) := by
  unfold onCount rectSum ind c
  rw [sum_range_shift_eq_Icc t (fun x =>
    ∑ j ∈ Finset.range (2 * t + 1), if cell 662 t x ((j : ℤ) - (t : ℤ)) then 1 else 0)]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact sum_range_shift_eq_Icc t (fun y => if cell 662 t x y then 1 else 0)

private lemma sum_Icc_split {a b d : ℤ} (hab : a ≤ b) (hbd : b < d) (f : ℤ → ℕ) :
    ∑ x ∈ Finset.Icc a d, f x =
      (∑ x ∈ Finset.Icc a b, f x) + ∑ x ∈ Finset.Icc (b + 1) d, f x := by
  have hunion : Finset.Icc a d = Finset.Icc a b ∪ Finset.Icc (b + 1) d := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc a b) (Finset.Icc (b + 1) d) := by
    rw [Finset.disjoint_left]; intro x hx1 hx2; simp only [Finset.mem_Icc] at hx1 hx2; omega
  rw [hunion, Finset.sum_union hdisj]

private lemma sum_Icc_shift (a b k : ℤ) (f : ℤ → ℕ) :
    ∑ x ∈ Finset.Icc (a + k) (b + k), f x = ∑ x ∈ Finset.Icc a b, f (x + k) := by
  refine Finset.sum_bij (fun x _ => x - k) ?_ ?_ ?_ ?_
  · intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
  · intro x1 _ x2 _ h; omega
  · intro y hy; simp only [Finset.mem_Icc] at hy
    exact ⟨y + k, by simp [Finset.mem_Icc]; omega, by ring⟩
  · intro x _; congr 1; ring

private lemma sum_Icc_neg (a b : ℤ) (f : ℤ → ℕ) :
    ∑ x ∈ Finset.Icc (-b) (-a), f x = ∑ x ∈ Finset.Icc a b, f (-x) := by
  refine Finset.sum_bij (fun x _ => -x) ?_ ?_ ?_ ?_
  · intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
  · intro x1 _ x2 _ h; omega
  · intro y hy; simp only [Finset.mem_Icc] at hy
    exact ⟨-y, by simp [Finset.mem_Icc]; omega, by ring⟩
  · intro x _; congr 1; ring

private lemma rectSum_extend_x {t M : ℕ} (htM : t ≤ M) (Y : Finset ℤ) :
    rectSum t (Finset.Icc (-(M : ℤ)) (M : ℤ)) Y = rectSum t (Finset.Icc (-(t : ℤ)) (t : ℤ)) Y := by
  unfold rectSum
  symm
  refine Finset.sum_subset ?_ ?_
  · intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
  · intro x hxM hxt
    simp only [Finset.mem_Icc] at hxM hxt
    refine Finset.sum_eq_zero fun y _ => ind_zero_outside ?_
    have hy0 : 0 ≤ |y| := abs_nonneg y
    have hax : (t : ℤ) < |x| := by
      rw [lt_abs]
      omega
    omega

private lemma rectSum_symm_y (t : ℕ) (X : Finset ℤ) (a b : ℤ) :
    rectSum t X (Finset.Icc (-b) (-a)) = rectSum t X (Finset.Icc a b) := by
  unfold rectSum
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [sum_Icc_neg]
  refine Finset.sum_congr rfl fun y _ => ind_neg_y t x y

private lemma rectSum_symm_x (t : ℕ) (a b : ℤ) (Y : Finset ℤ) :
    rectSum t (Finset.Icc (-b) (-a)) Y = rectSum t (Finset.Icc a b) Y := by
  unfold rectSum
  rw [sum_Icc_neg]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ind_neg_x t x y

private lemma rectSum_step_up {t : ℕ} (ht : 66 ≤ t) :
    rectSum (t + 8) (Finset.Icc (-((t + 8 : ℕ) : ℤ)) ((t + 8 : ℕ) : ℤ))
      (Finset.Icc 19 ((t + 8 : ℕ) : ℤ)) =
    rectSum t (Finset.Icc (-(t : ℤ)) (t : ℤ)) (Finset.Icc 11 (t : ℤ)) := by
  have hUp := (all_invariants t ht).2.1
  have h1 : rectSum (t + 8) (Finset.Icc (-((t + 8 : ℕ) : ℤ)) ((t + 8 : ℕ) : ℤ))
      (Finset.Icc 19 ((t + 8 : ℕ) : ℤ)) =
      rectSum t (Finset.Icc (-((t + 8 : ℕ) : ℤ)) ((t + 8 : ℕ) : ℤ)) (Finset.Icc 11 (t : ℤ)) := by
    unfold rectSum
    refine Finset.sum_congr rfl fun x _ => ?_
    have hshift := sum_Icc_shift 11 (t : ℤ) 8 (fun y => ind (t + 8) x y)
    have heq1 : (11 : ℤ) + 8 = 19 := by norm_num
    have heq2 : (t : ℤ) + 8 = ((t + 8 : ℕ) : ℤ) := by push_cast; ring
    rw [heq1, heq2] at hshift
    rw [hshift]
    refine Finset.sum_congr rfl fun y hy => ?_
    simp only [Finset.mem_Icc] at hy
    simp only [ind, hUp x y hy.1]
  rw [h1, rectSum_extend_x (by omega)]

private lemma rectSum_step_right {t : ℕ} (ht : 66 ≤ t) (Y : Finset ℤ) :
    rectSum (t + 8) (Finset.Icc 19 ((t + 8 : ℕ) : ℤ)) Y =
      rectSum t (Finset.Icc 11 (t : ℤ)) Y := by
  have hUp := (all_invariants t ht).2.1
  unfold rectSum
  have hshift := sum_Icc_shift 11 (t : ℤ) 8 (fun x => ∑ y ∈ Y, ind (t + 8) x y)
  have heq1 : (11 : ℤ) + 8 = 19 := by norm_num
  have heq2 : (t : ℤ) + 8 = ((t + 8 : ℕ) : ℤ) := by push_cast; ring
  rw [heq1, heq2] at hshift
  rw [hshift]
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y _ => ?_
  simp only [Finset.mem_Icc] at hx
  simp only [ind, hRight_of_hUp hUp x y hx.1]

private lemma rectSum_step_int {t : ℕ} (ht : 66 ≤ t) {X Y : Finset ℤ}
    (hX : ∀ x ∈ X, |x| ≤ 18) (hY : ∀ y ∈ Y, |y| ≤ 18) :
    rectSum (t + 8) X Y = rectSum t X Y := by
  have hInt := (all_invariants t ht).1
  unfold rectSum
  refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => ?_
  have hx' := hX x hx
  have hy' := hY y hy
  simp only [ind, hInt x y (by omega)]

private lemma rectSum_union_y (t : ℕ) (X : Finset ℤ) {a b d : ℤ} (hab : a ≤ b) (hbd : b < d) :
    rectSum t X (Finset.Icc a d) =
      rectSum t X (Finset.Icc a b) + rectSum t X (Finset.Icc (b + 1) d) := by
  unfold rectSum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => sum_Icc_split hab hbd (fun y => ind t x y)

private lemma rectSum_union_x (t : ℕ) {a b d : ℤ} (hab : a ≤ b) (hbd : b < d) (Y : Finset ℤ) :
    rectSum t (Finset.Icc a d) Y =
      rectSum t (Finset.Icc a b) Y + rectSum t (Finset.Icc (b + 1) d) Y := by
  unfold rectSum
  exact sum_Icc_split hab hbd (fun x => ∑ y ∈ Y, ind t x y)

private lemma onCount_step8 {t : ℕ} (ht : 66 ≤ t) :
    onCount 662 (t + 8) = onCount 662 t +
      2 * rectSum t (Finset.Icc (-(t : ℤ)) (t : ℤ)) (Finset.Icc 11 18) +
      2 * rectSum t (Finset.Icc 11 18) (Finset.Icc (-18) 18) := by
  rw [onCount_eq_rectSum (t + 8), onCount_eq_rectSum t]
  set M : ℤ := ((t + 8 : ℕ) : ℤ)
  set T : ℤ := (t : ℤ)
  have hyM1 := rectSum_union_y (t + 8) (Finset.Icc (-M) M) (a := -M) (b := -19) (d := M) (by omega) (by omega)
  have hyM2 := rectSum_union_y (t + 8) (Finset.Icc (-M) M) (a := -18) (b := 18) (d := M) (by omega) (by omega)
  have hxM1 := rectSum_union_x (t + 8) (a := -M) (b := -19) (d := M) (by omega) (by omega) (Finset.Icc (-18) 18)
  have hxM2 := rectSum_union_x (t + 8) (a := -18) (b := 18) (d := M) (by omega) (by omega) (Finset.Icc (-18) 18)
  have htop : rectSum (t + 8) (Finset.Icc (-M) M) (Finset.Icc 19 M) =
      rectSum t (Finset.Icc (-T) T) (Finset.Icc 11 T) := rectSum_step_up ht
  have hbot : rectSum (t + 8) (Finset.Icc (-M) M) (Finset.Icc (-M) (-19)) =
      rectSum t (Finset.Icc (-T) T) (Finset.Icc 11 T) := by
    rw [rectSum_symm_y, htop]
  have hright : rectSum (t + 8) (Finset.Icc 19 M) (Finset.Icc (-18) 18) =
      rectSum t (Finset.Icc 11 T) (Finset.Icc (-18) 18) := rectSum_step_right ht _
  have hleft : rectSum (t + 8) (Finset.Icc (-M) (-19)) (Finset.Icc (-18) 18) =
      rectSum t (Finset.Icc 11 T) (Finset.Icc (-18) 18) := by
    rw [rectSum_symm_x, hright]
  have hmid : rectSum (t + 8) (Finset.Icc (-18) 18) (Finset.Icc (-18) 18) =
      rectSum t (Finset.Icc (-18) 18) (Finset.Icc (-18) 18) := by
    apply rectSum_step_int ht
    · intro x hx; simp only [Finset.mem_Icc] at hx; rw [abs_le]; omega
    · intro y hy; simp only [Finset.mem_Icc] at hy; rw [abs_le]; omega
  have hyT1 := rectSum_union_y t (Finset.Icc (-T) T) (a := -T) (b := -19) (d := T) (by omega) (by omega)
  have hyT2 := rectSum_union_y t (Finset.Icc (-T) T) (a := -18) (b := 18) (d := T) (by omega) (by omega)
  have hxT1 := rectSum_union_x t (a := -T) (b := -19) (d := T) (by omega) (by omega) (Finset.Icc (-18) 18)
  have hxT2 := rectSum_union_x t (a := -18) (b := 18) (d := T) (by omega) (by omega) (Finset.Icc (-18) 18)
  have hyT_bot : rectSum t (Finset.Icc (-T) T) (Finset.Icc (-T) (-19)) =
      rectSum t (Finset.Icc (-T) T) (Finset.Icc 19 T) := rectSum_symm_y t _ 19 T
  have hxT_left : rectSum t (Finset.Icc (-T) (-19)) (Finset.Icc (-18) 18) =
      rectSum t (Finset.Icc 19 T) (Finset.Icc (-18) 18) := rectSum_symm_x t 19 T _
  have hsplit_y : rectSum t (Finset.Icc (-T) T) (Finset.Icc 11 T) =
      rectSum t (Finset.Icc (-T) T) (Finset.Icc 11 18) +
      rectSum t (Finset.Icc (-T) T) (Finset.Icc 19 T) :=
    rectSum_union_y t _ (a := 11) (b := 18) (d := T) (by omega) (by omega)
  have hsplit_x : rectSum t (Finset.Icc 11 T) (Finset.Icc (-18) 18) =
      rectSum t (Finset.Icc 11 18) (Finset.Icc (-18) 18) +
      rectSum t (Finset.Icc 19 T) (Finset.Icc (-18) 18) :=
    rectSum_union_x t (a := 11) (b := 18) (d := T) (by omega) (by omega) _
  norm_num at hyM1 hyM2 hxM1 hxM2 hyT1 hyT2 hxT1 hxT2
  linarith

private lemma strip_step8 {t : ℕ} (ht : 66 ≤ t) :
    rectSum (t + 8) (Finset.Icc (-((t + 8 : ℕ) : ℤ)) ((t + 8 : ℕ) : ℤ)) (Finset.Icc 11 18) =
      rectSum t (Finset.Icc (-(t : ℤ)) (t : ℤ)) (Finset.Icc 11 18) +
      2 * rectSum t (Finset.Icc 11 18) (Finset.Icc 11 18) := by
  set M : ℤ := ((t + 8 : ℕ) : ℤ)
  set T : ℤ := (t : ℤ)
  set Y := Finset.Icc (11 : ℤ) 18
  have hxM1 := rectSum_union_x (t + 8) (a := -M) (b := -19) (d := M) (by omega) (by omega) Y
  have hxM2 := rectSum_union_x (t + 8) (a := -18) (b := 18) (d := M) (by omega) (by omega) Y
  have hxT1 := rectSum_union_x t (a := -T) (b := -19) (d := T) (by omega) (by omega) Y
  have hxT2 := rectSum_union_x t (a := -18) (b := 18) (d := T) (by omega) (by omega) Y
  have hright : rectSum (t + 8) (Finset.Icc 19 M) Y = rectSum t (Finset.Icc 11 T) Y :=
    rectSum_step_right ht Y
  have hleft : rectSum (t + 8) (Finset.Icc (-M) (-19)) Y = rectSum t (Finset.Icc 11 T) Y := by
    rw [rectSum_symm_x, hright]
  have hmid : rectSum (t + 8) (Finset.Icc (-18) 18) Y = rectSum t (Finset.Icc (-18) 18) Y := by
    apply rectSum_step_int ht
    · intro x hx; simp only [Finset.mem_Icc] at hx; rw [abs_le]; omega
    · intro y hy; simp only [Y, Finset.mem_Icc] at hy; rw [abs_le]; omega
  have hxT_left : rectSum t (Finset.Icc (-T) (-19)) Y = rectSum t (Finset.Icc 19 T) Y :=
    rectSum_symm_x t 19 T Y
  have hsplit_x : rectSum t (Finset.Icc 11 T) Y =
      rectSum t (Finset.Icc 11 18) Y + rectSum t (Finset.Icc 19 T) Y :=
    rectSum_union_x t (a := 11) (b := 18) (d := T) (by omega) (by omega) Y
  norm_num at hxM1 hxM2 hxT1 hxT2
  linarith

private lemma onCount_second_diff {t : ℕ} (ht : 66 ≤ t) :
    onCount 662 (t + 16) + onCount 662 t =
      2 * onCount 662 (t + 8) + 4 * rectSum t (Finset.Icc 11 18) (Finset.Icc 11 18) := by
  have h1 := onCount_step8 ht
  have h2 := onCount_step8 (t := t + 8) (by omega)
  have hstrip := strip_step8 ht
  have hbox : rectSum (t + 8) (Finset.Icc 11 18) (Finset.Icc (-18) 18) =
      rectSum t (Finset.Icc 11 18) (Finset.Icc (-18) 18) := by
    apply rectSum_step_int ht
    · intro x hx; simp only [Finset.mem_Icc] at hx; rw [abs_le]; omega
    · intro y hy; simp only [Finset.mem_Icc] at hy; rw [abs_le]; omega
  have h16 : t + 8 + 8 = t + 16 := by omega
  rw [h16] at h2
  linarith

private lemma sq_const (k : ℕ) (hk : 8 ≤ k) :
    rectSum (8 * k + 7) (Finset.Icc 11 18) (Finset.Icc 11 18) =
      rectSum 71 (Finset.Icc 11 18) (Finset.Icc 11 18) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 8 := ⟨k - 8, by omega⟩
  clear hk
  induction m with
  | zero => rfl
  | succ m ih =>
    have hstep : 8 * (m + 1 + 8) + 7 = (8 * (m + 8) + 7) + 8 := by omega
    rw [hstep]
    have heq : rectSum ((8 * (m + 8) + 7) + 8) (Finset.Icc 11 18) (Finset.Icc 11 18) =
        rectSum (8 * (m + 8) + 7) (Finset.Icc 11 18) (Finset.Icc 11 18) := by
      apply rectSum_step_int (by omega)
      · intro x hx; simp only [Finset.mem_Icc] at hx; rw [abs_le]; omega
      · intro y hy; simp only [Finset.mem_Icc] at hy; rw [abs_le]; omega
    rw [heq, ih]

-- Connect countBits / countQuad / countSq11_18 to onCount / rectSum
private lemma countBits_eq_sum (r m : ℕ) :
    countBits r m = ∑ k ∈ Finset.range m, if r.testBit k then 1 else 0 := by
  induction m with
  | zero => simp [countBits]
  | succ m ih => rw [countBits, Finset.sum_range_succ, ih]

private lemma sum_Icc_even (t : ℕ) (f : ℤ → ℕ) (heven : ∀ x, f (-x) = f x) :
    ∑ x ∈ Finset.Icc (-(t : ℤ)) (t : ℤ), f x =
      f 0 + 2 * ∑ k ∈ Finset.range t, f ((k + 1 : ℕ) : ℤ) := by
  cases t with
  | zero => simp
  | succ t =>
    have h1 := sum_Icc_split (a := -((t + 1 : ℕ) : ℤ)) (b := -1) (d := ((t + 1 : ℕ) : ℤ)) (by omega) (by omega) f
    have h2 := sum_Icc_split (a := (0 : ℤ)) (b := 0) (d := ((t + 1 : ℕ) : ℤ)) (by omega) (by omega) f
    have hneg : ∑ x ∈ Finset.Icc (-((t + 1 : ℕ) : ℤ)) (-1), f x =
        ∑ x ∈ Finset.Icc (1 : ℤ) ((t + 1 : ℕ) : ℤ), f x := by
      rw [sum_Icc_neg]
      exact Finset.sum_congr rfl fun x _ => heven x
    have hpos : ∑ x ∈ Finset.Icc (1 : ℤ) ((t + 1 : ℕ) : ℤ), f x =
        ∑ k ∈ Finset.range (t + 1), f ((k + 1 : ℕ) : ℤ) := by
      refine Finset.sum_bij (fun x _ => (x - 1).toNat) ?_ ?_ ?_ ?_
      · intro x hx; simp only [Finset.mem_Icc] at hx; rw [Finset.mem_range]; omega
      · intro x1 hx1 x2 hx2 h; simp only [Finset.mem_Icc] at hx1 hx2; omega
      · intro k hk; rw [Finset.mem_range] at hk
        exact ⟨((k + 1 : ℕ) : ℤ), by simp [Finset.mem_Icc]; omega, by omega⟩
      · intro x hx; simp only [Finset.mem_Icc] at hx; congr 1; omega
    have hm0 : (-1 : ℤ) + 1 = 0 := by norm_num
    have hp1 : (0 : ℤ) + 1 = 1 := by norm_num
    rw [hm0] at h1
    rw [hp1, Finset.Icc_self, Finset.sum_singleton] at h2
    omega

private lemma list_sum_map_range (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
    simp

private lemma onCount_eq_countQuad (t : ℕ) :
    onCount 662 t = countQuad (rowsAt t) t := by
  rw [onCount_eq_rectSum]
  unfold rectSum
  rw [Finset.sum_comm]
  rw [sum_Icc_even t (fun y => ∑ x ∈ Finset.Icc (-(t : ℤ)) (t : ℤ), ind t x y)
    (fun y => Finset.sum_congr rfl fun x _ => ind_neg_y t x y)]
  have hrow : ∀ y : ℕ,
      (∑ x ∈ Finset.Icc (-(t : ℤ)) (t : ℤ), ind t x (y : ℤ)) =
        (if (getRow (rowsAt t) y).testBit 0 then 1 else 0) +
        2 * countBits (getRow (rowsAt t) y >>> 1) t := by
    intro y
    rw [sum_Icc_even t (fun x => ind t x (y : ℤ)) (fun x => ind_neg_x t x (y : ℤ))]
    rw [countBits_eq_sum]
    have h0 : ind t 0 (y : ℤ) = if (getRow (rowsAt t) y).testBit 0 then 1 else 0 := by
      unfold ind
      rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, cell_eq_rowsAt t 0 y]
    rw [h0]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [ind]
    rw [cell_eq_rowsAt t (k + 1) y, Nat.testBit_shiftRight, Nat.add_comm]
  have hzero : (0 : ℤ) = ((0 : ℕ) : ℤ) := rfl
  rw [hzero, hrow 0]
  dsimp only [countQuad]
  rw [list_sum_map_range]
  congr 2
  refine Finset.sum_congr rfl fun k _ => hrow (k + 1)

private lemma rectSum_sq11_18_eq (t : ℕ) :
    rectSum t (Finset.Icc 11 18) (Finset.Icc 11 18) = countSq11_18 (rowsAt t) := by
  unfold rectSum countSq11_18
  rw [Finset.sum_comm, list_sum_map_range]
  have hy : (∑ y ∈ Finset.Icc (11 : ℤ) 18, ∑ x ∈ Finset.Icc (11 : ℤ) 18, ind t x y) =
      ∑ dy ∈ Finset.range 8, ∑ x ∈ Finset.Icc (11 : ℤ) 18, ind t x ((11 + dy : ℕ) : ℤ) := by
    refine Finset.sum_bij (fun y _ => (y - 11).toNat) ?_ ?_ ?_ ?_
    · intro y hy; simp only [Finset.mem_Icc] at hy; rw [Finset.mem_range]; omega
    · intro y1 hy1 y2 hy2 h; simp only [Finset.mem_Icc] at hy1 hy2; omega
    · intro dy hdy; rw [Finset.mem_range] at hdy
      exact ⟨((11 + dy : ℕ) : ℤ), by simp [Finset.mem_Icc]; omega, by omega⟩
    · intro y hy; simp only [Finset.mem_Icc] at hy
      refine Finset.sum_congr rfl fun x _ => ?_
      congr 1; omega
  rw [hy]
  refine Finset.sum_congr rfl fun dy _ => ?_
  rw [countBits_eq_sum]
  refine Finset.sum_bij (fun x _ => (x - 11).toNat) ?_ ?_ ?_ ?_
  · intro x hx; simp only [Finset.mem_Icc] at hx; rw [Finset.mem_range]; omega
  · intro x1 hx1 x2 hx2 h; simp only [Finset.mem_Icc] at hx1 hx2; omega
  · intro dx hdx; rw [Finset.mem_range] at hdx
    exact ⟨((11 + dx : ℕ) : ℤ), by simp [Finset.mem_Icc]; omega, by omega⟩
  · intro x hx
    simp only [Finset.mem_Icc] at hx
    have hx_eq : x = ((11 + (x - 11).toNat : ℕ) : ℤ) := by omega
    conv_lhs => rw [hx_eq]
    simp only [ind, cell_eq_rowsAt, Nat.testBit_shiftRight]

private lemma base_counts :
    onCount 662 63 = 5037 ∧ onCount 662 71 = 6393 ∧ onCount 662 79 = 7909 ∧
      rectSum 71 (Finset.Icc 11 18) (Finset.Icc 11 18) = 40 := by
  have hall := check_everything_ok
  simp only [checkEverything, Bool.and_eq_true, beq_iff_eq] at hall
  rw [hist_getD 81 63 (by omega), hist_getD 81 71 (by omega), hist_getD 81 79 (by omega)] at hall
  rw [onCount_eq_countQuad 63, onCount_eq_countQuad 71, onCount_eq_countQuad 79, rectSum_sq11_18_eq 71]
  exact ⟨hall.1.1.1.2, hall.1.1.2, hall.1.2, hall.2⟩

private lemma onCount_8k_7 (k : ℕ) (hk : 7 ≤ k) :
    onCount 662 (8 * k + 7) = 80 * k ^ 2 + 156 * k + 25 := by
  obtain ⟨h63, h71, h79, hsq71⟩ := base_counts
  by_cases h7 : k = 7
  · subst h7; simpa using h63
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 8 := ⟨k - 8, by omega⟩
    clear hk h7
    induction m using Nat.strong_induction_on with
    | h m ih =>
      match m with
      | 0 => simpa using h71
      | 1 => simpa using h79
      | r + 2 =>
        have hr0 := ih r (by omega)
        have hr1 := ih (r + 1) (by omega)
        have hsd := onCount_second_diff (t := 8 * (r + 8) + 7) (by omega)
        have hsq := sq_const (r + 8) (by omega)
        rw [hsq71] at hsq
        rw [hsq] at hsd
        have heq1 : 8 * (r + 8) + 7 + 16 = 8 * (r + 2 + 8) + 7 := by omega
        have heq2 : 8 * (r + 8) + 7 + 8 = 8 * (r + 1 + 8) + 7 := by omega
        rw [heq1, heq2, hr0, hr1] at hsd
        nlinarith

end OMA.Proof_oeis_a273389

theorem OMA.solution : type_of% @OMA.S_oeis_a273389.main := by
  intro n hn
  unfold OMA.S_oeis_a273389.a
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have hpow : 2 ^ (m + 6) = 8 * (8 * 2 ^ m) := by ring
  have hk_ge : 7 ≤ 8 * 2 ^ m - 1 := by
    have : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
    omega
  have ht_eq : 2 ^ (m + 6) - 1 = 8 * (8 * 2 ^ m - 1) + 7 := by
    have : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
    omega
  rw [ht_eq, OMA.Proof_oeis_a273389.onCount_8k_7 (8 * 2 ^ m - 1) hk_ge]
  have h1 : 1 ≤ 8 * 2 ^ m := by
    have : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by norm_num)
    omega
  have hsub : m + 6 - 1 = m + 5 := by omega
  rw [hsub]
  push_cast [h1]
  have h4 : (4 : ℚ) ^ (m + 5) = ((2 : ℚ) ^ (m + 5)) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h2 : (2 : ℚ) ^ (m + 5) = 32 * (2 : ℚ) ^ m := by ring
  rw [h4, h2]
  ring
