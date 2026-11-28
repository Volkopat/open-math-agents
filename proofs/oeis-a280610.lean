import OMAStatements.S_oeis_a280610

section Disproof
open OMA.S_oeis_a280610

def lookupL {α : Type} : List α → ℕ → α → α
  | [], _, d => d
  | b :: _, 0, _ => b
  | _ :: bs, i + 1, d => lookupL bs i d

def buildL {α : Type} : ℕ → (ℕ → α) → List α
  | 0, _ => []
  | n + 1, f => f 0 :: buildL n (fun i => f (i + 1))

lemma lookupL_buildL {α : Type} (n : ℕ) (f : ℕ → α) (i : ℕ) (d : α) :
    lookupL (buildL n f) i d = if i < n then f i else d := by
  induction n generalizing f i with
  | zero => simp [buildL, lookupL]
  | succ n ih =>
    cases i with
    | zero => simp [buildL, lookupL]
    | succ i => simp only [buildL, lookupL, ih, Nat.succ_lt_succ_iff]

def evalBox (rows : List (List Bool)) (t : ℕ) (bg : Bool) (x y : ℤ) : Bool :=
  if -↑t ≤ x ∧ x ≤ ↑t ∧ -↑t ≤ y ∧ y ≤ ↑t then
    lookupL (lookupL rows (y + ↑t).toNat []) (x + ↑t).toNat bg
  else bg

lemma evalBox_out (rows : List (List Bool)) (t : ℕ) (bg : Bool) (x y : ℤ)
    (h : ¬(-↑t ≤ x ∧ x ≤ ↑t ∧ -↑t ≤ y ∧ y ≤ ↑t)) :
    evalBox rows t bg x y = bg :=
  if_neg h

def nextCfg (t : ℕ) (c : Bool × List (List Bool)) : Bool × List (List Bool) :=
  let bg := c.1
  let g := evalBox c.2 t bg
  let bg' := Nat.testBit 294 (bg.toNat + 2 * (bg.toNat + bg.toNat + bg.toNat + bg.toNat))
  let rows' := buildL (2 * (t + 1) + 1) fun iy =>
    buildL (2 * (t + 1) + 1) fun ix =>
      step g ((ix : ℤ) - ↑(t + 1)) ((iy : ℤ) - ↑(t + 1))
  (bg', rows')

def cfg : ℕ → Bool × List (List Bool)
  | 0 => (false, [[true]])
  | t + 1 => nextCfg t (cfg t)

lemma state_eq_cfg (t : ℕ) : state t = evalBox (cfg t).2 t (cfg t).1 := by
  induction t with
  | zero =>
    funext x y
    simp only [state, cfg, evalBox, Nat.cast_zero, neg_zero, add_zero]
    by_cases h : 0 ≤ x ∧ x ≤ 0 ∧ 0 ≤ y ∧ y ≤ 0
    · obtain ⟨rfl, rfl⟩ : x = 0 ∧ y = 0 := ⟨by omega, by omega⟩
      simp [lookupL]
    · have hxy : ¬(x = 0 ∧ y = 0) := by omega
      simp [h, hxy]
  | succ t ih =>
    funext x y
    change step (state t) x y = evalBox (nextCfg t (cfg t)).2 (t + 1) (nextCfg t (cfg t)).1 x y
    rw [ih]
    by_cases h : -↑(t + 1) ≤ x ∧ x ≤ ↑(t + 1) ∧ -↑(t + 1) ≤ y ∧ y ≤ ↑(t + 1)
    · unfold evalBox nextCfg
      rw [if_pos h]
      rw [lookupL_buildL, if_pos (by omega : (y + ↑(t + 1)).toNat < 2 * (t + 1) + 1)]
      rw [lookupL_buildL, if_pos (by omega : (x + ↑(t + 1)).toNat < 2 * (t + 1) + 1)]
      have hx : ((x + ↑(t + 1)).toNat : ℤ) - ↑(t + 1) = x := by omega
      have hy : ((y + ↑(t + 1)).toNat : ℤ) - ↑(t + 1) = y := by omega
      rw [hx, hy]
      rfl
    · rw [evalBox_out _ _ _ _ _ h]
      unfold step nextCfg
      rw [evalBox_out _ _ _ x y (by omega),
          evalBox_out _ _ _ (x - 1) y (by omega),
          evalBox_out _ _ _ (x + 1) y (by omega),
          evalBox_out _ _ _ x (y - 1) (by omega),
          evalBox_out _ _ _ x (y + 1) (by omega)]

def sumUp (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => sumUp f k + f k

lemma sum_range_eq_sumUp (f : ℕ → ℕ) (k : ℕ) :
    (∑ i ∈ Finset.range k, f i) = sumUp f k := by
  induction k with
  | zero => simp [sumUp]
  | succ k ih => rw [Finset.sum_range_succ, ih, sumUp]

def aFast (n : ℕ) : ℕ :=
  let c := cfg n
  sumUp (fun i => (evalBox c.2 n c.1 (i : ℤ) 0).toNat * 2 ^ (n - i)) (n + 1)

lemma a_eq_aFast (n : ℕ) : a n = aFast n := by
  unfold a aFast
  rw [state_eq_cfg, sum_range_eq_sumUp]

end Disproof

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 200000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a280610.main) := by
  rintro ⟨_, hrec⟩
  have h6 := hrec 6 (by decide)
  have v6 : OMA.S_oeis_a280610.a 6 = 65 :=
    (a_eq_aFast 6).trans (by decide)
  have v5 : OMA.S_oeis_a280610.a 5 = 39 :=
    (a_eq_aFast 5).trans (by decide)
  have v4 : OMA.S_oeis_a280610.a 4 = 17 :=
    (a_eq_aFast 4).trans (by decide)
  have v3 : OMA.S_oeis_a280610.a 3 = 7 :=
    (a_eq_aFast 3).trans (by decide)
  norm_num [v6, v5, v4, v3] at h6
