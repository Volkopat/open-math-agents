import OMAStatements.S_oeis_a282679

section Disproof_oeis_a282679
open OMA.S_oeis_a282679

def applyR (r : ℕ) (c n s w e : Bool) : Bool :=
  Nat.testBit r (c.toNat + 2 * (w.toNat + e.toNat + n.toNat + s.toNat))

def lookupL {α : Type} : List α → ℕ → α → α
  | [], _, d => d
  | b :: _, 0, _ => b
  | _ :: bs, i + 1, d => lookupL bs i d

lemma lookupL_map {α β : Type} (f : α → β) (xs : List α) (i : ℕ) (da : α) (db : β)
    (hi : i < xs.length) :
    lookupL (xs.map f) i db = f (lookupL xs i da) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons _ xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (by simp at hi; omega)

lemma lookupL_append {α : Type} (xs ys : List α) (i : ℕ) (d : α) :
    lookupL (xs ++ ys) i d =
      if i < xs.length then lookupL xs i d else lookupL ys (i - xs.length) d := by
  induction xs generalizing i with
  | nil => simp
  | cons _ xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.cons_append, lookupL, List.length_cons,
        Nat.succ_lt_succ_iff, Nat.succ_sub_succ_eq_sub, ih]

lemma lookupL_replicate_same {α : Type} (n i : ℕ) (v : α) :
    lookupL (List.replicate n v) i v = v := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

lemma lookupL_out {α : Type} (xs : List α) (i : ℕ) (d : α) (h : xs.length ≤ i) :
    lookupL xs i d = d := by
  induction xs generalizing i with
  | nil => rfl
  | cons _ xs ih =>
    cases i with
    | zero => simp at h
    | succ i => exact ih i (by simp at h; omega)

lemma lookupL_in_mem {α : Type} (xs : List α) (i : ℕ) (d : α) (hi : i < xs.length) :
    lookupL xs i d ∈ xs := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp [lookupL]
    | succ i => exact List.mem_cons_of_mem x (ih i (by simp at hi; omega))

lemma lookupL_congr_default {α : Type} (xs : List α) (i : ℕ) (d1 d2 : α) (hi : i < xs.length) :
    lookupL xs i d1 = lookupL xs i d2 := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons _ xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (by simp at hi; omega)

def pad1 {α : Type} (v : α) (xs : List α) : List α :=
  v :: v :: (xs ++ [v, v])

lemma length_pad1 {α : Type} (v : α) (xs : List α) : (pad1 v xs).length = xs.length + 4 := by
  simp [pad1]

lemma lookupL_pad1 {α : Type} (v : α) (xs : List α) (n i : ℕ) (h : xs.length = n) :
    lookupL (pad1 v xs) i v = if 2 ≤ i ∧ i < n + 2 then lookupL xs (i - 2) v else v := by
  subst h
  cases i with
  | zero => simp [pad1, lookupL]
  | succ i =>
    cases i with
    | zero => simp [pad1, lookupL]
    | succ j =>
      simp only [pad1, lookupL, lookupL_append]
      by_cases hj : j < xs.length
      · have hcond : 2 ≤ j + 1 + 1 ∧ j + 1 + 1 < xs.length + 2 := by omega
        simp [hj, hcond]
      · have hcond : ¬(2 ≤ j + 1 + 1 ∧ j + 1 + 1 < xs.length + 2) := by omega
        simp only [if_neg hj, if_neg hcond]
        rcases (show j - xs.length = 0 ∨ j - xs.length = 1 ∨ 2 ≤ j - xs.length by omega) with
          h0 | h1 | h2
        · rw [h0]; rfl
        · rw [h1]; rfl
        · exact lookupL_out [v, v] (j - xs.length) v (by simp; omega)

def stepRow3 (r : ℕ) : List Bool → List Bool → List Bool → List Bool
  | _ :: n :: ns, w :: c :: e :: cs, _ :: s :: ss =>
      applyR r c n s w e :: stepRow3 r (n :: ns) (c :: e :: cs) (s :: ss)
  | _, _, _ => []

lemma length_stepRow3 (r : ℕ) (r1 r2 r3 : List Bool) (n : ℕ)
    (h1 : r1.length = n + 2) (h2 : r2.length = n + 2) (h3 : r3.length = n + 2) :
    (stepRow3 r r1 r2 r3).length = n := by
  induction n generalizing r1 r2 r3 with
  | zero =>
    match r2 with
    | [_, _] => simp [stepRow3]
    | [] | [_] | _ :: _ :: _ :: _ => simp at h2
  | succ n ih =>
    match r1, r2, r3 with
    | _ :: b1 :: cs1, _ :: b2 :: c2 :: cs2, _ :: b3 :: cs3 =>
      simp only [stepRow3, List.length_cons]
      rw [ih (b1 :: cs1) (b2 :: c2 :: cs2) (b3 :: cs3)
        (by simp at h1 ⊢; omega) (by simp at h2 ⊢; omega) (by simp at h3 ⊢; omega)]
    | [], _, _ | [_], _, _ => simp at h1
    | _, [], _ | _, [_], _ | _, [_, _], _ => simp at h2
    | _, _, [] | _, _, [_] => simp at h3

lemma lookupL_stepRow3 (r : ℕ) (r1 r2 r3 : List Bool) (n i : ℕ) (d : Bool)
    (h1 : r1.length = n + 2) (h2 : r2.length = n + 2) (h3 : r3.length = n + 2) (hi : i < n) :
    lookupL (stepRow3 r r1 r2 r3) i d =
      applyR r (lookupL r2 (i + 1) d) (lookupL r1 (i + 1) d) (lookupL r3 (i + 1) d)
        (lookupL r2 i d) (lookupL r2 (i + 2) d) := by
  induction i generalizing r1 r2 r3 n with
  | zero =>
    rcases n with _ | n
    · omega
    match r1, r2, r3 with
    | _ :: _ :: _, _ :: _ :: _ :: _, _ :: _ :: _ => rfl
    | [], _, _ | [_], _, _ => simp at h1
    | _, [], _ | _, [_], _ | _, [_, _], _ => simp at h2
    | _, _, [] | _, _, [_] => simp at h3
  | succ i ih =>
    rcases n with _ | n
    · omega
    match r1, r2, r3 with
    | _ :: b1 :: cs1, _ :: b2 :: c2 :: cs2, _ :: b3 :: cs3 =>
      simp only [stepRow3, lookupL]
      exact ih (b1 :: cs1) (b2 :: c2 :: cs2) (b3 :: cs3) n
        (by simp at h1 ⊢; omega) (by simp at h2 ⊢; omega) (by simp at h3 ⊢; omega) (by omega)

def stepGrid (r : ℕ) : List (List Bool) → List (List Bool)
  | r1 :: r2 :: r3 :: rs => stepRow3 r r1 r2 r3 :: stepGrid r (r2 :: r3 :: rs)
  | _ => []

lemma length_stepGrid (r : ℕ) (ps : List (List Bool)) (m w : ℕ)
    (hlen : ps.length = m + 2) (hrow : ∀ row ∈ ps, row.length = w + 2) :
    (stepGrid r ps).length = m ∧ ∀ row ∈ stepGrid r ps, row.length = w := by
  induction m generalizing ps with
  | zero =>
    match ps with
    | [_, _] => simp [stepGrid]
    | [] | [_] | _ :: _ :: _ :: _ => simp at hlen
  | succ m ih =>
    match ps with
    | r1 :: r2 :: r3 :: rs =>
      have hr1 : r1.length = w + 2 := hrow r1 (by simp)
      have hr2 : r2.length = w + 2 := hrow r2 (by simp)
      have hr3 : r3.length = w + 2 := hrow r3 (by simp)
      have hsub := ih (r2 :: r3 :: rs) (by simp at hlen ⊢; omega)
        (fun row hr => hrow row (List.mem_cons_of_mem r1 hr))
      simp only [stepGrid, List.length_cons, hsub.1, true_and, List.mem_cons]
      rintro row (rfl | hr)
      · exact length_stepRow3 r r1 r2 r3 w hr1 hr2 hr3
      · exact hsub.2 row hr
    | [] | [_] | [_, _] => simp at hlen

lemma lookupL_stepGrid (r : ℕ) (ps : List (List Bool)) (m w iy ix : ℕ) (bg : Bool)
    (hlen : ps.length = m + 2) (hrow : ∀ row ∈ ps, row.length = w + 2)
    (hiy : iy < m) (hix : ix < w) :
    lookupL (lookupL (stepGrid r ps) iy []) ix bg =
      applyR r (lookupL (lookupL ps (iy + 1) []) (ix + 1) bg)
        (lookupL (lookupL ps iy []) (ix + 1) bg)
        (lookupL (lookupL ps (iy + 2) []) (ix + 1) bg)
        (lookupL (lookupL ps (iy + 1) []) ix bg)
        (lookupL (lookupL ps (iy + 1) []) (ix + 2) bg) := by
  induction iy generalizing ps m with
  | zero =>
    rcases m with _ | m
    · omega
    match ps with
    | r1 :: r2 :: r3 :: rs =>
      simp only [stepGrid, lookupL]
      exact lookupL_stepRow3 r r1 r2 r3 w ix bg
        (hrow r1 (by simp)) (hrow r2 (by simp)) (hrow r3 (by simp)) hix
    | [] | [_] | [_, _] => simp at hlen
  | succ iy ih =>
    rcases m with _ | m
    · omega
    match ps with
    | r1 :: r2 :: r3 :: rs =>
      simp only [stepGrid, lookupL]
      exact ih (r2 :: r3 :: rs) m (by simp at hlen ⊢; omega)
        (fun row hr => hrow row (List.mem_cons_of_mem r1 hr)) (by omega)

def evalBox (rows : List (List Bool)) (t : ℕ) (bg : Bool) (x y : ℤ) : Bool :=
  if -↑t ≤ x ∧ x ≤ ↑t ∧ -↑t ≤ y ∧ y ≤ ↑t then
    lookupL (lookupL rows (y + ↑t).toNat []) (x + ↑t).toNat bg
  else bg

lemma evalBox_out (rows : List (List Bool)) (t : ℕ) (bg : Bool) (x y : ℤ)
    (h : ¬(-↑t ≤ x ∧ x ≤ ↑t ∧ -↑t ≤ y ∧ y ≤ ↑t)) :
    evalBox rows t bg x y = bg :=
  if_neg h

def nextCfg (r t : ℕ) (c : Bool × List (List Bool)) : Bool × List (List Bool) :=
  let bg := c.1
  let bg' := applyR r bg bg bg bg bg
  let blank := List.replicate (2 * t + 5) bg
  let padded := pad1 blank (c.2.map (pad1 bg))
  (bg', stepGrid r padded)

def cfg (r : ℕ) : ℕ → Bool × List (List Bool)
  | 0 => (false, [[true]])
  | t + 1 => nextCfg r t (cfg r t)

def CfgWf (t : ℕ) (c : Bool × List (List Bool)) : Prop :=
  c.2.length = 2 * t + 1 ∧ ∀ row ∈ c.2, row.length = 2 * t + 1

lemma padded_wf (t : ℕ) (c : Bool × List (List Bool)) (hwf : CfgWf t c) :
    let blank := List.replicate (2 * t + 5) c.1
    let padded := pad1 blank (c.2.map (pad1 c.1))
    padded.length = (2 * (t + 1) + 1) + 2 ∧
      ∀ row ∈ padded, row.length = (2 * (t + 1) + 1) + 2 := by
  dsimp only
  refine ⟨by rw [length_pad1, List.length_map, hwf.1]; omega, ?_⟩
  intro row hr
  simp only [pad1, List.mem_cons, List.mem_append, List.mem_map] at hr
  rcases hr with rfl | rfl | ⟨⟨row0, hmem, rfl⟩ | hr2⟩
  · simp; omega
  · simp; omega
  · simp [hwf.2 row0 hmem]; omega
  · simp only [List.not_mem_nil, or_false] at hr2
    rcases hr2 with rfl | rfl <;> (simp; omega)

lemma cfg_wf (r t : ℕ) : CfgWf t (cfg r t) := by
  induction t with
  | zero => simp [CfgWf, cfg]
  | succ t ih =>
    unfold CfgWf cfg nextCfg
    dsimp only
    have hp := padded_wf t (cfg r t) ih
    exact length_stepGrid r _ (2 * (t + 1) + 1) (2 * (t + 1) + 1) hp.1 hp.2

lemma lookupL_padded (t : ℕ) (c : Bool × List (List Bool)) (hwf : CfgWf t c) (ky kx : ℕ) :
    lookupL (lookupL (pad1 (List.replicate (2 * t + 5) c.1) (c.2.map (pad1 c.1))) ky []) kx c.1 =
      evalBox c.2 t c.1 ((kx : ℤ) - ↑t - 2) ((ky : ℤ) - ↑t - 2) := by
  set blank := List.replicate (2 * t + 5) c.1
  have hmap_len : (c.2.map (pad1 c.1)).length = 2 * t + 1 := by simp [hwf.1]
  have hp_len : (pad1 blank (c.2.map (pad1 c.1))).length = 2 * t + 5 := by
    rw [length_pad1, hmap_len]
  have hswap : lookupL (lookupL (pad1 blank (c.2.map (pad1 c.1))) ky []) kx c.1 =
      lookupL (lookupL (pad1 blank (c.2.map (pad1 c.1))) ky blank) kx c.1 := by
    by_cases hky : ky < 2 * t + 5
    · rw [lookupL_congr_default _ ky [] blank (by omega)]
    · rw [lookupL_out _ ky [] (by omega), lookupL_out _ ky blank (by omega),
          lookupL_replicate_same]
      rfl
  rw [hswap, lookupL_pad1 blank (c.2.map (pad1 c.1)) (2 * t + 1) ky hmap_len]
  by_cases hky : 2 ≤ ky ∧ ky < (2 * t + 1) + 2
  · rw [if_pos hky, lookupL_map (pad1 c.1) c.2 (ky - 2) [] blank (by rw [hwf.1]; omega)]
    have hrow_len : (lookupL c.2 (ky - 2) []).length = 2 * t + 1 :=
      hwf.2 _ (lookupL_in_mem c.2 (ky - 2) [] (by rw [hwf.1]; omega))
    rw [lookupL_pad1 c.1 _ (2 * t + 1) kx hrow_len]
    unfold evalBox
    by_cases hkx : 2 ≤ kx ∧ kx < (2 * t + 1) + 2
    · have hbox : -(t : ℤ) ≤ (kx : ℤ) - ↑t - 2 ∧ (kx : ℤ) - ↑t - 2 ≤ ↑t ∧
          -(t : ℤ) ≤ (ky : ℤ) - ↑t - 2 ∧ (ky : ℤ) - ↑t - 2 ≤ ↑t := by omega
      rw [if_pos hkx, if_pos hbox]
      have ey : ((ky : ℤ) - ↑t - 2 + ↑t).toNat = ky - 2 := by omega
      have ex : ((kx : ℤ) - ↑t - 2 + ↑t).toNat = kx - 2 := by omega
      rw [ey, ex]
    · have hbox : ¬(-(t : ℤ) ≤ (kx : ℤ) - ↑t - 2 ∧ (kx : ℤ) - ↑t - 2 ≤ ↑t ∧
          -(t : ℤ) ≤ (ky : ℤ) - ↑t - 2 ∧ (ky : ℤ) - ↑t - 2 ≤ ↑t) := by omega
      rw [if_neg hkx, if_neg hbox]
  · rw [if_neg hky, lookupL_replicate_same]
    unfold evalBox
    have hbox : ¬(-(t : ℤ) ≤ (kx : ℤ) - ↑t - 2 ∧ (kx : ℤ) - ↑t - 2 ≤ ↑t ∧
        -(t : ℤ) ≤ (ky : ℤ) - ↑t - 2 ∧ (ky : ℤ) - ↑t - 2 ≤ ↑t) := by omega
    rw [if_neg hbox]

lemma state_eq_cfg (r t : ℕ) : state r t = evalBox (cfg r t).2 t (cfg r t).1 := by
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
    change step r (state r t) x y = evalBox (nextCfg r t (cfg r t)).2 (t + 1) (nextCfg r t (cfg r t)).1 x y
    rw [ih]
    by_cases h : -↑(t + 1) ≤ x ∧ x ≤ ↑(t + 1) ∧ -↑(t + 1) ≤ y ∧ y ≤ ↑(t + 1)
    · unfold evalBox nextCfg
      dsimp only
      rw [if_pos h]
      have hwf := cfg_wf r t
      have hp := padded_wf t (cfg r t) hwf
      have hiy : (y + ↑(t + 1)).toNat < 2 * (t + 1) + 1 := by omega
      have hix : (x + ↑(t + 1)).toNat < 2 * (t + 1) + 1 := by omega
      rw [lookupL_stepGrid r _ (2 * (t + 1) + 1) (2 * (t + 1) + 1) _ _ _ hp.1 hp.2 hiy hix]
      have chg : ∀ ky kx, ky < (2 * (t + 1) + 1) + 2 → kx < (2 * (t + 1) + 1) + 2 →
          lookupL (lookupL (pad1 (List.replicate (2 * t + 5) (cfg r t).1)
            ((cfg r t).2.map (pad1 (cfg r t).1))) ky []) kx
            (applyR r (cfg r t).1 (cfg r t).1 (cfg r t).1 (cfg r t).1 (cfg r t).1) =
          lookupL (lookupL (pad1 (List.replicate (2 * t + 5) (cfg r t).1)
            ((cfg r t).2.map (pad1 (cfg r t).1))) ky []) kx (cfg r t).1 := by
        intro ky kx hky hkx
        have hrmem := lookupL_in_mem _ ky [] (by rw [hp.1]; exact hky)
        exact lookupL_congr_default _ kx _ _ (by rw [hp.2 _ hrmem]; exact hkx)
      rw [chg ((y + ↑(t + 1)).toNat + 1) ((x + ↑(t + 1)).toNat + 1) (by omega) (by omega),
          chg (y + ↑(t + 1)).toNat ((x + ↑(t + 1)).toNat + 1) (by omega) (by omega),
          chg ((y + ↑(t + 1)).toNat + 2) ((x + ↑(t + 1)).toNat + 1) (by omega) (by omega),
          chg ((y + ↑(t + 1)).toNat + 1) (x + ↑(t + 1)).toNat (by omega) (by omega),
          chg ((y + ↑(t + 1)).toNat + 1) ((x + ↑(t + 1)).toNat + 2) (by omega) (by omega)]
      rw [lookupL_padded t (cfg r t) hwf ((y + ↑(t + 1)).toNat + 1) ((x + ↑(t + 1)).toNat + 1),
          lookupL_padded t (cfg r t) hwf (y + ↑(t + 1)).toNat ((x + ↑(t + 1)).toNat + 1),
          lookupL_padded t (cfg r t) hwf ((y + ↑(t + 1)).toNat + 2) ((x + ↑(t + 1)).toNat + 1),
          lookupL_padded t (cfg r t) hwf ((y + ↑(t + 1)).toNat + 1) (x + ↑(t + 1)).toNat,
          lookupL_padded t (cfg r t) hwf ((y + ↑(t + 1)).toNat + 1) ((x + ↑(t + 1)).toNat + 2)]
      have cx : (((x + ↑(t + 1)).toNat + 1 : ℕ) : ℤ) - ↑t - 2 = x := by omega
      have cy : (((y + ↑(t + 1)).toNat + 1 : ℕ) : ℤ) - ↑t - 2 = y := by omega
      have ny : ((y + ↑(t + 1)).toNat : ℤ) - ↑t - 2 = y - 1 := by omega
      have sy : (((y + ↑(t + 1)).toNat + 2 : ℕ) : ℤ) - ↑t - 2 = y + 1 := by omega
      have wx : ((x + ↑(t + 1)).toNat : ℤ) - ↑t - 2 = x - 1 := by omega
      have ex : (((x + ↑(t + 1)).toNat + 2 : ℕ) : ℤ) - ↑t - 2 = x + 1 := by omega
      unfold evalBox
      rw [cx, cy, ny, sy, wx, ex]
      rfl
    · rw [evalBox_out _ _ _ _ _ h]
      unfold step nextCfg
      dsimp only
      rw [evalBox_out _ _ _ x y (by omega),
          evalBox_out _ _ _ (x - 1) y (by omega),
          evalBox_out _ _ _ (x + 1) y (by omega),
          evalBox_out _ _ _ x (y - 1) (by omega),
          evalBox_out _ _ _ x (y + 1) (by omega)]
      rfl

def sumUp (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => sumUp f k + f k

lemma sum_range_eq_sumUp (f : ℕ → ℕ) (k : ℕ) :
    (∑ i ∈ Finset.range k, f i) = sumUp f k := by
  induction k with
  | zero => simp [sumUp]
  | succ k ih => rw [Finset.sum_range_succ, ih, sumUp]

def xaxisFast (r n : ℕ) : ℕ :=
  let c := cfg r n
  sumUp (fun i => (evalBox c.2 n c.1 (i : ℤ) 0).toNat * 10 ^ (n - i)) (n + 1)

lemma xaxis_eq_fast (r n : ℕ) : xaxisRight10 r n = xaxisFast r n := by
  unfold xaxisRight10 xaxisFast
  rw [state_eq_cfg, sum_range_eq_sumUp]

end Disproof_oeis_a282679

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a282679.main) := by
  intro h
  have h39 := h 39 (by decide)
  unfold OMA.S_oeis_a282679.a OMA.S_oeis_a282679.A282675 at h39
  rw [xaxis_eq_fast 499 39, xaxis_eq_fast 497 39] at h39
  have hneq : xaxisFast 499 39 ≠ xaxisFast 497 39 := by decide +kernel
  exact hneq h39
