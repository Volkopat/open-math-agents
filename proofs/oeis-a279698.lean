import OMAStatements.S_oeis_a279698

namespace Adapt279698

open PowerSeries

def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 185 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))

def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n ((i : ℤ) - n) 0).toNat * 10 ^ (n - i)

section StripProof_a279698
open Adapt279698
open PowerSeries

-- 1. Basic symmetries and alternating light-cone bound
lemma state_neg_x (t : ℕ) : ∀ x y : ℤ, state t (-x) y = state t x y := by
  induction t with
  | zero => intro x y; simp only [state, neg_eq_zero]
  | succ t ih =>
    intro x y
    change step (state t) (-x) y = step (state t) x y
    unfold step
    have h1 : -x - 1 = -(x + 1) := by omega
    have h2 : -x + 1 = -(x - 1) := by omega
    rw [h1, h2, ih x y, ih (x + 1) y, ih (x - 1) y, ih x (y - 1), ih x (y + 1)]
    congr 1; omega

lemma abs_step_lb (z : ℤ) : |z| - 1 ≤ |z - 1| ∧ |z| - 1 ≤ |z + 1| := by
  cases abs_cases z <;> cases abs_cases (z - 1) <;> cases abs_cases (z + 1) <;> omega

lemma state_out_all (t : ℕ) :
    ∀ x y : ℤ, (t : ℤ) < |x| + |y| → state t x y = decide (t % 2 = 1) := by
  induction t with
  | zero =>
    intro x y h
    have hne : ¬(x = 0 ∧ y = 0) := by rintro ⟨rfl, rfl⟩; simp at h
    simp [state, hne]
  | succ t ih =>
    intro x y h
    change step (state t) x y = decide ((t + 1) % 2 = 1)
    unfold step
    have hx := abs_step_lb x
    have hy := abs_step_lb y
    rw [ih x y (by omega), ih (x - 1) y (by omega), ih (x + 1) y (by omega),
        ih x (y - 1) (by omega), ih x (y + 1) (by omega)]
    rcases Nat.mod_two_eq_zero_or_one t with ht | ht
    · have ht1 : (t + 1) % 2 = 1 := by omega
      simp only [ht, ht1]; decide
    · have ht1 : (t + 1) % 2 = 0 := by omega
      simp only [ht, ht1]; decide

-- 2. O(1)-per-cell sliding-window grid evaluator
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
    lookupL (xs ++ ys) i d = if i < xs.length then lookupL xs i d else lookupL ys (i - xs.length) d := by
  induction xs generalizing i with
  | nil => simp
  | cons _ xs ih =>
    cases i with
    | zero => rfl
    | succ i => simp only [List.cons_append, lookupL, List.length_cons, Nat.succ_lt_succ_iff, Nat.succ_sub_succ_eq_sub, ih]

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
        rcases (show j - xs.length = 0 ∨ j - xs.length = 1 ∨ 2 ≤ j - xs.length by omega) with h0 | h1 | h2
        · rw [h0]; rfl
        · rw [h1]; rfl
        · exact lookupL_out [v, v] (j - xs.length) v (by simp; omega)

def stepRow3 : List Bool → List Bool → List Bool → List Bool
  | _ :: d :: ds, l :: c :: r :: cs, _ :: u :: us =>
      Nat.testBit 185 (c.toNat + 2 * (l.toNat + r.toNat + d.toNat + u.toNat)) ::
        stepRow3 (d :: ds) (c :: r :: cs) (u :: us)
  | _, _, _ => []

lemma length_stepRow3 (r1 r2 r3 : List Bool) (n : ℕ)
    (h1 : r1.length = n + 2) (h2 : r2.length = n + 2) (h3 : r3.length = n + 2) :
    (stepRow3 r1 r2 r3).length = n := by
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

lemma lookupL_stepRow3 (r1 r2 r3 : List Bool) (n i : ℕ) (d : Bool)
    (h1 : r1.length = n + 2) (h2 : r2.length = n + 2) (h3 : r3.length = n + 2) (hi : i < n) :
    lookupL (stepRow3 r1 r2 r3) i d =
      Nat.testBit 185 ((lookupL r2 (i + 1) d).toNat + 2 *
        ((lookupL r2 i d).toNat + (lookupL r2 (i + 2) d).toNat +
         (lookupL r1 (i + 1) d).toNat + (lookupL r3 (i + 1) d).toNat)) := by
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

def stepGrid : List (List Bool) → List (List Bool)
  | r1 :: r2 :: r3 :: rs => stepRow3 r1 r2 r3 :: stepGrid (r2 :: r3 :: rs)
  | _ => []

lemma length_stepGrid (ps : List (List Bool)) (m w : ℕ)
    (hlen : ps.length = m + 2) (hrow : ∀ r ∈ ps, r.length = w + 2) :
    (stepGrid ps).length = m ∧ ∀ r ∈ stepGrid ps, r.length = w := by
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
        (fun r hr => hrow r (List.mem_cons_of_mem r1 hr))
      simp only [stepGrid, List.length_cons, hsub.1, true_and, List.mem_cons]
      rintro r (rfl | hr)
      · exact length_stepRow3 r1 r2 r3 w hr1 hr2 hr3
      · exact hsub.2 r hr
    | [] | [_] | [_, _] => simp at hlen

lemma lookupL_stepGrid (ps : List (List Bool)) (m w iy ix : ℕ) (bg : Bool)
    (hlen : ps.length = m + 2) (hrow : ∀ r ∈ ps, r.length = w + 2)
    (hiy : iy < m) (hix : ix < w) :
    lookupL (lookupL (stepGrid ps) iy []) ix bg =
      Nat.testBit 185 ((lookupL (lookupL ps (iy + 1) []) (ix + 1) bg).toNat + 2 *
        ((lookupL (lookupL ps (iy + 1) []) ix bg).toNat +
         (lookupL (lookupL ps (iy + 1) []) (ix + 2) bg).toNat +
         (lookupL (lookupL ps iy []) (ix + 1) bg).toNat +
         (lookupL (lookupL ps (iy + 2) []) (ix + 1) bg).toNat)) := by
  induction iy generalizing ps m with
  | zero =>
    rcases m with _ | m
    · omega
    match ps with
    | r1 :: r2 :: r3 :: rs =>
      simp only [stepGrid, lookupL]
      exact lookupL_stepRow3 r1 r2 r3 w ix bg
        (hrow r1 (by simp)) (hrow r2 (by simp)) (hrow r3 (by simp)) hix
    | [] | [_] | [_, _] => simp at hlen
  | succ iy ih =>
    rcases m with _ | m
    · omega
    match ps with
    | r1 :: r2 :: r3 :: rs =>
      simp only [stepGrid, lookupL]
      exact ih (r2 :: r3 :: rs) m (by simp at hlen ⊢; omega)
        (fun r hr => hrow r (List.mem_cons_of_mem r1 hr)) (by omega)
    | [] | [_] | [_, _] => simp at hlen

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
  let bg' := Nat.testBit 185 (bg.toNat + 2 * (bg.toNat + bg.toNat + bg.toNat + bg.toNat))
  let blank := List.replicate (2 * t + 5) bg
  let padded := pad1 blank (c.2.map (pad1 bg))
  (bg', stepGrid padded)

def cfg : ℕ → Bool × List (List Bool)
  | 0 => (false, [[true]])
  | t + 1 => nextCfg t (cfg t)

def CfgWf (t : ℕ) (c : Bool × List (List Bool)) : Prop :=
  c.2.length = 2 * t + 1 ∧ ∀ r ∈ c.2, r.length = 2 * t + 1

lemma padded_wf (t : ℕ) (c : Bool × List (List Bool)) (hwf : CfgWf t c) :
    let blank := List.replicate (2 * t + 5) c.1
    let padded := pad1 blank (c.2.map (pad1 c.1))
    padded.length = (2 * (t + 1) + 1) + 2 ∧
      ∀ r ∈ padded, r.length = (2 * (t + 1) + 1) + 2 := by
  dsimp only
  refine ⟨by rw [length_pad1, List.length_map, hwf.1]; omega, ?_⟩
  intro r hr
  simp only [pad1, List.mem_cons, List.mem_append, List.mem_map] at hr
  rcases hr with rfl | rfl | ⟨⟨row, hmem, rfl⟩ | hr2⟩
  · simp; omega
  · simp; omega
  · simp [hwf.2 row hmem]; omega
  · simp only [List.not_mem_nil, or_false] at hr2
    rcases hr2 with rfl | rfl <;> (simp; omega)

lemma cfg_wf (t : ℕ) : CfgWf t (cfg t) := by
  induction t with
  | zero => simp [CfgWf, cfg]
  | succ t ih =>
    unfold CfgWf cfg nextCfg
    dsimp only
    have hp := padded_wf t (cfg t) ih
    exact length_stepGrid _ (2 * (t + 1) + 1) (2 * (t + 1) + 1) hp.1 hp.2

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
    have hwf := cfg_wf t
    have hp := padded_wf t (cfg t) hwf
    have hsg := length_stepGrid _ (2 * (t + 1) + 1) (2 * (t + 1) + 1) hp.1 hp.2
    by_cases h : -↑(t + 1) ≤ x ∧ x ≤ ↑(t + 1) ∧ -↑(t + 1) ≤ y ∧ y ≤ ↑(t + 1)
    · unfold evalBox nextCfg
      rw [if_pos h]
      dsimp only
      set iy := (y + ↑(t + 1)).toNat
      set ix := (x + ↑(t + 1)).toNat
      have hrow_len : (lookupL (stepGrid (pad1 (List.replicate (2 * t + 5) (cfg t).1)
          ((cfg t).2.map (pad1 (cfg t).1)))) iy []).length = 2 * (t + 1) + 1 :=
        hsg.2 _ (lookupL_in_mem _ iy [] (by rw [hsg.1]; omega))
      rw [lookupL_congr_default _ ix _ (cfg t).1 (by rw [hrow_len]; omega)]
      rw [lookupL_stepGrid _ (2 * (t + 1) + 1) (2 * (t + 1) + 1) iy ix (cfg t).1
        hp.1 hp.2 (by omega) (by omega)]
      rw [lookupL_padded t (cfg t) hwf (iy + 1) (ix + 1),
          lookupL_padded t (cfg t) hwf (iy + 1) ix,
          lookupL_padded t (cfg t) hwf (iy + 1) (ix + 2),
          lookupL_padded t (cfg t) hwf iy (ix + 1),
          lookupL_padded t (cfg t) hwf (iy + 2) (ix + 1)]
      unfold step
      have cx : ((ix + 1 : ℕ) : ℤ) - ↑t - 2 = x := by omega
      have cy : ((iy + 1 : ℕ) : ℤ) - ↑t - 2 = y := by omega
      have lx : (ix : ℤ) - ↑t - 2 = x - 1 := by omega
      have rx : ((ix + 2 : ℕ) : ℤ) - ↑t - 2 = x + 1 := by omega
      have dy : (iy : ℤ) - ↑t - 2 = y - 1 := by omega
      have uy : ((iy + 2 : ℕ) : ℤ) - ↑t - 2 = y + 1 := by omega
      rw [cx, cy, lx, rx, dy, uy]
      rfl
    · rw [evalBox_out _ _ _ _ _ h]
      unfold step nextCfg
      dsimp only
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

def aFromCfg (t : ℕ) (c : Bool × List (List Bool)) : ℕ :=
  sumUp (fun i => (evalBox c.2 t c.1 ((i : ℤ) - t) 0).toNat * 10 ^ (t - i)) (t + 1)

lemma a_eq_aFromCfg (t : ℕ) : a t = aFromCfg t (cfg t) := by
  unfold a aFromCfg
  rw [state_eq_cfg, sum_range_eq_sumUp]

def checkInitAux : ℕ → Bool × List (List Bool) → List ℕ → Bool
  | _, _, [] => true
  | t, c, v :: vs => (aFromCfg t c == v) && checkInitAux (t + 1) (nextCfg t c) vs

lemma checkInitAux_ok (t : ℕ) (vals : List ℕ) (h : checkInitAux t (cfg t) vals = true) :
    ∀ i, i < vals.length → a (t + i) = lookupL vals i 0 := by
  induction vals generalizing t with
  | nil => intro i hi; simp at hi
  | cons v vs ih =>
    simp only [checkInitAux, Bool.and_eq_true, beq_iff_eq] at h
    intro i hi
    cases i with
    | zero =>
      simp only [Nat.add_zero, lookupL]
      rw [a_eq_aFromCfg]; exact h.1
    | succ j =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi
      simp only [lookupL]
      have hj := ih (t + 1) h.2 j hi
      have ht : t + (j + 1) = t + 1 + j := by omega
      rw [ht]; exact hj

def initList : List ℕ := [1, 0, 101, 0, 10111, 100, 1010101, 10100, 101000001, 1011100, 10101010101, 101001000, 1010001001011, 10101000010, 101010001011000, 1010101011011, 10100010101011110, 101010101011110, 1010100010101010110, 10101010101010110, 101000100010101010110, 1010101010101010110, 10101000100010101010110, 101010101010101010110, 1010001010100010101010110, 10101010101010101010110, 101010001010100010101010110, 1010101010101010101010110, 10100010001010100010101010110, 101010101010101010101010110, 1010100010001010100010101010110, 10101010101010101010101010110, 101000101010001010100010101010110, 1010101010101010101010101010110, 10101000101010001010100010101010110]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 200000 in
lemma init_ok : checkInitAux 0 (cfg 0) initList = true := by decide

lemma a_val_0 : a 0 = 1 := by
  have h := checkInitAux_ok 0 initList init_ok 0 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_1 : a 1 = 0 := by
  have h := checkInitAux_ok 0 initList init_ok 1 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_2 : a 2 = 101 := by
  have h := checkInitAux_ok 0 initList init_ok 2 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_3 : a 3 = 0 := by
  have h := checkInitAux_ok 0 initList init_ok 3 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_4 : a 4 = 10111 := by
  have h := checkInitAux_ok 0 initList init_ok 4 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_5 : a 5 = 100 := by
  have h := checkInitAux_ok 0 initList init_ok 5 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_6 : a 6 = 1010101 := by
  have h := checkInitAux_ok 0 initList init_ok 6 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_7 : a 7 = 10100 := by
  have h := checkInitAux_ok 0 initList init_ok 7 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_8 : a 8 = 101000001 := by
  have h := checkInitAux_ok 0 initList init_ok 8 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_9 : a 9 = 1011100 := by
  have h := checkInitAux_ok 0 initList init_ok 9 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_10 : a 10 = 10101010101 := by
  have h := checkInitAux_ok 0 initList init_ok 10 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_11 : a 11 = 101001000 := by
  have h := checkInitAux_ok 0 initList init_ok 11 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_12 : a 12 = 1010001001011 := by
  have h := checkInitAux_ok 0 initList init_ok 12 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_13 : a 13 = 10101000010 := by
  have h := checkInitAux_ok 0 initList init_ok 13 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_14 : a 14 = 101010001011000 := by
  have h := checkInitAux_ok 0 initList init_ok 14 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_15 : a 15 = 1010101011011 := by
  have h := checkInitAux_ok 0 initList init_ok 15 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_16 : a 16 = 10100010101011110 := by
  have h := checkInitAux_ok 0 initList init_ok 16 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_17 : a 17 = 101010101011110 := by
  have h := checkInitAux_ok 0 initList init_ok 17 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_18 : a 18 = 1010100010101010110 := by
  have h := checkInitAux_ok 0 initList init_ok 18 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_19 : a 19 = 10101010101010110 := by
  have h := checkInitAux_ok 0 initList init_ok 19 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_20 : a 20 = 101000100010101010110 := by
  have h := checkInitAux_ok 0 initList init_ok 20 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_21 : a 21 = 1010101010101010110 := by
  have h := checkInitAux_ok 0 initList init_ok 21 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_22 : a 22 = 10101000100010101010110 := by
  have h := checkInitAux_ok 0 initList init_ok 22 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_23 : a 23 = 101010101010101010110 := by
  have h := checkInitAux_ok 0 initList init_ok 23 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_24 : a 24 = 1010001010100010101010110 := by
  have h := checkInitAux_ok 0 initList init_ok 24 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_25 : a 25 = 10101010101010101010110 := by
  have h := checkInitAux_ok 0 initList init_ok 25 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_26 : a 26 = 101010001010100010101010110 := by
  have h := checkInitAux_ok 0 initList init_ok 26 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_27 : a 27 = 1010101010101010101010110 := by
  have h := checkInitAux_ok 0 initList init_ok 27 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_28 : a 28 = 10100010001010100010101010110 := by
  have h := checkInitAux_ok 0 initList init_ok 28 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_29 : a 29 = 101010101010101010101010110 := by
  have h := checkInitAux_ok 0 initList init_ok 29 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_30 : a 30 = 1010100010001010100010101010110 := by
  have h := checkInitAux_ok 0 initList init_ok 30 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_31 : a 31 = 10101010101010101010101010110 := by
  have h := checkInitAux_ok 0 initList init_ok 31 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_32 : a 32 = 101000101010001010100010101010110 := by
  have h := checkInitAux_ok 0 initList init_ok 32 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_33 : a 33 = 1010101010101010101010101010110 := by
  have h := checkInitAux_ok 0 initList init_ok 33 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_34 : a 34 = 10101000101010001010100010101010110 := by
  have h := checkInitAux_ok 0 initList init_ok 34 (by decide)
  simpa [initList, lookupL] using h

-- 3. Moving right-front triangle T_8 with alternating background bit
def evalTri (tr : Bool × List (List Bool)) (dx y : ℤ) : Bool :=
  if 0 ≤ dx ∧ dx ≤ 8 ∧ -dx ≤ y ∧ y ≤ dx then
    lookupL (lookupL tr.2 dx.toNat []) (y + dx).toNat tr.1
  else tr.1

def TriMatch (t : ℕ) (tr : Bool × List (List Bool)) : Prop :=
  tr.1 = decide (t % 2 = 1) ∧
    ∀ dx y : ℤ, 0 ≤ dx ∧ dx ≤ 8 ∧ -dx ≤ y ∧ y ≤ dx →
      state t ((t : ℤ) - dx) y = evalTri tr dx y

lemma triMatch_eval (t : ℕ) (ht : 8 ≤ t) (tr : Bool × List (List Bool)) (hm : TriMatch t tr)
    (dx' y' : ℤ) (hdx : dx' ≤ 8) :
    state t ((t : ℤ) - dx') y' = evalTri tr dx' y' := by
  by_cases hin : 0 ≤ dx' ∧ dx' ≤ 8 ∧ -dx' ≤ y' ∧ y' ≤ dx'
  · exact hm.2 dx' y' hin
  · unfold evalTri
    rw [if_neg hin, hm.1]
    apply state_out_all t
    cases abs_cases ((t : ℤ) - dx') <;> cases abs_cases y' <;> omega

def nextTri (tr : Bool × List (List Bool)) : Bool × List (List Bool) :=
  (!tr.1,
   buildL 9 fun idx =>
     let dx : ℤ := idx
     buildL (2 * idx + 1) fun iy =>
       let y : ℤ := (iy : ℤ) - dx
       let c := evalTri tr (dx - 1) y
       let l := evalTri tr dx y
       let r := evalTri tr (dx - 2) y
       let d := evalTri tr (dx - 1) (y - 1)
       let u := evalTri tr (dx - 1) (y + 1)
       Nat.testBit 185 (c.toNat + 2 * (l.toNat + r.toNat + d.toNat + u.toNat)))

lemma triMatch_step (t : ℕ) (ht : 8 ≤ t) (tr : Bool × List (List Bool)) (hm : TriMatch t tr) :
    TriMatch (t + 1) (nextTri tr) := by
  refine ⟨?_, ?_⟩
  · dsimp [nextTri]
    rw [hm.1]
    rcases Nat.mod_two_eq_zero_or_one t with hpar | hpar
    · have hp1 : (t + 1) % 2 = 1 := by omega
      simp [hpar, hp1]
    · have hp1 : (t + 1) % 2 = 0 := by omega
      simp [hpar, hp1]
  · intro dx y h
    change step (state t) (((t + 1 : ℕ) : ℤ) - dx) y = evalTri (nextTri tr) dx y
    unfold evalTri nextTri
    rw [if_pos h]
    dsimp only
    rw [lookupL_buildL, if_pos (by omega : dx.toNat < 9)]
    rw [lookupL_buildL, if_pos (by omega : (y + dx).toNat < 2 * dx.toNat + 1)]
    have hdx : ((dx.toNat : ℕ) : ℤ) = dx := by omega
    have hy : (((y + dx).toNat : ℕ) : ℤ) - dx = y := by omega
    simp only [hdx, hy]
    unfold step
    have el : ((t + 1 : ℕ) : ℤ) - dx - 1 = (t : ℤ) - dx := by omega
    have er : ((t + 1 : ℕ) : ℤ) - dx + 1 = (t : ℤ) - (dx - 2) := by omega
    have ec : ((t + 1 : ℕ) : ℤ) - dx = (t : ℤ) - (dx - 1) := by omega
    rw [el, er, ec,
        triMatch_eval t ht tr hm (dx - 1) y (by omega),
        triMatch_eval t ht tr hm dx y (by omega),
        triMatch_eval t ht tr hm (dx - 2) y (by omega),
        triMatch_eval t ht tr hm (dx - 1) (y - 1) (by omega),
        triMatch_eval t ht tr hm (dx - 1) (y + 1) (by omega)]

def tri0 : Bool × List (List Bool) := (true, [[false], [true, false, true], [true, true, false, true, true], [true, true, false, true, false, true, true], [true, true, false, true, false, true, false, true, true], [true, true, true, false, true, true, true, false, true, true, true], [true, true, false, true, true, true, false, true, true, true, false, true, true], [true, true, true, false, true, false, true, true, true, false, true, false, true, true, true], [false, true, false, true, true, false, true, true, false, true, true, false, true, true, false, true, false]])

def triSeq : ℕ → Bool × List (List Bool)
  | 0 => tri0
  | k + 1 => nextTri (triSeq k)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 200000 in
lemma triSeq_period_base : triSeq 16 = tri0 := by decide

lemma triSeq_add_period (k : ℕ) : triSeq (k + 16) = triSeq k := by
  induction k with
  | zero => simpa [triSeq] using triSeq_period_base
  | succ k ih =>
    have heq : k + 1 + 16 = (k + 16) + 1 := by omega
    rw [heq, triSeq, ih, ← triSeq]

lemma triSeq_mod (k : ℕ) : triSeq k = triSeq (k % 16) := by
  have hdiv : k = 16 * (k / 16) + k % 16 := (Nat.div_add_mod k 16).symm
  conv_lhs => rw [hdiv]
  generalize k / 16 = q
  induction q with
  | zero => simp
  | succ q ih =>
    have heq : 16 * (q + 1) + k % 16 = (16 * q + k % 16) + 16 := by ring
    rw [heq, triSeq_add_period, ih]

-- 4. Autonomous W=2 strip pat185 of period 2 in t and spatial period 8 for |x| >= 5
def pat185Even : List (List Bool) := [[false, true, true, false, true, false, true, false, true, false, true, false, false], [true, true, false, true, true, true, true, true, true, true, true, true, false], [true, false, true, true, false, true, false, true, false, true, false, true, true]]
def pat185Odd  : List (List Bool) := [[false, true, true, false, true, false, true, false, true, false, true, false, true], [true, true, false, true, true, true, true, true, true, true, true, true, false], [true, false, true, true, false, true, false, true, false, true, false, true, true]]

def xIdx (x : ℤ) : ℕ :=
  let ax := x.natAbs
  if ax < 5 then ax else 5 + (ax - 5) % 8

def pat185 (par : ℕ) (x y : ℤ) : Bool :=
  let tbl := if par % 2 = 0 then pat185Even else pat185Odd
  lookupL (lookupL tbl y.natAbs []) (xIdx x) false

lemma pat185_neg_x (par : ℕ) (x y : ℤ) : pat185 par (-x) y = pat185 par x y := by
  unfold pat185 xIdx; rw [Int.natAbs_neg]

lemma xIdx_shift_ge13 (x : ℤ) (hx : 13 ≤ x) (d : ℤ) (hd : -1 ≤ d ∧ d ≤ 1) :
    xIdx (x + d) = xIdx ((13 + ((x - 13) % 8).toNat : ℕ) + d) := by
  unfold xIdx
  have h1 : ¬((x + d).natAbs < 5) := by omega
  have h2 : ¬((((13 + ((x - 13) % 8).toNat : ℕ) : ℤ) + d).natAbs < 5) := by omega
  dsimp only
  rw [if_neg h1, if_neg h2]
  omega

def checkT0 : Bool :=
  let c := cfg 23
  (List.range 9).all (fun idx =>
    (List.range (2 * idx + 1)).all (fun iy =>
      evalBox c.2 23 c.1 (23 - idx) ((iy : ℤ) - idx) ==
        evalTri tri0 idx ((iy : ℤ) - idx))) &&
  (List.range 5).all (fun iy =>
    (List.range 33).all (fun ix =>
      evalBox c.2 23 c.1 ((ix : ℤ) - 16) ((iy : ℤ) - 2) ==
        pat185 1 ((ix : ℤ) - 16) ((iy : ℤ) - 2)))

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 200000 in
lemma checkT0_true : checkT0 = true := by decide

lemma triMatch_t0 : TriMatch 23 tri0 := by
  refine ⟨rfl, ?_⟩
  have hc := checkT0_true
  unfold checkT0 at hc
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
  intro dx y h
  rw [state_eq_cfg 23]
  have h1 := hc.1 dx.toNat (by omega) (y + dx).toNat (by omega)
  have edx : ((dx.toNat : ℕ) : ℤ) = dx := by omega
  have ey : (((y + dx).toNat : ℕ) : ℤ) - dx = y := by omega
  rw [edx, ey] at h1
  exact h1

lemma triMatch_seq (k : ℕ) : TriMatch (23 + k) (triSeq k) := by
  induction k with
  | zero => simpa [triSeq] using triMatch_t0
  | succ k ih =>
    have heq : 23 + (k + 1) = (23 + k) + 1 := by omega
    rw [heq]
    exact triMatch_step (23 + k) (by omega) (triSeq k) ih

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 200000 in
lemma pat185_step_fin : ∀ (par : Fin 2) (ix : Fin 21) (y : ℤ),
    y ∈ ([-2, -1, 0, 1, 2] : List ℤ) →
    ∀ b : Bool,
      let x : ℤ := ix.val
      let c := pat185 par.val x y
      let l := pat185 par.val (x - 1) y
      let r := pat185 par.val (x + 1) y
      let d := if y = -2 then b else pat185 par.val x (y - 1)
      let u := if y = 2 then b else pat185 par.val x (y + 1)
      Nat.testBit 185 (c.toNat + 2 * (l.toNat + r.toNat + d.toNat + u.toNat)) =
        pat185 (par.val + 1) x y := by
  decide

lemma strip185_stay_nonneg (t : ℕ) (x y : ℤ) (hx : 0 ≤ x) (hy : |y| ≤ 2)
    (hnb : ∀ u v : ℤ, u ∈ [x - 1, x, x + 1] → |v| ≤ 2 → state t u v = pat185 (t % 2) u v) :
    state (t + 1) x y = pat185 ((t + 1) % 2) x y := by
  change step (state t) x y = pat185 ((t + 1) % 2) x y
  unfold step
  set par : Fin 2 := ⟨t % 2, by omega⟩
  have hpar1 : pat185 ((t + 1) % 2) = pat185 (par.val + 1) := by
    funext u v; unfold pat185
    have hmod : ((t + 1) % 2) % 2 = (par.val + 1) % 2 := by dsimp [par]; omega
    rw [hmod]
  rw [hpar1]
  let ixNat : ℕ := if x < 13 then x.toNat else 13 + ((x - 13) % 8).toNat
  have hix_lt : ixNat < 21 := by dsimp [ixNat]; split_ifs <;> omega
  set ix : Fin 21 := ⟨ixNat, hix_lt⟩
  have hx_idx : ∀ p : ℕ, ∀ d : ℤ, -1 ≤ d ∧ d ≤ 1 → ∀ v : ℤ,
      pat185 p (x + d) v = pat185 p ((ix.val : ℤ) + d) v := by
    intro p d hd v
    have hval : (ix.val : ℤ) = (ixNat : ℤ) := rfl
    rw [hval]
    dsimp only [ixNat]
    by_cases hlt : x < 13
    · rw [if_pos hlt]
      have hx_cast : ((x.toNat : ℕ) : ℤ) = x := by omega
      rw [hx_cast]
    · rw [if_neg hlt]
      unfold pat185
      rw [xIdx_shift_ge13 x (by omega) d hd]
  have hc : state t x y = pat185 par.val (ix.val : ℤ) y := by
    rw [hnb x y (by simp) hy]
    simpa using hx_idx (t % 2) 0 (by omega) y
  have hl : state t (x - 1) y = pat185 par.val ((ix.val : ℤ) - 1) y := by
    rw [hnb (x - 1) y (by simp) hy]
    simpa [sub_eq_add_neg] using hx_idx (t % 2) (-1) (by omega) y
  have hr : state t (x + 1) y = pat185 par.val ((ix.val : ℤ) + 1) y := by
    rw [hnb (x + 1) y (by simp) hy]
    exact hx_idx (t % 2) 1 (by omega) y
  have hrhs : pat185 (par.val + 1) x y = pat185 (par.val + 1) (ix.val : ℤ) y := by
    simpa using hx_idx (par.val + 1) 0 (by omega) y
  rw [hrhs]
  have hy_cases : y = -2 ∨ y = -1 ∨ y = 0 ∨ y = 1 ∨ y = 2 := by cases abs_cases y <;> omega
  rcases hy_cases with rfl | rfl | rfl | rfl | rfl
  · have hu : state t x (-2 + 1) = pat185 par.val (ix.val : ℤ) (-2 + 1) := by
      rw [hnb x (-2 + 1) (by simp) (by norm_num)]; simpa using hx_idx (t % 2) 0 (by omega) (-1)
    have hfin := pat185_step_fin par ix (-2) (by simp) (state t x (-2 - 1))
    dsimp only at hfin; rw [hc, hl, hr, hu]; simpa using hfin
  · have hd : state t x (-1 - 1) = pat185 par.val (ix.val : ℤ) (-1 - 1) := by
      rw [hnb x (-1 - 1) (by simp) (by norm_num)]; simpa using hx_idx (t % 2) 0 (by omega) (-2)
    have hu : state t x (-1 + 1) = pat185 par.val (ix.val : ℤ) (-1 + 1) := by
      rw [hnb x (-1 + 1) (by simp) (by norm_num)]; simpa using hx_idx (t % 2) 0 (by omega) 0
    have hfin := pat185_step_fin par ix (-1) (by simp) false
    dsimp only at hfin; rw [hc, hl, hr, hd, hu]; simpa using hfin
  · have hd : state t x (0 - 1) = pat185 par.val (ix.val : ℤ) (0 - 1) := by
      rw [hnb x (0 - 1) (by simp) (by norm_num)]; simpa using hx_idx (t % 2) 0 (by omega) (-1)
    have hu : state t x (0 + 1) = pat185 par.val (ix.val : ℤ) (0 + 1) := by
      rw [hnb x (0 + 1) (by simp) (by norm_num)]; simpa using hx_idx (t % 2) 0 (by omega) 1
    have hfin := pat185_step_fin par ix 0 (by simp) false
    dsimp only at hfin; rw [hc, hl, hr, hd, hu]; simpa using hfin
  · have hd : state t x (1 - 1) = pat185 par.val (ix.val : ℤ) (1 - 1) := by
      rw [hnb x (1 - 1) (by simp) (by norm_num)]; simpa using hx_idx (t % 2) 0 (by omega) 0
    have hu : state t x (1 + 1) = pat185 par.val (ix.val : ℤ) (1 + 1) := by
      rw [hnb x (1 + 1) (by simp) (by norm_num)]; simpa using hx_idx (t % 2) 0 (by omega) 2
    have hfin := pat185_step_fin par ix 1 (by simp) false
    dsimp only at hfin; rw [hc, hl, hr, hd, hu]; simpa using hfin
  · have hd : state t x (2 - 1) = pat185 par.val (ix.val : ℤ) (2 - 1) := by
      rw [hnb x (2 - 1) (by simp) (by norm_num)]; simpa using hx_idx (t % 2) 0 (by omega) 1
    have hfin := pat185_step_fin par ix 2 (by simp) (state t x (2 + 1))
    dsimp only at hfin; rw [hc, hl, hr, hd]; simpa using hfin

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 200000 in
lemma tri_feed_185 : ∀ r ∈ List.range 16, ∀ dy ∈ ([-2, -1, 0, 1, 2] : List ℤ),
    evalTri (triSeq r) 7 dy = pat185 ((23 + r) % 2) (((23 + r : ℕ) : ℤ) - 7) dy ∧
    evalTri (triSeq r) 8 dy = pat185 ((23 + r) % 2) (((23 + r : ℕ) : ℤ) - 8) dy := by decide

lemma pat185_ge5_mod8 (par : ℕ) (x1 x2 y : ℤ) (h1 : 5 ≤ x1) (h2 : 5 ≤ x2)
    (hm : (x1 - 5) % 8 = (x2 - 5) % 8) :
    pat185 par x1 y = pat185 par x2 y := by
  unfold pat185 xIdx
  have a1 : ¬(x1.natAbs < 5) := by omega
  have a2 : ¬(x2.natAbs < 5) := by omega
  dsimp only
  rw [if_neg a1, if_neg a2]
  have eqm : (x1.natAbs - 5) % 8 = (x2.natAbs - 5) % 8 := by omega
  rw [eqm]

lemma strip_185_hold (t : ℕ) (ht : 23 ≤ t) :
    ∀ x y : ℤ, |x| ≤ (t : ℤ) - 7 → |y| ≤ 2 → state t x y = pat185 (t % 2) x y := by
  obtain ⟨k, rfl⟩ : ∃ k, t = 23 + k := ⟨t - 23, by omega⟩
  induction k with
  | zero =>
    have hc := checkT0_true
    unfold checkT0 at hc
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
    intro x y hx hy
    rw [Nat.add_zero, state_eq_cfg 23]
    have hiy : (y + 2).toNat < 5 := by cases abs_cases y <;> omega
    have hix : (x + 16).toNat < 33 := by cases abs_cases x <;> omega
    have h2 := hc.2 (y + 2).toNat hiy (x + 16).toNat hix
    have ex : (((x + 16).toNat : ℕ) : ℤ) - 16 = x := by cases abs_cases x <;> omega
    have ey : (((y + 2).toNat : ℕ) : ℤ) - 2 = y := by cases abs_cases y <;> omega
    rw [ex, ey] at h2
    exact h2
  | succ k ih =>
    intro x y hx hy
    have ihk := ih (by omega)
    have hwlog : ∀ u : ℤ, 0 ≤ u → u ≤ ((23 + (k + 1) : ℕ) : ℤ) - 7 →
        state (23 + (k + 1)) u y = pat185 ((23 + (k + 1)) % 2) u y := by
      intro u hu0 hu_ub
      by_cases hin : u ≤ ((23 + k : ℕ) : ℤ) - 7 - 1
      · have heq : 23 + (k + 1) = (23 + k) + 1 := by omega
        rw [heq]
        apply strip185_stay_nonneg (23 + k) u y hu0 hy
        intro w v hw hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | hw0 | rfl
        · exact ihk (u - 1) v (by cases abs_cases (u - 1) <;> omega) hv
        · rw [hw0]; exact ihk u v (by cases abs_cases u <;> omega) hv
        · exact ihk (u + 1) v (by cases abs_cases (u + 1) <;> omega) hv
      · have hy_mem : y ∈ ([-2, -1, 0, 1, 2] : List ℤ) := by
          have : y = -2 ∨ y = -1 ∨ y = 0 ∨ y = 1 ∨ y = 2 := by cases abs_cases y <;> omega
          rcases this with rfl | rfl | rfl | rfl | rfl <;> simp
        have hcases : u = ((23 + (k + 1) : ℕ) : ℤ) - 8 ∨ u = ((23 + (k + 1) : ℕ) : ℤ) - 7 := by omega
        have hm := (triMatch_seq (k + 1)).2
        rw [triSeq_mod] at hm
        have hf := tri_feed_185 ((k + 1) % 16)
          (by rw [List.mem_range]; exact Nat.mod_lt _ (by decide)) y hy_mem
        have hpar_eq : (23 + (k + 1) % 16) % 2 = (23 + (k + 1)) % 2 := by omega
        rcases hcases with rfl | rfl
        · rw [hm 8 y (by cases abs_cases y <;> omega), hf.2, hpar_eq]
          exact pat185_ge5_mod8 ((23 + (k + 1)) % 2) _ _ y (by omega) (by omega) (by omega)
        · rw [hm 7 y (by cases abs_cases y <;> omega), hf.1, hpar_eq]
          exact pat185_ge5_mod8 ((23 + (k + 1)) % 2) _ _ y (by omega) (by omega) (by omega)
    by_cases hnn : 0 ≤ x
    · exact hwlog x hnn (by rw [abs_of_nonneg hnn] at hx; exact hx)
    · rw [← state_neg_x (23 + (k + 1)) x y, ← pat185_neg_x _ x y]
      exact hwlog (-x) (by omega) (by cases abs_cases x <;> omega)

-- 5. 2-step telescopic difference, recurrence, and generating function
lemma a_eq_sum_j (n : ℕ) :
    (a n : ℤ) = ∑ j ∈ Finset.range (n + 1), ((state n (j : ℤ) 0).toNat : ℤ) * 10 ^ j := by
  unfold a
  have href := Finset.sum_range_reflect
    (fun j => (state n ((n - j : ℕ) - (n : ℤ)) 0).toNat * 10 ^ j) (n + 1)
  have h1 : (∑ i ∈ Finset.range (n + 1), (state n ((i : ℤ) - n) 0).toNat * 10 ^ (n - i)) =
      ∑ j ∈ Finset.range (n + 1), (state n (j : ℤ) 0).toNat * 10 ^ j := by
    calc _
      _ = ∑ i ∈ Finset.range (n + 1),
            (state n (((n - (n - i) : ℕ) : ℤ) - n) 0).toNat * 10 ^ (n - i) := by
          apply Finset.sum_congr rfl
          intro i hi; rw [Finset.mem_range] at hi
          have : n - (n - i) = i := by omega
          rw [this]
      _ = ∑ j ∈ Finset.range (n + 1),
            (state n (((n - j : ℕ) : ℤ) - n) 0).toNat * 10 ^ j := by
          simpa [Nat.succ_sub_succ_eq_sub] using href
      _ = ∑ j ∈ Finset.range (n + 1), (state n (j : ℤ) 0).toNat * 10 ^ j := by
          apply Finset.sum_congr rfl
          intro j hj; rw [Finset.mem_range] at hj
          have hneg : (((n - j : ℕ) : ℤ) - n) = -(j : ℤ) := by omega
          rw [hneg, state_neg_x]
  rw [h1, Nat.cast_sum]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

def frontVal (r : ℕ) : ℤ :=
  ∑ k ∈ Finset.range 7,
    ((evalTri (triSeq r) ((7 - 1 - k : ℕ) : ℤ) 0).toNat : ℤ) * 10 ^ k

lemma a_decomp (n : ℕ) (hn : 23 ≤ n) :
    (a n : ℤ) = (∑ j ∈ Finset.range (n + 1 - 7), ((pat185 (n % 2) (j : ℤ) 0).toNat : ℤ) * (10 : ℤ) ^ j) +
      (10 : ℤ) ^ (n + 1 - 7) * frontVal ((n - 23) % 16) := by
  rw [a_eq_sum_j n]
  unfold frontVal
  have hsplit : n + 1 = (n + 1 - 7) + 7 := by omega
  conv_lhs => rw [hsplit, Finset.sum_range_add]
  rw [Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have hs := strip_185_hold n hn (j : ℤ) 0
      (by rw [abs_of_nonneg (Nat.cast_nonneg j)]; omega) (by norm_num)
    rw [hs]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    have hx : ((n + 1 - 7 + k : ℕ) : ℤ) = (n : ℤ) - ((7 - 1 - k : ℕ) : ℤ) := by omega
    have hm := (triMatch_seq (n - 23)).2
    have htn : 23 + (n - 23) = n := by omega
    rw [htn, triSeq_mod] at hm
    have htri := hm ((7 - 1 - k : ℕ) : ℤ) 0 (by omega)
    rw [hx, htri, pow_add]
    ring

def w2Diff (n : ℕ) : ℤ := (a n : ℤ) - a (n - 2)

lemma w2Diff_formula (n : ℕ) (hn : 25 ≤ n) :
    w2Diff n = (10 : ℤ) ^ (n - 8) *
      (((pat185 (n % 2) ((n - 8 : ℕ) : ℤ) 0).toNat : ℤ) +
       10 * ((pat185 (n % 2) ((n - 7 : ℕ) : ℤ) 0).toNat : ℤ) +
       100 * frontVal ((n - 23) % 16) - frontVal ((n - 2 - 23) % 16)) := by
  unfold w2Diff
  rw [a_decomp n (by omega), a_decomp (n - 2) (by omega)]
  have hpar : (n - 2) % 2 = n % 2 := by omega
  have hlen1 : n + 1 - 7 = (n - 8) + 2 := by omega
  have hlen2 : n - 2 + 1 - 7 = n - 8 := by omega
  rw [hpar, hlen1, hlen2, Finset.sum_range_add, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
  have c0 : n - 8 + 0 = n - 8 := by omega
  have c1 : n - 8 + 1 = n - 7 := by omega
  have p1 : (10 : ℤ) ^ (n - 7) = 10 * (10 : ℤ) ^ (n - 8) := by
    have : n - 7 = (n - 8) + 1 := by omega
    rw [this, pow_succ]; ring
  have p2 : (10 : ℤ) ^ (n - 8 + 2) = 100 * (10 : ℤ) ^ (n - 8) := by
    rw [pow_add]; ring
  rw [c0, c1, p1, p2]
  generalize frontVal = fv
  ring

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 200000 in
lemma front2_periodic : ∀ r0 ∈ List.range 16,
    (100 : ℤ) * frontVal ((r0 + 10) % 16) - frontVal ((r0 + 8) % 16) =
    (100 : ℤ) * frontVal ((r0 + 2) % 16) - frontVal r0 := by decide

lemma w2Diff_periodic (n : ℕ) (hn : 35 ≤ n) :
    w2Diff n = 100000000 * w2Diff (n - 8) := by
  rw [w2Diff_formula n (by omega), w2Diff_formula (n - 8) (by omega)]
  have hpar : (n - 8) % 2 = n % 2 := by omega
  have hp8 : pat185 (n % 2) ((n - 8 : ℕ) : ℤ) 0 = pat185 (n % 2) ((n - 8 - 8 : ℕ) : ℤ) 0 :=
    pat185_ge5_mod8 (n % 2) _ _ 0 (by omega) (by omega) (by omega)
  have hp7 : pat185 (n % 2) ((n - 7 : ℕ) : ℤ) 0 = pat185 (n % 2) ((n - 8 - 7 : ℕ) : ℤ) 0 :=
    pat185_ge5_mod8 (n % 2) _ _ 0 (by omega) (by omega) (by omega)
  have e1 : (n - 23) % 16 = ((n - 8 - 2 - 23) % 16 + 10) % 16 := by omega
  have e2 : (n - 2 - 23) % 16 = ((n - 8 - 2 - 23) % 16 + 8) % 16 := by omega
  have e3 : (n - 8 - 23) % 16 = ((n - 8 - 2 - 23) % 16 + 2) % 16 := by omega
  have hr_lt : (n - 8 - 2 - 23) % 16 < 16 := Nat.mod_lt _ (by decide)
  generalize (n - 8 - 2 - 23) % 16 = r at e1 e2 e3 hr_lt ⊢
  rw [hpar, hp8, hp7, e1, e2, e3]
  have hfp := front2_periodic r (by rw [List.mem_range]; exact hr_lt)
  have hpow : (10 : ℤ) ^ (n - 8) = 100000000 * (10 : ℤ) ^ (n - 8 - 8) := by
    have : (100000000 : ℤ) = (10 : ℤ) ^ 8 := by norm_num
    rw [this, ← pow_add]; congr 1; omega
  rw [hpow]
  generalize frontVal = fv at hfp ⊢
  generalize (10 : ℤ) ^ (n - 8 - 8) = pw
  generalize ((pat185 (n % 2) ((n - 8 - 8 : ℕ) : ℤ) 0).toNat : ℤ) = p8
  generalize ((pat185 (n % 2) ((n - 8 - 7 : ℕ) : ℤ) 0).toNat : ℤ) = p7
  linear_combination 100000000 * pw * hfp

lemma rec_claim (n : ℕ) (hn : 28 ≤ n) :
    (a n : ℤ) = a (n - 2) + 100000000 * a (n - 8) - 100000000 * a (n - 10) := by
  by_cases hhigh : 35 ≤ n
  · have hw := w2Diff_periodic n hhigh
    unfold w2Diff at hw
    have hsub : n - 8 - 2 = n - 10 := by omega
    rw [hsub] at hw
    linarith
  · interval_cases n <;> norm_num [a_val_0, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8, a_val_9, a_val_10, a_val_11, a_val_12, a_val_13, a_val_14, a_val_15, a_val_16, a_val_17, a_val_18, a_val_19, a_val_20, a_val_21, a_val_22, a_val_23, a_val_24, a_val_25, a_val_26, a_val_27, a_val_28, a_val_29, a_val_30, a_val_31, a_val_32, a_val_33, a_val_34]

set_option maxHeartbeats 2000000 in
lemma gf_claim :
    PowerSeries.mk (fun n => (a n : ℤ)) * (100000000 * X ^ 10 - 100000000 * X ^ 8 - X ^ 2 + 1) =
      100000000000 * X ^ 27 + 100000000000 * X ^ 26 - 9900000000 * X ^ 25 - 11000000000 * X ^ 24 - 1100100000000 * X ^ 23 - 998900000000 * X ^ 22 + 99000000000 * X ^ 21 + 909000000000 * X ^ 20 + 1009999999000 * X ^ 19 - 1010000001000 * X ^ 18 - 99999999901 * X ^ 17 + 10100000110 * X ^ 16 + 11001 * X ^ 15 + 1000009989 * X ^ 14 - 990 * X ^ 13 - 1100009090 * X ^ 12 + 99989900 * X ^ 11 + 10100 * X ^ 10 + 1001000 * X ^ 9 - 10100 * X ^ 8 + 10000 * X ^ 7 + 999990 * X ^ 6 + 100 * X ^ 5 + 10010 * X ^ 4 + 100 * X ^ 2 + 1 := by
  let s := PowerSeries.mk (fun n => (a n : ℤ))
  have hring : s * (100000000 * X ^ 10 - 100000000 * X ^ 8 - X ^ 2 + 1) =
      C (1 : ℤ) * (s * X ^ 0) + C (-1 : ℤ) * (s * X ^ 2) + C (-100000000 : ℤ) * (s * X ^ 8) + C (100000000 : ℤ) * (s * X ^ 10) := by
    simp only [map_neg, map_one, map_ofNat]; ring
  rw [hring]
  have hrhs : (100000000000 * X ^ 27 + 100000000000 * X ^ 26 - 9900000000 * X ^ 25 - 11000000000 * X ^ 24 - 1100100000000 * X ^ 23 - 998900000000 * X ^ 22 + 99000000000 * X ^ 21 + 909000000000 * X ^ 20 + 1009999999000 * X ^ 19 - 1010000001000 * X ^ 18 - 99999999901 * X ^ 17 + 10100000110 * X ^ 16 + 11001 * X ^ 15 + 1000009989 * X ^ 14 - 990 * X ^ 13 - 1100009090 * X ^ 12 + 99989900 * X ^ 11 + 10100 * X ^ 10 + 1001000 * X ^ 9 - 10100 * X ^ 8 + 10000 * X ^ 7 + 999990 * X ^ 6 + 100 * X ^ 5 + 10010 * X ^ 4 + 100 * X ^ 2 + 1 : PowerSeries ℤ) =
      C (1 : ℤ) * X ^ 0 + C (100 : ℤ) * X ^ 2 + C (10010 : ℤ) * X ^ 4 + C (100 : ℤ) * X ^ 5 + C (999990 : ℤ) * X ^ 6 + C (10000 : ℤ) * X ^ 7 + C (-10100 : ℤ) * X ^ 8 + C (1001000 : ℤ) * X ^ 9 + C (10100 : ℤ) * X ^ 10 + C (99989900 : ℤ) * X ^ 11 + C (-1100009090 : ℤ) * X ^ 12 + C (-990 : ℤ) * X ^ 13 + C (1000009989 : ℤ) * X ^ 14 + C (11001 : ℤ) * X ^ 15 + C (10100000110 : ℤ) * X ^ 16 + C (-99999999901 : ℤ) * X ^ 17 + C (-1010000001000 : ℤ) * X ^ 18 + C (1009999999000 : ℤ) * X ^ 19 + C (909000000000 : ℤ) * X ^ 20 + C (99000000000 : ℤ) * X ^ 21 + C (-998900000000 : ℤ) * X ^ 22 + C (-1100100000000 : ℤ) * X ^ 23 + C (-11000000000 : ℤ) * X ^ 24 + C (-9900000000 : ℤ) * X ^ 25 + C (100000000000 : ℤ) * X ^ 26 + C (100000000000 : ℤ) * X ^ 27 := by
    simp only [map_neg, map_one, map_ofNat]; ring
  rw [hrhs]
  ext n
  simp only [map_add, coeff_C_mul]
  simp only [coeff_mul_X_pow', coeff_X_pow, s, coeff_mk]
  by_cases hn : n ≤ 34
  · interval_cases n <;> norm_num [a_val_0, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8, a_val_9, a_val_10, a_val_11, a_val_12, a_val_13, a_val_14, a_val_15, a_val_16, a_val_17, a_val_18, a_val_19, a_val_20, a_val_21, a_val_22, a_val_23, a_val_24, a_val_25, a_val_26, a_val_27, a_val_28, a_val_29, a_val_30, a_val_31, a_val_32, a_val_33, a_val_34]
  · have hrec := rec_claim n (by omega)
    simp [show n ≠ 0 by omega, show n ≠ 2 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega, show n ≠ 8 by omega, show n ≠ 9 by omega, show n ≠ 10 by omega, show n ≠ 11 by omega, show n ≠ 12 by omega, show n ≠ 13 by omega, show n ≠ 14 by omega, show n ≠ 15 by omega, show n ≠ 16 by omega, show n ≠ 17 by omega, show n ≠ 18 by omega, show n ≠ 19 by omega, show n ≠ 20 by omega, show n ≠ 21 by omega, show n ≠ 22 by omega, show n ≠ 23 by omega, show n ≠ 24 by omega, show n ≠ 25 by omega, show n ≠ 26 by omega, show n ≠ 27 by omega, show 2 ≤ n by omega, show 8 ≤ n by omega, show 10 ≤ n by omega]
    linarith

end StripProof_a279698

lemma cell_bridge (n : ℕ) (x y : ℤ) : OMA.S_oeis_a279698.cell 185 n x y = state n x y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
    simp only [OMA.S_oeis_a279698.cell, state, step, ih]
    congr 1; omega

lemma value_bridge (n : ℕ) : OMA.S_oeis_a279698.a n = (a n : ℤ) := by
  unfold OMA.S_oeis_a279698.a a
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  rw [cell_bridge]
  split <;> rename_i h
  · simp [h]
  · simp [Bool.eq_false_iff.mpr h]

lemma map_series (f : ℕ → ℤ) :
    PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.mk f) =
      PowerSeries.mk (fun n => (f n : ℚ)) := by
  ext n; simp

end Adapt279698

open Adapt279698 in
theorem OMA.solution : type_of% @OMA.S_oeis_a279698.main := by
  simp only [value_bridge]
  refine ⟨?_, ?_⟩
  · intro n hn
    exact_mod_cast rec_claim n hn
  · have h := congrArg (PowerSeries.map (Int.castRingHom ℚ)) gf_claim
    simpa only [map_mul, map_one, map_add, map_sub, map_pow, map_neg, map_ofNat,
      PowerSeries.map_X, map_series, Int.cast_natCast] using h
