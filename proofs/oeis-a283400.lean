import OMAStatements.S_oeis_a283400

-- Sections 1-4 (the symmetries, the light cone, the verified grid evaluator, the periodic moving
-- front triangle and the stable axis strip of Rule 633) are taken from @longling12's proof of
-- A283407 (pull request #24203), with Rule 633 in place of Rule 637. Section 5 and the bridge are new.

namespace Adapt283400

open PowerSeries


def step (s : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 633 ((s x y).toNat + 2 * ((s (x - 1) y).toNat + (s (x + 1) y).toNat +
    (s x (y - 1)).toNat + (s x (y + 1)).toNat))


def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)


def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n ((i : ℤ) - n) 0).toNat * 10 ^ (n - i)


section StripProof_S_oeis_a283400
open Adapt283400
open PowerSeries

-- 1. Basic symmetries and light-cone bound
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

lemma state_neg_y (t : ℕ) : ∀ x y : ℤ, state t x (-y) = state t x y := by
  induction t with
  | zero => intro x y; simp only [state, neg_eq_zero]
  | succ t ih =>
    intro x y
    change step (state t) x (-y) = step (state t) x y
    unfold step
    have h1 : -y - 1 = -(y + 1) := by omega
    have h2 : -y + 1 = -(y - 1) := by omega
    rw [h1, h2, ih x y, ih (x - 1) y, ih (x + 1) y, ih x (y + 1), ih x (y - 1)]
    congr 1; omega

lemma abs_step_lb (z : ℤ) : |z| - 1 ≤ |z - 1| ∧ |z| - 1 ≤ |z + 1| := by
  cases abs_cases z <;> cases abs_cases (z - 1) <;> cases abs_cases (z + 1) <;> omega

lemma state_out_zero (x y : ℤ) (h : (0 : ℤ) < |x| + |y|) : state 0 x y = false := by
  have hne : ¬(x = 0 ∧ y = 0) := by rintro ⟨rfl, rfl⟩; simp at h
  simp [state, hne]

lemma state_out_cone (t : ℕ) (ht : 1 ≤ t) :
    ∀ x y : ℤ, (t : ℤ) < |x| + |y| → state t x y = true := by
  induction t with
  | zero => omega
  | succ t ih =>
    intro x y h
    change step (state t) x y = true
    unfold step
    have hx := abs_step_lb x
    have hy := abs_step_lb y
    cases t with
    | zero =>
      rw [state_out_zero x y (by omega), state_out_zero (x - 1) y (by omega),
          state_out_zero (x + 1) y (by omega), state_out_zero x (y - 1) (by omega),
          state_out_zero x (y + 1) (by omega)]
      decide
    | succ k =>
      have hk : 1 ≤ k + 1 := by omega
      rw [ih hk x y (by omega), ih hk (x - 1) y (by omega), ih hk (x + 1) y (by omega),
          ih hk x (y - 1) (by omega), ih hk x (y + 1) (by omega)]
      decide

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
  | nil => simp [lookupL]
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
      Nat.testBit 633 (c.toNat + 2 * (l.toNat + r.toNat + d.toNat + u.toNat)) ::
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
      Nat.testBit 633 ((lookupL r2 (i + 1) d).toNat + 2 *
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
      Nat.testBit 633 ((lookupL (lookupL ps (iy + 1) []) (ix + 1) bg).toNat + 2 *
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
  let bg' := Nat.testBit 633 (bg.toNat + 2 * (bg.toNat + bg.toNat + bg.toNat + bg.toNat))
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

def initList : List ℕ := [1, 0, 11, 1, 1110, 110, 111110, 11100, 11111011, 1110001, 1111111110, 111111110, 111111111110, 11111111110, 11111111111110, 1111111111110, 1111111111111110, 111111111111110, 111111111111111110, 11111111111111110, 11111111111111111110, 1111111111111111110, 1111111111111111111110, 111111111111111111100, 111111111111111111111111, 11111111111111111111111, 11111111111111111111111111, 1111111111111111111111111, 1111111111111111111111111111, 111111111111111111111111111, 111111111111111111111111111111, 11111111111111111111111111111, 11111111111111111111111111111111, 1111111111111111111111111111111]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 200000 in
lemma init_ok : checkInitAux 0 (cfg 0) initList = true := by decide

lemma a_val_0 : a 0 = 1 := by
  have h := checkInitAux_ok 0 initList init_ok 0 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_1 : a 1 = 0 := by
  have h := checkInitAux_ok 0 initList init_ok 1 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_2 : a 2 = 11 := by
  have h := checkInitAux_ok 0 initList init_ok 2 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_3 : a 3 = 1 := by
  have h := checkInitAux_ok 0 initList init_ok 3 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_4 : a 4 = 1110 := by
  have h := checkInitAux_ok 0 initList init_ok 4 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_5 : a 5 = 110 := by
  have h := checkInitAux_ok 0 initList init_ok 5 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_6 : a 6 = 111110 := by
  have h := checkInitAux_ok 0 initList init_ok 6 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_7 : a 7 = 11100 := by
  have h := checkInitAux_ok 0 initList init_ok 7 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_8 : a 8 = 11111011 := by
  have h := checkInitAux_ok 0 initList init_ok 8 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_9 : a 9 = 1110001 := by
  have h := checkInitAux_ok 0 initList init_ok 9 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_10 : a 10 = 1111111110 := by
  have h := checkInitAux_ok 0 initList init_ok 10 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_11 : a 11 = 111111110 := by
  have h := checkInitAux_ok 0 initList init_ok 11 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_12 : a 12 = 111111111110 := by
  have h := checkInitAux_ok 0 initList init_ok 12 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_13 : a 13 = 11111111110 := by
  have h := checkInitAux_ok 0 initList init_ok 13 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_14 : a 14 = 11111111111110 := by
  have h := checkInitAux_ok 0 initList init_ok 14 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_15 : a 15 = 1111111111110 := by
  have h := checkInitAux_ok 0 initList init_ok 15 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_16 : a 16 = 1111111111111110 := by
  have h := checkInitAux_ok 0 initList init_ok 16 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_17 : a 17 = 111111111111110 := by
  have h := checkInitAux_ok 0 initList init_ok 17 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_18 : a 18 = 111111111111111110 := by
  have h := checkInitAux_ok 0 initList init_ok 18 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_19 : a 19 = 11111111111111110 := by
  have h := checkInitAux_ok 0 initList init_ok 19 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_20 : a 20 = 11111111111111111110 := by
  have h := checkInitAux_ok 0 initList init_ok 20 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_21 : a 21 = 1111111111111111110 := by
  have h := checkInitAux_ok 0 initList init_ok 21 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_22 : a 22 = 1111111111111111111110 := by
  have h := checkInitAux_ok 0 initList init_ok 22 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_23 : a 23 = 111111111111111111100 := by
  have h := checkInitAux_ok 0 initList init_ok 23 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_24 : a 24 = 111111111111111111111111 := by
  have h := checkInitAux_ok 0 initList init_ok 24 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_25 : a 25 = 11111111111111111111111 := by
  have h := checkInitAux_ok 0 initList init_ok 25 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_26 : a 26 = 11111111111111111111111111 := by
  have h := checkInitAux_ok 0 initList init_ok 26 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_27 : a 27 = 1111111111111111111111111 := by
  have h := checkInitAux_ok 0 initList init_ok 27 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_28 : a 28 = 1111111111111111111111111111 := by
  have h := checkInitAux_ok 0 initList init_ok 28 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_29 : a 29 = 111111111111111111111111111 := by
  have h := checkInitAux_ok 0 initList init_ok 29 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_30 : a 30 = 111111111111111111111111111111 := by
  have h := checkInitAux_ok 0 initList init_ok 30 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_31 : a 31 = 11111111111111111111111111111 := by
  have h := checkInitAux_ok 0 initList init_ok 31 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_32 : a 32 = 11111111111111111111111111111111 := by
  have h := checkInitAux_ok 0 initList init_ok 32 (by decide)
  simpa [initList, lookupL] using h
lemma a_val_33 : a 33 = 1111111111111111111111111111111 := by
  have h := checkInitAux_ok 0 initList init_ok 33 (by decide)
  simpa [initList, lookupL] using h

-- 3. Moving right-front triangle T_5
def evalTri (tr : List (List Bool)) (dx y : ℤ) : Bool :=
  if 0 ≤ dx ∧ dx ≤ 5 ∧ -dx ≤ y ∧ y ≤ dx then
    lookupL (lookupL tr dx.toNat []) (y + dx).toNat true
  else true

def TriMatch (t : ℕ) (tr : List (List Bool)) : Prop :=
  ∀ dx y : ℤ, 0 ≤ dx ∧ dx ≤ 5 ∧ -dx ≤ y ∧ y ≤ dx →
    state t ((t : ℤ) - dx) y = evalTri tr dx y

lemma triMatch_eval (t : ℕ) (ht : 5 ≤ t) (tr : List (List Bool)) (hm : TriMatch t tr)
    (dx' y' : ℤ) (hdx : dx' ≤ 5) :
    state t ((t : ℤ) - dx') y' = evalTri tr dx' y' := by
  by_cases hin : 0 ≤ dx' ∧ dx' ≤ 5 ∧ -dx' ≤ y' ∧ y' ≤ dx'
  · exact hm dx' y' hin
  · unfold evalTri
    rw [if_neg hin]
    apply state_out_cone t (by omega)
    cases abs_cases ((t : ℤ) - dx') <;> cases abs_cases y' <;> omega

def nextTri (tr : List (List Bool)) : List (List Bool) :=
  buildL (5 + 1) fun idx =>
    let dx : ℤ := idx
    buildL (2 * idx + 1) fun iy =>
      let y : ℤ := (iy : ℤ) - dx
      let c := evalTri tr (dx - 1) y
      let l := evalTri tr dx y
      let r := evalTri tr (dx - 2) y
      let d := evalTri tr (dx - 1) (y - 1)
      let u := evalTri tr (dx - 1) (y + 1)
      Nat.testBit 633 (c.toNat + 2 * (l.toNat + r.toNat + d.toNat + u.toNat))

lemma triMatch_step (t : ℕ) (ht : 5 ≤ t) (tr : List (List Bool)) (hm : TriMatch t tr) :
    TriMatch (t + 1) (nextTri tr) := by
  intro dx y h
  change step (state t) (((t + 1 : ℕ) : ℤ) - dx) y = evalTri (nextTri tr) dx y
  unfold evalTri nextTri
  rw [if_pos h]
  rw [lookupL_buildL, if_pos (by omega : dx.toNat < 5 + 1)]
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

def tri0 : List (List Bool) := [[false], [false, false, false], [false, true, false, true, false], [false, false, false, true, false, false, false], [false, true, false, true, true, true, false, true, false], [false, false, false, true, false, true, false, true, false, false, false]]

def triSeq : ℕ → List (List Bool)
  | 0 => tri0
  | k + 1 => nextTri (triSeq k)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 200000 in
lemma triSeq_period_base : triSeq 8 = tri0 := by decide

lemma triSeq_add_period (k : ℕ) : triSeq (k + 8) = triSeq k := by
  induction k with
  | zero => simpa [triSeq] using triSeq_period_base
  | succ k ih =>
    have heq : k + 1 + 8 = (k + 8) + 1 := by omega
    rw [heq, triSeq, ih, ← triSeq]

lemma triSeq_mod (k : ℕ) : triSeq k = triSeq (k % 8) := by
  have hdiv : k = 8 * (k / 8) + k % 8 := (Nat.div_add_mod k 8).symm
  conv_lhs => rw [hdiv]
  generalize k / 8 = q
  induction q with
  | zero => simp
  | succ q ih =>
    have heq : 8 * (q + 1) + k % 8 = (8 * q + k % 8) + 8 := by ring
    rw [heq, triSeq_add_period, ih]

-- 4. Self-preserving interior strip
def checkT0 : Bool :=
  let c := cfg 31
  (List.range (5 + 1)).all (fun idx =>
    (List.range (2 * idx + 1)).all (fun iy =>
      evalBox c.2 31 c.1 ((31 : ℤ) - idx) ((iy : ℤ) - idx) ==
        evalTri tri0 idx ((iy : ℤ) - idx))) &&
  (List.range (55)).all (fun ix =>
    evalBox c.2 31 c.1 ((ix : ℤ) - 27) 0 == true)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 200000 in
lemma checkT0_true : checkT0 = true := by decide

lemma triMatch_t0 : TriMatch 31 tri0 := by
  have hc := checkT0_true
  unfold checkT0 at hc
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
  intro dx y h
  rw [state_eq_cfg 31]
  have h1 := hc.1 dx.toNat (by omega) (y + dx).toNat (by omega)
  have edx : ((dx.toNat : ℕ) : ℤ) = dx := by omega
  have ey : (((y + dx).toNat : ℕ) : ℤ) - dx = y := by omega
  rw [edx, ey] at h1
  exact h1

lemma triMatch_seq (k : ℕ) : TriMatch (31 + k) (triSeq k) := by
  induction k with
  | zero => simpa [triSeq] using triMatch_t0
  | succ k ih =>
    have heq : 31 + (k + 1) = (31 + k) + 1 := by omega
    rw [heq]
    exact triMatch_step (31 + k) (by omega) (triSeq k) ih

lemma xaxis_triple_stay (t : ℕ) (x : ℤ)
    (hl : state t (x - 1) 0 = true) (hc : state t x 0 = true) (hr : state t (x + 1) 0 = true) :
    state (t + 1) x 0 = true := by
  change step (state t) x 0 = true
  unfold step
  have hd : state t x (0 - 1) = state t x 1 := by
    have : (0 : ℤ) - 1 = -(1 : ℤ) := by omega
    rw [this, state_neg_y]
  have hu : (0 : ℤ) + 1 = 1 := by omega
  rw [hc, hl, hr, hd, hu]
  cases state t x 1 <;> decide

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 200000 in
lemma tri_feed_y0 : ∀ r ∈ List.range 8,
    evalTri (triSeq r) 4 0 = true ∧ evalTri (triSeq r) 5 0 = true := by decide

lemma strip_hold (t : ℕ) (ht : 31 ≤ t) :
    ∀ x : ℤ, |x| ≤ (t : ℤ) - 4 → state t x 0 = true := by
  obtain ⟨k, rfl⟩ : ∃ k, t = 31 + k := ⟨t - 31, by omega⟩
  induction k with
  | zero =>
    have hc := checkT0_true
    unfold checkT0 at hc
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hc
    intro x hx
    rw [Nat.add_zero, state_eq_cfg 31]
    have hix : (x + 27).toNat < 55 := by
      cases abs_cases x <;> omega
    have h2 := hc.2 (x + 27).toNat hix
    have ex : (((x + 27).toNat : ℕ) : ℤ) - 27 = x := by
      cases abs_cases x <;> omega
    rw [ex] at h2
    exact h2
  | succ k ih =>
    intro x hx
    have ihk := ih (by omega)
    by_cases hin : |x| ≤ ((31 + k : ℕ) : ℤ) - 4 - 1
    · have heq : 31 + (k + 1) = (31 + k) + 1 := by omega
      rw [heq]
      apply xaxis_triple_stay (31 + k) x
      · exact ihk (x - 1) (by cases abs_cases x <;> cases abs_cases (x - 1) <;> omega)
      · exact ihk x (by omega)
      · exact ihk (x + 1) (by cases abs_cases x <;> cases abs_cases (x + 1) <;> omega)
    · have hwlog : ∀ u : ℤ, 0 ≤ u →
          (u = ((31 + (k + 1) : ℕ) : ℤ) - 5 ∨ u = ((31 + (k + 1) : ℕ) : ℤ) - 4) →
          state (31 + (k + 1)) u 0 = true := by
        intro u _ hcases
        have hm := triMatch_seq (k + 1)
        rw [triSeq_mod] at hm
        have hf := tri_feed_y0 ((k + 1) % 8) (by rw [List.mem_range]; exact Nat.mod_lt _ (by decide))
        rcases hcases with rfl | rfl
        · rw [hm 5 0 (by omega)]; exact hf.2
        · rw [hm 4 0 (by omega)]; exact hf.1
      by_cases hnn : 0 ≤ x
      · exact hwlog x hnn (by rw [abs_of_nonneg hnn] at hx hin; omega)
      · rw [← state_neg_x (31 + (k + 1)) x 0]
        exact hwlog (-x) (by omega) (by cases abs_cases x <;> omega)

-- 5. Left-to-origin reading: decomposition, recurrence, and generating function
def tailVal (r : ℕ) : ℤ :=
  ∑ i ∈ Finset.range 4, ((evalTri (triSeq r) (i : ℤ) 0).toNat : ℤ) * 10 ^ (3 - i)

def G (k : ℕ) : ℤ := ∑ x ∈ Finset.range k, (10 : ℤ) ^ x

lemma G_succ (k : ℕ) : G (k + 1) = G k + 10 ^ k := by
  unfold G; rw [Finset.sum_range_succ]

lemma a_decomp (n : ℕ) (hn : 31 ≤ n) :
    (a n : ℤ) = 10 ^ (n - 3) * tailVal ((n - 31) % 8) + G (n - 3) := by
  unfold a
  push_cast
  have hsplit : n + 1 = 4 + (n - 3) := by omega
  rw [hsplit, Finset.sum_range_add]
  have hm := triMatch_seq (n - 31)
  have htn : 31 + (n - 31) = n := by omega
  rw [htn, triSeq_mod] at hm
  congr 1
  · unfold tailVal
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have hx : ((i : ℕ) : ℤ) - (n : ℤ) = -((n : ℤ) - (i : ℤ)) := by ring
    rw [hx, state_neg_x, hm (i : ℤ) 0 (by omega)]
    have hp : (10 : ℤ) ^ (n - i) = 10 ^ (n - 3) * 10 ^ (3 - i) := by
      rw [← pow_add]; congr 1; omega
    rw [hp]; ring
  · unfold G
    rw [← Finset.sum_range_reflect (fun x => (10 : ℤ) ^ x) (n - 3)]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_range] at hx
    have hs : state n (((4 + x : ℕ) : ℤ) - (n : ℤ)) 0 = true := by
      apply strip_hold n hn
      rw [abs_of_nonpos (by omega)]
      omega
    rw [hs]
    have he : n - (4 + x) = n - 3 - 1 - x := by omega
    rw [he]
    simp

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 200000 in
lemma tail_periodic : ∀ r0 ∈ List.range 8,
    1000 * tailVal ((r0 + 3) % 8) - 100 * tailVal ((r0 + 2) % 8) -
      1000 * tailVal ((r0 + 1) % 8) - (-100) * tailVal r0 +
      (111 - 11 - 100) = 0 := by decide

lemma rec_big (m : ℕ) :
    (a (m + 34) : ℤ) = a (m + 34 - 1) + 100 * a (m + 34 - 2) - 100 * a (m + 34 - 3) := by
  rw [a_decomp (m + 34) (by omega), a_decomp (m + 34 - 1) (by omega),
    a_decomp (m + 34 - 2) (by omega), a_decomp (m + 34 - 3) (by omega)]
  have e0 : (m + 34 - 31) % 8 = (m % 8 + 3) % 8 := by omega
  have e1 : (m + 34 - 1 - 31) % 8 = (m % 8 + 2) % 8 := by omega
  have e2 : (m + 34 - 2 - 31) % 8 = (m % 8 + 1) % 8 := by omega
  have e3 : (m + 34 - 3 - 31) % 8 = m % 8 := by omega
  have p3 : m + 34 - 3 - 3 = m + 28 := by omega
  have p1 : m + 34 - 1 - 3 = m + 30 := by omega
  have p2 : m + 34 - 2 - 3 = m + 29 := by omega
  have p0 : m + 34 - 3 = m + 31 := by omega
  rw [e0, e1, e2, e3, p3, p1, p2, p0]
  have hr_lt : m % 8 < 8 := Nat.mod_lt _ (by decide)
  have hp := tail_periodic (m % 8) (by rw [List.mem_range]; exact hr_lt)
  generalize m % 8 = r at hp ⊢
  generalize tailVal = tv at hp ⊢
  obtain ⟨q, hq⟩ : ∃ q, q = m + 28 := ⟨_, rfl⟩
  rw [show m + 31 = q + 1 + 1 + 1 by omega, show m + 30 = q + 1 + 1 by omega,
    show m + 29 = q + 1 by omega, show m + 28 = q by omega]
  simp only [G_succ, pow_succ]
  generalize G q = g
  generalize (10 : ℤ) ^ q = P
  linear_combination P * hp

lemma rec_claim (n : ℕ) (hn : 26 < n) :
    (a n : ℤ) = a (n - 1) + 100 * a (n - 2) - 100 * a (n - 3) := by
  by_cases hbig : 34 ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 34 := ⟨n - 34, by omega⟩
    exact rec_big m
  · interval_cases n <;> norm_num [a_val_0, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8, a_val_9, a_val_10, a_val_11, a_val_12, a_val_13, a_val_14, a_val_15, a_val_16, a_val_17, a_val_18, a_val_19, a_val_20, a_val_21, a_val_22, a_val_23, a_val_24, a_val_25, a_val_26, a_val_27, a_val_28, a_val_29, a_val_30, a_val_31, a_val_32, a_val_33]

lemma gf_claim :
    PowerSeries.mk (fun n => (a n : ℤ)) * ((X - 1) * (10 * X - 1) * (10 * X + 1)) =
      -1100 * X ^ 26 + 1000 * X ^ 25 + 11 * X ^ 24 - 10 * X ^ 23 - 110900 * X ^ 12 + 101000 * X ^ 11 + 10009 * X ^ 10 - 10 * X ^ 9 - 89 * X ^ 8 - 10 * X ^ 7 + 100 * X ^ 6 + 9 * X ^ 4 + 90 * X ^ 3 - 89 * X ^ 2 - X + 1 := by
  let s := PowerSeries.mk (fun n => (a n : ℤ))
  have hring : s * ((X - 1) * (10 * X - 1) * (10 * X + 1)) =
      C (1 : ℤ) * (s * X ^ 0) + C (-1 : ℤ) * (s * X ^ 1) + C (-100 : ℤ) * (s * X ^ 2) + C (100 : ℤ) * (s * X ^ 3) := by
    simp only [map_neg, map_one, map_ofNat]; ring
  rw [hring]
  have hrhs : (-1100 * X ^ 26 + 1000 * X ^ 25 + 11 * X ^ 24 - 10 * X ^ 23 - 110900 * X ^ 12 + 101000 * X ^ 11 + 10009 * X ^ 10 - 10 * X ^ 9 - 89 * X ^ 8 - 10 * X ^ 7 + 100 * X ^ 6 + 9 * X ^ 4 + 90 * X ^ 3 - 89 * X ^ 2 - X + 1 : PowerSeries ℤ) =
      C (1 : ℤ) * X ^ 0 + C (-1 : ℤ) * X ^ 1 + C (-89 : ℤ) * X ^ 2 + C (90 : ℤ) * X ^ 3 + C (9 : ℤ) * X ^ 4 + C (100 : ℤ) * X ^ 6 + C (-10 : ℤ) * X ^ 7 + C (-89 : ℤ) * X ^ 8 + C (-10 : ℤ) * X ^ 9 + C (10009 : ℤ) * X ^ 10 + C (101000 : ℤ) * X ^ 11 + C (-110900 : ℤ) * X ^ 12 + C (-10 : ℤ) * X ^ 23 + C (11 : ℤ) * X ^ 24 + C (1000 : ℤ) * X ^ 25 + C (-1100 : ℤ) * X ^ 26 := by
    simp only [map_neg, map_one, map_ofNat]; ring
  rw [hrhs]
  ext n
  simp only [map_add, coeff_C_mul]
  simp only [coeff_mul_X_pow', coeff_X_pow, s, coeff_mk]
  by_cases hn : n ≤ 26
  · interval_cases n <;> norm_num [a_val_0, a_val_1, a_val_2, a_val_3, a_val_4, a_val_5, a_val_6, a_val_7, a_val_8, a_val_9, a_val_10, a_val_11, a_val_12, a_val_13, a_val_14, a_val_15, a_val_16, a_val_17, a_val_18, a_val_19, a_val_20, a_val_21, a_val_22, a_val_23, a_val_24, a_val_25, a_val_26, a_val_27, a_val_28, a_val_29, a_val_30, a_val_31, a_val_32, a_val_33]
  · have hrec := rec_claim n (by omega)
    simp [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega, show n ≠ 8 by omega, show n ≠ 9 by omega, show n ≠ 10 by omega, show n ≠ 11 by omega, show n ≠ 12 by omega, show n ≠ 23 by omega, show n ≠ 24 by omega, show n ≠ 25 by omega, show n ≠ 26 by omega, show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega]
    linarith

end StripProof_S_oeis_a283400


lemma previous : (∀ n : ℕ, 26 < n → (a n : ℤ) = a (n - 1) + 100 * a (n - 2) - 100 * a (n - 3)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * ((X - 1) * (10 * X - 1) * (10 * X + 1)) = -1100 * X ^ 26 + 1000 * X ^ 25 + 11 * X ^ 24 - 10 * X ^ 23 - 110900 * X ^ 12 + 101000 * X ^ 11 + 10009 * X ^ 10 - 10 * X ^ 9 - 89 * X ^ 8 - 10 * X ^ 7 + 100 * X ^ 6 + 9 * X ^ 4 + 90 * X ^ 3 - 89 * X ^ 2 - X + 1 :=
  ⟨rec_claim, gf_claim⟩

lemma cell_bridge (n : ℕ) (x y : ℤ) : OMA.S_oeis_a283400.cell 633 n x y = state n x y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
    simp only [OMA.S_oeis_a283400.cell, state, step, ih]
    congr 1
    omega

lemma value_bridge (n : ℕ) : OMA.S_oeis_a283400.a n = (a n : ℤ) := by
  unfold OMA.S_oeis_a283400.a a
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
  ext n
  simp
end Adapt283400

open Adapt283400 (value_bridge map_series previous)

theorem OMA.solution : type_of% @OMA.S_oeis_a283400.main := by
  simp only [value_bridge]
  obtain ⟨hrec, hgf⟩ := previous
  refine ⟨?_ , ?_ ⟩
  · intro n hn
    exact_mod_cast hrec n (by omega)
  · have h := congrArg (PowerSeries.map (Int.castRingHom ℚ)) hgf
    simpa only [map_mul, map_one, map_add, map_sub, map_pow, map_neg, map_ofNat, PowerSeries.map_X, map_series, Int.cast_natCast] using h
