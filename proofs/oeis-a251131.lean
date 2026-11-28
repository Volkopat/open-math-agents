import OMAStatements.S_oeis_a251131
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: transfer matrix on the 27 rows (Fin 3 -> Fin 3); arrays counted row by row (Fin.init/Fin.snoc).
-- Dual vectors u_3..u_10 (tabulated, decide +kernel) satisfy the char-poly identity shifted by 3, giving the
-- order-7 recurrence for a(k+10); closed form by induction from a3..a9; g.f. by coefficient comparison.

namespace OMA.S_oeis_a251131

open PowerSeries

abbrev St := Fin 3 → Fin 3

def ok (r s : St) : Prop :=
  okBlock (r 0) (r 1) (s 0) (s 1) ∧ okBlock (r 1) (r 2) (s 1) (s 2)

instance (r s : St) : Decidable (ok r s) := by unfold ok; infer_instance

def w : ℕ → St → ℕ
  | 0, _ => 1
  | k + 1, s => ∑ r : St, if ok r s then w k r else 0

def u : ℕ → St → ℕ
  | 0, _ => 1
  | j + 1, r => ∑ s : St, if ok r s then u j s else 0

def Gd (k : ℕ) (x : Fin (k + 1) → St) : Prop := ∀ i : Fin k, ok (x i.castSucc) (x i.succ)

instance (k : ℕ) : DecidablePred (Gd k) := fun x => by unfold Gd; infer_instance

lemma iv_iff (k : ℕ) (x : Fin (k + 1) → St) : isValid k x ↔ Gd k x := by
  unfold isValid Gd ok
  apply forall_congr'; intro i
  rw [Fin.forall_fin_two]
  rfl

lemma gd_succ (k : ℕ) (x : Fin (k + 2) → St) :
    Gd (k + 1) x ↔ Gd k (Fin.init x) ∧ ok (x (Fin.last k).castSucc) (x (Fin.last (k + 1))) := by
  unfold Gd
  rw [Fin.forall_fin_succ']
  simp only [Fin.init, Fin.succ_castSucc, Fin.succ_last]

def cnt (k : ℕ) (s : St) : ℕ :=
  (Finset.univ.filter (fun x : Fin (k + 1) → St => x (Fin.last k) = s ∧ Gd k x)).card

lemma cnt_zero (s : St) : cnt 0 s = 1 := by
  unfold cnt
  rw [Finset.card_eq_one]
  refine ⟨fun _ => s, ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨h, -⟩; funext i; rw [show i = Fin.last 0 from Fin.ext (by omega)]; exact h
  · rintro rfl; exact ⟨rfl, fun i => i.elim0⟩

lemma cnt_succ (k : ℕ) (s : St) :
    cnt (k + 1) s = ∑ r : St, if ok r s then cnt k r else 0 := by
  have e : cnt (k + 1) s = (Finset.univ.filter
      (fun g : Fin (k + 1) → St => Gd k g ∧ ok (g (Fin.last k)) s)).card := by
    unfold cnt
    apply Finset.card_nbij' (fun f => Fin.init f) (fun g => Fin.snoc g s)
    · intro f hf
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hf ⊢
      obtain ⟨hl, hg⟩ := hf
      rw [gd_succ] at hg
      refine ⟨hg.1, ?_⟩
      have := hg.2; rw [hl] at this; simpa [Fin.init] using this
    · intro g hg
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hg ⊢
      obtain ⟨hg, ha⟩ := hg
      refine ⟨by simp, ?_⟩
      rw [gd_succ]
      refine ⟨by simpa using hg, ?_⟩
      simpa using ha
    · intro f hf
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hf
      rw [← hf.1]; exact Fin.snoc_init_self f
    · intro g _; exact Fin.init_snoc _ _
  rw [e, Finset.card_eq_sum_card_fiberwise (f := fun g : Fin (k + 1) → St => g (Fin.last k))
    (t := Finset.univ) (fun g _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.filter_filter]
  split_ifs with h
  · unfold cnt; congr 1; apply Finset.filter_congr
    intro g _
    constructor
    · rintro ⟨⟨hg, -⟩, hx⟩; exact ⟨hx, hg⟩
    · rintro ⟨hx, hg⟩; exact ⟨⟨hg, hx ▸ h⟩, hx⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro g - ⟨⟨-, ha⟩, hx⟩; exact h (hx ▸ ha)

lemma cnt_eq (k : ℕ) (s : St) : cnt k s = w k s := by
  induction k generalizing s with
  | zero => rw [cnt_zero]; rfl
  | succ k ih =>
    rw [cnt_succ k s, w]
    apply Finset.sum_congr rfl
    intro r _
    rw [ih r]

lemma card_w (k : ℕ) : (Finset.univ.filter (isValid k)).card = ∑ s : St, w k s := by
  rw [Finset.filter_congr (fun x _ => iv_iff k x)]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g : Fin (k + 1) → St => g (Fin.last k))
    (t := Finset.univ) (fun g _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro s _
  rw [← cnt_eq, cnt, Finset.filter_filter]
  congr 1; apply Finset.filter_congr
  intro x _; exact and_comm

lemma a_w (j : ℕ) (hj : 1 ≤ j) : a j = ∑ s : St, w j s := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact card_w (k + 1)

lemma dual (j k : ℕ) : ∑ s : St, w (k + j) s = ∑ r : St, w k r * u j r := by
  induction j generalizing k with
  | zero => simp [u]
  | succ j ih =>
    rw [show k + (j + 1) = (k + 1) + j by ring, ih (k + 1)]
    simp only [w, u, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _
    split_ifs <;> simp

lemma a_u (j : ℕ) (hj : 1 ≤ j) : a j = ∑ r : St, u j r := by
  rw [a_w j hj, show j = 0 + j by ring, dual j 0]
  simp [w]

def tb (L : List ℕ) (x : St) : ℕ := L.getD ((x 0).val * 9 + (x 1).val * 3 + (x 2).val) 0

def T1 : List ℕ := [10, 13, 18, 5, 8, 14, 3, 3, 9, 4, 6, 9, 1, 4, 8, 0, 0, 6, 1, 2, 3, 0, 1, 2, 0, 0, 3]
def T2 : List ℕ := [24, 45, 85, 6, 21, 55, 3, 3, 24, 6, 14, 28, 0, 15, 37, 0, 0, 21, 1, 3, 6, 0, 1, 3, 0, 0, 15]
def T3 : List ℕ := [62, 124, 283, 6, 37, 136, 3, 3, 40, 8, 25, 62, 0, 31, 94, 0, 0, 37, 1, 4, 10, 0, 1, 4, 0, 0, 31]
def T4 : List ℕ := [134, 287, 740, 6, 77, 299, 3, 3, 80, 10, 39, 115, 0, 71, 225, 0, 0, 77, 1, 5, 15, 0, 1, 5, 0, 0, 71]
def T5 : List ℕ := [288, 619, 1719, 6, 151, 631, 3, 3, 154, 12, 56, 191, 0, 145, 477, 0, 0, 151, 1, 6, 21, 0, 1, 6, 0, 0, 145]
def T6 : List ℕ := [592, 1273, 3687, 6, 307, 1285, 3, 3, 310, 14, 76, 294, 0, 301, 983, 0, 0, 307, 1, 7, 28, 0, 1, 7, 0, 0, 301]
def T7 : List ℕ := [1210, 2566, 7565, 6, 613, 2578, 3, 3, 616, 16, 99, 428, 0, 607, 1964, 0, 0, 613, 1, 8, 36, 0, 1, 8, 0, 0, 607]
def T8 : List ℕ := [2442, 5115, 15116, 6, 1233, 5127, 3, 3, 1236, 18, 125, 597, 0, 1227, 3901, 0, 0, 1233, 1, 9, 45, 0, 1, 9, 0, 0, 1227]
def T9 : List ℕ := [4916, 10165, 29833, 6, 2467, 10177, 3, 3, 2470, 20, 154, 805, 0, 2461, 7711, 0, 0, 2467, 1, 10, 55, 0, 1, 10, 0, 0, 2461]
def T10 : List ℕ := [9860, 20189, 58603, 6, 4943, 20201, 3, 3, 4946, 22, 186, 1056, 0, 4937, 15267, 0, 0, 4943, 1, 11, 66, 0, 1, 11, 0, 0, 4937]

set_option maxRecDepth 100000 in
lemma hu1 : ∀ x, u 1 x = tb T1 x := by decide +kernel

set_option maxRecDepth 100000 in
lemma hu2' : ∀ x, (∑ y : St, if ok x y then tb T1 y else 0) = tb T2 x := by decide +kernel

lemma hu2 (x : St) : u 2 x = tb T2 x := by
  show (∑ y : St, if ok x y then u 1 y else 0) = _
  simp only [hu1]; exact hu2' x

set_option maxRecDepth 100000 in
lemma hu3' : ∀ x, (∑ y : St, if ok x y then tb T2 y else 0) = tb T3 x := by decide +kernel

lemma hu3 (x : St) : u 3 x = tb T3 x := by
  show (∑ y : St, if ok x y then u 2 y else 0) = _
  simp only [hu2]; exact hu3' x

set_option maxRecDepth 100000 in
lemma hu4' : ∀ x, (∑ y : St, if ok x y then tb T3 y else 0) = tb T4 x := by decide +kernel

lemma hu4 (x : St) : u 4 x = tb T4 x := by
  show (∑ y : St, if ok x y then u 3 y else 0) = _
  simp only [hu3]; exact hu4' x

set_option maxRecDepth 100000 in
lemma hu5' : ∀ x, (∑ y : St, if ok x y then tb T4 y else 0) = tb T5 x := by decide +kernel

lemma hu5 (x : St) : u 5 x = tb T5 x := by
  show (∑ y : St, if ok x y then u 4 y else 0) = _
  simp only [hu4]; exact hu5' x

set_option maxRecDepth 100000 in
lemma hu6' : ∀ x, (∑ y : St, if ok x y then tb T5 y else 0) = tb T6 x := by decide +kernel

lemma hu6 (x : St) : u 6 x = tb T6 x := by
  show (∑ y : St, if ok x y then u 5 y else 0) = _
  simp only [hu5]; exact hu6' x

set_option maxRecDepth 100000 in
lemma hu7' : ∀ x, (∑ y : St, if ok x y then tb T6 y else 0) = tb T7 x := by decide +kernel

lemma hu7 (x : St) : u 7 x = tb T7 x := by
  show (∑ y : St, if ok x y then u 6 y else 0) = _
  simp only [hu6]; exact hu7' x

set_option maxRecDepth 100000 in
lemma hu8' : ∀ x, (∑ y : St, if ok x y then tb T7 y else 0) = tb T8 x := by decide +kernel

lemma hu8 (x : St) : u 8 x = tb T8 x := by
  show (∑ y : St, if ok x y then u 7 y else 0) = _
  simp only [hu7]; exact hu8' x

set_option maxRecDepth 100000 in
lemma hu9' : ∀ x, (∑ y : St, if ok x y then tb T8 y else 0) = tb T9 x := by decide +kernel

lemma hu9 (x : St) : u 9 x = tb T9 x := by
  show (∑ y : St, if ok x y then u 8 y else 0) = _
  simp only [hu8]; exact hu9' x

set_option maxRecDepth 100000 in
lemma hu10' : ∀ x, (∑ y : St, if ok x y then tb T9 y else 0) = tb T10 x := by decide +kernel

lemma hu10 (x : St) : u 10 x = tb T10 x := by
  show (∑ y : St, if ok x y then u 9 y else 0) = _
  simp only [hu9]; exact hu10' x

set_option maxRecDepth 100000 in
lemma hT : ∀ x : St, tb T10 x + 2 * tb T3 x + 14 * tb T5 x + 13 * tb T8 x =
    9 * tb T4 x + 5 * tb T6 x + 10 * tb T7 x + 6 * tb T9 x := by decide +kernel

lemma keyW (k : ℕ) :
    (∑ s : St, w (k + 10) s) + 2 * (∑ s : St, w (k + 3) s) + 14 * (∑ s : St, w (k + 5) s)
      + 13 * (∑ s : St, w (k + 8) s) =
    9 * (∑ s : St, w (k + 4) s) + 5 * (∑ s : St, w (k + 6) s) + 10 * (∑ s : St, w (k + 7) s)
      + 6 * (∑ s : St, w (k + 9) s) := by
  rw [dual 10 k, dual 3 k, dual 5 k, dual 8 k, dual 4 k, dual 6 k, dual 7 k, dual 9 k]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro x _
  have := hT x
  rw [hu3, hu4, hu5, hu6, hu7, hu8, hu9, hu10]
  calc w k x * tb T10 x + 2 * (w k x * tb T3 x) + 14 * (w k x * tb T5 x) + 13 * (w k x * tb T8 x)
      = w k x * (tb T10 x + 2 * tb T3 x + 14 * tb T5 x + 13 * tb T8 x) := by ring
    _ = w k x * (9 * tb T4 x + 5 * tb T6 x + 10 * tb T7 x + 6 * tb T9 x) := by rw [this]
    _ = 9 * (w k x * tb T4 x) + 5 * (w k x * tb T6 x) + 10 * (w k x * tb T7 x)
        + 6 * (w k x * tb T9 x) := by ring

lemma arec (k : ℕ) : (a (k + 10) : ℚ) = 6 * a (k + 9) - 13 * a (k + 8) + 10 * a (k + 7)
    + 5 * a (k + 6) - 14 * a (k + 5) + 9 * a (k + 4) - 2 * a (k + 3) := by
  have key := keyW k
  rw [← a_w (k + 10) (by omega), ← a_w (k + 3) (by omega), ← a_w (k + 5) (by omega),
    ← a_w (k + 8) (by omega), ← a_w (k + 4) (by omega), ← a_w (k + 6) (by omega),
    ← a_w (k + 7) (by omega), ← a_w (k + 9) (by omega)] at key
  have key' : ((a (k + 10) + 2 * a (k + 3) + 14 * a (k + 5) + 13 * a (k + 8) : ℕ) : ℚ) =
      ((9 * a (k + 4) + 5 * a (k + 6) + 10 * a (k + 7) + 6 * a (k + 9) : ℕ) : ℚ) := by
    rw [key]
  push_cast at key'
  linarith

lemma v0 : a 0 = 0 := rfl
set_option maxRecDepth 100000 in
lemma v1 : a 1 = 133 := by rw [a_u 1 (by omega)]; simp only [hu1]; decide +kernel
set_option maxRecDepth 100000 in
lemma v2 : a 2 = 416 := by rw [a_u 2 (by omega)]; simp only [hu2]; decide +kernel
set_option maxRecDepth 100000 in
lemma v3 : a 3 = 1002 := by rw [a_u 3 (by omega)]; simp only [hu3]; decide +kernel
set_option maxRecDepth 100000 in
lemma v4 : a 4 = 2264 := by rw [a_u 4 (by omega)]; simp only [hu4]; decide +kernel
set_option maxRecDepth 100000 in
lemma v5 : a 5 = 4786 := by rw [a_u 5 (by omega)]; simp only [hu5]; decide +kernel
set_option maxRecDepth 100000 in
lemma v6 : a 6 = 9786 := by rw [a_u 6 (by omega)]; simp only [hu6]; decide +kernel
set_option maxRecDepth 100000 in
lemma v7 : a 7 = 19548 := by rw [a_u 7 (by omega)]; simp only [hu7]; decide +kernel
set_option maxRecDepth 100000 in
lemma v8 : a 8 = 38674 := by rw [a_u 8 (by omega)]; simp only [hu8]; decide +kernel
set_option maxRecDepth 100000 in
lemma v9 : a 9 = 76196 := by rw [a_u 9 (by omega)]; simp only [hu9]; decide +kernel

def f (n : ℕ) : ℚ := (-873 + 49 * (-1 : ℚ) ^ n + 841 * (2 : ℚ) ^ (1 + n) - 614 * n
  - 11 * (n : ℚ) ^ 2 + 38 * (n : ℚ) ^ 3 + 5 * (n : ℚ) ^ 4) / 12

lemma closed (n : ℕ) (hn : 3 ≤ n) : (a n : ℚ) = f n := by
  have key : ∀ m : ℕ, (a (m + 3) : ℚ) = f (m + 3) ∧ (a (m + 4) : ℚ) = f (m + 4) ∧
      (a (m + 5) : ℚ) = f (m + 5) ∧ (a (m + 6) : ℚ) = f (m + 6) ∧
      (a (m + 7) : ℚ) = f (m + 7) ∧ (a (m + 8) : ℚ) = f (m + 8) ∧
      (a (m + 9) : ℚ) = f (m + 9) := by
    intro m
    induction m with
    | zero =>
      simp only [zero_add, f, v3, v4, v5, v6, v7, v8, v9]
      norm_num
    | succ m ih =>
      obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := ih
      refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
      rw [show m + 1 + 9 = m + 10 by ring, arec m, h0, h1, h2, h3, h4, h5, h6]
      simp only [f]
      push_cast
      ring
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  exact (key m).1

lemma ps (g : ℕ → ℚ) (n k : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk g * PowerSeries.X ^ k) = if k ≤ n then g (n-k) else 0 := by
  rw [PowerSeries.coeff_mul_X_pow']; simp

lemma ps1 (g : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk g * PowerSeries.X) = if 1 ≤ n then g (n-1) else 0 := by
  rw [← ps, pow_one]

theorem main_proof :
    (∀ n : ℕ, 10 ≤ n → (a n : ℤ) = 6 * a (n - 1) - 13 * a (n - 2) + 10 * a (n - 3) + 5 * a (n - 4) - 14 * a (n - 5) + 9 * a (n - 6) - 2 * a (n - 7)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 5 * (1 + X) * (1 - 2 * X)) =
      X * (133 - 382 * X + 235 * X ^ 2 + 330 * X ^ 3 - 597 * X ^ 4 + 264 * X ^ 5 + 27 * X ^ 6 - 26 * X ^ 7 - 4 * X ^ 8)) ∧
    (∀ n : ℕ, 3 ≤ n → (a n : ℚ) = (-873 + 49 * (-1 : ℚ) ^ n + 841 * (2 : ℚ) ^ (1 + n) - 614 * n - 11 * (n : ℚ) ^ 2 + 38 * (n : ℚ) ^ 3 + 5 * (n : ℚ) ^ 4) / 12) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
    have h := arec m
    rw [show m + 10 - 1 = m + 9 by omega, show m + 10 - 2 = m + 8 by omega,
      show m + 10 - 3 = m + 7 by omega, show m + 10 - 4 = m + 6 by omega,
      show m + 10 - 5 = m + 5 by omega, show m + 10 - 6 = m + 4 by omega,
      show m + 10 - 7 = m + 3 by omega]
    exact_mod_cast h
  · rw [show ((1 - X) ^ 5 * (1 + X) * (1 - 2 * X) : PowerSeries ℚ) =
        1 - PowerSeries.C (6:ℚ) * X + PowerSeries.C (13:ℚ) * X ^ 2
          - PowerSeries.C (10:ℚ) * X ^ 3 - PowerSeries.C (5:ℚ) * X ^ 4
          + PowerSeries.C (14:ℚ) * X ^ 5 - PowerSeries.C (9:ℚ) * X ^ 6
          + PowerSeries.C (2:ℚ) * X ^ 7 by
          simp only [map_ofNat]; ring,
      show (X * (133 - 382 * X + 235 * X ^ 2 + 330 * X ^ 3 - 597 * X ^ 4 + 264 * X ^ 5 + 27 * X ^ 6 - 26 * X ^ 7 - 4 * X ^ 8) : PowerSeries ℚ) =
        PowerSeries.C (133:ℚ) * X - PowerSeries.C (382:ℚ) * X ^ 2
          + PowerSeries.C (235:ℚ) * X ^ 3 + PowerSeries.C (330:ℚ) * X ^ 4
          - PowerSeries.C (597:ℚ) * X ^ 5 + PowerSeries.C (264:ℚ) * X ^ 6
          + PowerSeries.C (27:ℚ) * X ^ 7 - PowerSeries.C (26:ℚ) * X ^ 8
          - PowerSeries.C (4:ℚ) * X ^ 9 by
          simp only [map_ofNat]; ring]
    ext n
    simp only [mul_add, mul_sub, mul_one, map_add, map_sub, mul_left_comm _ (PowerSeries.C _),
      PowerSeries.coeff_C_mul, ps, ps1, PowerSeries.coeff_X, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow]
    rcases (show n ≤ 9 ∨ 10 ≤ n by omega) with h | h
    · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
      have hq := arec m
      simp [show m + 10 - 1 = m + 9 by omega, show m + 10 - 2 = m + 8 by omega,
        show m + 10 - 3 = m + 7 by omega, show m + 10 - 4 = m + 6 by omega,
        show m + 10 - 5 = m + 5 by omega, show m + 10 - 6 = m + 4 by omega,
        show m + 10 - 7 = m + 3 by omega,
        show m + 10 ≠ 1 by omega, show m + 10 ≠ 2 by omega, show m + 10 ≠ 3 by omega,
        show m + 10 ≠ 4 by omega, show m + 10 ≠ 5 by omega, show m + 10 ≠ 6 by omega,
        show m + 10 ≠ 7 by omega, show m + 10 ≠ 8 by omega, show m + 10 ≠ 9 by omega]
      rw [hq]; ring
  · intro n hn
    exact closed n hn

end OMA.S_oeis_a251131

theorem OMA.solution : type_of% @OMA.S_oeis_a251131.main := OMA.S_oeis_a251131.main_proof
