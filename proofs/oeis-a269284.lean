import OMAStatements.S_oeis_a269284
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: transfer matrix on states (row, pairs used in {0,1}); arrays split row by row (Fin.init/Fin.snoc).
-- Dual vectors u1..u3 (tabulated, decide +kernel) satisfy u3 + 441 u1 = 42 u2; recurrence, closed form, g.f. follow.

namespace OMA.S_oeis_a269284

open PowerSeries

abbrev Row := Fin 3 → Fin 4
abbrev St := Row × Fin 2

def hor (r : Row) : ℕ := ∑ j : Fin 2, if (r j.castSucc : ℕ) + (r j.succ : ℕ) = 3 then 1 else 0
def anti (r s : Row) : ℕ := ∑ j : Fin 2, if (r j.succ : ℕ) + (s j.castSucc : ℕ) = 3 then 1 else 0

def okc (p q : St) : Prop := (q.2 : ℕ) = p.2 + anti p.1 q.1 + hor q.1
instance (p q : St) : Decidable (okc p q) := by unfold okc; infer_instance

def w0 (p : St) : ℕ := if hor p.1 = p.2 then 1 else 0

def w : ℕ → St → ℕ
  | 0, p => w0 p
  | k + 1, q => ∑ p : St, if okc p q then w k p else 0

def u : ℕ → St → ℕ
  | 0, _ => 1
  | j + 1, p => ∑ q : St, if okc p q then u j q else 0

def pt (k : ℕ) (x : Fin (k + 1) → Row) : ℕ :=
  ∑ i, hor (x i) + ∑ i : Fin k, anti (x i.castSucc) (x i.succ)

lemma pt_eq (k : ℕ) (x : Fin (k + 1) → Row) : pairsTotallingThree k x = pt k x := by
  unfold pairsTotallingThree pt hor anti
  simp only [Finset.card_filter, Fintype.sum_prod_type]

lemma pt_succ (k : ℕ) (x : Fin (k + 2) → Row) : pt (k + 1) x =
    pt k (Fin.init x) + hor (x (Fin.last _)) + anti (x (Fin.last k).castSucc) (x (Fin.last (k + 1))) := by
  have h1 : ∑ i : Fin (k + 2), hor (x i) =
      ∑ i : Fin (k + 1), hor (Fin.init x i) + hor (x (Fin.last _)) := Fin.sum_univ_castSucc _
  have h2 : ∑ i : Fin (k + 1), anti (x i.castSucc) (x i.succ) =
      ∑ i : Fin k, anti (Fin.init x i.castSucc) (Fin.init x i.succ)
        + anti (x (Fin.last k).castSucc) (x (Fin.last (k + 1))) := by
    rw [Fin.sum_univ_castSucc]; simp only [Fin.init, Fin.succ_castSucc, Fin.succ_last]
  unfold pt; rw [h1, h2]; ring

lemma pt_zero (x : Fin 1 → Row) : pt 0 x = hor (x 0) := by simp [pt]

def mn (k : ℕ) (g : Fin (k + 1) → Row) : St := (g (Fin.last k), ⟨min (pt k g) 1, by omega⟩)

def cnt (k : ℕ) (p : St) : ℕ :=
  (Finset.univ.filter (fun x : Fin (k + 1) → Row => x (Fin.last k) = p.1 ∧ pt k x = p.2)).card

lemma cnt_zero (p : St) : cnt 0 p = w0 p := by
  unfold cnt w0
  split_ifs with h
  · rw [Finset.card_eq_one]
    refine ⟨fun _ => p.1, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, pt_zero]
    constructor
    · rintro ⟨h, -⟩; funext i; rw [show i = Fin.last 0 from Fin.ext (by omega)]; exact h
    · rintro rfl; exact ⟨rfl, h⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨h1, h2⟩
    apply h; rw [pt_zero] at h2; rw [← h1]; exact h2

set_option maxRecDepth 100000 in
lemma cnt_succ (k : ℕ) (q : St) :
    cnt (k + 1) q = ∑ p : St, if okc p q then cnt k p else 0 := by
  have e : cnt (k + 1) q = (Finset.univ.filter
      (fun g : Fin (k + 1) → Row => pt k g + hor q.1 + anti (g (Fin.last k)) q.1 = q.2)).card := by
    unfold cnt
    apply Finset.card_nbij' (fun f => Fin.init f) (fun g => Fin.snoc g q.1)
    · intro f hf
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hf ⊢
      obtain ⟨hl, hg⟩ := hf
      rw [pt_succ, hl] at hg
      simpa [Fin.init] using hg
    · intro g hg
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hg ⊢
      refine ⟨by simp, ?_⟩
      rw [pt_succ]
      simpa [Fin.init] using hg
    · intro f hf
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hf
      rw [← hf.1]; exact Fin.snoc_init_self f
    · intro g _; exact Fin.init_snoc _ _
  rw [e, Finset.card_eq_sum_card_fiberwise (f := mn k) (t := (Finset.univ : Finset St)) (fun g _ => Finset.mem_univ (mn k g))]
  apply Finset.sum_congr rfl
  rintro ⟨r, c0⟩ _
  rw [Finset.filter_filter]
  have hq := q.2.isLt
  have hc := c0.isLt
  split_ifs with h
  · unfold cnt; congr 1; apply Finset.filter_congr
    intro g _
    unfold okc at h
    simp only [mn, Prod.mk.injEq, Fin.ext_iff] at h ⊢
    constructor
    · rintro ⟨hc, rfl, h2⟩; refine ⟨rfl, ?_⟩; omega
    · rintro ⟨rfl, h2⟩; refine ⟨?_, rfl, ?_⟩ <;> omega
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro g _
    unfold okc at h
    simp only [mn, Prod.mk.injEq, Fin.ext_iff] at h ⊢
    rintro ⟨hc, rfl, h2⟩; apply h; omega

lemma cnt_eq (k : ℕ) (p : St) : cnt k p = w k p := by
  induction k generalizing p with
  | zero => rw [cnt_zero]; rfl
  | succ k ih =>
    rw [cnt_succ k p, w]
    apply Finset.sum_congr rfl
    intro r _
    rw [ih r]

set_option maxRecDepth 100000 in
lemma a_w (k : ℕ) : a (k + 1) = ∑ p : St, w k p := by
  simp only [a, pt_eq]
  rw [Finset.card_eq_sum_card_fiberwise (f := mn k) (t := (Finset.univ : Finset St)) (fun g _ => Finset.mem_univ (mn k g))]
  apply Finset.sum_congr rfl
  rintro ⟨r, c0⟩ _
  rw [← cnt_eq, cnt, Finset.filter_filter]
  have hc := c0.isLt
  congr 1; apply Finset.filter_congr
  intro x _
  simp only [mn, Prod.mk.injEq, Fin.ext_iff]
  constructor
  · rintro ⟨h1, rfl, h2⟩; exact ⟨rfl, by omega⟩
  · rintro ⟨rfl, h2⟩; exact ⟨by omega, rfl, by omega⟩

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

lemma a_u (j : ℕ) : a (j + 1) = ∑ r : St, w0 r * u j r := by
  have h := dual j 0
  rw [zero_add] at h
  rw [a_w, h]; rfl

def tb (L : List ℕ) (p : St) : ℕ :=
  L.getD (((p.1 0).val * 16 + (p.1 1).val * 4 + (p.1 2).val) * 2 + p.2.val) 0

def T1 : List ℕ := [46, 21, 46, 21, 46, 21, 51, 18, 46, 21, 46, 21, 51, 18, 46, 21, 46, 21, 51, 18, 46, 21, 46, 21, 51, 18, 46, 21, 46, 21, 46, 21, 46, 21, 46, 21, 46, 21, 51, 18, 46, 21, 46, 21, 51, 18, 46, 21, 46, 21, 51, 18, 46, 21, 46, 21, 51, 18, 46, 21, 46, 21, 46, 21, 46, 21, 46, 21, 46, 21, 51, 18, 46, 21, 46, 21, 51, 18, 46, 21, 46, 21, 51, 18, 46, 21, 46, 21, 51, 18, 46, 21, 46, 21, 46, 21, 46, 21, 46, 21, 46, 21, 51, 18, 46, 21, 46, 21, 51, 18, 46, 21, 46, 21, 51, 18, 46, 21, 46, 21, 51, 18, 46, 21, 46, 21, 46, 21]
def T2 : List ℕ := [1470, 441, 1470, 441, 1470, 441, 1503, 378, 1470, 441, 1470, 441, 1503, 378, 1470, 441, 1470, 441, 1503, 378, 1470, 441, 1470, 441, 1503, 378, 1470, 441, 1470, 441, 1470, 441, 1470, 441, 1470, 441, 1470, 441, 1503, 378, 1470, 441, 1470, 441, 1503, 378, 1470, 441, 1470, 441, 1503, 378, 1470, 441, 1470, 441, 1503, 378, 1470, 441, 1470, 441, 1470, 441, 1470, 441, 1470, 441, 1470, 441, 1503, 378, 1470, 441, 1470, 441, 1503, 378, 1470, 441, 1470, 441, 1503, 378, 1470, 441, 1470, 441, 1503, 378, 1470, 441, 1470, 441, 1470, 441, 1470, 441, 1470, 441, 1470, 441, 1503, 378, 1470, 441, 1470, 441, 1503, 378, 1470, 441, 1470, 441, 1503, 378, 1470, 441, 1470, 441, 1503, 378, 1470, 441, 1470, 441, 1470, 441]
def T3 : List ℕ := [41454, 9261, 41454, 9261, 41454, 9261, 40635, 7938, 41454, 9261, 41454, 9261, 40635, 7938, 41454, 9261, 41454, 9261, 40635, 7938, 41454, 9261, 41454, 9261, 40635, 7938, 41454, 9261, 41454, 9261, 41454, 9261, 41454, 9261, 41454, 9261, 41454, 9261, 40635, 7938, 41454, 9261, 41454, 9261, 40635, 7938, 41454, 9261, 41454, 9261, 40635, 7938, 41454, 9261, 41454, 9261, 40635, 7938, 41454, 9261, 41454, 9261, 41454, 9261, 41454, 9261, 41454, 9261, 41454, 9261, 40635, 7938, 41454, 9261, 41454, 9261, 40635, 7938, 41454, 9261, 41454, 9261, 40635, 7938, 41454, 9261, 41454, 9261, 40635, 7938, 41454, 9261, 41454, 9261, 41454, 9261, 41454, 9261, 41454, 9261, 41454, 9261, 40635, 7938, 41454, 9261, 41454, 9261, 40635, 7938, 41454, 9261, 41454, 9261, 40635, 7938, 41454, 9261, 41454, 9261, 40635, 7938, 41454, 9261, 41454, 9261, 41454, 9261]


set_option maxRecDepth 100000 in
lemma hu1 : ∀ x, u 1 x = tb T1 x := by decide +kernel

set_option maxRecDepth 100000 in
lemma hu2' : ∀ x, (∑ y : St, if okc x y then tb T1 y else 0) = tb T2 x := by decide +kernel

lemma hu2 (x : St) : u 2 x = tb T2 x := by
  show (∑ y : St, if okc x y then u 1 y else 0) = _
  simp only [hu1]; exact hu2' x

set_option maxRecDepth 100000 in
lemma hu3' : ∀ x, (∑ y : St, if okc x y then tb T2 y else 0) = tb T3 x := by decide +kernel

lemma hu3 (x : St) : u 3 x = tb T3 x := by
  show (∑ y : St, if okc x y then u 2 y else 0) = _
  simp only [hu2]; exact hu3' x

set_option maxRecDepth 100000 in
lemma hT : ∀ x : St, tb T3 x + 441 * tb T1 x = 42 * tb T2 x := by decide +kernel

lemma keyW (k : ℕ) :
    (∑ s : St, w (k + 3) s) + 441 * (∑ s : St, w (k + 1) s) = 42 * (∑ s : St, w (k + 2) s) := by
  rw [dual 3 k, dual 1 k, dual 2 k]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro x _
  have := hT x
  rw [hu1, hu2, hu3]
  calc w k x * tb T3 x + 441 * (w k x * tb T1 x) = w k x * (tb T3 x + 441 * tb T1 x) := by ring
    _ = w k x * (42 * tb T2 x) := by rw [this]
    _ = 42 * (w k x * tb T2 x) := by ring

lemma arec (k : ℕ) : (a (k + 4) : ℚ) = 42 * a (k + 3) - 441 * a (k + 2) := by
  have key := keyW k
  rw [← a_w (k + 3), ← a_w (k + 1), ← a_w (k + 2)] at key
  have key' : ((a (k + 3 + 1) + 441 * a (k + 1 + 1) : ℕ) : ℚ) = ((42 * a (k + 2 + 1) : ℕ) : ℚ) := by
    rw [key]
  push_cast at key'
  linarith

lemma v0 : a 0 = 0 := rfl
set_option maxRecDepth 100000 in
lemma v1 : a 1 = 60 := by rw [a_u 0]; decide +kernel
set_option maxRecDepth 100000 in
lemma v2 : a 2 = 2124 := by rw [a_u 1]; simp only [hu1]; decide +kernel
set_option maxRecDepth 100000 in
lemma v3 : a 3 = 62748 := by rw [a_u 2]; simp only [hu2]; decide +kernel

lemma arec' (n : ℕ) (hn : 3 ≤ n) : (a n : ℚ) = 42 * a (n - 1) - 441 * a (n - 2) := by
  rcases (show n = 3 ∨ 4 ≤ n by omega) with h | h
  · subst h; simp only [show 3 - 1 = 2 by rfl, show 3 - 2 = 1 by rfl, v1, v2, v3]; norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega]
    exact arec m

def g (n : ℕ) : ℚ := 4 * 3 ^ n * 7 ^ n * (24 * n + 11) / 49

lemma closed (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = g n := by
  have key : ∀ m : ℕ, (a (m + 1) : ℚ) = g (m + 1) ∧ (a (m + 2) : ℚ) = g (m + 2) := by
    intro m
    induction m with
    | zero => simp only [zero_add, g, v1, v2]; norm_num
    | succ m ih =>
      obtain ⟨h0, h1⟩ := ih
      refine ⟨h1, ?_⟩
      have := arec' (m + 3) (by omega)
      rw [show m + 1 + 2 = m + 3 by ring, this, show m + 3 - 1 = m + 2 by omega,
        show m + 3 - 2 = m + 1 by omega, h0, h1]
      simp only [g]; push_cast; ring
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (key m).1

lemma ps (f : ℕ → ℚ) (n k : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X ^ k) = if k ≤ n then f (n-k) else 0 := by
  rw [PowerSeries.coeff_mul_X_pow']; simp

lemma ps1 (f : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X) = if 1 ≤ n then f (n-1) else 0 := by
  rw [← ps, pow_one]

theorem main_proof :
    (∀ n : ℕ, 3 ≤ n →
      (a n : ℤ) = 42 * a (n - 1) - 441 * a (n - 2)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * (1 - 21 * X) ^ 2 =
      12 * X * (5 - 33 * X)) ∧
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 4 * 3 ^ n * 7 ^ ((n : ℤ) - 2) * (24 * n + 11)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    have h := arec' n hn
    exact_mod_cast h
  · rw [show ((1 - 21 * X) ^ 2 : PowerSeries ℚ) =
        1 - PowerSeries.C (42:ℚ) * X + PowerSeries.C (441:ℚ) * X ^ 2 by
          simp only [map_ofNat]; ring,
      show (12 * X * (5 - 33 * X) : PowerSeries ℚ) =
        PowerSeries.C (60:ℚ) * X - PowerSeries.C (396:ℚ) * X ^ 2 by
          simp only [map_ofNat]; ring]
    ext n
    simp only [mul_add, mul_sub, mul_one, map_add, map_sub, mul_left_comm _ (PowerSeries.C _),
      PowerSeries.coeff_C_mul, ps, ps1, PowerSeries.coeff_X, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow]
    rcases (show n ≤ 2 ∨ 3 ≤ n by omega) with h | h
    · interval_cases n <;> simp [v0, v1, v2] <;> norm_num
    · have hq := arec' n h
      simp [show 1 ≤ n by omega, show 2 ≤ n by omega, show n ≠ 1 by omega, show n ≠ 2 by omega]
      rw [hq]; ring
  · intro n hn
    rw [closed n hn, g, zpow_sub₀ (by norm_num), zpow_natCast]
    ring

end OMA.S_oeis_a269284

theorem OMA.solution : type_of% @OMA.S_oeis_a269284.main := OMA.S_oeis_a269284.main_proof
