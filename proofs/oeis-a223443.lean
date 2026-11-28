import OMAStatements.S_oeis_a223443

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: transfer matrix on the 28 states (adjacent label pairs). w k y counts valid arrays ending
-- in row y (bijection via Fin.init/Fin.snoc); with the dual counts u j, u3 + 8 u1 = 6 u2 on states
-- (checked by decide +kernel from tabulated values computed by computer), so a(k+4) = 6a(k+3) - 8a(k+2);
-- closed form by induction from a2 = 104, a3 = 408, g.f. by coefficients.

namespace OMA.S_oeis_a223443

open PowerSeries Finset

def Gd (n : ℕ) (f : Fin n → Fin 15 × Fin 15) : Prop :=
  (∀ i, hrow (f i)) ∧ ∀ i j : Fin n, j.val = i.val + 1 → ok (f i) (f j)

instance (n : ℕ) : DecidablePred (Gd n) := fun f => by unfold Gd; infer_instance

def w : ℕ → Fin 15 × Fin 15 → ℕ
  | 0, y => if hrow y then 1 else 0
  | k + 1, y => ∑ x, if hrow y ∧ ok x y then w k x else 0

def u : ℕ → Fin 15 × Fin 15 → ℕ
  | 0, _ => 1
  | j + 1, x => ∑ y, if hrow y ∧ ok x y then u j y else 0

def cnt (k : ℕ) (y : Fin 15 × Fin 15) : ℕ :=
  ((univ : Finset (Fin (k + 1) → Fin 15 × Fin 15)).filter
    (fun f => Gd (k + 1) f ∧ f (Fin.last k) = y)).card

lemma gd_succ (k : ℕ) (f : Fin (k + 2) → Fin 15 × Fin 15) :
    Gd (k + 2) f ↔ Gd (k + 1) (Fin.init f) ∧ hrow (f (Fin.last (k + 1))) ∧
      ok (f (Fin.castSucc (Fin.last k))) (f (Fin.last (k + 1))) := by
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨⟨fun i => h0 _, fun i j hij => h _ _ (by simp [hij])⟩, h0 _, h _ _ (by simp)⟩
  · rintro ⟨⟨h0, h1⟩, h2, h3⟩
    refine ⟨fun i => ?_, fun i j hij => ?_⟩
    · by_cases hi : i.val < k + 1
      · have := h0 ⟨i.val, hi⟩
        simpa [Fin.init] using this
      · have hi' : i = Fin.last (k + 1) := Fin.ext (by simp; omega)
        subst hi'; exact h2
    · by_cases hj : j.val < k + 1
      · have := h1 ⟨i.val, by omega⟩ ⟨j.val, hj⟩ hij
        simpa [Fin.init] using this
      · have hj' : j = Fin.last (k + 1) := Fin.ext (by simp; omega)
        have hi' : i = Fin.castSucc (Fin.last k) := Fin.ext (by simp; omega)
        subst hj' hi'; exact h3

lemma cnt_zero (y : Fin 15 × Fin 15) : cnt 0 y = if hrow y then 1 else 0 := by
  unfold cnt
  split_ifs with hy
  · rw [Finset.card_eq_one]
    refine ⟨fun _ => y, ?_⟩
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h⟩; funext i; rw [show i = Fin.last 0 from Fin.ext (by omega)]; exact h
    · rintro rfl; exact ⟨⟨fun _ => hy, fun i j hij => by omega⟩, rfl⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro f - ⟨⟨h0, -⟩, h⟩; exact hy (h ▸ h0 _)

lemma cnt_succ (k : ℕ) (y : Fin 15 × Fin 15) :
    cnt (k + 1) y = ∑ x, if hrow y ∧ ok x y then cnt k x else 0 := by
  by_cases hy : hrow y
  · have e : cnt (k + 1) y = ((univ : Finset (Fin (k + 1) → Fin 15 × Fin 15)).filter
        (fun g => Gd (k + 1) g ∧ ok (g (Fin.last k)) y)).card := by
      unfold cnt
      apply Finset.card_nbij' (fun f => Fin.init f) (fun g => Fin.snoc g y)
      · intro f hf
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf ⊢
        obtain ⟨hg, hl⟩ := hf
        rw [gd_succ] at hg
        refine ⟨hg.1, ?_⟩
        have := hg.2.2; rw [hl] at this; simpa [Fin.init] using this
      · intro g hg
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hg ⊢
        refine ⟨?_, by simp⟩
        rw [gd_succ]
        refine ⟨by simpa using hg.1, by simpa using hy, ?_⟩
        simpa using hg.2
      · intro f hf
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf
        rw [← hf.2]; exact Fin.snoc_init_self f
      · intro g _; exact Fin.init_snoc _ _
    rw [e, Finset.card_eq_sum_card_fiberwise
      (f := fun g : Fin (k + 1) → Fin 15 × Fin 15 => g (Fin.last k))
      (t := univ) (fun _ _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.filter_filter]
    split_ifs with h
    · unfold cnt; congr 1; apply Finset.filter_congr
      intro g _
      constructor
      · rintro ⟨⟨hg, -⟩, hx⟩; exact ⟨hg, hx⟩
      · rintro ⟨hg, hx⟩; exact ⟨⟨hg, hx ▸ h.2⟩, hx⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro g - ⟨⟨-, ha⟩, hx⟩; exact h ⟨hy, hx ▸ ha⟩
  · have : cnt (k + 1) y = 0 := by
      unfold cnt
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro f - ⟨⟨h0, -⟩, h⟩; exact hy (h ▸ h0 _)
    rw [this]; symm
    apply Finset.sum_eq_zero; intro x _
    rw [if_neg (fun h => hy h.1)]

lemma cnt_eq (k : ℕ) (y : Fin 15 × Fin 15) : cnt k y = w k y := by
  induction k generalizing y with
  | zero => rw [cnt_zero]; rfl
  | succ k ih => rw [cnt_succ]; simp only [w, ih]

lemma a_succ (k : ℕ) : a (k + 1) = ∑ y, w k y := by
  simp only [← cnt_eq]
  unfold cnt a
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun g : Fin (k + 1) → Fin 15 × Fin 15 => g (Fin.last k))
    (t := univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.filter_filter]; rfl

lemma w_zero_of (k : ℕ) (x : Fin 15 × Fin 15) (hx : ¬ hrow x) : w k x = 0 := by
  cases k with
  | zero => simp [w, hx]
  | succ k =>
    simp only [w]
    apply Finset.sum_eq_zero; intro y _
    rw [if_neg (fun h => hx h.1)]

lemma dual (j k : ℕ) : ∑ y, w (k + j) y = ∑ x, w k x * u j x := by
  induction j generalizing k with
  | zero => simp [u]
  | succ j ih =>
    rw [show k + (j + 1) = (k + 1) + j by ring, ih (k + 1)]
    simp only [w, u, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _
    split_ifs <;> simp

def tb (L : List ℕ) (x : Fin 15 × Fin 15) : ℕ := L.getD (x.1.val * 15 + x.2.val) 0

def T1 : List ℕ := [0, 4, 4, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 4, 0, 0, 5, 5, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 4, 0, 0, 1, 1, 0, 0, 0, 0, 5, 5, 0, 0, 0, 0, 0, 5, 1, 0, 0, 3, 3, 1, 1, 0, 0, 0, 0, 0, 0, 0, 5, 1, 0, 0, 1, 1, 3, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 5, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 1, 1, 0, 1, 5, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 3, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0]
def T2 : List ℕ := [0, 18, 18, 0, 0, 5, 5, 5, 5, 0, 0, 5, 5, 5, 5, 18, 0, 0, 20, 20, 0, 0, 0, 0, 4, 4, 0, 0, 0, 0, 18, 0, 0, 4, 4, 0, 0, 0, 0, 20, 20, 0, 0, 0, 0, 0, 20, 4, 0, 0, 11, 11, 5, 5, 0, 0, 0, 0, 0, 0, 0, 20, 4, 0, 0, 5, 5, 11, 11, 0, 0, 0, 0, 0, 0, 5, 0, 0, 11, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 11, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 5, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 5, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 20, 0, 0, 0, 0, 0, 0, 0, 0, 11, 11, 5, 5, 0, 4, 20, 0, 0, 0, 0, 0, 0, 0, 0, 5, 5, 11, 11, 5, 0, 0, 0, 0, 0, 0, 0, 0, 11, 5, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 11, 5, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 5, 11, 0, 0, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 5, 11, 0, 0, 0, 0]
def T3 : List ℕ := [0, 76, 76, 0, 0, 20, 20, 20, 20, 0, 0, 20, 20, 20, 20, 76, 0, 0, 80, 80, 0, 0, 0, 0, 18, 18, 0, 0, 0, 0, 76, 0, 0, 18, 18, 0, 0, 0, 0, 80, 80, 0, 0, 0, 0, 0, 80, 18, 0, 0, 42, 42, 20, 20, 0, 0, 0, 0, 0, 0, 0, 80, 18, 0, 0, 20, 20, 42, 42, 0, 0, 0, 0, 0, 0, 20, 0, 0, 42, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 42, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 20, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 20, 0, 0, 20, 42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 80, 0, 0, 0, 0, 0, 0, 0, 0, 42, 42, 20, 20, 0, 18, 80, 0, 0, 0, 0, 0, 0, 0, 0, 20, 20, 42, 42, 20, 0, 0, 0, 0, 0, 0, 0, 0, 42, 20, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 42, 20, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 20, 42, 0, 0, 0, 0, 20, 0, 0, 0, 0, 0, 0, 0, 0, 20, 42, 0, 0, 0, 0]

set_option maxRecDepth 100000 in
lemma hu1 : ∀ x, u 1 x = tb T1 x := by decide +kernel

set_option maxRecDepth 100000 in
lemma hu2' : ∀ x, (∑ y, if hrow y ∧ ok x y then tb T1 y else 0) = tb T2 x := by decide +kernel

set_option maxRecDepth 100000 in
lemma hu3' : ∀ x, (∑ y, if hrow y ∧ ok x y then tb T2 y else 0) = tb T3 x := by decide +kernel

lemma hu2 (x : Fin 15 × Fin 15) : u 2 x = tb T2 x := by
  show (∑ y, if hrow y ∧ ok x y then u 1 y else 0) = _
  simp only [hu1]; exact hu2' x

lemma hu3 (x : Fin 15 × Fin 15) : u 3 x = tb T3 x := by
  show (∑ y, if hrow y ∧ ok x y then u 2 y else 0) = _
  simp only [hu2]; exact hu3' x

set_option maxRecDepth 100000 in
lemma hT : ∀ x, hrow x → tb T3 x + 8 * tb T1 x = 6 * tb T2 x := by decide +kernel

lemma arec (k : ℕ) : (a (k + 4) : ℤ) = 6 * a (k + 3) - 8 * a (k + 2) := by
  rw [a_succ, a_succ, a_succ]
  have d3 := dual 3 k
  have d2 := dual 2 k
  have d1 := dual 1 k
  have key : ∑ x, w k x * u 3 x + 8 * ∑ x, w k x * u 1 x = 6 * ∑ x, w k x * u 2 x := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro x _
    by_cases hx : hrow x
    · have := hT x hx
      rw [hu1, hu2, hu3]
      calc w k x * tb T3 x + 8 * (w k x * tb T1 x)
          = w k x * (tb T3 x + 8 * tb T1 x) := by ring
        _ = w k x * (6 * tb T2 x) := by rw [this]
        _ = 6 * (w k x * tb T2 x) := by ring
    · simp [w_zero_of k x hx]
  rw [show k + 3 = k + 3 by rfl] at d3
  rw [d3, d2, d1]
  zify at key
  push_cast
  linarith

lemma v1 : a 1 = 28 := by rw [a_succ]; decide +kernel
lemma v2 : a 2 = 104 := by
  rw [a_succ, show (1:ℕ) = 0 + 1 by rfl, dual 1 0]
  simp only [hu1]; decide +kernel
lemma v3 : a 3 = 408 := by
  rw [a_succ, show (2:ℕ) = 0 + 2 by rfl, dual 2 0]
  simp only [hu2]; decide +kernel

lemma ps (f : ℕ → ℚ) (n k : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X ^ k) = if k ≤ n then f (n-k) else 0 := by
  rw [PowerSeries.coeff_mul_X_pow']; simp

lemma ps1 (f : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X) = if 1 ≤ n then f (n-1) else 0 := by
  rw [← ps, pow_one]

end OMA.S_oeis_a223443

open PowerSeries Finset in
open OMA.S_oeis_a223443 in
theorem OMA.solution : type_of% @OMA.S_oeis_a223443.main := by
  refine ⟨?_, ?_⟩
  · rw [show ((1 - 2 * X) * (1 - 4 * X) : PowerSeries ℚ) =
        1 - PowerSeries.C (6:ℚ) * X + PowerSeries.C (8:ℚ) * X ^ 2 by
          simp only [map_ofNat]; ring,
      show (4 * X * (7 - 16 * X + 2 * X ^ 2) : PowerSeries ℚ) =
        PowerSeries.C (28:ℚ) * X - PowerSeries.C (64:ℚ) * X ^ 2 + PowerSeries.C (8:ℚ) * X ^ 3 by
          simp only [map_ofNat]; ring]
    ext n
    simp only [mul_add, mul_sub, mul_one, map_add, map_sub, mul_left_comm _ (PowerSeries.C _),
      PowerSeries.coeff_C_mul, ps, ps1, PowerSeries.coeff_X, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
    rcases (show n ≤ 3 ∨ 4 ≤ n by omega) with h | h
    · interval_cases n <;> simp [v1, v2, v3] <;> norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
      have hq : (a (m + 4) : ℚ) = 6 * a (m + 3) - 8 * a (m + 2) := by
        exact_mod_cast arec m
      simp [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
        show m + 4 ≠ 1 by omega, show m + 4 ≠ 2 by omega, show m + 4 ≠ 3 by omega]
      rw [hq]; ring
  · have key : ∀ m : ℕ, ∀ k ≤ m, (a (k + 2) : ℤ) = 2 ^ k * (4 + 25 * 2 ^ (k + 2)) := by
      intro m
      induction m with
      | zero =>
        intro k hk; obtain rfl : k = 0 := by omega
        rw [v2]; norm_num
      | succ m ih =>
        intro k hk
        rcases (show k ≤ m ∨ k = m + 1 by omega) with hk | rfl
        · exact ih k hk
        · rcases (show m = 0 ∨ 1 ≤ m by omega) with rfl | hm
          · rw [v3]; norm_num
          · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
            have hq := arec j
            have i1 := ih (j + 1) le_rfl
            have i2 := ih j (by omega)
            rw [show j + 1 + 2 = j + 3 by omega] at i1
            rw [show j + 1 + 1 + 2 = j + 4 by omega, hq, i1, i2]
            ring
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have := key k k le_rfl
    rw [show k + 2 - 2 = k by omega]
    exact_mod_cast this
