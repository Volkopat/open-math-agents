import OMAStatements.S_oeis_a223962

-- Credit: @marcusbuffett (the owner of the agent is credited as the solver)
-- Sketch: the slices of the array along its long side (its columns) form a sequence of states with
-- conditions on single states, on adjacent pairs.
-- w k y counts valid sequences ending in y (bijection via Fin.init / Fin.snoc, adapted from the merged
-- proof of oeis-a223443 by @sntntHb); the dual vectors u j are tabulated and checked by decide +kernel,
-- together with the coordinatewise relation that gives the recurrence; the g.f. follows
-- coefficientwise from the recurrence and the first values.

namespace OMA.P_oeis_a223962

open Finset

section Gen
variable {σ : Type} [Fintype σ] [DecidableEq σ] (B : σ → Prop) [DecidablePred B]
  (T : σ → σ → Prop) [DecidableRel T]

def Gd (n : ℕ) (f : Fin n → σ) : Prop :=
  (∀ i, B (f i)) ∧ ∀ i j : Fin n, j.val = i.val + 1 → T (f i) (f j)

instance (n : ℕ) : DecidablePred (Gd B T n) := fun f => by unfold Gd; infer_instance

def w : ℕ → σ → ℕ
  | 0, y => if B y then 1 else 0
  | k + 1, y => ∑ x, if B y ∧ T x y then w k x else 0

def u : ℕ → σ → ℕ
  | 0, _ => 1
  | j + 1, x => ∑ y, if B y ∧ T x y then u j y else 0

def cnt (k : ℕ) (y : σ) : ℕ :=
  ((univ : Finset (Fin (k + 1) → σ)).filter (fun f => Gd B T (k + 1) f ∧ f (Fin.last k) = y)).card

lemma gd_succ (k : ℕ) (f : Fin (k + 2) → σ) :
    Gd B T (k + 2) f ↔ Gd B T (k + 1) (Fin.init f) ∧ B (f (Fin.last (k + 1))) ∧
      T (f (Fin.castSucc (Fin.last k))) (f (Fin.last (k + 1))) := by
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

lemma cnt_zero (y : σ) : cnt B T 0 y = if B y then 1 else 0 := by
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

lemma cnt_succ (k : ℕ) (y : σ) :
    cnt B T (k + 1) y = ∑ x, if B y ∧ T x y then cnt B T k x else 0 := by
  by_cases hy : B y
  · have e : cnt B T (k + 1) y = ((univ : Finset (Fin (k + 1) → σ)).filter
        (fun g => Gd B T (k + 1) g ∧ T (g (Fin.last k)) y)).card := by
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
      (f := fun g : Fin (k + 1) → σ => g (Fin.last k))
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
  · have : cnt B T (k + 1) y = 0 := by
      unfold cnt
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro f - ⟨⟨h0, -⟩, h⟩; exact hy (h ▸ h0 _)
    rw [this]; symm
    apply Finset.sum_eq_zero; intro x _
    rw [if_neg (fun h => hy h.1)]

lemma cnt_eq (k : ℕ) (y : σ) : cnt B T k y = w B T k y := by
  induction k generalizing y with
  | zero => rw [cnt_zero]; rfl
  | succ k ih => rw [cnt_succ]; simp only [w, ih]

lemma total (k : ℕ) :
    ((univ : Finset (Fin (k + 1) → σ)).filter (Gd B T (k + 1))).card = ∑ y, w B T k y := by
  simp only [← cnt_eq]
  unfold cnt
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun g : Fin (k + 1) → σ => g (Fin.last k))
    (t := univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.filter_filter]

lemma w_zero_of (k : ℕ) (x : σ) (hx : ¬ B x) : w B T k x = 0 := by
  cases k with
  | zero => simp [w, hx]
  | succ k =>
    simp only [w]
    apply Finset.sum_eq_zero; intro y _
    rw [if_neg (fun h => hx h.1)]

lemma dual (j k : ℕ) : ∑ y, w B T (k + j) y = ∑ x, w B T k x * u B T j x := by
  induction j generalizing k with
  | zero => simp [u]
  | succ j ih =>
    rw [show k + (j + 1) = (k + 1) + j by ring, ih (k + 1)]
    simp only [w, u, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _
    split_ifs <;> simp

/-- The count of valid sequences of length k + 1 + j through the dual vectors. -/
lemma total_dual (k j : ℕ) :
    ((univ : Finset (Fin (k + j + 1) → σ)).filter (Gd B T (k + j + 1))).card =
      ∑ x, w B T k x * u B T j x := by
  rw [total, dual]

end Gen


end OMA.P_oeis_a223962

namespace OMA.P_oeis_a223962

open Finset OMA.S_oeis_a223962

abbrev St := Fin 2 → Fin 4

def B (s : St) : Prop := True

def T (s t : St) : Prop := (∀ i : Fin 2, s i ≤ t i) ∧ (∀ i i' : Fin 2, i'.val = i.val + 1 → s i ≤ t i')

instance : DecidablePred B := fun s => by unfold B; infer_instance
instance : DecidableRel T := fun s t => by unfold T; infer_instance

lemma c1_iff (x : Fin 2 → Fin n → Fin 4) : AntidiagsUnimodal x ↔ True :=
  ⟨fun _ => trivial, fun _ i₁ i₂ i₃ j₁ j₂ j₃ h12 h23 _ _ => by
    have a1 := Fin.lt_def.mp h12; have a2 := Fin.lt_def.mp h23; have := i₃.isLt; omega⟩

lemma c2_iff (x : Fin 2 → Fin n → Fin 4) : RowsNondecreasing x ↔
    ∀ j j' : Fin n, j'.val = j.val + 1 → ∀ i : Fin 2, x i j ≤ x i j' :=
  ⟨fun h j j' hj i => h i j j' hj, fun h i j j' hj => h j j' hj i⟩

lemma c3_iff (x : Fin 2 → Fin n → Fin 4) : DiagsNondecreasing x ↔
    ∀ j j' : Fin n, j'.val = j.val + 1 → ∀ i i' : Fin 2, i'.val = i.val + 1 → x i j ≤ x i' j' :=
  ⟨fun h j j' hj i i' hi => h i i' j j' hi hj, fun h i i' j j' hi hj => h j j' hj i i' hi⟩

lemma good_iff {n : ℕ} (x : Fin 2 → Fin n → Fin 4) :
    good x ↔ Gd B T n (fun j i => x i j) := by
  unfold good
  rw [c1_iff x, c2_iff x, c3_iff x]
  simp only [Gd, B, T, forall_and, imp_and, implies_true, and_true, true_and]
  all_goals tauto

lemma a_eq (n : ℕ) : a n = ((univ : Finset (Fin n → St)).filter (Gd B T n)).card := by
  unfold a
  apply Finset.card_nbij' (fun x => fun j i => x i j) (fun f => fun i j => f j i)
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
    exact (good_iff x).1 hx
  · intro f hf
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf ⊢
    exact (good_iff _).2 hf
  · intro x _; rfl
  · intro f _; rfl

lemma aw (k j : ℕ) : a (k + j + 1) = ∑ x, w B T k x * u B T j x := by
  rw [a_eq]; exact total_dual B T k j

def idx (s : St) : ℕ := (s 0).val + 4 * (s 1).val

def tb (L : List ℕ) (s : St) : ℕ := L.getD (idx s) 0

def T1 : List ℕ := [16, 9, 4, 1, 12, 9, 4, 1, 8, 6, 4, 1, 4, 3, 2, 1]
def T2 : List ℕ := [85, 31, 8, 1, 55, 31, 8, 1, 29, 17, 8, 1, 10, 6, 3, 1]
def T3 : List ℕ := [295, 76, 13, 1, 170, 76, 13, 1, 75, 36, 13, 1, 20, 10, 4, 1]
def T4 : List ℕ := [805, 155, 19, 1, 420, 155, 19, 1, 160, 65, 19, 1, 35, 15, 5, 1]
def T5 : List ℕ := [1876, 281, 26, 1, 896, 281, 26, 1, 301, 106, 26, 1, 56, 21, 6, 1]
def T6 : List ℕ := [3906, 469, 34, 1, 1722, 469, 34, 1, 518, 161, 34, 1, 84, 28, 7, 1]
def T7 : List ℕ := [7470, 736, 43, 1, 3060, 736, 43, 1, 834, 232, 43, 1, 120, 36, 8, 1]

set_option maxRecDepth 100000 in
lemma hu1 : ∀ x, u B T 1 x = tb T1 x := by decide +kernel

set_option maxRecDepth 100000 in
lemma hs2 : ∀ x, (∑ y, if B y ∧ T x y then tb T1 y else 0) = tb T2 x := by
  decide +kernel

lemma hu2 (x : St) : u B T 2 x = tb T2 x := by
  show (∑ y, if B y ∧ T x y then u B T 1 y else 0) = _
  simp only [hu1]; exact hs2 x

set_option maxRecDepth 100000 in
lemma hs3 : ∀ x, (∑ y, if B y ∧ T x y then tb T2 y else 0) = tb T3 x := by
  decide +kernel

lemma hu3 (x : St) : u B T 3 x = tb T3 x := by
  show (∑ y, if B y ∧ T x y then u B T 2 y else 0) = _
  simp only [hu2]; exact hs3 x

set_option maxRecDepth 100000 in
lemma hs4 : ∀ x, (∑ y, if B y ∧ T x y then tb T3 y else 0) = tb T4 x := by
  decide +kernel

lemma hu4 (x : St) : u B T 4 x = tb T4 x := by
  show (∑ y, if B y ∧ T x y then u B T 3 y else 0) = _
  simp only [hu3]; exact hs4 x

set_option maxRecDepth 100000 in
lemma hs5 : ∀ x, (∑ y, if B y ∧ T x y then tb T4 y else 0) = tb T5 x := by
  decide +kernel

lemma hu5 (x : St) : u B T 5 x = tb T5 x := by
  show (∑ y, if B y ∧ T x y then u B T 4 y else 0) = _
  simp only [hu4]; exact hs5 x

set_option maxRecDepth 100000 in
lemma hs6 : ∀ x, (∑ y, if B y ∧ T x y then tb T5 y else 0) = tb T6 x := by
  decide +kernel

lemma hu6 (x : St) : u B T 6 x = tb T6 x := by
  show (∑ y, if B y ∧ T x y then u B T 5 y else 0) = _
  simp only [hu5]; exact hs6 x

set_option maxRecDepth 100000 in
lemma hs7 : ∀ x, (∑ y, if B y ∧ T x y then tb T6 y else 0) = tb T7 x := by
  decide +kernel

lemma hu7 (x : St) : u B T 7 x = tb T7 x := by
  show (∑ y, if B y ∧ T x y then u B T 6 y else 0) = _
  simp only [hu6]; exact hs7 x

set_option maxRecDepth 100000 in
lemma hrel : ∀ x, B x → tb T7 x + 21 * tb T5 x + 35 * tb T3 x + 7 * tb T1 x = 7 * tb T6 x + 35 * tb T4 x + 21 * tb T2 x + 1 := by
  decide +kernel

lemma arec (k : ℕ) : (a (k + 8) : ℤ) = 7 * a (k + 7) - 21 * a (k + 6) + 35 * a (k + 5) - 35 * a (k + 4) + 21 * a (k + 3) - 7 * a (k + 2) + a (k + 1) := by
  have e7 : a (k + 8) = ∑ x, w B T k x * u B T 7 x := aw k 7
  have e6 : a (k + 7) = ∑ x, w B T k x * u B T 6 x := aw k 6
  have e5 : a (k + 6) = ∑ x, w B T k x * u B T 5 x := aw k 5
  have e4 : a (k + 5) = ∑ x, w B T k x * u B T 4 x := aw k 4
  have e3 : a (k + 4) = ∑ x, w B T k x * u B T 3 x := aw k 3
  have e2 : a (k + 3) = ∑ x, w B T k x * u B T 2 x := aw k 2
  have e1 : a (k + 2) = ∑ x, w B T k x * u B T 1 x := aw k 1
  have e0 : a (k + 1) = ∑ x, w B T k x * u B T 0 x := aw k 0
  have key : ∑ x, w B T k x * u B T 7 x + 21 * ∑ x, w B T k x * u B T 5 x + 35 * ∑ x, w B T k x * u B T 3 x + 7 * ∑ x, w B T k x * u B T 1 x = 7 * ∑ x, w B T k x * u B T 6 x + 35 * ∑ x, w B T k x * u B T 4 x + 21 * ∑ x, w B T k x * u B T 2 x + ∑ x, w B T k x * u B T 0 x := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro x _
    by_cases hx : B x
    · have h := hrel x hx
      rw [hu7, hu6, hu5, hu4, hu3, hu2, hu1]
      try simp only [u]
      calc (w B T k x * tb T7 x) + 21 * (w B T k x * tb T5 x) + 35 * (w B T k x * tb T3 x) + 7 * (w B T k x * tb T1 x)
          = w B T k x * (tb T7 x + 21 * tb T5 x + 35 * tb T3 x + 7 * tb T1 x) := by ring
        _ = w B T k x * (7 * tb T6 x + 35 * tb T4 x + 21 * tb T2 x + 1) := by rw [h]
        _ = _ := by ring
    · simp [w_zero_of B T k x hx]
  rw [e7, e6, e5, e4, e3, e2, e1, e0]
  have := congrArg (fun t : ℕ => (t : ℤ)) key
  push_cast at this ⊢
  linarith

lemma val (j : ℕ) : a (j + 1) = ∑ x, (if B x then 1 else 0) * u B T j x := by
  rw [show j + 1 = 0 + j + 1 by ring, aw]; rfl

set_option maxRecDepth 100000 in
lemma v1 : a 1 = 16 := by
  rw [val 0]; simp only [u]; decide +kernel

set_option maxRecDepth 100000 in
lemma v2 : a 2 = 85 := by
  rw [val 1]; simp only [hu1]; decide +kernel

set_option maxRecDepth 100000 in
lemma v3 : a 3 = 295 := by
  rw [val 2]; simp only [hu2]; decide +kernel

set_option maxRecDepth 100000 in
lemma v4 : a 4 = 805 := by
  rw [val 3]; simp only [hu3]; decide +kernel

set_option maxRecDepth 100000 in
lemma v5 : a 5 = 1876 := by
  rw [val 4]; simp only [hu4]; decide +kernel

set_option maxRecDepth 100000 in
lemma v6 : a 6 = 3906 := by
  rw [val 5]; simp only [hu5]; decide +kernel

set_option maxRecDepth 100000 in
lemma v7 : a 7 = 7470 := by
  rw [val 6]; simp only [hu6]; decide +kernel

lemma recur (n : ℕ) (hn : 7 < n) : (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
  rw [show k + 8 - 1 = k + 7 by omega, show k + 8 - 2 = k + 6 by omega, show k + 8 - 3 = k + 5 by omega, show k + 8 - 4 = k + 4 by omega, show k + 8 - 5 = k + 3 by omega, show k + 8 - 6 = k + 2 by omega, show k + 8 - 7 = k + 1 by omega]
  exact arec k

lemma ps (f : ℕ → ℚ) (n k : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X ^ k) = if k ≤ n then f (n - k) else 0 := by
  rw [PowerSeries.coeff_mul_X_pow']; simp

lemma ps1 (f : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X) = if 1 ≤ n then f (n - 1) else 0 := by
  rw [← ps, pow_one]

end OMA.P_oeis_a223962

open PowerSeries Finset in
open OMA.S_oeis_a223962 OMA.P_oeis_a223962 in
theorem OMA.solution : type_of% @OMA.S_oeis_a223962.main := by
  refine ⟨?_, recur⟩
  rw [show ((1 - X) ^ 7 : PowerSeries ℚ) =
      1 - PowerSeries.C (7:ℚ) * X + PowerSeries.C (21:ℚ) * X ^ 2 - PowerSeries.C (35:ℚ) * X ^ 3 + PowerSeries.C (35:ℚ) * X ^ 4 - PowerSeries.C (21:ℚ) * X ^ 5 + PowerSeries.C (7:ℚ) * X ^ 6 - X ^ 7 by
        simp only [map_ofNat]; ring,
    show (X * (16 - 27 * X + 36 * X ^ 2 - 35 * X ^ 3 + 21 * X ^ 4 - 7 * X ^ 5 + X ^ 6) : PowerSeries ℚ) =
      PowerSeries.C (16:ℚ) * X - PowerSeries.C (27:ℚ) * X ^ 2 + PowerSeries.C (36:ℚ) * X ^ 3 - PowerSeries.C (35:ℚ) * X ^ 4 + PowerSeries.C (21:ℚ) * X ^ 5 - PowerSeries.C (7:ℚ) * X ^ 6 + X ^ 7 by
        simp only [map_ofNat]; ring]
  ext n
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, map_neg, mul_neg, mul_left_comm _ (PowerSeries.C _),
    PowerSeries.coeff_C_mul, ps, ps1, PowerSeries.coeff_X, PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
  rcases (show n ≤ 7 ∨ 8 ≤ n by omega) with h | h
  · interval_cases n <;> simp [v1, v2, v3, v4, v5, v6, v7] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    have hq : (a (m + 8) : ℚ) = 7 * a (m + 7) - 21 * a (m + 6) + 35 * a (m + 5) - 35 * a (m + 4) + 21 * a (m + 3) - 7 * a (m + 2) + a (m + 1) := by
      have := recur (m + 8) (by omega)
      rw [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega, show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega, show m + 8 - 5 = m + 3 by omega, show m + 8 - 6 = m + 2 by omega, show m + 8 - 7 = m + 1 by omega] at this
      exact_mod_cast this
    simp [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega, show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega, show m + 8 - 5 = m + 3 by omega, show m + 8 - 6 = m + 2 by omega, show m + 8 - 7 = m + 1 by omega,
      show m + 8 ≠ 1 by omega, show m + 8 ≠ 2 by omega, show m + 8 ≠ 3 by omega, show m + 8 ≠ 4 by omega, show m + 8 ≠ 5 by omega, show m + 8 ≠ 6 by omega, show m + 8 ≠ 7 by omega]
    rw [hq]; ring
