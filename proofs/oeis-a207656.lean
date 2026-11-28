import OMAStatements.S_oeis_a207656
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Transfer-matrix proof. The array is read as a sequence of 3-bit rows (encoded as Bool x Bool x Bool).
-- A generic lemma counts sequences whose elements satisfy P and whose consecutive triples satisfy
-- Q by a dynamic program G on the last two elements (bijection by removing the last element,
-- Fin.init / Fin.snoc). With dual vectors U j (U 0 = 1, U (j+1) = transposed step) one has
-- S (m + j) = sum of U j * G m, and the linear relation between the U j needed for the
-- recurrence holds on all pairs of admissible elements (checked by decide on 64 pairs).
-- Small terms are evaluated by decide; the conjectured formulas follow from the recurrence.

namespace OMA.P_oeis_a207656

open OMA.S_oeis_a207656

namespace ArrDP

variable {R : Type} [Fintype R] [DecidableEq R] (P : R → Prop) [DecidablePred P]
  (Q : R → R → R → Prop) [∀ a b c, Decidable (Q a b c)]

/-- Arrays (sequences of rows) whose rows satisfy `P` and whose consecutive row triples satisfy `Q`. -/
def Good (n : ℕ) (A : Fin n → R) : Prop :=
  (∀ i, P (A i)) ∧ ∀ i (h : i + 2 < n), Q (A ⟨i, by omega⟩) (A ⟨i + 1, by omega⟩) (A ⟨i + 2, h⟩)

noncomputable instance (n : ℕ) : DecidablePred (Good P Q n) := Classical.decPred _

noncomputable def cnt (m : ℕ) (r s : R) : ℕ :=
  (Finset.univ.filter (fun B : Fin (m + 2) → R =>
    Good P Q (m + 2) B ∧ B ⟨m, by omega⟩ = r ∧ B ⟨m + 1, by omega⟩ = s)).card

def G : ℕ → R → R → ℕ
  | 0, r, s => if P r ∧ P s then 1 else 0
  | m + 1, s, t => ∑ r, if P t ∧ Q r s t then G m r s else 0

lemma snoc_lt {k : ℕ} (B : Fin k → R) (t : R) (i : ℕ) (h : i < k + 1) (hi : i < k) :
    (Fin.snoc B t : Fin (k + 1) → R) ⟨i, h⟩ = B ⟨i, hi⟩ := by
  show (Fin.snoc B t : Fin (k + 1) → R) (Fin.castSucc ⟨i, hi⟩) = _
  exact Fin.snoc_castSucc ..

lemma snoc_eq {k : ℕ} (B : Fin k → R) (t : R) (h : k < k + 1) :
    (Fin.snoc B t : Fin (k + 1) → R) ⟨k, h⟩ = t := by
  show (Fin.snoc B t : Fin (k + 1) → R) (Fin.last k) = t
  exact Fin.snoc_last ..

lemma good_succ (m : ℕ) (A : Fin (m + 2 + 1) → R) :
    Good P Q (m + 2 + 1) A ↔ Good P Q (m + 2) (Fin.init A) ∧ P (A ⟨m + 2, by omega⟩) ∧
      Q (A ⟨m, by omega⟩) (A ⟨m + 1, by omega⟩) (A ⟨m + 2, by omega⟩) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun i => h1 _, fun i h => h2 i (by omega)⟩, h1 _, h2 m (by omega)⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨fun i => ?_, fun i h => ?_⟩
    · rcases i with ⟨i, hi⟩
      by_cases hlt : i < m + 2
      · exact h1 ⟨i, hlt⟩
      · obtain rfl : i = m + 2 := by omega
        exact h3
    · by_cases hlt : i + 2 < m + 2
      · exact h2 i hlt
      · obtain rfl : i = m := by omega
        exact h4

lemma cnt_zero (r s : R) : cnt P Q 0 r s = G P Q 0 r s := by
  unfold cnt G
  by_cases h : P r ∧ P s
  · rw [if_pos h, Finset.card_eq_one]
    refine ⟨![r, s], ?_⟩
    ext B
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h0, h1⟩
      funext i; fin_cases i
      · exact h0
      · exact h1
    · rintro rfl
      refine ⟨⟨fun i => ?_, fun i hi => by omega⟩, rfl, rfl⟩
      fin_cases i
      · exact h.1
      · exact h.2
  · rw [if_neg h, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro B - ⟨⟨hP, -⟩, h0, h1⟩
    exact h ⟨h0 ▸ hP _, h1 ▸ hP _⟩

lemma cnt_succ (m : ℕ) (s t : R) :
    cnt P Q (m + 1) s t = ∑ r, if P t ∧ Q r s t then cnt P Q m r s else 0 := by
  classical
  -- remove the last row
  have e : cnt P Q (m + 1) s t = (Finset.univ.filter (fun B : Fin (m + 2) → R =>
      Good P Q (m + 2) B ∧ B ⟨m + 1, by omega⟩ = s ∧ P t ∧ Q (B ⟨m, by omega⟩) s t)).card := by
    unfold cnt
    apply Finset.card_nbij' (fun A => Fin.init A) (fun B => Fin.snoc B t)
    · intro A hA
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hA ⊢
      obtain ⟨hg, h1, h2⟩ := hA
      rw [good_succ] at hg
      obtain ⟨hg, hp, hq⟩ := hg
      refine ⟨hg, h1, h2 ▸ hp, ?_⟩
      have := hq; rw [h1, h2] at this; exact this
    · intro B hB
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hB ⊢
      obtain ⟨hg, h1, hp, hq⟩ := hB
      refine ⟨?_, ?_, ?_⟩
      · rw [good_succ]
        refine ⟨by simpa [Fin.init_snoc] using hg, ?_, ?_⟩
        · rw [snoc_eq]; exact hp
        · rw [snoc_lt _ _ _ _ (by omega), snoc_lt _ _ _ _ (by omega), snoc_eq, h1]; exact hq
      · rw [snoc_lt _ _ _ _ (by omega)]; exact h1
      · rw [snoc_eq]
    · intro A hA
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hA
      have : A ⟨m + 2, by omega⟩ = t := hA.2.2
      rw [← this]
      exact Fin.snoc_init_self A
    · intro B _
      exact Fin.init_snoc ..
  rw [e, Finset.card_eq_sum_card_fiberwise (f := fun B : Fin (m + 2) → R => B ⟨m, by omega⟩)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.filter_filter]
  split_ifs with h
  · unfold cnt
    congr 1
    apply Finset.filter_congr
    intro B _
    constructor
    · rintro ⟨⟨hg, h1, -, -⟩, h0⟩; exact ⟨hg, h0, h1⟩
    · rintro ⟨hg, h0, h1⟩; exact ⟨⟨hg, h1, h.1, h0 ▸ h.2⟩, h0⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro B - ⟨⟨-, -, hp, hq⟩, h0⟩
    exact h ⟨hp, h0 ▸ hq⟩

lemma cnt_eq_G (m : ℕ) (r s : R) : cnt P Q m r s = G P Q m r s := by
  induction m generalizing r s with
  | zero => exact cnt_zero P Q r s
  | succ m ih =>
    rw [cnt_succ]; simp only [G, ih]

/-- The number of good arrays with at least two rows is the sum of the DP table. -/
lemma card_good (m : ℕ) :
    (Finset.univ.filter (Good P Q (m + 2))).card = ∑ r, ∑ s, G P Q m r s := by
  classical
  simp only [← cnt_eq_G]
  unfold cnt
  rw [Finset.card_eq_sum_card_fiberwise (f := fun B : Fin (m + 2) → R => B ⟨m, by omega⟩)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.card_eq_sum_card_fiberwise (f := fun B : Fin (m + 2) → R => B ⟨m + 1, by omega⟩)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.filter_filter, Finset.filter_filter]

end ArrDP

namespace ArrDP

variable {R : Type} [Fintype R] [DecidableEq R] (P : R → Prop) [DecidablePred P]
  (Q : R → R → R → Prop) [∀ a b c, Decidable (Q a b c)]

def U : ℕ → R → R → ℕ
  | 0, _, _ => 1
  | j + 1, r, s => ∑ t, if P t ∧ Q r s t then U j s t else 0

def S (m : ℕ) : ℕ := ∑ r, ∑ s, G P Q m r s

lemma dual (j m : ℕ) : S P Q (m + j) = ∑ r, ∑ s, U P Q j r s * G P Q m r s := by
  induction j generalizing m with
  | zero => simp [S, U]
  | succ j ih =>
    rw [show m + (j + 1) = (m + 1) + j by ring, ih (m + 1)]
    have key : ∀ f : R → R → R → ℕ, (∑ s, ∑ t, ∑ r, f r s t) = ∑ r, ∑ s, ∑ t, f r s t := by
      intro f
      calc (∑ s, ∑ t, ∑ r, f r s t) = ∑ s, ∑ r, ∑ t, f r s t := by
            apply Finset.sum_congr rfl; intro s _; exact Finset.sum_comm
        _ = ∑ r, ∑ s, ∑ t, f r s t := Finset.sum_comm
    have lhs : (∑ s, ∑ t, U P Q j s t * G P Q (m + 1) s t)
        = ∑ s, ∑ t, ∑ r, (if P t ∧ Q r s t then U P Q j s t * G P Q m r s else 0) := by
      apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro t _
      simp only [G, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro r _
      split_ifs <;> simp
    have rhs : (∑ r, ∑ s, U P Q (j + 1) r s * G P Q m r s)
        = ∑ r, ∑ s, ∑ t, (if P t ∧ Q r s t then U P Q j s t * G P Q m r s else 0) := by
      apply Finset.sum_congr rfl; intro r _; apply Finset.sum_congr rfl; intro s _
      simp only [U, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro t _
      split_ifs <;> simp
    rw [lhs, rhs, key]

lemma comb (c : ℕ → ℕ) (d m : ℕ) : ∑ j ∈ Finset.range d, c j * S P Q (m + j) =
    ∑ r, ∑ s, (∑ j ∈ Finset.range d, c j * U P Q j r s) * G P Q m r s := by
  simp only [dual, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro j _
  ring

lemma G_support (m : ℕ) (r s : R) (h : G P Q m r s ≠ 0) : P r ∧ P s := by
  induction m generalizing r s with
  | zero =>
    simp only [G] at h
    by_contra h'; exact h (if_neg h')
  | succ m ih =>
    simp only [G] at h
    obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    by_cases hc : P s ∧ Q x r s
    · rw [if_pos hc] at hx
      exact ⟨(ih x r hx).2, hc.1⟩
    · exact absurd (if_neg hc) hx

end ArrDP


open ArrDP

abbrev R3 := Bool × Bool × Bool

def Pr (r : R3) : Prop := Avoids [(false, false, false), (true, true, true)] r.1 r.2.1 r.2.2
def Qr (r s t : R3) : Prop :=
  Avoids [(false, false, true), (true, false, false)] r.1 s.1 t.1 ∧
  Avoids [(false, false, true), (true, false, false)] r.2.1 s.2.1 t.2.1 ∧
  Avoids [(false, false, true), (true, false, false)] r.2.2 s.2.2 t.2.2

instance : DecidablePred Pr := fun r => by unfold Pr Avoids; infer_instance
instance (r s t : R3) : Decidable (Qr r s t) := by unfold Qr Avoids; infer_instance

def φ : (Fin 3 → Bool) ≃ R3 where
  toFun f := (f 0, f 1, f 2)
  invFun v := ![v.1, v.2.1, v.2.2]
  left_inv f := by funext i; fin_cases i <;> rfl
  right_inv v := rfl

lemma counted_iff (n : ℕ) (A : Fin n → Fin 3 → Bool) :
    IsCounted n A ↔ Good Pr Qr n (fun i => φ (A i)) := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => h1 i 0 (by norm_num), fun i h => ⟨h2 i h 0, h2 i h 1, h2 i h 2⟩⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hj => ?_, fun i h j => ?_⟩
    · obtain rfl : j = 0 := by omega
      exact h1 i
    · obtain ⟨q0, q1, q2⟩ := h2 i h
      fin_cases j
      · exact q0
      · exact q1
      · exact q2

lemma a_eq_card (n : ℕ) : a n = (Finset.univ.filter (Good Pr Qr n)).card := by
  classical
  unfold a
  rw [Nat.card_congr (Equiv.subtypeEquiv (Equiv.arrowCongr (Equiv.refl (Fin n)) φ)
    (fun A => counted_iff n A)), Nat.card_eq_fintype_card, Fintype.card_subtype]

lemma a_two_add (m : ℕ) : a (m + 2) = S Pr Qr m := by
  rw [a_eq_card, card_good]; rfl

lemma a_one : a 1 = 6 := by
  classical
  unfold a
  have e : {A : Fin 1 → Fin 3 → Bool // IsCounted 1 A} ≃ {r : R3 // Pr r} :=
    (Equiv.subtypeEquiv (Equiv.arrowCongr (Equiv.refl (Fin 1)) φ) (fun A => counted_iff 1 A)).trans
      (Equiv.subtypeEquiv (Equiv.funUnique (Fin 1) R3) (fun B => by
        constructor
        · rintro ⟨h1, -⟩; exact h1 _
        · intro h; exact ⟨fun i => by rwa [Subsingleton.elim i default], fun i hi => by omega⟩))
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide

lemma S0 : S Pr Qr 0 = 36 := by decide
lemma S1 : S Pr Qr 1 = 84 := by decide
lemma S2 : S Pr Qr 2 = 198 := by decide

def cL : ℕ → ℕ := fun j => [1, 1, 0, 1].getD j 0
def cR : ℕ → ℕ := fun j => [0, 0, 3, 0].getD j 0

lemma hU : ∀ r s : R3, Pr r → Pr s →
    ∑ j ∈ Finset.range 4, cL j * U Pr Qr j r s = ∑ j ∈ Finset.range 4, cR j * U Pr Qr j r s := by
  decide

lemma Srec (m : ℕ) : ∑ j ∈ Finset.range 4, cL j * S Pr Qr (m + j) =
    ∑ j ∈ Finset.range 4, cR j * S Pr Qr (m + j) := by
  rw [comb, comb]
  apply Finset.sum_congr rfl; intro r _
  apply Finset.sum_congr rfl; intro s _
  by_cases hG : G Pr Qr m r s = 0
  · simp [hG]
  · obtain ⟨hr, hs⟩ := G_support Pr Qr m r s hG
    rw [hU r s hr hs]

lemma ps (f : ℕ → ℚ) (n k : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X ^ k) = if k ≤ n then f (n-k) else 0 := by
  rw [PowerSeries.coeff_mul_X_pow']; simp

lemma ps1 (f : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X) = if 1 ≤ n then f (n-1) else 0 := by
  rw [← ps, pow_one]

theorem main_proof :
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X - PowerSeries.X ^ 2)) =
      6 * PowerSeries.X * (1 + 3 * PowerSeries.X - 3 * PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3)) ∧
    (∀ n : ℕ, 2 ≤ n → (a n : ℝ) = 3 / 2 * (2 + (1 - 2 * Real.sqrt 2) * (1 - Real.sqrt 2) ^ n +
      (1 + Real.sqrt 2) ^ n * (1 + 2 * Real.sqrt 2))) := by
  have v1 : a 1 = 6 := a_one
  have v2 : a 2 = 36 := by rw [show (2:ℕ) = 0 + 2 by rfl, a_two_add, S0]
  have v3 : a 3 = 84 := by rw [show (3:ℕ) = 1 + 2 by rfl, a_two_add, S1]
  have v4 : a 4 = 198 := by rw [show (4:ℕ) = 2 + 2 by rfl, a_two_add, S2]
  have hrec : ∀ m : ℕ, (a (m + 5) : ℤ) = 3 * a (m + 4) - a (m + 3) - a (m + 2) := by
    intro m
    have h := Srec m
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, cL, cR, List.getD] at h
    simp only [show m + 5 = (m + 3) + 2 by omega, show m + 4 = (m + 2) + 2 by omega,
      show m + 3 = (m + 1) + 2 by omega, a_two_add]
    norm_num at h
    have h' : (S Pr Qr (m + 3) : ℤ) + S Pr Qr (m + 1) + S Pr Qr m = 3 * S Pr Qr (m + 2) := by
      exact_mod_cast (by omega : S Pr Qr (m + 3) + S Pr Qr (m + 1) + S Pr Qr m = 3 * S Pr Qr (m + 2))
    linear_combination h'
  refine ⟨?_, ?_⟩
  · rw [show ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X - PowerSeries.X ^ 2) : PowerSeries ℚ) =
        1 - PowerSeries.C (3:ℚ) * PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.X ^ 3 by
        simp only [map_ofNat]; ring,
      show (6 * PowerSeries.X * (1 + 3 * PowerSeries.X - 3 * PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3) :
        PowerSeries ℚ) = PowerSeries.C (6:ℚ) * PowerSeries.X + PowerSeries.C (18:ℚ) * PowerSeries.X ^ 2
          - PowerSeries.C (18:ℚ) * PowerSeries.X ^ 3 - PowerSeries.C (12:ℚ) * PowerSeries.X ^ 4 by
        simp only [map_ofNat]; ring]
    ext n
    simp only [mul_add, mul_sub, mul_one, map_add, map_sub, mul_left_comm _ (PowerSeries.C _),
      PowerSeries.coeff_C_mul, ps, ps1, PowerSeries.coeff_X, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
    rcases (show n ≤ 4 ∨ 5 ≤ n by omega) with h | h
    · interval_cases n <;> simp [v1, v2, v3, v4] <;> try norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
      have hq : (a (m + 5) : ℚ) = 3 * a (m + 4) - a (m + 3) - a (m + 2) := by exact_mod_cast hrec m
      simp [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
        show m + 5 - 3 = m + 2 by omega, show m + 5 ≠ 1 by omega, show m + 5 ≠ 2 by omega,
        show m + 5 ≠ 3 by omega, show m + 5 ≠ 4 by omega]
      rw [hq]; ring
  · have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have key : ∀ m : ℕ, ∀ k ≤ m, (a (k + 2) : ℝ) = 3 / 2 * (2 + (1 - 2 * Real.sqrt 2) *
        (1 - Real.sqrt 2) ^ (k + 2) + (1 + Real.sqrt 2) ^ (k + 2) * (1 + 2 * Real.sqrt 2)) := by
      intro m
      induction m with
      | zero =>
        intro k hk; obtain rfl : k = 0 := by omega
        rw [v2]; push_cast; linear_combination (-15 : ℝ) * hs
      | succ m ih =>
        intro k hk
        rcases (show k ≤ m ∨ k = m + 1 by omega) with hk | rfl
        · exact ih k hk
        · rcases (show m = 0 ∨ m = 1 ∨ 2 ≤ m by omega) with rfl | rfl | hm
          · rw [v3]; push_cast; linear_combination (-39 - 6 * Real.sqrt 2 ^ 2) * hs
          · rw [v4]; push_cast; linear_combination (-96 - 27 * Real.sqrt 2 ^ 2) * hs
          · obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
            have hq : (a (j + 5) : ℝ) = 3 * a (j + 4) - a (j + 3) - a (j + 2) := by
              exact_mod_cast hrec j
            rw [show j + 2 + 1 + 2 = j + 5 by omega, hq, show j + 4 = (j + 2) + 2 by omega,
              show j + 3 = (j + 1) + 2 by omega, ih (j + 2) le_rfl, ih (j + 1) (by omega), ih j (by omega)]
            linear_combination (-(3 / 2) * ((1 + 2 * Real.sqrt 2) * (1 + Real.sqrt 2) ^ (j + 2) * Real.sqrt 2
              - (1 - 2 * Real.sqrt 2) * (1 - Real.sqrt 2) ^ (j + 2) * Real.sqrt 2)) * hs
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    exact key k k le_rfl

end OMA.P_oeis_a207656

theorem OMA.solution : type_of% @OMA.S_oeis_a207656.main :=
  OMA.P_oeis_a207656.main_proof
