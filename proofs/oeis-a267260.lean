import OMAStatements.S_oeis_a267260
import Mathlib

namespace CAOEISA267260Aux

def F (t : ℕ) (i : ℤ) : Prop :=
  (((t : ℤ) = 0) ∧ (i = 0)) ∨
  (((t : ℤ) = 1) ∧ (¬(i = 1))) ∨
  (((t : ℤ) = 2) ∧ (0 ≤ i ∧ i ≤ 2)) ∨
  (((t : ℤ) = 3) ∧ (¬(i = 1 ∨ i = 3))) ∨
  (((t : ℤ) = 4) ∧ (0 ≤ i ∧ i ≤ 4)) ∨
  ((5 ≤ (t : ℤ) ∧ (t : ℤ) % 2 = 1) ∧ (¬(i = (t : ℤ) - 4 ∨ i = (t : ℤ) - 3 ∨ i = (t : ℤ) - 2 ∨ i = (t : ℤ)))) ∨
  ((6 ≤ (t : ℤ) ∧ (t : ℤ) % 2 = 0) ∧ ((i = (t : ℤ) - 6 ∨ ((t : ℤ) - 4 ≤ i ∧ i ≤ (t : ℤ)))))

lemma Fph0 (t : ℕ) (i : ℤ) (hg : (t : ℤ) = 0) :
    F t i ↔ (i = 0) := by
  unfold F
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h
    · exact h.2
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
  · intro h0
    have h := And.intro hg h0
    exact Or.inl h

lemma Fph1 (t : ℕ) (i : ℤ) (hg : (t : ℤ) = 1) :
    F t i ↔ (¬(i = 1)) := by
  unfold F
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h
    · exact absurd h.1 (by omega)
    · exact h.2
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
  · intro h0
    have h := And.intro hg h0
    exact Or.inr (Or.inl h)

lemma Fph2 (t : ℕ) (i : ℤ) (hg : (t : ℤ) = 2) :
    F t i ↔ (0 ≤ i ∧ i ≤ 2) := by
  unfold F
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
    · exact h.2
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
  · intro h0
    have h := And.intro hg h0
    exact Or.inr (Or.inr (Or.inl h))

lemma Fph3 (t : ℕ) (i : ℤ) (hg : (t : ℤ) = 3) :
    F t i ↔ (¬(i = 1 ∨ i = 3)) := by
  unfold F
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
    · exact h.2
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
  · intro h0
    have h := And.intro hg h0
    exact Or.inr (Or.inr (Or.inr (Or.inl h)))

lemma Fph4 (t : ℕ) (i : ℤ) (hg : (t : ℤ) = 4) :
    F t i ↔ (0 ≤ i ∧ i ≤ 4) := by
  unfold F
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
    · exact h.2
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
  · intro h0
    have h := And.intro hg h0
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

lemma Fph5 (t : ℕ) (i : ℤ) (hg : 5 ≤ (t : ℤ) ∧ (t : ℤ) % 2 = 1) :
    F t i ↔ (¬(i = (t : ℤ) - 4 ∨ i = (t : ℤ) - 3 ∨ i = (t : ℤ) - 2 ∨ i = (t : ℤ))) := by
  unfold F
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
    · exact h.2
    · exact absurd h.1 (by omega)
  · intro h0
    have h := And.intro hg h0
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

lemma Fph6 (t : ℕ) (i : ℤ) (hg : 6 ≤ (t : ℤ) ∧ (t : ℤ) % 2 = 0) :
    F t i ↔ ((i = (t : ℤ) - 6 ∨ ((t : ℤ) - 4 ≤ i ∧ i ≤ (t : ℤ)))) := by
  unfold F
  constructor
  · intro h
    rcases h with h | h | h | h | h | h | h
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
    · exact h.2
  · intro h0
    have h := And.intro hg h0
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h))))))

open OMA.S_oeis_a267260 in
lemma rule_step (b1 b2 b3 : Bool) (P1 P2 P3 Q : Prop) (h1 : b1 = true ↔ P1) (h2 : b2 = true ↔ P2)
    (h3 : b3 = true ↔ P3)
    (H0 : ¬P1 → ¬P2 → ¬P3 → Q) (H1 : ¬P1 → ¬P2 → P3 → Q)
    (H2 : ¬P1 → P2 → ¬P3 → Q) (H3 : ¬P1 → P2 → P3 → Q)
    (H4 : P1 → ¬P2 → ¬P3 → ¬Q) (H5 : P1 → ¬P2 → P3 → Q)
    (H6 : P1 → P2 → ¬P3 → Q) (H7 : P1 → P2 → P3 → ¬Q) :
    ruleOut 111 b1 b2 b3 = true ↔ Q := by
  cases b1 <;> cases b2 <;> cases b3
  · exact ⟨fun _ => H0 (fun h => Bool.false_ne_true (h1.mpr h)) (fun h => Bool.false_ne_true (h2.mpr h)) (fun h => Bool.false_ne_true (h3.mpr h)), fun _ => by decide⟩
  · exact ⟨fun _ => H1 (fun h => Bool.false_ne_true (h1.mpr h)) (fun h => Bool.false_ne_true (h2.mpr h)) (h3.mp rfl), fun _ => by decide⟩
  · exact ⟨fun _ => H2 (fun h => Bool.false_ne_true (h1.mpr h)) (h2.mp rfl) (fun h => Bool.false_ne_true (h3.mpr h)), fun _ => by decide⟩
  · exact ⟨fun _ => H3 (fun h => Bool.false_ne_true (h1.mpr h)) (h2.mp rfl) (h3.mp rfl), fun _ => by decide⟩
  · exact ⟨fun h => absurd h (by decide), fun q => absurd q (H4 (h1.mp rfl) (fun h => Bool.false_ne_true (h2.mpr h)) (fun h => Bool.false_ne_true (h3.mpr h)))⟩
  · exact ⟨fun _ => H5 (h1.mp rfl) (fun h => Bool.false_ne_true (h2.mpr h)) (h3.mp rfl), fun _ => by decide⟩
  · exact ⟨fun _ => H6 (h1.mp rfl) (h2.mp rfl) (fun h => Bool.false_ne_true (h3.mpr h)), fun _ => by decide⟩
  · exact ⟨fun h => absurd h (by decide), fun q => absurd q (H7 (h1.mp rfl) (h2.mp rfl) (h3.mp rfl))⟩

set_option maxHeartbeats 4000000 in
open OMA.S_oeis_a267260 in
lemma cell_iff : ∀ (t : ℕ) (i : ℤ), cell 111 t i = true ↔ F t i := by
  intro t
  induction t with
  | zero =>
    intro i
    rw [cell]
    simp only [decide_eq_true_eq]
    rw [Fph0 0 i (by omega)]
  | succ t ih =>
    intro i
    rw [cell]
    rcases (by omega : ((t : ℤ) = 0) ∨ ((t : ℤ) = 1) ∨ ((t : ℤ) = 2) ∨ ((t : ℤ) = 3) ∨ ((t : ℤ) = 4) ∨ (5 ≤ (t : ℤ) ∧ (t : ℤ) % 2 = 1) ∨ (6 ≤ (t : ℤ) ∧ (t : ℤ) % 2 = 0)) with hg | hg | hg | hg | hg | hg | hg
    · have hg' : ((t + 1 : ℕ) : ℤ) = 1 := by omega
      rw [Fph1 (t + 1) i hg']
      apply rule_step _ _ _ _ _ _ _ ((ih (i - 1)).trans (Fph0 t (i - 1) hg))
        ((ih i).trans (Fph0 t i hg)) ((ih (i + 1)).trans (Fph0 t (i + 1) hg)) <;> omega
    · have hg' : ((t + 1 : ℕ) : ℤ) = 2 := by omega
      rw [Fph2 (t + 1) i hg']
      apply rule_step _ _ _ _ _ _ _ ((ih (i - 1)).trans (Fph1 t (i - 1) hg))
        ((ih i).trans (Fph1 t i hg)) ((ih (i + 1)).trans (Fph1 t (i + 1) hg)) <;> omega
    · have hg' : ((t + 1 : ℕ) : ℤ) = 3 := by omega
      rw [Fph3 (t + 1) i hg']
      apply rule_step _ _ _ _ _ _ _ ((ih (i - 1)).trans (Fph2 t (i - 1) hg))
        ((ih i).trans (Fph2 t i hg)) ((ih (i + 1)).trans (Fph2 t (i + 1) hg)) <;> omega
    · have hg' : ((t + 1 : ℕ) : ℤ) = 4 := by omega
      rw [Fph4 (t + 1) i hg']
      apply rule_step _ _ _ _ _ _ _ ((ih (i - 1)).trans (Fph3 t (i - 1) hg))
        ((ih i).trans (Fph3 t i hg)) ((ih (i + 1)).trans (Fph3 t (i + 1) hg)) <;> omega
    · have hg' : 5 ≤ ((t + 1 : ℕ) : ℤ) ∧ ((t + 1 : ℕ) : ℤ) % 2 = 1 := by omega
      rw [Fph5 (t + 1) i hg']
      apply rule_step _ _ _ _ _ _ _ ((ih (i - 1)).trans (Fph4 t (i - 1) hg))
        ((ih i).trans (Fph4 t i hg)) ((ih (i + 1)).trans (Fph4 t (i + 1) hg)) <;> omega
    · have hg' : 6 ≤ ((t + 1 : ℕ) : ℤ) ∧ ((t + 1 : ℕ) : ℤ) % 2 = 0 := by omega
      rw [Fph6 (t + 1) i hg']
      apply rule_step _ _ _ _ _ _ _ ((ih (i - 1)).trans (Fph5 t (i - 1) hg))
        ((ih i).trans (Fph5 t i hg)) ((ih (i + 1)).trans (Fph5 t (i + 1) hg)) <;> omega
    · have hg' : 5 ≤ ((t + 1 : ℕ) : ℤ) ∧ ((t + 1 : ℕ) : ℤ) % 2 = 1 := by omega
      rw [Fph5 (t + 1) i hg']
      apply rule_step _ _ _ _ _ _ _ ((ih (i - 1)).trans (Fph6 t (i - 1) hg))
        ((ih i).trans (Fph6 t i hg)) ((ih (i + 1)).trans (Fph6 t (i + 1) hg)) <;> omega

open OMA.S_oeis_a267260 in
def w (t j : ℕ) : ℕ := if cell 111 t ((j : ℤ) - t) = true then 1 else 0

open OMA.S_oeis_a267260 in
lemma onCount_w (t : ℕ) : onCount 111 t = ∑ j ∈ Finset.range (2 * t + 1), w t j := rfl

lemma w_one (t j : ℕ) (h : F t ((j : ℤ) - t)) : w t j = 1 := by
  unfold w
  rw [if_pos ((cell_iff _ _).mpr h)]

lemma w_zero (t j : ℕ) (h : ¬ F t ((j : ℤ) - t)) : w t j = 0 := by
  unfold w
  rw [if_neg (fun hc => h ((cell_iff _ _).mp hc))]

lemma w_congr (t t' j j' : ℕ) (h : F t ((j : ℤ) - t) ↔ F t' ((j' : ℤ) - t')) : w t j = w t' j' := by
  by_cases hf : F t ((j : ℤ) - t)
  · rw [w_one t j hf, w_one t' j' (h.mp hf)]
  · rw [w_zero t j hf, w_zero t' j' (fun h' => hf (h.mpr h'))]


lemma sum_cut (f g : ℕ → ℕ) (A N s1 s2 s3 : ℕ) (hA : A ≤ N)
    (h1 : ∀ j, j < A → f (s1 + j) = g j)
    (h2 : ∀ j, A ≤ j → j < N → f (s1 + s2 + j) = g j) :
    ∑ j ∈ Finset.range (s1 + N + s2 + s3), f j =
      ∑ j ∈ Finset.range N, g j + (∑ k ∈ Finset.range s1, f k + ∑ k ∈ Finset.range s2, f (s1 + A + k)
        + ∑ k ∈ Finset.range s3, f (s1 + N + s2 + k)) := by
  obtain ⟨B, rfl⟩ : ∃ B, N = A + B := ⟨N - A, by omega⟩
  have e : s1 + (A + B) + s2 + s3 = (((s1 + A) + s2) + B) + s3 := by ring
  rw [e, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add,
    Finset.sum_range_add (fun j => g j) A B]
  have e1 : ∑ x ∈ Finset.range A, f (s1 + x) = ∑ x ∈ Finset.range A, g x :=
    Finset.sum_congr rfl (fun x hx => h1 x (Finset.mem_range.mp hx))
  have e2 : ∑ x ∈ Finset.range B, f (s1 + A + s2 + x) = ∑ x ∈ Finset.range B, g (A + x) :=
    Finset.sum_congr rfl (fun x hx => by
      have := h2 (A + x) (by omega) (by have := Finset.mem_range.mp hx; omega)
      rw [← this]
      congr 1
      ring)
  have e3 : ∑ x ∈ Finset.range s3, f (s1 + A + s2 + B + x) = ∑ x ∈ Finset.range s3, f (s1 + (A + B) + s2 + x) :=
    Finset.sum_congr rfl (fun x _ => by congr 1; ring)
  rw [e1, e2, e3]
  ring

open OMA.S_oeis_a267260 in
lemma oc0 : onCount 111 0 = 1 := by
  rw [onCount_w, show 2 * 0 + 1 = 1 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have v0 : w 0 (0) = 1 := w_one _ _ ((Fph0 0 _ (by omega)).mpr (by omega))
  omega

open OMA.S_oeis_a267260 in
lemma oc1 : onCount 111 1 = 2 := by
  rw [onCount_w, show 2 * 1 + 1 = 3 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have v0 : w 1 (0) = 1 := w_one _ _ ((Fph1 1 _ (by omega)).mpr (by omega))
  have v1 : w 1 (1) = 1 := w_one _ _ ((Fph1 1 _ (by omega)).mpr (by omega))
  have v2 : w 1 (2) = 0 := w_zero _ _ (fun h => by
    have h' := (Fph1 1 _ (by omega)).mp h
    omega)
  omega

open OMA.S_oeis_a267260 in
lemma oc2 : onCount 111 2 = 3 := by
  rw [onCount_w, show 2 * 2 + 1 = 5 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have v0 : w 2 (0) = 0 := w_zero _ _ (fun h => by
    have h' := (Fph2 2 _ (by omega)).mp h
    omega)
  have v1 : w 2 (1) = 0 := w_zero _ _ (fun h => by
    have h' := (Fph2 2 _ (by omega)).mp h
    omega)
  have v2 : w 2 (2) = 1 := w_one _ _ ((Fph2 2 _ (by omega)).mpr (by omega))
  have v3 : w 2 (3) = 1 := w_one _ _ ((Fph2 2 _ (by omega)).mpr (by omega))
  have v4 : w 2 (4) = 1 := w_one _ _ ((Fph2 2 _ (by omega)).mpr (by omega))
  omega

open OMA.S_oeis_a267260 in
lemma oc3 : onCount 111 3 = 5 := by
  rw [onCount_w, show 2 * 3 + 1 = 7 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have v0 : w 3 (0) = 1 := w_one _ _ ((Fph3 3 _ (by omega)).mpr (by omega))
  have v1 : w 3 (1) = 1 := w_one _ _ ((Fph3 3 _ (by omega)).mpr (by omega))
  have v2 : w 3 (2) = 1 := w_one _ _ ((Fph3 3 _ (by omega)).mpr (by omega))
  have v3 : w 3 (3) = 1 := w_one _ _ ((Fph3 3 _ (by omega)).mpr (by omega))
  have v4 : w 3 (4) = 0 := w_zero _ _ (fun h => by
    have h' := (Fph3 3 _ (by omega)).mp h
    omega)
  have v5 : w 3 (5) = 1 := w_one _ _ ((Fph3 3 _ (by omega)).mpr (by omega))
  have v6 : w 3 (6) = 0 := w_zero _ _ (fun h => by
    have h' := (Fph3 3 _ (by omega)).mp h
    omega)
  omega

open OMA.S_oeis_a267260 in
lemma oc4 : onCount 111 4 = 5 := by
  rw [onCount_w, show 2 * 4 + 1 = 9 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have v0 : w 4 (0) = 0 := w_zero _ _ (fun h => by
    have h' := (Fph4 4 _ (by omega)).mp h
    omega)
  have v1 : w 4 (1) = 0 := w_zero _ _ (fun h => by
    have h' := (Fph4 4 _ (by omega)).mp h
    omega)
  have v2 : w 4 (2) = 0 := w_zero _ _ (fun h => by
    have h' := (Fph4 4 _ (by omega)).mp h
    omega)
  have v3 : w 4 (3) = 0 := w_zero _ _ (fun h => by
    have h' := (Fph4 4 _ (by omega)).mp h
    omega)
  have v4 : w 4 (4) = 1 := w_one _ _ ((Fph4 4 _ (by omega)).mpr (by omega))
  have v5 : w 4 (5) = 1 := w_one _ _ ((Fph4 4 _ (by omega)).mpr (by omega))
  have v6 : w 4 (6) = 1 := w_one _ _ ((Fph4 4 _ (by omega)).mpr (by omega))
  have v7 : w 4 (7) = 1 := w_one _ _ ((Fph4 4 _ (by omega)).mpr (by omega))
  have v8 : w 4 (8) = 1 := w_one _ _ ((Fph4 4 _ (by omega)).mpr (by omega))
  omega

open OMA.S_oeis_a267260 in
lemma oc5 : onCount 111 5 = 7 := by
  rw [onCount_w, show 2 * 5 + 1 = 11 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have v0 : w 5 (0) = 1 := w_one _ _ ((Fph5 5 _ (by omega)).mpr (by omega))
  have v1 : w 5 (1) = 1 := w_one _ _ ((Fph5 5 _ (by omega)).mpr (by omega))
  have v2 : w 5 (2) = 1 := w_one _ _ ((Fph5 5 _ (by omega)).mpr (by omega))
  have v3 : w 5 (3) = 1 := w_one _ _ ((Fph5 5 _ (by omega)).mpr (by omega))
  have v4 : w 5 (4) = 1 := w_one _ _ ((Fph5 5 _ (by omega)).mpr (by omega))
  have v5 : w 5 (5) = 1 := w_one _ _ ((Fph5 5 _ (by omega)).mpr (by omega))
  have v6 : w 5 (6) = 0 := w_zero _ _ (fun h => by
    have h' := (Fph5 5 _ (by omega)).mp h
    omega)
  have v7 : w 5 (7) = 0 := w_zero _ _ (fun h => by
    have h' := (Fph5 5 _ (by omega)).mp h
    omega)
  have v8 : w 5 (8) = 0 := w_zero _ _ (fun h => by
    have h' := (Fph5 5 _ (by omega)).mp h
    omega)
  have v9 : w 5 (9) = 1 := w_one _ _ ((Fph5 5 _ (by omega)).mpr (by omega))
  have v10 : w 5 (10) = 0 := w_zero _ _ (fun h => by
    have h' := (Fph5 5 _ (by omega)).mp h
    omega)
  omega

open OMA.S_oeis_a267260 in
lemma oc6 : onCount 111 6 = 6 := by
  rw [onCount_w, show 2 * 6 + 1 = 13 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have v0 : w 6 (0) = 0 := w_zero _ _ (fun h => by
    have h' := (Fph6 6 _ (by omega)).mp h
    omega)
  have v1 : w 6 (1) = 0 := w_zero _ _ (fun h => by
    have h' := (Fph6 6 _ (by omega)).mp h
    omega)
  have v2 : w 6 (2) = 0 := w_zero _ _ (fun h => by
    have h' := (Fph6 6 _ (by omega)).mp h
    omega)
  have v3 : w 6 (3) = 0 := w_zero _ _ (fun h => by
    have h' := (Fph6 6 _ (by omega)).mp h
    omega)
  have v4 : w 6 (4) = 0 := w_zero _ _ (fun h => by
    have h' := (Fph6 6 _ (by omega)).mp h
    omega)
  have v5 : w 6 (5) = 0 := w_zero _ _ (fun h => by
    have h' := (Fph6 6 _ (by omega)).mp h
    omega)
  have v6 : w 6 (6) = 1 := w_one _ _ ((Fph6 6 _ (by omega)).mpr (by omega))
  have v7 : w 6 (7) = 0 := w_zero _ _ (fun h => by
    have h' := (Fph6 6 _ (by omega)).mp h
    omega)
  have v8 : w 6 (8) = 1 := w_one _ _ ((Fph6 6 _ (by omega)).mpr (by omega))
  have v9 : w 6 (9) = 1 := w_one _ _ ((Fph6 6 _ (by omega)).mpr (by omega))
  have v10 : w 6 (10) = 1 := w_one _ _ ((Fph6 6 _ (by omega)).mpr (by omega))
  have v11 : w 6 (11) = 1 := w_one _ _ ((Fph6 6 _ (by omega)).mpr (by omega))
  have v12 : w 6 (12) = 1 := w_one _ _ ((Fph6 6 _ (by omega)).mpr (by omega))
  omega

open OMA.S_oeis_a267260 in
lemma oc7 : onCount 111 7 = 11 := by
  rw [onCount_w, show 2 * 7 + 1 = 15 from rfl]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have v0 : w 7 (0) = 1 := w_one _ _ ((Fph5 7 _ (by omega)).mpr (by omega))
  have v1 : w 7 (1) = 1 := w_one _ _ ((Fph5 7 _ (by omega)).mpr (by omega))
  have v2 : w 7 (2) = 1 := w_one _ _ ((Fph5 7 _ (by omega)).mpr (by omega))
  have v3 : w 7 (3) = 1 := w_one _ _ ((Fph5 7 _ (by omega)).mpr (by omega))
  have v4 : w 7 (4) = 1 := w_one _ _ ((Fph5 7 _ (by omega)).mpr (by omega))
  have v5 : w 7 (5) = 1 := w_one _ _ ((Fph5 7 _ (by omega)).mpr (by omega))
  have v6 : w 7 (6) = 1 := w_one _ _ ((Fph5 7 _ (by omega)).mpr (by omega))
  have v7 : w 7 (7) = 1 := w_one _ _ ((Fph5 7 _ (by omega)).mpr (by omega))
  have v8 : w 7 (8) = 1 := w_one _ _ ((Fph5 7 _ (by omega)).mpr (by omega))
  have v9 : w 7 (9) = 1 := w_one _ _ ((Fph5 7 _ (by omega)).mpr (by omega))
  have v10 : w 7 (10) = 0 := w_zero _ _ (fun h => by
    have h' := (Fph5 7 _ (by omega)).mp h
    omega)
  have v11 : w 7 (11) = 0 := w_zero _ _ (fun h => by
    have h' := (Fph5 7 _ (by omega)).mp h
    omega)
  have v12 : w 7 (12) = 0 := w_zero _ _ (fun h => by
    have h' := (Fph5 7 _ (by omega)).mp h
    omega)
  have v13 : w 7 (13) = 1 := w_one _ _ ((Fph5 7 _ (by omega)).mpr (by omega))
  have v14 : w 7 (14) = 0 := w_zero _ _ (fun h => by
    have h' := (Fph5 7 _ (by omega)).mp h
    omega)
  omega

set_option maxHeartbeats 4000000 in
open OMA.S_oeis_a267260 in
lemma ocstep0 (m : ℕ) : onCount 111 (6 + 2 * (m + 1)) = onCount 111 (6 + 2 * m) + 0 := by
  rw [onCount_w, onCount_w]
  rw [show 2 * (6 + 2 * (m + 1)) + 1 = 4 + (2 * (6 + 2 * m) + 1) + 0 + 0 from by ring]
  rw [sum_cut (w (6 + 2 * (m + 1))) (w (6 + 2 * m)) (2 * (6 + 2 * m) + 1) (2 * (6 + 2 * m) + 1) 4 0 0 (by omega)
    (fun j hj => w_congr _ _ _ _ (((Fph6 (6 + 2 * (m + 1)) _ (by omega)).trans (by omega)).trans (Fph6 (6 + 2 * m) _ (by omega)).symm))
    (fun j hj1 hj2 => w_congr _ _ _ _ (((Fph6 (6 + 2 * (m + 1)) _ (by omega)).trans (by omega)).trans (Fph6 (6 + 2 * m) _ (by omega)).symm))]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have v1 : w (6 + 2 * (m + 1)) (0) = 0 := w_zero _ _ (fun h => by
    have h' := (Fph6 (6 + 2 * (m + 1)) _ (by omega)).mp h
    omega)
  have v2 : w (6 + 2 * (m + 1)) (1) = 0 := w_zero _ _ (fun h => by
    have h' := (Fph6 (6 + 2 * (m + 1)) _ (by omega)).mp h
    omega)
  have v3 : w (6 + 2 * (m + 1)) (2) = 0 := w_zero _ _ (fun h => by
    have h' := (Fph6 (6 + 2 * (m + 1)) _ (by omega)).mp h
    omega)
  have v4 : w (6 + 2 * (m + 1)) (3) = 0 := w_zero _ _ (fun h => by
    have h' := (Fph6 (6 + 2 * (m + 1)) _ (by omega)).mp h
    omega)
  omega

open OMA.S_oeis_a267260 in
lemma ocr0 (m : ℕ) : onCount 111 (6 + 2 * m) = 6 + 0 * m := by
  induction m with
  | zero => exact oc6
  | succ k ih =>
    rw [ocstep0, ih]
    ring

set_option maxHeartbeats 4000000 in
open OMA.S_oeis_a267260 in
lemma ocstep1 (m : ℕ) : onCount 111 (7 + 2 * (m + 1)) = onCount 111 (7 + 2 * m) + 4 := by
  rw [onCount_w, onCount_w]
  rw [show 2 * (7 + 2 * (m + 1)) + 1 = 4 + (2 * (7 + 2 * m) + 1) + 0 + 0 from by ring]
  rw [sum_cut (w (7 + 2 * (m + 1))) (w (7 + 2 * m)) (2 * (7 + 2 * m) + 1) (2 * (7 + 2 * m) + 1) 4 0 0 (by omega)
    (fun j hj => w_congr _ _ _ _ (((Fph5 (7 + 2 * (m + 1)) _ (by omega)).trans (by omega)).trans (Fph5 (7 + 2 * m) _ (by omega)).symm))
    (fun j hj1 hj2 => w_congr _ _ _ _ (((Fph5 (7 + 2 * (m + 1)) _ (by omega)).trans (by omega)).trans (Fph5 (7 + 2 * m) _ (by omega)).symm))]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  have v1 : w (7 + 2 * (m + 1)) (0) = 1 := w_one _ _ ((Fph5 (7 + 2 * (m + 1)) _ (by omega)).mpr (by omega))
  have v2 : w (7 + 2 * (m + 1)) (1) = 1 := w_one _ _ ((Fph5 (7 + 2 * (m + 1)) _ (by omega)).mpr (by omega))
  have v3 : w (7 + 2 * (m + 1)) (2) = 1 := w_one _ _ ((Fph5 (7 + 2 * (m + 1)) _ (by omega)).mpr (by omega))
  have v4 : w (7 + 2 * (m + 1)) (3) = 1 := w_one _ _ ((Fph5 (7 + 2 * (m + 1)) _ (by omega)).mpr (by omega))
  omega

open OMA.S_oeis_a267260 in
lemma ocr1 (m : ℕ) : onCount 111 (7 + 2 * m) = 11 + 4 * m := by
  induction m with
  | zero => exact oc7
  | succ k ih =>
    rw [ocstep1, ih]
    ring

open OMA.S_oeis_a267260 in
lemma ocE (m : ℕ) : (onCount 111 (6 + 2 * m) : ℤ) = 6 + 0 * (m : ℤ) := by
  rw [ocr0]
  push_cast
  ring

open OMA.S_oeis_a267260 in
lemma ocO (m : ℕ) : (onCount 111 (6 + 2 * m + 1) : ℤ) = 11 + 4 * (m : ℤ) := by
  rw [show 6 + 2 * m + 1 = 7 + 2 * m from by ring, ocr1]
  push_cast
  ring


open PowerSeries in
lemma coeff_term (f : ℕ → ℚ) (c : ℚ) (k n : ℕ) :
    coeff n (mk f * (C c * X ^ k)) = if k ≤ n then c * f (n - k) else 0 := by
  rw [← mul_assoc, mul_comm (mk f) (C c), mul_assoc, coeff_C_mul, coeff_mul_X_pow']
  split_ifs <;> simp [coeff_mk]

open OMA.S_oeis_a267260 in
lemma oc_eq (n : ℕ) (hn : 6 ≤ n) : (onCount 111 n : ℚ) = (((3 : ℚ) / 2) + (1 : ℚ) * (n : ℚ)) + (-1 : ℚ) ^ n * (((9 : ℚ) / 2) + (-1 : ℚ) * (n : ℚ)) := by
  obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 6 + 2 * m ∨ n = 6 + 2 * m + 1 := ⟨(n - 6) / 2, by omega⟩
  · have hs : (-1 : ℚ) ^ (6 + 2 * m) = 1 := Even.neg_one_pow ⟨3 + m, by ring⟩
    have h := ocE m
    have h' : ((onCount 111 (6 + 2 * m) : ℕ) : ℚ) = (((onCount 111 (6 + 2 * m) : ℕ) : ℤ) : ℚ) := by norm_cast
    rw [h', h, hs]
    push_cast
    ring
  · have hs : (-1 : ℚ) ^ (6 + 2 * m + 1) = -1 := Odd.neg_one_pow ⟨3 + m, by ring⟩
    have h := ocO m
    have h' : ((onCount 111 (6 + 2 * m + 1) : ℕ) : ℚ) = (((onCount 111 (6 + 2 * m + 1) : ℕ) : ℤ) : ℚ) := by norm_cast
    rw [h', h, hs]
    push_cast
    ring

open OMA.S_oeis_a267260 in
lemma a_eq (n : ℕ) (hn : 6 ≤ n) : (a n : ℚ) = ((2 : ℚ) * (n : ℚ) + ((1 : ℚ) / 2) * (n : ℚ) ^ 2) + (-1 : ℚ) ^ n * ((2 : ℚ) + (-(1 : ℚ) / 2) * (n : ℚ)) := by
  induction n, hn using Nat.le_induction with
  | base =>
    norm_num [a, Finset.sum_range_succ, oc0, oc1, oc2, oc3, oc4, oc5, oc6, oc7]
  | succ k hk ih =>
    have e : (a (k + 1) : ℚ) = (a k : ℚ) + (onCount 111 (k + 1) : ℚ) := by
      unfold a
      rw [Finset.sum_range_succ]
      push_cast
      ring
    rw [e, ih, oc_eq (k + 1) (by omega), pow_succ]
    push_cast
    ring

open OMA.S_oeis_a267260 in
lemma av0 : (a 0 : ℚ) = 1 := by
  norm_num [a, Finset.sum_range_succ, oc0, oc1, oc2, oc3, oc4, oc5, oc6, oc7]

open OMA.S_oeis_a267260 in
lemma av1 : (a 1 : ℚ) = 3 := by
  norm_num [a, Finset.sum_range_succ, oc0, oc1, oc2, oc3, oc4, oc5, oc6, oc7]

open OMA.S_oeis_a267260 in
lemma av2 : (a 2 : ℚ) = 6 := by
  norm_num [a, Finset.sum_range_succ, oc0, oc1, oc2, oc3, oc4, oc5, oc6, oc7]

open OMA.S_oeis_a267260 in
lemma av3 : (a 3 : ℚ) = 11 := by
  norm_num [a, Finset.sum_range_succ, oc0, oc1, oc2, oc3, oc4, oc5, oc6, oc7]

open OMA.S_oeis_a267260 in
lemma av4 : (a 4 : ℚ) = 16 := by
  norm_num [a, Finset.sum_range_succ, oc0, oc1, oc2, oc3, oc4, oc5, oc6, oc7]

open OMA.S_oeis_a267260 in
lemma av5 : (a 5 : ℚ) = 23 := by
  norm_num [a, Finset.sum_range_succ, oc0, oc1, oc2, oc3, oc4, oc5, oc6, oc7]

open OMA.S_oeis_a267260 in
lemma av6 : (a 6 : ℚ) = 29 := by
  rw [a_eq 6 (by norm_num)]
  norm_num

open OMA.S_oeis_a267260 in
lemma av7 : (a 7 : ℚ) = 40 := by
  rw [a_eq 7 (by norm_num)]
  norm_num

open OMA.S_oeis_a267260 in
lemma av8 : (a 8 : ℚ) = 46 := by
  rw [a_eq 8 (by norm_num)]
  norm_num

open OMA.S_oeis_a267260 in
lemma av9 : (a 9 : ℚ) = 61 := by
  rw [a_eq 9 (by norm_num)]
  norm_num

open OMA.S_oeis_a267260 in
lemma av10 : (a 10 : ℚ) = 67 := by
  rw [a_eq 10 (by norm_num)]
  norm_num

open OMA.S_oeis_a267260 in
lemma av11 : (a 11 : ℚ) = 86 := by
  rw [a_eq 11 (by norm_num)]
  norm_num

end CAOEISA267260Aux

set_option maxHeartbeats 1600000 in
open OMA.S_oeis_a267260 CAOEISA267260Aux in
theorem OMA.solution : type_of% @OMA.S_oeis_a267260.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    rcases Nat.lt_or_ge n 6 with h | h
    · interval_cases n
      · rw [av4]
        norm_num
      · rw [av5]
        norm_num
    · rw [a_eq n h]
      ring
  · have hD : (((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X) ^ 2) : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C (-1) * PowerSeries.X ^ 1 + PowerSeries.C (-2) * PowerSeries.X ^ 2 + PowerSeries.C 2 * PowerSeries.X ^ 3 + PowerSeries.C 1 * PowerSeries.X ^ 4 + PowerSeries.C (-1) * PowerSeries.X ^ 5 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    have hN : ((1 + 2 * PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.X ^ 3 - PowerSeries.X ^ 5 - PowerSeries.X ^ 6 + 2 * PowerSeries.X ^ 7 - PowerSeries.X ^ 8) : PowerSeries ℚ) =
        PowerSeries.C 1 * PowerSeries.X ^ 0 + PowerSeries.C 2 * PowerSeries.X ^ 1 + PowerSeries.C 1 * PowerSeries.X ^ 2 + PowerSeries.C 1 * PowerSeries.X ^ 3 + PowerSeries.C (-1) * PowerSeries.X ^ 5 + PowerSeries.C (-1) * PowerSeries.X ^ 6 + PowerSeries.C 2 * PowerSeries.X ^ 7 + PowerSeries.C (-1) * PowerSeries.X ^ 8 := by
      simp only [map_one, map_ofNat, map_neg]
      ring
    rw [hD, hN]
    ext n
    simp only [mul_add, map_add, coeff_term, PowerSeries.coeff_C_mul_X_pow]
    rcases Nat.lt_or_ge n 11 with h | h
    · interval_cases n
      · norm_num [av0]
      · norm_num [av0, av1]
      · norm_num [av0, av1, av2]
      · norm_num [av0, av1, av2, av3]
      · norm_num [av0, av1, av2, av3, av4]
      · norm_num [av0, av1, av2, av3, av4, av5]
      · norm_num [av1, av2, av3, av4, av5, av6]
      · norm_num [av2, av3, av4, av5, av6, av7]
      · norm_num [av3, av4, av5, av6, av7, av8]
      · norm_num [av4, av5, av6, av7, av8, av9]
      · norm_num [av5, av6, av7, av8, av9, av10]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 11 := ⟨n - 11, by omega⟩
      rw [if_pos (show 0 ≤ m + 11 from by omega), if_pos (show 1 ≤ m + 11 from by omega), if_pos (show 2 ≤ m + 11 from by omega), if_pos (show 3 ≤ m + 11 from by omega), if_pos (show 4 ≤ m + 11 from by omega), if_pos (show 5 ≤ m + 11 from by omega)]
      rw [if_neg (show ¬ (m + 11 = 0) from by omega), if_neg (show ¬ (m + 11 = 1) from by omega), if_neg (show ¬ (m + 11 = 2) from by omega), if_neg (show ¬ (m + 11 = 3) from by omega), if_neg (show ¬ (m + 11 = 5) from by omega), if_neg (show ¬ (m + 11 = 6) from by omega), if_neg (show ¬ (m + 11 = 7) from by omega), if_neg (show ¬ (m + 11 = 8) from by omega)]
      rw [show m + 11 - 0 = m + 11 from by omega, show m + 11 - 1 = m + 10 from by omega, show m + 11 - 2 = m + 9 from by omega, show m + 11 - 3 = m + 8 from by omega, show m + 11 - 4 = m + 7 from by omega, show m + 11 - 5 = m + 6 from by omega]
      rw [a_eq (m + 11) (by omega), a_eq (m + 10) (by omega), a_eq (m + 9) (by omega), a_eq (m + 8) (by omega), a_eq (m + 7) (by omega), a_eq (m + 6) (by omega)]
      push_cast
      ring
