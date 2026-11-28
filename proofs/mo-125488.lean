import OMAStatements.S_mo_125488
import Mathlib

open OMA.S_mo_125488

def mo125488_adjB (p q : Fin 4 × Fin 4) : Bool :=
  (p.1 == q.1 && ((p.2 : ℕ) + 1 == (q.2 : ℕ) || (q.2 : ℕ) + 1 == (p.2 : ℕ))) ||
    (p.2 == q.2 && ((p.1 : ℕ) + 1 == (q.1 : ℕ) || (q.1 : ℕ) + 1 == (p.1 : ℕ)))

def mo125488_vc (a : Fin 16 → Fin 4 × Fin 4) : ℕ :=
  (Finset.univ.filter (fun k : Fin 16 => (a k).1 ≠ (a (k + 1)).1)).card

def mo125488_hc (a : Fin 16 → Fin 4 × Fin 4) : ℕ :=
  (Finset.univ.filter (fun k : Fin 16 => (a k).2 ≠ (a (k + 1)).2)).card

lemma mo125488_adj_imp (p q : Fin 4 × Fin 4) (h : Adj p q) : mo125488_adjB p q = true := by
  unfold Adj at h
  unfold mo125488_adjB
  rcases h with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩ <;> simp [h1, h2]

def mo125488_cells : List (Fin 4 × Fin 4) := [(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3), (3, 0), (3, 1), (3, 2), (3, 3)]

lemma mo125488_mem (x : Fin 4 × Fin 4) : x ∈ mo125488_cells := by
  revert x; decide

def mo125488_L15 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 : Fin 4 × Fin 4) : Bool :=
  mo125488_cells.all (fun a15 => !(mo125488_adjB a14 a15 && decide (a15 ≠ a0) && decide (a15 ≠ a1) && decide (a15 ≠ a2) && decide (a15 ≠ a3) && decide (a15 ≠ a4) && decide (a15 ≠ a5) && decide (a15 ≠ a6) && decide (a15 ≠ a7) && decide (a15 ≠ a8) && decide (a15 ≠ a9) && decide (a15 ≠ a10) && decide (a15 ≠ a11) && decide (a15 ≠ a12) && decide (a15 ≠ a13) && decide (a15 ≠ a14)) || (!(mo125488_adjB a15 a0) || decide (mo125488_vc ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] ≠ mo125488_hc ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15])))

def mo125488_L14 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : Fin 4 × Fin 4) : Bool :=
  mo125488_cells.all (fun a14 => !(mo125488_adjB a13 a14 && decide (a14 ≠ a0) && decide (a14 ≠ a1) && decide (a14 ≠ a2) && decide (a14 ≠ a3) && decide (a14 ≠ a4) && decide (a14 ≠ a5) && decide (a14 ≠ a6) && decide (a14 ≠ a7) && decide (a14 ≠ a8) && decide (a14 ≠ a9) && decide (a14 ≠ a10) && decide (a14 ≠ a11) && decide (a14 ≠ a12) && decide (a14 ≠ a13)) || mo125488_L15 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14)

def mo125488_L13 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : Fin 4 × Fin 4) : Bool :=
  mo125488_cells.all (fun a13 => !(mo125488_adjB a12 a13 && decide (a13 ≠ a0) && decide (a13 ≠ a1) && decide (a13 ≠ a2) && decide (a13 ≠ a3) && decide (a13 ≠ a4) && decide (a13 ≠ a5) && decide (a13 ≠ a6) && decide (a13 ≠ a7) && decide (a13 ≠ a8) && decide (a13 ≠ a9) && decide (a13 ≠ a10) && decide (a13 ≠ a11) && decide (a13 ≠ a12)) || mo125488_L14 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13)

def mo125488_L12 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : Fin 4 × Fin 4) : Bool :=
  mo125488_cells.all (fun a12 => !(mo125488_adjB a11 a12 && decide (a12 ≠ a0) && decide (a12 ≠ a1) && decide (a12 ≠ a2) && decide (a12 ≠ a3) && decide (a12 ≠ a4) && decide (a12 ≠ a5) && decide (a12 ≠ a6) && decide (a12 ≠ a7) && decide (a12 ≠ a8) && decide (a12 ≠ a9) && decide (a12 ≠ a10) && decide (a12 ≠ a11)) || mo125488_L13 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12)

def mo125488_L11 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Fin 4 × Fin 4) : Bool :=
  mo125488_cells.all (fun a11 => !(mo125488_adjB a10 a11 && decide (a11 ≠ a0) && decide (a11 ≠ a1) && decide (a11 ≠ a2) && decide (a11 ≠ a3) && decide (a11 ≠ a4) && decide (a11 ≠ a5) && decide (a11 ≠ a6) && decide (a11 ≠ a7) && decide (a11 ≠ a8) && decide (a11 ≠ a9) && decide (a11 ≠ a10)) || mo125488_L12 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11)

def mo125488_L10 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Fin 4 × Fin 4) : Bool :=
  mo125488_cells.all (fun a10 => !(mo125488_adjB a9 a10 && decide (a10 ≠ a0) && decide (a10 ≠ a1) && decide (a10 ≠ a2) && decide (a10 ≠ a3) && decide (a10 ≠ a4) && decide (a10 ≠ a5) && decide (a10 ≠ a6) && decide (a10 ≠ a7) && decide (a10 ≠ a8) && decide (a10 ≠ a9)) || mo125488_L11 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10)

def mo125488_L9 (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Fin 4 × Fin 4) : Bool :=
  mo125488_cells.all (fun a9 => !(mo125488_adjB a8 a9 && decide (a9 ≠ a0) && decide (a9 ≠ a1) && decide (a9 ≠ a2) && decide (a9 ≠ a3) && decide (a9 ≠ a4) && decide (a9 ≠ a5) && decide (a9 ≠ a6) && decide (a9 ≠ a7) && decide (a9 ≠ a8)) || mo125488_L10 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9)

def mo125488_L8 (a0 a1 a2 a3 a4 a5 a6 a7 : Fin 4 × Fin 4) : Bool :=
  mo125488_cells.all (fun a8 => !(mo125488_adjB a7 a8 && decide (a8 ≠ a0) && decide (a8 ≠ a1) && decide (a8 ≠ a2) && decide (a8 ≠ a3) && decide (a8 ≠ a4) && decide (a8 ≠ a5) && decide (a8 ≠ a6) && decide (a8 ≠ a7)) || mo125488_L9 a0 a1 a2 a3 a4 a5 a6 a7 a8)

def mo125488_L7 (a0 a1 a2 a3 a4 a5 a6 : Fin 4 × Fin 4) : Bool :=
  mo125488_cells.all (fun a7 => !(mo125488_adjB a6 a7 && decide (a7 ≠ a0) && decide (a7 ≠ a1) && decide (a7 ≠ a2) && decide (a7 ≠ a3) && decide (a7 ≠ a4) && decide (a7 ≠ a5) && decide (a7 ≠ a6)) || mo125488_L8 a0 a1 a2 a3 a4 a5 a6 a7)

def mo125488_L6 (a0 a1 a2 a3 a4 a5 : Fin 4 × Fin 4) : Bool :=
  mo125488_cells.all (fun a6 => !(mo125488_adjB a5 a6 && decide (a6 ≠ a0) && decide (a6 ≠ a1) && decide (a6 ≠ a2) && decide (a6 ≠ a3) && decide (a6 ≠ a4) && decide (a6 ≠ a5)) || mo125488_L7 a0 a1 a2 a3 a4 a5 a6)

def mo125488_L5 (a0 a1 a2 a3 a4 : Fin 4 × Fin 4) : Bool :=
  mo125488_cells.all (fun a5 => !(mo125488_adjB a4 a5 && decide (a5 ≠ a0) && decide (a5 ≠ a1) && decide (a5 ≠ a2) && decide (a5 ≠ a3) && decide (a5 ≠ a4)) || mo125488_L6 a0 a1 a2 a3 a4 a5)

def mo125488_L4 (a0 a1 a2 a3 : Fin 4 × Fin 4) : Bool :=
  mo125488_cells.all (fun a4 => !(mo125488_adjB a3 a4 && decide (a4 ≠ a0) && decide (a4 ≠ a1) && decide (a4 ≠ a2) && decide (a4 ≠ a3)) || mo125488_L5 a0 a1 a2 a3 a4)

def mo125488_L3 (a0 a1 a2 : Fin 4 × Fin 4) : Bool :=
  mo125488_cells.all (fun a3 => !(mo125488_adjB a2 a3 && decide (a3 ≠ a0) && decide (a3 ≠ a1) && decide (a3 ≠ a2)) || mo125488_L4 a0 a1 a2 a3)

def mo125488_L2 (a0 a1 : Fin 4 × Fin 4) : Bool :=
  mo125488_cells.all (fun a2 => !(mo125488_adjB a1 a2 && decide (a2 ≠ a0) && decide (a2 ≠ a1)) || mo125488_L3 a0 a1 a2)

def mo125488_L1 (a0 : Fin 4 × Fin 4) : Bool :=
  mo125488_cells.all (fun a1 => !(mo125488_adjB a0 a1 && decide (a1 ≠ a0)) || mo125488_L2 a0 a1)

lemma mo125488_S1 (a0 : Fin 4 × Fin 4) (h : mo125488_L1 a0 = true)
    (a1 : Fin 4 × Fin 4) (hA : mo125488_adjB a0 a1 = true) (h0 : a1 ≠ a0) :
    mo125488_L2 a0 a1 = true := by
  unfold mo125488_L1 at h
  rw [List.all_eq_true] at h
  have hh := h a1 (mo125488_mem a1)
  simp only [hA, h0, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo125488_S2 (a0 a1 : Fin 4 × Fin 4) (h : mo125488_L2 a0 a1 = true)
    (a2 : Fin 4 × Fin 4) (hA : mo125488_adjB a1 a2 = true) (h0 : a2 ≠ a0) (h1 : a2 ≠ a1) :
    mo125488_L3 a0 a1 a2 = true := by
  unfold mo125488_L2 at h
  rw [List.all_eq_true] at h
  have hh := h a2 (mo125488_mem a2)
  simp only [hA, h0, h1, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo125488_S3 (a0 a1 a2 : Fin 4 × Fin 4) (h : mo125488_L3 a0 a1 a2 = true)
    (a3 : Fin 4 × Fin 4) (hA : mo125488_adjB a2 a3 = true) (h0 : a3 ≠ a0) (h1 : a3 ≠ a1) (h2 : a3 ≠ a2) :
    mo125488_L4 a0 a1 a2 a3 = true := by
  unfold mo125488_L3 at h
  rw [List.all_eq_true] at h
  have hh := h a3 (mo125488_mem a3)
  simp only [hA, h0, h1, h2, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo125488_S4 (a0 a1 a2 a3 : Fin 4 × Fin 4) (h : mo125488_L4 a0 a1 a2 a3 = true)
    (a4 : Fin 4 × Fin 4) (hA : mo125488_adjB a3 a4 = true) (h0 : a4 ≠ a0) (h1 : a4 ≠ a1) (h2 : a4 ≠ a2) (h3 : a4 ≠ a3) :
    mo125488_L5 a0 a1 a2 a3 a4 = true := by
  unfold mo125488_L4 at h
  rw [List.all_eq_true] at h
  have hh := h a4 (mo125488_mem a4)
  simp only [hA, h0, h1, h2, h3, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo125488_S5 (a0 a1 a2 a3 a4 : Fin 4 × Fin 4) (h : mo125488_L5 a0 a1 a2 a3 a4 = true)
    (a5 : Fin 4 × Fin 4) (hA : mo125488_adjB a4 a5 = true) (h0 : a5 ≠ a0) (h1 : a5 ≠ a1) (h2 : a5 ≠ a2) (h3 : a5 ≠ a3) (h4 : a5 ≠ a4) :
    mo125488_L6 a0 a1 a2 a3 a4 a5 = true := by
  unfold mo125488_L5 at h
  rw [List.all_eq_true] at h
  have hh := h a5 (mo125488_mem a5)
  simp only [hA, h0, h1, h2, h3, h4, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo125488_S6 (a0 a1 a2 a3 a4 a5 : Fin 4 × Fin 4) (h : mo125488_L6 a0 a1 a2 a3 a4 a5 = true)
    (a6 : Fin 4 × Fin 4) (hA : mo125488_adjB a5 a6 = true) (h0 : a6 ≠ a0) (h1 : a6 ≠ a1) (h2 : a6 ≠ a2) (h3 : a6 ≠ a3) (h4 : a6 ≠ a4) (h5 : a6 ≠ a5) :
    mo125488_L7 a0 a1 a2 a3 a4 a5 a6 = true := by
  unfold mo125488_L6 at h
  rw [List.all_eq_true] at h
  have hh := h a6 (mo125488_mem a6)
  simp only [hA, h0, h1, h2, h3, h4, h5, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo125488_S7 (a0 a1 a2 a3 a4 a5 a6 : Fin 4 × Fin 4) (h : mo125488_L7 a0 a1 a2 a3 a4 a5 a6 = true)
    (a7 : Fin 4 × Fin 4) (hA : mo125488_adjB a6 a7 = true) (h0 : a7 ≠ a0) (h1 : a7 ≠ a1) (h2 : a7 ≠ a2) (h3 : a7 ≠ a3) (h4 : a7 ≠ a4) (h5 : a7 ≠ a5) (h6 : a7 ≠ a6) :
    mo125488_L8 a0 a1 a2 a3 a4 a5 a6 a7 = true := by
  unfold mo125488_L7 at h
  rw [List.all_eq_true] at h
  have hh := h a7 (mo125488_mem a7)
  simp only [hA, h0, h1, h2, h3, h4, h5, h6, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo125488_S8 (a0 a1 a2 a3 a4 a5 a6 a7 : Fin 4 × Fin 4) (h : mo125488_L8 a0 a1 a2 a3 a4 a5 a6 a7 = true)
    (a8 : Fin 4 × Fin 4) (hA : mo125488_adjB a7 a8 = true) (h0 : a8 ≠ a0) (h1 : a8 ≠ a1) (h2 : a8 ≠ a2) (h3 : a8 ≠ a3) (h4 : a8 ≠ a4) (h5 : a8 ≠ a5) (h6 : a8 ≠ a6) (h7 : a8 ≠ a7) :
    mo125488_L9 a0 a1 a2 a3 a4 a5 a6 a7 a8 = true := by
  unfold mo125488_L8 at h
  rw [List.all_eq_true] at h
  have hh := h a8 (mo125488_mem a8)
  simp only [hA, h0, h1, h2, h3, h4, h5, h6, h7, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo125488_S9 (a0 a1 a2 a3 a4 a5 a6 a7 a8 : Fin 4 × Fin 4) (h : mo125488_L9 a0 a1 a2 a3 a4 a5 a6 a7 a8 = true)
    (a9 : Fin 4 × Fin 4) (hA : mo125488_adjB a8 a9 = true) (h0 : a9 ≠ a0) (h1 : a9 ≠ a1) (h2 : a9 ≠ a2) (h3 : a9 ≠ a3) (h4 : a9 ≠ a4) (h5 : a9 ≠ a5) (h6 : a9 ≠ a6) (h7 : a9 ≠ a7) (h8 : a9 ≠ a8) :
    mo125488_L10 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = true := by
  unfold mo125488_L9 at h
  rw [List.all_eq_true] at h
  have hh := h a9 (mo125488_mem a9)
  simp only [hA, h0, h1, h2, h3, h4, h5, h6, h7, h8, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo125488_S10 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Fin 4 × Fin 4) (h : mo125488_L10 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = true)
    (a10 : Fin 4 × Fin 4) (hA : mo125488_adjB a9 a10 = true) (h0 : a10 ≠ a0) (h1 : a10 ≠ a1) (h2 : a10 ≠ a2) (h3 : a10 ≠ a3) (h4 : a10 ≠ a4) (h5 : a10 ≠ a5) (h6 : a10 ≠ a6) (h7 : a10 ≠ a7) (h8 : a10 ≠ a8) (h9 : a10 ≠ a9) :
    mo125488_L11 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = true := by
  unfold mo125488_L10 at h
  rw [List.all_eq_true] at h
  have hh := h a10 (mo125488_mem a10)
  simp only [hA, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo125488_S11 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : Fin 4 × Fin 4) (h : mo125488_L11 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = true)
    (a11 : Fin 4 × Fin 4) (hA : mo125488_adjB a10 a11 = true) (h0 : a11 ≠ a0) (h1 : a11 ≠ a1) (h2 : a11 ≠ a2) (h3 : a11 ≠ a3) (h4 : a11 ≠ a4) (h5 : a11 ≠ a5) (h6 : a11 ≠ a6) (h7 : a11 ≠ a7) (h8 : a11 ≠ a8) (h9 : a11 ≠ a9) (h10 : a11 ≠ a10) :
    mo125488_L12 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = true := by
  unfold mo125488_L11 at h
  rw [List.all_eq_true] at h
  have hh := h a11 (mo125488_mem a11)
  simp only [hA, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo125488_S12 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : Fin 4 × Fin 4) (h : mo125488_L12 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = true)
    (a12 : Fin 4 × Fin 4) (hA : mo125488_adjB a11 a12 = true) (h0 : a12 ≠ a0) (h1 : a12 ≠ a1) (h2 : a12 ≠ a2) (h3 : a12 ≠ a3) (h4 : a12 ≠ a4) (h5 : a12 ≠ a5) (h6 : a12 ≠ a6) (h7 : a12 ≠ a7) (h8 : a12 ≠ a8) (h9 : a12 ≠ a9) (h10 : a12 ≠ a10) (h11 : a12 ≠ a11) :
    mo125488_L13 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = true := by
  unfold mo125488_L12 at h
  rw [List.all_eq_true] at h
  have hh := h a12 (mo125488_mem a12)
  simp only [hA, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo125488_S13 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 : Fin 4 × Fin 4) (h : mo125488_L13 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = true)
    (a13 : Fin 4 × Fin 4) (hA : mo125488_adjB a12 a13 = true) (h0 : a13 ≠ a0) (h1 : a13 ≠ a1) (h2 : a13 ≠ a2) (h3 : a13 ≠ a3) (h4 : a13 ≠ a4) (h5 : a13 ≠ a5) (h6 : a13 ≠ a6) (h7 : a13 ≠ a7) (h8 : a13 ≠ a8) (h9 : a13 ≠ a9) (h10 : a13 ≠ a10) (h11 : a13 ≠ a11) (h12 : a13 ≠ a12) :
    mo125488_L14 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 = true := by
  unfold mo125488_L13 at h
  rw [List.all_eq_true] at h
  have hh := h a13 (mo125488_mem a13)
  simp only [hA, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo125488_S14 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 : Fin 4 × Fin 4) (h : mo125488_L14 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 = true)
    (a14 : Fin 4 × Fin 4) (hA : mo125488_adjB a13 a14 = true) (h0 : a14 ≠ a0) (h1 : a14 ≠ a1) (h2 : a14 ≠ a2) (h3 : a14 ≠ a3) (h4 : a14 ≠ a4) (h5 : a14 ≠ a5) (h6 : a14 ≠ a6) (h7 : a14 ≠ a7) (h8 : a14 ≠ a8) (h9 : a14 ≠ a9) (h10 : a14 ≠ a10) (h11 : a14 ≠ a11) (h12 : a14 ≠ a12) (h13 : a14 ≠ a13) :
    mo125488_L15 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 = true := by
  unfold mo125488_L14 at h
  rw [List.all_eq_true] at h
  have hh := h a14 (mo125488_mem a14)
  simp only [hA, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  exact hh

lemma mo125488_S15 (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 : Fin 4 × Fin 4) (h : mo125488_L15 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 = true)
    (a15 : Fin 4 × Fin 4) (hA : mo125488_adjB a14 a15 = true) (h0 : a15 ≠ a0) (h1 : a15 ≠ a1) (h2 : a15 ≠ a2) (h3 : a15 ≠ a3) (h4 : a15 ≠ a4) (h5 : a15 ≠ a5) (h6 : a15 ≠ a6) (h7 : a15 ≠ a7) (h8 : a15 ≠ a8) (h9 : a15 ≠ a9) (h10 : a15 ≠ a10) (h11 : a15 ≠ a11) (h12 : a15 ≠ a12) (h13 : a15 ≠ a13) (h14 : a15 ≠ a14) :
    mo125488_adjB a15 a0 = true → mo125488_vc ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] ≠ mo125488_hc ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] := by
  unfold mo125488_L15 at h
  rw [List.all_eq_true] at h
  have hh := h a15 (mo125488_mem a15)
  simp only [hA, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, ne_eq, not_false_eq_true, decide_true, Bool.and_true, Bool.not_true, Bool.false_or] at hh
  intro hl
  simp only [hl, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hh
  exact hh

lemma mo125488_top : mo125488_L1 (0, 0) = true := by decide +kernel

theorem mo125488_no (c : Fin 16 → Fin 4 × Fin 4) (hbij : Function.Bijective c)
    (hadj : ∀ i, Adj (c i) (c (finRotate 16 i)))
    (hbal : (Finset.univ.filter (fun i => (c i).1 ≠ (c (finRotate 16 i)).1)).card =
      (Finset.univ.filter (fun i => (c i).2 ≠ (c (finRotate 16 i)).2)).card) : False := by
  obtain ⟨j, hj⟩ := hbij.2 (0, 0)
  have hrot : ∀ i : Fin 16, finRotate 16 i = i + 1 := fun i => finRotate_apply i
  set a : Fin 16 → Fin 4 × Fin 4 := fun k => c (j + k) with ha_def
  have ha : ∀ k : Fin 16, mo125488_adjB (a k) (a (k + 1)) = true := by
    intro k
    apply mo125488_adj_imp
    have := hadj (j + k)
    rw [hrot, add_assoc] at this
    exact this
  have hinj : ∀ p q : Fin 16, p ≠ q → a p ≠ a q :=
    fun p q hpq h => hpq (add_left_cancel (hbij.1 h))
  have h00 : a 0 = (0, 0) := by simp [a, hj]
  have hvc : (Finset.univ.filter (fun i => (c i).1 ≠ (c (finRotate 16 i)).1)).card =
      mo125488_vc a := by
    simp only [hrot, mo125488_vc, Finset.card_filter]
    rw [← Equiv.sum_comp (Equiv.addLeft j)]
    simp [a, add_assoc]
  have hhc : (Finset.univ.filter (fun i => (c i).2 ≠ (c (finRotate 16 i)).2)).card =
      mo125488_hc a := by
    simp only [hrot, mo125488_hc, Finset.card_filter]
    rw [← Equiv.sum_comp (Equiv.addLeft j)]
    simp [a, add_assoc]
  have hfun : a = ![a 0, a 1, a 2, a 3, a 4, a 5, a 6, a 7, a 8, a 9, a 10, a 11, a 12, a 13, a 14, a 15] := by
    funext k
    fin_cases k <;> rfl
  have t1 : mo125488_L1 (a 0) = true := by rw [h00]; exact mo125488_top
  have t2 := mo125488_S1 (a 0) t1 (a 1) (ha 0) (hinj 1 0 (by decide))
  have t3 := mo125488_S2 (a 0) (a 1) t2 (a 2) (ha 1) (hinj 2 0 (by decide)) (hinj 2 1 (by decide))
  have t4 := mo125488_S3 (a 0) (a 1) (a 2) t3 (a 3) (ha 2) (hinj 3 0 (by decide)) (hinj 3 1 (by decide)) (hinj 3 2 (by decide))
  have t5 := mo125488_S4 (a 0) (a 1) (a 2) (a 3) t4 (a 4) (ha 3) (hinj 4 0 (by decide)) (hinj 4 1 (by decide)) (hinj 4 2 (by decide)) (hinj 4 3 (by decide))
  have t6 := mo125488_S5 (a 0) (a 1) (a 2) (a 3) (a 4) t5 (a 5) (ha 4) (hinj 5 0 (by decide)) (hinj 5 1 (by decide)) (hinj 5 2 (by decide)) (hinj 5 3 (by decide)) (hinj 5 4 (by decide))
  have t7 := mo125488_S6 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) t6 (a 6) (ha 5) (hinj 6 0 (by decide)) (hinj 6 1 (by decide)) (hinj 6 2 (by decide)) (hinj 6 3 (by decide)) (hinj 6 4 (by decide)) (hinj 6 5 (by decide))
  have t8 := mo125488_S7 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) t7 (a 7) (ha 6) (hinj 7 0 (by decide)) (hinj 7 1 (by decide)) (hinj 7 2 (by decide)) (hinj 7 3 (by decide)) (hinj 7 4 (by decide)) (hinj 7 5 (by decide)) (hinj 7 6 (by decide))
  have t9 := mo125488_S8 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) t8 (a 8) (ha 7) (hinj 8 0 (by decide)) (hinj 8 1 (by decide)) (hinj 8 2 (by decide)) (hinj 8 3 (by decide)) (hinj 8 4 (by decide)) (hinj 8 5 (by decide)) (hinj 8 6 (by decide)) (hinj 8 7 (by decide))
  have t10 := mo125488_S9 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) t9 (a 9) (ha 8) (hinj 9 0 (by decide)) (hinj 9 1 (by decide)) (hinj 9 2 (by decide)) (hinj 9 3 (by decide)) (hinj 9 4 (by decide)) (hinj 9 5 (by decide)) (hinj 9 6 (by decide)) (hinj 9 7 (by decide)) (hinj 9 8 (by decide))
  have t11 := mo125488_S10 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) t10 (a 10) (ha 9) (hinj 10 0 (by decide)) (hinj 10 1 (by decide)) (hinj 10 2 (by decide)) (hinj 10 3 (by decide)) (hinj 10 4 (by decide)) (hinj 10 5 (by decide)) (hinj 10 6 (by decide)) (hinj 10 7 (by decide)) (hinj 10 8 (by decide)) (hinj 10 9 (by decide))
  have t12 := mo125488_S11 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) t11 (a 11) (ha 10) (hinj 11 0 (by decide)) (hinj 11 1 (by decide)) (hinj 11 2 (by decide)) (hinj 11 3 (by decide)) (hinj 11 4 (by decide)) (hinj 11 5 (by decide)) (hinj 11 6 (by decide)) (hinj 11 7 (by decide)) (hinj 11 8 (by decide)) (hinj 11 9 (by decide)) (hinj 11 10 (by decide))
  have t13 := mo125488_S12 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) t12 (a 12) (ha 11) (hinj 12 0 (by decide)) (hinj 12 1 (by decide)) (hinj 12 2 (by decide)) (hinj 12 3 (by decide)) (hinj 12 4 (by decide)) (hinj 12 5 (by decide)) (hinj 12 6 (by decide)) (hinj 12 7 (by decide)) (hinj 12 8 (by decide)) (hinj 12 9 (by decide)) (hinj 12 10 (by decide)) (hinj 12 11 (by decide))
  have t14 := mo125488_S13 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) t13 (a 13) (ha 12) (hinj 13 0 (by decide)) (hinj 13 1 (by decide)) (hinj 13 2 (by decide)) (hinj 13 3 (by decide)) (hinj 13 4 (by decide)) (hinj 13 5 (by decide)) (hinj 13 6 (by decide)) (hinj 13 7 (by decide)) (hinj 13 8 (by decide)) (hinj 13 9 (by decide)) (hinj 13 10 (by decide)) (hinj 13 11 (by decide)) (hinj 13 12 (by decide))
  have t15 := mo125488_S14 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) t14 (a 14) (ha 13) (hinj 14 0 (by decide)) (hinj 14 1 (by decide)) (hinj 14 2 (by decide)) (hinj 14 3 (by decide)) (hinj 14 4 (by decide)) (hinj 14 5 (by decide)) (hinj 14 6 (by decide)) (hinj 14 7 (by decide)) (hinj 14 8 (by decide)) (hinj 14 9 (by decide)) (hinj 14 10 (by decide)) (hinj 14 11 (by decide)) (hinj 14 12 (by decide)) (hinj 14 13 (by decide))
  have key := mo125488_S15 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9) (a 10) (a 11) (a 12) (a 13) (a 14) t15 (a 15) (ha 14) (hinj 15 0 (by decide)) (hinj 15 1 (by decide)) (hinj 15 2 (by decide)) (hinj 15 3 (by decide)) (hinj 15 4 (by decide)) (hinj 15 5 (by decide)) (hinj 15 6 (by decide)) (hinj 15 7 (by decide)) (hinj 15 8 (by decide)) (hinj 15 9 (by decide)) (hinj 15 10 (by decide)) (hinj 15 11 (by decide)) (hinj 15 12 (by decide)) (hinj 15 13 (by decide)) (hinj 15 14 (by decide)) (ha 15)
  rw [← hfun] at key
  exact key (hvc.symm.trans (hbal.trans hhc))

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_125488.main) := by
  intro h
  obtain ⟨c, ⟨hbij, hadj⟩, hbal⟩ := h 2 (by norm_num) (by decide)
  exact mo125488_no c hbij hadj hbal
