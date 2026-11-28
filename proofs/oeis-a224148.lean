import OMAStatements.S_oeis_a224148
import Mathlib

/-!
Proof of the empirical formula and Barker's conjectures for OEIS A224148
(Number of 4 X n 0..1 arrays with rows and antidiagonals unimodal and columns nondecreasing.).

Outline.
1. Generic part (namespace UG, proved for any number of rows): the array is read column by column.
   A line (row, diagonal or antidiagonal) is unimodal iff it has no valley; appending a column
   keeps every line valley-free iff no line that has already strictly descended rises again at the
   new cell (`UC_snoc`), and the descent flags update locally (`DS_snoc`). The state after a column
   is coded as a natural number (the column in base m plus one flag bit per line ending there), and
   the computable transition `okc`/`dc` is shown to match the semantics (`okc_stS`, `dc_stS`). This
   gives a(n + 1) as a sum of continuation counts `Wc n` over the admissible first columns
   (`count_eq`).
2. Certificate (checked by the kernel, `decide +kernel`): the list of the 38 reachable states,
   their successor lists, a lumping of the states into 11 blocks with equal continuation counts,
   and the block tables up to length 11. From them, the pointwise identity
   Sum_i (-1)^i C(9, i) Wc (n + 9 - i) s = 0 for n >= 0 and every reachable s, hence the
   binomial recurrence for a(n), n >= 10.
3. The recurrence, the polynomial and the generating function follow from the recurrence and
   the computed values a(1), ..., a(12).
-/

namespace UG

open Finset

/-- Cells (i1, j1) and (i2, j2) (row, column) lie on a common line of type t:
0 a row, 1 a diagonal (i - j constant), 2 an antidiagonal (i + j constant). -/
def al (t i1 j1 i2 j2 : ℕ) : Prop :=
  (t = 0 ∧ i1 = i2) ∨ (t = 1 ∧ i1 + j2 = i2 + j1) ∨ (t = 2 ∧ i1 + j1 = i2 + j2)

instance (t i1 j1 i2 j2 : ℕ) : Decidable (al t i1 j1 i2 j2) := by unfold al; infer_instance

/-- The cell (i, j + 1) continues the line of type t through (p, j). -/
def PR (t i p : ℕ) : Prop := (t = 0 ∧ p = i) ∨ (t = 1 ∧ p + 1 = i) ∨ (t = 2 ∧ p = i + 1)

section Sem

variable {R m : ℕ}

/-- No valley along the lines of type t (arrays given by their columns). -/
def UC (t : ℕ) {N : ℕ} (y : Fin N → Fin R → Fin m) : Prop :=
  ∀ j1 j2 j3 : Fin N, ∀ i1 i2 i3 : Fin R, j1 < j2 → j2 < j3 →
    al t i1 j1 i3 j3 → al t i2 j2 i3 j3 → ¬ (y j2 i2 < y j1 i1 ∧ y j2 i2 < y j3 i3)

/-- Rows nondecreasing. -/
def RN {N : ℕ} (y : Fin N → Fin R → Fin m) : Prop :=
  ∀ j1 j2 : Fin N, j1 ≤ j2 → ∀ i, y j1 i ≤ y j2 i

/-- The line of type t through the cell (p, N) of the last column has a strict descent. -/
def DS (t : ℕ) {N : ℕ} (y : Fin (N + 1) → Fin R → Fin m) (p : ℕ) : Prop :=
  ∃ j1 j2 : Fin (N + 1), ∃ i1 i2 : Fin R, j1 < j2 ∧ al t i1 j1 p N ∧ al t i2 j2 p N ∧
    y j2 i2 < y j1 i1

instance (t : ℕ) {N : ℕ} (y : Fin (N + 1) → Fin R → Fin m) (p : ℕ) : Decidable (DS t y p) := by
  unfold DS; infer_instance

lemma al_last {t p N : ℕ} {i2 : ℕ} (ht : t < 3) (h : al t i2 N p N) : i2 = p := by
  unfold al at h; omega

lemma al_pred {t i1 j1 i N : ℕ} (ht : t < 3) (hj : j1 ≤ N) (h : al t i1 j1 i (N + 1)) :
    ∃ p, PR t i p ∧ al t i1 j1 p N := by
  unfold al at h; unfold PR al
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact ⟨i, by omega, by omega⟩
  · exact ⟨i - 1, by omega, by omega⟩
  · exact ⟨i + 1, by omega, by omega⟩

lemma al_pred_bound {t i1 j1 i N p R : ℕ} (hi1 : i1 < R) (hi : i < R) (hj : j1 ≤ N)
    (hp : PR t i p) (h : al t i1 j1 p N) : p < R := by
  unfold PR at hp; unfold al at h; omega

lemma al_succ {t i1 j1 i N p : ℕ} (hp : PR t i p) (h : al t i1 j1 p N) : al t i1 j1 i (N + 1) := by
  unfold PR at hp; unfold al at h ⊢; omega

lemma al_self_succ {t i N p : ℕ} (hp : PR t i p) : al t p N i (N + 1) := by
  unfold PR at hp; unfold al; omega

lemma al_refl (t i N : ℕ) (ht : t < 3) : al t i N i N := by unfold al; omega

theorem UC_snoc (t : ℕ) (ht : t < 3) {N : ℕ} (y : Fin (N + 1) → Fin R → Fin m) (c : Fin R → Fin m) :
    UC t (Fin.snoc y c : Fin (N + 2) → Fin R → Fin m) ↔
      UC t y ∧ ∀ i p : Fin R, PR t i p → ¬ (DS t y p ∧ y (Fin.last N) p < c i) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro j1 j2 j3 i1 i2 i3 h12 h23 a1 a2
      have := h j1.castSucc j2.castSucc j3.castSucc i1 i2 i3 (by simpa using h12)
        (by simpa using h23) (by simpa using a1) (by simpa using a2)
      simpa using this
    · rintro i p hp ⟨⟨j1, j2, i1, i2, h12, a1, a2, hv⟩, hc⟩
      by_cases hj2 : (j2 : ℕ) = N
      · have hi2 : (i2 : ℕ) = p := al_last ht (hj2 ▸ a2)
        have e2 : j2 = Fin.last N := Fin.ext hj2
        have e3 : i2 = p := Fin.ext hi2
        subst e2 e3
        apply h j1.castSucc (Fin.last N).castSucc (Fin.last (N + 1)) i1 i2 i
          (Fin.castSucc_lt_castSucc_iff.2 h12) (Fin.castSucc_lt_last _) (by simpa using al_succ hp a1)
          (by simpa using al_self_succ (N := N) hp)
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        exact ⟨hv, hc⟩
      · have hj2' : (j2 : ℕ) < N := by have := j2.isLt; omega
        by_cases hlt : y (Fin.last N) p < y j2 i2
        · apply h j2.castSucc (Fin.last N).castSucc (Fin.last (N + 1)) i2 p i
            (by rw [Fin.lt_iff_val_lt_val]; simp only [Fin.coe_castSucc, Fin.val_last]; omega) (Fin.castSucc_lt_last _) (by simpa using al_succ hp a2)
            (by simpa using al_self_succ (N := N) hp)
          simp only [Fin.snoc_castSucc, Fin.snoc_last]
          exact ⟨hlt, hc⟩
        · push_neg at hlt
          apply h j1.castSucc j2.castSucc (Fin.last (N + 1)) i1 i2 i
            (Fin.castSucc_lt_castSucc_iff.2 h12) (Fin.castSucc_lt_last _) (by simpa using al_succ hp a1)
            (by simpa using al_succ hp a2)
          simp only [Fin.snoc_castSucc, Fin.snoc_last]
          exact ⟨hv, lt_of_le_of_lt hlt hc⟩
  · rintro ⟨h, hn⟩ j1 j2 j3 i1 i2 i3 h12 h23 a1 a2
    by_cases hj3 : (j3 : ℕ) = N + 1
    · have e3 : j3 = Fin.last (N + 1) := Fin.ext hj3
      subst e3
      have k12 : (j1 : ℕ) < j2 := h12
      have k23 : (j2 : ℕ) < N + 1 := h23
      have hj1 : (j1 : ℕ) ≤ N := by omega
      have hj2 : (j2 : ℕ) ≤ N := by omega
      obtain ⟨p, hp, ap1⟩ := al_pred ht hj1 (by simpa using a1)
      obtain ⟨p', hp', ap2⟩ := al_pred ht hj2 (by simpa using a2)
      have hpp : p' = p := by unfold PR at hp hp'; omega
      subst hpp
      have hpR : p' < R := al_pred_bound i1.isLt i3.isLt hj1 hp ap1
      let j1' : Fin (N + 1) := ⟨j1, by omega⟩
      let j2' : Fin (N + 1) := ⟨j2, by omega⟩
      have ej1 : j1 = j1'.castSucc := Fin.ext rfl
      have ej2 : j2 = j2'.castSucc := Fin.ext rfl
      rw [ej1, ej2]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      rintro ⟨v1, v2⟩
      have hds : DS t y p' := ⟨j1', j2', i1, i2, show (j1 : ℕ) < j2 from k12,
        ap1, ap2, v1⟩
      have hnot := hn i3 ⟨p', hpR⟩ hp
      have hle : c i3 ≤ y (Fin.last N) ⟨p', hpR⟩ := by
        by_contra hh; push_neg at hh; exact hnot ⟨hds, hh⟩
      by_cases hj2N : (j2 : ℕ) = N
      · have : j2' = Fin.last N := Fin.ext hj2N
        have hi2 : (i2 : ℕ) = p' := al_last ht (by simpa [j2', hj2N] using ap2)
        have : i2 = ⟨p', hpR⟩ := Fin.ext hi2
        subst this
        rw [show j2' = Fin.last N from Fin.ext hj2N] at v2
        exact absurd (lt_of_lt_of_le v2 hle) (lt_irrefl _)
      · apply h j1' j2' (Fin.last N) i1 i2 ⟨p', hpR⟩ (show (j1 : ℕ) < j2 from k12)
          (show (j2 : ℕ) < N by omega) ap1 ap2
        exact ⟨v1, lt_of_lt_of_le v2 hle⟩
    · have hj3' : (j3 : ℕ) < N + 1 := by have := j3.isLt; omega
      have k12 : (j1 : ℕ) < j2 := h12
      have k23 : (j2 : ℕ) < j3 := h23
      let j1' : Fin (N + 1) := ⟨j1, by omega⟩
      let j2' : Fin (N + 1) := ⟨j2, by omega⟩
      let j3' : Fin (N + 1) := ⟨j3, hj3'⟩
      have ej1 : j1 = j1'.castSucc := Fin.ext rfl
      have ej2 : j2 = j2'.castSucc := Fin.ext rfl
      have ej3 : j3 = j3'.castSucc := Fin.ext rfl
      rw [ej1, ej2, ej3]
      simp only [Fin.snoc_castSucc]
      exact h j1' j2' j3' i1 i2 i3 h12 h23 a1 a2

theorem DS_snoc (t : ℕ) (ht : t < 3) {N : ℕ} (y : Fin (N + 1) → Fin R → Fin m) (c : Fin R → Fin m)
    (i : Fin R) :
    DS t (Fin.snoc y c : Fin (N + 2) → Fin R → Fin m) i ↔
      ∃ p : Fin R, PR t i p ∧ (DS t y p ∨ c i < y (Fin.last N) p) := by
  constructor
  · rintro ⟨j1, j2, i1, i2, h12, a1, a2, hv⟩
    have k12 : (j1 : ℕ) < j2 := h12
    have hj1 : (j1 : ℕ) ≤ N := by have := j2.isLt; omega
    obtain ⟨p, hp, ap1⟩ := al_pred ht hj1 a1
    have hpR : p < R := al_pred_bound i1.isLt i.isLt hj1 hp ap1
    refine ⟨⟨p, hpR⟩, hp, ?_⟩
    let j1' : Fin (N + 1) := ⟨j1, by omega⟩
    have ej1 : j1 = j1'.castSucc := Fin.ext rfl
    by_cases hj2 : (j2 : ℕ) = N + 1
    · have e2 : j2 = Fin.last (N + 1) := Fin.ext hj2
      have hi2 : (i2 : ℕ) = i := al_last ht (by simpa [hj2] using a2)
      have e2' : i2 = i := Fin.ext hi2
      subst e2 e2'
      rw [ej1] at hv
      simp only [Fin.snoc_castSucc, Fin.snoc_last] at hv
      by_cases hj1N : (j1 : ℕ) = N
      · right
        have hi1 : (i1 : ℕ) = p := al_last ht (by simpa [hj1N] using ap1)
        have : i1 = ⟨p, hpR⟩ := Fin.ext hi1
        subst this
        rwa [show j1' = Fin.last N from Fin.ext hj1N] at hv
      · by_cases hlt : c i2 < y (Fin.last N) ⟨p, hpR⟩
        · exact Or.inr hlt
        · left
          push_neg at hlt
          exact ⟨j1', Fin.last N, i1, ⟨p, hpR⟩, show (j1 : ℕ) < N by omega, ap1,
            al_refl t p N ht, lt_of_le_of_lt hlt hv⟩
    · left
      have hj2' : (j2 : ℕ) < N + 1 := by have := j2.isLt; omega
      let j2' : Fin (N + 1) := ⟨j2, hj2'⟩
      have ej2 : j2 = j2'.castSucc := Fin.ext rfl
      rw [ej1, ej2] at hv
      simp only [Fin.snoc_castSucc] at hv
      obtain ⟨p', hp', ap2⟩ := al_pred ht (by omega : (j2 : ℕ) ≤ N) a2
      have hpp : p' = p := by unfold PR at hp hp'; omega
      subst hpp
      exact ⟨j1', j2', i1, i2, h12, ap1, ap2, hv⟩
  · rintro ⟨p, hp, hd | hc⟩
    · obtain ⟨j1, j2, i1, i2, h12, a1, a2, hv⟩ := hd
      refine ⟨j1.castSucc, j2.castSucc, i1, i2, by simpa using h12, by simpa using al_succ hp a1,
        by simpa using al_succ hp a2, ?_⟩
      simpa using hv
    · refine ⟨(Fin.last N).castSucc, Fin.last (N + 1), p, i, Fin.castSucc_lt_last _,
        by simpa using al_self_succ (N := N) hp, by simpa using al_refl t i (N + 1) ht, ?_⟩
      simpa using hc

theorem RN_snoc {N : ℕ} (y : Fin (N + 1) → Fin R → Fin m) (c : Fin R → Fin m) :
    RN (Fin.snoc y c : Fin (N + 2) → Fin R → Fin m) ↔ RN y ∧ ∀ i, y (Fin.last N) i ≤ c i := by
  constructor
  · intro h
    refine ⟨fun j1 j2 hj i => ?_, fun i => ?_⟩
    · have := h j1.castSucc j2.castSucc (by simpa using hj) i
      simpa using this
    · have := h (Fin.last N).castSucc (Fin.last (N + 1)) (Fin.castSucc_lt_last _).le i
      simpa using this
  · rintro ⟨h, hl⟩ j1 j2 hj i
    by_cases hj2 : (j2 : ℕ) = N + 1
    · have e2 : j2 = Fin.last (N + 1) := Fin.ext hj2
      subst e2
      by_cases hj1 : (j1 : ℕ) = N + 1
      · have e1 : j1 = Fin.last (N + 1) := Fin.ext hj1
        subst e1; exact le_refl _
      · let j1' : Fin (N + 1) := ⟨j1, by have := j1.isLt; omega⟩
        have ej1 : j1 = j1'.castSucc := Fin.ext rfl
        rw [ej1]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        exact le_trans (h j1' (Fin.last N) (Fin.le_last _) i) (hl i)
    · have k12 : (j1 : ℕ) ≤ j2 := hj
      let j1' : Fin (N + 1) := ⟨j1, by have := j2.isLt; omega⟩
      let j2' : Fin (N + 1) := ⟨j2, by have := j2.isLt; omega⟩
      have ej1 : j1 = j1'.castSucc := Fin.ext rfl
      have ej2 : j2 = j2'.castSucc := Fin.ext rfl
      rw [ej1, ej2]
      simp only [Fin.snoc_castSucc]
      exact h j1' j2' hj i

end Sem

end UG

namespace UG

open Finset

section Gen

variable {R m : ℕ}

/-- The generic array condition: every column satisfies CO, rows are nondecreasing when rn,
and no line of a type in U has a valley. -/
def P (CO : (Fin R → Fin m) → Prop) (rn : Bool) (U : List ℕ) {N : ℕ}
    (y : Fin N → Fin R → Fin m) : Prop :=
  (∀ j, CO (y j)) ∧ (rn = true → RN y) ∧ ∀ t ∈ U, UC t y

/-- The condition on a new last column c. -/
def OK (CO : (Fin R → Fin m) → Prop) (rn : Bool) (U : List ℕ) {N : ℕ}
    (y : Fin (N + 1) → Fin R → Fin m) (c : Fin R → Fin m) : Prop :=
  CO c ∧ (rn = true → ∀ i, y (Fin.last N) i ≤ c i) ∧
    ∀ t ∈ U, ∀ i p : Fin R, PR t i p → ¬ (DS t y p ∧ y (Fin.last N) p < c i)

theorem P_snoc (CO : (Fin R → Fin m) → Prop) (rn : Bool) (U : List ℕ) (hU : ∀ t ∈ U, t < 3)
    {N : ℕ} (y : Fin (N + 1) → Fin R → Fin m) (c : Fin R → Fin m) :
    P CO rn U (Fin.snoc y c : Fin (N + 2) → Fin R → Fin m) ↔ P CO rn U y ∧ OK CO rn U y c := by
  unfold P OK
  rw [Fin.forall_fin_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  have hr : (rn = true → RN (Fin.snoc y c : Fin (N + 2) → Fin R → Fin m)) ↔
      (rn = true → RN y) ∧ (rn = true → ∀ i, y (Fin.last N) i ≤ c i) := by
    rw [RN_snoc]
    constructor
    · intro h; exact ⟨fun h1 => (h h1).1, fun h1 => (h h1).2⟩
    · intro h h1; exact ⟨h.1 h1, h.2 h1⟩
  have hu : (∀ t ∈ U, UC t (Fin.snoc y c : Fin (N + 2) → Fin R → Fin m)) ↔
      (∀ t ∈ U, UC t y) ∧
        ∀ t ∈ U, ∀ i p : Fin R, PR t i p → ¬ (DS t y p ∧ y (Fin.last N) p < c i) := by
    constructor
    · intro h
      exact ⟨fun t ht => ((UC_snoc t (hU t ht) y c).1 (h t ht)).1,
        fun t ht => ((UC_snoc t (hU t ht) y c).1 (h t ht)).2⟩
    · intro h t ht
      exact (UC_snoc t (hU t ht) y c).2 ⟨h.1 t ht, h.2 t ht⟩
  rw [hr, hu]
  tauto

theorem P_one (CO : (Fin R → Fin m) → Prop) (rn : Bool) (U : List ℕ)
    (y : Fin 1 → Fin R → Fin m) : P CO rn U y ↔ CO (y 0) := by
  unfold P
  constructor
  · rintro ⟨h, -, -⟩; exact h 0
  · intro h
    refine ⟨fun j => by rw [Fin.fin_one_eq_zero j]; exact h, fun _ => ?_, fun t _ => ?_⟩
    · intro j1 j2 _ i
      rw [Fin.fin_one_eq_zero j1, Fin.fin_one_eq_zero j2]
    · intro j1 j2 _ _ _ _ h12
      rw [Fin.fin_one_eq_zero j1, Fin.fin_one_eq_zero j2] at h12
      exact absurd h12 (lt_irrefl _)

lemma DS_one (t : ℕ) (y : Fin 1 → Fin R → Fin m) (p : ℕ) : ¬ DS t y p := by
  rintro ⟨j1, j2, -, -, h12, -⟩
  rw [Fin.fin_one_eq_zero j1, Fin.fin_one_eq_zero j2] at h12
  exact lt_irrefl _ h12

/-! Codes. -/

def dg (m c i : ℕ) : ℕ := c / m ^ i % m

def ccode (v : Fin R → Fin m) : ℕ := (finFunctionFinEquiv v : ℕ)

lemma ccode_lt (v : Fin R → Fin m) : ccode v < m ^ R := (finFunctionFinEquiv v).isLt

lemma dg_ccode (v : Fin R → Fin m) (i : Fin R) : dg m (ccode v) i = v i := by
  have := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv v) i
  rw [Equiv.symm_apply_apply] at this
  rw [this]; rfl

lemma ccode_inj {v w : Fin R → Fin m} (h : ccode v = ccode w) : v = w := by
  have : finFunctionFinEquiv v = finFunctionFinEquiv w := Fin.ext h
  exact finFunctionFinEquiv.injective this

/-- The flags of y: bit t * R + p says that the line of type t ∈ U through (p, last) descends. -/
def gS (U : List ℕ) {N : ℕ} (y : Fin (N + 1) → Fin R → Fin m) : Fin (3 * R) → Fin 2 :=
  fun q => if (q : ℕ) / R ∈ U ∧ DS ((q : ℕ) / R) y ((q : ℕ) % R) then 1 else 0

/-- The code of the state after y: last column and flags. -/
def stS (U : List ℕ) {N : ℕ} (y : Fin (N + 1) → Fin R → Fin m) : ℕ :=
  ccode (y (Fin.last N)) + m ^ R * (finFunctionFinEquiv (gS U y) : ℕ)

def fb (R m s q : ℕ) : Bool := s / m ^ R / 2 ^ q % 2 == 1

def vb (R t i : ℕ) : Bool := t == 0 || (t == 1 && decide (0 < i)) || (t == 2 && decide (i + 1 < R))

def pv (t i : ℕ) : ℕ := if t = 0 then i else if t = 1 then i - 1 else i + 1

def allB (f : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => allB f n && f n

def bsum (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => bsum f n + if f n then 2 ^ n else 0

def okc (R m : ℕ) (COc : ℕ → Bool) (rn : Bool) (U : List ℕ) (s c : ℕ) : Bool :=
  COc c && (!rn || allB (fun i => decide (dg m (s % m ^ R) i ≤ dg m c i)) R) &&
    U.all (fun t => allB (fun i => !(vb R t i) ||
      !(fb R m s (t * R + pv t i) && decide (dg m (s % m ^ R) (pv t i) < dg m c i))) R)

def nfl (R m : ℕ) (U : List ℕ) (s c q : ℕ) : Bool :=
  U.contains (q / R) && vb R (q / R) (q % R) &&
    (fb R m s ((q / R) * R + pv (q / R) (q % R)) ||
      decide (dg m c (q % R) < dg m (s % m ^ R) (pv (q / R) (q % R))))

def dc (R m : ℕ) (U : List ℕ) (s c : ℕ) : ℕ := c + m ^ R * bsum (nfl R m U s c) (3 * R)

lemma allB_iff (f : ℕ → Bool) (n : ℕ) : allB f n = true ↔ ∀ i < n, f i = true := by
  induction n with
  | zero => simp [allB]
  | succ n ih =>
    simp only [allB, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
      · exact h1 i h
      · rw [h]; exact h2
    · intro h; exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

lemma bsum_eq (f : ℕ → Bool) (n : ℕ) : bsum f n = ∑ i ∈ range n, if f i then 2 ^ i else 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [bsum, ih, Finset.sum_range_succ]

lemma vb_pv (R t i : ℕ) (ht : t < 3) (hi : i < R) (p : ℕ) :
    (PR t i p ∧ p < R) ↔ (vb R t i = true ∧ p = pv t i) := by
  unfold PR vb pv
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with h | h | h <;> subst h <;> simp <;> omega

lemma stS_mod (U : List ℕ) {N : ℕ} (y : Fin (N + 1) → Fin R → Fin m) :
    stS U y % m ^ R = ccode (y (Fin.last N)) := by
  unfold stS
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ccode_lt _)]

lemma fb_stS (U : List ℕ) {N : ℕ} (y : Fin (N + 1) → Fin R → Fin m) (q : Fin (3 * R)) :
    fb R m (stS U y) q = decide ((q : ℕ) / R ∈ U ∧ DS ((q : ℕ) / R) y ((q : ℕ) % R)) := by
  have hm : 0 < m ^ R := by
    have := ccode_lt (y (Fin.last N)); omega
  unfold fb stS
  rw [Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt (ccode_lt _), zero_add]
  have := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv (gS U y)) q
  rw [Equiv.symm_apply_apply] at this
  rw [← this]
  unfold gS
  split_ifs with h <;> simp [h]

theorem okc_stS (CO : (Fin R → Fin m) → Prop) (COc : ℕ → Bool)
    (hCO : ∀ v, COc (ccode v) = true ↔ CO v) (rn : Bool) (U : List ℕ) (hU : ∀ t ∈ U, t < 3)
    {N : ℕ} (y : Fin (N + 1) → Fin R → Fin m) (c : Fin R → Fin m) :
    okc R m COc rn U (stS U y) (ccode c) = true ↔ OK CO rn U y c := by
  unfold okc OK
  simp only [Bool.and_eq_true, hCO, stS_mod]
  rw [and_assoc]
  apply and_congr (Iff.rfl)
  apply and_congr
  · cases rn
    · simp
    · simp only [Bool.not_true, Bool.false_or, allB_iff, decide_eq_true_eq, forall_const]
      constructor
      · intro h i
        have := h i i.isLt
        rw [dg_ccode, dg_ccode] at this
        exact this
      · intro h i hi
        have := h ⟨i, hi⟩
        rw [show i = ((⟨i, hi⟩ : Fin R) : ℕ) from rfl, dg_ccode, dg_ccode]
        exact this
  · simp only [List.all_eq_true, allB_iff]
    apply forall_congr'; intro t
    apply forall_congr'; intro htU
    have ht := hU t htU
    constructor
    · intro h i p hp ⟨hd, hc⟩
      have hpR : (p : ℕ) < R := p.isLt
      obtain ⟨hvb, hpe⟩ := (vb_pv R t i ht i.isLt p).1 ⟨hp, hpR⟩
      have := h i i.isLt
      rw [hvb, ← hpe] at this
      have hq : t * R + p < 3 * R := by
        have : t * R ≤ 2 * R := Nat.mul_le_mul_right _ (by omega)
        omega
      have hfb := fb_stS U y ⟨t * R + p, hq⟩
      simp only at hfb
      have e1 : (t * R + p) / R = t := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hpR, zero_add]
      have e2 : (t * R + p) % R = p := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hpR]
      rw [e1, e2] at hfb
      rw [hfb] at this
      have hdg1 : dg m (ccode (y (Fin.last N))) p = y (Fin.last N) p := dg_ccode _ p
      have hdg2 : dg m (ccode c) i = c i := dg_ccode _ i
      rw [hdg1, hdg2] at this
      simp only [Bool.not_true, Bool.false_or, Bool.not_eq_true', Bool.and_eq_false_iff,
        decide_eq_false_iff_not] at this
      rcases this with h1 | h1
      · exact h1 ⟨htU, hd⟩
      · exact h1 hc
    · intro h i hi
      cases hv : vb R t i
      · simp
      · simp only [Bool.not_true, Bool.false_or, Bool.not_eq_true', Bool.and_eq_false_iff,
          decide_eq_false_iff_not]
        have hpe : pv t i < R ∧ PR t i (pv t i) := by
          have := (vb_pv R t i ht hi (pv t i)).2 ⟨hv, rfl⟩
          exact ⟨this.2, this.1⟩
        have hq : t * R + pv t i < 3 * R := by
          have : t * R ≤ 2 * R := Nat.mul_le_mul_right _ (by omega)
          omega
        have hfb := fb_stS U y ⟨t * R + pv t i, hq⟩
        simp only at hfb
        have e1 : (t * R + pv t i) / R = t := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hpe.1, zero_add]
        have e2 : (t * R + pv t i) % R = pv t i := by
          rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hpe.1]
        rw [e1, e2] at hfb
        rw [hfb]
        have hdg1 : dg m (ccode (y (Fin.last N))) (pv t i) = y (Fin.last N) ⟨pv t i, hpe.1⟩ :=
          dg_ccode _ ⟨pv t i, hpe.1⟩
        have hdg2 : dg m (ccode c) i = c ⟨i, hi⟩ := dg_ccode _ ⟨i, hi⟩
        rw [hdg1, hdg2]
        have := h ⟨i, hi⟩ ⟨pv t i, hpe.1⟩ hpe.2
        by_cases hd : t ∈ U ∧ DS t y (pv t i)
        · right
          intro hc
          exact this ⟨hd.2, hc⟩
        · left
          simpa using hd

theorem dc_stS (U : List ℕ) (hU : ∀ t ∈ U, t < 3) {N : ℕ} (y : Fin (N + 1) → Fin R → Fin m)
    (c : Fin R → Fin m) :
    dc R m U (stS U y) (ccode c) = stS U (Fin.snoc y c : Fin (N + 2) → Fin R → Fin m) := by
  unfold dc
  conv_rhs => unfold stS
  simp only [Fin.snoc_last]
  congr 2
  rw [bsum_eq, finFunctionFinEquiv_apply, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro q _
  have hR : 0 < R := by have := q.isLt; omega
  have hqR : (q : ℕ) % R < R := Nat.mod_lt _ hR
  have ht3 : (q : ℕ) / R < 3 := by
    have := q.isLt
    exact Nat.div_lt_of_lt_mul (by linarith)
  have key : nfl R m U (stS U y) (ccode c) q = true ↔
      ((q : ℕ) / R ∈ U ∧ DS ((q : ℕ) / R) (Fin.snoc y c : Fin (N + 2) → Fin R → Fin m)
        ((q : ℕ) % R)) := by
    have hds := DS_snoc ((q : ℕ) / R) ht3 y c ⟨(q : ℕ) % R, hqR⟩
    simp only at hds
    rw [hds]
    unfold nfl
    simp only [Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨hU', hv⟩, hor⟩
      have hp := (vb_pv R _ _ ht3 hqR (pv ((q : ℕ) / R) ((q : ℕ) % R))).2 ⟨hv, rfl⟩
      refine ⟨hU', ⟨_, hp.2⟩, hp.1, ?_⟩
      have hq : (q : ℕ) / R * R + pv ((q : ℕ) / R) ((q : ℕ) % R) < 3 * R := by
        have : (q : ℕ) / R * R ≤ 2 * R := Nat.mul_le_mul_right _ (by omega)
        omega
      have hfb := fb_stS U y ⟨_, hq⟩
      simp only at hfb
      have e1 : ((q : ℕ) / R * R + pv ((q : ℕ) / R) ((q : ℕ) % R)) / R = (q : ℕ) / R := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hR, Nat.div_eq_of_lt hp.2, zero_add]
      have e2 : ((q : ℕ) / R * R + pv ((q : ℕ) / R) ((q : ℕ) % R)) % R =
          pv ((q : ℕ) / R) ((q : ℕ) % R) := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hp.2]
      rw [e1, e2] at hfb
      rcases hor with h1 | h1
      · rw [hfb] at h1
        simp only [decide_eq_true_eq] at h1
        exact Or.inl h1.2
      · right
        rw [stS_mod, dg_ccode c ⟨_, hqR⟩, dg_ccode _ ⟨_, hp.2⟩] at h1
        exact h1
    · rintro ⟨hU', ⟨p, hpR⟩, hp, hor⟩
      have hv := (vb_pv R _ _ ht3 hqR p).1 ⟨hp, hpR⟩
      refine ⟨⟨hU', hv.1⟩, ?_⟩
      have hpe : p = pv ((q : ℕ) / R) ((q : ℕ) % R) := hv.2
      subst hpe
      have hq : (q : ℕ) / R * R + pv ((q : ℕ) / R) ((q : ℕ) % R) < 3 * R := by
        have : (q : ℕ) / R * R ≤ 2 * R := Nat.mul_le_mul_right _ (by omega)
        omega
      have hfb := fb_stS U y ⟨_, hq⟩
      simp only at hfb
      have e1 : ((q : ℕ) / R * R + pv ((q : ℕ) / R) ((q : ℕ) % R)) / R = (q : ℕ) / R := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hR, Nat.div_eq_of_lt hpR, zero_add]
      have e2 : ((q : ℕ) / R * R + pv ((q : ℕ) / R) ((q : ℕ) % R)) % R =
          pv ((q : ℕ) / R) ((q : ℕ) % R) := by
        rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hpR]
      rw [e1, e2] at hfb
      rcases hor with h1 | h1
      · left
        rw [hfb]
        simp only [decide_eq_true_eq]
        exact ⟨hU', h1⟩
      · right
        rw [stS_mod, dg_ccode c ⟨_, hqR⟩, dg_ccode _ ⟨_, hpR⟩]
        exact h1
  unfold gS
  by_cases h : nfl R m U (stS U y) (ccode c) q = true
  · rw [if_pos h, if_pos (key.1 h)]; simp
  · rw [if_neg h, if_neg (fun h' => h (key.2 h'))]; simp

end Gen

end UG

namespace UG

open Finset

section Count

variable {R m : ℕ} (CO : (Fin R → Fin m) → Prop) [DecidablePred CO] (COc : ℕ → Bool)
  (hCO : ∀ v, COc (ccode v) = true ↔ CO v) (rn : Bool) (U : List ℕ) (hU : ∀ t ∈ U, t < 3)

instance instDecP {N : ℕ} (y : Fin N → Fin R → Fin m) : Decidable (P CO rn U y) := by
  unfold P UC RN; infer_instance

/-- Arrays of width N + 1 satisfying P, weighted by g of their final state. -/
def Cnt (N : ℕ) (g : ℕ → ℕ) : ℕ :=
  ∑ y : Fin (N + 1) → Fin R → Fin m, if P CO rn U y then g (stS U y) else 0

lemma sum_range_list (f : ℕ → ℕ) (B : ℕ) : ∑ i ∈ range B, f i = ((List.range B).map f).sum := by
  induction B with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.sum_append, ih]; simp

lemma sum_col (f : ℕ → ℕ) :
    ∑ c : Fin R → Fin m, f (ccode c) = ((List.range (m ^ R)).map f).sum := by
  rw [← sum_range_list, ← Fin.sum_univ_eq_sum_range]
  exact Fintype.sum_equiv finFunctionFinEquiv _ _ (fun c => rfl)

include hCO hU in
theorem Cnt_succ (N : ℕ) (g : ℕ → ℕ) :
    Cnt CO rn U (N + 1) g = Cnt CO rn U N (fun s => ((List.range (m ^ R)).map (fun c =>
      if okc R m COc rn U s c = true then g (dc R m U s c) else 0)).sum) := by
  unfold Cnt
  rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ => Fin R → Fin m))
    (fun p => if P CO rn U (Fin.snoc p.2 p.1 : Fin (N + 2) → Fin R → Fin m) then
      g (stS U (Fin.snoc p.2 p.1 : Fin (N + 2) → Fin R → Fin m)) else 0) _ (fun p => rfl)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : P CO rn U y
  · rw [if_pos hy]
    beta_reduce
    rw [← sum_col]
    apply Finset.sum_congr rfl
    intro c _
    rw [dc_stS U hU y c]
    by_cases hc : OK CO rn U y c
    · rw [if_pos ((P_snoc CO rn U hU y c).2 ⟨hy, hc⟩),
        if_pos ((okc_stS CO COc hCO rn U hU y c).2 hc)]
    · rw [if_neg (fun h => hc ((P_snoc CO rn U hU y c).1 h).2),
        if_neg (fun h => hc ((okc_stS CO COc hCO rn U hU y c).1 h))]
  · rw [if_neg hy]
    apply Finset.sum_eq_zero
    intro c _
    rw [if_neg (fun h => hy ((P_snoc CO rn U hU y c).1 h).1)]

/-- Continuation counts on codes. -/
def Wc (R m : ℕ) (COc : ℕ → Bool) (rn : Bool) (U : List ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | j + 1, s => ((List.range (m ^ R)).map (fun c =>
      if okc R m COc rn U s c = true then Wc R m COc rn U j (dc R m U s c) else 0)).sum

include hCO hU in
theorem Cnt_W (N j : ℕ) :
    Cnt CO rn U N (Wc R m COc rn U j) = Cnt CO rn U 0 (Wc R m COc rn U (N + j)) := by
  induction N generalizing j with
  | zero => simp
  | succ N ih =>
    rw [Cnt_succ CO COc hCO rn U hU]
    have : (fun s => ((List.range (m ^ R)).map (fun c =>
      if okc R m COc rn U s c = true then Wc R m COc rn U j (dc R m U s c) else 0)).sum) =
        Wc R m COc rn U (j + 1) := rfl
    rw [this, ih, show N + (j + 1) = N + 1 + j by omega]

include hCO in
theorem Cnt_zero (g : ℕ → ℕ) :
    Cnt CO rn U 0 g = ((List.range (m ^ R)).map (fun k => if COc k = true then g k else 0)).sum := by
  unfold Cnt
  rw [← sum_col]
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin R → Fin m)) _ _ (fun y => ?_)
  have hy : y = fun _ => y 0 := by funext j; rw [Fin.fin_one_eq_zero j]
  have hst : stS U y = ccode (y 0) := by
    unfold stS
    have : gS U y = fun _ => 0 := by
      funext q; unfold gS; rw [if_neg (fun h => DS_one _ y _ h.2)]
    rw [this, finFunctionFinEquiv_apply]
    simp
  simp only [Equiv.funUnique_apply, Function.eval]
  rw [show (default : Fin 1) = 0 from rfl, hst]
  by_cases h : CO (y 0)
  · rw [if_pos ((P_one CO rn U y).2 h), if_pos ((hCO _).2 h)]
  · rw [if_neg (fun h' => h ((P_one CO rn U y).1 h')), if_neg (fun h' => h ((hCO _).1 h'))]

include hCO hU in
theorem count_eq (N : ℕ) :
    (univ.filter (fun y : Fin (N + 1) → Fin R → Fin m => P CO rn U y)).card =
      ((List.range (m ^ R)).map (fun k => if COc k = true then Wc R m COc rn U N k else 0)).sum := by
  rw [Finset.card_filter]
  have : (∑ y : Fin (N + 1) → Fin R → Fin m, if P CO rn U y then 1 else 0) =
      Cnt CO rn U N (Wc R m COc rn U 0) := rfl
  rw [this, Cnt_W CO COc hCO rn U hU, Cnt_zero CO COc hCO, Nat.add_zero]

end Count

/-! The certificate. -/

def gL (L : List ℕ) (i : ℕ) : ℕ := L.getD i 0

lemma flt_sum (L : List ℕ) (p : ℕ → Bool) (g : ℕ → ℕ) (f : ℕ → ℕ) :
    (L.map (fun c => if p c = true then f (g c) else 0)).sum =
      ((L.filterMap (fun c => if p c = true then some (g c) else none)).map f).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => by_cases h : p a = true <;> simp [List.filterMap_cons, h, ih]

def Lin (cs : List (ℕ × ℕ)) (F : ℕ → ℕ) (n : ℕ) : ℕ := (cs.map (fun p => p.1 * F (n + p.2))).sum

lemma Lin_sum (cs : List (ℕ × ℕ)) (L : List ℕ) (G : ℕ → ℕ → ℕ) (n : ℕ) :
    Lin cs (fun j => (L.map (fun t => G t j)).sum) n = (L.map (fun t => Lin cs (G t) n)).sum := by
  induction cs with
  | nil => simp [Lin]
  | cons p cs ih =>
    unfold Lin at ih ⊢
    rw [List.map_cons, List.sum_cons, ih, ← List.sum_map_mul_left]
    simp only [List.map_cons, List.sum_cons]
    rw [← List.sum_map_add]

section Cert

variable (R m : ℕ) (COc : ℕ → Bool) (rn : Bool) (U : List ℕ) (RL : List ℕ) (SI : List (List ℕ))
  (BL : List ℕ) (BS : List (List ℕ)) (VT : List (List ℕ)) (NS NB : ℕ)

def c1 (idx : ℕ) : Bool :=
  ((List.range (m ^ R)).filterMap (fun c =>
    if okc R m COc rn U (gL RL idx) c = true then some (dc R m U (gL RL idx) c) else none)) ==
      (SI.getD idx []).map (gL RL) && (SI.getD idx []).all (fun t => decide (t < NS))

def chk1 : Bool := (List.range NS).all (c1 R m COc rn U RL SI NS)

lemma all_split (f : ℕ → Bool) (a k n : ℕ) (h1 : (List.range' a k).all f = true)
    (h2 : (List.range' (a + k) n).all f = true) : (List.range' a (k + n)).all f = true := by
  rw [List.all_eq_true] at h1 h2 ⊢
  intro x hx
  rw [List.mem_range'_1] at hx
  by_cases hxa : x < a + k
  · exact h1 x (List.mem_range'_1.2 ⟨hx.1, hxa⟩)
  · exact h2 x (List.mem_range'_1.2 ⟨by omega, by omega⟩)

lemma chk1_of (h : (List.range' 0 NS).all (c1 R m COc rn U RL SI NS) = true) :
    chk1 R m COc rn U RL SI NS = true := by
  unfold chk1; rw [List.range_eq_range']; exact h

def c2 : ℕ → Bool := fun idx =>
  decide (gL BL idx < NB) && ((SI.getD idx []).map (gL BL)).isPerm (BS.getD (gL BL idx) [])

def chk2 : Bool := (List.range NS).all (c2 SI BL BS NB)

lemma chk2_of (h : (List.range' 0 NS).all (c2 SI BL BS NB) = true) : chk2 SI BL BS NS NB = true := by
  unfold chk2; rw [List.range_eq_range']; exact h

def chkV (J : ℕ) : Bool :=
  (List.range NB).all (fun b => gL (VT.getD 0 []) b == 1) &&
    (List.range J).all (fun j => (List.range NB).all (fun b =>
      gL (VT.getD (j + 1) []) b == ((BS.getD b []).map (gL (VT.getD j []))).sum))

lemma W_succ (h1 : chk1 R m COc rn U RL SI NS = true) (idx : ℕ) (hi : idx < NS) (j : ℕ) :
    Wc R m COc rn U (j + 1) (gL RL idx) =
      ((SI.getD idx []).map (fun t => Wc R m COc rn U j (gL RL t))).sum := by
  unfold chk1 at h1
  rw [List.all_eq_true] at h1
  have h := h1 idx (List.mem_range.2 hi)
  unfold c1 at h
  rw [Bool.and_eq_true, beq_iff_eq] at h
  rw [Wc, flt_sum, h.1, List.map_map]
  rfl

lemma W_SI_lt (h1 : chk1 R m COc rn U RL SI NS = true) (idx : ℕ) (hi : idx < NS) :
    ∀ t ∈ SI.getD idx [], t < NS := by
  unfold chk1 at h1
  rw [List.all_eq_true] at h1
  have h := h1 idx (List.mem_range.2 hi)
  unfold c1 at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  intro t ht
  simpa using h.2 t ht

theorem W_eq_V (J : ℕ) (h1 : chk1 R m COc rn U RL SI NS = true) (h2 : chk2 SI BL BS NS NB = true)
    (hV : chkV BS VT NB J = true) :
    ∀ j ≤ J, ∀ idx < NS, Wc R m COc rn U j (gL RL idx) = gL (VT.getD j []) (gL BL idx) := by
  unfold chk2 c2 at h2
  unfold chkV at hV
  rw [List.all_eq_true] at h2
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hV
  intro j
  induction j with
  | zero =>
    intro _ idx hi
    have hb := h2 idx (List.mem_range.2 hi)
    rw [Bool.and_eq_true, decide_eq_true_eq] at hb
    have := hV.1 _ (List.mem_range.2 hb.1)
    rw [beq_iff_eq] at this
    rw [this]; rfl
  | succ j ih =>
    intro hj idx hi
    rw [W_succ R m COc rn U RL SI NS h1 idx hi]
    have hb := h2 idx (List.mem_range.2 hi)
    rw [Bool.and_eq_true, decide_eq_true_eq, List.isPerm_iff] at hb
    have e : ((SI.getD idx []).map (fun t => Wc R m COc rn U j (gL RL t))).sum =
        (((SI.getD idx []).map (gL BL)).map (gL (VT.getD j []))).sum := by
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro t ht
      exact ih (by omega) t (W_SI_lt R m COc rn U RL SI NS h1 idx hi t ht)
    rw [e, (hb.2.map _).sum_eq]
    have := List.all_eq_true.1 (hV.2 j (List.mem_range.2 (by omega))) (gL BL idx)
      (List.mem_range.2 hb.1)
    rw [beq_iff_eq] at this
    rw [this]

def chkI (LC RC : List (ℕ × ℕ)) (e : ℕ) : Bool :=
  (List.range NB).all (fun b =>
    Lin LC (fun j => gL (VT.getD j []) b) e == Lin RC (fun j => gL (VT.getD j []) b) e)

theorem W_ident (J : ℕ) (h1 : chk1 R m COc rn U RL SI NS = true) (h2 : chk2 SI BL BS NS NB = true)
    (hV : chkV BS VT NB J = true) (LC RC : List (ℕ × ℕ)) (e : ℕ)
    (hI : chkI VT NB LC RC e = true) (hJ : ∀ p ∈ LC ++ RC, e + p.2 ≤ J) :
    ∀ n, ∀ idx < NS, Lin LC (fun j => Wc R m COc rn U j (gL RL idx)) (e + n) =
      Lin RC (fun j => Wc R m COc rn U j (gL RL idx)) (e + n) := by
  intro n
  induction n with
  | zero =>
    intro idx hi
    have hWV := W_eq_V R m COc rn U RL SI BL BS VT NS NB J h1 h2 hV
    have hb : gL BL idx < NB := by
      unfold chk2 c2 at h2; rw [List.all_eq_true] at h2
      have := h2 idx (List.mem_range.2 hi)
      rw [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1
    unfold chkI at hI
    rw [List.all_eq_true] at hI
    have := hI _ (List.mem_range.2 hb)
    rw [beq_iff_eq] at this
    have eL : Lin LC (fun j => Wc R m COc rn U j (gL RL idx)) (e + 0) =
        Lin LC (fun j => gL (VT.getD j []) (gL BL idx)) e := by
      unfold Lin; congr 1; apply List.map_congr_left; intro p hp
      dsimp only
      rw [Nat.add_zero, hWV _ (hJ p (List.mem_append_left _ hp)) idx hi]
    have eR : Lin RC (fun j => Wc R m COc rn U j (gL RL idx)) (e + 0) =
        Lin RC (fun j => gL (VT.getD j []) (gL BL idx)) e := by
      unfold Lin; congr 1; apply List.map_congr_left; intro p hp
      dsimp only
      rw [Nat.add_zero, hWV _ (hJ p (List.mem_append_right _ hp)) idx hi]
    rw [eL, eR, this]
  | succ n ih =>
    intro idx hi
    have key : ∀ cs : List (ℕ × ℕ), Lin cs (fun j => Wc R m COc rn U j (gL RL idx)) (e + (n + 1)) =
        ((SI.getD idx []).map (fun t => Lin cs (fun j => Wc R m COc rn U j (gL RL t)) (e + n))).sum := by
      intro cs
      rw [← Lin_sum]
      unfold Lin
      congr 1
      apply List.map_congr_left
      intro p _
      dsimp only
      rw [show e + (n + 1) + p.2 = (e + n + p.2) + 1 by omega,
        W_succ R m COc rn U RL SI NS h1 idx hi]
    rw [key, key]
    congr 1
    apply List.map_congr_left
    intro t ht
    exact ih t (W_SI_lt R m COc rn U RL SI NS h1 idx hi t ht)

/-- The total counts. -/
def Ac (N : ℕ) : ℕ :=
  ((List.range (m ^ R)).map (fun k => if COc k = true then Wc R m COc rn U N k else 0)).sum

def chk3 (IL : List ℕ) : Bool :=
  ((List.range (m ^ R)).filterMap (fun k => if COc k = true then some k else none)) ==
    IL.map (gL RL) && IL.all (fun t => decide (t < NS))

lemma Ac_IL (IL : List ℕ) (h3 : chk3 R m COc RL NS IL = true) (N : ℕ) :
    Ac R m COc rn U N = (IL.map (fun t => Wc R m COc rn U N (gL RL t))).sum := by
  unfold chk3 at h3
  rw [Bool.and_eq_true, beq_iff_eq] at h3
  unfold Ac
  have e := flt_sum (List.range (m ^ R)) COc (fun k => k) (Wc R m COc rn U N)
  rw [e, h3.1, List.map_map]
  rfl

theorem A_ident (J : ℕ) (h1 : chk1 R m COc rn U RL SI NS = true) (h2 : chk2 SI BL BS NS NB = true)
    (hV : chkV BS VT NB J = true) (LC RC : List (ℕ × ℕ)) (e : ℕ)
    (hI : chkI VT NB LC RC e = true) (hJ : ∀ p ∈ LC ++ RC, e + p.2 ≤ J) (IL : List ℕ)
    (h3 : chk3 R m COc RL NS IL = true) (n : ℕ) :
    Lin LC (Ac R m COc rn U) (e + n) = Lin RC (Ac R m COc rn U) (e + n) := by
  have hA : Ac R m COc rn U = fun N => (IL.map (fun t => Wc R m COc rn U N (gL RL t))).sum := by
    funext N; exact Ac_IL R m COc rn U RL NS IL h3 N
  rw [hA, Lin_sum, Lin_sum]
  congr 1
  apply List.map_congr_left
  intro t ht
  have : t < NS := by
    unfold chk3 at h3; rw [Bool.and_eq_true, List.all_eq_true] at h3
    simpa using h3.2 t ht
  exact W_ident R m COc rn U RL SI BL BS VT NS NB J h1 h2 hV LC RC e hI hJ n t this

theorem A_val (J : ℕ) (h1 : chk1 R m COc rn U RL SI NS = true) (h2 : chk2 SI BL BS NS NB = true)
    (hV : chkV BS VT NB J = true) (IL : List ℕ) (h3 : chk3 R m COc RL NS IL = true) (N : ℕ)
    (hN : N ≤ J) :
    Ac R m COc rn U N = (IL.map (fun t => gL (VT.getD N []) (gL BL t))).sum := by
  rw [Ac_IL R m COc rn U RL NS IL h3]
  congr 1
  apply List.map_congr_left
  intro t ht
  have : t < NS := by
    unfold chk3 at h3; rw [Bool.and_eq_true, List.all_eq_true] at h3
    simpa using h3.2 t ht
  exact W_eq_V R m COc rn U RL SI BL BS VT NS NB J h1 h2 hV N hN t this

end Cert

end UG

namespace PA224148

open OMA.S_oeis_a224148 UG PowerSeries

def CO (v : Fin 4 → Fin 2) : Prop := Monotone v

instance : DecidablePred CO := fun v => by unfold CO Monotone; infer_instance

def COL : List Bool := [true, false, false, false, false, false, false, false, true, false, false, false, true, false, true, true]

def COc (c : ℕ) : Bool := COL.getD c false

def decCol (c : ℕ) : Fin 4 → Fin 2 := fun i => ⟨dg 2 c i, Nat.mod_lt _ (by norm_num)⟩

theorem decCol_ccode (v : Fin 4 → Fin 2) : decCol (ccode v) = v := by
  funext i; exact Fin.ext (dg_ccode v i)

theorem hCOL : ∀ c < 2 ^ 4, COL.getD c false = decide (CO (decCol c)) := by decide +kernel

theorem hCO (v : Fin 4 → Fin 2) : COc (ccode v) = true ↔ CO v := by
  have := hCOL (ccode v) (ccode_lt v)
  rw [decCol_ccode] at this
  unfold COc; rw [this]; simp

theorem hU : ∀ t ∈ ([0, 2] : List ℕ), t < 3 := by decide

theorem uc_anti {n : ℕ} (x : Fin 4 → Fin n → Fin 2) : AntidiagUnimodal x ↔ UC 2 (fun j i => x i j) := by
  constructor
  · intro h j1 j2 j3 i1 i2 i3 h12 h23 a1 a2
    exact h i1 i2 i3 j1 j2 j3 h12 h23 (by unfold al at a1 a2; omega) (by unfold al at a1 a2; omega)
  · intro h i1 i2 i3 j1 j2 j3 h12 h23 e1 e2
    exact h j1 j2 j3 i1 i2 i3 h12 h23 (by unfold al; omega) (by unfold al; omega)

theorem uc_row {n : ℕ} (x : Fin 4 → Fin n → Fin 2) : (∀ i, Unimodal (x i)) ↔ UC 0 (fun j i => x i j) := by
  constructor
  · intro h j1 j2 j3 i1 i2 i3 h12 h23 a1 a2
    have e1 : i1 = i3 := Fin.ext (by unfold al at a1; omega)
    have e2 : i2 = i3 := Fin.ext (by unfold al at a2; omega)
    subst e1 e2
    exact h i2 j1 j2 j3 h12 h23
  · intro h i j1 j2 j3 h12 h23
    exact h j1 j2 j3 i i i h12 h23 (by unfold al; omega) (by unfold al; omega)

theorem good_iff {n : ℕ} (x : Fin 4 → Fin n → Fin 2) : Good x ↔ P CO false [0, 2] (fun j i => x i j) := by
  unfold Good P
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, CO,
    Bool.false_eq_true, false_implies, true_and, implies_true, uc_row, uc_anti]
  tauto

theorem a_eq (N : ℕ) : a (N + 1) = Ac 4 2 COc false [0, 2] N := by
  rw [a, Ac, ← count_eq CO COc hCO false [0, 2] hU N]
  apply Finset.card_equiv (Equiv.piComm _)
  intro x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact good_iff x

def RL : List ℕ := [0, 8, 12, 14, 15, 16512, 16392, 24768, 24648, 8204, 28896, 28776, 12332, 4110,
    28912, 28792, 12348, 4126, 8320, 24704, 24584, 12480, 28864, 28744, 12300, 12512, 12528, 4224,
    12416, 28800, 28680, 4288, 4320, 4336, 128, 192, 224, 240]

def SI : List (List ℕ) := [[0, 1, 2, 3, 4], [5, 6, 2, 3, 4], [7, 8, 9, 3, 4], [10, 11, 12, 13, 4],
    [14, 15, 16, 17, 4], [18], [19, 20, 9], [21], [22, 23], [22, 23, 24, 13], [25], [10, 11], [10,
    11, 12], [10, 11, 12, 13, 4], [26], [14, 15], [14, 15, 16], [14, 15, 16, 17], [27], [28], [29,
    30, 24], [31], [21], [22, 23], [22, 23, 24, 13], [32], [33], [34], [27], [28], [29, 30, 24],
    [35], [36], [37], [34], [35], [36], [37]]

def BL : List ℕ := [0, 1, 2, 3, 4, 5, 6, 5, 7, 8, 5, 7, 9, 3, 5, 7, 9, 10, 5, 5, 6, 5, 5, 7, 8, 5,
    5, 5, 5, 5, 6, 5, 5, 5, 5, 5, 5, 5]

def BS : List (List ℕ) := [[0, 1, 2, 3, 4], [5, 6, 2, 3, 4], [5, 7, 8, 3, 4], [5, 7, 9, 3, 4], [5,
    7, 9, 10, 4], [5], [5, 6, 8], [5, 7], [5, 7, 8, 3], [5, 7, 9], [5, 7, 9, 10]]

def VT : List (List ℕ) := [[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], [5, 5, 5, 5, 5, 1, 3, 2, 4, 3, 4],
    [25, 19, 17, 16, 15, 1, 8, 3, 12, 6, 10], [92, 57, 47, 41, 35, 1, 21, 4, 32, 10, 20], [272,
    145, 113, 91, 70, 1, 54, 5, 78, 15, 35], [691, 329, 245, 182, 126, 1, 133, 6, 175, 21, 56],
    [1573, 687, 490, 336, 210, 1, 309, 7, 364, 28, 84], [3296, 1346, 918, 582, 330, 1, 674, 8, 708,
    36, 120], [6472, 2505, 1629, 957, 495, 1, 1383, 9, 1299, 45, 165], [12058, 4465, 2761, 1507,
    715, 1, 2683, 10, 2266, 55, 220], [21506, 7667, 4499, 2288, 1001, 1, 4950, 11, 3784, 66, 286],
    [36961, 12739, 7085, 3367, 1365, 1, 8735, 12, 6084, 78, 364]]

def IL : List ℕ := [0, 1, 2, 3, 4]

def AV : List ℕ := [0, 5, 25, 92, 272, 691, 1573, 3296, 6472, 12058, 21506, 36961, 61517]

def LC : List (ℕ × ℕ) := [(1, 9), (36, 7), (126, 5), (84, 3), (9, 1)]

def RC : List (ℕ × ℕ) := [(9, 8), (84, 6), (126, 4), (36, 2), (1, 0)]

set_option maxRecDepth 100000 in
theorem h1_0 : (List.range' 0 38).all (c1 4 2 COc false [0, 2] RL SI 38) = true := by
  decide +kernel

theorem h1 : chk1 4 2 COc false [0, 2] RL SI 38 = true :=
  chk1_of 4 2 COc false [0, 2] RL SI 38 h1_0


set_option maxRecDepth 100000 in
theorem h2_0 : (List.range' 0 38).all (c2 SI BL BS 11) = true := by
  decide +kernel

theorem h2 : chk2 SI BL BS 38 11 = true :=
  chk2_of SI BL BS 38 11 h2_0


set_option maxRecDepth 100000 in
theorem hV : chkV BS VT 11 11 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem hI : chkI VT 11 LC RC 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem h3 : chk3 4 2 COc RL 38 IL = true := by decide +kernel

theorem hJ : ∀ p ∈ LC ++ RC, 0 + p.2 ≤ 11 := by decide

set_option maxRecDepth 100000 in
theorem hAV : ∀ N ≤ 11, (IL.map (fun t => gL (VT.getD N []) (gL BL t))).sum = gL AV (N + 1) := by
  decide +kernel

theorem hid (M : ℕ) : Lin LC (Ac 4 2 COc false [0, 2]) (0 + M) = Lin RC (Ac 4 2 COc false [0, 2]) (0 + M) :=
  A_ident 4 2 COc false [0, 2] RL SI BL BS VT 38 11 11 h1 h2 hV LC RC 0 hI hJ IL h3 M

theorem hval (N : ℕ) (hN : N ≤ 11) : a (N + 1) = gL AV (N + 1) := by
  rw [a_eq, A_val 4 2 COc false [0, 2] RL SI BL BS VT 38 11 11 h1 h2 hV IL h3 N hN, hAV N hN]

/-! The rest is about any sequence with these properties (kept abstract for the kernel). -/

theorem recN (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (0 + M) = Lin RC A (0 + M)) (hval : ∀ N ≤ 11, f (N + 1) = gL AV (N + 1)) (M : ℕ) : 1 * f (M + 10) + 36 * f (M + 10 - 2) + 126 * f (M + 10 - 4) + 84 * f (M + 10 - 6) + 9 * f (M + 10 - 8) = 9 * f (M + 10 - 1) + 84 * f (M + 10 - 3) + 126 * f (M + 10 - 5) + 36 * f (M + 10 - 7) + 1 * f (M + 10 - 9) := by
  have h := hid M
  simp only [LC, RC, Lin, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at h
  rw [show M + 10 - 1 = 0 + M + 8 + 1 by omega, ha (0 + M + 8), show M + 10 - 2 = 0 + M + 7 + 1 by omega, ha (0 + M + 7), show M + 10 - 3 = 0 + M + 6 + 1 by omega, ha (0 + M + 6), show M + 10 - 4 = 0 + M + 5 + 1 by omega, ha (0 + M + 5), show M + 10 - 5 = 0 + M + 4 + 1 by omega, ha (0 + M + 4), show M + 10 - 6 = 0 + M + 3 + 1 by omega, ha (0 + M + 3), show M + 10 - 7 = 0 + M + 2 + 1 by omega, ha (0 + M + 2), show M + 10 - 8 = 0 + M + 1 + 1 by omega, ha (0 + M + 1), show M + 10 - 9 = 0 + M + 1 by omega, ha (0 + M), show M + 10 = 0 + M + 9 + 1 by omega, ha (0 + M + 9)]
  omega

theorem recZ (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (0 + M) = Lin RC A (0 + M)) (hval : ∀ N ≤ 11, f (N + 1) = gL AV (N + 1)) (n : ℕ) (hn : 9 < n) : (f n : ℤ) = 9 * f (n - 1) - 36 * f (n - 2) + 84 * f (n - 3) - 126 * f (n - 4) + 126 * f (n - 5) - 84 * f (n - 6) + 36 * f (n - 7) - 9 * f (n - 8) + f (n - 9) := by
  have v1 : f 1 = 5 := hval 0 (by norm_num)
  have v2 : f 2 = 25 := hval 1 (by norm_num)
  have v3 : f 3 = 92 := hval 2 (by norm_num)
  have v4 : f 4 = 272 := hval 3 (by norm_num)
  have v5 : f 5 = 691 := hval 4 (by norm_num)
  have v6 : f 6 = 1573 := hval 5 (by norm_num)
  have v7 : f 7 = 3296 := hval 6 (by norm_num)
  have v8 : f 8 = 6472 := hval 7 (by norm_num)
  have v9 : f 9 = 12058 := hval 8 (by norm_num)
  have v10 : f 10 = 21506 := hval 9 (by norm_num)
  have v11 : f 11 = 36961 := hval 10 (by norm_num)
  have v12 : f 12 = 61517 := hval 11 (by norm_num)
  by_cases hb : 10 ≤ n
  · obtain ⟨M, rfl⟩ : ∃ M, n = M + 10 := ⟨n - 10, by omega⟩
    have := recN f A ha hid hval M
    omega
  · interval_cases n <;> norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12]

theorem recQ (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (0 + M) = Lin RC A (0 + M)) (hval : ∀ N ≤ 11, f (N + 1) = gL AV (N + 1)) (n : ℕ) (hn : 9 < n) : (f n : ℚ) = 9 * (f (n - 1) : ℚ) - 36 * (f (n - 2) : ℚ) + 84 * (f (n - 3) : ℚ) - 126 * (f (n - 4) : ℚ) + 126 * (f (n - 5) : ℚ) - 84 * (f (n - 6) : ℚ) + 36 * (f (n - 7) : ℚ) - 9 * (f (n - 8) : ℚ) + (f (n - 9) : ℚ) := by
  have := recZ f A ha hid hval n hn
  exact_mod_cast this

theorem poly (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (0 + M) = Lin RC A (0 + M)) (hval : ∀ N ≤ 11, f (N + 1) = gL AV (N + 1)) (n : ℕ) (hn : 0 < n) : (f n : ℚ) = (1/40320) * (n : ℚ) ^ 8 + (1/3360) * (n : ℚ) ^ 7 + (1/192) * (n : ℚ) ^ 6 + (1/16) * (n : ℚ) ^ 5 + (223/640) * (n : ℚ) ^ 4 + (149/160) * (n : ℚ) ^ 3 + (3319/2016) * (n : ℚ) ^ 2 + (169/168) * (n : ℚ) + 1 := by
  have v1 : f 1 = 5 := hval 0 (by norm_num)
  have v2 : f 2 = 25 := hval 1 (by norm_num)
  have v3 : f 3 = 92 := hval 2 (by norm_num)
  have v4 : f 4 = 272 := hval 3 (by norm_num)
  have v5 : f 5 = 691 := hval 4 (by norm_num)
  have v6 : f 6 = 1573 := hval 5 (by norm_num)
  have v7 : f 7 = 3296 := hval 6 (by norm_num)
  have v8 : f 8 = 6472 := hval 7 (by norm_num)
  have v9 : f 9 = 12058 := hval 8 (by norm_num)
  have v10 : f 10 = 21506 := hval 9 (by norm_num)
  have v11 : f 11 = 36961 := hval 10 (by norm_num)
  have v12 : f 12 = 61517 := hval 11 (by norm_num)
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  by_cases hs : n ≤ 9
  · interval_cases n <;> norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
    rw [recQ f A ha hid hval (k + 9) (by omega), ih (k + 9 - 1) (by omega) (by omega), ih (k + 9 - 2) (by omega) (by omega), ih (k + 9 - 3) (by omega) (by omega), ih (k + 9 - 4) (by omega) (by omega), ih (k + 9 - 5) (by omega) (by omega), ih (k + 9 - 6) (by omega) (by omega), ih (k + 9 - 7) (by omega) (by omega), ih (k + 9 - 8) (by omega) (by omega), ih (k + 9 - 9) (by omega) (by omega)]
    simp only [show k + 9 - 1 = k + 8 by omega, show k + 9 - 2 = k + 7 by omega, show k + 9 - 3 = k + 6 by omega, show k + 9 - 4 = k + 5 by omega, show k + 9 - 5 = k + 4 by omega, show k + 9 - 6 = k + 3 by omega, show k + 9 - 7 = k + 2 by omega, show k + 9 - 8 = k + 1 by omega, show k + 9 - 9 = k + 0 by omega]
    push_cast
    ring

theorem gf (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (0 + M) = Lin RC A (0 + M)) (hval : ∀ N ≤ 11, f (N + 1) = gL AV (N + 1)) : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (f n : ℚ)) * (1 - X) ^ 9 =
    X * (5 - 20 * X + 47 * X ^ 2 - 76 * X ^ 3 + 85 * X ^ 4 - 62 * X ^ 5 + 29 * X ^ 6 - 8 * X ^ 7 + X ^ 8) := by
  have v1 : f 1 = 5 := hval 0 (by norm_num)
  have v2 : f 2 = 25 := hval 1 (by norm_num)
  have v3 : f 3 = 92 := hval 2 (by norm_num)
  have v4 : f 4 = 272 := hval 3 (by norm_num)
  have v5 : f 5 = 691 := hval 4 (by norm_num)
  have v6 : f 6 = 1573 := hval 5 (by norm_num)
  have v7 : f 7 = 3296 := hval 6 (by norm_num)
  have v8 : f 8 = 6472 := hval 7 (by norm_num)
  have v9 : f 9 = 12058 := hval 8 (by norm_num)
  have v10 : f 10 = 21506 := hval 9 (by norm_num)
  have v11 : f 11 = 36961 := hval 10 (by norm_num)
  have v12 : f 12 = 61517 := hval 11 (by norm_num)
  set F : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (f n : ℚ)) with hF
  have hmul : F * (1 - X) ^ 9 = F - C (9 : ℚ) * (X ^ 1 * F) + C (36 : ℚ) * (X ^ 2 * F) - C (84 : ℚ) * (X ^ 3 * F) + C (126 : ℚ) * (X ^ 4 * F) - C (126 : ℚ) * (X ^ 5 * F) + C (84 : ℚ) * (X ^ 6 * F) - C (36 : ℚ) * (X ^ 7 * F) + C (9 : ℚ) * (X ^ 8 * F) - X ^ 9 * F := by
    (try simp only [map_ofNat]); ring
  have hnum : (X * (5 - 20 * X + 47 * X ^ 2 - 76 * X ^ 3 + 85 * X ^ 4 - 62 * X ^ 5 + 29 * X ^ 6 - 8 * X ^ 7 + X ^ 8) : PowerSeries ℚ) = C (5 : ℚ) * X ^ 1 - C (20 : ℚ) * X ^ 2 + C (47 : ℚ) * X ^ 3 - C (76 : ℚ) * X ^ 4 + C (85 : ℚ) * X ^ 5 - C (62 : ℚ) * X ^ 6 + C (29 : ℚ) * X ^ 7 - C (8 : ℚ) * X ^ 8 + X ^ 9 := by
    (try simp only [map_ofNat]); ring
  rw [hmul, hnum]
  ext n
  simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, hF, coeff_mk]
  by_cases hn : 10 ≤ n
  · simp only [if_pos (show 1 ≤ n by omega),
      if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega),
      if_pos (show 4 ≤ n by omega),
      if_pos (show 5 ≤ n by omega),
      if_pos (show 6 ≤ n by omega),
      if_pos (show 7 ≤ n by omega),
      if_pos (show 8 ≤ n by omega),
      if_pos (show 9 ≤ n by omega),
      if_neg (show n ≠ 1 by omega),
      if_neg (show n ≠ 2 by omega),
      if_neg (show n ≠ 3 by omega),
      if_neg (show n ≠ 4 by omega),
      if_neg (show n ≠ 5 by omega),
      if_neg (show n ≠ 6 by omega),
      if_neg (show n ≠ 7 by omega),
      if_neg (show n ≠ 8 by omega),
      if_neg (show n ≠ 9 by omega),
      if_neg (show n ≠ 0 by omega),
      if_neg (show n - 1 ≠ 0 by omega),
      if_neg (show n - 2 ≠ 0 by omega),
      if_neg (show n - 3 ≠ 0 by omega),
      if_neg (show n - 4 ≠ 0 by omega),
      if_neg (show n - 5 ≠ 0 by omega),
      if_neg (show n - 6 ≠ 0 by omega),
      if_neg (show n - 7 ≠ 0 by omega),
      if_neg (show n - 8 ≠ 0 by omega),
      if_neg (show n - 9 ≠ 0 by omega),
      mul_zero, sub_zero, add_zero, mul_one, neg_zero]
    rw [recQ f A ha hid hval n (by omega)]
    ring
  · interval_cases n <;> norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12]

theorem final (f A : ℕ → ℕ) (ha : ∀ N, f (N + 1) = A N) (hid : ∀ M, Lin LC A (0 + M) = Lin RC A (0 + M)) (hval : ∀ N ≤ 11, f (N + 1) = gL AV (N + 1)) :
    (∀ n : ℕ, 0 < n → (f n : ℚ) = (1/40320) * (n : ℚ) ^ 8 + (1/3360) * (n : ℚ) ^ 7 + (1/192) * (n : ℚ) ^ 6 + (1/16) * (n : ℚ) ^ 5 + (223/640) * (n : ℚ) ^ 4 + (149/160) * (n : ℚ) ^ 3 + (3319/2016) * (n : ℚ) ^ 2 + (169/168) * (n : ℚ) + 1) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (f n : ℚ)) * (1 - X) ^ 9 =
      X * (5 - 20 * X + 47 * X ^ 2 - 76 * X ^ 3 + 85 * X ^ 4 - 62 * X ^ 5 + 29 * X ^ 6 - 8 * X ^ 7 + X ^ 8) ∧
    ∀ n : ℕ, 9 < n → (f n : ℤ) = 9 * f (n - 1) - 36 * f (n - 2) + 84 * f (n - 3) - 126 * f (n - 4) + 126 * f (n - 5) - 84 * f (n - 6) + 36 * f (n - 7) - 9 * f (n - 8) + f (n - 9) :=
  ⟨fun n hn => poly f A ha hid hval n hn, gf f A ha hid hval, fun n hn => recZ f A ha hid hval n hn⟩

end PA224148

theorem OMA.solution : type_of% @OMA.S_oeis_a224148.main :=
  PA224148.final _ _ PA224148.a_eq PA224148.hid PA224148.hval
