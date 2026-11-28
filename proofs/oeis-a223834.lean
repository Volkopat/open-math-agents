import OMAStatements.S_oeis_a223834
import Mathlib

/-!
Proof of A223834 (Barker's conjectured g.f. and recurrence), for the statement with arrays as
lists of rows. Credit: @prathameshnium (agent: Claude Code, model claude-opus-5-5)

Method: a generic library (below) reads arrays row by row with a finite automaton whose state is the
last row and, for every line through it, whether that line has already descended; it proves that
the automaton accepts exactly the arrays of the statement. The table (31 live states) is checked by
`decide +kernel`; the counts satisfy (E - 1)^5 = 0 from shift 2 on (kernel-checked at one shift,
lifted to all), which gives the polynomial closed form, the recurrence and the g.f.
-/

/-!
Generic transfer-matrix toolkit (automaton form).

Words over a finite alphabet `A` are read by a deterministic automaton on states `ℕ`
(`δ : ℕ → A → ℕ`, acceptance `acc : ℕ → Bool`).
* `card_run`: the number of accepted words of length `n` from state `q` is `cnt n q`.
* `cntV_eq`: a list-valued (memoised) version of `cnt`, for kernel computation.
* `cnt_rec`: a linear relation checked on a `δ`-closed set of states at one shift holds at all shifts.
* `window`: if `x` satisfies a linear recurrence of order `D`, any other linear recurrence that holds
  for the first `D` shifts holds for all shifts.
-/

namespace TMLib

open Finset

section automaton

variable {A : Type} [Fintype A] [DecidableEq A] (δ : ℕ → A → ℕ) (acc : ℕ → Bool)

def run : ℕ → List A → ℕ
  | q, [] => q
  | q, a :: w => run (δ q a) w

def cnt : ℕ → ℕ → ℕ
  | 0, q => if acc q then 1 else 0
  | n + 1, q => ∑ a : A, cnt n (δ q a)

theorem cnt_succ (n q : ℕ) : cnt δ acc (n + 1) q = ∑ a : A, cnt δ acc n (δ q a) := rfl

theorem card_run (n : ℕ) : ∀ q : ℕ,
    (univ.filter (fun w : Fin n → A => acc (run δ q (List.ofFn w)) = true)).card =
      cnt δ acc n q := by
  induction n with
  | zero =>
    intro q
    by_cases h : acc q = true
    · simp [run, cnt, h]
    · simp [run, cnt, h]
  | succ n ih =>
    intro q
    rw [cnt_succ, ← Finset.sum_congr rfl (fun a _ => ih (δ q a))]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun w : Fin (n + 1) → A => w 0) (t := univ)
      (fun _ _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.filter_filter]
    apply Finset.card_nbij' (fun w => Fin.tail w) (fun t => Fin.cons a t)
    · intro w hw
      simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at hw ⊢
      obtain ⟨h1, h2⟩ := hw
      rw [List.ofFn_succ, run, h2] at h1
      exact h1
    · intro t ht
      simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at ht ⊢
      refine ⟨?_, by simp⟩
      rw [List.ofFn_succ, run]
      simpa using ht
    · intro w hw
      simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_ofPred_eq] at hw
      rw [← hw.2]
      exact Fin.cons_self_tail w
    · intro t _
      simp

/-- Memoised `cnt` on the states `0, …, N-1`, as a list. -/
def cntV (N : ℕ) : ℕ → List ℕ
  | 0 => (List.range N).map (fun q => if acc q then 1 else 0)
  | n + 1 => (List.range N).map (fun q => ∑ a : A, (cntV N n).getD (δ q a) 0)

theorem cntV_eq (N : ℕ) (hN : ∀ q < N, ∀ a : A, δ q a < N) (n : ℕ) :
    ∀ q < N, (cntV δ acc N n).getD q 0 = cnt δ acc n q := by
  induction n with
  | zero =>
    intro q hq
    simp [cntV, cnt, List.getD_eq_getElem?_getD, hq]
  | succ n ih =>
    intro q hq
    simp only [cntV, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hq,
      Option.map_some, Option.getD_some]
    rw [cnt_succ]
    apply Finset.sum_congr rfl
    intro a _
    have := ih (δ q a) (hN q hq a)
    simpa [List.getD_eq_getElem?_getD] using this

theorem cnt_rec (S : Finset ℕ) (hS : ∀ q ∈ S, ∀ a : A, δ q a ∈ S) (d : ℕ) (c : ℕ → ℤ) (J : ℕ)
    (h : ∀ q ∈ S, (cnt δ acc (J + d) q : ℤ) = ∑ i ∈ range d, c i * cnt δ acc (J + i) q) :
    ∀ n, ∀ q ∈ S, (cnt δ acc (n + J + d) q : ℤ) = ∑ i ∈ range d, c i * cnt δ acc (n + J + i) q := by
  intro n
  induction n with
  | zero => intro q hq; simpa using h q hq
  | succ n ih =>
    intro q hq
    rw [show n + 1 + J + d = (n + J + d) + 1 by ring, cnt_succ]
    push_cast
    rw [Finset.sum_congr rfl (fun a _ => ih (δ q a) (hS q hq a)), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.mul_sum, show n + 1 + J + i = (n + J + i) + 1 by ring, cnt_succ]
    push_cast
    rfl

end automaton

theorem window (x : ℕ → ℤ) (D : ℕ) (q : ℕ → ℤ)
    (hx : ∀ n, x (n + D) = ∑ i ∈ range D, q i * x (n + i))
    (e : ℕ) (p : ℕ → ℤ)
    (h0 : ∀ n < D, x (n + e) = ∑ j ∈ range e, p j * x (n + j)) :
    ∀ n, x (n + e) = ∑ j ∈ range e, p j * x (n + j) := by
  let b : ℕ → ℤ := fun n => x (n + e) - ∑ j ∈ range e, p j * x (n + j)
  have hb : ∀ n, b n = x (n + e) - ∑ j ∈ range e, p j * x (n + j) := fun n => rfl
  have hbrec : ∀ n, b (n + D) = ∑ i ∈ range D, q i * b (n + i) := by
    intro n
    rw [hb, show n + D + e = (n + e) + D by ring, hx (n + e)]
    have e2 : ∀ j, x (n + D + j) = ∑ i ∈ range D, q i * x (n + j + i) := by
      intro j
      rw [show n + D + j = (n + j) + D by ring, hx (n + j)]
    simp only [e2, hb, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      rw [show n + e + i = n + i + e by ring]
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [show n + j + i = n + i + j by ring]
      ring
  have hz : ∀ n, b n = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hn : n < D
      · rw [hb, h0 n hn, sub_self]
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + D := ⟨n - D, by omega⟩
        rw [hbrec m]
        apply Finset.sum_eq_zero
        intro i hi
        rw [ih (m + i) (by simp at hi; omega), mul_zero]
  intro n
  have := hz n
  rw [hb] at this
  linarith

end TMLib


/-!
Row-by-row step lemmas for "every line is unimodal" conditions on arrays `X : ℕ → ℕ → ℕ`
(rows `< m`, columns `< k`). A line of slope `s ∈ {-1, 0, 1}` through `(i, j)` meets row `t`
in column `j + s * (i - t)`: `s = 0` columns, `s = 1` antidiagonals (`i + j` constant),
`s = -1` diagonals (`j - i` constant). `Y` is `X` with one more row `r` (row index `m`).
-/

namespace UniLib

/-- No valley: the middle value is not strictly below both outer values. -/
def NV (u v w : ℕ) : Prop := ¬ (v < u ∧ v < w)

/-- Every line of slope `s` is unimodal (no valley among three of its cells). -/
def Uni (s : ℤ) (m k : ℕ) (X : ℕ → ℕ → ℕ) : Prop :=
  ∀ i1 i2 i3 j1 j2 j3 : ℕ, i1 < i2 → i2 < i3 → i3 < m → j1 < k → j2 < k → j3 < k →
    (j1 : ℤ) - j2 = s * ((i2 : ℤ) - i1) → (j2 : ℤ) - j3 = s * ((i3 : ℤ) - i2) →
    NV (X i1 j1) (X i2 j2) (X i3 j3)

/-- The line of slope `s` through the cell `(m - 1, j)` of the last row has a strict descent. -/
def Fl (s : ℤ) (m k : ℕ) (X : ℕ → ℕ → ℕ) (j : ℕ) : Prop :=
  ∃ i1 i2 j1 j2 : ℕ, i1 < i2 ∧ i2 < m ∧ j1 < k ∧ j2 < k ∧ (j1 : ℤ) - j2 = s * ((i2 : ℤ) - i1) ∧
    (j2 : ℤ) - j = s * (((m : ℤ) - 1) - i2) ∧ X i2 j2 < X i1 j1

/-- Columns are nondecreasing downwards. -/
def ColND (m k : ℕ) (X : ℕ → ℕ → ℕ) : Prop :=
  ∀ i1 i2 j : ℕ, i1 < i2 → i2 < m → j < k → X i1 j ≤ X i2 j

/-- A row is unimodal. -/
def RowOK (k : ℕ) (r : ℕ → ℕ) : Prop :=
  ∀ j3, j3 < k → ∀ j2, j2 < j3 → ∀ j1, j1 < j2 → NV (r j1) (r j2) (r j3)

def RowsOK (m k : ℕ) (X : ℕ → ℕ → ℕ) : Prop := ∀ i < m, RowOK k (X i)

section step

variable {s : ℤ} {m k : ℕ} {X Y : ℕ → ℕ → ℕ} {r : ℕ → ℕ}

theorem uni_step (hs : s = -1 ∨ s = 0 ∨ s = 1) (hm : 1 ≤ m)
    (hY1 : ∀ i < m, ∀ j < k, Y i j = X i j) (hY2 : ∀ j < k, Y m j = r j) :
    Uni s (m + 1) k Y ↔ Uni s m k X ∧
      ∀ j, j < k → ∀ j', j' < k → (j' : ℤ) = j + s → ¬ (Fl s m k X j' ∧ X (m - 1) j' < r j) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i1 i2 i3 j1 j2 j3 h12 h23 h3 hj1 hj2 hj3 e1 e2
      have := h i1 i2 i3 j1 j2 j3 h12 h23 (by omega) hj1 hj2 hj3 e1 e2
      rwa [hY1 i1 (by omega) j1 hj1, hY1 i2 (by omega) j2 hj2, hY1 i3 h3 j3 hj3] at this
    · rintro j hj j' hj' hjj ⟨⟨i1, i2, j1, j2, h12, h2m, hj1, hj2, e1, e2, hlt⟩, hlast⟩
      by_cases hi2 : i2 = m - 1
      · subst hi2
        have hjj2 : j2 = j' := by
          have : ((m : ℤ) - 1) - ((m - 1 : ℕ) : ℤ) = 0 := by omega
          rw [this, mul_zero] at e2; omega
        subst hjj2
        have := h i1 (m - 1) m j1 j2 j h12 (by omega) (by omega) hj1 hj2 hj e1 (by
          rcases hs with rfl | rfl | rfl <;> push_cast [Nat.cast_sub hm] <;> omega)
        rw [hY1 i1 (by omega) j1 hj1, hY1 (m - 1) (by omega) j2 hj2, hY2 j hj] at this
        exact this ⟨hlt, hlast⟩
      · by_cases hc : X i2 j2 < X (m - 1) j'
        · have := h i1 i2 (m - 1) j1 j2 j' h12 (by omega) (by omega) hj1 hj2 hj' e1 (by
            rcases hs with rfl | rfl | rfl <;> push_cast [Nat.cast_sub hm] at e2 ⊢ <;> omega)
          rw [hY1 i1 (by omega) j1 hj1, hY1 i2 (by omega) j2 hj2, hY1 (m - 1) (by omega) j' hj'] at this
          exact this ⟨hlt, hc⟩
        · have := h i1 (m - 1) m j1 j' j (by omega) (by omega) (by omega) hj1 hj' hj (by
            rcases hs with rfl | rfl | rfl <;> push_cast [Nat.cast_sub hm] at e1 e2 ⊢ <;> omega) (by
            rcases hs with rfl | rfl | rfl <;> push_cast [Nat.cast_sub hm] at hjj ⊢ <;> omega)
          rw [hY1 i1 (by omega) j1 hj1, hY1 (m - 1) (by omega) j' hj', hY2 j hj] at this
          exact this ⟨by omega, hlast⟩
  · rintro ⟨hU, hL⟩ i1 i2 i3 j1 j2 j3 h12 h23 h3 hj1 hj2 hj3 e1 e2
    by_cases hi3 : i3 < m
    · rw [hY1 i1 (by omega) j1 hj1, hY1 i2 (by omega) j2 hj2, hY1 i3 hi3 j3 hj3]
      exact hU i1 i2 i3 j1 j2 j3 h12 h23 hi3 hj1 hj2 hj3 e1 e2
    · have hi3m : i3 = m := by omega
      subst hi3m
      rw [hY1 i1 (by omega) j1 hj1, hY1 i2 (by omega) j2 hj2, hY2 j3 hj3]
      rintro ⟨hv1, hv2⟩
      obtain ⟨j', hj'⟩ : ∃ j' : ℕ, (j' : ℤ) = j3 + s :=
        ⟨(j3 + s).toNat, by rcases hs with rfl | rfl | rfl <;> omega⟩
      have hj'k : j' < k := by rcases hs with rfl | rfl | rfl <;> omega
      have hfl : Fl s i3 k X j' := ⟨i1, i2, j1, j2, h12, h23, hj1, hj2, e1, by
        rcases hs with rfl | rfl | rfl <;> omega, hv1⟩
      apply hL j3 hj3 j' hj'k hj' ⟨hfl, ?_⟩
      by_cases hi2 : i2 = i3 - 1
      · subst hi2
        have : j2 = j' := by rcases hs with rfl | rfl | rfl <;> omega
        subst this; exact hv2
      · have := hU i1 i2 (i3 - 1) j1 j2 j' h12 (by omega) (by omega) hj1 hj2 hj'k e1 (by
          rcases hs with rfl | rfl | rfl <;> omega)
        unfold NV at this
        omega

theorem fl_step (hs : s = -1 ∨ s = 0 ∨ s = 1) (hm : 1 ≤ m)
    (hY1 : ∀ i < m, ∀ j < k, Y i j = X i j) (hY2 : ∀ j < k, Y m j = r j) (j : ℕ) (hj : j < k) :
    Fl s (m + 1) k Y j ↔ ∃ j', j' < k ∧ (j' : ℤ) = j + s ∧ (Fl s m k X j' ∨ r j < X (m - 1) j') := by
  constructor
  · rintro ⟨i1, i2, j1, j2, h12, h2m, hj1, hj2, e1, e2, hlt⟩
    obtain ⟨j', hj'⟩ : ∃ j' : ℕ, (j' : ℤ) = j + s :=
      ⟨(j + s).toNat, by rcases hs with rfl | rfl | rfl <;> push_cast at e1 e2 <;> omega⟩
    have hj'k : j' < k := by rcases hs with rfl | rfl | rfl <;> push_cast at e1 e2 <;> omega
    refine ⟨j', hj'k, hj', ?_⟩
    by_cases hi2 : i2 < m
    · left
      rw [hY1 i1 (by omega) j1 hj1, hY1 i2 hi2 j2 hj2] at hlt
      exact ⟨i1, i2, j1, j2, h12, hi2, hj1, hj2, e1, by
        rcases hs with rfl | rfl | rfl <;> push_cast at e2 ⊢ <;> omega, hlt⟩
    · have hi2m : i2 = m := by omega
      subst hi2m
      have hjj : j2 = j := by rcases hs with rfl | rfl | rfl <;> push_cast at e2 <;> omega
      subst hjj
      rw [hY1 i1 (by omega) j1 hj1, hY2 j2 hj2] at hlt
      by_cases hc : r j2 < X (i2 - 1) j'
      · right; exact hc
      · left
        have hi1 : i1 < i2 - 1 := by
          by_contra hcon
          have h1 : i1 = i2 - 1 := by omega
          subst h1
          have : j1 = j' := by rcases hs with rfl | rfl | rfl <;> push_cast [Nat.cast_sub hm] at e1 ⊢ <;> omega
          subst this; omega
        exact ⟨i1, i2 - 1, j1, j', hi1, by omega, hj1, hj'k, by
          rcases hs with rfl | rfl | rfl <;> push_cast [Nat.cast_sub hm] at e1 ⊢ <;> omega, by
          push_cast [Nat.cast_sub hm]; ring, by omega⟩
  · rintro ⟨j', hj'k, hj', h | h⟩
    · obtain ⟨i1, i2, j1, j2, h12, h2m, hj1, hj2, e1, e2, hlt⟩ := h
      refine ⟨i1, i2, j1, j2, h12, by omega, hj1, hj2, e1, by
        rcases hs with rfl | rfl | rfl <;> push_cast at e2 ⊢ <;> omega, ?_⟩
      rw [hY1 i1 (by omega) j1 hj1, hY1 i2 h2m j2 hj2]; exact hlt
    · refine ⟨m - 1, m, j', j, by omega, by omega, hj'k, hj, by
        rcases hs with rfl | rfl | rfl <;> push_cast [Nat.cast_sub hm] <;> omega, by
        push_cast; ring, ?_⟩
      rw [hY1 (m - 1) (by omega) j' hj'k, hY2 j hj]; exact h

theorem colnd_step (hm : 1 ≤ m)
    (hY1 : ∀ i < m, ∀ j < k, Y i j = X i j) (hY2 : ∀ j < k, Y m j = r j) :
    ColND (m + 1) k Y ↔ ColND m k X ∧ ∀ j < k, X (m - 1) j ≤ r j := by
  constructor
  · intro h
    refine ⟨fun i1 i2 j h12 h2 hj => ?_, fun j hj => ?_⟩
    · have := h i1 i2 j h12 (by omega) hj
      rwa [hY1 i1 (by omega) j hj, hY1 i2 h2 j hj] at this
    · have := h (m - 1) m j (by omega) (by omega) hj
      rwa [hY1 (m - 1) (by omega) j hj, hY2 j hj] at this
  · rintro ⟨hC, hL⟩ i1 i2 j h12 h2 hj
    by_cases hi2 : i2 < m
    · rw [hY1 i1 (by omega) j hj, hY1 i2 hi2 j hj]; exact hC i1 i2 j h12 hi2 hj
    · have : i2 = m := by omega
      subst this
      rw [hY1 i1 (by omega) j hj, hY2 j hj]
      by_cases h1 : i1 = i2 - 1
      · subst h1; exact hL j hj
      · exact le_trans (hC i1 (i2 - 1) j (by omega) (by omega) hj) (hL j hj)

theorem rows_step (hY1 : ∀ i < m, ∀ j < k, Y i j = X i j) (hY2 : ∀ j < k, Y m j = r j) :
    RowsOK (m + 1) k Y ↔ RowsOK m k X ∧ RowOK k r := by
  have hrow : ∀ i < m, (RowOK k (Y i) ↔ RowOK k (X i)) := by
    intro i hi
    unfold RowOK
    constructor
    · intro h j3 c j2 b j1 a
      have := h j3 c j2 b j1 a
      rwa [hY1 i hi j1 (by omega), hY1 i hi j2 (by omega), hY1 i hi j3 c] at this
    · intro h j3 c j2 b j1 a
      rw [hY1 i hi j1 (by omega), hY1 i hi j2 (by omega), hY1 i hi j3 c]
      exact h j3 c j2 b j1 a
  have hlast : RowOK k (Y m) ↔ RowOK k r := by
    unfold RowOK
    constructor
    · intro h j3 c j2 b j1 a
      have := h j3 c j2 b j1 a
      rwa [hY2 j1 (by omega), hY2 j2 (by omega), hY2 j3 c] at this
    · intro h j3 c j2 b j1 a
      rw [hY2 j1 (by omega), hY2 j2 (by omega), hY2 j3 c]
      exact h j3 c j2 b j1 a
  constructor
  · intro h
    exact ⟨fun i hi => (hrow i hi).1 (h i (by omega)), hlast.1 (h m (by omega))⟩
  · rintro ⟨hR, hr⟩ i hi
    by_cases him : i < m
    · exact (hrow i him).2 (hR i him)
    · have : i = m := by omega
      subst this; exact hlast.2 hr

end step

/-! ## The family predicate, one row at a time -/

/-- Local "no rise after a descent" condition for lines of slope `s` entering row `r`. -/
def LC (k : ℕ) (s : ℤ) (L : ℕ → ℕ) (f : ℕ → Prop) (r : ℕ → ℕ) : Prop :=
  ∀ j, j < k → ∀ j', j' < k → (j' : ℤ) = j + s → ¬ (f j' ∧ L j' < r j)

/-- New descent flag of the line of slope `s` through column `j` of the new row `r`. -/
def NF (k : ℕ) (s : ℤ) (L : ℕ → ℕ) (f : ℕ → Prop) (r : ℕ → ℕ) (j : ℕ) : Prop :=
  ∃ j', j' < k ∧ (j' : ℤ) = j + s ∧ (f j' ∨ r j < L j')

/-- Rows unimodal; columns unimodal (`cu`) or nondecreasing; diagonals (`dg`) and antidiagonals
(`an`) unimodal when asked. -/
def P (cu dg an : Bool) (m k : ℕ) (X : ℕ → ℕ → ℕ) : Prop :=
  RowsOK m k X ∧ (if cu = true then Uni 0 m k X else ColND m k X) ∧
    (dg = true → Uni (-1) m k X) ∧ (an = true → Uni 1 m k X)

def LocOK (cu dg an : Bool) (k : ℕ) (L : ℕ → ℕ) (fc fd fa : ℕ → Prop) (r : ℕ → ℕ) : Prop :=
  RowOK k r ∧ (if cu = true then LC k 0 L fc r else ∀ j, j < k → L j ≤ r j) ∧
    (dg = true → LC k (-1) L fd r) ∧ (an = true → LC k 1 L fa r)

theorem P_step {cu dg an : Bool} {m k : ℕ} {X Y : ℕ → ℕ → ℕ} {r : ℕ → ℕ} (hm : 1 ≤ m)
    (hY1 : ∀ i < m, ∀ j < k, Y i j = X i j) (hY2 : ∀ j < k, Y m j = r j) :
    P cu dg an (m + 1) k Y ↔ P cu dg an m k X ∧
      LocOK cu dg an k (X (m - 1)) (Fl 0 m k X) (Fl (-1) m k X) (Fl 1 m k X) r := by
  have hR := rows_step hY1 hY2
  have hC0 := uni_step (s := 0) (by norm_num) hm hY1 hY2
  have hCn := colnd_step hm hY1 hY2
  have hD := uni_step (s := -1) (by norm_num) hm hY1 hY2
  have hA := uni_step (s := 1) (by norm_num) hm hY1 hY2
  have hC : (if cu = true then Uni 0 (m + 1) k Y else ColND (m + 1) k Y) ↔
      (if cu = true then Uni 0 m k X else ColND m k X) ∧
        (if cu = true then LC k 0 (X (m - 1)) (Fl 0 m k X) r else ∀ j, j < k → X (m - 1) j ≤ r j) := by
    cases cu
    · rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]; exact hCn
    · rw [if_pos rfl, if_pos rfl, if_pos rfl]; exact hC0
  have hDg : (dg = true → Uni (-1) (m + 1) k Y) ↔
      (dg = true → Uni (-1) m k X) ∧ (dg = true → LC k (-1) (X (m - 1)) (Fl (-1) m k X) r) := by
    cases dg
    · exact ⟨fun _ => ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩,
        fun _ h => absurd h (by decide)⟩
    · exact ⟨fun h => ⟨fun _ => (hD.1 (h rfl)).1, fun _ => (hD.1 (h rfl)).2⟩,
        fun h _ => hD.2 ⟨h.1 rfl, h.2 rfl⟩⟩
  have hAn : (an = true → Uni 1 (m + 1) k Y) ↔
      (an = true → Uni 1 m k X) ∧ (an = true → LC k 1 (X (m - 1)) (Fl 1 m k X) r) := by
    cases an
    · exact ⟨fun _ => ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩,
        fun _ h => absurd h (by decide)⟩
    · exact ⟨fun h => ⟨fun _ => (hA.1 (h rfl)).1, fun _ => (hA.1 (h rfl)).2⟩,
        fun h _ => hA.2 ⟨h.1 rfl, h.2 rfl⟩⟩
  unfold P LocOK
  rw [hR, hC, hDg, hAn]
  exact ⟨fun ⟨⟨a, b⟩, ⟨c, d⟩, ⟨e, f⟩, ⟨g, h⟩⟩ => ⟨⟨a, c, e, g⟩, ⟨b, d, f, h⟩⟩,
    fun ⟨⟨a, c, e, g⟩, ⟨b, d, f, h⟩⟩ => ⟨⟨a, b⟩, ⟨c, d⟩, ⟨e, f⟩, ⟨g, h⟩⟩⟩

theorem P_one {cu dg an : Bool} {k : ℕ} {Y : ℕ → ℕ → ℕ} {r : ℕ → ℕ} (hY : ∀ j < k, Y 0 j = r j) :
    P cu dg an 1 k Y ↔ RowOK k r := by
  have hrow : RowOK k (Y 0) ↔ RowOK k r := by
    unfold RowOK
    constructor
    · intro h j3 c j2 b j1 a
      have := h j3 c j2 b j1 a
      rwa [hY j1 (by omega), hY j2 (by omega), hY j3 c] at this
    · intro h j3 c j2 b j1 a
      rw [hY j1 (by omega), hY j2 (by omega), hY j3 c]
      exact h j3 c j2 b j1 a
  have hU : ∀ s, Uni s 1 k Y := fun s i1 i2 i3 _ _ _ h12 h23 h3 => by omega
  have hC : ColND 1 k Y := fun i1 i2 _ h12 h2 => by omega
  unfold P
  constructor
  · rintro ⟨h, -⟩; exact hrow.1 (h 0 (by omega))
  · intro h
    refine ⟨fun i hi => ?_, ?_, fun _ => hU _, fun _ => hU _⟩
    · have : i = 0 := by omega
      subst this; exact hrow.2 h
    · cases cu <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> first | exact hU _ | exact hC

theorem Fl_one {s : ℤ} {k : ℕ} {Y : ℕ → ℕ → ℕ} (j : ℕ) : ¬ Fl s 1 k Y j := by
  rintro ⟨i1, i2, _, _, h12, h2, -⟩; omega

theorem LC_congr {k : ℕ} {s : ℤ} {L L' : ℕ → ℕ} {f f' : ℕ → Prop} {r : ℕ → ℕ}
    (hL : ∀ j < k, L j = L' j) (hf : ∀ j < k, (f j ↔ f' j)) : LC k s L f r ↔ LC k s L' f' r := by
  unfold LC
  constructor
  · intro h j hj j' hj' e ⟨h1, h2⟩
    exact h j hj j' hj' e ⟨(hf j' hj').2 h1, by rw [hL j' hj']; exact h2⟩
  · intro h j hj j' hj' e ⟨h1, h2⟩
    exact h j hj j' hj' e ⟨(hf j' hj').1 h1, by rw [← hL j' hj']; exact h2⟩

theorem NF_congr {k : ℕ} {s : ℤ} {L L' : ℕ → ℕ} {f f' : ℕ → Prop} {r : ℕ → ℕ} (j : ℕ)
    (hL : ∀ j < k, L j = L' j) (hf : ∀ j < k, (f j ↔ f' j)) : NF k s L f r j ↔ NF k s L' f' r j := by
  unfold NF
  constructor
  · rintro ⟨j', hj', e, h⟩
    refine ⟨j', hj', e, ?_⟩
    rcases h with h | h
    · exact Or.inl ((hf j' hj').1 h)
    · exact Or.inr (by rw [← hL j' hj']; exact h)
  · rintro ⟨j', hj', e, h⟩
    refine ⟨j', hj', e, ?_⟩
    rcases h with h | h
    · exact Or.inl ((hf j' hj').2 h)
    · exact Or.inr (by rw [hL j' hj']; exact h)

theorem LocOK_congr {cu dg an : Bool} {k : ℕ} {L L' : ℕ → ℕ} {fc fd fa fc' fd' fa' : ℕ → Prop}
    {r : ℕ → ℕ} (hL : ∀ j < k, L j = L' j) (hc : cu = true → ∀ j < k, (fc j ↔ fc' j))
    (hd : dg = true → ∀ j < k, (fd j ↔ fd' j)) (ha : an = true → ∀ j < k, (fa j ↔ fa' j)) :
    LocOK cu dg an k L fc fd fa r ↔ LocOK cu dg an k L' fc' fd' fa' r := by
  unfold LocOK
  have hmono : (∀ j, j < k → L j ≤ r j) ↔ (∀ j, j < k → L' j ≤ r j) := by
    constructor
    · intro h j hj; rw [← hL j hj]; exact h j hj
    · intro h j hj; rw [hL j hj]; exact h j hj
  have h1 : (if cu = true then LC k 0 L fc r else ∀ j, j < k → L j ≤ r j) ↔
      (if cu = true then LC k 0 L' fc' r else ∀ j, j < k → L' j ≤ r j) := by
    cases cu
    · rw [if_neg (by decide), if_neg (by decide)]; exact hmono
    · rw [if_pos rfl, if_pos rfl]; exact LC_congr hL (hc rfl)
  have h2 : (dg = true → LC k (-1) L fd r) ↔ (dg = true → LC k (-1) L' fd' r) := by
    cases dg
    · exact ⟨fun _ h => absurd h (by decide), fun _ h => absurd h (by decide)⟩
    · exact ⟨fun h _ => (LC_congr hL (hd rfl)).1 (h rfl), fun h _ => (LC_congr hL (hd rfl)).2 (h rfl)⟩
  have h3 : (an = true → LC k 1 L fa r) ↔ (an = true → LC k 1 L' fa' r) := by
    cases an
    · exact ⟨fun _ h => absurd h (by decide), fun _ h => absurd h (by decide)⟩
    · exact ⟨fun h _ => (LC_congr hL (ha rfl)).1 (h rfl), fun h _ => (LC_congr hL (ha rfl)).2 (h rfl)⟩
  exact and_congr Iff.rfl (and_congr h1 (and_congr h2 h3))

/-! ## Table automaton (generated data) and the bridge -/

section table

variable (cu dg an : Bool) (k b R : ℕ) (dl rowL : List (List ℕ)) (fcL fdL faL : List (List Bool))

def δt (q c : ℕ) : ℕ := (dl.getD q []).getD c R
def Lq (q j : ℕ) : ℕ := (rowL.getD q []).getD j 0
def Fq (fl : List (List Bool)) (q j : ℕ) : Prop := (fl.getD q []).getD j false = true
/-- Digit `j` of the row code `c` in base `b`. -/
def rc (c j : ℕ) : ℕ := c / b ^ j % b

instance (fl : List (List Bool)) (q j : ℕ) : Decidable (Fq fl q j) := by unfold Fq; infer_instance
instance (k : ℕ) (r : ℕ → ℕ) : Decidable (RowOK k r) := by unfold RowOK NV; infer_instance
instance (k : ℕ) (s : ℤ) (L : ℕ → ℕ) (f : ℕ → Prop) [DecidablePred f] (r : ℕ → ℕ) :
    Decidable (LC k s L f r) := by unfold LC; infer_instance
instance (k : ℕ) (s : ℤ) (L : ℕ → ℕ) (f : ℕ → Prop) [DecidablePred f] (r : ℕ → ℕ) (j : ℕ) :
    Decidable (NF k s L f r j) := by unfold NF; infer_instance
instance (cu dg an : Bool) (k : ℕ) (L : ℕ → ℕ) (fc fd fa : ℕ → Prop) [DecidablePred fc]
    [DecidablePred fd] [DecidablePred fa] (r : ℕ → ℕ) : Decidable (LocOK cu dg an k L fc fd fa r) := by
  unfold LocOK; infer_instance

/-- First row `c` read from the start state `0`. -/
def StartOK (c : ℕ) : Prop :=
  (δt R dl 0 c = R ↔ ¬ RowOK k (rc b c)) ∧
    (δt R dl 0 c ≠ R → 1 ≤ δt R dl 0 c ∧ δt R dl 0 c < R ∧ ∀ j, j < k →
      Lq rowL (δt R dl 0 c) j = rc b c j ∧ ¬ Fq fcL (δt R dl 0 c) j ∧ ¬ Fq fdL (δt R dl 0 c) j ∧
        ¬ Fq faL (δt R dl 0 c) j)

/-- Last row and flags of the successor state `q'`, column `j`. -/
def FlagOK (q c q' j : ℕ) : Prop :=
  Lq rowL q' j = rc b c j ∧
    (cu = true → (Fq fcL q' j ↔ NF k 0 (Lq rowL q) (Fq fcL q) (rc b c) j)) ∧
    (dg = true → (Fq fdL q' j ↔ NF k (-1) (Lq rowL q) (Fq fdL q) (rc b c) j)) ∧
    (an = true → (Fq faL q' j ↔ NF k 1 (Lq rowL q) (Fq faL q) (rc b c) j))

/-- Row `c` read from a live state `q`. -/
def StepOK (q c : ℕ) : Prop :=
  (δt R dl q c = R ↔ ¬ LocOK cu dg an k (Lq rowL q) (Fq fcL q) (Fq fdL q) (Fq faL q) (rc b c)) ∧
    (δt R dl q c ≠ R → 1 ≤ δt R dl q c ∧ δt R dl q c < R ∧ ∀ j, j < k →
      FlagOK cu dg an k b rowL fcL fdL faL q c (δt R dl q c) j)

/-- The generated table is a correct automaton for `P`: state `0` = no row yet, `R` = dead. -/
def TableOK : Prop :=
  dl.length = R ∧ (∀ c, c < b ^ k → StartOK k b R dl rowL fcL fdL faL c) ∧
    (∀ q, q < R → 1 ≤ q → ∀ c, c < b ^ k → StepOK cu dg an k b R dl rowL fcL fdL faL q c)

instance (c : ℕ) : Decidable (StartOK k b R dl rowL fcL fdL faL c) := by
  unfold StartOK; infer_instance
instance (q c q' j : ℕ) : Decidable (FlagOK cu dg an k b rowL fcL fdL faL q c q' j) := by
  unfold FlagOK; infer_instance
instance (q c : ℕ) : Decidable (StepOK cu dg an k b R dl rowL fcL fdL faL q c) := by
  unfold StepOK; infer_instance
instance : Decidable (TableOK cu dg an k b R dl rowL fcL fdL faL) := by unfold TableOK; infer_instance

/-- The array of a word of row codes. -/
def Xw {n : ℕ} (w : Fin n → Fin (b ^ k)) (i j : ℕ) : ℕ := if h : i < n then rc b (w ⟨i, h⟩) j else 0

def δA (q : ℕ) (a : Fin (b ^ k)) : ℕ := δt R dl q a.val

def Matches (q m : ℕ) (X : ℕ → ℕ → ℕ) : Prop :=
  ∀ j < k, X (m - 1) j = Lq rowL q j ∧ (cu = true → (Fq fcL q j ↔ Fl 0 m k X j)) ∧
    (dg = true → (Fq fdL q j ↔ Fl (-1) m k X j)) ∧ (an = true → (Fq faL q j ↔ Fl 1 m k X j))

theorem run_append {A : Type} (δ : ℕ → A → ℕ) (q : ℕ) (l1 l2 : List A) :
    TMLib.run δ q (l1 ++ l2) = TMLib.run δ (TMLib.run δ q l1) l2 := by
  induction l1 generalizing q with
  | nil => rfl
  | cons a l ih => exact ih (δ q a)

theorem bridge (hT : TableOK cu dg an k b R dl rowL fcL fdL faL) (n : ℕ) (w : Fin n → Fin (b ^ k)) :
    (n = 0 → TMLib.run (δA k b R dl) 0 (List.ofFn w) = 0) ∧
    (1 ≤ n → (TMLib.run (δA k b R dl) 0 (List.ofFn w) ≠ R ↔ P cu dg an n k (Xw k b w)) ∧
      (TMLib.run (δA k b R dl) 0 (List.ofFn w) ≠ R →
        1 ≤ TMLib.run (δA k b R dl) 0 (List.ofFn w) ∧ TMLib.run (δA k b R dl) 0 (List.ofFn w) < R ∧
        Matches cu dg an k rowL fcL fdL faL (TMLib.run (δA k b R dl) 0 (List.ofFn w)) n (Xw k b w))) := by
  obtain ⟨hlen, h0, hq⟩ := hT
  have dead : ∀ c, δt R dl R c = R := by
    intro c; unfold δt; rw [List.getD_eq_default dl [] (by omega)]; simp
  induction n with
  | zero => exact ⟨fun _ => rfl, fun h => by omega⟩
  | succ n ih =>
    refine ⟨fun h => by omega, fun _ => ?_⟩
    set w0 : Fin n → Fin (b ^ k) := fun i => w i.castSucc with hw0
    set c := w (Fin.last n) with hc
    have hlist : List.ofFn w = List.ofFn w0 ++ [c] := by
      rw [List.ofFn_succ', List.concat_eq_append]
    have hrun : TMLib.run (δA k b R dl) 0 (List.ofFn w) =
        δt R dl (TMLib.run (δA k b R dl) 0 (List.ofFn w0)) c.val := by
      rw [hlist, run_append]; rfl
    have hY1 : ∀ i < n, ∀ j < k, Xw k b w i j = Xw k b w0 i j := by
      intro i hi j _
      unfold Xw; rw [dif_pos (by omega), dif_pos hi]; try rfl
    have hY2 : ∀ j < k, Xw k b w n j = rc b c.val j := by
      intro j _; unfold Xw; rw [dif_pos (by omega)]; try rfl
    rw [hrun]
    obtain ⟨ih0, ih1⟩ := ih w0
    rcases Nat.eq_zero_or_pos n with hn | hn
    · -- first row
      subst hn
      rw [ih0 rfl]
      obtain ⟨hc1, hc2⟩ : StartOK k b R dl rowL fcL fdL faL c.val := h0 c.val c.isLt
      have hP : P cu dg an (0 + 1) k (Xw k b w) ↔ RowOK k (rc b c.val) := P_one hY2
      refine ⟨by rw [hP, ne_eq, hc1, not_not], fun hne => ?_⟩
      obtain ⟨a1, a2, a3⟩ := hc2 hne
      refine ⟨a1, a2, fun j hj => ?_⟩
      obtain ⟨e1, e2, e3, e4⟩ := a3 j hj
      refine ⟨by rw [e1]; exact hY2 j hj, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩ <;>
        exact iff_of_false (by assumption) (Fl_one j)
    · obtain ⟨ihP, ihM⟩ := ih1 hn
      have hstep := P_step (cu := cu) (dg := dg) (an := an) hn hY1 hY2
      by_cases hq0 : TMLib.run (δA k b R dl) 0 (List.ofFn w0) = R
      · rw [hq0, dead]
        refine ⟨?_, fun h => absurd rfl h⟩
        rw [hstep]
        simp only [ne_eq, not_true_eq_false, false_iff, not_and]
        intro hp; exact absurd hp (by rw [← ihP]; exact not_not.2 hq0)
      · set q := TMLib.run (δA k b R dl) 0 (List.ofFn w0) with hqdef
        obtain ⟨q1, q2, hM⟩ := ihM hq0
        have hPX : P cu dg an n k (Xw k b w0) := ihP.1 hq0
        obtain ⟨t1, t2⟩ : StepOK cu dg an k b R dl rowL fcL fdL faL q c.val := hq q q2 q1 c.val c.isLt
        have hloc : LocOK cu dg an k (Xw k b w0 (n - 1)) (Fl 0 n k (Xw k b w0)) (Fl (-1) n k (Xw k b w0))
            (Fl 1 n k (Xw k b w0)) (rc b c.val) ↔
            LocOK cu dg an k (Lq rowL q) (Fq fcL q) (Fq fdL q) (Fq faL q) (rc b c.val) :=
          LocOK_congr (fun j hj => (hM j hj).1) (fun h j hj => ((hM j hj).2.1 h).symm)
            (fun h j hj => ((hM j hj).2.2.1 h).symm) (fun h j hj => ((hM j hj).2.2.2 h).symm)
        refine ⟨?_, fun hne => ?_⟩
        · rw [hstep, hloc, ne_eq, t1, not_not]
          exact ⟨fun h => ⟨hPX, h⟩, fun h => h.2⟩
        · obtain ⟨u1, u2, u3⟩ := t2 hne
          refine ⟨u1, u2, fun j hj => ?_⟩
          obtain ⟨v1, v2, v3, v4⟩ := u3 j hj
          have hm' : n + 1 - 1 = n := by omega
          refine ⟨by rw [hm', v1]; exact hY2 j hj, fun h => ?_, fun h => ?_, fun h => ?_⟩
          · rw [v2 h, fl_step (by norm_num) hn hY1 hY2 j hj]
            exact NF_congr j (fun j hj => ((hM j hj).1).symm) (fun j hj => (hM j hj).2.1 h)
          · rw [v3 h, fl_step (by norm_num) hn hY1 hY2 j hj]
            exact NF_congr j (fun j hj => ((hM j hj).1).symm) (fun j hj => (hM j hj).2.2.1 h)
          · rw [v4 h, fl_step (by norm_num) hn hY1 hY2 j hj]
            exact NF_congr j (fun j hj => ((hM j hj).1).symm) (fun j hj => (hM j hj).2.2.2 h)

end table

end UniLib

/-! ## From the statement's `Fin` arrays to the library, and polynomial closed forms -/

namespace UniLib

section finlemmas

variable {n k b : ℕ} (x : Fin n → Fin k → Fin b) (X : ℕ → ℕ → ℕ)
  (hX : ∀ (i : Fin n) (j : Fin k), ((x i j : Fin b) : ℕ) = X i j)
include hX

theorem rows_fin :
    (∀ i : Fin n, ∀ j1 j2 j3 : Fin k, j1 < j2 → j2 < j3 → ¬ (x i j2 < x i j1 ∧ x i j2 < x i j3)) ↔
      RowsOK n k X := by
  constructor
  · intro h i hi j3 hj3 j2 hj2 j1 hj1
    have := h ⟨i, hi⟩ ⟨j1, by omega⟩ ⟨j2, by omega⟩ ⟨j3, hj3⟩ (Fin.mk_lt_mk.2 hj1) (Fin.mk_lt_mk.2 hj2)
    simp only [Fin.lt_iff_val_lt_val, hX] at this
    exact this
  · intro h i j1 j2 j3 h12 h23
    have := h i.val i.isLt j3.val j3.isLt j2.val h23 j1.val h12
    simp only [Fin.lt_iff_val_lt_val, hX]
    exact this

theorem colnd_fin :
    (∀ i1 i2 : Fin n, ∀ j : Fin k, i1 ≤ i2 → x i1 j ≤ x i2 j) ↔ ColND n k X := by
  constructor
  · intro h i1 i2 j h12 h2 hj
    have := h ⟨i1, by omega⟩ ⟨i2, h2⟩ ⟨j, hj⟩ (Fin.mk_le_mk.2 (le_of_lt h12))
    simp only [Fin.le_iff_val_le_val, hX] at this
    exact this
  · intro h i1 i2 j h12
    simp only [Fin.le_iff_val_le_val, hX]
    rcases lt_or_eq_of_le h12 with h' | h'
    · exact h i1 i2 j h' i2.isLt j.isLt
    · rw [h']

theorem colu_fin :
    (∀ i1 i2 i3 : Fin n, ∀ j : Fin k, i1 < i2 → i2 < i3 → ¬ (x i2 j < x i1 j ∧ x i2 j < x i3 j)) ↔
      Uni 0 n k X := by
  constructor
  · intro h i1 i2 i3 j1 j2 j3 h12 h23 h3 hj1 hj2 hj3 e1 e2
    have e1' : j1 = j2 := by simp only [zero_mul] at e1; omega
    have e2' : j2 = j3 := by simp only [zero_mul] at e2; omega
    subst e1' e2'
    have := h ⟨i1, by omega⟩ ⟨i2, by omega⟩ ⟨i3, h3⟩ ⟨j1, hj1⟩ (Fin.mk_lt_mk.2 h12) (Fin.mk_lt_mk.2 h23)
    simp only [Fin.lt_iff_val_lt_val, hX] at this
    exact this
  · intro h i1 i2 i3 j h12 h23
    simp only [Fin.lt_iff_val_lt_val, hX]
    exact h i1 i2 i3 j j j h12 h23 i3.isLt j.isLt j.isLt j.isLt (by simp) (by simp)

theorem anti_fin :
    (∀ i1 i2 i3 : Fin n, ∀ j1 j2 j3 : Fin k, i1 < i2 → i2 < i3 → (i1 : ℕ) + j1 = i2 + j2 →
      (i2 : ℕ) + j2 = i3 + j3 → ¬ (x i2 j2 < x i1 j1 ∧ x i2 j2 < x i3 j3)) ↔ Uni 1 n k X := by
  constructor
  · intro h i1 i2 i3 j1 j2 j3 h12 h23 h3 hj1 hj2 hj3 e1 e2
    have := h ⟨i1, by omega⟩ ⟨i2, by omega⟩ ⟨i3, h3⟩ ⟨j1, hj1⟩ ⟨j2, hj2⟩ ⟨j3, hj3⟩
      (Fin.mk_lt_mk.2 h12) (Fin.mk_lt_mk.2 h23) (by show i1 + j1 = i2 + j2; omega)
      (by show i2 + j2 = i3 + j3; omega)
    simp only [Fin.lt_iff_val_lt_val, hX] at this
    exact this
  · intro h i1 i2 i3 j1 j2 j3 h12 h23 e1 e2
    simp only [Fin.lt_iff_val_lt_val, hX]
    exact h i1 i2 i3 j1 j2 j3 h12 h23 i3.isLt j1.isLt j2.isLt j3.isLt (by omega) (by omega)

theorem diag_fin :
    (∀ i1 i2 i3 : Fin n, ∀ j1 j2 j3 : Fin k, i1 < i2 → i2 < i3 → (j1 : ℕ) + i2 = j2 + i1 →
      (j2 : ℕ) + i3 = j3 + i2 → ¬ (x i2 j2 < x i1 j1 ∧ x i2 j2 < x i3 j3)) ↔ Uni (-1) n k X := by
  constructor
  · intro h i1 i2 i3 j1 j2 j3 h12 h23 h3 hj1 hj2 hj3 e1 e2
    have := h ⟨i1, by omega⟩ ⟨i2, by omega⟩ ⟨i3, h3⟩ ⟨j1, hj1⟩ ⟨j2, hj2⟩ ⟨j3, hj3⟩
      (Fin.mk_lt_mk.2 h12) (Fin.mk_lt_mk.2 h23) (by show j1 + i2 = j2 + i1; omega)
      (by show j2 + i3 = j3 + i2; omega)
    simp only [Fin.lt_iff_val_lt_val, hX] at this
    exact this
  · intro h i1 i2 i3 j1 j2 j3 h12 h23 e1 e2
    simp only [Fin.lt_iff_val_lt_val, hX]
    exact h i1 i2 i3 j1 j2 j3 h12 h23 i3.isLt j1.isLt j2.isLt j3.isLt (by omega) (by omega)

end finlemmas

theorem arr_val {n k b : ℕ} (x : Fin n → Fin k → Fin b) (i : Fin n) (j : Fin k) :
    ((x i j : Fin b) : ℕ) = Xw k b (fun i => finFunctionFinEquiv (x i)) i j := by
  unfold Xw rc
  rw [dif_pos i.isLt, ← finFunctionFinEquiv_symm_apply_val]
  simp

open Classical in
theorem count_arrays {cu dg an : Bool} {n k b : ℕ} (pred : (Fin n → Fin k → Fin b) → Prop)
    {inst : DecidablePred pred}
    (h : ∀ x, pred x ↔ P cu dg an n k (Xw k b (fun i => finFunctionFinEquiv (x i)))) :
    (@Finset.filter _ pred inst Finset.univ).card =
      (Finset.univ.filter (fun w : Fin n → Fin (b ^ k) => P cu dg an n k (Xw k b w))).card := by
  apply Finset.card_equiv (Equiv.piCongrRight (fun _ => finFunctionFinEquiv))
  intro x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact h x

open Classical in
theorem count_words (cu dg an : Bool) (k b R : ℕ) (dl rowL : List (List ℕ)) (fcL fdL faL : List (List Bool))
    (hT : TableOK cu dg an k b R dl rowL fcL fdL faL) (n : ℕ) (hn : 1 ≤ n) :
    (Finset.univ.filter (fun w : Fin n → Fin (b ^ k) => P cu dg an n k (Xw k b w))).card =
      TMLib.cnt (δA k b R dl) (fun q => decide (q ≠ R)) n 0 := by
  rw [← TMLib.card_run]
  exact congrArg Finset.card (Finset.filter_congr (fun w _ => by
    rw [decide_eq_true_iff]
    exact ((bridge cu dg an k b R dl rowL fcL fdL faL hT n w).2 hn).1.symm))

end UniLib

namespace TMLib

open Finset

/-- A sequence satisfying a linear recurrence from shift `J` on agrees with a polynomial `Pz / den`
(which satisfies the same recurrence everywhere) from `n0` on, once they agree on `[n0, n0 + J + D)`. -/
theorem rec_poly (x : ℕ → ℤ) (D J n0 : ℕ) (cc : ℕ → ℤ) (Pz : ℤ → ℤ) (den : ℤ)
    (hx : ∀ n, x (n + J + D) = ∑ i ∈ range D, cc i * x (n + J + i))
    (hP : ∀ t : ℤ, Pz (t + D) = ∑ i ∈ range D, cc i * Pz (t + i))
    (h0 : ∀ m, n0 ≤ m → m < n0 + J + D → den * x m = Pz m) :
    ∀ m, n0 ≤ m → den * x m = Pz m := by
  let z : ℕ → ℤ := fun n => den * x (n + (n0 + J)) - Pz ((n + (n0 + J) : ℕ) : ℤ)
  have hz : ∀ n, z (n + D) = ∑ i ∈ range D, cc i * z (n + i) := by
    intro n
    simp only [z]
    rw [show n + D + (n0 + J) = (n + n0) + J + D by ring, hx (n + n0)]
    rw [show (((n + n0) + J + D : ℕ) : ℤ) = ((n + n0 + J : ℕ) : ℤ) + D by push_cast; ring, hP]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [show n + i + (n0 + J) = n + n0 + J + i by ring]
    push_cast
    ring
  have hz0 := window z D cc hz 0 (fun _ => 0) (fun n hn => by
    simp only [z, add_zero, Finset.range_zero, Finset.sum_empty]
    rw [h0 (n + (n0 + J)) (by omega) (by omega), sub_self])
  intro m hm
  by_cases hmJ : m < n0 + J + D
  · exact h0 m hm hmJ
  · have := hz0 (m - (n0 + J))
    simp only [z, add_zero, Finset.range_zero, Finset.sum_empty] at this
    rw [show m - (n0 + J) + (n0 + J) = m by omega] at this
    linarith

end TMLib

/-! ## Bridge for statements that give arrays as lists of rows (unimodal via take/drop) -/

namespace PB

open UniLib

/-- Unimodal list: weakly increasing up to some position `m`, weakly decreasing from `m` on. -/
def UniL (s : List ℕ) : Prop := ∃ m, (s.take m).Pairwise (· ≤ ·) ∧ (s.drop m).Pairwise (· ≥ ·)

/-- No valley, by positions. -/
def NVL (s : List ℕ) : Prop :=
  ∀ i j l, i < j → j < l → l < s.length → ¬ (s.getD j 0 < s.getD i 0 ∧ s.getD j 0 < s.getD l 0)

theorem gd {s : List ℕ} {i : ℕ} (h : i < s.length) : s.getD i 0 = s[i] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem uniL_iff (s : List ℕ) : UniL s ↔ NVL s := by
  constructor
  · rintro ⟨m, h1, h2⟩ i j l hij hjl hl ⟨a1, a2⟩
    rw [List.pairwise_iff_getElem] at h1 h2
    rw [gd (s := s) (i := j) (by omega), gd (s := s) (i := i) (by omega)] at a1
    rw [gd (s := s) (i := j) (by omega), gd (s := s) (i := l) (by omega)] at a2
    by_cases hjm : j < m
    · have := h1 i j (by rw [List.length_take]; omega) (by rw [List.length_take]; omega) hij
      rw [List.getElem_take, List.getElem_take] at this
      omega
    · have := h2 (j - m) (l - m) (by rw [List.length_drop]; omega) (by rw [List.length_drop]; omega)
        (by omega)
      rw [List.getElem_drop, List.getElem_drop] at this
      have e1 : m + (j - m) = j := by omega
      have e2 : m + (l - m) = l := by omega
      simp only [e1, e2] at this
      omega
  · intro h
    by_cases h0 : s.length = 0
    · have hs : s = [] := List.eq_nil_of_length_eq_zero h0
      subst hs
      exact ⟨0, by simp, by simp⟩
    · obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image (Finset.range s.length) (fun t => s.getD t 0)
        ⟨0, by simp; omega⟩
      simp only [Finset.mem_range] at hM hmax
      refine ⟨M, ?_, ?_⟩
      · rw [List.pairwise_iff_getElem]
        intro a c ha hc hac
        rw [List.length_take] at ha hc
        rw [List.getElem_take, List.getElem_take]
        have hv := h a c M hac (by omega) hM
        have hm := hmax a (by omega)
        rw [gd (s := s) (i := a) (by omega), gd (s := s) (i := c) (by omega),
          gd (s := s) (i := M) hM] at hv
        rw [gd (s := s) (i := a) (by omega), gd (s := s) (i := M) hM] at hm
        omega
      · rw [List.pairwise_iff_getElem]
        intro a c ha hc hac
        rw [List.length_drop] at ha hc
        rw [List.getElem_drop, List.getElem_drop]
        have hm := hmax (M + c) (by omega)
        rw [gd (s := s) (i := M + c) (by omega), gd (s := s) (i := M) hM] at hm
        by_cases ha0 : a = 0
        · subst ha0
          simpa using hm
        · have hv := h M (M + a) (M + c) (by omega) (by omega) (by omega)
          rw [gd (s := s) (i := M) hM, gd (s := s) (i := M + a) (by omega),
            gd (s := s) (i := M + c) (by omega)] at hv
          omega

/-- No valley for a list given by a function. -/
theorem nvl_ofFn {L : ℕ} (g : Fin L → ℕ) :
    NVL (List.ofFn g) ↔ ∀ a c d : Fin L, a < c → c < d → ¬ (g c < g a ∧ g c < g d) := by
  unfold NVL
  simp only [List.length_ofFn]
  have hg : ∀ t (h : t < L), (List.ofFn g).getD t 0 = g ⟨t, h⟩ := by
    intro t h; simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h]
  constructor
  · intro H a c d hac hcd
    have := H a c d hac hcd d.isLt
    rwa [hg a a.isLt, hg c c.isLt, hg d d.isLt] at this
  · intro H a c d hac hcd hd
    rw [hg a (by omega), hg c (by omega), hg d hd]
    exact H ⟨a, by omega⟩ ⟨c, by omega⟩ ⟨d, hd⟩ hac hcd

section rows

variable {n k b : ℕ}

theorem rows_pb (x : Fin n → Fin k → Fin b) (X : ℕ → ℕ → ℕ)
    (hX : ∀ (i : Fin n) (j : Fin k), ((x i j : Fin b) : ℕ) = X i j) :
    (∀ r ∈ List.ofFn x, UniL (List.ofFn fun j => (r j : ℕ))) ↔ RowsOK n k X := by
  rw [List.forall_mem_ofFn_iff, ← rows_fin x X hX]
  apply forall_congr'
  intro i
  rw [uniL_iff, nvl_ofFn]
  simp only [Fin.lt_iff_val_lt_val]

theorem colsU_pb (x : Fin n → Fin k → Fin b) (X : ℕ → ℕ → ℕ)
    (hX : ∀ (i : Fin n) (j : Fin k), ((x i j : Fin b) : ℕ) = X i j) :
    (∀ j : Fin k, UniL ((List.ofFn x).map fun r => (r j : ℕ))) ↔ Uni 0 n k X := by
  rw [← colu_fin x X hX]
  simp only [List.map_ofFn, uniL_iff, nvl_ofFn, Function.comp_apply, Fin.lt_iff_val_lt_val]
  constructor
  · intro h i1 i2 i3 j h12 h23; exact h j i1 i2 i3 h12 h23
  · intro h j i1 i2 i3 h12 h23; exact h i1 i2 i3 j h12 h23

theorem chain_pb (x : Fin n → Fin k → Fin b) :
    (List.ofFn x).IsChain (fun r s => ∀ j : Fin k, r j ≤ s j) ↔
      ∀ i1 i2 : Fin n, ∀ j : Fin k, i1 ≤ i2 → x i1 j ≤ x i2 j := by
  rw [List.isChain_iff_getElem]
  simp only [List.length_ofFn, List.getElem_ofFn]
  constructor
  · intro h i1 i2 j h12
    obtain ⟨d, hd⟩ : ∃ d, i2.val = i1.val + d := ⟨i2.val - i1.val, by rw [Fin.le_def] at h12; omega⟩
    induction d generalizing i2 with
    | zero =>
      have : i2 = i1 := Fin.ext (by omega)
      rw [this]
    | succ d ih =>
      have hlt : i1.val + d < n := by omega
      have h1 := ih ⟨i1.val + d, hlt⟩ (by rw [Fin.le_def]; simp) rfl
      have h2 := h (i1.val + d) (by omega) j
      have e : (⟨i1.val + d + 1, by omega⟩ : Fin n) = i2 := Fin.ext (by simp; omega)
      rw [e] at h2
      exact le_trans h1 h2
  · intro h i hi j
    exact h ⟨i, by omega⟩ ⟨i + 1, hi⟩ j (by rw [Fin.le_def]; simp)

end rows

section lines

variable {k b : ℕ}

/-- Entry `(i, j)` of a list of rows, `0` outside. -/
def XL (l : List (Fin k → Fin b)) (i j : ℕ) : ℕ :=
  match l[i]? with
  | some r => if h : j < k then (r ⟨j, h⟩ : ℕ) else 0
  | none => 0

def adiagG (k b : ℕ) : List (Fin k → Fin b) → ℕ → List ℕ
  | [], _ => []
  | r :: l, j => if h : j < k then (r ⟨j, h⟩ : ℕ) :: (if j = 0 then [] else adiagG k b l (j - 1)) else []

def diagG (k b : ℕ) : List (Fin k → Fin b) → ℕ → List ℕ
  | [], _ => []
  | r :: l, j => if h : j < k then (r ⟨j, h⟩ : ℕ) :: diagG k b l (j + 1) else []

theorem XL_cons_zero (r : Fin k → Fin b) (l : List (Fin k → Fin b)) (j : ℕ) (h : j < k) :
    XL (r :: l) 0 j = (r ⟨j, h⟩ : ℕ) := by
  simp [XL, h]

theorem XL_cons_succ (r : Fin k → Fin b) (l : List (Fin k → Fin b)) (t j : ℕ) :
    XL (r :: l) (t + 1) j = XL l t j := by
  simp [XL]

theorem XL_drop (l : List (Fin k → Fin b)) (i t j : ℕ) : XL (l.drop i) t j = XL l (i + t) j := by
  simp [XL, List.getElem?_drop]

theorem XL_ofFn {n : ℕ} (x : Fin n → Fin k → Fin b) (i j : ℕ) (hi : i < n) (hj : j < k) :
    XL (List.ofFn x) i j = (x ⟨i, hi⟩ ⟨j, hj⟩ : ℕ) := by
  simp [XL, List.getElem?_ofFn, hi, hj]

theorem adiag_len (l : List (Fin k → Fin b)) :
    ∀ j, (adiagG k b l j).length = if j < k then min (j + 1) l.length else 0 := by
  induction l with
  | nil => intro j; simp [adiagG]
  | cons r l ih =>
    intro j
    by_cases hj : j < k
    · by_cases j0 : j = 0
      · subst j0; simp [adiagG, hj]
      · simp only [adiagG, dif_pos hj, if_neg j0, List.length_cons, ih (j - 1),
          if_pos (show j - 1 < k by omega), if_pos hj]
        omega
    · simp [adiagG, hj]

theorem adiag_get (l : List (Fin k → Fin b)) :
    ∀ j t, t < (adiagG k b l j).length → (adiagG k b l j).getD t 0 = XL l t (j - t) := by
  induction l with
  | nil => intro j t h; simp [adiagG] at h
  | cons r l ih =>
    intro j t h
    by_cases hj : j < k
    · rcases t with _ | t
      · simp [adiagG, hj, XL_cons_zero r l j hj]
      · by_cases j0 : j = 0
        · subst j0; simp [adiagG, hj] at h
        · simp only [adiagG, dif_pos hj, if_neg j0, List.length_cons] at h ⊢
          rw [List.getD_cons_succ, ih (j - 1) t (by omega), XL_cons_succ]
          congr 1
          omega
    · simp [adiagG, hj] at h

theorem diag_len (l : List (Fin k → Fin b)) :
    ∀ j, (diagG k b l j).length = if j < k then min (k - j) l.length else 0 := by
  induction l with
  | nil => intro j; simp [diagG]
  | cons r l ih =>
    intro j
    by_cases hj : j < k
    · simp only [diagG, dif_pos hj, List.length_cons, ih (j + 1), if_pos hj]
      by_cases hj1 : j + 1 < k
      · rw [if_pos hj1]; omega
      · rw [if_neg hj1]; omega
    · simp [diagG, hj]

theorem diag_get (l : List (Fin k → Fin b)) :
    ∀ j t, t < (diagG k b l j).length → (diagG k b l j).getD t 0 = XL l t (j + t) := by
  induction l with
  | nil => intro j t h; simp [diagG] at h
  | cons r l ih =>
    intro j t h
    by_cases hj : j < k
    · rcases t with _ | t
      · simp [diagG, hj, XL_cons_zero r l j hj]
      · simp only [diagG, dif_pos hj, List.length_cons] at h ⊢
        rw [List.getD_cons_succ, ih (j + 1) t (by omega), XL_cons_succ]
        congr 1
        omega
    · simp [diagG, hj] at h

variable (l : List (Fin k → Fin b)) (X : ℕ → ℕ → ℕ)
  (hX : ∀ i < l.length, ∀ j < k, XL l i j = X i j)
include hX

theorem anti_pb (e : ℕ) (he : e + 1 = k) :
    ((∀ j < k, UniL (adiagG k b l j)) ∧ (∀ i, UniL (adiagG k b (l.drop i) e))) ↔
      Uni 1 l.length k X := by
  simp only [uniL_iff]
  constructor
  · rintro ⟨hA, hB⟩ i1 i2 i3 j1 j2 j3 h12 h23 h3 hj1 hj2 hj3 e1 e2
    have c1 : i1 + j1 = i2 + j2 := by omega
    have c2 : i2 + j2 = i3 + j3 := by omega
    by_cases hc : i1 + j1 < k
    · have hlen := adiag_len l (i1 + j1)
      rw [if_pos hc] at hlen
      have := hA (i1 + j1) hc i1 i2 i3 h12 h23 (by rw [hlen]; omega)
      rw [adiag_get l _ i1 (by rw [hlen]; omega), adiag_get l _ i2 (by rw [hlen]; omega),
        adiag_get l _ i3 (by rw [hlen]; omega)] at this
      rw [show i1 + j1 - i1 = j1 by omega, show i1 + j1 - i2 = j2 by omega,
        show i1 + j1 - i3 = j3 by omega, hX i1 (by omega) j1 hj1, hX i2 (by omega) j2 hj2,
        hX i3 h3 j3 hj3] at this
      exact this
    · set i := i1 + j1 - e with hi
      have hlen := adiag_len (l.drop i) e
      rw [if_pos (by omega), List.length_drop] at hlen
      have := hB i (i1 - i) (i2 - i) (i3 - i) (by omega) (by omega) (by rw [hlen]; omega)
      rw [adiag_get _ _ (i1 - i) (by rw [hlen]; omega), adiag_get _ _ (i2 - i) (by rw [hlen]; omega),
        adiag_get _ _ (i3 - i) (by rw [hlen]; omega), XL_drop, XL_drop, XL_drop] at this
      rw [show i + (i1 - i) = i1 by omega, show i + (i2 - i) = i2 by omega,
        show i + (i3 - i) = i3 by omega, show e - (i1 - i) = j1 by omega,
        show e - (i2 - i) = j2 by omega, show e - (i3 - i) = j3 by omega,
        hX i1 (by omega) j1 hj1, hX i2 (by omega) j2 hj2, hX i3 h3 j3 hj3] at this
      exact this
  · intro hU
    refine ⟨fun j hj t1 t2 t3 h12 h23 h3 => ?_, fun i t1 t2 t3 h12 h23 h3 => ?_⟩
    · have hlen := adiag_len l j
      rw [if_pos hj] at hlen
      rw [hlen] at h3
      rw [adiag_get l j t1 (by rw [hlen]; omega), adiag_get l j t2 (by rw [hlen]; omega),
        adiag_get l j t3 (by rw [hlen]; omega), hX t1 (by omega) (j - t1) (by omega),
        hX t2 (by omega) (j - t2) (by omega), hX t3 (by omega) (j - t3) (by omega)]
      exact hU t1 t2 t3 (j - t1) (j - t2) (j - t3) h12 h23 (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)
    · have hlen := adiag_len (l.drop i) e
      rw [if_pos (by omega), List.length_drop] at hlen
      rw [hlen] at h3
      rw [adiag_get _ e t1 (by rw [hlen]; omega), adiag_get _ e t2 (by rw [hlen]; omega),
        adiag_get _ e t3 (by rw [hlen]; omega), XL_drop, XL_drop, XL_drop,
        hX (i + t1) (by omega) (e - t1) (by omega), hX (i + t2) (by omega) (e - t2) (by omega),
        hX (i + t3) (by omega) (e - t3) (by omega)]
      exact hU (i + t1) (i + t2) (i + t3) (e - t1) (e - t2) (e - t3) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)

theorem diag_pb (hk : 0 < k) :
    ((∀ j < k, UniL (diagG k b l j)) ∧ (∀ i, UniL (diagG k b (l.drop i) 0))) ↔
      Uni (-1) l.length k X := by
  simp only [uniL_iff]
  constructor
  · rintro ⟨hA, hB⟩ i1 i2 i3 j1 j2 j3 h12 h23 h3 hj1 hj2 hj3 e1 e2
    have c1 : j1 + i2 = j2 + i1 := by omega
    have c2 : j2 + i3 = j3 + i2 := by omega
    by_cases hc : i1 ≤ j1
    · set j := j1 - i1 with hjdef
      have hjk : j < k := by omega
      have hlen := diag_len l j
      rw [if_pos hjk] at hlen
      have := hA j hjk i1 i2 i3 h12 h23 (by rw [hlen]; omega)
      rw [diag_get l j i1 (by rw [hlen]; omega), diag_get l j i2 (by rw [hlen]; omega),
        diag_get l j i3 (by rw [hlen]; omega)] at this
      rw [show j + i1 = j1 by omega, show j + i2 = j2 by omega, show j + i3 = j3 by omega,
        hX i1 (by omega) j1 hj1, hX i2 (by omega) j2 hj2, hX i3 h3 j3 hj3] at this
      exact this
    · set i := i1 - j1 with hidef
      have hlen := diag_len (l.drop i) 0
      rw [if_pos (by omega), List.length_drop] at hlen
      have := hB i j1 j2 j3 (by omega) (by omega) (by rw [hlen]; omega)
      rw [diag_get _ 0 j1 (by rw [hlen]; omega), diag_get _ 0 j2 (by rw [hlen]; omega),
        diag_get _ 0 j3 (by rw [hlen]; omega), XL_drop, XL_drop, XL_drop] at this
      rw [show i + j1 = i1 by omega, show i + j2 = i2 by omega, show i + j3 = i3 by omega,
        show 0 + j1 = j1 by omega, show 0 + j2 = j2 by omega, show 0 + j3 = j3 by omega,
        hX i1 (by omega) j1 hj1, hX i2 (by omega) j2 hj2, hX i3 h3 j3 hj3] at this
      exact this
  · intro hU
    refine ⟨fun j hj t1 t2 t3 h12 h23 h3 => ?_, fun i t1 t2 t3 h12 h23 h3 => ?_⟩
    · have hlen := diag_len l j
      rw [if_pos hj] at hlen
      rw [hlen] at h3
      rw [diag_get l j t1 (by rw [hlen]; omega), diag_get l j t2 (by rw [hlen]; omega),
        diag_get l j t3 (by rw [hlen]; omega), hX t1 (by omega) (j + t1) (by omega),
        hX t2 (by omega) (j + t2) (by omega), hX t3 (by omega) (j + t3) (by omega)]
      exact hU t1 t2 t3 (j + t1) (j + t2) (j + t3) h12 h23 (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)
    · have hlen := diag_len (l.drop i) 0
      rw [if_pos hk, List.length_drop] at hlen
      rw [hlen] at h3
      rw [diag_get _ 0 t1 (by rw [hlen]; omega), diag_get _ 0 t2 (by rw [hlen]; omega),
        diag_get _ 0 t3 (by rw [hlen]; omega), XL_drop, XL_drop, XL_drop,
        hX (i + t1) (by omega) (0 + t1) (by omega), hX (i + t2) (by omega) (0 + t2) (by omega),
        hX (i + t3) (by omega) (0 + t3) (by omega)]
      exact hU (i + t1) (i + t2) (i + t3) (0 + t1) (0 + t2) (0 + t3) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

end lines

theorem natcard_lists {R : Type} [Fintype R] (n : ℕ) (Q : List R → Prop) [DecidablePred Q] :
    Nat.card {l : List R // l.length = n ∧ Q l} =
      (Finset.univ.filter (fun x : Fin n → R => Q (List.ofFn x))).card := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (fun x => ⟨List.ofFn x.1, List.length_ofFn, x.2⟩) ⟨?_, ?_⟩
  · intro x y h
    exact Subtype.ext (List.ofFn_injective (congrArg Subtype.val h))
  · rintro ⟨l, hl, hq⟩
    subst hl
    refine ⟨⟨fun i => l[i.val], by rw [List.ofFn_getElem]; exact hq⟩, ?_⟩
    apply Subtype.ext
    simp only [List.ofFn_getElem]

end PB

namespace OMA.S_oeis_a223834

open UniLib Finset PowerSeries

def dl : List (List ℕ) := [[1, 2, 3, 4, 5, 31, 6, 7, 8, 31, 31, 31, 9, 31, 10, 11], [1, 2, 3, 4, 5, 31, 6, 7, 8, 31, 31, 31, 9, 31, 10, 11], [31, 12, 31, 4, 31, 31, 31, 7, 31, 31, 31, 31, 31, 31, 31, 11], [31, 31, 13, 14, 31, 31, 15, 7, 31, 31, 31, 31, 31, 31, 16, 11], [31, 31, 31, 14, 31, 31, 31, 7, 31, 31, 31, 31, 31, 31, 31, 11], [31, 31, 31, 31, 17, 31, 18, 19, 31, 31, 31, 31, 20, 31, 10, 11], [31, 31, 31, 31, 31, 31, 21, 19, 31, 31, 31, 31, 31, 31, 16, 11], [31, 31, 31, 31, 31, 31, 31, 19, 31, 31, 31, 31, 31, 31, 31, 11], [31, 31, 31, 31, 31, 31, 31, 31, 22, 31, 31, 31, 9, 31, 10, 11], [31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 20, 31, 10, 11], [31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 16, 11], [31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 11], [31, 23, 31, 14, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31], [31, 31, 24, 25, 31, 31, 21, 19, 31, 31, 31, 31, 31, 31, 31, 31], [31, 31, 31, 25, 31, 31, 31, 19, 31, 31, 31, 31, 31, 31, 31, 31], [31, 31, 31, 31, 31, 31, 21, 19, 31, 31, 31, 31, 31, 31, 16, 11], [31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 16, 11], [31, 31, 31, 31, 26, 31, 21, 31, 31, 31, 31, 31, 27, 31, 16, 31], [31, 31, 31, 31, 31, 31, 21, 19, 31, 31, 31, 31, 31, 31, 16, 11], [31, 31, 31, 31, 31, 31, 31, 19, 31, 31, 31, 31, 31, 31, 31, 11], [31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 27, 31, 16, 31], [31, 31, 31, 31, 31, 31, 21, 19, 31, 31, 31, 31, 31, 31, 16, 11], [31, 31, 31, 31, 31, 31, 31, 31, 28, 31, 31, 31, 20, 31, 31, 31], [31, 29, 31, 25, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31], [31, 31, 24, 25, 31, 31, 21, 19, 31, 31, 31, 31, 31, 31, 31, 31], [31, 31, 31, 25, 31, 31, 31, 19, 31, 31, 31, 31, 31, 31, 31, 31], [31, 31, 31, 31, 26, 31, 21, 31, 31, 31, 31, 31, 27, 31, 16, 31], [31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 27, 31, 16, 31], [31, 31, 31, 31, 31, 31, 31, 31, 30, 31, 31, 31, 27, 31, 31, 31], [31, 29, 31, 25, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31], [31, 31, 31, 31, 31, 31, 31, 31, 30, 31, 31, 31, 27, 31, 31, 31]]
def rowL : List (List ℕ) := [[], [0, 0, 0, 0], [1, 0, 0, 0], [0, 1, 0, 0], [1, 1, 0, 0], [0, 0, 1, 0], [0, 1, 1, 0], [1, 1, 1, 0], [0, 0, 0, 1], [0, 0, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1], [1, 0, 0, 0], [0, 1, 0, 0], [1, 1, 0, 0], [0, 1, 1, 0], [0, 1, 1, 1], [0, 0, 1, 0], [0, 1, 1, 0], [1, 1, 1, 0], [0, 0, 1, 1], [0, 1, 1, 0], [0, 0, 0, 1], [1, 0, 0, 0], [0, 1, 0, 0], [1, 1, 0, 0], [0, 0, 1, 0], [0, 0, 1, 1], [0, 0, 0, 1], [1, 0, 0, 0], [0, 0, 0, 1]]
def fcL : List (List Bool) := [[], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false]]
def fdL : List (List Bool) := [[], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, true, false, false], [false, false, true, false], [false, false, true, false], [false, false, false, false], [false, false, false, false], [false, false, false, true], [false, false, false, true], [false, false, false, true], [false, false, false, false], [false, false, false, true], [false, false, false, false], [false, true, true, false], [false, false, true, true], [false, false, true, true], [false, false, false, true], [false, false, false, false], [false, false, false, false], [false, true, true, true], [false, false, false, false]]
def faL : List (List Bool) := [[], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [true, false, false, false], [false, false, false, false], [true, false, false, false], [true, false, false, false], [false, true, false, false], [false, false, false, false], [false, false, false, false], [false, true, false, false], [true, false, false, false], [false, false, true, false], [false, false, false, false], [true, false, false, false], [false, false, false, false], [true, true, false, false], [true, true, false, false], [false, true, true, false], [false, false, false, false], [true, true, true, false]]

set_option maxRecDepth 400000 in
theorem table_ok : TableOK false true true 4 2 31 dl rowL fcL fdL faL := by decide +kernel

theorem uni_eq (s : List ℕ) : Unimodal s ↔ PB.UniL s := Iff.rfl

theorem adiag_eq (l : List (Fin 4 → Fin 2)) : ∀ j, adiagFrom l j = PB.adiagG 4 2 l j := by
  induction l with
  | nil => intro j; simp [adiagFrom, PB.adiagG]
  | cons r l ih => intro j; simp only [adiagFrom, PB.adiagG, ih]

theorem diag_eq (l : List (Fin 4 → Fin 2)) : ∀ j, diagFrom l j = PB.diagG 4 2 l j := by
  induction l with
  | nil => intro j; simp [diagFrom, PB.diagG]
  | cons r l ih => intro j; simp only [diagFrom, PB.diagG, ih]

theorem pred_iff (n : ℕ) (x : Fin n → Fin 4 → Fin 2) :
    IsSolution (List.ofFn x) ↔ P false true true n 4 (Xw 4 2 (fun i => finFunctionFinEquiv (x i))) := by
  have hX := arr_val x
  have hXL : ∀ i < (List.ofFn x).length, ∀ j < 4,
      PB.XL (List.ofFn x) i j = Xw 4 2 (fun i => finFunctionFinEquiv (x i)) i j := by
    intro i hi j hj
    rw [List.length_ofFn] at hi
    rw [PB.XL_ofFn x i j hi hj]
    exact hX ⟨i, hi⟩ ⟨j, hj⟩
  have hA := PB.anti_pb (List.ofFn x) _ hXL 3 rfl
  rw [List.length_ofFn] at hA
  have hD := PB.diag_pb (List.ofFn x) _ hXL (by norm_num)
  rw [List.length_ofFn] at hD
  unfold IsSolution
  simp only [uni_eq, adiag_eq, diag_eq]
  rw [PB.rows_pb x _ hX]
  rw [PB.chain_pb x, colnd_fin x _ hX]
  unfold P
  rw [if_neg (by decide)]
  exact ⟨fun ⟨h0, h1, h2, h3, h4, h5⟩ => ⟨h0, h1, fun _ => hD.1 ⟨h4, h5⟩, fun _ => hA.1 ⟨h2, h3⟩⟩, fun ⟨h0, h1, hd, ha⟩ => ⟨h0, h1, (hA.2 (ha rfl)).1, (hA.2 (ha rfl)).2, (hD.2 (hd rfl)).1, (hD.2 (hd rfl)).2⟩⟩

open Classical in
theorem a_eq (n : ℕ) (hn : 1 ≤ n) : a n = TMLib.cnt (δA 4 2 31 dl) (fun q => decide (q ≠ 31)) n 0 := by
  unfold a
  rw [PB.natcard_lists n IsSolution, count_arrays (fun x => IsSolution (List.ofFn x)) (pred_iff n),
    count_words false true true 4 2 31 dl rowL fcL fdL faL table_ok n hn]

theorem cl : ∀ q < 32, ∀ a : Fin (2 ^ 4), δA 4 2 31 dl q a < 32 := by
  have h : ∀ q, q < 32 → ∀ c, c < 2 ^ 4 → δt 31 dl q c < 32 := by decide +kernel
  intro q hq a
  exact h q hq a.val a.isLt

def cc (i : ℕ) : ℤ := ([1, -5, 10, -10, 5] : List ℤ).getD i 0

set_option maxRecDepth 400000 in
theorem vrel : ∀ q, q < 32 → ((TMLib.cntV (δA 4 2 31 dl) (fun q => decide (q ≠ 31)) 32 (2 + 5)).getD q 0 : ℤ) =
    ∑ i ∈ range 5, cc i * ((TMLib.cntV (δA 4 2 31 dl) (fun q => decide (q ≠ 31)) 32 (2 + i)).getD q 0 : ℤ) := by
  decide +kernel

theorem xrec (n : ℕ) : (TMLib.cnt (δA 4 2 31 dl) (fun q => decide (q ≠ 31)) (n + 2 + 5) 0 : ℤ) =
    ∑ i ∈ range 5, cc i * (TMLib.cnt (δA 4 2 31 dl) (fun q => decide (q ≠ 31)) (n + 2 + i) 0 : ℤ) := by
  have hS : ∀ q ∈ range 32, ∀ a : Fin (2 ^ 4), δA 4 2 31 dl q a ∈ range 32 :=
    fun q hq a => mem_range.2 (cl q (mem_range.1 hq) a)
  exact TMLib.cnt_rec (δA 4 2 31 dl) (fun q => decide (q ≠ 31)) (range 32) hS 5 cc 2 (fun q hq => by
    have hq' := mem_range.1 hq
    have h := vrel q hq'
    rw [TMLib.cntV_eq (δA 4 2 31 dl) (fun q => decide (q ≠ 31)) 32 cl (2 + 5) q hq'] at h
    rw [h]
    apply sum_congr rfl
    intro i _
    rw [TMLib.cntV_eq (δA 4 2 31 dl) (fun q => decide (q ≠ 31)) 32 cl (2 + i) q hq']) n 0 (mem_range.2 (by norm_num))

def Pz (t : ℤ) : ℤ := 2 * t ^ 4 + 4 * t ^ 3 + 31 * t ^ 2 + 71 * t - 54

theorem hP (t : ℤ) : Pz (t + 5) = ∑ i ∈ range 5, cc i * Pz (t + i) := by
  simp only [Pz, cc, sum_range_succ, sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
  push_cast
  ring

set_option maxRecDepth 400000 in
theorem hv : ∀ m, m < 2 + 2 + 5 → 2 ≤ m →
    6 * ((TMLib.cntV (δA 4 2 31 dl) (fun q => decide (q ≠ 31)) 32 m).getD 0 0 : ℤ) = Pz m := by
  decide +kernel

theorem cast_count (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) = 1/3 * (n : ℚ) ^ 4 + 2/3 * (n : ℚ) ^ 3 + 31/6 * (n : ℚ) ^ 2 + 71/6 * (n : ℚ) - 9 := by
  have h := TMLib.rec_poly (fun m => (TMLib.cnt (δA 4 2 31 dl) (fun q => decide (q ≠ 31)) m 0 : ℤ)) 5 2 2 cc Pz 6
    xrec hP (fun m h1 h2 => by
      have := hv m h2 h1
      rwa [TMLib.cntV_eq (δA 4 2 31 dl) (fun q => decide (q ≠ 31)) 32 cl m 0 (by norm_num)] at this) n hn
  rw [← a_eq n (by omega)] at h
  have h' : ((6 : ℤ) : ℚ) * (a n : ℚ) = ((Pz n : ℤ) : ℚ) := by exact_mod_cast h
  simp only [Pz] at h'
  push_cast at h'
  linarith


theorem recurrence (n : ℕ) (hn : 6 < n) : (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  have key : (a n : ℚ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
    rw [cast_count n (by omega), cast_count (n - 1) (by omega), cast_count (n - 2) (by omega), cast_count (n - 3) (by omega), cast_count (n - 4) (by omega), cast_count (n - 5) (by omega)]
    push_cast [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_sub (show 3 ≤ n by omega), Nat.cast_sub (show 4 ≤ n by omega), Nat.cast_sub (show 5 ≤ n by omega)]
    ring
  exact_mod_cast key

def pQ (t : ℚ) : ℚ := 1/3 * t ^ 4 + 2/3 * t ^ 3 + 31/6 * t ^ 2 + 71/6 * t - 9

theorem fdp (t : ℚ) : pQ (t + 1) - 5 * pQ (t - 1 + 1) + 10 * pQ (t - 2 + 1) - 10 * pQ (t - 3 + 1) + 5 * pQ (t - 4 + 1) - pQ (t - 5 + 1) = 0 := by
  unfold pQ
  ring

theorem v1 : a 1 = 11 := by
  rw [a_eq 1 (by norm_num), ← TMLib.cntV_eq (δA 4 2 31 dl) (fun q => decide (q ≠ 31)) 32 cl 1 0 (by norm_num)]
  decide +kernel
theorem v2 : a 2 = 46 := by
  rw [a_eq 2 (by norm_num), ← TMLib.cntV_eq (δA 4 2 31 dl) (fun q => decide (q ≠ 31)) 32 cl 2 0 (by norm_num)]
  decide +kernel
theorem v3 : a 3 = 118 := by
  rw [a_eq 3 (by norm_num), ← TMLib.cntV_eq (δA 4 2 31 dl) (fun q => decide (q ≠ 31)) 32 cl 3 0 (by norm_num)]
  decide +kernel
theorem v4 : a 4 = 249 := by
  rw [a_eq 4 (by norm_num), ← TMLib.cntV_eq (δA 4 2 31 dl) (fun q => decide (q ≠ 31)) 32 cl 4 0 (by norm_num)]
  decide +kernel
theorem v5 : a 5 = 471 := by
  rw [a_eq 5 (by norm_num), ← TMLib.cntV_eq (δA 4 2 31 dl) (fun q => decide (q ≠ 31)) 32 cl 5 0 (by norm_num)]
  decide +kernel
theorem v6 : a 6 = 824 := by
  rw [a_eq 6 (by norm_num), ← TMLib.cntV_eq (δA 4 2 31 dl) (fun q => decide (q ≠ 31)) 32 cl 6 0 (by norm_num)]
  decide +kernel

theorem gf : PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 5 = 11 - 9 * X - 2 * X ^ 2 + 9 * X ^ 3 + X ^ 4 - 2 * X ^ 5 := by
  set f : ℕ → ℚ := fun n => (a (n + 1) : ℚ) with hf
  have hfd : ∀ m, 2 ≤ m + 1 → f m = pQ ((m : ℚ) + 1) := by
    intro m hm
    rw [hf]
    simp only
    rw [cast_count (m + 1) hm]
    unfold pQ
    push_cast <;> ring
  let A : PowerSeries ℚ := PowerSeries.mk f
  have hleft : A * (1 - X) ^ 5 = A - A * X ^ 1 * C 5 + A * X ^ 2 * C 10 - A * X ^ 3 * C 10 + A * X ^ 4 * C 5 - A * X ^ 5 := by
    simp only [map_ofNat] <;> ring
  have hright : (11 - 9 * X - 2 * X ^ 2 + 9 * X ^ 3 + X ^ 4 - 2 * X ^ 5 : PowerSeries ℚ) = C 11 - C 9 * X ^ 1 - C 2 * X ^ 2 + C 9 * X ^ 3 + X ^ 4 - C 2 * X ^ 5 := by
    simp only [map_ofNat] <;> ring
  change A * (1 - X) ^ 5 = _
  rw [hleft, hright]
  apply PowerSeries.ext
  intro d
  simp only [map_add, map_sub, map_neg, coeff_mul_C, coeff_mul_X_pow', coeff_C_mul, coeff_C,
    coeff_X_pow, A, coeff_mk]
  by_cases hd : d < 6
  · interval_cases d <;> simp [hf, v1, v2, v3, v4, v5, v6] <;> norm_num
  · simp (disch := omega) only [if_pos, if_neg]
    rw [hfd d (by omega), hfd (d - 1) (by omega), hfd (d - 2) (by omega), hfd (d - 3) (by omega), hfd (d - 4) (by omega), hfd (d - 5) (by omega)]
    simp (disch := omega) only [Nat.cast_sub, Nat.cast_ofNat, Nat.cast_one]
    linear_combination fdp (d : ℚ)

theorem main_proof :
    (PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (1 - X) ^ 5 =
      11 - 9 * X - 2 * X ^ 2 + 9 * X ^ 3 + X ^ 4 - 2 * X ^ 5) ∧
    (∀ n > 6, (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5)) :=
  ⟨gf, fun n hn => recurrence n hn⟩

end OMA.S_oeis_a223834

theorem OMA.solution : type_of% @OMA.S_oeis_a223834.main := OMA.S_oeis_a223834.main_proof
