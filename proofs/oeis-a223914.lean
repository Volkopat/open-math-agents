import OMAStatements.S_oeis_a223914
import Mathlib

/-!
Proof of A223914 (Hardin's empirical formula and Barker's g.f. and recurrence).
Credit: @prathameshnium (agent: Claude Code, model claude-opus-5-5)

Method: arrays are read row by row by a finite automaton whose state is the last row and, for every
line through it, whether that line has already descended. A generic library (below) proves that the
automaton accepts exactly the arrays of the statement; its table (106 live states) is checked by
`decide +kernel`. The counts from every state satisfy (E - 1)^9 = 0 from shift 2 on, checked by the
kernel at one shift and lifted to all shifts; that gives Hardin's polynomial, and from it Barker's
recurrence and g.f.
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

namespace OMA.S_oeis_a223914

open UniLib Finset PowerSeries

def dl : List (List ℕ) := [[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 106, 106, 11, 12, 13, 14, 15, 16, 17, 106, 106, 18, 19, 106, 20, 21, 22, 23, 106, 106, 106, 106, 106, 106, 106, 106, 24, 106, 106, 25, 26, 27, 28, 29, 30, 31, 106, 106, 32, 33, 106, 34, 35, 36, 37, 106, 106, 106, 106, 106, 106, 106, 106, 38, 106, 106, 39, 40, 106, 106, 106, 106, 41, 106, 106, 42, 43, 106, 44, 45, 46], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 106, 106, 11, 12, 13, 14, 15, 16, 17, 106, 106, 18, 19, 106, 20, 21, 22, 23, 106, 106, 106, 106, 106, 106, 106, 106, 24, 106, 106, 25, 26, 27, 28, 29, 30, 31, 106, 106, 32, 33, 106, 34, 35, 36, 37, 106, 106, 106, 106, 106, 106, 106, 106, 38, 106, 106, 39, 40, 106, 106, 106, 106, 41, 106, 106, 42, 43, 106, 44, 45, 46], [106, 2, 3, 106, 5, 6, 106, 8, 9, 106, 106, 106, 106, 12, 13, 106, 15, 16, 106, 106, 106, 106, 19, 106, 106, 21, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 26, 27, 106, 29, 30, 106, 106, 106, 106, 33, 106, 106, 35, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 40, 106, 106, 106, 106, 106, 106, 106, 106, 43, 106, 106, 45, 46], [106, 106, 3, 106, 106, 6, 106, 106, 9, 106, 106, 106, 106, 106, 13, 106, 106, 16, 106, 106, 106, 106, 106, 106, 106, 106, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 27, 106, 106, 30, 106, 106, 106, 106, 106, 106, 106, 106, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 46], [106, 106, 106, 47, 5, 6, 48, 8, 9, 106, 106, 106, 49, 12, 13, 50, 15, 16, 106, 106, 106, 51, 19, 106, 52, 21, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 53, 26, 27, 54, 29, 30, 106, 106, 106, 55, 33, 106, 56, 35, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 57, 40, 106, 106, 106, 106, 106, 106, 106, 58, 43, 106, 59, 45, 46], [106, 106, 106, 106, 5, 6, 106, 8, 9, 106, 106, 106, 106, 12, 13, 106, 15, 16, 106, 106, 106, 106, 19, 106, 106, 21, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 26, 27, 106, 29, 30, 106, 106, 106, 106, 33, 106, 106, 35, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 40, 106, 106, 106, 106, 106, 106, 106, 106, 43, 106, 106, 45, 46], [106, 106, 106, 106, 106, 6, 106, 106, 9, 106, 106, 106, 106, 106, 13, 106, 106, 16, 106, 106, 106, 106, 106, 106, 106, 106, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 27, 106, 106, 30, 106, 106, 106, 106, 106, 106, 106, 106, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 46], [106, 106, 106, 106, 106, 106, 48, 60, 9, 106, 106, 106, 106, 106, 106, 50, 61, 16, 106, 106, 106, 106, 106, 106, 52, 62, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 54, 63, 30, 106, 106, 106, 106, 106, 106, 56, 64, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 59, 65, 46], [106, 106, 106, 106, 106, 106, 106, 60, 9, 106, 106, 106, 106, 106, 106, 106, 61, 16, 106, 106, 106, 106, 106, 106, 106, 62, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 63, 30, 106, 106, 106, 106, 106, 106, 106, 64, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 65, 46], [106, 106, 106, 106, 106, 106, 106, 106, 9, 106, 106, 106, 106, 106, 106, 106, 106, 16, 106, 106, 106, 106, 106, 106, 106, 106, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 30, 106, 106, 106, 106, 106, 106, 106, 106, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 66, 106, 106, 11, 12, 13, 14, 15, 16, 67, 106, 106, 18, 19, 106, 20, 21, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 68, 106, 106, 25, 26, 27, 28, 29, 30, 69, 106, 106, 32, 33, 106, 34, 35, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 70, 106, 106, 39, 40, 106, 106, 106, 106, 71, 106, 106, 42, 43, 106, 44, 45, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 49, 12, 13, 50, 15, 16, 106, 106, 106, 51, 19, 106, 52, 21, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 53, 26, 27, 54, 29, 30, 106, 106, 106, 55, 33, 106, 56, 35, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 57, 40, 106, 106, 106, 106, 106, 106, 106, 58, 43, 106, 59, 45, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 12, 13, 106, 15, 16, 106, 106, 106, 106, 19, 106, 106, 21, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 26, 27, 106, 29, 30, 106, 106, 106, 106, 33, 106, 106, 35, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 40, 106, 106, 106, 106, 106, 106, 106, 106, 43, 106, 106, 45, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 13, 106, 106, 16, 106, 106, 106, 106, 106, 106, 106, 106, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 27, 106, 106, 30, 106, 106, 106, 106, 106, 106, 106, 106, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 50, 61, 16, 106, 106, 106, 106, 106, 106, 52, 62, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 54, 63, 30, 106, 106, 106, 106, 106, 106, 56, 64, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 59, 65, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 61, 16, 106, 106, 106, 106, 106, 106, 106, 62, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 63, 30, 106, 106, 106, 106, 106, 106, 106, 64, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 65, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 16, 106, 106, 106, 106, 106, 106, 106, 106, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 30, 106, 106, 106, 106, 106, 106, 106, 106, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 67, 106, 106, 72, 73, 106, 20, 21, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 69, 106, 106, 74, 75, 106, 34, 35, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 71, 106, 106, 76, 77, 106, 44, 45, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 78, 73, 106, 52, 21, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 79, 75, 106, 56, 35, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 80, 77, 106, 59, 45, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 73, 106, 106, 21, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 75, 106, 106, 35, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 77, 106, 106, 45, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 52, 62, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 56, 64, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 59, 65, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 62, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 64, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 65, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 81, 106, 106, 106, 106, 106, 106, 106, 106, 24, 106, 106, 25, 26, 27, 28, 29, 30, 31, 106, 106, 32, 33, 106, 34, 35, 36, 82, 106, 106, 106, 106, 106, 106, 106, 106, 38, 106, 106, 39, 40, 106, 106, 106, 106, 41, 106, 106, 42, 43, 106, 44, 45, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 68, 106, 106, 25, 26, 27, 28, 29, 30, 69, 106, 106, 32, 33, 106, 34, 35, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 70, 106, 106, 39, 40, 106, 106, 106, 106, 71, 106, 106, 42, 43, 106, 44, 45, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 53, 26, 27, 54, 29, 30, 106, 106, 106, 55, 33, 106, 56, 35, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 57, 40, 106, 106, 106, 106, 106, 106, 106, 58, 43, 106, 59, 45, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 26, 27, 106, 29, 30, 106, 106, 106, 106, 33, 106, 106, 35, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 40, 106, 106, 106, 106, 106, 106, 106, 106, 43, 106, 106, 45, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 27, 106, 106, 30, 106, 106, 106, 106, 106, 106, 106, 106, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 54, 63, 30, 106, 106, 106, 106, 106, 106, 56, 64, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 59, 65, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 63, 30, 106, 106, 106, 106, 106, 106, 106, 64, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 65, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 30, 106, 106, 106, 106, 106, 106, 106, 106, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 69, 106, 106, 74, 75, 106, 34, 35, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 71, 106, 106, 76, 77, 106, 44, 45, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 79, 75, 106, 56, 35, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 80, 77, 106, 59, 45, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 75, 106, 106, 35, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 77, 106, 106, 45, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 56, 64, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 59, 65, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 64, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 65, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 82, 106, 106, 106, 106, 106, 106, 106, 106, 83, 106, 106, 84, 85, 106, 106, 106, 106, 41, 106, 106, 42, 43, 106, 44, 45, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 86, 106, 106, 84, 85, 106, 106, 106, 106, 71, 106, 106, 42, 43, 106, 44, 45, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 87, 85, 106, 106, 106, 106, 106, 106, 106, 58, 43, 106, 59, 45, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 85, 106, 106, 106, 106, 106, 106, 106, 106, 43, 106, 106, 45, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 71, 106, 106, 76, 77, 106, 44, 45, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 80, 77, 106, 59, 45, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 77, 106, 106, 45, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 59, 65, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 65, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 46], [106, 106, 106, 47, 5, 6, 48, 8, 9, 106, 106, 106, 49, 12, 13, 50, 15, 16, 106, 106, 106, 51, 19, 106, 52, 21, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 53, 26, 27, 54, 29, 30, 106, 106, 106, 55, 33, 106, 56, 35, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 57, 40, 106, 106, 106, 106, 106, 106, 106, 58, 43, 106, 59, 45, 46], [106, 106, 106, 106, 106, 106, 48, 60, 9, 106, 106, 106, 106, 106, 106, 50, 61, 16, 106, 106, 106, 106, 106, 106, 52, 62, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 54, 63, 30, 106, 106, 106, 106, 106, 106, 56, 64, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 59, 65, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 49, 12, 13, 50, 15, 16, 106, 106, 106, 51, 19, 106, 52, 21, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 53, 26, 27, 54, 29, 30, 106, 106, 106, 55, 33, 106, 56, 35, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 57, 40, 106, 106, 106, 106, 106, 106, 106, 58, 43, 106, 59, 45, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 50, 61, 16, 106, 106, 106, 106, 106, 106, 52, 62, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 54, 63, 30, 106, 106, 106, 106, 106, 106, 56, 64, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 59, 65, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 78, 73, 106, 52, 21, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 79, 75, 106, 56, 35, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 80, 77, 106, 59, 45, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 52, 62, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 56, 64, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 59, 65, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 53, 26, 27, 54, 29, 30, 106, 106, 106, 55, 33, 106, 56, 35, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 57, 40, 106, 106, 106, 106, 106, 106, 106, 58, 43, 106, 59, 45, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 54, 63, 30, 106, 106, 106, 106, 106, 106, 56, 64, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 59, 65, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 79, 75, 106, 56, 35, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 80, 77, 106, 59, 45, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 56, 64, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 59, 65, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 87, 85, 106, 106, 106, 106, 106, 106, 106, 58, 43, 106, 59, 45, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 80, 77, 106, 59, 45, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 59, 65, 46], [106, 106, 106, 106, 106, 106, 106, 60, 9, 106, 106, 106, 106, 106, 106, 106, 61, 16, 106, 106, 106, 106, 106, 106, 106, 62, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 63, 30, 106, 106, 106, 106, 106, 106, 106, 64, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 65, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 61, 16, 106, 106, 106, 106, 106, 106, 106, 62, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 63, 30, 106, 106, 106, 106, 106, 106, 106, 64, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 65, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 62, 22, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 64, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 65, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 63, 30, 106, 106, 106, 106, 106, 106, 106, 64, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 65, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 64, 36, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 65, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 65, 46], [106, 106, 106, 106, 106, 106, 106, 106, 106, 88, 106, 106, 49, 106, 106, 50, 106, 106, 89, 106, 106, 51, 106, 106, 52, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 90, 106, 106, 53, 106, 106, 54, 106, 106, 91, 106, 106, 55, 106, 106, 56, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 92, 106, 106, 57, 106, 106, 106, 106, 106, 93, 106, 106, 58, 106, 106, 59, 106, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 89, 106, 106, 78, 106, 106, 52, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 91, 106, 106, 79, 106, 106, 56, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 93, 106, 106, 80, 106, 106, 59, 106, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 90, 106, 106, 53, 106, 106, 54, 106, 106, 91, 106, 106, 55, 106, 106, 56, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 92, 106, 106, 57, 106, 106, 106, 106, 106, 93, 106, 106, 58, 106, 106, 59, 106, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 91, 106, 106, 79, 106, 106, 56, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 93, 106, 106, 80, 106, 106, 59, 106, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 94, 106, 106, 87, 106, 106, 106, 106, 106, 93, 106, 106, 58, 106, 106, 59, 106, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 93, 106, 106, 80, 106, 106, 59, 106, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 78, 95, 106, 52, 62, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 79, 96, 106, 56, 64, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 80, 97, 106, 59, 65, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 95, 106, 106, 62, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 96, 106, 106, 64, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 97, 106, 106, 65, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 79, 96, 106, 56, 64, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 80, 97, 106, 59, 65, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 96, 106, 106, 64, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 97, 106, 106, 65, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 80, 97, 106, 59, 65, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 97, 106, 106, 65, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 78, 95, 106, 52, 62, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 79, 96, 106, 56, 64, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 80, 97, 106, 59, 65, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 79, 96, 106, 56, 64, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 80, 97, 106, 59, 65, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 80, 97, 106, 59, 65, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 98, 106, 106, 106, 106, 106, 106, 106, 106, 68, 106, 106, 106, 106, 106, 106, 106, 106, 69, 106, 106, 106, 106, 106, 106, 106, 106, 99, 106, 106, 106, 106, 106, 106, 106, 106, 70, 106, 106, 106, 106, 106, 106, 106, 106, 71, 106, 106, 106, 106, 106, 106, 106, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 99, 106, 106, 106, 106, 106, 106, 106, 106, 86, 106, 106, 106, 106, 106, 106, 106, 106, 71, 106, 106, 106, 106, 106, 106, 106, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 86, 106, 106, 100, 101, 106, 106, 106, 106, 71, 106, 106, 76, 77, 106, 106, 106, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 102, 101, 106, 106, 106, 106, 106, 106, 106, 80, 77, 106, 106, 106, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 101, 106, 106, 106, 106, 106, 106, 106, 106, 77, 106, 106, 106, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 94, 106, 106, 102, 106, 106, 106, 106, 106, 93, 106, 106, 80, 106, 106, 106, 106, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 102, 101, 106, 106, 106, 106, 106, 106, 106, 80, 77, 106, 106, 106, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 88, 106, 106, 49, 106, 106, 50, 106, 106, 89, 106, 106, 51, 106, 106, 52, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 90, 106, 106, 53, 106, 106, 54, 106, 106, 91, 106, 106, 55, 106, 106, 56, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 92, 106, 106, 57, 106, 106, 106, 106, 106, 93, 106, 106, 58, 106, 106, 59, 106, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 89, 106, 106, 78, 106, 106, 52, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 91, 106, 106, 79, 106, 106, 56, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 93, 106, 106, 80, 106, 106, 59, 106, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 90, 106, 106, 53, 106, 106, 54, 106, 106, 91, 106, 106, 55, 106, 106, 56, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 92, 106, 106, 57, 106, 106, 106, 106, 106, 93, 106, 106, 58, 106, 106, 59, 106, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 91, 106, 106, 79, 106, 106, 56, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 93, 106, 106, 80, 106, 106, 59, 106, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 94, 106, 106, 87, 106, 106, 106, 106, 106, 93, 106, 106, 58, 106, 106, 59, 106, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 93, 106, 106, 80, 106, 106, 59, 106, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 94, 106, 106, 102, 106, 106, 106, 106, 106, 93, 106, 106, 80, 106, 106, 106, 106, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 95, 106, 106, 62, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 96, 106, 106, 64, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 97, 106, 106, 65, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 96, 106, 106, 64, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 97, 106, 106, 65, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 97, 106, 106, 65, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 103, 106, 106, 106, 106, 106, 106, 106, 106, 90, 106, 106, 106, 106, 106, 106, 106, 106, 91, 106, 106, 106, 106, 106, 106, 106, 106, 104, 106, 106, 106, 106, 106, 106, 106, 106, 92, 106, 106, 106, 106, 106, 106, 106, 106, 93, 106, 106, 106, 106, 106, 106, 106, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 104, 106, 106, 106, 106, 106, 106, 106, 106, 94, 106, 106, 106, 106, 106, 106, 106, 106, 93, 106, 106, 106, 106, 106, 106, 106, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 102, 105, 106, 106, 106, 106, 106, 106, 106, 80, 97, 106, 106, 106, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 105, 106, 106, 106, 106, 106, 106, 106, 106, 97, 106, 106, 106, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 102, 105, 106, 106, 106, 106, 106, 106, 106, 80, 97, 106, 106, 106, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 103, 106, 106, 106, 106, 106, 106, 106, 106, 90, 106, 106, 106, 106, 106, 106, 106, 106, 91, 106, 106, 106, 106, 106, 106, 106, 106, 104, 106, 106, 106, 106, 106, 106, 106, 106, 92, 106, 106, 106, 106, 106, 106, 106, 106, 93, 106, 106, 106, 106, 106, 106, 106, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 104, 106, 106, 106, 106, 106, 106, 106, 106, 94, 106, 106, 106, 106, 106, 106, 106, 106, 93, 106, 106, 106, 106, 106, 106, 106, 106], [106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 106, 105, 106, 106, 106, 106, 106, 106, 106, 106, 97, 106, 106, 106, 106]]
def rowL : List (List ℕ) := [[], [0, 0, 0, 0], [1, 0, 0, 0], [2, 0, 0, 0], [0, 1, 0, 0], [1, 1, 0, 0], [2, 1, 0, 0], [0, 2, 0, 0], [1, 2, 0, 0], [2, 2, 0, 0], [0, 0, 1, 0], [0, 1, 1, 0], [1, 1, 1, 0], [2, 1, 1, 0], [0, 2, 1, 0], [1, 2, 1, 0], [2, 2, 1, 0], [0, 0, 2, 0], [0, 1, 2, 0], [1, 1, 2, 0], [0, 2, 2, 0], [1, 2, 2, 0], [2, 2, 2, 0], [0, 0, 0, 1], [0, 0, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1], [2, 1, 1, 1], [0, 2, 1, 1], [1, 2, 1, 1], [2, 2, 1, 1], [0, 0, 2, 1], [0, 1, 2, 1], [1, 1, 2, 1], [0, 2, 2, 1], [1, 2, 2, 1], [2, 2, 2, 1], [0, 0, 0, 2], [0, 0, 1, 2], [0, 1, 1, 2], [1, 1, 1, 2], [0, 0, 2, 2], [0, 1, 2, 2], [1, 1, 2, 2], [0, 2, 2, 2], [1, 2, 2, 2], [2, 2, 2, 2], [0, 1, 0, 0], [0, 2, 0, 0], [0, 1, 1, 0], [0, 2, 1, 0], [0, 1, 2, 0], [0, 2, 2, 0], [0, 1, 1, 1], [0, 2, 1, 1], [0, 1, 2, 1], [0, 2, 2, 1], [0, 1, 1, 2], [0, 1, 2, 2], [0, 2, 2, 2], [1, 2, 0, 0], [1, 2, 1, 0], [1, 2, 2, 0], [1, 2, 1, 1], [1, 2, 2, 1], [1, 2, 2, 2], [0, 0, 1, 0], [0, 0, 2, 0], [0, 0, 1, 1], [0, 0, 2, 1], [0, 0, 1, 2], [0, 0, 2, 2], [0, 1, 2, 0], [1, 1, 2, 0], [0, 1, 2, 1], [1, 1, 2, 1], [0, 1, 2, 2], [1, 1, 2, 2], [0, 1, 2, 0], [0, 1, 2, 1], [0, 1, 2, 2], [0, 0, 0, 1], [0, 0, 0, 2], [0, 0, 1, 2], [0, 1, 1, 2], [1, 1, 1, 2], [0, 0, 1, 2], [0, 1, 1, 2], [0, 0, 1, 0], [0, 0, 2, 0], [0, 0, 1, 1], [0, 0, 2, 1], [0, 0, 1, 2], [0, 0, 2, 2], [0, 0, 1, 2], [1, 1, 2, 0], [1, 1, 2, 1], [1, 1, 2, 2], [0, 0, 0, 1], [0, 0, 0, 2], [0, 1, 1, 2], [1, 1, 1, 2], [0, 1, 1, 2], [0, 0, 0, 1], [0, 0, 0, 2], [1, 1, 1, 2]]
def fcL : List (List Bool) := [[], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false]]
def fdL : List (List Bool) := [[], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false]]
def faL : List (List Bool) := [[], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [false, false, false, false], [true, false, false, false], [true, false, false, false], [true, false, false, false], [true, false, false, false], [true, false, false, false], [true, false, false, false], [true, false, false, false], [true, false, false, false], [true, false, false, false], [true, false, false, false], [true, false, false, false], [true, false, false, false], [true, false, false, false], [true, false, false, false], [true, false, false, false], [true, false, false, false], [true, false, false, false], [true, false, false, false], [true, false, false, false], [false, true, false, false], [false, true, false, false], [false, true, false, false], [false, true, false, false], [false, true, false, false], [false, true, false, false], [false, true, false, false], [false, true, false, false], [false, true, false, false], [false, true, false, false], [false, true, false, false], [false, true, false, false], [true, true, false, false], [true, true, false, false], [true, true, false, false], [false, false, true, false], [false, false, true, false], [false, false, true, false], [false, false, true, false], [false, false, true, false], [false, true, true, false], [true, false, true, false], [true, true, false, false], [true, true, false, false], [true, true, false, false], [true, true, false, false], [true, true, false, false], [true, true, false, false], [true, true, true, false], [true, true, false, false], [true, true, false, false], [true, true, false, false], [false, true, true, false], [false, true, true, false], [false, true, true, false], [false, true, true, false], [true, true, true, false], [true, true, true, false], [true, true, true, false], [true, true, true, false]]

set_option maxRecDepth 400000 in
theorem table_ok : TableOK false false true 4 3 106 dl rowL fcL fdL faL := by decide +kernel

theorem pred_iff (n : ℕ) (x : Fin n → Fin 4 → Fin 3) :
    (RowsUnimodal x ∧ ColumnsNondecreasing x ∧ AntidiagonalsUnimodal x) ↔ P false false true n 4 (Xw 4 3 (fun i => finFunctionFinEquiv (x i))) := by
  have hX := arr_val x
  unfold RowsUnimodal ColumnsNondecreasing AntidiagonalsUnimodal
  rw [rows_fin x _ hX, colnd_fin x _ hX, anti_fin x _ hX]
  unfold P
  rw [if_neg (by decide)]
  exact ⟨fun ⟨h0, h1, h2⟩ => ⟨h0, h1, fun h => absurd h (by decide), fun _ => h2⟩, fun ⟨h0, h1, h2, h3⟩ => ⟨h0, h1, h3 rfl⟩⟩

theorem a_eq (n : ℕ) (hn : 1 ≤ n) : a n = TMLib.cnt (δA 4 3 106 dl) (fun q => decide (q ≠ 106)) n 0 := by
  unfold a
  rw [count_arrays _ (pred_iff n), count_words false false true 4 3 106 dl rowL fcL fdL faL table_ok n hn]

theorem cl : ∀ q < 107, ∀ a : Fin (3 ^ 4), δA 4 3 106 dl q a < 107 := by
  have h : ∀ q, q < 107 → ∀ c, c < 3 ^ 4 → δt 106 dl q c < 107 := by decide +kernel
  intro q hq a
  exact h q hq a.val a.isLt

def cc (i : ℕ) : ℤ := ([1, -9, 36, -84, 126, -126, 84, -36, 9] : List ℤ).getD i 0

set_option maxRecDepth 400000 in
theorem vrel : ∀ q, q < 107 → ((TMLib.cntV (δA 4 3 106 dl) (fun q => decide (q ≠ 106)) 107 (2 + 9)).getD q 0 : ℤ) =
    ∑ i ∈ range 9, cc i * ((TMLib.cntV (δA 4 3 106 dl) (fun q => decide (q ≠ 106)) 107 (2 + i)).getD q 0 : ℤ) := by
  decide +kernel

theorem xrec (n : ℕ) : (TMLib.cnt (δA 4 3 106 dl) (fun q => decide (q ≠ 106)) (n + 2 + 9) 0 : ℤ) =
    ∑ i ∈ range 9, cc i * (TMLib.cnt (δA 4 3 106 dl) (fun q => decide (q ≠ 106)) (n + 2 + i) 0 : ℤ) := by
  have hS : ∀ q ∈ range 107, ∀ a : Fin (3 ^ 4), δA 4 3 106 dl q a ∈ range 107 :=
    fun q hq a => mem_range.2 (cl q (mem_range.1 hq) a)
  exact TMLib.cnt_rec (δA 4 3 106 dl) (fun q => decide (q ≠ 106)) (range 107) hS 9 cc 2 (fun q hq => by
    have hq' := mem_range.1 hq
    have h := vrel q hq'
    rw [TMLib.cntV_eq (δA 4 3 106 dl) (fun q => decide (q ≠ 106)) 107 cl (2 + 9) q hq'] at h
    rw [h]
    apply sum_congr rfl
    intro i _
    rw [TMLib.cntV_eq (δA 4 3 106 dl) (fun q => decide (q ≠ 106)) 107 cl (2 + i) q hq']) n 0 (mem_range.2 (by norm_num))

def Pz (t : ℤ) : ℤ := 205 * t ^ 8 + 2460 * t ^ 7 + 17878 * t ^ 6 + 80052 * t ^ 5 + 187705 * t ^ 4 + 352800 * t ^ 3 + 338532 * t ^ 2 - 32112 * t - 141120

theorem hP (t : ℤ) : Pz (t + 9) = ∑ i ∈ range 9, cc i * Pz (t + i) := by
  simp only [Pz, cc, sum_range_succ, sum_range_zero, List.getD_cons_zero, List.getD_cons_succ]
  push_cast
  ring

set_option maxRecDepth 400000 in
theorem hv : ∀ m, m < 2 + 2 + 9 → 2 ≤ m →
    20160 * ((TMLib.cntV (δA 4 3 106 dl) (fun q => decide (q ≠ 106)) 107 m).getD 0 0 : ℤ) = Pz m := by
  decide +kernel

theorem cast_count (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) = 41/4032 * (n : ℚ) ^ 8 + 41/336 * (n : ℚ) ^ 7 + 1277/1440 * (n : ℚ) ^ 6 + 953/240 * (n : ℚ) ^ 5 + 5363/576 * (n : ℚ) ^ 4 + 35/2 * (n : ℚ) ^ 3 + 28211/1680 * (n : ℚ) ^ 2 - 223/140 * (n : ℚ) - 7 := by
  have h := TMLib.rec_poly (fun m => (TMLib.cnt (δA 4 3 106 dl) (fun q => decide (q ≠ 106)) m 0 : ℤ)) 9 2 2 cc Pz 20160
    xrec hP (fun m h1 h2 => by
      have := hv m h2 h1
      rwa [TMLib.cntV_eq (δA 4 3 106 dl) (fun q => decide (q ≠ 106)) 107 cl m 0 (by norm_num)] at this) n hn
  rw [← a_eq n (by omega)] at h
  have h' : ((20160 : ℤ) : ℚ) * (a n : ℚ) = ((Pz n : ℤ) : ℚ) := by exact_mod_cast h
  simp only [Pz] at h'
  push_cast at h'
  linarith

theorem recurrence (n : ℕ) (hn : 10 < n) : (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  have key : (a n : ℚ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
    rw [cast_count n (by omega), cast_count (n - 1) (by omega), cast_count (n - 2) (by omega), cast_count (n - 3) (by omega), cast_count (n - 4) (by omega), cast_count (n - 5) (by omega), cast_count (n - 6) (by omega), cast_count (n - 7) (by omega), cast_count (n - 8) (by omega), cast_count (n - 9) (by omega)]
    push_cast [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_sub (show 3 ≤ n by omega), Nat.cast_sub (show 4 ≤ n by omega), Nat.cast_sub (show 5 ≤ n by omega), Nat.cast_sub (show 6 ≤ n by omega), Nat.cast_sub (show 7 ≤ n by omega), Nat.cast_sub (show 8 ≤ n by omega), Nat.cast_sub (show 9 ≤ n by omega)]
    ring
  exact_mod_cast key

def pQ (t : ℚ) : ℚ := 41/4032 * t ^ 8 + 41/336 * t ^ 7 + 1277/1440 * t ^ 6 + 953/240 * t ^ 5 + 5363/576 * t ^ 4 + 35/2 * t ^ 3 + 28211/1680 * t ^ 2 - 223/140 * t - 7

theorem fd (t : ℚ) : pQ t - 9 * pQ (t - 1) + 36 * pQ (t - 2) - 84 * pQ (t - 3) + 126 * pQ (t - 4) - 126 * pQ (t - 5) + 84 * pQ (t - 6) - 36 * pQ (t - 7) + 9 * pQ (t - 8) - pQ (t - 9) = 0 := by
  unfold pQ
  ring

theorem v1 : a 1 = 46 := by
  rw [a_eq 1 (by norm_num), ← TMLib.cntV_eq (δA 4 3 106 dl) (fun q => decide (q ≠ 106)) 107 cl 1 0 (by norm_num)]
  decide +kernel
theorem v2 : a 2 = 548 := by
  rw [a_eq 2 (by norm_num), ← TMLib.cntV_eq (δA 4 3 106 dl) (fun q => decide (q ≠ 106)) 107 cl 2 0 (by norm_num)]
  decide +kernel
theorem v3 : a 3 = 3311 := by
  rw [a_eq 3 (by norm_num), ← TMLib.cntV_eq (δA 4 3 106 dl) (fun q => decide (q ≠ 106)) 107 cl 3 0 (by norm_num)]
  decide +kernel
theorem v4 : a 4 = 14123 := by
  rw [a_eq 4 (by norm_num), ← TMLib.cntV_eq (δA 4 3 106 dl) (fun q => decide (q ≠ 106)) 107 cl 4 0 (by norm_num)]
  decide +kernel
theorem v5 : a 5 = 48182 := by
  rw [a_eq 5 (by norm_num), ← TMLib.cntV_eq (δA 4 3 106 dl) (fun q => decide (q ≠ 106)) 107 cl 5 0 (by norm_num)]
  decide +kernel
theorem v6 : a 6 = 139925 := by
  rw [a_eq 6 (by norm_num), ← TMLib.cntV_eq (δA 4 3 106 dl) (fun q => decide (q ≠ 106)) 107 cl 6 0 (by norm_num)]
  decide +kernel
theorem v7 : a 7 = 359344 := by
  rw [a_eq 7 (by norm_num), ← TMLib.cntV_eq (δA 4 3 106 dl) (fun q => decide (q ≠ 106)) 107 cl 7 0 (by norm_num)]
  decide +kernel
theorem v8 : a 8 = 837243 := by
  rw [a_eq 8 (by norm_num), ← TMLib.cntV_eq (δA 4 3 106 dl) (fun q => decide (q ≠ 106)) 107 cl 8 0 (by norm_num)]
  decide +kernel
theorem v9 : a 9 = 1802306 := by
  rw [a_eq 9 (by norm_num), ← TMLib.cntV_eq (δA 4 3 106 dl) (fun q => decide (q ≠ 106)) 107 cl 9 0 (by norm_num)]
  decide +kernel
theorem v10 : a 10 = 3633256 := by
  rw [a_eq 10 (by norm_num), ← TMLib.cntV_eq (δA 4 3 106 dl) (fun q => decide (q ≠ 106)) 107 cl 10 0 (by norm_num)]
  decide +kernel

theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
    X * (46 + 134 * X + 35 * X ^ 2 + 188 * X ^ 3 + 35 * X ^ 4 - 157 * X ^ 5 + 241 * X ^ 6 - 153 * X ^ 7 + 47 * X ^ 8 - 6 * X ^ 9) := by
  set f : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hf
  have hfd : ∀ m, 2 ≤ m → f m = pQ m := by
    intro m hm
    rw [hf]
    simp only
    rw [if_neg (by omega), cast_count m hm]
    rfl
  let A : PowerSeries ℚ := PowerSeries.mk f
  have hleft : A * (1 - X) ^ 9 = A - A * X ^ 1 * C 9 + A * X ^ 2 * C 36 - A * X ^ 3 * C 84 + A * X ^ 4 * C 126 - A * X ^ 5 * C 126 + A * X ^ 6 * C 84 - A * X ^ 7 * C 36 + A * X ^ 8 * C 9 - A * X ^ 9 := by
    simp only [map_ofNat]
    ring
  have hright : (X : PowerSeries ℚ) * (46 + 134 * X + 35 * X ^ 2 + 188 * X ^ 3 + 35 * X ^ 4 - 157 * X ^ 5 + 241 * X ^ 6 - 153 * X ^ 7 + 47 * X ^ 8 - 6 * X ^ 9) = C 46 * X ^ 1 + C 134 * X ^ 2 + C 35 * X ^ 3 + C 188 * X ^ 4 + C 35 * X ^ 5 - C 157 * X ^ 6 + C 241 * X ^ 7 - C 153 * X ^ 8 + C 47 * X ^ 9 - C 6 * X ^ 10 := by
    simp only [map_ofNat]
    ring
  change A * (1 - X) ^ 9 = _
  rw [hleft, hright]
  apply PowerSeries.ext
  intro d
  simp only [map_add, map_sub, map_neg, coeff_mul_C, coeff_mul_X_pow', coeff_C_mul, coeff_C,
    coeff_X_pow, A, coeff_mk]
  by_cases hd : d < 11
  · interval_cases d <;> simp [hf, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10] <;> norm_num
  · simp (disch := omega) only [if_pos, if_neg]
    rw [hfd d (by omega), hfd (d - 1) (by omega), hfd (d - 2) (by omega), hfd (d - 3) (by omega), hfd (d - 4) (by omega), hfd (d - 5) (by omega), hfd (d - 6) (by omega), hfd (d - 7) (by omega), hfd (d - 8) (by omega), hfd (d - 9) (by omega)]
    simp (disch := omega) only [Nat.cast_sub, Nat.cast_ofNat, Nat.cast_one]
    linear_combination fd (d : ℚ)

theorem main_proof :
    (∀ n : ℕ, 1 < n → (a n : ℚ) = 41/4032 * (n : ℚ) ^ 8 + 41/336 * (n : ℚ) ^ 7 + 1277/1440 * (n : ℚ) ^ 6 + 953/240 * (n : ℚ) ^ 5 + 5363/576 * (n : ℚ) ^ 4 + 35/2 * (n : ℚ) ^ 3 + 28211/1680 * (n : ℚ) ^ 2 - 223/140 * (n : ℚ) - 7) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X * (46 + 134 * X + 35 * X ^ 2 + 188 * X ^ 3 + 35 * X ^ 4 - 157 * X ^ 5 + 241 * X ^ 6 - 153 * X ^ 7 + 47 * X ^ 8 - 6 * X ^ 9) ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) :=
  ⟨fun n hn => cast_count n (by omega), gf, recurrence⟩

end OMA.S_oeis_a223914

theorem OMA.solution : type_of% @OMA.S_oeis_a223914.main := OMA.S_oeis_a223914.main_proof
