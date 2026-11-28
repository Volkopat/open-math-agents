import OMAStatements.S_oeis_a190039

/-!
OEIS A190039 (R. H. Hardin, May 04 2011): Number of nondecreasing arrangements of n+2 numbers in 0..7 with the last equal to 7 and each after the second equal to the sum of one or two of the preceding three.
Conjectures from Colin Barker, May 04 2018: G.f.: x*(11 - 5*x - x^2 + 4*x^3 + 3*x^4 + 5*x^5 + 3*x^6) / (1 - x)^2. a(n) = 2*a(n-1) - a(n-2) for n>7.

Proof. Prefixes are counted by their last three entries: pref(m, p, q, r) counts the prefixes of
length m + 3 that are nondecreasing and satisfy the condition at every entry after the second,
ending with p, q, r; appending an entry d (Fin.snoc) gives pref(m + 1, q, r, d) = sum over p of [r
<= d and d is one of p, q, r or the sum of two of them] pref(m, p, q, r) (`pg_snoc`, `pref_succ`).
The continuation counts Gv satisfy the transposed recursion, so a(m + 1) = sum over the starts s of
pref(0, s) Gv(m, s) (`a_dual`). Tables of Gv for m <= 10, checked level by level on the
nondecreasing states (`g1_eq`, ...), give the small values and the vanishing of the second
difference of Gv at m = 8 (`vec_id`), which propagates to every later m by linearity (`R_zero`).
Hence the second difference of a vanishes from n = 6 on (`rec_a`), and the g.f. and the recurrence
follow by comparing coefficients.
-/

namespace OMA.S_oeis_a190039

open PowerSeries Finset


/-- The entry d may follow the entries p, q, r. -/
def okc (p q r d : ℕ) : Prop := d = p ∨ d = q ∨ d = r ∨ d = p + q ∨ d = p + r ∨ d = q + r

instance (p q r d : ℕ) : Decidable (okc p q r d) := by unfold okc; infer_instance

/-- The conditions on a prefix: nondecreasing, and every entry after the second is the sum of one or
two of the preceding three. -/
def pg {L : ℕ} (y : Fin L → Fin 8) : Prop := Monotone y ∧ ∀ i : Fin L, 2 ≤ (i : ℕ) → okAt y i

instance {L : ℕ} : DecidablePred (@pg L) := fun y => by unfold pg okAt Monotone; infer_instance

lemma snoc_lt {m : ℕ} (y : Fin (m + 3) → Fin 8) (d : Fin 8) (j : ℕ) (hj : j < m + 4) (h : j < m + 3) :
    (Fin.snoc y d : Fin (m + 4) → Fin 8) ⟨j, hj⟩ = y ⟨j, h⟩ := by
  simp [Fin.snoc, h]

lemma mono_snoc {m : ℕ} (y : Fin (m + 3) → Fin 8) (d : Fin 8) :
    Monotone (Fin.snoc y d : Fin (m + 4) → Fin 8) ↔ Monotone y ∧ y (Fin.last (m + 2)) ≤ d := by
  rw [Fin.monotone_iff_le_succ, Fin.monotone_iff_le_succ, Fin.forall_fin_succ']
  simp only [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, Fin.succ_castSucc]

lemma ok_snoc_cs {m : ℕ} (y : Fin (m + 3) → Fin 8) (d : Fin 8) (i : Fin (m + 3)) :
    okAt (Fin.snoc y d : Fin (m + 4) → Fin 8) i.castSucc ↔ okAt y i := by
  unfold okAt
  constructor
  · rintro ⟨⟨j, hjb⟩, ⟨l, hlb⟩, hj, hl, hj3, hl3, hv⟩
    simp only [Fin.lt_def, Fin.val_castSucc] at hj hl hj3 hl3
    have hji : j < m + 3 := by have := i.isLt; omega
    have hli : l < m + 3 := by have := i.isLt; omega
    rw [Fin.snoc_castSucc, snoc_lt y d j hjb hji, snoc_lt y d l hlb hli] at hv
    refine ⟨⟨j, hji⟩, ⟨l, hli⟩, by simp only [Fin.lt_def]; exact hj, by simp only [Fin.lt_def]; exact hl,
      hj3, hl3, ?_⟩
    simpa only [ne_eq, Fin.mk.injEq] using hv
  · rintro ⟨⟨j, hjb⟩, ⟨l, hlb⟩, hj, hl, hj3, hl3, hv⟩
    simp only [Fin.lt_def] at hj hl
    refine ⟨⟨j, by omega⟩, ⟨l, by omega⟩, by simp only [Fin.lt_def, Fin.val_castSucc]; exact hj,
      by simp only [Fin.lt_def, Fin.val_castSucc]; exact hl, by simpa using hj3, by simpa using hl3, ?_⟩
    rw [Fin.snoc_castSucc, snoc_lt y d j (by omega) hjb, snoc_lt y d l (by omega) hlb]
    simpa only [ne_eq, Fin.mk.injEq] using hv

lemma ok_snoc_last {m : ℕ} (y : Fin (m + 3) → Fin 8) (d : Fin 8) :
    okAt (Fin.snoc y d : Fin (m + 4) → Fin 8) (Fin.last (m + 3)) ↔
      okc (y ⟨m, by omega⟩) (y ⟨m + 1, by omega⟩) (y ⟨m + 2, by omega⟩) d := by
  unfold okAt okc
  rw [Fin.snoc_last]
  constructor
  · rintro ⟨⟨j, hjb⟩, ⟨l, hlb⟩, hj, hl, hj3, hl3, hv⟩
    simp only [Fin.lt_def, Fin.val_last] at hj hl hj3 hl3
    rw [snoc_lt y d j hjb hj, snoc_lt y d l hlb hl] at hv
    simp only [ne_eq, Fin.mk.injEq] at hv
    have hj' : j = m ∨ j = m + 1 ∨ j = m + 2 := by omega
    have hl' : l = m ∨ l = m + 1 ∨ l = m + 2 := by omega
    rcases hj' with rfl | rfl | rfl <;> rcases hl' with rfl | rfl | rfl <;> omega
  · have e0 := snoc_lt y d m (by omega) (by omega)
    have e1 := snoc_lt y d (m + 1) (by omega) (by omega)
    have e2 := snoc_lt y d (m + 2) (by omega) (by omega)
    intro h
    rcases h with h | h | h | h | h | h
    · exact ⟨⟨m, by omega⟩, ⟨m, by omega⟩, by simp [Fin.lt_def], by simp [Fin.lt_def], by simp, by simp,
        Or.inl (by rw [e0]; exact h)⟩
    · exact ⟨⟨m + 1, by omega⟩, ⟨m + 1, by omega⟩, by simp [Fin.lt_def], by simp [Fin.lt_def], by simp,
        by simp, Or.inl (by rw [e1]; exact h)⟩
    · exact ⟨⟨m + 2, by omega⟩, ⟨m + 2, by omega⟩, by simp [Fin.lt_def], by simp [Fin.lt_def], by simp,
        by simp, Or.inl (by rw [e2]; exact h)⟩
    · exact ⟨⟨m, by omega⟩, ⟨m + 1, by omega⟩, by simp [Fin.lt_def], by simp [Fin.lt_def], by simp,
        by simp, Or.inr ⟨by simp, by rw [e0, e1]; exact h⟩⟩
    · exact ⟨⟨m, by omega⟩, ⟨m + 2, by omega⟩, by simp [Fin.lt_def], by simp [Fin.lt_def], by simp,
        by simp, Or.inr ⟨by simp, by rw [e0, e2]; exact h⟩⟩
    · exact ⟨⟨m + 1, by omega⟩, ⟨m + 2, by omega⟩, by simp [Fin.lt_def], by simp [Fin.lt_def], by simp,
        by simp, Or.inr ⟨by simp, by rw [e1, e2]; exact h⟩⟩

lemma pg_snoc {m : ℕ} (y : Fin (m + 3) → Fin 8) (d : Fin 8) :
    pg (Fin.snoc y d : Fin (m + 4) → Fin 8) ↔
      pg y ∧ y (Fin.last (m + 2)) ≤ d ∧
        okc (y ⟨m, by omega⟩) (y ⟨m + 1, by omega⟩) (y ⟨m + 2, by omega⟩) d := by
  unfold pg
  rw [mono_snoc, Fin.forall_fin_succ']
  simp only [Fin.val_castSucc, ok_snoc_cs, Fin.val_last, ok_snoc_last, show 2 ≤ m + 3 by omega,
    true_implies]
  tauto

/-- The prefixes of length m + 3 ending with p, q, r. -/
def pref (m : ℕ) (p q r : Fin 8) : ℕ :=
  ((univ : Finset (Fin (m + 3) → Fin 8)).filter (fun y => pg y ∧
    y ⟨m, by omega⟩ = p ∧ y ⟨m + 1, by omega⟩ = q ∧ y ⟨m + 2, by omega⟩ = r)).card

lemma pref_succ (m : ℕ) (q r d : Fin 8) :
    pref (m + 1) q r d = ∑ p : Fin 8, if r ≤ d ∧ okc p q r d then pref m p q r else 0 := by
  have h1 : pref (m + 1) q r d = ((univ : Finset (Fin (m + 3) → Fin 8)).filter (fun y => pg y ∧
      y ⟨m + 1, by omega⟩ = q ∧ y ⟨m + 2, by omega⟩ = r ∧ r ≤ d ∧
        okc (y ⟨m, by omega⟩) q r d)).card := by
    show ((univ : Finset (Fin (m + 4) → Fin 8)).filter (fun x => pg x ∧
      x ⟨m + 1, by omega⟩ = q ∧ x ⟨m + 2, by omega⟩ = r ∧ x ⟨m + 3, by omega⟩ = d)).card = _
    refine card_bij' (fun x _ => Fin.init x) (fun y _ => Fin.snoc y d) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      obtain ⟨hpg, h1, h2, h3⟩ := hx
      have e : x = Fin.snoc (Fin.init x) d := by
        rw [← h3]
        exact (Fin.snoc_init_self x).symm
      rw [e, pg_snoc] at hpg
      obtain ⟨hp, hd, hc⟩ := hpg
      refine ⟨hp, h1, h2, ?_, ?_⟩
      · rw [← h2]
        exact hd
      · rw [← h1, ← h2]
        exact hc
    · intro y hy
      simp only [mem_filter, mem_univ, true_and] at hy ⊢
      obtain ⟨hp, h1, h2, hd, hc⟩ := hy
      refine ⟨(pg_snoc y d).mpr ⟨hp, ?_, ?_⟩, ?_, ?_, ?_⟩
      · rw [show (Fin.last (m + 2) : Fin (m + 3)) = ⟨m + 2, by omega⟩ from rfl, h2]
        exact hd
      · rw [h1, h2]
        exact hc
      · rw [snoc_lt y d (m + 1) (by omega) (by omega)]
        exact h1
      · rw [snoc_lt y d (m + 2) (by omega) (by omega)]
        exact h2
      · exact Fin.snoc_last (α := fun _ => Fin 8) d y
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx
      rw [← hx.2.2.2]
      exact Fin.snoc_init_self x
    · intro y _
      simp
  rw [h1, card_eq_sum_card_fiberwise (f := fun y => y ⟨m, by omega⟩) (t := univ) (by simp)]
  refine sum_congr rfl (fun p _ => ?_)
  rw [filter_filter]
  unfold pref
  split_ifs with hc
  · congr 1
    ext y
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨hp, h1, h2, _, _⟩, h0⟩
      exact ⟨hp, h0, h1, h2⟩
    · rintro ⟨hp, h0, h1, h2⟩
      refine ⟨⟨hp, h1, h2, hc.1, ?_⟩, h0⟩
      rw [h0]
      exact hc.2
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro y - ⟨⟨_, _, _, hd, hok⟩, h0⟩
    rw [h0] at hok
    exact hc ⟨hd, hok⟩

lemma pg3 : ∀ p q r : Fin 8, pg ![p, q, r] ↔
    (p ≤ q ∧ q ≤ r ∧ ((r : ℕ) = p ∨ (r : ℕ) = q ∨ (r : ℕ) = p + q)) := by
  decide +kernel

lemma pref_zero (p q r : Fin 8) :
    pref 0 p q r = if p ≤ q ∧ q ≤ r ∧ ((r : ℕ) = p ∨ (r : ℕ) = q ∨ (r : ℕ) = p + q) then 1 else 0 := by
  unfold pref
  have e : ∀ y : Fin 3 → Fin 8, y = ![y 0, y 1, y 2] := fun y => by
    funext i
    fin_cases i <;> rfl
  split_ifs with hc
  · rw [card_eq_one]
    refine ⟨![p, q, r], ?_⟩
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨_, h0, h1, h2⟩
      have h0' : y 0 = p := h0
      have h1' : y 1 = q := h1
      have h2' : y 2 = r := h2
      rw [e y, h0', h1', h2']
    · rintro rfl
      exact ⟨(pg3 p q r).mpr hc, rfl, rfl, rfl⟩
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro y - ⟨hp, h0, h1, h2⟩
    apply hc
    rw [e y] at hp
    have := (pg3 (y 0) (y 1) (y 2)).mp hp
    rw [show y 0 = p from h0, show y 1 = q from h1, show y 2 = r from h2] at this
    exact this

lemma a_eq (m : ℕ) : a (m + 1) = ∑ p : Fin 8, ∑ q : Fin 8, pref m p q ⟨7, by norm_num⟩ := by
  unfold a pref
  have hg : ∀ x : Fin (m + 3) → Fin 8, good x ↔ pg x ∧ x ⟨m + 2, by omega⟩ = ⟨7, by norm_num⟩ := by
    intro x
    unfold good pg
    rw [Fin.ext_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h3⟩, h2⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩
      exact ⟨h1, h2, h3⟩
  rw [filter_congr (fun x _ => hg x)]
  rw [card_eq_sum_card_fiberwise (f := fun x : Fin (m + 3) → Fin 8 => x ⟨m, by omega⟩) (t := univ) (by simp)]
  refine sum_congr rfl (fun p _ => ?_)
  rw [filter_filter,
    card_eq_sum_card_fiberwise (f := fun x : Fin (m + 3) → Fin 8 => x ⟨m + 1, by omega⟩) (t := univ) (by simp)]
  refine sum_congr rfl (fun q _ => ?_)
  rw [filter_filter]
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and]
  tauto

/-! Continuations: Gv m s counts the ways to continue m more entries from the last three entries s
and end with 7. -/

/-- The continuation counts. -/
def Gv : ℕ → Fin 8 → Fin 8 → Fin 8 → ℕ
  | 0, _, _, r => if (r : ℕ) = 7 then 1 else 0
  | m + 1, p, q, r => ∑ d : Fin 8, if r ≤ d ∧ okc p q r d then Gv m q r d else 0

lemma Gv_succ (m : ℕ) (p q r : Fin 8) :
    Gv (m + 1) p q r = ∑ d : Fin 8, if r ≤ d ∧ okc p q r d then Gv m q r d else 0 := rfl

lemma shift (m j : ℕ) :
    ∑ p : Fin 8, ∑ q : Fin 8, ∑ r : Fin 8, pref (m + 1) p q r * Gv j p q r =
      ∑ p : Fin 8, ∑ q : Fin 8, ∑ r : Fin 8, pref m p q r * Gv (j + 1) p q r := by
  simp only [pref_succ, Gv_succ, sum_mul, mul_sum, ite_mul, mul_ite, zero_mul, mul_zero]
  calc ∑ q : Fin 8, ∑ r : Fin 8, ∑ d : Fin 8, ∑ p : Fin 8,
        (if r ≤ d ∧ okc p q r d then pref m p q r * Gv j q r d else 0)
      = ∑ q : Fin 8, ∑ r : Fin 8, ∑ p : Fin 8, ∑ d : Fin 8,
        (if r ≤ d ∧ okc p q r d then pref m p q r * Gv j q r d else 0) :=
          sum_congr rfl (fun q _ => sum_congr rfl (fun r _ => Finset.sum_comm))
    _ = ∑ q : Fin 8, ∑ p : Fin 8, ∑ r : Fin 8, ∑ d : Fin 8,
        (if r ≤ d ∧ okc p q r d then pref m p q r * Gv j q r d else 0) :=
          sum_congr rfl (fun q _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

lemma a_dual (m : ℕ) :
    (a (m + 1) : ℤ) = ∑ p : Fin 8, ∑ q : Fin 8, ∑ r : Fin 8,
      (if p ≤ q ∧ q ≤ r ∧ ((r : ℕ) = p ∨ (r : ℕ) = q ∨ (r : ℕ) = p + q) then (1 : ℤ) else 0) *
        (Gv m p q r : ℤ) := by
  have h0 : a (m + 1) = ∑ p : Fin 8, ∑ q : Fin 8, ∑ r : Fin 8, pref m p q r * Gv 0 p q r := by
    rw [a_eq]
    refine sum_congr rfl (fun p _ => sum_congr rfl (fun q _ => ?_))
    have hk : ∀ r : Fin 8, ((r : ℕ) = 7) ↔ r = ⟨7, by norm_num⟩ := fun r => by rw [Fin.ext_iff]
    simp only [Gv, mul_ite, mul_one, mul_zero, hk, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hs : ∀ i j : ℕ, ∑ p : Fin 8, ∑ q : Fin 8, ∑ r : Fin 8, pref i p q r * Gv j p q r =
      ∑ p : Fin 8, ∑ q : Fin 8, ∑ r : Fin 8, pref 0 p q r * Gv (i + j) p q r := by
    intro i
    induction i with
    | zero => intro j; simp
    | succ i ih =>
      intro j
      rw [shift, ih, show i + (j + 1) = i + 1 + j by ring]
  rw [h0, hs, add_zero]
  push_cast
  simp only [pref_zero]
  push_cast
  rfl

/-! Gv for m ≤ 10, as tables g0, g1, ... checked level by level on the nondecreasing states. -/

/-- Gv 0 as a table. -/
def g0 : Fin 8 → Fin 8 → Fin 8 → ℕ :=
  ![![![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1]],
    ![![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 0, 1]]]

lemma g0_eq : ∀ p q r : Fin 8, p ≤ q → q ≤ r → g0 p q r = if (r : ℕ) = 7 then 1 else 0 := by
  decide +kernel

lemma Gv0 : ∀ p q r : Fin 8, p ≤ q → q ≤ r → Gv 0 p q r = g0 p q r := by
  intro p q r hpq hqr
  rw [g0_eq p q r hpq hqr]
  rfl

/-- Gv 1 as a table. -/
def g1 : Fin 8 → Fin 8 → Fin 8 → ℕ :=
  ![![![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 1, 0, 0, 1], ![0, 0, 0, 1, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 0, 0, 1], ![0, 1, 0, 0, 0, 0, 0, 1], ![1, 1, 1, 1, 1, 1, 1, 1]],
    ![![0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 1, 1, 1], ![0, 0, 0, 0, 1, 0, 1, 1], ![0, 0, 0, 1, 0, 0, 1, 1], ![0, 0, 1, 0, 0, 0, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1]],
    ![![0, 0, 0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 0, 1, 1, 1], ![0, 0, 0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 1, 1, 0, 1], ![0, 0, 0, 1, 0, 1, 0, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![0, 1, 0, 0, 0, 1, 0, 1], ![1, 1, 1, 1, 1, 1, 1, 1]],
    ![![0, 0, 0, 0, 1, 0, 0, 1], ![0, 0, 0, 0, 1, 0, 1, 1], ![0, 0, 0, 0, 1, 1, 0, 1], ![0, 0, 0, 0, 1, 0, 0, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![0, 0, 1, 0, 1, 0, 0, 1], ![0, 1, 0, 0, 1, 0, 0, 1], ![1, 1, 1, 1, 1, 1, 1, 1]],
    ![![0, 0, 0, 1, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0, 1, 1], ![0, 0, 0, 1, 0, 1, 0, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![0, 0, 0, 1, 0, 0, 0, 1], ![0, 0, 1, 1, 0, 0, 0, 1], ![0, 1, 0, 1, 0, 0, 0, 1], ![1, 1, 1, 1, 1, 1, 1, 1]],
    ![![0, 0, 1, 0, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 0, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![0, 0, 1, 0, 1, 0, 0, 1], ![0, 0, 1, 1, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 0, 0, 1], ![0, 1, 1, 0, 0, 0, 0, 1], ![1, 1, 1, 1, 1, 1, 1, 1]],
    ![![0, 1, 0, 0, 0, 0, 0, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![0, 1, 0, 0, 0, 1, 0, 1], ![0, 1, 0, 0, 1, 0, 0, 1], ![0, 1, 0, 1, 0, 0, 0, 1], ![0, 1, 1, 0, 0, 0, 0, 1], ![0, 1, 0, 0, 0, 0, 0, 1], ![1, 1, 1, 1, 1, 1, 1, 1]],
    ![![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1, 1]]]

lemma g1_eq : ∀ p q r : Fin 8, p ≤ q → q ≤ r →
    g1 p q r = ∑ d : Fin 8, if r ≤ d ∧ okc p q r d then g0 q r d else 0 := by
  decide +kernel

lemma Gv1 : ∀ p q r : Fin 8, p ≤ q → q ≤ r → Gv 1 p q r = g1 p q r := by
  intro p q r hpq hqr
  rw [Gv_succ, g1_eq p q r hpq hqr]
  refine sum_congr rfl (fun d _ => ?_)
  split_ifs with hc
  · rw [Gv0 q r d hqr hc.1]
  · rfl

/-- Gv 2 as a table. -/
def g2 : Fin 8 → Fin 8 → Fin 8 → ℕ :=
  ![![![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 1, 2, 1], ![0, 0, 0, 1, 0, 2, 0, 1], ![0, 1, 1, 0, 2, 0, 0, 1], ![0, 0, 0, 3, 0, 0, 0, 1], ![0, 1, 3, 0, 0, 0, 0, 1], ![0, 3, 0, 0, 0, 0, 0, 1], ![2, 2, 2, 2, 2, 2, 2, 1]],
    ![![0, 0, 0, 1, 0, 0, 1, 1], ![0, 0, 0, 1, 0, 1, 2, 1], ![0, 0, 0, 2, 1, 3, 1, 1], ![1, 1, 2, 1, 3, 0, 1, 1], ![0, 0, 2, 4, 0, 0, 1, 1], ![0, 2, 5, 1, 0, 0, 1, 1], ![2, 4, 1, 2, 1, 1, 1, 1], ![3, 3, 3, 3, 3, 3, 2, 1]],
    ![![0, 0, 0, 0, 0, 1, 0, 1], ![0, 0, 0, 1, 1, 2, 2, 1], ![0, 0, 0, 2, 0, 2, 0, 1], ![0, 1, 2, 0, 4, 1, 0, 1], ![0, 2, 0, 5, 0, 1, 0, 1], ![2, 3, 4, 1, 1, 1, 1, 1], ![0, 5, 0, 0, 0, 1, 0, 1], ![3, 4, 3, 3, 3, 2, 2, 1]],
    ![![0, 0, 1, 0, 1, 0, 0, 1], ![0, 0, 1, 2, 1, 1, 2, 1], ![1, 1, 1, 1, 2, 2, 0, 1], ![0, 2, 1, 0, 3, 0, 0, 1], ![2, 2, 3, 4, 1, 1, 1, 1], ![0, 1, 4, 0, 1, 0, 0, 1], ![0, 5, 1, 0, 1, 0, 0, 1], ![3, 4, 4, 3, 2, 2, 2, 1]],
    ![![0, 0, 0, 2, 0, 0, 0, 1], ![0, 0, 2, 2, 0, 1, 2, 1], ![0, 2, 0, 3, 0, 3, 0, 1], ![2, 2, 3, 2, 2, 1, 1, 1], ![0, 0, 0, 3, 0, 0, 0, 1], ![0, 1, 5, 2, 0, 0, 0, 1], ![0, 5, 0, 2, 0, 0, 0, 1], ![3, 4, 4, 3, 2, 2, 2, 1]],
    ![![0, 1, 2, 0, 0, 0, 0, 1], ![1, 1, 3, 2, 1, 1, 2, 1], ![2, 3, 2, 2, 2, 2, 1, 1], ![0, 2, 2, 0, 3, 0, 0, 1], ![0, 1, 2, 4, 0, 0, 0, 1], ![0, 1, 3, 0, 0, 0, 0, 1], ![0, 4, 2, 0, 0, 0, 0, 1], ![3, 4, 3, 3, 3, 2, 2, 1]],
    ![![0, 2, 0, 0, 0, 0, 0, 1], ![2, 2, 2, 3, 2, 2, 2, 1], ![0, 2, 0, 1, 0, 3, 0, 1], ![0, 3, 1, 0, 3, 0, 0, 1], ![0, 2, 0, 4, 0, 0, 0, 1], ![0, 2, 4, 0, 0, 0, 0, 1], ![0, 3, 0, 0, 0, 0, 0, 1], ![3, 3, 3, 3, 3, 3, 2, 1]],
    ![![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 2, 1, 2, 2, 1], ![1, 1, 1, 2, 1, 2, 1, 1], ![1, 2, 2, 1, 2, 1, 1, 1], ![1, 1, 1, 3, 1, 1, 1, 1], ![1, 2, 3, 1, 1, 1, 1, 1], ![1, 3, 1, 1, 1, 1, 1, 1], ![2, 2, 2, 2, 2, 2, 2, 1]]]

lemma g2_eq : ∀ p q r : Fin 8, p ≤ q → q ≤ r →
    g2 p q r = ∑ d : Fin 8, if r ≤ d ∧ okc p q r d then g1 q r d else 0 := by
  decide +kernel

lemma Gv2 : ∀ p q r : Fin 8, p ≤ q → q ≤ r → Gv 2 p q r = g2 p q r := by
  intro p q r hpq hqr
  rw [Gv_succ, g2_eq p q r hpq hqr]
  refine sum_congr rfl (fun d _ => ?_)
  split_ifs with hc
  · rw [Gv1 q r d hqr hc.1]
  · rfl

/-- Gv 3 as a table. -/
def g3 : Fin 8 → Fin 8 → Fin 8 → ℕ :=
  ![![![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 2, 4, 0, 1, 2, 1], ![0, 1, 0, 1, 0, 2, 0, 1], ![0, 3, 4, 0, 2, 0, 0, 1], ![0, 1, 0, 5, 0, 0, 0, 1], ![0, 4, 5, 0, 0, 0, 0, 1], ![0, 5, 0, 0, 0, 0, 0, 1], ![2, 2, 2, 2, 2, 2, 2, 1]],
    ![![0, 0, 1, 2, 0, 0, 1, 1], ![0, 0, 2, 4, 0, 1, 2, 1], ![0, 1, 2, 5, 1, 3, 1, 1], ![1, 4, 6, 3, 3, 0, 1, 1], ![0, 3, 6, 6, 0, 0, 1, 1], ![1, 7, 8, 3, 0, 0, 1, 1], ![3, 7, 2, 4, 1, 1, 1, 1], ![3, 3, 4, 4, 3, 3, 2, 1]],
    ![![0, 1, 0, 0, 0, 1, 0, 1], ![1, 1, 3, 4, 1, 2, 2, 1], ![0, 2, 0, 5, 0, 2, 0, 1], ![1, 5, 6, 0, 4, 1, 0, 1], ![0, 7, 0, 7, 0, 1, 0, 1], ![3, 10, 7, 1, 1, 1, 1, 1], ![0, 10, 0, 0, 0, 1, 0, 1], ![3, 5, 3, 3, 3, 2, 2, 1]],
    ![![0, 1, 3, 0, 1, 0, 0, 1], ![1, 1, 6, 5, 1, 1, 2, 1], ![1, 4, 4, 1, 2, 2, 0, 1], ![0, 5, 4, 0, 3, 0, 0, 1], ![3, 4, 7, 6, 1, 1, 1, 1], ![0, 7, 7, 0, 1, 0, 0, 1], ![0, 10, 4, 0, 1, 0, 0, 1], ![3, 5, 6, 3, 2, 2, 2, 1]],
    ![![0, 1, 0, 3, 0, 0, 0, 1], ![0, 1, 7, 5, 0, 1, 2, 1], ![0, 6, 0, 6, 0, 3, 0, 1], ![2, 5, 7, 4, 2, 1, 1, 1], ![0, 1, 0, 5, 0, 0, 0, 1], ![0, 5, 8, 4, 0, 0, 0, 1], ![0, 9, 0, 4, 0, 0, 0, 1], ![3, 5, 4, 4, 2, 2, 2, 1]],
    ![![0, 3, 3, 0, 0, 0, 0, 1], ![1, 3, 7, 5, 1, 1, 2, 1], ![2, 6, 3, 2, 2, 2, 1, 1], ![0, 6, 5, 0, 3, 0, 0, 1], ![0, 3, 4, 6, 0, 0, 0, 1], ![0, 4, 5, 0, 0, 0, 0, 1], ![0, 7, 4, 0, 0, 0, 0, 1], ![3, 6, 4, 3, 3, 2, 2, 1]],
    ![![0, 3, 0, 0, 0, 0, 0, 1], ![2, 3, 4, 6, 2, 2, 2, 1], ![0, 4, 0, 1, 0, 3, 0, 1], ![0, 6, 4, 0, 3, 0, 0, 1], ![0, 4, 0, 6, 0, 0, 0, 1], ![0, 5, 6, 0, 0, 0, 0, 1], ![0, 5, 0, 0, 0, 0, 0, 1], ![3, 4, 3, 3, 3, 3, 2, 1]],
    ![![1, 1, 1, 1, 1, 1, 1, 1], ![1, 1, 3, 5, 1, 2, 2, 1], ![1, 2, 1, 2, 1, 2, 1, 1], ![1, 4, 5, 1, 2, 1, 1, 1], ![1, 2, 1, 5, 1, 1, 1, 1], ![1, 5, 5, 1, 1, 1, 1, 1], ![1, 5, 1, 1, 1, 1, 1, 1], ![2, 2, 2, 2, 2, 2, 2, 1]]]

lemma g3_eq : ∀ p q r : Fin 8, p ≤ q → q ≤ r →
    g3 p q r = ∑ d : Fin 8, if r ≤ d ∧ okc p q r d then g2 q r d else 0 := by
  decide +kernel

lemma Gv3 : ∀ p q r : Fin 8, p ≤ q → q ≤ r → Gv 3 p q r = g3 p q r := by
  intro p q r hpq hqr
  rw [Gv_succ, g3_eq p q r hpq hqr]
  refine sum_congr rfl (fun d _ => ?_)
  split_ifs with hc
  · rw [Gv2 q r d hqr hc.1]
  · rfl

/-- Gv 4 as a table. -/
def g4 : Fin 8 → Fin 8 → Fin 8 → ℕ :=
  ![![![0, 0, 0, 0, 0, 0, 0, 1], ![0, 2, 7, 6, 0, 1, 2, 1], ![0, 8, 0, 1, 0, 2, 0, 1], ![0, 7, 7, 0, 2, 0, 0, 1], ![0, 2, 0, 7, 0, 0, 0, 1], ![0, 6, 6, 0, 0, 0, 0, 1], ![0, 6, 0, 0, 0, 0, 0, 1], ![2, 2, 2, 2, 2, 2, 2, 1]],
    ![![0, 2, 1, 2, 0, 0, 1, 1], ![1, 2, 7, 6, 0, 1, 2, 1], ![1, 8, 5, 5, 1, 3, 1, 1], ![2, 13, 9, 3, 3, 0, 1, 1], ![1, 9, 9, 8, 0, 0, 1, 1], ![3, 13, 9, 3, 0, 0, 1, 1], ![4, 10, 2, 4, 1, 1, 1, 1], ![3, 5, 4, 4, 3, 3, 2, 1]],
    ![![0, 6, 0, 0, 0, 1, 0, 1], ![3, 6, 8, 6, 1, 2, 2, 1], ![0, 9, 0, 5, 0, 2, 0, 1], ![3, 14, 9, 0, 4, 1, 0, 1], ![0, 16, 0, 9, 0, 1, 0, 1], ![4, 19, 8, 1, 1, 1, 1, 1], ![0, 16, 0, 0, 0, 1, 0, 1], ![3, 10, 3, 3, 3, 2, 2, 1]],
    ![![0, 4, 3, 0, 1, 0, 0, 1], ![2, 6, 11, 7, 1, 1, 2, 1], ![1, 11, 7, 1, 2, 2, 0, 1], ![0, 9, 7, 0, 3, 0, 0, 1], ![4, 8, 10, 8, 1, 1, 1, 1], ![0, 12, 8, 0, 1, 0, 0, 1], ![0, 14, 4, 0, 1, 0, 0, 1], ![3, 8, 6, 3, 2, 2, 2, 1]],
    ![![0, 1, 0, 3, 0, 0, 0, 1], ![0, 3, 12, 7, 0, 1, 2, 1], ![0, 13, 0, 6, 0, 3, 0, 1], ![2, 9, 10, 4, 2, 1, 1, 1], ![0, 2, 0, 7, 0, 0, 0, 1], ![0, 7, 9, 4, 0, 0, 0, 1], ![0, 10, 0, 4, 0, 0, 0, 1], ![3, 5, 4, 4, 2, 2, 2, 1]],
    ![![0, 3, 3, 0, 0, 0, 0, 1], ![1, 5, 12, 7, 1, 1, 2, 1], ![2, 13, 3, 2, 2, 2, 1, 1], ![0, 10, 8, 0, 3, 0, 0, 1], ![0, 4, 4, 8, 0, 0, 0, 1], ![0, 6, 6, 0, 0, 0, 0, 1], ![0, 8, 4, 0, 0, 0, 0, 1], ![3, 6, 4, 3, 3, 2, 2, 1]],
    ![![0, 3, 0, 0, 0, 0, 0, 1], ![2, 5, 9, 8, 2, 2, 2, 1], ![0, 11, 0, 1, 0, 3, 0, 1], ![0, 10, 7, 0, 3, 0, 0, 1], ![0, 5, 0, 8, 0, 0, 0, 1], ![0, 7, 7, 0, 0, 0, 0, 1], ![0, 6, 0, 0, 0, 0, 0, 1], ![3, 4, 3, 3, 3, 3, 2, 1]],
    ![![1, 1, 1, 1, 1, 1, 1, 1], ![1, 3, 8, 7, 1, 2, 2, 1], ![1, 9, 1, 2, 1, 2, 1, 1], ![1, 8, 8, 1, 2, 1, 1, 1], ![1, 3, 1, 7, 1, 1, 1, 1], ![1, 7, 6, 1, 1, 1, 1, 1], ![1, 6, 1, 1, 1, 1, 1, 1], ![2, 2, 2, 2, 2, 2, 2, 1]]]

lemma g4_eq : ∀ p q r : Fin 8, p ≤ q → q ≤ r →
    g4 p q r = ∑ d : Fin 8, if r ≤ d ∧ okc p q r d then g3 q r d else 0 := by
  decide +kernel

lemma Gv4 : ∀ p q r : Fin 8, p ≤ q → q ≤ r → Gv 4 p q r = g4 p q r := by
  intro p q r hpq hqr
  rw [Gv_succ, g4_eq p q r hpq hqr]
  refine sum_congr rfl (fun d _ => ?_)
  split_ifs with hc
  · rw [Gv3 q r d hqr hc.1]
  · rfl

/-- Gv 5 as a table. -/
def g5 : Fin 8 → Fin 8 → Fin 8 → ℕ :=
  ![![![0, 2, 0, 0, 0, 0, 0, 1], ![2, 9, 10, 6, 0, 1, 2, 1], ![0, 20, 0, 1, 0, 2, 0, 1], ![0, 14, 10, 0, 2, 0, 0, 1], ![0, 4, 0, 7, 0, 0, 0, 1], ![0, 8, 6, 0, 0, 0, 0, 1], ![0, 8, 0, 0, 0, 0, 0, 1], ![2, 4, 2, 2, 2, 2, 2, 1]],
    ![![0, 9, 1, 2, 0, 0, 1, 1], ![3, 9, 10, 6, 0, 1, 2, 1], ![6, 20, 5, 5, 1, 3, 1, 1], ![5, 25, 12, 3, 3, 0, 1, 1], ![1, 16, 9, 8, 0, 0, 1, 1], ![3, 20, 9, 3, 0, 0, 1, 1], ![4, 17, 2, 4, 1, 1, 1, 1], ![3, 12, 4, 4, 3, 3, 2, 1]],
    ![![0, 15, 0, 0, 0, 1, 0, 1], ![5, 15, 11, 6, 1, 2, 2, 1], ![0, 21, 0, 5, 0, 2, 0, 1], ![3, 26, 12, 0, 4, 1, 0, 1], ![0, 25, 0, 9, 0, 1, 0, 1], ![4, 28, 8, 1, 1, 1, 1, 1], ![0, 25, 0, 0, 0, 1, 0, 1], ![3, 19, 3, 3, 3, 2, 2, 1]],
    ![![0, 8, 3, 0, 1, 0, 0, 1], ![4, 15, 14, 7, 1, 1, 2, 1], ![1, 23, 7, 1, 2, 2, 0, 1], ![0, 16, 10, 0, 3, 0, 0, 1], ![4, 12, 10, 8, 1, 1, 1, 1], ![0, 16, 8, 0, 1, 0, 0, 1], ![0, 18, 4, 0, 1, 0, 0, 1], ![3, 12, 6, 3, 2, 2, 2, 1]],
    ![![0, 3, 0, 3, 0, 0, 0, 1], ![2, 10, 15, 7, 0, 1, 2, 1], ![0, 25, 0, 6, 0, 3, 0, 1], ![2, 16, 13, 4, 2, 1, 1, 1], ![0, 4, 0, 7, 0, 0, 0, 1], ![0, 9, 9, 4, 0, 0, 0, 1], ![0, 12, 0, 4, 0, 0, 0, 1], ![3, 7, 4, 4, 2, 2, 2, 1]],
    ![![0, 5, 3, 0, 0, 0, 0, 1], ![3, 12, 15, 7, 1, 1, 2, 1], ![2, 25, 3, 2, 2, 2, 1, 1], ![0, 17, 11, 0, 3, 0, 0, 1], ![0, 6, 4, 8, 0, 0, 0, 1], ![0, 8, 6, 0, 0, 0, 0, 1], ![0, 10, 4, 0, 0, 0, 0, 1], ![3, 8, 4, 3, 3, 2, 2, 1]],
    ![![0, 5, 0, 0, 0, 0, 0, 1], ![4, 12, 12, 8, 2, 2, 2, 1], ![0, 23, 0, 1, 0, 3, 0, 1], ![0, 17, 10, 0, 3, 0, 0, 1], ![0, 7, 0, 8, 0, 0, 0, 1], ![0, 9, 7, 0, 0, 0, 0, 1], ![0, 8, 0, 0, 0, 0, 0, 1], ![3, 6, 3, 3, 3, 3, 2, 1]],
    ![![1, 3, 1, 1, 1, 1, 1, 1], ![3, 10, 11, 7, 1, 2, 2, 1], ![1, 21, 1, 2, 1, 2, 1, 1], ![1, 15, 11, 1, 2, 1, 1, 1], ![1, 5, 1, 7, 1, 1, 1, 1], ![1, 9, 6, 1, 1, 1, 1, 1], ![1, 8, 1, 1, 1, 1, 1, 1], ![2, 4, 2, 2, 2, 2, 2, 1]]]

lemma g5_eq : ∀ p q r : Fin 8, p ≤ q → q ≤ r →
    g5 p q r = ∑ d : Fin 8, if r ≤ d ∧ okc p q r d then g4 q r d else 0 := by
  decide +kernel

lemma Gv5 : ∀ p q r : Fin 8, p ≤ q → q ≤ r → Gv 5 p q r = g5 p q r := by
  intro p q r hpq hqr
  rw [Gv_succ, g5_eq p q r hpq hqr]
  refine sum_congr rfl (fun d _ => ?_)
  split_ifs with hc
  · rw [Gv4 q r d hqr hc.1]
  · rfl

/-- Gv 6 as a table. -/
def g6 : Fin 8 → Fin 8 → Fin 8 → ℕ :=
  ![![![0, 9, 0, 0, 0, 0, 0, 1], ![9, 19, 10, 6, 0, 1, 2, 1], ![0, 32, 0, 1, 0, 2, 0, 1], ![0, 23, 10, 0, 2, 0, 0, 1], ![0, 11, 0, 7, 0, 0, 0, 1], ![0, 15, 6, 0, 0, 0, 0, 1], ![0, 15, 0, 0, 0, 0, 0, 1], ![2, 11, 2, 2, 2, 2, 2, 1]],
    ![![2, 19, 1, 2, 0, 0, 1, 1], ![10, 19, 10, 6, 0, 1, 2, 1], ![15, 32, 5, 5, 1, 3, 1, 1], ![9, 37, 12, 3, 3, 0, 1, 1], ![3, 26, 9, 8, 0, 0, 1, 1], ![5, 30, 9, 3, 0, 0, 1, 1], ![6, 27, 2, 4, 1, 1, 1, 1], ![5, 22, 4, 4, 3, 3, 2, 1]],
    ![![0, 25, 0, 0, 0, 1, 0, 1], ![12, 25, 11, 6, 1, 2, 2, 1], ![0, 33, 0, 5, 0, 2, 0, 1], ![3, 38, 12, 0, 4, 1, 0, 1], ![0, 35, 0, 9, 0, 1, 0, 1], ![4, 38, 8, 1, 1, 1, 1, 1], ![0, 35, 0, 0, 0, 1, 0, 1], ![3, 29, 3, 3, 3, 2, 2, 1]],
    ![![0, 15, 3, 0, 1, 0, 0, 1], ![11, 25, 14, 7, 1, 1, 2, 1], ![1, 35, 7, 1, 2, 2, 0, 1], ![0, 25, 10, 0, 3, 0, 0, 1], ![4, 19, 10, 8, 1, 1, 1, 1], ![0, 23, 8, 0, 1, 0, 0, 1], ![0, 25, 4, 0, 1, 0, 0, 1], ![3, 19, 6, 3, 2, 2, 2, 1]],
    ![![0, 10, 0, 3, 0, 0, 0, 1], ![9, 20, 15, 7, 0, 1, 2, 1], ![0, 37, 0, 6, 0, 3, 0, 1], ![2, 25, 13, 4, 2, 1, 1, 1], ![0, 11, 0, 7, 0, 0, 0, 1], ![0, 16, 9, 4, 0, 0, 0, 1], ![0, 19, 0, 4, 0, 0, 0, 1], ![3, 14, 4, 4, 2, 2, 2, 1]],
    ![![0, 12, 3, 0, 0, 0, 0, 1], ![10, 22, 15, 7, 1, 1, 2, 1], ![2, 37, 3, 2, 2, 2, 1, 1], ![0, 26, 11, 0, 3, 0, 0, 1], ![0, 13, 4, 8, 0, 0, 0, 1], ![0, 15, 6, 0, 0, 0, 0, 1], ![0, 17, 4, 0, 0, 0, 0, 1], ![3, 15, 4, 3, 3, 2, 2, 1]],
    ![![0, 12, 0, 0, 0, 0, 0, 1], ![11, 22, 12, 8, 2, 2, 2, 1], ![0, 35, 0, 1, 0, 3, 0, 1], ![0, 26, 10, 0, 3, 0, 0, 1], ![0, 14, 0, 8, 0, 0, 0, 1], ![0, 16, 7, 0, 0, 0, 0, 1], ![0, 15, 0, 0, 0, 0, 0, 1], ![3, 13, 3, 3, 3, 3, 2, 1]],
    ![![1, 10, 1, 1, 1, 1, 1, 1], ![10, 20, 11, 7, 1, 2, 2, 1], ![1, 33, 1, 2, 1, 2, 1, 1], ![1, 24, 11, 1, 2, 1, 1, 1], ![1, 12, 1, 7, 1, 1, 1, 1], ![1, 16, 6, 1, 1, 1, 1, 1], ![1, 15, 1, 1, 1, 1, 1, 1], ![2, 11, 2, 2, 2, 2, 2, 1]]]

lemma g6_eq : ∀ p q r : Fin 8, p ≤ q → q ≤ r →
    g6 p q r = ∑ d : Fin 8, if r ≤ d ∧ okc p q r d then g5 q r d else 0 := by
  decide +kernel

lemma Gv6 : ∀ p q r : Fin 8, p ≤ q → q ≤ r → Gv 6 p q r = g6 p q r := by
  intro p q r hpq hqr
  rw [Gv_succ, g6_eq p q r hpq hqr]
  refine sum_congr rfl (fun d _ => ?_)
  split_ifs with hc
  · rw [Gv5 q r d hqr hc.1]
  · rfl

/-- Gv 7 as a table. -/
def g7 : Fin 8 → Fin 8 → Fin 8 → ℕ :=
  ![![![0, 19, 0, 0, 0, 0, 0, 1], ![21, 29, 10, 6, 0, 1, 2, 1], ![0, 42, 0, 1, 0, 2, 0, 1], ![0, 33, 10, 0, 2, 0, 0, 1], ![0, 21, 0, 7, 0, 0, 0, 1], ![0, 25, 6, 0, 0, 0, 0, 1], ![0, 25, 0, 0, 0, 0, 0, 1], ![2, 21, 2, 2, 2, 2, 2, 1]],
    ![![9, 29, 1, 2, 0, 0, 1, 1], ![22, 29, 10, 6, 0, 1, 2, 1], ![25, 42, 5, 5, 1, 3, 1, 1], ![16, 47, 12, 3, 3, 0, 1, 1], ![10, 36, 9, 8, 0, 0, 1, 1], ![12, 40, 9, 3, 0, 0, 1, 1], ![13, 37, 2, 4, 1, 1, 1, 1], ![12, 32, 4, 4, 3, 3, 2, 1]],
    ![![0, 35, 0, 0, 0, 1, 0, 1], ![24, 35, 11, 6, 1, 2, 2, 1], ![0, 43, 0, 5, 0, 2, 0, 1], ![3, 48, 12, 0, 4, 1, 0, 1], ![0, 45, 0, 9, 0, 1, 0, 1], ![4, 48, 8, 1, 1, 1, 1, 1], ![0, 45, 0, 0, 0, 1, 0, 1], ![3, 39, 3, 3, 3, 2, 2, 1]],
    ![![0, 25, 3, 0, 1, 0, 0, 1], ![23, 35, 14, 7, 1, 1, 2, 1], ![1, 45, 7, 1, 2, 2, 0, 1], ![0, 35, 10, 0, 3, 0, 0, 1], ![4, 29, 10, 8, 1, 1, 1, 1], ![0, 33, 8, 0, 1, 0, 0, 1], ![0, 35, 4, 0, 1, 0, 0, 1], ![3, 29, 6, 3, 2, 2, 2, 1]],
    ![![0, 20, 0, 3, 0, 0, 0, 1], ![21, 30, 15, 7, 0, 1, 2, 1], ![0, 47, 0, 6, 0, 3, 0, 1], ![2, 35, 13, 4, 2, 1, 1, 1], ![0, 21, 0, 7, 0, 0, 0, 1], ![0, 26, 9, 4, 0, 0, 0, 1], ![0, 29, 0, 4, 0, 0, 0, 1], ![3, 24, 4, 4, 2, 2, 2, 1]],
    ![![0, 22, 3, 0, 0, 0, 0, 1], ![22, 32, 15, 7, 1, 1, 2, 1], ![2, 47, 3, 2, 2, 2, 1, 1], ![0, 36, 11, 0, 3, 0, 0, 1], ![0, 23, 4, 8, 0, 0, 0, 1], ![0, 25, 6, 0, 0, 0, 0, 1], ![0, 27, 4, 0, 0, 0, 0, 1], ![3, 25, 4, 3, 3, 2, 2, 1]],
    ![![0, 22, 0, 0, 0, 0, 0, 1], ![23, 32, 12, 8, 2, 2, 2, 1], ![0, 45, 0, 1, 0, 3, 0, 1], ![0, 36, 10, 0, 3, 0, 0, 1], ![0, 24, 0, 8, 0, 0, 0, 1], ![0, 26, 7, 0, 0, 0, 0, 1], ![0, 25, 0, 0, 0, 0, 0, 1], ![3, 23, 3, 3, 3, 3, 2, 1]],
    ![![1, 20, 1, 1, 1, 1, 1, 1], ![22, 30, 11, 7, 1, 2, 2, 1], ![1, 43, 1, 2, 1, 2, 1, 1], ![1, 34, 11, 1, 2, 1, 1, 1], ![1, 22, 1, 7, 1, 1, 1, 1], ![1, 26, 6, 1, 1, 1, 1, 1], ![1, 25, 1, 1, 1, 1, 1, 1], ![2, 21, 2, 2, 2, 2, 2, 1]]]

lemma g7_eq : ∀ p q r : Fin 8, p ≤ q → q ≤ r →
    g7 p q r = ∑ d : Fin 8, if r ≤ d ∧ okc p q r d then g6 q r d else 0 := by
  decide +kernel

lemma Gv7 : ∀ p q r : Fin 8, p ≤ q → q ≤ r → Gv 7 p q r = g7 p q r := by
  intro p q r hpq hqr
  rw [Gv_succ, g7_eq p q r hpq hqr]
  refine sum_congr rfl (fun d _ => ?_)
  split_ifs with hc
  · rw [Gv6 q r d hqr hc.1]
  · rfl

/-- Gv 8 as a table. -/
def g8 : Fin 8 → Fin 8 → Fin 8 → ℕ :=
  ![![![0, 29, 0, 0, 0, 0, 0, 1], ![38, 39, 10, 6, 0, 1, 2, 1], ![0, 52, 0, 1, 0, 2, 0, 1], ![0, 43, 10, 0, 2, 0, 0, 1], ![0, 31, 0, 7, 0, 0, 0, 1], ![0, 35, 6, 0, 0, 0, 0, 1], ![0, 35, 0, 0, 0, 0, 0, 1], ![2, 31, 2, 2, 2, 2, 2, 1]],
    ![![19, 39, 1, 2, 0, 0, 1, 1], ![39, 39, 10, 6, 0, 1, 2, 1], ![35, 52, 5, 5, 1, 3, 1, 1], ![26, 57, 12, 3, 3, 0, 1, 1], ![20, 46, 9, 8, 0, 0, 1, 1], ![22, 50, 9, 3, 0, 0, 1, 1], ![23, 47, 2, 4, 1, 1, 1, 1], ![22, 42, 4, 4, 3, 3, 2, 1]],
    ![![0, 45, 0, 0, 0, 1, 0, 1], ![41, 45, 11, 6, 1, 2, 2, 1], ![0, 53, 0, 5, 0, 2, 0, 1], ![3, 58, 12, 0, 4, 1, 0, 1], ![0, 55, 0, 9, 0, 1, 0, 1], ![4, 58, 8, 1, 1, 1, 1, 1], ![0, 55, 0, 0, 0, 1, 0, 1], ![3, 49, 3, 3, 3, 2, 2, 1]],
    ![![0, 35, 3, 0, 1, 0, 0, 1], ![40, 45, 14, 7, 1, 1, 2, 1], ![1, 55, 7, 1, 2, 2, 0, 1], ![0, 45, 10, 0, 3, 0, 0, 1], ![4, 39, 10, 8, 1, 1, 1, 1], ![0, 43, 8, 0, 1, 0, 0, 1], ![0, 45, 4, 0, 1, 0, 0, 1], ![3, 39, 6, 3, 2, 2, 2, 1]],
    ![![0, 30, 0, 3, 0, 0, 0, 1], ![38, 40, 15, 7, 0, 1, 2, 1], ![0, 57, 0, 6, 0, 3, 0, 1], ![2, 45, 13, 4, 2, 1, 1, 1], ![0, 31, 0, 7, 0, 0, 0, 1], ![0, 36, 9, 4, 0, 0, 0, 1], ![0, 39, 0, 4, 0, 0, 0, 1], ![3, 34, 4, 4, 2, 2, 2, 1]],
    ![![0, 32, 3, 0, 0, 0, 0, 1], ![39, 42, 15, 7, 1, 1, 2, 1], ![2, 57, 3, 2, 2, 2, 1, 1], ![0, 46, 11, 0, 3, 0, 0, 1], ![0, 33, 4, 8, 0, 0, 0, 1], ![0, 35, 6, 0, 0, 0, 0, 1], ![0, 37, 4, 0, 0, 0, 0, 1], ![3, 35, 4, 3, 3, 2, 2, 1]],
    ![![0, 32, 0, 0, 0, 0, 0, 1], ![40, 42, 12, 8, 2, 2, 2, 1], ![0, 55, 0, 1, 0, 3, 0, 1], ![0, 46, 10, 0, 3, 0, 0, 1], ![0, 34, 0, 8, 0, 0, 0, 1], ![0, 36, 7, 0, 0, 0, 0, 1], ![0, 35, 0, 0, 0, 0, 0, 1], ![3, 33, 3, 3, 3, 3, 2, 1]],
    ![![1, 30, 1, 1, 1, 1, 1, 1], ![39, 40, 11, 7, 1, 2, 2, 1], ![1, 53, 1, 2, 1, 2, 1, 1], ![1, 44, 11, 1, 2, 1, 1, 1], ![1, 32, 1, 7, 1, 1, 1, 1], ![1, 36, 6, 1, 1, 1, 1, 1], ![1, 35, 1, 1, 1, 1, 1, 1], ![2, 31, 2, 2, 2, 2, 2, 1]]]

lemma g8_eq : ∀ p q r : Fin 8, p ≤ q → q ≤ r →
    g8 p q r = ∑ d : Fin 8, if r ≤ d ∧ okc p q r d then g7 q r d else 0 := by
  decide +kernel

lemma Gv8 : ∀ p q r : Fin 8, p ≤ q → q ≤ r → Gv 8 p q r = g8 p q r := by
  intro p q r hpq hqr
  rw [Gv_succ, g8_eq p q r hpq hqr]
  refine sum_congr rfl (fun d _ => ?_)
  split_ifs with hc
  · rw [Gv7 q r d hqr hc.1]
  · rfl

/-- Gv 9 as a table. -/
def g9 : Fin 8 → Fin 8 → Fin 8 → ℕ :=
  ![![![0, 39, 0, 0, 0, 0, 0, 1], ![58, 49, 10, 6, 0, 1, 2, 1], ![0, 62, 0, 1, 0, 2, 0, 1], ![0, 53, 10, 0, 2, 0, 0, 1], ![0, 41, 0, 7, 0, 0, 0, 1], ![0, 45, 6, 0, 0, 0, 0, 1], ![0, 45, 0, 0, 0, 0, 0, 1], ![2, 41, 2, 2, 2, 2, 2, 1]],
    ![![29, 49, 1, 2, 0, 0, 1, 1], ![59, 49, 10, 6, 0, 1, 2, 1], ![45, 62, 5, 5, 1, 3, 1, 1], ![36, 67, 12, 3, 3, 0, 1, 1], ![30, 56, 9, 8, 0, 0, 1, 1], ![32, 60, 9, 3, 0, 0, 1, 1], ![33, 57, 2, 4, 1, 1, 1, 1], ![32, 52, 4, 4, 3, 3, 2, 1]],
    ![![0, 55, 0, 0, 0, 1, 0, 1], ![61, 55, 11, 6, 1, 2, 2, 1], ![0, 63, 0, 5, 0, 2, 0, 1], ![3, 68, 12, 0, 4, 1, 0, 1], ![0, 65, 0, 9, 0, 1, 0, 1], ![4, 68, 8, 1, 1, 1, 1, 1], ![0, 65, 0, 0, 0, 1, 0, 1], ![3, 59, 3, 3, 3, 2, 2, 1]],
    ![![0, 45, 3, 0, 1, 0, 0, 1], ![60, 55, 14, 7, 1, 1, 2, 1], ![1, 65, 7, 1, 2, 2, 0, 1], ![0, 55, 10, 0, 3, 0, 0, 1], ![4, 49, 10, 8, 1, 1, 1, 1], ![0, 53, 8, 0, 1, 0, 0, 1], ![0, 55, 4, 0, 1, 0, 0, 1], ![3, 49, 6, 3, 2, 2, 2, 1]],
    ![![0, 40, 0, 3, 0, 0, 0, 1], ![58, 50, 15, 7, 0, 1, 2, 1], ![0, 67, 0, 6, 0, 3, 0, 1], ![2, 55, 13, 4, 2, 1, 1, 1], ![0, 41, 0, 7, 0, 0, 0, 1], ![0, 46, 9, 4, 0, 0, 0, 1], ![0, 49, 0, 4, 0, 0, 0, 1], ![3, 44, 4, 4, 2, 2, 2, 1]],
    ![![0, 42, 3, 0, 0, 0, 0, 1], ![59, 52, 15, 7, 1, 1, 2, 1], ![2, 67, 3, 2, 2, 2, 1, 1], ![0, 56, 11, 0, 3, 0, 0, 1], ![0, 43, 4, 8, 0, 0, 0, 1], ![0, 45, 6, 0, 0, 0, 0, 1], ![0, 47, 4, 0, 0, 0, 0, 1], ![3, 45, 4, 3, 3, 2, 2, 1]],
    ![![0, 42, 0, 0, 0, 0, 0, 1], ![60, 52, 12, 8, 2, 2, 2, 1], ![0, 65, 0, 1, 0, 3, 0, 1], ![0, 56, 10, 0, 3, 0, 0, 1], ![0, 44, 0, 8, 0, 0, 0, 1], ![0, 46, 7, 0, 0, 0, 0, 1], ![0, 45, 0, 0, 0, 0, 0, 1], ![3, 43, 3, 3, 3, 3, 2, 1]],
    ![![1, 40, 1, 1, 1, 1, 1, 1], ![59, 50, 11, 7, 1, 2, 2, 1], ![1, 63, 1, 2, 1, 2, 1, 1], ![1, 54, 11, 1, 2, 1, 1, 1], ![1, 42, 1, 7, 1, 1, 1, 1], ![1, 46, 6, 1, 1, 1, 1, 1], ![1, 45, 1, 1, 1, 1, 1, 1], ![2, 41, 2, 2, 2, 2, 2, 1]]]

lemma g9_eq : ∀ p q r : Fin 8, p ≤ q → q ≤ r →
    g9 p q r = ∑ d : Fin 8, if r ≤ d ∧ okc p q r d then g8 q r d else 0 := by
  decide +kernel

lemma Gv9 : ∀ p q r : Fin 8, p ≤ q → q ≤ r → Gv 9 p q r = g9 p q r := by
  intro p q r hpq hqr
  rw [Gv_succ, g9_eq p q r hpq hqr]
  refine sum_congr rfl (fun d _ => ?_)
  split_ifs with hc
  · rw [Gv8 q r d hqr hc.1]
  · rfl

/-- Gv 10 as a table. -/
def g10 : Fin 8 → Fin 8 → Fin 8 → ℕ :=
  ![![![0, 49, 0, 0, 0, 0, 0, 1], ![78, 59, 10, 6, 0, 1, 2, 1], ![0, 72, 0, 1, 0, 2, 0, 1], ![0, 63, 10, 0, 2, 0, 0, 1], ![0, 51, 0, 7, 0, 0, 0, 1], ![0, 55, 6, 0, 0, 0, 0, 1], ![0, 55, 0, 0, 0, 0, 0, 1], ![2, 51, 2, 2, 2, 2, 2, 1]],
    ![![39, 59, 1, 2, 0, 0, 1, 1], ![79, 59, 10, 6, 0, 1, 2, 1], ![55, 72, 5, 5, 1, 3, 1, 1], ![46, 77, 12, 3, 3, 0, 1, 1], ![40, 66, 9, 8, 0, 0, 1, 1], ![42, 70, 9, 3, 0, 0, 1, 1], ![43, 67, 2, 4, 1, 1, 1, 1], ![42, 62, 4, 4, 3, 3, 2, 1]],
    ![![0, 65, 0, 0, 0, 1, 0, 1], ![81, 65, 11, 6, 1, 2, 2, 1], ![0, 73, 0, 5, 0, 2, 0, 1], ![3, 78, 12, 0, 4, 1, 0, 1], ![0, 75, 0, 9, 0, 1, 0, 1], ![4, 78, 8, 1, 1, 1, 1, 1], ![0, 75, 0, 0, 0, 1, 0, 1], ![3, 69, 3, 3, 3, 2, 2, 1]],
    ![![0, 55, 3, 0, 1, 0, 0, 1], ![80, 65, 14, 7, 1, 1, 2, 1], ![1, 75, 7, 1, 2, 2, 0, 1], ![0, 65, 10, 0, 3, 0, 0, 1], ![4, 59, 10, 8, 1, 1, 1, 1], ![0, 63, 8, 0, 1, 0, 0, 1], ![0, 65, 4, 0, 1, 0, 0, 1], ![3, 59, 6, 3, 2, 2, 2, 1]],
    ![![0, 50, 0, 3, 0, 0, 0, 1], ![78, 60, 15, 7, 0, 1, 2, 1], ![0, 77, 0, 6, 0, 3, 0, 1], ![2, 65, 13, 4, 2, 1, 1, 1], ![0, 51, 0, 7, 0, 0, 0, 1], ![0, 56, 9, 4, 0, 0, 0, 1], ![0, 59, 0, 4, 0, 0, 0, 1], ![3, 54, 4, 4, 2, 2, 2, 1]],
    ![![0, 52, 3, 0, 0, 0, 0, 1], ![79, 62, 15, 7, 1, 1, 2, 1], ![2, 77, 3, 2, 2, 2, 1, 1], ![0, 66, 11, 0, 3, 0, 0, 1], ![0, 53, 4, 8, 0, 0, 0, 1], ![0, 55, 6, 0, 0, 0, 0, 1], ![0, 57, 4, 0, 0, 0, 0, 1], ![3, 55, 4, 3, 3, 2, 2, 1]],
    ![![0, 52, 0, 0, 0, 0, 0, 1], ![80, 62, 12, 8, 2, 2, 2, 1], ![0, 75, 0, 1, 0, 3, 0, 1], ![0, 66, 10, 0, 3, 0, 0, 1], ![0, 54, 0, 8, 0, 0, 0, 1], ![0, 56, 7, 0, 0, 0, 0, 1], ![0, 55, 0, 0, 0, 0, 0, 1], ![3, 53, 3, 3, 3, 3, 2, 1]],
    ![![1, 50, 1, 1, 1, 1, 1, 1], ![79, 60, 11, 7, 1, 2, 2, 1], ![1, 73, 1, 2, 1, 2, 1, 1], ![1, 64, 11, 1, 2, 1, 1, 1], ![1, 52, 1, 7, 1, 1, 1, 1], ![1, 56, 6, 1, 1, 1, 1, 1], ![1, 55, 1, 1, 1, 1, 1, 1], ![2, 51, 2, 2, 2, 2, 2, 1]]]

lemma g10_eq : ∀ p q r : Fin 8, p ≤ q → q ≤ r →
    g10 p q r = ∑ d : Fin 8, if r ≤ d ∧ okc p q r d then g9 q r d else 0 := by
  decide +kernel

lemma Gv10 : ∀ p q r : Fin 8, p ≤ q → q ≤ r → Gv 10 p q r = g10 p q r := by
  intro p q r hpq hqr
  rw [Gv_succ, g10_eq p q r hpq hqr]
  refine sum_congr rfl (fun d _ => ?_)
  split_ifs with hc
  · rw [Gv9 q r d hqr hc.1]
  · rfl

/-- The weights of the starts: the arrangements of length 3. -/
def w (p q r : Fin 8) : ℤ :=
  if p ≤ q ∧ q ≤ r ∧ ((r : ℕ) = p ∨ (r : ℕ) = q ∨ (r : ℕ) = p + q) then 1 else 0

lemma a_S (m : ℕ) : (a (m + 1) : ℤ) = ∑ p : Fin 8, ∑ q : Fin 8, ∑ r : Fin 8, w p q r * (Gv m p q r : ℤ) :=
  a_dual m

lemma w_congr (f g : Fin 8 → Fin 8 → Fin 8 → ℕ) (h : ∀ p q r : Fin 8, p ≤ q → q ≤ r → f p q r = g p q r) :
    ∑ p : Fin 8, ∑ q : Fin 8, ∑ r : Fin 8, w p q r * (f p q r : ℤ) =
      ∑ p : Fin 8, ∑ q : Fin 8, ∑ r : Fin 8, w p q r * (g p q r : ℤ) := by
  refine sum_congr rfl (fun p _ => sum_congr rfl (fun q _ => sum_congr rfl (fun r _ => ?_)))
  unfold w
  split_ifs with hc
  · rw [h p q r hc.1 hc.2.1]
  · simp

lemma a1 : (a 1 : ℤ) = 11 := by
  rw [a_S, w_congr _ _ Gv0]
  decide +kernel

lemma a2 : (a 2 : ℤ) = 17 := by
  rw [a_S, w_congr _ _ Gv1]
  decide +kernel

lemma a3 : (a 3 : ℤ) = 22 := by
  rw [a_S, w_congr _ _ Gv2]
  decide +kernel

lemma a4 : (a 4 : ℤ) = 31 := by
  rw [a_S, w_congr _ _ Gv3]
  decide +kernel

lemma a5 : (a 5 : ℤ) = 43 := by
  rw [a_S, w_congr _ _ Gv4]
  decide +kernel

lemma a6 : (a 6 : ℤ) = 60 := by
  rw [a_S, w_congr _ _ Gv5]
  decide +kernel

lemma a7 : (a 7 : ℤ) = 80 := by
  rw [a_S, w_congr _ _ Gv6]
  decide +kernel

lemma a8 : (a 8 : ℤ) = 100 := by
  rw [a_S, w_congr _ _ Gv7]
  decide +kernel

lemma a9 : (a 9 : ℤ) = 120 := by
  rw [a_S, w_congr _ _ Gv8]
  decide +kernel

lemma a10 : (a 10 : ℤ) = 140 := by
  rw [a_S, w_congr _ _ Gv9]
  decide +kernel

/-- The second difference of the continuation counts. -/
def R (m : ℕ) (p q r : Fin 8) : ℤ := (Gv (m + 2) p q r : ℤ) - 2 * (Gv (m + 1) p q r : ℤ) + (Gv m p q r : ℤ)

lemma R_succ (m : ℕ) (p q r : Fin 8) :
    R (m + 1) p q r = ∑ d : Fin 8, if r ≤ d ∧ okc p q r d then R m q r d else 0 := by
  unfold R
  rw [show m + 1 + 1 = m + 1 + 1 by ring, show m + 1 + 2 = m + 2 + 1 by ring]
  rw [Gv_succ (m + 2), Gv_succ (m + 1), Gv_succ m]
  push_cast
  simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl (fun d _ => ?_)
  split_ifs <;> ring

lemma vec_id : ∀ p q r : Fin 8, p ≤ q → q ≤ r → (g10 p q r : ℤ) - 2 * (g9 p q r : ℤ) + (g8 p q r : ℤ) = 0 := by
  decide +kernel

lemma R_zero (m : ℕ) (hm : 8 ≤ m) : ∀ p q r : Fin 8, p ≤ q → q ≤ r → R m p q r = 0 := by
  induction m, hm using Nat.le_induction with
  | base =>
    intro p q r hpq hqr
    unfold R
    rw [Gv10 p q r hpq hqr, Gv9 p q r hpq hqr, Gv8 p q r hpq hqr]
    exact vec_id p q r hpq hqr
  | succ m hm ih =>
    intro p q r hpq hqr
    rw [R_succ]
    refine sum_eq_zero (fun d _ => ?_)
    split_ifs with hc
    · exact ih q r d hqr hc.1
    · rfl

lemma rec_a (n : ℕ) (hn : 6 ≤ n) : (a (n + 2) : ℤ) - 2 * (a (n + 1) : ℤ) + (a n : ℤ) = 0 := by
  rcases Nat.lt_or_ge n 9 with h | h
  · interval_cases n
    · rw [a8, a7, a6]
      norm_num
    · rw [a9, a8, a7]
      norm_num
    · rw [a10, a9, a8]
      norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [show m + 1 + 1 = m + 1 + 1 by ring, show m + 1 + 2 = m + 2 + 1 by ring]
    simp only [a_S]
    have hR := R_zero m (by omega)
    unfold R at hR
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_eq_zero (fun p _ => sum_eq_zero (fun q _ => sum_eq_zero (fun r _ => ?_)))
    by_cases hc : p ≤ q ∧ q ≤ r
    · linear_combination (w p q r) * hR p q r hc.1 hc.2
    · have hw : w p q r = 0 := by
        unfold w
        rw [if_neg (fun h => hc ⟨h.1, h.2.1⟩)]
      rw [hw]
      ring

/-- Barker's g.f. -/
theorem gf :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 2 =
      X * (11 - 5 * X - X ^ 2 + 4 * X ^ 3 + 3 * X ^ 4 + 5 * X ^ 5 + 3 * X ^ 6) := by
  have v1 : (a 1 : ℚ) = 11 := by exact_mod_cast a1
  have v2 : (a 2 : ℚ) = 17 := by exact_mod_cast a2
  have v3 : (a 3 : ℚ) = 22 := by exact_mod_cast a3
  have v4 : (a 4 : ℚ) = 31 := by exact_mod_cast a4
  have v5 : (a 5 : ℚ) = 43 := by exact_mod_cast a5
  have v6 : (a 6 : ℚ) = 60 := by exact_mod_cast a6
  have v7 : (a 7 : ℚ) = 80 := by exact_mod_cast a7
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 2 = A - C (2 : ℚ) * (A * X ^ 1) + A * X ^ 2 := by
    simp only [map_ofNat]
    ring
  have e2 : (X * (11 - 5 * X - X ^ 2 + 4 * X ^ 3 + 3 * X ^ 4 + 5 * X ^ 5 + 3 * X ^ 6) : ℚ⟦X⟧) = X ^ 1 * C (11 : ℚ) - X ^ 2 * C (5 : ℚ) - X ^ 3 + X ^ 4 * C (4 : ℚ) + X ^ 5 * C (3 : ℚ) + X ^ 6 * C (5 : ℚ) + X ^ 7 * C (3 : ℚ) := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk,
    coeff_C_mul]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | m
  · simp
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, if_true,
      if_false, v1]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, if_true,
      if_false, v1, v2]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, if_true,
      if_false, v1, v2, v3]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, if_true,
      if_false, v2, v3, v4]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, if_true,
      if_false, v3, v4, v5]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, if_true,
      if_false, v4, v5, v6]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, if_true,
      if_false, v5, v6, v7]
    all_goals norm_num
  · simp only [show ¬ (m + 8 = 0) by omega,
      show 1 ≤ m + 8 by omega,
      show m + 8 - 1 = m + 7 by omega,
      show ¬ (m + 7 = 0) by omega,
      show 2 ≤ m + 8 by omega,
      show m + 8 - 2 = m + 6 by omega,
      show ¬ (m + 6 = 0) by omega,
      show ¬ (m + 8 = 1) by omega,
      show ¬ (m + 8 = 2) by omega,
      show ¬ (m + 8 = 3) by omega,
      show ¬ (m + 8 = 4) by omega,
      show ¬ (m + 8 = 5) by omega,
      show ¬ (m + 8 = 6) by omega,
      show ¬ (m + 8 = 7) by omega, if_true, if_false]
    have h := rec_a (m + 6) (by omega)
    rw [show m + 6 + 1 = m + 7 by ring, show m + 6 + 2 = m + 8 by ring] at h
    have hq : (a (m + 8) : ℚ) - 2 * (a (m + 7) : ℚ) + (a (m + 6) : ℚ) = 0 := by exact_mod_cast h
    linear_combination hq

/-- Barker's recurrence. -/
theorem recur : ∀ n : ℕ, 7 < n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  rw [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega]
  have h := rec_a (m + 6) (by omega)
  rw [show m + 6 + 1 = m + 7 by ring, show m + 6 + 2 = m + 8 by ring] at h
  linear_combination h

/-- Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 2 =
      X * (11 - 5 * X - X ^ 2 + 4 * X ^ 3 + 3 * X ^ 4 + 5 * X ^ 5 + 3 * X ^ 6) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a190039

theorem OMA.solution : type_of% @OMA.S_oeis_a190039.main :=
  OMA.S_oeis_a190039.conjecture
