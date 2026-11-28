import OMAStatements.S_oeis_a190038

/-!
OEIS A190038 (R. H. Hardin, May 04 2011): Number of nondecreasing arrangements of n+2 numbers in 0..6 with the last equal to 6 and each after the second equal to the sum of one or two of the preceding three.
Conjectures from Colin Barker, May 04 2018: G.f.: x*(10 - 12*x + 6*x^2 + x^3 + 3*x^4 + 2*x^5 - x^6 - x^7) / (1 - x)^3. a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>8.

Proof. Prefixes are counted by their last three entries: pref(m, p, q, r) counts the prefixes of
length m + 3 that are nondecreasing and satisfy the condition at every entry after the second,
ending with p, q, r; appending an entry d (Fin.snoc) gives pref(m + 1, q, r, d) = sum over p of [r
<= d and d is one of p, q, r or the sum of two of them] pref(m, p, q, r) (`pg_snoc`, `pref_succ`).
The continuation counts Gv satisfy the transposed recursion, so a(m + 1) = sum over the starts s of
pref(0, s) Gv(m, s) (`a_dual`). Tables of Gv for m <= 11, checked level by level on the
nondecreasing states (`g1_eq`, ...), give the small values and the vanishing of the third difference
of Gv at m = 8 (`vec_id`), which propagates to every later m by linearity (`R_zero`). Hence the
third difference of a vanishes from n = 6 on (`rec_a`), and the g.f. and the recurrence follow by
comparing coefficients.
-/

namespace OMA.S_oeis_a190038

open PowerSeries Finset


/-- The entry d may follow the entries p, q, r. -/
def okc (p q r d : ℕ) : Prop := d = p ∨ d = q ∨ d = r ∨ d = p + q ∨ d = p + r ∨ d = q + r

instance (p q r d : ℕ) : Decidable (okc p q r d) := by unfold okc; infer_instance

/-- The conditions on a prefix: nondecreasing, and every entry after the second is the sum of one or
two of the preceding three. -/
def pg {L : ℕ} (y : Fin L → Fin 7) : Prop := Monotone y ∧ ∀ i : Fin L, 2 ≤ (i : ℕ) → okAt y i

instance {L : ℕ} : DecidablePred (@pg L) := fun y => by unfold pg okAt Monotone; infer_instance

lemma snoc_lt {m : ℕ} (y : Fin (m + 3) → Fin 7) (d : Fin 7) (j : ℕ) (hj : j < m + 4) (h : j < m + 3) :
    (Fin.snoc y d : Fin (m + 4) → Fin 7) ⟨j, hj⟩ = y ⟨j, h⟩ := by
  simp [Fin.snoc, h]

lemma mono_snoc {m : ℕ} (y : Fin (m + 3) → Fin 7) (d : Fin 7) :
    Monotone (Fin.snoc y d : Fin (m + 4) → Fin 7) ↔ Monotone y ∧ y (Fin.last (m + 2)) ≤ d := by
  rw [Fin.monotone_iff_le_succ, Fin.monotone_iff_le_succ, Fin.forall_fin_succ']
  simp only [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, Fin.succ_castSucc]

lemma ok_snoc_cs {m : ℕ} (y : Fin (m + 3) → Fin 7) (d : Fin 7) (i : Fin (m + 3)) :
    okAt (Fin.snoc y d : Fin (m + 4) → Fin 7) i.castSucc ↔ okAt y i := by
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

lemma ok_snoc_last {m : ℕ} (y : Fin (m + 3) → Fin 7) (d : Fin 7) :
    okAt (Fin.snoc y d : Fin (m + 4) → Fin 7) (Fin.last (m + 3)) ↔
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

lemma pg_snoc {m : ℕ} (y : Fin (m + 3) → Fin 7) (d : Fin 7) :
    pg (Fin.snoc y d : Fin (m + 4) → Fin 7) ↔
      pg y ∧ y (Fin.last (m + 2)) ≤ d ∧
        okc (y ⟨m, by omega⟩) (y ⟨m + 1, by omega⟩) (y ⟨m + 2, by omega⟩) d := by
  unfold pg
  rw [mono_snoc, Fin.forall_fin_succ']
  simp only [Fin.val_castSucc, ok_snoc_cs, Fin.val_last, ok_snoc_last, show 2 ≤ m + 3 by omega,
    true_implies]
  tauto

/-- The prefixes of length m + 3 ending with p, q, r. -/
def pref (m : ℕ) (p q r : Fin 7) : ℕ :=
  ((univ : Finset (Fin (m + 3) → Fin 7)).filter (fun y => pg y ∧
    y ⟨m, by omega⟩ = p ∧ y ⟨m + 1, by omega⟩ = q ∧ y ⟨m + 2, by omega⟩ = r)).card

lemma pref_succ (m : ℕ) (q r d : Fin 7) :
    pref (m + 1) q r d = ∑ p : Fin 7, if r ≤ d ∧ okc p q r d then pref m p q r else 0 := by
  have h1 : pref (m + 1) q r d = ((univ : Finset (Fin (m + 3) → Fin 7)).filter (fun y => pg y ∧
      y ⟨m + 1, by omega⟩ = q ∧ y ⟨m + 2, by omega⟩ = r ∧ r ≤ d ∧
        okc (y ⟨m, by omega⟩) q r d)).card := by
    show ((univ : Finset (Fin (m + 4) → Fin 7)).filter (fun x => pg x ∧
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
      · exact Fin.snoc_last (α := fun _ => Fin 7) d y
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

lemma pg3 : ∀ p q r : Fin 7, pg ![p, q, r] ↔
    (p ≤ q ∧ q ≤ r ∧ ((r : ℕ) = p ∨ (r : ℕ) = q ∨ (r : ℕ) = p + q)) := by
  decide +kernel

lemma pref_zero (p q r : Fin 7) :
    pref 0 p q r = if p ≤ q ∧ q ≤ r ∧ ((r : ℕ) = p ∨ (r : ℕ) = q ∨ (r : ℕ) = p + q) then 1 else 0 := by
  unfold pref
  have e : ∀ y : Fin 3 → Fin 7, y = ![y 0, y 1, y 2] := fun y => by
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

lemma a_eq (m : ℕ) : a (m + 1) = ∑ p : Fin 7, ∑ q : Fin 7, pref m p q ⟨6, by norm_num⟩ := by
  unfold a pref
  have hg : ∀ x : Fin (m + 3) → Fin 7, good x ↔ pg x ∧ x ⟨m + 2, by omega⟩ = ⟨6, by norm_num⟩ := by
    intro x
    unfold good pg
    rw [Fin.ext_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h3⟩, h2⟩
    · rintro ⟨⟨h1, h3⟩, h2⟩
      exact ⟨h1, h2, h3⟩
  rw [filter_congr (fun x _ => hg x)]
  rw [card_eq_sum_card_fiberwise (f := fun x : Fin (m + 3) → Fin 7 => x ⟨m, by omega⟩) (t := univ) (by simp)]
  refine sum_congr rfl (fun p _ => ?_)
  rw [filter_filter,
    card_eq_sum_card_fiberwise (f := fun x : Fin (m + 3) → Fin 7 => x ⟨m + 1, by omega⟩) (t := univ) (by simp)]
  refine sum_congr rfl (fun q _ => ?_)
  rw [filter_filter]
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and]
  tauto

/-! Continuations: Gv m s counts the ways to continue m more entries from the last three entries s
and end with 6. -/

/-- The continuation counts. -/
def Gv : ℕ → Fin 7 → Fin 7 → Fin 7 → ℕ
  | 0, _, _, r => if (r : ℕ) = 6 then 1 else 0
  | m + 1, p, q, r => ∑ d : Fin 7, if r ≤ d ∧ okc p q r d then Gv m q r d else 0

lemma Gv_succ (m : ℕ) (p q r : Fin 7) :
    Gv (m + 1) p q r = ∑ d : Fin 7, if r ≤ d ∧ okc p q r d then Gv m q r d else 0 := rfl

lemma shift (m j : ℕ) :
    ∑ p : Fin 7, ∑ q : Fin 7, ∑ r : Fin 7, pref (m + 1) p q r * Gv j p q r =
      ∑ p : Fin 7, ∑ q : Fin 7, ∑ r : Fin 7, pref m p q r * Gv (j + 1) p q r := by
  simp only [pref_succ, Gv_succ, sum_mul, mul_sum, ite_mul, mul_ite, zero_mul, mul_zero]
  calc ∑ q : Fin 7, ∑ r : Fin 7, ∑ d : Fin 7, ∑ p : Fin 7,
        (if r ≤ d ∧ okc p q r d then pref m p q r * Gv j q r d else 0)
      = ∑ q : Fin 7, ∑ r : Fin 7, ∑ p : Fin 7, ∑ d : Fin 7,
        (if r ≤ d ∧ okc p q r d then pref m p q r * Gv j q r d else 0) :=
          sum_congr rfl (fun q _ => sum_congr rfl (fun r _ => Finset.sum_comm))
    _ = ∑ q : Fin 7, ∑ p : Fin 7, ∑ r : Fin 7, ∑ d : Fin 7,
        (if r ≤ d ∧ okc p q r d then pref m p q r * Gv j q r d else 0) :=
          sum_congr rfl (fun q _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

lemma a_dual (m : ℕ) :
    (a (m + 1) : ℤ) = ∑ p : Fin 7, ∑ q : Fin 7, ∑ r : Fin 7,
      (if p ≤ q ∧ q ≤ r ∧ ((r : ℕ) = p ∨ (r : ℕ) = q ∨ (r : ℕ) = p + q) then (1 : ℤ) else 0) *
        (Gv m p q r : ℤ) := by
  have h0 : a (m + 1) = ∑ p : Fin 7, ∑ q : Fin 7, ∑ r : Fin 7, pref m p q r * Gv 0 p q r := by
    rw [a_eq]
    refine sum_congr rfl (fun p _ => sum_congr rfl (fun q _ => ?_))
    have hk : ∀ r : Fin 7, ((r : ℕ) = 6) ↔ r = ⟨6, by norm_num⟩ := fun r => by rw [Fin.ext_iff]
    simp only [Gv, mul_ite, mul_one, mul_zero, hk, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hs : ∀ i j : ℕ, ∑ p : Fin 7, ∑ q : Fin 7, ∑ r : Fin 7, pref i p q r * Gv j p q r =
      ∑ p : Fin 7, ∑ q : Fin 7, ∑ r : Fin 7, pref 0 p q r * Gv (i + j) p q r := by
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

/-! Gv for m ≤ 11, as tables g0, g1, ... checked level by level on the nondecreasing states. -/

/-- Gv 0 as a table. -/
def g0 : Fin 7 → Fin 7 → Fin 7 → ℕ :=
  ![![![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1]],
    ![![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1]],
    ![![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1]],
    ![![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1]],
    ![![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1]],
    ![![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1]],
    ![![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, 1]]]

lemma g0_eq : ∀ p q r : Fin 7, p ≤ q → q ≤ r → g0 p q r = if (r : ℕ) = 6 then 1 else 0 := by
  decide +kernel

lemma Gv0 : ∀ p q r : Fin 7, p ≤ q → q ≤ r → Gv 0 p q r = g0 p q r := by
  intro p q r hpq hqr
  rw [g0_eq p q r hpq hqr]
  rfl

/-- Gv 1 as a table. -/
def g1 : Fin 7 → Fin 7 → Fin 7 → ℕ :=
  ![![![0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 1, 0, 1], ![0, 0, 0, 1, 0, 0, 1], ![0, 0, 1, 0, 0, 0, 1], ![0, 1, 0, 0, 0, 0, 1], ![1, 1, 1, 1, 1, 1, 1]],
    ![![0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 0, 1, 1], ![0, 0, 0, 0, 1, 1, 1], ![0, 0, 0, 1, 0, 1, 1], ![0, 0, 1, 0, 0, 1, 1], ![1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1]],
    ![![0, 0, 0, 0, 1, 0, 1], ![0, 0, 0, 0, 1, 1, 1], ![0, 0, 0, 0, 1, 0, 1], ![0, 0, 0, 1, 1, 0, 1], ![1, 1, 1, 1, 1, 1, 1], ![0, 1, 0, 0, 1, 0, 1], ![1, 1, 1, 1, 1, 1, 1]],
    ![![0, 0, 0, 1, 0, 0, 1], ![0, 0, 0, 1, 0, 1, 1], ![0, 0, 0, 1, 1, 0, 1], ![1, 1, 1, 1, 1, 1, 1], ![0, 0, 1, 1, 0, 0, 1], ![0, 1, 0, 1, 0, 0, 1], ![1, 1, 1, 1, 1, 1, 1]],
    ![![0, 0, 1, 0, 0, 0, 1], ![0, 0, 1, 0, 0, 1, 1], ![1, 1, 1, 1, 1, 1, 1], ![0, 0, 1, 1, 0, 0, 1], ![0, 0, 1, 0, 0, 0, 1], ![0, 1, 1, 0, 0, 0, 1], ![1, 1, 1, 1, 1, 1, 1]],
    ![![0, 1, 0, 0, 0, 0, 1], ![1, 1, 1, 1, 1, 1, 1], ![0, 1, 0, 0, 1, 0, 1], ![0, 1, 0, 1, 0, 0, 1], ![0, 1, 1, 0, 0, 0, 1], ![0, 1, 0, 0, 0, 0, 1], ![1, 1, 1, 1, 1, 1, 1]],
    ![![1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1, 1]]]

lemma g1_eq : ∀ p q r : Fin 7, p ≤ q → q ≤ r →
    g1 p q r = ∑ d : Fin 7, if r ≤ d ∧ okc p q r d then g0 q r d else 0 := by
  decide +kernel

lemma Gv1 : ∀ p q r : Fin 7, p ≤ q → q ≤ r → Gv 1 p q r = g1 p q r := by
  intro p q r hpq hqr
  rw [Gv_succ, g1_eq p q r hpq hqr]
  refine sum_congr rfl (fun d _ => ?_)
  split_ifs with hc
  · rw [Gv0 q r d hqr hc.1]
  · rfl

/-- Gv 2 as a table. -/
def g2 : Fin 7 → Fin 7 → Fin 7 → ℕ :=
  ![![![0, 0, 0, 1, 0, 0, 1], ![0, 0, 0, 1, 1, 2, 1], ![0, 0, 1, 1, 2, 0, 1], ![1, 1, 1, 2, 0, 0, 1], ![0, 1, 3, 1, 0, 0, 1], ![0, 3, 0, 1, 0, 0, 1], ![2, 2, 2, 2, 2, 2, 1]],
    ![![0, 0, 0, 1, 0, 1, 1], ![0, 0, 0, 1, 1, 2, 1], ![0, 0, 1, 2, 3, 1, 1], ![1, 1, 2, 3, 0, 1, 1], ![0, 2, 5, 1, 0, 1, 1], ![2, 4, 1, 2, 1, 1, 1], ![3, 3, 3, 3, 3, 2, 1]],
    ![![0, 0, 1, 1, 1, 0, 1], ![0, 0, 1, 2, 2, 2, 1], ![1, 1, 1, 2, 2, 0, 1], ![1, 2, 2, 3, 1, 0, 1], ![2, 3, 3, 2, 1, 1, 1], ![0, 5, 1, 1, 1, 0, 1], ![3, 4, 3, 3, 2, 2, 1]],
    ![![0, 0, 0, 2, 0, 0, 1], ![0, 0, 2, 2, 1, 2, 1], ![0, 2, 1, 2, 3, 0, 1], ![2, 2, 2, 2, 1, 1, 1], ![0, 1, 5, 2, 0, 0, 1], ![0, 5, 0, 2, 0, 0, 1], ![3, 4, 4, 2, 2, 2, 1]],
    ![![0, 1, 2, 1, 0, 0, 1], ![1, 1, 3, 2, 1, 2, 1], ![2, 3, 2, 3, 2, 1, 1], ![1, 2, 3, 3, 0, 0, 1], ![0, 1, 3, 1, 0, 0, 1], ![0, 4, 2, 1, 0, 0, 1], ![3, 4, 3, 3, 2, 2, 1]],
    ![![0, 2, 0, 1, 0, 0, 1], ![2, 2, 2, 3, 2, 2, 1], ![0, 2, 1, 1, 3, 0, 1], ![1, 3, 1, 3, 0, 0, 1], ![0, 2, 4, 1, 0, 0, 1], ![0, 3, 0, 1, 0, 0, 1], ![3, 3, 3, 3, 3, 2, 1]],
    ![![1, 1, 1, 2, 1, 1, 1], ![1, 1, 1, 2, 2, 2, 1], ![1, 1, 2, 2, 2, 1, 1], ![2, 2, 2, 2, 1, 1, 1], ![1, 2, 3, 2, 1, 1, 1], ![1, 3, 1, 2, 1, 1, 1], ![2, 2, 2, 2, 2, 2, 1]]]

lemma g2_eq : ∀ p q r : Fin 7, p ≤ q → q ≤ r →
    g2 p q r = ∑ d : Fin 7, if r ≤ d ∧ okc p q r d then g1 q r d else 0 := by
  decide +kernel

lemma Gv2 : ∀ p q r : Fin 7, p ≤ q → q ≤ r → Gv 2 p q r = g2 p q r := by
  intro p q r hpq hqr
  rw [Gv_succ, g2_eq p q r hpq hqr]
  refine sum_congr rfl (fun d _ => ?_)
  split_ifs with hc
  · rw [Gv1 q r d hqr hc.1]
  · rfl

/-- Gv 3 as a table. -/
def g3 : Fin 7 → Fin 7 → Fin 7 → ℕ :=
  ![![![0, 0, 1, 2, 0, 0, 1], ![0, 0, 3, 3, 1, 2, 1], ![1, 3, 3, 3, 2, 0, 1], ![2, 3, 3, 3, 0, 0, 1], ![0, 4, 5, 3, 0, 0, 1], ![0, 5, 1, 3, 0, 0, 1], ![2, 2, 3, 3, 2, 2, 1]],
    ![![0, 0, 2, 2, 0, 1, 1], ![0, 0, 3, 3, 1, 2, 1], ![2, 3, 5, 4, 3, 1, 1], ![2, 5, 6, 4, 0, 1, 1], ![1, 7, 9, 3, 0, 1, 1], ![3, 7, 3, 4, 1, 1, 1], ![3, 3, 5, 4, 3, 2, 1]],
    ![![0, 1, 3, 2, 1, 0, 1], ![1, 1, 6, 4, 2, 2, 1], ![2, 5, 3, 4, 2, 0, 1], ![2, 7, 6, 4, 1, 0, 1], ![3, 10, 5, 4, 1, 1, 1], ![0, 10, 4, 3, 1, 0, 1], ![3, 5, 5, 4, 2, 2, 1]],
    ![![1, 2, 2, 3, 0, 0, 1], ![1, 2, 7, 4, 1, 2, 1], ![2, 7, 5, 4, 3, 0, 1], ![3, 4, 4, 3, 1, 1, 1], ![1, 6, 9, 4, 0, 0, 1], ![1, 10, 2, 4, 0, 0, 1], ![4, 6, 6, 3, 2, 2, 1]],
    ![![0, 3, 4, 2, 0, 0, 1], ![1, 3, 8, 4, 1, 2, 1], ![3, 8, 4, 5, 2, 1, 1], ![2, 5, 7, 4, 0, 0, 1], ![0, 4, 5, 3, 0, 0, 1], ![0, 7, 5, 3, 0, 0, 1], ![3, 6, 5, 4, 2, 2, 1]],
    ![![0, 3, 1, 2, 0, 0, 1], ![2, 3, 5, 5, 2, 2, 1], ![1, 6, 3, 3, 3, 0, 1], ![2, 6, 3, 4, 0, 0, 1], ![0, 5, 6, 3, 0, 0, 1], ![0, 5, 1, 3, 0, 0, 1], ![3, 4, 4, 4, 3, 2, 1]],
    ![![1, 1, 2, 3, 1, 1, 1], ![1, 1, 4, 4, 2, 2, 1], ![2, 4, 4, 4, 2, 1, 1], ![3, 4, 4, 3, 1, 1, 1], ![1, 5, 5, 4, 1, 1, 1], ![1, 5, 2, 4, 1, 1, 1], ![2, 2, 3, 3, 2, 2, 1]]]

lemma g3_eq : ∀ p q r : Fin 7, p ≤ q → q ≤ r →
    g3 p q r = ∑ d : Fin 7, if r ≤ d ∧ okc p q r d then g2 q r d else 0 := by
  decide +kernel

lemma Gv3 : ∀ p q r : Fin 7, p ≤ q → q ≤ r → Gv 3 p q r = g3 p q r := by
  intro p q r hpq hqr
  rw [Gv_succ, g3_eq p q r hpq hqr]
  refine sum_congr rfl (fun d _ => ?_)
  split_ifs with hc
  · rw [Gv2 q r d hqr hc.1]
  · rfl

/-- Gv 4 as a table. -/
def g4 : Fin 7 → Fin 7 → Fin 7 → ℕ :=
  ![![![0, 0, 3, 3, 0, 0, 1], ![0, 3, 9, 4, 1, 2, 1], ![3, 11, 5, 4, 2, 0, 1], ![4, 7, 9, 4, 0, 0, 1], ![0, 6, 7, 4, 0, 0, 1], ![0, 6, 3, 4, 0, 0, 1], ![2, 2, 5, 4, 2, 2, 1]],
    ![![0, 3, 6, 3, 0, 1, 1], ![2, 3, 9, 4, 1, 2, 1], ![6, 11, 9, 5, 3, 1, 1], ![6, 14, 12, 5, 0, 1, 1], ![3, 14, 13, 4, 0, 1, 1], ![4, 11, 7, 5, 1, 1, 1], ![3, 6, 9, 5, 3, 2, 1]],
    ![![1, 6, 5, 3, 1, 0, 1], ![4, 6, 12, 5, 2, 2, 1], ![4, 13, 5, 5, 2, 0, 1], ![6, 16, 12, 5, 1, 0, 1], ![5, 19, 7, 5, 1, 1, 1], ![1, 16, 6, 4, 1, 0, 1], ![4, 10, 7, 5, 2, 2, 1]],
    ![![2, 4, 6, 4, 0, 0, 1], ![2, 7, 13, 5, 1, 2, 1], ![5, 15, 9, 5, 3, 0, 1], ![5, 8, 10, 4, 1, 1, 1], ![2, 10, 13, 5, 0, 0, 1], ![2, 13, 6, 5, 0, 0, 1], ![5, 8, 10, 4, 2, 2, 1]],
    ![![0, 3, 6, 3, 0, 0, 1], ![1, 6, 14, 5, 1, 2, 1], ![5, 16, 6, 6, 2, 1, 1], ![4, 9, 13, 5, 0, 0, 1], ![0, 6, 7, 4, 0, 0, 1], ![0, 8, 7, 4, 0, 0, 1], ![3, 6, 7, 5, 2, 2, 1]],
    ![![0, 3, 3, 3, 0, 0, 1], ![2, 6, 11, 6, 2, 2, 1], ![3, 14, 5, 4, 3, 0, 1], ![4, 10, 9, 5, 0, 0, 1], ![0, 7, 8, 4, 0, 0, 1], ![0, 6, 3, 4, 0, 0, 1], ![3, 4, 6, 5, 3, 2, 1]],
    ![![1, 1, 4, 4, 1, 1, 1], ![1, 4, 10, 5, 2, 2, 1], ![4, 12, 6, 5, 2, 1, 1], ![5, 8, 10, 4, 1, 1, 1], ![1, 7, 7, 5, 1, 1, 1], ![1, 6, 4, 5, 1, 1, 1], ![2, 2, 5, 4, 2, 2, 1]]]

lemma g4_eq : ∀ p q r : Fin 7, p ≤ q → q ≤ r →
    g4 p q r = ∑ d : Fin 7, if r ≤ d ∧ okc p q r d then g3 q r d else 0 := by
  decide +kernel

lemma Gv4 : ∀ p q r : Fin 7, p ≤ q → q ≤ r → Gv 4 p q r = g4 p q r := by
  intro p q r hpq hqr
  rw [Gv_succ, g4_eq p q r hpq hqr]
  refine sum_congr rfl (fun d _ => ?_)
  split_ifs with hc
  · rw [Gv3 q r d hqr hc.1]
  · rfl

/-- Gv 5 as a table. -/
def g5 : Fin 7 → Fin 7 → Fin 7 → ℕ :=
  ![![![0, 3, 5, 4, 0, 0, 1], ![3, 12, 14, 5, 1, 2, 1], ![6, 23, 7, 5, 2, 0, 1], ![6, 13, 14, 5, 0, 0, 1], ![0, 9, 9, 5, 0, 0, 1], ![0, 9, 5, 5, 0, 0, 1], ![2, 5, 7, 5, 2, 2, 1]],
    ![![0, 12, 9, 4, 0, 1, 1], ![9, 12, 14, 5, 1, 2, 1], ![15, 23, 12, 6, 3, 1, 1], ![10, 26, 17, 6, 0, 1, 1], ![3, 23, 16, 5, 0, 1, 1], ![4, 20, 10, 6, 1, 1, 1], ![3, 15, 12, 6, 3, 2, 1]],
    ![![3, 16, 7, 4, 1, 0, 1], ![12, 16, 17, 6, 2, 2, 1], ![7, 25, 7, 6, 2, 0, 1], ![12, 28, 17, 6, 1, 0, 1], ![7, 29, 9, 6, 1, 1, 1], ![3, 26, 8, 5, 1, 0, 1], ![6, 20, 9, 6, 2, 2, 1]],
    ![![3, 8, 9, 5, 0, 0, 1], ![6, 17, 18, 6, 1, 2, 1], ![9, 27, 12, 6, 3, 0, 1], ![7, 14, 15, 5, 1, 1, 1], ![3, 14, 16, 6, 0, 0, 1], ![3, 17, 9, 6, 0, 0, 1], ![6, 12, 13, 5, 2, 2, 1]],
    ![![0, 6, 8, 4, 0, 0, 1], ![4, 15, 19, 6, 1, 2, 1], ![8, 28, 8, 7, 2, 1, 1], ![6, 15, 18, 6, 0, 0, 1], ![0, 9, 9, 5, 0, 0, 1], ![0, 11, 9, 5, 0, 0, 1], ![3, 9, 9, 6, 2, 2, 1]],
    ![![0, 6, 5, 4, 0, 0, 1], ![5, 15, 16, 7, 2, 2, 1], ![6, 26, 7, 5, 3, 0, 1], ![6, 16, 14, 6, 0, 0, 1], ![0, 10, 10, 5, 0, 0, 1], ![0, 9, 5, 5, 0, 0, 1], ![3, 7, 8, 6, 3, 2, 1]],
    ![![1, 4, 6, 5, 1, 1, 1], ![4, 13, 15, 6, 2, 2, 1], ![7, 24, 8, 6, 2, 1, 1], ![7, 14, 15, 5, 1, 1, 1], ![1, 10, 9, 6, 1, 1, 1], ![1, 9, 6, 6, 1, 1, 1], ![2, 5, 7, 5, 2, 2, 1]]]

lemma g5_eq : ∀ p q r : Fin 7, p ≤ q → q ≤ r →
    g5 p q r = ∑ d : Fin 7, if r ≤ d ∧ okc p q r d then g4 q r d else 0 := by
  decide +kernel

lemma Gv5 : ∀ p q r : Fin 7, p ≤ q → q ≤ r → Gv 5 p q r = g5 p q r := by
  intro p q r hpq hqr
  rw [Gv_succ, g5_eq p q r hpq hqr]
  refine sum_congr rfl (fun d _ => ?_)
  split_ifs with hc
  · rw [Gv4 q r d hqr hc.1]
  · rfl

/-- Gv 6 as a table. -/
def g6 : Fin 7 → Fin 7 → Fin 7 → ℕ :=
  ![![![0, 12, 7, 5, 0, 0, 1], ![12, 26, 18, 6, 1, 2, 1], ![10, 39, 9, 6, 2, 0, 1], ![8, 24, 18, 6, 0, 0, 1], ![0, 18, 11, 6, 0, 0, 1], ![0, 18, 7, 6, 0, 0, 1], ![2, 14, 9, 6, 2, 2, 1]],
    ![![3, 26, 12, 5, 0, 1, 1], ![21, 26, 18, 6, 1, 2, 1], ![30, 39, 15, 7, 3, 1, 1], ![16, 42, 21, 7, 0, 1, 1], ![6, 37, 19, 6, 0, 1, 1], ![7, 34, 13, 7, 1, 1, 1], ![6, 29, 15, 7, 3, 2, 1]],
    ![![5, 31, 9, 5, 1, 0, 1], ![25, 31, 21, 7, 2, 2, 1], ![11, 41, 9, 7, 2, 0, 1], ![17, 44, 21, 7, 1, 0, 1], ![9, 44, 11, 7, 1, 1, 1], ![5, 41, 10, 6, 1, 0, 1], ![8, 35, 11, 7, 2, 2, 1]],
    ![![4, 18, 12, 6, 0, 0, 1], ![16, 32, 22, 7, 1, 2, 1], ![14, 43, 15, 7, 3, 0, 1], ![9, 25, 19, 6, 1, 1, 1], ![4, 24, 19, 7, 0, 0, 1], ![4, 27, 12, 7, 0, 0, 1], ![7, 22, 16, 6, 2, 2, 1]],
    ![![0, 15, 10, 5, 0, 0, 1], ![13, 29, 23, 7, 1, 2, 1], ![12, 44, 10, 8, 2, 1, 1], ![8, 26, 22, 7, 0, 0, 1], ![0, 18, 11, 6, 0, 0, 1], ![0, 20, 11, 6, 0, 0, 1], ![3, 18, 11, 7, 2, 2, 1]],
    ![![0, 15, 7, 5, 0, 0, 1], ![14, 29, 20, 8, 2, 2, 1], ![10, 42, 9, 6, 3, 0, 1], ![8, 27, 18, 7, 0, 0, 1], ![0, 19, 12, 6, 0, 0, 1], ![0, 18, 7, 6, 0, 0, 1], ![3, 16, 10, 7, 3, 2, 1]],
    ![![1, 13, 8, 6, 1, 1, 1], ![13, 27, 19, 7, 2, 2, 1], ![11, 40, 10, 7, 2, 1, 1], ![9, 25, 19, 6, 1, 1, 1], ![1, 19, 11, 7, 1, 1, 1], ![1, 18, 8, 7, 1, 1, 1], ![2, 14, 9, 6, 2, 2, 1]]]

lemma g6_eq : ∀ p q r : Fin 7, p ≤ q → q ≤ r →
    g6 p q r = ∑ d : Fin 7, if r ≤ d ∧ okc p q r d then g5 q r d else 0 := by
  decide +kernel

lemma Gv6 : ∀ p q r : Fin 7, p ≤ q → q ≤ r → Gv 6 p q r = g6 p q r := by
  intro p q r hpq hqr
  rw [Gv_succ, g6_eq p q r hpq hqr]
  refine sum_congr rfl (fun d _ => ?_)
  split_ifs with hc
  · rw [Gv5 q r d hqr hc.1]
  · rfl

/-- Gv 7 as a table. -/
def g7 : Fin 7 → Fin 7 → Fin 7 → ℕ :=
  ![![![0, 26, 9, 6, 0, 0, 1], ![29, 44, 22, 7, 1, 2, 1], ![14, 59, 11, 7, 2, 0, 1], ![10, 40, 22, 7, 0, 0, 1], ![0, 32, 13, 7, 0, 0, 1], ![0, 32, 9, 7, 0, 0, 1], ![2, 28, 11, 7, 2, 2, 1]],
    ![![12, 44, 15, 6, 0, 1, 1], ![41, 44, 22, 7, 1, 2, 1], ![50, 59, 18, 8, 3, 1, 1], ![28, 62, 25, 8, 0, 1, 1], ![15, 55, 22, 7, 0, 1, 1], ![16, 52, 16, 8, 1, 1, 1], ![15, 47, 18, 8, 3, 2, 1]],
    ![![7, 50, 11, 6, 1, 0, 1], ![46, 50, 25, 8, 2, 2, 1], ![15, 61, 11, 8, 2, 0, 1], ![22, 64, 25, 8, 1, 0, 1], ![11, 63, 13, 8, 1, 1, 1], ![7, 60, 12, 7, 1, 0, 1], ![10, 54, 13, 8, 2, 2, 1]],
    ![![5, 33, 15, 7, 0, 0, 1], ![34, 51, 26, 8, 1, 2, 1], ![19, 63, 18, 8, 3, 0, 1], ![11, 41, 23, 7, 1, 1, 1], ![5, 39, 22, 8, 0, 0, 1], ![5, 42, 15, 8, 0, 0, 1], ![8, 37, 19, 7, 2, 2, 1]],
    ![![0, 29, 12, 6, 0, 0, 1], ![30, 47, 27, 8, 1, 2, 1], ![16, 64, 12, 9, 2, 1, 1], ![10, 42, 26, 8, 0, 0, 1], ![0, 32, 13, 7, 0, 0, 1], ![0, 34, 13, 7, 0, 0, 1], ![3, 32, 13, 8, 2, 2, 1]],
    ![![0, 29, 9, 6, 0, 0, 1], ![31, 47, 24, 9, 2, 2, 1], ![14, 62, 11, 7, 3, 0, 1], ![10, 43, 22, 8, 0, 0, 1], ![0, 33, 14, 7, 0, 0, 1], ![0, 32, 9, 7, 0, 0, 1], ![3, 30, 12, 8, 3, 2, 1]],
    ![![1, 27, 10, 7, 1, 1, 1], ![30, 45, 23, 8, 2, 2, 1], ![15, 60, 12, 8, 2, 1, 1], ![11, 41, 23, 7, 1, 1, 1], ![1, 33, 13, 8, 1, 1, 1], ![1, 32, 10, 8, 1, 1, 1], ![2, 28, 11, 7, 2, 2, 1]]]

lemma g7_eq : ∀ p q r : Fin 7, p ≤ q → q ≤ r →
    g7 p q r = ∑ d : Fin 7, if r ≤ d ∧ okc p q r d then g6 q r d else 0 := by
  decide +kernel

lemma Gv7 : ∀ p q r : Fin 7, p ≤ q → q ≤ r → Gv 7 p q r = g7 p q r := by
  intro p q r hpq hqr
  rw [Gv_succ, g7_eq p q r hpq hqr]
  refine sum_congr rfl (fun d _ => ?_)
  split_ifs with hc
  · rw [Gv6 q r d hqr hc.1]
  · rfl

/-- Gv 8 as a table. -/
def g8 : Fin 7 → Fin 7 → Fin 7 → ℕ :=
  ![![![0, 44, 11, 7, 0, 0, 1], ![56, 66, 26, 8, 1, 2, 1], ![18, 83, 13, 8, 2, 0, 1], ![12, 60, 26, 8, 0, 0, 1], ![0, 50, 15, 8, 0, 0, 1], ![0, 50, 11, 8, 0, 0, 1], ![2, 46, 13, 8, 2, 2, 1]],
    ![![26, 66, 18, 7, 0, 1, 1], ![71, 66, 26, 8, 1, 2, 1], ![74, 83, 21, 9, 3, 1, 1], ![45, 86, 29, 9, 0, 1, 1], ![29, 77, 25, 8, 0, 1, 1], ![30, 74, 19, 9, 1, 1, 1], ![29, 69, 21, 9, 3, 2, 1]],
    ![![9, 73, 13, 7, 1, 0, 1], ![77, 73, 29, 9, 2, 2, 1], ![19, 85, 13, 9, 2, 0, 1], ![27, 88, 29, 9, 1, 0, 1], ![13, 86, 15, 9, 1, 1, 1], ![9, 83, 14, 8, 1, 0, 1], ![12, 77, 15, 9, 2, 2, 1]],
    ![![6, 52, 18, 8, 0, 0, 1], ![62, 74, 30, 9, 1, 2, 1], ![24, 87, 21, 9, 3, 0, 1], ![13, 61, 27, 8, 1, 1, 1], ![6, 58, 25, 9, 0, 0, 1], ![6, 61, 18, 9, 0, 0, 1], ![9, 56, 22, 8, 2, 2, 1]],
    ![![0, 47, 14, 7, 0, 0, 1], ![57, 69, 31, 9, 1, 2, 1], ![20, 88, 14, 10, 2, 1, 1], ![12, 62, 30, 9, 0, 0, 1], ![0, 50, 15, 8, 0, 0, 1], ![0, 52, 15, 8, 0, 0, 1], ![3, 50, 15, 9, 2, 2, 1]],
    ![![0, 47, 11, 7, 0, 0, 1], ![58, 69, 28, 10, 2, 2, 1], ![18, 86, 13, 8, 3, 0, 1], ![12, 63, 26, 9, 0, 0, 1], ![0, 51, 16, 8, 0, 0, 1], ![0, 50, 11, 8, 0, 0, 1], ![3, 48, 14, 9, 3, 2, 1]],
    ![![1, 45, 12, 8, 1, 1, 1], ![57, 67, 27, 9, 2, 2, 1], ![19, 84, 14, 9, 2, 1, 1], ![13, 61, 27, 8, 1, 1, 1], ![1, 51, 15, 9, 1, 1, 1], ![1, 50, 12, 9, 1, 1, 1], ![2, 46, 13, 8, 2, 2, 1]]]

lemma g8_eq : ∀ p q r : Fin 7, p ≤ q → q ≤ r →
    g8 p q r = ∑ d : Fin 7, if r ≤ d ∧ okc p q r d then g7 q r d else 0 := by
  decide +kernel

lemma Gv8 : ∀ p q r : Fin 7, p ≤ q → q ≤ r → Gv 8 p q r = g8 p q r := by
  intro p q r hpq hqr
  rw [Gv_succ, g8_eq p q r hpq hqr]
  refine sum_congr rfl (fun d _ => ?_)
  split_ifs with hc
  · rw [Gv7 q r d hqr hc.1]
  · rfl

/-- Gv 9 as a table. -/
def g9 : Fin 7 → Fin 7 → Fin 7 → ℕ :=
  ![![![0, 66, 13, 8, 0, 0, 1], ![92, 92, 30, 9, 1, 2, 1], ![22, 111, 15, 9, 2, 0, 1], ![14, 84, 30, 9, 0, 0, 1], ![0, 72, 17, 9, 0, 0, 1], ![0, 72, 13, 9, 0, 0, 1], ![2, 68, 15, 9, 2, 2, 1]],
    ![![44, 92, 21, 8, 0, 1, 1], ![110, 92, 30, 9, 1, 2, 1], ![102, 111, 24, 10, 3, 1, 1], ![66, 114, 33, 10, 0, 1, 1], ![47, 103, 28, 9, 0, 1, 1], ![48, 100, 22, 10, 1, 1, 1], ![47, 95, 24, 10, 3, 2, 1]],
    ![![11, 100, 15, 8, 1, 0, 1], ![117, 100, 33, 10, 2, 2, 1], ![23, 113, 15, 10, 2, 0, 1], ![32, 116, 33, 10, 1, 0, 1], ![15, 113, 17, 10, 1, 1, 1], ![11, 110, 16, 9, 1, 0, 1], ![14, 104, 17, 10, 2, 2, 1]],
    ![![7, 75, 21, 9, 0, 0, 1], ![99, 101, 34, 10, 1, 2, 1], ![29, 115, 24, 10, 3, 0, 1], ![15, 85, 31, 9, 1, 1, 1], ![7, 81, 28, 10, 0, 0, 1], ![7, 84, 21, 10, 0, 0, 1], ![10, 79, 25, 9, 2, 2, 1]],
    ![![0, 69, 16, 8, 0, 0, 1], ![93, 95, 35, 10, 1, 2, 1], ![24, 116, 16, 11, 2, 1, 1], ![14, 86, 34, 10, 0, 0, 1], ![0, 72, 17, 9, 0, 0, 1], ![0, 74, 17, 9, 0, 0, 1], ![3, 72, 17, 10, 2, 2, 1]],
    ![![0, 69, 13, 8, 0, 0, 1], ![94, 95, 32, 11, 2, 2, 1], ![22, 114, 15, 9, 3, 0, 1], ![14, 87, 30, 10, 0, 0, 1], ![0, 73, 18, 9, 0, 0, 1], ![0, 72, 13, 9, 0, 0, 1], ![3, 70, 16, 10, 3, 2, 1]],
    ![![1, 67, 14, 9, 1, 1, 1], ![93, 93, 31, 10, 2, 2, 1], ![23, 112, 16, 10, 2, 1, 1], ![15, 85, 31, 9, 1, 1, 1], ![1, 73, 17, 10, 1, 1, 1], ![1, 72, 14, 10, 1, 1, 1], ![2, 68, 15, 9, 2, 2, 1]]]

lemma g9_eq : ∀ p q r : Fin 7, p ≤ q → q ≤ r →
    g9 p q r = ∑ d : Fin 7, if r ≤ d ∧ okc p q r d then g8 q r d else 0 := by
  decide +kernel

lemma Gv9 : ∀ p q r : Fin 7, p ≤ q → q ≤ r → Gv 9 p q r = g9 p q r := by
  intro p q r hpq hqr
  rw [Gv_succ, g9_eq p q r hpq hqr]
  refine sum_congr rfl (fun d _ => ?_)
  split_ifs with hc
  · rw [Gv8 q r d hqr hc.1]
  · rfl

/-- Gv 10 as a table. -/
def g10 : Fin 7 → Fin 7 → Fin 7 → ℕ :=
  ![![![0, 92, 15, 9, 0, 0, 1], ![136, 122, 34, 10, 1, 2, 1], ![26, 143, 17, 10, 2, 0, 1], ![16, 112, 34, 10, 0, 0, 1], ![0, 98, 19, 10, 0, 0, 1], ![0, 98, 15, 10, 0, 0, 1], ![2, 94, 17, 10, 2, 2, 1]],
    ![![66, 122, 24, 9, 0, 1, 1], ![157, 122, 34, 10, 1, 2, 1], ![134, 143, 27, 11, 3, 1, 1], ![91, 146, 37, 11, 0, 1, 1], ![69, 133, 31, 10, 0, 1, 1], ![70, 130, 25, 11, 1, 1, 1], ![69, 125, 27, 11, 3, 2, 1]],
    ![![13, 131, 17, 9, 1, 0, 1], ![165, 131, 37, 11, 2, 2, 1], ![27, 145, 17, 11, 2, 0, 1], ![37, 148, 37, 11, 1, 0, 1], ![17, 144, 19, 11, 1, 1, 1], ![13, 141, 18, 10, 1, 0, 1], ![16, 135, 19, 11, 2, 2, 1]],
    ![![8, 102, 24, 10, 0, 0, 1], ![144, 132, 38, 11, 1, 2, 1], ![34, 147, 27, 11, 3, 0, 1], ![17, 113, 35, 10, 1, 1, 1], ![8, 108, 31, 11, 0, 0, 1], ![8, 111, 24, 11, 0, 0, 1], ![11, 106, 28, 10, 2, 2, 1]],
    ![![0, 95, 18, 9, 0, 0, 1], ![137, 125, 39, 11, 1, 2, 1], ![28, 148, 18, 12, 2, 1, 1], ![16, 114, 38, 11, 0, 0, 1], ![0, 98, 19, 10, 0, 0, 1], ![0, 100, 19, 10, 0, 0, 1], ![3, 98, 19, 11, 2, 2, 1]],
    ![![0, 95, 15, 9, 0, 0, 1], ![138, 125, 36, 12, 2, 2, 1], ![26, 146, 17, 10, 3, 0, 1], ![16, 115, 34, 11, 0, 0, 1], ![0, 99, 20, 10, 0, 0, 1], ![0, 98, 15, 10, 0, 0, 1], ![3, 96, 18, 11, 3, 2, 1]],
    ![![1, 93, 16, 10, 1, 1, 1], ![137, 123, 35, 11, 2, 2, 1], ![27, 144, 18, 11, 2, 1, 1], ![17, 113, 35, 10, 1, 1, 1], ![1, 99, 19, 11, 1, 1, 1], ![1, 98, 16, 11, 1, 1, 1], ![2, 94, 17, 10, 2, 2, 1]]]

lemma g10_eq : ∀ p q r : Fin 7, p ≤ q → q ≤ r →
    g10 p q r = ∑ d : Fin 7, if r ≤ d ∧ okc p q r d then g9 q r d else 0 := by
  decide +kernel

lemma Gv10 : ∀ p q r : Fin 7, p ≤ q → q ≤ r → Gv 10 p q r = g10 p q r := by
  intro p q r hpq hqr
  rw [Gv_succ, g10_eq p q r hpq hqr]
  refine sum_congr rfl (fun d _ => ?_)
  split_ifs with hc
  · rw [Gv9 q r d hqr hc.1]
  · rfl

/-- Gv 11 as a table. -/
def g11 : Fin 7 → Fin 7 → Fin 7 → ℕ :=
  ![![![0, 122, 17, 10, 0, 0, 1], ![188, 156, 38, 11, 1, 2, 1], ![30, 179, 19, 11, 2, 0, 1], ![18, 144, 38, 11, 0, 0, 1], ![0, 128, 21, 11, 0, 0, 1], ![0, 128, 17, 11, 0, 0, 1], ![2, 124, 19, 11, 2, 2, 1]],
    ![![92, 156, 27, 10, 0, 1, 1], ![212, 156, 38, 11, 1, 2, 1], ![170, 179, 30, 12, 3, 1, 1], ![120, 182, 41, 12, 0, 1, 1], ![95, 167, 34, 11, 0, 1, 1], ![96, 164, 28, 12, 1, 1, 1], ![95, 159, 30, 12, 3, 2, 1]],
    ![![15, 166, 19, 10, 1, 0, 1], ![221, 166, 41, 12, 2, 2, 1], ![31, 181, 19, 12, 2, 0, 1], ![42, 184, 41, 12, 1, 0, 1], ![19, 179, 21, 12, 1, 1, 1], ![15, 176, 20, 11, 1, 0, 1], ![18, 170, 21, 12, 2, 2, 1]],
    ![![9, 133, 27, 11, 0, 0, 1], ![197, 167, 42, 12, 1, 2, 1], ![39, 183, 30, 12, 3, 0, 1], ![19, 145, 39, 11, 1, 1, 1], ![9, 139, 34, 12, 0, 0, 1], ![9, 142, 27, 12, 0, 0, 1], ![12, 137, 31, 11, 2, 2, 1]],
    ![![0, 125, 20, 10, 0, 0, 1], ![189, 159, 43, 12, 1, 2, 1], ![32, 184, 20, 13, 2, 1, 1], ![18, 146, 42, 12, 0, 0, 1], ![0, 128, 21, 11, 0, 0, 1], ![0, 130, 21, 11, 0, 0, 1], ![3, 128, 21, 12, 2, 2, 1]],
    ![![0, 125, 17, 10, 0, 0, 1], ![190, 159, 40, 13, 2, 2, 1], ![30, 182, 19, 11, 3, 0, 1], ![18, 147, 38, 12, 0, 0, 1], ![0, 129, 22, 11, 0, 0, 1], ![0, 128, 17, 11, 0, 0, 1], ![3, 126, 20, 12, 3, 2, 1]],
    ![![1, 123, 18, 11, 1, 1, 1], ![189, 157, 39, 12, 2, 2, 1], ![31, 180, 20, 12, 2, 1, 1], ![19, 145, 39, 11, 1, 1, 1], ![1, 129, 21, 12, 1, 1, 1], ![1, 128, 18, 12, 1, 1, 1], ![2, 124, 19, 11, 2, 2, 1]]]

lemma g11_eq : ∀ p q r : Fin 7, p ≤ q → q ≤ r →
    g11 p q r = ∑ d : Fin 7, if r ≤ d ∧ okc p q r d then g10 q r d else 0 := by
  decide +kernel

lemma Gv11 : ∀ p q r : Fin 7, p ≤ q → q ≤ r → Gv 11 p q r = g11 p q r := by
  intro p q r hpq hqr
  rw [Gv_succ, g11_eq p q r hpq hqr]
  refine sum_congr rfl (fun d _ => ?_)
  split_ifs with hc
  · rw [Gv10 q r d hqr hc.1]
  · rfl

/-- The weights of the starts: the arrangements of length 3. -/
def w (p q r : Fin 7) : ℤ :=
  if p ≤ q ∧ q ≤ r ∧ ((r : ℕ) = p ∨ (r : ℕ) = q ∨ (r : ℕ) = p + q) then 1 else 0

lemma a_S (m : ℕ) : (a (m + 1) : ℤ) = ∑ p : Fin 7, ∑ q : Fin 7, ∑ r : Fin 7, w p q r * (Gv m p q r : ℤ) :=
  a_dual m

lemma w_congr (f g : Fin 7 → Fin 7 → Fin 7 → ℕ) (h : ∀ p q r : Fin 7, p ≤ q → q ≤ r → f p q r = g p q r) :
    ∑ p : Fin 7, ∑ q : Fin 7, ∑ r : Fin 7, w p q r * (f p q r : ℤ) =
      ∑ p : Fin 7, ∑ q : Fin 7, ∑ r : Fin 7, w p q r * (g p q r : ℤ) := by
  refine sum_congr rfl (fun p _ => sum_congr rfl (fun q _ => sum_congr rfl (fun r _ => ?_)))
  unfold w
  split_ifs with hc
  · rw [h p q r hc.1 hc.2.1]
  · simp

lemma a1 : (a 1 : ℤ) = 10 := by
  rw [a_S, w_congr _ _ Gv0]
  decide +kernel

lemma a2 : (a 2 : ℤ) = 18 := by
  rw [a_S, w_congr _ _ Gv1]
  decide +kernel

lemma a3 : (a 3 : ℤ) = 30 := by
  rw [a_S, w_congr _ _ Gv2]
  decide +kernel

lemma a4 : (a 4 : ℤ) = 47 := by
  rw [a_S, w_congr _ _ Gv3]
  decide +kernel

lemma a5 : (a 5 : ℤ) = 72 := by
  rw [a_S, w_congr _ _ Gv4]
  decide +kernel

lemma a6 : (a 6 : ℤ) = 107 := by
  rw [a_S, w_congr _ _ Gv5]
  decide +kernel

lemma a7 : (a 7 : ℤ) = 151 := by
  rw [a_S, w_congr _ _ Gv6]
  decide +kernel

lemma a8 : (a 8 : ℤ) = 203 := by
  rw [a_S, w_congr _ _ Gv7]
  decide +kernel

lemma a9 : (a 9 : ℤ) = 263 := by
  rw [a_S, w_congr _ _ Gv8]
  decide +kernel

lemma a10 : (a 10 : ℤ) = 331 := by
  rw [a_S, w_congr _ _ Gv9]
  decide +kernel

lemma a11 : (a 11 : ℤ) = 407 := by
  rw [a_S, w_congr _ _ Gv10]
  decide +kernel

/-- The third difference of the continuation counts. -/
def R (m : ℕ) (p q r : Fin 7) : ℤ := (Gv (m + 3) p q r : ℤ) - 3 * (Gv (m + 2) p q r : ℤ) + 3 * (Gv (m + 1) p q r : ℤ) - (Gv m p q r : ℤ)

lemma R_succ (m : ℕ) (p q r : Fin 7) :
    R (m + 1) p q r = ∑ d : Fin 7, if r ≤ d ∧ okc p q r d then R m q r d else 0 := by
  unfold R
  rw [show m + 1 + 1 = m + 1 + 1 by ring, show m + 1 + 2 = m + 2 + 1 by ring, show m + 1 + 3 = m + 3 + 1 by ring]
  rw [Gv_succ (m + 3), Gv_succ (m + 2), Gv_succ (m + 1), Gv_succ m]
  push_cast
  simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl (fun d _ => ?_)
  split_ifs <;> ring

lemma vec_id : ∀ p q r : Fin 7, p ≤ q → q ≤ r → (g11 p q r : ℤ) - 3 * (g10 p q r : ℤ) + 3 * (g9 p q r : ℤ) - (g8 p q r : ℤ) = 0 := by
  decide +kernel

lemma R_zero (m : ℕ) (hm : 8 ≤ m) : ∀ p q r : Fin 7, p ≤ q → q ≤ r → R m p q r = 0 := by
  induction m, hm using Nat.le_induction with
  | base =>
    intro p q r hpq hqr
    unfold R
    rw [Gv11 p q r hpq hqr, Gv10 p q r hpq hqr, Gv9 p q r hpq hqr, Gv8 p q r hpq hqr]
    exact vec_id p q r hpq hqr
  | succ m hm ih =>
    intro p q r hpq hqr
    rw [R_succ]
    refine sum_eq_zero (fun d _ => ?_)
    split_ifs with hc
    · exact ih q r d hqr hc.1
    · rfl

lemma rec_a (n : ℕ) (hn : 6 ≤ n) : (a (n + 3) : ℤ) - 3 * (a (n + 2) : ℤ) + 3 * (a (n + 1) : ℤ) - (a n : ℤ) = 0 := by
  rcases Nat.lt_or_ge n 9 with h | h
  · interval_cases n
    · rw [a9, a8, a7, a6]
      norm_num
    · rw [a10, a9, a8, a7]
      norm_num
    · rw [a11, a10, a9, a8]
      norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [show m + 1 + 1 = m + 1 + 1 by ring, show m + 1 + 2 = m + 2 + 1 by ring, show m + 1 + 3 = m + 3 + 1 by ring]
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
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 3 =
      X * (10 - 12 * X + 6 * X ^ 2 + X ^ 3 + 3 * X ^ 4 + 2 * X ^ 5 - X ^ 6 - X ^ 7) := by
  have v1 : (a 1 : ℚ) = 10 := by exact_mod_cast a1
  have v2 : (a 2 : ℚ) = 18 := by exact_mod_cast a2
  have v3 : (a 3 : ℚ) = 30 := by exact_mod_cast a3
  have v4 : (a 4 : ℚ) = 47 := by exact_mod_cast a4
  have v5 : (a 5 : ℚ) = 72 := by exact_mod_cast a5
  have v6 : (a 6 : ℚ) = 107 := by exact_mod_cast a6
  have v7 : (a 7 : ℚ) = 151 := by exact_mod_cast a7
  have v8 : (a 8 : ℚ) = 203 := by exact_mod_cast a8
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 3 = A - C (3 : ℚ) * (A * X ^ 1) + C (3 : ℚ) * (A * X ^ 2) - A * X ^ 3 := by
    simp only [map_ofNat]
    ring
  have e2 : (X * (10 - 12 * X + 6 * X ^ 2 + X ^ 3 + 3 * X ^ 4 + 2 * X ^ 5 - X ^ 6 - X ^ 7) : ℚ⟦X⟧) = X ^ 1 * C (10 : ℚ) - X ^ 2 * C (12 : ℚ) + X ^ 3 * C (6 : ℚ) + X ^ 4 + X ^ 5 * C (3 : ℚ) + X ^ 6 * C (2 : ℚ) - X ^ 7 - X ^ 8 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk,
    coeff_C_mul]
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | m
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
      if_false, v1, v2, v3, v4]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, if_true,
      if_false, v2, v3, v4, v5]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, if_true,
      if_false, v3, v4, v5, v6]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, if_true,
      if_false, v4, v5, v6, v7]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, if_true,
      if_false, v5, v6, v7, v8]
    all_goals norm_num
  · simp only [show ¬ (m + 9 = 0) by omega,
      show 1 ≤ m + 9 by omega,
      show m + 9 - 1 = m + 8 by omega,
      show ¬ (m + 8 = 0) by omega,
      show 2 ≤ m + 9 by omega,
      show m + 9 - 2 = m + 7 by omega,
      show ¬ (m + 7 = 0) by omega,
      show 3 ≤ m + 9 by omega,
      show m + 9 - 3 = m + 6 by omega,
      show ¬ (m + 6 = 0) by omega,
      show ¬ (m + 9 = 1) by omega,
      show ¬ (m + 9 = 2) by omega,
      show ¬ (m + 9 = 3) by omega,
      show ¬ (m + 9 = 4) by omega,
      show ¬ (m + 9 = 5) by omega,
      show ¬ (m + 9 = 6) by omega,
      show ¬ (m + 9 = 7) by omega,
      show ¬ (m + 9 = 8) by omega, if_true, if_false]
    have h := rec_a (m + 6) (by omega)
    rw [show m + 6 + 1 = m + 7 by ring, show m + 6 + 2 = m + 8 by ring, show m + 6 + 3 = m + 9 by ring] at h
    have hq : (a (m + 9) : ℚ) - 3 * (a (m + 8) : ℚ) + 3 * (a (m + 7) : ℚ) - (a (m + 6) : ℚ) = 0 := by exact_mod_cast h
    linear_combination hq

/-- Barker's recurrence. -/
theorem recur : ∀ n : ℕ, 8 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
  rw [show m + 9 - 1 = m + 8 by omega, show m + 9 - 2 = m + 7 by omega, show m + 9 - 3 = m + 6 by omega]
  have h := rec_a (m + 6) (by omega)
  rw [show m + 6 + 1 = m + 7 by ring, show m + 6 + 2 = m + 8 by ring, show m + 6 + 3 = m + 9 by ring] at h
  linear_combination h

/-- Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 3 =
      X * (10 - 12 * X + 6 * X ^ 2 + X ^ 3 + 3 * X ^ 4 + 2 * X ^ 5 - X ^ 6 - X ^ 7) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a190038

theorem OMA.solution : type_of% @OMA.S_oeis_a190038.main :=
  OMA.S_oeis_a190038.conjecture
