import OMAStatements.S_oeis_a184038

namespace OMA.S_oeis_a184038

open PowerSeries Finset



/-! ### Multisets of two and four values -/

set_option maxHeartbeats 4000000 in
lemma canc_h : ∀ a x b y e g : Fin 4,
    ({a, x, b, y} : Multiset (Fin 4)) = {x, e, y, g} → ({a, b} : Multiset (Fin 4)) = {e, g} := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma canc_v : ∀ a x b y e g : Fin 4,
    ({a, x, b, y} : Multiset (Fin 4)) = {b, y, e, g} → ({a, x} : Multiset (Fin 4)) = {e, g} := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma uncanc_h : ∀ a x b y e g : Fin 4,
    ({a, b} : Multiset (Fin 4)) = {e, g} → ({a, x, b, y} : Multiset (Fin 4)) = {x, e, y, g} := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma uncanc_v : ∀ a x b y e g : Fin 4,
    ({a, x} : Multiset (Fin 4)) = {e, g} → ({a, x, b, y} : Multiset (Fin 4)) = {b, y, e, g} := by
  decide +kernel

lemma pair_left : ∀ a b c : Fin 4, ({a, b} : Multiset (Fin 4)) = {a, c} → b = c := by
  decide +kernel

lemma pair_right : ∀ a b c : Fin 4, ({a, b} : Multiset (Fin 4)) = {c, b} → a = c := by
  decide +kernel

lemma pair_swap : ∀ a b c d : Fin 4, ({a, b} : Multiset (Fin 4)) = {c, d} → c ≠ a →
    c = b ∧ d = a := by
  decide +kernel

lemma pair_symm : ∀ a b : Fin 4, ({a, b} : Multiset (Fin 4)) = {b, a} := by
  decide +kernel

/-! ### The array read through natural-number indices -/

/-- Entry (i, j) of the array, 0 outside it. -/
def F {n : ℕ} (f : Fin (n + 1) → Fin 9 → Fin 4) (i j : ℕ) : Fin 4 :=
  if h : i < n + 1 ∧ j < 9 then f ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

lemma F_mk {n : ℕ} (f : Fin (n + 1) → Fin 9 → Fin 4) (i : Fin (n + 1)) (j : Fin 9) :
    F f i j = f i j := by
  simp [F, i.isLt, j.isLt]

lemma blk_F {n : ℕ} (f : Fin (n + 1) → Fin 9 → Fin 4) (i : Fin n) (j : Fin 8) :
    blk f i j = {F f i j, F f i (j + 1), F f (i + 1) j, F f (i + 1) (j + 1)} := by
  simp only [blk, ← F_mk, Fin.val_castSucc, Fin.val_succ]

/-- Horizontally adjacent subblocks agree: in two consecutive rows the columns j and j + 2 carry
the same multiset. -/
def Hc {n : ℕ} (f : Fin (n + 1) → Fin 9 → Fin 4) : Prop :=
  ∀ i j : ℕ, i < n → j + 2 < 9 →
    ({F f i j, F f (i + 1) j} : Multiset (Fin 4)) = {F f i (j + 2), F f (i + 1) (j + 2)}

/-- Vertically adjacent subblocks agree: in two consecutive columns the rows i and i + 2 carry the
same multiset. -/
def Vc {n : ℕ} (f : Fin (n + 1) → Fin 9 → Fin 4) : Prop :=
  ∀ i j : ℕ, i + 1 < n → j + 1 < 9 →
    ({F f i j, F f i (j + 1)} : Multiset (Fin 4)) = {F f (i + 2) j, F f (i + 2) (j + 1)}

/-- Every row has period 2. -/
def RP {n : ℕ} (f : Fin (n + 1) → Fin 9 → Fin 4) : Prop :=
  ∀ i j : ℕ, i ≤ n → j + 2 < 9 → F f i j = F f i (j + 2)

/-- Every column has period 2. -/
def CP {n : ℕ} (f : Fin (n + 1) → Fin 9 → Fin 4) : Prop :=
  ∀ i j : ℕ, i + 1 < n → j < 9 → F f i j = F f (i + 2) j

/-- All 2 X 2 subblocks carry the same multiset. -/
def Valid {n : ℕ} (f : Fin (n + 1) → Fin 9 → Fin 4) : Prop :=
  ∀ i i' : Fin n, ∀ j j' : Fin 8, blk f i j = blk f i' j'

/-- The subblock multiset at natural-number indices. -/
def B {n : ℕ} (f : Fin (n + 1) → Fin 9 → Fin 4) (i j : ℕ) : Multiset (Fin 4) :=
  {F f i j, F f i (j + 1), F f (i + 1) j, F f (i + 1) (j + 1)}

lemma valid_iff {n : ℕ} (f : Fin (n + 1) → Fin 9 → Fin 4) : Valid f ↔ Hc f ∧ Vc f := by
  constructor
  · intro hv
    refine ⟨fun i j hi hj => ?_, fun i j hi hj => ?_⟩
    · have e := hv ⟨i, hi⟩ ⟨i, hi⟩ ⟨j, by omega⟩ ⟨j + 1, by omega⟩
      rw [blk_F, blk_F] at e
      exact canc_h _ _ _ _ _ _ e
    · have e := hv ⟨i, by omega⟩ ⟨i + 1, hi⟩ ⟨j, by omega⟩ ⟨j, by omega⟩
      rw [blk_F, blk_F] at e
      exact canc_v _ _ _ _ _ _ e
  · rintro ⟨hh, hvv⟩
    have hrow : ∀ i j, i < n → j < 8 → B f i j = B f i 0 := by
      intro i j hi hj
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [← ih (by omega)]
        exact (uncanc_h _ _ _ _ _ _ (hh i j hi (by omega))).symm
    have hcol : ∀ i, i < n → B f i 0 = B f 0 0 := by
      intro i hi
      induction i with
      | zero => rfl
      | succ i ih =>
        rw [← ih (by omega)]
        exact (uncanc_v _ _ _ _ _ _ (hvv i 0 hi (by omega))).symm
    intro i i' j j'
    rw [blk_F, blk_F]
    change B f i j = B f i' j'
    rw [hrow i j i.isLt j.isLt, hrow i' j' i'.isLt j'.isLt, hcol i i.isLt, hcol i' i'.isLt]

/-! ### The dichotomy: all rows or all columns have period 2 -/

/-- Row i has period 2. -/
def rp {n : ℕ} (f : Fin (n + 1) → Fin 9 → Fin 4) (i : ℕ) : Prop :=
  ∀ j, j + 2 < 9 → F f i j = F f i (j + 2)

lemma rp_succ {n : ℕ} {f : Fin (n + 1) → Fin 9 → Fin 4} (hh : Hc f) (i : ℕ) (hi : i < n) :
    rp f i ↔ rp f (i + 1) := by
  constructor
  · intro h j hj
    have e := hh i j hi hj
    rw [h j hj] at e
    exact pair_left _ _ _ e
  · intro h j hj
    have e := hh i j hi hj
    rw [h j hj] at e
    exact pair_right _ _ _ e

lemma rp_all {n : ℕ} {f : Fin (n + 1) → Fin 9 → Fin 4} (hh : Hc f) (i : ℕ) (hi : i ≤ n) :
    rp f 0 ↔ rp f i := by
  induction i with
  | zero => exact Iff.rfl
  | succ i ih => exact (ih (by omega)).trans (rp_succ hh i (by omega))

lemma v_lemma {n : ℕ} {f : Fin (n + 1) → Fin 9 → Fin 4} (hv : Vc f) (i : ℕ) (hi : i + 1 < n)
    (hnp : ¬ rp f i) : ∀ j, j < 9 → F f (i + 2) j = F f i j := by
  have hp : ∀ j, j + 1 < 9 →
      ({F f i j, F f i (j + 1)} : Multiset (Fin 4)) = {F f (i + 2) j, F f (i + 2) (j + 1)} :=
    fun j hj => hv i j hi hj
  by_cases h0 : F f (i + 2) 0 = F f i 0
  · intro j hj
    induction j with
    | zero => exact h0
    | succ j ih =>
      have e := hp j (by omega)
      rw [ih (by omega)] at e
      exact (pair_left _ _ _ e).symm
  · exfalso
    apply hnp
    have key : ∀ j, j + 1 < 9 → F f (i + 2) j = F f i (j + 1) ∧
        F f (i + 2) (j + 1) = F f i j ∧ F f i j ≠ F f i (j + 1) := by
      intro j hj
      induction j with
      | zero =>
        obtain ⟨e1, e2⟩ := pair_swap _ _ _ _ (hp 0 (by omega)) h0
        exact ⟨e1, e2, fun h => h0 (e1.trans h.symm)⟩
      | succ j ih =>
        obtain ⟨e1, e2, e3⟩ := ih (by omega)
        have e := hp (j + 1) hj
        rw [e2] at e
        obtain ⟨e4, e5⟩ := pair_swap _ _ _ _ e e3
        refine ⟨e2.trans e4, e5, fun h => e3 ?_⟩
        rw [e4]
        exact h.symm
    intro j hj
    have k1 := (key j (by omega)).2.1
    have k2 := (key (j + 1) (by omega)).1
    exact k1.symm.trans k2

lemma dichotomy {n : ℕ} {f : Fin (n + 1) → Fin 9 → Fin 4} (hh : Hc f) (hv : Vc f) :
    RP f ∨ CP f := by
  by_cases h : rp f 0
  · left
    intro i j hi hj
    exact (rp_all hh i hi).1 h j hj
  · right
    intro i j hi hj
    exact (v_lemma hv i hi (fun hr => h ((rp_all hh i (by omega)).2 hr)) j hj).symm

lemma RP_Hc {n : ℕ} {f : Fin (n + 1) → Fin 9 → Fin 4} (h : RP f) : Hc f := by
  intro i j hi hj
  rw [h i j (by omega) hj, h (i + 1) j (by omega) hj]

lemma CP_Vc {n : ℕ} {f : Fin (n + 1) → Fin 9 → Fin 4} (h : CP f) : Vc f := by
  intro i j hi hj
  rw [h i j hi (by omega), h i (j + 1) hi hj]

/-! ### Counting sequences of pairs whose multisets have period 2 -/

/-- The multiset of a pair. -/
def ms (p : Fin 4 × Fin 4) : Multiset (Fin 4) := {p.1, p.2}

/-- Sequences of pairs whose multisets agree at distance 2. -/
def per2 {K : ℕ} (g : Fin K → Fin 4 × Fin 4) : Prop :=
  ∀ i j : Fin K, j.val = i.val + 2 → ms (g i) = ms (g j)

instance {K : ℕ} : DecidablePred (@per2 K) := fun g => by unfold per2; infer_instance

/-- The pairs with the multiset of p. -/
def cls (p : Fin 4 × Fin 4) : Finset (Fin 4 × Fin 4) := univ.filter (fun p' => ms p' = ms p)

lemma cls_card : ∀ p : Fin 4 × Fin 4, (cls p).card = if p.1 = p.2 then 1 else 2 := by
  decide +kernel

/-- The entries allowed at position i once the first two entries are p0 and p1. -/
def tt {K : ℕ} (p0 p1 : Fin 4 × Fin 4) (i : Fin K) : Finset (Fin 4 × Fin 4) :=
  if i.val = 0 then {p0} else if i.val = 1 then {p1} else if i.val % 2 = 0 then cls p0 else cls p1

lemma per2_mod {K : ℕ} {g : Fin K → Fin 4 × Fin 4} (hg : per2 g) (h2 : 2 ≤ K) :
    ∀ i : Fin K, ms (g i) = ms (g ⟨i.val % 2, by omega⟩) := by
  intro i
  obtain ⟨i, hi⟩ := i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases h : i < 2
    · have e : (⟨i % 2, by omega⟩ : Fin K) = ⟨i, hi⟩ := Fin.ext (Nat.mod_eq_of_lt h)
      rw [e]
    · have e := hg ⟨i - 2, by omega⟩ ⟨i, hi⟩ (by simp; omega)
      rw [← e, ih (i - 2) (by omega) (by omega)]
      have e2 : (⟨(i - 2) % 2, by omega⟩ : Fin K) = ⟨i % 2, by omega⟩ := Fin.ext (by simp; omega)
      rw [e2]

lemma fiber_eq {K : ℕ} (h2 : 2 ≤ K) (p0 p1 : Fin 4 × Fin 4) :
    (univ.filter (fun g : Fin K → Fin 4 × Fin 4 => per2 g)).filter
      (fun g => (g ⟨0, by omega⟩, g ⟨1, by omega⟩) = (p0, p1)) =
      Fintype.piFinset (tt p0 p1) := by
  ext g
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, Prod.mk.injEq]
  constructor
  · rintro ⟨hp, e0, e1⟩ i
    have hm := per2_mod hp h2 i
    unfold tt
    split_ifs with c0 c1 c2
    · have : i = ⟨0, by omega⟩ := Fin.ext c0
      rw [this, e0]
      exact mem_singleton_self _
    · have : i = ⟨1, by omega⟩ := Fin.ext c1
      rw [this, e1]
      exact mem_singleton_self _
    · simp only [cls, mem_filter, mem_univ, true_and]
      have e : (⟨i.val % 2, by omega⟩ : Fin K) = ⟨0, by omega⟩ := Fin.ext (by simp [c2])
      rw [hm, e, e0]
    · simp only [cls, mem_filter, mem_univ, true_and]
      have e : (⟨i.val % 2, by omega⟩ : Fin K) = ⟨1, by omega⟩ := Fin.ext (by simp; omega)
      rw [hm, e, e1]
  · intro hg
    have h0 := hg ⟨0, by omega⟩
    have h1 := hg ⟨1, by omega⟩
    simp only [tt, if_true, mem_singleton] at h0
    simp only [tt, show (1 : ℕ) ≠ 0 by omega, if_false, if_true, mem_singleton] at h1
    refine ⟨fun i j hij => ?_, h0, h1⟩
    have hj := hg j
    have hi := hg i
    have pj : ms (g j) = ms (if j.val % 2 = 0 then p0 else p1) := by
      unfold tt at hj
      rw [if_neg (by omega), if_neg (by omega)] at hj
      split_ifs at hj ⊢ with c
      · simpa [cls] using hj
      · simpa [cls] using hj
    have pi : ms (g i) = ms (if i.val % 2 = 0 then p0 else p1) := by
      unfold tt at hi
      by_cases c0 : i.val = 0
      · rw [if_pos c0, mem_singleton] at hi
        rw [hi, if_pos (by omega)]
      · by_cases c1 : i.val = 1
        · rw [if_neg c0, if_pos c1, mem_singleton] at hi
          rw [hi, if_neg (by omega)]
        · rw [if_neg c0, if_neg c1] at hi
          by_cases c2 : i.val % 2 = 0
          · rw [if_pos c2] at hi
            rw [if_pos c2]
            simpa [cls] using hi
          · rw [if_neg c2] at hi
            rw [if_neg c2]
            simpa [cls] using hi
    rw [pi, pj, show j.val % 2 = i.val % 2 by omega]

lemma prod_range_par (c0 c1 : ℕ) : ∀ K, 2 ≤ K →
    ∏ m ∈ range K, (if m = 0 then 1 else if m = 1 then 1 else if m % 2 = 0 then c0 else c1) =
      c0 ^ ((K + 1) / 2 - 1) * c1 ^ (K / 2 - 1) := by
  intro K hK
  induction K with
  | zero => omega
  | succ K ih =>
    rcases Nat.lt_or_ge K 2 with h | h
    · interval_cases K
      · omega
      · simp [Finset.prod_range_succ]
    · rw [Finset.prod_range_succ, ih h, if_neg (by omega), if_neg (by omega)]
      rcases Nat.even_or_odd' K with ⟨t, rfl | rfl⟩
      · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
        rw [if_pos (by omega), show (2 * (s + 1) + 1) / 2 - 1 = s by omega,
          show 2 * (s + 1) / 2 - 1 = s by omega, show (2 * (s + 1) + 1 + 1) / 2 - 1 = s + 1 by omega]
        ring
      · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
        rw [if_neg (by omega), show (2 * (s + 1) + 1 + 1) / 2 - 1 = s + 1 by omega,
          show (2 * (s + 1) + 1) / 2 - 1 = s by omega,
          show (2 * (s + 1) + 1 + 1 + 1) / 2 - 1 = s + 1 by omega]
        ring

lemma prod_tt {K : ℕ} (h2 : 2 ≤ K) (p0 p1 : Fin 4 × Fin 4) :
    ∏ i : Fin K, (tt p0 p1 i).card =
      (cls p0).card ^ ((K + 1) / 2 - 1) * (cls p1).card ^ (K / 2 - 1) := by
  have e : ∀ i : Fin K, (tt p0 p1 i).card =
      (fun m : ℕ => if m = 0 then 1 else if m = 1 then 1 else
        if m % 2 = 0 then (cls p0).card else (cls p1).card) i.val := by
    intro i
    simp only [tt]
    split_ifs <;> simp
  rw [Finset.prod_congr rfl (fun i _ => e i), Fin.prod_univ_eq_prod_range
    (fun m : ℕ => if m = 0 then 1 else if m = 1 then 1 else
      if m % 2 = 0 then (cls p0).card else (cls p1).card) K]
  exact prod_range_par _ _ K h2

lemma sum_cls_pow (e : ℕ) : ∑ p : Fin 4 × Fin 4, (cls p).card ^ e = 4 + 12 * 2 ^ e := by
  have h : ∀ p : Fin 4 × Fin 4, (cls p).card ^ e = if p.1 = p.2 then 1 else 2 ^ e := by
    intro p
    rw [cls_card]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun p _ => h p), Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul, mul_one]
  have c1 : (univ.filter (fun p : Fin 4 × Fin 4 => p.1 = p.2)).card = 4 := by decide
  have c2 : (univ.filter (fun p : Fin 4 × Fin 4 => ¬ p.1 = p.2)).card = 12 := by decide
  rw [c1, c2]

/-- The number of sequences of K >= 2 pairs whose multisets have period 2. -/
lemma card_per2 {K : ℕ} (h2 : 2 ≤ K) :
    ((univ : Finset (Fin K → Fin 4 × Fin 4)).filter per2).card =
      (4 + 12 * 2 ^ ((K + 1) / 2 - 1)) * (4 + 12 * 2 ^ (K / 2 - 1)) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g => (g ⟨0, by omega⟩, g ⟨1, by omega⟩))
    (t := univ) (by simp)]
  have hf : ∀ q : (Fin 4 × Fin 4) × (Fin 4 × Fin 4),
      (((univ : Finset (Fin K → Fin 4 × Fin 4)).filter per2).filter
        (fun g => (g ⟨0, by omega⟩, g ⟨1, by omega⟩) = q)).card =
        (cls q.1).card ^ ((K + 1) / 2 - 1) * (cls q.2).card ^ (K / 2 - 1) := by
    rintro ⟨p0, p1⟩
    rw [fiber_eq h2 p0 p1, Fintype.card_piFinset, prod_tt h2]
  rw [Finset.sum_congr rfl (fun q _ => hf q), Fintype.sum_prod_type, ← sum_cls_pow,
    ← sum_cls_pow, Finset.sum_mul_sum]

/-! ### Arrays with rows of period 2, with columns of period 2, and with both -/

lemma RP_mod {n : ℕ} {f : Fin (n + 1) → Fin 9 → Fin 4} (h : RP f) (i : ℕ) (hi : i ≤ n) :
    ∀ j, j < 9 → F f i j = F f i (j % 2) := by
  intro j hj
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases h2 : j < 2
    · rw [Nat.mod_eq_of_lt h2]
    · have e := h i (j - 2) hi (by omega)
      rw [show j - 2 + 2 = j by omega] at e
      rw [← e, ih (j - 2) (by omega) (by omega), show (j - 2) % 2 = j % 2 by omega]

lemma CP_mod {n : ℕ} {f : Fin (n + 1) → Fin 9 → Fin 4} (h : CP f) (j : ℕ) (hj : j < 9) :
    ∀ i, i ≤ n → F f i j = F f (i % 2) j := by
  intro i hi
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases h2 : i < 2
    · rw [Nat.mod_eq_of_lt h2]
    · have e := h (i - 2) j (by omega) hj
      rw [show i - 2 + 2 = i by omega] at e
      rw [← e, ih (i - 2) (by omega) (by omega), show (i - 2) % 2 = i % 2 by omega]

/-- Rows of period 2 are determined by their first two entries. -/
def ofRows {n : ℕ} (g : Fin (n + 1) → Fin 4 × Fin 4) : Fin (n + 1) → Fin 9 → Fin 4 :=
  fun i j => if j.val % 2 = 0 then (g i).1 else (g i).2

/-- Columns of period 2 are determined by their first two entries. -/
def ofCols {n : ℕ} (h : Fin 9 → Fin 4 × Fin 4) : Fin (n + 1) → Fin 9 → Fin 4 :=
  fun i j => if i.val % 2 = 0 then (h j).1 else (h j).2

lemma F_ofRows {n : ℕ} (g : Fin (n + 1) → Fin 4 × Fin 4) (i j : ℕ) (hi : i ≤ n) (hj : j < 9) :
    F (ofRows g) i j = if j % 2 = 0 then (g ⟨i, by omega⟩).1 else (g ⟨i, by omega⟩).2 := by
  simp [F, ofRows, show i < n + 1 by omega, hj]

lemma F_ofCols {n : ℕ} (h : Fin 9 → Fin 4 × Fin 4) (i j : ℕ) (hi : i ≤ n) (hj : j < 9) :
    F (ofCols (n := n) h) i j = if i % 2 = 0 then (h ⟨j, hj⟩).1 else (h ⟨j, hj⟩).2 := by
  simp [F, ofCols, show i < n + 1 by omega, hj]

instance {n : ℕ} : DecidablePred (@Valid n) := fun f => by unfold Valid; infer_instance

open Classical in
lemma card_RV (n : ℕ) :
    ((univ : Finset (Fin (n + 1) → Fin 9 → Fin 4)).filter (fun f => RP f ∧ Vc f)).card =
      ((univ : Finset (Fin (n + 1) → Fin 4 × Fin 4)).filter per2).card := by
  refine Finset.card_bij' (fun f _ => fun i => (f i 0, f i 1)) (fun g _ => ofRows g) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf ⊢
    intro i j hij
    have e := hf.2 i.val 0 (by omega) (by omega)
    rw [show i.val + 2 = j.val by omega] at e
    simp only [ms]
    rw [← F_mk f i 0, ← F_mk f i 1, ← F_mk f j 0, ← F_mk f j 1]
    exact e
  · intro g hg
    simp only [mem_filter, mem_univ, true_and] at hg ⊢
    refine ⟨fun i j hi hj => ?_, fun i j hi hj => ?_⟩
    · rw [F_ofRows g i j hi (by omega), F_ofRows g i (j + 2) hi hj,
        show (j + 2) % 2 = j % 2 by omega]
    · rw [F_ofRows g i j (by omega) (by omega), F_ofRows g i (j + 1) (by omega) hj,
        F_ofRows g (i + 2) j (by omega) (by omega), F_ofRows g (i + 2) (j + 1) (by omega) hj]
      have e := hg ⟨i, by omega⟩ ⟨i + 2, by omega⟩ rfl
      simp only [ms] at e
      by_cases hj2 : j % 2 = 0
      · rw [if_pos hj2, if_neg (by omega), if_pos hj2, if_neg (by omega)]
        exact e
      · rw [if_neg hj2, if_pos (by omega), if_neg hj2, if_pos (by omega), pair_symm,
          pair_symm (g ⟨i + 2, _⟩).2]
        exact e
  · intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf
    funext i j
    have e := RP_mod hf.1 i.val (by omega) j.val j.isLt
    rw [F_mk] at e
    simp only [ofRows]
    rw [e]
    by_cases hj2 : j.val % 2 = 0
    · rw [if_pos hj2, hj2, ← F_mk f i 0]
      rfl
    · rw [if_neg hj2, show j.val % 2 = 1 by omega, ← F_mk f i 1]
      rfl
  · intro g _
    funext i
    simp [ofRows]

open Classical in
lemma card_CH (n : ℕ) (hn : 1 ≤ n) :
    ((univ : Finset (Fin (n + 1) → Fin 9 → Fin 4)).filter (fun f => CP f ∧ Hc f)).card =
      ((univ : Finset (Fin 9 → Fin 4 × Fin 4)).filter per2).card := by
  refine Finset.card_bij' (fun f _ => fun j => (f ⟨0, by omega⟩ j, f ⟨1, by omega⟩ j))
    (fun h _ => ofCols h) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf ⊢
    intro i j hij
    have e := hf.2 0 i.val (by omega) (by omega)
    rw [show i.val + 2 = j.val by omega] at e
    simp only [ms]
    rw [← F_mk f ⟨0, by omega⟩ i, ← F_mk f ⟨1, by omega⟩ i, ← F_mk f ⟨0, by omega⟩ j,
      ← F_mk f ⟨1, by omega⟩ j]
    exact e
  · intro h hh
    simp only [mem_filter, mem_univ, true_and] at hh ⊢
    refine ⟨fun i j hi hj => ?_, fun i j hi hj => ?_⟩
    · rw [F_ofCols h i j (by omega) hj, F_ofCols h (i + 2) j (by omega) hj,
        show (i + 2) % 2 = i % 2 by omega]
    · rw [F_ofCols h i j (by omega) (by omega), F_ofCols h (i + 1) j (by omega) (by omega),
        F_ofCols h i (j + 2) (by omega) hj, F_ofCols h (i + 1) (j + 2) (by omega) hj]
      have e := hh ⟨j, by omega⟩ ⟨j + 2, hj⟩ rfl
      simp only [ms] at e
      by_cases hi2 : i % 2 = 0
      · rw [if_pos hi2, if_neg (by omega), if_pos hi2, if_neg (by omega)]
        exact e
      · rw [if_neg hi2, if_pos (by omega), if_neg hi2, if_pos (by omega), pair_symm,
          pair_symm (h ⟨j + 2, hj⟩).2]
        exact e
  · intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf
    funext i j
    have e := CP_mod hf.1 j.val j.isLt i.val (by omega)
    rw [F_mk] at e
    simp only [ofCols]
    rw [e]
    by_cases hi2 : i.val % 2 = 0
    · rw [if_pos hi2, hi2, ← F_mk f ⟨0, by omega⟩ j]
    · rw [if_neg hi2, show i.val % 2 = 1 by omega, ← F_mk f ⟨1, by omega⟩ j]
  · intro h _
    funext j
    simp [ofCols]

open Classical in
lemma card_RC (n : ℕ) (hn : 1 ≤ n) :
    ((univ : Finset (Fin (n + 1) → Fin 9 → Fin 4)).filter (fun f => RP f ∧ CP f)).card = 256 := by
  have e : ((univ : Finset (Fin (n + 1) → Fin 9 → Fin 4)).filter (fun f => RP f ∧ CP f)).card =
      (univ : Finset (Fin 4 × Fin 4 × Fin 4 × Fin 4)).card := by
    refine Finset.card_bij'
      (fun (f : Fin (n + 1) → Fin 9 → Fin 4) _ => (f ⟨0, by omega⟩ 0, f ⟨0, by omega⟩ 1,
        f ⟨1, by omega⟩ 0, f ⟨1, by omega⟩ 1))
      (fun (x : Fin 4 × Fin 4 × Fin 4 × Fin 4) _ => fun (i : Fin (n + 1)) (j : Fin 9) =>
        if i.val % 2 = 0 then (if j.val % 2 = 0 then x.1 else x.2.1) else
        (if j.val % 2 = 0 then x.2.2.1 else x.2.2.2)) ?_ ?_ ?_ ?_
    · intro f _
      exact mem_univ _
    · intro x _
      simp only [mem_filter, mem_univ, true_and]
      refine ⟨fun i j hi hj => ?_, fun i j hi hj => ?_⟩
      · simp [F, show i < n + 1 by omega, show j < 9 by omega, hj, show (j + 2) % 2 = j % 2 by omega]
      · simp [F, show i < n + 1 by omega, show i + 2 < n + 1 by omega, hj,
          show (i + 2) % 2 = i % 2 by omega]
    · intro f hf
      simp only [mem_filter, mem_univ, true_and] at hf
      funext i j
      have e1 := RP_mod hf.1 i.val (by omega) j.val j.isLt
      have e2 := CP_mod hf.2 (j.val % 2) (by omega) i.val (by omega)
      rw [F_mk] at e1
      rw [e1, e2]
      have q : ∀ a b : ℕ, (ha : a ≤ 1) → (hb : b ≤ 1) →
          F f a b = f ⟨a, by omega⟩ ⟨b, by omega⟩ := by
        intro a b ha hb
        simp [F, show a < n + 1 by omega, show b < 9 by omega]
      have hi2 : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
      have hj2 : j.val % 2 = 0 ∨ j.val % 2 = 1 := by omega
      rcases hi2 with hi2 | hi2 <;> rcases hj2 with hj2 | hj2 <;>
        rw [hi2, hj2, q _ _ (by norm_num) (by norm_num)] <;> simp <;> rfl
    · intro x _
      simp
  rw [e]
  simp [Finset.card_univ]

open Classical in
/-- The number of (n+1) X 9 arrays with all subblocks carrying the same multiset. -/
lemma count (n : ℕ) (hn : 1 ≤ n) :
    ((univ : Finset (Fin (n + 1) → Fin 9 → Fin 4)).filter Valid).card + 256 =
      (4 + 12 * 2 ^ ((n + 1 + 1) / 2 - 1)) * (4 + 12 * 2 ^ ((n + 1) / 2 - 1)) +
      (4 + 12 * 2 ^ ((9 + 1) / 2 - 1)) * (4 + 12 * 2 ^ (9 / 2 - 1)) := by
  have hU : ((univ : Finset (Fin (n + 1) → Fin 9 → Fin 4)).filter Valid) =
      ((univ : Finset (Fin (n + 1) → Fin 9 → Fin 4)).filter (fun f => RP f ∧ Vc f)) ∪
      ((univ : Finset (Fin (n + 1) → Fin 9 → Fin 4)).filter (fun f => CP f ∧ Hc f)) := by
    ext f
    simp only [mem_filter, mem_univ, true_and, mem_union, valid_iff]
    constructor
    · rintro ⟨hh, hv⟩
      rcases dichotomy hh hv with h | h
      · exact Or.inl ⟨h, hv⟩
      · exact Or.inr ⟨h, hh⟩
    · rintro (⟨h, hv⟩ | ⟨h, hh⟩)
      · exact ⟨RP_Hc h, hv⟩
      · exact ⟨hh, CP_Vc h⟩
  have hI : ((univ : Finset (Fin (n + 1) → Fin 9 → Fin 4)).filter (fun f => RP f ∧ Vc f)) ∩
      ((univ : Finset (Fin (n + 1) → Fin 9 → Fin 4)).filter (fun f => CP f ∧ Hc f)) =
      ((univ : Finset (Fin (n + 1) → Fin 9 → Fin 4)).filter (fun f => RP f ∧ CP f)) := by
    ext f
    simp only [mem_filter, mem_univ, true_and, mem_inter]
    constructor
    · rintro ⟨⟨h1, _⟩, h2, _⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, CP_Vc h2⟩, h2, RP_Hc h1⟩
  rw [hU, ← card_RC n hn, ← hI, Finset.card_union_add_card_inter, card_RV, card_CH n hn,
    card_per2 (by omega), card_per2 (by omega)]

/-! ### The closed forms, the recurrence and the generating function -/

lemma a_valid (n : ℕ) : a n = ((univ : Finset (Fin (n + 1) → Fin 9 → Fin 4)).filter Valid).card / 16 :=
  rfl

lemma closed_even' (t : ℕ) : a (2 * (t + 1)) = 9 * 2 ^ t + 9 * 2 ^ (2 * t + 1) + 1210 := by
  have h := count (2 * (t + 1)) (by omega)
  rw [show (2 * (t + 1) + 1 + 1) / 2 - 1 = t + 1 by omega,
    show (2 * (t + 1) + 1) / 2 - 1 = t by omega] at h
  rw [a_valid]
  have e : ((univ : Finset (Fin (2 * (t + 1) + 1) → Fin 9 → Fin 4)).filter Valid).card =
      16 * (9 * 2 ^ t + 9 * 2 ^ (2 * t + 1) + 1210) := by
    generalize ((univ : Finset (Fin (2 * (t + 1) + 1) → Fin 9 → Fin 4)).filter Valid).card = c at h
    rw [show (2 : ℕ) ^ (t + 1) = 2 * 2 ^ t by ring] at h
    rw [show (2 : ℕ) ^ (2 * t + 1) = 2 * (2 ^ t * 2 ^ t) by ring]
    norm_num at h
    nlinarith [h]
  rw [e, Nat.mul_div_cancel_left _ (by norm_num)]

lemma closed_odd' (t : ℕ) : a (2 * t + 1) = 9 * 2 ^ (2 * t) + 3 * 2 ^ (t + 1) + 1210 := by
  have h := count (2 * t + 1) (by omega)
  rw [show (2 * t + 1 + 1 + 1) / 2 - 1 = t by omega,
    show (2 * t + 1 + 1) / 2 - 1 = t by omega] at h
  rw [a_valid]
  have e : ((univ : Finset (Fin (2 * t + 1 + 1) → Fin 9 → Fin 4)).filter Valid).card =
      16 * (9 * 2 ^ (2 * t) + 3 * 2 ^ (t + 1) + 1210) := by
    generalize ((univ : Finset (Fin (2 * t + 1 + 1) → Fin 9 → Fin 4)).filter Valid).card = c at h
    rw [show (2 : ℕ) ^ (2 * t) = 2 ^ t * 2 ^ t by ring, show (2 : ℕ) ^ (t + 1) = 2 * 2 ^ t by ring]
    norm_num at h
    nlinarith [h]
  rw [e, Nat.mul_div_cancel_left _ (by norm_num)]

/-- Barker's closed form for even n. -/
theorem closed_even : ∀ n : ℕ, 1 ≤ n → n % 2 = 0 → a n = 9 * 2 ^ (n / 2 - 1) + 9 * 2 ^ (n - 1) + 1210 := by
  intro n hn he
  obtain ⟨t, rfl⟩ : ∃ t, n = 2 * (t + 1) := ⟨n / 2 - 1, by omega⟩
  rw [closed_even' t, show 2 * (t + 1) / 2 - 1 = t by omega, show 2 * (t + 1) - 1 = 2 * t + 1 by omega]

/-- Barker's closed form for odd n. -/
theorem closed_odd : ∀ n : ℕ, n % 2 = 1 → a n = 9 * 2 ^ (n - 1) + 3 * 2 ^ ((n + 1) / 2) + 1210 := by
  intro n ho
  obtain ⟨t, rfl⟩ : ∃ t, n = 2 * t + 1 := ⟨n / 2, by omega⟩
  rw [closed_odd' t, show 2 * t + 1 - 1 = 2 * t by omega, show (2 * t + 1 + 1) / 2 = t + 1 by omega]

/-- a(n + 4) = 3 a(n + 3) - 6 a(n + 1) + 4 a(n) for n >= 1. -/
lemma a_rec (n : ℕ) (hn : 1 ≤ n) :
    (a (n + 4) : ℤ) = 3 * a (n + 3) - 6 * a (n + 1) + 4 * a n := by
  rcases Nat.even_or_odd' n with ⟨t, rfl | rfl⟩
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    rw [show 2 * (s + 1) + 4 = 2 * (s + 2 + 1) by ring, show 2 * (s + 1) + 3 = 2 * (s + 2) + 1 by ring,
      closed_even' (s + 2), closed_odd' (s + 2), closed_odd' (s + 1), closed_even' s]
    push_cast
    ring
  · rw [show 2 * t + 1 + 4 = 2 * (t + 2) + 1 by ring, show 2 * t + 1 + 3 = 2 * (t + 1 + 1) by ring,
      show 2 * t + 1 + 1 = 2 * (t + 1) by ring, closed_odd' (t + 2), closed_even' (t + 1),
      closed_even' t, closed_odd' t]
    push_cast
    ring

lemma a_one : a 1 = 1225 := by rw [closed_odd 1 (by norm_num)]; norm_num
lemma a_two : a 2 = 1237 := by rw [closed_even 2 (by norm_num) (by norm_num)]; norm_num
lemma a_three : a 3 = 1258 := by rw [closed_odd 3 (by norm_num)]; norm_num
lemma a_four : a 4 = 1300 := by rw [closed_even 4 (by norm_num) (by norm_num)]; norm_num

/-- Barker's g.f.: Sum_{n >= 1} a(n) x^n = x(1225 - 2438x - 2453x^2 + 4876x^3)/((1 - x)(1 - 2x)(1 - 2x^2)). -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 2 * X) * (1 - 2 * X ^ 2)) =
      X * (1225 - 2438 * X - 2453 * X ^ 2 + 4876 * X ^ 3) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) * (1 - 2 * X) * (1 - 2 * X ^ 2)) =
      A - A * X ^ 1 * C 3 + A * X ^ 3 * C 6 - A * X ^ 4 * C 4 := by
    rw [show (C (3 : ℚ) : ℚ⟦X⟧) = 3 from map_ofNat C 3, show (C (6 : ℚ) : ℚ⟦X⟧) = 6 from map_ofNat C 6,
      show (C (4 : ℚ) : ℚ⟦X⟧) = 4 from map_ofNat C 4]
    ring
  have e2 : (X * (1225 - 2438 * X - 2453 * X ^ 2 + 4876 * X ^ 3) : ℚ⟦X⟧) =
      X ^ 1 * C 1225 - X ^ 2 * C 2438 - X ^ 3 * C 2453 + X ^ 4 * C 4876 := by
    rw [show (C (1225 : ℚ) : ℚ⟦X⟧) = 1225 from map_ofNat C 1225,
      show (C (2438 : ℚ) : ℚ⟦X⟧) = 2438 from map_ofNat C 2438,
      show (C (2453 : ℚ) : ℚ⟦X⟧) = 2453 from map_ofNat C 2453,
      show (C (4876 : ℚ) : ℚ⟦X⟧) = 4876 from map_ofNat C 4876]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk]
  rcases n with _ | _ | _ | _ | _ | n
  · simp
  · simp [a_one]
  · simp [a_one, a_two] <;> norm_num
  · simp [a_one, a_two, a_three] <;> norm_num
  · simp [a_one, a_two, a_three, a_four] <;> norm_num
  · have hq : ((a (n + 5) : ℕ) : ℚ) = 3 * a (n + 4) - 6 * a (n + 2) + 4 * a (n + 1) := by
      have := a_rec (n + 1) (by omega)
      exact_mod_cast this
    simp only [if_false, if_true, show ¬ (n + 5 = 0) by omega, show 1 ≤ n + 5 by omega,
      show 3 ≤ n + 5 by omega, show 4 ≤ n + 5 by omega, show n + 5 - 1 = n + 4 by omega,
      show n + 5 - 3 = n + 2 by omega, show n + 5 - 4 = n + 1 by omega,
      show ¬ (n + 4 = 0) by omega, show ¬ (n + 2 = 0) by omega, show ¬ (n + 1 = 0) by omega,
      show ¬ (n + 5 = 1) by omega, show ¬ (n + 5 = 2) by omega, show ¬ (n + 5 = 3) by omega,
      show ¬ (n + 5 = 4) by omega]
    linear_combination hq

/-- Barker's three conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 2 * X) * (1 - 2 * X ^ 2)) =
      X * (1225 - 2438 * X - 2453 * X ^ 2 + 4876 * X ^ 3) ∧
    (∀ n : ℕ, 1 ≤ n → n % 2 = 0 → a n = 9 * 2 ^ (n / 2 - 1) + 9 * 2 ^ (n - 1) + 1210) ∧
    (∀ n : ℕ, n % 2 = 1 → a n = 9 * 2 ^ (n - 1) + 3 * 2 ^ ((n + 1) / 2) + 1210) :=
  ⟨gf, closed_even, closed_odd⟩

/-- Controls: the entry's terms a(1..12). -/
theorem controls : a 1 = 1225 ∧ a 2 = 1237 ∧ a 3 = 1258 ∧ a 4 = 1300 ∧ a 5 = 1378 ∧ a 6 = 1534 ∧ a 7 = 1834 ∧ a 8 = 2434 ∧ a 9 = 3610 ∧ a 10 = 5962 ∧ a 11 = 10618 ∧ a 12 = 19930 :=
  ⟨by rw [closed_odd 1 (by norm_num)]; norm_num,
    by rw [closed_even 2 (by norm_num) (by norm_num)]; norm_num,
    by rw [closed_odd 3 (by norm_num)]; norm_num,
    by rw [closed_even 4 (by norm_num) (by norm_num)]; norm_num,
    by rw [closed_odd 5 (by norm_num)]; norm_num,
    by rw [closed_even 6 (by norm_num) (by norm_num)]; norm_num,
    by rw [closed_odd 7 (by norm_num)]; norm_num,
    by rw [closed_even 8 (by norm_num) (by norm_num)]; norm_num,
    by rw [closed_odd 9 (by norm_num)]; norm_num,
    by rw [closed_even 10 (by norm_num) (by norm_num)]; norm_num,
    by rw [closed_odd 11 (by norm_num)]; norm_num,
    by rw [closed_even 12 (by norm_num) (by norm_num)]; norm_num⟩

end OMA.S_oeis_a184038

theorem OMA.solution : type_of% @OMA.S_oeis_a184038.main :=
  OMA.S_oeis_a184038.conjecture
