import OMAStatements.S_oeis_a163824
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Tactic

namespace OEISA163824Proof

open Finset BigOperators

/-! ## Section 1: Generic interval inclusion-exclusion -/

lemma card_biUnion_interval {α : Type*} [DecidableEq α] (m : ℕ) (F : ℕ → Finset α)
    (hint : ∀ x a b c, a ≤ b → b ≤ c → c < m → x ∈ F a → x ∈ F c → x ∈ F b) :
    ((Finset.range m).biUnion F).card + ∑ i ∈ Finset.range (m - 1), (F i ∩ F (i + 1)).card =
      ∑ i ∈ Finset.range m, (F i).card := by
  induction m with
  | zero => simp
  | succ m ih =>
    cases m with
    | zero => simp
    | succ k =>
      have hint' : ∀ x a b c, a ≤ b → b ≤ c → c < k + 1 → x ∈ F a → x ∈ F c → x ∈ F b :=
        fun x a b c hab hbc hc ha hc' => hint x a b c hab hbc (by omega) ha hc'
      have hih := ih hint'
      have h_inter : ((Finset.range (k + 1)).biUnion F) ∩ F (k + 1) = F k ∩ F (k + 1) := by
        ext x
        simp only [mem_inter, mem_biUnion, mem_range]
        constructor
        · rintro ⟨⟨a, ha, hxa⟩, hxk⟩
          exact ⟨hint x a k (k + 1) (by omega) (by omega) (by omega) hxa hxk, hxk⟩
        · rintro ⟨hxk, hxk1⟩
          exact ⟨⟨k, by omega, hxk⟩, hxk1⟩
      have h_union : (Finset.range (k + 2)).biUnion F =
          (Finset.range (k + 1)).biUnion F ∪ F (k + 1) := by
        rw [Finset.range_add_one, Finset.biUnion_insert, Finset.union_comm]
      have h_cu := Finset.card_union_add_card_inter ((Finset.range (k + 1)).biUnion F) (F (k + 1))
      rw [h_inter] at h_cu
      rw [h_union]
      have h_sum1 : ∑ i ∈ Finset.range (k + 1 + 1 - 1), (F i ∩ F (i + 1)).card =
          (∑ i ∈ Finset.range k, (F i ∩ F (i + 1)).card) + (F k ∩ F (k + 1)).card := by
        have : k + 1 + 1 - 1 = k + 1 := by omega
        rw [this, Finset.sum_range_succ]
      have h_sum2 : ∑ i ∈ Finset.range (k + 1 + 1), (F i).card =
          (∑ i ∈ Finset.range (k + 1), (F i).card) + (F (k + 1)).card := by
        rw [Finset.sum_range_succ]
      simp only [Nat.add_sub_cancel] at hih
      omega

/-! ## Section 2: Double-chevron gridding predicates, symmetries, and interval properties -/

/-- Gridding predicate with `ℕ` dividers `c` and `r`. -/
def IsGrid {n : ℕ} (c r : ℕ) (p : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j : Fin n, i < j →
    (i.val < c ↔ j.val < c) →
    ((p i).val < r ↔ (p j).val < r) →
    (p i < p j ↔ r ≤ (p i).val)

lemma hasDoubleChevronGridding_iff {n : ℕ} (p : Equiv.Perm (Fin n)) :
    OMA.S_oeis_a163824.HasDoubleChevronGridding p ↔
      ∃ c ∈ Finset.range (n + 1), ∃ r ∈ Finset.range (n + 1), IsGrid c r p := by
  constructor
  · rintro ⟨c, r, h⟩
    exact ⟨c.val, Finset.mem_range.mpr c.isLt, r.val, Finset.mem_range.mpr r.isLt, h⟩
  · rintro ⟨c, hc, r, hr, h⟩
    exact ⟨⟨c, Finset.mem_range.mp hc⟩, ⟨r, Finset.mem_range.mp hr⟩, h⟩

/-- Vertical reflection of a permutation: `i ↦ Fin.rev (p i)`. -/
def revVal {n : ℕ} (p : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  p.trans Fin.revPerm

lemma revVal_apply {n : ℕ} (p : Equiv.Perm (Fin n)) (i : Fin n) :
    revVal p i = Fin.rev (p i) := rfl

lemma revVal_revVal {n : ℕ} (p : Equiv.Perm (Fin n)) : revVal (revVal p) = p := by
  ext i
  simp [revVal_apply]

lemma isGrid_revVal_iff {n : ℕ} (c r : ℕ) (hr : r ≤ n) (p : Equiv.Perm (Fin n)) :
    IsGrid c (n - r) (revVal p) ↔ IsGrid c r p := by
  have hrev_lt : ∀ x : Fin n, (Fin.rev x).val < n - r ↔ r ≤ x.val := by
    intro x
    rw [Fin.val_rev]
    omega
  have hrev_le : ∀ x : Fin n, n - r ≤ (Fin.rev x).val ↔ x.val < r := by
    intro x
    rw [Fin.val_rev]
    omega
  constructor
  · intro h i j hij hcol hrow
    have hrow' : (revVal p i).val < n - r ↔ (revVal p j).val < n - r := by
      simp only [revVal_apply, hrev_lt]
      omega
    have h1 := h i j hij hcol hrow'
    simp only [revVal_apply, Fin.rev_lt_rev, hrev_le] at h1
    have hne : p i ≠ p j := fun heq => absurd (p.injective heq) (ne_of_lt hij)
    have hne_lt : p j < p i ↔ ¬ p i < p j :=
      ⟨fun hlt => not_lt_of_gt hlt, fun hnot => lt_of_le_of_ne (le_of_not_gt hnot) hne.symm⟩
    rw [hne_lt] at h1
    constructor
    · intro hlt
      by_contra hnot
      have : (p i).val < r := by omega
      exact (h1.mpr this) hlt
    · intro hle
      by_contra hnot
      have : (p i).val < r := h1.mp hnot
      omega
  · intro h i j hij hcol hrow
    simp only [revVal_apply, hrev_lt] at hrow
    have hrow' : (p i).val < r ↔ (p j).val < r := by omega
    have h1 := h i j hij hcol hrow'
    simp only [revVal_apply, Fin.rev_lt_rev, hrev_le]
    have hne : p i ≠ p j := fun heq => absurd (p.injective heq) (ne_of_lt hij)
    have hne_lt : p j < p i ↔ ¬ p i < p j :=
      ⟨fun hlt => not_lt_of_gt hlt, fun hnot => lt_of_le_of_ne (le_of_not_gt hnot) hne.symm⟩
    rw [hne_lt]
    constructor
    · intro hnot
      by_contra hle
      have : r ≤ (p i).val := by omega
      exact hnot (h1.mpr this)
    · intro hlt hpi
      have : r ≤ (p i).val := h1.mp hpi
      omega

/-- Row-divider interval property for fixed column divider `c`. -/
lemma isGrid_row_interval {n : ℕ} {c r₁ r r₂ : ℕ} {p : Equiv.Perm (Fin n)}
    (hr₁ : r₁ ≤ r) (hr₂ : r ≤ r₂) (h1 : IsGrid c r₁ p) (h2 : IsGrid c r₂ p) :
    IsGrid c r p := by
  intro i j hij hcol hrow
  by_cases hpi : r ≤ (p i).val
  · have hpj : r ≤ (p j).val := by omega
    have hrow1 : (p i).val < r₁ ↔ (p j).val < r₁ := by omega
    have hlt := (h1 i j hij hcol hrow1).mpr (by omega)
    exact ⟨fun _ => hpi, fun _ => hlt⟩
  · have hpj : (p j).val < r := by omega
    have hrow2 : (p i).val < r₂ ↔ (p j).val < r₂ := by omega
    have hnot : ¬ (p i < p j) := by
      intro hlt
      have := (h2 i j hij hcol hrow2).mp hlt
      omega
    exact ⟨fun hlt => absurd hlt hnot, fun hle => absurd hle hpi⟩

/-- Helper for column-divider interval property when `r₁ ≤ r₂`. -/
lemma isGrid_col_interval_le {n : ℕ} {c₁ c c₂ r₁ r₂ : ℕ} {p : Equiv.Perm (Fin n)}
    (hc₁ : c₁ < c) (hc₂ : c < c₂) (hr : r₁ ≤ r₂) (hr₂ : r₂ ≤ n)
    (h1 : IsGrid c₁ r₁ p) (h2 : IsGrid c₂ r₂ p) :
    ∃ r ≤ n, IsGrid c r p := by
  -- At most one element in [c₁, c₂) has value in [r₁, r₂)
  have h_uniq : ∀ a b : Fin n,
      c₁ ≤ a.val → a.val < c₂ → r₁ ≤ (p a).val → (p a).val < r₂ →
      c₁ ≤ b.val → b.val < c₂ → r₁ ≤ (p b).val → (p b).val < r₂ → a = b := by
    intro a b ha1 ha2 hpa1 hpa2 hb1 hb2 hpb1 hpb2
    by_contra hne
    rcases lt_or_gt_of_ne hne with hab | hba
    · have hlt : p a < p b := (h1 a b hab (by omega) (by omega)).mpr hpa1
      have hgt : ¬ (p a < p b) := fun h => by
        have := (h2 a b hab (by omega) (by omega)).mp h; omega
      exact hgt hlt
    · have hlt : p b < p a := (h1 b a hba (by omega) (by omega)).mpr hpb1
      have hgt : ¬ (p b < p a) := fun h => by
        have := (h2 b a hba (by omega) (by omega)).mp h; omega
      exact hgt hlt
  by_cases hex : ∃ k : Fin n, c₁ ≤ k.val ∧ k.val < c ∧ r₁ ≤ (p k).val ∧ (p k).val < r₂
  · rcases hex with ⟨k, hk1, hk2, hpk1, hpk2⟩
    refine ⟨(p k).val + 1, by omega, ?_⟩
    intro i j hij hcol hrow
    have hlt_val : i.val < j.val := hij
    by_cases hic : i.val < c
    · have hjc : j.val < c := hcol.mp hic
      by_cases hpi : (p k).val + 1 ≤ (p i).val
      · have hpj : (p k).val + 1 ≤ (p j).val := by omega
        constructor
        · intro _; exact hpi
        · intro _
          by_cases hj1 : j.val < c₁
          · exact (h1 i j hij (by omega) (by omega)).mpr (by omega)
          · have h_notM : ¬ (r₁ ≤ (p j).val ∧ (p j).val < r₂) := by
              intro ⟨hm1, hm2⟩
              have hjk : j = k := h_uniq j k (by omega) (by omega) hm1 hm2 hk1 (by omega) hpk1 hpk2
              subst hjk; omega
            have hpj2 : r₂ ≤ (p j).val := by omega
            by_cases hpi2 : r₂ ≤ (p i).val
            · exact (h2 i j hij (by omega) (by omega)).mpr hpi2
            · exact Fin.lt_def.mpr (by omega)
      · have hpj : (p j).val < (p k).val + 1 := by omega
        have hlt2 : ¬ (p i < p j) := fun hlt => by
          have := (h2 i j hij (by omega) (by omega)).mp hlt
          omega
        exact ⟨fun hlt => absurd hlt hlt2, fun hle => absurd hle hpi⟩
    · have hjc : ¬ (j.val < c) := fun hj => hic (hcol.mpr hj)
      by_cases hpi : (p k).val + 1 ≤ (p i).val
      · have hpj : (p k).val + 1 ≤ (p j).val := by omega
        exact ⟨fun _ => hpi, fun _ => (h1 i j hij (by omega) (by omega)).mpr (by omega)⟩
      · have hpj : (p j).val < (p k).val + 1 := by omega
        have hlt2 : ¬ (p i < p j) := by
          intro hlt
          by_cases hi2 : c₂ ≤ i.val
          · have := (h2 i j hij (by omega) (by omega)).mp hlt
            omega
          · have h_notMi : ¬ (r₁ ≤ (p i).val ∧ (p i).val < r₂) := by
              intro ⟨hm1, hm2⟩
              have hik : i = k := h_uniq i k (by omega) (by omega) hm1 hm2 hk1 (by omega) hpk1 hpk2
              subst hik; omega
            have hpi1 : (p i).val < r₁ := by omega
            have hpj1 : (p j).val < r₁ := by
              by_contra hge
              have hkj : k < j := Fin.lt_def.mpr (by omega)
              have hlt_kj : p k < p j := (h1 k j hkj (by omega) (by omega)).mpr hpk1
              have : (p k).val < (p j).val := hlt_kj
              omega
            have := (h1 i j hij (by omega) (by omega)).mp hlt
            omega
        exact ⟨fun hlt => absurd hlt hlt2, fun hle => absurd hle hpi⟩
  · push Not at hex
    refine ⟨r₁, by omega, ?_⟩
    intro i j hij hcol hrow
    have hlt_val : i.val < j.val := hij
    by_cases hic : i.val < c
    · have hjc : j.val < c := hcol.mp hic
      by_cases hpi : r₁ ≤ (p i).val
      · have hpj : r₁ ≤ (p j).val := by omega
        constructor
        · intro _; exact hpi
        · intro _
          by_cases hj1 : j.val < c₁
          · exact (h1 i j hij (by omega) (by omega)).mpr hpi
          · have hpj2 : r₂ ≤ (p j).val := hex j (by omega) hjc hpj
            by_cases hpi2 : r₂ ≤ (p i).val
            · exact (h2 i j hij (by omega) (by omega)).mpr hpi2
            · exact Fin.lt_def.mpr (by omega)
      · have hpj : (p j).val < r₁ := by omega
        have hnot : ¬ (p i < p j) := fun hlt => by
          have := (h2 i j hij (by omega) (by omega)).mp hlt
          omega
        exact ⟨fun hlt => absurd hlt hnot, fun hle => absurd hle hpi⟩
    · have hjc : ¬ (j.val < c) := fun hj => hic (hcol.mpr hj)
      exact h1 i j hij (by omega) hrow

/-- Full column-divider interval property. -/
lemma isGrid_col_interval {n : ℕ} {c₁ c c₂ r₁ r₂ : ℕ} {p : Equiv.Perm (Fin n)}
    (hc₁ : c₁ ≤ c) (hc₂ : c ≤ c₂) (hr₁ : r₁ ≤ n) (hr₂ : r₂ ≤ n)
    (h1 : IsGrid c₁ r₁ p) (h2 : IsGrid c₂ r₂ p) :
    ∃ r ≤ n, IsGrid c r p := by
  by_cases h_eq1 : c₁ = c
  · subst h_eq1; exact ⟨r₁, hr₁, h1⟩
  by_cases h_eq2 : c = c₂
  · subst h_eq2; exact ⟨r₂, hr₂, h2⟩
  have hlt1 : c₁ < c := lt_of_le_of_ne hc₁ h_eq1
  have hlt2 : c < c₂ := lt_of_le_of_ne hc₂ h_eq2
  rcases le_total r₁ r₂ with hle | hle
  · exact isGrid_col_interval_le hlt1 hlt2 hle hr₂ h1 h2
  · have h1' : IsGrid c₁ (n - r₁) (revVal p) := (isGrid_revVal_iff c₁ r₁ hr₁ p).mpr h1
    have h2' : IsGrid c₂ (n - r₂) (revVal p) := (isGrid_revVal_iff c₂ r₂ hr₂ p).mpr h2
    rcases isGrid_col_interval_le hlt1 hlt2 (by omega) (by omega) h1' h2' with ⟨r', hr', h'⟩
    refine ⟨n - r', by omega, ?_⟩
    have h'' : IsGrid c (n - (n - r')) (revVal p) := by
      have : n - (n - r') = r' := by omega
      rwa [this]
    exact (isGrid_revVal_iff c (n - r') (by omega) p).mp h''

/-- Helper for common row divider on adjacent columns when `r₁ ≤ r₂`. -/
lemma common_row_adj_col_le {n : ℕ} {c r₁ r₂ : ℕ} {p : Equiv.Perm (Fin n)}
    (hc : c < n) (hr : r₁ ≤ r₂) (hr₂ : r₂ ≤ n)
    (h1 : IsGrid c r₁ p) (h2 : IsGrid (c + 1) r₂ p) :
    ∃ r ≤ n, IsGrid c r p ∧ IsGrid (c + 1) r p := by
  let v := (p ⟨c, hc⟩).val
  by_cases hv1 : v < r₁
  · refine ⟨r₁, by omega, h1, ?_⟩
    intro i j hij hcol hrow
    have hlt_val : i.val < j.val := hij
    by_cases hjc : j.val = c
    · have hjeq : j = ⟨c, hc⟩ := Fin.ext hjc
      have hpj : (p j).val < r₁ := by rw [hjeq]; exact hv1
      have hpi : (p i).val < r₁ := hrow.mpr hpj
      have hnot : ¬ (p i < p j) := fun hlt => by
        have := (h2 i j hij (by omega) (by omega)).mp hlt
        omega
      exact ⟨fun hlt => absurd hlt hnot, fun hle => absurd hle (by omega)⟩
    · exact h1 i j hij (by omega) hrow
  · by_cases hv2 : r₂ ≤ v
    · refine ⟨r₂, hr₂, ?_, h2⟩
      intro i j hij hcol hrow
      have hlt_val : i.val < j.val := hij
      by_cases hic : i.val = c
      · have hieq : i = ⟨c, hc⟩ := Fin.ext hic
        have hpi : r₂ ≤ (p i).val := by rw [hieq]; exact hv2
        have hpj : r₂ ≤ (p j).val := by omega
        have hlt : p i < p j := (h1 i j hij (by omega) (by omega)).mpr (by omega)
        exact ⟨fun _ => hpi, fun _ => hlt⟩
      · exact h2 i j hij (by omega) hrow
    · refine ⟨v + 1, by omega, ?_, ?_⟩
      · intro i j hij hcol hrow
        have hlt_val : i.val < j.val := hij
        by_cases hpi : v + 1 ≤ (p i).val
        · have hpj : v + 1 ≤ (p j).val := by omega
          exact ⟨fun _ => hpi, fun _ => (h1 i j hij hcol (by omega)).mpr (by omega)⟩
        · have hpj : (p j).val < v + 1 := by omega
          have hnot : ¬ (p i < p j) := by
            intro hlt
            by_cases hic : i.val = c
            · have hieq : i = ⟨c, hc⟩ := Fin.ext hic
              have hval_lt : (p i).val < (p j).val := hlt
              rw [hieq] at hval_lt
              change v < (p j).val at hval_lt
              omega
            · have := (h2 i j hij (by omega) (by omega)).mp hlt
              omega
          exact ⟨fun hlt => absurd hlt hnot, fun hle => absurd hle hpi⟩
      · intro i j hij hcol hrow
        have hlt_val : i.val < j.val := hij
        by_cases hpi : v + 1 ≤ (p i).val
        · have hpj : v + 1 ≤ (p j).val := by omega
          have hjne : j.val ≠ c := by
            intro hjc
            have : j = ⟨c, hc⟩ := Fin.ext hjc
            rw [this] at hpj
            change v + 1 ≤ v at hpj
            omega
          have hine : i.val ≠ c := by
            intro hic
            have : i = ⟨c, hc⟩ := Fin.ext hic
            rw [this] at hpi
            change v + 1 ≤ v at hpi
            omega
          exact ⟨fun _ => hpi, fun _ => (h1 i j hij (by omega) (by omega)).mpr (by omega)⟩
        · have hpj : (p j).val < v + 1 := by omega
          have hnot : ¬ (p i < p j) := fun hlt => by
            have := (h2 i j hij hcol (by omega)).mp hlt
            omega
          exact ⟨fun hlt => absurd hlt hnot, fun hle => absurd hle hpi⟩

/-- Full common row divider lemma for adjacent columns `c` and `c + 1`. -/
lemma common_row_adj_col {n : ℕ} {c r₁ r₂ : ℕ} {p : Equiv.Perm (Fin n)}
    (hc : c < n) (hr₁ : r₁ ≤ n) (hr₂ : r₂ ≤ n)
    (h1 : IsGrid c r₁ p) (h2 : IsGrid (c + 1) r₂ p) :
    ∃ r ≤ n, IsGrid c r p ∧ IsGrid (c + 1) r p := by
  rcases le_total r₁ r₂ with hle | hle
  · exact common_row_adj_col_le hc hle hr₂ h1 h2
  · have h1' := (isGrid_revVal_iff c r₁ hr₁ p).mpr h1
    have h2' := (isGrid_revVal_iff (c + 1) r₂ hr₂ p).mpr h2
    rcases common_row_adj_col_le hc (by omega) (by omega) h1' h2' with ⟨r', hr', ha, hb⟩
    refine ⟨n - r', by omega, ?_, ?_⟩
    · have ha' : IsGrid c (n - (n - r')) (revVal p) := by
        have : n - (n - r') = r' := by omega
        rwa [this]
      exact (isGrid_revVal_iff c (n - r') (by omega) p).mp ha'
    · have hb' : IsGrid (c + 1) (n - (n - r')) (revVal p) := by
        have : n - (n - r') = r' := by omega
        rwa [this]
      exact (isGrid_revVal_iff (c + 1) (n - r') (by omega) p).mp hb'

/-! ## Section 4: Pure binomial sum identities -/

/-- Hockey-stick / negative-binomial convolution identity:
    `∑ b ∈ range (k + 1), (a + b).choose a * (d + k - b).choose d = (a + d + k + 1).choose (a + d + 1)`. -/
lemma sum_choose_shift_conv (a d k : ℕ) :
    ∑ b ∈ Finset.range (k + 1), (a + b).choose a * (d + k - b).choose d =
      (a + d + k + 1).choose (a + d + 1) := by
  induction d generalizing k with
  | zero =>
    simp only [Nat.choose_zero_right, mul_one, add_zero]
    induction k with
    | zero => simp
    | succ k ihk =>
      rw [Finset.sum_range_succ, ihk]
      have h1 : a + (k + 1) + 1 = (a + k + 1) + 1 := by omega
      rw [h1, Nat.choose_succ_succ (a + k + 1) a, Nat.succ_eq_add_one]
      ring
  | succ d ihd =>
    induction k with
    | zero =>
      simp
    | succ k ihk =>
      rw [Finset.sum_range_succ]
      have hsplit : ∀ b ∈ Finset.range (k + 1),
          (a + b).choose a * (d + 1 + (k + 1) - b).choose (d + 1) =
            (a + b).choose a * (d + 1 + k - b).choose (d + 1) +
            (a + b).choose a * (d + (k + 1) - b).choose d := by
        intro b hb
        have hbk : b ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
        have h1 : d + 1 + (k + 1) - b = (d + 1 + k - b) + 1 := by omega
        have h2 : d + 1 + k - b = d + (k + 1) - b := by omega
        rw [h1, Nat.choose_succ_succ, h2]
        ring
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, ihk]
      have hlast : (a + (k + 1)).choose a * (d + 1 + (k + 1) - (k + 1)).choose (d + 1) =
          (a + (k + 1)).choose a * (d + (k + 1) - (k + 1)).choose d := by
        have h1 : d + 1 + (k + 1) - (k + 1) = d + 1 := by omega
        have h2 : d + (k + 1) - (k + 1) = d := by omega
        rw [h1, h2, Nat.choose_self, Nat.choose_self]
      rw [hlast, add_assoc, ← Finset.sum_range_succ (fun b => (a + b).choose a * (d + (k + 1) - b).choose d),
          ihd (k + 1)]
      have h3 : a + (d + 1) + (k + 1) + 1 = (a + d + k + 2) + 1 := by omega
      have h4 : a + (d + 1) + k + 1 = a + d + k + 2 := by omega
      have h5 : a + d + (k + 1) + 1 = a + d + k + 2 := by omega
      have h6 : a + (d + 1) + 1 = (a + d + 1) + 1 := by omega
      rw [h3, h4, h5, h6, Nat.choose_succ_succ (a + d + k + 2) (a + d + 1)]
      ring

/-- Identity for the sum over `c, r, a` of `Upper` counts in `G c r ∩ G (c+1) r`. -/
lemma sum_upper_adj_col (n : ℕ) :
    2 * ∑ c ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1), ∑ a ∈ Finset.range (n + 1),
        c.choose a * (n - c).choose (r - a) * r.choose a = 3 ^ (n + 1) - 1 := by
  -- Change variables: sum over (a, d) with a + d ≤ n, then over b = c - a ∈ [0, n - a - d]
  have h_reidx :
      ∑ c ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1), ∑ a ∈ Finset.range (n + 1),
          c.choose a * (n - c).choose (r - a) * r.choose a =
      ∑ r ∈ Finset.range (n + 1), ∑ a ∈ Finset.range (r + 1),
          r.choose a * ∑ b ∈ Finset.range (n - r + 1),
            (a + b).choose a * ((r - a) + (n - r) - b).choose (r - a) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hrn : r ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    rw [Finset.sum_comm]
    -- Restrict a ∈ range (n + 1) to range (r + 1) since r.choose a = 0 for a > r
    have ha_restr :
        ∑ a ∈ Finset.range (n + 1), ∑ c ∈ Finset.range (n + 1),
            c.choose a * (n - c).choose (r - a) * r.choose a =
        ∑ a ∈ Finset.range (r + 1), ∑ c ∈ Finset.range (n + 1),
            c.choose a * (n - c).choose (r - a) * r.choose a := by
      symm
      refine Finset.sum_subset (Finset.range_mono (by omega)) ?_
      intro a _ ha_not
      have har : r < a := by
        simp only [Finset.mem_range] at ha_not
        omega
      simp [Nat.choose_eq_zero_of_lt har]
    rw [ha_restr]
    refine Finset.sum_congr rfl fun a ha => ?_
    have har : a ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    rw [Finset.mul_sum]
    -- Reindex c = a + b for b ∈ range (n - r + 1); outside this range one of the chooses is 0
    have hc_sum :
        ∑ c ∈ Finset.range (n + 1), c.choose a * (n - c).choose (r - a) * r.choose a =
        ∑ c ∈ Finset.Ico a (n - r + a + 1), c.choose a * (n - c).choose (r - a) * r.choose a := by
      symm
      refine Finset.sum_subset ?_ ?_
      · intro c hc
        simp only [Finset.mem_Ico, Finset.mem_range] at hc ⊢
        omega
      · intro c hc hc_not
        simp only [Finset.mem_range, Finset.mem_Ico] at hc hc_not
        by_cases hca : c < a
        · simp [Nat.choose_eq_zero_of_lt hca]
        · have hnc : n - c < r - a := by omega
          simp [Nat.choose_eq_zero_of_lt hnc]
    rw [hc_sum]
    refine Finset.sum_bij (fun c _ => c - a) ?_ ?_ ?_ ?_
    · intro c hc
      simp only [Finset.mem_Ico, Finset.mem_range] at hc ⊢
      omega
    · intro c₁ hc₁ c₂ hc₂ heq
      simp only [Finset.mem_Ico] at hc₁ hc₂
      omega
    · intro b hb
      refine ⟨a + b, ?_, by omega⟩
      simp only [Finset.mem_range, Finset.mem_Ico] at hb ⊢
      omega
    · intro c hc
      simp only [Finset.mem_Ico] at hc
      have h1 : a + (c - a) = c := by omega
      have h2 : r - a + (n - r) - (c - a) = n - c := by omega
      rw [h1, h2]
      ring
  rw [h_reidx]
  have h_inner :
      ∑ r ∈ Finset.range (n + 1), ∑ a ∈ Finset.range (r + 1),
          r.choose a * ∑ b ∈ Finset.range (n - r + 1),
            (a + b).choose a * ((r - a) + (n - r) - b).choose (r - a) =
      ∑ r ∈ Finset.range (n + 1), (n + 1).choose (r + 1) * 2 ^ r := by
    refine Finset.sum_congr rfl fun r hr => ?_
    have hrn : r ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have h_conv : ∀ a ∈ Finset.range (r + 1),
        r.choose a * ∑ b ∈ Finset.range (n - r + 1),
            (a + b).choose a * ((r - a) + (n - r) - b).choose (r - a) =
        r.choose a * (n + 1).choose (r + 1) := by
      intro a ha
      have har : a ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      rw [sum_choose_shift_conv a (r - a) (n - r)]
      have h1 : a + (r - a) + (n - r) + 1 = n + 1 := by omega
      have h2 : a + (r - a) + 1 = r + 1 := by omega
      rw [h1, h2]
    rw [Finset.sum_congr rfl h_conv, ← Finset.sum_mul, Nat.sum_range_choose r, mul_comm]
  rw [h_inner]
  -- 2 * ∑ r ∈ range (n + 1), (n + 1).choose (r + 1) * 2 ^ r = (1 + 2) ^ (n + 1) - 1
  have h_binom := add_pow (2 : ℕ) 1 (n + 1)
  have h3 : (2 + 1 : ℕ) ^ (n + 1) = 3 ^ (n + 1) := by norm_num
  rw [h3] at h_binom
  simp only [Nat.cast_id] at h_binom
  have h_split :
      ∑ m ∈ Finset.range (n + 1 + 1), (2 : ℕ) ^ m * 1 ^ (n + 1 - m) * (n + 1).choose m =
      1 + 2 * ∑ r ∈ Finset.range (n + 1), (n + 1).choose (r + 1) * 2 ^ r := by
    rw [Finset.sum_range_succ']
    simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, add_comm 1]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  rw [h_split] at h_binom
  omega

/-- Key auxiliary sum: `∑ a ∈ range (c + 1), c.choose a * a.choose j * (c - a).choose k =
    c.choose (j + k) * (j + k).choose j * 2 ^ (c - (j + k))`. -/
lemma sum_choose_triple (c j k : ℕ) :
    ∑ a ∈ Finset.range (c + 1), c.choose a * a.choose j * (c - a).choose k =
      c.choose (j + k) * (j + k).choose j * 2 ^ (c - (j + k)) := by
  by_cases hjk : j + k ≤ c
  · have h_sub :
        ∑ a ∈ Finset.range (c + 1), c.choose a * a.choose j * (c - a).choose k =
        ∑ a ∈ Finset.Ico j (c - k + 1), c.choose a * a.choose j * (c - a).choose k := by
      symm
      refine Finset.sum_subset ?_ ?_
      · intro a ha
        simp only [Finset.mem_Ico, Finset.mem_range] at ha ⊢
        omega
      · intro a ha ha_not
        simp only [Finset.mem_range, Finset.mem_Ico] at ha ha_not
        by_cases haj : a < j
        · simp [Nat.choose_eq_zero_of_lt haj]
        · have hck : c - a < k := by omega
          simp [Nat.choose_eq_zero_of_lt hck]
    rw [h_sub]
    have h_bij :
        ∑ a ∈ Finset.Ico j (c - k + 1), c.choose a * a.choose j * (c - a).choose k =
        ∑ t ∈ Finset.range (c - (j + k) + 1),
          c.choose (j + k) * (j + k).choose j * (c - (j + k)).choose t := by
      refine Finset.sum_bij (fun a _ => a - j) ?_ ?_ ?_ ?_
      · intro a ha
        simp only [Finset.mem_Ico, Finset.mem_range] at ha ⊢
        omega
      · intro a₁ ha₁ a₂ ha₂ heq
        simp only [Finset.mem_Ico] at ha₁ ha₂
        omega
      · intro t ht
        refine ⟨j + t, ?_, by omega⟩
        simp only [Finset.mem_range, Finset.mem_Ico] at ht ⊢
        omega
      · intro a ha
        simp only [Finset.mem_Ico] at ha
        -- Pure factorial identity:
        -- c.choose a * a.choose j * (c - a).choose k = c.choose (j+k) * (j+k).choose j * (c-j-k).choose (a-j)
        have h1 : c.choose a * a.choose j = c.choose j * (c - j).choose (a - j) :=
          Nat.choose_mul (n := c) (k := a) (s := j) (by omega)
        have h2 : (c - j).choose (a - j) * (c - a).choose k =
            (c - j).choose k * (c - j - k).choose (a - j) := by
          have hsub : c - j - (a - j) = c - a := by omega
          rw [← hsub]
          have hsym : (a - j + k).choose (a - j) = (a - j + k).choose k := by
            rw [← Nat.choose_symm (by omega : a - j ≤ a - j + k)]
            have : a - j + k - (a - j) = k := by omega
            rw [this]
          have hl : (c - j).choose (a - j) * (c - j - (a - j)).choose k =
              (c - j).choose (a - j + k) * (a - j + k).choose (a - j) := by
            have := Nat.choose_mul (n := c - j) (k := a - j + k) (s := a - j) (by omega)
            have hks : a - j + k - (a - j) = k := by omega
            rw [hks] at this
            exact this.symm
          have hr : (c - j).choose k * (c - j - k).choose (a - j) =
              (c - j).choose (a - j + k) * (a - j + k).choose k := by
            have := Nat.choose_mul (n := c - j) (k := a - j + k) (s := k) (by omega)
            have hks : a - j + k - k = a - j := by omega
            rw [hks] at this
            exact this.symm
          rw [hl, hr, hsym]
        have h3 : c.choose j * (c - j).choose k = c.choose (j + k) * (j + k).choose j := by
          have := Nat.choose_mul (n := c) (k := j + k) (s := j) (by omega)
          have hks : j + k - j = k := by omega
          rw [hks] at this
          exact this.symm
        calc c.choose a * a.choose j * (c - a).choose k
            = c.choose j * ((c - j).choose (a - j) * (c - a).choose k) := by rw [h1]; ring
          _ = (c.choose j * (c - j).choose k) * (c - j - k).choose (a - j) := by rw [h2]; ring
          _ = c.choose (j + k) * (j + k).choose j * (c - (j + k)).choose (a - j) := by
              rw [h3]
              have : c - j - k = c - (j + k) := by omega
              rw [this]
    rw [h_bij, ← Finset.mul_sum, Nat.sum_range_choose]
  · have hlt : c < j + k := by omega
    rw [Nat.choose_eq_zero_of_lt hlt, zero_mul, zero_mul]
    refine Finset.sum_eq_zero fun a ha => ?_
    have hac : a ≤ c := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    by_cases haj : a < j
    · simp [Nat.choose_eq_zero_of_lt haj]
    · have hck : c - a < k := by omega
      simp [Nat.choose_eq_zero_of_lt hck]

/-- Central binomial identity via Vandermonde: `∑ j ∈ range (m + 1), (m.choose j) ^ 2 = (2 * m).choose m`. -/
lemma sum_sq_choose (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), m.choose j * m.choose j = (2 * m).choose m := by
  have hv := Nat.add_choose_eq m m m
  rw [show m + m = 2 * m by omega] at hv
  rw [hv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => m.choose i * m.choose j)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [Nat.choose_symm hjm]

/-- Vandermonde in the form `∑ j ∈ range (n + 1), a.choose j * d.choose j = (a + d).choose a` for `a, d ≤ n`. -/
lemma sum_choose_mul_choose_eq (n a d : ℕ) (ha : a ≤ n) :
    ∑ j ∈ Finset.range (n + 1), a.choose j * d.choose j = (a + d).choose a := by
  have h_restr :
      ∑ j ∈ Finset.range (n + 1), a.choose j * d.choose j =
      ∑ j ∈ Finset.range (a + 1), a.choose j * d.choose j := by
    symm
    refine Finset.sum_subset (Finset.range_mono (by omega)) ?_
    intro j _ hj_not
    simp only [Finset.mem_range] at hj_not
    simp [Nat.choose_eq_zero_of_lt (by omega : a < j)]
  rw [h_restr]
  have hv := Nat.add_choose_eq a d a
  rw [hv, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => a.choose i * d.choose j)]
  -- Swap i ↔ a - i in sum over range (a + 1)
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hja : j ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have h1 : a + 1 - 1 - j = a - j := by omega
  rw [h1, Nat.choose_symm hja]

/-- The total gridding count `T n`. -/
def T (n : ℕ) : ℕ :=
  ∑ c ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1), ∑ a ∈ Finset.range (n + 1),
    c.choose a * (n - c).choose (r - a) * r.choose a * (n - r).choose (c - a)

/-- For fixed `c ≤ n`, the row-sum of `|G_{c,r}|` equals
    `∑ m ∈ range (n + 1), c.choose m * (n - c).choose m * 2 ^ (n - 2 * m) * (2 * m).choose m`. -/
lemma sum_r_G_formula (n c : ℕ) (hc : c ≤ n) :
    ∑ r ∈ Finset.range (n + 1), ∑ a ∈ Finset.range (n + 1),
        c.choose a * (n - c).choose (r - a) * r.choose a * (n - r).choose (c - a) =
    ∑ m ∈ Finset.range (n + 1),
        c.choose m * (n - c).choose m * 2 ^ (n - 2 * m) * (2 * m).choose m := by
  -- Step 1: reindex (r, a) → (a, d) with a ∈ range (c+1), d ∈ range (n-c+1), r = a + d
  have h1 :
      ∑ r ∈ Finset.range (n + 1), ∑ a ∈ Finset.range (n + 1),
          c.choose a * (n - c).choose (r - a) * r.choose a * (n - r).choose (c - a) =
      ∑ a ∈ Finset.range (c + 1), ∑ d ∈ Finset.range (n - c + 1),
          c.choose a * (n - c).choose d * (a + d).choose a * ((c - a) + (n - c - d)).choose (c - a) := by
    rw [Finset.sum_comm]
    have ha_restr :
        ∑ a ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1),
            c.choose a * (n - c).choose (r - a) * r.choose a * (n - r).choose (c - a) =
        ∑ a ∈ Finset.range (c + 1), ∑ r ∈ Finset.range (n + 1),
            c.choose a * (n - c).choose (r - a) * r.choose a * (n - r).choose (c - a) := by
      symm
      refine Finset.sum_subset (Finset.range_mono (by omega)) ?_
      intro a _ ha_not
      simp only [Finset.mem_range] at ha_not
      simp [Nat.choose_eq_zero_of_lt (by omega : c < a)]
    rw [ha_restr]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hac : a ≤ c := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    have hr_sub :
        ∑ r ∈ Finset.range (n + 1),
            c.choose a * (n - c).choose (r - a) * r.choose a * (n - r).choose (c - a) =
        ∑ r ∈ Finset.Ico a (n - c + a + 1),
            c.choose a * (n - c).choose (r - a) * r.choose a * (n - r).choose (c - a) := by
      symm
      refine Finset.sum_subset ?_ ?_
      · intro r hr
        simp only [Finset.mem_Ico, Finset.mem_range] at hr ⊢
        omega
      · intro r hr hr_not
        simp only [Finset.mem_range, Finset.mem_Ico] at hr hr_not
        by_cases hra : r < a
        · simp [Nat.choose_eq_zero_of_lt hra]
        · have hnc : n - c < r - a := by omega
          simp [Nat.choose_eq_zero_of_lt hnc]
    rw [hr_sub]
    refine Finset.sum_bij (fun r _ => r - a) ?_ ?_ ?_ ?_
    · intro r hr
      simp only [Finset.mem_Ico, Finset.mem_range] at hr ⊢
      omega
    · intro r₁ hr₁ r₂ hr₂ heq
      simp only [Finset.mem_Ico] at hr₁ hr₂
      omega
    · intro d hd
      refine ⟨a + d, ?_, by omega⟩
      simp only [Finset.mem_range, Finset.mem_Ico] at hd ⊢
      omega
    · intro r hr
      simp only [Finset.mem_Ico] at hr
      have h_ad : a + (r - a) = r := by omega
      have h_be : c - a + (n - c - (r - a)) = n - r := by omega
      rw [h_ad, h_be]
  rw [h1]
  -- Step 2: expand (a+d).choose a and (b+e).choose b via Vandermonde
  have h2 :
      ∑ a ∈ Finset.range (c + 1), ∑ d ∈ Finset.range (n - c + 1),
          c.choose a * (n - c).choose d * (a + d).choose a * ((c - a) + (n - c - d)).choose (c - a) =
      ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          (∑ a ∈ Finset.range (c + 1), c.choose a * a.choose j * (c - a).choose k) *
          (∑ d ∈ Finset.range (n - c + 1), (n - c).choose d * d.choose j * (n - c - d).choose k) := by
    have h_exp : ∀ a ∈ Finset.range (c + 1), ∀ d ∈ Finset.range (n - c + 1),
        c.choose a * (n - c).choose d * (a + d).choose a * ((c - a) + (n - c - d)).choose (c - a) =
        ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          (c.choose a * a.choose j * (c - a).choose k) *
          ((n - c).choose d * d.choose j * (n - c - d).choose k) := by
      intro a ha d hd
      have hac : a ≤ c := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      rw [← sum_choose_mul_choose_eq n a d (by omega),
          ← sum_choose_mul_choose_eq n (c - a) (n - c - d) (by omega)]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    calc ∑ a ∈ Finset.range (c + 1), ∑ d ∈ Finset.range (n - c + 1),
            c.choose a * (n - c).choose d * (a + d).choose a * ((c - a) + (n - c - d)).choose (c - a)
        = ∑ a ∈ Finset.range (c + 1), ∑ d ∈ Finset.range (n - c + 1),
            ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
              (c.choose a * a.choose j * (c - a).choose k) *
              ((n - c).choose d * d.choose j * (n - c - d).choose k) := by
          refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun d hd => h_exp a ha d hd
      _ = ∑ a ∈ Finset.range (c + 1), ∑ j ∈ Finset.range (n + 1),
            ∑ d ∈ Finset.range (n - c + 1), ∑ k ∈ Finset.range (n + 1),
              (c.choose a * a.choose j * (c - a).choose k) *
              ((n - c).choose d * d.choose j * (n - c - d).choose k) := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ j ∈ Finset.range (n + 1), ∑ a ∈ Finset.range (c + 1),
            ∑ d ∈ Finset.range (n - c + 1), ∑ k ∈ Finset.range (n + 1),
              (c.choose a * a.choose j * (c - a).choose k) *
              ((n - c).choose d * d.choose j * (n - c - d).choose k) := Finset.sum_comm
      _ = ∑ j ∈ Finset.range (n + 1), ∑ a ∈ Finset.range (c + 1),
            ∑ k ∈ Finset.range (n + 1), ∑ d ∈ Finset.range (n - c + 1),
              (c.choose a * a.choose j * (c - a).choose k) *
              ((n - c).choose d * d.choose j * (n - c - d).choose k) := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
            ∑ a ∈ Finset.range (c + 1), ∑ d ∈ Finset.range (n - c + 1),
              (c.choose a * a.choose j * (c - a).choose k) *
              ((n - c).choose d * d.choose j * (n - c - d).choose k) := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
  rw [h2]
  -- Step 3: apply sum_choose_triple to both inner sums, then group by m = j + k
  have h3 :
      ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          (∑ a ∈ Finset.range (c + 1), c.choose a * a.choose j * (c - a).choose k) *
          (∑ d ∈ Finset.range (n - c + 1), (n - c).choose d * d.choose j * (n - c - d).choose k) =
      ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          c.choose (j + k) * (n - c).choose (j + k) * 2 ^ (n - 2 * (j + k)) *
          ((j + k).choose j * (j + k).choose j) := by
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [sum_choose_triple c j k, sum_choose_triple (n - c) j k]
    by_cases h1 : j + k ≤ c ∧ j + k ≤ n - c
    · have hp : 2 ^ (c - (j + k)) * 2 ^ (n - c - (j + k)) = 2 ^ (n - 2 * (j + k)) := by
        rw [← pow_add]
        congr 1
        omega
      calc c.choose (j + k) * (j + k).choose j * 2 ^ (c - (j + k)) *
              ((n - c).choose (j + k) * (j + k).choose j * 2 ^ (n - c - (j + k)))
          = c.choose (j + k) * (n - c).choose (j + k) *
              (2 ^ (c - (j + k)) * 2 ^ (n - c - (j + k))) *
              ((j + k).choose j * (j + k).choose j) := by ring
        _ = _ := by rw [hp]
    · rcases not_and_or.mp h1 with hlt | hlt
      · have hlt' : c < j + k := by omega
        simp [Nat.choose_eq_zero_of_lt hlt']
      · have hlt' : n - c < j + k := by omega
        simp [Nat.choose_eq_zero_of_lt hlt']
  rw [h3]
  -- Step 4: group (j, k) by m = j + k ∈ range (n + 1)
  have h4 :
      ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          c.choose (j + k) * (n - c).choose (j + k) * 2 ^ (n - 2 * (j + k)) *
          ((j + k).choose j * (j + k).choose j) =
      ∑ m ∈ Finset.range (n + 1),
          c.choose m * (n - c).choose m * 2 ^ (n - 2 * m) *
          (∑ j ∈ Finset.range (m + 1), m.choose j * m.choose j) := by
    have h_zero : ∀ j ∈ Finset.range (n + 1), ∀ k ∈ Finset.range (n + 1),
        n < j + k →
        c.choose (j + k) * (n - c).choose (j + k) * 2 ^ (n - 2 * (j + k)) *
          ((j + k).choose j * (j + k).choose j) = 0 := by
      intro j _ k _ hgt
      have : c < j + k := by omega
      simp [Nat.choose_eq_zero_of_lt this]
    -- Rewrite RHS as double sum over (m, j) with j ≤ m ≤ n, then bijection with (j, k) with j + k ≤ n
    symm
    calc ∑ m ∈ Finset.range (n + 1),
            c.choose m * (n - c).choose m * 2 ^ (n - 2 * m) *
            (∑ j ∈ Finset.range (m + 1), m.choose j * m.choose j)
        = ∑ m ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
            c.choose m * (n - c).choose m * 2 ^ (n - 2 * m) *
            (m.choose j * m.choose j) := by
          refine Finset.sum_congr rfl fun m _ => Finset.mul_sum ..
      _ = ∑ p ∈ (Finset.range (n + 1)).sigma (fun m => Finset.range (m + 1)),
            c.choose p.1 * (n - c).choose p.1 * 2 ^ (n - 2 * p.1) *
            (p.1.choose p.2 * p.1.choose p.2) := by
          rw [Finset.sum_sigma]
      _ = ∑ p ∈ ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter (fun p => p.1 + p.2 ≤ n),
            c.choose (p.1 + p.2) * (n - c).choose (p.1 + p.2) * 2 ^ (n - 2 * (p.1 + p.2)) *
            ((p.1 + p.2).choose p.1 * (p.1 + p.2).choose p.1) := by
          refine Finset.sum_bij (fun p _ => (p.2, p.1 - p.2)) ?_ ?_ ?_ ?_
          · intro p hp
            simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter, Finset.mem_product] at hp ⊢
            omega
          · intro p₁ hp₁ p₂ hp₂ heq
            simp only [Finset.mem_sigma, Finset.mem_range] at hp₁ hp₂
            simp only [Prod.mk.injEq] at heq
            exact Sigma.ext (by omega) (heq_of_eq (by omega))
          · intro q hq
            simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hq
            refine ⟨⟨q.1 + q.2, q.1⟩, ?_, ?_⟩
            · simp only [Finset.mem_sigma, Finset.mem_range]
              omega
            · ext
              · rfl
              · dsimp; omega
          · intro p hp
            simp only [Finset.mem_sigma, Finset.mem_range] at hp
            have : p.2 + (p.1 - p.2) = p.1 := by omega
            rw [this]
      _ = ∑ p ∈ (Finset.range (n + 1)) ×ˢ (Finset.range (n + 1)),
            c.choose (p.1 + p.2) * (n - c).choose (p.1 + p.2) * 2 ^ (n - 2 * (p.1 + p.2)) *
            ((p.1 + p.2).choose p.1 * (p.1 + p.2).choose p.1) := by
          refine Finset.sum_subset (Finset.filter_subset _ _) ?_
          intro p hp hp_not
          have hgt : n < p.1 + p.2 := by
            by_contra hle
            exact hp_not (Finset.mem_filter.mpr ⟨hp, by omega⟩)
          exact h_zero p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2 hgt
      _ = _ := by rw [Finset.sum_product]
  rw [h4]
  refine Finset.sum_congr rfl fun m _ => by rw [sum_sq_choose m]

/-- Explicit closed sum formula for `T n`. -/
lemma T_formula (n : ℕ) :
    T n = ∑ m ∈ Finset.range (n + 1),
      (n + 1).choose (2 * m + 1) * 2 ^ (n - 2 * m) * (2 * m).choose m := by
  unfold T
  have h1 :
      ∑ c ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1), ∑ a ∈ Finset.range (n + 1),
          c.choose a * (n - c).choose (r - a) * r.choose a * (n - r).choose (c - a) =
      ∑ c ∈ Finset.range (n + 1), ∑ m ∈ Finset.range (n + 1),
          c.choose m * (n - c).choose m * 2 ^ (n - 2 * m) * (2 * m).choose m :=
    Finset.sum_congr rfl fun c hc =>
      sum_r_G_formula n c (Nat.lt_succ_iff.mp (Finset.mem_range.mp hc))
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hpull :
      ∑ c ∈ Finset.range (n + 1),
          c.choose m * (n - c).choose m * 2 ^ (n - 2 * m) * (2 * m).choose m =
      (∑ c ∈ Finset.range (n + 1), c.choose m * (n - c).choose m) *
        (2 ^ (n - 2 * m) * (2 * m).choose m) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => by ring
  rw [hpull]
  by_cases h2m : 2 * m ≤ n
  · have h_sub :
        ∑ c ∈ Finset.range (n + 1), c.choose m * (n - c).choose m =
        ∑ c ∈ Finset.Ico m (n - m + 1), c.choose m * (n - c).choose m := by
      symm
      refine Finset.sum_subset ?_ ?_
      · intro c hc
        simp only [Finset.mem_Ico, Finset.mem_range] at hc ⊢
        omega
      · intro c hc hc_not
        simp only [Finset.mem_range, Finset.mem_Ico] at hc hc_not
        by_cases hcm : c < m
        · simp [Nat.choose_eq_zero_of_lt hcm]
        · simp [Nat.choose_eq_zero_of_lt (by omega : n - c < m)]
    rw [h_sub]
    have h_bij :
        ∑ c ∈ Finset.Ico m (n - m + 1), c.choose m * (n - c).choose m =
        ∑ b ∈ Finset.range (n - 2 * m + 1), (m + b).choose m * (m + (n - 2 * m) - b).choose m := by
      refine Finset.sum_bij (fun c _ => c - m) ?_ ?_ ?_ ?_
      · intro c hc
        simp only [Finset.mem_Ico, Finset.mem_range] at hc ⊢
        omega
      · intro c₁ hc₁ c₂ hc₂ heq
        simp only [Finset.mem_Ico] at hc₁ hc₂
        omega
      · intro b hb
        refine ⟨m + b, ?_, by omega⟩
        simp only [Finset.mem_range, Finset.mem_Ico] at hb ⊢
        omega
      · intro c hc
        simp only [Finset.mem_Ico] at hc
        have h1 : m + (c - m) = c := by omega
        have h2 : m + (n - 2 * m) - (c - m) = n - c := by omega
        rw [h1, h2]
    rw [h_bij, sum_choose_shift_conv m m (n - 2 * m)]
    have h1 : m + m + (n - 2 * m) + 1 = n + 1 := by omega
    have h2 : m + m + 1 = 2 * m + 1 := by omega
    rw [h1, h2]
    ring
  · have hlt : n + 1 < 2 * m + 1 := by omega
    rw [Nat.choose_eq_zero_of_lt hlt, zero_mul, zero_mul]
    have hzero : ∑ c ∈ Finset.range (n + 1), c.choose m * (n - c).choose m = 0 := by
      refine Finset.sum_eq_zero fun c hc => ?_
      by_cases hcm : c < m
      · simp [Nat.choose_eq_zero_of_lt hcm]
      · simp [Nat.choose_eq_zero_of_lt (by omega : n - c < m)]
    rw [hzero, zero_mul]

/-- Polynomial coefficient identity:
    `∑ m ∈ range (n + 1), n.choose (2 * m) * 2 ^ (n - 2 * m) * (2 * m).choose m = (2 * n).choose n`. -/
lemma sum_choose_even_central (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), n.choose (2 * m) * 2 ^ (n - 2 * m) * (2 * m).choose m =
      (2 * n).choose n := by
  open Polynomial in
  have hpoly : ((1 + X : Polynomial ℕ) ^ (2 * n)) = (2 * X + (1 + X ^ 2)) ^ n := by
    rw [pow_mul]
    congr 1
    ring
  have hlhs : ((1 + X : Polynomial ℕ) ^ (2 * n)).coeff n = (2 * n).choose n := by
    rw [add_comm, Polynomial.coeff_X_add_one_pow]
    simp
  rw [hpoly, add_pow, Polynomial.finsetSum_coeff, ← Finset.sum_range_reflect] at hlhs
  have h_coeff : ∀ j ∈ Finset.range (n + 1),
      ((2 * X : Polynomial ℕ) ^ (n + 1 - 1 - j) * (1 + X ^ 2) ^ (n - (n + 1 - 1 - j)) *
        ((n.choose (n + 1 - 1 - j) : ℕ) : Polynomial ℕ)).coeff n =
      if Even j then n.choose j * 2 ^ (n - j) * j.choose (j / 2) else 0 := by
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have h1 : n + 1 - 1 - j = n - j := by omega
    have h2 : n - (n - j) = j := by omega
    rw [h1, h2, Nat.choose_symm hjn]
    rw [Polynomial.coeff_mul_natCast, mul_pow, show (2 : Polynomial ℕ) = Polynomial.C 2 by rfl,
        ← Polynomial.C_pow, mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
    have hsub_le : n - j ≤ n := Nat.sub_le n j
    rw [if_pos hsub_le, h2]
    have h_sq : ((1 + X ^ 2 : Polynomial ℕ) ^ j).coeff j =
        if Even j then j.choose (j / 2) else 0 := by
      rw [add_comm, add_pow, Polynomial.finsetSum_coeff]
      simp only [one_pow, mul_one, ← pow_mul, Polynomial.coeff_mul_natCast, Polynomial.coeff_X_pow]
      by_cases hev : Even j
      · rcases hev with ⟨m, rfl⟩
        rw [if_pos ⟨m, rfl⟩]
        have hm2 : (m + m) / 2 = m := by omega
        rw [hm2]
        rw [Finset.sum_eq_single m]
        · simp [two_mul]
        · intro b _ hbm
          have hne : m + m ≠ 2 * b := by omega
          simp [hne]
        · intro hm_not
          simp only [Finset.mem_range] at hm_not
          omega
      · rw [if_neg hev]
        refine Finset.sum_eq_zero fun b _ => ?_
        have hne : j ≠ 2 * b := by
          intro h
          exact hev ⟨b, by omega⟩
        simp [hne]
    rw [h_sq]
    split_ifs
    · simp only [Nat.cast_id]; ring
    · simp
  rw [Finset.sum_congr rfl h_coeff] at hlhs
  rw [← hlhs]
  have h_restr :
      ∑ m ∈ Finset.range (n + 1), n.choose (2 * m) * 2 ^ (n - 2 * m) * (2 * m).choose m =
      ∑ m ∈ Finset.range (n / 2 + 1), n.choose (2 * m) * 2 ^ (n - 2 * m) * (2 * m).choose m := by
    symm
    refine Finset.sum_subset (Finset.range_mono (by omega)) ?_
    intro m _ hm_not
    simp only [Finset.mem_range] at hm_not
    have hlt : n < 2 * m := by omega
    simp [Nat.choose_eq_zero_of_lt hlt]
  rw [h_restr, ← Finset.sum_filter]
  refine Finset.sum_bij (fun m _ => 2 * m) ?_ ?_ ?_ ?_
  · intro m hm
    simp only [Finset.mem_range, Finset.mem_filter] at hm ⊢
    exact ⟨by omega, ⟨m, by omega⟩⟩
  · intro m₁ _ m₂ _ heq
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    rcases hj.2 with ⟨m, rfl⟩
    refine ⟨m, Finset.mem_range.mpr (by omega), by omega⟩
  · intro m _
    have : 2 * m / 2 = m := by omega
    rw [this]

/-- Key recurrence for `T`: `T (n + 1) = 2 * T n + (2 * (n + 1)).choose (n + 1)`. -/
lemma T_succ_eq (n : ℕ) :
    T (n + 1) = 2 * T n + (2 * (n + 1)).choose (n + 1) := by
  have h2T : 2 * T n = ∑ m ∈ Finset.range (n + 2),
      2 * ((n + 1).choose (2 * m + 1) * 2 ^ (n - 2 * m) * (2 * m).choose m) := by
    rw [T_formula n, Finset.mul_sum]
    symm
    rw [Finset.sum_range_succ]
    have hzero : 2 * ((n + 1).choose (2 * (n + 1) + 1) * 2 ^ (n - 2 * (n + 1)) *
        (2 * (n + 1)).choose (n + 1)) = 0 := by
      simp [Nat.choose_eq_zero_of_lt (by omega : n + 1 < 2 * (n + 1) + 1)]
    rw [hzero, add_zero]
  rw [T_formula (n + 1), h2T, ← sum_choose_even_central (n + 1), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases h2m : 2 * m ≤ n
  · have hp : 2 ^ (n + 1 - 2 * m) = 2 * 2 ^ (n - 2 * m) := by
      have : n + 1 - 2 * m = (n - 2 * m) + 1 := by omega
      rw [this, pow_succ']
    rw [Nat.choose_succ_succ (n + 1) (2 * m), hp]
    ring
  · by_cases h2m' : 2 * m = n + 1
    · have hlt1 : n + 1 < 2 * m + 1 := by omega
      rw [Nat.choose_eq_zero_of_lt hlt1]
      have h1 : n + 1 - 2 * m = 0 := by omega
      have h2 : n + 1 + 1 = 2 * m + 1 := by omega
      rw [h1, h2, ← h2m', Nat.choose_self, Nat.choose_self]
      ring
    · have hlt1 : n + 1 < 2 * m := by omega
      have hlt2 : n + 1 < 2 * m + 1 := by omega
      have hlt3 : n + 2 < 2 * m + 1 := by omega
      rw [Nat.choose_eq_zero_of_lt hlt1, Nat.choose_eq_zero_of_lt hlt2,
          Nat.choose_eq_zero_of_lt hlt3]
      ring

/-! ## Section 5: Deduction of R. J. Mathar's recurrence from the closed form -/

lemma central_binom_succ (m : ℕ) :
    ((m + 1 : ℤ) * ((2 * (m + 1)).choose (m + 1) : ℤ)) =
      2 * (2 * (m : ℤ) + 1) * ((2 * m).choose m : ℤ) := by
  have h1 : (2 * m + 1 + 1) * (2 * m + 1).choose m = (2 * m + 1 + 1).choose (m + 1) * (m + 1) := by
    have hsym : (2 * m + 1).choose (m + 1) = (2 * m + 1).choose m := by
      rw [← Nat.choose_symm (by omega : m + 1 ≤ 2 * m + 1)]
      congr 1; omega
    have := Nat.choose_mul_succ_eq (2 * m + 1) (m + 1)
    have hsub : 2 * m + 1 + 1 - (m + 1) = m + 1 := by omega
    rw [hsym, hsub] at this
    linarith
  have h2 : (2 * m).choose m * (2 * m + 1) = (2 * m + 1).choose m * (m + 1) := by
    have := Nat.choose_mul_succ_eq (2 * m) m
    have hsub : 2 * m + 1 - m = m + 1 := by omega
    rwa [hsub] at this
  have h3 : (m + 1) * (2 * (m + 1)).choose (m + 1) = 2 * (2 * m + 1) * (2 * m).choose m := by
    have h2m2 : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
    rw [h2m2]
    have hmul : (m + 1) * ((m + 1) * (2 * m + 1 + 1).choose (m + 1)) =
        (m + 1) * (2 * (2 * m + 1) * (2 * m).choose m) := by
      calc (m + 1) * ((m + 1) * (2 * m + 1 + 1).choose (m + 1))
          = (m + 1) * ((2 * m + 1 + 1).choose (m + 1) * (m + 1)) := by ring
        _ = (m + 1) * ((2 * m + 1 + 1) * (2 * m + 1).choose m) := by rw [← h1]
        _ = (2 * m + 1 + 1) * ((2 * m + 1).choose m * (m + 1)) := by ring
        _ = (2 * m + 1 + 1) * ((2 * m).choose m * (2 * m + 1)) := by rw [← h2]
        _ = (m + 1) * (2 * (2 * m + 1) * (2 * m).choose m) := by ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos m) hmul
  exact_mod_cast h3

lemma recurrence_of_closed_form (f : ℕ → ℤ)
    (hf : ∀ k : ℕ, f (k + 1) = ((2 * (k + 1)).choose (k + 1) : ℤ) - 2 * 3 ^ k + 2 ^ k) :
    ∀ n : ℕ, 4 ≤ n →
      let x : ℤ := n
      x * (x ^ 2 - 6 * x + 11) * f n +
        (-9 * x ^ 3 + 56 * x ^ 2 - 119 * x + 60) * f (n - 1) +
        2 * (13 * x ^ 3 - 83 * x ^ 2 + 193 * x - 150) * f (n - 2) -
        12 * (2 * x - 5) * (x ^ 2 - 4 * x + 6) * f (n - 3) = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  -- n = 4 + k
  have hn0 : 4 + k = (k + 3) + 1 := by omega
  have hn1 : 4 + k - 1 = (k + 2) + 1 := by omega
  have hn2 : 4 + k - 2 = (k + 1) + 1 := by omega
  have hn3 : 4 + k - 3 = k + 1 := by omega
  dsimp only
  rw [hn1, hn2, hn3]
  have hf4 : f (4 + k) = ((2 * (k + 4)).choose (k + 4) : ℤ) - 2 * 3 ^ (k + 3) + 2 ^ (k + 3) := by
    rw [hn0, hf (k + 3)]
  have hf3 := hf (k + 2)
  have hf2 := hf (k + 1)
  have hf1 := hf k
  rw [hf4, hf3, hf2, hf1]
  have hcb1 := central_binom_succ (k + 1)
  have hcb2 := central_binom_succ (k + 2)
  have hcb3 := central_binom_succ (k + 3)
  set C1 : ℤ := ((2 * (k + 1)).choose (k + 1) : ℤ)
  set C2 : ℤ := ((2 * (k + 2)).choose (k + 2) : ℤ)
  set C3 : ℤ := ((2 * (k + 3)).choose (k + 3) : ℤ)
  set C4 : ℤ := ((2 * (k + 4)).choose (k + 4) : ℤ)
  set t : ℤ := (k : ℤ)
  have hx : ((4 + k : ℕ) : ℤ) = t + 4 := by push_cast; ring
  rw [hx]
  have h1 : (t + 2) * C2 = 2 * (2 * t + 3) * C1 := by
    convert hcb1 using 2 <;> (push_cast; ring)
  have h2 : (t + 3) * C3 = 2 * (2 * t + 5) * C2 := by
    convert hcb2 using 2 <;> (push_cast; ring)
  have h3 : (t + 4) * C4 = 2 * (2 * t + 7) * C3 := by
    convert hcb3 using 2 <;> (push_cast; ring)
  have hpos : (t + 2) * (t + 3) ≠ 0 := by positivity
  apply mul_left_cancel₀ hpos
  rw [mul_zero]
  have hC4 : (t + 2) * (t + 3) * ((t + 4) * C4) =
      8 * (2 * t + 7) * (2 * t + 5) * (2 * t + 3) * C1 := by
    calc (t + 2) * (t + 3) * ((t + 4) * C4)
        = (t + 2) * (2 * (2 * t + 7) * ((t + 3) * C3)) := by rw [h3]; ring
      _ = 2 * (2 * t + 7) * (2 * (2 * t + 5) * ((t + 2) * C2)) := by rw [h2]; ring
      _ = 2 * (2 * t + 7) * (2 * (2 * t + 5) * (2 * (2 * t + 3) * C1)) := by rw [h1]
      _ = 8 * (2 * t + 7) * (2 * t + 5) * (2 * t + 3) * C1 := by ring
  have hC3 : (t + 2) * (t + 3) * C3 = 4 * (2 * t + 5) * (2 * t + 3) * C1 := by
    calc (t + 2) * (t + 3) * C3
        = (t + 2) * ((t + 3) * C3) := by ring
      _ = 2 * (2 * t + 5) * ((t + 2) * C2) := by rw [h2]; ring
      _ = 2 * (2 * t + 5) * (2 * (2 * t + 3) * C1) := by rw [h1]
      _ = 4 * (2 * t + 5) * (2 * t + 3) * C1 := by ring
  have hC2 : (t + 2) * (t + 3) * C2 = 2 * (t + 3) * (2 * t + 3) * C1 := by
    calc (t + 2) * (t + 3) * C2
        = (t + 3) * ((t + 2) * C2) := by ring
      _ = 2 * (t + 3) * (2 * t + 3) * C1 := by rw [h1]; ring
  have hp3 : (3 : ℤ) ^ (k + 3) = 27 * 3 ^ k := by ring
  have hp3_2 : (3 : ℤ) ^ (k + 2) = 9 * 3 ^ k := by ring
  have hp3_1 : (3 : ℤ) ^ (k + 1) = 3 * 3 ^ k := by ring
  have hp2 : (2 : ℤ) ^ (k + 3) = 8 * 2 ^ k := by ring
  have hp2_2 : (2 : ℤ) ^ (k + 2) = 4 * 2 ^ k := by ring
  have hp2_1 : (2 : ℤ) ^ (k + 1) = 2 * 2 ^ k := by ring
  rw [hp3, hp3_2, hp3_1, hp2, hp2_2, hp2_1]
  linear_combination
    ((t + 4) ^ 2 - 6 * (t + 4) + 11) * hC4 +
    (-9 * (t + 4) ^ 3 + 56 * (t + 4) ^ 2 - 119 * (t + 4) + 60) * hC3 +
    2 * (13 * (t + 4) ^ 3 - 83 * (t + 4) ^ 2 + 193 * (t + 4) - 150) * hC2

/-! ## Section 3: Finite sets, monotone bijections, and the four exact counting lemmas -/

section Counting

open Classical

/-- Permutations of `Fin n` valid for gridding `(c, r)`. -/
noncomputable def G (n c r : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun p => IsGrid c r p)

/-- Permutations of `Fin n` valid for column divider `c` and some row divider `r ≤ n`. -/
noncomputable def S (n c : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  (Finset.range (n + 1)).biUnion (G n c)

/-- Permutations of `Fin n` admitting a double-chevron gridding. -/
noncomputable def DC (n : ℕ) : Finset (Equiv.Perm (Fin n)) :=
  (Finset.range (n + 1)).biUnion (S n)

lemma mem_G {n c r : ℕ} {p : Equiv.Perm (Fin n)} : p ∈ G n c r ↔ IsGrid c r p := by
  simp [G]

lemma mem_S {n c : ℕ} {p : Equiv.Perm (Fin n)} :
    p ∈ S n c ↔ ∃ r ∈ Finset.range (n + 1), IsGrid c r p := by
  simp [S, mem_G]

lemma mem_DC {n : ℕ} {p : Equiv.Perm (Fin n)} :
    p ∈ DC n ↔ OMA.S_oeis_a163824.HasDoubleChevronGridding p := by
  simp [DC, mem_S, hasDoubleChevronGridding_iff]

lemma gridCount_eq_card_DC (n : ℕ) :
    OMA.S_oeis_a163824.gridCount n = ((DC n).card : ℤ) := by
  unfold OMA.S_oeis_a163824.gridCount
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  refine Finset.card_bij (fun p _ => p) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact mem_DC.mpr hp
  · intro _ _ _ _ h; exact h
  · intro p hp
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, mem_DC.mp hp⟩, rfl⟩

/-! ### Helper: Monotone bijections between Finsets of `Fin n` and 4-block gluing -/

lemma orderIso_fin_eq_id {k : ℕ} (e : Fin k ≃o Fin k) : ∀ x : Fin k, e x = x := by
  have hle : ∀ (f : Fin k ≃o Fin k) (m : ℕ) (hm : m < k), m ≤ (f ⟨m, hm⟩).val := by
    intro f m
    induction m with
    | zero => intro _; exact Nat.zero_le _
    | succ m ih =>
      intro hm
      have h1 : m ≤ (f ⟨m, by omega⟩).val := ih (by omega)
      have hlt_arg : (⟨m, by omega⟩ : Fin k) < ⟨m + 1, hm⟩ := Fin.lt_def.mpr (by dsimp; omega)
      have h2 : f ⟨m, by omega⟩ < f ⟨m + 1, hm⟩ := f.strictMono hlt_arg
      have h3 : (f ⟨m, by omega⟩).val < (f ⟨m + 1, hm⟩).val := h2
      omega
  intro x
  have h1 : x.val ≤ (e x).val := hle e x.val x.isLt
  have h2 : (e x).val ≤ (e.symm (e x)).val := hle e.symm (e x).val (e x).isLt
  rw [e.symm_apply_apply] at h2
  exact Fin.ext (le_antisymm h2 h1)

lemma strictMono_bij_unique {n : ℕ} {A B : Finset (Fin n)}
    {f g : {x // x ∈ A} → {y // y ∈ B}}
    (hf_bij : Function.Bijective f) (hg_bij : Function.Bijective g)
    (hf_mono : StrictMono (fun x => (f x).val))
    (hg_mono : StrictMono (fun x => (g x).val)) :
    ∀ x, f x = g x := by
  let ef : {x // x ∈ A} ≃o {y // y ∈ B} :=
    { toEquiv := Equiv.ofBijective f hf_bij
      map_rel_iff' := fun {a b} => hf_mono.le_iff_le }
  let eg : {x // x ∈ A} ≃o {y // y ∈ B} :=
    { toEquiv := Equiv.ofBijective g hg_bij
      map_rel_iff' := fun {a b} => hg_mono.le_iff_le }
  let isoA : Fin A.card ≃o {x // x ∈ A} := A.orderIsoOfFin rfl
  let φ : Fin A.card ≃o Fin A.card := (isoA.trans (ef.trans eg.symm)).trans isoA.symm
  intro x
  have hφ := orderIso_fin_eq_id φ (isoA.symm x)
  have h1 : eg.symm (ef x) = x := by
    have := congrArg isoA hφ
    simpa [φ] using this
  have h2 : ef x = eg x := by
    have := congrArg eg h1
    simpa using this
  exact h2

lemma strictAnti_bij_unique {n : ℕ} {A B : Finset (Fin n)}
    {f g : {x // x ∈ A} → {y // y ∈ B}}
    (hf_bij : Function.Bijective f) (hg_bij : Function.Bijective g)
    (hf_anti : StrictAnti (fun x => (f x).val))
    (hg_anti : StrictAnti (fun x => (g x).val)) :
    ∀ x, f x = g x := by
  let B' : Finset (Fin n) := B.image Fin.rev
  let revB : {y // y ∈ B} ≃ {y // y ∈ B'} :=
    { toFun := fun y => ⟨Fin.rev y.val, Finset.mem_image.mpr ⟨y.val, y.property, rfl⟩⟩
      invFun := fun z => ⟨Fin.rev z.val, by
        rcases Finset.mem_image.mp z.property with ⟨y, hy, hyz⟩
        rw [← hyz, Fin.rev_rev]; exact hy⟩
      left_inv := fun y => Subtype.ext (Fin.rev_rev y.val)
      right_inv := fun z => Subtype.ext (Fin.rev_rev z.val) }
  have h := strictMono_bij_unique
    (f := fun x => revB (f x)) (g := fun x => revB (g x))
    (revB.bijective.comp hf_bij) (revB.bijective.comp hg_bij)
    (fun a b hab => Fin.rev_lt_rev.mpr (hf_anti hab))
    (fun a b hab => Fin.rev_lt_rev.mpr (hg_anti hab))
  intro x
  exact revB.injective (h x)

/-- The unique strictly increasing bijection `{x // x ∈ A} ≃ {y // y ∈ B}` when `A.card = B.card`. -/
noncomputable def incBij {n : ℕ} (A B : Finset (Fin n)) (h : A.card = B.card) :
    {x // x ∈ A} ≃ {y // y ∈ B} :=
  ((A.orderIsoOfFin rfl).symm.trans (Fin.castOrderIso h)).trans (B.orderIsoOfFin rfl) |>.toEquiv

lemma incBij_strictMono {n : ℕ} (A B : Finset (Fin n)) (h : A.card = B.card) :
    StrictMono (fun x => (incBij A B h x).val) := by
  intro a b hab
  change (((A.orderIsoOfFin rfl).symm.trans (Fin.castOrderIso h)).trans (B.orderIsoOfFin rfl) a).val <
         (((A.orderIsoOfFin rfl).symm.trans (Fin.castOrderIso h)).trans (B.orderIsoOfFin rfl) b).val
  exact (((A.orderIsoOfFin rfl).symm.trans (Fin.castOrderIso h)).trans (B.orderIsoOfFin rfl)).strictMono hab

/-- The unique strictly decreasing bijection `{x // x ∈ A} ≃ {y // y ∈ B}` when `A.card = B.card`. -/
noncomputable def decBij {n : ℕ} (A B : Finset (Fin n)) (h : A.card = B.card) :
    {x // x ∈ A} ≃ {y // y ∈ B} :=
  ((A.orderIsoOfFin rfl).symm.toEquiv.trans Fin.revPerm).trans
    ((Fin.castOrderIso h).trans (B.orderIsoOfFin rfl)).toEquiv

lemma decBij_strictAnti {n : ℕ} (A B : Finset (Fin n)) (h : A.card = B.card) :
    StrictAnti (fun x => (decBij A B h x).val) := by
  intro a b hab
  have h1 : (A.orderIsoOfFin rfl).symm a < (A.orderIsoOfFin rfl).symm b :=
    (A.orderIsoOfFin rfl).symm.strictMono hab
  have h2 : Fin.rev ((A.orderIsoOfFin rfl).symm b) < Fin.rev ((A.orderIsoOfFin rfl).symm a) :=
    Fin.rev_lt_rev.mpr h1
  exact ((Fin.castOrderIso h).trans (B.orderIsoOfFin rfl)).strictMono h2

/-- Glue 4 bijections across 4-part partitions of `Fin n`. -/
noncomputable def glue4 {n : ℕ}
    (A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Finset (Fin n))
    (hA12 : Disjoint A₁ A₂) (hA13 : Disjoint A₁ A₃) (hA14 : Disjoint A₁ A₄)
    (hA23 : Disjoint A₂ A₃) (hA24 : Disjoint A₂ A₄) (hA34 : Disjoint A₃ A₄)
    (hAcov : ∀ x : Fin n, x ∈ A₁ ∨ x ∈ A₂ ∨ x ∈ A₃ ∨ x ∈ A₄)
    (hB12 : Disjoint B₁ B₂) (hB13 : Disjoint B₁ B₃) (hB14 : Disjoint B₁ B₄)
    (hB23 : Disjoint B₂ B₃) (hB24 : Disjoint B₂ B₄) (hB34 : Disjoint B₃ B₄)
    (hBcov : ∀ y : Fin n, y ∈ B₁ ∨ y ∈ B₂ ∨ y ∈ B₃ ∨ y ∈ B₄)
    (e₁ : {x // x ∈ A₁} ≃ {y // y ∈ B₁})
    (e₂ : {x // x ∈ A₂} ≃ {y // y ∈ B₂})
    (e₃ : {x // x ∈ A₃} ≃ {y // y ∈ B₃})
    (e₄ : {x // x ∈ A₄} ≃ {y // y ∈ B₄}) :
    Equiv.Perm (Fin n) where
  toFun x :=
    if h1 : x ∈ A₁ then (e₁ ⟨x, h1⟩).val
    else if h2 : x ∈ A₂ then (e₂ ⟨x, h2⟩).val
    else if h3 : x ∈ A₃ then (e₃ ⟨x, h3⟩).val
    else (e₄ ⟨x, by rcases hAcov x with h | h | h | h <;> tauto⟩).val
  invFun y :=
    if h1 : y ∈ B₁ then (e₁.symm ⟨y, h1⟩).val
    else if h2 : y ∈ B₂ then (e₂.symm ⟨y, h2⟩).val
    else if h3 : y ∈ B₃ then (e₃.symm ⟨y, h3⟩).val
    else (e₄.symm ⟨y, by rcases hBcov y with h | h | h | h <;> tauto⟩).val
  left_inv x := by
    dsimp only
    by_cases h1 : x ∈ A₁
    · rw [dif_pos h1, dif_pos (e₁ ⟨x, h1⟩).property]
      exact congrArg Subtype.val (e₁.symm_apply_apply ⟨x, h1⟩)
    · by_cases h2 : x ∈ A₂
      · have hb1 : (e₂ ⟨x, h2⟩).val ∉ B₁ :=
          Finset.disjoint_right.mp hB12 (e₂ ⟨x, h2⟩).property
        rw [dif_neg h1, dif_pos h2, dif_neg hb1, dif_pos (e₂ ⟨x, h2⟩).property]
        exact congrArg Subtype.val (e₂.symm_apply_apply ⟨x, h2⟩)
      · by_cases h3 : x ∈ A₃
        · have hb1 : (e₃ ⟨x, h3⟩).val ∉ B₁ :=
            Finset.disjoint_right.mp hB13 (e₃ ⟨x, h3⟩).property
          have hb2 : (e₃ ⟨x, h3⟩).val ∉ B₂ :=
            Finset.disjoint_right.mp hB23 (e₃ ⟨x, h3⟩).property
          rw [dif_neg h1, dif_neg h2, dif_pos h3, dif_neg hb1, dif_neg hb2,
              dif_pos (e₃ ⟨x, h3⟩).property]
          exact congrArg Subtype.val (e₃.symm_apply_apply ⟨x, h3⟩)
        · have h4 : x ∈ A₄ := by rcases hAcov x with h | h | h | h <;> tauto
          have hb1 : (e₄ ⟨x, h4⟩).val ∉ B₁ :=
            Finset.disjoint_right.mp hB14 (e₄ ⟨x, h4⟩).property
          have hb2 : (e₄ ⟨x, h4⟩).val ∉ B₂ :=
            Finset.disjoint_right.mp hB24 (e₄ ⟨x, h4⟩).property
          have hb3 : (e₄ ⟨x, h4⟩).val ∉ B₃ :=
            Finset.disjoint_right.mp hB34 (e₄ ⟨x, h4⟩).property
          rw [dif_neg h1, dif_neg h2, dif_neg h3, dif_neg hb1, dif_neg hb2, dif_neg hb3]
          exact congrArg Subtype.val (e₄.symm_apply_apply ⟨x, h4⟩)
  right_inv y := by
    dsimp only
    by_cases h1 : y ∈ B₁
    · rw [dif_pos h1, dif_pos (e₁.symm ⟨y, h1⟩).property]
      exact congrArg Subtype.val (e₁.apply_symm_apply ⟨y, h1⟩)
    · by_cases h2 : y ∈ B₂
      · have ha1 : (e₂.symm ⟨y, h2⟩).val ∉ A₁ :=
          Finset.disjoint_right.mp hA12 (e₂.symm ⟨y, h2⟩).property
        rw [dif_neg h1, dif_pos h2, dif_neg ha1, dif_pos (e₂.symm ⟨y, h2⟩).property]
        exact congrArg Subtype.val (e₂.apply_symm_apply ⟨y, h2⟩)
      · by_cases h3 : y ∈ B₃
        · have ha1 : (e₃.symm ⟨y, h3⟩).val ∉ A₁ :=
            Finset.disjoint_right.mp hA13 (e₃.symm ⟨y, h3⟩).property
          have ha2 : (e₃.symm ⟨y, h3⟩).val ∉ A₂ :=
            Finset.disjoint_right.mp hA23 (e₃.symm ⟨y, h3⟩).property
          rw [dif_neg h1, dif_neg h2, dif_pos h3, dif_neg ha1, dif_neg ha2,
              dif_pos (e₃.symm ⟨y, h3⟩).property]
          exact congrArg Subtype.val (e₃.apply_symm_apply ⟨y, h3⟩)
        · have h4 : y ∈ B₄ := by rcases hBcov y with h | h | h | h <;> tauto
          have ha1 : (e₄.symm ⟨y, h4⟩).val ∉ A₁ :=
            Finset.disjoint_right.mp hA14 (e₄.symm ⟨y, h4⟩).property
          have ha2 : (e₄.symm ⟨y, h4⟩).val ∉ A₂ :=
            Finset.disjoint_right.mp hA24 (e₄.symm ⟨y, h4⟩).property
          have ha3 : (e₄.symm ⟨y, h4⟩).val ∉ A₃ :=
            Finset.disjoint_right.mp hA34 (e₄.symm ⟨y, h4⟩).property
          rw [dif_neg h1, dif_neg h2, dif_neg h3, dif_neg ha1, dif_neg ha2, dif_neg ha3]
          exact congrArg Subtype.val (e₄.apply_symm_apply ⟨y, h4⟩)

/-- Helper finsets `IioFin n k = {i : Fin n | i.val < k}` and `IciFin n k = {i : Fin n | k ≤ i.val}`. -/
def IioFin (n k : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => i.val < k)
def IciFin (n k : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => k ≤ i.val)

lemma card_IioFin (n k : ℕ) (hk : k ≤ n) : (IioFin n k).card = k := by
  have hbij : (IioFin n k).card = (Finset.range k).card := by
    refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
    · intro i hi
      simp only [IioFin, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hi ⊢
      exact hi
    · intro i₁ _ i₂ _ h; exact Fin.ext h
    · intro m hm
      have hmk : m < k := Finset.mem_range.mp hm
      exact ⟨⟨m, by omega⟩, by simp [IioFin, hmk], rfl⟩
  rw [hbij, Finset.card_range]

lemma card_IciFin (n k : ℕ) (hk : k ≤ n) : (IciFin n k).card = n - k := by
  have hdisj : Disjoint (IioFin n k) (IciFin n k) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    simp only [IioFin, IciFin, Finset.mem_filter, Finset.mem_univ, true_and] at hi1 hi2
    omega
  have hunion : IioFin n k ∪ IciFin n k = Finset.univ := by
    ext i
    simp only [IioFin, IciFin, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      iff_true]
    omega
  have hcu := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.card_univ, Fintype.card_fin, card_IioFin n k hk] at hcu
  omega

/-! ### Exact Cardinality Lemma 1: `|G n c r|` -/

lemma card_G (n c r : ℕ) (hc : c ≤ n) (hr : r ≤ n) :
    (G n c r).card = ∑ a ∈ Finset.range (n + 1),
      c.choose a * (n - c).choose (r - a) * r.choose a * (n - r).choose (c - a) := by
  let B (a : ℕ) :=
    ((IioFin n c).powersetCard a ×ˢ (IciFin n c).powersetCard (r - a)) ×ˢ
    ((IioFin n r).powersetCard a ×ˢ (IciFin n r).powersetCard (c - a))
  let target := (Finset.range (n + 1)).sigma B
  have htarget_card : target.card = ∑ a ∈ Finset.range (n + 1),
      c.choose a * (n - c).choose (r - a) * r.choose a * (n - r).choose (c - a) := by
    rw [Finset.card_sigma]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [B, Finset.card_product, Finset.card_powersetCard,
      card_IioFin n c hc, card_IciFin n c hc, card_IioFin n r hr, card_IciFin n r hr]
    ring
  rw [← htarget_card]
  let toTuple (p : Equiv.Perm (Fin n)) :
      Σ _ : ℕ, (Finset (Fin n) × Finset (Fin n)) × (Finset (Fin n) × Finset (Fin n)) :=
    let IL := Finset.univ.filter (fun i : Fin n => i.val < c ∧ (p i).val < r)
    let IR := Finset.univ.filter (fun i : Fin n => c ≤ i.val ∧ (p i).val < r)
    let VL := Finset.univ.filter (fun v : Fin n => v.val < r ∧ (p.symm v).val < c)
    let VU := Finset.univ.filter (fun v : Fin n => r ≤ v.val ∧ (p.symm v).val < c)
    ⟨IL.card, ((IL, IR), (VL, VU))⟩
  refine Finset.card_bij (fun p _ => toTuple p) ?_ ?_ ?_
  · intro p _
    simp only [target, B, toTuple, Finset.mem_sigma, Finset.mem_range, Finset.mem_product,
      Finset.mem_powersetCard]
    set IL := Finset.univ.filter (fun i : Fin n => i.val < c ∧ (p i).val < r)
    set IR := Finset.univ.filter (fun i : Fin n => c ≤ i.val ∧ (p i).val < r)
    set VL := Finset.univ.filter (fun v : Fin n => v.val < r ∧ (p.symm v).val < c)
    set VU := Finset.univ.filter (fun v : Fin n => r ≤ v.val ∧ (p.symm v).val < c)
    have hIL_le : IL.card ≤ n := by
      calc IL.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ _)
        _ = n := by simp
    have hIL_eq_VL : IL.card = VL.card := by
      refine Finset.card_bij (fun i _ => p i) ?_ ?_ ?_
      · intro i hi
        simp only [IL, VL, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact ⟨hi.2, by simpa using hi.1⟩
      · intro i₁ _ i₂ _ h; exact p.injective h
      · intro v hv
        simp only [IL, VL, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        exact ⟨p.symm v, ⟨hv.2, by simpa using hv.1⟩, p.apply_symm_apply v⟩
    have hIL_IR : IL.card + IR.card = r := by
      have hdisj : Disjoint IL IR := by
        rw [Finset.disjoint_left]; intro i h1 h2
        simp only [IL, IR, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2; omega
      rw [← Finset.card_union_of_disjoint hdisj]
      have hbij : (IL ∪ IR).card = (IioFin n r).card := by
        refine Finset.card_bij (fun i _ => p i) ?_ ?_ ?_
        · intro i hi
          simp only [IL, IR, IioFin, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
            true_and] at hi ⊢
          rcases hi with h | h <;> exact h.2
        · intro i₁ _ i₂ _ h; exact p.injective h
        · intro v hv
          simp only [IioFin, Finset.mem_filter, Finset.mem_univ, true_and] at hv
          refine ⟨p.symm v, ?_, p.apply_symm_apply v⟩
          simp only [IL, IR, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases hlt : (p.symm v).val < c
          · left; exact ⟨hlt, by simpa using hv⟩
          · right; exact ⟨by omega, by simpa using hv⟩
      rw [hbij, card_IioFin n r hr]
    have hVL_VU : VL.card + VU.card = c := by
      have hdisj : Disjoint VL VU := by
        rw [Finset.disjoint_left]; intro v h1 h2
        simp only [VL, VU, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2; omega
      rw [← Finset.card_union_of_disjoint hdisj]
      have hbij : (VL ∪ VU).card = (IioFin n c).card := by
        refine Finset.card_bij (fun v _ => p.symm v) ?_ ?_ ?_
        · intro v hv
          simp only [VL, VU, IioFin, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
            true_and] at hv ⊢
          rcases hv with h | h <;> exact h.2
        · intro v₁ _ v₂ _ h; exact p.symm.injective h
        · intro i hi
          simp only [IioFin, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          refine ⟨p i, ?_, p.symm_apply_apply i⟩
          simp only [VL, VU, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases hlt : (p i).val < r
          · left; exact ⟨hlt, by simpa using hi⟩
          · right; exact ⟨by omega, by simpa using hi⟩
      rw [hbij, card_IioFin n c hc]
    refine ⟨by omega, ⟨⟨?_, trivial⟩, ⟨?_, by omega⟩⟩, ⟨⟨?_, hIL_eq_VL.symm⟩, ⟨?_, by omega⟩⟩⟩
    · intro i hi; simp only [IL, IioFin, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hi.1
    · intro i hi; simp only [IR, IciFin, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hi.1
    · intro v hv; simp only [VL, IioFin, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢; exact hv.1
    · intro v hv; simp only [VU, IciFin, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢; exact hv.1
  · -- Injectivity: same (IL, IR, VL, VU) and both in G n c r → p₁ = p₂
    intro p₁ hp₁ p₂ hp₂ heq
    have hg₁ : IsGrid c r p₁ := mem_G.mp hp₁
    have hg₂ : IsGrid c r p₂ := mem_G.mp hp₂
    have heq2 := (Sigma.mk.inj_iff.mp heq).2
    have hprod : ((Finset.univ.filter (fun i : Fin n => i.val < c ∧ (p₁ i).val < r),
                   Finset.univ.filter (fun i : Fin n => c ≤ i.val ∧ (p₁ i).val < r)),
                  (Finset.univ.filter (fun v : Fin n => v.val < r ∧ (p₁.symm v).val < c),
                   Finset.univ.filter (fun v : Fin n => r ≤ v.val ∧ (p₁.symm v).val < c))) =
                 ((Finset.univ.filter (fun i : Fin n => i.val < c ∧ (p₂ i).val < r),
                   Finset.univ.filter (fun i : Fin n => c ≤ i.val ∧ (p₂ i).val < r)),
                  (Finset.univ.filter (fun v : Fin n => v.val < r ∧ (p₂.symm v).val < c),
                   Finset.univ.filter (fun v : Fin n => r ≤ v.val ∧ (p₂.symm v).val < c))) :=
      eq_of_heq heq2
    simp only [Prod.mk.injEq] at hprod
    rcases hprod with ⟨⟨hIL, hIR⟩, ⟨hVL, hVU⟩⟩
    -- Helper: p₁ and p₂ agree on any cell where they share domain A and codomain B
    have h_cell_dec : ∀ (A B : Finset (Fin n)),
        (∀ x, x ∈ A ↔ p₁ x ∈ B) → (∀ x, x ∈ A ↔ p₂ x ∈ B) →
        (∀ i j, i ∈ A → j ∈ A → i < j → p₁ j < p₁ i) →
        (∀ i j, i ∈ A → j ∈ A → i < j → p₂ j < p₂ i) →
        ∀ x ∈ A, p₁ x = p₂ x := by
      intro A B hAB1 hAB2 hanti1 hanti2 x hx
      let f₁ : {i // i ∈ A} → {v // v ∈ B} := fun i => ⟨p₁ i.val, (hAB1 i.val).mp i.property⟩
      let f₂ : {i // i ∈ A} → {v // v ∈ B} := fun i => ⟨p₂ i.val, (hAB2 i.val).mp i.property⟩
      have hf₁ : Function.Bijective f₁ := by
        refine ⟨fun a b h => Subtype.ext (p₁.injective (congrArg Subtype.val h)), fun y => ?_⟩
        refine ⟨⟨p₁.symm y.val, (hAB1 (p₁.symm y.val)).mpr (by simp [y.property])⟩,
          Subtype.ext (p₁.apply_symm_apply y.val)⟩
      have hf₂ : Function.Bijective f₂ := by
        refine ⟨fun a b h => Subtype.ext (p₂.injective (congrArg Subtype.val h)), fun y => ?_⟩
        refine ⟨⟨p₂.symm y.val, (hAB2 (p₂.symm y.val)).mpr (by simp [y.property])⟩,
          Subtype.ext (p₂.apply_symm_apply y.val)⟩
      have huniq := strictAnti_bij_unique hf₁ hf₂
        (fun a b hab => hanti1 a.val b.val a.property b.property hab)
        (fun a b hab => hanti2 a.val b.val a.property b.property hab)
        ⟨x, hx⟩
      exact congrArg Subtype.val huniq
    have h_cell_inc : ∀ (A B : Finset (Fin n)),
        (∀ x, x ∈ A ↔ p₁ x ∈ B) → (∀ x, x ∈ A ↔ p₂ x ∈ B) →
        (∀ i j, i ∈ A → j ∈ A → i < j → p₁ i < p₁ j) →
        (∀ i j, i ∈ A → j ∈ A → i < j → p₂ i < p₂ j) →
        ∀ x ∈ A, p₁ x = p₂ x := by
      intro A B hAB1 hAB2 hmono1 hmono2 x hx
      let f₁ : {i // i ∈ A} → {v // v ∈ B} := fun i => ⟨p₁ i.val, (hAB1 i.val).mp i.property⟩
      let f₂ : {i // i ∈ A} → {v // v ∈ B} := fun i => ⟨p₂ i.val, (hAB2 i.val).mp i.property⟩
      have hf₁ : Function.Bijective f₁ := by
        refine ⟨fun a b h => Subtype.ext (p₁.injective (congrArg Subtype.val h)), fun y => ?_⟩
        refine ⟨⟨p₁.symm y.val, (hAB1 (p₁.symm y.val)).mpr (by simp [y.property])⟩,
          Subtype.ext (p₁.apply_symm_apply y.val)⟩
      have hf₂ : Function.Bijective f₂ := by
        refine ⟨fun a b h => Subtype.ext (p₂.injective (congrArg Subtype.val h)), fun y => ?_⟩
        refine ⟨⟨p₂.symm y.val, (hAB2 (p₂.symm y.val)).mpr (by simp [y.property])⟩,
          Subtype.ext (p₂.apply_symm_apply y.val)⟩
      have huniq := strictMono_bij_unique hf₁ hf₂
        (fun a b hab => hmono1 a.val b.val a.property b.property hab)
        (fun a b hab => hmono2 a.val b.val a.property b.property hab)
        ⟨x, hx⟩
      exact congrArg Subtype.val huniq
    ext x
    by_cases hxc : x.val < c
    · by_cases hxr : (p₁ x).val < r
      · -- Lower-left
        let A := Finset.univ.filter (fun i : Fin n => i.val < c ∧ (p₁ i).val < r)
        let B := Finset.univ.filter (fun v : Fin n => v.val < r ∧ (p₁.symm v).val < c)
        have h := h_cell_dec A B
          (fun i => by simp [A, B, and_comm])
          (fun i => by dsimp only [A, B]; rw [hIL, hVL]; simp [and_comm])
          (fun i j hi hj hij => by
            simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
            have hnot : ¬ (p₁ i < p₁ j) := fun hlt => by
              have := (hg₁ i j hij (by omega) (by omega)).mp hlt; omega
            have hne : p₁ i ≠ p₁ j := fun heq => absurd (p₁.injective heq) (ne_of_lt hij)
            exact lt_of_le_of_ne (le_of_not_gt hnot) hne.symm)
          (fun i j hi hj hij => by
            dsimp only [A] at hi hj
            rw [hIL] at hi hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
            have hnot : ¬ (p₂ i < p₂ j) := fun hlt => by
              have := (hg₂ i j hij (by omega) (by omega)).mp hlt; omega
            have hne : p₂ i ≠ p₂ j := fun heq => absurd (p₂.injective heq) (ne_of_lt hij)
            exact lt_of_le_of_ne (le_of_not_gt hnot) hne.symm)
          x (by simp [A, hxc, hxr])
        exact congrArg Fin.val h
      · -- Upper-left
        let A := Finset.univ.filter (fun i : Fin n => i.val < c ∧ r ≤ (p₁ i).val)
        let B := Finset.univ.filter (fun v : Fin n => r ≤ v.val ∧ (p₁.symm v).val < c)
        have hAeq : A = Finset.univ.filter (fun i : Fin n => i.val < c ∧ r ≤ (p₂ i).val) := by
          ext i
          have hmem := Finset.ext_iff.mp hIL i
          simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
          omega
        have h := h_cell_inc A B
          (fun i => by simp [A, B, and_comm])
          (fun i => by dsimp only [B]; rw [hAeq, hVU]; simp [and_comm])
          (fun i j hi hj hij => by
            simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
            exact (hg₁ i j hij (by omega) (by omega)).mpr hi.2)
          (fun i j hi hj hij => by
            rw [hAeq] at hi hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
            exact (hg₂ i j hij (by omega) (by omega)).mpr hi.2)
          x (by simp [A, hxc]; omega)
        exact congrArg Fin.val h
    · by_cases hxr : (p₁ x).val < r
      · -- Lower-right
        let A := Finset.univ.filter (fun i : Fin n => c ≤ i.val ∧ (p₁ i).val < r)
        let B := Finset.univ.filter (fun v : Fin n => v.val < r ∧ c ≤ (p₁.symm v).val)
        have hBeq : B = Finset.univ.filter (fun v : Fin n => v.val < r ∧ c ≤ (p₂.symm v).val) := by
          ext v
          have hmem := Finset.ext_iff.mp hVL v
          simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
          omega
        have h := h_cell_dec A B
          (fun i => by simp [A, B, and_comm])
          (fun i => by dsimp only [A]; rw [hIR, hBeq]; simp [and_comm])
          (fun i j hi hj hij => by
            simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
            have hnot : ¬ (p₁ i < p₁ j) := fun hlt => by
              have := (hg₁ i j hij (by omega) (by omega)).mp hlt; omega
            have hne : p₁ i ≠ p₁ j := fun heq => absurd (p₁.injective heq) (ne_of_lt hij)
            exact lt_of_le_of_ne (le_of_not_gt hnot) hne.symm)
          (fun i j hi hj hij => by
            dsimp only [A] at hi hj
            rw [hIR] at hi hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
            have hnot : ¬ (p₂ i < p₂ j) := fun hlt => by
              have := (hg₂ i j hij (by omega) (by omega)).mp hlt; omega
            have hne : p₂ i ≠ p₂ j := fun heq => absurd (p₂.injective heq) (ne_of_lt hij)
            exact lt_of_le_of_ne (le_of_not_gt hnot) hne.symm)
          x (by simp [A, hxr]; omega)
        exact congrArg Fin.val h
      · -- Upper-right
        let A := Finset.univ.filter (fun i : Fin n => c ≤ i.val ∧ r ≤ (p₁ i).val)
        let B := Finset.univ.filter (fun v : Fin n => r ≤ v.val ∧ c ≤ (p₁.symm v).val)
        have hAeq : A = Finset.univ.filter (fun i : Fin n => c ≤ i.val ∧ r ≤ (p₂ i).val) := by
          ext i
          have hmem := Finset.ext_iff.mp hIR i
          simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
          omega
        have hBeq : B = Finset.univ.filter (fun v : Fin n => r ≤ v.val ∧ c ≤ (p₂.symm v).val) := by
          ext v
          have hmem := Finset.ext_iff.mp hVU v
          simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
          omega
        have h := h_cell_inc A B
          (fun i => by simp [A, B, and_comm])
          (fun i => by rw [hAeq, hBeq]; simp [and_comm])
          (fun i j hi hj hij => by
            simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
            exact (hg₁ i j hij (by omega) (by omega)).mpr hi.2)
          (fun i j hi hj hij => by
            rw [hAeq] at hi hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
            exact (hg₂ i j hij (by omega) (by omega)).mpr hi.2)
          x (by simp [A]; omega)
        exact congrArg Fin.val h
  · -- Surjectivity: glue the 4 monotone bijections!
    rintro ⟨a, ⟨⟨IL, IR⟩, ⟨VL, VU⟩⟩⟩ hmem
    simp only [target, B, Finset.mem_sigma, Finset.mem_range, Finset.mem_product,
      Finset.mem_powersetCard] at hmem
    rcases hmem with ⟨ha_lt, ⟨⟨hIL_sub, hIL_card⟩, ⟨hIR_sub, hIR_card⟩⟩,
      ⟨⟨hVL_sub, hVL_card⟩, ⟨hVU_sub, hVU_card⟩⟩⟩
    have hac : a ≤ c := by
      calc a = IL.card := hIL_card.symm
        _ ≤ (IioFin n c).card := Finset.card_le_card hIL_sub
        _ = c := card_IioFin n c hc
    have har : a ≤ r := by
      calc a = VL.card := hVL_card.symm
        _ ≤ (IioFin n r).card := Finset.card_le_card hVL_sub
        _ = r := card_IioFin n r hr
    have hra_nc : r - a ≤ n - c := by
      calc r - a = IR.card := hIR_card.symm
        _ ≤ (IciFin n c).card := Finset.card_le_card hIR_sub
        _ = n - c := card_IciFin n c hc
    have hca_nr : c - a ≤ n - r := by
      calc c - a = VU.card := hVU_card.symm
        _ ≤ (IciFin n r).card := Finset.card_le_card hVU_sub
        _ = n - r := card_IciFin n r hr
    let A₁ := IL
    let A₂ := IioFin n c \ IL
    let A₃ := IR
    let A₄ := IciFin n c \ IR
    let B₁ := VL
    let B₂ := VU
    let B₃ := IioFin n r \ VL
    let B₄ := IciFin n r \ VU
    have hc1 : A₁.card = B₁.card := by dsimp only [A₁, B₁]; omega
    have hc2 : A₂.card = B₂.card := by
      dsimp only [A₂, B₂]; rw [Finset.card_sdiff_of_subset hIL_sub, card_IioFin n c hc]; omega
    have hc3 : A₃.card = B₃.card := by
      dsimp only [A₃, B₃]; rw [Finset.card_sdiff_of_subset hVL_sub, card_IioFin n r hr]; omega
    have hc4 : A₄.card = B₄.card := by
      dsimp only [A₄, B₄]
      rw [Finset.card_sdiff_of_subset hIR_sub, Finset.card_sdiff_of_subset hVU_sub,
          card_IciFin n c hc, card_IciFin n r hr]
      omega
    have hA12 : Disjoint A₁ A₂ := Finset.disjoint_sdiff
    have hA13 : Disjoint A₁ A₃ := Finset.disjoint_left.mpr fun x h1 h3 => by
      have hx1 := hIL_sub h1; have hx3 := hIR_sub h3
      simp only [IioFin, IciFin, Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx3; omega
    have hA14 : Disjoint A₁ A₄ := Finset.disjoint_left.mpr fun x h1 h4 => by
      have hx1 := hIL_sub h1; have hx4 := (Finset.mem_sdiff.mp h4).1
      simp only [IioFin, IciFin, Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx4; omega
    have hA23 : Disjoint A₂ A₃ := Finset.disjoint_left.mpr fun x h2 h3 => by
      have hx2 := (Finset.mem_sdiff.mp h2).1; have hx3 := hIR_sub h3
      simp only [IioFin, IciFin, Finset.mem_filter, Finset.mem_univ, true_and] at hx2 hx3; omega
    have hA24 : Disjoint A₂ A₄ := Finset.disjoint_left.mpr fun x h2 h4 => by
      have hx2 := (Finset.mem_sdiff.mp h2).1; have hx4 := (Finset.mem_sdiff.mp h4).1
      simp only [IioFin, IciFin, Finset.mem_filter, Finset.mem_univ, true_and] at hx2 hx4; omega
    have hA34 : Disjoint A₃ A₄ := Finset.disjoint_sdiff
    have hAcov : ∀ x : Fin n, x ∈ A₁ ∨ x ∈ A₂ ∨ x ∈ A₃ ∨ x ∈ A₄ := by
      intro x
      by_cases hxc : x.val < c
      · by_cases hx : x ∈ IL
        · exact Or.inl hx
        · exact Or.inr (Or.inl (Finset.mem_sdiff.mpr ⟨by simp [IioFin, hxc], hx⟩))
      · by_cases hx : x ∈ IR
        · exact Or.inr (Or.inr (Or.inl hx))
        · exact Or.inr (Or.inr (Or.inr (Finset.mem_sdiff.mpr ⟨by simp [IciFin]; omega, hx⟩)))
    have hB12 : Disjoint B₁ B₂ := Finset.disjoint_left.mpr fun y h1 h2 => by
      have hy1 := hVL_sub h1; have hy2 := hVU_sub h2
      simp only [IioFin, IciFin, Finset.mem_filter, Finset.mem_univ, true_and] at hy1 hy2; omega
    have hB13 : Disjoint B₁ B₃ := Finset.disjoint_sdiff
    have hB14 : Disjoint B₁ B₄ := Finset.disjoint_left.mpr fun y h1 h4 => by
      have hy1 := hVL_sub h1; have hy4 := (Finset.mem_sdiff.mp h4).1
      simp only [IioFin, IciFin, Finset.mem_filter, Finset.mem_univ, true_and] at hy1 hy4; omega
    have hB23 : Disjoint B₂ B₃ := Finset.disjoint_left.mpr fun y h2 h3 => by
      have hy2 := hVU_sub h2; have hy3 := (Finset.mem_sdiff.mp h3).1
      simp only [IioFin, IciFin, Finset.mem_filter, Finset.mem_univ, true_and] at hy2 hy3; omega
    have hB24 : Disjoint B₂ B₄ := Finset.disjoint_sdiff
    have hB34 : Disjoint B₃ B₄ := Finset.disjoint_left.mpr fun y h3 h4 => by
      have hy3 := (Finset.mem_sdiff.mp h3).1; have hy4 := (Finset.mem_sdiff.mp h4).1
      simp only [IioFin, IciFin, Finset.mem_filter, Finset.mem_univ, true_and] at hy3 hy4; omega
    have hBcov : ∀ y : Fin n, y ∈ B₁ ∨ y ∈ B₂ ∨ y ∈ B₃ ∨ y ∈ B₄ := by
      intro y
      by_cases hyr : y.val < r
      · by_cases hy : y ∈ VL
        · exact Or.inl hy
        · exact Or.inr (Or.inr (Or.inl (Finset.mem_sdiff.mpr ⟨by simp [IioFin, hyr], hy⟩)))
      · by_cases hy : y ∈ VU
        · exact Or.inr (Or.inl hy)
        · exact Or.inr (Or.inr (Or.inr (Finset.mem_sdiff.mpr ⟨by simp [IciFin]; omega, hy⟩)))
    let e₁ := decBij A₁ B₁ hc1
    let e₂ := incBij A₂ B₂ hc2
    let e₃ := decBij A₃ B₃ hc3
    let e₄ := incBij A₄ B₄ hc4
    let p := glue4 A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄
      hA12 hA13 hA14 hA23 hA24 hA34 hAcov
      hB12 hB13 hB14 hB23 hB24 hB34 hBcov e₁ e₂ e₃ e₄
    have hp1 : ∀ x (hx : x ∈ A₁), p x = (e₁ ⟨x, hx⟩).val := fun x hx => by
      change (if h1 : x ∈ A₁ then (e₁ ⟨x, h1⟩).val else _) = _
      rw [dif_pos hx]
    have hp2 : ∀ x (hx : x ∈ A₂), p x = (e₂ ⟨x, hx⟩).val := fun x hx => by
      have h1 : x ∉ A₁ := Finset.disjoint_right.mp hA12 hx
      change (if h1 : x ∈ A₁ then _ else if h2 : x ∈ A₂ then (e₂ ⟨x, h2⟩).val else _) = _
      rw [dif_neg h1, dif_pos hx]
    have hp3 : ∀ x (hx : x ∈ A₃), p x = (e₃ ⟨x, hx⟩).val := fun x hx => by
      have h1 : x ∉ A₁ := Finset.disjoint_right.mp hA13 hx
      have h2 : x ∉ A₂ := Finset.disjoint_right.mp hA23 hx
      change (if h1 : x ∈ A₁ then _ else if h2 : x ∈ A₂ then _ else
        if h3 : x ∈ A₃ then (e₃ ⟨x, h3⟩).val else _) = _
      rw [dif_neg h1, dif_neg h2, dif_pos hx]
    have hp4 : ∀ x (hx : x ∈ A₄), p x = (e₄ ⟨x, hx⟩).val := fun x hx => by
      have h1 : x ∉ A₁ := Finset.disjoint_right.mp hA14 hx
      have h2 : x ∉ A₂ := Finset.disjoint_right.mp hA24 hx
      have h3 : x ∉ A₃ := Finset.disjoint_right.mp hA34 hx
      change (if h1 : x ∈ A₁ then _ else if h2 : x ∈ A₂ then _ else
        if h3 : x ∈ A₃ then _ else (e₄ ⟨x, _⟩).val) = _
      rw [dif_neg h1, dif_neg h2, dif_neg h3]
    have hpmem1 : ∀ x ∈ A₁, (p x).val < r := fun x hx => by
      rw [hp1 x hx]; have := hVL_sub (e₁ ⟨x, hx⟩).property
      simp only [IioFin, Finset.mem_filter, Finset.mem_univ, true_and] at this; exact this
    have hpmem2 : ∀ x ∈ A₂, r ≤ (p x).val := fun x hx => by
      rw [hp2 x hx]; have := hVU_sub (e₂ ⟨x, hx⟩).property
      simp only [IciFin, Finset.mem_filter, Finset.mem_univ, true_and] at this; exact this
    have hpmem3 : ∀ x ∈ A₃, (p x).val < r := fun x hx => by
      rw [hp3 x hx]; have := (Finset.mem_sdiff.mp (e₃ ⟨x, hx⟩).property).1
      simp only [IioFin, Finset.mem_filter, Finset.mem_univ, true_and] at this; exact this
    have hpmem4 : ∀ x ∈ A₄, r ≤ (p x).val := fun x hx => by
      rw [hp4 x hx]; have := (Finset.mem_sdiff.mp (e₄ ⟨x, hx⟩).property).1
      simp only [IciFin, Finset.mem_filter, Finset.mem_univ, true_and] at this; exact this
    have hp_grid : IsGrid c r p := by
      intro i j hij hcol hrow
      by_cases hic : i.val < c
      · have hjc : j.val < c := hcol.mp hic
        by_cases hi : i ∈ A₁
        · have hpi : (p i).val < r := hpmem1 i hi
          have hpj : (p j).val < r := hrow.mp hpi
          have hj : j ∈ A₁ := by
            by_contra hj_not
            have hj2 : j ∈ A₂ := Finset.mem_sdiff.mpr ⟨by simp [IioFin, hjc], hj_not⟩
            have := hpmem2 j hj2; omega
          have hgt : p j < p i := by
            rw [hp1 i hi, hp1 j hj]
            exact decBij_strictAnti A₁ B₁ hc1 hij
          exact ⟨fun hlt => absurd hlt (not_lt_of_gt hgt), fun hle => by omega⟩
        · have hi2 : i ∈ A₂ := Finset.mem_sdiff.mpr ⟨by simp [IioFin, hic], hi⟩
          have hpi : r ≤ (p i).val := hpmem2 i hi2
          have hpj : r ≤ (p j).val := by omega
          have hj2 : j ∈ A₂ := by
            refine Finset.mem_sdiff.mpr ⟨by simp [IioFin, hjc], ?_⟩
            intro hj1; have := hpmem1 j hj1; omega
          have hlt : p i < p j := by
            rw [hp2 i hi2, hp2 j hj2]
            exact incBij_strictMono A₂ B₂ hc2 hij
          exact ⟨fun _ => hpi, fun _ => hlt⟩
      · have hjc : ¬ (j.val < c) := fun h => hic (hcol.mpr h)
        by_cases hi : i ∈ A₃
        · have hpi : (p i).val < r := hpmem3 i hi
          have hpj : (p j).val < r := hrow.mp hpi
          have hj : j ∈ A₃ := by
            by_contra hj_not
            have hj4 : j ∈ A₄ := Finset.mem_sdiff.mpr ⟨by simp [IciFin]; omega, hj_not⟩
            have := hpmem4 j hj4; omega
          have hgt : p j < p i := by
            rw [hp3 i hi, hp3 j hj]
            exact decBij_strictAnti A₃ B₃ hc3 hij
          exact ⟨fun hlt => absurd hlt (not_lt_of_gt hgt), fun hle => by omega⟩
        · have hi4 : i ∈ A₄ := Finset.mem_sdiff.mpr ⟨by simp [IciFin]; omega, hi⟩
          have hpi : r ≤ (p i).val := hpmem4 i hi4
          have hpj : r ≤ (p j).val := by omega
          have hj4 : j ∈ A₄ := by
            refine Finset.mem_sdiff.mpr ⟨by simp [IciFin]; omega, ?_⟩
            intro hj3; have := hpmem3 j hj3; omega
          have hlt : p i < p j := by
            rw [hp4 i hi4, hp4 j hj4]
            exact incBij_strictMono A₄ B₄ hc4 hij
          exact ⟨fun _ => hpi, fun _ => hlt⟩
    refine ⟨p, mem_G.mpr hp_grid, ?_⟩
    have hIL' : Finset.univ.filter (fun i : Fin n => i.val < c ∧ (p i).val < r) = IL := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro ⟨hic, hir⟩
        by_contra hnot
        have hi2 : i ∈ A₂ := Finset.mem_sdiff.mpr ⟨by simp [IioFin, hic], hnot⟩
        have := hpmem2 i hi2; omega
      · intro hi
        have hx := hIL_sub hi
        simp only [IioFin, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        exact ⟨hx, hpmem1 i hi⟩
    have hIR' : Finset.univ.filter (fun i : Fin n => c ≤ i.val ∧ (p i).val < r) = IR := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro ⟨hic, hir⟩
        by_contra hnot
        have hi4 : i ∈ A₄ := Finset.mem_sdiff.mpr ⟨by simp [IciFin, hic], hnot⟩
        have := hpmem4 i hi4; omega
      · intro hi
        have hx := hIR_sub hi
        simp only [IciFin, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        exact ⟨hx, hpmem3 i hi⟩
    have hVL' : Finset.univ.filter (fun v : Fin n => v.val < r ∧ (p.symm v).val < c) = VL := by
      ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro ⟨hvr, hvc⟩
        have h1 : p.symm v ∈ A₁ := by
          dsimp only [A₁]
          rw [← hIL']
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hvc, by simpa using hvr⟩
        have := hp1 (p.symm v) h1
        rw [p.apply_symm_apply] at this
        rw [this]; exact (e₁ ⟨p.symm v, h1⟩).property
      · intro hv
        have hy := hVL_sub hv
        simp only [IioFin, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        refine ⟨hy, ?_⟩
        have hsymm : p.symm v = (e₁.symm ⟨v, hv⟩).val := by
          change (if h1 : v ∈ B₁ then (e₁.symm ⟨v, h1⟩).val else _) = _
          rw [dif_pos hv]
        rw [hsymm]
        have := hIL_sub (e₁.symm ⟨v, hv⟩).property
        simp only [IioFin, Finset.mem_filter, Finset.mem_univ, true_and] at this; exact this
    have hVU' : Finset.univ.filter (fun v : Fin n => r ≤ v.val ∧ (p.symm v).val < c) = VU := by
      ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro ⟨hvr, hvc⟩
        have h2 : p.symm v ∈ A₂ := by
          refine Finset.mem_sdiff.mpr ⟨by simp [IioFin, hvc], ?_⟩
          intro h1; have := hpmem1 (p.symm v) h1; rw [p.apply_symm_apply] at this; omega
        have := hp2 (p.symm v) h2
        rw [p.apply_symm_apply] at this
        rw [this]; exact (e₂ ⟨p.symm v, h2⟩).property
      · intro hv
        have hy := hVU_sub hv
        simp only [IciFin, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        refine ⟨hy, ?_⟩
        have hb1 : v ∉ B₁ := Finset.disjoint_right.mp hB12 hv
        have hsymm : p.symm v = (e₂.symm ⟨v, hv⟩).val := by
          change (if h1 : v ∈ B₁ then _ else if h2 : v ∈ B₂ then (e₂.symm ⟨v, h2⟩).val else _) = _
          rw [dif_neg hb1, dif_pos hv]
        rw [hsymm]
        have := (Finset.mem_sdiff.mp (e₂.symm ⟨v, hv⟩).property).1
        simp only [IioFin, Finset.mem_filter, Finset.mem_univ, true_and] at this; exact this
    simp only [toTuple, hIL', hIR', hVL', hVU', hIL_card]

/-! ### Helper: Insertion bijection `insPerm` for deleting one fixed `(i₀, v₀)` -/

/-- Insert `(i₀, v₀)` into a permutation `q : Perm (Fin n)` to get `Perm (Fin (n + 1))`. -/
def insPerm {n : ℕ} (i₀ v₀ : Fin (n + 1)) (q : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) where
  toFun := i₀.insertNth v₀ (fun i => v₀.succAbove (q i))
  invFun := v₀.insertNth i₀ (fun j => i₀.succAbove (q.symm j))
  left_inv x := by
    refine Fin.succAboveCases i₀ ?_ ?_ x
    · simp
    · intro i; simp
  right_inv y := by
    refine Fin.succAboveCases v₀ ?_ ?_ y
    · simp
    · intro j; simp

lemma insPerm_self {n : ℕ} (i₀ v₀ : Fin (n + 1)) (q : Equiv.Perm (Fin n)) :
    insPerm i₀ v₀ q i₀ = v₀ := by
  simp [insPerm]

lemma insPerm_succAbove {n : ℕ} (i₀ v₀ : Fin (n + 1)) (q : Equiv.Perm (Fin n)) (i : Fin n) :
    insPerm i₀ v₀ q (i₀.succAbove i) = v₀.succAbove (q i) := by
  simp [insPerm]

lemma insPerm_injective {n : ℕ} (i₀ v₀ : Fin (n + 1)) :
    Function.Injective (insPerm i₀ v₀) := by
  intro q₁ q₂ h
  ext i
  have hi := congrArg (fun p => p (i₀.succAbove i)) h
  simp only [insPerm_succAbove] at hi
  exact congrArg Fin.val (Fin.succAbove_right_injective hi)

lemma exists_insPerm_of_apply {n : ℕ} (i₀ v₀ : Fin (n + 1)) (p : Equiv.Perm (Fin (n + 1)))
    (hp : p i₀ = v₀) : ∃ q : Equiv.Perm (Fin n), insPerm i₀ v₀ q = p := by
  -- Extract the induced bijection on Fin n using Fin.predAbove / Fin.exists_succAbove_eq
  have hne : ∀ i : Fin n, p (i₀.succAbove i) ≠ v₀ := fun i h => by
    have := p.injective (h.trans hp.symm)
    exact Fin.succAbove_ne i₀ i this
  have hne' : ∀ j : Fin n, p.symm (v₀.succAbove j) ≠ i₀ := fun j h => by
    have := congrArg p h
    rw [p.apply_symm_apply, hp] at this
    exact Fin.succAbove_ne v₀ j this
  let fwd : Fin n → Fin n := fun i => Classical.choose (Fin.exists_succAbove_eq (hne i))
  let bwd : Fin n → Fin n := fun j => Classical.choose (Fin.exists_succAbove_eq (hne' j))
  have hfwd : ∀ i, v₀.succAbove (fwd i) = p (i₀.succAbove i) :=
    fun i => Classical.choose_spec (Fin.exists_succAbove_eq (hne i))
  have hbwd : ∀ j, i₀.succAbove (bwd j) = p.symm (v₀.succAbove j) :=
    fun j => Classical.choose_spec (Fin.exists_succAbove_eq (hne' j))
  let q : Equiv.Perm (Fin n) :=
    { toFun := fwd
      invFun := bwd
      left_inv := fun i => Fin.succAbove_right_injective (by rw [hbwd, hfwd, p.symm_apply_apply])
      right_inv := fun j => Fin.succAbove_right_injective (by rw [hfwd, hbwd, p.apply_symm_apply]) }
  refine ⟨q, ?_⟩
  ext x
  refine Fin.succAboveCases i₀ ?_ ?_ x
  · rw [insPerm_self, hp]
  · intro i; rw [insPerm_succAbove]; exact congrArg Fin.val (hfwd i)

lemma succAbove_zero_val {n : ℕ} (i : Fin n) : ((0 : Fin (n + 1)).succAbove i).val = i.val + 1 := by
  simp [Fin.succAbove]

lemma succAbove_lt_iff {n : ℕ} (k : Fin (n + 1)) (i : Fin n) :
    (k.succAbove i).val < k.val ↔ i.val < k.val := by
  simp only [Fin.succAbove]
  split_ifs with h
  · have : i.val < k.val := by
      have : (i.castSucc : Fin (n + 1)) < k := h
      exact this
    simp [this]
  · have : k.val ≤ i.val := by
      have : ¬ (i.castSucc < k) := h
      simp only [Fin.lt_def, Fin.val_castSucc] at this
      omega
    simp only [Fin.val_succ]
    omega

/-- Pullback of `IsGrid` along `insPerm` at `i₀ = 0, v₀ = r` (with `1 ≤ c`). -/
lemma isGrid_insPerm_zero_iff {n c r : ℕ} (hc : 1 ≤ c) (hr : r ≤ n) (q : Equiv.Perm (Fin n)) :
    (IsGrid c r (insPerm 0 ⟨r, by omega⟩ q) ∧ IsGrid c (r + 1) (insPerm 0 ⟨r, by omega⟩ q)) ↔
      IsGrid (c - 1) r q := by
  set v₀ : Fin (n + 1) := ⟨r, by omega⟩
  set p := insPerm 0 v₀ q
  have hcol0 : ∀ i : Fin n, ((0 : Fin (n + 1)).succAbove i).val < c ↔ i.val < c - 1 := by
    intro i; rw [succAbove_zero_val]; omega
  have hrow0 : ∀ i : Fin n, (p ((0 : Fin (n + 1)).succAbove i)).val < r ↔ (q i).val < r := by
    intro i; rw [insPerm_succAbove]; exact succAbove_lt_iff v₀ (q i)
  have hrow1 : ∀ i : Fin n, (p ((0 : Fin (n + 1)).succAbove i)).val < r + 1 ↔ (q i).val < r := by
    intro i
    rw [insPerm_succAbove]
    have hne : v₀.succAbove (q i) ≠ v₀ := Fin.succAbove_ne v₀ (q i)
    have hval_ne : (v₀.succAbove (q i)).val ≠ r := fun h => hne (Fin.ext h)
    have hlt := succAbove_lt_iff v₀ (q i)
    change (v₀.succAbove (q i)).val < r ↔ (q i).val < r at hlt
    omega
  constructor
  · intro ⟨h1, _⟩ i j hij hcol hrow
    have hij' : (0 : Fin (n + 1)).succAbove i < (0 : Fin (n + 1)).succAbove j :=
      Fin.succAbove_lt_succAbove_iff.mpr hij
    have hcol' : ((0 : Fin (n + 1)).succAbove i).val < c ↔ ((0 : Fin (n + 1)).succAbove j).val < c := by
      rw [hcol0, hcol0]; exact hcol
    have hrow' : (p ((0 : Fin (n + 1)).succAbove i)).val < r ↔
        (p ((0 : Fin (n + 1)).succAbove j)).val < r := by
      rw [hrow0, hrow0]; exact hrow
    have h := h1 _ _ hij' hcol' hrow'
    rw [insPerm_succAbove, insPerm_succAbove, Fin.succAbove_lt_succAbove_iff] at h
    have hi_r := hrow0 i
    rw [insPerm_succAbove] at hi_r
    omega
  · intro hq
    constructor
    · intro x y
      refine Fin.succAboveCases 0 ?_ ?_ x
      · refine Fin.succAboveCases 0 ?_ ?_ y
        · intro hxy _ _; exact absurd hxy (lt_irrefl _)
        · intro j hxy _ hrow
          have hp0 : (p 0).val = r := by simp [p, insPerm_self, v₀]
          have hne : p ((0 : Fin (n + 1)).succAbove j) ≠ p 0 :=
            fun h => absurd (p.injective h) (ne_of_gt hxy)
          have hval_ne : (p ((0 : Fin (n + 1)).succAbove j)).val ≠ r :=
            fun h => hne (Fin.ext (by omega))
          have hpy : r ≤ (p ((0 : Fin (n + 1)).succAbove j)).val := by omega
          exact ⟨fun _ => by omega, fun _ => Fin.lt_def.mpr (by omega)⟩
      · intro i
        refine Fin.succAboveCases 0 ?_ ?_ y
        · intro hxy _ _; exfalso; exact not_lt_of_ge (Fin.zero_le _) hxy
        · intro j hxy hcol hrow
          have hij : i < j := Fin.succAbove_lt_succAbove_iff.mp hxy
          have hcol' : i.val < c - 1 ↔ j.val < c - 1 := by
            rw [← hcol0, ← hcol0]; exact hcol
          have hrow' : (q i).val < r ↔ (q j).val < r := by
            rw [← hrow0, ← hrow0]; exact hrow
          have h := hq i j hij hcol' hrow'
          rw [insPerm_succAbove, insPerm_succAbove, Fin.succAbove_lt_succAbove_iff]
          have hi_r := hrow0 i
          rw [insPerm_succAbove] at hi_r
          omega
    · intro x y
      refine Fin.succAboveCases 0 ?_ ?_ x
      · refine Fin.succAboveCases 0 ?_ ?_ y
        · intro hxy _ _; exact absurd hxy (lt_irrefl _)
        · intro j hxy _ hrow
          have hp0 : (p 0).val = r := by simp [p, insPerm_self, v₀]
          have hne : p ((0 : Fin (n + 1)).succAbove j) ≠ p 0 :=
            fun h => absurd (p.injective h) (ne_of_gt hxy)
          have hval_ne : (p ((0 : Fin (n + 1)).succAbove j)).val ≠ r :=
            fun h => hne (Fin.ext (by omega))
          have hpy : (p ((0 : Fin (n + 1)).succAbove j)).val < r + 1 := hrow.mp (by omega)
          have hgt : p ((0 : Fin (n + 1)).succAbove j) < p 0 := Fin.lt_def.mpr (by omega)
          exact ⟨fun hlt => absurd hlt (not_lt_of_gt hgt), fun hle => by omega⟩
      · intro i
        refine Fin.succAboveCases 0 ?_ ?_ y
        · intro hxy _ _; exfalso; exact not_lt_of_ge (Fin.zero_le _) hxy
        · intro j hxy hcol hrow
          have hij : i < j := Fin.succAbove_lt_succAbove_iff.mp hxy
          have hcol' : i.val < c - 1 ↔ j.val < c - 1 := by
            rw [← hcol0, ← hcol0]; exact hcol
          have hrow' : (q i).val < r ↔ (q j).val < r := by
            rw [← hrow1, ← hrow1]; exact hrow
          have h := hq i j hij hcol' hrow'
          rw [insPerm_succAbove, insPerm_succAbove, Fin.succAbove_lt_succAbove_iff]
          have hi_r := hrow1 i
          rw [insPerm_succAbove] at hi_r
          omega

/-- Pullback of `IsGrid` along `insPerm` at `i₀ = c, v₀ = r` (with `c ≤ n`). -/
lemma isGrid_insPerm_c_iff {n c r : ℕ} (hc : c ≤ n) (hr : r ≤ n) (q : Equiv.Perm (Fin n)) :
    (IsGrid c r (insPerm ⟨c, by omega⟩ ⟨r, by omega⟩ q) ∧
     IsGrid c (r + 1) (insPerm ⟨c, by omega⟩ ⟨r, by omega⟩ q)) ↔
      IsGrid c r q := by
  set i₀ : Fin (n + 1) := ⟨c, by omega⟩
  set v₀ : Fin (n + 1) := ⟨r, by omega⟩
  set p := insPerm i₀ v₀ q
  have hcol0 : ∀ i : Fin n, (i₀.succAbove i).val < c ↔ i.val < c :=
    fun i => succAbove_lt_iff i₀ i
  have hrow0 : ∀ i : Fin n, (p (i₀.succAbove i)).val < r ↔ (q i).val < r := by
    intro i; rw [insPerm_succAbove]; exact succAbove_lt_iff v₀ (q i)
  have hrow1 : ∀ i : Fin n, (p (i₀.succAbove i)).val < r + 1 ↔ (q i).val < r := by
    intro i
    rw [insPerm_succAbove]
    have hne : v₀.succAbove (q i) ≠ v₀ := Fin.succAbove_ne v₀ (q i)
    have hval_ne : (v₀.succAbove (q i)).val ≠ r := fun h => hne (Fin.ext h)
    have hlt := succAbove_lt_iff v₀ (q i)
    change (v₀.succAbove (q i)).val < r ↔ (q i).val < r at hlt
    omega
  constructor
  · intro ⟨h1, _⟩ i j hij hcol hrow
    have hij' : i₀.succAbove i < i₀.succAbove j := Fin.succAbove_lt_succAbove_iff.mpr hij
    have hcol' : (i₀.succAbove i).val < c ↔ (i₀.succAbove j).val < c := by
      rw [hcol0, hcol0]; exact hcol
    have hrow' : (p (i₀.succAbove i)).val < r ↔ (p (i₀.succAbove j)).val < r := by
      rw [hrow0, hrow0]; exact hrow
    have h := h1 _ _ hij' hcol' hrow'
    rw [insPerm_succAbove, insPerm_succAbove, Fin.succAbove_lt_succAbove_iff] at h
    have hi_r := hrow0 i
    rw [insPerm_succAbove] at hi_r
    omega
  · intro hq
    constructor
    · intro x y
      refine Fin.succAboveCases i₀ ?_ ?_ x
      · refine Fin.succAboveCases i₀ ?_ ?_ y
        · intro hxy _ _; exact absurd hxy (lt_irrefl _)
        · intro j hxy _ hrow
          have hp0 : (p i₀).val = r := by simp [p, insPerm_self, v₀]
          have hne : p (i₀.succAbove j) ≠ p i₀ := fun h => absurd (p.injective h) (ne_of_gt hxy)
          have hval_ne : (p (i₀.succAbove j)).val ≠ r := fun h => hne (Fin.ext (by omega))
          have hpy : r ≤ (p (i₀.succAbove j)).val := by omega
          exact ⟨fun _ => by omega, fun _ => Fin.lt_def.mpr (by omega)⟩
      · intro i
        refine Fin.succAboveCases i₀ ?_ ?_ y
        · intro hxy hcol _
          exfalso
          have hlt : (i₀.succAbove i).val < c := hxy
          have hnot : ¬ (i₀.val < c) := by simp [i₀]
          exact hnot (hcol.mp hlt)
        · intro j hxy hcol hrow
          have hij : i < j := Fin.succAbove_lt_succAbove_iff.mp hxy
          have hcol' : i.val < c ↔ j.val < c := by rw [← hcol0, ← hcol0]; exact hcol
          have hrow' : (q i).val < r ↔ (q j).val < r := by rw [← hrow0, ← hrow0]; exact hrow
          have h := hq i j hij hcol' hrow'
          rw [insPerm_succAbove, insPerm_succAbove, Fin.succAbove_lt_succAbove_iff]
          have hi_r := hrow0 i
          rw [insPerm_succAbove] at hi_r
          omega
    · intro x y
      refine Fin.succAboveCases i₀ ?_ ?_ x
      · refine Fin.succAboveCases i₀ ?_ ?_ y
        · intro hxy _ _; exact absurd hxy (lt_irrefl _)
        · intro j hxy _ hrow
          have hp0 : (p i₀).val = r := by simp [p, insPerm_self, v₀]
          have hne : p (i₀.succAbove j) ≠ p i₀ := fun h => absurd (p.injective h) (ne_of_gt hxy)
          have hval_ne : (p (i₀.succAbove j)).val ≠ r := fun h => hne (Fin.ext (by omega))
          have hpy : (p (i₀.succAbove j)).val < r + 1 := hrow.mp (by omega)
          have hgt : p (i₀.succAbove j) < p i₀ := Fin.lt_def.mpr (by omega)
          exact ⟨fun hlt => absurd hlt (not_lt_of_gt hgt), fun hle => by omega⟩
      · intro i
        refine Fin.succAboveCases i₀ ?_ ?_ y
        · intro hxy hcol _
          exfalso
          have hlt : (i₀.succAbove i).val < c := hxy
          have hnot : ¬ (i₀.val < c) := by simp [i₀]
          exact hnot (hcol.mp hlt)
        · intro j hxy hcol hrow
          have hij : i < j := Fin.succAbove_lt_succAbove_iff.mp hxy
          have hcol' : i.val < c ↔ j.val < c := by rw [← hcol0, ← hcol0]; exact hcol
          have hrow' : (q i).val < r ↔ (q j).val < r := by rw [← hrow1, ← hrow1]; exact hrow
          have h := hq i j hij hcol' hrow'
          rw [insPerm_succAbove, insPerm_succAbove, Fin.succAbove_lt_succAbove_iff]
          have hi_r := hrow1 i
          rw [insPerm_succAbove] at hi_r
          omega

/-- Characterization of adjacent-row overlap: value `r` must sit at index `0` (if `1 ≤ c`) or `c` (if `c ≤ n`). -/
lemma adj_row_char {n c r : ℕ} (hc : c ≤ n + 1) (hr : r ≤ n) {p : Equiv.Perm (Fin (n + 1))}
    (h1 : IsGrid c r p) (h2 : IsGrid c (r + 1) p) :
    (1 ≤ c ∧ (p 0).val = r) ∨ (∃ (_ : c ≤ n), (p ⟨c, by omega⟩).val = r) := by
  let k : Fin (n + 1) := p.symm ⟨r, by omega⟩
  have hpk : (p k).val = r := by simp [k]
  by_cases hkc : k.val < c
  · left
    refine ⟨by omega, ?_⟩
    by_contra hne
    have hk_pos : 0 < k.val := by
      by_contra h0
      have hk0 : k = 0 := Fin.ext (by dsimp; omega)
      rw [← hk0] at hne
      exact hne hpk
    have h0k : (0 : Fin (n + 1)) < k := Fin.lt_def.mpr hk_pos
    have hcol : (0 : Fin (n + 1)).val < c ↔ k.val < c := by simp [hkc]; omega
    by_cases h0r : (p 0).val < r
    · have hrow2 : (p 0).val < r + 1 ↔ (p k).val < r + 1 := by omega
      have hlt : p 0 < p k := Fin.lt_def.mpr (by omega)
      have := (h2 0 k h0k hcol hrow2).mp hlt
      omega
    · have hrow1 : (p 0).val < r ↔ (p k).val < r := by omega
      have hlt : p 0 < p k := (h1 0 k h0k hcol hrow1).mpr (by omega)
      have : (p 0).val < (p k).val := hlt
      omega
  · right
    have hcn : c ≤ n := by omega
    refine ⟨hcn, ?_⟩
    by_contra hne
    have hkc_gt : c < k.val := by
      by_contra hle
      have hkeq : k = ⟨c, by omega⟩ := Fin.ext (by dsimp; omega)
      rw [← hkeq] at hne
      exact hne hpk
    let cfin : Fin (n + 1) := ⟨c, by omega⟩
    have hck : cfin < k := Fin.lt_def.mpr hkc_gt
    have hcol : cfin.val < c ↔ k.val < c := by simp [cfin]; omega
    by_cases hcr : (p cfin).val < r
    · have hrow2 : (p cfin).val < r + 1 ↔ (p k).val < r + 1 := by omega
      have hlt : p cfin < p k := Fin.lt_def.mpr (by omega)
      have := (h2 cfin k hck hcol hrow2).mp hlt
      omega
    · have hrow1 : (p cfin).val < r ↔ (p k).val < r := by omega
      have hlt : p cfin < p k := (h1 cfin k hck hcol hrow1).mpr (by omega)
      have : (p cfin).val < (p k).val := hlt
      omega

/-! ### Exact Cardinality Lemma 2: `|G (n+1) c r ∩ G (n+1) c (r+1)|` -/

lemma card_G_adj_row (n c r : ℕ) (hc : c ≤ n + 1) (hr : r ≤ n) :
    (G (n + 1) c r ∩ G (n + 1) c (r + 1)).card =
      (if 1 ≤ c then (G n (c - 1) r).card else 0) +
      (if c ≤ n then (G n c r).card else 0) := by
  let A := (G (n + 1) c r ∩ G (n + 1) c (r + 1)).filter (fun p => 1 ≤ c ∧ (p 0).val = r)
  let B := (G (n + 1) c r ∩ G (n + 1) c (r + 1)).filter
    (fun p => ∃ h : c ≤ n, (p ⟨c, by omega⟩).val = r)
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro p hpA hpB
    simp only [A, B, Finset.mem_filter] at hpA hpB
    rcases hpA.2 with ⟨hc1, hp0⟩
    rcases hpB.2 with ⟨hcn, hpc⟩
    have heq : p 0 = p ⟨c, by omega⟩ := Fin.ext (by omega)
    have := p.injective heq
    have hval : (0 : Fin (n + 1)).val = (⟨c, by omega⟩ : Fin (n + 1)).val := congrArg Fin.val this
    simp at hval
    omega
  have hunion : A ∪ B = G (n + 1) c r ∩ G (n + 1) c (r + 1) := by
    ext p
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_inter, mem_G]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro ⟨h1, h2⟩
      rcases adj_row_char hc hr h1 h2 with ⟨hc1, hp0⟩ | ⟨hcn, hpc⟩
      · left; exact ⟨⟨h1, h2⟩, hc1, hp0⟩
      · right; exact ⟨⟨h1, h2⟩, hcn, hpc⟩
  rw [← hunion, Finset.card_union_of_disjoint hdisj]
  congr 1
  · by_cases hc1 : 1 ≤ c
    · rw [if_pos hc1]
      symm
      refine Finset.card_bij (fun q _ => insPerm 0 ⟨r, by omega⟩ q) ?_ ?_ ?_
      · intro q hq
        simp only [A, Finset.mem_filter, Finset.mem_inter, mem_G] at hq ⊢
        refine ⟨(isGrid_insPerm_zero_iff hc1 hr q).mpr hq, hc1, ?_⟩
        simp [insPerm_self]
      · intro q₁ _ q₂ _ h; exact insPerm_injective _ _ h
      · intro p hp
        simp only [A, Finset.mem_filter, Finset.mem_inter, mem_G] at hp
        have hp0 : p 0 = ⟨r, by omega⟩ := Fin.ext hp.2.2
        rcases exists_insPerm_of_apply 0 ⟨r, by omega⟩ p hp0 with ⟨q, hq⟩
        refine ⟨q, mem_G.mpr ?_, hq⟩
        rw [← hq] at hp
        exact (isGrid_insPerm_zero_iff hc1 hr q).mp hp.1
    · rw [if_neg hc1]
      refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun p _ => ?_)
      simp [hc1]
  · by_cases hcn : c ≤ n
    · rw [if_pos hcn]
      symm
      refine Finset.card_bij (fun q _ => insPerm ⟨c, by omega⟩ ⟨r, by omega⟩ q) ?_ ?_ ?_
      · intro q hq
        simp only [B, Finset.mem_filter, Finset.mem_inter, mem_G] at hq ⊢
        refine ⟨(isGrid_insPerm_c_iff hcn hr q).mpr hq, hcn, ?_⟩
        simp [insPerm_self]
      · intro q₁ _ q₂ _ h; exact insPerm_injective _ _ h
      · intro p hp
        simp only [B, Finset.mem_filter, Finset.mem_inter, mem_G] at hp
        rcases hp.2 with ⟨_, hpc⟩
        have hpc' : p ⟨c, by omega⟩ = ⟨r, by omega⟩ := Fin.ext hpc
        rcases exists_insPerm_of_apply ⟨c, by omega⟩ ⟨r, by omega⟩ p hpc' with ⟨q, hq⟩
        refine ⟨q, mem_G.mpr ?_, hq⟩
        rw [← hq] at hp
        exact (isGrid_insPerm_c_iff hcn hr q).mp hp.1
    · rw [if_neg hcn]
      refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun p _ => ?_)
      simp [hcn]

/-! ### Exact Cardinality Lemma 3: `|G (n+1) c r ∩ G (n+1) (c+1) r|` -/

/-- Upper half of `G (n+1) c r ∩ G (n+1) (c+1) r`: those with `r ≤ (p c).val`. -/
noncomputable def GAdjColUpper (n c r : ℕ) (hc : c ≤ n) : Finset (Equiv.Perm (Fin (n + 1))) :=
  (G (n + 1) c r ∩ G (n + 1) (c + 1) r).filter (fun p => r ≤ (p ⟨c, by omega⟩).val)

/-- Lower half of `G (n+1) c r ∩ G (n+1) (c+1) r`: those with `(p c).val < r`. -/
noncomputable def GAdjColLower (n c r : ℕ) (hc : c ≤ n) : Finset (Equiv.Perm (Fin (n + 1))) :=
  (G (n + 1) c r ∩ G (n + 1) (c + 1) r).filter (fun p => (p ⟨c, by omega⟩).val < r)

lemma card_GAdjColUpper_eq (n c r : ℕ) (hc : c ≤ n) (hr : r ≤ n) :
    (GAdjColUpper n c r hc).card =
      ∑ a ∈ Finset.range (n + 1), c.choose a * (n - c).choose (r - a) * r.choose a := by
  -- Helper finsets: indices < c (card c), indices > c (card n - c), values < r (card r)
  let Ilt := IioFin (n + 1) c
  let Igt := IciFin (n + 1) (c + 1)
  let Vlt := IioFin (n + 1) r
  have hIlt_card : Ilt.card = c := card_IioFin (n + 1) c (by omega)
  have hIgt_card : Igt.card = n - c := by
    rw [card_IciFin (n + 1) (c + 1) (by omega)]; omega
  have hVlt_card : Vlt.card = r := card_IioFin (n + 1) r (by omega)
  let B (a : ℕ) :=
    (Ilt.powersetCard a ×ˢ Igt.powersetCard (r - a)) ×ˢ Vlt.powersetCard a
  let target := (Finset.range (n + 1)).sigma B
  have htarget_card : target.card =
      ∑ a ∈ Finset.range (n + 1), c.choose a * (n - c).choose (r - a) * r.choose a := by
    rw [Finset.card_sigma]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [B, Finset.card_product, Finset.card_powersetCard, hIlt_card, hIgt_card, hVlt_card]
  rw [← htarget_card]
  let toTuple (p : Equiv.Perm (Fin (n + 1))) :
      Σ _ : ℕ, (Finset (Fin (n + 1)) × Finset (Fin (n + 1))) × Finset (Fin (n + 1)) :=
    let IL := Finset.univ.filter (fun i : Fin (n + 1) => i.val < c ∧ (p i).val < r)
    let IR := Finset.univ.filter (fun i : Fin (n + 1) => c + 1 ≤ i.val ∧ (p i).val < r)
    let VL := Finset.univ.filter (fun v : Fin (n + 1) => v.val < r ∧ (p.symm v).val < c)
    ⟨IL.card, ((IL, IR), VL)⟩
  refine Finset.card_bij (fun p _ => toTuple p) ?_ ?_ ?_
  · intro p hp
    simp only [GAdjColUpper, Finset.mem_filter, Finset.mem_inter, mem_G] at hp
    rcases hp with ⟨_, hpc⟩
    simp only [target, B, toTuple, Finset.mem_sigma, Finset.mem_range, Finset.mem_product,
      Finset.mem_powersetCard]
    set IL := Finset.univ.filter (fun i : Fin (n + 1) => i.val < c ∧ (p i).val < r)
    set IR := Finset.univ.filter (fun i : Fin (n + 1) => c + 1 ≤ i.val ∧ (p i).val < r)
    set VL := Finset.univ.filter (fun v : Fin (n + 1) => v.val < r ∧ (p.symm v).val < c)
    have hIL_le : IL.card ≤ c := by
      calc IL.card ≤ Ilt.card := Finset.card_le_card (fun i hi => by
            simp only [IL, Ilt, IioFin, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hi.1)
        _ = c := hIlt_card
    have hIL_eq_VL : IL.card = VL.card := by
      refine Finset.card_bij (fun i _ => p i) ?_ ?_ ?_
      · intro i hi
        simp only [IL, VL, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact ⟨hi.2, by simpa using hi.1⟩
      · intro i₁ _ i₂ _ h; exact p.injective h
      · intro v hv
        simp only [IL, VL, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        exact ⟨p.symm v, ⟨hv.2, by simpa using hv.1⟩, p.apply_symm_apply v⟩
    have hIL_IR : IL.card + IR.card = r := by
      have hdisj : Disjoint IL IR := by
        rw [Finset.disjoint_left]; intro i h1 h2
        simp only [IL, IR, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2; omega
      rw [← Finset.card_union_of_disjoint hdisj]
      have hbij : (IL ∪ IR).card = Vlt.card := by
        refine Finset.card_bij (fun i _ => p i) ?_ ?_ ?_
        · intro i hi
          simp only [IL, IR, Vlt, IioFin, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
            true_and] at hi ⊢
          rcases hi with h | h <;> exact h.2
        · intro i₁ _ i₂ _ h; exact p.injective h
        · intro v hv
          simp only [Vlt, IioFin, Finset.mem_filter, Finset.mem_univ, true_and] at hv
          refine ⟨p.symm v, ?_, p.apply_symm_apply v⟩
          simp only [IL, IR, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          have hne_c : (p.symm v).val ≠ c := by
            intro heq
            have : p.symm v = ⟨c, by omega⟩ := Fin.ext heq
            have hv' : v = p ⟨c, by omega⟩ := by rw [← this, p.apply_symm_apply]
            rw [hv'] at hv; omega
          by_cases hlt : (p.symm v).val < c
          · left; exact ⟨hlt, by simpa using hv⟩
          · right; exact ⟨by omega, by simpa using hv⟩
      rw [hbij, hVlt_card]
    refine ⟨by omega, ⟨⟨?_, trivial⟩, ⟨?_, by omega⟩⟩, ⟨?_, hIL_eq_VL.symm⟩⟩
    · intro i hi; simp only [IL, Ilt, IioFin, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hi.1
    · intro i hi; simp only [IR, Igt, IciFin, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hi.1
    · intro v hv; simp only [VL, Vlt, IioFin, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢; exact hv.1
  · -- Injectivity: same (IL, IR, VL) and both in GAdjColUpper → p₁ = p₂
    intro p₁ hp₁ p₂ hp₂ heq
    simp only [GAdjColUpper, Finset.mem_filter, Finset.mem_inter, mem_G] at hp₁ hp₂
    rcases hp₁ with ⟨⟨h1a, h1b⟩, hpc₁⟩
    rcases hp₂ with ⟨⟨h2a, h2b⟩, hpc₂⟩
    have hprod := eq_of_heq (Sigma.mk.inj_iff.mp heq).2
    simp only [Prod.mk.injEq] at hprod
    rcases hprod with ⟨⟨hIL, hIR⟩, hVL⟩
    have h_cell_dec : ∀ (A B : Finset (Fin (n + 1))),
        (∀ x, x ∈ A ↔ p₁ x ∈ B) → (∀ x, x ∈ A ↔ p₂ x ∈ B) →
        (∀ i j, i ∈ A → j ∈ A → i < j → p₁ j < p₁ i) →
        (∀ i j, i ∈ A → j ∈ A → i < j → p₂ j < p₂ i) →
        ∀ x ∈ A, p₁ x = p₂ x := by
      intro A B hAB1 hAB2 hanti1 hanti2 x hx
      let f₁ : {i // i ∈ A} → {v // v ∈ B} := fun i => ⟨p₁ i.val, (hAB1 i.val).mp i.property⟩
      let f₂ : {i // i ∈ A} → {v // v ∈ B} := fun i => ⟨p₂ i.val, (hAB2 i.val).mp i.property⟩
      have hf₁ : Function.Bijective f₁ :=
        ⟨fun a b h => Subtype.ext (p₁.injective (congrArg Subtype.val h)), fun y =>
          ⟨⟨p₁.symm y.val, (hAB1 _).mpr (by simp [y.property])⟩,
            Subtype.ext (p₁.apply_symm_apply y.val)⟩⟩
      have hf₂ : Function.Bijective f₂ :=
        ⟨fun a b h => Subtype.ext (p₂.injective (congrArg Subtype.val h)), fun y =>
          ⟨⟨p₂.symm y.val, (hAB2 _).mpr (by simp [y.property])⟩,
            Subtype.ext (p₂.apply_symm_apply y.val)⟩⟩
      exact congrArg Subtype.val (strictAnti_bij_unique hf₁ hf₂
        (fun a b hab => hanti1 a.val b.val a.property b.property hab)
        (fun a b hab => hanti2 a.val b.val a.property b.property hab) ⟨x, hx⟩)
    have h_cell_inc : ∀ (A B : Finset (Fin (n + 1))),
        (∀ x, x ∈ A ↔ p₁ x ∈ B) → (∀ x, x ∈ A ↔ p₂ x ∈ B) →
        (∀ i j, i ∈ A → j ∈ A → i < j → p₁ i < p₁ j) →
        (∀ i j, i ∈ A → j ∈ A → i < j → p₂ i < p₂ j) →
        ∀ x ∈ A, p₁ x = p₂ x := by
      intro A B hAB1 hAB2 hmono1 hmono2 x hx
      let f₁ : {i // i ∈ A} → {v // v ∈ B} := fun i => ⟨p₁ i.val, (hAB1 i.val).mp i.property⟩
      let f₂ : {i // i ∈ A} → {v // v ∈ B} := fun i => ⟨p₂ i.val, (hAB2 i.val).mp i.property⟩
      have hf₁ : Function.Bijective f₁ :=
        ⟨fun a b h => Subtype.ext (p₁.injective (congrArg Subtype.val h)), fun y =>
          ⟨⟨p₁.symm y.val, (hAB1 _).mpr (by simp [y.property])⟩,
            Subtype.ext (p₁.apply_symm_apply y.val)⟩⟩
      have hf₂ : Function.Bijective f₂ :=
        ⟨fun a b h => Subtype.ext (p₂.injective (congrArg Subtype.val h)), fun y =>
          ⟨⟨p₂.symm y.val, (hAB2 _).mpr (by simp [y.property])⟩,
            Subtype.ext (p₂.apply_symm_apply y.val)⟩⟩
      exact congrArg Subtype.val (strictMono_bij_unique hf₁ hf₂
        (fun a b hab => hmono1 a.val b.val a.property b.property hab)
        (fun a b hab => hmono2 a.val b.val a.property b.property hab) ⟨x, hx⟩)
    -- In GAdjColUpper, the ENTIRE upper row is strictly increasing!
    have hupper_inc : ∀ p : Equiv.Perm (Fin (n + 1)),
        IsGrid c r p → IsGrid (c + 1) r p → r ≤ (p ⟨c, by omega⟩).val →
        ∀ i j : Fin (n + 1), r ≤ (p i).val → r ≤ (p j).val → i < j → p i < p j := by
      intro p ha hb hpc i j hpi hpj hij
      let cfin : Fin (n + 1) := ⟨c, by omega⟩
      have hcfin_val : cfin.val = c := rfl
      have hpc' : r ≤ (p cfin).val := hpc
      by_cases hic : i.val < c
      · by_cases hjc : j.val ≤ c
        · exact (hb i j hij (by omega) (by omega)).mpr hpi
        · have h1 : p i < p cfin :=
            (hb i cfin (Fin.lt_def.mpr (by omega)) (by omega) (by omega)).mpr hpi
          have h2 : p cfin < p j :=
            (ha cfin j (Fin.lt_def.mpr (by omega)) (by omega) (by omega)).mpr hpc'
          exact lt_trans h1 h2
      · have hjc : c ≤ j.val := by
          have : i.val < j.val := hij
          omega
        exact (ha i j hij (by omega) (by omega)).mpr hpi
    ext x
    by_cases hxr : (p₁ x).val < r
    · by_cases hxc : x.val < c
      · let A := Finset.univ.filter (fun i : Fin (n + 1) => i.val < c ∧ (p₁ i).val < r)
        let B := Finset.univ.filter (fun v : Fin (n + 1) => v.val < r ∧ (p₁.symm v).val < c)
        have h := h_cell_dec A B
          (fun i => by simp [A, B, and_comm])
          (fun i => by dsimp only [A, B]; rw [hIL, hVL]; simp [and_comm])
          (fun i j hi hj hij => by
            simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
            have hnot : ¬ (p₁ i < p₁ j) := fun hlt => by
              have := (h1a i j hij (by omega) (by omega)).mp hlt; omega
            have hne : p₁ i ≠ p₁ j := fun h => absurd (p₁.injective h) (ne_of_lt hij)
            exact lt_of_le_of_ne (le_of_not_gt hnot) hne.symm)
          (fun i j hi hj hij => by
            dsimp only [A] at hi hj
            rw [hIL] at hi hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
            have hnot : ¬ (p₂ i < p₂ j) := fun hlt => by
              have := (h2a i j hij (by omega) (by omega)).mp hlt; omega
            have hne : p₂ i ≠ p₂ j := fun h => absurd (p₂.injective h) (ne_of_lt hij)
            exact lt_of_le_of_ne (le_of_not_gt hnot) hne.symm)
          x (by simp [A, hxc, hxr])
        exact congrArg Fin.val h
      · have hxc_gt : c + 1 ≤ x.val := by
          by_contra hle
          have hx_eq : x = ⟨c, by omega⟩ := Fin.ext (by dsimp; omega)
          rw [hx_eq] at hxr; omega
        let A := Finset.univ.filter (fun i : Fin (n + 1) => c + 1 ≤ i.val ∧ (p₁ i).val < r)
        let B := Finset.univ.filter (fun v : Fin (n + 1) => v.val < r ∧ c + 1 ≤ (p₁.symm v).val)
        have hBeq : B = Finset.univ.filter (fun v : Fin (n + 1) => v.val < r ∧ c + 1 ≤ (p₂.symm v).val) := by
          ext v
          have hmem := Finset.ext_iff.mp hVL v
          simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
          constructor
          · intro ⟨hvr, hvc⟩
            refine ⟨hvr, ?_⟩
            have hne1 : ¬ ((p₂.symm v).val < c) := fun h => by
              have := hmem.mpr ⟨hvr, h⟩; omega
            have hne2 : (p₂.symm v).val ≠ c := fun h => by
              have : p₂.symm v = ⟨c, by omega⟩ := Fin.ext h
              have hv' : v = p₂ ⟨c, by omega⟩ := by rw [← this, p₂.apply_symm_apply]
              rw [hv'] at hvr; omega
            omega
          · intro ⟨hvr, hvc⟩
            refine ⟨hvr, ?_⟩
            have hne1 : ¬ ((p₁.symm v).val < c) := fun h => by
              have := hmem.mp ⟨hvr, h⟩; omega
            have hne2 : (p₁.symm v).val ≠ c := fun h => by
              have : p₁.symm v = ⟨c, by omega⟩ := Fin.ext h
              have hv' : v = p₁ ⟨c, by omega⟩ := by rw [← this, p₁.apply_symm_apply]
              rw [hv'] at hvr; omega
            omega
        have h := h_cell_dec A B
          (fun i => by simp [A, B, and_comm])
          (fun i => by dsimp only [A]; rw [hIR, hBeq]; simp [and_comm])
          (fun i j hi hj hij => by
            simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
            have hnot : ¬ (p₁ i < p₁ j) := fun hlt => by
              have := (h1a i j hij (by omega) (by omega)).mp hlt; omega
            have hne : p₁ i ≠ p₁ j := fun h => absurd (p₁.injective h) (ne_of_lt hij)
            exact lt_of_le_of_ne (le_of_not_gt hnot) hne.symm)
          (fun i j hi hj hij => by
            dsimp only [A] at hi hj
            rw [hIR] at hi hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
            have hnot : ¬ (p₂ i < p₂ j) := fun hlt => by
              have := (h2a i j hij (by omega) (by omega)).mp hlt; omega
            have hne : p₂ i ≠ p₂ j := fun h => absurd (p₂.injective h) (ne_of_lt hij)
            exact lt_of_le_of_ne (le_of_not_gt hnot) hne.symm)
          x (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxc_gt, hxr⟩)
        exact congrArg Fin.val h
    · -- Upper row (all indices i with r ≤ p i)
      let A := Finset.univ.filter (fun i : Fin (n + 1) => r ≤ (p₁ i).val)
      let B := IciFin (n + 1) r
      have hAeq : A = Finset.univ.filter (fun i : Fin (n + 1) => r ≤ (p₂ i).val) := by
        ext i
        have h1 := Finset.ext_iff.mp hIL i
        have h2 := Finset.ext_iff.mp hIR i
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2 ⊢
        by_cases hic : i.val < c
        · omega
        · by_cases hieq : i.val = c
          · have hi_c : i = ⟨c, by omega⟩ := Fin.ext hieq
            rw [hi_c]; exact ⟨fun _ => hpc₂, fun _ => hpc₁⟩
          · omega
      have h := h_cell_inc A B
        (fun i => by simp [A, B, IciFin])
        (fun i => by rw [hAeq]; simp [B, IciFin])
        (fun i j hi hj hij => by
          simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
          exact hupper_inc p₁ h1a h1b hpc₁ i j hi hj hij)
        (fun i j hi hj hij => by
          rw [hAeq] at hi hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
          exact hupper_inc p₂ h2a h2b hpc₂ i j hi hj hij)
        x (by simp [A]; omega)
      exact congrArg Fin.val h
  · -- Surjectivity: glue 3 blocks (IL → VL dec, IR → Vlt \ VL dec, U → IciFin r inc) + empty 4th block
    rintro ⟨a, ⟨⟨IL, IR⟩, VL⟩⟩ hmem
    simp only [target, B, Finset.mem_sigma, Finset.mem_range, Finset.mem_product,
      Finset.mem_powersetCard] at hmem
    rcases hmem with ⟨_, ⟨⟨hIL_sub, hIL_card⟩, ⟨hIR_sub, hIR_card⟩⟩, ⟨hVL_sub, hVL_card⟩⟩
    have har : a ≤ r := by
      calc a = VL.card := hVL_card.symm
        _ ≤ Vlt.card := Finset.card_le_card hVL_sub
        _ = r := hVlt_card
    let A₁ := IL
    let A₂ := IR
    let A₃ := Finset.univ \ (IL ∪ IR)
    let A₄ : Finset (Fin (n + 1)) := ∅
    let B₁ := VL
    let B₂ := Vlt \ VL
    let B₃ := IciFin (n + 1) r
    let B₄ : Finset (Fin (n + 1)) := ∅
    have hIL_IR_disj : Disjoint IL IR := Finset.disjoint_left.mpr fun x h1 h2 => by
      have hx1 := hIL_sub h1; have hx2 := hIR_sub h2
      simp only [Ilt, Igt, IioFin, IciFin, Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
      omega
    have hc1 : A₁.card = B₁.card := by dsimp only [A₁, B₁]; omega
    have hc2 : A₂.card = B₂.card := by
      dsimp only [A₂, B₂]; rw [Finset.card_sdiff_of_subset hVL_sub, hVlt_card]; omega
    have hc3 : A₃.card = B₃.card := by
      dsimp only [A₃, B₃]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
          Finset.card_union_of_disjoint hIL_IR_disj, card_IciFin (n + 1) r (by omega)]
      omega
    have hc4 : A₄.card = B₄.card := rfl
    have hA12 : Disjoint A₁ A₂ := hIL_IR_disj
    have hA13 : Disjoint A₁ A₃ := Finset.disjoint_left.mpr fun x h1 h3 =>
      (Finset.mem_sdiff.mp h3).2 (Finset.mem_union_left _ h1)
    have hA23 : Disjoint A₂ A₃ := Finset.disjoint_left.mpr fun x h2 h3 =>
      (Finset.mem_sdiff.mp h3).2 (Finset.mem_union_right _ h2)
    have hAcov : ∀ x : Fin (n + 1), x ∈ A₁ ∨ x ∈ A₂ ∨ x ∈ A₃ ∨ x ∈ A₄ := by
      intro x
      by_cases h1 : x ∈ IL
      · exact Or.inl h1
      · by_cases h2 : x ∈ IR
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr (Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, by simp [h1, h2]⟩)))
    have hB12 : Disjoint B₁ B₂ := Finset.disjoint_sdiff
    have hB13 : Disjoint B₁ B₃ := Finset.disjoint_left.mpr fun y h1 h3 => by
      have hy1 := hVL_sub h1
      simp only [Vlt, B₃, IioFin, IciFin, Finset.mem_filter, Finset.mem_univ, true_and] at hy1 h3
      omega
    have hB23 : Disjoint B₂ B₃ := Finset.disjoint_left.mpr fun y h2 h3 => by
      have hy2 := (Finset.mem_sdiff.mp h2).1
      simp only [Vlt, B₃, IioFin, IciFin, Finset.mem_filter, Finset.mem_univ, true_and] at hy2 h3
      omega
    have hBcov : ∀ y : Fin (n + 1), y ∈ B₁ ∨ y ∈ B₂ ∨ y ∈ B₃ ∨ y ∈ B₄ := by
      intro y
      by_cases hyr : y.val < r
      · by_cases h1 : y ∈ VL
        · exact Or.inl h1
        · exact Or.inr (Or.inl (Finset.mem_sdiff.mpr ⟨by simp [Vlt, IioFin, hyr], h1⟩))
      · exact Or.inr (Or.inr (Or.inl (by simp [B₃, IciFin]; omega)))
    let e₁ := decBij A₁ B₁ hc1
    let e₂ := decBij A₂ B₂ hc2
    let e₃ := incBij A₃ B₃ hc3
    let e₄ := incBij A₄ B₄ hc4
    let p := glue4 A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄
      hA12 hA13 (Finset.disjoint_empty_right _) hA23 (Finset.disjoint_empty_right _)
      (Finset.disjoint_empty_right _) hAcov
      hB12 hB13 (Finset.disjoint_empty_right _) hB23 (Finset.disjoint_empty_right _)
      (Finset.disjoint_empty_right _) hBcov e₁ e₂ e₃ e₄
    have hp1 : ∀ x (hx : x ∈ A₁), p x = (e₁ ⟨x, hx⟩).val := fun x hx => by
      change (if h1 : x ∈ A₁ then (e₁ ⟨x, h1⟩).val else _) = _; rw [dif_pos hx]
    have hp2 : ∀ x (hx : x ∈ A₂), p x = (e₂ ⟨x, hx⟩).val := fun x hx => by
      have h1 : x ∉ A₁ := Finset.disjoint_right.mp hA12 hx
      change (if h1 : x ∈ A₁ then _ else if h2 : x ∈ A₂ then (e₂ ⟨x, h2⟩).val else _) = _
      rw [dif_neg h1, dif_pos hx]
    have hp3 : ∀ x (hx : x ∈ A₃), p x = (e₃ ⟨x, hx⟩).val := fun x hx => by
      have h1 : x ∉ A₁ := Finset.disjoint_right.mp hA13 hx
      have h2 : x ∉ A₂ := Finset.disjoint_right.mp hA23 hx
      change (if h1 : x ∈ A₁ then _ else if h2 : x ∈ A₂ then _ else
        if h3 : x ∈ A₃ then (e₃ ⟨x, h3⟩).val else _) = _
      rw [dif_neg h1, dif_neg h2, dif_pos hx]
    have hpmem1 : ∀ x ∈ A₁, (p x).val < r := fun x hx => by
      rw [hp1 x hx]; have := hVL_sub (e₁ ⟨x, hx⟩).property
      simp only [Vlt, IioFin, Finset.mem_filter, Finset.mem_univ, true_and] at this; exact this
    have hpmem2 : ∀ x ∈ A₂, (p x).val < r := fun x hx => by
      rw [hp2 x hx]; have := (Finset.mem_sdiff.mp (e₂ ⟨x, hx⟩).property).1
      simp only [Vlt, IioFin, Finset.mem_filter, Finset.mem_univ, true_and] at this; exact this
    have hpmem3 : ∀ x ∈ A₃, r ≤ (p x).val := fun x hx => by
      rw [hp3 x hx]; have := (e₃ ⟨x, hx⟩).property
      simp only [B₃, IciFin, Finset.mem_filter, Finset.mem_univ, true_and] at this; exact this
    have hc_in_A3 : (⟨c, by omega⟩ : Fin (n + 1)) ∈ A₃ := by
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      simp only [Finset.mem_union]
      rintro (h | h)
      · have := hIL_sub h; simp [Ilt, IioFin] at this
      · have := hIR_sub h; simp [Igt, IciFin] at this
    have hp_grid_c : IsGrid c r p := by
      intro i j hij hcol hrow
      by_cases hi3 : i ∈ A₃
      · have hpi := hpmem3 i hi3
        have hpj : r ≤ (p j).val := by omega
        have hj3 : j ∈ A₃ := by
          refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
          simp only [Finset.mem_union]
          rintro (h | h)
          · have := hpmem1 j h; omega
          · have := hpmem2 j h; omega
        have hlt : p i < p j := by rw [hp3 i hi3, hp3 j hj3]; exact incBij_strictMono A₃ B₃ hc3 hij
        exact ⟨fun _ => hpi, fun _ => hlt⟩
      · rcases hAcov i with hi1 | hi2 | hi3' | hi4
        · have hpi := hpmem1 i hi1
          have hpj := hrow.mp hpi
          have hic : i.val < c := by have := hIL_sub hi1; simp [Ilt, IioFin] at this; exact this
          have hjc : j.val < c := hcol.mp hic
          have hj1 : j ∈ A₁ := by
            rcases hAcov j with h | h | h | h
            · exact h
            · have := hIR_sub h; simp [Igt, IciFin] at this; omega
            · have := hpmem3 j h; omega
            · simp [A₄] at h
          have hgt : p j < p i := by rw [hp1 i hi1, hp1 j hj1]; exact decBij_strictAnti A₁ B₁ hc1 hij
          exact ⟨fun hlt => absurd hlt (not_lt_of_gt hgt), fun hle => by omega⟩
        · have hpi := hpmem2 i hi2
          have hpj := hrow.mp hpi
          have hic : c + 1 ≤ i.val := by have := hIR_sub hi2; simp [Igt, IciFin] at this; exact this
          have hjc : ¬ (j.val < c) := fun h => by have := hcol.mpr h; omega
          have hj2 : j ∈ A₂ := by
            rcases hAcov j with h | h | h | h
            · have := hIL_sub h; simp [Ilt, IioFin] at this; omega
            · exact h
            · have := hpmem3 j h; omega
            · simp [A₄] at h
          have hgt : p j < p i := by rw [hp2 i hi2, hp2 j hj2]; exact decBij_strictAnti A₂ B₂ hc2 hij
          exact ⟨fun hlt => absurd hlt (not_lt_of_gt hgt), fun hle => by omega⟩
        · exact absurd hi3' hi3
        · simp [A₄] at hi4
    have hp_grid_c1 : IsGrid (c + 1) r p := by
      intro i j hij hcol hrow
      by_cases hi3 : i ∈ A₃
      · have hpi := hpmem3 i hi3
        have hpj : r ≤ (p j).val := by omega
        have hj3 : j ∈ A₃ := by
          refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
          simp only [Finset.mem_union]
          rintro (h | h)
          · have := hpmem1 j h; omega
          · have := hpmem2 j h; omega
        have hlt : p i < p j := by rw [hp3 i hi3, hp3 j hj3]; exact incBij_strictMono A₃ B₃ hc3 hij
        exact ⟨fun _ => hpi, fun _ => hlt⟩
      · rcases hAcov i with hi1 | hi2 | hi3' | hi4
        · have hpi := hpmem1 i hi1
          have hpj := hrow.mp hpi
          have hic : i.val < c := by have := hIL_sub hi1; simp [Ilt, IioFin] at this; exact this
          have hjc : j.val < c + 1 := hcol.mp (by omega)
          have hj1 : j ∈ A₁ := by
            rcases hAcov j with h | h | h | h
            · exact h
            · have := hIR_sub h; simp [Igt, IciFin] at this; omega
            · have := hpmem3 j h; omega
            · simp [A₄] at h
          have hgt : p j < p i := by rw [hp1 i hi1, hp1 j hj1]; exact decBij_strictAnti A₁ B₁ hc1 hij
          exact ⟨fun hlt => absurd hlt (not_lt_of_gt hgt), fun hle => by omega⟩
        · have hpi := hpmem2 i hi2
          have hpj := hrow.mp hpi
          have hic : c + 1 ≤ i.val := by have := hIR_sub hi2; simp [Igt, IciFin] at this; exact this
          have hjc : ¬ (j.val < c + 1) := fun h => by have := hcol.mpr h; omega
          have hj2 : j ∈ A₂ := by
            rcases hAcov j with h | h | h | h
            · have := hIL_sub h; simp [Ilt, IioFin] at this; omega
            · exact h
            · have := hpmem3 j h; omega
            · simp [A₄] at h
          have hgt : p j < p i := by rw [hp2 i hi2, hp2 j hj2]; exact decBij_strictAnti A₂ B₂ hc2 hij
          exact ⟨fun hlt => absurd hlt (not_lt_of_gt hgt), fun hle => by omega⟩
        · exact absurd hi3' hi3
        · simp [A₄] at hi4
    refine ⟨p, ?_, ?_⟩
    · simp only [GAdjColUpper, Finset.mem_filter, Finset.mem_inter, mem_G]
      exact ⟨⟨hp_grid_c, hp_grid_c1⟩, hpmem3 _ hc_in_A3⟩
    · have hIL' : Finset.univ.filter (fun i : Fin (n + 1) => i.val < c ∧ (p i).val < r) = IL := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro ⟨hic, hir⟩
          rcases hAcov i with h | h | h | h
          · exact h
          · have := hIR_sub h; simp [Igt, IciFin] at this; omega
          · have := hpmem3 i h; omega
          · simp [A₄] at h
        · intro hi
          have hx := hIL_sub hi; simp [Ilt, IioFin] at hx
          exact ⟨hx, hpmem1 i hi⟩
      have hIR' : Finset.univ.filter (fun i : Fin (n + 1) => c + 1 ≤ i.val ∧ (p i).val < r) = IR := by
        ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro ⟨hic, hir⟩
          rcases hAcov i with h | h | h | h
          · have := hIL_sub h; simp [Ilt, IioFin] at this; omega
          · exact h
          · have := hpmem3 i h; omega
          · simp [A₄] at h
        · intro hi
          have hx := hIR_sub hi; simp [Igt, IciFin] at hx
          exact ⟨hx, hpmem2 i hi⟩
      have hVL' : Finset.univ.filter (fun v : Fin (n + 1) => v.val < r ∧ (p.symm v).val < c) = VL := by
        ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro ⟨hvr, hvc⟩
          have h1 : p.symm v ∈ A₁ := by
            dsimp only [A₁]
            rw [← hIL']; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hvc, by simpa using hvr⟩
          have := hp1 (p.symm v) h1
          rw [p.apply_symm_apply] at this
          rw [this]; exact (e₁ ⟨p.symm v, h1⟩).property
        · intro hv
          have hy := hVL_sub hv; simp [Vlt, IioFin] at hy
          refine ⟨hy, ?_⟩
          have hsymm : p.symm v = (e₁.symm ⟨v, hv⟩).val := by
            change (if h1 : v ∈ B₁ then (e₁.symm ⟨v, h1⟩).val else _) = _; rw [dif_pos hv]
          rw [hsymm]
          have := hIL_sub (e₁.symm ⟨v, hv⟩).property; simp [Ilt, IioFin] at this; exact this
      simp only [toTuple, hIL', hIR', hVL', hIL_card]

lemma card_GAdjColLower_eq (n c r : ℕ) (hc : c ≤ n) (hr : r ≤ n + 1) :
    (GAdjColLower n c r hc).card = (GAdjColUpper n c (n + 1 - r) hc).card := by
  refine Finset.card_bij (fun p _ => revVal p) ?_ ?_ ?_
  · intro p hp
    simp only [GAdjColLower, GAdjColUpper, Finset.mem_filter, Finset.mem_inter, mem_G] at hp ⊢
    refine ⟨⟨(isGrid_revVal_iff c r hr p).mpr hp.1.1,
             (isGrid_revVal_iff (c + 1) r hr p).mpr hp.1.2⟩, ?_⟩
    rw [revVal_apply, Fin.val_rev]
    omega
  · intro p₁ _ p₂ _ h
    have := congrArg revVal h
    simpa [revVal_revVal] using this
  · intro q hq
    refine ⟨revVal q, ?_, revVal_revVal q⟩
    simp only [GAdjColLower, GAdjColUpper, Finset.mem_filter, Finset.mem_inter, mem_G] at hq ⊢
    have h1 : IsGrid c (n + 1 - r) (revVal (revVal q)) := by rw [revVal_revVal]; exact hq.1.1
    have h2 : IsGrid (c + 1) (n + 1 - r) (revVal (revVal q)) := by rw [revVal_revVal]; exact hq.1.2
    refine ⟨⟨(isGrid_revVal_iff c r hr (revVal q)).mp h1,
             (isGrid_revVal_iff (c + 1) r hr (revVal q)).mp h2⟩, ?_⟩
    have hq_val := hq.2
    rw [revVal_apply, Fin.val_rev]
    omega

/-- Total adjacent-column overlap sum: `∑ c < m, ∑ r ≤ m, |G m c r ∩ G m (c+1) r| = 3 ^ m - 1`. -/
lemma sum_G_adj_col (m : ℕ) :
    ∑ c ∈ Finset.range m, ∑ r ∈ Finset.range (m + 1),
      (G m c r ∩ G m (c + 1) r).card = 3 ^ m - 1 := by
  cases m with
  | zero => simp
  | succ n =>
    have hsplit : ∀ c (hc : c ∈ Finset.range (n + 1)),
        ∑ r ∈ Finset.range (n + 2), (G (n + 1) c r ∩ G (n + 1) (c + 1) r).card =
        2 * ∑ r ∈ Finset.range (n + 1),
          (GAdjColUpper n c r (Nat.lt_succ_iff.mp (Finset.mem_range.mp hc))).card := by
      intro c hc
      have hcn : c ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
      have hterm : ∀ r ∈ Finset.range (n + 2),
          (G (n + 1) c r ∩ G (n + 1) (c + 1) r).card =
          (GAdjColUpper n c r hcn).card + (GAdjColLower n c r hcn).card := by
        intro r _
        have hdisj : Disjoint (GAdjColUpper n c r hcn) (GAdjColLower n c r hcn) := by
          rw [Finset.disjoint_left]; intro p h1 h2
          simp only [GAdjColUpper, GAdjColLower, Finset.mem_filter] at h1 h2; omega
        have hunion : GAdjColUpper n c r hcn ∪ GAdjColLower n c r hcn =
            G (n + 1) c r ∩ G (n + 1) (c + 1) r := by
          ext p
          simp only [GAdjColUpper, GAdjColLower, Finset.mem_union, Finset.mem_filter]
          constructor
          · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
          · intro h
            by_cases hle : r ≤ (p ⟨c, by omega⟩).val
            · left; exact ⟨h, hle⟩
            · right; exact ⟨h, by omega⟩
        rw [← hunion, Finset.card_union_of_disjoint hdisj]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
      have hU_last : (GAdjColUpper n c (n + 1) hcn).card = 0 := by
        refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun p _ => ?_)
        have := (p ⟨c, by omega⟩).isLt
        omega
      have hU_sum : ∑ r ∈ Finset.range (n + 2), (GAdjColUpper n c r hcn).card =
          ∑ r ∈ Finset.range (n + 1), (GAdjColUpper n c r hcn).card := by
        rw [Finset.sum_range_succ, hU_last, add_zero]
      have hL_sum : ∑ r ∈ Finset.range (n + 2), (GAdjColLower n c r hcn).card =
          ∑ r ∈ Finset.range (n + 1), (GAdjColUpper n c r hcn).card := by
        have h1 : ∀ r ∈ Finset.range (n + 2),
            (GAdjColLower n c r hcn).card = (GAdjColUpper n c (n + 2 - 1 - r) hcn).card := fun r hr => by
          have : n + 2 - 1 - r = n + 1 - r := by omega
          rw [this]
          exact card_GAdjColLower_eq n c r hcn (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))
        rw [Finset.sum_congr rfl h1,
            Finset.sum_range_reflect (fun r => (GAdjColUpper n c r hcn).card) (n + 2),
            Finset.sum_range_succ, hU_last, add_zero]
      rw [hU_sum, hL_sum, two_mul]
    calc ∑ c ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 2),
            (G (n + 1) c r ∩ G (n + 1) (c + 1) r).card
        = ∑ c ∈ Finset.range (n + 1),
            2 * ∑ r ∈ Finset.range (n + 1),
              ∑ a ∈ Finset.range (n + 1), c.choose a * (n - c).choose (r - a) * r.choose a := by
          refine Finset.sum_congr rfl fun c hc => ?_
          rw [hsplit c hc]
          congr 1
          refine Finset.sum_congr rfl fun r hr => ?_
          exact card_GAdjColUpper_eq n c r
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hc))
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))
      _ = 2 * ∑ c ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1), ∑ a ∈ Finset.range (n + 1),
            c.choose a * (n - c).choose (r - a) * r.choose a := by rw [← Finset.mul_sum]
      _ = 3 ^ (n + 1) - 1 := sum_upper_adj_col n

/-! ### Exact Cardinality Lemma 4: 4-way intersection `|G c r ∩ G (c+1) r ∩ G c (r+1) ∩ G (c+1) (r+1)|` -/

lemma card_G_4way (n c r : ℕ) (hc : c ≤ n) (hr : r ≤ n) :
    (G (n + 1) c r ∩ G (n + 1) (c + 1) r ∩ G (n + 1) c (r + 1) ∩ G (n + 1) (c + 1) (r + 1)).card =
      if c = 0 then n.choose r else (G n (c - 1) r ∩ G n c r).card := by
  let Q := G (n + 1) c r ∩ G (n + 1) (c + 1) r ∩ G (n + 1) c (r + 1) ∩ G (n + 1) (c + 1) (r + 1)
  have hp0_forced : ∀ p ∈ Q, (p 0).val = r := by
    intro p hp
    simp only [Q, Finset.mem_inter, mem_G] at hp
    rcases hp with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    rcases adj_row_char (by omega : c ≤ n + 1) hr h1 h3 with ⟨_, h0⟩ | ⟨_, hpc⟩
    · exact h0
    · by_cases hc0 : c = 0
      · subst hc0; exact hpc
      · rcases adj_row_char (by omega : c + 1 ≤ n + 1) hr h2 h4 with ⟨_, h0⟩ | ⟨hc1n, hpc1⟩
        · exact h0
        · exfalso
          have heq : p ⟨c, by omega⟩ = p ⟨c + 1, by omega⟩ := Fin.ext (by omega)
          have := congrArg Fin.val (p.injective heq)
          simp at this
  by_cases hc0 : c = 0
  · subst hc0
    rw [if_pos rfl]
    have hcard0 : (G n 0 r).card = n.choose r := by
      rw [card_G n 0 r (Nat.zero_le _) hr, Finset.sum_eq_single 0]
      · simp
      · intro a _ ha0
        have hpos : 0 < a := Nat.pos_of_ne_zero ha0
        simp [Nat.choose_eq_zero_of_lt hpos]
      · simp
    rw [← hcard0]
    symm
    refine Finset.card_bij (fun q _ => insPerm 0 ⟨r, by omega⟩ q) ?_ ?_ ?_
    · intro q hq
      simp only [Finset.mem_inter, mem_G] at hq ⊢
      have h01 := (isGrid_insPerm_c_iff (n := n) (c := 0) (r := r) (Nat.zero_le _) hr q).mpr hq
      have h10 := (isGrid_insPerm_zero_iff (n := n) (c := 1) (r := r) (le_refl 1) hr q).mpr
        (by simpa using hq)
      exact ⟨⟨⟨h01.1, h10.1⟩, h01.2⟩, h10.2⟩
    · intro q₁ _ q₂ _ h; exact insPerm_injective _ _ h
    · intro p hp
      have hp0 : p 0 = ⟨r, by omega⟩ := Fin.ext (hp0_forced p hp)
      rcases exists_insPerm_of_apply 0 ⟨r, by omega⟩ p hp0 with ⟨q, hq⟩
      refine ⟨q, mem_G.mpr ?_, hq⟩
      simp only [Finset.mem_inter, mem_G] at hp
      rw [← hq] at hp
      exact (isGrid_insPerm_c_iff (n := n) (c := 0) (r := r) (Nat.zero_le _) hr q).mp
        ⟨hp.1.1.1, hp.1.2⟩
  · rw [if_neg hc0]
    have hc1 : 1 ≤ c := by omega
    symm
    refine Finset.card_bij (fun q _ => insPerm 0 ⟨r, by omega⟩ q) ?_ ?_ ?_
    · intro q hq
      simp only [Finset.mem_inter, mem_G] at hq ⊢
      have hA := (isGrid_insPerm_zero_iff hc1 hr q).mpr hq.1
      have hB := (isGrid_insPerm_zero_iff (c := c + 1) (by omega) hr q).mpr (by simpa using hq.2)
      exact ⟨⟨⟨hA.1, hB.1⟩, hA.2⟩, hB.2⟩
    · intro q₁ _ q₂ _ h; exact insPerm_injective _ _ h
    · intro p hp
      have hp0 : p 0 = ⟨r, by omega⟩ := Fin.ext (hp0_forced p hp)
      rcases exists_insPerm_of_apply 0 ⟨r, by omega⟩ p hp0 with ⟨q, hq⟩
      refine ⟨q, ?_, hq⟩
      simp only [Finset.mem_inter, mem_G] at hp ⊢
      rw [← hq] at hp
      refine ⟨(isGrid_insPerm_zero_iff hc1 hr q).mp ⟨hp.1.1.1, hp.1.2⟩, ?_⟩
      have hB := (isGrid_insPerm_zero_iff (c := c + 1) (by omega) hr q).mp ⟨hp.1.1.2, hp.2⟩
      simpa using hB

/-! ## Section 6: Assembly of the exact closed form and final theorem -/

lemma sum_S_eq_central_binom (n : ℕ) :
    ∑ c ∈ Finset.range (n + 2), (S (n + 1) c).card = (2 * (n + 1)).choose (n + 1) := by
  have hS_ie : ∀ c ∈ Finset.range (n + 2),
      (S (n + 1) c).card + ∑ r ∈ Finset.range (n + 1), (G (n + 1) c r ∩ G (n + 1) c (r + 1)).card =
        ∑ r ∈ Finset.range (n + 2), (G (n + 1) c r).card := by
    intro c _
    have := card_biUnion_interval (n + 2) (G (n + 1) c) (fun p a b d hab hbd _ ha hd => by
      simp only [mem_G] at ha hd ⊢
      exact isGrid_row_interval hab hbd ha hd)
    simpa [S] using this
  have hsum := Finset.sum_congr rfl hS_ie
  rw [Finset.sum_add_distrib] at hsum
  have hG_sum : ∑ c ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 2), (G (n + 1) c r).card =
      T (n + 1) := by
    unfold T
    refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun r hr =>
      card_G (n + 1) c r (Nat.lt_succ_iff.mp (Finset.mem_range.mp hc))
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))
  have hG_prev : ∑ c ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1), (G n c r).card = T n := by
    unfold T
    refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun r hr =>
      card_G n c r (Nat.lt_succ_iff.mp (Finset.mem_range.mp hc))
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))
  have hadj_sum :
      ∑ c ∈ Finset.range (n + 2), ∑ r ∈ Finset.range (n + 1),
        (G (n + 1) c r ∩ G (n + 1) c (r + 1)).card = 2 * T n := by
    have h1 : ∀ c ∈ Finset.range (n + 2),
        ∑ r ∈ Finset.range (n + 1), (G (n + 1) c r ∩ G (n + 1) c (r + 1)).card =
        (if 1 ≤ c then ∑ r ∈ Finset.range (n + 1), (G n (c - 1) r).card else 0) +
        (if c ≤ n then ∑ r ∈ Finset.range (n + 1), (G n c r).card else 0) := by
      intro c hc
      have hcn : c ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hc)
      have h2 : ∀ r ∈ Finset.range (n + 1),
          (G (n + 1) c r ∩ G (n + 1) c (r + 1)).card =
          (if 1 ≤ c then (G n (c - 1) r).card else 0) +
          (if c ≤ n then (G n c r).card else 0) :=
        fun r hr => card_G_adj_row n c r hcn (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))
      rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
    have hleft :
        ∑ c ∈ Finset.range (n + 2),
          (if 1 ≤ c then ∑ r ∈ Finset.range (n + 1), (G n (c - 1) r).card else 0) = T n := by
      rw [Finset.sum_range_succ']
      simp only [↓reduceIte, Nat.succ_le_succ_iff, Nat.zero_le, Nat.add_sub_cancel]
      simpa using hG_prev
    have hright :
        ∑ c ∈ Finset.range (n + 2),
          (if c ≤ n then ∑ r ∈ Finset.range (n + 1), (G n c r).card else 0) = T n := by
      rw [Finset.sum_range_succ]
      have hnot : ¬ (n + 1 ≤ n) := by omega
      rw [if_neg hnot, add_zero]
      have hle : ∀ c ∈ Finset.range (n + 1),
          (if c ≤ n then ∑ r ∈ Finset.range (n + 1), (G n c r).card else 0) =
          ∑ r ∈ Finset.range (n + 1), (G n c r).card := fun c hc =>
        if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hc))
      rw [Finset.sum_congr rfl hle]
      exact hG_prev
    rw [hleft, hright, two_mul]
  rw [hG_sum, hadj_sum, T_succ_eq n] at hsum
  omega

lemma sum_S_adj_eq (n : ℕ) :
    ∑ c ∈ Finset.range (n + 1), (S (n + 1) c ∩ S (n + 1) (c + 1)).card =
      2 * 3 ^ n - 2 ^ n := by
  have hS_inter : ∀ c ∈ Finset.range (n + 1),
      S (n + 1) c ∩ S (n + 1) (c + 1) =
        (Finset.range (n + 2)).biUnion (fun r => G (n + 1) c r ∩ G (n + 1) (c + 1) r) := by
    intro c hc
    have hcn : c < n + 1 := Finset.mem_range.mp hc
    ext p
    simp only [Finset.mem_inter, Finset.mem_biUnion, mem_S, mem_G, Finset.mem_range]
    constructor
    · rintro ⟨⟨r₁, hr₁, h1⟩, ⟨r₂, hr₂, h2⟩⟩
      rcases common_row_adj_col hcn (by omega) (by omega) h1 h2 with ⟨r, hr, ha, hb⟩
      exact ⟨r, by omega, ha, hb⟩
    · rintro ⟨r, hr, ha, hb⟩
      exact ⟨⟨r, hr, ha⟩, ⟨r, hr, hb⟩⟩
  have h_ie : ∀ c ∈ Finset.range (n + 1),
      (S (n + 1) c ∩ S (n + 1) (c + 1)).card +
        ∑ r ∈ Finset.range (n + 1),
          (G (n + 1) c r ∩ G (n + 1) (c + 1) r ∩ G (n + 1) c (r + 1) ∩ G (n + 1) (c + 1) (r + 1)).card =
      ∑ r ∈ Finset.range (n + 2), (G (n + 1) c r ∩ G (n + 1) (c + 1) r).card := by
    intro c hc
    rw [hS_inter c hc]
    have := card_biUnion_interval (n + 2) (fun r => G (n + 1) c r ∩ G (n + 1) (c + 1) r)
      (fun p a b d hab hbd _ ha hd => by
        simp only [Finset.mem_inter, mem_G] at ha hd ⊢
        exact ⟨isGrid_row_interval hab hbd ha.1 hd.1, isGrid_row_interval hab hbd ha.2 hd.2⟩)
    have h_assoc : ∀ r ∈ Finset.range (n + 1),
        ((G (n + 1) c r ∩ G (n + 1) (c + 1) r) ∩ (G (n + 1) c (r + 1) ∩ G (n + 1) (c + 1) (r + 1))).card =
        (G (n + 1) c r ∩ G (n + 1) (c + 1) r ∩ G (n + 1) c (r + 1) ∩ G (n + 1) (c + 1) (r + 1)).card := by
      intro r _
      congr 1
      ext p; simp only [Finset.mem_inter]; tauto
    simpa [Finset.sum_congr rfl h_assoc] using this
  have hsum := Finset.sum_congr rfl h_ie
  rw [Finset.sum_add_distrib, sum_G_adj_col (n + 1)] at hsum
  have h4way :
      ∑ c ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1),
        (G (n + 1) c r ∩ G (n + 1) (c + 1) r ∩ G (n + 1) c (r + 1) ∩ G (n + 1) (c + 1) (r + 1)).card =
      2 ^ n + (3 ^ n - 1) := by
    rw [Finset.sum_range_succ']
    have h0 : ∑ r ∈ Finset.range (n + 1),
        (G (n + 1) 0 r ∩ G (n + 1) 1 r ∩ G (n + 1) 0 (r + 1) ∩ G (n + 1) 1 (r + 1)).card = 2 ^ n := by
      have hterm : ∀ r ∈ Finset.range (n + 1),
          (G (n + 1) 0 r ∩ G (n + 1) 1 r ∩ G (n + 1) 0 (r + 1) ∩ G (n + 1) 1 (r + 1)).card =
          n.choose r := fun r hr => by
        simpa using card_G_4way n 0 r (Nat.zero_le _) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))
      rw [Finset.sum_congr rfl hterm, Nat.sum_range_choose]
    have hrest : ∑ c ∈ Finset.range n, ∑ r ∈ Finset.range (n + 1),
        (G (n + 1) (c + 1) r ∩ G (n + 1) (c + 1 + 1) r ∩ G (n + 1) (c + 1) (r + 1) ∩
          G (n + 1) (c + 1 + 1) (r + 1)).card = 3 ^ n - 1 := by
      rw [← sum_G_adj_col n]
      refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun r hr => ?_
      have hcn : c + 1 ≤ n := Finset.mem_range.mp hc
      have hrn : r ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      have h := card_G_4way n (c + 1) r hcn hrn
      simpa using h
    rw [h0, hrest, add_comm]
  rw [h4way] at hsum
  have hpow3_ge : 1 ≤ 3 ^ n := Nat.one_le_pow n 3 (by decide)
  have hpow_le : 2 ^ n ≤ 2 * 3 ^ n := by
    have : 2 ^ n ≤ 3 ^ n := Nat.pow_le_pow_left (by decide) n
    omega
  have h3succ : 3 ^ (n + 1) = 3 * 3 ^ n := by ring
  omega

/-- Exact closed form for `gridCount (n + 1)` for all `n : ℕ`. -/
theorem gridCount_closed_form (n : ℕ) :
    OMA.S_oeis_a163824.gridCount (n + 1) =
      ((2 * (n + 1)).choose (n + 1) : ℤ) - 2 * 3 ^ n + 2 ^ n := by
  rw [gridCount_eq_card_DC]
  have hDC_ie :
      (DC (n + 1)).card + ∑ c ∈ Finset.range (n + 1), (S (n + 1) c ∩ S (n + 1) (c + 1)).card =
        ∑ c ∈ Finset.range (n + 2), (S (n + 1) c).card := by
    have := card_biUnion_interval (n + 2) (S (n + 1)) (fun p a b d hab hbd _ ha hd => by
      simp only [mem_S, Finset.mem_range] at ha hd ⊢
      rcases ha with ⟨r₁, hr₁, h1⟩
      rcases hd with ⟨r₂, hr₂, h2⟩
      rcases isGrid_col_interval hab hbd (by omega) (by omega) h1 h2 with ⟨r, hr, h⟩
      exact ⟨r, by omega, h⟩)
    simpa [DC] using this
  rw [sum_S_eq_central_binom n, sum_S_adj_eq n] at hDC_ie
  have hle : 2 ^ n ≤ 2 * 3 ^ n := by
    have : 2 ^ n ≤ 3 ^ n := Nat.pow_le_pow_left (by decide) n
    omega
  have hDC_int : ((DC (n + 1)).card : ℤ) + ((2 * 3 ^ n - 2 ^ n : ℕ) : ℤ) =
      ((2 * (n + 1)).choose (n + 1) : ℤ) := by
    exact_mod_cast hDC_ie
  rw [Nat.cast_sub hle] at hDC_int
  push_cast at hDC_int
  linarith

end Counting

end OEISA163824Proof

/-- Complete proof of `OMA.S_oeis_a163824.main`. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a163824.main :=
  OEISA163824Proof.recurrence_of_closed_form
    OMA.S_oeis_a163824.gridCount
    OEISA163824Proof.gridCount_closed_form

