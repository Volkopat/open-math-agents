import OMAReductions.R_ManickamMiklosSinghiConjecture_manickam_miklos_singhi_conjecture_variants_pokrovskiy_R1
import Mathlib.Combinatorics.Additive.ETransform
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Combinatorics.Additive.Convolution
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Pokrovskiy's linear bound for the Manickam-Miklos-Singhi conjecture (Step H2)

Self-contained formalization of Pokrovskiy's cyclic double-interval hypergraph theorem
(arXiv:1308.2176, Theorem 1.5), establishing that for `2 <= k`, `10^46 * k <= n < 8 * k^2`,
and any zero-sum weighting `x : Fin n -> Real`, at least `k * (k - 1)^2` cyclic double
intervals have nonnegative sum.
-/

namespace PokrovskiyHypergraph
open Finset

abbrev Idx (n k : ℕ) := Fin n × Fin (k - 1) × Fin (k - 1)

/-- Canonical `ℕ → Fin n` map without typeclass ambiguity. -/
def natToFin {n : ℕ} [NeZero n] (d : ℕ) : Fin n :=
  ⟨d % n, Nat.mod_lt d (NeZero.pos n)⟩

@[simp]
lemma val_natToFin {n : ℕ} [NeZero n] (d : ℕ) : (natToFin d : Fin n).val = d % n := rfl

lemma natToFin_zero {n : ℕ} [NeZero n] : (natToFin 0 : Fin n) = 0 := by
  ext; simp

lemma natToFin_add {n : ℕ} [NeZero n] (a b : ℕ) :
    (natToFin (a + b) : Fin n) = natToFin a + natToFin b := by
  ext
  simp [Fin.val_add, Nat.add_mod]

/-- Exact edge Finset from `H2`. -/
def edgeSet {n k : ℕ} (hn : 2 * k ≤ n) (a : Idx n k) : Finset (Fin n) :=
  univ.image (fun t : Fin k => a.1 + (⟨if t.val ≤ a.2.1.val then t.val else t.val + a.2.2.val + 1,
    by have := t.isLt; have := a.2.2.isLt; split <;> omega⟩ : Fin n))

/-- Cyclic interval `{u, u + 1, ..., u + L - 1}` in `Fin n`. -/
def cycInt {n : ℕ} [NeZero n] (u : Fin n) (L : ℕ) : Finset (Fin n) :=
  image (fun d : ℕ => u + natToFin d) (range L)

lemma card_cycInt {n : ℕ} [NeZero n] (u : Fin n) {L : ℕ} (hL : L ≤ n) :
    #(cycInt u L) = L := by
  unfold cycInt
  rw [card_image_of_injOn, card_range]
  intro d₁ hd₁ d₂ hd₂ heq
  rw [mem_coe, mem_range] at hd₁ hd₂
  have hcancel : (natToFin d₁ : Fin n) = natToFin d₂ := add_left_cancel heq
  have hval := congrArg Fin.val hcancel
  simp only [val_natToFin, Nat.mod_eq_of_lt (lt_of_lt_of_le hd₁ hL),
    Nat.mod_eq_of_lt (lt_of_lt_of_le hd₂ hL)] at hval
  exact hval

lemma cycInt_zero {n : ℕ} [NeZero n] (u : Fin n) : cycInt u 0 = ∅ := by
  simp [cycInt]

lemma cycInt_add {n : ℕ} [NeZero n] (u : Fin n) (L₁ L₂ : ℕ) :
    cycInt u (L₁ + L₂) = cycInt u L₁ ∪ cycInt (u + natToFin L₁) L₂ := by
  ext w
  simp only [cycInt, mem_union, mem_image, mem_range]
  constructor
  · rintro ⟨d, hd, rfl⟩
    by_cases h : d < L₁
    · exact Or.inl ⟨d, h, rfl⟩
    · refine Or.inr ⟨d - L₁, by omega, ?_⟩
      have hd_eq : natToFin L₁ + natToFin (d - L₁) = (natToFin d : Fin n) := by
        rw [← natToFin_add, show L₁ + (d - L₁) = d by omega]
      rw [add_assoc, hd_eq]
  · rintro (⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩)
    · exact ⟨d, by omega, rfl⟩
    · refine ⟨L₁ + d, by omega, ?_⟩
      rw [natToFin_add, add_assoc]

lemma disjoint_cycInt_add {n : ℕ} [NeZero n] (u : Fin n) {L₁ L₂ : ℕ} (hL : L₁ + L₂ ≤ n) :
    Disjoint (cycInt u L₁) (cycInt (u + natToFin L₁) L₂) := by
  rw [disjoint_left]
  intro w hw₁ hw₂
  simp only [cycInt, mem_image, mem_range] at hw₁ hw₂
  rcases hw₁ with ⟨d₁, hd₁, rfl⟩
  rcases hw₂ with ⟨d₂, hd₂, heq⟩
  have h1 : (natToFin d₁ : Fin n) = natToFin (L₁ + d₂) := by
    rw [natToFin_add]
    rw [add_assoc] at heq
    exact add_left_cancel heq.symm
  have hval := congrArg Fin.val h1
  simp only [val_natToFin, Nat.mod_eq_of_lt (by omega : d₁ < n),
    Nat.mod_eq_of_lt (by omega : L₁ + d₂ < n)] at hval
  omega

def intSum {n : ℕ} [NeZero n] (x : Fin n → ℝ) (u : Fin n) (L : ℕ) : ℝ :=
  ∑ w ∈ cycInt u L, x w

lemma intSum_zero {n : ℕ} [NeZero n] (x : Fin n → ℝ) (u : Fin n) :
    intSum x u 0 = 0 := by
  simp [intSum, cycInt_zero]

lemma intSum_add {n : ℕ} [NeZero n] (x : Fin n → ℝ) (u : Fin n) {L₁ L₂ : ℕ}
    (hL : L₁ + L₂ ≤ n) :
    intSum x u (L₁ + L₂) = intSum x u L₁ + intSum x (u + natToFin L₁) L₂ := by
  unfold intSum
  rw [cycInt_add, sum_union (disjoint_cycInt_add u hL)]

lemma intSum_seg {n : ℕ} [NeZero n] (x : Fin n → ℝ) (v : Fin n) {a len : ℕ}
    (h : a + len ≤ n) :
    intSum x (v + natToFin a) len = intSum x v (a + len) - intSum x v a := by
  rw [intSum_add x v h]
  ring

/-- Double-interval decomposition into two disjoint cyclic intervals. -/
lemma edgeSet_eq_union {n k : ℕ} [NeZero n] (hn : 2 * k ≤ n) (a : Idx n k) :
    let i := a.2.1.val + 1
    let j := a.2.2.val + 1
    edgeSet hn a = cycInt a.1 i ∪ cycInt (a.1 + natToFin (i + j)) (k - i) := by
  intro i j
  ext w
  simp only [edgeSet, cycInt, mem_union, mem_image, mem_univ, true_and, mem_range]
  have hi_lt : i < k := by have := a.2.1.isLt; omega
  have hj_lt : j < k := by have := a.2.2.isLt; omega
  constructor
  · rintro ⟨t, rfl⟩
    by_cases ht : t.val ≤ a.2.1.val
    · refine Or.inl ⟨t.val, by omega, ?_⟩
      congr 1
      apply Fin.ext
      simp [ht, Nat.mod_eq_of_lt (by omega : t.val < n)]
    · refine Or.inr ⟨t.val - i, by omega, ?_⟩
      have heq : (i + j) + (t.val - i) = t.val + a.2.2.val + 1 := by omega
      rw [add_assoc, ← natToFin_add, heq]
      congr 1
      apply Fin.ext
      simp [ht, Nat.mod_eq_of_lt (by omega : t.val + a.2.2.val + 1 < n)]
  · rintro (⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩)
    · refine ⟨⟨d, by omega⟩, ?_⟩
      have hd_le : d ≤ a.2.1.val := by omega
      congr 1
      apply Fin.ext
      simp [hd_le, Nat.mod_eq_of_lt (by omega : d < n)]
    · refine ⟨⟨i + d, by omega⟩, ?_⟩
      have hd_gt : ¬ (i + d ≤ a.2.1.val) := by omega
      rw [add_assoc a.1, ← natToFin_add]
      congr 1
      apply Fin.ext
      dsimp only
      rw [if_neg hd_gt, val_natToFin, Nat.mod_eq_of_lt (by omega : (i + j) + d < n)]
      omega

lemma disjoint_edgeSet_parts {n k : ℕ} [NeZero n] (hn : 2 * k ≤ n) (a : Idx n k) :
    let i := a.2.1.val + 1
    let j := a.2.2.val + 1
    Disjoint (cycInt a.1 i) (cycInt (a.1 + natToFin (i + j)) (k - i)) := by
  dsimp only
  have hi_lt : a.2.1.val + 1 < k := by have := a.2.1.isLt; omega
  have hj_lt : a.2.2.val + 1 < k := by have := a.2.2.isLt; omega
  have hsub : cycInt a.1 (a.2.1.val + 1) ⊆ cycInt a.1 (a.2.1.val + 1 + (a.2.2.val + 1)) := by
    rw [cycInt_add a.1 (a.2.1.val + 1) (a.2.2.val + 1)]
    intro w hw
    exact mem_union_left _ hw
  exact (disjoint_cycInt_add a.1
    (by omega : (a.2.1.val + 1 + (a.2.2.val + 1)) + (k - (a.2.1.val + 1)) ≤ n)).mono_left hsub

def edgeSum {n k : ℕ} (hn : 2 * k ≤ n) (x : Fin n → ℝ) (a : Idx n k) : ℝ :=
  ∑ w ∈ edgeSet hn a, x w

lemma edgeSum_eq_intSum_add {n k : ℕ} [NeZero n] (hn : 2 * k ≤ n) (x : Fin n → ℝ) (a : Idx n k) :
    edgeSum hn x a =
      intSum x a.1 (a.2.1.val + 1) +
        intSum x (a.1 + natToFin (a.2.1.val + 1 + (a.2.2.val + 1))) (k - (a.2.1.val + 1)) := by
  unfold edgeSum intSum
  rw [edgeSet_eq_union hn a, sum_union (disjoint_edgeSet_parts hn a)]

def mkIdx {n k : ℕ} (u : Fin n) (a b : ℕ)
    (ha : 1 ≤ a ∧ a ≤ k - 1) (hb : 1 ≤ b ∧ b ≤ k - 1) : Idx n k :=
  (u, ⟨a - 1, by omega⟩, ⟨b - 1, by omega⟩)

/-- Express `edgeSum` of a shifted `mkIdx` directly via prefix sums from `v`! -/
lemma edgeSum_mkIdx_prefix {n k : ℕ} [NeZero n] (hn : 2 * k ≤ n) (x : Fin n → ℝ)
    (v : Fin n) (off a b : ℕ) (ha : 1 ≤ a ∧ a ≤ k - 1) (hb : 1 ≤ b ∧ b ≤ k - 1)
    (hbound : off + k + b ≤ n) :
    edgeSum hn x (mkIdx (v + natToFin off) a b ha hb) =
      (intSum x v (off + a) - intSum x v off) +
        (intSum x v (off + k + b) - intSum x v (off + a + b)) := by
  rw [edgeSum_eq_intSum_add]
  simp only [mkIdx]
  have ha1 : a - 1 + 1 = a := by omega
  have hb1 : b - 1 + 1 = b := by omega
  rw [ha1, hb1]
  have h1 : intSum x (v + natToFin off) a = intSum x v (off + a) - intSum x v off :=
    intSum_seg x v (by omega)
  have h2 : v + natToFin off + natToFin (a + b) = v + natToFin (off + a + b) := by
    rw [add_assoc v, ← natToFin_add, ← add_assoc]
  have h3 : (off + a + b) + (k - a) = off + k + b := by omega
  rw [h1, h2, intSum_seg x v (by omega : (off + a + b) + (k - a) ≤ n), h3]

/- Shift and reflection symmetries on `Idx n k` -/

def shiftIdx {n k : ℕ} (d : Fin n) (e : Idx n k) : Idx n k :=
  (d + e.1, e.2.1, e.2.2)

lemma shiftIdx_injective {n k : ℕ} (d : Fin n) : Function.Injective (shiftIdx (k := k) d) := by
  rintro ⟨u₁, i₁, j₁⟩ ⟨u₂, i₂, j₂⟩ h
  simp only [shiftIdx, Prod.mk.injEq] at h
  exact Prod.ext (add_left_cancel h.1) (Prod.ext h.2.1 h.2.2)

lemma edgeSet_shiftIdx {n k : ℕ} (hn : 2 * k ≤ n) (d : Fin n) (e : Idx n k) :
    edgeSet hn (shiftIdx d e) = image (fun w => d + w) (edgeSet hn e) := by
  ext w
  simp only [edgeSet, shiftIdx, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨e.1 + _, ⟨t, rfl⟩, (add_assoc d e.1 _).symm⟩
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨t, add_assoc d e.1 _⟩

lemma edgeSum_shiftIdx {n k : ℕ} (hn : 2 * k ≤ n) (x : Fin n → ℝ) (d : Fin n) (e : Idx n k) :
    edgeSum hn x (shiftIdx d e) = edgeSum hn (fun w => x (d + w)) e := by
  unfold edgeSum
  rw [edgeSet_shiftIdx, sum_image (fun _ _ _ _ h => add_left_cancel h)]

def reflIdx {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (c : Fin n) (e : Idx n k) : Idx n k :=
  (c - (e.1 + natToFin (e.2.2.val + k)),
    ⟨k - 2 - e.2.1.val, by have := e.2.1.isLt; omega⟩,
    e.2.2)

lemma reflIdx_involutive {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (c : Fin n) :
    Function.Involutive (reflIdx (n := n) hk c) := by
  rintro ⟨u, i₀, j₀⟩
  have hi : i₀.val < k - 1 := i₀.isLt
  ext
  · simp only [reflIdx]; abel_nf
  · simp only [reflIdx]; omega
  · rfl

lemma reflIdx_injective {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (c : Fin n) :
    Function.Injective (reflIdx (n := n) hk c) :=
  (reflIdx_involutive hk c).injective

lemma cycInt_image_sub {n : ℕ} [NeZero n] (c u : Fin n) {L : ℕ} (hL : 1 ≤ L) :
    image (fun w => c - w) (cycInt u L) = cycInt (c - (u + natToFin (L - 1))) L := by
  ext w
  simp only [cycInt, mem_image, mem_range]
  constructor
  · rintro ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    refine ⟨L - 1 - d, by omega, ?_⟩
    have heq : L - 1 = d + (L - 1 - d) := by omega
    have hcast : (natToFin (L - 1) : Fin n) = natToFin d + natToFin (L - 1 - d) := by
      rw [← natToFin_add, ← heq]
    rw [hcast]; abel
  · rintro ⟨d, hd, rfl⟩
    refine ⟨u + natToFin (L - 1 - d), ⟨L - 1 - d, by omega, rfl⟩, ?_⟩
    have heq : L - 1 = (L - 1 - d) + d := by omega
    have hcast : (natToFin (L - 1) : Fin n) = natToFin (L - 1 - d) + natToFin d := by
      rw [← natToFin_add, ← heq]
    rw [hcast]; abel

lemma edgeSet_reflIdx {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hn : 2 * k ≤ n)
    (c : Fin n) (e : Idx n k) :
    edgeSet hn (reflIdx hk c e) = image (fun w => c - w) (edgeSet hn e) := by
  have hi : e.2.1.val < k - 1 := e.2.1.isLt
  have hj : e.2.2.val < k - 1 := e.2.2.isLt
  rw [edgeSet_eq_union hn e, image_union,
    cycInt_image_sub c e.1 (by omega : 1 ≤ e.2.1.val + 1),
    cycInt_image_sub c _ (by omega : 1 ≤ k - (e.2.1.val + 1)),
    edgeSet_eq_union hn (reflIdx hk c e), union_comm]
  congr 1
  · simp only [reflIdx]
    have hlen : k - (k - 2 - e.2.1.val + 1) = e.2.1.val + 1 := by omega
    rw [hlen]
    congr 1
    have h1 : e.2.1.val + 1 - 1 = e.2.1.val := by omega
    have h2 : (k - 2 - e.2.1.val + 1 + (e.2.2.val + 1)) + e.2.1.val = e.2.2.val + k := by omega
    rw [h1]
    have hcast : (natToFin (k - 2 - e.2.1.val + 1 + (e.2.2.val + 1)) : Fin n) =
        natToFin (e.2.2.val + k) - natToFin e.2.1.val := by
      rw [eq_sub_iff_add_eq, ← natToFin_add, h2]
    rw [hcast]; abel
  · simp only [reflIdx]
    have hlen : k - 2 - e.2.1.val + 1 = k - (e.2.1.val + 1) := by omega
    rw [hlen]
    congr 1
    have hsum : (e.2.1.val + 1 + (e.2.2.val + 1)) + (k - (e.2.1.val + 1) - 1) =
        e.2.2.val + k := by omega
    rw [add_assoc, ← natToFin_add, hsum]

lemma edgeSum_reflIdx {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hn : 2 * k ≤ n)
    (x : Fin n → ℝ) (c : Fin n) (e : Idx n k) :
    edgeSum hn x (reflIdx hk c e) = edgeSum hn (fun w => x (c - w)) e := by
  unfold edgeSum
  rw [edgeSet_reflIdx, sum_image (fun _ _ _ _ h => sub_right_injective h)]

/- Structured 41-element Slot type -/

inductive Slot : Type
  | univ : Fin 4 → Slot
  | gtExtra : Fin 3 → Slot
  | gtGe : Fin 6 → Slot
  | gtLt : Fin 6 → Slot
  | ltPar : Bool → Fin 11 → Slot
  deriving DecidableEq

def allSlots : Finset Slot :=
  image Slot.univ univ ∪
  image Slot.gtExtra univ ∪
  image Slot.gtGe univ ∪
  image Slot.gtLt univ ∪
  image (Slot.ltPar false) univ ∪
  image (Slot.ltPar true) univ

lemma mem_allSlots (s : Slot) : s ∈ allSlots := by
  unfold allSlots
  cases s with
  | univ m => simp
  | gtExtra m => simp
  | gtGe m => simp
  | gtLt m => simp
  | ltPar b m => cases b <;> simp

lemma card_allSlots_le : #allSlots ≤ 41 := by
  unfold allSlots
  have h1 := card_union_le (image Slot.univ univ ∪ image Slot.gtExtra univ ∪
    image Slot.gtGe univ ∪ image Slot.gtLt univ ∪ image (Slot.ltPar false) univ)
    (image (Slot.ltPar true) univ)
  have h2 := card_union_le (image Slot.univ univ ∪ image Slot.gtExtra univ ∪
    image Slot.gtGe univ ∪ image Slot.gtLt univ) (image (Slot.ltPar false) univ)
  have h3 := card_union_le (image Slot.univ univ ∪ image Slot.gtExtra univ ∪
    image Slot.gtGe univ) (image Slot.gtLt univ)
  have h4 := card_union_le (image Slot.univ univ ∪ image Slot.gtExtra univ)
    (image Slot.gtGe univ)
  have h5 := card_union_le (image Slot.univ univ) (image Slot.gtExtra univ)
  have c1 : #(image Slot.univ univ) ≤ 4 := card_image_le.trans (by simp)
  have c2 : #(image Slot.gtExtra univ) ≤ 3 := card_image_le.trans (by simp)
  have c3 : #(image Slot.gtGe univ) ≤ 6 := card_image_le.trans (by simp)
  have c4 : #(image Slot.gtLt univ) ≤ 6 := card_image_le.trans (by simp)
  have c5 : #(image (Slot.ltPar false) univ) ≤ 11 := card_image_le.trans (by simp)
  have c6 : #(image (Slot.ltPar true) univ) ≤ 11 := card_image_le.trans (by simp)
  omega

instance : Fintype Slot where
  elems := allSlots
  complete := mem_allSlots

lemma fintype_card_slot_le : Fintype.card Slot ≤ 41 :=
  card_allSlots_le

/-- Slot specification `(cond, offset, lenA, lenB)` for `1 ≤ i, j ≤ k - 1`. -/
def slotSpec (k : ℕ) (s : Slot) (i j : ℕ) : Bool × ℕ × ℕ × ℕ :=
  match s with
  | .univ m =>
    match m.val with
    | 0 => (true, 0, i, j)
    | 1 => (true, i, j, k - i)
    | 2 => (true, 2 * k, i, j)
    | _ => (true, 2 * k + i, j, k - i)
  | .gtExtra m =>
    let c := decide (k < i + j)
    match m.val with
    | 0 => (c, i, j, 2 * k - i - j)
    | 1 => (c, 3 * k - j, i, j)
    | _ => (c, 3 * k - j + i, j, k - i)
  | .gtGe m =>
    let c := decide (k < i + j ∧ j ≤ i)
    match m.val with
    | 0 => (c, 0, i, i + j - k)
    | 1 => (c, i, i + j - k, 2 * k - 2 * i)
    | 2 => (c, i + j, k - i, 2 * k - i - j)
    | 3 => (c, k + j, i, i + j - k)
    | 4 => (c, k + i + j, i + j - k, 2 * k - 2 * i)
    | _ => (c, k + i + 2 * j, k - i, 2 * k - i - j)
  | .gtLt m =>
    let c := decide (k < i + j ∧ i < j)
    match m.val with
    | 0 => (c, 0, j, i + j - k)
    | 1 => (c, j, i + j - k, 2 * k - 2 * j)
    | 2 => (c, i + j, k - j, 2 * k - i - j)
    | 3 => (c, k + j, j, i + j - k)
    | 4 => (c, k + 2 * j, i + j - k, 2 * k - 2 * j)
    | _ => (c, k + i + 2 * j, k - j, 2 * k - i - j)
  | .ltPar odd m =>
    let c := decide (i + j < k ∧ 2 ≤ i ∧ i % 2 = (if odd then 1 else 0))
    let h := i / 2
    match m.val with
    | 0 => (c, 0, k - h, i + j)
    | 1 => (c, k - h, i + j, 2 * h)
    | 2 => (c, k + i + j, h, k - i - j)
    | 3 => (c, k + j, k - h, i + j)
    | 4 => (c, 2 * k + j - h, i + j, 2 * h)
    | 5 => (c, 2 * k + i + 2 * j, h, k - i - j)
    | 6 => (c, 0, i + j, h)
    | 7 => (c, i, j + h, k - i - j)
    | 8 => (c, 2 * k - j, k - h, i + j)
    | 9 => (c, 3 * k - j - h, i + j, 2 * h)
    | _ => (c, 3 * k + i, h, k - i - j)

lemma slotSpec_valid {k : ℕ} (s : Slot) {i j : ℕ}
    (hi : 1 ≤ i ∧ i ≤ k - 1) (hj : 1 ≤ j ∧ j ≤ k - 1)
    (hc : (slotSpec k s i j).1 = true) :
    1 ≤ (slotSpec k s i j).2.2.1 ∧ (slotSpec k s i j).2.2.1 ≤ k - 1 ∧
      1 ≤ (slotSpec k s i j).2.2.2 ∧ (slotSpec k s i j).2.2.2 ≤ k - 1 := by
  cases s with
  | univ m => fin_cases m <;> simp only [slotSpec] at hc ⊢ <;> omega
  | gtExtra m => fin_cases m <;> simp only [slotSpec, decide_eq_true_eq] at hc ⊢ <;> omega
  | gtGe m => fin_cases m <;> simp only [slotSpec, decide_eq_true_eq] at hc ⊢ <;> omega
  | gtLt m => fin_cases m <;> simp only [slotSpec, decide_eq_true_eq] at hc ⊢ <;> omega
  | ltPar odd m =>
    cases odd <;> fin_cases m <;> simp only [slotSpec, decide_eq_true_eq] at hc ⊢ <;> omega

lemma slotSpec_inj {k : ℕ} (s : Slot) {i₁ j₁ i₂ j₂ : ℕ}
    (hi₁ : 1 ≤ i₁ ∧ i₁ ≤ k - 1) (hj₁ : 1 ≤ j₁ ∧ j₁ ≤ k - 1)
    (hi₂ : 1 ≤ i₂ ∧ i₂ ≤ k - 1) (hj₂ : 1 ≤ j₂ ∧ j₂ ≤ k - 1)
    (hc₁ : (slotSpec k s i₁ j₁).1 = true) (hc₂ : (slotSpec k s i₂ j₂).1 = true)
    (ha : (slotSpec k s i₁ j₁).2.2.1 = (slotSpec k s i₂ j₂).2.2.1)
    (hb : (slotSpec k s i₁ j₁).2.2.2 = (slotSpec k s i₂ j₂).2.2.2) :
    i₁ = i₂ ∧ j₁ = j₂ := by
  cases s with
  | univ m => fin_cases m <;> simp only [slotSpec] at hc₁ hc₂ ha hb <;> omega
  | gtExtra m => fin_cases m <;> simp only [slotSpec, decide_eq_true_eq] at hc₁ hc₂ ha hb <;> omega
  | gtGe m => fin_cases m <;> simp only [slotSpec, decide_eq_true_eq] at hc₁ hc₂ ha hb <;> omega
  | gtLt m => fin_cases m <;> simp only [slotSpec, decide_eq_true_eq] at hc₁ hc₂ ha hb <;> omega
  | ltPar odd m =>
    cases odd <;> fin_cases m <;> simp only [slotSpec, decide_eq_true_eq] at hc₁ hc₂ ha hb <;> omega

def evalSlot {n k : ℕ} [NeZero n] (s : Slot) (p : Idx n k) : Option (Idx n k) :=
  let sp := slotSpec k s (p.2.1.val + 1) (p.2.2.val + 1)
  if hc : sp.1 = true then
    let vld := slotSpec_valid s ⟨by omega, by have := p.2.1.isLt; omega⟩
      ⟨by omega, by have := p.2.2.isLt; omega⟩ hc
    some (mkIdx (p.1 + natToFin sp.2.1)
      sp.2.2.1 sp.2.2.2 ⟨vld.1, vld.2.1⟩ ⟨vld.2.2.1, vld.2.2.2⟩)
  else
    none

lemma evalSlot_shift {n k : ℕ} [NeZero n] (s : Slot) (d : Fin n) (p : Idx n k) :
    evalSlot s (shiftIdx d p) = (evalSlot s p).map (shiftIdx d) := by
  unfold evalSlot shiftIdx
  dsimp only
  split_ifs with hc
  · simp only [Option.map_some, mkIdx, add_assoc]
  · rfl

lemma evalSlot_inj {n k : ℕ} [NeZero n] (s : Slot) {p₁ p₂ : Idx n k} {e : Idx n k}
    (h₁ : evalSlot s p₁ = some e) (h₂ : evalSlot s p₂ = some e) :
    p₁ = p₂ := by
  unfold evalSlot at h₁ h₂
  dsimp only at h₁ h₂
  split_ifs at h₁ with hc₁
  split_ifs at h₂ with hc₂
  rw [Option.some.injEq] at h₁ h₂
  have heq := h₁.trans h₂.symm
  simp only [mkIdx, Prod.mk.injEq, Fin.ext_iff] at heq
  have vld₁ := slotSpec_valid s ⟨by omega, by have := p₁.2.1.isLt; omega⟩
    ⟨by omega, by have := p₁.2.2.isLt; omega⟩ hc₁
  have vld₂ := slotSpec_valid s ⟨by omega, by have := p₂.2.1.isLt; omega⟩
    ⟨by omega, by have := p₂.2.2.isLt; omega⟩ hc₂
  have ha : (slotSpec k s (p₁.2.1.val + 1) (p₁.2.2.val + 1)).2.2.1 =
      (slotSpec k s (p₂.2.1.val + 1) (p₂.2.2.val + 1)).2.2.1 := by omega
  have hb : (slotSpec k s (p₁.2.1.val + 1) (p₁.2.2.val + 1)).2.2.2 =
      (slotSpec k s (p₂.2.1.val + 1) (p₂.2.2.val + 1)).2.2.2 := by omega
  obtain ⟨hi_eq, hj_eq⟩ := slotSpec_inj s
    ⟨by omega, by have := p₁.2.1.isLt; omega⟩ ⟨by omega, by have := p₁.2.2.isLt; omega⟩
    ⟨by omega, by have := p₂.2.1.isLt; omega⟩ ⟨by omega, by have := p₂.2.2.isLt; omega⟩
    hc₁ hc₂ ha hb
  have hij₁ : p₁.2.1 = p₂.2.1 := Fin.ext (by omega)
  have hij₂ : p₁.2.2 = p₂.2.2 := Fin.ext (by omega)
  have hoff : (slotSpec k s (p₁.2.1.val + 1) (p₁.2.2.val + 1)).2.1 =
      (slotSpec k s (p₂.2.1.val + 1) (p₂.2.2.val + 1)).2.1 := by
    rw [hi_eq, hj_eq]
  have hv_fin : p₁.1 + natToFin (slotSpec k s (p₁.2.1.val + 1) (p₁.2.2.val + 1)).2.1 =
      p₂.1 + natToFin (slotSpec k s (p₂.2.1.val + 1) (p₂.2.2.val + 1)).2.1 :=
    Fin.ext heq.1
  rw [hoff] at hv_fin
  exact Prod.ext (add_right_cancel hv_fin) (Prod.ext hij₁ hij₂)

def bundlePlus {n k : ℕ} [NeZero n] (v : Fin n) (i₀ j₀ : Fin (k - 1)) : Finset (Idx n k) :=
  allSlots.biUnion (fun s =>
    match evalSlot s (v, i₀, j₀) with
    | some e => {e}
    | none => ∅)

def bundleMinus {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (v : Fin n) (i₀ j₀ : Fin (k - 1)) :
    Finset (Idx n k) :=
  image (reflIdx hk (v + v)) (bundlePlus v i₀ j₀)

def bundle {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (v : Fin n) : Finset (Idx n k) :=
  (univ : Finset (Fin (k - 1) × Fin (k - 1))).biUnion
    (fun ij => bundlePlus v ij.1 ij.2 ∪ bundleMinus hk v ij.1 ij.2)

lemma bundlePlus_shift {n k : ℕ} [NeZero n] (d v : Fin n) (i₀ j₀ : Fin (k - 1)) :
    bundlePlus (d + v) i₀ j₀ = image (shiftIdx d) (bundlePlus v i₀ j₀) := by
  ext e
  simp only [bundlePlus, mem_biUnion, mem_image]
  constructor
  · rintro ⟨s, hs, he⟩
    have hsh := evalSlot_shift s d (v, i₀, j₀)
    change evalSlot s (d + v, i₀, j₀) = _ at hsh
    rw [hsh] at he
    cases h : evalSlot s (v, i₀, j₀) with
    | none => simp [h] at he
    | some e₀ =>
      simp only [h, Option.map_some, mem_singleton] at he
      exact ⟨e₀, ⟨s, hs, by simp [h]⟩, he.symm⟩
  · rintro ⟨e₀, ⟨s, hs, he₀⟩, rfl⟩
    refine ⟨s, hs, ?_⟩
    have hsh := evalSlot_shift s d (v, i₀, j₀)
    change evalSlot s (d + v, i₀, j₀) = _ at hsh
    rw [hsh]
    cases h : evalSlot s (v, i₀, j₀) with
    | none => simp [h] at he₀
    | some e₁ =>
      simp only [h, mem_singleton] at he₀
      subst he₀
      simp

lemma bundle_shift {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (d v : Fin n) :
    bundle hk (d + v) = image (shiftIdx d) (bundle hk v) := by
  have hminus : ∀ i₀ j₀, bundleMinus hk (d + v) i₀ j₀ =
      image (shiftIdx d) (bundleMinus hk v i₀ j₀) := by
    intro i₀ j₀
    unfold bundleMinus
    rw [bundlePlus_shift, image_image, image_image]
    refine image_congr fun e _ => ?_
    ext
    · simp only [Function.comp_apply, reflIdx, shiftIdx]
      abel_nf
    · rfl
    · rfl
  ext e
  simp only [bundle, mem_biUnion, mem_univ, true_and, mem_image]
  constructor
  · rintro ⟨ij, hij⟩
    rw [bundlePlus_shift, hminus, ← image_union, mem_image] at hij
    rcases hij with ⟨e₀, he₀, rfl⟩
    exact ⟨e₀, ⟨ij, he₀⟩, rfl⟩
  · rintro ⟨e₀, ⟨ij, he₀⟩, rfl⟩
    refine ⟨ij, ?_⟩
    rw [bundlePlus_shift, hminus, ← image_union]
    exact mem_image_of_mem _ he₀

lemma bundle_refl {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (m v : Fin n) :
    image (reflIdx hk m) (bundle hk v) = bundle hk (m - v) := by
  have hswap : ∀ i₀ j₀,
      image (reflIdx hk m) (bundlePlus v i₀ j₀ ∪ bundleMinus hk v i₀ j₀) =
        bundlePlus (m - v) i₀ j₀ ∪ bundleMinus hk (m - v) i₀ j₀ := by
    intro i₀ j₀
    rw [image_union, union_comm]
    have hsh : m - v = (m - (v + v)) + v := by abel
    congr 1
    · unfold bundleMinus
      rw [hsh, bundlePlus_shift, image_image]
      refine image_congr fun e _ => ?_
      ext
      · simp only [Function.comp_apply, reflIdx, shiftIdx]
        abel_nf
      · simp only [Function.comp_apply, reflIdx, shiftIdx]
        have hi : e.2.1.val < k - 1 := e.2.1.isLt
        omega
      · rfl
    · unfold bundleMinus
      have hsh2 := bundlePlus_shift (m - (v + v)) v i₀ j₀
      rw [← hsh] at hsh2
      rw [hsh2, image_image]
      refine image_congr fun e _ => ?_
      ext
      · simp only [Function.comp_apply, reflIdx, shiftIdx]
        abel_nf
      · rfl
      · rfl
  ext e
  simp only [bundle, mem_image, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨e₀, ⟨ij, he₀⟩, rfl⟩
    exact ⟨ij, by rw [← hswap]; exact mem_image_of_mem _ he₀⟩
  · rintro ⟨ij, he⟩
    rw [← hswap, mem_image] at he
    rcases he with ⟨e₀, he₀, rfl⟩
    exact ⟨e₀, ⟨ij, he₀⟩, rfl⟩

/-- Degree bound Lemma 3.2 (`spreadout`): every `e : Idx n k` belongs to at most `88`
triples `(v, i₀, j₀)` via `bundlePlus ∪ bundleMinus`! -/
lemma card_triples_containing_le {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (e : Idx n k) :
    #(univ.filter (fun p : Idx n k => e ∈ bundlePlus p.1 p.2.1 p.2.2 ∪
      bundleMinus hk p.1 p.2.1 p.2.2)) ≤ 88 := by
  let Fplus := univ.filter (fun p : Idx n k => e ∈ bundlePlus p.1 p.2.1 p.2.2)
  let Fminus := univ.filter (fun p : Idx n k => e ∈ bundleMinus hk p.1 p.2.1 p.2.2)
  have hsub : univ.filter (fun p : Idx n k => e ∈ bundlePlus p.1 p.2.1 p.2.2 ∪
      bundleMinus hk p.1 p.2.1 p.2.2) ⊆ Fplus ∪ Fminus := by
    intro p hp
    simp only [Fplus, Fminus, mem_union, mem_filter, mem_univ, true_and] at hp ⊢
    exact hp
  have hplus_le : #Fplus ≤ 41 := by
    have hex : ∀ p ∈ Fplus, ∃ s : Slot, evalSlot s p = some e := by
      intro p hp
      simp only [Fplus, bundlePlus, mem_filter, mem_univ, true_and, mem_biUnion] at hp
      rcases hp with ⟨s, _, hs⟩
      cases h : evalSlot s p with
      | none => simp [h] at hs
      | some e' =>
        simp only [h, mem_singleton] at hs
        exact ⟨s, hs ▸ h⟩
    choose f hf using hex
    have hinj : Function.Injective (fun x : {p // p ∈ Fplus} => f x.1 x.2) := by
      intro x y heq
      have h1 := hf x.1 x.2
      have h2 := hf y.1 y.2
      dsimp at heq
      rw [heq] at h1
      exact Subtype.ext (evalSlot_inj _ h1 h2)
    have hcard := (Fintype.card_le_of_injective _ hinj).trans fintype_card_slot_le
    simpa using hcard
  have hminus_le : #Fminus ≤ 41 := by
    have hex : ∀ p ∈ Fminus, ∃ s : Slot, evalSlot s p = some (reflIdx hk (p.1 + p.1) e) := by
      intro p hp
      simp only [Fminus, bundleMinus, bundlePlus, mem_filter, mem_univ, true_and, mem_image,
        mem_biUnion] at hp
      rcases hp with ⟨e', ⟨s, _, hs⟩, he'⟩
      cases h : evalSlot s p with
      | none => simp [h] at hs
      | some e₁ =>
        simp only [h, mem_singleton] at hs
        have hrev : e₁ = reflIdx hk (p.1 + p.1) e := by
          rw [← he', hs, reflIdx_involutive hk (p.1 + p.1) e₁]
        exact ⟨s, hrev ▸ h⟩
    choose f hf using hex
    have hinj : Function.Injective (fun x : {p // p ∈ Fminus} => f x.1 x.2) := by
      intro x y heq
      have h1 := hf x.1 x.2
      have h2 := hf y.1 y.2
      dsimp at heq
      rw [heq] at h1
      let s := f y.1 y.2
      change evalSlot s x.1 = _ at h1
      change evalSlot s y.1 = _ at h2
      unfold evalSlot at h1 h2
      dsimp only at h1 h2
      split_ifs at h1 with hc₁
      split_ifs at h2 with hc₂
      rw [Option.some.injEq] at h1 h2
      simp only [mkIdx, reflIdx, Prod.mk.injEq, Fin.ext_iff] at h1 h2
      have vld₁ := slotSpec_valid s ⟨by omega, by have := x.1.2.1.isLt; omega⟩
        ⟨by omega, by have := x.1.2.2.isLt; omega⟩ hc₁
      have vld₂ := slotSpec_valid s ⟨by omega, by have := y.1.2.1.isLt; omega⟩
        ⟨by omega, by have := y.1.2.2.isLt; omega⟩ hc₂
      have ha : (slotSpec k s (x.1.2.1.val + 1) (x.1.2.2.val + 1)).2.2.1 =
          (slotSpec k s (y.1.2.1.val + 1) (y.1.2.2.val + 1)).2.2.1 := by omega
      have hb : (slotSpec k s (x.1.2.1.val + 1) (x.1.2.2.val + 1)).2.2.2 =
          (slotSpec k s (y.1.2.1.val + 1) (y.1.2.2.val + 1)).2.2.2 := by omega
      obtain ⟨hi_eq, hj_eq⟩ := slotSpec_inj s
        ⟨by omega, by have := x.1.2.1.isLt; omega⟩ ⟨by omega, by have := x.1.2.2.isLt; omega⟩
        ⟨by omega, by have := y.1.2.1.isLt; omega⟩ ⟨by omega, by have := y.1.2.2.isLt; omega⟩
        hc₁ hc₂ ha hb
      have hij₁ : x.1.2.1 = y.1.2.1 := Fin.ext (by omega)
      have hij₂ : x.1.2.2 = y.1.2.2 := Fin.ext (by omega)
      have hoff : (slotSpec k s (x.1.2.1.val + 1) (x.1.2.2.val + 1)).2.1 =
          (slotSpec k s (y.1.2.1.val + 1) (y.1.2.2.val + 1)).2.1 := by
        rw [hi_eq, hj_eq]
      have hx_fin : x.1.1 + natToFin (slotSpec k s (x.1.2.1.val + 1) (x.1.2.2.val + 1)).2.1 =
          (x.1.1 + x.1.1) - (e.1 + natToFin (e.2.2.val + k)) := Fin.ext h1.1
      have hy_fin : y.1.1 + natToFin (slotSpec k s (y.1.2.1.val + 1) (y.1.2.2.val + 1)).2.1 =
          (y.1.1 + y.1.1) - (e.1 + natToFin (e.2.2.val + k)) := Fin.ext h2.1
      rw [hoff] at hx_fin
      have hv_eq : x.1.1 = y.1.1 := by
        have hx' : x.1.1 = (e.1 + natToFin (e.2.2.val + k)) +
            natToFin (slotSpec k s (y.1.2.1.val + 1) (y.1.2.2.val + 1)).2.1 := by
          calc x.1.1 = ((x.1.1 + x.1.1) - (e.1 + natToFin (e.2.2.val + k))) - x.1.1 +
              (e.1 + natToFin (e.2.2.val + k)) := by abel
          _ = (x.1.1 + natToFin (slotSpec k s (y.1.2.1.val + 1) (y.1.2.2.val + 1)).2.1) -
              x.1.1 + (e.1 + natToFin (e.2.2.val + k)) := by rw [hx_fin]
          _ = _ := by abel
        have hy' : y.1.1 = (e.1 + natToFin (e.2.2.val + k)) +
            natToFin (slotSpec k s (y.1.2.1.val + 1) (y.1.2.2.val + 1)).2.1 := by
          calc y.1.1 = ((y.1.1 + y.1.1) - (e.1 + natToFin (e.2.2.val + k))) - y.1.1 +
              (e.1 + natToFin (e.2.2.val + k)) := by abel
          _ = (y.1.1 + natToFin (slotSpec k s (y.1.2.1.val + 1) (y.1.2.2.val + 1)).2.1) -
              y.1.1 + (e.1 + natToFin (e.2.2.val + k)) := by rw [hy_fin]
          _ = _ := by abel
        exact hx'.trans hy'.symm
      exact Subtype.ext (Prod.ext hv_eq (Prod.ext hij₁ hij₂))
    have hcard := (Fintype.card_le_of_injective _ hinj).trans fintype_card_slot_le
    simpa using hcard
  have hunion := (card_le_card hsub).trans (card_union_le Fplus Fminus)
  omega

lemma card_vertices_containing_le {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (e : Idx n k) :
    #(univ.filter (fun v : Fin n => e ∈ bundle hk v)) ≤ 88 := by
  let V := univ.filter (fun v : Fin n => e ∈ bundle hk v)
  let T := univ.filter (fun p : Idx n k => e ∈ bundlePlus p.1 p.2.1 p.2.2 ∪
    bundleMinus hk p.1 p.2.1 p.2.2)
  have hex : ∀ x : {v // v ∈ V}, ∃ ij : Fin (k - 1) × Fin (k - 1), (x.1, ij) ∈ T := by
    rintro ⟨v, hv⟩
    simp only [V, bundle, mem_filter, mem_univ, true_and, mem_biUnion] at hv
    rcases hv with ⟨ij, hij⟩
    exact ⟨ij, mem_filter.mpr ⟨mem_univ _, hij⟩⟩
  choose g hg using hex
  have hinj : Function.Injective (fun x : {v // v ∈ V} => (⟨(x.1, g x), hg x⟩ : {p // p ∈ T})) := by
    intro x y h
    have hv : x.1 = y.1 := congrArg (fun z : {p // p ∈ T} => z.1.1) h
    exact Subtype.ext hv
  have hcard := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_coe] at hcard
  exact hcard.trans (card_triples_containing_le hk e)

lemma card_bundle_le {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (v : Fin n) :
    #(bundle hk v) ≤ 88 * k ^ 2 := by
  unfold bundle
  calc #((univ : Finset (Fin (k - 1) × Fin (k - 1))).biUnion _)
    _ ≤ ∑ ij : Fin (k - 1) × Fin (k - 1), #(bundlePlus v ij.1 ij.2 ∪ bundleMinus hk v ij.1 ij.2) :=
      card_biUnion_le
    _ ≤ ∑ _ij : Fin (k - 1) × Fin (k - 1), 88 := by
      refine sum_le_sum fun ij _ => ?_
      have hp : #(bundlePlus v ij.1 ij.2) ≤ 41 := by
        unfold bundlePlus
        calc #(allSlots.biUnion _)
          _ ≤ ∑ s ∈ allSlots, #(match evalSlot s (v, ij.1, ij.2) with | some e => {e} | none => ∅) :=
            card_biUnion_le
          _ ≤ ∑ _s ∈ allSlots, 1 := by
            refine sum_le_sum fun s _ => ?_
            cases evalSlot s (v, ij.1, ij.2) <;> simp
          _ = #allSlots := by simp
          _ ≤ 41 := card_allSlots_le
      have hm : #(bundleMinus hk v ij.1 ij.2) ≤ 41 := card_image_le.trans hp
      have hu := card_union_le (bundlePlus v ij.1 ij.2) (bundleMinus hk v ij.1 ij.2)
      omega
    _ = (k - 1) * (k - 1) * 88 := by simp
    _ ≤ 88 * k ^ 2 := by
      have hle : k - 1 ≤ k := Nat.sub_le k 1
      calc (k - 1) * (k - 1) * 88 ≤ k * k * 88 :=
          Nat.mul_le_mul_right 88 (Nat.mul_le_mul hle hle)
        _ = 88 * k ^ 2 := by ring

/- Lemma 3.1 (`nonnegativeintervals`): the 5 interval sum identities -/

def isInterior (k : ℕ) (i₀ j₀ : Fin (k - 1)) : Prop :=
  let i := i₀.val + 1
  let j := j₀.val + 1
  i + j ≠ k ∧ (i + j < k → 2 ≤ i)

lemma slot_edgeSum_neg {n k : ℕ} [NeZero n] (hn : 5 * k ≤ n) {x : Fin n → ℝ}
    {v : Fin n} {i₀ j₀ : Fin (k - 1)}
    (hall : ∀ e ∈ bundlePlus v i₀ j₀, edgeSum (by omega) x e < 0)
    (s : Slot) (hc : (slotSpec k s (i₀.val + 1) (j₀.val + 1)).1 = true) :
    (intSum x v ((slotSpec k s (i₀.val + 1) (j₀.val + 1)).2.1 +
        (slotSpec k s (i₀.val + 1) (j₀.val + 1)).2.2.1) -
      intSum x v (slotSpec k s (i₀.val + 1) (j₀.val + 1)).2.1) +
    (intSum x v ((slotSpec k s (i₀.val + 1) (j₀.val + 1)).2.1 + k +
        (slotSpec k s (i₀.val + 1) (j₀.val + 1)).2.2.2) -
      intSum x v ((slotSpec k s (i₀.val + 1) (j₀.val + 1)).2.1 +
        (slotSpec k s (i₀.val + 1) (j₀.val + 1)).2.2.1 +
        (slotSpec k s (i₀.val + 1) (j₀.val + 1)).2.2.2)) < 0 := by
  have hi : 1 ≤ i₀.val + 1 ∧ i₀.val + 1 ≤ k - 1 := ⟨by omega, by have := i₀.isLt; omega⟩
  have hj : 1 ≤ j₀.val + 1 ∧ j₀.val + 1 ≤ k - 1 := ⟨by omega, by have := j₀.isLt; omega⟩
  have vld := slotSpec_valid s hi hj hc
  let e := mkIdx (v + natToFin (slotSpec k s (i₀.val + 1) (j₀.val + 1)).2.1)
    (slotSpec k s (i₀.val + 1) (j₀.val + 1)).2.2.1
    (slotSpec k s (i₀.val + 1) (j₀.val + 1)).2.2.2
    ⟨vld.1, vld.2.1⟩ ⟨vld.2.2.1, vld.2.2.2⟩
  have hmem : e ∈ bundlePlus v i₀ j₀ := by
    unfold bundlePlus
    rw [mem_biUnion]
    refine ⟨s, mem_allSlots s, ?_⟩
    have hev : evalSlot s (v, i₀, j₀) = some e := by
      unfold evalSlot
      dsimp only
      rw [dif_pos hc]
    rw [hev]
    exact mem_singleton_self e
  have hneg := hall e hmem
  have hbound : (slotSpec k s (i₀.val + 1) (j₀.val + 1)).2.1 + k +
      (slotSpec k s (i₀.val + 1) (j₀.val + 1)).2.2.2 ≤ n := by
    cases s with
    | univ m => fin_cases m <;> simp only [slotSpec] at hc ⊢ <;> omega
    | gtExtra m => fin_cases m <;> simp only [slotSpec, decide_eq_true_eq] at hc ⊢ <;> omega
    | gtGe m => fin_cases m <;> simp only [slotSpec, decide_eq_true_eq] at hc ⊢ <;> omega
    | gtLt m => fin_cases m <;> simp only [slotSpec, decide_eq_true_eq] at hc ⊢ <;> omega
    | ltPar odd m =>
      cases odd <;> fin_cases m <;> simp only [slotSpec, decide_eq_true_eq] at hc ⊢ <;> omega
  rw [edgeSum_mkIdx_prefix (by omega) x v _ _ _
    ⟨vld.1, vld.2.1⟩ ⟨vld.2.2.1, vld.2.2.2⟩ hbound] at hneg
  exact hneg

/-- Lemma 3.1(i): `intSum x v (2 * k) < 0` whenever `bundlePlus v i₀ j₀` is all-negative. -/
lemma intSum_twoK_neg {n k : ℕ} [NeZero n] (hn : 5 * k ≤ n) {x : Fin n → ℝ}
    {v : Fin n} {i₀ j₀ : Fin (k - 1)}
    (hall : ∀ e ∈ bundlePlus v i₀ j₀, edgeSum (by omega) x e < 0) :
    intSum x v (2 * k) < 0 := by
  have hi : i₀.val < k - 1 := i₀.isLt
  let i := i₀.val + 1
  let j := j₀.val + 1
  have h0 := slot_edgeSum_neg hn hall (.univ 0) rfl
  have h1 := slot_edgeSum_neg hn hall (.univ 1) rfl
  change (intSum x v (0 + i) - intSum x v 0) + (intSum x v (0 + k + j) - intSum x v (0 + i + j)) < 0 at h0
  change (intSum x v (i + j) - intSum x v i) + (intSum x v (i + k + (k - i)) - intSum x v (i + j + (k - i))) < 0 at h1
  simp only [zero_add, intSum_zero] at h0
  rw [show k + j = i + j + (k - i) by omega] at h0
  rw [show i + k + (k - i) = 2 * k by omega] at h1
  linarith

/-- Lemma 3.1(iii): `intSum x v (4 * k) < 0` whenever `bundlePlus v i₀ j₀` is all-negative. -/
lemma intSum_fourK_neg {n k : ℕ} [NeZero n] (hn : 5 * k ≤ n) {x : Fin n → ℝ}
    {v : Fin n} {i₀ j₀ : Fin (k - 1)}
    (hall : ∀ e ∈ bundlePlus v i₀ j₀, edgeSum (by omega) x e < 0) :
    intSum x v (4 * k) < 0 := by
  have hi : i₀.val < k - 1 := i₀.isLt
  let i := i₀.val + 1
  let j := j₀.val + 1
  have h2k := intSum_twoK_neg hn hall
  have h2 := slot_edgeSum_neg hn hall (.univ 2) rfl
  have h3 := slot_edgeSum_neg hn hall (.univ 3) rfl
  change (intSum x v (2 * k + i) - intSum x v (2 * k)) +
    (intSum x v (2 * k + k + j) - intSum x v (2 * k + i + j)) < 0 at h2
  change (intSum x v (2 * k + i + j) - intSum x v (2 * k + i)) +
    (intSum x v (2 * k + i + k + (k - i)) - intSum x v (2 * k + i + j + (k - i))) < 0 at h3
  rw [show 2 * k + k + j = 3 * k + j by omega] at h2
  rw [show 2 * k + i + k + (k - i) = 4 * k by omega,
      show 2 * k + i + j + (k - i) = 3 * k + j by omega] at h3
  linarith

/-- Lemma 3.1(ii): `intSum x v (3 * k) < 0` for interior `(i₀, j₀)`. -/
lemma intSum_threeK_neg {n k : ℕ} [NeZero n] (hn : 5 * k ≤ n) {x : Fin n → ℝ}
    {v : Fin n} {i₀ j₀ : Fin (k - 1)} (hint : isInterior k i₀ j₀)
    (hall : ∀ e ∈ bundlePlus v i₀ j₀, edgeSum (by omega) x e < 0) :
    intSum x v (3 * k) < 0 := by
  have hi : i₀.val < k - 1 := i₀.isLt
  have hj : j₀.val < k - 1 := j₀.isLt
  let i := i₀.val + 1
  let j := j₀.val + 1
  rcases lt_trichotomy (i + j) k with hlt | heq | hgt
  · have hi2 : 2 ≤ i := hint.2 hlt
    let odd := decide (i % 2 = 1)
    have hc : (i + j < k ∧ 2 ≤ i ∧ i % 2 = (if odd then 1 else 0)) := by
      refine ⟨hlt, hi2, ?_⟩
      dsimp only [odd]
      by_cases hpar : i % 2 = 1
      · simp [hpar]
      · simp [hpar]; omega
    have h0 := slot_edgeSum_neg hn hall (.ltPar odd 0) (by simp [slotSpec, i, j, hc])
    have h1 := slot_edgeSum_neg hn hall (.ltPar odd 1) (by simp [slotSpec, i, j, hc])
    have h2 := slot_edgeSum_neg hn hall (.ltPar odd 2) (by simp [slotSpec, i, j, hc])
    dsimp [slotSpec] at h0 h1 h2
    change (intSum x v (0 + (k - i / 2)) - intSum x v 0) +
      (intSum x v (0 + k + (i + j)) - intSum x v (0 + (k - i / 2) + (i + j))) < 0 at h0
    change (intSum x v (k - i / 2 + (i + j)) - intSum x v (k - i / 2)) +
      (intSum x v (k - i / 2 + k + 2 * (i / 2)) - intSum x v (k - i / 2 + (i + j) + 2 * (i / 2))) < 0 at h1
    change (intSum x v (k + i + j + i / 2) - intSum x v (k + i + j)) +
      (intSum x v (k + i + j + k + (k - i - j)) - intSum x v (k + i + j + i / 2 + (k - i - j))) < 0 at h2
    simp only [zero_add, intSum_zero] at h0
    rw [show k + (i + j) = k + i + j by omega] at h0
    rw [show k - i / 2 + k + 2 * (i / 2) = 2 * k + i / 2 by omega,
        show k - i / 2 + (i + j) + 2 * (i / 2) = k + i + j + i / 2 by omega] at h1
    rw [show k + i + j + k + (k - i - j) = 3 * k by omega,
        show k + i + j + i / 2 + (k - i - j) = 2 * k + i / 2 by omega] at h2
    linarith
  · exact (hint.1 heq).elim
  · by_cases hij : j ≤ i
    · have h0 := slot_edgeSum_neg hn hall (.gtGe 0) (by simp [slotSpec, i, j, hgt, hij])
      have h1 := slot_edgeSum_neg hn hall (.gtGe 1) (by simp [slotSpec, i, j, hgt, hij])
      have h2 := slot_edgeSum_neg hn hall (.gtGe 2) (by simp [slotSpec, i, j, hgt, hij])
      dsimp [slotSpec] at h0 h1 h2
      change (intSum x v (0 + i) - intSum x v 0) +
        (intSum x v (0 + k + (i + j - k)) - intSum x v (0 + i + (i + j - k))) < 0 at h0
      change (intSum x v (i + (i + j - k)) - intSum x v i) +
        (intSum x v (i + k + (2 * k - 2 * i)) - intSum x v (i + (i + j - k) + (2 * k - 2 * i))) < 0 at h1
      change (intSum x v (i + j + (k - i)) - intSum x v (i + j)) +
        (intSum x v (i + j + k + (2 * k - i - j)) - intSum x v (i + j + (k - i) + (2 * k - i - j))) < 0 at h2
      simp only [zero_add, intSum_zero] at h0
      rw [show k + (i + j - k) = i + j by omega] at h0
      rw [show i + k + (2 * k - 2 * i) = 3 * k - i by omega,
          show i + (i + j - k) + (2 * k - 2 * i) = k + j by omega] at h1
      rw [show i + j + (k - i) = k + j by omega,
          show i + j + k + (2 * k - i - j) = 3 * k by omega,
          show k + j + (2 * k - i - j) = 3 * k - i by omega] at h2
      linarith
    · have hij' : i < j := not_le.mp hij
      have h0 := slot_edgeSum_neg hn hall (.gtLt 0) (by simp [slotSpec, i, j, hgt, hij'])
      have h1 := slot_edgeSum_neg hn hall (.gtLt 1) (by simp [slotSpec, i, j, hgt, hij'])
      have h2 := slot_edgeSum_neg hn hall (.gtLt 2) (by simp [slotSpec, i, j, hgt, hij'])
      dsimp [slotSpec] at h0 h1 h2
      change (intSum x v (0 + j) - intSum x v 0) +
        (intSum x v (0 + k + (i + j - k)) - intSum x v (0 + j + (i + j - k))) < 0 at h0
      change (intSum x v (j + (i + j - k)) - intSum x v j) +
        (intSum x v (j + k + (2 * k - 2 * j)) - intSum x v (j + (i + j - k) + (2 * k - 2 * j))) < 0 at h1
      change (intSum x v (i + j + (k - j)) - intSum x v (i + j)) +
        (intSum x v (i + j + k + (2 * k - i - j)) - intSum x v (i + j + (k - j) + (2 * k - i - j))) < 0 at h2
      simp only [zero_add, intSum_zero] at h0
      rw [show k + (i + j - k) = i + j by omega] at h0
      rw [show j + k + (2 * k - 2 * j) = 3 * k - j by omega,
          show j + (i + j - k) + (2 * k - 2 * j) = k + i by omega] at h1
      rw [show i + j + (k - j) = k + i by omega,
          show i + j + k + (2 * k - i - j) = 3 * k by omega,
          show k + i + (2 * k - i - j) = 3 * k - j by omega] at h2
      linarith

/-- Lemma 3.1(iv): `intSum x (v + i) j < 0 → intSum x v (4 * k + j) < 0` for interior `(i₀, j₀)`. -/
lemma intSum_fourKPlusJ_neg {n k : ℕ} [NeZero n] (hn : 5 * k ≤ n) {x : Fin n → ℝ}
    {v : Fin n} {i₀ j₀ : Fin (k - 1)} (hint : isInterior k i₀ j₀)
    (hall : ∀ e ∈ bundlePlus v i₀ j₀, edgeSum (by omega) x e < 0)
    (hgap : intSum x (v + natToFin (i₀.val + 1)) (j₀.val + 1) < 0) :
    intSum x v (4 * k + (j₀.val + 1)) < 0 := by
  have hi : i₀.val < k - 1 := i₀.isLt
  have hj : j₀.val < k - 1 := j₀.isLt
  let i := i₀.val + 1
  let j := j₀.val + 1
  have hgap' : intSum x v (i + j) - intSum x v i < 0 := by
    rwa [← intSum_seg x v (by omega : i + j ≤ n)]
  have hu0 := slot_edgeSum_neg hn hall (.univ 0) rfl
  dsimp [slotSpec] at hu0
  change (intSum x v (0 + i) - intSum x v 0) + (intSum x v (0 + k + j) - intSum x v (0 + i + j)) < 0 at hu0
  simp only [zero_add, intSum_zero] at hu0
  have hkj : intSum x v (k + j) < 0 := by linarith
  rcases lt_trichotomy (i + j) k with hlt | heq | hgt
  · have hi2 : 2 ≤ i := hint.2 hlt
    let odd := decide (i % 2 = 1)
    have hc : (i + j < k ∧ 2 ≤ i ∧ i % 2 = (if odd then 1 else 0)) := by
      refine ⟨hlt, hi2, ?_⟩
      dsimp only [odd]
      by_cases hpar : i % 2 = 1
      · simp [hpar]
      · simp [hpar]; omega
    have h3 := slot_edgeSum_neg hn hall (.ltPar odd 3) (by simp [slotSpec, i, j, hc])
    have h4 := slot_edgeSum_neg hn hall (.ltPar odd 4) (by simp [slotSpec, i, j, hc])
    have h5 := slot_edgeSum_neg hn hall (.ltPar odd 5) (by simp [slotSpec, i, j, hc])
    dsimp [slotSpec] at h3 h4 h5
    change (intSum x v (k + j + (k - i / 2)) - intSum x v (k + j)) +
      (intSum x v (k + j + k + (i + j)) - intSum x v (k + j + (k - i / 2) + (i + j))) < 0 at h3
    change (intSum x v (2 * k + j - i / 2 + (i + j)) - intSum x v (2 * k + j - i / 2)) +
      (intSum x v (2 * k + j - i / 2 + k + 2 * (i / 2)) -
        intSum x v (2 * k + j - i / 2 + (i + j) + 2 * (i / 2))) < 0 at h4
    change (intSum x v (2 * k + i + 2 * j + i / 2) - intSum x v (2 * k + i + 2 * j)) +
      (intSum x v (2 * k + i + 2 * j + k + (k - i - j)) -
        intSum x v (2 * k + i + 2 * j + i / 2 + (k - i - j))) < 0 at h5
    rw [show k + j + (k - i / 2) = 2 * k + j - i / 2 by omega,
        show k + j + k + (i + j) = 2 * k + i + 2 * j by omega] at h3
    rw [show 2 * k + j - i / 2 + k + 2 * (i / 2) = 3 * k + j + i / 2 by omega,
        show 2 * k + j - i / 2 + (i + j) + 2 * (i / 2) = 2 * k + i + 2 * j + i / 2 by omega] at h4
    rw [show 2 * k + i + 2 * j + k + (k - i - j) = 4 * k + j by omega,
        show 2 * k + i + 2 * j + i / 2 + (k - i - j) = 3 * k + j + i / 2 by omega] at h5
    linarith
  · exact (hint.1 heq).elim
  · by_cases hij : j ≤ i
    · have h3 := slot_edgeSum_neg hn hall (.gtGe 3) (by simp [slotSpec, i, j, hgt, hij])
      have h4 := slot_edgeSum_neg hn hall (.gtGe 4) (by simp [slotSpec, i, j, hgt, hij])
      have h5 := slot_edgeSum_neg hn hall (.gtGe 5) (by simp [slotSpec, i, j, hgt, hij])
      dsimp [slotSpec] at h3 h4 h5
      change (intSum x v (k + j + i) - intSum x v (k + j)) +
        (intSum x v (k + j + k + (i + j - k)) - intSum x v (k + j + i + (i + j - k))) < 0 at h3
      change (intSum x v (k + i + j + (i + j - k)) - intSum x v (k + i + j)) +
        (intSum x v (k + i + j + k + (2 * k - 2 * i)) -
          intSum x v (k + i + j + (i + j - k) + (2 * k - 2 * i))) < 0 at h4
      change (intSum x v (k + i + 2 * j + (k - i)) - intSum x v (k + i + 2 * j)) +
        (intSum x v (k + i + 2 * j + k + (2 * k - i - j)) -
          intSum x v (k + i + 2 * j + (k - i) + (2 * k - i - j))) < 0 at h5
      rw [show k + j + i = k + i + j by omega,
          show k + j + k + (i + j - k) = k + i + 2 * j by omega] at h3
      rw [show k + i + j + k + (2 * k - 2 * i) = 4 * k + j - i by omega,
          show k + i + j + (i + j - k) + (2 * k - 2 * i) = 2 * k + 2 * j by omega] at h4
      rw [show k + i + 2 * j + (k - i) = 2 * k + 2 * j by omega,
          show k + i + 2 * j + k + (2 * k - i - j) = 4 * k + j by omega,
          show 2 * k + 2 * j + (2 * k - i - j) = 4 * k + j - i by omega] at h5
      linarith
    · have hij' : i < j := not_le.mp hij
      have h3 := slot_edgeSum_neg hn hall (.gtLt 3) (by simp [slotSpec, i, j, hgt, hij'])
      have h4 := slot_edgeSum_neg hn hall (.gtLt 4) (by simp [slotSpec, i, j, hgt, hij'])
      have h5 := slot_edgeSum_neg hn hall (.gtLt 5) (by simp [slotSpec, i, j, hgt, hij'])
      dsimp [slotSpec] at h3 h4 h5
      change (intSum x v (k + j + j) - intSum x v (k + j)) +
        (intSum x v (k + j + k + (i + j - k)) - intSum x v (k + j + j + (i + j - k))) < 0 at h3
      change (intSum x v (k + 2 * j + (i + j - k)) - intSum x v (k + 2 * j)) +
        (intSum x v (k + 2 * j + k + (2 * k - 2 * j)) -
          intSum x v (k + 2 * j + (i + j - k) + (2 * k - 2 * j))) < 0 at h4
      change (intSum x v (k + i + 2 * j + (k - j)) - intSum x v (k + i + 2 * j)) +
        (intSum x v (k + i + 2 * j + k + (2 * k - i - j)) -
          intSum x v (k + i + 2 * j + (k - j) + (2 * k - i - j))) < 0 at h5
      rw [show k + j + j = k + 2 * j by omega,
          show k + j + k + (i + j - k) = k + i + 2 * j by omega] at h3
      rw [show k + 2 * j + k + (2 * k - 2 * j) = 4 * k by omega,
          show k + 2 * j + (i + j - k) + (2 * k - 2 * j) = 2 * k + i + j by omega] at h4
      rw [show k + i + 2 * j + (k - j) = 2 * k + i + j by omega,
          show k + i + 2 * j + k + (2 * k - i - j) = 4 * k + j by omega,
          show 2 * k + i + j + (2 * k - i - j) = 4 * k by omega] at h5
      linarith

/-- Lemma 3.1(v): `0 ≤ intSum x (v + i) j → intSum x v (5 * k - j) < 0` for interior `(i₀, j₀)`. -/
lemma intSum_fiveKMinusJ_neg {n k : ℕ} [NeZero n] (hn : 5 * k ≤ n) {x : Fin n → ℝ}
    {v : Fin n} {i₀ j₀ : Fin (k - 1)} (hint : isInterior k i₀ j₀)
    (hall : ∀ e ∈ bundlePlus v i₀ j₀, edgeSum (by omega) x e < 0)
    (hgap : 0 ≤ intSum x (v + natToFin (i₀.val + 1)) (j₀.val + 1)) :
    intSum x v (5 * k - (j₀.val + 1)) < 0 := by
  have hi : i₀.val < k - 1 := i₀.isLt
  have hj : j₀.val < k - 1 := j₀.isLt
  let i := i₀.val + 1
  let j := j₀.val + 1
  have hgap' : 0 ≤ intSum x v (i + j) - intSum x v i := by
    rwa [← intSum_seg x v (by omega : i + j ≤ n)]
  rcases lt_trichotomy (i + j) k with hlt | heq | hgt
  · have hi2 : 2 ≤ i := hint.2 hlt
    let odd := decide (i % 2 = 1)
    have hc : (i + j < k ∧ 2 ≤ i ∧ i % 2 = (if odd then 1 else 0)) := by
      refine ⟨hlt, hi2, ?_⟩
      dsimp only [odd]
      by_cases hpar : i % 2 = 1
      · simp [hpar]
      · simp [hpar]; omega
    have h6 := slot_edgeSum_neg hn hall (.ltPar odd 6) (by simp [slotSpec, i, j, hc])
    have h7 := slot_edgeSum_neg hn hall (.ltPar odd 7) (by simp [slotSpec, i, j, hc])
    have h8 := slot_edgeSum_neg hn hall (.ltPar odd 8) (by simp [slotSpec, i, j, hc])
    have h9 := slot_edgeSum_neg hn hall (.ltPar odd 9) (by simp [slotSpec, i, j, hc])
    have h10 := slot_edgeSum_neg hn hall (.ltPar odd 10) (by simp [slotSpec, i, j, hc])
    dsimp [slotSpec] at h6 h7 h8 h9 h10
    change (intSum x v (0 + (i + j)) - intSum x v 0) +
      (intSum x v (0 + k + i / 2) - intSum x v (0 + (i + j) + i / 2)) < 0 at h6
    change (intSum x v (i + (j + i / 2)) - intSum x v i) +
      (intSum x v (i + k + (k - i - j)) - intSum x v (i + (j + i / 2) + (k - i - j))) < 0 at h7
    change (intSum x v (2 * k - j + (k - i / 2)) - intSum x v (2 * k - j)) +
      (intSum x v (2 * k - j + k + (i + j)) - intSum x v (2 * k - j + (k - i / 2) + (i + j))) < 0 at h8
    change (intSum x v (3 * k - j - i / 2 + (i + j)) - intSum x v (3 * k - j - i / 2)) +
      (intSum x v (3 * k - j - i / 2 + k + 2 * (i / 2)) -
        intSum x v (3 * k - j - i / 2 + (i + j) + 2 * (i / 2))) < 0 at h9
    change (intSum x v (3 * k + i + i / 2) - intSum x v (3 * k + i)) +
      (intSum x v (3 * k + i + k + (k - i - j)) -
        intSum x v (3 * k + i + i / 2 + (k - i - j))) < 0 at h10
    simp only [zero_add, intSum_zero] at h6
    rw [show i + (j + i / 2) = i + j + i / 2 by omega,
        show i + k + (k - i - j) = 2 * k - j by omega,
        show i + j + i / 2 + (k - i - j) = k + i / 2 by omega] at h7
    rw [show 2 * k - j + (k - i / 2) = 3 * k - j - i / 2 by omega,
        show 2 * k - j + k + (i + j) = 3 * k + i by omega] at h8
    rw [show 3 * k - j - i / 2 + k + 2 * (i / 2) = 4 * k - j + i / 2 by omega,
        show 3 * k - j - i / 2 + (i + j) + 2 * (i / 2) = 3 * k + i + i / 2 by omega] at h9
    rw [show 3 * k + i + k + (k - i - j) = 5 * k - j by omega,
        show 3 * k + i + i / 2 + (k - i - j) = 4 * k - j + i / 2 by omega] at h10
    linarith
  · exact (hint.1 heq).elim
  · have h2k := intSum_twoK_neg hn hall
    have he0 := slot_edgeSum_neg hn hall (.gtExtra 0) (by simp [slotSpec, i, j, hgt])
    have he1 := slot_edgeSum_neg hn hall (.gtExtra 1) (by simp [slotSpec, i, j, hgt])
    have he2 := slot_edgeSum_neg hn hall (.gtExtra 2) (by simp [slotSpec, i, j, hgt])
    dsimp [slotSpec] at he0 he1 he2
    change (intSum x v (i + j) - intSum x v i) +
      (intSum x v (i + k + (2 * k - i - j)) - intSum x v (i + j + (2 * k - i - j))) < 0 at he0
    change (intSum x v (3 * k - j + i) - intSum x v (3 * k - j)) +
      (intSum x v (3 * k - j + k + j) - intSum x v (3 * k - j + i + j)) < 0 at he1
    change (intSum x v (3 * k - j + i + j) - intSum x v (3 * k - j + i)) +
      (intSum x v (3 * k - j + i + k + (k - i)) - intSum x v (3 * k - j + i + j + (k - i))) < 0 at he2
    rw [show i + k + (2 * k - i - j) = 3 * k - j by omega,
        show i + j + (2 * k - i - j) = 2 * k by omega] at he0
    rw [show 3 * k - j + k + j = 4 * k by omega,
        show 3 * k - j + i + j = 3 * k + i by omega] at he1
    rw [show 3 * k - j + i + j = 3 * k + i by omega,
        show 3 * k - j + i + k + (k - i) = 5 * k - j by omega,
        show 3 * k + i + (k - i) = 4 * k by omega] at he2
    linarith

end PokrovskiyHypergraph

namespace PokrovskiyAddComb
open Finset
open scoped Pointwise Combinatorics.Additive

/- Basic representation counts and Dyson e-transform -/

def repCount {G : Type*} [AddCommGroup G] [DecidableEq G] (A B : Finset G) (z : G) : ℕ :=
  #{ab ∈ A ×ˢ B | ab.1 + ab.2 = z}

lemma repCount_eq_card_filter_left {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B : Finset G) (z : G) :
    repCount A B z = #{a ∈ A | z - a ∈ B} := by
  unfold repCount
  refine card_nbij' (fun ab => ab.1) (fun a => (a, z - a)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ h
    simp only [mem_coe, mem_filter, mem_product] at h ⊢
    exact ⟨h.1.1, by convert h.1.2 using 1; rw [← h.2]; abel_nf⟩
  · intro a h
    simp only [mem_coe, mem_filter, mem_product] at h ⊢
    exact ⟨⟨h.1, h.2⟩, by abel_nf⟩
  · rintro ⟨a, b⟩ h
    simp only [mem_coe, mem_filter, mem_product] at h
    ext <;> [rfl; (rw [← h.2]; abel_nf)]
  · intro a _; rfl

lemma repCount_le_card_right {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B : Finset G) (z : G) :
    repCount A B z ≤ #B := by
  simpa [repCount, card_add_eq] using addConvolution_le_card_right (A := A) (B := B) (x := z)

lemma sum_repCount {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A B : Finset G) :
    ∑ z : G, repCount A B z = #A * #B := by
  unfold repCount
  rw [← card_product, card_eq_sum_card_fiberwise (f := fun ab : G × G => ab.1 + ab.2)
    (t := univ) (fun _ _ => mem_univ _)]

def dysonA {G : Type*} [AddCommGroup G] [DecidableEq G] (e : G) (A B : Finset G) : Finset G :=
  A ∪ (e +ᵥ B)

def dysonB {G : Type*} [AddCommGroup G] [DecidableEq G] (e : G) (A B : Finset G) : Finset G :=
  B ∩ ((-e) +ᵥ A)

lemma dyson_card_sum {G : Type*} [AddCommGroup G] [DecidableEq G] (e : G) (A B : Finset G) :
    #(dysonA e A B) + #(dysonB e A B) = #A + #B := by
  simpa [dysonA, dysonB] using addDysonETransform.card e (A, B)

lemma dyson_repCount_le {G : Type*} [AddCommGroup G] [DecidableEq G]
    (e : G) (A B : Finset G) (z : G) :
    repCount (dysonA e A B) (dysonB e A B) z ≤ repCount A B z := by
  rw [repCount_eq_card_filter_left, repCount_eq_card_filter_left]
  let S := {a ∈ A | z - a ∈ B}
  let S' := {a ∈ dysonA e A B | z - a ∈ dysonB e A B}
  let f : G → G := fun a => if a ∈ A then a else z + e - a
  refine card_le_card_of_injOn f (s := S') (t := S) ?_ ?_
  · intro a ha
    rw [mem_coe] at ha ⊢
    simp only [S', dysonA, dysonB, mem_filter, mem_union, mem_inter, mem_vadd_finset,
      vadd_eq_add] at ha
    rcases ha with ⟨ha1, hb1, a', ha', heq⟩
    by_cases hA : a ∈ A
    · change (if a ∈ A then a else z + e - a) ∈ S
      rw [if_pos hA]
      exact mem_filter.mpr ⟨hA, hb1⟩
    · change (if a ∈ A then a else z + e - a) ∈ S
      rw [if_neg hA]
      rcases ha1.resolve_left hA with ⟨b, hb, rfl⟩
      have ha'_eq : z + e - (e + b) = a' := by
        calc z + e - (e + b) = (z - (e + b)) + e := by abel_nf
        _ = (-e + a') + e := by rw [← heq]
        _ = a' := by abel_nf
      refine mem_filter.mpr ⟨ha'_eq ▸ ha', ?_⟩
      convert hb using 1
      abel_nf
  · intro a₁ ha₁ a₂ ha₂ hfeq
    rw [mem_coe] at ha₁ ha₂
    simp only [S', dysonA, dysonB, mem_filter, mem_union, mem_inter, mem_vadd_finset,
      vadd_eq_add] at ha₁ ha₂
    by_cases h1 : a₁ ∈ A <;> by_cases h2 : a₂ ∈ A
    · simp only [f, h1, h2, ↓reduceIte] at hfeq
      exact hfeq
    · simp only [f, h1, h2, ↓reduceIte] at hfeq
      rcases ha₁.2.2 with ⟨a''', ha''', heq1⟩
      have ha2_eq : a₂ = a''' := by
        have : -e + a''' = z - (z + e - a₂) := by rw [← hfeq, heq1]
        calc a₂ = e + (z - (z + e - a₂)) := by abel_nf
        _ = e + (-e + a''') := by rw [← this]
        _ = a''' := by abel_nf
      exact (h2 (ha2_eq ▸ ha''')).elim
    · simp only [f, h1, h2, ↓reduceIte] at hfeq
      rcases ha₂.2.2 with ⟨a''', ha''', heq2⟩
      have ha1_eq : a₁ = a''' := by
        have : -e + a''' = z - (z + e - a₁) := by rw [hfeq, heq2]
        calc a₁ = e + (z - (z + e - a₁)) := by abel_nf
        _ = e + (-e + a''') := by rw [← this]
        _ = a''' := by abel_nf
      exact (h1 (ha1_eq ▸ ha''')).elim
    · simp only [f, h1, h2, ↓reduceIte] at hfeq
      calc a₁ = z + e - (z + e - a₁) := by abel_nf
      _ = z + e - (z + e - a₂) := by rw [hfeq]
      _ = a₂ := by abel_nf

lemma exists_dyson_minimal {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A₀ B₀ : Finset G) (t : ℕ) (ht : t ≤ #B₀) :
    ∃ A B : Finset G,
      A₀ ⊆ A ∧
      #A + #B = #A₀ + #B₀ ∧
      t ≤ #B ∧
      (∀ z : G, repCount A B z ≤ repCount A₀ B₀ z) ∧
      (∀ e : G, #(dysonB e A B) < #B → #(dysonB e A B) < t) := by
  suffices ∀ m : ℕ, ∀ A₀ B₀ : Finset G, #B₀ = m → t ≤ #B₀ →
      ∃ A B : Finset G,
        A₀ ⊆ A ∧
        #A + #B = #A₀ + #B₀ ∧
        t ≤ #B ∧
        (∀ z : G, repCount A B z ≤ repCount A₀ B₀ z) ∧
        (∀ e : G, #(dysonB e A B) < #B → #(dysonB e A B) < t) by
    exact this #B₀ A₀ B₀ rfl ht
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro A₀ B₀ hm ht
    by_cases hex : ∃ e : G, t ≤ #(dysonB e A₀ B₀) ∧ #(dysonB e A₀ B₀) < #B₀
    · rcases hex with ⟨e, hge, hlt⟩
      rw [hm] at hlt
      obtain ⟨A, B, hsub, hsum, hBt, hrep, hmin⟩ :=
        ih #(dysonB e A₀ B₀) hlt (dysonA e A₀ B₀) (dysonB e A₀ B₀) rfl hge
      refine ⟨A, B, subset_union_left.trans hsub, ?_, hBt, ?_, hmin⟩
      · rw [hsum, dyson_card_sum]
      · intro z; exact (hrep z).trans (dyson_repCount_le e A₀ B₀ z)
    · refine ⟨A₀, B₀, Subset.rfl, rfl, ht, fun _ => le_rfl, ?_⟩
      intro e hlt
      by_contra hnot
      exact hex ⟨e, le_of_not_gt hnot, hlt⟩

private lemma mem_neg_of_neg_mem {G : Type*} [AddCommGroup G] [DecidableEq G] {A : Finset G} {x : G}
    (h : -x ∈ A) : x ∈ -A :=
  mem_neg.mpr ⟨-x, h, neg_neg x⟩

private lemma neg_mem_of_mem_neg {G : Type*} [AddCommGroup G] [DecidableEq G] {A : Finset G} {x : G}
    (h : x ∈ -A) : -x ∈ A := by
  rcases mem_neg.mp h with ⟨y, hy, rfl⟩
  simpa using hy

lemma addEnergy_eq_sum_dysonB_sq {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A B : Finset G) :
    E[A, B] = ∑ e : G, #(dysonB e A B) ^ 2 := by
  have hswap : E[A, B] = E[A, -B] := by
    unfold addEnergy
    refine card_nbij' (fun x => (x.1, (-x.2.2, -x.2.1)))
      (fun y => (y.1, (-y.2.2, -y.2.1))) ?_ ?_ ?_ ?_
    · rintro ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ h
      simp only [mem_coe, mem_filter, mem_product] at h ⊢
      refine ⟨⟨h.1.1, ⟨mem_neg_of_neg_mem (by simpa using h.1.2.2),
        mem_neg_of_neg_mem (by simpa using h.1.2.1)⟩⟩, ?_⟩
      calc a₁ + -b₂ = a₁ + b₁ - b₁ - b₂ := by abel_nf
      _ = a₂ + b₂ - b₁ - b₂ := by rw [h.2]
      _ = a₂ + -b₁ := by abel_nf
    · rintro ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ h
      simp only [mem_coe, mem_filter, mem_product] at h ⊢
      refine ⟨⟨h.1.1, ⟨neg_mem_of_mem_neg h.1.2.2, neg_mem_of_mem_neg h.1.2.1⟩⟩, ?_⟩
      calc a₁ + -b₂ = a₁ + b₁ - b₁ - b₂ := by abel_nf
      _ = a₂ + b₂ - b₁ - b₂ := by rw [h.2]
      _ = a₂ + -b₁ := by abel_nf
    · rintro ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ _; simp
    · rintro ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ _; simp
  rw [hswap, addEnergy_eq_sum_sq]
  refine Fintype.sum_congr _ _ fun e => ?_
  congr 1
  unfold dysonB
  refine card_nbij' (fun ab => -ab.2) (fun b => (e + b, -b)) ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_inter, mem_vadd_finset, vadd_eq_add] at h ⊢
    refine ⟨neg_mem_of_mem_neg h.1.2, ⟨a, h.1.1, ?_⟩⟩
    rw [← h.2]; abel_nf
  · intro b h
    simp only [mem_coe, mem_inter, mem_vadd_finset, vadd_eq_add, mem_filter, mem_product] at h ⊢
    rcases h with ⟨hb, a, ha, heq⟩
    have ha_eq : e + b = a := by rw [← heq]; abel_nf
    exact ⟨⟨ha_eq ▸ ha, mem_neg_of_neg_mem (by simpa using hb)⟩, by abel_nf⟩
  · rintro ⟨a, b⟩ h
    simp only [mem_coe, mem_filter, mem_product] at h
    ext
    · dsimp; rw [← h.2]; abel_nf
    · simp
  · intro b _; simp

lemma sum_dysonB_card {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A B : Finset G) :
    ∑ e : G, #(dysonB e A B) = #A * #B := by
  unfold dysonB
  have h1 : ∀ e : G, #(B ∩ ((-e) +ᵥ A)) = #{ab ∈ A ×ˢ B | ab.1 - ab.2 = e} := by
    intro e
    refine card_nbij' (fun b => (e + b, b)) (fun ab => ab.2) ?_ ?_ ?_ ?_
    · intro b h
      simp only [mem_coe, mem_inter, mem_vadd_finset, vadd_eq_add, mem_filter, mem_product] at h ⊢
      rcases h with ⟨hb, a, ha, heq⟩
      have : e + b = a := by rw [← heq]; abel_nf
      exact ⟨⟨this ▸ ha, hb⟩, by abel_nf⟩
    · rintro ⟨a, b⟩ h
      simp only [mem_coe, mem_filter, mem_product, mem_inter, mem_vadd_finset, vadd_eq_add] at h ⊢
      exact ⟨h.1.2, a, h.1.1, by rw [← h.2]; abel_nf⟩
    · intro b _; rfl
    · rintro ⟨a, b⟩ h
      simp only [mem_coe, mem_filter, mem_product] at h
      ext <;> [ (rw [← h.2]; abel_nf); rfl ]
  simp_rw [h1]
  rw [← card_product, card_eq_sum_card_fiberwise (f := fun ab : G × G => ab.1 - ab.2)
    (t := univ) (fun _ _ => mem_univ _)]

/- Asymmetric small-doubling subgroup closure on finsets -/

lemma card_inter_vadd_of_subset_sum {G : Type*} [AddCommGroup G] [DecidableEq G]
    (T' B' U' : Finset G) (hTU : T' + B' ⊆ U') {b₁ b₂ : G} (hb₁ : b₁ ∈ B') (hb₂ : b₂ ∈ B') :
    2 * #T' ≤ #(T' ∩ ((b₁ - b₂) +ᵥ T')) + #U' := by
  have hsub1 : (b₁ +ᵥ T') ⊆ U' := by
    intro x hx
    rw [mem_vadd_finset] at hx
    rcases hx with ⟨t, ht, rfl⟩
    exact hTU (by simpa [add_comm] using add_mem_add ht hb₁)
  have hsub2 : (b₂ +ᵥ T') ⊆ U' := by
    intro x hx
    rw [mem_vadd_finset] at hx
    rcases hx with ⟨t, ht, rfl⟩
    exact hTU (by simpa [add_comm] using add_mem_add ht hb₂)
  have hunion : #((b₁ +ᵥ T') ∪ (b₂ +ᵥ T')) ≤ #U' :=
    card_le_card (union_subset hsub1 hsub2)
  have hinter : #((b₁ +ᵥ T') ∩ (b₂ +ᵥ T')) = #(T' ∩ ((b₁ - b₂) +ᵥ T')) := by
    rw [← card_vadd_finset (-b₂) ((b₁ +ᵥ T') ∩ (b₂ +ᵥ T')), vadd_finset_inter,
      neg_vadd_vadd, inter_comm]
    have hv : (-b₂) +ᵥ (b₁ +ᵥ T') = (b₁ - b₂) +ᵥ T' := by
      rw [vadd_vadd]
      have : -b₂ + b₁ = b₁ - b₂ := by abel_nf
      rw [this]
    rw [hv]
  have hsum := card_inter_add_card_union (b₁ +ᵥ T') (b₂ +ᵥ T')
  rw [card_vadd_finset, card_vadd_finset, hinter] at hsum
  omega

lemma diff_finset_closed {G : Type*} [AddCommGroup G] [DecidableEq G]
    (T' B' : Finset G) (hB0 : (0 : G) ∈ B')
    (hTB : 2 * #(T' + B') < 3 * #T') (hBT : 2 * #(T' + B') < 3 * #B') :
    let H := B' - B'
    (0 : G) ∈ H ∧ (∀ x ∈ H, -x ∈ H) ∧ (∀ x ∈ H, ∀ y ∈ H, x + y ∈ H) ∧
      (∀ h ∈ H, 2 * #T' ≤ #(T' ∩ (h +ᵥ T')) + #(T' + B')) := by
  intro H
  have h0 : (0 : G) ∈ H := mem_sub.mpr ⟨0, hB0, 0, hB0, sub_self 0⟩
  have hneg : ∀ x ∈ H, -x ∈ H := by
    intro x hx
    rcases mem_sub.mp hx with ⟨b₁, hb₁, b₂, hb₂, rfl⟩
    exact mem_sub.mpr ⟨b₂, hb₂, b₁, hb₁, by abel_nf⟩
  have hinter : ∀ h ∈ H, 2 * #T' ≤ #(T' ∩ (h +ᵥ T')) + #(T' + B') := by
    intro h hh
    rcases mem_sub.mp hh with ⟨b₁, hb₁, b₂, hb₂, rfl⟩
    exact card_inter_vadd_of_subset_sum T' B' (T' + B') Subset.rfl hb₁ hb₂
  have hadd : ∀ x ∈ H, ∀ y ∈ H, x + y ∈ H := by
    intro x hx y hy
    have h1 := hinter x hx
    have h2 := hinter (-y) (hneg y hy)
    let X₁ := T' ∩ (x +ᵥ T')
    let X₂ := T' ∩ ((-y) +ᵥ T')
    have hXsub : X₁ ∪ X₂ ⊆ T' := union_subset inter_subset_left inter_subset_left
    have hXcard : 0 < #(X₁ ∩ X₂) := by
      have := card_inter_add_card_union X₁ X₂
      have := card_le_card hXsub
      change 2 * #T' ≤ #X₁ + #(T' + B') at h1
      change 2 * #T' ≤ #X₂ + #(T' + B') at h2
      omega
    obtain ⟨t₀, ht₀⟩ := card_pos.mp hXcard
    simp only [X₁, X₂, mem_inter, mem_vadd_finset, vadd_eq_add] at ht₀
    rcases ht₀ with ⟨⟨_, t₁, ht₁, heq₁⟩, ⟨_, t₂, ht₂, heq₂⟩⟩
    have h3 := card_inter_vadd_of_subset_sum B' T' (T' + B')
      (by rw [add_comm]) ht₂ ht₁
    have hposB : 0 < #(B' ∩ ((t₂ - t₁) +ᵥ B')) := by omega
    obtain ⟨b₅, hb₅⟩ := card_pos.mp hposB
    simp only [mem_inter, mem_vadd_finset, vadd_eq_add] at hb₅
    rcases hb₅ with ⟨hb₅, b₆, hb₆, heq₃⟩
    refine mem_sub.mpr ⟨b₅, hb₅, b₆, hb₆, ?_⟩
    have ht_eq : t₂ - t₁ = x + y := by
      have : x + t₁ = -y + t₂ := heq₁.trans heq₂.symm
      calc t₂ - t₁ = (-y + t₂) - (x + t₁) + (x + y) := by abel_nf
      _ = (x + t₁) - (x + t₁) + (x + y) := by rw [← this]
      _ = x + y := by abel_nf
    calc b₅ - b₆ = t₂ - t₁ := by rw [← heq₃]; abel_nf
    _ = x + y := ht_eq
  exact ⟨h0, hneg, hadd, hinter⟩

lemma sum_inter_vadd_le_sq {G : Type*} [AddCommGroup G] [DecidableEq G]
    (T' H : Finset G) :
    ∑ h ∈ H, #(T' ∩ (h +ᵥ T')) ≤ #T' ^ 2 := by
  have h1 : ∀ h : G, #(T' ∩ (h +ᵥ T')) = #{ab ∈ T' ×ˢ T' | ab.1 - ab.2 = h} := by
    intro h
    refine card_nbij' (fun x => (x, x - h)) (fun ab => ab.1) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [mem_coe, mem_inter, mem_vadd_finset, vadd_eq_add, mem_filter, mem_product] at hx ⊢
      rcases hx with ⟨hxT, t, ht, rfl⟩
      exact ⟨⟨hxT, by convert ht using 1; abel_nf⟩, by abel_nf⟩
    · rintro ⟨a, b⟩ hab
      simp only [mem_coe, mem_filter, mem_product, mem_inter, mem_vadd_finset, vadd_eq_add] at hab ⊢
      exact ⟨hab.1.1, b, hab.1.2, by rw [← hab.2]; abel_nf⟩
    · intro x _; rfl
    · rintro ⟨a, b⟩ hab
      simp only [mem_coe, mem_filter, mem_product] at hab
      ext <;> [rfl; (rw [← hab.2]; abel_nf)]
  simp_rw [h1]
  rw [sq, ← card_product, ← card_biUnion]
  · refine card_le_card fun ab hab => ?_
    rw [mem_biUnion] at hab
    rcases hab with ⟨_, _, hmem⟩
    exact (mem_filter.mp hmem).1
  · intro h₁ _ h₂ _ hne
    exact disjoint_left.mpr fun ab hab1 hab2 =>
      hne ((mem_filter.mp hab1).2.symm.trans (mem_filter.mp hab2).2)

/- Antisymmetric cardinality helpers in `ZMod k` -/

lemma card_ge_half_of_antisymm {k : ℕ} [NeZero k] {A : Finset (ZMod k)}
    (hA : ∀ x : ZMod k, x ∈ A ∨ -x ∈ A) :
    k ≤ 2 * #A := by
  have huniv : (univ : Finset (ZMod k)) = A ∪ (-A) := by
    ext x
    simp only [mem_univ, mem_union, true_iff]
    exact (hA x).imp id mem_neg_of_neg_mem
  have h1 : k = #(A ∪ (-A)) := by
    rw [← huniv, card_univ, ZMod.card]
  have h2 := card_union_le A (-A)
  rw [card_neg] at h2
  omega

lemma card_inter_coset_ge_quarter {k : ℕ} [NeZero k] {A C₂ : Finset (ZMod k)}
    (hA : ∀ x : ZMod k, x ∈ A ∨ -x ∈ A)
    (hC₂_card : 2 * #C₂ = k)
    (hC₂_neg : ∀ x ∈ C₂, -x ∈ C₂) :
    k ≤ 4 * #(A ∩ C₂) := by
  have hcov : C₂ ⊆ (A ∩ C₂) ∪ ((-A) ∩ C₂) := by
    intro x hx
    simp only [mem_union, mem_inter]
    rcases hA x with h | h
    · exact Or.inl ⟨h, hx⟩
    · exact Or.inr ⟨mem_neg_of_neg_mem h, hx⟩
  have hcard_neg : #((-A) ∩ C₂) = #(A ∩ C₂) := by
    refine card_nbij' (fun x => -x) (fun x => -x) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [mem_coe, mem_inter] at hx ⊢
      exact ⟨neg_mem_of_mem_neg hx.1, hC₂_neg x hx.2⟩
    · intro x hx
      simp only [mem_coe, mem_inter] at hx ⊢
      exact ⟨mem_neg_of_neg_mem (by simpa using hx.1), hC₂_neg x hx.2⟩
    · intro x _; simp
    · intro x _; simp
  have hle := (card_le_card hcov).trans (card_union_le _ _)
  rw [hcard_neg] at hle
  omega

/-- Main restricted sumset growth lemma (Claim 5.8 of Pokrovskiy), completely self-contained. -/
theorem sumset_growth_zmod {k : ℕ} [NeZero k] (hk : 200000 < k)
    (A₀ B₀ : Finset (ZMod k))
    (hA₀ : ∀ x : ZMod k, x ∈ A₀ ∨ -x ∈ A₀)
    (hB₀ : ∀ x : ZMod k, x ∈ B₀ ∨ -x ∈ B₀)
    (S : Finset (ZMod k × ZMod k))
    (hS : S ⊆ A₀ ×ˢ B₀)
    (b3 : ℕ) (hb3_ub : 400 * b3 ≤ k) (hb3_lb : k ≤ 400 * (b3 + 1))
    (hS_loss : #(A₀ ×ˢ B₀) - #S ≤ b3 ^ 2) :
    508 * k ≤ 1000 * #(S.image (fun p => p.1 + p.2)) := by
  have hA₀_card : k ≤ 2 * #A₀ := card_ge_half_of_antisymm hA₀
  have hB₀_card : k ≤ 2 * #B₀ := card_ge_half_of_antisymm hB₀
  let t : ℕ := 12 * b3
  have ht_ub : 100 * t ≤ 3 * k := by omega
  have ht_lb : 299 * k ≤ 10000 * t := by omega
  have ht_le_B₀ : t ≤ #B₀ := by omega
  obtain ⟨A, B, hA_sub, hAB_sum, htB, hrep_le, hmin⟩ :=
    exists_dyson_minimal A₀ B₀ t ht_le_B₀
  have hA_anti : ∀ x : ZMod k, x ∈ A ∨ -x ∈ A := by
    intro x
    exact (hA₀ x).imp (fun h => hA_sub h) (fun h => hA_sub h)
  have hA_half : k ≤ 2 * #A := card_ge_half_of_antisymm hA_anti
  have hA_le_k : #A ≤ k := by simpa [ZMod.card] using card_le_univ A
  have hB_le_k : #B ≤ k := by simpa [ZMod.card] using card_le_univ B
  have hAB_ge_k : k ≤ #A + #B := by linarith only [hA₀_card, hB₀_card, hAB_sum]
  let P : Finset (ZMod k) := univ.filter (fun z => b3 + 1 ≤ repCount A B z)
  have hP_large : 511 * k ≤ 1000 * #P := by
    have hsum_compl : ∑ z ∈ univ \ P, repCount A B z ≤ k * b3 := by
      calc ∑ z ∈ univ \ P, repCount A B z
        _ ≤ ∑ _z ∈ univ \ P, b3 := by
          refine sum_le_sum fun z hz => ?_
          simp only [P, mem_sdiff, mem_univ, mem_filter, true_and] at hz
          omega
        _ = #(univ \ P) * b3 := by simp
        _ ≤ k * b3 := by
          refine Nat.mul_le_mul_right b3 ?_
          simpa [ZMod.card] using card_le_univ (univ \ P)
    have hsum_split : ∑ z ∈ P, repCount A B z + ∑ z ∈ univ \ P, repCount A B z = #A * #B := by
      rw [add_comm, sum_sdiff (subset_univ P), sum_repCount]
    by_cases hCase1 : 595 * k ≤ 1000 * #A
    · have hP_upper : ∑ z ∈ P, repCount A B z ≤ #P * #B := by
        calc ∑ z ∈ P, repCount A B z
          _ ≤ ∑ _z ∈ P, #B := sum_le_sum fun z _ => repCount_le_card_right A B z
          _ = #P * #B := by simp
      have hineq : #A * #B ≤ #P * #B + k * b3 := by linarith only [hsum_split, hsum_compl, hP_upper]
      have hBt_num : 299 * k ≤ 10000 * #B := by linarith only [ht_lb, htB]
      have hkB_pos : 0 < #B := by linarith only [hBt_num, hk]
      have hstep : 595 * 299 * (k * #B) ≤ 299000 * (#P * #B) + 25000 * (k * #B) := by
        have h1 : 595 * (k * #B) ≤ 1000 * (#A * #B) := by
          calc 595 * (k * #B) = (595 * k) * #B := by ring
            _ ≤ (1000 * #A) * #B := Nat.mul_le_mul_right #B hCase1
            _ = 1000 * (#A * #B) := by ring
        have h2 : 400 * (k * b3) ≤ k * k := by
          calc 400 * (k * b3) = k * (400 * b3) := by ring
            _ ≤ k * k := Nat.mul_le_mul_left k hb3_ub
        have h3 : 299 * (k * k) ≤ 10000 * (k * #B) := by
          calc 299 * (k * k) = k * (299 * k) := by ring
            _ ≤ k * (10000 * #B) := Nat.mul_le_mul_left k hBt_num
            _ = 10000 * (k * #B) := by ring
        linarith only [hineq, h1, h2, h3]
      have hstep' : (595 * 299 - 25000) * k * #B ≤ 299000 * #P * #B := by
        have h4 : 152905 * (k * #B) ≤ 299000 * (#P * #B) := by linarith only [hstep]
        calc (595 * 299 - 25000) * k * #B = 152905 * (k * #B) := by ring
          _ ≤ 299000 * (#P * #B) := h4
          _ = 299000 * #P * #B := by ring
      have hcancel : (595 * 299 - 25000) * k ≤ 299000 * #P :=
        Nat.le_of_mul_le_mul_right hstep' hkB_pos
      linarith only [hcancel]
    · have hA_lt : 1000 * #A < 595 * k := not_le.mp hCase1
      have hB_gt : 405 * k < 1000 * #B := by linarith only [hAB_ge_k, hA_lt]
      let T : Finset (ZMod k) := univ.filter (fun e => #(dysonB e A B) = #B)
      by_cases hCase2 : 1000 * #T ≤ 420 * k
      · have hdyson_le : ∀ e : ZMod k, #(dysonB e A B) ≤ #B := by
          intro e; unfold dysonB; exact card_le_card inter_subset_left
        have hdyson_notT : ∀ e ∈ univ \ T, #(dysonB e A B) ≤ t := by
          intro e he
          simp only [T, mem_sdiff, mem_univ, mem_filter, true_and] at he
          exact le_of_lt (hmin e (lt_of_le_of_ne (hdyson_le e) he))
        have hE_bound : E[A, B] ≤ #T * #B ^ 2 + t * (#A * #B) := by
          rw [addEnergy_eq_sum_dysonB_sq]
          have hsplitE : ∑ e : ZMod k, #(dysonB e A B) ^ 2 =
              ∑ e ∈ T, #(dysonB e A B) ^ 2 + ∑ e ∈ univ \ T, #(dysonB e A B) ^ 2 := by
            rw [add_comm, sum_sdiff (subset_univ T)]
          rw [hsplitE]
          have hET : ∑ e ∈ T, #(dysonB e A B) ^ 2 = #T * #B ^ 2 := by
            have hcongr : ∀ e ∈ T, #(dysonB e A B) ^ 2 = #B ^ 2 := by
              intro e he; simp only [T, mem_filter, mem_univ, true_and] at he; rw [he]
            rw [sum_congr rfl hcongr, sum_const, smul_eq_mul]
          have hEnotT : ∑ e ∈ univ \ T, #(dysonB e A B) ^ 2 ≤ t * (#A * #B) := by
            calc ∑ e ∈ univ \ T, #(dysonB e A B) ^ 2
              _ ≤ ∑ e ∈ univ \ T, t * #(dysonB e A B) := by
                refine sum_le_sum fun e he => ?_
                rw [sq]
                exact Nat.mul_le_mul_right _ (hdyson_notT e he)
              _ = t * ∑ e ∈ univ \ T, #(dysonB e A B) := by rw [mul_sum]
              _ ≤ t * ∑ e : ZMod k, #(dysonB e A B) :=
                Nat.mul_le_mul_left t (sum_le_sum_of_subset (subset_univ _))
              _ = t * (#A * #B) := by rw [sum_dysonB_card]
          linarith only [hET, hEnotT]
        have hCS := card_sq_le_card_mul_addEnergy A B P
        have hcardP_prod : #{ab ∈ A ×ˢ B | ab.1 + ab.2 ∈ P} = ∑ z ∈ P, repCount A B z := by
          unfold repCount
          exact (sum_card_fiberwise_eq_card_filter (A ×ˢ B) P (fun ab => ab.1 + ab.2)).symm
        rw [hcardP_prod] at hCS
        have hkb3_small : 1000 * (k * b3) ≤ 13 * (#A * #B) := by
          have h1 : 400 * (k * b3) ≤ k * k := by
            calc 400 * (k * b3) = k * (400 * b3) := by ring
              _ ≤ k * k := Nat.mul_le_mul_left k hb3_ub
          have h2 : 405 * (k * k) ≤ 2000 * (#A * #B) := by
            calc 405 * (k * k) = k * (405 * k) := by ring
              _ ≤ (2 * #A) * (1000 * #B) := Nat.mul_le_mul hA_half hB_gt.le
              _ = 2000 * (#A * #B) := by ring
          have h3 : 0 ≤ #A * #B := Nat.zero_le _
          linarith only [h1, h2, h3]
        have hP_sum_lb : 987 * (#A * #B) ≤ 1000 * ∑ z ∈ P, repCount A B z := by
          linarith only [hsum_split, hsum_compl, hkb3_small]
        have htA_bound : 40500 * (t * (#A * #B)) ≤ 1785 * (k * #B ^ 2) := by
          have h1 : 100000 * (t * #A) ≤ 1785 * (k * k) := by
            calc 100000 * (t * #A) = (100 * t) * (1000 * #A) := by ring
              _ ≤ (3 * k) * (595 * k) := Nat.mul_le_mul ht_ub hA_lt.le
              _ = 1785 * (k * k) := by ring
          have h4 := Nat.mul_le_mul_right #B h1
          have h5 := Nat.mul_le_mul_left (1785 * k * #B) hB_gt.le
          have h6 : 40500000 * (t * (#A * #B)) ≤ 1785000 * (k * #B ^ 2) := by
            calc 40500000 * (t * (#A * #B))
              _ = 405 * (100000 * (t * #A) * #B) := by ring
              _ ≤ 405 * (1785 * (k * k) * #B) := Nat.mul_le_mul_left 405 h4
              _ = 1785 * k * #B * (405 * k) := by ring
              _ ≤ 1785 * k * #B * (1000 * #B) := h5
              _ = 1785000 * (k * #B ^ 2) := by ring
          linarith only [h6]
        have hE_scaled : 40500 * E[A, B] ≤ 18805 * (k * #B ^ 2) := by
          have hT_mul := Nat.mul_le_mul_right (#B ^ 2) hCase2
          have hEb := Nat.mul_le_mul_left 40500 hE_bound
          have hT_rw : 1000 * #T * #B ^ 2 = 1000 * (#T * #B ^ 2) := by ring
          have hK_rw : 420 * k * #B ^ 2 = 420 * (k * #B ^ 2) := by ring
          rw [hT_rw, hK_rw] at hT_mul
          linarith only [hEb, hT_mul, htA_bound]
        have hCS_scaled : 974169 * (#A * #B) ^ 2 ≤ 1000000 * (#P * E[A, B]) := by
          have h1 : (987 * (#A * #B)) ^ 2 ≤ (1000 * ∑ z ∈ P, repCount A B z) ^ 2 :=
            Nat.pow_le_pow_left hP_sum_lb 2
          have h2 := Nat.mul_le_mul_left 1000000 hCS
          calc 974169 * (#A * #B) ^ 2 = (987 * (#A * #B)) ^ 2 := by ring
            _ ≤ (1000 * ∑ z ∈ P, repCount A B z) ^ 2 := h1
            _ = 1000000 * (∑ z ∈ P, repCount A B z) ^ 2 := by ring
            _ ≤ 1000000 * (#P * E[A, B]) := h2
        have hAB_sq : k ^ 2 * #B ^ 2 ≤ 4 * (#A * #B) ^ 2 := by
          have h1 : k * #B ≤ 2 * (#A * #B) := by
            have := Nat.mul_le_mul_right #B hA_half; linarith only [this]
          calc k ^ 2 * #B ^ 2 = (k * #B) ^ 2 := by ring
            _ ≤ (2 * (#A * #B)) ^ 2 := Nat.pow_le_pow_left h1 2
            _ = 4 * (#A * #B) ^ 2 := by ring
        have hB2_pos : 0 < k * #B ^ 2 := by
          have hBpos : 0 < #B := by linarith only [hB_gt, hk]
          positivity
        have hmain_ineq : 39453844500 * k * (k * #B ^ 2) ≤ 75220000000 * #P * (k * #B ^ 2) := by
          calc 39453844500 * k * (k * #B ^ 2)
            _ = 40500 * 974169 * (k ^ 2 * #B ^ 2) := by ring
            _ ≤ 40500 * 974169 * (4 * (#A * #B) ^ 2) := Nat.mul_le_mul_left _ hAB_sq
            _ = 4 * 40500 * (974169 * (#A * #B) ^ 2) := by ring
            _ ≤ 4 * 40500 * (1000000 * (#P * E[A, B])) := Nat.mul_le_mul_left _ hCS_scaled
            _ = 4000000 * #P * (40500 * E[A, B]) := by ring
            _ ≤ 4000000 * #P * (18805 * (k * #B ^ 2)) := Nat.mul_le_mul_left _ hE_scaled
            _ = 75220000000 * #P * (k * #B ^ 2) := by ring
        have hmain_cancel : 39453844500 * k ≤ 75220000000 * #P :=
          Nat.le_of_mul_le_mul_right hmain_ineq hB2_pos
        have hP0 : 0 ≤ #P := Nat.zero_le _
        linarith only [hmain_cancel, hP0]
      · exfalso
        have hT_gt : 420 * k < 1000 * #T := not_le.mp hCase2
        have hTB_sub_A : T + B ⊆ A := by
          intro x hx
          rcases mem_add.mp hx with ⟨e, he, b, hb, rfl⟩
          have he' : #(B ∩ ((-e) +ᵥ A)) = #B := (mem_filter.mp he).2
          have hBsub : B ⊆ (-e) +ᵥ A := by
            have heq := eq_of_subset_of_card_le inter_subset_left he'.ge
            rw [← heq]
            exact inter_subset_right
          have hmem := hBsub hb
          rw [mem_vadd_finset] at hmem
          rcases hmem with ⟨a, ha, heq⟩
          have : e + b = a := by simp only [vadd_eq_add] at heq; rw [← heq]; abel_nf
          exact this ▸ ha
        obtain ⟨t₀, ht₀⟩ : T.Nonempty := card_pos.mp (by linarith only [hT_gt, hk])
        obtain ⟨b₀, hb₀⟩ : B.Nonempty := card_pos.mp (by linarith only [hB_gt, hk])
        let T' : Finset (ZMod k) := (-t₀) +ᵥ T
        let B' : Finset (ZMod k) := (-b₀) +ᵥ B
        have hT'card : #T' = #T := card_vadd_finset (-t₀) T
        have hB'card : #B' = #B := card_vadd_finset (-b₀) B
        have hT'0 : (0 : ZMod k) ∈ T' :=
          mem_vadd_finset.mpr ⟨t₀, ht₀, neg_add_cancel t₀⟩
        have hB'0 : (0 : ZMod k) ∈ B' :=
          mem_vadd_finset.mpr ⟨b₀, hb₀, neg_add_cancel b₀⟩
        have hT'B'_card : #(T' + B') ≤ #A := by
          have hshift : T' + B' = (-(t₀ + b₀)) +ᵥ (T + B) := by
            ext x
            constructor
            · intro hx
              rcases mem_add.mp hx with ⟨_, ha1, _, hb1, rfl⟩
              rw [mem_vadd_finset] at ha1 hb1 ⊢
              rcases ha1 with ⟨t₁, ht₁, rfl⟩
              rcases hb1 with ⟨b₁, hb₁, rfl⟩
              refine ⟨t₁ + b₁, add_mem_add ht₁ hb₁, ?_⟩
              simp only [vadd_eq_add]; abel_nf
            · intro hx
              rw [mem_vadd_finset] at hx
              rcases hx with ⟨_, hx, rfl⟩
              rcases mem_add.mp hx with ⟨t₁, ht₁, b₁, hb₁, rfl⟩
              refine mem_add.mpr ⟨-t₀ +ᵥ t₁, mem_vadd_finset.mpr ⟨t₁, ht₁, rfl⟩,
                -b₀ +ᵥ b₁, mem_vadd_finset.mpr ⟨b₁, hb₁, rfl⟩, ?_⟩
              simp only [vadd_eq_add]; abel_nf
          rw [hshift, card_vadd_finset]
          exact card_le_card hTB_sub_A
        have h2TB_T : 2 * #(T' + B') < 3 * #T' := by linarith only [hT'B'_card, hA_lt, hT'card, hT_gt]
        have h2TB_B : 2 * #(T' + B') < 3 * #B' := by linarith only [hT'B'_card, hA_lt, hB'card, hB_gt]
        let H : Finset (ZMod k) := B' - B'
        obtain ⟨_hH0, hHneg, hHadd, hHinter⟩ :=
          diff_finset_closed T' B' hB'0 h2TB_T h2TB_B
        have hB'_sub_H : B' ⊆ H := by
          intro x hx
          exact mem_sub.mpr ⟨x, hx, 0, hB'0, sub_zero x⟩
        have hH_gt : 405 * k < 1000 * #H := by
          have := card_le_card hB'_sub_H; linarith only [this, hB'card, hB_gt]
        have hH_lt_k : #H < k := by
          have hsum_lb : #H * (2 * #T' - #(T' + B')) ≤ ∑ h ∈ H, #(T' ∩ (h +ᵥ T')) := by
            calc #H * (2 * #T' - #(T' + B'))
              _ = ∑ _h ∈ H, (2 * #T' - #(T' + B')) := by simp
              _ ≤ ∑ h ∈ H, #(T' ∩ (h +ᵥ T')) := by
                refine sum_le_sum fun h hh => ?_
                have := hHinter h hh
                omega
          have hsum_ub := sum_inter_vadd_le_sq T' H
          have hle_sq : #H * (2 * #T' - #(T' + B')) ≤ #T' ^ 2 := hsum_lb.trans hsum_ub
          have hsub_pos : #(T' + B') < 2 * #T' := by linarith only [h2TB_T]
          have hquad : #T' ^ 2 < k * (2 * #T' - #(T' + B')) := by
            have hkT : #T' ≤ k := by rw [hT'card]; simpa [ZMod.card] using card_le_univ T
            have hkTB : #(T' + B') ≤ k := hT'B'_card.trans hA_le_k
            have h1 : 1000 * (k - #T') < 580 * k := by omega
            have h2 : (1000 * (k - #T')) ^ 2 < (580 * k) ^ 2 := by
              nlinarith only [h1, hk]
            have h3 : 405 * k < 1000 * (k - #(T' + B')) := by omega
            zify [hsub_pos.le, hkT, hkTB] at h2 h3 ⊢
            nlinarith only [h2, h3, hk]
          exact Nat.lt_of_mul_lt_mul_right (hle_sq.trans_lt hquad)
        have hnot_univ : H ≠ univ := by
          intro heq
          rw [heq, card_univ, ZMod.card] at hH_lt_k
          exact lt_irrefl k hH_lt_k
        obtain ⟨g, hg⟩ : (univ \ H).Nonempty := by
          rw [sdiff_nonempty]
          intro h
          exact hnot_univ (Subset.antisymm (subset_univ H) h)
        rw [mem_sdiff] at hg
        have hgH : g ∉ H := hg.2
        have hdisj_g : Disjoint H (g +ᵥ H) := by
          rw [disjoint_left]
          intro x hx1 hx2
          rw [mem_vadd_finset] at hx2
          rcases hx2 with ⟨h, hh, heq⟩
          simp only [vadd_eq_add] at heq
          have : g = x + (-h) := by rw [← heq]; abel_nf
          exact hgH (this ▸ hHadd x hx1 (-h) (hHneg h hh))
        have huniv_eq : (univ : Finset (ZMod k)) = H ∪ (g +ᵥ H) := by
          by_contra hne
          have hne' : (univ \ (H ∪ (g +ᵥ H))).Nonempty := by
            rw [sdiff_nonempty]
            intro h
            exact hne (Subset.antisymm h (subset_univ _))
          obtain ⟨w, hw⟩ := hne'
          simp only [mem_sdiff, mem_univ, mem_union, true_and, not_or] at hw
          have hdisj_w1 : Disjoint H (w +ᵥ H) := by
            rw [disjoint_left]
            intro x hx1 hx2
            rw [mem_vadd_finset] at hx2
            rcases hx2 with ⟨h, hh, heq⟩
            simp only [vadd_eq_add] at heq
            have : w = x + (-h) := by rw [← heq]; abel_nf
            exact hw.1 (this ▸ hHadd x hx1 (-h) (hHneg h hh))
          have hdisj_w2 : Disjoint (g +ᵥ H) (w +ᵥ H) := by
            rw [disjoint_left]
            intro x hx1 hx2
            rw [mem_vadd_finset] at hx1 hx2
            rcases hx1 with ⟨h₁, hh₁, rfl⟩
            rcases hx2 with ⟨h₂, hh₂, heq⟩
            simp only [vadd_eq_add] at heq
            have hw_eq : w = g + (h₁ + (-h₂)) := by
              calc w = (w + h₂) - h₂ := by abel_nf
              _ = (g + h₁) - h₂ := by rw [heq]
              _ = g + (h₁ + (-h₂)) := by abel_nf
            exact hw.2 (mem_vadd_finset.mpr ⟨h₁ + (-h₂), hHadd h₁ hh₁ (-h₂) (hHneg h₂ hh₂), hw_eq.symm⟩)
          have h3card : 3 * #H ≤ k := by
            have hsub3 : H ∪ (g +ᵥ H) ∪ (w +ᵥ H) ⊆ univ := subset_univ _
            have hc := card_le_card hsub3
            rw [card_univ, ZMod.card, card_union_of_disjoint (disjoint_union_left.mpr ⟨hdisj_w1, hdisj_w2⟩),
              card_union_of_disjoint hdisj_g, card_vadd_finset, card_vadd_finset] at hc
            linarith only [hc]
          linarith only [h3card, hH_gt]
        have h2H_eq_k : 2 * #H = k := by
          have hc := congrArg card huniv_eq
          rw [card_univ, ZMod.card, card_union_of_disjoint hdisj_g, card_vadd_finset] at hc
          linarith only [hc]
        have hT'_sub_H : T' ⊆ H := by
          intro x hx
          have h3 := card_inter_vadd_of_subset_sum B' T' (T' + B')
            (by rw [add_comm]) hx hT'0
          have hposB : 0 < #(B' ∩ ((x - 0) +ᵥ B')) := by omega
          obtain ⟨b₅, hb₅⟩ := card_pos.mp hposB
          simp only [sub_zero, mem_inter, mem_vadd_finset, vadd_eq_add] at hb₅
          rcases hb₅ with ⟨hb₅, b₆, hb₆, heq⟩
          exact mem_sub.mpr ⟨b₅, hb₅, b₆, hb₆, by rw [← heq]; abel_nf⟩
        let C₁ : Finset (ZMod k) := (t₀ + b₀) +ᵥ H
        have hTB_sub_C₁ : T + B ⊆ C₁ := by
          intro x hx
          rcases mem_add.mp hx with ⟨t₁, ht₁, b₁, hb₁, rfl⟩
          have ht₁' : -t₀ + t₁ ∈ H := hT'_sub_H (mem_vadd_finset.mpr ⟨t₁, ht₁, rfl⟩)
          have hb₁' : -b₀ + b₁ ∈ H := hB'_sub_H (mem_vadd_finset.mpr ⟨b₁, hb₁, rfl⟩)
          exact mem_vadd_finset.mpr ⟨(-t₀ + t₁) + (-b₀ + b₁), hHadd _ ht₁' _ hb₁', by
            simp only [vadd_eq_add]; abel_nf⟩
        let C₂ : Finset (ZMod k) := univ \ C₁
        have hC₁_card : #C₁ = #H := card_vadd_finset _ H
        have hC₂_card : 2 * #C₂ = k := by
          have := card_sdiff_add_card_eq_card (subset_univ C₁)
          rw [card_univ, ZMod.card, hC₁_card] at this
          linarith only [this, h2H_eq_k]
        have htwo_mem_H : ∀ x : ZMod k, x + x ∈ H := by
          intro x
          have hx : x ∈ H ∪ (g +ᵥ H) := huniv_eq ▸ mem_univ x
          rcases mem_union.mp hx with hxH | hxgH
          · exact hHadd x hxH x hxH
          · rw [mem_vadd_finset] at hxgH
            rcases hxgH with ⟨h₁, hh₁, rfl⟩
            have hgg : g + g ∈ H := by
              have hgg_u : g + g ∈ H ∪ (g +ᵥ H) := huniv_eq ▸ mem_univ (g + g)
              rcases mem_union.mp hgg_u with h | h
              · exact h
              · rw [mem_vadd_finset] at h
                rcases h with ⟨h₂, hh₂, heq⟩
                simp only [vadd_eq_add] at heq
                have : g = h₂ := add_left_cancel heq.symm
                exact (hgH (this ▸ hh₂)).elim
            simp only [vadd_eq_add]
            have : (g + h₁) + (g + h₁) = (g + g) + (h₁ + h₁) := by abel_nf
            rw [this]
            exact hHadd _ hgg _ (hHadd h₁ hh₁ h₁ hh₁)
        have hC₂_neg : ∀ x ∈ C₂, -x ∈ C₂ := by
          intro x hx
          simp only [C₂, C₁, mem_sdiff, mem_univ, true_and, mem_vadd_finset, vadd_eq_add] at hx ⊢
          rintro ⟨h, hh, heq⟩
          apply hx
          refine ⟨h + (x + x), hHadd h hh _ (htwo_mem_H x), ?_⟩
          calc t₀ + b₀ + (h + (x + x)) = (t₀ + b₀ + h) + x + x := by abel_nf
          _ = -x + x + x := by rw [heq]
          _ = x := by abel_nf
        have hAC₂_quarter : k ≤ 4 * #(A ∩ C₂) :=
          card_inter_coset_ge_quarter hA_anti hC₂_card hC₂_neg
        obtain ⟨a, ha⟩ : (A ∩ C₂).Nonempty := card_pos.mp (by linarith only [hAC₂_quarter, hk])
        obtain ⟨_haA, haC₂⟩ := mem_inter.mp ha
        let e₀ : ZMod k := a - b₀
        have he₀_not_T : e₀ ∉ T := by
          intro he₀T
          have ha_in_TB : a ∈ T + B := mem_add.mpr ⟨e₀, he₀T, b₀, hb₀, sub_add_cancel a b₀⟩
          exact (mem_sdiff.mp haC₂).2 (hTB_sub_C₁ ha_in_TB)
        have hdyson_lt_B : #(dysonB e₀ A B) < #B := by
          have hle : #(dysonB e₀ A B) ≤ #B := card_le_card inter_subset_left
          refine lt_of_le_of_ne hle fun heq => he₀_not_T ?_
          simp only [T, mem_filter, mem_univ, true_and]
          exact heq
        have he₀B_sub_C₂ : (e₀ +ᵥ B) ⊆ C₂ := by
          intro y hy
          rw [mem_vadd_finset] at hy
          rcases hy with ⟨b₁, hb₁, rfl⟩
          simp only [C₂, C₁, mem_sdiff, mem_univ, true_and, mem_vadd_finset, vadd_eq_add]
          rintro ⟨h, hh, heq⟩
          apply (mem_sdiff.mp haC₂).2
          simp only [C₁, mem_vadd_finset, vadd_eq_add]
          have hb₁' : -b₀ + b₁ ∈ H := hB'_sub_H (mem_vadd_finset.mpr ⟨b₁, hb₁, rfl⟩)
          refine ⟨h + (-(-b₀ + b₁)), hHadd h hh _ (hHneg _ hb₁'), ?_⟩
          dsimp only [e₀] at heq
          calc t₀ + b₀ + (h + -(-b₀ + b₁)) = (t₀ + b₀ + h) - b₁ + b₀ := by abel_nf
          _ = (a - b₀ + b₁) - b₁ + b₀ := by rw [heq]
          _ = a := by abel_nf
        have hdyson_ge_t : t ≤ #(dysonB e₀ A B) := by
          have hcard_eq : #(dysonB e₀ A B) = #((e₀ +ᵥ B) ∩ A) := by
            unfold dysonB
            rw [← card_vadd_finset e₀ (B ∩ ((-e₀) +ᵥ A)), vadd_finset_inter, vadd_neg_vadd]
          rw [hcard_eq]
          have hsub_inter' : (e₀ +ᵥ B) ∩ (A ∩ C₂) ⊆ (e₀ +ᵥ B) ∩ A := by
            intro z hz
            exact mem_inter.mpr ⟨(mem_inter.mp hz).1, (mem_inter.mp (mem_inter.mp hz).2).1⟩
          have hsub_union : (e₀ +ᵥ B) ∪ (A ∩ C₂) ⊆ C₂ :=
            union_subset he₀B_sub_C₂ inter_subset_right
          have h1 := card_inter_add_card_union (e₀ +ᵥ B) (A ∩ C₂)
          rw [card_vadd_finset] at h1
          have h2 := card_le_card hsub_union
          have h3 := card_le_card hsub_inter'
          linarith only [h1, h2, h3, hB_gt, hAC₂_quarter, hC₂_card, ht_ub]
        exact (not_lt_of_ge hdyson_ge_t) (hmin e₀ hdyson_lt_B)
  let Im := S.image (fun p => p.1 + p.2)
  let R := P \ Im
  have hP_sub : P ⊆ Im ∪ R := by
    intro z hz
    by_cases h : z ∈ Im
    · exact mem_union_left _ h
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hz, h⟩)
  have hR_disj : ∀ z ∈ R, repCount A₀ B₀ z ≤ #{ab ∈ (A₀ ×ˢ B₀) \ S | ab.1 + ab.2 = z} := by
    intro z hz
    unfold repCount
    refine card_le_card fun ab hab => ?_
    simp only [mem_filter, mem_sdiff] at hab ⊢
    refine ⟨⟨hab.1, fun habS => ?_⟩, hab.2⟩
    have hzIm : z ∈ Im := mem_image.mpr ⟨ab, habS, hab.2⟩
    exact (mem_sdiff.mp hz).2 hzIm
  have hR_bound : #R * (b3 + 1) ≤ #(A₀ ×ˢ B₀) - #S := by
    calc #R * (b3 + 1)
      _ = ∑ _z ∈ R, (b3 + 1) := by simp
      _ ≤ ∑ z ∈ R, repCount A B z := by
        refine sum_le_sum fun z hz => ?_
        have hzP := (mem_sdiff.mp hz).1
        simp only [P, mem_filter, mem_univ, true_and] at hzP
        exact hzP
      _ ≤ ∑ z ∈ R, repCount A₀ B₀ z := sum_le_sum fun z _ => hrep_le z
      _ ≤ ∑ z ∈ R, #{ab ∈ (A₀ ×ˢ B₀) \ S | ab.1 + ab.2 = z} :=
        sum_le_sum fun z hz => hR_disj z hz
      _ = #{ab ∈ (A₀ ×ˢ B₀) \ S | ab.1 + ab.2 ∈ R} :=
        sum_card_fiberwise_eq_card_filter ((A₀ ×ˢ B₀) \ S) R (fun ab => ab.1 + ab.2)
      _ ≤ #((A₀ ×ˢ B₀) \ S) := card_filter_le _ _
      _ = #(A₀ ×ˢ B₀) - #S := card_sdiff_of_subset hS
  have hR_small : #R ≤ b3 := by
    have h1 : #R * (b3 + 1) ≤ b3 ^ 2 := hR_bound.trans hS_loss
    by_contra hgt
    have hge : b3 + 1 ≤ #R := by omega
    have : (b3 + 1) * (b3 + 1) ≤ b3 ^ 2 := (Nat.mul_le_mul_right _ hge).trans h1
    nlinarith only [this]
  have hIm_ge : #P ≤ #Im + #R := (card_le_card hP_sub).trans (card_union_le Im R)
  linarith only [hP_large, hIm_ge, hR_small, hb3_ub]

end PokrovskiyAddComb

namespace PokrovskiyCover
open Finset PokrovskiyHypergraph

lemma card_filter_add_not {α : Type*} [DecidableEq α] (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    #(s.filter p) + #(s.filter (fun x => ¬ p x)) = #s := by
  rw [← card_union_of_disjoint (disjoint_filter.mpr fun _ _ h1 h2 => h2 h1)]
  congr 1
  ext x
  simp only [mem_union, mem_filter]
  tauto

open Classical in
noncomputable def nonnegEdges {n k : ℕ} (hn : 2 * k ≤ n) (x : Fin n → ℝ) : Finset (Idx n k) :=
  univ.filter (fun e => 0 ≤ edgeSum hn x e)

open Classical in
noncomputable def badEdgesAt {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hn : 2 * k ≤ n)
    (x : Fin n → ℝ) (v : Fin n) : Finset (Idx n k) :=
  (bundle hk v).filter (fun e => 0 ≤ edgeSum hn x e)

def isBad {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hn : 2 * k ≤ n) (x : Fin n → ℝ) (v : Fin n) : Prop :=
  3 * k ^ 2 / (2 * 10 ^ 9) ≤ #(badEdgesAt hk hn x v)

def isGood {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hn : 2 * k ≤ n) (x : Fin n → ℝ) (v : Fin n) : Prop :=
  ¬ isBad hk hn x v

lemma badEdgesAt_subset_nonnegEdges {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hn : 2 * k ≤ n)
    (x : Fin n → ℝ) (v : Fin n) :
    badEdgesAt hk hn x v ⊆ nonnegEdges hn x := by
  intro e he
  simp only [badEdgesAt, nonnegEdges, mem_filter, mem_univ, true_and] at he ⊢
  exact he.2

/- Shift and reflection symmetries for `cycInt`, `intSum`, `nonnegEdges`, `isBad`, `isGood` -/

lemma cycInt_shift {n : ℕ} [NeZero n] (d u : Fin n) (L : ℕ) :
    cycInt (d + u) L = image (fun w => d + w) (cycInt u L) := by
  ext w
  simp only [cycInt, mem_image, mem_range]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨u + natToFin m, ⟨m, hm, rfl⟩, (add_assoc d u _).symm⟩
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨m, hm, add_assoc d u _⟩

lemma intSum_shift {n : ℕ} [NeZero n] (x : Fin n → ℝ) (d u : Fin n) (L : ℕ) :
    intSum (fun w => x (d + w)) u L = intSum x (d + u) L := by
  unfold intSum
  rw [cycInt_shift, sum_image (fun _ _ _ _ h => add_left_cancel h)]

lemma intSum_refl {n : ℕ} [NeZero n] (x : Fin n → ℝ) (c u : Fin n) {L : ℕ} (hL : 1 ≤ L) :
    intSum (fun w => x (c - w)) u L = intSum x (c - (u + natToFin (L - 1))) L := by
  unfold intSum
  rw [← cycInt_image_sub c u hL, sum_image (fun _ _ _ _ h => sub_right_injective h)]

lemma card_nonnegEdges_shift {n k : ℕ} [NeZero n] (hn : 2 * k ≤ n) (x : Fin n → ℝ) (d : Fin n) :
    #(nonnegEdges hn (fun w => x (d + w))) = #(nonnegEdges hn x) := by
  classical
  unfold nonnegEdges
  refine card_nbij' (shiftIdx d) (shiftIdx (-d)) ?_ ?_ ?_ ?_
  · intro e he
    simp only [mem_coe, mem_filter, mem_univ, true_and] at he ⊢
    rwa [edgeSum_shiftIdx]
  · intro e he
    simp only [mem_coe, mem_filter, mem_univ, true_and] at he ⊢
    have h1 := edgeSum_shiftIdx hn x d (shiftIdx (-d) e)
    have h2 : shiftIdx d (shiftIdx (-d) e) = e :=
      Prod.ext (by dsimp [shiftIdx]; abel_nf) rfl
    rw [h2] at h1
    rwa [← h1]
  · intro e _; exact Prod.ext (by dsimp [shiftIdx]; abel_nf) rfl
  · intro e _; exact Prod.ext (by dsimp [shiftIdx]; abel_nf) rfl

lemma badEdgesAt_shift {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hn : 2 * k ≤ n)
    (x : Fin n → ℝ) (d v : Fin n) :
    badEdgesAt hk hn x (d + v) = image (shiftIdx d) (badEdgesAt hk hn (fun w => x (d + w)) v) := by
  classical
  ext e
  simp only [badEdgesAt, mem_filter, mem_image]
  constructor
  · rintro ⟨hb, hsum⟩
    rw [bundle_shift, mem_image] at hb
    rcases hb with ⟨e₀, he₀, rfl⟩
    rw [edgeSum_shiftIdx] at hsum
    exact ⟨e₀, ⟨he₀, hsum⟩, rfl⟩
  · rintro ⟨e₀, ⟨he₀, hsum⟩, rfl⟩
    rw [bundle_shift, edgeSum_shiftIdx]
    exact ⟨mem_image_of_mem _ he₀, hsum⟩

lemma isBad_shift {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hn : 2 * k ≤ n)
    (x : Fin n → ℝ) (d v : Fin n) :
    isBad hk hn x (d + v) ↔ isBad hk hn (fun w => x (d + w)) v := by
  unfold isBad
  rw [badEdgesAt_shift, card_image_of_injective _ (shiftIdx_injective d)]

lemma isGood_shift {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hn : 2 * k ≤ n)
    (x : Fin n → ℝ) (d v : Fin n) :
    isGood hk hn x (d + v) ↔ isGood hk hn (fun w => x (d + w)) v :=
  not_congr (isBad_shift hk hn x d v)

lemma card_nonnegEdges_refl {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hn : 2 * k ≤ n)
    (x : Fin n → ℝ) (c : Fin n) :
    #(nonnegEdges hn (fun w => x (c - w))) = #(nonnegEdges hn x) := by
  classical
  unfold nonnegEdges
  refine card_nbij' (reflIdx hk c) (reflIdx hk c) ?_ ?_ ?_ ?_
  · intro e he
    simp only [mem_coe, mem_filter, mem_univ, true_and] at he ⊢
    rwa [edgeSum_reflIdx hk hn x c e]
  · intro e he
    simp only [mem_coe, mem_filter, mem_univ, true_and] at he ⊢
    have h1 := edgeSum_reflIdx hk hn x c (reflIdx hk c e)
    rw [reflIdx_involutive hk c e] at h1
    rwa [← h1]
  · intro e _; exact reflIdx_involutive hk c e
  · intro e _; exact reflIdx_involutive hk c e

lemma badEdgesAt_refl {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hn : 2 * k ≤ n)
    (x : Fin n → ℝ) (c v : Fin n) :
    image (reflIdx hk c) (badEdgesAt hk hn x v) =
      badEdgesAt hk hn (fun w => x (c - w)) (c - v) := by
  classical
  ext e
  simp only [badEdgesAt, mem_image, mem_filter]
  constructor
  · rintro ⟨e₀, ⟨he₀, hsum⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← bundle_refl hk c v]
      exact mem_image_of_mem _ he₀
    · have h1 := edgeSum_reflIdx hk hn x c (reflIdx hk c e₀)
      rw [reflIdx_involutive hk c e₀] at h1
      rwa [← h1]
  · rintro ⟨he, hsum⟩
    rw [← bundle_refl hk c v, mem_image] at he
    rcases he with ⟨e₀, he₀, rfl⟩
    refine ⟨e₀, ⟨he₀, ?_⟩, rfl⟩
    have h1 := edgeSum_reflIdx hk hn x c (reflIdx hk c e₀)
    rw [reflIdx_involutive hk c e₀] at h1
    rwa [h1]

lemma isBad_refl {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hn : 2 * k ≤ n)
    (x : Fin n → ℝ) (c v : Fin n) :
    isBad hk hn (fun w => x (c - w)) (c - v) ↔ isBad hk hn x v := by
  unfold isBad
  rw [← badEdgesAt_refl, card_image_of_injective _ (reflIdx_injective hk c)]

lemma isGood_refl {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hn : 2 * k ≤ n)
    (x : Fin n → ℝ) (c v : Fin n) :
    isGood hk hn (fun w => x (c - w)) (c - v) ↔ isGood hk hn x v :=
  not_congr (isBad_refl hk hn x c v)

/- Double counting bad vertices against nonnegative edges -/

lemma card_biUnion_badEdgesAt_ge {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hn : 2 * k ≤ n)
    (x : Fin n → ℝ) (V : Finset (Fin n)) (hV : ∀ v ∈ V, isBad hk hn x v) :
    #V * (3 * k ^ 2 / (2 * 10 ^ 9)) ≤ 88 * #(V.biUnion (badEdgesAt hk hn x)) := by
  let U := V.biUnion (badEdgesAt hk hn x)
  have h1 : #V * (3 * k ^ 2 / (2 * 10 ^ 9)) ≤ ∑ v ∈ V, #(badEdgesAt hk hn x v) := by
    calc #V * (3 * k ^ 2 / (2 * 10 ^ 9))
      _ = ∑ _v ∈ V, (3 * k ^ 2 / (2 * 10 ^ 9)) := by simp
      _ ≤ ∑ v ∈ V, #(badEdgesAt hk hn x v) := sum_le_sum hV
  have h2 : ∑ v ∈ V, #(badEdgesAt hk hn x v) =
      ∑ e ∈ U, #(V.filter (fun v => e ∈ badEdgesAt hk hn x v)) := by
    have hrew : ∀ v ∈ V, #(badEdgesAt hk hn x v) =
        ∑ e ∈ U, if e ∈ badEdgesAt hk hn x v then 1 else 0 := by
      intro v hv
      rw [← card_filter]
      congr 1
      ext e
      simp only [mem_filter]
      exact ⟨fun he => ⟨mem_biUnion.mpr ⟨v, hv, he⟩, he⟩, fun h => h.2⟩
    rw [sum_congr rfl hrew, sum_comm]
    refine sum_congr rfl fun e _ => ?_
    rw [card_filter]
  have h3 : ∑ e ∈ U, #(V.filter (fun v => e ∈ badEdgesAt hk hn x v)) ≤ 88 * #U := by
    calc ∑ e ∈ U, #(V.filter (fun v => e ∈ badEdgesAt hk hn x v))
      _ ≤ ∑ e ∈ U, #(univ.filter (fun v : Fin n => e ∈ bundle hk v)) := by
        refine sum_le_sum fun e _ => card_le_card fun v hv => ?_
        simp only [badEdgesAt, mem_filter, mem_univ, true_and] at hv ⊢
        exact hv.2.1
      _ ≤ ∑ _e ∈ U, 88 := sum_le_sum fun e _ => card_vertices_containing_le hk e
      _ = 88 * #U := by simp [mul_comm]
  exact h1.trans (h2.trans_le h3)

/- Arithmetic & structural helpers for Claim `cover` -/

lemma nat_mul_add_inj {M q₁ r₁ q₂ r₂ : ℕ} (hr₁ : r₁ < M) (hr₂ : r₂ < M)
    (heq : M * q₁ + r₁ = M * q₂ + r₂) : q₁ = q₂ ∧ r₁ = r₂ := by
  rcases lt_trichotomy q₁ q₂ with hlt | rfl | hgt
  · exfalso
    have hle : M * (q₁ + 1) ≤ M * q₂ := Nat.mul_le_mul_left M hlt
    have hmul : M * (q₁ + 1) = M * q₁ + M := by ring
    omega
  · exact ⟨rfl, by omega⟩
  · exfalso
    have hle : M * (q₂ + 1) ≤ M * q₁ := Nat.mul_le_mul_left M hgt
    have hmul : M * (q₂ + 1) = M * q₂ + M := by ring
    omega

lemma nat_mul_add_icc_inj {M q₁ r₁ q₂ r₂ : ℕ}
    (hr₁ : 1 ≤ r₁ ∧ r₁ ≤ M) (hr₂ : 1 ≤ r₂ ∧ r₂ ≤ M)
    (heq : M * q₁ + r₁ = M * q₂ + r₂) : q₁ = q₂ ∧ r₁ = r₂ := by
  have heq' : M * q₁ + (r₁ - 1) = M * q₂ + (r₂ - 1) := by omega
  obtain ⟨hq, hr⟩ := nat_mul_add_inj (M := M) (by omega) (by omega) heq'
  exact ⟨hq, by omega⟩

def covEdge1 {n k : ℕ} (v : Fin n) (i₀ j₀ : Fin (k - 1)) : Idx n k :=
  mkIdx v (i₀.val + 1) (j₀.val + 1)
    ⟨by omega, by have := i₀.isLt; omega⟩
    ⟨by omega, by have := j₀.isLt; omega⟩

def covEdge2 {n k : ℕ} [NeZero n] (v : Fin n) (i₀ j₀ : Fin (k - 1)) : Idx n k :=
  mkIdx (v + natToFin (i₀.val + 1)) (j₀.val + 1) (k - (i₀.val + 1))
    ⟨by omega, by have := j₀.isLt; omega⟩
    ⟨by have := i₀.isLt; omega, by omega⟩

lemma intSum_twoK_neg_of_covEdges {n k : ℕ} [NeZero n] (hn : 2 * k ≤ n)
    (x : Fin n → ℝ) (v : Fin n) (i₀ j₀ : Fin (k - 1))
    (h1 : edgeSum hn x (covEdge1 v i₀ j₀) < 0)
    (h2 : edgeSum hn x (covEdge2 v i₀ j₀) < 0) :
    intSum x v (2 * k) < 0 := by
  have hi : i₀.val < k - 1 := i₀.isLt
  have hj : j₀.val < k - 1 := j₀.isLt
  have eq1 : covEdge1 v i₀ j₀ =
      mkIdx (v + natToFin 0) (i₀.val + 1) (j₀.val + 1) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ := by
    simp [covEdge1, natToFin_zero]
  rw [eq1, edgeSum_mkIdx_prefix hn x v 0 (i₀.val + 1) (j₀.val + 1)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)] at h1
  unfold covEdge2 at h2
  rw [edgeSum_mkIdx_prefix hn x v (i₀.val + 1) (j₀.val + 1) (k - (i₀.val + 1))
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)] at h2
  simp only [zero_add, intSum_zero] at h1
  rw [show i₀.val + 1 + k + (k - (i₀.val + 1)) = 2 * k by omega,
      show i₀.val + 1 + (j₀.val + 1) + (k - (i₀.val + 1)) = k + (j₀.val + 1) by omega] at h2
  linarith

lemma intSum_mul_twoK_neg {n k : ℕ} [NeZero n] (x : Fin n → ℝ) (v : Fin n) :
    ∀ {d : ℕ}, 1 ≤ d → 2 * k * d ≤ n →
      (∀ u < d, intSum x (v + natToFin (2 * k * u)) (2 * k) < 0) →
      intSum x v (2 * k * d) < 0
  | 0, hd, _, _ => by omega
  | 1, _, _, hall => by
    simpa [natToFin_zero] using hall 0 (by omega)
  | d + 2, _, hbound, hall => by
    have hsplit : 2 * k * (d + 2) = 2 * k * (d + 1) + 2 * k := by ring
    rw [hsplit, intSum_add x v (by omega)]
    have hprev := intSum_mul_twoK_neg x v (d := d + 1) (by omega) (by omega)
      (fun u hu => hall u (by omega))
    have hlast := hall (d + 1) (by omega)
    linarith

lemma bundle_base_val_lt {n k : ℕ} [NeZero n] (hk : 2 ≤ k)
    {s₀ : ℕ} (hs₀ : s₀ ≤ 2 * k) {e₀ : Idx n k}
    (he₀ : e₀ ∈ bundle hk (natToFin (6 * k + s₀))) :
    ∃ u₀ < 13 * k, e₀.1 = natToFin u₀ := by
  let b₀ : Fin n := natToFin (6 * k + s₀)
  have hplus_spec : ∀ i₀ j₀ : Fin (k - 1), ∀ e₁ ∈ bundlePlus b₀ i₀ j₀,
      ∃ off ≤ 4 * k, off + (e₁.2.2.val + k) < 5 * k ∧ e₁.1 = natToFin (6 * k + s₀ + off) := by
    intro i₀ j₀ e₁ he₁
    have hi : i₀.val < k - 1 := i₀.isLt
    have hj : j₀.val < k - 1 := j₀.isLt
    simp only [bundlePlus, mem_biUnion] at he₁
    rcases he₁ with ⟨s, _, hs⟩
    unfold evalSlot at hs
    dsimp only at hs
    split_ifs at hs with hc
    swap
    · simp at hs
    rw [mem_singleton] at hs
    subst hs
    have vld := slotSpec_valid s ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hc
    have hsp_bounds : (slotSpec k s (i₀.val + 1) (j₀.val + 1)).2.1 ≤ 4 * k ∧
        (slotSpec k s (i₀.val + 1) (j₀.val + 1)).2.1 + k +
          (slotSpec k s (i₀.val + 1) (j₀.val + 1)).2.2.2 ≤ 5 * k := by
      cases s with
      | univ m => fin_cases m <;> simp only [slotSpec] at hc ⊢ <;> omega
      | gtExtra m => fin_cases m <;> simp only [slotSpec, decide_eq_true_eq] at hc ⊢ <;> omega
      | gtGe m => fin_cases m <;> simp only [slotSpec, decide_eq_true_eq] at hc ⊢ <;> omega
      | gtLt m => fin_cases m <;> simp only [slotSpec, decide_eq_true_eq] at hc ⊢ <;> omega
      | ltPar odd m =>
        cases odd <;> fin_cases m <;> simp only [slotSpec, decide_eq_true_eq] at hc ⊢ <;> omega
    refine ⟨(slotSpec k s (i₀.val + 1) (j₀.val + 1)).2.1, hsp_bounds.1, ?_, ?_⟩
    · simp only [mkIdx]
      have := vld.2.2.1
      omega
    · simp only [mkIdx, b₀, ← natToFin_add]
  simp only [bundle, mem_biUnion, mem_univ, true_and, mem_union] at he₀
  rcases he₀ with ⟨⟨i₀, j₀⟩, hplus | hminus⟩
  · obtain ⟨off, hoff, _, heq⟩ := hplus_spec i₀ j₀ e₀ hplus
    exact ⟨6 * k + s₀ + off, by omega, heq⟩
  · simp only [bundleMinus, mem_image] at hminus
    rcases hminus with ⟨e₁, he₁, rfl⟩
    obtain ⟨off, _, hoff2, heq₁⟩ := hplus_spec i₀ j₀ e₁ he₁
    refine ⟨(6 * k + s₀) - (off + (e₁.2.2.val + k)), by omega, ?_⟩
    simp only [reflIdx, heq₁]
    rw [sub_eq_iff_eq_add]
    rw [← natToFin_add, ← natToFin_add, ← natToFin_add]
    congr 1
    omega

/-- Helper 1 for `claim_cover`: construct `U₁, U₂` for blocked `r` and bound intersection
with any shift-tower over `Ico 3 T_end`. -/
lemma cover_blocked_and_tower {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hn : 2 * k ≤ n)
    (x' : Fin n → ℝ) {T_end : ℕ}
    (hTend_bound : 2 * k * T_end + 4 * k < n)
    (hShift_bound : 2 * k * (T_end - 3) + 13 * k < n)
    (blocked : Finset ℕ) (hblk_sub : blocked ⊆ Icc 1 (2 * k))
    (hblk_prop : ∀ r ∈ blocked, ∃ t ∈ Ico 3 T_end, ∀ ij : Fin (k - 1) × Fin (k - 1),
      0 ≤ edgeSum hn x' (covEdge1 (natToFin (2 * k * t + r)) ij.1 ij.2) ∨
      0 ≤ edgeSum hn x' (covEdge2 (natToFin (2 * k * t + r)) ij.1 ij.2)) :
    ∃ U_blk ⊆ nonnegEdges hn x',
      #blocked * (k - 1) ^ 2 ≤ 2 * #U_blk ∧
      ∀ (W : Finset (Fin n)) (s₀ : ℕ), s₀ ≤ 2 * k →
        (∀ v ∈ W, ∃ t ∈ Ico 3 T_end, v = natToFin (2 * k * t + s₀)) →
        #((W.biUnion (badEdgesAt hk hn x')) ∩ U_blk) ≤ 176 * k ^ 2 := by
  classical
  let T_all := Ico 3 T_end
  have hblk_ex : ∀ r : ℕ, ∃ t : ℕ, r ∉ blocked ∨
      (t ∈ T_all ∧ ∀ ij : Fin (k - 1) × Fin (k - 1),
        0 ≤ edgeSum hn x' (covEdge1 (natToFin (2 * k * t + r)) ij.1 ij.2) ∨
        0 ≤ edgeSum hn x' (covEdge2 (natToFin (2 * k * t + r)) ij.1 ij.2)) := by
    intro r
    by_cases hr : r ∈ blocked
    · rcases hblk_prop r hr with ⟨t, ht, hij⟩
      exact ⟨t, Or.inr ⟨ht, hij⟩⟩
    · exact ⟨3, Or.inl hr⟩
  choose t_blk ht_blk_or using hblk_ex
  have ht_blk : ∀ r : ℕ, r ∈ blocked →
      t_blk r ∈ T_all ∧ ∀ ij : Fin (k - 1) × Fin (k - 1),
        0 ≤ edgeSum hn x' (covEdge1 (natToFin (2 * k * t_blk r + r)) ij.1 ij.2) ∨
        0 ≤ edgeSum hn x' (covEdge2 (natToFin (2 * k * t_blk r + r)) ij.1 ij.2) :=
    fun r hr => (ht_blk_or r).resolve_left fun hnot => hnot hr
  let B_pairs := blocked ×ˢ (univ : Finset (Fin (k - 1) × Fin (k - 1)))
  let S₁ := B_pairs.filter (fun p =>
    0 ≤ edgeSum hn x' (covEdge1 (natToFin (2 * k * t_blk p.1 + p.1)) p.2.1 p.2.2))
  let S₂ := B_pairs.filter (fun p =>
    ¬ 0 ≤ edgeSum hn x' (covEdge1 (natToFin (2 * k * t_blk p.1 + p.1)) p.2.1 p.2.2))
  let U₁ : Finset (Idx n k) := S₁.image (fun p => covEdge1 (natToFin (2 * k * t_blk p.1 + p.1)) p.2.1 p.2.2)
  let U₂ : Finset (Idx n k) := S₂.image (fun p => covEdge2 (natToFin (2 * k * t_blk p.1 + p.1)) p.2.1 p.2.2)
  let U_blk := U₁ ∪ U₂
  have hUblk_sub : U_blk ⊆ nonnegEdges hn x' := by
    intro e he
    simp only [U_blk, U₁, U₂, S₁, S₂, nonnegEdges, mem_union, mem_image, mem_filter, mem_univ,
      true_and] at he ⊢
    rcases he with ⟨p, ⟨_, hnonneg⟩, rfl⟩ | ⟨p, ⟨hpB, hneg1⟩, rfl⟩
    · exact hnonneg
    · have hrB : p.1 ∈ blocked := (mem_product.mp hpB).1
      exact ((ht_blk p.1 hrB).2 p.2).resolve_left hneg1
  have hU₁_card : #U₁ = #S₁ := by
    dsimp only [U₁]
    refine card_image_of_injOn fun p₁ hp₁ p₂ hp₂ heq => ?_
    rw [mem_coe, mem_filter, mem_product] at hp₁ hp₂
    have hr₁ : 1 ≤ p₁.1 ∧ p₁.1 ≤ 2 * k := mem_Icc.mp (hblk_sub hp₁.1.1)
    have hr₂ : 1 ≤ p₂.1 ∧ p₂.1 ≤ 2 * k := mem_Icc.mp (hblk_sub hp₂.1.1)
    have ht₁ : t_blk p₁.1 < T_end := (mem_Ico.mp (ht_blk p₁.1 hp₁.1.1).1).2
    have ht₂ : t_blk p₂.1 < T_end := (mem_Ico.mp (ht_blk p₂.1 hp₂.1.1).1).2
    simp only [covEdge1, mkIdx, Prod.mk.injEq, Fin.ext_iff] at heq
    have hij1 : p₁.2.1 = p₂.2.1 := Fin.ext (by omega)
    have hij2 : p₁.2.2 = p₂.2.2 := Fin.ext (by omega)
    have hlt1 : 2 * k * t_blk p₁.1 + p₁.1 < n := by
      have := Nat.mul_le_mul_left (2 * k) ht₁.le; omega
    have hlt2 : 2 * k * t_blk p₂.1 + p₂.1 < n := by
      have := Nat.mul_le_mul_left (2 * k) ht₂.le; omega
    have hv := heq.1
    simp only [val_natToFin, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hv
    have hr_eq := (nat_mul_add_icc_inj hr₁ hr₂ hv).2
    exact Prod.ext hr_eq (Prod.ext hij1 hij2)
  have hU₂_card : #U₂ = #S₂ := by
    dsimp only [U₂]
    refine card_image_of_injOn fun p₁ hp₁ p₂ hp₂ heq => ?_
    rw [mem_coe, mem_filter, mem_product] at hp₁ hp₂
    have hr₁ : 1 ≤ p₁.1 ∧ p₁.1 ≤ 2 * k := mem_Icc.mp (hblk_sub hp₁.1.1)
    have hr₂ : 1 ≤ p₂.1 ∧ p₂.1 ≤ 2 * k := mem_Icc.mp (hblk_sub hp₂.1.1)
    have ht₁ : t_blk p₁.1 < T_end := (mem_Ico.mp (ht_blk p₁.1 hp₁.1.1).1).2
    have ht₂ : t_blk p₂.1 < T_end := (mem_Ico.mp (ht_blk p₂.1 hp₂.1.1).1).2
    have hi₁ : p₁.2.1.val < k - 1 := p₁.2.1.isLt
    have hi₂ : p₂.2.1.val < k - 1 := p₂.2.1.isLt
    simp only [covEdge2, mkIdx, Prod.mk.injEq, Fin.ext_iff] at heq
    have hij2 : p₁.2.2 = p₂.2.2 := Fin.ext (by omega)
    have hij1 : p₁.2.1 = p₂.2.1 := Fin.ext (by omega)
    have hlt1 : 2 * k * t_blk p₁.1 + p₁.1 + (p₁.2.1.val + 1) < n := by
      have := Nat.mul_le_mul_left (2 * k) ht₁.le; omega
    have hlt2 : 2 * k * t_blk p₂.1 + p₂.1 + (p₂.2.1.val + 1) < n := by
      have := Nat.mul_le_mul_left (2 * k) ht₂.le; omega
    have hv := heq.1
    rw [← natToFin_add, ← natToFin_add] at hv
    simp only [val_natToFin, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hv
    rw [hij1] at hv
    have hv' : 2 * k * t_blk p₁.1 + p₁.1 = 2 * k * t_blk p₂.1 + p₂.1 := by omega
    have hr_eq := (nat_mul_add_icc_inj hr₁ hr₂ hv').2
    exact Prod.ext hr_eq (Prod.ext hij1 hij2)
  have hUblk_lb : #blocked * (k - 1) ^ 2 ≤ 2 * #U_blk := by
    have hS_sum : #S₁ + #S₂ = #blocked * (k - 1) ^ 2 := by
      have h1 := card_filter_add_not B_pairs
        (fun p => 0 ≤ edgeSum hn x' (covEdge1 (natToFin (2 * k * t_blk p.1 + p.1)) p.2.1 p.2.2))
      have h2 : #B_pairs = #blocked * (k - 1) ^ 2 := by
        simp [B_pairs, pow_two]
      change #S₁ + #S₂ = #B_pairs at h1
      omega
    have hle1 : #U₁ ≤ #U_blk := card_le_card fun _ h => mem_union_left _ h
    have hle2 : #U₂ ≤ #U_blk := card_le_card fun _ h => mem_union_right _ h
    omega
  refine ⟨U_blk, hUblk_sub, hUblk_lb, ?_⟩
  intro W s₀ hs₀ hv_shift
  let b₀ : Fin n := natToFin (6 * k + s₀)
  let sh (t : ℕ) (e₀ : Idx n k) : Idx n k := shiftIdx (natToFin (2 * k * (t - 3))) e₀
  have hsub_tower : (W.biUnion (badEdgesAt hk hn x')) ∩ U_blk ⊆
      (bundle hk b₀).biUnion (fun e₀ =>
        (T_all.filter (fun t => sh t e₀ ∈ U_blk)).image (fun t => sh t e₀)) := by
    intro e he
    rcases mem_inter.mp he with ⟨heV, heB⟩
    rcases mem_biUnion.mp heV with ⟨v, hv, hev⟩
    obtain ⟨t, ht, rfl⟩ := hv_shift v hv
    have ht3 : 3 ≤ t := (mem_Ico.mp ht).1
    have hv_eq : (natToFin (2 * k * t + s₀) : Fin n) = natToFin (2 * k * (t - 3)) + b₀ := by
      dsimp only [b₀]
      rw [← natToFin_add]
      congr 1
      have h1 : 2 * k * (t - 3) + 2 * k * 3 = 2 * k * t := by
        rw [← Nat.mul_add, Nat.sub_add_cancel ht3]
      linarith
    have he_bun : e ∈ bundle hk (natToFin (2 * k * (t - 3)) + b₀) := by
      rw [← hv_eq]
      exact (mem_filter.mp hev).1
    rw [bundle_shift] at he_bun
    rcases mem_image.mp he_bun with ⟨e₀, he₀, rfl⟩
    exact mem_biUnion.mpr ⟨e₀, he₀, mem_image.mpr ⟨t, mem_filter.mpr ⟨ht, heB⟩, rfl⟩⟩
  have hfiber_le_two : ∀ e₀ ∈ bundle hk b₀,
      #(T_all.filter (fun t => sh t e₀ ∈ U_blk)) ≤ 2 := by
    intro e₀ he₀
    obtain ⟨u₀, hu₀, he₀_fst⟩ := bundle_base_val_lt hk hs₀ he₀
    let F₁ := T_all.filter (fun t => sh t e₀ ∈ U₁)
    let F₂ := T_all.filter (fun t => sh t e₀ ∈ U₂)
    have hF_sub : T_all.filter (fun t => sh t e₀ ∈ U_blk) ⊆ F₁ ∪ F₂ := by
      intro t ht
      simp only [F₁, F₂, U_blk, mem_union, mem_filter] at ht ⊢
      exact ht.2.imp (fun h => ⟨ht.1, h⟩) (fun h => ⟨ht.1, h⟩)
    have hF₁ : #F₁ ≤ 1 := by
      refine card_le_one.mpr fun t ht t' ht' => ?_
      simp only [F₁, U₁, mem_filter, mem_image] at ht ht'
      rcases ht with ⟨ht_mem, p, hp, heq⟩
      rcases ht' with ⟨ht'_mem, p', hp', heq'⟩
      rw [mem_Ico] at ht_mem ht'_mem
      rw [mem_filter, mem_product] at hp hp'
      have hrp : 1 ≤ p.1 ∧ p.1 ≤ 2 * k := mem_Icc.mp (hblk_sub hp.1.1)
      have hrp' : 1 ≤ p'.1 ∧ p'.1 ≤ 2 * k := mem_Icc.mp (hblk_sub hp'.1.1)
      have htp : t_blk p.1 < T_end := (mem_Ico.mp (ht_blk p.1 hp.1.1).1).2
      have htp' : t_blk p'.1 < T_end := (mem_Ico.mp (ht_blk p'.1 hp'.1.1).1).2
      have hv1 := congrArg (fun z : Idx n k => z.1.val) heq
      have hv2 := congrArg (fun z : Idx n k => z.1.val) heq'
      simp only [covEdge1, mkIdx, sh, shiftIdx, he₀_fst, ← natToFin_add] at hv1 hv2
      have hlt_sh1 : 2 * k * (t - 3) + u₀ < n := by
        have hle : t - 3 ≤ T_end - 3 := by omega
        have := Nat.mul_le_mul_left (2 * k) hle; linarith
      have hlt_sh2 : 2 * k * (t' - 3) + u₀ < n := by
        have hle : t' - 3 ≤ T_end - 3 := by omega
        have := Nat.mul_le_mul_left (2 * k) hle; linarith
      have hlt_p1 : 2 * k * t_blk p.1 + p.1 < n := by
        have := Nat.mul_le_mul_left (2 * k) htp.le; omega
      have hlt_p2 : 2 * k * t_blk p'.1 + p'.1 < n := by
        have := Nat.mul_le_mul_left (2 * k) htp'.le; omega
      simp only [val_natToFin, Nat.mod_eq_of_lt hlt_sh1, Nat.mod_eq_of_lt hlt_sh2,
        Nat.mod_eq_of_lt hlt_p1, Nat.mod_eq_of_lt hlt_p2] at hv1 hv2
      have hcross : 2 * k * (t_blk p.1 + (t' - 3)) + p.1 =
          2 * k * (t_blk p'.1 + (t - 3)) + p'.1 := by
        have hmul1 : 2 * k * (t_blk p.1 + (t' - 3)) = 2 * k * t_blk p.1 + 2 * k * (t' - 3) := by ring
        have hmul2 : 2 * k * (t_blk p'.1 + (t - 3)) = 2 * k * t_blk p'.1 + 2 * k * (t - 3) := by ring
        linarith
      have hp_eq : p.1 = p'.1 := (nat_mul_add_icc_inj hrp hrp' hcross).2
      rw [hp_eq] at hv1
      have hdiff : 2 * k * (t - 3) = 2 * k * (t' - 3) := by linarith
      have hpos : 0 < 2 * k := by omega
      have ht3_eq : t - 3 = t' - 3 := Nat.eq_of_mul_eq_mul_left hpos hdiff
      omega
    have hF₂ : #F₂ ≤ 1 := by
      refine card_le_one.mpr fun t ht t' ht' => ?_
      simp only [F₂, U₂, mem_filter, mem_image] at ht ht'
      rcases ht with ⟨ht_mem, p, hp, heq⟩
      rcases ht' with ⟨ht'_mem, p', hp', heq'⟩
      rw [mem_Ico] at ht_mem ht'_mem
      rw [mem_filter, mem_product] at hp hp'
      have hrp : 1 ≤ p.1 ∧ p.1 ≤ 2 * k := mem_Icc.mp (hblk_sub hp.1.1)
      have hrp' : 1 ≤ p'.1 ∧ p'.1 ≤ 2 * k := mem_Icc.mp (hblk_sub hp'.1.1)
      have htp : t_blk p.1 < T_end := (mem_Ico.mp (ht_blk p.1 hp.1.1).1).2
      have htp' : t_blk p'.1 < T_end := (mem_Ico.mp (ht_blk p'.1 hp'.1.1).1).2
      have hip : p.2.1.val < k - 1 := p.2.1.isLt
      have hip' : p'.2.1.val < k - 1 := p'.2.1.isLt
      have hi_eq1 : k - (p.2.1.val + 1) - 1 = e₀.2.2.val :=
        congrArg (fun z : Idx n k => z.2.2.val) heq
      have hi_eq2 : k - (p'.2.1.val + 1) - 1 = e₀.2.2.val :=
        congrArg (fun z : Idx n k => z.2.2.val) heq'
      have hp_ival : p.2.1.val = p'.2.1.val := by omega
      have hv1 := congrArg (fun z : Idx n k => z.1.val) heq
      have hv2 := congrArg (fun z : Idx n k => z.1.val) heq'
      simp only [covEdge2, mkIdx, sh, shiftIdx, he₀_fst, ← natToFin_add] at hv1 hv2
      have hlt_sh1 : 2 * k * (t - 3) + u₀ < n := by
        have hle : t - 3 ≤ T_end - 3 := by omega
        have := Nat.mul_le_mul_left (2 * k) hle; linarith
      have hlt_sh2 : 2 * k * (t' - 3) + u₀ < n := by
        have hle : t' - 3 ≤ T_end - 3 := by omega
        have := Nat.mul_le_mul_left (2 * k) hle; linarith
      have hlt_p1 : 2 * k * t_blk p.1 + p.1 + (p.2.1.val + 1) < n := by
        have := Nat.mul_le_mul_left (2 * k) htp.le; omega
      have hlt_p2 : 2 * k * t_blk p'.1 + p'.1 + (p'.2.1.val + 1) < n := by
        have := Nat.mul_le_mul_left (2 * k) htp'.le; omega
      simp only [val_natToFin, Nat.mod_eq_of_lt hlt_sh1, Nat.mod_eq_of_lt hlt_sh2,
        Nat.mod_eq_of_lt hlt_p1, Nat.mod_eq_of_lt hlt_p2] at hv1 hv2
      rw [hp_ival] at hv1
      have hcross : 2 * k * (t_blk p.1 + (t' - 3)) + p.1 =
          2 * k * (t_blk p'.1 + (t - 3)) + p'.1 := by
        have hmul1 : 2 * k * (t_blk p.1 + (t' - 3)) = 2 * k * t_blk p.1 + 2 * k * (t' - 3) := by ring
        have hmul2 : 2 * k * (t_blk p'.1 + (t - 3)) = 2 * k * t_blk p'.1 + 2 * k * (t - 3) := by ring
        linarith
      have hp_eq : p.1 = p'.1 := (nat_mul_add_icc_inj hrp hrp' hcross).2
      rw [hp_eq] at hv1
      have hdiff : 2 * k * (t - 3) = 2 * k * (t' - 3) := by linarith
      have hpos : 0 < 2 * k := by omega
      have ht3_eq : t - 3 = t' - 3 := Nat.eq_of_mul_eq_mul_left hpos hdiff
      omega
    have hu := (card_le_card hF_sub).trans (card_union_le F₁ F₂)
    omega
  calc #((W.biUnion (badEdgesAt hk hn x')) ∩ U_blk)
    _ ≤ #((bundle hk b₀).biUnion (fun e₀ =>
        (T_all.filter (fun t => sh t e₀ ∈ U_blk)).image (fun t => sh t e₀))) :=
      card_le_card hsub_tower
    _ ≤ ∑ e₀ ∈ bundle hk b₀, #((T_all.filter (fun t => sh t e₀ ∈ U_blk)).image (fun t => sh t e₀)) :=
      card_biUnion_le
    _ ≤ ∑ e₀ ∈ bundle hk b₀, #(T_all.filter (fun t => sh t e₀ ∈ U_blk)) :=
      sum_le_sum fun _ _ => card_image_le
    _ ≤ ∑ _e₀ ∈ bundle hk b₀, 2 := sum_le_sum hfiber_le_two
    _ = 2 * #(bundle hk b₀) := by simp [mul_comm]
    _ ≤ 2 * (88 * k ^ 2) := Nat.mul_le_mul_left 2 (card_bundle_le hk b₀)
    _ = 176 * k ^ 2 := by ring

/-- Claim `cover` (Claim 4.1 of Pokrovskiy): any interval `cycInt a₀ L` of length
`1 ≤ L` with `L + (4 * 10 ^ 15 + 20) * k ≤ n` can be extended to `cycInt j₀ L_J` of
length `L_J ≤ L + 4 * 10 ^ 15 * k` with negative sum and good outer neighbors. -/
theorem claim_cover {n k : ℕ} [NeZero n]
    (hk_large : 10 ^ 45 < k)
    (hn : 2 * k ≤ n)
    (x : Fin n → ℝ)
    (h_few : #(nonnegEdges hn x) < k * (k - 1) ^ 2)
    (a₀ : Fin n) {L : ℕ} (hL_pos : 1 ≤ L)
    (hL_ub : L + (4 * 10 ^ 15 + 20) * k ≤ n) :
    ∃ (j₀ : Fin n) (L_J : ℕ),
      1 ≤ L_J ∧
      L_J ≤ L + 4 * 10 ^ 15 * k ∧
      cycInt a₀ L ⊆ cycInt j₀ L_J ∧
      isGood (by omega) hn x (j₀ - natToFin 1) ∧
      isGood (by omega) hn x (j₀ + natToFin L_J) ∧
      intSum x j₀ L_J < 0 := by
  classical
  have hk : 2 ≤ k := by omega
  let d : Fin n := a₀ - natToFin (2 * k * (10 ^ 15 + 3))
  let x' : Fin n → ℝ := fun w => x (d + w)
  have h_few' : #(nonnegEdges hn x') < k * (k - 1) ^ 2 := by
    rwa [card_nonnegEdges_shift]
  suffices hshifted : ∃ (j₀' : Fin n) (L_J : ℕ),
      1 ≤ L_J ∧
      L_J ≤ L + 4 * 10 ^ 15 * k ∧
      cycInt (natToFin (2 * k * (10 ^ 15 + 3))) L ⊆ cycInt j₀' L_J ∧
      isGood hk hn x' (j₀' - natToFin 1) ∧
      isGood hk hn x' (j₀' + natToFin L_J) ∧
      intSum x' j₀' L_J < 0 by
    rcases hshifted with ⟨j₀', L_J, h1, h2, hsub, hg1, hg2, hsum⟩
    refine ⟨d + j₀', L_J, h1, h2, ?_, ?_, ?_, ?_⟩
    · have hdO : d + natToFin (2 * k * (10 ^ 15 + 3)) = a₀ := sub_add_cancel a₀ _
      rw [← hdO, cycInt_shift d _ L, cycInt_shift d j₀' L_J]
      exact image_subset_image hsub
    · have heq : d + j₀' - natToFin 1 = d + (j₀' - natToFin 1) := by abel_nf
      rw [heq, isGood_shift]
      exact hg1
    · rw [add_assoc, isGood_shift]
      exact hg2
    · rwa [← intSum_shift]
  by_contra hno
  obtain ⟨C2, hC2_eq⟩ : ∃ C2, C2 = 10 ^ 15 := ⟨_, rfl⟩
  obtain ⟨m, hm_eq⟩ : ∃ m, m = (L - 1) / (2 * k) := ⟨_, rfl⟩
  have hm_lb : 2 * k * m < L := by
    have hle : 2 * k * m ≤ L - 1 := hm_eq ▸ Nat.mul_div_le (L - 1) (2 * k)
    omega
  have hm_ub : L ≤ 2 * k * (m + 1) := by
    have hpos : 0 < 2 * k := by omega
    have hlt : L - 1 < 2 * k * (m + 1) := by
      have := Nat.lt_mul_div_succ (L - 1) hpos
      rw [← hm_eq] at this
      simpa [Nat.add_comm] using this
    omega
  obtain ⟨T_end, hTend_eq⟩ : ∃ T_end, T_end = 2 * C2 + m + 4 := ⟨_, rfl⟩
  have hTend_bound : 2 * k * T_end + 4 * k < n := by
    have heq : 2 * k * T_end + 4 * k = 2 * k * m + (4 * 10 ^ 15 + 12) * k := by
      rw [hTend_eq, hC2_eq]; ring
    linarith
  have hShift_bound : 2 * k * (T_end - 3) + 13 * k < n := by
    have hsub3 : T_end - 3 = 2 * C2 + m + 1 := by omega
    have heq : 2 * k * (T_end - 3) + 13 * k = 2 * k * m + (4 * 10 ^ 15 + 15) * k := by
      rw [hsub3, hC2_eq]; ring
    linarith
  let T₁ : Finset ℕ := Ico 3 (3 + C2)
  let T₂ : Finset ℕ := Ico (C2 + m + 4) T_end
  let T_all : Finset ℕ := Ico 3 T_end
  let R_all : Finset ℕ := Icc 1 (2 * k)
  let isUnblocked (r : ℕ) : Prop :=
    ∀ t ∈ T_all, ∃ ij : Fin (k - 1) × Fin (k - 1),
      edgeSum hn x' (covEdge1 (natToFin (2 * k * t + r)) ij.1 ij.2) < 0 ∧
      edgeSum hn x' (covEdge2 (natToFin (2 * k * t + r)) ij.1 ij.2) < 0
  let unblocked : Finset ℕ := R_all.filter (fun r => isUnblocked r)
  let blocked : Finset ℕ := R_all.filter (fun r => ¬ isUnblocked r)
  have hpart_card : #unblocked + #blocked = 2 * k := by
    have h1 := card_filter_add_not R_all (fun r => isUnblocked r)
    have h2 : #R_all = 2 * k := by simp [R_all]
    change #unblocked + #blocked = #R_all at h1
    omega
  have hunb_bad : ∀ r ∈ unblocked,
      (∀ t₁ ∈ T₁, isBad hk hn x' (natToFin (2 * k * t₁ + r - 1))) ∨
      (∀ t₂ ∈ T₂, isBad hk hn x' (natToFin (2 * k * t₂ + r))) := by
    intro r hr
    simp only [unblocked, R_all, mem_filter, mem_Icc] at hr
    rcases hr with ⟨⟨hr1, hr2⟩, hunb⟩
    by_contra hnot
    push Not at hnot
    rcases hnot with ⟨⟨t₁, ht₁, hg₁⟩, ⟨t₂, ht₂, hg₂⟩⟩
    simp only [T₁, T₂, mem_Ico] at ht₁ ht₂
    have ht_lt : t₁ < t₂ := by omega
    let j₀' : Fin n := natToFin (2 * k * t₁ + r)
    let L_J : ℕ := 2 * k * (t₂ - t₁)
    have h1 : 1 ≤ L_J := by
      dsimp only [L_J]
      have hpos_d : 1 ≤ t₂ - t₁ := by omega
      nlinarith only [hk, hpos_d]
    have h2 : L_J ≤ L + 4 * 10 ^ 15 * k := by
      dsimp only [L_J]
      have hdiff : t₂ - t₁ ≤ 2 * 10 ^ 15 + m := by omega
      have hmul := Nat.mul_le_mul_left (2 * k) hdiff
      have hring : 2 * k * (2 * 10 ^ 15 + m) = 2 * k * m + 4 * 10 ^ 15 * k := by ring
      linarith only [hmul, hring, hm_lb]
    have h3 : cycInt (natToFin (2 * k * (10 ^ 15 + 3))) L ⊆ cycInt j₀' L_J := by
      intro w hw
      simp only [cycInt, mem_image, mem_range] at hw ⊢
      rcases hw with ⟨p, hp, rfl⟩
      have hlo : 2 * k * t₁ + r ≤ 2 * k * (10 ^ 15 + 3) + p := by
        have ht₁_le : t₁ + 1 ≤ 10 ^ 15 + 3 := by omega
        have hmul := Nat.mul_le_mul_left (2 * k) ht₁_le
        have hring : 2 * k * (t₁ + 1) = 2 * k * t₁ + 2 * k := by ring
        linarith only [hmul, hring, hr2]
      have hhi : 2 * k * (10 ^ 15 + 3) + p < (2 * k * t₁ + r) + L_J := by
        dsimp only [L_J]
        have ht₂_ge : 10 ^ 15 + m + 4 ≤ t₂ := hC2_eq ▸ ht₂.1
        have hmul := Nat.mul_le_mul_left (2 * k) ht₂_ge
        have hring1 : 2 * k * (10 ^ 15 + m + 4) = 2 * k * (10 ^ 15 + 3) + 2 * k * (m + 1) := by ring
        have hsub_add : 2 * k * t₁ + 2 * k * (t₂ - t₁) = 2 * k * t₂ := by
          rw [← Nat.mul_add, Nat.add_sub_of_le ht_lt.le]
        linarith only [hmul, hring1, hsub_add, hp, hm_ub, hr1]
      refine ⟨(2 * k * (10 ^ 15 + 3) + p) - (2 * k * t₁ + r), by omega, ?_⟩
      dsimp only [j₀']
      rw [← natToFin_add, ← natToFin_add]
      congr 1
      omega
    have h4 : isGood hk hn x' (j₀' - natToFin 1) := by
      have heq : j₀' - natToFin 1 = natToFin (2 * k * t₁ + r - 1) := by
        rw [sub_eq_iff_eq_add, ← natToFin_add]
        dsimp only [j₀']
        congr 1
        omega
      rw [heq]
      exact hg₁
    have h5 : isGood hk hn x' (j₀' + natToFin L_J) := by
      have heq : j₀' + natToFin L_J = natToFin (2 * k * t₂ + r) := by
        dsimp only [j₀', L_J]
        rw [← natToFin_add]
        congr 1
        have hsub_add : 2 * k * t₁ + 2 * k * (t₂ - t₁) = 2 * k * t₂ := by
          rw [← Nat.mul_add, Nat.add_sub_of_le ht_lt.le]
        linarith
      rw [heq]
      exact hg₂
    have h6 : intSum x' j₀' L_J < 0 := by
      have hLJ_le_n : 2 * k * (t₂ - t₁) ≤ n := by
        have hle : t₂ - t₁ ≤ T_end := by omega
        have := Nat.mul_le_mul_left (2 * k) hle
        linarith
      refine intSum_mul_twoK_neg x' j₀' (d := t₂ - t₁) (by omega) hLJ_le_n fun u hu => ?_
      have htu_mem : t₁ + u ∈ T_all := by
        simp only [T_all, mem_Ico]
        omega
      obtain ⟨ij, he1, he2⟩ := hunb (t₁ + u) htu_mem
      have hv_eq : j₀' + natToFin (2 * k * u) = natToFin (2 * k * (t₁ + u) + r) := by
        dsimp only [j₀']
        rw [← natToFin_add]
        congr 1
        ring
      rw [hv_eq]
      exact intSum_twoK_neg_of_covEdges hn x' _ ij.1 ij.2 he1 he2
    exact hno ⟨j₀', L_J, h1, h2, h3, h4, h5, h6⟩
  -- Unblocked vertex sets V_r
  let V_r (r : ℕ) : Finset (Fin n) :=
    if ∀ t₁ ∈ T₁, isBad hk hn x' (natToFin (2 * k * t₁ + r - 1)) then
      T₁.image (fun t₁ => natToFin (2 * k * t₁ + r - 1))
    else
      T₂.image (fun t₂ => natToFin (2 * k * t₂ + r))
  have hVr_bad : ∀ r ∈ unblocked, ∀ v ∈ V_r r, isBad hk hn x' v := by
    intro r hr v hv
    dsimp only [V_r] at hv
    split_ifs at hv with hleft
    · rcases mem_image.mp hv with ⟨t₁, ht₁, rfl⟩
      exact hleft t₁ ht₁
    · rcases mem_image.mp hv with ⟨t₂, ht₂, rfl⟩
      exact (hunb_bad r hr).resolve_left hleft t₂ ht₂
  have hVr_card : ∀ r ∈ unblocked, #(V_r r) = C2 := by
    intro r hr
    have hr_mem : 1 ≤ r ∧ r ≤ 2 * k := mem_Icc.mp (mem_filter.mp hr).1
    dsimp only [V_r]
    split_ifs with hleft
    · rw [card_image_of_injOn]
      · simp [T₁]
      · intro t₁ ht₁ t₁' ht₁' heq
        rw [mem_coe, mem_Ico] at ht₁ ht₁'
        have hlt1 : 2 * k * t₁ + r - 1 < n := by
          have hle : t₁ ≤ T_end := by omega
          have := Nat.mul_le_mul_left (2 * k) hle
          omega
        have hlt2 : 2 * k * t₁' + r - 1 < n := by
          have hle : t₁' ≤ T_end := by omega
          have := Nat.mul_le_mul_left (2 * k) hle
          omega
        have hv := congrArg Fin.val heq
        simp only [val_natToFin, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hv
        have hv' : 2 * k * t₁ + (r - 1) = 2 * k * t₁' + (r - 1) := by omega
        exact (nat_mul_add_inj (M := 2 * k) (by omega) (by omega) hv').1
    · rw [card_image_of_injOn]
      · simp [T₂]; omega
      · intro t₂ ht₂ t₂' ht₂' heq
        rw [mem_coe, mem_Ico] at ht₂ ht₂'
        have hlt1 : 2 * k * t₂ + r < n := by
          have := Nat.mul_le_mul_left (2 * k) ht₂.2.le; omega
        have hlt2 : 2 * k * t₂' + r < n := by
          have := Nat.mul_le_mul_left (2 * k) ht₂'.2.le; omega
        have hv := congrArg Fin.val heq
        simp only [val_natToFin, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hv
        exact (nat_mul_add_icc_inj hr_mem hr_mem hv).1
  have hVr_disj : (unblocked : Set ℕ).PairwiseDisjoint V_r := by
    intro r₁ hr₁ r₂ hr₂ hne
    rw [mem_coe] at hr₁ hr₂
    have hr₁_mem : 1 ≤ r₁ ∧ r₁ ≤ 2 * k := mem_Icc.mp (mem_filter.mp hr₁).1
    have hr₂_mem : 1 ≤ r₂ ∧ r₂ ≤ 2 * k := mem_Icc.mp (mem_filter.mp hr₂).1
    rw [Function.onFun, disjoint_left]
    intro v hv₁ hv₂
    dsimp only [V_r] at hv₁ hv₂
    split_ifs at hv₁ with hl₁ <;> split_ifs at hv₂ with hl₂
    · rcases mem_image.mp hv₁ with ⟨t₁, ht₁, rfl⟩
      rcases mem_image.mp hv₂ with ⟨t₁', ht₁', heq⟩
      rw [mem_Ico] at ht₁ ht₁'
      have hlt1 : 2 * k * t₁ + r₁ - 1 < n := by
        have hle : t₁ ≤ T_end := by omega
        have := Nat.mul_le_mul_left (2 * k) hle; omega
      have hlt2 : 2 * k * t₁' + r₂ - 1 < n := by
        have hle : t₁' ≤ T_end := by omega
        have := Nat.mul_le_mul_left (2 * k) hle; omega
      have hv := congrArg Fin.val heq
      simp only [val_natToFin, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hv
      have hv' : 2 * k * t₁ + (r₁ - 1) = 2 * k * t₁' + (r₂ - 1) := by omega
      have hreq := (nat_mul_add_inj (M := 2 * k) (by omega) (by omega) hv').2
      omega
    · rcases mem_image.mp hv₁ with ⟨t₁, ht₁, rfl⟩
      rcases mem_image.mp hv₂ with ⟨t₂, ht₂, heq⟩
      rw [mem_Ico] at ht₁ ht₂
      have hlt1 : 2 * k * t₁ + r₁ - 1 < 2 * k * (10 ^ 15 + 3) := by
        have ht₁_le : t₁ + 1 ≤ 10 ^ 15 + 3 := by omega
        have hmul := Nat.mul_le_mul_left (2 * k) ht₁_le
        have : 2 * k * (t₁ + 1) = 2 * k * t₁ + 2 * k := by ring
        omega
      have hge2 : 2 * k * (10 ^ 15 + 3) < 2 * k * t₂ + r₂ := by
        have ht₀_le : 10 ^ 15 + 3 ≤ t₂ := by omega
        have hmul := Nat.mul_le_mul_left (2 * k) ht₀_le
        omega
      have hlt2 : 2 * k * t₂ + r₂ < n := by
        have := Nat.mul_le_mul_left (2 * k) ht₂.2.le; omega
      have hv := congrArg Fin.val heq
      simp only [val_natToFin, Nat.mod_eq_of_lt (by linarith : 2 * k * t₁ + r₁ - 1 < n),
        Nat.mod_eq_of_lt hlt2] at hv
      omega
    · rcases mem_image.mp hv₁ with ⟨t₂, ht₂, rfl⟩
      rcases mem_image.mp hv₂ with ⟨t₁, ht₁, heq⟩
      rw [mem_Ico] at ht₁ ht₂
      have hlt1 : 2 * k * t₁ + r₂ - 1 < 2 * k * (10 ^ 15 + 3) := by
        have ht₁_le : t₁ + 1 ≤ 10 ^ 15 + 3 := by omega
        have hmul := Nat.mul_le_mul_left (2 * k) ht₁_le
        have : 2 * k * (t₁ + 1) = 2 * k * t₁ + 2 * k := by ring
        omega
      have hge2 : 2 * k * (10 ^ 15 + 3) < 2 * k * t₂ + r₁ := by
        have ht₀_le : 10 ^ 15 + 3 ≤ t₂ := by omega
        have hmul := Nat.mul_le_mul_left (2 * k) ht₀_le
        omega
      have hlt2 : 2 * k * t₂ + r₁ < n := by
        have := Nat.mul_le_mul_left (2 * k) ht₂.2.le; omega
      have hv := congrArg Fin.val heq
      simp only [val_natToFin, Nat.mod_eq_of_lt (by linarith : 2 * k * t₁ + r₂ - 1 < n),
        Nat.mod_eq_of_lt hlt2] at hv
      omega
    · rcases mem_image.mp hv₁ with ⟨t₂, ht₂, rfl⟩
      rcases mem_image.mp hv₂ with ⟨t₂', ht₂', heq⟩
      rw [mem_Ico] at ht₂ ht₂'
      have hlt1 : 2 * k * t₂ + r₁ < n := by
        have := Nat.mul_le_mul_left (2 * k) ht₂.2.le; omega
      have hlt2 : 2 * k * t₂' + r₂ < n := by
        have := Nat.mul_le_mul_left (2 * k) ht₂'.2.le; omega
      have hv := congrArg Fin.val heq
      simp only [val_natToFin, Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hv
      exact hne (nat_mul_add_icc_inj hr₁_mem hr₂_mem hv.symm).2
  let V_all : Finset (Fin n) := unblocked.biUnion V_r
  let U_unb : Finset (Idx n k) := V_all.biUnion (badEdgesAt hk hn x')
  have hVall_card : #V_all = #unblocked * C2 := by
    dsimp only [V_all]
    rw [card_biUnion hVr_disj, sum_congr rfl hVr_card, sum_const, smul_eq_mul]
  have hVall_bad : ∀ v ∈ V_all, isBad hk hn x' v := by
    intro v hv
    rcases mem_biUnion.mp hv with ⟨r, hr, hvr⟩
    exact hVr_bad r hr v hvr
  have hUunb_lb : (#unblocked * 10 ^ 15) * (3 * k ^ 2 / (2 * 10 ^ 9)) ≤ 88 * #U_unb := by
    rw [← hC2_eq, ← hVall_card]
    exact card_biUnion_badEdgesAt_ge hk hn x' V_all hVall_bad
  have hUunb_sub : U_unb ⊆ nonnegEdges hn x' := by
    intro e he
    rcases mem_biUnion.mp he with ⟨v, _, hev⟩
    exact badEdgesAt_subset_nonnegEdges hk hn x' v hev
  have hblk_prop : ∀ r ∈ blocked, ∃ t ∈ Ico 3 T_end, ∀ ij : Fin (k - 1) × Fin (k - 1),
      0 ≤ edgeSum hn x' (covEdge1 (natToFin (2 * k * t + r)) ij.1 ij.2) ∨
      0 ≤ edgeSum hn x' (covEdge2 (natToFin (2 * k * t + r)) ij.1 ij.2) := by
    intro r hr
    have hnot_unb : ¬ isUnblocked r := (mem_filter.mp hr).2
    dsimp only [isUnblocked, T_all] at hnot_unb
    push Not at hnot_unb
    rcases hnot_unb with ⟨t, ht, hij⟩
    refine ⟨t, ht, fun ij => ?_⟩
    by_cases h1 : 0 ≤ edgeSum hn x' (covEdge1 (natToFin (2 * k * t + r)) ij.1 ij.2)
    · exact Or.inl h1
    · exact Or.inr (hij ij (lt_of_not_ge h1))
  obtain ⟨U_blk, hUblk_sub, hUblk_lb, htower⟩ :=
    cover_blocked_and_tower hk hn x' hTend_bound hShift_bound blocked (filter_subset _ R_all) hblk_prop
  have hinter_per_r : ∀ r ∈ unblocked,
      #(((V_r r).biUnion (badEdgesAt hk hn x')) ∩ U_blk) ≤ 176 * k ^ 2 := by
    intro r hr
    have hr_mem : 1 ≤ r ∧ r ≤ 2 * k := mem_Icc.mp (mem_filter.mp hr).1
    dsimp only [V_r]
    split_ifs with hl
    · refine htower _ (r - 1) (by omega) fun v hv => ?_
      rcases mem_image.mp hv with ⟨t₁, ht₁, rfl⟩
      rw [mem_Ico] at ht₁
      exact ⟨t₁, mem_Ico.mpr ⟨ht₁.1, by omega⟩, by congr 1; omega⟩
    · refine htower _ r hr_mem.2 fun v hv => ?_
      rcases mem_image.mp hv with ⟨t₂, ht₂, rfl⟩
      rw [mem_Ico] at ht₂
      exact ⟨t₂, mem_Ico.mpr ⟨by omega, ht₂.2⟩, rfl⟩
  have hinter_ub : #(U_unb ∩ U_blk) ≤ #unblocked * (176 * k ^ 2) := by
    have hsub_inter : U_unb ∩ U_blk ⊆
        unblocked.biUnion (fun r => ((V_r r).biUnion (badEdgesAt hk hn x')) ∩ U_blk) := by
      intro e he
      rcases mem_inter.mp he with ⟨heU, heB⟩
      rcases mem_biUnion.mp heU with ⟨v, hv, hev⟩
      rcases mem_biUnion.mp hv with ⟨r, hr, hvr⟩
      exact mem_biUnion.mpr ⟨r, hr, mem_inter.mpr ⟨mem_biUnion.mpr ⟨v, hvr, hev⟩, heB⟩⟩
    calc #(U_unb ∩ U_blk)
      _ ≤ #(unblocked.biUnion (fun r => ((V_r r).biUnion (badEdgesAt hk hn x')) ∩ U_blk)) :=
        card_le_card hsub_inter
      _ ≤ ∑ r ∈ unblocked, #(((V_r r).biUnion (badEdgesAt hk hn x')) ∩ U_blk) :=
        card_biUnion_le
      _ ≤ ∑ _r ∈ unblocked, 176 * k ^ 2 := sum_le_sum hinter_per_r
      _ = #unblocked * (176 * k ^ 2) := by simp
  -- Final inclusion-exclusion contradiction
  have hunion_sub : U_blk ∪ U_unb ⊆ nonnegEdges hn x' :=
    union_subset hUblk_sub hUunb_sub
  have hunion_le : #(U_blk ∪ U_unb) ≤ #(nonnegEdges hn x') := card_le_card hunion_sub
  have hie := card_union_add_card_inter U_blk U_unb
  rw [inter_comm] at hie
  obtain ⟨B0, hB0_eq⟩ : ∃ B0, B0 = 3 * k ^ 2 / (2 * 10 ^ 9) := ⟨_, rfl⟩
  rw [← hB0_eq] at hUunb_lb
  have hB0_lb : k ^ 2 ≤ 10 ^ 9 * B0 := by
    have hdiv := Nat.div_add_mod (3 * k ^ 2) (2 * 10 ^ 9)
    rw [← hB0_eq] at hdiv
    have hmod : 3 * k ^ 2 % (2 * 10 ^ 9) < 2 * 10 ^ 9 := Nat.mod_lt _ (by positivity)
    have hk_sq : 2 * 10 ^ 9 < k ^ 2 := by nlinarith only [hk_large]
    linarith only [hdiv, hmod, hk_sq]
  have hUunb_strong : #unblocked * (177 * k ^ 2) ≤ #U_unb := by
    have h1 : #unblocked * (10 ^ 6 * k ^ 2) ≤ (#unblocked * 10 ^ 15) * B0 := by
      calc #unblocked * (10 ^ 6 * k ^ 2)
        _ = (#unblocked * 10 ^ 6) * k ^ 2 := by ring
        _ ≤ (#unblocked * 10 ^ 6) * (10 ^ 9 * B0) := Nat.mul_le_mul_left _ hB0_lb
        _ = (#unblocked * 10 ^ 15) * B0 := by ring
    have h2 : 88 * (#unblocked * (177 * k ^ 2)) ≤ #unblocked * (10 ^ 6 * k ^ 2) := by
      have hc : 88 * 177 ≤ 10 ^ 6 := by norm_num
      have hm := Nat.mul_le_mul_right (#unblocked * k ^ 2) hc
      have hr1 : 88 * 177 * (#unblocked * k ^ 2) = 88 * (#unblocked * (177 * k ^ 2)) := by ring
      have hr2 : 10 ^ 6 * (#unblocked * k ^ 2) = #unblocked * (10 ^ 6 * k ^ 2) := by ring
      linarith only [hm, hr1, hr2]
    have h3 : 88 * (#unblocked * (177 * k ^ 2)) ≤ 88 * #U_unb := h2.trans (h1.trans hUunb_lb)
    linarith only [h3]
  have hnet_unb : #unblocked * (k - 1) ^ 2 + #(U_unb ∩ U_blk) ≤ #U_unb := by
    have hk1_sq : (k - 1) ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left (Nat.sub_le k 1) 2
    have h1 : #unblocked * (k - 1) ^ 2 ≤ #unblocked * k ^ 2 := Nat.mul_le_mul_left _ hk1_sq
    have hr : #unblocked * (177 * k ^ 2) = #unblocked * k ^ 2 + #unblocked * (176 * k ^ 2) := by ring
    linarith only [h1, hr, hUunb_strong, hinter_ub]
  have htotal : 2 * (k * (k - 1) ^ 2) ≤ 2 * #(U_blk ∪ U_unb) := by
    have hsum_parts : (#unblocked + #blocked) * (k - 1) ^ 2 =
        #unblocked * (k - 1) ^ 2 + #blocked * (k - 1) ^ 2 := by ring
    rw [hpart_card] at hsum_parts
    have hr : 2 * k * (k - 1) ^ 2 = 2 * (k * (k - 1) ^ 2) := by ring
    have h0_unb : 0 ≤ #unblocked * (k - 1) ^ 2 := Nat.zero_le _
    linarith only [hsum_parts, hr, hnet_unb, hUblk_lb, hie, h0_unb]
  linarith only [htotal, hunion_le, h_few']

end PokrovskiyCover

namespace PokrovskiyTransverse
open Finset PokrovskiyHypergraph PokrovskiyCover PokrovskiyAddComb

open Classical

/- Section 1: Good vertices have an interior all-negative `bundlePlus` -/

lemma card_interiorPairs_ge {k : ℕ} (hk : 4 ≤ k) :
    (k - 3) ^ 2 ≤ #(univ.filter (fun ij : Fin (k - 1) × Fin (k - 1) => isInterior k ij.1 ij.2)) := by
  let U : Finset (Fin (k - 1) × Fin (k - 1)) := univ
  let IntP := U.filter (fun ij => isInterior k ij.1 ij.2)
  let BadP := U.filter (fun ij => ¬ isInterior k ij.1 ij.2)
  have hpart : #IntP + #BadP = (k - 1) ^ 2 := by
    have h1 := card_filter_add_not U (fun ij => isInterior k ij.1 ij.2)
    have h2 : #U = (k - 1) ^ 2 := by simp [U, pow_two]
    dsimp only [IntP, BadP]
    omega
  let B₁ : Finset (Fin (k - 1) × Fin (k - 1)) :=
    (univ : Finset (Fin (k - 1))).image (fun j₀ => (⟨0, by omega⟩, j₀))
  let B₂ : Finset (Fin (k - 1) × Fin (k - 1)) :=
    (univ : Finset (Fin (k - 1))).image (fun i₀ => (i₀, ⟨k - 2 - i₀.val, by have := i₀.isLt; omega⟩))
  have hBad_sub : BadP ⊆ B₁ ∪ B₂ := by
    intro ⟨i₀, j₀⟩ h
    have hnot_int : ¬ isInterior k i₀ j₀ := (mem_filter.mp h).2
    unfold isInterior at hnot_int
    have hi : i₀.val < k - 1 := i₀.isLt
    have hj : j₀.val < k - 1 := j₀.isLt
    by_cases hsum : (i₀.val + 1) + (j₀.val + 1) = k
    · refine mem_union_right _ (mem_image.mpr ⟨i₀, mem_univ _, ?_⟩)
      ext
      · simp
      · simp; omega
    · have hlt_not : (i₀.val + 1) + (j₀.val + 1) < k ∧ ¬ (2 ≤ i₀.val + 1) := by
        by_contra hnot
        apply hnot_int
        refine ⟨hsum, fun hlt => ?_⟩
        by_contra hn2
        exact hnot ⟨hlt, hn2⟩
      have hi0 : i₀.val = 0 := by omega
      refine mem_union_left _ (mem_image.mpr ⟨j₀, mem_univ _, ?_⟩)
      ext <;> simp [hi0]
  have hB₁_le : #B₁ ≤ k - 1 := card_image_le.trans (by simp)
  have hB₂_le : #B₂ ≤ k - 1 := card_image_le.trans (by simp)
  have hBad_le : #BadP ≤ 2 * (k - 1) := by
    have := (card_le_card hBad_sub).trans (card_union_le B₁ B₂)
    omega
  have hcalc : (k - 3) ^ 2 + 2 * (k - 1) ≤ (k - 1) ^ 2 := by
    zify [show 3 ≤ k by omega, show 1 ≤ k by omega]
    nlinarith
  linarith

lemma card_pairs_containing_plus_le {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (v : Fin n) (e : Idx n k) :
    #(univ.filter (fun ij : Fin (k - 1) × Fin (k - 1) => e ∈ bundlePlus v ij.1 ij.2)) ≤ 88 := by
  let P := univ.filter (fun ij : Fin (k - 1) × Fin (k - 1) => e ∈ bundlePlus v ij.1 ij.2)
  let T := univ.filter (fun p : Idx n k => e ∈ bundlePlus p.1 p.2.1 p.2.2 ∪
    bundleMinus hk p.1 p.2.1 p.2.2)
  have hinj : ∀ ij₁ ∈ P, ∀ ij₂ ∈ P, (v, ij₁) = (v, ij₂) → ij₁ = ij₂ := by
    intro _ _ _ _ h; exact (Prod.mk.inj h).2
  have hmaps : ∀ ij ∈ P, (v, ij) ∈ T := by
    intro ij hij
    simp only [P, T, mem_filter, mem_univ, true_and, mem_union] at hij ⊢
    exact Or.inl hij
  exact (card_le_card_of_injOn (fun ij => (v, ij)) hmaps (fun _ h1 _ h2 h => hinj _ h1 _ h2 h)).trans
    (card_triples_containing_le hk e)

lemma exists_interior_all_neg {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hk_large : 10 ^ 45 < k)
    (hn : 2 * k ≤ n) (z : Fin n → ℝ) (v : Fin n) (hv : isGood hk hn z v) :
    ∃ i₀ j₀ : Fin (k - 1), isInterior k i₀ j₀ ∧
      ∀ e ∈ bundlePlus v i₀ j₀, edgeSum hn z e < 0 := by
  by_contra hno
  push Not at hno
  let IntP := univ.filter (fun ij : Fin (k - 1) × Fin (k - 1) => isInterior k ij.1 ij.2)
  have hex : ∀ ij ∈ IntP, ∃ e : Idx n k,
      e ∈ badEdgesAt hk hn z v ∧ e ∈ bundlePlus v ij.1 ij.2 := by
    intro ij hij
    have hint : isInterior k ij.1 ij.2 := (mem_filter.mp hij).2
    obtain ⟨e, he_in, he_ge⟩ := hno ij.1 ij.2 hint
    have he_bun : e ∈ bundle hk v := by
      unfold bundle
      exact mem_biUnion.mpr ⟨ij, mem_univ _, mem_union_left _ he_in⟩
    exact ⟨e, mem_filter.mpr ⟨he_bun, he_ge⟩, he_in⟩
  have hInt_le : #IntP ≤ 88 * #(badEdgesAt hk hn z v) := by
    let B := badEdgesAt hk hn z v
    have hcov : IntP ⊆ B.biUnion (fun e => univ.filter (fun ij : Fin (k - 1) × Fin (k - 1) =>
        e ∈ bundlePlus v ij.1 ij.2)) := by
      intro ij hij
      obtain ⟨e, heB, heP⟩ := hex ij hij
      exact mem_biUnion.mpr ⟨e, heB, mem_filter.mpr ⟨mem_univ _, heP⟩⟩
    calc #IntP
      _ ≤ #(B.biUnion (fun e => univ.filter (fun ij : Fin (k - 1) × Fin (k - 1) =>
          e ∈ bundlePlus v ij.1 ij.2))) := card_le_card hcov
      _ ≤ ∑ e ∈ B, #(univ.filter (fun ij : Fin (k - 1) × Fin (k - 1) =>
          e ∈ bundlePlus v ij.1 ij.2)) := card_biUnion_le
      _ ≤ ∑ _e ∈ B, 88 := sum_le_sum fun e _ => card_pairs_containing_plus_le hk v e
      _ = 88 * #B := by simp [mul_comm]
  have hInt_ge := card_interiorPairs_ge (k := k) (by omega)
  have hv_lt : #(badEdgesAt hk hn z v) < 3 * k ^ 2 / (2 * 10 ^ 9) := not_le.mp hv
  have hB0_ub : 2 * 10 ^ 9 * (3 * k ^ 2 / (2 * 10 ^ 9)) ≤ 3 * k ^ 2 :=
    Nat.mul_div_le (3 * k ^ 2) (2 * 10 ^ 9)
  have hquad : 2 * 10 ^ 9 * (k - 3) ^ 2 > 88 * (3 * k ^ 2) := by
    zify [show 3 ≤ k by omega]
    nlinarith only [hk_large]
  have hmul := Nat.mul_le_mul_left (2 * 10 ^ 9) (hInt_ge.trans hInt_le)
  have hmul2 := Nat.mul_le_mul_left 88 (Nat.mul_le_mul_left (2 * 10 ^ 9) hv_lt.le)
  have hr : 88 * (2 * 10 ^ 9 * #(badEdgesAt hk hn z v)) =
      2 * 10 ^ 9 * (88 * #(badEdgesAt hk hn z v)) := by ring
  have hr2 : 88 * (2 * 10 ^ 9 * (3 * k ^ 2 / (2 * 10 ^ 9))) ≤ 88 * (3 * k ^ 2) :=
    Nat.mul_le_mul_left 88 hB0_ub
  linarith only [hmul, hmul2, hr, hr2, hquad]

lemma good_intSum_neg_234 {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hk_large : 10 ^ 45 < k)
    (hn : 2 * k ≤ n) (hn5 : 5 * k ≤ n)
    (z : Fin n → ℝ) (v : Fin n) (hv : isGood hk hn z v) :
    intSum z v (2 * k) < 0 ∧ intSum z v (3 * k) < 0 ∧ intSum z v (4 * k) < 0 := by
  obtain ⟨i₀, j₀, hint, hall⟩ := exists_interior_all_neg hk hk_large hn z v hv
  exact ⟨intSum_twoK_neg hn5 hall, intSum_threeK_neg hn5 hint hall, intSum_fourK_neg hn5 hall⟩

/- Section 2: `Rset`, `basicR`, and propagation -/

noncomputable def Rset {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hn : 2 * k ≤ n) (z : Fin n → ℝ) (m v : ℕ) :
    Finset ℕ :=
  (Icc (v + 1) m).filter (fun u => intSum z (natToFin v) (u - v) < 0 ∧ isGood hk hn z (natToFin u))

lemma Rset_trans {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hn : 2 * k ≤ n) (z : Fin n → ℝ)
    {m : ℕ} (hm_n : m + 1 ≤ n) {v u w : ℕ}
    (hu : u ∈ Rset hk hn z m v) (hw : w ∈ Rset hk hn z m u) :
    w ∈ Rset hk hn z m v := by
  simp only [Rset, mem_filter, mem_Icc] at hu hw ⊢
  rcases hu with ⟨⟨hvu, _⟩, hsum_vu, _⟩
  rcases hw with ⟨⟨huw, hwm⟩, hsum_uw, hgw⟩
  refine ⟨⟨by omega, hwm⟩, ?_, hgw⟩
  have hlen : w - v = (u - v) + (w - u) := by omega
  have hvu_eq : natToFin v + natToFin (u - v) = (natToFin u : Fin n) := by
    rw [← natToFin_add, show v + (u - v) = u by omega]
  rw [hlen, intSum_add z (natToFin v) (by omega), hvu_eq]
  linarith

lemma Rset_step_twoK {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hk_large : 10 ^ 45 < k)
    (hn : 2 * k ≤ n) (hn5 : 5 * k ≤ n)
    (z : Fin n → ℝ) {m : ℕ} (hm_n : m + 1 ≤ n) {v u : ℕ}
    (hu : u ∈ Rset hk hn z m v)
    (hum : u + 2 * k ≤ m)
    (hg : isGood hk hn z (natToFin (u + 2 * k))) :
    u + 2 * k ∈ Rset hk hn z m v := by
  simp only [Rset, mem_filter, mem_Icc] at hu ⊢
  rcases hu with ⟨⟨hvu, _⟩, hsum_vu, hgu⟩
  refine ⟨⟨by omega, hum⟩, ?_, hg⟩
  have h2k := (good_intSum_neg_234 hk hk_large hn hn5 z (natToFin u) hgu).1
  have hlen : u + 2 * k - v = (u - v) + 2 * k := by omega
  have hvu_eq : natToFin v + natToFin (u - v) = (natToFin u : Fin n) := by
    rw [← natToFin_add, show v + (u - v) = u by omega]
  rw [hlen, intSum_add z (natToFin v) (by omega), hvu_eq]
  linarith

lemma Rset_step_threeK {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hk_large : 10 ^ 45 < k)
    (hn : 2 * k ≤ n) (hn5 : 5 * k ≤ n)
    (z : Fin n → ℝ) {m : ℕ} (hm_n : m + 1 ≤ n) {v u : ℕ}
    (hu : u ∈ Rset hk hn z m v)
    (hum : u + 3 * k ≤ m)
    (hg : isGood hk hn z (natToFin (u + 3 * k))) :
    u + 3 * k ∈ Rset hk hn z m v := by
  simp only [Rset, mem_filter, mem_Icc] at hu ⊢
  rcases hu with ⟨⟨hvu, _⟩, hsum_vu, hgu⟩
  refine ⟨⟨by omega, hum⟩, ?_, hg⟩
  have h3k := (good_intSum_neg_234 hk hk_large hn hn5 z (natToFin u) hgu).2.1
  have hlen : u + 3 * k - v = (u - v) + 3 * k := by omega
  have hvu_eq : natToFin v + natToFin (u - v) = (natToFin u : Fin n) := by
    rw [← natToFin_add, show v + (u - v) = u by omega]
  rw [hlen, intSum_add z (natToFin v) (by omega), hvu_eq]
  linarith

lemma card_filter_shift_bad_le {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hn : 2 * k ≤ n)
    (z : Fin n → ℝ) {m B1 : ℕ}
    (hz_sparse : ∀ u : ℕ, u + k ≤ m + 1 →
      #((Ico u (u + k)).filter (fun p => isBad hk hn z (natToFin p))) ≤ B1)
    {X : Finset ℕ} {u₀ sh : ℕ}
    (hX : X ⊆ Ico u₀ (u₀ + k))
    (hub : u₀ + sh + k ≤ m + 1) :
    #(X.filter (fun x => isBad hk hn z (natToFin (x + sh)))) ≤ B1 := by
  let S_src := X.filter (fun x => isBad hk hn z (natToFin (x + sh)))
  let S_dst := (Ico (u₀ + sh) (u₀ + sh + k)).filter (fun p => isBad hk hn z (natToFin p))
  have hinj : Set.InjOn (fun x => x + sh) S_src :=
    fun _ _ _ _ h => Nat.add_right_cancel h
  have hmaps : Set.MapsTo (fun x => x + sh) S_src S_dst := by
    intro x hx
    rw [mem_coe] at hx ⊢
    rcases mem_filter.mp hx with ⟨hxX, hxB⟩
    have hxI := mem_Ico.mp (hX hxX)
    dsimp only
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, hxB⟩
  exact (card_le_card_of_injOn _ hmaps hinj).trans (hz_sparse (u₀ + sh) hub)

lemma propagate_R0_steps {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hk_large : 10 ^ 45 < k)
    (hn : 2 * k ≤ n) (hn5 : 5 * k ≤ n)
    (z : Fin n → ℝ) {m B1 : ℕ} (hm_n : m + 1 ≤ n)
    (hz_sparse : ∀ u : ℕ, u + k ≤ m + 1 →
      #((Ico u (u + k)).filter (fun p => isBad hk hn z (natToFin p))) ≤ B1) :
    ∀ {d : ℕ}, 2 ≤ d → 16 * k + (d + 2) * k ≤ m + 1 →
      ∃ Xd ⊆ Ico (16 * k) (17 * k),
        #(Rset hk hn z m 0 ∩ Ico (16 * k) (17 * k)) ≤ #Xd + (d + 1) * B1 ∧
        ∀ x ∈ Xd, x + d * k ∈ Rset hk hn z m 0 ∧
          x + (d + 1) * k ∈ Rset hk hn z m 0
  | 0, hd, _ => by omega
  | 1, hd, _ => by omega
  | 2, _, hub => by
    let X₀ := Rset hk hn z m 0 ∩ Ico (16 * k) (17 * k)
    let X₂ := X₀.filter (fun x =>
      isGood hk hn z (natToFin (x + 2 * k)) ∧ isGood hk hn z (natToFin (x + 3 * k)))
    refine ⟨X₂, (filter_subset _ X₀).trans inter_subset_right, ?_, ?_⟩
    · have hsub : X₀ \ X₂ ⊆
          X₀.filter (fun x => isBad hk hn z (natToFin (x + 2 * k))) ∪
          X₀.filter (fun x => isBad hk hn z (natToFin (x + 3 * k))) := by
        intro x hx
        rcases mem_sdiff.mp hx with ⟨hx0, hx_not⟩
        have hbad_or : isBad hk hn z (natToFin (x + 2 * k)) ∨
            isBad hk hn z (natToFin (x + 3 * k)) := by
          by_contra hnb
          push Not at hnb
          exact hx_not (mem_filter.mpr ⟨hx0, hnb⟩)
        exact hbad_or.imp
          (fun h => mem_filter.mpr ⟨hx0, h⟩)
          (fun h => mem_filter.mpr ⟨hx0, h⟩) |> mem_union.mpr
      have hX₀_ico : X₀ ⊆ Ico (16 * k) (16 * k + k) := by
        rw [show 16 * k + k = 17 * k by omega]
        exact inter_subset_right
      have hb1 := card_filter_shift_bad_le hk hn z hz_sparse hX₀_ico (sh := 2 * k) (by omega)
      have hb2 := card_filter_shift_bad_le hk hn z hz_sparse hX₀_ico (sh := 3 * k) (by omega)
      have hX₂_sub : X₂ ⊆ X₀ := filter_subset _ X₀
      have hsd := card_sdiff_add_card_eq_card hX₂_sub
      have hun := (card_le_card hsub).trans (card_union_le _ _)
      linarith only [hsd, hun, hb1, hb2]
    · intro x hx
      rcases mem_filter.mp hx with ⟨hx0, hg2, hg3⟩
      rcases mem_inter.mp hx0 with ⟨hxR, hxI⟩
      have hxhi := (mem_Ico.mp hxI).2
      exact ⟨Rset_step_twoK hk hk_large hn hn5 z hm_n hxR (by omega) hg2,
             Rset_step_threeK hk hk_large hn hn5 z hm_n hxR (by omega) hg3⟩
  | d + 3, _, hub => by
    have hub_prev : 16 * k + (d + 2 + 2) * k ≤ m + 1 := by
      have : (d + 3 + 2) * k = (d + 2 + 2) * k + k := by ring
      omega
    obtain ⟨Xd, hXd_sub, hXd_card, hXd_mem⟩ :=
      propagate_R0_steps hk hk_large hn hn5 z hm_n hz_sparse (d := d + 2) (by omega) hub_prev
    let Xnext := Xd.filter (fun x => isGood hk hn z (natToFin (x + (d + 4) * k)))
    have hXnext_sub : Xnext ⊆ Xd := filter_subset _ Xd
    refine ⟨Xnext, hXnext_sub.trans hXd_sub, ?_, ?_⟩
    · have hbad : Xd \ Xnext = Xd.filter (fun x => isBad hk hn z (natToFin (x + (d + 4) * k))) := by
        ext x
        constructor
        · intro hx
          rcases mem_sdiff.mp hx with ⟨hx1, hx2⟩
          exact mem_filter.mpr ⟨hx1, by by_contra h; exact hx2 (mem_filter.mpr ⟨hx1, h⟩)⟩
        · intro hx
          rcases mem_filter.mp hx with ⟨hx1, hx2⟩
          exact mem_sdiff.mpr ⟨hx1, fun h => (mem_filter.mp h).2 hx2⟩
      have hXd_ico : Xd ⊆ Ico (16 * k) (16 * k + k) := by
        rwa [show 16 * k + k = 17 * k by omega]
      have hb := card_filter_shift_bad_le hk hn z hz_sparse hXd_ico (sh := (d + 4) * k)
        (by
          have : 16 * k + (d + 4) * k + k = 16 * k + (d + 3 + 2) * k := by ring
          omega)
      have hsd := card_sdiff_add_card_eq_card hXnext_sub
      rw [hbad] at hsd
      have hring : (d + 3 + 1) * B1 = (d + 2 + 1) * B1 + B1 := by ring
      linarith only [hXd_card, hsd, hb, hring]
    · intro x hx
      rcases mem_filter.mp hx with ⟨hxXd, hg4⟩
      obtain ⟨hR_d2, hR_d3⟩ := hXd_mem x hxXd
      refine ⟨hR_d3, ?_⟩
      have hx_lt : x < 17 * k := (mem_Ico.mp (hXd_sub hxXd)).2
      have hsum_eq : x + (d + 4) * k = (x + (d + 2) * k) + 2 * k := by ring
      have hum : (x + (d + 2) * k) + 2 * k ≤ m := by
        have h1 : 17 * k + (d + 4) * k = 16 * k + (d + 3 + 2) * k := by ring
        omega
      rw [hsum_eq] at hg4 ⊢
      exact Rset_step_twoK hk hk_large hn hn5 z hm_n hR_d2 hum hg4

lemma propagate_R0_window {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hk_large : 10 ^ 45 < k)
    (hn : 2 * k ≤ n) (hn5 : 5 * k ≤ n)
    (z : Fin n → ℝ) {m B1 : ℕ} (hm_n : m + 1 ≤ n)
    (hz_sparse : ∀ u : ℕ, u + k ≤ m + 1 →
      #((Ico u (u + k)).filter (fun p => isBad hk hn z (natToFin p))) ≤ B1)
    {v₀ : ℕ} (hv₀_lb : 18 * k ≤ v₀) (hv₀_ub : v₀ + 2 * k ≤ m + 1) :
    #(Rset hk hn z m 0 ∩ Ico (16 * k) (17 * k)) ≤
      #(Rset hk hn z m 0 ∩ Ico v₀ (v₀ + k)) + ((v₀ - 16 * k) / k + 1) * B1 := by
  obtain ⟨q, hq_eq⟩ : ∃ q, q = (v₀ - 16 * k) / k := ⟨_, rfl⟩
  rw [← hq_eq]
  have hq_ge : 2 ≤ q := by
    have h1 : 2 * k ≤ v₀ - 16 * k := by omega
    rw [hq_eq]
    exact (Nat.le_div_iff_mul_le (by omega : 0 < k)).mpr h1
  have hqk_le : 16 * k + q * k ≤ v₀ := by
    have := hq_eq ▸ Nat.mul_div_le (v₀ - 16 * k) k
    have hr : k * q = q * k := by ring
    omega
  have hqk_gt : v₀ < 16 * k + (q + 1) * k := by
    have hpos : 0 < k := by omega
    have := hq_eq ▸ Nat.lt_mul_div_succ (v₀ - 16 * k) hpos
    have hr : k * (q + 1) = (q + 1) * k := by ring
    omega
  have hub_q : 16 * k + (q + 2) * k ≤ m + 1 := by
    have : 16 * k + (q + 2) * k = (16 * k + q * k) + 2 * k := by ring
    linarith only [hqk_le, hv₀_ub, this]
  obtain ⟨Xq, hXq_sub, hXq_card, hXq_mem⟩ :=
    propagate_R0_steps hk hk_large hn hn5 z hm_n hz_sparse hq_ge hub_q
  let f (x : ℕ) : ℕ := if v₀ ≤ x + q * k then x + q * k else x + (q + 1) * k
  let Target : Finset ℕ := Rset hk hn z m 0 ∩ Ico v₀ (v₀ + k)
  have hmaps : Set.MapsTo f Xq Target := by
    intro x hx
    rw [mem_coe] at hx ⊢
    have hxI := mem_Ico.mp (hXq_sub hx)
    obtain ⟨h1, h2⟩ := hXq_mem x hx
    dsimp only [f, Target]
    split_ifs with hge
    · refine mem_inter.mpr ⟨h1, mem_Ico.mpr ⟨hge, ?_⟩⟩
      have : 17 * k + q * k = (16 * k + q * k) + k := by ring
      linarith
    · refine mem_inter.mpr ⟨h2, mem_Ico.mpr ⟨?_, ?_⟩⟩
      · have : (q + 1) * k = q * k + k := by ring
        omega
      · have : (q + 1) * k = q * k + k := by ring
        omega
  have hinj : Set.InjOn f Xq := by
    intro x₁ hx₁ x₂ hx₂ heq
    rw [mem_coe] at hx₁ hx₂
    have h1 := mem_Ico.mp (hXq_sub hx₁)
    have h2 := mem_Ico.mp (hXq_sub hx₂)
    dsimp only [f] at heq
    have hk_expand : (q + 1) * k = q * k + k := by ring
    split_ifs at heq <;> omega
  have hXq_le : #Xq ≤ #Target :=
    card_le_card_of_injOn f hmaps hinj
  dsimp only [Target] at hXq_le
  linarith only [hXq_card, hXq_le]

/- Section 3: `Qset`, `basicQ`, `firstpower`, and `Qsumset` -/

noncomputable def Qlt {n : ℕ} [NeZero n] (k : ℕ) (z : Fin n → ℝ) (v thr : ℕ) : Finset ℕ :=
  (Icc 1 (k - 1)).filter (fun j =>
    thr ≤ #((Icc 1 (k - 1)).filter (fun i => intSum z (natToFin (v + i)) j < 0)))

noncomputable def Qge {n : ℕ} [NeZero n] (k : ℕ) (z : Fin n → ℝ) (v thr : ℕ) : Finset ℕ :=
  (Icc 1 (k - 1)).filter (fun j' =>
    thr ≤ #((Icc 1 (k - 1)).filter (fun i => 0 ≤ intSum z (natToFin (v + i)) (k - j'))))

noncomputable def Qset {n : ℕ} [NeZero n] (k : ℕ) (z : Fin n → ℝ) (v thr : ℕ) : Finset ℕ :=
  Qlt k z v thr ∪ Qge k z v thr ∪ {0}

lemma Qset_subset_range {n k : ℕ} [NeZero n] (hk : 1 ≤ k) (z : Fin n → ℝ) (v thr : ℕ) :
    Qset k z v thr ⊆ range k := by
  intro j hj
  simp only [Qset, Qlt, Qge, mem_union, mem_filter, mem_Icc, mem_singleton, mem_range] at hj ⊢
  rcases hj with (⟨⟨_, h⟩, _⟩ | ⟨⟨_, h⟩, _⟩) | rfl <;> omega

lemma natCast_injOn_range_k {k : ℕ} [NeZero k] :
    Set.InjOn (fun j : ℕ => (j : ZMod k)) (range k) := by
  intro j₁ hj₁ j₂ hj₂ heq
  rw [mem_coe, mem_range] at hj₁ hj₂
  have hv := congrArg ZMod.val heq
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hj₁, Nat.mod_eq_of_lt hj₂] at hv
  exact hv

lemma Qset_image_antisymm {n k : ℕ} [NeZero n] [NeZero k] (hk : 2 ≤ k)
    (z : Fin n → ℝ) (v thr : ℕ) (hthr : 2 * thr ≤ k - 1) :
    ∀ x : ZMod k,
      x ∈ (Qset k z v thr).image (fun j : ℕ => (j : ZMod k)) ∨
      -x ∈ (Qset k z v thr).image (fun j : ℕ => (j : ZMod k)) := by
  intro x
  let j := x.val
  have hj_lt : j < k := ZMod.val_lt x
  have hx_eq : (j : ZMod k) = x := ZMod.natCast_zmod_val x
  by_cases hj0 : j = 0
  · refine Or.inl (mem_image.mpr ⟨0, ?_, by rw [← hx_eq, hj0]⟩)
    simp [Qset]
  · have hj_mem : j ∈ Icc 1 (k - 1) := mem_Icc.mpr ⟨by omega, by omega⟩
    let S_lt := (Icc 1 (k - 1)).filter (fun i => intSum z (natToFin (v + i)) j < 0)
    let S_ge := (Icc 1 (k - 1)).filter (fun i => ¬ intSum z (natToFin (v + i)) j < 0)
    have hsum : #S_lt + #S_ge = k - 1 := by
      have h1 := card_filter_add_not (Icc 1 (k - 1))
        (fun i => intSum z (natToFin (v + i)) j < 0)
      have h2 : #(Icc 1 (k - 1)) = k - 1 := by simp
      dsimp only [S_lt, S_ge]
      omega
    by_cases hlt : thr ≤ #S_lt
    · refine Or.inl (mem_image.mpr ⟨j, ?_, hx_eq⟩)
      exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hj_mem, hlt⟩))
    · have hge : thr ≤ #S_ge := by omega
      refine Or.inr (mem_image.mpr ⟨k - j, ?_, ?_⟩)
      · refine mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩))
        have hkj : k - (k - j) = j := by omega
        rw [hkj]
        have hS_eq : S_ge = (Icc 1 (k - 1)).filter (fun i => 0 ≤ intSum z (natToFin (v + i)) j) := by
          ext i; simp [S_ge, not_lt]
        rwa [← hS_eq]
      · have hadd : ((k - j : ℕ) : ZMod k) + (j : ZMod k) = 0 := by
          rw [← Nat.cast_add, show k - j + j = k by omega, ZMod.natCast_self]
        rw [hx_eq] at hadd
        exact eq_neg_of_add_eq_zero_left hadd

lemma Qset_sevenK_subset {n k : ℕ} [NeZero n] (hk_large : 10 ^ 45 < k)
    (z : Fin n → ℝ) {a : ℕ} (ha : a < k) :
    Qset k z (7 * k) (9 * k / 20) ⊆
      Qset k z (a + 6 * k) (k / 5) ∪ Qset k z (a + 7 * k) (k / 5) := by
  have hthr_gap : 2 * (k / 5) + 1 < 9 * k / 20 := by
    have hd1 := Nat.div_add_mod (9 * k) 20
    have hm1 : 9 * k % 20 < 20 := Nat.mod_lt _ (by positivity)
    have hd2 : 5 * (k / 5) ≤ k := Nat.mul_div_le k 5
    linarith only [hd1, hm1, hd2, hk_large]
  have hsplit_idx : ∀ P : ℕ → Prop,
      9 * k / 20 ≤ #((Icc 1 (k - 1)).filter (fun i => P (7 * k + i))) →
      k / 5 ≤ #((Icc 1 (k - 1)).filter (fun i => P (a + 6 * k + i))) ∨
      k / 5 ≤ #((Icc 1 (k - 1)).filter (fun i => P (a + 7 * k + i))) := by
    intro P hbig
    let Big := (Icc 1 (k - 1)).filter (fun i => P (7 * k + i))
    let L1 := Big.filter (fun i => i < a)
    let Lmid := Big.filter (fun i => i = a)
    let L2 := Big.filter (fun i => a < i)
    have hBig_sub : Big ⊆ L1 ∪ Lmid ∪ L2 := by
      intro i hi
      rcases lt_trichotomy i a with h1 | h2 | h3
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hi, h1⟩))
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hi, h2⟩))
      · exact mem_union_right _ (mem_filter.mpr ⟨hi, h3⟩)
    have hLmid_le : #Lmid ≤ 1 := by
      refine card_le_one.mpr fun x hx y hy => ?_
      exact (mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm
    have hL1_le : #L1 ≤ #((Icc 1 (k - 1)).filter (fun i' => P (a + 6 * k + i'))) := by
      refine card_le_card_of_injOn (fun i => k + i - a) ?_ ?_
      · intro i hi
        rw [mem_coe] at hi ⊢
        rcases mem_filter.mp hi with ⟨hiB, hia⟩
        rcases mem_filter.mp hiB with ⟨hiIcc, hiP⟩
        have hiI := mem_Icc.mp hiIcc
        dsimp only
        refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
        have heq : a + 6 * k + (k + i - a) = 7 * k + i := by omega
        rwa [heq]
      · intro i₁ h₁ i₂ h₂ heq
        rw [mem_coe] at h₁ h₂
        have hia₁ : i₁ < a := (mem_filter.mp h₁).2
        have hia₂ : i₂ < a := (mem_filter.mp h₂).2
        dsimp only at heq
        omega
    have hL2_le : #L2 ≤ #((Icc 1 (k - 1)).filter (fun i' => P (a + 7 * k + i'))) := by
      refine card_le_card_of_injOn (fun i => i - a) ?_ ?_
      · intro i hi
        rw [mem_coe] at hi ⊢
        rcases mem_filter.mp hi with ⟨hiB, hai⟩
        rcases mem_filter.mp hiB with ⟨hiIcc, hiP⟩
        have hiI := mem_Icc.mp hiIcc
        dsimp only
        refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
        have heq : a + 7 * k + (i - a) = 7 * k + i := by omega
        rwa [heq]
      · intro i₁ h₁ i₂ h₂ heq
        rw [mem_coe] at h₁ h₂
        have hai₁ : a < i₁ := (mem_filter.mp h₁).2
        have hai₂ : a < i₂ := (mem_filter.mp h₂).2
        dsimp only at heq
        omega
    have hun1 := (card_le_card hBig_sub).trans (card_union_le _ _)
    have hun2 := card_union_le L1 Lmid
    by_contra hnot
    push Not at hnot
    dsimp only [Big] at hun1
    linarith only [hbig, hun1, hun2, hLmid_le, hL1_le, hL2_le, hnot.1, hnot.2, hthr_gap]
  intro j hj
  simp only [Qset, mem_union, mem_singleton] at hj ⊢
  rcases hj with (hj_lt | hj_ge) | rfl
  · simp only [Qlt, mem_filter] at hj_lt
    rcases hsplit_idx (fun u => intSum z (natToFin u) j < 0) hj_lt.2 with h1 | h2
    · exact Or.inl (Or.inl (Or.inl (mem_filter.mpr ⟨hj_lt.1, h1⟩)))
    · exact Or.inr (Or.inl (Or.inl (mem_filter.mpr ⟨hj_lt.1, h2⟩)))
  · simp only [Qge, mem_filter] at hj_ge
    rcases hsplit_idx (fun u => 0 ≤ intSum z (natToFin u) (k - j)) hj_ge.2 with h1 | h2
    · exact Or.inl (Or.inl (Or.inr (mem_filter.mpr ⟨hj_ge.1, h1⟩)))
    · exact Or.inr (Or.inl (Or.inr (mem_filter.mpr ⟨hj_ge.1, h2⟩)))
  · exact Or.inl (Or.inr rfl)

/-- Claim 5.5 (`firstpower`): for a good vertex `v` with `v + 5 * k ≤ m + 1`, most of
`Qset k z v (k / 5)` lands in `Rset` after shifting by `v + 4 * k`. -/
lemma exists_Q_shift_fourK {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hk_large : 10 ^ 45 < k)
    (hn : 2 * k ≤ n) (hn5 : 5 * k ≤ n)
    (z : Fin n → ℝ) {m B1 : ℕ} (_hm_n : m + 1 ≤ n)
    (hz_sparse : ∀ u : ℕ, u + k ≤ m + 1 →
      #((Ico u (u + k)).filter (fun p => isBad hk hn z (natToFin p))) ≤ B1)
    (hB1_ub : B1 ≤ k / (5 * 10 ^ 18))
    {v : ℕ} (hv_ub : v + 5 * k ≤ m + 1)
    (hv_good : isGood hk hn z (natToFin v)) :
    ∃ Q' ⊆ Qset k z v (k / 5),
      #(Qset k z v (k / 5)) ≤ #Q' + 3 * k / (2 * 10 ^ 6) ∧
      ∀ j' ∈ Q', v + 4 * k + j' ∈ Rset hk hn z m v := by
  let vf : Fin n := natToFin v
  let hasBadPlus (i j : ℕ) : Prop :=
    ∃ hi : i - 1 < k - 1, ∃ hj : j - 1 < k - 1,
      ∃ e ∈ bundlePlus vf ⟨i - 1, hi⟩ ⟨j - 1, hj⟩, 0 ≤ edgeSum hn z e
  let T_bad : Finset ℕ := (Icc 1 (k - 1)).filter (fun j =>
    19 * k / 100 ≤ #((Icc 1 (k - 1)).filter (fun i => hasBadPlus i j)))
  -- Bound #T_bad using goodness of vf
  have hT_card_mul : #T_bad * (19 * k / 100) ≤ 88 * #(badEdgesAt hk hn z vf) := by
    let Pairs := T_bad.biUnion (fun j =>
      ((Icc 1 (k - 1)).filter (fun i => hasBadPlus i j)).image (fun i => (i, j)))
    have hP_lb : #T_bad * (19 * k / 100) ≤ #Pairs := by
      dsimp only [Pairs]
      rw [card_biUnion]
      · calc #T_bad * (19 * k / 100)
          _ = ∑ _j ∈ T_bad, (19 * k / 100) := by simp
          _ ≤ ∑ j ∈ T_bad, #(((Icc 1 (k - 1)).filter (fun i => hasBadPlus i j)).image (fun i => (i, j))) := by
            refine sum_le_sum fun j hj => ?_
            rw [card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)]
            exact (mem_filter.mp hj).2
      · intro j₁ _ j₂ _ hne
        rw [Function.onFun, disjoint_left]
        intro p hp1 hp2
        rcases mem_image.mp hp1 with ⟨_, _, rfl⟩
        rcases mem_image.mp hp2 with ⟨_, _, heq⟩
        exact hne (Prod.mk.inj heq).2.symm
    let B := badEdgesAt hk hn z vf
    have hP_ub : #Pairs ≤ 88 * #B := by
      let IJ_bad := univ.filter (fun ij : Fin (k - 1) × Fin (k - 1) =>
        ∃ e ∈ bundlePlus vf ij.1 ij.2, 0 ≤ edgeSum hn z e)
      have hPairs_le_IJ : #Pairs ≤ #IJ_bad := by
        refine card_le_card_of_injOn
          (fun p : ℕ × ℕ => (⟨(p.1 - 1) % (k - 1), Nat.mod_lt _ (by omega)⟩,
                             ⟨(p.2 - 1) % (k - 1), Nat.mod_lt _ (by omega)⟩)) ?_ ?_
        · intro ⟨i, j⟩ hp
          rw [mem_coe, mem_biUnion] at hp
          rcases hp with ⟨j', hj', hp'⟩
          rcases mem_image.mp hp' with ⟨i', hi', heq⟩
          rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
          have hi_f := mem_filter.mp hi'
          rcases hi_f.2 with ⟨hi_lt, hj_lt, e, he_in, he_ge⟩
          rw [mem_coe]
          dsimp only
          refine mem_filter.mpr ⟨mem_univ _, e, ?_, he_ge⟩
          have hfin1 : (⟨(i' - 1) % (k - 1), Nat.mod_lt _ (by omega)⟩ : Fin (k - 1)) =
              ⟨i' - 1, hi_lt⟩ := Fin.ext (Nat.mod_eq_of_lt hi_lt)
          have hfin2 : (⟨(j' - 1) % (k - 1), Nat.mod_lt _ (by omega)⟩ : Fin (k - 1)) =
              ⟨j' - 1, hj_lt⟩ := Fin.ext (Nat.mod_eq_of_lt hj_lt)
          rwa [hfin1, hfin2]
        · intro ⟨i₁, j₁⟩ h₁ ⟨i₂, j₂⟩ h₂ heq
          rw [mem_coe, mem_biUnion] at h₁ h₂
          rcases h₁ with ⟨j₁', hj₁, hp₁⟩
          rcases h₂ with ⟨j₂', hj₂, hp₂⟩
          rcases mem_image.mp hp₁ with ⟨i₁', hi₁, heq₁⟩
          rcases mem_image.mp hp₂ with ⟨i₂', hi₂, heq₂⟩
          rcases Prod.mk.inj heq₁ with ⟨rfl, rfl⟩
          rcases Prod.mk.inj heq₂ with ⟨rfl, rfl⟩
          have hi₁_mem := mem_Icc.mp (mem_filter.mp hi₁).1
          have hi₂_mem := mem_Icc.mp (mem_filter.mp hi₂).1
          have hj₁_mem := mem_Icc.mp (mem_filter.mp hj₁).1
          have hj₂_mem := mem_Icc.mp (mem_filter.mp hj₂).1
          simp only [Prod.mk.injEq, Fin.ext_iff,
            Nat.mod_eq_of_lt (by omega : i₁' - 1 < k - 1),
            Nat.mod_eq_of_lt (by omega : i₂' - 1 < k - 1),
            Nat.mod_eq_of_lt (by omega : j₁' - 1 < k - 1),
            Nat.mod_eq_of_lt (by omega : j₂' - 1 < k - 1)] at heq
          exact Prod.ext (by omega) (by omega)
      have hIJ_sub : IJ_bad ⊆ B.biUnion (fun e =>
          univ.filter (fun ij : Fin (k - 1) × Fin (k - 1) => e ∈ bundlePlus vf ij.1 ij.2)) := by
        intro ij hij
        rcases (mem_filter.mp hij).2 with ⟨e, he_in, he_ge⟩
        have heB : e ∈ B := by
          refine mem_filter.mpr ⟨?_, he_ge⟩
          unfold bundle
          exact mem_biUnion.mpr ⟨ij, mem_univ _, mem_union_left _ he_in⟩
        exact mem_biUnion.mpr ⟨e, heB, mem_filter.mpr ⟨mem_univ _, he_in⟩⟩
      calc #Pairs
        _ ≤ #IJ_bad := hPairs_le_IJ
        _ ≤ #(B.biUnion (fun e =>
            univ.filter (fun ij : Fin (k - 1) × Fin (k - 1) => e ∈ bundlePlus vf ij.1 ij.2))) :=
          card_le_card hIJ_sub
        _ ≤ ∑ e ∈ B, #(univ.filter (fun ij : Fin (k - 1) × Fin (k - 1) => e ∈ bundlePlus vf ij.1 ij.2)) :=
          card_biUnion_le
        _ ≤ ∑ _e ∈ B, 88 := sum_le_sum fun e _ => card_pairs_containing_plus_le hk vf e
        _ = 88 * #B := by simp [mul_comm]
    exact hP_lb.trans hP_ub
  let T_both : Finset ℕ := T_bad ∪ T_bad.image (fun j => k - j)
  let Q_clean : Finset ℕ := Qset k z v (k / 5) \ T_both
  -- Show every j' ∈ Q_clean satisfies intSum z vf (4 * k + j') < 0
  have hthr_pigeon : (19 * k / 100) + 2 < k / 5 := by
    have hd1 := Nat.div_add_mod k 5
    have hm1 : k % 5 < 5 := Nat.mod_lt _ (by positivity)
    have hd2 : 100 * (19 * k / 100) ≤ 19 * k := Nat.mul_div_le (19 * k) 100
    linarith only [hd1, hm1, hd2, hk_large]
  have hpigeon_i : ∀ (j : ℕ) (hj : j ∈ Icc 1 (k - 1)) (hjT : j ∉ T_bad)
      (P : ℕ → Prop),
      k / 5 ≤ #((Icc 1 (k - 1)).filter P) →
      ∃ i₀ : Fin (k - 1),
        let j₀ : Fin (k - 1) := ⟨j - 1, by have := mem_Icc.mp hj; omega⟩
        isInterior k i₀ j₀ ∧
        (∀ e ∈ bundlePlus vf i₀ j₀, edgeSum hn z e < 0) ∧
        P (i₀.val + 1) := by
    intro j hj hjT P hP_card
    have hj_b := mem_Icc.mp hj
    have hnot_ge : #((Icc 1 (k - 1)).filter (fun i => hasBadPlus i j)) < 19 * k / 100 := by
      by_contra hge
      exact hjT (mem_filter.mpr ⟨hj, le_of_not_gt hge⟩)
    let GoodI := (Icc 1 (k - 1)).filter P
    let BadI := (Icc 1 (k - 1)).filter (fun i => hasBadPlus i j) ∪ ({1, k - j} : Finset ℕ)
    have hBadI_card : #BadI ≤ (19 * k / 100) + 2 := by
      have h1 := card_union_le ((Icc 1 (k - 1)).filter (fun i => hasBadPlus i j)) ({1, k - j} : Finset ℕ)
      have h2 : #({1, k - j} : Finset ℕ) ≤ 2 := (card_insert_le _ _).trans (by simp)
      dsimp only [BadI]
      linarith only [h1, h2, hnot_ge]
    have hpos : 0 < #(GoodI \ BadI) := by
      have hsd := card_sdiff_add_card_inter GoodI BadI
      have hin : #(GoodI ∩ BadI) ≤ #BadI := card_le_card inter_subset_right
      dsimp only [GoodI] at hsd hin ⊢
      linarith only [hthr_pigeon, hP_card, hBadI_card, hsd, hin]
    obtain ⟨i, hi_mem⟩ := card_pos.mp hpos
    rw [mem_sdiff] at hi_mem
    rcases hi_mem with ⟨hiG, hi_notB⟩
    have hiI := mem_Icc.mp (mem_filter.mp hiG).1
    have hiP : P i := (mem_filter.mp hiG).2
    simp only [BadI, mem_union, mem_insert, mem_singleton, not_or] at hi_notB
    rcases hi_notB with ⟨hno_bad, hi_ne1, hi_nekj⟩
    have hno_plus : ¬ hasBadPlus i j := fun h => hno_bad (mem_filter.mpr ⟨mem_Icc.mpr hiI, h⟩)
    let i₀ : Fin (k - 1) := ⟨i - 1, by omega⟩
    let j₀ : Fin (k - 1) := ⟨j - 1, by omega⟩
    have hi₀_eq : i₀.val + 1 = i := by dsimp [i₀]; omega
    have hj₀_eq : j₀.val + 1 = j := by dsimp [j₀]; omega
    refine ⟨i₀, ?_, ?_, ?_⟩
    · unfold isInterior
      rw [hi₀_eq, hj₀_eq]
      exact ⟨by omega, fun _ => by omega⟩
    · intro e he
      by_contra hge
      exact hno_plus ⟨by omega, by omega, e, he, not_lt.mp hge⟩
    · rwa [hi₀_eq]
  have hQ_clean_neg : ∀ j' ∈ Q_clean, intSum z vf (4 * k + j') < 0 := by
    intro j' hj'
    rw [mem_sdiff] at hj'
    rcases hj' with ⟨hj'Q, hj'_notT⟩
    simp only [Qset, mem_union, mem_singleton] at hj'Q
    rcases hj'Q with (hj_lt | hj_ge) | rfl
    · have hj_mem := (mem_filter.mp hj_lt).1
      have hj_card := (mem_filter.mp hj_lt).2
      have hj_not_bad : j' ∉ T_bad := fun h => hj'_notT (mem_union_left _ h)
      obtain ⟨i₀, hint, hall, hgap⟩ := hpigeon_i j' hj_mem hj_not_bad
        (fun i => intSum z (natToFin (v + i)) j' < 0) hj_card
      have hj₀_eq : (⟨j' - 1, by have := mem_Icc.mp hj_mem; omega⟩ : Fin (k - 1)).val + 1 = j' := by
        dsimp; have := mem_Icc.mp hj_mem; omega
      have hgap' : intSum z (vf + natToFin (i₀.val + 1))
          ((⟨j' - 1, by have := mem_Icc.mp hj_mem; omega⟩ : Fin (k - 1)).val + 1) < 0 := by
        rw [hj₀_eq]
        simpa [vf, natToFin_add] using hgap
      have hres := intSum_fourKPlusJ_neg hn5 hint hall hgap'
      rwa [hj₀_eq] at hres
    · have hj'_mem := (mem_filter.mp hj_ge).1
      have hj'_b := mem_Icc.mp hj'_mem
      have hj'_card := (mem_filter.mp hj_ge).2
      let j := k - j'
      have hj_mem : j ∈ Icc 1 (k - 1) := mem_Icc.mpr ⟨by omega, by omega⟩
      have hj_not_bad : j ∉ T_bad := by
        intro h
        apply hj'_notT
        refine mem_union_right _ (mem_image.mpr ⟨j, h, ?_⟩)
        dsimp [j]; omega
      obtain ⟨i₀, hint, hall, hgap⟩ := hpigeon_i j hj_mem hj_not_bad
        (fun i => 0 ≤ intSum z (natToFin (v + i)) j) hj'_card
      have hj₀_eq : (⟨j - 1, by omega⟩ : Fin (k - 1)).val + 1 = j := by
        dsimp; omega
      have hgap' : 0 ≤ intSum z (vf + natToFin (i₀.val + 1))
          ((⟨j - 1, by omega⟩ : Fin (k - 1)).val + 1) := by
        rw [hj₀_eq]
        simpa [vf, natToFin_add] using hgap
      have hres := intSum_fiveKMinusJ_neg hn5 hint hall hgap'
      rw [hj₀_eq, show 5 * k - j = 4 * k + j' by dsimp [j]; omega] at hres
      exact hres
    · simpa using (good_intSum_neg_234 hk hk_large hn hn5 z vf hv_good).2.2
  let Q' := Q_clean.filter (fun j' => isGood hk hn z (natToFin (v + 4 * k + j')))
  refine ⟨Q', (filter_subset _ Q_clean).trans sdiff_subset, ?_, ?_⟩
  · have hQ_sub : Qset k z v (k / 5) ⊆ Q' ∪ T_both ∪
        Q_clean.filter (fun j' => isBad hk hn z (natToFin (v + 4 * k + j'))) := by
      intro x hx
      by_cases hxT : x ∈ T_both
      · exact mem_union_left _ (mem_union_right _ hxT)
      · have hxC : x ∈ Q_clean := mem_sdiff.mpr ⟨hx, hxT⟩
        by_cases hxg : isGood hk hn z (natToFin (v + 4 * k + x))
        · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hxC, hxg⟩))
        · exact mem_union_right _ (mem_filter.mpr ⟨hxC, not_not.mp hxg⟩)
    have hQc_range : Q_clean ⊆ Ico 0 (0 + k) := by
      intro x hx
      have := mem_range.mp (Qset_subset_range (by omega) z v (k / 5) (mem_sdiff.mp hx).1)
      exact mem_Ico.mpr ⟨Nat.zero_le x, by omega⟩
    have hbad_sh : #(Q_clean.filter (fun j' => isBad hk hn z (natToFin (v + 4 * k + j')))) ≤ B1 := by
      have hrew : Q_clean.filter (fun j' => isBad hk hn z (natToFin (v + 4 * k + j'))) =
          Q_clean.filter (fun j' => isBad hk hn z (natToFin (j' + (v + 4 * k)))) := by
        congr 1; ext j'; rw [Nat.add_comm j' (v + 4 * k)]
      rw [hrew]
      exact card_filter_shift_bad_le hk hn z hz_sparse hQc_range (sh := v + 4 * k) (by omega)
    have hTboth_le : #T_both ≤ 2 * #T_bad := by
      have h1 := card_union_le T_bad (T_bad.image (fun j => k - j))
      have h2 : #(T_bad.image (fun j => k - j)) ≤ #T_bad := card_image_le
      dsimp only [T_both]
      linarith only [h1, h2]
    have h2T_B1_le : 2 * #T_bad + B1 ≤ 3 * k / (2 * 10 ^ 6) := by
      obtain ⟨q19, hq19_eq⟩ : ∃ q19, q19 = 19 * k / 100 := ⟨_, rfl⟩
      rw [← hq19_eq] at hT_card_mul
      obtain ⟨B2, hB2_eq⟩ : ∃ B2, B2 = 3 * k / (2 * 10 ^ 6) := ⟨_, rfl⟩
      rw [← hB2_eq]
      have hv_lt : #(badEdgesAt hk hn z vf) ≤ 3 * k ^ 2 / (2 * 10 ^ 9) := (not_le.mp hv_good).le
      have hB0_ub : 2 * 10 ^ 9 * (3 * k ^ 2 / (2 * 10 ^ 9)) ≤ 3 * k ^ 2 :=
        Nat.mul_div_le (3 * k ^ 2) (2 * 10 ^ 9)
      have h19_lb : 19 * k - 100 < 100 * q19 := by
        have hd := Nat.div_add_mod (19 * k) 100
        rw [← hq19_eq] at hd
        have hm : 19 * k % 100 < 100 := Nat.mod_lt _ (by positivity)
        omega
      have hT_ineq : 2 * 10 ^ 9 * (#T_bad * (19 * k - 100)) ≤ 88 * 100 * (3 * k ^ 2) := by
        have h1 : #T_bad * (19 * k - 100) ≤ #T_bad * (100 * q19) :=
          Nat.mul_le_mul_left _ h19_lb.le
        have h2 : #T_bad * (100 * q19) = 100 * (#T_bad * q19) := by ring
        have h3 := Nat.mul_le_mul_left 100 (hT_card_mul.trans (Nat.mul_le_mul_left 88 hv_lt))
        have h4 := Nat.mul_le_mul_left (2 * 10 ^ 9) (h1.trans (h2.trans_le h3))
        have h5 := Nat.mul_le_mul_left 8800 hB0_ub
        have hr : 2 * 10 ^ 9 * (100 * (88 * (3 * k ^ 2 / (2 * 10 ^ 9)))) =
            8800 * (2 * 10 ^ 9 * (3 * k ^ 2 / (2 * 10 ^ 9))) := by ring
        linarith only [h4, h5, hr]
      obtain ⟨q14, hq14_eq⟩ : ∃ q14, q14 = 14 * k / 10 ^ 7 := ⟨_, rfl⟩
      have h2T_ub : 2 * #T_bad ≤ q14 := by
        by_contra hgt
        have hge : q14 + 1 ≤ 2 * #T_bad := by omega
        have hd : 14 * k < 10 ^ 7 * (q14 + 1) := by
          have := hq14_eq ▸ Nat.lt_mul_div_succ (14 * k) (by positivity : 0 < 10 ^ 7)
          linarith only [this]
        have hmul1 : 14 * k < 10 ^ 7 * (2 * #T_bad) := hd.trans_le (Nat.mul_le_mul_left _ hge)
        have hmul2 := Nat.mul_le_mul_right (19 * k - 100) hmul1.le
        zify [show 100 ≤ 19 * k by omega] at hT_ineq hmul2
        nlinarith only [hT_ineq, hmul2, hk_large]
      have hB2_lb : 3 * k < 2 * 10 ^ 6 * B2 + 2 * 10 ^ 6 := by
        have hd := Nat.div_add_mod (3 * k) (2 * 10 ^ 6)
        rw [← hB2_eq] at hd
        have hm : 3 * k % (2 * 10 ^ 6) < 2 * 10 ^ 6 := Nat.mod_lt _ (by positivity)
        linarith only [hd, hm]
      have h14_ub : 10 ^ 7 * q14 ≤ 14 * k := hq14_eq ▸ Nat.mul_div_le (14 * k) (10 ^ 7)
      have hB1_k : 5 * 10 ^ 18 * B1 ≤ k :=
        (Nat.mul_le_mul_left (5 * 10 ^ 18) hB1_ub).trans (Nat.mul_div_le k (5 * 10 ^ 18))
      have hm_2T := Nat.mul_le_mul_left (10 ^ 7) h2T_ub
      have h0_B1 : 0 ≤ B1 := Nat.zero_le B1
      linarith only [hm_2T, h14_ub, hB1_k, hB2_lb, hk_large, h0_B1]
    have hun1 := (card_le_card hQ_sub).trans (card_union_le _ _)
    have hun2 := card_union_le Q' T_both
    linarith only [hun1, hun2, hbad_sh, hTboth_le, h2T_B1_le]
  · intro j' hj'
    rcases mem_filter.mp hj' with ⟨hj'C, hj'g⟩
    have hj'_lt : j' < k := mem_range.mp (Qset_subset_range (by omega) z v (k / 5) (mem_sdiff.mp hj'C).1)
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, ?_, hj'g⟩
    have hlen : v + 4 * k + j' - v = 4 * k + j' := by omega
    rw [hlen]
    exact hQ_clean_neg j' hj'C

lemma exists_Qv_six_seven {n k : ℕ} [NeZero n] (hk : 2 ≤ k) (hk_large : 10 ^ 45 < k)
    (hn : 2 * k ≤ n) (hn5 : 5 * k ≤ n)
    (z : Fin n → ℝ) {m B1 : ℕ} (hm_n : m + 1 ≤ n)
    (hz_sparse : ∀ u : ℕ, u + k ≤ m + 1 →
      #((Ico u (u + k)).filter (fun p => isBad hk hn z (natToFin p))) ≤ B1)
    (hB1_ub : B1 ≤ k / (5 * 10 ^ 18))
    {v : ℕ} (hv_ub : v + 8 * k ≤ m + 1)
    (hv_good : isGood hk hn z (natToFin v)) :
    ∃ Qv ⊆ Qset k z v (k / 5),
      #(Qset k z v (k / 5)) ≤ #Qv + (3 * k / (2 * 10 ^ 6) + 2 * B1) ∧
      ∀ j ∈ Qv, v + 6 * k + j ∈ Rset hk hn z m v ∧
        v + 7 * k + j ∈ Rset hk hn z m v := by
  obtain ⟨Q', hQ'_sub, hQ'_card, hQ'_R⟩ :=
    exists_Q_shift_fourK hk hk_large hn hn5 z hm_n hz_sparse hB1_ub (by omega) hv_good
  let Qv := Q'.filter (fun j =>
    isGood hk hn z (natToFin (v + 6 * k + j)) ∧ isGood hk hn z (natToFin (v + 7 * k + j)))
  refine ⟨Qv, (filter_subset _ Q').trans hQ'_sub, ?_, ?_⟩
  · have hQ'_ico : Q' ⊆ Ico 0 (0 + k) := by
      intro j hj
      have := mem_range.mp (Qset_subset_range (by omega) z v (k / 5) (hQ'_sub hj))
      exact mem_Ico.mpr ⟨Nat.zero_le j, by omega⟩
    have hsub : Q' \ Qv ⊆
        Q'.filter (fun j => isBad hk hn z (natToFin (j + (v + 6 * k)))) ∪
        Q'.filter (fun j => isBad hk hn z (natToFin (j + (v + 7 * k)))) := by
      intro j hj
      rcases mem_sdiff.mp hj with ⟨hj0, hj_not⟩
      have hbad_or : isBad hk hn z (natToFin (j + (v + 6 * k))) ∨
          isBad hk hn z (natToFin (j + (v + 7 * k))) := by
        by_contra hnb
        push Not at hnb
        rw [Nat.add_comm j (v + 6 * k), Nat.add_comm j (v + 7 * k)] at hnb
        exact hj_not (mem_filter.mpr ⟨hj0, hnb⟩)
      exact mem_union.mpr (hbad_or.imp (fun h => mem_filter.mpr ⟨hj0, h⟩) (fun h => mem_filter.mpr ⟨hj0, h⟩))
    have hb6 := card_filter_shift_bad_le hk hn z hz_sparse hQ'_ico (sh := v + 6 * k) (by omega)
    have hb7 := card_filter_shift_bad_le hk hn z hz_sparse hQ'_ico (sh := v + 7 * k) (by omega)
    have hQv_sub : Qv ⊆ Q' := filter_subset _ Q'
    have hsd := card_sdiff_add_card_eq_card hQv_sub
    have hun := (card_le_card hsub).trans (card_union_le _ _)
    linarith only [hQ'_card, hsd, hun, hb6, hb7]
  · intro j hj
    rcases mem_filter.mp hj with ⟨hjQ', hg6, hg7⟩
    have hj_lt : j < k := mem_range.mp (Qset_subset_range (by omega) z v (k / 5) (hQ'_sub hjQ'))
    have hR4 := hQ'_R j hjQ'
    have h6_eq : v + 6 * k + j = (v + 4 * k + j) + 2 * k := by omega
    have h7_eq : v + 7 * k + j = (v + 4 * k + j) + 3 * k := by omega
    rw [h6_eq] at hg6 ⊢
    rw [h7_eq] at hg7 ⊢
    exact ⟨Rset_step_twoK hk hk_large hn hn5 z hm_n hR4 (by omega) hg6,
           Rset_step_threeK hk hk_large hn hn5 z hm_n hR4 (by omega) hg7⟩

/-- Forward density lemma at `[16k, 17k)` for any `z` with `0` good and `B1`-sparse length-`k` subintervals. -/
lemma forward_R0_density {n k : ℕ} [NeZero n]
    (hk : 2 ≤ k) (hk_large : 10 ^ 45 < k) (hn : 2 * k ≤ n) (hn5 : 5 * k ≤ n)
    (z : Fin n → ℝ) {m B1 : ℕ}
    (hm_lb : 40 * k ≤ m + 1) (hm_n : m + 1 ≤ n)
    (hz0 : isGood hk hn z 0)
    (hz_sparse : ∀ u : ℕ, u + k ≤ m + 1 →
      #((Ico u (u + k)).filter (fun p => isBad hk hn z (natToFin p))) ≤ B1)
    (hB1_ub : B1 ≤ k / (5 * 10 ^ 18)) :
    508 * k ≤ 1000 * (#(Rset hk hn z m 0 ∩ Ico (16 * k) (17 * k)) + B1) := by
  have : NeZero k := ⟨by omega⟩
  obtain ⟨loss1, hloss1_eq⟩ : ∃ loss1, loss1 = 3 * k / (2 * 10 ^ 6) + 2 * B1 := ⟨_, rfl⟩
  have hex_Qv : ∀ v : ℕ, ∃ Qv : Finset ℕ,
      ¬ (v + 8 * k ≤ m + 1 ∧ isGood hk hn z (natToFin v)) ∨
        (Qv ⊆ Qset k z v (k / 5) ∧
        #(Qset k z v (k / 5)) ≤ #Qv + loss1 ∧
        ∀ j ∈ Qv, v + 6 * k + j ∈ Rset hk hn z m v ∧ v + 7 * k + j ∈ Rset hk hn z m v) := by
    intro v
    by_cases hv : v + 8 * k ≤ m + 1 ∧ isGood hk hn z (natToFin v)
    · obtain ⟨Qv, h1, h2, h3⟩ := exists_Qv_six_seven hk hk_large hn hn5 z hm_n hz_sparse hB1_ub hv.1 hv.2
      exact ⟨Qv, Or.inr ⟨h1, hloss1_eq ▸ h2, h3⟩⟩
    · exact ⟨∅, Or.inl hv⟩
  choose Qv hQv_or using hex_Qv
  have hQv : ∀ v : ℕ, (v + 8 * k ≤ m + 1 ∧ isGood hk hn z (natToFin v)) →
      Qv v ⊆ Qset k z v (k / 5) ∧
      #(Qset k z v (k / 5)) ≤ #(Qv v) + loss1 ∧
      ∀ j ∈ Qv v, v + 6 * k + j ∈ Rset hk hn z m v ∧ v + 7 * k + j ∈ Rset hk hn z m v :=
    fun v hv => (hQv_or v).resolve_left fun hnot => hnot hv
  have h0_ok : 0 + 8 * k ≤ m + 1 ∧ isGood hk hn z (natToFin 0) := by
    refine ⟨by omega, ?_⟩
    simpa [natToFin_zero] using hz0
  obtain ⟨hQ0_sub, hQ0_card, hQ0_R⟩ := hQv 0 h0_ok
  let Q0_full := Qset k z 0 (k / 5)
  let Q7_full := Qset k z (7 * k) (9 * k / 20)
  let S_nat : Finset (ℕ × ℕ) := (Qv 0).biUnion (fun a =>
    ((Qv (a + 6 * k) ∪ Qv (a + 7 * k)) ∩ Q7_full).image (fun b => (a, b)))
  have hS_sub : S_nat ⊆ Q0_full ×ˢ Q7_full := by
    intro p hp
    rcases mem_biUnion.mp hp with ⟨a, ha, hp'⟩
    rcases mem_image.mp hp' with ⟨b, hb, rfl⟩
    exact mem_product.mpr ⟨hQ0_sub ha, (mem_inter.mp hb).2⟩
  have hS_sum_R0 : ∀ p ∈ S_nat, p.1 + p.2 + 13 * k ∈ Rset hk hn z m 0 := by
    intro ⟨a, b⟩ hp
    rcases mem_biUnion.mp hp with ⟨a', ha', hp'⟩
    rcases mem_image.mp hp' with ⟨b', hb', heq⟩
    rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    obtain ⟨ha6_R0, ha7_R0⟩ := hQ0_R a' ha'
    rw [zero_add, Nat.add_comm (6 * k) a'] at ha6_R0
    rw [zero_add, Nat.add_comm (7 * k) a'] at ha7_R0
    have ha_lt : a' < k := mem_range.mp (Qset_subset_range (by omega) z 0 (k / 5) (hQ0_sub ha'))
    rcases mem_union.mp (mem_inter.mp hb').1 with hb6 | hb7
    · have hg6 : isGood hk hn z (natToFin (a' + 6 * k)) := by
        have hmem := ha6_R0; rw [Rset, mem_filter] at hmem; exact hmem.2.2
      have ha6_ok : (a' + 6 * k) + 8 * k ≤ m + 1 ∧ isGood hk hn z (natToFin (a' + 6 * k)) :=
        ⟨by omega, hg6⟩
      have hb_R := ((hQv (a' + 6 * k) ha6_ok).2.2 b' hb6).2
      have heq_sum : (a' + 6 * k) + 7 * k + b' = a' + b' + 13 * k := by omega
      rw [heq_sum] at hb_R
      exact Rset_trans hk hn z hm_n ha6_R0 hb_R
    · have hg7 : isGood hk hn z (natToFin (a' + 7 * k)) := by
        have hmem := ha7_R0; rw [Rset, mem_filter] at hmem; exact hmem.2.2
      have ha7_ok : (a' + 7 * k) + 8 * k ≤ m + 1 ∧ isGood hk hn z (natToFin (a' + 7 * k)) :=
        ⟨by omega, hg7⟩
      have hb_R := ((hQv (a' + 7 * k) ha7_ok).2.2 b' hb7).1
      have heq_sum : (a' + 7 * k) + 6 * k + b' = a' + b' + 13 * k := by omega
      rw [heq_sum] at hb_R
      exact Rset_trans hk hn z hm_n ha7_R0 hb_R
  -- Lower bound #S_nat
  have hSnat_loss : #(Q0_full ×ˢ Q7_full) - #S_nat ≤ 3 * loss1 * k := by
    have hfiber_lb : ∀ a ∈ Qv 0,
        #Q7_full ≤ #((Qv (a + 6 * k) ∪ Qv (a + 7 * k)) ∩ Q7_full) + 2 * loss1 := by
      intro a ha
      obtain ⟨ha6_R0, ha7_R0⟩ := hQ0_R a ha
      rw [zero_add, Nat.add_comm (6 * k) a] at ha6_R0
      rw [zero_add, Nat.add_comm (7 * k) a] at ha7_R0
      have ha_lt : a < k := mem_range.mp (Qset_subset_range (by omega) z 0 (k / 5) (hQ0_sub ha))
      have hg6 : isGood hk hn z (natToFin (a + 6 * k)) := by
        have hmem := ha6_R0; rw [Rset, mem_filter] at hmem; exact hmem.2.2
      have hg7 : isGood hk hn z (natToFin (a + 7 * k)) := by
        have hmem := ha7_R0; rw [Rset, mem_filter] at hmem; exact hmem.2.2
      obtain ⟨hsub6, hcard6, _⟩ := hQv (a + 6 * k) ⟨by omega, hg6⟩
      obtain ⟨hsub7, hcard7, _⟩ := hQv (a + 7 * k) ⟨by omega, hg7⟩
      have hcov7 := Qset_sevenK_subset hk_large z ha_lt
      have hQ7_sub_union : Q7_full ⊆
          ((Qv (a + 6 * k) ∪ Qv (a + 7 * k)) ∩ Q7_full) ∪
          (Qset k z (a + 6 * k) (k / 5) \ Qv (a + 6 * k)) ∪
          (Qset k z (a + 7 * k) (k / 5) \ Qv (a + 7 * k)) := by
        intro b hb
        by_cases hb_in : b ∈ Qv (a + 6 * k) ∪ Qv (a + 7 * k)
        · exact mem_union_left _ (mem_union_left _ (mem_inter.mpr ⟨hb_in, hb⟩))
        · simp only [mem_union, not_or] at hb_in
          rcases mem_union.mp (hcov7 hb) with h6 | h7
          · exact mem_union_left _ (mem_union_right _ (mem_sdiff.mpr ⟨h6, hb_in.1⟩))
          · exact mem_union_right _ (mem_sdiff.mpr ⟨h7, hb_in.2⟩)
      have hsd6 := card_sdiff_add_card_eq_card hsub6
      have hsd7 := card_sdiff_add_card_eq_card hsub7
      have hun1 := (card_le_card hQ7_sub_union).trans (card_union_le _ _)
      have hun2 := card_union_le ((Qv (a + 6 * k) ∪ Qv (a + 7 * k)) ∩ Q7_full)
        (Qset k z (a + 6 * k) (k / 5) \ Qv (a + 6 * k))
      linarith only [hun1, hun2, hsd6, hsd7, hcard6, hcard7]
    have hS_eq_sum : #S_nat = ∑ a ∈ Qv 0, #((Qv (a + 6 * k) ∪ Qv (a + 7 * k)) ∩ Q7_full) := by
      dsimp only [S_nat]
      rw [card_biUnion]
      · refine sum_congr rfl fun a _ => ?_
        exact card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
      · intro a₁ _ a₂ _ hne
        rw [Function.onFun, disjoint_left]
        intro p hp1 hp2
        rcases mem_image.mp hp1 with ⟨_, _, rfl⟩
        rcases mem_image.mp hp2 with ⟨_, _, heq⟩
        exact hne (Prod.mk.inj heq).1.symm
    have hQ0_le_k : #Q0_full ≤ k :=
      (card_le_card (Qset_subset_range (by omega) z 0 (k / 5))).trans (by simp)
    have hQ7_le_k : #Q7_full ≤ k :=
      (card_le_card (Qset_subset_range (by omega) z (7 * k) (9 * k / 20))).trans (by simp)
    have hsum_add : #S_nat + #(Qv 0) * (2 * loss1) ≥ #(Qv 0) * #Q7_full := by
      calc #(Qv 0) * #Q7_full
        _ = ∑ _a ∈ Qv 0, #Q7_full := by simp
        _ ≤ ∑ a ∈ Qv 0, (#((Qv (a + 6 * k) ∪ Qv (a + 7 * k)) ∩ Q7_full) + 2 * loss1) :=
          sum_le_sum hfiber_lb
        _ = #S_nat + #(Qv 0) * (2 * loss1) := by rw [sum_add_distrib, ← hS_eq_sum]; simp
    have hQv0_le_k : #(Qv 0) ≤ k := (card_le_card hQ0_sub).trans hQ0_le_k
    have hprod_card : #(Q0_full ×ˢ Q7_full) = #Q0_full * #Q7_full := card_product _ _
    have hm1 : (#Q0_full - #(Qv 0)) * #Q7_full ≤ loss1 * k := by
      have hd : #Q0_full - #(Qv 0) ≤ loss1 := by
        dsimp only [Q0_full]; omega
      exact Nat.mul_le_mul hd hQ7_le_k
    have hm2 : #(Qv 0) * (2 * loss1) ≤ 2 * loss1 * k := by
      calc #(Qv 0) * (2 * loss1) = 2 * loss1 * #(Qv 0) := by ring
        _ ≤ 2 * loss1 * k := Nat.mul_le_mul_left _ hQv0_le_k
    have hsplit_q0 : #Q0_full * #Q7_full = (#Q0_full - #(Qv 0)) * #Q7_full + #(Qv 0) * #Q7_full := by
      have hle : #(Qv 0) ≤ #Q0_full := card_le_card hQ0_sub
      rw [← Nat.add_mul, Nat.sub_add_cancel hle]
    have hr3 : loss1 * k + 2 * loss1 * k = 3 * loss1 * k := by ring
    omega
  -- Push into ZMod k and invoke `sumset_growth_zmod`
  let A₀ : Finset (ZMod k) := Q0_full.image (fun j : ℕ => (j : ZMod k))
  let B₀ : Finset (ZMod k) := Q7_full.image (fun j : ℕ => (j : ZMod k))
  let pairCast (p : ℕ × ℕ) : ZMod k × ZMod k := ((p.1 : ZMod k), (p.2 : ZMod k))
  let S_zmod : Finset (ZMod k × ZMod k) := S_nat.image pairCast
  have hA₀_card : #A₀ = #Q0_full :=
    card_image_of_injOn (natCast_injOn_range_k.mono (Qset_subset_range (by omega) z 0 (k / 5)))
  have hB₀_card : #B₀ = #Q7_full :=
    card_image_of_injOn (natCast_injOn_range_k.mono (Qset_subset_range (by omega) z (7 * k) (9 * k / 20)))
  have hSzmod_card : #S_zmod = #S_nat := by
    refine card_image_of_injOn fun p₁ hp₁ p₂ hp₂ heq => ?_
    rw [mem_coe] at hp₁ hp₂
    have hp₁' := mem_product.mp (hS_sub hp₁)
    have hp₂' := mem_product.mp (hS_sub hp₂)
    have h1 := natCast_injOn_range_k
      (Qset_subset_range (by omega) z 0 (k / 5) hp₁'.1)
      (Qset_subset_range (by omega) z 0 (k / 5) hp₂'.1)
      (Prod.mk.inj heq).1
    have h2 := natCast_injOn_range_k
      (Qset_subset_range (by omega) z (7 * k) (9 * k / 20) hp₁'.2)
      (Qset_subset_range (by omega) z (7 * k) (9 * k / 20) hp₂'.2)
      (Prod.mk.inj heq).2
    exact Prod.ext h1 h2
  have hSzmod_sub : S_zmod ⊆ A₀ ×ˢ B₀ := by
    intro q hq
    rcases mem_image.mp hq with ⟨p, hp, rfl⟩
    have hp' := mem_product.mp (hS_sub hp)
    exact mem_product.mpr ⟨mem_image_of_mem _ hp'.1, mem_image_of_mem _ hp'.2⟩
  have hA₀_anti : ∀ x : ZMod k, x ∈ A₀ ∨ -x ∈ A₀ := by
    refine Qset_image_antisymm hk z 0 (k / 5) ?_
    obtain ⟨q5, hq5⟩ : ∃ q5, q5 = k / 5 := ⟨_, rfl⟩
    rw [← hq5]
    have : 5 * q5 ≤ k := hq5 ▸ Nat.mul_div_le k 5
    omega
  have hB₀_anti : ∀ x : ZMod k, x ∈ B₀ ∨ -x ∈ B₀ := by
    refine Qset_image_antisymm hk z (7 * k) (9 * k / 20) ?_
    obtain ⟨q20, hq20⟩ : ∃ q20, q20 = 9 * k / 20 := ⟨_, rfl⟩
    rw [← hq20]
    have : 20 * q20 ≤ 9 * k := hq20 ▸ Nat.mul_div_le (9 * k) 20
    omega
  obtain ⟨b3, hb3_eq⟩ : ∃ b3, b3 = k / 400 := ⟨_, rfl⟩
  have hb3_ub : 400 * b3 ≤ k := hb3_eq ▸ Nat.mul_div_le k 400
  have hb3_lb : k ≤ 400 * (b3 + 1) := by
    have := hb3_eq ▸ Nat.lt_mul_div_succ k (by positivity : 0 < 400)
    linarith only [this]
  have hloss_le_b3 : #(A₀ ×ˢ B₀) - #S_zmod ≤ b3 ^ 2 := by
    rw [card_product, hA₀_card, hB₀_card, hSzmod_card, ← card_product]
    refine hSnat_loss.trans ?_
    have hB2_ub : 2 * 10 ^ 6 * (3 * k / (2 * 10 ^ 6)) ≤ 3 * k := Nat.mul_div_le (3 * k) (2 * 10 ^ 6)
    have hB1_k : 5 * 10 ^ 18 * B1 ≤ k :=
      (Nat.mul_le_mul_left (5 * 10 ^ 18) hB1_ub).trans (Nat.mul_div_le k (5 * 10 ^ 18))
    have hloss1_ub : 10 ^ 6 * loss1 ≤ 2 * k := by
      have h0_B1 : 0 ≤ B1 := Nat.zero_le B1
      rw [hloss1_eq]
      linarith only [hB2_ub, hB1_k, h0_B1]
    have h1 : 10 ^ 6 * (3 * loss1 * k) ≤ 6 * k ^ 2 := by
      calc 10 ^ 6 * (3 * loss1 * k) = 3 * k * (10 ^ 6 * loss1) := by ring
        _ ≤ 3 * k * (2 * k) := Nat.mul_le_mul_left _ hloss1_ub
        _ = 6 * k ^ 2 := by ring
    have hb3_lb2 : k - 400 < 400 * b3 := by
      have hd := Nat.div_add_mod k 400
      rw [← hb3_eq] at hd
      have hm : k % 400 < 400 := Nat.mod_lt _ (by positivity)
      omega
    have hquad : 400 ^ 2 * (6 * k ^ 2) ≤ 10 ^ 6 * (k - 400) ^ 2 := by
      zify [show 400 ≤ k by omega]
      nlinarith only [hk_large]
    have h2 : (k - 400) ^ 2 ≤ (400 * b3) ^ 2 := Nat.pow_le_pow_left hb3_lb2.le 2
    have h3 : 400 ^ 2 * 10 ^ 6 * (3 * loss1 * k) ≤ 400 ^ 2 * 10 ^ 6 * b3 ^ 2 := by
      have hm := Nat.mul_le_mul_left (400 ^ 2) h1
      have hm2 := Nat.mul_le_mul_left (10 ^ 6) h2
      have hr : 10 ^ 6 * (400 * b3) ^ 2 = 400 ^ 2 * 10 ^ 6 * b3 ^ 2 := by ring
      have hr2 : 400 ^ 2 * (10 ^ 6 * (3 * loss1 * k)) = 400 ^ 2 * 10 ^ 6 * (3 * loss1 * k) := by ring
      linarith only [hm, hm2, hquad, hr, hr2]
    linarith only [h3]
  let Im := S_zmod.image (fun q => q.1 + q.2)
  have hIm_large : 508 * k ≤ 1000 * #Im :=
    sumset_growth_zmod (by omega) A₀ B₀ hA₀_anti hB₀_anti S_zmod hSzmod_sub b3 hb3_ub hb3_lb hloss_le_b3
  -- Mod-k lift from Im ⊆ ZMod k directly into Ico (16*k) (17*k)
  have hIm_neg16 : ∀ z_bar ∈ Im, intSum z 0 (z_bar.val + 16 * k) < 0 := by
    intro z_bar hz_bar
    rcases mem_image.mp hz_bar with ⟨_, hp_zmod, rfl⟩
    rcases mem_image.mp hp_zmod with ⟨⟨a, b⟩, habS, rfl⟩
    have hab_R0 := hS_sum_R0 (a, b) habS
    have hab_prod := mem_product.mp (hS_sub habS)
    have ha_lt : a < k := mem_range.mp (Qset_subset_range (by omega) z 0 (k / 5) hab_prod.1)
    have hb_lt : b < k := mem_range.mp (Qset_subset_range (by omega) z (7 * k) (9 * k / 20) hab_prod.2)
    have hval_eq : ((a : ZMod k) + (b : ZMod k)).val = (a + b) % k := by
      rw [← Nat.cast_add, ZMod.val_natCast]
    dsimp only [pairCast]
    rw [hval_eq]
    simp only [Rset, mem_filter, Nat.sub_zero, natToFin_zero] at hab_R0
    rcases hab_R0 with ⟨_, hsum13, hg13⟩
    by_cases hab_k : a + b < k
    · rw [Nat.mod_eq_of_lt hab_k]
      have h3k := (good_intSum_neg_234 hk hk_large hn hn5 z (natToFin (a + b + 13 * k)) hg13).2.1
      have hlen : a + b + 16 * k = (a + b + 13 * k) + 3 * k := by omega
      rw [hlen, intSum_add z 0 (by omega), zero_add]
      linarith only [hsum13, h3k]
    · have hmod_sub : (a + b) % k = a + b - k := by
        conv_lhs => rw [show a + b = (a + b - k) + k by omega]
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [hmod_sub]
      have h2k := (good_intSum_neg_234 hk hk_large hn hn5 z (natToFin (a + b + 13 * k)) hg13).1
      have hlen : a + b - k + 16 * k = (a + b + 13 * k) + 2 * k := by omega
      rw [hlen, intSum_add z 0 (by omega), zero_add]
      linarith only [hsum13, h2k]
  let Im_nat := Im.image (fun z_bar : ZMod k => z_bar.val + 16 * k)
  have hIm_nat_card : #Im_nat = #Im :=
    card_image_of_injective _ (fun _ _ h => ZMod.val_injective k (Nat.add_right_cancel h))
  have hIm_nat_sub : Im_nat ⊆
      (Rset hk hn z m 0 ∩ Ico (16 * k) (17 * k)) ∪
      (Ico (16 * k) (17 * k)).filter (fun p => isBad hk hn z (natToFin p)) := by
    intro p hp
    rcases mem_image.mp hp with ⟨z_bar, hz_bar, rfl⟩
    have hc_lt : z_bar.val < k := ZMod.val_lt z_bar
    have hp_ico : z_bar.val + 16 * k ∈ Ico (16 * k) (17 * k) := mem_Ico.mpr ⟨by omega, by omega⟩
    by_cases hgood : isGood hk hn z (natToFin (z_bar.val + 16 * k))
    · refine mem_union_left _ (mem_inter.mpr ⟨?_, hp_ico⟩)
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, ?_, hgood⟩
      simpa [natToFin_zero] using hIm_neg16 z_bar hz_bar
    · exact mem_union_right _ (mem_filter.mpr ⟨hp_ico, not_not.mp hgood⟩)
  have hbad16 := hz_sparse (16 * k) (by omega)
  rw [show 16 * k + k = 17 * k by omega] at hbad16
  have hun := (card_le_card hIm_nat_sub).trans (card_union_le _ _)
  rw [hIm_nat_card] at hun
  linarith only [hIm_large, hun, hbad16]

/-- Claim 4.2 (`transverse`): any interval `cycInt a₀ (m + 1)` of length between `40 * k`
and `(4 * 10 ^ 15 + 40) * k` with good endpoints and `B1`-sparse length-`k` subintervals
has strictly negative sum. -/
theorem claim_transverse {n k : ℕ} [NeZero n]
    (hk : 2 ≤ k)
    (hk_large : 10 ^ 45 < k)
    (hn : 2 * k ≤ n)
    (hn_large : (4 * 10 ^ 15 + 50) * k ≤ n)
    (x : Fin n → ℝ)
    (a₀ : Fin n) {m : ℕ}
    (hm_lb : 40 * k ≤ m + 1)
    (hm_ub : m + 1 ≤ (4 * 10 ^ 15 + 40) * k)
    (hgood_left : isGood hk hn x a₀)
    (hgood_right : isGood hk hn x (a₀ + natToFin m))
    (hsparse : ∀ u : ℕ, u + k ≤ m + 1 →
      #((cycInt (a₀ + natToFin u) k).filter (fun w => isBad hk hn x w)) ≤
        k / (5 * 10 ^ 18)) :
    intSum x a₀ (m + 1) < 0 := by
  have hn5 : 5 * k ≤ n := by linarith only [hn_large]
  have hm_n : m + 1 ≤ n := by linarith only [hm_ub, hn_large]
  obtain ⟨B1, hB1_eq⟩ : ∃ B1, B1 = k / (5 * 10 ^ 18) := ⟨_, rfl⟩
  -- Shift a₀ to 0
  let x' : Fin n → ℝ := fun w => x (a₀ + w)
  have hx'0 : isGood hk hn x' 0 := by
    rw [← isGood_shift hk hn x a₀ 0, add_zero]
    exact hgood_left
  have hx'm : isGood hk hn x' (natToFin m) := by
    rw [← isGood_shift hk hn x a₀ (natToFin m)]
    exact hgood_right
  have hx'_sparse : ∀ u : ℕ, u + k ≤ m + 1 →
      #((Ico u (u + k)).filter (fun p => isBad hk hn x' (natToFin p))) ≤ B1 := by
    intro u hu
    let S_src := (Ico u (u + k)).filter (fun p => isBad hk hn x' (natToFin p))
    let S_dst := (cycInt (a₀ + natToFin u) k).filter (fun w => isBad hk hn x w)
    have hmaps : Set.MapsTo (fun p => a₀ + natToFin p) S_src S_dst := by
      intro p hp
      rw [mem_coe] at hp ⊢
      rcases mem_filter.mp hp with ⟨hp_ico, hp_bad⟩
      have hpI := mem_Ico.mp hp_ico
      refine mem_filter.mpr ⟨?_, (isBad_shift hk hn x a₀ (natToFin p)).mpr hp_bad⟩
      simp only [cycInt, mem_image, mem_range]
      refine ⟨p - u, by omega, ?_⟩
      rw [add_assoc, ← natToFin_add, show u + (p - u) = p by omega]
    have hinj : Set.InjOn (fun p => a₀ + natToFin p) S_src := by
      intro p₁ hp₁ p₂ hp₂ heq
      rw [mem_coe] at hp₁ hp₂
      have h1 := mem_Ico.mp (mem_filter.mp hp₁).1
      have h2 := mem_Ico.mp (mem_filter.mp hp₂).1
      have hv := congrArg Fin.val (add_left_cancel heq)
      simp only [val_natToFin, Nat.mod_eq_of_lt (by omega : p₁ < n),
        Nat.mod_eq_of_lt (by omega : p₂ < n)] at hv
      exact hv
    exact (card_le_card_of_injOn _ hmaps hinj).trans (hB1_eq ▸ hsparse u hu)
  -- Reflected function y(w) = x' (natToFin m - w)
  let y : Fin n → ℝ := fun w => x' (natToFin m - w)
  have hy0 : isGood hk hn y 0 := by
    have := (isGood_refl hk hn x' (natToFin m) (natToFin m)).mpr hx'm
    rwa [sub_self] at this
  have hy_sparse : ∀ u : ℕ, u + k ≤ m + 1 →
      #((Ico u (u + k)).filter (fun p => isBad hk hn y (natToFin p))) ≤ B1 := by
    intro u hu
    let u' := m + 1 - (u + k)
    have hu' : u' + k ≤ m + 1 := by omega
    let S_src := (Ico u (u + k)).filter (fun p => isBad hk hn y (natToFin p))
    let S_dst := (Ico u' (u' + k)).filter (fun p => isBad hk hn x' (natToFin p))
    have hmaps : Set.MapsTo (fun p => m - p) S_src S_dst := by
      intro p hp
      rw [mem_coe] at hp ⊢
      rcases mem_filter.mp hp with ⟨hp_ico, hp_bad⟩
      have hpI := mem_Ico.mp hp_ico
      dsimp only
      refine mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
      have hsub_fin : (natToFin m : Fin n) - natToFin (m - p) = natToFin p := by
        rw [sub_eq_iff_eq_add, ← natToFin_add, show p + (m - p) = m by omega]
      have hy_bad : isBad hk hn y (natToFin m - natToFin (m - p)) := by
        rwa [hsub_fin]
      exact (isBad_refl hk hn x' (natToFin m) (natToFin (m - p))).mp hy_bad
    have hinj : Set.InjOn (fun p => m - p) S_src := by
      intro p₁ hp₁ p₂ hp₂ heq
      rw [mem_coe] at hp₁ hp₂
      have h1 := mem_Ico.mp (mem_filter.mp hp₁).1
      have h2 := mem_Ico.mp (mem_filter.mp hp₂).1
      dsimp only at heq
      omega
    exact (card_le_card_of_injOn _ hmaps hinj).trans (hx'_sparse u' hu')
  -- Apply forward_R0_density to x' (propagated to W) and to y (at [16k, 17k))
  have hfwd_x := forward_R0_density hk hk_large hn hn5 x' hm_lb hm_n hx'0 hx'_sparse hB1_eq.le
  have hfwd_y := forward_R0_density hk hk_large hn hn5 y hm_lb hm_n hy0 hy_sparse hB1_eq.le
  let v₀ := m + 2 - 17 * k
  let W := Ico v₀ (v₀ + k)
  have hprop_x := propagate_R0_window hk hk_large hn hn5 x' hm_n hx'_sparse
    (v₀ := v₀) (by omega) (by omega)
  obtain ⟨qv, hqv_eq⟩ : ∃ qv, qv = (v₀ - 16 * k) / k := ⟨_, rfl⟩
  rw [← hqv_eq] at hprop_x
  have hloss_x_small : 1000 * (B1 + (qv + 1) * B1) < 2 * k := by
    have hq_ub : qv ≤ 4 * 10 ^ 15 + 40 := by
      have h1 : v₀ - 16 * k ≤ k * (4 * 10 ^ 15 + 40) := by
        have hr : k * (4 * 10 ^ 15 + 40) = (4 * 10 ^ 15 + 40) * k := by ring
        dsimp only [v₀]
        omega
      rw [hqv_eq]
      exact Nat.div_le_of_le_mul h1
    have hB1_k : 5 * 10 ^ 18 * B1 ≤ k := hB1_eq ▸ Nat.mul_div_le k (5 * 10 ^ 18)
    have hsum_coeff : 1000 * (B1 + (qv + 1) * B1) ≤ 5 * 10 ^ 18 * B1 := by
      have h0_B1 : 0 ≤ B1 := Nat.zero_le B1
      nlinarith only [hq_ub, h0_B1]
    linarith only [hsum_coeff, hB1_k, hk_large]
  have hA_gt_half : k < 2 * #(Rset hk hn x' m 0 ∩ W) := by
    dsimp only [W]
    linarith only [hfwd_x, hprop_x, hloss_x_small]
  let B_W := (Rset hk hn y m 0 ∩ Ico (16 * k) (17 * k)).image (fun u' => m + 1 - u')
  have hBW_sub : B_W ⊆ W := by
    intro w hw
    rcases mem_image.mp hw with ⟨u', hu', rfl⟩
    have hu'I := mem_Ico.mp (mem_inter.mp hu').2
    exact mem_Ico.mpr ⟨by omega, by omega⟩
  have hBW_card : #B_W = #(Rset hk hn y m 0 ∩ Ico (16 * k) (17 * k)) := by
    refine card_image_of_injOn fun u₁ hu₁ u₂ hu₂ heq => ?_
    rw [mem_coe, mem_inter] at hu₁ hu₂
    have h1 := mem_Ico.mp hu₁.2
    have h2 := mem_Ico.mp hu₂.2
    omega
  have hBW_gt_half : k < 2 * #B_W := by
    have hB1_k : 5 * 10 ^ 18 * B1 ≤ k := hB1_eq ▸ Nat.mul_div_le k (5 * 10 ^ 18)
    have h0_B1 : 0 ≤ B1 := Nat.zero_le B1
    rw [hBW_card]
    linarith only [hfwd_y, hB1_k, hk_large, h0_B1]
  have hW_card : #W = k := by simp [W]
  have hinter_pos : 0 < #((Rset hk hn x' m 0 ∩ W) ∩ B_W) := by
    have hsub_u : (Rset hk hn x' m 0 ∩ W) ∪ B_W ⊆ W :=
      union_subset inter_subset_right hBW_sub
    have h1 := card_inter_add_card_union (Rset hk hn x' m 0 ∩ W) B_W
    have h2 := card_le_card hsub_u
    linarith only [h1, h2, hW_card, hA_gt_half, hBW_gt_half]
  obtain ⟨w, hw⟩ := card_pos.mp hinter_pos
  rcases mem_inter.mp hw with ⟨hwA, hwB⟩
  have hwRx : w ∈ Rset hk hn x' m 0 := (mem_inter.mp hwA).1
  have hwW := mem_Ico.mp (mem_inter.mp hwA).2
  have hsum_left : intSum x' 0 w < 0 := by
    rw [Rset, mem_filter] at hwRx
    simpa [natToFin_zero] using hwRx.2.1
  rcases mem_image.mp hwB with ⟨u', hu', rfl⟩
  have hu'Ry : u' ∈ Rset hk hn y m 0 := (mem_inter.mp hu').1
  have hu'I := mem_Ico.mp (mem_inter.mp hu').2
  have hsum_y : intSum y 0 u' < 0 := by
    rw [Rset, mem_filter] at hu'Ry
    simpa [natToFin_zero] using hu'Ry.2.1
  have hy_eq_right : intSum y 0 u' = intSum x' (natToFin (m + 1 - u')) u' := by
    dsimp only [y]
    rw [intSum_refl x' (natToFin m) 0 (by omega : 1 ≤ u'), zero_add]
    congr 1
    rw [sub_eq_iff_eq_add, ← natToFin_add]
    congr 1
    omega
  rw [hy_eq_right] at hsum_y
  have htotal_x' : intSum x' 0 (m + 1) < 0 := by
    have hsplit : m + 1 = (m + 1 - u') + u' := by omega
    rw [hsplit, intSum_add x' 0 (by omega), zero_add]
    linarith only [hsum_left, hsum_y]
  have hsh := intSum_shift x a₀ 0 (m + 1)
  rw [add_zero] at hsh
  rwa [← hsh]

end PokrovskiyTransverse

namespace PokrovskiyMain
open Finset PokrovskiyHypergraph PokrovskiyCover PokrovskiyTransverse

open Classical

lemma cycInt_univ {n : ℕ} [NeZero n] (u : Fin n) : cycInt u n = univ :=
  eq_univ_of_card _ (by rw [card_cycInt u le_rfl, Fintype.card_fin])

lemma intSum_univ {n : ℕ} [NeZero n] (x : Fin n → ℝ) (u : Fin n) :
    intSum x u n = ∑ v : Fin n, x v := by
  unfold intSum
  rw [cycInt_univ]

lemma nat_split_three {W u k : ℕ} (h : u + k ≤ W) : W = u + (k + (W - u - k)) := by
  omega

theorem prove_H2 :
    OMA.R_ManickamMiklosSinghiConjecture_manickam_miklos_singhi_conjecture_variants_pokrovskiy_R1.H2 := by
  intro n k hk hn_lb hn_ub hn x hx_zero
  dsimp only
  have hk_large : 10 ^ 45 < k := by nlinarith only [hn_lb, hn_ub, hk]
  have hn_pos : 0 < n := by linarith only [hk, hn]
  have : NeZero n := ⟨Nat.ne_of_gt hn_pos⟩
  suffices h_goal : k * (k - 1) ^ 2 ≤ #(nonnegEdges hn x) by
    refine Nat.le_trans h_goal (Nat.le_of_eq (congrArg Finset.card ?_))
    unfold nonnegEdges
    let p : Idx n k → Prop := fun e => 0 ≤ edgeSum hn x e
    change @Finset.filter (Idx n k) p _ univ = @Finset.filter (Idx n k) p _ univ
    exact congrArg (fun inst => @Finset.filter (Idx n k) p inst univ) (Subsingleton.elim _ _)
  by_contra h_lt
  have h_lt' : #(nonnegEdges hn x) < k * (k - 1) ^ 2 := not_le.mp h_lt
  obtain ⟨W_len, hW_eq⟩ : ∃ W_len, W_len = (4 * 10 ^ 15 + 40) * k := ⟨_, rfl⟩
  obtain ⟨B1, hB1_eq⟩ : ∃ B1, B1 = k / (5 * 10 ^ 18) := ⟨_, rfl⟩
  let isSparse (a₀ : Fin n) : Prop :=
    ∀ u : ℕ, u + k ≤ W_len →
      #((cycInt (a₀ + natToFin u) k).filter (fun w => isBad hk hn x w)) ≤ B1
  by_cases hex_sparse : ∃ a₀ : Fin n, isSparse a₀
  · -- Case 2: a sparse interval of length W_len exists; apply cover + transverse
    rcases hex_sparse with ⟨a₀, ha₀_sparse⟩
    let c₀ : Fin n := a₀ + natToFin W_len
    let L_c : ℕ := n - W_len
    have hW_lt_n : W_len < n := by
      rw [hW_eq]
      linarith only [hn_lb, hk]
    have hWLc : W_len + L_c = n := Nat.add_sub_of_le hW_lt_n.le
    have hLc_pos : 1 ≤ L_c := by linarith only [hW_lt_n, hWLc]
    have hLc_ub : L_c + (4 * 10 ^ 15 + 20) * k ≤ n := by
      have hr : (4 * 10 ^ 15 + 40) * k = (4 * 10 ^ 15 + 20) * k + 20 * k := by ring
      linarith only [hWLc, hW_eq, hr, hk]
    obtain ⟨j₀, L_J, _hLJ_pos, hLJ_ub, hsub_cov, hg_left_cov, hg_right_cov, hsum_J_neg⟩ :=
      claim_cover hk_large hn x h_lt' c₀ hLc_pos hLc_ub
    have hLJ_le_n40 : L_J + 40 * k ≤ n := by
      have hr : (4 * 10 ^ 15 + 40) * k = 4 * 10 ^ 15 * k + 40 * k := by ring
      linarith only [hLJ_ub, hWLc, hW_eq, hr]
    let b₀ : Fin n := j₀ + natToFin L_J
    let L_K : ℕ := n - L_J
    let m_K : ℕ := L_K - 1
    have hLJ_le_n : L_J ≤ n := by linarith only [hLJ_le_n40, hk]
    have hJLK : L_J + L_K = n := Nat.add_sub_of_le hLJ_le_n
    have hLK_ge : 40 * k ≤ L_K := by linarith only [hLJ_le_n40, hJLK]
    have hLK_pos : 1 ≤ L_K := by linarith only [hLK_ge, hk]
    have hmK_eq : m_K + 1 = L_K := Nat.sub_add_cancel hLK_pos
    have hLc_le_LJ : L_c ≤ L_J := by
      have hc1 := card_cycInt c₀ (by linarith only [hWLc] : L_c ≤ n)
      have hc2 := card_cycInt j₀ hLJ_le_n
      have hle := card_le_card hsub_cov
      linarith only [hc1, hc2, hle]
    have hmK_ub : m_K + 1 ≤ (4 * 10 ^ 15 + 40) * k := by
      linarith only [hmK_eq, hLc_le_LJ, hWLc, hJLK, hW_eq]
    -- Complement inclusion: cycInt b₀ L_K ⊆ cycInt a₀ W_len
    have hpart_a₀ : cycInt a₀ W_len ∪ cycInt c₀ L_c = univ := by
      rw [← cycInt_add a₀ W_len L_c, hWLc, cycInt_univ]
    have hdisj_a₀ : Disjoint (cycInt a₀ W_len) (cycInt c₀ L_c) :=
      disjoint_cycInt_add a₀ hWLc.le
    have hpart_j₀ : cycInt j₀ L_J ∪ cycInt b₀ L_K = univ := by
      rw [← cycInt_add j₀ L_J L_K, hJLK, cycInt_univ]
    have hdisj_j₀ : Disjoint (cycInt j₀ L_J) (cycInt b₀ L_K) :=
      disjoint_cycInt_add j₀ hJLK.le
    have hsub_K_W : cycInt b₀ L_K ⊆ cycInt a₀ W_len := by
      intro w hw
      have hw_not_J : w ∉ cycInt j₀ L_J := disjoint_right.mp hdisj_j₀ hw
      have hw_not_c : w ∉ cycInt c₀ L_c := fun hc => hw_not_J (hsub_cov hc)
      have hw_u : w ∈ cycInt a₀ W_len ∪ cycInt c₀ L_c := by rw [hpart_a₀]; exact mem_univ w
      exact (mem_union.mp hw_u).resolve_right hw_not_c
    -- Find offset d₀ < W_len with b₀ = a₀ + natToFin d₀ and d₀ + L_K ≤ W_len
    have hb₀_in_K : b₀ ∈ cycInt b₀ L_K := by
      simp only [cycInt, mem_image, mem_range]
      exact ⟨0, hLK_pos, by simp [natToFin_zero]⟩
    obtain ⟨d₀, hd₀_lt, hb₀_eq⟩ := by
      simpa only [cycInt, mem_image, mem_range] using hsub_K_W hb₀_in_K
    have hd₀_LK_le : d₀ + L_K ≤ W_len := by
      by_contra hgt
      have hgt' : W_len < d₀ + L_K := not_le.mp hgt
      have hd₀_sub : d₀ + (W_len - d₀) = W_len := Nat.add_sub_of_le hd₀_lt.le
      have hdiff_lt : W_len - d₀ < L_K := by linarith only [hgt', hd₀_sub]
      have hc₀_in_K : c₀ ∈ cycInt b₀ L_K := by
        simp only [cycInt, mem_image, mem_range]
        refine ⟨W_len - d₀, hdiff_lt, ?_⟩
        rw [← hb₀_eq, add_assoc, ← natToFin_add, hd₀_sub]
      have hc₀_in_c : c₀ ∈ cycInt c₀ L_c := by
        simp only [cycInt, mem_image, mem_range]
        exact ⟨0, hLc_pos, by simp [natToFin_zero]⟩
      exact disjoint_left.mp hdisj_a₀ (hsub_K_W hc₀_in_K) hc₀_in_c
    have hK_sparse : ∀ u : ℕ, u + k ≤ m_K + 1 →
        #((cycInt (b₀ + natToFin u) k).filter (fun w => isBad hk hn x w)) ≤ B1 := by
      intro u hu
      have hb_u : b₀ + natToFin u = a₀ + natToFin (d₀ + u) := by
        rw [← hb₀_eq, add_assoc, ← natToFin_add]
      rw [hb_u]
      exact ha₀_sparse (d₀ + u) (by linarith only [hu, hmK_eq, hd₀_LK_le])
    have hg_K_right : isGood hk hn x (b₀ + natToFin m_K) := by
      have heq : b₀ + natToFin m_K = j₀ - natToFin 1 := by
        dsimp only [b₀]
        rw [add_assoc, ← natToFin_add, eq_sub_iff_add_eq, add_assoc, ← natToFin_add]
        have hsum_n : L_J + m_K + 1 = n := by linarith only [hmK_eq, hJLK]
        have hn0 : (natToFin n : Fin n) = 0 := by ext; simp
        rw [hsum_n, hn0, add_zero]
      rw [heq]
      exact hg_left_cov
    have hsum_K_neg : intSum x b₀ (m_K + 1) < 0 :=
      claim_transverse hk hk_large hn (by linarith only [hn_lb]) x b₀
        (by rw [hmK_eq]; exact hLK_ge) hmK_ub hg_right_cov hg_K_right
        (fun u hu => hB1_eq ▸ hK_sparse u hu)
    rw [hmK_eq] at hsum_K_neg
    have htotal := intSum_add x j₀ (L₁ := L_J) (L₂ := L_K) hJLK.le
    rw [hJLK, intSum_univ] at htotal
    change ∑ v, x v = intSum x j₀ L_J + intSum x b₀ L_K at htotal
    linarith only [htotal, hx_zero, hsum_J_neg, hsum_K_neg]
  · -- Case 1: every interval of length W_len has ≥ B1 + 1 bad vertices
    have hnot_sp : ∀ a₀ : Fin n, ∃ u, u + k ≤ W_len ∧
        B1 < #((cycInt (a₀ + natToFin u) k).filter (fun w => isBad hk hn x w)) := by
      intro a₀
      by_contra hall
      push Not at hall
      exact hex_sparse ⟨a₀, hall⟩
    obtain ⟨M, hM_eq⟩ : ∃ M, M = n / W_len := ⟨_, rfl⟩
    have hW_pos : 0 < W_len := by rw [hW_eq]; linarith only [hk]
    have hM_lb : 2 * 10 ^ 30 ≤ M := by
      have hdiv := hM_eq ▸ Nat.lt_mul_div_succ n hW_pos
      have hW_ub : W_len < 5 * 10 ^ 15 * k := by rw [hW_eq]; linarith only [hk_large]
      have h1 : 10 ^ 46 * k < (5 * 10 ^ 15 * k) * (M + 1) := by
        calc 10 ^ 46 * k ≤ n := hn_lb
          _ < W_len * (M + 1) := hdiv
          _ < (5 * 10 ^ 15 * k) * (M + 1) :=
            Nat.mul_lt_mul_of_pos_right hW_ub (Nat.succ_pos M)
      have hr : (5 * 10 ^ 15 * k) * (M + 1) = 5 * 10 ^ 15 * (M + 1) * k := by ring
      have hr2 : 10 ^ 46 * k = 5 * 10 ^ 15 * (2 * 10 ^ 30) * k := by ring
      rw [hr, hr2] at h1
      have h3 : 5 * 10 ^ 15 * (2 * 10 ^ 30) < 5 * 10 ^ 15 * (M + 1) :=
        Nat.lt_of_mul_lt_mul_right h1
      have h4 : 2 * 10 ^ 30 < M + 1 := by linarith only [h3]
      exact Nat.le_of_lt_succ h4
    let block (q : ℕ) : Finset (Fin n) := (cycInt (natToFin (q * W_len)) W_len).filter (isBad hk hn x)
    have hblock_ge : ∀ q ∈ range M, B1 + 1 ≤ #(block q) := by
      intro q _
      let v_q : Fin n := natToFin (q * W_len)
      obtain ⟨u, hu, hgt⟩ := hnot_sp v_q
      have hsub : cycInt (v_q + natToFin u) k ⊆ cycInt v_q W_len := by
        have hw_split := nat_split_three hu
        conv_rhs => rw [hw_split]
        rw [cycInt_add v_q u (k + (W_len - u - k)),
            cycInt_add (v_q + natToFin u) k (W_len - u - k)]
        intro w hw
        exact mem_union_right _ (mem_union_left _ hw)
      have hf_sub : (cycInt (v_q + natToFin u) k).filter (isBad hk hn x) ⊆ block q :=
        filter_subset_filter _ hsub
      exact (Nat.succ_le_of_lt hgt).trans (card_le_card hf_sub)
    have hMW : M * W_len ≤ n := by
      have h1 := hM_eq ▸ Nat.mul_div_le n W_len
      have hr : W_len * M = M * W_len := by ring
      linarith only [h1, hr]
    have hblock_disj : (range M : Set ℕ).PairwiseDisjoint block := by
      intro q₁ hq₁ q₂ hq₂ hne
      rw [mem_coe, mem_range] at hq₁ hq₂
      rw [Function.onFun, disjoint_left]
      intro w hw₁ hw₂
      have hc₁ := (mem_filter.mp hw₁).1
      have hc₂ := (mem_filter.mp hw₂).1
      simp only [cycInt, mem_image, mem_range] at hc₁ hc₂
      rcases hc₁ with ⟨d₁, hd₁, rfl⟩
      rcases hc₂ with ⟨d₂, hd₂, heq⟩
      rw [← natToFin_add, ← natToFin_add] at heq
      have hlt₁ : q₁ * W_len + d₁ < n := by
        have hm1 : (q₁ + 1) * W_len ≤ M * W_len := Nat.mul_le_mul_right W_len hq₁
        have hr1 : (q₁ + 1) * W_len = q₁ * W_len + W_len := by ring
        linarith only [hm1, hr1, hd₁, hMW]
      have hlt₂ : q₂ * W_len + d₂ < n := by
        have hm2 : (q₂ + 1) * W_len ≤ M * W_len := Nat.mul_le_mul_right W_len hq₂
        have hr2 : (q₂ + 1) * W_len = q₂ * W_len + W_len := by ring
        linarith only [hm2, hr2, hd₂, hMW]
      have hv := congrArg Fin.val heq
      simp only [val_natToFin, Nat.mod_eq_of_lt hlt₁, Nat.mod_eq_of_lt hlt₂] at hv
      have hr_c1 : q₁ * W_len = W_len * q₁ := by ring
      have hr_c2 : q₂ * W_len = W_len * q₂ := by ring
      have hv' : W_len * q₁ + d₁ = W_len * q₂ + d₂ := by linarith only [hv, hr_c1, hr_c2]
      exact hne (nat_mul_add_inj hd₁ hd₂ hv').1
    let V_bad := (range M).biUnion block
    have hVbad_card : M * (B1 + 1) ≤ #V_bad := by
      dsimp only [V_bad]
      rw [card_biUnion hblock_disj]
      calc M * (B1 + 1)
        _ = ∑ _q ∈ range M, (B1 + 1) := by simp
        _ ≤ ∑ q ∈ range M, #(block q) := sum_le_sum hblock_ge
    have hVbad_bad : ∀ v ∈ V_bad, isBad hk hn x v := by
      intro v hv
      rcases mem_biUnion.mp hv with ⟨q, _, hvq⟩
      exact (mem_filter.mp hvq).2
    have hU_ge := card_biUnion_badEdgesAt_ge hk hn x V_bad hVbad_bad
    have hU_le : #(V_bad.biUnion (badEdgesAt hk hn x)) ≤ #(nonnegEdges hn x) := by
      refine card_le_card fun e he => ?_
      rcases mem_biUnion.mp he with ⟨v, _, hev⟩
      exact badEdgesAt_subset_nonnegEdges hk hn x v hev
    have hVbad_k : 4 * 10 ^ 11 * k ≤ #V_bad := by
      have hB1_lb : k < 5 * 10 ^ 18 * (B1 + 1) :=
        hB1_eq ▸ Nat.lt_mul_div_succ k (by positivity : 0 < 5 * 10 ^ 18)
      have h1 : 2 * 10 ^ 30 * k ≤ 5 * 10 ^ 18 * (M * (B1 + 1)) := by
        calc 2 * 10 ^ 30 * k ≤ M * k := Nat.mul_le_mul_right k hM_lb
          _ ≤ M * (5 * 10 ^ 18 * (B1 + 1)) := Nat.mul_le_mul_left M hB1_lb.le
          _ = 5 * 10 ^ 18 * (M * (B1 + 1)) := by ring
      have h2 := Nat.mul_le_mul_left (5 * 10 ^ 18) hVbad_card
      linarith only [h1, h2]
    obtain ⟨B0, hB0_eq⟩ : ∃ B0, B0 = 3 * k ^ 2 / (2 * 10 ^ 9) := ⟨_, rfl⟩
    rw [← hB0_eq] at hU_ge
    have hB0_lb : k ^ 2 ≤ 10 ^ 9 * B0 := by
      have hd := Nat.div_add_mod (3 * k ^ 2) (2 * 10 ^ 9)
      rw [← hB0_eq] at hd
      have hm : 3 * k ^ 2 % (2 * 10 ^ 9) < 2 * 10 ^ 9 := Nat.mod_lt _ (by positivity)
      have hk_sq : 2 * 10 ^ 9 < k ^ 2 := by nlinarith only [hk_large]
      linarith only [hd, hm, hk_sq]
    have hprod_ge : 88 * (k * (k - 1) ^ 2) ≤ #V_bad * B0 := by
      have hk1_sq : (k - 1) ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left (Nat.sub_le k 1) 2
      have h1 : 400 * k ^ 3 ≤ #V_bad * B0 := by
        have hm := Nat.mul_le_mul hVbad_k hB0_lb
        have hr : (4 * 10 ^ 11 * k) * k ^ 2 = 10 ^ 9 * (400 * k ^ 3) := by ring
        have hr2 : #V_bad * (10 ^ 9 * B0) = 10 ^ 9 * (#V_bad * B0) := by ring
        rw [hr, hr2] at hm
        linarith only [hm]
      have h2 : 88 * (k * (k - 1) ^ 2) ≤ 88 * k ^ 3 := by
        have hm2 := Nat.mul_le_mul_left (88 * k) hk1_sq
        have hr1 : 88 * k * k ^ 2 = 88 * k ^ 3 := by ring
        have hr2 : 88 * k * (k - 1) ^ 2 = 88 * (k * (k - 1) ^ 2) := by ring
        linarith only [hm2, hr1, hr2]
      have hk3_0 : 0 ≤ k ^ 3 := Nat.zero_le _
      linarith only [h1, h2, hk3_0]
    have h88 : 88 * (k * (k - 1) ^ 2) ≤ 88 * #(nonnegEdges hn x) :=
      hprod_ge.trans (hU_ge.trans (Nat.mul_le_mul_left 88 hU_le))
    linarith only [h88, h_lt']

end PokrovskiyMain

theorem OMA.solution : OMA.R_ManickamMiklosSinghiConjecture_manickam_miklos_singhi_conjecture_variants_pokrovskiy_R1.H2 :=
  PokrovskiyMain.prove_H2
