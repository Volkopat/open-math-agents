import OMAStatements.S_erdos_776
import Mathlib


/-!
# Generic finite antichain infrastructure

The extremal problem uses finite families of finite sets on several different
ground-set types.  These definitions are intentionally independent of `Fin n`
so that constructions can add named points using sum types and transport the
result to a numerical ground set only at the end.
-/

namespace Erdos776.Antichain

open Finset

/-- A finite family of finite subsets of `α`. -/
abbrev Family (α : Type*) := Finset (Finset α)

/-- The Sperner/antichain property under set inclusion. -/
def IsSperner {α : Type*} (F : Family α) : Prop :=
  IsAntichain (· ⊆ ·) (F : Set (Finset α))

/-- The members of `F` on level `i`. -/
def level {α : Type*} [DecidableEq α] (F : Family α) (i : ℕ) : Family α :=
  F.filter fun s => s.card = i

@[simp] theorem mem_level {α : Type*} [DecidableEq α]
    {F : Family α} {i : ℕ} {s : Finset α} :
    s ∈ level F i ↔ s ∈ F ∧ s.card = i := by
  simp [level]

theorem level_mono {α : Type*} [DecidableEq α]
    {F G : Family α} (hFG : F ⊆ G) (i : ℕ) :
    level F i ⊆ level G i := by
  intro s hs
  exact mem_level.mpr ⟨hFG (mem_level.mp hs).1, (mem_level.mp hs).2⟩

/-- `F` contains at least `r` members on level `i`. -/
def HasMultiplicityAt {α : Type*} [DecidableEq α]
    (F : Family α) (r i : ℕ) : Prop :=
  r ≤ (level F i).card

/-- `F` contains at least `r` members on every level from `lo` through `hi`. -/
def HasMultiplicities {α : Type*} [DecidableEq α]
    (F : Family α) (r lo hi : ℕ) : Prop :=
  ∀ i, lo ≤ i → i ≤ hi → HasMultiplicityAt F r i

/-- A set which contains no member of `F`. -/
def FreeFor {α : Type*} (F : Family α) (d : Finset α) : Prop :=
  ∀ c ∈ F, ¬ c ⊆ d

/-- Every member of `D` is free for `F`. -/
def IsFreeFamily {α : Type*} (F D : Family α) : Prop :=
  ∀ d ∈ D, FreeFor F d

/-- Map every set in a family along an embedding of ground sets. -/
def mapFamily {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (F : Family α) : Family β :=
  F.map (Finset.mapEmbedding e).toEmbedding

@[simp] theorem mem_mapFamily {α β : Type*} [DecidableEq α] [DecidableEq β]
    {e : α ↪ β} {F : Family α} {t : Finset β} :
    t ∈ mapFamily e F ↔ ∃ s ∈ F, s.map e = t := by
  simp only [mapFamily, mem_map]
  constructor
  · rintro ⟨s, hs, hst⟩
    exact ⟨s, hs, (Finset.mapEmbedding_apply (f := e) (s := s)).symm.trans hst⟩
  · rintro ⟨s, hs, hst⟩
    exact ⟨s, hs, (Finset.mapEmbedding_apply (f := e) (s := s)).trans hst⟩

@[simp] theorem card_mapFamily {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (F : Family α) :
    (mapFamily e F).card = F.card := by
  simp [mapFamily]

theorem level_mapFamily {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (F : Family α) (i : ℕ) :
    level (mapFamily e F) i = mapFamily e (level F i) := by
  ext t
  constructor
  · intro ht
    obtain ⟨htF, htcard⟩ := mem_level.mp ht
    obtain ⟨s, hs, hst⟩ := mem_mapFamily.mp htF
    subst t
    apply mem_mapFamily.mpr
    exact ⟨s, mem_level.mpr ⟨hs, by simpa using htcard⟩, rfl⟩
  · intro ht
    obtain ⟨s, hs, hst⟩ := mem_mapFamily.mp ht
    subst t
    apply mem_level.mpr
    exact ⟨mem_mapFamily.mpr ⟨s, (mem_level.mp hs).1, rfl⟩,
      by simpa using (mem_level.mp hs).2⟩

@[simp] theorem card_level_mapFamily
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ↪ β) (F : Family α) (i : ℕ) :
    (level (mapFamily e F) i).card = (level F i).card := by
  rw [level_mapFamily, card_mapFamily]

theorem isSperner_mapFamily
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {e : α ↪ β} {F : Family α} (hF : IsSperner F) :
    IsSperner (mapFamily e F) := by
  intro s hs t ht hst hsub
  obtain ⟨u, hu, rfl⟩ := mem_mapFamily.mp hs
  obtain ⟨v, hv, rfl⟩ := mem_mapFamily.mp ht
  have huv : u ⊆ v := Finset.map_subset_map.mp hsub
  have huv_eq : u = v := hF.eq hu hv huv
  apply hst
  rw [huv_eq]

theorem freeFor_map
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {e : α ↪ β} {F : Family α} {d : Finset α}
    (hd : FreeFor F d) :
    FreeFor (mapFamily e F) (d.map e) := by
  intro t ht htd
  obtain ⟨s, hs, rfl⟩ := mem_mapFamily.mp ht
  exact hd s hs (Finset.map_subset_map.mp htd)

end Erdos776.Antichain


/-!
# Numerical binomial cascades

This file defines the numerical objects used in the cascade formulation of
Kruskal--Katona.  The colex/set-family semantics are added in
`CascadeFamily.lean`; keeping the arithmetic representation separate makes it
possible to test the indexing conventions before introducing finite sets.
-/

namespace Erdos776.KruskalKatona

/--
The value of digits `aₖ, aₖ₋₁, ...` placed at consecutive lower indices
`k, k-1, ...`.
-/
def cascadeValue : ℕ → List ℕ → ℕ
  | _, [] => 0
  | k, a :: digits => a.choose k + cascadeValue (k - 1) digits

@[simp] theorem cascadeValue_nil (k : ℕ) : cascadeValue k [] = 0 := rfl

@[simp] theorem cascadeValue_cons (k a : ℕ) (digits : List ℕ) :
    cascadeValue k (a :: digits) = a.choose k + cascadeValue (k - 1) digits := rfl

theorem cascadeValue_append (k : ℕ) (xs ys : List ℕ) :
    cascadeValue k (xs ++ ys) =
      cascadeValue k xs + cascadeValue (k - xs.length) ys := by
  induction xs generalizing k with
  | nil => simp
  | cons a xs ih =>
      simp only [List.cons_append, cascadeValue_cons, List.length_cons]
      rw [ih]
      rw [show k - (xs.length + 1) = k - 1 - xs.length by omega]
      omega

/-- The value obtained by lowering every lower binomial index by one. -/
def cascadeShadowValue (k : ℕ) (digits : List ℕ) : ℕ :=
  cascadeValue (k - 1) digits

@[simp] theorem cascadeShadowValue_nil (k : ℕ) :
    cascadeShadowValue k [] = 0 := rfl

@[simp] theorem cascadeShadowValue_cons (k a : ℕ) (digits : List ℕ) :
    cascadeShadowValue k (a :: digits) =
      a.choose (k - 1) + cascadeValue (k - 2) digits := by
  simp only [cascadeShadowValue, cascadeValue_cons]
  rw [show k - 1 - 1 = k - 2 by omega]

theorem cascadeShadowValue_append (k : ℕ) (xs ys : List ℕ) :
    cascadeShadowValue k (xs ++ ys) =
      cascadeShadowValue k xs +
        cascadeValue (k - 1 - xs.length) ys := by
  unfold cascadeShadowValue
  rw [cascadeValue_append]

/--
`digits` is a canonical `k`-cascade: every digit is at least its lower index,
the lower indices are consecutive and positive, and the upper digits strictly
decrease.  Consecutive lower indices are built into the recursion.
-/
def IsCanonical : ℕ → List ℕ → Prop
  | _, [] => True
  | 0, _ :: _ => False
  | k + 1, a :: digits =>
      k + 1 ≤ a ∧ (∀ b ∈ digits, b < a) ∧ IsCanonical k digits

@[simp] theorem isCanonical_nil (k : ℕ) : IsCanonical k [] := by
  cases k <;> trivial

@[simp] theorem isCanonical_zero_cons (a : ℕ) (digits : List ℕ) :
    ¬ IsCanonical 0 (a :: digits) := by simp [IsCanonical]

@[simp] theorem isCanonical_succ_cons (k a : ℕ) (digits : List ℕ) :
    IsCanonical (k + 1) (a :: digits) ↔
      k + 1 ≤ a ∧ (∀ b ∈ digits, b < a) ∧ IsCanonical k digits := by
  rfl

theorem isCanonical_cons_of_pos {k a : ℕ} {digits : List ℕ} (hk : 0 < k) :
    IsCanonical k (a :: digits) ↔
      k ≤ a ∧ (∀ b ∈ digits, b < a) ∧ IsCanonical (k - 1) digits := by
  cases k with
  | zero => omega
  | succ k => rfl

theorem IsCanonical.length_le {k : ℕ} {digits : List ℕ}
    (h : IsCanonical k digits) : digits.length ≤ k := by
  induction k generalizing digits with
  | zero =>
      cases digits with
      | nil => simp
      | cons => simp at h
  | succ k ih =>
      cases digits with
      | nil => simp
      | cons a digits =>
          simp only [isCanonical_succ_cons] at h
          simp only [List.length_cons, Nat.add_le_add_iff_right]
          exact ih h.2.2

theorem IsCanonical.head_le {k a : ℕ} {digits : List ℕ}
    (h : IsCanonical k (a :: digits)) : k ≤ a := by
  cases k with
  | zero => simp at h
  | succ k => exact h.1

theorem isCanonical_singleton {k a : ℕ} (hk : 1 ≤ k) (hka : k ≤ a) :
    IsCanonical k [a] := by
  cases k with
  | zero => omega
  | succ k => simp [IsCanonical, hka]

theorem IsCanonical.tail {k a : ℕ} {digits : List ℕ}
    (h : IsCanonical k (a :: digits)) : IsCanonical (k - 1) digits := by
  cases k with
  | zero => simp at h
  | succ k => exact h.2.2

theorem IsCanonical.tail_lt_head {k a : ℕ} {digits : List ℕ}
    (h : IsCanonical k (a :: digits)) {b : ℕ} (hb : b ∈ digits) : b < a := by
  cases k with
  | zero => simp at h
  | succ k => exact h.2.1 b hb

theorem IsCanonical.all_lt_of_head {k b : ℕ} {digits : List ℕ}
    (h : IsCanonical k (b :: digits)) {n : ℕ}
    (hb : b < n) : ∀ a ∈ b :: digits, a < n := by
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact hb
  · exact (h.tail_lt_head ha).trans hb

/-- Lowering every occupied cascade position preserves canonicity. -/
theorem IsCanonical.lowerIndex
    {k k' : ℕ} {digits : List ℕ} (h : IsCanonical k digits)
    (hkk : k' ≤ k) (hlen : digits.length ≤ k') :
    IsCanonical k' digits := by
  induction digits generalizing k k' with
  | nil => simp
  | cons a digits ih =>
      cases k' with
      | zero => simp at hlen
      | succ k' =>
          cases k with
          | zero => simp at h
          | succ k =>
              simp only [isCanonical_succ_cons] at h ⊢
              refine ⟨hkk.trans h.1, h.2.1, ?_⟩
              apply ih h.2.2 (by omega)
              simpa using hlen

/-- Concatenate two canonical cascades whose digits are separated. -/
theorem isCanonical_append
    {k : ℕ} {xs ys : List ℕ}
    (hxs : IsCanonical k xs)
    (hys : IsCanonical (k - xs.length) ys)
    (hcross : ∀ a ∈ xs, ∀ b ∈ ys, b < a) :
    IsCanonical k (xs ++ ys) := by
  induction xs generalizing k with
  | nil => simpa using hys
  | cons a xs ih =>
      cases k with
      | zero => simp at hxs
      | succ k =>
          simp only [List.cons_append, isCanonical_succ_cons] at hxs ⊢
          refine ⟨hxs.1, ?_, ?_⟩
          · intro b hb
            rcases List.mem_append.mp hb with hb | hb
            · exact hxs.2.1 b hb
            · exact hcross a List.mem_cons_self b hb
          · apply ih hxs.2.2
              (by simpa [List.length_cons] using hys)
            intro c hc b hb
            exact hcross c (List.mem_cons_of_mem a hc) b hb

/-! ### Diagonal (unary) runs -/

/-- `a, a-1, ...` with the requested number of terms. -/
def diagonalDigits : ℕ → ℕ → List ℕ
  | _, 0 => []
  | a, len + 1 => a :: diagonalDigits (a - 1) len

@[simp] theorem diagonalDigits_zero (a : ℕ) : diagonalDigits a 0 = [] := rfl

@[simp] theorem diagonalDigits_succ (a len : ℕ) :
    diagonalDigits a (len + 1) = a :: diagonalDigits (a - 1) len := rfl

theorem mem_diagonalDigits_le {a len d : ℕ}
    (hd : d ∈ diagonalDigits a len) : d ≤ a := by
  induction len generalizing a with
  | zero => simp at hd
  | succ len ih =>
      rcases List.mem_cons.mp hd with rfl | hd
      · exact le_rfl
      · exact (ih hd).trans (Nat.sub_le a 1)

theorem isCanonical_diagonalDigits {a len : ℕ} (hlen : len ≤ a) :
    IsCanonical a (diagonalDigits a len) := by
  induction len generalizing a with
  | zero => simp
  | succ len ih =>
      cases a with
      | zero => omega
      | succ a =>
          simp only [diagonalDigits_succ, Nat.add_sub_cancel,
            isCanonical_succ_cons]
          refine ⟨le_rfl, ?_, ih (by omega)⟩
          intro d hd
          exact lt_of_le_of_lt (mem_diagonalDigits_le hd) (Nat.lt_succ_self a)

theorem cascadeValue_diagonalDigits {a len : ℕ} (hlen : len ≤ a) :
    cascadeValue a (diagonalDigits a len) = len := by
  induction len generalizing a with
  | zero => simp
  | succ len ih =>
      cases a with
      | zero => omega
      | succ a =>
          have hi := ih (a := a) (by omega)
          simp only [diagonalDigits_succ, cascadeValue_cons, Nat.add_sub_cancel,
            Nat.choose_self]
          rw [hi]
          omega

/-- The lowered value of the full diagonal run is `1 + ... + a`. -/
theorem cascadeShadowValue_diagonalDigits_full (a : ℕ) :
    cascadeShadowValue a (diagonalDigits a a) = (a + 1).choose 2 := by
  induction a with
  | zero => simp [cascadeShadowValue]
  | succ a ih =>
      simp only [diagonalDigits_succ, cascadeShadowValue_cons,
        Nat.add_sub_cancel, show a + 1 - 2 = a - 1 by omega]
      rw [show cascadeValue (a - 1) (diagonalDigits a a) =
          cascadeShadowValue a (diagonalDigits a a) by rfl, ih]
      have hp : (a + 1 + 1).choose 2 = a + 1 + (a + 1).choose 2 := by
        simpa [Nat.choose_one_right] using Nat.choose_succ_succ (a + 1) 1
      rw [hp]
      simp

/-- The lowered value of an arbitrary initial diagonal run. -/
theorem cascadeShadowValue_diagonalDigits {a len : ℕ} (hlen : len ≤ a) :
    cascadeShadowValue a (diagonalDigits a len) =
      (a + 1).choose 2 - (a + 1 - len).choose 2 := by
  induction len generalizing a with
  | zero => simp
  | succ len ih =>
      cases a with
      | zero => omega
      | succ a =>
          have hlen' : len ≤ a := by omega
          have hi := ih (a := a) hlen'
          simp only [diagonalDigits_succ, cascadeShadowValue_cons,
            Nat.add_sub_cancel, show a + 1 - 2 = a - 1 by omega]
          rw [show cascadeValue (a - 1) (diagonalDigits a len) =
              cascadeShadowValue a (diagonalDigits a len) by rfl,
            hi]
          have hp : (a + 2).choose 2 = a + 1 + (a + 1).choose 2 := by
            simpa [Nat.choose_one_right] using Nat.choose_succ_succ (a + 1) 1
          rw [show (a + 1).choose a = a + 1 by
              exact Nat.choose_succ_self_right a,
            hp]
          have hidx : a + 1 + 1 - (len + 1) = a + 1 - len := by omega
          rw [hidx]
          have hchoose : (a + 1 - len).choose 2 ≤ (a + 1).choose 2 :=
            Nat.choose_le_choose 2 (Nat.sub_le (a + 1) len)
          omega

/-- The lowered value of the diagonal run ending at digit `2`. -/
theorem cascadeShadowValue_diagonalDigits_drop_one (a : ℕ) :
    cascadeShadowValue a (diagonalDigits a (a - 1)) =
      (a + 1).choose 2 - 1 := by
  induction a with
  | zero => simp [cascadeShadowValue]
  | succ a ih =>
      cases a with
      | zero => simp [cascadeShadowValue]
      | succ a =>
          simp only [diagonalDigits_succ,
            cascadeShadowValue_cons,
            show a + 1 + 1 - 1 = a + 1 by omega,
            show a + 1 + 1 - 2 = a by omega]
          rw [show cascadeValue a (diagonalDigits (a + 1) a) =
              cascadeShadowValue (a + 1) (diagonalDigits (a + 1) a) by rfl]
          have hi : cascadeShadowValue (a + 1) (diagonalDigits (a + 1) a) =
              (a + 2).choose 2 - 1 := by simpa using ih
          rw [hi]
          have hp : (a + 3).choose 2 = a + 2 + (a + 2).choose 2 := by
            simpa [Nat.choose_one_right] using Nat.choose_succ_succ (a + 2) 1
          have hpos : 1 ≤ (a + 2).choose 2 := Nat.choose_pos (by omega)
          rw [show a + 1 + 1 + 1 = a + 3 by omega,
            show (a + 1 + 1).choose (a + 1) = a + 2 by
              exact Nat.choose_succ_self_right (a + 1), hp]
          omega

end Erdos776.KruskalKatona


/-!
# Set families represented by numerical cascades

For canonical digits `aₖ > aₖ₋₁ > ...`, `cascadeFamily k digits` is the
recursive colex family consisting of all `k`-subsets below `aₖ`, followed by
sets containing `aₖ` whose remainders belong to the tail family.
-/

namespace Erdos776.KruskalKatona

open Finset

/-- The concrete finite family encoded by a list of cascade digits. -/
def cascadeFamily : ℕ → List ℕ → Finset (Finset ℕ)
  | _, [] => ∅
  | 0, _ :: _ => {∅}
  | k + 1, a :: digits =>
      (range a).powersetCard (k + 1) ∪
        (cascadeFamily k digits).image (insert a)

@[simp] theorem cascadeFamily_nil (k : ℕ) : cascadeFamily k [] = ∅ := by
  cases k <;> rfl

@[simp] theorem cascadeFamily_zero_cons (a : ℕ) (digits : List ℕ) :
    cascadeFamily 0 (a :: digits) = {∅} := rfl

@[simp] theorem cascadeFamily_succ_cons (k a : ℕ) (digits : List ℕ) :
    cascadeFamily (k + 1) (a :: digits) =
      (range a).powersetCard (k + 1) ∪
      (cascadeFamily k digits).image (insert a) := rfl

/--
The diagonal cascade of length `len` consists of the first `len` colex
`a`-sets: the sets obtained from `range (a+1)` by deleting one of its final
`len` points.
-/
theorem erase_range_mem_cascadeFamily_diagonalDigits
    {a len j : ℕ} (hlen : len ≤ a)
    (hjlow : a + 1 - len ≤ j) (hjhigh : j ≤ a) :
    (range (a + 1)).erase j ∈
      cascadeFamily a (diagonalDigits a len) := by
  induction len generalizing a j with
  | zero => omega
  | succ len ih =>
      cases a with
      | zero => omega
      | succ a =>
          simp only [diagonalDigits_succ, cascadeFamily_succ_cons]
          by_cases hja : j = a + 1
          · subst j
            apply mem_union_left
            apply mem_powersetCard.mpr
            have heq : (range (a + 1 + 1)).erase (a + 1) = range (a + 1) := by
              ext x
              simp
              omega
            rw [heq]
            simp
          · apply mem_union_right
            apply mem_image.mpr
            refine ⟨(range (a + 1)).erase j, ?_, ?_⟩
            · apply ih (by omega) (by omega) (by omega)
            · ext x
              simp
              omega

/-- Every point used by the family is below some cascade digit. -/
theorem mem_cascadeFamily_lt_of_digits_lt
    {k A : ℕ} {digits : List ℕ} {s : Finset ℕ}
    (hdigits : ∀ d ∈ digits, d < A)
    (hs : s ∈ cascadeFamily k digits) : ∀ x ∈ s, x < A := by
  induction k generalizing digits s with
  | zero =>
      cases digits with
      | nil => simp at hs
      | cons =>
          simp at hs
          subst s
          simp
  | succ k ih =>
      cases digits with
      | nil => simp at hs
      | cons a digits =>
          simp only [cascadeFamily_succ_cons, mem_union, mem_powersetCard,
            mem_image] at hs
          intro x hx
          rcases hs with hs | ⟨t, ht, hst⟩
          · exact (Finset.mem_range.mp (hs.1 hx)).trans
              (hdigits a (List.mem_cons_self))
          · subst s
            rcases mem_insert.mp hx with hxa | hx
            · subst x
              exact hdigits a (List.mem_cons_self)
            · exact ih (fun d hd => hdigits d (List.mem_cons_of_mem a hd)) ht x hx

/-- Tail-family members do not contain the preceding canonical digit. -/
theorem IsCanonical.head_notMem_tail_family
    {k a : ℕ} {digits : List ℕ} (h : IsCanonical (k + 1) (a :: digits))
    {s : Finset ℕ} (hs : s ∈ cascadeFamily k digits) : a ∉ s := by
  intro ha
  exact (Nat.lt_irrefl a) <|
    mem_cascadeFamily_lt_of_digits_lt h.2.1 hs a ha

/-- Every member has the lower index prescribed by the cascade. -/
theorem sized_cascadeFamily {k : ℕ} {digits : List ℕ}
    (h : IsCanonical k digits) :
    (cascadeFamily k digits : Set (Finset ℕ)).Sized k := by
  induction k generalizing digits with
  | zero =>
      cases digits with
      | nil => simp
      | cons => simp at h
  | succ k ih =>
      cases digits with
      | nil => simp
      | cons a digits =>
          intro s hs
          rw [cascadeFamily_succ_cons, mem_coe, mem_union] at hs
          rcases hs with hs | hs
          · exact (mem_powersetCard.mp hs).2
          · obtain ⟨t, ht, rfl⟩ := mem_image.mp hs
            rw [card_insert_of_notMem (h.head_notMem_tail_family ht)]
            exact congrArg (· + 1) (ih h.2.2 ht)

/-- The full block of `k+1`-sets below `a` shadows to the full `k`-block. -/
theorem shadow_powersetCard_range {k a : ℕ} (hka : k + 1 ≤ a) :
    Finset.shadow ((range a).powersetCard (k + 1)) =
      (range a).powersetCard k := by
  ext t
  simp only [mem_shadow_iff, mem_powersetCard]
  constructor
  · rintro ⟨s, hs, x, hx, rfl⟩
    refine ⟨fun y hy => hs.1 (mem_of_mem_erase hy), ?_⟩
    rw [card_erase_of_mem hx, hs.2]
    omega
  · rintro ⟨htrange, htcard⟩
    have hcard : t.card < (range a).card := by
      simp only [card_range, htcard]
      omega
    obtain ⟨x, hx⟩ := sdiff_nonempty_of_card_lt_card hcard
    have hxrange : x ∈ range a := (mem_sdiff.mp hx).1
    have hxnot : x ∉ t := (mem_sdiff.mp hx).2
    refine ⟨insert x t, ?_, x, mem_insert_self x t, erase_insert hxnot⟩
    refine ⟨?_, ?_⟩
    · exact insert_subset hxrange htrange
    · rw [card_insert_of_notMem hxnot, htcard]

/--
Shadowing one recursive colex block: removing the new largest point either
lands in the full lower block, or removes a point from the tail family.
-/
theorem shadow_fullBlock_union_insert
    {k a : ℕ} {T : Finset (Finset ℕ)}
    (hka : k + 1 ≤ a)
    (hsize : (T : Set (Finset ℕ)).Sized k)
    (hbound : ∀ s ∈ T, s ⊆ range a) :
    Finset.shadow
        ((range a).powersetCard (k + 1) ∪ T.image (insert a)) =
      (range a).powersetCard k ∪ (Finset.shadow T).image (insert a) := by
  ext t
  constructor
  · intro ht
    obtain ⟨s, hs, x, hx, hxt⟩ := mem_shadow_iff.mp ht
    rcases mem_union.mp hs with hs | hs
    · apply mem_union_left
      rw [← shadow_powersetCard_range hka]
      exact hxt ▸ erase_mem_shadow hs hx
    · obtain ⟨u, hu, hsu⟩ := mem_image.mp hs
      subst s
      have hau : a ∉ u := by
        intro ha
        exact (Finset.mem_range.mp (hbound u hu ha)).false
      rcases mem_insert.mp hx with hxa | hxu
      · subst x
        rw [erase_insert hau] at hxt
        subst t
        apply mem_union_left
        exact mem_powersetCard.mpr ⟨hbound u hu, hsize hu⟩
      · have hxa : a ≠ x := fun h => hau (h ▸ hxu)
        rw [erase_insert_of_ne hxa] at hxt
        subst t
        apply mem_union_right
        exact mem_image.mpr ⟨u.erase x, erase_mem_shadow hu hxu, rfl⟩
  · intro ht
    rcases mem_union.mp ht with ht | ht
    · have ht' : t ∈ Finset.shadow ((range a).powersetCard (k + 1)) := by
        rwa [shadow_powersetCard_range hka]
      exact shadow_mono subset_union_left ht'
    · obtain ⟨v, hv, rfl⟩ := mem_image.mp ht
      obtain ⟨u, hu, x, hxu, hxv⟩ := mem_shadow_iff.mp hv
      have hau : a ∉ u := by
        intro ha
        exact (Finset.mem_range.mp (hbound u hu ha)).false
      have hax : a ≠ x := fun h => hau (h ▸ hxu)
      apply mem_shadow_iff.mpr
      refine ⟨insert a u, mem_union.mpr (Or.inr (mem_image.mpr ⟨u, hu, rfl⟩)),
        x, mem_insert_of_mem hxu, ?_⟩
      rw [erase_insert_of_ne hax, hxv]

/-- A canonical cascade shadows term by term. -/
theorem shadow_cascadeFamily {k : ℕ} {digits : List ℕ}
    (h : IsCanonical k digits) :
    Finset.shadow (cascadeFamily k digits) =
      cascadeFamily (k - 1) digits := by
  induction k generalizing digits with
  | zero =>
      cases digits with
      | nil => simp
      | cons => simp at h
  | succ k ih =>
      cases digits with
      | nil => simp
      | cons a digits =>
          have htail : IsCanonical k digits := h.2.2
          have hbound : ∀ s ∈ cascadeFamily k digits, s ⊆ range a := by
            intro s hs x hx
            exact mem_range.mpr <| mem_cascadeFamily_lt_of_digits_lt h.2.1 hs x hx
          rw [cascadeFamily_succ_cons,
            shadow_fullBlock_union_insert h.1 (sized_cascadeFamily htail) hbound]
          cases k with
          | zero =>
              cases digits with
              | nil => simp
              | cons => simp at htail
          | succ k =>
              rw [ih htail]
              rfl

/-- `cascadeFamily` has exactly the cardinality represented by its digits. -/
theorem card_cascadeFamily {k : ℕ} {digits : List ℕ}
    (h : IsCanonical k digits) :
    (cascadeFamily k digits).card = cascadeValue k digits := by
  induction k generalizing digits with
  | zero =>
      cases digits with
      | nil => simp
      | cons => simp at h
  | succ k ih =>
      cases digits with
      | nil => simp
      | cons a digits =>
          have htail : IsCanonical k digits := h.2.2
          have hnot : ∀ s ∈ cascadeFamily k digits, a ∉ s :=
            fun s hs => h.head_notMem_tail_family hs
          have hinj : Set.InjOn (insert a) (cascadeFamily k digits : Set (Finset ℕ)) := by
            intro s hs t ht hst
            have hs' := hnot s hs
            have ht' := hnot t ht
            have herase := congrArg (erase · a) hst
            simpa [hs', ht'] using herase
          have hdisjoint :
              Disjoint ((range a).powersetCard (k + 1))
                ((cascadeFamily k digits).image (insert a)) := by
            rw [Finset.disjoint_left]
            intro s hs hsi
            obtain ⟨t, ht, rfl⟩ := mem_image.mp hsi
            have ha_range := (mem_powersetCard.mp hs).1 (mem_insert_self a t)
            simp at ha_range
          rw [cascadeFamily_succ_cons, card_union_of_disjoint hdisjoint,
            card_powersetCard, card_range, card_image_of_injOn hinj, ih htail]
          rfl

/-- The lowered family has the cardinality obtained by lowering every index. -/
theorem card_lowered_cascadeFamily {k : ℕ} {digits : List ℕ}
    (h : IsCanonical k digits) :
    (cascadeFamily (k - 1) digits).card = cascadeValue (k - 1) digits := by
  induction k generalizing digits with
  | zero =>
      cases digits with
      | nil => simp
      | cons => simp at h
  | succ k ih =>
      cases digits with
      | nil => simp
      | cons a digits =>
          have htail : IsCanonical k digits := h.2.2
          cases k with
          | zero =>
              cases digits with
              | nil => simp [cascadeValue]
              | cons => simp at htail
          | succ k =>
              have hnot : ∀ s ∈ cascadeFamily k digits, a ∉ s := by
                intro s hs ha
                exact (Nat.lt_irrefl a) <|
                  mem_cascadeFamily_lt_of_digits_lt h.2.1 hs a ha
              have hinj :
                  Set.InjOn (insert a) (cascadeFamily k digits : Set (Finset ℕ)) := by
                intro s hs t ht hst
                have herase := congrArg (erase · a) hst
                simpa [hnot s hs, hnot t ht] using herase
              have hdisjoint :
                  Disjoint ((range a).powersetCard (k + 1))
                    ((cascadeFamily k digits).image (insert a)) := by
                rw [Finset.disjoint_left]
                intro s hs hsi
                obtain ⟨t, ht, rfl⟩ := mem_image.mp hsi
                have ha_range := (mem_powersetCard.mp hs).1 (mem_insert_self a t)
                simp at ha_range
              have hi :
                  (cascadeFamily k digits).card = cascadeValue k digits := by
                simpa using ih htail
              rw [show k + 1 + 1 - 1 = k + 1 by omega,
                cascadeFamily_succ_cons, card_union_of_disjoint hdisjoint,
                card_powersetCard, card_range, card_image_of_injOn hinj, hi]
              rfl

/-- The cardinal form of termwise cascade shadowing. -/
theorem card_shadow_cascadeFamily {k : ℕ} {digits : List ℕ}
    (h : IsCanonical k digits) :
    (Finset.shadow (cascadeFamily k digits)).card =
      cascadeShadowValue k digits := by
  rw [shadow_cascadeFamily h, card_lowered_cascadeFamily h]
  rfl

/-- Adding a full block below `a` to a bounded initial segment preserves colex initiality. -/
theorem isInitSeg_fullBlock_union_insert
    {k a : ℕ} {T : Finset (Finset ℕ)}
    (hT : Finset.Colex.IsInitSeg T k)
    (hbound : ∀ s ∈ T, s ⊆ range a) :
    Finset.Colex.IsInitSeg
      ((range a).powersetCard (k + 1) ∪ T.image (insert a)) (k + 1) := by
  constructor
  · intro s hs
    rcases mem_union.mp hs with hs | hs
    · exact (mem_powersetCard.mp hs).2
    · obtain ⟨u, hu, rfl⟩ := mem_image.mp hs
      have hau : a ∉ u := by
        intro ha
        exact (mem_range.mp (hbound u hu ha)).false
      rw [card_insert_of_notMem hau, hT.1 hu]
  · intro s t hs ht
    rcases mem_union.mp hs with hs | hs
    · apply mem_union_left
      exact mem_powersetCard.mpr ⟨fun x hx => mem_range.mpr <|
        Finset.Colex.forall_lt_mono ht.1.le
          (fun y hy => mem_range.mp ((mem_powersetCard.mp hs).1 hy)) x hx, ht.2⟩
    · obtain ⟨u, hu, rfl⟩ := mem_image.mp hs
      have hau : a ∉ u := by
        intro ha
        exact (mem_range.mp (hbound u hu ha)).false
      by_cases hat : a ∈ t
      · apply mem_union_right
        refine mem_image.mpr ⟨t.erase a, ?_, insert_erase hat⟩
        apply hT.2 hu
        refine ⟨?_, ?_⟩
        · have hremove :=
            (Finset.Colex.toColex_sdiff_lt_toColex_sdiff
              (s := t) (t := insert a u) (u := {a})
              (by simpa using hat) (by simp)).2 ht.1
          simpa [sdiff_singleton_eq_erase, hau] using hremove
        · rw [card_erase_of_mem hat, ht.2]
          omega
      · apply mem_union_left
        refine mem_powersetCard.mpr ⟨?_, ht.2⟩
        intro x hx
        have hle : x ≤ a :=
          Finset.Colex.forall_le_mono ht.1.le (fun y hy => by
            rcases mem_insert.mp hy with rfl | hy
            · exact le_rfl
            · exact (mem_range.mp (hbound u hu hy)).le) x hx
        have hne : x ≠ a := fun hxa => hat (hxa ▸ hx)
        exact mem_range.mpr (lt_of_le_of_ne hle hne)

/-- The recursively represented canonical family is a colex initial segment. -/
theorem isInitSeg_cascadeFamily {k : ℕ} {digits : List ℕ}
    (h : IsCanonical k digits) :
    Finset.Colex.IsInitSeg (cascadeFamily k digits) k := by
  induction k generalizing digits with
  | zero =>
      cases digits with
      | nil => simp
      | cons => simp at h
  | succ k ih =>
      cases digits with
      | nil => simp
      | cons a digits =>
          have htail : IsCanonical k digits := h.2.2
          have hbound : ∀ s ∈ cascadeFamily k digits, s ⊆ range a := by
            intro s hs x hx
            exact mem_range.mpr <| mem_cascadeFamily_lt_of_digits_lt h.2.1 hs x hx
          rw [cascadeFamily_succ_cons]
          exact isInitSeg_fullBlock_union_insert (ih htail) hbound

end Erdos776.KruskalKatona


/-!
# Greedy normal form for binomial cascades

Mathlib's Kruskal--Katona development deliberately leaves the numerical
cascade representation as a TODO.  This file supplies it: every natural
number has a canonical `k`-cascade for `k > 0`, obtained by repeatedly taking
the largest possible upper binomial index.
-/

namespace Erdos776.KruskalKatona

/-- A simple finite bound large enough to contain the greedy head digit. -/
theorem lt_choose_add (m k : ℕ) (hk : 1 ≤ k) :
    m < (m + k).choose k := by
  induction m with
  | zero =>
      simpa only [Nat.zero_add] using (Nat.choose_pos (show k ≤ k from le_rfl))
  | succ m ih =>
      have hpos : 0 < (m + k).choose (k - 1) :=
        Nat.choose_pos (by omega)
      have hp : (m + 1 + k).choose k =
          (m + k).choose (k - 1) + (m + k).choose k := by
        simpa only [Nat.succ_eq_add_one, show k - 1 + 1 = k by omega,
          show m + k + 1 = m + 1 + k by omega] using
            Nat.choose_succ_succ (m + k) (k - 1)
      rw [hp]
      omega

/-- The largest `a ≤ m+k` with `choose a k ≤ m`. -/
def greedyHead (m k : ℕ) : ℕ :=
  Nat.findGreatest (fun a => a.choose k ≤ m) (m + k)

theorem greedyHead_spec {m k : ℕ} (hm : 0 < m) :
    (greedyHead m k).choose k ≤ m := by
  unfold greedyHead
  exact Nat.findGreatest_spec
    (P := fun a => a.choose k ≤ m) (m := k) (n := m + k)
    (by omega) (by simpa using Nat.succ_le_of_lt hm)

theorem le_greedyHead {m k : ℕ} (hm : 0 < m) :
    k ≤ greedyHead m k := by
  apply Nat.le_findGreatest
    (P := fun a => a.choose k ≤ m) (m := k) (n := m + k)
  · omega
  · simpa using Nat.succ_le_of_lt hm

theorem greedyHead_lt_bound {m k : ℕ} (hm : 0 < m) (hk : 1 ≤ k) :
    greedyHead m k < m + k := by
  have hle := Nat.findGreatest_le (P := fun a => a.choose k ≤ m) (m + k)
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hspec := greedyHead_spec (k := k) hm
  rw [heq] at hspec
  exact (Nat.not_lt_of_ge hspec) (lt_choose_add m k hk)

theorem greedyHead_next_gt {m k : ℕ} (hm : 0 < m) (hk : 1 ≤ k) :
    m < (greedyHead m k + 1).choose k := by
  have hnext : greedyHead m k + 1 ≤ m + k := by
    exact greedyHead_lt_bound hm hk
  have hnot := Nat.findGreatest_is_greatest
    (P := fun a => a.choose k ≤ m)
    (Nat.lt_succ_self (greedyHead m k)) hnext
  have hnot' : ¬(greedyHead m k + 1).choose k ≤ m := by
    simpa [Nat.succ_eq_add_one] using hnot
  omega

/-- The remainder after removing the greedy head fits below the next digit. -/
theorem greedyRemainder_lt {m k : ℕ} (hm : 0 < m) (hk : 1 ≤ k) :
    m - (greedyHead m k).choose k <
      (greedyHead m k).choose (k - 1) := by
  have hnext := greedyHead_next_gt hm hk
  have hspec := greedyHead_spec (k := k) hm
  have hp : (greedyHead m k + 1).choose k =
      (greedyHead m k).choose (k - 1) +
        (greedyHead m k).choose k := by
    simpa only [Nat.succ_eq_add_one, show k - 1 + 1 = k by omega] using
      Nat.choose_succ_succ (greedyHead m k) (k - 1)
  rw [hp] at hnext
  omega

/-- Greedy canonical digits, recursively indexed by the lower binomial index. -/
def canonicalDigits : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, m =>
      if m = 0 then []
      else
        let a := greedyHead m (k + 1)
        a :: canonicalDigits k (m - a.choose (k + 1))

@[simp] theorem canonicalDigits_zero (m : ℕ) : canonicalDigits 0 m = [] := rfl

@[simp] theorem canonicalDigits_succ_zero (k : ℕ) :
    canonicalDigits (k + 1) 0 = [] := by
  simp [canonicalDigits]

theorem canonicalDigits_succ_of_pos {k m : ℕ} (hm : 0 < m) :
    canonicalDigits (k + 1) m =
      greedyHead m (k + 1) ::
        canonicalDigits k (m - (greedyHead m (k + 1)).choose (k + 1)) := by
  simp [canonicalDigits, hm.ne']

/-- The greedy digits represent the original value. -/
theorem cascadeValue_canonicalDigits {k m : ℕ} (hk : 1 ≤ k) :
    cascadeValue k (canonicalDigits k m) = m := by
  induction k generalizing m with
  | zero => omega
  | succ k ih =>
      by_cases hm : m = 0
      · subst m
        simp
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        rw [canonicalDigits_succ_of_pos hmpos, cascadeValue_cons]
        have htail :
            cascadeValue k
                (canonicalDigits k
                  (m - (greedyHead m (k + 1)).choose (k + 1))) =
              m - (greedyHead m (k + 1)).choose (k + 1) := by
          by_cases hk0 : k = 0
          · subst k
            have hrem := greedyRemainder_lt hmpos (show 1 ≤ 0 + 1 by omega)
            simp at hrem ⊢
            omega
          · exact ih (Nat.one_le_iff_ne_zero.mpr hk0)
        rw [show k + 1 - 1 = k by omega, htail]
        exact Nat.add_sub_of_le (greedyHead_spec (k := k + 1) hmpos)

/-- Every greedy digit lies below any binomial bound which already exceeds `m`. -/
theorem canonicalDigits_all_lt
    {k m A : ℕ} (hk : 1 ≤ k) (hmA : m < A.choose k) :
    ∀ d ∈ canonicalDigits k m, d < A := by
  induction k generalizing m A with
  | zero => omega
  | succ k ih =>
      by_cases hm : m = 0
      · subst m
        simp
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        rw [canonicalDigits_succ_of_pos hmpos]
        have hheadA : greedyHead m (k + 1) < A := by
          by_contra hnot
          have hchoose : A.choose (k + 1) ≤
              (greedyHead m (k + 1)).choose (k + 1) :=
            Nat.choose_le_choose (k + 1) (by omega)
          exact (Nat.not_lt_of_ge
            (hchoose.trans (greedyHead_spec (k := k + 1) hmpos))) hmA
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact hheadA
        · by_cases hk0 : k = 0
          · subst k
            have hrem := greedyRemainder_lt hmpos (show 1 ≤ 0 + 1 by omega)
            simp at hrem hd
          · have hrem := greedyRemainder_lt hmpos (show 1 ≤ k + 1 by omega)
            rw [show k + 1 - 1 = k by omega] at hrem
            exact (ih (A := greedyHead m (k + 1))
                (Nat.one_le_iff_ne_zero.mpr hk0) hrem d hd).trans hheadA

/-- The greedy representation is canonical. -/
theorem isCanonical_canonicalDigits {k m : ℕ} (hk : 1 ≤ k) :
    IsCanonical k (canonicalDigits k m) := by
  induction k generalizing m with
  | zero => omega
  | succ k ih =>
      by_cases hm : m = 0
      · subst m
        simp
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        rw [canonicalDigits_succ_of_pos hmpos]
        rw [isCanonical_succ_cons]
        refine ⟨le_greedyHead (k := k + 1) hmpos, ?_, ?_⟩
        · by_cases hk0 : k = 0
          · subst k
            have hrem := greedyRemainder_lt hmpos (show 1 ≤ 0 + 1 by omega)
            simp at hrem
            simp [hrem]
          · have hrem := greedyRemainder_lt hmpos (show 1 ≤ k + 1 by omega)
            rw [show k + 1 - 1 = k by omega] at hrem
            exact canonicalDigits_all_lt
              (Nat.one_le_iff_ne_zero.mpr hk0) hrem
        · by_cases hk0 : k = 0
          · subst k
            simp
          · exact ih (Nat.one_le_iff_ne_zero.mpr hk0)

/-- A bounded canonical cascade is strictly below the next complete block. -/
theorem cascadeValue_lt_choose_of_all_lt
    {k A : ℕ} {digits : List ℕ}
    (hkA : k ≤ A) (hcanon : IsCanonical k digits)
    (hall : ∀ d ∈ digits, d < A) :
    cascadeValue k digits < A.choose k := by
  induction k generalizing A digits with
  | zero =>
      cases digits with
      | nil => simp
      | cons => simp at hcanon
  | succ k ih =>
      cases digits with
      | nil =>
          simp only [cascadeValue_nil]
          exact Nat.choose_pos hkA
      | cons a digits =>
          have haA : a < A := hall a List.mem_cons_self
          have htailcanon : IsCanonical k digits := hcanon.2.2
          have htailall : ∀ d ∈ digits, d < a := hcanon.2.1
          have htail : cascadeValue k digits < a.choose k :=
            ih ((Nat.le_succ k).trans hcanon.1) htailcanon htailall
          have hp : (a + 1).choose (k + 1) =
              a.choose k + a.choose (k + 1) := by
            simpa only [Nat.succ_eq_add_one] using Nat.choose_succ_succ a k
          have hmono : (a + 1).choose (k + 1) ≤ A.choose (k + 1) :=
            Nat.choose_le_choose (k + 1) (by omega)
          simp only [cascadeValue_cons, Nat.add_sub_cancel]
          omega

/-- A number bracketed by two consecutive binomials has that greedy head. -/
theorem greedyHead_eq_of_bounds
    {m k a : ℕ} (hk : 1 ≤ k) (ha : k ≤ a)
    (hle : a.choose k ≤ m) (hlt : m < (a + 1).choose k) :
    greedyHead m k = a := by
  have hm : 0 < m :=
    lt_of_lt_of_le (Nat.choose_pos ha) hle
  have habound : a ≤ m + k := by
    by_contra hnot
    have hmono : (m + k).choose k ≤ a.choose k :=
      Nat.choose_le_choose k (by omega)
    exact (Nat.not_lt_of_ge (hmono.trans hle)) (lt_choose_add m k hk)
  unfold greedyHead
  apply Nat.findGreatest_eq_iff.mpr
  refine ⟨habound, fun _ => hle, ?_⟩
  intro b hab hbbound hb
  have hmono : (a + 1).choose k ≤ b.choose k :=
    Nat.choose_le_choose k (by omega)
  omega

/-- Canonical binomial cascades are unique. -/
theorem canonicalDigits_unique
    {k m : ℕ} {digits : List ℕ}
    (hcanon : IsCanonical k digits)
    (hvalue : cascadeValue k digits = m) :
    digits = canonicalDigits k m := by
  induction k generalizing m digits with
  | zero =>
      cases digits with
      | nil => simp
      | cons => simp at hcanon
  | succ k ih =>
      by_cases hm : m = 0
      · have hvalue0 : cascadeValue (k + 1) digits = 0 := hvalue.trans hm
        have hdigits : digits = [] := by
          cases digits with
          | nil => rfl
          | cons a tail =>
              have hpos : 0 < a.choose (k + 1) := Nat.choose_pos hcanon.1
              simp only [cascadeValue_cons, Nat.add_sub_cancel] at hvalue0
              omega
        simp [hdigits, hm]
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        cases digits with
        | nil =>
            simp at hvalue
            omega
        | cons a tail =>
            have htailcanon : IsCanonical k tail := hcanon.2.2
            have htaillt : cascadeValue k tail < a.choose k :=
              cascadeValue_lt_choose_of_all_lt
                ((Nat.le_succ k).trans hcanon.1) htailcanon hcanon.2.1
            have hvalue' : a.choose (k + 1) + cascadeValue k tail = m := by
              simpa only [cascadeValue_cons, Nat.add_sub_cancel] using hvalue
            have hle : a.choose (k + 1) ≤ m := by omega
            have hp : (a + 1).choose (k + 1) =
                a.choose k + a.choose (k + 1) := by
              simpa only [Nat.succ_eq_add_one] using Nat.choose_succ_succ a k
            have hlt : m < (a + 1).choose (k + 1) := by omega
            have hhead : greedyHead m (k + 1) = a :=
              greedyHead_eq_of_bounds (by omega) hcanon.1 hle hlt
            have htailvalue : cascadeValue k tail = m - a.choose (k + 1) := by
              omega
            have htail : tail = canonicalDigits k (m - a.choose (k + 1)) :=
              ih htailcanon htailvalue
            rw [canonicalDigits_succ_of_pos hmpos, hhead]
            exact congrArg (List.cons a) htail

end Erdos776.KruskalKatona


/-!
# The core-to-full construction

A core antichain supplies levels `2, ..., ⌊n/2⌋-1`.  We adjoin a pivot and
private points, attach the pivot to every core member, add the private pairs,
and finally take these lower members together with their complements.  The
result supplies every level `2, ..., n-2`.

The ground set is given a named decomposition into core points, one pivot,
`r` private points, and arbitrary spare points.  This makes the construction
fully explicit and avoids cardinality-choice axioms.
-/

namespace Erdos776.Antichain

open Finset

/-- Named ground set for the core-to-full construction. -/
abbrev CoreGround (α : Type*) (r : ℕ) (γ : Type*) :=
  α ⊕ (Unit ⊕ (Fin r ⊕ γ))

variable {α γ : Type*} [Fintype α] [DecidableEq α]
  [Fintype γ] [DecidableEq γ]
variable {r : ℕ}

/-- Inclusion of the core ground set. -/
def corePointEmbedding : α ↪ CoreGround α r γ :=
  ⟨Sum.inl, Sum.inl_injective⟩

/-- The common pivot point. -/
def corePivot : CoreGround α r γ :=
  Sum.inr (Sum.inl Unit.unit)

/-- The private point indexed by `j`. -/
def privatePoint (j : Fin r) : CoreGround α r γ :=
  Sum.inr (Sum.inr (Sum.inl j))

/-- Restrict a core to the levels used by the construction. -/
def coreWindow (C : Family α) (h : ℕ) : Family α :=
  C.filter fun c => 2 ≤ c.card ∧ c.card ≤ h - 1

omit [Fintype α] [DecidableEq α] in
@[simp] theorem mem_coreWindow {C : Family α} {h : ℕ} {c : Finset α} :
    c ∈ coreWindow C h ↔ c ∈ C ∧ 2 ≤ c.card ∧ c.card ≤ h - 1 := by
  simp [coreWindow]

omit [Fintype α] [DecidableEq α] in
theorem isSperner_coreWindow {C : Family α} {h : ℕ}
    (hC : IsSperner C) : IsSperner (coreWindow C h) := by
  exact hC.subset (by intro c hc; exact (mem_coreWindow.mp hc).1)

omit [Fintype α] in
theorem level_coreWindow_eq {C : Family α} {h i : ℕ}
    (hi2 : 2 ≤ i) (hih : i ≤ h - 1) :
    level (coreWindow C h) i = level C i := by
  ext c
  simp only [mem_level, mem_coreWindow]
  constructor
  · rintro ⟨⟨hc, -, -⟩, hcard⟩
    exact ⟨hc, hcard⟩
  · rintro ⟨hc, hcard⟩
    exact ⟨⟨hc, hcard ▸ hi2, hcard ▸ hih⟩, hcard⟩

/-- Attach the pivot to a core member. -/
def pivotedSet (c : Finset α) : Finset (CoreGround α r γ) :=
  insert corePivot (c.map corePointEmbedding)

/-- The pair formed by the pivot and one private point. -/
def privatePair (j : Fin r) : Finset (CoreGround α r γ) :=
  {corePivot, privatePoint j}

omit [Fintype α] [Fintype γ] in
@[simp] theorem mem_pivotedSet_core {c : Finset α} {x : α} :
    corePointEmbedding x ∈ (pivotedSet c : Finset (CoreGround α r γ)) ↔ x ∈ c := by
  simp [pivotedSet, corePointEmbedding, corePivot]

omit [Fintype α] [Fintype γ] in
@[simp] theorem pivot_mem_pivotedSet {c : Finset α} :
    (corePivot : CoreGround α r γ) ∈ pivotedSet c := by
  simp [pivotedSet]

omit [Fintype α] [Fintype γ] in
@[simp] theorem private_not_mem_pivotedSet {c : Finset α} {j : Fin r} :
    privatePoint j ∉ (pivotedSet c : Finset (CoreGround α r γ)) := by
  simp [pivotedSet, privatePoint, corePivot, corePointEmbedding]

omit [Fintype α] [Fintype γ] in
@[simp] theorem card_pivotedSet (c : Finset α) :
    (pivotedSet c : Finset (CoreGround α r γ)).card = c.card + 1 := by
  rw [pivotedSet, card_insert_of_notMem]
  · simp
  · simp [corePivot, corePointEmbedding]

omit [Fintype α] [Fintype γ] in
@[simp] theorem pivot_mem_privatePair (j : Fin r) :
    (corePivot : CoreGround α r γ) ∈ privatePair j := by
  simp [privatePair]

omit [Fintype α] [Fintype γ] in
@[simp] theorem private_mem_privatePair (j : Fin r) :
    privatePoint j ∈ (privatePair j : Finset (CoreGround α r γ)) := by
  simp [privatePair]

omit [Fintype α] [Fintype γ] in
@[simp] theorem card_privatePair (j : Fin r) :
    (privatePair j : Finset (CoreGround α r γ)).card = 2 := by
  simp [privatePair, privatePoint, corePivot]

omit [Fintype α] [Fintype γ] in
theorem pivotedSet_injective :
    Function.Injective (pivotedSet (α := α) (r := r) (γ := γ)) := by
  intro c d hcd
  ext x
  have h := congrArg
    (fun s : Finset (CoreGround α r γ) => corePointEmbedding x ∈ s) hcd
  simpa using h

omit [Fintype α] [Fintype γ] in
theorem privatePair_injective :
    Function.Injective (privatePair (α := α) (r := r) (γ := γ)) := by
  intro i j hij
  have hmem : privatePoint i ∈ (privatePair j : Finset (CoreGround α r γ)) := by
    rw [← hij]
    exact private_mem_privatePair i
  simp [privatePair, privatePoint, corePivot] at hmem
  exact hmem

def pivotedSetEmbedding :
    Finset α ↪ Finset (CoreGround α r γ) :=
  ⟨pivotedSet, pivotedSet_injective⟩

def privatePairEmbedding :
    Fin r ↪ Finset (CoreGround α r γ) :=
  ⟨privatePair, privatePair_injective⟩

/-- Pivoted members from the usable part of the core. -/
def pivotedFamily (C : Family α) (h : ℕ) : Family (CoreGround α r γ) :=
  (coreWindow C h).map pivotedSetEmbedding

/-- The `r` private pairs on level two. -/
def privatePairFamily : Family (CoreGround α r γ) :=
  (Finset.univ : Finset (Fin r)).map privatePairEmbedding

/-- The lower half before adjoining complements. -/
def lowerCoreFamily (C : Family α) (h : ℕ) : Family (CoreGround α r γ) :=
  privatePairFamily ∪ pivotedFamily C h

omit [Fintype α] [Fintype γ] in
@[simp] theorem mem_pivotedFamily {C : Family α} {h : ℕ}
    {u : Finset (CoreGround α r γ)} :
    u ∈ pivotedFamily C h ↔ ∃ c ∈ coreWindow C h, pivotedSet c = u := by
  simp [pivotedFamily, pivotedSetEmbedding]

omit [Fintype α] [Fintype γ] in
@[simp] theorem mem_privatePairFamily {u : Finset (CoreGround α r γ)} :
    u ∈ (privatePairFamily : Family (CoreGround α r γ)) ↔
      ∃ j : Fin r, privatePair j = u := by
  simp [privatePairFamily, privatePairEmbedding]

omit [Fintype α] [Fintype γ] in
@[simp] theorem card_privatePairFamily :
    (privatePairFamily : Family (CoreGround α r γ)).card = r := by
  simp [privatePairFamily]

omit [Fintype α] [Fintype γ] in
theorem privatePairFamily_sized :
    ((privatePairFamily (α := α) (r := r) (γ := γ) :
      Family (CoreGround α r γ)) : Set (Finset (CoreGround α r γ))).Sized 2 := by
  intro u hu
  obtain ⟨j, rfl⟩ := mem_privatePairFamily.mp hu
  exact card_privatePair j

omit [Fintype α] [Fintype γ] in
theorem pivotedSet_subset_iff {c d : Finset α} :
    (pivotedSet c : Finset (CoreGround α r γ)) ⊆ pivotedSet d ↔ c ⊆ d := by
  constructor
  · intro h x hx
    exact mem_pivotedSet_core.mp (h (mem_pivotedSet_core.mpr hx))
  · intro h x hx
    rcases mem_insert.mp hx with hx | hx
    · exact hx ▸ pivot_mem_pivotedSet
    · obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
      exact mem_pivotedSet_core.mpr (h hy)

omit [Fintype α] [Fintype γ] in
theorem isSperner_pivotedFamily {C : Family α} {h : ℕ}
    (hC : IsSperner C) :
    IsSperner (pivotedFamily (r := r) (γ := γ) C h) := by
  intro u hu v hv huv hsub
  obtain ⟨c, hc, rfl⟩ := mem_pivotedFamily.mp hu
  obtain ⟨d, hd, rfl⟩ := mem_pivotedFamily.mp hv
  have hcd : c ⊆ d := pivotedSet_subset_iff.mp hsub
  have heq : c = d := (isSperner_coreWindow hC).eq hc hd hcd
  exact huv (congrArg pivotedSet heq)

omit [Fintype α] [Fintype γ] in
theorem privatePair_not_subset_pivotedSet
    (j : Fin r) (c : Finset α) :
    ¬ (privatePair j : Finset (CoreGround α r γ)) ⊆ pivotedSet c := by
  intro hsub
  exact private_not_mem_pivotedSet (hsub (private_mem_privatePair j))

omit [Fintype α] [Fintype γ] in
theorem pivotedSet_not_subset_privatePair
    {C : Family α} {h : ℕ} {c : Finset α}
    (hc : c ∈ coreWindow C h) (j : Fin r) :
    ¬ (pivotedSet c : Finset (CoreGround α r γ)) ⊆ privatePair j := by
  intro hsub
  have hcard := card_le_card hsub
  rw [card_pivotedSet, card_privatePair] at hcard
  have hc2 := (mem_coreWindow.mp hc).2.1
  omega

omit [Fintype α] [Fintype γ] in
theorem isSperner_lowerCoreFamily {C : Family α} {h : ℕ}
    (hC : IsSperner C) :
    IsSperner (lowerCoreFamily (r := r) (γ := γ) C h) := by
  have hpairs : IsSperner
      (privatePairFamily (α := α) (r := r) (γ := γ) :
        Family (CoreGround α r γ)) :=
    privatePairFamily_sized.isAntichain
  have hpivoted : IsSperner (pivotedFamily (r := r) (γ := γ) C h) :=
    isSperner_pivotedFamily hC
  unfold IsSperner lowerCoreFamily
  rw [Finset.coe_union]
  apply isAntichain_union.mpr
  refine ⟨hpairs, hpivoted, ?_⟩
  intro u hu v hv huv
  obtain ⟨j, rfl⟩ := mem_privatePairFamily.mp hu
  obtain ⟨c, hc, rfl⟩ := mem_pivotedFamily.mp hv
  exact ⟨privatePair_not_subset_pivotedSet j c,
    pivotedSet_not_subset_privatePair hc j⟩

omit [Fintype α] [Fintype γ] in
theorem level_pivotedFamily_succ {C : Family α} {h i : ℕ} :
    level (pivotedFamily (r := r) (γ := γ) C h) (i + 1) =
      (level (coreWindow C h) i).map
        (pivotedSetEmbedding (r := r) (γ := γ)) := by
  ext u
  constructor
  · intro hu
    obtain ⟨huF, hucard⟩ := mem_level.mp hu
    obtain ⟨c, hc, rfl⟩ := mem_pivotedFamily.mp huF
    apply mem_map.mpr
    refine ⟨c, mem_level.mpr ⟨hc, ?_⟩, rfl⟩
    rw [card_pivotedSet] at hucard
    omega
  · intro hu
    obtain ⟨c, hc, rfl⟩ := mem_map.mp hu
    apply mem_level.mpr
    refine ⟨mem_pivotedFamily.mpr ⟨c, (mem_level.mp hc).1, rfl⟩, ?_⟩
    change (pivotedSet c : Finset (CoreGround α r γ)).card = i + 1
    rw [card_pivotedSet, (mem_level.mp hc).2]

omit [Fintype α] [Fintype γ] in
theorem card_level_pivotedFamily_succ {C : Family α} {h i : ℕ} :
    (level (pivotedFamily (r := r) (γ := γ) C h) (i + 1)).card =
      (level (coreWindow C h) i).card := by
  rw [level_pivotedFamily_succ, card_map]

omit [Fintype α] [Fintype γ] in
theorem level_privatePairFamily_two :
    level (privatePairFamily (α := α) (r := r) (γ := γ) :
      Family (CoreGround α r γ)) 2 =
      privatePairFamily (α := α) (r := r) (γ := γ) := by
  ext u
  constructor
  · exact fun hu => (mem_level.mp hu).1
  · intro hu
    exact mem_level.mpr ⟨hu, privatePairFamily_sized hu⟩

omit [Fintype α] [Fintype γ] in
theorem hasMultiplicities_lowerCoreFamily
    {C : Family α} {h : ℕ} (hh : 2 ≤ h)
    (hlevels : HasMultiplicities C r 2 (h - 1)) :
    HasMultiplicities (lowerCoreFamily (r := r) (γ := γ) C h) r 2 h := by
  intro i hi2 hih
  unfold HasMultiplicityAt
  by_cases hi : i = 2
  · subst i
    have hsubset :
        (privatePairFamily (α := α) (r := r) (γ := γ) :
          Family (CoreGround α r γ)) ⊆
        lowerCoreFamily (r := r) (γ := γ) C h := subset_union_left
    have hcard := card_le_card (level_mono hsubset 2)
    rw [level_privatePairFamily_two, card_privatePairFamily] at hcard
    exact hcard
  · have hi3 : 3 ≤ i := by omega
    have hsubset : pivotedFamily (r := r) (γ := γ) C h ⊆
        lowerCoreFamily (r := r) (γ := γ) C h := subset_union_right
    have hcard := card_le_card (level_mono hsubset i)
    have hpred2 : 2 ≤ i - 1 := by omega
    have hpredh : i - 1 ≤ h - 1 := by omega
    have hcore := hlevels (i - 1) hpred2 hpredh
    unfold HasMultiplicityAt at hcore
    rw [show i = (i - 1) + 1 by omega,
      card_level_pivotedFamily_succ,
      level_coreWindow_eq hpred2 hpredh] at hcard
    simpa [show i - 1 + 1 = i by omega] using hcore.trans hcard

/-! ### Complements and the full family -/

theorem level_compls {δ : Type*} [Fintype δ] [DecidableEq δ]
    (F : Family δ) {i : ℕ} (hi : i ≤ Fintype.card δ) :
    level (Finset.compls F) i =
      Finset.compls (level F (Fintype.card δ - i)) := by
  ext s
  simp only [mem_level, Finset.mem_compls]
  constructor
  · rintro ⟨hsF, hcard⟩
    refine ⟨hsF, ?_⟩
    rw [Finset.card_compl, hcard]
  · rintro ⟨hsF, hcard⟩
    refine ⟨hsF, ?_⟩
    rw [Finset.card_compl] at hcard
    have hsle : s.card ≤ Fintype.card δ := by
      simpa using card_le_card (subset_univ s)
    omega

theorem card_level_compls {δ : Type*} [Fintype δ] [DecidableEq δ]
    (F : Family δ) {i : ℕ} (hi : i ≤ Fintype.card δ) :
    (level (Finset.compls F) i).card =
      (level F (Fintype.card δ - i)).card := by
  rw [level_compls F hi, Finset.card_compls]

/-- Add the complemented upper half to the lower construction. -/
def coreToFullFamily (C : Family α) (h : ℕ) :
    Family (CoreGround α r γ) :=
  lowerCoreFamily C h ∪ Finset.compls (lowerCoreFamily C h)

omit [Fintype α] [Fintype γ] in
theorem pivot_mem_lowerCoreFamily {C : Family α} {h : ℕ}
    {u : Finset (CoreGround α r γ)}
    (hu : u ∈ lowerCoreFamily (r := r) (γ := γ) C h) :
    corePivot ∈ u := by
  rcases mem_union.mp hu with hu | hu
  · obtain ⟨j, rfl⟩ := mem_privatePairFamily.mp hu
    exact pivot_mem_privatePair j
  · obtain ⟨c, hc, rfl⟩ := mem_pivotedFamily.mp hu
    exact pivot_mem_pivotedSet

omit [Fintype α] [Fintype γ] in
theorem card_lowerCoreFamily_le {C : Family α} {h : ℕ} (hh : 2 ≤ h)
    {u : Finset (CoreGround α r γ)}
    (hu : u ∈ lowerCoreFamily (r := r) (γ := γ) C h) :
    u.card ≤ h := by
  rcases mem_union.mp hu with hu | hu
  · obtain ⟨j, rfl⟩ := mem_privatePairFamily.mp hu
    rw [card_privatePair]
    exact hh
  · obtain ⟨c, hc, rfl⟩ := mem_pivotedFamily.mp hu
    rw [card_pivotedSet]
    have hcupper := (mem_coreWindow.mp hc).2.2
    omega

theorem isSperner_compls {δ : Type*} [Fintype δ] [DecidableEq δ]
    {F : Family δ} (hF : IsSperner F) :
    IsSperner (Finset.compls F) := by
  unfold IsSperner at hF ⊢
  simpa only [Finset.coe_compls] using hF.image_compl

/--
The lower family and its complement are mutually incomparable because all
lower members contain the pivot and have size at most half the ground set.
-/
theorem isSperner_coreToFullFamily
    {C : Family α} {h : ℕ} (hh : 2 ≤ h)
    (hhalf : 2 * h ≤ Fintype.card (CoreGround α r γ))
    (hC : IsSperner C) :
    IsSperner (coreToFullFamily (r := r) (γ := γ) C h) := by
  have hL : IsSperner
      (lowerCoreFamily (r := r) (γ := γ) C h) :=
    isSperner_lowerCoreFamily hC
  have hLc : IsSperner
      (Finset.compls (lowerCoreFamily (r := r) (γ := γ) C h)) :=
    isSperner_compls hL
  unfold IsSperner coreToFullFamily
  rw [Finset.coe_union]
  apply isAntichain_union.mpr
  refine ⟨hL, hLc, ?_⟩
  intro a ha b hb hab
  have hbL : bᶜ ∈ lowerCoreFamily (r := r) (γ := γ) C h :=
    Finset.mem_compls.mp hb
  constructor
  · intro habsub
    have hpiva : corePivot ∈ a := pivot_mem_lowerCoreFamily ha
    have hpivb : corePivot ∈ b := habsub hpiva
    have hpivbc : corePivot ∈ bᶜ := pivot_mem_lowerCoreFamily hbL
    have hpiv_not : corePivot ∉ b := by simpa using hpivbc
    exact hpiv_not hpivb
  · intro hbasub
    have hunion : a ∪ bᶜ = (Finset.univ : Finset (CoreGround α r γ)) := by
      ext x
      simp only [mem_union, mem_compl, mem_univ, iff_true]
      by_cases hxb : x ∈ b
      · exact Or.inl (hbasub hxb)
      · exact Or.inr hxb
    have hinter : 1 ≤ (a ∩ bᶜ).card := by
      apply card_pos.mpr
      exact ⟨corePivot,
        mem_inter.mpr ⟨pivot_mem_lowerCoreFamily ha,
          pivot_mem_lowerCoreFamily hbL⟩⟩
    have hacard : a.card ≤ h := card_lowerCoreFamily_le hh ha
    have hbcard : bᶜ.card ≤ h := card_lowerCoreFamily_le hh hbL
    have hcount := card_union_add_card_inter a bᶜ
    rw [hunion, card_univ] at hcount
    omega

theorem hasMultiplicities_coreToFullFamily
    {C : Family α}
    (hn : 4 ≤ Fintype.card (CoreGround α r γ))
    (hlevels : HasMultiplicities C r 2
      (Fintype.card (CoreGround α r γ) / 2 - 1)) :
    HasMultiplicities
      (coreToFullFamily (r := r) (γ := γ) C
        (Fintype.card (CoreGround α r γ) / 2))
      r 2 (Fintype.card (CoreGround α r γ) - 2) := by
  let n := Fintype.card (CoreGround α r γ)
  let h := n / 2
  let L : Family (CoreGround α r γ) :=
    lowerCoreFamily (r := r) (γ := γ) C h
  have hh : 2 ≤ h := by
    dsimp [h, n]
    omega
  have hL : HasMultiplicities L r 2 h := by
    exact hasMultiplicities_lowerCoreFamily hh hlevels
  intro i hi2 hin
  unfold HasMultiplicityAt
  by_cases hilow : i ≤ h
  · have hsubset : L ⊆ coreToFullFamily (r := r) (γ := γ) C h :=
      subset_union_left
    exact (hL i hi2 hilow).trans (card_le_card (level_mono hsubset i))
  · have hij2 : 2 ≤ n - i := by
      dsimp [n] at hin ⊢
      omega
    have hijh : n - i ≤ h := by
      dsimp [h]
      omega
    have hi_le_n : i ≤ n := by omega
    have hcomp_subset : Finset.compls L ⊆
        coreToFullFamily (r := r) (γ := γ) C h := subset_union_right
    have hcomp_card := card_le_card (level_mono hcomp_subset i)
    have hlevel_compl := card_level_compls L hi_le_n
    have hLj := hL (n - i) hij2 hijh
    rw [hlevel_compl] at hcomp_card
    exact hLj.trans hcomp_card

/-- The manuscript's core-to-full lemma, with antichain and profile conclusions. -/
theorem coreToFull
    {C : Family α}
    (hn : 4 ≤ Fintype.card (CoreGround α r γ))
    (hC : IsSperner C)
    (hlevels : HasMultiplicities C r 2
      (Fintype.card (CoreGround α r γ) / 2 - 1)) :
    IsSperner
        (coreToFullFamily (r := r) (γ := γ) C
          (Fintype.card (CoreGround α r γ) / 2)) ∧
      HasMultiplicities
        (coreToFullFamily (r := r) (γ := γ) C
          (Fintype.card (CoreGround α r γ) / 2))
        r 2 (Fintype.card (CoreGround α r γ) - 2) := by
  have hhalf :
      2 * (Fintype.card (CoreGround α r γ) / 2) ≤
        Fintype.card (CoreGround α r γ) :=
    Nat.mul_div_le _ 2
  have hh : 2 ≤ Fintype.card (CoreGround α r γ) / 2 := by omega
  exact ⟨isSperner_coreToFullFamily hh hhalf hC,
    hasMultiplicities_coreToFullFamily hn hlevels⟩

/-- Transport the named construction to the conventional ground set `Fin n`. -/
noncomputable def coreToFullFinFamily (C : Family α) :
    Family (Fin (Fintype.card (CoreGround α r γ))) :=
  mapFamily (Fintype.equivFin (CoreGround α r γ)).toEmbedding <|
    coreToFullFamily (r := r) (γ := γ) C
      (Fintype.card (CoreGround α r γ) / 2)

/-- `coreToFull`, stated on the numerical ground set used in the manuscripts. -/
theorem coreToFull_fin
    {C : Family α}
    (hn : 4 ≤ Fintype.card (CoreGround α r γ))
    (hC : IsSperner C)
    (hlevels : HasMultiplicities C r 2
      (Fintype.card (CoreGround α r γ) / 2 - 1)) :
    IsSperner (coreToFullFinFamily (r := r) (γ := γ) C) ∧
      HasMultiplicities (coreToFullFinFamily (r := r) (γ := γ) C)
        r 2 (Fintype.card (CoreGround α r γ) - 2) := by
  obtain ⟨hanti, hprofile⟩ := coreToFull hn hC hlevels
  constructor
  · exact isSperner_mapFamily hanti
  · intro i hi hin
    unfold HasMultiplicityAt
    rw [coreToFullFinFamily, card_level_mapFamily]
    exact hprofile i hi hin

end Erdos776.Antichain


/-!
# Transporting finitely supported colex families to `Fin n`

Mathlib's Kruskal--Katona theorem is stated for families of subsets of
`Fin n`.  Our recursive cascade family is more convenient over `ℕ`; this file
provides the lossless transport for families supported below `n`.
-/

namespace Erdos776.KruskalKatona

open Finset

/-- The subset of `Fin n` whose values belong to `s`. -/
noncomputable def finify (n : ℕ) (s : Finset ℕ) : Finset (Fin n) :=
  s.preimage Fin.val Fin.val_injective.injOn

@[simp] theorem mem_finify {n : ℕ} {s : Finset ℕ} {x : Fin n} :
    x ∈ finify n s ↔ x.val ∈ s := by
  simp [finify]

/-- Mapping a bounded `finify` back to naturals recovers the original set. -/
theorem map_valEmbedding_finify {n : ℕ} {s : Finset ℕ}
    (hs : ∀ x ∈ s, x < n) :
    (finify n s).map Fin.valEmbedding = s := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := mem_map.mp hx
    simpa [← hyx] using (mem_finify.mp hy)
  · intro hx
    exact mem_map.mpr ⟨⟨x, hs x hx⟩, mem_finify.mpr hx, rfl⟩

theorem card_finify {n : ℕ} {s : Finset ℕ}
    (hs : ∀ x ∈ s, x < n) : (finify n s).card = s.card := by
  have h := congrArg Finset.card (map_valEmbedding_finify hs)
  simpa using h

/-- A family is supported on the first `n` natural numbers. -/
def BoundedFamily (n : ℕ) (F : Finset (Finset ℕ)) : Prop :=
  ∀ s ∈ F, ∀ x ∈ s, x < n

/-- Apply `finify` to every member of a family. -/
noncomputable def finifyFamily (n : ℕ) (F : Finset (Finset ℕ)) :
    Finset (Finset (Fin n)) :=
  F.image (finify n)

theorem finify_injOn {n : ℕ} {F : Finset (Finset ℕ)}
    (hF : BoundedFamily n F) : Set.InjOn (finify n) (F : Set (Finset ℕ)) := by
  intro s hs t ht hst
  have := congrArg (Finset.map Fin.valEmbedding) hst
  simpa [map_valEmbedding_finify (hF s hs), map_valEmbedding_finify (hF t ht)] using this

theorem card_finifyFamily {n : ℕ} {F : Finset (Finset ℕ)}
    (hF : BoundedFamily n F) : (finifyFamily n F).card = F.card := by
  exact card_image_of_injOn (finify_injOn hF)

theorem sized_finifyFamily {n k : ℕ} {F : Finset (Finset ℕ)}
    (hF : BoundedFamily n F)
    (hsize : (F : Set (Finset ℕ)).Sized k) :
    (finifyFamily n F : Set (Finset (Fin n))).Sized k := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hs
  rw [card_finify (hF t ht), hsize ht]

theorem bounded_cascadeFamily {n k : ℕ} {a : ℕ} {digits : List ℕ}
    (h : IsCanonical k (a :: digits)) (ha : a < n) :
    BoundedFamily n (cascadeFamily k (a :: digits)) := by
  intro s hs
  exact mem_cascadeFamily_lt_of_digits_lt (h.all_lt_of_head ha) hs

/-- Colex comparison is preserved by lossless transport to `Fin n`. -/
theorem colex_finify_lt_iff {n : ℕ} {s t : Finset ℕ}
    (hs : ∀ x ∈ s, x < n) (ht : ∀ x ∈ t, x < n) :
    toColex (finify n s) < toColex (finify n t) ↔
      toColex s < toColex t := by
  have hs' : image Fin.val (finify n s) = s := by
    simpa [map_eq_image] using map_valEmbedding_finify hs
  have ht' : image Fin.val (finify n t) = t := by
    simpa [map_eq_image] using map_valEmbedding_finify ht
  constructor
  · intro hst
    have himage :=
      (Finset.Colex.toColex_image_lt_toColex_image Fin.val_strictMono).mpr hst
    rwa [hs', ht'] at himage
  · intro hst
    rw [← hs', ← ht'] at hst
    exact (Finset.Colex.toColex_image_lt_toColex_image Fin.val_strictMono).mp hst

/-- A bounded colex initial segment transports to an initial segment on `Fin n`. -/
theorem isInitSeg_finifyFamily {n k : ℕ} {F : Finset (Finset ℕ)}
    (hF : BoundedFamily n F)
    (hinit : Finset.Colex.IsInitSeg F k) :
    Finset.Colex.IsInitSeg (finifyFamily n F) k := by
  constructor
  · exact sized_finifyFamily hF hinit.1
  · intro s t hs ht
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hs
    let v : Finset ℕ := t.map Fin.valEmbedding
    have hvcard : v.card = k := by
      simp [v, ht.2]
    have hvbound : ∀ x ∈ v, x < n := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
      exact y.isLt
    have hvcolex : toColex v < toColex u := by
      have himage :=
        (Finset.Colex.toColex_image_lt_toColex_image Fin.val_strictMono).mpr ht.1
      have hu' : image Fin.val (finify n u) = u := by
        simpa [map_eq_image] using map_valEmbedding_finify (hF u hu)
      simpa [v, map_eq_image, hu'] using himage
    have hvF : v ∈ F := hinit.2 hu ⟨hvcolex, hvcard⟩
    apply mem_image.mpr
    refine ⟨v, hvF, ?_⟩
    ext x
    simp only [v, finify, mem_preimage, mem_map]
    constructor
    · rintro ⟨y, hy, hval⟩
      exact Fin.val_injective hval ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩

theorem finify_erase {n : ℕ} {s : Finset ℕ} {x : ℕ}
    (hx : x < n) :
    finify n (s.erase x) = (finify n s).erase ⟨x, hx⟩ := by
  ext y
  rw [mem_finify, mem_erase, mem_erase, mem_finify]
  constructor
  · rintro ⟨hne, hmem⟩
    exact ⟨fun h => hne (congrArg Fin.val h), hmem⟩
  · rintro ⟨hne, hmem⟩
    exact ⟨fun h => hne (Fin.ext h), hmem⟩

theorem BoundedFamily.shadow {n : ℕ} {F : Finset (Finset ℕ)}
    (hF : BoundedFamily n F) : BoundedFamily n (Finset.shadow F) := by
  intro t ht x hx
  obtain ⟨s, hs, y, hy, rfl⟩ := mem_shadow_iff.mp ht
  exact hF s hs x (mem_of_mem_erase hx)

/-- `finifyFamily` commutes with taking a lower shadow. -/
theorem shadow_finifyFamily {n : ℕ} {F : Finset (Finset ℕ)}
    (hF : BoundedFamily n F) :
    Finset.shadow (finifyFamily n F) =
      finifyFamily n (Finset.shadow F) := by
  ext t
  constructor
  · intro ht
    obtain ⟨s, hs, x, hx, hxt⟩ := mem_shadow_iff.mp ht
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hs
    have hxu : x.val ∈ u := mem_finify.mp hx
    apply mem_image.mpr
    refine ⟨u.erase x.val, erase_mem_shadow hu hxu, ?_⟩
    rw [finify_erase x.isLt]
    exact hxt
  · intro ht
    obtain ⟨v, hv, rfl⟩ := mem_image.mp ht
    obtain ⟨u, hu, x, hxu, hxv⟩ := mem_shadow_iff.mp hv
    have hxn : x < n := hF u hu x hxu
    apply mem_shadow_iff.mpr
    refine ⟨finify n u, mem_image.mpr ⟨u, hu, rfl⟩,
      ⟨x, hxn⟩, mem_finify.mpr hxu, ?_⟩
    rw [← finify_erase hxn, hxv]

theorem card_shadow_finifyFamily {n : ℕ} {F : Finset (Finset ℕ)}
    (hF : BoundedFamily n F) :
    (Finset.shadow (finifyFamily n F)).card = (Finset.shadow F).card := by
  rw [shadow_finifyFamily hF, card_finifyFamily hF.shadow]

end Erdos776.KruskalKatona


/-!
# The numerical Kruskal--Katona shadow

`kkShadow n k m` is the least lower-shadow size among `m` distinct `k`-sets
on `Fin n`.  A maximal sentinel is included for impossible cardinalities; this
makes the function globally monotone without changing any feasible value.
-/

namespace Erdos776.KruskalKatona

open Finset

def uniformFamilies (n k m : ℕ) : Finset (Finset (Finset (Fin n))) :=
  Finset.univ.filter fun A =>
    (∀ s ∈ A, s.card = k) ∧ A.card = m

def shadowCandidates (n k m : ℕ) : Finset ℕ :=
  insert (n.choose (k - 1)) <|
    (uniformFamilies n k m).image fun A => (Finset.shadow A).card

/-- The minimum numerical lower-shadow size, extended monotonically off range. -/
noncomputable def kkShadow (n k m : ℕ) : ℕ :=
  (shadowCandidates n k m).min' <| by
    exact ⟨n.choose (k - 1), mem_insert_self _ _⟩

theorem sentinel_mem_shadowCandidates (n k m : ℕ) :
    n.choose (k - 1) ∈ shadowCandidates n k m := by
  exact mem_insert_self _ _

theorem shadowCandidates_nonempty (n k m : ℕ) :
    (shadowCandidates n k m).Nonempty :=
  ⟨n.choose (k - 1), sentinel_mem_shadowCandidates n k m⟩

theorem mem_shadowCandidates_iff {n k m q : ℕ} :
    q ∈ shadowCandidates n k m ↔
      q = n.choose (k - 1) ∨
      ∃ A : Finset (Finset (Fin n)),
        (A : Set (Finset (Fin n))).Sized k ∧
        A.card = m ∧ (Finset.shadow A).card = q := by
  simp only [shadowCandidates, mem_insert, mem_image, uniformFamilies,
    mem_filter, mem_univ, true_and, Set.Sized]
  constructor
  · rintro (h | ⟨A, ⟨hsize, hcard⟩, hshadow⟩)
    · exact Or.inl h
    · exact Or.inr ⟨A, hsize, hcard, hshadow⟩
  · rintro (h | ⟨A, hsize, hcard, hshadow⟩)
    · exact Or.inl h
    · exact Or.inr ⟨A, ⟨hsize, hcard⟩, hshadow⟩

theorem kkShadow_le_sentinel (n k m : ℕ) :
    kkShadow n k m ≤ n.choose (k - 1) := by
  exact min'_le _ _ (sentinel_mem_shadowCandidates n k m)

/-- Global monotonicity in the number of sets. -/
theorem kkShadow_mono (n k : ℕ) : Monotone (kkShadow n k) := by
  intro x y hxy
  apply le_min' (shadowCandidates n k y) (shadowCandidates_nonempty n k y)
  intro q hq
  rcases mem_shadowCandidates_iff.mp hq with hq | hq
  · rw [hq]
    exact kkShadow_le_sentinel n k x
  · obtain ⟨A, hAsize, hAcard, rfl⟩ := hq
    obtain ⟨B, hBA, hBcard⟩ := exists_subset_card_eq (hAcard ▸ hxy)
    have hBsize : (B : Set (Finset (Fin n))).Sized k := hAsize.mono hBA
    have hBcandidate : (Finset.shadow B).card ∈ shadowCandidates n k x := by
      exact mem_shadowCandidates_iff.mpr (Or.inr ⟨B, hBsize, hBcard, rfl⟩)
    exact (min'_le _ _ hBcandidate).trans
      (card_le_card (shadow_mono hBA))

/-- Every uniform family has shadow at least the numerical minimum. -/
theorem kkShadow_le_card_shadow
    {n k : ℕ} {A : Finset (Finset (Fin n))}
    (hsize : (A : Set (Finset (Fin n))).Sized k) :
    kkShadow n k A.card ≤ (Finset.shadow A).card := by
  apply min'_le
  exact mem_shadowCandidates_iff.mpr
    (Or.inr ⟨A, hsize, rfl, rfl⟩)

/--
The concrete family represented by a bounded canonical cascade realizes the
numerical minimum.  The lower bound is exactly mathlib's Kruskal--Katona
theorem applied to the transported colex initial segment.
-/
theorem kkShadow_eq_cascadeShadowValue
    {n k : ℕ} {digits : List ℕ}
    (hcanon : IsCanonical k digits)
    (hbound : BoundedFamily n (cascadeFamily k digits)) :
    kkShadow n k (cascadeValue k digits) =
      cascadeShadowValue k digits := by
  let C : Finset (Finset (Fin n)) :=
    finifyFamily n (cascadeFamily k digits)
  have hCsize : (C : Set (Finset (Fin n))).Sized k :=
    sized_finifyFamily hbound (sized_cascadeFamily hcanon)
  have hCcard : C.card = cascadeValue k digits := by
    rw [show C = finifyFamily n (cascadeFamily k digits) by rfl,
      card_finifyFamily hbound, card_cascadeFamily hcanon]
  have hCshadow : (Finset.shadow C).card = cascadeShadowValue k digits := by
    rw [show C = finifyFamily n (cascadeFamily k digits) by rfl,
      card_shadow_finifyFamily hbound, card_shadow_cascadeFamily hcanon]
  have hCinit : Finset.Colex.IsInitSeg C k :=
    isInitSeg_finifyFamily hbound (isInitSeg_cascadeFamily hcanon)
  apply le_antisymm
  · apply min'_le
    exact mem_shadowCandidates_iff.mpr (Or.inr ⟨C, hCsize, hCcard, hCshadow⟩)
  · apply le_min' (shadowCandidates n k (cascadeValue k digits))
      (shadowCandidates_nonempty n k (cascadeValue k digits))
    intro q hq
    rcases mem_shadowCandidates_iff.mp hq with hq | hq
    · rw [hq, ← hCshadow]
      exact (by
        simpa using card_le_card (subset_powersetCard_univ_iff.mpr hCsize.shadow))
    · obtain ⟨A, hAsize, hAcard, rfl⟩ := hq
      rw [← hCshadow]
      apply Finset.kruskal_katona hAsize
      · rw [hCcard, hAcard]
      · exact hCinit

/-- Convenient head-bound form of the cascade evaluation theorem. -/
theorem kkShadow_eq_cascadeShadowValue_of_head
    {n k a : ℕ} {digits : List ℕ}
    (hcanon : IsCanonical k (a :: digits)) (ha : a < n) :
    kkShadow n k (cascadeValue k (a :: digits)) =
      cascadeShadowValue k (a :: digits) :=
  kkShadow_eq_cascadeShadowValue hcanon (bounded_cascadeFamily hcanon ha)

end Erdos776.KruskalKatona


/-!
# The ground-independent numerical cascade shadow

The greedy normal form turns the finite minimum `kkShadow n k m` into a
numerical function of `k,m` alone whenever `m ≤ choose n k`.
-/

namespace Erdos776.KruskalKatona

open Finset

/-- Lower every index in the unique canonical cascade of `m`. -/
def canonicalShadow (k m : ℕ) : ℕ :=
  cascadeShadowValue k (canonicalDigits k m)

/-- Evaluate the canonical shadow through any proved canonical representation. -/
theorem canonicalShadow_eq_cascadeShadowValue
    {k m : ℕ} {digits : List ℕ}
    (hcanon : IsCanonical k digits)
    (hvalue : cascadeValue k digits = m) :
    canonicalShadow k m = cascadeShadowValue k digits := by
  unfold canonicalShadow
  rw [← canonicalDigits_unique hcanon hvalue]

/-- Closed form for the shadow of a diagonal representation of `len`. -/
theorem canonicalShadow_diagonal {a len : ℕ} (hlen : len ≤ a) :
    canonicalShadow a len =
      (a + 1).choose 2 - (a + 1 - len).choose 2 := by
  rw [canonicalShadow_eq_cascadeShadowValue
      (isCanonical_diagonalDigits hlen)
      (cascadeValue_diagonalDigits hlen),
    cascadeShadowValue_diagonalDigits hlen]

@[simp] theorem canonicalShadow_zero (k : ℕ) : canonicalShadow k 0 = 0 := by
  cases k with
  | zero => simp [canonicalShadow, cascadeShadowValue]
  | succ k => simp [canonicalShadow, cascadeShadowValue]

theorem bounded_cascadeFamily_canonicalDigits_of_lt
    {n k m : ℕ} (hk : 1 ≤ k) (hm : m < n.choose k) :
    BoundedFamily n (cascadeFamily k (canonicalDigits k m)) := by
  intro s hs
  exact mem_cascadeFamily_lt_of_digits_lt
    (canonicalDigits_all_lt hk hm) hs

theorem bounded_cascadeFamily_singleton_digit
    {n k : ℕ} (hk : 1 ≤ k) :
    BoundedFamily n (cascadeFamily k [n]) := by
  cases k with
  | zero => omega
  | succ k =>
      intro s hs x hx
      simp only [cascadeFamily_succ_cons, cascadeFamily_nil, image_empty,
        union_empty, mem_powersetCard] at hs
      exact mem_range.mp (hs.1 hx)

theorem canonicalDigits_eq_singleton_choose
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    canonicalDigits k (n.choose k) = [n] := by
  symm
  apply canonicalDigits_unique
  · cases k with
    | zero => omega
    | succ k => simp [IsCanonical, hkn]
  · simp [cascadeValue]

/-- The shadow of a complete numerical level is the complete lower level. -/
theorem canonicalShadow_choose {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    canonicalShadow k (n.choose k) = n.choose (k - 1) := by
  rw [canonicalShadow, canonicalDigits_eq_singleton_choose hk hkn,
    cascadeShadowValue_cons, cascadeValue_nil, Nat.add_zero]

theorem bounded_cascadeFamily_canonicalDigits
    {n k m : ℕ} (hk : 1 ≤ k) (hm : m ≤ n.choose k) :
    BoundedFamily n (cascadeFamily k (canonicalDigits k m)) := by
  by_cases hm0 : m = 0
  · subst m
    have hdigits : canonicalDigits k 0 = [] := by
      cases k with
      | zero => omega
      | succ k => simp
    rw [hdigits, cascadeFamily_nil]
    intro s hs
    simp at hs
  · rcases lt_or_eq_of_le hm with hlt | heq
    · exact bounded_cascadeFamily_canonicalDigits_of_lt hk hlt
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      have hkn : k ≤ n := by
        by_contra hnot
        rw [heq, Nat.choose_eq_zero_of_lt (by omega)] at hmpos
        omega
      rw [heq, canonicalDigits_eq_singleton_choose hk hkn]
      exact bounded_cascadeFamily_singleton_digit hk

/--
For every feasible cardinality, the finite minimum shadow equals the cascade
shadow of the unique numerical normal form.
-/
theorem kkShadow_eq_canonicalShadow
    {n k m : ℕ} (hk : 1 ≤ k) (hm : m ≤ n.choose k) :
    kkShadow n k m = canonicalShadow k m := by
  have hcanon : IsCanonical k (canonicalDigits k m) :=
    isCanonical_canonicalDigits hk
  by_cases hm0 : m = 0
  · subst m
    have hdigits : canonicalDigits k 0 = [] := by
      cases k with
      | zero => omega
      | succ k => simp
    have heval := kkShadow_eq_cascadeShadowValue hcanon
      (show BoundedFamily n (cascadeFamily k (canonicalDigits k 0)) by
        rw [hdigits, cascadeFamily_nil]
        intro s hs
        simp at hs)
    rw [cascadeValue_canonicalDigits hk] at heval
    simpa [canonicalShadow] using heval
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    rcases lt_or_eq_of_le hm with hlt | heq
    · have heval := kkShadow_eq_cascadeShadowValue hcanon
        (bounded_cascadeFamily_canonicalDigits hk hlt.le)
      rw [cascadeValue_canonicalDigits hk] at heval
      exact heval
    · have hkn : k ≤ n := by
        by_contra hnot
        have hzero : n.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
        rw [heq, hzero] at hmpos
        omega
      have hsingle : IsCanonical k [n] := by
        cases k with
        | zero => omega
        | succ k => simp [IsCanonical, hkn]
      have hnormal : canonicalDigits k m = [n] := by
        symm
        apply canonicalDigits_unique hsingle
        simp [cascadeValue, heq]
      rw [heq] at hnormal ⊢
      have heval := kkShadow_eq_cascadeShadowValue hsingle
        (bounded_cascadeFamily_singleton_digit (n := n) hk)
      rw [cascadeValue_cons, cascadeValue_nil, Nat.add_zero] at heval
      simpa [canonicalShadow, hnormal] using heval

theorem canonicalShadow_eq_kkShadow
    {n k m : ℕ} (hk : 1 ≤ k) (hm : m ≤ n.choose k) :
    canonicalShadow k m = kkShadow n k m :=
  (kkShadow_eq_canonicalShadow hk hm).symm

/-- The canonical numerical shadow is monotone in the represented value. -/
theorem canonicalShadow_mono (k : ℕ) (hk : 1 ≤ k) :
    Monotone (canonicalShadow k) := by
  intro x y hxy
  let n := y + k
  have hycap : y ≤ n.choose k := by
    exact (lt_choose_add y k hk).le
  have hxcap : x ≤ n.choose k := hxy.trans hycap
  rw [canonicalShadow_eq_kkShadow hk hxcap,
    canonicalShadow_eq_kkShadow hk hycap]
  exact kkShadow_mono n k hxy

@[simp] theorem canonicalShadow_one (k : ℕ) (hk : 1 ≤ k) :
    canonicalShadow k 1 = k := by
  have hdigits : canonicalDigits k 1 = [k] := by
    simpa using canonicalDigits_eq_singleton_choose hk le_rfl
  cases k with
  | zero => omega
  | succ k =>
      simp [canonicalShadow, hdigits, cascadeShadowValue,
        Nat.choose_succ_self_right]

theorem canonicalShadow_pos {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    0 < canonicalShadow k m := by
  have hmono := canonicalShadow_mono k hk hm
  rw [canonicalShadow_one k hk] at hmono
  omega

/-- The finite sentinel extension never exceeds the true numerical shadow. -/
theorem kkShadow_le_canonicalShadow (n k m : ℕ) (hk : 1 ≤ k) :
    kkShadow n k m ≤ canonicalShadow k m := by
  by_cases hm : m ≤ n.choose k
  · rw [kkShadow_eq_canonicalShadow hk hm]
  · have hcap : n.choose k < m := by omega
    by_cases hkn : k ≤ n
    · have hmono := canonicalShadow_mono k hk hcap.le
      have hcapShadow : canonicalShadow k (n.choose k) = n.choose (k - 1) := by
        rw [canonicalShadow,
          canonicalDigits_eq_singleton_choose hk hkn,
          cascadeShadowValue_cons, cascadeValue_nil, Nat.add_zero]
      rw [hcapShadow] at hmono
      exact (kkShadow_le_sentinel n k m).trans hmono
    · by_cases hpred : k - 1 ≤ n
      · have hsucc : k = n + 1 := by omega
        have hsentinel : n.choose (k - 1) = 1 := by
          rw [hsucc]
          simp
        have hkk : kkShadow n k m ≤ 1 := by
          simpa [hsentinel] using kkShadow_le_sentinel n k m
        exact hkk.trans (canonicalShadow_pos hk (by omega))
      · have hsentinel : n.choose (k - 1) = 0 :=
          Nat.choose_eq_zero_of_lt (by omega)
        have hkk : kkShadow n k m ≤ 0 := by
          simpa [hsentinel] using kkShadow_le_sentinel n k m
        exact hkk.trans (Nat.zero_le _)

/-- Feasible ground sets give the same numerical shadow value. -/
theorem kkShadow_eq_kkShadow_of_feasible
    {n₁ n₂ k m : ℕ} (hk : 1 ≤ k)
    (h₁ : m ≤ n₁.choose k) (h₂ : m ≤ n₂.choose k) :
    kkShadow n₁ k m = kkShadow n₂ k m := by
  rw [kkShadow_eq_canonicalShadow hk h₁,
    kkShadow_eq_canonicalShadow hk h₂]

end Erdos776.KruskalKatona


/-!
# Diagonal cascade transfer

This file proves identity (16.1) of `UNIFORM_THEOREM.md`.  A diagonal run of
binomial digits can be placed above an arbitrary canonical tail; one shadow
step lowers the shell and applies the ordinary canonical shadow to the tail.
-/

namespace Erdos776.KruskalKatona

@[simp] theorem length_diagonalDigits (a len : ℕ) :
    (diagonalDigits a len).length = len := by
  induction len generalizing a with
  | zero => rfl
  | succ len ih =>
      simp [diagonalDigits, ih]

theorem choose_diagonal_mono (A b t : ℕ) :
    A.choose b ≤ (A + t).choose (b + t) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hp := Nat.choose_succ_succ (A + t) (b + t)
      rw [show A + (t + 1) = A + t + 1 by omega,
        show b + (t + 1) = b + t + 1 by omega, hp]
      omega

/-- The value of the diagonal shell before attaching its residual tail. -/
theorem cascadeValue_diagonal_shell (A b t : ℕ) :
    cascadeValue (b + t) (diagonalDigits (A + t - 1) t) =
      (A + t).choose (b + t) - A.choose b := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hAt : A + (t + 1) - 1 = A + t := by omega
      rw [hAt, diagonalDigits_succ, cascadeValue_cons,
        show b + (t + 1) - 1 = b + t by omega, ih]
      have hp := Nat.choose_succ_succ (A + t) (b + t)
      rw [show A + (t + 1) = A + t + 1 by omega,
        show b + (t + 1) = b + t + 1 by omega, hp]
      have hmono := choose_diagonal_mono A b t
      simp only [Nat.succ_eq_add_one]
      omega

/-- The same shell after lowering every lower binomial index once. -/
theorem cascadeValue_diagonal_shell_shadow
    (A b t : ℕ) (hb : 1 ≤ b) :
    cascadeValue (b + t - 1) (diagonalDigits (A + t - 1) t) =
      (A + t).choose (b + t - 1) - A.choose (b - 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hAt : A + (t + 1) - 1 = A + t := by omega
      rw [hAt, diagonalDigits_succ, cascadeValue_cons,
        show b + (t + 1) - 1 - 1 = b + t - 1 by omega, ih]
      have hp : (A + t + 1).choose (b + t) =
          (A + t).choose (b + t - 1) + (A + t).choose (b + t) := by
        simpa only [Nat.succ_eq_add_one,
          show b + t - 1 + 1 = b + t by omega] using
            Nat.choose_succ_succ (A + t) (b + t - 1)
      rw [show A + (t + 1) = A + t + 1 by omega,
        show b + (t + 1) - 1 = b + t by omega, hp]
      have hmono : A.choose (b - 1) ≤
          (A + t).choose (b + t - 1) := by
        simpa [show b - 1 + t = b + t - 1 by omega] using
          choose_diagonal_mono A (b - 1) t
      omega

/-- The explicit canonical digits for the transferred shell and residual. -/
def transferDigits (A b t x : ℕ) : List ℕ :=
  diagonalDigits (A + t - 1) t ++ canonicalDigits b x

theorem cascadeValue_transferDigits
    (A b t x : ℕ) (hb : 1 ≤ b) :
    cascadeValue (b + t) (transferDigits A b t x) =
      (A + t).choose (b + t) - A.choose b + x := by
  rw [transferDigits, cascadeValue_append, length_diagonalDigits,
    show b + t - t = b by omega, cascadeValue_diagonal_shell,
    cascadeValue_canonicalDigits hb]

theorem cascadeShadowValue_transferDigits
    (A b t x : ℕ) (hb : 1 ≤ b) :
    cascadeShadowValue (b + t) (transferDigits A b t x) =
      (A + t).choose (b + t - 1) - A.choose (b - 1) +
        canonicalShadow b x := by
  unfold cascadeShadowValue canonicalShadow transferDigits
  rw [cascadeValue_append, length_diagonalDigits,
    show b + t - 1 - t = b - 1 by omega,
    cascadeValue_diagonal_shell_shadow A b t hb]
  rfl

theorem isCanonical_transferDigits
    {A b t x : ℕ} (hb : 1 ≤ b) (hbA : b < A)
    (hx : x < A.choose b) :
    IsCanonical (b + t) (transferDigits A b t x) := by
  induction t with
  | zero =>
      simpa [transferDigits] using isCanonical_canonicalDigits hb
  | succ t ih =>
      have hAt : A + (t + 1) - 1 = A + t := by omega
      rw [transferDigits, hAt, diagonalDigits_succ, List.cons_append]
      rw [show b + (t + 1) = (b + t) + 1 by omega,
        isCanonical_succ_cons]
      refine ⟨by omega, ?_, ?_⟩
      · intro d hd
        rcases List.mem_append.mp hd with hd | hd
        · exact (mem_diagonalDigits_le hd).trans_lt (by omega)
        · exact (canonicalDigits_all_lt hb hx d hd).trans_le (by omega)
      · simpa [transferDigits] using ih

/--
**Diagonal transfer identity (16.1).**  The strict residual bound prevents a
carry into the diagonal shell, so shadowing acts independently on the shell
and residual cascade.
-/
theorem canonicalShadow_diagonal_transfer
    {A b t x : ℕ} (hb : 1 ≤ b) (hbA : b < A)
    (hx : x < A.choose b) :
    canonicalShadow (b + t)
        ((A + t).choose (b + t) - A.choose b + x) =
      (A + t).choose (b + t - 1) - A.choose (b - 1) +
        canonicalShadow b x := by
  let digits := transferDigits A b t x
  have hcanon : IsCanonical (b + t) digits :=
    isCanonical_transferDigits hb hbA hx
  have hvalue : cascadeValue (b + t) digits =
      (A + t).choose (b + t) - A.choose b + x :=
    cascadeValue_transferDigits A b t x hb
  have hnormal : canonicalDigits (b + t)
      ((A + t).choose (b + t) - A.choose b + x) = digits :=
    (canonicalDigits_unique hcanon hvalue).symm
  rw [canonicalShadow, hnormal]
  exact cascadeShadowValue_transferDigits A b t x hb

/-- Peel one complete binomial shell followed by a subcritical residual. -/
theorem canonicalShadow_add_shell
    {B k x : ℕ} (hk : 2 ≤ k) (hkB : k ≤ B)
    (hx : x < B.choose (k - 1)) :
    canonicalShadow k (B.choose k + x) =
      B.choose (k - 1) + canonicalShadow (k - 1) x := by
  have htransfer := canonicalShadow_diagonal_transfer
    (A := B) (b := k - 1) (t := 1) (x := x)
    (by omega) (by omega) hx
  have hpIn : (B + 1).choose k =
      B.choose (k - 1) + B.choose k := by
    simpa only [Nat.succ_eq_add_one, show k - 1 + 1 = k by omega] using
      Nat.choose_succ_succ B (k - 1)
  have hpOut : (B + 1).choose (k - 1) =
      B.choose (k - 2) + B.choose (k - 1) := by
    simpa only [Nat.succ_eq_add_one,
      show k - 2 + 1 = k - 1 by omega] using
      Nat.choose_succ_succ B (k - 2)
  have harg : (B + 1).choose k - B.choose (k - 1) + x =
      B.choose k + x := by omega
  have hout : (B + 1).choose (k - 1) - B.choose (k - 2) =
      B.choose (k - 1) := by omega
  simpa only [show k - 1 + 1 = k by omega,
    show k - 1 - 1 = k - 2 by omega, harg, hout] using htransfer

end Erdos776.KruskalKatona


/-!
# Two-point padding and persistent free sets

This is the symbolic construction used in both `TECHNICAL_NOTE.md` and
`SMALL_R_NOTE.md`.  It is stated over an arbitrary ground-set type.  Two new
points are represented by the right summand `Fin 2`; old points use the left
summand.
-/

namespace Erdos776.Antichain

open Finset

variable {α : Type*} [DecidableEq α]

/-- The left injection as a bundled embedding. -/
def oldEmbedding : α ↪ α ⊕ Fin 2 :=
  ⟨Sum.inl, Sum.inl_injective⟩

/-- The right injection of the two new points as a bundled embedding. -/
def newPointEmbedding : Fin 2 ↪ α ⊕ Fin 2 :=
  ⟨Sum.inr, Sum.inr_injective⟩

/-- Embed an old set into the enlarged ground set. -/
def oldSet (s : Finset α) : Finset (α ⊕ Fin 2) :=
  s.map oldEmbedding

/-- The pair of newly added points. -/
def addedPoints : Finset (α ⊕ Fin 2) :=
  (Finset.univ : Finset (Fin 2)).map newPointEmbedding

/-- The new member born from a free set `d`. -/
def paddedSet (d : Finset α) : Finset (α ⊕ Fin 2) :=
  oldSet d ∪ addedPoints

/-- The free set retained for the next padding stage; it uses only new point `0`. -/
def persistentSet (d : Finset α) : Finset (α ⊕ Fin 2) :=
  insert (Sum.inr (0 : Fin 2)) (oldSet d)

omit [DecidableEq α] in
@[simp] theorem mem_oldSet_inl {s : Finset α} {x : α} :
    Sum.inl x ∈ oldSet s ↔ x ∈ s := by
  simp [oldSet, oldEmbedding]

omit [DecidableEq α] in
@[simp] theorem not_mem_oldSet_inr {s : Finset α} {j : Fin 2} :
    Sum.inr j ∉ oldSet s := by
  simp [oldSet, oldEmbedding]

omit [DecidableEq α] in
@[simp] theorem mem_addedPoints_inr (j : Fin 2) :
    Sum.inr j ∈ (addedPoints : Finset (α ⊕ Fin 2)) := by
  simp [addedPoints, newPointEmbedding]

omit [DecidableEq α] in
@[simp] theorem not_mem_addedPoints_inl (x : α) :
    Sum.inl x ∉ (addedPoints : Finset (α ⊕ Fin 2)) := by
  simp [addedPoints, newPointEmbedding]

@[simp] theorem mem_paddedSet_inl {d : Finset α} {x : α} :
    Sum.inl x ∈ paddedSet d ↔ x ∈ d := by
  simp [paddedSet]

@[simp] theorem mem_paddedSet_inr {d : Finset α} (j : Fin 2) :
    Sum.inr j ∈ paddedSet d := by
  simp [paddedSet]

@[simp] theorem mem_persistentSet_inl {d : Finset α} {x : α} :
    Sum.inl x ∈ persistentSet d ↔ x ∈ d := by
  simp [persistentSet]

@[simp] theorem mem_persistentSet_zero {d : Finset α} :
    Sum.inr (0 : Fin 2) ∈ persistentSet d := by
  simp [persistentSet]

@[simp] theorem not_mem_persistentSet_one {d : Finset α} :
    Sum.inr (1 : Fin 2) ∉ persistentSet d := by
  simp [persistentSet]

theorem paddedSet_injective : Function.Injective (paddedSet (α := α)) := by
  intro d e hde
  ext x
  have h := congrArg (fun s => Sum.inl x ∈ s) hde
  simpa using h

theorem persistentSet_injective : Function.Injective (persistentSet (α := α)) := by
  intro d e hde
  ext x
  have h := congrArg (fun s => Sum.inl x ∈ s) hde
  simpa using h

/-- `paddedSet` as an embedding, used to map whole families. -/
def paddedSetEmbedding : Finset α ↪ Finset (α ⊕ Fin 2) :=
  ⟨paddedSet, paddedSet_injective⟩

/-- `persistentSet` as an embedding. -/
def persistentSetEmbedding : Finset α ↪ Finset (α ⊕ Fin 2) :=
  ⟨persistentSet, persistentSet_injective⟩

/-- The old members inside the enlarged ground set. -/
def oldFamily (C : Family α) : Family (α ⊕ Fin 2) :=
  mapFamily oldEmbedding C

/-- The family of members born in one padding step. -/
def bornFamily (D : Family α) : Family (α ⊕ Fin 2) :=
  D.map paddedSetEmbedding

/-- The complete result of one two-point padding step. -/
def twoPointPadding (C D : Family α) : Family (α ⊕ Fin 2) :=
  oldFamily C ∪ bornFamily D

/-- The family of free sets retained after the padding step. -/
def persistentFreeFamily (D : Family α) : Family (α ⊕ Fin 2) :=
  D.map persistentSetEmbedding

@[simp] theorem mem_bornFamily {D : Family α} {u : Finset (α ⊕ Fin 2)} :
    u ∈ bornFamily D ↔ ∃ d ∈ D, paddedSet d = u := by
  simp [bornFamily, paddedSetEmbedding]

@[simp] theorem mem_persistentFreeFamily
    {D : Family α} {u : Finset (α ⊕ Fin 2)} :
    u ∈ persistentFreeFamily D ↔ ∃ d ∈ D, persistentSet d = u := by
  simp [persistentFreeFamily, persistentSetEmbedding]

@[simp] theorem card_bornFamily (D : Family α) :
    (bornFamily D).card = D.card := by
  simp [bornFamily]

@[simp] theorem card_persistentFreeFamily (D : Family α) :
    (persistentFreeFamily D).card = D.card := by
  simp [persistentFreeFamily]

omit [DecidableEq α] in
theorem oldSet_disjoint_addedPoints (s : Finset α) :
    Disjoint (oldSet s) (addedPoints : Finset (α ⊕ Fin 2)) := by
  rw [Finset.disjoint_left]
  intro x hxs hxa
  obtain x | x := x
  · exact not_mem_addedPoints_inl x hxa
  · exact not_mem_oldSet_inr hxs

@[simp] theorem card_paddedSet (d : Finset α) :
    (paddedSet d).card = d.card + 2 := by
  rw [paddedSet, card_union_of_disjoint (oldSet_disjoint_addedPoints d)]
  simp [oldSet, addedPoints]

@[simp] theorem card_persistentSet (d : Finset α) :
    (persistentSet d).card = d.card + 1 := by
  rw [persistentSet, card_insert_of_notMem]
  · simp [oldSet]
  · exact not_mem_oldSet_inr

theorem bornFamily_sized {D : Family α} {s : ℕ} (hs : 1 ≤ s)
    (hD : (D : Set (Finset α)).Sized (s - 1)) :
    (bornFamily D : Set (Finset (α ⊕ Fin 2))).Sized (s + 1) := by
  intro u hu
  obtain ⟨d, hd, rfl⟩ := mem_bornFamily.mp hu
  rw [card_paddedSet, hD hd]
  omega

theorem persistentFreeFamily_sized {D : Family α} {s : ℕ} (hs : 1 ≤ s)
    (hD : (D : Set (Finset α)).Sized (s - 1)) :
    (persistentFreeFamily D : Set (Finset (α ⊕ Fin 2))).Sized s := by
  intro u hu
  obtain ⟨d, hd, rfl⟩ := mem_persistentFreeFamily.mp hu
  rw [card_persistentSet, hD hd]
  omega

theorem oldSet_not_subset_paddedSet
    {C D : Family α} (hfree : IsFreeFamily C D)
    {c d : Finset α} (hc : c ∈ C) (hd : d ∈ D) :
    ¬ oldSet c ⊆ paddedSet d := by
  intro hsub
  apply hfree d hd c hc
  intro x hx
  exact mem_paddedSet_inl.mp (hsub (mem_oldSet_inl.mpr hx))

theorem paddedSet_not_subset_oldSet (c d : Finset α) :
    ¬ paddedSet d ⊆ oldSet c := by
  intro hsub
  exact not_mem_oldSet_inr (hsub (mem_paddedSet_inr (d := d) 0))

/-- The set-theoretic heart of the two-point padding lemma. -/
theorem isSperner_twoPointPadding
    {C D : Family α} {s : ℕ} (hs : 1 ≤ s)
    (hC : IsSperner C)
    (hD : (D : Set (Finset α)).Sized (s - 1))
    (hfree : IsFreeFamily C D) :
    IsSperner (twoPointPadding C D) := by
  have hold : IsSperner (oldFamily C) := isSperner_mapFamily hC
  have hborn : IsSperner (bornFamily D) :=
    (bornFamily_sized hs hD).isAntichain
  unfold IsSperner twoPointPadding
  rw [Finset.coe_union]
  apply isAntichain_union.mpr
  refine ⟨hold, hborn, ?_⟩
  intro a ha b hb hab
  obtain ⟨c, hc, rfl⟩ := mem_mapFamily.mp ha
  obtain ⟨d, hd, rfl⟩ := mem_bornFamily.mp hb
  exact ⟨oldSet_not_subset_paddedSet hfree hc hd,
    paddedSet_not_subset_oldSet c d⟩

/-- Every old level survives a padding step with at least its old cardinality. -/
theorem card_level_le_twoPointPadding
    (C D : Family α) (i : ℕ) :
    (level C i).card ≤ (level (twoPointPadding C D) i).card := by
  have hsubset : oldFamily C ⊆ twoPointPadding C D := subset_union_left
  have hlevel := card_le_card (level_mono hsubset i)
  simpa [oldFamily] using hlevel

theorem level_bornFamily_eq {D : Family α} {s : ℕ} (hs : 1 ≤ s)
    (hD : (D : Set (Finset α)).Sized (s - 1)) :
    level (bornFamily D) (s + 1) = bornFamily D := by
  ext u
  constructor
  · exact fun hu => (mem_level.mp hu).1
  · intro hu
    exact mem_level.mpr ⟨hu, bornFamily_sized hs hD hu⟩

/-- The born family supplies the next level. -/
theorem card_freeFamily_le_new_level
    {C D : Family α} {s : ℕ} (hs : 1 ≤ s)
    (hD : (D : Set (Finset α)).Sized (s - 1)) :
    D.card ≤ (level (twoPointPadding C D) (s + 1)).card := by
  have hsubset : bornFamily D ⊆ twoPointPadding C D := subset_union_right
  have hlevel := card_le_card (level_mono hsubset (s + 1))
  rw [level_bornFamily_eq hs hD, card_bornFamily] at hlevel
  exact hlevel

/-- One padding step extends multiplicity support from `2..s` to `2..s+1`. -/
theorem hasMultiplicities_twoPointPadding
    {C D : Family α} {r s : ℕ} (hs : 1 ≤ s)
    (hlevels : HasMultiplicities C r 2 s)
    (hDsize : (D : Set (Finset α)).Sized (s - 1))
    (hDcard : r ≤ D.card) :
    HasMultiplicities (twoPointPadding C D) r 2 (s + 1) := by
  intro i hi his
  unfold HasMultiplicityAt
  by_cases htop : i = s + 1
  · subst i
    exact hDcard.trans (card_freeFamily_le_new_level hs hDsize)
  · have his' : i ≤ s := by omega
    exact (hlevels i hi his').trans (card_level_le_twoPointPadding C D i)

theorem oldSet_not_subset_persistentSet
    {C D : Family α} (hfree : IsFreeFamily C D)
    {c d : Finset α} (hc : c ∈ C) (hd : d ∈ D) :
    ¬ oldSet c ⊆ persistentSet d := by
  intro hsub
  apply hfree d hd c hc
  intro x hx
  exact mem_persistentSet_inl.mp (hsub (mem_oldSet_inl.mpr hx))

theorem paddedSet_not_subset_persistentSet (d e : Finset α) :
    ¬ paddedSet e ⊆ persistentSet d := by
  intro hsub
  exact not_mem_persistentSet_one
    (hsub (mem_paddedSet_inr (d := e) (1 : Fin 2)))

/-- The chosen free sets remain free after the padding step. -/
theorem isFreeFamily_persistent
    {C D : Family α} (hfree : IsFreeFamily C D) :
    IsFreeFamily (twoPointPadding C D) (persistentFreeFamily D) := by
  intro u hu
  obtain ⟨d, hd, rfl⟩ := mem_persistentFreeFamily.mp hu
  intro a ha
  rcases mem_union.mp ha with ha | ha
  · obtain ⟨c, hc, rfl⟩ := mem_mapFamily.mp ha
    exact oldSet_not_subset_persistentSet hfree hc hd
  · obtain ⟨e, he, rfl⟩ := mem_bornFamily.mp ha
    exact paddedSet_not_subset_persistentSet d e

/--
The complete reusable padding package: antichain, one extra occupied level,
and a same-cardinality free family ready for the next iteration.
-/
theorem twoPointPadding_with_persistent_free
    {C D : Family α} {r s : ℕ} (hs : 1 ≤ s)
    (hC : IsSperner C)
    (hlevels : HasMultiplicities C r 2 s)
    (hDsize : (D : Set (Finset α)).Sized (s - 1))
    (hDcard : r ≤ D.card)
    (hfree : IsFreeFamily C D) :
    IsSperner (twoPointPadding C D) ∧
      HasMultiplicities (twoPointPadding C D) r 2 (s + 1) ∧
      (persistentFreeFamily D : Set (Finset (α ⊕ Fin 2))).Sized s ∧
      (persistentFreeFamily D).card = D.card ∧
      IsFreeFamily (twoPointPadding C D) (persistentFreeFamily D) := by
  exact ⟨isSperner_twoPointPadding hs hC hDsize hfree,
    hasMultiplicities_twoPointPadding hs hlevels hDsize hDcard,
    persistentFreeFamily_sized hs hDsize,
    card_persistentFreeFamily D,
    isFreeFamily_persistent hfree⟩

/-! ### Arbitrarily many padding stages -/

universe u

/-- The ground type after adjoining `t` successive pairs of points. -/
def IteratedGround (α : Type u) : ℕ → Type u
  | 0 => α
  | t + 1 => IteratedGround α t ⊕ Fin 2

instance iteratedGroundDecidableEq [DecidableEq α] :
    (t : ℕ) → DecidableEq (IteratedGround α t)
  | 0 => inferInstanceAs (DecidableEq α)
  | t + 1 =>
      letI : DecidableEq (IteratedGround α t) := iteratedGroundDecidableEq t
      inferInstanceAs (DecidableEq (IteratedGround α t ⊕ Fin 2))

instance iteratedGroundFintype [Fintype α] (t : ℕ) :
    Fintype (IteratedGround α t) := by
  induction t with
  | zero => simpa [IteratedGround] using (inferInstance : Fintype α)
  | succ t ih =>
      letI : Fintype (IteratedGround α t) := ih
      change Fintype (IteratedGround α t ⊕ Fin 2)
      exact inferInstance

omit [DecidableEq α] in
@[simp] theorem card_iteratedGround [Fintype α] (t : ℕ) :
    Fintype.card (IteratedGround α t) = Fintype.card α + 2 * t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      change Fintype.card (IteratedGround α t ⊕ Fin 2) =
        Fintype.card α + 2 * (t + 1)
      rw [Fintype.card_sum, ih]
      simp
      omega

/-- A family together with the free family reserved for the next stage. -/
structure PaddingState (α : Type u) where
  family : Family α
  free : Family α

/-- Iterate the explicit padding construction `t` times. -/
def iteratedPaddingState
    (C D : Family α) : (t : ℕ) → PaddingState (IteratedGround α t)
  | 0 => ⟨C, D⟩
  | t + 1 =>
      let previous := iteratedPaddingState C D t
      ⟨twoPointPadding previous.family previous.free,
        persistentFreeFamily previous.free⟩

/--
Persistent freeness really supports any finite number of padding stages, not
merely the first checked stage.
-/
theorem iteratedPaddingState_spec
    {C D : Family α} {r s : ℕ} (hs : 1 ≤ s)
    (hC : IsSperner C)
    (hlevels : HasMultiplicities C r 2 s)
    (hDsize : (D : Set (Finset α)).Sized (s - 1))
    (hDcard : r ≤ D.card)
    (hfree : IsFreeFamily C D) :
    ∀ t,
      let state := iteratedPaddingState C D t
      IsSperner state.family ∧
        HasMultiplicities state.family r 2 (s + t) ∧
        (state.free : Set (Finset (IteratedGround α t))).Sized (s + t - 1) ∧
        state.free.card = D.card ∧
        IsFreeFamily state.family state.free := by
  intro t
  induction t with
  | zero =>
      change IsSperner C ∧ HasMultiplicities C r 2 s ∧
        (D : Set (Finset α)).Sized (s - 1) ∧ D.card = D.card ∧ IsFreeFamily C D
      exact ⟨hC, hlevels, hDsize, rfl, hfree⟩
  | succ t ih =>
      dsimp only [iteratedPaddingState]
      have hst : 1 ≤ s + t := by omega
      have hcard : r ≤ (iteratedPaddingState C D t).free.card := by
        rw [ih.2.2.2.1]
        exact hDcard
      have hstep := twoPointPadding_with_persistent_free
        hst ih.1 ih.2.1 ih.2.2.1 hcard ih.2.2.2.2
      refine ⟨hstep.1, ?_, ?_, ?_, hstep.2.2.2.2⟩
      · show HasMultiplicities (twoPointPadding (iteratedPaddingState C D t).family
          (iteratedPaddingState C D t).free) r 2 (s + (t + 1))
        exact hstep.2.1
      · show (persistentFreeFamily (iteratedPaddingState C D t).free :
          Set (Finset (IteratedGround α t ⊕ Fin 2))).Sized (s + t)
        exact hstep.2.2.1
      · exact hstep.2.2.2.1.trans ih.2.2.2.1

end Erdos776.Antichain


/-!
# The necessary half of the antichain profile criterion

For a finite antichain, `cumulativeLevel F i` consists of the `i`-sets lying
below at least one member of `F`.  The shadow of level `i+1` is contained in
level `i`; moreover it is disjoint from the actual level-`i` slice of `F`.
Kruskal--Katona therefore gives the top-down profile recurrence as a lower
bound.  This is the Clements--Daykin--Godfrey--Hilton necessity argument used
by L4.
-/

namespace Erdos776.KruskalKatona

open Finset

/-- The members of a family lying on one level. -/
def levelFamily {n : ℕ} (F : Finset (Finset (Fin n))) (i : ℕ) :
    Finset (Finset (Fin n)) :=
  F.filter fun s => s.card = i

@[simp] theorem mem_levelFamily {n i : ℕ}
    {F : Finset (Finset (Fin n))} {s : Finset (Fin n)} :
    s ∈ levelFamily F i ↔ s ∈ F ∧ s.card = i := by
  simp [levelFamily]

/-- The level-`i` part of the down-closure of a family. -/
def cumulativeLevel {n : ℕ} (F : Finset (Finset (Fin n))) (i : ℕ) :
    Finset (Finset (Fin n)) :=
  (Finset.univ.powersetCard i).filter fun s => ∃ t ∈ F, s ⊆ t

@[simp] theorem mem_cumulativeLevel {n i : ℕ}
    {F : Finset (Finset (Fin n))} {s : Finset (Fin n)} :
    s ∈ cumulativeLevel F i ↔ s.card = i ∧ ∃ t ∈ F, s ⊆ t := by
  simp [cumulativeLevel, and_comm]

theorem levelFamily_subset_cumulativeLevel {n i : ℕ}
    {F : Finset (Finset (Fin n))} :
    levelFamily F i ⊆ cumulativeLevel F i := by
  intro s hs
  exact mem_cumulativeLevel.mpr
    ⟨(mem_levelFamily.mp hs).2, s, (mem_levelFamily.mp hs).1, Subset.rfl⟩

theorem cumulativeLevel_sized {n i : ℕ}
    {F : Finset (Finset (Fin n))} :
    (cumulativeLevel F i : Set (Finset (Fin n))).Sized i := by
  intro s hs
  exact (mem_cumulativeLevel.mp hs).1

theorem card_cumulativeLevel_le_choose {n i : ℕ}
    {F : Finset (Finset (Fin n))} :
    (cumulativeLevel F i).card ≤ n.choose i := by
  calc
    (cumulativeLevel F i).card ≤ (Finset.univ.powersetCard i).card :=
      card_le_card (filter_subset _ _)
    _ = n.choose i := by simp

/-- Taking one shadow step stays in the down-closure of the original family. -/
theorem shadow_cumulativeLevel_subset {n i : ℕ}
    {F : Finset (Finset (Fin n))} :
    Finset.shadow (cumulativeLevel F (i + 1)) ⊆ cumulativeLevel F i := by
  intro s hs
  obtain ⟨u, hu, x, hx, rfl⟩ := mem_shadow_iff.mp hs
  obtain ⟨hu_card, t, htF, hut⟩ := mem_cumulativeLevel.mp hu
  apply mem_cumulativeLevel.mpr
  constructor
  · rw [card_erase_of_mem hx, hu_card]
    omega
  · exact ⟨t, htF, (Finset.erase_subset x u).trans hut⟩

/-- Antichain members on level `i` avoid the down-closure shadow from above. -/
theorem disjoint_levelFamily_shadow_cumulativeLevel
    {n i : ℕ} {F : Finset (Finset (Fin n))}
    (hanti : IsAntichain (· ⊆ ·) (F : Set (Finset (Fin n)))) :
    Disjoint (levelFamily F i)
      (Finset.shadow (cumulativeLevel F (i + 1))) := by
  rw [Finset.disjoint_left]
  intro s hsF hsShadow
  obtain ⟨u, hu, x, hx, hsu⟩ := mem_shadow_iff.mp hsShadow
  obtain ⟨hu_card, t, htF, hut⟩ := mem_cumulativeLevel.mp hu
  have hs_member : s ∈ F := (mem_levelFamily.mp hsF).1
  have hst : s ⊆ t := by
    rw [← hsu]
    exact (Finset.erase_subset x u).trans hut
  have heq : s = t := hanti.eq hs_member htF hst
  have hs_card : s.card = i := (mem_levelFamily.mp hsF).2
  have ht_card_ge : i + 1 ≤ t.card := by
    rw [← hu_card]
    exact card_le_card hut
  rw [heq] at hs_card
  omega

/--
One necessary profile step: a level with at least `q` antichain members,
together with the shadow forced from above, consumes at least
`q + kkShadow` sets in the current cumulative level.
-/
theorem profile_step_le_cumulativeLevel
    {n i q : ℕ} {F : Finset (Finset (Fin n))}
    (hanti : IsAntichain (· ⊆ ·) (F : Set (Finset (Fin n))))
    (hlevel : q ≤ (levelFamily F i).card) :
    q + kkShadow n (i + 1) (cumulativeLevel F (i + 1)).card ≤
      (cumulativeLevel F i).card := by
  have hshadow :
      kkShadow n (i + 1) (cumulativeLevel F (i + 1)).card ≤
        (Finset.shadow (cumulativeLevel F (i + 1))).card :=
    kkShadow_le_card_shadow cumulativeLevel_sized
  have hunion_subset :
      levelFamily F i ∪ Finset.shadow (cumulativeLevel F (i + 1)) ⊆
        cumulativeLevel F i :=
    union_subset levelFamily_subset_cumulativeLevel shadow_cumulativeLevel_subset
  have hunion_card := card_le_card hunion_subset
  rw [card_union_of_disjoint
    (disjoint_levelFamily_shadow_cumulativeLevel hanti)] at hunion_card
  omega

end Erdos776.KruskalKatona


/-!
# Sufficiency in the prescribed-profile criterion

Given a top-down cascade recurrence which fits inside every level of `Fin n`,
this file constructs the corresponding colex antichain.  Together with
`ProfileNecessity.lean`, this supplies both mathematical directions of the
squashed-antichain profile theorem used throughout the research package.
-/

namespace Erdos776.KruskalKatona

open Finset
open Erdos776.Antichain

/-- The colex initial segment represented by the canonical cascade of `m`. -/
noncomputable def canonicalFamily (n k m : ℕ) : Family (Fin n) :=
  finifyFamily n (cascadeFamily k (canonicalDigits k m))

theorem canonicalFamily_sized
    {n k m : ℕ} (hk : 1 ≤ k) (hm : m ≤ n.choose k) :
    (canonicalFamily n k m : Set (Finset (Fin n))).Sized k := by
  exact sized_finifyFamily
    (bounded_cascadeFamily_canonicalDigits hk hm)
    (sized_cascadeFamily (isCanonical_canonicalDigits hk))

@[simp] theorem card_canonicalFamily
    {n k m : ℕ} (hk : 1 ≤ k) (hm : m ≤ n.choose k) :
    (canonicalFamily n k m).card = m := by
  rw [canonicalFamily,
    card_finifyFamily (bounded_cascadeFamily_canonicalDigits hk hm),
    card_cascadeFamily (isCanonical_canonicalDigits hk),
    cascadeValue_canonicalDigits hk]

theorem canonicalFamily_isInitSeg
    {n k m : ℕ} (hk : 1 ≤ k) (hm : m ≤ n.choose k) :
    Finset.Colex.IsInitSeg (canonicalFamily n k m) k := by
  exact isInitSeg_finifyFamily
    (bounded_cascadeFamily_canonicalDigits hk hm)
    (isInitSeg_cascadeFamily (isCanonical_canonicalDigits hk))

@[simp] theorem card_shadow_canonicalFamily
    {n k m : ℕ} (hk : 1 ≤ k) (hm : m ≤ n.choose k) :
    (Finset.shadow (canonicalFamily n k m)).card = canonicalShadow k m := by
  rw [canonicalFamily,
    card_shadow_finifyFamily (bounded_cascadeFamily_canonicalDigits hk hm),
    card_shadow_cascadeFamily (isCanonical_canonicalDigits hk)]
  rfl

/-- Initial colex segments are ordered by their cardinalities. -/
theorem initSeg_subset_of_card_le
    {n k : ℕ} {A B : Family (Fin n)}
    (hA : Finset.Colex.IsInitSeg A k)
    (hB : Finset.Colex.IsInitSeg B k)
    (hcard : A.card ≤ B.card) : A ⊆ B := by
  rcases hA.total hB with hAB | hBA
  · exact hAB
  · have heq : B = A := eq_of_subset_of_card_le hBA hcard
    exact heq ▸ Subset.rfl

/--
`m` is the top-down cascade recurrence for profile `f` on levels `lo..hi`.
The zero at `hi+1` makes the top-level equation uniform with all other levels.
-/
def IsProfileRecurrence
    (n lo hi : ℕ) (f m : ℕ → ℕ) : Prop :=
  m (hi + 1) = 0 ∧
    (∀ i, lo ≤ i → i ≤ hi →
      m i = f i + canonicalShadow (i + 1) (m (i + 1))) ∧
    ∀ i, lo ≤ i → i ≤ hi + 1 → m i ≤ n.choose i

/-- The members selected at level `i` after excluding the shadow from above. -/
noncomputable def selectedLayer (n : ℕ) (m : ℕ → ℕ) (i : ℕ) :
    Family (Fin n) :=
  canonicalFamily n i (m i) \
    Finset.shadow (canonicalFamily n (i + 1) (m (i + 1)))

/-- One recurrence step says that the shadow from above lies in the next segment. -/
theorem shadow_canonicalFamily_subset
    {n lo hi : ℕ} {f m : ℕ → ℕ}
    (hlo : 1 ≤ lo) (hrec : IsProfileRecurrence n lo hi f m)
    {i : ℕ} (hloi : lo ≤ i) (hihi : i ≤ hi) :
    Finset.shadow (canonicalFamily n (i + 1) (m (i + 1))) ⊆
      canonicalFamily n i (m i) := by
  have hi1 : 1 ≤ i := hlo.trans hloi
  have hcap_i : m i ≤ n.choose i := hrec.2.2 i hloi (by omega)
  have hcap_next : m (i + 1) ≤ n.choose (i + 1) :=
    hrec.2.2 (i + 1) (by omega) (by omega)
  have hcurrent := canonicalFamily_isInitSeg hi1 hcap_i
  have hnext := canonicalFamily_isInitSeg (by omega : 1 ≤ i + 1) hcap_next
  have hshadow : Finset.Colex.IsInitSeg
      (Finset.shadow (canonicalFamily n (i + 1) (m (i + 1)))) i := by
    simpa using hnext.shadow
  apply initSeg_subset_of_card_le hshadow hcurrent
  rw [card_shadow_canonicalFamily (by omega) hcap_next,
    card_canonicalFamily hi1 hcap_i, hrec.2.1 i hloi hihi]
  omega

theorem selectedLayer_sized
    {n lo hi : ℕ} {f m : ℕ → ℕ}
    (hlo : 1 ≤ lo) (hrec : IsProfileRecurrence n lo hi f m)
    {i : ℕ} (hloi : lo ≤ i) (hihi : i ≤ hi) :
    (selectedLayer n m i : Set (Finset (Fin n))).Sized i := by
  intro s hs
  have hcap : m i ≤ n.choose i := hrec.2.2 i hloi (by omega)
  exact canonicalFamily_sized (hlo.trans hloi) hcap (mem_sdiff.mp hs).1

@[simp] theorem card_selectedLayer
    {n lo hi : ℕ} {f m : ℕ → ℕ}
    (hlo : 1 ≤ lo) (hrec : IsProfileRecurrence n lo hi f m)
    {i : ℕ} (hloi : lo ≤ i) (hihi : i ≤ hi) :
    (selectedLayer n m i).card = f i := by
  have hcap_i : m i ≤ n.choose i := hrec.2.2 i hloi (by omega)
  have hcap_next : m (i + 1) ≤ n.choose (i + 1) :=
    hrec.2.2 (i + 1) (by omega) (by omega)
  rw [selectedLayer, card_sdiff_of_subset
      (shadow_canonicalFamily_subset hlo hrec hloi hihi),
    card_canonicalFamily (hlo.trans hloi) hcap_i,
    card_shadow_canonicalFamily (by omega) hcap_next,
    hrec.2.1 i hloi hihi]
  omega

/-- The antichain assembled from all selected profile layers. -/
noncomputable def profileFamily
    (n lo hi : ℕ) (m : ℕ → ℕ) : Family (Fin n) :=
  (Finset.Icc lo hi).biUnion (selectedLayer n m)

@[simp] theorem mem_profileFamily
    {n lo hi : ℕ} {m : ℕ → ℕ} {s : Finset (Fin n)} :
    s ∈ profileFamily n lo hi m ↔
      ∃ i ∈ Finset.Icc lo hi, s ∈ selectedLayer n m i := by
  simp [profileFamily]

/--
If a set from a higher canonical segment contains a lower-sized set, the
lower set belongs to the corresponding lower canonical segment.
-/
theorem subset_mem_canonicalFamily
    {n lo hi : ℕ} {f m : ℕ → ℕ}
    (hlo : 1 ≤ lo) (hrec : IsProfileRecurrence n lo hi f m)
    {i j : ℕ} (hloi : lo ≤ i) (hij : i ≤ j) (hjhi : j ≤ hi + 1)
    {u v : Finset (Fin n)}
    (hucard : u.card = i) (hvcard : v.card = j)
    (huv : u ⊆ v) (hv : v ∈ canonicalFamily n j (m j)) :
    u ∈ canonicalFamily n i (m i) := by
  induction j, hij using Nat.le_induction generalizing v with
  | base =>
      have huv_eq : u = v := eq_of_subset_of_card_le huv (by omega)
      simpa [huv_eq] using hv
  | succ j hij ih =>
      obtain ⟨w, huw, hwv, hwcard⟩ :=
        exists_subsuperset_card_eq huv (by omega) (by omega : j ≤ v.card)
      have hwshadow : w ∈ Finset.shadow (canonicalFamily n (j + 1) (m (j + 1))) := by
        apply mem_shadow_iff_exists_mem_card_add_one.mpr
        exact ⟨v, hv, hwv, by omega⟩
      have hjlo : lo ≤ j := hloi.trans hij
      have hjhi' : j ≤ hi := by omega
      have hw : w ∈ canonicalFamily n j (m j) :=
        shadow_canonicalFamily_subset hlo hrec hjlo hjhi' hwshadow
      exact ih (by omega) hwcard huw hw

/-- The selected layers are pairwise incomparable. -/
theorem isSperner_profileFamily
    {n lo hi : ℕ} {f m : ℕ → ℕ}
    (hlo : 1 ≤ lo) (hrec : IsProfileRecurrence n lo hi f m) :
    IsSperner (profileFamily n lo hi m) := by
  intro a ha b hb hab hsub
  obtain ⟨i, hiIcc, hai⟩ := mem_profileFamily.mp ha
  obtain ⟨j, hjIcc, hbj⟩ := mem_profileFamily.mp hb
  have hiBounds : lo ≤ i ∧ i ≤ hi := Finset.mem_Icc.mp hiIcc
  have hjBounds : lo ≤ j ∧ j ≤ hi := Finset.mem_Icc.mp hjIcc
  have hacard : a.card = i :=
    selectedLayer_sized hlo hrec hiBounds.1 hiBounds.2 hai
  have hbcard : b.card = j :=
    selectedLayer_sized hlo hrec hjBounds.1 hjBounds.2 hbj
  have hij : i < j := by
    have hssub : a ⊂ b := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hab⟩
    exact hacard ▸ hbcard ▸ card_lt_card hssub
  obtain ⟨u, hau, hub, hucard⟩ :=
    exists_subsuperset_card_eq (n := i + 1) hsub
      (by omega) (by omega : i + 1 ≤ b.card)
  have hbM : b ∈ canonicalFamily n j (m j) := (mem_sdiff.mp hbj).1
  have huM : u ∈ canonicalFamily n (i + 1) (m (i + 1)) :=
    subset_mem_canonicalFamily (i := i + 1) (j := j)
      hlo hrec (by omega) (by omega) (by omega)
      hucard hbcard hub hbM
  have haShadow : a ∈ Finset.shadow (canonicalFamily n (i + 1) (m (i + 1))) := by
    apply mem_shadow_iff_exists_mem_card_add_one.mpr
    exact ⟨u, huM, hau, by omega⟩
  exact (mem_sdiff.mp hai).2 haShadow

theorem level_profileFamily
    {n lo hi : ℕ} {f m : ℕ → ℕ}
    (hlo : 1 ≤ lo) (hrec : IsProfileRecurrence n lo hi f m)
    {i : ℕ} (hloi : lo ≤ i) (hihi : i ≤ hi) :
    level (profileFamily n lo hi m) i = selectedLayer n m i := by
  ext s
  constructor
  · intro hs
    obtain ⟨hsF, hscard⟩ := mem_level.mp hs
    obtain ⟨j, hjIcc, hsj⟩ := mem_profileFamily.mp hsF
    have hjBounds : lo ≤ j ∧ j ≤ hi := Finset.mem_Icc.mp hjIcc
    have hjcard : s.card = j :=
      selectedLayer_sized hlo hrec hjBounds.1 hjBounds.2 hsj
    have : j = i := by omega
    simpa [this] using hsj
  · intro hs
    apply mem_level.mpr
    refine ⟨mem_profileFamily.mpr ⟨i, mem_Icc.mpr ⟨hloi, hihi⟩, hs⟩, ?_⟩
    exact selectedLayer_sized hlo hrec hloi hihi hs

/-- Every member of the constructed family lies on one of the requested levels. -/
theorem profileFamily_card_mem_Icc
    {n lo hi : ℕ} {f m : ℕ → ℕ}
    (hlo : 1 ≤ lo) (hrec : IsProfileRecurrence n lo hi f m)
    {s : Finset (Fin n)} (hs : s ∈ profileFamily n lo hi m) :
    s.card ∈ Finset.Icc lo hi := by
  obtain ⟨i, hiIcc, hsi⟩ := mem_profileFamily.mp hs
  have hiBounds : lo ≤ i ∧ i ≤ hi := Finset.mem_Icc.mp hiIcc
  have hcard := selectedLayer_sized hlo hrec hiBounds.1 hiBounds.2 hsi
  simpa [hcard] using hiIcc

/--
The sufficiency direction of the prescribed-profile theorem: fitting the
canonical recurrence produces an actual antichain with exactly profile `f`.
-/
theorem profile_sufficiency
    {n lo hi : ℕ} {f m : ℕ → ℕ}
    (hlo : 1 ≤ lo) (hrec : IsProfileRecurrence n lo hi f m) :
    ∃ F : Family (Fin n),
      IsSperner F ∧
        (∀ i, lo ≤ i → i ≤ hi → (level F i).card = f i) ∧
        ∀ s ∈ F, s.card ∈ Finset.Icc lo hi := by
  refine ⟨profileFamily n lo hi m, isSperner_profileFamily hlo hrec, ?_, ?_⟩
  · intro i hloi hihi
    rw [level_profileFamily hlo hrec hloi hihi,
      card_selectedLayer hlo hrec hloi hihi]
  · exact fun s hs => profileFamily_card_mem_Icc hlo hrec hs

end Erdos776.KruskalKatona


/-!
# The prescribed-profile criterion

This file packages the generic necessity and sufficiency arguments into the
exact iff statement used in the manuscripts.  It concerns profiles supported
on a nonempty interval `lo..hi` with `lo ≥ 1`.
-/

namespace Erdos776.KruskalKatona

open Finset
open Erdos776.Antichain

/-- The exact top-down recurrence associated with a profile. -/
def profileDescending (f : ℕ → ℕ) (hi : ℕ) : ℕ → ℕ
  | 0 => 0
  | d + 1 =>
      f (hi - d) +
        canonicalShadow (hi - d + 1) (profileDescending f hi d)

/-- Reindex the descending recurrence by the actual set-size level. -/
def profileChain (f : ℕ → ℕ) (hi i : ℕ) : ℕ :=
  profileDescending f hi (hi + 1 - i)

@[simp] theorem profileChain_top (f : ℕ → ℕ) (hi : ℕ) :
    profileChain f hi (hi + 1) = 0 := by
  simp [profileChain, profileDescending]

theorem profileChain_step (f : ℕ → ℕ) {hi i : ℕ} (hi_le : i ≤ hi) :
    profileChain f hi i =
      f i + canonicalShadow (i + 1) (profileChain f hi (i + 1)) := by
  have hdist : hi + 1 - i = (hi - i) + 1 := by omega
  have hlevel : hi - (hi - i) = i := by omega
  have hnext : hi + 1 - (i + 1) = hi - i := by omega
  rw [profileChain, hdist, profileDescending, hlevel]
  rw [profileChain, hnext]

theorem levelFamily_eq_level {n i : ℕ}
    (F : Finset (Finset (Fin n))) :
    levelFamily F i = Erdos776.Antichain.level F i := by
  rfl

/--
Generic necessity: every antichain carrying at least the proposed profile
forces every state of its canonical recurrence to fit inside the corresponding
level of `Fin n`.
-/
theorem profile_necessity
    {n lo hi : ℕ} {f m : ℕ → ℕ}
    (htop : m (hi + 1) = 0)
    (hstep : ∀ i, lo ≤ i → i ≤ hi →
      m i = f i + canonicalShadow (i + 1) (m (i + 1)))
    {F : Family (Fin n)}
    (hanti : IsSperner F)
    (hprofile : ∀ i, lo ≤ i → i ≤ hi → f i ≤ (level F i).card) :
    IsProfileRecurrence n lo hi f m := by
  have hcumulative :
      ∀ i, lo ≤ i → i ≤ hi + 1 →
        m i ≤ (cumulativeLevel F i).card := by
    intro i hloi hihi
    apply Nat.decreasingInduction'
        (P := fun k => m k ≤ (cumulativeLevel F k).card)
        (m := i) (n := hi + 1) ?_ hihi
    · rw [htop]
      omega
    · intro k hkhi hik ih
      have hlok : lo ≤ k := hloi.trans hik
      have hkhi' : k ≤ hi := by omega
      rw [hstep k hlok hkhi']
      have hmono := canonicalShadow_mono (k + 1) (by omega) ih
      have hcap : (cumulativeLevel F (k + 1)).card ≤
          n.choose (k + 1) := card_cumulativeLevel_le_choose
      have hshadowEq := kkShadow_eq_canonicalShadow (by omega) hcap
      have hlevel : f k ≤ (levelFamily F k).card := by
        rw [levelFamily_eq_level]
        exact hprofile k hlok hkhi'
      have hprofileStep := profile_step_le_cumulativeLevel hanti hlevel
      rw [hshadowEq] at hprofileStep
      exact (Nat.add_le_add_left hmono (f k)).trans hprofileStep
  refine ⟨htop, hstep, ?_⟩
  intro i hloi hihi
  exact (hcumulative i hloi hihi).trans card_cumulativeLevel_le_choose

/-- The canonical recurrence is feasible whenever the requested antichain exists. -/
theorem profileChain_isProfileRecurrence_of_antichain
    {n lo hi : ℕ} {f : ℕ → ℕ}
    {F : Family (Fin n)}
    (hanti : IsSperner F)
    (hprofile : ∀ i, lo ≤ i → i ≤ hi → f i ≤ (level F i).card) :
    IsProfileRecurrence n lo hi f (profileChain f hi) := by
  apply profile_necessity (profileChain_top f hi)
      (fun i _ hi_i => profileChain_step f hi_i) hanti hprofile

/--
The classical prescribed-profile criterion: an exact finite antichain profile
exists iff its top-down canonical recurrence fits in every level.
-/
theorem profile_criterion
    {n lo hi : ℕ} {f : ℕ → ℕ} (hlo : 1 ≤ lo) :
    (∃ F : Family (Fin n),
      IsSperner F ∧
        (∀ i, lo ≤ i → i ≤ hi → (level F i).card = f i) ∧
        ∀ s ∈ F, s.card ∈ Finset.Icc lo hi) ↔
      ∃ m : ℕ → ℕ, IsProfileRecurrence n lo hi f m := by
  constructor
  · rintro ⟨F, hanti, hprofile, hsupport⟩
    refine ⟨profileChain f hi,
      profileChain_isProfileRecurrence_of_antichain hanti ?_⟩
    intro i hloi hihi
    rw [hprofile i hloi hihi]
  · rintro ⟨m, hrec⟩
    exact profile_sufficiency hlo hrec

end Erdos776.KruskalKatona


/-!
# L4: the reverse-envelope argument

This file isolates the order-theoretic core of L4 from the binomial-cascade
calculations.  It proves that any monotone shadow operation satisfying the
displayed reverse steps forces every feasible recurrence below `Ghat`, which
contradicts the independently forced state at level `r - 2`.

The remaining cascade layer must prove `ReverseSteps` and `TopStepIdentities`
for the Kruskal--Katona shadow.  Keeping that interface explicit prevents a
numerical checker from being mistaken for a proof of the symbolic identities.
-/

namespace Erdos776.L4

/-- The bounding sequence `Ĝ` in `docs/L4_PROOF.md`. -/
def Ghat (r i : ℕ) : ℕ :=
  if i = 2 then
    (r + 4).choose 2
  else if i = 3 then
    (r + 3).choose 3 + 3
  else if i = 4 then
    (r + 2).choose 4 + (r + 1).choose 3 + 6
  else if i = 5 then
    (r + 2).choose 5 + r.choose 4 + (r - 1).choose 3 + 10
  else if i = 6 then
    (r + 2).choose 6 + r.choose 5 + (r - 2).choose 4 +
      (r - 3).choose 3 + 21
  else if i = 7 then
    (r + 2).choose 7 + r.choose 6 + (r - 2).choose 5 +
      (r - 4).choose 4 + (r - 5).choose 3 + 120
  else
    (r + 2).choose i + r.choose (i - 1) + (r - 2).choose (i - 2) +
      (r - 4).choose (i - 3) + (r - 5).choose (i - 4) +
      (23 : ℕ).choose (i - 5)

/-- The recurrence forced by feasibility of the L4 profile. -/
def IsL4Chain (shadow : ℕ → ℕ → ℕ) (r : ℕ) (c : ℕ → ℕ) : Prop :=
  c (r + 1) = r ∧
    ∀ i, 2 ≤ i → i ≤ r → c i = r + shadow (i + 1) (c (i + 1))

/-- The reverse-step inequalities called Lemma RS in the manuscript. -/
def ReverseSteps (shadow : ℕ → ℕ → ℕ) (r : ℕ) : Prop :=
  ∀ i, 3 ≤ i → i ≤ r - 2 →
    Ghat r (i - 1) < r + shadow i (Ghat r i + 1)

/-- The closed form for the state forced three levels below the top. -/
def forcedTopValue (r : ℕ) : ℕ :=
  (r + 2).choose 4 + r.choose 3 + (r - 2).choose 2 + (3 * r - 9)

/-- The general formula for `Ĝ` specialized to the comparison level. -/
theorem ghat_at_top (r : ℕ) (hr : 29 ≤ r) :
    Ghat r (r - 2) =
      (r + 2).choose 4 + r.choose 3 + (r - 2).choose 2 +
        (r - 4) + (r - 5) + (23 : ℕ).choose (r - 7) := by
  have h4 : (r + 2).choose (r - 2) = (r + 2).choose 4 := by
    simpa only [show r + 2 - 4 = r - 2 by omega] using
      (Nat.choose_symm (n := r + 2) (k := 4) (by omega))
  have h3 : r.choose (r - 3) = r.choose 3 := by
    simpa only using (Nat.choose_symm (n := r) (k := 3) (by omega))
  have h2 : (r - 2).choose (r - 4) = (r - 2).choose 2 := by
    simpa only [show r - 2 - 2 = r - 4 by omega] using
      (Nat.choose_symm (n := r - 2) (k := 2) (by omega))
  have h1a : (r - 4).choose (r - 5) = r - 4 := by
    have hsym := Nat.choose_symm (n := r - 4) (k := 1) (by omega)
    rw [show r - 4 - 1 = r - 5 by omega] at hsym
    simpa using hsym
  have h1b : (r - 5).choose (r - 6) = r - 5 := by
    have hsym := Nat.choose_symm (n := r - 5) (k := 1) (by omega)
    rw [show r - 5 - 1 = r - 6 by omega] at hsym
    simpa using hsym
  simp only [Ghat, if_neg (show r - 2 ≠ 2 by omega),
    if_neg (show r - 2 ≠ 3 by omega), if_neg (show r - 2 ≠ 4 by omega),
    if_neg (show r - 2 ≠ 5 by omega), if_neg (show r - 2 ≠ 6 by omega),
    if_neg (show r - 2 ≠ 7 by omega)]
  rw [show r - 2 - 1 = r - 3 by omega,
    show r - 2 - 2 = r - 4 by omega,
    show r - 2 - 3 = r - 5 by omega,
    show r - 2 - 4 = r - 6 by omega,
    show r - 2 - 5 = r - 7 by omega,
    h4, h3, h2, h1a, h1b]

/-- The tapering corrector is strictly smaller than the final margin. -/
theorem corrector_lt_r (r : ℕ) (hr : 29 ≤ r) :
    (23 : ℕ).choose (r - 7) < r := by
  rcases lt_or_eq_of_le hr with hr' | rfl
  · by_cases h30 : r = 30
    · subst r
      simp
    · have hr31 : 31 ≤ r := by omega
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      omega
  · simp

/-- The final positive margin, including the exceptional cases 29 and 30. -/
theorem ghat_lt_forcedTopValue (r : ℕ) (hr : 29 ≤ r) :
    Ghat r (r - 2) < forcedTopValue r := by
  rw [ghat_at_top r hr]
  unfold forcedTopValue
  have hc := corrector_lt_r r hr
  omega

/-- Lemma L4-T, stated as the exact value needed by the envelope argument. -/
def ForcedTop (r : ℕ) (c : ℕ → ℕ) : Prop :=
  c (r - 2) = forcedTopValue r

/-- The state one level below the top, in the proof of Lemma L4-T. -/
def topRValue (r : ℕ) : ℕ :=
  (r + 2).choose 2 + (r - 1)

/-- The state two levels below the top, in the proof of Lemma L4-T. -/
def topRm1Value (r : ℕ) : ℕ :=
  (r + 2).choose (r - 1) + r.choose 2 + r

/--
The three concrete cascade evaluations used in Lemma L4-T.  This is a
deliberately narrow interface for the future numerical-cascade module.
-/
def TopStepIdentities (shadow : ℕ → ℕ → ℕ) (r : ℕ) : Prop :=
  shadow (r + 1) r = (r + 2).choose 2 - 1 ∧
  shadow r (topRValue r) = (r + 2).choose (r - 1) + r.choose 2 ∧
  shadow (r - 1) (topRm1Value r) =
    (r + 2).choose (r - 2) + r.choose (r - 3) +
      (r - 2).choose (r - 4) + (r - 4) + (r - 5)

/-- Lemma L4-T follows from its three explicit cascade evaluations. -/
theorem forcedTop_of_topStepIdentities
    (shadow : ℕ → ℕ → ℕ) (r : ℕ) (c : ℕ → ℕ)
    (hr : 15 ≤ r)
    (hchain : IsL4Chain shadow r c)
    (htop : TopStepIdentities shadow r) : ForcedTop r c := by
  have hcr : c r = topRValue r := by
    rw [hchain.2 r (by omega) (by omega), hchain.1, htop.1]
    unfold topRValue
    have hpos : 0 < (r + 2).choose 2 := Nat.choose_pos (by omega)
    omega
  have hcrm1 : c (r - 1) = topRm1Value r := by
    have hrec := hchain.2 (r - 1) (by omega) (by omega)
    rw [show r - 1 + 1 = r by omega, hcr, htop.2.1] at hrec
    unfold topRm1Value
    omega
  have hcrm2 := hchain.2 (r - 2) (by omega) (by omega)
  rw [show r - 2 + 1 = r - 1 by omega, hcrm1, htop.2.2] at hcrm2
  unfold ForcedTop forcedTopValue
  rw [hcrm2]
  have h4 : (r + 2).choose (r - 2) = (r + 2).choose 4 := by
    simpa only [show r + 2 - 4 = r - 2 by omega] using
      (Nat.choose_symm (n := r + 2) (k := 4) (by omega))
  have h3 : r.choose (r - 3) = r.choose 3 := by
    simpa only using (Nat.choose_symm (n := r) (k := 3) (by omega))
  have h2 : (r - 2).choose (r - 4) = (r - 2).choose 2 := by
    simpa only [show r - 2 - 2 = r - 4 by omega] using
      (Nat.choose_symm (n := r - 2) (k := 2) (by omega))
  rw [h4, h3, h2]
  omega

/--
Lemma IND from the paper.  Notice that this proof uses only monotonicity,
the recurrence, the level-2 capacity, and Lemma RS.
-/
theorem chain_le_ghat
    (shadow : ℕ → ℕ → ℕ) (r : ℕ) (c : ℕ → ℕ)
    (hmono : ∀ k, Monotone (shadow k))
    (hchain : IsL4Chain shadow r c)
    (hcapacity : c 2 ≤ (r + 4).choose 2)
    (hreverse : ReverseSteps shadow r) :
    ∀ i, 2 ≤ i → i ≤ r - 2 → c i ≤ Ghat r i := by
  intro i hi hir
  induction i, hi using Nat.le_induction with
  | base =>
      simpa [Ghat] using hcapacity
  | succ i hi ih =>
      have hir' : i ≤ r := by omega
      have hrec := hchain.2 i hi hir'
      have hrs : Ghat r i < r + shadow (i + 1) (Ghat r (i + 1) + 1) := by
        simpa using hreverse (i + 1) (by omega) (by omega)
      by_contra hnot
      have hlarge : Ghat r (i + 1) + 1 ≤ c (i + 1) := by omega
      have hshadow := hmono (i + 1) hlarge
      have : Ghat r i < c i := by
        rw [hrec]
        exact lt_of_lt_of_le hrs (Nat.add_le_add_left hshadow r)
      exact (Nat.not_lt_of_ge (ih (by omega))) this

/--
The final, short logical core of L4: the reverse envelope and the forced top
state are incompatible with level-2 capacity.
-/
theorem not_l4_chain_of_forcedTop_gt
    (shadow : ℕ → ℕ → ℕ) (r : ℕ)
    (hr : 4 ≤ r)
    (hmono : ∀ k, Monotone (shadow k))
    (hreverse : ReverseSteps shadow r)
    (htop : Ghat r (r - 2) < forcedTopValue r) :
    ¬ ∃ c : ℕ → ℕ,
      IsL4Chain shadow r c ∧
      c 2 ≤ (r + 4).choose 2 ∧
      ForcedTop r c := by
  rintro ⟨c, hchain, hcapacity, hforced⟩
  have hbound := chain_le_ghat shadow r c hmono hchain hcapacity hreverse
    (r - 2) (by omega) (by omega)
  unfold ForcedTop at hforced
  rw [hforced] at hbound
  exact (Nat.not_lt_of_ge hbound) htop

/-- L4's contradiction when Lemma L4-T is already available. -/
theorem not_l4_chain_with_forcedTop
    (shadow : ℕ → ℕ → ℕ) (r : ℕ)
    (hr : 29 ≤ r)
    (hmono : ∀ k, Monotone (shadow k))
    (hreverse : ReverseSteps shadow r) :
    ¬ ∃ c : ℕ → ℕ,
      IsL4Chain shadow r c ∧
      c 2 ≤ (r + 4).choose 2 ∧
      ForcedTop r c :=
  not_l4_chain_of_forcedTop_gt shadow r (by omega) hmono hreverse
    (ghat_lt_forcedTopValue r hr)

/--
L4's contradiction reduced exactly to monotonicity and the displayed cascade
evaluations (Lemma RS and the three top steps of Lemma L4-T).
-/
theorem not_l4_chain
    (shadow : ℕ → ℕ → ℕ) (r : ℕ)
    (hr : 29 ≤ r)
    (hmono : ∀ k, Monotone (shadow k))
    (hreverse : ReverseSteps shadow r)
    (htop : TopStepIdentities shadow r) :
    ¬ ∃ c : ℕ → ℕ,
      IsL4Chain shadow r c ∧
      c 2 ≤ (r + 4).choose 2 := by
  rintro ⟨c, hchain, hcapacity⟩
  exact not_l4_chain_with_forcedTop shadow r hr hmono hreverse
    ⟨c, hchain, hcapacity, forcedTop_of_topStepIdentities shadow r c (by omega) hchain htop⟩

end Erdos776.L4


/-!
# Cascade evaluations used by L4

This file instantiates the generic numerical Kruskal--Katona bridge with the
specific cascades in `docs/L4_PROOF.md`.
-/

namespace Erdos776.L4

open Erdos776.KruskalKatona

/-- The concrete numerical shadow on the `r+4` point ground set. -/
noncomputable def l4Shadow (r : ℕ) : ℕ → ℕ → ℕ :=
  kkShadow (r + 4)

theorem l4Shadow_mono (r : ℕ) : ∀ k, Monotone (l4Shadow r k) := by
  intro k
  exact kkShadow_mono (r + 4) k

private theorem top_step_one (r : ℕ) :
    l4Shadow r (r + 1) r = (r + 2).choose 2 - 1 := by
  let digits := diagonalDigits (r + 1) r
  have hcanon : IsCanonical (r + 1) digits :=
    isCanonical_diagonalDigits (by omega)
  have hbound : BoundedFamily (r + 4) (cascadeFamily (r + 1) digits) := by
    intro s hs
    apply mem_cascadeFamily_lt_of_digits_lt _ hs
    intro d hd
    exact (mem_diagonalDigits_le hd).trans_lt (by omega)
  have heval := kkShadow_eq_cascadeShadowValue hcanon hbound
  have hvalue : cascadeValue (r + 1) digits = r :=
    cascadeValue_diagonalDigits (by omega)
  have hshadow : cascadeShadowValue (r + 1) digits = (r + 2).choose 2 - 1 := by
    simpa [digits] using cascadeShadowValue_diagonalDigits_drop_one (r + 1)
  change kkShadow (r + 4) (r + 1) r = (r + 2).choose 2 - 1
  rw [hvalue, hshadow] at heval
  exact heval

private theorem top_step_two (r : ℕ) (hr : 2 ≤ r) :
    l4Shadow r r (topRValue r) =
      (r + 2).choose (r - 1) + r.choose 2 := by
  let digits := (r + 2) :: diagonalDigits (r - 1) (r - 1)
  have htail : IsCanonical (r - 1) (diagonalDigits (r - 1) (r - 1)) :=
    isCanonical_diagonalDigits le_rfl
  have hcanon : IsCanonical r digits := by
    rw [show r = (r - 1) + 1 by omega]
    rw [isCanonical_succ_cons]
    refine ⟨by omega, ?_, htail⟩
    intro d hd
    exact lt_of_le_of_lt (mem_diagonalDigits_le hd) (by omega)
  have hsym : (r + 2).choose r = (r + 2).choose 2 := by
    simpa only [show r + 2 - 2 = r by omega] using
      (Nat.choose_symm (n := r + 2) (k := 2) (by omega))
  have hvalue : cascadeValue r digits = topRValue r := by
    simp only [digits, cascadeValue_cons]
    rw [cascadeValue_diagonalDigits le_rfl, hsym]
    rfl
  have hshadow : cascadeShadowValue r digits =
      (r + 2).choose (r - 1) + r.choose 2 := by
    simp only [digits, cascadeShadowValue_cons]
    rw [show cascadeValue (r - 2) (diagonalDigits (r - 1) (r - 1)) =
        cascadeShadowValue (r - 1) (diagonalDigits (r - 1) (r - 1)) by rfl,
      cascadeShadowValue_diagonalDigits_full]
    congr 2
    omega
  have hcanon' : IsCanonical r ((r + 2) :: diagonalDigits (r - 1) (r - 1)) := by
    simpa [digits] using hcanon
  have heval := kkShadow_eq_cascadeShadowValue_of_head hcanon' (by omega : r + 2 < r + 4)
  change kkShadow (r + 4) r (topRValue r) =
    (r + 2).choose (r - 1) + r.choose 2
  rw [← hvalue]
  change kkShadow (r + 4) r (cascadeValue r ((r + 2) :: diagonalDigits (r - 1) (r - 1))) = _
  rw [heval]
  exact hshadow

private theorem top_five_canonical (r : ℕ) (hr : 15 ≤ r) :
    IsCanonical (r - 1) [r + 2, r, r - 2, r - 4, r - 5] := by
  rw [show r - 1 = (r - 2) + 1 by omega]
  rw [isCanonical_succ_cons]
  refine ⟨by omega, ?_, ?_⟩
  · simp
    omega
  rw [show r - 2 = (r - 3) + 1 by omega]
  rw [isCanonical_succ_cons]
  refine ⟨by omega, ?_, ?_⟩
  · simp
    omega
  rw [show r - 3 = (r - 4) + 1 by omega]
  rw [isCanonical_succ_cons]
  refine ⟨by omega, ?_, ?_⟩
  · simp
    omega
  rw [show r - 4 = (r - 5) + 1 by omega]
  rw [isCanonical_succ_cons]
  refine ⟨by omega, ?_, ?_⟩
  · simp
  rw [show r - 5 = (r - 6) + 1 by omega]
  rw [isCanonical_succ_cons]
  exact ⟨by omega, by simp, by simp⟩

private theorem top_step_three (r : ℕ) (hr : 15 ≤ r) :
    l4Shadow r (r - 1) (topRm1Value r) =
      (r + 2).choose (r - 2) + r.choose (r - 3) +
        (r - 2).choose (r - 4) + (r - 4) + (r - 5) := by
  let digits := [r + 2, r, r - 2, r - 4, r - 5]
  have hcanon : IsCanonical (r - 1) digits := top_five_canonical r hr
  have hr2 : r.choose (r - 2) = r.choose 2 := by
    simpa only using (Nat.choose_symm (n := r) (k := 2) (by omega))
  have hr3 : (r - 2).choose (r - 3) = r - 2 := by
    have hsym := Nat.choose_symm (n := r - 2) (k := 1) (by omega)
    rw [show r - 2 - 1 = r - 3 by omega] at hsym
    simpa using hsym
  have hr4 : (r - 4).choose (r - 5) = r - 4 := by
    have hsym := Nat.choose_symm (n := r - 4) (k := 1) (by omega)
    rw [show r - 4 - 1 = r - 5 by omega] at hsym
    simpa using hsym
  have hr5 : (r - 5).choose (r - 6) = r - 5 := by
    have hsym := Nat.choose_symm (n := r - 5) (k := 1) (by omega)
    rw [show r - 5 - 1 = r - 6 by omega] at hsym
    simpa using hsym
  have hvalue : cascadeValue (r - 1) digits = topRm1Value r := by
    simp only [digits, cascadeValue_cons, cascadeValue_nil]
    rw [show r - 1 - 1 = r - 2 by omega,
      show r - 2 - 1 = r - 3 by omega,
      show r - 3 - 1 = r - 4 by omega,
      show r - 4 - 1 = r - 5 by omega,
      hr2, hr3, Nat.choose_self, Nat.choose_self]
    unfold topRm1Value
    omega
  have hshadow : cascadeShadowValue (r - 1) digits =
      (r + 2).choose (r - 2) + r.choose (r - 3) +
        (r - 2).choose (r - 4) + (r - 4) + (r - 5) := by
    simp only [digits, cascadeShadowValue, cascadeValue_cons, cascadeValue_nil]
    rw [show r - 1 - 1 = r - 2 by omega,
      show r - 2 - 1 = r - 3 by omega,
      show r - 3 - 1 = r - 4 by omega,
      show r - 4 - 1 = r - 5 by omega,
      show r - 5 - 1 = r - 6 by omega,
      hr4, hr5]
    omega
  have hcanon' : IsCanonical (r - 1) [r + 2, r, r - 2, r - 4, r - 5] := by
    simpa [digits] using hcanon
  have heval := kkShadow_eq_cascadeShadowValue_of_head hcanon' (by omega : r + 2 < r + 4)
  change kkShadow (r + 4) (r - 1) (topRm1Value r) = _
  rw [← hvalue]
  change kkShadow (r + 4) (r - 1)
      (cascadeValue (r - 1) [r + 2, r, r - 2, r - 4, r - 5]) = _
  rw [heval]
  exact hshadow

/-- The three exact top cascade evaluations in Lemma L4-T. -/
theorem l4_topStepIdentities (r : ℕ) (hr : 29 ≤ r) :
    TopStepIdentities (l4Shadow r) r := by
  exact ⟨top_step_one r, top_step_two r (by omega), top_step_three r (by omega)⟩

end Erdos776.L4


/-!
# The reverse-step cascade calculations in L4
-/

namespace Erdos776.L4

open Erdos776.KruskalKatona

private theorem l4Shadow_eval
    {r k a m q : ℕ} {digits : List ℕ}
    (hcanon : IsCanonical k (a :: digits))
    (ha : a < r + 4)
    (hvalue : cascadeValue k (a :: digits) = m)
    (hshadow : cascadeShadowValue k (a :: digits) = q) :
    l4Shadow r k m = q := by
  have heval := kkShadow_eq_cascadeShadowValue_of_head hcanon ha
  rw [hvalue, hshadow] at heval
  exact heval

private theorem reverse_shadow_3 (r : ℕ) (hr : 29 ≤ r) :
    l4Shadow r 3 (Ghat r 3 + 1) = (r + 3).choose 2 + 3 + 1 := by
  apply l4Shadow_eval (a := r + 3) (digits := [3, 1])
  · simp [IsCanonical]
    omega
  · omega
  · simp [Ghat, cascadeValue]
  · simp [cascadeShadowValue, cascadeValue]

private theorem reverse_step_3 (r : ℕ) (hr : 29 ≤ r) :
    Ghat r 2 < r + l4Shadow r 3 (Ghat r 3 + 1) := by
  rw [reverse_shadow_3 r hr]
  have hp : (r + 4).choose 2 = r + 3 + (r + 3).choose 2 := by
    simpa [Nat.choose_one_right] using Nat.choose_succ_succ (r + 3) 1
  simp only [Ghat, if_pos]
  omega

private theorem reverse_shadow_4 (r : ℕ) (hr : 29 ≤ r) :
    l4Shadow r 4 (Ghat r 4 + 1) =
      (r + 2).choose 3 + (r + 1).choose 2 + 4 + 1 := by
  apply l4Shadow_eval (a := r + 2) (digits := [r + 1, 4, 1])
  · simp [IsCanonical]
    omega
  · omega
  · simp [Ghat, cascadeValue]
    norm_num [Nat.choose]
    omega
  · simp [cascadeShadowValue, cascadeValue]
    norm_num [Nat.choose]
    omega

private theorem reverse_step_4 (r : ℕ) (hr : 29 ≤ r) :
    Ghat r 3 < r + l4Shadow r 4 (Ghat r 4 + 1) := by
  rw [reverse_shadow_4 r hr]
  have hp3 : (r + 3).choose 3 = (r + 2).choose 2 + (r + 2).choose 3 := by
    simpa using Nat.choose_succ_succ (r + 2) 2
  have hp2 : (r + 2).choose 2 = r + 1 + (r + 1).choose 2 := by
    simpa [Nat.choose_one_right] using Nat.choose_succ_succ (r + 1) 1
  simp [Ghat]
  omega

private theorem reverse_shadow_5 (r : ℕ) (hr : 29 ≤ r) :
    l4Shadow r 5 (Ghat r 5 + 1) =
      (r + 2).choose 4 + r.choose 3 + (r - 1).choose 2 + 5 + 1 := by
  apply l4Shadow_eval (a := r + 2) (digits := [r, r - 1, 5, 1])
  · simp [IsCanonical]
    omega
  · omega
  · simp [Ghat, cascadeValue]
    norm_num [Nat.choose]
    omega
  · simp [cascadeShadowValue, cascadeValue]
    norm_num [Nat.choose]
    omega

private theorem reverse_step_5 (r : ℕ) (hr : 29 ≤ r) :
    Ghat r 4 < r + l4Shadow r 5 (Ghat r 5 + 1) := by
  rw [reverse_shadow_5 r hr]
  have hp3 : (r + 1).choose 3 = r.choose 2 + r.choose 3 := by
    simpa using Nat.choose_succ_succ r 2
  have hp2 : r.choose 2 = r - 1 + (r - 1).choose 2 := by
    simpa only [Nat.succ_eq_add_one, show r - 1 + 1 = r by omega,
      Nat.choose_one_right] using Nat.choose_succ_succ (r - 1) 1
  simp [Ghat]
  omega

private theorem reverse_shadow_6 (r : ℕ) (hr : 29 ≤ r) :
    l4Shadow r 6 (Ghat r 6 + 1) =
      (r + 2).choose 5 + r.choose 4 + (r - 2).choose 3 +
        (r - 3).choose 2 + 7 + 1 := by
  apply l4Shadow_eval (a := r + 2) (digits := [r, r - 2, r - 3, 7, 1])
  · simp [IsCanonical]
    omega
  · omega
  · simp [Ghat, cascadeValue]
    norm_num [Nat.choose]
    omega
  · simp [cascadeShadowValue, cascadeValue]
    norm_num [Nat.choose]
    omega

private theorem reverse_step_6 (r : ℕ) (hr : 29 ≤ r) :
    Ghat r 5 < r + l4Shadow r 6 (Ghat r 6 + 1) := by
  rw [reverse_shadow_6 r hr]
  have hp3 : (r - 1).choose 3 = (r - 2).choose 2 + (r - 2).choose 3 := by
    simpa only [Nat.succ_eq_add_one, show r - 2 + 1 = r - 1 by omega] using
      Nat.choose_succ_succ (r - 2) 2
  have hp2 : (r - 2).choose 2 = r - 3 + (r - 3).choose 2 := by
    simpa [Nat.choose_one_right, show r - 3 + 1 = r - 2 by omega] using
      Nat.choose_succ_succ (r - 3) 1
  simp [Ghat]
  omega

private theorem reverse_shadow_7 (r : ℕ) (hr : 29 ≤ r) :
    l4Shadow r 7 (Ghat r 7 + 1) =
      (r + 2).choose 6 + r.choose 5 + (r - 2).choose 4 +
        (r - 4).choose 3 + (r - 5).choose 2 + 16 + 1 := by
  apply l4Shadow_eval (a := r + 2)
      (digits := [r, r - 2, r - 4, r - 5, 16, 1])
  · simp [IsCanonical]
    omega
  · omega
  · simp [Ghat, cascadeValue]
    norm_num [Nat.choose]
    omega
  · simp [cascadeShadowValue, cascadeValue]
    norm_num [Nat.choose]
    omega

private theorem reverse_step_7 (r : ℕ) (hr : 29 ≤ r) :
    Ghat r 6 < r + l4Shadow r 7 (Ghat r 7 + 1) := by
  rw [reverse_shadow_7 r hr]
  have hp3 : (r - 3).choose 3 = (r - 4).choose 2 + (r - 4).choose 3 := by
    simpa only [Nat.succ_eq_add_one, show r - 4 + 1 = r - 3 by omega] using
      Nat.choose_succ_succ (r - 4) 2
  have hp2 : (r - 4).choose 2 = r - 5 + (r - 5).choose 2 := by
    simpa [Nat.choose_one_right, show r - 5 + 1 = r - 4 by omega] using
      Nat.choose_succ_succ (r - 5) 1
  simp [Ghat]
  omega

private theorem reverse_shadow_8 (r : ℕ) (hr : 29 ≤ r) :
    l4Shadow r 8 (Ghat r 8 + 1) =
      (r + 2).choose 7 + r.choose 6 + (r - 2).choose 5 +
        (r - 4).choose 4 + (r - 5).choose 3 + (23 : ℕ).choose 2 + 2 := by
  apply l4Shadow_eval (a := r + 2)
      (digits := [r, r - 2, r - 4, r - 5, 23, 2])
  · simp [IsCanonical]
    omega
  · omega
  · simp [Ghat, cascadeValue]
    norm_num [Nat.choose]
    omega
  · simp [cascadeShadowValue, cascadeValue]
    norm_num [Nat.choose]
    omega

private theorem reverse_step_8 (r : ℕ) (hr : 29 ≤ r) :
    Ghat r 7 < r + l4Shadow r 8 (Ghat r 8 + 1) := by
  rw [reverse_shadow_8 r hr]
  simp [Ghat]
  norm_num [Nat.choose]
  omega

private theorem canonical_seven
    {k a b c d e f g : ℕ}
    (hk : 7 ≤ k)
    (ha : k ≤ a) (hb : k - 1 ≤ b) (hc : k - 2 ≤ c)
    (hd : k - 3 ≤ d) (he : k - 4 ≤ e) (hf : k - 5 ≤ f)
    (hg : k - 6 ≤ g)
    (hab : b < a) (hbc : c < b) (hcd : d < c)
    (hde : e < d) (hef : f < e) (hfg : g < f) :
    IsCanonical k [a, b, c, d, e, f, g] := by
  apply (isCanonical_cons_of_pos (by omega)).2
  refine ⟨ha, ?_, ?_⟩
  · simp
    omega
  apply (isCanonical_cons_of_pos (by omega : 0 < k - 1)).2
  refine ⟨hb, ?_, ?_⟩
  · simp
    omega
  apply (isCanonical_cons_of_pos (by omega : 0 < k - 2)).2
  refine ⟨hc, ?_, ?_⟩
  · simp
    omega
  apply (isCanonical_cons_of_pos (by omega : 0 < k - 3)).2
  refine ⟨hd, ?_, ?_⟩
  · simp
    omega
  apply (isCanonical_cons_of_pos (by omega : 0 < k - 4)).2
  refine ⟨he, ?_, ?_⟩
  · simp
    omega
  apply (isCanonical_cons_of_pos (by omega : 0 < k - 5)).2
  refine ⟨hf, by simpa, ?_⟩
  apply (isCanonical_cons_of_pos (by omega : 0 < k - 6)).2
  exact ⟨hg, by simp, by simp⟩

private theorem reverse_shadow_9_28
    (r i : ℕ) (hr : 29 ≤ r) (hi9 : 9 ≤ i) (hi28 : i ≤ 28) :
    l4Shadow r i (Ghat r i + 1) =
      (r + 2).choose (i - 1) + r.choose (i - 2) +
        (r - 2).choose (i - 3) + (r - 4).choose (i - 4) +
        (r - 5).choose (i - 5) + (23 : ℕ).choose (i - 6) + (i - 6) := by
  have hcanon :
      IsCanonical i [r + 2, r, r - 2, r - 4, r - 5, 23, i - 6] := by
    apply canonical_seven (by omega) <;> omega
  have hlast : (i - 6).choose (i - 7) = i - 6 := by
    simpa only [show i - 6 - 1 = i - 7 by omega, Nat.choose_one_right] using
      (Nat.choose_symm (n := i - 6) (k := 1) (by omega))
  apply l4Shadow_eval (a := r + 2)
      (digits := [r, r - 2, r - 4, r - 5, 23, i - 6])
  · exact hcanon
  · omega
  · simp only [cascadeValue_cons, cascadeValue_nil]
    simp only [Ghat, if_neg (show i ≠ 2 by omega), if_neg (show i ≠ 3 by omega),
      if_neg (show i ≠ 4 by omega), if_neg (show i ≠ 5 by omega),
      if_neg (show i ≠ 6 by omega), if_neg (show i ≠ 7 by omega)]
    rw [show i - 1 - 1 = i - 2 by omega,
      show i - 2 - 1 = i - 3 by omega,
      show i - 3 - 1 = i - 4 by omega,
      show i - 4 - 1 = i - 5 by omega,
      show i - 5 - 1 = i - 6 by omega,
      Nat.choose_self]
    omega
  · simp only [cascadeShadowValue, cascadeValue_cons, cascadeValue_nil]
    rw [show i - 1 - 1 = i - 2 by omega,
      show i - 2 - 1 = i - 3 by omega,
      show i - 3 - 1 = i - 4 by omega,
      show i - 4 - 1 = i - 5 by omega,
      show i - 5 - 1 = i - 6 by omega,
      show i - 6 - 1 = i - 7 by omega, hlast]
    omega

private theorem reverse_step_9_28
    (r i : ℕ) (hr : 29 ≤ r) (hi9 : 9 ≤ i) (hi28 : i ≤ 28) :
    Ghat r (i - 1) < r + l4Shadow r i (Ghat r i + 1) := by
  rw [reverse_shadow_9_28 r i hr hi9 hi28]
  simp only [Ghat, if_neg (show i - 1 ≠ 2 by omega),
    if_neg (show i - 1 ≠ 3 by omega), if_neg (show i - 1 ≠ 4 by omega),
    if_neg (show i - 1 ≠ 5 by omega), if_neg (show i - 1 ≠ 6 by omega),
    if_neg (show i - 1 ≠ 7 by omega)]
  rw [show i - 1 - 1 = i - 2 by omega,
    show i - 1 - 2 = i - 3 by omega,
    show i - 1 - 3 = i - 4 by omega,
    show i - 1 - 4 = i - 5 by omega,
    show i - 1 - 5 = i - 6 by omega]
  omega

private theorem canonical_six
    {k a b c d e f : ℕ}
    (hk : 6 ≤ k)
    (ha : k ≤ a) (hb : k - 1 ≤ b) (hc : k - 2 ≤ c)
    (hd : k - 3 ≤ d) (he : k - 4 ≤ e) (hf : k - 5 ≤ f)
    (hab : b < a) (hbc : c < b) (hcd : d < c)
    (hde : e < d) (hef : f < e) :
    IsCanonical k [a, b, c, d, e, f] := by
  apply (isCanonical_cons_of_pos (by omega)).2
  refine ⟨ha, ?_, ?_⟩
  · simp
    omega
  apply (isCanonical_cons_of_pos (by omega : 0 < k - 1)).2
  refine ⟨hb, ?_, ?_⟩
  · simp
    omega
  apply (isCanonical_cons_of_pos (by omega : 0 < k - 2)).2
  refine ⟨hc, ?_, ?_⟩
  · simp
    omega
  apply (isCanonical_cons_of_pos (by omega : 0 < k - 3)).2
  refine ⟨hd, ?_, ?_⟩
  · simp
    omega
  apply (isCanonical_cons_of_pos (by omega : 0 < k - 4)).2
  refine ⟨he, by simpa, ?_⟩
  apply (isCanonical_cons_of_pos (by omega : 0 < k - 5)).2
  exact ⟨hf, by simp, by simp⟩

private theorem reverse_shadow_29 (r : ℕ) (hr : 31 ≤ r) :
    l4Shadow r 29 (Ghat r 29 + 1) =
      (r + 2).choose 28 + r.choose 27 + (r - 2).choose 26 +
        (r - 4).choose 25 + (r - 5).choose 24 + 24 := by
  have hcanon : IsCanonical 29 [r + 2, r, r - 2, r - 4, r - 5, 24] := by
    apply canonical_six <;> omega
  have hlast : (24 : ℕ).choose 23 = 24 := by
    norm_num [Nat.choose]
  apply l4Shadow_eval (a := r + 2)
      (digits := [r, r - 2, r - 4, r - 5, 24])
  · exact hcanon
  · omega
  · simp only [cascadeValue_cons, cascadeValue_nil]
    simp only [Ghat, if_neg (by decide : 29 ≠ 2), if_neg (by decide : 29 ≠ 3),
      if_neg (by decide : 29 ≠ 4), if_neg (by decide : 29 ≠ 5),
      if_neg (by decide : 29 ≠ 6), if_neg (by decide : 29 ≠ 7)]
    norm_num [Nat.choose]
    omega
  · simp only [cascadeShadowValue, cascadeValue_cons, cascadeValue_nil]
    norm_num [Nat.choose]
    omega

private theorem reverse_step_29 (r : ℕ) (hr : 31 ≤ r) :
    Ghat r 28 < r + l4Shadow r 29 (Ghat r 29 + 1) := by
  rw [reverse_shadow_29 r hr]
  norm_num [Ghat, Nat.choose]
  omega

private theorem reverse_shadow_ge_30
    (r i : ℕ) (hi : 30 ≤ i) (hir : i ≤ r - 2) :
    l4Shadow r i (Ghat r i + 1) =
      (r + 2).choose (i - 1) + r.choose (i - 2) +
        (r - 2).choose (i - 3) + (r - 4).choose (i - 4) +
        (r - 5).choose (i - 5) + (i - 5) := by
  have hcanon :
      IsCanonical i [r + 2, r, r - 2, r - 4, r - 5, i - 5] := by
    apply canonical_six <;> omega
  have hlast : (i - 5).choose (i - 6) = i - 5 := by
    simpa only [show i - 5 - 1 = i - 6 by omega, Nat.choose_one_right] using
      (Nat.choose_symm (n := i - 5) (k := 1) (by omega))
  have hzero : (23 : ℕ).choose (i - 5) = 0 :=
    Nat.choose_eq_zero_of_lt (by omega)
  apply l4Shadow_eval (a := r + 2)
      (digits := [r, r - 2, r - 4, r - 5, i - 5])
  · exact hcanon
  · omega
  · simp only [cascadeValue_cons, cascadeValue_nil]
    simp only [Ghat, if_neg (show i ≠ 2 by omega), if_neg (show i ≠ 3 by omega),
      if_neg (show i ≠ 4 by omega), if_neg (show i ≠ 5 by omega),
      if_neg (show i ≠ 6 by omega), if_neg (show i ≠ 7 by omega)]
    rw [show i - 1 - 1 = i - 2 by omega,
      show i - 2 - 1 = i - 3 by omega,
      show i - 3 - 1 = i - 4 by omega,
      show i - 4 - 1 = i - 5 by omega,
      Nat.choose_self, hzero]
    omega
  · simp only [cascadeShadowValue, cascadeValue_cons, cascadeValue_nil]
    rw [show i - 1 - 1 = i - 2 by omega,
      show i - 2 - 1 = i - 3 by omega,
      show i - 3 - 1 = i - 4 by omega,
      show i - 4 - 1 = i - 5 by omega,
      show i - 5 - 1 = i - 6 by omega, hlast]
    omega

private theorem reverse_step_ge_30
    (r i : ℕ) (hi : 30 ≤ i) (hir : i ≤ r - 2) :
    Ghat r (i - 1) < r + l4Shadow r i (Ghat r i + 1) := by
  rw [reverse_shadow_ge_30 r i hi hir]
  have hzero : (23 : ℕ).choose (i - 6) = 0 :=
    Nat.choose_eq_zero_of_lt (by omega)
  simp only [Ghat, if_neg (show i - 1 ≠ 2 by omega),
    if_neg (show i - 1 ≠ 3 by omega), if_neg (show i - 1 ≠ 4 by omega),
    if_neg (show i - 1 ≠ 5 by omega), if_neg (show i - 1 ≠ 6 by omega),
    if_neg (show i - 1 ≠ 7 by omega)]
  rw [show i - 1 - 1 = i - 2 by omega,
    show i - 1 - 2 = i - 3 by omega,
    show i - 1 - 3 = i - 4 by omega,
    show i - 1 - 4 = i - 5 by omega,
    show i - 1 - 5 = i - 6 by omega, hzero]
  omega

/-- Every reverse-step inequality in Lemma RS for the concrete shadow. -/
theorem l4_reverseSteps (r : ℕ) (hr : 29 ≤ r) :
    ReverseSteps (l4Shadow r) r := by
  intro i hi hir
  by_cases hi8 : i ≤ 8
  · have hcases : i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by
      omega
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact reverse_step_3 r hr
    · exact reverse_step_4 r hr
    · exact reverse_step_5 r hr
    · exact reverse_step_6 r hr
    · exact reverse_step_7 r hr
    · exact reverse_step_8 r hr
  · have hi9 : 9 ≤ i := by omega
    by_cases hi28 : i ≤ 28
    · exact reverse_step_9_28 r i hr hi9 hi28
    · by_cases hi29 : i = 29
      · subst i
        exact reverse_step_29 r (by omega)
      · exact reverse_step_ge_30 r i (by omega) hir

/--
The fully concrete recurrence form of L4.  All monotonicity, reverse-step and
top-step premises of `not_l4_chain` have now been discharged.
-/
theorem l4_no_recurrence (r : ℕ) (hr : 29 ≤ r) :
    ¬ ∃ c : ℕ → ℕ,
      IsL4Chain (l4Shadow r) r c ∧
      c 2 ≤ (r + 4).choose 2 :=
  not_l4_chain (l4Shadow r) r hr (l4Shadow_mono r)
    (l4_reverseSteps r hr) (l4_topStepIdentities r hr)

end Erdos776.L4


/-!
# The semantic L4 theorem

This file turns the numerical recurrence contradiction into a theorem about
actual antichains.  `HasL4MultiplicityProfile r F` says that `F` is an
antichain with at least `r` members on every level `2, ..., r+1`.
-/

namespace Erdos776.L4

open Finset
open Erdos776.KruskalKatona

/-- An antichain carrying the level multiplicities ruled out by L4. -/
def HasL4MultiplicityProfile {n : ℕ} (r : ℕ)
    (F : Finset (Finset (Fin n))) : Prop :=
  IsAntichain (· ⊆ ·) (F : Set (Finset (Fin n))) ∧
    ∀ i, 2 ≤ i → i ≤ r + 1 → r ≤ (levelFamily F i).card

/-- Build the exact top-down numerical recurrence, indexed by distance from the top. -/
def l4DescendingChain (shadow : ℕ → ℕ → ℕ) (r : ℕ) : ℕ → ℕ
  | 0 => r
  | d + 1 => r + shadow (r + 1 - d) (l4DescendingChain shadow r d)

/-- The recurrence indexed by its set-size level. -/
def l4ProfileChain (shadow : ℕ → ℕ → ℕ) (r i : ℕ) : ℕ :=
  l4DescendingChain shadow r (r + 1 - i)

theorem isL4Chain_l4ProfileChain (shadow : ℕ → ℕ → ℕ) (r : ℕ) :
    IsL4Chain shadow r (l4ProfileChain shadow r) := by
  constructor
  · simp [l4ProfileChain, l4DescendingChain]
  · intro i hi hir
    have hdist : r + 1 - i = (r - i) + 1 := by omega
    have hlevel : r + 1 - (r - i) = i + 1 := by omega
    have hnext : r + 1 - (i + 1) = r - i := by omega
    rw [l4ProfileChain, hdist, l4DescendingChain, hlevel]
    rw [l4ProfileChain, hnext]

/--
The necessary half of the profile criterion, specialized to the constant L4
profile but valid on an arbitrary finite ground set.
-/
theorem l4_profile_forces_recurrence
    {n r : ℕ} {F : Finset (Finset (Fin n))}
    (hr : 2 ≤ r) (hF : HasL4MultiplicityProfile r F) :
    ∃ c : ℕ → ℕ,
      IsL4Chain (kkShadow n) r c ∧ c 2 ≤ n.choose 2 := by
  let c : ℕ → ℕ := l4ProfileChain (kkShadow n) r
  have hchain : IsL4Chain (kkShadow n) r c := by
    exact isL4Chain_l4ProfileChain (kkShadow n) r
  have hcumulative :
      ∀ i, 2 ≤ i → i ≤ r + 1 →
        c i ≤ (cumulativeLevel F i).card := by
    intro i hi hir
    apply Nat.decreasingInduction'
        (P := fun k => c k ≤ (cumulativeLevel F k).card)
        (m := i) (n := r + 1) ?_ hir
    · calc
        c (r + 1) = r := hchain.1
        _ ≤ (levelFamily F (r + 1)).card := hF.2 (r + 1) (by omega) (by omega)
        _ ≤ (cumulativeLevel F (r + 1)).card :=
          card_le_card levelFamily_subset_cumulativeLevel
    · intro k hkr hik ih
      have hk2 : 2 ≤ k := hi.trans hik
      have hkle : k ≤ r := by omega
      rw [hchain.2 k hk2 hkle]
      calc
        r + kkShadow n (k + 1) (c (k + 1)) ≤
            r + kkShadow n (k + 1) (cumulativeLevel F (k + 1)).card :=
          Nat.add_le_add_left (kkShadow_mono n (k + 1) ih) r
        _ ≤ (cumulativeLevel F k).card :=
          profile_step_le_cumulativeLevel hF.1 (hF.2 k hk2 (by omega))
  refine ⟨c, hchain, ?_⟩
  exact (hcumulative 2 le_rfl (by omega)).trans card_cumulativeLevel_le_choose

/--
**Theorem L4.** On `r+4` points there is no antichain containing at least
`r` sets of every size from `2` through `r+1`, for any `r ≥ 29`.
-/
theorem l4_multiplicity_profile_infeasible (r : ℕ) (hr : 29 ≤ r) :
    ¬ ∃ F : Finset (Finset (Fin (r + 4))),
      HasL4MultiplicityProfile r F := by
  rintro ⟨F, hF⟩
  obtain ⟨c, hchain, hcapacity⟩ :=
    l4_profile_forces_recurrence (F := F) (by omega) hF
  apply l4_no_recurrence r hr
  exact ⟨c, by simpa [l4Shadow] using hchain, hcapacity⟩

end Erdos776.L4


/-!
# The symbolic diagonal-shell obstruction

This file formalizes the non-computational transfer argument from Section 16
of `UNIFORM_THEOREM.md`.  It first extracts a ground-independent consequence
of L4 and then transports the upper part of the long constant-profile
recurrence through a diagonal binomial shell.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona
open Erdos776.L4

/-- The ground-independent version of the canonical L4 recurrence. -/
def canonicalL4Chain (r : ℕ) : ℕ → ℕ :=
  l4ProfileChain canonicalShadow r

/-- The finite L4 recurrence is pointwise bounded by the canonical recurrence. -/
theorem l4ProfileChain_le_canonicalL4Chain (r : ℕ) :
    ∀ i, 2 ≤ i → i ≤ r + 1 →
      l4ProfileChain (l4Shadow r) r i ≤ canonicalL4Chain r i := by
  intro i hi hir
  let d := l4ProfileChain (l4Shadow r) r
  let c := canonicalL4Chain r
  have hd : IsL4Chain (l4Shadow r) r d :=
    isL4Chain_l4ProfileChain (l4Shadow r) r
  have hc : IsL4Chain canonicalShadow r c :=
    isL4Chain_l4ProfileChain canonicalShadow r
  change d i ≤ c i
  apply Nat.decreasingInduction'
      (P := fun k => d k ≤ c k) (m := i) (n := r + 1) ?_ hir
  · rw [hd.1, hc.1]
  · intro k hkr hik ih
    have hk2 : 2 ≤ k := hi.trans hik
    have hkle : k ≤ r := by omega
    rw [hd.2 k hk2 hkle, hc.2 k hk2 hkle]
    apply Nat.add_le_add_left
    exact (kkShadow_le_canonicalShadow (r + 4) (k + 1)
      (d (k + 1)) (by omega)).trans
        (canonicalShadow_mono (k + 1) (by omega) ih)

/-- L4 forces the bottom of its canonical numerical recurrence over capacity. -/
theorem canonicalL4Chain_bottom_gt (r : ℕ) (hr : 29 ≤ r) :
    (r + 4).choose 2 < canonicalL4Chain r 2 := by
  by_contra h
  have hcap : canonicalL4Chain r 2 ≤ (r + 4).choose 2 := by omega
  apply l4_no_recurrence r hr
  refine ⟨l4ProfileChain (l4Shadow r) r,
    isL4Chain_l4ProfileChain (l4Shadow r) r, ?_⟩
  exact (l4ProfileChain_le_canonicalL4Chain r 2 le_rfl (by omega)).trans hcap

/-- The upper residual recurrence after removing the diagonal shell. -/
def IsUpperCoreRecurrence (r : ℕ) (x : ℕ → ℕ) : Prop :=
  x (r + 3) = 0 ∧
    (∀ b, 3 ≤ b → b ≤ r + 2 →
      x b = r + canonicalShadow (b + 1) (x (b + 1))) ∧
    ∀ b, 4 ≤ b → b ≤ r + 2 → x b < (r + 4).choose b

/-- The canonical recurrence for the upper core on levels `3,...,r+2`. -/
def upperCoreChain (r : ℕ) : ℕ → ℕ :=
  profileChain (fun _ => r) (r + 2)

@[simp] theorem upperCoreChain_above_top (r : ℕ) :
    upperCoreChain r (r + 3) = 0 := by
  exact profileChain_top (fun _ => r) (r + 2)

theorem upperCoreChain_step (r b : ℕ) (hb : b ≤ r + 2) :
    upperCoreChain r b =
      r + canonicalShadow (b + 1) (upperCoreChain r (b + 1)) := by
  exact profileChain_step (fun _ => r) hb

/-- The computational upper-core input only needs to provide strict fit. -/
theorem upperCoreChain_isUpperCoreRecurrence (r : ℕ)
    (hstrict : ∀ b, 4 ≤ b → b ≤ r + 2 →
      upperCoreChain r b < (r + 4).choose b) :
    IsUpperCoreRecurrence r (upperCoreChain r) := by
  exact ⟨upperCoreChain_above_top r,
    (fun b _ hb => upperCoreChain_step r b hb), hstrict⟩

/--
Non-strict upper-core capacity, together with a carry smaller than the
positive prescribed load, implies the strict no-carry inequalities (16.0).
-/
theorem upperCoreChain_strict_of_fit
    (r : ℕ) (hr : 2 ≤ r) {e : ℕ}
    (hfit : ∀ b, 4 ≤ b → b ≤ r + 2 →
      upperCoreChain r b ≤ (r + 4).choose b)
    (hexcess : upperCoreChain r 3 = (r + 4).choose 3 + e)
    (her : e < r) :
    ∀ b, 4 ≤ b → b ≤ r + 2 →
      upperCoreChain r b < (r + 4).choose b := by
  intro b hb4 hbr
  have hle := hfit b hb4 hbr
  apply lt_of_le_of_ne hle
  intro heq'
  have heq : upperCoreChain r b = (r + 4).choose b :=
    heq'
  have hshadow : canonicalShadow b ((r + 4).choose b) =
      (r + 4).choose (b - 1) :=
    canonicalShadow_choose (by omega) (by omega)
  by_cases hb : b = 4
  · subst b
    have hstep := upperCoreChain_step r 3 (by omega)
    rw [heq, hshadow] at hstep
    simp only [show 4 - 1 = 3 by omega] at hstep
    omega
  · have hb5 : 5 ≤ b := by omega
    have hstep := upperCoreChain_step r (b - 1) (by omega)
    rw [show b - 1 + 1 = b by omega, heq, hshadow] at hstep
    have hfitLower := hfit (b - 1) (by omega) (by omega)
    omega

/-- The full constant-profile recurrence, with `r` sets on each occupied level. -/
def fullProfileChain (r : ℕ) : ℕ → ℕ :=
  profileChain (fun _ => r) (2 * r + 3)

@[simp] theorem fullProfileChain_above_top (r : ℕ) :
    fullProfileChain r (2 * r + 4) = 0 := by
  simp [fullProfileChain, show 2 * r + 4 = (2 * r + 3) + 1 by omega]

@[simp] theorem fullProfileChain_top (r : ℕ) :
    fullProfileChain r (2 * r + 3) = r := by
  rw [fullProfileChain, profileChain_step (fun _ => r) (by omega)]
  simp

theorem fullProfileChain_step (r i : ℕ) (hi : i ≤ 2 * r + 3) :
    fullProfileChain r i =
      r + canonicalShadow (i + 1) (fullProfileChain r (i + 1)) := by
  exact profileChain_step (fun _ => r) hi

/--
The upper-shell formula (16.2a): while the residual remains strictly below
the next shell, the full recurrence is the diagonal shell plus that residual.
-/
theorem fullProfileChain_diagonal_transfer
    {r : ℕ} {x : ℕ → ℕ} (hx : IsUpperCoreRecurrence r x) :
    ∀ b, 3 ≤ b → b ≤ r + 3 →
      fullProfileChain r (b + r) =
        (2 * r + 4).choose (b + r) - (r + 4).choose b + x b := by
  intro b hb hbr
  apply Nat.decreasingInduction'
      (P := fun k => fullProfileChain r (k + r) =
        (2 * r + 4).choose (k + r) - (r + 4).choose k + x k)
      (m := b) (n := r + 3) ?_ hbr
  · rw [show r + 3 + r = 2 * r + 3 by omega,
      fullProfileChain_top, hx.1]
    have hB : (2 * r + 4).choose (2 * r + 3) = 2 * r + 4 := by
      simpa only [show 2 * r + 4 = (2 * r + 3) + 1 by omega] using
        Nat.choose_succ_self_right (2 * r + 3)
    have hA : (r + 4).choose (r + 3) = r + 4 := by
      simpa only [show r + 4 = (r + 3) + 1 by omega] using
        Nat.choose_succ_self_right (r + 3)
    rw [hB, hA]
    omega
  · intro k hkr hbk ih
    have hk3 : 3 ≤ k := hb.trans hbk
    have hkupper : k ≤ r + 2 := by omega
    have hres : x (k + 1) < (r + 4).choose (k + 1) := by
      by_cases htop : k + 1 = r + 3
      · rw [htop, hx.1]
        have : 0 < (r + 4).choose (r + 3) := by
          rw [show r + 4 = (r + 3) + 1 by omega,
            Nat.choose_succ_self_right]
          omega
        exact this
      · exact hx.2.2 (k + 1) (by omega) (by omega)
    have htransfer := canonicalShadow_diagonal_transfer
      (A := r + 4) (b := k + 1) (t := r) (x := x (k + 1))
      (by omega) (by omega) hres
    have htransfer' :
        canonicalShadow (k + r + 1)
            ((2 * r + 4).choose (k + r + 1) -
              (r + 4).choose (k + 1) + x (k + 1)) =
          (2 * r + 4).choose (k + r) - (r + 4).choose k +
            canonicalShadow (k + 1) (x (k + 1)) := by
      simpa only [show k + 1 + r = k + r + 1 by omega,
        show r + 4 + r = 2 * r + 4 by omega,
        show k + 1 + r - 1 = k + r by omega,
        show k + r + 1 - 1 = k + r by omega,
        show k + 1 - 1 = k by omega] using htransfer
    have ih' : fullProfileChain r (k + r + 1) =
        (2 * r + 4).choose (k + r + 1) -
          (r + 4).choose (k + 1) + x (k + 1) := by
      simpa only [show k + 1 + r = k + r + 1 by omega] using ih
    rw [fullProfileChain_step r (k + r) (by omega), ih', htransfer']
    rw [hx.2.1 k hk3 hkupper]
    omega

/-- A positive core excess at level three becomes a residual above the shell. -/
theorem fullProfileChain_level_r_add_three
    {r e : ℕ} {x : ℕ → ℕ} (hx : IsUpperCoreRecurrence r x)
    (hx3 : x 3 = (r + 4).choose 3 + e) :
    fullProfileChain r (r + 3) =
      (2 * r + 4).choose (r + 3) + e := by
  have hformula := fullProfileChain_diagonal_transfer hx 3 (by omega) (by omega)
  have hmono : (r + 4).choose 3 ≤
      (2 * r + 4).choose (r + 3) := by
    simpa only [show r + 4 + r = 2 * r + 4 by omega,
      show 3 + r = r + 3 by omega] using
        choose_diagonal_mono (r + 4) 3 r
  rw [show 3 + r = r + 3 by omega, hx3] at hformula
  omega

/-- The residual recurrence (16.3), indexed by distance below its top. -/
def residualDescending (r : ℕ) : ℕ → ℕ
  | 0 => 1
  | d + 1 =>
      r + canonicalShadow (r + 2 - d) (residualDescending r d)

/-- The same residual recurrence indexed by set-size level. -/
def residualChain (r i : ℕ) : ℕ :=
  residualDescending r (r + 3 - i)

@[simp] theorem residualChain_top (r : ℕ) :
    residualChain r (r + 3) = 1 := by
  simp [residualChain, residualDescending]

theorem residualChain_step (r i : ℕ) (hi : 3 ≤ i) (hir : i ≤ r + 2) :
    residualChain r i =
      r + canonicalShadow i (residualChain r (i + 1)) := by
  have hdist : r + 3 - i = (r + 2 - i) + 1 := by omega
  have hlevel : r + 2 - (r + 2 - i) = i := by omega
  have hnext : r + 3 - (i + 1) = r + 2 - i := by omega
  rw [residualChain, hdist, residualDescending, hlevel]
  rw [residualChain, hnext]

theorem residualChain_next_to_top (r : ℕ) (hr : 1 ≤ r) :
    residualChain r (r + 2) = 2 * r + 2 := by
  rw [residualChain_step r (r + 2) (by omega) (by omega),
    residualChain_top, canonicalShadow_one (r + 2) (by omega)]
  omega

/-- The residual recurrence dominates the canonical L4 recurrence one level over. -/
theorem canonicalL4Chain_le_residualChain (r : ℕ) (hr : 1 ≤ r) :
    ∀ i, 2 ≤ i → i ≤ r + 1 →
      canonicalL4Chain r i ≤ residualChain r (i + 1) := by
  intro i hi hir
  have hc : IsL4Chain canonicalShadow r (canonicalL4Chain r) :=
    isL4Chain_l4ProfileChain canonicalShadow r
  apply Nat.decreasingInduction'
      (P := fun k => canonicalL4Chain r k ≤ residualChain r (k + 1))
      (m := i) (n := r + 1) ?_ hir
  · rw [hc.1, residualChain_next_to_top r hr]
    omega
  · intro k hkr hik ih
    have hk2 : 2 ≤ k := hi.trans hik
    have hkle : k ≤ r := by omega
    rw [hc.2 k hk2 hkle,
      residualChain_step r (k + 1) (by omega) (by omega)]
    exact Nat.add_le_add_left
      (canonicalShadow_mono (k + 1) (by omega) ih) r

/-- The bottom residual exceeds the two-level capacity inherited from L4. -/
theorem residualChain_three_gt (r : ℕ) (hr : 29 ≤ r) :
    (r + 4).choose 2 < residualChain r 3 := by
  exact (canonicalL4Chain_bottom_gt r hr).trans_le
    (canonicalL4Chain_le_residualChain r (by omega) 2 le_rfl (by omega))

/--
The full constant-profile recurrence exceeds a level of `Fin (2*r+5)`.
The hypotheses on `x` are precisely the non-computational interface to the
upper-core calculation: strict fit above level three and a positive excess at
level three.
-/
theorem fullProfileChain_overflows
    (r : ℕ) (hr : 29 ≤ r) {x : ℕ → ℕ} {e : ℕ}
    (hx : IsUpperCoreRecurrence r x)
    (hx3 : x 3 = (r + 4).choose 3 + e) (he : 1 ≤ e) :
    ∃ i, 2 ≤ i ∧ i ≤ 2 * r + 3 ∧
      (2 * r + 5).choose i < fullProfileChain r i := by
  by_contra hnot
  have hcap : ∀ i, 2 ≤ i → i ≤ 2 * r + 3 →
      fullProfileChain r i ≤ (2 * r + 5).choose i := by
    intro i hi hii
    by_contra hfail
    apply hnot
    exact ⟨i, hi, hii, by omega⟩
  have hstart : (2 * r + 4).choose (r + 3) + residualChain r (r + 3) ≤
      fullProfileChain r (r + 3) := by
    rw [residualChain_top,
      fullProfileChain_level_r_add_three hx hx3]
    omega
  have noCarry : ∀ k, 3 ≤ k → k ≤ r + 3 →
      (2 * r + 4).choose k + residualChain r k ≤ fullProfileChain r k →
      residualChain r k < (2 * r + 4).choose (k - 1) := by
    intro k hk3 hkr hlower
    by_contra hnotlt
    have hreslarge : (2 * r + 4).choose (k - 1) ≤
        residualChain r k := by omega
    have hp : (2 * r + 5).choose k =
        (2 * r + 4).choose (k - 1) + (2 * r + 4).choose k := by
      simpa only [Nat.succ_eq_add_one,
        show 2 * r + 4 + 1 = 2 * r + 5 by omega,
        show k - 1 + 1 = k by omega] using
          Nat.choose_succ_succ (2 * r + 4) (k - 1)
    have hfull : (2 * r + 5).choose k ≤ fullProfileChain r k := by
      rw [hp]
      omega
    have heq : fullProfileChain r k = (2 * r + 5).choose k := by
      exact Nat.le_antisymm (hcap k (by omega) (by omega)) hfull
    have hstep := fullProfileChain_step r (k - 1) (by omega)
    have hshadow : canonicalShadow k ((2 * r + 5).choose k) =
        (2 * r + 5).choose (k - 1) := by
      exact canonicalShadow_choose (by omega) (by omega)
    rw [show k - 1 + 1 = k by omega, heq, hshadow] at hstep
    have hcapLower := hcap (k - 1) (by omega) (by omega)
    omega
  have hlower3 : (2 * r + 4).choose 3 + residualChain r 3 ≤
      fullProfileChain r 3 := by
    refine Nat.decreasingInduction'
        (P := fun k => (2 * r + 4).choose k + residualChain r k ≤
          fullProfileChain r k)
        (m := 3) (n := r + 3) ?_ (by omega) hstart
    intro k hkr hk3 ih
    have hkupper : k ≤ r + 2 := by omega
    have hnc := noCarry (k + 1) (by omega) (by omega) ih
    have hmono := canonicalShadow_mono (k + 1) (by omega) ih
    have hshell := canonicalShadow_add_shell
      (B := 2 * r + 4) (k := k + 1) (x := residualChain r (k + 1))
      (by omega) (by omega) hnc
    have hstep := fullProfileChain_step r k (by omega)
    have hresstep := residualChain_step r k hk3 hkupper
    rw [hstep]
    calc
      (2 * r + 4).choose k + residualChain r k =
          r + ((2 * r + 4).choose k +
            canonicalShadow k (residualChain r (k + 1))) := by
              rw [hresstep]
              omega
      _ = r + canonicalShadow (k + 1)
          ((2 * r + 4).choose (k + 1) + residualChain r (k + 1)) := by
            rw [hshell]
            simp only [show k + 1 - 1 = k by omega]
      _ ≤ r + canonicalShadow (k + 1) (fullProfileChain r (k + 1)) :=
        Nat.add_le_add_left hmono r
  have hnc3 := noCarry 3 (by omega) (by omega) hlower3
  have hmono3 := canonicalShadow_mono 3 (by omega) hlower3
  have hshell3 := canonicalShadow_add_shell
    (B := 2 * r + 4) (k := 3) (x := residualChain r 3)
    (by omega) (by omega) hnc3
  have hspecial : canonicalShadow 2 ((r + 4).choose 2 + 1) = r + 5 := by
    have hs := canonicalShadow_add_shell
      (B := r + 4) (k := 2) (x := 1) (by omega) (by omega)
        (by simp [Nat.choose_one_right])
    simpa [Nat.choose_one_right, canonicalShadow_one] using hs
  have hresLower : (r + 4).choose 2 + 1 ≤ residualChain r 3 := by
    have := residualChain_three_gt r hr
    omega
  have hshadowLower : r + 5 ≤ canonicalShadow 2 (residualChain r 3) := by
    have hm := canonicalShadow_mono 2 (by omega) hresLower
    rw [hspecial] at hm
    exact hm
  have hM2 : r + (2 * r + 4).choose 2 + (r + 5) ≤
      fullProfileChain r 2 := by
    rw [fullProfileChain_step r 2 (by omega)]
    calc
      r + (2 * r + 4).choose 2 + (r + 5) ≤
          r + ((2 * r + 4).choose 2 +
            canonicalShadow 2 (residualChain r 3)) := by omega
      _ = r + canonicalShadow 3
          ((2 * r + 4).choose 3 + residualChain r 3) := by
            rw [hshell3]
      _ ≤ r + canonicalShadow 3 (fullProfileChain r 3) :=
        Nat.add_le_add_left hmono3 r
  have hp2 : (2 * r + 5).choose 2 =
      (2 * r + 4).choose 1 + (2 * r + 4).choose 2 := by
    simpa only [Nat.succ_eq_add_one,
      show 2 * r + 4 + 1 = 2 * r + 5 by omega] using
        Nat.choose_succ_succ (2 * r + 4) 1
  have hcap2 := hcap 2 le_rfl (by omega)
  rw [hp2, Nat.choose_one_right] at hcap2
  omega

/--
Semantic endpoint: under the upper-core interface, no antichain on
`2*r+5` points can carry `r` members on every level `2,...,2*r+3`.
-/
theorem full_multiplicity_profile_infeasible
    (r : ℕ) (hr : 29 ≤ r) {x : ℕ → ℕ} {e : ℕ}
    (hx : IsUpperCoreRecurrence r x)
    (hx3 : x 3 = (r + 4).choose 3 + e) (he : 1 ≤ e) :
    ¬ ∃ F : Erdos776.Antichain.Family (Fin (2 * r + 5)),
      Erdos776.Antichain.IsSperner F ∧
        ∀ i, 2 ≤ i → i ≤ 2 * r + 3 →
          r ≤ (Erdos776.Antichain.level F i).card := by
  rintro ⟨F, hanti, hprofile⟩
  have hrec := profileChain_isProfileRecurrence_of_antichain
    (n := 2 * r + 5) (lo := 2) (hi := 2 * r + 3)
    (f := fun _ => r) (F := F) hanti hprofile
  obtain ⟨i, hi2, hii, hover⟩ :=
    fullProfileChain_overflows r hr hx hx3 he
  have hcap := hrec.2.2 i hi2 (by omega)
  change fullProfileChain r i ≤ (2 * r + 5).choose i at hcap
  omega

/--
The same semantic endpoint stated directly with the two facts supplied by the
upper-core computation in the research package.
-/
theorem upperCore_full_multiplicity_profile_infeasible
    (r : ℕ) (hr : 29 ≤ r) {e : ℕ}
    (hstrict : ∀ b, 4 ≤ b → b ≤ r + 2 →
      upperCoreChain r b < (r + 4).choose b)
    (hexcess : upperCoreChain r 3 = (r + 4).choose 3 + e)
    (he : 1 ≤ e) :
    ¬ ∃ F : Erdos776.Antichain.Family (Fin (2 * r + 5)),
      Erdos776.Antichain.IsSperner F ∧
        ∀ i, 2 ≤ i → i ≤ 2 * r + 3 →
          r ≤ (Erdos776.Antichain.level F i).card := by
  exact full_multiplicity_profile_infeasible r hr
    (upperCoreChain_isUpperCoreRecurrence r hstrict) hexcess he

/--
Certificate-facing form: ordinary upper-core feasibility and the manuscript's
bound `1 ≤ e ≤ 6` supply every hypothesis of the symbolic obstruction.
-/
theorem upperCore_fit_full_multiplicity_profile_infeasible
    (r : ℕ) (hr : 29 ≤ r) {e : ℕ}
    (hfit : ∀ b, 4 ≤ b → b ≤ r + 2 →
      upperCoreChain r b ≤ (r + 4).choose b)
    (hexcess : upperCoreChain r 3 = (r + 4).choose 3 + e)
    (heLower : 1 ≤ e) (heUpper : e ≤ 6) :
    ¬ ∃ F : Erdos776.Antichain.Family (Fin (2 * r + 5)),
      Erdos776.Antichain.IsSperner F ∧
        ∀ i, 2 ≤ i → i ≤ 2 * r + 3 →
          r ≤ (Erdos776.Antichain.level F i).card := by
  apply upperCore_full_multiplicity_profile_infeasible r hr
      (e := e) ?_ hexcess heLower
  exact upperCoreChain_strict_of_fit r (by omega) hfit hexcess (by omega)

end Erdos776.Uniform


/-!
# Conditional assembly of the uniform threshold profile

This file connects the symbolic obstruction and construction layers.  The
remaining mathematical inputs are represented as ordinary propositions, not
axioms: upper-core recurrence data for the obstruction and one suitable free
core for the construction.
-/

namespace Erdos776.Uniform

open Erdos776.Antichain
open Erdos776.KruskalKatona

/-- An antichain with multiplicity at least `r` on every middle level. -/
def FullMiddleProfileExists (n r : ℕ) : Prop :=
  ∃ F : Family (Fin n),
    IsSperner F ∧ HasMultiplicities F r 2 (n - 2)

/--
The exact core interface needed by persistent padding and `coreToFull`.
The core lives on `r+5` points, reaches level `r+2`, and carries at least `r`
free sets of size `r+1`.
-/
def HasSuitableFreeCore (r : ℕ) : Prop :=
  ∃ C D : Family (Fin (r + 5)),
    IsSperner C ∧
      HasMultiplicities C r 2 (r + 2) ∧
      (D : Set (Finset (Fin (r + 5)))).Sized (r + 1) ∧
      r ≤ D.card ∧
      IsFreeFamily C D

/-- The two upper-core facts supplied by Sections 13--14. -/
def HasUpperCoreData (r : ℕ) : Prop :=
  ∃ e : ℕ,
    (∀ b, 4 ≤ b → b ≤ r + 2 →
      upperCoreChain r b ≤ (r + 4).choose b) ∧
    upperCoreChain r 3 = (r + 4).choose 3 + e ∧
    1 ≤ e ∧ e ≤ 6

/-- The obstruction/construction threshold statement for full middle profiles. -/
def FullMiddleProfileThreshold (r : ℕ) : Prop :=
  (¬ FullMiddleProfileExists (2 * r + 5) r) ∧
    ∀ n, 2 * r + 6 ≤ n → FullMiddleProfileExists n r

/-- Generic full-profile threshold event, with an arbitrary last failing size. -/
def FullMiddleProfileThresholdAt (r N : ℕ) : Prop :=
  (¬ FullMiddleProfileExists N r) ∧
    ∀ n, N < n → FullMiddleProfileExists n r

theorem fullMiddleProfileThreshold_iff_at (r : ℕ) :
    FullMiddleProfileThreshold r ↔
      FullMiddleProfileThresholdAt r (2 * r + 5) := by
  simp only [FullMiddleProfileThreshold, FullMiddleProfileThresholdAt]
  constructor <;> rintro ⟨hfail, hsuccess⟩ <;>
    exact ⟨hfail, fun n hn => hsuccess n (by omega)⟩

/-- Any exact overflow of the prescribed-profile recurrence is an obstruction. -/
theorem not_fullMiddleProfileExists_of_chain_overflow
    {n r i : ℕ} (hi2 : 2 ≤ i) (hin : i ≤ n - 2)
    (hoverflow : n.choose i < profileChain (fun _ => r) (n - 2) i) :
    ¬ FullMiddleProfileExists n r := by
  rintro ⟨F, hanti, hprofile⟩
  have hrec := profileChain_isProfileRecurrence_of_antichain
    (n := n) (lo := 2) (hi := n - 2) (f := fun _ => r)
    (F := F) hanti hprofile
  have hcap := hrec.2.2 i hi2 (by omega)
  exact (Nat.not_lt_of_ge hcap) hoverflow

/-- Every natural offset is an even number plus a zero-or-one remainder. -/
theorem exists_two_step_decomposition {base n : ℕ} (hbase : base ≤ n) :
    ∃ t ε : ℕ, ε < 2 ∧ n = base + 2 * t + ε := by
  let d := n - base
  refine ⟨d / 2, d % 2, Nat.mod_lt d (by omega), ?_⟩
  have hsub : base + d = n := by
    dsimp [d]
    omega
  have hdiv := Nat.mod_add_div d 2
  omega

/-- A suitable free core produces the full middle profile at every later size. -/
theorem fullMiddleProfileExists_of_suitableFreeCore
    {r n : ℕ} (hcore : HasSuitableFreeCore r)
    (hn : 2 * r + 6 ≤ n) :
    FullMiddleProfileExists n r := by
  obtain ⟨C, D, hC, hlevels, hDsize, hDcard, hfree⟩ := hcore
  obtain ⟨t, ε, hε, hnform⟩ :=
    exists_two_step_decomposition (base := 2 * r + 6) hn
  have hspec := iteratedPaddingState_spec
    (r := r) (s := r + 2) (by omega) hC hlevels
    (by simpa only [show r + 2 - 1 = r + 1 by omega] using hDsize)
    hDcard hfree t
  let state := iteratedPaddingState C D t
  have hstateAnti : IsSperner state.family := by
    exact hspec.1
  have hstateLevels :
      HasMultiplicities state.family r 2 (r + 2 + t) := by
    exact hspec.2.1
  let G := CoreGround (IteratedGround (Fin (r + 5)) t) r (Fin ε)
  have hcard : Fintype.card G = n := by
    dsimp [G, CoreGround]
    simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin,
      card_iteratedGround]
    omega
  have hneeded : HasMultiplicities state.family r 2
      (Fintype.card G / 2 - 1) := by
    intro i hi2 hii
    apply hstateLevels i hi2
    rw [hcard] at hii
    have hhalf : n / 2 - 1 ≤ r + 2 + t := by
      omega
    exact hii.trans hhalf
  have hfull := coreToFull_fin
    (α := IteratedGround (Fin (r + 5)) t) (γ := Fin ε) (r := r)
    (C := state.family) (by rw [hcard]; omega) hstateAnti hneeded
  have hcard' : Fintype.card
      (CoreGround (IteratedGround (Fin (r + 5)) t) r (Fin ε)) = n :=
    hcard
  let eFin : Fin (Fintype.card
      (CoreGround (IteratedGround (Fin (r + 5)) t) r (Fin ε))) ↪ Fin n :=
    Fin.castLEEmb hcard'.le
  let F : Family (Fin n) := mapFamily eFin (coreToFullFinFamily
      (α := IteratedGround (Fin (r + 5)) t) (γ := Fin ε) (r := r)
      state.family)
  refine ⟨F, isSperner_mapFamily hfull.1, ?_⟩
  intro i hi2 hin
  unfold HasMultiplicityAt
  simp only [F, card_level_mapFamily]
  exact hfull.2 i hi2 (by simpa only [hcard'] using hin)

/-- The Section 16 theorem expressed through `FullMiddleProfileExists`. -/
theorem not_fullMiddleProfileExists_of_upperCoreData
    (r : ℕ) (hr : 29 ≤ r) (hupper : HasUpperCoreData r) :
    ¬ FullMiddleProfileExists (2 * r + 5) r := by
  obtain ⟨e, hfit, hexcess, heLower, heUpper⟩ := hupper
  intro hfull
  apply upperCore_fit_full_multiplicity_profile_infeasible
    r hr hfit hexcess heLower heUpper
  obtain ⟨F, hanti, hlevels⟩ := hfull
  refine ⟨F, hanti, ?_⟩
  intro i hi2 hii
  exact hlevels i hi2 (by omega)

/--
Pure assembly: once obstruction and a suitable free core are available, all
indices, parity cases, padding stages, and ground-set transports compose.
-/
theorem fullMiddleProfileThreshold_of_components
    {r : ℕ}
    (hobstruction : ¬ FullMiddleProfileExists (2 * r + 5) r)
    (hcore : HasSuitableFreeCore r) :
    FullMiddleProfileThreshold r := by
  exact ⟨hobstruction,
    fun n hn => fullMiddleProfileExists_of_suitableFreeCore hcore hn⟩

/--
Conditional uniform assembly with exactly the two remaining major inputs:
upper-core data and a suitable free core.
-/
theorem uniform_profile_threshold_from_components
    (r : ℕ) (hr : 29 ≤ r)
    (hupper : HasUpperCoreData r)
    (hcore : HasSuitableFreeCore r) :
    FullMiddleProfileThreshold r := by
  exact fullMiddleProfileThreshold_of_components
    (not_fullMiddleProfileExists_of_upperCoreData r hr hupper) hcore

end Erdos776.Uniform


/-!
# The explicit free core from Section 15

The upper-core data first makes the complete constant core profile feasible
on `r+5` points.  We then identify its first `r` top-level colex members and
use them to certify an explicit family of `r` free `(r+1)`-sets.
-/

namespace Erdos776.Uniform

open Finset
open Erdos776.Antichain
open Erdos776.KruskalKatona

/-- The upper-core data makes the complete core recurrence fit on `r+5` points. -/
theorem upperCoreChain_is_core_recurrence
    (r : ℕ) (hr : 1 ≤ r) (hupper : HasUpperCoreData r) :
    IsProfileRecurrence (r + 5) 2 (r + 2) (fun _ => r)
      (upperCoreChain r) := by
  obtain ⟨e, hfit, hexcess, heLower, heUpper⟩ := hupper
  refine ⟨upperCoreChain_above_top r,
    (fun i _ hi => upperCoreChain_step r i hi), ?_⟩
  intro i hi2 hii
  by_cases htop : i = r + 3
  · subst i
    simp
  have hiCore : i ≤ r + 2 := by omega
  by_cases hi2eq : i = 2
  · subst i
    have hten : 10 ≤ (r + 4).choose 2 := by
      have hmono := Nat.choose_le_choose 2 (by omega : 5 ≤ r + 4)
      norm_num at hmono
      exact hmono
    have heLt : e < (r + 4).choose 2 := by omega
    have hshell := canonicalShadow_add_shell
      (B := r + 4) (k := 3) (x := e)
      (by omega) (by omega) heLt
    have hshell' : canonicalShadow 3 ((r + 4).choose 3 + e) =
        (r + 4).choose 2 + canonicalShadow 2 e := by
      simpa only [show 3 - 1 = 2 by omega] using hshell
    have hsix : canonicalShadow 2 6 = 4 := by
      rw [show 6 = (4 : ℕ).choose 2 by norm_num [Nat.choose],
        canonicalShadow_choose (by omega) (by omega)]
      norm_num [Nat.choose]
    have hshadowE : canonicalShadow 2 e ≤ 4 := by
      have hm := canonicalShadow_mono 2 (by omega) heUpper
      rw [hsix] at hm
      exact hm
    have hstep : upperCoreChain r 2 =
        r + ((r + 4).choose 2 + canonicalShadow 2 e) := by
      rw [upperCoreChain_step r 2 (by omega), hexcess, hshell']
    have hp : (r + 5).choose 2 =
        (r + 4).choose 1 + (r + 4).choose 2 := by
      simpa only [show r + 5 = r + 4 + 1 by omega] using
        Nat.choose_succ_succ (r + 4) 1
    calc
      upperCoreChain r 2 =
          r + ((r + 4).choose 2 + canonicalShadow 2 e) := hstep
      _ ≤ r + ((r + 4).choose 2 + 4) := by omega
      _ = (r + 5).choose 2 := by
        rw [hp, Nat.choose_one_right]
        omega
  by_cases hi3eq : i = 3
  · subst i
    have hsix : 6 ≤ (r + 4).choose 2 := by
      have hmono := Nat.choose_le_choose 2 (by omega : 4 ≤ r + 4)
      norm_num at hmono
      exact hmono
    have hp : (r + 5).choose 3 =
        (r + 4).choose 2 + (r + 4).choose 3 := by
      simpa only [show r + 5 = r + 4 + 1 by omega] using
        Nat.choose_succ_succ (r + 4) 2
    rw [hexcess, hp]
    omega
  exact (hfit i (by omega) hiCore).trans
    (Nat.choose_le_choose i (by omega : r + 4 ≤ r + 5))

/-- The natural-number representative of the `j`th top core member. -/
def coreTopNatural (r : ℕ) (j : Fin r) : Finset ℕ :=
  (range (r + 3)).erase (j.val + 3)

/-- The `j`th top core member `X \ {j+3}` on `Fin (r+5)`. -/
noncomputable def coreTopSet (r : ℕ) (j : Fin r) :
    Finset (Fin (r + 5)) :=
  finify (r + 5) (coreTopNatural r j)

/-- The proposed free set is obtained by deleting point zero once more. -/
noncomputable def explicitFreeSet (r : ℕ) (j : Fin r) :
    Finset (Fin (r + 5)) :=
  (coreTopSet r j).erase 0

/-- The family of all `r` explicit free sets. -/
noncomputable def explicitFreeFamily (r : ℕ) :
    Family (Fin (r + 5)) :=
  Finset.univ.image (explicitFreeSet r)

theorem coreTopNatural_bounded {r : ℕ} {j : Fin r} :
    ∀ x ∈ coreTopNatural r j, x < r + 5 := by
  intro x hx
  exact (mem_range.mp (mem_of_mem_erase hx)).trans (by omega)

@[simp] theorem card_coreTopSet (r : ℕ) (j : Fin r) :
    (coreTopSet r j).card = r + 2 := by
  rw [coreTopSet, card_finify coreTopNatural_bounded,
    coreTopNatural, card_erase_of_mem (mem_range.mpr (by omega)), card_range]
  omega

@[simp] theorem zero_mem_coreTopSet (r : ℕ) (j : Fin r) :
    (0 : Fin (r + 5)) ∈ coreTopSet r j := by
  simp [coreTopSet, coreTopNatural]

@[simp] theorem card_explicitFreeSet (r : ℕ) (j : Fin r) :
    (explicitFreeSet r j).card = r + 1 := by
  rw [explicitFreeSet, card_erase_of_mem (zero_mem_coreTopSet r j),
    card_coreTopSet]
  omega

theorem explicitFreeSet_subset_coreTopSet (r : ℕ) (j : Fin r) :
    explicitFreeSet r j ⊆ coreTopSet r j := by
  exact erase_subset _ _

theorem coreTopSet_not_subset_explicitFreeSet (r : ℕ) (j : Fin r) :
    ¬ coreTopSet r j ⊆ explicitFreeSet r j := by
  intro hsub
  exact (notMem_erase 0 (coreTopSet r j))
    (hsub (zero_mem_coreTopSet r j))

theorem explicitFreeSet_injective (r : ℕ) :
    Function.Injective (explicitFreeSet r) := by
  intro i j hij
  apply Fin.ext
  by_contra hval
  let p : Fin (r + 5) := ⟨i.val + 3, by omega⟩
  have hpi : p ∉ explicitFreeSet r i := by
    simp [p, explicitFreeSet, coreTopSet, coreTopNatural]
  have hpj : p ∈ explicitFreeSet r j := by
    simp [p, explicitFreeSet, coreTopSet, coreTopNatural]
    exact hval
  rw [hij] at hpi
  exact hpi hpj

@[simp] theorem card_explicitFreeFamily (r : ℕ) :
    (explicitFreeFamily r).card = r := by
  rw [explicitFreeFamily, card_image_of_injective _
    (explicitFreeSet_injective r)]
  simp

theorem explicitFreeFamily_sized (r : ℕ) :
    (explicitFreeFamily r : Set (Finset (Fin (r + 5)))).Sized (r + 1) := by
  intro d hd
  obtain ⟨j, -, rfl⟩ := mem_image.mp hd
  exact card_explicitFreeSet r j

/-- The top state of the complete core recurrence is exactly `r`. -/
@[simp] theorem upperCoreChain_at_top (r : ℕ) :
    upperCoreChain r (r + 2) = r := by
  rw [upperCoreChain_step r (r + 2) (by omega),
    upperCoreChain_above_top, canonicalShadow_zero]
  omega

theorem coreTopSet_mem_canonicalFamily (r : ℕ) (j : Fin r) :
    coreTopSet r j ∈ canonicalFamily (r + 5) (r + 2) r := by
  have hcanon : IsCanonical (r + 2) (diagonalDigits (r + 2) r) :=
    isCanonical_diagonalDigits (by omega)
  have hvalue : cascadeValue (r + 2) (diagonalDigits (r + 2) r) = r :=
    cascadeValue_diagonalDigits (by omega)
  have hdigits : canonicalDigits (r + 2) r = diagonalDigits (r + 2) r :=
    (canonicalDigits_unique hcanon hvalue).symm
  have hmem : coreTopNatural r j ∈
      cascadeFamily (r + 2) (diagonalDigits (r + 2) r) := by
    exact erase_range_mem_cascadeFamily_diagonalDigits
      (by omega) (by omega) (by omega)
  rw [canonicalFamily, hdigits, finifyFamily]
  exact mem_image.mpr ⟨coreTopNatural r j, hmem, rfl⟩

/-- The canonical constant-profile core used in Section 15. -/
noncomputable def canonicalCore (r : ℕ) : Family (Fin (r + 5)) :=
  profileFamily (r + 5) 2 (r + 2) (upperCoreChain r)

theorem coreTopSet_mem_canonicalCore (r : ℕ) (j : Fin r) :
    coreTopSet r j ∈ canonicalCore r := by
  apply mem_profileFamily.mpr
  refine ⟨r + 2, mem_Icc.mpr ⟨by omega, le_rfl⟩, ?_⟩
  have htop := coreTopSet_mem_canonicalFamily r j
  have hempty : canonicalFamily (r + 5) (r + 3) 0 = ∅ := by
    apply card_eq_zero.mp
    exact card_canonicalFamily
      (n := r + 5) (k := r + 3) (m := 0)
      (by omega) (Nat.zero_le _)
  rw [selectedLayer, upperCoreChain_at_top,
    upperCoreChain_above_top, hempty]
  simpa using htop

/-- Any capacity proof for the core recurrence gives the required core profile. -/
theorem canonicalCore_spec_of_recurrence
    (r : ℕ)
    (hrec : IsProfileRecurrence (r + 5) 2 (r + 2) (fun _ => r)
      (upperCoreChain r)) :
    IsSperner (canonicalCore r) ∧
      HasMultiplicities (canonicalCore r) r 2 (r + 2) := by
  constructor
  · exact isSperner_profileFamily (by omega) hrec
  · intro i hi2 hir
    unfold HasMultiplicityAt
    rw [canonicalCore, level_profileFamily (by omega) hrec hi2 hir,
      card_selectedLayer (by omega) hrec hi2 hir]

/-- The canonical core is an antichain with exactly `r` members per level. -/
theorem canonicalCore_spec
    (r : ℕ) (hr : 1 ≤ r) (hupper : HasUpperCoreData r) :
    IsSperner (canonicalCore r) ∧
      HasMultiplicities (canonicalCore r) r 2 (r + 2) := by
  exact canonicalCore_spec_of_recurrence r
    (upperCoreChain_is_core_recurrence r hr hupper)

/-- Antichainness alone makes every displayed `D_j` free for the core. -/
theorem explicitFreeFamily_isFree_of_isSperner
    (r : ℕ) (hanti : IsSperner (canonicalCore r)) :
    IsFreeFamily (canonicalCore r) (explicitFreeFamily r) := by
  intro d hd
  obtain ⟨j, -, rfl⟩ := mem_image.mp hd
  intro c hc hcd
  have htop : coreTopSet r j ∈ canonicalCore r :=
    coreTopSet_mem_canonicalCore r j
  have hctop : c ⊆ coreTopSet r j :=
    hcd.trans (explicitFreeSet_subset_coreTopSet r j)
  have heq : c = coreTopSet r j := hanti.eq hc htop hctop
  apply coreTopSet_not_subset_explicitFreeSet r j
  simpa [heq] using hcd

/-- Every displayed set `D_j` is free for the entire canonical core. -/
theorem explicitFreeFamily_isFree
    (r : ℕ) (hr : 1 ≤ r) (hupper : HasUpperCoreData r) :
    IsFreeFamily (canonicalCore r) (explicitFreeFamily r) := by
  exact explicitFreeFamily_isFree_of_isSperner r
    (canonicalCore_spec r hr hupper).1

/-- Any feasible canonical core recurrence carries the explicit free family. -/
theorem hasSuitableFreeCore_of_recurrence
    (r : ℕ)
    (hrec : IsProfileRecurrence (r + 5) 2 (r + 2) (fun _ => r)
      (upperCoreChain r)) :
    HasSuitableFreeCore r := by
  have hspec := canonicalCore_spec_of_recurrence r hrec
  refine ⟨canonicalCore r, explicitFreeFamily r,
    hspec.1, hspec.2, explicitFreeFamily_sized r, ?_,
    explicitFreeFamily_isFree_of_isSperner r hspec.1⟩
  rw [card_explicitFreeFamily]

/-- Section 15 supplies the suitable free core required by the assembly. -/
theorem hasSuitableFreeCore_of_upperCoreData
    (r : ℕ) (hr : 1 ≤ r) (hupper : HasUpperCoreData r) :
    HasSuitableFreeCore r := by
  have hspec := canonicalCore_spec r hr hupper
  refine ⟨canonicalCore r, explicitFreeFamily r,
    hspec.1, hspec.2, explicitFreeFamily_sized r, ?_,
    explicitFreeFamily_isFree r hr hupper⟩
  rw [card_explicitFreeFamily]

/--
After formalizing the free core, upper-core data is the sole remaining input
to the full middle-profile threshold for the symbolic range.
-/
theorem fullMiddleProfileThreshold_of_upperCoreData
    (r : ℕ) (hr : 29 ≤ r) (hupper : HasUpperCoreData r) :
    FullMiddleProfileThreshold r := by
  exact uniform_profile_threshold_from_components r hr hupper
    (hasSuitableFreeCore_of_upperCoreData r (by omega) hupper)

end Erdos776.Uniform


/-!
# Reflection and the core carry

This file formalizes Sections 13--14.  The lower-window theorem is exposed as
one semantic feasibility proposition.  Complementing its witness produces the
reflected upper profile; comparison of the two canonical recurrences gives the
upper-core fit and the bound `e ≤ 6`, while semantic L4 forces `e ≥ 1`.
-/

namespace Erdos776.Uniform

open Finset
open Erdos776.Antichain
open Erdos776.KruskalKatona
open Erdos776.L4

/-- The lower-window profile defining the lower bound on `alpha_r`. -/
def lowerWindowProfile (r i : ℕ) : ℕ :=
  if i = r + 1 then r - 6 else r

/-- Semantic form of the sole remaining lower-window input. -/
def LowerWindowFeasible (r : ℕ) : Prop :=
  ∃ F : Family (Fin (r + 4)),
    IsSperner F ∧
      ∀ i, 2 ≤ i → i ≤ r + 1 →
        (level F i).card = lowerWindowProfile r i

/-- The canonical lower-window recurrence used by the finite checker and supersolution. -/
def lowerWindowChain (r : ℕ) : ℕ → ℕ :=
  profileChain (lowerWindowProfile r) (r + 1)

/-- Certificate-facing form of the lower-window theorem: every state fits. -/
def LowerWindowFits (r : ℕ) : Prop :=
  ∀ i, 2 ≤ i → i ≤ r + 2 →
    lowerWindowChain r i ≤ (r + 4).choose i

@[simp] theorem lowerWindowChain_above_top (r : ℕ) :
    lowerWindowChain r (r + 2) = 0 := by
  exact profileChain_top (lowerWindowProfile r) (r + 1)

theorem lowerWindowChain_step (r i : ℕ) (hi : i ≤ r + 1) :
    lowerWindowChain r i = lowerWindowProfile r i +
      canonicalShadow (i + 1) (lowerWindowChain r (i + 1)) := by
  exact profileChain_step (lowerWindowProfile r) hi

/-- Fitting numerical states construct an actual lower-window antichain. -/
theorem lowerWindowFeasible_of_fits
    (r : ℕ) (hfit : LowerWindowFits r) :
    LowerWindowFeasible r := by
  have hrec : IsProfileRecurrence (r + 4) 2 (r + 1)
      (lowerWindowProfile r) (lowerWindowChain r) :=
    ⟨lowerWindowChain_above_top r,
      (fun i _ hi => lowerWindowChain_step r i hi), hfit⟩
  obtain ⟨F, hanti, hprofile, -⟩ :=
    profile_sufficiency (n := r + 4) (lo := 2) (hi := r + 1)
      (f := lowerWindowProfile r) (m := lowerWindowChain r)
      (by omega) hrec
  exact ⟨F, hanti, hprofile⟩

/-- The complemented lower-window profile, supported on levels `3,...,r+2`. -/
def reflectedWindowProfile (r i : ℕ) : ℕ :=
  if i = 3 then r - 6 else r

/-- Its canonical top-down recurrence. -/
def reflectedWindowChain (r : ℕ) : ℕ → ℕ :=
  profileChain (reflectedWindowProfile r) (r + 2)

@[simp] theorem reflectedWindowChain_above_top (r : ℕ) :
    reflectedWindowChain r (r + 3) = 0 := by
  exact profileChain_top (reflectedWindowProfile r) (r + 2)

theorem reflectedWindowChain_step (r i : ℕ) (hi : i ≤ r + 2) :
    reflectedWindowChain r i = reflectedWindowProfile r i +
      canonicalShadow (i + 1) (reflectedWindowChain r (i + 1)) := by
  exact profileChain_step (reflectedWindowProfile r) hi

/-- Above level three, reflection has exactly the upper-core recurrence. -/
theorem reflectedWindowChain_eq_upperCoreChain (r : ℕ) :
    ∀ i, 4 ≤ i → i ≤ r + 3 →
      reflectedWindowChain r i = upperCoreChain r i := by
  intro i hi4 hir
  apply Nat.decreasingInduction'
      (P := fun k => reflectedWindowChain r k = upperCoreChain r k)
      (m := i) (n := r + 3) ?_ hir
  · rw [reflectedWindowChain_above_top, upperCoreChain_above_top]
  · intro k hkr hik ih
    have hk4 : 4 ≤ k := hi4.trans hik
    have hkupper : k ≤ r + 2 := by omega
    rw [reflectedWindowChain_step r k hkupper,
      upperCoreChain_step r k hkupper, ih, reflectedWindowProfile]
    simp [show k ≠ 3 by omega]

/-- The reflected level-three state differs from the core state only in load. -/
theorem reflectedWindowChain_three (r : ℕ) (hr : 2 ≤ r) :
    reflectedWindowChain r 3 =
      (r - 6) + canonicalShadow 4 (upperCoreChain r 4) := by
  rw [reflectedWindowChain_step r 3 (by omega), reflectedWindowProfile,
    if_pos rfl, reflectedWindowChain_eq_upperCoreChain r 4 (by omega) (by omega)]

/-- Complementing a lower-window witness realizes the reflected recurrence. -/
theorem reflectedWindowChain_isProfileRecurrence_of_lowerWindow
    (r : ℕ) (hr : 6 ≤ r) (hwindow : LowerWindowFeasible r) :
    IsProfileRecurrence (r + 4) 3 (r + 2)
      (reflectedWindowProfile r) (reflectedWindowChain r) := by
  obtain ⟨F, hanti, hprofile⟩ := hwindow
  let G : Family (Fin (r + 4)) := Finset.compls F
  have hantiG : IsSperner G := by
    exact isSperner_compls hanti
  apply profileChain_isProfileRecurrence_of_antichain hantiG
  intro i hi3 hir
  have hj2 : 2 ≤ r + 4 - i := by omega
  have hjtop : r + 4 - i ≤ r + 1 := by omega
  have hlevels := hprofile (r + 4 - i) hj2 hjtop
  have hprofiles : reflectedWindowProfile r i =
      lowerWindowProfile r (r + 4 - i) := by
    simp only [reflectedWindowProfile, lowerWindowProfile]
    split_ifs <;> omega
  have hiCard : i ≤ Fintype.card (Fin (r + 4)) := by
    simp
    omega
  have hcompl := card_level_compls (i := i) F hiCard
  have hcompl' : (level G i).card = (level F (r + 4 - i)).card := by
    simpa [G] using hcompl
  rw [hprofiles, ← hlevels, ← hcompl']

/-- Lower-window feasibility supplies every upper-core capacity above level three. -/
theorem upperCoreChain_fit_of_lowerWindow
    (r : ℕ) (hr : 6 ≤ r) (hwindow : LowerWindowFeasible r) :
    ∀ b, 4 ≤ b → b ≤ r + 2 →
      upperCoreChain r b ≤ (r + 4).choose b := by
  have hrec := reflectedWindowChain_isProfileRecurrence_of_lowerWindow
    r hr hwindow
  intro b hb4 hbr
  rw [← reflectedWindowChain_eq_upperCoreChain r b hb4 (by omega)]
  exact hrec.2.2 b (by omega) (by omega)

/-- The reflected level-three capacity says that the core carry is at most six. -/
theorem upperCoreChain_three_le_of_lowerWindow
    (r : ℕ) (hr : 6 ≤ r) (hwindow : LowerWindowFeasible r) :
    upperCoreChain r 3 ≤ (r + 4).choose 3 + 6 := by
  have hrec := reflectedWindowChain_isProfileRecurrence_of_lowerWindow
    r hr hwindow
  have hcap := hrec.2.2 3 le_rfl (by omega)
  rw [reflectedWindowChain_three r (by omega)] at hcap
  have hstep := upperCoreChain_step r 3 (by omega)
  simp only [show 3 + 1 = 4 by omega] at hstep
  omega

/-- If level three also fitted, complementation would produce the forbidden L4 profile. -/
theorem upperCoreChain_three_gt_of_fit
    (r : ℕ) (hr : 29 ≤ r)
    (hfit : ∀ b, 4 ≤ b → b ≤ r + 2 →
      upperCoreChain r b ≤ (r + 4).choose b) :
    (r + 4).choose 3 < upperCoreChain r 3 := by
  by_contra hnot
  have hthree : upperCoreChain r 3 ≤ (r + 4).choose 3 := by omega
  have hrec : IsProfileRecurrence (r + 4) 3 (r + 2)
      (fun _ => r) (upperCoreChain r) := by
    refine ⟨upperCoreChain_above_top r,
      (fun i _ hi => upperCoreChain_step r i hi), ?_⟩
    intro i hi3 hii
    by_cases htop : i = r + 3
    · subst i
      simp
    have hiCore : i ≤ r + 2 := by omega
    by_cases hi : i = 3
    · simpa [hi] using hthree
    · exact hfit i (by omega) hiCore
  obtain ⟨G, hantiG, hprofileG, -⟩ :=
    profile_sufficiency (n := r + 4) (lo := 3) (hi := r + 2)
      (f := fun _ => r) (m := upperCoreChain r) (by omega) hrec
  apply l4_multiplicity_profile_infeasible r hr
  refine ⟨Finset.compls G, ?_⟩
  constructor
  · exact isSperner_compls hantiG
  · intro i hi2 hir
    have hj3 : 3 ≤ r + 4 - i := by omega
    have hjtop : r + 4 - i ≤ r + 2 := by omega
    have hiCard : i ≤ Fintype.card (Fin (r + 4)) := by
      simp
      omega
    have hcompl := card_level_compls (i := i) G hiCard
    have hcompl' : (level (Finset.compls G) i).card =
        (level G (r + 4 - i)).card := by
      simpa using hcompl
    rw [levelFamily_eq_level, hcompl',
      hprofileG (r + 4 - i) hj3 hjtop]

/-- Lower-window feasibility implies the complete upper-core data package. -/
theorem hasUpperCoreData_of_lowerWindowFeasible
    (r : ℕ) (hr : 29 ≤ r) (hwindow : LowerWindowFeasible r) :
    HasUpperCoreData r := by
  have hfit := upperCoreChain_fit_of_lowerWindow r (by omega) hwindow
  have hlower := upperCoreChain_three_gt_of_fit r hr hfit
  have hupper := upperCoreChain_three_le_of_lowerWindow r (by omega) hwindow
  let e := upperCoreChain r 3 - (r + 4).choose 3
  refine ⟨e, hfit, ?_, ?_, ?_⟩
  · dsimp [e]
    omega
  · dsimp [e]
    omega
  · dsimp [e]
    omega

/-- The entire symbolic middle-profile threshold now follows from the lower window. -/
theorem fullMiddleProfileThreshold_of_lowerWindowFeasible
    (r : ℕ) (hr : 29 ≤ r) (hwindow : LowerWindowFeasible r) :
    FullMiddleProfileThreshold r := by
  exact fullMiddleProfileThreshold_of_upperCoreData r hr
    (hasUpperCoreData_of_lowerWindowFeasible r hr hwindow)

/-- Certificate-facing final endpoint: only the lower-window capacities remain. -/
theorem fullMiddleProfileThreshold_of_lowerWindowFits
    (r : ℕ) (hr : 29 ≤ r) (hfit : LowerWindowFits r) :
    FullMiddleProfileThreshold r := by
  exact fullMiddleProfileThreshold_of_lowerWindowFeasible r hr
    (lowerWindowFeasible_of_fits r hfit)

end Erdos776.Uniform


/-!
# Occupied levels and the global threshold formulation

This file formalizes the elementary reduction in Section 17: for `r ≥ 4`, an
`r`-multiplicity antichain with `n-3` occupied levels must occupy exactly the
middle levels `2,...,n-2`.
-/

namespace Erdos776.Uniform

open Finset
open Erdos776.Antichain

/-- The set sizes represented by a family on `Fin n`. -/
def occupiedLevels {n : ℕ} (F : Family (Fin n)) : Finset ℕ :=
  (range (n + 1)).filter fun i => (level F i).Nonempty

@[simp] theorem mem_occupiedLevels {n : ℕ} {F : Family (Fin n)} {i : ℕ} :
    i ∈ occupiedLevels F ↔ i ≤ n ∧ (level F i).Nonempty := by
  simp [occupiedLevels]

/-- An antichain with at least `r` members on each level that it occupies. -/
def IsMultiplicityAntichain {n : ℕ} (F : Family (Fin n)) (r : ℕ) : Prop :=
  IsSperner F ∧
    ∀ i ∈ occupiedLevels F, r ≤ (level F i).card

theorem card_level_le_choose {n i : ℕ} (F : Family (Fin n)) :
    (level F i).card ≤ n.choose i := by
  have hsub : level F i ⊆ (Finset.univ : Finset (Fin n)).powersetCard i := by
    intro s hs
    exact mem_powersetCard.mpr
      ⟨subset_univ s, (mem_level.mp hs).2⟩
  simpa using card_le_card hsub

theorem zero_not_mem_occupiedLevels
    {n r : ℕ} {F : Family (Fin n)}
    (hr : 2 ≤ r) (hF : IsMultiplicityAntichain F r) :
    0 ∉ occupiedLevels F := by
  intro hzero
  have hmult := hF.2 0 hzero
  have hcap := card_level_le_choose (i := 0) F
  simp at hcap
  omega

theorem top_not_mem_occupiedLevels
    {n r : ℕ} {F : Family (Fin n)}
    (hr : 2 ≤ r) (hF : IsMultiplicityAntichain F r) :
    n ∉ occupiedLevels F := by
  intro htop
  have hmult := hF.2 n htop
  have hcap := card_level_le_choose (i := n) F
  rw [Nat.choose_self] at hcap
  omega

/-- Points whose singleton belongs to the family. -/
def singletonPoints {n : ℕ} (F : Family (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun x => ({x} : Finset (Fin n)) ∈ F

def singletonSetEmbedding (n : ℕ) : Fin n ↪ Finset (Fin n) where
  toFun x := {x}
  inj' := by
    intro x y h
    simpa using h

theorem level_one_eq_singletonPoints_map {n : ℕ} (F : Family (Fin n)) :
    level F 1 = (singletonPoints F).map (singletonSetEmbedding n) := by
  ext s
  constructor
  · intro hs
    have hcard := (mem_level.mp hs).2
    rw [card_eq_one] at hcard
    obtain ⟨x, rfl⟩ := hcard
    apply mem_map.mpr
    exact ⟨x, by simpa [singletonPoints] using (mem_level.mp hs).1, rfl⟩
  · intro hs
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hs
    have hxF : ({x} : Finset (Fin n)) ∈ F := (mem_filter.mp hx).2
    exact mem_level.mpr ⟨hxF, card_singleton x⟩

@[simp] theorem card_singletonPoints {n : ℕ} (F : Family (Fin n)) :
    (singletonPoints F).card = (level F 1).card := by
  rw [level_one_eq_singletonPoints_map, card_map]

theorem disjoint_singletonPoints_of_card_ne_one
    {n : ℕ} {F : Family (Fin n)} (hanti : IsSperner F)
    {s : Finset (Fin n)} (hs : s ∈ F) (hcard : s.card ≠ 1) :
    Disjoint s (singletonPoints F) := by
  rw [disjoint_left]
  intro x hxs hxsingle
  have hxF : ({x} : Finset (Fin n)) ∈ F := by
    simpa [singletonPoints] using hxsingle
  have heq : ({x} : Finset (Fin n)) = s :=
    hanti.eq hxF hs (singleton_subset_iff.mpr hxs)
  apply hcard
  rw [← heq]
  simp

theorem card_le_ground_sub_singletons
    {n r : ℕ} {F : Family (Fin n)}
    (hanti : IsSperner F) (hsingle : r ≤ (singletonPoints F).card)
    {s : Finset (Fin n)} (hs : s ∈ F) (hcard : s.card ≠ 1) :
    s.card ≤ n - r := by
  have hdisj := disjoint_singletonPoints_of_card_ne_one hanti hs hcard
  have hunion : (s ∪ singletonPoints F).card =
      s.card + (singletonPoints F).card := card_union_of_disjoint hdisj
  have hground : (s ∪ singletonPoints F).card ≤ n := by
    simpa using card_le_card (subset_univ (s ∪ singletonPoints F))
  omega

/-- If level one occurs, all occupied levels lie in `1,...,n-r`. -/
theorem occupiedLevels_subset_Icc_of_one
    {n r : ℕ} {F : Family (Fin n)}
    (hr : 2 ≤ r) (hnr : r + 1 ≤ n) (hF : IsMultiplicityAntichain F r)
    (hone : 1 ∈ occupiedLevels F) :
    occupiedLevels F ⊆ Finset.Icc 1 (n - r) := by
  have hsingle : r ≤ (singletonPoints F).card := by
    rw [card_singletonPoints]
    exact hF.2 1 hone
  intro i hi
  have hiPos : 1 ≤ i := by
    have hi0 := (mem_occupiedLevels.mp hi).1
    by_contra
    have : i = 0 := by omega
    subst i
    exact zero_not_mem_occupiedLevels hr hF hi
  apply mem_Icc.mpr
  refine ⟨hiPos, ?_⟩
  by_cases hi1 : i = 1
  · omega
  · obtain ⟨s, hslevel⟩ := (mem_occupiedLevels.mp hi).2
    have hsF := (mem_level.mp hslevel).1
    have hscard := (mem_level.mp hslevel).2
    have hle := card_le_ground_sub_singletons hF.1 hsingle hsF (by omega)
    omega

theorem card_occupiedLevels_le_of_one
    {n r : ℕ} {F : Family (Fin n)}
    (hr : 2 ≤ r) (hnr : r + 1 ≤ n) (hF : IsMultiplicityAntichain F r)
    (hone : 1 ∈ occupiedLevels F) :
    (occupiedLevels F).card ≤ n - r := by
  have hcard := card_le_card (occupiedLevels_subset_Icc_of_one hr hnr hF hone)
  simpa [hnr] using hcard

/-! ### The complementary top-level reduction -/

/-- Complementing every member reverses the set of occupied levels. -/
theorem occupiedLevels_compls {n : ℕ} (F : Family (Fin n)) :
    occupiedLevels (Finset.compls F) =
      (occupiedLevels F).image (fun i => n - i) := by
  ext i
  constructor
  · intro hi
    have hi' := mem_occupiedLevels.mp hi
    have hlevel := hi'.2
    rw [level_compls F (by simpa using hi'.1), Finset.compls_nonempty] at hlevel
    apply mem_image.mpr
    refine ⟨n - i, ?_, by omega⟩
    apply mem_occupiedLevels.mpr
    refine ⟨by omega, ?_⟩
    simpa [show n - (n - i) = i by omega] using hlevel
  · intro hi
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
    have hj' := mem_occupiedLevels.mp hj
    apply mem_occupiedLevels.mpr
    refine ⟨by omega, ?_⟩
    rw [level_compls F (by simp), Finset.compls_nonempty]
    simpa [show n - (n - j) = j by omega] using hj'.2

@[simp] theorem card_occupiedLevels_compls {n : ℕ} (F : Family (Fin n)) :
    (occupiedLevels (Finset.compls F)).card = (occupiedLevels F).card := by
  rw [occupiedLevels_compls]
  apply card_image_of_injOn
  intro i hi j hj hij
  have hi' := (mem_occupiedLevels.mp hi).1
  have hj' := (mem_occupiedLevels.mp hj).1
  change n - i = n - j at hij
  omega

theorem isMultiplicityAntichain_compls
    {n r : ℕ} {F : Family (Fin n)}
    (hF : IsMultiplicityAntichain F r) :
    IsMultiplicityAntichain (Finset.compls F) r := by
  refine ⟨isSperner_compls hF.1, ?_⟩
  intro i hi
  have hiLe := (mem_occupiedLevels.mp hi).1
  have hrev : n - i ∈ occupiedLevels F := by
    rw [occupiedLevels_compls] at hi
    obtain ⟨j, hj, hji⟩ := mem_image.mp hi
    have hjLe := (mem_occupiedLevels.mp hj).1
    have : j = n - i := by omega
    simpa [this] using hj
  rw [card_level_compls F (by simpa using hiLe)]
  simpa using hF.2 (n - i) hrev

theorem card_occupiedLevels_le_of_penultimate
    {n r : ℕ} {F : Family (Fin n)}
    (hr : 2 ≤ r) (hnr : r + 1 ≤ n) (hF : IsMultiplicityAntichain F r)
    (htop : n - 1 ∈ occupiedLevels F) :
    (occupiedLevels F).card ≤ n - r := by
  let G : Family (Fin n) := Finset.compls F
  have hG : IsMultiplicityAntichain G r :=
    isMultiplicityAntichain_compls hF
  have hone : 1 ∈ occupiedLevels G := by
    rw [show occupiedLevels G =
      (occupiedLevels F).image (fun i => n - i) by
        simpa [G] using occupiedLevels_compls F]
    apply mem_image.mpr
    exact ⟨n - 1, htop, by omega⟩
  have hbound := card_occupiedLevels_le_of_one hr hnr hG hone
  simpa [G] using hbound

/-! ### Forcing all middle levels -/

theorem occupiedLevels_subset_middle_of_boundary_free
    {n r : ℕ} {F : Family (Fin n)}
    (hr : 2 ≤ r) (hF : IsMultiplicityAntichain F r)
    (hone : 1 ∉ occupiedLevels F) (hpen : n - 1 ∉ occupiedLevels F) :
    occupiedLevels F ⊆ Finset.Icc 2 (n - 2) := by
  intro i hi
  have hiLe := (mem_occupiedLevels.mp hi).1
  have hi0 : i ≠ 0 := fun h =>
    zero_not_mem_occupiedLevels hr hF (h ▸ hi)
  have hiTop : i ≠ n := fun h =>
    top_not_mem_occupiedLevels hr hF (h ▸ hi)
  have hi1 : i ≠ 1 := fun h => hone (h ▸ hi)
  have hiPen : i ≠ n - 1 := fun h => hpen (h ▸ hi)
  exact mem_Icc.mpr ⟨by omega, by omega⟩

theorem card_occupiedLevels_le_of_boundary_free
    {n r : ℕ} {F : Family (Fin n)}
    (hr : 2 ≤ r) (hF : IsMultiplicityAntichain F r)
    (hone : 1 ∉ occupiedLevels F) (hpen : n - 1 ∉ occupiedLevels F) :
    (occupiedLevels F).card ≤ n - 3 := by
  have hcard := card_le_card
    (occupiedLevels_subset_middle_of_boundary_free hr hF hone hpen)
  simpa [Nat.card_Icc, show n - 2 - 1 = n - 3 by omega] using hcard

/-- Section 17 upper bound: at most the `n-3` middle levels can occur. -/
theorem card_occupiedLevels_le_middle
    {n r : ℕ} {F : Family (Fin n)}
    (hr : 4 ≤ r) (hnr : r + 1 ≤ n)
    (hF : IsMultiplicityAntichain F r) :
    (occupiedLevels F).card ≤ n - 3 := by
  by_cases hone : 1 ∈ occupiedLevels F
  · have hbound := card_occupiedLevels_le_of_one (by omega) hnr hF hone
    omega
  by_cases hpen : n - 1 ∈ occupiedLevels F
  · have hbound := card_occupiedLevels_le_of_penultimate (by omega) hnr hF hpen
    omega
  exact card_occupiedLevels_le_of_boundary_free
    (by omega) hF hone hpen

/-- Equality in the occupied-level bound forces exactly levels `2,...,n-2`. -/
theorem occupiedLevels_eq_middle_of_card
    {n r : ℕ} {F : Family (Fin n)}
    (hr : 4 ≤ r) (hnr : r + 1 ≤ n)
    (hF : IsMultiplicityAntichain F r)
    (hcard : (occupiedLevels F).card = n - 3) :
    occupiedLevels F = Finset.Icc 2 (n - 2) := by
  have hone : 1 ∉ occupiedLevels F := by
    intro hone
    have hbound := card_occupiedLevels_le_of_one (by omega) hnr hF hone
    omega
  have hpen : n - 1 ∉ occupiedLevels F := by
    intro hpen
    have hbound := card_occupiedLevels_le_of_penultimate (by omega) hnr hF hpen
    omega
  apply eq_of_subset_of_card_le
    (occupiedLevels_subset_middle_of_boundary_free (by omega) hF hone hpen)
  rw [hcard, Nat.card_Icc]
  omega

/-! ### Equivalence with the full-middle profile -/

/-- Discard every member outside the middle levels. -/
def middlePart {n : ℕ} (F : Family (Fin n)) : Family (Fin n) :=
  F.filter fun s => 2 ≤ s.card ∧ s.card ≤ n - 2

theorem level_middlePart_eq
    {n i : ℕ} (F : Family (Fin n)) (hi2 : 2 ≤ i) (hin : i ≤ n - 2) :
    level (middlePart F) i = level F i := by
  ext s
  constructor
  · intro hs
    exact mem_level.mpr ⟨(mem_filter.mp (mem_level.mp hs).1).1,
      (mem_level.mp hs).2⟩
  · intro hs
    have hs' := mem_level.mp hs
    apply mem_level.mpr
    refine ⟨mem_filter.mpr ⟨hs'.1, ?_⟩, hs'.2⟩
    omega

theorem isSperner_middlePart
    {n : ℕ} {F : Family (Fin n)} (hF : IsSperner F) :
    IsSperner (middlePart F) := by
  intro s hs t ht hst hsub
  apply hst
  exact hF.eq (mem_filter.mp hs).1 (mem_filter.mp ht).1 hsub

theorem occupiedLevels_middlePart_eq
    {n r : ℕ} {F : Family (Fin n)}
    (hr : 1 ≤ r) (hlevels : HasMultiplicities F r 2 (n - 2)) :
    occupiedLevels (middlePart F) = Finset.Icc 2 (n - 2) := by
  ext i
  constructor
  · intro hi
    obtain ⟨s, hs⟩ := (mem_occupiedLevels.mp hi).2
    have hsfilter := (mem_filter.mp (mem_level.mp hs).1).2
    have hscard := (mem_level.mp hs).2
    exact mem_Icc.mpr ⟨by omega, by omega⟩
  · intro hi
    have hi' := mem_Icc.mp hi
    apply mem_occupiedLevels.mpr
    refine ⟨by omega, ?_⟩
    rw [level_middlePart_eq F hi'.1 hi'.2]
    apply card_pos.mp
    have hmult := hlevels i hi'.1 hi'.2
    unfold HasMultiplicityAt at hmult
    omega

theorem isMultiplicityAntichain_middlePart
    {n r : ℕ} {F : Family (Fin n)}
    (hr : 1 ≤ r) (hanti : IsSperner F)
    (hlevels : HasMultiplicities F r 2 (n - 2)) :
    IsMultiplicityAntichain (middlePart F) r := by
  refine ⟨isSperner_middlePart hanti, ?_⟩
  intro i hi
  have hi' : i ∈ Finset.Icc 2 (n - 2) := by
    rw [← occupiedLevels_middlePart_eq hr hlevels]
    exact hi
  rw [level_middlePart_eq F (mem_Icc.mp hi').1 (mem_Icc.mp hi').2]
  exact hlevels i (mem_Icc.mp hi').1 (mem_Icc.mp hi').2

/-- The original extremal event: an `r`-multiplicity antichain attaining `n-3` levels. -/
def OccupiedMiddleProfileExists (n r : ℕ) : Prop :=
  ∃ F : Family (Fin n),
    IsMultiplicityAntichain F r ∧ (occupiedLevels F).card = n - 3

/-- For `r ≥ 4`, attaining `n-3` occupied levels is exactly the full-middle profile. -/
theorem occupiedMiddleProfileExists_iff_fullMiddleProfileExists
    {n r : ℕ} (hr : 4 ≤ r) (hnr : r + 1 ≤ n) :
    OccupiedMiddleProfileExists n r ↔ FullMiddleProfileExists n r := by
  constructor
  · rintro ⟨F, hF, hcard⟩
    have hoccupied := occupiedLevels_eq_middle_of_card hr hnr hF hcard
    refine ⟨F, hF.1, ?_⟩
    intro i hi2 hin
    exact hF.2 i (by rw [hoccupied]; exact mem_Icc.mpr ⟨hi2, hin⟩)
  · rintro ⟨F, hanti, hlevels⟩
    let M := middlePart F
    have hM : IsMultiplicityAntichain M r :=
      isMultiplicityAntichain_middlePart (by omega) hanti hlevels
    refine ⟨M, hM, ?_⟩
    rw [show occupiedLevels M = Finset.Icc 2 (n - 2) by
      simpa [M] using occupiedLevels_middlePart_eq (by omega) hlevels,
      Nat.card_Icc]
    omega

end Erdos776.Uniform


/-!
# The global extremal function and threshold

This file packages the semantic occupied-level reduction as the extremal
function `g(n,r)` from the problem statement and proves that the existing
full-middle-profile threshold really is the least global threshold.
-/

namespace Erdos776.Uniform

open Finset
open Erdos776.Antichain

/-- The maximum number of occupied levels in an `r`-multiplicity antichain. -/
noncomputable def extremalOccupiedLevels (n r : ℕ) : ℕ :=
  by
    classical
    exact (Finset.univ : Finset (Family (Fin n))).sup fun F =>
      if IsMultiplicityAntichain F r then (occupiedLevels F).card else 0

/-- Every admissible family gives a lower bound for `extremalOccupiedLevels`. -/
theorem card_occupiedLevels_le_extremal
    {n r : ℕ} {F : Family (Fin n)} (hF : IsMultiplicityAntichain F r) :
    (occupiedLevels F).card ≤ extremalOccupiedLevels n r := by
  classical
  unfold extremalOccupiedLevels
  have hle := Finset.le_sup
    (s := (Finset.univ : Finset (Family (Fin n))))
    (f := fun G => if IsMultiplicityAntichain G r then
      (occupiedLevels G).card else 0) (mem_univ F)
  simpa [hF] using hle

/-- For `r ≥ 4`, the elementary reduction gives the global upper bound. -/
theorem extremalOccupiedLevels_le_middle
    {n r : ℕ} (hr : 4 ≤ r) (hnr : r + 1 ≤ n) :
    extremalOccupiedLevels n r ≤ n - 3 := by
  classical
  unfold extremalOccupiedLevels
  apply Finset.sup_le
  intro F hFmem
  by_cases hF : IsMultiplicityAntichain F r
  · simpa [hF] using card_occupiedLevels_le_middle hr hnr hF
  · simp [hF]

theorem extremalOccupiedLevels_eq_middle_iff
    {n r : ℕ} (hr : 4 ≤ r) (hnr : r + 1 ≤ n) :
    extremalOccupiedLevels n r = n - 3 ↔ OccupiedMiddleProfileExists n r := by
  classical
  constructor
  · intro hg
    have hpos : 0 < n - 3 := by omega
    have hle : n - 3 ≤
        (Finset.univ : Finset (Family (Fin n))).sup (fun F =>
          if IsMultiplicityAntichain F r then
            (occupiedLevels F).card else 0) := by
      have hle' : n - 3 ≤ extremalOccupiedLevels n r := hg.ge
      simpa only [extremalOccupiedLevels] using hle'
    rw [Finset.le_sup_iff hpos] at hle
    obtain ⟨F, hFuniv, hFcard⟩ := hle
    by_cases hF : IsMultiplicityAntichain F r
    · have hupper := card_occupiedLevels_le_middle hr hnr hF
      simp only [if_pos hF] at hFcard
      refine ⟨F, hF, ?_⟩
      exact Nat.le_antisymm hupper hFcard
    · simp only [if_neg hF] at hFcard
      omega
  · rintro ⟨F, hF, hcard⟩
    apply Nat.le_antisymm (extremalOccupiedLevels_le_middle hr hnr)
    rw [← hcard]
    exact card_occupiedLevels_le_extremal hF

/-- The numerical equality `g(n,r)=n-3` is the full-middle profile event. -/
theorem extremalOccupiedLevels_eq_middle_iff_fullMiddleProfileExists
    {n r : ℕ} (hr : 4 ≤ r) (hnr : r + 1 ≤ n) :
    extremalOccupiedLevels n r = n - 3 ↔ FullMiddleProfileExists n r := by
  rw [extremalOccupiedLevels_eq_middle_iff hr hnr,
    occupiedMiddleProfileExists_iff_fullMiddleProfileExists hr hnr]

/-- `N` is the least integer after which `g(n,r)=n-3` always holds. -/
def IsErdosThreshold (r N : ℕ) : Prop :=
  (∀ n, N < n → extremalOccupiedLevels n r = n - 3) ∧
    ∀ M, (∀ n, M < n → extremalOccupiedLevels n r = n - 3) → N ≤ M

/-- The full-middle threshold assembled earlier is the actual global threshold. -/
theorem isErdosThreshold_of_fullMiddleProfileThresholdAt
    {r N : ℕ} (hr : 4 ≤ r) (hrN : r + 1 ≤ N)
    (hthreshold : FullMiddleProfileThresholdAt r N) :
    IsErdosThreshold r N := by
  have hsuccess : ∀ n, N < n →
      extremalOccupiedLevels n r = n - 3 := by
    intro n hn
    apply (extremalOccupiedLevels_eq_middle_iff_fullMiddleProfileExists
      hr (by omega)).2
    exact hthreshold.2 n hn
  refine ⟨hsuccess, ?_⟩
  intro M hM
  by_contra hMN
  have hg := hM N (by omega)
  have hfull := (extremalOccupiedLevels_eq_middle_iff_fullMiddleProfileExists
    (n := N) hr hrN).1 hg
  exact hthreshold.1 hfull

/-- The standard uniform full-middle threshold is the actual global threshold. -/
theorem isErdosThreshold_of_fullMiddleProfileThreshold
    {r : ℕ} (hr : 4 ≤ r) (hthreshold : FullMiddleProfileThreshold r) :
    IsErdosThreshold r (2 * r + 5) := by
  apply isErdosThreshold_of_fullMiddleProfileThresholdAt hr (by omega)
  exact (fullMiddleProfileThreshold_iff_at r).mp hthreshold

/-- The single remaining lower-window input implies the global threshold. -/
theorem isErdosThreshold_of_lowerWindowFits
    (r : ℕ) (hr : 29 ≤ r) (hfit : LowerWindowFits r) :
    IsErdosThreshold r (2 * r + 5) := by
  exact isErdosThreshold_of_fullMiddleProfileThreshold (by omega)
    (fullMiddleProfileThreshold_of_lowerWindowFits r hr hfit)

end Erdos776.Uniform


/-!
# Supersolutions for the lower-window recurrence

This is the formal comparison principle used throughout Sections 3--11 of
the uniform proof.  Once a numerical sequence pays each incoming load after
shadowing, monotonicity of the canonical Kruskal--Katona shadow keeps the
exact lower-window recurrence below it.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

/-- A supersolution for the constant-load part of the lower-window recurrence. -/
def IsLowerWindowSupersolution (r : ℕ) (V : ℕ → ℕ) : Prop :=
  r - 6 ≤ V (r + 1) ∧
    ∀ i, 2 ≤ i → i ≤ r →
      r + canonicalShadow (i + 1) (V (i + 1)) ≤ V i

theorem lowerWindowProfile_eq_of_le
    {r i : ℕ} (hi : i ≤ r) : lowerWindowProfile r i = r := by
  simp [lowerWindowProfile]
  omega

@[simp] theorem lowerWindowChain_top_value (r : ℕ) :
    lowerWindowChain r (r + 1) = r - 6 := by
  rw [lowerWindowChain_step r (r + 1) le_rfl,
    lowerWindowProfile, if_pos rfl, lowerWindowChain_above_top,
    canonicalShadow_zero, Nat.add_zero]

/-- The exact recurrence stays below every supersolution. -/
theorem lowerWindowChain_le_supersolution
    {r : ℕ} {V : ℕ → ℕ} (hV : IsLowerWindowSupersolution r V) :
    ∀ i, 2 ≤ i → i ≤ r + 1 → lowerWindowChain r i ≤ V i := by
  intro i hi2 hir
  apply Nat.decreasingInduction'
      (P := fun k => lowerWindowChain r k ≤ V k)
      (m := i) (n := r + 1) ?_ hir
  · rw [lowerWindowChain_top_value]
    exact hV.1
  · intro k hkr hik ih
    have hk2 : 2 ≤ k := hi2.trans hik
    have hkle : k ≤ r := by omega
    rw [lowerWindowChain_step r k (by omega), lowerWindowProfile_eq_of_le hkle]
    have hshadow := canonicalShadow_mono (k + 1) (by omega) ih
    exact (Nat.add_le_add_left hshadow r).trans (hV.2 k hk2 hkle)

/-- A capacity-bounded supersolution proves the exact lower-window predicate. -/
theorem lowerWindowFits_of_supersolution
    {r : ℕ} {V : ℕ → ℕ}
    (hV : IsLowerWindowSupersolution r V)
    (hcap : ∀ i, 2 ≤ i → i ≤ r + 1 → V i ≤ (r + 4).choose i) :
    LowerWindowFits r := by
  intro i hi2 hir
  by_cases htop : i = r + 2
  · subst i
    simp
  · have hir' : i ≤ r + 1 := by omega
    exact (lowerWindowChain_le_supersolution hV i hi2 hir').trans
      (hcap i hi2 hir')

/-- It is enough to give supersolution steps as equalities. -/
theorem isLowerWindowSupersolution_of_eq
    {r : ℕ} {V : ℕ → ℕ}
    (htop : r - 6 ≤ V (r + 1))
    (hstep : ∀ i, 2 ≤ i → i ≤ r →
      V i = r + canonicalShadow (i + 1) (V (i + 1))) :
    IsLowerWindowSupersolution r V := by
  refine ⟨htop, ?_⟩
  intro i hi2 hir
  exact (hstep i hi2 hir).ge

end Erdos776.Uniform


/-!
# Parameters of the lower-window anchor ladder

This file formalizes the threshold sequence and the maximal anchor index from
Sections 3--5.  These are pure arithmetic facts, independent of the later
cascade manipulations.
-/

namespace Erdos776.Uniform

/-- `T_q` from (3.1). -/
def anchorThreshold : ℕ → ℕ
  | 0 => 28
  | q + 1 => (anchorThreshold q - 2 * q).choose 2

/-- `B_q = T_q - 2q`. -/
def anchorBase (q : ℕ) : ℕ := anchorThreshold q - 2 * q

@[simp] theorem anchorThreshold_zero : anchorThreshold 0 = 28 := rfl

@[simp] theorem anchorThreshold_succ (q : ℕ) :
    anchorThreshold (q + 1) = (anchorThreshold q - 2 * q).choose 2 := rfl

@[simp] theorem anchorThreshold_one : anchorThreshold 1 = 378 := by
  norm_num [anchorThreshold, Nat.choose_two_right]

@[simp] theorem anchorThreshold_two : anchorThreshold 2 = 70500 := by
  norm_num [anchorThreshold, Nat.choose_two_right]

@[simp] theorem anchorThreshold_three : anchorThreshold 3 = 2484807760 := by
  norm_num [anchorThreshold, Nat.choose_two_right]

/-- A coarse estimate used to prove that the anchor ladder is unbounded. -/
theorem two_mul_le_choose_two :
    ∀ x : ℕ, 5 ≤ x → 2 * x ≤ x.choose 2 := by
  intro x hx
  induction x with
  | zero => omega
  | succ x ih =>
      by_cases hx5 : 5 ≤ x
      · have hprev := ih hx5
        rw [show (x + 1).choose 2 = x.choose 1 + x.choose 2 by
          simpa using Nat.choose_succ_succ x 1]
        simp only [Nat.choose_one_right]
        omega
      · have hx4 : x = 4 := by omega
        subst x
        norm_num [Nat.choose_two_right]

/-- The elementary growth estimate (3.5). -/
theorem anchorThreshold_lower (t : ℕ) (ht : 1 ≤ t) :
    128 * t + 250 ≤ anchorThreshold t := by
  induction t with
  | zero => omega
  | succ t ih =>
      by_cases ht0 : t = 0
      · subst t
        norm_num [Nat.choose_two_right]
      · have ht1 : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr ht0
        have hprev := ih ht1
        let x := anchorThreshold t - 2 * t
        have hx : 126 * t + 250 ≤ x := by
          dsimp [x]
          omega
        have hx5 : 5 ≤ x := by omega
        have hchoose := two_mul_le_choose_two x hx5
        rw [anchorThreshold_succ]
        change (128 * (t + 1) + 250 ≤ x.choose 2)
        exact (show 128 * (t + 1) + 250 ≤ 2 * x by omega).trans hchoose

theorem anchorThreshold_mono (q : ℕ) :
    anchorThreshold q ≤ anchorThreshold (q + 1) := by
  by_cases hq0 : q = 0
  · subst q
    norm_num [Nat.choose_two_right]
  · have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
    have hlower := anchorThreshold_lower q hq1
    let x := anchorThreshold q - 2 * q
    have hx : 5 ≤ x := by
      dsimp [x]
      omega
    have hchoose := two_mul_le_choose_two x hx
    rw [anchorThreshold_succ]
    change anchorThreshold q ≤ x.choose 2
    exact (show anchorThreshold q ≤ 2 * x by
      dsimp [x]
      omega).trans hchoose

theorem monotone_anchorThreshold : Monotone anchorThreshold :=
  monotone_nat_of_le_succ anchorThreshold_mono

theorem anchorThreshold_eventually_gt (r : ℕ) :
    ∃ q, r < anchorThreshold q := by
  refine ⟨r + 1, ?_⟩
  have hlower := anchorThreshold_lower (r + 1) (by omega)
  omega

/-- The first anchor threshold strictly above `r`. -/
noncomputable def firstExceedingAnchor (r : ℕ) : ℕ :=
  Nat.find (anchorThreshold_eventually_gt r)

/-- The maximal `t` satisfying `T_t ≤ r`. -/
noncomputable def maximalAnchorIndex (r : ℕ) : ℕ :=
  firstExceedingAnchor r - 1

/-- The three properties in (3.3), including positivity. -/
def IsMaximalAnchorIndex (r t : ℕ) : Prop :=
  1 ≤ t ∧ anchorThreshold t ≤ r ∧ r < anchorThreshold (t + 1)

theorem firstExceedingAnchor_spec (r : ℕ) :
    r < anchorThreshold (firstExceedingAnchor r) := by
  exact Nat.find_spec (anchorThreshold_eventually_gt r)

theorem maximalAnchorIndex_spec (r : ℕ) (hr : 378 ≤ r) :
    IsMaximalAnchorIndex r (maximalAnchorIndex r) := by
  let q := firstExceedingAnchor r
  have hqspec : r < anchorThreshold q := firstExceedingAnchor_spec r
  have hq2 : 2 ≤ q := by
    by_contra hnot
    have hcases : q = 0 ∨ q = 1 := by omega
    rcases hcases with hq0 | hq1
    · rw [hq0, anchorThreshold_zero] at hqspec
      omega
    · rw [hq1, anchorThreshold_one] at hqspec
      omega
  have hpredlt : q - 1 < q := by omega
  have hpredNot : ¬ r < anchorThreshold (q - 1) := by
    exact Nat.find_min (anchorThreshold_eventually_gt r) hpredlt
  have hsucc : q - 1 + 1 = q := by omega
  dsimp [maximalAnchorIndex, firstExceedingAnchor]
  change IsMaximalAnchorIndex r (q - 1)
  exact ⟨by omega, by omega, by simpa [hsucc] using hqspec⟩

/-- `N = r-2t` from (3.4). -/
def anchorN (r t : ℕ) : ℕ := r - 2 * t

/-- `c = 2t+3` from (3.4). -/
def phaseWidth (t : ℕ) : ℕ := 2 * t + 3

/-- `h = t+2` from (3.4). -/
def phaseSlot (t : ℕ) : ℕ := t + 2

/-- `s_j` from (4.4), with the formula extended harmlessly to `j=0`. -/
def towerStone (r t j : ℕ) : ℕ :=
  r + 1 - phaseWidth t * 2 ^ (j - 1)

/-- The consequence `r ≥ 64c` recorded as (3.6). -/
theorem sixtyFour_mul_phaseWidth_le
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    64 * phaseWidth t ≤ r := by
  have hlower := anchorThreshold_lower t ht.1
  have hTr := ht.2.1
  simp only [phaseWidth]
  omega

theorem first_towerStone_eq (r t : ℕ) :
    towerStone r t 1 = anchorN r t - 2 := by
  simp [towerStone, phaseWidth, anchorN]
  omega

theorem towerStone_succ
    {r t j : ℕ} (hj : 1 ≤ j)
    (hpow : phaseWidth t * 2 ^ j ≤ r + 1) :
    towerStone r t (j + 1) = 2 * towerStone r t j - r - 1 := by
  have hpowEq : 2 ^ j = 2 * 2 ^ (j - 1) := by
    conv_lhs => rw [show j = (j - 1) + 1 by omega, pow_succ]
    omega
  let a := phaseWidth t * 2 ^ (j - 1)
  have hmul : phaseWidth t * 2 ^ j = 2 * a := by
    dsimp [a]
    rw [hpowEq]
    simp [Nat.mul_assoc, Nat.mul_comm]
  have htwoa : 2 * a ≤ r + 1 := by
    rw [← hmul]
    exact hpow
  simp only [towerStone, show j + 1 - 1 = j by omega, hmul]
  change r + 1 - 2 * a = 2 * (r + 1 - a) - r - 1
  omega

end Erdos776.Uniform


/-!
# Exact lower-window anchors

The lists below are the canonical cascades in (3.2): a finite ladder of
two-spaced anchor digits followed by the remaining diagonal (unary) block.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

/-- The digits `r+2, r, ..., r+2-2q` in the anchor part of (3.2). -/
def anchorHeadDigits (r : ℕ) : ℕ → List ℕ
  | 0 => [r + 2]
  | q + 1 => anchorHeadDigits r q ++ [r - 2 * q]

@[simp] theorem length_anchorHeadDigits (r q : ℕ) :
    (anchorHeadDigits r q).length = q + 1 := by
  induction q with
  | zero => rfl
  | succ q ih => simp [anchorHeadDigits, ih]

theorem mem_anchorHeadDigits
    {r q d : ℕ} (hrq : 2 * q ≤ r) (hd : d ∈ anchorHeadDigits r q) :
    ∃ j ≤ q, d = r + 2 - 2 * j := by
  induction q with
  | zero =>
      simp [anchorHeadDigits] at hd
      exact ⟨0, le_rfl, by omega⟩
  | succ q ih =>
      simp only [anchorHeadDigits, List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | rfl
      · obtain ⟨j, hj, rfl⟩ := ih (by omega) hd
        exact ⟨j, by omega, rfl⟩
      · exact ⟨q + 1, le_rfl, by omega⟩

theorem isCanonical_anchorHeadDigits
    {r q : ℕ} (hrq : 2 * q + 2 ≤ r) :
    IsCanonical (r - q) (anchorHeadDigits r q) := by
  induction q with
  | zero =>
      exact isCanonical_singleton (by omega) (by omega)
  | succ q ih =>
      have hprev : IsCanonical (r - q) (anchorHeadDigits r q) :=
        ih (by omega)
      have hlen : (anchorHeadDigits r q).length ≤ r - (q + 1) := by
        rw [length_anchorHeadDigits]
        omega
      have hlower : IsCanonical (r - (q + 1)) (anchorHeadDigits r q) :=
        hprev.lowerIndex (by omega) hlen
      have htail : IsCanonical
          (r - (q + 1) - (anchorHeadDigits r q).length) [r - 2 * q] := by
        rw [length_anchorHeadDigits]
        have hindex : r - (q + 1) - (q + 1) = r - 2 * q - 2 := by omega
        rw [hindex]
        exact isCanonical_singleton (by omega) (by omega)
      rw [anchorHeadDigits]
      apply isCanonical_append hlower htail
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst b
      obtain ⟨j, hj, rfl⟩ :=
        mem_anchorHeadDigits (q := q) (by omega) ha
      omega

theorem anchorThreshold_position_bound (q : ℕ) :
    2 * q + 2 ≤ anchorThreshold q := by
  by_cases hq0 : q = 0
  · subst q
    norm_num
  · have hlower := anchorThreshold_lower q
      (Nat.one_le_iff_ne_zero.mpr hq0)
    omega

/-- The full canonical digit list in (3.2). -/
def anchorDigits (r q : ℕ) : List ℕ :=
  anchorHeadDigits r q ++
    diagonalDigits (r - 2 * q - 1) (r - anchorThreshold q)

/-- Numerical value of the exact `q`-th anchor. -/
def anchorValue (r q : ℕ) : ℕ :=
  cascadeValue (r - q) (anchorDigits r q)

theorem isCanonical_anchorDigits
    {r q : ℕ} (hT : anchorThreshold q ≤ r) :
    IsCanonical (r - q) (anchorDigits r q) := by
  have hpos := anchorThreshold_position_bound q
  have hhead := isCanonical_anchorHeadDigits
    (r := r) (q := q) (by omega)
  have htailLen : r - anchorThreshold q ≤ r - 2 * q - 1 := by omega
  have htail : IsCanonical (r - 2 * q - 1)
      (diagonalDigits (r - 2 * q - 1) (r - anchorThreshold q)) :=
    isCanonical_diagonalDigits htailLen
  unfold anchorDigits
  apply isCanonical_append hhead
  · convert htail using 1
    rw [length_anchorHeadDigits]
    omega
  · intro a ha b hb
    have hbLe := mem_diagonalDigits_le hb
    obtain ⟨j, hj, rfl⟩ :=
      mem_anchorHeadDigits (q := q) (by omega) ha
    omega

/-- The top state is the first exact anchor (`q=0`). -/
theorem lowerWindowChain_eq_anchorValue_zero
    {r : ℕ} (hr : 28 ≤ r) :
    lowerWindowChain r r = anchorValue r 0 := by
  rw [lowerWindowChain_step r r (by omega),
    lowerWindowProfile_eq_of_le le_rfl,
    lowerWindowChain_top_value,
    canonicalShadow_diagonal (show r - 6 ≤ r + 1 by omega)]
  have hidx : r + 1 + 1 - (r - 6) = 8 := by omega
  rw [hidx, show Nat.choose 8 2 = 28 by norm_num [Nat.choose_two_right]]
  unfold anchorValue anchorDigits
  simp only [anchorHeadDigits]
  rw [cascadeValue_append]
  simp only [cascadeValue_cons, cascadeValue_nil, Nat.add_zero,
    List.length_singleton, Nat.sub_zero]
  simp only [anchorThreshold_zero, Nat.mul_zero, Nat.sub_zero]
  rw [cascadeValue_diagonalDigits (show r - 28 ≤ r - 1 by omega)]
  have hsymm : (r + 2).choose r = (r + 2).choose 2 := by
    exact Nat.choose_symm_of_eq_add (by omega)
  rw [hsymm, show r + 1 + 1 = r + 2 by omega]
  have hchoose : 28 ≤ (r + 2).choose 2 := by
    have := Nat.choose_le_choose 2 (show 8 ≤ r + 2 by omega)
    norm_num [Nat.choose_two_right] at this ⊢
    exact this
  omega

/-- Shadowing the diagonal remainder produces the residual in Lemma 3.1. -/
theorem anchorTail_shadow
    {r q : ℕ} (hcurrent : anchorThreshold q ≤ r) :
    cascadeValue (r - q - 1 - (anchorHeadDigits r q).length)
        (diagonalDigits (r - 2 * q - 1) (r - anchorThreshold q)) =
      (r - 2 * q).choose 2 - anchorThreshold (q + 1) := by
  have hpos := anchorThreshold_position_bound q
  have hlen : r - anchorThreshold q ≤ r - 2 * q - 1 := by omega
  rw [length_anchorHeadDigits]
  have hindex : r - q - 1 - (q + 1) = (r - 2 * q - 1) - 1 := by omega
  rw [hindex]
  change cascadeShadowValue (r - 2 * q - 1)
      (diagonalDigits (r - 2 * q - 1) (r - anchorThreshold q)) = _
  rw [cascadeShadowValue_diagonalDigits hlen]
  have htop : r - 2 * q - 1 + 1 = r - 2 * q := by omega
  have hbottom : r - 2 * q - (r - anchorThreshold q) =
      anchorThreshold q - 2 * q := by omega
  rw [htop, hbottom, anchorThreshold_succ]

/-- Appending the next completed anchor contributes `choose (r-2q) 2`. -/
theorem anchorHeadDigits_succ_value
    {r q : ℕ} (hrq : 2 * q + 4 ≤ r) :
    cascadeValue (r - (q + 1)) (anchorHeadDigits r (q + 1)) =
      cascadeValue (r - q - 1) (anchorHeadDigits r q) +
        (r - 2 * q).choose 2 := by
  rw [anchorHeadDigits, cascadeValue_append, length_anchorHeadDigits]
  have hindex : r - (q + 1) - (q + 1) = r - 2 * q - 2 := by omega
  rw [hindex]
  simp only [cascadeValue_cons, cascadeValue_nil, Nat.add_zero]
  have hsymm : (r - 2 * q).choose (r - 2 * q - 2) =
      (r - 2 * q).choose 2 := by
    exact Nat.choose_symm (by omega)
  rw [hsymm]
  congr 1

/-- The new diagonal remainder represents `r-T_(q+1)` exactly. -/
theorem anchorTail_succ_value
    {r q : ℕ} (hnext : anchorThreshold (q + 1) ≤ r) :
    cascadeValue (r - (q + 1) - (anchorHeadDigits r (q + 1)).length)
        (diagonalDigits (r - 2 * (q + 1) - 1)
          (r - anchorThreshold (q + 1))) =
      r - anchorThreshold (q + 1) := by
  have hpos := anchorThreshold_position_bound (q + 1)
  rw [length_anchorHeadDigits]
  have hindex : r - (q + 1) - (q + 1 + 1) =
      r - 2 * (q + 1) - 1 := by omega
  rw [hindex]
  exact cascadeValue_diagonalDigits (by omega)

/-- One exact anchor shadows to the next exact anchor. -/
theorem anchorValue_step
    {r q : ℕ} (hnext : anchorThreshold (q + 1) ≤ r) :
    r + canonicalShadow (r - q) (anchorValue r q) =
      anchorValue r (q + 1) := by
  have hcurrent : anchorThreshold q ≤ r :=
    (anchorThreshold_mono q).trans hnext
  have hcanon := isCanonical_anchorDigits hcurrent
  change r + canonicalShadow (r - q)
      (cascadeValue (r - q) (anchorDigits r q)) = anchorValue r (q + 1)
  rw [canonicalShadow_eq_cascadeShadowValue hcanon rfl]
  unfold anchorValue anchorDigits
  rw [cascadeShadowValue_append, cascadeValue_append]
  rw [anchorHeadDigits_succ_value (show 2 * q + 4 ≤ r by
      have := anchorThreshold_position_bound (q + 1)
      omega)]
  rw [anchorTail_shadow hcurrent, anchorTail_succ_value hnext]
  have hhead : cascadeShadowValue (r - q) (anchorHeadDigits r q) =
      cascadeValue (r - q - 1) (anchorHeadDigits r q) := by
    rfl
  rw [hhead]
  have hbase : anchorThreshold q - 2 * q ≤ r - 2 * q := by omega
  have hchoose : anchorThreshold (q + 1) ≤ (r - 2 * q).choose 2 := by
    rw [anchorThreshold_succ]
    exact Nat.choose_le_choose 2 hbase
  have hchooseSub : (r - 2 * q).choose 2 - anchorThreshold (q + 1) +
      anchorThreshold (q + 1) = (r - 2 * q).choose 2 :=
    Nat.sub_add_cancel hchoose
  have hrSub : r - anchorThreshold (q + 1) + anchorThreshold (q + 1) = r :=
    Nat.sub_add_cancel hnext
  omega

/-- Lemma 3.1: all anchor states are exact states of the recurrence. -/
theorem lowerWindowChain_eq_anchorValue
    {r q : ℕ} (hT : anchorThreshold q ≤ r) :
    lowerWindowChain r (r - q) = anchorValue r q := by
  induction q with
  | zero =>
      simpa using lowerWindowChain_eq_anchorValue_zero
        (show 28 ≤ r by simpa using hT)
  | succ q ih =>
      have hcurrent : anchorThreshold q ≤ r :=
        (anchorThreshold_mono q).trans hT
      have hi := ih hcurrent
      have hqr : q + 1 ≤ r := by
        have := anchorThreshold_position_bound (q + 1)
        omega
      rw [show r - (q + 1) = (r - q) - 1 by omega,
        lowerWindowChain_step r ((r - q) - 1) (by omega),
        lowerWindowProfile_eq_of_le (by omega),
        show (r - q - 1) + 1 = r - q by omega,
        hi]
      exact anchorValue_step hT

/-! ### Capacity on the exact anchor segment -/

theorem anchorDigits_all_lt
    {r q : ℕ} (hT : anchorThreshold q ≤ r) :
    ∀ d ∈ anchorDigits r q, d < r + 3 := by
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · obtain ⟨j, hj, rfl⟩ := mem_anchorHeadDigits
      (q := q) (by
        have := anchorThreshold_position_bound q
        omega) hd
    omega
  · have hdLe := mem_diagonalDigits_le hd
    omega

theorem anchorValue_lt_choose_r3
    {r q : ℕ} (hT : anchorThreshold q ≤ r) :
    anchorValue r q < (r + 3).choose (r - q) := by
  unfold anchorValue
  exact cascadeValue_lt_choose_of_all_lt
    (by omega) (isCanonical_anchorDigits hT) (anchorDigits_all_lt hT)

theorem anchorValue_lt_capacity
    {r q : ℕ} (hT : anchorThreshold q ≤ r) :
    anchorValue r q < (r + 4).choose (r - q) := by
  have hsmall := anchorValue_lt_choose_r3 hT
  have hposBound := anchorThreshold_position_bound q
  have hkpos : 1 ≤ r - q := by omega
  have hterm : 0 < (r + 3).choose (r - q - 1) :=
    Nat.choose_pos (by omega)
  have hp := Nat.choose_succ_succ (r + 3) (r - q - 1)
  have hindex : r - q - 1 + 1 = r - q := by omega
  simp only [Nat.succ_eq_add_one] at hp
  rw [hindex] at hp
  rw [show r + 3 + 1 = r + 4 by omega] at hp
  omega

/-- Every exact state from the top through the maximal anchor fits. -/
theorem lowerWindowChain_fit_anchor_segment
    {r t i : ℕ} (hT : anchorThreshold t ≤ r)
    (hiLower : r - t ≤ i) (hiUpper : i ≤ r + 1) :
    lowerWindowChain r i ≤ (r + 4).choose i := by
  by_cases hitop : i = r + 1
  · subst i
    rw [lowerWindowChain_top_value]
    have hbase : (r + 2).choose (r + 1) ≤ (r + 4).choose (r + 1) :=
      Nat.choose_le_choose (r + 1) (by omega)
    rw [show (r + 2).choose (r + 1) = r + 2 by
      exact Nat.choose_succ_self_right (r + 1)] at hbase
    omega
  · have hir : i ≤ r := by omega
    let q := r - i
    have hq : q ≤ t := by
      dsimp [q]
      omega
    have hTq : anchorThreshold q ≤ r :=
      (monotone_anchorThreshold hq).trans hT
    have hiq : r - q = i := by
      dsimp [q]
      omega
    rw [← hiq, lowerWindowChain_eq_anchorValue hTq]
    exact (anchorValue_lt_capacity hTq).le

/-! ### The additional completed anchor from Section 4 -/

/-- The rounded state (4.1), with the final old remainder completed. -/
def completedAnchorValue (r t : ℕ) : ℕ :=
  cascadeValue (r - t - 1) (anchorHeadDigits r (t + 1))

/-- Descending once past the maximal exact anchor is bounded by (4.1). -/
theorem lowerWindowChain_le_completedAnchor
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    lowerWindowChain r (r - t - 1) ≤ completedAnchorValue r t := by
  have hT := ht.2.1
  have hpos := anchorThreshold_position_bound t
  rw [lowerWindowChain_step r (r - t - 1) (by omega),
    lowerWindowProfile_eq_of_le (by omega),
    show r - t - 1 + 1 = r - t by omega,
    lowerWindowChain_eq_anchorValue hT]
  have hcanon := isCanonical_anchorDigits hT
  change r + canonicalShadow (r - t)
      (cascadeValue (r - t) (anchorDigits r t)) ≤ completedAnchorValue r t
  rw [canonicalShadow_eq_cascadeShadowValue hcanon rfl]
  unfold anchorDigits completedAnchorValue
  rw [cascadeShadowValue_append, anchorTail_shadow hT]
  have hheadSucc := anchorHeadDigits_succ_value
    (r := r) (q := t) (show 2 * t + 4 ≤ r by
      have hlower := anchorThreshold_lower t ht.1
      omega)
  rw [show r - (t + 1) = r - t - 1 by omega] at hheadSucc
  rw [hheadSucc]
  have hhead : cascadeShadowValue (r - t) (anchorHeadDigits r t) =
      cascadeValue (r - t - 1) (anchorHeadDigits r t) := by rfl
  rw [hhead]
  have hbase : anchorThreshold t - 2 * t ≤ r - 2 * t := by omega
  have hnextCap : anchorThreshold (t + 1) ≤ (r - 2 * t).choose 2 := by
    rw [anchorThreshold_succ]
    exact Nat.choose_le_choose 2 hbase
  have hsub : (r - 2 * t).choose 2 - anchorThreshold (t + 1) +
      anchorThreshold (t + 1) = (r - 2 * t).choose 2 :=
    Nat.sub_add_cancel hnextCap
  have hrt : 2 * t ≤ r := by omega
  have hrDecomp : r - 2 * t + 2 * t = r := Nat.sub_add_cancel hrt
  have hrNext : r < anchorThreshold (t + 1) := ht.2.2
  omega

theorem completedAnchorValue_lt_capacity
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    completedAnchorValue r t < (r + 4).choose (r - t - 1) := by
  have hlower := anchorThreshold_lower t ht.1
  have hTr := ht.2.1
  have hcanon0 := isCanonical_anchorHeadDigits
    (r := r) (q := t + 1) (show 2 * (t + 1) + 2 ≤ r by omega)
  have hcanon : IsCanonical (r - t - 1) (anchorHeadDigits r (t + 1)) := by
    simpa only [show r - (t + 1) = r - t - 1 by omega] using hcanon0
  have hall : ∀ d ∈ anchorHeadDigits r (t + 1), d < r + 3 := by
    intro d hd
    obtain ⟨j, hj, rfl⟩ := mem_anchorHeadDigits
      (q := t + 1) (by omega) hd
    omega
  have hsmall : completedAnchorValue r t <
      (r + 3).choose (r - t - 1) := by
    unfold completedAnchorValue
    exact cascadeValue_lt_choose_of_all_lt (by omega) hcanon hall
  have hkpos : 1 ≤ r - t - 1 := by omega
  have hterm : 0 < (r + 3).choose (r - t - 2) :=
    Nat.choose_pos (by omega)
  have hp := Nat.choose_succ_succ (r + 3) (r - t - 2)
  simp only [Nat.succ_eq_add_one] at hp
  rw [show r - t - 2 + 1 = r - t - 1 by omega,
    show r + 3 + 1 = r + 4 by omega] at hp
  omega

end Erdos776.Uniform


/-!
# Finite supersolution segments

This module packages a bounded interval of the lower-window supersolution.
It lets the mathematical blocks of the construction be proved in their
natural parameters and then stitched at a common endpoint.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

def HasEnvelopeSegment
    (r lo hi bottom top : ℕ) : Prop :=
  ∃ V : ℕ → ℕ,
    V lo = bottom ∧
    V hi = top ∧
    (∀ i, lo ≤ i → i < hi →
      r + canonicalShadow (i + 1) (V (i + 1)) ≤ V i) ∧
    ∀ i, lo ≤ i → i ≤ hi → V i ≤ (r + 4).choose i

/-- Reparameterize a segment by its distance below the top level. -/
theorem hasEnvelopeSegment_of_descent
    {r hi len : ℕ} {f : ℕ → ℕ}
    (hlen : len ≤ hi)
    (hstep : ∀ L, L < len →
      r + canonicalShadow (hi - L) (f L) ≤ f (L + 1))
    (hcap : ∀ L, L ≤ len → f L ≤ (r + 4).choose (hi - L)) :
    HasEnvelopeSegment r (hi - len) hi (f len) (f 0) := by
  let V : ℕ → ℕ := fun i => f (hi - i)
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · dsimp [V]
    rw [Nat.sub_sub_self hlen]
  · simp [V]
  · intro i hlo hhi
    let L := hi - (i + 1)
    have hLlt : L < len := by
      dsimp [L]
      omega
    have hiL : hi - L = i + 1 := by
      dsimp [L]
      omega
    have hiPred : hi - i = L + 1 := by
      dsimp [L]
      omega
    have hLdef : hi - (i + 1) = L := rfl
    dsimp [V]
    rw [hLdef, hiPred]
    rw [← hiL]
    exact hstep L hLlt
  · intro i hlo hhi
    let L := hi - i
    have hL : L ≤ len := by
      dsimp [L]
      omega
    have hiL : hi - L = i := by
      dsimp [L]
      omega
    dsimp [V]
    change f L ≤ (r + 4).choose i
    rw [← hiL]
    exact hcap L hL

/-- Stitch a lower segment to a higher one at their common state. -/
theorem HasEnvelopeSegment.stitch
    {r lo mid hi bottom seam top : ℕ}
    (hlow : HasEnvelopeSegment r lo mid bottom seam)
    (hhigh : HasEnvelopeSegment r mid hi seam top)
    (hlomid : lo ≤ mid) (hmidhi : mid < hi) :
    HasEnvelopeSegment r lo hi bottom top := by
  let Vlow := hlow.choose
  let Vhigh := hhigh.choose
  let V : ℕ → ℕ := fun i => if i ≤ mid then Vlow i else Vhigh i
  have hlowSpec := hlow.choose_spec
  have hhighSpec := hhigh.choose_spec
  have hlowBottom : Vlow lo = bottom := hlowSpec.1
  have hlowSeam : Vlow mid = seam := hlowSpec.2.1
  have hhighSeam : Vhigh mid = seam := hhighSpec.1
  have hhighTop : Vhigh hi = top := hhighSpec.2.1
  refine ⟨V, ?_, ?_, ?_, ?_⟩
  · simp [V, hlomid, hlowBottom]
  · have hnot : ¬hi ≤ mid := by omega
    simp [V, hnot, hhighTop]
  · intro i hlo hhi
    by_cases hilow : i < mid
    · have hiMid : i ≤ mid := by omega
      have hisMid : i + 1 ≤ mid := by omega
      simpa [V, hiMid, hisMid] using hlowSpec.2.2.1 i hlo hilow
    · by_cases hieq : i = mid
      · subst i
        have hstep := hhighSpec.2.2.1 mid le_rfl hmidhi
        have hstep' : r + canonicalShadow (mid + 1) (Vhigh (mid + 1)) ≤
            Vhigh mid := hstep
        have hnext : ¬mid + 1 ≤ mid := by omega
        simp only [V, if_pos le_rfl, if_neg hnext]
        rw [hlowSeam]
        rw [hhighSeam] at hstep'
        exact hstep'
      · have hmidlt : mid < i := by omega
        have hiNot : ¬i ≤ mid := by omega
        have hisNot : ¬i + 1 ≤ mid := by omega
        simpa [V, hiNot, hisNot] using
          hhighSpec.2.2.1 i (by omega) hhi
  · intro i hlo hhi
    by_cases hiMid : i ≤ mid
    · simp only [V, if_pos hiMid]
      exact hlowSpec.2.2.2 i hlo hiMid
    · simp only [V, if_neg hiMid]
      exact hhighSpec.2.2.2 i (by omega) hhi

end Erdos776.Uniform


/-!
# The scalar bottom collapse

This file isolates Section 10.  It proves the small residual recurrence and
its terminal value independently of the phase construction that feeds it.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

theorem choose_two_mul_gt_sq {q : ℕ} (hq : 2 ≤ q) :
    q ^ 2 < (2 * q).choose 2 := by
  have hchoose : (2 * q).choose 2 = q * (2 * q - 1) := by
    rw [Nat.choose_two_right]
    calc
      2 * q * (2 * q - 1) / 2 =
          2 * (q * (2 * q - 1)) / 2 := by
            apply congrArg (fun n : ℕ => n / 2)
            simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ = q * (2 * q - 1) := Nat.mul_div_cancel_left _ (by omega)
  rw [hchoose, pow_two]
  have hsplit : 2 * q - 1 = q + (q - 1) := by omega
  rw [hsplit, Nat.mul_add]
  have hpositive : 0 < q * (q - 1) := Nat.mul_pos (by omega) (by omega)
  omega

theorem cascadeShadowValue_two_le
    {q : ℕ} {digits : List ℕ}
    (hlen : digits.length ≤ 2)
    (hall : ∀ d ∈ digits, d < 2 * q) :
    cascadeShadowValue 2 digits ≤ 2 * q := by
  cases digits with
  | nil => simp
  | cons a tail =>
      cases tail with
      | nil =>
          have ha := hall a List.mem_cons_self
          simp [cascadeShadowValue, cascadeValue, Nat.choose_one_right]
          omega
      | cons b tail =>
          cases tail with
          | nil =>
              have ha := hall a List.mem_cons_self
              simp [cascadeShadowValue, cascadeValue, Nat.choose_one_right]
              omega
          | cons c tail => simp at hlen

/-- The estimate on `∂₂` used in the invariant `z_q ≤ q²`. -/
theorem canonicalShadow_two_le_two_mul
    {q m : ℕ} (hq : 2 ≤ q) (hm : m ≤ q ^ 2) :
    canonicalShadow 2 m ≤ 2 * q := by
  have hmLt : m < (2 * q).choose 2 :=
    hm.trans_lt (choose_two_mul_gt_sq hq)
  unfold canonicalShadow
  apply cascadeShadowValue_two_le
  · exact (isCanonical_canonicalDigits (k := 2) (m := m) (by omega)).length_le
  · exact canonicalDigits_all_lt (k := 2) (m := m) (A := 2 * q)
      (by omega) hmLt

/-! Fixed two-shadow values used at the bottom of the induction. -/

theorem canonicalShadow_two_five : canonicalShadow 2 5 = 4 := by
  rw [canonicalShadow_eq_cascadeShadowValue
    (digits := [3, 2]) (by norm_num [IsCanonical])
    (by norm_num [cascadeValue, Nat.choose])]
  norm_num [cascadeShadowValue, cascadeValue, Nat.choose]

theorem canonicalShadow_two_three : canonicalShadow 2 3 = 3 := by
  rw [show 3 = (3 : ℕ).choose 2 by norm_num [Nat.choose],
    canonicalShadow_choose (by omega) (by omega)]
  norm_num

theorem canonicalShadow_two_four : canonicalShadow 2 4 = 4 := by
  rw [canonicalShadow_eq_cascadeShadowValue
    (digits := [3, 1]) (by norm_num [IsCanonical])
    (by norm_num [cascadeValue, Nat.choose])]
  norm_num [cascadeShadowValue, cascadeValue, Nat.choose]

theorem canonicalShadow_two_six : canonicalShadow 2 6 = 4 := by
  rw [show 6 = (4 : ℕ).choose 2 by norm_num [Nat.choose],
    canonicalShadow_choose (by omega) (by omega)]
  norm_num

theorem canonicalShadow_two_seven : canonicalShadow 2 7 = 5 := by
  rw [canonicalShadow_eq_cascadeShadowValue
    (digits := [4, 1]) (by norm_num [IsCanonical])
    (by norm_num [cascadeValue, Nat.choose])]
  norm_num [cascadeShadowValue, cascadeValue, Nat.choose]

theorem canonicalShadow_two_eight : canonicalShadow 2 8 = 5 := by
  rw [canonicalShadow_eq_cascadeShadowValue
    (digits := [4, 2]) (by norm_num [IsCanonical])
    (by norm_num [cascadeValue, Nat.choose])]
  norm_num [cascadeShadowValue, cascadeValue, Nat.choose]

theorem canonicalShadow_two_nine : canonicalShadow 2 9 = 5 := by
  rw [canonicalShadow_eq_cascadeShadowValue
    (digits := [4, 3]) (by norm_num [IsCanonical])
    (by norm_num [cascadeValue, Nat.choose])]
  norm_num [cascadeShadowValue, cascadeValue, Nat.choose]

theorem canonicalShadow_two_eleven : canonicalShadow 2 11 = 6 := by
  rw [canonicalShadow_eq_cascadeShadowValue
    (digits := [5, 1]) (by norm_num [IsCanonical])
    (by norm_num [cascadeValue, Nat.choose])]
  norm_num [cascadeShadowValue, cascadeValue, Nat.choose]

theorem canonicalShadow_two_twelve : canonicalShadow 2 12 = 6 := by
  rw [canonicalShadow_eq_cascadeShadowValue
    (digits := [5, 2]) (by norm_num [IsCanonical])
    (by norm_num [cascadeValue, Nat.choose])]
  norm_num [cascadeShadowValue, cascadeValue, Nat.choose]

theorem canonicalShadow_two_fourteen : canonicalShadow 2 14 = 6 := by
  rw [canonicalShadow_eq_cascadeShadowValue
    (digits := [5, 4]) (by norm_num [IsCanonical])
    (by norm_num [cascadeValue, Nat.choose])]
  norm_num [cascadeShadowValue, cascadeValue, Nat.choose]

theorem canonicalShadow_two_sixteen : canonicalShadow 2 16 = 7 := by
  rw [canonicalShadow_eq_cascadeShadowValue
    (digits := [6, 1]) (by norm_num [IsCanonical])
    (by norm_num [cascadeValue, Nat.choose])]
  norm_num [cascadeShadowValue, cascadeValue, Nat.choose]

theorem canonicalShadow_two_twenty : canonicalShadow 2 20 = 7 := by
  rw [canonicalShadow_eq_cascadeShadowValue
    (digits := [6, 5]) (by norm_num [IsCanonical])
    (by norm_num [cascadeValue, Nat.choose])]
  norm_num [cascadeShadowValue, cascadeValue, Nat.choose]

theorem canonicalShadow_two_thirtySix : canonicalShadow 2 36 = 9 := by
  rw [show 36 = (9 : ℕ).choose 2 by norm_num [Nat.choose],
    canonicalShadow_choose (by omega) (by omega)]
  norm_num

/-- Run the recurrence downward for a prescribed number of steps. -/
def scalarDescent (t : ℕ) : ℕ → ℕ
  | 0 => 0
  | d + 1 =>
      let q := t - d
      2 * q - 1 + canonicalShadow 2 (scalarDescent t d)

/-- `z_q`, with `z_t=0`. -/
def scalarResidual (t q : ℕ) : ℕ := scalarDescent t (t - q)

@[simp] theorem scalarResidual_top (t : ℕ) : scalarResidual t t = 0 := by
  simp [scalarResidual, scalarDescent]

theorem scalarResidual_step
    {t q : ℕ} (hq : 1 ≤ q) (hqt : q ≤ t) :
    scalarResidual t (q - 1) =
      2 * q - 1 + canonicalShadow 2 (scalarResidual t q) := by
  unfold scalarResidual
  rw [show t - (q - 1) = (t - q) + 1 by omega]
  simp only [scalarDescent]
  rw [show t - (t - q) = q by omega]

/-- The quadratic invariant from Lemma 10.2. -/
theorem scalarResidual_le_sq
    {t q : ℕ} (hq : 6 ≤ q) (hqt : q ≤ t) :
    scalarResidual t q ≤ q ^ 2 := by
  apply Nat.decreasingInduction'
      (P := fun k => scalarResidual t k ≤ k ^ 2)
      (m := q) (n := t) ?_ hqt
  · simp
  · intro k hkt hqk ih
    have hk6 : 6 ≤ k := hq.trans hqk
    have hk1t : k + 1 ≤ t := by omega
    rw [show k = (k + 1) - 1 by omega,
      scalarResidual_step (show 1 ≤ k + 1 by omega) hk1t]
    have hshadow := canonicalShadow_two_le_two_mul
      (q := k + 1) (m := scalarResidual t (k + 1)) (by omega) ih
    have hmul : 6 * k ≤ k ^ 2 := by
      rw [pow_two]
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left k hk6
    have hsquare : 2 * (k + 1) - 1 + 2 * (k + 1) ≤ k ^ 2 := by
      omega
    exact (Nat.add_le_add_left hshadow (2 * (k + 1) - 1)).trans hsquare

theorem scalarResidual_two_bounds
    {t : ℕ} (ht : 3 ≤ t) :
    5 ≤ scalarResidual t 2 ∧ scalarResidual t 2 ≤ 11 := by
  constructor
  · rw [show 2 = 3 - 1 by omega, scalarResidual_step (q := 3) (by omega) ht]
    omega
  · by_cases ht3 : t = 3
    · subst t
      norm_num [scalarResidual, scalarDescent, canonicalShadow_two_five,
        canonicalShadow_two_three]
    by_cases ht4 : t = 4
    · subst t
      norm_num [scalarResidual, scalarDescent, canonicalShadow_two_seven,
        canonicalShadow_two_three]
    by_cases ht5 : t = 5
    · subst t
      norm_num [scalarResidual, scalarDescent, canonicalShadow_two_nine,
        canonicalShadow_two_twelve, canonicalShadow_two_five,
        canonicalShadow_two_three]
    have ht6 : 6 ≤ t := by omega
    have hz6 := scalarResidual_le_sq (t := t) (q := 6) (by omega) ht6
    have hs6 := canonicalShadow_mono 2 (by omega) hz6
    rw [show (6 : ℕ) ^ 2 = 36 by norm_num,
      canonicalShadow_two_thirtySix] at hs6
    have hz5 : scalarResidual t 5 ≤ 20 := by
      rw [show 5 = 6 - 1 by omega,
        scalarResidual_step (q := 6) (by omega) ht6]
      omega
    have hs5 := canonicalShadow_mono 2 (by omega) hz5
    rw [canonicalShadow_two_twenty] at hs5
    have hz4 : scalarResidual t 4 ≤ 16 := by
      rw [show 4 = 5 - 1 by omega,
        scalarResidual_step (q := 5) (by omega) (by omega)]
      omega
    have hs4 := canonicalShadow_mono 2 (by omega) hz4
    rw [canonicalShadow_two_sixteen] at hs4
    have hz3 : scalarResidual t 3 ≤ 14 := by
      rw [show 3 = 4 - 1 by omega,
        scalarResidual_step (q := 4) (by omega) (by omega)]
      omega
    have hs3 := canonicalShadow_mono 2 (by omega) hz3
    rw [canonicalShadow_two_fourteen] at hs3
    rw [show 2 = 3 - 1 by omega,
      scalarResidual_step (q := 3) (by omega) (by omega)]
    omega

theorem canonicalShadow_two_eq_five_of_range
    {m : ℕ} (hlower : 7 ≤ m) (hupper : m ≤ 9) :
    canonicalShadow 2 m = 5 := by
  have hm : m = 7 ∨ m = 8 ∨ m = 9 := by omega
  rcases hm with rfl | rfl | rfl
  · exact canonicalShadow_two_seven
  · exact canonicalShadow_two_eight
  · exact canonicalShadow_two_nine

/-- Lemma 10.2, including the exceptional first two anchor indices. -/
theorem scalarResidual_zero (t : ℕ) (ht : 1 ≤ t) :
    scalarResidual t 0 = if t = 1 then 1 else if t = 2 then 4 else 6 := by
  by_cases ht1 : t = 1
  · subst t
    simp [scalarResidual, scalarDescent]
  by_cases ht2 : t = 2
  · subst t
    simp [scalarResidual, scalarDescent, canonicalShadow_two_three]
  have ht3 : 3 ≤ t := by omega
  have hz2 := scalarResidual_two_bounds ht3
  have hshadowLower := canonicalShadow_mono 2 (by omega) hz2.1
  have hshadowUpper := canonicalShadow_mono 2 (by omega) hz2.2
  rw [canonicalShadow_two_five] at hshadowLower
  rw [canonicalShadow_two_eleven] at hshadowUpper
  have hz1 : 7 ≤ scalarResidual t 1 ∧ scalarResidual t 1 ≤ 9 := by
    rw [show 1 = 2 - 1 by omega,
      scalarResidual_step (q := 2) (by omega) (by omega)]
    exact ⟨by omega, by omega⟩
  have hs1 := canonicalShadow_two_eq_five_of_range hz1.1 hz1.2
  rw [show 0 = 1 - 1 by omega,
    scalarResidual_step (q := 1) (by omega) (by omega), hs1]
  simp [ht1, ht2]

end Erdos776.Uniform


/-!
# The final two lower-window levels

This is Section 11.  It turns the three possible terminal scalar residuals
into the exact level-three and level-two supersolution states.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

/-- `F₀(z)` at level four. -/
def finalFourState (r z : ℕ) : ℕ :=
  (r + 2).choose 4 + (r + 1).choose 3 + z

/-- The general level-four to level-three identity (11.1). -/
theorem finalFourState_step
    {r z : ℕ} (hr : 6 ≤ r) (hz : z ≤ 6) (hzpos : 1 ≤ z) :
    r + canonicalShadow 4 (finalFourState r z) =
      (r + 3).choose 3 + (canonicalShadow 2 z - 1) := by
  have hzCap : z < (r + 1).choose 2 := by
    have hcap : 10 ≤ (r + 1).choose 2 := by
      have hmono := Nat.choose_le_choose 2 (show 5 ≤ r + 1 by omega)
      norm_num at hmono
      exact hmono
    omega
  have hinnerCap : (r + 1).choose 3 + z < (r + 2).choose 3 := by
    have hp := Nat.choose_succ_succ (r + 1) 2
    simpa only [Nat.succ_eq_add_one, ← hp] using (show
      (r + 1).choose 3 + z <
        (r + 1).choose 2 + (r + 1).choose 3 by omega)
  have hshell4 := canonicalShadow_add_shell
    (B := r + 2) (k := 4) (x := (r + 1).choose 3 + z)
    (by omega) (by omega) hinnerCap
  have hshell3 := canonicalShadow_add_shell
    (B := r + 1) (k := 3) (x := z)
    (by omega) (by omega) hzCap
  have hshell4' : canonicalShadow 4
      ((r + 2).choose 4 + ((r + 1).choose 3 + z)) =
      (r + 2).choose 3 + canonicalShadow 3 ((r + 1).choose 3 + z) := by
    simpa using hshell4
  have hshell3' : canonicalShadow 3 ((r + 1).choose 3 + z) =
      (r + 1).choose 2 + canonicalShadow 2 z := by
    simpa using hshell3
  unfold finalFourState
  rw [show (r + 2).choose 4 + (r + 1).choose 3 + z =
      (r + 2).choose 4 + ((r + 1).choose 3 + z) by omega,
    hshell4', hshell3']
  have hp1 : (r + 2).choose 2 = r + 1 + (r + 1).choose 2 := by
    simpa only [Nat.succ_eq_add_one, Nat.choose_one_right,
      show r + 1 + 1 = r + 2 by omega] using
        Nat.choose_succ_succ (r + 1) 1
  have hp2 : (r + 3).choose 3 =
      (r + 2).choose 2 + (r + 2).choose 3 := by
    simpa only [Nat.succ_eq_add_one,
      show r + 2 + 1 = r + 3 by omega] using
        Nat.choose_succ_succ (r + 2) 2
  have hshadowPos := canonicalShadow_pos (k := 2) (m := z) (by omega) hzpos
  have hshadowSub : canonicalShadow 2 z - 1 + 1 = canonicalShadow 2 z :=
    Nat.sub_add_cancel hshadowPos
  omega

theorem finalFourState_scalar_step
    {r t : ℕ} (hr : 6 ≤ r) (ht : 1 ≤ t) :
    r + canonicalShadow 4 (finalFourState r (scalarResidual t 0)) =
      if t = 1 then (r + 3).choose 3 + 1
      else (r + 3).choose 3 + 3 := by
  have hz := scalarResidual_zero t ht
  by_cases ht1 : t = 1
  · subst t
    have hz1 : scalarResidual 1 0 = 1 := by simpa using hz
    rw [hz1, finalFourState_step hr (by omega) (by omega)]
    simp [canonicalShadow_one]
  · simp only [if_neg ht1] at hz ⊢
    by_cases ht2 : t = 2
    · subst t
      have hz2 : scalarResidual 2 0 = 4 := by simpa using hz
      rw [hz2, finalFourState_step hr (by omega) (by omega),
        canonicalShadow_two_four]
    · have hz6 : scalarResidual t 0 = 6 := by simpa [ht2] using hz
      rw [hz6, finalFourState_step hr (by omega) (by omega),
        canonicalShadow_two_six]

/-- The last shadow is one below capacity for `t=1`, and tight thereafter. -/
theorem finalThreeState_step
    {r d : ℕ} (hr : 6 ≤ r) (hd : d = 1 ∨ d = 3) :
    r + canonicalShadow 3 ((r + 3).choose 3 + d) =
      if d = 1 then (r + 4).choose 2 - 1 else (r + 4).choose 2 := by
  have hdCap : d < (r + 3).choose 2 := by
    have hcap : 6 ≤ (r + 3).choose 2 := by
      have hmono := Nat.choose_le_choose 2 (show 4 ≤ r + 3 by omega)
      norm_num at hmono
      exact hmono
    rcases hd with rfl | rfl <;> omega
  have hp : (r + 4).choose 2 = r + 3 + (r + 3).choose 2 := by
    simpa only [Nat.succ_eq_add_one, Nat.choose_one_right,
      show r + 3 + 1 = r + 4 by omega] using
        Nat.choose_succ_succ (r + 3) 1
  rcases hd with rfl | rfl
  · change r + canonicalShadow 3 ((r + 3).choose 3 + 1) =
      (r + 4).choose 2 - 1
    have hshell := canonicalShadow_add_shell
      (B := r + 3) (k := 3) (x := 1)
      (by omega) (by omega) hdCap
    have hshell' : canonicalShadow 3 ((r + 3).choose 3 + 1) =
        (r + 3).choose 2 + canonicalShadow 2 1 := by
      simpa using hshell
    rw [hshell', canonicalShadow_one 2 (by omega)]
    have hpSub : (r + 4).choose 2 - 1 =
        r + 2 + (r + 3).choose 2 := by omega
    rw [hpSub]
    omega
  · change r + canonicalShadow 3 ((r + 3).choose 3 + 3) =
      (r + 4).choose 2
    have hshell := canonicalShadow_add_shell
      (B := r + 3) (k := 3) (x := 3)
      (by omega) (by omega) hdCap
    have hshell' : canonicalShadow 3 ((r + 3).choose 3 + 3) =
        (r + 3).choose 2 + canonicalShadow 2 3 := by
      simpa using hshell
    rw [hshell', canonicalShadow_two_three]
    rw [hp]
    omega

theorem finalScalar_bottom
    {r t : ℕ} (hr : 6 ≤ r) (_ht : 1 ≤ t) :
    let E3 := if t = 1 then (r + 3).choose 3 + 1
      else (r + 3).choose 3 + 3
    r + canonicalShadow 3 E3 =
      if t = 1 then (r + 4).choose 2 - 1 else (r + 4).choose 2 := by
  dsimp only
  by_cases ht1 : t = 1
  · simp only [ht1, if_pos]
    exact finalThreeState_step hr (Or.inl rfl)
  · simp only [ht1, if_false]
    exact finalThreeState_step hr (Or.inr rfl)

end Erdos776.Uniform


/-!
# Parameters of the doubling-phase segment

This file formalizes the integer `K` selected in Section 5 and the resulting
lower bounds on the tower stones.  In particular, `phaseCount` is selected by
least-number search; it is not an externally computed parameter.
-/

namespace Erdos776.Uniform

/-- The elementary exponential estimate used to show that a phase count exists. -/
theorem succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ]
      omega

/-- Some power of two, after scaling by the positive phase width, exceeds `r/4`. -/
theorem exists_phaseCount_exponent (r t : ℕ) :
    ∃ K, r / 4 < phaseWidth t * 2 ^ K := by
  let x := r / 4
  refine ⟨x + 1, ?_⟩
  have hpow := succ_le_two_pow (x + 1)
  have hwidth : 1 ≤ phaseWidth t := by simp [phaseWidth]
  have hmul := Nat.mul_le_mul_right (2 ^ (x + 1)) hwidth
  dsimp [x] at hpow ⊢
  have hscaled : 2 ^ (r / 4 + 1) ≤
      phaseWidth t * 2 ^ (r / 4 + 1) := by
    simpa [Nat.mul_comm] using hmul
  omega

/-- The least `K` for which `r/4 < c 2^K`. -/
noncomputable def phaseCount (r t : ℕ) : ℕ :=
  Nat.find (exists_phaseCount_exponent r t)

theorem phaseCount_upper (r t : ℕ) :
    r / 4 < phaseWidth t * 2 ^ phaseCount r t := by
  exact Nat.find_spec (exists_phaseCount_exponent r t)

/-- The two inequalities selecting `K` in (5.1), together with positivity. -/
def IsPhaseCount (r t K : ℕ) : Prop :=
  1 ≤ K ∧
    phaseWidth t * 2 ^ (K - 1) ≤ r / 4 ∧
    r / 4 < phaseWidth t * 2 ^ K

theorem phaseCount_spec_of_width_le
    {r t : ℕ} (hwidth : phaseWidth t ≤ r / 4) :
    IsPhaseCount r t (phaseCount r t) := by
  have hupper := phaseCount_upper r t
  have hpos : 1 ≤ phaseCount r t := by
    by_contra hnot
    have hzero : phaseCount r t = 0 := by omega
    rw [hzero] at hupper
    simp only [pow_zero, Nat.mul_one] at hupper
    omega
  have hminimal : ¬ r / 4 <
      phaseWidth t * 2 ^ (phaseCount r t - 1) := by
    have hlt : phaseCount r t - 1 < phaseCount r t := by omega
    simpa only [phaseCount] using
      (Nat.find_min (exists_phaseCount_exponent r t) hlt)
  exact ⟨hpos, Nat.le_of_not_gt hminimal, hupper⟩

theorem phaseWidth_le_quarter
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    phaseWidth t ≤ r / 4 := by
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 4)).2
  have h64 := sixtyFour_mul_phaseWidth_le ht
  omega

/-- Under the maximal-anchor hypotheses, the least exponent satisfies `K ≥ 5`. -/
theorem five_le_phaseCount
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    5 ≤ phaseCount r t := by
  have hspec := phaseCount_spec_of_width_le (phaseWidth_le_quarter ht)
  by_contra hnot
  have hK4 : phaseCount r t ≤ 4 := by omega
  have hpow : 2 ^ phaseCount r t ≤ 2 ^ 4 :=
    pow_le_pow_right' (by omega) hK4
  have hscaled : phaseWidth t * 2 ^ phaseCount r t ≤
      phaseWidth t * 2 ^ 4 := Nat.mul_le_mul_left _ hpow
  have hquarter : 16 * phaseWidth t ≤ r / 4 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 4)).2
    have h64 := sixtyFour_mul_phaseWidth_le ht
    omega
  have hscaled' : phaseWidth t * 2 ^ phaseCount r t ≤
      16 * phaseWidth t := by
    norm_num at hscaled ⊢
    simpa [Nat.mul_comm] using hscaled
  have := hscaled'.trans hquarter
  have hupper := hspec.2.2
  omega

theorem phaseCount_spec
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    IsPhaseCount r t (phaseCount r t) :=
  phaseCount_spec_of_width_le (phaseWidth_le_quarter ht)

/-- For every ordinary phase, the tower stone remains above `3r/4`. -/
theorem towerStone_phase_lower
    {r t j : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t) :
    3 * r / 4 + 1 ≤ towerStone r t j := by
  have hspec := phaseCount_spec ht
  have hexp : j - 1 ≤ phaseCount r t - 1 := by omega
  have hpow : 2 ^ (j - 1) ≤ 2 ^ (phaseCount r t - 1) :=
    pow_le_pow_right' (by omega) hexp
  have hdist : phaseWidth t * 2 ^ (j - 1) ≤ r / 4 :=
    (Nat.mul_le_mul_left _ hpow).trans hspec.2.1
  unfold towerStone
  omega

/-- The first stone after the ordinary phases is still above `r/2`. -/
theorem towerStone_after_phases_lower
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    r / 2 + 1 ≤ towerStone r t (phaseCount r t + 1) := by
  have hspec := phaseCount_spec ht
  have hK : 1 ≤ phaseCount r t := hspec.1
  have hpow : 2 ^ phaseCount r t =
      2 * 2 ^ (phaseCount r t - 1) := by
    conv_lhs => rw [show phaseCount r t = phaseCount r t - 1 + 1 by omega,
      pow_succ]
    omega
  have hdist : phaseWidth t * 2 ^ phaseCount r t ≤ r / 2 := by
    have hlower := hspec.2.1
    calc
      phaseWidth t * 2 ^ phaseCount r t =
          2 * (phaseWidth t * 2 ^ (phaseCount r t - 1)) := by
        rw [hpow]
        ac_rfl
      _ ≤ 2 * (r / 4) := Nat.mul_le_mul_left 2 hlower
      _ ≤ r / 2 := by omega
  simp only [towerStone, show phaseCount r t + 1 - 1 = phaseCount r t by omega]
  omega

end Erdos776.Uniform


/-!
# Positions and birth levels of the ordinary phases

This file formalizes (5.4)--(5.8).  Phase numbers are one-based.  The value
at index zero is defined to agree with phase one only so that the recursive
definition is total; all mathematical statements below use `1 ≤ j`.
-/

namespace Erdos776.Uniform

/-- The active top position `u_j`. -/
def phaseTop (r t : ℕ) : ℕ → ℕ
  | 0 => anchorN r t - 4
  | 1 => anchorN r t - 4
  | 2 =>
      let u := anchorN r t - 4
      u - (u - 5) / 2 - 2
  | j + 3 => (phaseTop r t (j + 2) + 1) / 2

@[simp] theorem phaseTop_zero (r t : ℕ) :
    phaseTop r t 0 = anchorN r t - 4 := rfl

@[simp] theorem phaseTop_one (r t : ℕ) :
    phaseTop r t 1 = anchorN r t - 4 := rfl

@[simp] theorem phaseTop_two (r t : ℕ) :
    phaseTop r t 2 =
      (anchorN r t - 4) - ((anchorN r t - 4) - 5) / 2 - 2 := rfl

/-- The number `ell_j` of in-phase extensions. -/
def phaseExtensionCount (r t j : ℕ) : ℕ :=
  if j = 1 then (phaseTop r t j - 5) / 2
  else (phaseTop r t j - 4) / 2

theorem phaseTop_one_eq_width
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    phaseTop r t 1 = r - phaseWidth t - 1 := by
  have h64 := sixtyFour_mul_phaseWidth_le ht
  simp [phaseTop, anchorN, phaseWidth] at h64 ⊢
  omega

theorem five_le_phaseTop_one
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    5 ≤ phaseTop r t 1 := by
  rw [phaseTop_one_eq_width ht]
  have h64 := sixtyFour_mul_phaseWidth_le ht
  have hc : 3 ≤ phaseWidth t := by simp [phaseWidth]
  omega

/-- Apart from the exceptional first transition, `u_{j+1}=ceil(u_j/2)`. -/
theorem phaseTop_succ_eq_ceil
    {r t j : ℕ} (hj : 2 ≤ j) :
    phaseTop r t (j + 1) = (phaseTop r t j + 1) / 2 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show 2 + j + 1 = j + 3 by omega,
    show 2 + j = j + 2 by omega]
  rfl

/-- The recurrence in (5.6), including the exceptional definition of `ell_1`. -/
theorem phaseTop_succ_eq_sub
    {r t j : ℕ} (hj : 1 ≤ j) (hu : 4 ≤ phaseTop r t j) :
    phaseTop r t (j + 1) =
      phaseTop r t j - phaseExtensionCount r t j - 2 := by
  by_cases hj1 : j = 1
  · subst j
    rw [show 1 + 1 = 2 by omega, phaseTop_two, phaseTop_one]
    simp [phaseExtensionCount]
  · have hj2 : 2 ≤ j := by omega
    rw [phaseTop_succ_eq_ceil hj2]
    simp only [phaseExtensionCount, if_neg hj1]
    omega

/-- Every phase transition is at least a halving. -/
theorem phaseTop_le_two_mul_succ
    {r t j : ℕ} (ht : IsMaximalAnchorIndex r t) (hj : 1 ≤ j) :
    phaseTop r t j ≤ 2 * phaseTop r t (j + 1) := by
  by_cases hj1 : j = 1
  · subst j
    have hu := five_le_phaseTop_one ht
    rw [show 1 + 1 = 2 by omega, phaseTop_two, phaseTop_one]
    rw [phaseTop_one] at hu
    omega
  · have hj2 : 2 ≤ j := by omega
    rw [phaseTop_succ_eq_ceil hj2]
    omega

/-- The rounding error in a phase transition is at most two. -/
theorem two_mul_phaseTop_succ_le
    {r t j : ℕ} (ht : IsMaximalAnchorIndex r t) (hj : 1 ≤ j) :
    2 * phaseTop r t (j + 1) ≤ phaseTop r t j + 2 := by
  by_cases hj1 : j = 1
  · subst j
    have hu := five_le_phaseTop_one ht
    rw [show 1 + 1 = 2 by omega, phaseTop_two, phaseTop_one]
    rw [phaseTop_one] at hu
    omega
  · have hj2 : 2 ≤ j := by omega
    rw [phaseTop_succ_eq_ceil hj2]
    omega

theorem phaseTop_succ_le (r t j : ℕ) :
    phaseTop r t (j + 1) ≤ phaseTop r t j := by
  by_cases hj0 : j = 0
  · subst j
    simp
  by_cases hj1 : j = 1
  · subst j
    rw [show 1 + 1 = 2 by omega, phaseTop_two, phaseTop_one]
    omega
  · rw [phaseTop_succ_eq_ceil (j := j) (by omega)]
    omega

theorem antitone_phaseTop (r t : ℕ) : Antitone (phaseTop r t) :=
  antitone_nat_of_succ_le (phaseTop_succ_le r t)

/-- Multiplicative form of the lower half of (5.7). -/
theorem phaseTop_scaled_lower
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) (n : ℕ) :
    phaseTop r t 1 ≤ 2 ^ n * phaseTop r t (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hhalf := phaseTop_le_two_mul_succ ht
        (j := n + 1) (by omega)
      have hhalf' : phaseTop r t (n + 1) ≤
          2 * phaseTop r t (n + 2) := by
        simpa only [show n + 1 + 1 = n + 2 by omega] using hhalf
      calc
        phaseTop r t 1 ≤ 2 ^ n * phaseTop r t (n + 1) := ih
        _ ≤ 2 ^ n * (2 * phaseTop r t (n + 2)) :=
          Nat.mul_le_mul_left _ hhalf'
        _ = 2 ^ (n + 1) * phaseTop r t (n + 1 + 1) := by
          simp only [pow_succ, show n + 1 + 1 = n + 2 by omega,
            Nat.mul_assoc]

/-- Multiplicative form of the upper half of (5.7). -/
theorem phaseTop_scaled_upper
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) (n : ℕ) :
    2 ^ n * phaseTop r t (n + 1) ≤
      phaseTop r t 1 + 2 * 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hround := two_mul_phaseTop_succ_le ht
        (j := n + 1) (by omega)
      have hround' : 2 * phaseTop r t (n + 2) ≤
          phaseTop r t (n + 1) + 2 := by
        simpa only [show n + 1 + 1 = n + 2 by omega] using hround
      calc
        2 ^ (n + 1) * phaseTop r t (n + 1 + 1) =
            2 ^ n * (2 * phaseTop r t (n + 2)) := by
          simp only [pow_succ, show n + 1 + 1 = n + 2 by omega,
            Nat.mul_assoc]
        _ ≤ 2 ^ n * (phaseTop r t (n + 1) + 2) :=
          Nat.mul_le_mul_left _ hround'
        _ = 2 ^ n * phaseTop r t (n + 1) + 2 * 2 ^ n := by
          simp [Nat.mul_add, Nat.mul_comm]
        _ ≤ (phaseTop r t 1 + 2 * 2 ^ n) + 2 * 2 ^ n :=
          Nat.add_le_add_right ih _
        _ = phaseTop r t 1 + 2 * 2 ^ (n + 1) := by
          rw [pow_succ]
          omega

/-- The lower quantitative endpoint in (5.8). -/
theorem three_mul_phaseWidth_le_finalTop
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    3 * phaseWidth t ≤ phaseTop r t (phaseCount r t) := by
  let K := phaseCount r t
  let p := 2 ^ (K - 1)
  have hK : 1 ≤ K := (phaseCount_spec ht).1
  have hscaled : phaseTop r t 1 ≤ p * phaseTop r t K := by
    have h := phaseTop_scaled_lower ht (K - 1)
    simpa [K, p, show K - 1 + 1 = K by omega] using h
  have hphase : phaseWidth t * p ≤ r / 4 := by
    simpa [K, p] using (phaseCount_spec ht).2.1
  have hleft : (3 * phaseWidth t) * p ≤ 3 * (r / 4) := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 3 hphase
  have hquarter : 3 * (r / 4) ≤ phaseTop r t 1 := by
    rw [phaseTop_one_eq_width ht]
    have h64 := sixtyFour_mul_phaseWidth_le ht
    have hc : 3 ≤ phaseWidth t := by simp [phaseWidth]
    omega
  have hprod : p * (3 * phaseWidth t) ≤
      p * phaseTop r t K := by
    rw [Nat.mul_comm p (3 * phaseWidth t)]
    exact hleft.trans (hquarter.trans hscaled)
  simpa only [K] using Nat.le_of_mul_le_mul_left hprod (by simp [p])

/-- The upper quantitative endpoint in (5.8). -/
theorem finalTop_le_eight_mul_phaseWidth_add_two
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    phaseTop r t (phaseCount r t) ≤ 8 * phaseWidth t + 2 := by
  let K := phaseCount r t
  let p := 2 ^ (K - 1)
  have hK : 1 ≤ K := (phaseCount_spec ht).1
  have hscaled : p * phaseTop r t K ≤ phaseTop r t 1 + 2 * p := by
    have h := phaseTop_scaled_upper ht (K - 1)
    simpa [K, p, show K - 1 + 1 = K by omega] using h
  have hpow : 2 ^ K = 2 * p := by
    dsimp [p]
    conv_lhs => rw [show K = K - 1 + 1 by omega, pow_succ]
    omega
  have hupper : r / 4 < 2 * (phaseWidth t * p) := by
    have h := (phaseCount_spec ht).2.2
    rw [hpow] at h
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  have hr : r < 8 * (phaseWidth t * p) := by omega
  have hu1 : phaseTop r t 1 ≤ r := by
    rw [phaseTop_one]
    exact (Nat.sub_le (anchorN r t) 4).trans (Nat.sub_le r (2 * t))
  have hprod : p * phaseTop r t K < p * (8 * phaseWidth t + 2) := by
    calc
      p * phaseTop r t K ≤ phaseTop r t 1 + 2 * p := hscaled
      _ ≤ r + 2 * p := Nat.add_le_add_right hu1 _
      _ < 8 * (phaseWidth t * p) + 2 * p := Nat.add_lt_add_right hr _
      _ = p * (8 * phaseWidth t + 2) := by
        simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
  simpa only [K] using (Nat.lt_of_mul_lt_mul_left hprod).le

theorem phaseTop_between_at_phase
    {r t j : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t) :
    3 * phaseWidth t ≤ phaseTop r t j ∧
      phaseTop r t j ≤ phaseTop r t 1 := by
  constructor
  · exact (three_mul_phaseWidth_le_finalTop ht).trans
      (antitone_phaseTop r t hjK)
  · exact antitone_phaseTop r t hj

theorem phaseTop_two_le_half_add_one
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    phaseTop r t 2 ≤ r / 2 + 1 := by
  have hround := two_mul_phaseTop_succ_le ht (j := 1) (by omega)
  have hu1 : phaseTop r t 1 ≤ r := by
    rw [phaseTop_one]
    exact (Nat.sub_le (anchorN r t) 4).trans (Nat.sub_le r (2 * t))
  have hround' : 2 * phaseTop r t 2 ≤ phaseTop r t 1 + 2 := by
    simpa only [show 1 + 1 = 2 by omega] using hround
  omega

theorem phaseTop_le_half_add_one_of_two_le
    {r t j : ℕ} (ht : IsMaximalAnchorIndex r t) (hj : 2 ≤ j) :
    phaseTop r t j ≤ r / 2 + 1 :=
  (antitone_phaseTop r t hj).trans (phaseTop_two_le_half_add_one ht)

theorem four_le_phaseTop_at_phase
    {r t j : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t) :
    4 ≤ phaseTop r t j := by
  have h := (phaseTop_between_at_phase ht hj hjK).1
  simp only [phaseWidth] at h
  omega

/-- `b_j`, defined so that the slot identity (5.6b) is visible by construction. -/
def phaseBirth (r t j : ℕ) : ℕ :=
  phaseTop r t j + t + j + 1

theorem phaseBirth_sub_phaseTop (r t j : ℕ) :
    phaseBirth r t j - phaseTop r t j = t + j + 1 := by
  unfold phaseBirth
  omega

theorem phaseBirth_one
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    phaseBirth r t 1 = r - t - 2 := by
  unfold phaseBirth
  rw [phaseTop_one_eq_width ht]
  have h64 := sixtyFour_mul_phaseWidth_le ht
  simp only [phaseWidth] at h64 ⊢
  omega

/-- A harvest lands exactly one level above the next phase birth. -/
theorem phaseBirth_succ
    {r t j : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t) :
    phaseBirth r t (j + 1) =
      phaseBirth r t j - phaseExtensionCount r t j - 1 := by
  have hu := four_le_phaseTop_at_phase ht hj hjK
  unfold phaseBirth
  rw [phaseTop_succ_eq_sub hj hu]
  have hell : phaseExtensionCount r t j + 2 ≤ phaseTop r t j := by
    by_cases hj1 : j = 1
    · subst j
      have hu5 := five_le_phaseTop_one ht
      simp only [phaseExtensionCount, if_pos]
      omega
    · simp only [phaseExtensionCount, if_neg hj1]
      omega
  omega

theorem phaseBirth_succ_add_one
    {r t j : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t) :
    phaseBirth r t (j + 1) + 1 =
      phaseBirth r t j - phaseExtensionCount r t j := by
  rw [phaseBirth_succ ht hj hjK]
  have hu := four_le_phaseTop_at_phase ht hj hjK
  have hell : phaseExtensionCount r t j + 1 ≤ phaseBirth r t j := by
    unfold phaseBirth
    by_cases hj1 : j = 1
    · subst j
      have hu5 := five_le_phaseTop_one ht
      simp only [phaseExtensionCount, if_pos]
      omega
    · simp only [phaseExtensionCount, if_neg hj1]
      omega
  omega

end Erdos776.Uniform


/-!
# Cascade states and ordinary in-phase transitions

The lists in this file are the active runs (6.0a)--(6.0b), not merely their
cardinalities.  The main transition lemma evaluates the actual canonical
Kruskal--Katona shadow through such a list and appends the new paying term.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

/-! ### Generic cascade transition lemmas -/

theorem length_diagonalDigits_of_le
    {a len : ℕ} (hlen : len ≤ a) :
    (diagonalDigits a len).length = len := by
  induction len generalizing a with
  | zero => rfl
  | succ len ih =>
      cases a with
      | zero => omega
      | succ a =>
          simp only [diagonalDigits_succ, List.length_cons]
          rw [ih (by omega)]

/-- Appending one term that has value at least `r` gives a supersolution step. -/
theorem cascade_append_pays
    {r k a : ℕ} {digits : List ℕ}
    (hcanon : IsCanonical k digits)
    (hpay : r ≤ a.choose (k - 1 - digits.length)) :
    r + canonicalShadow k (cascadeValue k digits) ≤
      cascadeValue (k - 1) (digits ++ [a]) := by
  rw [canonicalShadow_eq_cascadeShadowValue hcanon rfl]
  unfold cascadeShadowValue
  rw [cascadeValue_append]
  simp only [cascadeValue_cons, cascadeValue_nil, Nat.add_zero]
  omega

/-- A descending partial run is dominated, after shadowing, by its completion. -/
theorem diagonalRun_shadow_le_completion
    {s p len : ℕ} (hp : 1 ≤ p) (hlen : len ≤ p) (hps : p < s) :
    cascadeShadowValue p (diagonalDigits (s - 1) len) ≤
      s.choose (p - 1) := by
  have hspos : 1 ≤ s := by omega
  have hcanonTop : IsCanonical (s - 1)
      (diagonalDigits (s - 1) len) :=
    isCanonical_diagonalDigits (by omega)
  have hcanon : IsCanonical p (diagonalDigits (s - 1) len) :=
    hcanonTop.lowerIndex (by omega) (by
      rw [length_diagonalDigits_of_le (by omega)]
      exact hlen)
  have hall : ∀ d ∈ diagonalDigits (s - 1) len, d < s := by
    intro d hd
    exact (mem_diagonalDigits_le hd).trans_lt (by omega)
  have hvalue : cascadeValue p (diagonalDigits (s - 1) len) <
      s.choose p :=
    cascadeValue_lt_choose_of_all_lt (by omega) hcanon hall
  have hmono := canonicalShadow_mono p hp hvalue.le
  rw [canonicalShadow_eq_cascadeShadowValue hcanon rfl,
    canonicalShadow_choose hp (by omega)] at hmono
  exact hmono

/--
Complete an old descending run to the digit `s`; a newborn term `a` then
pays the incoming load.  This is the abstract hockey-stick harvest argument.
-/
theorem cascade_harvest_pays
    {r k s a len : ℕ} {fixed : List ℕ}
    (hcanon : IsCanonical k (fixed ++ diagonalDigits (s - 1) len))
    (hfixed : fixed.length + 2 ≤ k)
    (hlen : len ≤ k - fixed.length)
    (hstone : k - fixed.length < s)
    (hpay : r ≤ a.choose (k - fixed.length - 2)) :
    r + canonicalShadow k
        (cascadeValue k (fixed ++ diagonalDigits (s - 1) len)) ≤
      cascadeValue (k - 1) (fixed ++ [s, a]) := by
  rw [canonicalShadow_eq_cascadeShadowValue hcanon rfl]
  unfold cascadeShadowValue
  rw [cascadeValue_append, cascadeValue_append]
  have hp : 1 ≤ k - fixed.length := by omega
  have hcomplete := diagonalRun_shadow_le_completion
    hp hlen hstone
  simp only [cascadeValue_cons, cascadeValue_nil, Nat.add_zero]
  have hidx1 : k - 1 - fixed.length = k - fixed.length - 1 := by omega
  have hidx2 : k - fixed.length - 1 - 1 =
      k - fixed.length - 2 := by omega
  rw [hidx1, hidx2]
  change cascadeValue (k - fixed.length - 1)
      (diagonalDigits (s - 1) len) ≤ s.choose (k - fixed.length - 1)
    at hcomplete
  omega

/-! ### The displayed phase states -/

/-- The already-completed tower stones `s₁,...,s_count`. -/
def towerDigits (r t : ℕ) : ℕ → List ℕ
  | 0 => []
  | count + 1 => towerDigits r t count ++ [towerStone r t (count + 1)]

@[simp] theorem length_towerDigits (r t count : ℕ) :
    (towerDigits r t count).length = count := by
  induction count with
  | zero => rfl
  | succ count ih => simp [towerDigits, ih]

theorem towerDigits_succ (r t count : ℕ) :
    towerDigits r t (count + 1) =
      towerDigits r t count ++ [towerStone r t (count + 1)] := rfl

/-- A useful list form of extending a descending digit run by one place. -/
theorem diagonalDigits_add_one (a len : ℕ) :
    diagonalDigits a (len + 1) =
      diagonalDigits a len ++ [a - len] := by
  induction len generalizing a with
  | zero => simp
  | succ len ih =>
      change a :: diagonalDigits (a - 1) (len + 1) =
        (a :: diagonalDigits (a - 1) len) ++ [a - (len + 1)]
      rw [List.cons_append, ih]
      congr 2
      simp [Nat.sub_sub, Nat.add_comm]

/-- Number of active terms after `L` extensions in phase `j`. -/
def phaseRunLength (j L : ℕ) : ℕ :=
  if j = 1 then L + 2 else L + 1

/-- The active run `R_{j,L}` from (6.0a)--(6.0b), represented by its digits. -/
def phaseRunDigits (r t j L : ℕ) : List ℕ :=
  diagonalDigits (towerStone r t j - 1) (phaseRunLength j L)

@[simp] theorem length_phaseRunDigits
    {r t j L : ℕ} (hlen : phaseRunLength j L ≤ towerStone r t j - 1) :
    (phaseRunDigits r t j L).length = phaseRunLength j L := by
  unfold phaseRunDigits
  exact length_diagonalDigits_of_le hlen

/-- The new digit appended by the next in-phase extension. -/
def phaseExtensionDigit (r t j L : ℕ) : ℕ :=
  if j = 1 then towerStone r t j - 3 - L
  else towerStone r t j - 2 - L

/-- Its lower binomial index, as displayed in (6.1) and (6.3). -/
def phaseExtensionIndex (r t j L : ℕ) : ℕ :=
  if j = 1 then phaseTop r t j - 3 - 2 * L
  else phaseTop r t j - 2 - 2 * L

theorem phaseRunDigits_succ (r t j L : ℕ) :
    phaseRunDigits r t j (L + 1) =
      phaseRunDigits r t j L ++ [phaseExtensionDigit r t j L] := by
  by_cases hj1 : j = 1
  · subst j
    simp only [phaseRunDigits, phaseRunLength, if_pos, phaseExtensionDigit]
    rw [show L + 1 + 2 = (L + 2) + 1 by omega,
      diagonalDigits_add_one]
    congr 2
    simp [Nat.sub_sub, Nat.add_comm, Nat.add_left_comm]
  · simp only [phaseRunDigits, phaseRunLength, if_neg hj1,
      phaseExtensionDigit]
    rw [show L + 1 + 1 = (L + 1) + 1 by omega,
      diagonalDigits_add_one]
    congr 2
    simp [Nat.sub_sub, Nat.add_comm, Nat.add_left_comm]

/-- Digits that remain fixed during phase `j`. -/
def phaseFixedDigits (r t j : ℕ) : List ℕ :=
  anchorHeadDigits r (t + 1) ++ towerDigits r t (j - 1)

@[simp] theorem length_phaseFixedDigits (r t j : ℕ) :
    (phaseFixedDigits r t j).length = t + 2 + (j - 1) := by
  simp [phaseFixedDigits]

/-- The complete digit list at level `b_j-L`. -/
def phaseDigits (r t j L : ℕ) : List ℕ :=
  phaseFixedDigits r t j ++ phaseRunDigits r t j L

/-- The numerical state represented by the displayed phase cascade. -/
def phaseState (r t j L : ℕ) : ℕ :=
  cascadeValue (phaseBirth r t j - L) (phaseDigits r t j L)

theorem phaseDigits_succ (r t j L : ℕ) :
    phaseDigits r t j (L + 1) =
      phaseDigits r t j L ++ [phaseExtensionDigit r t j L] := by
  unfold phaseDigits
  rw [phaseRunDigits_succ]
  simp [List.append_assoc]

theorem phaseExtensionIndex_four_le
    {r t j L : ℕ} (_ht : IsMaximalAnchorIndex r t)
    (_hj : 1 ≤ j) (_hjK : j ≤ phaseCount r t)
    (hL : L < phaseExtensionCount r t j) :
    4 ≤ phaseExtensionIndex r t j L := by
  unfold phaseExtensionIndex
  unfold phaseExtensionCount at hL
  by_cases hj1 : j = 1
  · simp only [hj1, if_pos] at hL ⊢
    omega
  · simp only [if_neg hj1] at hL ⊢
    omega

theorem phaseRunLength_le_stone
    {r t j L : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t)
    (hL : L ≤ phaseExtensionCount r t j) :
    phaseRunLength j L ≤ towerStone r t j - 1 := by
  have hu := (phaseTop_between_at_phase ht hj hjK).2
  have hs := towerStone_phase_lower ht hj hjK
  unfold phaseRunLength
  unfold phaseExtensionCount at hL
  by_cases hj1 : j = 1
  · subst j
    simp at hL
    simp only [if_pos]
    have hu1 := five_le_phaseTop_one ht
    have hstone : towerStone r t 1 = phaseTop r t 1 + 2 := by
      rw [first_towerStone_eq]
      simp only [phaseTop_one]
      rw [phaseTop_one] at hu1
      omega
    rw [hstone]
    rw [phaseTop_one]
    rw [phaseTop_one] at hu1
    omega
  · simp only [if_neg hj1] at hL ⊢
    have hj2 : 2 ≤ j := by omega
    have huHalf := phaseTop_le_half_add_one_of_two_le ht hj2
    have h64 := sixtyFour_mul_phaseWidth_le ht
    have hc : 3 ≤ phaseWidth t := by simp [phaseWidth]
    omega

theorem phaseExtension_actual_index
    {r t j L : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t)
    (hL : L < phaseExtensionCount r t j) :
    phaseBirth r t j - L - 1 - (phaseDigits r t j L).length =
      phaseExtensionIndex r t j L := by
  have hrun := phaseRunLength_le_stone ht hj hjK hL.le
  unfold phaseDigits
  rw [List.length_append, length_phaseFixedDigits,
    length_phaseRunDigits hrun]
  unfold phaseBirth phaseRunLength phaseExtensionIndex
  by_cases hj1 : j = 1
  · subst j
    simp only [if_pos]
    omega
  · simp only [if_neg hj1]
    omega

/-- One actual in-phase cascade transition from Section 6. -/
theorem phase_extension_pays
    {r t j L : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t)
    (hL : L < phaseExtensionCount r t j)
    (hcanon : IsCanonical (phaseBirth r t j - L) (phaseDigits r t j L))
    (hpay : r ≤ (phaseExtensionDigit r t j L).choose
      (phaseExtensionIndex r t j L)) :
    r + canonicalShadow (phaseBirth r t j - L) (phaseState r t j L) ≤
      phaseState r t j (L + 1) := by
  have hindex := phaseExtension_actual_index ht hj hjK hL
  have hidx4 := phaseExtensionIndex_four_le ht hj hjK hL
  have hlevel : phaseBirth r t j - (L + 1) =
      phaseBirth r t j - L - 1 := by
    have : L + 1 ≤ phaseBirth r t j := by
      have hnonneg : 4 ≤ phaseBirth r t j - L - 1 := by
        have hsub : phaseBirth r t j - L - 1 -
            (phaseDigits r t j L).length ≤ phaseBirth r t j - L - 1 :=
          Nat.sub_le _ _
        rw [hindex] at hsub
        exact hidx4.trans hsub
      omega
    omega
  unfold phaseState
  rw [phaseDigits_succ, hlevel]
  apply cascade_append_pays hcanon
  rw [hindex]
  exact hpay

end Erdos776.Uniform


/-!
# Quantitative bounds for ordinary phase terms

This file supplies the binomial estimates from Lemma 5.1 and Section 6.  The
proof is uniform in `r`; no finite numerical scan is imported.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

/-- Binomial coefficients increase in the lower index up to the midpoint. -/
theorem choose_mono_right_of_le_half
    {n a b : ℕ} (hab : a ≤ b) (hb : b ≤ n / 2) :
    n.choose a ≤ n.choose b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
      exact (ih (by omega)).trans
        (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- Away from both endpoints, `choose d k` is at least `choose d 2`. -/
theorem choose_two_le_choose_of_interior
    {d k : ℕ} (hk : 2 ≤ k) (hcomp : k + 2 ≤ d) :
    d.choose 2 ≤ d.choose k := by
  have hkd : k ≤ d := by omega
  by_cases hkhalf : k ≤ d / 2
  · exact choose_mono_right_of_le_half hk hkhalf
  · have hcompHalf : d - k ≤ d / 2 := by omega
    have hcompTwo : 2 ≤ d - k := by omega
    rw [← Nat.choose_symm hkd]
    exact choose_mono_right_of_le_half hcompTwo hcompHalf

/-- A convenient linear lower bound for triangular numbers. -/
theorem five_mul_le_choose_two :
    ∀ d : ℕ, 11 ≤ d → 5 * d ≤ d.choose 2 := by
  intro d hd
  induction d with
  | zero => omega
  | succ d ih =>
      by_cases hd11 : 11 ≤ d
      · have hprev := ih hd11
        rw [show (d + 1).choose 2 = d.choose 1 + d.choose 2 by
          simpa using Nat.choose_succ_succ d 1]
        simp only [Nat.choose_one_right]
        omega
      · have hd10 : d = 10 := by omega
        subst d
        norm_num [Nat.choose_two_right]

/-- For `r ≥ 378`, even the quarter-scale endpoint binomial exceeds `r`. -/
theorem r_lt_choose_quarter_sub_one
    {r : ℕ} (hr : 378 ≤ r) :
    r < (r / 4 - 1).choose 2 := by
  let d := r / 4 - 1
  have hd : 11 ≤ d := by
    dsimp [d]
    omega
  have hfive := five_mul_le_choose_two d hd
  have hrfive : r < 5 * d := by
    dsimp [d]
    omega
  exact hrfive.trans_le hfive

/-- A term with both indices at least two and a quarter-scale digit pays `r`. -/
theorem binomial_pays_of_quarter_digit
    {r d k : ℕ} (hr : 378 ≤ r)
    (hd : r / 4 - 1 ≤ d) (hk : 2 ≤ k) (hcomp : k + 2 ≤ d) :
    r ≤ d.choose k := by
  have hquarter := r_lt_choose_quarter_sub_one hr
  have hfirst : (r / 4 - 1).choose 2 ≤ d.choose 2 :=
    Nat.choose_le_choose 2 hd
  have hsecond := choose_two_le_choose_of_interior hk hcomp
  exact hquarter.le.trans (hfirst.trans hsecond)

theorem phaseExtensionDigit_quarter_lower
    {r t j L : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t)
    (hL : L < phaseExtensionCount r t j) :
    r / 4 - 1 ≤ phaseExtensionDigit r t j L := by
  unfold phaseExtensionDigit
  unfold phaseExtensionCount at hL
  by_cases hj1 : j = 1
  · subst j
    simp only [if_pos] at hL ⊢
    have hu := five_le_phaseTop_one ht
    have hstone : towerStone r t 1 = phaseTop r t 1 + 2 := by
      rw [first_towerStone_eq]
      simp only [phaseTop_one]
      have hu := five_le_phaseTop_one ht
      rw [phaseTop_one] at hu
      omega
    rw [hstone]
    have hueq := phaseTop_one_eq_width ht
    have h64 := sixtyFour_mul_phaseWidth_le ht
    omega
  · simp only [if_neg hj1] at hL ⊢
    have hj2 : 2 ≤ j := by omega
    have hu := phaseTop_le_half_add_one_of_two_le ht hj2
    have hs := towerStone_phase_lower ht hj hjK
    omega

theorem phaseExtensionIndex_add_two_le_digit
    {r t j L : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t)
    (hL : L < phaseExtensionCount r t j) :
    phaseExtensionIndex r t j L + 2 ≤ phaseExtensionDigit r t j L := by
  unfold phaseExtensionDigit phaseExtensionIndex
  unfold phaseExtensionCount at hL
  by_cases hj1 : j = 1
  · subst j
    simp only [if_pos] at hL ⊢
    have hu := five_le_phaseTop_one ht
    have hstone : towerStone r t 1 = phaseTop r t 1 + 2 := by
      rw [first_towerStone_eq]
      simp only [phaseTop_one]
      rw [phaseTop_one] at hu
      omega
    rw [hstone]
    omega
  · simp only [if_neg hj1] at hL ⊢
    have hj2 : 2 ≤ j := by omega
    have hu := phaseTop_le_half_add_one_of_two_le ht hj2
    have hs := towerStone_phase_lower ht hj hjK
    omega

/-- Every displayed in-phase extension term pays the full incoming load. -/
theorem phaseExtension_binomial_pays
    {r t j L : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t)
    (hL : L < phaseExtensionCount r t j) :
    r ≤ (phaseExtensionDigit r t j L).choose
      (phaseExtensionIndex r t j L) := by
  apply binomial_pays_of_quarter_digit hr
  · exact phaseExtensionDigit_quarter_lower hr ht hj hjK hL
  · exact (phaseExtensionIndex_four_le ht hj hjK hL).trans' (by omega)
  · exact phaseExtensionIndex_add_two_le_digit hr ht hj hjK hL

/-- The in-phase transition with its quantitative payment discharged. -/
theorem phase_extension_valid
    {r t j L : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t)
    (hL : L < phaseExtensionCount r t j)
    (hcanon : IsCanonical (phaseBirth r t j - L) (phaseDigits r t j L)) :
    r + canonicalShadow (phaseBirth r t j - L) (phaseState r t j L) ≤
      phaseState r t j (L + 1) :=
  phase_extension_pays ht hj hjK hL hcanon
    (phaseExtension_binomial_pays hr ht hj hjK hL)

end Erdos776.Uniform


/-!
# Ordinary phase harvests

At a harvest the old diagonal run is completed to `s_j`, while the first
term of phase `j+1` pays the incoming load.  The theorem below identifies
both sides with the explicit phase cascades, including the exceptional
length of phase one.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

theorem phaseFixedDigits_succ
    {r t j : ℕ} (hj : 1 ≤ j) :
    phaseFixedDigits r t (j + 1) =
      phaseFixedDigits r t j ++ [towerStone r t j] := by
  unfold phaseFixedDigits
  rw [show j + 1 - 1 = (j - 1) + 1 by omega,
    towerDigits_succ, show j - 1 + 1 = j by omega]
  simp [List.append_assoc]

theorem phaseRunDigits_next_zero
    {r t j : ℕ} (hj : 1 ≤ j) :
    phaseRunDigits r t (j + 1) 0 = [towerStone r t (j + 1) - 1] := by
  unfold phaseRunDigits phaseRunLength
  simp only [if_neg (show j + 1 ≠ 1 by omega)]
  rfl

theorem phaseDigits_next_zero
    {r t j : ℕ} (hj : 1 ≤ j) :
    phaseDigits r t (j + 1) 0 =
      phaseFixedDigits r t j ++
        [towerStone r t j, towerStone r t (j + 1) - 1] := by
  unfold phaseDigits
  rw [phaseFixedDigits_succ hj, phaseRunDigits_next_zero hj]
  simp [List.append_assoc]

theorem phase_harvest_active_index
    {r t j : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t) :
    phaseBirth r t j - phaseExtensionCount r t j -
        (phaseFixedDigits r t j).length =
      phaseTop r t j - phaseExtensionCount r t j := by
  rw [length_phaseFixedDigits]
  unfold phaseBirth
  have hu := four_le_phaseTop_at_phase ht hj hjK
  omega

theorem phaseRunLength_le_active_at_harvest
    {r t j : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t) :
    phaseRunLength j (phaseExtensionCount r t j) ≤
      phaseTop r t j - phaseExtensionCount r t j := by
  have hu := four_le_phaseTop_at_phase ht hj hjK
  unfold phaseRunLength phaseExtensionCount
  by_cases hj1 : j = 1
  · simp only [hj1, if_pos]
    have hu5 := five_le_phaseTop_one ht
    simpa only [hj1] using (show
      (phaseTop r t 1 - 5) / 2 + 2 ≤
        phaseTop r t 1 - (phaseTop r t 1 - 5) / 2 by omega)
  · simp only [if_neg hj1]
    omega

theorem phase_harvest_active_lt_stone
    {r t j : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t) :
    phaseTop r t j - phaseExtensionCount r t j < towerStone r t j := by
  by_cases hj1 : j = 1
  · subst j
    have hu := five_le_phaseTop_one ht
    have hstone : towerStone r t 1 = phaseTop r t 1 + 2 := by
      rw [first_towerStone_eq]
      simp only [phaseTop_one]
      rw [phaseTop_one] at hu
      omega
    rw [hstone]
    omega
  · have hj2 : 2 ≤ j := by omega
    have hu := phaseTop_le_half_add_one_of_two_le ht hj2
    have hs := towerStone_phase_lower ht hj hjK
    omega

/-- The newborn active term at an ordinary harvest pays `r` by itself. -/
theorem newborn_binomial_pays
    {r t j : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 2 ≤ j) (hjK : j ≤ phaseCount r t) :
    r ≤ (towerStone r t j - 1).choose (phaseTop r t j) := by
  apply binomial_pays_of_quarter_digit hr
  · have hs := towerStone_phase_lower ht (by omega) hjK
    omega
  · have hu := four_le_phaseTop_at_phase ht (by omega) hjK
    omega
  · have hu := phaseTop_le_half_add_one_of_two_le ht hj
    have hs := towerStone_phase_lower ht (by omega) hjK
    omega

theorem phase_harvest_newborn_index
    {r t j : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t) :
    phaseBirth r t j - phaseExtensionCount r t j -
        (phaseFixedDigits r t j).length - 2 =
      phaseTop r t (j + 1) := by
  rw [phase_harvest_active_index ht hj hjK,
    phaseTop_succ_eq_sub hj (four_le_phaseTop_at_phase ht hj hjK)]

/--
The ordinary harvest transition, with both the hockey-stick completion and
the newborn payment discharged.  It is used for `j+1 ≤ K`; the manuscript
replaces the last such ordinary birth by the one-digit final zone.
-/
theorem phase_harvest_valid
    {r t j : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j + 1 ≤ phaseCount r t)
    (hcanon : IsCanonical
      (phaseBirth r t j - phaseExtensionCount r t j)
      (phaseDigits r t j (phaseExtensionCount r t j))) :
    r + canonicalShadow
        (phaseBirth r t j - phaseExtensionCount r t j)
        (phaseState r t j (phaseExtensionCount r t j)) ≤
      phaseState r t (j + 1) 0 := by
  let ell := phaseExtensionCount r t j
  let k := phaseBirth r t j - ell
  let fixed := phaseFixedDigits r t j
  let s := towerStone r t j
  let a := towerStone r t (j + 1) - 1
  have hjK' : j ≤ phaseCount r t := by omega
  have hactive := phase_harvest_active_index ht hj hjK'
  have hrun := phaseRunLength_le_active_at_harvest ht hj hjK'
  have hactiveLt := phase_harvest_active_lt_stone hr ht hj hjK'
  have hindex := phase_harvest_newborn_index ht hj hjK'
  have hpay := newborn_binomial_pays hr ht (show 2 ≤ j + 1 by omega) hjK
  have hfixed : fixed.length + 2 ≤ k := by
    dsimp [fixed, k, ell]
    have hu := four_le_phaseTop_at_phase ht hj hjK'
    rw [length_phaseFixedDigits]
    unfold phaseBirth phaseExtensionCount
    by_cases hj1 : j = 1
    · simp only [hj1, if_pos]
      have hu5 := five_le_phaseTop_one ht
      omega
    · simp only [if_neg hj1]
      omega
  have hgeneric : r + canonicalShadow k
      (cascadeValue k (fixed ++ diagonalDigits (s - 1)
        (phaseRunLength j ell))) ≤
      cascadeValue (k - 1) (fixed ++ [s, a]) := by
    apply cascade_harvest_pays hcanon hfixed
    · rw [hactive]
      exact hrun
    · rw [hactive]
      exact hactiveLt
    · change r ≤ (towerStone r t (j + 1) - 1).choose
        (phaseBirth r t j - phaseExtensionCount r t j -
          (phaseFixedDigits r t j).length - 2)
      rw [hindex]
      exact hpay
  have hbirth : phaseBirth r t (j + 1) = k - 1 := by
    dsimp [k, ell]
    exact phaseBirth_succ ht hj hjK'
  unfold phaseState
  rw [phaseDigits_next_zero hj]
  unfold phaseDigits phaseRunDigits
  change r + canonicalShadow k
      (cascadeValue k (fixed ++ diagonalDigits (s - 1)
        (phaseRunLength j ell))) ≤
    cascadeValue (phaseBirth r t (j + 1)) (fixed ++ [s, a])
  rw [hbirth]
  exact hgeneric

end Erdos776.Uniform


/-!
# Canonicity of the displayed phase cascades

The transition lemmas evaluate `canonicalShadow` through the displayed digit
lists.  This file proves that the first phase is canonical and that every
in-phase extension preserves canonicity.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

theorem isCanonical_pairwise_gt
    {k : ℕ} {digits : List ℕ} (h : IsCanonical k digits) :
    digits.Pairwise (· > ·) := by
  induction digits generalizing k with
  | nil => simp
  | cons a digits ih =>
      cases k with
      | zero => simp at h
      | succ k =>
          simp only [isCanonical_succ_cons] at h
          simp only [List.pairwise_cons]
          exact ⟨h.2.1, ih h.2.2⟩

/-- Lower a canonical list one level and append a digit below its old last digit. -/
theorem isCanonical_lower_append_after_last
    {k last a : ℕ} {init : List ℕ}
    (hcanon : IsCanonical k (init ++ [last]))
    (hlen : (init ++ [last]).length ≤ k - 1)
    (hindex : 1 ≤ k - 1 - (init ++ [last]).length)
    (hvalid : k - 1 - (init ++ [last]).length ≤ a)
    (ha : a < last) :
    IsCanonical (k - 1) ((init ++ [last]) ++ [a]) := by
  have hlower : IsCanonical (k - 1) (init ++ [last]) :=
    hcanon.lowerIndex (by omega) hlen
  have hsingle : IsCanonical (k - 1 - (init ++ [last]).length) [a] :=
    isCanonical_singleton hindex hvalid
  apply isCanonical_append hlower hsingle
  intro d hd b hb
  simp only [List.mem_singleton] at hb
  subst b
  rcases List.mem_append.mp hd with hd | hd
  · have hp := isCanonical_pairwise_gt hcanon
    simp only [List.pairwise_append, List.pairwise_singleton,
      List.mem_singleton, forall_eq] at hp
    exact ha.trans (hp.2.2 d hd)
  · simp only [List.mem_singleton] at hd
    subst d
    exact ha

/-- The part of the current run before its last digit. -/
def phaseRunInitLength (j L : ℕ) : ℕ :=
  if j = 1 then L + 1 else L

def phasePreviousDigit (r t j L : ℕ) : ℕ :=
  towerStone r t j - 1 - phaseRunInitLength j L

theorem phaseRunLength_eq_init_add_one (j L : ℕ) :
    phaseRunLength j L = phaseRunInitLength j L + 1 := by
  unfold phaseRunLength phaseRunInitLength
  split <;> omega

theorem phaseDigits_eq_append_previous (r t j L : ℕ) :
    phaseDigits r t j L =
      (phaseFixedDigits r t j ++
        diagonalDigits (towerStone r t j - 1)
          (phaseRunInitLength j L)) ++
        [phasePreviousDigit r t j L] := by
  unfold phaseDigits phaseRunDigits phasePreviousDigit
  rw [phaseRunLength_eq_init_add_one, diagonalDigits_add_one]
  simp [List.append_assoc]

theorem phaseExtensionDigit_lt_previous
    {r t j L : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t)
    (hL : L < phaseExtensionCount r t j) :
    phaseExtensionDigit r t j L < phasePreviousDigit r t j L := by
  have hpos := phaseExtensionDigit_quarter_lower hr ht hj hjK hL
  unfold phaseExtensionDigit at hpos
  unfold phaseExtensionDigit phasePreviousDigit phaseRunInitLength
  by_cases hj1 : j = 1
  · simp only [hj1, if_pos] at hpos ⊢
    omega
  · simp only [if_neg hj1] at hpos ⊢
    omega

theorem phase_one_birth_index_after_anchors
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    phaseBirth r t 1 - (anchorHeadDigits r (t + 1)).length =
      phaseTop r t 1 := by
  rw [length_anchorHeadDigits, phaseBirth_one ht]
  have h64 := sixtyFour_mul_phaseWidth_le ht
  simp only [phaseWidth] at h64
  simp only [phaseTop_one, anchorN]
  omega

/-- The two-term state (4.2), i.e. phase one at birth, is canonical. -/
theorem isCanonical_phase_one_birth
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    IsCanonical (phaseBirth r t 1) (phaseDigits r t 1 0) := by
  have h64 := sixtyFour_mul_phaseWidth_le ht
  simp only [phaseWidth] at h64
  have hanchorTop := isCanonical_anchorHeadDigits
    (r := r) (q := t + 1) (show 2 * (t + 1) + 2 ≤ r by
      have hc : 3 ≤ phaseWidth t := by simp [phaseWidth]
      omega)
  have hbirth : phaseBirth r t 1 = r - t - 2 := phaseBirth_one ht
  have hanchorLen : (anchorHeadDigits r (t + 1)).length ≤
      phaseBirth r t 1 := by
    rw [length_anchorHeadDigits, hbirth]
    omega
  have hanchor : IsCanonical (phaseBirth r t 1)
      (anchorHeadDigits r (t + 1)) := by
    apply hanchorTop.lowerIndex
    · rw [hbirth]
      omega
    · exact hanchorLen
  have hu := five_le_phaseTop_one ht
  have hstone : towerStone r t 1 = phaseTop r t 1 + 2 := by
    rw [first_towerStone_eq]
    simp only [phaseTop_one]
    rw [phaseTop_one] at hu
    omega
  have hrunTop : IsCanonical (towerStone r t 1 - 1)
      (diagonalDigits (towerStone r t 1 - 1) 2) :=
    isCanonical_diagonalDigits (by omega)
  have hrun : IsCanonical (phaseBirth r t 1 -
      (anchorHeadDigits r (t + 1)).length)
      (diagonalDigits (towerStone r t 1 - 1) 2) := by
    rw [phase_one_birth_index_after_anchors ht]
    apply hrunTop.lowerIndex
    · rw [hstone]
      omega
    · rw [length_diagonalDigits_of_le (by omega)]
      omega
  have hcross : ∀ a ∈ anchorHeadDigits r (t + 1),
      ∀ b ∈ diagonalDigits (towerStone r t 1 - 1) 2, b < a := by
    intro a ha b hb
    obtain ⟨q, hq, rfl⟩ := mem_anchorHeadDigits
      (q := t + 1) (by omega) ha
    have hbLe := mem_diagonalDigits_le hb
    have hbN : b < anchorN r t := by
      rw [first_towerStone_eq] at hbLe
      have hN : 5 ≤ anchorN r t := by
        have hu' := five_le_phaseTop_one ht
        rw [phaseTop_one] at hu'
        omega
      omega
    have hNa : anchorN r t ≤ r + 2 - 2 * q := by
      unfold anchorN
      omega
    exact hbN.trans_le hNa
  have hfull := isCanonical_append hanchor hrun hcross
  unfold phaseDigits phaseFixedDigits phaseRunDigits phaseRunLength
  simp [towerDigits]
  exact hfull

/-- Every legal in-phase extension preserves canonicity. -/
theorem isCanonical_phase_extension
    {r t j L : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t)
    (hL : L < phaseExtensionCount r t j)
    (hcanon : IsCanonical (phaseBirth r t j - L) (phaseDigits r t j L)) :
    IsCanonical (phaseBirth r t j - (L + 1))
      (phaseDigits r t j (L + 1)) := by
  let k := phaseBirth r t j - L
  let init := phaseFixedDigits r t j ++
    diagonalDigits (towerStone r t j - 1) (phaseRunInitLength j L)
  let last := phasePreviousDigit r t j L
  let a := phaseExtensionDigit r t j L
  have hdecomp := phaseDigits_eq_append_previous r t j L
  have hcanon' : IsCanonical k (init ++ [last]) := by
    dsimp [k, init, last]
    rw [← hdecomp]
    exact hcanon
  have hindexEq := phaseExtension_actual_index ht hj hjK hL
  have hindex4 := phaseExtensionIndex_four_le ht hj hjK hL
  have hlen : (init ++ [last]).length ≤ k - 1 := by
    have hpos : 0 < k - 1 - (phaseDigits r t j L).length := by
      rw [hindexEq]
      omega
    have hlenPhase : (phaseDigits r t j L).length ≤ k - 1 :=
      (Nat.sub_pos_iff_lt.mp hpos).le
    dsimp [init, last, k]
    rw [← hdecomp]
    exact hlenPhase
  have hactual : k - 1 - (init ++ [last]).length =
      phaseExtensionIndex r t j L := by
    dsimp [k, init, last]
    rw [← hdecomp]
    exact hindexEq
  have hvalid := phaseExtensionIndex_add_two_le_digit hr ht hj hjK hL
  have ha := phaseExtensionDigit_lt_previous hr ht hj hjK hL
  have hnext := isCanonical_lower_append_after_last hcanon' hlen
    (by rw [hactual]; omega) (by rw [hactual]; omega) ha
  have hlevel : phaseBirth r t j - (L + 1) = k - 1 := by
    have : L + 1 ≤ phaseBirth r t j := by
      have hnonneg : 4 ≤ k - 1 := by
        exact hindex4.trans (by
          rw [← hindexEq]
          exact Nat.sub_le _ _)
      dsimp [k] at hnonneg
      omega
    dsimp [k]
    omega
  rw [phaseDigits_succ, hlevel]
  dsimp [init, last, a] at hnext
  rw [← hdecomp] at hnext
  exact hnext

/-! ### Canonicity across a harvest -/

theorem isCanonical_append_left
    {k : ℕ} {xs ys : List ℕ} (h : IsCanonical k (xs ++ ys)) :
    IsCanonical k xs := by
  induction xs generalizing k with
  | nil => simp
  | cons a xs ih =>
      cases k with
      | zero => simp at h
      | succ k =>
          simp only [List.cons_append, isCanonical_succ_cons] at h ⊢
          refine ⟨h.1, ?_, ih h.2.2⟩
          intro b hb
          exact h.2.1 b (List.mem_append_left ys hb)

theorem mem_towerDigits
    {r t count d : ℕ} (hd : d ∈ towerDigits r t count) :
    ∃ q, 1 ≤ q ∧ q ≤ count ∧ d = towerStone r t q := by
  induction count with
  | zero => simp [towerDigits] at hd
  | succ count ih =>
      rw [towerDigits_succ] at hd
      rcases List.mem_append.mp hd with hd | hd
      · obtain ⟨q, hq1, hqCount, rfl⟩ := ih hd
        exact ⟨q, hq1, by omega, rfl⟩
      · simp only [List.mem_singleton] at hd
        exact ⟨count + 1, by omega, le_rfl, hd⟩

theorem towerStone_anti_of_le
    {r t q j : ℕ} (hq : 1 ≤ q) (hqj : q ≤ j) :
    towerStone r t j ≤ towerStone r t q := by
  have hexp : q - 1 ≤ j - 1 := by omega
  have hpow : 2 ^ (q - 1) ≤ 2 ^ (j - 1) :=
    pow_le_pow_right' (by omega) hexp
  have hmul : phaseWidth t * 2 ^ (q - 1) ≤
      phaseWidth t * 2 ^ (j - 1) := Nat.mul_le_mul_left _ hpow
  unfold towerStone
  omega

theorem towerStone_strict_of_lt
    {r t q j : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hq : 1 ≤ q) (hqj : q < j) (hjK : j ≤ phaseCount r t) :
    towerStone r t j < towerStone r t q := by
  have hexp : q - 1 < j - 1 := by omega
  have hpow : 2 ^ (q - 1) < 2 ^ (j - 1) :=
    Nat.pow_lt_pow_right (by omega) hexp
  have hc : 0 < phaseWidth t := by simp [phaseWidth]
  have hmul : phaseWidth t * 2 ^ (q - 1) <
      phaseWidth t * 2 ^ (j - 1) :=
    (Nat.mul_lt_mul_left hc).2 hpow
  have hjpos : 1 ≤ j := by omega
  have hexpK : j - 1 ≤ phaseCount r t - 1 := by omega
  have hpowK : 2 ^ (j - 1) ≤ 2 ^ (phaseCount r t - 1) :=
    pow_le_pow_right' (by omega) hexpK
  have hdist : phaseWidth t * 2 ^ (j - 1) ≤ r / 4 :=
    (Nat.mul_le_mul_left _ hpowK).trans (phaseCount_spec ht).2.1
  unfold towerStone
  omega

theorem phaseFixed_digit_gt_stone
    {r t j d : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t)
    (hd : d ∈ phaseFixedDigits r t j) :
    towerStone r t j < d := by
  rcases List.mem_append.mp hd with hd | hd
  · obtain ⟨q, hq, rfl⟩ := mem_anchorHeadDigits
      (q := t + 1) (by
        have h64 := sixtyFour_mul_phaseWidth_le ht
        simp [phaseWidth] at h64
        omega) hd
    have hstoneFirst : towerStone r t j ≤ towerStone r t 1 :=
      towerStone_anti_of_le (by omega) hj
    rw [first_towerStone_eq] at hstoneFirst
    unfold anchorN at hstoneFirst
    have h64 := sixtyFour_mul_phaseWidth_le ht
    simp only [phaseWidth] at h64
    omega
  · obtain ⟨q, hq1, hqCount, rfl⟩ := mem_towerDigits hd
    exact towerStone_strict_of_lt ht hq1 (by omega) hjK

/-- An ordinary harvest produces a canonical birth state for the next phase. -/
theorem isCanonical_phase_harvest
    {r t j : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j + 1 ≤ phaseCount r t)
    (hcanon : IsCanonical
      (phaseBirth r t j - phaseExtensionCount r t j)
      (phaseDigits r t j (phaseExtensionCount r t j))) :
    IsCanonical (phaseBirth r t (j + 1)) (phaseDigits r t (j + 1) 0) := by
  let ell := phaseExtensionCount r t j
  let k := phaseBirth r t j - ell
  let fixed := phaseFixedDigits r t j
  let s := towerStone r t j
  let a := towerStone r t (j + 1) - 1
  have hjK' : j ≤ phaseCount r t := by omega
  have hfixedSize : fixed.length + 2 ≤ k := by
    dsimp [fixed, k, ell]
    rw [length_phaseFixedDigits]
    unfold phaseBirth phaseExtensionCount
    by_cases hj1 : j = 1
    · simp only [hj1, if_pos]
      have hu := five_le_phaseTop_one ht
      omega
    · simp only [if_neg hj1]
      have hu := four_le_phaseTop_at_phase ht hj hjK'
      omega
  have hfixedCanonK : IsCanonical k fixed := by
    apply isCanonical_append_left
    simpa [k, fixed, ell, phaseDigits] using hcanon
  have hfixedCanon : IsCanonical (k - 1) fixed :=
    hfixedCanonK.lowerIndex (by omega) (by omega)
  have hactive := phase_harvest_active_index ht hj hjK'
  have hnewIndex := phase_harvest_newborn_index ht hj hjK'
  have hnewIndex' : k - fixed.length - 2 = phaseTop r t (j + 1) := by
    simpa [k, fixed, ell] using hnewIndex
  have hp : k - 1 - fixed.length =
      phaseTop r t (j + 1) + 1 := by
    omega
  have hnewInterior : phaseTop r t (j + 1) + 2 ≤ a := by
    dsimp [a]
    have hu := phaseTop_le_half_add_one_of_two_le ht (show 2 ≤ j + 1 by omega)
    have hs := towerStone_phase_lower ht (show 1 ≤ j + 1 by omega) hjK
    omega
  have hstoneStep : towerStone r t (j + 1) < s := by
    dsimp [s]
    exact towerStone_strict_of_lt ht hj (by omega) hjK
  have htail : IsCanonical (k - 1 - fixed.length) [s, a] := by
    rw [hp]
    simp only [isCanonical_succ_cons]
    refine ⟨?_, ?_, ?_⟩
    · have huNext := four_le_phaseTop_at_phase ht (by omega) hjK
      have hsNext := towerStone_phase_lower ht (by omega) hjK
      dsimp [s]
      omega
    · intro b hb
      simp only [List.mem_singleton] at hb
      subst b
      have hstep := hstoneStep
      dsimp [a, s]
      dsimp [s] at hstep
      omega
    · have huNext := four_le_phaseTop_at_phase ht (by omega) hjK
      exact isCanonical_singleton (by omega) (by omega)
  have hcross : ∀ d ∈ fixed, ∀ b ∈ [s, a], b < d := by
    intro d hd b hb
    have hsd := phaseFixed_digit_gt_stone ht hj hjK' hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hsd
    · have has : a < s := by
        have hstep := hstoneStep
        dsimp [a, s]
        dsimp [s] at hstep
        omega
      exact has.trans hsd
  have hfull := isCanonical_append hfixedCanon htail hcross
  have hbirth : phaseBirth r t (j + 1) = k - 1 := by
    dsimp [k, ell]
    exact phaseBirth_succ ht hj hjK'
  rw [phaseDigits_next_zero hj, hbirth]
  exact hfull

/-! ### Chainable ordinary phases -/

theorem isCanonical_phase_within
    {r t j : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t)
    (hbirth : IsCanonical (phaseBirth r t j) (phaseDigits r t j 0)) :
    ∀ L, L ≤ phaseExtensionCount r t j →
      IsCanonical (phaseBirth r t j - L) (phaseDigits r t j L) := by
  intro L hL
  induction L, Nat.zero_le L using Nat.le_induction with
  | base => simpa using hbirth
  | succ L _ ih =>
      exact isCanonical_phase_extension hr ht hj hjK (by omega) (ih (by omega))

/-- Every ordinary phase birth through `K` has the displayed canonical cascade. -/
theorem isCanonical_phase_birth
    {r t j : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t) :
    IsCanonical (phaseBirth r t j) (phaseDigits r t j 0) := by
  induction j, hj using Nat.le_induction with
  | base => exact isCanonical_phase_one_birth ht
  | succ j hj ih =>
      have hjK' : j ≤ phaseCount r t := by omega
      have hend := isCanonical_phase_within hr ht hj hjK' (ih hjK')
        (phaseExtensionCount r t j) le_rfl
      exact isCanonical_phase_harvest hr ht hj (by omega) hend

theorem isCanonical_phase_state
    {r t j L : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t)
    (hL : L ≤ phaseExtensionCount r t j) :
    IsCanonical (phaseBirth r t j - L) (phaseDigits r t j L) :=
  isCanonical_phase_within hr ht hj hjK
    (isCanonical_phase_birth hr ht hj hjK) L hL

/-- Every in-phase transition in phases `1,...,K` is a valid supersolution step. -/
theorem phase_extension_valid_auto
    {r t j L : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t)
    (hL : L < phaseExtensionCount r t j) :
    r + canonicalShadow (phaseBirth r t j - L) (phaseState r t j L) ≤
      phaseState r t j (L + 1) :=
  phase_extension_valid hr ht hj hjK hL
    (isCanonical_phase_state hr ht hj hjK hL.le)

/-- Every ordinary harvest before the final phase is a valid supersolution step. -/
theorem phase_harvest_valid_auto
    {r t j : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j + 1 ≤ phaseCount r t) :
    r + canonicalShadow
        (phaseBirth r t j - phaseExtensionCount r t j)
        (phaseState r t j (phaseExtensionCount r t j)) ≤
      phaseState r t (j + 1) 0 :=
  phase_harvest_valid hr ht hj hjK
    (isCanonical_phase_state hr ht hj (by omega) le_rfl)

end Erdos776.Uniform


/-!
# Entry into the ordinary phase block

This is the transition (4.1)--(4.3): after shadowing the completed anchor,
the two-term run `(N-3,N-4)` pays the incoming load and becomes phase one.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

theorem phase_one_digits_at_birth (r t : ℕ) :
    phaseDigits r t 1 0 =
      anchorHeadDigits r (t + 1) ++
        diagonalDigits (towerStone r t 1 - 1) 2 := by
  unfold phaseDigits phaseFixedDigits phaseRunDigits phaseRunLength
  simp [towerDigits]

/-- The two newborn phase-one terms have total value `2N-7 ≥ r`. -/
theorem phase_one_run_pays
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    r ≤ cascadeValue (phaseTop r t 1)
      (diagonalDigits (towerStone r t 1 - 1) 2) := by
  have hu := five_le_phaseTop_one ht
  have hstone : towerStone r t 1 = phaseTop r t 1 + 2 := by
    rw [first_towerStone_eq]
    simp only [phaseTop_one]
    rw [phaseTop_one] at hu
    omega
  rw [hstone]
  simp only [diagonalDigits_succ, cascadeValue_cons]
  have hchoose1 : (phaseTop r t 1 + 2 - 1).choose (phaseTop r t 1) =
      phaseTop r t 1 + 1 := by
    rw [show phaseTop r t 1 + 2 - 1 = phaseTop r t 1 + 1 by omega]
    exact Nat.choose_succ_self_right _
  have hchoose2 : (phaseTop r t 1 + 2 - 1 - 1).choose
      (phaseTop r t 1 - 1) = phaseTop r t 1 := by
    rw [show phaseTop r t 1 + 2 - 1 - 1 = phaseTop r t 1 by omega]
    rw [Nat.choose_symm (n := phaseTop r t 1) (k := 1) (by omega),
      Nat.choose_one_right]
  rw [hchoose1, hchoose2]
  simp only [diagonalDigits_zero, cascadeValue_nil, Nat.add_zero]
  rw [phaseTop_one_eq_width ht]
  have h64 := sixtyFour_mul_phaseWidth_le ht
  omega

/-- The completed anchor feeds the first phase birth. -/
theorem completedAnchor_to_phase_one
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    r + canonicalShadow (r - t - 1) (completedAnchorValue r t) ≤
      phaseState r t 1 0 := by
  have hcanon0 := isCanonical_anchorHeadDigits
    (r := r) (q := t + 1) (show 2 * (t + 1) + 2 ≤ r by
      have h64 := sixtyFour_mul_phaseWidth_le ht
      simp [phaseWidth] at h64
      omega)
  have hcanon : IsCanonical (r - t - 1) (anchorHeadDigits r (t + 1)) := by
    simpa only [show r - (t + 1) = r - t - 1 by omega] using hcanon0
  rw [canonicalShadow_eq_cascadeShadowValue hcanon]
  · unfold phaseState
    rw [phase_one_digits_at_birth, phaseBirth_one ht, cascadeValue_append]
    unfold cascadeShadowValue
    have hindex : r - t - 2 - (anchorHeadDigits r (t + 1)).length =
        phaseTop r t 1 := by
      rw [length_anchorHeadDigits]
      have h64 := sixtyFour_mul_phaseWidth_le ht
      simp only [phaseTop_one, anchorN, phaseWidth] at h64 ⊢
      omega
    simp only [Nat.sub_zero,
      show r - t - 1 - 1 = r - t - 2 by omega]
    rw [hindex]
    simpa [Nat.add_comm] using Nat.add_le_add_left (phase_one_run_pays ht)
      (cascadeValue (r - t - 2) (anchorHeadDigits r (t + 1)))
  · rfl

end Erdos776.Uniform


/-!
# Capacity of the ordinary phase states

Every displayed phase cascade has all digits below `r+3`.  Together with
canonicity, this puts its value below the `(r+3)`-ground-set level and hence
below the required `(r+4)` capacity.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

theorem towerStone_le_r (r t j : ℕ) : towerStone r t j ≤ r := by
  have hc : 0 < phaseWidth t := by simp [phaseWidth]
  have hp : 0 < 2 ^ (j - 1) := pow_pos (by omega) _
  have hprod : 0 < phaseWidth t * 2 ^ (j - 1) := Nat.mul_pos hc hp
  unfold towerStone
  omega

theorem phaseDigits_all_lt_r3
    {r t j L d : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hd : d ∈ phaseDigits r t j L) :
    d < r + 3 := by
  rcases List.mem_append.mp hd with hd | hd
  · rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨q, hq, rfl⟩ := mem_anchorHeadDigits
        (q := t + 1) (by
          have h64 := sixtyFour_mul_phaseWidth_le ht
          simp [phaseWidth] at h64
          omega) hd
      omega
    · obtain ⟨q, hq1, hqCount, rfl⟩ := mem_towerDigits hd
      exact (towerStone_le_r r t q).trans_lt (by omega)
  · have hdLe := mem_diagonalDigits_le hd
    exact hdLe.trans_lt (by
      have hs := towerStone_le_r r t j
      omega)

theorem phaseBirth_le_phaseBirth_one
    {r t j : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t) :
    phaseBirth r t j ≤ phaseBirth r t 1 := by
  induction j, hj using Nat.le_induction with
  | base => exact le_rfl
  | succ j hj ih =>
      have hjK' : j ≤ phaseCount r t := by omega
      rw [phaseBirth_succ ht hj hjK']
      exact (Nat.sub_le _ _).trans ((Nat.sub_le _ _).trans (ih hjK'))

theorem phaseLevel_le_r
    {r t j L : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t) :
    phaseBirth r t j - L ≤ r := by
  exact (Nat.sub_le _ _).trans
    ((phaseBirth_le_phaseBirth_one ht hj hjK).trans (by
      rw [phaseBirth_one ht]
      omega))

/-- Every state in every ordinary phase fits the required level capacity. -/
theorem phaseState_lt_capacity
    {r t j L : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t)
    (hL : L ≤ phaseExtensionCount r t j) :
    phaseState r t j L < (r + 4).choose (phaseBirth r t j - L) := by
  have hcanon := isCanonical_phase_state hr ht hj hjK hL
  have hlevel := phaseLevel_le_r (L := L) ht hj hjK
  have hsmall : phaseState r t j L <
      (r + 3).choose (phaseBirth r t j - L) := by
    unfold phaseState
    exact cascadeValue_lt_choose_of_all_lt (by omega) hcanon
      (fun d hd => phaseDigits_all_lt_r3 ht hd)
  exact hsmall.trans_le (Nat.choose_le_choose _ (by omega))

end Erdos776.Uniform


/-!
# The one-digit final zone

This file formalizes Section 7.  The completed stones remain fixed while one
tail digit rises as its lower index descends from `u_K-1` to `2`.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

/-- `D=s_{K+1}+2` from (7.1). -/
noncomputable def finalTailCeiling (r t : ℕ) : ℕ :=
  towerStone r t (phaseCount r t + 1) + 2

/-- The digit `d_p` from (7.3). -/
noncomputable def risingTailDigit (r t p : ℕ) : ℕ :=
  if p = 2 then finalTailCeiling r t
  else finalTailCeiling r t - p + 1

/-- The anchors and all completed stones `s₁,...,s_K`. -/
noncomputable def risingFixedDigits (r t : ℕ) : List ℕ :=
  phaseFixedDigits r t (phaseCount r t) ++ [towerStone r t (phaseCount r t)]

theorem length_risingFixedDigits (r t : ℕ) (hK : 1 ≤ phaseCount r t) :
    (risingFixedDigits r t).length = t + 2 + phaseCount r t := by
  simp [risingFixedDigits]
  omega

/-- At tail position `p`, the common level is `t+K+p+2`. -/
noncomputable def risingLevel (r t p : ℕ) : ℕ := t + phaseCount r t + p + 2

noncomputable def risingDigits (r t p : ℕ) : List ℕ :=
  risingFixedDigits r t ++ [risingTailDigit r t p]

noncomputable def risingState (r t p : ℕ) : ℕ :=
  cascadeValue (risingLevel r t p) (risingDigits r t p)

theorem finalTop_le_eighth_add_two
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    phaseTop r t (phaseCount r t) ≤ r / 8 + 2 := by
  have hu := finalTop_le_eight_mul_phaseWidth_add_two ht
  have h64 := sixtyFour_mul_phaseWidth_le ht
  have hwidth : 8 * phaseWidth t ≤ r / 8 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 8)).2
    omega
  omega

theorem finalTailCeiling_lower
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    r / 2 + 3 ≤ finalTailCeiling r t := by
  unfold finalTailCeiling
  have hs := towerStone_after_phases_lower ht
  omega

theorem finalTailCeiling_lt_finalStone
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    finalTailCeiling r t < towerStone r t (phaseCount r t) := by
  let K := phaseCount r t
  let c := phaseWidth t
  let p := 2 ^ (K - 1)
  have hK : 5 ≤ K := five_le_phaseCount ht
  have hpow : 2 ^ K = 2 * p := by
    dsimp [p]
    conv_lhs => rw [show K = K - 1 + 1 by omega, pow_succ]
    omega
  have hdist : c * 2 ^ K ≤ r / 2 := by
    have hlower := (phaseCount_spec ht).2.1
    dsimp [K, c, p] at hpow ⊢
    rw [hpow]
    calc
      phaseWidth t * (2 * 2 ^ (phaseCount r t - 1)) =
          2 * (phaseWidth t * 2 ^ (phaseCount r t - 1)) := by
        simp [Nat.mul_assoc, Nat.mul_comm]
      _ ≤ 2 * (r / 4) := Nat.mul_le_mul_left 2 hlower
      _ ≤ r / 2 := by omega
  have hgap : 3 ≤ c * p := by
    have hc : 3 ≤ c := by simp [c, phaseWidth]
    have hp : 0 < p := pow_pos (by omega) _
    exact (show 3 * 1 ≤ c * p from Nat.mul_le_mul hc hp)
  have hrec : towerStone r t (K + 1) =
      2 * towerStone r t K - r - 1 := by
    apply towerStone_succ (j := K) (by omega)
    exact hdist.trans (by omega)
  have hsK : towerStone r t K ≤ r - 2 := by
    unfold towerStone
    dsimp [c, p] at hgap ⊢
    omega
  unfold finalTailCeiling
  dsimp [K] at hrec hsK ⊢
  rw [hrec]
  have hsLower := towerStone_phase_lower ht (phaseCount_spec ht).1 le_rfl
  omega

theorem risingTailDigit_le_ceiling {r t p : ℕ}
    (ht : IsMaximalAnchorIndex r t) (hp : 1 ≤ p) :
    risingTailDigit r t p ≤ finalTailCeiling r t := by
  have hD := finalTailCeiling_lower ht
  unfold risingTailDigit
  by_cases h : p = 2
  · simp [h]
  · simp only [if_neg h]
    omega

theorem risingTailDigit_lt_finalStone
    {r t p : ℕ} (ht : IsMaximalAnchorIndex r t) (hp : 1 ≤ p) :
    risingTailDigit r t p < towerStone r t (phaseCount r t) :=
  (risingTailDigit_le_ceiling ht hp).trans_lt
    (finalTailCeiling_lt_finalStone ht)

theorem risingTailDigit_valid
    {r t p : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hp2 : 2 ≤ p) (hpu : p < phaseTop r t (phaseCount r t)) :
    p ≤ risingTailDigit r t p := by
  have hD := finalTailCeiling_lower ht
  have hu := finalTop_le_eighth_add_two ht
  unfold risingTailDigit
  by_cases hp : p = 2
  · simp only [hp, if_pos]
    omega
  · simp only [if_neg hp]
    omega

theorem risingLevel_sub_fixedLength (r t p : ℕ)
    (hK : 1 ≤ phaseCount r t) :
    risingLevel r t p - (risingFixedDigits r t).length = p := by
  rw [length_risingFixedDigits r t hK]
  unfold risingLevel
  omega

theorem risingLevel_le_birth
    {r t p : ℕ} (hp : p < phaseTop r t (phaseCount r t)) :
    risingLevel r t p ≤ phaseBirth r t (phaseCount r t) := by
  unfold risingLevel phaseBirth
  omega

/-- Every displayed rising-tail state is a canonical cascade. -/
theorem isCanonical_risingState
    {r t p : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hp2 : 2 ≤ p) (hpu : p < phaseTop r t (phaseCount r t)) :
    IsCanonical (risingLevel r t p) (risingDigits r t p) := by
  let K := phaseCount r t
  let fixed := phaseFixedDigits r t K
  let s := towerStone r t K
  let d := risingTailDigit r t p
  have hK : 1 ≤ K := (phaseCount_spec ht).1
  have hbirth := isCanonical_phase_birth hr ht hK le_rfl
  have hfixedBirth : IsCanonical (phaseBirth r t K) fixed := by
    apply isCanonical_append_left
    simpa [K, fixed, phaseDigits, phaseRunDigits, phaseRunLength] using hbirth
  have hlevel := risingLevel_le_birth hpu
  have hfixedLen : fixed.length ≤ risingLevel r t p := by
    rw [length_phaseFixedDigits]
    unfold risingLevel
    omega
  have hfixed : IsCanonical (risingLevel r t p) fixed :=
    hfixedBirth.lowerIndex hlevel hfixedLen
  have htailIndex : risingLevel r t p - fixed.length = p + 1 := by
    dsimp [fixed, K]
    rw [length_phaseFixedDigits]
    unfold risingLevel
    omega
  have hdValid := risingTailDigit_valid hr ht hp2 hpu
  have hsValid : p + 1 ≤ s := by
    have hs := towerStone_phase_lower ht hK le_rfl
    have hu := finalTop_le_eighth_add_two ht
    dsimp [K] at hs
    dsimp [s, K]
    omega
  have htail : IsCanonical (risingLevel r t p - fixed.length) [s, d] := by
    rw [htailIndex]
    simp only [isCanonical_succ_cons]
    refine ⟨?_, ?_, isCanonical_singleton (by omega) hdValid⟩
    · exact hsValid
    · intro b hb
      simp only [List.mem_singleton] at hb
      subst b
      dsimp [d, s, K]
      exact risingTailDigit_lt_finalStone ht (by omega)
  have hcross : ∀ a ∈ fixed, ∀ b ∈ [s, d], b < a := by
    intro a ha b hb
    have hsa := phaseFixed_digit_gt_stone ht hK le_rfl ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hsa
    · exact (risingTailDigit_lt_finalStone ht (by omega)).trans hsa
  have hfull := isCanonical_append hfixed htail hcross
  unfold risingDigits risingFixedDigits
  dsimp [fixed, s, d, K] at hfull ⊢
  simpa [List.append_assoc] using hfull

theorem risingTailDigit_step
    {r t p : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hp4 : 4 ≤ p) (hpu : p < phaseTop r t (phaseCount r t)) :
    risingTailDigit r t (p - 1) = risingTailDigit r t p + 1 := by
  have hvalid := risingTailDigit_valid hr ht (by omega) hpu
  unfold risingTailDigit at hvalid ⊢
  simp only [if_neg (show p ≠ 2 by omega),
    if_neg (show p - 1 ≠ 2 by omega)] at hvalid ⊢
  omega

theorem risingTail_gain_pays
    {r t p : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hp4 : 4 ≤ p) (hpu : p < phaseTop r t (phaseCount r t)) :
    r + (risingTailDigit r t p).choose (p - 1) ≤
      (risingTailDigit r t (p - 1)).choose (p - 1) := by
  have hstep := risingTailDigit_step hr ht hp4 hpu
  have hdValid := risingTailDigit_valid hr ht (by omega) hpu
  have hD := finalTailCeiling_lower ht
  have hu := finalTop_le_eighth_add_two ht
  have hdQuarter : r / 4 - 1 ≤ risingTailDigit r t p := by
    unfold risingTailDigit
    simp only [if_neg (show p ≠ 2 by omega)]
    omega
  have hpay : r ≤ (risingTailDigit r t p).choose (p - 2) := by
    apply binomial_pays_of_quarter_digit hr hdQuarter (by omega)
    omega
  have hpascal := Nat.choose_succ_succ (risingTailDigit r t p) (p - 2)
  have hpascal' : (risingTailDigit r t p + 1).choose (p - 1) =
      (risingTailDigit r t p).choose (p - 2) +
        (risingTailDigit r t p).choose (p - 1) := by
    simpa only [Nat.succ_eq_add_one, show p - 2 + 1 = p - 1 by omega] using hpascal
  rw [hstep, hpascal']
  simpa [Nat.add_comm, Nat.add_left_comm] using
    Nat.add_le_add_right hpay ((risingTailDigit r t p).choose (p - 1))

/-- Every ordinary `p → p-1` rise (`p ≥ 4`) is a valid supersolution step. -/
theorem risingState_step
    {r t p : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hp4 : 4 ≤ p) (hpu : p < phaseTop r t (phaseCount r t)) :
    r + canonicalShadow (risingLevel r t p) (risingState r t p) ≤
      risingState r t (p - 1) := by
  have hcanon := isCanonical_risingState hr ht (by omega) hpu
  unfold risingState
  rw [show risingLevel r t (p - 1) = risingLevel r t p - 1 by
    unfold risingLevel
    omega]
  unfold risingDigits
  unfold risingDigits at hcanon
  rw [canonicalShadow_eq_cascadeShadowValue hcanon rfl]
  unfold cascadeShadowValue
  rw [cascadeValue_append, cascadeValue_append]
  simp only [cascadeValue_cons, cascadeValue_nil, Nat.add_zero]
  rw [show risingLevel r t p - 1 - (risingFixedDigits r t).length = p - 1 by
      rw [length_risingFixedDigits r t (phaseCount_spec ht).1]
      unfold risingLevel
      omega]
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    Nat.add_le_add_left (risingTail_gain_pays hr ht hp4 hpu)
      (cascadeValue (risingLevel r t p - 1) (risingFixedDigits r t))

/-! ### Entry, final jump, and capacity -/

theorem risingEntryPosition_two_le
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    2 ≤ phaseTop r t (phaseCount r t) - 1 := by
  have hu := three_mul_phaseWidth_le_finalTop ht
  have hc : 3 ≤ phaseWidth t := by simp [phaseWidth]
  omega

theorem risingEntryLevel
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    risingLevel r t (phaseTop r t (phaseCount r t) - 1) =
      phaseBirth r t (phaseCount r t) := by
  unfold risingLevel phaseBirth
  have hu := risingEntryPosition_two_le ht
  omega

theorem phaseK_state_le_rising_entry
    {r t : ℕ} (_hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t) :
    phaseState r t (phaseCount r t) 0 ≤
      risingState r t (phaseTop r t (phaseCount r t) - 1) := by
  let K := phaseCount r t
  let u := phaseTop r t K
  let fixed := phaseFixedDigits r t K
  let s := towerStone r t K
  let p := u - 1
  have hK : 1 ≤ K := (phaseCount_spec ht).1
  have hK5 : 5 ≤ K := by
    dsimp [K]
    exact five_le_phaseCount ht
  have hp2 : 2 ≤ p := by
    dsimp [p, u, K]
    exact risingEntryPosition_two_le ht
  have hlevel : risingLevel r t p = phaseBirth r t K := by
    dsimp [p, u, K]
    exact risingEntryLevel ht
  have hphaseDigits : phaseDigits r t K 0 = fixed ++ [s - 1] := by
    have hK1 : K ≠ 1 := by omega
    unfold phaseDigits phaseRunDigits phaseRunLength
    simp [fixed, s, hK1]
  unfold phaseState risingState
  rw [hlevel, hphaseDigits]
  unfold risingDigits risingFixedDigits
  dsimp [fixed, s, p, u, K]
  rw [cascadeValue_append, cascadeValue_append, cascadeValue_append]
  simp only [cascadeValue_cons, cascadeValue_nil, Nat.add_zero]
  have hindex : phaseBirth r t (phaseCount r t) -
      (phaseFixedDigits r t (phaseCount r t)).length =
      phaseTop r t (phaseCount r t) := by
    rw [length_phaseFixedDigits]
    unfold phaseBirth
    omega
  rw [hindex]
  have hmono : (towerStone r t (phaseCount r t) - 1).choose
      (phaseTop r t (phaseCount r t)) ≤
      (towerStone r t (phaseCount r t)).choose
        (phaseTop r t (phaseCount r t)) :=
    Nat.choose_le_choose _ (Nat.sub_le _ _)
  omega

/-- The special final gain `choose D 2 - choose (D-2) 2 = 2D-3`. -/
theorem risingTail_final_gain
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    r + (risingTailDigit r t 3).choose 2 ≤
      (risingTailDigit r t 2).choose 2 := by
  let D := finalTailCeiling r t
  have hD : r / 2 + 3 ≤ D := by
    dsimp [D]
    exact finalTailCeiling_lower ht
  have hD2 : 2 ≤ D := by omega
  have hd3 : risingTailDigit r t 3 = D - 2 := by
    unfold risingTailDigit
    simp only [if_neg (by omega : (3 : ℕ) ≠ 2)]
    dsimp [D] at hD ⊢
    omega
  have hd2 : risingTailDigit r t 2 = D := by
    simp [risingTailDigit, D]
  rw [hd3, hd2]
  have hp1 : D.choose 2 = (D - 1).choose 1 + (D - 1).choose 2 := by
    have h := Nat.choose_succ_succ (D - 1) 1
    simpa only [Nat.succ_eq_add_one, show D - 1 + 1 = D by omega] using h
  have hp2 : (D - 1).choose 2 =
      (D - 2).choose 1 + (D - 2).choose 2 := by
    have h := Nat.choose_succ_succ (D - 2) 1
    simpa only [Nat.succ_eq_add_one,
      show D - 2 + 1 = D - 1 by omega] using h
  rw [hp1, hp2, Nat.choose_one_right, Nat.choose_one_right]
  omega

theorem risingState_final_step
    {r t : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t) :
    r + canonicalShadow (risingLevel r t 3) (risingState r t 3) ≤
      risingState r t 2 := by
  have hu := three_mul_phaseWidth_le_finalTop ht
  have hc : 3 ≤ phaseWidth t := by simp [phaseWidth]
  have hcanon := isCanonical_risingState (p := 3) hr ht (by omega) (by omega)
  unfold risingState
  rw [show risingLevel r t 2 = risingLevel r t 3 - 1 by
    unfold risingLevel
    omega]
  unfold risingDigits
  unfold risingDigits at hcanon
  rw [canonicalShadow_eq_cascadeShadowValue hcanon rfl]
  unfold cascadeShadowValue
  rw [cascadeValue_append, cascadeValue_append]
  simp only [cascadeValue_cons, cascadeValue_nil, Nat.add_zero]
  have hK := (phaseCount_spec ht).1
  rw [show risingLevel r t 3 - 1 - (risingFixedDigits r t).length = 2 by
    rw [length_risingFixedDigits r t hK]
    unfold risingLevel
    omega]
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    Nat.add_le_add_left (risingTail_final_gain ht)
      (cascadeValue (risingLevel r t 3 - 1) (risingFixedDigits r t))

/-- The last ordinary harvest enters the one-digit final zone. -/
theorem final_phase_harvest_to_rising
    {r t : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t) :
    let K := phaseCount r t
    let j := K - 1
    r + canonicalShadow
        (phaseBirth r t j - phaseExtensionCount r t j)
        (phaseState r t j (phaseExtensionCount r t j)) ≤
      risingState r t (phaseTop r t K - 1) := by
  dsimp only
  have hK : 5 ≤ phaseCount r t := five_le_phaseCount ht
  have hharvest := phase_harvest_valid_auto hr ht
    (j := phaseCount r t - 1) (by omega)
    (show phaseCount r t - 1 + 1 ≤ phaseCount r t by omega)
  rw [show phaseCount r t - 1 + 1 = phaseCount r t by omega] at hharvest
  exact hharvest.trans (phaseK_state_le_rising_entry hr ht)

theorem risingDigits_all_lt_r3
    {r t p d : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hp : 1 ≤ p) (hd : d ∈ risingDigits r t p) :
    d < r + 3 := by
  rcases List.mem_append.mp hd with hd | hd
  · rcases List.mem_append.mp hd with hd | hd
    · rcases List.mem_append.mp hd with hd | hd
      · obtain ⟨q, hq, rfl⟩ := mem_anchorHeadDigits
          (q := t + 1) (by
            have h64 := sixtyFour_mul_phaseWidth_le ht
            simp [phaseWidth] at h64
            omega) hd
        omega
      · obtain ⟨q, hq1, hqCount, rfl⟩ := mem_towerDigits hd
        exact (towerStone_le_r r t q).trans_lt (by omega)
    · simp only [List.mem_singleton] at hd
      subst d
      exact (towerStone_le_r r t (phaseCount r t)).trans_lt (by omega)
  · simp only [List.mem_singleton] at hd
    subst d
    exact (risingTailDigit_lt_finalStone ht hp).trans
      ((towerStone_le_r r t (phaseCount r t)).trans_lt (by omega))

theorem risingState_lt_capacity
    {r t p : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hp2 : 2 ≤ p) (hpu : p < phaseTop r t (phaseCount r t)) :
    risingState r t p < (r + 4).choose (risingLevel r t p) := by
  have hcanon := isCanonical_risingState hr ht hp2 hpu
  have hlevel : risingLevel r t p ≤ r := by
    exact (risingLevel_le_birth hpu).trans
      (phaseLevel_le_r (L := 0) ht (phaseCount_spec ht).1 le_rfl)
  have hsmall : risingState r t p < (r + 3).choose (risingLevel r t p) := by
    unfold risingState
    exact cascadeValue_lt_choose_of_all_lt (by omega) hcanon
      (fun d hd => risingDigits_all_lt_r3 ht (by omega) hd)
  exact hsmall.trans_le (Nat.choose_le_choose _ (by omega))

end Erdos776.Uniform


/-!
# The exact generalized envelope

This is Section 8.  At level `i`, `envelopeCount t i = i-t-4` tower stones
have been completed, and the terminal position-two digit is the next stone
plus two.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

def envelopeCount (t i : ℕ) : ℕ := i - t - 4

def generalizedEnvelopeDigits (r t i : ℕ) : List ℕ :=
  anchorHeadDigits r (t + 1) ++ towerDigits r t (envelopeCount t i) ++
    [towerStone r t (envelopeCount t i + 1) + 2]

def generalizedEnvelopeState (r t i : ℕ) : ℕ :=
  cascadeValue i (generalizedEnvelopeDigits r t i)

theorem envelope_level_eq
    {t i : ℕ} (hi : t + 4 ≤ i) :
    i = t + envelopeCount t i + 4 := by
  unfold envelopeCount
  omega

theorem envelopeCount_pos
    {t i : ℕ} (hi : t + 5 ≤ i) : 1 ≤ envelopeCount t i := by
  unfold envelopeCount
  omega

theorem envelopeCount_le_phaseCount
    {r t i : ℕ} (hi : i ≤ t + phaseCount r t + 4) :
    envelopeCount t i ≤ phaseCount r t := by
  unfold envelopeCount
  omega

theorem generalizedEnvelopeDigits_eq_phaseFixed
    {r t i : ℕ} (hi : t + 5 ≤ i) :
    generalizedEnvelopeDigits r t i =
      phaseFixedDigits r t (envelopeCount t i) ++
        [towerStone r t (envelopeCount t i),
          towerStone r t (envelopeCount t i + 1) + 2] := by
  let m := envelopeCount t i
  have hm : 1 ≤ m := envelopeCount_pos hi
  unfold generalizedEnvelopeDigits phaseFixedDigits
  rw [show envelopeCount t i = (envelopeCount t i - 1) + 1 by omega,
    towerDigits_succ, show envelopeCount t i - 1 + 1 = envelopeCount t i by omega]
  simp [List.append_assoc]

theorem towerStone_succ_add_two_lt
    {r t m : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hm : 1 ≤ m) (hmK : m ≤ phaseCount r t) :
    towerStone r t (m + 1) + 2 < towerStone r t m := by
  have hK : 1 ≤ phaseCount r t := (phaseCount_spec ht).1
  have hpowK : 2 ^ phaseCount r t =
      2 * 2 ^ (phaseCount r t - 1) := by
    conv_lhs => rw [show phaseCount r t = phaseCount r t - 1 + 1 by omega,
      pow_succ]
    omega
  have hpow : 2 ^ m ≤ 2 ^ phaseCount r t :=
    pow_le_pow_right' (by omega) hmK
  have hdistK : phaseWidth t * 2 ^ phaseCount r t ≤ r / 2 := by
    rw [hpowK]
    calc
      phaseWidth t * (2 * 2 ^ (phaseCount r t - 1)) =
          2 * (phaseWidth t * 2 ^ (phaseCount r t - 1)) := by
        simp [Nat.mul_assoc, Nat.mul_comm]
      _ ≤ 2 * (r / 4) :=
        Nat.mul_le_mul_left 2 (phaseCount_spec ht).2.1
      _ ≤ r / 2 := by omega
  have hdist : phaseWidth t * 2 ^ m ≤ r / 2 :=
    (Nat.mul_le_mul_left _ hpow).trans hdistK
  have hrec := towerStone_succ (r := r) (t := t) (j := m) hm
    (hdist.trans (by omega))
  have hgap : 3 ≤ phaseWidth t * 2 ^ (m - 1) := by
    have hc : 3 ≤ phaseWidth t := by simp [phaseWidth]
    have hp : 0 < 2 ^ (m - 1) := pow_pos (by omega) _
    exact Nat.mul_le_mul hc hp
  have hs : towerStone r t m ≤ r - 2 := by
    unfold towerStone
    omega
  have hsLower := towerStone_phase_lower ht hm hmK
  omega

/-- Every generalized-envelope display is canonical in its stated range. -/
theorem isCanonical_generalizedEnvelope
    {r t i : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hiLower : t + 5 ≤ i) (hiUpper : i ≤ t + phaseCount r t + 4) :
    IsCanonical i (generalizedEnvelopeDigits r t i) := by
  let m := envelopeCount t i
  let fixed := phaseFixedDigits r t m
  let s := towerStone r t m
  let d := towerStone r t (m + 1) + 2
  have hm : 1 ≤ m := envelopeCount_pos hiLower
  have hmK : m ≤ phaseCount r t := envelopeCount_le_phaseCount hiUpper
  have hbirth := isCanonical_phase_birth hr ht hm hmK
  have hfixedBirth : IsCanonical (phaseBirth r t m) fixed := by
    apply isCanonical_append_left
    simpa [m, fixed, phaseDigits] using hbirth
  have hiEq : i = t + m + 4 := by
    dsimp [m]
    exact envelope_level_eq (by omega)
  have hiBirth : i ≤ phaseBirth r t m := by
    rw [hiEq]
    unfold phaseBirth
    have hu := four_le_phaseTop_at_phase ht hm hmK
    omega
  have hfixedLen : fixed.length ≤ i := by
    dsimp [fixed]
    rw [length_phaseFixedDigits, hiEq]
    omega
  have hfixed : IsCanonical i fixed :=
    hfixedBirth.lowerIndex hiBirth hfixedLen
  have htailIndex : i - fixed.length = 3 := by
    dsimp [fixed]
    rw [length_phaseFixedDigits, hiEq]
    omega
  have hsd : d < s := by
    dsimp [d, s, m]
    exact towerStone_succ_add_two_lt ht hm hmK
  have hsLower := towerStone_phase_lower ht hm hmK
  have htail : IsCanonical (i - fixed.length) [s, d] := by
    rw [htailIndex]
    norm_num [IsCanonical]
    omega
  have hcross : ∀ a ∈ fixed, ∀ b ∈ [s, d], b < a := by
    intro a ha b hb
    have hsa := phaseFixed_digit_gt_stone ht hm hmK ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · exact hsa
    · exact hsd.trans hsa
  have hfull := isCanonical_append hfixed htail hcross
  rw [generalizedEnvelopeDigits_eq_phaseFixed hiLower]
  simpa [m, fixed, s, d] using hfull

theorem generalizedEnvelope_top_eq_rising
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    generalizedEnvelopeState r t (t + phaseCount r t + 4) =
      risingState r t 2 := by
  unfold generalizedEnvelopeState risingState
  have hcount : envelopeCount t (t + phaseCount r t + 4) =
      phaseCount r t := by
    unfold envelopeCount
    omega
  have hlevel : risingLevel r t 2 = t + phaseCount r t + 4 := by
    unfold risingLevel
    omega
  rw [hlevel]
  have hK := five_le_phaseCount ht
  rw [generalizedEnvelopeDigits_eq_phaseFixed (show
    t + 5 ≤ t + phaseCount r t + 4 by omega)]
  rw [hcount]
  unfold risingDigits risingFixedDigits risingTailDigit finalTailCeiling
  simp [List.append_assoc]

theorem envelope_stone_recurrence
    {r t m : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hm : 1 ≤ m) (hmK : m ≤ phaseCount r t) :
    towerStone r t (m + 1) = 2 * towerStone r t m - r - 1 := by
  have hpow : phaseWidth t * 2 ^ m ≤ r / 2 := by
    have hKm : 2 ^ m ≤ 2 ^ phaseCount r t :=
      pow_le_pow_right' (a := 2) (by omega) hmK
    have hpowK : 2 ^ phaseCount r t =
        2 * 2 ^ (phaseCount r t - 1) := by
      conv_lhs => rw [show phaseCount r t = phaseCount r t - 1 + 1 by
        have := (phaseCount_spec ht).1
        omega, pow_succ]
      omega
    calc
      phaseWidth t * 2 ^ m ≤ phaseWidth t * 2 ^ phaseCount r t :=
        Nat.mul_le_mul_left _ hKm
      _ = 2 * (phaseWidth t * 2 ^ (phaseCount r t - 1)) := by
        rw [hpowK]
        simp [Nat.mul_assoc, Nat.mul_comm]
      _ ≤ 2 * (r / 4) :=
        Nat.mul_le_mul_left 2 (phaseCount_spec ht).2.1
      _ ≤ r / 2 := by omega
  exact towerStone_succ hm (hpow.trans (by omega))

theorem envelope_bottom_gain
    {r t m : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hm : 1 ≤ m) (hmK : m ≤ phaseCount r t) :
    r + (towerStone r t m).choose 2 +
        (towerStone r t (m + 1) + 2) =
      (towerStone r t m + 2).choose 2 := by
  let s := towerStone r t m
  let sn := towerStone r t (m + 1)
  have hrec : sn = 2 * s - r - 1 := by
    dsimp [sn, s]
    exact envelope_stone_recurrence ht hm hmK
  have hs := towerStone_phase_lower ht hm hmK
  have hp1 : (s + 1).choose 2 = s + s.choose 2 := by
    simpa [Nat.choose_one_right] using Nat.choose_succ_succ s 1
  have hp2 : (s + 2).choose 2 = s + 1 + (s + 1).choose 2 := by
    simpa [Nat.choose_one_right] using Nat.choose_succ_succ (s + 1) 1
  change r + s.choose 2 + (sn + 2) = (s + 2).choose 2
  rw [hp2, hp1]
  omega

/-- The exact envelope recurrence (8.2). -/
theorem generalizedEnvelope_step
    {r t i : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hiLower : t + 6 ≤ i) (hiUpper : i ≤ t + phaseCount r t + 4) :
    generalizedEnvelopeState r t (i - 1) =
      r + canonicalShadow i (generalizedEnvelopeState r t i) := by
  let m := envelopeCount t i
  let fixed := phaseFixedDigits r t m
  let s := towerStone r t m
  let d := towerStone r t (m + 1) + 2
  have hm : 2 ≤ m := by
    dsimp [m]
    unfold envelopeCount
    omega
  have hmK : m ≤ phaseCount r t := envelopeCount_le_phaseCount hiUpper
  have hiEq : i = t + m + 4 := by
    dsimp [m]
    exact envelope_level_eq (by omega)
  have holdDigits : generalizedEnvelopeDigits r t i = fixed ++ [s, d] := by
    dsimp [fixed, s, d, m]
    exact generalizedEnvelopeDigits_eq_phaseFixed (by omega)
  have hnewCount : envelopeCount t (i - 1) = m - 1 := by
    dsimp [m]
    unfold envelopeCount
    omega
  have hnewDigits : generalizedEnvelopeDigits r t (i - 1) =
      fixed ++ [s + 2] := by
    unfold generalizedEnvelopeDigits
    rw [hnewCount]
    dsimp [fixed, s, m]
    unfold phaseFixedDigits
    rw [show envelopeCount t i - 1 + 1 = envelopeCount t i by omega]
  have hcanon := isCanonical_generalizedEnvelope hr ht (by omega) hiUpper
  rw [holdDigits] at hcanon
  unfold generalizedEnvelopeState
  rw [holdDigits, hnewDigits,
    canonicalShadow_eq_cascadeShadowValue hcanon rfl]
  unfold cascadeShadowValue
  rw [cascadeValue_append, cascadeValue_append]
  simp only [cascadeValue_cons, cascadeValue_nil, Nat.add_zero]
  have hindex : i - 1 - fixed.length = 2 := by
    dsimp [fixed]
    rw [length_phaseFixedDigits, hiEq]
    omega
  rw [hindex]
  have hgain := envelope_bottom_gain ht (by omega) hmK
  norm_num [Nat.choose_one_right]
  dsimp [s, d] at hgain ⊢
  omega

theorem generalizedEnvelopeState_lt_capacity
    {r t i : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hiLower : t + 5 ≤ i) (hiUpper : i ≤ t + phaseCount r t + 4) :
    generalizedEnvelopeState r t i < (r + 4).choose i := by
  have hcanon := isCanonical_generalizedEnvelope hr ht hiLower hiUpper
  have hall : ∀ d ∈ generalizedEnvelopeDigits r t i, d < r + 3 := by
    intro d hd
    rw [generalizedEnvelopeDigits_eq_phaseFixed hiLower] at hd
    rcases List.mem_append.mp hd with hd | hd
    · unfold phaseFixedDigits at hd
      rcases List.mem_append.mp hd with hd | hd
      · obtain ⟨q, hq, rfl⟩ := mem_anchorHeadDigits
          (q := t + 1) (by
            have h64 := sixtyFour_mul_phaseWidth_le ht
            simp [phaseWidth] at h64
            omega) hd
        omega
      · obtain ⟨q, hq1, hqCount, rfl⟩ := mem_towerDigits hd
        exact (towerStone_le_r r t q).trans_lt (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact (towerStone_le_r r t (envelopeCount t i)).trans_lt (by omega)
      · have hs := towerStone_le_r r t (envelopeCount t i + 1)
        omega
  have hlevel : i ≤ r + 3 := by
    let m := envelopeCount t i
    have hm1 : 1 ≤ m := envelopeCount_pos hiLower
    have hmK : m ≤ phaseCount r t := envelopeCount_le_phaseCount hiUpper
    have hb := phaseLevel_le_r (L := 0) ht hm1 hmK
    have hiEq : i = t + m + 4 := by
      dsimp [m]
      exact envelope_level_eq (by omega)
    have hu := four_le_phaseTop_at_phase ht hm1 hmK
    have hiBirth : i ≤ phaseBirth r t m := by
      rw [hiEq]
      unfold phaseBirth
      omega
    exact hiBirth.trans (hb.trans (by omega))
  have hsmall : generalizedEnvelopeState r t i < (r + 3).choose i := by
    unfold generalizedEnvelopeState
    exact cascadeValue_lt_choose_of_all_lt hlevel hcanon hall
  exact hsmall.trans_le (Nat.choose_le_choose _ (by omega))

end Erdos776.Uniform


/-!
# Semantic scalar-collapse states

The scalar recurrence was proved in `ScalarCollapse.lean`.  Here `F_q(z)` is
represented by its actual canonical-cascade digit list, the envelope collision
is checked, and one scalar recurrence step is evaluated through
`canonicalShadow`.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

/-- The digit list representing `F_q(z)` from (9.1). -/
def scalarDigits (r q z : ℕ) : List ℕ :=
  anchorHeadDigits r q ++ [r - 2 * q + 1] ++ canonicalDigits 2 z

def scalarState (r q z : ℕ) : ℕ :=
  cascadeValue (q + 4) (scalarDigits r q z)

theorem scalarState_value (r q z : ℕ) :
    scalarState r q z =
      cascadeValue (q + 4) (anchorHeadDigits r q) +
        (r - 2 * q + 1).choose 3 + z := by
  unfold scalarState scalarDigits
  rw [cascadeValue_append, cascadeValue_append]
  rw [length_anchorHeadDigits]
  have hidx3 : q + 4 - (q + 1) = 3 := by omega
  rw [hidx3]
  simp only [cascadeValue_cons, cascadeValue_nil,
    Nat.add_zero]
  rw [List.length_append, length_anchorHeadDigits, List.length_singleton]
  have hidx2 : q + 4 - (q + 1 + 1) = 2 := by omega
  rw [hidx2, cascadeValue_canonicalDigits (by omega)]

@[simp] theorem scalarState_zero_residual (r q : ℕ) :
    scalarState r q 0 =
      cascadeValue (q + 4) (anchorHeadDigits r q) +
        (r - 2 * q + 1).choose 3 := by
  rw [scalarState_value]
  omega

theorem scalarState_bottom_eq_finalFour (r z : ℕ) :
    scalarState r 0 z = finalFourState r z := by
  rw [scalarState_value]
  unfold finalFourState
  simp [anchorHeadDigits, cascadeValue]

theorem envelope_bottom_digits
    {r t : ℕ} :
    generalizedEnvelopeDigits r t (t + 5) =
      anchorHeadDigits r t ++
        [anchorN r t, towerStone r t 1, towerStone r t 2 + 2] := by
  have hcount : envelopeCount t (t + 5) = 1 := by
    unfold envelopeCount
    omega
  rw [generalizedEnvelopeDigits_eq_phaseFixed (r := r) (by omega), hcount]
  simp [phaseFixedDigits, towerDigits, anchorHeadDigits, anchorN,
    List.append_assoc]

/-- Section 9: the extra anchors collide exactly to `F_t(0)`. -/
theorem generalizedEnvelope_collision
    {r t : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t) :
    scalarState r t 0 =
      r + canonicalShadow (t + 5) (generalizedEnvelopeState r t (t + 5)) := by
  have hK := five_le_phaseCount ht
  have hcanon := isCanonical_generalizedEnvelope hr ht (by omega)
    (show t + 5 ≤ t + phaseCount r t + 4 by omega)
  have hdigits := envelope_bottom_digits (r := r) (t := t)
  rw [hdigits] at hcanon
  unfold generalizedEnvelopeState
  rw [hdigits, canonicalShadow_eq_cascadeShadowValue hcanon rfl]
  unfold cascadeShadowValue scalarState scalarDigits
  have hanchor : anchorHeadDigits r (t + 1) =
      anchorHeadDigits r t ++ [anchorN r t] := by
    rw [anchorHeadDigits]
    rfl
  have hscalarZero : canonicalDigits 2 0 = [] := by simp
  rw [hscalarZero]
  simp only [List.append_nil]
  rw [show t + 5 - 1 = t + 4 by omega]
  rw [cascadeValue_append, cascadeValue_append]
  have hlen : (anchorHeadDigits r t).length = t + 1 :=
    length_anchorHeadDigits r t
  rw [hlen]
  have hidxNew : t + 4 - (t + 1) = 3 := by omega
  rw [hidxNew]
  simp only [cascadeValue_cons, cascadeValue_nil, Nat.add_zero]
  have hN : towerStone r t 1 + 2 = anchorN r t := by
    rw [first_towerStone_eq]
    have hu := five_le_phaseTop_one ht
    rw [phaseTop_one] at hu
    omega
  have hgain := envelope_bottom_gain ht (m := 1) (by omega)
    (show 1 ≤ phaseCount r t from (phaseCount_spec ht).1)
  rw [hN] at hgain
  norm_num at hgain
  have hpascal : (anchorN r t + 1).choose 3 =
      (anchorN r t).choose 2 + (anchorN r t).choose 3 := by
    simpa using Nat.choose_succ_succ (anchorN r t) 2
  have hspecial : r - 2 * t + 1 = anchorN r t + 1 := by
    unfold anchorN
    have h64 := sixtyFour_mul_phaseWidth_le ht
    simp [phaseWidth] at h64
    omega
  rw [hspecial, hpascal]
  norm_num [Nat.choose_one_right]
  omega

theorem anchorHeadDigits_pred_append
    {r q : ℕ} (hq : 1 ≤ q) :
    anchorHeadDigits r q =
      anchorHeadDigits r (q - 1) ++ [r - 2 * (q - 1)] := by
  conv_lhs => rw [show q = (q - 1) + 1 by omega, anchorHeadDigits]

/-- One semantic scalar transition, assuming the displayed old state is canonical. -/
theorem scalarState_step
    {r t q : ℕ} (hq : 1 ≤ q) (hqt : q ≤ t) (hqr : 2 * q ≤ r)
    (hcanon : IsCanonical (q + 4)
      (scalarDigits r q (scalarResidual t q))) :
    scalarState r (q - 1) (scalarResidual t (q - 1)) =
      r + canonicalShadow (q + 4) (scalarState r q (scalarResidual t q)) := by
  let a := r - 2 * q + 2
  let z := scalarResidual t q
  let z' := scalarResidual t (q - 1)
  let fixed := anchorHeadDigits r (q - 1)
  have hanchor := anchorHeadDigits_pred_append (r := r) hq
  have ha : r - 2 * (q - 1) = a := by
    dsimp [a]
    omega
  have hspecialOld : r - 2 * q + 1 = a - 1 := by
    dsimp [a]
  have hspecialNew : r - 2 * (q - 1) + 1 = a + 1 := by
    dsimp [a]
    omega
  have hzstep : z' = 2 * q - 1 + canonicalShadow 2 z := by
    dsimp [z', z]
    exact scalarResidual_step hq hqt
  have hcanon' : IsCanonical (q + 4)
      (fixed ++ [a, a - 1] ++ canonicalDigits 2 z) := by
    dsimp [fixed, a, z]
    unfold scalarDigits at hcanon
    rw [hanchor, ha, hspecialOld] at hcanon
    dsimp [a] at hcanon
    have hconv : anchorHeadDigits r (q - 1) ++
          [r - 2 * q + 2] ++ [r - 2 * q + 1] ++
            canonicalDigits 2 (scalarResidual t q) =
        anchorHeadDigits r (q - 1) ++
          [r - 2 * q + 2, r - 2 * q + 1] ++
            canonicalDigits 2 (scalarResidual t q) := by
      simp [List.append_assoc]
    rw [hconv] at hcanon
    exact hcanon
  unfold scalarState scalarDigits
  rw [hanchor, ha, hspecialOld]
  simp only [List.append_assoc]
  have hcanon'' : IsCanonical (q + 4)
      (fixed ++ ([a] ++ ([a - 1] ++ canonicalDigits 2 z))) := by
    have hconv : fixed ++ [a, a - 1] ++ canonicalDigits 2 z =
        fixed ++ ([a] ++ ([a - 1] ++ canonicalDigits 2 z)) := by
      simp [List.append_assoc]
    rw [hconv] at hcanon'
    exact hcanon'
  change cascadeValue (q - 1 + 4)
      (fixed ++ ([a + 1] ++ canonicalDigits 2 z')) =
    r + canonicalShadow (q + 4)
      (cascadeValue (q + 4)
        (fixed ++ ([a] ++ ([a - 1] ++ canonicalDigits 2 z))))
  rw [canonicalShadow_eq_cascadeShadowValue hcanon'' rfl]
  unfold cascadeShadowValue
  rw [cascadeValue_append (q - 1 + 4) fixed
      ([a + 1] ++ canonicalDigits 2 z')]
  rw [cascadeValue_append (q + 4 - 1) fixed
      ([a] ++ ([a - 1] ++ canonicalDigits 2 z))]
  have hlen : fixed.length = q := by
    dsimp [fixed]
    rw [length_anchorHeadDigits]
    omega
  rw [hlen]
  have hidx : q + 4 - 1 - q = 3 := by omega
  have hidxNew : q - 1 + 4 - q = 3 := by omega
  rw [hidx, hidxNew]
  change cascadeValue (q - 1 + 4) fixed +
      ((a + 1).choose 3 + cascadeValue 2 (canonicalDigits 2 z')) =
    r + (cascadeValue (q + 4 - 1) fixed +
      (a.choose 3 + ((a - 1).choose 2 +
        cascadeValue 1 (canonicalDigits 2 z))))
  rw [cascadeValue_canonicalDigits (by omega)]
  have hzshadow : cascadeValue 1 (canonicalDigits 2 z) = canonicalShadow 2 z := rfl
  rw [hzshadow, hzstep]
  have hp1 : (a + 1).choose 3 = a.choose 2 + a.choose 3 := by
    simpa using Nat.choose_succ_succ a 2
  have hp2 : a.choose 2 = (a - 1) + (a - 1).choose 2 := by
    have haPos : 1 ≤ a := by
      dsimp [a]
      omega
    have h := Nat.choose_succ_succ (a - 1) 1
    have hasucc : (a - 1).succ = a := by omega
    rw [hasucc] at h
    simpa [Nat.choose_one_right] using h
  have hfixedIndex : q - 1 + 4 = q + 4 - 1 := by omega
  have har : a - 1 + (2 * q - 1) = r := by
    dsimp [a]
    omega
  rw [hp1, hp2]
  rw [hfixedIndex]
  omega

/-! ### Canonicity and capacity of the scalar states -/

theorem scalarResidual_five_four_three_bounds
    {t : ℕ} (ht : 6 ≤ t) :
    scalarResidual t 5 ≤ 20 ∧
      scalarResidual t 4 ≤ 16 ∧ scalarResidual t 3 ≤ 14 := by
  have hz6 := scalarResidual_le_sq (t := t) (q := 6) (by omega) ht
  have hs6 := canonicalShadow_mono 2 (by omega) hz6
  rw [show (6 : ℕ) ^ 2 = 36 by norm_num,
    canonicalShadow_two_thirtySix] at hs6
  have hz5 : scalarResidual t 5 ≤ 20 := by
    rw [show 5 = 6 - 1 by omega,
      scalarResidual_step (q := 6) (by omega) ht]
    omega
  have hs5 := canonicalShadow_mono 2 (by omega) hz5
  rw [canonicalShadow_two_twenty] at hs5
  have hz4 : scalarResidual t 4 ≤ 16 := by
    rw [show 4 = 5 - 1 by omega,
      scalarResidual_step (q := 5) (by omega) (by omega)]
    omega
  have hs4 := canonicalShadow_mono 2 (by omega) hz4
  rw [canonicalShadow_two_sixteen] at hs4
  have hz3 : scalarResidual t 3 ≤ 14 := by
    rw [show 3 = 4 - 1 by omega,
      scalarResidual_step (q := 4) (by omega) (by omega)]
    omega
  exact ⟨hz5, hz4, hz3⟩

theorem scalarResidual_le_thirtySix
    {t q : ℕ} (ht : 1 ≤ t) (hqt : q ≤ t) (hq : q ≤ 5) :
    scalarResidual t q ≤ 36 := by
  have hcases : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [scalarResidual_zero t ht]
    by_cases ht1 : t = 1
    · simp [ht1]
    by_cases ht2 : t = 2
    · simp [ht2]
    · simp [ht1, ht2]
  · by_cases ht1 : t = 1
    · subst t
      simp
    have ht2 : 2 ≤ t := by omega
    by_cases ht2' : t = 2
    · subst t
      rw [show 1 = 2 - 1 by omega,
        scalarResidual_step (q := 2) (by omega) (by omega),
        scalarResidual_top]
      simp
    have ht3 : 3 ≤ t := by omega
    have hz2 := (scalarResidual_two_bounds ht3).2
    have hs2 := canonicalShadow_mono 2 (by omega) hz2
    rw [canonicalShadow_two_eleven] at hs2
    rw [show 1 = 2 - 1 by omega,
      scalarResidual_step (q := 2) (by omega) (by omega)]
    omega
  · by_cases ht2 : t = 2
    · subst t
      simp
    exact (scalarResidual_two_bounds (by omega)).2.trans (by omega)
  · by_cases ht3 : t = 3
    · subst t
      simp
    by_cases ht4 : t = 4
    · subst t
      rw [show 3 = 4 - 1 by omega,
        scalarResidual_step (q := 4) (by omega) (by omega),
        scalarResidual_top]
      simp
    by_cases ht5 : t = 5
    · subst t
      have hz4 : scalarResidual 5 4 = 9 := by
        rw [show 4 = 5 - 1 by omega,
          scalarResidual_step (q := 5) (by omega) (by omega),
          scalarResidual_top]
        simp
      rw [show 3 = 4 - 1 by omega,
        scalarResidual_step (q := 4) (by omega) (by omega), hz4,
        canonicalShadow_two_nine]
      omega
    exact (scalarResidual_five_four_three_bounds (by omega)).2.2.trans
      (by omega)
  · by_cases ht4 : t = 4
    · subst t
      simp
    by_cases ht5 : t = 5
    · subst t
      rw [show 4 = 5 - 1 by omega,
        scalarResidual_step (q := 5) (by omega) (by omega),
        scalarResidual_top]
      simp
    exact (scalarResidual_five_four_three_bounds (by omega)).2.1.trans
      (by omega)
  · by_cases ht5 : t = 5
    · subst t
      simp
    exact (scalarResidual_five_four_three_bounds (by omega)).1.trans
      (by omega)

theorem scalarResidual_lt_special_choose_two
    {r t q : ℕ} (ht : IsMaximalAnchorIndex r t) (hqt : q ≤ t) :
    scalarResidual t q < (r - 2 * q + 1).choose 2 := by
  have h64 := sixtyFour_mul_phaseWidth_le ht
  simp [phaseWidth] at h64
  by_cases hq6 : 6 ≤ q
  · have hz := scalarResidual_le_sq hq6 hqt
    have hquad := choose_two_mul_gt_sq (show 2 ≤ q by omega)
    have hspecial : 2 * q ≤ r - 2 * q + 1 := by omega
    exact hz.trans_lt (hquad.trans_le (Nat.choose_le_choose 2 hspecial))
  · have hz := scalarResidual_le_thirtySix ht.1 hqt (by omega)
    have hspecial : 10 ≤ r - 2 * q + 1 := by omega
    have hchoose := Nat.choose_le_choose 2 hspecial
    have hbase : 36 < (10 : ℕ).choose 2 := by norm_num [Nat.choose]
    exact hz.trans_lt (hbase.trans_le hchoose)

theorem isCanonical_scalarDigits
    {r t q : ℕ} (ht : IsMaximalAnchorIndex r t) (hqt : q ≤ t) :
    IsCanonical (q + 4) (scalarDigits r q (scalarResidual t q)) := by
  let s := r - 2 * q + 1
  let tail := canonicalDigits 2 (scalarResidual t q)
  have h64 := sixtyFour_mul_phaseWidth_le ht
  simp [phaseWidth] at h64
  have hrq : 2 * q + 4 ≤ r := by omega
  have hheadHigh := isCanonical_anchorHeadDigits
    (r := r) (q := q) (show 2 * q + 2 ≤ r by omega)
  have hhead : IsCanonical (q + 4) (anchorHeadDigits r q) := by
    apply hheadHigh.lowerIndex (by omega)
    rw [length_anchorHeadDigits]
    omega
  have hresLt : scalarResidual t q < s.choose 2 := by
    dsimp [s]
    exact scalarResidual_lt_special_choose_two ht hqt
  have htailDigits : IsCanonical 2 tail := by
    dsimp [tail]
    exact isCanonical_canonicalDigits (by omega)
  have htailLt : ∀ d ∈ tail, d < s := by
    dsimp [tail]
    exact canonicalDigits_all_lt (by omega) hresLt
  have hs3 : 3 ≤ s := by
    dsimp [s]
    omega
  have htail : IsCanonical 3 (s :: tail) := by
    rw [isCanonical_succ_cons]
    exact ⟨hs3, htailLt, htailDigits⟩
  have hcross : ∀ a ∈ anchorHeadDigits r q, ∀ b ∈ s :: tail, b < a := by
    intro a ha b hb
    obtain ⟨j, hj, rfl⟩ := mem_anchorHeadDigits
      (q := q) (show 2 * q ≤ r by omega) ha
    have hba : b < s + 1 := by
      rcases List.mem_cons.mp hb with rfl | hb
      · omega
      · exact (htailLt b hb).trans_le (by omega)
    dsimp [s] at hba ⊢
    omega
  unfold scalarDigits
  simp only [List.append_assoc]
  change IsCanonical (q + 4)
    (anchorHeadDigits r q ++ (s :: tail))
  apply isCanonical_append hhead
  · simpa [length_anchorHeadDigits] using htail
  · exact hcross

theorem scalarState_lt_capacity
    {r t q : ℕ} (ht : IsMaximalAnchorIndex r t) (hqt : q ≤ t) :
    scalarState r q (scalarResidual t q) < (r + 4).choose (q + 4) := by
  have hcanon := isCanonical_scalarDigits ht hqt
  have h64 := sixtyFour_mul_phaseWidth_le ht
  simp [phaseWidth] at h64
  have hlevel : q + 4 ≤ r + 3 := by omega
  have hall : ∀ d ∈ scalarDigits r q (scalarResidual t q), d < r + 3 := by
    intro d hd
    unfold scalarDigits at hd
    simp only [List.append_assoc] at hd
    change d ∈ anchorHeadDigits r q ++
      ((r - 2 * q + 1) :: canonicalDigits 2 (scalarResidual t q)) at hd
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨j, hj, rfl⟩ := mem_anchorHeadDigits
        (q := q) (by omega) hd
      omega
    · rcases List.mem_cons.mp hd with rfl | hd
      · omega
      · have hlt := canonicalDigits_all_lt (k := 2)
          (m := scalarResidual t q) (A := r - 2 * q + 1)
          (by omega) (scalarResidual_lt_special_choose_two ht hqt) d hd
        omega
  have hsmall : scalarState r q (scalarResidual t q) <
      (r + 3).choose (q + 4) := by
    unfold scalarState
    exact cascadeValue_lt_choose_of_all_lt hlevel hcanon hall
  exact hsmall.trans_le (Nat.choose_le_choose _ (by omega))

/-- The scalar recurrence with all semantic side conditions discharged. -/
theorem scalarState_step_auto
    {r t q : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hq : 1 ≤ q) (hqt : q ≤ t) :
    scalarState r (q - 1) (scalarResidual t (q - 1)) =
      r + canonicalShadow (q + 4)
        (scalarState r q (scalarResidual t q)) := by
  apply scalarState_step hq hqt
  · have h64 := sixtyFour_mul_phaseWidth_le ht
    simp [phaseWidth] at h64
    omega
  · exact isCanonical_scalarDigits ht hqt

end Erdos776.Uniform


/-!
# Assembly of the symbolic lower-window envelope

The individual phase, rising-tail, generalized-envelope, and scalar proofs
are stitched here into one capacity-bounded supersolution from the completed
anchor down to level four.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

theorem phase_extension_segment
    {r t j : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t) :
    HasEnvelopeSegment r
      (phaseBirth r t j - phaseExtensionCount r t j)
      (phaseBirth r t j)
      (phaseState r t j (phaseExtensionCount r t j))
      (phaseState r t j 0) := by
  apply hasEnvelopeSegment_of_descent
  · have hu := four_le_phaseTop_at_phase ht hj hjK
    unfold phaseBirth phaseExtensionCount
    split <;> omega
  · intro L hL
    exact phase_extension_valid_auto hr ht hj hjK hL
  · intro L hL
    exact (phaseState_lt_capacity hr ht hj hjK hL).le

theorem completed_anchor_entry_segment
    {r t : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t) :
    HasEnvelopeSegment r (phaseBirth r t 1) (r - t - 1)
      (phaseState r t 1 0) (completedAnchorValue r t) := by
  let f : ℕ → ℕ := fun L =>
    if L = 0 then completedAnchorValue r t else phaseState r t 1 0
  have hseg : HasEnvelopeSegment r ((r - t - 1) - 1) (r - t - 1)
      (phaseState r t 1 0) (completedAnchorValue r t) := by
    apply hasEnvelopeSegment_of_descent (f := f)
    · have h64 := sixtyFour_mul_phaseWidth_le ht
      simp [phaseWidth] at h64
      omega
    · intro L hL
      have hL0 : L = 0 := by omega
      subst L
      simpa [f] using completedAnchor_to_phase_one ht
    · intro L hL
      have hcases : L = 0 ∨ L = 1 := by omega
      rcases hcases with rfl | rfl
      · simpa [f] using (completedAnchorValue_lt_capacity ht).le
      · have hcap := phaseState_lt_capacity hr ht
          (j := 1) (L := 0) (by omega)
          (show 1 ≤ phaseCount r t from (phaseCount_spec ht).1) (by omega)
        simpa [f, phaseBirth_one ht, show r - t - 1 - 1 = r - t - 2 by omega] using hcap.le
  simpa [phaseBirth_one ht, show r - t - 1 - 1 = r - t - 2 by omega] using hseg

theorem ordinary_harvest_segment
    {r t j : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j + 1 ≤ phaseCount r t) :
    HasEnvelopeSegment r (phaseBirth r t (j + 1))
      (phaseBirth r t j - phaseExtensionCount r t j)
      (phaseState r t (j + 1) 0)
      (phaseState r t j (phaseExtensionCount r t j)) := by
  let f : ℕ → ℕ := fun L => if L = 0 then
    phaseState r t j (phaseExtensionCount r t j)
    else phaseState r t (j + 1) 0
  have hjK' : j ≤ phaseCount r t := by omega
  have hseg := hasEnvelopeSegment_of_descent (r := r)
    (hi := phaseBirth r t j - phaseExtensionCount r t j)
    (len := 1) (f := f)
    (by
      have hu := four_le_phaseTop_at_phase ht hj hjK'
      unfold phaseBirth phaseExtensionCount
      split <;> omega)
    (by
      intro L hL
      have hL0 : L = 0 := by omega
      subst L
      simpa [f] using phase_harvest_valid_auto hr ht hj hjK)
    (by
      intro L hL
      have hcases : L = 0 ∨ L = 1 := by omega
      rcases hcases with rfl | rfl
      · simpa [f] using
          (phaseState_lt_capacity hr ht hj hjK' (L := phaseExtensionCount r t j)
            le_rfl).le
      · simpa [f, phaseBirth_succ ht hj hjK'] using
          (phaseState_lt_capacity hr ht (j := j + 1) (L := 0)
            (by omega) hjK (by omega)).le)
  simpa [f, phaseBirth_succ ht hj hjK'] using hseg

theorem ordinary_birth_to_anchor_segment
    {r t j : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hj : 1 ≤ j) (hjK : j ≤ phaseCount r t - 1) :
    HasEnvelopeSegment r (phaseBirth r t j) (r - t - 1)
      (phaseState r t j 0) (completedAnchorValue r t) := by
  induction j, hj using Nat.le_induction with
  | base => exact completed_anchor_entry_segment hr ht
  | succ j hj ih =>
      have hjK' : j ≤ phaseCount r t - 1 := by omega
      have hjCount : j ≤ phaseCount r t := by omega
      have hjNext : j + 1 ≤ phaseCount r t := by omega
      have hacc := ih hjK'
      have hphase := phase_extension_segment hr ht hj hjCount
      have hbirthLt : phaseBirth r t j < r - t - 1 := by
        have hb := phaseBirth_le_phaseBirth_one ht hj hjCount
        rw [phaseBirth_one ht] at hb
        have h64 := sixtyFour_mul_phaseWidth_le ht
        simp [phaseWidth] at h64
        omega
      have hext := hphase.stitch hacc (Nat.sub_le _ _) hbirthLt
      have hharvest := ordinary_harvest_segment hr ht hj hjNext
      exact hharvest.stitch hext
        (by rw [phaseBirth_succ ht hj hjCount]; omega)
        (lt_of_le_of_lt (Nat.sub_le _ _) hbirthLt)

theorem final_harvest_segment
    {r t : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t) :
    let K := phaseCount r t
    let j := K - 1
    let p := phaseTop r t K - 1
    HasEnvelopeSegment r (risingLevel r t p)
      (phaseBirth r t j - phaseExtensionCount r t j)
      (risingState r t p)
      (phaseState r t j (phaseExtensionCount r t j)) := by
  dsimp only
  let K := phaseCount r t
  let j := K - 1
  let p := phaseTop r t K - 1
  have hK : 5 ≤ K := by dsimp [K]; exact five_le_phaseCount ht
  have hj : 1 ≤ j := by dsimp [j]; omega
  have hjK : j ≤ K := by dsimp [j]; omega
  have hp2 : 2 ≤ p := by
    dsimp [p, K]
    exact risingEntryPosition_two_le ht
  have hpu : p < phaseTop r t K := by dsimp [p]; omega
  let f : ℕ → ℕ := fun L => if L = 0 then
    phaseState r t j (phaseExtensionCount r t j) else risingState r t p
  have hseg := hasEnvelopeSegment_of_descent (r := r)
    (hi := phaseBirth r t j - phaseExtensionCount r t j)
    (len := 1) (f := f)
    (by
      have hu := four_le_phaseTop_at_phase ht hj hjK
      unfold phaseBirth phaseExtensionCount
      split <;> omega)
    (by
      intro L hL
      have hL0 : L = 0 := by omega
      subst L
      simpa [f, K, j, p] using final_phase_harvest_to_rising hr ht)
    (by
      intro L hL
      have hcases : L = 0 ∨ L = 1 := by omega
      rcases hcases with rfl | rfl
      · simpa [f, K, j] using
          (phaseState_lt_capacity hr ht hj hjK
            (L := phaseExtensionCount r t j) le_rfl).le
      · have hcap := risingState_lt_capacity hr ht hp2 hpu
        have hlevel : risingLevel r t p =
            phaseBirth r t j - phaseExtensionCount r t j - 1 := by
          have hentry := risingEntryLevel ht
          have hsucc := phaseBirth_succ ht (j := K - 1) (by omega) (by omega)
          dsimp [K, j, p] at hentry hsucc ⊢
          rw [show phaseCount r t - 1 + 1 = phaseCount r t by omega] at hsucc
          omega
        simpa [f, hlevel] using hcap.le)
  have hlevel : risingLevel r t p =
      phaseBirth r t j - phaseExtensionCount r t j - 1 := by
    have hentry := risingEntryLevel ht
    have hsucc := phaseBirth_succ ht (j := K - 1) (by omega) (by omega)
    dsimp [K, j, p] at hentry hsucc ⊢
    rw [show phaseCount r t - 1 + 1 = phaseCount r t by omega] at hsucc
    omega
  change HasEnvelopeSegment r (risingLevel r t p)
    (phaseBirth r t j - phaseExtensionCount r t j)
    (risingState r t p)
    (phaseState r t j (phaseExtensionCount r t j))
  rw [hlevel]
  exact hseg

theorem rising_tail_segment
    {r t : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t) :
    let p := phaseTop r t (phaseCount r t) - 1
    HasEnvelopeSegment r (risingLevel r t 2) (risingLevel r t p)
      (risingState r t 2) (risingState r t p) := by
  dsimp only
  let u := phaseTop r t (phaseCount r t)
  let p₀ := u - 1
  have hp2 : 2 ≤ p₀ := by
    dsimp [p₀, u]
    exact risingEntryPosition_two_le ht
  have hpU : p₀ < u := by dsimp [p₀]; omega
  have hseg := hasEnvelopeSegment_of_descent (r := r)
    (hi := risingLevel r t p₀) (len := p₀ - 2)
    (f := fun L => risingState r t (p₀ - L))
    (by unfold risingLevel; omega)
    (by
      intro L hL
      let p := p₀ - L
      have hp3 : 3 ≤ p := by dsimp [p]; omega
      have hpU' : p < u := by dsimp [p]; omega
      have hlevel : risingLevel r t p₀ - L = risingLevel r t p := by
        dsimp [p]
        unfold risingLevel
        omega
      have hnext : p₀ - (L + 1) = p - 1 := by
        dsimp [p]
        omega
      change r + canonicalShadow (risingLevel r t p₀ - L)
          (risingState r t (p₀ - L)) ≤
        risingState r t (p₀ - (L + 1))
      rw [hlevel, show p₀ - L = p by rfl, hnext]
      by_cases hp : p = 3
      · rw [hp]
        exact risingState_final_step hr ht
      · exact risingState_step hr ht (by omega) (by
          dsimp [u] at hpU' ⊢
          exact hpU'))
    (by
      intro L hL
      let p := p₀ - L
      have hp2' : 2 ≤ p := by dsimp [p]; omega
      have hpU' : p < u := by dsimp [p]; omega
      have hlevel : risingLevel r t p₀ - L = risingLevel r t p := by
        dsimp [p]
        unfold risingLevel
        omega
      change risingState r t (p₀ - L) ≤
        (r + 4).choose (risingLevel r t p₀ - L)
      rw [hlevel]
      exact (risingState_lt_capacity hr ht hp2' (by
        dsimp [u] at hpU' ⊢
        exact hpU')).le)
  change HasEnvelopeSegment r (risingLevel r t 2) (risingLevel r t p₀)
    (risingState r t 2) (risingState r t p₀)
  have hlo : risingLevel r t p₀ - (p₀ - 2) = risingLevel r t 2 := by
    unfold risingLevel
    omega
  have hpbot : p₀ - (p₀ - 2) = 2 := by omega
  change HasEnvelopeSegment r (risingLevel r t p₀ - (p₀ - 2))
    (risingLevel r t p₀)
    (risingState r t (p₀ - (p₀ - 2))) (risingState r t (p₀ - 0)) at hseg
  rw [hlo, hpbot, Nat.sub_zero] at hseg
  exact hseg

theorem generalized_envelope_segment
    {r t : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t) :
    HasEnvelopeSegment r (t + 5) (t + phaseCount r t + 4)
      (generalizedEnvelopeState r t (t + 5))
      (generalizedEnvelopeState r t (t + phaseCount r t + 4)) := by
  let hi := t + phaseCount r t + 4
  let len := phaseCount r t - 1
  have hK : 5 ≤ phaseCount r t := five_le_phaseCount ht
  have hseg := hasEnvelopeSegment_of_descent (r := r) (hi := hi) (len := len)
    (f := fun L => generalizedEnvelopeState r t (hi - L))
    (by dsimp [hi, len]; omega)
    (by
      intro L hL
      let i := hi - L
      have hiLower : t + 6 ≤ i := by dsimp [i, hi, len] at *; omega
      have hiUpper : i ≤ t + phaseCount r t + 4 := by
        dsimp [i, hi]
        omega
      have hpred : hi - (L + 1) = i - 1 := by dsimp [i]; omega
      change r + canonicalShadow (hi - L)
          (generalizedEnvelopeState r t (hi - L)) ≤
        generalizedEnvelopeState r t (hi - (L + 1))
      rw [show hi - L = i by rfl, hpred]
      exact (generalizedEnvelope_step hr ht hiLower hiUpper).ge)
    (by
      intro L hL
      let i := hi - L
      have hiLower : t + 5 ≤ i := by dsimp [i, hi, len] at *; omega
      have hiUpper : i ≤ t + phaseCount r t + 4 := by
        dsimp [i, hi]
        omega
      change generalizedEnvelopeState r t i ≤ (r + 4).choose (hi - L)
      rw [show hi - L = i by rfl]
      exact (generalizedEnvelopeState_lt_capacity hr ht hiLower hiUpper).le)
  have hlo : hi - len = t + 5 := by dsimp [hi, len]; omega
  change HasEnvelopeSegment r (hi - len) hi
    (generalizedEnvelopeState r t (hi - len))
    (generalizedEnvelopeState r t (hi - 0)) at hseg
  rw [hlo, Nat.sub_zero] at hseg
  dsimp [hi] at hseg
  exact hseg

theorem envelope_collision_segment
    {r t : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t) :
    HasEnvelopeSegment r (t + 4) (t + 5)
      (scalarState r t 0) (generalizedEnvelopeState r t (t + 5)) := by
  let f : ℕ → ℕ := fun L => if L = 0 then
    generalizedEnvelopeState r t (t + 5) else scalarState r t 0
  have hseg := hasEnvelopeSegment_of_descent (r := r) (hi := t + 5)
    (len := 1) (f := f)
    (by omega)
    (by
      intro L hL
      have hL0 : L = 0 := by omega
      subst L
      simpa [f] using (generalizedEnvelope_collision hr ht).ge)
    (by
      intro L hL
      have hcases : L = 0 ∨ L = 1 := by omega
      rcases hcases with rfl | rfl
      · simpa [f] using
          (generalizedEnvelopeState_lt_capacity hr ht (by omega)
            (show t + 5 ≤ t + phaseCount r t + 4 by
              have := five_le_phaseCount ht
              omega)).le
      · simpa [f] using (scalarState_lt_capacity ht (q := t) le_rfl).le)
  have hlo : t + 5 - 1 = t + 4 := by omega
  rw [hlo] at hseg
  exact hseg

theorem scalar_collapse_segment
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t) :
    HasEnvelopeSegment r 4 (t + 4)
      (finalFourState r (scalarResidual t 0)) (scalarState r t 0) := by
  have hseg := hasEnvelopeSegment_of_descent (r := r) (hi := t + 4) (len := t)
    (f := fun L => scalarState r (t - L) (scalarResidual t (t - L)))
    (by omega)
    (by
      intro L hL
      let q := t - L
      have hq : 1 ≤ q := by dsimp [q]; omega
      have hnext : t - (L + 1) = q - 1 := by dsimp [q]; omega
      have hlevel : t + 4 - L = q + 4 := by dsimp [q]; omega
      change r + canonicalShadow (t + 4 - L)
          (scalarState r (t - L) (scalarResidual t (t - L))) ≤
        scalarState r (t - (L + 1)) (scalarResidual t (t - (L + 1)))
      rw [hlevel, show t - L = q by rfl, hnext]
      exact (scalarState_step_auto ht hq (by dsimp [q]; omega)).ge)
    (by
      intro L hL
      let q := t - L
      have hlevel : t + 4 - L = q + 4 := by dsimp [q]; omega
      change scalarState r (t - L) (scalarResidual t (t - L)) ≤
        (r + 4).choose (t + 4 - L)
      rw [hlevel]
      exact (scalarState_lt_capacity ht (q := q) (by dsimp [q]; omega)).le)
  have hlo : t + 4 - t = 4 := by omega
  rw [hlo] at hseg
  simp only [Nat.sub_self, Nat.sub_zero, scalarResidual_top] at hseg
  rw [scalarState_bottom_eq_finalFour] at hseg
  exact hseg

end Erdos776.Uniform


/-!
# Assembly interface for the phase/envelope segment

All top anchors and the scalar bottom collapse are already proved.  This file
checks that the remaining Section 4--9 phase construction has exactly the
right endpoints and inequalities to imply `LowerWindowFits` and hence the
global Erdős threshold.
-/

namespace Erdos776.Uniform

open Erdos776.KruskalKatona

/-- The level-three endpoint selected by the terminal scalar residual. -/
def finalThreeState (r t : ℕ) : ℕ :=
  if t = 1 then (r + 3).choose 3 + 1 else (r + 3).choose 3 + 3

/--
The assembly interface for Sections 4--10: a capacity-bounded supersolution
from the completed anchor down to `F₀(z₀)` at level four.
-/
def HasLowerWindowPhaseEnvelope (r t : ℕ) : Prop :=
  ∃ V : ℕ → ℕ,
    V (r - t - 1) = completedAnchorValue r t ∧
    V 4 = finalFourState r (scalarResidual t 0) ∧
    (∀ i, 4 ≤ i → i < r - t - 1 →
      r + canonicalShadow (i + 1) (V (i + 1)) ≤ V i) ∧
    ∀ i, 4 ≤ i → i ≤ r - t - 1 → V i ≤ (r + 4).choose i

/-- Sections 4--10, assembled into the exact lower-window obligation. -/
theorem hasLowerWindowPhaseEnvelope
    {r t : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t) :
    HasLowerWindowPhaseEnvelope r t := by
  let K := phaseCount r t
  let j := K - 1
  let p := phaseTop r t K - 1
  let A := r - t - 1
  have hK : 5 ≤ K := by dsimp [K]; exact five_le_phaseCount ht
  have hj : 1 ≤ j := by dsimp [j]; omega
  have hjLast : j ≤ phaseCount r t - 1 := by
    dsimp [j, K]
    exact le_rfl
  have hjCount : j ≤ phaseCount r t := by dsimp [j, K]; omega
  have hp2 : 2 ≤ p := by
    dsimp [p, K]
    exact risingEntryPosition_two_le ht
  have h64 := sixtyFour_mul_phaseWidth_le ht
  simp [phaseWidth] at h64
  have hbirthLt : phaseBirth r t j < A := by
    have hb := phaseBirth_le_phaseBirth_one ht hj hjCount
    rw [phaseBirth_one ht] at hb
    dsimp [A]
    omega
  have hendLt : phaseBirth r t j - phaseExtensionCount r t j < A :=
    lt_of_le_of_lt (Nat.sub_le _ _) hbirthLt
  have hfinalLevel : risingLevel r t p =
      phaseBirth r t j - phaseExtensionCount r t j - 1 := by
    have hentry := risingEntryLevel ht
    have hsucc := phaseBirth_succ ht (j := K - 1) (by omega) (by omega)
    dsimp [K, j, p] at hentry hsucc ⊢
    rw [show phaseCount r t - 1 + 1 = phaseCount r t by omega] at hsucc
    omega
  have hord := ordinary_birth_to_anchor_segment hr ht hj hjLast
  change HasEnvelopeSegment r (phaseBirth r t j) A
    (phaseState r t j 0) (completedAnchorValue r t) at hord
  have hphase := phase_extension_segment hr ht hj hjCount
  have hthroughPhase := hphase.stitch hord (Nat.sub_le _ _) hbirthLt
  have hfinal := final_harvest_segment hr ht
  change HasEnvelopeSegment r (risingLevel r t p)
    (phaseBirth r t j - phaseExtensionCount r t j)
    (risingState r t p)
    (phaseState r t j (phaseExtensionCount r t j)) at hfinal
  have hthroughFinal := hfinal.stitch hthroughPhase
    (by rw [hfinalLevel]; omega) hendLt
  have hrising := rising_tail_segment hr ht
  change HasEnvelopeSegment r (risingLevel r t 2) (risingLevel r t p)
    (risingState r t 2) (risingState r t p) at hrising
  have hrisingTopLt : risingLevel r t p < A := by
    rw [hfinalLevel]
    omega
  have hthroughRising := hrising.stitch hthroughFinal
    (by unfold risingLevel; omega) hrisingTopLt
  have henv0 := generalized_envelope_segment hr ht
  rw [generalizedEnvelope_top_eq_rising ht] at henv0
  have henv : HasEnvelopeSegment r (t + 5) (risingLevel r t 2)
      (generalizedEnvelopeState r t (t + 5)) (risingState r t 2) := by
    simpa [risingLevel, K] using henv0
  have henvTopLt : risingLevel r t 2 < A := by
    have : risingLevel r t 2 ≤ risingLevel r t p := by
      unfold risingLevel
      omega
    exact this.trans_lt hrisingTopLt
  have hthroughEnvelope := henv.stitch hthroughRising
    (by unfold risingLevel; omega) henvTopLt
  have hcollision := envelope_collision_segment hr ht
  have hcollisionTopLt : t + 5 < A := by
    have : t + 5 ≤ risingLevel r t 2 := by
      unfold risingLevel
      omega
    exact this.trans_lt henvTopLt
  have hthroughCollision := hcollision.stitch hthroughEnvelope
    (by omega) hcollisionTopLt
  have hscalar := scalar_collapse_segment ht
  have hscalarTopLt : t + 4 < A := by omega
  have hfull := hscalar.stitch hthroughCollision (by omega) hscalarTopLt
  rcases hfull with ⟨V, hV4, hVtop, hstep, hcap⟩
  exact ⟨V, hVtop, hV4, hstep, hcap⟩

theorem lowerWindowChain_le_phaseEnvelope
    {r t : ℕ} (ht : IsMaximalAnchorIndex r t)
    (hphase : HasLowerWindowPhaseEnvelope r t) :
    ∀ i, 4 ≤ i → i ≤ r - t - 1 →
      lowerWindowChain r i ≤ hphase.choose i := by
  intro i hi4 hii
  let V := hphase.choose
  have hVtop : V (r - t - 1) = completedAnchorValue r t :=
    hphase.choose_spec.1
  have hstart : lowerWindowChain r (r - t - 1) ≤ V (r - t - 1) := by
    rw [hVtop]
    exact lowerWindowChain_le_completedAnchor ht
  apply Nat.decreasingInduction'
      (P := fun k => lowerWindowChain r k ≤ V k)
      (m := i) (n := r - t - 1) ?_ hii
  · exact hstart
  · intro k hk hki ih
    have hk4 : 4 ≤ k := hi4.trans hki
    rw [lowerWindowChain_step r k (by omega),
      lowerWindowProfile_eq_of_le (by omega)]
    have hshadow := canonicalShadow_mono (k + 1) (by omega) ih
    exact (Nat.add_le_add_left hshadow r).trans
      (hphase.choose_spec.2.2.1 k hk4 (by omega))

theorem lowerWindowChain_three_le_final
    {r t : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hphase : HasLowerWindowPhaseEnvelope r t) :
    lowerWindowChain r 3 ≤ finalThreeState r t := by
  let V := hphase.choose
  have hi4 : 4 ≤ r - t - 1 := by
    have hlower := anchorThreshold_lower t ht.1
    have hTr := ht.2.1
    have hsum : 4 + (t + 1) ≤ r := by omega
    rw [show r - t - 1 = r - (t + 1) by omega]
    exact Nat.le_sub_of_add_le hsum
  have hchain4 : lowerWindowChain r 4 ≤ V 4 :=
    lowerWindowChain_le_phaseEnvelope ht hphase 4 le_rfl hi4
  rw [lowerWindowChain_step r 3 (by omega),
    lowerWindowProfile_eq_of_le (by omega)]
  have hshadow := canonicalShadow_mono 4 (by omega) hchain4
  have hV4 : V 4 = finalFourState r (scalarResidual t 0) :=
    hphase.choose_spec.2.1
  rw [hV4] at hshadow
  exact (Nat.add_le_add_left hshadow r).trans_eq
    (by simpa [finalThreeState] using
      finalFourState_scalar_step (r := r) (t := t) (by omega) ht.1)

theorem finalThreeState_le_capacity
    {r t : ℕ} (hr : 6 ≤ r) :
    finalThreeState r t ≤ (r + 4).choose 3 := by
  have hp : (r + 4).choose 3 =
      (r + 3).choose 2 + (r + 3).choose 3 := by
    simpa only [Nat.succ_eq_add_one,
      show r + 3 + 1 = r + 4 by omega] using
        Nat.choose_succ_succ (r + 3) 2
  have hcap : 3 ≤ (r + 3).choose 2 := by
    have hmono := Nat.choose_le_choose 2 (show 3 ≤ r + 3 by omega)
    norm_num at hmono
    exact hmono
  unfold finalThreeState
  split <;> omega

theorem lowerWindowChain_two_le_capacity_of_phaseEnvelope
    {r t : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hphase : HasLowerWindowPhaseEnvelope r t) :
    lowerWindowChain r 2 ≤ (r + 4).choose 2 := by
  have hthree := lowerWindowChain_three_le_final hr ht hphase
  rw [lowerWindowChain_step r 2 (by omega),
    lowerWindowProfile_eq_of_le (by omega)]
  have hshadow := canonicalShadow_mono 3 (by omega) hthree
  have hbottom := finalScalar_bottom (r := r) (t := t) (by omega) ht.1
  have hbottom' : r + canonicalShadow 3 (finalThreeState r t) =
      if t = 1 then (r + 4).choose 2 - 1 else (r + 4).choose 2 := by
    simpa [finalThreeState] using hbottom
  exact (Nat.add_le_add_left hshadow r).trans (by
    rw [hbottom']
    split <;> omega)

/-- The phase-envelope obligation implies the complete symbolic lower window. -/
theorem lowerWindowFits_of_phaseEnvelope
    {r t : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hphase : HasLowerWindowPhaseEnvelope r t) :
    LowerWindowFits r := by
  intro i hi2 hir
  by_cases hitop : i = r + 2
  · subst i
    simp
  have hir' : i ≤ r + 1 := by omega
  by_cases hi2eq : i = 2
  · subst i
    exact lowerWindowChain_two_le_capacity_of_phaseEnvelope hr ht hphase
  by_cases hi3eq : i = 3
  · subst i
    exact (lowerWindowChain_three_le_final hr ht hphase).trans
      (finalThreeState_le_capacity (by omega))
  have hi4 : 4 ≤ i := by omega
  by_cases hiPhase : i ≤ r - t - 1
  · exact (lowerWindowChain_le_phaseEnvelope ht hphase i hi4 hiPhase).trans
      (hphase.choose_spec.2.2.2 i hi4 hiPhase)
  · have hiAnchor : r - t ≤ i := by omega
    exact lowerWindowChain_fit_anchor_segment ht.2.1 hiAnchor hir'

/-- A phase envelope implies the global threshold. -/
theorem isErdosThreshold_of_phaseEnvelope
    {r t : ℕ} (hr : 378 ≤ r) (ht : IsMaximalAnchorIndex r t)
    (hphase : HasLowerWindowPhaseEnvelope r t) :
    IsErdosThreshold r (2 * r + 5) := by
  exact isErdosThreshold_of_lowerWindowFits r (by omega)
    (lowerWindowFits_of_phaseEnvelope hr ht hphase)

/-- The symbolic lower-window capacities hold uniformly from `r=378` onward. -/
theorem lowerWindowFits_of_ge_378 (r : ℕ) (hr : 378 ≤ r) :
    LowerWindowFits r := by
  let t := maximalAnchorIndex r
  have ht : IsMaximalAnchorIndex r t := maximalAnchorIndex_spec r hr
  exact lowerWindowFits_of_phaseEnvelope hr ht
    (hasLowerWindowPhaseEnvelope hr ht)

/-- The full middle-profile threshold in the non-computational uniform range. -/
theorem fullMiddleProfileThreshold_of_ge_378 (r : ℕ) (hr : 378 ≤ r) :
    FullMiddleProfileThreshold r := by
  exact fullMiddleProfileThreshold_of_lowerWindowFits r (by omega)
    (lowerWindowFits_of_ge_378 r hr)

/-- The global Erdős threshold in the non-computational uniform range. -/
theorem isErdosThreshold_of_ge_378 (r : ℕ) (hr : 378 ≤ r) :
    IsErdosThreshold r (2 * r + 5) := by
  exact isErdosThreshold_of_lowerWindowFits r (by omega)
    (lowerWindowFits_of_ge_378 r hr)

end Erdos776.Uniform
namespace Erdos776.Uniform

open Finset
open Erdos776.Antichain
open Filter Topology

/-- Occupied numerical levels are exactly the image of the cardinality function. -/
theorem occupiedLevels_eq_image_card {n : ℕ} (F : Family (Fin n)) :
    occupiedLevels F = F.image Finset.card := by
  ext i
  simp only [mem_occupiedLevels, Finset.mem_image]
  constructor
  · rintro ⟨hin, hnempty⟩
    obtain ⟨s, hslevel⟩ := hnempty
    exact ⟨s, (mem_level.mp hslevel).1, (mem_level.mp hslevel).2⟩
  · rintro ⟨s, hsF, rfl⟩
    have hle : s.card ≤ n := by
      have hle' := card_le_card (subset_univ s)
      simpa using hle'
    exact ⟨hle, ⟨s, mem_level.mpr ⟨hsF, rfl⟩⟩⟩

/-- The external occupied-profile event is exactly the contest admissibility event. -/
theorem occupiedMiddleProfileExists_iff_contest (n r : ℕ) :
    OccupiedMiddleProfileExists n r ↔
      ∃ F : Finset (Finset (Fin n)), OMA.S_erdos_776.IsAdmissible r n F := by
  constructor
  · rintro ⟨F, ⟨hanti, hmult⟩, hcard⟩
    refine ⟨F, hanti, ?_, ?_⟩
    · intro A hA
      have hocc : A.card ∈ occupiedLevels F := by
        rw [mem_occupiedLevels]
        have hle : A.card ≤ n := by
          have hle' := card_le_card (subset_univ A)
          simpa using hle'
        exact ⟨hle, ⟨A, mem_level.mpr ⟨hA, rfl⟩⟩⟩
      have hm := hmult A.card hocc
      simpa [level] using hm
    · rw [← occupiedLevels_eq_image_card F]
      exact hcard
  · rintro ⟨F, hanti, hmult, hcard⟩
    refine ⟨F, ⟨hanti, ?_⟩, ?_⟩
    · intro i hi
      obtain ⟨A, hAlevel⟩ := (mem_occupiedLevels.mp hi).2
      have hAF := (mem_level.mp hAlevel).1
      have hAcard := (mem_level.mp hAlevel).2
      have hm := hmult A hAF
      rw [← hAcard]
      simpa [level] using hm
    · rw [occupiedLevels_eq_image_card]
      exact hcard

/-- At the exact large-parameter threshold, no contest-admissible family exists. -/
theorem no_contest_admissible_at_threshold {r : ℕ} (hr : 378 ≤ r) :
    ¬ ∃ F : Finset (Finset (Fin (2 * r + 5))),
      OMA.S_erdos_776.IsAdmissible r (2 * r + 5) F := by
  have hthreshold := fullMiddleProfileThreshold_of_ge_378 r hr
  intro hcontest
  have hocc := (occupiedMiddleProfileExists_iff_contest (2 * r + 5) r).mpr hcontest
  have hfull := (occupiedMiddleProfileExists_iff_fullMiddleProfileExists
    (n := 2 * r + 5) (r := r) (by omega) (by omega)).mp hocc
  exact hthreshold.1 hfull

/-- Above the exact large-parameter threshold, a contest-admissible family exists. -/
theorem contest_admissible_exists_above_threshold {r n : ℕ} (hr : 378 ≤ r)
    (hn : 2 * r + 5 < n) :
    ∃ F : Finset (Finset (Fin n)), OMA.S_erdos_776.IsAdmissible r n F := by
  have hfull := (fullMiddleProfileThreshold_of_ge_378 r hr).2 n (by omega)
  have hocc := (occupiedMiddleProfileExists_iff_fullMiddleProfileExists
    (n := n) (r := r) (by omega) (by omega)).mpr hfull
  exact (occupiedMiddleProfileExists_iff_contest n r).mp hocc

/-- In the uniform symbolic range, the contest threshold is exactly `2r+5`. -/
theorem n0_eq_two_mul_add_five_of_ge_378 {r : ℕ} (hr : 378 ≤ r) :
    OMA.S_erdos_776.n₀ r = 2 * r + 5 := by
  unfold OMA.S_erdos_776.n₀
  apply IsGreatest.csSup_eq
  constructor
  · exact no_contest_admissible_at_threshold hr
  · intro x hx
    by_contra hxle
    have hs := contest_admissible_exists_above_threshold (r := r) (n := x) hr (by omega)
    exact hx hs

end Erdos776.Uniform

open Erdos776.Uniform
open Filter Topology

/-- Formal affirmative proof of Erdős Problem 776: the exact large-parameter threshold
`n₀(r)=2r+5` for `r≥378` implies the contest asymptotic. -/
theorem OMA.solution : type_of% @OMA.S_erdos_776.main := by
  have hconv : (fun r : ℕ => (OMA.S_erdos_776.n₀ r : ℝ) / (r : ℝ)) =ᶠ[atTop]
      fun r : ℕ => 2 + (5 : ℝ) / (r : ℝ) := by
    filter_upwards [eventually_ge_atTop 378] with r hr
    rw [n0_eq_two_mul_add_five_of_ge_378 hr]
    have hr0 : (r : ℝ) ≠ 0 := by
      exact_mod_cast (show r ≠ 0 by omega)
    field_simp [hr0]
    norm_num
    exact mul_comm 2 (r : ℝ)
  have h5 : Tendsto (fun r : ℕ => (5 : ℝ) / (r : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul tendsto_inv_atTop_nhds_zero_nat :
      Tendsto (fun r : ℕ => (5 : ℝ) * (r : ℝ)⁻¹) atTop (𝓝 (5 * 0)))
  have htarget : Tendsto (fun r : ℕ => 2 + (5 : ℝ) / (r : ℝ)) atTop (𝓝 2) := by
    simpa using tendsto_const_nhds.add h5
  exact (tendsto_congr' hconv).mpr htarget
