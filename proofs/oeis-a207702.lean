import OMAStatements.S_oeis_a207702
import Mathlib

namespace TMEngine
open Finset

section Engine
variable {R : Type*} [Fintype R] [DecidableEq R]
  (P : R → Prop) (Q : R → R → R → Prop) [DecidablePred P] [∀ a b c, Decidable (Q a b c)]

/-- Words over `R` whose letters satisfy `P` and whose consecutive triples satisfy `Q`. -/
def good3 {n : ℕ} (w : Fin n → R) : Prop :=
  (∀ i, P (w i)) ∧ ∀ (i : Fin n) (h : i.val + 2 < n), Q (w i) (w ⟨i.val + 1, by omega⟩) (w ⟨i.val + 2, h⟩)

instance {n : ℕ} : DecidablePred (good3 P Q (n := n)) := fun _ => by unfold good3; infer_instance

lemma cons_succ_mk {n : ℕ} (a : R) (w : Fin n → R) (k : ℕ) (h : k + 1 < n + 1) :
    (Fin.cons a w : Fin (n + 1) → R) ⟨k + 1, h⟩ = w ⟨k, by omega⟩ := rfl

lemma good3_cons {n : ℕ} (a : R) (w : Fin (n + 2) → R) :
    good3 P Q (Fin.cons a w : Fin (n + 3) → R) ↔
      P a ∧ Q a (w ⟨0, by omega⟩) (w ⟨1, by omega⟩) ∧ good3 P Q w := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1 0, ?_, fun i => ?_, fun i h => ?_⟩
    · have := h2 ⟨0, by omega⟩ (by simp)
      exact this
    · simpa using h1 i.succ
    · exact h2 ⟨i.val + 1, by omega⟩ (by simp; omega)
  · rintro ⟨ha, hq, h1, h2⟩
    refine ⟨fun i => ?_, fun i h => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using ha
      · simpa using h1 j
    · rcases i with ⟨_ | i, hi⟩
      · exact hq
      · exact h2 ⟨i, by omega⟩ (by simp at h ⊢; omega)

/-- The transfer recursion: `D m a b` counts the good words of length `m + 2` starting `a, b`. -/
def D : ℕ → R → R → ℕ
  | 0, a, b => if P a ∧ P b then 1 else 0
  | m + 1, a, b => ∑ c, if P a ∧ Q a b c then D m b c else 0

lemma sum_cons {n : ℕ} {M : Type*} [AddCommMonoid M] (f : (Fin (n + 1) → R) → M) :
    ∑ w, f w = ∑ c, ∑ w : Fin n → R, f (Fin.cons c w) := by
  rw [← (Fin.consEquiv fun _ => R).sum_comp, Fintype.sum_prod_type]
  rfl

lemma count_D (m : ℕ) (a b : R) :
    (∑ w : Fin m → R, if good3 P Q (Fin.cons a (Fin.cons b w) : Fin (m + 2) → R) then 1 else 0)
      = D P Q m a b := by
  induction m generalizing a b with
  | zero =>
    rw [Fintype.sum_unique]
    simp only [D]
    congr 1
    apply propext
    constructor
    · rintro ⟨h1, -⟩
      exact ⟨by simpa using h1 0, by simpa using h1 1⟩
    · rintro ⟨ha, hb⟩
      refine ⟨fun i => ?_, fun i h => absurd h (by omega)⟩
      fin_cases i
      · simpa using ha
      · simpa using hb
  | succ m ih =>
    rw [sum_cons]
    simp only [D]
    refine Finset.sum_congr rfl fun c _ => ?_
    have : ∀ w : Fin m → R, good3 P Q (Fin.cons a (Fin.cons b (Fin.cons c w)) : Fin (m + 3) → R) ↔
        (P a ∧ Q a b c) ∧ good3 P Q (Fin.cons b (Fin.cons c w) : Fin (m + 2) → R) := by
      intro w
      rw [good3_cons]
      simp [and_assoc]
    simp only [this]
    split_ifs with h
    · simpa [h] using ih b c
    · simp [h]

lemma count_total (m : ℕ) :
    (∑ w : Fin (m + 2) → R, if good3 P Q w then 1 else 0) = ∑ a, ∑ b, D P Q m a b := by
  rw [sum_cons]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [sum_cons]
  exact Finset.sum_congr rfl fun b _ => count_D P Q m a b

lemma count_one :
    (∑ w : Fin 1 → R, if good3 P Q w then 1 else 0) = ∑ a, if P a then 1 else 0 := by
  rw [sum_cons]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_unique]
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, -⟩
    simpa using h1 0
  · intro ha
    refine ⟨fun i => ?_, fun i h => absurd h (by omega)⟩
    fin_cases i
    simpa using ha

/-- Product decomposition of the transfer recursion along an equivalence `R ≃ R₁ × R₂`. -/
lemma D_prod {R₁ R₂ : Type*} [Fintype R₁] [DecidableEq R₁] [Fintype R₂] [DecidableEq R₂]
    (P₁ : R₁ → Prop) (Q₁ : R₁ → R₁ → R₁ → Prop) [DecidablePred P₁] [∀ a b c, Decidable (Q₁ a b c)]
    (P₂ : R₂ → Prop) (Q₂ : R₂ → R₂ → R₂ → Prop) [DecidablePred P₂] [∀ a b c, Decidable (Q₂ a b c)]
    (e : R ≃ R₁ × R₂) (hP : ∀ r, P r ↔ P₁ (e r).1 ∧ P₂ (e r).2)
    (hQ : ∀ a b c, Q a b c ↔ Q₁ (e a).1 (e b).1 (e c).1 ∧ Q₂ (e a).2 (e b).2 (e c).2) :
    ∀ m a b, D P Q m a b = D P₁ Q₁ m (e a).1 (e b).1 * D P₂ Q₂ m (e a).2 (e b).2 := by
  intro m
  induction m with
  | zero =>
    intro a b
    simp only [D, hP]
    split_ifs <;> simp_all
  | succ m ih =>
    intro a b
    simp only [D]
    rw [← e.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun c₁ _ => Finset.sum_congr rfl fun c₂ _ => ?_
    simp only [ih, hP, hQ, Equiv.apply_symm_apply]
    split_ifs <;> simp_all

/-- Polynomial certificate: if `β` satisfies the transfer identities coefficientwise, then
`L * D m a b` is the polynomial with coefficients `β a b`. -/
lemma D_poly (d L : ℕ) (β : R → R → ℕ → ℤ)
    (h0 : ∀ a b, (L : ℤ) * (if P a ∧ P b then 1 else 0) = β a b 0)
    (hs : ∀ a b, ∀ j ∈ range (d + 1),
      ∑ k ∈ range (d + 1), β a b k * (k.choose j : ℤ) = ∑ c, if P a ∧ Q a b c then β b c j else 0) :
    ∀ m a b, (L : ℤ) * D P Q m a b = ∑ k ∈ range (d + 1), β a b k * (m : ℤ) ^ k := by
  intro m
  induction m with
  | zero =>
    intro a b
    simp only [D, Nat.cast_ite, Nat.cast_one, h0, CharP.cast_eq_zero]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k _ hk; simp [hk]
    · intro h; simp at h
  | succ m ih =>
    intro a b
    simp only [D]
    push_cast
    rw [Finset.mul_sum]
    have e1 : ∀ c, (L : ℤ) * (if P a ∧ Q a b c then (D P Q m b c : ℤ) else 0) =
        ∑ j ∈ range (d + 1), (if P a ∧ Q a b c then β b c j else 0) * (m : ℤ) ^ j := by
      intro c
      split_ifs
      · exact ih b c
      · simp
    rw [Finset.sum_congr rfl fun c _ => e1 c, Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    rw [Finset.sum_congr rfl fun j hj => by rw [← hs a b j hj]]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [add_pow]
    simp only [one_pow, mul_one]
    rw [Finset.mul_sum]
    have hk' : k + 1 ≤ d + 1 := by simp at hk; omega
    rw [← Finset.sum_range_add_sum_Ico _ hk']
    have : ∑ x ∈ Ico (k + 1) (d + 1), β a b k * (k.choose x : ℤ) * (m : ℤ) ^ x = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      simp at hx
      simp [Nat.choose_eq_zero_of_lt (by omega : k < x)]
    rw [this, add_zero]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring

end Engine

end TMEngine

namespace A207702
open OMA.S_oeis_a207702 TMEngine Finset

/-- Bits of a code. -/
def bv {N : ℕ} (a : Fin N) (j : ℕ) : ℕ := a.val / 2 ^ j % 2

def P4 (a : Fin (2 ^ 4)) : Prop := ∀ j < 3, ¬ (bv a j = 0 ∧ bv a (j + 1) = 0)
def Q4 (a b c : Fin (2 ^ 4)) : Prop := ∀ j < 4, ¬ (bv a j = bv b j ∧ bv b j ≠ bv c j)
def P3 (a : Fin (2 ^ 3)) : Prop := ∀ j < 2, ¬ (bv a j = 0 ∧ bv a (j + 1) = 0)
def Q3 (a b c : Fin (2 ^ 3)) : Prop := ∀ j < 3, ¬ (bv a j = bv b j ∧ bv b j ≠ bv c j)
instance : DecidablePred P4 := fun _ => by unfold P4; infer_instance
instance : DecidablePred P3 := fun _ => by unfold P3; infer_instance
instance (a b c) : Decidable (Q4 a b c) := by unfold Q4; infer_instance
instance (a b c) : Decidable (Q3 a b c) := by unfold Q3; infer_instance

/-- Entry `j` of a row (`0` past the end). -/
def rg (r : Fin 7 → Fin 2) (j : ℕ) : ℕ := if h : j < 7 then (r ⟨j, h⟩ : ℕ) else 0

def P7 (r : Fin 7 → Fin 2) : Prop := ∀ j < 5, ¬ (rg r j = 0 ∧ rg r (j + 2) = 0)
def Q7 (r s t : Fin 7 → Fin 2) : Prop := ∀ j < 7, ¬ (rg r j = rg s j ∧ rg s j ≠ rg t j)
instance : DecidablePred P7 := fun _ => by unfold P7; infer_instance
instance (a b c) : Decidable (Q7 a b c) := by unfold Q7; infer_instance

lemma rg_le (r : Fin 7 → Fin 2) (j : ℕ) : rg r j ≤ 1 := by
  unfold rg; split_ifs
  · have := (r ⟨j, by assumption⟩).2; omega
  · omega

lemma get_eq {n : ℕ} (x : Fin n → Fin 7 → Fin 2) (i j : ℕ) (hi : i < n) :
    OMA.S_oeis_a207702.get x i j = rg (x ⟨i, hi⟩) j := by
  unfold OMA.S_oeis_a207702.get rg; by_cases hj : j < 7 <;> simp [hi, hj]

lemma avoids_iff {n : ℕ} (x : Fin n → Fin 7 → Fin 2) : avoids x = true ↔ good3 P7 Q7 x := by
  unfold avoids good3 P7 Q7
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j hj => ?_, fun i hi j hj => ?_⟩
    · have := h1 i i.2 j (by omega)
      rw [get_eq x i j i.2, get_eq x i (j + 1) i.2, get_eq x i (j + 2) i.2] at this
      have := rg_le (x i) (j + 1)
      simp only [Fin.eta, ne_eq, Prod.mk.injEq] at *
      omega
    · have := h2 i (by omega) j hj
      rw [get_eq x i j i.2, get_eq x (i + 1) j (by omega), get_eq x (i + 2) j (by omega)] at this
      have := rg_le (x i) j
      have := rg_le (x ⟨i + 1, by omega⟩) j
      have := rg_le (x ⟨i + 2, by omega⟩) j
      simp only [Fin.eta, ne_eq, Prod.mk.injEq] at *
      omega
  · rintro ⟨h1, h2⟩
    refine ⟨fun i hi j hj => ?_, fun i hi j hj => ?_⟩
    · rw [get_eq x i j hi, get_eq x i (j + 1) hi, get_eq x i (j + 2) hi]
      have := h1 ⟨i, hi⟩ j (by omega)
      simp only [ne_eq, Prod.mk.injEq]
      omega
    · rw [get_eq x i j (by omega), get_eq x (i + 1) j (by omega), get_eq x (i + 2) j (by omega)]
      have := h2 ⟨i, by omega⟩ (by simp; omega) j hj
      dsimp only at this
      have := rg_le (x ⟨i, by omega⟩) j
      have := rg_le (x ⟨i + 1, by omega⟩) j
      have := rg_le (x ⟨i + 2, by omega⟩) j
      simp only [ne_eq, Prod.mk.injEq] at *
      omega

/-- Splitting a row into its even and odd positions. -/
def sp : (Fin 7 → Fin 2) ≃ (Fin 4 → Fin 2) × (Fin 3 → Fin 2) where
  toFun r := (fun j => r ⟨2 * j.val, by omega⟩, fun j => r ⟨2 * j.val + 1, by omega⟩)
  invFun p i := if h : i.val % 2 = 0 then p.1 ⟨i.val / 2, by omega⟩ else p.2 ⟨i.val / 2, by omega⟩
  left_inv r := by funext i; fin_cases i <;> rfl
  right_inv p := by
    rcases p with ⟨p, q⟩
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;> fin_cases j <;> rfl

def e : (Fin 7 → Fin 2) ≃ Fin (2 ^ 4) × Fin (2 ^ 3) :=
  sp.trans (Equiv.prodCongr finFunctionFinEquiv finFunctionFinEquiv)

lemma bv_e1 (r : Fin 7 → Fin 2) (j : ℕ) (hj : j < 4) : bv (e r).1 j = rg r (2 * j) := by
  have h := finFunctionFinEquiv_symm_apply_val (e r).1 ⟨j, hj⟩
  simp only at h
  unfold bv rg
  rw [dif_pos (by omega), ← h]
  simp [e, sp]

lemma bv_e2 (r : Fin 7 → Fin 2) (j : ℕ) (hj : j < 3) : bv (e r).2 j = rg r (2 * j + 1) := by
  have h := finFunctionFinEquiv_symm_apply_val (e r).2 ⟨j, hj⟩
  simp only at h
  unfold bv rg
  rw [dif_pos (by omega), ← h]
  simp [e, sp]

lemma hP (r : Fin 7 → Fin 2) : P7 r ↔ P4 (e r).1 ∧ P3 (e r).2 := by
  unfold P7 P4 P3
  constructor
  · intro h
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rw [bv_e1 r j (by omega), bv_e1 r (j + 1) (by omega)]
      have := h (2 * j) (by omega)
      rwa [show 2 * j + 2 = 2 * (j + 1) by ring] at this
    · rw [bv_e2 r j (by omega), bv_e2 r (j + 1) (by omega)]
      have := h (2 * j + 1) (by omega)
      rwa [show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by ring] at this
  · rintro ⟨h1, h2⟩ j hj
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
    · have := h1 k (by omega)
      rw [bv_e1 r k (by omega), bv_e1 r (k + 1) (by omega)] at this
      rwa [show 2 * k + 2 = 2 * (k + 1) by ring]
    · have := h2 k (by omega)
      rw [bv_e2 r k (by omega), bv_e2 r (k + 1) (by omega)] at this
      rwa [show 2 * k + 1 + 2 = 2 * (k + 1) + 1 by ring]

lemma hQ (r s t : Fin 7 → Fin 2) :
    Q7 r s t ↔ Q4 (e r).1 (e s).1 (e t).1 ∧ Q3 (e r).2 (e s).2 (e t).2 := by
  unfold Q7 Q4 Q3
  constructor
  · intro h
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rw [bv_e1 r j hj, bv_e1 s j hj, bv_e1 t j hj]; exact h (2 * j) (by omega)
    · rw [bv_e2 r j hj, bv_e2 s j hj, bv_e2 t j hj]; exact h (2 * j + 1) (by omega)
  · rintro ⟨h1, h2⟩ j hj
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
    · have := h1 k (by omega)
      rwa [bv_e1 r k (by omega), bv_e1 s k (by omega), bv_e1 t k (by omega)] at this
    · have := h2 k (by omega)
      rwa [bv_e2 r k (by omega), bv_e2 s k (by omega), bv_e2 t k (by omega)] at this

def tb4 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [24, 0, 0, 0, 0], [24, 36, 12, 0, 0], [24, 24, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [24, 66, 67, 30, 5], [24, 52, 36, 8, 0], [0, 0, 0, 0, 0], [24, 24, 0, 0, 0], [24, 60, 48, 12, 0], [24, 48, 24, 0, 0]],
   [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [24, 36, 12, 0, 0], [24, 0, 0, 0, 0], [24, 24, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [24, 36, 12, 0, 0], [24, 60, 48, 12, 0], [0, 0, 0, 0, 0], [24, 60, 48, 12, 0], [24, 24, 0, 0, 0], [24, 48, 24, 0, 0]],
   [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [24, 24, 0, 0, 0], [24, 24, 0, 0, 0], [24, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [24, 60, 48, 12, 0], [24, 36, 12, 0, 0], [0, 0, 0, 0, 0], [24, 48, 24, 0, 0], [24, 48, 24, 0, 0], [24, 24, 0, 0, 0]],
   [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [24, 66, 67, 30, 5], [24, 36, 12, 0, 0], [24, 60, 48, 12, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [24, 0, 0, 0, 0], [24, 24, 0, 0, 0], [0, 0, 0, 0, 0], [24, 52, 36, 8, 0], [24, 24, 0, 0, 0], [24, 48, 24, 0, 0]],
   [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [24, 52, 36, 8, 0], [24, 60, 48, 12, 0], [24, 36, 12, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [24, 24, 0, 0, 0], [24, 0, 0, 0, 0], [0, 0, 0, 0, 0], [24, 36, 12, 0, 0], [24, 48, 24, 0, 0], [24, 24, 0, 0, 0]],
   [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]],
   [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [24, 24, 0, 0, 0], [24, 60, 48, 12, 0], [24, 48, 24, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [24, 52, 36, 8, 0], [24, 36, 12, 0, 0], [0, 0, 0, 0, 0], [24, 0, 0, 0, 0], [24, 36, 12, 0, 0], [24, 24, 0, 0, 0]],
   [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [24, 60, 48, 12, 0], [24, 24, 0, 0, 0], [24, 48, 24, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [24, 24, 0, 0, 0], [24, 48, 24, 0, 0], [0, 0, 0, 0, 0], [24, 36, 12, 0, 0], [24, 0, 0, 0, 0], [24, 24, 0, 0, 0]],
   [[0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [24, 48, 24, 0, 0], [24, 48, 24, 0, 0], [24, 24, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [24, 48, 24, 0, 0], [24, 24, 0, 0, 0], [0, 0, 0, 0, 0], [24, 24, 0, 0, 0], [24, 24, 0, 0, 0], [24, 0, 0, 0, 0]]]
def tb3 : List (List (List ℤ)) :=
  [[[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [6, 0, 0, 0], [6, 6, 0, 0], [0, 0, 0, 0], [6, 13, 9, 2], [6, 6, 0, 0], [6, 12, 6, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [6, 6, 0, 0], [6, 0, 0, 0], [0, 0, 0, 0], [6, 9, 3, 0], [6, 12, 6, 0], [6, 6, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [6, 13, 9, 2], [6, 9, 3, 0], [0, 0, 0, 0], [6, 0, 0, 0], [6, 9, 3, 0], [6, 6, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [6, 6, 0, 0], [6, 12, 6, 0], [0, 0, 0, 0], [6, 9, 3, 0], [6, 0, 0, 0], [6, 6, 0, 0]],
   [[0, 0, 0, 0], [0, 0, 0, 0], [6, 12, 6, 0], [6, 6, 0, 0], [0, 0, 0, 0], [6, 6, 0, 0], [6, 6, 0, 0], [6, 0, 0, 0]]]

def β4 (a b : Fin (2 ^ 4)) (k : ℕ) : ℤ := ((tb4.getD a.val []).getD b.val []).getD k 0
def β3 (a b : Fin (2 ^ 3)) (k : ℕ) : ℤ := ((tb3.getD a.val []).getD b.val []).getD k 0

lemma cert4 : ∀ m a b, ((24 : ℕ) : ℤ) * D P4 Q4 m a b = ∑ k ∈ range (4 + 1), β4 a b k * (m : ℤ) ^ k :=
  D_poly P4 Q4 4 24 β4 (by decide +kernel) (by decide +kernel)

lemma cert3 : ∀ m a b, ((6 : ℕ) : ℤ) * D P3 Q3 m a b = ∑ k ∈ range (3 + 1), β3 a b k * (m : ℤ) ^ k :=
  D_poly P3 Q3 3 6 β3 (by decide +kernel) (by decide +kernel)


def f4 (m : ℕ) : ℕ := ∑ a, ∑ b, D P4 Q4 m a b
def f3 (m : ℕ) : ℕ := ∑ a, ∑ b, D P3 Q3 m a b

lemma tot4 : (∑ a, ∑ b, β4 a b 0) = 1536 ∧ (∑ a, ∑ b, β4 a b 1) = 2236 ∧
    (∑ a, ∑ b, β4 a b 2) = 1070 ∧ (∑ a, ∑ b, β4 a b 3) = 188 ∧ (∑ a, ∑ b, β4 a b 4) = 10 := by
  decide +kernel

lemma tot3 : (∑ a, ∑ b, β3 a b 0) = 150 ∧ (∑ a, ∑ b, β3 a b 1) = 170 ∧
    (∑ a, ∑ b, β3 a b 2) = 54 ∧ (∑ a, ∑ b, β3 a b 3) = 4 := by
  decide +kernel

lemma f4_eq (m : ℕ) :
    (24 : ℤ) * f4 m = 1536 + 2236 * m + 1070 * m ^ 2 + 188 * m ^ 3 + 10 * m ^ 4 := by
  have c := cert4 m
  simp only [Nat.cast_ofNat] at c
  have h : (24 : ℤ) * f4 m = ∑ k ∈ range (4 + 1), (∑ a, ∑ b, β4 a b k) * (m : ℤ) ^ k := by
    unfold f4
    push_cast
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum, c]
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
    simp_rw [Finset.sum_mul]
  obtain ⟨t0, t1, t2, t3, t4⟩ := tot4
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, t0, t1, t2, t3, t4]
  ring

lemma f3_eq (m : ℕ) :
    (6 : ℤ) * f3 m = 150 + 170 * m + 54 * m ^ 2 + 4 * m ^ 3 := by
  have c := cert3 m
  simp only [Nat.cast_ofNat] at c
  have h : (6 : ℤ) * f3 m = ∑ k ∈ range (3 + 1), (∑ a, ∑ b, β3 a b k) * (m : ℤ) ^ k := by
    unfold f3
    push_cast
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum, c]
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm, Finset.sum_comm]
    simp_rw [Finset.sum_mul]
  obtain ⟨t0, t1, t2, t3⟩ := tot3
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, t0, t1, t2, t3]
  ring

lemma card_eq (n : ℕ) :
    ((Finset.univ : Finset (Fin n → Fin 7 → Fin 2)).filter (fun x => avoids x)).card =
      ∑ x : Fin n → Fin 7 → Fin 2, if good3 P7 Q7 x then 1 else 0 := by
  rw [Finset.card_filter]
  exact Finset.sum_congr rfl fun x _ => by simp only [avoids_iff]

lemma a_two (m : ℕ) : a (m + 2) = ((f4 m * f3 m : ℕ) : ℤ) := by
  have key : ∑ a, ∑ b, D P7 Q7 m a b = f4 m * f3 m := by
    simp_rw [D_prod P7 Q7 P4 Q4 P3 Q3 e hP hQ m]
    rw [Fintype.sum_equiv e (fun a => ∑ b, D P4 Q4 m (e a).1 (e b).1 * D P3 Q3 m (e a).2 (e b).2)
      (fun p : Fin (2 ^ 4) × Fin (2 ^ 3) => ∑ b, D P4 Q4 m p.1 (e b).1 * D P3 Q3 m p.2 (e b).2)
      (fun _ => rfl)]
    simp_rw [fun p : Fin (2 ^ 4) × Fin (2 ^ 3) => Fintype.sum_equiv e (fun b => D P4 Q4 m p.1 (e b).1 * D P3 Q3 m p.2 (e b).2)
      (fun q : Fin (2 ^ 4) × Fin (2 ^ 3) => D P4 Q4 m p.1 q.1 * D P3 Q3 m p.2 q.2) (fun _ => rfl)]
    unfold f4 f3
    simp only [Fintype.sum_prod_type, Finset.sum_mul_sum]
  unfold a
  rw [card_eq, count_total, key]

lemma a_one : a 1 = 40 := by
  unfold a
  rw [card_eq, count_one]
  rw [Fintype.sum_equiv e (fun r => if P7 r then 1 else 0)
    (fun p => if P4 p.1 ∧ P3 p.2 then 1 else 0) (fun r => by simp only [hP])]
  decide +kernel

/-- The closed form. -/
def pp (n : ℕ) : ℚ := (n : ℚ) * (162 - 327 * (n : ℚ) - 881 * (n : ℚ) ^ 2 + 1296 * (n : ℚ) ^ 3 +
  997 * (n : ℚ) ^ 4 + 183 * (n : ℚ) ^ 5 + 10 * (n : ℚ) ^ 6) / 36

lemma a_eq (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = pp n := by
  rcases n with _ | _ | m
  · omega
  · rw [a_one]; norm_num [pp]
  · rw [a_two]
    have h4 : (24 : ℚ) * f4 m = 1536 + 2236 * m + 1070 * m ^ 2 + 188 * m ^ 3 + 10 * m ^ 4 := by
      exact_mod_cast f4_eq m
    have h3 : (6 : ℚ) * f3 m = 150 + 170 * m + 54 * m ^ 2 + 4 * m ^ 3 := by
      exact_mod_cast f3_eq m
    have e4 : (f4 m : ℚ) = (1536 + 2236 * m + 1070 * m ^ 2 + 188 * m ^ 3 + 10 * m ^ 4) / 24 := by
      linarith
    have e3 : (f3 m : ℚ) = (150 + 170 * m + 54 * m ^ 2 + 4 * m ^ 3) / 6 := by linarith
    push_cast
    rw [e4, e3]
    unfold pp
    push_cast
    ring

lemma c_eq (n : ℕ) : (if n < 1 then 0 else (a n : ℚ)) = pp n := by
  split_ifs with h
  · have : n = 0 := by omega
    subst this; simp [pp]
  · exact a_eq n (by omega)

lemma coeff_F_mul_X (F : PowerSeries ℚ) (hF : F = PowerSeries.mk pp) (k n : ℕ) :
    PowerSeries.coeff n (F * PowerSeries.X ^ k) = if k ≤ n then pp (n - k) else 0 := by
  subst hF
  simp only [PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk]

lemma gf : PowerSeries.mk pp * (1 - PowerSeries.X) ^ 8 = (2 : PowerSeries ℚ) * PowerSeries.X *
    (20 + 640 * PowerSeries.X + 775 * PowerSeries.X ^ 2 - 1013 * PowerSeries.X ^ 3 +
      259 * PowerSeries.X ^ 4 + 31 * PowerSeries.X ^ 5 - 12 * PowerSeries.X ^ 6) := by
  set F := PowerSeries.mk pp with hF
  have el : F * (1 - PowerSeries.X) ^ 8 = F - PowerSeries.C 8 * (F * PowerSeries.X ^ 1) + PowerSeries.C 28 * (F * PowerSeries.X ^ 2) - PowerSeries.C 56 * (F * PowerSeries.X ^ 3) + PowerSeries.C 70 * (F * PowerSeries.X ^ 4) - PowerSeries.C 56 * (F * PowerSeries.X ^ 5) + PowerSeries.C 28 * (F * PowerSeries.X ^ 6) - PowerSeries.C 8 * (F * PowerSeries.X ^ 7) + F * PowerSeries.X ^ 8 := by
    simp only [map_ofNat, pow_one]
    ring
  have er : (2 : PowerSeries ℚ) * PowerSeries.X *
      (20 + 640 * PowerSeries.X + 775 * PowerSeries.X ^ 2 - 1013 * PowerSeries.X ^ 3 +
        259 * PowerSeries.X ^ 4 + 31 * PowerSeries.X ^ 5 - 12 * PowerSeries.X ^ 6) = PowerSeries.C 40 * PowerSeries.X ^ 1 + PowerSeries.C 1280 * PowerSeries.X ^ 2 + PowerSeries.C 1550 * PowerSeries.X ^ 3 - PowerSeries.C 2026 * PowerSeries.X ^ 4 + PowerSeries.C 518 * PowerSeries.X ^ 5 + PowerSeries.C 62 * PowerSeries.X ^ 6 - PowerSeries.C 24 * PowerSeries.X ^ 7 := by
    simp only [map_ofNat, pow_one]
    ring
  rw [el, er]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_F_mul_X F hF,
    PowerSeries.coeff_X_pow]
  rw [hF, PowerSeries.coeff_mk]
  by_cases hn : 8 ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    rw [if_pos (show 1 ≤ m + 8 by omega)]
    rw [if_pos (show 2 ≤ m + 8 by omega)]
    rw [if_pos (show 3 ≤ m + 8 by omega)]
    rw [if_pos (show 4 ≤ m + 8 by omega)]
    rw [if_pos (show 5 ≤ m + 8 by omega)]
    rw [if_pos (show 6 ≤ m + 8 by omega)]
    rw [if_pos (show 7 ≤ m + 8 by omega)]
    rw [if_pos (show 8 ≤ m + 8 by omega)]
    rw [if_neg (show ¬ (m + 8 = 1) by omega)]
    rw [if_neg (show ¬ (m + 8 = 2) by omega)]
    rw [if_neg (show ¬ (m + 8 = 3) by omega)]
    rw [if_neg (show ¬ (m + 8 = 4) by omega)]
    rw [if_neg (show ¬ (m + 8 = 5) by omega)]
    rw [if_neg (show ¬ (m + 8 = 6) by omega)]
    rw [if_neg (show ¬ (m + 8 = 7) by omega)]
    rw [show m + 8 - 1 = m + 7 from by omega]
    rw [show m + 8 - 2 = m + 6 from by omega]
    rw [show m + 8 - 3 = m + 5 from by omega]
    rw [show m + 8 - 4 = m + 4 from by omega]
    rw [show m + 8 - 5 = m + 3 from by omega]
    rw [show m + 8 - 6 = m + 2 from by omega]
    rw [show m + 8 - 7 = m + 1 from by omega]
    rw [show m + 8 - 8 = m + 0 from by omega]
    simp only [pp]
    push_cast
    ring
  · have hn' : n < 8 := by omega
    interval_cases n <;> norm_num [pp]

end A207702

theorem OMA.solution : type_of% @OMA.S_oeis_a207702.main := by
  have hc : (fun n => if n < 1 then (0 : ℚ) else (OMA.S_oeis_a207702.a n : ℚ)) = A207702.pp :=
    funext A207702.c_eq
  refine ⟨?_, fun n hn => A207702.a_eq n hn⟩
  rw [hc]
  exact A207702.gf
