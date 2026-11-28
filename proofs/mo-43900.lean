import OMAStatements.S_mo_43900
import Mathlib.Algebra.CharP.Reduced
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Set.Card
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OMA.Density43900.Affine

abbrev F (i : ℕ) := GaloisField 2 (i + 3)

structure A (i : ℕ) where
  slope : (F i)ˣ
  offset : F i

private theorem A.ext {i : ℕ} {x y : A i}
    (hs : x.slope = y.slope) (ho : x.offset = y.offset) : x = y := by
  cases x
  cases y
  cases hs
  cases ho
  rfl

private def equivProd (i : ℕ) : A i ≃ (F i)ˣ × F i where
  toFun x := (x.slope, x.offset)
  invFun x := ⟨x.1, x.2⟩
  left_inv := by rintro ⟨_, _⟩; rfl
  right_inv := by rintro ⟨_, _⟩; rfl

instance (i : ℕ) : Finite (A i) := Finite.of_injective (equivProd i) (equivProd i).injective

noncomputable instance (i : ℕ) : Mul (A i) where
  mul x y := ⟨x.slope * y.slope, x.offset + (x.slope : F i) * y.offset⟩

noncomputable instance (i : ℕ) : One (A i) where
  one := ⟨1, 0⟩

noncomputable instance (i : ℕ) : Inv (A i) where
  inv x := ⟨x.slope⁻¹, -((↑(x.slope⁻¹) : F i) * x.offset)⟩

@[simp] theorem mul_slope {i : ℕ} (x y : A i) : (x * y).slope = x.slope * y.slope := rfl
@[simp] theorem mul_offset {i : ℕ} (x y : A i) :
    (x * y).offset = x.offset + (x.slope : F i) * y.offset := rfl
@[simp] theorem one_slope {i : ℕ} : (1 : A i).slope = 1 := rfl
@[simp] theorem one_offset {i : ℕ} : (1 : A i).offset = 0 := rfl
@[simp] theorem inv_slope {i : ℕ} (x : A i) : x⁻¹.slope = x.slope⁻¹ := rfl
@[simp] theorem inv_offset {i : ℕ} (x : A i) :
    (x⁻¹).offset = -((↑(x.slope⁻¹) : F i) * x.offset) := rfl

noncomputable instance (i : ℕ) : Group (A i) where
  mul_assoc x y z := by
    apply A.ext
    · simp [mul_assoc]
    · simp only [mul_offset, mul_slope, Units.val_mul]
      ring
  one_mul x := by apply A.ext <;> simp
  mul_one x := by apply A.ext <;> simp
  inv_mul_cancel x := by apply A.ext <;> simp

private noncomputable def slopeHom (i : ℕ) : A i →* (F i)ˣ where
  toFun := A.slope
  map_one' := rfl
  map_mul' _ _ := rfl

noncomputable def V (i : ℕ) : Subgroup (A i) := (slopeHom i).ker

@[simp] theorem mem_V {i : ℕ} (x : A i) : x ∈ V i ↔ x.slope = 1 := Iff.rfl

theorem square_iff (i : ℕ) (x : A i) : IsSquare x ↔ x ∉ V i ∨ x = 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    by_cases hy : y * y ∈ V i
    · right
      have hs : y.slope * y.slope = 1 := (mem_V (y * y)).mp hy
      have hy1 : y.slope = 1 := by
        apply Units.ext
        apply frobenius_inj (F i) 2
        simpa [frobenius_def, pow_two] using congrArg (fun u : (F i)ˣ => (u : F i)) hs
      apply A.ext
      · exact hs
      · simp [hy1, CharTwo.add_self_eq_zero]
    · exact Or.inl hy
  · rintro (hx | rfl)
    · obtain ⟨r, hr⟩ := isSquare_of_charTwo' (x.slope : F i)
      have hr0 : r ≠ 0 := by
        rintro rfl
        simp at hr
      let s := Units.mk0 r hr0
      have hden : 1 + r ≠ 0 := by
        intro h
        have hr1 : r = 1 := by
          rw [add_eq_zero_iff_eq_neg] at h
          simpa [CharTwo.neg_eq] using h.symm
        apply hx
        apply (mem_V x).mpr
        apply Units.ext
        simpa [hr1] using hr
      refine ⟨⟨s, x.offset / (1 + r)⟩, A.ext ?_ ?_⟩
      · apply Units.ext
        exact hr
      · change x.offset = x.offset / (1 + r) + r * (x.offset / (1 + r))
        rw [← one_add_mul, mul_div_cancel₀]
        exact hden
    · exact ⟨1, by simp⟩

theorem card_F (i : ℕ) : Nat.card (F i) = 2 ^ (i + 3) :=
  GaloisField.card 2 (i + 3) (by omega)

theorem card_V (i : ℕ) : Nat.card ↥(V i) = 2 ^ (i + 3) := by
  let e : ↥(V i) ≃ F i :=
    { toFun := fun x => x.val.offset
      invFun := fun b => ⟨⟨1, b⟩, (mem_V _).2 rfl⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact A.ext ((mem_V x.val).mp x.property).symm rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (card_F i)

theorem card_A (i : ℕ) : Nat.card (A i) = 2 ^ (i + 3) * (2 ^ (i + 3) - 1) := by
  rw [Nat.card_congr (equivProd i), Nat.card_prod, Nat.card_units, card_F, Nat.mul_comm]

theorem ncard_nonsquares (i : ℕ) : {x : A i | ¬ IsSquare x}.ncard = 2 ^ (i + 3) - 1 := by
  have h : {x : A i | ¬ IsSquare x} = (V i : Set (A i)) \ {1} := by
    ext x
    simp [square_iff]
  rw [h, Set.ncard_sdiff_singleton_of_mem (V i).one_mem]
  exact congrArg (fun n : ℕ => n - 1) (card_V i)

theorem card_nonsquares (i : ℕ) : Nat.card {x : A i // ¬ IsSquare x} = 2 ^ (i + 3) - 1 :=
  ncard_nonsquares i

end OMA.Density43900.Affine

namespace OMA.Density43900.Stages

universe u

variable (A : ℕ → Type u) [∀ i, Group (A i)]

def restricted : Subgroup (∀ i, A i) where
  carrier := {f | ∃ k : ℕ, ∀ i, k ≤ i → f i = 1}
  one_mem' := ⟨0, fun _ _ => rfl⟩
  mul_mem' := by
    rintro f g ⟨k, hf⟩ ⟨l, hg⟩
    refine ⟨max k l, fun i hi => ?_⟩
    change f i * g i = 1
    rw [hf i ((le_max_left k l).trans hi), hg i ((le_max_right k l).trans hi), mul_one]
  inv_mem' := by
    rintro f ⟨k, hf⟩
    refine ⟨k, fun i hi => ?_⟩
    change (f i)⁻¹ = 1
    rw [hf i hi, inv_one]

abbrev G := ↥(restricted A)

def coord {A : ℕ → Type u} [∀ i, Group (A i)] (x : G A) (i : ℕ) : A i := x.val i

@[simp] theorem coord_one (i : ℕ) : coord (1 : G A) i = 1 := rfl
@[simp] theorem coord_mul (x y : G A) (i : ℕ) :
    coord (x * y) i = coord x i * coord y i := rfl
@[simp] theorem coord_inv (x : G A) (i : ℕ) : coord x⁻¹ i = (coord x i)⁻¹ := rfl

theorem coord_ext {x y : G A} (h : ∀ i, coord x i = coord y i) : x = y :=
  Subtype.ext (funext h)

theorem isSquare_iff_coord {A : ℕ → Type u} [∀ i, Group (A i)] (x : G A) :
    IsSquare x ↔ ∀ i, IsSquare (coord x i) := by
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨coord y i, rfl⟩
  · intro h
    obtain ⟨k, hk⟩ := x.property
    let y : G A := ⟨fun i => if i < k then (h i).choose else 1,
      ⟨k, fun i hi => if_neg (Nat.not_lt_of_ge hi)⟩⟩
    refine ⟨y, coord_ext A fun i => ?_⟩
    by_cases hi : i < k
    · simpa [y, coord, hi] using (h i).choose_spec
    · have hxi := hk i (Nat.le_of_not_gt hi)
      simpa [y, coord, hi] using hxi

def even (k : ℕ) : Subgroup (G A) where
  carrier := {x | ∀ i, k ≤ i → coord x i = 1}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro x y hx hy i hi
    simp [coord_mul, hx i hi, hy i hi]
  inv_mem' := by
    intro x hx i hi
    simp [coord_inv, hx i hi]

variable (V : ∀ i, Subgroup (A i))

def odd (k : ℕ) : Subgroup (G A) where
  carrier := {x | coord x k ∈ V k ∧ ∀ i, k < i → coord x i = 1}
  one_mem' := ⟨(V k).one_mem, fun _ _ => rfl⟩
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    exact ⟨(V k).mul_mem hx hy, fun i hi => by simp [hx' i hi, hy' i hi]⟩
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    exact ⟨(V k).inv_mem hx, fun i hi => by simp [hx' i hi]⟩

theorem even_le_odd (k : ℕ) : even A k ≤ odd A V k := by
  intro x hx
  change ∀ i, k ≤ i → coord x i = 1 at hx
  refine ⟨?_, fun i hi => hx i hi.le⟩
  rw [hx k le_rfl]
  exact (V k).one_mem

theorem odd_le_even_succ (k : ℕ) : odd A V k ≤ even A (k + 1) := by
  intro x hx i hi
  exact hx.2 i hi

def levels (i : ℕ) : Subgroup (G A) :=
  if i % 2 = 0 then even A (i / 2) else odd A V (i / 2)

@[simp] theorem levels_even (k : ℕ) : levels A V (2 * k) = even A k := by
  simp [levels, show 2 * k % 2 = 0 by omega, show 2 * k / 2 = k by omega]

@[simp] theorem levels_odd (k : ℕ) : levels A V (2 * k + 1) = odd A V k := by
  simp [levels, show (2 * k + 1) / 2 = k by omega]

theorem monotone_levels : Monotone (levels A V) := by
  apply monotone_nat_of_le_succ
  intro i
  by_cases hi : i % 2 = 0
  · let k := i / 2
    rw [show i = 2 * k by dsimp [k]; omega, levels_even, levels_odd]
    exact even_le_odd A V k
  · let k := i / 2
    rw [show i = 2 * k + 1 by dsimp [k]; omega, levels_odd,
      show 2 * k + 1 + 1 = 2 * (k + 1) by omega, levels_even]
    exact odd_le_even_succ A V k

theorem exhausts (x : G A) : ∃ i, x ∈ levels A V i := by
  obtain ⟨k, hk⟩ := x.property
  exact ⟨2 * k, by rw [levels_even]; exact hk⟩

private def extendFin (k : ℕ) (f : ∀ i : Fin k, A i) (i : ℕ) : A i :=
  if hi : i < k then f ⟨i, hi⟩ else 1

def evenEquiv (k : ℕ) : ↥(even A k) ≃ (∀ i : Fin k, A i) where
  toFun x i := coord x.val i
  invFun f := ⟨⟨extendFin A k f, ⟨k, fun i hi => dif_neg (Nat.not_lt_of_ge hi)⟩⟩,
    fun i hi => dif_neg (Nat.not_lt_of_ge hi)⟩
  left_inv x := by
    apply Subtype.ext
    apply coord_ext A
    intro i
    change extendFin A k (fun j => coord x.val j) i = coord x.val i
    by_cases hi : i < k
    · simp [extendFin, hi]
    · rw [extendFin, dif_neg hi, x.property i (Nat.le_of_not_gt hi)]
  right_inv f := by
    funext i
    change extendFin A k f i = f i
    simp [extendFin, i.isLt]

@[simp] theorem evenEquiv_apply (k : ℕ) (x : ↥(even A k)) (i : Fin k) :
    evenEquiv A k x i = coord x.val i := rfl

def oddEquiv (k : ℕ) : ↥(odd A V k) ≃ ((∀ i : Fin k, A i) × ↥(V k)) where
  toFun x := (fun i => coord x.val i, ⟨coord x.val k, x.property.1⟩)
  invFun f :=
    let ff := Function.update (extendFin A k f.1) k f.2.val
    have hf : ∀ i, k < i → ff i = 1 := by
      intro i hi
      have hn : i ≠ k := Nat.ne_of_gt hi
      have hlt : ¬ (i < k) := Nat.not_lt_of_ge hi.le
      simp [ff, Function.update_of_ne hn, extendFin, hlt]
    ⟨⟨ff, ⟨k + 1, hf⟩⟩, ⟨by simp [coord, ff], hf⟩⟩
  left_inv x := by
    apply Subtype.ext
    apply coord_ext A
    intro i
    change Function.update (extendFin A k fun j => coord x.val j) k (coord x.val k) i =
      coord x.val i
    by_cases hi : i = k
    · subst i
      simp
    rw [Function.update_of_ne hi]
    by_cases hl : i < k
    · simp [extendFin, hl]
    · have hg : k < i := by omega
      rw [extendFin, dif_neg hl, x.property.2 i hg]
  right_inv f := by
    apply Prod.ext
    · funext i
      change Function.update (extendFin A k f.1) k f.2.val i = f.1 i
      rw [Function.update_of_ne (Nat.ne_of_lt i.isLt)]
      simp [extendFin, i.isLt]
    · apply Subtype.ext
      change Function.update (extendFin A k f.1) k f.2.val k = f.2.val
      simp

@[simp] theorem oddEquiv_fst_apply (k : ℕ) (x : ↥(odd A V k)) (i : Fin k) :
    (oddEquiv A V k x).1 i = coord x.val i := rfl

@[simp] theorem oddEquiv_snd_coe (k : ℕ) (x : ↥(odd A V k)) :
    ((oddEquiv A V k x).2 : A k) = coord x.val k := rfl

instance finite_even [∀ i, Finite (A i)] (k : ℕ) : Finite ↥(even A k) := by
  let (i : Fin k) : Fintype (A i) := Fintype.ofFinite _
  exact Finite.of_equiv _ (evenEquiv A k).symm

instance finite_odd [∀ i, Finite (A i)] (k : ℕ) : Finite ↥(odd A V k) := by
  let (i : Fin k) : Fintype (A i) := Fintype.ofFinite _
  exact Finite.of_equiv _ (oddEquiv A V k).symm

theorem finite_levels [∀ i, Finite (A i)] (i : ℕ) : Finite ↥(levels A V i) := by
  unfold levels
  split <;> infer_instance

end OMA.Density43900.Stages

namespace OMA.Density43900.Count

noncomputable def badFraction {B : Type*} (P : B → Prop) : ℝ :=
  ({b | ¬ P b} : Set B).ncard / (Nat.card B : ℝ)

theorem badFraction_equiv {A B : Type*} (e : A ≃ B) (P : B → Prop) :
    badFraction (P ∘ e) = badFraction P := by
  change ((e ⁻¹' {b : B | ¬ P b}).ncard : ℝ) / Nat.card A =
    ({b : B | ¬ P b}.ncard : ℝ) / Nat.card B
  rw [Set.ncard_preimage_of_injective_subset_range e.injective, Nat.card_congr e]
  simp [e.surjective.range_eq]

private theorem badFraction_prod_le {A B : Type*} [Finite A] [Finite B]
    [Nonempty A] [Nonempty B] (P : A → Prop) (Q : B → Prop) :
    badFraction (fun x : A × B => P x.1 ∧ Q x.2) ≤ badFraction P + badFraction Q := by
  let s : Set A := {a | ¬ P a}
  let t : Set B := {b | ¬ Q b}
  have hs : {x : A × B | ¬ (P x.1 ∧ Q x.2)} =
      (s ×ˢ (Set.univ : Set B)) ∪ ((Set.univ : Set A) ×ˢ t) := by
    ext x
    change ¬ (P x.1 ∧ Q x.2) ↔ (¬ P x.1 ∧ True) ∨ (True ∧ ¬ Q x.2)
    simp only [true_and, and_true, not_and_or]
  have hcard := Set.ncard_union_le (s ×ˢ (Set.univ : Set B)) ((Set.univ : Set A) ×ˢ t)
  rw [← hs, Set.ncard_prod, Set.ncard_prod, Set.ncard_univ, Set.ncard_univ] at hcard
  have hcast : (({x : A × B | ¬ (P x.1 ∧ Q x.2)} : Set (A × B)).ncard : ℝ) ≤
      (s.ncard : ℝ) * Nat.card B + (Nat.card A : ℝ) * t.ncard := by
    exact_mod_cast hcard
  have ha : 0 < (Nat.card A : ℝ) := by exact_mod_cast Nat.card_pos (α := A)
  have hb : 0 < (Nat.card B : ℝ) := by exact_mod_cast Nat.card_pos (α := B)
  unfold badFraction
  rw [Nat.card_prod, Nat.cast_mul]
  calc
    _ ≤ ((s.ncard : ℝ) * Nat.card B + (Nat.card A : ℝ) * t.ncard) /
        ((Nat.card A : ℝ) * Nat.card B) :=
      div_le_div_of_nonneg_right hcast (mul_nonneg ha.le hb.le)
    _ = _ := by
      rw [add_div, mul_div_mul_right _ _ hb.ne', mul_div_mul_left _ _ ha.ne']

theorem badFraction_prod_ge {A B : Type*} [Finite A] [Finite B] [Nonempty A]
    (P : A → Prop) (Q : B → Prop) :
    badFraction Q ≤ badFraction (fun x : A × B => P x.1 ∧ Q x.2) := by
  let t : Set B := {b | ¬ Q b}
  have hsub : (Set.univ : Set A) ×ˢ t ⊆ {x : A × B | ¬ (P x.1 ∧ Q x.2)} :=
    fun _ hx hgood => hx.2 hgood.2
  have hcard := Set.ncard_le_ncard hsub
  rw [Set.ncard_prod, Set.ncard_univ] at hcard
  have hcast : (Nat.card A : ℝ) * t.ncard ≤
      (({x : A × B | ¬ (P x.1 ∧ Q x.2)} : Set (A × B)).ncard : ℝ) := by
    exact_mod_cast hcard
  have ha : 0 < (Nat.card A : ℝ) := by exact_mod_cast Nat.card_pos (α := A)
  unfold badFraction
  rw [Nat.card_prod, Nat.cast_mul]
  calc
    _ = ((Nat.card A : ℝ) * t.ncard) / ((Nat.card A : ℝ) * Nat.card B) := by
      rw [mul_div_mul_left _ _ ha.ne']
    _ ≤ _ := div_le_div_of_nonneg_right hcast (by positivity)

theorem badFraction_pi_le {k : ℕ} {B : Fin k → Type*} [∀ i, Finite (B i)]
    [∀ i, Nonempty (B i)] (P : ∀ i, B i → Prop) :
    badFraction (fun x : ∀ i, B i => ∀ i, P i (x i)) ≤ ∑ i, badFraction (P i) := by
  induction k with
  | zero => simp [badFraction]
  | succ k ih =>
      let Q : (∀ i : Fin k, B i.succ) → Prop := fun ys => ∀ i, P i.succ (ys i)
      have hp :
          ((fun x : ∀ i, B i => ∀ i, P i (x i)) ∘ Fin.consEquiv B) =
            (fun x : B 0 × (∀ i : Fin k, B i.succ) => P 0 x.1 ∧ Q x.2) := by
        funext x
        simp [Q, Fin.consEquiv_apply, Fin.forall_fin_succ]
      rw [← badFraction_equiv (Fin.consEquiv B), hp, Fin.sum_univ_succ]
      exact (badFraction_prod_le (P 0) Q).trans
        (add_le_add le_rfl (ih (fun i => P i.succ)))

theorem geom_le (k : ℕ) :
    (∑ i ∈ Finset.range k, 1 / ((2 : ℝ) ^ (i + 3))) ≤ 1 / 4 := by
  have h (n : ℕ) :
      (∑ i ∈ Finset.range n, 1 / ((2 : ℝ) ^ (i + 3))) =
        1 / 4 - 1 / (2 : ℝ) ^ (n + 2) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        change 1 / 4 - 1 / (2 : ℝ) ^ (n + 2) + 1 / (2 : ℝ) ^ (n + 2 + 1) =
          1 / 4 - 1 / (2 : ℝ) ^ (n + 2 + 1)
        rw [pow_succ]
        have hpow : (2 : ℝ) ^ (n + 2) ≠ 0 := by positivity
        field_simp
        ring
  rw [h]
  exact sub_le_self _ (by positivity)

end OMA.Density43900.Count

namespace OMA.Density43900.Assembly

open FirstOrder Filter OMA.S_mo_43900
open scoped Topology

private def squareBody : groupLanguage.BoundedFormula (Fin 1) 1 :=
  .equal (.var (.inl 0)) (.func GroupFunction.product (fun _ => .var (.inr 0)))

def nonsquareFormula : groupLanguage.Formula (Fin 1) := squareBody.ex.not

theorem realize_nonsquare {G : Type} [Group G] (v : Fin 1 → G) :
    letI := groupInterpretation G
    nonsquareFormula.Realize v ↔ ¬ IsSquare (v 0) := by
  letI := groupInterpretation G
  change nonsquareFormula.Realize v ↔ ¬ IsSquare (v 0)
  rw [nonsquareFormula, Language.Formula.realize_not]
  change (¬ squareBody.ex.Realize v default) ↔ ¬ IsSquare (v 0)
  rw [Language.BoundedFormula.realize_ex]
  rfl

noncomputable def stageDensity {G : Type} [Group G] (H : Subgroup G) : ℝ :=
  ({x : H | ¬ IsSquare (x : G)}.ncard : ℝ) / (Nat.card H : ℝ)

theorem formula_density {G : Type} [Group G] (H : Subgroup G) :
    letI := groupInterpretation G
    ({tuple : Fin 1 → H |
      nonsquareFormula.Realize (fun j => (tuple j : G))}.ncard : ℝ) /
        (Nat.card (Fin 1 → H) : ℝ) = stageDensity H := by
  letI := groupInterpretation G
  let e : (Fin 1 → H) ≃ H := Equiv.funUnique (Fin 1) H
  have hs : {tuple : Fin 1 → H |
      nonsquareFormula.Realize (fun j => (tuple j : G))} =
      e ⁻¹' {x : H | ¬ IsSquare (x : G)} := by
    ext tuple
    change nonsquareFormula.Realize (fun j => (tuple j : G)) ↔ ¬ IsSquare ((e tuple : H) : G)
    rw [realize_nonsquare]
    change ¬ IsSquare (tuple 0 : G) ↔ ¬ IsSquare (tuple default : G)
    rw [show (default : Fin 1) = 0 from Subsingleton.elim _ _]
  have hr : {x : H | ¬ IsSquare (x : G)} ⊆ Set.range e :=
    fun x _ => e.surjective x
  rw [hs, Set.ncard_preimage_of_injective_subset_range e.injective hr, Nat.card_congr e]
  rfl

theorem no_limit (a : ℕ → ℝ)
    (heven : ∀ k, a (2 * k) ≤ 1 / 4)
    (hodd : ∀ k, 3 / 4 ≤ a (2 * k + 1)) (limit : ℝ) :
    ¬ Tendsto a atTop (𝓝 limit) := by
  intro h
  by_cases hl : limit < 1 / 2
  · have hh : ∀ᶠ k in atTop, a k < 3 / 4 :=
      h.eventually_lt_const (by linarith)
    obtain ⟨k, hk⟩ := eventually_atTop.mp hh
    exact (not_lt_of_ge (hodd k)) (hk (2 * k + 1) (by omega))
  · have hh : ∀ᶠ k in atTop, 1 / 4 < a k :=
      h.eventually_const_lt (by linarith)
    obtain ⟨k, hk⟩ := eventually_atTop.mp hh
    exact (not_lt_of_ge (heven k)) (hk (2 * k) (by omega))

end OMA.Density43900.Assembly

namespace OMA.Density43900.Assembly

open Filter OMA.S_mo_43900
open scoped Topology BigOperators

private theorem field_size_lower (i : ℕ) : 4 ≤ (2 : ℕ) ^ (i + 3) := by
  calc
    4 = (2 : ℕ) ^ 2 := by norm_num
    _ ≤ (2 : ℕ) ^ (i + 3) := Nat.pow_le_pow_right (by decide) (by omega)

private theorem affine_bad (i : ℕ) :
    Count.badFraction (fun x : Affine.A i => IsSquare x) = 1 / (2 : ℝ) ^ (i + 3) := by
  let q : ℕ := 2 ^ (i + 3)
  have hq : 4 ≤ q := field_size_lower i
  have hq1 : 1 ≤ q := by omega
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqsub : (0 : ℝ) < (q : ℝ) - 1 :=
    sub_pos.mpr (by exact_mod_cast (show (1 : ℕ) < q by omega))
  rw [Count.badFraction, Affine.ncard_nonsquares, Affine.card_A]
  change ((q - 1 : ℕ) : ℝ) / ((q * (q - 1) : ℕ) : ℝ) = _
  push_cast [Nat.cast_sub hq1]
  rw [show ((2 : ℝ) ^ (i + 3)) = (q : ℝ) by norm_cast]
  field_simp

private theorem translations_bad (i : ℕ) :
    3 / 4 ≤ Count.badFraction (fun x : ↥(Affine.V i) => IsSquare (x : Affine.A i)) := by
  let q : ℕ := 2 ^ (i + 3)
  have hq : 4 ≤ q := field_size_lower i
  have hq1 : 1 ≤ q := by omega
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq' : (4 : ℝ) ≤ q := by exact_mod_cast hq
  have hset : {x : ↥(Affine.V i) | ¬ IsSquare (x : Affine.A i)} =
      ({1} : Set ↥(Affine.V i))ᶜ := by
    ext x
    change (¬ IsSquare (x : Affine.A i)) ↔ ¬ x = 1
    rw [Affine.square_iff]
    constructor
    · intro hn h
      exact hn (Or.inr (congrArg (fun y : ↥(Affine.V i) => (y : Affine.A i)) h))
    · intro hn h
      rcases h with h | h
      · exact h x.property
      · exact hn (Subtype.ext h)
  rw [Count.badFraction, hset, Set.ncard_compl, Set.ncard_singleton, Affine.card_V]
  change (3 : ℝ) / 4 ≤ ((q - 1 : ℕ) : ℝ) / q
  rw [Nat.cast_sub hq1, Nat.cast_one, le_div_iff₀ hqpos]
  linarith

private theorem even_density (k : ℕ) : stageDensity (Stages.even Affine.A k) ≤ 1 / 4 := by
  let e := Stages.evenEquiv Affine.A k
  let P := fun x : (∀ i : Fin k, Affine.A i) => ∀ i, IsSquare (x i)
  have hp : (fun x : ↥(Stages.even Affine.A k) =>
      IsSquare (x : Stages.G Affine.A)) = P ∘ e := by
    funext x
    apply propext
    rw [Stages.isSquare_iff_coord]
    change (∀ i, IsSquare (Stages.coord x.val i)) ↔ ∀ i : Fin k, IsSquare (Stages.coord x.val i)
    refine ⟨fun h i => h i, ?_⟩
    intro h i
    by_cases hi : i < k
    · exact h ⟨i, hi⟩
    · rw [x.property i (Nat.le_of_not_gt hi)]
      exact ⟨1, by simp⟩
  change Count.badFraction (fun x : ↥(Stages.even Affine.A k) =>
    IsSquare (x : Stages.G Affine.A)) ≤ _
  rw [hp, Count.badFraction_equiv]
  calc
    Count.badFraction P ≤ ∑ i : Fin k, Count.badFraction
        (fun x : Affine.A i => IsSquare x) :=
      Count.badFraction_pi_le (fun _ x => IsSquare x)
    _ ≤ 1 / 4 := by
      simp only [affine_bad]
      have h := Count.geom_le k
      rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ => 1 / (2 : ℝ) ^ (i + 3)) k] at h
      exact h

private theorem odd_density (k : ℕ) : 3 / 4 ≤ stageDensity (Stages.odd Affine.A Affine.V k) := by
  let e := Stages.oddEquiv Affine.A Affine.V k
  let P := fun x : (∀ i : Fin k, Affine.A i) => ∀ i, IsSquare (x i)
  let Q := fun x : ↥(Affine.V k) => IsSquare (x : Affine.A k)
  have hp : (fun x : ↥(Stages.odd Affine.A Affine.V k) =>
      IsSquare (x : Stages.G Affine.A)) = (fun t => P t.1 ∧ Q t.2) ∘ e := by
    funext x
    apply propext
    rw [Stages.isSquare_iff_coord]
    change (∀ i, IsSquare (Stages.coord x.val i)) ↔
      (∀ i : Fin k, IsSquare (Stages.coord x.val i)) ∧ IsSquare (Stages.coord x.val k)
    refine ⟨fun h => ⟨fun i => h i, h k⟩, ?_⟩
    rintro ⟨h₁, h₂⟩ i
    rcases lt_trichotomy i k with hi | rfl | hi
    · exact h₁ ⟨i, hi⟩
    · exact h₂
    · rw [x.property.2 i hi]
      exact ⟨1, by simp⟩
  change _ ≤ Count.badFraction (fun x : ↥(Stages.odd Affine.A Affine.V k) =>
    IsSquare (x : Stages.G Affine.A))
  rw [hp, Count.badFraction_equiv]
  exact (translations_bad k).trans (Count.badFraction_prod_ge P Q)

end OMA.Density43900.Assembly

open OMA.Density43900 in
theorem OMA.solution : type_of% @OMA.S_mo_43900.main := by
  refine ⟨Stages.G Affine.A, inferInstance, Stages.levels Affine.A Affine.V,
    1, Assembly.nonsquareFormula, Stages.monotone_levels Affine.A Affine.V,
    Stages.finite_levels Affine.A Affine.V, Stages.exhausts Affine.A Affine.V, ?_⟩
  intro limit
  simp only [Assembly.formula_density]
  apply Assembly.no_limit _ _ _ limit
  · intro k
    rw [Stages.levels_even]
    exact Assembly.even_density k
  · intro k
    rw [Stages.levels_odd]
    exact Assembly.odd_density k
