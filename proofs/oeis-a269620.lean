import OMAStatements.S_oeis_a269620
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace A269620Proof

open OMA.S_oeis_a269620

open scoped Classical

abbrev Word (n : ℕ) := Fin 4 → Fin (n + 1)

private def tuple {α : Type*} (a b c d : α) (i : Fin 4) : α :=
  match i.val with
  | 0 => a
  | 1 => b
  | 2 => c
  | _ => d

@[simp] private theorem cast0 : (0 : Fin 3).castSucc = (0 : Fin 4) := rfl
@[simp] private theorem cast1 : (1 : Fin 3).castSucc = (1 : Fin 4) := rfl
@[simp] private theorem cast2 : (2 : Fin 3).castSucc = (2 : Fin 4) := rfl
@[simp] private theorem succ0 : (0 : Fin 3).succ = (1 : Fin 4) := rfl
@[simp] private theorem succ1 : (1 : Fin 3).succ = (2 : Fin 4) := rfl
@[simp] private theorem succ2 : (2 : Fin 3).succ = (3 : Fin 4) := rfl

private theorem valid_iff {n : ℕ} (w : Word n) :
    valid w ↔ (pair w 0 → pair w 1 → allowed w 0 1) ∧
      (pair w 1 → pair w 2 → allowed w 1 2) ∧
      (pair w 0 → ¬ pair w 1 → pair w 2 → allowed w 0 2) := by
  constructor
  · intro h
    refine ⟨fun h0 h1 => h 0 1 (by decide) h0 h1 ?_,
      fun h1 h2 => h 1 2 (by decide) h1 h2 ?_,
      fun h0 h1 h2 => h 0 2 (by decide) h0 h2 ?_⟩
    · intro k h0 h1
      simp only [Fin.lt_def] at h0 h1
      omega
    · intro k h1 h2
      simp only [Fin.lt_def] at h1 h2
      omega
    · intro k hk1 hk2
      have h : k = 1 := by
        apply Fin.ext
        simp only [Fin.lt_def] at hk1 hk2
        omega
      rwa [h]
  · intro h i j hij hi hj hk
    fin_cases i <;> fin_cases j <;> try (norm_num [Fin.lt_def] at hij)
    · exact h.1 hi hj
    · exact h.2.2 hi (hk 1 (by decide) (by decide)) hj
    · exact h.2.1 hi hj

private noncomputable def ind (p : Prop) : ℤ := if p then 1 else 0

private def paired {n : ℕ} (w : Word n) : Prop :=
  w 0 = w 1 ∧ w 2 = w 3

private def same {n : ℕ} (w : Word n) : Prop :=
  w 0 = w 1 ∧ w 1 = w 2 ∧ w 2 = w 3

private def up2 {n : ℕ} (w : Word n) : Prop :=
  w 0 = w 1 ∧ w 2 = w 3 ∧ (w 0).val + 2 = (w 2).val

private def down1 {n : ℕ} (w : Word n) : Prop :=
  w 0 = w 1 ∧ w 2 = w 3 ∧ (w 2).val + 1 = (w 0).val

set_option maxHeartbeats 2000000 in
private theorem indicators {n : ℕ} (w : Word n) :
    ind (valid w) = 1 - ind (paired w) + ind (same w) + ind (up2 w) + ind (down1 w) := by
  simp [ind, valid_iff, pair, allowed, paired, same, up2, down1, Fin.ext_iff]
  split_ifs <;> omega

private def translate {n width : ℕ} (x : Fin (n + 1 - width)) (offset : Fin (width + 1)) :
    Fin (n + 1) :=
  ⟨x.val + offset.val, by have hx := x.isLt; have ho := offset.isLt; omega⟩

private theorem paired_card (n : ℕ) :
    Nat.card {w : Word n // paired w} = (n + 1) * (n + 1) := by
  let word : Fin (n + 1) × Fin (n + 1) → Word n := fun t => tuple t.1 t.1 t.2 t.2
  let e : {w : Word n // paired w} ≃ Fin (n + 1) × Fin (n + 1) := {
    toFun := fun w => (w.1 0, w.1 2)
    invFun := fun t => ⟨word t, by simp [word, tuple, paired]⟩
    left_inv := fun w => by
      have h := w.2
      simp [paired, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin, Nat.card_prod] using Nat.card_congr e

private theorem same_card (n : ℕ) :
    Nat.card {w : Word n // same w} = (n + 1) := by
  let word : Fin (n + 1) → Word n := fun t => tuple t t t t
  let e : {w : Word n // same w} ≃ Fin (n + 1) := {
    toFun := fun w => w.1 0
    invFun := fun t => ⟨word t, by simp [word, tuple, same]⟩
    left_inv := fun w => by
      have h := w.2
      simp [same, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin] using Nat.card_congr e

private theorem up2_card (n : ℕ) :
    Nat.card {w : Word n // up2 w} = (n - 1) := by
  let word : Fin (n - 1) → Word n := fun t => tuple (translate (width := 2) t 0) (translate (width := 2) t 0) (translate (width := 2) t 2) (translate (width := 2) t 2)
  let e : {w : Word n // up2 w} ≃ Fin (n - 1) := {
    toFun := fun w => ⟨(w.1 0).val, by
      have h := w.2
      simp [up2, Fin.ext_iff] at h
      have hb := (w.1 2).isLt
      omega⟩
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, up2]⟩
    left_inv := fun w => by
      have h := w.2
      simp [up2, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin] using Nat.card_congr e

private theorem down1_card (n : ℕ) :
    Nat.card {w : Word n // down1 w} = n := by
  let word : Fin n → Word n := fun t => tuple (translate (width := 1) t 1) (translate (width := 1) t 1) (translate (width := 1) t 0) (translate (width := 1) t 0)
  let e : {w : Word n // down1 w} ≃ Fin n := {
    toFun := fun w => ⟨(w.1 2).val, by
      have h := w.2
      simp [down1, Fin.ext_iff] at h
      have hb := (w.1 0).isLt
      omega⟩
    invFun := fun t => ⟨word t, by simp [word, tuple, translate, down1]⟩
    left_inv := fun w => by
      have h := w.2
      simp [down1, Fin.ext_iff] at h
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [word, tuple, translate, Fin.ext_iff] <;> omega
    right_inv := fun _ => rfl }
  simpa only [Nat.card_fin] using Nat.card_congr e

open scoped BigOperators

private theorem sum_ind {ι : Type*} [Fintype ι] (p : ι → Prop) :
    (∑ x, ind (p x)) = (Nat.card {x // p x} : ℤ) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact Finset.sum_boole p _

private def poly (x : ℤ) : ℤ :=
  x ^ 4 + 4 * x ^ 3 + 5 * x ^ 2 + 5 * x

private theorem a_poly (n : ℕ) (hn : 0 < n) : a n = poly n := by
  have h := Finset.sum_congr (s₁ := (Finset.univ : Finset (Word n))) rfl
    (fun w _ => indicators w)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_ind,
    paired_card, same_card, up2_card, down1_card,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_fun,
    Fintype.card_fin] at h
  rw [a, if_neg (show n ≠ 0 by omega), h]
  push_cast [Int.ofNat_sub (show 1 ≤ n by omega)]
  unfold poly
  ring

private theorem recurrence (n : ℕ) (hn : 5 < n) :
    a n = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) -
      5 * a (n - 4) + a (n - 5) := by
  rw [a_poly n (by omega), a_poly (n - 1) (by omega), a_poly (n - 2) (by omega),
    a_poly (n - 3) (by omega), a_poly (n - 4) (by omega), a_poly (n - 5) (by omega)]
  simp only [Int.natCast_sub (show 1 ≤ n by omega),
    Int.natCast_sub (show 2 ≤ n by omega), Int.natCast_sub (show 3 ≤ n by omega),
    Int.natCast_sub (show 4 ≤ n by omega), Int.natCast_sub (show 5 ≤ n by omega), Nat.cast_ofNat]
  unfold poly
  ring

private theorem a_at_all (n : ℕ) : a n = if n = 0 then 0 else poly n := by
  by_cases hn : n = 0
  · simp [a, hn]
  · simpa [hn] using a_poly n (by omega)

open PowerSeries

private theorem generating_function : (1 - X) ^ 5 * mk a = 3 * X * (5 + X + 3 * X ^ 2 - X ^ 3) := by
  have hd : ((1 - X) : PowerSeries ℤ) ^ 5 =
      1 - C 5 * X ^ 1 + C 10 * X ^ 2 - C 10 * X ^ 3 + C 5 * X ^ 4 - X ^ 5 := by
    norm_num
    ring
  have hq : (3 * X * (5 + X + 3 * X ^ 2 - X ^ 3) : PowerSeries ℤ) = C 15 * X ^ 1 + C 3 * X ^ 2 + C 9 * X ^ 3 - C 3 * X ^ 4 := by
    norm_num
    ring
  rw [hd, hq]
  ext n
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_add, map_sub,
    coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow]
  by_cases hn : n < 6
  · interval_cases n <;> norm_num [a_at_all, poly]
  · simp only [if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega),
      if_pos (show 3 ≤ n by omega), if_pos (show 4 ≤ n by omega), if_pos (show 5 ≤ n by omega),
      if_neg (show n ≠ 1 by omega), if_neg (show n ≠ 2 by omega),
      if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 4 by omega), mul_zero, add_zero, sub_zero]
    have hr := recurrence n (by omega)
    omega

end A269620Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a269620.main :=
  ⟨A269620Proof.generating_function, A269620Proof.recurrence⟩
