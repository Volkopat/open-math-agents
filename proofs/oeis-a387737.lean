import OMAStatements.S_oeis_a387737
import Mathlib

namespace A387737Proof

open Finset OMA.S_oeis_a387737

private theorem twice_sum_indices (r : ℕ) :
    2 * (∑ i : Fin r, (i.val : ℤ)) = (r : ℤ) * ((r : ℤ) - 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_succ]
    nlinarith only [ih]

private def shift (r : ℕ) (i : Fin r) : ℤ := 2 * (i.val : ℤ) - ((r : ℤ) - 1)
private def up {r : ℕ} (f : Fin r → ℤ) (i : Fin r) : ℤ := f i + shift r i
private def down {r : ℕ} (f : Fin r → ℤ) (i : Fin r) : ℤ := f i - shift r i

private theorem sum_shift (r : ℕ) : (∑ i : Fin r, shift r i) = 0 := by
  simp only [shift, sum_sub_distrib, ← mul_sum, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, twice_sum_indices]
  ring

private theorem sum_up {r : ℕ} (f : Fin r → ℤ) : (∑ i, up f i) = ∑ i, f i := by
  simp only [up, sum_add_distrib, sum_shift, add_zero]

private theorem sum_down {r : ℕ} (f : Fin r → ℤ) : (∑ i, down f i) = ∑ i, f i := by
  simp only [down, sum_sub_distrib, sum_shift, sub_zero]

private theorem single_le_total {r : ℕ} {f : Fin r → ℤ} (h : ∀ i, 0 ≤ f i) (i : Fin r) :
    f i ≤ ∑ j, f j :=
  single_le_sum (f := f) (fun j _ => h j) (mem_univ i)

private theorem pair_le_total {r : ℕ} {f : Fin r → ℤ} (h : ∀ i, 0 ≤ f i)
    (i j : Fin r) (hij : i ≠ j) : f i + f j ≤ ∑ k, f k := by
  classical
  rw [← sum_pair hij]
  exact sum_le_sum_of_subset_of_nonneg (by simp) fun k _ _ => h k

private theorem another_index {r : ℕ} (hr : 2 ≤ r) (i : Fin r) : ∃ j : Fin r, i ≠ j := by
  let z : Fin r := ⟨0, by omega⟩
  let o : Fin r := ⟨1, by omega⟩
  by_cases hi : i = z
  · refine ⟨o, ?_⟩
    rw [hi]
    intro h
    have hv := congrArg Fin.val h
    simp [z, o] at hv
  · exact ⟨z, hi⟩

private theorem up_valid {n r : ℕ} (hr : 2 ≤ r) {f : Fin r → ℤ} (hf : A n r f) :
    B n r (up f) := by
  obtain ⟨hlow, hmin, hmono, htotal⟩ := hf
  have hl : largest n (up f) = largest n f := by simp only [largest, sum_up]
  have hmin' (i : Fin r) : 2 ≤ up f i := by
    have h := hmin i
    dsimp [up, shift]
    omega
  have htotal' : (∑ i, up f i) ≤ largest n (up f) := by
    simpa only [hl, sum_up] using htotal
  refine ⟨by rw [hl]; omega, hmin', ?_, ?_, htotal'⟩
  · intro i j hij
    have h := hmono hij
    dsimp [up, shift]
    omega
  · intro i
    obtain ⟨j, hij⟩ := another_index hr i
    have hj := hmin' j
    have hp := (pair_le_total (fun k => (by norm_num : (0 : ℤ) ≤ 2).trans (hmin' k)) i j hij).trans htotal'
    omega

private theorem down_valid {n r : ℕ} (hr : 2 ≤ r) {f : Fin r → ℤ} (hf : B n r f) :
    A n r (down f) := by
  obtain ⟨_, hmin, hgap, _, htotal⟩ := hf
  let z : Fin r := ⟨0, by omega⟩
  have hmin' (i : Fin r) : (r : ℤ) + 1 ≤ down f i := by
    have h := hgap z i (by change 0 ≤ i.val; omega)
    have hz := hmin z
    have hzval : z.val = 0 := rfl
    simp only [hzval, Nat.cast_zero, mul_zero, add_zero] at h
    dsimp [down, shift]
    omega
  have htotal' : (∑ i, down f i) ≤ largest n (down f) := by
    simpa only [largest, sum_down] using htotal
  refine ⟨?_, hmin', ?_, htotal'⟩
  · have hnonneg (i : Fin r) : 0 ≤ down f i := by
      have := hmin' i
      omega
    exact (hmin' z).trans ((single_le_total hnonneg z).trans htotal')
  · intro i j hij
    have h := hgap i j hij
    dsimp [down, shift]
    omega

private theorem equal_multi (n r : ℕ) (hr : 2 ≤ r) : countA n r = countB n r := by
  unfold countA countB
  exact Nat.card_congr {
    toFun := fun f => ⟨up f.val, up_valid hr f.property⟩
    invFun := fun f => ⟨down f.val, down_valid hr f.property⟩
    left_inv := fun f => Subtype.ext (funext fun i => by simp [up, down])
    right_inv := fun f => Subtype.ext (funext fun i => by simp [up, down]) }

private theorem equal_empty (n : ℕ) (hn : 4 ≤ n) : countA n 0 = countB n 0 := by
  unfold countA countB
  exact Nat.card_congr {
    toFun := fun f => ⟨f.val, by simp [B, largest] <;> omega⟩
    invFun := fun f => ⟨f.val, by simp [A, largest, Monotone] <;> omega⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

private def evaluate {P : (Fin 1 → ℤ) → Prop} {Q : ℤ → Prop}
    (h : ∀ f, P f ↔ Q (f 0)) : {f // P f} ≃ {x // Q x} where
  toFun f := ⟨f.val 0, (h f.val).mp f.property⟩
  invFun x := ⟨fun _ => x.val, (h (fun _ => x.val)).mpr x.property⟩
  left_inv f := Subtype.ext (funext fun i => by fin_cases i; rfl)
  right_inv _ := rfl

private theorem interval_card (a b : ℤ) :
    Nat.card {x : ℤ // a ≤ x ∧ x ≤ b} = (b + 1 - a).toNat := by
  have hm : ∀ x : ℤ, x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b := fun _ => mem_Icc
  letI : Fintype {x : ℤ // a ≤ x ∧ x ≤ b} := Fintype.ofFinset (Icc a b) hm
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_ofFinset (Icc a b) hm).trans (Int.card_Icc a b)

private theorem one_difference (n : ℕ) (hn : 4 ≤ n) : countA n 1 = countB n 1 + 1 := by
  have ha (f : Fin 1 → ℤ) : A n 1 f ↔ 2 ≤ f 0 ∧ f 0 ≤ (n : ℤ) / 2 := by
    simp [A, largest, Monotone, Fin.forall_fin_one] <;> omega
  have hb (f : Fin 1 → ℤ) : B n 1 f ↔ 2 ≤ f 0 ∧ f 0 ≤ (n : ℤ) / 2 - 1 := by
    simp [B, largest, Fin.forall_fin_one] <;> omega
  have hA := Nat.card_congr
    (evaluate (P := A n 1) (Q := fun x => 2 ≤ x ∧ x ≤ (n : ℤ) / 2) ha)
  have hB := Nat.card_congr
    (evaluate (P := B n 1) (Q := fun x => 2 ≤ x ∧ x ≤ (n : ℤ) / 2 - 1) hb)
  unfold countA countB
  rw [hA, hB, interval_card, interval_card]
  omega

end A387737Proof

open Finset OMA.S_oeis_a387737 A387737Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a387737.main := by
  intro n hn
  have h1 : 1 ∈ range n := mem_range.mpr (by omega)
  have hA := sum_erase_add (range n) (countA n) h1
  have hB := sum_erase_add (range n) (countB n) h1
  have hrest : (∑ r ∈ (range n).erase 1, countA n r) =
      ∑ r ∈ (range n).erase 1, countB n r := by
    apply sum_congr rfl
    intro r hr
    have hne : r ≠ 1 := (mem_erase.mp hr).1
    by_cases hz : r = 0
    · subst r
      exact equal_empty n hn
    · exact equal_multi n r (by omega)
  rw [← hA, ← hB, hrest, one_difference n hn]
  omega
