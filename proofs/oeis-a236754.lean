import OMAStatements.S_oeis_a236754
import Mathlib

namespace A236754

open OMA.S_oeis_a236754

private theorem traverse_append (xs ys : List ℕ) (x : ℤ) :
    OMA.S_oeis_a236754.traverse (xs ++ ys) x = OMA.S_oeis_a236754.traverse ys (OMA.S_oeis_a236754.traverse xs x) := by
  induction xs generalizing x with
  | nil => rfl
  | cons c cs ih => exact ih _

private theorem affine (cs : List ℕ) :
    ∃ b : ℤ, ∀ x, OMA.S_oeis_a236754.traverse cs x = if cs.length % 2 = 0 then x + b else b - x := by
  induction cs with
  | nil => exact ⟨0, by simp [OMA.S_oeis_a236754.traverse]⟩
  | cons c cs ih =>
      obtain ⟨b, hb⟩ := ih
      by_cases he : cs.length % 2 = 0
      · have ho : (c :: cs).length % 2 ≠ 0 := by simp only [List.length_cons]; omega
        refine ⟨2 * (c : ℤ) + b, fun x => ?_⟩
        rw [OMA.S_oeis_a236754.traverse, hb, if_pos he, if_neg ho]
        ring
      · have ho : (c :: cs).length % 2 = 0 := by simp only [List.length_cons]; omega
        refine ⟨b - 2 * (c : ℤ), fun x => ?_⟩
        rw [OMA.S_oeis_a236754.traverse, hb, if_neg he, if_pos ho]
        ring

private theorem odd_loop (cs : List ℕ) (h : cs.length % 2 = 1) : IsLoop cs := by
  obtain ⟨b, hb⟩ := affine cs
  have ht (x) : OMA.S_oeis_a236754.traverse cs x = b - x := by
    rw [hb]
    simp [h]
  refine ⟨2, by decide, by omega, ?_⟩
  simp only [afterLaps, ht]
  ring

private def balanced : ℕ → List ℕ
  | 0 => []
  | k + 1 => balanced k ++ [4 * k, 4 * k + 1, 4 * k + 3, 4 * k + 2]

private theorem balanced_perm (k : ℕ) : (balanced k).Perm (List.range (4 * k)) := by
  induction k with
  | zero => exact List.Perm.nil
  | succ k ih =>
      have he : List.range (4 * (k + 1)) =
          List.range (4 * k) ++ [4 * k, 4 * k + 1, 4 * k + 2, 4 * k + 3] := by
        rw [show 4 * (k + 1) = 4 * k + 1 + 1 + 1 + 1 by omega]
        simp only [List.range_succ, List.append_assoc]
        rfl
      rw [balanced, he]
      exact ih.append (List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ [])))

private theorem traverse_balanced (k : ℕ) (x : ℤ) : OMA.S_oeis_a236754.traverse (balanced k) x = x := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [balanced, traverse_append, ih]
      simp only [OMA.S_oeis_a236754.traverse, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring

private theorem traverse_range (k : ℕ) (x : ℤ) :
    OMA.S_oeis_a236754.traverse (List.range (2 * k)) x = x + 2 * (k : ℤ) := by
  induction k with
  | zero => simp [OMA.S_oeis_a236754.traverse]
  | succ k ih =>
      have he : List.range (2 * (k + 1)) =
          List.range (2 * k) ++ [2 * k, 2 * k + 1] := by
        rw [show 2 * (k + 1) = 2 * k + 1 + 1 by omega]
        simp only [List.range_succ, List.append_assoc]
        rfl
      rw [he, traverse_append, ih]
      simp only [OMA.S_oeis_a236754.traverse, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      ring

private theorem range_expands (n : ℕ) (hn : 0 < n) (he : 2 ∣ n) : IsExpanded (List.range n) := by
  obtain ⟨k, rfl⟩ := he
  have ht (x) : OMA.S_oeis_a236754.traverse (List.range (2 * k)) x = x + (2 * k : ℕ) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    exact traverse_range k x
  have hL (a : ℕ) :
      afterLaps (List.range (2 * k)) (start (List.range (2 * k))) a =
        start (List.range (2 * k)) + (a : ℤ) * ((2 * k : ℕ) : ℤ) := by
    induction a with
    | zero => simp [afterLaps]
    | succ a ih =>
        rw [afterLaps, ht, ih, Nat.cast_succ]
        ring
  have hs : start (List.range (2 * k)) = -1 := by
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    simp [hj, start, List.range_succ_eq_map]
  intro B
  let i : Fin (List.range (2 * k)).length := ⟨0, by simpa using hn⟩
  refine ⟨B + 2, i, ?_⟩
  have hi : (List.range (2 * k))[i] = 0 := by simp [i]
  rw [hi]
  change B < (afterLaps (List.range (2 * k)) (start (List.range (2 * k))) (B + 2) - 0).natAbs
  rw [sub_zero, hL, hs]
  have hm : (B : ℤ) + 2 ≤ ((B + 2 : ℕ) : ℤ) * ((2 * k : ℕ) : ℤ) := by
    have hk : (1 : ℤ) ≤ ((2 * k : ℕ) : ℤ) := by exact_mod_cast hn
    simpa using mul_le_mul_of_nonneg_left hk (show (0 : ℤ) ≤ (B : ℤ) + 2 by positivity)
  omega

end A236754

open A236754 OMA.S_oeis_a236754 in
theorem OMA.solution : type_of% @OMA.S_oeis_a236754.main := by
  classical
  constructor
  · intro n hn
    have hl (cs : List ℕ) (h : cs.Perm (List.range n)) : IsLoop cs := by
      apply odd_loop
      simpa [h.length_eq] using hn
    refine ⟨hl, ?_⟩
    unfold loopCount
    rw [List.filter_eq_self.mpr, List.length_permutations, List.length_range]
    intro cs h
    exact decide_eq_true (hl cs (List.mem_permutations.mp h))
  · intro n hn h₄
    have h₂ : 2 ∣ n := by omega
    refine ⟨?_, List.range n, List.Perm.refl _, range_expands n hn h₂⟩
    have hm : 4 * (n / 4) = n := by omega
    have hP := balanced_perm (n / 4)
    rw [hm] at hP
    refine ⟨_, hP, 1, by decide, ?_, ?_⟩
    · simpa [hP.length_eq] using (show n % 2 = 0 by omega)
    · simpa only [afterLaps] using traverse_balanced (n / 4) (start (balanced (n / 4)))