import OMAStatements.S_oeis_a225665
import Mathlib

open OMA.S_oeis_a225665

namespace OMA.A225665

theorem hist_cons (a : ℕ) (l : List ℕ) : histogram (a :: l) = bump a (histogram l) := rfl

theorem hist_bump_nil (n : ℕ) : histogram (bump n []) = [n, 1] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show histogram (0 :: bump n []) = [n + 1, 1]
    rw [hist_cons, ih]; rfl

theorem hist_zeros (k : ℕ) : histogram (List.replicate (k + 1) 0) = [k + 1] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, hist_cons, ih]; rfl

theorem digits_pow (k : ℕ) : Nat.digits 16 (16 ^ k) = List.replicate k 0 ++ [1] := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Nat.digits_def' (by norm_num) (by positivity)]
    have h1 : 16 ^ (k + 1) % 16 = 0 := by rw [pow_succ]; simp
    have h2 : 16 ^ (k + 1) / 16 = 16 ^ k := by rw [pow_succ]; simp
    rw [h1, h2, ih]; rfl

theorem hex_pow (k : ℕ) : hexadecimal (16 ^ k) = 1 :: List.replicate k 0 := by
  have h : (16 : ℕ) ^ k ≠ 0 := by positivity
  unfold hexadecimal
  rw [if_neg h, digits_pow]
  simp

theorem step1 (k : ℕ) : histogram (hexadecimal (16 ^ (k + 1))) = [k + 1, 1] := by
  rw [hex_pow, hist_cons, hist_zeros]; rfl

theorem step2 (n : ℕ) : histogram (histogram [n + 2, 1]) = [n + 1, 2] := by
  have h : histogram [n + 2, 1] = 0 :: 1 :: bump n [] := rfl
  rw [h, hist_cons, hist_cons, hist_bump_nil]; rfl

theorem step3 (n : ℕ) : histogram (histogram [n + 3, 2]) = [n + 2, 2] := by
  have h : histogram [n + 3, 2] = 0 :: 0 :: 1 :: bump n [] := rfl
  rw [h, hist_cons, hist_cons, hist_cons, hist_bump_nil]; rfl

theorem descend (i : ℕ) : histogram^[2 * i] [i + 3, 2] = [3, 2] := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have e : 2 * (i + 1) = 2 * i + 2 := by ring
    rw [e, Function.iterate_add_apply]
    show histogram^[2 * i] (histogram (histogram [i + 1 + 3, 2])) = [3, 2]
    rw [step3]; exact ih

theorem reach (i : ℕ) :
    histogram^[2 * (i + 2)] (hexadecimal (16 ^ (i + 4))) = [0, 0, 1, 1] := by
  have e : 2 * (i + 2) = 1 + (2 * i + (2 + 1)) := by ring
  rw [e, Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_add_apply]
  show histogram (histogram^[2 * i]
    (histogram (histogram (histogram (hexadecimal (16 ^ (i + 3 + 1))))))) = [0, 0, 1, 1]
  rw [step1]
  show histogram (histogram^[2 * i] (histogram (histogram [i + 2 + 2, 1]))) = [0, 0, 1, 1]
  rw [step2]
  show histogram (histogram^[2 * i] [i + 3, 2]) = [0, 0, 1, 1]
  rw [descend]; rfl

theorem mem (i : ℕ) : oddPreperiod (hexadecimal (16 ^ (i + 4))) := by
  refine ⟨i + 2, ?_⟩
  show histogram^[6] (histogram^[2 * (i + 2)] (hexadecimal (16 ^ (i + 4)))) ≠
      histogram^[2 * (i + 2)] (hexadecimal (16 ^ (i + 4))) ∧
    histogram^[6] (histogram (histogram^[2 * (i + 2)] (hexadecimal (16 ^ (i + 4))))) =
      histogram (histogram^[2 * (i + 2)] (hexadecimal (16 ^ (i + 4))))
  rw [reach]
  constructor
  · decide
  · decide

end OMA.A225665

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a225665.main) := by
  intro hfin
  have hinf : {n : ℕ | oddPreperiod (hexadecimal n)}.Infinite := by
    refine Set.infinite_of_injective_forall_mem (f := fun i : ℕ => 16 ^ (i + 4)) ?_ ?_
    · intro a b hab
      have := Nat.pow_right_injective (le_refl 2 |>.trans (by norm_num : 2 ≤ 16)) hab
      omega
    · intro i
      exact OMA.A225665.mem i
  exact hinf hfin
