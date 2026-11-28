import OMAStatements.S_oeis_a225664
import Mathlib

/-!
# OEIS A225664: infinitely many decimal inputs have odd preperiod

Disproof. For every `t`, the number `10 ^ (t + 4)` has odd preperiod.
Its decimal vector is `1 :: replicate (t + 4) 0`, and writing `H` for `histogram`:
`H^3` of it is `[t + 3, 2]`; `H (H [n + 3, 2]) = [n + 2, 2]`; so `H^(2t + 3)` gives `[3, 2]`
and `H^(2 (t + 2))` gives `u = [0, 0, 1, 1]`.  Then `H u = [2, 2]` lies on the 6-cycle,
while `H^6 u = [1, 0, 0, 1] ≠ u`.
-/

namespace OMA.A225664

open OMA.S_oeis_a225664

lemma bump_nil (n : ℕ) : bump n [] = List.replicate n 0 ++ [1] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [bump, ih, List.replicate_succ]

lemma hist_zeros (n : ℕ) : histogram (List.replicate (n + 1) 0) = [n + 1] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have : histogram (List.replicate (n + 1 + 1) 0)
        = bump 0 (histogram (List.replicate (n + 1) 0)) := rfl
    rw [this, ih]; rfl

lemma hist_spike (n : ℕ) : histogram (List.replicate n 0 ++ [1]) = [n, 1] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have : histogram (List.replicate (n + 1) 0 ++ [1])
        = bump 0 (histogram (List.replicate n 0 ++ [1])) := rfl
    rw [this, ih]; rfl

lemma step_one (n : ℕ) : histogram (histogram [n + 2, 1]) = [n + 1, 2] := by
  have h1 : histogram [n + 2, 1] = 0 :: 1 :: (List.replicate n 0 ++ [1]) := by
    have : histogram [n + 2, 1] = 0 :: 1 :: bump n [] := rfl
    rw [this, bump_nil]
  have h2 : histogram (0 :: 1 :: (List.replicate n 0 ++ [1]))
      = bump 0 (bump 1 (histogram (List.replicate n 0 ++ [1]))) := rfl
  rw [h1, h2, hist_spike]; rfl

lemma step_two (n : ℕ) : histogram (histogram [n + 3, 2]) = [n + 2, 2] := by
  have h1 : histogram [n + 3, 2] = 0 :: 0 :: 1 :: (List.replicate n 0 ++ [1]) := by
    have : histogram [n + 3, 2] = 0 :: 0 :: 1 :: bump n [] := rfl
    rw [this, bump_nil]
  have h2 : histogram (0 :: 0 :: 1 :: (List.replicate n 0 ++ [1]))
      = bump 0 (bump 0 (bump 1 (histogram (List.replicate n 0 ++ [1])))) := rfl
  rw [h1, h2, hist_spike]; rfl

lemma iter_two (t m : ℕ) : histogram^[2 * t] [t + m + 3, 2] = [m + 3, 2] := by
  induction t generalizing m with
  | zero => simp
  | succ t ih =>
    have e : 2 * (t + 1) = 2 * t + 2 := by ring
    rw [e, Function.iterate_add_apply]
    have e2 : histogram^[2] [t + 1 + m + 3, 2] = [t + m + 3, 2] := by
      have := step_two (t + m + 1)
      have e3 : t + 1 + m + 3 = t + m + 1 + 3 := by ring
      rw [e3]; exact this
    rw [e2, ih]

lemma decimal_pow (k : ℕ) : decimal (10 ^ k) = 1 :: List.replicate k 0 := by
  have h := Nat.digits_base_pow_mul (b := 10) (k := k) (m := 1) (by norm_num) (by norm_num)
  have hne : (10 : ℕ) ^ k ≠ 0 := by positivity
  rw [mul_one] at h
  unfold decimal
  rw [if_neg hne, h]
  simp

lemma start (k : ℕ) : histogram^[3] (decimal (10 ^ (k + 2))) = [k + 1, 2] := by
  rw [decimal_pow]
  have h1 : histogram (1 :: List.replicate (k + 2) 0)
      = bump 1 (histogram (List.replicate (k + 1 + 1) 0)) := rfl
  have h2 : histogram^[3] (1 :: List.replicate (k + 2) 0)
      = histogram (histogram (histogram (1 :: List.replicate (k + 2) 0))) := rfl
  rw [h2, h1, hist_zeros]
  exact step_one k

lemma reach (t : ℕ) : histogram^[2 * (t + 2)] (decimal (10 ^ (t + 4))) = [0, 0, 1, 1] := by
  have e : 2 * (t + 2) = 1 + (2 * t + 3) := by ring
  rw [e, Function.iterate_add_apply, Function.iterate_add_apply]
  have h := start (t + 2)
  have e2 : t + 2 + 1 = t + 0 + 3 := by ring
  rw [e2] at h
  have h3 : histogram^[2 * t] [t + 0 + 3, 2] = [0 + 3, 2] := iter_two t 0
  rw [h, h3]
  rfl

lemma odd (t : ℕ) : oddPreperiod (decimal (10 ^ (t + 4))) := by
  refine ⟨t + 2, ?_⟩
  show histogram^[6] (histogram^[2 * (t + 2)] (decimal (10 ^ (t + 4))))
        ≠ histogram^[2 * (t + 2)] (decimal (10 ^ (t + 4))) ∧
      histogram^[6] (histogram (histogram^[2 * (t + 2)] (decimal (10 ^ (t + 4)))))
        = histogram (histogram^[2 * (t + 2)] (decimal (10 ^ (t + 4))))
  rw [reach]
  decide

end OMA.A225664

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a225664.main) := by
  intro hfin
  have hinf : {n : ℕ | OMA.S_oeis_a225664.oddPreperiod (OMA.S_oeis_a225664.decimal n)}.Infinite := by
    refine Set.infinite_of_injective_forall_mem (f := fun t : ℕ => 10 ^ (t + 4)) ?_ ?_
    · intro a b hab
      have := Nat.pow_right_injective (le_refl 2 |>.trans (by norm_num : 2 ≤ 10)) hab
      omega
    · intro t
      exact OMA.A225664.odd t
  exact hinf hfin
