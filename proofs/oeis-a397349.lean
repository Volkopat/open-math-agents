import OMAStatements.S_oeis_a397349
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a397349

open OMA.S_oeis_a397349

private lemma prove_a397349 (a : ℕ → ℤ) (ha1 : a 1 = 1)
    (harec : ∀ n : ℕ, 2 ≤ n →
      (a n : ℚ) = ((3 * n ^ 2 - 1 : ℕ) : ℚ) *
        ((a (n - 1) : ℚ) +
          ∑ k ∈ Finset.Icc 2 (n - 1),
            (a (n - k) : ℚ) * (a k : ℚ) * (3 * (k : ℚ)) / ((3 * k ^ 2 - 1 : ℕ) : ℚ)))
    (n : ℕ) (hn : 1 ≤ n) :
    a n ≡ (if n % 2 = 1 then 1 else 2) [ZMOD 3] := by
  have hmod3 : ∀ m : ℕ, 1 ≤ m → (a m : ZMod 3) = if m % 2 = 1 then 1 else 2 := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hmpos
      · simp [ha1]
      · have hm2 : 2 ≤ m + 1 := by omega
        have hrec := harec (m + 1) hm2
        -- Clear denominators by multiplying by `D = ∏ k ∈ Icc 2 m, (3*k^2 - 1)`!
        set D : ℕ := ∏ k ∈ Finset.Icc 2 m, (3 * k ^ 2 - 1)
        have hD_pos : ∀ k ∈ Finset.Icc 2 m, (3 * k ^ 2 - 1 : ℕ) ≠ 0 := by
          intro k hk
          have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
          have : 4 ≤ k ^ 2 := by nlinarith
          omega
        -- Express `D * ∑ (...)` as an integer sum divisible by `3`!
        have hsum_int : (D : ℚ) * ∑ k ∈ Finset.Icc 2 m,
            (a (m + 1 - k) : ℚ) * (a k : ℚ) * (3 * (k : ℚ)) / ((3 * k ^ 2 - 1 : ℕ) : ℚ) =
            ((3 * ∑ k ∈ Finset.Icc 2 m,
              a (m + 1 - k) * a k * (k : ℤ) * ((∏ j ∈ (Finset.Icc 2 m).erase k, (3 * j ^ 2 - 1) : ℕ) : ℤ) : ℤ) : ℚ) := by
          rw [Finset.mul_sum]
          push_cast
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k hk => ?_)
          have hDk : (D : ℚ) = ((3 * k ^ 2 - 1 : ℕ) : ℚ) *
              (∏ j ∈ (Finset.Icc 2 m).erase k, ((3 * j ^ 2 - 1 : ℕ) : ℚ)) := by
            dsimp [D]
            rw [← Finset.mul_prod_erase (Finset.Icc 2 m) (fun j => 3 * j ^ 2 - 1) hk]
            push_cast; rfl
          have hne : ((3 * k ^ 2 - 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hD_pos k hk)
          rw [hDk]
          field_simp [hne]
        have hmul_q := congr_arg (fun z : ℚ => (D : ℚ) * z) hrec
        simp only [Nat.add_sub_cancel] at hmul_q
        have heq_q : ((D : ℤ) * a (m + 1) : ℚ) =
            (((3 * (m + 1) ^ 2 - 1 : ℕ) : ℤ) * ((D : ℤ) * a m +
              3 * ∑ k ∈ Finset.Icc 2 m,
                a (m + 1 - k) * a k * (k : ℤ) * ((∏ j ∈ (Finset.Icc 2 m).erase k, (3 * j ^ 2 - 1) : ℕ) : ℤ)) : ℚ) := by
          calc ((D : ℤ) * a (m + 1) : ℚ)
              = (D : ℚ) * (a (m + 1) : ℚ) := by push_cast; rfl
            _ = (D : ℚ) * (((3 * (m + 1) ^ 2 - 1 : ℕ) : ℚ) * ((a m : ℚ) +
                  ∑ k ∈ Finset.Icc 2 m, (a (m + 1 - k) : ℚ) * (a k : ℚ) * (3 * (k : ℚ)) / ((3 * k ^ 2 - 1 : ℕ) : ℚ))) := hmul_q
            _ = ((3 * (m + 1) ^ 2 - 1 : ℕ) : ℚ) * ((D : ℚ) * (a m : ℚ) +
                  (D : ℚ) * ∑ k ∈ Finset.Icc 2 m, (a (m + 1 - k) : ℚ) * (a k : ℚ) * (3 * (k : ℚ)) / ((3 * k ^ 2 - 1 : ℕ) : ℚ)) := by ring
            _ = _ := by rw [hsum_int]; push_cast; ring
        have heq_z : (D : ℤ) * a (m + 1) =
            ((3 * (m + 1) ^ 2 - 1 : ℕ) : ℤ) * ((D : ℤ) * a m +
              3 * ∑ k ∈ Finset.Icc 2 m,
                a (m + 1 - k) * a k * (k : ℤ) * ((∏ j ∈ (Finset.Icc 2 m).erase k, (3 * j ^ 2 - 1) : ℕ) : ℤ)) := by
          exact_mod_cast heq_q
        have hcast := congr_arg (Int.cast (R := ZMod 3)) heq_z
        push_cast at hcast
        have h30 : (3 : ZMod 3) = 0 := by decide
        have hcoeff : ((3 * (m + 1) ^ 2 - 1 : ℕ) : ZMod 3) = -1 := by
          have h1 : 1 ≤ 3 * (m + 1) ^ 2 := by nlinarith
          rw [Nat.cast_sub h1]; push_cast; rw [h30]; ring
        have hD_unit : (D : ZMod 3) ≠ 0 := by
          dsimp [D]
          rw [Nat.cast_prod]
          refine Finset.prod_ne_zero_iff.mpr (fun k hk => ?_)
          have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
          have h1 : 1 ≤ 3 * k ^ 2 := by nlinarith
          rw [Nat.cast_sub h1]; push_cast; rw [h30, zero_mul, zero_sub]; decide
        rw [h30, zero_mul, add_zero, hcoeff] at hcast
        have hstep : (D : ZMod 3) * ((a (m + 1) : ZMod 3) + (a m : ZMod 3)) = 0 := by
          linear_combination hcast
        have hadd0 : (a (m + 1) : ZMod 3) + (a m : ZMod 3) = 0 :=
          (mul_eq_zero.mp hstep).resolve_left hD_unit
        have hih := ih hmpos
        rw [hih] at hadd0
        by_cases hpar : m % 2 = 1
        · have hpar1 : (m + 1) % 2 ≠ 1 := by omega
          rw [if_pos hpar] at hadd0
          rw [if_neg hpar1]
          have h3 : (1 : ZMod 3) + 2 = 0 := by decide
          linear_combination hadd0 - h3
        · have hpar1 : (m + 1) % 2 = 1 := by omega
          rw [if_neg hpar] at hadd0
          rw [if_pos hpar1]
          have h3 : (1 : ZMod 3) + 2 = 0 := by decide
          linear_combination hadd0 - h3
  have hval : (a n : ZMod 3) = ((if n % 2 = 1 then (1 : ℤ) else 2 : ℤ) : ZMod 3) := by
    rw [hmod3 n hn]
    split_ifs <;> simp
  exact (ZMod.intCast_eq_intCast_iff (a n) (if n % 2 = 1 then 1 else 2) 3).mp hval

end OMA.P_oeis_a397349

theorem OMA.solution : type_of% @OMA.S_oeis_a397349.main :=
  OMA.P_oeis_a397349.prove_a397349
