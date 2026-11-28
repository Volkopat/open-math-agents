import OMAStatements.S_oeis_a396846
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a396846

open OMA.S_oeis_a396846

/-- Number of odd integers in `Finset.Icc 2 m` equals `(m - 1) / 2` for `m ≥ 1`. -/
private lemma card_odd_Icc_two (m : ℕ) (hm : 1 ≤ m) :
    ((Finset.Icc 2 m).filter (fun k => k % 2 = 1)).card = (m - 1) / 2 := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · decide
    · have hIcc : Finset.Icc 2 (m + 1) = insert (m + 1) (Finset.Icc 2 m) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.filter_insert]
      have hnotmem : m + 1 ∉ (Finset.Icc 2 m).filter (fun k => k % 2 = 1) := by
        simp only [Finset.mem_filter, Finset.mem_Icc]; omega
      by_cases hodd : (m + 1) % 2 = 1
      · rw [if_pos hodd, Finset.card_insert_of_notMem hnotmem, ih hmpos]; omega
      · rw [if_neg hodd, ih hmpos]; omega

private lemma prove_a396846 (a : ℕ → ℤ) (ha1 : a 1 = 1)
    (harec : ∀ n : ℕ, 2 ≤ n →
      (a n : ℚ) = ((4 * n ^ 2 - 1 : ℕ) : ℚ) *
        ((a (n - 1) : ℚ) +
          ∑ k ∈ Finset.Icc 2 (n - 1),
            (a (n - k) : ℚ) * (a k : ℚ) * (4 * (k : ℚ)) / ((4 * k ^ 2 - 1 : ℕ) : ℚ)))
    (n : ℕ) (hn : 1 ≤ n) :
    a n ≡ (if n % 4 = 1 then 1 else if n % 4 = 3 then 5 else 7) [ZMOD 8] := by
  let target : ℕ → ZMod 8 := fun m => if m % 4 = 1 then 1 else if m % 4 = 3 then 5 else 7
  have hmod8 : ∀ m : ℕ, 1 ≤ m → (a m : ZMod 8) = target m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      rcases Nat.eq_zero_or_pos (m - 1) with hm1 | hm2'
      · have : m = 1 := by omega
        subst this; simp [ha1, target]
      · have hm2 : 2 ≤ m := by omega
        have hrec := harec m hm2
        set D : ℕ := ∏ k ∈ Finset.Icc 2 (m - 1), (4 * k ^ 2 - 1)
        have hD_pos : ∀ k ∈ Finset.Icc 2 (m - 1), (4 * k ^ 2 - 1 : ℕ) ≠ 0 := by
          intro k hk
          have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
          have : 4 ≤ k ^ 2 := by nlinarith
          omega
        have hsum_int : (D : ℚ) * ∑ k ∈ Finset.Icc 2 (m - 1),
            (a (m - k) : ℚ) * (a k : ℚ) * (4 * (k : ℚ)) / ((4 * k ^ 2 - 1 : ℕ) : ℚ) =
            ((∑ k ∈ Finset.Icc 2 (m - 1),
              a (m - k) * a k * (4 * (k : ℤ)) * ((∏ j ∈ (Finset.Icc 2 (m - 1)).erase k, (4 * j ^ 2 - 1) : ℕ) : ℤ) : ℤ) : ℚ) := by
          rw [Finset.mul_sum]
          push_cast
          refine Finset.sum_congr rfl (fun k hk => ?_)
          have hDk : (D : ℚ) = ((4 * k ^ 2 - 1 : ℕ) : ℚ) *
              (∏ j ∈ (Finset.Icc 2 (m - 1)).erase k, ((4 * j ^ 2 - 1 : ℕ) : ℚ)) := by
            dsimp [D]
            rw [← Finset.mul_prod_erase (Finset.Icc 2 (m - 1)) (fun j => 4 * j ^ 2 - 1) hk]
            push_cast; rfl
          have hne : ((4 * k ^ 2 - 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hD_pos k hk)
          rw [hDk]
          field_simp [hne]
        have hmul_q := congr_arg (fun z : ℚ => (D : ℚ) * z) hrec
        have heq_q : ((D : ℤ) * a m : ℚ) =
            (((4 * m ^ 2 - 1 : ℕ) : ℤ) * ((D : ℤ) * a (m - 1) +
              ∑ k ∈ Finset.Icc 2 (m - 1),
                a (m - k) * a k * (4 * (k : ℤ)) * ((∏ j ∈ (Finset.Icc 2 (m - 1)).erase k, (4 * j ^ 2 - 1) : ℕ) : ℤ)) : ℚ) := by
          calc ((D : ℤ) * a m : ℚ)
              = (D : ℚ) * (a m : ℚ) := by push_cast; rfl
            _ = (D : ℚ) * (((4 * m ^ 2 - 1 : ℕ) : ℚ) * ((a (m - 1) : ℚ) +
                  ∑ k ∈ Finset.Icc 2 (m - 1), (a (m - k) : ℚ) * (a k : ℚ) * (4 * (k : ℚ)) / ((4 * k ^ 2 - 1 : ℕ) : ℚ))) := hmul_q
            _ = ((4 * m ^ 2 - 1 : ℕ) : ℚ) * ((D : ℚ) * (a (m - 1) : ℚ) +
                  (D : ℚ) * ∑ k ∈ Finset.Icc 2 (m - 1), (a (m - k) : ℚ) * (a k : ℚ) * (4 * (k : ℚ)) / ((4 * k ^ 2 - 1 : ℕ) : ℚ)) := by ring
            _ = _ := by rw [hsum_int]; push_cast; ring
        have heq_z : (D : ℤ) * a m =
            ((4 * m ^ 2 - 1 : ℕ) : ℤ) * ((D : ℤ) * a (m - 1) +
              ∑ k ∈ Finset.Icc 2 (m - 1),
                a (m - k) * a k * (4 * (k : ℤ)) * ((∏ j ∈ (Finset.Icc 2 (m - 1)).erase k, (4 * j ^ 2 - 1) : ℕ) : ℤ)) := by
          exact_mod_cast heq_q
        have hcast := congr_arg (Int.cast (R := ZMod 8)) heq_z
        push_cast at hcast
        -- Every `4 * j^2 - 1` is odd, so `D` is odd (a unit in `ZMod 8`) and `4 * (odd) = 4` in `ZMod 8`!
        have hodd_four : ∀ x : ZMod 8, (∃ u : ZMod 8, x = 2 * u + 1) → x * 4 = 4 := by
          intro x ⟨u, hu⟩; subst hu
          have h8 : (8 : ZMod 8) = 0 := by decide
          linear_combination u * h8
        have htarget_odd : ∀ r : ℕ, ∃ u : ZMod 8, target r = 2 * u + 1 := by
          intro r; dsimp [target]
          split_ifs
          · exact ⟨0, by decide⟩
          · exact ⟨2, by decide⟩
          · exact ⟨3, by decide⟩
        have hprod_odd : ∀ S : Finset ℕ, (∀ j ∈ S, 1 ≤ j) →
            ∃ u : ZMod 8, ((∏ j ∈ S, (4 * j ^ 2 - 1) : ℕ) : ZMod 8) = 2 * u + 1 := by
          intro S hS
          induction S using Finset.induction_on with
          | empty => exact ⟨0, by simp⟩
          | insert j s hj ihs =>
            rw [Finset.prod_insert hj, Nat.cast_mul]
            obtain ⟨u1, hu1⟩ := ihs (fun x hx => hS x (Finset.mem_insert_of_mem hx))
            have hj1 : 1 ≤ j := hS j (Finset.mem_insert_self j s)
            have hfac_odd : ∃ v : ZMod 8, ((4 * j ^ 2 - 1 : ℕ) : ZMod 8) = 2 * v + 1 := by
              have h1 : 1 ≤ 4 * j ^ 2 := by nlinarith
              rw [Nat.cast_sub h1]; push_cast
              refine ⟨2 * (j : ZMod 8) ^ 2 - 1, by ring⟩
            obtain ⟨v, hv⟩ := hfac_odd
            rw [hv, hu1]
            exact ⟨2 * v * u1 + v + u1, by ring⟩
        have hD_odd : ∃ u : ZMod 8, (D : ZMod 8) = 2 * u + 1 :=
          hprod_odd (Finset.Icc 2 (m - 1)) (fun j hj => by have := (Finset.mem_Icc.mp hj).1; omega)
        have hD_unit : IsUnit (D : ZMod 8) := by
          obtain ⟨u, hu⟩ := hD_odd
          rw [hu]
          -- Every odd element in `ZMod 8` is its own inverse (`(2u + 1)^2 = 1`)!
          have hsq : (2 * u + 1) * (2 * u + 1) = 1 := by
            have h4 : (4 : ZMod 8) * (u * (u + 1)) = 0 := by
              fin_cases u <;> decide
            linear_combination h4
          exact ⟨⟨2 * u + 1, 2 * u + 1, hsq, hsq⟩, rfl⟩
        -- Evaluate the sum mod 8: term `k` is `4` if `k` is odd, `0` if `k` is even!
        have hsum8 : ∑ k ∈ Finset.Icc 2 (m - 1),
            (a (m - k) : ZMod 8) * (a k : ZMod 8) * (4 * (k : ZMod 8)) *
              ((∏ j ∈ (Finset.Icc 2 (m - 1)).erase k, (4 * j ^ 2 - 1) : ℕ) : ZMod 8) =
            (((m - 2) / 2 : ℕ) : ZMod 8) * 4 := by
          have hterm : ∀ k ∈ Finset.Icc 2 (m - 1),
              (a (m - k) : ZMod 8) * (a k : ZMod 8) * (4 * (k : ZMod 8)) *
                ((∏ j ∈ (Finset.Icc 2 (m - 1)).erase k, (4 * j ^ 2 - 1) : ℕ) : ZMod 8) =
              if k % 2 = 1 then (4 : ZMod 8) else 0 := by
            intro k hk
            have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
            have hkm : k ≤ m - 1 := (Finset.mem_Icc.mp hk).2
            rw [ih (m - k) (by omega) (by omega), ih k (by omega) (by omega)]
            obtain ⟨u1, hu1⟩ := htarget_odd (m - k)
            obtain ⟨u2, hu2⟩ := htarget_odd k
            obtain ⟨u3, hu3⟩ := hprod_odd ((Finset.Icc 2 (m - 1)).erase k)
              (fun j hj => by have := (Finset.mem_Icc.mp (Finset.mem_erase.mp hj).2).1; omega)
            rw [hu1, hu2, hu3]
            by_cases hkodd : k % 2 = 1
            · rw [if_pos hkodd]
              have hk4 : (4 : ZMod 8) * (k : ZMod 8) = 4 := by
                have hk_eq : k = 2 * (k / 2) + 1 := by omega
                conv_lhs => rw [hk_eq]
                push_cast
                have h8 : (8 : ZMod 8) = 0 := by decide
                linear_combination ((k / 2 : ℕ) : ZMod 8) * h8
              rw [hk4]
              have hprod : (2 * u1 + 1) * (2 * u2 + 1) * (2 * u3 + 1) =
                  2 * (2 * u1 * u2 * (2 * u3 + 1) + u1 * (2 * u3 + 1) + u2 * (2 * u3 + 1) + u3) + 1 := by ring
              have hrearr : (2 * u1 + 1) * (2 * u2 + 1) * 4 * (2 * u3 + 1) =
                  ((2 * u1 + 1) * (2 * u2 + 1) * (2 * u3 + 1)) * 4 := by ring
              rw [hrearr, hprod]
              exact hodd_four _ ⟨_, rfl⟩
            · rw [if_neg hkodd]
              have hk_eq : k = 2 * (k / 2) := by omega
              have hk4 : (4 : ZMod 8) * (k : ZMod 8) = 0 := by
                conv_lhs => rw [hk_eq]
                push_cast
                have h8 : (8 : ZMod 8) = 0 := by decide
                linear_combination ((k / 2 : ℕ) : ZMod 8) * h8
              rw [hk4]; ring
          rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
            card_odd_Icc_two (m - 1) (by omega), show m - 1 - 1 = m - 2 by omega]
        simp only [← Nat.cast_prod] at hcast
        rw [hsum8, ih (m - 1) (by omega) (by omega)] at hcast
        -- Replace `((m - 2) / 2) * 4` by `(D : ZMod 8) * (((m - 2) / 2) * 4)` since `D` is odd!
        have hD4 : (D : ZMod 8) * ((((m - 2) / 2 : ℕ) : ZMod 8) * 4) = (((m - 2) / 2 : ℕ) : ZMod 8) * 4 := by
          have : (D : ZMod 8) * ((((m - 2) / 2 : ℕ) : ZMod 8) * 4) =
              (((m - 2) / 2 : ℕ) : ZMod 8) * ((D : ZMod 8) * 4) := by ring
          rw [this, hodd_four _ hD_odd]
        rw [← hD4] at hcast
        have hfactor : (D : ZMod 8) * (a m : ZMod 8) =
            (D : ZMod 8) * (((4 * m ^ 2 - 1 : ℕ) : ZMod 8) * (target (m - 1) + (((m - 2) / 2 : ℕ) : ZMod 8) * 4)) := by
          linear_combination hcast
        have hval_m : (a m : ZMod 8) =
            ((4 * m ^ 2 - 1 : ℕ) : ZMod 8) * (target (m - 1) + (((m - 2) / 2 : ℕ) : ZMod 8) * 4) :=
          hD_unit.mul_left_cancel hfactor
        rw [hval_m]
        -- Case split on `m % 4`!
        have h1 : 1 ≤ 4 * m ^ 2 := by nlinarith
        rw [Nat.cast_sub h1]; push_cast
        have h4m2 : (4 : ZMod 8) * (m : ZMod 8) ^ 2 = if m % 2 = 1 then 4 else 0 := by
          by_cases hpar : m % 2 = 1
          · rw [if_pos hpar]
            have hm_eq : m = 2 * (m / 2) + 1 := by omega
            conv_lhs => rw [hm_eq]
            push_cast
            have h8 : (8 : ZMod 8) = 0 := by decide
            linear_combination (2 * ((m / 2 : ℕ) : ZMod 8) ^ 2 + 2 * ((m / 2 : ℕ) : ZMod 8)) * h8
          · rw [if_neg hpar]
            have hm_eq : m = 2 * (m / 2) := by omega
            conv_lhs => rw [hm_eq]
            push_cast
            have h8 : (8 : ZMod 8) = 0 := by decide
            linear_combination (2 * ((m / 2 : ℕ) : ZMod 8) ^ 2) * h8
        have hhalf4 : (((m - 2) / 2 : ℕ) : ZMod 8) * 4 = if ((m - 2) / 2) % 2 = 1 then 4 else 0 := by
          by_cases hpar : ((m - 2) / 2) % 2 = 1
          · rw [if_pos hpar]
            have hq : (m - 2) / 2 = 2 * ((m - 2) / 2 / 2) + 1 := by omega
            conv_lhs => rw [hq]
            push_cast
            have h8 : (8 : ZMod 8) = 0 := by decide
            linear_combination (((m - 2) / 2 / 2 : ℕ) : ZMod 8) * h8
          · rw [if_neg hpar]
            have hq : (m - 2) / 2 = 2 * ((m - 2) / 2 / 2) := by omega
            conv_lhs => rw [hq]
            push_cast
            have h8 : (8 : ZMod 8) = 0 := by decide
            linear_combination (((m - 2) / 2 / 2 : ℕ) : ZMod 8) * h8
        rw [h4m2, hhalf4]
        dsimp [target]
        have hmod4 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
        rcases hmod4 with h | h | h | h
        · have h1' : m % 2 = 0 := by omega
          have h2' : (m - 1) % 4 = 3 := by omega
          have h3' : ((m - 2) / 2) % 2 = 1 := by omega
          simp [h, h1', h2', h3']; decide
        · have h1' : m % 2 = 1 := by omega
          have h2' : (m - 1) % 4 = 0 := by omega
          have h3' : ((m - 2) / 2) % 2 = 1 := by omega
          simp [h, h1', h2', h3']; decide
        · have h1' : m % 2 = 0 := by omega
          have h2' : (m - 1) % 4 = 1 := by omega
          have h3' : ((m - 2) / 2) % 2 = 0 := by omega
          simp [h, h1', h2', h3']; decide
        · have h1' : m % 2 = 1 := by omega
          have h2' : (m - 1) % 4 = 2 := by omega
          have h3' : ((m - 2) / 2) % 2 = 0 := by omega
          simp [h, h1', h2', h3']; decide
  have hval : (a n : ZMod 8) = ((if n % 4 = 1 then (1 : ℤ) else if n % 4 = 3 then 5 else 7 : ℤ) : ZMod 8) := by
    rw [hmod8 n hn]
    dsimp [target]
    split_ifs <;> simp
  exact (ZMod.intCast_eq_intCast_iff (a n) (if n % 4 = 1 then 1 else if n % 4 = 3 then 5 else 7) 8).mp hval

end OMA.P_oeis_a396846

theorem OMA.solution : type_of% @OMA.S_oeis_a396846.main :=
  OMA.P_oeis_a396846.prove_a396846
