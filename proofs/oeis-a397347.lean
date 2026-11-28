import OMAStatements.S_oeis_a397347
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a397347

open OMA.S_oeis_a397347

/-- Auxiliary integer sequence `b n = a n / (2 * n^2 - 1)` for `n ≥ 1`. -/
private def bSeq (a : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    a (n + 1) +
      ∑ k : Fin n,
        (2 * ((k.1 + 2 : ℕ) : ℤ)) * bSeq a (k.1 + 2) * a (n - k.1)

private lemma bSeq_eq_Ico (a : ℕ → ℤ) (n : ℕ) (hn : 2 ≤ n) :
    bSeq a n = a (n - 1) +
      ∑ k ∈ Finset.Ico 2 n, (2 * (k : ℤ)) * bSeq a k * a (n - k) := by
  rcases Nat.exists_eq_add_of_le hn with ⟨r, rfl⟩
  rw [show 2 + r = r + 2 by omega, show r + 2 - 1 = r + 1 by omega]
  conv_lhs => unfold bSeq
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun k => (2 * ((k + 2 : ℕ) : ℤ)) * bSeq a (k + 2) * a (r - k))]
  refine Finset.sum_bij (fun k _ => k + 2) ?_ ?_ ?_ ?_
  · intro k hk; rw [Finset.mem_range] at hk; rw [Finset.mem_Ico]; omega
  · intro k1 _ k2 _ h; omega
  · intro j hj; rw [Finset.mem_Ico] at hj; exact ⟨j - 2, Finset.mem_range.mpr (by omega), by omega⟩
  · intro k hk; rw [Finset.mem_range] at hk; rw [show r + 2 - (k + 2) = r - k by omega]

private lemma coeff_mul_range_rev {R : Type*} [CommSemiring R] (f g : PowerSeries R) (m : ℕ) :
    PowerSeries.coeff m (f * g) =
      ∑ j ∈ Finset.range (m + 1), PowerSeries.coeff j f * PowerSeries.coeff (m - j) g := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => PowerSeries.coeff x f * PowerSeries.coeff y g) m]

private lemma sum_two_mul_Ico_mod4 (n : ℕ) (hn : 2 ≤ n) :
    (∑ k ∈ Finset.Ico 2 n, ((2 * k : ℕ) : ZMod 4)) =
      if (n / 2 - 1) % 2 = 1 then 2 else 0 := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_Ico_succ_top hm, ih]
    have h4 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
    rcases h4 with h | h | h | h
    · have h2m : ((2 * m : ℕ) : ZMod 4) = 0 := by
        rw [← ZMod.natCast_mod, show 2 * m % 4 = 0 by omega]; rfl
      rw [h2m, add_zero, show (m + 1) / 2 = m / 2 by omega]
    · have h2m : ((2 * m : ℕ) : ZMod 4) = 2 := by
        rw [← ZMod.natCast_mod, show 2 * m % 4 = 2 by omega]; rfl
      rw [h2m, show (m / 2 - 1) % 2 = 1 by omega, show ((m + 1) / 2 - 1) % 2 = 0 by omega]
      decide
    · have h2m : ((2 * m : ℕ) : ZMod 4) = 0 := by
        rw [← ZMod.natCast_mod, show 2 * m % 4 = 0 by omega]; rfl
      rw [h2m, add_zero, show (m + 1) / 2 = m / 2 by omega]
    · have h2m : ((2 * m : ℕ) : ZMod 4) = 2 := by
        rw [← ZMod.natCast_mod, show 2 * m % 4 = 2 by omega]; rfl
      rw [h2m, show (m / 2 - 1) % 2 = 0 by omega, show ((m + 1) / 2 - 1) % 2 = 1 by omega]
      decide

private theorem prove_main : type_of% @OMA.S_oeis_a397347.main := by
  intro a hEq
  set B : PowerSeries ℚ := PowerSeries.mk fun n =>
    if n = 0 then (1 : ℚ)
    else if n = 1 then (1 : ℚ)
    else ((2 * (n : ℚ)) / (2 * (n : ℚ) ^ 2 - 1)) * (a n : ℚ)
  set L : PowerSeries ℚ := PowerSeries.mk fun n =>
    if n = 0 then (0 : ℚ) else (a n : ℚ) / (n : ℚ)
  have hL0 : PowerSeries.constantCoeff L = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]; simp [L]
  have hSub : PowerSeries.HasSubst L := PowerSeries.HasSubst.of_constantCoeff_zero hL0
  -- Differentiate B = subst L (exp ℚ) to get B' = B * L'
  have hderiv : PowerSeries.derivative ℚ B = B * PowerSeries.derivative ℚ L := by
    conv_lhs => rw [hEq]
    rw [PowerSeries.derivative_subst hSub, PowerSeries.derivative_exp, ← hEq]
  -- Step 1: coeff 0 (derivative L) = a 1, and coeff m (derivative L) = a (m + 1)
  have hdL : ∀ m : ℕ, PowerSeries.coeff m (PowerSeries.derivative ℚ L) = (a (m + 1) : ℚ) := by
    intro m
    rw [PowerSeries.coeff_derivative]
    simp only [L, PowerSeries.coeff_mk, show m + 1 ≠ 0 by omega, ↓reduceIte]
    have hne : ((m + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp [hne]
  -- Step 2: a 1 = 1 from coeff 0 of hderiv
  have ha1 : a 1 = 1 := by
    have hc := congrArg (PowerSeries.coeff 0) hderiv
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero,
      Finset.sum_singleton, hdL 0] at hc
    simp only [B, PowerSeries.coeff_mk] at hc
    norm_num at hc
    exact_mod_cast hc.symm
  -- Step 3: For all n ≥ 1, a n = (2 * n^2 - 1) * bSeq a n
  have ha_eq : ∀ n : ℕ, 1 ≤ n → a n = (2 * (n : ℤ) ^ 2 - 1) * bSeq a n := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      cases n with
      | zero => omega
      | succ m =>
        cases m with
        | zero => simp [bSeq, ha1]
        | succ r =>
          have hc := congrArg (PowerSeries.coeff (r + 1)) hderiv
          rw [PowerSeries.coeff_derivative, coeff_mul_range_rev] at hc
          simp_rw [hdL] at hc
          -- Split off j = 0 (B_0 * a(r+2)) and j = 1 (B_1 * a(r+1)) from range (r + 2)
          rw [Finset.sum_range_succ', Finset.sum_range_succ'] at hc
          simp only [B, PowerSeries.coeff_mk, show r + 1 + 1 ≠ 0 by omega,
            show r + 1 + 1 ≠ 1 by omega, ↓reduceIte, Nat.sub_zero, one_mul,
            show r + 1 - 1 = r by omega] at hc
          have hB1 : (if (1 : ℕ) = 0 then (1 : ℚ) else 1) = 1 := by norm_num
          rw [hB1, one_mul] at hc
          -- Simplify middle sum j ∈ range r (corresponding to k = j + 2)
          have hmid : ∑ j ∈ Finset.range r,
              (if j + 1 + 1 = 0 then (1 : ℚ) else if j + 1 + 1 = 1 then 1 else
                2 * ((j + 1 + 1 : ℕ) : ℚ) / (2 * ((j + 1 + 1 : ℕ) : ℚ) ^ 2 - 1) * (a (j + 1 + 1) : ℚ)) *
                (a (r + 1 - (j + 1 + 1) + 1) : ℚ) =
              ((∑ k : Fin r, (2 * ((k.1 + 2 : ℕ) : ℤ)) * bSeq a (k.1 + 2) * a (r - k.1) : ℤ) : ℚ) := by
            rw [Fin.sum_univ_eq_sum_range (fun k => (2 * ((k + 2 : ℕ) : ℤ)) * bSeq a (k + 2) * a (r - k))]
            push_cast
            refine Finset.sum_congr rfl fun j hj => ?_
            rw [Finset.mem_range] at hj
            have hih := ih (j + 2) (by omega) (by omega)
            have hihQ : (a (j + 2) : ℚ) = (2 * ((j + 2 : ℕ) : ℚ) ^ 2 - 1) * (bSeq a (j + 2) : ℚ) := by
              exact_mod_cast hih
            rw [show j + 1 + 1 = j + 2 by omega, show r - (j + 1) + 1 = r - j by omega, hihQ]
            rw [show ((j : ℚ) + 1 + 1) = ((j : ℚ) + 2) by ring]
            push_cast
            have hden : 2 * ((j : ℚ) + 2) ^ 2 - 1 ≠ 0 := by
              have hge : (0 : ℚ) ≤ (j : ℚ) := Nat.cast_nonneg j
              nlinarith
            field_simp [hden]
          have hc' : (2 * ((r + 2 : ℕ) : ℚ)) / (2 * ((r + 2 : ℕ) : ℚ) ^ 2 - 1) * (a (r + 2) : ℚ) * ((r + 2 : ℕ) : ℚ) =
              ((∑ k : Fin r, (2 * ((k.1 + 2 : ℕ) : ℤ)) * bSeq a (k.1 + 2) * a (r - k.1) : ℤ) : ℚ) +
                (a (r + 1) : ℚ) + (a (r + 2) : ℚ) := by
            rw [← hmid]
            rw [show ((r + 1 : ℕ) : ℚ) + 1 = ((r + 2 : ℕ) : ℚ) by push_cast; ring] at hc
            simpa only [show r + 1 + 1 = r + 2 by omega] using hc
          have hden : 2 * ((r + 2 : ℕ) : ℚ) ^ 2 - 1 ≠ 0 := by
            have hge : (2 : ℚ) ≤ ((r + 2 : ℕ) : ℚ) := by exact_mod_cast (show 2 ≤ r + 2 by omega)
            nlinarith
          have haQ : (a (r + 2) : ℚ) = (2 * ((r + 2 : ℕ) : ℚ) ^ 2 - 1) * (bSeq a (r + 2) : ℚ) := by
            conv_rhs => unfold bSeq
            have hdiff : 2 * ((r + 2 : ℕ) : ℚ) / (2 * ((r + 2 : ℕ) : ℚ) ^ 2 - 1) * (a (r + 2) : ℚ) * ((r + 2 : ℕ) : ℚ) -
                (a (r + 2) : ℚ) = (a (r + 2) : ℚ) / (2 * ((r + 2 : ℕ) : ℚ) ^ 2 - 1) := by
              field_simp [hden]; ring
            have hstep : (a (r + 2) : ℚ) / (2 * ((r + 2 : ℕ) : ℚ) ^ 2 - 1) =
                (a (r + 1) : ℚ) + ((∑ k : Fin r, (2 * ((k.1 + 2 : ℕ) : ℤ)) * bSeq a (k.1 + 2) * a (r - k.1) : ℤ) : ℚ) := by
              linarith
            have hmul := congrArg (fun t => (2 * ((r + 2 : ℕ) : ℚ) ^ 2 - 1) * t) hstep
            rw [mul_div_cancel₀ _ hden] at hmul
            push_cast at hmul ⊢
            exact hmul
          exact_mod_cast haQ
  -- Step 4: Mod-4 strong induction on (bSeq a n, a n) for n ≥ 1!
  have hmod4 : ∀ n : ℕ, 1 ≤ n →
      ((bSeq a n : ℤ) : ZMod 4) = (if n % 4 = 3 then 3 else 1) ∧
      ((a n : ℤ) : ZMod 4) = (if n % 4 = 1 then 1 else 3) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      cases n with
      | zero => omega
      | succ m =>
        cases m with
        | zero => simp [bSeq, ha1]
        | succ r =>
          set N := r + 2
          have hN2 : 2 ≤ N := by omega
          -- First compute bSeq a N mod 4!
          have hbN : ((bSeq a N : ℤ) : ZMod 4) = if N % 4 = 3 then 3 else 1 := by
            rw [bSeq_eq_Ico a N hN2]
            push_cast
            rw [(ih (N - 1) (by omega) (by omega)).2]
            -- In the sum, every bSeq a k and a (N - k) is odd (≡ 1 or 3 mod 4), so 2*k * odd * odd ≡ 2*k (mod 4)!
            have hsum : (∑ k ∈ Finset.Ico 2 N,
                2 * (k : ZMod 4) * ((bSeq a k : ℤ) : ZMod 4) * ((a (N - k) : ℤ) : ZMod 4)) =
                ∑ k ∈ Finset.Ico 2 N, ((2 * k : ℕ) : ZMod 4) := by
              refine Finset.sum_congr rfl fun k hk => ?_
              rw [Finset.mem_Ico] at hk
              rw [(ih k hk.2 (by omega)).1, (ih (N - k) (by omega) (by omega)).2]
              push_cast
              have hodd_mul : ∀ x y : ZMod 4, (x = 1 ∨ x = 3) → (y = 1 ∨ y = 3) →
                  ∀ z : ZMod 4, 2 * z * x * y = 2 * z := by
                intro x y hx hy z
                rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> revert z <;> decide
              exact hodd_mul _ _ (by split_ifs <;> simp) (by split_ifs <;> simp) (k : ZMod 4)
            rw [hsum, sum_two_mul_Ico_mod4 N hN2]
            have h4 : N % 4 = 0 ∨ N % 4 = 1 ∨ N % 4 = 2 ∨ N % 4 = 3 := by omega
            rcases h4 with h | h | h | h
            · simp [show (N - 1) % 4 = 3 by omega, show (N / 2 - 1) % 2 = 1 by omega, h]; decide
            · simp [show (N - 1) % 4 = 0 by omega, show (N / 2 - 1) % 2 = 1 by omega, h]; decide
            · simp [show (N - 1) % 4 = 1 by omega, show (N / 2 - 1) % 2 = 0 by omega, h]
            · simp [show (N - 1) % 4 = 2 by omega, show (N / 2 - 1) % 2 = 0 by omega, h]
          refine ⟨hbN, ?_⟩
          rw [ha_eq N (by omega)]
          push_cast
          rw [hbN]
          have h4 : N % 4 = 0 ∨ N % 4 = 1 ∨ N % 4 = 2 ∨ N % 4 = 3 := by omega
          rcases h4 with h | h | h | h
          · have hN4 : (N : ZMod 4) = 0 := by rw [← ZMod.natCast_mod, h]; rfl
            simp [h, hN4]; decide
          · have hN4 : (N : ZMod 4) = 1 := by rw [← ZMod.natCast_mod, h]; rfl
            simp [h, hN4]; decide
          · have hN4 : (N : ZMod 4) = 2 := by rw [← ZMod.natCast_mod, h]; rfl
            simp [h, hN4]; decide
          · have hN4 : (N : ZMod 4) = 3 := by rw [← ZMod.natCast_mod, h]; rfl
            simp [h, hN4]; decide
  intro n hn
  have h4 := (hmod4 n hn).2
  have hval := congrArg ZMod.val h4
  have hmod_eq : ((a n % 4).toNat : ℕ) = ((a n : ℤ) : ZMod 4).val := by
    have h1 : ((a n : ℤ) : ZMod 4) = ((a n % 4 : ℤ) : ZMod 4) := by
      have hdiv : (4 : ℤ) ∣ a n - a n % 4 := by
        refine ⟨a n / 4, ?_⟩; linarith [Int.emod_add_mul_ediv (a n) 4]
      have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mpr hdiv
      push_cast at hz
      exact sub_eq_zero.mp hz
    rw [h1]
    have hnn : 0 ≤ a n % 4 := Int.emod_nonneg _ (by norm_num)
    have hlt : a n % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
    have hcast : ((a n % 4 : ℤ) : ZMod 4) = (((a n % 4).toNat : ℕ) : ZMod 4) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
    rw [hcast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hnn : 0 ≤ a n % 4 := Int.emod_nonneg _ (by norm_num)
  split_ifs at hval ⊢
  · have : (a n % 4).toNat = 1 := by rw [hmod_eq, hval]; decide
    omega
  · have : (a n % 4).toNat = 3 := by rw [hmod_eq, hval]; decide
    omega

end OMA.P_oeis_a397347

theorem OMA.solution : type_of% @OMA.S_oeis_a397347.main :=
  OMA.P_oeis_a397347.prove_main
