import OMAStatements.S_oeis_a301933
import Mathlib

open PowerSeries

namespace OMA.S_oeis_a301933.Proof

/-! ### Parity part -/

lemma two_eq_zero : (2 : ZMod 2) = 0 := rfl

lemma natCast_add_one (m : ℕ) : ((m : ZMod 2) + 1) = if m % 2 = 0 then 1 else 0 := by
  conv_lhs => rw [← Nat.div_add_mod m 2]
  push_cast
  rw [two_eq_zero, zero_mul, zero_add]
  rcases Nat.mod_two_eq_zero_or_one m with h | h <;> rw [h] <;> rfl

/-- Over `ZMod 2`, the `n`-th coefficient of `A²` is `a_{n/2}` for even `n` and `0` otherwise. -/
lemma sq_coeff_mod2 (A : PowerSeries ℤ) (n : ℕ) :
    ((coeff n (A ^ 2) : ℤ) : ZMod 2) =
      if n % 2 = 0 then ((coeff (n / 2) A : ℤ) : ZMod 2) else 0 := by
  rw [pow_two, coeff_mul, Int.cast_sum]
  set f : ℕ × ℕ → ZMod 2 := fun p => ((coeff p.1 A * coeff p.2 A : ℤ) : ZMod 2) with hf
  have hswap : ∀ p : ℕ × ℕ, f p + f p.swap = 0 := by
    intro p
    simp only [hf, Prod.fst_swap, Prod.snd_swap, Int.cast_mul]
    rw [mul_comm ((coeff p.2 A : ℤ) : ZMod 2), ← two_mul, two_eq_zero, zero_mul]
  split_ifs with hn
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := ⟨n / 2, by omega⟩
    have hmem : (m, m) ∈ Finset.HasAntidiagonal.antidiagonal (2 * m) := by
      rw [Finset.HasAntidiagonal.mem_antidiagonal]; ring
    rw [← Finset.add_sum_erase _ _ hmem]
    have hrest : ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (2 * m)).erase (m, m), f x = 0 := by
      refine Finset.sum_involution (fun p _ => p.swap) (fun p _ => hswap p) ?_ ?_ ?_
      · intro p hp _ heq
        rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hp
        apply hp.1
        have h1 : p.2 = p.1 := congrArg Prod.fst heq
        ext <;> simp <;> omega
      · intro p hp
        rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
        refine ⟨?_, ?_⟩
        · intro h
          apply hp.1
          rw [← Prod.swap_swap p, h]; rfl
        · simp only [Prod.fst_swap, Prod.snd_swap]; omega
      · intro p _
        exact Prod.swap_swap p
    show f (m, m) + _ = _
    rw [hrest, add_zero]
    have h2 : 2 * m / 2 = m := by omega
    rw [h2]
    simp only [hf, Int.cast_mul]
    generalize ((coeff m A : ℤ) : ZMod 2) = x
    fin_cases x <;> rfl
  · refine Finset.sum_involution (fun p _ => p.swap) (fun p _ => hswap p) ?_ ?_ ?_
    · intro p hp _ heq
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      have h1 : p.2 = p.1 := congrArg Prod.fst heq
      omega
    · intro p hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
      simp only [Prod.fst_swap, Prod.snd_swap]; omega
    · intro p _
      exact Prod.swap_swap p

lemma deriv_coeff_mod2 (A : PowerSeries ℤ) (n : ℕ) :
    ((coeff n (d⁄dX ℤ A) : ℤ) : ZMod 2) =
      ((coeff (n + 1) A : ℤ) : ZMod 2) * (if n % 2 = 0 then 1 else 0) := by
  rw [coeff_derivative, Int.cast_mul, ← natCast_add_one]
  push_cast
  rfl

lemma pow2_double (m : ℕ) : (∃ k : ℕ, 2 * m = 2 ^ k) ↔ ∃ k : ℕ, m = 2 ^ k := by
  constructor
  · rintro ⟨k, hk⟩
    rcases k with _ | k
    · omega
    · exact ⟨k, by rw [pow_succ] at hk; omega⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k + 1, by rw [pow_succ]; ring⟩

lemma not_pow2_odd (n : ℕ) (h1 : 1 < n) (h2 : n % 2 = 1) : ¬ ∃ k : ℕ, n = 2 ^ k := by
  rintro ⟨k, rfl⟩
  rcases k with _ | k
  · simp at h1
  · rw [pow_succ] at h2; omega

lemma eq_of_add_eq_zero_mod2 {x y : ZMod 2} (h : x + y = 0) : x = y := by
  revert h; revert x y; decide

theorem parity (A : PowerSeries ℤ) (hA : Defines A) :
    ∀ n : ℕ, 0 < n →
      (Odd (coeff n A) ↔ ∃ k : ℕ, n = 2^k) ∧
      (Odd (coeff n (A * d⁄dX ℤ A)) ↔ ∃ k : ℕ, n = 2^k) := by
  obtain ⟨_, h1, hE⟩ := hA
  set b : ℕ → ZMod 2 := fun n => ((coeff n A : ℤ) : ZMod 2) with hb
  have hb1 : b 1 = 1 := by simp [hb, h1]
  have hE' : A + A ^ 2 * d⁄dX ℤ A = X + C (4 : ℤ) * (X * (A * d⁄dX ℤ A)) := by
    rw [map_ofNat]; linear_combination hE
  -- the coefficient equation mod 2
  have hcoef : ∀ n : ℕ, b n + ((coeff n (A ^ 2 * d⁄dX ℤ A) : ℤ) : ZMod 2) =
      if n = 1 then 1 else 0 := by
    intro n
    have := congrArg (fun F => ((coeff n F : ℤ) : ZMod 2)) hE'
    simp only [map_add, coeff_C_mul, Int.cast_add, Int.cast_mul, coeff_X] at this
    rw [this]
    have h4 : ((4 : ℤ) : ZMod 2) = 0 := rfl
    rw [h4, zero_mul, add_zero]
    split_ifs <;> simp
  -- product coefficients mod 2
  have hprod : ∀ n : ℕ, ((coeff n (A ^ 2 * d⁄dX ℤ A) : ℤ) : ZMod 2) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        (if p.1 % 2 = 0 then b (p.1 / 2) else 0) * (b (p.2 + 1) * (if p.2 % 2 = 0 then 1 else 0)) := by
    intro n
    rw [coeff_mul, Int.cast_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Int.cast_mul, sq_coeff_mod2, deriv_coeff_mod2]
  have hc_odd : ∀ n : ℕ, n % 2 = 1 → ((coeff n (A ^ 2 * d⁄dX ℤ A) : ℤ) : ZMod 2) = 0 := by
    intro n hn
    rw [hprod]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    by_cases h : p.1 % 2 = 0
    · rw [if_neg (show ¬ p.2 % 2 = 0 by omega)]; simp
    · rw [if_neg h]; simp
  have hb_odd : ∀ n : ℕ, n % 2 = 1 → b n = if n = 1 then 1 else 0 := by
    intro n hn
    have := hcoef n
    rwa [hc_odd n hn, add_zero] at this
  have hb_even : ∀ m : ℕ, 1 ≤ m → b (2 * m) = b m := by
    intro m _
    have h := hcoef (2 * m)
    rw [if_neg (by omega), hprod] at h
    rw [Finset.sum_eq_single (2 * m, 0)] at h
    · simp only [show 2 * m % 2 = 0 by omega, show 2 * m / 2 = m by omega, if_true, zero_add,
        Nat.zero_mod, hb1, mul_one] at h
      exact eq_of_add_eq_zero_mod2 h
    · intro p hp hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      by_cases h2 : p.2 % 2 = 0
      · have hp2 : p.2 ≠ 0 := by
          intro h0; apply hne; ext <;> simp <;> omega
        rw [hb_odd (p.2 + 1) (by omega), if_neg (show ¬ (p.2 + 1 = 1) by omega)]; simp
      · rw [if_neg h2]; simp
    · intro h; exfalso; apply h
      rw [Finset.HasAntidiagonal.mem_antidiagonal]; ring
  have hmain : ∀ n : ℕ, 0 < n → (b n = 1 ↔ ∃ k : ℕ, n = 2 ^ k) := by
    intro n hn
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases Nat.even_or_odd' n with ⟨m, hm | hm⟩
      · subst hm
        rw [hb_even m (by omega), pow2_double]
        exact ih m (by omega) (by omega)
      · rw [hb_odd n (by omega)]
        by_cases h1n : n = 1
        · subst h1n
          refine ⟨fun _ => ⟨0, rfl⟩, fun _ => ?_⟩
          simp
        · rw [if_neg h1n]
          constructor
          · intro h0; exact absurd h0 (by decide)
          · intro h0; exact absurd h0 (not_pow2_odd n (by omega) (by omega))
  -- `A · A'` agrees with `A` mod 2
  have hAA : ∀ n : ℕ, ((coeff n (A * d⁄dX ℤ A) : ℤ) : ZMod 2) = b n := by
    intro n
    rw [coeff_mul, Int.cast_sum, Finset.sum_eq_single (n, 0)]
    · rw [Int.cast_mul, deriv_coeff_mod2]
      simp only [Nat.zero_mod, if_true, zero_add, mul_one]
      rw [show ((coeff 1 A : ℤ) : ZMod 2) = b 1 from rfl, hb1, mul_one]
    · intro p hp hne
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rw [Int.cast_mul, deriv_coeff_mod2]
      by_cases h2 : p.2 % 2 = 0
      · have hp2 : p.2 ≠ 0 := by
          intro h0; apply hne; ext <;> simp <;> omega
        rw [show ((coeff (p.2 + 1) A : ℤ) : ZMod 2) = b (p.2 + 1) from rfl,
          hb_odd (p.2 + 1) (by omega), if_neg (show ¬ (p.2 + 1 = 1) by omega)]; simp
      · rw [if_neg h2]; simp
    · intro h; exfalso; apply h
      rw [Finset.HasAntidiagonal.mem_antidiagonal]; ring
  intro n hn
  constructor
  · rw [← ZMod.intCast_eq_one_iff_odd]
    exact hmain n hn
  · rw [← ZMod.intCast_eq_one_iff_odd, hAA]
    exact hmain n hn

/-! ### Existence part -/

/-- The fixed-point map: `A = F A` is the differential equation. -/
noncomputable def F (B : PowerSeries ℤ) : PowerSeries ℤ :=
  X + C (4 : ℤ) * (X * (B * d⁄dX ℤ B)) - B ^ 2 * d⁄dX ℤ B

lemma F_const (B : PowerSeries ℤ) (hB : constantCoeff B = 0) : constantCoeff (F B) = 0 := by
  simp [F, hB]

lemma deriv_dvd (E : PowerSeries ℤ) (m : ℕ) (h : X ^ (m + 1) ∣ E) : X ^ m ∣ d⁄dX ℤ E := by
  rw [X_pow_dvd_iff] at h ⊢
  intro k hk
  rw [coeff_derivative, h (k + 1) (by omega), zero_mul]

lemma contract (B1 B2 : PowerSeries ℤ) (h1 : constantCoeff B1 = 0) (h2 : constantCoeff B2 = 0)
    (n : ℕ) (h : X ^ n ∣ B1 - B2) : X ^ (n + 1) ∣ F B1 - F B2 := by
  rcases n with _ | m
  · rw [zero_add, pow_one]
    apply dvd_sub <;> rw [X_dvd_iff] <;> exact F_const _ ‹_›
  · have hX1 : X ∣ B1 := X_dvd_iff.mpr h1
    have hX2 : X ∣ B2 := X_dvd_iff.mpr h2
    have hE' : X ^ m ∣ d⁄dX ℤ B1 - d⁄dX ℤ B2 := by
      rw [← map_sub]; exact deriv_dvd _ m h
    have key : F B1 - F B2 =
        C (4 : ℤ) * X * ((B1 - B2) * d⁄dX ℤ B1 + B2 * (d⁄dX ℤ B1 - d⁄dX ℤ B2)) -
          ((B1 - B2) * (B1 + B2) * d⁄dX ℤ B1 + B2 ^ 2 * (d⁄dX ℤ B1 - d⁄dX ℤ B2)) := by
      simp only [F]; ring
    rw [key]
    apply dvd_sub
    · rw [show X ^ (m + 1 + 1) = X * X ^ (m + 1) by ring]
      rw [mul_assoc]
      apply Dvd.dvd.mul_left
      apply mul_dvd_mul (dvd_refl X)
      apply dvd_add
      · exact Dvd.dvd.mul_right h _
      · rw [show X ^ (m + 1) = X * X ^ m by ring]
        exact mul_dvd_mul hX2 hE'
    · apply dvd_add
      · rw [show X ^ (m + 1 + 1) = X ^ (m + 1) * X by ring]
        exact Dvd.dvd.mul_right (mul_dvd_mul h (dvd_add hX1 hX2)) _
      · rw [show X ^ (m + 1 + 1) = X ^ 2 * X ^ m by ring]
        exact mul_dvd_mul (pow_dvd_pow_of_dvd hX2 2) hE'

noncomputable def seq (k : ℕ) : PowerSeries ℤ := F^[k] 0

lemma seq_const (k : ℕ) : constantCoeff (seq k) = 0 := by
  induction k with
  | zero => simp [seq]
  | succ k ih =>
    rw [seq, Function.iterate_succ_apply']
    exact F_const _ ih

lemma seq_succ (k : ℕ) : seq (k + 1) = F (seq k) := by
  rw [seq, Function.iterate_succ_apply']; rfl

lemma seq_step (k : ℕ) : X ^ k ∣ seq (k + 1) - seq k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := contract (seq (k + 1)) (seq k) (seq_const _) (seq_const _) k ih
    rw [← seq_succ (k + 1), ← seq_succ k] at h
    exact h

lemma seq_stab (k j : ℕ) : X ^ k ∣ seq (k + j) - seq k := by
  induction j with
  | zero => simp
  | succ j ih =>
    have : seq (k + (j + 1)) - seq k = (seq (k + j + 1) - seq (k + j)) + (seq (k + j) - seq k) := by
      rw [← add_assoc]; ring
    rw [this]
    exact dvd_add (dvd_trans (pow_dvd_pow X (by omega)) (seq_step (k + j))) ih

noncomputable def lim : PowerSeries ℤ := PowerSeries.mk fun n => coeff n (seq (n + 1))

lemma lim_close (k : ℕ) : X ^ k ∣ lim - seq k := by
  rw [X_pow_dvd_iff]
  intro m hm
  rw [map_sub, lim, coeff_mk]
  have := seq_stab (m + 1) (k - (m + 1))
  rw [show m + 1 + (k - (m + 1)) = k by omega, X_pow_dvd_iff] at this
  have h := this m (by omega)
  rw [map_sub] at h
  rw [sub_eq_zero] at h ⊢
  exact h.symm

lemma eq_zero_of_dvd_all (P : PowerSeries ℤ) (h : ∀ k, X ^ k ∣ P) : P = 0 := by
  ext m
  have := h (m + 1)
  rw [X_pow_dvd_iff] at this
  simpa using this m (by omega)

lemma lim_const : constantCoeff lim = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, lim, coeff_mk, coeff_zero_eq_constantCoeff_apply,
    seq_const]

lemma lim_fix : lim = F lim := by
  symm
  rw [← sub_eq_zero]
  apply eq_zero_of_dvd_all
  intro k
  rcases k with _ | k
  · simp
  · have e : F lim - lim = (F lim - F (seq k)) + (seq (k + 1) - lim) := by
      rw [seq_succ]; ring
    rw [e]
    apply dvd_add
    · exact contract _ _ lim_const (seq_const k) k (lim_close k)
    · rw [← neg_sub]; exact (dvd_neg).mpr (lim_close (k + 1))

theorem exists_defines : ∃ A, Defines A := by
  refine ⟨lim, lim_const, ?_, ?_⟩
  · obtain ⟨G, hG⟩ := X_dvd_iff.mpr lim_const
    have hfix := lim_fix
    rw [F] at hfix
    generalize d⁄dX ℤ lim = dA at hfix
    have := congrArg (coeff 1) hfix
    rw [hG] at this
    rw [hG, this]
    have e1 : (C (4 : ℤ) * (X * (X * G * dA)) : PowerSeries ℤ) = C 4 * (X * (X * (G * dA))) := by
      ring
    have e2 : ((X * G) ^ 2 * dA : PowerSeries ℤ) = X * (X * (G ^ 2 * dA)) := by ring
    rw [e1, e2, map_sub, map_add, coeff_C_mul, coeff_succ_X_mul, coeff_succ_X_mul, coeff_X,
      coeff_zero_X_mul, coeff_zero_X_mul]
    simp
  · have hfix := lim_fix
    rw [F, map_ofNat] at hfix
    linear_combination hfix

end OMA.S_oeis_a301933.Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a301933.main :=
  ⟨OMA.S_oeis_a301933.Proof.exists_defines, OMA.S_oeis_a301933.Proof.parity⟩
