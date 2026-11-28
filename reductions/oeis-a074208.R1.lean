import OMAStatements.S_oeis_a074208

namespace OMA.R_oeis_a074208_R1

open OMA.S_oeis_a074208 (a)
open Asymptotics Filter
open scoped Classical BigOperators

private theorem a_le_witness {n m : ℕ} (hm : 1 < m)
    (hd : n ∣ (∑ d ∈ m.divisors, d) - m) : a n ≤ m := by
  unfold a
  exact Nat.sInf_le ⟨hm, hd⟩

/-- Sum the distribution up to `T` and charge the remaining terms their
pointwise upper bound. -/
private theorem sum_le_truncated_counts (s : Finset ℕ) (f : ℕ → ℕ) (T : ℕ) (M : ℝ)
    (hM : ∀ i ∈ s, (f i : ℝ) ≤ M) :
    (∑ i ∈ s, (f i : ℝ)) ≤
      (∑ t ∈ Finset.Icc 1 T, ((s.filter (fun i => t ≤ f i)).card : ℝ)) +
        M * ((s.filter (fun i => T ≤ f i)).card : ℝ) := by
  calc
    _ ≤ ∑ i ∈ s, ((∑ t ∈ Finset.Icc 1 T, if t ≤ f i then (1 : ℝ) else 0) +
        M * (if T ≤ f i then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases ht : T ≤ f i
      · rw [if_pos ht, mul_one]
        apply (hM i hi).trans
        exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => by split <;> positivity)
      · rw [if_neg ht, mul_zero, add_zero, Finset.sum_boole]
        have hfilter : (Finset.Icc 1 T).filter (fun t => t ≤ f i) = Finset.Icc 1 (f i) := by
          ext t
          simp only [Finset.mem_filter, Finset.mem_Icc]
          omega
        simp [hfilter, Nat.card_Icc]
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_comm, ← Finset.mul_sum]
      simp only [Finset.sum_boole]

private theorem harmonic_square_bound {X : ℕ} {δ : ℝ} (hX : 1 ≤ X) (hδ : 0 < δ) :
    (∑ t ∈ Finset.Icc 1 (X ^ 2), (t : ℝ)⁻¹) ≤ (1 + 2 / δ) * (X : ℝ) ^ δ := by
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hsum : (∑ t ∈ Finset.Icc 1 (X ^ 2), (t : ℝ)⁻¹) ≤ 1 + 2 * Real.log (X : ℝ) := by
    calc
      _ ≤ 1 + Real.log ((X ^ 2 : ℕ) : ℝ) := by
        simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
          using harmonic_le_one_add_log (X ^ 2)
      _ = 1 + 2 * Real.log (X : ℝ) := by
        rw [Nat.cast_pow, Real.log_pow] <;> norm_num
  calc
    _ ≤ 1 + 2 * Real.log (X : ℝ) := hsum
    _ ≤ (X : ℝ) ^ δ + 2 * ((X : ℝ) ^ δ / δ) := by
      linarith only [Real.one_le_rpow hXR hδ.le, Real.log_le_rpow_div (Nat.cast_nonneg X) hδ]
    _ = _ := by ring

/-- Pointwise witnesses at the quadratic scale, up to an arbitrarily small
exponent loss. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, 1 ≤ n →
    ∃ m : ℕ, 1 < m ∧ n ∣ (∑ d ∈ m.divisors, d) - m ∧ (m : ℝ) ≤ A * (n : ℝ) ^ (2 + ε)

/-- At thresholds up to `X²`, count the moduli not covered by the proper-divisor
sums of smaller integers. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ X t : ℕ, 1 ≤ X → 1 ≤ t → t ≤ X ^ 2 →
    (t : ℝ) * (((Finset.Icc 1 X).filter (fun n =>
      ∀ m ∈ Finset.Ico 2 t, ¬ (n ∣ (∑ d ∈ m.divisors, d) - m))).card : ℝ) ≤
      C * (X : ℝ) ^ (2 + ε)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a074208.main := by
  intro hPoint hCoverage ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨A, hA, hWitness⟩ := hPoint δ hδ
  obtain ⟨C, hC, hCovered⟩ := hCoverage δ hδ
  refine Asymptotics.IsBigO.of_bound (C * (1 + 2 / δ) + A * C) ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hXp : 0 < (X : ℝ) := zero_lt_one.trans_le hXR
  let T := X ^ 2
  let s := Finset.Icc 1 X
  let M : ℝ := A * (X : ℝ) ^ (2 + δ)
  let D : ℝ := C * (X : ℝ) ^ (2 + δ)
  have hM : 0 ≤ M := mul_nonneg hA (Real.rpow_nonneg hXp.le _)
  have hD : 0 ≤ D := mul_nonneg hC (Real.rpow_nonneg hXp.le _)
  have hBound (n : ℕ) (hn : n ∈ s) : (a n : ℝ) ≤ M := by
    obtain ⟨hn₁, hn₂⟩ := Finset.mem_Icc.mp hn
    obtain ⟨m, hm, hd, hSize⟩ := hWitness n hn₁
    have hle : (a n : ℝ) ≤ (m : ℝ) := by exact_mod_cast a_le_witness hm hd
    have hnX : (n : ℝ) ≤ (X : ℝ) := by exact_mod_cast hn₂
    exact hle.trans (hSize.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg n) hnX (by linarith)) hA))
  have hCount (t : ℕ) (ht₁ : 1 ≤ t) (ht₂ : t ≤ T) :
      ((s.filter (fun n => t ≤ a n)).card : ℝ) ≤ D * (t : ℝ)⁻¹ := by
    have hSub : s.filter (fun n => t ≤ a n) ⊆ s.filter (fun n =>
        ∀ m ∈ Finset.Ico 2 t, ¬ (n ∣ (∑ d ∈ m.divisors, d) - m)) := by
      intro n hn
      obtain ⟨hns, hna⟩ := Finset.mem_filter.mp hn
      refine Finset.mem_filter.mpr ⟨hns, ?_⟩
      intro m hm hd
      obtain ⟨hm₁, hm₂⟩ := Finset.mem_Ico.mp hm
      exact (not_lt_of_ge hna) ((a_le_witness (by omega) hd).trans_lt hm₂)
    have hCard : ((s.filter (fun n => t ≤ a n)).card : ℝ) ≤
        ((s.filter (fun n => ∀ m ∈ Finset.Ico 2 t,
          ¬ (n ∣ (∑ d ∈ m.divisors, d) - m))).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hSub
    have ht : 0 < (t : ℝ) := by exact_mod_cast (show 0 < t by omega)
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ ht).mpr
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_left hCard ht.le).trans (hCovered X t hX ht₁ ht₂)
  have hT : 1 ≤ T := by
    have hXpNat : 0 < X := by omega
    have hTpos : 0 < T := pow_pos hXpNat _
    omega
  have hTC : (T : ℝ) = (X : ℝ) ^ 2 := by simp [T]
  have hTail : ((s.filter (fun n => T ≤ a n)).card : ℝ) ≤ C * (X : ℝ) ^ δ := by
    refine (hCount T hT le_rfl).trans_eq ?_
    calc
      D * (T : ℝ)⁻¹ = C * (X : ℝ) ^ δ * ((X : ℝ) ^ 2 * ((X : ℝ) ^ 2)⁻¹) := by
        dsimp only [D]
        rw [hTC, Real.rpow_add hXp, Real.rpow_two]
        ring
      _ = _ := by rw [mul_inv_cancel₀ (pow_ne_zero _ hXp.ne'), mul_one]
  have hSmall : (∑ t ∈ Finset.Icc 1 T, ((s.filter (fun n => t ≤ a n)).card : ℝ)) ≤
      D * ((1 + 2 / δ) * (X : ℝ) ^ δ) := by
    calc
      _ ≤ ∑ t ∈ Finset.Icc 1 T, D * (t : ℝ)⁻¹ := by
        exact Finset.sum_le_sum fun t ht => hCount t (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp ht).2
      _ = D * ∑ t ∈ Finset.Icc 1 T, (t : ℝ)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_square_bound hX hδ) hD
  change ‖∑ n ∈ s, (a n : ℝ)‖ ≤ (C * (1 + 2 / δ) + A * C) * ‖(X : ℝ) ^ (2 + ε)‖
  have hSumNonneg : 0 ≤ ∑ n ∈ s, (a n : ℝ) := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  rw [Real.norm_of_nonneg hSumNonneg, Real.norm_of_nonneg (Real.rpow_nonneg hXp.le _)]
  calc
    (∑ n ∈ s, (a n : ℝ)) ≤
        (∑ t ∈ Finset.Icc 1 T, ((s.filter (fun n => t ≤ a n)).card : ℝ)) +
          M * ((s.filter (fun n => T ≤ a n)).card : ℝ) :=
      sum_le_truncated_counts s a T M hBound
    _ ≤ D * ((1 + 2 / δ) * (X : ℝ) ^ δ) + M * (C * (X : ℝ) ^ δ) :=
      add_le_add hSmall (mul_le_mul_of_nonneg_left hTail hM)
    _ = _ := by
      have hExp : 2 + ε = (2 + δ) + δ := by dsimp [δ]; ring
      dsimp only [D, M]
      rw [hExp, Real.rpow_add hXp (2 + δ) δ]
      ring

end OMA.R_oeis_a074208_R1
