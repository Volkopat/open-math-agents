import FormalConjectures.ErdosProblems.«673»

open Erdos673

theorem OMA.solution : type_of% @Erdos673.erdos_673.variants.tao := by
  intro n m hn hm hmn
  let d := Nat.nth (· ∣ n)
  let rank := Nat.count (· ∣ n)
  have hset : Set.ofPred (· ∣ n) = (n.divisors : Set ℕ) := by
    ext a
    simp [Nat.mem_divisors, hn.ne']
  have hfinite : (Set.ofPred (· ∣ n)).Finite := hset ▸ n.divisors.finite_toSet
  have hcard : hfinite.toFinset = n.divisors := by
    ext a
    simp [hset]
  have ordered {i j} (hij : i ≤ j) (hj : j < n.divisors.card) : d i ≤ d j :=
    Nat.nth_le_nth_of_lt_card hfinite hij (by rwa [hcard])
  have atRank {a} (ha : a ∣ n) : d (rank a) = a := Nat.nth_count ha
  have rankBound {a} (ha : a ∣ n) : rank a < n.divisors.card := by
    simpa only [hcard] using Nat.count_lt_card hfinite ha
  let ratio (i : ℕ) : ℝ := (d i : ℝ) / d (i + 1)
  have sumRatios : G n = ∑ i ∈ Finset.range (n.divisors.card - 1), ratio i :=
    Fin.sum_univ_eq_sum_range ratio (n.divisors.card - 1)
  constructor
  · have divisor {a} (ha : a ∈ (n / m).divisors) : a ∣ n :=
      (Nat.mem_divisors.mp ha).1.trans (Nat.div_dvd_of_dvd hmn)
    have scaledDivisor {a} (ha : a ∈ (n / m).divisors) : m * a ∣ n :=
      Nat.mul_div_cancel' hmn ▸ Nat.mul_dvd_mul_left m (Nat.mem_divisors.mp ha).1
    -- The scaled divisor lies at or after the successor of the original divisor.
    have next {a} (ha : a ∈ (n / m).divisors) :
        rank a + 1 ≤ rank (m * a) ∧ rank (m * a) < n.divisors.card := by
      have hlt : a < m * a := by
        simpa only [one_mul] using Nat.mul_lt_mul_of_pos_right hm (Nat.pos_of_dvd_of_pos (divisor ha) hn)
      exact ⟨Nat.count_strict_mono (divisor ha) hlt, rankBound (scaledDivisor ha)⟩
    have rankInj : Set.InjOn rank ((n / m).divisors : Set ℕ) := by
      intro a ha b hb hab
      rw [← atRank (divisor ha), ← atRank (divisor hb), hab]
    rw [sumRatios]
    calc
      _ = ∑ _a ∈ (n / m).divisors, (1 : ℝ) / m := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
      _ ≤ ∑ a ∈ (n / m).divisors, ratio (rank a) := by
        apply Finset.sum_le_sum
        intro a ha
        obtain ⟨hstep, hbound⟩ := next ha
        have hle := ordered hstep hbound
        rw [atRank (scaledDivisor ha)] at hle
        have hdvd : d (rank a + 1) ∣ n :=
          Nat.nth_mem_of_lt_card hfinite (by rw [hcard]; omega)
        have hpos : (0 : ℝ) < d (rank a + 1) := by
          exact_mod_cast Nat.pos_of_dvd_of_pos hdvd hn
        have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
        change (1 : ℝ) / m ≤ (d (rank a) : ℝ) / d (rank a + 1)
        rw [atRank (divisor ha)]
        apply (div_le_div_iff₀ hmpos hpos).2
        simpa [mul_comm] using (show (d (rank a + 1) : ℝ) ≤ (m : ℝ) * a by exact_mod_cast hle)
      _ = ∑ i ∈ (n / m).divisors.image rank, ratio i := (Finset.sum_image rankInj).symm
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun i _ _ => by dsimp [ratio]; positivity)
        intro i hi
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
        have := next ha
        exact Finset.mem_range.mpr (by omega)
  · rw [sumRatios]
    calc
      _ ≤ ∑ _i ∈ Finset.range (n.divisors.card - 1), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hnext : i + 1 < n.divisors.card := by have := Finset.mem_range.mp hi; omega
        exact div_le_one_of_le₀ (by exact_mod_cast ordered (Nat.le_succ i) hnext) (by positivity)
      _ ≤ _ := by simp
