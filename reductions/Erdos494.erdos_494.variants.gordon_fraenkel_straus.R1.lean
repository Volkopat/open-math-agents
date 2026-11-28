import FormalConjectures.ErdosProblems.«494»

-- Reduction Erdos494.erdos_494.variants.gordon_fraenkel_straus.R1 of Erdős Problem 494 — gordon fraenkel straus
-- Credit: @jared-jasinski
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos494_erdos_494_variants_gordon_fraenkel_straus_R1

open Filter Finset

-- Selfridge-Straus (1958) / Gordon-Fraenkel-Straus (1962, Sec. 3) necessary condition:
-- if Erdos494Unique s n fails for n > s > 2, then the Diophantine equation
-- sum_{i=1}^s (-1)^(i-1) * C(n, s-i) * i^(r-1) = 0 has a solution r >= 1.
def H1 : Prop :=
  ∀ s n : ℕ, 2 < s → s < n → ¬ Erdos494.Erdos494Unique s n →
    ∃ r : ℕ, 1 ≤ r ∧
      (∑ i ∈ Finset.Icc 1 s, (-1 : ℤ) ^ (i - 1) * (Nat.choose n (s - i) : ℤ) * (i : ℤ) ^ (r - 1)) = 0

-- Ridout (1957) theorem for S-smooth positive integers:
-- for any s >= 1 and epsilon > 0, there are only finitely many pairs (p, q) of positive integers
-- whose prime factors are all <= s such that 0 < |q - p| < q^(1 - epsilon).
def H2 : Prop :=
  ∀ (s : ℕ) (ε : ℝ), 0 < ε →
    Set.Finite {pq : ℕ × ℕ | 0 < pq.1 ∧ 0 < pq.2 ∧
      (∀ p : ℕ, p.Prime → p ∣ pq.1 → p ≤ s) ∧
      (∀ p : ℕ, p.Prime → p ∣ pq.2 → p ≤ s) ∧
      pq.1 ≠ pq.2 ∧
      |(pq.2 : ℝ) - (pq.1 : ℝ)| < (pq.2 : ℝ) ^ (1 - ε)}

lemma succ_mul_choose_eq_aux : ∀ n k : ℕ, (n + 1) * Nat.choose n k = Nat.choose (n + 1) (k + 1) * (k + 1)
  | 0, 0 => by simp
  | 0, k + 1 => by simp [Nat.choose_eq_zero_of_lt]
  | n + 1, 0 => by simp
  | n + 1, k + 1 => by
    have ih1 := succ_mul_choose_eq_aux n k
    have ih2 := succ_mul_choose_eq_aux n (k + 1)
    have hp1 : Nat.choose (n + 1) (k + 1) = Nat.choose n k + Nat.choose n (k + 1) := Nat.choose_succ_succ n k
    calc (n + 1 + 1) * Nat.choose (n + 1) (k + 1)
        = (n + 1) * (Nat.choose n k + Nat.choose n (k + 1)) + Nat.choose (n + 1) (k + 1) := by rw [hp1]; ring
      _ = (n + 1) * Nat.choose n k + (n + 1) * Nat.choose n (k + 1) + Nat.choose (n + 1) (k + 1) := by ring
      _ = Nat.choose (n + 1) (k + 1) * (k + 1) + Nat.choose (n + 1) (k + 1 + 1) * (k + 1 + 1) +
            Nat.choose (n + 1) (k + 1) := by rw [ih1, ih2]
      _ = (Nat.choose (n + 1) (k + 1) + Nat.choose (n + 1) (k + 1 + 1)) * (k + 1 + 1) := by ring
      _ = Nat.choose (n + 1 + 1) (k + 1 + 1) * (k + 1 + 1) := by rw [Nat.choose_succ_succ (n + 1) (k + 1)]

lemma dvd_fac_mul_choose (s n i : ℕ) (hi1 : 1 ≤ i) (his : i < s) :
    n ∣ Nat.factorial (s - 1) * Nat.choose n (s - i) := by
  have hm : 1 ≤ s - i := by omega
  have hms : s - i ≤ s - 1 := by omega
  have hdvd : s - i ∣ Nat.factorial (s - 1) := Nat.dvd_factorial hm hms
  obtain ⟨c, hc⟩ := hdvd
  have hch : Nat.choose n (s - i) * (s - i) = n * Nat.choose (n - 1) (s - i - 1) := by
    have h2 : s - i - 1 + 1 = s - i := by omega
    by_cases hn : n = 0
    · subst hn; simp [Nat.choose_eq_zero_of_lt (by omega : 0 < s - i)]
    · have h3 := succ_mul_choose_eq_aux (n - 1) (s - i - 1)
      have h4 : n - 1 + 1 = n := by omega
      rw [h4, h2] at h3
      linarith
  refine ⟨c * Nat.choose (n - 1) (s - i - 1), ?_⟩
  calc Nat.factorial (s - 1) * Nat.choose n (s - i)
      = (s - i) * c * Nat.choose n (s - i) := by rw [hc]
    _ = c * (Nat.choose n (s - i) * (s - i)) := by ring
    _ = c * (n * Nat.choose (n - 1) (s - i - 1)) := by rw [hch]
    _ = n * (c * Nat.choose (n - 1) (s - i - 1)) := by ring

lemma smooth_and_bound_of_eq (s n r : ℕ) (hs : 2 < s) (hn : s < n) (hr : 1 ≤ r)
    (heq : (∑ i ∈ Finset.Icc 1 s, (-1 : ℤ) ^ (i - 1) * (Nat.choose n (s - i) : ℤ) * (i : ℤ) ^ (r - 1)) = 0) :
    n ∣ Nat.factorial (s - 1) * s ^ (r - 1) := by
  have hsplit : Finset.Icc 1 s = insert s (Finset.Icc 1 (s - 1)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hsnot : s ∉ Finset.Icc 1 (s - 1) := by simp; omega
  rw [hsplit, Finset.sum_insert hsnot] at heq
  have hfac_eq :
      ((Nat.factorial (s - 1) : ℤ) * ((-1 : ℤ) ^ (s - 1) * (Nat.choose n (s - s) : ℤ) * (s : ℤ) ^ (r - 1))) =
      - ((Nat.factorial (s - 1) : ℤ) *
        ∑ i ∈ Finset.Icc 1 (s - 1), (-1 : ℤ) ^ (i - 1) * (Nat.choose n (s - i) : ℤ) * (i : ℤ) ^ (r - 1)) := by
    linear_combination (Nat.factorial (s - 1) : ℤ) * heq
  have hchoose0 : Nat.choose n (s - s) = 1 := by simp
  rw [hchoose0] at hfac_eq
  push_cast at hfac_eq
  have hdvd_sum : (n : ℤ) ∣
      (Nat.factorial (s - 1) : ℤ) *
      ∑ i ∈ Finset.Icc 1 (s - 1), (-1 : ℤ) ^ (i - 1) * (Nat.choose n (s - i) : ℤ) * (i : ℤ) ^ (r - 1) := by
    rw [Finset.mul_sum]
    apply Finset.dvd_sum
    intro i hi
    simp only [Finset.mem_Icc] at hi
    have hnat := dvd_fac_mul_choose s n i hi.1 (by omega)
    have hint : (n : ℤ) ∣ (Nat.factorial (s - 1) : ℤ) * (Nat.choose n (s - i) : ℤ) := by
      exact_mod_cast hnat
    calc (n : ℤ) ∣ (Nat.factorial (s - 1) : ℤ) * (Nat.choose n (s - i) : ℤ) := hint
      _ ∣ (Nat.factorial (s - 1) : ℤ) * (Nat.choose n (s - i) : ℤ) * ((-1 : ℤ) ^ (i - 1) * (i : ℤ) ^ (r - 1)) :=
          dvd_mul_right _ _
      _ = (Nat.factorial (s - 1) : ℤ) * ((-1 : ℤ) ^ (i - 1) * (Nat.choose n (s - i) : ℤ) * (i : ℤ) ^ (r - 1)) := by
          ring
  have hdvd_lhs : (n : ℤ) ∣ (-1 : ℤ) ^ (s - 1) * ((Nat.factorial (s - 1) * s ^ (r - 1) : ℕ) : ℤ) := by
    have h1 : (-1 : ℤ) ^ (s - 1) * ((Nat.factorial (s - 1) * s ^ (r - 1) : ℕ) : ℤ) =
        (Nat.factorial (s - 1) : ℤ) * ((-1 : ℤ) ^ (s - 1) * (1 : ℤ) * (s : ℤ) ^ (r - 1)) := by
      push_cast; ring
    rw [h1, hfac_eq]
    exact dvd_neg.mpr hdvd_sum
  have hdvd_int : (n : ℤ) ∣ ((Nat.factorial (s - 1) * s ^ (r - 1) : ℕ) : ℤ) := by
    have hunit : IsUnit ((-1 : ℤ) ^ (s - 1)) := IsUnit.pow _ isUnit_one.neg
    exact (hunit.dvd_mul_left).mp hdvd_lhs
  exact_mod_cast hdvd_int

lemma prime_le_of_dvd_fac_mul_pow (s n r p : ℕ) (hspos : 0 < s) (hp : p.Prime)
    (hdvd : n ∣ Nat.factorial (s - 1) * s ^ (r - 1)) (hpn : p ∣ n) : p ≤ s := by
  have h1 : p ∣ Nat.factorial (s - 1) * s ^ (r - 1) := dvd_trans hpn hdvd
  rcases hp.dvd_mul.mp h1 with hfac | hpow
  · exact le_trans (hp.dvd_factorial.mp hfac) (Nat.sub_le s 1)
  · exact Nat.le_of_dvd hspos (hp.dvd_of_dvd_pow hpow)

lemma term_pos (s n r i : ℕ) (hn : s < n) (hi1 : 1 ≤ i) (his : i ≤ s) :
    0 < ((Nat.choose n (s - i) : ℝ) * (i : ℝ) ^ (r - 1)) := by
  have hch : 0 < Nat.choose n (s - i) := Nat.choose_pos (by omega)
  have hi : (0 : ℝ) < (i : ℝ) := by exact_mod_cast (by omega : 0 < i)
  positivity

lemma term_ratio_eq (s n r i : ℕ) (hn : s < n) (hi1 : 1 ≤ i) (his : i < s) :
    ((Nat.choose n (s - (i + 1)) : ℝ) * ((i + 1 : ℕ) : ℝ) ^ (r - 1)) /
      ((Nat.choose n (s - i) : ℝ) * (i : ℝ) ^ (r - 1)) =
    ((s - i : ℕ) : ℝ) / ((n - s + i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) / (i : ℝ)) ^ (r - 1) := by
  have hch : Nat.choose n (s - i) * (s - i) = Nat.choose n (s - (i + 1)) * (n - s + i + 1) := by
    have h1 := Nat.choose_succ_right_eq n (s - (i + 1))
    have h2 : s - (i + 1) + 1 = s - i := by omega
    have h3 : n - (s - (i + 1)) = n - s + i + 1 := by omega
    rw [h2, h3] at h1
    linarith
  have hchR : (Nat.choose n (s - i) : ℝ) * ((s - i : ℕ) : ℝ) =
      (Nat.choose n (s - (i + 1)) : ℝ) * ((n - s + i + 1 : ℕ) : ℝ) := by
    exact_mod_cast hch
  have h1 : (0 : ℝ) < (Nat.choose n (s - i) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : s - i ≤ n)
  have h2 : (0 : ℝ) < ((n - s + i + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - s + i + 1)
  have h3 : (0 : ℝ) < (i : ℝ) := by exact_mod_cast (by omega : 0 < i)
  rw [div_pow]
  field_simp
  nlinarith

lemma ratio_step_bound (s n r a b : ℕ) (hs : 2 < s) (hn : s < n) (hr : 1 ≤ r)
    (ha1 : 1 ≤ a) (hab : a < b) (hbs : b < s) :
    (1 + 1 / (s : ℝ) ^ 2) ^ (r - 1) *
      (((s - b : ℕ) : ℝ) / ((n - s + b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ) / (b : ℝ)) ^ (r - 1)) ≤
    ((s - a : ℕ) : ℝ) / ((n - s + a + 1 : ℕ) : ℝ) * (((a + 1 : ℕ) : ℝ) / (a : ℝ)) ^ (r - 1) := by
  have hfrac : ((s - b : ℕ) : ℝ) / ((n - s + b + 1 : ℕ) : ℝ) ≤
      ((s - a : ℕ) : ℝ) / ((n - s + a + 1 : ℕ) : ℝ) := by
    have hna : (0 : ℝ) < ((n - s + a + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - s + a + 1)
    have hnb : (0 : ℝ) < ((n - s + b + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - s + b + 1)
    rw [div_le_div_iff₀ hnb hna]
    have hnum : ((s - b : ℕ) : ℝ) ≤ ((s - a : ℕ) : ℝ) := by exact_mod_cast (by omega : s - b ≤ s - a)
    have hden : ((n - s + a + 1 : ℕ) : ℝ) ≤ ((n - s + b + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : n - s + a + 1 ≤ n - s + b + 1)
    nlinarith
  have hbase : (1 + 1 / (s : ℝ) ^ 2) * (((b + 1 : ℕ) : ℝ) / (b : ℝ)) ≤
      ((a + 1 : ℕ) : ℝ) / (a : ℝ) := by
    have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
    have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
    have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
    have habR : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast (by omega : a + 1 ≤ b)
    have hbaR : (a : ℝ) * ((b : ℝ) + 1) ≤ (s : ℝ) ^ 2 := by
      have ha_le : (a : ℝ) ≤ (s : ℝ) := by exact_mod_cast (by omega : a ≤ s)
      have hb_le : (b : ℝ) + 1 ≤ (s : ℝ) := by exact_mod_cast (by omega : b + 1 ≤ s)
      nlinarith
    have h1 : (1 + 1 / (s : ℝ) ^ 2) * (((b + 1 : ℕ) : ℝ) / (b : ℝ)) =
        (((b : ℝ) + 1) * ((s : ℝ) ^ 2 + 1)) / ((b : ℝ) * (s : ℝ) ^ 2) := by
      push_cast; field_simp
    have h2 : ((a + 1 : ℕ) : ℝ) / (a : ℝ) = ((a : ℝ) + 1) / (a : ℝ) := by push_cast; rfl
    rw [h1, h2, div_le_div_iff₀ (by positivity) haR]
    nlinarith
  have hpow : (1 + 1 / (s : ℝ) ^ 2) ^ (r - 1) * (((b + 1 : ℕ) : ℝ) / (b : ℝ)) ^ (r - 1) ≤
      (((a + 1 : ℕ) : ℝ) / (a : ℝ)) ^ (r - 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hbase (r - 1)
  have hfrac_nonneg : 0 ≤ ((s - b : ℕ) : ℝ) / ((n - s + b + 1 : ℕ) : ℝ) := by positivity
  have hpow_nonneg : 0 ≤ (((a + 1 : ℕ) : ℝ) / (a : ℝ)) ^ (r - 1) := by positivity
  calc (1 + 1 / (s : ℝ) ^ 2) ^ (r - 1) *
        (((s - b : ℕ) : ℝ) / ((n - s + b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ) / (b : ℝ)) ^ (r - 1))
      = ((s - b : ℕ) : ℝ) / ((n - s + b + 1 : ℕ) : ℝ) *
        ((1 + 1 / (s : ℝ) ^ 2) ^ (r - 1) * (((b + 1 : ℕ) : ℝ) / (b : ℝ)) ^ (r - 1)) := by ring
    _ ≤ ((s - b : ℕ) : ℝ) / ((n - s + b + 1 : ℕ) : ℝ) *
        (((a + 1 : ℕ) : ℝ) / (a : ℝ)) ^ (r - 1) :=
        mul_le_mul_of_nonneg_left hpow hfrac_nonneg
    _ ≤ ((s - a : ℕ) : ℝ) / ((n - s + a + 1 : ℕ) : ℝ) *
        (((a + 1 : ℕ) : ℝ) / (a : ℝ)) ^ (r - 1) :=
        mul_le_mul_of_nonneg_right hfrac hpow_nonneg

set_option maxHeartbeats 800000 in
lemma localization_of_eq (s n r : ℕ) (hs : 2 < s) (hn : s < n) (hr : 1 ≤ r)
    (heq : (∑ i ∈ Finset.Icc 1 s, (-1 : ℤ) ^ (i - 1) * (Nat.choose n (s - i) : ℤ) * (i : ℤ) ^ (r - 1)) = 0)
    (hB : (4 * (s : ℝ)) < (Real.sqrt (1 + 1 / (s : ℝ) ^ 2)) ^ (r - 1)) :
    ∃ j : ℕ, 1 ≤ j ∧ j < s ∧
      |(n : ℝ) * (j : ℝ) ^ (r - 1) - ((s - j : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) ^ (r - 1)| ≤
        (s : ℝ) * (j : ℝ) ^ (r - 1) +
        (4 * (s : ℝ) ^ 2) / (Real.sqrt (1 + 1 / (s : ℝ) ^ 2)) ^ (r - 1) * ((j + 1 : ℕ) : ℝ) ^ (r - 1) := by
  let T : ℕ → ℝ := fun i => (Nat.choose n (s - i) : ℝ) * (i : ℝ) ^ (r - 1)
  let R : ℕ → ℝ := fun i => T (i + 1) / T i
  let B : ℝ := (Real.sqrt (1 + 1 / (s : ℝ) ^ 2)) ^ (r - 1)
  have hBpos : 0 < B := by positivity
  have hBsq : B ^ 2 = (1 + 1 / (s : ℝ) ^ 2) ^ (r - 1) := by
    dsimp [B]
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by positivity)]
  have hTpos : ∀ i, 1 ≤ i → i ≤ s → 0 < T i := fun i hi1 his => term_pos s n r i hn hi1 his
  have hRratio : ∀ a b, 1 ≤ a → a < b → b < s → B ^ 2 * R b ≤ R a := by
    intro a b ha1 hab hbs
    rw [hBsq]
    dsimp [R, T]
    rw [term_ratio_eq s n r a hn ha1 (by omega), term_ratio_eq s n r b hn (by omega) hbs]
    exact ratio_step_bound s n r a b hs hn hr ha1 hab hbs
  have hsum0 : (∑ i ∈ Finset.Icc 1 s, (-1 : ℝ) ^ (i - 1) * T i) = 0 := by
    have hcast : ((∑ i ∈ Finset.Icc 1 s, (-1 : ℤ) ^ (i - 1) * (Nat.choose n (s - i) : ℤ) * (i : ℤ) ^ (r - 1) : ℤ) : ℝ) = 0 := by
      exact_mod_cast heq
    push_cast at hcast
    simpa [T, mul_assoc] using hcast
  -- Find maximizer i0 of T on Icc 1 s
  have hne : (Finset.Icc 1 s).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  obtain ⟨i0, hi0_mem, hi0_max⟩ := Finset.exists_max_image (Finset.Icc 1 s) T hne
  have hi0_1 : 1 ≤ i0 := (Finset.mem_Icc.mp hi0_mem).1
  have hi0_s : i0 ≤ s := (Finset.mem_Icc.mp hi0_mem).2
  -- Show there exists j in {1..s-1} with 1/B <= R j <= B and T i <= max(T j, T(j+1))/B for i != j, j+1
  have hdom : ∃ j : ℕ, 1 ≤ j ∧ j < s ∧
      ∀ i ∈ Finset.Icc 1 s, i ≠ j → i ≠ j + 1 → T i ≤ max (T j) (T (j + 1)) / B := by
    -- Either i0 > 1 and T (i0 - 1) >= T i0 / s, or i0 < s and T (i0 + 1) >= T i0 / s
    have hsecond : ∃ i1 ∈ (Finset.Icc 1 s).erase i0, T i0 / (s : ℝ) ≤ T i1 := by
      have hne' : ((Finset.Icc 1 s).erase i0).Nonempty := by
        by_cases h1 : i0 = 1
        · exact ⟨2, Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩⟩
        · exact ⟨1, Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩⟩
      obtain ⟨i1, hi1_mem, hi1_max⟩ := Finset.exists_max_image _ T hne'
      refine ⟨i1, hi1_mem, ?_⟩
      have hTi0_eq : (-1 : ℝ) ^ (i0 - 1) * T i0 =
          - ∑ i ∈ (Finset.Icc 1 s).erase i0, (-1 : ℝ) ^ (i - 1) * T i := by
        have hadd := Finset.add_sum_erase (Finset.Icc 1 s) (fun i => (-1 : ℝ) ^ (i - 1) * T i) hi0_mem
        linarith
      have hTi0_le : T i0 ≤ ∑ i ∈ (Finset.Icc 1 s).erase i0, T i := by
        have habs : T i0 = |(-1 : ℝ) ^ (i0 - 1) * T i0| := by
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos (hTpos i0 hi0_1 hi0_s)]
        rw [habs, hTi0_eq, abs_neg]
        calc |∑ i ∈ (Finset.Icc 1 s).erase i0, (-1 : ℝ) ^ (i - 1) * T i|
            ≤ ∑ i ∈ (Finset.Icc 1 s).erase i0, |(-1 : ℝ) ^ (i - 1) * T i| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ i ∈ (Finset.Icc 1 s).erase i0, T i := by
              apply Finset.sum_congr rfl
              intro i hi
              have him := Finset.mem_Icc.mp (Finset.mem_of_mem_erase hi)
              rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos (hTpos i him.1 him.2)]
      have hsum_le : ∑ i ∈ (Finset.Icc 1 s).erase i0, T i ≤ (s : ℝ) * T i1 := by
        have hcard : ((Finset.Icc 1 s).erase i0).card ≤ s := by
          have : (Finset.Icc 1 s).card = s := by simp
          calc ((Finset.Icc 1 s).erase i0).card ≤ (Finset.Icc 1 s).card := Finset.card_erase_le
            _ = s := this
        calc ∑ i ∈ (Finset.Icc 1 s).erase i0, T i
            ≤ ∑ _i ∈ (Finset.Icc 1 s).erase i0, T i1 := Finset.sum_le_sum fun i hi => hi1_max i hi
          _ = (((Finset.Icc 1 s).erase i0).card : ℝ) * T i1 := by simp
          _ ≤ (s : ℝ) * T i1 := by
              have hTi1_nn : 0 ≤ T i1 := by
                have him := Finset.mem_Icc.mp (Finset.mem_of_mem_erase hi1_mem)
                exact le_of_lt (hTpos i1 him.1 him.2)
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hTi1_nn
      have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
      rw [div_le_iff₀ hspos]
      linarith
    obtain ⟨i1, hi1_mem, hi1_ge⟩ := hsecond
    have hi1_ne : i1 ≠ i0 := (Finset.mem_erase.mp hi1_mem).1
    have hi1_icc := Finset.mem_Icc.mp (Finset.mem_of_mem_erase hi1_mem)
    -- Helper: if R k >= B for all k in [a, b-1], then T a <= T b / B^(b - a)
    -- Actually we just need T i <= T k / B when i < k and R i >= B, etc.
    have hBgt1 : 1 < B := by
      have : (2 : ℝ) ≤ 2 * (s : ℝ) := by exact_mod_cast (by omega : 2 ≤ 2 * s)
      linarith
    -- Case split on i1 < i0 vs i0 < i1
    rcases lt_or_gt_of_ne hi1_ne with hlt | hgt
    · -- i1 < i0, so i0 >= 2 and R (i0 - 1) >= 1
      have hRi0 : 1 ≤ R (i0 - 1) := by
        dsimp [R]
        have hsub : i0 - 1 + 1 = i0 := by omega
        rw [hsub, one_le_div (hTpos (i0 - 1) (by omega) (by omega))]
        exact hi0_max (i0 - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      -- Show i1 = i0 - 1
      have hi1_eq : i1 = i0 - 1 := by
        by_contra hne1
        have hle2 : i1 ≤ i0 - 2 := by omega
        have hR_ge : ∀ k, i1 ≤ k → k ≤ i0 - 2 → B ^ 2 ≤ R k := by
          intro k hk1 hk2
          have := hRratio k (i0 - 1) (by omega) (by omega) (by omega)
          nlinarith
        -- T i1 <= T (i1 + 1) / B^2 <= T i0 / B^2
        have hstep : B ^ 2 * T i1 ≤ T (i1 + 1) := by
          have := hR_ge i1 le_rfl hle2
          dsimp [R] at this
          rwa [le_div_iff₀ (hTpos i1 hi1_icc.1 hi1_icc.2)] at this
        have hle_i0 : T (i1 + 1) ≤ T i0 :=
          hi0_max (i1 + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
        have hTi0pos : 0 < T i0 := hTpos i0 hi0_1 hi0_s
        have hB2_gt_s : (s : ℝ) < B ^ 2 := by nlinarith
        have : B ^ 2 * (T i0 / (s : ℝ)) ≤ T i0 := by nlinarith
        rw [mul_div_assoc', div_le_iff₀ hspos] at this
        nlinarith
      refine ⟨i0 - 1, by omega, by omega, ?_⟩
      intro i hi hne_j hne_j1
      have hi_icc := Finset.mem_Icc.mp hi
      have hsub : i0 - 1 + 1 = i0 := by omega
      rw [hsub] at hne_j1 ⊢
      have hmax_ge : T i0 ≤ max (T (i0 - 1)) (T i0) := le_max_right _ _
      rcases lt_or_gt_of_ne (by omega : i ≠ i0) with hilt | higt
      · -- i < i0 - 1, so R i >= B^2 >= B
        have hRi : B ≤ R i := by
          have := hRratio i (i0 - 1) hi_icc.1 (by omega) (by omega)
          nlinarith
        dsimp [R] at hRi
        rw [le_div_iff₀ (hTpos i hi_icc.1 hi_icc.2)] at hRi
        have hTi1_le : T (i + 1) ≤ T i0 :=
          hi0_max (i + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        rw [le_div_iff₀ hBpos]
        linarith
      · -- i > i0, so i - 1 >= i0, and R (i0 - 1) <= s, so R (i - 1) <= s / B^2 <= 1 / B
        have hRj_le : R (i0 - 1) ≤ (s : ℝ) := by
          dsimp [R]
          rw [hsub, div_le_iff₀ (hTpos (i0 - 1) (by omega) (by omega))]
          have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
          rw [hi1_eq] at hi1_ge
          rw [div_le_iff₀ hspos] at hi1_ge
          linarith
        have hRi : R (i - 1) ≤ 1 / B := by
          have h1 := hRratio (i0 - 1) (i - 1) (by omega) (by omega) (by omega)
          rw [le_div_iff₀ hBpos]
          have : B ^ 2 * R (i - 1) ≤ (s : ℝ) := le_trans h1 hRj_le
          have hRnn : 0 ≤ R (i - 1) := div_nonneg (le_of_lt (hTpos _ (by omega) (by omega)))
            (le_of_lt (hTpos _ (by omega) (by omega)))
          nlinarith
        dsimp [R] at hRi
        have hisub : i - 1 + 1 = i := by omega
        rw [hisub, div_le_div_iff₀ (hTpos (i - 1) (by omega) (by omega)) hBpos] at hRi
        have hTim1_le : T (i - 1) ≤ T i0 :=
          hi0_max (i - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        rw [le_div_iff₀ hBpos]
        linarith
    · -- i0 < i1, so i0 < s and R i0 <= 1
      have hRi0 : R i0 ≤ 1 := by
        dsimp [R]
        rw [div_le_one (hTpos i0 hi0_1 hi0_s)]
        exact hi0_max (i0 + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      have hi1_eq : i1 = i0 + 1 := by
        by_contra hne1
        have hge2 : i0 + 2 ≤ i1 := by omega
        have hR_le : R (i1 - 1) ≤ 1 / B ^ 2 := by
          have := hRratio i0 (i1 - 1) hi0_1 (by omega) (by omega)
          rw [le_div_iff₀ (by positivity)]
          linarith
        dsimp [R] at hR_le
        have hisub : i1 - 1 + 1 = i1 := by omega
        rw [hisub, div_le_div_iff₀ (hTpos (i1 - 1) (by omega) (by omega)) (by positivity)] at hR_le
        have hle_i0 : T (i1 - 1) ≤ T i0 :=
          hi0_max (i1 - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
        have hTi0pos : 0 < T i0 := hTpos i0 hi0_1 hi0_s
        have hB2_gt_s : (s : ℝ) < B ^ 2 := by nlinarith
        have : B ^ 2 * (T i0 / (s : ℝ)) ≤ T i0 := by nlinarith
        rw [mul_div_assoc', div_le_iff₀ hspos] at this
        nlinarith
      refine ⟨i0, hi0_1, by omega, ?_⟩
      intro i hi hne_j hne_j1
      have hi_icc := Finset.mem_Icc.mp hi
      have hmax_ge : T i0 ≤ max (T i0) (T (i0 + 1)) := le_max_left _ _
      rcases lt_or_gt_of_ne hne_j with hilt | higt
      · -- i < i0, R i0 >= 1/s so R i >= B^2 / s >= B
        have hRj_ge : 1 / (s : ℝ) ≤ R i0 := by
          dsimp [R]
          have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
          rw [div_le_div_iff₀ hspos (hTpos i0 hi0_1 hi0_s)]
          rw [hi1_eq] at hi1_ge
          rw [div_le_iff₀ hspos] at hi1_ge
          linarith
        have hRi : B ≤ R i := by
          have h1 := hRratio i i0 hi_icc.1 hilt (by omega)
          have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
          have h2 : B ^ 2 / (s : ℝ) ≤ B ^ 2 * R i0 := by
            rw [div_eq_mul_one_div]
            exact mul_le_mul_of_nonneg_left hRj_ge (sq_nonneg B)
          have h3 : B ≤ B ^ 2 / (s : ℝ) := by
            rw [le_div_iff₀ hspos]; nlinarith
          linarith
        dsimp [R] at hRi
        rw [le_div_iff₀ (hTpos i hi_icc.1 hi_icc.2)] at hRi
        have hTi1_le : T (i + 1) ≤ T i0 :=
          hi0_max (i + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        rw [le_div_iff₀ hBpos]
        linarith
      · -- i > i0 + 1, so i - 1 > i0, R (i - 1) <= 1 / B^2 <= 1 / B
        have hRi : R (i - 1) ≤ 1 / B := by
          have h1 := hRratio i0 (i - 1) hi0_1 (by omega) (by omega)
          rw [le_div_iff₀ hBpos]
          have hRnn : 0 ≤ R (i - 1) := div_nonneg (le_of_lt (hTpos _ (by omega) (by omega)))
            (le_of_lt (hTpos _ (by omega) (by omega)))
          nlinarith
        dsimp [R] at hRi
        have hisub : i - 1 + 1 = i := by omega
        rw [hisub, div_le_div_iff₀ (hTpos (i - 1) (by omega) (by omega)) hBpos] at hRi
        have hTim1_le : T (i - 1) ≤ T i0 :=
          hi0_max (i - 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        rw [le_div_iff₀ hBpos]
        linarith
  obtain ⟨j, hj1, hjs, hdom_j⟩ := hdom
  refine ⟨j, hj1, hjs, ?_⟩
  -- Now |T j - T (j + 1)| <= (s / B) * max (T j) (T (j + 1))
  have hj_mem : j ∈ Finset.Icc 1 s := Finset.mem_Icc.mpr ⟨hj1, by omega⟩
  have hj1_mem : j + 1 ∈ (Finset.Icc 1 s).erase j :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩
  have hdiff_eq : (-1 : ℝ) ^ (j - 1) * (T j - T (j + 1)) =
      - ∑ i ∈ ((Finset.Icc 1 s).erase j).erase (j + 1), (-1 : ℝ) ^ (i - 1) * T i := by
    have h1 := Finset.add_sum_erase (Finset.Icc 1 s) (fun i => (-1 : ℝ) ^ (i - 1) * T i) hj_mem
    have h2 := Finset.add_sum_erase ((Finset.Icc 1 s).erase j) (fun i => (-1 : ℝ) ^ (i - 1) * T i) hj1_mem
    have hsign : (-1 : ℝ) ^ (j + 1 - 1) = -((-1 : ℝ) ^ (j - 1)) := by
      have : j + 1 - 1 = (j - 1) + 1 := by omega
      rw [this, pow_succ]; ring
    rw [hsign] at h2
    linarith
  have hdiff_le : |T j - T (j + 1)| ≤ (s : ℝ) * (max (T j) (T (j + 1)) / B) := by
    have habs : |T j - T (j + 1)| = |(-1 : ℝ) ^ (j - 1) * (T j - T (j + 1))| := by
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    rw [habs, hdiff_eq, abs_neg]
    calc |∑ i ∈ ((Finset.Icc 1 s).erase j).erase (j + 1), (-1 : ℝ) ^ (i - 1) * T i|
        ≤ ∑ i ∈ ((Finset.Icc 1 s).erase j).erase (j + 1), |(-1 : ℝ) ^ (i - 1) * T i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ ((Finset.Icc 1 s).erase j).erase (j + 1), T i := by
          apply Finset.sum_congr rfl
          intro i hi
          have him := Finset.mem_Icc.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi))
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos (hTpos i him.1 him.2)]
      _ ≤ ∑ _i ∈ ((Finset.Icc 1 s).erase j).erase (j + 1), (max (T j) (T (j + 1)) / B) := by
          apply Finset.sum_le_sum
          intro i hi
          have hne1 : i ≠ j + 1 := (Finset.mem_erase.mp hi).1
          have hi' := Finset.mem_of_mem_erase hi
          have hne0 : i ≠ j := (Finset.mem_erase.mp hi').1
          exact hdom_j i (Finset.mem_of_mem_erase hi') hne0 hne1
      _ = ((((Finset.Icc 1 s).erase j).erase (j + 1)).card : ℝ) * (max (T j) (T (j + 1)) / B) := by simp
      _ ≤ (s : ℝ) * (max (T j) (T (j + 1)) / B) := by
          have hcard : (((Finset.Icc 1 s).erase j).erase (j + 1)).card ≤ s := by
            calc (((Finset.Icc 1 s).erase j).erase (j + 1)).card
                ≤ ((Finset.Icc 1 s).erase j).card := Finset.card_erase_le
              _ ≤ (Finset.Icc 1 s).card := Finset.card_erase_le
              _ = s := by simp
          have hnn : 0 ≤ max (T j) (T (j + 1)) / B := by
            have := hTpos j hj1 (by omega)
            exact div_nonneg (le_trans (le_of_lt this) (le_max_left _ _)) (le_of_lt hBpos)
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hnn
  -- From |T j - T (j + 1)| <= (s / B) * max(T j, T (j+1)) and B > 2*s, we get max <= 2 * T j
  have hTj_pos : 0 < T j := hTpos j hj1 (by omega)
  have hmax_le : max (T j) (T (j + 1)) ≤ 2 * T j := by
    have hsb : (s : ℝ) / B ≤ 1 / 2 := by rw [div_le_div_iff₀ hBpos (by norm_num)]; linarith
    have h1 : T (j + 1) - T j ≤ (s : ℝ) / B * max (T j) (T (j + 1)) := by
      have h1a := (abs_le.mp hdiff_le).1
      have h1b : (s : ℝ) * (max (T j) (T (j + 1)) / B) = (s : ℝ) / B * max (T j) (T (j + 1)) := by ring
      linarith
    have hmax_nn : 0 ≤ max (T j) (T (j + 1)) := le_trans (le_of_lt hTj_pos) (le_max_left _ _)
    have h2 : T (j + 1) - T j ≤ 1 / 2 * max (T j) (T (j + 1)) := by
      have := mul_le_mul_of_nonneg_right hsb hmax_nn
      linarith
    rcases le_total (T j) (T (j + 1)) with hle | hge
    · rw [max_eq_right hle] at h2 ⊢; linarith
    · rw [max_eq_left hge]; linarith
  have hRdiff : |1 - R j| ≤ (2 * (s : ℝ)) / B := by
    have h1 : |T j - T (j + 1)| ≤ (2 * (s : ℝ)) / B * T j := by
      have hs_nn : 0 ≤ (s : ℝ) := by positivity
      calc |T j - T (j + 1)| ≤ (s : ℝ) * (max (T j) (T (j + 1)) / B) := hdiff_le
        _ ≤ (s : ℝ) * (2 * T j / B) := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hmax_le (le_of_lt hBpos)) hs_nn
        _ = (2 * (s : ℝ)) / B * T j := by ring
    dsimp [R]
    have h2 : |1 - T (j + 1) / T j| = |T j - T (j + 1)| / T j := by
      rw [show 1 - T (j + 1) / T j = (T j - T (j + 1)) / T j by field_simp, abs_div, abs_of_pos hTj_pos]
    rw [h2, div_le_iff₀ hTj_pos]
    exact h1
  -- Express R j = (s - j) / (n - s + j + 1) * ((j + 1) / j)^(r - 1)
  have hRj_eq : R j = ((s - j : ℕ) : ℝ) / ((n - s + j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) / (j : ℝ)) ^ (r - 1) :=
    term_ratio_eq s n r j hn hj1 hjs
  -- Bound (n - s + j + 1) <= 2 * (s - j) * ((j + 1) / j)^(r - 1)
  have hden_pos : (0 : ℝ) < ((n - s + j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - s + j + 1)
  have hRj_ge_half : (1 / 2 : ℝ) ≤ R j := by
    have h1 := (abs_le.mp hRdiff).2
    have h2 : (2 * (s : ℝ)) / B ≤ 1 / 2 := by rw [div_le_div_iff₀ hBpos (by norm_num)]; linarith
    linarith
  have hden_le : ((n - s + j + 1 : ℕ) : ℝ) ≤ 2 * ((s - j : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) / (j : ℝ)) ^ (r - 1) := by
    rw [hRj_eq] at hRj_ge_half
    have hmul : (1 / 2 : ℝ) * ((n - s + j + 1 : ℕ) : ℝ) ≤
        ((s - j : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) / (j : ℝ)) ^ (r - 1) := by
      have := mul_le_mul_of_nonneg_right hRj_ge_half (le_of_lt hden_pos)
      field_simp at this ⊢
      linarith
    linarith
  -- Multiply |1 - R j| <= 2*s/B by (n - s + j + 1) * j^(r - 1)
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hmain_diff : |((n - s + j + 1 : ℕ) : ℝ) * (j : ℝ) ^ (r - 1) - ((s - j : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) ^ (r - 1)| ≤
      (4 * (s : ℝ) ^ 2) / B * ((j + 1 : ℕ) : ℝ) ^ (r - 1) := by
    have hid : ((n - s + j + 1 : ℕ) : ℝ) * (j : ℝ) ^ (r - 1) - ((s - j : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) ^ (r - 1) =
        (1 - R j) * (((n - s + j + 1 : ℕ) : ℝ) * (j : ℝ) ^ (r - 1)) := by
      rw [hRj_eq, div_pow]
      field_simp
    rw [hid, abs_mul, abs_of_pos (mul_pos hden_pos (pow_pos hjpos _))]
    have hprod_le : ((n - s + j + 1 : ℕ) : ℝ) * (j : ℝ) ^ (r - 1) ≤
        2 * (s : ℝ) * ((j + 1 : ℕ) : ℝ) ^ (r - 1) := by
      have hsj_le : ((s - j : ℕ) : ℝ) ≤ (s : ℝ) := by exact_mod_cast (by omega : s - j ≤ s)
      calc ((n - s + j + 1 : ℕ) : ℝ) * (j : ℝ) ^ (r - 1)
          ≤ (2 * ((s - j : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) / (j : ℝ)) ^ (r - 1)) * (j : ℝ) ^ (r - 1) :=
            mul_le_mul_of_nonneg_right hden_le (by positivity)
        _ = 2 * ((s - j : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) ^ (r - 1) := by
            rw [div_pow]; field_simp
        _ ≤ 2 * (s : ℝ) * ((j + 1 : ℕ) : ℝ) ^ (r - 1) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    calc |1 - R j| * (((n - s + j + 1 : ℕ) : ℝ) * (j : ℝ) ^ (r - 1))
        ≤ (2 * (s : ℝ) / B) * (2 * (s : ℝ) * ((j + 1 : ℕ) : ℝ) ^ (r - 1)) :=
          mul_le_mul hRdiff hprod_le (by positivity) (by positivity)
      _ = (4 * (s : ℝ) ^ 2) / B * ((j + 1 : ℕ) : ℝ) ^ (r - 1) := by ring
  -- Finally, |(n - (n - s + j + 1)) * j^(r-1)| <= s * j^(r-1)
  have hshift : (n : ℝ) - ((n - s + j + 1 : ℕ) : ℝ) = ((s - j - 1 : ℕ) : ℝ) := by
    have : n = (n - s + j + 1) + (s - j - 1) := by omega
    have hcast : (n : ℝ) = ((n - s + j + 1 : ℕ) : ℝ) + ((s - j - 1 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have htri : |(n : ℝ) * (j : ℝ) ^ (r - 1) - ((s - j : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) ^ (r - 1)| ≤
      |((s - j - 1 : ℕ) : ℝ) * (j : ℝ) ^ (r - 1)| +
      |((n - s + j + 1 : ℕ) : ℝ) * (j : ℝ) ^ (r - 1) - ((s - j : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) ^ (r - 1)| := by
    have hsplit : (n : ℝ) * (j : ℝ) ^ (r - 1) - ((s - j : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) ^ (r - 1) =
        ((s - j - 1 : ℕ) : ℝ) * (j : ℝ) ^ (r - 1) +
        (((n - s + j + 1 : ℕ) : ℝ) * (j : ℝ) ^ (r - 1) - ((s - j : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) ^ (r - 1)) := by
      linarith [mul_sub ((n : ℝ) - ((n - s + j + 1 : ℕ) : ℝ)) ((j : ℝ) ^ (r - 1)) 0,
        congrArg (· * (j : ℝ) ^ (r - 1)) hshift]
    rw [hsplit]
    exact abs_add_le _ _
  have hfirst_le : |((s - j - 1 : ℕ) : ℝ) * (j : ℝ) ^ (r - 1)| ≤ (s : ℝ) * (j : ℝ) ^ (r - 1) := by
    rw [abs_of_nonneg (by positivity)]
    have : ((s - j - 1 : ℕ) : ℝ) ≤ (s : ℝ) := by exact_mod_cast (by omega : s - j - 1 ≤ s)
    exact mul_le_mul_of_nonneg_right this (by positivity)
  linarith

lemma no_exact_solution_j1 (s r : ℕ) (hs : 2 < s) (hr : 1 ≤ r)
    (hr_big : (2 * (s : ℝ)) * (2 / 3 : ℝ) ^ (r - 1) < 1 / 2)
    (hn : 2 * s ≤ (s - 1) * 2 ^ (r - 1)) :
    (∑ i ∈ Finset.Icc 1 s, (-1 : ℤ) ^ (i - 1) *
      (Nat.choose ((s - 1) * 2 ^ (r - 1)) (s - i) : ℤ) * (i : ℤ) ^ (r - 1)) ≠ 0 := by
  set n := (s - 1) * 2 ^ (r - 1)
  have hns : s < n := by omega
  let T : ℕ → ℝ := fun i => (Nat.choose n (s - i) : ℝ) * (i : ℝ) ^ (r - 1)
  have hTpos : ∀ i, 1 ≤ i → i ≤ s → 0 < T i := fun i hi1 his => term_pos s n r i hns hi1 his
  intro heq
  have hsum0 : (∑ i ∈ Finset.Icc 1 s, (-1 : ℝ) ^ (i - 1) * T i) = 0 := by
    have hcast : ((∑ i ∈ Finset.Icc 1 s, (-1 : ℤ) ^ (i - 1) * (Nat.choose n (s - i) : ℤ) * (i : ℤ) ^ (r - 1) : ℤ) : ℝ) = 0 := by
      exact_mod_cast heq
    push_cast at hcast
    simpa [T, mul_assoc] using hcast
  -- Compute T 1 - T 2
  have hT12_abs : |T 1 - T 2| ≤ (2 / 3 : ℝ) ^ (r - 1) * T 3 := by
    have hch12 : Nat.choose n (s - 1) * (s - 1) = Nat.choose n (s - 2) * (n - s + 2) := by
      have h1 := Nat.choose_succ_right_eq n (s - 2)
      have h2 : s - 2 + 1 = s - 1 := by omega
      have h3 : n - (s - 2) = n - s + 2 := by omega
      rw [h2, h3] at h1; linarith
    have hch23 : Nat.choose n (s - 2) * (s - 2) = Nat.choose n (s - 3) * (n - s + 3) := by
      have h1 := Nat.choose_succ_right_eq n (s - 3)
      have h2 : s - 3 + 1 = s - 2 := by omega
      have h3 : n - (s - 3) = n - s + 3 := by omega
      rw [h2, h3] at h1; linarith
    have hch12R : (Nat.choose n (s - 1) : ℝ) * ((s - 1 : ℕ) : ℝ) =
        (Nat.choose n (s - 2) : ℝ) * ((n - s + 2 : ℕ) : ℝ) := by exact_mod_cast hch12
    have hch23R : (Nat.choose n (s - 2) : ℝ) * ((s - 2 : ℕ) : ℝ) =
        (Nat.choose n (s - 3) : ℝ) * ((n - s + 3 : ℕ) : ℝ) := by exact_mod_cast hch23
    have hs1_pos : (0 : ℝ) < ((s - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < s - 1)
    have hn_eq : (n : ℝ) = ((s - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (r - 1) := by
      dsimp [n]; push_cast; rfl
    have hns2 : ((n - s + 2 : ℕ) : ℝ) = (n : ℝ) - ((s - 2 : ℕ) : ℝ) := by
      have : (n - s + 2) + (s - 2) = n := by omega
      have hc : ((n - s + 2 : ℕ) : ℝ) + ((s - 2 : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast this
      linarith
    have hT12_eq : T 1 - T 2 = -(((s - 2 : ℕ) : ℝ) / ((s - 1 : ℕ) : ℝ)) * (Nat.choose n (s - 2) : ℝ) := by
      dsimp [T]
      have h1 : (Nat.choose n (s - 1) : ℝ) =
          (Nat.choose n (s - 2) : ℝ) * ((n - s + 2 : ℕ) : ℝ) / ((s - 1 : ℕ) : ℝ) := by
        rw [eq_div_iff (ne_of_gt hs1_pos)]; exact hch12R
      rw [h1, hns2, hn_eq]
      field_simp
      ring
    rw [hT12_eq, neg_mul, abs_neg, abs_of_nonneg (by positivity)]
    have hle1 : ((s - 2 : ℕ) : ℝ) * (Nat.choose n (s - 2) : ℝ) =
        (Nat.choose n (s - 3) : ℝ) * ((n - s + 3 : ℕ) : ℝ) := by linarith
    have hns3_le : ((n - s + 3 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : n - s + 3 ≤ n)
    dsimp [T]
    calc ((s - 2 : ℕ) : ℝ) / ((s - 1 : ℕ) : ℝ) * (Nat.choose n (s - 2) : ℝ)
        = (Nat.choose n (s - 3) : ℝ) * ((n - s + 3 : ℕ) : ℝ) / ((s - 1 : ℕ) : ℝ) := by
          rw [div_mul_eq_mul_div, hle1]
      _ ≤ (Nat.choose n (s - 3) : ℝ) * (n : ℝ) / ((s - 1 : ℕ) : ℝ) := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hs1_pos)
          exact mul_le_mul_of_nonneg_left hns3_le (by positivity)
      _ = (Nat.choose n (s - 3) : ℝ) * (2 : ℝ) ^ (r - 1) := by
          rw [hn_eq]; field_simp
      _ = (2 / 3 : ℝ) ^ (r - 1) * ((Nat.choose n (s - 3) : ℝ) * (3 : ℝ) ^ (r - 1)) := by
          rw [div_pow]; field_simp
  -- For every i >= 4, T i <= (2*s * (2/3)^(r-1)) * T 3 <= (1/2) * T 3 / s? Actually T i <= (2/3)^(r-1) * 2 * T 3
  have hTi_le : ∀ i ∈ Finset.Icc 4 s, T i ≤ (2 * (2 / 3 : ℝ) ^ (r - 1)) * T 3 := by
    -- Show by induction on i >= 4 that T i <= (2 * (2/3)^(r-1)) * T 3
    intro i hi
    have hi_icc := Finset.mem_Icc.mp hi
    -- First show for all k in [3, s-1], T (k + 1) / T k <= 2 * (2/3)^(r-1)
    have hstep_le : ∀ k, 3 ≤ k → k < s → T (k + 1) ≤ (2 * (2 / 3 : ℝ) ^ (r - 1)) * T k := by
      intro k hk3 hks
      have hrat := term_ratio_eq s n r k hns (by omega) hks
      dsimp [T] at hrat ⊢
      rw [← div_le_iff₀ (hTpos k (by omega) (by omega)), hrat]
      have hbase_le : (((k + 1 : ℕ) : ℝ) / (k : ℝ)) ≤ 4 / 3 := by
        have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        push_cast; linarith
      have hpow_le : (((k + 1 : ℕ) : ℝ) / (k : ℝ)) ^ (r - 1) ≤ (4 / 3 : ℝ) ^ (r - 1) :=
        pow_le_pow_left₀ (by positivity) hbase_le (r - 1)
      have hfrac_le : ((s - k : ℕ) : ℝ) / ((n - s + k + 1 : ℕ) : ℝ) ≤ 2 / (2 : ℝ) ^ (r - 1) := by
        have hden_pos : (0 : ℝ) < ((n - s + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - s + k + 1)
        rw [div_le_div_iff₀ hden_pos (by positivity)]
        have hsk : ((s - k : ℕ) : ℝ) ≤ ((s - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : s - k ≤ s - 1)
        have h2n : (n : ℝ) ≤ 2 * ((n - s + k + 1 : ℕ) : ℝ) := by
          have : n ≤ 2 * (n - s + k + 1) := by omega
          exact_mod_cast this
        have hn_eq : (n : ℝ) = ((s - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (r - 1) := by
          dsimp [n]; push_cast; rfl
        have hmul : ((s - k : ℕ) : ℝ) * (2 : ℝ) ^ (r - 1) ≤ ((s - 1 : ℕ) : ℝ) * (2 : ℝ) ^ (r - 1) :=
          mul_le_mul_of_nonneg_right hsk (by positivity)
        linarith
      calc ((s - k : ℕ) : ℝ) / ((n - s + k + 1 : ℕ) : ℝ) * (((k + 1 : ℕ) : ℝ) / (k : ℝ)) ^ (r - 1)
          ≤ (2 / (2 : ℝ) ^ (r - 1)) * (4 / 3 : ℝ) ^ (r - 1) :=
            mul_le_mul hfrac_le hpow_le (by positivity) (by positivity)
        _ = 2 * (2 / 3 : ℝ) ^ (r - 1) := by
            rw [div_pow, div_pow]
            have : (4 : ℝ) ^ (r - 1) = (2 : ℝ) ^ (r - 1) * (2 : ℝ) ^ (r - 1) := by rw [← mul_pow]; norm_num
            rw [this]; field_simp
    have hcoeff_le1 : 2 * (2 / 3 : ℝ) ^ (r - 1) ≤ 1 := by
      have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast (by omega : 1 ≤ s)
      nlinarith
    -- Induction on d = i - 4
    obtain ⟨d, rfl⟩ : ∃ d, i = 4 + d := ⟨i - 4, by omega⟩
    induction d with
    | zero => exact hstep_le 3 le_rfl (by omega)
    | succ d ih =>
      have hprev := ih (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) (by omega)
      have hnext := hstep_le (4 + d) (by omega) (by omega)
      have hTnn : 0 ≤ T (4 + d) := le_of_lt (hTpos (4 + d) (by omega) (by omega))
      calc T (4 + d + 1) ≤ (2 * (2 / 3 : ℝ) ^ (r - 1)) * T (4 + d) := hnext
        _ ≤ 1 * T (4 + d) := mul_le_mul_of_nonneg_right hcoeff_le1 hTnn
        _ = T (4 + d) := one_mul _
        _ ≤ (2 * (2 / 3 : ℝ) ^ (r - 1)) * T 3 := hprev
  -- Split the sum Icc 1 s into {1, 2, 3} and Icc 4 s
  have hsplit : Finset.Icc 1 s = insert 1 (insert 2 (insert 3 (Finset.Icc 4 s))) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hsplit, Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp)] at hsum0
  have hT3_eq : T 3 = -(T 1 - T 2) - ∑ i ∈ Finset.Icc 4 s, (-1 : ℝ) ^ (i - 1) * T i := by
    norm_num at hsum0
    linarith
  have hT3_le : T 3 ≤ |T 1 - T 2| + ∑ i ∈ Finset.Icc 4 s, T i := by
    calc T 3 = -(T 1 - T 2) - ∑ i ∈ Finset.Icc 4 s, (-1 : ℝ) ^ (i - 1) * T i := hT3_eq
      _ ≤ |T 1 - T 2| + |∑ i ∈ Finset.Icc 4 s, (-1 : ℝ) ^ (i - 1) * T i| := by
          linarith [neg_le_abs (T 1 - T 2), neg_le_abs (∑ i ∈ Finset.Icc 4 s, (-1 : ℝ) ^ (i - 1) * T i)]
      _ ≤ |T 1 - T 2| + ∑ i ∈ Finset.Icc 4 s, |(-1 : ℝ) ^ (i - 1) * T i| := by
          linarith [Finset.abs_sum_le_sum_abs (fun i => (-1 : ℝ) ^ (i - 1) * T i) (Finset.Icc 4 s)]
      _ = |T 1 - T 2| + ∑ i ∈ Finset.Icc 4 s, T i := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          have him := Finset.mem_Icc.mp hi
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos (hTpos i (by omega) him.2)]
  have hsum4_le : ∑ i ∈ Finset.Icc 4 s, T i ≤ ((s : ℝ) - 1) * (2 * (2 / 3 : ℝ) ^ (r - 1)) * T 3 := by
    have hcard : (Finset.Icc 4 s).card ≤ s - 1 := by simp; omega
    calc ∑ i ∈ Finset.Icc 4 s, T i
        ≤ ∑ _i ∈ Finset.Icc 4 s, ((2 * (2 / 3 : ℝ) ^ (r - 1)) * T 3) :=
          Finset.sum_le_sum hTi_le
      _ = ((Finset.Icc 4 s).card : ℝ) * ((2 * (2 / 3 : ℝ) ^ (r - 1)) * T 3) := by simp
      _ ≤ ((s - 1 : ℕ) : ℝ) * ((2 * (2 / 3 : ℝ) ^ (r - 1)) * T 3) := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by have := hTpos 3 (by omega) (by omega); positivity)
      _ = ((s : ℝ) - 1) * (2 * (2 / 3 : ℝ) ^ (r - 1)) * T 3 := by
          have : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by exact_mod_cast (Nat.cast_sub (by omega : 1 ≤ s))
          rw [this]; ring
  have hT3pos : 0 < T 3 := hTpos 3 (by omega) (by omega)
  have htot : T 3 ≤ (2 * (s : ℝ)) * (2 / 3 : ℝ) ^ (r - 1) * T 3 := by
    have : (2 / 3 : ℝ) ^ (r - 1) * T 3 + ((s : ℝ) - 1) * (2 * (2 / 3 : ℝ) ^ (r - 1)) * T 3 ≤
        (2 * (s : ℝ)) * (2 / 3 : ℝ) ^ (r - 1) * T 3 := by
      have : 0 ≤ (2 / 3 : ℝ) ^ (r - 1) * T 3 := by positivity
      linarith
    linarith
  nlinarith

theorem main : H1 → H2 → type_of% @Erdos494.erdos_494.variants.gordon_fraenkel_straus := by
  intro h1 h2 s hs
  -- Choose lambda = max ((s-1)/s) (1 / sqrt(1 + 1/s^2)) < 1 and epsilon > 0
  let γ : ℝ := Real.sqrt (1 + 1 / (s : ℝ) ^ 2)
  have hγ_gt1 : 1 < γ := by
    dsimp [γ]
    rw [Real.lt_sqrt (by norm_num)]
    have : 0 < 1 / (s : ℝ) ^ 2 := by positivity
    linarith
  let lam : ℝ := max (((s - 1 : ℕ) : ℝ) / (s : ℝ)) (1 / γ)
  have hlam_pos : 0 < lam := by
    have : 0 < 1 / γ := by positivity
    exact lt_of_lt_of_le this (le_max_right _ _)
  have hlam_lt1 : lam < 1 := by
    apply max_lt
    · have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
      rw [div_lt_one hspos]
      exact_mod_cast (by omega : s - 1 < s)
    · rw [div_lt_one (by linarith)]; exact hγ_gt1
  -- Pick epsilon > 0 so that s^epsilon < lam^(-1/2)
  have hlog_lam_neg : Real.log lam < 0 := Real.log_neg hlam_pos hlam_lt1
  have hlog_lam_neg' : 0 < -Real.log lam := neg_pos.mpr hlog_lam_neg
  have hlog_s_pos : 0 < Real.log (s : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < s))
  let ε : ℝ := (-Real.log lam) / (4 * Real.log (s : ℝ))
  have hε_pos : 0 < ε := by dsimp [ε]; positivity
  -- Compute (lam * (s : ℝ) ^ ε) < 1 directly!
  have hlam_sε_lt1 : lam * (s : ℝ) ^ ε < 1 := by
    have h1 : Real.log (lam * (s : ℝ) ^ ε) < 0 := by
      rw [Real.log_mul (ne_of_gt hlam_pos) (ne_of_gt (Real.rpow_pos_of_pos (by positivity) ε)),
          Real.log_rpow (by positivity)]
      dsimp [ε]
      field_simp
      linarith
    have h2 := Real.exp_lt_exp.mpr h1
    rw [Real.exp_log (by positivity), Real.exp_zero] at h2
    exact h2
  -- By H2, the set of exceptional (p, q) is finite, so q is bounded above by some Qmax
  have hfin := h2 s ε hε_pos
  obtain ⟨Qmax, hQmax⟩ : ∃ Qmax : ℕ, ∀ pq ∈ {pq : ℕ × ℕ | 0 < pq.1 ∧ 0 < pq.2 ∧
      (∀ p : ℕ, p.Prime → p ∣ pq.1 → p ≤ s) ∧
      (∀ p : ℕ, p.Prime → p ∣ pq.2 → p ≤ s) ∧
      pq.1 ≠ pq.2 ∧
      |(pq.2 : ℝ) - (pq.1 : ℝ)| < (pq.2 : ℝ) ^ (1 - ε)}, pq.2 ≤ Qmax := by
    obtain ⟨B, hB⟩ := (hfin.image Prod.snd).bddAbove
    refine ⟨B, fun pq hpq => hB ⟨pq, hpq, rfl⟩⟩
  -- Pick R0 large enough for all asymptotic inequalities
  have h_ev_r : ∀ᶠ r : ℕ in atTop,
      1 ≤ r ∧
      (4 * (s : ℝ)) < γ ^ (r - 1) ∧
      (2 * (s : ℝ)) * (2 / 3 : ℝ) ^ (r - 1) < 1 / 2 ∧
      s < 2 ^ (r - 1) ∧
      Qmax < 2 ^ (r - 1) ∧
      ((s : ℝ) + 4 * (s : ℝ) ^ 2) * (s : ℝ) ^ ε * (lam * (s : ℝ) ^ ε) ^ (r - 1) < 1 := by
    have h1 : ∀ᶠ r : ℕ in atTop, 1 ≤ r := eventually_ge_atTop 1
    have h2' : ∀ᶠ r : ℕ in atTop, (4 * (s : ℝ)) < γ ^ (r - 1) := by
      have ht := tendsto_pow_atTop_atTop_of_one_lt hγ_gt1
      have ht' := (ht.comp (tendsto_sub_atTop_nat 1)).eventually_gt_atTop (4 * (s : ℝ))
      exact ht'
    have h3 : ∀ᶠ r : ℕ in atTop, (2 * (s : ℝ)) * (2 / 3 : ℝ) ^ (r - 1) < 1 / 2 := by
      have ht : Tendsto (fun r : ℕ => (2 * (s : ℝ)) * (2 / 3 : ℝ) ^ (r - 1)) atTop (nhds 0) := by
        simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num : (2 / 3 : ℝ) < 1)).comp
          (tendsto_sub_atTop_nat 1)).const_mul (2 * (s : ℝ))
      exact ht.eventually (gt_mem_nhds (by norm_num))
    have h4 : ∀ᶠ r : ℕ in atTop, s < 2 ^ (r - 1) :=
      Filter.eventually_atTop.mpr ⟨s + 2, fun r hr =>
        lt_trans (by omega : s < r - 1) Nat.lt_two_pow_self⟩
    have h5 : ∀ᶠ r : ℕ in atTop, Qmax < 2 ^ (r - 1) :=
      Filter.eventually_atTop.mpr ⟨Qmax + 2, fun r hr =>
        lt_trans (by omega : Qmax < r - 1) Nat.lt_two_pow_self⟩
    have h6 : ∀ᶠ r : ℕ in atTop,
        ((s : ℝ) + 4 * (s : ℝ) ^ 2) * (s : ℝ) ^ ε * (lam * (s : ℝ) ^ ε) ^ (r - 1) < 1 := by
      have ht : Tendsto (fun r : ℕ => ((s : ℝ) + 4 * (s : ℝ) ^ 2) * (s : ℝ) ^ ε * (lam * (s : ℝ) ^ ε) ^ (r - 1))
          atTop (nhds 0) := by
        simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hlam_sε_lt1).comp
          (tendsto_sub_atTop_nat 1)).const_mul (((s : ℝ) + 4 * (s : ℝ) ^ 2) * (s : ℝ) ^ ε)
      exact ht.eventually (gt_mem_nhds (by norm_num))
    exact h1.and (h2'.and (h3.and (h4.and (h5.and h6))))
  rw [Filter.eventually_atTop] at h_ev_r ⊢
  obtain ⟨R0, hR0⟩ := h_ev_r
  -- Choose N0 = max s (Nat.factorial (s - 1) * s ^ R0) + 1
  refine ⟨max s (Nat.factorial (s - 1) * s ^ R0) + 1, ?_⟩
  intro n hn
  by_contra hnot
  have hns : s < n := by omega
  obtain ⟨r, hr1, heq⟩ := h1 s n hs hns hnot
  have hdvd : n ∣ Nat.factorial (s - 1) * s ^ (r - 1) := smooth_and_bound_of_eq s n r hs hns hr1 heq
  have hpos_rhs : 0 < Nat.factorial (s - 1) * s ^ (r - 1) := by positivity
  have hn_le : n ≤ Nat.factorial (s - 1) * s ^ (r - 1) := Nat.le_of_dvd hpos_rhs hdvd
  -- Deduce R0 <= r
  have hr_ge : R0 ≤ r := by
    by_contra hlt
    have hrlt : r - 1 ≤ R0 := by omega
    have hpow_le : s ^ (r - 1) ≤ s ^ R0 := Nat.pow_le_pow_right (by omega) hrlt
    have hmul_le : Nat.factorial (s - 1) * s ^ (r - 1) ≤ Nat.factorial (s - 1) * s ^ R0 :=
      Nat.mul_le_mul_left _ hpow_le
    omega
  obtain ⟨_, hB, h23, hs2, hQ2, hlam_small⟩ := hR0 r hr_ge
  -- Apply localization_of_eq
  obtain ⟨j, hj1, hjs, hloc⟩ := localization_of_eq s n r hs hns hr1 heq hB
  let p_val : ℕ := n * j ^ (r - 1)
  let q_val : ℕ := (s - j) * (j + 1) ^ (r - 1)
  -- Check p_val = q_val via H2
  have hpq_eq : p_val = q_val := by
    by_contra hne
    have hp_pos : 0 < p_val := Nat.mul_pos (by omega) (pow_pos (by omega) _)
    have hq_pos : 0 < q_val := Nat.mul_pos (by omega) (pow_pos (by omega) _)
    have hp_smooth : ∀ p : ℕ, p.Prime → p ∣ p_val → p ≤ s := by
      intro p hp hdp
      rcases hp.dvd_mul.mp hdp with hdn | hdj
      · exact prime_le_of_dvd_fac_mul_pow s n r p (by omega) hp hdvd hdn
      · exact le_trans (Nat.le_of_dvd (by omega) (hp.dvd_of_dvd_pow hdj)) (by omega)
    have hq_smooth : ∀ p : ℕ, p.Prime → p ∣ q_val → p ≤ s := by
      intro p hp hdq
      rcases hp.dvd_mul.mp hdq with hdsj | hdj1
      · exact le_trans (Nat.le_of_dvd (by omega) hdsj) (by omega)
      · exact le_trans (Nat.le_of_dvd (by omega) (hp.dvd_of_dvd_pow hdj1)) (by omega)
    have hq_ge_j1 : ((j + 1 : ℕ) : ℝ) ^ (r - 1) ≤ (q_val : ℝ) := by
      dsimp [q_val]
      have h1 : (j + 1) ^ (r - 1) ≤ (s - j) * (j + 1) ^ (r - 1) :=
        Nat.le_mul_of_pos_left _ (by omega)
      exact_mod_cast h1
    have hq_le_sr : (q_val : ℝ) ≤ (s : ℝ) ^ r := by
      dsimp [q_val]
      have h1 : s - j ≤ s := by omega
      have h2 : j + 1 ≤ s := by omega
      have h3 : (s - j) * (j + 1) ^ (r - 1) ≤ s * s ^ (r - 1) :=
        Nat.mul_le_mul h1 (Nat.pow_le_pow_left h2 _)
      have h4 : s * s ^ (r - 1) = s ^ r := by
        have : r = (r - 1) + 1 := by omega
        conv_rhs => rw [this, pow_succ, mul_comm]
      exact_mod_cast (h4 ▸ h3)
    have hq_rpow_le : (q_val : ℝ) ^ ε ≤ (s : ℝ) ^ ε * ((s : ℝ) ^ ε) ^ (r - 1) := by
      have h1 : (q_val : ℝ) ^ ε ≤ ((s : ℝ) ^ r) ^ ε :=
        Real.rpow_le_rpow (by positivity) hq_le_sr (le_of_lt hε_pos)
      have h2 : ((s : ℝ) ^ r) ^ ε = ((s : ℝ) ^ ε) ^ r := by
        rw [← Real.rpow_natCast (s : ℝ) r, ← Real.rpow_mul (by positivity), mul_comm,
            Real.rpow_mul (by positivity), Real.rpow_natCast]
      have h3 : ((s : ℝ) ^ ε) ^ r = (s : ℝ) ^ ε * ((s : ℝ) ^ ε) ^ (r - 1) := by
        have : r = (r - 1) + 1 := by omega
        conv_lhs => rw [this, pow_succ, mul_comm]
      linarith
    have hdiff_lt : |(q_val : ℝ) - (p_val : ℝ)| < (q_val : ℝ) ^ (1 - ε) := by
      have hloc' : |(q_val : ℝ) - (p_val : ℝ)| ≤
          ((s : ℝ) + 4 * (s : ℝ) ^ 2) * lam ^ (r - 1) * (q_val : ℝ) := by
        rw [abs_sub_comm]
        have hp_cast : (p_val : ℝ) = (n : ℝ) * (j : ℝ) ^ (r - 1) := by dsimp [p_val]; push_cast; rfl
        have hq_cast : (q_val : ℝ) = ((s - j : ℕ) : ℝ) * ((j + 1 : ℕ) : ℝ) ^ (r - 1) := by
          dsimp [q_val]; push_cast; rfl
        rw [hp_cast, hq_cast]
        have hj_lam : (j : ℝ) ^ (r - 1) ≤ lam ^ (r - 1) * ((j + 1 : ℕ) : ℝ) ^ (r - 1) := by
          rw [← mul_pow]
          apply pow_le_pow_left₀ (by positivity)
          have hjj1 : (j : ℝ) / ((j + 1 : ℕ) : ℝ) ≤ lam := by
            refine le_trans ?_ (le_max_left _ _)
            have hspos : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
            have hj1pos : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < j + 1)
            rw [div_le_div_iff₀ hj1pos hspos]
            have h1 : j * s ≤ (s - 1) * (j + 1) := by
              cases s with
              | zero => omega
              | succ s' => simp only [Nat.add_sub_cancel]; nlinarith
            exact_mod_cast h1
          rwa [div_le_iff₀ (by positivity)] at hjj1
        have hinv_lam : 1 / γ ^ (r - 1) ≤ lam ^ (r - 1) := by
          rw [one_div, ← inv_pow]
          apply pow_le_pow_left₀ (by positivity)
          rw [← one_div]
          exact le_max_right _ _
        have h1 : (s : ℝ) * (j : ℝ) ^ (r - 1) ≤ (s : ℝ) * lam ^ (r - 1) * (q_val : ℝ) := by
          calc (s : ℝ) * (j : ℝ) ^ (r - 1)
              ≤ (s : ℝ) * (lam ^ (r - 1) * ((j + 1 : ℕ) : ℝ) ^ (r - 1)) :=
                mul_le_mul_of_nonneg_left hj_lam (by positivity)
            _ ≤ (s : ℝ) * (lam ^ (r - 1) * (q_val : ℝ)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq_ge_j1 (by positivity)) (by positivity)
            _ = (s : ℝ) * lam ^ (r - 1) * (q_val : ℝ) := by ring
        have h2 : (4 * (s : ℝ) ^ 2) / γ ^ (r - 1) * ((j + 1 : ℕ) : ℝ) ^ (r - 1) ≤
            (4 * (s : ℝ) ^ 2) * lam ^ (r - 1) * (q_val : ℝ) := by
          calc (4 * (s : ℝ) ^ 2) / γ ^ (r - 1) * ((j + 1 : ℕ) : ℝ) ^ (r - 1)
              = (4 * (s : ℝ) ^ 2) * (1 / γ ^ (r - 1)) * ((j + 1 : ℕ) : ℝ) ^ (r - 1) := by ring
            _ ≤ (4 * (s : ℝ) ^ 2) * lam ^ (r - 1) * (q_val : ℝ) := by
                have := mul_le_mul hinv_lam hq_ge_j1 (by positivity) (by positivity)
                have h4nn : 0 ≤ 4 * (s : ℝ) ^ 2 := by positivity
                nlinarith
        rw [← hq_cast] at hloc ⊢
        linarith
      have hqR_pos : (0 : ℝ) < (q_val : ℝ) := by exact_mod_cast hq_pos
      have hrpow_split : (q_val : ℝ) ^ (1 - ε) * (q_val : ℝ) ^ ε = (q_val : ℝ) := by
        rw [← Real.rpow_add hqR_pos, sub_add_cancel, Real.rpow_one]
      have hmul_lt : |(q_val : ℝ) - (p_val : ℝ)| * (q_val : ℝ) ^ ε < (q_val : ℝ) := by
        calc |(q_val : ℝ) - (p_val : ℝ)| * (q_val : ℝ) ^ ε
            ≤ (((s : ℝ) + 4 * (s : ℝ) ^ 2) * lam ^ (r - 1) * (q_val : ℝ)) *
                ((s : ℝ) ^ ε * ((s : ℝ) ^ ε) ^ (r - 1)) :=
              mul_le_mul hloc' hq_rpow_le (by positivity) (by positivity)
          _ = (((s : ℝ) + 4 * (s : ℝ) ^ 2) * (s : ℝ) ^ ε * (lam * (s : ℝ) ^ ε) ^ (r - 1)) * (q_val : ℝ) := by
              rw [mul_pow]; ring
          _ < 1 * (q_val : ℝ) := mul_lt_mul_of_pos_right hlam_small hqR_pos
          _ = (q_val : ℝ) := one_mul _
      have hqe_pos : 0 < (q_val : ℝ) ^ ε := Real.rpow_pos_of_pos hqR_pos ε
      nlinarith
    have hq_le_max : q_val ≤ Qmax :=
      hQmax (p_val, q_val) ⟨hp_pos, hq_pos, hp_smooth, hq_smooth, hne, hdiff_lt⟩
    have hq_gt_max : Qmax < q_val := by
      dsimp [q_val]
      have h1 : 1 ≤ s - j := by omega
      have h2 : 2 ≤ j + 1 := by omega
      have h3 : 2 ^ (r - 1) ≤ (j + 1) ^ (r - 1) := Nat.pow_le_pow_left h2 _
      have h4 : 2 ^ (r - 1) ≤ (s - j) * (j + 1) ^ (r - 1) := by
        calc 2 ^ (r - 1) = 1 * 2 ^ (r - 1) := (one_mul _).symm
          _ ≤ (s - j) * (j + 1) ^ (r - 1) := Nat.mul_le_mul h1 h3
      omega
    omega
  -- Now p_val = q_val, i.e. n * j^(r-1) = (s - j) * (j + 1)^(r-1)
  have hj_eq1 : j = 1 := by
    by_contra hjne1
    have hj2 : 2 ≤ j := by omega
    have hcop : Nat.Coprime (j ^ (r - 1)) ((j + 1) ^ (r - 1)) :=
      (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right j)).pow (r - 1) (r - 1)
    have hdvd_sj : j ^ (r - 1) ∣ s - j := by
      have hd : j ^ (r - 1) ∣ (s - j) * (j + 1) ^ (r - 1) := ⟨n, by dsimp [p_val, q_val] at hpq_eq; linarith⟩
      exact hcop.dvd_of_dvd_mul_right hd
    have hle_sj : j ^ (r - 1) ≤ s - j := Nat.le_of_dvd (by omega) hdvd_sj
    have hge_2 : 2 ^ (r - 1) ≤ j ^ (r - 1) := Nat.pow_le_pow_left hj2 _
    omega
  subst hj_eq1
  have hn_exact : n = (s - 1) * 2 ^ (r - 1) := by
    dsimp [p_val, q_val] at hpq_eq
    simpa using hpq_eq
  have h2s_le : 2 * s ≤ (s - 1) * 2 ^ (r - 1) := by
    have : 2 ≤ s - 1 := by omega
    calc 2 * s ≤ (s - 1) * s := Nat.mul_le_mul_right s this
      _ ≤ (s - 1) * 2 ^ (r - 1) := Nat.mul_le_mul_left (s - 1) (le_of_lt hs2)
  rw [hn_exact] at heq
  exact no_exact_solution_j1 s r hs hr1 h23 h2s_le heq

end OMA.R_Erdos494_erdos_494_variants_gordon_fraenkel_straus_R1
