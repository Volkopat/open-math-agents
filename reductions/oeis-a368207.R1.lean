import OMAStatements.S_oeis_a368207

/-!
Reduction for OEIS A368207, contributed by @rgoldman73-dev.
The conjectures are due to Pontus von Brömssen and Chai Wah Wu; the
registered statement was contributed by @pyaf. Context: Roland Bacher,
A Quixotic Proof of Fermat's Two Squares Theorem for Prime Numbers,
https://arxiv.org/abs/2210.07657 and https://oeis.org/A368207.

H1 is a proposed exact counting identity, not a proved formula. Its explicit
correction sums positive weights over middle divisors. A strict pair d < e
with d*e = n and e < 2*d contributes 4*(2*d-e); a square contributes
2*sqrt(n)-1, and a twice-square boundary contributes 1. The identity was
tested independently for n = 1 through 5000; those tests do not prove H1.

H2 isolates the classical divisor-count limit. All other work is proved
here: the correction vanishes precisely without middle divisors, its values
on every prime power give Wu's three formulas, and its bound by
8 * number-of-divisors * sqrt(n) gives the required limit from H2.
-/

namespace OMA.R_oeis_a368207_R1

open Finset Filter Topology ArithmeticFunction OMA.S_oeis_a368207

def H1 : Prop := ∀ n : ℕ, 0 < n →
  2 * a n = sigma 1 n +
    ∑ d ∈ n.divisors.filter (fun d => n ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * n),
      if d ^ 2 = n then 2 * d - 1
      else max 1 (2 * (2 * min d (n / d) - max d (n / d)))

def H2 : Prop :=
  Tendsto (fun n : ℕ => (n.divisors.card : ℝ) / Real.sqrt n) atTop (𝓝 0)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a368207.main := by
  intro h1 h2
  let middle (n : ℕ) : Finset ℕ :=
    n.divisors.filter fun d => n ≤ 2 * d ^ 2 ∧ d ^ 2 < 2 * n

  let weight (n d : ℕ) : ℕ :=
    if d ^ 2 = n then 2 * d - 1
    else max 1 (2 * (2 * min d (n / d) - max d (n / d)))

  let correction (n : ℕ) : ℕ := ∑ d ∈ middle n, weight n d

  have weight_pos {n d : ℕ} (hd : d ∈ n.divisors) : 0 < weight n d := by
    have hp := Nat.pos_of_mem_divisors hd
    unfold weight
    split_ifs <;> omega

  have correction_zero_iff (n : ℕ) : correction n = 0 ↔ ¬ HasMiddleDivisor n := by
    constructor
    · intro hz ⟨d, hd, h1, h2⟩
      have hm : d ∈ middle n := by simp [middle, hd, h1, h2]
      have hle := Finset.single_le_sum (fun i _ => Nat.zero_le (weight n i)) hm
      have hp := weight_pos hd
      change weight n d ≤ correction n at hle
      omega
    · intro hn
      have he : middle n = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro d hd
        simp only [middle, mem_filter] at hd
        exact hn ⟨d, hd.1, hd.2⟩
      simp [correction, he]

  have pow_eq_square (p k : ℕ) : p ^ (2 * k) = (p ^ k) ^ 2 := by
    rw [Nat.mul_comm 2 k, pow_mul]

  have pow_eq_square_mul (p k : ℕ) : p ^ (2 * k + 1) = (p ^ k) ^ 2 * p := by
    rw [pow_succ, pow_eq_square]

  have pow_gap {p i j : ℕ} (hp : 2 ≤ p) (hij : i < j) :
      2 * p ^ i ≤ p ^ j := by
    calc
      2 * p ^ i ≤ p * p ^ i := Nat.mul_le_mul_right _ hp
      _ = p ^ (i + 1) := by rw [pow_succ, Nat.mul_comm]
      _ ≤ p ^ j := Nat.pow_le_pow_right (by omega) hij

  have middle_even_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
      middle (p ^ (2 * k)) = {p ^ k} := by
    ext d
    simp only [middle, mem_filter, Nat.mem_divisors_prime_pow hp, mem_singleton]
    constructor
    · rintro ⟨⟨j, hj, rfl⟩, h1, h2⟩
      have hm : 0 < p ^ k := pow_pos hp.pos _
      have hd : 0 < p ^ j := pow_pos hp.pos _
      rw [pow_eq_square] at h1 h2
      rcases lt_trichotomy j k with h | rfl | h
      · have hgap := pow_gap hp.two_le h
        nlinarith
      · rfl
      · have hgap := pow_gap hp.two_le h
        nlinarith
    · rintro rfl
      have hm : 0 < p ^ k := pow_pos hp.pos _
      refine ⟨⟨k, by omega, rfl⟩, ?_, ?_⟩ <;> rw [pow_eq_square] <;> nlinarith

  have middle_odd_pow {p : ℕ} (hp : p.Prime) (h2 : 2 < p) (k : ℕ) :
      middle (p ^ (2 * k + 1)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro d hd
    simp only [middle, mem_filter, Nat.mem_divisors_prime_pow hp] at hd
    obtain ⟨⟨j, hj, rfl⟩, h1, h2'⟩ := hd
    rw [pow_eq_square_mul] at h1 h2'
    have hm : 0 < p ^ k := pow_pos hp.pos _
    have hp3 : 3 ≤ p := h2
    by_cases hjk : j ≤ k
    · have hle : p ^ j ≤ p ^ k := Nat.pow_le_pow_right hp.one_lt.le hjk
      have hs := Nat.pow_le_pow_left hle 2
      have hl := Nat.mul_le_mul_left ((p ^ k) ^ 2) hp3
      nlinarith
    · have hjk : k + 1 ≤ j := by omega
      have hle : p ^ k * p ≤ p ^ j := by
        simpa [pow_succ] using Nat.pow_le_pow_right hp.one_lt.le hjk
      have hs := Nat.pow_le_pow_left hle 2
      have hl := Nat.mul_le_mul_left ((p ^ k) ^ 2 * p) hp3
      nlinarith

  have middle_two_odd (k : ℕ) : middle (2 ^ (2 * k + 1)) = {2 ^ k} := by
    ext d
    simp only [middle, mem_filter, Nat.mem_divisors_prime_pow Nat.prime_two, mem_singleton]
    constructor
    · rintro ⟨⟨j, hj, rfl⟩, h1, h2⟩
      have hm : 0 < 2 ^ k := Nat.two_pow_pos _
      have hd : 0 < 2 ^ j := Nat.two_pow_pos _
      rw [pow_eq_square_mul] at h1 h2
      rcases lt_trichotomy j k with h | rfl | h
      · have hgap := pow_gap (by omega : 2 ≤ 2) h
        nlinarith
      · rfl
      · have hgap := pow_gap (by omega : 2 ≤ 2) h
        nlinarith
    · rintro rfl
      have hm : 0 < 2 ^ k := Nat.two_pow_pos _
      refine ⟨⟨k, by omega, rfl⟩, ?_, ?_⟩ <;> rw [pow_eq_square_mul] <;> nlinarith

  have correction_even_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
      correction (p ^ (2 * k)) = 2 * p ^ k - 1 := by
    simp only [correction]
    rw [middle_even_pow hp, Finset.sum_singleton]
    simp [weight, pow_eq_square]

  have correction_odd_pow {p : ℕ} (hp : p.Prime) (h2 : 2 < p) (k : ℕ) :
      correction (p ^ (2 * k + 1)) = 0 := by
    simp [correction, middle_odd_pow hp h2]

  have correction_two_odd (k : ℕ) : correction (2 ^ (2 * k + 1)) = 1 := by
    have hp : 0 < 2 ^ k := Nat.two_pow_pos _
    have hn : (2 ^ k) ^ 2 ≠ 2 ^ (2 * k + 1) := by
      rw [pow_eq_square_mul]
      nlinarith
    have hd : 2 ^ (2 * k + 1) / 2 ^ k = 2 * 2 ^ k := by
      rw [pow_eq_square_mul]
      have he : (2 ^ k) ^ 2 * 2 = (2 * 2 ^ k) * 2 ^ k := by ring
      rw [he, Nat.mul_div_left _ hp]
    have hle : 2 ^ k ≤ 2 * 2 ^ k := by omega
    simp [correction, middle_two_odd, weight, hn, hd, min_eq_left hle, max_eq_right hle]

  have weight_le {n d : ℕ} (hd : d ∈ n.divisors) : weight n d ≤ 4 * d := by
    have hp := Nat.pos_of_mem_divisors hd
    have hm := min_le_left d (n / d)
    unfold weight
    split_ifs <;> omega

  have correction_bound (n : ℕ) :
      (correction n : ℝ) ≤ 8 * (n.divisors.card : ℝ) * Real.sqrt n := by
    have each : ∀ d ∈ middle n, (weight n d : ℝ) ≤ 8 * Real.sqrt n := by
      intro d hd
      obtain ⟨hd, hlo, hhi⟩ := Finset.mem_filter.mp hd
      have hw : (weight n d : ℝ) ≤ 4 * (d : ℝ) := by exact_mod_cast weight_le hd
      have hsq : (d : ℝ) ^ 2 < 2 * (n : ℝ) := by exact_mod_cast hhi
      have hs := Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)
      have hp := Real.sqrt_nonneg (n : ℝ)
      have hd0 : 0 ≤ (d : ℝ) := by positivity
      nlinarith
    have hc : ((middle n).card : ℝ) ≤ (n.divisors.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    calc
      (correction n : ℝ) = ∑ d ∈ middle n, (weight n d : ℝ) := by simp [correction]
      _ ≤ ∑ _d ∈ middle n, 8 * Real.sqrt n := Finset.sum_le_sum each
      _ = (middle n).card * (8 * Real.sqrt n) := by simp
      _ ≤ (n.divisors.card : ℝ) * (8 * Real.sqrt n) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = 8 * (n.divisors.card : ℝ) * Real.sqrt n := by ring

  have self_le_sigma (n : ℕ) (hn : 0 < n) : n ≤ sigma 1 n := by
    rw [sigma_one_apply]
    exact Finset.single_le_sum (fun d _ => Nat.zero_le d)
      (Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩)

  have correction_ratio_bound {n : ℕ} (hn : 0 < n) :
      (correction n : ℝ) / (sigma 1 n : ℝ) ≤
        8 * ((n.divisors.card : ℝ) / Real.sqrt n) := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
    have hsig : (n : ℝ) ≤ (sigma 1 n : ℝ) := by exact_mod_cast self_le_sigma n hn
    calc
      (correction n : ℝ) / (sigma 1 n : ℝ) ≤ (correction n : ℝ) / n :=
        div_le_div_of_nonneg_left (by positivity) hnR hsig
      _ ≤ (8 * (n.divisors.card : ℝ) * Real.sqrt n) / n :=
        div_le_div_of_nonneg_right (correction_bound n) hnR.le
      _ = 8 * ((n.divisors.card : ℝ) / Real.sqrt n) := by
        rw [← mul_div_assoc]
        apply (div_eq_div_iff hnR.ne' hs.ne').mpr
        calc
          (8 * (n.divisors.card : ℝ) * Real.sqrt n) * Real.sqrt n =
              8 * (n.divisors.card : ℝ) * (Real.sqrt n) ^ 2 := by ring
          _ = 8 * (n.divisors.card : ℝ) * n := by rw [Real.sq_sqrt hnR.le]

  have conjecture_one (h : ∀ n : ℕ, 0 < n → 2 * a n = sigma 1 n + correction n) : Conj1 := by
    intro n hn
    have hc := h n (by omega)
    refine ⟨by omega, ?_⟩
    rw [← correction_zero_iff]
    omega

  have conjecture_wu (h : ∀ n : ℕ, 0 < n → 2 * a n = sigma 1 n + correction n) : ConjWu := by
    refine ⟨?_, ?_, ?_⟩
    · intro p m hp hp2 hm
      obtain ⟨k, rfl⟩ := hm
      have hc := h (p ^ (2 * k + 1)) (pow_pos hp.pos _)
      rw [correction_odd_pow hp hp2, Nat.add_zero] at hc
      exact hc
    · intro p m hp hm
      obtain ⟨k, rfl⟩ := hm
      have he : k + k = 2 * k := by omega
      rw [he]
      have hc := h (p ^ (2 * k)) (pow_pos hp.pos _)
      rw [correction_even_pow hp] at hc
      have hs := sigma_pos 1 (p ^ (2 * k)) (pow_ne_zero _ hp.ne_zero)
      have hk : 0 < p ^ k := pow_pos hp.pos _
      have hd : 2 * k / 2 = k := by omega
      rw [hd]
      omega
    · intro m hm
      obtain ⟨k, rfl⟩ := hm
      have hc := h (2 ^ (2 * k + 1)) (Nat.two_pow_pos _)
      rwa [correction_two_odd] at hc

  have correction_limit (h : H2) :
      Tendsto (fun n : ℕ => (correction n : ℝ) / (sigma 1 n : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun n => by positivity))
      (g := fun n : ℕ => 8 * ((n.divisors.card : ℝ) / Real.sqrt n))
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact correction_ratio_bound (by omega)
    · simpa using h.const_mul 8

  have conjecture_two (h1 : ∀ n : ℕ, 0 < n → 2 * a n = sigma 1 n + correction n) (h2 : H2) : Conj2 := by
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hl : Tendsto
        (fun n : ℕ => (1 + (correction n : ℝ) / (sigma 1 n : ℝ)) / 2)
        atTop (𝓝 (1 / 2)) := by
      simpa using (hconst.add (correction_limit h2)).div_const (2 : ℝ)
    apply hl.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hs : (sigma 1 n : ℝ) ≠ 0 := by
      exact_mod_cast (sigma_pos 1 n (by omega)).ne'
    have hc : 2 * (a n : ℝ) = (sigma 1 n : ℝ) + (correction n : ℝ) := by
      exact_mod_cast h1 n (by omega)
    field_simp
    linarith

  have hid : ∀ n : ℕ, 0 < n → 2 * a n = sigma 1 n + correction n := h1
  exact ⟨conjecture_one hid, conjecture_two hid h2, conjecture_wu hid⟩

end OMA.R_oeis_a368207_R1
