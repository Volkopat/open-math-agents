import OMAStatements.S_oeis_a363558
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace OeisA363558Proof

open OMA.S_oeis_a363558

private lemma hockey_stick (d : ℕ) :
    ∀ r : ℕ, ∑ s ∈ Finset.range (r + 1), Nat.choose (s + d) s = Nat.choose (r + d + 1) r := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    have h := Nat.choose_succ_succ (r + d + 1) r
    rw [show r + 1 + d + 1 = r + d + 2 by omega,
        show r + 1 + d = r + d + 1 by omega]
    linarith

private lemma coeff_posTerm (c : ℤ) (n N : ℕ) (hn : 1 ≤ n) :
    PowerSeries.coeff N (posTerm c n) =
      if n ∣ N ∧ 1 ≤ N / n ∧ N / n - 1 ≤ 2 * n then
        c ^ (2 * n - (N / n - 1)) * (Nat.choose (2 * n) (N / n - 1) : ℤ)
      else 0 := by
  unfold posTerm
  rw [add_comm (PowerSeries.C c) (PowerSeries.X ^ n), add_pow, Finset.mul_sum, map_sum]
  have hterm : ∀ k ∈ Finset.range (2 * n + 1),
      PowerSeries.coeff N (PowerSeries.X ^ n * ((PowerSeries.X ^ n) ^ k * PowerSeries.C c ^ (2 * n - k) * (((2 * n).choose k : ℕ) : PowerSeries ℤ))) =
      if N = n * (k + 1) then c ^ (2 * n - k) * ((2 * n).choose k : ℤ) else 0 := by
    intro k _
    have heq : PowerSeries.X ^ n * ((PowerSeries.X ^ n) ^ k * PowerSeries.C c ^ (2 * n - k) * (((2 * n).choose k : ℕ) : PowerSeries ℤ)) =
        PowerSeries.C (c ^ (2 * n - k) * ((2 * n).choose k : ℤ)) * PowerSeries.X ^ (n * (k + 1)) := by
      rw [← pow_mul, map_mul, map_pow, map_natCast, mul_add, mul_one, pow_add]
      ring
    rw [heq, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hterm]
  by_cases hcond : n ∣ N ∧ 1 ≤ N / n ∧ N / n - 1 ≤ 2 * n
  · rw [if_pos hcond]
    rcases hcond with ⟨hdvd, hq1, hq2⟩
    rw [Finset.sum_eq_single (N / n - 1)]
    · have hN : N = n * (N / n - 1 + 1) := by
        rw [Nat.sub_add_cancel hq1, Nat.mul_div_cancel' hdvd]
      rw [if_pos hN]
    · intro k _ hne
      rw [if_neg]
      intro hN
      have hdiv : N / n = k + 1 := by rw [hN, Nat.mul_div_cancel_left _ (by omega)]
      omega
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · rw [if_neg hcond]
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_range] at hk
    rw [if_neg]
    intro hN
    apply hcond
    have hdvd : n ∣ N := ⟨k + 1, hN⟩
    have hdiv : N / n = k + 1 := by rw [hN, Nat.mul_div_cancel_left _ (by omega)]
    exact ⟨hdvd, by omega, by omega⟩

private lemma coeff_invGeom_pow (c : ℤ) (j : ℕ) (hj : 1 ≤ j) :
    ∀ d m : ℕ, PowerSeries.coeff m ((invGeom c j) ^ (d + 1)) =
      if j ∣ m then (-c) ^ (m / j) * (Nat.choose (m / j + d) (m / j) : ℤ) else 0 := by
  intro d
  induction d with
  | zero =>
    intro m
    simp only [Nat.zero_add, pow_one, add_zero, Nat.choose_self, Nat.cast_one, mul_one]
    unfold invGeom
    rw [PowerSeries.coeff_mk]
  | succ d ih =>
    intro m
    rw [pow_succ, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i l => PowerSeries.coeff i ((invGeom c j) ^ (d + 1)) * PowerSeries.coeff l (invGeom c j))]
    by_cases hjm : j ∣ m
    · rw [if_pos hjm]
      have hsub :
          ∑ i ∈ Finset.range (m + 1),
            PowerSeries.coeff i ((invGeom c j) ^ (d + 1)) * PowerSeries.coeff (m - i) (invGeom c j) =
          ∑ i ∈ (Finset.range (m / j + 1)).image (fun s => j * s),
            PowerSeries.coeff i ((invGeom c j) ^ (d + 1)) * PowerSeries.coeff (m - i) (invGeom c j) := by
        symm
        apply Finset.sum_subset
        · intro i hi
          rcases Finset.mem_image.mp hi with ⟨s, hs, rfl⟩
          rw [Finset.mem_range] at hs ⊢
          have hm : j * (m / j) = m := Nat.mul_div_cancel' hjm
          have : j * s ≤ j * (m / j) := Nat.mul_le_mul_left j (by omega)
          omega
        · intro i hi hnot
          rw [Finset.mem_range] at hi
          by_cases hji : j ∣ i
          · exfalso; apply hnot
            rcases hji with ⟨s, rfl⟩
            refine Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr ?_, rfl⟩
            have hm : j * (m / j) = m := Nat.mul_div_cancel' hjm
            by_contra hlt
            have : j * (m / j + 1) ≤ j * s := Nat.mul_le_mul_left j (by omega)
            rw [mul_add, mul_one, hm] at this
            omega
          · rw [ih i, if_neg hji, zero_mul]
      rw [hsub, Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left (by omega) h)]
      have hterm : ∀ s ∈ Finset.range (m / j + 1),
          PowerSeries.coeff (j * s) ((invGeom c j) ^ (d + 1)) * PowerSeries.coeff (m - j * s) (invGeom c j) =
          (-c) ^ (m / j) * (Nat.choose (s + d) s : ℤ) := by
        intro s hs
        rw [Finset.mem_range] at hs
        have hm : j * (m / j) = m := Nat.mul_div_cancel' hjm
        have hsub_eq : m - j * s = j * (m / j - s) := by
          conv_lhs => rw [← hm]
          rw [← Nat.mul_sub_left_distrib]
        rw [ih (j * s), if_pos (dvd_mul_right j s), Nat.mul_div_cancel_left s (by omega)]
        unfold invGeom
        rw [PowerSeries.coeff_mk, hsub_eq, if_pos (dvd_mul_right j _), Nat.mul_div_cancel_left _ (by omega)]
        rw [show (-c) ^ s * (Nat.choose (s + d) s : ℤ) * (-c) ^ (m / j - s) =
            ((-c) ^ s * (-c) ^ (m / j - s)) * (Nat.choose (s + d) s : ℤ) by ring,
          ← pow_add, show s + (m / j - s) = m / j by omega]
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Nat.cast_sum, hockey_stick d (m / j),
        show m / j + d + 1 = m / j + (d + 1) by omega]
    · rw [if_neg hjm]
      apply Finset.sum_eq_zero
      intro i hi
      rw [Finset.mem_range] at hi
      by_cases hji : j ∣ i
      · have hnd : ¬ (j ∣ m - i) := by
          intro h; apply hjm
          have : i + (m - i) = m := by omega
          rw [← this]; exact dvd_add hji h
        unfold invGeom
        rw [PowerSeries.coeff_mk, if_neg hnd, mul_zero]
      · rw [ih i, if_neg hji, zero_mul]

private lemma coeff_negTerm (c : ℤ) (j N : ℕ) (hj : 1 ≤ j) :
    PowerSeries.coeff N (negTerm c j) =
      if j ∣ N ∧ 2 * j - 1 ≤ N / j then
        (-c) ^ (N / j - (2 * j - 1)) * (Nat.choose (N / j) (2 * j - 1) : ℤ)
      else 0 := by
  unfold negTerm
  rw [PowerSeries.coeff_X_pow_mul']
  have hdeg : 2 * j ^ 2 - j = j * (2 * j - 1) := by
    have : 2 * j ^ 2 = j * (2 * j) := by ring
    rw [this, Nat.mul_sub_left_distrib, mul_one]
  rw [hdeg]
  by_cases hcond : j ∣ N ∧ 2 * j - 1 ≤ N / j
  · rcases hcond with ⟨hdvd, hle⟩
    have hNge : j * (2 * j - 1) ≤ N := by
      have hm : j * (N / j) = N := Nat.mul_div_cancel' hdvd
      rw [← hm]; exact Nat.mul_le_mul_left j hle
    rw [if_pos hNge, if_pos ⟨hdvd, hle⟩]
    conv_lhs => arg 2; rw [show 2 * j = (2 * j - 1) + 1 by omega]
    rw [coeff_invGeom_pow c j hj (2 * j - 1)]
    have hsub : N - j * (2 * j - 1) = j * (N / j - (2 * j - 1)) := by
      have hm : j * (N / j) = N := Nat.mul_div_cancel' hdvd
      conv_lhs => rw [← hm]
      rw [← Nat.mul_sub_left_distrib]
    rw [hsub, if_pos (dvd_mul_right j _), Nat.mul_div_cancel_left _ (by omega)]
    rw [show N / j - (2 * j - 1) + (2 * j - 1) = N / j by omega,
      Nat.choose_symm hle]
  · rw [if_neg hcond]
    by_cases hle : j * (2 * j - 1) ≤ N
    · rw [if_pos hle]
      conv_lhs => arg 2; rw [show 2 * j = (2 * j - 1) + 1 by omega]
      rw [coeff_invGeom_pow c j hj (2 * j - 1)]
      have hnd : ¬ (j ∣ N - j * (2 * j - 1)) := by
        intro h
        apply hcond
        have hdvd : j ∣ N := by
          have : N = j * (2 * j - 1) + (N - j * (2 * j - 1)) := by omega
          rw [this]; exact dvd_add (dvd_mul_right j _) h
        have hm : j * (N / j) = N := Nat.mul_div_cancel' hdvd
        have hq : 2 * j - 1 ≤ N / j := by
          by_contra hlt
          have : j * (N / j + 1) ≤ j * (2 * j - 1) := Nat.mul_le_mul_left j (by omega)
          rw [mul_add, mul_one, hm] at this
          omega
        exact ⟨hdvd, hq⟩
      rw [if_neg hnd]
    · rw [if_neg hle]

private lemma coeff_bilateral_prime (c : ℤ) (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    PowerSeries.coeff p
      (PowerSeries.mk fun N =>
        (if N = 0 then (1 : ℤ) else 0) +
          ∑ n ∈ Finset.Icc 1 N, (PowerSeries.coeff N (posTerm c n) + PowerSeries.coeff N (negTerm c n))) =
    (p : ℤ) * (c ^ 2) ^ ((p - 1) / 2) + (c ^ 2) ^ p := by
  rw [PowerSeries.coeff_mk, if_neg (by omega), zero_add, Finset.sum_add_distrib]
  have hpos : ∑ n ∈ Finset.Icc 1 p, PowerSeries.coeff p (posTerm c n) = (c ^ 2) ^ p := by
    rw [Finset.sum_eq_single p]
    · rw [coeff_posTerm c p p (by omega), if_pos ⟨dvd_refl p, by simp [Nat.div_self (by omega : 0 < p)], by simp [Nat.div_self (by omega : 0 < p)]⟩]
      simp [Nat.div_self (by omega : 0 < p), pow_mul]
    · intro n hn hne
      rw [Finset.mem_Icc] at hn
      rw [coeff_posTerm c n p hn.1, if_neg]
      rintro ⟨hdvd, _, hle⟩
      rcases (Nat.dvd_prime hp).mp hdvd with h1 | h2
      · rw [h1] at hle; simp at hle; omega
      · exact hne h2
    · intro h; exact absurd (Finset.mem_Icc.mpr ⟨by omega, le_refl p⟩) h
  have hneg : ∑ j ∈ Finset.Icc 1 p, PowerSeries.coeff p (negTerm c j) =
      (p : ℤ) * (c ^ 2) ^ ((p - 1) / 2) := by
    rw [Finset.sum_eq_single 1]
    · rw [coeff_negTerm c 1 p (le_refl 1), if_pos ⟨one_dvd p, by simp; omega⟩]
      simp only [Nat.div_one, show 2 * 1 - 1 = 1 by decide, Nat.choose_one_right]
      have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
      have hpow : (-c) ^ (p - 1) = (c ^ 2) ^ ((p - 1) / 2) := by
        conv_lhs => rw [show p - 1 = 2 * ((p - 1) / 2) by omega, pow_mul, neg_sq]
      rw [hpow, mul_comm]
    · intro j hj hne
      rw [Finset.mem_Icc] at hj
      rw [coeff_negTerm c j p hj.1, if_neg]
      rintro ⟨hdvd, hle⟩
      rcases (Nat.dvd_prime hp).mp hdvd with h1 | h2
      · exact hne h1
      · rw [h2, Nat.div_self (by omega : 0 < p)] at hle; omega
    · intro h; exact absurd (Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩) h
  rw [hpos, hneg, add_comm]

private lemma coeff_bilateral_pow2 (c : ℤ) (m : ℕ) (hm : 0 < m) :
    PowerSeries.coeff (2 ^ m)
      (PowerSeries.mk fun N =>
        (if N = 0 then (1 : ℤ) else 0) +
          ∑ n ∈ Finset.Icc 1 N, (PowerSeries.coeff N (posTerm c n) + PowerSeries.coeff N (negTerm c n))) =
    (c ^ 2) ^ (2 ^ m) := by
  have h2m_pos : 0 < 2 ^ m := Nat.pos_of_ne_zero (by positivity)
  rw [PowerSeries.coeff_mk, if_neg (by omega), zero_add, Finset.sum_add_distrib]
  have hpos_img :
      ∑ n ∈ Finset.Icc 1 (2 ^ m), PowerSeries.coeff (2 ^ m) (posTerm c n) =
      ∑ a ∈ Finset.range (m + 1), PowerSeries.coeff (2 ^ m) (posTerm c (2 ^ a)) := by
    have hsub :
        ∑ n ∈ Finset.Icc 1 (2 ^ m), PowerSeries.coeff (2 ^ m) (posTerm c n) =
        ∑ n ∈ (Finset.range (m + 1)).image (fun a => 2 ^ a), PowerSeries.coeff (2 ^ m) (posTerm c n) := by
      symm
      apply Finset.sum_subset
      · intro n hn
        rcases Finset.mem_image.mp hn with ⟨a, ha, rfl⟩
        rw [Finset.mem_range] at ha
        exact Finset.mem_Icc.mpr ⟨Nat.one_le_pow a 2 (by decide), Nat.pow_le_pow_right (by decide) (by omega)⟩
      · intro n hn hnot
        rw [Finset.mem_Icc] at hn
        rw [coeff_posTerm c n (2 ^ m) hn.1, if_neg]
        rintro ⟨hdvd, _, _⟩
        rcases (Nat.dvd_prime_pow Nat.prime_two).mp hdvd with ⟨a, hale, rfl⟩
        exact hnot (Finset.mem_image.mpr ⟨a, Finset.mem_range.mpr (by omega), rfl⟩)
    rw [hsub, Finset.sum_image (fun a _ b _ h => Nat.pow_right_injective (by decide : 2 ≤ 2) h)]
  have hneg_img :
      ∑ j ∈ Finset.Icc 1 (2 ^ m), PowerSeries.coeff (2 ^ m) (negTerm c j) =
      ∑ u ∈ Finset.range (m + 1), PowerSeries.coeff (2 ^ m) (negTerm c (2 ^ u)) := by
    have hsub :
        ∑ j ∈ Finset.Icc 1 (2 ^ m), PowerSeries.coeff (2 ^ m) (negTerm c j) =
        ∑ j ∈ (Finset.range (m + 1)).image (fun u => 2 ^ u), PowerSeries.coeff (2 ^ m) (negTerm c j) := by
      symm
      apply Finset.sum_subset
      · intro j hj
        rcases Finset.mem_image.mp hj with ⟨u, hu, rfl⟩
        rw [Finset.mem_range] at hu
        exact Finset.mem_Icc.mpr ⟨Nat.one_le_pow u 2 (by decide), Nat.pow_le_pow_right (by decide) (by omega)⟩
      · intro j hj hnot
        rw [Finset.mem_Icc] at hj
        rw [coeff_negTerm c j (2 ^ m) hj.1, if_neg]
        rintro ⟨hdvd, _⟩
        rcases (Nat.dvd_prime_pow Nat.prime_two).mp hdvd with ⟨u, hule, rfl⟩
        exact hnot (Finset.mem_image.mpr ⟨u, Finset.mem_range.mpr (by omega), rfl⟩)
    rw [hsub, Finset.sum_image (fun a _ b _ h => Nat.pow_right_injective (by decide : 2 ≤ 2) h)]
  rw [hpos_img, hneg_img, Finset.sum_range_succ, Finset.sum_range_succ]
  have htop_pos : PowerSeries.coeff (2 ^ m) (posTerm c (2 ^ m)) = (c ^ 2) ^ (2 ^ m) := by
    rw [coeff_posTerm c (2 ^ m) (2 ^ m) (by omega),
      if_pos ⟨dvd_refl _, by simp [Nat.div_self h2m_pos], by simp [Nat.div_self h2m_pos]⟩]
    simp [Nat.div_self h2m_pos, pow_mul]
  have htop_neg : PowerSeries.coeff (2 ^ m) (negTerm c (2 ^ m)) = 0 := by
    rw [coeff_negTerm c (2 ^ m) (2 ^ m) (by omega), if_neg]
    rintro ⟨_, hle⟩
    rw [Nat.div_self h2m_pos] at hle
    have h2 : 2 ≤ 2 ^ m := le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by decide) hm)
    omega
  rw [htop_pos, htop_neg, add_zero]
  have hcancel :
      ∑ a ∈ Finset.range m, PowerSeries.coeff (2 ^ m) (posTerm c (2 ^ a)) +
      ∑ u ∈ Finset.range m, PowerSeries.coeff (2 ^ m) (negTerm c (2 ^ u)) = 0 := by
    rw [← Finset.sum_range_reflect (fun u => PowerSeries.coeff (2 ^ m) (negTerm c (2 ^ u))) m,
      ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro a ha
    rw [Finset.mem_range] at ha
    set u := m - 1 - a
    have ha1 : a + 1 = m - u := by omega
    have hu1 : u + 1 = m - a := by omega
    have hdvd_a : 2 ^ a ∣ 2 ^ m := Nat.pow_dvd_pow 2 (by omega)
    have hdvd_u : 2 ^ u ∣ 2 ^ m := Nat.pow_dvd_pow 2 (by omega)
    have hdiv_a : 2 ^ m / 2 ^ a = 2 ^ (m - a) := by
      conv_lhs => rw [show m = a + (m - a) by omega, pow_add]
      rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (by positivity))]
    have hdiv_u : 2 ^ m / 2 ^ u = 2 ^ (m - u) := by
      conv_lhs => rw [show m = u + (m - u) by omega, pow_add]
      rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (by positivity))]
    rw [coeff_posTerm c (2 ^ a) (2 ^ m) (Nat.one_le_pow a 2 (by decide)),
      coeff_negTerm c (2 ^ u) (2 ^ m) (Nat.one_le_pow u 2 (by decide)),
      hdiv_a, hdiv_u]
    have h2a_eq : 2 * 2 ^ a = 2 ^ (m - u) := by rw [← pow_succ', ha1]
    have h2u_eq : 2 * 2 ^ u = 2 ^ (m - a) := by rw [← pow_succ', hu1]
    have hpos_ge1 : 1 ≤ 2 ^ (m - a) := Nat.one_le_pow _ 2 (by decide)
    rw [h2a_eq, h2u_eq]
    by_cases hle : 2 ^ (m - a) - 1 ≤ 2 ^ (m - u)
    · rw [if_pos ⟨hdvd_a, hpos_ge1, hle⟩, if_pos ⟨hdvd_u, hle⟩]
      have hodd : Odd (2 ^ (m - u) - (2 ^ (m - a) - 1)) := by
        have hmu_ge1 : 1 ≤ m - u := by omega
        have hma_ge1 : 1 ≤ m - a := by omega
        have he1 : 2 ∣ 2 ^ (m - u) := dvd_pow_self 2 (by omega)
        have he2 : 2 ∣ 2 ^ (m - a) := dvd_pow_self 2 (by omega)
        rcases he1 with ⟨q1, hq1⟩
        rcases he2 with ⟨q2, hq2⟩
        have hq2_pos : 1 ≤ q2 := by
          have : 1 ≤ 2 ^ (m - a) := hpos_ge1; omega
        refine ⟨q1 - q2, ?_⟩
        omega
      rw [neg_eq_neg_one_mul c, mul_pow, hodd.neg_one_pow]
      ring
    · rw [if_neg (by tauto), if_neg (by tauto), add_zero]
  calc ∑ a ∈ Finset.range m, PowerSeries.coeff (2 ^ m) (posTerm c (2 ^ a)) + (c ^ 2) ^ (2 ^ m) +
        ∑ u ∈ Finset.range m, PowerSeries.coeff (2 ^ m) (negTerm c (2 ^ u))
      = (∑ a ∈ Finset.range m, PowerSeries.coeff (2 ^ m) (posTerm c (2 ^ a)) +
          ∑ u ∈ Finset.range m, PowerSeries.coeff (2 ^ m) (negTerm c (2 ^ u))) + (c ^ 2) ^ (2 ^ m) := by ring
    _ = (c ^ 2) ^ (2 ^ m) := by rw [hcancel, zero_add]

private lemma prove_main :
    (∀ m : ℕ, 0 < m → PowerSeries.coeff (2 ^ m) A = (4 : ℤ) ^ (2 ^ m)) ∧
    (∀ p : ℕ, Nat.Prime p → 3 < p → PowerSeries.coeff p A = (p : ℤ) * (2 : ℤ) ^ (p - 1) + (4 : ℤ) ^ p) := by
  constructor
  · intro m hm
    have h : PowerSeries.coeff (2 ^ m) A = ((2 : ℤ) ^ 2) ^ (2 ^ m) := by
      simpa [A] using coeff_bilateral_pow2 (2 : ℤ) m hm
    rw [h]; norm_num
  · intro p hp hp3
    have h : PowerSeries.coeff p A = (p : ℤ) * ((2 : ℤ) ^ 2) ^ ((p - 1) / 2) + ((2 : ℤ) ^ 2) ^ p := by
      simpa [A] using coeff_bilateral_prime (2 : ℤ) p hp hp3
    rw [h]
    have hodd : p % 2 = 1 := by
      have hp2 : p ≠ 2 := by omega
      exact Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    have hpow : ((2 : ℤ) ^ 2) ^ ((p - 1) / 2) = (2 : ℤ) ^ (p - 1) := by
      rw [← pow_mul, show 2 * ((p - 1) / 2) = p - 1 by omega]
    rw [hpow]; norm_num

end OeisA363558Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a363558.main :=
  OeisA363558Proof.prove_main
