import OMAStatements.S_oeis_a336305
import Mathlib

open OMA.S_oeis_a336305

private lemma tri_odd (i : ℕ) : (2 * i + 1) * (2 * i + 1 + 1) / 2 = (2 * i + 1) * (i + 1) := by
  rw [show (2 * i + 1) * (2 * i + 1 + 1) = 2 * ((2 * i + 1) * (i + 1)) by ring]
  omega

private lemma tri_even (j : ℕ) : 2 * j * (2 * j + 1) / 2 = j * (2 * j + 1) := by
  rw [show 2 * j * (2 * j + 1) = 2 * (j * (2 * j + 1)) by ring]
  omega

/-- odd k: T n k ≠ 0 iff k ∣ n ∧ k*k < 2n, and then 2 T = 2n/k - k + 1. -/
private lemma T_odd (n i : ℕ) :
    (T n (2 * i + 1) ≠ 0 ↔ (2 * i + 1) ∣ n ∧ (2 * i + 1) * (2 * i + 1) < 2 * n) ∧
    ((2 * i + 1) ∣ n → (2 * i + 1) * (2 * i + 1) < 2 * n →
      2 * T n (2 * i + 1) = 2 * n / (2 * i + 1) - (2 * i + 1) + 1) := by
  unfold T
  rw [tri_odd]
  set k := 2 * i + 1 with hk
  have kpos : 0 < k := by omega
  constructor
  · constructor
    · intro h
      have hv : k * (i + 1) ≤ n ∧ k ∣ n - k * (i + 1) := by
        by_contra hc; exact h (if_neg hc)
      have hd : k ∣ n := by
        have := Nat.dvd_add hv.2 (Dvd.intro (i + 1) rfl)
        rwa [Nat.sub_add_cancel hv.1] at this
      obtain ⟨q, rfl⟩ := hd
      refine ⟨⟨q, rfl⟩, ?_⟩
      have := (Nat.mul_le_mul_left_iff kpos).1 hv.1
      have : k < 2 * q := by omega
      nlinarith
    · rintro ⟨⟨q, rfl⟩, h2⟩
      have hq : i + 1 ≤ q := by
        by_contra hc
        have : q ≤ i := by omega
        have : k * q ≤ k * i := Nat.mul_le_mul_left k this
        nlinarith
      rw [if_pos ⟨Nat.mul_le_mul_left k hq, by rw [← Nat.mul_sub]; exact Dvd.intro _ rfl⟩]
      exact Nat.succ_ne_zero _
  · rintro ⟨q, rfl⟩ h2
    have hq : i + 1 ≤ q := by
      by_contra hc
      have : q ≤ i := by omega
      have : k * q ≤ k * i := Nat.mul_le_mul_left k this
      nlinarith
    rw [if_pos ⟨Nat.mul_le_mul_left k hq, by rw [← Nat.mul_sub]; exact Dvd.intro _ rfl⟩,
      ← Nat.mul_sub, Nat.mul_div_cancel_left _ kpos, show 2 * (k * q) = k * (2 * q) by ring,
      Nat.mul_div_cancel_left _ kpos]
    omega

/-- even k = 2j: T n k ≠ 0 iff n = j d with d odd and 2j < d; then 2 T = d - 2j + 1. -/
private lemma T_even (n j : ℕ) (hj : 0 < j) :
    (T n (2 * j) ≠ 0 ↔ ∃ d, n = j * d ∧ d % 2 = 1 ∧ 2 * j < d) ∧
    (∀ d, n = j * d → d % 2 = 1 → 2 * j < d → 2 * T n (2 * j) = d - 2 * j + 1) := by
  unfold T
  rw [show 2 * j + 1 = 2 * j + 1 from rfl, tri_even]
  have key : ∀ d, n = j * d → d % 2 = 1 → 2 * j < d →
      j * (2 * j + 1) ≤ n ∧ n - j * (2 * j + 1) = 2 * j * ((d - 2 * j - 1) / 2) := by
    rintro d rfl hd h2
    refine ⟨Nat.mul_le_mul_left j (by omega), ?_⟩
    rw [← Nat.mul_sub, show 2 * j * ((d - 2 * j - 1) / 2) = j * (2 * ((d - 2 * j - 1) / 2)) by ring]
    congr 1; omega
  constructor
  · constructor
    · intro h
      have hv : j * (2 * j + 1) ≤ n ∧ 2 * j ∣ n - j * (2 * j + 1) := by
        by_contra hc; exact h (if_neg hc)
      obtain ⟨s, hs⟩ := hv.2
      refine ⟨2 * s + 2 * j + 1, ?_, by omega, by omega⟩
      have : n = (n - j * (2 * j + 1)) + j * (2 * j + 1) := by omega
      rw [this, hs]; ring
    · rintro ⟨d, hd, hodd, h2⟩
      obtain ⟨h1, h3⟩ := key d hd hodd h2
      rw [if_pos ⟨h1, by rw [h3]; exact Dvd.intro _ rfl⟩]
      exact Nat.succ_ne_zero _
  · intro d hd hodd h2
    obtain ⟨h1, h3⟩ := key d hd hodd h2
    rw [if_pos ⟨h1, by rw [h3]; exact Dvd.intro _ rfl⟩, h3, Nat.mul_div_cancel_left _ (by omega)]
    omega

private lemma negpow (k : ℕ) (hk : 1 ≤ k) : ((-1 : ℤ) ^ (k - 1)) = if k % 2 = 1 then 1 else -1 := by
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [show 2 * (i + 1) - 1 = 2 * i + 1 by omega, pow_succ, pow_mul]; simp
  · rw [show 2 * j + 1 - 1 = 2 * j by omega, pow_mul]; simp

private lemma odd_dvd (n e m c : ℕ) (hn : n = 2 ^ e * m) (hc : c % 2 = 1) : c ∣ n ↔ c ∣ m := by
  constructor
  · intro h
    have hcop : Nat.Coprime c (2 ^ e) := Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr (by
      rw [Nat.odd_iff]; exact hc))
    rw [hn] at h
    exact hcop.dvd_of_dvd_mul_left h
  · intro h; rw [hn]; exact Dvd.dvd.mul_left h _

private def G (n c : ℕ) : ℤ :=
  if c * c < 2 * n then ((2 * n / c : ℕ) : ℤ) - c + 1 else ((2 * n / c : ℕ) : ℤ) - c - 1

private lemma partC (n e m : ℕ) (hn : n = 2 ^ e * m) (hm : m % 2 = 1) (hn1 : 1 ≤ n) :
    2 * a n = ∑ c ∈ m.divisors, G n c := by
  have hm0 : m ≠ 0 := by omega
  unfold a
  rw [Finset.mul_sum]
  -- facts about nonzero terms
  have nz : ∀ k ∈ Finset.Icc 1 n, 2 * ((-1 : ℤ) ^ (k - 1) * (T n k : ℤ)) ≠ 0 → T n k ≠ 0 := by
    intro k _ h hT; rw [hT] at h; simp at h
  refine Finset.sum_bij_ne_zero (fun k _ _ => if k % 2 = 1 then k else 2 * n / k) ?_ ?_ ?_ ?_
  · intro k hk hne
    have hT := nz k hk hne
    simp only [Finset.mem_Icc] at hk
    split_ifs with hp
    · obtain ⟨i, rfl⟩ : ∃ i, k = 2 * i + 1 := ⟨k / 2, by omega⟩
      have := ((T_odd n i).1.1 hT).1
      rw [Nat.mem_divisors]; exact ⟨(odd_dvd n e m _ hn hp).1 this, hm0⟩
    · obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
      obtain ⟨d, hd, hodd, _⟩ := (T_even n j (by omega)).1.1 hT
      rw [show 2 * n / (2 * j) = d by rw [hd, show 2 * (j * d) = 2 * j * d by ring,
        Nat.mul_div_cancel_left _ (by omega)]]
      rw [Nat.mem_divisors]
      exact ⟨(odd_dvd n e m _ hn hodd).1 ⟨j, by rw [hd]; ring⟩, hm0⟩
  · intro k1 hk1 hne1 k2 hk2 hne2 heq
    have hT1 := nz k1 hk1 hne1
    have hT2 := nz k2 hk2 hne2
    simp only [Finset.mem_Icc] at hk1 hk2
    by_cases p1 : k1 % 2 = 1 <;> by_cases p2 : k2 % 2 = 1 <;> simp only [p1, p2, if_true, if_false] at heq
    · exact heq
    · exfalso
      obtain ⟨i, rfl⟩ : ∃ i, k1 = 2 * i + 1 := ⟨k1 / 2, by omega⟩
      obtain ⟨j, rfl⟩ : ∃ j, k2 = 2 * j := ⟨k2 / 2, by omega⟩
      have h1 := ((T_odd n i).1.1 hT1).2
      obtain ⟨d, hd, hodd, h2⟩ := (T_even n j (by omega)).1.1 hT2
      rw [show 2 * n / (2 * j) = d by rw [hd, show 2 * (j * d) = 2 * j * d by ring,
        Nat.mul_div_cancel_left _ (by omega)]] at heq
      rw [heq, hd] at h1
      nlinarith
    · exfalso
      obtain ⟨i, rfl⟩ : ∃ i, k2 = 2 * i + 1 := ⟨k2 / 2, by omega⟩
      obtain ⟨j, rfl⟩ : ∃ j, k1 = 2 * j := ⟨k1 / 2, by omega⟩
      have h1 := ((T_odd n i).1.1 hT2).2
      obtain ⟨d, hd, hodd, h2⟩ := (T_even n j (by omega)).1.1 hT1
      rw [show 2 * n / (2 * j) = d by rw [hd, show 2 * (j * d) = 2 * j * d by ring,
        Nat.mul_div_cancel_left _ (by omega)]] at heq
      rw [← heq, hd] at h1
      nlinarith
    · obtain ⟨j1, rfl⟩ : ∃ j, k1 = 2 * j := ⟨k1 / 2, by omega⟩
      obtain ⟨j2, rfl⟩ : ∃ j, k2 = 2 * j := ⟨k2 / 2, by omega⟩
      obtain ⟨d1, hd1, -, -⟩ := (T_even n j1 (by omega)).1.1 hT1
      obtain ⟨d2, hd2, -, -⟩ := (T_even n j2 (by omega)).1.1 hT2
      rw [show 2 * n / (2 * j1) = d1 by rw [hd1, show 2 * (j1 * d1) = 2 * j1 * d1 by ring,
        Nat.mul_div_cancel_left _ (by omega)],
        show 2 * n / (2 * j2) = d2 by rw [hd2, show 2 * (j2 * d2) = 2 * j2 * d2 by ring,
        Nat.mul_div_cancel_left _ (by omega)]] at heq
      subst heq
      have hdpos : 0 < d1 := by rcases Nat.eq_zero_or_pos d1 with h | h <;> [simp [h] at hd1; exact h] <;> omega
      have : j1 = j2 := by
        have := hd1.symm.trans hd2
        exact Nat.eq_of_mul_eq_mul_right hdpos this
      rw [this]
  · intro c hc _
    rw [Nat.mem_divisors] at hc
    have hcodd : c % 2 = 1 := by
      obtain ⟨q, hq⟩ := hc.1
      rcases Nat.mod_two_eq_zero_or_one c with h | h
      · exfalso; rw [hq] at hm; rw [Nat.mul_mod, h] at hm; simp at hm
      · exact h
    have hcn : c ∣ n := (odd_dvd n e m c hn hcodd).2 hc.1
    obtain ⟨q, hq⟩ := hcn
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · rw [h] at hq; omega
      · exact h
    have hqpos : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · rw [h] at hq; omega
      · exact h
    by_cases hsq : c * c < 2 * n
    · obtain ⟨i, rfl⟩ : ∃ i, c = 2 * i + 1 := ⟨c / 2, by omega⟩
      have hT : T n (2 * i + 1) ≠ 0 := (T_odd n i).1.2 ⟨⟨q, hq⟩, hsq⟩
      refine ⟨2 * i + 1, ?_, ?_, ?_⟩
      · rw [Finset.mem_Icc]; refine ⟨by omega, ?_⟩
        rw [hq]; nlinarith
      · intro h0; apply hT; rcases (mul_eq_zero.1 h0) with h | h
        · norm_num at h
        · simpa using h
      · simp only [hcodd, if_true]
    · have hgt : 2 * q < c := by
        by_contra hc'
        have : c ≤ 2 * q := by omega
        have h3 : c * c ≤ c * (2 * q) := Nat.mul_le_mul_left c this
        rw [hq] at hsq
        have h5 : c * (2 * q) = 2 * (c * q) := by ring
        have h4 : c * c = c * (2 * q) := by omega
        have := Nat.eq_of_mul_eq_mul_left hcpos h4
        omega
      have hT : T n (2 * q) ≠ 0 := (T_even n q hqpos).1.2 ⟨c, by rw [hq]; ring, hcodd, hgt⟩
      refine ⟨2 * q, ?_, ?_, ?_⟩
      · rw [Finset.mem_Icc]; refine ⟨by omega, ?_⟩
        rw [hq]; nlinarith
      · intro h0; apply hT; rcases (mul_eq_zero.1 h0) with h | h
        · norm_num at h
        · simpa using h
      · rw [if_neg (show ¬ (2 * q % 2 = 1) by omega)]
        rw [hq, show 2 * (c * q) = 2 * q * c by ring, Nat.mul_div_cancel_left _ (by omega)]
  · intro k hk hne
    have hT := nz k hk hne
    simp only [Finset.mem_Icc] at hk
    rw [negpow k hk.1]
    by_cases hp : k % 2 = 1
    · simp only [hp, if_true, one_mul]
      obtain ⟨i, rfl⟩ : ∃ i, k = 2 * i + 1 := ⟨k / 2, by omega⟩
      obtain ⟨hd, hsq⟩ := (T_odd n i).1.1 hT
      have h2 := (T_odd n i).2 hd hsq
      obtain ⟨q, hq⟩ := hd
      have hdiv : 2 * n / (2 * i + 1) = 2 * q := by
        rw [hq, show 2 * ((2 * i + 1) * q) = (2 * i + 1) * (2 * q) by ring,
          Nat.mul_div_cancel_left _ (by omega)]
      have hlt : 2 * i + 1 < 2 * q := by
        rw [hq] at hsq
        by_contra hc; have : 2 * q ≤ 2 * i + 1 := by omega
        have := Nat.mul_le_mul_left (2 * i + 1) this; nlinarith
      unfold G
      rw [if_pos hsq, hdiv]
      rw [hdiv] at h2
      have : (2 * (T n (2 * i + 1)) : ℤ) = ((2 * q - (2 * i + 1) + 1 : ℕ) : ℤ) := by exact_mod_cast h2
      rw [this]; push_cast [Nat.sub_add_comm hlt.le, Nat.cast_sub hlt.le]; ring
    · simp only [hp, if_false]
      obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
      obtain ⟨d, hd, hodd, hgt⟩ := (T_even n j (by omega)).1.1 hT
      have h2 := (T_even n j (by omega)).2 d hd hodd hgt
      have hdiv : 2 * n / (2 * j) = d := by
        rw [hd, show 2 * (j * d) = 2 * j * d by ring, Nat.mul_div_cancel_left _ (by omega)]
      have hdiv2 : 2 * n / d = 2 * j := by
        rw [hd, show 2 * (j * d) = d * (2 * j) by ring, Nat.mul_div_cancel_left _ (by omega)]
      rw [hdiv]
      unfold G
      have hns : ¬ d * d < 2 * n := by
        rw [hd]; intro h; have := Nat.mul_le_mul_right d hgt.le; nlinarith
      rw [if_neg hns, hdiv2]
      have : (2 * (T n (2 * j)) : ℤ) = ((d - 2 * j + 1 : ℕ) : ℤ) := by exact_mod_cast h2
      have hle : 2 * j ≤ d := hgt.le
      have e1 : ((d - 2 * j + 1 : ℕ) : ℤ) = (d : ℤ) - 2 * j + 1 := by
        rw [Nat.cast_add, Nat.cast_sub hle]; push_cast; ring
      push_cast
      linear_combination (-1 : ℤ) * this - e1

private lemma partB (n e m : ℕ) (hn : n = 2 ^ e * m) (hm : m % 2 = 1) :
    (ArithmeticFunction.sigma 1 n : ℤ) = ∑ c ∈ m.divisors, (((2 * n / c : ℕ) : ℤ) - c) := by
  have hcop : Nat.Coprime (2 ^ e) m :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (by rw [Nat.odd_iff]; exact hm))
  have h2 : (∑ k ∈ Finset.range (e + 1), (2 : ℤ) ^ k) = 2 ^ (e + 1) - 1 := by
    have := geom_sum_mul (2 : ℤ) (e + 1); norm_num at this; linarith
  have L : (ArithmeticFunction.sigma 1 n : ℤ) = (2 ^ (e + 1) - 1) * ∑ c ∈ m.divisors, (c : ℤ) := by
    rw [hn, ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop,
      ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two, ArithmeticFunction.sigma_one_apply]
    push_cast
    rw [h2]
  have hdiv : ∀ c ∈ m.divisors, ((2 * n / c : ℕ) : ℤ) = 2 ^ (e + 1) * ((m / c : ℕ) : ℤ) := by
    intro c hc
    rw [Nat.mem_divisors] at hc
    rw [hn, show 2 * (2 ^ e * m) = 2 ^ (e + 1) * m by ring, Nat.mul_div_assoc _ hc.1]
    push_cast; ring
  have h1 : ∑ c ∈ m.divisors, ((m / c : ℕ) : ℤ) = ∑ c ∈ m.divisors, (c : ℤ) := by
    exact_mod_cast Nat.sum_div_divisors m (fun x => (x : ℤ))
  rw [L, Finset.sum_sub_distrib, Finset.sum_congr rfl hdiv, ← Finset.mul_sum, h1]
  ring

private lemma tele (n c : ℕ) (e : ℕ) :
    ∑ b ∈ Finset.range (e + 1),
      (if n ≤ 2 * (2 ^ b * c) ^ 2 ∧ (2 ^ b * c) ^ 2 < 2 * n then (1 : ℤ) else 0) =
    (if c * c < 2 * n then 1 else 0) - (if 4 ^ (e + 1) * (c * c) < 2 * n then 1 else 0) := by
  have key : ∀ b, (if n ≤ 2 * (2 ^ b * c) ^ 2 ∧ (2 ^ b * c) ^ 2 < 2 * n then (1 : ℤ) else 0) =
      (if 4 ^ b * (c * c) < 2 * n then 1 else 0) - (if 4 ^ (b + 1) * (c * c) < 2 * n then 1 else 0) := by
    intro b
    have hX : (2 ^ b * c) ^ 2 = 4 ^ b * (c * c) := by
      rw [mul_pow, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm b 2]; ring
    rw [hX, pow_succ]
    set X := 4 ^ b * (c * c)
    rw [show 4 ^ b * 4 * (c * c) = 4 * X by ring]
    split_ifs <;> omega
  rw [Finset.sum_congr rfl (fun b _ => key b), Finset.sum_range_sub']
  simp

private lemma g_end (e m c : ℕ) (hc : c ∣ m) (hm0 : m ≠ 0) :
    4 ^ (e + 1) * (c * c) < 2 * (2 ^ e * m) ↔ 2 * (2 ^ e * m) < (m / c) * (m / c) := by
  obtain ⟨c', rfl⟩ := hc
  have hc0 : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp at hm0)
  have hc'0 : 0 < c' := Nat.pos_of_ne_zero (by rintro rfl; simp at hm0)
  rw [Nat.mul_div_cancel_left _ hc0]
  set P := 2 ^ (e + 1) with hP
  have hPpos : 0 < P := by positivity
  rw [show 4 ^ (e + 1) * (c * c) = (P * c) * (P * c) by
      rw [hP, show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]; ring,
    show 2 * (2 ^ e * (c * c')) = (P * c) * c' by rw [hP, pow_succ]; ring]
  rw [Nat.mul_lt_mul_left (by positivity), Nat.mul_lt_mul_right hc'0]

private lemma partA (n e m : ℕ) (hn : n = 2 ^ e * m) (hm : m % 2 = 1) :
    (A067742 n : ℤ) = ∑ c ∈ m.divisors, ((if c * c < 2 * n then (1 : ℤ) else 0) -
      (if 2 * n < c * c then 1 else 0)) := by
  have hcop : Nat.Coprime (2 ^ e) m :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr (by rw [Nat.odd_iff]; exact hm))
  have hm0 : m ≠ 0 := by omega
  unfold A067742
  rw [Finset.natCast_card_filter, hn]
  set F : ℕ → ℤ := fun t => if 2 ^ e * m ≤ 2 * t ^ 2 ∧ t ^ 2 < 2 * (2 ^ e * m) then 1 else 0 with hF
  show ∑ t ∈ (2 ^ e * m).divisors, F t = _
  rw [Nat.Coprime.divisors_mul hcop, Finset.sum_map]
  show ∑ x ∈ ((2 ^ e).divisors ×ˢ m.divisors).attach, F (x.1.1 * x.1.2) = _
  rw [Finset.sum_attach _ (fun p : ℕ × ℕ => F (p.1 * p.2))]
  rw [Finset.sum_product, Nat.divisors_prime_pow Nat.prime_two, Finset.sum_map, Finset.sum_comm]
  simp only [Function.Embedding.coeFn_mk, hF]
  rw [Finset.sum_congr rfl (fun c _ => tele (2 ^ e * m) c e), Finset.sum_sub_distrib,
    Finset.sum_sub_distrib]
  congr 1
  rw [← Nat.sum_div_divisors m (fun x => if 2 * (2 ^ e * m) < x * x then (1 : ℤ) else 0)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Nat.mem_divisors] at hc
  by_cases h : 4 ^ (e + 1) * (c * c) < 2 * (2 ^ e * m)
  · rw [if_pos h, if_pos ((g_end e m c hc.1 hm0).1 h)]
  · rw [if_neg h, if_neg (fun h' => h ((g_end e m c hc.1 hm0).2 h'))]

theorem OMA.solution : type_of% @OMA.S_oeis_a336305.main := by
  intro n hn
  obtain ⟨e, m, hmo, hnm⟩ := Nat.exists_eq_two_pow_mul_odd (show n ≠ 0 by omega)
  have hm : m % 2 = 1 := Nat.odd_iff.mp hmo
  rw [partC n e m hnm hm hn, partB n e m hnm hm, partA n e m hnm hm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Nat.mem_divisors] at hc
  have hcodd : c % 2 = 1 := by
    obtain ⟨q, hq⟩ := hc.1
    rcases Nat.mod_two_eq_zero_or_one c with h | h
    · exfalso; rw [hq, Nat.mul_mod, h] at hm; simp at hm
    · exact h
  have hne : c * c ≠ 2 * n := by
    intro h
    have : (c * c) % 2 = 1 := by rw [Nat.mul_mod, hcodd]
    omega
  unfold G
  by_cases h1 : c * c < 2 * n
  · rw [if_pos h1, if_pos h1, if_neg (by omega)]; ring
  · rw [if_neg h1, if_neg h1, if_pos (by omega)]; ring
