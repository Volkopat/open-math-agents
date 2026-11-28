import OMAStatements.S_oeis_a280364
import Mathlib

namespace A280364

open Finset PowerSeries OMA.S_oeis_a280364

lemma three_pow_bound : ∀ n : ℕ, 1 ≤ n → 2 * n ^ 2 < 3 ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k
      norm_num
    · have h1 : 2 * (k + 1) ^ 2 ≤ 3 * (2 * k ^ 2) := by nlinarith
      calc 2 * (k + 1) ^ 2 ≤ 3 * (2 * k ^ 2) := h1
        _ < 3 * 3 ^ k := by omega
        _ = 3 ^ (k + 1) := by ring

lemma two_pow_bound : ∀ m : ℕ, 6 ≤ m → (m + 1) * (m + 1) < 2 ^ m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h1 : (k + 1 + 1) * (k + 1 + 1) ≤ 2 * ((k + 1) * (k + 1)) := by nlinarith
    calc (k + 1 + 1) * (k + 1 + 1) ≤ 2 * ((k + 1) * (k + 1)) := h1
      _ < 2 * 2 ^ k := by omega
      _ = 2 ^ (k + 1) := by ring

lemma no_two (n : ℕ) (hn : 1 ≤ n) (u v s t : ℕ) (hu : u ≤ n) (hv : v ≤ n) (hs : s ≤ n)
    (ht : t ≤ n) (h1 : u * v + s * t = 2 ^ n) (h2 : u * v = s * t + 2) : False := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
  have hle : u * v ≤ (m + 1) * (m + 1) := Nat.mul_le_mul hu hv
  have hm : m < 6 := by
    by_contra hcon
    have h3 := two_pow_bound m (by omega)
    omega
  interval_cases m
  all_goals norm_num at h1
  all_goals interval_cases u <;> first | omega | (interval_cases s <;> omega)

lemma accept_fwd (n : ℕ) (hn : 1 ≤ n) (u v s t : ℕ) (hu : u ≤ n) (hv : v ≤ n) (hs : s ≤ n)
    (ht : t ≤ n) (h : accept n (u * v) (s * t)) :
    (u * v = 0 ∧ s * t = 0) ∨ (u * v = 1 ∧ s * t = 0) ∨ (Even n ∧ u * v = 0 ∧ s * t = 1) := by
  unfold accept at h
  have hx : u * v ≤ n * n := Nat.mul_le_mul hu hv
  have hy : s * t ≤ n * n := Nat.mul_le_mul hs ht
  obtain ⟨x, hxe⟩ : ∃ x, x = u * v := ⟨_, rfl⟩
  obtain ⟨y, hye⟩ : ∃ y, y = s * t := ⟨_, rfl⟩
  rw [← hxe] at h hx ⊢
  rw [← hye] at h hy ⊢
  have hb := three_pow_bound n hn
  have hd : -2 ≤ (x:ℤ) - y ∧ (x:ℤ) - y ≤ 2 := by
    by_contra hcon
    have h9 : (9:ℤ) ≤ ((x:ℤ) - y) * ((x:ℤ) - y) := by
      rcases not_and_or.mp hcon with h' | h'
      · have h3 : (x:ℤ) - y ≤ -3 := by omega
        nlinarith [mul_self_nonneg ((x:ℤ) - y + 3)]
      · have h3 : 3 ≤ (x:ℤ) - y := by omega
        nlinarith [mul_self_nonneg ((x:ℤ) - y - 3)]
    have h9n : (9:ℤ) ^ n ≤ (((x:ℤ) - y) * ((x:ℤ) - y)) ^ n :=
      pow_le_pow_left₀ (by norm_num) h9 n
    have hlt : (x:ℤ) + y < 3 ^ n := by
      have hsq : n ^ 2 = n * n := sq n
      have h3 : x + y < 3 ^ n := by omega
      exact_mod_cast h3
    have hnn : (0:ℤ) ≤ (x:ℤ) + y := by positivity
    have hsq : ((x:ℤ) + y) * ((x:ℤ) + y) < 3 ^ n * 3 ^ n := mul_lt_mul'' hlt hlt hnn hnn
    rw [h] at hsq
    have e1 : ((x:ℤ) - y) ^ n * ((x:ℤ) - y) ^ n = (((x:ℤ) - y) * ((x:ℤ) - y)) ^ n :=
      (mul_pow _ _ _).symm
    have e2 : (3:ℤ) ^ n * 3 ^ n = 9 ^ n := by
      rw [← mul_pow]
      norm_num
    rw [e1, e2] at hsq
    linarith
  obtain ⟨hd1, hd2⟩ := hd
  have hcases : (x:ℤ) - y = -2 ∨ (x:ℤ) - y = -1 ∨ (x:ℤ) - y = 0 ∨ (x:ℤ) - y = 1 ∨
      (x:ℤ) - y = 2 := by omega
  rcases hcases with hc | hc | hc | hc | hc
  · rw [hc] at h
    rcases Nat.even_or_odd n with he | ho
    · rw [he.neg_pow] at h
      exfalso
      have h1 : x + y = 2 ^ n := by exact_mod_cast h
      have h2 : y = x + 2 := by omega
      exact no_two n hn s t u v hs ht hu hv (by rw [← hxe, ← hye]; omega)
        (by rw [← hxe, ← hye]; exact h2)
    · rw [ho.neg_pow] at h
      have hpos : (0:ℤ) < 2 ^ n := by positivity
      omega
  · rw [hc] at h
    rcases Nat.even_or_odd n with he | ho
    · rw [he.neg_one_pow] at h
      right
      right
      exact ⟨he, by omega, by omega⟩
    · rw [ho.neg_one_pow] at h
      omega
  · rw [hc, zero_pow (by omega)] at h
    left
    exact ⟨by omega, by omega⟩
  · rw [hc, one_pow] at h
    right
    left
    exact ⟨by omega, by omega⟩
  · rw [hc] at h
    exfalso
    have h1 : x + y = 2 ^ n := by exact_mod_cast h
    have h2 : x = y + 2 := by omega
    exact no_two n hn u v s t hu hv hs ht (by rw [← hxe, ← hye]; exact h1)
      (by rw [← hxe, ← hye]; exact h2)

lemma accept_bwd (n : ℕ) (hn : 1 ≤ n) (x y : ℕ)
    (h : (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 0) ∨ (Even n ∧ x = 0 ∧ y = 1)) : accept n x y := by
  unfold accept
  have hn0 : n ≠ 0 := by omega
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨he, rfl, rfl⟩
  · simp [hn0]
  · simp
  · simp [he.neg_one_pow]

lemma ind_aux (E : Prop) [Decidable E] (A : Prop) [Decidable A] (x y : ℕ)
    (hiff : A ↔ (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 0) ∨ (E ∧ x = 0 ∧ y = 1)) :
    (if A then 1 else 0 : ℕ) =
      (if x = 0 then 1 else 0) * (if y = 0 then 1 else 0) +
      (if x = 1 then 1 else 0) * (if y = 0 then 1 else 0) +
      (if E then 1 else 0) * ((if x = 0 then 1 else 0) * (if y = 1 then 1 else 0)) := by
  rw [if_congr hiff rfl rfl]
  by_cases hE : E <;> by_cases hx0 : x = 0 <;> by_cases hx1 : x = 1 <;>
    by_cases hy0 : y = 0 <;> by_cases hy1 : y = 1 <;>
    first | omega | simp [hE, hx0, hx1, hy0, hy1]

lemma Z_sum (n : ℕ) :
    ∑ p ∈ entryPairs n, (if pairProduct p = 0 then 1 else 0 : ℕ) = 2 * n + 1 := by
  unfold entryPairs
  rw [Finset.sum_product, Finset.sum_range_succ']
  have inner : ∀ u : ℕ,
      ∑ v ∈ range (n + 1), (if pairProduct (u + 1, v) = 0 then 1 else 0 : ℕ) = 1 := by
    intro u
    rw [Finset.sum_range_succ']
    simp [pairProduct]
  simp only [inner]
  simp [pairProduct]
  omega

lemma O_sum (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ entryPairs n, (if pairProduct p = 1 then 1 else 0 : ℕ) = 1 := by
  rw [← Finset.card_filter]
  have h : (entryPairs n).filter (fun p => pairProduct p = 1) = {(1, 1)} := by
    apply Finset.ext
    rintro ⟨u, v⟩
    rw [Finset.mem_filter, Finset.mem_singleton, Prod.mk.injEq]
    unfold entryPairs
    simp only [Finset.mem_product, Finset.mem_range]
    constructor
    · rintro ⟨_, h1'⟩
      have h1 : u * v = 1 := h1'
      exact ⟨Nat.dvd_one.mp ⟨v, h1.symm⟩, Nat.dvd_one.mp ⟨u, by rw [mul_comm]; exact h1.symm⟩⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨by omega, by omega⟩, rfl⟩
  rw [h, Finset.card_singleton]

lemma a_formula (n : ℕ) (hn : 1 ≤ n) :
    a n = (2 * n + 1) * (2 * n + 1) + 1 * (2 * n + 1) +
      (if Even n then 1 else 0) * ((2 * n + 1) * 1) := by
  unfold a matrices
  rw [Finset.card_filter, Finset.sum_product]
  have hind : ∀ p ∈ entryPairs n, ∀ q ∈ entryPairs n,
      (if accept n (pairProduct p) (pairProduct q) then 1 else 0 : ℕ) =
        (if pairProduct p = 0 then 1 else 0) * (if pairProduct q = 0 then 1 else 0) +
        (if pairProduct p = 1 then 1 else 0) * (if pairProduct q = 0 then 1 else 0) +
        (if Even n then 1 else 0) *
          ((if pairProduct p = 0 then 1 else 0) * (if pairProduct q = 1 then 1 else 0)) := by
    intro p hp q hq
    apply ind_aux
    obtain ⟨u, v⟩ := p
    obtain ⟨s, t⟩ := q
    simp only [entryPairs, Finset.mem_product, Finset.mem_range] at hp hq
    exact ⟨accept_fwd n hn u v s t (by omega) (by omega) (by omega) (by omega),
      accept_bwd n hn _ _⟩
  rw [Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun q hq => hind p hp q hq))]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [Z_sum, O_sum n hn]

lemma fE (n : ℕ) (hn : 0 < n) (he : Even n) : a n = 4 * n ^ 2 + 8 * n + 3 := by
  rw [a_formula n hn, if_pos he]
  ring

lemma fO (n : ℕ) (ho : Odd n) : a n = 4 * n ^ 2 + 6 * n + 2 := by
  have hn : 1 ≤ n := ho.pos
  rw [a_formula n hn, if_neg (Nat.not_even_iff_odd.mpr ho)]
  ring

lemma rec3 (n : ℕ) (hn : 5 < n) :
    (a n : ℤ) = (a (n - 1) : ℤ) + 2 * (a (n - 2) : ℤ) - 2 * (a (n - 3) : ℤ) -
      (a (n - 4) : ℤ) + (a (n - 5) : ℤ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have e1 : m + 6 - 1 = m + 5 := by omega
  have e2 : m + 6 - 2 = m + 4 := by omega
  have e3 : m + 6 - 3 = m + 3 := by omega
  have e4 : m + 6 - 4 = m + 2 := by omega
  have e5 : m + 6 - 5 = m + 1 := by omega
  rw [e1, e2, e3, e4, e5]
  rcases Nat.even_or_odd' m with ⟨j, rfl | rfl⟩
  · rw [fE (2 * j + 6) (by omega) ⟨j + 3, by ring⟩, fO (2 * j + 5) ⟨j + 2, by ring⟩,
      fE (2 * j + 4) (by omega) ⟨j + 2, by ring⟩, fO (2 * j + 3) ⟨j + 1, by ring⟩,
      fE (2 * j + 2) (by omega) ⟨j + 1, by ring⟩, fO (2 * j + 1) ⟨j, by ring⟩]
    push_cast
    ring
  · rw [fO (2 * j + 1 + 6) ⟨j + 3, by ring⟩, fE (2 * j + 1 + 5) (by omega) ⟨j + 3, by ring⟩,
      fO (2 * j + 1 + 4) ⟨j + 2, by ring⟩, fE (2 * j + 1 + 3) (by omega) ⟨j + 2, by ring⟩,
      fO (2 * j + 1 + 2) ⟨j + 1, by ring⟩, fE (2 * j + 1 + 1) (by omega) ⟨j + 1, by ring⟩]
    push_cast
    ring

lemma vals : a 0 = 0 ∧ a 1 = 12 ∧ a 2 = 35 ∧ a 3 = 56 ∧ a 4 = 99 ∧ a 5 = 132 := by
  have h1 := fO 1 ⟨0, rfl⟩
  have h2 := fE 2 (by norm_num) ⟨1, rfl⟩
  have h3 := fO 3 ⟨1, rfl⟩
  have h4 := fE 4 (by norm_num) ⟨2, rfl⟩
  have h5 := fO 5 ⟨2, rfl⟩
  norm_num at h1 h2 h3 h4 h5
  exact ⟨by decide, h1, h2, h3, h4, h5⟩

lemma coef_claim (n : ℕ) :
    (a n : ℚ) - (if 1 ≤ n then (a (n - 1) : ℚ) else 0) -
        2 * (if 2 ≤ n then (a (n - 2) : ℚ) else 0) +
        2 * (if 3 ≤ n then (a (n - 3) : ℚ) else 0) +
        (if 4 ≤ n then (a (n - 4) : ℚ) else 0) - (if 5 ≤ n then (a (n - 5) : ℚ) else 0) =
      12 * (if n = 1 then 1 else 0) + 23 * (if n = 2 then 1 else 0) -
        3 * (if n = 3 then 1 else 0) - 3 * (if n = 4 then 1 else 0) +
        3 * (if n = 5 then 1 else 0) := by
  obtain ⟨v0, v1, v2, v3, v4, v5⟩ := vals
  by_cases h : 6 ≤ n
  · have hr := rec3 n (by omega)
    have hr' : (a n : ℚ) = (a (n - 1) : ℚ) + 2 * (a (n - 2) : ℚ) - 2 * (a (n - 3) : ℚ) -
        (a (n - 4) : ℚ) + (a (n - 5) : ℚ) := by exact_mod_cast hr
    have c1 : 1 ≤ n := by omega
    have c2 : 2 ≤ n := by omega
    have c3 : 3 ≤ n := by omega
    have c4 : 4 ≤ n := by omega
    have c5 : 5 ≤ n := by omega
    have d1 : ¬ n = 1 := by omega
    have d2 : ¬ n = 2 := by omega
    have d3 : ¬ n = 3 := by omega
    have d4 : ¬ n = 4 := by omega
    have d5 : ¬ n = 5 := by omega
    rw [if_pos c1, if_pos c2, if_pos c3, if_pos c4, if_pos c5, if_neg d1, if_neg d2, if_neg d3,
      if_neg d4, if_neg d5]
    linarith
  · have h' : n ≤ 5 := by omega
    interval_cases n <;> norm_num [v0, v1, v2, v3, v4, v5]

lemma ogf_eq : ogf * ((1 - X) ^ 3 * (1 + X) ^ 2) =
    X * (12 + 23 * X - 3 * X ^ 2 - 3 * X ^ 3 + 3 * X ^ 4) := by
  have e1 : ogf * ((1 - X) ^ 3 * (1 + X) ^ 2) =
      ogf - ogf * X ^ 1 - C (2:ℚ) * (ogf * X ^ 2) + C (2:ℚ) * (ogf * X ^ 3) + ogf * X ^ 4 -
        ogf * X ^ 5 := by
    simp only [map_ofNat]
    ring
  have e2 : (X : PowerSeries ℚ) * (12 + 23 * X - 3 * X ^ 2 - 3 * X ^ 3 + 3 * X ^ 4) =
      C (12:ℚ) * X ^ 1 + C (23:ℚ) * X ^ 2 - C (3:ℚ) * X ^ 3 - C (3:ℚ) * X ^ 4 +
        C (3:ℚ) * X ^ 5 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k ogf = (a k : ℚ) := fun k => by simp [ogf]
  conv_lhs => simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', hc]
  conv_rhs => simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow]
  have h := coef_claim n
  linarith

end A280364

theorem OMA.solution : type_of% @OMA.S_oeis_a280364.main := by
  refine ⟨fun n hn he => A280364.fE n hn he, fun n ho => A280364.fO n ho,
    fun n hn => A280364.rec3 n hn, ?_⟩
  show OMA.S_oeis_a280364.ogf = PowerSeries.X * (12 + 23 * PowerSeries.X - 3 * PowerSeries.X ^ 2 -
    3 * PowerSeries.X ^ 3 + 3 * PowerSeries.X ^ 4) *
      (((1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X) ^ 2)⁻¹)
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  exact A280364.ogf_eq
