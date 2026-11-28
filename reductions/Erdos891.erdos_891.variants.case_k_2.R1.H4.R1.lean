import OMAReductions.R_Erdos891_erdos_891_variants_case_k_2_R1
import Mathlib

-- Reduction Erdos891.erdos_891.variants.case_k_2.R1.H4.R1 of step Erdos891.erdos_891.variants.case_k_2.R1.H4
-- Credit: @rickmanelius

/-!
# Erdős 891, `k = 2`: the windows at `M`, `M - 1`, `M - 2`, split by the cube-free part of `M`

The step asks that, for large `M = 2 ^ a 3 ^ b` with `a, b ≥ 1`, each window `[M - i, M - i + 6)`
with `i ≤ 2` contains an integer with at least `3` distinct prime factors. Write `M = c t ^ 3` with
`c = 2 ^ (a mod 3) 3 ^ (b mod 3)` and `t = 2 ^ ⌊a / 3⌋ 3 ^ ⌊b / 3⌋`.

Proved below, with no hypothesis: the classes `c = 2` and `c = 3` (`classA`, `classB`), for
`M ≥ 2000`. There `M + c = c (t ^ 3 + 1) = c (t + 1) (t ^ 2 - t + 1)`, and `M + 2`, `M + 3` lie in
all three windows. The two factors share no prime other than `3`, since
`t ^ 2 - t + 1 = (t + 1) (t - 2) + 3`, so `c`, a prime factor of `t + 1` and a prime factor of
`t ^ 2 - t + 1` are three distinct primes (`cube_omega`) once the edge families are checked. For
`t = 3 ^ y` (that is `a = 1`) the factor `t + 1 = 3 ^ y + 1` is not a power of `2`, being `2` or `4`
modulo `8`. For `t = 2 ^ x` with `x` odd (that is `b = 1`) the factor `t + 1 = 2 ^ x + 1` is not a
power of `3` (modulo `27`, then `19`), and `t ^ 2 - t + 1` is `3` times a number prime to `3`. In
these two classes the only exceptions are `M = 24, 54, 1536`.

The other cube-free parts are left as three hypotheses, each the step restricted to them, grouped
by `b mod 3`:
* `H1`: `b ≡ 0` and `a ≢ 1 (mod 3)`, that is `c ∈ {1, 4}`.
* `H2`: `b ≡ 1` and `a ≢ 0 (mod 3)`, that is `c ∈ {6, 12}`.
* `H3`: `b ≡ 2 (mod 3)`, that is `c ∈ {9, 18, 36}`.
-/

namespace OMA.R_Erdos891_erdos_891_variants_case_k_2_R1_H4_R1

open Finset Filter
open scoped ArithmeticFunction.omega

/-- The windows for `M = c t ^ 3` with `c ∈ {1, 4}`: `b ≡ 0` and `a ≢ 1 (mod 3)`. -/
def H1 : Prop :=
  ∀ᶠ M : ℕ in atTop, ∀ a b : ℕ, 0 < a → 0 < b → M = 2 ^ a * 3 ^ b → b % 3 = 0 → a % 3 ≠ 1 →
    ∀ i : ℕ, i ≤ 2 → ∃ m ∈ Ico (M - i) (M - i + 6), 3 ≤ ω m

/-- The windows for `M = c t ^ 3` with `c ∈ {6, 12}`: `b ≡ 1` and `a ≢ 0 (mod 3)`. -/
def H2 : Prop :=
  ∀ᶠ M : ℕ in atTop, ∀ a b : ℕ, 0 < a → 0 < b → M = 2 ^ a * 3 ^ b → b % 3 = 1 → a % 3 ≠ 0 →
    ∀ i : ℕ, i ≤ 2 → ∃ m ∈ Ico (M - i) (M - i + 6), 3 ≤ ω m

/-- The windows for `M = c t ^ 3` with `c ∈ {9, 18, 36}`: `b ≡ 2 (mod 3)`. -/
def H3 : Prop :=
  ∀ᶠ M : ℕ in atTop, ∀ a b : ℕ, 0 < a → 0 < b → M = 2 ^ a * 3 ^ b → b % 3 = 2 →
    ∀ i : ℕ, i ≤ 2 → ∃ m ∈ Ico (M - i) (M - i + 6), 3 ≤ ω m

/-- `c ^ i` modulo `m` only depends on `i` modulo a period `k` of `c` modulo `m`. -/
lemma pow_mod_period (c : ℕ) {i k m : ℕ} (hm : 2 ≤ m) (h : c ^ k % m = 1) :
    c ^ i % m = c ^ (i % k) % m := by
  have e : c ^ i = c ^ (i % k) * (c ^ k) ^ (i / k) := by
    rw [← pow_mul, ← pow_add, Nat.mod_add_div]
  rw [e, Nat.mul_mod, Nat.pow_mod (c ^ k), h, one_pow, Nat.mod_eq_of_lt (by omega : 1 < m),
    mul_one, Nat.mod_mod]

/-- Three distinct primes dividing `n ≠ 0` give `ω n ≥ 3`. -/
lemma three_le_omega {n p q r : ℕ} (hn : n ≠ 0) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hpn : p ∣ n) (hqn : q ∣ n) (hrn : r ∣ n) :
    3 ≤ ω n := by
  have hω : ω n = n.primeFactors.card := by
    rw [ArithmeticFunction.cardDistinctFactors_apply, Nat.primeFactors, List.card_toFinset]
  rw [hω]
  have hsub : ({p, q, r} : Finset ℕ) ⊆ n.primeFactors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact Nat.mem_primeFactors.mpr ⟨hp, hpn, hn⟩
    · exact Nat.mem_primeFactors.mpr ⟨hq, hqn, hn⟩
    · exact Nat.mem_primeFactors.mpr ⟨hr, hrn, hn⟩
  have hcard : ({p, q, r} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hpq, hpr]), Finset.card_pair hqr]
  calc 3 = ({p, q, r} : Finset ℕ).card := hcard.symm
    _ ≤ n.primeFactors.card := Finset.card_le_card hsub

/-- A number `x ≥ 2` that is not a power of the prime `c` has a prime factor other than `c`. -/
lemma exists_prime_ne {x c : ℕ} (hx : 2 ≤ x) (hnot : ∀ m, x ≠ c ^ m) :
    ∃ p, p.Prime ∧ p ∣ x ∧ p ≠ c := by
  by_contra hall
  push Not at hall
  exact hnot _ (Nat.eq_prime_pow_of_unique_prime_dvd (by omega) fun hp hd => hall _ hp hd)

/-- The cube identity: with `t = s + 1`, the number `c (t ^ 3 + 1) = c (s + 2) (s ^ 2 + s + 1)` has
three distinct prime factors once `s + 2` has a prime factor `p ∉ {c, 3}` and `s ^ 2 + s + 1` has a
prime factor `r ≠ c`; the two factors share no prime other than `3`. -/
lemma cube_omega {c s p r : ℕ} (hc : c.Prime) (hp : p.Prime) (hr : r.Prime)
    (hps : p ∣ s + 2) (hrq : r ∣ s * s + s + 1) (hpc : p ≠ c) (hrc : r ≠ c) (hp3 : p ≠ 3) :
    3 ≤ ω (c * ((s + 2) * (s * s + s + 1))) := by
  have hrp : r ≠ p := by
    rintro rfl
    have h3 : (r : ℤ) ∣ 3 := by
      have h1 : (r : ℤ) ∣ (s : ℤ) + 2 := by exact_mod_cast hps
      have h2 : (r : ℤ) ∣ (s : ℤ) * s + s + 1 := by exact_mod_cast hrq
      have := dvd_sub h2 (dvd_mul_of_dvd_left h1 ((s : ℤ) - 1))
      have e : (s : ℤ) * s + s + 1 - ((s : ℤ) + 2) * ((s : ℤ) - 1) = 3 := by ring
      rwa [e] at this
    have h3' : r ∣ 3 := by exact_mod_cast h3
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3')
  refine three_le_omega (Nat.mul_ne_zero hc.ne_zero (by positivity)) hc hp hr (Ne.symm hpc)
    (Ne.symm hrc) (Ne.symm hrp) (dvd_mul_right c _) ?_ ?_
  · exact Dvd.dvd.mul_left (Dvd.dvd.mul_right hps _) c
  · exact Dvd.dvd.mul_left (Dvd.dvd.mul_left hrq _) c

/-- `3 ^ y + 1` is not a power of `2` for `y ≥ 2` (it is `2` or `4` modulo `8`). -/
lemma three_pow_add_one_ne {y : ℕ} (hy : 2 ≤ y) (m : ℕ) : 3 ^ y + 1 ≠ 2 ^ m := by
  intro h
  have h8 := pow_mod_period 3 (i := y) (k := 2) (m := 8) (by norm_num) (by norm_num)
  have hr : y % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hmod : 3 ^ y % 8 = 1 ∨ 3 ^ y % 8 = 3 := by
    rw [h8]
    interval_cases (y % 2) <;> simp
  rcases Nat.lt_or_ge m 3 with hm | hm
  · have h1 : 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 3 ^ 2 ≤ 3 ^ y := Nat.pow_le_pow_right (by norm_num) hy
    omega
  · have e : 2 ^ m = 8 * 2 ^ (m - 3) := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add, show 3 + (m - 3) = m by omega]
    omega

/-- `2 ^ x + 1` is not a power of `3` for `x ≥ 4` (modulo `27`, then modulo `19`). -/
lemma two_pow_add_one_ne {x : ℕ} (hx : 4 ≤ x) (v : ℕ) : 2 ^ x + 1 ≠ 3 ^ v := by
  intro h
  have hv : 3 ≤ v := by
    by_contra hlt
    have h1 : 3 ^ v ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ 4 ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) hx
    omega
  have e : 3 ^ v = 27 * 3 ^ (v - 3) := by
    rw [show (27 : ℕ) = 3 ^ 3 by norm_num, ← pow_add, show 3 + (v - 3) = v by omega]
  have h26 : 2 ^ x % 27 = 26 := by omega
  have hp27 := pow_mod_period 2 (i := x) (k := 18) (m := 27) (by norm_num) (by norm_num)
  have hp19 := pow_mod_period 2 (i := x) (k := 18) (m := 19) (by norm_num) (by norm_num)
  have hr : x % 18 < 18 := Nat.mod_lt _ (by norm_num)
  have h19 : 2 ^ x % 19 = 18 := by
    rw [hp27] at h26
    rw [hp19]
    interval_cases (x % 18) <;> simp_all
  have hd : 19 ∣ 3 ^ v := by rw [← h]; omega
  have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 19) hd
  norm_num at this

/-- If `r` divides `3 X + 1` then `r ≠ 3`. -/
lemma ne_three_of_dvd {r X : ℕ} (h : r ∣ 3 * X + 1) : r ≠ 3 := by
  rintro rfl
  have := (Nat.dvd_add_right (dvd_mul_right 3 X)).mp h
  norm_num at this

/-- The class `M = 2 t ^ 3` (`a ≡ 1`, `b ≡ 0 (mod 3)`): `M + 2` has three prime factors. -/
lemma classA {a b : ℕ} (ha : a % 3 = 1) (hb : b % 3 = 0) (hb0 : 0 < b)
    (hM : 2000 ≤ 2 ^ a * 3 ^ b) : 3 ≤ ω (2 ^ a * 3 ^ b + 2) := by
  obtain ⟨x, rfl⟩ : ∃ x, a = 3 * x + 1 := ⟨a / 3, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, b = 3 * y := ⟨b / 3, by omega⟩
  have hy : 1 ≤ y := by omega
  set t := 2 ^ x * 3 ^ y with ht
  have ht0 : t ≠ 0 := by rw [ht]; positivity
  obtain ⟨s, hs⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have hfac : 2 ^ (3 * x + 1) * 3 ^ (3 * y) + 2 = 2 * ((s + 2) * (s * s + s + 1)) := by
    have e : 2 ^ (3 * x + 1) * 3 ^ (3 * y) = 2 * t ^ 3 := by rw [ht]; ring
    rw [e, hs]
    ring
  rw [hfac]
  have h3t : 3 ∣ t := by
    rw [ht]
    exact Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _
  have hs3 : s % 3 = 2 := by omega
  obtain ⟨j, hj⟩ : ∃ j, s = 3 * j + 2 := ⟨s / 3, by omega⟩
  have hq : s * s + s + 1 = 3 * (3 * j * j + 5 * j + 2) + 1 := by rw [hj]; ring
  obtain ⟨r, hr, hrq⟩ := Nat.exists_prime_and_dvd (show s * s + s + 1 ≠ 1 by rw [hq]; omega)
  have hr2 : r ≠ 2 := by
    rintro rfl
    have hodd : (s * s + s + 1) % 2 = 1 := by
      have : s * s + s = s * (s + 1) := by ring
      rw [this, Nat.add_mod, Nat.mul_mod]
      rcases Nat.mod_two_eq_zero_or_one s with h0 | h0 <;> simp [h0, Nat.add_mod]
    omega
  obtain ⟨p, hp, hps, hp2⟩ : ∃ p, p.Prime ∧ p ∣ s + 2 ∧ p ≠ 2 := by
    rcases Nat.eq_zero_or_pos x with hx | hx
    · subst hx
      have hy2 : 2 ≤ y := by
        by_contra hlt
        have : 3 ^ (3 * y) ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
        norm_num at hM
        omega
      refine exists_prime_ne (by omega) fun m hm => ?_
      have ht' : t = 3 ^ y := by rw [ht]; simp
      exact three_pow_add_one_ne hy2 m (by omega)
    · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (show s + 2 ≠ 1 by omega)
      refine ⟨p, hp, hpd, ?_⟩
      rintro rfl
      have h2t : 2 ∣ t := by
        rw [ht]
        exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
      omega
  have hp3 : p ≠ 3 := by
    rintro rfl
    omega
  exact cube_omega Nat.prime_two hp hr hps hrq hp2 hr2 hp3

/-- The class `M = 3 t ^ 3` (`a ≡ 0`, `b ≡ 1 (mod 3)`): `M + 3` has three prime factors. -/
lemma classB {a b : ℕ} (ha : a % 3 = 0) (ha0 : 0 < a) (hb : b % 3 = 1)
    (hM : 2000 ≤ 2 ^ a * 3 ^ b) : 3 ≤ ω (2 ^ a * 3 ^ b + 3) := by
  obtain ⟨x, rfl⟩ : ∃ x, a = 3 * x := ⟨a / 3, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, b = 3 * y + 1 := ⟨b / 3, by omega⟩
  have hx : 1 ≤ x := by omega
  set t := 2 ^ x * 3 ^ y with ht
  have ht0 : t ≠ 0 := by rw [ht]; positivity
  obtain ⟨s, hs⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have hfac : 2 ^ (3 * x) * 3 ^ (3 * y + 1) + 3 = 3 * ((s + 2) * (s * s + s + 1)) := by
    have e : 2 ^ (3 * x) * 3 ^ (3 * y + 1) = 3 * t ^ 3 := by rw [ht]; ring
    rw [e, hs]
    ring
  rw [hfac]
  have h2t : 2 ∣ t := by
    rw [ht]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  rcases Nat.eq_zero_or_pos y with hy | hy
  · subst hy
    have ht' : t = 2 ^ x := by rw [ht]; simp
    rcases Nat.even_or_odd x with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- `t = 4 ^ k ≡ 1 (mod 3)`
      have ht3 : t % 3 = 1 := by
        rw [ht', hk, ← two_mul, pow_mul, Nat.pow_mod]
        norm_num
      obtain ⟨j, hj⟩ : ∃ j, s = 3 * j := ⟨s / 3, by omega⟩
      have hq : s * s + s + 1 = 3 * (3 * j * j + j) + 1 := by rw [hj]; ring
      obtain ⟨r, hr, hrq⟩ := Nat.exists_prime_and_dvd (show s * s + s + 1 ≠ 1 by rw [hq]; omega)
      obtain ⟨p, hp, hps⟩ := Nat.exists_prime_and_dvd (show s + 2 ≠ 1 by omega)
      have hp3 : p ≠ 3 := by
        rw [show s + 2 = 3 * j + 2 by omega] at hps
        rintro rfl
        omega
      exact cube_omega Nat.prime_three hp hr hps hrq hp3 (ne_three_of_dvd (hq ▸ hrq)) hp3
    · -- `t = 2 ^ x` with `x` odd, `x ≥ 5`: `t ≡ 2 (mod 3)`
      have hx4 : 4 ≤ x := by
        by_contra hlt
        have : 2 ^ (3 * x) ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) (by omega)
        norm_num at hM
        omega
      have ht3 : t % 3 = 2 := by
        rw [ht', hk, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
        norm_num
      obtain ⟨p, hp, hps, hp3⟩ := exists_prime_ne (c := 3) (show 2 ≤ s + 2 by omega)
        fun m hm => two_pow_add_one_ne hx4 m (by omega)
      obtain ⟨j, hj⟩ : ∃ j, s = 3 * j + 1 := ⟨s / 3, by omega⟩
      have hj1 : 1 ≤ j := by
        have : 2 ^ 4 ≤ 2 ^ x := Nat.pow_le_pow_right (by norm_num) hx4
        omega
      have hq : s * s + s + 1 = 3 * (3 * (j * j + j) + 1) := by rw [hj]; ring
      obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (show 3 * (j * j + j) + 1 ≠ 1 by
        have : 1 ≤ j * j := Nat.one_le_iff_ne_zero.mpr (by positivity)
        omega)
      have hrq : r ∣ s * s + s + 1 := by rw [hq]; exact Dvd.dvd.mul_left hrd 3
      exact cube_omega Nat.prime_three hp hr hps hrq hp3 (ne_three_of_dvd hrd) hp3
  · -- `3 ∣ t`: both factors are `1 (mod 3)`
    have h3t : 3 ∣ t := by
      rw [ht]
      exact Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _
    obtain ⟨j, hj⟩ : ∃ j, s = 3 * j + 2 := ⟨s / 3, by omega⟩
    have hq : s * s + s + 1 = 3 * (3 * j * j + 5 * j + 2) + 1 := by rw [hj]; ring
    obtain ⟨r, hr, hrq⟩ := Nat.exists_prime_and_dvd (show s * s + s + 1 ≠ 1 by rw [hq]; omega)
    obtain ⟨p, hp, hps⟩ := Nat.exists_prime_and_dvd (show s + 2 ≠ 1 by omega)
    have hp3 : p ≠ 3 := by
      rw [show s + 2 = 3 * (j + 1) + 1 by omega] at hps
      exact ne_three_of_dvd hps
    exact cube_omega Nat.prime_three hp hr hps hrq hp3 (ne_three_of_dvd (hq ▸ hrq)) hp3

theorem main : H1 → H2 → H3 → OMA.R_Erdos891_erdos_891_variants_case_k_2_R1.H4 := by
  intro h1 h2 h3
  filter_upwards [h1, h2, h3, eventually_ge_atTop 2000] with M hM1 hM2 hM3 hM a b ha hb hab i hi
  have hM' : 2000 ≤ 2 ^ a * 3 ^ b := by rw [← hab]; exact hM
  by_cases hA : a % 3 = 1 ∧ b % 3 = 0
  · refine ⟨M + 2, by rw [mem_Ico]; omega, ?_⟩
    rw [hab]
    exact classA hA.1 hA.2 hb hM'
  by_cases hB : a % 3 = 0 ∧ b % 3 = 1
  · refine ⟨M + 3, by rw [mem_Ico]; omega, ?_⟩
    rw [hab]
    exact classB hB.1 ha hB.2 hM'
  rcases (by omega : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2) with h0 | h0 | h0
  · exact hM1 a b ha hb hab h0 (fun h => hA ⟨h, h0⟩) i hi
  · exact hM2 a b ha hb hab h0 (fun h => hB ⟨h, h0⟩) i hi
  · exact hM3 a b ha hb hab h0 i hi

end OMA.R_Erdos891_erdos_891_variants_case_k_2_R1_H4_R1
