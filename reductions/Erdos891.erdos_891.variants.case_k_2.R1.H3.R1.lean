import OMAReductions.R_Erdos891_erdos_891_variants_case_k_2_R1
import Mathlib

-- Reduction Erdos891.erdos_891.variants.case_k_2.R1.H3.R1 of step Erdos891.erdos_891.variants.case_k_2.R1.H3
-- Credit: @rickmanelius

/-!
# Erdős 891, `k = 2`: the window `[M - 3, M + 3)` when `M` or `M / 36` is a fourth power

The step asks that, for large `M = 2 ^ a 3 ^ b` with `a, b ≥ 1` both even, one of
`M - 3, ..., M + 2` has at least `3` distinct prime factors. Write `M = s ^ 2` with
`s = 2 ^ (a / 2) 3 ^ (b / 2)`.

Proved below, with no hypothesis: the classes `a ≡ b (mod 4)`, that is `M = r ^ 4` or
`M = 36 r ^ 4` with `r` a `3`-smooth number. Then `M ≡ 1 (mod 5)`, since
`4 ^ x 9 ^ y ≡ (-1) ^ (x + y)`, so `5` divides `M - 1 = (s + 1) (s - 1)`. The two factors are odd
and coprime, so `ω (M - 1) = ω (s + 1) + ω (s - 1)`, which is at least `3` unless the factor
divisible by `5` is a power of `5`. That happens only for `s = 6` and `s = 24`
(`sunit_minus`, `sunit_plus`): `2 ^ x 3 ^ y = 5 ^ i + 1` forces `x = 1` (modulo `4`) and then
`y = 1` (modulo `9`, then `7`), and `2 ^ x 3 ^ y + 1 = 5 ^ i` forces `y = 1` (modulo `9`, then `31`)
and `x ≤ 3` (modulo `16`, then `13`). So `M - 1` works for every `M > 576` in these classes
(`omega_three`).

In the two remaining classes `5` divides `M + 1` instead. They are left as hypotheses, each the
step restricted to one class:
* `H1`: `a ≡ 0` and `b ≡ 2 (mod 4)`, that is `M = 9 r ^ 4`.
* `H2`: `a ≡ 2` and `b ≡ 0 (mod 4)`, that is `M = 4 r ^ 4`. Here
  `M + 1 = (2 r ^ 2 - 2 r + 1) (2 r ^ 2 + 2 r + 1)` (Sophie Germain), a product of two coprime
  factors greater than `1`.
-/

namespace OMA.R_Erdos891_erdos_891_variants_case_k_2_R1_H3_R1

open Finset Filter
open scoped ArithmeticFunction.omega

/-- The window `[M - 3, M + 3)` for `M = 2 ^ a 3 ^ b` with `a ≡ 0` and `b ≡ 2 (mod 4)`. -/
def H1 : Prop :=
  ∀ᶠ M : ℕ in atTop, ∀ a b : ℕ, 0 < a → 0 < b → M = 2 ^ a * 3 ^ b → a % 4 = 0 → b % 4 = 2 →
    ∃ m ∈ Ico (M - 3) (M + 3), 3 ≤ ω m

/-- The window `[M - 3, M + 3)` for `M = 2 ^ a 3 ^ b` with `a ≡ 2` and `b ≡ 0 (mod 4)`. -/
def H2 : Prop :=
  ∀ᶠ M : ℕ in atTop, ∀ a b : ℕ, 0 < a → 0 < b → M = 2 ^ a * 3 ^ b → a % 4 = 2 → b % 4 = 0 →
    ∃ m ∈ Ico (M - 3) (M + 3), 3 ≤ ω m

/-- `5 ^ i` modulo `m` only depends on `i` modulo a period `k` of `5` modulo `m`. -/
lemma pow_mod_period {i k m : ℕ} (hm : 2 ≤ m) (h : 5 ^ k % m = 1) :
    5 ^ i % m = 5 ^ (i % k) % m := by
  have e : 5 ^ i = 5 ^ (i % k) * (5 ^ k) ^ (i / k) := by
    rw [← pow_mul, ← pow_add, Nat.mod_add_div]
  rw [e, Nat.mul_mod, Nat.pow_mod (5 ^ k), h, one_pow, Nat.mod_eq_of_lt (by omega : 1 < m),
    mul_one, Nat.mod_mod]

/-- `2 ^ x * 3 ^ y = 5 ^ i + 1` with `x, y ≥ 1` only for `x = y = 1` (that is `6 = 5 + 1`). -/
lemma sunit_minus {x y i : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y) (h : 2 ^ x * 3 ^ y = 5 ^ i + 1) :
    x = 1 ∧ y = 1 := by
  have h4 : 5 ^ i % 4 = 1 := by rw [Nat.pow_mod]; norm_num
  have hx1 : x = 1 := by
    by_contra hne
    have e : 2 ^ x * 3 ^ y = 4 * (2 ^ (x - 2) * 3 ^ y) := by
      rw [← mul_assoc, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, show 2 + (x - 2) = x by omega]
    omega
  refine ⟨hx1, ?_⟩
  subst hx1
  by_contra hne
  have e : 2 ^ 1 * 3 ^ y = 9 * (2 * 3 ^ (y - 2)) := by
    rw [show (9 : ℕ) = 3 ^ 2 by norm_num, pow_one, mul_left_comm, ← pow_add,
      show 2 + (y - 2) = y by omega]
  have h9 : 5 ^ i % 9 = 8 := by omega
  have hp9 := pow_mod_period (i := i) (k := 6) (m := 9) (by norm_num) (by norm_num)
  have hp7 := pow_mod_period (i := i) (k := 6) (m := 7) (by norm_num) (by norm_num)
  have hr : i % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have h7 : 5 ^ i % 7 = 6 := by
    rw [hp9] at h9
    rw [hp7]
    interval_cases (i % 6) <;> simp_all
  -- so 7 divides 2 * 3 ^ y
  have hd : 7 ∣ 2 * 3 ^ y := by
    rw [← pow_one 2, h]
    omega
  have h7p : Nat.Prime 7 := by norm_num
  rcases (Nat.Prime.dvd_mul h7p).mp hd with h | h
  · norm_num at h
  · have := Nat.Prime.dvd_of_dvd_pow h7p h
    norm_num at this

/-- `2 ^ x * 3 ^ y + 1 = 5 ^ i` with `x, y ≥ 1` only for `x = 3, y = 1` (that is `24 + 1 = 25`). -/
lemma sunit_plus {x y i : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y) (h : 2 ^ x * 3 ^ y + 1 = 5 ^ i) :
    x = 3 ∧ y = 1 := by
  have hy1 : y = 1 := by
    by_contra hne
    have e : 2 ^ x * 3 ^ y = 9 * (2 ^ x * 3 ^ (y - 2)) := by
      rw [show (9 : ℕ) = 3 ^ 2 by norm_num, mul_left_comm, ← pow_add,
        show 2 + (y - 2) = y by omega]
    have h9 : 5 ^ i % 9 = 1 := by omega
    have hp9 := pow_mod_period (i := i) (k := 6) (m := 9) (by norm_num) (by norm_num)
    have hp31 := pow_mod_period (i := i) (k := 3) (m := 31) (by norm_num) (by norm_num)
    have hr : i % 6 < 6 := Nat.mod_lt _ (by norm_num)
    have h31 : 5 ^ i % 31 = 1 := by
      rw [hp9] at h9
      rw [hp31]
      have : i % 3 = (i % 6) % 3 := by omega
      rw [this]
      interval_cases (i % 6) <;> simp_all
    have hd : 31 ∣ 2 ^ x * 3 ^ y := by omega
    have h31p : Nat.Prime 31 := by norm_num
    rcases (Nat.Prime.dvd_mul h31p).mp hd with h | h
    · have := Nat.Prime.dvd_of_dvd_pow h31p h
      norm_num at this
    · have := Nat.Prime.dvd_of_dvd_pow h31p h
      norm_num at this
  subst hy1
  have hx3 : x ≤ 3 := by
    by_contra hne
    have e : 2 ^ x * 3 ^ 1 = 16 * (2 ^ (x - 4) * 3) := by
      rw [show (16 : ℕ) = 2 ^ 4 by norm_num, pow_one, ← mul_assoc, ← pow_add,
        show 4 + (x - 4) = x by omega]
    have h16 : 5 ^ i % 16 = 1 := by omega
    have hp16 := pow_mod_period (i := i) (k := 4) (m := 16) (by norm_num) (by norm_num)
    have hp13 := pow_mod_period (i := i) (k := 4) (m := 13) (by norm_num) (by norm_num)
    have hr : i % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have h13 : 5 ^ i % 13 = 1 := by
      rw [hp16] at h16
      rw [hp13]
      interval_cases (i % 4) <;> simp_all
    have hd : 13 ∣ 2 ^ x * 3 ^ 1 := by omega
    have h13p : Nat.Prime 13 := by norm_num
    rcases (Nat.Prime.dvd_mul h13p).mp hd with h | h
    · have := Nat.Prime.dvd_of_dvd_pow h13p h
      norm_num at this
    · norm_num at h
  refine ⟨?_, rfl⟩
  have hi : i ≤ 1 ∨ 2 ≤ i := by omega
  interval_cases x
  · exfalso
    rcases hi with hi | hi
    · interval_cases i <;> simp at h
    · have : 5 ^ 2 ≤ 5 ^ i := Nat.pow_le_pow_right (by norm_num) hi
      norm_num at h
      omega
  · exfalso
    rcases hi with hi | hi
    · interval_cases i <;> simp at h
    · have : 5 ^ 2 ≤ 5 ^ i := Nat.pow_le_pow_right (by norm_num) hi
      norm_num at h
      omega
  · rfl

/-- If `s = 2 ^ x * 3 ^ y` with `x = y (mod 2)` and `s > 24`, then `s ^ 2 - 1` has at least three
prime factors: `5` divides `s ^ 2 - 1 = (s + 1) (s - 1)`, the two factors are odd and coprime, and
the one divisible by `5` is not a power of `5`. -/
lemma omega_three (x y : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hxy : x % 2 = y % 2)
    (hbig : 24 < 2 ^ x * 3 ^ y) : 3 ≤ ω ((2 ^ x * 3 ^ y) ^ 2 - 1) := by
  set s := 2 ^ x * 3 ^ y with hs
  have hs2 : 2 ∣ s := by
    rw [hs]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  -- `s ^ 2 = 1 (mod 5)`
  have hsq : s ^ 2 = 4 ^ x * 9 ^ y := by
    rw [hs, mul_pow, ← pow_mul, ← pow_mul, mul_comm x 2, mul_comm y 2, pow_mul, pow_mul]
    norm_num
  have hmod : s ^ 2 % 5 = 1 := by
    have e2 : x + y = 2 * ((x + y) / 2) := by omega
    have h9 : 9 ^ y ≡ 4 ^ y [MOD 5] := Nat.ModEq.pow y (by decide)
    have : 4 ^ x * 9 ^ y ≡ 1 [MOD 5] := by
      calc 4 ^ x * 9 ^ y ≡ 4 ^ x * 4 ^ y [MOD 5] := Nat.ModEq.mul_left _ h9
        _ = 16 ^ ((x + y) / 2) := by rw [← pow_add, e2, pow_mul]; norm_num
        _ ≡ 1 ^ ((x + y) / 2) [MOD 5] := Nat.ModEq.pow _ (by decide)
        _ = 1 := one_pow _
    rw [hsq]
    exact this
  have hfac : s ^ 2 - 1 = (s + 1) * (s - 1) := by
    have := Nat.sq_sub_sq s 1
    rwa [one_pow] at this
  have h5 : 5 ∣ (s + 1) * (s - 1) := by
    rw [← hfac]
    have : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hcop : Nat.Coprime (s + 1) (s - 1) := by
    rw [Nat.Coprime]
    have h1 := Nat.gcd_dvd_left (s + 1) (s - 1)
    have h2 := Nat.gcd_dvd_right (s + 1) (s - 1)
    have h3 : Nat.gcd (s + 1) (s - 1) ∣ 2 := by
      have := Nat.dvd_sub h1 h2
      rwa [show s + 1 - (s - 1) = 2 by omega] at this
    rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h | h
    · exact h
    · exfalso
      rw [h] at h2
      omega
  rw [hfac, ArithmeticFunction.cardDistinctFactors_mul hcop]
  have hpos : ∀ t : ℕ, 2 ≤ t → 1 ≤ ω t := by
    intro t ht
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [ArithmeticFunction.cardDistinctFactors_eq_zero] at h0
    omega
  -- a factor divisible by `5` that is not a power of `5` has two prime factors
  have htwo : ∀ t : ℕ, 2 ≤ t → 5 ∣ t → (∀ k, t ≠ 5 ^ k) → 2 ≤ ω t := by
    intro t ht h5t hnot
    by_contra hlt
    have h1 : ω t = 1 := by have := hpos t ht; omega
    rw [ArithmeticFunction.cardDistinctFactors_eq_one_iff, isPrimePow_nat_iff] at h1
    obtain ⟨p, k, hp, _, hpk⟩ := h1
    have hp5 : p = 5 := by
      have : 5 ∣ p := Nat.prime_five.dvd_of_dvd_pow (hpk ▸ h5t)
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp this).symm
    exact hnot k (by rw [← hpk, hp5])
  rcases (Nat.Prime.dvd_mul Nat.prime_five).mp h5 with h | h
  · have hA : 2 ≤ ω (s + 1) := by
      refine htwo (s + 1) (by omega) h fun k hk => ?_
      obtain ⟨hx3, hy1⟩ := sunit_plus hx hy hk
      rw [hx3, hy1] at hs
      omega
    have hB := hpos (s - 1) (by omega)
    omega
  · have hA : 2 ≤ ω (s - 1) := by
      refine htwo (s - 1) (by omega) h fun k hk => ?_
      have : 2 ^ x * 3 ^ y = 5 ^ k + 1 := by omega
      obtain ⟨hx1, hy1⟩ := sunit_minus hx hy this
      rw [hx1, hy1] at hs
      omega
    have hB := hpos (s + 1) (by omega)
    omega

theorem main : H1 → H2 → OMA.R_Erdos891_erdos_891_variants_case_k_2_R1.H3 := by
  intro h1 h2
  filter_upwards [h1, h2, eventually_ge_atTop 577] with M hM1 hM2 hM a b ha hb hab hea heb
  obtain ⟨x, hx⟩ := hea
  obtain ⟨y, hy⟩ := heb
  have hsq : M = (2 ^ x * 3 ^ y) ^ 2 := by
    rw [hab, hx, hy]
    ring
  have hbig : 24 < 2 ^ x * 3 ^ y := by
    by_contra h
    rw [not_lt] at h
    have h2 : (2 ^ x * 3 ^ y) ^ 2 ≤ 24 ^ 2 := Nat.pow_le_pow_left h 2
    rw [← hsq] at h2
    omega
  rcases Nat.even_or_odd x with hxe | hxo <;> rcases Nat.even_or_odd y with hye | hyo
  · -- `a`, `b` both `0 (mod 4)`: `M` is a fourth power
    refine ⟨M - 1, by rw [mem_Ico]; omega, ?_⟩
    rw [hsq]
    exact omega_three x y (by omega) (by omega)
      (by rw [Nat.even_iff.mp hxe, Nat.even_iff.mp hye]) hbig
  · exact hM1 a b ha hb hab (by obtain ⟨u, hu⟩ := hxe; omega) (by obtain ⟨v, hv⟩ := hyo; omega)
  · exact hM2 a b ha hb hab (by obtain ⟨u, hu⟩ := hxo; omega) (by obtain ⟨v, hv⟩ := hye; omega)
  · -- `a`, `b` both `2 (mod 4)`: `M` is `36` times a fourth power
    refine ⟨M - 1, by rw [mem_Ico]; omega, ?_⟩
    rw [hsq]
    exact omega_three x y (by omega) (by omega)
      (by rw [Nat.odd_iff.mp hxo, Nat.odd_iff.mp hyo]) hbig

end OMA.R_Erdos891_erdos_891_variants_case_k_2_R1_H3_R1
