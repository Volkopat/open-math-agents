import OMAReductions.R_Erdos687_erdos_687_parts_iii_R3

/-!
# Reduction `Erdos687.erdos_687.parts.iii.R3.H2.R1`

Credit: @sanchan

Advances the prime-gap cutoff in `Erdos687.parts.iii.R3` from `y^(3/2)` to `y^(19/10)` using
Baker-Harman-Pintz's 2001 prime-gap theorem (`H1`, exponent `21/40 = 0.525`, since
`19/10 * 21/40 = 399/400 < 1`), proves the exact combinatorial lower-bound sieve main-term
plus remainder decomposition and `< 1` interval-multiple remainder error bound, and reduces
the remaining huge offsets (`y^19 < b^10`) to lower-bound sieve positivity (`H2`, lossless
via the Mobius function).
-/

open Filter

namespace OMA.R_Erdos687_erdos_687_parts_iii_R3_H2_R1

/-- Baker-Harman-Pintz (2001) prime-gap theorem: every sufficiently large interval
`(n, n + n^(21/40)]` contains a prime (written in `ℕ` as `(p - n)^40 ≤ n^21`).
Closes all medium offsets `y^(3/2) < b ≤ y^(19/10)` since `19/10 * 21/40 = 399/400 < 1`. -/
def H1 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ n < p ∧ (p - n) ^ 40 ≤ n ^ 21

/-- Lower-bound sieve positivity on huge offsets `y^19 < b^10` (`2 * b + y < primorial x`):
for every `ε > 0` and all sufficiently large `x`, letting `y = ⌈x^(1 + ε)⌉₊` and
`P = primorial x`, there exists a lower-bound sieve weight `lam : ℕ → ℝ` on `P`
(`lam 1 = 1` and `∑_{d ∣ n} lam d ≤ 0` for all `1 < n ∣ P`) whose main term
`y * ∑_{d ∣ P} lam d / d` plus signed remainder `∑_{d ∣ P} lam d * r(b, y, d)` is
strictly positive. Lossless via the Mobius function `lam = μ`. -/
def H2 : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ x : ℕ in atTop,
    let y := ⌈(x : ℝ) ^ (1 + ε)⌉₊
    let P := primorial x
    ∀ b : ℕ, y ^ 19 < b ^ 10 → 2 * b + y < P →
      ∃ lam : ℕ → ℝ, lam 1 = 1 ∧
        (∀ n ∈ P.divisors, 1 < n → ∑ d ∈ n.divisors, lam d ≤ 0) ∧
        0 < (y : ℝ) * (∑ d ∈ P.divisors, lam d / (d : ℝ)) +
          ∑ d ∈ P.divisors, lam d *
            ((((Finset.Icc 1 y).filter (fun m => d ∣ b + m)).card : ℝ) - (y : ℝ) / (d : ℝ))

/-- Exact count of multiples of `d > 0` in the shifted interval `[b + 1, b + y]`. -/
theorem count_multiples_Icc {b y d : ℕ} (hd : 0 < d) :
    ((Finset.Icc 1 y).filter (fun m => d ∣ b + m)).card = (b + y) / d - b / d := by
  let S : Finset ℕ := (Finset.Icc 1 y).filter (fun m => d ∣ b + m)
  let T : Finset ℕ := Finset.Ioc (b / d) ((b + y) / d)
  have hTmem : ∀ k : ℕ, k ∈ T ↔ b < k * d ∧ k * d ≤ b + y := by
    intro k
    simp only [T, Finset.mem_Ioc, Nat.le_div_iff_mul_le hd]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      by_contra hle
      push Not at hle
      have : k ≤ b / d := (Nat.le_div_iff_mul_le hd).mpr hle
      omega
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      by_contra hle
      push Not at hle
      have : k * d ≤ b := (Nat.le_div_iff_mul_le hd).mp hle
      omega
  have hSeq : S = T.image (fun k => k * d - b) := by
    ext m
    simp only [S, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hm1, hmy⟩, ⟨k, hk⟩⟩
      have hkd : k * d = b + m := by rw [mul_comm]; exact hk.symm
      refine ⟨k, (hTmem k).mpr ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨k, hkT, rfl⟩
      obtain ⟨h1, h2⟩ := (hTmem k).mp hkT
      refine ⟨⟨by omega, by omega⟩, ⟨k, by rw [Nat.add_sub_cancel' (le_of_lt h1), mul_comm]⟩⟩
  have hinj : Set.InjOn (fun k => k * d - b) (T : Set ℕ) := by
    intro k1 hk1 k2 hk2 heq
    dsimp only at heq
    have h1 := ((hTmem k1).mp (Finset.mem_coe.mp hk1)).1
    have h2 := ((hTmem k2).mp (Finset.mem_coe.mp hk2)).1
    have hmul : k1 * d = k2 * d := by omega
    exact Nat.eq_of_mul_eq_mul_right hd hmul
  change S.card = (b + y) / d - b / d
  rw [hSeq, Finset.card_image_of_injOn hinj]
  exact Nat.card_Ioc (b / d) ((b + y) / d)

/-- Standard sieve remainder error bound: the count of multiples of `d > 0` in
`[b + 1, b + y]` differs from `y / d` by strictly less than `1`. -/
theorem count_multiples_error_lt_one {b y d : ℕ} (hd : 0 < d) :
    |(((Finset.Icc 1 y).filter (fun m => d ∣ b + m)).card : ℝ) - (y : ℝ) / (d : ℝ)| < 1 := by
  rw [count_multiples_Icc hd]
  have hq : b / d ≤ (b + y) / d := Nat.div_le_div_right (Nat.le_add_right b y)
  have h1 : d * (b / d) + b % d = b := Nat.div_add_mod b d
  have h2 : d * ((b + y) / d) + (b + y) % d = b + y := Nat.div_add_mod (b + y) d
  have hr1 : b % d < d := Nat.mod_lt b hd
  have hr2 : (b + y) % d < d := Nat.mod_lt (b + y) hd
  have hdR : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have h1R : (d : ℝ) * (b / d : ℕ) + (b % d : ℕ) = (b : ℝ) := by exact_mod_cast h1
  have h2R : (d : ℝ) * ((b + y) / d : ℕ) + ((b + y) % d : ℕ) = (b : ℝ) + (y : ℝ) := by
    exact_mod_cast h2
  have hsub : (((b + y) / d - b / d : ℕ) : ℝ) = ((b + y) / d : ℕ) - (b / d : ℕ) :=
    Nat.cast_sub hq
  have hr1_lt : ((b % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast hr1
  have hr2_lt : (((b + y) % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast hr2
  have hr1_nn : (0 : ℝ) ≤ ((b % d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hr2_nn : (0 : ℝ) ≤ (((b + y) % d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hnum : (d : ℝ) * ((((b + y) / d - b / d : ℕ) : ℝ) - (y : ℝ) / (d : ℝ)) =
      ((b % d : ℕ) : ℝ) - (((b + y) % d : ℕ) : ℝ) := by
    rw [hsub]
    field_simp [hdR.ne']
    linarith
  rw [abs_lt]
  constructor
  · have hlt : -(d : ℝ) < (d : ℝ) * ((((b + y) / d - b / d : ℕ) : ℝ) - (y : ℝ) / (d : ℝ)) := by
      linarith
    nlinarith
  · have hlt : (d : ℝ) * ((((b + y) / d - b / d : ℕ) : ℝ) - (y : ℝ) / (d : ℝ)) < (d : ℝ) := by
      linarith
    nlinarith

/-- Exact combinatorial sieve swap identity decomposing the weighted divisor sum over
`[b + 1, b + y]` into main term `y * ∑ lam d / d` plus signed remainder. -/
theorem sieve_swap_identity {b y P : ℕ} (hP : 0 < P) (lam : ℕ → ℝ) :
    ∑ m ∈ Finset.Icc 1 y, ∑ d ∈ (Nat.gcd (b + m) P).divisors, lam d =
      (y : ℝ) * (∑ d ∈ P.divisors, lam d / (d : ℝ)) +
        ∑ d ∈ P.divisors, lam d *
          ((((Finset.Icc 1 y).filter (fun m => d ∣ b + m)).card : ℝ) - (y : ℝ) / (d : ℝ)) := by
  have hdiv : ∀ m : ℕ, (Nat.gcd (b + m) P).divisors = P.divisors.filter (fun d => d ∣ b + m) := by
    intro m
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
    have hg0 : Nat.gcd (b + m) P ≠ 0 := Nat.gcd_ne_zero_right hP.ne'
    have hP0 : P ≠ 0 := hP.ne'
    tauto
  have hswap : ∑ m ∈ Finset.Icc 1 y, ∑ d ∈ (Nat.gcd (b + m) P).divisors, lam d =
      ∑ d ∈ P.divisors, lam d * (((Finset.Icc 1 y).filter (fun m => d ∣ b + m)).card : ℝ) := by
    calc ∑ m ∈ Finset.Icc 1 y, ∑ d ∈ (Nat.gcd (b + m) P).divisors, lam d
        = ∑ m ∈ Finset.Icc 1 y, ∑ d ∈ P.divisors, if d ∣ b + m then lam d else 0 := by
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [hdiv m, Finset.sum_filter]
      _ = ∑ d ∈ P.divisors, ∑ m ∈ Finset.Icc 1 y, if d ∣ b + m then lam d else 0 :=
            Finset.sum_comm
      _ = ∑ d ∈ P.divisors, lam d * (((Finset.Icc 1 y).filter (fun m => d ∣ b + m)).card : ℝ) := by
            refine Finset.sum_congr rfl fun d _ => ?_
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hswap, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => by ring

/-- Fundamental lower-bound sieve criterion: any lower-bound sieve weight `lam` on `P > 0`
with strictly positive main term plus remainder guarantees an integer in `[b + 1, b + y]`
coprime to `P`. -/
theorem lower_sieve_exists_coprime {b y P : ℕ} (hP : 0 < P) (lam : ℕ → ℝ)
    (hneg : ∀ n ∈ P.divisors, 1 < n → ∑ d ∈ n.divisors, lam d ≤ 0)
    (hpos : 0 < (y : ℝ) * (∑ d ∈ P.divisors, lam d / (d : ℝ)) +
      ∑ d ∈ P.divisors, lam d *
        ((((Finset.Icc 1 y).filter (fun m => d ∣ b + m)).card : ℝ) - (y : ℝ) / (d : ℝ))) :
    ∃ m ∈ Finset.Icc 1 y, (b + m).Coprime P := by
  by_contra hnone
  push Not at hnone
  have hle : ∑ m ∈ Finset.Icc 1 y, ∑ d ∈ (Nat.gcd (b + m) P).divisors, lam d ≤ 0 := by
    refine Finset.sum_nonpos fun m hm => ?_
    have hnc : ¬ (b + m).Coprime P := hnone m hm
    have hgne1 : Nat.gcd (b + m) P ≠ 1 := hnc
    have hgpos : 0 < Nat.gcd (b + m) P := Nat.gcd_pos_of_pos_right _ hP
    have hg1 : 1 < Nat.gcd (b + m) P := by omega
    have hgdvd : Nat.gcd (b + m) P ∈ P.divisors :=
      Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hP.ne'⟩
    exact hneg _ hgdvd hg1
  rw [sieve_swap_identity hP lam] at hle
  linarith

/-- Any prime `p > x` is coprime to `primorial x`. -/
theorem coprime_primorial_of_prime_gt {x p : ℕ} (hp : p.Prime) (hxp : x < p) :
    p.Coprime (primorial x) :=
  hp.coprime_iff_not_dvd.mpr fun hd => (not_le.mpr hxp) (hp.dvd_primorial_iff.mp hd)

theorem main : H1 → H2 → OMA.R_Erdos687_erdos_687_parts_iii_R3.H2 := by
  intro hBHP hSieve ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp hBHP
  filter_upwards [hSieve ε hε, eventually_ge_atTop (max N 2)] with x hsieve hx
  set y := ⌈(x : ℝ) ^ (1 + ε)⌉₊ with hydef
  have hxN : N ≤ x := le_trans (le_max_left N 2) hx
  have hx2 : 2 ≤ x := le_trans (le_max_right N 2) hx
  have hxy : x ≤ y := by
    have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
    have hpow : (x : ℝ) ≤ (x : ℝ) ^ (1 + ε) := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hx1 (by linarith : (1 : ℝ) ≤ 1 + ε)
    have hceil : (x : ℝ) ≤ (y : ℝ) := hpow.trans (Nat.le_ceil _)
    exact_mod_cast hceil
  have hy2 : 2 ≤ y := le_trans hx2 hxy
  intro b hb_low hb_half
  by_cases hhuge : y ^ 19 < b ^ 10
  · obtain ⟨lam, _, hneg, hpos⟩ := hsieve b hhuge hb_half
    have hPpos : 0 < primorial x := by omega
    exact lower_sieve_exists_coprime hPpos lam hneg hpos
  · push Not at hhuge
    have hyb : y < b := by
      by_contra hle
      push Not at hle
      have hb2 : b ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left hle 2
      have hy23 : y ^ 2 < y ^ 3 := by nlinarith
      omega
    have hNb : N ≤ b := by omega
    obtain ⟨p, hp, hbp, hgap⟩ := hN b hNb
    have hp_le : p - b ≤ y := by
      have h400 : (p - b) ^ 400 ≤ y ^ 400 := by
        calc (p - b) ^ 400
            = ((p - b) ^ 40) ^ 10 := by rw [← pow_mul]
          _ ≤ (b ^ 21) ^ 10 := Nat.pow_le_pow_left hgap 10
          _ = (b ^ 10) ^ 21 := by rw [← pow_mul, ← pow_mul]
          _ ≤ (y ^ 19) ^ 21 := Nat.pow_le_pow_left hhuge 21
          _ = y ^ 399 := by rw [← pow_mul]
          _ ≤ y ^ 400 := Nat.pow_le_pow_right (by omega : 1 ≤ y) (by decide)
      exact (Nat.pow_le_pow_iff_left (by decide : 400 ≠ 0)).mp h400
    refine ⟨p - b, Finset.mem_Icc.mpr ⟨by omega, hp_le⟩, ?_⟩
    rw [show b + (p - b) = p by omega]
    exact coprime_primorial_of_prime_gt hp (by omega)

end OMA.R_Erdos687_erdos_687_parts_iii_R3_H2_R1
