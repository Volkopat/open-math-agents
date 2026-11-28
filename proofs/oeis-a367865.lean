import OMAStatements.S_oeis_a367865

-- rad(nk)/rad(k) = rad(n)/rad(gcd(n,k)), so the right side is rad(n)^2/n * Σ_{d|n} φ(n/d)/rad(d).
-- Both sides are multiplicative in n and equal p^2 - p + 1 at every prime power.

namespace OMA.A367865
open ArithmeticFunction OMA.S_oeis_a367865

def af (u : ℕ → ℚ) : ArithmeticFunction ℚ := ⟨fun n => if n = 0 then 0 else u n, by simp⟩

lemma af_apply (u : ℕ → ℚ) {n : ℕ} (hn : n ≠ 0) : af u n = u n := by
  show (if n = 0 then 0 else u n) = u n
  rw [if_neg hn]

lemma conv (u v : ℕ → ℚ) {n : ℕ} :
    (af u * af v) n = ∑ d ∈ n.divisors, u d * v (n / d) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => af u x * af v y)]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  have hq : n / d ≠ 0 := (Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_ne_zero hd0)).ne'
  rw [af_apply u hd0, af_apply v hq]

lemma mult_af (u : ℕ → ℚ) (h1 : u 1 = 1)
    (hm : ∀ m n : ℕ, m ≠ 0 → n ≠ 0 → Nat.Coprime m n → u (m * n) = u m * u n) :
    (af u).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by rw [af_apply u one_ne_zero, h1], fun {m n} hm0 hn0 hmn => ?_⟩
  rw [af_apply u (mul_ne_zero hm0 hn0), af_apply u hm0, af_apply u hn0, hm m n hm0 hn0 hmn]

lemma gcd_sum (G : ℕ → ℚ) (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.Icc 1 n, G (Nat.gcd k n) = ∑ d ∈ n.divisors, G d * (Nat.totient (n / d) : ℚ) := by
  have e1 : ∑ k ∈ Finset.Icc 1 n, G (Nat.gcd k n) = ∑ k ∈ Finset.range n, G (Nat.gcd n k) := by
    rw [show Finset.Icc 1 n = Finset.Ico 1 (n + 1) from rfl, Finset.sum_Ico_eq_sum_range,
      show n + 1 - 1 = n by omega]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [Nat.gcd_zero_right]
    congr 1
    · apply Finset.sum_congr rfl
      intro k _
      rw [add_comm 1 k, Nat.gcd_comm (k + 1)]
    · rw [add_comm 1 m, Nat.gcd_self]
  rw [e1, ← Finset.sum_fiberwise_of_maps_to (s := Finset.range n) (t := n.divisors)
    (g := fun k => Nat.gcd n k) (fun k _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left n k, hn.ne'⟩)]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_congr rfl (fun k hk => by rw [(Finset.mem_filter.mp hk).2]), Finset.sum_const,
    Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd), nsmul_eq_mul, mul_comm]

lemma rad_pos (n : ℕ) : 0 < rad n := Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos

lemma rad_mul (m n : ℕ) (h : Nat.Coprime m n) : rad (m * n) = rad m * rad n := by
  rw [rad, rad, rad, h.primeFactors_mul, Finset.prod_union h.disjoint_primeFactors]

lemma rad_pp (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) : rad (p ^ k) = p := by
  rw [rad, Nat.primeFactors_prime_pow hk hp, Finset.prod_singleton]

lemma rad_one : rad 1 = 1 := by simp [rad]

lemma rad_gcd (n k : ℕ) : rad (Nat.gcd n k) * rad (n * k) = rad n * rad k :=
  Nat.prod_primeFactors_gcd_mul_prod_primeFactors_mul n k id

lemma sum_phi_pp (p k : ℕ) (hp : p.Prime) :
    ∑ j ∈ Finset.range (k + 1), (Nat.totient (p ^ j) : ℚ) = (p : ℚ) ^ k := by
  have := Nat.sum_totient (p ^ k)
  rw [Nat.sum_divisors_prime_pow hp] at this
  exact_mod_cast this

end OMA.A367865

open OMA.A367865 OMA.S_oeis_a367865 ArithmeticFunction in
theorem OMA.solution : type_of% @OMA.S_oeis_a367865.main := by
  intro n hn
  set h : ℕ → ℚ := fun d => (d : ℚ) * (d.totient : ℚ) * ((ArithmeticFunction.moebius d : ℤ) : ℚ) ^ 2
  set R1 : ℕ → ℚ := fun n => (rad n : ℚ) ^ 2 / n
  set R2 : ℕ → ℚ := fun d => 1 / (rad d : ℚ)
  set P : ℕ → ℚ := fun n => (Nat.totient n : ℚ)
  have hH : (af h).IsMultiplicative := by
    apply mult_af
    · simp [h]
    · intro m k _ _ hmk
      simp only [h]
      rw [Nat.totient_mul hmk, isMultiplicative_moebius.map_mul_of_coprime hmk]
      push_cast; ring
  have hZ : (af (fun _ => 1)).IsMultiplicative := mult_af _ rfl (fun _ _ _ _ _ => by ring)
  have hR1 : (af R1).IsMultiplicative := by
    apply mult_af
    · simp [R1, rad_one]
    · intro m k hm hk hmk
      simp only [R1]
      rw [rad_mul m k hmk]
      push_cast
      field_simp
  have hR2 : (af R2).IsMultiplicative := by
    apply mult_af
    · simp [R2, rad_one]
    · intro m k _ _ hmk
      simp only [R2]
      rw [rad_mul m k hmk]
      push_cast
      field_simp
  have hP : (af P).IsMultiplicative := by
    apply mult_af
    · simp [P]
    · intro m k _ _ hmk
      simp only [P]
      rw [Nat.totient_mul hmk]; push_cast; ring
  have key : af h * af (fun _ => 1) = (af R1).pmul (af R2 * af P) := by
    rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ (hH.mul hZ) _ (hR1.pmul (hR2.mul hP))]
    intro p i hp
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [pow_zero, (hH.mul hZ).map_one, (hR1.pmul (hR2.mul hP)).map_one]
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [pmul_apply, conv, conv, af_apply _ (pow_ne_zero _ hp.ne_zero),
      Nat.sum_divisors_prime_pow hp, Nat.sum_divisors_prime_pow hp]
    -- left side
    have hl : ∑ j ∈ Finset.range (k + 1 + 1), h (p ^ j) * 1 = 1 + (p : ℚ) * ((p : ℚ) - 1) := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      have hz : ∀ j ∈ Finset.range k, h (p ^ (j + 1 + 1)) * 1 = 0 := by
        intro j _
        simp only [h, mul_one]
        rw [moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
        simp
      rw [Finset.sum_congr rfl hz, Finset.sum_const_zero]
      simp only [h, zero_add, pow_zero, pow_one, mul_one, Nat.totient_one, moebius_apply_one,
        moebius_apply_prime hp, Nat.totient_prime hp]
      rw [Nat.cast_sub hp.one_le]
      push_cast; ring
    rw [hl]
    -- right side
    have hr : ∑ j ∈ Finset.range (k + 1 + 1), R2 (p ^ j) * P (p ^ (k + 1) / p ^ j) =
        (p : ℚ) ^ k * ((p : ℚ) - 1) + (p : ℚ) ^ k / p := by
      rw [Finset.sum_range_succ']
      have hs : ∀ j ∈ Finset.range (k + 1), R2 (p ^ (j + 1)) * P (p ^ (k + 1) / p ^ (j + 1)) =
          (1 / (p : ℚ)) * (Nat.totient (p ^ (k - j)) : ℚ) := by
        intro j hj
        rw [Finset.mem_range] at hj
        simp only [R2, P]
        rw [rad_pp p _ hp (by omega), Nat.pow_div (by omega) hp.pos,
          show k + 1 - (j + 1) = k - j by omega]
      rw [Finset.sum_congr rfl hs, ← Finset.mul_sum]
      have hrefl : ∑ j ∈ Finset.range (k + 1), (Nat.totient (p ^ (k - j)) : ℚ) =
          ∑ j ∈ Finset.range (k + 1), (Nat.totient (p ^ j) : ℚ) := by
        rw [← Finset.sum_range_reflect (fun j => (Nat.totient (p ^ j) : ℚ)) (k + 1)]
        apply Finset.sum_congr rfl
        intro j _
        rw [show k + 1 - 1 - j = k - j by omega]
      rw [hrefl, sum_phi_pp p k hp]
      simp only [R2, P, pow_zero, rad_one, Nat.div_one]
      rw [Nat.totient_prime_pow hp (by omega), Nat.cast_mul, Nat.cast_sub hp.one_le]
      push_cast
      try simp only [Nat.add_sub_cancel]
      ring
    rw [hr]
    simp only [R1]
    rw [rad_pp p _ hp (by omega)]
    push_cast
    field_simp
    ring
  -- conclude
  have hn0 : n ≠ 0 := by omega
  have hl := DFunLike.congr_fun key n
  rw [pmul_apply, conv, conv, af_apply _ hn0] at hl
  have hlhs : (a n : ℚ) = ∑ d ∈ n.divisors, h d * 1 := by
    simp only [a, h, mul_one]; push_cast; rfl
  rw [hlhs, hl]
  have hrad : ∀ k ∈ Finset.Icc 1 n, (rad (n * k) : ℚ) / (rad k : ℚ) =
      (rad n : ℚ) * (1 / (rad (Nat.gcd k n) : ℚ)) := by
    intro k _
    have e := rad_gcd n k
    have h1 : (rad (Nat.gcd n k) : ℚ) ≠ 0 := by exact_mod_cast (rad_pos _).ne'
    have h2 : (rad k : ℚ) ≠ 0 := by exact_mod_cast (rad_pos _).ne'
    rw [Nat.gcd_comm k n]
    have e' : (rad (Nat.gcd n k) : ℚ) * rad (n * k) = rad n * rad k := by exact_mod_cast e
    field_simp
    linear_combination e'
  rw [Finset.sum_congr rfl hrad, ← Finset.mul_sum,
    gcd_sum (fun d => 1 / (rad d : ℚ)) n (by omega)]
  simp only [R1, R2, P]
  have : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  field_simp

