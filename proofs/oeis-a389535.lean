import OMAStatements.S_oeis_a389535
import Mathlib

namespace OeisA389535Proof

private lemma five_eq_zero_ps5 : (5 : PowerSeries (ZMod 5)) = 0 := by
  ext k
  rw [show (5 : PowerSeries (ZMod 5)) = PowerSeries.C 5 from rfl, PowerSeries.coeff_C]
  split_ifs <;> simp [show (5 : ZMod 5) = 0 by decide]

private lemma add_pow5_ps5 (u v : PowerSeries (ZMod 5)) : (u + v) ^ 5 = u ^ 5 + v ^ 5 := by
  calc (u + v) ^ 5 = u ^ 5 + v ^ 5 +
        5 * (u ^ 4 * v + 2 * u ^ 3 * v ^ 2 + 2 * u ^ 2 * v ^ 3 + u * v ^ 4) := by ring
    _ = u ^ 5 + v ^ 5 := by rw [five_eq_zero_ps5, zero_mul, add_zero]

private lemma finset_sum_pow5_ps5 {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → PowerSeries (ZMod 5)) : (∑ i ∈ s, f i) ^ 5 = ∑ i ∈ s, (f i) ^ 5 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, add_pow5_ps5, ih, Finset.sum_insert ha]

private lemma coeff_pow5_mod5 (f : PowerSeries (ZMod 5)) (n : ℕ) :
    PowerSeries.coeff n (f ^ 5) = if 5 ∣ n then PowerSeries.coeff (n / 5) f else 0 := by
  let P : PowerSeries (ZMod 5) :=
    ∑ i ∈ Finset.range (n + 1), PowerSeries.C (PowerSeries.coeff i f) * PowerSeries.X ^ i
  let R : PowerSeries (ZMod 5) := f - P
  have hP_coeff : ∀ j ≤ n, PowerSeries.coeff j P = PowerSeries.coeff j f := by
    intro j hj
    dsimp only [P]
    rw [map_sum]
    simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hne; simp [Ne.symm hne]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have hR_zero : ∀ j ≤ n, PowerSeries.coeff j R = 0 := fun j hj => by
    dsimp only [R]; rw [map_sub, hP_coeff j hj, sub_self]
  have hR_mul_zero : ∀ g : PowerSeries (ZMod 5), PowerSeries.coeff n (R * g) = 0 := by
    intro g
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i R * PowerSeries.coeff j g)]
    apply Finset.sum_eq_zero
    intro i hi; rw [Finset.mem_range] at hi; rw [hR_zero i (by omega), zero_mul]
  have hf_eq : f = P + R := by dsimp only [R]; ring
  have hf5 : PowerSeries.coeff n (f ^ 5) = PowerSeries.coeff n (P ^ 5) := by
    rw [hf_eq, add_pow5_ps5, map_add, show R ^ 5 = R * R ^ 4 by ring, hR_mul_zero, add_zero]
  rw [hf5]
  dsimp only [P]
  rw [finset_sum_pow5_ps5, map_sum]
  have hterm : ∀ i : ℕ,
      PowerSeries.coeff n ((PowerSeries.C (PowerSeries.coeff i f) * PowerSeries.X ^ i) ^ 5) =
        if n = 5 * i then PowerSeries.coeff i f else 0 := by
    intro i
    rw [mul_pow, ← map_pow, ← pow_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow,
      show i * 5 = 5 * i by ring]
    have hpow5 : ∀ x : ZMod 5, x ^ 5 = x := by decide
    rw [hpow5]
    split_ifs <;> simp
  simp_rw [hterm]
  by_cases h5 : 5 ∣ n
  · rw [if_pos h5, Finset.sum_eq_single (n / 5)]
    · rw [if_pos (by omega)]
    · intro i _ hne; rw [if_neg (by omega)]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · rw [if_neg h5]
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg (by omega)]

end OeisA389535Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a389535.main := by
  intro A _ n
  change PowerSeries.coeff n (A ^ 5) ≡
    (if 5 ∣ n then PowerSeries.coeff (n / 5) A else 0) [ZMOD ((5 : ℕ) : ℤ)]
  rw [← ZMod.intCast_eq_intCast_iff]
  have hc := OeisA389535Proof.coeff_pow5_mod5 (PowerSeries.map (Int.castRingHom (ZMod 5)) A) n
  rw [← map_pow] at hc
  simp only [PowerSeries.coeff_map, Int.coe_castRingHom] at hc
  rw [hc]
  split_ifs <;> simp
