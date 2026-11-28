import OMAStatements.S_oeis_a129654
import Mathlib

namespace R129654
open OMA.S_oeis_a129654
open PowerSeries

theorem tri_pos (k : ℕ) (hk : 1 ≤ k) : 0 < k * (k + 1) / 2 := by
  have h : 1 * 2 ≤ k * (k + 1) := Nat.mul_le_mul hk (by omega)
  omega

theorem pol_eq (t k : ℕ) :
    polygonal (t + 2) (k + 1) = ((t * (k * (k + 1) / 2) + k + 1 : ℕ) : ℤ) := by
  have h2 : 2 * (k * (k + 1) / 2) = k * (k + 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self k)
  obtain ⟨T, hT⟩ : ∃ T, k * (k + 1) / 2 = T := ⟨_, rfl⟩
  rw [hT] at h2 ⊢
  have h2' : (2 : ℤ) * T = k * (k + 1) := by exact_mod_cast h2
  have key : ((k + 1 : ℕ) : ℤ) * ((((t + 2 : ℕ) : ℤ) - 2) * ((k + 1 : ℕ) : ℤ)
      - (((t + 2 : ℕ) : ℤ) - 4)) = 2 * ((t * T + k + 1 : ℕ) : ℤ) := by
    push_cast
    linear_combination (-(t : ℤ)) * h2'
  have e : polygonal (t + 2) (k + 1) = ((k + 1 : ℕ) : ℤ) * ((((t + 2 : ℕ) : ℤ) - 2)
      * ((k + 1 : ℕ) : ℤ) - (((t + 2 : ℕ) : ℤ) - 4)) / 2 := rfl
  rw [e, key]
  first
  | exact Int.mul_ediv_cancel_left _ two_ne_zero
  | omega
  | simp

theorem inv_eq (d : ℕ) (hd : 0 < d) :
    ((1 : ℚ⟦X⟧) - X ^ d)⁻¹ = PowerSeries.mk (fun i => if d ∣ i then (1 : ℚ) else 0) := by
  have h0 : PowerSeries.constantCoeff ((1 : ℚ⟦X⟧) - X ^ d) ≠ 0 := by
    first
    | (rw [map_sub, map_one, map_pow, PowerSeries.constantCoeff_X, zero_pow hd.ne']; norm_num)
    | simp [hd.ne']
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one h0]
  refine PowerSeries.ext (fun n => ?_)
  rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk,
    PowerSeries.coeff_mk, PowerSeries.coeff_one]
  try dsimp only
  by_cases h : d ≤ n
  · have hn : n ≠ 0 := by omega
    have hiff : d ∣ n - d ↔ d ∣ n := by
      first
      | exact Nat.dvd_sub_iff_left h (dvd_refl d)
      | exact ⟨fun h1 => by simpa [Nat.sub_add_cancel h] using Nat.dvd_add h1 (dvd_refl d),
          fun h1 => Nat.dvd_sub h1 (dvd_refl d)⟩
    rw [if_pos h, if_neg hn]
    by_cases h2 : d ∣ n
    · rw [if_pos h2, if_pos (hiff.2 h2)] <;> norm_num
    · rw [if_neg h2, if_neg (fun h3 => h2 (hiff.1 h3))] <;> norm_num
  · rw [if_neg h, sub_zero]
    by_cases hn : n = 0
    · subst hn
      simp
    · rw [if_neg hn, if_neg (fun h3 => h (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h3))]

theorem coeff_eq (n : ℕ) :
    PowerSeries.coeff n
      (∑ k ∈ Finset.Icc 1 n, (X : ℚ⟦X⟧) * X ^ k * (1 - X ^ (k * (k + 1) / 2))⁻¹)
      = (((Finset.Icc 1 n).filter
          (fun k => k + 1 ≤ n ∧ k * (k + 1) / 2 ∣ n - (k + 1))).card : ℚ) := by
  rw [Finset.natCast_card_filter, map_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  try dsimp only
  rw [inv_eq _ (tri_pos k hk1), show (X : ℚ⟦X⟧) * X ^ k = X ^ (k + 1) by ring,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk]
  try dsimp only
  first
  | (rw [ite_and]; done)
  | exact (ite_and _ _ _ _).symm
  | (by_cases h1 : k + 1 ≤ n <;> by_cases h2 : k * (k + 1) / 2 ∣ n - (k + 1) <;>
      simp only [h1, h2, and_true, and_false, true_and, false_and, if_true, if_false])
  | (split_ifs <;> simp_all)

theorem g_inj (n : ℕ) :
    Function.Injective (fun k : ℕ => ((n - (k + 1)) / (k * (k + 1) / 2) + 2, k + 1)) := by
  intro x y h
  have h2 := congrArg Prod.snd h
  change x + 1 = y + 1 at h2
  omega

theorem set_eq (n : ℕ) :
    {p : ℕ × ℕ | 1 < p.1 ∧ 1 < p.2 ∧ polygonal p.1 p.2 = n}
      = (fun k : ℕ => ((n - (k + 1)) / (k * (k + 1) / 2) + 2, k + 1)) ''
        ((((Finset.Icc 1 n).filter
          (fun k => k + 1 ≤ n ∧ k * (k + 1) / 2 ∣ n - (k + 1))) : Finset ℕ) : Set ℕ) := by
  apply Set.Subset.antisymm
  · rintro ⟨m, r⟩ ⟨hm, hr, hp⟩
    change 1 < m at hm
    change 1 < r at hr
    change polygonal m r = (n : ℤ) at hp
    obtain ⟨t, rfl⟩ : ∃ t, m = t + 2 := ⟨m - 2, by omega⟩
    obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
    have hk : 1 ≤ k := by omega
    have hT := tri_pos k hk
    rw [pol_eq] at hp
    have hp' : t * (k * (k + 1) / 2) + k + 1 = n := by
      first
      | exact_mod_cast hp
      | exact Nat.cast_injective hp
    have hsub : n - (k + 1) = t * (k * (k + 1) / 2) := by omega
    refine (Set.mem_image _ _ _).2 ⟨k, ?_, ?_⟩
    · exact Finset.mem_coe.2 (Finset.mem_filter.2
        ⟨Finset.mem_Icc.2 ⟨hk, by omega⟩, by omega, Dvd.intro_left t hsub.symm⟩)
    · show ((n - (k + 1)) / (k * (k + 1) / 2) + 2, k + 1) = (t + 2, k + 1)
      rw [hsub, Nat.mul_div_cancel _ hT]
  · rintro ⟨m, r⟩ ⟨k, hk, he⟩
    obtain ⟨hkI, hk2, c, hc⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hk)
    obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.1 hkI
    have hT := tri_pos k hk1
    have he' : ((n - (k + 1)) / (k * (k + 1) / 2) + 2, k + 1) = (m, r) := he
    rw [hc, Nat.mul_div_cancel_left _ hT] at he'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he'
    show 1 < c + 2 ∧ 1 < k + 1 ∧ polygonal (c + 2) (k + 1) = (n : ℤ)
    refine ⟨by omega, by omega, ?_⟩
    have hmc := Nat.mul_comm c (k * (k + 1) / 2)
    have hcn : c * (k * (k + 1) / 2) + k + 1 = n := by omega
    rw [pol_eq, hcn]

theorem a_eq (n : ℕ) : OMA.S_oeis_a129654.a n
    = ((Finset.Icc 1 n).filter (fun k => k + 1 ≤ n ∧ k * (k + 1) / 2 ∣ n - (k + 1))).card := by
  show Set.ncard {p : ℕ × ℕ | 1 < p.1 ∧ 1 < p.2 ∧ polygonal p.1 p.2 = n} = _
  rw [set_eq n, Set.ncard_image_of_injective _ (g_inj n), Set.ncard_coe_finset]

end R129654

theorem OMA.solution : type_of% @OMA.S_oeis_a129654.main := by
  intro n _
  rw [R129654.a_eq n, R129654.coeff_eq n]
