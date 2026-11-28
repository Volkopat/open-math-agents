import OMAStatements.S_oeis_a218980

open Finset OMA.S_oeis_a218980

namespace OMA.A218980

lemma self_le_sigma (n : ℕ) (hn : 0 < n) : n ≤ sigma n := by
  change n ≤ ArithmeticFunction.sigma 1 n
  rw [ArithmeticFunction.sigma_one_apply]
  exact single_le_sum (f := id) (fun _ _ => Nat.zero_le _) (n.mem_divisors_self hn.ne')

lemma self_add_one_le_sigma (n : ℕ) (hn : 1 < n) : n + 1 ≤ sigma n := by
  change n + 1 ≤ ArithmeticFunction.sigma 1 n
  rw [ArithmeticFunction.sigma_one_apply]
  have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
    intro d hd
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact Nat.one_mem_divisors.mpr (by omega)
    · exact Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩
  have hs := sum_le_sum_of_subset_of_nonneg (f := id) hsub (fun _ _ _ => Nat.zero_le _)
  simp [sum_insert, show 1 ≠ n by omega] at hs
  omega

lemma self_add_four_le_sigma (n : ℕ) (hn : 3 < n) (h3 : 3 ∣ n) : n + 4 ≤ sigma n := by
  change n + 4 ≤ ArithmeticFunction.sigma 1 n
  rw [ArithmeticFunction.sigma_one_apply]
  have hsub : ({1, 3, n} : Finset ℕ) ⊆ n.divisors := by
    intro d hd
    simp only [mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact Nat.one_mem_divisors.mpr (by omega)
    · exact Nat.mem_divisors.mpr ⟨h3, by omega⟩
    · exact Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩
  have hs := sum_le_sum_of_subset_of_nonneg (f := id) hsub (fun _ _ _ => Nat.zero_le _)
  simp [sum_insert, show 1 ≠ n by omega, show 3 ≠ n by omega] at hs
  omega

lemma prime_not_represented {p : ℕ} (hp : p.Prime) (hp5 : 5 < p)
    (hp3 : p ≡ 2 [MOD 3]) : ¬ InA218852 p := by
  intro h
  obtain ⟨x, y, z, hx, hy, hz, hsum, hσ⟩ := h
  have hpσ : sigma p = p + 1 := by
    change ArithmeticFunction.sigma 1 p = p + 1
    rw [ArithmeticFunction.sigma_one_apply, hp.divisors]
    simp [show 1 ≠ p by omega, add_comm]
  rw [hpσ] at hσ
  have hxσ := self_le_sigma x hx
  have hyσ := self_le_sigma y hy
  have hzσ := self_le_sigma z hz
  have hsmall (u : ℕ) (hu : u + 2 = p) : u + 4 ≤ sigma u := by
    apply self_add_four_le_sigma u (by omega)
    change p % 3 = 2 at hp3
    omega
  by_cases hx1 : x = 1
  · by_cases hy1 : y = 1
    · have := hsmall z (by omega)
      omega
    · by_cases hz1 : z = 1
      · have := hsmall y (by omega)
        omega
      · have := self_add_one_le_sigma y (by omega)
        have := self_add_one_le_sigma z (by omega)
        omega
  · by_cases hy1 : y = 1
    · by_cases hz1 : z = 1
      · have := hsmall x (by omega)
        omega
      · have := self_add_one_le_sigma x (by omega)
        have := self_add_one_le_sigma z (by omega)
        omega
    · have := self_add_one_le_sigma x (by omega)
      have := self_add_one_le_sigma y (by omega)
      omega

end OMA.A218980

theorem OMA.solution : type_of% @OMA.S_oeis_a218980.main := by
  apply Set.infinite_iff_exists_gt.mpr
  intro n
  obtain ⟨p, hp, hprime, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max n 5) (q := 3) (a := 2) (by decide) (by decide)
  exact ⟨p, ⟨by omega, OMA.A218980.prime_not_represented hprime (by omega) hmod⟩, by omega⟩
