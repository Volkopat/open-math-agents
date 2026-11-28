import FormalConjectures.ErdosProblems.«291»

open Erdos291 Finset

theorem OMA.solution : type_of% @Erdos291.erdos_291.parts.ii := by
  refine Set.infinite_of_forall_exists_gt fun b => ?_
  let q := 3 ^ (b + 1); let n := 2 * q; let M := L n
  have hq : 0 < q := by positivity
  have hn : 0 < n := by dsimp [n]; omega
  have hns : n ∈ Icc 1 n := mem_Icc.mpr ⟨hn, le_rfl⟩
  have hqs : q ∈ (Icc 1 n).erase n :=
    mem_erase.mpr ⟨by dsimp [n]; omega, mem_Icc.mpr (by dsimp [n]; omega)⟩
  have hnM : n ∣ M := Finset.dvd_lcm (f := id) hns
  have h3M : 3 ∣ M := dvd_trans (dvd_mul_of_dvd_right (dvd_pow_self 3 (by omega)) 2) hnM
  have hreg : 3 ∣ ∑ k ∈ ((Icc 1 n).erase n).erase q, M / k := Finset.dvd_sum fun k hk => by
    obtain ⟨hkq, hk⟩ := mem_erase.mp hk; obtain ⟨hkn, hk⟩ := mem_erase.mp hk
    have hqM : q ∣ M := Finset.dvd_lcm (f := id) (mem_Icc.mpr (by dsimp [n]; omega))
    have hkM : k ∣ M := Finset.dvd_lcm (f := id) hk
    by_contra h
    have hc : Nat.Coprime q (M / k) := (Nat.prime_three.coprime_iff_not_dvd.mpr h).pow_left _
    obtain ⟨j, hj⟩ := hc.dvd_mul_right.mp (by simpa [Nat.mul_div_cancel' hkM] using hqM : q ∣ k * (M / k))
    obtain ⟨_, hkb⟩ := mem_Icc.mp hk
    have : j ≤ 2 := by dsimp [n] at hkb; nlinarith
    interval_cases j <;> simp_all [n, Nat.mul_comm]
  have hpair : 3 ∣ M / n + M / q := by
    obtain ⟨u, hu⟩ := hnM
    rw [hu, Nat.mul_div_cancel_left _ hn, show n * u = q * (2 * u) by dsimp [n]; ring,
      Nat.mul_div_cancel_left _ hq]
    exact ⟨u, by omega⟩
  have h3a : 3 ∣ a n := by
    change 3 ∣ ∑ k ∈ Icc 1 n, M / k
    rw [← add_sum_erase _ _ hns, ← add_sum_erase _ _ hqs, ← add_assoc]
    exact dvd_add hpair hreg
  have hM : M ≠ 0 := lcm_ne_zero_iff.mpr fun k hk => Nat.ne_of_gt (mem_Icc.mp hk).1
  refine ⟨n, lt_of_lt_of_le (by decide : 1 < 3)
    (Nat.le_of_dvd (Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hM)) (Nat.dvd_gcd h3a h3M)), ?_⟩
  have : b < 3 ^ b := Nat.lt_pow_self (by decide)
  dsimp [n, q]; rw [pow_succ]; omega
