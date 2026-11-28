import OMAStatements.S_oeis_a070297
import Mathlib

namespace OMA.A070297Proof

open OMA.S_oeis_a070297

-- The number of `j` with `1 ≤ j < M` that do not divide `M`.
def nondiv (M : ℕ) : ℕ := ((Finset.Ico 1 M).filter (fun j => ¬ j ∣ M)).card

-- A prime has no unrelated numbers.
theorem unrelated_prime (p : ℕ) (hp : p.Prime) : unrelated p = 0 := by
  unfold unrelated
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k hk hk2
  rw [Finset.mem_Ico] at hk
  apply hk2.1
  have h1 : ¬ p ∣ k := fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
  exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr h1).symm

-- With `m = p * M` and `p` prime, `j ↦ j * p` sends the non-divisors `j < M` of `M` injectively to unrelated
-- numbers of `m`.
theorem lower (m p M : ℕ) (hp : p.Prime) (hm : m = p * M) : nondiv M ≤ unrelated m := by
  unfold nondiv unrelated
  apply Finset.card_le_card_of_injOn (fun j => j * p)
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at hj ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hj
    refine ⟨⟨Nat.mul_pos (by omega) hp.pos, ?_⟩, ?_, ?_⟩
    · rw [hm, mul_comm p M]
      exact mul_lt_mul_of_pos_right h2 hp.pos
    · intro hg
      have hd : p ∣ Nat.gcd (j * p) m :=
        Nat.dvd_gcd (dvd_mul_left p j) (by rw [hm]; exact dvd_mul_right p M)
      rw [hg] at hd
      exact hp.one_lt.ne' (Nat.dvd_one.mp hd)
    · intro hd
      apply h3
      rw [hm, mul_comm p M] at hd
      exact (mul_dvd_mul_iff_right hp.ne_zero).mp hd
  · intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_right hp.pos hab

-- For `M ≥ 29`, the fourteen numbers `M - 14, ..., M - 1` are non-divisors of `M`.
theorem nondiv_ge (M : ℕ) (hM : 29 ≤ M) : 14 ≤ nondiv M := by
  have hsub : Finset.Ico (M - 14) M ⊆ (Finset.Ico 1 M).filter (fun j => ¬ j ∣ M) := by
    intro j hj
    rw [Finset.mem_Ico] at hj
    rw [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨by omega, hj.2⟩, ?_⟩
    rintro ⟨c, hc⟩
    rcases c with _ | _ | c
    · omega
    · omega
    · have h2 : j * 2 ≤ j * (c + 1 + 1) := Nat.mul_le_mul (le_refl j) (by omega)
      omega
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Ico] at hcard
  unfold nondiv
  omega

-- No number has exactly 2, or exactly 13, unrelated numbers. With `p = minFac m` and `m = p * M`, an `m` with at
-- most 13 unrelated numbers has `nondiv M ≤ 13`, so `M ≤ 28`, and `p ≤ minFac M`; the 33 values of `m` left
-- (all `≤ 169`) are checked by `decide`.
set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem key (m : ℕ) : unrelated m ≠ 2 ∧ unrelated m ≠ 13 := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m <;> decide
  by_cases hprime : m.Prime
  · rw [unrelated_prime m hprime]
    decide
  by_cases hU : 14 ≤ unrelated m
  · exact ⟨by omega, by omega⟩
  obtain ⟨p, hpdef⟩ : ∃ p, p = m.minFac := ⟨_, rfl⟩
  have hp : p.Prime := by
    rw [hpdef]
    exact Nat.minFac_prime (by omega)
  have hp2 : 2 ≤ p := hp.two_le
  have hpm : p ∣ m := by
    rw [hpdef]
    exact Nat.minFac_dvd m
  obtain ⟨M, hM⟩ := hpm
  have hN : nondiv M ≤ 13 := by
    have := lower m p M hp hM
    omega
  have hM28 : M ≤ 28 := by
    by_contra h
    have := nondiv_ge M (by omega)
    omega
  have hM2 : 2 ≤ M := by
    rcases Nat.lt_or_ge M 2 with h | h
    · interval_cases M
      · omega
      · rw [Nat.mul_one] at hM
        rw [hM] at hprime
        exact absurd hp hprime
    · exact h
  have hq : p ≤ M.minFac := by
    rw [hpdef]
    apply Nat.minFac_le_of_dvd (Nat.minFac_prime (by omega)).two_le
    rw [hM]
    exact dvd_mul_of_dvd_right (Nat.minFac_dvd M) p
  clear hpdef hU hprime
  interval_cases M
  all_goals first
    | exact absurd hN (by decide)
    | (norm_num at hq; interval_cases p <;> first | (exfalso; norm_num at hp; done) | (subst hM; decide))

end OMA.A070297Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a070297.main := by
  exact ⟨fun m => (OMA.A070297Proof.key m).1, fun m => (OMA.A070297Proof.key m).2⟩
