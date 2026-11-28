import OMAReductions.R_Erdos1113_erdos_1113_variants_filaseta_finch_kozek_R1

-- Step Erdos1113.erdos_1113.variants.filaseta_finch_kozek.R1.H1: hypothesis H1 of reduction
-- Erdos1113.erdos_1113.variants.filaseta_finch_kozek.R1.
-- Written with Claude Code (AI-assisted).
-- Selfridge's covering set {3, 5, 7, 13, 19, 37, 73} (2^36 ≡ 1 mod their product) and the
-- covering set {3, 5, 7, 13, 17, 241} of 271129 (2^24 ≡ 1 mod their product): modulo the product
-- M, k * 2^n + 1 ≡ c * 2^(n % e) + 1, and the finitely many residues are checked by `decide`.

namespace OMA.E1113H1

theorem cover (k M e c : ℕ) (P : Finset ℕ) (he0 : 0 < e) (hk : k ≡ c [MOD M])
    (he : 2 ^ e ≡ 1 [MOD M]) (hP : ∀ p ∈ P, p ∣ M)
    (hchk : ∀ r < e, ∃ p ∈ P, p ∣ c * 2 ^ r + 1) :
    ∀ n, ∃ p ∈ P, p ∣ k * 2 ^ n + 1 := by
  intro n
  obtain ⟨p, hp, hdvd⟩ := hchk (n % e) (Nat.mod_lt n he0)
  refine ⟨p, hp, ?_⟩
  have hpow : 2 ^ n ≡ 2 ^ (n % e) [MOD M] := by
    have h1 : 2 ^ n = (2 ^ e) ^ (n / e) * 2 ^ (n % e) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    rw [h1]
    have h2 : (2 ^ e) ^ (n / e) ≡ 1 ^ (n / e) [MOD M] := he.pow _
    rw [one_pow] at h2
    simpa using h2.mul_right (2 ^ (n % e))
  have hmod : k * 2 ^ n + 1 ≡ c * 2 ^ (n % e) + 1 [MOD M] := (hk.mul hpow).add_right 1
  exact (Nat.ModEq.dvd_iff hmod (hP p hp)).mpr hdvd

end OMA.E1113H1

open Erdos1113 in
theorem OMA.solution : OMA.R_Erdos1113_erdos_1113_variants_filaseta_finch_kozek_R1.H1 := by
  intro k hk
  rcases hk with hk | hk
  · refine ⟨{3, 5, 7, 13, 19, 37, 73}, by simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]; norm_num, ?_⟩
    exact OMA.E1113H1.cover k 70050435 36 78557 _ (by norm_num) hk (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  · refine ⟨{3, 5, 7, 13, 17, 241}, by simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]; norm_num, ?_⟩
    exact OMA.E1113H1.cover k 5592405 24 271129 _ (by norm_num) hk (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
