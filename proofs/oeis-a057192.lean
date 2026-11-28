import OMAStatements.S_oeis_a057192
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Tactic.NormNum.Prime

/-!
Refutation of Aguirre's parity conjecture as stated for OEIS A057192.
The counterexample uses Sierpiński's known prime 271129, identified for this
sequence by Jianing Song. Its six covering primes are listed in OEIS A206001.
Conjecture recorded by Lorenzo Sauras Altuzarra; statement by @divmxnd0x.
Formal proof by @ptlom using OpenAI Codex (gpt-6.2-astra).
-/

open OMA.S_oeis_a057192

private abbrev cover := 5592405

private theorem periodic (m : ℕ) : 2^m ≡ 2^(m%24) [MOD cover] := by
  have period : 2^24 ≡ 1 [MOD cover] := by decide
  calc
    2^m = 2^(m%24) * (2^24)^(m/24) := by
      rw [← pow_mul, ← pow_add, Nat.mod_add_div]
    _ ≡ _ [MOD cover] := by
      simpa using (Nat.ModEq.refl (2^(m%24))).mul (period.pow (m/24))

private theorem composite (m : ℕ) : ¬ (1 + 271129*2^m).Prime := by
  have table : ∀ r : Fin 24,
      2 ≤ (1 + 271129*2^r.val).gcd cover ∧ (1 + 271129*2^r.val).gcd cover ≤ 241 := by decide
  have eqg := ((periodic m).mul_left 271129 |>.add_left 1).gcd_eq
  have bounds := table ⟨m%24, Nat.mod_lt _ (by decide)⟩
  change 2 ≤ (1 + 271129*2^(m%24)).gcd cover ∧ _ at bounds
  rw [← eqg] at bounds
  have pos : 0 < (2:ℕ)^m := Nat.pow_pos (by decide)
  exact Nat.not_prime_of_dvd_of_lt (Nat.gcd_dvd_left _ cover) bounds.1 (by omega)

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a057192.main) := by
  intro claim
  have hp : Nat.Prime 271129 := by norm_num
  obtain ⟨k, hk⟩ := Nat.subset_range_nth (p := Nat.Prime) hp
  have hk0 : k ≠ 0 := by
    intro hz
    rw [hz, Nat.nth_prime_zero_eq_two] at hk
    exact (by decide : (2:ℕ) ≠ 271129) hk
  have h := claim (k+1) (by omega)
  simp only [Nat.add_sub_cancel, hk] at h
  have parity := h.mpr (by decide)
  have missing : ¬ ∃ m : ℕ, (1 + 271129*2^m).Prime := by
    rintro ⟨m,hm⟩
    exact composite m hm
  have missingAt : ¬ ∃ m : ℕ, (1 + Nat.nth Nat.Prime (k+1-1)*2^m).Prime := by
    simpa only [Nat.add_sub_cancel, hk] using missing
  unfold a at parity
  rw [dif_neg missingAt] at parity
  obtain ⟨z,hz⟩ := parity
  omega
