import OMAStatements.S_mse_698186
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-! Retains @Solfanbtc’s mod-four counterexample from #31277.
Dirichlet’s theorem supplies infinitude of the chosen prime residue class.
The earlier mod-three counterexample by @lucasfreund2-cmd is in #25145. -/

namespace OMA.Disproof_mse_698186

private def S3 : Set ℕ := {p : ℕ | p.Prime ∧ p % 4 = 3}

private lemma list_map_prod_emod_four (f : ℕ → ℤ) :
    ∀ l : List ℕ, (∀ p ∈ l, f p % 4 = (p : ℤ) % 4) →
      (l.map f).prod % 4 = (l.prod : ℤ) % 4
  | [], _ => rfl
  | p :: ps, h => by
      simp only [List.map_cons, List.prod_cons]
      rw [Int.mul_emod, h p (by simp),
        list_map_prod_emod_four f ps (fun q hq => h q (by simp [hq])), ← Int.mul_emod]
      simp

private lemma S3_infinite : S3.Infinite := by
  simpa [S3, Nat.ModEq] using
    Nat.infinite_setOfPred_prime_and_modEq (q := 4) (a := 3) (by decide) (by decide)

private lemma generated_S3_ne_one_of_mod_four_eq_three {m : ℕ} (hm : m % 4 = 3) :
    OMA.S_mse_698186.generated S3 m ≠ 1 := by
  intro hgen
  have hmne : m ≠ 0 := by omega
  have hmod : (OMA.S_mse_698186.generated S3 m) % 4 = (m.primeFactorsList.prod : ℤ) % 4 := by
    unfold OMA.S_mse_698186.generated
    apply list_map_prod_emod_four
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactorsList hp
    have hpdvd : p ∣ m := Nat.dvd_of_mem_primeFactorsList hp
    have hpne2 : p ≠ 2 := by
      intro h2
      rw [h2] at hpdvd
      omega
    have hpodd : p % 2 = 1 := (hpp.eq_two_or_odd).resolve_left hpne2
    split_ifs with hpS
    · have hp3 : p % 4 = 3 := hpS.2
      omega
    · have hpne3 : p % 4 ≠ 3 := fun h3 => hpS ⟨hpp, h3⟩
      omega
  rw [hgen, Nat.prod_primeFactorsList hmne] at hmod
  omega

end OMA.Disproof_mse_698186

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_698186.main) := by
  intro hmain
  have hinf :=
    hmain OMA.Disproof_mse_698186.S3 (fun _ hp => hp.1) OMA.Disproof_mse_698186.S3_infinite 4
  rcases hinf.nonempty with ⟨n, _, hn⟩
  let i : ℕ := 3 - n % 4
  have hi : i < 4 := by omega
  have hmod : (n + i) % 4 = 3 := by omega
  exact OMA.Disproof_mse_698186.generated_S3_ne_one_of_mod_four_eq_three hmod (hn i hi)
