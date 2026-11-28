import FormalConjectures.Wikipedia.Mersenne
import Mathlib.NumberTheory.Multiplicity

/-! Shorter proof of `Mersenne.rotkiewicz_infinite_non_wieferich_of_squarefree_mersenne`. -/

theorem OMA.solution :
    type_of% @Mersenne.rotkiewicz_infinite_non_wieferich_of_squarefree_mersenne := by
  classical
  intro hinf hfin
  obtain ⟨n, hs, hn⟩ := hinf.exists_gt (∏ p ∈ hfin.toFinset, p)
  have incl : (mersenne n).primeFactors ⊆ hfin.toFinset := fun p hp => by
    obtain ⟨hpr, hd, -⟩ := Nat.mem_primeFactors.mp hp
    refine hfin.mem_toFinset.mpr ⟨hpr, fun hw => ?_⟩
    have hne : p ≠ 2 := by rintro rfl; exact (by decide : ¬IsWieferichPrime 2) hw
    have lift := Nat.emultiplicity_pow_sub_pow hpr (hpr.odd_of_ne_two hne) (y := 1) (x := 2 ^ n) hd
      (fun h => hne ((Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).mp (hpr.dvd_of_dvd_pow h))) (p - 1)
    have hpred : ¬ p ∣ p - 1 := Nat.not_dvd_of_pos_of_lt (by have := hpr.two_le; omega)
      (by have := hpr.pos; omega)
    rw [one_pow, emultiplicity_eq_zero.mpr hpred, add_zero] at lift
    have raised := (hw.pow_modEq (by decide : 2 ≠ 0)).pow n
    rw [one_pow, ← pow_mul, Nat.mul_comm (p - 1) n, pow_mul] at raised
    have hsq : p ^ 2 ∣ (2 ^ n) ^ (p - 1) - 1 := raised.symm.dvd'
    rw [pow_dvd_iff_le_emultiplicity, lift, ← pow_dvd_iff_le_emultiplicity] at hsq
    exact Nat.squarefree_iff_prime_squarefree.mp hs p hpr (by simpa [pow_two, mersenne] using hsq)
  have hdiv := Finset.prod_dvd_prod_of_subset _ _ (fun p : ℕ => p) incl
  rw [Nat.prod_primeFactors_of_squarefree hs] at hdiv
  have hle := Nat.le_of_dvd (Finset.prod_pos fun p hp => (hfin.mem_toFinset.mp hp).1.pos) hdiv
  have := Nat.lt_two_pow_self (n := n)
  unfold mersenne at hle; omega
