import OMAStatements.S_oeis_a101042
import Mathlib

/-- Every prime is the smallest prime beginning some prime pair. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a101042.main := by
  intro q hq
  let M := (q - 1).factorial
  have hM : M ≠ 0 := Nat.factorial_ne_zero _
  have hc : q.Coprime M := hq.coprime_factorial_of_lt (by have := hq.two_le; omega)
  obtain ⟨r, hrq, hrprime, hrmod⟩ := Nat.forall_exists_prime_gt_and_modEq q hM hc
  have hdiv : M ∣ r - q := hrmod.symm.dvd'
  refine ⟨r - q, by omega, ?_, ?_⟩
  · simpa [Nat.add_sub_of_le (le_of_lt hrq)] using hrprime
  · intro p hp hpq hpdprime
    have hpM : p ∣ M := Nat.dvd_factorial hp.pos (by omega)
    have hpd : p ∣ r - q := dvd_trans hpM hdiv
    have hps : p ∣ p + (r - q) := dvd_add (dvd_refl p) hpd
    rcases hpdprime.eq_one_or_self_of_dvd p hps with h | h
    · exact hp.ne_one h
    · omega

