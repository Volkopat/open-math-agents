import OMAReductions.R_Erdos828_erdos_828_variants_lehmer_conjecture_R1
import Mathlib

/-- Step Erdos828.erdos_828.variants.lehmer_conjecture.R1.H2. -/
theorem OMA.solution : OMA.R_Erdos828_erdos_828_variants_lehmer_conjecture_R1.H2 := by
  intro n hn hp
  rw [Nat.totient_prime (Nat.prime_iff.mpr hp)]
