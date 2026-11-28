import OMAReductions.R_oeis_a227864_R1

open OMA.S_oeis_a227864

private instance (priority := high) (n : ℕ) : Decidable n.Prime :=
  decidable_of_iff (2 ≤ n ∧ ∀ d ≤ n.sqrt, 2 ≤ d → ¬d∣n) (by
    rw [Nat.prime_def_le_sqrt]
    constructor <;> rintro ⟨hn,h⟩ <;> exact ⟨hn,fun d hd he => h d he hd⟩)

set_option maxRecDepth 10000 in
theorem OMA.solution : OMA.R_oeis_a227864_R1.H1 := by
  have cert : ∀ p : Fin 2001, 3 ≤ p.val → p.val.Prime →
      ∃ k : Fin 18, (reversal (p.val+1+k.val) (p.val^2)).Prime := by decide +kernel
  intro p lo hi prime
  obtain ⟨k,h⟩ := cert ⟨p,by omega⟩ lo prime
  exact ⟨p+1+k.val,by omega,h⟩
