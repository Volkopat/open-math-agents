import OMAStatements.S_oeis_a230260

-- Credit: @tjgksruf9801 (shorter proof). n = 139: every split 278 = p + q into primes has an
-- even total binary digit sum.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a230260.main) := fun h => by
  obtain ⟨p, q, hp, hq, hs, hodd⟩ := h 139 (by decide)
  obtain rfl : q = 278 - p := by omega
  exact (by decide +kernel : ∀ p < 279, p.Prime → (278 - p).Prime →
    ¬ Odd ((Nat.digits 2 p).sum + (Nat.digits 2 (278 - p)).sum)) p (by omega) hp hq hodd
