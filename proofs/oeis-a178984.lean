import OMAStatements.S_oeis_a178984

-- Source: https://oeis.org/A178984. Original proof: @Solitude1312
open OMA.S_oeis_a178984

theorem OMA.solution : type_of% @OMA.S_oeis_a178984.main := by
  intro h n hn
  have hp : (primeAt n).Prime := Nat.prime_nth_prime _
  have hbound : n - 1 + 2 ≤ primeAt n := Nat.add_two_le_nth_prime _
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two (by omega)
  obtain ⟨p, q, hp', hq, hsum⟩ := h (primeAt n + 1) (by omega) ⟨k + 1, by omega⟩
  have hmem : p ∈ candidates n := ⟨hp', by rwa [show primeAt n + 1 - p = q by omega]⟩
  exact ⟨Nat.sInf_mem ⟨p, hmem⟩, fun _ hm => Nat.sInf_le hm⟩
