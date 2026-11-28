import OMAReductions.R_mo_301581_R1

/-!
# Proof of `mo-301581.R1.H1`

If `s ∈ {2, 3, 4}` satisfies `s ≤ n` and every prime `q ≡ 3 (mod 4)` dividing `n - s` appears with
even `q`-adic valuation, then by Fermat's two-square theorem (`Nat.eq_sq_add_sq_iff`) we can write
`n - s = a^2 + b^2`. Moreover `2 = C(0) + C(0)`, `3 = C(0) + C(1)`, and `4 = C(2,1) + C(2,1)` where
`C(k) = Nat.centralBinom k`, giving `n = a^2 + b^2 + C(c) + C(d)`.
-/

theorem OMA.solution : OMA.R_mo_301581_R1.H1 := by
  intro n ⟨s, hs2, hs4, hsn, hpf⟩
  obtain ⟨a, b, hab⟩ := Nat.eq_sq_add_sq_iff.mpr hpf
  have h0 : Nat.centralBinom 0 = 1 := by decide
  have h1 : Nat.centralBinom 1 = 2 := by decide
  interval_cases s
  · exact ⟨a, b, 0, 0, by rw [h0]; omega⟩
  · exact ⟨a, b, 0, 1, by rw [h0, h1]; omega⟩
  · exact ⟨a, b, 1, 1, by rw [h1]; omega⟩
