import OMAReductions.R_OeisA109908_conjecture_R1

/-! With `n = d + 2k` (`k ≥ 1`), the identity `n² = d² + 4(p+1)` gives `p + 1 = k(n-k)`, and
`1 ≤ k ≤ n/2`, so `p` is one of the primes over which `a n` takes the supremum. -/

namespace OMA.A109908H1

lemma mem_of_factor (n k p : ℕ) (hk : 1 ≤ k) (hb : k ≤ n / 2) (hp : p.Prime)
    (he : p + 1 = k * (n - k)) : p ≤ OeisA109908.a n := by
  unfold OeisA109908.a
  have hmem : p ∈ ((Finset.Icc 1 (n / 2)).image (fun k => k * (n - k) - 1)).filter Nat.Prime := by
    rw [Finset.mem_filter, Finset.mem_image]
    refine ⟨⟨k, Finset.mem_Icc.mpr ⟨hk, hb⟩, ?_⟩, hp⟩
    show k * (n - k) - 1 = p
    omega
  exact Finset.le_sup (f := id) hmem

end OMA.A109908H1

theorem OMA.solution : OMA.R_OeisA109908_conjecture_R1.H1 := by
  intro n p _ hp ⟨d, hd, hpar, he⟩
  obtain ⟨k, hk⟩ : ∃ k, n = d + 2 * k := ⟨(n - d) / 2, by omega⟩
  subst hk
  have hkpos : 1 ≤ k := by omega
  have h1 : p + 1 = k * (d + k) := by nlinarith
  apply OMA.A109908H1.mem_of_factor (d + 2 * k) k p hkpos (by omega) hp
  rw [show d + 2 * k - k = d + k by omega]
  exact h1
