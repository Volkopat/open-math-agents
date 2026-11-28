import OMAReductions.R_arxiv_2609_05358_R1

/-!
# Step H1 of reduction R1 of arxiv-2609.05358: the slab `a < b < 2a`, `a + b < c < 2b`

On this slab no game `{a, b, c}` is purely periodic, so the open direction of Conjecture 52
(arXiv 2609.05358) holds there vacuously. Write `b = a + d`, `c = 2a + d + r`, `0 < r < d < a`.
If `G(x + p) = G(x)` for all `x`, put `Z0 = E p` with `E = c + a + r`; then `Z0, ..., Z0 + a - 1`
are P-positions, as `0, ..., a - 1` are. Independence (no move between P-positions) and
domination (every N-position has a move to a P-position), applied at positions below `Z0`,
give: `Z0 - r` is an N-position whose three options `Z0 - (a + r)`, `Z0 - (b + r)`,
`Z0 - (c + r)` are all N-positions, a contradiction.
-/

namespace OMA.Aux2609_05358

open OMA.S_arxiv_2609_05358

lemma mex_eq_zero_iff (t : Finset ℕ) : mex t = 0 ↔ 0 ∉ t := by
  unfold mex
  rw [Nat.find_eq_zero]

lemma grundy_eq_zero_iff (S : Finset ℕ) (x : ℕ) :
    grundy S x = 0 ↔ ∀ s ∈ S, 0 < s → s ≤ x → grundy S (x - s) ≠ 0 := by
  rw [grundy, mex_eq_zero_iff]
  constructor
  · intro h s hs hs0 hsx h0
    apply h
    rw [Finset.mem_image]
    exact ⟨⟨s, Finset.mem_filter.mpr ⟨hs, hs0, hsx⟩⟩, Finset.mem_attach _ _, h0⟩
  · intro h hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨⟨s, hs⟩, -, h0⟩ := hmem
    obtain ⟨hsS, hs0, hsx⟩ := Finset.mem_filter.mp hs
    exact h s hsS hs0 hsx h0

/-- Independence: an option of a P-position is not a P-position. -/
lemma indep {S : Finset ℕ} {x s : ℕ} (hs : s ∈ S) (hs0 : 0 < s) (hsx : s ≤ x)
    (h : grundy S x = 0) : grundy S (x - s) ≠ 0 :=
  (grundy_eq_zero_iff S x).mp h s hs hs0 hsx

/-- Domination: an N-position has an option that is a P-position. -/
lemma dom {S : Finset ℕ} {x : ℕ} (h : grundy S x ≠ 0) :
    ∃ s ∈ S, 0 < s ∧ s ≤ x ∧ grundy S (x - s) = 0 := by
  by_contra hne
  apply h
  rw [grundy_eq_zero_iff]
  intro s hs hs0 hsx h0
  exact hne ⟨s, hs, hs0, hsx, h0⟩

/-- Below the least move every position is a P-position. -/
lemma small {a b c x : ℕ} (hab : a < b) (hbc : b < c) (hx : x < a) :
    grundy {a, b, c} x = 0 := by
  rw [grundy_eq_zero_iff]
  intro s hs _ hsx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl <;> omega

/-- **Slab theorem.** If `a < b < 2a` and `a + b < c < 2b`, then `G_{a,b,c}` is not purely
periodic. (Angle `ρ = c - (a+b)` with `0 < ρ < b - a`, the region left open in
arXiv 2609.05358 apart from the candidate periods excluded by Moriwaki.) -/
theorem not_purely_periodic_slab (a b c : ℕ) (hab : a < b) (hb2 : b < 2 * a)
    (hc1 : a + b < c) (hc2 : c < 2 * b) :
    ¬ ∃ p ≥ 1, ∀ x, grundy {a, b, c} (x + p) = grundy {a, b, c} x := by
  rintro ⟨p, hp1, hp⟩
  set g := grundy {a, b, c} with hg
  have ha : a ∈ ({a, b, c} : Finset ℕ) := by simp
  have hb : b ∈ ({a, b, c} : Finset ℕ) := by simp
  have hc : c ∈ ({a, b, c} : Finset ℕ) := by simp
  have ha0 : 0 < a := by omega
  have hb0 : 0 < b := by omega
  have hc0 : 0 < c := by omega
  -- parameters: b = a + d, c = 2a + d + r, 0 < r < d < a
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, c = 2 * a + d + r := ⟨c - (2 * a + d), by omega⟩
  have hr0 : 0 < r := by omega
  have hrd : r < d := by omega
  have hda : d < a := by omega
  -- periodicity along multiples of p
  have hper : ∀ k x, g (x + k * p) = g x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [Nat.succ_mul, ← Nat.add_assoc, hp, ih]
  set E := (2 * a + d + r) + a + r with hE
  set Z0 := E * p with hZ0
  have hEZ : E ≤ Z0 := by
    rw [hZ0]; exact Nat.le_mul_of_pos_right E hp1
  have hsm : ∀ i, i < a → g (Z0 + i) = 0 := by
    intro i hi
    rw [Nat.add_comm, hZ0, hper E i]
    exact small (by omega) (by omega) hi
  -- P-positions used
  have P1 : g (Z0 + (d - r)) = 0 := hsm _ (by omega)
  have P2 : g (Z0 + d) = 0 := hsm _ (by omega)
  have P3 : g (Z0 + 0) = 0 := hsm _ (by omega)
  have P4 : g (Z0 + (a - d)) = 0 := hsm _ (by omega)
  have P5 : g (Z0 + (a - d + r)) = 0 := hsm _ (by omega)
  have P6 : g (Z0 + (a - r)) = 0 := hsm _ (by omega)
  -- N-positions obtained by independence
  have N1 : g (Z0 - (a + r)) ≠ 0 := by
    have := indep (x := Z0 + (d - r)) hb (by omega) (by omega) P1
    rwa [show Z0 + (d - r) - (a + d) = Z0 - (a + r) by omega] at this
  have N2 : g (Z0 - (2 * a + r)) ≠ 0 := by
    have := indep (x := Z0 + d) hc (by omega) (by omega) P2
    rwa [show Z0 + d - (2 * a + d + r) = Z0 - (2 * a + r) by omega] at this
  have N3 : g (Z0 - (2 * a + d + r)) ≠ 0 := by
    have := indep (x := Z0 + 0) hc (by omega) (by omega) P3
    rwa [show Z0 + 0 - (2 * a + d + r) = Z0 - (2 * a + d + r) by omega] at this
  have N4 : g (Z0 - d) ≠ 0 := by
    have := indep (x := Z0 + (a - d)) ha (by omega) (by omega) P4
    rwa [show Z0 + (a - d) - a = Z0 - d by omega] at this
  have N5 : g (Z0 - (a + d)) ≠ 0 := by
    have := indep (x := Z0 + 0) hb (by omega) (by omega) P3
    rwa [show Z0 + 0 - (a + d) = Z0 - (a + d) by omega] at this
  have N6 : g (Z0 - (a + 2 * d)) ≠ 0 := by
    have := indep (x := Z0 + (a - d + r)) hc (by omega) (by omega) P5
    rwa [show Z0 + (a - d + r) - (2 * a + d + r) = Z0 - (a + 2 * d) by omega] at this
  have N7 : g (Z0 - r) ≠ 0 := by
    have := indep (x := Z0 + (a - r)) ha (by omega) (by omega) P6
    rwa [show Z0 + (a - r) - a = Z0 - r by omega] at this
  -- forced P-positions by domination
  have F1 : g (Z0 - (a + r + (2 * a + d + r))) = 0 := by
    obtain ⟨s, hs, -, hsx, h0⟩ := dom N1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with h | h | h <;> rw [h] at h0
    · exact absurd (by rwa [show Z0 - (a + r) - a = Z0 - (2 * a + r) by omega] at h0) N2
    · exact absurd (by rwa [show Z0 - (a + r) - (a + d) = Z0 - (2 * a + d + r) by omega] at h0) N3
    · rwa [show Z0 - (a + r) - (2 * a + d + r) = Z0 - (a + r + (2 * a + d + r)) by omega] at h0
  have F2 : g (Z0 - (d + (2 * a + d + r))) = 0 := by
    obtain ⟨s, hs, -, hsx, h0⟩ := dom N4
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with h | h | h <;> rw [h] at h0
    · exact absurd (by rwa [show Z0 - d - a = Z0 - (a + d) by omega] at h0) N5
    · exact absurd (by rwa [show Z0 - d - (a + d) = Z0 - (a + 2 * d) by omega] at h0) N6
    · rwa [show Z0 - d - (2 * a + d + r) = Z0 - (d + (2 * a + d + r)) by omega] at h0
  -- consequences
  have N8 : g (Z0 - ((2 * a + d + r) + r)) ≠ 0 := by
    intro h
    have := indep (x := Z0 - ((2 * a + d + r) + r)) ha ha0 (by omega) h
    rw [show Z0 - ((2 * a + d + r) + r) - a = Z0 - (a + r + (2 * a + d + r)) by omega] at this
    exact this F1
  have N9 : g (Z0 - ((a + d) + r)) ≠ 0 := by
    intro h
    have := indep (x := Z0 - ((a + d) + r)) hb hb0 (by omega) h
    rw [show Z0 - ((a + d) + r) - (a + d) = Z0 - (d + (2 * a + d + r)) by omega] at this
    exact this F2
  -- contradiction at Z0 - r
  obtain ⟨s, hs, -, hsx, h0⟩ := dom N7
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with h | h | h <;> rw [h] at h0
  · exact N1 (by rwa [show Z0 - r - a = Z0 - (a + r) by omega] at h0)
  · exact N9 (by rwa [show Z0 - r - (a + d) = Z0 - ((a + d) + r) by omega] at h0)
  · exact N8 (by rwa [show Z0 - r - (2 * a + d + r) = Z0 - ((2 * a + d + r) + r) by omega] at h0)

end OMA.Aux2609_05358

theorem OMA.solution : OMA.R_arxiv_2609_05358_R1.H1 := by
  intro a b c _ hab _ _ _ hb2 hc1 hc2 hper
  exact absurd hper (OMA.Aux2609_05358.not_purely_periodic_slab a b c hab hb2 hc1 hc2)
