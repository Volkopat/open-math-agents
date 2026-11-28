import OMAReductions.R_Erdos1191_erdos_1191_parts_i_R1

-- Reduction Erdos1191.erdos_1191.parts.i.R1.H2.R1 of step Erdos1191.erdos_1191.parts.i.R1.H2
-- Credit: @ihateSAS
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The counting hypothesis of H2 is free at small dyadic scales: if a Sidon set has `s` positive
-- elements below `2^R`, then `s ^ 2 ≤ 3 * 2 ^ R`, because the differences of those elements are
-- pairwise distinct nonzero integers below `2^R`. Therefore `s ^ 2 * R ≤ 512 * 2 ^ R` holds
-- automatically for every `R ≤ 170`, and for `R₀ ≤ 85` the whole content of H2 is the existence
-- of a *light* window, one holding at most `2^{R/2-L/2}/√(R+L)` elements between `2^R` and
-- `2^{R+L}`. H1 isolates exactly that combinatorial statement at the scales forced by `R₀`, and
-- H2 keeps the general statement, where the counting hypothesis is no longer free.

namespace OMA.R_Erdos1191_erdos_1191_parts_i_R1_H2_R1

/-- A Sidon set has few positive elements below any dyadic scale: `#T ^ 2 ≤ 3 * 2 ^ R`. -/
lemma card_sq_le {T : Finset ℕ} (hpos : ∀ x ∈ T, 0 < x) (hT : IsSidon (T : Set ℕ)) (R : ℕ)
    (hsub : ∀ x ∈ T, x ≤ 2 ^ R) : T.card ^ 2 ≤ 3 * 2 ^ R := by
  classical
  have hmem : ∀ x ∈ T, x ∈ (T : Set ℕ) := fun x hx => Finset.mem_coe.mpr hx
  -- The pairing map: branch `A` when the second coordinate is smaller, branch `B` otherwise.
  set f : ℕ × ℕ → ℕ := fun p => if p.2 < p.1 then p.1 - p.2 else 2 ^ (R + 1) - (p.2 - p.1)
    with hf
  have hlt : ∀ p ∈ T.offDiag, f p < 2 ^ (R + 1) := by
    rintro ⟨a, b⟩ hp
    obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hp
    have hpa := hpos a ha
    have hpb := hpos b hb
    have hsa := hsub a ha
    have hsb := hsub b hb
    have h2 : 2 ^ (R + 1) = 2 * 2 ^ R := by rw [pow_succ]; ring
    simp only [hf]
    split_ifs with h
    · omega
    · have : 0 < b - a := by omega
      omega
  have hinj : Set.InjOn f (T.offDiag : Set (ℕ × ℕ)) := by
    rintro ⟨a, b⟩ hp ⟨c, d⟩ hq hEq
    rw [Finset.mem_coe] at hp hq
    obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hp
    obtain ⟨hc, hd, hcd⟩ := Finset.mem_offDiag.mp hq
    have hpa := hpos a ha
    have hpb := hpos b hb
    have hpc := hpos c hc
    have hpd := hpos d hd
    have hsa := hsub a ha
    have hsb := hsub b hb
    have hsc := hsub c hc
    have hsd := hsub d hd
    have h2 : 2 ^ (R + 1) = 2 * 2 ^ R := by rw [pow_succ]; ring
    simp only [hf] at hEq
    by_cases hltab : b < a
    · by_cases hltcd : d < c
      · rw [if_pos hltab, if_pos hltcd] at hEq
        have hsum : a + d = c + b := by omega
        obtain ⟨e1, e2⟩ | ⟨e1, e2⟩ :=
          hT a (hmem a ha) c (hmem c hc) d (hmem d hd) b (hmem b hb) hsum
        · exact Prod.ext e1 e2.symm
        · exact absurd e1 hab
      · rw [if_pos hltab, if_neg hltcd] at hEq
        have hb1 : a - b < 2 ^ R := by omega
        have hb2 : 2 ^ R < 2 ^ (R + 1) - (d - c) := by
          have hdc : d - c < 2 ^ R := by omega
          omega
        omega
    · by_cases hltcd : d < c
      · rw [if_neg hltab, if_pos hltcd] at hEq
        have hb1 : c - d < 2 ^ R := by omega
        have hb2 : 2 ^ R < 2 ^ (R + 1) - (b - a) := by
          have hba : b - a < 2 ^ R := by omega
          omega
        omega
      · rw [if_neg hltab, if_neg hltcd] at hEq
        have hsum : b + c = d + a := by omega
        obtain ⟨e1, e2⟩ | ⟨e1, e2⟩ :=
          hT b (hmem b hb) d (hmem d hd) c (hmem c hc) a (hmem a ha) hsum
        · exact Prod.ext e2.symm e1
        · exact absurd e1.symm hab
  have hcard : (T.offDiag.image f).card = T.offDiag.card := Finset.card_image_of_injOn hinj
  have hle : T.offDiag.card ≤ 2 ^ (R + 1) := by
    rw [← hcard]
    have hsub2 : T.offDiag.image f ⊆ Finset.range (2 ^ (R + 1)) := by
      intro y hy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_range.mpr (hlt p hp)
    calc (T.offDiag.image f).card ≤ (Finset.range (2 ^ (R + 1))).card := Finset.card_le_card hsub2
      _ = 2 ^ (R + 1) := Finset.card_range _
  rw [Finset.offDiag_card] at hle
  have hsmall : T.card ≤ 2 ^ R := by
    have hsub' : T ⊆ Finset.Icc 1 (2 ^ R) := fun x hx =>
      Finset.mem_Icc.mpr ⟨hpos x hx, hsub x hx⟩
    have hc : (Finset.Icc 1 (2 ^ R)).card = 2 ^ R := by
      rw [Nat.card_Icc]
      omega
    exact (Finset.card_le_card hsub').trans_eq hc
  have hpos_card : T.card ≤ T.card * T.card := by
    rcases Nat.eq_zero_or_pos T.card with h | h
    · simp [h]
    · exact Nat.le_mul_of_pos_left T.card h
  have hkey : T.card * T.card ≤ 2 ^ (R + 1) + T.card := by
    have h := Nat.sub_add_cancel hpos_card
    omega
  have hstep : 2 ^ (R + 1) + T.card ≤ 3 * 2 ^ R := by
    have h2 : 2 ^ (R + 1) = 2 * 2 ^ R := by rw [pow_succ]; ring
    omega
  calc T.card ^ 2 = T.card * T.card := by ring
    _ ≤ 3 * 2 ^ R := hkey.trans hstep

/-- At every scale `R ≤ 170` the counting hypothesis of H2 is automatic for Sidon sets. -/
lemma good_of_le {S : Finset ℕ} (hpos : ∀ x ∈ S, 0 < x) (hS : IsSidon (S : Set ℕ)) {R : ℕ}
    (hR : R ≤ 170) : (S.filter (· ≤ 2 ^ R)).card ^ 2 * R ≤ 512 * 2 ^ R := by
  classical
  have hpos' : ∀ x ∈ S.filter (fun x => x ≤ 2 ^ R), 0 < x := fun x hx =>
    hpos x (Finset.mem_of_mem_filter x hx)
  have hsub : ∀ x ∈ S.filter (fun x => x ≤ 2 ^ R), x ≤ 2 ^ R := fun x hx =>
    (Finset.mem_filter.mp hx).2
  have hsid : IsSidon ((S.filter (fun x => x ≤ 2 ^ R) : Finset ℕ) : Set ℕ) := by
    have hcoe : ((S.filter (fun x => x ≤ 2 ^ R) : Finset ℕ) : Set ℕ) ⊆ (S : Set ℕ) := by
      intro x hx
      have hx' : x ∈ S.filter (fun x => x ≤ 2 ^ R) := by simpa using hx
      exact Finset.mem_coe.mpr (Finset.mem_of_mem_filter x hx')
    exact Set.IsSidon.subset hS hcoe
  have hsq := card_sq_le hpos' hsid R hsub
  have : (S.filter (fun x => x ≤ 2 ^ R)).card ^ 2 * R ≤ 3 * 2 ^ R * R :=
    Nat.mul_le_mul_right R hsq
  have h3 : 3 * 2 ^ R * R ≤ 512 * 2 ^ R := by
    have : 3 * R ≤ 512 := by omega
    calc 3 * 2 ^ R * R = (3 * R) * 2 ^ R := by ring
      _ ≤ 512 * 2 ^ R := Nat.mul_le_mul_right (2 ^ R) this
  exact this.trans h3

/-- The light-window statement at the scales forced by a small base `R₀`; the counting
hypothesis is automatic there, so it does not appear. -/
def H1 : Prop :=
  ∀ L R₀ : ℕ, 16 ≤ R₀ → R₀ ≤ 85 → 1 ≤ L →
    ∃ K : ℕ, 2 * R₀ + L ≤ K ∧
      ∀ S : Finset ℕ, (↑S : Set ℕ) ⊆ Set.Icc 1 (2 ^ K) → IsSidon (↑S : Set ℕ) →
        ∃ R ∈ Set.Icc R₀ (2 * R₀),
          2 ^ L * (S.filter (fun a => 2 ^ R < a ∧ a ≤ 2 ^ (R + L))).card ^ 2 * (R + L) ≤
            2 ^ (R + L)

/-- The general statement, for bases `R₀` beyond the range where the counting bound is free. -/
def H2 : Prop :=
  ∀ L R₀ : ℕ, 86 ≤ R₀ → 1 ≤ L →
    ∃ K : ℕ, 2 * R₀ + L ≤ K ∧
      ∀ S : Finset ℕ, (↑S : Set ℕ) ⊆ Set.Icc 1 (2 ^ K) → IsSidon (↑S : Set ℕ) →
        (∃ R ∈ Set.Icc R₀ (K - L), (S.filter (· ≤ 2 ^ R)).card ^ 2 * R ≤ 512 * 2 ^ R) →
        ∃ R ∈ Set.Icc R₀ (K - L),
          (S.filter (· ≤ 2 ^ R)).card ^ 2 * R ≤ 512 * 2 ^ R ∧
          2 ^ L * (S.filter (fun a => 2 ^ R < a ∧ a ≤ 2 ^ (R + L))).card ^ 2 * (R + L) ≤
            2 ^ (R + L)

theorem main : H1 → H2 → OMA.R_Erdos1191_erdos_1191_parts_i_R1.H2 := by
  rintro h1 h2 L R₀ hR₀ hL
  by_cases hsmall : R₀ ≤ 85
  · obtain ⟨K, hK, hK'⟩ := h1 L R₀ hR₀ hsmall hL
    refine ⟨K, hK, ?_⟩
    rintro S hS hsid -
    obtain ⟨R, hR, hlight⟩ := hK' S hS hsid
    have hpos : ∀ x ∈ S, 0 < x := fun x hx => (hS (by simpa using hx)).1
    have hR170 : R ≤ 170 := by
      have := hR.2
      omega
    exact ⟨R, ⟨hR.1, by
      have : R ≤ 2 * R₀ := hR.2
      have : 2 * R₀ ≤ K - L := by omega
      omega⟩, good_of_le hpos hsid hR170, hlight⟩
  · exact h2 L R₀ (by omega) hL

end OMA.R_Erdos1191_erdos_1191_parts_i_R1_H2_R1
