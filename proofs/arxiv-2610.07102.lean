import OMAStatements.S_arxiv_2610_07102
import Mathlib

-- Problem arxiv-2610.07102: the statement claims that for every odd n >= 3 the carousel tournament T_n on Z_n
-- (arcs x -> y when y - x is one of 1, ..., (n-1)/2) has a Hamilton cycle decomposition that is invariant
-- under translation by 1.
-- Upstream: statements/arxiv-2610.07102.lean (declaration OMA.S_arxiv_2610_07102.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Refutation: it fails for n = 9. Suppose F is such a decomposition of T_9.
-- (1) Two cycles of F that agree at one vertex are equal, because the arc leaving that vertex lies on exactly
--     one cycle of F.
-- (2) F is closed under conjugation by every translation, and the conjugate of s by translation by m is
--     z -> s (z - m) + m.
-- (3) Let s in F be the cycle through the arc 0 -> 3. The nine differences s x - x take only the four values
--     1, 2, 3, 4, so s x - x = s y - y for some x != y. With k = y - x != 0, the conjugate of s by translation
--     by k agrees with s at y, hence equals s: s (z + k) = s z + k for all z.
-- (4) Therefore s (j k) = 3 + j k for all j. Every nonzero k in Z_9 has multiples equal to 3 and to 6, so
--     s 3 = 6 and s 6 = 0. Thus {0, 3, 6} is closed under s, and no power of s maps 0 to 1, contradicting that
--     s is a single cycle through all nine vertices.

open OMA.S_arxiv_2610_07102

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2610_07102.main) := by
  intro hmain
  obtain ⟨F, hHam, hUniq, hConj⟩ := hmain 9 (by decide) (by norm_num)
  have hagree : ∀ σ ∈ F, ∀ ρ ∈ F, ∀ x : ZMod 9, σ x = ρ x → σ = ρ := by
    intro σ hσ ρ hρ x hx
    obtain ⟨_, _, harcσ⟩ := hHam σ hσ
    obtain ⟨τ, _, hτ⟩ := hUniq x (σ x) (harcσ x)
    exact (hτ σ ⟨hσ, rfl⟩).trans (hτ ρ ⟨hρ, hx.symm⟩).symm
  have hT : ∀ (ρ : Equiv.Perm (ZMod 9)) (z : ZMod 9),
      (Equiv.addRight (1 : ZMod 9) * ρ * (Equiv.addRight (1 : ZMod 9))⁻¹) z = ρ (z + -1) + 1 := by
    intro ρ z
    simp [Equiv.Perm.mul_apply]
  have hshift : ∀ m : ℕ, ∀ σ ∈ F, ∃ ρ ∈ F, ∀ z : ZMod 9, ρ z = σ (z - m) + m := by
    intro m
    induction m with
    | zero =>
      intro σ hσ
      exact ⟨σ, hσ, fun z => by simp⟩
    | succ m ih =>
      intro σ hσ
      obtain ⟨ρ, hρ, hρz⟩ := ih σ hσ
      refine ⟨_, hConj ρ hρ, fun z => ?_⟩
      have e : z + -1 - (m : ZMod 9) = z - ((m + 1 : ℕ) : ZMod 9) := by
        push_cast
        ring
      rw [hT, hρz, e]
      push_cast
      ring
  obtain ⟨σ, ⟨hσF, hσ0⟩, _⟩ := hUniq 0 3 (by
    show ((3 : ZMod 9) - 0).val ∈ Finset.Icc 1 ((9 - 1) / 2)
    decide)
  obtain ⟨hcyc, hfix, harc⟩ := hHam σ hσF
  have harc' : ∀ x : ZMod 9, (σ x - x).val ∈ Finset.Icc 1 4 := by
    intro x
    have h := harc x
    unfold IsArc at h
    exact h
  obtain ⟨x, _, y, _, hxy, hfxy⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := (Finset.univ : Finset (ZMod 9))) (t := Finset.Icc 1 4) (by decide)
    (f := fun x => (σ x - x).val) (fun a _ => harc' a)
  have hd : σ x - x = σ y - y := ZMod.val_injective 9 hfxy
  have hk0 : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  obtain ⟨ρ, hρF, hρz⟩ := hshift (y - x).val σ hσF
  have hk : (((y - x).val : ℕ) : ZMod 9) = y - x := ZMod.natCast_zmod_val (y - x)
  have hρy : ρ y = σ y := by
    have e : y - (y - x) = x := by ring
    rw [hρz, hk, e]
    linear_combination hd
  have hρσ : ρ = σ := hagree ρ hρF σ hσF y hρy
  have hsh : ∀ z : ZMod 9, σ (z + (y - x)) = σ z + (y - x) := by
    intro z
    have h1 := hρz (z + (y - x))
    have e : z + (y - x) - (y - x) = z := by ring
    rw [hρσ, hk, e] at h1
    exact h1
  have hiter : ∀ j : ℕ, σ ((j : ZMod 9) * (y - x)) = 3 + (j : ZMod 9) * (y - x) := by
    intro j
    induction j with
    | zero => simpa using hσ0
    | succ j ih =>
      have e : ((j + 1 : ℕ) : ZMod 9) * (y - x) = (j : ZMod 9) * (y - x) + (y - x) := by
        push_cast
        ring
      rw [e, hsh, ih]
      ring
  have hdec : ∀ k : ZMod 9, k ≠ 0 → (∃ j : ZMod 9, j * k = 3) ∧ (∃ j : ZMod 9, j * k = 6) := by
    decide
  obtain ⟨⟨j3, hj3⟩, ⟨j6, hj6⟩⟩ := hdec (y - x) hk0
  have hσ3 : σ 3 = 6 := by
    have h := hiter j3.val
    rw [ZMod.natCast_zmod_val, hj3] at h
    rw [h]
    decide
  have hσ6 : σ 6 = 0 := by
    have h := hiter j6.val
    rw [ZMod.natCast_zmod_val, hj6] at h
    rw [h]
    decide
  have hinv : ∀ i : ℕ, (σ ^ i) 0 = 0 ∨ (σ ^ i) 0 = 3 ∨ (σ ^ i) 0 = 6 := by
    intro i
    induction i with
    | zero =>
      left
      simp
    | succ i ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      rcases ih with h | h | h
      · rw [h, hσ0]
        right
        left
        rfl
      · rw [h, hσ3]
        right
        right
        rfl
      · rw [h, hσ6]
        left
        rfl
  obtain ⟨i, hi⟩ := hcyc.exists_pow_eq (hfix 0) (hfix 1)
  rcases hinv i with h | h | h
  · rw [h] at hi
    exact absurd hi (by decide)
  · rw [h] at hi
    exact absurd hi (by decide)
  · rw [h] at hi
    exact absurd hi (by decide)
