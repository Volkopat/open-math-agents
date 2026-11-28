import OMAReductions.R_Erdos441_erdos_441_variants_chen_dai_upper_bound_R1
import Mathlib
-- Credit: @LordMike

theorem OMA.solution : OMA.R_Erdos441_erdos_441_variants_chen_dai_upper_bound_R1.H1 := by
  unfold OMA.R_Erdos441_erdos_441_variants_chen_dai_upper_bound_R1.H1
  refine ⟨3, fun N => ?_⟩
  set a := Nat.sqrt (N / 2) with ha
  set b := Nat.sqrt (2 * N) with hb
  have ha1 : a * a ≤ N / 2 := Nat.sqrt_le _
  have ha2 : N / 2 < (a + 1) * (a + 1) := Nat.lt_succ_sqrt _
  have hb1 : b * b ≤ 2 * N := Nat.sqrt_le _
  have hb2 : 2 * N < (b + 1) * (b + 1) := Nat.lt_succ_sqrt _
  have haN : a ≤ N := by nlinarith [Nat.sqrt_le_self (N / 2), Nat.div_le_self N 2]
  have hbN : b ≤ N := by
    by_contra h
    push_neg at h
    nlinarith
  have haa : 2 * (a * a) ≤ N := by omega
  have hab : a ≤ b := by
    by_contra h
    push_neg at h
    nlinarith
  set A : Finset ℕ := (Finset.Icc 1 N).filter (fun x => x ≤ a ∨ (2 ∣ x ∧ x ≤ b)) with hA
  have hAsub : A ⊆ Finset.Icc 1 N := Finset.filter_subset _ _
  have hlcm : ∀ x ∈ A, ∀ y ∈ A, Nat.lcm x y ≤ N := by
    intro x hx y hy
    simp only [hA, Finset.mem_filter, Finset.mem_Icc] at hx hy
    obtain ⟨⟨hx1, hxN⟩, hxc⟩ := hx
    obtain ⟨⟨hy1, hyN⟩, hyc⟩ := hy
    have hg := Nat.gcd_mul_lcm x y
    have hgpos : 0 < Nat.gcd x y := Nat.gcd_pos_of_pos_left _ (by omega)
    have hl : Nat.lcm x y ≤ x * y := by
      by_contra h
      push_neg at h
      nlinarith
    have key : ∀ p q : ℕ, p ≤ a → q ≤ b → p * q ≤ N := by
      intro p q hp hq
      have h1 : (p * q) * (p * q) ≤ N * N := by
        have : (p * q) * (p * q) = (p * p) * (q * q) := by ring
        rw [this]
        have hpp : p * p ≤ a * a := Nat.mul_le_mul hp hp
        have hqq : q * q ≤ b * b := Nat.mul_le_mul hq hq
        nlinarith
      exact Nat.mul_self_le_mul_self_iff.mp h1
    rcases hxc with hxa | ⟨hx2, hxb⟩ <;> rcases hyc with hya | ⟨hy2, hyb⟩
    · exact hl.trans (key x y hxa (hya.trans hab))
    · exact hl.trans (key x y hxa hyb)
    · exact hl.trans (by rw [mul_comm]; exact key y x hya hxb)
    · have h2 : 2 ≤ Nat.gcd x y := by
        have := Nat.dvd_gcd hx2 hy2
        exact Nat.le_of_dvd hgpos this
      have hxy : x * y ≤ b * b := Nat.mul_le_mul hxb hyb
      nlinarith
  have hmem : A.card ∈ {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
      (∀ a ∈ A, ∀ b ∈ A, Nat.lcm a b ≤ N) ∧ A.card = k} := ⟨A, hAsub, hlcm, rfl⟩
  have hbdd : BddAbove {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
      (∀ a ∈ A, ∀ b ∈ A, Nat.lcm a b ≤ N) ∧ A.card = k} := by
    refine ⟨N, ?_⟩
    rintro k ⟨B, hB, -, rfl⟩
    simpa using Finset.card_le_card hB
  have hgN : A.card ≤ Erdos441.g N := le_csSup hbdd hmem
  have hS1 : Finset.Icc 1 a ⊆ A := by
    intro x hx
    simp only [Finset.mem_Icc] at hx
    simp only [hA, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hx.1, hx.2.trans haN⟩, Or.inl hx.2⟩
  have hS2 : (Finset.Ioc (a / 2) (b / 2)).image (fun k => 2 * k) ⊆ A := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_Ioc] at hx
    obtain ⟨k, ⟨hk1, hk2⟩, rfl⟩ := hx
    simp only [hA, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, Or.inr ⟨dvd_mul_right _ _, by omega⟩⟩
  have hdisj : Disjoint (Finset.Icc 1 a) ((Finset.Ioc (a / 2) (b / 2)).image (fun k => 2 * k)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_image, Finset.mem_Ioc, Finset.mem_Icc] at hx hx'
    obtain ⟨k, ⟨hk1, hk2⟩, rfl⟩ := hx'
    omega
  have hcardS2 : ((Finset.Ioc (a / 2) (b / 2)).image (fun k => 2 * k)).card = b / 2 - a / 2 := by
    rw [Finset.card_image_of_injective _ (fun x y h => by simpa using h), Nat.card_Ioc]
  have hcard : a + (b / 2 - a / 2) ≤ A.card := by
    have := Finset.card_le_card (Finset.union_subset hS1 hS2)
    rw [Finset.card_union_of_disjoint hdisj, hcardS2] at this
    simpa using this
  have hcardR : (a : ℝ) / 2 + (b : ℝ) / 2 - 1 ≤ A.card := by
    have h1 : (a : ℝ) + ((b / 2 - a / 2 : ℕ) : ℝ) ≤ A.card := by exact_mod_cast hcard
    have h2 : ((b / 2 - a / 2 : ℕ) : ℝ) ≥ ((b / 2 : ℕ) : ℝ) - ((a / 2 : ℕ) : ℝ) := by
      have h5 : (b / 2 : ℕ) ≤ (b / 2 - a / 2 : ℕ) + a / 2 := by omega
      have : ((b / 2 : ℕ) : ℝ) ≤ ((b / 2 - a / 2 : ℕ) : ℝ) + ((a / 2 : ℕ) : ℝ) := by
        exact_mod_cast h5
      linarith
    have h3 : (b : ℝ) ≤ 2 * ((b / 2 : ℕ) : ℝ) + 1 := by
      have h6 : b ≤ 2 * (b / 2) + 1 := by omega
      exact_mod_cast h6
    have h4 : 2 * ((a / 2 : ℕ) : ℝ) ≤ (a : ℝ) := by
      have h7 : 2 * (a / 2) ≤ a := by omega
      exact_mod_cast h7
    linarith
  have hNR : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hsa : √((N : ℝ) / 2) ≤ a + 1 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have h8 : N ≤ 2 * ((a + 1) * (a + 1)) := by omega
    have : (N : ℝ) ≤ 2 * (((a : ℝ) + 1) * ((a : ℝ) + 1)) := by exact_mod_cast h8
    nlinarith
  have hsb : √(2 * (N : ℝ)) ≤ b + 1 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have h9 : 2 * N ≤ (b + 1) * (b + 1) := by omega
    have : 2 * (N : ℝ) ≤ ((b : ℝ) + 1) * ((b : ℝ) + 1) := by exact_mod_cast h9
    nlinarith
  have hprod : √((N : ℝ) / 2) * √(2 * (N : ℝ)) = N := by
    rw [← Real.sqrt_mul (by positivity)]
    have : (N : ℝ) / 2 * (2 * N) = (N : ℝ) ^ 2 := by ring
    rw [this, Real.sqrt_sq hNR]
  have hmain : √(9 / 8 * (N : ℝ)) ≤ (√((N : ℝ) / 2) + √(2 * (N : ℝ))) / 2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have e1 := Real.sq_sqrt (show (0 : ℝ) ≤ (N : ℝ) / 2 by positivity)
    have e2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * (N : ℝ) by positivity)
    nlinarith
  have hfin : √(9 / 8 * (N : ℝ)) - 3 ≤ A.card := by linarith
  exact hfin.trans (by exact_mod_cast hgN)
