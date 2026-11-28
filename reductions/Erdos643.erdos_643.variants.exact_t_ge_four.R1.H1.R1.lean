import OMAReductions.R_Erdos643_erdos_643_variants_exact_t_ge_four_R1

namespace OMA.R_Erdos643_erdos_643_variants_exact_t_ge_four_R1_H1_R1

open Filter

/-- Completions of a core by an off-center vertex outside the exceptional set. -/
private def completions {n : ℕ}
    (G : Finset (Finset (Fin n))) (v : Fin n) (U S : Finset (Fin n)) :
    Finset (Fin n) :=
  (Finset.univ.erase v \ U).filter fun x => x ∉ S ∧ insert x S ∈ G

/-- Aligned local stars give the exceptional-set hypothesis (Lemma 3.2). -/
private theorem completion_bound {n t : ℕ} {G : Finset (Finset (Fin n))}
    {v : Fin n} {W : Finset (Fin n)}
    (align : ∀ (S : Finset (Fin n)) (x y : Fin n), S.card = t - 1 →
      x ∈ W → y ∈ W → x ≠ y → x ∉ S → y ∉ S →
      insert x S ∈ G → insert y S ∈ G → v ∈ S)
    {S : Finset (Fin n)} (hS : S.card = t - 1) (hv : v ∉ S) :
    (completions G v (Finset.univ.erase v \ W) S).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro x hx y hy
  have expand {z : Fin n} (hz : z ∈ completions G v (Finset.univ.erase v \ W) S) :
      z ∈ W ∧ z ∉ S ∧ insert z S ∈ G := by
    obtain ⟨hzU, hzS, hzG⟩ := Finset.mem_filter.mp hz
    obtain ⟨hzv, hnot⟩ := Finset.mem_sdiff.mp hzU
    exact ⟨not_not.mp (fun hzW => hnot (Finset.mem_sdiff.mpr ⟨hzv, hzW⟩)), hzS, hzG⟩
  obtain ⟨hxW, hxS, hxG⟩ := expand hx
  obtain ⟨hyW, hyS, hyG⟩ := expand hy
  by_contra hxy
  exact hv (align S x y hS hxW hyW hxy hxS hyS hxG hyG)

private theorem avoiding_subset {n : ℕ} {F G : Finset (Finset (Fin n))}
    (sub : G ⊆ F) (avoid : ¬ F.HasRepeatedDisjointUnion) :
    ¬ G.HasRepeatedDisjointUnion := by
  rintro ⟨A, hA, B, hB, C, hC, D, hD, hAB, hCD, heq, hABne, hCDne,
    hAC, hAD, hBC, hBD⟩
  exact avoid ⟨A, sub hA, B, sub hB, C, sub hC, D, sub hD, hAB, hCD, heq,
    hABne, hCDne, hAC, hAD, hBC, hBD⟩

private theorem choose_shift (a k : ℕ) :
    a.choose 3 ≤ (a + k).choose (3 + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, Nat.add_succ, Nat.choose_succ_succ]
    exact ih.trans (Nat.le_add_right _ _)

/-- A quadratic deficit is eventually smaller than any positive fraction of a star. -/
private theorem square_le_star_fraction {t : ℕ} (ht : 4 ≤ t) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 2 ≤ δ * ((n - 1).choose (t - 1) : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (48 / δ)
  filter_upwards [eventually_ge_atTop (2 * t), eventually_ge_atTop N] with n hn hnN
  let a := n - t + 3
  have hshift := choose_shift a (t - 4)
  rw [show a + (t - 4) = n - 1 by dsimp [a]; omega,
    show 3 + (t - 4) = t - 1 by omega] at hshift
  have hchoose : (a.choose 3 : ℝ) ≤ ((n - 1).choose (t - 1) : ℝ) := by
    exact_mod_cast hshift
  have h0 : (n : ℝ) ≤ 2 * (a : ℝ) := by
    exact_mod_cast (show n ≤ 2 * a by dsimp [a]; omega)
  have h1 : (n : ℝ) ≤ 2 * ((a - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show n ≤ 2 * (a - 1) by dsimp [a]; omega)
  have h2 : (n : ℝ) ≤ 2 * ((a - 2 : ℕ) : ℝ) := by
    exact_mod_cast (show n ≤ 2 * (a - 2) by dsimp [a]; omega)
  have hfac := Nat.descFactorial_eq_factorial_mul_choose a 3
  change (a - 2) * ((a - 1) * (a * 1)) = 6 * a.choose 3 at hfac
  simp only [Nat.mul_one] at hfac
  have hprod : ((a - 2 : ℕ) : ℝ) * (((a - 1 : ℕ) : ℝ) * (a : ℝ)) =
      6 * (a.choose 3 : ℝ) := by exact_mod_cast hfac
  have hcube : (n : ℝ) ^ 3 ≤ 48 * (a.choose 3 : ℝ) := calc
    (n : ℝ) ^ 3 = (n : ℝ) * ((n : ℝ) * (n : ℝ)) := by ring
    _ ≤ (2 * ((a - 2 : ℕ) : ℝ)) * ((2 * ((a - 1 : ℕ) : ℝ)) * (2 * (a : ℝ))) :=
      mul_le_mul h2 (mul_le_mul h1 h0 (by positivity) (by positivity))
        (by positivity) (by positivity)
    _ = 48 * (a.choose 3 : ℝ) := by linear_combination 8 * hprod
  have hN' : 48 / δ ≤ (n : ℝ) := hN.trans (by exact_mod_cast hnN)
  have hnδ : 48 ≤ (n : ℝ) * δ := (div_le_iff₀ hδ).mp hN'
  have hscaled := mul_le_mul_of_nonneg_right hnδ (sq_nonneg (n : ℝ))
  have hlarge := mul_le_mul_of_nonneg_left hcube hδ.le
  have hstar := mul_le_mul_of_nonneg_left hchoose hδ.le
  linarith [show (n : ℝ) * δ * (n : ℝ) ^ 2 = δ * (n : ℝ) ^ 3 by ring]

/-- Lemmas 2.1 and 2.2 of Huang, Ma and Yang give a dense subfamily with aligned
local stars. The parameter controls the density loss and exceptional set together. -/
def H1 : Prop :=
  ∀ t : ℕ, 4 ≤ t → ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
    ∀ F : Finset (Finset (Fin n)), F.IsUniform t → ¬ F.HasRepeatedDisjointUnion →
      (n - 1).choose (t - 1) + (n - 1) / t ≤ F.card →
      ∃ (G : Finset (Finset (Fin n))) (v : Fin n) (W : Finset (Fin n)),
        G ⊆ F ∧
        (1 - η) * ((n - 1).choose (t - 1) : ℝ) ≤ (G.card : ℝ) ∧
        ((Finset.univ.erase v \ W).card : ℝ) ≤ η * (n : ℝ) ∧
        (∀ (S : Finset (Fin n)) (x y : Fin n), S.card = t - 1 →
          x ∈ W → y ∈ W → x ≠ y → x ∉ S → y ∉ S →
          insert x S ∈ G → insert y S ∈ G → v ∈ S)

/-- A quadratic bound on the deficit when the density loss and exceptional set
are small. The counting argument of Lemma 3.3 yields the sharper n log n bound. -/
def H2 : Prop :=
  ∀ t : ℕ, 4 ≤ t → ∃ η : ℝ, 0 < η ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (G : Finset (Finset (Fin n))) (v : Fin n) (U : Finset (Fin n)),
        G.IsUniform t → ¬ G.HasRepeatedDisjointUnion →
        (1 - η) * ((n - 1).choose (t - 1) : ℝ) ≤ (G.card : ℝ) →
        (U.card : ℝ) ≤ η * (n : ℝ) →
        (∀ S : Finset (Fin n), S.card = t - 1 → v ∉ S →
          ((Finset.univ.erase v \ U).filter (fun x => x ∉ S ∧ insert x S ∈ G)).card ≤ 1) →
        (n - 1).choose (t - 1) - (G.filter fun E => v ∈ E).card ≤ n ^ 2

theorem main : H1 → H2 → OMA.R_Erdos643_erdos_643_variants_exact_t_ge_four_R1.H1 := by
  classical
  intro align deficit t ht δ hδ
  obtain ⟨η, hη, hdef⟩ := deficit t ht
  filter_upwards [align t ht η hη, hdef, square_le_star_fraction ht hδ] with n hlocal hcount hfraction
  intro F hF hfree hlarge
  obtain ⟨G, v, W, hsub, hGlarge, hW, halign⟩ := hlocal F hF hfree hlarge
  have hG : G.IsUniform t := fun E hE => hF E (hsub hE)
  have hsmall := hcount G v (Finset.univ.erase v \ W) hG
    (avoiding_subset hsub hfree) hGlarge hW (fun _ hS hv => completion_bound halign hS hv)
  have hdegrees : (G.filter fun E => v ∈ E).card ≤ (F.filter fun E => v ∈ E).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ hsub)
  have hmonotone :
      (↑((n - 1).choose (t - 1) - (F.filter fun E => v ∈ E).card) : ℝ) ≤
      ↑((n - 1).choose (t - 1) - (G.filter fun E => v ∈ E).card) := by
    exact_mod_cast Nat.sub_le_sub_left hdegrees ((n - 1).choose (t - 1))
  have hsmallReal :
      (↑((n - 1).choose (t - 1) - (G.filter fun E => v ∈ E).card) : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast hsmall
  exact ⟨v, hmonotone.trans (hsmallReal.trans hfraction)⟩

end OMA.R_Erdos643_erdos_643_variants_exact_t_ge_four_R1_H1_R1
