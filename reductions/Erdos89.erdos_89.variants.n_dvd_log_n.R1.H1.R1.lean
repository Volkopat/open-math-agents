import OMAReductions.R_Erdos89_erdos_89_variants_n_dvd_log_n_R1

/-!
A finite form of the Elekes–Sharir motion reduction. The two inputs are
the endpoint bound for 2-rich motions and the uniform bound for k-rich
motions for k at least 3. The summation and encoding are proved here.
Guth–Katz, On the Erdős distinct distances problem in the plane,
Ann. of Math. 181 (2015), 155–190, Sections 2 and 3.
-/
namespace OMA.R_Erdos89_erdos_89_variants_n_dvd_log_n_R1_H1_R1

open Finset Filter EuclideanGeometry
open scoped Classical

/-- The endpoint incidence bound for distinct motions carrying at least two points. -/
def H1 : Prop := ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℝ²) (T : Finset (ℂ × ℂ)),
  (∀ g ∈ T, ‖g.1‖ = 1 ∧ 2 ≤ (S.filter fun x =>
    Complex.orthonormalBasisOneI.repr (g.1 * Complex.orthonormalBasisOneI.repr.symm x + g.2) ∈ S).card) →
  (T.card : ℝ) ≤ C * (S.card : ℝ)^3

/-- The incidence bound for k-rich motions, k at least three. -/
def H2 : Prop := ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℝ²) (T : Finset (ℂ × ℂ)) (k : ℕ), 3 ≤ k →
  (∀ g ∈ T, ‖g.1‖ = 1 ∧ k ≤ (S.filter fun x =>
    Complex.orthonormalBasisOneI.repr (g.1 * Complex.orthonormalBasisOneI.repr.symm x + g.2) ∈ S).card) →
  (T.card : ℝ) ≤ C * (S.card : ℝ)^3 / (k : ℝ)^2

lemma key_endpoints (q : (ℝ² × ℝ²) × (ℝ² × ℝ²)) (h : q.1.1 ≠ q.1.2) :
    let c := Complex.orthonormalBasisOneI.repr.symm
    let u := (c q.2.1 - c q.2.2) / (c q.1.1 - c q.1.2)
    let g := (u, c q.2.1 - u * c q.1.1)
    g.1 * c q.1.1 + g.2 = c q.2.1 ∧ g.1 * c q.1.2 + g.2 = c q.2.2 := by
  let c := Complex.orthonormalBasisOneI.repr.symm
  have hne : c q.1.1 - c q.1.2 ≠ 0 := sub_ne_zero.mpr (fun he => h (c.injective he))
  dsimp only
  constructor
  · ring
  · let a := c q.1.1
    let b := c q.1.2
    let x := c q.2.1
    let y := c q.2.2
    change ((x - y) / (a - b)) * b + (x - ((x - y) / (a - b)) * a) = y
    calc
      _ = x - ((x - y) / (a - b)) * (a - b) := by ring
      _ = y := by rw [div_mul_cancel₀ _ hne]; ring

lemma key_unit {S : Finset ℝ²} {q : (ℝ² × ℝ²) × (ℝ² × ℝ²)} (hq : q ∈ ((S.offDiag ×ˢ S.offDiag).filter (fun z => dist z.1.1 z.1.2 = dist z.2.1 z.2.2))) :
    ‖((let u := (Complex.orthonormalBasisOneI.repr.symm q.2.1 - Complex.orthonormalBasisOneI.repr.symm q.2.2) / (Complex.orthonormalBasisOneI.repr.symm q.1.1 - Complex.orthonormalBasisOneI.repr.symm q.1.2); (u, Complex.orthonormalBasisOneI.repr.symm q.2.1 - u * Complex.orthonormalBasisOneI.repr.symm q.1.1))).1‖ = 1 := by
  obtain ⟨hp, hd⟩ := Finset.mem_filter.mp hq
  have ha := (Finset.mem_offDiag.mp (Finset.mem_product.mp hp).1).2.2
  have he : ‖Complex.orthonormalBasisOneI.repr.symm q.2.1 - Complex.orthonormalBasisOneI.repr.symm q.2.2‖ = ‖Complex.orthonormalBasisOneI.repr.symm q.1.1 - Complex.orthonormalBasisOneI.repr.symm q.1.2‖ := by
    rw [← dist_eq_norm, ← dist_eq_norm, Complex.orthonormalBasisOneI.repr.symm.isometry.dist_eq, Complex.orthonormalBasisOneI.repr.symm.isometry.dist_eq, hd]
  change ‖(Complex.orthonormalBasisOneI.repr.symm q.2.1 - Complex.orthonormalBasisOneI.repr.symm q.2.2) / (Complex.orthonormalBasisOneI.repr.symm q.1.1 - Complex.orthonormalBasisOneI.repr.symm q.1.2)‖ = 1
  rw [norm_div, he, div_self (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (fun h => ha (Complex.orthonormalBasisOneI.repr.symm.injective h))))]

lemma fiber_bound (S : Finset ℝ²) (g : ℂ × ℂ) :
    ((((S.offDiag ×ˢ S.offDiag).filter (fun z => dist z.1.1 z.1.2 = dist z.2.1 z.2.2))).filter fun q => (let u := (Complex.orthonormalBasisOneI.repr.symm q.2.1 - Complex.orthonormalBasisOneI.repr.symm q.2.2) / (Complex.orthonormalBasisOneI.repr.symm q.1.1 - Complex.orthonormalBasisOneI.repr.symm q.1.2); (u, Complex.orthonormalBasisOneI.repr.symm q.2.1 - u * Complex.orthonormalBasisOneI.repr.symm q.1.1)) = g).card ≤ ((S.filter fun x => Complex.orthonormalBasisOneI.repr (g.1 * Complex.orthonormalBasisOneI.repr.symm x + g.2) ∈ S)).card ^ 2 := by
  rw [pow_two, ← Finset.card_product]
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro q hq
    simp only [Finset.mem_coe] at hq ⊢
    obtain ⟨he, hg⟩ := Finset.mem_filter.mp hq
    obtain ⟨hp, _⟩ := Finset.mem_filter.mp he
    obtain ⟨ha, hb, hn⟩ := Finset.mem_offDiag.mp (Finset.mem_product.mp hp).1
    obtain ⟨hc, hd, _⟩ := Finset.mem_offDiag.mp (Finset.mem_product.mp hp).2
    obtain ⟨h₁, h₂⟩ := key_endpoints q hn
    rw [hg] at h₁ h₂
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨ha, by rw [h₁, LinearIsometryEquiv.apply_symm_apply]; exact hc⟩,
      Finset.mem_filter.mpr ⟨hb, by rw [h₂, LinearIsometryEquiv.apply_symm_apply]; exact hd⟩⟩
  · intro p hp q hq hf
    simp only [Finset.mem_coe] at hp hq
    obtain ⟨he, hg⟩ := Finset.mem_filter.mp hp
    obtain ⟨he', hg'⟩ := Finset.mem_filter.mp hq
    have hn := (Finset.mem_offDiag.mp (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1).2.2
    have hn' := (Finset.mem_offDiag.mp (Finset.mem_product.mp (Finset.mem_filter.mp he').1).1).2.2
    obtain ⟨h₁,h₂⟩ := key_endpoints p hn
    obtain ⟨h₁',h₂'⟩ := key_endpoints q hn'
    change p.1 = q.1 at hf
    rw [hg, hf] at h₁ h₂
    rw [hg'] at h₁' h₂'
    exact Prod.ext hf (Prod.ext (Complex.orthonormalBasisOneI.repr.symm.injective (h₁.symm.trans h₁')) (Complex.orthonormalBasisOneI.repr.symm.injective (h₂.symm.trans h₂')))

lemma key_rich {S : Finset ℝ²} {q : (ℝ² × ℝ²) × (ℝ² × ℝ²)} (hq : q ∈ ((S.offDiag ×ˢ S.offDiag).filter (fun z => dist z.1.1 z.1.2 = dist z.2.1 z.2.2))) :
    2 ≤ ((S.filter fun x => Complex.orthonormalBasisOneI.repr (((let u := (Complex.orthonormalBasisOneI.repr.symm q.2.1 - Complex.orthonormalBasisOneI.repr.symm q.2.2) / (Complex.orthonormalBasisOneI.repr.symm q.1.1 - Complex.orthonormalBasisOneI.repr.symm q.1.2); (u, Complex.orthonormalBasisOneI.repr.symm q.2.1 - u * Complex.orthonormalBasisOneI.repr.symm q.1.1))).1 * Complex.orthonormalBasisOneI.repr.symm x + ((let u := (Complex.orthonormalBasisOneI.repr.symm q.2.1 - Complex.orthonormalBasisOneI.repr.symm q.2.2) / (Complex.orthonormalBasisOneI.repr.symm q.1.1 - Complex.orthonormalBasisOneI.repr.symm q.1.2); (u, Complex.orthonormalBasisOneI.repr.symm q.2.1 - u * Complex.orthonormalBasisOneI.repr.symm q.1.1))).2) ∈ S)).card := by
  obtain ⟨hp, _⟩ := Finset.mem_filter.mp hq
  obtain ⟨ha, hb, hn⟩ := Finset.mem_offDiag.mp (Finset.mem_product.mp hp).1
  obtain ⟨hc, hd, _⟩ := Finset.mem_offDiag.mp (Finset.mem_product.mp hp).2
  obtain ⟨h₁, h₂⟩ := key_endpoints q hn
  apply Finset.one_lt_card.mpr
  refine ⟨q.1.1, Finset.mem_filter.mpr ⟨ha, ?_⟩, q.1.2, Finset.mem_filter.mpr ⟨hb, ?_⟩, hn⟩
  · rw [h₁, LinearIsometryEquiv.apply_symm_apply]
    exact hc
  · rw [h₂, LinearIsometryEquiv.apply_symm_apply]
    exact hd

lemma square_as_tail (w n : ℕ) (h : w ≤ n) :
    (w : ℝ)^2 = ∑ k ∈ Finset.Icc 1 n, if k ≤ w then (2 * (k : ℝ) - 1) else 0 := by
  rw [← Finset.sum_filter]
  have hs : ((Finset.Icc 1 n).filter fun k => k ≤ w) = Finset.Icc 1 w := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hs]
  clear hs h n
  induction w with
  | zero => simp
  | succ w ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ w + 1), ← ih]
      push_cast
      ring

/-- A finite tail estimate independent of geometry. -/
lemma tail_bound {α : Type*} (T : Finset α) (w : α → ℕ) (n : ℕ) (B : ℝ)
    (hw : ∀ g ∈ T, w g ≤ n)
    (hr : ∀ k ∈ Finset.Icc 1 n, (((T.filter fun g => k ≤ w g).card : ℕ) : ℝ)
      ≤ B / (k : ℝ)^2) :
    (∑ g ∈ T, (w g : ℝ)^2) ≤ (2 * B) * (harmonic n : ℝ) := by
  classical
  calc
    (∑ g ∈ T, (w g : ℝ)^2) =
        ∑ g ∈ T, ∑ k ∈ Finset.Icc 1 n, if k ≤ w g then (2 * (k : ℝ) - 1) else 0 :=
      Finset.sum_congr rfl fun g hg => square_as_tail (w g) n (hw g hg)
    _ = ∑ k ∈ Finset.Icc 1 n, (((T.filter fun g => k ≤ w g).card : ℕ) : ℝ) *
          (2 * (k : ℝ) - 1) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_filter]
      simp <;> ring
    _ ≤ ∑ k ∈ Finset.Icc 1 n, (2 * B) * (k : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro k hk
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Icc.mp hk).1
      have hk0 : (0 : ℝ) < k := by linarith
      calc
        _ ≤ (((T.filter fun g => k ≤ w g).card : ℕ) : ℝ) * (2 * (k : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ ≤ (B / (k : ℝ)^2) * (2 * (k : ℝ)) :=
          mul_le_mul_of_nonneg_right (hr k hk) (by positivity)
        _ = (2 * B) * (k : ℝ)⁻¹ := by field_simp
    _ = (2 * B) * (harmonic n : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum, Finset.mul_sum]
      simp only [Rat.cast_inv, Rat.cast_natCast]

theorem main : H1 → H2 → OMA.R_Erdos89_erdos_89_variants_n_dvd_log_n_R1.H1 := by
  classical
  rintro ⟨A, hA, ha⟩ ⟨D, hD, hd⟩
  let M := max A D
  have hM : 0 < M := hA.trans_le (le_max_left _ _)
  refine ⟨8 * M * (1 + (Real.log 2)⁻¹), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with n hn S hS
  change ((((S.offDiag ×ˢ S.offDiag).filter (fun z => dist z.1.1 z.1.2 = dist z.2.1 z.2.2))).card : ℝ) ≤ 8 * M * (1 + (Real.log 2)⁻¹) * (n : ℝ)^3 * Real.log n
  let E := (S.offDiag ×ˢ S.offDiag).filter
    (fun z => dist z.1.1 z.1.2 = dist z.2.1 z.2.2)
  let c := Complex.orthonormalBasisOneI.repr.symm
  let f := fun q : (ℝ² × ℝ²) × (ℝ² × ℝ²) =>
    let u := (c q.2.1 - c q.2.2) / (c q.1.1 - c q.1.2)
    (u, c q.2.1 - u * c q.1.1)
  let T := E.image f
  let w := fun g : ℂ × ℂ => ((S.filter fun x => Complex.orthonormalBasisOneI.repr (g.1 * Complex.orthonormalBasisOneI.repr.symm x + g.2) ∈ S)).card
  let B := 4 * M * (n : ℝ)^3
  have hunit : ∀ g ∈ T, ‖g.1‖ = 1 ∧ 2 ≤ w g := by
    intro g hg
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hg
    exact ⟨key_unit hq, key_rich hq⟩
  have hmaxA : A ≤ M := le_max_left _ _
  have hmaxD : D ≤ M := le_max_right _ _
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hln : Real.log 2 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hcount : (E.card : ℝ) ≤ ∑ g ∈ T, (w g : ℝ)^2 := by
    have he : E.card = ∑ g ∈ T, (E.filter fun q => f q = g).card :=
      Finset.card_eq_sum_card_image f E
    rw [he, Nat.cast_sum]
    exact Finset.sum_le_sum fun g _ => by exact_mod_cast fiber_bound S g
  have htail := tail_bound T w n B
    (fun g _ => hS ▸ Finset.card_le_card (Finset.filter_subset _ S))
    (by
      intro k hk
      let R := T.filter fun g => k ≤ w g
      change (R.card : ℝ) ≤ B / (k : ℝ)^2
      have hk1 := (Finset.mem_Icc.mp hk).1
      have hk0 : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
      have hpow : 0 < (k : ℝ)^2 := by positivity
      by_cases h3 : 3 ≤ k
      · have hR : ∀ g ∈ R, ‖g.1‖ = 1 ∧ k ≤ w g := by
          intro g hg
          exact ⟨(hunit g (Finset.mem_filter.mp hg).1).1, (Finset.mem_filter.mp hg).2⟩
        apply (hd S R k h3 hR).trans
        rw [hS]
        apply div_le_div_of_nonneg_right _ hpow.le
        dsimp [B]
        gcongr
        linarith
      · have hsmall : (k : ℝ) ≤ 2 := by exact_mod_cast (show k ≤ 2 by omega)
        have hsub : (R.card : ℝ) ≤ (T.card : ℝ) := by
          exact_mod_cast Finset.card_le_card (Finset.filter_subset (fun g => k ≤ w g) T)
        have hTa : (T.card : ℝ) ≤ A * (n : ℝ)^3 := by simpa only [hS] using ha S T hunit
        refine hsub.trans (hTa.trans ((le_div_iff₀ hpow).mpr ?_))
        have hkle : (k : ℝ)^2 ≤ 4 := by nlinarith
        calc
          _ ≤ (M * (n : ℝ)^3) * 4 := by gcongr
          _ = B := by dsimp [B]; ring)
  have hH : (harmonic n : ℝ) ≤ (1 + (Real.log 2)⁻¹) * Real.log n := by
    apply (harmonic_le_one_add_log n).trans
    have hi : (1 : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := (le_div_iff₀ hlog).mpr (by simpa using hln)
    rw [add_mul, one_mul, mul_comm (Real.log 2)⁻¹, ← div_eq_mul_inv]
    linarith
  calc
    _ ≤ (2 * B) * (harmonic n : ℝ) := hcount.trans htail
    _ ≤ (2 * B) * ((1 + (Real.log 2)⁻¹) * Real.log n) :=
      mul_le_mul_of_nonneg_left hH (by dsimp [B]; positivity)
    _ = _ := by dsimp [B]; ring

end OMA.R_Erdos89_erdos_89_variants_n_dvd_log_n_R1_H1_R1
