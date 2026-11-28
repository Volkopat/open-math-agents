import OMAReductions.R_LonelyRunnerConjecture_lonely_runner_conjecture_variants_tao_2017_R1

/-!
Reduction LonelyRunnerConjecture.lonely_runner_conjecture.variants.tao_2017.R1.H1.R1.
Arithmetic extraction and matching imply the dense-case overlap estimate.
Credit: @John-A-McMahon
-/

open MeasureTheory MeasureTheory.Measure Function Metric Set Filter

namespace OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_variants_tao_2017_R1_H1_R1

-- Pull back a small ball along multiplication by the common divisor.
lemma pair_overlap_lower_bound (n u v D : ℕ) (hn : 2 ≤ n)
    (hu : 0 < u) (_hv : 0 < v) (hD : 0 < D)
    (hheight : max u v ≤ D * Nat.gcd u v) :
    1 / ((n : ℝ) * D) ≤ volume.real
      (((fun t : UnitAddCircle => (u : ℤ) • t) ⁻¹'
          closedBall 0 (1 / (2 * (n : ℝ)))) ∩
       ((fun t : UnitAddCircle => (v : ℤ) • t) ⁻¹'
          closedBall 0 (1 / (2 * (n : ℝ))))) := by
  let g := Nat.gcd u v
  have hg : 0 < g := Nat.gcd_pos_of_pos_left v hu
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  let r : ℝ := 1 / (2 * (n : ℝ) * D)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hrsmall : 2 * r ≤ 1 := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
    have hND : (1 : ℝ) ≤ (n : ℝ) * D := by
      simpa using mul_le_mul hn1 hD1 zero_le_one (by positivity : (0 : ℝ) ≤ n)
    dsimp [r]
    rw [mul_one_div]
    apply (div_le_one (by positivity : (0 : ℝ) < 2 * n * D)).2
    nlinarith
  have hmul : (D : ℝ) * r = 1 / (2 * (n : ℝ)) := by
    dsimp [r]
    field_simp [hnR.ne', hDR.ne'] <;> ring
  have hsub (w : ℕ) (hw : g ∣ w) (hbound : w ≤ D * g) :
      (fun t : UnitAddCircle => (g : ℤ) • t) ⁻¹' closedBall 0 r ⊆
        (fun t : UnitAddCircle => (w : ℤ) • t) ⁻¹'
          closedBall 0 (1 / (2 * (n : ℝ))) := by
    intro t ht
    have hnorm : ‖(g : ℤ) • t‖ ≤ r := by
      simpa only [mem_preimage, mem_closedBall, dist_zero_right] using ht
    have hwD : w / g ≤ D := Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using hbound)
    have hwDR : ((w / g : ℕ) : ℝ) ≤ D := by exact_mod_cast hwD
    have heq : (w : ℤ) • t = (w / g : ℕ) • ((g : ℤ) • t) := by
      calc
        (w : ℤ) • t = (((w / g) * g : ℕ) : ℤ) • t := by
          rw [Nat.div_mul_cancel hw]
        _ = ((w / g : ℕ) : ℤ) • ((g : ℤ) • t) := by
          rw [Nat.cast_mul, mul_smul]
        _ = (w / g : ℕ) • ((g : ℤ) • t) := natCast_zsmul _ _
    change dist ((w : ℤ) • t) 0 ≤ _
    rw [dist_zero_right, heq]
    calc
      ‖(w / g : ℕ) • ((g : ℤ) • t)‖ ≤ ((w / g : ℕ) : ℝ) * ‖(g : ℤ) • t‖ :=
        norm_nsmul_le
      _ ≤ (D : ℝ) * r := mul_le_mul hwDR hnorm (norm_nonneg _) (by positivity)
      _ = _ := hmul
  have hm : MeasurePreserving (fun t : UnitAddCircle => (g : ℤ) • t) volume volume :=
    measurePreserving_zsmul volume (by exact_mod_cast hg.ne')
  have hmass : volume.real
      ((fun t : UnitAddCircle => (g : ℤ) • t) ⁻¹' closedBall 0 r) =
        1 / ((n : ℝ) * D) := by
    unfold Measure.real
    rw [hm.measure_preimage measurableSet_closedBall.nullMeasurableSet,
      AddCircle.volume_closedBall, ENNReal.toReal_ofReal (le_min zero_le_one (by positivity)),
      min_eq_right hrsmall]
    dsimp [r]
    field_simp [hnR.ne', hDR.ne'] <;> ring
  rw [← hmass]
  refine measureReal_mono ?_ (by finiteness)
  exact subset_inter
    (hsub u (Nat.gcd_dvd_left u v) ((le_max_left u v).trans hheight))
    (hsub v (Nat.gcd_dvd_right u v) ((le_max_right u v).trans hheight))

-- Arithmetic extraction from the proof of Hu and Jing, Theorem 7.2.
-- The bounded range of small n can be handled by one low-height pair.
def H1 : Prop :=
  ∃ θ C : ℝ, 0 < θ ∧ 1 ≤ C ∧
    ∀ (n : ℕ), 2 ≤ n → ∀ v : Fin n ↪ ℕ, (∀ i, 0 < v i) →
      n ^ 2 ≤ 64 * ((Finset.univ : Finset (Fin n × Fin n)).filter fun ij =>
        ij.1 < ij.2 ∧ max (v ij.1) (v ij.2) ≤
          64 * n * Nat.gcd (v ij.1) (v ij.2)).card →
      ∃ U : Finset (Fin n), 2 ≤ U.card ∧ θ * n ≤ U.card ∧
        ∃ (ξ : ℚ) (A B : ℕ), 0 < ξ ∧ 0 < A ∧ 0 < B ∧
          (A : ℝ) * B ≤ C * U.card ∧
          ∀ i ∈ U, ∃ a b : ℕ, 0 < a ∧ a ≤ A ∧ 0 < b ∧ b ≤ B ∧
            (v i : ℚ) = ξ * a / b

-- Arithmetic matching statement from the proof of Hu and Jing, Lemma 5.1.
def H2 : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∃ (D : ℕ) (η : ℝ), 0 < D ∧ 0 < η ∧
    ∀ (n : ℕ) (v : Fin n ↪ ℕ), (∀ i, 0 < v i) →
      ∀ U : Finset (Fin n), 2 ≤ U.card →
      ∀ (ξ : ℚ) (A B : ℕ), 0 < ξ → 0 < A → 0 < B →
        (A : ℝ) * B ≤ C * U.card →
        (∀ i ∈ U, ∃ a b : ℕ, 0 < a ∧ a ≤ A ∧ 0 < b ∧ b ≤ B ∧
          (v i : ℚ) = ξ * a / b) →
        ∃ (m : ℕ) (e : Fin m × Bool ↪ Fin n), η * U.card ≤ m ∧
          ∀ p : Fin m, e (p, false) ∈ U ∧ e (p, true) ∈ U ∧
            max (v (e (p, false))) (v (e (p, true))) ≤
              D * Nat.gcd (v (e (p, false))) (v (e (p, true)))

theorem main : H1 → H2 →
    OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_variants_tao_2017_R1.H1 := by
  classical
  rintro ⟨θ, C, hθ, hC, hextract⟩ hmatch
  obtain ⟨D, η, hD, hη, hmatching⟩ := hmatch C hC
  refine ⟨θ * η / D, by positivity, ?_⟩
  intro n hn v hv hdense
  obtain ⟨U, hU, hsize, ξ, A, B, hξ, hA, hB, harea, hrepr⟩ :=
    hextract n hn v hv hdense
  obtain ⟨m, e, hm, he⟩ := hmatching n v hv U hU ξ A B hξ hA hB harea hrepr
  let S (i : Fin n) : Set UnitAddCircle :=
    (fun t => (v i : ℤ) • t) ⁻¹' closedBall 0 (1 / (2 * (n : ℝ)))
  let F (i : Fin n) : ℝ := volume.real (S i ∩ ⋃ j, ⋃ (_ : j ≠ i), S j)
  change θ * η / (D : ℝ) ≤ ∑ i, F i
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hinj : Function.Injective (fun p : Fin m => e (p, false)) := by
    intro p q hpq
    exact congrArg Prod.fst (e.injective hpq)
  have hpoint (p : Fin m) : 1 / ((n : ℝ) * D) ≤ F (e (p, false)) := by
    have hne : e (p, true) ≠ e (p, false) := by
      intro h
      have hb : true = false := congrArg Prod.snd (e.injective h)
      cases hb
    have hpair := pair_overlap_lower_bound n (v (e (p, false))) (v (e (p, true))) D
      hn (hv _) (hv _) hD (he p).2.2
    apply hpair.trans
    refine measureReal_mono ?_ (by finiteness)
    rintro t ⟨ht, hs⟩
    exact ⟨ht, mem_iUnion.mpr ⟨e (p, true), mem_iUnion.mpr ⟨hne, hs⟩⟩⟩
  have hselected : (∑ p : Fin m, F (e (p, false))) ≤ ∑ i : Fin n, F i := by
    calc
      (∑ p : Fin m, F (e (p, false))) =
          ∑ i ∈ Finset.univ.image (fun p : Fin m => e (p, false)), F i := by
        rw [Finset.sum_image]
        exact fun _ _ _ _ h => hinj h
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => measureReal_nonneg)
  have hlower : (m : ℝ) / ((n : ℝ) * D) ≤ ∑ i : Fin n, F i := by
    calc
      (m : ℝ) / ((n : ℝ) * D) = ∑ _p : Fin m, 1 / ((n : ℝ) * D) := by
        simp [div_eq_mul_inv]
      _ ≤ ∑ p : Fin m, F (e (p, false)) := Finset.sum_le_sum fun p _ => hpoint p
      _ ≤ _ := hselected
  have hcount : θ * η * n ≤ (m : ℝ) := by
    calc
      θ * η * n = η * (θ * n) := by ring
      _ ≤ η * (U.card : ℝ) := mul_le_mul_of_nonneg_left hsize hη.le
      _ ≤ _ := hm
  calc
    θ * η / (D : ℝ) = (θ * η * n) / ((n : ℝ) * D) := by field_simp [hnR.ne', hDR.ne'] <;> ring
    _ ≤ (m : ℝ) / ((n : ℝ) * D) :=
      div_le_div_of_nonneg_right hcount (mul_pos hnR hDR).le
    _ ≤ _ := hlower

end OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_variants_tao_2017_R1_H1_R1
