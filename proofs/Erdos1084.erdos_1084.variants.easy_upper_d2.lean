import FormalConjectures.ErdosProblems.«1084»

/-! Pack unit neighbors into angular sectors and apply the degree-sum formula. -/

open scoped EuclideanGeometry

lemma OMA.unit_distance_chord_lt_one {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hangle : |x.arg - y.arg| < Real.pi / 3) : ‖x - y‖ < 1 := by
  have hx0 : x ≠ 0 := by
    intro h
    simp [h] at hx
  have hy0 : y ≠ 0 := by
    intro h
    simp [h] at hy
  have hx_sq : x.re * x.re + x.im * x.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hx, one_pow]
  have hy_sq : y.re * y.re + y.im * y.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hy, one_pow]
  have hdot : Real.cos (x.arg - y.arg) = x.re * y.re + x.im * y.im := by
    rw [Real.cos_sub, Complex.cos_arg hx0, Complex.cos_arg hy0, Complex.sin_arg, Complex.sin_arg]
    simp [hx, hy]
  have hdist_sq : ‖x - y‖ ^ 2 = 2 - 2 * Real.cos (x.arg - y.arg) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hdot]
    nlinarith only [hx_sq, hy_sq]
  have hπ := Real.pi_pos
  have hangle_mem : |x.arg - y.arg| ∈ Set.Icc (0 : ℝ) Real.pi :=
    ⟨abs_nonneg _, by linarith⟩
  have hπ_mem : Real.pi / 3 ∈ Set.Icc (0 : ℝ) Real.pi := ⟨by positivity, by linarith⟩
  have hcos := Real.strictAntiOn_cos hangle_mem hπ_mem hangle
  rw [Real.cos_pi_div_three, Real.cos_abs] at hcos
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by linarith [hdist_sq])

noncomputable def OMA.unit_distance_sector_coordinate (z : ℂ) : ℝ :=
  (Real.pi - z.arg) / (Real.pi / 3)

lemma OMA.unit_distance_sector_bound {A : Type*} (T : Finset A) (u : A → ℂ) (k : ℕ)
    (hnorm : ∀ a ∈ T, ‖u a‖ = 1)
    (hsep : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → 1 ≤ ‖u a - u b‖)
    (hlimit : ∀ a ∈ T, OMA.unit_distance_sector_coordinate (u a) < (k : ℝ)) :
    T.card ≤ k := by
  let sector (a : A) : ℕ := ⌊OMA.unit_distance_sector_coordinate (u a)⌋₊
  have hπ : 0 < Real.pi / 3 := by positivity
  have hnonneg (z : ℂ) : 0 ≤ OMA.unit_distance_sector_coordinate z :=
    div_nonneg (sub_nonneg.mpr (Complex.arg_le_pi z)) hπ.le
  rw [← Finset.card_range k]
  apply Finset.card_le_card_of_injOn sector
  · intro a ha
    exact Finset.mem_range.mpr ((Nat.floor_lt (hnonneg (u a))).mpr (hlimit a ha))
  · intro a ha b hb heq
    by_contra hab
    have hal := (Nat.floor_eq_iff (hnonneg (u a))).mp heq
    have hbl := (Nat.floor_eq_iff (hnonneg (u b))).mp (rfl : sector b = sector b)
    have hdiff : ((u a).arg - (u b).arg) / (Real.pi / 3) =
        OMA.unit_distance_sector_coordinate (u b) - OMA.unit_distance_sector_coordinate (u a) := by
      unfold OMA.unit_distance_sector_coordinate
      ring
    have hangle : |(u a).arg - (u b).arg| / (Real.pi / 3) < 1 := by
      rw [← abs_of_pos hπ, ← abs_div, hdiff, abs_lt]
      constructor <;> linarith [hal.1, hal.2, hbl.1, hbl.2]
    exact (not_lt_of_ge (hsep a ha b hb hab))
      (OMA.unit_distance_chord_lt_one (hnorm a ha) (hnorm b hb)
        (by simpa using (div_lt_iff₀ hπ).mp hangle))

lemma OMA.unit_distance_card_lt (S : Finset ℝ²) (hS : S.Nonempty)
    (hsep : Metric.IsSeparated' 1 (S : Set ℝ²)) : unitDistNum S < 3 * S.card := by
  classical
  let G : SimpleGraph (↥S) :=
    { Adj := fun a b => dist (a : ℝ²) (b : ℝ²) = 1
      symm := ⟨fun a b h => by simpa only [dist_comm (b : ℝ²) (a : ℝ²)] using h⟩
      loopless := ⟨fun a => by simp⟩ }
  let e : ℝ² ≃ₗᵢ[ℝ] ℂ := (Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)).symm
  let u (a b : ↥S) : ℂ := e (b : ℝ²) - e (a : ℝ²)
  have hnorm (a : ↥S) : ∀ b ∈ G.neighborFinset a, ‖u a b‖ = 1 := by
    intro b hb
    have hab : dist (a : ℝ²) (b : ℝ²) = 1 := (G.mem_neighborFinset a b).mp hb
    dsimp [u]
    rw [← dist_eq_norm, e.dist_map, dist_comm, hab]
  have hrad_sep (a : ↥S) : ∀ b ∈ G.neighborFinset a, ∀ c ∈ G.neighborFinset a,
      b ≠ c → 1 ≤ ‖u a b - u a c‖ := by
    intro b _ c _ hbc
    have hbne : (b : ℝ²) ≠ (c : ℝ²) := fun h => hbc (Subtype.ext h)
    have hd : (1 : ENNReal) ≤ edist (b : ℝ²) (c : ℝ²) := hsep b.property c.property hbne
    have hd' : 1 ≤ dist (b : ℝ²) (c : ℝ²) := by
      apply (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp
      simpa only [ENNReal.ofReal_one, ← edist_dist] using hd
    dsimp [u]
    rw [sub_sub_sub_cancel_right, ← dist_eq_norm, e.dist_map]
    exact hd'
  have hdeg (a : ↥S) : G.degree a ≤ 6 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply OMA.unit_distance_sector_bound (G.neighborFinset a) (u a) 6 (hnorm a) (hrad_sep a)
    intro b _
    unfold OMA.unit_distance_sector_coordinate
    apply (div_lt_iff₀ (by positivity : 0 < Real.pi / 3)).mpr
    linarith [Complex.neg_pi_lt_arg (u a b)]
  obtain ⟨p, hp, hmin⟩ := S.exists_min_image (fun x => (e x).im) hS
  let a : ↥S := ⟨p, hp⟩
  have ha_deg : G.degree a ≤ 4 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply OMA.unit_distance_sector_bound (G.neighborFinset a) (u a) 4 (hnorm a) (hrad_sep a)
    intro b _
    have him : 0 ≤ (u a b).im := by
      change 0 ≤ (e (b : ℝ²) - e p).im
      rw [Complex.sub_im]
      exact sub_nonneg.mpr (hmin b b.property)
    have harg := Complex.arg_nonneg_iff.mpr him
    unfold OMA.unit_distance_sector_coordinate
    apply (div_lt_iff₀ (by positivity : 0 < Real.pi / 3)).mpr
    linarith [Real.pi_pos]
  have hcount : unitDistNum S ≤ G.edgeFinset.card := by
    let lift : Sym2 (↥S) ↪ Sym2 ℝ² := (Function.Embedding.subtype fun x => x ∈ S).sym2Map
    rw [← Finset.card_map lift, unitDistNum]
    apply Finset.card_le_card
    intro d hd
    obtain ⟨hd_in, hd_unit⟩ := Finset.mem_filter.mp hd
    have hfst : d.out.1 ∈ S := (Finset.mem_sym2_iff.mp hd_in) _ (Sym2.out_fst_mem d)
    have hsnd : d.out.2 ∈ S := (Finset.mem_sym2_iff.mp hd_in) _ (Sym2.out_snd_mem d)
    let v : ↥S := ⟨d.out.1, hfst⟩
    let w : ↥S := ⟨d.out.2, hsnd⟩
    refine Finset.mem_map.mpr ⟨s(v, w), ?_, ?_⟩
    · apply SimpleGraph.mem_edgeFinset.mpr
      change G.Adj v w
      exact hd_unit
    · change s(d.out.1, d.out.2) = d
      exact Quot.out_eq d
  have hsum : (∑ v : ↥S, G.degree v) < ∑ _ : ↥S, (6 : ℕ) :=
    Finset.sum_lt_sum (fun v _ => hdeg v) ⟨a, Finset.mem_univ a, by omega⟩
  rw [G.sum_degrees_eq_twice_card_edges] at hsum
  have hsum_const : (∑ _ : ↥S, (6 : ℕ)) = 6 * S.card := by
    simp [mul_comm]
  rw [hsum_const] at hsum
  omega

theorem OMA.solution : type_of% @Erdos1084.erdos_1084.variants.easy_upper_d2 := by
  intro n hn
  apply lt_of_le_of_lt _ (show 3 * n - 1 < 3 * n by omega)
  unfold Erdos1084.f
  refine ciSup_le' (fun S => ciSup_le' (fun hS => ciSup_le' (fun hsep => ?_)))
  have hs_ne : S.Nonempty := Finset.card_pos.mp (by rw [hS]; omega)
  have hlt := OMA.unit_distance_card_lt S hs_ne hsep
  omega
