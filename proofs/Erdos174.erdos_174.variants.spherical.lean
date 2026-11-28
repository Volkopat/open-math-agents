import FormalConjectures.ErdosProblems.«174»

/-! A finite coloring excludes every congruent image of a noncospherical set. -/

open Finset

theorem OMA.solution : type_of% @Erdos174.erdos_174.variants.spherical := by
  classical
  intro n A ⟨hfin, hRam⟩
  by_contra hnot
  obtain ⟨a₀, ha₀⟩ : A.Nonempty := by_contra fun hn => hnot ⟨0, 0, by simp [Set.not_nonempty_iff_eq_empty.1 hn]⟩
  let E := EuclideanSpace ℝ (Fin n)
  let o : A := ⟨a₀, ha₀⟩
  let _ : Fintype A := hfin.fintype
  have ⟨w, hw, hs⟩ : ∃ w : A → ℝ, (∀ z : E, ∑ i, w i * inner ℝ ((i : E) - o) z = 0) ∧
      ∑ i, w i * ‖(i : E) - o‖ ^ 2 = 1 := by
    let T : E →ₗ[ℝ] (A → ℝ) := LinearMap.pi fun i => (2 : ℝ) • (innerSL ℝ ((i : E) - o)).toLinearMap
    let b : A → ℝ := fun i => ‖(i : E) - o‖ ^ 2
    have hTa (z : E) (i : A) : T z i = 2 * inner ℝ ((i : E) - o) z := by simp [T, smul_eq_mul, inner_sub_left]
    have hbr : b ∉ LinearMap.range T := by
      rintro ⟨z, hz⟩
      refine hnot ⟨(o : E) + z, ‖z‖, fun a ha => ?_⟩
      have hr := congrFun hz ⟨a, ha⟩
      rw [hTa] at hr
      change 2 * inner ℝ (a - (o : E)) z = ‖a - (o : E)‖ ^ 2 at hr
      rw [dist_eq_norm, show a - ((o : E) + z) = a - (o : E) - z by abel]
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by rw [norm_sub_sq_real]; linarith)
    obtain ⟨f, hres, hf⟩ := LinearMap.exists_extend_of_notMem (0 : LinearMap.range T →ₗ[ℝ] ℝ) hbr 1
    have hfs (x : A → ℝ) : f x = ∑ i, f (Pi.single i 1) * x i := by
      calc f x = f (∑ i, Pi.single i (x i)) := congrArg f (univ_sum_single x).symm
        _ = ∑ i, f (Pi.single i 1) * x i := by
          rw [map_sum]; refine sum_congr rfl fun i _ => ?_
          rw [show Pi.single i (x i) = x i • Pi.single i (1 : ℝ) by funext j; by_cases h : j = i <;> simp [h],
            map_smul, smul_eq_mul, mul_comm]
    refine ⟨fun i => f (Pi.single i 1), fun z => ?_, (hfs b).symm.trans hf⟩
    have h0 : f (T z) = 0 := by simpa using congrArg (fun g : LinearMap.range T →ₗ[ℝ] ℝ => g ⟨T z, ⟨z, rfl⟩⟩) hres
    have h1 := (hfs (T z)).symm.trans h0
    simp_rw [hTa] at h1
    have h2 : ∑ i, f (Pi.single i 1) * (2 * inner ℝ ((i : E) - o) z) =
        2 * ∑ i, f (Pi.single i 1) * inner ℝ ((i : E) - o) z := by rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
    linarith
  let m : ℕ := 2 * Fintype.card A + 1
  have hm : 0 < m := by positivity
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  let bin (t : ℝ) : Fin m := ⟨Nat.floor ((m : ℝ) * Int.fract t),
    (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg m) (Int.fract_nonneg t))).2
      (by simpa using mul_lt_mul_of_pos_left (Int.fract_lt_one t) hmr)⟩
  let e := Fintype.equivFin (A → Fin m)
  obtain ⟨d, hd⟩ := hRam (Fintype.card (A → Fin m))
    (by let _ : Nonempty (A → Fin m) := ⟨fun _ => ⟨0, hm⟩⟩; exact Fintype.card_pos)
  let F (i : A) (x : EuclideanSpace ℝ (Fin d)) := w i * ‖x‖ ^ 2 / 2
  obtain ⟨p, hp, _, hc⟩ := hd fun x => e (fun i => bin (F i x))
  have hsum : ∑ i, (F i (p i) - F i (p o)) = 1 / 2 := by
    let v (i : A) := p i - p o
    let vS : EuclideanSpace ℝ (Fin d) := ∑ i, w i • v i
    have hv (j : A) : inner ℝ vS (v j) = 0 := by
      simp only [vS, sum_inner, real_inner_smul_left, v]
      have hanc (i : A) : inner ℝ (p i - p o) (p j - p o) = inner ℝ ((i : E) - o) ((j : E) - o) := by
        have hi := hp.dist_eq i o; have hj := hp.dist_eq j o; have hij := hp.dist_eq i j
        simp only [dist_eq_norm] at hi hj hij
        have ha := norm_sub_sq_real ((i : E) - o) ((j : E) - o)
        have hpp := norm_sub_sq_real (p i - p o) (p j - p o)
        rw [show ((i : E) - o) - ((j : E) - o) = (i : E) - j by abel, hi, hj, hij] at ha
        rw [show (p i - p o) - (p j - p o) = p i - p j by abel] at hpp; linarith
      simp_rw [hanc]; exact hw ((j : E) - o)
    have h0 : vS = 0 := (@inner_self_eq_zero ℝ _ _ _ _).1
      (by change inner ℝ vS (∑ i, w i • v i) = 0; simp [inner_sum, real_inner_smul_right, hv])
    have horth : ∑ i, w i * inner ℝ (v i) (p o) = 0 := by
      simpa only [vS, sum_inner, real_inner_smul_left, inner_zero_left] using congrArg (inner ℝ · (p o)) h0
    have htr : ∑ i, w i * (‖p i‖ ^ 2 - ‖p o‖ ^ 2) = 1 := by
      have hsh (i : A) : ‖p i‖ ^ 2 - ‖p o‖ ^ 2 = ‖v i‖ ^ 2 + 2 * inner ℝ (v i) (p o) := by
        have := norm_add_sq_real (v i) (p o); rw [show v i + p o = p i by simp [v]] at this; linarith
      have hn (i : A) : ‖v i‖ = ‖(i : E) - o‖ := by simpa only [v, dist_eq_norm] using (hp.dist_eq i o).symm
      calc ∑ i, w i * (‖p i‖ ^ 2 - ‖p o‖ ^ 2) = (∑ i, w i * ‖v i‖ ^ 2) + 2 * ∑ i, w i * inner ℝ (v i) (p o) := by
            simp_rw [hsh, mul_add, sum_add_distrib, mul_sum]; congr 1; exact sum_congr rfl fun _ _ => by ring
        _ = 1 := by simpa [hn, horth] using hs
    calc ∑ i, (F i (p i) - F i (p o)) = (∑ i, w i * (‖p i‖ ^ 2 - ‖p o‖ ^ 2)) / 2 := by
          rw [sum_div]; exact sum_congr rfl fun _ _ => by dsimp [F]; ring
      _ = 1 / 2 := by rw [htr]
  have hfb (i : A) : |Int.fract (F i (p i)) - Int.fract (F i (p o))| ≤ 1 / (m : ℝ) := by
    have he : Nat.floor ((m : ℝ) * Int.fract (F i (p i))) = Nat.floor ((m : ℝ) * Int.fract (F i (p o))) :=
      congrArg Fin.val (congrFun (e.injective ((hc i).trans (hc o).symm)) i)
    have h1 := Nat.floor_le (mul_nonneg (Nat.cast_nonneg m) (Int.fract_nonneg (F i (p i))))
    have h2 := Nat.lt_floor_add_one ((m : ℝ) * Int.fract (F i (p i)))
    have h3 := Nat.floor_le (mul_nonneg (Nat.cast_nonneg m) (Int.fract_nonneg (F i (p o))))
    have h4 := Nat.lt_floor_add_one ((m : ℝ) * Int.fract (F i (p o)))
    rw [he] at h1 h2; rw [abs_le, ← neg_div, div_le_iff₀ hmr, le_div_iff₀ hmr]; exact ⟨by linarith, by linarith⟩
  have hbd : |∑ i, (Int.fract (F i (p i)) - Int.fract (F i (p o)))| < 1 / 2 := by
    calc _ ≤ ∑ i, |Int.fract (F i (p i)) - Int.fract (F i (p o))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : A, (1 / (m : ℝ)) := sum_le_sum fun i _ => hfb i
      _ < 1 / 2 := by rw [sum_const, card_univ, nsmul_eq_mul, mul_one_div, div_lt_iff₀ hmr]; push_cast [m]; linarith
  let z : ℤ := ∑ i, (Int.floor (F i (p i)) - Int.floor (F i (p o)))
  have hz : ∑ i, (Int.fract (F i (p i)) - Int.fract (F i (p o))) = 1 / 2 - z := by
    rw [← hsum]; simp only [z, Int.cast_sum, Int.cast_sub, ← sum_sub_distrib]
    exact sum_congr rfl fun _ _ => by unfold Int.fract; ring
  rw [hz, abs_lt] at hbd
  have : (0 : ℤ) < z := by exact_mod_cast (show (0 : ℝ) < z by linarith)
  have : z < 1 := by exact_mod_cast (show (z : ℝ) < 1 by linarith)
  omega
