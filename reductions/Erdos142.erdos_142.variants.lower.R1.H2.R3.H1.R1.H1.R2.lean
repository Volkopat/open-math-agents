import OMAReductions.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1

-- Credit: @yuka30240

/-!
# From monochromatic progressions to a cyclic progression count

Join the first two terms of every nonconstant progression in `A` by an edge.
If there are at most `p` progressions, the independent-set bound gives a
progression-free subset of density at least one third of the square of the
original density. Random translates of this subset cover the whole group.
Coloring each point by a covering translate now contradicts the multicolor
van der Waerden bound on the interval of length `p`.
-/

namespace OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R2

open Finset Filter Real

/-- The independent-set bound for a finite graph given by its oriented edges.
Duplicating an edge in the opposite orientation only weakens the bound. -/
def H1 : Prop :=
  ∀ (V : Type) (A : Finset V) (E : Finset (V × V)),
    (∀ e ∈ E, e.1 ≠ e.2) →
    ∃ B ⊆ A, A.card ^ 2 ≤ (A.card + 2 * E.card) * B.card ∧
      ∀ e ∈ E, e.1 ∈ B → e.2 ∉ B

/-- A quasipolynomial upper bound on the multicolor van der Waerden number.
For fixed length, a polynomial in `2 + log r` bounds the logarithm of a
sufficient interval length, as in the coloring-threshold bound in section 1
of OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions* (September 2026). -/
def H2 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∃ (K : ℝ) (D : ℕ), 1 ≤ K ∧ 0 < D ∧
    ∀ N r : ℕ, 0 < r → K * (2 + log (r : ℝ)) ^ D ≤ log (N : ℝ) →
      ∀ color : ℕ → Fin r, ∃ a d : ℕ, 0 < d ∧ a + (k - 1) * d < N ∧
        ∀ i : Fin k, color (a + i.val * d) = color a

/-- Invert the color bound while retaining a constant in the exponential
for the independent-set and covering losses. -/
lemma colors_at_scale (mono : H2) {k : ℕ} (hk : 4 ≤ k) :
    ∃ b η : ℝ, 0 < b ∧ 0 < η ∧ ∀ᶠ N : ℕ in atTop,
      ∀ r : ℕ, (r : ℝ) ≤ exp (b * log (N : ℝ) ^ η) → ∀ color : ℕ → Fin r,
        ∃ a d : ℕ, 0 < d ∧ a + (k - 1) * d < N ∧
          ∀ i : Fin k, color (a + i.val * d) = color a := by
  obtain ⟨K, D, hK, hD, force⟩ := mono k hk
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  let η := (D : ℝ)⁻¹
  have hη : 0 < η := by dsimp [η]; positivity
  have hX := (tendsto_rpow_atTop hη).comp
    (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  refine ⟨1 / (2 * K), η, by positivity, hη, ?_⟩
  filter_upwards [hX.eventually_ge_atTop (4 * K), eventually_ge_atTop (1 : ℕ)] with N hlarge hN
  intro r hr color
  have hrpos : 0 < r := (color 0).pos
  have hlr : 0 ≤ log (r : ℝ) := log_nonneg (by exact_mod_cast hrpos)
  have hlN : 0 ≤ log (N : ℝ) := log_nonneg (by exact_mod_cast hN)
  let X := log (N : ℝ) ^ η
  change 4 * K ≤ X at hlarge
  have hlogr := (log_le_log (by exact_mod_cast hrpos) hr).trans_eq (log_exp _)
  change log (r : ℝ) ≤ 1 / (2 * K) * X at hlogr
  have hbase : 2 + log (r : ℝ) ≤ X / K := by
    apply (le_div_iff₀ hKpos).mpr
    have hbudget : log (r : ℝ) * (2 * K) ≤ X := by
      apply (le_div_iff₀ (show 0 < 2 * K by positivity)).mp
      simpa [div_eq_mul_inv, mul_comm] using hlogr
    linarith only [hlarge, hbudget]
  apply force N r hrpos _ color
  calc
    K * (2 + log (r : ℝ)) ^ D ≤ K ^ D * (X / K) ^ D := by
      gcongr
      exact le_self_pow₀ hK hD.ne'
    _ = X ^ D := by rw [← mul_pow]; field_simp
    _ = log (N : ℝ) := Real.rpow_inv_natCast_pow hlN hD.ne'

/-- The bad `r`-tuples for each uncovered point have exactly `(p - |B|)^r` elements. -/
private lemma cover_of_count {p r : ℕ} [NeZero p] (B : Finset (ZMod p))
    (h : p * (p - B.card) ^ r < p ^ r) :
    ∃ shifts : Fin r → ZMod p, ∀ x, ∃ j, x + shifts j ∈ B := by
  classical
  let missing (x : ZMod p) := Bᶜ.map (Equiv.addLeft x).symm.toEmbedding
  let bad (x : ZMod p) := Fintype.piFinset (fun _ : Fin r => missing x)
  have card_bad (x : ZMod p) : (bad x).card = (p - B.card) ^ r := by
    simp [bad, missing, Fintype.card_piFinset, card_compl, ZMod.card]
  have smaller : (univ.biUnion bad).card < (univ : Finset (Fin r → ZMod p)).card := by
    apply lt_of_le_of_lt card_biUnion_le
    simpa [card_bad, Fintype.card_fun, ZMod.card] using h
  obtain ⟨shifts, _, hshifts⟩ := exists_mem_notMem_of_card_lt_card smaller
  refine ⟨shifts, fun x => ?_⟩
  by_contra! hmiss
  apply hshifts
  refine mem_biUnion.mpr ⟨x, mem_univ _, Fintype.mem_piFinset.mpr (fun j => ?_)⟩
  simpa [missing, mem_map_equiv] using hmiss j

/-- Independent random shifts cover every point once `r` exceeds the usual
logarithmic covering threshold. -/
private lemma translate_cover {p : ℕ} [NeZero p] (B : Finset (ZMod p)) (hB : 0 < B.card) :
    ∃ (r : ℕ) (shifts : Fin r → ZMod p),
      (r : ℝ) ≤ (p : ℝ) / B.card * (2 + log (p : ℝ)) ∧
      ∀ x, ∃ j, x + shifts j ∈ B := by
  have hp : (0 : ℝ) < p := by exact_mod_cast NeZero.pos p
  have hb : (0 : ℝ) < B.card := by exact_mod_cast hB
  have hle : B.card ≤ p := by simpa [ZMod.card] using B.card_le_univ
  have hratio : (1 : ℝ) ≤ p / (B.card : ℝ) := (one_le_div hb).mpr (by exact_mod_cast hle)
  have hlog : 0 ≤ log (p : ℝ) := log_nonneg (by exact_mod_cast NeZero.one_le)
  let r := ⌈(p : ℝ) / B.card * (1 + log (p : ℝ))⌉₊
  have hcard : (p : ℝ) / B.card * (1 + log (p : ℝ)) ≤ r := Nat.le_ceil _
  have hforecast : 1 + log (p : ℝ) ≤ (r : ℝ) * (B.card / (p : ℝ)) := by
    calc
      _ = ((p : ℝ) / B.card * (1 + log (p : ℝ))) * (B.card / (p : ℝ)) := by field_simp
      _ ≤ _ := by gcongr
  have hprob : ((p - B.card : ℕ) : ℝ) / p ≤ exp (-(B.card / (p : ℝ))) := by
    rw [Nat.cast_sub hle, sub_div, div_self hp.ne']
    linarith [Real.add_one_le_exp (-(B.card / (p : ℝ)))]
  have hmiss : (p : ℝ) * (((p - B.card : ℕ) : ℝ) / p) ^ r < 1 := by
    calc
      _ ≤ (p : ℝ) * exp (-(B.card / (p : ℝ))) ^ r := by gcongr
      _ < (p : ℝ) * exp (-log (p : ℝ)) := by
        apply mul_lt_mul_of_pos_left _ hp
        rw [← exp_nat_mul, exp_lt_exp, mul_neg]
        linarith only [hforecast]
      _ = 1 := by rw [exp_neg, exp_log hp, mul_inv_cancel₀ hp.ne']
  rw [div_pow, ← mul_div_assoc] at hmiss
  have hcount : p * (p - B.card) ^ r < p ^ r := by
    exact_mod_cast (div_lt_one (pow_pos hp r)).mp hmiss
  obtain ⟨shifts, hshifts⟩ := cover_of_count B hcount
  refine ⟨r, shifts, ?_, hshifts⟩
  have hr : (r : ℝ) < (p : ℝ) / B.card * (1 + log (p : ℝ)) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  linarith only [hr, hratio]

private lemma absorb_log {b η : ℝ} (hb : 0 < b) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, 3 * (2 + log (N : ℝ)) ≤ exp (b / 2 * log (N : ℝ) ^ η) := by
  have hlog : Tendsto (fun n : ℕ => log (n : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := (isLittleO_log_rpow_atTop hη).bound (show 0 < b / 4 by positivity)
  filter_upwards [hlog.eventually hsmall, hlog.eventually_ge_atTop 8] with n hsmall hn
  let x := log (n : ℝ)
  change (8 : ℝ) ≤ x at hn
  change ‖log x‖ ≤ b / 4 * ‖x ^ η‖ at hsmall
  rw [Real.norm_eq_abs, abs_of_nonneg (log_nonneg (by linarith)), Real.norm_eq_abs,
    abs_of_nonneg (rpow_nonneg (by linarith) _)] at hsmall
  calc
    3 * (2 + x) ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 4)]
    _ = exp (2 * log x) := by rw [show (2 : ℝ) = (2 : ℕ) by norm_num, exp_nat_mul,
                                    exp_log (by linarith)]
    _ ≤ exp (b / 2 * x ^ η) := exp_le_exp.mpr (by linarith only [hsmall])

/-- An independent set in the graph of initial pairs contains no nonconstant
progression. The bound counts ordered progressions, so opposite orientations
and coincident image edges cause no loss. -/
private lemma sparse_subset (independent : H1) {k p : ℕ} (hk : 2 ≤ k) [NeZero p]
    (A : Finset (ZMod p))
    (few : (univ.filter fun u : ZMod p × ZMod p =>
      ∀ i : Fin k, u.1 + (i.val : ZMod p) * u.2 ∈ A).card ≤ p) :
    ∃ B : Finset (ZMod p), A.card ^ 2 ≤ 3 * p * B.card ∧
      ∀ a d : ZMod p, (∀ i : Fin k, a + (i.val : ZMod p) * d ∈ B) → d = 0 := by
  classical
  let P := univ.filter fun u : ZMod p × ZMod p =>
    ∀ i : Fin k, u.1 + (i.val : ZMod p) * u.2 ∈ A
  let E := (P.filter fun u => u.2 ≠ 0).image (fun u => (u.1, u.1 + u.2))
  have loopless (e) (he : e ∈ E) : e.1 ≠ e.2 := by
    obtain ⟨u, hu, rfl⟩ := mem_image.mp he
    simpa using (mem_filter.mp hu).2
  obtain ⟨B, hBA, hsize, hind⟩ := independent (ZMod p) A E loopless
  have hedge : E.card ≤ p := card_image_le.trans ((card_filter_le _ _).trans few)
  have hA : A.card ≤ p := by simpa [ZMod.card] using A.card_le_univ
  refine ⟨B, hsize.trans (Nat.mul_le_mul_right _ (by omega)), ?_⟩
  intro a d hmem
  by_contra hd
  have hpair : (a, d) ∈ P := mem_filter.mpr ⟨mem_univ _, fun i => hBA (hmem i)⟩
  have he : (a, a + d) ∈ E := mem_image.mpr ⟨(a, d), mem_filter.mpr ⟨hpair, hd⟩, rfl⟩
  have hfirst : a ∈ B := by simpa using hmem ⟨0, by omega⟩
  have hsecond : a + d ∈ B := by simpa using hmem ⟨1, by omega⟩
  exact hind _ he hfirst hsecond

/-- If `B` has density at least a third of the squared density of `A`, the
inverse density of `B` costs at most twice the exponential loss of `A`. -/
private lemma inverse_density {n m p e : ℝ} (hp : 0 < p) (hm : 0 < m)
    (hn : p ≤ n * e) (hsize : n ^ 2 ≤ 3 * p * m) : p / m ≤ 3 * e ^ 2 := by
  apply (div_le_iff₀ hm).mpr
  have hsq : p ^ 2 ≤ 3 * e ^ 2 * m * p := calc
    p ^ 2 ≤ (n * e) ^ 2 := pow_le_pow_left₀ hp.le hn _
    _ = n ^ 2 * e ^ 2 := mul_pow _ _ _
    _ ≤ (3 * p * m) * e ^ 2 := by gcongr
    _ = _ := by ring
  by_contra! h
  have := mul_lt_mul_of_pos_right h hp
  linarith only [hsq, this]

theorem main : H1 → H2 → OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1.H1 := by
  classical
  intro independent monochromatic k hk
  obtain ⟨b, η, hb, hη, hcolors⟩ := colors_at_scale monochromatic hk
  obtain ⟨P, htail⟩ := eventually_atTop.mp (hcolors.and (absorb_log hb hη))
  let c := b / 4
  have hc : 0 < c := by dsimp [c]; positivity
  let M := max 2 P
  have hM : 2 ≤ M := le_max_left _ _
  let C := exp (c * log (M : ℝ) ^ η)
  have hlogM : 0 ≤ log (M : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ M by omega))
  have hC : 1 ≤ C := Real.one_le_exp (by positivity)
  refine ⟨C, c, η, exp_pos _, hc, hη, ?_⟩
  intro p hp
  let : NeZero p := ⟨hp.ne_zero⟩
  intro A hA
  let X := log (p : ℝ) ^ η
  change C * (p : ℝ) * exp (-c * X) < A.card at hA
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : 0 ≤ log (p : ℝ) := log_nonneg (by exact_mod_cast hp.one_le)
  have hlarge : P ≤ p := by
    by_contra! hsmall
    have hpM : p ≤ M := hsmall.le.trans (le_max_right _ _)
    have hXM : X ≤ log (M : ℝ) ^ η :=
      rpow_le_rpow hlog (log_le_log hp' (by exact_mod_cast hpM)) hη.le
    have hfactor : 1 ≤ C * exp (-c * X) := by
      dsimp [C]
      rw [← exp_add]
      apply Real.one_le_exp
      linarith only [mul_le_mul_of_nonneg_left hXM hc.le]
    have hcap : (A.card : ℝ) ≤ p := by
      exact_mod_cast (show A.card ≤ p by simpa [ZMod.card] using A.card_le_univ)
    linarith only [hA, hcap, mul_le_mul_of_nonneg_right hfactor hp'.le]
  obtain ⟨force, hover⟩ := htail p hlarge
  change 3 * (2 + log (p : ℝ)) ≤ exp (b / 2 * X) at hover
  have hscaled : (p : ℝ) * exp (-c * X) < A.card := by
    calc
      _ ≤ C * p * exp (-c * X) := by gcongr; simpa using mul_le_mul_of_nonneg_right hC hp'.le
      _ < _ := hA
  rw [neg_mul, exp_neg, ← div_eq_mul_inv, div_lt_iff₀ (exp_pos _)] at hscaled
  by_contra! few
  obtain ⟨B, hsize, hfree⟩ := sparse_subset independent (by omega : 2 ≤ k) A few
  have hn : 0 < A.card := by
    by_contra! hzero
    simp [Nat.eq_zero_of_le_zero hzero] at hscaled
    linarith
  have hm : 0 < B.card := by
    by_contra! hzero
    simp [Nat.eq_zero_of_le_zero hzero, hn.ne'] at hsize
  have hratio : (p : ℝ) / B.card ≤ 3 * exp (c * X) ^ 2 :=
    inverse_density hp' (by exact_mod_cast hm) hscaled.le (by exact_mod_cast hsize)
  obtain ⟨r, shifts, hr, cover⟩ := translate_cover B hm
  have hlimit : (r : ℝ) ≤ exp (b * X) := calc
    _ ≤ (p : ℝ) / B.card * (2 + log (p : ℝ)) := hr
    _ ≤ (3 * exp (c * X) ^ 2) * (2 + log (p : ℝ)) := by gcongr
    _ = (3 * (2 + log (p : ℝ))) * exp (c * X) ^ 2 := by ring
    _ ≤ exp (b / 2 * X) * exp (c * X) ^ 2 := by gcongr
    _ = exp (b * X) := by rw [sq, ← exp_add, ← exp_add]; congr 1; dsimp [c]; ring
  choose color hcover using fun n : ℕ => cover (n : ZMod p)
  obtain ⟨a, d, hd, hend, hmono⟩ := force r hlimit color
  have hdp : d < p := by
    have := Nat.le_mul_of_pos_left d (show 0 < k - 1 by omega)
    omega
  have hmem (i : Fin k) : (a + shifts (color a)) + (i.val : ZMod p) * d ∈ B := by
    have hi := hcover (a + i.val * d)
    rw [hmono i] at hi
    simpa [Nat.cast_add, Nat.cast_mul, add_right_comm] using hi
  have hd0 := hfree _ _ hmem
  exact (Nat.le_of_dvd hd ((ZMod.natCast_eq_zero_iff d p).mp hd0)).not_gt hdp

end OMA.R_Erdos142_erdos_142_variants_lower_R1_H2_R3_H1_R1_H1_R2
