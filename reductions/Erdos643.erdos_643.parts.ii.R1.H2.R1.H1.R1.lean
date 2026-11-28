import OMAReductions.R_Erdos643_erdos_643_parts_ii_R1_H2_R1

/-!
# Erdős 643: reduction of the asymptotic stability hypothesis

Local starification, alignment of the local centers, and the star-deficit
bound imply stability at the full-star size threshold. The proof takes the
error tolerance to be the reciprocal of the claimed integral multiplier.
See Huang, Ma, and Yang, arXiv:2609.37744, Sections 2–3.

Credit: @justusklocke-cloud
-/

namespace OMA.R_Erdos643_erdos_643_parts_ii_R1_H2_R1_H1_R1

open Filter
open scoped Topology

private theorem power_le_binomial_multiple {n k : ℕ} (hn : 0 < n) (hlarge : 2 * k ≤ n) :
    (n : ℝ) ^ k ≤ (2 : ℝ) ^ k * (k.factorial : ℝ) * (((n - 1).choose k : ℕ) : ℝ) := by
  have hbase : n ≤ 2 * (n - k) := by omega
  have hpow : (n - k) ^ k ≤ (n - 1).descFactorial k := by
    simpa only [Nat.sub_add_cancel (show 1 ≤ n by omega)] using
      (n - 1).pow_sub_le_descFactorial k
  have hnat : n ^ k ≤ 2 ^ k * k.factorial * (n - 1).choose k := by
    calc
      n ^ k ≤ (2 * (n - k)) ^ k := Nat.pow_le_pow_left hbase k
      _ = 2 ^ k * (n - k) ^ k := mul_pow _ _ _
      _ ≤ 2 ^ k * (n - 1).descFactorial k := Nat.mul_le_mul_left _ hpow
      _ = _ := by rw [Nat.descFactorial_eq_factorial_mul_choose, mul_assoc]
  exact_mod_cast hnat

/-- A single small density coefficient controls the exceptional set, the
density loss and the logarithmic comparison for all large natural orders. -/
private theorem stability_scales {t : ℕ} (ht : 4 ≤ t) {δ K : ℝ} (hδ : 0 < δ) (hK : 0 < K) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ {ε u m : ℝ}, ε ≤ ε₀ → 0 ≤ u → u ≤ ε * (n : ℝ) →
        let S : ℝ := ((n - 1).choose (t - 1) : ℕ)
        δ * S < m →
        u ≤ (n : ℝ) / (50 * (t : ℝ) ^ (4 * t + 3)) ∧
        K * u ^ (t - 1) ≤ m ∧ ε * S ≤ m / (2 * (t : ℝ)) ∧
        (n : ℝ) * Real.log n < m := by
  let k := t - 1
  let D : ℝ := (2 : ℝ) ^ k * (k.factorial : ℝ)
  let A : ℝ := 50 * (t : ℝ) ^ (4 * t + 3)
  let B : ℝ := 2 * (t : ℝ)
  let ε₀ : ℝ := min 1 (min (1 / A) (min (δ / B) (δ / (K * D))))
  have htreal : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hD : 0 < D := by dsimp [D]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hε₀ : 0 < ε₀ := by
    exact lt_min (by norm_num) (lt_min (one_div_pos.mpr hA)
      (lt_min (div_pos hδ hB) (div_pos hδ (mul_pos hK hD))))
  have hεone : ε₀ ≤ 1 := min_le_left _ _
  have hεA : ε₀ ≤ 1 / A := (min_le_right _ _).trans (min_le_left _ _)
  have hεinner : ε₀ ≤ min (δ / B) (δ / (K * D)) := (min_le_right _ _).trans (min_le_right _ _)
  have hεB : ε₀ ≤ δ / B := hεinner.trans (min_le_left _ _)
  have hεKD : ε₀ ≤ δ / (K * D) := hεinner.trans (min_le_right _ _)
  have hk : 2 ≤ k := by dsimp [k]; omega
  have hεpow : ε₀ ^ k ≤ ε₀ := pow_le_of_le_one hε₀.le hεone (by omega)
  have hlim : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa only [mul_one, one_mul, add_zero, pow_one] using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
  have hlog : ∀ᶠ n : ℕ in atTop, Real.log n / (n : ℝ) < δ / D :=
    (hlim.comp tendsto_natCast_atTop_atTop).eventually (Iio_mem_nhds (div_pos hδ hD))
  refine ⟨ε₀, hε₀, ?_⟩
  filter_upwards [eventually_ge_atTop (2 * k), hlog] with n hnlarge hnlog
  intro ε u m hε hu hUn
  let S : ℝ := (((n - 1).choose k : ℕ) : ℝ)
  change δ * S < m → u ≤ (n : ℝ) / A ∧
    K * u ^ k ≤ m ∧ ε * S ≤ m / B ∧ (n : ℝ) * Real.log n < m
  intro hdeficit
  have hn : 0 < n := by omega
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hnreal
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hUn' : u ≤ ε₀ * (n : ℝ) := hUn.trans (mul_le_mul_of_nonneg_right hε hnpos.le)
  have hpow := power_le_binomial_multiple hn hnlarge
  change (n : ℝ) ^ k ≤ D * S at hpow
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      u ≤ ε₀ * (n : ℝ) := hUn'
      _ ≤ (1 / A) * (n : ℝ) := mul_le_mul_of_nonneg_right hεA hnpos.le
      _ = (n : ℝ) / A := by ring
  · calc
      K * u ^ k ≤ K * (ε₀ * (n : ℝ)) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu hUn' _) hK.le
      _ = (K * ε₀ ^ k) * (n : ℝ) ^ k := by rw [mul_pow, mul_assoc]
      _ ≤ (K * ε₀) * (n : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hεpow hK.le) (by positivity)
      _ ≤ (K * ε₀) * (D * S) := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (ε₀ * (K * D)) * S := by ring
      _ ≤ δ * S :=
        mul_le_mul_of_nonneg_right ((le_div_iff₀ (mul_pos hK hD)).mp hεKD) hS
      _ ≤ m := hdeficit.le
  · apply (le_div_iff₀ hB).mpr
    calc
      (ε * S) * B ≤ (ε₀ * S) * B :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hε hS) hB.le
      _ = (ε₀ * B) * S := by ring
      _ ≤ δ * S := mul_le_mul_of_nonneg_right ((le_div_iff₀ hB).mp hεB) hS
      _ ≤ m := hdeficit.le
  · have hlogn := (div_lt_iff₀ hnpos).mp hnlog
    calc
      (n : ℝ) * Real.log n < (n : ℝ) * ((δ / D) * (n : ℝ)) :=
        mul_lt_mul_of_pos_left hlogn hnpos
      _ = (δ / D) * (n : ℝ) ^ 2 := by ring
      _ ≤ (δ / D) * (n : ℝ) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hnreal hk) (div_nonneg hδ.le hD.le)
      _ ≤ (δ / D) * (D * S) := mul_le_mul_of_nonneg_left hpow (div_nonneg hδ.le hD.le)
      _ = δ * S := by field_simp
      _ < m := hdeficit


/-- Outside the exceptional set, an off-star link has at most one completion. -/
private theorem outside_neighbors_card_le_one {V : Type*} [Fintype V] [DecidableEq V]
    {G : Finset (Finset V)} {W : Finset V}
    {v : V} {t : ℕ}
    (halign : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → ∀ S : Finset V, S.card = t - 1 →
      x ∉ S → y ∉ S → insert x S ∈ G → insert y S ∈ G → v ∈ S) :
    let U := Finset.univ.erase v \ W
    let H := G.filter (fun E => v ∉ E)
    ∀ S : Finset V, S.card = t - 1 →
      ((Finset.univ.filter (fun x => x ∉ S ∧ insert x S ∈ H)) \ U).card ≤ 1 := by
  intro U H S hS
  let neighbors := (Finset.univ.filter (fun x => x ∉ S ∧ insert x S ∈ H)) \ U
  change neighbors.card ≤ 1
  have hmem {x} (hx : x ∈ neighbors) : x ∈ W ∧ x ∉ S ∧ insert x S ∈ G ∧ v ∉ S := by
    obtain ⟨hfilter, hxU⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨_, hxS, hxH⟩ := Finset.mem_filter.mp hfilter
    obtain ⟨hxG, hv⟩ := Finset.mem_filter.mp hxH
    have hxv : x ≠ v := by
      rintro rfl
      exact hv (Finset.mem_insert_self _ _)
    have hxW : x ∈ W := by
      by_contra hxnot
      exact hxU (Finset.mem_sdiff.mpr
        ⟨Finset.mem_erase.mpr ⟨hxv, Finset.mem_univ _⟩, hxnot⟩)
    exact ⟨hxW, hxS, hxG, fun hs => hv (Finset.mem_insert_of_mem hs)⟩
  apply Finset.card_le_one.mpr
  intro x hx y hy
  by_contra hne
  obtain ⟨hxW, hxS, hxG, hvS⟩ := hmem hx
  obtain ⟨hyW, hyS, hyG, _⟩ := hmem hy
  exact hvS (halign x hxW y hyW hne S hS hxS hyS hxG hyG)

/-- The exceptional set omits every vertex in `W`, regardless of whether `v` lies in `W`. -/
private theorem exceptional_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (v : V) (W : Finset V) :
    (Finset.univ.erase v \ W).card ≤ Fintype.card V - W.card := by
  rw [← Finset.card_univ, ← Finset.card_sdiff_of_subset (Finset.subset_univ W)]
  exact Finset.card_le_card
    (Finset.sdiff_subset_sdiff_left W (Finset.erase_subset v Finset.univ))


private theorem degree_le_star {n t : ℕ} {F : Finset (Finset (Fin n))}
    (ht : 1 ≤ t) (hF : F.IsUniform t) (v : Fin n) :
    (F.filter (fun e => v ∈ e)).card ≤ (n - 1).choose (t - 1) := by
  calc
    (F.filter (fun e => v ∈ e)).card ≤
        (((Finset.univ : Finset (Fin n)).powersetCard t).filter
          (fun e => {v} ⊆ e)).card := by
      apply Finset.card_le_card
      intro e he
      obtain ⟨he, hv⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hF e he⟩,
          Finset.singleton_subset_iff.mpr hv⟩
    _ = (n - 1).choose (t - 1) := by
      simpa using Finset.card_filter_powersetCard_subset
        ({v} : Finset (Fin n)) Finset.univ t (Finset.subset_univ _) (by simpa using ht)

private theorem missing_card {n t : ℕ} {F : Finset (Finset (Fin n))} (v : Fin n)
    (hF : F.IsUniform t) :
    (((Finset.univ.erase v).powersetCard (t - 1)).filter
      fun E => insert v E ∉ F).card =
      (n - 1).choose (t - 1) - (F.filter fun E => v ∈ E).card := by
  let L := (Finset.univ.erase v).powersetCard (t - 1)
  have hlcard : L.card = (n - 1).choose (t - 1) := by
    simp [L, Finset.card_erase_of_mem (Finset.mem_univ v)]
  have hpresent : (L.filter (fun E => insert v E ∈ F)).card =
      (F.filter (fun E => v ∈ E)).card := by
    apply Finset.card_nbij' (insert v) (fun E => E.erase v)
    · intro E hE
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hE).2, Finset.mem_insert_self _ _⟩
    · intro E hE
      obtain ⟨hEF, hv⟩ := Finset.mem_filter.mp hE
      refine Finset.mem_filter.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, by simpa [Finset.insert_erase hv] using hEF⟩
      · intro x hx
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, Finset.mem_univ _⟩
      · rw [Finset.card_erase_of_mem hv, hF E hEF]
    · intro E hE
      have hs := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hE).1).1
      apply Finset.erase_insert
      intro hv
      exact (Finset.mem_erase.mp (hs hv)).1 rfl
    · intro E hE
      exact Finset.insert_erase (Finset.mem_filter.mp hE).2
  have hsplit := Finset.card_filter_add_card_filter_not (s := L) (fun E => insert v E ∈ F)
  rw [hpresent, hlcard] at hsplit
  change (L.filter (fun E => insert v E ∉ F)).card = _
  omega

/-- Local starification after deleting a small fraction of the edges. -/
def H1 : Prop :=
  ∀ t : ℕ, 4 ≤ t → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
    ∀ F : Finset (Finset (Fin n)), F.IsUniform t → ¬ F.HasRepeatedDisjointUnion →
      (n - 1).choose (t - 1) ≤ F.card →
      ∃ G : Finset (Finset (Fin n)), G ⊆ F ∧ G.IsUniform t ∧
        ¬ G.HasRepeatedDisjointUnion ∧
        (1 - ε) * (((n - 1).choose (t - 1) : ℕ) : ℝ) ≤ (G.card : ℝ) ∧
        (∀ x y : Fin n, x ≠ y → ∃ v : Fin n, ∀ S : Finset (Fin n),
          S.card = t - 1 → x ∉ S → y ∉ S → insert x S ∈ G → insert y S ∈ G → v ∈ S)

/-- At high density, most pairs of vertices can share one center. -/
def H2 : Prop :=
  ∀ t : ℕ, 4 ≤ t → ∀ γ : ℝ, 0 < γ → ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in atTop,
    ∀ G : Finset (Finset (Fin n)), G.IsUniform t → ¬ G.HasRepeatedDisjointUnion →
      (1 - ε) * (((n - 1).choose (t - 1) : ℕ) : ℝ) ≤ (G.card : ℝ) →
      (∀ x y : Fin n, x ≠ y → ∃ v : Fin n, ∀ S : Finset (Fin n),
        S.card = t - 1 → x ∉ S → y ∉ S → insert x S ∈ G → insert y S ∈ G → v ∈ S) →
      ∃ (v : Fin n) (W : Finset (Fin n)), (n : ℝ) - (W.card : ℝ) ≤ γ * (n : ℝ) ∧
        (∀ x ∈ W, ∀ y ∈ W, x ≠ y → ∀ S : Finset (Fin n), S.card = t - 1 →
          x ∉ S → y ∉ S → insert x S ∈ G → insert y S ∈ G → v ∈ S)

/-- The star deficit is logarithmic under the alignment and density bounds. -/
def H3 : Prop :=
  ∃ K : ℕ → ℕ, (∀ t : ℕ, 4 ≤ t → 0 < K t) ∧
    ∀ t : ℕ, 4 ≤ t → ∀ᶠ n : ℕ in atTop,
      ∀ G : Finset (Finset (Fin n)), G.IsUniform t → ¬ G.HasRepeatedDisjointUnion →
        ∀ (v : Fin n) (U : Finset (Fin n)), U ⊆ Finset.univ.erase v →
          let H := G.filter (fun E => v ∉ E)
          let m := (n - 1).choose (t - 1) - (G.filter (fun E => v ∈ E)).card
          (2 * t - 1) * m ≤ 2 * t * H.card →
          (U.card : ℝ) ≤ (n : ℝ) / (50 * (t : ℝ) ^ (4 * t + 3)) →
          ((K t : ℕ) : ℝ) * (U.card : ℝ) ^ (t - 1) ≤ (m : ℝ) →
          (∀ S : Finset (Fin n), S.card = t - 1 →
            ((Finset.univ.filter (fun x => x ∉ S ∧ insert x S ∈ H)) \ U).card ≤ 1) →
          (m : ℝ) ≤ (n : ℝ) * Real.log n

theorem stability_of_star_size : H1 → H2 → H3 →
    ∀ t : ℕ, 4 ≤ t → ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      ∀ F : Finset (Finset (Fin n)), F.IsUniform t → ¬ F.HasRepeatedDisjointUnion →
        (n - 1).choose (t - 1) ≤ F.card → ∃ v : Fin n,
          ((((n - 1).choose (t - 1) - (F.filter fun E => v ∈ E).card : ℕ)) : ℝ) ≤
            δ * ((n - 1).choose (t - 1) : ℝ) := by
  intro hdelete halign hdeficit t ht δ hδ
  obtain ⟨K, hK, hdeficit⟩ := hdeficit
  have hKreal : (0 : ℝ) < K t := by exact_mod_cast hK t ht
  obtain ⟨γ, hγ, hscales⟩ := stability_scales ht hδ hKreal
  obtain ⟨ε, hε, halign⟩ := halign t ht γ hγ
  let η := min γ ε
  have hη : 0 < η := lt_min hγ hε
  have hηγ : η ≤ γ := min_le_left _ _
  have hηε : η ≤ ε := min_le_right _ _
  filter_upwards [hdelete t ht η hη, halign, hdeficit t ht, hscales] with n hDel hAlign hDef hScale
  intro F hF hfree hLarge
  let S := (n - 1).choose (t - 1)
  obtain ⟨G, hGF, hGunif, hGfree, hGsize, hGlocal⟩ := hDel F hF hfree hLarge
  change (1 - η) * (S : ℝ) ≤ (G.card : ℝ) at hGsize
  have hSnonneg : (0 : ℝ) ≤ S := by positivity
  have hGsize' : (1 - ε) * (S : ℝ) ≤ (G.card : ℝ) :=
    (mul_le_mul_of_nonneg_right (sub_le_sub_left hηε 1) hSnonneg).trans hGsize
  obtain ⟨v, W, hWlarge, hWalign⟩ := hAlign G hGunif hGfree hGsize' hGlocal
  let U := Finset.univ.erase v \ W
  let H := G.filter fun E => v ∉ E
  let d := (G.filter fun E => v ∈ E).card
  let m := S - d
  have hdS : d ≤ S := degree_le_star (by omega) hGunif v
  have hdm : (d : ℝ) + (m : ℝ) = (S : ℝ) := by
    exact_mod_cast (show d + m = S by dsimp only [m]; omega)
  have hdH : (d : ℝ) + (H.card : ℝ) = (G.card : ℝ) := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s := G) (fun E => v ∈ E))
  have hUcover : (U.card : ℝ) ≤ (n : ℝ) - (W.card : ℝ) := by
    have hWcard : W.card ≤ n := by simpa using Finset.card_le_univ W
    rw [← Nat.cast_sub hWcard]
    exact_mod_cast (show U.card ≤ n - W.card by simpa [U] using exceptional_card_le v W)
  have hnear : (m : ℝ) ≤ δ * (S : ℝ) := by
    by_contra! hm
    obtain ⟨hu, huPow, hLoss, hStrict⟩ :=
      hScale (ε := γ) le_rfl (by positivity) (hUcover.trans hWlarge) hm
    have htrimLoss : η * (S : ℝ) ≤ (m : ℝ) / (2 * (t : ℝ)) :=
      (mul_le_mul_of_nonneg_right hηγ hSnonneg).trans hLoss
    have htpos : 0 < 2 * (t : ℝ) := by positivity
    have hscaledLoss := (le_div_iff₀ htpos).mp htrimLoss
    have hmass : (m : ℝ) ≤ (H.card : ℝ) + η * (S : ℝ) := by
      nlinarith only [hGsize, hdm, hdH]
    have hscaledMass := mul_le_mul_of_nonneg_left hmass htpos.le
    have hmassReal : (2 * (t : ℝ) - 1) * (m : ℝ) ≤ 2 * (t : ℝ) * (H.card : ℝ) := by
      nlinarith only [hscaledLoss, hscaledMass]
    have hmassNat : (2 * t - 1) * m ≤ 2 * t * H.card := by
      have hcast : (((2 * t - 1) * m : ℕ) : ℝ) ≤ ((2 * t * H.card : ℕ) : ℝ) := by
        push_cast [Nat.cast_sub (show 1 ≤ 2 * t by omega)]
        exact hmassReal
      exact_mod_cast hcast
    have hlog : (m : ℝ) ≤ (n : ℝ) * Real.log n :=
      hDef G hGunif hGfree v U Finset.sdiff_subset hmassNat hu huPow
        (outside_neighbors_card_le_one hWalign)
    exact (not_lt_of_ge hlog) hStrict
  refine ⟨v, ?_⟩
  have hdegree : d ≤ (F.filter fun E => v ∈ E).card :=
    Finset.card_le_card (Finset.filter_subset_filter _ hGF)
  have hdef : S - (F.filter fun E => v ∈ E).card ≤ m := Nat.sub_le_sub_left hdegree S
  exact (show ((S - (F.filter fun E => v ∈ E).card : ℕ) : ℝ) ≤ (m : ℝ) by
    exact_mod_cast hdef).trans hnear

theorem main : H1 → H2 → H3 → OMA.R_Erdos643_erdos_643_parts_ii_R1_H2_R1.H1 := by
  intro hdelete halign hdeficit t ht a ha
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hstable := stability_of_star_size hdelete halign hdeficit
    t ht (1 / (a : ℝ)) (one_div_pos.mpr haR)
  filter_upwards [hstable] with n hn
  intro F hF hfree hLarge
  obtain ⟨v,hv⟩ := hn F hF hfree hLarge
  refine ⟨v, ?_⟩
  dsimp only
  rw [missing_card v hF]
  have hm := (le_div_iff₀ haR).mp
    (show (((n - 1).choose (t - 1) - (F.filter fun E => v ∈ E).card : ℕ) : ℝ) ≤
      (((n - 1).choose (t - 1) : ℕ) : ℝ) / (a : ℝ) by
        simpa [div_eq_mul_inv, mul_comm] using hv)
  exact_mod_cast (by simpa only [mul_comm] using hm :
    (a : ℝ) * (((n - 1).choose (t - 1) - (F.filter fun E => v ∈ E).card : ℕ) : ℝ) ≤
      ((n - 1).choose (t - 1) : ℝ))

end OMA.R_Erdos643_erdos_643_parts_ii_R1_H2_R1_H1_R1
