import OMAStatements.S_mo_433993

namespace OMA.Mo433993

open Finset OMA.S_mo_433993

def layer (d k : ℕ) : Family d :=
  (Finset.univ : Finset (Fin d)).powersetCard k

noncomputable def center0 (d k : ℕ) : V d := fun _ => (k : ℝ) / d

noncomputable def radius (d k : ℕ) : ℝ := (k : ℝ) * ((d : ℝ) - k) / d

def dot {d : ℕ} (u v : V d) : ℝ := ∑ i, u i * v i

noncomputable def centered {d : ℕ} (k : ℕ) (s : Finset (Fin d)) : V d :=
  fun i => bit s i - center0 d k i

noncomputable def centeredAvg {d : ℕ} (k : ℕ) (S : Family d) : V d :=
  fun i => avg S i - center0 d k i

lemma mem_layer {d k : ℕ} {s : Finset (Fin d)} :
    s ∈ layer d k ↔ s.card = k := by
  simp [layer, Finset.mem_powersetCard]

lemma card_layer (d k : ℕ) : (layer d k).card = d.choose k := by
  simp [layer, Finset.card_powersetCard]

lemma sum_bit {d : ℕ} (s : Finset (Fin d)) :
    ∑ i, bit s i = (s.card : ℝ) := by
  calc
    ∑ i, bit s i = ∑ i ∈ (Finset.univ.filter fun i => i ∈ s), (1 : ℝ) := by
      rw [Finset.sum_filter] <;> rfl
    _ = _ := by simp

lemma bit_sq {d : ℕ} (s : Finset (Fin d)) (i : Fin d) :
    (bit s i)^2 = bit s i := by
  by_cases hi : i ∈ s <;> simp [bit, hi]

lemma centered_sum_zero {d k : ℕ} (hd : 0 < d) {s : Finset (Fin d)}
    (hs : s.card = k) : ∑ i, centered k s i = 0 := by
  have hdn : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  simp only [centered, center0, Finset.sum_sub_distrib, sum_bit, hs,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hdn] <;> ring

lemma centered_dot_self {d k : ℕ} (hd : 0 < d) {s : Finset (Fin d)}
    (hs : s.card = k) : dot (centered k s) (centered k s) = radius d k := by
  have hdn : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  let c : ℝ := (k : ℝ) / d
  calc
    dot (centered k s) (centered k s) = ∑ i, (bit s i - c)^2 := by
      simp [dot, centered, center0, c, pow_two]
    _ = ∑ i, (bit s i - (2*c) * bit s i + c^2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [sub_sq, bit_sq]
      ring
    _ = (∑ i, bit s i) - (2*c) * (∑ i, bit s i) + (d : ℝ) * c^2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp [nsmul_eq_mul]
    _ = radius d k := by
      rw [sum_bit, hs]
      dsimp [c, radius]
      field_simp [hdn] <;> ring

end OMA.Mo433993

namespace OMA.Mo433993

open Finset OMA.S_mo_433993

theorem layer_sum_avg {d k : ℕ} {S : Family d} (hS : S.Nonempty)
    (hsize : ∀ s ∈ S, s.card = k) : (∑ i, avg S i) = (k : ℝ) := by
  have hcard : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast hS.card_ne_zero
  unfold avg
  rw [← sum_div, sum_comm]
  calc
    (∑ s ∈ S, ∑ i, bit s i) / (S.card : ℝ) =
        (∑ _s ∈ S, (k : ℝ)) / (S.card : ℝ) := by
      congr 1
      exact sum_congr rfl fun s hs => by rw [sum_bit, hsize s hs]
    _ = k := by simp [hcard]

theorem centered_avg_sum_zero {d k : ℕ} {S : Family d} (hkd : k < d)
    (hS : S.Nonempty) (hsize : ∀ s ∈ S, s.card = k) :
    ∑ i, centeredAvg k S i = 0 := by
  have hd : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt ((Nat.zero_le k).trans_lt hkd))
  simp [centeredAvg, center0, sum_sub_distrib, layer_sum_avg hS hsize, mul_div_cancel₀ _ hd]

theorem coord_variance {d : ℕ} {S : Family d} (hS : S.Nonempty)
    (C : V d) (i : Fin d) :
    (∑ s ∈ S, (bit s i - C i)^2) =
      (∑ s ∈ S, (bit s i - avg S i)^2) + (S.card : ℝ) * (avg S i - C i)^2 := by
  have hcard : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast hS.card_ne_zero
  have hsum : (∑ s ∈ S, (bit s i - avg S i)) = 0 := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
    simp [avg, mul_div_cancel₀, hcard]
  calc
    (∑ s ∈ S, (bit s i - C i)^2) =
        ∑ s ∈ S, ((bit s i - avg S i)^2 + (avg S i - C i)^2 +
          (2 * (avg S i - C i)) * (bit s i - avg S i)) := by
      apply sum_congr rfl
      intro s _
      ring
    _ = _ := by
      rw [sum_add_distrib, sum_add_distrib, ← mul_sum, hsum]
      simp

theorem sum_squared_dist_split {d : ℕ} {S : Family d} (hS : S.Nonempty)
    (C : V d) :
    (∑ s ∈ S, sqDist (bit s) C) =
      (∑ s ∈ S, sqDist (bit s) (avg S)) + (S.card : ℝ) * sqDist (avg S) C := by
  unfold sqDist
  rw [sum_comm]
  simp_rw [coord_variance hS C]
  rw [sum_add_distrib, sum_comm, ← mul_sum]

theorem center_average_bound {d k : ℕ} {S : Family d} {C : V d} (hkd : k < d)
    (hS : S.Nonempty) (hsize : ∀ s ∈ S, s.card = k) (hC : Center S C) :
    sqDist (avg S) C ≤ dot (centeredAvg k S) (centeredAvg k S) ∧
      sqDist (avg S) C ≤ radius d k := by
  obtain ⟨R, hcover, hminimal⟩ := hC
  have hcard : (0 : ℝ) < S.card := by
    exact_mod_cast hS.card_pos
  have hdist (s : Finset (Fin d)) (hs : s ∈ S) :
      sqDist (bit s) (center0 d k) = radius d k := by
    simpa [sqDist, dot, centered, pow_two] using
      centered_dot_self ((Nat.zero_le k).trans_lt hkd) (hsize s hs)
  have hR : R ≤ radius d k :=
    hminimal (center0 d k) _ fun s hs => (hdist s hs).le
  have hsum : (∑ s ∈ S, sqDist (bit s) C) ≤ (S.card : ℝ) * radius d k := by
    calc
      _ ≤ ∑ _s ∈ S, radius d k := sum_le_sum fun s hs => (hcover s hs).trans hR
      _ = _ := by simp
  have hsum0 :
      (∑ s ∈ S, sqDist (bit s) (center0 d k)) = (S.card : ℝ) * radius d k := by
    calc
      _ = ∑ _s ∈ S, radius d k := sum_congr rfl hdist
      _ = _ := by simp
  have hrelative := hsum.trans_eq hsum0.symm
  rw [sum_squared_dist_split hS C, sum_squared_dist_split hS (center0 d k)] at hrelative
  have hvar :
      0 ≤ ∑ s ∈ S, sqDist (bit s) (avg S) :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  rw [sum_squared_dist_split hS C] at hsum
  constructor
  · simpa [dot, centeredAvg, sqDist, pow_two] using
      (le_of_mul_le_mul_left (le_of_add_le_add_left hrelative) hcard :
        sqDist (avg S) C ≤ sqDist (avg S) (center0 d k))
  · exact le_of_mul_le_mul_left ((le_add_of_nonneg_left hvar).trans hsum) hcard

end OMA.Mo433993

namespace OMA.Mo433993

open Finset OMA.S_mo_433993

lemma layer_sum_perm (d k : ℕ) (e : Equiv.Perm (Fin d)) (f : Finset (Fin d) → ℝ) :
    (∑ s ∈ layer d k, f (s.map e.toEmbedding)) = ∑ s ∈ layer d k, f s := by
  refine Finset.sum_equiv (Equiv.finsetCongr e) (fun s => ?_) (fun _ _ => rfl)
  simp [Equiv.finsetCongr_apply, layer, Finset.mem_powersetCard]

lemma layer_centered_map {d k : ℕ} (s : Finset (Fin d)) (e : Equiv.Perm (Fin d))
    (i : Fin d) : centered k (s.map e.toEmbedding) (e i) = centered k s i := by
  have hm : e i ∈ s.map e.toEmbedding ↔ i ∈ s := Finset.mem_map' e.toEmbedding
  simp only [centered, center0, bit, hm]

lemma layer_dot_sum_zero (d k : ℕ) (hk : k < d) (u : V d) :
    (∑ s ∈ layer d k, dot (centered k s) u) = 0 := by
  have hd : 0 < d := by omega
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have htotal : (∑ i : Fin d, ∑ s ∈ layer d k, centered k s i) = 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun s hs => centered_sum_zero hd (mem_layer.mp hs)
  have hperm (i j : Fin d) :
      (∑ s ∈ layer d k, centered k s i) = ∑ s ∈ layer d k, centered k s j := by
    calc
      _ = ∑ s ∈ layer d k, centered k (s.map (Equiv.swap i j).toEmbedding) j := by
        apply Finset.sum_congr rfl
        intro s _
        simpa only [Equiv.swap_apply_left] using
          (layer_centered_map s (Equiv.swap i j) (k := k) i).symm
      _ = _ := layer_sum_perm d k (Equiv.swap i j) (fun s => centered k s j)
  have hmoment (i : Fin d) : (∑ s ∈ layer d k, centered k s i) = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hd0
    calc
      _ = ∑ j : Fin d, ∑ s ∈ layer d k, centered k s i := by simp
      _ = ∑ j : Fin d, ∑ s ∈ layer d k, centered k s j :=
        Finset.sum_congr rfl fun j _ => hperm i j
      _ = 0 := htotal
  unfold dot
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, hmoment, zero_mul, Finset.sum_const_zero]

noncomputable def layerCov (d k : ℕ) (i j : Fin d) : ℝ :=
  ∑ s ∈ layer d k, centered k s i * centered k s j

lemma layerCov_perm (d k : ℕ) (e : Equiv.Perm (Fin d)) (i j : Fin d) :
    layerCov d k i j = layerCov d k (e i) (e j) := by
  unfold layerCov
  calc
    _ = ∑ s ∈ layer d k,
        centered k (s.map e.toEmbedding) (e i) * centered k (s.map e.toEmbedding) (e j) := by
      simp only [layer_centered_map]
    _ = _ := layer_sum_perm d k e (fun s => centered k s (e i) * centered k s (e j))

lemma layerCov_diag (d k : ℕ) (hk : k < d) (i : Fin d) :
    layerCov d k i i = (d.choose k : ℝ) * radius d k / d := by
  have hd : 0 < d := by omega
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  apply (eq_div_iff hd0).2
  calc
    layerCov d k i i * d = ∑ j : Fin d, layerCov d k i i := by simp [mul_comm]
    _ = ∑ j : Fin d, layerCov d k j j := by
      apply Finset.sum_congr rfl
      intro j _
      simpa only [Equiv.swap_apply_left] using layerCov_perm d k (Equiv.swap i j) i i
    _ = ∑ s ∈ layer d k, dot (centered k s) (centered k s) := by
      simp only [layerCov, dot]
      rw [Finset.sum_comm]
    _ = ∑ _s ∈ layer d k, radius d k :=
      Finset.sum_congr rfl fun s hs => centered_dot_self hd (mem_layer.mp hs)
    _ = _ := by simp [card_layer, nsmul_eq_mul]

lemma layerCov_off (d k : ℕ) (hd : 1 < d) (hk : k < d) (i j : Fin d) (hji : j ≠ i) :
    layerCov d k i j = -((d.choose k : ℝ) * radius d k / d) / ((d : ℝ) - 1) := by
  have hdReal : (1 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  have hrow : (∑ a : Fin d, layerCov d k i a) = 0 := by
    simp only [layerCov]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro s hs
    rw [← Finset.mul_sum, centered_sum_zero (by omega) (mem_layer.mp hs), mul_zero]
  have hconst : (∑ a ∈ (Finset.univ : Finset (Fin d)).erase i, layerCov d k i a) =
      ((d : ℝ) - 1) * layerCov d k i j := by
    calc
      _ = ∑ _a ∈ (Finset.univ : Finset (Fin d)).erase i, layerCov d k i j := by
        apply Finset.sum_congr rfl
        intro a ha
        have hai := (Finset.mem_erase.mp ha).1
        simpa only [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hai.symm hji.symm] using
          layerCov_perm d k (Equiv.swap a j) i a
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [Finset.cast_card_erase_of_mem (Finset.mem_univ i)]
        simp
  have hadd := Finset.sum_erase_add (s := Finset.univ) (layerCov d k i) (Finset.mem_univ i)
  rw [hconst, hrow, layerCov_diag d k hk i] at hadd
  apply (eq_div_iff hd1).2
  linarith only [hadd]

lemma layer_dot_sq_sum (d k : ℕ) (hd : 1 < d) (hk : k < d) (u : V d)
    (hsum : ∑ i, u i = 0) :
    (∑ s ∈ layer d k, (dot (centered k s) u)^2) =
      (d.choose k : ℝ) * (radius d k / ((d : ℝ) - 1)) * dot u u := by
  have hdReal : (1 : ℝ) < d := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := by linarith
  have hd1 : (d : ℝ) - 1 ≠ 0 := by linarith
  have hrow (i : Fin d) :
      (∑ j, layerCov d k i j * u j) =
        (d.choose k : ℝ) * (radius d k / ((d : ℝ) - 1)) * u i := by
    have hsplit :=
      Finset.sum_erase_add (s := Finset.univ) (fun j => layerCov d k i j * u j) (Finset.mem_univ i)
    have husum : (∑ j ∈ (Finset.univ : Finset (Fin d)).erase i, u j) = -u i := by
      have h := Finset.sum_erase_add (s := Finset.univ) u (Finset.mem_univ i)
      rw [hsum] at h
      linarith only [h]
    have hoff : (∑ j ∈ (Finset.univ : Finset (Fin d)).erase i, layerCov d k i j * u j) =
        ∑ j ∈ (Finset.univ : Finset (Fin d)).erase i,
          (-((d.choose k : ℝ) * radius d k / d) / ((d : ℝ) - 1)) * u j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [layerCov_off d k hd hk i j (Finset.mem_erase.mp hj).1]
    rw [← hsplit, hoff, ← Finset.mul_sum, husum, layerCov_diag d k hk i]
    field_simp
    ring
  calc
    _ = ∑ s ∈ layer d k, ∑ i : Fin d, ∑ j : Fin d,
        centered k s i * centered k s j * u j * u i := by
      apply Finset.sum_congr rfl
      intro s _
      simp only [dot, pow_two, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ i : Fin d, ∑ j : Fin d, ∑ s ∈ layer d k,
        centered k s i * centered k s j * u j * u i := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i : Fin d, (∑ j, layerCov d k i j * u j) * u i := by
      simp only [layerCov, Finset.sum_mul]
    _ = _ := by
      simp only [hrow, dot, Finset.mul_sum, mul_assoc]

end OMA.Mo433993

namespace OMA.Mo433993

open Finset OMA.S_mo_433993

lemma density_bound {d k : ℕ} {S : Family d} (hS : S.Nonempty)
    (hcard : ∀ s ∈ S, s.card = k) (hd : 1 < d) (hk : k < d)
    (hmean : ∑ s ∈ layer d k, dot (centered k s) (centeredAvg k S) = 0)
    (hsecond : ∑ s ∈ layer d k, dot (centered k s) (centeredAvg k S) ^ 2 =
      (d.choose k : ℝ) * (radius d k / ((d : ℝ) - 1)) *
        dot (centeredAvg k S) (centeredAvg k S)) :
    dot (centeredAvg k S) (centeredAvg k S) ≤
      ((d.choose k : ℝ) / (S.card : ℝ) - 1) * (radius d k / ((d : ℝ) - 1)) := by
  classical
  let L := layer d k
  let m : ℝ := S.card
  let n : ℝ := d.choose k
  let q : ℝ := radius d k / ((d : ℝ) - 1)
  let u := centeredAvg k S
  let f := fun s => dot (centered k s) u
  let w := fun s => (if s ∈ S then 1 else 0) - m / n
  change dot u u ≤ (n / m - 1) * q
  have hsub : S ⊆ L := by
    intro s hs
    exact mem_layer.mpr (hcard s hs)
  have hLcard : L.card = d.choose k := card_layer d k
  have hm : 0 < m := by
    change 0 < (S.card : ℝ)
    exact_mod_cast Finset.card_pos.mpr hS
  have hmn : m ≤ n := by
    have h := Finset.card_le_card hsub
    rw [hLcard] at h
    change (S.card : ℝ) ≤ (d.choose k : ℝ)
    exact_mod_cast h
  have hn : 0 < n := hm.trans_le hmn
  have hfilter : L.filter (fun s => s ∈ S) = S := by
    ext s
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hs => ⟨hsub hs, hs⟩⟩
  have hsumIndicator (g : Finset (Fin d) → ℝ) :
      (∑ s ∈ L, (if s ∈ S then 1 else 0) * g s) = ∑ s ∈ S, g s := by
    simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter, hfilter]
  have hcoord (i : Fin d) : ∑ s ∈ S, centered k s i = m * u i := by
    change (∑ s ∈ S, (bit s i - center0 d k i)) =
      (S.card : ℝ) * ((∑ s ∈ S, bit s i) / (S.card : ℝ) - center0 d k i)
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have hcard_ne : (S.card : ℝ) ≠ 0 := ne_of_gt hm
    field_simp
  have hsumS : ∑ s ∈ S, f s = m * dot u u := by
    change (∑ s ∈ S, ∑ i : Fin d, centered k s i * u i) =
      m * ∑ i : Fin d, u i * u i
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul, hcoord]
    ring
  have hsumWf : ∑ s ∈ L, w s * f s = m * dot u u := by
    simp only [w, sub_mul, Finset.sum_sub_distrib, hsumIndicator, ← Finset.mul_sum]
    rw [show (∑ s ∈ L, f s) = 0 from hmean, mul_zero, sub_zero, hsumS]
  have hsqW (s : Finset (Fin d)) : w s ^ 2 =
      (if s ∈ S then 1 else 0) * (1 - 2 * (m / n)) + (m / n) ^ 2 := by
    by_cases hs : s ∈ S
    · simp [w, hs]
      ring
    · simp [w, hs]
  have hsumWsq : ∑ s ∈ L, w s ^ 2 = m - m * m / n := by
    simp only [hsqW, Finset.sum_add_distrib, hsumIndicator, Finset.sum_const, nsmul_eq_mul]
    rw [hLcard]
    change m * (1 - 2 * (m / n)) + n * (m / n) ^ 2 = m - m * m / n
    field_simp [ne_of_gt hn]
    ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq L w f
  have hsecond' : ∑ s ∈ L, f s ^ 2 = n * q * dot u u := hsecond
  rw [hsumWf, hsumWsq, hsecond'] at hcs
  have hfactor : (m - m * m / n) * (n * q * dot u u) =
      (m * dot u u) * (m * ((n / m - 1) * q)) := by
    field_simp [ne_of_gt hm, ne_of_gt hn]
  rw [hfactor, sq] at hcs
  have hu : 0 ≤ dot u u := Finset.sum_nonneg (fun i _ => mul_self_nonneg (u i))
  rcases hu.eq_or_lt with hu0 | hu0
  · rw [← hu0]
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd.le
    have hk' : (k : ℝ) ≤ d := by exact_mod_cast hk.le
    have hq : 0 ≤ q :=
      div_nonneg
        (div_nonneg (mul_nonneg (Nat.cast_nonneg k) (sub_nonneg.mpr hk')) (Nat.cast_nonneg d))
        (sub_nonneg.mpr hd')
    exact mul_nonneg (sub_nonneg.mpr ((le_div_iff₀ hm).mpr (by simpa using hmn))) hq
  · have h := (mul_le_mul_iff_right₀ (mul_pos hm hu0)).mp hcs
    exact (mul_le_mul_iff_right₀ hm).mp h

end OMA.Mo433993

open Finset OMA.S_mo_433993 OMA.Mo433993 in
theorem OMA.solution : type_of% @OMA.S_mo_433993.main := by
  intro d k S C hk hs hcard hc
  obtain ⟨hmean, hrad⟩ :=
    center_average_bound (d := d) (k := k) (S := S) (C := C) hk hs hcard hc
  refine ⟨hrad, ?_⟩
  by_cases hd : 1 < d
  · let u := centeredAvg k S
    have hz : ∑ i, u i = 0 := by
      dsimp [u]
      apply centered_avg_sum_zero <;> first | assumption | omega
    have hnorm := density_bound hs hcard hd hk
      (layer_dot_sum_zero d k hk u) (layer_dot_sq_sum d k hd hk u hz)
    simpa only [radius, div_div] using hmean.trans hnorm
  · have hd' : d = 1 := by omega
    have hk' : k = 0 := by omega
    subst k
    subst d
    simpa [radius] using hrad
