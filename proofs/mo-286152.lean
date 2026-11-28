import OMAStatements.S_mo_286152

namespace OMA.S_mo_286152_Proof

open Finset Submodule
open scoped InnerProductSpace

abbrev Coord' := (Fin 3 × Fin 5) ⊕ Fin 10
abbrev H' := EuclideanSpace ℂ Coord'
abbrev Op' := H' →L[ℂ] H'

def pattern : Fin 3 → ℤ := ![1, 1, 2]

def pairs : Fin 10 → Fin 5 × Fin 5 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

def uZ : Coord' → ℤ
  | Sum.inl (k, _) => pattern k
  | Sum.inr _ => 0

def eZ (i : Fin 5) : Coord' → ℤ
  | Sum.inl (k, i') => if i' = i then pattern k else 0
  | Sum.inr _ => 0

def vZ (i : Fin 5) : Coord' → ℤ :=
  fun c => uZ c + 5 * eZ i c

def mZ (i j : Fin 5) : Coord' → ℤ
  | Sum.inl _ => 0
  | Sum.inr b =>
      let pq := pairs b
      if (pq.1 = i ∧ pq.2 = j) ∨ (pq.1 = j ∧ pq.2 = i) then 3
      else if pq.1 = i ∨ pq.1 = j ∨ pq.2 = i ∨ pq.2 = j then -1
      else 1

def zZ (i j : Fin 5) : Coord' → ℤ :=
  fun c => -uZ c + 10 * (eZ i c + eZ j c) + 5 * mZ i j c

def yZ (i j : Fin 5) : Coord' → ℤ :=
  fun c => -uZ c + eZ i c + 4 * eZ j c + 2 * mZ i j c

def dotZ (f g : Coord' → ℤ) : ℤ := ∑ c : Coord', f c * g c

lemma uZ_ne_zero : uZ (Sum.inl (0, 0)) ≠ 0 := by decide

lemma dotZ_vZ_uZ : ∀ i : Fin 5, dotZ (vZ i) uZ = 60 := by decide

lemma dotZ_vZ_self : ∀ i : Fin 5, dotZ (vZ i) (vZ i) = 240 := by decide

lemma dotZ_yZ_uZ : ∀ i j : Fin 5, j ≠ i → dotZ (yZ i j) uZ = 0 := by decide

lemma dotZ_yZ_vZ : ∀ i j : Fin 5, j ≠ i → dotZ (yZ i j) (vZ i) = 0 := by decide

lemma dotZ_yZ_yZ :
    ∀ i j k : Fin 5, j ≠ i → k ≠ i →
      dotZ (yZ i j) (yZ i k) = if j = k then 144 else -48 := by
  decide

lemma dotZ_yZ_vZ_other :
    ∀ i j k : Fin 5, j ≠ i → k ≠ i →
      dotZ (yZ i j) (vZ k) = if j = k then 90 else -30 := by
  decide

lemma dotZ_vZ_vZ_other :
    ∀ i k : Fin 5, k ≠ i → dotZ (vZ i) (vZ k) = 90 := by
  decide

lemma sum_yZ_eq_zero : ∀ i : Fin 5, ∀ c : Coord', ∑ j ∈ Finset.univ.erase i, yZ i j c = 0 := by
  decide

lemma sum_vZ_eq : ∀ c : Coord', ∑ i : Fin 5, vZ i c = 10 * uZ c := by
  decide

lemma zZ_symm : ∀ i j : Fin 5, ∀ c : Coord', zZ i j c = zZ j i c := by
  decide

lemma yZ_rel : ∀ i j : Fin 5, ∀ c : Coord', 5 * yZ i j c = 2 * zZ i j c - 3 * vZ i c := by
  decide

noncomputable def vec (f : Coord' → ℤ) : H' :=
  WithLp.toLp 2 (fun c => (f c : ℂ))

lemma vec_apply (f : Coord' → ℤ) (c : Coord') : vec f c = (f c : ℂ) := rfl

lemma inner_vec (f g : Coord' → ℤ) : ⟪vec f, vec g⟫_ℂ = ((dotZ f g : ℤ) : ℂ) := by
  rw [PiLp.inner_apply]
  simp only [vec_apply, RCLike.inner_apply, map_intCast]
  push_cast [dotZ]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

lemma vec_sum {ι : Type*} (s : Finset ι) (f : ι → Coord' → ℤ) :
    vec (fun c => ∑ i ∈ s, f i c) = ∑ i ∈ s, vec (f i) := by
  ext c
  simp [vec_apply, Finset.sum_apply]

lemma vec_zero : vec (fun _ => 0) = 0 := by
  ext c
  simp [vec_apply]

lemma u_ne_zero : vec uZ ≠ 0 := by
  intro h
  have hc : vec uZ (Sum.inl (0, 0)) = (0 : H') (Sum.inl (0, 0)) :=
    congrArg (fun x => x (Sum.inl (0, 0))) h
  simp only [vec_apply, PiLp.zero_apply, Int.cast_eq_zero] at hc
  exact uZ_ne_zero hc

noncomputable def rankSelf (w : H') : Op' :=
  (innerSL ℂ w).smulRight w

lemma rankSelf_apply (w x : H') : rankSelf w x = ⟪w, x⟫_ℂ • w := rfl

noncomputable def projOp (i : Fin 5) : Op' :=
  (1 / 240 : ℂ) • rankSelf (vec (vZ i)) +
    (1 / 192 : ℂ) • ∑ j ∈ Finset.univ.erase i, rankSelf (vec (yZ i j))

lemma projOp_apply (i : Fin 5) (x : H') :
    projOp i x = (1 / 240 : ℂ) • (⟪vec (vZ i), x⟫_ℂ • vec (vZ i)) +
      (1 / 192 : ℂ) • ∑ j ∈ Finset.univ.erase i, (⟪vec (yZ i j), x⟫_ℂ • vec (yZ i j)) := by
  simp [projOp, rankSelf_apply]

lemma projOp_isSelfAdjoint (i : Fin 5) : IsSelfAdjoint (projOp i) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x z
  simp only [ContinuousLinearMap.coe_coe, projOp_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, inner_sum, sum_inner]
  have h240 : starRingEnd ℂ (1 / 240 : ℂ) = (1 / 240 : ℂ) := by
    simp only [map_div₀, map_one, map_ofNat]
  have h192 : starRingEnd ℂ (1 / 192 : ℂ) = (1 / 192 : ℂ) := by
    simp only [map_div₀, map_one, map_ofNat]
  rw [h240, h192]
  congr 1
  · rw [inner_conj_symm]
    ring
  · congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_conj_symm]
    ring

lemma projOp_vec_vZ_self (i : Fin 5) : projOp i (vec (vZ i)) = vec (vZ i) := by
  rw [projOp_apply]
  have h1 : ⟪vec (vZ i), vec (vZ i)⟫_ℂ = (240 : ℂ) := by
    rw [inner_vec, dotZ_vZ_self i]
    norm_num
  have h2 : ∑ j ∈ Finset.univ.erase i, ⟪vec (yZ i j), vec (vZ i)⟫_ℂ • vec (yZ i j) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [inner_vec, dotZ_yZ_vZ i j (Finset.ne_of_mem_erase hj)]
    simp
  rw [h1, h2]
  simp [smul_smul]

lemma projOp_vec_yZ (i j : Fin 5) (hji : j ≠ i) : projOp i (vec (yZ i j)) = vec (yZ i j) := by
  rw [projOp_apply]
  have h1 : ⟪vec (vZ i), vec (yZ i j)⟫_ℂ = 0 := by
    rw [← inner_conj_symm, inner_vec, dotZ_yZ_vZ i j hji]
    simp
  have hsum : ∑ k ∈ Finset.univ.erase i, vec (yZ i k) = 0 := by
    rw [← vec_sum]
    simpa [vec_zero] using congrArg vec (funext (sum_yZ_eq_zero i))
  have h2 :
      ∑ k ∈ Finset.univ.erase i, ⟪vec (yZ i k), vec (yZ i j)⟫_ℂ • vec (yZ i k) =
        (192 : ℂ) • vec (yZ i j) := by
    have hsplit :
        ∑ k ∈ Finset.univ.erase i, ⟪vec (yZ i k), vec (yZ i j)⟫_ℂ • vec (yZ i k) =
          ∑ k ∈ Finset.univ.erase i,
            ((if k = j then (144 : ℂ) else (-48 : ℂ)) • vec (yZ i k)) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [inner_vec, dotZ_yZ_yZ i k j (Finset.ne_of_mem_erase hk) hji]
      split_ifs <;> norm_num
    rw [hsplit]
    have hrew :
        ∑ k ∈ Finset.univ.erase i,
            ((if k = j then (144 : ℂ) else (-48 : ℂ)) • vec (yZ i k)) =
          ∑ k ∈ Finset.univ.erase i,
            ((if k = j then (192 : ℂ) else 0) • vec (yZ i k) +
              (-48 : ℂ) • vec (yZ i k)) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs
      · rw [← add_smul]; norm_num
      · simp
    rw [hrew, Finset.sum_add_distrib, ← Finset.smul_sum, hsum, smul_zero, add_zero]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj; simp [hkj]
    · intro hj; exact absurd (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩) hj
  rw [h1, h2]
  simp [smul_smul]

lemma projOp_isIdempotent (i : Fin 5) : IsIdempotentElem (projOp i) := by
  rw [isIdempotentElem_iff]
  refine ContinuousLinearMap.ext fun x => ?_
  change projOp i (projOp i x) = projOp i x
  conv_lhs => arg 2; rw [projOp_apply]
  rw [map_add, map_smul, map_smul, map_smul, map_sum]
  simp only [map_smul, projOp_vec_vZ_self]
  have hs :
      ∑ j ∈ Finset.univ.erase i, ⟪vec (yZ i j), x⟫_ℂ • projOp i (vec (yZ i j)) =
        ∑ j ∈ Finset.univ.erase i, ⟪vec (yZ i j), x⟫_ℂ • vec (yZ i j) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [projOp_vec_yZ i j (Finset.ne_of_mem_erase hj)]
  rw [hs, ← projOp_apply]

lemma projOp_isStarProjection (i : Fin 5) : IsStarProjection (projOp i) :=
  ⟨projOp_isIdempotent i, projOp_isSelfAdjoint i⟩

lemma projOp_u (i : Fin 5) : projOp i (vec uZ) = (1 / 4 : ℂ) • vec (vZ i) := by
  rw [projOp_apply]
  have h1 : ⟪vec (vZ i), vec uZ⟫_ℂ = (60 : ℂ) := by
    rw [inner_vec, dotZ_vZ_uZ i]
    norm_num
  have h2 : ∑ j ∈ Finset.univ.erase i, ⟪vec (yZ i j), vec uZ⟫_ℂ • vec (yZ i j) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [inner_vec, dotZ_yZ_uZ i j (Finset.ne_of_mem_erase hj)]
    simp
  rw [h1, h2]
  simp [smul_smul]
  norm_num

lemma projOp_vZ_other (i k : Fin 5) (hki : k ≠ i) :
    projOp i (vec (vZ k)) = (1 / 4 : ℂ) • vec (zZ i k) := by
  rw [projOp_apply]
  have h1 : ⟪vec (vZ i), vec (vZ k)⟫_ℂ = (90 : ℂ) := by
    rw [inner_vec, dotZ_vZ_vZ_other i k hki]
    norm_num
  have hsum : ∑ j ∈ Finset.univ.erase i, vec (yZ i j) = 0 := by
    rw [← vec_sum]
    simpa [vec_zero] using congrArg vec (funext (sum_yZ_eq_zero i))
  have h2 :
      ∑ j ∈ Finset.univ.erase i, ⟪vec (yZ i j), vec (vZ k)⟫_ℂ • vec (yZ i j) =
        (120 : ℂ) • vec (yZ i k) := by
    have hsplit :
        ∑ j ∈ Finset.univ.erase i, ⟪vec (yZ i j), vec (vZ k)⟫_ℂ • vec (yZ i j) =
          ∑ j ∈ Finset.univ.erase i,
            ((if j = k then (90 : ℂ) else (-30 : ℂ)) • vec (yZ i j)) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [inner_vec, dotZ_yZ_vZ_other i j k (Finset.ne_of_mem_erase hj) hki]
      split_ifs <;> norm_num
    rw [hsplit]
    have hrew :
        ∑ j ∈ Finset.univ.erase i,
            ((if j = k then (90 : ℂ) else (-30 : ℂ)) • vec (yZ i j)) =
          ∑ j ∈ Finset.univ.erase i,
            ((if j = k then (120 : ℂ) else 0) • vec (yZ i j) +
              (-30 : ℂ) • vec (yZ i j)) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs
      · rw [← add_smul]; norm_num
      · simp
    rw [hrew, Finset.sum_add_distrib, ← Finset.smul_sum, hsum, smul_zero, add_zero]
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hjk; simp [hjk]
    · intro hk; exact absurd (Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩) hk
  have hrel : (5 : ℂ) • vec (yZ i k) = (2 : ℂ) • vec (zZ i k) - (3 : ℂ) • vec (vZ i) := by
    ext c
    have hc := congrArg (fun n : ℤ => (n : ℂ)) (yZ_rel i k c)
    simpa [vec_apply] using hc
  rw [h1, h2]
  have h120 : (1 / 192 : ℂ) • ((120 : ℂ) • vec (yZ i k)) =
      (1 / 8 : ℂ) • ((5 : ℂ) • vec (yZ i k)) := by
    rw [smul_smul, smul_smul]
    congr 1
    norm_num
  rw [h120, hrel]
  simp only [smul_sub, smul_smul]
  norm_num

lemma projOp_comm_u (i j : Fin 5) :
    projOp i (projOp j (vec uZ)) = projOp j (projOp i (vec uZ)) := by
  rw [projOp_u i, projOp_u j, map_smul, map_smul]
  by_cases hij : i = j
  · subst hij; rfl
  · rw [projOp_vZ_other i j (Ne.symm hij), projOp_vZ_other j i hij]
    have hz : vec (zZ i j) = vec (zZ j i) := congrArg vec (funext (zZ_symm i j))
    rw [hz]

lemma sum_projOp_u : ∑ i : Fin 5, projOp i (vec uZ) = (5 / 2 : ℂ) • vec uZ := by
  simp_rw [projOp_u, ← Finset.smul_sum, ← vec_sum]
  have hsum : vec (fun c => ∑ i : Fin 5, vZ i c) = (10 : ℂ) • vec uZ := by
    ext c
    have hc := congrArg (fun n : ℤ => (n : ℂ)) (sum_vZ_eq c)
    simpa [vec_apply] using hc
  rw [hsum, smul_smul]
  norm_num

noncomputable def polyProd (T : Op') : ℕ → Op'
  | 0 => T
  | n + 1 => polyProd T n * (T - ((n + 1 : ℕ) : ℂ) • (1 : Op'))

lemma commute_polyProd {T e : Op'} (hc : Commute T e) :
    ∀ n : ℕ, Commute (polyProd T n) e
  | 0 => hc
  | n + 1 => (commute_polyProd hc n).mul_left (hc.sub_left (Commute.smul_left (Commute.one_left e) _))

lemma polyProd_add_one (T : Op') :
    ∀ n : ℕ, polyProd (T + 1) (n + 1) = (T + 1) * polyProd T n
  | 0 => by
      simp only [polyProd]
      have h : T + 1 - ((1 : ℕ) : ℂ) • (1 : Op') = T := by simp
      rw [h]
  | n + 1 => by
      have ih := polyProd_add_one T n
      simp only [polyProd] at ih ⊢
      rw [ih, mul_assoc]
      congr 2
      rw [show ((n + 2 : ℕ) : ℂ) • (1 : Op') = ((n + 1 : ℕ) : ℂ) • (1 : Op') + 1 by
        refine ContinuousLinearMap.ext fun x => ?_
        simp [add_smul, Nat.cast_add]
        module]
      abel

lemma one_sub_mul_polyProd_add {T e : Op'} (he : e * e = e) (hc : Commute T e) :
    ∀ n : ℕ, (1 - e) * polyProd (T + e) n = (1 - e) * polyProd T n
  | 0 => by
      simp only [polyProd, mul_add, sub_mul, one_mul, he, sub_self, add_zero]
  | n + 1 => by
      have ih := one_sub_mul_polyProd_add he hc n
      simp only [polyProd]
      have hcomm : Commute (polyProd T n) (1 - e) :=
        Commute.sub_right (Commute.one_right _) (commute_polyProd hc n)
      have hsub : (1 - e) * (T + e - ((n + 1 : ℕ) : ℂ) • (1 : Op')) =
          (1 - e) * (T - ((n + 1 : ℕ) : ℂ) • (1 : Op')) := by
        rw [add_sub_right_comm, mul_add,
          show (1 - e) * e = 0 by rw [sub_mul, one_mul, he, sub_self], add_zero]
      calc
        (1 - e) * (polyProd (T + e) n * (T + e - ((n + 1 : ℕ) : ℂ) • (1 : Op')))
            = ((1 - e) * polyProd (T + e) n) * (T + e - ((n + 1 : ℕ) : ℂ) • (1 : Op')) := by
                rw [mul_assoc]
        _ = ((1 - e) * polyProd T n) * (T + e - ((n + 1 : ℕ) : ℂ) • (1 : Op')) := by
                rw [ih]
        _ = (polyProd T n * (1 - e)) * (T + e - ((n + 1 : ℕ) : ℂ) • (1 : Op')) := by
                rw [hcomm.symm.eq]
        _ = polyProd T n * ((1 - e) * (T + e - ((n + 1 : ℕ) : ℂ) • (1 : Op'))) := by
                rw [mul_assoc]
        _ = polyProd T n * ((1 - e) * (T - ((n + 1 : ℕ) : ℂ) • (1 : Op'))) := by
                rw [hsub]
        _ = (polyProd T n * (1 - e)) * (T - ((n + 1 : ℕ) : ℂ) • (1 : Op')) := by
                rw [← mul_assoc]
        _ = ((1 - e) * polyProd T n) * (T - ((n + 1 : ℕ) : ℂ) • (1 : Op')) := by
                rw [hcomm.eq]
        _ = (1 - e) * (polyProd T n * (T - ((n + 1 : ℕ) : ℂ) • (1 : Op'))) := by
                rw [mul_assoc]

lemma mul_polyProd_add {T e : Op'} (he : e * e = e) (hc : Commute T e) :
    ∀ n : ℕ, e * polyProd (T + e) n = e * polyProd (T + 1) n
  | 0 => by
      simp only [polyProd, mul_add, he, mul_one]
  | n + 1 => by
      have ih := mul_polyProd_add he hc n
      simp only [polyProd]
      have hcomm : Commute (polyProd (T + 1) n) e :=
        commute_polyProd (hc.add_left (Commute.one_left e)) n
      have hsub : e * (T + e - ((n + 1 : ℕ) : ℂ) • (1 : Op')) =
          e * (T + 1 - ((n + 1 : ℕ) : ℂ) • (1 : Op')) := by
        rw [add_sub_right_comm, add_sub_right_comm T 1, mul_add, mul_add, he, mul_one]
      calc
        e * (polyProd (T + e) n * (T + e - ((n + 1 : ℕ) : ℂ) • (1 : Op')))
            = (e * polyProd (T + e) n) * (T + e - ((n + 1 : ℕ) : ℂ) • (1 : Op')) := by
                rw [mul_assoc]
        _ = (e * polyProd (T + 1) n) * (T + e - ((n + 1 : ℕ) : ℂ) • (1 : Op')) := by
                rw [ih]
        _ = (polyProd (T + 1) n * e) * (T + e - ((n + 1 : ℕ) : ℂ) • (1 : Op')) := by
                rw [hcomm.symm.eq]
        _ = polyProd (T + 1) n * (e * (T + e - ((n + 1 : ℕ) : ℂ) • (1 : Op'))) := by
                rw [mul_assoc]
        _ = polyProd (T + 1) n * (e * (T + 1 - ((n + 1 : ℕ) : ℂ) • (1 : Op'))) := by
                rw [hsub]
        _ = (polyProd (T + 1) n * e) * (T + 1 - ((n + 1 : ℕ) : ℂ) • (1 : Op')) := by
                rw [← mul_assoc]
        _ = (e * polyProd (T + 1) n) * (T + 1 - ((n + 1 : ℕ) : ℂ) • (1 : Op')) := by
                rw [hcomm.eq]
        _ = e * (polyProd (T + 1) n * (T + 1 - ((n + 1 : ℕ) : ℂ) • (1 : Op'))) := by
                rw [mul_assoc]

lemma polyProd_add_idempotent {T e : Op'} {n : ℕ}
    (hT : polyProd T n = 0) (he : e * e = e) (hc : Commute T e) :
    polyProd (T + e) (n + 1) = 0 := by
  have h1 : (1 - e) * polyProd (T + e) (n + 1) = 0 := by
    rw [one_sub_mul_polyProd_add he hc (n + 1), polyProd, hT, zero_mul, mul_zero]
  have h2 : e * polyProd (T + e) (n + 1) = 0 := by
    rw [mul_polyProd_add he hc (n + 1), polyProd_add_one T n, hT, mul_zero, mul_zero]
  calc
    polyProd (T + e) (n + 1)
        = (1 - e + e) * polyProd (T + e) (n + 1) := by simp
    _ = (1 - e) * polyProd (T + e) (n + 1) + e * polyProd (T + e) (n + 1) := by rw [add_mul]
    _ = 0 := by rw [h1, h2, add_zero]

lemma polyProd_sum_eq_zero (Q : Fin 5 → Op')
    (hQ_idem : ∀ i, IsIdempotentElem (Q i))
    (hQ_comm : ∀ i j, Commute (Q i) (Q j)) :
    ∀ s : Finset (Fin 5), polyProd (∑ i ∈ s, Q i) s.card = 0 := by
  intro s
  induction s using Finset.induction_on with
  | empty => simp [polyProd]
  | @insert a s has ih =>
      rw [Finset.sum_insert has, Finset.card_insert_of_notMem has, add_comm (Q a)]
      refine polyProd_add_idempotent ih (hQ_idem a).eq ?_
      change (∑ i ∈ s, Q i) * Q a = Q a * ∑ i ∈ s, Q i
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => hQ_comm i a

lemma polyProd_eigenvec (T : Op') (u : H') (c : ℂ) (hu : T u = c • u) :
    ∀ n : ℕ, (polyProd T n) u = (∏ m ∈ Finset.range (n + 1), (c - (m : ℂ))) • u
  | 0 => by simpa [polyProd] using hu
  | n + 1 => by
      have ih := polyProd_eigenvec T u c hu n
      rw [polyProd, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
        sub_apply, smul_apply, one_apply_eq_self, hu, ← sub_smul,
        map_smul, ih, smul_smul, mul_comm (c - _), ← Finset.prod_range_succ]

end OMA.S_mo_286152_Proof

theorem OMA.solution : type_of% @OMA.S_mo_286152.main := by
  refine ⟨OMA.S_mo_286152_Proof.vec OMA.S_mo_286152_Proof.uZ,
    OMA.S_mo_286152_Proof.projOp,
    OMA.S_mo_286152_Proof.u_ne_zero,
    OMA.S_mo_286152_Proof.projOp_isStarProjection,
    ?_, ?_⟩
  · intro i j y hy
    rcases Submodule.mem_span_singleton.mp hy with ⟨c, rfl⟩
    simp only [map_smul, OMA.S_mo_286152_Proof.projOp_comm_u]
  · rintro ⟨Q, hQ_idem, hQ_eq, hQ_comm⟩
    have hu_mem : OMA.S_mo_286152_Proof.vec OMA.S_mo_286152_Proof.uZ ∈
        ℂ ∙ OMA.S_mo_286152_Proof.vec OMA.S_mo_286152_Proof.uZ :=
      Submodule.mem_span_singleton_self _
    have hSum : (∑ i : Fin 5, Q i) (OMA.S_mo_286152_Proof.vec OMA.S_mo_286152_Proof.uZ) =
        (5 / 2 : ℂ) • OMA.S_mo_286152_Proof.vec OMA.S_mo_286152_Proof.uZ := by
      rw [sum_apply]
      simp_rw [hQ_eq _ _ hu_mem]
      exact OMA.S_mo_286152_Proof.sum_projOp_u
    have hZero : OMA.S_mo_286152_Proof.polyProd (∑ i : Fin 5, Q i) 5 = 0 := by
      simpa [Finset.card_fin] using
        OMA.S_mo_286152_Proof.polyProd_sum_eq_zero Q hQ_idem hQ_comm Finset.univ
    have hEval : (OMA.S_mo_286152_Proof.polyProd (∑ i : Fin 5, Q i) 5)
        (OMA.S_mo_286152_Proof.vec OMA.S_mo_286152_Proof.uZ) = 0 := by
      rw [hZero]
      simp
    have hEigen := OMA.S_mo_286152_Proof.polyProd_eigenvec
      (∑ i : Fin 5, Q i)
      (OMA.S_mo_286152_Proof.vec OMA.S_mo_286152_Proof.uZ)
      (5 / 2 : ℂ) hSum 5
    rw [hEval] at hEigen
    have hProd : (∏ m ∈ Finset.range 6, ((5 / 2 : ℂ) - (m : ℂ))) ≠ 0 := by
      rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
        Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_one]
      norm_num
    rcases smul_eq_zero.mp hEigen.symm with hc | hu0
    · exact hProd hc
    · exact OMA.S_mo_286152_Proof.u_ne_zero hu0
