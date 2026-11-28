import OMAStatements.S_mo_396352
import Mathlib

open Matrix OMA.S_mo_396352

namespace PermutationMixing

private theorem squareEntry {n r : ℕ} (p : Fin r → Equiv.Perm (Fin n)) (w : Fin r → ℝ)
    (i j : Fin n) : (mix p w ^ 2) i j =
      ∑ a : Fin r × Fin r, if p a.2 (p a.1 i) = j then w a.1 * w a.2 else 0 := by
  classical
  rw [pow_two, mix, Matrix.sum_mul, Fintype.sum_prod_type]
  simp_rw [Matrix.mul_sum, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [smul_mul_assoc, mul_smul_comm, ← Matrix.permMatrix_mul]
  simp only [Matrix.smul_apply, smul_eq_mul, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Equiv.Perm.mul_apply]
  split_ifs <;> ring

private def images : Fin 4 → Fin 6 → Fin 6 :=
  ![![0, 1, 2, 4, 5, 3], ![3, 4, 5, 1, 2, 0],
    ![2, 0, 1, 5, 3, 4], ![4, 5, 3, 0, 1, 2]]

private noncomputable def permutations (a : Fin 4) : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective (images a) (by fin_cases a <;> decide +kernel)

private def numerators : Fin 4 → ℕ := ![2, 2, 1, 1]

private noncomputable def weights (a : Fin 4) : ℝ := (numerators a : ℝ) / 6

private theorem transitionCounts : ∀ i j : Fin 6,
    (∑ a : Fin 4 × Fin 4, if images a.2 (images a.1 i) = j then
      numerators a.1 * numerators a.2 else 0) = 6 := by decide +kernel

private theorem fourPermutations :
    ∃ (p : Fin 4 → Equiv.Perm (Fin 6)) (w : Fin 4 → ℝ), Function.Injective p ∧
      (∀ i, 0 < w i) ∧ (∑ i, w i) = 1 ∧ (mix p w) ^ 2 = uniform 6 := by
  refine ⟨permutations, weights, ?_, ?_, ?_, ?_⟩
  · intro a b h
    have h0 := congrArg (fun q : Equiv.Perm (Fin 6) => q 0) h
    change images a 0 = images b 0 at h0
    exact (show Function.Injective (fun i : Fin 4 => images i 0) from by decide +kernel) h0
  · intro i
    fin_cases i <;> norm_num [weights, numerators]
  · norm_num [Fin.sum_univ_succ, weights, numerators]
  · ext i j
    rw [squareEntry]
    change (∑ a : Fin 4 × Fin 4, if images a.2 (images a.1 i) = j then
      weights a.1 * weights a.2 else 0) = (6 : ℝ)⁻¹
    calc
      _ = (∑ a : Fin 4 × Fin 4, ((if images a.2 (images a.1 i) = j then
            numerators a.1 * numerators a.2 else 0 : ℕ) : ℝ)) / 36 := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro a _
          unfold weights
          split_ifs <;> push_cast <;> ring
      _ = _ := by rw [← Nat.cast_sum, transitionCounts]; norm_num

private theorem thirdLabel : ∀ u v : Fin 3, u ≠ v →
    ∃ z : Fin 3, z ≠ u ∧ z ≠ v ∧ ∀ a : Fin 3, a = u ∨ a = v ∨ a = z :=
  by decide +kernel

private theorem equalBinsImpossible (w : Fin 3 → ℝ) (hw : ∀ a, 0 ≤ w a)
    (htotal : ∑ a, w a = 1) (e : Fin 3 × Fin 3 → Fin 6)
    (he : ∀ j, (∑ a : Fin 3 × Fin 3, if e a = j then w a.1 * w a.2 else 0) = 1 / 6) :
    False := by
  classical
  let fiber (j : Fin 6) := Finset.univ.filter fun a : Fin 3 × Fin 3 => e a = j
  have hsum (j : Fin 6) : (∑ a ∈ fiber j, w a.1 * w a.2) = 1 / 6 := by
    simpa only [fiber, Finset.sum_filter] using he j
  have hbound (a : Fin 3 × Fin 3) : w a.1 * w a.2 ≤ 1 / 6 := by
    rw [← hsum (e a)]
    exact Finset.single_le_sum (f := fun b : Fin 3 × Fin 3 => w b.1 * w b.2)
      (fun b _ => mul_nonneg (hw b.1) (hw b.2)) (by simp [fiber])
  let t := Real.sqrt (1 / 6)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = 1 / 6 := Real.sq_sqrt (by norm_num)
  have hwt (a : Fin 3) : w a ≤ t := by
    apply (sq_le_sq₀ (hw a) ht0).mp
    rw [ht2, pow_two]
    exact hbound (a, a)
  have htlo : (7 / 18 : ℝ) < t := (sq_lt_sq₀ (by norm_num) ht0).mp (by rw [ht2]; norm_num)
  have hthi : t < (5 / 12 : ℝ) := (sq_lt_sq₀ ht0 (by norm_num)).mp (by rw [ht2]; norm_num)
  have hprod (a b : Fin 3) (h : w a * w b = 1 / 6) : w a = t ∧ w b = t := by
    have aux (x y : Fin 3) (hxy : w x * w y = 1 / 6) : w x = t := by
      by_contra hne
      have hlt := lt_of_le_of_ne (hwt x) hne
      have hmul := mul_lt_mul_of_pos_right hlt (show 0 < t by linarith only [htlo])
      have hle := mul_le_mul_of_nonneg_left (hwt y) (hw x)
      rw [← pow_two, ht2] at hmul
      linarith only [hxy, hle, hmul]
    exact ⟨aux a b h, aux b a (by rwa [mul_comm])⟩
  have hnonempty (j) : 1 ≤ (fiber j).card := by
    by_contra! hj
    have hemp : fiber j = ∅ := Finset.card_eq_zero.mp (by omega)
    simpa [hemp] using hsum j
  have hcount : (∑ j : Fin 6, (fiber j).card) = 9 := by
    symm
    simpa [fiber] using (Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ) (t := (Finset.univ : Finset (Fin 6))) (f := e) (by simp))
  have hone : ∃ j, (fiber j).card = 1 := by
    by_contra! hn
    have htwo (j) : 2 ≤ (fiber j).card := by have := hn j; have := hnonempty j; omega
    have hge := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 6))) (fun j _ => htwo j)
    norm_num at hge
    omega
  obtain ⟨j, hj⟩ := hone
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hj
  have hwa : w a.1 = t := (hprod a.1 a.2 (by simpa [ha] using hsum j)).1
  have hother : ∃ v, v ≠ a.1 ∧ w v = t := by
    by_contra! hn
    let j0 := e (a.1, a.1)
    have guarded (k) (hk : k ≠ j0) : 2 ≤ (fiber k).card := by
      by_contra! hlt
      obtain ⟨b, hb⟩ := Finset.card_eq_one.mp (by have := hnonempty k; omega : (fiber k).card = 1)
      have hbws := hprod b.1 b.2 (by simpa [hb] using hsum k)
      have hba : b = (a.1, a.1) := Prod.ext (by by_contra h; exact hn _ h hbws.1)
        (by by_contra h; exact hn _ h hbws.2)
      have hm : b ∈ fiber k := by simp [hb]
      apply hk
      simpa [fiber, hba, j0, eq_comm] using hm
    have h5 := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 6)).erase j0)
      (fun k hk => guarded k (Finset.ne_of_mem_erase hk))
    have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin 6)))
      (f := fun j => (fiber j).card) (Finset.mem_univ j0)
    norm_num at h5
    rw [hcount] at hsplit
    have := hnonempty j0
    omega
  obtain ⟨v, hva, hv⟩ := hother
  let u := a.1
  have huv : u ≠ v := Ne.symm hva
  obtain ⟨z, hzu, hzv, hlabels⟩ := thirdLabel u v huv
  have hu : w u = t := hwa
  have hall : (Finset.univ : Finset (Fin 3)) = {u, v, z} := by
    ext r
    simpa using hlabels r
  have hz : w z = 1 - 2 * t := by
    rw [hall] at htotal
    simp [huv, hzu.symm, hzv.symm, hu, hv] at htotal
    linarith only [htotal]
  let top : Finset (Fin 3) := {u, v}
  let high := top.product top
  have hhigh : high.card = 4 := by simp [high, top, huv]
  let excluded := insert (e (z, z)) (high.image e)
  have helim : excluded.card < (Finset.univ : Finset (Fin 6)).card := by
    have hs := Finset.card_insert_le (s := high.image e) (a := e (z, z))
    have hi := Finset.card_image_le (s := high) (f := e)
    simp only [Finset.card_univ, Fintype.card_fin]
    dsimp [excluded]
    omega
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card helim
  have htop (x : Fin 3) (hx : x ≠ z) : x ∈ top := by
    rcases hlabels x with h | h | h
    · simp [top, h]
    · simp [top, h]
    · exact (hx h).elim
  have htopval (x : Fin 3) (hx : x ≠ z) : w x = t := by
    have hm := htop x hx
    rcases (show x = u ∨ x = v by simpa [top] using hm) with h | h
    · simpa [h] using hu
    · simpa [h] using hv
  have hmix (b : Fin 3 × Fin 3) (hb : b ∈ fiber k) : w b.1 * w b.2 = t * w z := by
    have heq : e b = k := by simpa [fiber] using hb
    have hnothigh : b ∉ high := by
      intro h
      exact hk (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨b, h, heq⟩))
    have hnotlow : b ≠ (z, z) := by
      intro h
      apply hk
      rw [← heq, h]
      exact Finset.mem_insert_self _ _
    rcases b with ⟨b₁, b₂⟩
    by_cases h₁ : b₁ = z
    · have h₂ : b₂ ≠ z := by intro h; exact hnotlow (Prod.ext h₁ h)
      change w b₁ * w b₂ = _
      rw [h₁, htopval b₂ h₂, mul_comm]
    · have h₂ : b₂ = z := by
        by_contra h
        exact hnothigh (Finset.mem_product.mpr ⟨htop b₁ h₁, htop b₂ h⟩)
      change w b₁ * w b₂ = _
      rw [h₂, htopval b₁ h₁]
  have hmass : ((fiber k).card : ℝ) * (t * w z) = 1 / 6 := by
    rw [← hsum k, ← nsmul_eq_mul]
    exact (Finset.sum_const (b := t * w z)).symm.trans (Finset.sum_congr rfl fun b hb => (hmix b hb).symm)
  have hform : t * w z = t - 1 / 3 := by rw [hz]; nlinarith only [ht2]
  have hpos : 0 ≤ t * w z := mul_nonneg ht0 (hw z)
  by_cases hsmall : (fiber k).card ≤ 2
  · have hle := mul_le_mul_of_nonneg_right (by exact_mod_cast hsmall : ((fiber k).card : ℝ) ≤ 2) hpos
    linarith only [hmass, hform, hthi, hle]
  · have hlarge : 3 ≤ (fiber k).card := by omega
    have hle := mul_le_mul_of_nonneg_right (by exact_mod_cast hlarge : (3 : ℝ) ≤ (fiber k).card) hpos
    linarith only [hmass, hform, htlo, hle]

private theorem threePermutations (p : Fin 3 → Equiv.Perm (Fin 6)) (w : Fin 3 → ℝ)
    (hw : ∀ i, 0 ≤ w i) (ht : ∑ i, w i = 1) : (mix p w) ^ 2 ≠ uniform 6 := by
  intro h
  apply equalBinsImpossible w hw ht (fun a => p a.2 (p a.1 0))
  intro j
  rw [← squareEntry p w 0 j, h]
  norm_num [uniform]


theorem twoPermutation {n k : ℕ} (hn : 2 ≤ n) (p q : Equiv.Perm (Fin n)) (a : ℝ)
    (hm : (a • p.permMatrix ℝ + (1 - a) • q.permMatrix ℝ) ^ k = uniform n) :
    a = 1 / 2 ∧ n ∣ 2 ^ k := by
  classical
  let A : Mat n := a • p.permMatrix ℝ + (1 - a) • q.permMatrix ℝ
  change A ^ k = uniform n at hm
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have hval := congrArg Fin.val h
    simp [i, j] at hval
  have hu : (uniform n).det = 0 :=
    Matrix.det_zero_of_row_eq hij (by rfl)
  have hpow : A.det ^ k = 0 := by
    rw [← Matrix.det_pow, hm, hu]
  have hdet : A.det = 0 := by
    by_contra h
    exact (pow_ne_zero k h) hpow
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hsumzero : a • (v ∘ p) + (1 - a) • (v ∘ q) = 0 := by
    simpa only [A, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.permMatrix_mulVec] using hAv
  let S : ℝ := ∑ l : Fin n, (v l) ^ 2
  obtain ⟨l, hl⟩ : ∃ l, v l ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  have hterm : (v l) ^ 2 ≤ S :=
    Finset.single_le_sum (f := fun r => (v r) ^ 2)
      (fun r _ => sq_nonneg (v r)) (Finset.mem_univ l)
  have hS : S ≠ 0 := ne_of_gt (lt_of_lt_of_le (sq_pos_of_ne_zero hl) hterm)
  have hp : (∑ l : Fin n, (v (p l)) ^ 2) = S :=
    Equiv.sum_comp p (fun l => (v l) ^ 2)
  have hq : (∑ l : Fin n, (v (q l)) ^ 2) = S :=
    Equiv.sum_comp q (fun l => (v l) ^ 2)
  have hterms : (∑ l : Fin n, a ^ 2 * (v (p l)) ^ 2) =
      ∑ l : Fin n, (1 - a) ^ 2 * (v (q l)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro r _
    have hr : a * v (p r) + (1 - a) * v (q r) = 0 := congrFun hsumzero r
    have hn : a * v (p r) = -((1 - a) * v (q r)) := by linarith only [hr]
    calc
      _ = (a * v (p r)) ^ 2 := by ring
      _ = ((1 - a) * v (q r)) ^ 2 := by rw [hn]; ring
      _ = _ := by ring
  have hSprod : a ^ 2 * S = (1 - a) ^ 2 * S := by
    simpa only [← Finset.mul_sum, hp, hq] using hterms
  have hweights : a ^ 2 = (1 - a) ^ 2 := mul_right_cancel₀ hS hSprod
  have ha : a = 1 / 2 := by nlinarith only [hweights]
  let B : Matrix (Fin n) (Fin n) ℕ := p.permMatrix ℕ + q.permMatrix ℕ
  have hdouble : B.map (Nat.castRingHom ℝ) = (2 : ℝ) • A := by
    ext x y
    change (((p.permMatrix ℕ x y + q.permMatrix ℕ x y : ℕ) : ℝ)) =
      2 * (a * p.permMatrix ℝ x y + (1 - a) * q.permMatrix ℝ x y)
    rw [Nat.cast_add, ha]
    simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
      Option.mem_def, Option.some.injEq]
    by_cases hpMem : p x = y <;> by_cases hqMem : q x = y <;>
      norm_num [hpMem, hqMem]
  have hscaled : (B ^ k).map (Nat.castRingHom ℝ) = (2 : ℝ) ^ k • uniform n := by
    rw [Matrix.map_pow, hdouble, smul_pow, hm]
  have hentry : (((B ^ k) i i : ℕ) : ℝ) = (2 : ℝ) ^ k * (n : ℝ)⁻¹ :=
    congrArg (fun M : Mat n => M i i) hscaled
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hmultiple : (2 : ℕ) ^ k = n * (B ^ k) i i := by
    exact_mod_cast
      (calc
        (2 : ℝ) ^ k = (((B ^ k) i i : ℕ) : ℝ) * (n : ℝ) :=
          ((eq_mul_inv_iff_mul_eq₀ hnR).mp hentry).symm
        _ = (n : ℝ) * (((B ^ k) i i : ℕ) : ℝ) := mul_comm _ _)
  exact ⟨ha, (B ^ k) i i, hmultiple⟩


end PermutationMixing

theorem OMA.solution : type_of% @OMA.S_mo_396352.main := by
  refine ⟨PermutationMixing.fourPermutations, PermutationMixing.threePermutations, ?_⟩
  intro n k hn _ p q a _ _ hp
  exact PermutationMixing.twoPermutation hn p q a hp