-- Credit: Daniel Whorlow (@draonbioetl)
import OMAStatements.S_arxiv_2602_22129

namespace OMA_A2602_Full

open scoped Classical Polynomial BigOperators Matrix
open Polynomial BigOperators

section Mobius

variable {F : Type*} [Field F]

noncomputable def polyFromCoeffs (m : ℕ) (c : Fin m → F) : F[X] :=
  X ^ m + ∑ i : Fin m, C (c i) * X ^ i.val

lemma coeff_polyFromCoeffs_lt (m : ℕ) (c : Fin m → F) {k : ℕ} (hk : k < m) :
    (polyFromCoeffs m c).coeff k = c ⟨k, hk⟩ := by
  unfold polyFromCoeffs
  rw [coeff_add, coeff_X_pow, if_neg (Nat.ne_of_lt hk), zero_add, finsetSum_coeff]
  rw [Finset.sum_eq_single ⟨k, hk⟩]
  · simp [coeff_C_mul, coeff_X_pow]
  · intro i _ hi
    have hne : k ≠ i.val := fun h => hi (Fin.ext h.symm)
    simp [coeff_C_mul, coeff_X_pow, hne]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma coeff_polyFromCoeffs_eq (m : ℕ) (c : Fin m → F) :
    (polyFromCoeffs m c).coeff m = 1 := by
  unfold polyFromCoeffs
  rw [coeff_add, coeff_X_pow, if_pos rfl, finsetSum_coeff]
  have h0 : ∑ i : Fin m, (C (c i) * X ^ i.val).coeff m = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hne : m ≠ i.val := Nat.ne_of_gt i.isLt
    simp [coeff_C_mul, coeff_X_pow, hne]
  rw [h0, add_zero]

lemma coeff_polyFromCoeffs_gt (m : ℕ) (c : Fin m → F) {k : ℕ} (hk : m < k) :
    (polyFromCoeffs m c).coeff k = 0 := by
  unfold polyFromCoeffs
  rw [coeff_add, coeff_X_pow, if_neg (Nat.ne_of_gt hk), zero_add, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i _
  have hne : k ≠ i.val := Nat.ne_of_gt (lt_trans i.isLt hk)
  simp [coeff_C_mul, coeff_X_pow, hne]

lemma natDegree_polyFromCoeffs (m : ℕ) (c : Fin m → F) :
    (polyFromCoeffs m c).natDegree = m := by
  apply le_antisymm
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    exact coeff_polyFromCoeffs_gt m c hk
  · apply le_natDegree_of_ne_zero
    rw [coeff_polyFromCoeffs_eq]
    exact one_ne_zero

lemma monic_polyFromCoeffs (m : ℕ) (c : Fin m → F) :
    (polyFromCoeffs m c).Monic := by
  rw [Monic, leadingCoeff, natDegree_polyFromCoeffs, coeff_polyFromCoeffs_eq]

lemma polyFromCoeffs_injective (m : ℕ) :
    Function.Injective (polyFromCoeffs (F := F) m) := by
  intro c1 c2 h
  funext i
  have h1 := coeff_polyFromCoeffs_lt m c1 i.isLt
  have h2 := coeff_polyFromCoeffs_lt m c2 i.isLt
  rw [h] at h1
  exact h1.symm.trans h2

lemma eq_polyFromCoeffs_of_monic {g : F[X]} {m : ℕ} (hm : g.Monic) (hd : g.natDegree = m) :
    g = polyFromCoeffs m (fun i => g.coeff i.val) := by
  ext k
  rcases lt_trichotomy k m with hk | rfl | hk
  · rw [coeff_polyFromCoeffs_lt m _ hk]
  · rw [coeff_polyFromCoeffs_eq, ← hd]; exact hm.leadingCoeff
  · rw [coeff_polyFromCoeffs_gt m _ hk]
    exact coeff_eq_zero_of_natDegree_lt (hd ▸ hk)

variable [Fintype F]

noncomputable def monicDeg (m : ℕ) : Finset F[X] :=
  Finset.univ.image (polyFromCoeffs (F := F) m)

lemma mem_monicDeg {m : ℕ} {g : F[X]} :
    g ∈ monicDeg (F := F) m ↔ g.Monic ∧ g.natDegree = m := by
  unfold monicDeg
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨monic_polyFromCoeffs m c, natDegree_polyFromCoeffs m c⟩
  · rintro ⟨hm, hd⟩
    exact ⟨fun i => g.coeff i.val, (eq_polyFromCoeffs_of_monic hm hd).symm⟩

lemma card_monicDeg (m : ℕ) : (monicDeg (F := F) m).card = Fintype.card F ^ m := by
  unfold monicDeg
  rw [Finset.card_image_of_injective _ (polyFromCoeffs_injective m)]
  simp [Fintype.card_pi]

lemma monicDeg_zero : monicDeg (F := F) 0 = {1} := by
  ext g
  rw [mem_monicDeg, Finset.mem_singleton]
  constructor
  · rintro ⟨hm, hd⟩
    exact Polynomial.eq_one_of_monic_natDegree_zero hm hd
  · rintro rfl
    exact ⟨monic_one, natDegree_one⟩

noncomputable def monicDivisors (H : F[X]) : Finset F[X] :=
  (Finset.range (H.natDegree + 1)).biUnion (fun m => (monicDeg (F := F) m).filter (· ∣ H))

lemma mem_monicDivisors {H g : F[X]} (hH : H ≠ 0) :
    g ∈ monicDivisors H ↔ g.Monic ∧ g ∣ H := by
  unfold monicDivisors
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, mem_monicDeg]
  constructor
  · rintro ⟨m, _, ⟨hm, _⟩, hdvd⟩
    exact ⟨hm, hdvd⟩
  · rintro ⟨hm, hdvd⟩
    refine ⟨g.natDegree, Nat.lt_succ_of_le (Polynomial.natDegree_le_of_dvd hdvd hH), ⟨hm, rfl⟩, hdvd⟩

noncomputable def mobiusAux : ℕ → F[X] → ℤ
  | 0, _ => 1
  | n + 1, H =>
    if H.natDegree ≤ n then mobiusAux n H
    else - ∑ g ∈ (Finset.range (n + 1)).biUnion (fun m => (monicDeg (F := F) m).filter (· ∣ H)),
      mobiusAux n g

lemma mobiusAux_eq_of_le : ∀ (n : ℕ) (H : F[X]), H.natDegree ≤ n →
    mobiusAux n H = mobiusAux H.natDegree H
  | 0, H, h => by
    have h0 : H.natDegree = 0 := Nat.le_zero.mp h
    rw [h0]
  | n + 1, H, h => by
    rcases Nat.eq_or_lt_of_le h with heq | hlt
    · rw [heq]
    · have hle : H.natDegree ≤ n := Nat.lt_succ_iff.mp hlt
      simp only [mobiusAux, hle, ↓reduceIte]
      exact mobiusAux_eq_of_le n H hle

noncomputable def mobius (H : F[X]) : ℤ := mobiusAux H.natDegree H

lemma mobius_one : mobius (1 : F[X]) = 1 := by
  simp [mobius, mobiusAux]

lemma sum_mobius_monicDivisors {H : F[X]} (hH : H.Monic) :
    ∑ g ∈ monicDivisors H, mobius g = if H = 1 then 1 else 0 := by
  by_cases h1 : H = 1
  · subst h1
    have hset : monicDivisors (1 : F[X]) = {1} := by
      ext g
      rw [mem_monicDivisors one_ne_zero, Finset.mem_singleton]
      constructor
      · rintro ⟨hm, hdvd⟩
        have hle := Polynomial.natDegree_le_of_dvd hdvd one_ne_zero
        rw [natDegree_one] at hle
        exact Polynomial.eq_one_of_monic_natDegree_zero hm (Nat.le_zero.mp hle)
      · rintro rfl; exact ⟨monic_one, dvd_refl 1⟩
    rw [hset, Finset.sum_singleton, mobius_one, if_pos rfl]
  · rw [if_neg h1]
    have hd_pos : 0 < H.natDegree := by
      by_contra h0
      have hd0 : H.natDegree = 0 := Nat.eq_zero_of_not_pos h0
      exact h1 (Polynomial.eq_one_of_monic_natDegree_zero hH hd0)
    obtain ⟨n, hn⟩ : ∃ n, H.natDegree = n + 1 := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd_pos)
    have hmemH : H ∈ monicDivisors H := (mem_monicDivisors hH.ne_zero).mpr ⟨hH, dvd_refl H⟩
    rw [← Finset.add_sum_erase _ _ hmemH]
    have herase : (monicDivisors H).erase H =
        (Finset.range (n + 1)).biUnion (fun m => (monicDeg (F := F) m).filter (· ∣ H)) := by
      ext g
      simp only [Finset.mem_erase, mem_monicDivisors hH.ne_zero, Finset.mem_biUnion,
        Finset.mem_range, Finset.mem_filter, mem_monicDeg]
      constructor
      · rintro ⟨hne, hm, hdvd⟩
        have hle := Polynomial.natDegree_le_of_dvd hdvd hH.ne_zero
        have hlt : g.natDegree < n + 1 := by
          rw [← hn]
          apply lt_of_le_of_ne hle
          intro heq
          obtain ⟨q, hq⟩ := hdvd
          have hq0 : q ≠ 0 := by rintro rfl; simp at hq; exact hH.ne_zero hq
          have hdegq : q.natDegree = 0 := by
            have hsum := Polynomial.natDegree_mul hm.ne_zero hq0
            rw [← hq, heq] at hsum; omega
          have hqm : q.Monic := by
            have := congr_arg Polynomial.leadingCoeff hq
            rw [Polynomial.leadingCoeff_mul, hH.leadingCoeff, hm.leadingCoeff, one_mul] at this
            exact this.symm
          have hq1 := Polynomial.eq_one_of_monic_natDegree_zero hqm hdegq
          rw [hq1, mul_one] at hq
          exact hne hq.symm
        exact ⟨g.natDegree, hlt, ⟨hm, rfl⟩, hdvd⟩
      · rintro ⟨m, hm_lt, ⟨hgm, hgd⟩, hdvd⟩
        refine ⟨?_, hgm, hdvd⟩
        rintro rfl; omega
    rw [herase]
    have hmob : mobius H = - ∑ g ∈ (Finset.range (n + 1)).biUnion
        (fun m => (monicDeg (F := F) m).filter (· ∣ H)), mobius g := by
      unfold mobius
      rw [hn]
      simp only [mobiusAux, hn, show ¬ (n + 1 ≤ n) by omega, ↓reduceIte]
      congr 1
      apply Finset.sum_congr rfl
      intro g hg
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, mem_monicDeg] at hg
      rcases hg with ⟨m, hm_lt, ⟨_, hgd⟩, _⟩
      exact mobiusAux_eq_of_le n g (by omega)
    rw [hmob, neg_add_cancel]

lemma sum_mobius_weighted_eq (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1),
      ((Fintype.card F : ℤ) ^ (n - m)) * (∑ g ∈ monicDeg (F := F) m, mobius g) =
      if n = 0 then 1 else 0 := by
  -- Evaluate ∑_{H ∈ monicDeg n} ∑_{g ∈ monicDivisors H} mobius g in two ways
  have hLHS : ∑ H ∈ monicDeg (F := F) n, ∑ g ∈ monicDivisors H, mobius g =
      if n = 0 then 1 else 0 := by
    by_cases hn0 : n = 0
    · subst hn0
      rw [monicDeg_zero, Finset.sum_singleton, sum_mobius_monicDivisors monic_one, if_pos rfl,
        if_pos rfl]
    · rw [if_neg hn0]
      apply Finset.sum_eq_zero
      intro H hH
      have ⟨hHm, hHd⟩ := mem_monicDeg.mp hH
      rw [sum_mobius_monicDivisors hHm, if_neg]
      rintro rfl; simp at hHd; exact hn0 hHd.symm
  rw [← hLHS]
  -- Swap sums: ∑_{H ∈ monicDeg n} ∑_{m ≤ n} ∑_{g ∈ monicDeg m, g ∣ H} mobius g
  have hstep1 : ∀ H ∈ monicDeg (F := F) n,
      ∑ g ∈ monicDivisors H, mobius g =
      ∑ m ∈ Finset.range (n + 1), ∑ g ∈ (monicDeg (F := F) m).filter (· ∣ H), mobius g := by
    intro H hH
    have ⟨_, hHd⟩ := mem_monicDeg.mp hH
    unfold monicDivisors
    rw [hHd, Finset.sum_biUnion]
    intro m1 _ m2 _ hne
    exact Finset.disjoint_left.mpr fun g hg1 hg2 => by
      simp only [Finset.mem_filter, mem_monicDeg] at hg1 hg2
      exact hne (hg1.1.2.symm.trans hg2.1.2)
  rw [Finset.sum_congr rfl hstep1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  -- Now swap ∑_{H ∈ monicDeg n} ∑_{g ∈ (monicDeg m).filter (· ∣ H)} mobius g
  have hswap : ∑ H ∈ monicDeg (F := F) n, ∑ g ∈ (monicDeg (F := F) m).filter (· ∣ H), mobius g =
      ∑ g ∈ monicDeg (F := F) m, ∑ H ∈ (monicDeg (F := F) n).filter (g ∣ ·), mobius g := by
    simp only [Finset.sum_filter]
    exact Finset.sum_comm
  rw [hswap, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g hg
  have ⟨hgm, hgd⟩ := mem_monicDeg.mp hg
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 1
  -- Count H ∈ monicDeg n with g ∣ H: bijection with Q ∈ monicDeg (n - m) via Q ↦ g * Q
  have hbij : (monicDeg (F := F) n).filter (g ∣ ·) =
      (monicDeg (F := F) (n - m)).image (g * ·) := by
    ext H
    simp only [Finset.mem_filter, Finset.mem_image, mem_monicDeg]
    constructor
    · rintro ⟨⟨hHm, hHd⟩, ⟨Q, hQ⟩⟩
      have hQ0 : Q ≠ 0 := by rintro rfl; simp at hQ; exact hHm.ne_zero hQ
      have hQm : Q.Monic := by
        have := congr_arg Polynomial.leadingCoeff hQ
        rw [Polynomial.leadingCoeff_mul, hHm.leadingCoeff, hgm.leadingCoeff, one_mul] at this
        exact this.symm
      have hQd : Q.natDegree = n - m := by
        have hmul := Polynomial.natDegree_mul hgm.ne_zero hQ0
        rw [← hQ, hHd, hgd] at hmul; omega
      exact ⟨Q, ⟨hQm, hQd⟩, hQ.symm⟩
    · rintro ⟨Q, ⟨hQm, hQd⟩, rfl⟩
      refine ⟨⟨hgm.mul hQm, ?_⟩, dvd_mul_right g Q⟩
      rw [Polynomial.natDegree_mul hgm.ne_zero hQm.ne_zero, hgd, hQd]; omega
  rw [hbij, Finset.card_image_of_injective _ (mul_right_injective₀ hgm.ne_zero), card_monicDeg]
  norm_cast

lemma sum_mobius_monicDeg (m : ℕ) :
    ∑ g ∈ monicDeg (F := F) m, mobius g =
      if m = 0 then 1 else if m = 1 then -(Fintype.card F : ℤ) else 0 := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    have h := sum_mobius_weighted_eq (F := F) m
    rcases m with _ | m'
    · simp at h; simpa using h
    · rcases m' with _ | m''
      · rw [Finset.sum_range_succ, Finset.sum_range_one] at h
        simp only [zero_add, Nat.sub_zero, pow_one, Nat.sub_self, pow_zero, one_mul, one_ne_zero,
          ↓reduceIte] at h
        have h0 := ih 0 (by omega)
        simp only [↓reduceIte] at h0
        rw [h0, mul_one] at h
        simp only [one_ne_zero, ↓reduceIte, zero_add]
        linarith
      · set n := m'' + 2
        have h0 := ih 0 (by omega)
        have h1 := ih 1 (by omega)
        simp only [↓reduceIte, show (1 : ℕ) ≠ 0 by omega] at h0 h1
        rw [Finset.sum_range_succ] at h
        simp only [Nat.sub_self, pow_zero, one_mul, show n ≠ 0 by omega, ↓reduceIte] at h
        have hsplit : ∑ k ∈ Finset.range n,
            ((Fintype.card F : ℤ) ^ (n - k)) * (∑ g ∈ monicDeg (F := F) k, mobius g) = 0 := by
          have hge2 : 2 ≤ n := by omega
          rw [show n = (n - 2) + 2 by omega]
          have h01 : ∀ k ∈ Finset.range ((n - 2) + 2),
              ((Fintype.card F : ℤ) ^ (((n - 2) + 2) - k)) *
                (∑ g ∈ monicDeg (F := F) k, mobius g) =
              if k = 0 then (Fintype.card F : ℤ) ^ ((n - 2) + 2)
              else if k = 1 then -(Fintype.card F : ℤ) ^ ((n - 2) + 2)
              else 0 := by
            intro k hk
            have hkn : k < n := by
              rw [Finset.mem_range] at hk; omega
            rw [ih k hkn]
            by_cases hk0 : k = 0
            · subst hk0; simp
            · by_cases hk1 : k = 1
              · subst hk1
                simp only [hk0, ↓reduceIte]
                have hexp : (n - 2) + 2 - 1 + 1 = (n - 2) + 2 := by omega
                rw [mul_neg, ← pow_succ, hexp]
              · simp [hk0, hk1]
          rw [Finset.sum_congr rfl h01]
          have hmem0 : (0 : ℕ) ∈ Finset.range ((n - 2) + 2) := Finset.mem_range.mpr (by omega)
          have hmem1 : (1 : ℕ) ∈ (Finset.range ((n - 2) + 2)).erase 0 := by
            simp [Finset.mem_erase, Finset.mem_range]
          rw [← Finset.add_sum_erase _ _ hmem0, ← Finset.add_sum_erase _ _ hmem1]
          simp only [↓reduceIte, show (1 : ℕ) ≠ 0 by omega]
          have hrest : ∑ x ∈ ((Finset.range ((n - 2) + 2)).erase 0).erase 1,
              (if x = 0 then (Fintype.card F : ℤ) ^ ((n - 2) + 2)
               else if x = 1 then -(Fintype.card F : ℤ) ^ ((n - 2) + 2)
               else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro x hx
            simp only [Finset.mem_erase] at hx
            simp [hx.1, hx.2.1]
          rw [hrest]; ring
        rw [hsplit, zero_add] at h
        simp only [show n ≠ 0 by omega, show n ≠ 1 by omega, ↓reduceIte]
        exact h

-- Now: counting coprime affine tuples in ∏ s : Fin r, degreeLT F (d s + 1)!

def IsCoprimeTuple {r : ℕ} (P : Fin r → F[X]) : Prop :=
  ∀ g : F[X], g.Monic → (∀ s, g ∣ P s) → g = 1

noncomputable def monicGcd {r : ℕ} (P : Fin r → F[X]) : F[X] :=
  C (Finset.univ.gcd P).leadingCoeff⁻¹ * Finset.univ.gcd P

lemma monicGcd_spec {r : ℕ} {P : Fin r → F[X]} (hne : ∃ s, P s ≠ 0) :
    (monicGcd P).Monic ∧ (∀ g : F[X], g ∣ monicGcd P ↔ ∀ s, g ∣ P s) := by
  have hgcd_ne : Finset.univ.gcd P ≠ 0 := by
    intro h0
    rcases hne with ⟨s, hs⟩
    have hdvd : Finset.univ.gcd P ∣ P s := Finset.gcd_dvd (Finset.mem_univ s)
    rw [h0, zero_dvd_iff] at hdvd
    exact hs hdvd
  have hlc : (Finset.univ.gcd P).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hgcd_ne
  refine ⟨?_, ?_⟩
  · unfold monicGcd
    rw [Monic, leadingCoeff_mul, leadingCoeff_C, inv_mul_cancel₀ hlc]
  · intro g
    unfold monicGcd
    have hu : IsUnit (C (Finset.univ.gcd P).leadingCoeff⁻¹) :=
      (isUnit_C.mpr (inv_ne_zero hlc).isUnit)
    rw [hu.dvd_mul_left, Finset.dvd_gcd_iff]
    simp

lemma isCoprimeTuple_iff_monicGcd_eq_one {r : ℕ} {P : Fin r → F[X]} (hne : ∃ s, P s ≠ 0) :
    IsCoprimeTuple P ↔ monicGcd P = 1 := by
  have ⟨hm, hdvd⟩ := monicGcd_spec hne
  constructor
  · intro hc
    exact hc (monicGcd P) hm ((hdvd (monicGcd P)).mp (dvd_refl _))
  · intro h1 g hgm hg
    have hg1 : g ∣ 1 := h1 ▸ (hdvd g).mpr hg
    have hle := Polynomial.natDegree_le_of_dvd hg1 one_ne_zero
    rw [natDegree_one] at hle
    exact Polynomial.eq_one_of_monic_natDegree_zero hgm (Nat.le_zero.mp hle)

-- Single-coordinate count: #{r ∈ degreeLT F (d + 1) | g ∣ C α * X^(d + 1) + r}
lemma card_dvd_affine_single (d : ℕ) (α : F) {g : F[X]} {m : ℕ}
    (hgm : g.Monic) (hgd : g.natDegree = m) :
    letI : Fintype (degreeLT F (d + 1)) := Fintype.ofEquiv (Fin (d + 1) → F) (degreeLTEquiv F (d + 1)).symm.toEquiv
    (Finset.univ.filter (fun r : degreeLT F (d + 1) => g ∣ C α * X ^ (d + 1) + r.val)).card =
      if m ≤ d + 1 then Fintype.card F ^ (d + 1 - m)
      else if α = 0 then 1 else 0 := by
  letI : Fintype (degreeLT F (d + 1)) := Fintype.ofEquiv (Fin (d + 1) → F) (degreeLTEquiv F (d + 1)).symm.toEquiv
  by_cases hmd : m ≤ d + 1
  · rw [if_pos hmd]
    -- Bijection between degreeLT F (d + 1 - m) and the filtered finset!
    letI : Fintype (degreeLT F (d + 1 - m)) :=
      Fintype.ofEquiv (Fin (d + 1 - m) → F) (degreeLTEquiv F (d + 1 - m)).symm.toEquiv
    have hdeg_lt : ∀ q : degreeLT F (d + 1 - m),
        g * (C α * X ^ (d + 1 - m) + q.val) - C α * X ^ (d + 1) ∈ degreeLT F (d + 1) := by
      intro q
      rw [mem_degreeLT]
      have hsub : g * (C α * X ^ (d + 1 - m) + q.val) - C α * X ^ (d + 1) =
          (g - X ^ m) * (C α * X ^ (d + 1 - m)) + g * q.val := by
        have hpow : X ^ m * (C α * X ^ (d + 1 - m)) = C α * X ^ (d + 1) := by
          rw [mul_left_comm, ← pow_add, show m + (d + 1 - m) = d + 1 by omega]
        rw [mul_add, sub_mul, hpow]; ring
      rw [hsub]
      apply lt_of_le_of_lt (degree_add_le _ _)
      rw [max_lt_iff]
      constructor
      · by_cases hgx : g - X ^ m = 0
        · simp [hgx]
        · by_cases hα : α = 0
          · simp [hα]
          · have hlt_g : (g - X ^ m).degree < (m : WithBot ℕ) := by
              rw [degree_lt_iff_coeff_zero]
              intro k hk
              rw [coeff_sub, coeff_X_pow]
              rcases eq_or_lt_of_le hk with rfl | hgt
              · rw [if_pos rfl, ← hgd, ← leadingCoeff, hgm.leadingCoeff, sub_self]
              · rw [if_neg (Nat.ne_of_gt hgt), coeff_eq_zero_of_natDegree_lt (hgd ▸ hgt), sub_zero]
            have hdeg_r : (C α * X ^ (d + 1 - m)).degree ≤ ((d + 1 - m : ℕ) : WithBot ℕ) := by
              rw [degree_C_mul hα, degree_X_pow]
            calc ((g - X ^ m) * (C α * X ^ (d + 1 - m))).degree
                = (g - X ^ m).degree + (C α * X ^ (d + 1 - m)).degree := degree_mul
              _ < (m : WithBot ℕ) + ((d + 1 - m : ℕ) : WithBot ℕ) :=
                  WithBot.add_lt_add_of_lt_of_le (by rw [degree_C_mul hα, degree_X_pow]; exact WithBot.coe_ne_bot) hlt_g hdeg_r
              _ = ((d + 1 : ℕ) : WithBot ℕ) := by norm_cast; omega
      · have hqlt : q.val.degree < ((d + 1 - m : ℕ) : WithBot ℕ) := (mem_degreeLT.mp q.2)
        have hgd' : g.degree = (m : WithBot ℕ) := by
          rw [degree_eq_natDegree hgm.ne_zero, hgd]
        calc (g * q.val).degree = g.degree + q.val.degree := degree_mul
          _ < (m : WithBot ℕ) + ((d + 1 - m : ℕ) : WithBot ℕ) :=
              WithBot.add_lt_add_of_le_of_lt (by rw [hgd']; exact WithBot.coe_ne_bot) (le_of_eq hgd') hqlt
          _ = ((d + 1 : ℕ) : WithBot ℕ) := by norm_cast; omega
    let f : degreeLT F (d + 1 - m) → degreeLT F (d + 1) :=
      fun q => ⟨g * (C α * X ^ (d + 1 - m) + q.val) - C α * X ^ (d + 1), hdeg_lt q⟩
    have hf_inj : Function.Injective f := by
      intro q1 q2 h
      have hv : (f q1).val = (f q2).val := congr_arg Subtype.val h
      simp only [f] at hv
      have hmul : g * (C α * X ^ (d + 1 - m) + q1.val) = g * (C α * X ^ (d + 1 - m) + q2.val) :=
        sub_left_inj.mp hv
      have hadd := mul_left_cancel₀ hgm.ne_zero hmul
      exact Subtype.ext (add_left_cancel hadd)
    have hf_img : Finset.univ.filter (fun r : degreeLT F (d + 1) => g ∣ C α * X ^ (d + 1) + r.val) =
        Finset.univ.image f := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨Q, hQ⟩
        -- Show Q - C α * X^(d + 1 - m) ∈ degreeLT F (d + 1 - m)
        have hqmem : Q - C α * X ^ (d + 1 - m) ∈ degreeLT F (d + 1 - m) := by
          rw [mem_degreeLT]
          by_contra hge
          push Not at hge
          have hne0 : Q - C α * X ^ (d + 1 - m) ≠ 0 := by
            intro h0; rw [h0, degree_zero] at hge; exact not_lt_of_ge hge (WithBot.bot_lt_coe _)
          have hdeg_mul : (g * (Q - C α * X ^ (d + 1 - m))).degree ≥ ((d + 1 : ℕ) : WithBot ℕ) := by
            rw [degree_mul, degree_eq_natDegree hgm.ne_zero, hgd]
            calc ((d + 1 : ℕ) : WithBot ℕ) = (m : WithBot ℕ) + ((d + 1 - m : ℕ) : WithBot ℕ) := by
                  norm_cast; omega
              _ ≤ (m : WithBot ℕ) + (Q - C α * X ^ (d + 1 - m)).degree :=
                  add_le_add (le_refl _) hge
          have heq : g * (Q - C α * X ^ (d + 1 - m)) =
              r.val - (g - X ^ m) * (C α * X ^ (d + 1 - m)) := by
            have hpow : X ^ m * (C α * X ^ (d + 1 - m)) = C α * X ^ (d + 1) := by
              rw [mul_left_comm, ← pow_add, show m + (d + 1 - m) = d + 1 by omega]
            rw [mul_sub, ← hQ, sub_mul, hpow]; ring
          rw [heq] at hdeg_mul
          have hrlt : r.val.degree < ((d + 1 : ℕ) : WithBot ℕ) := mem_degreeLT.mp r.2
          have h2lt : ((g - X ^ m) * (C α * X ^ (d + 1 - m))).degree < ((d + 1 : ℕ) : WithBot ℕ) := by
            by_cases hgx : g - X ^ m = 0
            · simp [hgx]
            · by_cases hα : α = 0
              · simp [hα]
              · have hlt_g : (g - X ^ m).degree < (m : WithBot ℕ) := by
                  rw [degree_lt_iff_coeff_zero]
                  intro k hk
                  rw [coeff_sub, coeff_X_pow]
                  rcases eq_or_lt_of_le hk with rfl | hgt
                  · rw [if_pos rfl, ← hgd, ← leadingCoeff, hgm.leadingCoeff, sub_self]
                  · rw [if_neg (Nat.ne_of_gt hgt), coeff_eq_zero_of_natDegree_lt (hgd ▸ hgt), sub_zero]
                have hdeg_r : (C α * X ^ (d + 1 - m)).degree ≤ ((d + 1 - m : ℕ) : WithBot ℕ) := by
                  rw [degree_C_mul hα, degree_X_pow]
                calc ((g - X ^ m) * (C α * X ^ (d + 1 - m))).degree
                    = (g - X ^ m).degree + (C α * X ^ (d + 1 - m)).degree := degree_mul
                  _ < (m : WithBot ℕ) + ((d + 1 - m : ℕ) : WithBot ℕ) :=
                      WithBot.add_lt_add_of_lt_of_le (by rw [degree_C_mul hα, degree_X_pow]; exact WithBot.coe_ne_bot) hlt_g hdeg_r
                  _ = ((d + 1 : ℕ) : WithBot ℕ) := by norm_cast; omega
          have hsublt : (r.val - (g - X ^ m) * (C α * X ^ (d + 1 - m))).degree <
              ((d + 1 : ℕ) : WithBot ℕ) :=
            lt_of_le_of_lt (degree_sub_le _ _) (max_lt hrlt h2lt)
          exact not_lt_of_ge hdeg_mul hsublt
        refine ⟨⟨Q - C α * X ^ (d + 1 - m), hqmem⟩, ?_⟩
        apply Subtype.ext
        simp only [f]
        have : C α * X ^ (d + 1 - m) + (Q - C α * X ^ (d + 1 - m)) = Q := by ring
        rw [this, ← hQ]; ring
      · rintro ⟨q, rfl⟩
        refine ⟨C α * X ^ (d + 1 - m) + q.val, ?_⟩
        simp only [f]; ring
    rw [hf_img, Finset.card_image_of_injective _ hf_inj, Finset.card_univ]
    rw [Fintype.card_congr (degreeLTEquiv F (d + 1 - m)).toEquiv]
    simp [Fintype.card_pi]
  · rw [if_neg hmd]
    have hgt : d + 1 < m := Nat.lt_of_not_le hmd
    by_cases hα : α = 0
    · rw [if_pos hα]
      have hset : Finset.univ.filter (fun r : degreeLT F (d + 1) => g ∣ C α * X ^ (d + 1) + r.val) =
          {0} := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hα,
          map_zero, zero_mul, zero_add]
        constructor
        · intro hdvd
          by_contra hr0
          have hval0 : r.val ≠ 0 := fun h => hr0 (Subtype.ext h)
          have hle := Polynomial.natDegree_le_of_dvd hdvd hval0
          have hrlt : r.val.natDegree < d + 1 := by
            have := mem_degreeLT.mp r.2
            rw [degree_eq_natDegree hval0] at this
            exact WithBot.coe_lt_coe.mp this
          omega
        · rintro rfl; exact dvd_zero g
      rw [hset, Finset.card_singleton]
    · rw [if_neg hα]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro r _ hdvd
      have hne0 : C α * X ^ (d + 1) + r.val ≠ 0 := by
        intro h0
        have hc := congr_arg (fun p : F[X] => p.coeff (d + 1)) h0
        have hr0 : r.val.coeff (d + 1) = 0 := by
          have := mem_degreeLT.mp r.2
          exact (degree_lt_iff_coeff_zero _ _).mp this (d + 1) (le_refl _)
        simp [coeff_C_mul, coeff_X_pow, hr0] at hc
        exact hα hc
      have hle := Polynomial.natDegree_le_of_dvd hdvd hne0
      have hdeg_le : (C α * X ^ (d + 1) + r.val).natDegree ≤ d + 1 := by
        apply natDegree_add_le_of_degree_le
        · exact natDegree_C_mul_X_pow_le α (d + 1)
        · exact natDegree_le_of_degree_le (le_of_lt (mem_degreeLT.mp r.2))
      omega

-- Main Mobius counting theorem for coprime affine polynomial tuples!
theorem card_coprime_affine {r : ℕ} (d : Fin r → ℕ) (α : Fin r → F) (hα : ∃ s, α s ≠ 0) :
    letI : ∀ s, Fintype (degreeLT F (d s + 1)) :=
      fun s => Fintype.ofEquiv (Fin (d s + 1) → F) (degreeLTEquiv F (d s + 1)).symm.toEquiv
    (Finset.univ.filter (fun R : ∀ s : Fin r, degreeLT F (d s + 1) =>
      IsCoprimeTuple (fun s => C (α s) * X ^ (d s + 1) + (R s).val))).card =
      Fintype.card F ^ (∑ s : Fin r, (d s + 1)) - Fintype.card F ^ ((∑ s : Fin r, d s) + 1) := by
  letI : ∀ s, Fintype (degreeLT F (d s + 1)) :=
    fun s => Fintype.ofEquiv (Fin (d s + 1) → F) (degreeLTEquiv F (d s + 1)).symm.toEquiv
  rcases hα with ⟨s0, hs0⟩
  set M := d s0 + 1
  have hP_ne : ∀ R : ∀ s : Fin r, degreeLT F (d s + 1),
      (C (α s0) * X ^ (d s0 + 1) + (R s0).val) ≠ 0 := by
    intro R h0
    have hc := congr_arg (fun p : F[X] => p.coeff (d s0 + 1)) h0
    have hr0 : (R s0).val.coeff (d s0 + 1) = 0 :=
      (degree_lt_iff_coeff_zero _ _).mp (mem_degreeLT.mp (R s0).2) _ (le_refl _)
    simp [coeff_C_mul, coeff_X_pow, hr0] at hc
    exact hs0 hc
  have hP_deg : ∀ R : ∀ s : Fin r, degreeLT F (d s + 1),
      (C (α s0) * X ^ (d s0 + 1) + (R s0).val).natDegree ≤ M := by
    intro R
    apply natDegree_add_le_of_degree_le
    · exact natDegree_C_mul_X_pow_le (α s0) (d s0 + 1)
    · exact natDegree_le_of_degree_le (le_of_lt (mem_degreeLT.mp (R s0).2))
  -- Express indicator as Mobius sum over m ≤ M and g ∈ monicDeg m
  have hind : ∀ R : ∀ s : Fin r, degreeLT F (d s + 1),
      (if IsCoprimeTuple (fun s => C (α s) * X ^ (d s + 1) + (R s).val) then (1 : ℤ) else 0) =
      ∑ m ∈ Finset.range (M + 1), ∑ g ∈ monicDeg (F := F) m,
        if (∀ s, g ∣ C (α s) * X ^ (d s + 1) + (R s).val) then mobius g else 0 := by
    intro R
    set P := fun s => C (α s) * X ^ (d s + 1) + (R s).val
    have hne : ∃ s, P s ≠ 0 := ⟨s0, hP_ne R⟩
    have ⟨hmH, hdvdH⟩ := monicGcd_spec hne
    have hite : (if IsCoprimeTuple P then (1 : ℤ) else 0) = if monicGcd P = 1 then 1 else 0 := by
      by_cases hc : IsCoprimeTuple P
      · rw [if_pos hc, if_pos ((isCoprimeTuple_iff_monicGcd_eq_one hne).mp hc)]
      · rw [if_neg hc, if_neg (mt (isCoprimeTuple_iff_monicGcd_eq_one hne).mpr hc)]
    change (if IsCoprimeTuple P then (1 : ℤ) else 0) = _
    rw [hite, ← sum_mobius_monicDivisors hmH]
    have hdegH : (monicGcd P).natDegree ≤ M := by
      have hdvd0 : monicGcd P ∣ P s0 := (hdvdH (monicGcd P)).mp (dvd_refl _) s0
      exact le_trans (Polynomial.natDegree_le_of_dvd hdvd0 (hP_ne R)) (hP_deg R)
    have hset : monicDivisors (monicGcd P) =
        (Finset.range (M + 1)).biUnion
          (fun m => (monicDeg (F := F) m).filter (fun g => ∀ s, g ∣ P s)) := by
      ext g
      rw [mem_monicDivisors hmH.ne_zero, hdvdH]
      simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, mem_monicDeg]
      constructor
      · rintro ⟨hgm, hg⟩
        have hg_le := le_trans (Polynomial.natDegree_le_of_dvd ((hdvdH g).mpr hg) hmH.ne_zero) hdegH
        exact ⟨g.natDegree, Nat.lt_succ_of_le hg_le, ⟨hgm, rfl⟩, hg⟩
      · rintro ⟨m, _, ⟨hgm, _⟩, hg⟩
        exact ⟨hgm, hg⟩
    rw [hset, Finset.sum_biUnion]
    · apply Finset.sum_congr rfl
      intro m _
      rw [Finset.sum_filter]
    · intro m1 _ m2 _ hne_m
      exact Finset.disjoint_left.mpr fun g hg1 hg2 => by
        simp only [Finset.mem_filter, mem_monicDeg] at hg1 hg2
        exact hne_m (hg1.1.2.symm.trans hg2.1.2)
  -- Cast the target equality to ℤ and swap sums
  have hle_exp : (∑ s : Fin r, d s) + 1 ≤ ∑ s : Fin r, (d s + 1) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one]
    have hr_pos : 1 ≤ r := Nat.pos_of_ne_zero (by rintro rfl; exact Fin.elim0 s0)
    omega
  have hle_pow : Fintype.card F ^ ((∑ s : Fin r, d s) + 1) ≤
      Fintype.card F ^ (∑ s : Fin r, (d s + 1)) :=
    Nat.pow_le_pow_right Fintype.card_pos hle_exp
  zify [hle_pow]
  have hcard_eq : ((Finset.univ.filter (fun R : ∀ s : Fin r, degreeLT F (d s + 1) =>
      IsCoprimeTuple (fun s => C (α s) * X ^ (d s + 1) + (R s).val))).card : ℤ) =
      ∑ R : ∀ s : Fin r, degreeLT F (d s + 1),
        if IsCoprimeTuple (fun s => C (α s) * X ^ (d s + 1) + (R s).val) then (1 : ℤ) else 0 := by
    simp [Finset.sum_boole]
  rw [hcard_eq]
  simp_rw [hind]
  rw [Finset.sum_comm]
  -- For each m ≤ M, evaluate ∑ g ∈ monicDeg m, ∑ R, (if ∀ s, g ∣ P R s then mobius g else 0)
  have hterm : ∀ m ∈ Finset.range (M + 1),
      ∑ R : ∀ s : Fin r, degreeLT F (d s + 1), ∑ g ∈ monicDeg (F := F) m,
        (if (∀ s, g ∣ C (α s) * X ^ (d s + 1) + (R s).val) then mobius g else 0) =
      (∏ s : Fin r, (if m ≤ d s + 1 then (Fintype.card F : ℤ) ^ (d s + 1 - m)
        else if α s = 0 then 1 else 0)) * (∑ g ∈ monicDeg (F := F) m, mobius g) := by
    intro m _
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g hg
    have ⟨hgm, hgd⟩ := mem_monicDeg.mp hg
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    congr 1
    -- Factor the Pi filter into product of per-coordinate filters!
    have hpi : Finset.univ.filter (fun R : ∀ s : Fin r, degreeLT F (d s + 1) =>
        ∀ s, g ∣ C (α s) * X ^ (d s + 1) + (R s).val) =
        Fintype.piFinset (fun s => Finset.univ.filter
          (fun r : degreeLT F (d s + 1) => g ∣ C (α s) * X ^ (d s + 1) + r.val)) := by
      ext R
      simp [Fintype.mem_piFinset]
    rw [hpi, Fintype.card_piFinset]
    push_cast
    apply Finset.prod_congr rfl
    intro s _
    have hs := card_dvd_affine_single (d s) (α s) hgm hgd
    rw [hs]
    split_ifs <;> norm_cast
  rw [Finset.sum_congr rfl hterm]
  -- Evaluate the sum over m ∈ range (M + 1): only m = 0 and m = 1 contribute!
  have hM1 : 1 ≤ M := by omega
  have hmem0 : (0 : ℕ) ∈ Finset.range (M + 1) := Finset.mem_range.mpr (by omega)
  have hmem1 : (1 : ℕ) ∈ (Finset.range (M + 1)).erase 0 := by
    simp [Finset.mem_erase, Finset.mem_range]; omega
  rw [← Finset.add_sum_erase _ _ hmem0, ← Finset.add_sum_erase _ _ hmem1]
  have hrest : ∑ m ∈ ((Finset.range (M + 1)).erase 0).erase 1,
      (∏ s : Fin r, (if m ≤ d s + 1 then (Fintype.card F : ℤ) ^ (d s + 1 - m)
        else if α s = 0 then 1 else 0)) * (∑ g ∈ monicDeg (F := F) m, mobius g) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    simp only [Finset.mem_erase] at hm
    rw [sum_mobius_monicDeg m, if_neg hm.2.1, if_neg hm.1, mul_zero]
  rw [hrest, add_zero]
  rw [sum_mobius_monicDeg 0, sum_mobius_monicDeg 1]
  simp only [↓reduceIte, show (1 : ℕ) ≠ 0 by omega, Nat.zero_le, Nat.sub_zero,
    show ∀ s : Fin r, 1 ≤ d s + 1 from fun s => Nat.succ_le_succ (Nat.zero_le _),
    Nat.add_sub_cancel, mul_one, mul_neg]
  rw [pow_succ, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum]
  ring

end Mobius



open Polynomial BigOperators Matrix

section Pencil

variable {F : Type*} [Field F]

abbrev AC (F : Type*) [Field F] := AlgebraicClosure F

def NondegenerateRect {D j : ℕ} (A B : Matrix (Fin D) (Fin j) F) : Prop :=
  ∀ c₁ c₂ : AC F, (c₁, c₂) ≠ 0 →
    (c₁ • A.map (algebraMap F (AC F)) + c₂ • B.map (algebraMap F (AC F))).rank = j

-- Equivalent injectivity characterization over AC F
lemma nondegenerateRect_iff_injective {D j : ℕ} (A B : Matrix (Fin D) (Fin j) F) :
    NondegenerateRect A B ↔
      ∀ c₁ c₂ : AC F, (c₁, c₂) ≠ 0 →
        Function.Injective (c₁ • A.map (algebraMap F (AC F)) + c₂ • B.map (algebraMap F (AC F))).mulVecLin := by
  constructor
  · intro h c₁ c₂ hc
    have hr := h c₁ c₂ hc
    rw [Matrix.rank] at hr
    have hfin := LinearMap.finrank_range_add_finrank_ker
      (c₁ • A.map (algebraMap F (AC F)) + c₂ • B.map (algebraMap F (AC F))).mulVecLin
    rw [Module.finrank_pi, Fintype.card_fin] at hfin
    have hker : Module.finrank (AC F) (LinearMap.ker
        (c₁ • A.map (algebraMap F (AC F)) + c₂ • B.map (algebraMap F (AC F))).mulVecLin) = 0 := by
      omega
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.finrank_eq_zero.mp hker
  · intro h c₁ c₂ hc
    have hinj := h c₁ c₂ hc
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj, Module.finrank_pi, Fintype.card_fin]

lemma mulVecLin_injective_of_map_injective {D j : ℕ} (M : Matrix (Fin D) (Fin j) F)
    (h : Function.Injective (M.map (algebraMap F (AC F))).mulVecLin) :
    Function.Injective M.mulVecLin := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  have hv' : (M.map (algebraMap F (AC F))).mulVecLin (fun i => algebraMap F (AC F) (v i)) = 0 := by
    ext u
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply]
    have h0 : (M *ᵥ v) u = 0 := congr_fun hv u
    simp only [Matrix.mulVec, dotProduct] at h0
    simp_rw [← map_mul]
    rw [← map_sum, h0, map_zero]
  have hzero : (fun i => algebraMap F (AC F) (v i)) = 0 := h (hv'.trans (map_zero _).symm)
  ext i
  exact (algebraMap F (AC F)).injective (by simpa using congr_fun hzero i)

lemma map_mulVecLin_injective_of_injective {D j : ℕ} (M : Matrix (Fin D) (Fin j) F)
    (h : Function.Injective M.mulVecLin) :
    Function.Injective (M.map (algebraMap F (AC F))).mulVecLin := by
  -- Use rank preservation or linear independence preservation:
  -- Equivalently, M has a left inverse N : Matrix (Fin j) (Fin D) F with N * M = 1!
  have hsurj : Function.Surjective Mᵀ.mulVecLin := by
    have hrank : M.rank = j := by
      rw [Matrix.rank, LinearMap.finrank_range_of_inj h, Module.finrank_pi, Fintype.card_fin]
    have hrankT : Mᵀ.rank = j := by rw [Matrix.rank_transpose, hrank]
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank, hrankT, Module.finrank_pi, Fintype.card_fin]
  -- Pick a right inverse of Mᵀ, i.e., a left inverse N of M!
  choose col hcol using fun i : Fin j => hsurj (Pi.single i 1)
  let N : Matrix (Fin j) (Fin D) F := Matrix.of (fun i u => col i u)
  have hNM : N * M = 1 := by
    ext i l
    have hi := congr_fun (hcol i) l
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Pi.single_apply] at hi
    simp only [Matrix.mul_apply, Matrix.one_apply, N, Matrix.of_apply]
    convert hi using 1
    · apply Finset.sum_congr rfl; intro u _; ring
    · simp [eq_comm]
  have hNM_map : N.map (algebraMap F (AC F)) * M.map (algebraMap F (AC F)) = 1 := by
    rw [← Matrix.map_mul, hNM, Matrix.map_one (algebraMap F (AC F)) (map_zero _) (map_one _)]
  intro v1 v2 hv
  have h1 : (N.map (algebraMap F (AC F))) *ᵥ ((M.map (algebraMap F (AC F))) *ᵥ v1) =
      (N.map (algebraMap F (AC F))) *ᵥ ((M.map (algebraMap F (AC F))) *ᵥ v2) :=
    congr_arg _ hv
  simpa [Matrix.mulVec_mulVec, hNM_map] using h1

-- Linear map (X • A^T + B^T) : (Fin D → F[X]) →ₗ[F[X]] (Fin j → F[X])
noncomputable def pencilT {D j : ℕ} (A B : Matrix (Fin D) (Fin j) F) :
    (Fin D → F[X]) →ₗ[F[X]] (Fin j → F[X]) :=
  ((X : F[X]) • Aᵀ.map C + Bᵀ.map C).mulVecLin

-- Linear map (X • A + B) : (Fin j → F[X]) →ₗ[F[X]] (Fin D → F[X])
noncomputable def pencil {D j : ℕ} (A B : Matrix (Fin D) (Fin j) F) :
    (Fin j → F[X]) →ₗ[F[X]] (Fin D → F[X]) :=
  ((X : F[X]) • A.map C + B.map C).mulVecLin

-- Vector degree and coefficient vector
noncomputable def vdeg {D : ℕ} (p : Fin D → F[X]) : ℕ :=
  Finset.univ.sup (fun u : Fin D => (p u).natDegree)

def coeffVec {D : ℕ} (p : Fin D → F[X]) (d : ℕ) : Fin D → F :=
  fun u => (p u).coeff d

noncomputable def leadVec {D : ℕ} (p : Fin D → F[X]) : Fin D → F :=
  coeffVec p (vdeg p)

lemma natDegree_le_vdeg {D : ℕ} (p : Fin D → F[X]) (u : Fin D) :
    (p u).natDegree ≤ vdeg p :=
  Finset.le_sup (f := fun u : Fin D => (p u).natDegree) (Finset.mem_univ u)

lemma coeffVec_eq_zero_of_gt {D : ℕ} (p : Fin D → F[X]) {k : ℕ} (hk : vdeg p < k) :
    coeffVec p k = 0 := by
  ext u
  exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_le_vdeg p u) hk)

lemma vdeg_le_iff {D : ℕ} (p : Fin D → F[X]) (N : ℕ) :
    vdeg p ≤ N ↔ ∀ u : Fin D, (p u).natDegree ≤ N := by
  unfold vdeg
  simp [Finset.sup_le_iff]

lemma leadVec_ne_zero {D : ℕ} {p : Fin D → F[X]} (hp : p ≠ 0) :
    leadVec p ≠ 0 := by
  have hex : ∃ u : Fin D, p u ≠ 0 := by
    by_contra hall; push Not at hall; exact hp (funext hall)
  -- Pick u achieving vdeg p (or if vdeg p = 0, pick any u with p u ≠ 0)
  by_cases h0 : vdeg p = 0
  · rcases hex with ⟨u, hu⟩
    intro hz
    have hcu : (p u).coeff 0 = 0 := by simpa [leadVec, coeffVec, h0] using congr_fun hz u
    have hdu : (p u).natDegree = 0 := Nat.le_zero.mp (h0 ▸ natDegree_le_vdeg p u)
    have hlc : (p u).leadingCoeff = 0 := by rw [leadingCoeff, hdu, hcu]
    exact hu (leadingCoeff_eq_zero.mp hlc)
  · have hpos : 0 < vdeg p := Nat.pos_of_ne_zero h0
    have hex_max : ∃ u : Fin D, (p u).natDegree = vdeg p := by
      have hne_univ : (Finset.univ : Finset (Fin D)).Nonempty := by
        rcases hex with ⟨u, _⟩; exact ⟨u, Finset.mem_univ u⟩
      obtain ⟨u, _, hu⟩ := Finset.exists_mem_eq_sup Finset.univ hne_univ (fun u => (p u).natDegree)
      exact ⟨u, hu.symm⟩
    rcases hex_max with ⟨u, hu⟩
    have hpu : p u ≠ 0 := by
      intro hz; rw [hz, natDegree_zero] at hu; omega
    intro hz
    have hcu : (p u).coeff (vdeg p) = 0 := congr_fun hz u
    rw [← hu] at hcu
    exact leadingCoeff_ne_zero.mpr hpu hcu

lemma leadVec_mem_ker_AT {D j : ℕ} {A B : Matrix (Fin D) (Fin j) F}
    {p : Fin D → F[X]} (hp : p ∈ LinearMap.ker (pencilT A B)) :
    Aᵀ *ᵥ leadVec p = 0 := by
  ext i
  have hi : (pencilT A B p i).coeff (vdeg p + 1) = 0 := by
    rw [LinearMap.mem_ker.mp hp]; simp
  simp only [pencilT, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.add_apply,
    Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, finsetSum_coeff] at hi
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, leadVec, coeffVec]
  convert hi using 1
  apply Finset.sum_congr rfl
  intro u _
  have h0 : (p u).coeff (vdeg p + 1) = 0 :=
    coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_of_le (natDegree_le_vdeg p u))
  rw [add_mul, mul_assoc, coeff_add, coeff_X_mul, coeff_C_mul, coeff_C_mul, h0, mul_zero, add_zero]

lemma coeffVec_add {D : ℕ} (p q : Fin D → F[X]) (d : ℕ) :
    coeffVec (p + q) d = coeffVec p d + coeffVec q d := by
  ext u; simp [coeffVec]

lemma coeffVec_smul_C {D : ℕ} (c : F) (p : Fin D → F[X]) (d : ℕ) :
    coeffVec (C c • p) d = c • coeffVec p d := by
  ext u; simp [coeffVec]

lemma coeffVec_X_pow_smul {D : ℕ} (k : ℕ) (p : Fin D → F[X]) (d : ℕ) :
    coeffVec ((X ^ k : F[X]) • p) (d + k) = coeffVec p d := by
  ext u; simp [coeffVec, coeff_X_pow_mul']

lemma vdeg_smul_le {D : ℕ} (f : F[X]) (p : Fin D → F[X]) :
    vdeg (f • p) ≤ f.natDegree + vdeg p := by
  rw [vdeg_le_iff]
  intro u
  exact le_trans natDegree_mul_le (add_le_add (le_refl _) (natDegree_le_vdeg p u))

lemma vdeg_sum_le {D : ℕ} {ι : Type*} (s : Finset ι) (g : ι → Fin D → F[X]) (N : ℕ)
    (h : ∀ i ∈ s, vdeg (g i) ≤ N) : vdeg (∑ i ∈ s, g i) ≤ N := by
  rw [vdeg_le_iff]
  intro u
  rw [Finset.sum_apply]
  apply natDegree_sum_le_of_forall_le
  intro i hi
  exact le_trans (natDegree_le_vdeg (g i) u) (h i hi)

-- Crucial property of a leading-vector-independent tuple: no cancellation at top degree!
lemma vdeg_linear_comb_eq {D s : ℕ} (p : Fin s → Fin D → F[X])
    (hind : LinearIndependent F (fun t : Fin s => leadVec (p t)))
    (f : Fin s → F[X]) (hf : ∃ t, f t ≠ 0) :
    let M := Finset.univ.sup (fun t : Fin s => if f t = 0 then 0 else (f t).natDegree + vdeg (p t))
    (∑ t : Fin s, f t • p t) ≠ 0 ∧ vdeg (∑ t : Fin s, f t • p t) = M := by
  intro M
  have hle : vdeg (∑ t : Fin s, f t • p t) ≤ M := by
    apply vdeg_sum_le
    intro t _
    by_cases hft : f t = 0
    · simp [hft, vdeg]
    · calc vdeg (f t • p t) ≤ (f t).natDegree + vdeg (p t) := vdeg_smul_le (f t) (p t)
        _ ≤ M := by
          have := Finset.le_sup (f := fun t : Fin s =>
            if f t = 0 then 0 else (f t).natDegree + vdeg (p t)) (Finset.mem_univ t)
          dsimp only [M]
          simpa [hft] using this
  -- Compute coeffVec at M!
  have hcoeffM : coeffVec (∑ t : Fin s, f t • p t) M =
      ∑ t : Fin s, (if f t ≠ 0 ∧ (f t).natDegree + vdeg (p t) = M then (f t).leadingCoeff else 0) •
        leadVec (p t) := by
    ext u
    simp only [coeffVec, Finset.sum_apply, finsetSum_coeff, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro t _
    by_cases hft : f t = 0
    · simp [hft]
    · have hle_t : (f t).natDegree + vdeg (p t) ≤ M := by
        have := Finset.le_sup (f := fun t : Fin s =>
          if f t = 0 then 0 else (f t).natDegree + vdeg (p t)) (Finset.mem_univ t)
        dsimp only [M]
        simpa [hft] using this
      by_cases heq : (f t).natDegree + vdeg (p t) = M
      · rw [if_pos ⟨hft, heq⟩, ← heq]
        have hpu_le : (p t u).natDegree ≤ vdeg (p t) := natDegree_le_vdeg (p t) u
        rw [Polynomial.coeff_mul]
        -- Only the term ((f t).natDegree, vdeg (p t)) can be nonzero!
        rw [Finset.sum_eq_single ((f t).natDegree, vdeg (p t))]
        · rfl
        · intro x hx hne
          rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
          rcases lt_or_gt_of_ne (show x.1 ≠ (f t).natDegree by
            intro h1; exact hne (Prod.ext h1 (by omega))) with hlt | hgt
          · have h2gt : vdeg (p t) < x.2 := by omega
            rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hpu_le h2gt), mul_zero]
          · rw [coeff_eq_zero_of_natDegree_lt hgt, zero_mul]
        · intro h; exact (h (Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl)).elim
      · rw [if_neg (fun hc => heq hc.2), zero_mul]
        have hlt_t : (f t).natDegree + vdeg (p t) < M := lt_of_le_of_ne hle_t heq
        exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (le_trans natDegree_mul_le
          (add_le_add (le_refl _) (natDegree_le_vdeg (p t) u))) hlt_t)
  -- At least one t has f t ≠ 0 and (f t).natDegree + vdeg (p t) = M!
  have hex_max : ∃ t : Fin s, f t ≠ 0 ∧ (f t).natDegree + vdeg (p t) = M := by
    rcases hf with ⟨t0, ht0⟩
    have hne_s : (Finset.univ.filter (fun t : Fin s => f t ≠ 0)).Nonempty :=
      ⟨t0, Finset.mem_filter.mpr ⟨Finset.mem_univ t0, ht0⟩⟩
    obtain ⟨tm, htm, hmax⟩ := Finset.exists_mem_eq_sup _ hne_s
      (fun t : Fin s => (f t).natDegree + vdeg (p t))
    have htm_ne : f tm ≠ 0 := (Finset.mem_filter.mp htm).2
    have hM_eq : M = (f tm).natDegree + vdeg (p tm) := by
      apply le_antisymm
      · apply Finset.sup_le
        intro t _
        by_cases hft : f t = 0
        · rw [if_pos hft]; exact Nat.zero_le _
        · rw [if_neg hft, ← hmax]
          exact Finset.le_sup (f := fun t : Fin s => (f t).natDegree + vdeg (p t))
            (Finset.mem_filter.mpr ⟨Finset.mem_univ t, hft⟩)
      · have := Finset.le_sup (f := fun t : Fin s =>
          if f t = 0 then 0 else (f t).natDegree + vdeg (p t)) (Finset.mem_univ tm)
        dsimp only [M]
        simpa [htm_ne] using this
    exact ⟨tm, htm_ne, hM_eq.symm⟩
  have hne_coeffM : coeffVec (∑ t : Fin s, f t • p t) M ≠ 0 := by
    rw [hcoeffM]
    intro h0
    have hlin := (Fintype.linearIndependent_iff.mp hind)
      (fun t => if f t ≠ 0 ∧ (f t).natDegree + vdeg (p t) = M then (f t).leadingCoeff else 0) h0
    rcases hex_max with ⟨tm, htm1, htm2⟩
    have := hlin tm
    rw [if_pos ⟨htm1, htm2⟩] at this
    exact leadingCoeff_ne_zero.mpr htm1 this
  have hne_sum : (∑ t : Fin s, f t • p t) ≠ 0 := by
    intro h0; rw [h0] at hne_coeffM; apply hne_coeffM; ext u; simp [coeffVec]
  refine ⟨hne_sum, le_antisymm hle ?_⟩
  by_contra hlt
  push Not at hlt
  exact hne_coeffM (coeffVec_eq_zero_of_gt _ hlt)

-- Bounded-degree subspace of Fin D → F[X]: vectors with vdeg ≤ N (isomorphic to Fin D → Fin (N+1) → F)
noncomputable def boundedPolys (D N : ℕ) : Submodule F (Fin D → F[X]) where
  carrier := {p | ∀ u : Fin D, p u ∈ degreeLT F (N + 1)}
  add_mem' ha hb u := Submodule.add_mem _ (ha u) (hb u)
  zero_mem' u := Submodule.zero_mem _
  smul_mem' c a ha u := Submodule.smul_mem _ c (ha u)

lemma mem_boundedPolys_iff {D N : ℕ} {p : Fin D → F[X]} :
    p ∈ boundedPolys (F := F) D N ↔ vdeg p ≤ N := by
  simp only [boundedPolys, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq, mem_degreeLT, vdeg_le_iff]
  constructor
  · intro h u
    by_cases h0 : p u = 0
    · simp [h0]
    · have := h u
      rw [degree_eq_natDegree h0] at this
      exact Nat.lt_succ_iff.mp (WithBot.coe_lt_coe.mp this)
  · intro h u
    by_cases h0 : p u = 0
    · simp [h0]
    · rw [degree_eq_natDegree h0]
      exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le (h u))

noncomputable def boundedPolysEquiv (D N : ℕ) :
    boundedPolys (F := F) D N ≃ₗ[F] (Fin D → Fin (N + 1) → F) where
  toFun p u := degreeLTEquiv F (N + 1) ⟨p.val u, p.2 u⟩
  map_add' p q := by
    funext u
    have h : (⟨(p + q).val u, (p + q).2 u⟩ : degreeLT F (N + 1)) =
        ⟨p.val u, p.2 u⟩ + ⟨q.val u, q.2 u⟩ := rfl
    rw [h, map_add]; rfl
  map_smul' c p := by
    funext u
    have h : (⟨(c • p).val u, (c • p).2 u⟩ : degreeLT F (N + 1)) =
        c • (⟨p.val u, p.2 u⟩ : degreeLT F (N + 1)) := rfl
    rw [h, map_smul]; rfl
  invFun f := ⟨fun u => ((degreeLTEquiv F (N + 1)).symm (f u)).val,
    fun u => ((degreeLTEquiv F (N + 1)).symm (f u)).2⟩
  left_inv p := by
    apply Subtype.ext; funext u
    exact congr_arg Subtype.val ((degreeLTEquiv F (N + 1)).left_inv ⟨p.val u, p.2 u⟩)
  right_inv f := by
    funext u
    exact (degreeLTEquiv F (N + 1)).right_inv (f u)

lemma finite_degreeLT (k : ℕ) : Module.Finite F (degreeLT F k) :=
  Module.Finite.equiv (degreeLTEquiv F k).symm

lemma finite_boundedPolys (D N : ℕ) : Module.Finite F (boundedPolys (F := F) D N) :=
  Module.Finite.equiv (boundedPolysEquiv (F := F) D N).symm

lemma finrank_boundedPolys (D N : ℕ) :
    Module.finrank F (boundedPolys (F := F) D N) = D * (N + 1) := by
  rw [LinearEquiv.finrank_eq (boundedPolysEquiv (F := F) D N), Module.finrank_pi_fintype]
  simp [Module.finrank_pi]

-- Restricted F-linear map T_N : boundedPolys D N →ₗ[F] boundedPolys j (N + 1)
noncomputable def pencilT_bounded {D j : ℕ} (A B : Matrix (Fin D) (Fin j) F) (N : ℕ) :
    boundedPolys (F := F) D N →ₗ[F] boundedPolys (F := F) j (N + 1) where
  toFun p := ⟨pencilT A B p.val, by
    rw [mem_boundedPolys_iff, vdeg_le_iff]
    intro i
    simp only [pencilT, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.add_apply,
      Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    apply natDegree_sum_le_of_forall_le
    intro u _
    have hpu : (p.val u).natDegree ≤ N := (vdeg_le_iff _ _).mp (mem_boundedPolys_iff.mp p.2) u
    apply le_trans natDegree_mul_le
    have hlin : (X * C (Aᵀ i u) + C (Bᵀ i u)).natDegree ≤ 1 := by
      apply natDegree_add_le_of_degree_le
      · exact le_trans natDegree_mul_le (by simp [natDegree_X, natDegree_C])
      · simp [natDegree_C]
    omega⟩
  map_add' p q := Subtype.ext (map_add (pencilT A B) p.val q.val)
  map_smul' c p := Subtype.ext (by
    have h1 : (c • p).val = C c • p.val := by
      funext u; simp [Polynomial.smul_eq_C_mul]
    have h2 : c • pencilT A B p.val = C c • pencilT A B p.val := by
      funext i; simp [Polynomial.smul_eq_C_mul]
    change pencilT A B (c • p).val = c • pencilT A B p.val
    rw [h1, h2, map_smul])

lemma finrank_ker_pencilT_bounded_ge {D j : ℕ} (A B : Matrix (Fin D) (Fin j) F) (N : ℕ) :
    (N + 1) * D ≤ Module.finrank F (LinearMap.ker (pencilT_bounded A B N)) + (N + 2) * j := by
  haveI := finite_boundedPolys (F := F) D N
  haveI := finite_boundedPolys (F := F) j (N + 1)
  have h1 := LinearMap.finrank_range_add_finrank_ker (pencilT_bounded A B N)
  have hdom := finrank_boundedPolys (F := F) D N
  have hcod := finrank_boundedPolys (F := F) j (N + 1)
  have hle : Module.finrank F (LinearMap.range (pencilT_bounded A B N)) ≤ j * (N + 2) := by
    rw [← hcod]
    exact Submodule.finrank_le _
  rw [hdom] at h1
  nlinarith

end Pencil


section MinimalBasis

variable {F : Type*} [Field F]

-- Helper: write an element of Submodule.span F[X] (Set.range p) as ∑ t : Fin s, f t • p t
lemma mem_span_range_fin {D s : ℕ} (p : Fin s → Fin D → F[X]) {q : Fin D → F[X]}
    (hq : q ∈ Submodule.span F[X] (Set.range p)) :
    ∃ f : Fin s → F[X], ∑ t : Fin s, f t • p t = q := by
  rw [Submodule.mem_span_range_iff_exists_fun] at hq
  exact hq

-- Existence of a greedy minimal-degree basis of ker (pencilT A B) of length s ≤ D - j!
lemma exists_minimal_basis_aux {D j : ℕ} (A B : Matrix (Fin D) (Fin j) F)
    (s : ℕ) (hs : s ≤ D - j) :
    ∃ p : Fin s → (Fin D → F[X]),
      (∀ t, p t ∈ LinearMap.ker (pencilT A B)) ∧
      (∀ t, p t ≠ 0) ∧
      Monotone (fun t => vdeg (p t)) ∧
      (∀ t : Fin s, ∀ q ∈ LinearMap.ker (pencilT A B),
        q ∉ Submodule.span F[X] (Set.range (fun i : Fin t.val => p ⟨i.val, lt_trans i.isLt t.isLt⟩)) →
        vdeg (p t) ≤ vdeg q) ∧
      LinearIndependent F (fun t => leadVec (p t)) := by
  classical
  induction s with
  | zero =>
    refine ⟨Fin.elim0, fun t => t.elim0, fun t => t.elim0, fun a => a.elim0, fun t => t.elim0, ?_⟩
    exact linearIndependent_empty_type
  | succ s ih =>
    obtain ⟨p, hp_ker, hp_ne, hp_mono, hp_min, hp_ind⟩ := ih (Nat.le_of_succ_le hs)
    have hjD : j < D := by omega
    -- Show there exists q ∈ ker (pencilT A B) outside span_{F[X]} (range p)!
    have hex_out : ∃ q : Fin D → F[X], q ∈ LinearMap.ker (pencilT A B) ∧
        q ∉ Submodule.span F[X] (Set.range p) := by
      by_contra hall
      push Not at hall
      haveI : Module.Finite F (degreeLT F (j + 1)) := finite_degreeLT (F := F) (j + 1)
      let Lspan : (Fin s → degreeLT F (j + 1)) →ₗ[F] (Fin D → F[X]) :=
        { toFun := fun f => ∑ t : Fin s, (f t).val • p t
          map_add' := fun f g => by
            simp only [Pi.add_apply, Submodule.coe_add, add_smul, Finset.sum_add_distrib]
          map_smul' := fun c f => by
            simp only [Pi.smul_apply, SetLike.val_smul, RingHom.id_apply, Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro t _
            exact smul_assoc c (f t).val (p t) }
      let Kj : Submodule F (Fin D → F[X]) :=
        Submodule.map (boundedPolys (F := F) D j).subtype (LinearMap.ker (pencilT_bounded A B j))
      have hsub : Kj ≤ LinearMap.range Lspan := by
        intro q hq
        rcases Submodule.mem_map.mp hq with ⟨⟨qval, hq_bnd⟩, hq_ker, rfl⟩
        have hq_ker' : qval ∈ LinearMap.ker (pencilT A B) := by
          rw [LinearMap.mem_ker] at hq_ker ⊢
          exact congr_arg Subtype.val hq_ker
        have hq_span := hall qval hq_ker'
        rcases mem_span_range_fin p hq_span with ⟨f, hf⟩
        have hqvdeg : vdeg qval ≤ j := mem_boundedPolys_iff.mp hq_bnd
        have hf_deg : ∀ t : Fin s, f t ∈ degreeLT F (j + 1) := by
          intro t
          rw [mem_degreeLT]
          by_cases hft : f t = 0
          · simp [hft]
          · have ⟨_, hvdeg_eq⟩ := vdeg_linear_comb_eq p hp_ind f ⟨t, hft⟩
            rw [hf] at hvdeg_eq
            have hle_M : (f t).natDegree + vdeg (p t) ≤ vdeg qval := by
              rw [hvdeg_eq]
              have := Finset.le_sup (f := fun t : Fin s =>
                if f t = 0 then 0 else (f t).natDegree + vdeg (p t)) (Finset.mem_univ t)
              simpa [hft] using this
            rw [degree_eq_natDegree hft]
            exact Nat.cast_lt.mpr (by omega)
        exact ⟨fun t => ⟨f t, hf_deg t⟩, hf⟩
      have hfin_dom : Module.finrank F (Fin s → degreeLT F (j + 1)) = s * (j + 1) := by
        rw [Module.finrank_pi_fintype]
        have h1 : Module.finrank F (degreeLT F (j + 1)) = j + 1 := by
          rw [LinearEquiv.finrank_eq (degreeLTEquiv F (j + 1)), Module.finrank_pi, Fintype.card_fin]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, h1]
      have hfin_rng : Module.finrank F (LinearMap.range Lspan) ≤ s * (j + 1) := by
        rw [← hfin_dom]
        exact LinearMap.finrank_range_le Lspan
      have hfin_Kj : Module.finrank F Kj =
          Module.finrank F (LinearMap.ker (pencilT_bounded A B j)) :=
        Submodule.finrank_map_subtype_eq _ _
      have hfin_le : Module.finrank F Kj ≤ Module.finrank F (LinearMap.range Lspan) :=
        Submodule.finrank_mono hsub
      have hge := finrank_ker_pencilT_bounded_ge A B j
      have hs1 : s + 1 ≤ D - j := hs
      have hcontra : (j + 1) * D ≤ s * (j + 1) + (j + 2) * j := by omega
      have hD : D ≥ j + s + 1 := by omega
      nlinarith
    -- Pick ps outside span(p) of minimal vdeg!
    have hex_deg : ∃ d : ℕ, ∃ q ∈ LinearMap.ker (pencilT A B),
        q ∉ Submodule.span F[X] (Set.range p) ∧ vdeg q = d := by
      rcases hex_out with ⟨q, hq1, hq2⟩
      exact ⟨vdeg q, q, hq1, hq2, rfl⟩
    let d_min := Nat.find hex_deg
    have hd_spec := Nat.find_spec hex_deg
    obtain ⟨ps, hps_ker, hps_out, hps_deg⟩ := hd_spec
    have hps_min : ∀ q ∈ LinearMap.ker (pencilT A B),
        q ∉ Submodule.span F[X] (Set.range p) → vdeg ps ≤ vdeg q := by
      intro q hq1 hq2
      rw [hps_deg]
      exact Nat.find_min' hex_deg ⟨q, hq1, hq2, rfl⟩
    have hps_ne : ps ≠ 0 := by
      intro h0; rw [h0] at hps_out; exact hps_out (Submodule.zero_mem _)
    -- Extend p to p' : Fin (s + 1) → (Fin D → F[X]) via Fin.snoc
    let p' : Fin (s + 1) → (Fin D → F[X]) := Fin.snoc p ps
    have hp'_ker : ∀ t, p' t ∈ LinearMap.ker (pencilT A B) := by
      intro t
      refine Fin.lastCases ?_ ?_ t
      · simpa [p'] using hps_ker
      · intro i; simpa [p'] using hp_ker i
    have hp'_ne : ∀ t, p' t ≠ 0 := by
      intro t
      refine Fin.lastCases ?_ ?_ t
      · simpa [p'] using hps_ne
      · intro i; simpa [p'] using hp_ne i
    have hp'_mono_last : ∀ i : Fin s, vdeg (p i) ≤ vdeg ps := by
      intro i
      have hnot : ps ∉ Submodule.span F[X]
          (Set.range (fun k : Fin i.val => p ⟨k.val, lt_trans k.isLt i.isLt⟩)) := by
        intro hmem
        apply hps_out
        refine Submodule.span_mono ?_ hmem
        rintro _ ⟨k, rfl⟩
        exact ⟨⟨k.val, lt_trans k.isLt i.isLt⟩, rfl⟩
      exact hp_min i ps hps_ker hnot
    have hp'_mono : Monotone (fun t => vdeg (p' t)) := by
      intro a b
      refine Fin.lastCases ?_ ?_ b
      · refine Fin.lastCases ?_ ?_ a
        · intro _; exact le_refl _
        · intro i _; simpa [p'] using hp'_mono_last i
      · intro jb
        refine Fin.lastCases ?_ ?_ a
        · intro hle
          have := Fin.le_def.mp hle; simp at this; omega
        · intro ja hle
          simpa [p'] using hp_mono (Fin.castSucc_le_castSucc_iff.mp hle)
    have hp'_min : ∀ t : Fin (s + 1), ∀ q ∈ LinearMap.ker (pencilT A B),
        q ∉ Submodule.span F[X] (Set.range (fun i : Fin t.val => p' ⟨i.val, lt_trans i.isLt t.isLt⟩)) →
        vdeg (p' t) ≤ vdeg q := by
      intro t
      refine Fin.lastCases ?_ ?_ t
      · intro q hqk hqn
        simp only [p', Fin.snoc_last]
        apply hps_min q hqk
        intro hmem; apply hqn
        refine Submodule.span_mono ?_ hmem
        rintro _ ⟨i, rfl⟩
        exact ⟨⟨i.val, i.isLt⟩, by
          have hi : (⟨i.val, lt_trans i.isLt (Fin.last s).isLt⟩ : Fin (s + 1)) = i.castSucc := rfl
          dsimp only [p']; rw [hi, Fin.snoc_castSucc]⟩
      · intro i q hqk hqn
        simp only [p', Fin.snoc_castSucc]
        apply hp_min i q hqk
        intro hmem; apply hqn
        refine Submodule.span_mono ?_ hmem
        rintro _ ⟨k, rfl⟩
        exact ⟨⟨k.val, k.isLt⟩, by
          have hk : (⟨k.val, lt_trans k.isLt i.castSucc.isLt⟩ : Fin (s + 1)) =
            (⟨k.val, lt_trans k.isLt i.isLt⟩ : Fin s).castSucc := rfl
          dsimp only [p']; rw [hk, Fin.snoc_castSucc]⟩
    -- Prove leadVec (p' t) are F-linearly independent!
    have hp'_ind : LinearIndependent F (fun t => leadVec (p' t)) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      rw [Fin.sum_univ_castSucc] at hc
      simp only [p', Fin.snoc_castSucc, Fin.snoc_last] at hc
      by_cases hcs : c (Fin.last s) = 0
      · rw [hcs, zero_smul, add_zero] at hc
        have hc_init := (Fintype.linearIndependent_iff.mp hp_ind) (fun i => c i.castSucc) hc
        intro t
        refine Fin.lastCases hcs (fun i => hc_init i) t
      · -- Contradiction: build q ∈ ker \ span(p) with vdeg q < vdeg ps!
        exfalso
        let q : Fin D → F[X] :=
          ps + ∑ i : Fin s, (C ((c (Fin.last s))⁻¹ * c i.castSucc) * X ^ (vdeg ps - vdeg (p i))) • p i
        have hq_ker : q ∈ LinearMap.ker (pencilT A B) := by
          apply Submodule.add_mem _ hps_ker
          apply Submodule.sum_mem
          intro i _
          exact Submodule.smul_mem _ _ (hp_ker i)
        have hq_out : q ∉ Submodule.span F[X] (Set.range p) := by
          intro hq_in
          apply hps_out
          have hsum_in : ∑ i : Fin s,
              (C ((c (Fin.last s))⁻¹ * c i.castSucc) * X ^ (vdeg ps - vdeg (p i))) • p i ∈
              Submodule.span F[X] (Set.range p) := by
            apply Submodule.sum_mem
            intro i _
            exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
          have hps_eq : ps = q - ∑ i : Fin s,
              (C ((c (Fin.last s))⁻¹ * c i.castSucc) * X ^ (vdeg ps - vdeg (p i))) • p i := by
            simp [q]
          rw [hps_eq]
          exact Submodule.sub_mem _ hq_in hsum_in
        have hq_ne : q ≠ 0 := by intro h0; rw [h0] at hq_out; exact hq_out (Submodule.zero_mem _)
        have hq_vdeg_le : vdeg q ≤ vdeg ps := by
          rw [vdeg_le_iff]
          intro u
          simp only [q, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
          apply natDegree_add_le_of_degree_le
          · exact natDegree_le_vdeg ps u
          · apply natDegree_sum_le_of_forall_le
            intro i _
            have hle_i := hp'_mono_last i
            apply le_trans natDegree_mul_le
            have h1 : (C ((c (Fin.last s))⁻¹ * c i.castSucc) * X ^ (vdeg ps - vdeg (p i))).natDegree ≤ vdeg ps - vdeg (p i) :=
              natDegree_C_mul_X_pow_le _ _
            have h2 := natDegree_le_vdeg (p i) u
            omega
        -- Its coeffVec at vdeg ps is 0!
        have hq_coeff_zero : coeffVec q (vdeg ps) = 0 := by
          ext u
          simp only [q, coeffVec, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
            coeff_add, finsetSum_coeff, Pi.zero_apply]
          have hterm : ∀ i : Fin s,
              (C ((c (Fin.last s))⁻¹ * c i.castSucc) * X ^ (vdeg ps - vdeg (p i)) * p i u).coeff (vdeg ps) =
              (c (Fin.last s))⁻¹ * c i.castSucc * leadVec (p i) u := by
            intro i
            have hle_i := hp'_mono_last i
            rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul']
            rw [if_pos (by omega)]
            simp only [leadVec, coeffVec, show vdeg ps - (vdeg ps - vdeg (p i)) = vdeg (p i) by omega]
          rw [Finset.sum_congr rfl (fun i _ => hterm i)]
          have hcu := congr_fun hc u
          simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcu
          have hps_u : (ps u).coeff (vdeg ps) = leadVec ps u := rfl
          rw [hps_u]
          have hmul : (c (Fin.last s))⁻¹ * (∑ i : Fin s, c i.castSucc * leadVec (p i) u +
              c (Fin.last s) * leadVec ps u) = 0 := by rw [hcu, mul_zero]
          rw [mul_add, Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ hcs, one_mul] at hmul
          convert hmul using 1
          rw [add_comm]
          congr 1
          apply Finset.sum_congr rfl
          intro i _; ring
        -- If vdeg ps = 0, then vdeg q = 0 and leadVec q = 0, contradicting leadVec_ne_zero hq_ne!
        -- If vdeg ps > 0, then vdeg q < vdeg ps, contradicting hps_min!
        have hq_lt : vdeg q < vdeg ps := by
          apply lt_of_le_of_ne hq_vdeg_le
          intro heq
          have : leadVec q = 0 := by unfold leadVec; rw [heq]; exact hq_coeff_zero
          exact leadVec_ne_zero hq_ne this
        exact not_le_of_gt hq_lt (hps_min q hq_ker hq_out)
    exact ⟨p', hp'_ker, hp'_ne, hp'_mono, hp'_min, hp'_ind⟩

-- Now at s = r = D - j: prove p spans ALL of ker (pencilT A B), ∑ vdeg (p t) ≤ j,
-- and construct Phi : (Fin D → F[X]) →ₗ[F[X]] (Fin r → F[X]) with all properties!

lemma ker_AT_eq_span_leadVec {D j : ℕ} {A B : Matrix (Fin D) (Fin j) F}
    (hA : Function.Injective A.mulVecLin) (hjD : j < D)
    {p : Fin (D - j) → (Fin D → F[X])}
    (hp_ker : ∀ t, p t ∈ LinearMap.ker (pencilT A B))
    (hp_ind : LinearIndependent F (fun t => leadVec (p t))) :
    Submodule.span F (Set.range (fun t => leadVec (p t))) = LinearMap.ker Aᵀ.mulVecLin := by
  have hsub : Submodule.span F (Set.range (fun t => leadVec (p t))) ≤ LinearMap.ker Aᵀ.mulVecLin := by
    rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    exact leadVec_mem_ker_AT (hp_ker t)
  apply Submodule.eq_of_le_of_finrank_eq hsub
  rw [finrank_span_eq_card hp_ind, Fintype.card_fin]
  have hrank : A.rank = j := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hA, Module.finrank_pi, Fintype.card_fin]
  have hrankT : Aᵀ.rank = j := by rw [Matrix.rank_transpose, hrank]
  have hfin := LinearMap.finrank_range_add_finrank_ker Aᵀ.mulVecLin
  rw [← Matrix.rank, hrankT, Module.finrank_pi, Fintype.card_fin] at hfin
  omega

lemma span_minimal_basis_eq_ker {D j : ℕ} {A B : Matrix (Fin D) (Fin j) F}
    (hA : Function.Injective A.mulVecLin) (hjD : j < D)
    {p : Fin (D - j) → (Fin D → F[X])}
    (hp_ker : ∀ t, p t ∈ LinearMap.ker (pencilT A B))
    (hp_mono : Monotone (fun t => vdeg (p t)))
    (hp_min : ∀ t : Fin (D - j), ∀ q ∈ LinearMap.ker (pencilT A B),
      q ∉ Submodule.span F[X] (Set.range (fun i : Fin t.val => p ⟨i.val, lt_trans i.isLt t.isLt⟩)) →
      vdeg (p t) ≤ vdeg q)
    (hp_ind : LinearIndependent F (fun t => leadVec (p t))) :
    ∀ q ∈ LinearMap.ker (pencilT A B), q ∈ Submodule.span F[X] (Set.range p) := by
  classical
  have hspan_lead := ker_AT_eq_span_leadVec hA hjD hp_ker hp_ind
  -- Prove by strong induction on d = vdeg q!
  suffices h : ∀ d : ℕ, ∀ q ∈ LinearMap.ker (pencilT A B), vdeg q = d →
      q ∈ Submodule.span F[X] (Set.range p) by
    intro q hq; exact h (vdeg q) q hq rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro q hq hd
    by_contra hq_out
    have hq_ne : q ≠ 0 := by intro h0; rw [h0] at hq_out; exact hq_out (Submodule.zero_mem _)
    have hlead_mem : leadVec q ∈ Submodule.span F (Set.range (fun t => leadVec (p t))) := by
      rw [hspan_lead]
      exact leadVec_mem_ker_AT hq
    rw [Submodule.mem_span_range_iff_exists_fun] at hlead_mem
    obtain ⟨c, hc⟩ := hlead_mem
    -- Show c t = 0 whenever vdeg (p t) > d (otherwise hq_out contradicts hp_min t)!
    have hc_zero : ∀ t : Fin (D - j), d < vdeg (p t) → c t = 0 := by
      intro t hlt
      exfalso
      have hq_not_init : q ∉ Submodule.span F[X]
          (Set.range (fun i : Fin t.val => p ⟨i.val, lt_trans i.isLt t.isLt⟩)) := by
        intro hmem; apply hq_out
        refine Submodule.span_mono ?_ hmem
        rintro _ ⟨i, rfl⟩; exact ⟨⟨i.val, lt_trans i.isLt t.isLt⟩, rfl⟩
      have hge := hp_min t q hq hq_not_init
      omega
    -- Subtract ∑ t, (if vdeg (p t) ≤ d then C (c t) * X^(d - vdeg (p t)) else 0) • p t!
    let q' : Fin D → F[X] :=
      q - ∑ t : Fin (D - j), (if vdeg (p t) ≤ d then C (c t) * X ^ (d - vdeg (p t)) else 0) • p t
    have hsum_mem : ∑ t : Fin (D - j),
        (if vdeg (p t) ≤ d then C (c t) * X ^ (d - vdeg (p t)) else 0) • p t ∈
        Submodule.span F[X] (Set.range p) := by
      apply Submodule.sum_mem
      intro t _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
    have hq'_ker : q' ∈ LinearMap.ker (pencilT A B) := by
      apply Submodule.sub_mem _ hq
      apply Submodule.sum_mem
      intro t _
      exact Submodule.smul_mem _ _ (hp_ker t)
    have hq'_out : q' ∉ Submodule.span F[X] (Set.range p) := by
      intro hmem; apply hq_out
      have hq_eq : q = q' + ∑ t : Fin (D - j),
          (if vdeg (p t) ≤ d then C (c t) * X ^ (d - vdeg (p t)) else 0) • p t := by simp [q']
      rw [hq_eq]; exact Submodule.add_mem _ hmem hsum_mem
    have hq'_ne : q' ≠ 0 := by intro h0; rw [h0] at hq'_out; exact hq'_out (Submodule.zero_mem _)
    have hq'_vdeg_le : vdeg q' ≤ d := by
      rw [vdeg_le_iff]
      intro u
      simp only [q', Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply le_trans (natDegree_sub_le _ _)
      apply max_le
      · exact hd ▸ natDegree_le_vdeg q u
      · apply natDegree_sum_le_of_forall_le
        intro t _
        by_cases htd : vdeg (p t) ≤ d
        · rw [if_pos htd]
          apply le_trans natDegree_mul_le
          have h1 := natDegree_C_mul_X_pow_le (c t) (d - vdeg (p t))
          have h2 := natDegree_le_vdeg (p t) u
          omega
        · rw [if_neg htd, zero_mul, natDegree_zero]; exact Nat.zero_le _
    have hq'_coeff_zero : coeffVec q' d = 0 := by
      ext u
      simp only [q', coeffVec, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        coeff_sub, finsetSum_coeff, Pi.zero_apply]
      have hterm : ∀ t : Fin (D - j),
          ((if vdeg (p t) ≤ d then C (c t) * X ^ (d - vdeg (p t)) else 0) * p t u).coeff d =
          c t * leadVec (p t) u := by
        intro t
        by_cases htd : vdeg (p t) ≤ d
        · rw [if_pos htd, mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_pos (by omega)]
          simp [leadVec, coeffVec, show d - (d - vdeg (p t)) = vdeg (p t) by omega]
        · rw [if_neg htd, zero_mul, coeff_zero, hc_zero t (by omega), zero_mul]
      rw [Finset.sum_congr rfl (fun t _ => hterm t)]
      have hcu := congr_fun hc u
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hcu
      rw [hcu]
      unfold leadVec coeffVec
      rw [hd, sub_self]
    have hq'_lt : vdeg q' < d := by
      apply lt_of_le_of_ne hq'_vdeg_le
      intro heq
      exact leadVec_ne_zero hq'_ne (by unfold leadVec; rw [heq]; exact hq'_coeff_zero)
    exact hq'_out (ih (vdeg q') hq'_lt q' hq'_ker rfl)

lemma sum_vdeg_le {D j : ℕ} {A B : Matrix (Fin D) (Fin j) F}
    (hA : Function.Injective A.mulVecLin) (hjD : j < D)
    {p : Fin (D - j) → (Fin D → F[X])}
    (hp_ker : ∀ t, p t ∈ LinearMap.ker (pencilT A B))
    (hp_mono : Monotone (fun t => vdeg (p t)))
    (hp_min : ∀ t : Fin (D - j), ∀ q ∈ LinearMap.ker (pencilT A B),
      q ∉ Submodule.span F[X] (Set.range (fun i : Fin t.val => p ⟨i.val, lt_trans i.isLt t.isLt⟩)) →
      vdeg (p t) ≤ vdeg q)
    (hp_ind : LinearIndependent F (fun t => leadVec (p t))) :
    ∑ t : Fin (D - j), vdeg (p t) ≤ j := by
  classical
  have hspan := span_minimal_basis_eq_ker hA hjD hp_ker hp_mono hp_min hp_ind
  let N : ℕ := Finset.univ.sup (fun t : Fin (D - j) => vdeg (p t))
  have hleN : ∀ t : Fin (D - j), vdeg (p t) ≤ N :=
    fun t => Finset.le_sup (f := fun t : Fin (D - j) => vdeg (p t)) (Finset.mem_univ t)
  haveI : ∀ t : Fin (D - j), Module.Finite F (degreeLT F (N + 1 - vdeg (p t))) :=
    fun t => finite_degreeLT (F := F) (N + 1 - vdeg (p t))
  let L : (∀ t : Fin (D - j), degreeLT F (N + 1 - vdeg (p t))) →ₗ[F] (Fin D → F[X]) :=
    { toFun := fun f => ∑ t : Fin (D - j), (f t).val • p t
      map_add' := fun f g => by
        simp only [Pi.add_apply, Submodule.coe_add, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c f => by
        simp only [Pi.smul_apply, SetLike.val_smul, RingHom.id_apply, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro t _
        exact smul_assoc c (f t).val (p t) }
  let KN : Submodule F (Fin D → F[X]) :=
    Submodule.map (boundedPolys (F := F) D N).subtype (LinearMap.ker (pencilT_bounded A B N))
  have hsub : KN ≤ LinearMap.range L := by
    intro q hq
    rcases Submodule.mem_map.mp hq with ⟨⟨qval, hq_bnd⟩, hq_ker, rfl⟩
    have hq_ker' : qval ∈ LinearMap.ker (pencilT A B) := by
      rw [LinearMap.mem_ker] at hq_ker ⊢; exact congr_arg Subtype.val hq_ker
    rcases mem_span_range_fin p (hspan qval hq_ker') with ⟨f, hf⟩
    have hqvdeg : vdeg qval ≤ N := mem_boundedPolys_iff.mp hq_bnd
    have hf_deg : ∀ t : Fin (D - j), f t ∈ degreeLT F (N + 1 - vdeg (p t)) := by
      intro t
      rw [mem_degreeLT]
      by_cases hft : f t = 0
      · simp [hft]
      · have ⟨_, hvdeg_eq⟩ := vdeg_linear_comb_eq p hp_ind f ⟨t, hft⟩
        rw [hf] at hvdeg_eq
        have hle_M : (f t).natDegree + vdeg (p t) ≤ vdeg qval := by
          rw [hvdeg_eq]
          have := Finset.le_sup (f := fun t : Fin (D - j) =>
            if f t = 0 then 0 else (f t).natDegree + vdeg (p t)) (Finset.mem_univ t)
          simpa [hft] using this
        have hlt := hleN t
        rw [degree_eq_natDegree hft]
        exact Nat.cast_lt.mpr (by omega)
    exact ⟨fun t => ⟨f t, hf_deg t⟩, hf⟩
  have hfin_dom : Module.finrank F (∀ t : Fin (D - j), degreeLT F (N + 1 - vdeg (p t))) =
      ∑ t : Fin (D - j), (N + 1 - vdeg (p t)) := by
    rw [Module.finrank_pi_fintype]
    apply Finset.sum_congr rfl
    intro t _
    rw [LinearEquiv.finrank_eq (degreeLTEquiv F (N + 1 - vdeg (p t))), Module.finrank_pi,
      Fintype.card_fin]
  have hfin_rng : Module.finrank F (LinearMap.range L) ≤ ∑ t : Fin (D - j), (N + 1 - vdeg (p t)) := by
    rw [← hfin_dom]; exact LinearMap.finrank_range_le L
  have hfin_KN : Module.finrank F KN = Module.finrank F (LinearMap.ker (pencilT_bounded A B N)) :=
    Submodule.finrank_map_subtype_eq _ _
  have hfin_le : Module.finrank F KN ≤ Module.finrank F (LinearMap.range L) :=
    Submodule.finrank_mono hsub
  have hge := finrank_ker_pencilT_bounded_ge A B N
  have hsum_sub : (∑ t : Fin (D - j), (N + 1 - vdeg (p t))) + (∑ t : Fin (D - j), vdeg (p t)) =
      (D - j) * (N + 1) := by
    rw [← Finset.sum_add_distrib]
    have h1 : ∀ t : Fin (D - j), (N + 1 - vdeg (p t)) + vdeg (p t) = N + 1 :=
      fun t => by have := hleN t; omega
    rw [Finset.sum_congr rfl (fun t _ => h1 t), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  have hD : D = (D - j) + j := by omega
  nlinarith

-- Define Phi : (Fin D → F[X]) →ₗ[F[X]] (Fin r → F[X])
noncomputable def phiMap {D r : ℕ} (p : Fin r → (Fin D → F[X])) :
    (Fin D → F[X]) →ₗ[F[X]] (Fin r → F[X]) where
  toFun v t := ∑ u : Fin D, p t u * v u
  map_add' v w := by funext t; simp [mul_add, Finset.sum_add_distrib]
  map_smul' f v := by
    funext t
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _; ring

lemma phiMap_pencil {D j r : ℕ} {A B : Matrix (Fin D) (Fin j) F}
    {p : Fin r → (Fin D → F[X])} (hp_ker : ∀ t, p t ∈ LinearMap.ker (pencilT A B))
    (u : Fin j → F[X]) : phiMap p (pencil A B u) = 0 := by
  funext t
  simp only [phiMap, LinearMap.coe_mk, AddHom.coe_mk, pencil, Matrix.mulVecLin_apply,
    Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul, Pi.zero_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  have hi := congr_fun (LinearMap.mem_ker.mp (hp_ker t)) i
  simp only [pencilT, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.add_apply,
    Matrix.smul_apply, Matrix.map_apply, Matrix.transpose_apply, smul_eq_mul, Pi.zero_apply] at hi
  have hmul : ∑ x : Fin D, p t x * ((X * C (A x i) + C (B x i)) * u i) =
      (∑ x : Fin D, (X * C (A x i) + C (B x i)) * p t x) * u i := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro x _; ring
  rw [hmul, hi, zero_mul]

lemma range_A_eq_ker_leadDot {D j : ℕ} {A B : Matrix (Fin D) (Fin j) F}
    (hA : Function.Injective A.mulVecLin) (hjD : j < D)
    {p : Fin (D - j) → (Fin D → F[X])}
    (hp_ker : ∀ t, p t ∈ LinearMap.ker (pencilT A B))
    (hp_ind : LinearIndependent F (fun t => leadVec (p t)))
    (v : Fin D → F) (hv : ∀ t : Fin (D - j), ∑ u : Fin D, leadVec (p t) u * v u = 0) :
    v ∈ LinearMap.range A.mulVecLin := by
  let L : (Fin D → F) →ₗ[F] (Fin (D - j) → F) :=
    { toFun := fun w t => ∑ u : Fin D, leadVec (p t) u * w u
      map_add' := fun w1 w2 => by ext t; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c w => by
        ext t; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro u _; ring }
  -- L is surjective because its transpose matrix has columns leadVec (p t) which are linearly independent!
  let M : Matrix (Fin (D - j)) (Fin D) F := Matrix.of (fun t u => leadVec (p t) u)
  have hL_eq : L = M.mulVecLin := by
    ext v t; simp [L, M, Matrix.mulVec, dotProduct]
  have hMT_inj : Function.Injective Mᵀ.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    have hsum : ∑ t : Fin (D - j), c t • leadVec (p t) = 0 := by
      ext u
      have hu := congr_fun hc u
      simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
        M, Matrix.of_apply, Pi.zero_apply] at hu
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      convert hu using 1
      apply Finset.sum_congr rfl; intro t _; ring
    ext t
    exact (Fintype.linearIndependent_iff.mp hp_ind) c hsum t
  have hM_rank : M.rank = D - j := by
    rw [← Matrix.rank_transpose, Matrix.rank, LinearMap.finrank_range_of_inj hMT_inj,
      Module.finrank_pi, Fintype.card_fin]
  have hkerL_fin : Module.finrank F (LinearMap.ker L) = j := by
    have hrange : Module.finrank F (LinearMap.range L) = D - j := by
      rw [hL_eq, ← Matrix.rank, hM_rank]
    have hfin := LinearMap.finrank_range_add_finrank_ker L
    rw [hrange, Module.finrank_pi, Fintype.card_fin] at hfin
    omega
  have hsub : LinearMap.range A.mulVecLin ≤ LinearMap.ker L := by
    rintro _ ⟨u, rfl⟩
    rw [LinearMap.mem_ker]
    ext t
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVecLin_apply, Matrix.mulVec,
      dotProduct, Pi.zero_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i _
    have hi := congr_fun (leadVec_mem_ker_AT (hp_ker t)) i
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] at hi
    have : ∑ x : Fin D, leadVec (p t) x * (A x i * u i) =
        (∑ x : Fin D, A x i * leadVec (p t) x) * u i := by
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro x _; ring
    rw [this, hi, zero_mul]
  have heq : LinearMap.range A.mulVecLin = LinearMap.ker L := by
    apply Submodule.eq_of_le_of_finrank_eq hsub
    rw [LinearMap.finrank_range_of_inj hA, Module.finrank_pi, Fintype.card_fin, hkerL_fin]
  rw [heq, LinearMap.mem_ker]
  ext t; exact hv t

-- Key lemma: no nonzero constant vector lies in ker (phiMap p)!
lemma ker_phiMap_const_eq_zero {D j : ℕ} {A B : Matrix (Fin D) (Fin j) F}
    (hnd : NondegenerateRect A B) (hjD : j < D)
    {p : Fin (D - j) → (Fin D → F[X])}
    (hp_ker : ∀ t, p t ∈ LinearMap.ker (pencilT A B))
    (hp_ind : LinearIndependent F (fun t => leadVec (p t)))
    (v : Fin D → F) (hv : phiMap p (fun u => C (v u)) = 0) : v = 0 := by
  have hA_map : Function.Injective (A.map (algebraMap F (AC F))).mulVecLin := by
    have h := (nondegenerateRect_iff_injective A B).mp hnd 1 0 (by simp)
    simpa using h
  have hA : Function.Injective A.mulVecLin := mulVecLin_injective_of_map_injective A hA_map
  -- Any constant w in ker (phiMap p) lies in range A.mulVecLin!
  have hmemA : ∀ w : Fin D → F, phiMap p (fun u => C (w u)) = 0 →
      w ∈ LinearMap.range A.mulVecLin := by
    intro w hw
    apply range_A_eq_ker_leadDot hA hjD hp_ker hp_ind
    intro t
    have ht := congr_arg (fun f : F[X] => f.coeff (vdeg (p t))) (congr_fun hw t)
    simp only [phiMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, finsetSum_coeff,
      coeff_mul_C, coeff_zero] at ht
    exact ht
  -- Define U = {u : Fin j → F | phiMap p (C ∘ (A *ᵥ u)) = 0}
  let U : Submodule F (Fin j → F) :=
    { carrier := {u | phiMap p (fun x => C ((A *ᵥ u) x)) = 0}
      add_mem' := fun {u1 u2} h1 h2 => by
        change phiMap p (fun x => C ((A *ᵥ (u1 + u2)) x)) = 0
        have heq : (fun x => C ((A *ᵥ (u1 + u2)) x)) =
            (fun x => C ((A *ᵥ u1) x)) + (fun x => C ((A *ᵥ u2) x)) := by
          funext x; simp [Matrix.mulVec_add, map_add]
        rw [heq, map_add, h1, h2, add_zero]
      zero_mem' := by
        change phiMap p (fun x => C ((A *ᵥ 0) x)) = 0
        have heq : (fun x => C ((A *ᵥ 0) x)) = 0 := by funext x; simp
        rw [heq, map_zero]
      smul_mem' := fun c {u} hu => by
        change phiMap p (fun x => C ((A *ᵥ (c • u)) x)) = 0
        have heq : (fun x => C ((A *ᵥ (c • u)) x)) = C c • (fun x => C ((A *ᵥ u) x)) := by
          funext x; simp [Matrix.mulVec_smul, map_mul]
        rw [heq, map_smul, hu, smul_zero] }
  -- For u ∈ U, B *ᵥ u ∈ ker (phiMap p) ⊆ range A!
  have hBU : ∀ u ∈ U, ∃ u' ∈ U, A *ᵥ u' = B *ᵥ u := by
    intro u hu
    have hphiB : phiMap p (fun x => C ((B *ᵥ u) x)) = 0 := by
      have hpenc := phiMap_pencil hp_ker (fun i => C (u i))
      have hsplit : pencil A B (fun i => C (u i)) =
          (X : F[X]) • (fun x => C ((A *ᵥ u) x)) + (fun x => C ((B *ᵥ u) x)) := by
        funext x
        simp only [pencil, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.add_apply,
          Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Pi.add_apply, Pi.smul_apply,
          map_sum, map_mul, Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _; ring
      rw [hsplit, map_add, map_smul, hu, smul_zero, zero_add] at hpenc
      exact hpenc
    rcases hmemA (B *ᵥ u) hphiB with ⟨u', hu'⟩
    simp only [Matrix.mulVecLin_apply] at hu'
    refine ⟨u', ?_, hu'⟩
    change phiMap p (fun x => C ((A *ᵥ u') x)) = 0
    rw [hu']; exact hphiB
  -- Show U = ⊥ using eigenvalue over AC F!
  have hUbot : U = ⊥ := by
    by_contra hUne
    have hpos : 0 < Module.finrank F U := by
      by_contra h0
      exact hUne (Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_not_pos h0))
    set m := Module.finrank F U
    haveI : NeZero m := ⟨Nat.ne_of_gt hpos⟩
    -- Build T : U →ₗ[F] U with A *ᵥ (T u).val = B *ᵥ u.val
    choose Tf hTfU hTfEq using fun u : U => hBU u.val u.2
    let T : U →ₗ[F] U :=
      { toFun := fun u => ⟨Tf u, hTfU u⟩
        map_add' := fun u1 u2 => Subtype.ext (hA (by
          change A *ᵥ Tf (u1 + u2) = A *ᵥ (Tf u1 + Tf u2)
          rw [hTfEq, Matrix.mulVec_add, hTfEq, hTfEq, Submodule.coe_add, Matrix.mulVec_add]))
        map_smul' := fun c u => Subtype.ext (hA (by
          change A *ᵥ Tf (c • u) = A *ᵥ (c • Tf u)
          rw [hTfEq, Matrix.mulVec_smul, hTfEq, SetLike.val_smul, Matrix.mulVec_smul])) }
    let e : Module.Basis (Fin m) F U := Module.finBasis F U
    let MT : Matrix (Fin m) (Fin m) F := LinearMap.toMatrix e e T
    let E : Matrix (Fin j) (Fin m) F := Matrix.of (fun i a => (e a).val i)
    have hEA : A * E * MT = B * E := by
      ext x a
      have hTa : A *ᵥ (T (e a)).val = B *ᵥ (e a).val := hTfEq (e a)
      have hx := congr_fun hTa x
      have hrepr : (T (e a)).val = ∑ b : Fin m, MT b a • (e b).val := by
        have h1 := (e.sum_repr (T (e a))).symm
        have h2 := congr_arg Subtype.val h1
        simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at h2
        rw [h2]
        apply Finset.sum_congr rfl
        intro b _
        congr 1
        simp [MT, LinearMap.toMatrix_apply]
      rw [hrepr] at hx
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hx
      simp only [Matrix.mul_apply, E, Matrix.of_apply]
      rw [← hx]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro i _; ring
    have hE_inj : Function.Injective E.mulVecLin := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro w hw
      have hlin : ∑ a : Fin m, w a • e a = 0 := by
        apply Subtype.ext
        ext i
        have hi := congr_fun hw i
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, E, Matrix.of_apply,
          Pi.zero_apply] at hi
        simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul, Submodule.coe_zero, Pi.zero_apply]
        convert hi using 1
        apply Finset.sum_congr rfl; intro a _; ring
      ext a
      exact (Fintype.linearIndependent_iff.mp e.linearIndependent) w hlin a
    have hE_map_inj := map_mulVecLin_injective_of_injective E hE_inj
    -- Over AC F, MT.map φ has an eigenvalue μ and eigenvector w ≠ 0!
    let φ := algebraMap F (AC F)
    haveI : Nontrivial (Fin m → AC F) := inferInstance
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (MT.map φ).mulVecLin
    obtain ⟨w, hw_mem, hw_ne⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hμ
    have hw_eq : (MT.map φ) *ᵥ w = μ • w := by
      have := Module.End.mem_eigenspace_iff.mp hw_mem
      simpa using this
    let vbar : Fin j → AC F := (E.map φ) *ᵥ w
    have hvbar_ne : vbar ≠ 0 := by
      intro h0
      exact hw_ne (hE_map_inj (h0.trans (map_zero _).symm))
    have hEA_map : (A.map φ) * (E.map φ) * (MT.map φ) = (B.map φ) * (E.map φ) := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, hEA]
    have hBv : (B.map φ) *ᵥ vbar = μ • ((A.map φ) *ᵥ vbar) := by
      dsimp only [vbar]
      rw [Matrix.mulVec_mulVec, ← hEA_map, ← Matrix.mulVec_mulVec, hw_eq,
        Matrix.mulVec_smul, Matrix.mulVec_mulVec]
    have hzero : ((-μ) • (A.map φ) + (1 : AC F) • (B.map φ)) *ᵥ vbar = 0 := by
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, one_smul, hBv, neg_smul,
        neg_add_cancel]
    have hinj := (nondegenerateRect_iff_injective A B).mp hnd (-μ) 1 (by simp)
    exact hvbar_ne (hinj (hzero.trans (map_zero _).symm))
  rcases hmemA v hv with ⟨u, rfl⟩
  have hu : u ∈ U := hv
  rw [hUbot, Submodule.mem_bot] at hu
  simp [hu]

end MinimalBasis



-- Part 3: phiConstEquiv -> grand_master_step -> column_induction -> main!
-- Assumes OMA_A2602_Part1 (card_coprime_affine, IsCoprimeTuple) and OMA_A2602_Part2 (Pencil, MinimalBasis)

section GrandMaster

open Polynomial BigOperators Matrix

variable {F : Type*} [Field F]

-- Snoc a column onto a Matrix (Fin D) (Fin j) R
def snocCol {R : Type*} {D j : ℕ} (A : Matrix (Fin D) (Fin j) R) (a : Fin D → R) :
    Matrix (Fin D) (Fin (j + 1)) R :=
  Matrix.of (fun r c => Fin.lastCases (a r) (fun i => A r i) c)

lemma snocCol_apply_castSucc {R : Type*} {D j : ℕ} (A : Matrix (Fin D) (Fin j) R) (a : Fin D → R)
    (r : Fin D) (i : Fin j) : snocCol A a r i.castSucc = A r i := by
  simp [snocCol]

lemma snocCol_apply_last {R : Type*} {D j : ℕ} (A : Matrix (Fin D) (Fin j) R) (a : Fin D → R)
    (r : Fin D) : snocCol A a r (Fin.last j) = a r := by
  simp [snocCol]

lemma snocCol_map {R K : Type*} [CommRing R] [CommRing K] {D j : ℕ} (φ : R →+* K)
    (A : Matrix (Fin D) (Fin j) R) (a : Fin D → R) :
    (snocCol A a).map φ = snocCol (A.map φ) (fun r => φ (a r)) := by
  ext r c
  refine Fin.lastCases ?_ ?_ c
  · simp [snocCol]
  · intro i; simp [snocCol]

lemma snocCol_mulVec {D j : ℕ} {K : Type*} [CommRing K]
    (A : Matrix (Fin D) (Fin j) K) (a : Fin D → K) (v : Fin (j + 1) → K) :
    snocCol A a *ᵥ v = A *ᵥ (fun i => v i.castSucc) + v (Fin.last j) • a := by
  ext r
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, snocCol_apply_castSucc,
    snocCol_apply_last, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

-- Extract phiConstEquiv, sum_vdeg_eq, phiMap_surjective, ker_phiMap_eq_range_pencil!
lemma pencil_quotient_data {D j : ℕ} {A B : Matrix (Fin D) (Fin j) F}
    (hnd : NondegenerateRect A B) (hjD : j < D) :
    ∃ (p : Fin (D - j) → (Fin D → F[X])),
      (∀ t, p t ∈ LinearMap.ker (pencilT A B)) ∧
      (∑ t : Fin (D - j), vdeg (p t) = j) ∧
      (∀ t : Fin (D - j), ∀ v : Fin D → F, phiMap p (fun u => C (v u)) t ∈ degreeLT F (vdeg (p t) + 1)) ∧
      (Function.Bijective (fun (v : Fin D → F) (t : Fin (D - j)) =>
        (⟨phiMap p (fun u => C (v u)) t, by
          simp only [phiMap, LinearMap.coe_mk, AddHom.coe_mk, mem_degreeLT]
          apply lt_of_le_of_lt (degree_sum_le _ _)
          rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
          intro u _
          have h1 : (p t u * C (v u)).degree ≤ (p t u).degree := by
            by_cases hv : v u = 0
            · simp [hv]
            · rw [degree_mul_C hv]
          have h2 : (p t u).degree < ((vdeg (p t) + 1 : ℕ) : WithBot ℕ) := by
            by_cases hp0 : p t u = 0
            · simp [hp0]
            · rw [degree_eq_natDegree hp0]
              exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le (natDegree_le_vdeg (p t) u))
          exact lt_of_le_of_lt h1 h2⟩ : degreeLT F (vdeg (p t) + 1)))) ∧
      (Function.Surjective (phiMap p)) ∧
      (∀ v : Fin D → F[X], phiMap p v = 0 ↔ v ∈ LinearMap.range (pencil A B)) ∧
      (∀ a : Fin D → F, a ∉ LinearMap.range A.mulVecLin →
        ∃ t : Fin (D - j), (phiMap p (fun u => C (a u)) t).coeff (vdeg (p t)) ≠ 0) := by
  have hA_map : Function.Injective (A.map (algebraMap F (AC F))).mulVecLin := by
    simpa using (nondegenerateRect_iff_injective A B).mp hnd 1 0 (by simp)
  have hA : Function.Injective A.mulVecLin := mulVecLin_injective_of_map_injective A hA_map
  obtain ⟨p, hp_ker, hp_ne, hp_mono, hp_min, hp_ind⟩ :=
    exists_minimal_basis_aux A B (D - j) (le_refl _)
  have hsum_le : ∑ t : Fin (D - j), vdeg (p t) ≤ j :=
    sum_vdeg_le hA hjD hp_ker hp_mono hp_min hp_ind
  have hdeg_mem : ∀ (t : Fin (D - j)) (v : Fin D → F),
      phiMap p (fun u => C (v u)) t ∈ degreeLT F (vdeg (p t) + 1) := by
    intro t v
    simp only [phiMap, LinearMap.coe_mk, AddHom.coe_mk, mem_degreeLT]
    apply lt_of_le_of_lt (degree_sum_le _ _)
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro u _
    have h1 : (p t u * C (v u)).degree ≤ (p t u).degree := by
      by_cases hv : v u = 0
      · simp [hv]
      · rw [degree_mul_C hv]
    have h2 : (p t u).degree < ((vdeg (p t) + 1 : ℕ) : WithBot ℕ) := by
      by_cases hp0 : p t u = 0
      · simp [hp0]
      · rw [degree_eq_natDegree hp0]
        exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le (natDegree_le_vdeg (p t) u))
    exact lt_of_le_of_lt h1 h2
  -- F-linear map phiConst : (Fin D → F) →ₗ[F] (∀ t, degreeLT F (vdeg (p t) + 1))
  let phiConst : (Fin D → F) →ₗ[F] (∀ t : Fin (D - j), degreeLT F (vdeg (p t) + 1)) :=
    { toFun := fun v t => ⟨phiMap p (fun u => C (v u)) t, hdeg_mem t v⟩
      map_add' := fun v1 v2 => by
        funext t
        apply Subtype.ext
        have heq : (fun u => C ((v1 + v2) u)) = (fun u => C (v1 u)) + (fun u => C (v2 u)) := by
          funext u; simp [map_add]
        change phiMap p (fun u => C ((v1 + v2) u)) t =
          phiMap p (fun u => C (v1 u)) t + phiMap p (fun u => C (v2 u)) t
        rw [heq, map_add, Pi.add_apply]
      map_smul' := fun c v => by
        funext t
        apply Subtype.ext
        have heq : (fun u => C ((c • v) u)) = C c • (fun u => C (v u)) := by
          funext u; simp [map_mul]
        change phiMap p (fun u => C ((c • v) u)) t = c • phiMap p (fun u => C (v u)) t
        rw [heq, map_smul, Pi.smul_apply, smul_eq_mul, Polynomial.smul_eq_C_mul] }
  have hphiConst_inj : Function.Injective phiConst := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    apply ker_phiMap_const_eq_zero hnd hjD hp_ker hp_ind
    funext t
    have ht := congr_fun hv t
    exact congr_arg Subtype.val ht
  haveI : ∀ t : Fin (D - j), Module.Finite F (degreeLT F (vdeg (p t) + 1)) :=
    fun t => finite_degreeLT (F := F) (vdeg (p t) + 1)
  have hfin_cod : Module.finrank F (∀ t : Fin (D - j), degreeLT F (vdeg (p t) + 1)) =
      ∑ t : Fin (D - j), (vdeg (p t) + 1) := by
    rw [Module.finrank_pi_fintype]
    apply Finset.sum_congr rfl
    intro t _
    rw [LinearEquiv.finrank_eq (degreeLTEquiv F (vdeg (p t) + 1)), Module.finrank_pi, Fintype.card_fin]
  have hD_le : D ≤ ∑ t : Fin (D - j), (vdeg (p t) + 1) := by
    have h1 := LinearMap.finrank_le_finrank_of_injective hphiConst_inj
    rw [Module.finrank_pi, Fintype.card_fin, hfin_cod] at h1
    exact h1
  have hsum_add : ∑ t : Fin (D - j), (vdeg (p t) + 1) = (∑ t : Fin (D - j), vdeg (p t)) + (D - j) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one]
  have hsum_eq : ∑ t : Fin (D - j), vdeg (p t) = j := by omega
  have hfin_eq : Module.finrank F (Fin D → F) =
      Module.finrank F (∀ t : Fin (D - j), degreeLT F (vdeg (p t) + 1)) := by
    rw [Module.finrank_pi, Fintype.card_fin, hfin_cod, hsum_add, hsum_eq]; omega
  have hphiConst_bij : Function.Bijective phiConst :=
    ⟨hphiConst_inj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin_eq).mp hphiConst_inj⟩
  -- Surjectivity of phiMap p over F[X]: every basis vector Pi.single t 1 is in range phiConst!
  have hphi_surj : Function.Surjective (phiMap p) := by
    have hsingle : ∀ t0 : Fin (D - j), ∃ w : Fin D → F, phiMap p (fun u => C (w u)) = Pi.single t0 1 := by
      intro t0
      let target : ∀ t : Fin (D - j), degreeLT F (vdeg (p t) + 1) :=
        fun t => ⟨(Pi.single t0 (1 : F[X]) : Fin (D - j) → F[X]) t, by
          by_cases h : t = t0
          · subst h
            rw [mem_degreeLT, Pi.single_eq_same, degree_one]
            exact Nat.cast_pos.mpr (Nat.succ_pos _)
          · simp [Pi.single_eq_of_ne h]⟩
      obtain ⟨w, hw⟩ := hphiConst_bij.2 target
      refine ⟨w, ?_⟩
      funext t
      exact congr_arg Subtype.val (congr_fun hw t)
    choose e he using hsingle
    intro q
    refine ⟨∑ t0 : Fin (D - j), q t0 • (fun u => C (e t0 u)), ?_⟩
    rw [map_sum]
    funext t
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, he]
    rw [Finset.sum_eq_single t]
    · simp
    · intro t0 _ hne; simp [Pi.single_eq_of_ne (Ne.symm hne)]
    · intro h; exact absurd (Finset.mem_univ t) h
  -- ker (phiMap p) = range (pencil A B) by strong induction on vdeg v!
  have hker_eq : ∀ v : Fin D → F[X], phiMap p v = 0 ↔ v ∈ LinearMap.range (pencil A B) := by
    intro v
    constructor
    · suffices h : ∀ d : ℕ, ∀ v : Fin D → F[X], vdeg v = d → phiMap p v = 0 →
          v ∈ LinearMap.range (pencil A B) by
        exact h (vdeg v) v rfl
      intro d
      induction d using Nat.strong_induction_on with
      | h d ih =>
        intro v hd hv0
        rcases d with _ | d'
        · -- vdeg v = 0 => v is constant!
          have hv_const : v = fun u => C ((v u).coeff 0) := by
            funext u
            exact Polynomial.eq_C_of_natDegree_eq_zero (Nat.le_zero.mp (hd ▸ natDegree_le_vdeg v u))
          rw [hv_const] at hv0 ⊢
          have h0 := ker_phiMap_const_eq_zero hnd hjD hp_ker hp_ind (fun u => (v u).coeff 0) hv0
          refine ⟨0, ?_⟩
          funext u; simp [congr_fun h0 u]
        · -- vdeg v = d' + 1 => leadVec v ⊥ leadVec (p t), so leadVec v ∈ range A!
          have hdot : ∀ t : Fin (D - j), ∑ u : Fin D, leadVec (p t) u * leadVec v u = 0 := by
            intro t
            have ht := congr_arg (fun f : F[X] => f.coeff (vdeg (p t) + (d' + 1))) (congr_fun hv0 t)
            simp only [phiMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, finsetSum_coeff,
              coeff_zero] at ht
            rw [← ht]
            apply Finset.sum_congr rfl
            intro u _
            rw [Polynomial.coeff_mul]
            rw [Finset.sum_eq_single (vdeg (p t), d' + 1)]
            · simp [leadVec, coeffVec, hd]
            · intro x hx hne
              rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
              rcases lt_or_gt_of_ne (show x.1 ≠ vdeg (p t) by
                intro h1; exact hne (Prod.ext h1 (by omega))) with hlt | hgt
              · have h2gt : d' + 1 < x.2 := by omega
                rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hd ▸ natDegree_le_vdeg v u) h2gt),
                  mul_zero]
              · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_le_vdeg (p t) u) hgt),
                  zero_mul]
            · intro h; exact (h (Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl)).elim
          rcases range_A_eq_ker_leadDot hA hjD hp_ker hp_ind (leadVec v) hdot with ⟨w, hw⟩
          let sub_term : Fin D → F[X] := pencil A B (fun i => C (w i) * X ^ d')
          let v' : Fin D → F[X] := v - sub_term
          have hv'_phi : phiMap p v' = 0 := by
            simp only [v', sub_term, map_sub, hv0, phiMap_pencil hp_ker, sub_self]
          have hv'_le : vdeg v' ≤ d' + 1 := by
            rw [vdeg_le_iff]
            intro u
            simp only [v', sub_term, Pi.sub_apply, pencil, Matrix.mulVecLin_apply, Matrix.mulVec,
              dotProduct, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
            apply le_trans (natDegree_sub_le _ _)
            apply max_le
            · exact hd ▸ natDegree_le_vdeg v u
            · apply natDegree_sum_le_of_forall_le
              intro i _
              apply le_trans natDegree_mul_le
              have h1 : (X * C (A u i) + C (B u i)).natDegree ≤ 1 := by
                apply natDegree_add_le_of_degree_le
                · exact le_trans natDegree_mul_le (by simp [natDegree_X, natDegree_C])
                · simp [natDegree_C]
              have h2 := natDegree_C_mul_X_pow_le (w i) d'
              omega
          have hv'_coeff : coeffVec v' (d' + 1) = 0 := by
            ext u
            simp only [v', sub_term, coeffVec, Pi.sub_apply, coeff_sub, Pi.zero_apply,
              pencil, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.add_apply,
              Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, finsetSum_coeff]
            have hterm : ∀ i : Fin j,
                ((X * C (A u i) + C (B u i)) * (C (w i) * X ^ d')).coeff (d' + 1) = A u i * w i := by
              intro i
              have hexp : (X * C (A u i) + C (B u i)) * (C (w i) * X ^ d') =
                  C (A u i * w i) * X ^ (d' + 1) + C (B u i * w i) * X ^ d' := by
                rw [map_mul, map_mul, pow_succ]; ring
              rw [hexp, coeff_add, coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one,
                coeff_C_mul, coeff_X_pow, if_neg (by omega), mul_zero, add_zero]
            rw [Finset.sum_congr rfl (fun i _ => hterm i)]
            have hwu := congr_fun hw u
            simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, leadVec, coeffVec, hd] at hwu
            rw [hwu, sub_self]
          have hv'_lt : vdeg v' < d' + 1 := by
            by_cases h0 : v' = 0
            · simp [h0, vdeg]
            · apply lt_of_le_of_ne hv'_le
              intro heq
              exact leadVec_ne_zero h0 (by unfold leadVec; rw [heq]; exact hv'_coeff)
          rcases ih (vdeg v') hv'_lt v' rfl hv'_phi with ⟨u', hu'⟩
          refine ⟨u' + fun i => C (w i) * X ^ d', ?_⟩
          rw [map_add, hu']
          simp [v', sub_term]
    · rintro ⟨u, rfl⟩
      exact phiMap_pencil hp_ker u
  -- Nonvanishing of top coeff for a ∉ range A!
  have ha_ne : ∀ a : Fin D → F, a ∉ LinearMap.range A.mulVecLin →
      ∃ t : Fin (D - j), (phiMap p (fun u => C (a u)) t).coeff (vdeg (p t)) ≠ 0 := by
    intro a ha
    by_contra hall
    push Not at hall
    apply ha
    apply range_A_eq_ker_leadDot hA hjD hp_ker hp_ind a
    intro t
    have ht := hall t
    simp only [phiMap, LinearMap.coe_mk, AddHom.coe_mk, finsetSum_coeff, coeff_mul_C] at ht
    exact ht
  exact ⟨p, hp_ker, hsum_eq, hdeg_mem, hphiConst_bij, hphi_surj, hker_eq, ha_ne⟩

-- Equivalence between NondegenerateRect (snocCol A a) (snocCol B b) and IsCoprimeTuple (phiMap p (X a + b))!
lemma nondegenerateRect_snoc_iff_coprime {D j : ℕ} {A B : Matrix (Fin D) (Fin j) F}
    (hnd : NondegenerateRect A B) (hjD : j < D)
    {p : Fin (D - j) → (Fin D → F[X])}
    (hp_ker : ∀ t, p t ∈ LinearMap.ker (pencilT A B))
    (hphi_surj : Function.Surjective (phiMap p))
    (hker_eq : ∀ v : Fin D → F[X], phiMap p v = 0 ↔ v ∈ LinearMap.range (pencil A B))
    {a : Fin D → F} (ha : a ∉ LinearMap.range A.mulVecLin) (b : Fin D → F) :
    NondegenerateRect (snocCol A a) (snocCol B b) ↔
      IsCoprimeTuple (phiMap p (fun u => X * C (a u) + C (b u))) := by
  let φ := algebraMap F (AC F)
  have hA_map : Function.Injective (A.map φ).mulVecLin := by
    simpa using (nondegenerateRect_iff_injective A B).mp hnd 1 0 (by simp)
  have hA : Function.Injective A.mulVecLin := mulVecLin_injective_of_map_injective A hA_map
  have hAa_inj : Function.Injective (snocCol A a).mulVecLin := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, snocCol_mulVec] at hv
    by_cases hlast : v (Fin.last j) = 0
    · rw [hlast, zero_smul, add_zero] at hv
      have hinit : (fun i : Fin j => v i.castSucc) = 0 := hA (hv.trans (map_zero _).symm)
      ext c
      exact Fin.lastCases hlast (fun i => congr_fun hinit i) c
    · exfalso
      apply ha
      refine ⟨-(v (Fin.last j))⁻¹ • (fun i => v i.castSucc), ?_⟩
      change A *ᵥ (-(v (Fin.last j))⁻¹ • (fun i => v i.castSucc)) = a
      rw [Matrix.mulVec_smul]
      have h1 : v (Fin.last j) • a = -(A *ᵥ (fun i => v i.castSucc)) := eq_neg_of_add_eq_zero_right hv
      have h2 := congr_arg (fun x => (v (Fin.last j))⁻¹ • x) h1
      simp only [smul_smul, inv_mul_cancel₀ hlast, one_smul, smul_neg] at h2
      rw [neg_smul, h2]
  have hAa_map_inj := map_mulVecLin_injective_of_injective (snocCol A a) hAa_inj
  constructor
  · -- Nondegenerate → IsCoprimeTuple
    intro hnd' g hgm hg
    by_contra hg1
    have hdeg_pos : 0 < g.natDegree := by
      by_contra h0
      exact hg1 (Polynomial.eq_one_of_monic_natDegree_zero hgm (Nat.eq_zero_of_not_pos h0))
    have hmap_deg : (g.map φ).degree ≠ 0 := by
      rw [Polynomial.degree_map_eq_of_injective φ.injective,
        Polynomial.degree_eq_natDegree hgm.ne_zero]
      intro h0
      have : g.natDegree = 0 := WithBot.coe_eq_coe.mp h0
      omega
    obtain ⟨lam, hlam⟩ := IsAlgClosed.exists_root (g.map φ) hmap_deg
    have haeval_g : aeval lam g = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      exact hlam
    choose q hq using hg
    obtain ⟨w, hw⟩ := hphi_surj q
    have hphi_sub : phiMap p ((fun u => X * C (a u) + C (b u)) - g • w) = 0 := by
      rw [map_sub, map_smul, hw]
      funext t
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hq t, sub_self, Pi.zero_apply]
    rcases (hker_eq _).mp hphi_sub with ⟨u, hu⟩
    -- Apply aeval lam to both sides of hu!
    let v_ac : Fin (j + 1) → AC F :=
      Fin.snoc (fun i : Fin j => -(aeval lam (u i))) (1 : AC F)
    have hv_ne : v_ac ≠ 0 := by
      intro h0
      have := congr_fun h0 (Fin.last j)
      simp [v_ac] at this
    have hker_v : (lam • (snocCol A a).map φ + (1 : AC F) • (snocCol B b).map φ) *ᵥ v_ac = 0 := by
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, one_smul,
        snocCol_map, snocCol_map, snocCol_mulVec, snocCol_mulVec]
      ext r
      have hr := congr_arg (aeval lam) (congr_fun hu r)
      rw [pencil, Matrix.mulVecLin_apply] at hr
      simp only [Matrix.mulVec, dotProduct, Matrix.add_apply,
        Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Pi.sub_apply, Pi.smul_apply,
        map_sum, map_add, map_sub, map_mul, aeval_X, aeval_C, haeval_g, zero_mul, sub_zero] at hr
      simp only [Pi.add_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
        smul_eq_mul, v_ac, Fin.snoc_castSucc, Fin.snoc_last, one_smul, Pi.zero_apply]
      rw [mul_add, Finset.mul_sum]
      have hrearr : (∑ i : Fin j, lam * (φ (A r i) * -aeval lam (u i))) + lam * φ (a r) +
          ((∑ i : Fin j, φ (B r i) * -aeval lam (u i)) + φ (b r)) =
          (∑ i : Fin j, (lam * (φ (A r i) * -aeval lam (u i)) + φ (B r i) * -aeval lam (u i))) +
          (lam * φ (a r) + φ (b r)) := by
        rw [Finset.sum_add_distrib]; ring
      rw [hrearr]
      have hsum_eq : ∑ i : Fin j, (lam * (φ (A r i) * -aeval lam (u i)) + φ (B r i) * -aeval lam (u i)) =
          -(∑ i : Fin j, (lam * φ (A r i) + φ (B r i)) * aeval lam (u i)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl; intro i _; ring
      rw [hsum_eq, hr]
      ring
    have hinj := (nondegenerateRect_iff_injective (snocCol A a) (snocCol B b)).mp hnd' lam 1 (by simp)
    exact hv_ne (hinj (hker_v.trans (map_zero _).symm))
  · -- IsCoprimeTuple → Nondegenerate
    intro hcop
    rw [nondegenerateRect_iff_injective]
    intro c₁ c₂ hc
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker] at hv
    by_cases hlast : v (Fin.last j) = 0
    · rw [Matrix.mulVecLin_apply, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
        snocCol_map, snocCol_map, snocCol_mulVec, snocCol_mulVec, hlast] at hv
      simp only [zero_smul, add_zero] at hv
      rw [← Matrix.smul_mulVec, ← Matrix.smul_mulVec, ← Matrix.add_mulVec] at hv
      have hinit : (fun i : Fin j => v i.castSucc) = 0 :=
        ((nondegenerateRect_iff_injective A B).mp hnd c₁ c₂ hc) (hv.trans (map_zero _).symm)
      ext c
      exact Fin.lastCases hlast (fun i => congr_fun hinit i) c
    · by_cases hc2 : c₂ = 0
      · have hc1 : c₁ ≠ 0 := by intro h1; exact hc (Prod.ext h1 hc2)
        rw [hc2, zero_smul, add_zero, Matrix.mulVecLin_apply, Matrix.smul_mulVec] at hv
        have hv0 : (snocCol A a).map φ *ᵥ v = 0 := by
          have := congr_arg (fun x => c₁⁻¹ • x) hv
          simpa [smul_smul, inv_mul_cancel₀ hc1] using this
        exact hAa_map_inj (hv0.trans (map_zero _).symm)
      · -- Normalize c₂ = 1, lam = c₁ / c₂, and show minpoly F lam divides every coordinate of phiMap!
        exfalso
        let lam : AC F := c₁ / c₂
        let uvec : Fin j → AC F := fun i => -(v (Fin.last j))⁻¹ * v i.castSucc
        have hrel : ∀ r : Fin D, lam * φ (a r) + φ (b r) =
            ∑ i : Fin j, (lam * φ (A r i) + φ (B r i)) * uvec i := by
          intro r
          have hr := congr_fun hv r
          rw [Matrix.mulVecLin_apply, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
            snocCol_map, snocCol_map, snocCol_mulVec, snocCol_mulVec] at hr
          simp only [Pi.add_apply, Pi.smul_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
            smul_eq_mul, Pi.zero_apply] at hr
          have hdiv := congr_arg (fun x => (c₂ * v (Fin.last j))⁻¹ * x) hr
          simp only [mul_zero] at hdiv
          have hc2v : c₂ * v (Fin.last j) ≠ 0 := mul_ne_zero hc2 hlast
          have hlhs : (c₂ * v (Fin.last j))⁻¹ * (c₁ * (∑ i : Fin j, φ (A r i) * v i.castSucc +
              v (Fin.last j) * φ (a r)) + c₂ * (∑ i : Fin j, φ (B r i) * v i.castSucc +
              v (Fin.last j) * φ (b r))) =
              (lam * φ (a r) + φ (b r)) - ∑ i : Fin j, (lam * φ (A r i) + φ (B r i)) * uvec i := by
            simp only [lam, uvec]
            have h1 : (c₂ * v (Fin.last j))⁻¹ * (c₁ * (v (Fin.last j) * φ (a r)) +
                c₂ * (v (Fin.last j) * φ (b r))) = c₁ / c₂ * φ (a r) + φ (b r) := by
              field_simp [hc2, hlast]
            have h2 : (c₂ * v (Fin.last j))⁻¹ * (∑ i : Fin j, (c₁ * (φ (A r i) * v i.castSucc) +
                c₂ * (φ (B r i) * v i.castSucc))) =
                -(∑ i : Fin j, (c₁ / c₂ * φ (A r i) + φ (B r i)) * (-(v (Fin.last j))⁻¹ * v i.castSucc)) := by
              rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro i _
              field_simp [hc2, hlast]
            have hrearr : (c₂ * v (Fin.last j))⁻¹ * (c₁ * (∑ i : Fin j, φ (A r i) * v i.castSucc +
                v (Fin.last j) * φ (a r)) + c₂ * (∑ i : Fin j, φ (B r i) * v i.castSucc +
                v (Fin.last j) * φ (b r))) =
                (c₂ * v (Fin.last j))⁻¹ * (c₁ * (v (Fin.last j) * φ (a r)) +
                  c₂ * (v (Fin.last j) * φ (b r))) +
                (c₂ * v (Fin.last j))⁻¹ * (∑ i : Fin j, (c₁ * (φ (A r i) * v i.castSucc) +
                  c₂ * (φ (B r i) * v i.castSucc))) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring
            rw [hrearr, h1, h2]; ring
          rw [hlhs, sub_eq_zero] at hdiv
          exact hdiv
        -- Show aeval lam (phiMap p (X a + b) t) = 0 for all t!
        have haeval0 : ∀ t : Fin (D - j),
            aeval lam (phiMap p (fun u => X * C (a u) + C (b u)) t) = 0 := by
          intro t
          simp only [phiMap, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_add, map_mul,
            aeval_X, aeval_C]
          have h1 : ∑ r : Fin D, aeval lam (p t r) * (lam * φ (a r) + φ (b r)) =
              ∑ r : Fin D, aeval lam (p t r) * ∑ i : Fin j, (lam * φ (A r i) + φ (B r i)) * uvec i := by
            apply Finset.sum_congr rfl; intro r _; rw [hrel r]
          rw [h1]
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_eq_zero
          intro i _
          have hi := congr_arg (aeval lam) (congr_fun (LinearMap.mem_ker.mp (hp_ker t)) i)
          rw [pencilT, Matrix.mulVecLin_apply] at hi
          simp only [Matrix.mulVec, dotProduct, Matrix.add_apply,
            Matrix.smul_apply, Matrix.map_apply, Matrix.transpose_apply, smul_eq_mul,
            map_sum, map_add, map_mul, aeval_X, aeval_C, Pi.zero_apply, map_zero] at hi
          have hfac : ∑ r : Fin D, aeval lam (p t r) * ((lam * φ (A r i) + φ (B r i)) * uvec i) =
              (∑ r : Fin D, (lam * φ (A r i) + φ (B r i)) * aeval lam (p t r)) * uvec i := by
            rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro r _; ring
          rw [hfac, hi, zero_mul]
        have halg : IsIntegral F lam := (Algebra.IsAlgebraic.isAlgebraic lam).isIntegral
        have hmin_monic : (minpoly F lam).Monic := minpoly.monic halg
        have hmin_dvd : ∀ t : Fin (D - j), minpoly F lam ∣ phiMap p (fun u => X * C (a u) + C (b u)) t :=
          fun t => minpoly.dvd F lam (haeval0 t)
        have hmin_eq1 : minpoly F lam = 1 := hcop (minpoly F lam) hmin_monic hmin_dvd
        have hpos := minpoly.natDegree_pos halg
        rw [hmin_eq1, natDegree_one] at hpos
        omega

end GrandMaster


-- Part 4: grand_master_step + column_induction + main assembly!

section Counting

open Polynomial BigOperators Matrix

variable {F : Type*} [Field F] [Fintype F]

-- Grand Master Lemma: for NondegenerateRect A B (with j < D) and a ∉ range A.mulVecLin,
-- the number of b : Fin D → F such that NondegenerateRect (snocCol A a) (snocCol B b) is q^D - q^(j + 1)!
lemma card_good_b {D j : ℕ} {A B : Matrix (Fin D) (Fin j) F}
    (hnd : NondegenerateRect A B) (hjD : j < D)
    {a : Fin D → F} (ha : a ∉ LinearMap.range A.mulVecLin) :
    (Finset.univ.filter (fun b : Fin D → F => NondegenerateRect (snocCol A a) (snocCol B b))).card =
      Fintype.card F ^ D - Fintype.card F ^ (j + 1) := by
  obtain ⟨p, hp_ker, hsum_eq, hdeg_mem, hphiConst_bij, hphi_surj, hker_eq, ha_ne⟩ :=
    pencil_quotient_data hnd hjD
  let d : Fin (D - j) → ℕ := fun t => vdeg (p t)
  let α : Fin (D - j) → F := fun t => (phiMap p (fun u => C (a u)) t).coeff (d t)
  have hα : ∃ t : Fin (D - j), α t ≠ 0 := ha_ne a ha
  -- For each t, X * phiMap p (C ∘ a) t - C (α t) * X^(d t + 1) lies in degreeLT F (d t + 1)!
  have hshift_mem : ∀ t : Fin (D - j),
      X * phiMap p (fun u => C (a u)) t - C (α t) * X ^ (d t + 1) ∈ degreeLT F (d t + 1) := by
    intro t
    rw [mem_degreeLT, degree_lt_iff_coeff_zero]
    intro k hk
    rw [coeff_sub, coeff_C_mul, coeff_X_pow]
    have hfa : phiMap p (fun u => C (a u)) t ∈ degreeLT F (d t + 1) := hdeg_mem t a
    have hfa_zero : ∀ m, d t + 1 ≤ m → (phiMap p (fun u => C (a u)) t).coeff m = 0 :=
      (degree_lt_iff_coeff_zero _ _).mp (mem_degreeLT.mp hfa)
    rcases eq_or_lt_of_le hk with rfl | hgt
    · rw [coeff_X_mul, if_pos rfl, mul_one]; exact sub_self _
    · rcases Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0) with ⟨k', rfl⟩
      rw [coeff_X_mul, if_neg (by omega), mul_zero, hfa_zero k' (by omega), sub_zero]
  let shift : ∀ t : Fin (D - j), degreeLT F (d t + 1) :=
    fun t => ⟨X * phiMap p (fun u => C (a u)) t - C (α t) * X ^ (d t + 1), hshift_mem t⟩
  letI : ∀ t : Fin (D - j), Fintype (degreeLT F (d t + 1)) :=
    fun t => Fintype.ofEquiv (Fin (d t + 1) → F) (degreeLTEquiv F (d t + 1)).symm.toEquiv
  -- Build bijection (Fin D → F) ≃ (∀ t, degreeLT F (d t + 1)) sending b ↦ shift + phiConst b!
  let e_base : (Fin D → F) ≃ (∀ t : Fin (D - j), degreeLT F (d t + 1)) :=
    Equiv.ofBijective _ hphiConst_bij
  let e : (Fin D → F) ≃ (∀ t : Fin (D - j), degreeLT F (d t + 1)) :=
    e_base.trans (Equiv.addLeft shift)
  have he_val : ∀ (b : Fin D → F) (t : Fin (D - j)),
      phiMap p (fun u => X * C (a u) + C (b u)) t = C (α t) * X ^ (d t + 1) + (e b t).val := by
    intro b t
    have hsplit : (fun u => X * C (a u) + C (b u)) = (X : F[X]) • (fun u => C (a u)) + (fun u => C (b u)) := by
      funext u; simp
    rw [hsplit, map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    change X * (phiMap p) (fun u => C (a u)) t + (phiMap p) (fun u => C (b u)) t =
      C (α t) * X ^ (d t + 1) + ((shift t).val + (e_base b t).val)
    simp only [shift, e_base, Equiv.ofBijective_apply]
    ring
  have hiff : ∀ b : Fin D → F,
      NondegenerateRect (snocCol A a) (snocCol B b) ↔
      IsCoprimeTuple (fun t => C (α t) * X ^ (d t + 1) + (e b t).val) := by
    intro b
    rw [nondegenerateRect_snoc_iff_coprime hnd hjD hp_ker hphi_surj hker_eq ha b]
    have hfun : phiMap p (fun u => X * C (a u) + C (b u)) =
        fun t => C (α t) * X ^ (d t + 1) + (e b t).val := funext (he_val b)
    rw [hfun]
  -- Transfer card via bijection e!
  have hcard_eq : (Finset.univ.filter (fun b : Fin D → F =>
      NondegenerateRect (snocCol A a) (snocCol B b))).card =
      (Finset.univ.filter (fun R : ∀ t : Fin (D - j), degreeLT F (d t + 1) =>
        IsCoprimeTuple (fun t => C (α t) * X ^ (d t + 1) + (R t).val))).card := by
    apply Finset.card_bij (fun b _ => e b)
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact (hiff b).mp hb
    · intro b1 _ b2 _ h; exact e.injective h
    · intro R hR
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hR
      refine ⟨e.symm R, ?_, e.apply_symm_apply R⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hiff, e.apply_symm_apply]; exact hR
  rw [hcard_eq, card_coprime_affine d α hα]
  have hsum_d1 : ∑ t : Fin (D - j), (d t + 1) = D := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      mul_one]
    change (∑ t : Fin (D - j), vdeg (p t)) + (D - j) = D
    rw [hsum_eq]; omega
  rw [hsum_d1, show ∑ t : Fin (D - j), d t = j from hsum_eq]

-- RespectsRect for n × m matrices
def RespectsRect {n m : ℕ} (lam : Fin m → ℕ) (M : Matrix (Fin n) (Fin m) F) : Prop :=
  ∀ (r : Fin n) (j : Fin m), n ≤ r.val + lam j → M r j = 0

-- Dropping the last `c` zero rows of an n × m matrix preserves NondegenerateRect!
def topRows {n m : ℕ} (D : ℕ) (hD : D ≤ n) (M : Matrix (Fin n) (Fin m) F) :
    Matrix (Fin D) (Fin m) F :=
  Matrix.of (fun r c => M ⟨r.val, lt_of_lt_of_le r.isLt hD⟩ c)

lemma nondegenerateRect_iff_topRows {n m D : ℕ} (hD : D ≤ n)
    {A B : Matrix (Fin n) (Fin m) F}
    (hA0 : ∀ (r : Fin n) (j : Fin m), D ≤ r.val → A r j = 0)
    (hB0 : ∀ (r : Fin n) (j : Fin m), D ≤ r.val → B r j = 0) :
    NondegenerateRect A B ↔ NondegenerateRect (topRows D hD A) (topRows D hD B) := by
  rw [nondegenerateRect_iff_injective, nondegenerateRect_iff_injective]
  let φ := algebraMap F (AC F)
  have h_eq : ∀ (c₁ c₂ : AC F) (v : Fin m → AC F),
      (c₁ • A.map φ + c₂ • B.map φ) *ᵥ v = 0 ↔
      (c₁ • (topRows D hD A).map φ + c₂ • (topRows D hD B).map φ) *ᵥ v = 0 := by
    intro c₁ c₂ v
    constructor
    · intro h
      ext r
      have hr := congr_fun h ⟨r.val, lt_of_lt_of_le r.isLt hD⟩
      simpa [topRows, Matrix.mulVec, dotProduct] using hr
    · intro h
      ext r
      by_cases hlt : r.val < D
      · have hr := congr_fun h ⟨r.val, hlt⟩
        simpa [topRows, Matrix.mulVec, dotProduct] using hr
      · push Not at hlt
        simp only [Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.smul_apply,
          Matrix.map_apply, smul_eq_mul, Pi.zero_apply]
        apply Finset.sum_eq_zero
        intro j _
        rw [hA0 r j hlt, hB0 r j hlt, map_zero, mul_zero, mul_zero, add_zero, zero_mul]
  constructor
  · intro h c₁ c₂ hc
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    have hv' : (c₁ • A.map φ + c₂ • B.map φ) *ᵥ v = 0 := (h_eq c₁ c₂ v).mpr hv
    exact h c₁ c₂ hc (hv'.trans (map_zero _).symm)
  · intro h c₁ c₂ hc
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    have hv' : (c₁ • (topRows D hD A).map φ + c₂ • (topRows D hD B).map φ) *ᵥ v = 0 :=
      (h_eq c₁ c₂ v).mp hv
    exact h c₁ c₂ hc (hv'.trans (map_zero _).symm)

-- Deleting the last column preserves NondegenerateRect!
lemma nondegenerateRect_of_snocCol {n m : ℕ} {A B : Matrix (Fin n) (Fin m) F}
    {a b : Fin n → F} (h : NondegenerateRect (snocCol A a) (snocCol B b)) :
    NondegenerateRect A B ∧ a ∉ LinearMap.range A.mulVecLin := by
  let φ := algebraMap F (AC F)
  have hnd : NondegenerateRect A B := by
    rw [nondegenerateRect_iff_injective] at h ⊢
    intro c₁ c₂ hc
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    let v' : Fin (m + 1) → AC F := Fin.snoc v 0
    have hv' : (c₁ • (snocCol A a).map φ + c₂ • (snocCol B b).map φ) *ᵥ v' = 0 := by
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
        snocCol_map, snocCol_map, snocCol_mulVec, snocCol_mulVec]
      simp only [v', Fin.snoc_castSucc, Fin.snoc_last, zero_smul, add_zero]
      rw [← Matrix.smul_mulVec, ← Matrix.smul_mulVec, ← Matrix.add_mulVec]
      exact hv
    have hv'0 : v' = 0 := h c₁ c₂ hc (hv'.trans (map_zero _).symm)
    ext i
    have := congr_fun hv'0 i.castSucc
    simpa [v'] using this
  have ha : a ∉ LinearMap.range A.mulVecLin := by
    rintro ⟨u, hu⟩
    simp only [Matrix.mulVecLin_apply] at hu
    have hAa_inj : Function.Injective (snocCol A a).mulVecLin :=
      mulVecLin_injective_of_map_injective (snocCol A a)
        (by simpa using (nondegenerateRect_iff_injective _ _).mp h 1 0 (by simp))
    let w : Fin (m + 1) → F := Fin.snoc u (-1)
    have hw0 : (snocCol A a).mulVecLin w = 0 := by
      rw [Matrix.mulVecLin_apply, snocCol_mulVec]
      simp only [w, Fin.snoc_castSucc, Fin.snoc_last, neg_smul, one_smul]
      change A *ᵥ u + -(a) = 0
      rw [hu, add_neg_cancel]
    have hw : w = 0 := hAa_inj (hw0.trans (map_zero _).symm)
    have := congr_fun hw (Fin.last m)
    simp [w] at this
  exact ⟨hnd, ha⟩

-- Helper: cardinality of {a : Fin n → F | (∀ r, D ≤ r.val → a r = 0) ∧ a ∉ range A.mulVecLin}
lemma card_good_a {n m D : ℕ} (hD : D ≤ n) (hmD : m ≤ D)
    {A : Matrix (Fin n) (Fin m) F} (hA : Function.Injective A.mulVecLin)
    (hA0 : ∀ (r : Fin n) (j : Fin m), D ≤ r.val → A r j = 0) :
    (Finset.univ.filter (fun a : Fin n → F =>
      (∀ r : Fin n, D ≤ r.val → a r = 0) ∧ a ∉ LinearMap.range A.mulVecLin)).card =
      Fintype.card F ^ D - Fintype.card F ^ m := by
  -- Bijection between {a | ∀ r ≥ D, a r = 0} and (Fin D → F)
  let W : Submodule F (Fin n → F) :=
    { carrier := {a | ∀ r : Fin n, D ≤ r.val → a r = 0}
      add_mem' := fun {a1 a2} h1 h2 r hr => by simp [h1 r hr, h2 r hr]
      zero_mem' := fun r _ => rfl
      smul_mem' := fun c {a} ha r hr => by simp [ha r hr] }
  have hsub : LinearMap.range A.mulVecLin ≤ W := by
    rintro _ ⟨u, rfl⟩ r hr
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro j _
    rw [hA0 r j hr, zero_mul]
  let eW : W ≃ₗ[F] (Fin D → F) :=
    { toFun := fun a r => a.val ⟨r.val, lt_of_lt_of_le r.isLt hD⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun v => ⟨fun r => if h : r.val < D then v ⟨r.val, h⟩ else 0, by
        intro r hr; simp [Nat.not_lt.mpr hr]⟩
      left_inv := fun a => by
        apply Subtype.ext; ext r
        by_cases h : r.val < D
        · simp [h]
        · simp [h, a.2 r (Nat.not_lt.mp h)]
      right_inv := fun v => by ext r; simp [r.isLt] }
  have hcardW : (Finset.univ.filter (fun a : Fin n → F => a ∈ W)).card = Fintype.card F ^ D := by
    rw [← Fintype.card_subtype]
    rw [Fintype.card_congr eW.toEquiv]
    simp [Fintype.card_pi]
  have hcardR : (Finset.univ.filter (fun a : Fin n → F => a ∈ LinearMap.range A.mulVecLin)).card =
      Fintype.card F ^ m := by
    have himg : Finset.univ.filter (fun a : Fin n → F => a ∈ LinearMap.range A.mulVecLin) =
        Finset.univ.image A.mulVecLin := by
      ext a; simp [LinearMap.mem_range]
    rw [himg, Finset.card_image_of_injective _ hA, Finset.card_univ]
    simp [Fintype.card_pi]
  have hsdiff : Finset.univ.filter (fun a : Fin n → F =>
      (∀ r : Fin n, D ≤ r.val → a r = 0) ∧ a ∉ LinearMap.range A.mulVecLin) =
      (Finset.univ.filter (fun a : Fin n → F => a ∈ W)) \
      (Finset.univ.filter (fun a : Fin n → F => a ∈ LinearMap.range A.mulVecLin)) := by
    ext a; simp [W]
  have hsub_fin : Finset.univ.filter (fun a : Fin n → F => a ∈ LinearMap.range A.mulVecLin) ⊆
      Finset.univ.filter (fun a : Fin n → F => a ∈ W) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact hsub ha
  rw [hsdiff, Finset.card_sdiff_of_subset hsub_fin, hcardW, hcardR]

-- Main column-by-column induction theorem!
theorem card_nondegenerate_rect (n m : ℕ) (lam mu : Fin m → ℕ)
    (hlam_anti : Antitone lam) (hmu_anti : Antitone mu)
    (hle : ∀ j, mu j ≤ lam j)
    (hlam_bnd : ∀ j : Fin m, lam j + j.val + 1 ≤ n)
    (hmu_bnd : ∀ j : Fin m, mu j + j.val + 2 ≤ n) :
    Nat.card {M : Matrix (Fin n) (Fin m) F × Matrix (Fin n) (Fin m) F //
      RespectsRect lam M.1 ∧ RespectsRect mu M.2 ∧ NondegenerateRect M.1 M.2} =
      ∏ j : Fin m, (Fintype.card F ^ (n - lam j) - Fintype.card F ^ j.val) *
        (Fintype.card F ^ (n - mu j) - Fintype.card F ^ (j.val + 1)) := by
  classical
  induction m with
  | zero =>
    rw [Finset.prod_eq_one (fun j _ => j.elim0), Nat.card_eq_fintype_card, Fintype.card_eq_one_iff]
    refine ⟨⟨(Matrix.of (fun _ j => j.elim0), Matrix.of (fun _ j => j.elim0)), ?_, ?_, ?_⟩, ?_⟩
    · intro _ j; exact j.elim0
    · intro _ j; exact j.elim0
    · rw [nondegenerateRect_iff_injective]; intro _ _ _ v1 v2 _; ext j; exact j.elim0
    · rintro ⟨⟨M1, M2⟩, _⟩; apply Subtype.ext; apply Prod.ext <;> ext _ j <;> exact j.elim0
  | succ m ih =>
    let lam' : Fin m → ℕ := fun i => lam i.castSucc
    let mu' : Fin m → ℕ := fun i => mu i.castSucc
    have hih := ih lam' mu'
      (fun a b hab => hlam_anti (Fin.castSucc_le_castSucc_iff.mpr hab))
      (fun a b hab => hmu_anti (Fin.castSucc_le_castSucc_iff.mpr hab))
      (fun i => hle i.castSucc)
      (fun i => hlam_bnd i.castSucc)
      (fun i => hmu_bnd i.castSucc)
    -- Split (M1, M2) into ((M1', M2'), a, b) via snocCol!
    let S_prev := {P : Matrix (Fin n) (Fin m) F × Matrix (Fin n) (Fin m) F //
      RespectsRect lam' P.1 ∧ RespectsRect mu' P.2 ∧ NondegenerateRect P.1 P.2}
    let D1 := n - lam (Fin.last m)
    let D2 := n - mu (Fin.last m)
    have hD1_le : D1 ≤ n := Nat.sub_le _ _
    have hD2_le : D2 ≤ n := Nat.sub_le _ _
    have hlam_last := hlam_bnd (Fin.last m)
    have hmu_last := hmu_bnd (Fin.last m)
    simp only [Fin.val_last] at hlam_last hmu_last
    have hm_le_D1 : m ≤ D1 := by omega
    have hm_lt_D2 : m < D2 := by omega
    have hD1_le_D2 : D1 ≤ D2 := by have := hle (Fin.last m); omega
    -- Rewrite LHS as sum over P ∈ S_prev, a ∈ good_a(P), b ∈ good_b(P, a)
    let S_cur := {M : Matrix (Fin n) (Fin (m + 1)) F × Matrix (Fin n) (Fin (m + 1)) F //
      RespectsRect lam M.1 ∧ RespectsRect mu M.2 ∧ NondegenerateRect M.1 M.2}
    let FiberA (P : S_prev) :=
      {a : Fin n → F // (∀ r : Fin n, D1 ≤ r.val → a r = 0) ∧ a ∉ LinearMap.range P.val.1.mulVecLin}
    let FiberB (P : S_prev) (a : FiberA P) :=
      {b : Fin n → F // (∀ r : Fin n, D2 ≤ r.val → b r = 0) ∧
        NondegenerateRect (snocCol P.val.1 a.val) (snocCol P.val.2 b)}
    -- Build equivalence S_cur ≃ Σ P : S_prev, Σ a : FiberA P, FiberB P a!
    let e_split : S_cur ≃ Σ P : S_prev, Σ a : FiberA P, FiberB P a :=
      { toFun := fun M =>
          let M1' : Matrix (Fin n) (Fin m) F := Matrix.of (fun r i => M.val.1 r i.castSucc)
          let M2' : Matrix (Fin n) (Fin m) F := Matrix.of (fun r i => M.val.2 r i.castSucc)
          let a : Fin n → F := fun r => M.val.1 r (Fin.last m)
          let b : Fin n → F := fun r => M.val.2 r (Fin.last m)
          have hM1 : snocCol M1' a = M.val.1 := by
            ext r c; refine Fin.lastCases ?_ ?_ c <;> simp [snocCol, M1', a]
          have hM2 : snocCol M2' b = M.val.2 := by
            ext r c; refine Fin.lastCases ?_ ?_ c <;> simp [snocCol, M2', b]
          have hnd_split : NondegenerateRect M1' M2' ∧ a ∉ LinearMap.range M1'.mulVecLin :=
            nondegenerateRect_of_snocCol (hM1.symm ▸ hM2.symm ▸ M.2.2.2)
          let P : S_prev := ⟨(M1', M2'),
            fun r i hr => M.2.1 r i.castSucc hr,
            fun r i hr => M.2.2.1 r i.castSucc hr,
            hnd_split.1⟩
          let a_sub : FiberA P := ⟨a,
            fun r hr => M.2.1 r (Fin.last m) (by omega),
            hnd_split.2⟩
          let b_sub : FiberB P a_sub := ⟨b,
            fun r hr => M.2.2.1 r (Fin.last m) (by omega),
            hM1.symm ▸ hM2.symm ▸ M.2.2.2⟩
          ⟨P, a_sub, b_sub⟩
        invFun := fun ⟨P, a, b⟩ =>
          ⟨(snocCol P.val.1 a.val, snocCol P.val.2 b.val),
            by
              intro r c
              refine Fin.lastCases ?_ ?_ c
              · intro hr
                simp only [snocCol_apply_last]
                exact a.2.1 r (by dsimp only [D1]; omega)
              · intro i hr
                simp only [snocCol_apply_castSucc]
                exact P.2.1 r i hr,
            by
              intro r c
              refine Fin.lastCases ?_ ?_ c
              · intro hr
                simp only [snocCol_apply_last]
                exact b.2.1 r (by dsimp only [D2]; omega)
              · intro i hr
                simp only [snocCol_apply_castSucc]
                exact P.2.2.1 r i hr,
            b.2.2⟩
        left_inv := fun M => by
          apply Subtype.ext; apply Prod.ext <;> ext r c <;>
            refine Fin.lastCases ?_ ?_ c <;> simp [snocCol]
        right_inv := fun ⟨P, a, b⟩ => by
          rcases P with ⟨⟨M1', M2'⟩, hP⟩
          rcases a with ⟨av, ha⟩
          rcases b with ⟨bv, hb⟩
          have h_eq : ∀ (A1 : Matrix (Fin n) (Fin m) F) (A2 : Matrix (Fin n) (Fin m) F)
              (a1 a2 : Fin n → F)
              (h1 : A1 = M1') (h2 : A2 = M2') (h3 : a1 = av) (h4 : a2 = bv)
              (hP' : RespectsRect lam' A1 ∧ RespectsRect mu' A2 ∧ NondegenerateRect A1 A2)
              (ha' : (∀ r : Fin n, D1 ≤ r.val → a1 r = 0) ∧ a1 ∉ LinearMap.range A1.mulVecLin)
              (hb' : (∀ r : Fin n, D2 ≤ r.val → a2 r = 0) ∧
                NondegenerateRect (snocCol A1 a1) (snocCol A2 a2)),
              (⟨⟨(A1, A2), hP'⟩, ⟨⟨a1, ha'⟩, ⟨a2, hb'⟩⟩⟩ :
                Σ P : S_prev, Σ a : FiberA P, FiberB P a) =
              ⟨⟨(M1', M2'), hP⟩, ⟨⟨av, ha⟩, ⟨bv, hb⟩⟩⟩ := by
            rintro _ _ _ _ rfl rfl rfl rfl _ _ _; rfl
          exact h_eq _ _ _ _
            (by ext r i; simp [snocCol]) (by ext r i; simp [snocCol])
            (by funext r; simp [snocCol]) (by funext r; simp [snocCol]) _ _ _ }
    -- Count each FiberB and FiberA!
    have hcard_B : ∀ (P : S_prev) (a : FiberA P),
        Fintype.card (FiberB P a) = Fintype.card F ^ D2 - Fintype.card F ^ (m + 1) := by
      intro P a
      -- Restrict to top D2 rows!
      have hP1_zero : ∀ (r : Fin n) (i : Fin m), D2 ≤ r.val → P.val.1 r i = 0 := by
        intro r i hr
        apply P.2.1 r i
        have h1 : mu (Fin.last m) ≤ lam (Fin.last m) := hle (Fin.last m)
        have h2 : lam (Fin.last m) ≤ lam i.castSucc := hlam_anti (Fin.le_last _)
        dsimp only [D2, lam'] at hr ⊢
        omega
      have hP2_zero : ∀ (r : Fin n) (i : Fin m), D2 ≤ r.val → P.val.2 r i = 0 := by
        intro r i hr
        apply P.2.2.1 r i
        have h2 : mu (Fin.last m) ≤ mu i.castSucc := hmu_anti (Fin.le_last _)
        dsimp only [D2, mu'] at hr ⊢
        omega
      have ha_zero : ∀ r : Fin n, D2 ≤ r.val → a.val r = 0 :=
        fun r hr => a.2.1 r (le_trans hD1_le_D2 hr)
      let A_top := topRows D2 hD2_le P.val.1
      let B_top := topRows D2 hD2_le P.val.2
      let a_top : Fin D2 → F := fun r => a.val ⟨r.val, lt_of_lt_of_le r.isLt hD2_le⟩
      have hnd_top : NondegenerateRect A_top B_top :=
        (nondegenerateRect_iff_topRows hD2_le hP1_zero hP2_zero).mp P.2.2.2
      have ha_top : a_top ∉ LinearMap.range A_top.mulVecLin := by
        rintro ⟨u, hu⟩
        apply a.2.2
        refine ⟨u, ?_⟩
        ext r
        by_cases hlt : r.val < D2
        · have hr := congr_fun hu ⟨r.val, hlt⟩
          simpa [A_top, a_top, topRows, Matrix.mulVec, dotProduct] using hr
        · push Not at hlt
          rw [ha_zero r hlt]
          simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
          apply Finset.sum_eq_zero
          intro i _; rw [hP1_zero r i hlt, zero_mul]
      -- Equivalence between FiberB P a and {b_top : Fin D2 → F // NondegenerateRect (snocCol A_top a_top) (snocCol B_top b_top)}!
      let eB : FiberB P a ≃
          {b_top : Fin D2 → F // NondegenerateRect (snocCol A_top a_top) (snocCol B_top b_top)} :=
        { toFun := fun b =>
            ⟨fun r => b.val ⟨r.val, lt_of_lt_of_le r.isLt hD2_le⟩, by
              have hsnoc1 : topRows D2 hD2_le (snocCol P.val.1 a.val) = snocCol A_top a_top := by
                ext r c; refine Fin.lastCases ?_ ?_ c <;> simp [topRows, snocCol, A_top, a_top]
              have hsnoc2 : topRows D2 hD2_le (snocCol P.val.2 b.val) =
                  snocCol B_top (fun r => b.val ⟨r.val, lt_of_lt_of_le r.isLt hD2_le⟩) := by
                ext r c; refine Fin.lastCases ?_ ?_ c <;> simp [topRows, snocCol, B_top]
              rw [← hsnoc1, ← hsnoc2]
              refine (nondegenerateRect_iff_topRows hD2_le ?_ ?_).mp b.2.2
              · intro r c hr; refine Fin.lastCases ?_ ?_ c
                · simpa [snocCol] using ha_zero r hr
                · intro i; simpa [snocCol] using hP1_zero r i hr
              · intro r c hr; refine Fin.lastCases ?_ ?_ c
                · simpa [snocCol] using b.2.1 r hr
                · intro i; simpa [snocCol] using hP2_zero r i hr⟩
          invFun := fun b_top =>
            ⟨fun r => if h : r.val < D2 then b_top.val ⟨r.val, h⟩ else 0,
              fun r hr => by simp [Nat.not_lt.mpr hr],
              by
                refine (nondegenerateRect_iff_topRows hD2_le ?_ ?_).mpr ?_
                · intro r c hr; refine Fin.lastCases ?_ ?_ c
                  · simpa [snocCol] using ha_zero r hr
                  · intro i; simpa [snocCol] using hP1_zero r i hr
                · intro r c hr; refine Fin.lastCases ?_ ?_ c
                  · simp [snocCol, Nat.not_lt.mpr hr]
                  · intro i; simpa [snocCol] using hP2_zero r i hr
                · have hsnoc1 : topRows D2 hD2_le (snocCol P.val.1 a.val) = snocCol A_top a_top := by
                    ext r c; refine Fin.lastCases ?_ ?_ c <;> simp [topRows, snocCol, A_top, a_top]
                  have hsnoc2 : topRows D2 hD2_le
                      (snocCol P.val.2 (fun r => if h : r.val < D2 then b_top.val ⟨r.val, h⟩ else 0)) =
                      snocCol B_top b_top.val := by
                    ext r c; refine Fin.lastCases ?_ ?_ c <;> simp [topRows, snocCol, B_top]
                  rw [hsnoc1, hsnoc2]; exact b_top.2⟩
          left_inv := fun b => by
            apply Subtype.ext; ext r
            by_cases h : r.val < D2
            · simp [h]
            · simp [h, b.2.1 r (Nat.not_lt.mp h)]
          right_inv := fun b_top => by apply Subtype.ext; ext r; simp [r.isLt] }
      rw [Fintype.card_congr eB, Fintype.card_subtype]
      exact card_good_b hnd_top hm_lt_D2 ha_top
    have hcard_A : ∀ P : S_prev,
        Fintype.card (FiberA P) = Fintype.card F ^ D1 - Fintype.card F ^ m := by
      intro P
      have hP1_inj : Function.Injective P.val.1.mulVecLin :=
        mulVecLin_injective_of_map_injective P.val.1
          (by simpa using (nondegenerateRect_iff_injective _ _).mp P.2.2.2 1 0 (by simp))
      have hP1_zero : ∀ (r : Fin n) (i : Fin m), D1 ≤ r.val → P.val.1 r i = 0 := by
        intro r i hr
        apply P.2.1 r i
        have h2 : lam (Fin.last m) ≤ lam i.castSucc := hlam_anti (Fin.le_last _)
        dsimp only [D1, lam'] at hr ⊢
        omega
      rw [Fintype.card_subtype]
      exact card_good_a hD1_le hm_le_D1 hP1_inj hP1_zero
    -- Assemble total cardinality!
    rw [Nat.card_eq_fintype_card, Fintype.card_congr e_split, Fintype.card_sigma]
    have hinner : ∀ P : S_prev,
        Fintype.card (Σ a : FiberA P, FiberB P a) =
          (Fintype.card F ^ D1 - Fintype.card F ^ m) *
          (Fintype.card F ^ D2 - Fintype.card F ^ (m + 1)) := by
      intro P
      rw [Fintype.card_sigma]
      simp only [hcard_B P, Finset.sum_const, Finset.card_univ, smul_eq_mul, hcard_A P]
    simp only [hinner, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [← Nat.card_eq_fintype_card, hih, Fin.prod_univ_castSucc]
    simp only [lam', mu', D1, D2, Fin.val_castSucc, Fin.val_last]

end Counting



open BigOperators

def qInt (n q : ℕ) : ℕ := ∑ i ∈ Finset.range n, q ^ i

lemma mul_qInt (n q : ℕ) (hq : 1 ≤ q) : (q - 1) * qInt n q = q ^ n - 1 := by
  unfold qInt
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h1 : 1 ≤ q ^ m := Nat.one_le_pow m q hq
    zify [hq, h1, Nat.one_le_pow (m + 1) q hq]
    ring

lemma rhs_rewrite (q k : ℕ) (hq : 1 ≤ q) (lam mu : Fin k → ℕ)
    (hlam : ∀ j : Fin k, lam j + j.val ≤ k)
    (hmu : ∀ j : Fin k, mu j + j.val + 1 ≤ k) :
    q ^ (k ^ 2) * (q - 1) ^ (2 * k) *
      (∏ j : Fin k, qInt (k + 1 - j.val - lam j) q) *
      (∏ j : Fin k, qInt (k - j.val - mu j) q) =
    ∏ j : Fin k, (q ^ (k + 1 - lam j) - q ^ j.val) * (q ^ (k + 1 - mu j) - q ^ (j.val + 1)) := by
  have hsum : ∑ j : Fin k, (2 * j.val + 1) = k ^ 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun j => 2 * j + 1) k]
    suffices ∀ n : ℕ, ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 from this k
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]; ring
  rw [← hsum, ← Finset.prod_pow_eq_pow_sum]
  have h2k : (q - 1) ^ (2 * k) = ∏ _j : Fin k, ((q - 1) * (q - 1)) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← sq, ← pow_mul, mul_comm]
  rw [h2k, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  have hl := hlam j
  have hm := hmu j
  have h1 : q ^ j.val * ((q - 1) * qInt (k + 1 - j.val - lam j) q) =
      q ^ (k + 1 - lam j) - q ^ j.val := by
    rw [mul_qInt _ q hq, Nat.mul_sub_left_distrib, mul_one, ← pow_add]
    congr 2; omega
  have h2 : q ^ (j.val + 1) * ((q - 1) * qInt (k - j.val - mu j) q) =
      q ^ (k + 1 - mu j) - q ^ (j.val + 1) := by
    rw [mul_qInt _ q hq, Nat.mul_sub_left_distrib, mul_one, ← pow_add]
    congr 2; omega
  rw [← h1, ← h2]
  have hpow : q ^ (2 * j.val + 1) = q ^ j.val * q ^ (j.val + 1) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow]; ring

end OMA_A2602_Full


theorem OMA.solution : type_of% @OMA.S_arxiv_2602_22129.main := by
  intro F _ _ k _ lam mu hlam_anti hmu_anti hle hlam hmu
  have h1 := OMA_A2602_Full.card_nondegenerate_rect (F := F) (k + 1) k lam mu
    hlam_anti hmu_anti hle
    (fun j => by have := hlam j; omega)
    (fun j => by have := hmu j; omega)
  have h2 := OMA_A2602_Full.rhs_rewrite (Fintype.card F) k Fintype.card_pos lam mu hlam hmu
  exact h1.trans h2.symm
