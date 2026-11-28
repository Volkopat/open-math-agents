import OMAReductions.R_oeis_a000952_R1

namespace OMA.Proof_oeis_a000952_R1_H1

open OMA.S_oeis_a000952

private def chi (p : ℕ) [Fact p.Prime] (x : ZMod p) : ℤ :=
  legendreSym p (x.val : ℤ)

private lemma chi_eq_legendreSym (p : ℕ) [Fact p.Prime] (a : ℤ) :
    chi p (a : ZMod p) = legendreSym p a := by
  unfold chi
  rw [legendreSym.mod p ((a : ZMod p).val : ℤ), legendreSym.mod p a]
  congr 1
  have h1 : (((a : ZMod p).val : ℕ) : ZMod p) = (a : ZMod p) := ZMod.natCast_zmod_val _
  have hp : (0 : ℤ) < (p : ℤ) := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hvlt : ((a : ZMod p).val : ℤ) < (p : ℤ) := Nat.cast_lt.mpr (ZMod.val_lt _)
  have hvnn : (0 : ℤ) ≤ ((a : ZMod p).val : ℤ) := Nat.cast_nonneg _
  rw [Int.emod_eq_of_lt hvnn hvlt]
  have hdvd : (p : ℤ) ∣ (((a : ZMod p).val : ℤ) - a) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h1, sub_self]
  have hmod := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd hdvd)
  rw [Int.emod_eq_of_lt hvnn hvlt] at hmod
  exact hmod

private lemma chi_zero (p : ℕ) [Fact p.Prime] : chi p 0 = 0 := by
  simp [chi]

private lemma chi_one (p : ℕ) [Fact p.Prime] : chi p 1 = 1 := by
  have := chi_eq_legendreSym p 1
  simpa using this

private lemma chi_mul (p : ℕ) [Fact p.Prime] (x y : ZMod p) :
    chi p (x * y) = chi p x * chi p y := by
  have hx : ((x.val : ℤ) : ZMod p) = x := by simp
  have hy : ((y.val : ℤ) : ZMod p) = y := by simp
  have hxy : ((((x.val : ℤ) * (y.val : ℤ)) : ℤ) : ZMod p) = x * y := by
    rw [Int.cast_mul, hx, hy]
  rw [← hxy, chi_eq_legendreSym, legendreSym.mul, chi, chi]

private lemma chi_neg_one_of_mod_four (p : ℕ) [Fact p.Prime] (h4 : p % 4 = 1) :
    chi p (-1) = 1 := by
  have hp2 : p ≠ 2 := by omega
  have hcast : ((-1 : ℤ) : ZMod p) = -1 := by simp
  rw [← hcast, chi_eq_legendreSym, legendreSym.at_neg_one hp2]
  have hmod : (p : ZMod 4) = 1 := by
    have : ((p % 4 : ℕ) : ZMod 4) = (p : ZMod 4) := ZMod.natCast_mod p 4
    rw [← this, h4]; rfl
  rw [hmod]
  decide

private lemma chi_neg_of_mod_four (p : ℕ) [Fact p.Prime] (h4 : p % 4 = 1) (x : ZMod p) :
    chi p (-x) = chi p x := by
  rw [show -x = (-1 : ZMod p) * x by ring, chi_mul, chi_neg_one_of_mod_four p h4, one_mul]

private lemma chi_values (p : ℕ) [Fact p.Prime] (x : ZMod p) :
    chi p x = -1 ∨ chi p x = 0 ∨ chi p x = 1 := by
  by_cases hx : x = 0
  · subst hx; exact Or.inr (Or.inl (chi_zero p))
  · have hne : ((x.val : ℤ) : ZMod p) ≠ 0 := by simpa [ZMod.natCast_zmod_val] using hx
    rcases legendreSym.eq_one_or_neg_one p hne with h1 | hm1
    · exact Or.inr (Or.inr h1)
    · exact Or.inl hm1

private lemma chi_sq_of_ne_zero (p : ℕ) [Fact p.Prime] {x : ZMod p} (hx : x ≠ 0) :
    chi p x * chi p x = 1 := by
  have hne : ((x.val : ℤ) : ZMod p) ≠ 0 := by simpa [ZMod.natCast_zmod_val] using hx
  rcases legendreSym.eq_one_or_neg_one p hne with h1 | hm1
  · unfold chi; rw [h1]; ring
  · unfold chi; rw [hm1]; ring

private lemma sum_chi_eq_zero (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ∑ x : ZMod p, chi p x = 0 := by
  have hp : p.Prime := Fact.out
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  let U : Finset (ZMod p) := Finset.univ.erase 0
  let QR : Finset (ZMod p) := U.filter (fun x => chi p x = 1)
  let QNR : Finset (ZMod p) := U.filter (fun x => chi p x = -1)
  have hQR_card : QR.card = (p - 1) / 2 := by
    have hbij : (Finset.Icc 1 ((p - 1) / 2)).card = QR.card := by
      refine Finset.card_bij (fun k _ => ((k : ZMod p) ^ 2)) ?_ ?_ ?_
      · intro k hk
        rw [Finset.mem_Icc] at hk
        have hkne : (k : ZMod p) ≠ 0 := by
          intro h0
          exact Nat.not_dvd_of_pos_of_lt hk.1 (by omega) ((ZMod.natCast_eq_zero_iff k p).mp h0)
        rw [Finset.mem_filter, Finset.mem_erase]
        refine ⟨⟨pow_ne_zero 2 hkne, Finset.mem_univ _⟩, ?_⟩
        rw [sq, chi_mul, chi_sq_of_ne_zero p hkne]
      · intro k1 hk1 k2 hk2 heq
        rw [Finset.mem_Icc] at hk1 hk2
        have hmul : ((k1 : ZMod p) - (k2 : ZMod p)) * ((k1 : ZMod p) + (k2 : ZMod p)) = 0 := by
          linear_combination heq
        rcases mul_eq_zero.mp hmul with hsub | hadd
        · have hz : (k1 : ZMod p) = (k2 : ZMod p) := sub_eq_zero.mp hsub
          have hv := congrArg ZMod.val hz
          rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv
          exact hv
        · have hsum : ((k1 + k2 : ℕ) : ZMod p) = 0 := by simpa [Nat.cast_add] using hadd
          have hdvd : p ∣ k1 + k2 := (ZMod.natCast_eq_zero_iff (k1 + k2) p).mp hsum
          exact absurd hdvd (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
      · intro r hr
        rw [Finset.mem_filter, Finset.mem_erase] at hr
        obtain ⟨⟨hr0, _⟩, hchi⟩ := hr
        have hne : ((r.val : ℤ) : ZMod p) ≠ 0 := by simpa [ZMod.natCast_zmod_val] using hr0
        have hsq : IsSquare ((r.val : ℤ) : ZMod p) := (legendreSym.eq_one_iff p hne).mp hchi
        obtain ⟨a, ha⟩ := hsq
        have ha' : r = a ^ 2 := by
          have : ((r.val : ℤ) : ZMod p) = r := by simp [ZMod.natCast_zmod_val]
          rw [← this, ha, sq]
        have ha0 : a ≠ 0 := by rintro rfl; simp at ha'; exact hr0 ha'
        have hpos : 0 < a.val := Nat.pos_of_ne_zero fun h => ha0 (by
          have := ZMod.natCast_zmod_val a; rw [h, Nat.cast_zero] at this; exact this.symm)
        have hlt : a.val < p := a.val_lt
        by_cases hle : a.val ≤ (p - 1) / 2
        · refine ⟨a.val, Finset.mem_Icc.mpr ⟨by omega, hle⟩, ?_⟩
          rw [ZMod.natCast_zmod_val, ← ha']
        · refine ⟨p - a.val, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
          rw [Nat.cast_sub hlt.le, ZMod.natCast_self, zero_sub, ZMod.natCast_zmod_val, neg_sq, ← ha']
    rw [← hbij, Nat.card_Icc]
    omega
  have hpart : U = QR ∪ QNR := by
    ext x
    simp only [Finset.mem_union, QR, QNR, Finset.mem_filter]
    constructor
    · intro hx
      have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
      have hne : ((x.val : ℤ) : ZMod p) ≠ 0 := by simpa [ZMod.natCast_zmod_val] using hx0
      rcases legendreSym.eq_one_or_neg_one p hne with h1 | hm1
      · exact Or.inl ⟨hx, h1⟩
      · exact Or.inr ⟨hx, hm1⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  have hdisj : Disjoint QR QNR := by
    rw [Finset.disjoint_filter]
    intro x _ h1 hm1; omega
  have hU_card : U.card = p - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  have hQNR_card : QNR.card = (p - 1) / 2 := by
    have hsum_card : QR.card + QNR.card = U.card := by
      rw [← Finset.card_union_of_disjoint hdisj, ← hpart]
    omega
  rw [← Finset.add_sum_erase Finset.univ (chi p) (Finset.mem_univ 0), chi_zero, zero_add]
  change ∑ x ∈ U, chi p x = 0
  rw [hpart, Finset.sum_union hdisj]
  have h1 : ∑ x ∈ QR, chi p x = (QR.card : ℤ) := by
    calc ∑ x ∈ QR, chi p x
        = ∑ _x ∈ QR, (1 : ℤ) :=
          Finset.sum_congr rfl fun x hx => (Finset.mem_filter.mp (show x ∈ U.filter (fun y => chi p y = 1) from hx)).2
      _ = (QR.card : ℤ) := by simp
  have h2 : ∑ x ∈ QNR, chi p x = -(QNR.card : ℤ) := by
    calc ∑ x ∈ QNR, chi p x
        = ∑ _x ∈ QNR, (-1 : ℤ) :=
          Finset.sum_congr rfl fun x hx => (Finset.mem_filter.mp (show x ∈ U.filter (fun y => chi p y = -1) from hx)).2
      _ = -(QNR.card : ℤ) := by simp
  rw [h1, h2, hQR_card, hQNR_card]
  ring

private lemma sum_chi_shift_eq_neg_one (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {d : ZMod p} (hd : d ≠ 0) :
    ∑ x : ZMod p, chi p x * chi p (x + d) = -1 := by
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ 0), chi_zero, zero_mul, zero_add]
  have hterm : ∀ x ∈ (Finset.univ : Finset (ZMod p)).erase 0,
      chi p x * chi p (x + d) = chi p (1 + d * x⁻¹) := by
    intro x hx
    have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
    have h1 : chi p x * chi p x = 1 := chi_sq_of_ne_zero p hx0
    have h2 : x⁻¹ * (x + d) = 1 + d * x⁻¹ := by
      rw [mul_add, inv_mul_cancel₀ hx0, mul_comm x⁻¹ d]
    have hinv : chi p x * chi p x⁻¹ = 1 := by
      rw [← chi_mul, mul_inv_cancel₀ hx0, chi_one]
    calc
      chi p x * chi p (x + d)
          = chi p x * (chi p x * chi p x⁻¹) * chi p (x + d) := by rw [hinv, mul_one]
      _ = (chi p x * chi p x) * (chi p x⁻¹ * chi p (x + d)) := by ring
      _ = chi p (x⁻¹ * (x + d)) := by rw [h1, one_mul, ← chi_mul]
      _ = chi p (1 + d * x⁻¹) := by rw [h2]
  rw [Finset.sum_congr rfl hterm]
  have hbij : ∑ x ∈ (Finset.univ : Finset (ZMod p)).erase 0, chi p (1 + d * x⁻¹) =
      ∑ y ∈ (Finset.univ : Finset (ZMod p)).erase 1, chi p y := by
    refine Finset.sum_bij (fun x _ => 1 + d * x⁻¹) ?_ ?_ ?_ ?_
    · intro x hx
      have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ _⟩
      intro heq
      have h0 : d * x⁻¹ = 0 := by linear_combination heq
      exact absurd h0 (mul_ne_zero hd (inv_ne_zero hx0))
    · intro x1 hx1 x2 hx2 heq
      have hdx : d * x1⁻¹ = d * x2⁻¹ := by linear_combination heq
      have hinv : x1⁻¹ = x2⁻¹ := mul_left_cancel₀ hd hdx
      exact inv_injective hinv
    · intro y hy
      have hy1 : y ≠ 1 := (Finset.mem_erase.mp hy).1
      have hsub : y - 1 ≠ 0 := sub_ne_zero.mpr hy1
      refine ⟨d * (y - 1)⁻¹, Finset.mem_erase.mpr ⟨mul_ne_zero hd (inv_ne_zero hsub), Finset.mem_univ _⟩, ?_⟩
      field_simp [hd, hsub]
      ring
    · intro x _; rfl
  rw [hbij]
  have htot := sum_chi_eq_zero p hp2
  rw [← Finset.add_sum_erase Finset.univ (chi p) (Finset.mem_univ 1), chi_one] at htot
  omega

private def paleyMat (p : ℕ) [Fact p.Prime] : Matrix (Fin (p + 1)) (Fin (p + 1)) ℤ :=
  fun i j =>
    if hi : i.val < p then
      if hj : j.val < p then chi p ((i.val : ZMod p) - (j.val : ZMod p)) else 1
    else
      if hj : j.val < p then 1 else 0

end OMA.Proof_oeis_a000952_R1_H1

theorem OMA.solution : OMA.R_oeis_a000952_R1.H1 := by
  intro p hp h4
  open OMA.S_oeis_a000952 OMA.Proof_oeis_a000952_R1_H1 in
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  let A := paleyMat p
  refine ⟨A, ?_, ?_, ?_⟩
  · ext i j
    simp only [Matrix.transpose_apply, A, paleyMat]
    by_cases hi : i.val < p <;> by_cases hj : j.val < p <;> simp [hi, hj]
    have hsub : ((j.val : ZMod p) - (i.val : ZMod p)) = -((i.val : ZMod p) - (j.val : ZMod p)) := by
      ring
    rw [hsub, chi_neg_of_mod_four p h4]
  · intro i j
    simp only [A, paleyMat]
    split_ifs
    · exact chi_values p _
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
  · ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    rw [Fin.sum_univ_castSucc]
    have hlast : (Fin.last p).val = p := Fin.val_last p
    have hcast_lt : ∀ k : Fin p, (k.castSucc : Fin (p + 1)).val < p := fun k => k.isLt
    by_cases hi : i.val < p <;> by_cases hj : j.val < p
    · have hsum_eq :
          ∑ k : Fin p, A i k.castSucc * A j k.castSucc =
            ∑ x : ZMod p, chi p ((i.val : ZMod p) - x) * chi p ((j.val : ZMod p) - x) := by
        have hcast_fin : ∑ k : Fin p, A i k.castSucc * A j k.castSucc =
            ∑ k : Fin p, chi p ((i.val : ZMod p) - (k.val : ZMod p)) *
              chi p ((j.val : ZMod p) - (k.val : ZMod p)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          simp [A, paleyMat, hi, hj, hcast_lt k]
        rw [hcast_fin]
        refine Finset.sum_bij (fun (k : Fin p) _ => (k.val : ZMod p))
          (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
        · intro k1 _ k2 _ heq
          have hv := congrArg ZMod.val heq
          rw [ZMod.val_natCast_of_lt k1.isLt, ZMod.val_natCast_of_lt k2.isLt] at hv
          exact Fin.ext hv
        · intro x _
          exact ⟨⟨x.val, x.val_lt⟩, Finset.mem_univ _, ZMod.natCast_zmod_val x⟩
      have hlast_term : A i (Fin.last p) * A j (Fin.last p) = 1 := by
        simp [A, paleyMat, hi, hj, hlast]
      rw [hsum_eq, hlast_term]
      by_cases hij : i = j
      · subst hij
        simp only [↓reduceIte, mul_one]
        have hshift : ∑ x : ZMod p, chi p ((i.val : ZMod p) - x) * chi p ((i.val : ZMod p) - x) =
            ∑ y : ZMod p, chi p y * chi p y := by
          refine Fintype.sum_equiv (Equiv.subLeft (i.val : ZMod p)) _ _ fun x => rfl
        rw [hshift, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ 0), chi_zero, zero_mul, zero_add]
        have hones : ∑ y ∈ (Finset.univ : Finset (ZMod p)).erase 0, chi p y * chi p y =
            ((Finset.univ : Finset (ZMod p)).erase 0).card := by
          rw [Finset.sum_congr rfl fun y hy => chi_sq_of_ne_zero p (Finset.mem_erase.mp hy).1]
          simp
        rw [hones, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
        have hp1 : 1 ≤ p := hp.one_le
        omega
      · simp only [hij, ↓reduceIte, mul_zero]
        have hne : (j.val : ZMod p) - (i.val : ZMod p) ≠ 0 := by
          intro h0
          have heq : (j.val : ZMod p) = (i.val : ZMod p) := sub_eq_zero.mp h0
          have hv := congrArg ZMod.val heq
          rw [ZMod.val_natCast_of_lt hj, ZMod.val_natCast_of_lt hi] at hv
          exact hij (Fin.ext hv.symm)
        have hshift : ∑ x : ZMod p, chi p ((i.val : ZMod p) - x) * chi p ((j.val : ZMod p) - x) =
            ∑ y : ZMod p, chi p y * chi p (y + ((j.val : ZMod p) - (i.val : ZMod p))) := by
          refine Fintype.sum_equiv (Equiv.subLeft (i.val : ZMod p)) _ _ fun x => ?_
          congr 2
          dsimp [Equiv.subLeft]
          ring
        rw [hshift, sum_chi_shift_eq_neg_one p hp2 hne]
        ring
    · have hij : i ≠ j := fun h => hj (h ▸ hi)
      simp only [hij, ↓reduceIte, mul_zero]
      have hlast_term : A i (Fin.last p) * A j (Fin.last p) = 0 := by
        simp [A, paleyMat, hi, hj, hlast]
      rw [hlast_term, add_zero]
      have hsum_eq : ∑ k : Fin p, A i k.castSucc * A j k.castSucc =
          ∑ x : ZMod p, chi p ((i.val : ZMod p) - x) := by
        have h1 : ∑ k : Fin p, A i k.castSucc * A j k.castSucc =
            ∑ k : Fin p, chi p ((i.val : ZMod p) - (k.val : ZMod p)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          simp [A, paleyMat, hi, hj, hcast_lt k]
        rw [h1]
        refine Finset.sum_bij (fun (k : Fin p) _ => (k.val : ZMod p))
          (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
        · intro k1 _ k2 _ heq
          have hv := congrArg ZMod.val heq
          rw [ZMod.val_natCast_of_lt k1.isLt, ZMod.val_natCast_of_lt k2.isLt] at hv
          exact Fin.ext hv
        · intro x _
          exact ⟨⟨x.val, x.val_lt⟩, Finset.mem_univ _, ZMod.natCast_zmod_val x⟩
      rw [hsum_eq]
      have hshift : ∑ x : ZMod p, chi p ((i.val : ZMod p) - x) = ∑ y : ZMod p, chi p y :=
        Fintype.sum_equiv (Equiv.subLeft (i.val : ZMod p)) _ _ fun _ => rfl
      rw [hshift, sum_chi_eq_zero p hp2]
    · have hij : i ≠ j := fun h => hi (h ▸ hj)
      simp only [hij, ↓reduceIte, mul_zero]
      have hlast_term : A i (Fin.last p) * A j (Fin.last p) = 0 := by
        simp [A, paleyMat, hi, hj, hlast]
      rw [hlast_term, add_zero]
      have hsum_eq : ∑ k : Fin p, A i k.castSucc * A j k.castSucc =
          ∑ x : ZMod p, chi p ((j.val : ZMod p) - x) := by
        have h1 : ∑ k : Fin p, A i k.castSucc * A j k.castSucc =
            ∑ k : Fin p, chi p ((j.val : ZMod p) - (k.val : ZMod p)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          simp [A, paleyMat, hi, hj, hcast_lt k]
        rw [h1]
        refine Finset.sum_bij (fun (k : Fin p) _ => (k.val : ZMod p))
          (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
        · intro k1 _ k2 _ heq
          have hv := congrArg ZMod.val heq
          rw [ZMod.val_natCast_of_lt k1.isLt, ZMod.val_natCast_of_lt k2.isLt] at hv
          exact Fin.ext hv
        · intro x _
          exact ⟨⟨x.val, x.val_lt⟩, Finset.mem_univ _, ZMod.natCast_zmod_val x⟩
      rw [hsum_eq]
      have hshift : ∑ x : ZMod p, chi p ((j.val : ZMod p) - x) = ∑ y : ZMod p, chi p y :=
        Fintype.sum_equiv (Equiv.subLeft (j.val : ZMod p)) _ _ fun _ => rfl
      rw [hshift, sum_chi_eq_zero p hp2]
    · have hij : i = j := Fin.ext (by omega)
      subst hij
      simp only [↓reduceIte, mul_one]
      have hlast_term : A i (Fin.last p) * A i (Fin.last p) = 0 := by
        simp [A, paleyMat, hi, hlast]
      rw [hlast_term, add_zero]
      have h1 : ∑ k : Fin p, A i k.castSucc * A i k.castSucc = ∑ _k : Fin p, (1 : ℤ) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp [A, paleyMat, hi, hcast_lt k]
      rw [h1]
      simp
