import FormalConjectures.OEIS.«228304»
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.GroupTheory.Perm.Cycle.Type

/-! Shorter proof of `OeisA228304.conjecture_2` via Lucas's theorem and column reversal. -/

open scoped BigOperators

private lemma lucas (p n k : ℕ) [Fact p.Prime] :
    (n.choose k : ZMod p) = ((n % p).choose (k % p) : ZMod p) * ((n / p).choose (k / p) : ZMod p) := by
  rw [← Nat.cast_mul, ZMod.natCast_eq_natCast_iff]
  exact Choose.choose_modEq_choose_mod_mul_choose_div_nat

private def cent (p k : ℕ) : ZMod p := ((2 * k).choose k : ℕ)
private def sumd (p n k : ℕ) : ZMod p :=
  (-1) ^ k * (n.choose k : ZMod p) ^ 2 * cent p k * cent p (n - k)

private lemma czero (p k : ℕ) [Fact p.Prime] (hk : k < p) (hc : p ≤ 2 * k) : cent p k = 0 := by
  unfold cent
  rw [lucas, show 2 * k % p = 2 * k - p by rw [Nat.mod_eq_sub_mod hc, Nat.mod_eq_of_lt (by omega)],
    Nat.mod_eq_of_lt hk, Nat.choose_eq_zero_of_lt (by omega)]; simp

theorem OMA.solution : type_of% @OeisA228304.conjecture_2 := by
  classical
  intro p hp hodd
  let inst : Fact p.Prime := ⟨hp⟩
  have hodd' : Odd p := hp.odd_of_ne_two hodd
  have hmod : p % 2 = 1 := Nat.odd_iff.mp hodd'
  have smod {k : ℕ} (hk : k < p) : (p + k) % p = k := by simp [Nat.add_mod_left, Nat.mod_eq_of_lt hk]
  have sdiv {k : ℕ} (hk : k < p) : (p + k) / p = 1 := by
    rw [show p + k = k + p * 1 by omega, Nat.add_mul_div_left _ _ hp.pos, Nat.div_eq_of_lt hk, zero_add]
  have cshift {k : ℕ} (hk : k < p) : cent p (p + k) = 2 * cent p k := by
    have hd : 2 * (p + k) = 2 * k + p * 2 := by omega
    change (((2 * (p + k)).choose (p + k) : ℕ) : ZMod p) = 2 * cent p k
    rw [lucas, hd, Nat.add_mul_mod_self_left, smod hk, sdiv hk, Nat.add_mul_div_left _ _ hp.pos]
    by_cases h : 2 * k < p
    · rw [Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h]; simp [cent, mul_comm]
    · rw [show 2 * k % p = 2 * k - p by rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)],
        Nat.choose_eq_zero_of_lt (by omega), czero p k hk (by omega)]; simp
  have ccast (n : ℕ) : (OeisA228304.c n : ZMod p) = ∑ k ∈ Finset.range (n + 1), sumd p n k := by
    simp [OeisA228304.c, sumd, cent]
  let C : Matrix (Fin p) (Fin p) ℤ := fun i j => OeisA228304.c (i.val + j.val)
  let D := C.map (Int.castRingHom (ZMod p))
  change C.det ≡ 1 [ZMOD p]
  rw [← ZMod.intCast_eq_intCast_iff, Int.cast_one]
  change (Int.castRingHom (ZMod p)) C.det = 1; rw [RingHom.map_det]
  change D.det = 1
  let T := D.submatrix id (Fin.revPerm : Equiv.Perm (Fin p))
  have hT : T.IsUpperTriangular := fun i j hij => by
    have hj := j.isLt; have hi := i.isLt; change j.val < i.val at hij
    change (OeisA228304.c (i.val + (Fin.rev j).val) : ZMod p) = 0
    rw [Fin.val_rev, show i.val + (p - (j.val + 1)) = p + (i.val - (j.val + 1)) by omega]
    set d := i.val - (j.val + 1)
    have hd : d < p := by omega
    have hlo {k : ℕ} (hk : k < p) : ((p + d).choose k : ZMod p) = (d.choose k : ZMod p) := by
      rw [lucas, smod hd, Nat.mod_eq_of_lt hk, Nat.div_eq_of_lt hk]; simp
    have hcut : ∑ k ∈ Finset.range (d + 1), sumd p (p + d) k = ∑ k ∈ Finset.range p, sumd p (p + d) k :=
      Finset.sum_subset (Finset.range_mono (by omega)) fun k hk hk' => by
        simp only [Finset.mem_range, not_lt] at hk hk'
        unfold sumd; rw [hlo hk, Nat.choose_eq_zero_of_lt (by omega)]; simp
    have hpair (k : ℕ) (hk : k < d + 1) : sumd p (p + d) (p + k) = -sumd p (p + d) k := by
      unfold sumd
      have hhi : ((p + d).choose (p + k) : ZMod p) = (d.choose k : ZMod p) := by
        rw [lucas, smod hd, smod (by omega), sdiv hd, sdiv (by omega)]; simp
      rw [hhi, hlo (by omega), show p + d - (p + k) = d - k by omega,
        show p + d - k = p + (d - k) by omega, cshift (by omega), cshift (by omega),
        pow_add, hodd'.neg_one_pow]
      ring
    rw [ccast, Nat.add_assoc, Finset.sum_range_add, ← hcut, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun k hk => by rw [hpair k (Finset.mem_range.mp hk), add_neg_cancel]
  let a : ZMod p := (-1 : ZMod p) ^ ((p - 1) / 2)
  have hdiag (i : Fin p) : T i i = a := by
    change (OeisA228304.c (i.val + (Fin.rev i).val) : ZMod p) = a
    have hi := i.isLt
    rw [Fin.val_rev, show i.val + (p - (i.val + 1)) = p - 1 by omega]
    let m := (p - 1) / 2
    have hpred : ∀ k < p, ((p - 1).choose k : ZMod p) = (-1 : ZMod p) ^ k := fun k => by
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        have h := congrArg (fun n : ℕ => (n : ZMod p)) (Nat.choose_succ_right_eq (p - 1) k)
        simp only [Nat.cast_mul] at h
        have hneg : ((p - 1 - k : ℕ) : ZMod p) = -((k + 1 : ℕ) : ZMod p) :=
          eq_neg_of_add_eq_zero_left (by rw [← Nat.cast_add, show p - 1 - k + (k + 1) = p by omega, ZMod.natCast_self])
        rw [ih (by omega), hneg] at h
        refine mul_right_cancel₀ (by rw [ne_eq, ZMod.natCast_eq_zero_iff]; exact Nat.not_dvd_of_pos_of_lt (by omega) hk) ?_
        rw [pow_succ]; linear_combination h
    have hs : ((-1 : ZMod p) ^ m) ^ 2 = 1 := by
      rw [← pow_mul]; exact (show Even (m * 2) from ⟨m, by omega⟩).neg_one_pow
    rw [ccast, Finset.sum_eq_single m]
    · unfold sumd cent
      rw [show p - 1 - m = m by omega, show 2 * m = p - 1 by omega, hpred m (by omega),
        hs, mul_one, mul_assoc, ← pow_two, hs, mul_one]
    · intro k hk hkm; simp only [Finset.mem_range] at hk; unfold sumd
      rcases lt_or_gt_of_ne hkm with h | h
      · rw [czero p (p - 1 - k) (by omega) (by omega), mul_zero]
      · rw [czero p k (by omega) (by omega), mul_zero, zero_mul]
    · exact fun hn => (hn (Finset.mem_range.mpr (by omega))).elim
  have hdet : T.det = a := by
    rw [Matrix.det_of_isUpperTriangular hT]; simp_rw [hdiag]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    change ((-1 : ZMod p) ^ ((p - 1) / 2)) ^ p = a
    rw [← pow_mul, Nat.mul_comm ((p - 1) / 2) p, pow_mul, hodd'.neg_one_pow]
  have hs : (↑((Fin.revPerm : Equiv.Perm (Fin p)).sign : ℤ) : ZMod p) = a := by
    have hs2 : (Fin.revPerm : Equiv.Perm (Fin p)) ^ 2 = 1 := by ext; simp [pow_two]
    let mid : Fin p := ⟨(p - 1) / 2, by omega⟩
    let instU : Unique (Function.fixedPoints (Fin.revPerm : Equiv.Perm (Fin p))) :=
      ⟨⟨⟨mid, Fin.ext (by change (Fin.rev mid).1 = mid.1; rw [Fin.val_rev]; change p - ((p - 1) / 2 + 1) = (p - 1) / 2; omega)⟩⟩,
       fun i => Subtype.ext (Fin.ext (by
         have h := congrArg Fin.val i.property; change (Fin.rev i.1).1 = i.1.1 at h
         rw [Fin.val_rev] at h; have := i.1.isLt; change i.1.1 = (p - 1) / 2; omega))⟩
    rw [Equiv.Perm.sign_of_pow_two_eq_one hs2, Fintype.card_fin, Fintype.card_unique]; simp [a]
  change (D.submatrix id (Fin.revPerm : Equiv.Perm (Fin p))).det = a at hdet
  rw [Matrix.det_permute', hs] at hdet
  exact mul_left_cancel₀ (show a ≠ 0 by simp [a]) (by simpa using hdet)
