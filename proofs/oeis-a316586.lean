import OMAStatements.S_oeis_a316586
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic

namespace OMA.P_oeis_a316586

open OMA.S_oeis_a316586
open scoped Classical

private lemma char_p_one_add_pow {p : ℕ} [Fact p.Prime]
    (N : Matrix (Fin 2) (Fin 2) (ZMod p)) :
    (1 + N) ^ p = 1 + N ^ p := by
  have hp : p.Prime := Fact.out
  have hcomm : Commute (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) N := Commute.one_left N
  rw [hcomm.add_pow]
  have hsplit : ∑ m ∈ Finset.range (p + 1),
      (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ m * N ^ (p - m) * (p.choose m : ℕ) =
      N ^ p + (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
    rw [Finset.sum_range_succ, Nat.choose_self, Nat.sub_self, pow_zero, one_pow, one_mul,
      Nat.cast_one, mul_one]
    have h0 : 0 ∈ Finset.range p := Finset.mem_range.mpr hp.pos
    rw [← Finset.add_sum_erase _ _ h0, Nat.choose_zero_right, Nat.sub_zero, pow_zero, one_mul,
      Nat.cast_one, mul_one]
    have hmid : ∑ m ∈ (Finset.range p).erase 0,
        (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ m * N ^ (p - m) * (p.choose m : ℕ) = 0 := by
      refine Finset.sum_eq_zero (fun m hm => ?_)
      have hm0 : m ≠ 0 := (Finset.mem_erase.mp hm).1
      have hmp : m < p := Finset.mem_range.mp (Finset.mem_erase.mp hm).2
      have hdvd : p ∣ p.choose m := hp.dvd_choose_self hm0 hmp
      have hcast : ((p.choose m : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
      have hmat : ((p.choose m : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod p)) = 0 := by
        ext i j
        simp [Matrix.natCast_apply, hcast]
      rw [hmat, mul_zero]
    rw [hmid, add_zero]
  rw [hsplit, add_comm]

private lemma mat2_cayley_hamilton {R : Type*} [CommRing R] (N : Matrix (Fin 2) (Fin 2) R) :
    N ^ 2 = (N 0 0 + N 1 1) • N - (N 0 0 * N 1 1 - N 0 1 * N 1 0) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sq, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private lemma mat2_det_eq {R : Type*} [CommRing R] (N : Matrix (Fin 2) (Fin 2) R) :
    N.det = N 0 0 * N 1 1 - N 0 1 * N 1 0 := by
  simp [Matrix.det_fin_two]

private lemma nilpotent_iff_sq_zero {p : ℕ} [Fact p.Prime]
    (N : Matrix (Fin 2) (Fin 2) (ZMod p)) :
    N ^ p = 0 ↔ N ^ 2 = 0 := by
  have hp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hp.two_le
  constructor
  · intro hNp
    have hdetp : N.det ^ p = 0 := by
      rw [← Matrix.det_pow, hNp, Matrix.det_zero]
    have hdet : N.det = 0 := eq_zero_of_pow_eq_zero hdetp
    have hdet' : N 0 0 * N 1 1 - N 0 1 * N 1 0 = 0 := by rwa [← mat2_det_eq]
    set t : ZMod p := N 0 0 + N 1 1
    have hN2 : N ^ 2 = t • N := by
      rw [mat2_cayley_hamilton, hdet', zero_smul, sub_zero]
    have hNk : ∀ k : ℕ, 1 ≤ k → N ^ k = t ^ (k - 1) • N := by
      intro k hk
      induction k with
      | zero => omega
      | succ k ih =>
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · simp
        · rw [pow_succ, ih hkpos, smul_mul_assoc, ← sq, hN2, smul_smul, ← pow_succ,
            show k - 1 + 1 = k by omega]
          simp
    have h0 : t ^ (p - 1) • N = 0 := by
      rw [← hNk p (by omega), hNp]
    by_cases ht : t = 0
    · rw [hN2, ht, zero_smul]
    · have htp : t ^ (p - 1) ≠ 0 := pow_ne_zero _ ht
      have hN0 : N = 0 := by
        have := congr_arg ((t ^ (p - 1))⁻¹ • ·) h0
        simp [smul_smul, inv_mul_cancel₀ htp] at this
        exact this
      rw [hN0, zero_pow (by norm_num)]
  · intro hN2
    calc N ^ p = N ^ (2 + (p - 2)) := by congr 1; omega
      _ = N ^ 2 * N ^ (p - 2) := pow_add N 2 (p - 2)
      _ = 0 := by rw [hN2, zero_mul]

private lemma sq_zero_iff_entries {p : ℕ} [Fact p.Prime]
    (N : Matrix (Fin 2) (Fin 2) (ZMod p)) :
    N ^ 2 = 0 ↔ N 1 1 = -N 0 0 ∧ N 0 0 ^ 2 + N 0 1 * N 1 0 = 0 := by
  constructor
  · intro hN2
    have hdet2 : N.det ^ 2 = 0 := by
      rw [← Matrix.det_pow, hN2, Matrix.det_zero]
    have hdet : N 0 0 * N 1 1 - N 0 1 * N 1 0 = 0 := by
      rw [← mat2_det_eq]; exact eq_zero_of_pow_eq_zero hdet2
    have htN : (N 0 0 + N 1 1) • N = 0 := by
      have hch := mat2_cayley_hamilton N
      rw [hN2, hdet, zero_smul, sub_zero] at hch
      exact hch.symm
    have htr : N 0 0 + N 1 1 = 0 := by
      by_cases hN0 : N = 0
      · simp [hN0]
      · by_contra ht
        have := congr_arg ((N 0 0 + N 1 1)⁻¹ • ·) htN
        simp [smul_smul, inv_mul_cancel₀ ht] at this
        exact hN0 this
    have hd : N 1 1 = -N 0 0 := eq_neg_of_add_eq_zero_right htr
    refine ⟨hd, ?_⟩
    rw [hd] at hdet
    linear_combination -hdet
  · rintro ⟨hd, hq⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sq, Matrix.mul_apply, Fin.sum_univ_two, hd]
    · linear_combination hq
    · ring
    · ring
    · linear_combination hq

private lemma det_one_add_of_sq_zero {p : ℕ} [Fact p.Prime]
    (N : Matrix (Fin 2) (Fin 2) (ZMod p)) (hN2 : N ^ 2 = 0) :
    (1 + N).det = 1 := by
  obtain ⟨hd, hq⟩ := (sq_zero_iff_entries N).mp hN2
  simp [Matrix.det_fin_two, hd]
  linear_combination -hq

private lemma prove_a316586 (p : ℕ) (hp : p.Prime) :
    Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) // x ^ p = 1} = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  let toN : {x : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) // x ^ p = 1} →
      Matrix (Fin 2) (Fin 2) (ZMod p) := fun x => (x.1 : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1
  have htoN_sq : ∀ x, (toN x) ^ 2 = 0 := by
    intro ⟨x, hx⟩
    rw [← nilpotent_iff_sq_zero]
    have hxp : (x : Matrix (Fin 2) (Fin 2) (ZMod p)) ^ p = 1 := by
      exact_mod_cast congr_arg Subtype.val hx
    have h1 : (1 + toN ⟨x, hx⟩) ^ p = 1 := by
      dsimp [toN]; rwa [add_sub_cancel]
    rw [char_p_one_add_pow] at h1
    exact add_left_cancel (h1.trans (add_zero 1).symm)
  let mkX : ∀ N : Matrix (Fin 2) (Fin 2) (ZMod p), N ^ 2 = 0 →
      {x : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) // x ^ p = 1} := fun N hN =>
    ⟨⟨1 + N, det_one_add_of_sq_zero N hN⟩, by
      apply Subtype.ext
      change (1 + N) ^ p = 1
      rw [char_p_one_add_pow, (nilpotent_iff_sq_zero N).mpr hN, add_zero]⟩
  have heq : {x : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) // x ^ p = 1} ≃
      ZMod p × ZMod p :=
    { toFun := fun x =>
        let N := toN x
        if N 0 1 = 0 then (0, N 1 0) else (N 0 1, N 0 0)
      invFun := fun ⟨u, v⟩ =>
        if hu : u = 0 then
          mkX !![0, 0; v, 0] (by
            rw [sq_zero_iff_entries]; simp)
        else
          mkX !![v, u; -(v ^ 2) / u, -v] (by
            rw [sq_zero_iff_entries]
            refine ⟨by simp, ?_⟩
            simp [mul_div_cancel₀ _ hu])
      left_inv := by
        intro x
        have hsq := htoN_sq x
        obtain ⟨hd, hq⟩ := (sq_zero_iff_entries (toN x)).mp hsq
        dsimp only
        by_cases hb : toN x 0 1 = 0
        · rw [if_pos hb, dif_pos rfl]
          have ha : toN x 0 0 = 0 := by
            rw [hb, zero_mul, add_zero] at hq
            exact eq_zero_of_pow_eq_zero hq
          apply Subtype.ext; apply Subtype.ext
          change 1 + !![0, 0; toN x 1 0, 0] = (x.1 : Matrix (Fin 2) (Fin 2) (ZMod p))
          have hmat : !![0, 0; toN x 1 0, 0] = toN x := by
            ext i j
            fin_cases i <;> fin_cases j
            · simp [ha]
            · simp [hb]
            · rfl
            · simp [hd, ha]
          rw [hmat]; dsimp [toN]; exact add_sub_cancel 1 _
        · rw [if_neg hb, dif_neg hb]
          have hc : toN x 1 0 = -(toN x 0 0 ^ 2) / toN x 0 1 := by
            apply eq_div_of_mul_eq hb
            linear_combination hq
          apply Subtype.ext; apply Subtype.ext
          change 1 + !![toN x 0 0, toN x 0 1; -(toN x 0 0 ^ 2) / toN x 0 1, -toN x 0 0] =
            (x.1 : Matrix (Fin 2) (Fin 2) (ZMod p))
          have hmat : !![toN x 0 0, toN x 0 1; -(toN x 0 0 ^ 2) / toN x 0 1, -toN x 0 0] = toN x := by
            ext i j
            fin_cases i <;> fin_cases j
            · rfl
            · rfl
            · exact hc.symm
            · exact hd.symm
          rw [hmat]; dsimp [toN]; exact add_sub_cancel 1 _
      right_inv := by
        rintro ⟨u, v⟩
        have hN : ∀ M hM, toN (mkX M hM) = M := fun M _ => by dsimp [toN, mkX]; simp
        dsimp only
        by_cases hu : u = 0
        · subst hu
          rw [dif_pos rfl]
          simp [hN]
        · rw [dif_neg hu]
          simp [hN, hu] }
  rw [Nat.card_congr heq, Nat.card_prod, Nat.card_eq_fintype_card, ZMod.card p, sq]

end OMA.P_oeis_a316586

theorem OMA.solution : type_of% @OMA.S_oeis_a316586.main :=
  OMA.P_oeis_a316586.prove_a316586
