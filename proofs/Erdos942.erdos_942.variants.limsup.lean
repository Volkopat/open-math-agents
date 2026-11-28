import FormalConjectures.ErdosProblems.«942»

open Nat Finset in
theorem OMA.solution : type_of% @Erdos942.erdos_942.variants.limsup := by
  rw [Filter.limsup_eq_iInf_iSup_of_nat]
  refine iInf_eq_top.mpr fun N => ENat.eq_top_iff_forall_ge.mpr fun k => ?_
  set K := 2 * k
  let p := nth Nat.Prime
  have hp n : (p n).Prime := prime_nth_prime n
  have hsm : StrictMono p := nth_strictMono infinite_setOfPred_prime
  set Q := p K ^ 3
  have hQ : (0 : ℝ) < Q := by have := (hp K).pos; positivity
  let c (i : Fin K) := Real.sqrt ((p i : ℝ) ^ 3)
  have hc i : 0 < c i := Real.sqrt_pos.mpr (by have := (hp i).pos; positivity)
  let g (j : ℕ) (i : Fin K) := (j : ℝ) * (N + 1 : ℕ) * (c i)⁻¹
  obtain ⟨a, b, hab, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun (j : Fin (Q ^ K + 1)) (i : Fin K) => Fin.mk ⌊Int.fract (g j i) * Q⌋₊
      ((floor_lt (by positivity)).mpr (mul_lt_of_lt_one_left hQ (Int.fract_lt_one _))))
    (by simp)
  wlog hlt : a.1 < b.1 generalizing a b
  · exact this b a hab.symm hf.symm (by omega)
  set n := (b.1 - a.1) * (N + 1)
  have hNn : N + 1 ≤ n := Nat.le_mul_of_pos_left _ (by omega)
  set m := n - 1
  let z (i : Fin K) : ℤ := ⌊g b i⌋ - ⌊g a i⌋
  have hbd i : (m : ℝ) < z i * c i ∧ (z i : ℝ) * c i < m + 2 := by
    set x := Int.fract (g b i)
    set y := Int.fract (g a i)
    have hi : (⌊y * Q⌋₊ : ℝ) = ⌊x * Q⌋₊ := congrArg (Nat.cast ∘ Fin.val) (congrFun hf i)
    have habs : |x - y| * Q < 1 := by
      rw [← abs_of_pos hQ, ← abs_mul, sub_mul, abs_lt]
      constructor <;> linarith [floor_le (a := x * Q) (by positivity), lt_floor_add_one (x * Q),
        floor_le (a := y * Q) (by positivity), lt_floor_add_one (y * Q)]
    have hcQ : c i ≤ Q := (Real.sqrt_le_left hQ.le).mpr <| by
      norm_cast; exact (pow_le_pow_left' (hsm i.2).le 3).trans (le_self_pow two_ne_zero Q)
    have hmn : (m : ℝ) + 1 = n := by exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ n)
    suffices |(n : ℝ) - z i * c i| < 1 by rw [abs_lt] at this; constructor <;> linarith
    rw [show (n : ℝ) - z i * c i = (x - y) * c i by
      simp only [n, z, x, y, g, Int.fract, Nat.cast_mul, Nat.cast_sub hlt.le, Int.cast_sub]
      field_simp [(hc i).ne']; ring, abs_mul, abs_of_pos (hc i)]
    nlinarith [abs_nonneg (x - y)]
  set h := Erdos942.erdos_942.h
  have hsum : K ≤ h m + h (m + 1) := by
    dsimp [h, Erdos942.erdos_942.h]
    refine le_trans ?_ (card_union_le _ _)
    rw [← filter_union, Ico_union_Ico_eq_Ico (by gcongr; omega) (by gcongr; omega),
      ← Fintype.card_fin K, ← Finset.card_univ]
    apply card_le_card_of_injOn (fun (i : Fin K) => p i ^ 3 * (z i).natAbs ^ 2)
    · intro i _
      have ⟨hlo, hhi⟩ := hbd i
      have hsq : ((z i : ℝ) * c i) ^ 2 = (p i : ℝ) ^ 3 * |(z i : ℝ)| ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity), sq_abs, mul_comm]
      simp; refine ⟨⟨by rify; nlinarith, by rify; nlinarith⟩, fun q hq => ?_⟩
      obtain ⟨hqp, hqd, -⟩ := mem_primeFactors.mp hq
      rcases hqp.dvd_mul.mp hqd with h | h <;> have h2 := pow_dvd_pow_of_dvd (hqp.dvd_of_dvd_pow h) 2
      · exact (h2.trans (pow_dvd_pow _ (by omega))).mul_right _
      · exact h2.mul_left _
    · intro i _ j _ hij
      by_contra hne
      have hne0 l : (z l).natAbs ≠ 0 := fun h0 =>
        absurd (hbd l).1 (by simp [Int.natAbs_eq_zero.mp h0])
      have h1 := congrArg (·.factorization (p i)) hij
      simp [Nat.factorization_mul, (hp i).ne_zero, (hp j).ne_zero, hne0 i, hne0 j,
        (hp i).factorization_pow, (hp j).factorization_pow,
        (hsm.injective.ne (Fin.val_ne_of_ne hne)).symm] at h1
      omega
  by_cases hk : k ≤ h m
  · exact le_iSup₂_of_le m (by omega) (Nat.cast_le.mpr hk)
  · exact le_iSup₂_of_le (m + 1) (by omega) (Nat.cast_le.mpr (by omega))
