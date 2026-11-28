import OMAStatements.S_oeis_a002034

/-!
The finite cosine sum is the indicator of divisibility. Applying it
to factorials counts all indices from the first divisible factorial
through the endpoint of the summation.
-/

namespace Kempner

open Finset

private theorem shifted_geom (n : ℕ) (z : ℂ) :
    (∑ k ∈ Icc 1 n, z ^ k) = z * ∑ k ∈ range n, z ^ k := by
  rw [mul_sum]
  symm
  refine sum_bij (fun k _ => k+1) (fun k hk => ?_) ?_ ?_ ?_
  · exact mem_Icc.mpr ⟨by omega, Nat.succ_le_iff.mpr (mem_range.mp hk)⟩
  · intro k _ l _ h
    omega
  · intro k hk
    obtain ⟨h₁,h₂⟩ := mem_Icc.mp hk
    exact ⟨k-1,mem_range.mpr (by omega),by omega⟩
  · intro k _
    rw [pow_succ']
    
private theorem cosine_filter (n t : ℕ) (hn : n ≠ 0) :
    (∑ k ∈ Icc 1 n, Real.cos (-2 * Real.pi * k / n * t) / n) =
      if n ∣ t then (1:ℝ) else 0 := by
  let ζ := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))
  let z := ζ ^ t
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn
  have hpow : z ^ n = 1 := by
    dsimp [z]
    rw [← pow_mul, mul_comm t n, pow_mul, hζ.pow_eq_one, one_pow]
  have hreal (k : ℕ) :
      Real.cos (-2 * Real.pi * k / n * t) = (z ^ k).re := by
    rw [show (-2 * Real.pi * k / n * t : ℝ) = -(2 * Real.pi * k / n * t) by ring,
      Real.cos_neg, ← Complex.exp_ofReal_mul_I_re]
    dsimp [z,ζ]
    rw [← pow_mul, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hsum : (∑ k ∈ Icc 1 n, z ^ k) = if n ∣ t then (n:ℂ) else 0 := by
    by_cases hd : n ∣ t
    · have hz : z = 1 := (hζ.pow_eq_one_iff_dvd t).mpr hd
      simp [hz,hd,Nat.card_Icc]
    · have hz : z ≠ 1 := fun hz => hd ((hζ.pow_eq_one_iff_dvd t).mp hz)
      have hg := geom_sum_mul z n
      rw [hpow, sub_self] at hg
      have hzero : (∑ i ∈ range n, z ^ i) = 0 :=
        (mul_eq_zero.mp hg).resolve_right (sub_ne_zero.mpr hz)
      simp [shifted_geom, hzero, hd]
  rw [← sum_div]
  simp_rw [hreal]
  rw [← Complex.re_sum, hsum]
  split_ifs <;> simp [show (n:ℝ) ≠ 0 by exact_mod_cast hn]

end Kempner

open OMA.S_oeis_a002034 Finset in
theorem OMA.solution : type_of% @OMA.S_oeis_a002034.main := by
  intro n hn
  have hn0 : 0 < n := by omega
  let S : Set ℕ := {m | 0 < m ∧ n ∣ m.factorial}
  have hnS : n ∈ S := ⟨hn0, Nat.dvd_factorial hn0 le_rfl⟩
  have haS : a n ∈ S := Nat.sInf_mem ⟨n, hnS⟩
  have han : a n ≤ n := Nat.sInf_le hnS
  have ha0 : 0 < a n := haS.1
  have iff_a (m : ℕ) (hm : 0 < m) : n ∣ m.factorial ↔ a n ≤ m :=
    ⟨fun h => Nat.sInf_le (show m ∈ S from ⟨hm,h⟩),
      fun h => haS.2.trans (Nat.factorial_dvd_factorial h)⟩
  rw [sum_comm]
  have hs : (∑ m ∈ Icc 1 n, ∑ k ∈ Icc 1 n,
        Real.cos (-2 * Real.pi * k / n * (m.factorial : ℝ)) / n) =
      ((Icc (a n) n).card : ℝ) := by
    calc
      _ = ∑ m ∈ Icc 1 n, if a n ≤ m then (1:ℝ) else 0 := by
        apply sum_congr rfl
        intro m hm
        rw [Kempner.cosine_filter n m.factorial hn0.ne']
        exact if_congr (iff_a m (by have := (mem_Icc.mp hm).1; omega)) rfl rfl
      _ = _ := by
        rw [← Finset.sum_filter]
        have eq : (Icc 1 n).filter (fun m : ℕ => a n ≤ m) = Icc (a n) n := by
          ext m
          simp only [mem_filter, mem_Icc]
          omega
        simp [eq]
  rw [hs, Nat.card_Icc, Nat.cast_sub (Nat.le_succ_of_le han), Nat.cast_succ]
  ring
