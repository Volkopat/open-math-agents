import OMAStatements.S_oeis_a371918
import Mathlib

/-!
Powers of two have every positive decimal prefix at arbitrarily large
exponents, by the irrational rotation with step log 2 on the circle of
circumference log 10. This supplies unused candidates at each greedy step.
At input 2^k, any eligible exponent is at least k, so k must already
have been used or must be chosen at that step.
-/

namespace OMA.P_oeis_a371918
open OMA.S_oeis_a371918

private theorem irrational_ratio : Irrational (Real.log 2 / Real.log 10) := by
  rintro ⟨q, hq⟩
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hd : (0:ℝ) < q.den := by exact_mod_cast q.den_pos
  rw [Rat.cast_def] at hq
  have hm := (div_eq_div_iff (ne_of_gt hd) (ne_of_gt h10)).mp hq
  have hpos : (0:ℝ) < q.num := pos_of_mul_pos_left (hm ▸ mul_pos h2 hd) h10.le
  have hz : (0:ℤ) < q.num := by exact_mod_cast hpos
  lift q.num to ℕ using hz.le with m hm' 
  have hpow : (2:ℕ)^q.den = 10^m := by
    have h : Real.log ((2:ℝ)^q.den) = Real.log ((10:ℝ)^m) := by
      rw [Real.log_pow, Real.log_pow]
      push_cast at hm
      linarith
    exact_mod_cast Real.log_injOn_pos (show 0 < (2:ℝ)^q.den by positivity) (show 0 < (10:ℝ)^m by positivity) h
  have hmpos : 0 < m := by omega
  have hdiv : 5 ∣ (2:ℕ)^q.den := hpow ▸ dvd_pow (by decide : 5 ∣ 10) (Nat.ne_of_gt hmpos)
  exact (by decide : ¬ (5 ∣ (2:ℕ))) ((by decide : Nat.Prime 5).dvd_of_dvd_pow hdiv)

private theorem prefixHit (n B : ℕ) (hn : 0 < n) :
    ∃ k j : ℕ, B < k ∧ 10^j ≤ 2^k ∧ 2^k / 10^j = n := by
  let p := Real.log 10
  have hp : 0 < p := Real.log_pos (by norm_num)
  let : Fact (0 < p) := ⟨hp⟩
  let b := B+n+2
  let t := (b:ℝ)*Real.log 2
  let I := Set.Ioo (Real.log n - t) (Real.log (n+1) - t)
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have hi : I.Nonempty := Set.nonempty_Ioo.mpr (by apply sub_lt_sub_right; apply Real.log_lt_log hn'; linarith)
  have hd : DenseRange (fun k : ℕ => k • (↑(Real.log 2) : AddCircle p)) :=
    denseRange_zsmul_iff_nsmul.mp (AddCircle.denseRange_zsmul_coe_iff.mpr irrational_ratio)
  have ho : IsOpenMap ((↑) : ℝ → AddCircle p) := QuotientAddGroup.isOpenMap_coe
  obtain ⟨k,y,hy,he⟩ := hd.exists_mem_open (ho I isOpen_Ioo) (hi.image _)
  have he' : (↑((k:ℝ)*Real.log 2 - y) : AddCircle p) = 0 := by
    rw [AddCircle.coe_sub, ← nsmul_eq_mul, AddCircle.coe_nsmul, he, sub_self]
  obtain ⟨j,hj⟩ := (AddCircle.coe_eq_zero_iff p).mp he'
  rw [zsmul_eq_mul] at hj
  change Real.log n - t < y ∧ y < Real.log (n+1) - t at hy
  dsimp [t] at hy
  have hl : Real.log n + (j:ℝ)*p < (k+b:ℕ)*Real.log 2 := by push_cast; linarith [hy.1]
  have hu : ((k+b:ℕ):ℝ)*Real.log 2 < Real.log (n+1) + (j:ℝ)*p := by push_cast; linarith [hy.2]
  have hnle : n+1 ≤ 2^(k+b) := by
    have h : k+b < 2^(k+b) := Nat.lt_two_pow_self
    dsimp [b] at h ⊢; omega
  have hj0 : 0 ≤ j := by
    by_contra! hneg
    have hneg' : (j:ℝ)*p < 0 := mul_neg_of_neg_of_pos (by exact_mod_cast hneg) hp
    have hle : Real.log (n+1) ≤ Real.log ((2:ℝ)^(k+b)) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hnle)
    rw [Real.log_pow] at hle
    linarith
  lift j to ℕ using hj0
  push_cast at hl hu
  have lo : n*10^j < 2^(k+b) := by
    have h : Real.log ((n:ℝ)*10^j) < Real.log ((2:ℝ)^(k+b)) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      exact_mod_cast hl
    exact_mod_cast (Real.log_lt_log_iff (by positivity) (by positivity)).mp h
  have up : 2^(k+b) < (n+1)*10^j := by
    have h : Real.log ((2:ℝ)^(k+b)) < Real.log (((n:ℝ)+1)*10^j) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      exact_mod_cast hu
    exact_mod_cast (Real.log_lt_log_iff (by positivity) (by positivity)).mp h
  exact ⟨k+b,j,by dsimp [b]; omega, (Nat.le_mul_of_pos_left _ hn).trans lo.le,
    Nat.div_eq_of_lt_le lo.le up⟩

private theorem candidates (n B : ℕ) : ∃ k, B < k ∧ contains (2^k) n := by
  by_cases hn : n = 0
  · subst n
    obtain ⟨k,j,hk,hl,hq⟩ := prefixHit 10 B (by decide)
    exact ⟨k,hk,Or.inr ⟨j,hl,by rw [hq]; decide⟩⟩
  · obtain ⟨k,j,hk,hl,hq⟩ := prefixHit n B (by omega)
    exact ⟨k,hk,Or.inr ⟨j,hl,by rw [hq]; exact Nat.mod_eq_of_lt (Nat.lt_pow_succ_log_self (by decide) n)⟩⟩

private noncomputable def seq (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ contains (2^k) n ∧ ∀ i, ∀ _hi : i < n, seq i ≠ k}
termination_by n

private theorem seqGreedy : greedy seq := by
  intro n
  have he : seq n = sInf {k | eligible seq n k} := by rw [seq]; rfl
  let B := ∑ i ∈ Finset.range n, seq i
  obtain ⟨k,hk,hc⟩ := candidates n B
  have hne : {k | eligible seq n k}.Nonempty := by
    refine ⟨k,by omega,hc,?_⟩
    intro i hi
    have hl : seq i ≤ B := Finset.single_le_sum (f := seq) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hi)
    omega
  constructor
  · rw [he]; exact Nat.sInf_mem hne
  · intro j hj; rw [he]; exact Nat.sInf_le hj

private theorem properties (a : ℕ → ℕ) (ha : greedy a) :
    Function.Injective a ∧ Set.range a = {k : ℕ | 0 < k} := by
  constructor
  · intro i j h
    rcases lt_trichotomy i j with hlt | he | hgt
    · exact ((ha j).1.2.2 i hlt h).elim
    · exact he
    · exact ((ha i).1.2.2 j hgt h.symm).elim
  · ext k
    constructor
    · rintro ⟨n,rfl⟩; exact (ha n).1.1
    · intro hk
      by_contra hmiss
      have hself : contains (2^k) (2^k) := Or.inr ⟨0, by rw [pow_zero]; exact Nat.one_le_two_pow, by
        simp only [pow_zero, Nat.div_one]; exact Nat.mod_eq_of_lt (Nat.lt_pow_succ_log_self (by decide) _)⟩
      have hmin := (ha (2^k)).2 k ⟨hk,hself,fun i _ h => hmiss ⟨i,h⟩⟩
      have hlt : a (2^k) < k := lt_of_le_of_ne hmin (fun e => hmiss ⟨_,e⟩)
      rcases (ha (2^k)).1.2.1 with h | ⟨j,_,hc⟩
      · exact (Nat.ne_of_gt (by positivity : 0 < 2^k)) h.2
      · have hl := (Nat.mod_le (2^a (2^k) / 10^j) (10^(Nat.log 10 (2^k)+1))).trans (Nat.div_le_self _ _)
        rw [hc] at hl
        exact (Nat.not_lt_of_ge hl) (Nat.pow_lt_pow_right (by decide) hlt)

end OMA.P_oeis_a371918

theorem OMA.solution : type_of% @OMA.S_oeis_a371918.main :=
  ⟨⟨_, OMA.P_oeis_a371918.seqGreedy⟩, OMA.P_oeis_a371918.properties⟩
