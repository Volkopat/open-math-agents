import OMAStatements.S_oeis_a275673

-- Credit: @Aryan-Poonacha
-- Kagey's Haskell enumerator adds each positive increment six times.
-- The quadratic description of the spokes below proves that enumeration.
namespace SpiralSpokes
open OMA.S_oeis_a275673

private def spoke : ℕ → ℕ
  | 0 => 1
  | t+1 => (3*(t/6) + t%6 + 1)*(t/6+1)+1

private lemma step (t : ℕ) : spoke (t+1) = spoke t + t/6+1 := by
  cases t with
  | zero => decide
  | succ j =>
    simp only [spoke]
    by_cases h : j%6 = 5
    · rw [show (j+1)/6=j/6+1 by omega, show (j+1)%6=0 by omega,h]
      ring
    · rw [show (j+1)/6=j/6 by omega, show (j+1)%6=j%6+1 by omega]
      ring

private lemma spoke_mem (t : ℕ) : spoke t ∈ S := by
  cases t with
  | zero => exact ⟨0,0,by decide,by decide,by decide⟩
  | succ j =>
    refine ⟨j/6+1, ((j%6 : ℕ) : ℤ)-2, by omega, by omega, ?_⟩
    simp only [spoke, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring

private lemma spoke_onto (v : ℕ) (hv : v ∈ S) : v ∈ Set.range spoke := by
  obtain ⟨k,b,lo,hi,h⟩ := hv
  cases k with
  | zero => exact ⟨0,by simp only [spoke]; norm_num at h; omega⟩
  | succ q =>
    let r := (b+2).toNat
    have hr : (r : ℤ) = b+2 := Int.toNat_of_nonneg (by omega)
    have bound : r < 6 := by omega
    refine ⟨(6*q+r)+1,?_⟩
    rw [spoke,show (6*q+r)/6=q by omega, show (6*q+r)%6=r by omega]
    apply Int.ofNat_inj.mp
    push_cast at h ⊢
    rw [hr]
    linarith only [h]

private lemma indexed (t : ℕ) : a (t+1) = spoke t := by
  have inc : StrictMono spoke := strictMono_nat_of_lt_succ (fun j => by rw [step]; omega)
  have inf : (Set.ofPred S).Infinite := by
    change S.Infinite
    exact (Set.infinite_range_of_injective inc.injective).mono (Set.range_subset_iff.mpr spoke_mem)
  have hi (i : ℕ) : ∀ h : (Set.ofPred S).Finite, i < h.toFinset.card :=
    fun h => (inf h).elim
  have eq := Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (p := S) spoke
    (fun v hv => by obtain ⟨j,hj⟩ := spoke_onto v hv; exact ⟨j,hi j,hj⟩)
    (fun j _ => spoke_mem j) (inc.strictMonoOn _) (hi t)
  simpa only [a,Nat.add_sub_cancel] using eq.symm

private lemma closed (n : ℕ) (hn : 1 ≤ n) :
    a n = (n+4-3*((n+4)/6)-2)*((n+4)/6)+1 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  rw [indexed]
  cases j with
  | zero => decide
  | succ t =>
    rw [spoke,show (t+1+1+4)/6=t/6+1 by omega,
      show t+1+1+4-3*(t/6+1)-2=3*(t/6)+t%6+1 by omega]

private lemma recurrence (n : ℕ) (hn : 8<n) :
    (a n : ℤ) = 2*a (n-1)-a (n-2)+a (n-6)-2*a (n-7)+a (n-8) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (show 9 ≤ n by omega)
  have ar (k : ℕ) (hk : k≤8) : a (9+j-k) = spoke (j+(8-k)) := by
    rw [show 9+j-k=(j+(8-k))+1 by omega,indexed]
  rw [show 9+j=(j+8)+1 by omega,indexed]
  simp only [show j+8+1=9+j by omega,ar 1 (by decide),ar 2 (by decide),ar 6 (by decide),
    ar 7 (by decide),ar 8 (by decide)]
  norm_num only [Nat.reduceSub,Nat.add_zero]
  have s1 : spoke (j+8) = spoke (j+7) + (j+7)/6 + 1 := step (j+7)
  have s2 : spoke (j+7) = spoke (j+6) + (j+6)/6 + 1 := step (j+6)
  have s3 : spoke (j+2) = spoke (j+1) + (j+1)/6 + 1 := step (j+1)
  have s4 := step j
  omega

open PowerSeries
private noncomputable def series : PowerSeries ℤ := mk fun n => if n=0 then 0 else (a n : ℤ)

private lemma shifted (n k : ℕ) : coeff n (series * X^k) =
    if k ≤ n then (if n-k=0 then 0 else (a (n-k) : ℤ)) else 0 := by
  simp only [coeff_mul_X_pow',series,coeff_mk]

private lemma generating :
    series * ((1-X)^3*(1+X)*(1-X+X^2)*(1+X+X^2)) = X*(1-X^6+X^7) := by
  have lhs : series * ((1-X)^3*(1+X)*(1-X+X^2)*(1+X+X^2)) =
      series - C 2*(series*X^1) + series*X^2 - series*X^6 +
      C 2*(series*X^7) - series*X^8 := by simp only [map_ofNat]; ring
  have rhs : X*(1-X^6+X^7 : PowerSeries ℤ) = X^1-X^7+X^8 := by ring
  rw [lhs,rhs]
  apply PowerSeries.ext
  intro n
  simp only [map_add,map_sub,coeff_C_mul,shifted,coeff_X_pow]
  simp only [series,coeff_mk]
  by_cases h : n≤8
  · interval_cases n <;> norm_num [closed]
  · have rel := recurrence n (by omega)
    simp only [if_pos (show 1≤n by omega),if_pos (show 2≤n by omega),if_pos (show 6≤n by omega),
      if_pos (show 7≤n by omega),if_pos (show 8≤n by omega),
      if_neg (show n≠0 by omega),if_neg (show n-1≠0 by omega),if_neg (show n-2≠0 by omega),
      if_neg (show n-6≠0 by omega),if_neg (show n-7≠0 by omega),if_neg (show n-8≠0 by omega),
      if_neg (show n≠1 by omega),if_neg (show n≠7 by omega),if_neg (show n≠8 by omega)]
    linarith
end SpiralSpokes

theorem OMA.solution : type_of% @OMA.S_oeis_a275673.main := by
  exact ⟨SpiralSpokes.recurrence,SpiralSpokes.generating,SpiralSpokes.closed⟩
