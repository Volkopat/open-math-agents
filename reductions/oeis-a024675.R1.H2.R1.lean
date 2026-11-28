import OMAReductions.R_oeis_a024675_R1

namespace OMA.R_oeis_a024675_R1_H2_R1

open OMA.S_oeis_a024675


/-- At a gap with valuation one, the earlier balance must cover one unit. -/
def H1 : Prop := ∀ p k : ℕ, p.Prime → p ≠ 2 → 0 < k →
  (d k).factorization p = 1 → (∑ i ∈ Finset.Icc 1 (k-1), (d i).factorization p) + 1 ≤ (∑ i ∈ Finset.Icc 1 (k-1), (a i).factorization p)

/-- At higher valuation the earlier balance must cover the full gap valuation. -/
def H2 : Prop := ∀ p k : ℕ, p.Prime → p ≠ 2 → 0 < k →
  2 ≤ (d k).factorization p →
  (∑ i ∈ Finset.Icc 1 (k-1), (d i).factorization p) + (d k).factorization p ≤ (∑ i ∈ Finset.Icc 1 (k-1), (a i).factorization p)

lemma exclusive {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) (hd : p ∣ d k) :
    ¬ p ∣ a k := by
  intro ha
  let x := Nat.nth Nat.Prime k
  let y := Nat.nth Nat.Prime (k+1)
  have hx := Nat.prime_nth_prime k
  have hy := Nat.prime_nth_prime (k+1)
  have hlt : x < y := Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self k)
  have hxbound := Nat.add_two_le_nth_prime k
  have hxo := hx.eq_two_or_odd.resolve_left (by omega)
  change x % 2 = 1 at hxo
  have hyo := hy.eq_two_or_odd.resolve_left (by change y ≠ 2; omega)
  change y % 2 = 1 at hyo
  have hsub : a k - d k = x := by change (x+y)/2 - (y-x)/2 = x; omega
  have hadd : a k + d k = y := by change (x+y)/2 + (y-x)/2 = y; omega
  have hpx := Nat.dvd_sub ha hd
  have hpy := dvd_add ha hd
  rw [hsub] at hpx
  rw [hadd] at hpy
  have ex : p = x := (Nat.prime_dvd_prime_iff_eq hp hx).mp hpx
  have ey : p = y := (Nat.prime_dvd_prime_iff_eq hp hy).mp hpy
  omega

theorem main : H1 → H2 → OMA.R_oeis_a024675_R1.H2 := by
  intro one many p hp odd n hn
  clear hn
  change (∑ i ∈ Finset.Icc 1 n, (d i).factorization p) ≤ (∑ i ∈ Finset.Icc 1 n, (a i).factorization p)
  induction n with
  | zero => simp
  | succ n ih =>
    have hg : (∑ i ∈ Finset.Icc 1 (n+1), (d i).factorization p) = (∑ i ∈ Finset.Icc 1 n, (d i).factorization p) + (d (n+1)).factorization p := by
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n+1)]
    have hc : (∑ i ∈ Finset.Icc 1 (n+1), (a i).factorization p) = (∑ i ∈ Finset.Icc 1 n, (a i).factorization p) + (a (n+1)).factorization p := by
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n+1)]
    rw [hg,hc]
    by_cases hz : (d (n+1)).factorization p = 0
    · omega
    have hd : p ∣ d (n+1) := by
      by_contra h
      exact hz (Nat.factorization_eq_zero_of_not_dvd h)
    rw [Nat.factorization_eq_zero_of_not_dvd (exclusive hp (by omega) hd), Nat.add_zero]
    by_cases h : (d (n+1)).factorization p = 1
    · rw [h]
      simpa using one p (n+1) hp odd (by omega) h
    · simpa using many p (n+1) hp odd (by omega) (by omega)

end OMA.R_oeis_a024675_R1_H2_R1
