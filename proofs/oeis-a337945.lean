import OMAStatements.S_oeis_a337945
import Mathlib

namespace OMA.A337945

open OMA.S_oeis_a337945

private theorem divisibility (m s t : ℕ) (h : s+t=m) :
    m ∣ s^2+t^2 ↔ m ∣ 2*s*s := by
  have h1 : m ∣ (s^2+t^2) + 2*s*t := by
    refine ⟨m, ?_⟩
    rw [← h]
    ring
  have h2 : m ∣ (2*s*t) + 2*s*s := by
    refine ⟨2*s, ?_⟩
    rw [← h]
    ring
  constructor
  · intro hd
    have ht := (Nat.dvd_add_iff_right hd).mpr h1
    exact (Nat.dvd_add_iff_right ht).mpr h2
  · intro hd
    have ht := (Nat.dvd_add_iff_left hd).mpr h2
    exact (Nat.dvd_add_iff_left ht).mpr h1

/-- A split is admissible precisely when its smaller part satisfies the divisibility condition. -/
private theorem term_iff (m : ℕ) :
    IsTerm m ↔ ∃ s : ℕ, 0 < s ∧ 2*s ≤ m ∧ m ∣ 2*s*s := by
  constructor
  · rintro ⟨s,t,k,hk,h,hs,hst,_,_⟩
    refine ⟨s, by omega, by omega, (divisibility m s t h).mp ?_⟩
    exact ⟨k, by rw [hk, mul_comm]⟩
  · rintro ⟨s,hs,hsm,hd⟩
    let t := m-s
    have ht : 0 < t := by dsimp [t]; omega
    have hst : s ≤ t := by dsimp [t]; omega
    have h : s+t=m := by dsimp [t]; omega
    obtain ⟨k,hk⟩ := (divisibility m s t h).mpr hd
    have mpos : 0 < m := by omega
    have kpos : 0 < k := by
      by_contra! h0
      have : k = 0 := by omega
      rw [this, mul_zero] at hk
      have sqpos : 0 < s^2 := pow_pos hs 2
      omega
    have smaller : s^2+t^2 < m*m := by
      have product : 0 < s*t := Nat.mul_pos hs ht
      rw [← h]
      nlinarith only [product]
    have klt : k < m := Nat.lt_of_mul_lt_mul_left (hk ▸ smaller)
    exact ⟨s,t,k,by simpa only [Nat.mul_comm] using hk,h,by omega,hst,by omega,by omega⟩

private theorem odd_no_two (m : ℕ) (h : Odd m) : ¬ 2 ∣ m :=
  fun hm => (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr hm)

private theorem term_classification (m : ℕ) (hm : 1 ≤ m) :
    IsTerm m ↔ ¬ (Odd m ∧ Squarefree m) := by
  rw [term_iff]
  constructor
  · rintro ⟨s,hs,hsm,hd⟩ ⟨ho,hq⟩
    have cop := (Nat.prime_two.coprime_iff_not_dvd.mpr (odd_no_two m ho)).symm
    have sq : m ∣ s^2 := cop.dvd_of_dvd_mul_left (by simpa [pow_two, mul_assoc] using hd)
    have ds : m ∣ s := (hq.dvd_pow_iff_dvd (by decide)).mp sq
    have lower := Nat.le_of_dvd hs ds
    omega
  · intro h
    by_cases ho : Odd m
    · have hq : ¬ Squarefree m := fun sq => h ⟨ho,sq⟩
      rw [Nat.squarefree_iff_prime_squarefree] at hq
      push Not at hq
      obtain ⟨p,hp,q,rfl⟩ := hq
      have qpos : 0 < q := by
        by_contra! h0
        have : q = 0 := by omega
        simp [this] at hm
      have lower := Nat.mul_le_mul_right (p*q) hp.two_le
      refine ⟨p*q, Nat.mul_pos hp.pos qpos, by simpa only [mul_assoc] using lower, ⟨2*q, ?_⟩⟩
      ring
    · obtain ⟨q,rfl⟩ := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp ho)
      exact ⟨q, by omega, le_rfl, ⟨q, rfl⟩⟩

private theorem product_zero (m : ℕ) (hm : 1 ≤ m) :
    clausen m 0 = ∏ p ∈ m.primeFactors, p := by
  have same : (Finset.range (m+0+1)).filter (fun p => p.Prime ∧ (p-0) ∣ m) =
      m.primeFactors := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Nat.sub_zero, Nat.add_zero,
      Nat.mem_primeFactors_of_ne_zero (by omega : m ≠ 0)]
    exact ⟨And.right, fun hp => ⟨by have := Nat.le_of_dvd (by omega : 0 < m) hp.2; omega, hp⟩⟩
  unfold clausen
  rw [same]

private theorem product_one_of_odd (m : ℕ) (hm : 1 ≤ m) (ho : Odd m) : clausen m 1 = 2 := by
  have same : (Finset.range (m+1+1)).filter (fun p => p.Prime ∧ (p-1) ∣ m) = {2} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨_,hp,hd⟩
      by_contra neq
      obtain ⟨q,hq⟩ := hp.odd_of_ne_two neq
      exact odd_no_two m ho (dvd_trans (show 2 ∣ p-1 from ⟨q, by omega⟩) hd)
    · rintro rfl
      exact ⟨by omega, Nat.prime_two, by simp⟩
  unfold clausen
  rw [same]
  simp

private theorem product_one_of_even (m : ℕ) (hm : 1 ≤ m) (he : Even m) : 6 ≤ clausen m 1 := by
  let primes := (Finset.range (m+1+1)).filter (fun p => p.Prime ∧ (p-1) ∣ m)
  have subset : ({2,3} : Finset ℕ) ⊆ primes := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · simp only [primes, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, Nat.prime_two, by simp⟩
    · simp only [primes, Finset.mem_filter, Finset.mem_range]
      have lower : 2 ≤ m := by obtain ⟨q,hq⟩ := he; omega
      exact ⟨by omega, Nat.prime_three, he.two_dvd⟩
  have pos : 0 < ∏ p ∈ primes, p := Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.1.pos)
  have hd := Finset.prod_dvd_prod_of_subset {2,3} primes id subset
  have le := Nat.le_of_dvd pos hd
  change _ ≤ ∏ p ∈ primes, p at le
  norm_num at le
  exact le

private theorem prime_product_squarefree (m : ℕ) : Squarefree (∏ p ∈ m.primeFactors, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq ne
    have pp := (Nat.mem_primeFactors.mp hp).1
    have pq := (Nat.mem_primeFactors.mp hq).1
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes pp pq).mpr ne)
  · intro p hp
    exact (Nat.mem_primeFactors.mp hp).1.squarefree

private theorem product_classification (m : ℕ) (hm : 1 ≤ m) :
    (m * clausen m 1 ≠ 2 * clausen m 0) ↔ ¬ (Odd m ∧ Squarefree m) := by
  rw [product_zero m hm]
  by_cases odd : Odd m
  · rw [product_one_of_odd m hm odd]
    constructor
    · rintro hi ⟨_,sq⟩
      apply hi
      rw [Nat.prod_primeFactors_of_squarefree sq, mul_comm]
    · intro hi heq
      have eq : (∏ p ∈ m.primeFactors, p) = m := by omega
      exact hi ⟨odd, eq ▸ prime_product_squarefree m⟩
  · have six := product_one_of_even m hm (Nat.not_odd_iff_even.mp odd)
    have upper := Nat.le_of_dvd (by omega : 0 < m) (Nat.prod_primeFactors_dvd m)
    have lower := Nat.mul_le_mul_left m six
    constructor
    · exact fun _ h => odd h.1
    · intro _ heq
      rw [heq] at lower
      omega

end OMA.A337945

theorem OMA.solution : type_of% @OMA.S_oeis_a337945.main := by
  refine ⟨?_, OMA.A337945.term_classification⟩
  intro m h
  exact (OMA.A337945.term_classification m h).trans (OMA.A337945.product_classification m h).symm