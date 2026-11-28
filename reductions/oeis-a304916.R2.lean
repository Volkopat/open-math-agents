import OMAStatements.S_oeis_a304916

/-!
# Prime exponents in the central binomial coefficient

We certify the fourteen terms through 10^60, show all terms have natural
density zero, and give an infinite geometric progression of excluded
indices from every nonterm. For the remaining binary digit weights, two
inputs suffice: a finite large-prime-square computation, and the first two
frequencies of the explicit reciprocal exponential sum bound.

Reference: A. Granville and O. Ramaré, “Explicit bounds on exponential sums
and the scarcity of squarefree binomial coefficients”, Mathematika 43
(1996), 73–107, doi:10.1112/S0025579300011608. Theorem 1* states the
large-prime-square result. Proposition 2.4 supplies three-prime intervals.
The exponential sum estimate is printed after Lemma 7.2 (manuscript p. 28).
The finite certificates and estimates proved below use only Mathlib.
-/

namespace Bin304
open OMA.S_oeis_a304916

theorem term_iff_valuations {k : ℕ} : IsTerm k ↔
    ∀ p : ℕ, p.Prime → ∃ j : ℕ, (Nat.centralBinom k).factorization p + 1 = 2^j := by
  have nz : k.centralBinom ≠ 0 := (Nat.centralBinom_pos k).ne'
  constructor
  · rintro ⟨j,hj⟩ p hp
    by_cases hm : p ∈ k.centralBinom.primeFactors
    · have hd : k.centralBinom.factorization p+1 ∣ 2^j := by
        rw [← hj,Nat.card_divisors nz]
        exact Finset.dvd_prod_of_mem _ hm
      obtain ⟨e,_,he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
      exact ⟨e,he⟩
    · exact ⟨0, by simp [Nat.factorization_eq_zero_of_not_dvd
        (fun h => hm (Nat.mem_primeFactors.mpr ⟨hp,h,nz⟩))]⟩
  · intro hv
    classical
    have hA : ∀ p ∈ k.centralBinom.primeFactors, ∃ j : ℕ, k.centralBinom.factorization p+1=2^j :=
      fun p h => hv p (Nat.prime_of_mem_primeFactors h)
    let e (p : ℕ) := if h : p ∈ k.centralBinom.primeFactors then (hA p h).choose else 0
    refine ⟨∑ p ∈ k.centralBinom.primeFactors, e p,?_⟩
    rw [Nat.card_divisors nz, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro p hp
    simpa only [e,dif_pos hp] using (hA p hp).choose_spec

/-- A sufficiently large prime square divisor has exact exponent two. -/
theorem exact_two_of_square {k p : ℕ} (hk : 0<k) (hp : p.Prime)
    (hd : p^2 ∣ k.centralBinom) (hbig : 2*k < p^3) :
    k.centralBinom.factorization p = 2 := by
  have lo := (hp.pow_dvd_iff_le_factorization (Nat.centralBinom_pos k).ne').mp hd
  have powle : p ^ (k.centralBinom.factorization p) ≤ 2*k :=
    Nat.pow_factorization_choose_le (by omega)
  by_contra h
  have hu : 3 ≤ k.centralBinom.factorization p := by omega
  have := (Nat.pow_le_pow_right hp.pos hu).trans powle
  omega

theorem not_term_of_square {k p : ℕ} (hk : 0<k) (hp : p.Prime)
    (hd : p^2 ∣ k.centralBinom) (hbig : 2*k < p^3) : ¬ IsTerm k := by
  intro ht
  obtain ⟨j,hj⟩ := term_iff_valuations.mp ht p hp
  rw [exact_two_of_square hk hp hd hbig] at hj
  have hd3 : 3 ∣ 2^j := hj ▸ dvd_refl 3
  exact (by decide : ¬3∣2) ((by decide : Nat.Prime 3).dvd_of_dvd_pow hd3)

/-- The published large-prime bound implies the desired exponent bound. -/
theorem of_granville_ramare {k : ℕ} (hk : 2082 ≤ k)
    (h : ∃ p : ℕ, p.Prime ∧ k ≤ 5*p^2 ∧ p^2 ∣ k.centralBinom) : ¬IsTerm k := by
  obtain ⟨p,hp,hv,hd⟩ := h
  have hp10 : 10 < p := by
    by_contra! h
    have hh := Nat.pow_le_pow_left h 2
    omega
  apply not_term_of_square (by omega) hp hd
  calc
    2*k ≤ 10*p^2 := by omega
    _ < p^3 := by rw [pow_succ, mul_comm 10]; exact Nat.mul_lt_mul_of_pos_left hp10 (by positivity)

end Bin304

/-! The three-prime covering intervals of Granville and Ramaré, Proposition 2.4. -/
namespace Bin304

theorem interval_carry {n p a : ℕ} (hp : 0 < p)
    (hlo : 2*(a*p)+p ≤ 2*n) (hhi : n < (a+1)*p) : p ≤ n%p + n%p := by
  have hlow : a*p ≤ n := by omega
  have eq : n/p=a := Nat.div_eq_of_lt_le hlow hhi
  have hm := Nat.mod_add_div n p
  rw [eq, Nat.mul_comm p a] at hm
  omega

theorem triplet_exact {n p a b : ℕ} (hp : p.Prime) (h3 : 2*n < p^3)
    (hl : 2*(a*p)+p ≤ 2*n) (hu : n < (a+1)*p)
    (hl2 : 2*(b*p^2)+p^2 ≤ 2*n) (hu2 : n < (b+1)*p^2) :
    (Nat.centralBinom n).factorization p = 2 := by
  change ((2*n).choose n).factorization p = 2
  rw [two_mul, Nat.factorization_choose' hp (b:=3) ((Nat.log_lt_iff_lt_pow hp.one_lt (by have := hp.pos; omega)).mpr (by omega))]
  have h1 := interval_carry hp.pos hl hu
  have h2 := interval_carry (pow_pos hp.pos 2) hl2 hu2
  rw [show Finset.Ico 1 3 = {1,2} by decide]
  rw [Finset.filter_eq_self.mpr ?_]
  · decide
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl|rfl
    · simpa using h1
    · exact h2

set_option maxHeartbeats 400000 in
theorem triplet_cover {m n : ℕ} (hm : 2 ≤ m) (hp : (6*m+1).Prime)
    (hq : (12*m-1).Prime) (hr : (12*m+1).Prime)
    (lo : 96*m^2-2*m ≤ n) (hi : n ≤ 108*m^2+3*m-2) :
    ∃ p : ℕ, p.Prime ∧ (Nat.centralBinom n).factorization p=2 := by
  have hm5 : 5 ≤ m := by
    by_contra! h
    rcases (show m=2 ∨ m=3 ∨ m=4 by omega) with rfl|rfl|rfl
    · exact (by decide : ¬ Nat.Prime 25) hr
    · exact (by decide : ¬ Nat.Prime 35) hq
    · exact (by decide : ¬ Nat.Prime 25) hp
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hm5
  let p := 6*t+31
  let q := 12*t+59
  let r := 12*t+61
  have hpp : p.Prime := by
    convert hp using 1
    dsimp [p]
    omega
  have hqq : q.Prime := by
    convert hq using 1
    dsimp [q]
    omega
  have hrr : r.Prime := by
    convert hr using 1
    dsimp [r]
    omega
  let A := 8*t+40
  let base := A*q+(6*t+30)
  have b0 : base ≤ n := by
    have hv := Nat.sub_le_iff_le_add.mp lo
    dsimp [base,A,q]
    linarith only [hv]
  have b1 : n < ((A+(5+t))+1)*q := by
    have hv := Nat.sub_add_cancel (by omega : 2 ≤ 108*(5+t)^2+3*(5+t))
    dsimp [A,q]
    linarith only [hi,hv]
  let j := (n-base)/q
  have hjlo : j*q + base ≤ n := by
    exact (Nat.add_le_add_right (Nat.div_mul_le_self (n-base) q) base).trans_eq (Nat.sub_add_cancel b0)
  have hjhi : n < (j+1)*q+base := by
    have h := Nat.lt_mul_div_succ (n-base) hqq.pos
    rw [mul_comm q] at h
    exact (Nat.sub_add_cancel b0).symm.trans_lt (Nat.add_lt_add_right h base)
  let u := A+j
  let w := 8*t+39+j
  let z := 16*t+78+2*j
  have jmax : j ≤ 5+t := by
    apply Nat.le_of_lt_succ
    apply Nat.lt_of_mul_lt_mul_right (a:=q)
    dsimp [base] at hjlo
    linarith only [hjlo,b1]
  have p3 : 2*n < p^3 := by
    dsimp [p]
    have htop : n ≤ 108*(5+t)^2+3*(5+t) := hi.trans (Nat.sub_le ..)
    linarith only [htop,Nat.zero_le (t^2),Nat.zero_le (t^3),Nat.zero_le t]
  have pq : p ≤ q := by dsimp [p,q]; omega
  have pr : p ≤ r := by dsimp [p,r]; omega
  have q2 : q^2 ≤ 2*n := by
    dsimp [base,A,q] at b0 ⊢
    linarith only [b0,Nat.zero_le (t^2),Nat.zero_le t]
  have r2 : r^2 ≤ 2*n := by
    dsimp [base,A,q,r] at b0 ⊢
    linarith only [b0,Nat.zero_le (t^2),Nat.zero_le t]
  have qupper : n < q^2 := by
    dsimp [A,q] at b1 ⊢
    linarith only [b1,Nat.zero_le (t^2),Nat.zero_le t]
  have rupper : n < r^2 := qupper.trans_le (Nat.pow_le_pow_left (by dsimp [q,r]; omega) 2)
  by_cases hQ : n < (u+1)*q
  · refine ⟨q,hqq,triplet_exact (a:=u) (b:=0) hqq (p3.trans_le (Nat.pow_le_pow_left pq _)) ?_ hQ
       (by simpa using q2) (by simpa using qupper)⟩
    dsimp [u,base,A,q] at hjlo ⊢
    linarith only [hjlo]
  have jlt : j < 5+t := by
    by_contra! h
    have eq : j=5+t := le_antisymm jmax h
    exact hQ (by simpa [u,eq] using b1)
  have wlo : w*r+(6*t+31) ≤ n := by
    have j1 : j+1 ≤ 5+t := jlt
    dsimp [u,A,q,w,r] at hQ ⊢
    linarith only [not_lt.mp hQ,j1]
  by_cases hR : n < (w+1)*r
  · refine ⟨r,hrr,triplet_exact (a:=w) (b:=0) hrr (p3.trans_le (Nat.pow_le_pow_left pr _)) ?_ hR
       (by simpa using r2) (by simpa using rupper)⟩
    dsimp [r] at wlo ⊢
    linarith only [wlo]
  have zlo : z*p+(3*t+16) ≤ n := by
    dsimp [z,p,w,r] at hR ⊢
    linarith only [not_lt.mp hR,jlt]
  have zhi : n < (z+1)*p := by
    dsimp [z,p,base,A,q] at hjhi ⊢
    linarith only [hjhi,Nat.zero_le j]
  refine ⟨p,hpp,triplet_exact (a:=z) (b:=2) hpp p3 ?_ zhi ?_ ?_⟩
  · dsimp [p] at zlo ⊢
    linarith only [zlo]
  · dsimp [z,p] at zlo ⊢
    linarith only [zlo,Nat.zero_le (t^2),Nat.zero_le t,Nat.zero_le j,Nat.zero_le (j*t)]
  · have htop : n ≤ 108*(5+t)^2+3*(5+t) := hi.trans (Nat.sub_le ..)
    dsimp [p]
    linarith only [htop,Nat.zero_le t]

end Bin304

namespace Bin304

/-- Kummer's formula for doubling k, with the powers of the prime evaluated
once and shared by the finite check. -/
theorem carry_count (k p d : ℕ) (hp : p.Prime) (bound : 2*k < p^(1+d)) :
    (Nat.centralBinom k).factorization p =
      ((List.range' 1 d).map (p^·)).countP (fun q => decide (q ≤ k%q+k%q)) := by
  have hlog : Nat.log p (k+k) < 1+d := by
    by_cases z : k=0
    · simp [z]
    · exact (Nat.log_lt_iff_lt_pow hp.one_lt (by omega)).mpr (by simpa [two_mul] using bound)
  rw [Nat.centralBinom, two_mul, Nat.factorization_choose' hp hlog]
  rw [← List.toFinset_range'_1, List.Nodup.card_eq_countP, List.countP_map]
  · rfl
  · exact List.nodup_range' 1

private theorem exclude_rows (rows : List (ℕ × ℕ)) (start size : ℕ)
    (valid : rows.all (fun pd => decide (pd.1.Prime ∧ 2*(start+size-1)<pd.1^(1+pd.2))) = true) :
    let powers := rows.map (fun pd => (List.range' 1 pd.2).map (pd.1^·))
    (List.range' start size).all (fun k => powers.any (fun qs =>
      let v := qs.countP (fun q => decide (q≤k%q+k%q))+1
      v != 2^v.log2)) = true →
    ∀ k : ℕ, start ≤ k → k < start+size →
      (∀ p : ℕ, p.Prime → ∃ j : ℕ, (Nat.centralBinom k).factorization p + 1 = 2^j) → False := by
  intro powers tested k low high all
  obtain ⟨qs,hm,bad⟩ := List.any_eq_true.mp (List.all_eq_true.mp tested k (List.mem_range'_1.mpr ⟨low,high⟩))
  obtain ⟨⟨p,d⟩,member,rfl⟩ := List.mem_map.mp hm
  obtain ⟨hp,hsize⟩ := of_decide_eq_true (List.all_eq_true.mp valid _ member)
  change p.Prime at hp
  change 2*(start+size-1)<p^(1+d) at hsize
  have c := carry_count k p d hp (by omega)
  obtain ⟨j,hj⟩ := all p hp
  rw [c] at hj
  change ((_ : ℕ) != 2^(_ : ℕ).log2) = true at bad
  simp only [hj, Nat.log2_two_pow, bne_self_eq_false, Bool.false_eq_true] at bad

/- Every index from 785 through 2081 has a prime whose carry count plus one
is not a power of two. Eight primes suffice for this range. -/
set_option maxRecDepth 16000 in
set_option maxHeartbeats 2400000 in
theorem finite_exclusion {k : ℕ} (lo : 784<k) (hi : k≤2081)
    (h : ∀ p : ℕ, p.Prime → ∃ j : ℕ, (Nat.centralBinom k).factorization p + 1 = 2^j) : False := by
  let rows : List (ℕ × ℕ) := [(2,12),(3,7),(5,5),(23,2),(7,4),(13,3),(41,2),(11,3)]
  exact exclude_rows rows 785 1297 (by decide +kernel) (by decide +kernel) k lo (by omega) h

end Bin304
namespace Bin304

private theorem check_square_block (rows : List (ℕ × ℕ)) (start size : ℕ)
    (valid : rows.all (fun pd => decide (pd.1.Prime ∧ 2*(start+size-1)<pd.1^(1+pd.2))) = true) :
    let powers := rows.map (fun pd => (List.range' 1 pd.2).map (pd.1^·))
    (List.range' start size).all (fun k => k==786 || powers.any (fun qs =>
      qs.countP (fun q => decide (q≤k%q+k%q)) == 2)) = true →
    ∀ k : ℕ, start ≤ k → k < start+size → k ≠ 786 → ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  intro powers tested k low high ne
  have testedK := List.all_eq_true.mp tested k (List.mem_range'_1.mpr ⟨low,high⟩)
  simp only [show (k==786)=false from beq_eq_false_iff_ne.mpr ne, Bool.false_or] at testedK
  obtain ⟨qs,hm,hit⟩ := List.any_eq_true.mp testedK
  obtain ⟨⟨p,d⟩,member,rfl⟩ := List.mem_map.mp hm
  obtain ⟨hp,hsize⟩ := of_decide_eq_true (List.all_eq_true.mp valid _ member)
  change p.Prime at hp
  change 2*(start+size-1)<p^(1+d) at hsize
  exact ⟨p,hp,(carry_count k p d hp (by omega)).trans (beq_iff_eq.mp hit)⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
private theorem square_block_0 (k : ℕ) (lo : 785≤k) (hi : k<1809) (ne : k≠786) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  check_square_block [(19,3),(17,3),(13,4),(11,4),(23,3),(29,3),(31,3),(41,2),(43,2),(61,2),(83,2),(97,2),(7,5),(67,2),(47,2),(73,2),(37,2),(137,2),(139,2),(3,9),(5,6),(71,2),(53,2)] 785 1024 (by decide +kernel) (by decide +kernel) k lo hi ne

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
private theorem square_block_1 (k : ℕ) (lo : 1809≤k) (hi : k<2833) (ne : k≠786) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  check_square_block [(19,3),(17,3),(13,4),(11,4),(23,3),(29,3),(31,3),(41,2),(43,2),(61,2),(83,2),(97,2),(7,5),(67,2),(47,2),(73,2),(37,2),(137,2),(139,2),(3,9),(5,6),(71,2),(53,2)] 1809 1024 (by decide +kernel) (by decide +kernel) k lo hi ne

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
private theorem square_block_2 (k : ℕ) (lo : 2833≤k) (hi : k<3857) (ne : k≠786) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  check_square_block [(19,3),(17,3),(13,4),(11,4),(23,3),(29,3),(31,3),(41,2),(43,2),(61,2),(83,2),(97,2),(7,5),(67,2),(47,2),(73,2),(37,2),(137,2),(139,2),(3,9),(5,6),(71,2),(53,2)] 2833 1024 (by decide +kernel) (by decide +kernel) k lo hi ne

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
private theorem square_block_3 (k : ℕ) (lo : 3857≤k) (hi : k<4881) (ne : k≠786) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  check_square_block [(19,3),(17,3),(13,4),(11,4),(23,3),(29,3),(31,3),(41,2),(43,2),(61,2),(83,2),(97,2),(7,5),(67,2),(47,2),(73,2),(37,2),(137,2),(139,2),(3,9),(5,6),(71,2),(53,2)] 3857 1024 (by decide +kernel) (by decide +kernel) k lo hi ne

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
private theorem square_block_4 (k : ℕ) (lo : 4881≤k) (hi : k<5905) (ne : k≠786) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  check_square_block [(19,3),(17,3),(13,4),(11,4),(23,3),(29,3),(31,3),(41,2),(43,2),(61,2),(83,2),(97,2),(7,5),(67,2),(47,2),(73,2),(37,2),(137,2),(139,2),(3,9),(5,6),(71,2),(53,2)] 4881 1024 (by decide +kernel) (by decide +kernel) k lo hi ne

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
private theorem square_block_5 (k : ℕ) (lo : 5905≤k) (hi : k<6929) (ne : k≠786) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  check_square_block [(19,3),(17,3),(13,4),(11,4),(23,3),(29,3),(31,3),(41,2),(43,2),(61,2),(83,2),(97,2),(7,5),(67,2),(47,2),(73,2),(37,2),(137,2),(139,2),(3,9),(5,6),(71,2),(53,2)] 5905 1024 (by decide +kernel) (by decide +kernel) k lo hi ne

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
private theorem square_block_6 (k : ℕ) (lo : 6929≤k) (hi : k<7953) (ne : k≠786) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  check_square_block [(19,3),(17,3),(13,4),(11,4),(23,3),(29,3),(31,3),(41,2),(43,2),(61,2),(83,2),(97,2),(7,5),(67,2),(47,2),(73,2),(37,2),(137,2),(139,2),(3,9),(5,6),(71,2),(53,2)] 6929 1024 (by decide +kernel) (by decide +kernel) k lo hi ne

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
private theorem square_block_7 (k : ℕ) (lo : 7953≤k) (hi : k<8977) (ne : k≠786) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  check_square_block [(19,3),(17,3),(13,4),(11,4),(23,3),(29,3),(31,3),(41,2),(43,2),(61,2),(83,2),(97,2),(7,5),(67,2),(47,2),(73,2),(37,2),(137,2),(139,2),(3,9),(5,6),(71,2),(53,2)] 7953 1024 (by decide +kernel) (by decide +kernel) k lo hi ne

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
private theorem square_block_8 (k : ℕ) (lo : 8977≤k) (hi : k<10001) (ne : k≠786) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  check_square_block [(19,3),(17,3),(13,4),(11,4),(23,3),(29,3),(31,3),(41,2),(43,2),(61,2),(83,2),(97,2),(7,5),(67,2),(47,2),(73,2),(37,2),(137,2),(139,2),(3,9),(5,6),(71,2),(53,2)] 8977 1024 (by decide +kernel) (by decide +kernel) k lo hi ne

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
private theorem square_block_9 (k : ℕ) (lo : 10001≤k) (hi : k<11025) (ne : k≠786) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  check_square_block [(19,3),(17,3),(13,4),(11,4),(23,3),(29,3),(31,3),(41,2),(43,2),(61,2),(83,2),(97,2),(7,5),(67,2),(47,2),(73,2),(37,2),(137,2),(139,2),(3,9),(5,6),(71,2),(53,2)] 10001 1024 (by decide +kernel) (by decide +kernel) k lo hi ne

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
private theorem square_block_10 (k : ℕ) (lo : 11025≤k) (hi : k<12049) (ne : k≠786) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  check_square_block [(19,3),(17,3),(13,4),(11,4),(23,3),(29,3),(31,3),(41,2),(43,2),(61,2),(83,2),(97,2),(7,5),(67,2),(47,2),(73,2),(37,2),(137,2),(139,2),(3,9),(5,6),(71,2),(53,2)] 11025 1024 (by decide +kernel) (by decide +kernel) k lo hi ne

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
private theorem square_block_11 (k : ℕ) (lo : 12049≤k) (hi : k<13073) (ne : k≠786) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  check_square_block [(19,3),(17,3),(13,4),(11,4),(23,3),(29,3),(31,3),(41,2),(43,2),(61,2),(83,2),(97,2),(7,5),(67,2),(47,2),(73,2),(37,2),(137,2),(139,2),(3,9),(5,6),(71,2),(53,2)] 12049 1024 (by decide +kernel) (by decide +kernel) k lo hi ne

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
private theorem square_block_12 (k : ℕ) (lo : 13073≤k) (hi : k<14097) (ne : k≠786) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  check_square_block [(19,3),(17,3),(13,4),(11,4),(23,3),(29,3),(31,3),(41,2),(43,2),(61,2),(83,2),(97,2),(7,5),(67,2),(47,2),(73,2),(37,2),(137,2),(139,2),(3,9),(5,6),(71,2),(53,2)] 13073 1024 (by decide +kernel) (by decide +kernel) k lo hi ne

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
private theorem square_block_13 (k : ℕ) (lo : 14097≤k) (hi : k<15121) (ne : k≠786) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  check_square_block [(19,3),(17,3),(13,4),(11,4),(23,3),(29,3),(31,3),(41,2),(43,2),(61,2),(83,2),(97,2),(7,5),(67,2),(47,2),(73,2),(37,2),(137,2),(139,2),(3,9),(5,6),(71,2),(53,2)] 14097 1024 (by decide +kernel) (by decide +kernel) k lo hi ne

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
private theorem square_block_14 (k : ℕ) (lo : 15121≤k) (hi : k<16145) (ne : k≠786) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  check_square_block [(19,3),(17,3),(13,4),(11,4),(23,3),(29,3),(31,3),(41,2),(43,2),(61,2),(83,2),(97,2),(7,5),(67,2),(47,2),(73,2),(37,2),(137,2),(139,2),(3,9),(5,6),(71,2),(53,2)] 15121 1024 (by decide +kernel) (by decide +kernel) k lo hi ne

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
private theorem square_block_15 (k : ℕ) (lo : 16145≤k) (hi : k<17169) (ne : k≠786) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  check_square_block [(19,3),(17,3),(13,4),(11,4),(23,3),(29,3),(31,3),(41,2),(43,2),(61,2),(83,2),(97,2),(7,5),(67,2),(47,2),(73,2),(37,2),(137,2),(139,2),(3,9),(5,6),(71,2),(53,2)] 16145 1024 (by decide +kernel) (by decide +kernel) k lo hi ne

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
private theorem square_block_16 (k : ℕ) (lo : 17169≤k) (hi : k<18193) (ne : k≠786) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  check_square_block [(19,3),(17,3),(13,4),(11,4),(23,3),(29,3),(31,3),(41,2),(43,2),(61,2),(83,2),(97,2),(7,5),(67,2),(47,2),(73,2),(37,2),(137,2),(139,2),(3,9),(5,6),(71,2),(53,2)] 17169 1024 (by decide +kernel) (by decide +kernel) k lo hi ne

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
private theorem square_block_17 (k : ℕ) (lo : 18193≤k) (hi : k<19217) (ne : k≠786) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  check_square_block [(19,3),(17,3),(13,4),(11,4),(23,3),(29,3),(31,3),(41,2),(43,2),(61,2),(83,2),(97,2),(7,5),(67,2),(47,2),(73,2),(37,2),(137,2),(139,2),(3,9),(5,6),(71,2),(53,2)] 18193 1024 (by decide +kernel) (by decide +kernel) k lo hi ne

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1800000 in
private theorem square_block_18 (k : ℕ) (lo : 19217≤k) (hi : k<20124) (ne : k≠786) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  check_square_block [(19,3),(17,3),(13,4),(11,4),(23,3),(29,3),(31,3),(41,2),(43,2),(61,2),(83,2),(97,2),(7,5),(67,2),(47,2),(73,2),(37,2),(137,2),(139,2),(3,9),(5,6),(71,2),(53,2)] 19217 907 (by decide +kernel) (by decide +kernel) k lo hi ne

theorem small_multiplicity_two (k : ℕ) (lo : 785≤k) (hi : k<20124) (ne : k≠786) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  by_cases stop0 : k<1809
  · exact square_block_0 k (by omega) stop0 ne
  by_cases stop1 : k<2833
  · exact square_block_1 k (by omega) stop1 ne
  by_cases stop2 : k<3857
  · exact square_block_2 k (by omega) stop2 ne
  by_cases stop3 : k<4881
  · exact square_block_3 k (by omega) stop3 ne
  by_cases stop4 : k<5905
  · exact square_block_4 k (by omega) stop4 ne
  by_cases stop5 : k<6929
  · exact square_block_5 k (by omega) stop5 ne
  by_cases stop6 : k<7953
  · exact square_block_6 k (by omega) stop6 ne
  by_cases stop7 : k<8977
  · exact square_block_7 k (by omega) stop7 ne
  by_cases stop8 : k<10001
  · exact square_block_8 k (by omega) stop8 ne
  by_cases stop9 : k<11025
  · exact square_block_9 k (by omega) stop9 ne
  by_cases stop10 : k<12049
  · exact square_block_10 k (by omega) stop10 ne
  by_cases stop11 : k<13073
  · exact square_block_11 k (by omega) stop11 ne
  by_cases stop12 : k<14097
  · exact square_block_12 k (by omega) stop12 ne
  by_cases stop13 : k<15121
  · exact square_block_13 k (by omega) stop13 ne
  by_cases stop14 : k<16145
  · exact square_block_14 k (by omega) stop14 ne
  by_cases stop15 : k<17169
  · exact square_block_15 k (by omega) stop15 ne
  by_cases stop16 : k<18193
  · exact square_block_16 k (by omega) stop16 ne
  by_cases stop17 : k<19217
  · exact square_block_17 k (by omega) stop17 ne
  exact square_block_18 k (by omega) hi ne

theorem multiplicity_four_786 : (Nat.centralBinom 786).factorization 2 = 4 := by
  rw [carry_count 786 2 10 (by decide) (by decide)]
  decide +kernel

end Bin304
namespace Bin304

private theorem factorial_window {p w : ℕ} (hp : 1 < p) (size : p < (w+1)^2)
    (cop : p.gcd w.factorial = 1) : p.Prime := by
  by_contra hn
  have sq := Nat.minFac_sq_le_self (by omega : 0 < p) hn
  have prime := Nat.minFac_prime (by omega : p ≠ 1)
  have small : p.minFac ≤ w := by
    by_contra! contra
    have h := Nat.pow_le_pow_left (by omega : w+1 ≤ p.minFac) 2
    omega
  have h := Nat.dvd_gcd (Nat.minFac_dvd p) (Nat.dvd_factorial prime.pos small)
  rw [cop, Nat.dvd_one] at h
  exact prime.ne_one h

private theorem square_interval {x k p : ℕ} (hp : p.Prime) (lo : x ≤ k)
    (h2 : p^2 ≤ 2*x) (h1 : 2*((x/p)*p)+p ≤ 2*x) (last : k < min ((x/p+1)*p) (p^2)) :
    k.centralBinom.factorization p = 2 := by
  obtain ⟨hu,hu2⟩ := lt_min_iff.mp last
  have d := Nat.div_eq_of_lt_le ((Nat.div_mul_le_self x p).trans lo) hu
  have hm := Nat.mod_add_div k p
  rw [d,mul_comm p (x/p)] at hm
  have c1 : p ≤ k%p+k%p := by omega
  have c2 : p^2 ≤ k%(p^2)+k%(p^2) := by rw [Nat.mod_eq_of_lt hu2]; omega
  have hh : 2*k<p^3 := calc
    2*k < 2*(p^2) := by omega
    _ ≤ p*(p^2) := Nat.mul_le_mul_right _ hp.two_le
    _ = p^3 := by ring
  rw [carry_count k p 2 hp hh, show List.range' 1 2 = [1,2] by rfl]
  simp [c1,c2]

/-- A checked interval chain can use different primes at its successive links. -/
private theorem scan_sound (P : ℕ → Prop) (step : ℕ → ℕ → ℕ)
    (valid : ∀ x w k, x≤k → k<step x w → P k) (c w x k : ℕ) (lo : x≤k)
    (hi : k < Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ a => a)
      (fun _ f u a => f (u/4096) (step a (u%4096))) c w x) : P k := by
  induction c generalizing x w with
  | zero => change k < x at hi; omega
  | succ c ih =>
    by_cases pass : k < step x (w%4096)
    · exact valid _ _ _ lo pass
    · exact ih (w/4096) (step x (w%4096)) (by omega) hi

/-- Labels below 2048 select a prime near the square root of twice the left
endpoint. The other labels select the parameter of a
Granville–Ramaré three-prime interval. Each checked endpoint is exclusive. -/
theorem packed_interval
    (trip : ∀ {m n : ℕ}, (2 ≤ m) → (6*m+1).Prime → (12*m-1).Prime → (12*m+1).Prime →
      (96*m^2-2*m ≤ n) → (n ≤ 108*m^2+3*m-2) → ∃ p : ℕ, p.Prime ∧ n.centralBinom.factorization p=2)
    (c w x y : ℕ) :
    let good (p : ℕ) := if p≤16 then decide p.Prime else if p≤255 then p.gcd (Nat.factorial 16) == 1
        else decide (p<65536) && (p.gcd (Nat.factorial 255) == 1)
    let step (a v : ℕ) :=
      let m := if v<2048 then
        let top := Nat.sqrt (2*a)
        top - ((top+1)%2) - 2*v
      else Nat.sqrt (a/96) + 1 - (v-2048)
      if v<2048 then if good m && decide (m^2≤2*a ∧ 2*((a/m)*m)+m≤2*a) then min ((a/m+1)*m) (m^2) else a
      else if decide (2≤ m ∧ 96*m^2-2*m≤a) && good (6*m+1) && good (12*m-1) && good (12*m+1)
        then 108*m^2+3*m-1 else a
    y ≤ Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ a => a)
      (fun _ f u a => f (u/4096) (step a (u%4096))) c w x →
    ∀ k : ℕ, x≤k → k<y → ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  intro good step finish k lo hi
  have prim (p : ℕ) (h : good p = true) : p.Prime := by
    dsimp only [good] at h
    split at h
    · exact of_decide_eq_true h
    · split at h
      · exact factorial_window (w:=16) (by omega) (by omega) (beq_iff_eq.mp h)
      · obtain ⟨lim,cop⟩ := Bool.and_eq_true_iff.mp h
        exact factorial_window (w:=255) (by omega) (of_decide_eq_true lim) (beq_iff_eq.mp cop)
  apply scan_sound _ step _ c w x k lo (hi.trans_le finish)
  intro a v n low last
  dsimp only [step] at last
  split at last
  · split at last
    · rename_i h
      obtain ⟨p,t⟩ := Bool.and_eq_true_iff.mp h
      obtain ⟨c2,c1⟩ := of_decide_eq_true t
      exact ⟨_,prim _ p,square_interval (prim _ p) low c2 c1 last⟩
    · omega
  · split at last
    · rename_i h
      simp only [Bool.and_eq_true_iff] at h
      obtain ⟨⟨⟨b,p⟩,q⟩,r⟩ := h
      obtain ⟨hm,hl⟩ := of_decide_eq_true b
      exact trip hm (prim _ p) (prim _ q) (prim _ r) (hl.trans low) (by omega)
    · omega

end Bin304
namespace Bin304

section
variable (trip : ∀ {m n : ℕ}, (2 ≤ m) → (6*m+1).Prime → (12*m-1).Prime → (12*m+1).Prime →
  (96*m^2-2*m ≤ n) → (n ≤ 108*m^2+3*m-2) → ∃ p : ℕ, p.Prime ∧ n.centralBinom.factorization p=2)
include trip

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_0 (k : ℕ) (lo : 20124≤k) (hi : k<48475) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x1000800101a01d00c01200000702200c00e02001101800c01100a00501a00b00c00900402401002300e00300800b02000e00200802000c00901c00600901600601200c01200000702800400e00b00600901800d00a00300800202000f00400800200801a01001900000700a00501401d00501b00001300e00400800100700a01801900002701101700601700b00800101f01700401600001801e00000600900302401702300d00200d02201200d02400c02500100601100302002300b01300a01000e00401000901200d00a00f00800000c01100200701600b00800200601e00f00d00100600900b01b00e00401c00a00401902300402100a00c01b02200600900b00801800500800100700a01601500401500000601701400800001400d00200701300300c00100601380001800e00b01400401400a01300c00300c01900201101201800c00100b00800a00700100600f00a00701000501500900601a01e00500800401101400401300300700d00500c00200500c012005011004013001010 20124 48475 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_1 (k : ℕ) (lo : 48475≤k) (hi : k<94275) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x700c00502402901502000401901701c03100400900d01802201b00800c02103600e00701602301102501802401b00a00002302401e02400000801100401902000701c00300900d00602903000800c00503201a00700b00400a00d02701200502302601800c00401000d00801c00201b00c02d00a00c00601100e01501a00501001f01402900400900c00701900302001200802c00500a00d02801600601500401e00101a01500501501200e00a00201401c00601000301000d01a01102102401200700b80100502100001601400501400201602e00300901501202a00003001400201301101301d01501300001302100500f00000801102602001f01302600d02800300f01f00500f02700e02700200e00b02601c00100d00f00300f00000e00b01500900100800b01f00a00c01f01e02d00900001200b01a01d00b00501601c00801c00601600401b01c00600f01400801400502900200701900301201901501900c01800002601b00201a00b01a01600301201001c00a01b00e00002700f 48475 94275 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_2 (k : ℕ) (lo : 94275≤k) (hi : k<160973) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x402704900902500305101502001403002902f02301400200901e01c01e00501d00001d04500703802202001a00601900303d03c00503b00f02002a00202300e02300d01601300001801e04e03f01501700c00201c03e01101400100a01500901503b01800f02601e00703500e00701902f01200d00703901002f02401703901a03800e03802901600a02401f00d01e01800201801e00802b03400b02e01600c01002d02e01102001e00b01500802300502301a01b00d00704300403002f00600c00301780100a01400800d01504200104201800f01e01400801803400a00e01101c00601202500901c01501b00502400303101300703800300a00103a01300502a00e00901802200b00101600d00300a00001603900f00b00000902401400a00100a01f00703f01800901300600b02401102400702300500b00200901b01001b01803002100801e00401d00201d01301804000d00700c00501100003f01e01400b00501a00100901301502d00e02c02302a02000201f02900701a00101000c 94275 160973 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_3 (k : ℕ) (lo : 160973≤k) (hi : k<227916) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x5d01c00600d01e00900f02300e00500d02200b03203702801200d01e01a01700901702602000100b01000900f00701600303001d01a01700702000500d00201f04e01301c00503000001a03800405601000a04001201500102701003e02d00002301702200e00701602500c00f01901600501501100c01100a04402200d00300c02800a02800800e01201500201401700a01c00600c00001f01000800e00501501d00a02001900e00601f00303a01c00801b00300c02100a02001900e00603101c00a01c00802300500c00001301600800e00603d03401901600501403800901b00401401700b01000704002a01301600603505300900e01701400101401c04803700400c00000b00f03c00e00501400201402f02400d00400c00102d05602a00c01704a00e00702e04f01800d04002b03100803f01701402002f00e00800e00602500300a01f01101e00501403e02c02800402801001202200702200202a03802400e00501900101903a00700c00400c00001801e00602d00000a02802000d 160973 227916 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_4 (k : ℕ) (lo : 227916≤k) (hi : k<343191) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x203f02603e02901c00e00103901207001900604105402301a03206a02e01702e00a04801c01802101d02903500e01b01606b01c01f00100c03702701904a02301a05402901301780100505003b00a03a01404900100c03f00901800603e02400b02f00500d00102602800901e02502700302604e03601801300e00204002f00903100603400100c01103002303205601905603700603601f01c04c02f00e00502a02f02505602c01d00100c04602502e00602d04d03801801304700103d03700902200400d00000c01101501800704101900b01001f01600105202702400e00503300002505503702606201b01001b03600602102300b01e01300e00504d01100904600400d00000c01e02f01800700e02e01603b02404e00600d00101502a01b03301301c00401c04100a04000703c00301503001b01800805f01100a02600701600402501902400f00801700502802201401700600d00101b01002303f00000c03000a02c01302500102401000a03701203600000c01101f025007016011 227916 343191 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_5 (k : ℕ) (lo : 343191≤k) (hi : k<440013) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0xd02800801a01d02603f01705f00701a06b00c02200a02700101803b02401a00402001403a06101602100702101502a01203203000502001301f02204903d00003d01301e07500500f00200e01301f02c02d01900100d01c02901102901a02800e01c05802c05e01905e00c02200902603b00e05900b03a04102002800c02700a04000603f01403f02c00a01100802b00402501c06603d02302000502001403b01103b01000402e02201f02202d01102d02601c00e00100e01c02402b00a02b07500e00000e06600a01a04001901c02d03600903c02701802703e01b01601101601a00701900601903702403601e06900400e00200e01303002e00602e00102d01b02d01202c01002c02500102405404200f00001e01103002a02f00e02b03d01100700f06100c04802700f01402902f00b02e02c05f01400c01200904503c00c01200b02a02b03400201703200903100603105202301a02303800703400400e02b00c02a03302500602400202403201d01100a01101c02400001e04000800f 343191 440013 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_6 (k : ℕ) (lo : 440013≤k) (hi : k<549556) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x702300403a03400c03f01703e00201a04e05e01000100e03800a01c06402e01f00e01400c05000703a00102208e00a02e00702e00002d01e02d02a00a02e01702e00300f01e01907800801100605601500d01404602300400f02a04302e00502d00001a01500d04f00a02301602200100c01307100f02a02103303401100703202500d01c00601000002704103c02300702202f00e02f03001c00a03a01e00f01e03902400b03d01f01000300f00003903702603600904e00501a00101a03700c03600a03600603500301a01504a03202603200701000403103302601200801b00000e03203402303301000403c02403e04d02f04d00002001300b01c01602100102103a00c02d00901100001905600b05604000f03600d01301701b00600e02904605300501a04600c02800a01b03200f00303001402f03101703102403000103006101701100602101502002302f03102402100400f00100e01402002304f01100804400203a02803a06000600f03c02003c03201000103704703f00f000 440013 549556 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_7 (k : ℕ) (lo : 549556≤k) (hi : k<673163) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x1901203c00e03b02301402e01d02e02b01705b01f03401e05a04102d00e05a00a01d02802b01700f01601b03f00b01201803007103803e00a02502d01001601b05200b05100801200405301600e04903302b01804800302f01503803e00701100103d03200d03102201e03b01102700f07a00b03504f01100101b01f00d01e00906b00602403200d07901902b02702a00001b03600b03500903500502f01f00d03a00a05500702400102302c07e01e00701c00501c00201b07005402b00801100502a00002201402804a00200f05a02201e01801203201100401002600d02b03a01001604601500b01d03202403600d01401901300901c03a05408b00c05904801200701001f05604402d03400902a00604501402101d00801c01705f01600d05402102a00502900201b02603204300b01d03d04200004b04001801200801100201a02503e03800602e00001b01604d01400b03c01702900403b03500d03402101301701101703300203a01403a038009037006010039036014021024008011 549556 673163 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_8 (k : ℕ) (lo : 673163≤k) (hi : k<1010363) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x3e04401703a03100903000401209a07201500803000303503d04401703904000104001980180002705401200004002f00e01600c01f00903302204e07800b01400701100103204d03f01f00a01f00802600505d01700e02004703d01903c00303c06a00c01400903800503700102c04900a03c00703c04603f02001b01500a04400504403e00f01606a03300801200602600202501703102004206100106a03d06907400005c06903e04001904000201006400d05a02f02c00202c02100e01f00b01f01907900001003d00c01400901e01801c02e00e03800a05e00701200203603301b01500b03200803200104202700a01300603603800e04402202c00501100201002e02b01602301400b01402202c00502506108701300903f02103002d04503200701102e04c01f00a05d00602502100f02000e04702902c00804602e01b02d00d02d06001d00601d00101c03702304300902501802500002404a04505001903100701d02803901503903f00601106c02301404701d00401001605b049 673163 1010363 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_9 (k : ℕ) (lo : 1010363≤k) (hi : k<1323913) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0xe01700c06c0070140050ac04703107c00a01500601400501406002004103e01703d80003002300b01400501302501002400f01800c07503b02100202003a01004d00c02b00a01500602005c04b02400e08b00b02b0070310250a003f01d03e00b03e00703d02502002503c01800f01805903200801400501300401300201f02403003900b01506b02a06b08303e01d02203a01300401300001207703c03906205300704f03401006400c01601b06300001102400e01703b03801b01300307801900e01700b01502502000102008205505a00c01600901407404a02c01d07a00801400601300301204805105d00c06600701300501301a00f02b00d04f02d04105701101800e01700d04f01b04e00104e04300e04200b02a00008b04f00d02200a04e02501300005104703b01702605c00805c04c01e02207804600504502405104703a04605003700603600106704f00c0b602401104704c03708202000101f04b04001806b03c01b03c00003503d00d06a00701f03d05704601b045006045 1010363 1323913 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_10 (k : ℕ) (lo : 1323913≤k) (hi : k<1697416) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x1d01403203501a00e0be0070a904002d01b08601800c02f00502e03208c04600f04504201805101502902307d05207c03b02500701504001205e04d05d02002604c05c03201302801003f06308700803601d01405a02207601005900c07500602409d02c01a06303803a04906505f01900c02501e06408a07704a02004a00a01600805c02902201b05204500b01700806001d01303103402600902400601500201405d01105d07c02f07c01600601500002d02801102702105400d05303a03d04001206400f05801e02400201403901008000d05303905280101803f0b100507b01b02101a03202e01f01601c02200002203700f01806209301c02200102205605701902a04200c03b06801406b03202e01f01700a06600001304301104200e01806103406101403d01001900f02e00b01500601402702005000d01700904f03d05706703802d00b02d00704a04c06502e01e06900901500504501b01202f04405800d05800a05b00605b01b01103c02003c0310170280230070220000450ca 1323913 1697416 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_11 (k : ℕ) (lo : 1697416≤k) (hi : k<2143534) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x6003001d02304300e05f07f03a00108d02b01206c02301a00b06b00401601f02405a03704904b06201e01401d06102900e01a00c0c000001501e02405f01103b05b03100502601f03009301201b00e04202101800701600204105b01305a06101b00e05903601704b01401d01303401005400c01800805301e04d02a01001a00e01a04b03a00903a00503905004d04a01001a00d05900601603d02508401108c00e04200a04102c04102b01302a07806700e04800809e04403808c04c04900c02700903100303001e07101d01106200e03200906100104003402304208704e05506d00104006b02e06a00d01900906900003006b06807f03e03a00701600007b03c07a04805f04100201401d01304f0b805803603100603000303802a01001a80003a06502806403f00a01600008d01b01101b06402602b05500702400002407503507406004500504403a07302807203000c03004101500301504102207700e07701e02400102407801203903509001f01600703e01d04301b03c0300090b1 1697416 2143534 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_12 (k : ℕ) (lo : 2143534≤k) (hi : k<2856020) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x1800001703902702d02507403b04703a0160390150eb01104800c03602202900104602e01208400d03600902900202902103d01f06e04101007800a02a00607709905301e01101d02501c00c02a80580105200f05104e08100701700201604d02504502401c02308400b06e00406d02c01407706c05102201900802700302704d08603501107a08506900706002d01503e05f04500e01a04001904607c03603105207b01a00c06502001700101604604808701008702101802d0320a401301d04106e00d07c00601601f01403501203504004a00b04300403a09001209005d03b02d0270020d003d01004400d03300c04300604203e0c301d03802900e02900c02802d02700402605706303501103406b09d00a01800905500107e04b01204b02304a00e04a06102700702700202608304803502f05000e01a00a03a01f03a02b02306800c01802c0310a902501d05801b06602800902700604202c0140ad04001a02d02700405e01e07203300b02700501601f02505601005502205506004e 2143534 2856020 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_13 (k : ℕ) (lo : 2856020≤k) (hi : k<3142396) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x7f02201705302801f03402e06603800e03807404005f03503a01301e00f01c06f02a03b04803004706403406401008b00c0370060180300620590140bc04d04100903600404803001506901202d03203700b03702206708802801f01201e00f04103104000102905203302d01001c05905c00208608402601d01003800d02b00a01900002902f01508f04d04102504100a0b50520160520270510120510250500a002b00707503a01603a07401e07405d07301a00705c00207905804e02e01202d04d01d00e06703106700305502101605803302d04d01d00e04000b05600701800006102101505102709804c02b00b01a04301807201505109f06c02401a00301702f0280ad0450d500d01b04b04700001702104608604d03800f03702402b00906600001702101304901101d00f04800c0480090b306803e02001303802601d00f01c00d08500601802f03e02005f0b604c03700c0360090190050600420150420a401d03203700c05b00903f00101705d0150e601103703b01a006018004 2856020 3142396 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_14 (k : ℕ) (lo : 3142396≤k) (hi : k<3438355) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x890b90230b807602801f04f07502507000002a04506f02f05601c00b07000106f04503609702701e00f01d06208200805f04604907f08109a00c01b02401a04e01608302808307204200a04200301708f05005a05c01c02506500706405b0640610ae01e09b04b06702b00504102201602106908b01108a06204a07b01604402803a01003900f03900b05100001805401308e0340a300c01b00905804501507503f09900e04a00a04a00704005a06304c05c02d00e05f00b05e00405e03105d07003f01e00f02c00b0a200205003b02904409d02d04601b00809006603603b04705202606a00a03700001805405604b02602d03204100803702303604c0930430330b600b06904d02906501306503306404606402306305a05d08604705202601d0b109306005d02105c04b08302d00d01a00409a03b02804b03401e07e02c00b01a00201705303502003407805504203c01a00807705a03502f01408503d01c06609303101702105610203d03802502c0310400030400dc04e01e01102d0b0 3142396 3438355 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_15 (k : ℕ) (lo : 3438355≤k) (hi : k<4212945) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x200290770a001c00a01c00505d05906303201304701109705a06400302d03403907207a03e01307101006507801b00001904901502102a09301007600d07603402d06001806001505f05405002808000d01d00908d02408d07201404707e03000e03b00a06400506f0330cd08a00f08904a03b02503a05980105a07904a02101503c02804d01104d03404c00c04c02407105602a08a01001d00e08900904b00004b05d04103001403003502e00b04300601900001909607502001108d00a02c02302b03d01603c0a504504801d00e01b00801a00701a00401903d07f04607e07201201e02607100a02c00102b0d307008509206c09201b00703800203802309a04503606d0ad05a00c0c000008b0620a102001206c03403903207508904108903509b01001d08508700007003108602f08609000b01a03d02b04607908406406100f05306306000802b03101703101507602707600c03800603800007904d02904d02706007310f08d08a06c02705a02505900805905c01602104905b02707a 3438355 4212945 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_16 (k : ℕ) (lo : 4212945≤k) (hi : k<5124273) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0xf0910090f007907505d03b04102b07701007100c07600601c00109007e06f02408f04007404a00c0490090490020480b701803506e0a307a02007901e00907000006f08302d02303a0910c203104301c0030900360f380101a02504f04a05d09101006002705f00805f06901702208f03e00f03000a01c00609802409803301405902903d00c03c00a08706904502404506804d06703802001006605403c00603b00001a05302c09101402004206c02701c00106b0d205603f08e02003701d00a04f00101902404d03201403204c03d00e02f00702e02504e0330b402005c05003502e00502e03501905a04e06101504801209007401c03502e05306407301607302904700f05f02603b04a01903410604801304804203000f10b02501a05202c0230150940630a003605700905706e02c06d0ad03e0420bb00d03c00903b00603b05a02b03201408200f04600a01c0030a202405d03f03803d01101f00c02e00701b00301a00002d0240170ca07a0580360b700901b040044023039060014 4212945 5124273 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_17 (k : ℕ) (lo : 5124273≤k) (hi : k<5505687) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0xc301e00701c00102f04307003407007302901e02901d09603d05f02e05f07003402b05504505c00201b0440190fa09208502a08404503100008305f01803601603501402202b04003910f0a308d0350150560130650100650af0310280b50af03c0bd01202101008902903105805202508d06605002000e03200a01d02601905f02d07f06902206807e00b07e00707d05f02e04d01504c12304b02901e00904a0040490260190cb0a308401204002907100201b02602e05601602304604b00f07804407705707705f0170e802c02201202102a01f00b07d00008d0ae0170ad01402208b0b404f03f02801b03606211f06e08800701a04303c02405103401203300f0b400801c00401c08501802401602209902000f08305f0820a10190980150a004602104504a00c01e00801c00401c00204808e01505d01105c04507d00801c03701a0d60c004b0120d206603002701a04d01704c0610b000f06a0570af07f03c02401702401409b02b05c00c05b00905b00102f0cf051065046064013064 5124273 5505687 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_18 (k : ℕ) (lo : 5505687≤k) (hi : k<5900924) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0xd01f00a01e00007a09303e03601302202b04100a06d0280310b702f0680530350110340100200a60550040310a60170a502d0a500d05e06201d00101c07008b04f0150230a707b02907a02807a07001806f0640a507102002a01e0070310b604a05805b03406a04c06901d00601d07701a06802e0230120c700c05e00303e02603e04402e06705205f02a01f02a06600806504505406f01402202b02000d01f00c0400ae03e06006b02301302201105606904b02806c04f01804e01704e06a0b000e01f03905d00001b07601802401502307d05e00d01f00a05d04f03003701707b0480350c412a00101c0cb01805701509606203300e03307c01d00501c0760490750a605701407a00f03300a03100403102807209601809603b04100e10804502f02505204d0120e800c0ab00003e08107e05701402203b04102a04000c04b00604a0020ba02606a0a707d07a00f04b00c01e00804a0000d20b407702307702203a06c0090ba0b809c04d03c04208202004603200311d09a06309a02c021 5505687 5900924 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_19 (k : ℕ) (lo : 5900924≤k) (hi : k<6311784) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x6f09605f0960ce04402e04f06405700905700001b0270300450aa11007304d00104c02804002701806208d02401307002c07000c0330090330010980ad03f02606d04f09702200f01f00901e03a06e0270c30620c202201109400c09d00301c05109c05904a02409108306401f00908209001b08501808403e08405308305c02006304c00008204603002601806201606101307d09f06705101c03907409e01402301004d07904100404004608d0a805404408c0bc0100340790980290ba09901606101104200f04200b05f02901c09a03002505404f0120b700e04d00809204609206a01807002e03602c02100f06f00505509406d09401502204803400c01e00805600208c03804a03708b0a608501f00908108f01b05002f08e04904305203400f08207e03200608707e06504401704408502204807c00b07b00306606203e03701707d02d06f03c06f08f01e00801d08f08002603e05801304202b03300601b03801a03802f08805c02201008700d08700208607d05d07d016035052034 5900924 6311784 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_20 (k : ℕ) (lo : 6311784≤k) (hi : k<6739956) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x4104701a0b503f02504b03701103500e03500a06102901c03a04006401806401508604a02100d08500708505303103903002501402301204400e03400a08b03b01c08108a05b04a03601104400e02002b01f00607e03a05708702f05a03e02301007100b07100101c02801b02803002603009201409103d03500c04200701e06d08f05103003806e02201104f02b0580090580010570920d802602f09103d08b08103300108a02808902604b02302c03400b03400101c02801b03902f0240140230490a906d01f0010a804601904602f02404a04407403400b03400901e0af01b0730e702401402310902002b09500201c05b04005102f05006e04409201f00a01f00401c05b03102701805a01707201306100d06102a06000006003a0b00380180a50130220100a40090a303a0400270170db06603601103501003506401e0070330000b005101a02713105901302201004200c04200804100209903901903802e02300f11800901e00501d0000e007201607102e07103c03400d034009 6311784 6739956 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_21 (k : ℕ) (lo : 6739956≤k) (hi : k<8069221) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x3002411102200c07e00003504b0500290430aa01505e04006702d06600906605705b07104f02603002401211503e04504b01d02a01a0260740ec0a002102d0360040e704a07503b07407004107007303700c07e00101d0600e70800310260160260300d50f702100805104b01e04b80101604602f03701005a00c09300601d03b0420d701902601704609006300d08d00308c0cf04111407005b07002300f02100a04f00004e05303205304008804c0b60100b500c01f00001d03b08608914e05b01302300d04303c03400004203b04204801a0470910b604b05a00f05a00b05900501e00001d07c0320280c00b101506c02d06b07d03500a03400507903b06902701906d06808104b02303d08005e01f00604204807f02807710405f03600e03500d03505d04e00001b0280770510b70980b604302b01f02a04212d03105204b02406f03604903400803409405702705703903f0b003e0b002c02000b06a00201c12a03006c0b60440b605900805800107103a01905101509d01109c02c0e1 6739956 8069221 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_22 (k : ℕ) (lo : 8069221≤k) (hi : k<8551488) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x2b01b10e0650260130d908b03800904600006708a01b03c01802704f02504f08800c0370060b505806603c0330c903103a04102300c03700903709d01d12503305601405f01105f02e03700005203d06506009e08102f08005905e00404502b01c05703305601709b02f03804d07002c08502807606004105402f02302e05300806702c06605706604b0ed0690150690b202305902205807f0040cf02a0ce0b001202407405304d04600201e07306604b01a0720fe02604107000d05304c01f00101f04c05102a01a0e401605f0e502303f04600601f07b01b04a0320270160260310940b105d00301f04c01d04b01b07201708001306800f03702d04600204505709e0e001908e01704901305e00f08d09b04509b07e07201703a0140b90100b80090c103d07d06904202601305e02f0380090360060ae04b05003b0180cb07405e01003800d02100a05d0030f603c03306903106801406805803700c0370090360020920570430280320490630ae02e0460060450000c90560190550320aa 8069221 8551488 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_23 (k : ℕ) (lo : 8551488≤k) (hi : k<9046780) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x7d16908303105601006004f05500905404d0710630ee0a904305601004800c0a802d0360750a70c30320c207706a00d0eb00303703f01d03e03509804302605006a05a06900a0690000a106c01a04b03204a03103a07602202e02100305302a08004b01612e06505504002100905402d01e06301d03e03402904406b0b50600930690050680630a102a0190970a002604f03900f03904e0210020ce06303406b0940a305b02410802202d01e0d808703c0160d701302208508e05801c02a04403c0330cf01307a10105f00701f08b01e08b01b05704405701705605b0ee00c03703f0de06c01b0570180e304102200a08800108707c05207c03307b01703b01405501107a02e07908401e04c05107b07703b01407a01107a02e0a600303607c01a0b705009c01002306d03800a0370a308704c0440a20170270310a100e0a100a0d909101e09106f09003302703104901308f04008e00407009d01a0c004207201007102e04700604600109a04c04402904403c01605504105f00c0e8001067 8551488 9046780 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_24 (k : ℕ) (lo : 9046780≤k) (hi : k<9559102) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0xb0610030600400b503f03502a0530b704402604304a00c02100702100004702c0470a707108503203b00f04906602200804800309806501c03e0820290810570700a50a106007701e0a103506d0680f70430250bd03900803802d01e03f01a03d06802801512107802200502000002009b09d03e01a02910902501203a04103806e01e06e0c708c01708c01302503103a00e03902f0980fb05f0fa01a02901802803302708709e00b06002d01d02b01c05907906c01606c05002400f02300808206401d04d08105801802808009803009800b0a904012e0590520c403304b01404a0a705600d0220080b906e04606d01b09304402701502605003a0ca09100201e06d0b804c05112b05002400d0c70020370a001c02a01b04c08009e06602400e09d00402008604608505e04c01803c01704b03103a01103a00f04800a0a305a08106301b0630440af0a107c0a003900c02100602000207a03f0351090170f804206a00f09d00009c11c10e0920320a901307300c07200709004e07103e08f 9046780 9559102 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_25 (k : ℕ) (lo : 9559102≤k) (hi : k<10086465) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x6702100402102e06b18511c0b405e0b30110b300a04907901f0700b104d0d40770680ad00e03a00708507006106601b02a01a11a04402603205800f05700c05700401e0780470780340590160590e803a00c0220060dd02d0dd03f01a03e03408e01208d05108d0080210050210001070d606a06503402805207600e07502f03900007408801d02b01910807203c01203b05104a00a05600107405b0c008e03406403202606808d05c08c0eb0370be04504c01602705106c03002300b05600505602e06a04e01c0a80db0630320630110620670a607001e0a206a02b0690590450a10a304a0790a000509f0a208b0a211902701503b05005600805604101f0400c005a05302905305901605804403b0880610070610ae0980ad03509b01609a01302500d04905b01f04001d03f03605a05306d05205801205700f09300909200009210e03505901907603103a00f03a00b09200604804e04603e05303d01603c0150a600f0ce0080a50780a40b203506401806305202705106201206c050061 9559102 10086465 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_26 (k : ℕ) (lo : 10086465≤k) (hi : k<10627130) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x1817b06904b00c04b00704a10a01d02c01b02a12302801403c0110590c203a00803a0010a208207502a01702704502600d07f00107f0e304804003602a05407804502600d02300a02214004804006112103303c04406e00a02200706d06801e04f01c02b0ad0900a707808b03b04302209206c09103709101a0a401803e0730260da0a90010490d904802b06002901803e01611903206409f0220000390d905406501502701306e0110250430a200303902e0a106606b04e0160590320dc05d02100102102e0ad0a401b04e0ac08f01308f0430a200a0a202e01d06606b13508b02603105800a05700704902d0ef03f01a02a0a610701410700c02200605702d03604e03502901702805f07705103a00902200101e03f08c02908b0770320250820220060c30fd03603f05404d08307f01102500f03a00a05700002005c05602d01d05b05502b09913907b07f03004a00b04a00504904101f09701b0960190c903302706902604308607a04a00604907908504f08402a08404d01604c01106d 10086465 10627130 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_27 (k : ℕ) (lo : 10627130≤k) (hi : k<14141037) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x3c09d09806206802c0ad02901402801009a0960250ac0690450740ab08f11613d02801003f07b02407004e02f07e0620a60410140410491000330240010c20c50200a408f06108f14201003f03403f0050c205606908c01c08b08f1340ac07600d0f700305d05614408301c08205b0820370a206605100909903210806310702c01909b01304010207600105d08c02002f1130b007c0520120510100510040230ea03c0ea04c0e910f05201205101005105702408302008306802e06808204b02b0180a207b0a100e02600b07f0320a008c07307801b09304a0290140920a407f03202208c10209309706106604106609201008800203d04601e07804c06d0180410710e300d04f00102208309707801b0430b904181580180003d07302400903a00003907205702d09502b04716401204c0be04b06902006805706811305b0350290160270120c600b0c504202004208e07101c08203405a06a02500e02300b13405106207a08608205403d0330c600f04b00b04b00502002e01f0500a803f 10627130 14141037 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_28 (k : ℕ) (lo : 14141037≤k) (hi : k<14782001) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0xa802a0ea0c600d0c500103e0320c40cd0db06f0da04201504204a02804a06d00d0250480a309f1b502d0a10c00110d100b0250c804f09605d04503906e06802a0110c500b0cb07c02104601f09603904205a0410350400590cb0010f909601e0e801b0540680290350a300b0a305803d04607508d01a06e0f80530bb0250020500320d50ba0e50630390b901702a0140410d90770020760d80b706404d02d0a806e06702901306d01006c06606c03306b0320e009608805501c05508709404b09405902700c08a0480890460200460af02d07e04305a0f909f09b10d04f0460200460e402e07e05407d02a01404100e05f00506b03206a08d01f0cc01b05401802a0c704004902607b0240030b705703c07a03b06301a02c0380e607c12a00c02500613808402007a03a0790c80430160b10360280960500030b00470d905501d05505b0b80e80a303505100c0a200006a03106a0ac07e0790a01390720410ff08a00b08907004f03104e06f01f06f08702d06802c0a602901307700a18109d 14141037 14782001 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_29 (k : ℕ) (lo : 14782001≤k) (hi : k<15438904) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0xda08905401111800b0260880240480220720b90c908a04401704301607a03606100c04000705104803e15509b0b504d0430130b40100790050b304803e07202007105e02f01c07003a02d0380290680b400b0b307d09403103c04601c02d0180840150ad0340250010ac07d03d05705e0cf09202c01806f0130530110410900250040240a802003003c02f0890d901410f00f02700d04000102303202005703b0df08902b0370de0100610090d209809c08601d02e01c02e01802a0d002700c06000605103305012401f02f01b08401808401408c05a02600302303202207106a04506a13301702a01502a01314e05902500402407c0210310a202d04d07a01602901305300f07800c0250010c505703c09f01c04401a0440180ed0120e800b0510660770860200460dc08e01b08d0180fc03602700e0cc00503e07c05010601c0d80150d803506000b06000202304702008e03a0a504c0540140b900e0b90020b804703d03107502e01c0550680420110a400a0dc0c805006504e0c701c02d 14782001 15438904 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_30 (k : ℕ) (lo : 15438904≤k) (hi : k<16111050) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0xb0620340610490bc0730bb04605e02d03806308005400d05300a0260060250030520330500470ff02f11502c06a0430120420690270000ff0b106c02f0df04404d02b06902805b0f10b202307e03e0480ce0d103b02e11d0550cd05400b02600203f0cc03d04701f0470ac04501906403806f0360260070e007306d09101f09004f09001a08f03908f03707a05b04100402404903f07302003001d0b704d0b605c09705a07909106004803c02f01d06501902c01705500d1e707310303009c05609c04401604301402900f0a605a0610340600990500720fd06401904401510807f02700702403305103203d0c404f0c406a09701509701105300e02700b0260070250020510480210870de0560de02c03706201006200407804802204807709801b05605c04308905303402503305103101d0c308a04408907a07f0c203402500602507e03e07d02107d04f04612405601806f01304204a1020020a509902009804f0860a305503902b01502a01408410408c00108c07d03c0c301c0c3018 15438904 16111050 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_31 (k : ℕ) (lo : 16111050≤k) (hi : k<21179656) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x110bc00c04500704506102609207503507409104007a0640490190490170cb03b05a0610bb00206807c0a009105504b0720b40140b40500590040440370810e102106d01d03003e05c07106a01102b0390f70000eb0ae18503205406c0190bc0a702c03a0bb0390bb0880d703504109b09507907f05c01805b06302d06207707d06900806807c02609209604c02103309505c19508401302b05002800302704e04307b02103312005d01c05c05302e0e804600f02a00b1071140c903502203404106d05407901c04901705a06202a00a02800702818a02406d02103305412b05302f09d07701309806f02800309708702308604103301f03209508501b0c305202d01205903904500206706e08c03508b04b0c01410170470140470500d700a0d71040240b506603406506c03f05c05206a01602c01204600f04500502705f80f80b8010ad09901a09901604301309800a13f0b203f0e405003006c07d03a08601608601208500f08500b08405a0e105905014001c0650df06301206300e062 16111050 21179656 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_32 (k : ℕ) (lo : 21179656≤k) (hi : k<21967731) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x7f0a400d0a30030270f70420f60560330ca04a01a04a01804901502d0b908400507709e09807c02207c01f0dc12d05d01805c01502d03b0b500e04605008e04e0ed07c0740ae01b0ae03d08501410000a02800110503708d06e0a107b0a009b01904906310500d0bd0390a209302410701f0320740ef06409001508507108f0080da09e04307c0670340a00be17a08501108400e08400808304f0bc0d607512a06605e06504a03e02f0160b50b906a0090280000b40d60aa0920aa07b0800d407304901604801206a0390830380ab0930d105e07406d0d00790d002d01208f00e02a0020580fb0b303401f09103f0cd0720e706307800e07700a02807d0ca08702107b06503003e05c0520a30c808f00a08e0931090dc02109b01d05d06406b10702b0390450030a209d07507b05607b01f07a01d09b0180a30130a30500450030260f505605e04003101b08507f0480890d205005900009706e02206e0400ff07303007206b01502c01004600b0f20af0750db0f105e01e05d1410cc0a70cb 21179656 21967731 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_33 (k : ℕ) (lo : 21967731≤k) (hi : k<22771547) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x370be0e619b0de01b0d00a10cf01402d01004700b0290020be04f0691630410320cc07b01607a05305c00c05a0000fc07e02307d0420b90fa04a1000af0520f000c0ae07f05912e0240350200a705608805413607304800e02900004509507604d0200d001b03005405d01404801104700a0460040dc0380240c107603301b05d01805d01605c0100470011770c90430c904103305606e09704a01702e03c0480120a500b0ef0a80db09e05606e01c0a603d0ae0130ae00e0290500450d80430350760a708109c0180ea03c06b00f02a00a0cd00109a0380990360240360b40c809803201c0c703e02f03c0480120c60001760360240890c40b801f0320c305d12902d00e02a00216b0c909805f02005f0550c70bb02e01413400b0290f80440370440b90570340670330740bf03e0bf07f0a40950290060280c10bd0940230c00980c00bb0bf03e02f0160be07f0be00b0bd0380bd08902308808205f01e0b70bb05d0ba02c01206b00d0290500280380b408802203301d04a01a04a017085 21967731 22771547 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_34 (k : ℕ) (lo : 22771547≤k) (hi : k<23591538) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x6b0bc05904f04206001f09f06609301409301009200a02900202806305a0cc09004e02004d0a307c08e02e03c04800f04800c04700904700404608b06a0a002109f0570d201a09301507b0a105b00702908c02708b13803608f03301e1350cd04a01604901005b03a05b00112e07102307e04104c0400310190c905402e0110d70bc0c80720440f40430b201e04b08208801508703c05c00d05b0080290c409003608404e0f617001a0f90fb07a0100f80c40780370250360f00c204105f0ef04a0170c110c02b00c0c00010bf06207807102207d0dc03203f07b12c02d01108600202705004308901f08901c0880a202e0a102c00e1290040280a006a0710430f31020940750a701a03001702e06504910005b0090910510270500900d20680341180d10660300a207b01407a17402903811807002207d01e04b0550300180c80e106c00e06b00112d0380690611180a801e03201d0c90190a60140a60c302a0d20270d208f06002106001f05f06703206610901802e01402c00f047096059 22771547 23591538 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_35 (k : ℕ) (lo : 23591538≤k) (hi : k<24426534) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x302605010c03410b04c04004c0cf06e0110da00702900202906404503707903602104d09008a0c702e0c704900c0ca0010460f10590f00200f001d0320400310c705e0c707c07405c00905c00202807304607315a04f04303404107d01a03001402c0530ee0520c90970240970c807e04106005505e01604a01304903c07b03a02607211c04e06814e01714e01002b00d0e708d08603804505002308b02208b0570e801b03007509e0120b100b0470640b911f06a08b02208b07706001d0320ad02f01604a11404800d02a0060c90510d81640200bb04003108202e08202d08107a08c06b08c04407104304d01c04b0191b603c0a703b02a00011b0aa0220b309a0b204013b01507b07404800a04700206b0380250370240360210e10680e10a309e0820e001009d00c1350511200aa0230aa02004d01d03203f0300180a80a205c00c02a0020e506206a08b08403408403301d06f05605f01905e08208801202a0070f90390450620f804e0f708905608901808801602e01202c00e06c005 23591538 24426534 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_36 (k : ℕ) (lo : 24426534≤k) (hi : k<39040632) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x17309a00f0300010670828000bc07403a0490e001e0df01b0340180320b305001004f00e04f00a0640000640d902909902709904906a0b51400810330180880140870410f600602c14c0f50e90240ba01f11414712000f81880880d80109f00b09f00006b0ac09d03501f0ab01c03103f05f03e02d00e18205202803802403602204f0690c507703007604a08f08900a0880520280520870630230a201f08b0c104c01605e01302d00e02a00605c0740260ac09203506903301b04c08f02d01202d00e02b00a06d08e0270510450ac0210ab0420ab0680aa05602f01302d0540f600007a0980450980220970200610a50f003f0f003c0ef00902a0050290a302806416004f02106109015001806f01406e00d14b06402503702407214009601d06001909501709501304901005d00b05c0000930390b009705909701f03301e0960ae04b01716101108800b0880020460510ca0c60c90a106909601a15808302e0120e100d06d00606c0980270c60df0aa0d005f01605e01509f03c09e03b09e 24426534 39040632 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_37 (k : ℕ) (lo : 39040632≤k) (hi : k<40120221) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x3b02206d01f1880e206a0e216811a02c0f20bd08108803b0bc06d0480370480360740a80ae0bf00a02f00702f0010dc0b804f0ac0650ab02609e02306d0d00a90180340150a812e02f00015c07107903e0fe0c204b0c10220f911306b0fc07d0130520ce02f0ce08a08202b05b06506f13d03b13c05601d0a90190a80f305200b02f09209911902909e08809d01f09c07503607405401805401605301403207208b00609912008903e08906f07703b04a07f01e1fc0601b900f02f0d702d0d70fd0e80b008f04908e0af07e01b07d06009b01419400b06808316b03f02a0b70270b607708f0491bd06105501906a01606a01406900f03005d04f11814903e1420580f409c04707d01a07d05f07c01407c01007b0720510b806603f0b108107705814806d01e05501c0550a108c0840a700a0500401700d602709d04b1b00fb03604706b01906a01706a05e08b07205100605004108a17d04d05906406e0760390210c001e0350ce05301308b00a02f00402e09f02b08109603b04a0570611dc 39040632 40120221 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_38 (k : ℕ) (lo : 40120221≤k) (hi : k<41216032) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x2308004a0390760d604703501606a01006a00b0de0020680410dd05b0dd1610e503a0b105701d05601b06c0460e80740320730f004202e1560990d808a0ce0e509e0770f206107e01803401417f00c1010ba02c04007a0a00dc03c0640900d10aa0ed03501703401313400102e0fc06705b04d05a09805902303a0220800480550bb0a90110a800b0a800302e0eb0a705c0f70e10f709f0f60e90630e901c0a90460a90ae05200c0300060a704102d04104f0ce0be0820270cd0780cd0210aa06216a01605309419c0a109903f02a0820a503b0230c204905601d0550160de0d90b405d0990ea0290ea0640800881b806109c0190a904408c0a105114f04f0b80b209102405802105701e0560c607e0c506a0c509b00d03000909a04004e05a08903c08813404a08f04807e01b07e01808d01414600e0dd0040500710bd0810780900b003806205604703501903501515d00f06900906800006805d0dc09102816a1b018d04807e07403301403201003100e08c0050670400a608204d08114a 40120221 41216032 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_39 (k : ℕ) (lo : 41216032≤k) (hi : k<42322173) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x4b08101e1040bd0350160fb0110b613310210602a03f10106f04b08101f08004908001b07f01907f0751430440e00db21203e0280f50240810780390c805601a0ab0160aa01408e00c13c0420510e402903e0660b902206e01f03810f0550150330110531740500da0d403d04d0ad04b0d80b20d801d0d709603305f0a900b0a905e02d1da0f013e04a03902003911e08f01908f01503304509c05e1a31050f003c0ef05804906d06103401503301107d04408d00308c04112e0a108a0eb02409112c0d706203609505301005304306900006909402c10507a03e0d303b06410401e12f06112f01111900b03012b0ca0d902903e0d30910d309f0d20380620360190c10fe0a90060a809302b0fd08a0d804b0390a40e004705501503304503100802f0020f90c50b305b0b30c40dc0ab01f0570870aa0db07e07406a0440cb09402d04002a03f04d0d80650810200aa0190e90af0e800c0e807302c03f04e19102503b06403a1831120db0cc0140cb05f0cb0080ca0410bf08308a0d80a60d8 41216032 42322173 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_40 (k : ℕ) (lo : 42322173≤k) (hi : k<43444520) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x6007e00d07e0000d70bc02d04104f0bb06715a13603901c0ac08703300e07e00014b08502c04002809309a1f20f908004805601705507607f06003100c03100405117c0682760ca0d901c0d90760d80130540440d700007d04202c0af0f208304c0820220a001e09f07709001616900e08e0431ab0af02a03f0270ae04d0ed16106e01d0c40190c30760c301105307402f0b002b1070cb03d0240a00ca03901e0800c903601722000e1a204310b08402a11e0a709210a06f01f06e01d0370190b701305405f0301171680d10290da07a0da04b03a0210cf0770c30180c30140d700e0d705f02d0a202b14d04d14c06503b08918401c03708703401515d05f1130000690411120710280d002506f0f905801e13101a03504613700e0310020b505d0b51f80d403b0230590d306d01a12a01507e01207e00602f0d105104102b0d00290da08a18902103901d0560bd08f0b00b600d06a0020510af0b50f60290f50260f50640ac11815701813007513000802f00002f0ff0500fe10a1060e70c4 42322173 43444520 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_41 (k : ℕ) (lo : 43444520≤k) (hi : k<44583672) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x9101603401211e00d03100002f0bd02c0bd1460710c108304b08201f05801b0360bf1cb00d18705f02e05e02a0720270d207a0d114c03904906e01a09106103300c0310080300000c30a40500bc02803e0241080211080780ad11308001103200710605f02b04007c03f0cc07106616d04a0381030ad10206c0100d90020d80860510c804f0940260af0c003a0c003901d05701b0570190800160ac0750c30000c30960c20d206807202619702205901f08106303601403301109e00509d10102c07304f1000670af0cb05902105904a1a00a60560a511d0f003004306904102c0410b50ee0d60ee1440810780810480ec0c909e00a09d0c819007304f0af0b503c06509204b06f0d40d90170550120540100ab00307d2120f30a202507002208207809106316b04506b00c0530010521ca04f14808a03a08a19b0771ee0a503300e05300a0530a412a0400a909402709304d0930790a00640380480900be05501205408712b0031450a302c0bc02a0bb0b503d14a0c50210ed18806d016055 43444520 44583672 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_42 (k : ℕ) (lo : 44583672≤k) (hi : k<51408775) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x9601309500d0320020310b803008b0b00b60a103f04f03d02316f06705a0190e200e18513b18509b02b0890a113a04e0ed01f05b01b03801a0f60140a400d0a40040a30f905410206b1010271010e805c0e80a60190a508d07004706f00803200306e0aa0f404305216f0f30a807e07407e08704c0e21ae18b09c0940f90820780530da11705f06a03d0e81c001b1ab08d08400f08300b0830000820e506d0e514409902709904e05c04d0860ac0370dc05809c06f00a06f07911708a11706009104012e0c20c70d80210d804b0a50650350110340640d60040ea0450300450bd08a05380108404c03b0220830d60db01b0370170e40bf18e0600ec1370501370270dc02207001d10809903601608001308009703100410f04305110a09c03e0250830b50590b41a70180e40a50300030300a508e05e02c0a409c08406705b02305902005901c0d007706d01207f00a0cf0430510dd02a0dd0260af0b503a01e03701b03601709000f03204405305f05213012408407b03d02408307a15c15e 44583672 51408775 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_43 (k : ℕ) (lo : 51408775≤k) (hi : k<52649213) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x6406e19b05306002809a02603e01f03a04c0390151a900f0570000a40d102e0d102b0db02805e0210c206803901a05904903501003300a1320461401950b10410281340500e509008701e08701b0e30150d800b0320050560460550dc02e0dc0fe04105105f02603e04f0da01f0d901c0390f20d809e09600e0d70050d708c0d60f002b0d002703f02603e0e90ee06803a01b0cd0190370650cc08d0570000310790550dc08108a0a21830240740210740d30c101a0370150a50100c00090bf0ab03015802b0410e005f07f0a804f05d01e03901a0b401407000e07000a0b20dc0300fa0e011c06b03f0251760e903a01909604905800f03300b0950b91610c402b0770910990250e41160390ad0d801403501007000a06f00106f06310709b1070771060b60251760c70a615f0c000f03300c03300008208b0be0610bd07611705d02103b0681cb04a07111509500202e0b702b0b71a00ce0690a707c03801903701603607b0a50ab0560020830ab0ca09b12816a07f1690690870ba096017 51408775 52649213 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_44 (k : ℕ) (lo : 52649213≤k) (hi : k<53912704) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x3706609700c15f06415e04402d08c13a0aa0260aa06a03d06a0a911003901a08704a05901305901008500d0330050320de0840de02e0620a40dd0b111e0a211e06905c01e05c01c05b0a00380160e404903400b03300903300605609d02f09d08207802a06002703f17005d04d16c0f416c08e05800c03300603200008408d02f15a10904105105e0240fa0200b61070da0170ee01008500a08400008404608316702c0780be07605005e0221c001e0f909f0f801207100a03207a05609d0820e71410400260f00240f00200ef01d0ef0180ee04903400c0570000e307a0bf0430ec0410eb0f01691030200da01e0da01a0860170d900f0840000ed0c602d0780ec12e05005e04f12d0fd07301b1b001507101210100a0320020320640e20ab19904213105f02705f1a80b60200da0670d90150360120d800c0330070320040b30460b209c05407802a03f0d50c30680a701a03810e09600f03400c0330000c00d209404402e0440930fa0be0400bd0cf19d0da04c0d901a1420130330090a5 52649213 53912704 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_45 (k : ℕ) (lo : 53912704≤k) (hi : k<119018928) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0xd1171a20681560380ab0342e902f04d02d04c0820720e715305d08d01c08b01604101308a01003f1751e30bf03513403113302e04c0280491050a609904401d06e05904001013000206907903909409f0aa0650500320a91210d002d0cf02a17217f06f02006f1d90dd0160dd00f15100003c1d10f90510331df20b0e00b20a70270480240700d50b901a10a01008900210907a03a07809f0511770f002c0f017608e0260df05d11801e1dd0c204101411700a1ea10f06809403610e0340760c60cf02c0cf09b07105f0ce0240cd07f19e01a04201408a00d03e82580f80c81e80980109a03a0aa13100003504b05b04907614602d14502a0661eb1441370a401c0a301a1a206c0cf0040340a909f0810750d402b0c50280b60241d21500b406e06001706001405e0020dc18a09f17402e06705680781b8010240f106913d14f08704a0970100970010311300a513002a04106c07702503e0d621801c07301907304a10b00b03300009506202c17b1830760be09a02003b0bd09901a038017 53912704 119018928 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_46 (k : ℕ) (lo : 119018928≤k) (hi : k<120925921) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x1620351610b504f03004e0632250c608f02708f08004702308e07f13205b0cd0590cc00e03f0060892050680ac0660930b507608404e02f21808204a0280e002204501f0df01b0a407d18e00e03e0070dd0c20690d30370520650500c80750b307302808f02508e05e04605c21601804214206b0010cb07a0870780371410650500da09202f0d00b30730600490270cf15913205c0ba01404000e03e15806905503a05412f07703513512e1000d91001060f00280f012c06f05c06e01704101311800717a0c10690c10380e308613503213412e04d0611690281690210ba07e06e01906d0980b901012400106a12a0380531a60d212e04f0310be12d04b0c607216d16814304401a16707c16700215c16b03916b1650aa0330aa15a07406204c02804802508e05d08d02006f05b04301a14801313000003d1360681c21be05109e04f0d90d002a07208104902308d02108d05b04301913105819500006a0f412f0c01790d217804f17813f0b213e0f704802308d0f60a501c0a4017041012117 119018928 120925921 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_47 (k : ℕ) (lo : 120925921≤k) (hi : k<122838675) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0xb70c10660c00330930c80a902b0730c608e02107001d11a0171550111540971a91431240ab0330ab0630d10b40d110704902514012d11a01811a01103f00c03f0c30890f517c14e03614d15d07609e04d17a0900f808e01f10d1050cd01210c00b06b10410b1590380d30a00770fa2200b40a902a15602608f0800460200440190ba05a15f00b15e0c203b09615d12a08605003110f15c1750c60a709b1740b017305904000103d0961720541710c01710f309e07402c1910c60cf1140460b006e07e08c01408b00d1490e614811103911106605109f09202e04c09d0f11e40bb01e0430180420140a400e03e0f51970d41962f209f0760b407408304b2840460d70fe01306c00a08a09703c1ac0390952290e306507608424402b0f109b0470231b20c406e01a06d07c03f07b1180960fb1100860ab0320aa0da10f0c710e0610e10260e002410d01c08c0d606d01303f00c08a05703c07a10a1921af0e30eb0500310e202e09102a0720f808f08004708007001e2650150ee00c03e1920a2 120925921 122838675 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_48 (k : ℕ) (lo : 122838675≤k) (hi : k<140360219) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x80107a1190950a00ab0850750c804b0c804a25604705e04601e1d40180bb0590ba00c06c00603d1130b92170370780870510300d20630aa0611011520711510a609a04301708c01408c01008b00b08b15b0cc1440b81440870780fc05003104f22c1420280a809c14123706e0d70ce0100cd00513f1af1540e50360e50b609302f0bf02b0be0290be09c0480240bd13a06f13a0f007d0400040b91cf0880e50ed0c10330500320ab02f0aa02e0e30ea09002707209b0bc01d04401a1600f70400f60de0d50fd2230662221fd0e302b0e20290e215110e02108e01d08d01b08d0160df12d0cd0af1a10551a10e50860500322221160d111604a0251751a706f01a06e01704201404001004000e0a30ae06a0ae13d1770320931160d102b0d10600d00250481951b301a0420130cd00e0cd07c0a238108709409f0bf02f0750620be02b0be1150e10d807001e0a50170a50130400020a30e603a0e50880790b60c00330c019f04d19f07302710e02410e01d14a05a0ef00d06b0970a322f039177 122838675 140360219 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_49 (k : ℕ) (lo : 140360219≤k) (hi : k<254204464) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x8401627700104a29b07e1920430641080ce12e1910be0af0be08c07520d0300ca02c0ab1fd05311610c01908300f04b00a0810000f511410a1140440e80411481c81e40d90e511908a0741cd02c0560d623c02421f1020c606b0c50b608106917e1c40dd2590a20b21500e703c0b007808d0761ee0742681c614407013312905102013201904d06a14200113017707f17717d0fe0410e722f1f90770e516c0ca17a0c91d10f806f0f801d08301908306a0a61770a517704511312f0cf36d0b003b1e40d80e403305a10405709b0c90290c810317206d2ad0160df00e0de0031702191090650a306404006103d06007813509e0cb0320ca0310ca16b0ab0ba2970210c606c04e1850a60072141271091840a30640c014714f1c203805c03505b13c0ac0bb0c90290540ed0aa02217f13a17f0131301cf07f19f1500fe15012512d08e12d19d0bd0ca0310ca09b1f70ba0540d40520230850d304f01b04e0120f50000f51140dc16711c16703f16603d16607708c09e80381e80582f80a810831 140360219 254204464 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_50 (k : ℕ) (lo : 254204464≤k) (hi : k<256992448) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x7626a03013507108710405306d22a0160f700710b09410b11507e0920c20b311c11203b05f0390af0360af0bd1460bc05702b12202905520818110313306c1320121320031311151420d107c0630c121024c19116e19103108911908820820d0210e126c04d0b70a700014215a11e15a0a30910dc1590c00b103c15807708c12d05b0301b61bc0ac0290ab0261551e826801904d06a0f61150c40b507e0e91411260f20fd03a0e610605b07513509b0561040530980a931a0831ae2670b50a51ad1b219210817607733709d0ad14d10e0ed05101e05001d0500eb04c1dc0801dc0a309107c0e803f0e70a10e710729212d33109c0fa02d0c906f10d06e0f801c10c0160f70120f60061a71152d206511d15904015812e0b00371aa13e1aa03008913d0e31e808602513301f13209710c00e10b0001ec0660dc19f0400ce03c0cd0390cc0d80e40bc0e30280530b90f80970f70190f700e04b0090f60691990e90a40e907c1f01a50e703c0e610708d03705b0341900300c90ee0870ed0f80d4 254204464 256992448 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_51 (k : ℕ) (lo : 256992448≤k) (hi : k<259797497) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0xff03e1860f20cd1d60af03105813e05513d0530210aa01d1d912a10d00710c06904913b10b13a0451280a312704017812f17717e0cd0350fc0750fc02f0fb0bc0880d617406f0f901804e0150a800d0a700804a26e1f81ba11e1780a106012f17703708c0f108b1b10e402d17512b0f90210f901c0f80170f80120f70690df27604514a0412ca1400b00380b003405a03005827f0c91df13412a1640160830101320001320eb2330e91a70621a608e03a05e2a70e50750e51190e324c12201f04f0d408300f10c0eb0a609425714a1520b315106107a14907808d03719f03305a0bd0591190880290550271450d50840120a71790481790dd0e915212719916807916819823f16e05902f0ca09b2e406f05202205201e0501fe04d0100c50010a614b07e1690420ff03f0fe07a0fe0da0b011b1671d42351050ac0270c806f0c820804f0171ee00504909410b06710a06510a1141ca1b803a3ca07505a09c0ca10405414d15501c0e00140e000c0df14b0c40671b31a00410cf0a11c416f05e 256992448 259797497 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_52 (k : ℕ) (lo : 259797497≤k) (hi : k<262621704) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x1ee0fe03408b0f108a0f005611a1100d60860d610f06d0a91180c700f10d0b70a706807f0b504409203f22603a0b11e20e61b313702c0560291840d624906d04f01504d0112f41890801880c40b518027f0a206114105f1412e803205909d0cb16e0ac0270540241830ba0c821404d00e12100208106910c17a22b2391e323907705c0350fd03005807305712c30802005101d05001a2630b704b0b71200d207e0d11b517903e06107a15a0781771cb0af0bd0cb02d2750281ab09a05302217406d04f01504d06b15500019c0eb0470eb15318704206303f18611d1e80da12503414809c0571981570240860200c816c0f80ec04a0950460930450ea0c206310a1140a11930380b00f105a0f119202c12302712310419001d04f01329b15c0490670c30650c309204115a03e29e1080cd09f05b03208a02d0570bb10f14e05214d1b60121b60011b50d20472870dd0e91b40620db0b103a05e03605c0350cc02f11002b08823a05101f05101d0e10180f800e0f70050f714c07f09307e18717f 259797497 262621704 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_53 (k : ℕ) (lo : 262621704≤k) (hi : k<265455361) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x10d28a0450d21431152a508f0f30e709f17802d05709c05609b25402217606d25c00d04c00804b00004b0690f72dd27510103d2bf03a0b10bf13803213811b24202605313e08501b04f0ed0a80020c60950470670df0eb0c30911c214b07808d0361e91070e502b18509a18409908501408300f08300004a15d0a61bd18109107c1f503c0b10c005d0f211209e05902e1111b31240231230ba0aa16d08300e1db06a1da0940df06604223103e15b1090ce1521131d71ad0730570270870240ab0ee0500ee0a90100a800108115d0a50930f615c2b316a03b05e1a708b03115902d0ad07215807008601d04f0151cf00d04c00904b0001650691810d11a90910f40cf0c10ff17f05d07712603212502e08902805409a10f01810e00e0a80030f706808006704310004014b07a14a0a10ce2aa1a00740e502b05502805520108602108606d29500e04c0d410c13b0c40b50c209003c05f0770e60be05907312407213602413502013501a13409704d00713316c1ce0d20440d10421950c10e8 262621704 265455361 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_54 (k : ℕ) (lo : 265455361≤k) (hi : k<268315730) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x2e16902905507021d18c04f0151b900e16700004910304617c1b71891320611311880380ff0bf0cd0310cd02e17802b1780260870211770ee0a900e04c0b81830670463160c313b03e09003b13a0a113a0361390760cd17f05607212502312412d05001904f0160e20061f212b1f217c04317b07d10103d0b20f411403305a02f1d30291d209b0ac0210ab01f0ab01b0aa01708400e04c0081ac0d41ab09404609407e1a40f60b40c214b0f405e0f314a0760cd02f14902c1490bc14802505301e04f01804f0121460001461d60df1d50431970a306103d0b207808d1d90b003114907308902705402419301d1920182120101660071460b80490b71450670450930a52de0dd0b31430e90393060340af0bd1370290fc0d70530230fb01e0fa01b0fa01408300e0830070821030491030f710207f15d1e520007b17a0a118710905c12f0af0be1592341fd01b0aa01304d01104d00104920122e0b50411df07a06007905e0380ce12f0cc0d90ae0290540241101190c80190c80130c700f0c7 265455361 268315730 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_55 (k : ℕ) (lo : 268315730≤k) (hi : k<271191260) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x1450eb0400eb07b1290a21290371280a005c09f1271090cd16221f0271c80221d317f05001804f06d0840030a815f0470b707f0b619f06414416c07905e03613a07713a03105919c16a02508702105201e05101d13706d0c80101360040a813e0e10ed0c50ec13409315510103d06115405e1e60ff11d05902d0ae0280ad0bc0530bb26801804f01504e06c2790d50a709529906529817b29818903505c2cd05a02e05809d0890250e401e0510ba15801515800a17606a04a10416606704639c1550d12a00900a132303505c11d0cd11d0af02605301e0ab01904f0160aa00d04c0030c722204706504209203e0b311f05f0370ff22e05b15212610824e02505201f12401612300f0e209712216e0480680460ec0442170c30910a313b1da1140c005c0bf0cd07405807205502505201d05001715800e1571a604918b0f71020df18a03f1890a205f0a00ce17208c02e0581712920f00530f00e401d0e30ef04f0150e200f04c0000e106904806825412a0c40eb0400ea07b1150382e5033245 268315730 271191260 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_56 (k : ℕ) (lo : 271191260≤k) (hi : k<274080900) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x2340241a301a04f0131370050a80b81a10670c50651a012b03e06107a08f03708e0363400bf17a19d0560261790200ac1510c90130c900b0831500a81500461d80e01d81451d710c06010b0e903605d10a05b1821ca0be0571c31c91711c801b0ab01419400b04c0ef0820ee0a80690a70ed21e09322712a1e808f0780b10330e809e0fe1530cc0230530700520990c901608501204d00c0c80b921e0950a714f0422f71c506011f0cf03519709e1880f20890d805201c0ab01408400f04d00b0831e410f11904509319214e07b09003b14d0a108e1e705c10912714205709c0ad02305306e0850170850130840d614813f04813e0c60ed04306407d0920a30900790b213113a0320ff13013909d3ec07011101b17809804d00f04d0000490950802860df06404012a03b08f0a10cf03405b11e0b026e0ae02a14a0d805310708706e0e30131c70050c70b80490b80f806604413d07c0911dc0b30791b10dc08d03205a0752160d90890d936206f0511060850b90830060830b9049068122094 271191260 274080900 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_57 (k : ℕ) (lo : 274080900≤k) (hi : k<276983038) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0xd1c91060a81051a20671470b607e0b60a40eb0a305f03714d10b0b102f14c0740e70260e607105301f0ca01827d00604b0ef04a0ef1940671942381210610a30900dd05d2690b102f16c1310560bd0fd1811260991110111110050a909704a1f11230671680ed07d0d210d1ef19f1ee0321ee1ab0cd0280551aa1260d808601104d00a0e31401361a80e10ed2bb10203c10203a05f0c20d01740e809f0e80740e717317a09a05001104d00a04c0030490690a70d40450ed17612b07c0620de2041750d013208d03308d03108c10a0591090570be16b02128d12f0fc01016900804c12e0c71a80461a80421ef07d0921660d103b0b324d08d0311a50da0570290e607017901a04f0d604c0011691c21a10ed04413e10d13d03e06103a14d03708e0331d60bf24817208802228d09904f0130840090831700a817004619a0440d30c416e1210b40c219807827502f05802c0cd2111120f10ac0990c91401c806b1c71190a710407e0b50400b503e15e03c15e07908e0c115d19011402e0af02a 274080900 276983038 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_58 (k : ℕ) (lo : 276983038≤k) (hi : k<279896264) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x510181a400c0e40d71a30680e209507f09412333f03c0600380b31a013c0f508c02b05702a08a09c1b202022d0192180111be0051bd1c31c926804112c10e0ec1212fb03512a0311d81c608b02a1140261140221130d911301811201204e00e04d00c04d12f0e206812409507e0d327406003817d15615e02c0af0290af0270cc02212701804e01104e00a12506b12509704513f1c82672150b30380b313318b0dc08c1740571740e702418909b08701a0ca01104d0032020970821c30450d40f91700c426f12113d10b1001ff13b02913a09c0e601d08606e04f00d1110031bd0d60812390c624c07d0922e924b03608e1920b10bf1140290e70220fd0bc0500120840070c90ba1d40661d40ed07d0b503e12b07919912013c0750ff09e08a07108802219701b0fc0bb08500f0840002ae1401941040a621b0f70b407b0eb0c210119205c1910b00740cd0270cc1ab0880bc24801424800004a1a91240ee07f1a807e09303f22407b1a70371a61f416d02e0af0be0550710cb09b0cb1521a3 276983038 279896264 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_59 (k : ℕ) (lo : 279896264≤k) (hi : k<282829027) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x23c2180d42030b607c0b503a24407805c1a105902c05802b13c09d0e716505211d20f0091bf06b0c80b90470680450ee04311a0c50630c51f20f716f03205b02e25502a12902412809c0fe06e04f06d04d35b04911b0810670410ed03f0ed03d06103b21215705d07805b2a621002608914305201d0ad1421391902772280450650420650e00920e017f0de05e0361fc1200cf12016e10a0890da05301e17b0150ca0060c90ba04a1411240ee07f15103f15003d06131b10103210102e0b002c0b01d20552290cc01b05001404e00d04c1f31e206707f1cf12315010d0d103814f03514e03214e07505802a14d0260890240ae0d90cb0bc14b00f0fc00614a09704714004406507d1700a41600f605d0f60d003215e02f15e0291280be12801f12701c12726914a06b04b12f1370ee0440ee07e15003f0b503b14f03914f10c14e0c105b0f408b02a0af0260ae0240ae0200fd0190fd01314a0000c90970a809504518007d1600a40611211fb0f60ea0320e903015e0bf0af0280cd02127f01c 279896264 282829027 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_60 (k : ℕ) (lo : 282829027≤k) (hi : k<385766415) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x1009000b18910418915c04d15b0f515b18706d1b724a1622ca03c0fe0380fd08024802d1141c205b0231671351670a61660731c71030490c60b406d0d50e40863fb1d20c11d21430341420311421b31550aa11420517901c17901609007615300117716e13d0e71871be16306b1620692081ae2071bc08109903406107f1420ed14107b05b1b23590a71aa00e0b81481a910308b1db04806d0d51da1620e31731430381430340611213c11eb05a0240591810911491f10082160720d813208a1461ef1be12409d04109d03f32d0821bc14c1bb03012c02c0951d009402412a10684482183b80011401d08706e04f00e0850010e41c51890d60452091491621360621361610f705e07808e18508c17616e02316d07016d01508500d0ab06c04b06b0e40f004706828017207e0640f918003b17f0c317f07710118505842f08801e11401811300e0ab0000aa0d70830970811720c70660f90b603f0b603d17f07a05f0792710332e809e0ff0720ff07005221505001304e06d0e500604b1d116b 282829027 385766415 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_61 (k : ℕ) (lo : 385766415≤k) (hi : k<389218922) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x30b925804f13308c2570f40e50f325603f09c03c09b08206433b0610311ad02d0be0271ac0231ac0771120cb1120ca2f41b104b1c00471b00450c50861300401be0391bd0ae0e124320124305d02805b0230dd0780570780dc01505400908f14915211c15223512606d0d60e504125503e0e31a625f10a25f02e0be02b05d0270bc02112b01c12a01712a00f1290010520ca12811c0b60a20f406d3611460850ff18612f03806303609903209702f05f02d12c0ed0de0240dd02138d0163250050520a41990701990c70480c604716d04316c0d41180ae0632e915702f15602d09602909402509407905801e05801b0ba01517900d0530080531b216510308b1ce0471cd0f31cd10c11803d1cc0391cb22c0611d11ac1080bd0251c902005801c05701b1ba00f1b90e91b910404d15b15106e08806c1871db1d312f1d309b1d211603411602e2ec34816801d05701b0570190560171120052852561651a11e21010f32552381bd2830c103612d07f09702c0950291bb0cd224106167015090 385766415 389218922 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_62 (k : ℕ) (lo : 389218922≤k) (hi : k<392685922) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0xd1ca0cb08e0730f70721c80a108a06e0f406b04309e08506708413012306228512e1090be1c40fb02114101c14101414000c14007513f0e904f2aa1c80e71c816e1500680b109c0830c208209a0340610ac0df07a12b01805600d05300538f0e91780701780e704706c04506c2231f710d06817522816214422105f02d16a02805b07a0590eb05501305500c0f80050db0ea0f70a40d907104b06f04926d16411a0871311b706703d0670af0641620c10ef16a1c405d0281690ce16901e1d81060900000500a404e1c10d706d0d606b0850670840661b609903517d1b505e07d0950a90fa0cd3070cb0540cb0db0ea2f521e0b621e04619019810019706603b06519606210a23302d05e02b05d07b26910712b01905501012a0cb08e07304f19204b16e17728b04328a03e28003a11703611703211603005f07c05c0aa05b02405a0221410cc14001105400b0530070521700d90e813e07004a06f13d06e0d613104406a1a719f03a19f08119e03319e18414202b1f41360bb01b0bb212053 389218922 392685922 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_63 (k : ℕ) (lo : 392685922≤k) (hi : k<396169714) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0xa512a0731290c90b713404913304713316509f0f413222409c03c16d0370c113a06113916b0ac05e02916a0aa05a01f0dd07705500f05400918c1d20da0a41bb0711100a10892830d509d03d0672b71590330c002e0bf1220df02109301e0570170f900e0ba0020f811e1ca0e904b1ec0b50a00b309e03f0e416314503732317409717405e0cf05c0241e80cd09201909200f2010ea20113504e11d08c11d04a0a10b50c704616e04206903e0c30b00ff03519f0ad1be02b05d0cf19e02119d0a812b00d05300112a2380d90e823119204519104223616309b10c0c20360c11620c016114307d1430a905901a0920150910130540080530050b914a0d91de04906d0881b10871b113b09c08309b0381db0801db1090df07c1da1201d910712b00d12a00108f1ed04f0721ab11d04a06f08a2420b313104009d10c17e17509903206003017d07d17c0280950a90fa01c14101209000917a07508e1701790712682bc0b41cf04106808406603728a0ef0bf02b0df02505a0200dd0a80570a7091 392685922 396169714 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_64 (k : ℕ) (lo : 396169714≤k) (hi : k<547222417) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x2912d0df0600df12c01b12b01412b00b12a0b31430b21420fc0970790ea1643b10f909107104434603f2140be19f1940f30ba0ce0280cd08514601f21101321117d1430db1711b61271341ab11815713204513215606f1a90f608c0a60380d11a70f31033bb0261100202b70172560040ee1670570b210c2170c50780ea07704c0d70e90ad21c0d50903db15514925212f0320a302e0651690cd02506001d05d01705d01409d0112f60dc09a0db09907b14107804d07532e1a00430700e51301cc1140e30a503519e0312570290a10250a008419c01b0ef0150ef00d0ee0dc05882f8348498010fa0100f90751cb0ca0b707111117004616f08816f0d506703c3ca03512f03212f10a0bf02c05e02a0df02505b0230de01d12c0770dc00829e0cb08e0730b80a304a1a30481a308815b0b215b03c06603915a13a24c0ad11702b11602805c07b1150a92280140530000512211790e825f06e0b429704206a03f0e40d40c30f116c13a06113909702a05d2090bd02316a0cd16901416900d12a 396169714 547222417 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_65 (k : ℕ) (lo : 547222417≤k) (hi : k<551342872) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x1a11ff18d03c06c12318c13c06813c1600e10640e118a0840cc0b711001610f01105b00605a0b40ee07e15b30609821818525c1be1a20451a104325b1820f612306b03711303216015312d0251e42b233200005a11d14311b0c711b3d218f04c0760c30741400ab0430aa20e0a903c1300e406a20c0a402f12e13a0620250611392a101610f00610e0b405907e05624225607904f1d81591a20471a116e1a10bf06e03e28c19506903328b0b911102611102019c0b609e01309d00d09c1a505727619a0da04f11904d1190c311810907304507122b0d410606d03d06d1050a61950a51940cf19415f02806202606217e0f001b05d08019b13710d0db1280b00eb0fb04c0fa04b1181250d50440aa04113103e1152d41c30330671200650870a20251c101d10f00d10e00110e2dd1712690980fc0c407604a1330c114b04314b0bf1b213d06b03806a0350f40310f31030a31a61460210cc01c0cb01409d00905a07e09a07c1700fb0ea14d04936115711608e0a808d06c03922210411302f221 547222417 551342872 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_66 (k : ℕ) (lo : 551342872≤k) (hi : k<555474375) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0xce1801f501309d1ca19c0b31c00b110c0791bf16520107404716416f2170400a803c0a80bd0690350a502e0651a80a10211c208221300109c19210e0fe2110b00500b004e2c80ea0750921f826f1321060a71821d60311d502d2980261d41530601521f425f09d17e14417d09a07b34e0783d41651f017913f06e0e506c0be0d20360d10350a502f06502b2050240600b72040111880ff18807e2201b714307904f1651271e91580ab15811708f06e03e0f703c0f615614a0360a508a1491540a302b11202506102106001e11001a1460130ef1b80591511c01b705407b1bf37e0ea0ae04a0ad0e90740460ab0431b40bf1b308d0d222a0d00310d002b0631530610210600201b00100ca1eb09b07d0c713617107904e1e90ea2421091e82b60700402a419606a16b29702a0a20e006113a0a01390f00820f00120ef0021880ff18719110d0fd15a1f904c0761261f80c20720443ce10706e1de1300371770890a40300652e91f401f14600f05b0001f30dc1431c80500780950760940fa34c 551342872 555474375 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_67 (k : ℕ) (lo : 555474375≤k) (hi : k<559628233) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0xbe1310371310341301bc06608728d0e10ce0e020501620500a20415119c07b15b07804e0fc0c41fa10a0730c10d50401a228806b0362690892680292681dd14701c12d01405c00e1f50de17307d17307c0c722822f0d91bf1d91411a30430aa1840d403c1621230691a91130870f30850610220f201c1d40131d40de1d31920c819215b2900950fb1590731590720900f80c017903a0a60340d10bb12f02b19f02323f01d05f01a05e01905e01309d00309d1cb1880b30560b318707a1870791862430c41c812607212617a13f1161240a708b11403106702f0cf0e10ce0230cd0200cd0df05e0181d40091d32910571b80521b70970b010b0d804b0d81d018f1261b51bd06e03d06d0be1b30e41b30890a41cd1b202621401f2f000f05b0010ca07f23d1500991eb14207704d0771991e92100ab0c01d71831d713d0d11220a41030641030631021d401d0cc0160cb01105c00d05b00609d1932580fe0c813710c17c0970b004e1350ea17b2f70ab0440d51570f703d11516c0f41810cf029 555474375 559628233 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_68 (k : ℕ) (lo : 559628233≤k) (hi : k<563798341) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x14e0c107009018f03b06c03918e16d32502b0a31810610220611021110181110110cb00211008010f1ed1f507c1f41370ec17d1281c91420741410722021181251c71f10a71f00680310671ff06408506102006001d17608217500a1751000ee0dc1c207b1c117d0c617d04c17c1c00d70450ab04226b1070a81071160371e82560670bb3880270a20240f20200f201a05e0160f100d05b00005a11e10e3d40ed30015b0d915b0761270ac2da0ab2d913203b13203506816d0a40872f210311201d11101705d00d05b00509d0b51c20dc09a2530ec25219b14f04a0ad20217b0c117a04017a16e06c16e06b03718d1970d119617702b0f30230f20e009f01309e01105c00c09d1691891931440db14413704f1b70950fb0481b60451b60421b52100a808c0a60350a61ef0f408739002105f0b70cc0000ef26015d0fe05211b19b0fc19a1190481190c211819945503c1c60370d20bc1c51221c51bb0ce08523201b26701220500109c32705607d0ec0b004f14f0940752200fa21f0d50e73ba 559628233 563798341 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_69 (k : ℕ) (lo : 563798341≤k) (hi : k<567986649) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x460ac0420f909006f03d4c00373c503006621f14a02714902106001c05f2ce09e1010ca1cc0550ff29916810d16804d1ca0942530450721f32520bf0a803906b08b0a603221802e1c61bd0a30270a20860f301f0f201c0f201605d01019f23a15e0b42e81dd12a0792743ce14213504514e0901b60e71b603a0a71be0a61bd06602e1b40ba06302706302332f18105e0150cc0100cc0080cb1fe0570dd21417e09807904e11b09611b10b0750480ad09217b0e817b08e0f70390f72f90f502f0f51041610230a101e0a001c0a001715f00815f15310f1691451ed09717d2980d80471a40440ab14013314006d26406a0bd11508911402d2421a916001d0cd01532e00018a1001891380990db04f11b04d0d90942eb1c00fa0422ca10811703a11608b2081bc06302706326f06008309f01123200109d1000c90dc2141b90c630009519104617b1e211803f11708e06d08d11603911603417808917802b06302225c01b0cc01405c00b05b0801b107f0570ff0c90ff0ed11c1d315012807415a 563798341 567986649 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_70 (k : ℕ) (lo : 567986649≤k) (hi : k<572185657) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x7d2c907b0c71510ec0773250d80930ac14106f1411650e61640350a613e06613e0640860f302006001c0cd01405c0010f01ff0571ff0c807b0510fe2230af0c51fd14207219b07003e1fb15906c08c06a0e50a603031e02b0640860621970f301c0f20170f20120f10011112c412c0dd0541940500790970da04b19204919204511924c0d524b0f70be1ea1230662c50640261610b906001c05f0b805e0121e700109d07f0570b405623a1e507904d1370492b60461660900aa03f06e03b16422f2361ab0d002a0640861130b906001c0cd01724200105a07f0ca1a82b12d804e0b004c0af0c51dc0930730451db0900aa03f06e0e606b0370a703414b0311150e31a110406201f16001316000915f0b509c20e0541dd27520d10c0d90c41fc0431fb0c11900bf1fa03818f0350680320d10bb1303750610842070b711100211007f05816a09a2c20ed07904e17d2040740461b70910d604014d0c01b62fa2a802f0f51821490200a00b70cc00305a0b50570b33540fe04f2380c50760c4286 567986649 572185657 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_71 (k : ℕ) (lo : 572185657≤k) (hi : k<576404116) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x12d1df18b07c18a1de04f1de1b00ae1290ad0440ac0e90701412c23700d30bd1c802d0a40261301220a101805e01605e0b705c00c05c00505b0b609d07f1e711e09a11e0512632330da0950d91e50ad0431a50901a50e70a826716402f0d12a40640ba13002213001b16101709f00b1600df09d36e2b31de05111d04d1370951370470ad0461670910d60901660c00f80390f808c0f70350f710611502d1150870620230a10b80f201411200c0cc00105b08115f07e0560b415e2950971cc1f50d80452940900d503b0f810711612406702e0660871140232b408309f00b2d51a909b1bb0ed1ba15d1512d30ad09311a04317c0c10aa03c17b03917b1581c803217a02f0f50e31c70851c61211c601109e0001112000ca11e1c41a80c71a704e1a71880750481a60921a51c10d61c019008e06c1bf0690320f602e0650282c00851c601c1c601109e0811c51df10f0dc05207a28e3d81f519236606f03f06f1f30d403a06b0e50f60300671052510ba25101d05f0830f200905b00005b1bc0ef 572185657 576404116 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_72 (k : ℕ) (lo : 576404116≤k) (hi : k<580631217) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x390a80362ef08a1eb0e41eb0e20a101a0a000f1e90810f10df05711f09b34b1e71bb1c40760941680461681c214f03e0aa2750f80e60d30300670e40d02d20600840f301116100705b0800ca30615f11e05011d04e07815d0760953e30430d60901350e70d40380f80340f703227b0880d008716313d11301405d0e01a011f1763a310e0b110e2710c51680470d817214f0c20fa17106d03a40803311602f13202913122106110309f0011c607f1c50dd0c94d404d0da10d1510c42952be07003e0d50c006c19a0d303214c02b06408706302314a10414a0161491971120800580b505707e0c922d0c807a1450da10d0fd0490fc0930731f50711f526f23f26e03426e31b0640872b60b906001d0600170f200d0f20b632807b09913904e13804d1380c50740c40ac04014e15a0a903914d0350691242b602b0a40ba27918327900f0cc1aa18c10105610018b07c10e0b11451381730ae3090ad1871660c113403706a0340690300a502c0651d01300b905f01609f01009f00809e12005a0b6 576404116 580631217 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_73 (k : ℕ) (lo : 580631217≤k) (hi : k<584865565) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0xe61171c114d1240640250a302120b01b1da0111d90b712f1be16007d16011f10f0dc15f0ff0c613809511c1d51ba19d07003d1180e73372ff0a520422a1840a10190ce00f0cd00325318309c07e25211f0c807914613919e0750460730440d70410d71720aa1270a903624708a1b71230620ba0ce0101780e01fa1552c107c05111e09613810d07538517e19d2ae0c006c1f506a1f41a419a21b2300a112211300105a07f1d80de1d722e2cc0b114517f0c50740c31360910d603c06c08d22b0e51160890a402706310522916d2280b72280b61602982270b30510ff2430780961380950752bf0fb1433370c011823206a29a0f602c0f602806208616301c0a00b820a0b705923d05723d2080b21461390961382073240ea0d70c223a1090a910911803611708b17b02a13102313112205f2020f213c0f00b405407c09918004e0fe09511b0c40ad04217d03f19217119108d1b810711602e1640bb0630220f401709f00c0f208114815405615425e0dc04f30604a13704713704416725c06e 580631217 584865565 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_74 (k : ℕ) (lo : 584865565≤k) (hi : k<589118597) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x190ce0830ce0021121830571831770b30500ff19f1520951520c411b18911a15b1a60e70d40320d30310d31862fb0870d001b1a30111a300205b0e00590b61a138416010015f07804d07819f0da0ec2f30ea16815c0fa0380d41d41cb1071ca0281ca1050a201e16300f1c800314a1d11611d01c707c05111e04e48c0470d80c316803d0aa10a1670361661080d314011633c14c01f14b0160ce00a0cd0000cd1562f90de0f00b40ef3561460761440721440ac03e16703b1921d31ca1402b91050a21230f40150f300e0f30001490df1c71ab14716b10f1530c60753d21cd0401cc03d14f08d14e0330691070d202d0d21061640bb0d01bf05d00f05d00c05c00509f28e0591d01611d01c62200990dc12b2000951bb0920ac2501361c227d03614e1070d20bd0d216f0d00230620e220b01505d0041fa1972280b422741b1462a40940ae0c428b20606e20632408b13302e13302a1320e41320231311230600190a00130a012112f1ab2ee13b15f07a2790770c51510c41370911fe19c0f9 584865565 589118597 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_75 (k : ℕ) (lo : 589118597≤k) (hi : k<593396104) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x1ff08a2640272641580601050a100b05c08205b1221121bf09c1bf0530dd04e13a1f90fd0460fd04316918a0700e906e0e916803821e03411802e21d0271a501d21c0171a400b1a313d0f207f18d1ab05110004d11d0951e00921370911bb03a1ba0c02650300660890650bb0f501f14c08414b00f14b00414a0e018e1d114816c1101d015f0db15f1cf0472d30440ad2260aa03b06d12717d03317d02f17c08917c0261ca02217b01c17a01517a1d20592821fb0b40ef0b204f1e125218017507304207117419403d19303a20f1f614e0313070290d11f506202006101d2a20130f30030f32401fb18309c1200ef07a04f23e1d71801750fd0440fc1f817f1f70d612820f03717d03417d02f06602c0661700641700a313e16300f05d00917913d1621bf12e1be3a318212c1e010e25904525804207119d06e0c106d1d41661260d314006502916513f0f513f06113e1630120a01990591831491831100dd0981cf0c61ce1c52bc0ea0fb10b11a03a27e1721180300a5159064024062020164 589118597 593396104 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_76 (k : ℕ) (lo : 593396104≤k) (hi : k<597689002) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x1b30d826d0aa0391681091670310d302a0d20280d21af06202106201f0611060d00151a40811ec1d21c807b09932a0c70772a12a70930721750ac03e0ab08f0aa0380a910a06b1720a60bd0d21590621e50f500d05c00105c18505816e05716e09b18312e0b304f18210f0770c61392370fd0420fc1c506f0c10fa17317e08b17d02e0661c231201d0f501424859f09d23205223104f07912c3860472be09107009106e4d224a1c30671c217c1d41cb01d11501605e0011ec1d205835a11007a0ef0b104a0760951bd0931bc12a0700901bb0e911a22624a0321ba15a0660bd0a50270630230620851ca0141ca0051c925c1fc1560531e21fb13b26e1961d80740eb07212a0d81d606e03b0aa1f706a0340d415a28b0280640871dc01e0a20190a10830a000409f1c005a1c00571bf1eb1ac1ea1001c70dc04c1bd10e2f51e82b11b22f419d06b03516703006719c06602916515906201d05e0100a000209f1ad13010305719809b19811007a04f07904b0760c61390930d80c31371281de19d 593396104 597689002 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_77 (k : ℕ) (lo : 597689002≤k) (hi : k<601992936) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x205c23409d2241a30b304e0dc0ee32b20a0d80c306f08f0d60c10a903417e1f80660291170240631060d001a17c00f0a00b805a3810cb07d29736522a0772e70af0451e10c41e103e0fb1c52011092ea0290650270642171cc01b1cb0120cf00005b1c105916f09c10212f0b40ef13b0c80780c720304613912a33d03c06d0350f90bf0d41f720f0230621f61320131320091311040590b724818409b18405118304f0791fb1821fb1be1a030b0400ac03c0d60c10d503206802f14f0891a619c0620ba1a50841a50011fd0e00570b61fc1ac04f0b21601ab0961ab0471aa20a11c03d06e08f0aa0360f91e71180291170260630222980850f501005d00c05d0010f323317a2330f123209a07a20b0780c70db0c50ae0930ad2091510c22112080a80e71930891921e60d101f0d001923b0041a40e11a40b705716e09c26a05215524711f24633d15f0730420d82450d703b1a808e1360331a71420a602a0651411a601f3080160a108309f1570581030cb07d09b0b41101ab160077048300 597689002 601992936 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_78 (k : ℕ) (lo : 601992936≤k) (hi : k<606317167) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x1f00250f701c0d00131ef00009f10409e1581ed2c22570b31b610017818312c0fe04507204107117618103c06d03906c10a0a814319402906402519301f31f08405e00a1ee12309e1d41ed0df05307c1ec0b24451e310e24009324003e0d703b0d70371e00331e008a0660890a510706210706101b0d00161cc00c1dd2430591040562420f12422560782561e31a12131d907103d21208f2120340f902e0a60290a50261a70860d00171a600205b1231142ce05616e12f0de04f07904a16c15f0fd0400d80c223003606b35506702c1df0251de01e0f60840a100f0cf2071dc1031630df09a07b0f01201b50750470740441960eb07019f1691290d612816802c0650230d10200d101c0600180d00140cf00f0cf08305b10423b10312f0b409a1990c80783b00ff0471d00431d012a0ab03c0ab0391ce12806912706702c1180e50630211cc0150cf00e0cf2510cd19a0550df09a24f22b07922a1820c60da2290ad2c507003d15103a06d03817f10a0a81420a61420641710d001914d00f05d 601992936 606317167 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_79 (k : ℕ) (lo : 606317167≤k) (hi : k<610648697) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0xcc07e14b0b50510de12f2511fd11f0c711e04216b09116b08f06c10b0d502e0672a21f101f06101c0a30180a20112e11f809e0800cd1f717a07c14a0de11007711011f18d0730921391ea06d1ea1bd0bf0f90e71bc0261bb0220d10100cf0010584a514a07b14a0de11011f4b42410c324014506c1441a920a0d40890650891a801f1a71410d000c0cf0020cf14009e1580550b509a07b04f23411015504a15527e0da0432410400700eb1f308f1371b30691b21a802814f02114e0bb0600110cf0b917c1050cd2f01ee0b512f16e04f16e1ec11f1611980ec07110d27703927608d0a802d1352090a401f0a31253bc0b905a0b705707f3c31d30510de12e1001612782af1f315f0d80c20aa03206902f0671270f80250f71261170171ef14005d0830ce13f0592260550df05107b11011f16113b0470740940fe1ea1961ea0ab03838003306902e2b30292752080a30e40d000e05d00805c1e609d1221900b50521e40c907904b07721c0ff21b1e221b07009025b1290a908c11902f119029 606317167 610648697 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_80 (k : ℕ) (lo : 610648697≤k) (hi : k<614996785) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x1c806f09011c0350a915e2aa02a3790e50a301205d0020cf1c40cd07f1cc0e00511021901d41790b104811f09411e26516c15f0fc0390fc15e1d00330690bf06702c16915c06415c06302006215b11715a1660831330b91650e10cd13f0542520512521791841b725109407214725003c0d72d340802e1190291191f911701811708405d0000cf22805815817b2600f00791a40b20480ff0453422710d710c0aa0340690310d508a1bc0260f80200a30852b41b109f1b016512305407d0531af05007a04f1ae09727912d27904218223a06f03b1811450fb08b0f918a1502371170180a20100a10071331061320e105707f09c26d32019a0970dc0c716d04516c09316c15f32d0391380350fa0e80a71d70640bd1181d617d00814d1051310b609b07c20e2e50970760ed0da0ec11d03d11c1c70aa1c60690310d502d06608919410714e0170d000c0cf08205b0e21310e009c20733d1841490772980af04519827e2910900ab0e906b03520308b06602816802416701a05f00e0f500420019c 610648697 614996785 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_81 (k : ℕ) (lo : 614996785≤k) (hi : k<619364575) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x17109b1221cc07a1cb2c52671000440720410710910ac12b0aa0340a90330d602f0a702a0650252ef0860d100f0d00040d00ba23014014d1c422f0df0f11af0970b104907509313a10e06f03b06e03a1390361380c10d63290660290650e611801a39e0020a015a09f24613126109b07b3d70770ef1ae0c625f04211e1770d833e0fc14506a0311be02d0f90280f90e60630200a40860a301719400d19317205b0821921711922c617b2c51120791621841b71990920d812b15308e06b0c115214413602713602313501e13501305e1060a00b905807f3220b505107b0500de0970770c833a1781981a20fd1a10d717635f02e0a710a0650880d201e0610152760832cc18827510413110304f1d412f36a0480750952b80ec0ad03d0ac1a106d23a0a908c3832391190bc0d10170d10120d000d0d000305a1590571590f212209b12212f0790c90781100db04513b0ec0ad0ec0d903d29215f2140320691290a71090f80880620192d71b109f4470f21af0511af04d0dd0c82e636d072042183 614996785 619364575 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_82 (k : ℕ) (lo : 619364575≤k) (hi : k<623748978) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0xd301e0d201911801111700221330b11519d2ef1f91300791b93630450db0c60721a30701a30ac18d2a008d0d615e06608a11a0251f30e60610181e101005e00426a0e305a1890f419d09d1b10521e714b0de04b1850470b004418404118412c0fd03a0fd0c21821fd2a00e80a702906526419501b06000e2401e905a12509e1e823f07d0521e704f23712f10114a0b10471551dc0fe03a06d03706c1761520c00681751d01280d301f1cf0120a20e40cf1d71f110505520917c0b51ef12104b2e818f0741790720920d90910fd15f0a91da40b0270630bd19508505e00d05e00930f1d71330b80570b71321e80f21e70501e70f00b204b0b21102e70c613b03e0fd03b1e408e1e30c10a81440660290d40231e10861cf0011ce10613317205633c0531b01a507904d2080970dc0461ae1610ae1a320603b11c03720503111a08a0a602420301e20301405e08314e1062830e124d1591ef07a04e0de0491000ee11f24a18309106f03b18203342902c3f20230f801c0a300d0d019e09f080056 619364575 623748978 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_83 (k : ℕ) (lo : 623748978≤k) (hi : k<628148909) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x3c1840391830c206b03218208c1821291810251510bc1500111500060a10831a915b11515a09d3161df1221df1020491010c816f04328910f0701dc0ab0350aa0310fb08c1822ec06302119617405f01205f1741940e319408009d0e117d1d70501d604d0780971d50471d50940ae03f18403925212b19802e19702b0a70270a60251d101e1d01080d100319415b05808009d20a1a707b1a613e1a60780ef20819013c10f2171b711d03511c0ea37522c0a60220d30850a214205b2e023107e09c2df04f20904c07750e0af0c62611a313a08f06c38211b02e11b0280d30880d301d0d201a0d20140d100226b0822220e20f41240511b01a61020971af1631af0c60ff21f13b1fe18310d37e17606723b0650250640240a501e1500860600131a900b17f1ea1a808114e19e1a70b61a70e01a607a0ca17035e0750460731a306f03b26008e3a10e906808a25e0220d301a0601fb16808405b1061a81fa0f312332407b04e0de0f013d12e3131ee18403d1833360fc0320690bf0660be0d3022 623748978 628148909 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_84 (k : ℕ) (lo : 628148909≤k) (hi : k<632560155) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x2730cf08005607f1e11241e00df19218704718638619b03d0fe1b81550360fc0c10a808a2881a10a401605f0050f70832ac0e20551fb1e01d704e1d722113d0ef0dc0c607203d06f0c30ab08f26f02f26e0bf06508826d0181360e505c12626c1b31a80b61662480990790f124704524604115626806d0371c10c12dd1b606602706502615201f06224a0f800f0f70000f70ba05a1b309f1b30cd07d05238204c0b21ba0761b91af0c616e03b13a03713a03313908d1981290d40231bf01c2e71a005e00605d17419530d05719e21307d0500df11307911212117b38104216e2100ad36806a0c13ac24a0640220d301a0d20860d200e17f10717f0b905710505426404e1700c91d60470b024d13c03f13b12d06f0391830300a80290d40250d40210610190600110d10050a10ba05912509e3c829e07b09a0b404d0b31cd1021cc16f0460b00430db1ef16e03c2070c30ab03420623c15214406301f15101720400f15000205c1422861c60f41e91141590991582011b023e18509418503f11e 628148909 632560155 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_85 (k : ℕ) (lo : 632560155≤k) (hi : k<896117606) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0xbc16615703715609a07323f1e90d11e90230b30162ed16115119616e08d2d030c0aa1ef0dd13d16a08218411818434804507b0d71160400ec1ca07412407002e07002c06f02a18c0943070920e50fa0af0ca2670f72661da26611c2652fe0520822642fd04815909f1580411581ca07603b0760360b80330b828106f02a06e0224670920680102341c60641c62331402330c812e0882a40850dc0c32310820a423904b0f00a12261492260d50bb22e2370990e902c1110262350201330162340072d122b06222a1d022a05c89481981080118302b0661290631290a501719600111831938807f05521c14d34a04d1710970dd1ba1f90931f803c0ac08f13a0331f70e90670281f60220f90bd1f500f0a20000a23c20f50e21671c605107b09a10304b1021f11c40ef1c30431c310f13b0c40d91ee0aa1ee06908b11b1ed0a60210f90870610151be14305c08314f0e30581060cd40204f0b42311700f017009516f0940af2100d922f0fd08d1980e919822d13715e0d301819600d05e0e51e2 632560155 896117606 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_86 (k : ℕ) (lo : 896117606≤k) (hi : k<901402974) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x1b1331980e50000e408f0632191a20f71a214027708727721712c0c212b08012a1180d907d1030ee26428c09c0750382130341be02e1be0281a501e06a01721000f1bc0000b030115130126711d1093ff1ce0f20a50c21cd15a40c13a0431750d60ed1471a703325a02b0b50250b501f10f01510f00e10e0cb06326005f17b0ac17b0df0c60580f412c0c31071d904d07f4281910a01c003f0781011bf1ca18e03107109818d02818c02406c02018b01506800206529f3140f830638e0de13e05408437d0f20da5030a10be0430bd09f33034d0ba1260740340b802f18d0d00b51f31a501a1a40112581f20e317c06108c05d11d05b0c72eb1ac18615c1060f104d0f104b0f00495282630782631740380b909a0730d21e902a1e902115301506801006700d0670fa1510ca0ae19623308a0ab15e05817905527e05126d31e07f04827c18338103e1370380b90990b702e17236e06c0200e60170e501306700416e08d1a215f0e015e0ab15e12d0850550850dc22804e07f04a1ec04507b09e 896117606 901402974 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_87 (k : ℕ) (lo : 901402974≤k) (hi : k<1412682099) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x5f1c42350910b826b24a0d61cf35b4741bf1200842861340ec13427117e03038427007802407801f0760173832451560a01561171552f00c22f02772420620dd2c21f91740d91731a40531a40501f704d1f71923ae25e08403e1a003c0cf16d0cd03440625b07802407802107501807500e2f928337430106911437309912936b0600952f60922f626b3dc21004e21004a20f0470860442681e820e0ac2670eb1051ca13138a0770a410101910100924f0e424f33106b3962633960be1122e616405d2561263a24531a30b410b04a0860430d103f15c03a3840320cc39807a1ac26511926500117a18a0fd0e10c00991980de19716405f2dd05b0d80542b80b444d04b2b724815d21a0820ac10603910603507d03010402c1030284c101c17b24419b11712c3001d444406109583381e87782f80126c03628b1b31d502c1d40261d41221330141330071320900e41f20600c915008a14f15e05911c05511b1080f30500812eb0c00472fe10307903f07821d07603811303315602b06e022134 901402974 1412682099 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_88 (k : ℕ) (lo : 1412682099≤k) (hi : k<1419328010) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x28d09d0c218a06709a1992a928b13d05d13d05b13c0b91df0542290f322904d2ca3540862872a403a1a003319f02d07b2851590200c91190c700a1002172791e32794682e71650f90dd15109405c1101ec0900b81621d008d05130f0b308927427e04208423230d0aa30c02f2a30281310222a20131000001570a006e5820fc1a922029524d09505d18624c10f1731f80511f81b21f72740d30451090430840ad1340381340350cd0aa32c1ad0ca0240780e71f22450ff09f0fd09d2210e02201e10631650bc11121f09321e1a52352b905110c1230d50f008704520f11f26803a20e0eb07e0331bd02c07a02a07a02320b01307400c1ba29720a09f2091410c209c39d0980be2950bb3a31960d905608f2f61f825f1c00460860431bf0ae1350ec36803536802c07a0281310211300191d70030710e41d618b06d09d06a1670670df0641c537209212613b14e10d0b508c19313804b3d619108419108303a10603832c1e61f302a0ca0231f201d4d600512e2ce06e18a2200df2200de0620dd 1412682099 1419328010 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_89 (k : ℕ) (lo : 1419328010≤k) (hi : k<1425991333) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x23c0150c700a0730a20710a11d74fb23909b06809b2c51fc0630970601fb1970da0f51df14f1c30f31c204e0d529c0d22c110803a0801490ce11d19f0a819f02415911a0742d006d2bd2652cf06709a2641fc1ee0950f81fb1751a60581a605508e0f408d19430f1b210a0440850430850ee1080ae1083050ce33507d1ae07a0280ca01e2b50100730e51f10e31f118b1f028312b3322b22143482580f50d819508d21d3a304a1a31921092881361e808003507e28617e28607901e1300151300a231b24519b11606814031a1fc23718705d5710560d812508d04f1600b31c10461c014b1c003f1350ad08139a07c02f07c11b0ca0e817d01a1010e62a21442c618b06d09e1d53220661fc0f91fb23711105c1103c52122e549c04b0d30450d20440d22c00820ac0800341332bf17e0230c91ca0c80110c700b0c70010c634206f1c812c16706822d0651880611121d216305a0915c91c21d029312210a04710a0451090af13603e3690381a016d32c2000ca1ff13001807501412f0000c6360 1419328010 1425991333 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_90 (k : ℕ) (lo : 1425991333≤k) (hi : k<1432668451) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x1c012008203b08103908011e10641c17f0280780222680142671192670a106d3c20680e012a3510f911205d35f2373501b408c04f1f904b1f841115f0414e51e920f03120e02b20e0a620d0a507601807400b20c43e06d3f50c109b0c01890631891290951d313d1d210f0553312353d92f70d304126a29c08103707f0351060a90cc0ea20e02620d02010201420c0014bb0a00c41e40c31e40681c712b18906137c0bb22c17536d21f08e2613200b30890490880470d321c1c01ce0d003815c16e31e0a71d90e81d90191d800a07318d1d70e41d71431d62f23c809a12a25912925905c1a605645217308c17308b23415f04615f23310803e10803b1070ac20f0eb25302d07b02925201e1bc00a1bb22f0c421712c1150c111506609906522d15222c0f811041108e05208d0501c20b40d554815e04013623207e0311050a80cb0a732d0a413001407418d1570e406f11712c0e149a09850809505b24224c0d80b70d83c52401b333f04723f14b10904010830623e1af10503015b028079026 1425991333 1432668451 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_91 (k : ℕ) (lo : 1432668451≤k) (hi : k<1439358533) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x13e0ba0920b95752771a514e10c0480872760851202280ed0cf0eb0cd02e2270240780a60c901507400f07400a0c72ad3b011815622f0fd22f19a0990621a905f1a817616415010f1501633392a80b40d504908841e1370ee21003a2100ab20f0aa20f11c07902207701836a0002ec3de1d73dd0681410bf0980612442080db15124305608f0541623741604581c124a26a1e907e0301be0a80cb0a62680190c81453940a00ff18c23a25b0fc16712a13f20911205d09305b1e11501e00f51a620608c2360d604b1602051830422550ad1350eb0cd19015b1ae2fd01b3f10062fc1e506e3442fb09b2fb16719913f06113f1281641d329614f28114e1f90f10d30f02110410d141d0810382923551a002a0780a61bd0a40750a40c80e61bb0a047c1690fd3610c11150bf1890620dd27813d1510da05508e17408d0b41a404a2ba0460860440850ae0d00ac1a10331f502d07a14634c0110742001f218c0c41690c20e112c0e017809817809730a0dc30a1c505613b14f0d730828004a280307 1432668451 1439358533 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_92 (k : ℕ) (lo : 1439358533≤k) (hi : k<1446072160) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x9505d2840591e10b810f0512f104e2821232120451380411371930830390cf1b115d1b026a02a26a0230ca0200ca1ae07501507500e1d90e61d90a120c09e17b1420660df2b509717713e05c13e0b931319722c04f3123d51840450860f018304018203d2290391810371810aa47402a15b1ae1310140740042250e522509f1562460682460fb1400be2453d60933d61e12070d70500d742b2570443a61201a203961b02f10502a17f2481f40012a40a00c41172670e212c0e01791673bc25a2091c61b61631750d80510d70501621730880460861213c00ee40023313403018002b17f02525416c2530011300a212f1ca06e09f0fe25c0c225c1b925b25022e05f22d0f81111272140b81630f408d0511620b421204508604325624b0d003925548f2ee02a10402313201c1310140c818e0c624725209f17a3532b51670610dd2091880ba09137610f05310e0510d714e3500b335f04515f21d1dd03908003808011e07d02e1db21a15a01f15a01715921912f0e40c240f155115178096177 1439358533 1446072160 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_93 (k : ℕ) (lo : 1446072160≤k) (hi : k<1452800282) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x9927b38e17811205b1110ba09127929726413b26310c0f21df04339903c0820392940ab07e0310cd0a94010222cb2020750002ca44d29109e12d1160fd1ff06418a1540de1b83de05a0db0b926f4453b604e08b2073130472121b30830ac07f28a15d02e15c02b18002617f11c07701a17e01107400225332720d18d0fe09c0680e11d64400fa1134bd3241271c51251622071852361600443c20ae08203c08214a1350ec4b619010402310401f10301b0760e710200f07400613011927d11827c09c06909c27b1fe0631401994a305b18826413c1500d826330204b22b1720d304422a1cf1081cf2290ec22802f25516d0ca0100740020721cb10009f46809c06909c06721706111305d16505b1a81b608f0f562d31a28112210a04010919308203908003610711e13402b3101cc0c901607511a1582e40c516a0c24cd0650df0bd4c217709330b0900561c50503dc04d3020f13010430840ae15e28a2de2030cd02f13402b3b20a61322011590001590e61002001d827206927120b2850f9 1446072160 1452800282 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_94 (k : ℕ) (lo : 1452800282≤k) (hi : k<1459542394) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x18d19d14306709a2a437323a1a90f81650561640b816405118633c2590442580410d203e24114b08029e1c002d1c016e23f01e23f0a40c816c0c70e612f1ad06c1ad0c232720c0990fa11305f1131293630f71c60b71c512608d14f08b14f1c40b21c30451c350d2810382810322800a928001f13201927f0e70c61cb12f1ad06a1ac06828720b1fe1781890ba1e20b90900531630500d70b40d504910c14d26d03f18303a1820381360ab07e21d18102c1800272de0e80760190760131da11a0c60e50ff16a12e1ca33e1150652181540971b921705c21615218805613c0523a91ed13904610b0421c23ae31203207d19126b02126a01826a2020c63560c509e06a25d0fd1422b64111784351d40da0b90da32c08e0500d714e1a50481390f010a2b215f24b18103207d0a910502810502317f11c17f0110740010711e72a409c15624712b0981d61fe1993eb1283eb0b708e17510e04e08a2a01fa04410a0411f903c1dd0ed07f0303980271a02320c81ae1bd23212f32722509d22409b066 1452800282 1459542394 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_95 (k : ℕ) (lo : 1459542394≤k) (hi : k<1466296667) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x1ea10502224001823f00e07416d10131906e0e31d818c2250df0601131f10932501c64751870b53d20493d20f00d221f2421b210703107c02a10502515c2031a001407500e07400415a1af0c616b19e1440fe09c2b81ac0640981ba2180f90dc2b61650544b005031524e0d424e3140ee0810390d003307e0aa4620a710401a1a00091020a319f1cc1581cb1d90e30681160671164b62ad05d5020574850512be04a2bd1ed1841711080374ec14907b0291340a713301c0760150750000c71cc1581441f41ad1bb09b27d0e00630df1ba0971f13812a309227a1870521870b53b727922c0f008403b0811cf1060291f701e1f60e81f60e71592492542f706a0e20682f62671fe2230930591880572f40521632210d72202590480870441df21f24203b2571b22570a92560a807902115b01a15b01307421b0c70e629209f06d1440c31432dc0e11ba34623b1e405b25b0f734512608d0500d704c13a0b310c04610b21f1a403b1080ab07e02f3dc0250791471320160c900e0c81461310e60c5 1459542394 1466296667 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_96 (k : ℕ) (lo : 1466296667≤k) (hi : k<1473063576) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x20a3902b50890b322d04322c0af08312115f03449b1490cc0260cc1484c400807330a17d28923e1ad0661ac1bb0980be1ff17913f0583060542ad1ef10e1ef1a70b310c0b20861b413803c0820382820323030291c00221c001b0760a50750e83321461be0a10c509e3111e712d0e10661423ce0962521c80591c743d34604c16204816227910b0b00d21211370ac13603013502d0cd11d0780202f10100740a30703bc0c421a06921a0fc0982dc21805b1c70b90da0541c619822e1d31620f21850411fa12210a03c1f914b07e14913419118001617f00d17f47310009f06d16b06909c4b818c0bf0980fb09705e1e42fe1111981e212610e0490880440d31721830ee0d00ab07e02d0cc0a607701c0770040721cc1da0e419d2001bb2000621ff05f24715309305a1fe31e25b0b708d22108b22110d0b22431232431ec13703925811f0ce0aa07c02707902218001723f26010121b0c409e06b21a0fd1691561151790960bd1aa27b5c91b718720808a0490d520708620721321e07f03415e 1466296667 1473063576 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_97 (k : ℕ) (lo : 1473063576≤k) (hi : k<1479841486) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x7701b10400e0743b00c73b019e09d3011cb0fc09817a3ae0f809205850f1510d82fe18714f2152211850af1841ed1091ec07e02e10602410502010511c3130021a00a13120e406c0e406911717c0e10bf32912b1670ba09123b1fe0f50d81761fd12510d0b31fc0b11e00f01841ec0cf1d018202607901a0ca00107221c06f21c17d16b0ff27506709a2b91ca0601c905e0941f113e0560da1f01a804f18732e10c0b210c14d2430ad0802d810702f1a30250790212410a50c900f0c93b023f0e513011926a1ad0661420621411550950bb16635e0da05213c1b710e04a1861b60870434062201600ee15f4b65290240780173f800007316d44c0a00c411823e1cb1560990fc0980611c923c16705a1890f743820913b04a08904710c3880d30ae0810ee1c202c0cc24c0cb01a15b00d32324b1301cc1f51ae1bc1431bc09906218b0be18b12a0930ba0db0b708d05008c35c28414e2840af29717229703507d02f2961b12951481f700415a33a1593930fe3393f61e60be2473f511205825c 1473063576 1479841486 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_98 (k : ℕ) (lo : 1479841486≤k) (hi : k<1486643262) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x10b03d10a0380800ab1c202b07b0243ed21e07519126c1cd1db1af2551170fd6092692190bc21919a2180535890b413b04618624f1e01950810ac1df02f13602a13501c0760110c90001321471010a01db11906a24a1570e10fc0981bb16805c16712a1670ba16605716605413d0500d83c110d0470880b113903f27003b26f03615f0ec1de02810602210501e3630122570050723870c538623f18e06718d2a71ad23d14105d1e51780910b91e42675e604b08a04816204422d03b22c12122c03022b02b1060ea1dd01a1dd0060c80a31dc21d17e21c13009f12f0e31f511722616922627405b13f1290db15208f05108d04d2d21252d204308403f2d10382130301070282cf2050ca0120c90092a920410118f06e09e12e33a0c135919c0df19c21919a0920ba47329016417608b28f0d504638214d08303924319310702e10711e0cc1920780153b728b0710e623f1181bd34a17b16906311519b14023c0923c11641f008b0f318604627019513803c13803813719407f02e0cd02a0cd11d 1479841486 1486643262 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_99 (k : ℕ) (lo : 1486643262≤k) (hi : k<1493466430) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 256 0x2ad27b2e403310814b07c14a07a20607700b0743880700a11db1450ff11812e09b1f516a06216917b0df05e16817a51c4041891521100b613c44c0880451620400840ef08132f1080aa10702b1070270cc01f15d0143352a02960e606e0e51301cd0690e21f520206220126a29d05929c0561662910d81516010471863f63830370d00ee13702b07b0a910601d07701507511c1312e91db2e92552d60632e805f2e720d11305911205813f25208e04f0d82901e21d408723918503d08228e15f03015f02a2d00210cb0170ca0130ca00a5c419006f20415923406909c0c13b020e09720d32a1542190560da0532180f516404c2ae2221861241860b018503c0d10ee29803107c02407902207902007801e2420142413790c716d13021c0c421c0fe21b2df2751d827405c3fe0f713e27d08e20a10e04b10e0492e404410c04027014d13803613703307e02f0cd0251810130c900045a23506e23406c0e415838606729e0c016926a23205d29c1d73e40b811005213d0b508b04c1a814f13a1d3 1486643262 1493466430 (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem span_100 (k : ℕ) (lo : 1493466430≤k) (hi : k<1494800045) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  packed_interval trip 50 0x440d412408503f0840af08203607e02f07d02c07c02b1fa0211810162830000722ea0c611a10009e06b09e17d1443b820212c20105f2752de0dc1ba0910b808e04f2e604b08a0f32ae043 1493466430 1494800045 (by decide +kernel) k lo hi

omit trip in
private theorem span_join (a b c : ℕ)
    (left : ∀ k : ℕ, a≤k → k<b → ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2)
    (right : ∀ k : ℕ, b≤k → k<c → ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2)
    (k : ℕ) (lo : a≤k) (hi : k<c) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  by_cases cut : k<b
  · exact left k lo cut
  · exact right k (by omega) hi

theorem packed_multiplicity_two (k : ℕ) (lo : 20124≤k) (hi : k<1494800045) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  (span_join 20124 254204464 1494800045 (span_join 20124 9559102 254204464 (span_join 20124 2143534 9559102 (span_join 20124 440013 2143534 (span_join 20124 160973 440013 (span_join 20124 48475 160973 (span_0 trip) (span_join 48475 94275 160973 (span_1 trip) (span_2 trip))) (span_join 160973 227916 440013 (span_3 trip) (span_join 227916 343191 440013 (span_4 trip) (span_5 trip)))) (span_join 440013 1010363 2143534 (span_join 440013 549556 1010363 (span_6 trip) (span_join 549556 673163 1010363 (span_7 trip) (span_8 trip))) (span_join 1010363 1323913 2143534 (span_9 trip) (span_join 1323913 1697416 2143534 (span_10 trip) (span_11 trip))))) (span_join 2143534 5505687 9559102 (span_join 2143534 3438355 5505687 (span_join 2143534 2856020 3438355 (span_12 trip) (span_join 2856020 3142396 3438355 (span_13 trip) (span_14 trip))) (span_join 3438355 4212945 5505687 (span_15 trip) (span_join 4212945 5124273 5505687 (span_16 trip) (span_17 trip)))) (span_join 5505687 6739956 9559102 (span_join 5505687 5900924 6739956 (span_18 trip) (span_join 5900924 6311784 6739956 (span_19 trip) (span_20 trip))) (span_join 6739956 8551488 9559102 (span_join 6739956 8069221 8551488 (span_21 trip) (span_22 trip)) (span_join 8551488 9046780 9559102 (span_23 trip) (span_24 trip)))))) (span_join 9559102 39040632 254204464 (span_join 9559102 16111050 39040632 (span_join 9559102 14141037 16111050 (span_join 9559102 10086465 14141037 (span_25 trip) (span_join 10086465 10627130 14141037 (span_26 trip) (span_27 trip))) (span_join 14141037 14782001 16111050 (span_28 trip) (span_join 14782001 15438904 16111050 (span_29 trip) (span_30 trip)))) (span_join 16111050 22771547 39040632 (span_join 16111050 21179656 22771547 (span_31 trip) (span_join 21179656 21967731 22771547 (span_32 trip) (span_33 trip))) (span_join 22771547 23591538 39040632 (span_34 trip) (span_join 23591538 24426534 39040632 (span_35 trip) (span_36 trip))))) (span_join 39040632 51408775 254204464 (span_join 39040632 42322173 51408775 (span_join 39040632 40120221 42322173 (span_37 trip) (span_join 40120221 41216032 42322173 (span_38 trip) (span_39 trip))) (span_join 42322173 43444520 51408775 (span_40 trip) (span_join 43444520 44583672 51408775 (span_41 trip) (span_42 trip)))) (span_join 51408775 119018928 254204464 (span_join 51408775 52649213 119018928 (span_43 trip) (span_join 52649213 53912704 119018928 (span_44 trip) (span_45 trip))) (span_join 119018928 122838675 254204464 (span_join 119018928 120925921 122838675 (span_46 trip) (span_47 trip)) (span_join 122838675 140360219 254204464 (span_48 trip) (span_49 trip))))))) (span_join 254204464 589118597 1494800045 (span_join 254204464 389218922 589118597 (span_join 254204464 271191260 389218922 (span_join 254204464 262621704 271191260 (span_join 254204464 256992448 262621704 (span_50 trip) (span_join 256992448 259797497 262621704 (span_51 trip) (span_52 trip))) (span_join 262621704 265455361 271191260 (span_53 trip) (span_join 265455361 268315730 271191260 (span_54 trip) (span_55 trip)))) (span_join 271191260 279896264 389218922 (span_join 271191260 274080900 279896264 (span_56 trip) (span_join 274080900 276983038 279896264 (span_57 trip) (span_58 trip))) (span_join 279896264 282829027 389218922 (span_59 trip) (span_join 282829027 385766415 389218922 (span_60 trip) (span_61 trip))))) (span_join 389218922 559628233 589118597 (span_join 389218922 547222417 559628233 (span_join 389218922 392685922 547222417 (span_62 trip) (span_join 392685922 396169714 547222417 (span_63 trip) (span_64 trip))) (span_join 547222417 551342872 559628233 (span_65 trip) (span_join 551342872 555474375 559628233 (span_66 trip) (span_67 trip)))) (span_join 559628233 572185657 589118597 (span_join 559628233 563798341 572185657 (span_68 trip) (span_join 563798341 567986649 572185657 (span_69 trip) (span_70 trip))) (span_join 572185657 580631217 589118597 (span_join 572185657 576404116 580631217 (span_71 trip) (span_72 trip)) (span_join 580631217 584865565 589118597 (span_73 trip) (span_74 trip)))))) (span_join 589118597 1412682099 1494800045 (span_join 589118597 614996785 1412682099 (span_join 589118597 601992936 614996785 (span_join 589118597 593396104 601992936 (span_75 trip) (span_join 593396104 597689002 601992936 (span_76 trip) (span_77 trip))) (span_join 601992936 606317167 614996785 (span_78 trip) (span_join 606317167 610648697 614996785 (span_79 trip) (span_80 trip)))) (span_join 614996785 628148909 1412682099 (span_join 614996785 619364575 628148909 (span_81 trip) (span_join 619364575 623748978 628148909 (span_82 trip) (span_83 trip))) (span_join 628148909 896117606 1412682099 (span_join 628148909 632560155 896117606 (span_84 trip) (span_85 trip)) (span_join 896117606 901402974 1412682099 (span_86 trip) (span_87 trip))))) (span_join 1412682099 1452800282 1494800045 (span_join 1412682099 1432668451 1452800282 (span_join 1412682099 1419328010 1432668451 (span_88 trip) (span_join 1419328010 1425991333 1432668451 (span_89 trip) (span_90 trip))) (span_join 1432668451 1439358533 1452800282 (span_91 trip) (span_join 1439358533 1446072160 1452800282 (span_92 trip) (span_93 trip)))) (span_join 1452800282 1473063576 1494800045 (span_join 1452800282 1459542394 1473063576 (span_94 trip) (span_join 1459542394 1466296667 1473063576 (span_95 trip) (span_96 trip))) (span_join 1473063576 1486643262 1494800045 (span_join 1473063576 1479841486 1486643262 (span_97 trip) (span_98 trip)) (span_join 1486643262 1493466430 1494800045 (span_99 trip) (span_100 trip)))))))) k lo hi

end
end Bin304

namespace Bin304

/-- The finite interval has a prime of multiplicity exactly two at every
index other than 786; there the prime two has multiplicity four. -/
theorem prefix_multiplicity_two {k : ℕ} (lo : 784 < k) (hi : k ≤ 1494800044) (ne : k ≠ 786) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  by_cases cut : k<20124
  · exact small_multiplicity_two k lo cut ne
  · exact packed_multiplicity_two (@triplet_cover) k (by omega) (by omega)

theorem multiplicity_succ_dvd_card {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) (hpos : 0<n.factorization p) :
    n.factorization p + 1 ∣ n.divisors.card := by
  have hd : p ∣ n := by
    by_contra contra
    rw [Nat.factorization_eq_zero_of_not_dvd contra] at hpos
    omega
  rw [Nat.card_divisors hn]
  exact Finset.dvd_prod_of_mem _ (Nat.mem_primeFactors.mpr ⟨hp,hd,hn⟩)

theorem prefix_three_dvd {k : ℕ} (lo : 784 < k) (hi : k ≤ 1494800044) (ne : k ≠ 786) :
    3 ∣ k.centralBinom.divisors.card := by
  obtain ⟨p,hp,hv⟩ := prefix_multiplicity_two lo hi ne
  simpa only [hv] using multiplicity_succ_dvd_card (Nat.centralBinom_pos k).ne' hp (by omega)

theorem five_dvd_card_786 : 5 ∣ (Nat.centralBinom 786).divisors.card := by
  have hv := multiplicity_four_786
  simpa only [hv] using multiplicity_succ_dvd_card (Nat.centralBinom_pos 786).ne' Nat.prime_two (by omega)

end Bin304

/- The shared Lucas graph and binary modular-power verifier are adapted from
OMA proof OeisA245211.conjecture.R3.H1 by @connoranderson. -/
namespace Bin304

theorem prime_of_factorial_window (p w : ℕ) (hp : 1 < p) (size : p < (w+1)^2)
    (cop : p.gcd w.factorial = 1) : p.Prime := by
  by_contra hn
  have sq := Nat.minFac_sq_le_self (by omega : 0 < p) hn
  have prime := Nat.minFac_prime (by omega : p ≠ 1)
  have small : p.minFac ≤ w := by
    by_contra! contra
    have h := Nat.pow_le_pow_left (by omega : w+1 ≤ p.minFac) 2
    omega
  have h := Nat.dvd_gcd (Nat.minFac_dvd p) (Nat.dvd_factorial prime.pos small)
  rw [cop, Nat.dvd_one] at h
  exact prime.ne_one h

theorem bounded_pow_mod (p a k e : ℕ) (hk : e < 2^k) :
    (Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 1%p)
      (fun _ f t => (f (t/2)^2*(if t%2=0 then 1 else a))%p) k e) = a^e%p := by
  induction k generalizing e with
  | zero =>
    have : e=0 := by simpa using hk
    subst e
    simp
  | succ k ih =>
    have h : e/2 < 2^k := (Nat.div_lt_iff_lt_mul (by decide : 0<2)).mpr (by simpa [pow_succ] using hk)
    change ((_ : ℕ)^2*(if e%2=0 then 1 else a))%p = a^e%p
    rw [ih _ h]
    have he : e = e/2*2 + e%2 := by omega
    conv_rhs => rw [he,pow_add,pow_mul]
    have ha : (if e%2=0 then 1 else a) = a^(e%2) := by
      split <;> rename_i hbit
      · simp [hbit]
      · simp [show e%2=1 by omega]
    rw [ha]
    exact ((Nat.mod_modEq _ _).pow 2).mul_right _

/-- Each non-leaf row contains the candidate, a Lucas witness, and the
complete factorization of its predecessor. The strict decreases justify sharing. -/
theorem lucas_graph (rows : List (ℕ × ℕ × List ℕ)) :
    let pool := rows.map Prod.fst
    let power (p a e : ℕ) := Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 1%p)
      (fun _ f t => (f (t/2)^2*(if t%2=0 then 1 else a))%p) (p.log2+1) e
    let check (row : ℕ × ℕ × List ℕ) :=
      let (p,a,fs) := row
      if a=0 then
        if p ≤ 12 then decide p.Prime else
          let w := if p ≤ 142 then 12 else 142
          decide (1 < p ∧ p < (w+1)^2 ∧ p.gcd w.factorial = 1)
      else
        decide (1<p ∧ p < 2^(p.log2+1) ∧ fs.prod=p-1) &&
        (power p a (p-1) == 1) &&
        fs.eraseDups.all (fun q => q < p && pool.contains q && power p a ((p-1)/q) != 1)
    rows.all check = true → ∀ r ∈ pool, Nat.Prime r := by
  intro pool power check ok r
  induction r using Nat.strong_induction_on with
  | h p ih =>
    intro mem
    obtain ⟨⟨t,a,fs⟩,hr,ht⟩ := List.mem_map.mp mem
    change t=p at ht
    subst t
    have row := List.all_eq_true.mp ok _ hr
    change (if a=0 then _ else _) = true at row
    split at row
    · split at row
      · exact of_decide_eq_true row
      · obtain ⟨positive,bound,cop⟩ := of_decide_eq_true row
        exact prime_of_factorial_window _ _ positive bound cop
    · obtain ⟨h0, tests⟩ := Bool.and_eq_true_iff.mp row
      obtain ⟨bounds, full⟩ := Bool.and_eq_true_iff.mp h0
      obtain ⟨hp,limit,hprod⟩ := of_decide_eq_true bounds
      have child (q : ℕ) (hq : q ∈ fs) := List.all_eq_true.mp tests q (List.mem_eraseDups.mpr hq)
      have fact (q : ℕ) (hq : q ∈ fs) : q.Prime := by
        obtain ⟨both,_⟩ := Bool.and_eq_true_iff.mp (child q hq)
        obtain ⟨lt,known⟩ := Bool.and_eq_true_iff.mp both
        exact ih q (of_decide_eq_true lt) (List.contains_iff_mem.mp known)
      have bridge (e : ℕ) (he : e ≤ p) :
          (a : ZMod p)^e = 1 ↔ power p a e = 1 := by
        rw [← Nat.cast_pow, ← Nat.cast_one (R := ZMod p), ZMod.natCast_eq_natCast_iff']
        have calcPow : power p a e = a^e%p := bounded_pow_mod p a _ e (he.trans_lt limit)
        rw [calcPow, Nat.mod_eq_of_lt hp]
      apply lucas_primality p (a : ZMod p) ((bridge (p-1) (by omega)).mpr (beq_iff_eq.mp full))
      intro q hq hd
      have memq := (Nat.mem_primeFactorsList (by omega : p-1 ≠ 0)).mpr ⟨hq,hd⟩
      have hqf := (Nat.primeFactorsList_unique hprod fact).mem_iff.mpr memq
      have neq := (Bool.and_eq_true_iff.mp (child q hqf)).2
      intro contra
      have eq := (bridge ((p-1)/q) ((Nat.div_le_self _ _).trans (by omega))).mp contra
      simp [eq] at neq

private theorem list_sweep_sound (P : ℕ → Prop) (step : ℕ → ℕ → ℕ)
    (valid : ∀ x m k, x≤k → k<step x m → P k) (ms : List ℕ) (x k : ℕ)
    (lo : x≤k) (hi : k < ms.foldl step x) : P k := by
  induction ms generalizing x with
  | nil => change k<x at hi; omega
  | cons m ms ih =>
    by_cases left : k<step x m
    · exact valid x m k lo left
    · exact ih (step x m) (by omega) hi

/-- A Lucas-checked chain of overlapping triplet intervals certifies every
integer from the first endpoint through the last, inclusive. -/
theorem certified_cover (rows : List (ℕ × ℕ × List ℕ)) (ms : List ℕ) (lo hi : ℕ) :
    let pool := rows.map Prod.fst
    let power (p a e : ℕ) := Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => 1%p)
      (fun _ f t => (f (t/2)^2*(if t%2=0 then 1 else a))%p) (p.log2+1) e
    let check (row : ℕ × ℕ × List ℕ) :=
      let (p,a,fs) := row
      if a=0 then
        if p ≤ 12 then decide p.Prime else
          let w := if p ≤ 142 then 12 else 142
          decide (1 < p ∧ p < (w+1)^2 ∧ p.gcd w.factorial = 1)
      else
        decide (1<p ∧ p < 2^(p.log2+1) ∧ fs.prod=p-1) &&
        (power p a (p-1) == 1) &&
        fs.eraseDups.all (fun q => q < p && pool.contains q && power p a ((p-1)/q) != 1)
    let step (x m : ℕ) :=
      if decide (2 ≤ m ∧ 96*m^2-2*m ≤ x) && pool.contains (6*m+1) &&
          pool.contains (12*m-1) && pool.contains (12*m+1)
      then max x (108*m^2+3*m-1) else x
    rows.all check = true → hi < ms.foldl step lo →
    ∀ k : ℕ, lo≤k → k≤hi → ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  intro pool power check step primes cover k hlow hhigh
  have proven := lucas_graph rows primes
  apply list_sweep_sound _ step _ ms lo k hlow (hhigh.trans_lt cover)
  intro x m n nx stop
  dsimp only [step] at stop
  split at stop
  · rename_i good
    simp only [Bool.and_eq_true_iff] at good
    obtain ⟨⟨⟨both,p⟩,q⟩,r⟩ := good
    obtain ⟨hm,below⟩ := of_decide_eq_true both
    apply triplet_cover hm (proven _ (List.contains_iff_mem.mp p))
      (proven _ (List.contains_iff_mem.mp q)) (proven _ (List.contains_iff_mem.mp r)) (below.trans nx)
    omega
  · omega

end Bin304


namespace Bin304

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_0 (k : ℕ) (lo : 1494800044≤k) (hi : k≤8602834273) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,67,101,113,181,229,349,449,569,577,661,673,947,1021,1117,1217,1973,2383,2531,3677,3923,4397,4877,5431,5897]
  let factors : List (ℕ × ℕ × List ℕ) := [(5,2,[3,1973]),(5,3,[3,3,7,7,7]),(6,2,[3,3,5,11,13]),(6,1,[3,3,3,5,101]),(2,2,[3,2383]),(3,1,[3,3,5,7,47]),(2,2,[3,3,3,3,5,19]),(2,1,[3,5431]),(2,2,[3,5,569]),(3,1,[3,5,29,41]),(17,1,[3,7,19,47]),(5,3,[3,3,3,181]),(17,6,[3,5,43]),(2,1,[3,11,661]),(10,2,[3,3,5,11,23]),(13,1,[5,5,947]),(5,3,[3,1973]),(7,1,[3,5,7,229]),(11,1,[5,11,449]),(5,4,[3,3,7,7,7]),(7,3,[3,5,5,5,17]),(7,1,[7,3677]),(17,3,[3,3,5,11,13]),(2,2,[11,1217]),(3,1,[3,3,5,5,7,17]),(2,1,[11,37,67]),(2,2,[3,3,3,5,101]),(7,1,[5,7,19,43]),(5,3,[3,2383]),(2,1,[29,1021]),(2,2,[3,3,5,7,47]),(7,1,[7,4397]),(7,3,[3,3,3,3,5,19]),(2,1,[5,7,7,7,19]),(2,2,[3,5431]),(7,1,[7,4877]),(7,3,[3,5,569]),(2,1,[53,673]),(6,2,[3,5,29,41]),(6,1,[5,13,577]),(2,2,[3,7,19,47]),(11,1,[5,7,1117]),(5,4,[3,3,3,181]),(7,1,[7,5897]),(7,7,[3,5,43]),(2,1,[5,5,5,349]),(2,2,[3,11,661]),(7,1,[13,31,113]),(17,3,[3,3,5,11,23]),(2,1,[19,2531]),(6,2,[3,5,7,229]),(7,1,[13,3923]),(31,4,[3,5,5,5,17]),(2,1,[53549]),(6,2,[3,3,5,5,7,17])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [3946,4116,4290,4545,4766,4935,5130,5431,5690,5945,6251,6516,6880,7271,7590,8015,8500,8925] 1494800044 8602834273 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_1 (k : ℕ) (lo : 8602834274≤k) (hi : k≤60432445663) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,43,47,53,59,67,71,83,89,103,107,109,127,223,239,293,479,509,523,653,809,997,1423,1453,1879,1999,2089,2441,2459,2689,3191,3301,3457,3613,4751,5153,12197,13591]
  let factors : List (ℕ × ℕ × List ℕ) := [(13,1,[53,523]),(38,4,[3,3,5,7,11]),(11,1,[3,3,5,653]),(2,1,[3,7,1453]),(7,1,[3,3,5,23,31]),(2,2,[3,7,809]),(2,2,[3,5,11,109]),(6,1,[3,3,5,7,11,11]),(2,2,[7,43,67]),(3,1,[3,5,2689]),(6,2,[3,5,1423]),(3,1,[3,3,5,17,59]),(2,1,[3,5,3191]),(2,1,[3,3,3,1879]),(23,3,[3,5,7,127]),(13,1,[55439]),(69,5,[3,3,5,7,11]),(3,1,[3,3,3,2089]),(2,1,[17,3457]),(10,2,[3,3,5,653]),(15,6,[3,7,89]),(2,1,[5,5,2441]),(2,2,[3,7,1453]),(15,3,[3,11,479]),(2,1,[7,89,103]),(2,2,[3,3,5,23,31]),(2,1,[13,5153]),(6,2,[3,5,7,11,29]),(23,1,[5,13591]),(5,3,[3,7,809]),(2,1,[3,3,5,19,83]),(7,1,[7,43,239]),(7,3,[3,5,11,109]),(2,1,[31,2459]),(6,2,[3,3,5,7,11,11]),(2,1,[80669]),(2,2,[3,5,2689]),(7,1,[7,12197]),(14,3,[3,5,1423]),(2,1,[19,4751]),(10,2,[3,3,5,17,59]),(2,1,[29,3301]),(2,2,[3,5,3191]),(6,1,[5,7,13,223]),(2,2,[3,3,3,1879]),(11,1,[107,997]),(17,4,[3,5,7,127]),(2,1,[5,7,11,293]),(5,2,[3,3,3,2089]),(11,1,[5,47,509]),(5,7,[3,7,89]),(14,1,[5,7,3613]),(5,4,[3,11,479]),(17,1,[133979]),(17,3,[3,5,7,11,29]),(2,1,[71,1999]),(6,2,[3,3,5,19,83])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [9240,9795,10171,10695,11326,11990,12705,13445,14230,15045,15955,16911,17780,18801,19936,21076,22330,23655] 8602834274 60432445663 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_2 (k : ℕ) (lo : 60432445664≤k) (hi : k≤433907278453) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,67,73,83,89,103,107,109,151,197,199,227,229,271,373,401,491,541,593,797,823,1439,1447,1451,1601,1811,3067,3821,7643,11329,11731]
  let factors : List (ℕ × ℕ × List ℕ) := [(2,1,[3,3,11,107]),(5,1,[31,593]),(5,3,[3,3,541]),(3,1,[3,5,1447]),(5,2,[3,3821]),(6,1,[3,5,43,47]),(3,1,[3,3,17,491]),(7,6,[3,823]),(2,2,[3,3,3,3,5,103]),(7,3,[3,5,1451]),(2,2,[3,67,229]),(3,1,[3,11,13,227]),(3,1,[3,43,797]),(10,5,[3,7,17,19]),(3,1,[3,3,47,271]),(2,1,[3,3,5,37,73]),(2,1,[3,5,23,373]),(7,3,[3,11329]),(13,4,[3,7,23,37]),(2,1,[5,151,199]),(2,2,[3,3,17,491]),(2,2,[3,3,3,7,401]),(14,1,[5,11,13,13,17]),(5,7,[3,823]),(3,1,[3,7,7643]),(11,1,[7,11,11,197]),(13,3,[3,3,3,3,5,103]),(17,3,[3,3,3,3,3,5,5,7]),(11,1,[11,11,1439]),(7,4,[3,5,1451]),(7,2,[3,3,3,5,23,29]),(17,1,[5,23,1601]),(5,3,[3,67,229]),(2,2,[31,3067]),(3,1,[3,5,7,1811]),(6,1,[5,38953]),(2,2,[3,11,13,227]),(2,1,[5,5,5,5,7,47]),(2,2,[3,43,797]),(13,1,[5,43411]),(5,6,[3,7,17,19]),(2,1,[5,45853]),(5,2,[3,3,47,271]),(2,1,[7,7,11,11,41]),(6,2,[3,3,5,37,73]),(2,1,[7,36767]),(6,2,[3,5,23,373]),(17,1,[5,13,47,89]),(5,4,[3,11329]),(11,1,[5,13,53,83]),(5,5,[3,7,23,37]),(17,1,[5,60631]),(5,3,[3,3,3,7,401]),(6,1,[5,19,31,109]),(5,2,[3,7,7643]),(11,1,[29,11731]),(11,4,[3,3,3,3,3,5,5,7]),(37,1,[17,21187]),(7,3,[3,3,3,5,23,29]),(2,1,[380309]),(2,2,[3,5,7,1811])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [25041,26336,27810,29020,30686,32461,34271,36176,38211,40515,42895,45316,47656,50526,53501,56700,60030,63385] 60432445664 433907278453 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_3 (k : ℕ) (lo : 433907278454≤k) (hi : k≤3470140005859) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,47,53,59,61,71,79,97,109,131,137,163,179,191,211,271,313,317,353,379,487,499,563,827,863,937,1327,1567,2269,2381,3037,6389,9733,10733,12653,12893,12923,13553,16871,19163]
  let factors : List (ℕ × ℕ × List ℕ) := [(2,1,[10733]),(5,3,[3,29,31]),(5,1,[12923]),(10,4,[3,17,41]),(2,2,[9733]),(3,1,[3,12893]),(22,4,[3,5,5,71]),(2,1,[5,59,191]),(11,3,[3,19,353]),(3,1,[3,3,5,5,5,179]),(5,1,[3,3,3,7,7,7,23]),(5,1,[3,3,29,863]),(7,3,[3,3,5,1327]),(2,1,[3,5,16871]),(6,2,[3,7,6389]),(6,2,[3,3,97,163]),(2,1,[3,3,33457]),(2,1,[3,5,7,3037]),(14,1,[3,112691]),(13,3,[3,53,563]),(3,3,[7,13553]),(3,1,[3,3,3,3,5,937]),(3,1,[3,7,19163]),(2,1,[487,827]),(2,2,[3,3,5,5,5,179]),(6,1,[3,3,5,5,31,61]),(2,1,[5,85201]),(11,2,[3,3,3,7,7,7,23]),(2,1,[5,7,61,211]),(5,2,[3,3,29,863]),(7,8,[3,5,5,47]),(11,1,[11,137,317]),(23,4,[3,3,5,1327]),(6,2,[3,3,3,5,7,11,23]),(2,1,[13,38933]),(10,2,[3,5,16871]),(28,3,[3,3,3,3,5,313]),(13,1,[5,5,21467]),(5,3,[3,7,6389]),(2,1,[3,79,2269]),(7,1,[5,11,79,131]),(5,3,[3,3,97,163]),(2,1,[5,5,13,17,109]),(5,2,[3,3,33457]),(10,1,[11,37,1567]),(6,2,[3,5,7,3037]),(10,1,[5,271,499]),(2,2,[3,112691]),(7,1,[5,7,7,37,79]),(7,4,[3,53,563]),(2,1,[758969]),(2,2,[3,3,3,3,5,937]),(2,1,[5,160969]),(2,2,[3,7,19163]),(2,1,[11,77359]),(2,2,[3,3,5,5,31,61]),(17,1,[379,2381]),(14,9,[3,5,5,47]),(13,1,[37,25847]),(17,3,[3,3,3,5,7,11,23]),(11,1,[47,21577]),(14,4,[3,3,3,3,5,313]),(6,1,[5,17,12653]),(2,2,[3,79,2269])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [67125,71001,75081,79620,84355,89446,94866,100371,106295,112691,119356,126495,134141,141825,150400,159390,169020,179251] 433907278454 3470140005859 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_4 (k : ℕ) (lo : 3470140005860≤k) (hi : k≤28400207023309) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,23,29,31,37,43,47,53,59,61,67,73,83,107,113,163,173,193,233,239,283,293,383,401,431,509,613,809,823,911,1117,1181,1307,1489,1607,1657,1663,1933,2543,2657,3041,3557,4013,5431,10687,10691,19069]
  let factors : List (ℕ × ℕ × List ℕ) := [(5,1,[10691]),(5,4,[3,3,163]),(3,3,[3041]),(3,1,[3,3,1607]),(5,1,[21383]),(3,1,[3,7,13,83]),(2,2,[53,383]),(2,1,[3,3,7,823]),(2,1,[193,401]),(3,3,[7,13,239]),(2,1,[5,59,431]),(7,2,[3,5,5,29,31]),(13,3,[3,3,5,29,31]),(5,1,[3,3,19069]),(2,1,[173993]),(2,1,[3,5,47,809]),(3,4,[83,911]),(3,1,[3,5,7,7,823]),(2,1,[3,5,42767]),(3,1,[3,5,45319]),(3,1,[3,3,3,5,73,73]),(2,1,[3,254291]),(3,1,[3,269701]),(7,3,[3,43,1663]),(3,1,[3,3,61,1657]),(5,6,[3,11,11,83]),(6,2,[3,7,24329]),(2,1,[7,154787]),(6,2,[3,3,3,5,4013]),(2,1,[11,103699]),(6,2,[3,5,47,809]),(2,1,[3,293,1307]),(2,1,[1209809]),(10,2,[3,5,7,7,823]),(3,1,[3,5,81197]),(2,1,[7,13,23,613]),(6,2,[3,5,42767]),(2,1,[3,3,3,3,3,47,113]),(6,1,[47,28927]),(7,2,[3,5,45319]),(22,2,[3,193,1181]),(2,1,[7,17,107,113]),(10,2,[3,3,3,5,73,73]),(2,1,[3,5,5,83,233]),(6,1,[5,13,23473]),(2,2,[3,254291]),(3,1,[3,193,2657]),(2,1,[5,323641]),(2,2,[3,269701]),(7,1,[5,343243]),(15,4,[3,43,1663]),(2,1,[5,67,5431]),(2,2,[3,3,61,1657]),(7,1,[5,7,37,1489]),(7,7,[3,11,11,83]),(11,1,[5,11,73,509]),(5,3,[3,7,24329]),(13,1,[2167019]),(7,3,[3,3,3,5,4013]),(2,1,[5,43,10687]),(2,2,[3,293,1307]),(2,1,[7,347987]),(7,2,[3,5,81197]),(2,1,[5,7,29,2543]),(6,2,[3,3,3,3,3,47,113]),(11,1,[5,283,1933]),(7,3,[3,193,1181]),(2,1,[7,7,53,1117]),(6,2,[3,5,5,83,233]),(2,1,[5,173,3557]),(13,2,[3,193,2657])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [190115,201635,213835,226595,239805,254291,269701,286036,303231,321376,340606,361170,382951,405985,430191,455866,483475,512801] 3470140005860 28400207023309 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_5 (k : ℕ) (lo : 28400207023310≤k) (hi : k≤234868748802868) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,31,37,41,53,59,61,67,71,101,103,107,109,127,131,137,139,157,179,181,227,263,269,271,277,293,311,379,401,421,457,503,839,853,863,997,1063,1549,1663,2281,2417,3511,3701,6421,6793,10271,15541,16843,19571]
  let factors : List (ℕ × ℕ × List ℕ) := [(2,1,[3,3511]),(3,1,[3,3,5,263]),(3,1,[3,17,311]),(3,1,[3,3,7,401]),(2,1,[3,7,7,227]),(6,5,[5,11,41]),(2,2,[3,7,11,107]),(2,2,[13,23,137]),(3,3,[7,3701]),(3,1,[3,11,17,271]),(7,4,[3,3,59,103]),(11,3,[3,3,3,5,853]),(6,1,[3,163853]),(5,1,[3,3,109,1663]),(5,6,[3,67,269]),(3,1,[3,11,23,2417]),(2,2,[3,5,61,1063]),(10,3,[3,3,37,1549]),(3,1,[3,71,10271]),(13,4,[3,5,139,139]),(2,2,[3,7,139,421]),(3,1,[3,11,157,503]),(5,1,[3,921241]),(13,3,[3,5,7,7,997]),(2,2,[7,7,31723]),(3,1,[3,5,207257]),(2,1,[5,7,13,71,101]),(6,2,[3,3,109,1663]),(2,2,[3,5,131,839]),(7,1,[5,7,98869]),(5,7,[3,67,269]),(2,1,[3,3,5,5,15541]),(2,1,[5,31,23671]),(17,2,[3,11,23,2417]),(3,1,[3,5,7,11,13,13,19]),(7,1,[7,11,50527]),(14,3,[3,5,61,1063]),(3,1,[3,3,5,5,7,11,227]),(7,1,[5,7,7,16843]),(5,4,[3,3,37,1549]),(11,3,[3,7,17,23,127]),(2,1,[5,875089]),(2,2,[3,71,10271]),(2,1,[13,53,6421]),(6,2,[3,5,7,21067]),(11,1,[11,17,137,181]),(13,5,[3,5,139,139]),(13,1,[5,983119]),(10,3,[3,7,139,421]),(2,1,[5,457,2281]),(13,2,[3,11,157,503]),(2,1,[5,7,7,7,11,293]),(2,2,[3,921241]),(13,1,[863,6793]),(23,4,[3,5,7,7,997]),(2,1,[6217709]),(2,2,[3,5,207257]),(7,1,[7,19,179,277]),(19,3,[3,5,131,839]),(2,1,[23,304063]),(2,2,[3,3,5,5,15541]),(2,1,[379,19571]),(22,2,[3,5,7,11,13,13,19]),(2,1,[109,72161]),(19,2,[3,3,5,5,7,11,227]),(13,1,[5,5,5,66739]),(11,4,[3,7,17,23,127]),(17,1,[8848139]),(13,3,[3,5,7,21067])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [543801,576736,611501,648430,687756,729241,772840,819266,868681,921241,977060,1036285,1099090,1165575,1236235,1310925,1390396,1474690] 28400207023310 234868748802868 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_6 (k : ℕ) (lo : 234868748802869≤k) (hi : k≤1950498488857384) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,43,47,53,59,61,67,71,73,79,83,89,97,101,127,131,157,167,179,193,197,199,233,251,337,353,383,401,409,421,467,509,571,601,727,811,983,1049,1217,1373,1471,1619,1669,1987,2011,2069,3623,5569,5651,8233,9127,10453,12781,13339]
  let factors : List (ℕ × ℕ × List ℕ) := [(11,1,[3,3,17,97]),(2,2,[8233]),(3,3,[73,89]),(3,2,[5,5,601]),(2,1,[32933]),(2,2,[11,19,83]),(3,1,[3,11,1373]),(3,1,[3,17,23,61]),(5,1,[3,23,1619]),(2,2,[3,29683]),(13,1,[23,10453]),(2,1,[3,3,3,5,5,17,23]),(5,5,[3,9127]),(11,1,[480839]),(34,3,[3,3,3,5,29,67]),(14,4,[3,3,3,3,29,67]),(2,2,[11,69389]),(3,1,[3,7,223423]),(13,3,[3,5,197,421]),(2,2,[467,5651]),(3,1,[3,5,7,7,43,167]),(15,4,[3,3,7,29,383]),(15,1,[3,3,3,5,7,11,571]),(6,1,[3,2098441]),(5,3,[3,3,31,31,193]),(6,2,[3,7,101,1669]),(2,2,[3,19,65867]),(3,1,[3,199,13339]),(3,1,[3,7,17,59,401]),(14,2,[3,5,7,29,1471]),(10,1,[5,337,5569]),(2,2,[3,7,223423]),(2,2,[3,3,527851]),(7,1,[7,7,101,2011]),(11,4,[3,5,197,421]),(17,3,[3,3,5,7,11,727]),(2,1,[10556069]),(2,2,[3,5,7,7,43,167]),(10,2,[3,5,356197]),(11,1,[5,11,251,811]),(5,5,[3,3,7,29,383]),(7,1,[3,5,7,13,19,19,23]),(2,1,[131,90619]),(6,2,[3,3,3,5,7,11,571]),(13,3,[3,7,143107]),(2,1,[5,2518129]),(2,2,[3,2098441]),(2,2,[3,13,79,2069]),(11,1,[5,11,13,19,983]),(5,4,[3,3,31,31,193]),(11,1,[5,13,179,1217]),(5,3,[3,7,101,1669]),(11,1,[5,5,47,12781]),(5,3,[3,19,65867]),(2,1,[5,53,60101]),(6,2,[3,199,13339]),(2,1,[5,5,13,51977]),(2,2,[3,7,17,59,401]),(11,1,[71,127,1987]),(37,3,[3,5,7,29,1471]),(13,1,[5,1049,3623]),(5,3,[3,3,527851]),(23,1,[23,876193]),(13,4,[3,3,5,7,11,727]),(7,1,[7,3053117]),(11,3,[3,5,356197]),(2,1,[157,353,409]),(6,2,[3,5,7,13,19,19,23]),(11,1,[5,5,961679]),(13,4,[3,7,143107]),(29,1,[5,43,233,509]),(10,3,[3,13,79,2069])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [1563961,1658740,1759345,1865976,1978515,2098441,2225676,2359966,2502946,2654461,2815421,2986130,3167106,3358740,3561970,3777865,4006996,4249726] 234868748802869 1950498488857384 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_7 (k : ℕ) (lo : 1950498488857385≤k) (hi : k≤16229873735087374) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,47,53,79,83,97,101,109,113,131,163,181,193,223,233,269,277,281,397,419,421,463,467,491,521,659,757,887,1019,1097,1181,1303,1433,1699,1747,1801,1949,1973,2683,2711,2939,3079,4159,5167,5869,7879,13627,14479,15497,19483]
  let factors : List (ℕ × ℕ × List ℕ) := [(2,2,[5,1433]),(2,2,[97,109]),(19,1,[5,5,887]),(10,2,[3,5869]),(2,2,[3,7,1303]),(2,1,[5,5,17,193]),(26,1,[3,53,659]),(3,4,[7,7,7,7,7]),(3,4,[7,2683]),(2,2,[13,13,463]),(5,1,[164051]),(11,3,[3,15497]),(2,1,[3,3,113,277]),(29,3,[3,3,11,11,79]),(2,1,[13,28661]),(3,6,[7,1699]),(7,7,[3,5,5,83]),(7,3,[5,23,1019]),(3,1,[3,5,29,1181]),(7,3,[3,47,1097]),(3,1,[3,163,1801]),(3,1,[3,3,300497]),(23,1,[5,1027471]),(2,2,[3,491,1973]),(5,7,[3,70429]),(2,2,[3,3,796801]),(2,1,[3,3,3,563419]),(29,3,[3,5,268913]),(5,3,[3,181,7879]),(5,6,[3,97,1949]),(5,3,[3,521,3079]),(26,3,[3,5,5,11,23,269]),(2,2,[3,11,328103]),(3,1,[3,5,521,2939]),(2,2,[3,5,5,13,13,31,31]),(2,2,[3,13,17,19483]),(7,1,[5,5408947]),(5,8,[3,70429]),(7,3,[3,3,761153]),(13,1,[5,421,13627]),(15,3,[3,3,796801]),(3,1,[3,13,745187]),(6,1,[5,5,5,7,11,29,109]),(2,2,[3,3,3,563419]),(2,1,[3,10274711]),(7,1,[7,109,42293]),(7,4,[3,5,268913]),(5,3,[3,13,209563]),(11,1,[5,5,5,101,2711]),(5,4,[3,181,7879]),(5,1,[3,7,397,4159]),(7,1,[5,5,281,5167]),(10,7,[3,97,1949]),(10,5,[3,7,109453]),(7,1,[5,17,23,47,419]),(5,4,[3,521,3079]),(7,1,[7,7,37,101,223]),(7,4,[3,5,5,11,23,269]),(7,1,[5,7,1237417]),(5,3,[3,11,328103]),(2,1,[7,7,937481]),(2,2,[3,5,521,2939]),(7,1,[131,371929]),(17,3,[3,5,5,13,13,31,31]),(7,1,[5,233,44351]),(15,3,[3,13,17,19483]),(17,1,[5,757,14479]),(5,4,[3,3,761153]),(2,1,[5,11624917]),(2,2,[3,13,745187]),(2,1,[5,7,1761379]),(2,2,[3,10274711]),(19,1,[5,19,688249]),(11,4,[3,13,209563]),(2,1,[5,17,467,1747]),(5,2,[3,7,397,4159]),(17,1,[5,47,312989]),(11,6,[3,7,109453])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [4507456,4780806,5070771,5378260,5704396,6049696,6416636,6805700,7218266,7656095,8120450,8611486,9133836,9687431,10274711,10897276,11557861,12258736] 1950498488857385 16229873735087374 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_8 (k : ℕ) (lo : 16229873735087375≤k) (hi : k≤134982947321560804) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,89,97,101,103,109,127,149,151,163,173,211,269,311,379,443,449,457,499,503,509,683,863,953,967,1031,1087,1097,1129,1229,1447,1759,1847,2693,2707,2711,3209,3499,3947,4663,4733,4909,7349,7541,7823,13187,14087,19037]
  let factors : List (ℕ × ℕ × List ℕ) := [(3,4,[5,269]),(3,1,[3,43,89]),(11,1,[41,379]),(3,1,[3,11,503]),(3,4,[5,5,103]),(3,1,[3,3,2711]),(6,1,[13,2693]),(3,4,[37,151]),(2,1,[3,3,3,3,953]),(3,3,[23,1087]),(2,1,[5,17,1229]),(3,1,[3,3,11,1097]),(5,2,[3,47,443]),(2,1,[3,5,5,1847]),(2,1,[29,4909]),(2,2,[31,4663]),(15,1,[3,13,7541]),(2,1,[11,23,23,67]),(2,2,[588199]),(3,3,[11,61,457]),(13,3,[3,3,3,5,11,211]),(11,1,[5,73,3499]),(3,1,[3,19,33199]),(7,1,[5,43,47,311]),(2,2,[3,578213]),(5,3,[3,509,1447]),(3,1,[3,6285311]),(2,1,[3,683,19037]),(2,2,[3,3,11,208931]),(2,2,[3,3,173,14087]),(3,1,[3,499,31079]),(5,5,[3,7,17,53,163]),(3,1,[3,3,3,3,7,7,13187]),(2,1,[3,3,3,23,89393]),(5,4,[3,2453177]),(2,1,[3,3,6938557]),(3,1,[3,11,13,154387]),(2,1,[3,3,17,97,4733]),(3,1,[3,71,109,3209]),(2,1,[5,5,5,29,21521]),(5,2,[3,683,19037]),(3,1,[3,7,13,37,7823]),(23,1,[5,5,7,31,101,151]),(5,3,[3,3,11,208931]),(7,4,[3,3,1031,1129]),(7,1,[5,7,2506681]),(5,3,[3,3,173,14087]),(2,2,[3,19,779747]),(2,1,[5,5,23,41,3947]),(5,2,[3,499,31079]),(5,3,[3,7,23,48799]),(11,1,[5,79,249853]),(5,6,[3,7,17,53,163]),(2,1,[3,7,1759,2707]),(6,1,[5,13,23,70019]),(2,2,[3,3,3,3,7,7,13187]),(5,2,[3,17676553]),(6,1,[5,967,22963]),(5,2,[3,3,3,23,89393]),(7,1,[5,7,59,127,449]),(7,5,[3,2453177]),(2,1,[5,5,23,217207]),(2,2,[3,3,6938557]),(7,1,[5,7,3784687]),(2,2,[3,11,13,154387]),(2,1,[5,11,2554271]),(2,2,[3,3,17,97,4733]),(6,1,[5,149,200009]),(2,2,[3,71,109,3209]),(2,1,[5,11,17,23,7349]),(5,2,[3,7,13,37,7823]),(17,1,[5,11,11,277051]),(7,5,[3,3,1031,1129]),(11,1,[5,863,41201]),(10,3,[3,19,779747]),(13,1,[5,37711867]),(5,4,[3,7,23,48799]),(6,1,[5,17,2352797]),(2,2,[3,7,1759,2707]),(17,1,[5,149,284723]),(7,3,[3,17676553])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [13002271,13789446,14622306,15508421,16448656,17446401,18504351,19625416,20815671,22077341,23414151,24834451,26340041,27935976,29630386,31426556,33331291,35353106] 16229873735087375 134982947321560804 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_9 (k : ℕ) (lo : 134982947321560805≤k) (hi : k≤1123735244629542424) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,41,43,47,59,61,67,71,97,101,103,107,127,139,157,167,173,197,229,271,281,283,293,379,409,419,431,463,499,557,593,601,647,751,821,983,1033,1279,1543,1657,2081,2129,2381,3761,4273,5413,6151,7247,9103,9341,10267,11821,11953,15901,18089]
  let factors : List (ℕ × ℕ × List ℕ) := [(2,2,[5,11,97]),(3,4,[1657]),(2,1,[31,431]),(3,3,[3761]),(6,1,[3,5413]),(5,4,[3,7,101]),(2,1,[21341]),(2,1,[3,3,5,557]),(2,1,[3,3,3,17,59]),(2,2,[31,463]),(5,3,[3,3,1033]),(5,1,[7,13,593]),(2,2,[103,271]),(2,1,[57413]),(2,2,[32479]),(6,1,[13,17,409]),(5,1,[197,463]),(2,2,[54163]),(13,4,[3,3,5,7,47]),(3,7,[13,173]),(23,1,[3,3,3,5,7,167]),(2,1,[287873]),(2,2,[19,61,127]),(6,1,[3,216653]),(3,3,[180779]),(2,2,[5,129917]),(3,1,[3,3,7,11,2081]),(5,1,[13,114827]),(2,2,[3,5,5,26513]),(3,5,[5,71,821]),(5,3,[3,47,10267]),(17,4,[3,5,13,31,127]),(7,3,[3,575747]),(2,2,[557,18089]),(3,1,[3,7953901]),(6,1,[3,5,17,111653]),(2,1,[3,13,2884267]),(6,2,[3,3,3,7,315631]),(5,3,[3,43,103,2381]),(11,3,[3,59,293,647]),(5,2,[3,11,29,74377]),(2,1,[3,7,13,23,139,173]),(3,1,[3,11,11,13,33937]),(3,1,[3,13,601,7247]),(5,2,[3,3,17,588773]),(2,1,[3,7,7,1299919]),(2,2,[3,13,2598341]),(2,2,[3,11,61,107,499]),(2,1,[5,5,7,11,19,6151]),(6,2,[3,13,2884267]),(5,3,[3,379,50131]),(13,1,[5,47723407]),(5,3,[3,3,3,7,315631]),(5,2,[3,40302293]),(13,1,[5,5,7,1446233]),(5,4,[3,43,103,2381]),(5,3,[3,17,983,1279]),(7,1,[5,7,7,41,26723]),(5,4,[3,59,293,647]),(2,2,[3,13,97,157,229]),(7,1,[5,56943031]),(5,3,[3,11,29,74377]),(2,2,[3,7,29,236881]),(2,1,[5,5,283,42683]),(5,2,[3,7,13,23,139,173]),(14,2,[3,3,3,7,43,67,281]),(2,1,[5,2129,30089]),(2,2,[3,11,11,13,33937]),(2,1,[5,4273,15901]),(2,2,[3,13,601,7247]),(13,1,[5,5,1543,9341]),(5,3,[3,3,17,588773]),(2,1,[5,419,182423]),(2,2,[3,7,7,1299919]),(28,1,[5,7,11581177]),(10,3,[3,13,2598341]),(14,1,[5,7,12283441]),(5,3,[3,11,61,107,499]),(14,1,[5,5,13,13,107927]),(5,4,[3,379,50131]),(7,1,[5,7,13817929]),(5,3,[3,40302293]),(11,1,[5,11,9326561]),(5,4,[3,17,983,1279]),(11,1,[5,9103,11953]),(10,3,[3,13,97,157,229]),(11,1,[5,13,751,11821]),(10,3,[3,7,29,236881]),(17,1,[5,41,2985503]),(5,3,[3,3,3,7,43,67,281])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [37495471,39769506,42181796,44738756,47452526,50330371,53382901,56620811,60054846,63696031,67556866,71653406,75998596,80604586,85493476,90673466,96173686,102004686] 134982947321560805 1123735244629542424 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_10 (k : ℕ) (lo : 1123735244629542425≤k) (hi : k≤9359571870991978414) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,31,37,41,43,53,59,67,79,83,89,97,101,107,109,113,131,157,163,167,181,241,263,281,283,337,389,449,467,503,593,599,709,757,877,883,1097,1327,1619,2111,2153,2477,2663,2957,3083,3491,3923,4211,4889,4969,5659,6607,6967,7669,7841,11789,13487,15241,18797]
  let factors : List (ℕ × ℕ × List ℕ) := [(2,2,[3,5,5,97]),(3,5,[7,11,19]),(2,2,[23,599]),(3,1,[3,31,337]),(2,2,[17,1097]),(2,1,[3,3,4969]),(3,5,[43,101]),(7,2,[3,5,2957]),(2,2,[3,15241]),(5,3,[3,11,709]),(2,2,[13,37,109]),(5,1,[13,13487]),(13,7,[3,1327]),(7,1,[7,55109]),(6,2,[3,7,7,2111]),(15,1,[3,3,5,41,467]),(2,1,[3,11,11,2663]),(6,2,[3,5,7,6967]),(7,1,[3,7,181,449]),(5,1,[41,62683]),(3,5,[7,59,883]),(2,2,[3413299]),(11,2,[3,89,113,163]),(2,1,[7,19,138977]),(7,5,[3,3,31,4211]),(14,1,[7,7,41,59,281]),(3,1,[3,3,19,509569]),(5,2,[3,17,17,187177]),(10,4,[3,13,167,6607]),(2,2,[3,7,7,7,177421]),(15,4,[3,13,1241269]),(2,2,[3,79,113,7669]),(13,2,[3,7,41,503,503]),(5,2,[3,3,11,757,3083]),(19,2,[3,7,11669729]),(2,2,[3,7,19,263,2477]),(6,2,[3,4889,18797]),(5,4,[3,3,7,19,157,389]),(5,3,[3,67,771527]),(7,1,[5,41,67,167,283]),(5,3,[3,17,17,187177]),(2,2,[3,3,3,2153,5659]),(7,1,[5,7,19671493]),(10,5,[3,13,167,6607]),(11,2,[3,7,13,163,7841]),(29,1,[5,17,23,107,3491]),(13,3,[3,7,7,7,177421]),(10,5,[3,3,5140007]),(11,1,[5,7,11,11,182893]),(15,5,[3,13,1241269]),(5,3,[3,877,74597]),(7,1,[5,11,167,89443]),(5,3,[3,79,113,7669]),(5,6,[3,3,11,67,3923]),(13,1,[5,174272599]),(5,3,[3,7,41,503,503]),(5,5,[3,3,131,46817]),(7,1,[5,5,36967883]),(13,3,[3,3,11,757,3083]),(11,1,[5,67,2926141]),(5,3,[3,7,11669729]),(17,1,[5,593,350663]),(31,3,[3,7,19,263,2477]),(11,1,[5,11,13,53,29101]),(7,3,[3,4889,18797]),(11,1,[5,11,11,1933339]),(5,5,[3,3,7,19,157,389]),(7,1,[5,13,1619,11789]),(10,4,[3,67,771527]),(13,1,[5,7,37595809]),(5,3,[3,3,3,2153,5659]),(22,1,[5,11,11,11,209717]),(10,3,[3,7,13,163,7841]),(11,1,[5,19,19,41,83,241]),(5,6,[3,3,5140007]),(11,1,[5,23,13653197]),(13,4,[3,877,74597]),(14,1,[5,5,66614423]),(5,7,[3,3,11,67,3923]),(7,1,[5,5,41,1723231]),(5,6,[3,3,131,46817])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [108188306,114750376,121710806,129091976,136922326,145227166,154032846,163376206,173285966,183797066,194945016,206769236,219308886,232611106,246720336,261686276,277560096,294385296] 1123735244629542425 9359571870991978414 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_11 (k : ℕ) (lo : 9359571870991978415≤k) (hi : k≤77923389811670798974) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,53,59,61,67,79,83,101,103,109,151,211,227,239,293,359,379,383,419,461,503,521,547,593,641,859,919,1249,1297,1483,1511,1543,1697,1913,2143,2381,2999,3391,4651,5171,5477,5519,5827,6043,6089,6763,9103,10193,10289,12641,13003,13381,13691,14851,17011]
  let factors : List (ℕ × ℕ × List ℕ) := [(2,2,[3,3391]),(5,5,[3,461]),(3,5,[1511]),(2,2,[3,3,3,521]),(3,1,[3,13381]),(2,1,[3,7,1913]),(2,2,[53,503]),(17,2,[3,5,5,5,103]),(2,2,[3,7,17,109]),(6,1,[3,3,13691]),(7,3,[3,13003]),(2,2,[151,547]),(6,2,[3,40693]),(11,6,[3,5,5,5,23]),(13,3,[3,5,4651]),(2,1,[5,56269]),(2,2,[29,5477]),(6,1,[3,154501]),(2,1,[3,7,13,2381]),(2,2,[488317]),(14,4,[3,3,11,1297]),(6,2,[3,5,5,5,5,293]),(2,2,[3,3,13,59,211]),(5,2,[3,562691]),(3,1,[3,3,5,80287]),(10,3,[3,3,7,41,359]),(5,1,[859,6089]),(3,11,[12641]),(2,2,[3,3,3,3,3,7,7,1697]),(7,4,[3,3,3,37,5827]),(2,2,[3,3,19,359,593]),(2,1,[3,17,83,44257]),(3,1,[3,3,5,5,5,31,6043]),(7,5,[3,3,61,106637]),(10,3,[3,7,2143,5519]),(10,6,[3,17,23,67,419]),(10,3,[3,93138769]),(11,3,[3,3,3,227,48353]),(5,3,[3,3,17,2054449]),(5,3,[3,7,1543,10289]),(5,3,[3,3,83,379,1249]),(5,8,[3,7,558121]),(11,4,[3,3,17,1300027]),(5,9,[3,2197501]),(5,4,[3,239,312073]),(17,1,[5,374679763]),(7,6,[3,3,61,106637]),(5,3,[3,3,3,3,3,1953269]),(19,1,[5,13,2999,10193]),(5,4,[3,7,2143,5519]),(5,3,[3,3,3,3,919,6763]),(7,1,[5,421499251]),(11,7,[3,17,23,67,419]),(5,9,[3,3,927007]),(13,1,[5,41,641,17011]),(5,4,[3,93138769]),(10,4,[3,383,246439]),(17,1,[5,859,552001]),(5,4,[3,3,3,227,48353]),(5,4,[3,3,101,330389]),(19,1,[5,5,13,521,14851]),(5,4,[3,3,17,2054449]),(5,8,[3,3,3,3,3,3,3,9103]),(11,1,[5,79,6752293]),(11,4,[3,7,1543,10289]),(7,1,[5,7,80824717]),(7,4,[3,3,83,379,1249]),(11,1,[5,103,5826133]),(5,9,[3,7,558121]),(7,1,[5,83,1483,5171]),(5,5,[3,3,17,1300027]),(7,1,[5,7,13,7418377]),(5,10,[3,2197501]),(7,1,[5,7,7,23,635333]),(5,5,[3,239,312073]),(7,1,[5,7,17,41,155653]),(5,4,[3,3,3,3,3,1953269]),(7,1,[5,7,11,10460903]),(5,4,[3,3,3,3,919,6763]),(14,1,[5,7,7,7,31,80347]),(5,10,[3,3,927007]),(17,1,[5,5,7,25888769]),(5,5,[3,383,246439]),(7,1,[5,7,19,7225831]),(5,5,[3,3,101,330389]),(7,1,[5,7,145614709]),(5,9,[3,3,3,3,3,3,3,9103])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [312233136,331162076,351249376,372555076,395140716,419107596,444525956,471477516,500076416,530411016,562560256,596683576,632859156,671241276,711941376,755089096,800862936,849419136] 9359571870991978415 77923389811670798974 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_12 (k : ℕ) (lo : 77923389811670798975≤k) (hi : k≤648236330623735253734) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,41,43,53,79,83,97,103,107,113,137,173,233,251,281,293,313,349,419,421,433,439,461,509,521,613,691,709,733,787,919,1013,1019,1129,1223,1231,1259,1301,1307,1433,1549,2377,2659,2843,3769,3851,3929,4021,4603,5441,5507,7951,8243,10091,10243,10357,11503,17389,17903,17981,19381,19577]
  let factors : List (ℕ × ℕ × List ℕ) := [(5,1,[10091]),(22,1,[5,2659]),(2,2,[5,1433]),(2,1,[79,251]),(2,2,[3,3929]),(23,1,[5,5,1019]),(2,2,[19,691]),(2,1,[17,1549]),(3,1,[3,10357]),(2,2,[3,7951]),(2,1,[3,23,709]),(5,1,[7,41,433]),(2,1,[7,17903]),(3,3,[43,1307]),(5,1,[250643]),(6,1,[3,5,17389]),(10,3,[3,3,7,1223]),(11,1,[3,3,3,11,11,97]),(2,2,[3,103,1301]),(6,1,[3,3,3,5,79,79]),(2,2,[13,47149]),(2,1,[3,521671]),(5,7,[3,3,2843]),(2,1,[3,3,7,26591]),(10,2,[3,5,7,17,17,41]),(5,5,[3,52517]),(5,1,[3,3,83,3769]),(3,6,[97843]),(7,3,[3,3,5,107,439]),(2,1,[3,5,633799]),(3,1,[3,3275137]),(5,1,[7,313,5441]),(15,1,[3,5041633]),(3,1,[3,3,3,3,3,19,4603]),(11,1,[5,5630887]),(3,4,[1231,4021]),(6,2,[3,233,62143]),(7,4,[3,11,509,1013]),(2,2,[3,7,7,419,1129]),(3,1,[3,3,3,3,11,11,17,919]),(13,5,[3,56308871]),(5,3,[3,83,281,10243]),(10,5,[3,5507,11503]),(5,4,[3,3,3,3,4976581]),(10,6,[3,11,113,28661]),(5,8,[3,3,3,11,95413]),(5,6,[3,23,733,2377]),(5,6,[3,42504103]),(5,4,[3,107,1685071]),(11,5,[3,3,13,2451749]),(10,4,[3,3851,52667]),(5,4,[3,349,616393]),(7,1,[5,7,13,613,19381]),(17,6,[3,56308871]),(5,6,[3,3,19013971]),(7,1,[5,7,7,11,53,137,293]),(5,4,[3,83,281,10243]),(10,7,[3,30249799]),(11,1,[5,7,173751829]),(5,6,[3,5507,11503]),(5,5,[3,313,521,787]),(11,1,[5,5,7,11,3350467]),(5,5,[3,3,3,3,4976581]),(10,4,[3,272245777]),(14,1,[5,7,23,421,20183]),(5,7,[3,11,113,28661]),(5,10,[3,3,3,501287]),(17,1,[5,7,461,449609]),(5,9,[3,3,3,11,95413]),(5,4,[3,306242047]),(7,1,[5,7,13,16910281]),(5,7,[3,23,733,2377]),(13,1,[5,5,7,29,1608037]),(5,7,[3,42504103]),(11,1,[5,7,79,3130027]),(5,5,[3,107,1685071]),(7,1,[5,7,11,23842463]),(7,6,[3,3,13,2451749]),(7,1,[5,7,278153989]),(7,5,[3,3851,52667]),(7,1,[5,7,43,173,39659]),(5,5,[3,349,616393]),(11,1,[5,7,1259,248543]),(5,7,[3,3,19013971]),(11,1,[5,7,53,6261953]),(10,8,[3,30249799]),(7,1,[5,7,17981,19577]),(7,6,[3,313,521,787]),(13,1,[5,7,19,19650823]),(7,5,[3,272245777]),(14,1,[5,5,7,79197617]),(5,11,[3,3,3,501287]),(7,1,[5,7,8243,50951]),(10,5,[3,306242047])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [900941936,955589956,1013552336,1074941496,1140019936,1209073536,1282362976,1360131296,1442420776,1529891376,1622564936,1720969256,1825341216,1935987136,2053415216,2177966216,2309930496,2449936376] 77923389811670798975 648236330623735253734 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_13 (k : ℕ) (lo : 648236330623735253735≤k) (hi : k≤5398017626070663048334) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,41,43,47,59,67,71,79,83,89,101,103,107,137,139,157,167,181,197,211,233,257,277,281,337,347,379,383,409,419,461,487,491,617,673,733,907,937,947,1039,1091,2017,2131,2267,2381,2417,2707,3529,3691,4007,4493,5477,5791,8053,9151,10457,10861,11701,18457]
  let factors : List (ℕ × ℕ × List ℕ) := [(7,1,[5,5,491]),(7,1,[5,7,19,31]),(2,2,[11,947]),(3,4,[11,257]),(5,1,[24551]),(7,1,[5,59,89]),(7,1,[7,5477]),(11,3,[3,3529]),(10,6,[3,461]),(5,1,[3,31,487]),(7,1,[3,3,3,7,281]),(2,2,[3,19,937]),(5,1,[7,83,211]),(5,1,[3,3,3,19,19,19]),(11,1,[17,41,347]),(5,1,[245183]),(3,2,[5,13,19,233]),(6,1,[3,13,43,383]),(2,2,[11,11,2707]),(2,1,[5,5,41669]),(5,2,[3,3,3,29,29,29]),(2,2,[43,67,277]),(11,2,[3,3,3,3,5,7,13,23]),(2,1,[43,49103]),(2,1,[1091,3691]),(23,3,[3,3,5,7,29,137]),(13,1,[5,1284583]),(7,1,[3,7,19,18457]),(5,1,[8053763]),(2,1,[5,13,17,10457]),(10,2,[5,1310189]),(3,2,[7,23,103,419]),(2,2,[3,3192149]),(3,4,[71,45233]),(12,1,[3,3,3,5,157,2267]),(2,2,[89,490367]),(6,1,[3,5,5,13,213637]),(5,1,[11,23,107,8053]),(2,1,[3,5,14728687]),(5,2,[3,3,12845831]),(2,2,[3,3,7,31,157,617]),(6,2,[3,5,59,101,2381]),(5,5,[3,11,139,106219]),(5,4,[3,4493,76679]),(19,5,[3,2017,90583]),(5,9,[3,11,13,84697]),(5,7,[3,51384689]),(5,4,[3,436005527]),(5,4,[3,462449917]),(5,4,[3,167,733,4007]),(10,5,[3,11,43,47,11701]),(5,5,[3,3,1039,88513]),(5,5,[3,13,13,13,23,5791]),(5,5,[3,31,10011961]),(19,1,[5,7,17,26203781]),(5,6,[3,11,139,106219]),(17,6,[3,11,13,1151021]),(7,1,[5,7,17,27793109]),(5,5,[3,4493,76679]),(11,6,[3,174570653]),(7,1,[5,7,23,2381,9151]),(10,6,[3,2017,90583]),(10,9,[3,2131,10861]),(7,1,[5,7,23,23109971]),(5,10,[3,11,13,84697]),(10,5,[3,11,11,17,79,2417]),(7,1,[5,5,7,7,16107527]),(5,8,[3,51384689]),(5,5,[3,416592151]),(7,1,[5,7,7,41,2083451]),(7,5,[3,436005527]),(5,5,[3,441860611]),(7,1,[5,7,673,907,1039]),(5,5,[3,462449917]),(7,1,[5,7,7,96098131]),(13,5,[3,167,733,4007]),(7,1,[5,5,5,7,59,483719]),(5,6,[3,11,43,47,11701]),(7,1,[5,7,756740629]),(5,6,[3,3,1039,88513]),(14,1,[5,7,11,197,370387]),(5,6,[3,13,13,13,23,5791]),(7,1,[5,7,851302741]),(5,6,[3,31,10011961]),(7,1,[5,5,7,19,181,52511]),(7,7,[3,11,13,1151021]),(14,1,[5,5,5,7,38305789]),(5,7,[3,174570653]),(7,1,[5,5,7,13,379,41231]),(7,10,[3,2131,10861]),(7,1,[5,7,409,2634013]),(10,6,[3,11,11,17,79,2417]),(14,1,[5,7,337,3390661]),(7,6,[3,416592151]),(7,1,[5,7,7,41,4222859]),(5,6,[3,441860611])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [2598541616,2756149976,2923294576,3100587776,3288620096,3488044216,3699599336,3924007016,4161998896,4414320336,4682000336,4965932656,5267072096,5586260896,5925066496,6284316016,6665474416,7069769776] 648236330623735253735 5398017626070663048334 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_14 (k : ℕ) (lo : 5398017626070663048335≤k) (hi : k≤44952220242206939987134) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,59,67,71,73,83,89,97,103,107,109,113,137,139,149,151,157,163,167,179,191,193,229,233,239,263,317,331,353,379,389,419,421,499,523,541,569,577,613,701,797,823,859,983,1237,1249,1777,1867,2273,2311,2707,3137,3203,3539,4243,4651,4817,6763,6911,7757,11783,14431,18749]
  let factors : List (ℕ × ℕ × List ℕ) := [(2,1,[3,3,5,229]),(3,1,[3,31,167]),(5,5,[3,3,7,17]),(11,3,[5,7,151]),(11,1,[11,11,239]),(3,3,[11,11,71]),(7,5,[3,3,17,17]),(3,1,[3,14431]),(3,3,[29,421]),(5,1,[3,7,19,149]),(3,9,[233]),(10,3,[3,41,139]),(2,2,[7,17,353]),(3,1,[3,11,17,163]),(2,1,[5,5,29,157]),(2,2,[83233]),(2,1,[168029]),(2,2,[3,17,29,67]),(14,4,[3,5,5,389]),(3,1,[3,332933]),(3,4,[19,6763]),(5,5,[3,3,7757]),(14,1,[5,499,613]),(5,6,[3,31,541]),(2,1,[7,336059]),(5,1,[3058871]),(5,4,[3,3,3,37,983]),(3,2,[7,7,7,7,1867]),(11,1,[5,7,7,73,4651]),(5,1,[7,191,118903]),(7,1,[3,3,3,3,7,13,73,331]),(22,1,[5,5,137,86587]),(6,2,[3,3,3,3,3,23,97673]),(2,2,[3,5,7,2311,3203]),(5,5,[3,3,2273,68729]),(10,6,[3,3,3,151,182887]),(5,7,[3,3,193,227651]),(5,9,[3,17,2055953]),(5,5,[3,593120951]),(5,7,[3,37,41,83,1249]),(5,6,[3,167,1997599]),(5,7,[3,379,466801]),(5,6,[3,37,541,18749]),(17,7,[3,3,31,37,57839]),(10,6,[3,3539,119297]),(5,5,[3,3,19,15712273]),(11,1,[5,7,577,823,2707]),(5,6,[3,3,2273,68729]),(10,5,[3,19,4243,11783]),(7,1,[5,7,83,797,20611]),(7,7,[3,3,3,151,182887]),(5,7,[3,17,19,67,103,113]),(7,1,[5,7,97,109,136777]),(7,8,[3,3,193,227651]),(10,5,[3,3,356210947]),(7,1,[5,7,37,41,569,1777]),(5,10,[3,17,2055953]),(10,10,[3,11,3220033]),(7,1,[5,7,109,353,42281]),(7,6,[3,593120951]),(5,6,[3,37,523,31063]),(7,1,[5,5,7,43,107,179,419]),(5,8,[3,37,41,83,1249]),(5,7,[3,3,3,3,3,19,43,4817]),(14,1,[5,7,11,166366271]),(5,7,[3,167,1997599]),(7,1,[5,7,59,83,396373]),(7,8,[3,379,466801]),(7,1,[5,7,13,263,701,859]),(5,7,[3,37,541,18749]),(7,1,[5,7,2183577589]),(5,8,[3,3,31,37,57839]),(7,1,[5,7,17,137,317,3137]),(7,7,[3,3539,119297]),(14,1,[5,7,137,17930669]),(5,6,[3,3,19,15712273]),(11,1,[5,7,11,6911,34273]),(7,6,[3,19,4243,11783]),(14,1,[5,7,1237,2234017]),(5,8,[3,17,19,67,103,113]),(7,1,[5,7,7,89,4704827]),(5,6,[3,3,356210947]),(7,1,[5,7,3108895861]),(5,11,[3,11,3220033]),(13,1,[5,7,7,7,11,6117743]),(5,7,[3,37,523,31063]),(11,1,[5,7,11,317946623]),(5,8,[3,3,3,3,3,19,43,4817])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [7498608816,7953389856,8435835456,8947507456,9489935216,10064821696,10675169056,11322725056,12009559456,12737535936,13510146656,14329592976,15198561776,16120294336,17098125456,18135225856,19235203616,20401574976] 5398017626070663048335 44952220242206939987134 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_15 (k : ℕ) (lo : 44952220242206939987135≤k) (hi : k≤374147880289409352327934) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,61,67,71,73,79,83,89,97,103,107,109,137,149,157,173,193,211,251,257,269,313,347,349,563,569,613,739,743,857,947,971,1229,1447,1471,1571,1861,1901,1987,2089,2113,2381,2677,3313,3529,3923,4021,4129,5171,5309,5701,6277,6703,7331,8731,9067,10333,11887,13913]
  let factors : List (ℕ × ℕ × List ℕ) := [(3,4,[13,97]),(3,3,[53,67]),(3,1,[3,3,3,3,7,29]),(2,1,[5,3529]),(3,1,[3,6277]),(2,2,[10333]),(3,1,[3,5,1447]),(10,3,[3,3,7,103]),(6,1,[3,5,5,19,19]),(15,2,[3,23,211]),(3,2,[11,17,79]),(3,1,[3,5,7,349]),(2,2,[3,7331]),(2,1,[3,3,3,11,173]),(2,2,[3,31,313]),(5,1,[11,5701]),(2,2,[3,3,3,5,5,73]),(3,1,[3,3,3,4129]),(2,2,[17,17,211]),(13,1,[5,5,5,1471]),(3,1,[3,5,7,1987]),(13,1,[5,43411]),(7,1,[5,7,11,569]),(2,2,[17,61,107]),(11,1,[3,11,19,563]),(3,1,[3,7,67,269]),(2,1,[3,13,11887]),(2,1,[5,5,20177]),(3,4,[87973]),(2,2,[3,197101]),(10,1,[3,23,32887]),(5,4,[3,251,569]),(7,1,[37,103,1229]),(2,2,[83,28409]),(2,2,[17,17,8731]),(2,1,[193,41333]),(7,1,[9367439]),(17,1,[2089,5171]),(3,1,[3,3,7,79,9067]),(3,1,[3,3,3,5,11,58237]),(3,1,[3,347,102763]),(5,3,[3,2381,6703]),(12,1,[3,3,19,1407569]),(5,1,[47,6855313]),(5,2,[3,563,739,743]),(7,2,[3,5,5,13,1008851]),(5,6,[3,149,4538407]),(10,9,[3,11,157,51913]),(5,7,[3,857,443837]),(5,9,[3,19,31,109,1571]),(5,8,[3,213952567]),(10,6,[3,11,89,927187]),(5,7,[3,481388599]),(10,6,[3,19,71,756967]),(5,8,[3,3,90252919]),(5,9,[3,3,3,15954539]),(5,6,[3,3313,367751]),(5,6,[3,137,9431789]),(7,1,[5,7,3709564213]),(7,7,[3,149,4538407]),(5,6,[3,3,3923,116437]),(13,1,[5,7,3934518901]),(5,10,[3,11,157,51913]),(10,10,[3,3,3,10093037]),(7,1,[5,7,23,257,706003]),(10,8,[3,857,443837]),(5,6,[3,3,3,3,19,41,73291]),(7,1,[5,7,35291,125423]),(5,10,[3,19,31,109,1571]),(5,7,[3,3,3,3,3,1901,5309]),(7,1,[5,7,31,4021,37663]),(10,9,[3,213952567]),(13,7,[3,3,67,73,59093]),(7,1,[5,7,13,383036233]),(5,7,[3,11,89,927187]),(5,9,[3,19,29,417271]),(7,1,[5,7,7,11,29,2365213]),(5,8,[3,481388599]),(7,1,[5,7,13,23,18734879]),(15,7,[3,19,71,756967]),(7,1,[5,5,5,7,11,21604439]),(5,9,[3,3,90252919]),(7,1,[5,7,7,11,89,947,971]),(7,10,[3,3,3,15954539]),(7,1,[5,7,11,47,53,243917]),(5,7,[3,3313,367751]),(53,1,[5,7,11,644399423]),(7,7,[3,137,9431789]),(7,1,[5,5,7,11,613,222967]),(5,7,[3,3,3923,116437]),(7,1,[5,5,7,11,2677,54151]),(7,11,[3,3,3,10093037]),(7,1,[5,5,7,11,43,257,13913]),(5,7,[3,3,3,3,19,41,73291]),(14,1,[5,7,11,1861,438131]),(7,8,[3,3,3,3,3,1901,5309]),(7,1,[5,5,7,11,172963891]),(5,8,[3,3,67,73,59093]),(7,1,[5,7,11,2113,434111]),(5,10,[3,19,29,417271])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [21639124576,22951360256,24343571776,25820101376,27385928576,29046914336,30808870336,32676751456,34657120896,36759257856,38987490016,41348962976,43851105696,46508714496,49328947296,52319048256,55492581696,58858578176] 44952220242206939987135 374147880289409352327934 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_16 (k : ℕ) (lo : 374147880289409352327935≤k) (hi : k≤3112168098155495977307134) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,73,79,83,89,97,101,103,113,127,137,163,173,193,199,229,241,251,313,349,353,383,433,439,499,521,593,647,743,751,877,1051,1091,1289,1327,1399,1471,1511,1597,1999,2053,2069,2221,3119,3391,3461,3823,4013,4099,4201,4691,5231,6067,6113,6271,8423,8467,8719,9857,12289,13619,17669,18013,19753]
  let factors : List (ℕ × ℕ × List ℕ) := [(3,1,[3,3391]),(5,4,[3,3,199]),(2,1,[3,5231]),(5,2,[3,7,383]),(2,1,[17669]),(5,1,[127,173]),(3,7,[5,103]),(3,2,[5,5,23,29]),(2,2,[18013]),(13,4,[3,3,11,47]),(2,1,[66701]),(6,2,[3,83,137]),(7,1,[7,9857]),(14,1,[5,7,2053]),(13,1,[3,41,593]),(2,1,[3,3,3,3,13,73]),(2,2,[5,5,1597]),(3,3,[19,1289]),(13,1,[17,6067]),(2,1,[3,3,12289]),(5,1,[3,7,6271]),(11,1,[137999]),(2,2,[74449]),(3,1,[3,5,17,751]),(3,3,[173,433]),(7,1,[5,7,23,647]),(2,2,[5,72053]),(2,2,[3,3,193,349]),(17,1,[41,145879]),(2,2,[3,3,19,97,1471]),(5,1,[3,11,11,159701]),(6,6,[5,13,65921]),(5,1,[83,1051,6271]),(5,1,[29,29,1041671]),(11,1,[5,11,97,195929]),(5,6,[3,3,37,59,297797]),(5,7,[3,313,1597,2069]),(10,9,[3,274231361]),(10,8,[3,251,743,3119]),(5,8,[3,4013,153739]),(5,7,[3,13,29,79,43943]),(5,8,[3,23,3461,8719]),(5,9,[3,31,31,383011]),(5,11,[3,97597909]),(5,7,[3,17,353,275999]),(10,7,[3,23,53,1441061]),(5,7,[3,8423,221203]),(21,1,[5,5,7,11,31,43,73,1999]),(5,7,[3,3,37,59,297797]),(5,7,[3,3,41,61,263383]),(13,1,[5,7,11,29,4201,8467]),(5,8,[3,313,1597,2069]),(5,9,[3,3,61,89,32173]),(7,1,[5,7,11,1094076287]),(5,10,[3,274231361]),(5,7,[3,31,499,143711]),(11,1,[5,7,11,97,11962079]),(5,9,[3,251,743,3119]),(5,9,[3,19,61,229,2221]),(7,1,[5,5,7,11,11,53,103,4099]),(19,9,[3,4013,153739]),(5,7,[3,3,3,3,3,3,521,19753]),(11,1,[5,7,11,11,41,101,28657]),(5,8,[3,13,29,79,43943]),(11,11,[3,4691,35339]),(11,1,[5,5,7,11,31,439,20347]),(5,9,[3,23,3461,8719]),(7,1,[5,7,7,11,113,1327,1399]),(5,10,[3,31,31,383011]),(11,1,[5,7,11,23,113,599273]),(7,12,[3,97597909]),(21,1,[5,7,11,11,163,241,3823]),(5,8,[3,17,353,275999]),(7,1,[5,7,11,1752090623]),(5,8,[3,23,53,1441061]),(7,1,[5,7,11,13619,136453]),(5,8,[3,8423,221203]),(11,1,[5,7,11,17,115942927]),(5,8,[3,3,41,61,263383]),(7,1,[5,7,11,2090562431]),(7,10,[3,3,61,89,32173]),(14,1,[5,7,11,11,1511,133403]),(5,8,[3,31,499,143711]),(17,1,[5,7,11,13,877,206279]),(5,10,[3,19,61,229,2221]),(21,1,[5,7,11,13,6113,31387]),(5,8,[3,3,3,3,3,3,521,19753]),(11,1,[5,7,11,1091,2424853]),(5,12,[3,4691,35339])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [62408721696,66189594176,70203228416,74453973376,78970189696,83760279616,88839495296,94226834176,99940258816,106001279936,112425814976,119244343616,126474409536,134144422656,142276189376,150906324736,160050499776,169753854976] 374147880289409352327935 3112168098155495977307134 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_17 (k : ℕ) (lo : 3112168098155495977307135≤k) (hi : k≤25906211690884115771609854) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,53,61,67,71,73,79,97,109,113,137,149,157,181,191,197,227,241,251,283,313,347,389,401,421,449,467,569,577,601,619,653,797,859,1049,1051,1087,1151,1193,1201,1223,1321,1367,1949,2053,2087,2099,2179,2347,2521,2609,2689,2767,3203,4793,6173,6829,8951,9209,9421,9623,10211,10301,10333,11003,12569,16493,18803]
  let factors : List (ℕ × ℕ × List ℕ) := [(3,2,[13,17,23]),(2,2,[3,5,13,29]),(7,1,[67,197]),(2,1,[3,5,7,137]),(6,1,[3,3,5,347]),(7,1,[3,5,17,181]),(2,1,[19,41,79]),(5,6,[3,3,251]),(3,1,[3,43,797]),(5,1,[123083]),(2,1,[3,5,10211]),(17,1,[13,18803]),(3,1,[3,5,22621]),(2,1,[3,11,10333]),(2,2,[5,5,6829]),(2,1,[11,31231]),(3,2,[11,17,1321]),(11,1,[19,137,313]),(5,4,[3,3,12569]),(2,2,[3,29,31,197]),(3,3,[283,1223]),(6,1,[3,7,7,7,1367]),(3,4,[7,71,653]),(3,3,[569,1201]),(11,1,[17,205627]),(2,1,[11,678631]),(2,2,[29,37,4793]),(2,2,[2053,2689]),(3,1,[3,29,157,1087]),(3,3,[5192657]),(3,4,[11,389,619]),(3,1,[3,7,1629479]),(5,1,[401,92311]),(2,2,[3,6991319]),(5,6,[3,7,97,859]),(6,1,[3,3,3,2125237]),(3,1,[3,11,2813287]),(5,1,[227,467,2099]),(3,1,[3,3,1193,26399]),(2,1,[7,7,53,144577]),(2,2,[3,5,5,13,306331]),(7,1,[2179,682901]),(11,1,[5,11,6173,9421]),(5,8,[3,19,74033423]),(5,8,[3,13,114762799]),(5,10,[3,3,3,3,37,43,9209]),(5,11,[3,191,421,2609]),(11,10,[3,445025783]),(15,7,[3,3,3,19,22082069]),(5,10,[3,149,1049,3203]),(5,7,[3,2347,1809937]),(5,8,[3,3,750932939]),(5,9,[3,1194690901]),(5,8,[3,61,41541257]),(5,11,[3,3,111986113]),(7,1,[5,7,11,41,68438119]),(5,9,[3,19,74033423]),(10,13,[3,3,29694667]),(7,1,[5,7,11,2976082559]),(5,9,[3,13,114762799]),(11,8,[3,109,2521,11003]),(11,1,[5,7,11,17,185676943]),(5,11,[3,3,3,3,37,43,9209]),(5,8,[3,3,19,2767,20333]),(7,1,[5,7,11,79,42379217]),(5,12,[3,191,421,2609]),(10,9,[3,3,566892127]),(7,1,[5,5,5,7,11,577,246167]),(5,11,[3,445025783]),(10,8,[3,43,83895829]),(7,1,[5,7,11,23,347,449,1051]),(7,8,[3,3,3,19,22082069]),(5,9,[3,3,31,20571557]),(7,1,[5,7,11,13,31,601,16493]),(7,11,[3,149,1049,3203]),(7,1,[5,5,5,7,11,31,5466953]),(5,8,[3,2347,1809937]),(7,1,[5,7,7,11,43,14929883]),(7,9,[3,3,750932939]),(17,1,[5,7,11,29,241,681979]),(5,10,[3,1194690901]),(7,1,[5,7,7,11,1051,687083]),(5,9,[3,61,41541257]),(7,1,[5,7,7,11,41,2087,8951]),(5,12,[3,3,111986113]),(7,1,[5,5,7,11,1151,988109]),(5,14,[3,3,29694667]),(7,1,[5,7,11,13,13,73,488879]),(5,9,[3,109,2521,11003]),(7,1,[5,7,11,6397141631]),(5,9,[3,3,19,2767,20333]),(7,1,[5,7,11,11,11,1949,28771]),(7,10,[3,3,566892127]),(7,1,[5,7,11,23,113,2768873]),(5,9,[3,43,83895829]),(11,1,[5,7,7,11,11,9623,10301]),(5,10,[3,3,31,20571557])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [180049284736,190965297536,202542598656,214827314176,227853200896,241666163136,256323636736,271867016896,288358248576,305840870656,324354134656,344021339136,364888068096,387008430976,410483254656,435373153536,461762642816,489767629056] 3112168098155495977307135 25906211690884115771609854 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_18 (k : ℕ) (lo : 25906211690884115771609855≤k) (hi : k≤215729467198384297245002494) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,59,61,67,71,73,83,97,101,107,109,127,131,137,139,151,163,173,179,191,197,211,251,257,277,283,293,347,367,373,401,409,431,479,499,607,619,701,751,797,821,857,1009,1051,1093,1123,1427,1973,2333,2903,3719,3923,4799,5399,5701,5791,6143,6563,7019,7547,7687,9967,15199,18143]
  let factors : List (ℕ × ℕ × List ℕ) := [(2,1,[83,163]),(2,2,[5,7,197]),(5,2,[3,2333]),(3,3,[3719]),(3,1,[3,3,7,251]),(3,3,[11,367]),(2,2,[3,13,211]),(2,1,[3,7,821]),(3,3,[5,1093]),(17,3,[3,3,5,131]),(2,2,[5,41,61]),(2,1,[7,4799]),(3,1,[3,23,499]),(2,1,[59,619]),(7,1,[13,3923]),(2,1,[11,11,11,43]),(10,1,[11,13,13,37]),(2,2,[34483]),(11,1,[101999]),(2,1,[5,7,43,73]),(3,2,[5,23,607]),(22,3,[3,3,5,7,7,17]),(7,1,[7,11,29,71]),(5,1,[219731]),(11,1,[7,32297]),(5,1,[17,41,479]),(13,1,[5,68863]),(2,1,[3,137567]),(7,1,[5,5,7,41,109]),(2,1,[3,17,83,257]),(6,4,[5,29753]),(3,1,[3,17,27059]),(2,1,[5,299881]),(6,2,[3,11,73,347]),(2,2,[3,279221]),(3,3,[1564151]),(2,2,[3343693]),(2,2,[17,203999]),(5,1,[3,2380241]),(2,1,[11,825403]),(2,2,[5,5,13,15199]),(3,1,[3,3,3,19,71,367]),(5,1,[19,71,9967]),(3,1,[3,109,163,283]),(7,1,[7,17,37,5701]),(3,8,[373,751]),(5,1,[3,7,857,2903]),(6,1,[5,5,619,6563]),(5,3,[3,3,2998811]),(2,2,[104490583]),(5,4,[3,29,37,107,139]),(2,2,[13,23,97,7019]),(2,1,[417962333]),(2,2,[215914393]),(3,3,[41,137,43721]),(2,1,[3,5,5,18158867]),(3,3,[5,179,439463]),(7,1,[3,13,50203007]),(3,3,[43,12513209]),(5,4,[3,3,3,13374773]),(5,8,[3,3,173,431,18143]),(5,8,[3,4304543897]),(10,10,[3,29,1427,27581]),(5,11,[3,3,293,688631]),(5,8,[3,191,26890967]),(5,9,[3,2723830051]),(5,8,[3,5777901937]),(5,8,[3,31,59,3350653]),(5,13,[3,203124851]),(5,8,[3,3,3,766018993]),(5,8,[3,3,7687,317087]),(10,8,[3,17,1009,452159]),(7,1,[5,7,7,11,101,409,27997]),(5,9,[3,3,173,431,18143]),(10,14,[3,3,3,14281447]),(7,1,[5,7,11,619,13871933]),(5,9,[3,4304543897]),(5,9,[3,31627,137933]),(7,1,[5,7,11,127,71711489]),(5,11,[3,29,1427,27581]),(10,9,[3,13,7547,47161]),(7,1,[5,7,11,797,1973,6143]),(5,12,[3,3,293,688631]),(10,9,[3,67187,73043]),(7,1,[5,7,11,17,277,2175763]),(5,9,[3,191,26890967]),(5,11,[3,3,19,29,701,1123]),(11,1,[5,7,11,13,835924667]),(5,10,[3,2723830051]),(10,9,[3,3,61,30168367]),(14,1,[5,7,7,11,32917,50021]),(7,9,[3,5777901937]),(13,1,[5,7,11,17,23,5399,5791]),(5,9,[3,31,59,3350653]),(7,1,[5,5,7,11,97,26734483]),(5,14,[3,203124851]),(7,1,[5,7,7,11,1964646857]),(5,9,[3,3,3,766018993]),(11,1,[5,5,7,7,11,151,2760019]),(5,9,[3,3,7687,317087]),(7,1,[5,7,11,19,814288229]),(7,9,[3,17,1009,452159]),(11,1,[5,7,11,19,863657573]),(5,15,[3,3,3,14281447]),(11,1,[5,5,7,11,13,401,667727]),(7,10,[3,31627,137933]),(7,1,[5,7,11,29,67,83,114467]),(5,10,[3,13,7547,47161]),(11,1,[5,5,7,11,3915834547]),(5,10,[3,67187,73043]),(7,1,[5,7,11,1051,19758701]),(5,12,[3,3,19,29,701,1123]),(11,1,[5,7,7,11,3146555081]),(5,10,[3,3,61,30168367])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [519473859456,550981618816,584388875776,619834008576,657430361216,697300493056,739571447936,784428075136,831999389696,882453879936,935979943296,992753065856,1052942524416,1116776189696,1184515294976,1256330250496,1332510329856,1413327657216] 25906211690884115771609855 215729467198384297245002494 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_19 (k : ℕ) (lo : 215729467198384297245002495≤k) (hi : k≤1796859816709802564152317694) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,59,61,67,71,73,79,89,103,107,109,127,131,137,139,151,163,173,179,193,199,227,229,257,271,293,307,317,331,367,439,461,463,467,571,709,821,839,1013,1033,1049,1223,1279,1481,1549,1723,1987,2309,2557,2789,2909,3301,3631,3881,4339,4349,4621,5279,5351,5443,5711,6101,6361,6421,8537,10091,10499,11503,12721,13933]
  let factors : List (ℕ × ℕ × List ℕ) := [(5,1,[10091]),(7,1,[5,5,29,43]),(3,1,[3,3,31,127]),(3,1,[3,41,317]),(3,1,[3,103,127]),(3,1,[3,5,5,5,5,29]),(13,4,[3,5,461]),(43,1,[5,11,37,41]),(5,2,[11,17,229]),(2,2,[13,3301]),(14,3,[3,5,11,151]),(2,2,[13,4339]),(2,1,[3,179,257]),(3,1,[3,13,4621]),(2,1,[3,3,109,193]),(3,3,[5,5,23,109]),(2,2,[5,5,5,1013]),(2,2,[3,163,293]),(3,3,[19,5711]),(2,1,[506501]),(2,1,[3,109,1723]),(5,2,[3,108751]),(13,1,[5,199,709]),(5,1,[3,23,37,461]),(7,4,[3,139,439]),(2,2,[13,23,31,107]),(2,2,[1305013]),(2,2,[19,78487]),(2,1,[5220053]),(3,6,[378667]),(2,1,[11,1126843]),(21,4,[5,7,171653]),(2,2,[19,19,59,1481]),(2,2,[3,3,3967133]),(2,1,[17,2557,2557]),(2,2,[3,5,1279,4349]),(2,2,[5,7,271,10499]),(5,1,[3,3,3,19,37,11503]),(2,1,[3,41,151,13933]),(5,4,[7,43,110641]),(2,1,[398332061]),(2,2,[517555219]),(7,5,[3,137,225629]),(5,4,[3,13,79,70867]),(2,2,[3,5351,77983]),(2,1,[3,89,10440107]),(2,2,[5,796664123]),(7,1,[5,7,333742261]),(17,1,[131,142816789]),(5,12,[3,199,1013,3631]),(5,9,[3,3,2070220877]),(5,9,[3,13,173,2929009]),(5,10,[3,3493459633]),(11,9,[3,8537,868073]),(10,10,[3,3,3,436676887]),(5,11,[3,3,3,839,276019]),(5,9,[3,3,37,139,573109]),(5,11,[3,17,17,2789,2909]),(11,10,[3,3,331,821,6101]),(5,9,[3,31,1987,171293]),(10,10,[3,17,5279,62351]),(13,1,[5,7,11,23361958271]),(7,13,[3,199,1013,3631]),(11,11,[3,2967472609]),(7,1,[5,7,11,193,6361,20183]),(5,10,[3,3,2070220877]),(5,9,[3,3,3,3881,360439]),(7,1,[5,5,7,7,11,11,29,2353867]),(5,10,[3,13,173,2929009]),(5,10,[3,3,13,13,13,1013003]),(7,1,[5,5,7,11,5575017139]),(5,11,[3,3493459633]),(15,13,[3,89,1549,6421]),(21,1,[5,7,7,11,19,222300467]),(5,10,[3,8537,868073]),(5,9,[3,3,5007444397]),(7,1,[5,5,7,11,67,71,571,2309]),(5,11,[3,3,3,436676887]),(11,9,[3,15933282461]),(13,1,[5,7,11,166871,199321]),(7,12,[3,3,3,839,276019]),(7,1,[5,7,11,367,96125681]),(5,10,[3,3,37,139,573109]),(7,1,[5,7,11,37417998719]),(10,12,[3,17,17,2789,2909]),(7,1,[5,7,11,23,1223,1410911]),(5,11,[3,3,331,821,6101]),(7,1,[5,7,11,79,532847057]),(5,10,[3,31,1987,171293]),(7,1,[5,7,7,11,12721,501401]),(5,11,[3,17,5279,62351]),(11,1,[5,7,11,17,467,5965013]),(7,12,[3,2967472609]),(7,1,[5,7,11,19,463,1049,5443]),(5,10,[3,3,3,3881,360439]),(7,1,[5,7,7,11,307,24790547]),(5,11,[3,3,13,13,13,1013003]),(7,1,[5,7,11,73,227,1033,3301]),(5,14,[3,89,1549,6421]),(7,1,[5,5,5,7,11,19,126175277]),(5,10,[3,3,5007444397]),(7,1,[5,7,11,43,61,24234689]),(5,10,[3,15933282461])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [1499058989056,1589929633536,1686359357696,1788651332096,1897149235456,2012207095296,2134240736256,2263679682816,2400988251136,2546615579136,2701090539776,2864929686016,3038691951616,3222982100736,3418471819776,3625801650176,3845717296896,4078920310016] 215729467198384297245002495 1796859816709802564152317694 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_20 (k : ℕ) (lo : 1796859816709802564152317695≤k) (hi : k≤14956760007299482974445756414) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,79,83,97,101,113,127,137,139,173,179,181,191,197,227,229,233,367,373,401,443,449,461,587,719,739,751,1381,1429,1433,1471,1493,1667,1723,1907,2003,2131,2153,2287,2309,2729,2797,4373,4801,5471,7459,7877,8233,8269,9391,12527,13183,13457,16091,16249,17351,17657]
  let factors : List (ℕ × ℕ × List ℕ) := [(10,3,[3,3,7,43]),(5,2,[3,7,13,23]),(2,1,[3,5,7,137]),(2,2,[7459]),(5,1,[83,181]),(2,2,[5,11,13,13]),(2,2,[7,29,71]),(3,1,[3,13,19,41]),(2,2,[5,5,5,5,5,5]),(2,2,[16249]),(2,1,[37181]),(5,1,[3,17351]),(2,1,[11,61,79]),(3,1,[3,19,29,37]),(2,1,[62501]),(5,1,[23,2797]),(3,11,[5,13]),(2,2,[101,443]),(11,1,[11,8269]),(7,1,[106019]),(2,1,[5,5,4373]),(5,1,[125003]),(2,2,[59,1667]),(7,6,[3,2131]),(2,1,[13,23,739]),(2,2,[13,53,191]),(3,1,[3,104107]),(3,3,[53,1723]),(23,8,[3,5,233]),(2,1,[7,74363]),(55,3,[3,5,7,1429]),(5,3,[3,79,751]),(2,1,[3,23,67,191]),(3,1,[3,3,3,3,3,29,137]),(10,2,[3,212039]),(6,2,[3,5,60763]),(2,2,[5,181,1907]),(3,1,[3,5,29,8233]),(2,2,[1930879]),(5,3,[3,3,3,3,3,7,719]),(3,4,[137,5471]),(2,2,[11,19,181,227]),(5,4,[11,17,43,367]),(3,1,[3,5,5,43,21673]),(7,1,[7,11992433]),(22,4,[3,3645781]),(5,2,[3,3,13,17,30047]),(2,1,[11,179,64997]),(3,3,[47,894721]),(7,6,[3,5,624643]),(3,8,[173,16091]),(7,4,[3,17,1041083]),(6,1,[3,5,5,2003,9391]),(2,2,[47,1433,25117]),(5,3,[3,197,2544469]),(5,11,[3,3,41,34348733]),(10,12,[3,229,9784153]),(5,12,[3,17,139790851]),(10,10,[3,37,373,730553]),(5,10,[3,1493,7162711]),(5,14,[3,17,233,178973]),(5,10,[3,12030249433]),(5,12,[3,19,167894063]),(5,11,[3,6766620269]),(5,10,[3,3,3,3,3,401,441923]),(5,10,[3,3,29,174997489]),(5,11,[3,461,587,29837]),(7,1,[5,7,11,13,13183,393413]),(5,12,[3,3,41,34348733]),(5,10,[3,128663,133121]),(7,1,[5,7,11,47,197,7723517]),(5,13,[3,229,9784153]),(5,11,[3,3,3,3,336415097]),(7,1,[5,7,11,449,1381,122323]),(7,13,[3,17,139790851]),(11,13,[3,3,3,1471,181919]),(11,1,[5,7,11,43,181,2153,4801]),(5,11,[3,37,373,730553]),(5,10,[3,29,587,1200361]),(7,1,[5,7,11,29,13457,218651]),(10,11,[3,1493,7162711]),(5,10,[3,3,17657,409153]),(13,1,[5,7,11,127,712638209]),(5,15,[3,17,233,178973]),(5,14,[3,2729,526397]),(7,1,[5,5,7,11,97,139,1423897]),(7,11,[3,12030249433]),(7,1,[5,7,11,57653,1765987]),(7,13,[3,19,167894063]),(14,1,[5,7,11,2287,47216753]),(5,12,[3,6766620269]),(7,1,[5,7,11,191,599657281]),(5,11,[3,3,3,3,3,401,441923]),(7,1,[5,7,11,11,13,849523729]),(5,11,[3,3,29,174997489]),(7,1,[5,7,7,7,11,11,239053933]),(7,12,[3,461,587,29837]),(11,1,[5,7,11,19,28771,250007]),(5,11,[3,128663,133121]),(7,1,[5,7,11,13,113,7877,12527]),(5,12,[3,3,3,3,336415097]),(7,1,[5,7,11,13,13,31,71,179,2309]),(5,14,[3,3,3,1471,181919]),(7,1,[5,7,7,7,11,13,255958187]),(5,11,[3,29,587,1200361]),(7,1,[5,7,11,13,41,47,6903341]),(5,11,[3,3,17657,409153]),(7,1,[5,5,7,11,13,2821525951]),(5,15,[3,2729,526397])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [4326291618816,4588689483776,4866958268416,5162169319936,5475290891776,5807407538176,6159487709696,6533093779456,6929019155456,7349299693056,7795088150016,8267879484416,8769406578176,9301204601856,9864911425536,10462077595136,11096700704256,11768114487296] 1796859816709802564152317695 14956760007299482974445756414 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_21 (k : ℕ) (lo : 14956760007299482974445756415≤k) (hi : k≤124239395924916865525385005054) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,59,61,67,73,79,83,89,97,101,103,109,113,131,139,149,151,157,163,179,191,233,241,251,271,311,313,317,331,443,457,499,503,509,521,613,691,757,787,1303,1399,1447,1499,1783,1979,2017,2309,2357,2549,2693,2857,3221,4079,4241,5903,6277,7963,9241,9467,10781,11093,11213,11489,12457,12671,15647,17093]
  let factors : List (ℕ × ℕ × List ℕ) := [(2,1,[5,11,191]),(2,2,[3,1783]),(2,1,[10781]),(5,1,[3,3,1399]),(5,1,[12671]),(7,1,[5,7,7,79]),(5,1,[21011]),(5,6,[3,241]),(5,1,[59,457]),(2,2,[7,13,157]),(3,1,[3,3,3,3,5,83]),(3,3,[11,787]),(2,2,[7,2857]),(3,4,[67,109]),(3,1,[3,5,7,7,101]),(7,1,[7,11093]),(2,2,[3,5,5,5,7,19]),(3,3,[97,311]),(2,2,[3,5,4241]),(3,1,[3,61,757]),(2,2,[5,15647]),(3,5,[11489]),(2,1,[3,67231]),(7,1,[43,43,131]),(10,3,[3,3,61,113]),(7,1,[484439]),(11,3,[3,5,5,7,313]),(3,4,[61,1447]),(5,4,[3,103,443]),(11,1,[5,19,12457]),(5,2,[3,277063]),(7,4,[3,116849]),(2,1,[3,17,17,4079]),(2,2,[59,42023]),(29,6,[3,7,9467]),(2,1,[43,155303]),(2,2,[5608753]),(5,1,[11,1314601]),(3,4,[29,69257]),(13,1,[5,7,496297]),(5,2,[3,3,3,3,13,61,163]),(5,1,[13,2366831]),(2,1,[32135249]),(2,2,[3,5,19,41,2357]),(7,5,[3,5,254461]),(13,1,[5,5,37,139,509]),(2,1,[7,11,691,1303]),(2,2,[41879917]),(2,1,[457,367649]),(11,1,[13,13,19,233,313]),(2,1,[3,13,19,251,1979]),(7,2,[3,64270499]),(6,2,[3,3,28921223]),(13,1,[5,5,130889351]),(3,1,[3,11,61,151,11213]),(2,1,[3,11,110166181]),(13,1,[5,736152379]),(3,4,[11,37,1412273]),(2,1,[5,139,331,46273]),(5,11,[3,19,29,149,148471]),(5,11,[3,5903,2190193]),(5,10,[3,73,113,3324757]),(10,12,[3,7270967947]),(5,14,[3,3,3221,199501]),(5,10,[3,3,271,503,79997]),(5,13,[3,613,7072987]),(5,12,[3,9196721777]),(10,11,[3,317,61537607]),(5,14,[3,3,3,17,2693,6277]),(5,11,[3,131,167519669]),(5,13,[3,41,41,1499,2309]),(7,1,[5,5,7,11,13,73,131,312941]),(10,12,[3,19,29,149,148471]),(5,12,[3,89,138657443]),(7,1,[5,5,7,11,13,251,499,25343]),(5,12,[3,5903,2190193]),(5,13,[3,6544467551]),(21,1,[5,7,11,13,31,21563,25183]),(10,11,[3,73,113,3324757]),(10,13,[3,3,3,771245989]),(11,1,[5,7,11,13,23,61,12723649]),(5,13,[3,7270967947]),(5,13,[3,7361523791]),(17,1,[5,5,7,11,13,31,122141281]),(5,15,[3,3,3221,199501]),(5,12,[3,38711,403387]),(7,1,[5,5,7,11,13,179,22435013]),(5,11,[3,3,271,503,79997]),(5,12,[3,17093,968879]),(11,1,[5,7,11,13,21289744571]),(5,14,[3,613,7072987]),(7,1,[5,5,7,11,13,31,2549,57149]),(5,13,[3,9196721777]),(7,1,[5,7,11,13,23,1041164029]),(5,12,[3,317,61537607]),(7,1,[5,7,11,13,29,109,149,53927]),(5,15,[3,3,3,17,2693,6277]),(7,1,[5,7,11,13,2017,13356059]),(5,12,[3,131,167519669]),(7,1,[5,7,11,13,61,468350039]),(5,14,[3,41,41,1499,2309]),(7,1,[5,5,7,11,13,13,47,9917429]),(7,13,[3,89,138657443]),(7,1,[5,5,5,7,11,13,37,34740791]),(5,14,[3,6544467551]),(11,1,[5,5,7,11,13,6816674239]),(5,14,[3,3,3,771245989]),(7,1,[5,7,7,11,13,21397,241337]),(10,14,[3,7361523791]),(7,1,[5,7,11,13,521,7963,9241]),(5,13,[3,38711,403387]),(7,1,[5,7,11,11,11,13,336031187]),(7,13,[3,17093,968879])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [12481864324096,13238998301696,14042071292416,14890942355456,15792358711296,16749513309696,17759195262976,18834886199296,19975599533056,21187019022336,22471758478336,23831601442816,25273369450496,26806139088896,28431212138496,30152801447936,31980572993536,33917027833856] 14956760007299482974445756415 124239395924916865525385005054 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_22 (k : ℕ) (lo : 124239395924916865525385005055≤k) (hi : k≤1033663869923839772943807154174) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,67,71,73,79,83,97,101,109,113,127,139,151,163,167,179,181,193,211,227,233,241,263,331,367,389,449,487,563,569,619,647,659,719,739,769,787,797,863,887,1013,1277,1297,1301,1531,1579,1627,1663,1831,1913,1997,2111,2237,2521,2689,2857,3037,3221,3359,3733,3853,3943,5153,5197,5801,8017,11549,12241,12637,13331,14731,16649,18757]
  let factors : List (ℕ × ℕ × List ℕ) := [(2,2,[5197]),(11,5,[3,233]),(5,4,[3,3,163]),(10,1,[3,11,11,43]),(11,5,[3,7,53]),(2,2,[3,3,13,79]),(10,2,[3,5,769]),(6,2,[3,3943]),(2,2,[18757]),(14,4,[3,5,13,29]),(2,2,[23473]),(3,1,[3,3,3,2689]),(17,3,[3,3,5,449]),(3,1,[3,3,3,3,2521]),(3,1,[3,5,7,7,11,67]),(2,2,[13,22369]),(3,3,[7,7,3221]),(19,1,[3,71,3853]),(2,2,[83,5801]),(7,1,[5,5,7,41,139]),(3,4,[5,43,647]),(2,1,[13,37,43,71]),(5,3,[3,13,14731]),(5,3,[3,19,12241]),(11,3,[3,5,113,449]),(7,3,[3,3,90481]),(2,2,[3,5,145207]),(7,1,[19,487,863]),(2,2,[3,1579,1627]),(10,1,[3,3,2225681]),(2,1,[7,2936987]),(2,2,[3,3,1262633]),(5,5,[3,7,408403]),(7,4,[3,6088441]),(3,1,[3,5,127,179,449]),(23,4,[3,3,5,787,1301]),(7,1,[3,5,5,7,1083391]),(7,1,[3,13,193,263,389]),(2,1,[3,306213511]),(3,4,[274446817]),(5,1,[73,887,46141]),(2,2,[1540129579]),(2,2,[1837281067]),(12,1,[3,5,737198641]),(13,3,[3,17,59,1641379]),(2,2,[3,11,331,563,1831]),(13,1,[59,59,1663,5153]),(2,1,[7,11,73,6514633]),(2,1,[263,2111,93893]),(5,14,[3,4391149073]),(10,12,[3,3,151,41117819]),(5,11,[3,39511275289]),(5,12,[3,47,97,4596073]),(11,13,[3,3,3,619,1994651]),(5,11,[3,3,3,17,29,797,13331]),(5,11,[3,3,1913,8712421]),(11,12,[3,17,20789,75029]),(11,11,[3,3,3359,5581897]),(5,11,[3,59660434319]),(10,13,[3,19,97,241,35617]),(10,11,[3,59,1137560551]),(11,1,[5,7,7,11,13,6160518317]),(5,15,[3,4391149073]),(5,12,[3,3,3,3,29,45454789]),(11,1,[5,7,11,13,19,19,19,23,227,1277]),(7,13,[3,3,151,41117819]),(5,12,[3,3,37,59,719,8017]),(7,1,[5,7,11,13,3037,15970679]),(5,12,[3,39511275289]),(5,13,[3,3,211,1013,31219]),(7,1,[5,7,7,11,13,7349124269]),(10,13,[3,47,97,4596073]),(13,12,[3,17,1297,1925933]),(11,1,[5,7,11,13,739,1997,36973]),(5,14,[3,3,3,619,1994651]),(5,12,[3,45040029277]),(7,1,[5,7,11,13,31,11549,161641]),(5,12,[3,3,3,17,29,797,13331]),(5,12,[3,67,163,1531,2857]),(7,1,[5,7,11,11,13,181,30828397]),(5,12,[3,3,1913,8712421]),(14,1,[5,5,5,5,7,11,13,13,40062259]),(5,13,[3,17,20789,75029]),(7,1,[5,7,11,11,13,101,3733,16649]),(15,12,[3,3,3359,5581897]),(11,1,[5,7,11,13,73237504187]),(5,12,[3,59660434319]),(14,1,[5,7,11,13,13,5975351783]),(5,14,[3,19,97,241,35617]),(7,1,[5,7,11,13,193,367,1163189]),(5,12,[3,59,1137560551]),(11,1,[5,7,11,13,13,23,292245169]),(5,13,[3,3,3,3,29,45454789]),(7,1,[5,5,7,11,13,31,12637,47317]),(7,13,[3,3,37,59,719,8017]),(14,1,[5,5,7,11,13,13,37,109,569,659]),(17,14,[3,3,211,1013,31219]),(11,1,[5,7,11,13,104257472699]),(5,13,[3,17,1297,1925933]),(7,1,[5,5,7,11,13,22115959231]),(5,13,[3,45040029277]),(21,1,[5,7,11,13,13,19,31,41,167,2237]),(7,13,[3,67,163,1531,2857])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [35972293206016,38146809870336,40459545895936,42912761460736,45515574153216,48273683106816,51200598137856,54305226704896,57598746694656,61092284742656,64797710626816,68726858249216,72890572363776,77311787882496,81995891306496,86968108476416,92241979959296,97831292327936] 124239395924916865525385005055 1033663869923839772943807154174 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_23 (k : ℕ) (lo : 1033663869923839772943807154175≤k) (hi : k≤8606338612891744630593965469694) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,89,97,101,107,113,127,139,149,151,163,173,191,227,229,233,257,277,281,313,317,379,431,457,463,479,509,521,523,541,577,613,787,853,877,911,967,1229,1279,1327,1543,1567,1667,1721,1789,1877,1933,2063,2131,2137,2311,2383,2411,2447,2777,2957,3217,3373,4001,4729,5569,5641,5749,5867,8933,9133,13411,13721,16903,19531]
  let factors : List (ℕ × ℕ × List ℕ) := [(2,1,[53,277]),(7,1,[3,13,521]),(7,1,[7,2957]),(3,1,[3,13,577]),(5,1,[19,1229]),(2,1,[3,73,107]),(3,2,[5,5,541]),(5,3,[3,2383]),(5,1,[29363]),(2,1,[113,277]),(2,2,[5,7,479]),(5,1,[46703]),(2,1,[3,16903]),(3,1,[3,3,13,463]),(5,1,[62603]),(3,5,[4001]),(6,6,[5,509]),(3,1,[3,5,5569]),(2,2,[46867]),(11,2,[3,139,257]),(2,1,[3,3,5,5641]),(10,1,[3,11,9133]),(37,4,[3,3,3,5,7,41]),(2,1,[5,5,13721]),(2,1,[23,19531]),(2,1,[3,167071]),(13,1,[5,108343]),(5,1,[686051]),(14,2,[3,5,29,853]),(11,1,[5,457,523]),(2,1,[3,7,57193]),(2,2,[3,5,23,1789]),(3,1,[3,229,1933]),(5,7,[3,29,317]),(3,1,[3,3,3,5,101,139]),(18,2,[3,5,7,11,877]),(2,1,[5,619921]),(2,2,[3,13,31,1327]),(2,2,[3,3,3,29,2131]),(2,2,[1667,1877]),(2,1,[5,5,13,128033]),(3,1,[3,5,5,898427]),(5,2,[3,11,1083431]),(2,1,[3,5,7,787,1279]),(3,1,[3,53,2390111]),(5,4,[3,3,3,13,1002427]),(11,1,[3,13,23,3530113]),(2,1,[1721,6674293]),(12,1,[3,3,23,47,71,151,191]),(2,2,[3,3,11,1543,125207]),(3,1,[3,11,47,4729,5867]),(3,1,[3,11,71,79,97,3217]),(2,1,[7,59,61,2468821]),(2,1,[7,7,911,3790531]),(10,12,[3,3,3,5629630033]),(10,12,[3,3,3,3,3,3,149,1484221]),(5,12,[3,3,3,6333022723]),(5,18,[3,1567,602779]),(10,12,[3,3,3,3,19,2777,45007]),(15,14,[3,3,17,19,173,101419]),(5,13,[3,19,19,79,613,2063]),(13,12,[3,76504982797]),(10,13,[3,17,40639,58727]),(10,12,[3,86065123387]),(5,13,[3,3,93407,162881]),(5,15,[3,967,12515837]),(11,1,[5,7,11,13,124394014907]),(5,13,[3,3,3,5629630033]),(5,13,[3,3,127,134764051]),(14,1,[5,7,11,13,17,41399,187469]),(7,13,[3,3,3,3,3,3,149,1484221]),(5,13,[3,19,79,541,67061]),(11,1,[5,7,11,13,19,89,163,507691]),(10,13,[3,3,3,6333022723]),(11,12,[3,115518667507]),(7,1,[5,5,5,7,7,11,11,13,5749,13411]),(5,19,[3,1567,602779]),(5,13,[3,3,97,227,379,2447]),(7,1,[5,7,11,13,67,379,6199211]),(5,13,[3,3,3,3,19,2777,45007]),(5,12,[3,54101,2402107]),(14,1,[5,7,7,11,13,73,79,463,8933]),(5,15,[3,3,17,19,173,101419]),(5,13,[3,3,22972916507]),(7,1,[5,7,11,13,233,760055299]),(5,14,[3,19,19,79,613,2063]),(11,1,[5,7,11,13,37,61,83221451]),(5,13,[3,76504982797]),(14,1,[5,5,7,11,13,39844360639]),(10,14,[3,17,40639,58727]),(14,1,[5,7,11,11,11,13,431,4051741]),(5,13,[3,86065123387]),(21,1,[5,5,7,11,13,31,3373,428677]),(7,14,[3,3,93407,162881]),(7,1,[5,7,11,13,19,59,281,313,2411]),(15,16,[3,967,12515837]),(22,1,[5,7,11,13,17,2311,6417373]),(5,14,[3,3,127,134764051]),(7,1,[5,5,7,11,11,13,23,211380331]),(5,14,[3,19,79,541,67061]),(14,1,[5,7,11,11,13,19,23,43,1372103]),(5,13,[3,115518667507]),(7,1,[5,7,11,13,53,2137,2655943]),(5,14,[3,3,97,227,379,2447]),(14,1,[5,7,11,13,23,97,143012893]),(7,13,[3,54101,2402107]),(11,1,[5,7,11,13,338411026619]),(5,14,[3,3,22972916507])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [103765340768256,110057860601856,116730274830336,123804672720896,131311651239936,139276917989376,147724981293056,156682204768256,166184187498496,176261372696576,186952403767296,198292510785536,210309543653376,223052929028096,236582231054336,250929645735936,266150688372736,282291198038016] 1033663869923839772943807154175 8606338612891744630593965469694 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_24 (k : ℕ) (lo : 8606338612891744630593965469695≤k) (hi : k≤71669396469699673331911983230974) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,97,109,113,131,139,151,179,263,277,293,311,347,353,421,431,439,449,463,491,557,563,601,607,613,619,673,761,773,787,821,857,863,883,887,947,971,1051,1259,1427,1483,1531,1571,1873,1877,1933,1951,2207,2693,2749,3461,4079,4297,4339,4483,4759,5471,6703,6907,7369,8233,8501,8513,8581,8647,8849,11083,13687,14797,15809,19457]
  let factors : List (ℕ × ℕ × List ℕ) := [(2,1,[37,293]),(11,1,[109,131]),(3,4,[7,7,37]),(2,2,[3,3,3,431]),(2,1,[3,3,3,3,7,47]),(2,1,[31,863]),(3,1,[3,19,557]),(5,3,[3,7,607]),(3,2,[5,7,761]),(3,3,[15809]),(5,1,[3,11,1951]),(2,1,[3,21683]),(3,4,[7,1531]),(5,1,[11,19,439]),(2,2,[5,17,619]),(2,1,[3,3,3,3,1933]),(10,2,[3,5,7,1051]),(3,1,[3,31,47,61]),(10,1,[3,7,7,2207]),(3,1,[3,5,41,773]),(2,1,[3,5,13,41,71]),(2,1,[11,63499]),(2,2,[3,7,113,151]),(3,1,[3,13,19457]),(7,3,[3,53,2749]),(2,2,[5,210461]),(6,1,[3,3,5,53507]),(7,1,[5,648859]),(3,6,[101977]),(2,1,[7,7,7,23,421]),(2,2,[11,41,4297]),(3,1,[3,179,7369]),(13,3,[3,5,43,43,73]),(13,2,[3,3,17,29009]),(3,6,[7,47,1877]),(3,1,[3,1427,11083]),(3,3,[13,37,28559]),(10,1,[3,5,5,11,106541]),(2,1,[3,3,16197241]),(2,1,[17,787,13687]),(6,1,[5,5,7751789]),(5,1,[37,6642539]),(11,1,[3,5,11,29,53299]),(3,3,[491,130099]),(2,2,[3,5,31,673,887]),(6,2,[3,5,23,179,8849]),(5,2,[3,511028873]),(11,7,[3,5,5,7,183503]),(17,1,[3,3,3,1483,950791]),(2,2,[3,5,5,5,37,1396979]),(2,1,[439,4339,126473]),(2,1,[883,491547887]),(10,17,[3,3,29,29,37,109,449]),(15,13,[3,77532334501]),(10,17,[3,3,5471,313147]),(5,13,[3,3,3,19,510071431]),(5,14,[3,3,3,41,2693,46549]),(10,13,[3,3,3,3,8233,441421]),(11,13,[3,947,109895033]),(10,14,[3,3,3,6132346477]),(11,14,[3,3,3,37,175792651]),(5,14,[3,1571,39522113]),(5,15,[3,347,94892647]),(5,13,[3,3,53,613,1433293]),(11,1,[5,7,7,11,11,13,19,31,7914307]),(17,18,[3,3,29,29,37,109,449]),(5,15,[3,1259,3461,8501]),(11,1,[5,5,7,11,13,76141244863]),(5,14,[3,77532334501]),(10,14,[3,3,353,8581,8647]),(11,1,[5,5,7,11,13,277,291550339]),(7,18,[3,3,5471,313147]),(5,13,[3,3,8513,6526529]),(11,1,[5,5,7,11,13,13,17,387589451]),(10,14,[3,3,3,19,510071431]),(5,13,[3,3,3,4079,4815631]),(7,1,[5,7,11,13,179,4759,533263]),(5,15,[3,3,3,41,2693,46549]),(5,16,[3,6703,3496729]),(11,1,[5,7,11,13,481816852667]),(5,14,[3,3,3,3,8233,441421]),(5,13,[3,3,17,601,6488591]),(7,1,[5,5,7,7,7,11,13,311,971,6907]),(5,14,[3,947,109895033]),(11,1,[5,7,11,13,128767,4209221]),(5,15,[3,3,3,6132346477]),(11,1,[5,7,11,13,263,2185879981]),(5,15,[3,3,3,37,175792651]),(7,1,[5,7,7,7,11,13,97,113,1135291]),(5,15,[3,1571,39522113]),(7,1,[5,7,11,13,13,23,563,857,4483]),(10,16,[3,347,94892647]),(7,1,[5,7,11,13,1873,366236747]),(5,14,[3,3,53,613,1433293]),(7,1,[5,7,11,13,59,12331401601]),(5,16,[3,1259,3461,8501]),(7,1,[5,5,7,11,13,139,1110328861]),(10,15,[3,3,353,8581,8647]),(14,1,[5,7,11,13,13,13,61,463,171473]),(5,14,[3,3,8513,6526529]),(7,1,[5,7,11,13,868073568443]),(5,14,[3,3,3,4079,4815631]),(11,1,[5,7,11,13,41,14797,1517647]),(5,17,[3,6703,3496729]),(11,1,[5,7,11,13,67,821,17753509]),(5,14,[3,3,17,601,6488591])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [299413752446976,317572442116096,336834180612096,357262191415296,378933515329536,401915557933056,426273162244096,452125641056256,479551101198336,508635050172416,539488231571456,572206157131776,606900205961216,643708530794496,682725474840576,724118035009536,768035208790016,814619864027136] 8606338612891744630593965469695 71669396469699673331911983230974 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_25 (k : ℕ) (lo : 71669396469699673331911983230975≤k) (hi : k≤596696160471664649054305859444734) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,59,61,67,71,73,79,83,97,101,107,109,127,131,139,151,173,181,191,193,223,227,233,251,257,263,271,283,353,359,367,383,389,409,419,439,571,587,593,619,641,647,709,797,823,1093,1297,1553,1579,1789,1907,2137,2399,2531,2753,2819,3203,3329,3541,3593,4003,4219,4363,5179,5209,5639,5743,7109,7669,7759,9151,9187,10091,11489,12251,13687,14369,17189,17341]
  let factors : List (ℕ × ℕ × List ℕ) := [(7,1,[97,107]),(3,1,[3,3541]),(2,2,[5743]),(11,9,[3,3,5]),(3,1,[3,3,11,131]),(2,2,[61,109]),(2,2,[13,619]),(2,2,[9187]),(17,1,[5,13,283]),(5,1,[7,2753]),(3,3,[5,29,47]),(17,1,[5,71,101]),(2,2,[3,7,11,79]),(2,1,[3,7,47,47]),(5,1,[3,17341]),(3,1,[3,5,3593]),(3,3,[19,23,31]),(2,1,[3,7,43,83]),(5,1,[3,36791]),(2,2,[11,5639]),(2,1,[7,20759]),(2,2,[3,67,389]),(6,1,[5,13,13,193]),(2,1,[173,1093]),(2,2,[3,17,1907]),(2,2,[3,36749]),(3,1,[3,151,641]),(5,1,[326171]),(3,1,[3,3,3,3,4219]),(11,3,[3,32189]),(3,1,[3,17,7759]),(3,1,[3,359,383]),(7,1,[5,107791]),(3,1,[3,3,7,67,139]),(5,1,[652343]),(10,3,[3,7,11,709]),(7,3,[3,5,13687]),(2,2,[3,7,25939]),(6,2,[3,5,11,41,131]),(3,1,[3,251,3203]),(6,1,[3,11,104047]),(2,2,[5,17,21247]),(3,4,[11,223,257]),(5,3,[3,23,37,593]),(7,1,[3,7,587,647]),(2,2,[5,7,29,4363]),(11,1,[5,11,71,4003]),(7,1,[5,5,7,73,1553]),(3,4,[5,383,1579]),(6,2,[3,11,389029]),(3,1,[3,13,772537]),(7,1,[7,11,580747]),(2,1,[48380561]),(3,3,[41,440989]),(2,1,[3,19,127,10091]),(6,1,[3,139,378179]),(2,2,[37,2178877]),(2,2,[3,3,7,59,79,353]),(10,2,[5,7,109,108377]),(2,2,[414623917]),(11,5,[3,17713781]),(6,1,[3,22973,54521]),(2,2,[3,1653833021]),(7,1,[3,3,5,7,11,23,248117]),(3,3,[7109,1173439]),(5,3,[3,1297,4823719]),(2,2,[7669,6867103]),(2,2,[5,109,96761123]),(2,1,[181,227,15951139]),(10,13,[3,210939248141]),(5,15,[3,1789,31263431]),(5,14,[3,3,39547368631]),(5,15,[3,37,1700522977]),(5,15,[3,66735822809]),(10,14,[3,439,322473797]),(5,14,[3,150152725033]),(5,14,[3,3,367,144644393]),(5,15,[3,19,367,12111433]),(10,16,[3,233,233,824983]),(5,17,[3,2531,2819,3329]),(5,14,[3,3,3,71,315401287]),(7,1,[5,7,11,13,17189,60257887]),(5,14,[3,210939248141]),(10,14,[3,312757,683479]),(7,1,[5,7,7,11,13,47,11489,290627]),(7,16,[3,1789,31263431]),(5,15,[3,823,5179,26597]),(11,1,[5,7,7,11,13,23041,7223981]),(7,15,[3,3,39547368631]),(5,19,[3,7515065599]),(7,1,[5,7,11,13,23,271,2137,92779]),(7,16,[3,37,1700522977]),(10,16,[3,23,31,89435039]),(7,1,[5,7,11,13,1310768896187]),(5,16,[3,66735822809]),(10,15,[3,3,3,9151,1642441]),(11,1,[5,7,7,11,13,191,797,1304687]),(7,15,[3,439,322473797]),(5,14,[3,3,72997,1310233]),(11,1,[5,7,7,11,13,210655251629]),(5,15,[3,150152725033]),(7,1,[5,7,11,13,23,41,1658495669]),(7,15,[3,3,367,144644393]),(21,1,[5,7,11,11,13,17,139,5209,12251]),(7,16,[3,19,367,12111433]),(7,1,[5,7,11,13,31,71711,791419]),(5,17,[3,233,233,824983]),(11,1,[5,7,11,13,131,359,39679151]),(5,18,[3,2531,2819,3329]),(11,1,[5,7,11,13,38543,51351829]),(5,15,[3,3,3,71,315401287]),(7,1,[5,7,11,13,14369,146097499]),(7,15,[3,312757,683479]),(14,1,[5,7,11,13,220747,10086737]),(5,16,[3,823,5179,26597]),(14,1,[5,7,7,11,13,17,19845996253]),(5,20,[3,7515065599]),(11,1,[5,7,11,13,17,263,409,571,2399]),(5,17,[3,23,31,89435039]),(14,1,[5,5,7,11,13,149899,3544861]),(7,16,[3,3,3,9151,1642441]),(11,1,[5,7,11,13,17,367,419,1077911]),(15,15,[3,3,72997,1310233])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [864007160385536,916361675718656,971916131475456,1030870632841216,1093399720902656,1159708646465536,1230051123470336,1304604481069056,1383678317510656,1467596868386816,1556614052642816,1651027332243456,1751145198411776,1857369624559616,1970029356384256,2089523046219776,2216260375658496,2350524292325376] 71669396469699673331911983230975 596696160471664649054305859444734 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_26 (k : ℕ) (lo : 596696160471664649054305859444735≤k) (hi : k≤4959726881428298139407231799607294) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,137,139,149,151,157,163,167,173,181,191,193,251,263,277,293,433,439,457,479,547,571,719,773,811,929,971,1019,1051,1129,1303,1493,1669,1709,1723,1831,2213,2423,2441,2659,3067,3253,3433,3529,3559,3767,3929,3947,4327,5279,9661,10321,11093,11173,11197,11789,13477,14731,15731,16661]
  let factors : List (ℕ × ℕ × List ℕ) := [(2,2,[3,29,71]),(2,1,[5,3253]),(7,1,[5,41,83]),(19,1,[13,17,79]),(17,5,[3,3,3,5,11]),(3,5,[41,43]),(7,3,[3,5,571]),(2,1,[3,67,181]),(3,1,[3,13477]),(3,1,[3,11,1303]),(2,2,[151,163]),(2,2,[24709]),(2,1,[5,71,167]),(3,5,[11,433]),(2,1,[71,1831]),(2,2,[3,37,719]),(2,2,[85999]),(5,1,[7,7,5279]),(3,1,[3,3,3,11093]),(2,2,[101,1493]),(2,2,[7,37,811]),(2,1,[149,3529]),(3,1,[3,7,34031]),(11,4,[3,7,7,929]),(7,1,[7,73,2441]),(2,1,[479,2659]),(11,1,[5,43,43,151]),(5,1,[7,7,107,277]),(2,2,[5,43,43,89]),(2,1,[3,3,433,433]),(2,2,[3,5,7,61,137]),(11,1,[59,47521]),(3,4,[89,3947]),(2,2,[157,9661]),(5,1,[3,3,343997]),(5,1,[17,19,11197]),(2,1,[1723,2423]),(2,2,[2185009]),(3,3,[11,11,43,263]),(3,3,[19,98453]),(2,1,[3,2791991]),(2,1,[7,139,16661]),(5,3,[3,3,517343]),(3,1,[3,3,457,10321]),(3,6,[3374803]),(3,4,[7,3509941]),(2,1,[3,23,23,41,3067]),(5,3,[3,7,5607479]),(2,1,[17,37248697]),(2,2,[7,17,3291221]),(3,1,[3,191,1429303]),(2,1,[3,5,53,1051643]),(7,1,[1266455699]),(5,6,[3,3,13,19,19,29,103]),(7,1,[3,3,5,151,840197]),(2,2,[7,163,173,15731]),(6,1,[3,5,5,5,3559,14731]),(2,1,[5,7,11,11173,11789]),(2,1,[3,2213,16751947]),(2,1,[3,39320721751]),(2,1,[3,3,7,1051,1669,1709]),(5,14,[3,3,101423242691]),(5,14,[3,193,1672112371]),(5,14,[3,56417,6067109]),(10,15,[3,72763,2494703]),(5,14,[3,31,12420757133]),(5,15,[3,47,773,5620529]),(5,14,[3,3,61,73,32422307]),(5,14,[3,3,29,263,293,68521]),(5,16,[3,3,79,83,6191947]),(5,20,[3,8074362817]),(5,18,[3,3,11418277231]),(5,16,[3,3,80863,599023]),(22,1,[5,7,7,11,13,13,13,17,17,8740037]),(5,15,[3,3,101423242691]),(5,16,[3,97,547,2904623]),(11,1,[5,7,7,11,13,17,17,1566621197]),(5,15,[3,193,1672112371]),(5,16,[3,3,3,3,3,3,3,31,7233263]),(11,1,[5,7,11,13,17,17,137,84900547]),(7,15,[3,56417,6067109]),(10,15,[3,251,4327,319237]),(7,1,[5,7,11,13,17,971,215987393]),(5,16,[3,72763,2494703]),(11,17,[3,152417,603173]),(11,1,[5,7,11,13,17,222432352267]),(7,15,[3,31,12420757133]),(5,16,[3,83,157,14964857]),(7,1,[5,7,11,13,17,235924330507]),(7,16,[3,47,773,5620529]),(5,15,[3,23,53,3433,98837]),(11,1,[5,5,5,7,11,13,17,3929,2547323]),(5,15,[3,3,61,73,32422307]),(7,1,[5,7,11,13,17,59,67,71,251,3767]),(5,15,[3,3,29,263,293,68521]),(11,1,[5,7,11,13,17,31,34919,260003]),(5,17,[3,3,79,83,6191947]),(7,1,[5,5,7,11,13,17,31,37,439,118571]),(5,21,[3,8074362817]),(7,1,[5,5,5,5,7,11,13,17,2532911399]),(7,19,[3,3,11418277231]),(7,1,[5,5,7,11,13,17,41,1637981239]),(5,17,[3,3,80863,599023]),(14,1,[5,7,11,13,17,32531,10947113]),(5,17,[3,97,547,2904623]),(7,1,[5,7,11,13,17,377721460747]),(5,17,[3,3,3,3,3,3,3,31,7233263]),(7,1,[5,7,11,13,17,1019,393113393]),(5,16,[3,251,4327,319237]),(14,1,[5,7,11,11,13,17,41,942056473]),(7,18,[3,152417,603173]),(7,1,[5,7,11,13,17,1129,399120979]),(5,17,[3,83,157,14964857]),(7,1,[5,7,11,11,11,11,13,17,43,8349659]),(5,16,[3,23,53,3433,98837])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [2492577612374016,2643703296843776,2804024020606976,2974057666789376,3154276115439616,3345603610198016,3548197676752896,3763190966624256,3991201036271616,4233291532599296,4489849299664896,4761727485444096,5050085925093376,5356405081276416,5680594341871616,6024974771224576,6389991065747456,6776680385724416] 596696160471664649054305859444735 4959726881428298139407231799607294 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_27 (k : ℕ) (lo : 4959726881428298139407231799607295≤k) (hi : k≤41203610185680866539752074506960894) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,97,101,103,113,127,139,163,167,173,181,197,223,227,229,239,251,257,277,281,307,347,353,433,463,479,523,593,599,601,641,701,727,743,823,863,887,911,1013,1021,1039,1163,1201,1283,1373,1567,1733,1759,1783,1933,1987,2069,2143,2221,2243,3041,3067,3413,3677,4391,4931,4993,5693,5849,7193,8209,8669,9157,10729,12613,13399,13907,17099,18793,19069,19751]
  let factors : List (ℕ × ℕ × List ℕ) := [(3,3,[3041]),(11,1,[19,641]),(5,5,[3,307]),(6,1,[3,4993]),(11,1,[5,3067]),(6,1,[3,23,227]),(2,2,[17,479]),(7,1,[13,1283]),(2,2,[3,3,3,7,47]),(5,3,[3,7,7,31]),(2,2,[9157]),(5,3,[3,1733]),(15,1,[3,3,3,5,5,31]),(11,1,[5,5,863]),(2,1,[3,5,1987]),(5,1,[30671]),(3,1,[3,3,5,5,163]),(3,1,[3,7,1783]),(3,2,[5,13,13,41]),(17,3,[3,5,11,113]),(2,1,[3,71,353]),(3,3,[19751]),(13,1,[5,31,601]),(5,1,[3,31327]),(2,1,[5,29473]),(11,3,[3,3,4391]),(3,1,[3,3,3,3,2143]),(2,2,[3,29959]),(2,2,[3,5,5,5,593]),(2,2,[347167]),(2,1,[5,359509]),(5,3,[3,150379]),(5,4,[3,127,727]),(5,1,[3,3,3,3,7,11,13,31]),(5,7,[3,7,19,101]),(5,1,[3,173,8209]),(6,2,[3,23,71,743]),(2,2,[4431793]),(3,2,[5,7,138581]),(2,2,[353,17099]),(2,2,[3,7,17,17,17,59]),(3,1,[3,29,257,911]),(2,1,[24143789]),(11,1,[5,101,186311]),(2,1,[23,181,59611]),(3,4,[4931,7193]),(6,2,[3,7,11,13,61343]),(2,2,[11,823,24329]),(2,2,[59,277,24359]),(2,1,[5,5,29,887,2243]),(2,2,[53,19401341]),(17,6,[3,5,229,18793]),(5,1,[2884834451]),(3,3,[31,1373,19069]),(2,2,[17,188174111]),(5,3,[3,567498929]),(3,1,[3,4113084293]),(5,1,[43,197,257,5849]),(2,2,[3,1987,1388669]),(2,2,[3,3,3,5693,158009]),(2,1,[97,281,1933,2221]),(5,1,[139,881001749]),(5,1,[19,6493070777]),(2,1,[3,23,4131453121]),(2,1,[103,167,24348829]),(3,1,[3,3,523,599,187963]),(5,15,[3,29,1039,14559829]),(5,15,[3,3,3,3,3,3,47,40738099]),(11,16,[3,246736689527]),(10,16,[3,3,223,10729,36457]),(5,15,[3,53,35533,294731]),(5,16,[3,23,12795839549]),(5,16,[3,36629,8520943]),(5,16,[3,43,347,1759,12613]),(5,15,[3,3,234039123203]),(10,15,[3,3,3,59,61,307,74887]),(5,19,[3,31,1592396549]),(10,15,[3,837648415259]),(7,1,[5,7,11,13,17,37,463,3413,8669]),(5,16,[3,29,1039,14559829]),(10,17,[3,3,3,24678505759]),(7,1,[5,7,7,11,13,17,29,41,433,149161]),(5,16,[3,3,3,3,3,3,47,40738099]),(5,15,[3,37,25467095807]),(11,1,[5,7,11,13,17,570140530699]),(5,17,[3,246736689527]),(10,17,[3,19,41593,316153]),(7,1,[5,7,11,13,17,239,701,3609097]),(5,17,[3,3,223,10729,36457]),(5,15,[3,1059920725519]),(11,1,[5,5,7,11,13,13,13,17,23,1013,32573]),(7,16,[3,53,35533,294731]),(5,16,[3,19,29,13907,73351]),(7,1,[5,7,7,11,13,17,97150885597]),(5,17,[3,23,12795839549]),(10,16,[3,1201,496321187]),(7,1,[5,5,5,5,7,11,13,17,5769668903]),(5,17,[3,36629,8520943]),(11,1,[5,7,11,13,17,43151,17727173]),(5,17,[3,43,347,1759,12613]),(7,1,[5,7,11,13,13,17,17,1021,3595091]),(15,16,[3,3,234039123203]),(7,1,[5,5,7,11,13,17,33359,5158273]),(5,16,[3,3,3,59,61,307,74887]),(7,1,[5,7,11,13,17,67,13619974297]),(5,20,[3,31,1592396549]),(7,1,[5,7,11,13,13,17,59,251,5027023]),(5,16,[3,837648415259]),(11,1,[5,7,11,13,17,31,33111423637]),(5,18,[3,3,3,24678505759]),(14,1,[5,7,11,13,17,19,1163,3677,13399]),(5,16,[3,37,25467095807]),(7,1,[5,7,11,13,17,1567,736852117]),(7,18,[3,19,41593,316153]),(22,1,[5,5,7,11,13,17,244918486223]),(5,16,[3,1059920725519]),(11,1,[5,7,11,13,13,17,2069,48287579]),(5,17,[3,19,29,13907,73351]),(11,1,[5,7,11,13,17,37,41851,889501]),(7,17,[3,1201,496321187])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [7187696969302016,7622980873076736,8085067842420736,8574646529458176,9093969690935296,9643763617857536,10227339137744896,10847560987672576,11503490983673856,12200822355050496,12940553229172736,13724031635603456,14555974980796416,15438357214969856,16373860456923136,17365741166903296,18417938881150976,19532406639394816] 4959726881428298139407231799607295 41203610185680866539752074506960894 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_28 (k : ℕ) (lo : 41203610185680866539752074506960895≤k) (hi : k≤342914391149760390443021924737744894) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,43,47,53,59,61,67,71,73,79,83,101,103,109,113,131,137,157,163,167,179,181,193,199,227,229,251,263,269,293,311,313,337,347,373,421,593,653,659,677,701,719,769,823,881,971,1013,1019,1031,1069,1229,1301,1493,1597,1619,1667,1723,1811,1867,1871,2113,2417,3137,3413,3761,4003,4157,4261,4391,4517,5471,5783,5807,5927,8039,9043,10639,12107,13711,17923]
  let factors : List (ℕ × ℕ × List ℕ) := [(6,2,[3,7,313]),(3,1,[3,4517]),(3,3,[3761]),(6,6,[5,101]),(2,2,[3,3,3,5,61]),(2,1,[5,5,677]),(2,1,[3,73,79]),(2,1,[3,5,23,53]),(13,3,[3,5,347]),(13,2,[3,11,19,19]),(10,1,[3,5,1723]),(5,1,[71,373]),(2,1,[19,1667]),(5,1,[43,881]),(10,2,[3,5,5,263]),(2,1,[7,5807]),(5,1,[31,1493]),(5,1,[13,4391]),(17,1,[5,5,5,5,5,19]),(3,3,[47,337]),(2,2,[3,10639]),(5,3,[3,3,7,293]),(2,2,[3,3,3,19,79]),(11,2,[3,7,2113]),(3,1,[3,19,1619]),(5,1,[13,79,113]),(5,3,[3,7,31,59]),(3,1,[3,3,5,4003]),(2,1,[3,3,103,227]),(11,1,[5,11,4157]),(7,4,[3,5,11,179]),(19,1,[5,51691]),(3,1,[3,5,7,11,229]),(3,3,[5,13711]),(3,2,[5,37,971]),(3,3,[43,3413]),(7,1,[11,11,37,227]),(2,1,[5,7,11,17,193]),(14,3,[3,23,61,79]),(3,3,[7,52967]),(5,1,[2526371]),(2,1,[2966153]),(3,1,[3,3,457271]),(7,1,[3,5,7,61,701]),(3,1,[3,5,11,23,1871]),(17,2,[3,3,3,5,11,11,13,19]),(2,2,[83,81299]),(2,2,[1229,5783]),(2,1,[3,5932307]),(2,2,[3,137,30089]),(2,2,[3,5052743]),(2,1,[1031,34603]),(3,4,[11,516911]),(2,1,[3,3,23,29,73,167]),(13,1,[19,23,184567]),(2,1,[11,8979811]),(11,3,[3,3,3,5,5,126713]),(2,1,[3,11,17,269,32941]),(2,2,[3,5,7,7,16138981]),(2,2,[13,26293,36571]),(5,7,[3,881,2660089]),(2,1,[3,23,23,23,269,78901]),(10,1,[3,12107,26991269]),(2,1,[3,2417,161311559]),(2,1,[3,3,7,103,1811,118751]),(5,16,[3,67,181,823,63347]),(5,16,[3,47,109,311,420859]),(10,16,[3,3,593,1301,307273]),(5,16,[3,3,3,3,59,659,718541]),(5,20,[3,50001187757]),(5,16,[3,31,769,35593843]),(10,16,[3,899918749057]),(10,21,[3,3,3,67,49466317]),(5,17,[3,19,73,1013,360271]),(10,18,[3,3,3,3,9942186739]),(10,16,[3,31,251,146365147]),(5,17,[3,3,1019,197555843]),(7,1,[5,7,11,13,17,177493,8230879]),(5,17,[3,67,181,823,63347]),(5,16,[3,3,3,3,47448604141]),(7,1,[5,7,11,13,17,1549421385739]),(5,17,[3,47,109,311,420859]),(5,19,[3,1867,90976337]),(7,1,[5,7,11,13,17,27103,60632917]),(5,17,[3,3,593,1301,307273]),(10,22,[3,47653,472561]),(7,1,[5,7,11,13,17,29,1069,3137,17923]),(10,17,[3,3,3,3,59,659,718541]),(26,18,[3,23,181,719,127669]),(7,1,[5,7,11,13,17,131,163,373,232103]),(7,21,[3,50001187757]),(11,16,[3,114167,14200891]),(7,1,[5,7,11,13,17,1960699762699]),(5,17,[3,31,769,35593843]),(5,19,[3,43,33851,147673]),(14,1,[5,7,11,11,13,17,17,5471,2032559]),(5,17,[3,899918749057]),(7,1,[5,7,11,13,17,47,137,2113,162109]),(5,22,[3,3,3,67,49466317]),(11,1,[5,7,11,13,17,2339340228619]),(5,18,[3,19,73,1013,360271]),(7,1,[5,7,11,13,13,17,653,9043,32321]),(5,19,[3,3,3,3,9942186739]),(7,1,[5,7,11,13,17,92567,28429229]),(7,17,[3,31,251,146365147]),(7,1,[5,7,11,13,17,2791023515659]),(5,18,[3,3,1019,197555843]),(14,1,[5,7,7,11,13,17,5927,71351387]),(5,17,[3,3,3,3,47448604141]),(11,1,[5,7,7,11,13,17,199,4261,528991]),(5,20,[3,1867,90976337]),(19,1,[5,7,11,13,17,31,157,684250201]),(7,23,[3,47653,472561]),(7,1,[5,5,7,11,13,17,17,75767,548441]),(5,19,[3,23,181,719,127669]),(11,1,[5,5,7,11,13,17,19,593,1597,41641]),(5,17,[3,114167,14200891]),(21,1,[5,7,11,13,17,421,8039,1174073]),(7,20,[3,43,33851,147673])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [20717111338172416,21972086434267136,23303844848173056,24717393945133056,26215022726742016,27804356551540736,29488537569099776,31277123267198976,33173793892007936,35184842106863616,37318400698187776,39579039304974336,41979488233291776,44525897955147776,47225659631599616,50087653250564096,53125877687812096,56348320750370816] 41203610185680866539752074506960895 342914391149760390443021924737744894 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_29 (k : ℕ) (lo : 342914391149760390443021924737744895≤k) (hi : k≤2855961681505938789824544240495230974) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,83,89,97,101,103,109,113,131,137,139,151,167,181,269,293,317,337,359,379,419,463,479,491,569,641,659,691,709,739,769,821,839,947,1009,1031,1109,1637,1657,1753,1823,1951,2141,2309,2593,2633,2657,2897,3449,3491,3593,3623,4093,4259,4423,4451,4933,4999,7043,7499,7589,8447,9059,9479,11351,12041,15619,16189,17387,18287,18301]
  let factors : List (ℕ × ℕ × List ℕ) := [(3,1,[3,3491]),(3,3,[37,71]),(2,1,[3,5,739]),(2,2,[13,463]),(2,1,[12041]),(2,1,[5,2593]),(3,4,[1657]),(2,2,[3,3,5,5,37]),(7,1,[7,7,11,37]),(2,2,[11,947]),(2,2,[3,4093]),(2,1,[7,3623]),(2,1,[3,3,5,7,7,13]),(2,2,[11,19,71]),(6,2,[3,5,1109]),(2,2,[7,41,59]),(2,1,[41669]),(15,1,[11,23,167]),(2,1,[7,17,17,23]),(2,1,[19,23,109]),(11,1,[61,839]),(2,1,[11,13,13,31]),(10,1,[13,4451]),(2,1,[3,20947]),(2,1,[7,9059]),(2,1,[67733]),(5,1,[84503]),(2,2,[43,1009]),(13,1,[93059]),(3,3,[24077]),(3,1,[3,33301]),(2,2,[5,7,19,101]),(5,1,[3,49117]),(15,1,[3,13,47,83]),(3,3,[39887]),(6,2,[3,5,7,7,151]),(2,2,[7,18301]),(3,1,[3,125683]),(7,1,[3,5,83,317]),(3,5,[26513]),(2,2,[7,7,67,109]),(2,2,[3,5,25931]),(3,3,[31,7589]),(2,1,[5,101,2633]),(3,1,[3,7,66541]),(3,4,[199807]),(5,1,[3,3,186119]),(2,2,[3,7,11,4423]),(17,1,[5,754099]),(17,1,[5,789331]),(2,2,[7,304279]),(3,1,[3,5,19,16189]),(7,1,[19,268661]),(3,3,[1431389]),(3,1,[3,7,294703]),(5,1,[7893311]),(7,1,[10209119]),(3,1,[3,5,5,13,11351]),(2,2,[2309,2657]),(2,1,[11,641,1823]),(13,1,[17,1031,1637]),(3,5,[2659331]),(2,1,[23,2794723]),(17,3,[3,7,13,115727]),(7,3,[3,5,379,8447]),(13,4,[3,7,19,181,419]),(2,2,[3,101,181,7499]),(2,2,[19,22134451]),(10,4,[3,13,4086853]),(2,1,[139,20418239]),(5,4,[3,128557259]),(5,1,[3,53,103,491,709]),(2,2,[37,47,71,113,419]),(3,1,[3,5,9479,126827]),(2,1,[11,17,41,659,3593]),(13,3,[3,5,23,15786623]),(2,2,[29,131,3350143]),(2,1,[3,17,47,479,57331]),(3,1,[3,3,11402289727]),(2,2,[137,4933,102359]),(2,1,[13,23383546973]),(3,11,[53,269,21017]),(6,2,[3,3,19,1682218277]),(2,2,[3,3,3,5,2550196273]),(3,3,[5,43571079481]),(10,16,[3,3,607972221299]),(11,17,[3,19,50908773029]),(13,16,[3,3,89,24083,319097]),(5,18,[3,22171,24540053]),(5,17,[3,135467,8519813]),(10,18,[3,29,821,25707947]),(5,19,[3,3,3,36065793991]),(5,17,[3,1377105987421]),(5,18,[3,1753,4999,83339]),(10,19,[3,3,3,50723,848417]),(5,17,[3,3,59357,9227731]),(5,17,[3,1742843179241]),(7,1,[5,5,5,7,11,13,17,23,29,252747769]),(7,17,[3,3,607972221299]),(5,18,[3,23,83,484156177]),(7,1,[5,7,11,13,17,17,169007,1555861]),(5,18,[3,19,50908773029]),(5,18,[3,3,3,3,36307645859]),(7,1,[5,7,11,11,13,17,97,359,12377527]),(5,17,[3,3,89,24083,319097]),(5,17,[3,337,6170748433]),(14,1,[5,7,7,11,13,17,95267,7540991]),(7,19,[3,22171,24540053]),(5,17,[3,192617,11451113]),(21,1,[5,7,7,11,13,17,19,67,3449,173549]),(19,18,[3,135467,8519813]),(10,17,[3,59,691,57383399]),(7,1,[5,7,11,13,17,19,181,1645070629]),(5,19,[3,29,821,25707947]),(5,19,[3,1951,17387,18287]),(14,1,[5,7,11,13,17,15619,384169561]),(5,20,[3,3,3,36065793991]),(23,1,[5,7,11,13,17,23,276705446957]),(5,18,[3,1377105987421]),(7,1,[5,7,11,11,13,17,613661427713]),(5,19,[3,1753,4999,83339]),(22,1,[5,7,11,13,17,19,293,2897,443941]),(5,20,[3,3,3,50723,848417]),(7,1,[5,7,11,13,17,37,205241215087]),(7,18,[3,3,59357,9227731]),(7,1,[5,7,7,11,13,17,1150637301469]),(5,18,[3,1742843179241]),(14,1,[5,5,7,7,11,13,17,43,5676270443]),(5,19,[3,23,83,484156177]),(7,1,[5,5,5,7,11,13,17,4259,85098593]),(5,19,[3,3,3,3,36307645859]),(7,1,[5,7,11,13,17,73,131650665907]),(5,18,[3,337,6170748433]),(14,1,[5,7,11,13,17,769,7043,1882073]),(5,18,[3,192617,11451113]),(14,1,[5,7,7,11,11,13,17,569,2141,115259]),(7,18,[3,59,691,57383399]),(7,1,[5,7,7,11,13,17,512429,3196913]),(5,20,[3,1951,17387,18287])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [59766101242576896,63390789635342336,67234859732729856,71313328054337536,75638604278726656,80226616622841856,85089883499790336,90250017991622656,95724534724427776,101530546842894336,107688184178343936,114218970594738176,121143838886199296,128490725466832896,136284879055814656,144551381088403456,153319099192508416,162616387992027136] 342914391149760390443021924737744895 2855961681505938789824544240495230974 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_30 (k : ℕ) (lo : 2855961681505938789824544240495230975≤k) (hi : k≤23784947663657349347535370593630683134) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,107,109,127,131,149,157,191,193,199,211,263,277,317,353,373,419,487,523,557,569,577,599,613,827,907,929,941,997,1063,1087,1123,1297,1303,1493,1579,1609,1637,2003,2357,2417,2503,2543,2957,3079,3359,3391,3511,3581,5381,5503,5573,5711,5821,7591,8017,8689,9439,9511,11699,11903,11953,12119,15263,15427,16493,18061,19013]
  let factors : List (ℕ × ℕ × List ℕ) := [(2,2,[5503]),(3,5,[5,5,29]),(5,3,[3,3,3,131]),(3,3,[3581]),(2,1,[53,277]),(2,1,[16493]),(5,5,[7,149]),(2,2,[43,211]),(2,1,[22013]),(5,3,[3,11,13,13]),(5,1,[29363]),(2,1,[3,5,5,419]),(7,3,[3,5,557]),(5,2,[3,5573]),(3,1,[3,11953]),(2,1,[5,7,1087]),(2,2,[73,373]),(6,1,[7,19,19,23]),(2,1,[3,71,353]),(5,1,[76091]),(5,1,[3,28297]),(2,2,[3,3,5,1063]),(3,1,[3,3,12119]),(5,1,[116243]),(3,4,[15427]),(2,2,[3,7,3079]),(5,1,[7,19013]),(10,4,[3,3,2543]),(2,2,[5,5,5,5,199]),(5,1,[17,107,149]),(14,6,[3,3,3,5,71]),(2,2,[83,2003]),(6,1,[3,191341]),(2,2,[37,8017]),(7,1,[3,5,7,5821]),(14,2,[3,7,19,827]),(6,1,[5,5,28649]),(2,2,[3,19,9439]),(6,1,[7,11,19,907]),(2,2,[13,62851]),(2,1,[3,11,66877]),(2,2,[5,232487]),(2,2,[3,3,3,11,53,79]),(7,2,[3,41,11699]),(2,2,[3,3,3,3,7,43,67]),(3,4,[11,47,1123]),(7,3,[3,664997]),(11,1,[5,29,58727]),(19,1,[73,152183]),(2,2,[3,3,7,19,67,71]),(3,1,[3,19,218143]),(2,1,[3,5,5,169783]),(2,2,[5,5,258637]),(2,1,[19,1432451]),(6,1,[5,7,13,71719]),(7,1,[54433139]),(7,1,[67,1186517]),(11,2,[3,3,3,13,97,1637]),(3,3,[109,266183]),(3,3,[7,4649741]),(13,1,[3,3,3,5755909]),(2,2,[5,89,193,1303]),(2,1,[447632621]),(2,1,[941,613441]),(3,1,[3,232111577]),(2,2,[3,3,1579,32987]),(11,5,[3,5,4974157]),(3,1,[3,97,6534109]),(2,2,[23,29,827,2957]),(3,1,[3,5381,246833]),(2,2,[5,37,22218719]),(3,2,[5,895265243]),(5,3,[7,73,107,44617]),(2,1,[613,25863701]),(3,4,[5,317,2152093]),(11,2,[3,5,5,5,108866279]),(2,2,[5,31,71,15959929]),(5,3,[3,7,17,47,191,36293]),(3,2,[29,11903,1222411]),(2,1,[3,59,263,25467451]),(2,1,[3,2357,1154495963]),(10,17,[3,83,31708897427]),(5,17,[3,3,930491257417]),(5,17,[3,1579,1875113029]),(5,17,[3,191,16441852061]),(10,17,[3,1493,33377,66841]),(5,17,[3,929,3802851439]),(11,23,[3,3,19516189673]),(5,17,[3,15263,260385497]),(5,18,[3,3,702556074581]),(5,18,[3,89,1297,3391,5711]),(10,18,[3,2371070623003]),(10,21,[3,37,23201,366193]),(11,1,[5,7,11,13,17,17,542063,1319893]),(5,18,[3,83,31708897427]),(5,20,[3,3,997,222939757]),(11,1,[5,7,11,13,17,79,163299418501]),(17,18,[3,3,930491257417]),(10,19,[3,79,17905304861]),(14,1,[5,7,11,13,17,17,101,7969250239]),(5,18,[3,1579,1875113029]),(5,19,[3,3,1609,310819087]),(19,1,[5,7,7,11,13,13,17,47,47,7591,9511]),(5,18,[3,191,16441852061]),(5,18,[3,31,43,2387595361]),(11,1,[5,7,7,11,13,17,1579,1392669463]),(5,18,[3,1493,33377,66841]),(5,19,[3,1687841543429]),(11,1,[5,7,11,13,17,16326881908747]),(5,18,[3,929,3802851439]),(10,20,[3,19,523,599,150379]),(23,1,[5,7,11,13,17,108917,158993279]),(5,24,[3,3,19516189673]),(11,1,[5,5,7,11,13,17,17,8689,24868303]),(5,18,[3,15263,260385497]),(7,1,[5,5,7,11,13,13,17,83,83,157,487,569]),(7,19,[3,3,702556074581]),(7,1,[5,7,7,11,13,17,19,61,577,4413883]),(7,19,[3,89,1297,3391,5711]),(7,1,[5,7,11,13,17,3359,6524431253]),(10,19,[3,2371070623003]),(11,1,[5,7,11,13,17,31,44027,17030831]),(15,22,[3,37,23201,366193]),(7,1,[5,7,11,13,17,2653883,9289457]),(5,21,[3,3,997,222939757]),(14,1,[5,7,11,13,17,1148047,22776517]),(15,20,[3,79,17905304861]),(7,1,[5,7,11,13,17,2417,3511,3268253]),(15,20,[3,3,1609,310819087]),(14,1,[5,7,7,7,11,11,13,17,54577078481]),(5,19,[3,31,43,2387595361]),(7,1,[5,7,11,13,17,191,2503,65264291]),(5,20,[3,1687841543429]),(7,1,[5,7,11,13,17,29,127,18061,497501]),(5,21,[3,19,523,599,150379])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [172480167047397376,182942025138241536,194039216392830976,205808844383911936,218288057293275136,231528791200956416,245570497230667776,260457355064836096,276256289422442496,293008256982450176,310780968698249216,329623661802684416,349601956200185856,370807690761076736,393300864650182656,417158216576270336,442457533560651776,469287754885758976] 2855961681505938789824544240495230975 23784947663657349347535370593630683134 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_31 (k : ℕ) (lo : 23784947663657349347535370593630683135≤k) (hi : k≤197408778092644864465856335061493743614) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,73,79,83,89,97,103,107,127,149,151,173,181,191,199,229,251,271,277,283,317,349,409,419,449,457,467,509,521,587,593,619,641,683,797,877,977,1109,1259,1277,1439,1453,1723,1787,1789,1831,1871,1949,2179,2713,3137,3517,3823,4931,5653,5657,5791,6211,6637,7499,8167,8443,8867,10831,10957,11471,13043,14087,16447,16607,17393,18223,19699]
  let factors : List (ℕ × ℕ × List ℕ) := [(3,4,[23,59]),(2,2,[37,151]),(5,1,[11471]),(3,5,[5,181]),(6,4,[5,419]),(2,2,[8443]),(2,2,[5,11,11,17]),(2,1,[21713]),(11,4,[3,3,3,3,5,7]),(5,1,[22943]),(5,1,[7,7,587]),(2,2,[3,3,1787]),(2,1,[33773]),(2,1,[3,3,19,199]),(3,1,[3,3,3,5,7,37]),(2,2,[29,641]),(2,1,[13,3137]),(2,1,[3,14087]),(10,3,[3,3823]),(3,4,[5791]),(3,1,[3,16607]),(2,1,[7,7499]),(7,3,[3,5,5,5,43]),(3,1,[3,7,7,457]),(5,3,[3,23,283]),(2,1,[5,79,199]),(3,9,[7,47]),(31,1,[5,89,191]),(3,3,[22349]),(6,2,[3,3,7,19,61]),(5,1,[157211]),(2,1,[178793]),(3,1,[3,3,17,1277]),(3,1,[3,5,13043]),(2,1,[23,23,509]),(2,2,[3,3,3,41,127]),(10,3,[3,3,3,3517]),(2,1,[13,41141]),(5,1,[538523]),(3,4,[277,283]),(2,1,[3,5,57527]),(5,3,[3,17,41,107]),(7,4,[3,3,5,13,229]),(2,1,[5,5,43,1439]),(3,1,[3,349,1723]),(47,4,[3,3,3,5,1871]),(5,4,[3,92657]),(3,2,[7,31,6211]),(6,1,[5,562357]),(2,1,[467,8167]),(2,2,[1831,6637]),(7,3,[5,19,91753]),(7,2,[3,3,19,67,2179]),(3,1,[3,5,5,759673]),(3,1,[3,3,3,13,390763]),(2,2,[3,3,5,5,357587]),(2,1,[5,11,11,61,61,73]),(2,1,[3,3,3,409,16447]),(7,7,[3,17,67547]),(2,1,[3,3,3,53,169991]),(2,2,[3,3,3,5,79,18223]),(3,1,[3,440946817]),(5,5,[3,11,3093851]),(2,2,[3,5,5657,10831]),(11,1,[5,83,5391149]),(2,2,[11,59,1789897]),(3,3,[83,173,81563]),(3,3,[593,4447537]),(5,1,[11,29,317,129001]),(2,1,[21099115529]),(7,1,[42198231059]),(6,1,[3,43,328675931]),(10,2,[3,3,5,5,99859213]),(2,2,[7,29,103,1077047]),(2,2,[7,41,107,1725811]),(2,2,[3,3,3,3,23,113950951]),(5,5,[3,3,3,3,3,3,7,5623571]),(3,2,[5,7,45887,156217]),(2,1,[3,5,5,19,1789,292069]),(7,4,[3,97,486514243]),(5,1,[149,5653,3607963]),(3,1,[3,1259,4646572613]),(5,19,[3,4931,8867,43427]),(5,18,[3,19,211991719997]),(10,18,[3,19,619,363248443]),(5,19,[3,2265210315409]),(5,19,[3,3,104987,7627979]),(5,19,[3,3,849162486853]),(5,18,[3,19699,274315627]),(5,19,[3,877,3267106657]),(5,18,[3,6077952822023]),(5,18,[3,41,41,45361,84523]),(5,18,[3,3,3,977,777393181]),(5,19,[3,29,99643,1254257]),(11,1,[5,7,11,13,17,35100209518603]),(5,20,[3,4931,8867,43427]),(5,19,[3,1453,2645680903]),(11,1,[5,5,5,7,11,13,17,1489157606851]),(5,19,[3,19,211991719997]),(10,19,[3,1109,3676258021]),(7,1,[5,7,11,13,17,43,918306650017]),(5,19,[3,19,619,363248443]),(13,23,[3,3,90079902893]),(7,1,[5,5,5,7,11,13,17,19,19,23,2713,74357]),(5,20,[3,2265210315409]),(5,20,[3,1069667,2143441]),(11,1,[5,7,11,13,17,19,33521,69732281]),(5,20,[3,3,104987,7627979]),(5,22,[3,797,1949,391291]),(19,1,[5,5,7,11,13,17,19,19,26089936247]),(5,20,[3,3,849162486853]),(10,21,[3,3,47,68059,134359]),(7,1,[5,7,11,13,17,19,31,84798390199]),(5,19,[3,19699,274315627]),(7,1,[5,7,7,11,13,17,19,89,4474653671]),(10,20,[3,877,3267106657]),(7,1,[5,7,11,13,17,19,251,69931,168449]),(5,19,[3,6077952822023]),(19,1,[5,5,7,11,13,17,19,31,64333,314423]),(7,19,[3,41,41,45361,84523]),(7,1,[5,7,11,13,17,19,37,89873291701]),(5,19,[3,3,3,977,777393181]),(14,1,[5,7,11,13,17,19,10957,321828301]),(7,20,[3,29,99643,1254257]),(7,1,[5,5,7,11,13,17,19,271,683,4041361]),(5,20,[3,1453,2645680903]),(7,1,[5,7,11,13,17,19,47,84396462119]),(5,20,[3,1109,3676258021]),(7,1,[5,7,11,13,17,19,449,9369304937]),(5,24,[3,3,90079902893]),(7,1,[5,7,11,13,17,17,19,521,17393,28961]),(7,21,[3,1069667,2143441]),(7,1,[5,5,5,7,11,13,17,17,19,229,48609389]),(7,23,[3,797,1949,391291]),(11,1,[5,5,7,11,13,17,19,1003566127061]),(5,22,[3,3,47,68059,134359])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [497750221148389376,527937395745488896,559961202769657856,593811292922576896,629805126469287936,667808552860778496,708279472786374656,751108761371017216,796649432288198656,844763543220125696,895958154023141376,950104221883826176,1007727241346154496,1068753261766639616,1133467491071164416,1202070803787022336,1274676350755536896,1351983378748932096] 23784947663657349347535370593630683135 197408778092644864465856335061493743614 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_32 (k : ℕ) (lo : 197408778092644864465856335061493743615≤k) (hi : k≤1639577419169801617090623296675290546174) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,131,149,151,157,167,191,193,197,211,227,229,241,251,263,271,311,317,337,347,409,491,523,557,571,641,643,701,709,761,883,919,1013,1163,1171,1543,1621,1657,1741,1787,1913,1933,2437,2713,2719,2833,2957,3109,3851,3863,4561,4789,5179,5233,5323,5479,5779,6133,6379,6679,6907,7213,7927,7963,8093,8291,11789,13291,14423,14653,15493,16927,18353,19687]
  let factors : List (ℕ × ℕ × List ℕ) := [(7,1,[7,31,47]),(2,2,[5779]),(5,5,[3,3,3,29]),(11,5,[3,3,7,13]),(3,4,[1657]),(2,2,[6679]),(26,1,[5,2719]),(5,3,[7,557]),(3,4,[11,197]),(5,3,[3,37,47]),(2,2,[47,251]),(2,2,[16927]),(13,1,[5,5,5,5,59]),(11,6,[3,3,3,3,17]),(2,1,[11,5479]),(7,1,[5,13291]),(5,1,[73751]),(5,1,[3,25057]),(2,1,[3,27191]),(6,4,[5,5,409]),(2,1,[7,73,191]),(2,1,[7,14423]),(5,3,[3,3,2833]),(3,1,[3,71,643]),(2,1,[163601]),(7,1,[5,5,7,17,61]),(2,2,[3,7,4789]),(2,1,[53,5233]),(3,5,[5,4561]),(2,2,[3,3,13,1741]),(3,1,[3,163147]),(3,1,[3,203977]),(3,3,[7,229,317]),(3,1,[3,3,273919]),(6,4,[5,5,7,17,131]),(3,4,[109,6133]),(2,1,[6235601]),(2,1,[3,3,641,1621]),(7,2,[5,5,23,8291]),(3,3,[11,402277]),(3,3,[5,73,15493]),(2,2,[919,14653]),(11,1,[3,3,17,201923]),(6,1,[3,10695953]),(3,3,[2713,2957]),(2,1,[7,523,11789]),(2,1,[64178729]),(7,5,[3,3,73,79,103]),(5,1,[3,7,7,37,97,271]),(2,2,[3,167,147503]),(2,2,[7,83,195203]),(2,1,[3,61,89,20399]),(2,1,[5,7,7,11,17,7963]),(5,1,[7,53864429]),(2,2,[3,5,23,271,3851]),(2,1,[3,5,641,132911]),(3,5,[86319059]),(6,1,[3,211,701,3863]),(2,2,[3,5,7,151,67709]),(3,3,[11,61788439]),(2,2,[3,11,13,13,59,7213]),(7,1,[17,709,978883]),(5,1,[7,2762209889]),(3,3,[7,729649691]),(13,1,[5,227,19069301]),(5,1,[6907,4065209]),(3,1,[3,9493548637]),(2,1,[3,5,1933,1223863]),(6,2,[3,43,295596013]),(2,1,[3,5,38670938447]),(2,2,[11,11,53,45239561]),(3,1,[3,3,3,5,5437382633]),(3,1,[3,3,5,120539,150343]),(2,2,[101,571,1913,5179]),(7,3,[3,31,241,35400377]),(14,3,[3,5,70971815371]),(3,1,[3,1013,1440196981]),(7,3,[3,3,13,107,128357459]),(5,20,[3,554699,4930543]),(5,20,[3,67,43287313271]),(5,21,[3,3,3,3,56961291823]),(10,21,[3,1630997538931]),(13,22,[3,3,23117,12471203]),(5,19,[3,311,23596953599]),(10,21,[3,3,34673,18703099]),(10,20,[3,101,40860382697]),(5,19,[3,8753517250519]),(5,22,[3,1160485218773]),(5,20,[3,3,3,3,29,149,5323,7927]),(5,19,[3,3,3,1160128153411]),(19,1,[5,7,11,13,13,17,19,6379,64175719]),(5,21,[3,554699,4930543]),(5,21,[3,3,263,491,883,8093]),(11,1,[5,7,11,13,17,19,37,152527542709]),(7,21,[3,67,43287313271]),(5,20,[3,3,571,3428281159]),(14,1,[5,5,7,11,13,13,17,19,19,347,761,18353]),(17,22,[3,3,3,3,56961291823]),(5,20,[3,2437,2555878531]),(11,1,[5,7,11,13,17,19,6347429197609]),(7,22,[3,1630997538931]),(5,19,[3,3,3,1468093310911]),(7,1,[5,7,11,13,17,19,79,113,754102007]),(5,23,[3,3,23117,12471203]),(5,19,[3,71,157,1543,814789]),(7,1,[5,7,11,13,17,19,41737,171072289]),(7,20,[3,311,23596953599]),(5,20,[3,1787,47189,88129]),(11,1,[5,7,11,13,17,17,19,31,19687,729761]),(5,22,[3,3,34673,18703099]),(7,1,[5,7,11,11,13,13,17,19,56156797127]),(7,21,[3,101,40860382697]),(7,1,[5,7,11,13,17,19,8516617844521]),(7,20,[3,8753517250519]),(7,1,[5,5,7,11,11,13,17,17,19,337,919,31193]),(5,23,[3,1160485218773]),(7,1,[5,7,11,13,17,19,19,53,26209,362951]),(5,21,[3,3,3,3,29,149,5323,7927]),(11,1,[5,7,11,13,17,19,1171,26513,327203]),(7,20,[3,3,3,1160128153411]),(7,1,[5,7,11,13,13,17,19,193,4294104781]),(5,22,[3,3,263,491,883,8093]),(19,1,[5,5,7,11,13,17,19,2285484890069]),(7,21,[3,3,571,3428281159]),(7,1,[5,7,11,13,17,19,26717,453651773]),(10,21,[3,2437,2555878531]),(7,1,[5,7,11,13,17,19,12855256233769]),(5,20,[3,3,3,1468093310911]),(7,1,[5,7,11,13,17,19,41,1163,285949987]),(5,20,[3,71,157,1543,814789]),(19,1,[5,7,7,11,13,17,19,3109,664477027]),(5,21,[3,1787,47189,88129])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [1433910520870076416,1520566266315145216,1612662575434039296,1710224875382112256,1813806630574227456,1923783739123695616,2039981177444499456,2163683440667918336,2294682026120052736,2433713897520234496,2580971877463228416,2737085711829958656,2902877121524269056,3078957629632413696,3265620072226881536,3463666676059078656,3673744986018676736,3896315233617575936] 197408778092644864465856335061493743615 1639577419169801617090623296675290546174 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_33 (k : ℕ) (lo : 1639577419169801617090623296675290546175≤k) (hi : k≤13608489505686209262113906953343287689214) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,73,79,83,89,101,103,109,131,137,139,173,197,233,277,281,283,311,463,503,509,547,577,613,653,719,743,929,971,977,1091,1117,1151,1223,1277,1381,1567,1597,1627,1753,2017,2203,2269,2657,2837,3041,3257,3319,3581,3727,4789,4993,5011,5393,5483,5879,6047,6481,7523,7793,8087,8317,8699,9413,10079,10091,11909,12659,12911,13147,16141,16481,17449]
  let factors : List (ℕ × ℕ × List ℕ) := [(2,2,[3,3,577]),(2,1,[11909]),(7,1,[3,3,3,5,7,13]),(22,2,[3,5,5,89]),(2,2,[5,5,5,59]),(2,1,[13,1277]),(11,3,[3,5,281]),(2,1,[3,7523]),(7,1,[23819]),(6,1,[3,9413]),(7,3,[3,3,17,47]),(2,2,[5,3041]),(5,3,[3,3319]),(5,1,[89,547]),(3,1,[3,16481]),(3,3,[12911]),(3,4,[5,17,79]),(13,6,[3,5,7,19]),(2,1,[7,10079]),(3,1,[3,33721]),(2,1,[107441]),(3,6,[3727]),(2,1,[13,19,503]),(3,3,[23,29,53]),(3,1,[3,61,977]),(3,3,[7,8087]),(3,1,[3,3,11,2657]),(5,1,[11,23,1091]),(3,4,[5,5,1381]),(5,5,[3,3,3,719]),(7,1,[173,2203]),(2,2,[173,1151]),(7,1,[5,29,29,103]),(3,3,[41,43,73]),(2,1,[23,24571]),(2,1,[3,3,103289]),(3,1,[3,61,8317]),(3,4,[202327]),(11,1,[17,98887]),(2,2,[3,7,45139]),(5,2,[3,357583]),(3,2,[5,282809]),(3,1,[3,743,1627]),(3,4,[526087]),(19,3,[3,3,238529]),(3,1,[3,3,233,4789]),(5,1,[19,1130267]),(2,2,[5,3237233]),(2,1,[5,929,7793]),(3,1,[3,19,509,1567]),(7,1,[7,8417393]),(3,3,[19,796493]),(2,1,[19,3362159]),(13,1,[3,3,3,3,3,5,60821]),(5,1,[37,1223,1753]),(11,4,[3,5,103,12659]),(3,3,[29,53,29501]),(3,6,[7,11,17,5011]),(3,3,[109,552401]),(11,3,[3,3,3,3,3,137,3257]),(2,1,[3,3,5,7,13,141107]),(3,1,[3,312930481]),(2,1,[11,90926743]),(22,3,[3,3,3,5,5,7,17,4993]),(2,2,[3,3,5,20085067]),(2,2,[11,11,17,552047]),(6,2,[3,7,121066937]),(31,4,[3,3,5,19,613,2269]),(2,1,[11,13147,79657]),(23,1,[5,17,158650007]),(2,1,[5,3615312061]),(2,2,[10169622709]),(7,5,[3,481693673]),(5,1,[36153120611]),(7,1,[5,7,1155666331]),(2,1,[5,13,867430297]),(6,1,[3,5,13,101,197,20773]),(3,3,[112765938611]),(5,1,[11,1117,1597,56479]),(2,1,[11,161194948591]),(2,2,[3,3,13,40678490837]),(5,3,[3,13,53,1877582887]),(5,20,[3,109,72306241223]),(5,21,[3,29,1223,117843503]),(5,22,[3,2216500168763]),(10,20,[3,3,1029593,3044023]),(5,25,[3,3,3,43,61,277,47639]),(5,20,[3,3,3,3,3,89,233,971,6481]),(10,20,[3,26701,419801537]),(5,22,[3,61,2837,17174089]),(10,21,[3,3,3,5483,127762043]),(5,20,[3,2017,8699,762239]),(13,22,[3,3546288869003]),(5,20,[3,653,23039512739]),(14,1,[5,7,11,13,17,17,19,902127508889]),(5,21,[3,109,72306241223]),(10,21,[3,1859203,4290997]),(7,1,[5,7,11,13,17,19,3581,4542242717]),(5,22,[3,29,1223,117843503]),(5,20,[3,3,41,131,277,3791677]),(21,1,[5,7,11,13,17,19,19,283,3208501801]),(5,23,[3,2216500168763]),(5,20,[3,41,6047,72396971]),(7,1,[5,5,7,11,13,17,17,19,248483,866231]),(5,21,[3,3,1029593,3044023]),(11,20,[3,19037533711717]),(7,1,[5,7,7,11,13,17,19,101,127681,214883]),(5,26,[3,3,3,43,61,277,47639]),(10,20,[3,10091,2000388347]),(7,1,[5,7,11,13,17,19,23,47,19027470961]),(10,21,[3,3,3,3,3,89,233,971,6481]),(10,20,[3,463,46242592609]),(7,1,[5,7,11,13,13,17,17,19,17449,5656181]),(15,21,[3,26701,419801537]),(11,1,[5,5,7,11,13,17,19,1381,5393,621217]),(5,23,[3,61,2837,17174089]),(7,1,[5,5,7,11,13,17,19,33203,147795031]),(5,22,[3,3,3,5483,127762043]),(11,1,[5,7,11,13,17,19,83,139,311,7253167]),(5,21,[3,2017,8699,762239]),(7,1,[5,7,11,13,17,19,23,23,29,29,137,452873]),(17,23,[3,3546288869003]),(7,1,[5,5,7,11,13,17,19,16141,362744297]),(5,21,[3,653,23039512739]),(7,1,[5,7,11,13,17,19,31047710619433]),(5,22,[3,1859203,4290997]),(11,1,[5,7,11,13,17,19,5879,57529,97367]),(5,21,[3,3,41,131,277,3791677]),(14,1,[5,5,7,7,11,13,17,19,37,26970501191]),(7,21,[3,41,6047,72396971]),(7,1,[5,5,7,11,11,13,17,19,101,103,64744661]),(5,21,[3,19037533711717]),(7,1,[5,7,11,13,17,19,31,29501,42950147]),(5,21,[3,10091,2000388347]),(11,1,[5,5,7,11,13,17,19,103,80896643171]),(7,21,[3,463,46242592609])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [4132113111217340416,4382581609884286976,4648337761921662976,4929520569112068096,5226405492305166336,5541943776665665536,5876807546666745856,6232937741833732096,6610929357601898496,7011909664525254656,7437106794207379456,7887809055852855296,8365365783839113216,8872733308761931776,9410531205640093696,9981150474648682496,10583235000835506176,11225174050323562496] 1639577419169801617090623296675290546175 13608489505686209262113906953343287689214 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_34 (k : ℕ) (lo : 13608489505686209262113906953343287689215≤k) (hi : k≤113212912248146446914748909106302052990974) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,79,83,89,97,101,103,109,127,131,163,191,193,227,233,239,263,271,293,317,337,397,419,421,439,467,479,491,521,523,563,577,599,683,751,761,827,863,907,1051,1091,1223,1231,1327,1373,1427,1459,1493,1637,1693,1709,1979,1999,2237,2389,2459,2579,2741,2803,2927,3209,3581,3881,4091,4639,5479,5569,6007,6131,6547,7687,7741,8287,8329,10169,13967,14543,16493,16553,17027,18593,19001]
  let factors : List (ℕ × ℕ × List ℕ) := [(2,2,[3,3,563]),(2,2,[3,1709]),(3,3,[2927]),(3,1,[3,3,1327]),(2,2,[6547]),(2,1,[3,5,1051]),(3,1,[3,7,751]),(2,1,[3,7,761]),(2,1,[3,3,3,3,5,41]),(2,1,[7,2579]),(3,2,[7,17,83]),(11,3,[5,7,163]),(5,3,[3,1979]),(2,1,[26189]),(7,3,[3,5,5,89]),(3,1,[3,7,1373]),(5,1,[17,1999]),(2,2,[20509]),(5,1,[83,577]),(3,2,[17,17,103]),(2,1,[11,5479]),(2,1,[37,1637]),(2,2,[3,10169]),(5,5,[3,23,67]),(10,2,[5,13,599]),(2,2,[17,2459]),(14,1,[5,7,11,239]),(2,1,[3,31531]),(3,5,[6131]),(2,1,[167213]),(2,2,[83,1223]),(3,1,[3,3,7,7,479]),(2,1,[109,2741]),(3,3,[121139]),(5,1,[89,7687]),(2,1,[7,7,11,1459]),(7,4,[3,33211]),(2,1,[17,122029]),(5,1,[7,19,31,521]),(5,1,[11,17,43,491]),(7,1,[5,5,184031]),(2,1,[5,7,101,1427]),(19,5,[3,3,11,3581]),(2,1,[7,1368287]),(10,3,[3,1572803]),(2,2,[3,3,3,5,95783]),(7,1,[3,3,7,13,53401]),(6,1,[3,41,969113]),(2,1,[5,5,5,31,31543]),(7,7,[3,13,52379]),(5,3,[3,29,29,18593]),(5,3,[3,19156019]),(7,1,[421,597539]),(2,1,[5,19,43,271,271]),(6,2,[3,17,4148987]),(2,2,[29,7896263]),(12,1,[3,3,5,397,31963]),(6,2,[3,17,683,39509]),(5,2,[3,3,3,3,67,406037]),(3,1,[3,3,16553,67967]),(3,1,[3,7,17,29,71,79,317]),(3,6,[17027,45641]),(3,3,[5,17,244458251]),(3,1,[3,5,5,5,43,421,13967]),(2,2,[5,7,29,375281113]),(3,1,[3,19,59,67,11344609]),(2,2,[53,49736275649]),(2,2,[3,11,11,83,233,467,827]),(3,3,[5,5,2803,4091,5569]),(3,1,[3,3,5,29,8814251197]),(2,2,[3,5,131,907,1493,2579]),(2,2,[3,13,13,13,89,523,23417]),(15,3,[3,3881,503127839]),(19,3,[3,13,13,3209,4296167]),(11,23,[3,3,3,193,8329,196193]),(5,20,[3,127,189633450751]),(5,21,[3,12772025907401]),(5,20,[3,2237,20269,597539]),(10,20,[3,28736525334037]),(10,23,[3,8287,459744457]),(5,21,[3,439,36816365419]),(13,20,[3,1693,20251039519]),(5,21,[3,23,863,915966509]),(5,23,[3,29,166231610681]),(11,23,[3,5112357288979]),(5,22,[3,10844836775653]),(21,1,[5,7,11,13,17,19,29,1523641318781]),(7,24,[3,3,3,193,8329,196193]),(10,21,[3,23005195624171]),(7,1,[5,7,11,13,17,19,46863339435817]),(5,21,[3,127,189633450751]),(5,21,[3,127,227,846393349]),(7,1,[5,7,11,11,13,17,17,19,47,47497,119069]),(5,22,[3,12772025907401]),(5,22,[3,147937,87470839]),(7,1,[5,5,7,11,13,17,19,10544090437589]),(5,21,[3,2237,20269,597539]),(5,21,[3,27449913671941]),(19,1,[5,7,11,13,17,19,55917638006569]),(7,21,[3,28736525334037]),(10,21,[3,3,29,293,1142037991]),(14,1,[5,7,11,13,17,19,29,37,6007,9201551]),(7,24,[3,8287,459744457]),(5,22,[3,3,3,191,57667,155741]),(19,1,[5,7,11,13,17,19,29,1091,16493,120539]),(5,22,[3,439,36816365419]),(11,1,[5,5,7,11,11,13,17,19,4639,261475969]),(5,21,[3,1693,20251039519]),(11,1,[5,7,11,13,17,19,23887,36107,82037]),(5,22,[3,23,863,915966509]),(7,1,[5,5,7,11,13,17,17,19,19,1231,37747273]),(7,24,[3,29,166231610681]),(7,1,[5,7,11,13,13,13,17,19,131,19001,189187]),(5,24,[3,5112357288979]),(7,1,[5,7,11,11,13,17,19,37,61,337,10088891]),(10,23,[3,10844836775653]),(7,1,[5,5,7,11,13,17,19,43,83,97,51722821]),(17,22,[3,23005195624171]),(7,1,[5,5,5,7,11,11,13,17,19,71,14543,334427]),(5,22,[3,127,227,846393349]),(7,1,[5,7,11,13,17,19,422479,238401799]),(17,23,[3,147937,87470839]),(7,1,[5,7,11,13,17,19,23,7741,600012971]),(10,22,[3,27449913671941]),(7,1,[5,7,11,13,17,19,71,419,2389,1594129]),(7,22,[3,3,29,293,1142037991]),(11,1,[5,7,11,13,17,19,83,263,5504867989]),(7,23,[3,3,3,191,57667,155741])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [11905183484378873856,12626662913672216576,13392439837878910976,14204778968969117696,15066215394331590656,15979888520080654336,16947488404475478016,17975219273422340096,19064180427604361216,20219551378567069696,21442780626593775616,22743271133734240256,24122696006810730496,25585960991662800896,27137510755046260736,28783320678469206016,30525819902839750656,32376962581461467136] 13608489505686209262113906953343287689215 113212912248146446914748909106302052990974 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_35 (k : ℕ) (lo : 113212912248146446914748909106302052990975≤k) (hi : k≤942631794226429097258751070810596395974654) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,67,71,73,79,83,97,103,107,109,127,149,191,193,199,223,229,233,251,257,293,313,347,353,359,383,409,433,449,491,503,557,563,613,617,619,647,691,743,751,797,809,823,863,907,947,967,1009,1061,1063,1151,1409,1487,1667,1861,1877,2029,2053,2129,2143,2213,2311,2333,2341,2383,2459,2927,2957,3257,4253,4673,4987,5081,5413,5521,6577,6653,8237,11119,11491,12487,12941,14153,14831,16217,17321,17971]
  let factors : List (ℕ × ℕ × List ℕ) := [(3,1,[3,3,5,223]),(11,5,[3,233]),(2,2,[6577]),(17,1,[5,5,19,29]),(2,2,[3,31,79]),(5,1,[14831]),(3,1,[3,17,353]),(2,2,[3,3,3,3,127]),(2,1,[3,3,7,383]),(10,6,[3,17,19]),(2,2,[5,3257]),(5,1,[7,4673]),(5,3,[3,3,3,3,107]),(2,1,[7,7,809]),(2,1,[11,37,103]),(10,4,[3,7,257]),(2,2,[43,613]),(15,2,[3,11,823]),(5,3,[3,3,2311]),(2,2,[3,3,4987]),(2,1,[5,59,359]),(5,1,[3,17,2333]),(7,3,[3,5,2053]),(6,1,[5,5,11,11,41]),(10,1,[3,5,13,743]),(5,1,[7,26309]),(2,1,[11,20071]),(7,1,[7,7,83,97]),(3,3,[5,5,5081]),(3,1,[3,5,11,19,229]),(11,1,[788999]),(5,4,[3,47,797]),(2,1,[1016201]),(3,5,[65423]),(6,1,[3,3,3,5,11,19,41]),(2,2,[7,103,1009]),(5,1,[11,166393]),(7,1,[7,11,29,863]),(5,1,[2032403]),(3,1,[3,3,3,86353]),(2,2,[3,441563]),(2,2,[5,5,69337]),(2,2,[3,11,65141]),(5,4,[3,11,22369]),(2,2,[29,105437]),(2,1,[3,2313631]),(6,4,[5,5,19,1861]),(3,1,[3,5,7,73,1063]),(11,3,[3,5,179533]),(3,3,[3660647]),(3,1,[3,3,5,13,29663]),(5,3,[3,3,29,36007]),(3,1,[3,3,7,691,1151]),(2,1,[3,5,4064807]),(2,1,[5,11,11,191,563]),(2,2,[3,3,8598613]),(11,1,[5,5,17,107,4253]),(3,1,[3,5,5,11,246361]),(11,4,[3,3,5,1435831]),(3,1,[3,29,59,108637]),(5,1,[53,13881787]),(5,10,[3,13,67,751]),(5,1,[1471469423]),(5,1,[109,491,29389]),(5,1,[11,2927,83843]),(2,2,[11,19,12230693]),(7,4,[3,406495651]),(5,1,[3,3,11,12487,16217]),(7,3,[3,17,130114931]),(2,2,[3,17,53,2341,2383]),(2,2,[19511791249]),(3,1,[3,3,7,1115267443]),(2,2,[19,83,29285177]),(2,2,[29,383,449,17321]),(7,3,[3,5,5,11,13,149,79283]),(7,1,[7,78047164997]),(7,2,[3,5,5,13,386810351]),(7,1,[3,3,3,7,491,14143601]),(2,2,[7,1409,11491,12941]),(2,2,[2625024058399]),(5,1,[11,1508560368901]),(13,1,[5,17971,309550069]),(7,3,[3,149,40095332443]),(11,3,[3,5,17,947,2029,41149]),(7,3,[3,3,5,617,1033798321]),(7,3,[3,17,313,409,4663063]),(15,3,[3,7,11,83,2009459713]),(5,3,[3,7,11,31,37,53,2909957]),(5,22,[3,71,14153,16295791]),(10,22,[3,5521,3145739783]),(5,22,[3,347,53086891849]),(5,22,[3,3,2213,2942938847]),(10,23,[3,31,211811,1577999]),(5,22,[3,3,23,59,5398986143]),(5,22,[3,23,1013569728601]),(5,25,[3,3,3,797,1487,289771]),(5,21,[3,3,3,3,433,2143,2093537]),(5,21,[3,55629242899991]),(5,22,[3,3,3,3,1092660309959]),(5,21,[3,5298757,11810833]),(29,1,[5,7,11,13,17,19,907,140523697819]),(5,23,[3,71,14153,16295791]),(5,22,[3,33188328115823]),(7,1,[5,7,11,13,17,19,1798033,75182617]),(5,23,[3,5521,3145739783]),(5,23,[3,3,5866710883013]),(7,1,[5,7,11,13,17,19,143380908816169]),(5,23,[3,347,53086891849]),(5,22,[3,619,60315855637]),(7,1,[5,7,11,13,17,19,1061,6653,21543961]),(7,23,[3,3,2213,2942938847]),(5,22,[3,73,5413,100212967]),(7,1,[5,7,11,13,17,19,161295213213481]),(15,24,[3,31,211811,1577999]),(5,24,[3,10500096233597]),(7,1,[5,7,11,13,17,19,1667,2957,34705711]),(5,23,[3,3,23,59,5398986143]),(10,22,[3,503,967,8237,11119]),(14,1,[5,5,7,11,13,17,19,2459,62017,237967]),(5,23,[3,23,1013569728601]),(7,1,[5,7,11,13,17,19,557,345522287213]),(5,26,[3,3,3,797,1487,289771]),(11,1,[5,7,7,11,13,17,17,19,251,27551,248051]),(5,22,[3,3,3,3,433,2143,2093537]),(7,1,[5,7,11,13,17,19,647,48259,6933701]),(5,22,[3,55629242899991]),(14,1,[5,7,11,13,17,19,229627283060521]),(7,23,[3,3,3,3,1092660309959]),(7,1,[5,7,11,13,17,19,243556145116969]),(5,22,[3,5298757,11810833]),(7,1,[5,5,7,11,13,17,19,199,2129,121944211]),(5,23,[3,33188328115823]),(11,1,[5,7,11,13,17,19,193,368327,3854159]),(5,24,[3,3,5866710883013]),(7,1,[5,7,11,13,17,19,97,293,10224859349]),(5,23,[3,619,60315855637]),(7,1,[5,7,11,13,17,19,308218968618793]),(7,23,[3,73,5413,100212967]),(11,1,[5,7,11,13,17,19,326909714183977]),(5,25,[3,10500096233597]),(7,1,[5,7,11,13,17,19,1877,184730896517]),(5,23,[3,503,967,8237,11119])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [34340942499824009216,36422558609714446336,38631954650975174656,40974514399966396416,43458710184851931136,46093875466790240256,48889025019926020096,51854519562494017536,54998948387572678656,58331489003100962816,61869818367480692736,65622752923044806656,69600968684754436096,73820306770394873856,78298249196843565056,83045234658945007616,88081191265921662976,93424151956350304256] 113212912248146446914748909106302052990975 942631794226429097258751070810596395974654 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_36 (k : ℕ) (lo : 942631794226429097258751070810596395974655≤k) (hi : k≤7850509911003015886599502290291887708307454) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,71,73,79,83,89,97,101,103,107,109,127,149,151,157,163,173,179,191,193,199,227,233,241,263,283,293,331,349,353,367,379,397,431,433,491,563,587,593,601,773,823,937,1091,1213,1429,1433,1559,1601,1607,1709,1747,2029,2081,2089,2423,2467,2621,2731,2753,2791,3011,3761,4057,4273,4621,4909,5261,5711,7187,7433,7561,8101,8237,9157,9463,11701,11719,12373,12511,14423,15443,17167,17903,19889]
  let factors : List (ℕ × ℕ × List ℕ) := [(6,3,[5,5,101]),(2,2,[3,1709]),(11,3,[3,3,3,5,19]),(3,1,[3,3761]),(3,1,[3,3,5,7,37]),(3,3,[11,331]),(2,2,[13,601]),(6,1,[3,5261]),(13,3,[3,5,283]),(2,1,[3,3,2029]),(2,2,[9157]),(2,2,[9463]),(2,2,[53,191]),(3,1,[3,3,43,73]),(26,1,[3,3,5,17,37]),(2,1,[37,773]),(10,3,[3,2423]),(2,2,[17167]),(2,1,[36629]),(5,3,[3,3,1091]),(2,2,[3,17,397]),(6,1,[3,5,2753]),(11,3,[3,3,3,433]),(26,3,[3,5,11,79]),(2,1,[71,823]),(3,2,[5,17,367]),(2,1,[68669]),(6,2,[3,5,41,61]),(3,1,[3,3,53,179]),(3,1,[3,33961]),(13,3,[3,3,3,3,3,127]),(5,1,[7,47,379]),(2,1,[3,3,3,7,13,73]),(23,7,[3,5,11,17]),(2,2,[5,20201]),(5,1,[7,31253]),(12,1,[3,5,15443]),(10,6,[3,2731]),(3,1,[3,3,31567]),(3,3,[7,7,1601]),(3,1,[3,3,5,5,11,127]),(2,1,[29,107,107]),(6,2,[3,179,349]),(3,1,[3,203767]),(7,2,[3,3,37853]),(3,3,[19,19,491]),(2,2,[5,73259]),(2,2,[3,241,563]),(6,2,[3,137339]),(11,1,[3,193,2089]),(2,2,[23,29129]),(5,2,[3,41,7433]),(3,1,[3,17,36523]),(3,1,[3,749653]),(7,3,[3,97,3011]),(2,2,[3,628651]),(2,1,[3,7,404021]),(2,2,[5,11,41,2753]),(14,6,[3,5,13,2467]),(11,3,[3,5,19,14423]),(11,3,[3,1628197]),(2,2,[1607,7187]),(3,4,[5,627593]),(3,3,[2621,2791]),(3,3,[29,358723]),(2,2,[3,7009609]),(2,2,[3,5,11,170767]),(19,4,[3,53,151,367]),(3,5,[13,17,20509]),(2,1,[5,23,664043]),(6,2,[3,3,937,5711]),(17,3,[3,19,149,4057]),(5,1,[152729891]),(3,3,[46198037]),(3,1,[3,5,5,47,58153]),(3,4,[11,233,11719]),(3,3,[83223737]),(6,5,[5,157,80989]),(2,2,[19,30788161]),(3,1,[3,409978651]),(2,1,[2034443681]),(2,2,[349,3657037]),(11,3,[3,5,7,23,353,4273]),(3,3,[19889,359041]),(5,1,[107,275648809]),(2,2,[7,29141689081]),(12,1,[3,3,5,78553,116867]),(28,3,[3,5,5,11,11,109,437543]),(2,2,[5,37,103,4909,40493]),(2,2,[3,82591,16968883]),(2,2,[3,19,1559,84115309]),(3,3,[19,73,4068887363]),(2,2,[11,107,12511,1362709]),(3,1,[3,3,3,83,101,8237,22567]),(5,3,[3,3,31,163,8101,124781]),(5,22,[3,3,283,12373,4497919]),(5,22,[3,104281,480572753]),(5,22,[3,89,246889,2419063]),(5,22,[3,3,227,56503,1465181]),(5,23,[3,29898954814669]),(5,22,[3,3,57203,369584297]),(5,24,[3,16817724190237]),(5,25,[3,1747,5105223653]),(5,23,[3,107,249383,1418009]),(10,22,[3,80265996623693]),(5,22,[3,293,11701,24832061]),(10,23,[3,45148374179849]),(7,1,[5,7,11,13,17,19,367763724121897]),(7,23,[3,3,283,12373,4497919]),(5,24,[3,3,56611,140980849]),(7,1,[5,7,7,11,13,13,17,19,568207,7543813]),(5,23,[3,104281,480572753]),(5,23,[3,3,59,431,665789897]),(14,1,[5,5,7,11,13,17,19,1648069,50207441]),(7,23,[3,89,246889,2419063]),(5,23,[3,23,41,57127731593]),(7,1,[5,7,11,13,17,19,43,173,58988845127]),(5,23,[3,3,227,56503,1465181]),(5,24,[3,93529,305459783]),(14,1,[5,7,11,13,17,19,53,150061,58521689]),(5,24,[3,29898954814669]),(5,25,[3,15151022042141]),(7,1,[5,5,7,11,11,11,13,17,19,815967294269]),(5,23,[3,3,57203,369584297]),(10,24,[3,199,1433,112706221]),(7,1,[5,5,7,11,13,17,19,2679869,39076729]),(5,25,[3,16817724190237]),(11,1,[5,7,11,11,13,17,19,587,593,145039649]),(5,26,[3,1747,5105223653]),(7,1,[5,7,7,11,13,17,19,84146512454479]),(5,24,[3,107,249383,1418009]),(14,1,[5,7,7,11,13,17,19,463291,192643453]),(5,23,[3,80265996623693]),(19,1,[5,5,5,7,11,13,13,17,19,263,2081,3725347]),(5,23,[3,293,11701,24832061]),(7,1,[5,5,7,11,13,13,17,19,4621,2339900237]),(5,24,[3,45148374179849]),(7,1,[5,7,11,13,13,17,19,23311,2459871907]),(5,25,[3,3,56611,140980849]),(7,1,[5,7,11,13,17,17,19,79,17903,32884441]),(5,24,[3,3,59,431,665789897]),(7,1,[5,5,7,7,11,13,17,19,29,826222810591]),(5,24,[3,23,41,57127731593]),(11,1,[5,7,11,13,17,19,157,1429,7561,524353]),(5,25,[3,93529,305459783]),(11,1,[5,7,11,13,17,19,31,1213,20521,1222603]),(5,26,[3,15151022042141]),(11,1,[5,7,11,13,17,17,17,19,3462452776201]),(5,25,[3,199,1433,112706221])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [99088725478553419776,105097948835281371136,111472780783120285696,118233298603937366016,125405305774985445376,133009750881988509696,141077295684015620096,149633065600843513856,158704599936863830016,168329995351371022336,178539072812163792896,189366006416037380096,200850123496605351936,213033372079626387456,225953241962953834496,239657061558419193856,254191969421760659456,269610657399445651456] 942631794226429097258751070810596395974655 7850509911003015886599502290291887708307454 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_37 (k : ℕ) (lo : 7850509911003015886599502290291887708307455≤k) (hi : k≤65388181237838415887562540913331332423090174) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,67,83,97,101,107,109,139,151,163,173,179,211,223,227,233,239,251,257,271,337,349,353,379,383,389,397,509,547,577,593,631,647,683,733,743,827,857,937,983,1013,1103,1117,1123,1129,1193,1291,1423,1433,1459,1471,1481,1601,1697,1753,1777,1823,1931,1999,2063,2141,2143,3037,3067,3169,4157,4759,5233,6043,6473,7481,7699,7933,8297,9421,10181,15331,15373,16931,17027,17291,18691]
  let factors : List (ℕ × ℕ × List ℕ) := [(5,1,[7,1433]),(2,1,[3,3,1129]),(3,1,[3,3,3,509]),(3,6,[577]),(5,6,[3,7,29]),(11,3,[5,7,151]),(11,3,[3,1777]),(11,1,[5,4759]),(7,2,[3,5,1117]),(2,1,[7,7,13,53]),(2,1,[36929]),(5,4,[3,1697]),(5,1,[7,17,349]),(7,1,[5,5,7,353]),(7,1,[3,3,41,211]),(2,1,[83,1123]),(3,1,[3,5,11,631]),(17,1,[5,13,2143]),(3,3,[5,5,1481]),(2,1,[3,3,3,6043]),(10,1,[3,139,397]),(2,1,[11,15331]),(3,3,[29,1471]),(11,1,[186419]),(5,1,[59,3169]),(3,1,[3,3,67,337]),(2,1,[107,1999]),(2,2,[7,18691]),(2,2,[3,47591]),(5,2,[3,17,23,151]),(19,6,[3,5,857]),(3,1,[3,11,19,683]),(14,2,[3,3,13,1931]),(2,1,[3,257,631]),(5,3,[3,42649]),(5,1,[37,20063]),(13,3,[3,37,2141]),(2,2,[3,3,5,17291]),(6,1,[3,571093]),(14,1,[5,389,983]),(3,1,[3,708493]),(5,1,[7,271,1193]),(5,1,[37,67523]),(7,1,[5,7,81457]),(10,5,[3,7,7,1753]),(5,1,[4526243]),(3,5,[296201]),(5,3,[3,17,53,593]),(2,1,[11,109,7699]),(2,1,[3,3823871]),(2,2,[7,1023577]),(5,5,[3,3,11,13,23,31]),(12,2,[5,5,11,11,19,139]),(19,5,[3,341273]),(6,3,[5,5,239,1459]),(10,3,[3,3,7,7,13,1823]),(2,2,[5,5,903709]),(5,1,[31,1484663]),(2,2,[3,9478433]),(5,1,[7,11,856483]),(2,1,[3,19,23,73859]),(6,2,[3,3,13,427787]),(10,2,[3,3,19,227,1291]),(2,1,[3,17,3426559]),(11,1,[3,5,12823033]),(2,2,[5,7,41,223,379]),(2,1,[3,11,8246113]),(2,1,[7,11,13,173,1601]),(5,1,[3,3,11,13,211,1123]),(7,3,[3,5,5,5,83,3037]),(13,7,[3,5,5,123551]),(2,2,[29,18462203]),(3,7,[28660157]),(2,1,[3,5,43,43,67,1013]),(2,2,[7,53,4996703]),(2,2,[3,23,29364193]),(2,1,[11,19,83,163,10181]),(2,2,[13,31,200450989]),(11,1,[7,29,251,1423,7481]),(2,1,[3,373943,523349]),(2,1,[3,3,11,13,609917023]),(2,1,[5,67021,3112381]),(2,1,[326323,5701991]),(5,1,[7,179,3764804371]),(7,3,[3,5,11,23,544243459]),(17,1,[5,5233,384690991]),(7,1,[3,5,5,937,8297,38977]),(2,2,[53,67,3668500097]),(7,4,[3,19,59,27487,83063]),(13,1,[19,67,57574797083]),(3,1,[3,5,5,15373,69740201]),(19,3,[3,7,2063,42281,155719]),(11,22,[3,3,45452769352951]),(5,23,[3,3,20323,1186089601]),(11,25,[3,3,278591,22943227]),(5,23,[3,973003,83610073]),(5,25,[3,83,7933,32762209]),(11,23,[3,3,3,3,16931,200204317]),(10,25,[3,31,101,9421,822721]),(5,23,[3,3,372839,92049107]),(5,23,[3,3,31,1174216170643]),(10,26,[3,23,331099,1901209]),(10,23,[3,122851879459249]),(5,23,[3,83,1569926417203]),(7,1,[5,7,11,13,17,19,23,29,743,2141615549]),(5,23,[3,3,45452769352951]),(10,23,[3,647,1103,193658299]),(7,1,[5,7,7,11,13,17,19,160817416495951]),(7,24,[3,3,20323,1186089601]),(5,23,[3,146585433373319]),(7,1,[5,7,11,13,17,19,9052487,131898383]),(10,26,[3,3,278591,22943227]),(13,25,[3,3,179,17027,4250959]),(22,1,[5,7,11,13,17,19,233,733,7415107253]),(5,24,[3,973003,83610073]),(5,26,[3,3,179,337,547,208231]),(11,1,[5,7,11,13,17,19,4157,323126994269]),(10,26,[3,83,7933,32762209]),(5,23,[3,47,3721381618187]),(7,1,[5,7,11,13,17,19,683,2085948870011]),(5,24,[3,3,3,3,16931,200204317]),(10,24,[3,41,6473,349509019]),(11,1,[5,7,11,13,17,19,29,52107375377789]),(5,26,[3,31,101,9421,822721]),(11,1,[5,7,11,13,17,19,97,16523231415241]),(5,24,[3,3,372839,92049107]),(7,1,[5,5,5,5,7,11,13,17,17,17,19,97,485127581]),(5,24,[3,3,31,1174216170643]),(7,1,[5,7,11,13,17,19,47,337283,113741197]),(5,27,[3,23,331099,1901209]),(11,1,[5,5,7,11,13,17,19,19,20130879559031]),(5,24,[3,122851879459249]),(7,1,[5,5,7,11,13,17,19,43,9434599753727]),(5,24,[3,83,1569926417203]),(7,1,[5,7,7,11,13,17,19,406423,756213001]),(5,24,[3,647,1103,193658299]),(7,1,[5,7,11,13,17,19,2281893473236777]),(5,24,[3,146585433373319]),(11,1,[5,7,11,13,17,19,23,97,1084836552479]),(5,26,[3,3,179,17027,4250959]),(7,1,[5,7,11,13,17,19,383,827,8104517269]),(5,27,[3,3,179,337,547,208231]),(11,1,[5,7,11,13,17,19,1601,3067,554499947]),(7,24,[3,47,3721381618187]),(7,1,[5,7,11,13,17,19,31956101,90370901]),(5,25,[3,41,6473,349509019])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [285964098462239686656,303309822396702130176,321708647568151412736,341218591964529688576,361916696476270985216,383866061132100796416,407148229124094427136,431839210695322238976,458026821069513424896,485808890379319115776,515278129423445917696,546534138064557572096,579663307605683470336,614823869539445374976,652107558261784313856,691650649764246061056,733604472914345721856,778104184908793511936] 7850509911003015886599502290291887708307455 65388181237838415887562540913331332423090174 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_38 (k : ℕ) (lo : 65388181237838415887562540913331332423090175≤k) (hi : k≤544718574944255015728900398161949631558189054) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,73,79,83,89,97,101,103,109,127,131,137,139,149,151,157,163,179,181,191,199,227,233,239,241,263,269,281,307,331,347,367,389,397,439,449,457,487,587,599,619,631,641,709,719,757,773,859,1109,1123,1283,1307,1367,1613,1637,1847,1931,2003,2011,2063,2099,2269,2357,2543,2801,2837,2897,2903,3229,3301,3907,4139,4651,4657,5479,5807,6961,7369,7589,8053,9473,11953,12809,15199,18119,19421]
  let factors : List (ℕ × ℕ × List ℕ) := [(2,2,[3,41,43]),(5,2,[3,1931]),(17,2,[3,5,13,31]),(3,1,[3,47,131]),(13,1,[3,3,5,11,41]),(2,1,[5,7,7,109]),(2,2,[29,641]),(7,2,[3,5,13,109]),(2,1,[3,3,31,199]),(5,1,[3,17,1123]),(2,2,[3,3,3,1109]),(2,2,[3,3,4651]),(2,1,[5,21157]),(2,2,[3,18119]),(2,2,[67,859]),(2,1,[5,24181]),(3,1,[3,5,11953]),(2,1,[3,11,6961]),(41,4,[3,3,5,13,59]),(2,2,[3,5,5,2543]),(13,4,[3,19421]),(7,3,[3,5,47,181]),(11,6,[3,41,139]),(2,2,[127,2269]),(5,2,[3,111043]),(2,1,[3,3,67,1307]),(3,1,[3,137,2099]),(13,1,[3,5,5,7,2003]),(3,1,[3,11,13,3301]),(2,1,[5,457,709]),(2,1,[29,85021]),(2,1,[13,331,587]),(2,2,[1332517]),(2,2,[7,217429]),(2,2,[17,191,757]),(5,1,[5051723]),(13,1,[3,5,19,83,233]),(2,2,[2832259]),(23,5,[3,3,7,61,163]),(11,1,[11,932209]),(19,4,[3,5,7,7,43,53]),(6,1,[5,5,23,40591]),(3,3,[13,17,181,307]),(3,1,[3,3,3,7,11,41,631]),(2,2,[7,11,239,2011]),(2,1,[8053,9473]),(5,3,[3,11,269,2801]),(2,2,[97,281,2897]),(2,2,[3,13,47,157,397]),(3,3,[2837,36943]),(3,3,[13,9831917]),(3,1,[3,23,11023231]),(2,1,[79,10103447]),(13,8,[3,41,53411]),(3,3,[7,151,230213]),(2,1,[1022519369]),(5,9,[3,2103151]),(2,2,[3,227,1576243]),(6,1,[3,3,7,7,31,552241]),(2,2,[7,67,439,23173]),(7,1,[5,11,11,5479,7369]),(3,1,[3,3,17,263,1094209]),(13,3,[5,4293685933]),(2,1,[59,1521205879]),(2,2,[3,15099373423]),(2,2,[17,439,599,15199]),(3,1,[3,3,5,5,7,1931,74357]),(3,1,[3,3,3,12809,762901]),(2,2,[11,19084448573]),(2,2,[3,13,5807,1152653]),(5,3,[3,3,19,37,73,719,1613]),(3,1,[3,3,3,59,347,6088013]),(2,2,[3,3,119773,3240131]),(3,3,[7,73,179,20045089]),(2,1,[5,163,2357,20508599]),(6,3,[5,17,41,3230439937]),(2,1,[181,271778608253]),(15,3,[3,89,48853448711]),(17,4,[3,61,389,107571619]),(2,2,[5,5,13970887569469]),(10,24,[3,98383856187587]),(10,24,[3,104350966446697]),(10,24,[3,3,241811,152572139]),(5,25,[3,3,109,179502293723]),(5,23,[3,37,6730554068047]),(10,26,[3,73,452287606051]),(5,23,[3,3,3,37,67,269,46679651]),(5,24,[3,3,3,3907,4139,1020841]),(11,25,[3,78792191584091]),(5,24,[3,23,29,149,1681805569]),(5,26,[3,3,7589,1946681129]),(5,24,[3,3,3,397,114547,459427]),(14,1,[5,5,5,7,11,13,17,19,122523213468049]),(7,25,[3,98383856187587]),(10,24,[3,191,1044179131477]),(7,1,[5,7,11,13,17,19,53,73,839715737213]),(15,25,[3,104350966446697]),(5,25,[3,3,3,29,1283,315854117]),(7,1,[5,5,7,11,13,17,19,29,37,3229,198915817]),(5,25,[3,3,241811,152572139]),(10,24,[3,3,23,131,4657,5330069]),(7,1,[5,7,11,13,13,17,19,1637,171747437321]),(7,26,[3,3,109,179502293723]),(10,26,[3,3,3,41,101,1596344627]),(14,1,[5,7,7,11,13,17,19,19,331,88059751903]),(5,24,[3,37,6730554068047]),(10,24,[3,3,1109,211571,358591]),(7,1,[5,7,11,11,13,17,19,2063,181192481077]),(5,27,[3,73,452287606051]),(5,24,[3,31,41,103,2045038739]),(7,1,[5,7,11,13,17,19,29,43,97,367,98242457]),(5,24,[3,3,3,37,67,269,46679651]),(14,1,[5,5,7,7,11,13,17,19,4931219,26801041]),(5,25,[3,3,3,3907,4139,1020841]),(21,1,[5,7,11,13,17,19,241,619,2903,11329037]),(5,26,[3,78792191584091]),(7,1,[5,7,7,11,13,17,19,31,37,773,838458329]),(5,25,[3,23,29,149,1681805569]),(7,1,[5,7,7,11,13,17,19,1725379,456996229]),(7,27,[3,3,7589,1946681129]),(11,1,[5,5,7,11,13,13,17,19,90064665443561]),(10,25,[3,3,3,397,114547,459427]),(7,1,[5,7,7,11,13,17,19,41,41,527687941087]),(5,25,[3,191,1044179131477]),(11,1,[5,7,11,13,17,19,449,14668033965929]),(7,26,[3,3,3,29,1283,315854117]),(7,1,[5,5,7,11,13,17,19,1397088756946901]),(5,25,[3,3,23,131,4657,5330069]),(7,1,[5,7,7,11,13,13,17,19,19,4285228053097]),(7,27,[3,3,3,41,101,1596344627]),(21,1,[5,7,11,13,17,19,29,641,1367,1847,167437]),(15,25,[3,3,1109,211571,358591]),(11,1,[5,7,7,11,13,17,19,83,199,487,148033733]),(10,25,[3,31,41,103,2045038739])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [825303603086041808896,875359351942494027776,928458385485459357696,984776442651592359936,1044509624443554758656,1107866521682717966336,1175056694812644212736,1246319389633199210496,1321913617319676870656,1402096124335400943616,1487135421440905445376,1577332132198792298496,1673008998406533677056,1774490185782301556736,1882128867343095300096,1996293011320042684416,2117377165797334450176,2245816223278989049856] 65388181237838415887562540913331332423090175 544718574944255015728900398161949631558189054 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_39 (k : ℕ) (lo : 544718574944255015728900398161949631558189055≤k) (hi : k≤4537920068239263404312538273026024052470317054) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,71,73,79,83,89,97,101,103,107,113,137,139,157,163,167,179,181,191,193,197,199,211,227,229,277,281,307,311,337,379,397,419,431,457,479,487,491,499,509,523,613,631,641,673,719,757,787,911,941,953,1051,1061,1123,1201,1283,1301,1303,1487,1493,1523,1637,1657,1693,1801,1847,1873,1877,1987,2029,2473,2617,3011,3229,3517,3559,4153,4217,4547,4999,5237,5849,7243,7649,7699,9521,10501,12799,13841,14951,17033,17489,18121,18443,19141,19289,19577,19949]
  let factors : List (ℕ × ℕ × List ℕ) := [(2,2,[7,31,37]),(5,1,[89,199]),(2,2,[83,113]),(2,1,[3,3,7,11,37]),(13,4,[3,1201]),(2,2,[3,7,787]),(3,4,[4153]),(13,3,[3,5,613]),(3,1,[3,13841]),(2,2,[5,37,113]),(7,3,[3,47,79]),(2,1,[3,5,5,631]),(7,3,[3,4217]),(2,2,[3,5,1801]),(5,1,[181,311]),(10,2,[3,5,5,397]),(6,3,[17,1303]),(2,1,[5,18121]),(5,2,[3,18443]),(5,1,[112583]),(13,6,[3,7,7,31]),(23,5,[3,3,5,5,41]),(5,1,[3,7,19,457]),(2,1,[3,19,3229]),(2,2,[19,19,277]),(2,2,[61,1693]),(5,1,[17,37,379]),(2,2,[29,4547]),(3,1,[3,3,3,5,2029]),(5,3,[13,5849]),(3,1,[3,7,14951]),(2,1,[5,47,1523]),(10,6,[3,7,673]),(7,1,[41,12799]),(2,2,[163,1873]),(14,3,[3,5,17,641]),(2,2,[364687]),(2,2,[5,83621]),(13,3,[3,5,5,3559]),(7,1,[3,5,17,23,191]),(5,1,[7,177209]),(2,2,[5,181211]),(5,1,[719,2617]),(2,1,[19,97,1487]),(3,3,[11,66109]),(11,1,[3,5,5,7,7243]),(2,2,[3,3,31,43,197]),(5,1,[5481083]),(3,1,[3,53,37517]),(2,2,[281,32117]),(6,2,[3,3,5,23,47,191]),(10,1,[3,5,83,139,139]),(2,2,[139,119101]),(2,2,[19,953,1061]),(2,1,[3,17,1049519]),(3,1,[3,3,3,17,225167]),(2,2,[19,167,17489]),(6,2,[3,5,13,43,79,101]),(3,3,[179,431,911]),(10,3,[3,107,608297]),(5,1,[13,17,43,108061]),(2,2,[7,107050939]),(3,1,[3,7,17,103,51283]),(3,3,[941,1307641]),(5,1,[191,4999,7699]),(2,1,[9843921449]),(2,2,[337,1493,17033]),(2,1,[3,3,3,7,31,1301,3011]),(3,4,[19289,399989]),(11,4,[3,3,5,7,499,101209]),(2,2,[23,419,9453637]),(3,2,[11,1051,10962167]),(5,3,[3,17,1562106697]),(2,1,[17,19,29,79,527453]),(3,2,[5,7,13,97,487,9521]),(3,2,[7,19,337,11930407]),(2,2,[637339532377]),(3,5,[5,7,37,307,479,509]),(3,3,[818567784581]),(47,3,[3,5,7,83,1637,295201]),(2,2,[3,13,103,3771454387]),(3,5,[2138931088589]),(7,3,[3,1123,10501,291649]),(2,2,[3,157,19949,3624221]),(3,1,[3,3763247,7605151]),(5,1,[3,904513,66220157]),(7,3,[3,5,3517,94651,221317]),(5,3,[3,227,491,719,5817593]),(37,3,[3,5,7,11,47,757,36099509]),(5,3,[3,23,715811,48109291]),(5,25,[3,1877,35423,2135401]),(5,25,[3,7649,19687842899]),(10,24,[3,43,73,181,562261913]),(10,24,[3,229,479,1847,1672421]),(5,24,[3,359381957211247]),(5,25,[3,523,364418799077]),(5,26,[3,3,33691774259641]),(5,27,[3,3,3,1987,2997426293]),(5,24,[3,31,89,66449,2480927]),(5,25,[3,3,103,780623055659]),(5,24,[3,3,83047,2053807367]),(5,25,[3,107,211,19141,627943]),(7,1,[5,7,11,13,17,19,8840841319888681]),(7,26,[3,1877,35423,2135401]),(5,25,[3,19577,14702148983]),(7,1,[5,7,11,13,17,19,137,68445794834849]),(5,26,[3,7649,19687842899]),(5,25,[3,2473,123446205137]),(11,1,[5,7,11,13,17,19,37164781,267615661]),(5,25,[3,43,73,181,562261913]),(10,25,[3,1458749,221970389]),(14,1,[5,7,11,13,17,19,19,179,3101783046881]),(5,25,[3,229,479,1847,1672421]),(5,26,[3,171720370111783]),(7,1,[5,7,11,13,17,19,11188988205545257]),(15,25,[3,359381957211247]),(10,25,[3,29,457,57649,476783]),(7,1,[5,7,11,13,17,19,11867712139769641]),(5,26,[3,523,364418799077]),(5,25,[3,59,6548542276649]),(7,1,[5,7,11,13,13,17,19,23,547831,76846109]),(5,27,[3,3,33691774259641]),(7,1,[5,7,11,13,17,19,5237,2549358129509]),(5,28,[3,3,3,1987,2997426293]),(14,1,[5,7,11,13,17,19,413093,34280002613]),(10,25,[3,31,89,66449,2480927]),(7,1,[5,5,7,11,11,13,17,19,1657,73561,2240431]),(7,26,[3,3,103,780623055659]),(7,1,[5,7,11,13,17,19,193,82543360927849]),(5,25,[3,3,83047,2053807367]),(11,1,[5,7,11,13,17,19,368107,45903050299]),(15,26,[3,107,211,19141,627943]),(11,1,[5,7,11,13,17,19,71,1221197,206703307]),(5,26,[3,19577,14702148983]),(11,1,[5,7,11,13,17,19,19009312154400553]),(5,26,[3,2473,123446205137]),(7,1,[5,7,11,13,17,19,31,1283,506934450749]),(5,26,[3,1458749,221970389]),(11,1,[5,7,11,13,17,19,157,136212417629437]),(7,27,[3,171720370111783]),(7,1,[5,7,11,13,17,19,89113,254536586641]),(5,26,[3,29,457,57649,476783]),(7,1,[5,7,11,13,17,19,397,60599729090317]),(5,26,[3,59,6548542276649])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [2382039448391973339136,2526519718420116668416,2679775774454931521536,2842322831689054683136,3014714361317924274176,3197586910138949697536,3391525045063422836736,3597234718852006281216,3815434794479707488256,4046874620385659191296,4292346872881716658176,4552720360573151215616,4828884925408142688256,5121789861414374998016,5432447155813771902976,5761979481930655072256,6111483367193067913216,6482112187367849721856] 544718574944255015728900398161949631558189055 4537920068239263404312538273026024052470317054 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_40 (k : ℕ) (lo : 4537920068239263404312538273026024052470317055≤k) (hi : k≤37807207924022242178699991307404362612805206014) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,67,71,79,89,97,101,103,109,127,131,139,149,157,191,193,199,241,257,271,293,331,337,353,367,397,409,421,439,461,467,479,547,587,593,613,647,659,661,739,769,857,967,1049,1129,1307,1381,1439,1483,1571,1607,1667,1741,1873,1901,1907,1931,1979,2027,2341,2797,2833,2897,2971,3121,3191,3527,3671,3823,3881,3923,4021,4051,4483,5323,5449,5683,6089,6323,6367,7669,7757,7841,9007,9377,9649,10853,10909,11351,12071,13721,14057,14321]
  let factors : List (ℕ × ℕ × List ℕ) := [(2,2,[3,41,41]),(3,1,[3,13,331]),(2,1,[14321]),(3,1,[3,3,5,11,29]),(2,2,[7669]),(2,1,[3,3,19,103]),(5,1,[11,1741]),(5,1,[19,1049]),(2,2,[5,11,193]),(3,3,[59,139]),(2,2,[59,293]),(7,5,[3,3,271]),(2,2,[13,1873]),(11,3,[3,5,967]),(3,3,[79,191]),(3,3,[5,5,647]),(5,1,[3,3,7757]),(2,2,[23,31,59]),(2,1,[3,3,9649]),(14,3,[3,3,31,79]),(3,3,[13,2027]),(5,5,[3,47,53]),(3,1,[3,3,5,3191]),(6,2,[3,5,6367]),(3,1,[3,5,14057]),(3,5,[13,1307]),(2,2,[5,79,353]),(2,2,[5,19,19,89]),(2,1,[5,5,7,1979]),(2,2,[3,3,11,1907]),(11,3,[3,3,7,1607]),(7,1,[5,17,19,257]),(2,2,[3,5,53,397]),(2,1,[3,3,3,79,421]),(3,3,[17,29,467]),(3,1,[3,3,5,29,857]),(2,1,[3,421711]),(2,2,[5,5,28711]),(5,2,[3,3,3,7,4051]),(3,4,[5,5,5,5,337]),(13,3,[3,3,5,5,29,71]),(2,2,[3,3,116041]),(11,4,[3,3,35227]),(5,3,[3,479,587]),(2,2,[11,210809]),(2,2,[3,3,3,97397]),(3,4,[7,17,6089]),(10,2,[5,7,13,12071]),(11,5,[3,543713]),(6,5,[5,5,129401]),(12,1,[3,5,11593457]),(7,2,[3,17,103,39863]),(5,3,[3,3,3,4177477]),(11,1,[11,52196449]),(6,1,[3,3,3,5,1901,2897]),(5,4,[3,17,769,3923]),(2,2,[17,29,37,67,547]),(7,1,[5,5,7,9275597]),(2,1,[5,837601357]),(2,2,[3,1571,642581]),(2,2,[11,11,109,239137]),(2,1,[241,2797,10853]),(17,3,[3,7,41,2236771]),(6,2,[3,4483,287191]),(11,4,[3,5,6323,11351]),(3,3,[5,739,1262461]),(2,2,[3,14631515363]),(11,5,[3,2461698193]),(2,2,[41,101,103,421,613]),(10,2,[3,3,3,41,103520801]),(3,3,[7,12615911573]),(3,1,[3,3,5,29,347803711]),(2,2,[3,5,5,13,3881,65609]),(5,1,[19,29,29,109,557741]),(13,1,[5,11,2833,21969221]),(5,4,[3,3,157,1148321879]),(2,2,[17,97,37318347161]),(26,3,[3,3,199,439,1129,42461]),(6,1,[3,3,7,7,41,2971,3370001]),(3,3,[7,6846268340231]),(2,2,[13,2530267,10518877]),(2,1,[1384009502208269]),(7,3,[3,5,23,139,38303,1841849]),(7,3,[3,191,409,17225369521]),(7,3,[3,3,3,13,19,53,12113937013]),(5,3,[3,7,25819,8376013571]),(5,26,[3,3,149,458390106829]),(10,25,[3,3823,30677,3706201]),(13,27,[3,29,59,176329,382021]),(5,26,[3,593,1439,3671,78049]),(5,26,[3,37,1667,2341,1795987]),(5,26,[3,3,101,907767685711]),(5,26,[3,79,1381,2674057637]),(5,26,[3,3,409,461,659,830111]),(5,25,[3,661,993051263101]),(5,25,[3,79,367,7841,3062557]),(5,25,[3,3,246151817873957]),(10,25,[3,131,4021,1486943191]),(23,1,[5,7,11,13,17,19,19,5683,236323026529]),(7,27,[3,3,149,458390106829]),(5,30,[3,25961261040433]),(7,1,[5,7,11,13,17,19,27065166019639081]),(5,26,[3,3823,30677,3706201]),(5,26,[3,53,3121,3527,755173]),(7,1,[5,7,11,13,17,19,23,41,9377,3246458951]),(5,28,[3,29,59,176329,382021]),(11,25,[3,5323,175578184357]),(7,1,[5,7,11,11,13,17,19,2768019004416539]),(5,27,[3,593,1439,3671,78049]),(10,25,[3,3,3,97,168269,6748153]),(14,1,[5,7,11,13,17,19,32295087398663977]),(5,27,[3,37,1667,2341,1795987]),(11,27,[3,3,199,440296280717]),(7,1,[5,7,11,13,17,19,34254046678431529]),(10,27,[3,3,101,907767685711]),(13,26,[3,5449,20173,5072689]),(14,1,[5,7,11,13,17,19,36331729457461033]),(10,27,[3,79,1381,2674057637]),(14,1,[5,5,7,11,13,17,19,10909,706491048089]),(5,27,[3,3,409,461,659,830111]),(11,1,[5,7,11,13,17,19,19,139627,15406878649]),(7,26,[3,661,993051263101]),(7,1,[5,7,11,13,13,17,19,23,1483,120713,809929]),(5,26,[3,79,367,7841,3062557]),(14,1,[5,7,11,13,17,19,127,362063815177303]),(10,26,[3,3,246151817873957]),(11,1,[5,7,11,13,13,17,19,1931,1942847269703]),(5,26,[3,131,4021,1486943191]),(14,1,[5,5,5,5,5,7,11,11,13,17,19,191,13721,2871101]),(7,31,[3,25961261040433]),(7,1,[5,7,11,13,17,19,43,157,9007,902335033]),(5,27,[3,53,3121,3527,755173]),(14,1,[5,7,11,13,17,19,193,301532586502249]),(5,26,[3,5323,175578184357]),(7,1,[5,7,7,11,13,17,19,23,383391027052937]),(5,26,[3,3,3,97,168269,6748153]),(11,1,[5,7,11,13,17,19,19,28643,173683,692651]),(5,28,[3,3,199,440296280717]),(11,1,[5,5,7,11,13,13,17,19,69149,15449727037]),(5,27,[3,5449,20173,5072689])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [6875315792072688009216,7292325560806472155136,7734653778719288590336,8203838578512212525056,8701453785831860862976,9229267611842097709056,9789069802812227977216,10382859163692586500096,11012680092018200805376,11680695048691836256256,12389226651792112091136,13140734514130117984256,13937845891447333584896,14783301817529727451136,15680030958228053426176,16631184219511430578176,17640026583738756366336,18710070551370002333696] 4537920068239263404312538273026024052470317055 37807207924022242178699991307404362612805206014 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_41 (k : ℕ) (lo : 37807207924022242178699991307404362612805206015≤k) (hi : k≤314994925738196187620127920066782521967641624574) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,101,103,107,109,113,131,137,149,151,163,167,173,181,191,211,223,257,271,293,307,311,313,317,331,337,367,373,383,401,463,467,487,499,541,577,587,593,601,619,631,653,751,757,761,811,839,911,937,997,1009,1019,1021,1033,1109,1117,1319,1471,1601,1607,1733,1801,1831,1907,2063,2347,2437,2521,2777,2971,3023,3413,3461,3491,3539,3947,4493,4583,4649,5231,5393,5839,5861,6449,6871,7589,8093,8669,8719,9181,10651,10883,12739,12899,12911,13901,14087,17341]
  let factors : List (ℕ × ℕ × List ℕ) := [(13,1,[5,7,313]),(7,1,[12899]),(7,5,[3,3,5,19]),(5,3,[3,11,113]),(3,1,[3,53,101]),(3,5,[1019]),(2,2,[8719]),(2,2,[3,23,137]),(7,4,[3,19,43]),(5,1,[11,1801]),(2,2,[3,3491]),(3,6,[757]),(3,1,[3,3,2971]),(2,1,[59,487]),(5,1,[19,2777]),(2,1,[3,7,2521]),(2,1,[5,41,317]),(3,1,[3,41,653]),(7,1,[109,911]),(3,3,[13,13,149]),(2,1,[73,1601]),(2,2,[3,103,191]),(3,1,[3,3,13,1009]),(2,2,[3,53,383]),(3,1,[3,41893]),(2,2,[3,13,2063]),(2,2,[3,27361]),(2,2,[13,6871]),(13,1,[5,89,467]),(6,2,[3,47,937]),(3,1,[3,3,34877]),(2,1,[61,5393]),(3,1,[3,31,3947]),(10,3,[3,3,10651]),(3,5,[32609]),(2,2,[3,13,23,331]),(2,1,[7,23,29,149]),(3,3,[198599]),(5,1,[7,43,3023]),(6,2,[3,160639]),(19,1,[19,23,2347]),(11,1,[5,251359]),(13,2,[3,7,7,41,131]),(2,1,[3,3,31,5839]),(2,1,[7,233747]),(7,1,[3,101,5861]),(7,6,[3,3,3,13,163]),(6,1,[3,3,401,631]),(3,1,[3,766873]),(2,2,[11,105527]),(2,1,[3,3,321829]),(2,2,[7,17,12911]),(3,3,[5,307,751]),(2,1,[4643189]),(2,1,[3,5,415631]),(7,1,[5,7,13,17341]),(2,1,[811,10883]),(2,2,[43,105883]),(3,1,[3,7,541,811]),(2,1,[3,5,627787]),(11,1,[3,5,11,57467]),(2,1,[3,3551767]),(3,3,[5,23,41,577]),(2,2,[3,3,7,17,17,311]),(7,5,[3,23,13901]),(2,2,[3,3158149]),(2,2,[3,5,13,53479]),(6,3,[5,7,337,499]),(2,2,[5,5,37,12739]),(2,2,[463,37813]),(2,1,[3,3,3,5,11,41,601]),(5,3,[3,3272459]),(2,1,[47085641]),(5,6,[3,53,71,181]),(3,5,[7,37,25799]),(5,1,[7,7,13,357293]),(3,3,[70029677]),(3,3,[5,18964111]),(5,4,[3,18211877]),(5,4,[83,1043489]),(2,2,[3,3,5,30693409]),(3,1,[3,7,7,21310603]),(3,5,[455191283]),(2,2,[1471,4554559]),(3,1,[3,59,71,1927669]),(3,4,[5,79,9222281]),(7,6,[3,41,293,29833]),(3,3,[17,211,3661633]),(5,1,[7,13,257,839,3461]),(2,2,[1117,78539017]),(3,4,[29,1319,734143]),(6,3,[5,1033,1607,21911]),(23,7,[3,3,7,17,15780311]),(2,1,[3,243589,1819847]),(2,1,[17,149,1385753393]),(3,3,[31,58284815921]),(6,1,[5,11,67,105074220569]),(2,2,[3,37,37,68809695169]),(6,2,[3,331,373,3413,528469]),(2,1,[3,6145637,94171283]),(5,3,[3,997,7020226688939]),(5,26,[3,29,761,26799025157]),(10,26,[3,8093,236077,328333]),(5,26,[3,1187629,560237417]),(13,26,[3,48449,14566121057]),(10,27,[3,4649,8669,9286379]),(5,26,[3,367,2163291274369]),(5,28,[3,3,3,271,4583,18833611]),(5,26,[3,3,23,71,39623,4601239]),(10,27,[3,3,1907,4493,18427543]),(5,26,[3,3,31,223,48450032647]),(5,28,[3,593,449307262289]),(10,26,[3,1130405672236333]),(7,1,[5,7,11,13,17,19,47,7589,129971,1588793]),(5,27,[3,29,761,26799025157]),(5,27,[3,47,167,1831,41713621]),(7,1,[5,7,11,13,17,19,12468931,6265317283]),(10,27,[3,8093,236077,328333]),(5,29,[3,3,151,350912327957]),(11,1,[5,7,11,13,17,19,107,774397005593531]),(19,27,[3,1187629,560237417]),(5,28,[3,109,3539,874170097]),(7,1,[5,7,11,13,17,19,173,191,2659768265299]),(5,27,[3,48449,14566121057]),(10,27,[3,3,3258163,73183771]),(7,1,[5,7,11,13,17,19,6449,14454634348409]),(5,28,[3,4649,8669,9286379]),(10,26,[3,1021,39217,37897789]),(11,1,[5,7,11,13,17,19,37,2672230253828533]),(10,27,[3,367,2163291274369]),(5,27,[3,3,2051279,130771777]),(14,1,[5,5,7,11,11,13,17,19,2513591,758564441]),(5,29,[3,3,3,271,4583,18833611]),(14,1,[5,5,7,11,11,13,17,19,1733,201449,5792923]),(5,27,[3,3,23,71,39623,4601239]),(7,1,[5,7,11,13,17,19,131,619,1454917569641]),(5,28,[3,3,1907,4493,18427543]),(7,1,[5,7,11,13,17,19,22649509,5524813621]),(5,27,[3,3,31,223,48450032647]),(11,1,[5,7,11,13,17,19,107,1109,5231,213822113]),(10,29,[3,593,449307262289]),(21,1,[5,7,11,13,17,17,19,23,31,657947,17652227]),(5,27,[3,1130405672236333]),(7,1,[5,7,11,13,17,19,43,3472455126853627]),(5,28,[3,47,167,1831,41713621]),(7,1,[5,7,7,11,13,17,19,19,107,236107,47134301]),(5,30,[3,3,151,350912327957]),(22,1,[5,7,11,13,17,19,167979984212932393]),(23,29,[3,109,3539,874170097]),(7,1,[5,7,7,7,11,13,17,19,31,587,9181,21764441]),(15,28,[3,3,3258163,73183771]),(7,1,[5,7,11,13,17,19,1391363,135821358947]),(5,27,[3,1021,39217,37897789]),(7,1,[5,7,11,13,17,17,17,17,19,37,2437,14087,32119]),(5,28,[3,3,2051279,130771777])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [19845020079174090489856,21048814681087138594816,22325582371023619096576,23679832393933364658176,25116252513738514497536,26639799656056918900736,28255639208496879108096,29969498641192080900096,31787449768984870649856,33715668664835119251456,35760864951569488019456,37930120261468323577856,40230965155105746190336,42671381779334956056576,45259827029731616751616,48005249746131449020416,50917125212194614542336,54005737498538762305536] 37807207924022242178699991307404362612805206015 314994925738196187620127920066782521967641624574 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_42 (k : ℕ) (lo : 314994925738196187620127920066782521967641624575≤k) (hi : k≤2624426974461194131168937844575824509804547670014) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,97,101,103,107,113,131,137,149,151,163,167,173,191,199,223,227,233,251,257,263,269,277,281,283,293,307,313,331,347,359,373,383,389,439,467,487,491,521,587,601,617,659,743,809,823,883,941,983,997,1103,1181,1193,1201,1291,1303,1459,1579,1667,1877,2113,2129,2239,2251,2273,2609,2797,3499,3529,3559,4013,4817,5059,5531,5741,6977,7589,8269,9551,10687,11467,12983,13009,13523,15373,16433,18427,19427,19553]
  let factors : List (ℕ × ℕ × List ℕ) := [(3,3,[37,71]),(7,1,[5,5,491]),(2,1,[3,3,3,467]),(2,1,[73,233]),(2,1,[5,61,73]),(10,1,[23,997]),(3,1,[3,7,1103]),(6,1,[3,5,1877]),(2,1,[5,5,1193]),(2,2,[5,5,5,5,5,5]),(3,3,[31,257]),(7,4,[3,11,137]),(14,1,[3,12983]),(5,1,[107,373]),(7,3,[3,3,3,383]),(11,1,[3,3,5,983]),(7,2,[3,79,97]),(2,1,[3,18427]),(13,1,[5,11467]),(2,1,[62501]),(12,1,[3,5,17,269]),(3,5,[7,617]),(2,2,[3,13523]),(5,1,[7,7,1667]),(11,2,[3,3,3,7,293]),(5,1,[114671]),(2,1,[3,13,3559]),(2,1,[3,3,3,5,1459]),(3,3,[5,13009]),(7,7,[3,3,5,5,23]),(5,5,[3,19,389]),(6,3,[5,67,283]),(6,2,[3,5,5,11,257]),(10,1,[3,5,5,7,7,199]),(5,1,[61,73,167]),(2,1,[758441]),(5,3,[3,3,59,439]),(5,1,[7,17,8269]),(17,4,[3,44531]),(2,2,[5,7,7,13,191]),(2,2,[3,3,61,1181]),(2,2,[13,56311]),(2,1,[3,149,3499]),(2,1,[3,5,7,21017]),(3,5,[11,13,1291]),(3,3,[5,31,5059]),(3,3,[19,45863]),(2,2,[1864873]),(2,2,[883,2251]),(2,1,[3,19,72337]),(2,2,[7,59,5531]),(2,1,[3,5,17,19427]),(6,1,[3,3,3,221509]),(10,5,[3,137191]),(2,1,[7459493]),(6,1,[3,3,389,2239]),(2,1,[3,7,43,9551]),(3,3,[1201,1877]),(6,1,[3,3,13,19,4817]),(3,6,[5,79,941]),(3,4,[29,263,313]),(7,1,[5,4413571]),(5,1,[3,9907771]),(17,6,[3,3,11,10687]),(17,1,[3,11961487]),(2,2,[3,3,3,467,2273]),(7,1,[5,13170337]),(5,1,[137,251,2609]),(2,1,[97,281,3529]),(10,1,[3,11,2928173]),(2,1,[5,11,11,162277]),(2,1,[487,229343]),(11,4,[3,6273161]),(7,1,[2113,79823]),(3,3,[29,1462651]),(22,3,[3,5,5,5,5,5,5,19,59]),(2,1,[37,5907617]),(2,2,[193259419]),(2,2,[17,31,520361]),(3,4,[5,14918987]),(3,3,[179431367]),(15,3,[3,31,1968023]),(3,3,[196355171]),(2,1,[5,11,823,19553]),(6,1,[3,5,7,17249107]),(5,3,[3,13,44135711]),(2,1,[11,31,73,2593477]),(2,2,[3,61,223380083]),(7,1,[5,5,5,59,223,59651]),(3,6,[587,6971177]),(2,2,[11,31,339335033]),(17,3,[3,3,5,13,19,67,138209]),(3,1,[3,13,4013,8246419]),(13,1,[19,46327,1516883]),(2,2,[3,71,269,18034217]),(3,4,[1579,301111729]),(3,1,[3,3,3,3,3,47,103,9137213]),(2,1,[3,3,13,19,167,2797,91957]),(11,4,[3,3,5,17,43,420375001]),(6,2,[3,163,462852985013]),(3,1,[3,7,277,88471,7950533]),(3,3,[7,19,6977,3622312471]),(2,2,[53,97,659,5741,1487303]),(10,30,[3,3,2129,25219,662401]),(5,27,[3,905340438685429]),(5,26,[3,3,101,7589,24551,34019]),(5,27,[3,709537,1435450937]),(5,27,[3,3,23,113,163367,848101]),(5,28,[3,3,190969139115379]),(5,27,[3,61,277603,71768923]),(5,28,[3,23,107,261893177537]),(13,30,[3,3,59,809,1193518961]),(5,27,[3,21416383,67712833]),(5,33,[3,3,3,2670360272159]),(5,27,[3,41,73,347,1570841369]),(7,1,[5,7,7,11,13,17,19,37,2433341,337331999]),(5,31,[3,3,2129,25219,662401]),(10,27,[3,3,393931,1464209113]),(11,1,[5,7,11,13,17,19,131,125003,13770341833]),(7,28,[3,905340438685429]),(5,27,[3,3,743,823399466761]),(7,1,[5,7,11,13,17,19,23,47,221251770526321]),(5,27,[3,3,101,7589,24551,34019]),(5,28,[3,3,227,1303,1096920989]),(7,1,[5,7,11,13,17,19,31,8183257933070263]),(15,28,[3,709537,1435450937]),(10,27,[3,15677479,131703371]),(14,1,[5,7,11,13,17,19,59,359,16433,773037677]),(5,28,[3,3,23,113,163367,848101]),(5,28,[3,41,199,307,437163659]),(14,1,[5,7,11,13,17,19,110563,2581244596867]),(7,29,[3,3,190969139115379]),(10,28,[3,281,4133226125797]),(7,1,[5,7,11,13,17,17,19,151,601,196207051751]),(5,28,[3,61,277603,71768923]),(11,1,[5,5,7,11,13,17,19,29,103,21497358592639]),(7,29,[3,23,107,261893177537]),(7,1,[5,7,11,13,17,19,192379907,1770133091]),(5,31,[3,3,59,809,1193518961]),(7,1,[5,5,7,11,11,13,17,19,331,521,997,38196017]),(5,28,[3,21416383,67712833]),(7,1,[5,7,11,13,17,19,77899,82729,59446627]),(7,34,[3,3,3,2670360272159]),(11,1,[5,7,11,13,17,19,149,23788481,114641029]),(10,28,[3,41,73,347,1570841369]),(7,1,[5,7,11,13,17,19,73,883,2137489,3128107]),(5,28,[3,3,393931,1464209113]),(14,1,[5,7,11,13,17,17,19,26890338053217689]),(5,28,[3,3,743,823399466761]),(7,1,[5,7,11,13,17,19,63737,7607286721457]),(7,29,[3,3,227,1303,1096920989]),(11,1,[5,7,7,11,11,13,13,17,19,23,173,129118845923]),(7,28,[3,15677479,131703371]),(7,1,[5,7,7,11,13,17,19,31,15373,163514220757]),(5,29,[3,41,199,307,437163659]),(14,1,[5,5,7,11,13,17,19,115712429091182549]),(5,29,[3,281,4133226125797])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [57281664789992372699136,60756368373440793542656,64441820736861750951936,68350750537930313302016,72496882365142438772736,76894331910546297716736,81558702198825026584576,86505890585850985578496,91753150433959530725376,97318856341328490397696,103221990337145078808576,109483433553975559847936,116124646782161362354176,123168750913723790524416,130640176088303592800256,138564827681631110168576,146970186007097561317376,155885373796035063709696] 314994925738196187620127920066782521967641624575 2624426974461194131168937844575824509804547670014 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_43 (k : ℕ) (lo : 2624426974461194131168937844575824509804547670015≤k) (hi : k≤21865985680473949388194443528516696172678921322494) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,109,127,131,137,151,157,163,167,179,181,191,193,199,227,233,239,251,257,277,283,307,331,337,349,389,397,409,431,433,463,467,523,557,577,641,709,761,787,857,919,997,1123,1259,1303,1373,1439,1471,1493,1579,1613,1693,1789,1873,1979,1987,2113,2129,2311,2393,2521,2753,2879,2963,3623,4007,4253,4987,6521,7333,7547,7963,8237,8423,8647,8863,9293,9521,10691,10771,10853,11027,11503,14173,14783,17053,17419,17911,18433,18743,19141,19319]
  let factors : List (ℕ × ℕ × List ℕ) := [(3,1,[3,47,71]),(5,1,[10691]),(13,1,[17,787]),(2,1,[3,11,433]),(2,2,[3,31,79]),(5,5,[3,307]),(2,2,[3,2521]),(2,2,[47,167]),(17,1,[5,4987]),(2,1,[3,8423]),(2,2,[3,11,13,31]),(2,2,[37,397]),(14,1,[7,7,13,47]),(2,2,[3,61,83]),(7,4,[3,5,5,53]),(3,1,[3,3,3,13,109]),(14,4,[3,3,557]),(2,2,[3,5,1471]),(3,3,[23,523]),(2,1,[19,41,79]),(6,1,[3,7,2963]),(5,7,[3,433]),(5,4,[3,3,1303]),(3,1,[3,5,53,191]),(6,2,[3,5,5,1123]),(2,2,[3,3,9521]),(2,2,[3,30253]),(3,1,[3,63601]),(5,1,[11,19141]),(2,2,[17,67,101]),(2,1,[3,3,13,2113]),(7,1,[23,18433]),(3,3,[5,13,1693]),(5,2,[3,17,71,89]),(5,1,[7,96233]),(5,1,[3,17,23,641]),(3,1,[3,3,3,29389]),(2,2,[7,7,83,101]),(3,6,[28579]),(2,1,[577,1613]),(6,1,[5,187633]),(29,3,[3,5,37,431]),(2,2,[227,2129]),(13,3,[3,3,5,6521]),(2,1,[3,494443]),(7,2,[3,5,53197]),(2,1,[1643069]),(5,1,[761,2311]),(7,1,[23,179,467]),(3,3,[847919]),(5,1,[73,49871]),(3,2,[5,7,11,23,251]),(2,1,[3,1503787]),(2,2,[5,5,5,13,1439]),(2,2,[7,363037]),(7,1,[3,5,43,9293]),(2,1,[3,5,5,19,7333]),(2,1,[3,3517343]),(3,1,[3,13,23,17053]),(5,5,[3,13,31397]),(2,2,[89,123083]),(3,1,[3,13,331,1789]),(2,2,[3,3,1861403]),(3,3,[8890421]),(10,1,[5,31,381607]),(2,2,[3,3,7,11,50539]),(5,4,[3,3,11,13,8863]),(5,1,[118298171]),(3,1,[3,3,3,23,181,1259]),(2,2,[3,43,1587007]),(2,2,[29,409,19319]),(3,1,[3,3,31,227,11027]),(2,2,[5,1579,59879]),(7,1,[7,29,67,76519]),(3,1,[3,13,39183457]),(2,1,[37,4007,10771]),(7,1,[3,3,5,5,7,131,8237]),(2,2,[233,283,18743]),(5,1,[13,19,71,166273]),(2,1,[4943578709]),(13,4,[3,239,880361]),(3,2,[5,5,182506897]),(13,1,[3,5,163,337,20023]),(2,1,[3,277,30593083]),(3,1,[3,3,9887157419]),(3,1,[3,5,11,29,37,61,89,389]),(3,3,[431,283025719]),(2,2,[3,7,257,67010509]),(2,2,[5,11,127,131,460157]),(14,3,[3,193,2081469839]),(2,2,[11,53,59,2393,60757]),(3,4,[73,10853,1933133]),(2,1,[3,1493,3056309647]),(2,2,[7,7,31,50845703947]),(6,2,[3,3,13,19,23,349,7281167]),(11,4,[3,5,37,177968833543]),(2,2,[4253,17419,9353501]),(7,1,[3,5,157,2347561,3286139]),(34,3,[3,5,5,7,101,1446622868293]),(11,3,[3,5,3623,1684239041981]),(14,3,[3,3,3,3,3,3,3,3,151,11503,10165037]),(17,3,[3,5,43817549,236596343]),(15,27,[3,23,1373,8647,9022723]),(5,27,[3,97,1289077,20899051]),(10,27,[3,2771741920230029]),(5,27,[3,7963,124447,2966659]),(5,28,[3,3,519701187410029]),(5,28,[3,103,2753,5831859203]),(5,28,[3,1913641,916570637]),(10,28,[3,3,31,20004125839589]),(10,28,[3,163,14783,818895613]),(5,27,[3,3,239,1829057,3191821]),(10,27,[3,857,1347263,3845279]),(5,29,[3,43,27378421817827]),(14,1,[5,7,11,13,17,19,613657420729890601]),(7,28,[3,23,1373,8647,9022723]),(5,28,[3,193,709,18250689701]),(7,1,[5,7,11,13,17,17,19,11987971,3193795379]),(5,28,[3,97,1289077,20899051]),(10,28,[3,3,26759,32996502391]),(7,1,[5,7,11,13,17,19,19,36334879375371091]),(7,28,[3,2771741920230029]),(5,28,[3,2879,975872679113]),(11,1,[5,7,11,13,17,19,732239765891659561]),(7,28,[3,7963,124447,2966659]),(5,37,[3,3,3,463,1396745983]),(7,1,[5,7,11,13,17,19,23,997,17911,1890978821]),(7,29,[3,3,519701187410029]),(10,29,[3,1580363241861841]),(11,1,[5,7,11,13,17,19,43,1987,9641368294249]),(5,29,[3,103,2753,5831859203]),(5,28,[3,239,303691,46188403]),(7,1,[5,7,11,13,17,19,137,1876331,3398998051]),(5,29,[3,1913641,916570637]),(11,1,[5,7,11,13,17,19,926738180095555369]),(7,29,[3,3,31,20004125839589]),(7,1,[5,7,11,11,13,17,19,21383,58757,71123369]),(5,29,[3,163,14783,818895613]),(7,1,[5,7,11,13,17,19,29,37,919,7547,140094109]),(5,28,[3,3,239,1829057,3191821]),(7,1,[5,5,5,7,11,13,13,17,19,336901,10099501393]),(15,28,[3,857,1347263,3845279]),(7,1,[5,7,11,11,13,17,19,23,41,1979,8423,6783353]),(5,30,[3,43,27378421817827]),(7,1,[5,7,11,13,17,19,1244048622314796841]),(5,29,[3,193,709,18250689701]),(7,1,[5,5,7,11,11,13,17,19,14173,80209,21104059]),(5,29,[3,3,26759,32996502391]),(7,1,[5,7,7,11,13,17,19,41,199,24504981580433]),(5,29,[3,2879,975872679113]),(7,1,[5,5,7,11,13,17,19,31,31,308938497181973]),(5,38,[3,3,3,463,1396745983]),(31,1,[5,5,7,11,13,17,19,421103,747795943291]),(5,30,[3,1580363241861841]),(11,1,[5,7,11,13,17,19,1873,29473,88261,342757]),(7,29,[3,239,303691,46188403])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [165341298535542015655936,175370704651786456662016,186008451567815864877056,197291631522824203534336,209259337839228890382336,221952657545405457760256,235416170262421911371776,249696473835862707142656,264843067112418030125056,280908454631958103719936,297948324983771701968896,316021583244835805986816,335191277260572549185536,355524000845781056618496,377089732352713536045056,399963882404653087850496,424225527474821577834496,449958698521051808137216] 2624426974461194131168937844575824509804547670015 21865985680473949388194443528516696172678921322494 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_44 (k : ℕ) (lo : 21865985680473949388194443528516696172678921322495≤k) (hi : k≤182183349958096900658611386065147197364161757577214) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,107,109,113,137,139,149,151,157,181,193,197,199,227,229,263,269,281,283,293,307,313,331,337,373,383,439,457,463,487,557,577,659,701,727,757,769,881,911,967,983,1009,1061,1117,1259,1319,1361,1453,1523,1531,1721,1777,1879,1931,2029,2473,2593,2797,2999,3083,3203,3637,3947,4129,4153,4463,5179,5507,5519,6047,6779,7129,8699,9043,9521,9851,9967,10607,12113,12637,13513,14153,14753,15583,15809,16943,17207]
  let factors : List (ℕ × ℕ × List ℕ) := [(2,1,[14153]),(6,4,[7,17,17]),(5,1,[3,41,137]),(11,4,[3,3,13,19]),(2,1,[101,181]),(11,1,[5,11,11,31]),(3,3,[5,11,89]),(3,4,[47,53]),(3,4,[2797]),(3,1,[3,3,3,3,373]),(10,1,[3,3,5,17,41]),(3,1,[3,19,557]),(3,1,[3,17,701]),(3,3,[5,1879]),(11,4,[3,37,43]),(2,1,[7,6047]),(2,2,[3,5,5,313]),(10,2,[3,5,1777]),(2,2,[3,9851]),(2,1,[3,89,263]),(3,1,[3,3,9967]),(2,2,[5,12113]),(2,2,[76369]),(3,3,[39161]),(2,1,[151,1319]),(5,2,[3,44753]),(3,3,[7,10607]),(2,2,[3,3,3,29,193]),(3,1,[3,5,89,227]),(2,2,[31,5179]),(3,4,[23,1931]),(13,1,[5,71503]),(3,1,[3,3,5,67,139]),(3,3,[13,8699]),(3,1,[3,7,7,13,281]),(7,5,[3,59,229]),(2,1,[3,3,3,3,37,229]),(2,1,[3,5,113,487]),(3,6,[33703]),(6,1,[3,5,75161]),(3,1,[3,157,4153]),(11,3,[3,3,7,7,1361]),(2,2,[1297057]),(2,2,[3,3,3,3,3,6779]),(11,4,[3,5,7,3947]),(3,1,[3,73,15809]),(5,4,[3,3,3,3,53,137]),(3,3,[457,3203]),(2,2,[7,7,60427]),(5,1,[47,107,1259]),(6,1,[3,13,43,5507]),(2,2,[4801609]),(5,2,[3,1650931]),(5,1,[12663023]),(6,1,[3,5,7,229,727]),(2,2,[9410257]),(2,1,[13,181,14753]),(11,6,[3,41,89,107]),(6,2,[3,11,11,62731]),(2,1,[11,43,106621]),(2,1,[3,37,715031]),(7,1,[3,3,5,5,5,5,5,2999]),(3,1,[3,3,47,242261]),(13,10,[3,3,5,4463]),(2,2,[11,11,59,9521]),(2,1,[5,5,13,710609]),(2,2,[97,1372627]),(3,2,[5,5,7,23,39857]),(7,2,[3,5,11843693]),(47,3,[3,5,7,17,181,283]),(5,1,[461895851]),(5,1,[29,18470479]),(2,1,[641697701]),(7,2,[3,59,2254831]),(2,1,[149,6630961]),(2,1,[7,11,91085413]),(3,3,[35569,84659]),(7,5,[3,5,5,11710169]),(7,4,[3,5,11,881,12637]),(13,1,[5,463,6589189]),(3,4,[151,193,93901]),(2,1,[7,13,331,2156993]),(2,1,[113,710621581]),(3,1,[3,3,5,61,37641029]),(3,3,[7,41,3083,37511]),(2,1,[3,137,137,3912127]),(12,1,[3,11,17,113,113,32369]),(3,5,[11,71,4129,5519]),(5,4,[3,61,271881677]),(12,1,[3,5,7,14027153603]),(11,3,[5,13,41,1523,140443]),(5,1,[3,3,3,7,659,34961431]),(5,1,[3637,1283395403]),(2,1,[23,983,9043,36563]),(5,3,[3,13,41,307,577,7129]),(5,1,[14950843752563]),(3,1,[3,263,160600477307]),(7,1,[5,63499,1596420349]),(7,3,[3,3,79,265524164249]),(2,2,[5,227,440560269979]),(5,1,[1013710957411511]),(13,1,[5,398339,532579277]),(3,1,[3,3,439,569516471393]),(2,2,[5,5,7,109,1453,204952807]),(2,1,[383,305477,923791703]),(6,1,[3,5,7,197,8708962384963]),(7,3,[3,83,1117,796069550257]),(11,28,[3,17207,206649249211]),(5,30,[3,101,9335418161423]),(5,29,[3,2000143625704661]),(5,29,[3,2121470966209031]),(11,28,[3,4500319156947487]),(5,29,[3,3,28307,28104405601]),(5,34,[3,2593,30507945071]),(5,32,[3,313289,1071287783]),(10,28,[3,3,25326047,74965057]),(5,30,[3,1510301446248313]),(5,28,[3,43,293,2473,205655041]),(5,28,[3,3,37,37,43,67,967,593993]),(21,1,[5,7,11,13,17,19,1771305697773041449]),(5,29,[3,17207,206649249211]),(5,28,[3,41,157,1531,731464441]),(14,1,[5,7,11,13,17,19,83,757,29901687505127]),(5,31,[3,101,9335418161423]),(5,28,[3,29,2029,129941572307]),(7,1,[5,7,7,11,11,13,17,19,73,179407,1976026379]),(5,30,[3,2000143625704661]),(13,30,[3,2027421914823023]),(14,1,[5,7,11,13,17,19,269,16943,463744771843]),(5,30,[3,2121470966209031]),(5,28,[3,3,139,1073983,19206437]),(7,1,[5,7,7,11,13,13,17,19,838171,29391640081]),(7,29,[3,4500319156947487]),(5,30,[3,3,3,253427553190447]),(11,1,[5,7,11,11,13,17,19,216162992431915547]),(15,30,[3,3,28307,28104405601]),(5,29,[3,1061,4560234769481]),(14,1,[5,7,7,11,13,17,19,360289773865919311]),(5,35,[3,2593,30507945071]),(11,1,[5,7,11,13,17,19,199,337,911,43784909489]),(7,33,[3,313289,1071287783]),(19,1,[5,7,11,13,17,19,604477,904697,5188229]),(7,29,[3,3,25326047,74965057]),(11,1,[5,7,7,11,13,17,19,23,769,1009,24089887769]),(5,31,[3,1510301446248313]),(7,1,[5,5,7,7,11,13,17,19,29,19811173,158736883]),(5,29,[3,43,293,2473,205655041]),(14,1,[5,7,11,13,17,19,149,22721867499967301]),(7,29,[3,3,37,37,43,67,967,593993]),(7,1,[5,7,11,13,17,19,37,47,701,2945702256631]),(5,29,[3,41,157,1531,731464441]),(11,1,[5,7,11,13,17,19,137,1721,16154043725353]),(5,29,[3,29,2029,129941572307]),(11,1,[5,7,11,13,13,17,19,15583,118213,168693751]),(5,31,[3,2027421914823023]),(7,1,[5,5,5,7,11,13,17,17,19,23,31,41,537037,642197]),(5,29,[3,3,139,1073983,19206437]),(7,1,[5,7,11,11,13,17,19,59,69427619,100863467]),(5,31,[3,3,3,253427553190447]),(11,1,[5,5,7,11,13,17,17,19,13513,606091,6924343]),(5,30,[3,1061,4560234769481])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [477253226767560900345856,506203360684677452005376,536909466231523996860416,569478026205081827803136,604022612520367120449536,640662616018922112024576,679524828241295338110976,720744213436161616510976,764464674494047045287936,810836914842250778771456,860021749752090691895296,912190710406747684601856,967524121255731062112256,1026214260305163123163136,1088463852419822676606976,1154489934793204769488896,1224520934465554115198976,1298800550501261032554496] 21865985680473949388194443528516696172678921322495 182183349958096900658611386065147197364161757577214 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_45 (k : ℕ) (lo : 182183349958096900658611386065147197364161757577215≤k) (hi : k≤1517925041354314083167506089471868852362815666651134) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,79,83,89,97,101,103,107,109,113,127,131,149,151,157,167,173,193,223,233,239,241,257,263,269,277,283,311,313,331,337,353,367,379,433,491,503,523,563,577,587,617,631,641,653,659,661,761,787,797,881,953,967,1063,1087,1201,1237,1249,1361,1427,1531,1553,1609,1621,1693,1747,1951,1987,2081,2237,2243,2311,2671,2729,2879,3011,3079,3137,3187,3331,3457,3583,3637,4289,4391,4523,4861,5119,5563,7127,7573,7741,8293,8861,9497,10433,11621,12911,13963,19391]
  let factors : List (ℕ × ℕ × List ℕ) := [(3,1,[3,5,5,151]),(5,5,[3,3,89]),(10,4,[3,7,7,11]),(6,1,[3,59,83]),(2,2,[7573]),(11,1,[5,3331]),(14,1,[3,3,3,3,13,17]),(3,3,[7,641]),(3,3,[13,353]),(5,1,[19391]),(3,8,[157]),(5,4,[3,3,3,103]),(2,2,[43,283]),(3,4,[3187]),(2,1,[5,11,491]),(2,1,[11,37,67]),(10,2,[5,2729]),(2,1,[3,59,157]),(3,1,[3,7,17,83]),(2,1,[40193]),(2,2,[25633]),(3,5,[7,587]),(3,4,[8293]),(11,7,[3,3,7,17]),(3,5,[5,17,53]),(2,2,[149,263]),(6,2,[3,3,7,631]),(2,2,[7,7,1237]),(2,1,[3,5,7,1237]),(6,3,[5,7,967]),(2,2,[3,11,31,83]),(17,4,[3,11,761]),(13,1,[5,17,2879]),(5,4,[11,11,277]),(2,1,[270761]),(3,1,[3,107,953]),(3,2,[5,5,61,103]),(11,1,[11,19,1531]),(7,4,[3,23,23,31]),(10,3,[3,35803]),(3,5,[41,661]),(2,2,[353,653]),(2,1,[263,2311]),(7,1,[639959]),(10,1,[3,7,7,17,269]),(2,1,[5,5,30293]),(2,2,[401809]),(2,2,[11,50993]),(7,1,[1279919]),(2,1,[3,489431]),(2,2,[193,5119]),(3,4,[19,13963]),(11,1,[3,787153]),(2,1,[3,3,3,3,37,797]),(17,3,[3,7,71,577]),(6,1,[5,5,29,4861]),(3,1,[3,3,5,80387]),(3,4,[41,11621]),(2,1,[7,31,43,503]),(2,2,[5,536273]),(2,1,[5,7,13,22651]),(2,2,[3,7,17,17,1087]),(5,1,[11,641,2081]),(7,1,[7,7,13,17,1951]),(2,2,[257,54581]),(7,2,[3,3,3,3,5,149,233]),(2,2,[11,787,2237]),(15,1,[3,5,13,47,4523]),(2,2,[3,3,11,167,1693]),(2,1,[56109269]),(2,2,[3,5,29,241,269]),(3,5,[13,193,1427]),(29,5,[3,3,5,7,7,23,101]),(11,3,[3,6882457]),(2,1,[3,7,1747,3079]),(7,1,[5,5,7,7,7,7,2243]),(2,2,[23,61,54011]),(2,2,[3,7,13,37,37,337]),(34,3,[3,5,5,1607237]),(2,2,[3,3,82906591]),(17,4,[3,3,5,5,7,159013]),(3,1,[3,3,3,761,102533]),(2,1,[5,5,114570977]),(3,3,[5,5,5,131,48677]),(3,1,[3,3,3,7,1201,55579]),(3,3,[5,47,20612411]),(7,4,[3,5,37,7048451]),(2,2,[43,43,1621,5563]),(11,1,[659,1609,137089]),(5,2,[3,3,31,379,867233]),(3,3,[5,1987,4722919]),(2,1,[3,3,62590244881]),(11,1,[367,523,1249,4391]),(14,2,[3,5,311,303109733]),(2,2,[3,5,31,2671,1215587]),(2,2,[3,617,29383,54539]),(2,2,[3,7,7,628301,9386987]),(13,4,[3,61,1361,3637,242453]),(7,2,[3,5,2311,66694339709]),(3,1,[3,5,131489,375377602121]),(29,3,[3,5,10725461,4213491103]),(7,3,[3,103,3513986274997489]),(17,3,[3,3,5,7,7,4244753,165178969]),(5,29,[3,37,149,3457,269272151]),(10,29,[3,37,36713,4007127601]),(11,31,[3,239,6039109151221]),(10,29,[3,101,541523,111961477]),(5,31,[3,3,71,259771,29346263]),(5,31,[3,7623377,225918547]),(11,29,[3,3,3,7234831,112218539]),(5,29,[3,59,103,103,433,3011,9497]),(5,29,[3,37,38783,5728548851]),(5,29,[3,71,109,1126624407859]),(10,29,[3,9247837144049941]),(5,29,[3,3,1553,2105346701639]),(11,1,[5,5,7,11,13,17,19,26388013,38751332681]),(5,30,[3,37,149,3457,269272151]),(5,29,[3,3,3467937751623157]),(14,1,[5,7,11,13,17,19,5422996139888817961]),(5,30,[3,37,36713,4007127601]),(5,29,[3,1951,5656027617781]),(29,1,[5,7,7,11,11,13,17,19,77462837,964342201]),(7,32,[3,239,6039109151221]),(5,29,[3,3,611827,6376687001]),(11,1,[5,7,11,13,17,19,53,313,2243693,163910881]),(5,30,[3,101,541523,111961477]),(5,31,[3,3,3,79,173,25231643263]),(11,1,[5,7,11,13,17,19,103,881,3137,7741,2936587]),(5,32,[3,3,71,259771,29346263]),(5,29,[3,35897,366808338613]),(7,1,[5,7,11,13,13,17,19,44497,11865053911549]),(5,32,[3,7623377,225918547]),(5,29,[3,223,7127,25873,339637]),(7,1,[5,7,11,13,17,17,19,8861,859273,56241541]),(5,30,[3,3,3,7234831,112218539]),(7,1,[5,5,7,11,13,17,17,19,97,10433,59263,1514651]),(10,30,[3,59,103,103,433,3011,9497]),(11,1,[5,7,11,13,17,19,144161,1344463,42254759]),(10,30,[3,37,38783,5728548851]),(7,1,[5,7,11,13,17,19,8686574071793792809]),(5,30,[3,71,109,1126624407859]),(11,1,[5,5,7,11,13,17,19,1063,3583,4289,112802461]),(5,30,[3,9247837144049941]),(7,1,[5,7,11,13,17,19,29,33311,2559839,3951869]),(5,30,[3,3,1553,2105346701639]),(7,1,[5,7,7,11,13,17,19,1480740765758645071]),(5,30,[3,3,3467937751623157]),(11,1,[5,7,11,13,17,19,29,101,12911,290719432919]),(5,30,[3,1951,5656027617781]),(11,1,[5,7,11,13,17,17,19,31,331,132689,503797477]),(5,30,[3,3,611827,6376687001]),(22,1,[5,7,11,13,17,19,12368178822881949481]),(10,32,[3,3,3,79,173,25231643263]),(7,1,[5,7,11,13,17,19,19,156749,922037,4777219]),(5,30,[3,35897,366808338613]),(7,1,[5,7,11,13,17,19,113,127,563,577,2984637277]),(5,30,[3,223,7127,25873,339637])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [1377585903814109871210496,1461149484114393574670336,1549782134012743679737856,1643791682056258506981376,1743503987262483937099776,1849265015168671422611456,1961441631972693991489536,2080421960811566487044096,2206620374434253557989376,2340474323845487060320256,2482447380776783599108096,2633032461117441290797056,2792752355209730668363776,2962161066171618700558336,3141845841682434764046336,3332430567958883793371136,3534575261591651395567616,3748981394195152136830976] 182183349958096900658611386065147197364161757577215 1517925041354314083167506089471868852362815666651134 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_46 (k : ℕ) (lo : 1517925041354314083167506089471868852362815666651135≤k) (hi : k≤12647179923613923665559974066223780521992910605910014) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,89,97,101,103,107,109,113,127,131,137,139,149,151,157,167,179,181,191,193,197,199,211,223,227,229,233,269,277,293,307,373,379,419,421,433,439,487,541,571,593,619,661,683,709,787,809,811,821,823,857,883,929,937,953,971,1021,1069,1283,1367,1409,1471,1613,1697,1723,1747,1801,1997,2027,2203,2351,2473,2687,3067,3089,3119,3623,4021,4229,4447,4451,4457,4603,4799,5591,6763,7349,8377,8821,9181,9391,9433,10037,10271,10691,10711,10891,11261,13799,13903,14437,14639,15259,17929]
  let factors : List (ℕ × ℕ × List ℕ) := [(2,1,[3,3623]),(5,3,[3,1069]),(3,1,[3,3,5,293]),(2,2,[5,1697]),(3,4,[17,149]),(5,2,[3,3,29,43]),(10,7,[3,7,17]),(2,1,[5,71,71]),(3,1,[3,7,1283]),(3,2,[5,5,5,113]),(14,1,[7,7,13,47]),(3,1,[3,10037]),(3,1,[3,11261]),(14,4,[3,5,307]),(5,3,[3,3119]),(2,2,[3,7,19,47]),(7,1,[5,11,11,67]),(2,1,[5,7,11,113]),(5,1,[3,31,487]),(5,1,[50411]),(3,3,[7,2027]),(3,1,[3,3,3,3,709]),(3,2,[5,17,379]),(3,3,[11,1471]),(2,1,[3,3,41,229]),(3,4,[10891]),(5,4,[3,7,541]),(3,2,[5,17,787]),(3,5,[7,1409]),(5,2,[3,17,1613]),(2,2,[5,79,233]),(2,2,[3,7,4457]),(10,2,[3,5,7,971]),(2,2,[7,17929]),(12,1,[3,3,3,5,13,199]),(6,1,[19,31,821]),(2,1,[269,1801]),(7,3,[3,5,11,823]),(3,3,[19,41,181]),(2,1,[5,5,7,7,17,37]),(7,1,[967139]),(6,4,[11,13,929]),(2,1,[13,223,419]),(7,1,[5,31,9181]),(2,1,[3,5,157,619]),(11,5,[3,3,10271]),(5,1,[661,2351]),(5,1,[3,7,87011]),(3,5,[23,6763]),(3,2,[19,67567]),(2,1,[17,67,3067]),(3,1,[3,3,7,7,7,23,79]),(2,2,[5,5,5,43,593]),(11,2,[3,3,3,5,7,4021]),(6,1,[17,107,4451]),(3,1,[3,3,968939]),(2,1,[3,2915491]),(7,1,[7,433,4229]),(2,1,[3,3,13,113513]),(5,3,[3,1934279]),(19,1,[25636199]),(2,2,[17440903]),(2,2,[3,3,3,3,3,7,11,1997]),(2,2,[13,17,174257]),(3,3,[11,149,13799]),(3,2,[7,1747,4447]),(3,1,[3,3,3,7,7,137,883]),(2,2,[571,169003]),(2,2,[3,7,421,13903]),(2,2,[7,11,19,53,4603]),(5,3,[3,71,683,1723]),(2,1,[1427648069]),(3,1,[3,5,47,1409,2203]),(5,1,[7,386002853]),(3,3,[11,320089267]),(3,1,[3,3,191,1021,8377]),(5,4,[3,193,3654463]),(2,1,[3,3,211,17492947]),(13,1,[3,10691,1127993]),(3,3,[7,97,227,74857]),(5,1,[3,19,103,15199381]),(3,7,[7,809,329053]),(11,3,[3,5,7,7,51272399]),(7,1,[3,3,5,199,439,40529]),(26,3,[3,5,4376678071]),(3,3,[37,59,139,407821]),(5,3,[3,90583,502013]),(2,1,[23,29404928647]),(3,1,[3,5,131,8821,114859]),(3,3,[14639,149463469]),(3,7,[5,5,44893,368141]),(2,1,[3,101,167,2687,3108023]),(2,2,[7,67,379,2005282537]),(3,3,[929,301481706121]),(2,1,[31,2125553,26562043]),(5,1,[2958049,2855296139]),(5,3,[3,41,17503965781529]),(2,2,[4799,989983846217]),(2,2,[19,4977569,217529453]),(2,1,[82290357499821533]),(37,5,[3,5,7,17,3981762969271]),(11,4,[3,3,5,698491,491665693]),(13,1,[5591,1541051,16192739]),(2,2,[61,17223902329024537]),(2,2,[5,13,13,2240612039891273]),(15,3,[3,3,3,3,3,7,23,23,97,33854945233]),(5,3,[3,59879,129449,180932489]),(10,29,[3,75013,181777,1086361]),(10,30,[3,89,277,318658857211]),(10,34,[3,11218159,46422697]),(10,29,[3,3,3,12749501,154043189]),(5,31,[3,73,109,109,5404039943]),(11,32,[3,47,52886252521601]),(5,30,[3,374389,28167855497]),(5,32,[3,127,315617,69763613]),(10,32,[3,3,10711,92303471849]),(5,33,[3,21739,72356238979]),(10,30,[3,3,43,197,525201368521]),(10,30,[3,3,15259,60223,5135093]),(7,1,[5,7,11,11,13,17,19,293,25657,178471131703]),(5,30,[3,75013,181777,1086361]),(13,32,[3,56501,66438212707]),(7,1,[5,5,7,11,13,17,19,953,1367,3089,14437,53887]),(5,31,[3,89,277,318658857211]),(5,30,[3,3,3,3,2473,238518673793]),(7,1,[5,7,11,13,17,19,73,227438300804759521]),(5,35,[3,11218159,46422697]),(5,30,[3,16892211777345623]),(21,1,[5,7,11,13,17,19,107,164580714999643067]),(5,30,[3,3,3,12749501,154043189]),(5,31,[3,37,179,1352626717763]),(7,1,[5,7,11,13,17,19,37,37,619,821,9433,2846111]),(5,32,[3,73,109,109,5404039943]),(5,30,[3,19003729911981533]),(11,1,[5,7,11,13,17,19,71,279033801182000399]),(5,33,[3,47,52886252521601]),(5,31,[3,151,7349,33941,267581]),(7,1,[5,5,7,11,13,17,19,4202632168281987029]),(5,31,[3,374389,28167855497]),(11,1,[5,7,11,13,17,19,26371,845163991976803]),(10,33,[3,127,315617,69763613]),(7,1,[5,7,11,13,17,19,23639801334914561833]),(5,33,[3,3,10711,92303471849]),(7,1,[5,7,11,13,13,17,19,19,29,3500459871456299]),(5,34,[3,21739,72356238979]),(7,1,[5,7,11,13,17,19,23,811,1425763904937149]),(10,31,[3,3,43,197,525201368521]),(7,1,[5,7,11,13,17,19,79,373,73681,100823,128861]),(7,31,[3,3,15259,60223,5135093]),(7,1,[5,7,11,11,11,13,17,19,247265324329869361]),(7,33,[3,56501,66438212707]),(11,1,[5,7,7,11,13,17,19,37,131,857,1091372245897]),(7,31,[3,3,3,3,2473,238518673793]),(7,1,[5,7,11,13,17,19,33658986744279938857]),(5,31,[3,16892211777345623]),(11,1,[5,7,11,11,13,17,19,19,571,937,45697,6986627]),(5,32,[3,37,179,1352626717763]),(11,1,[5,5,7,11,13,17,19,7573268694832502741]),(10,31,[3,19003729911981533]),(7,1,[5,5,7,11,13,17,19,43,101,9391,81071,2429363]),(5,32,[3,151,7349,33941,267581])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [3976394926633368174985216,4217602483256835331588096,4473442051975083475337216,4744801804328138918854656,5032621588731820576342016,5337901037224434971181056,5661698502272653717405696,6005137255844182979772416,6369409572507150729609216,6755778597180108099813376,7165585127008660698955776,7600250408650902796763136,8061278784545890433499136,8550276135209077661761536,9068937142600685559218176,9619058955424852476952576,10202549809247205348868096,10821437880949094739869696] 1517925041354314083167506089471868852362815666651135 12647179923613923665559974066223780521992910605910014 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_47 (k : ℕ) (lo : 12647179923613923665559974066223780521992910605910015≤k) (hi : k≤105375014618463822560513826692051241962591418524368894) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,89,101,103,107,127,137,139,149,157,163,179,181,191,193,199,211,233,239,241,263,269,277,283,313,331,337,353,359,367,373,419,421,431,479,487,491,577,619,683,787,821,823,827,839,853,857,881,887,953,983,997,1031,1091,1109,1151,1181,1229,1237,1249,1327,1399,1427,1999,2017,2467,2693,3011,3221,3329,3361,3517,3761,3779,3833,3919,4007,4057,4363,4463,4519,5119,5407,5743,5857,5867,6211,6269,6473,6791,6823,6949,7727,7927,9133,9689,14947,15413,16141,16477,16553,17483,18269,19447]
  let factors : List (ℕ × ℕ × List ℕ) := [(11,3,[3,3,3,5,19]),(2,2,[5,1151]),(3,1,[3,5,821]),(5,1,[41,331]),(2,1,[3,5407]),(2,1,[16553]),(6,1,[3,3,3,3,3,7,11]),(3,1,[3,11,577]),(10,7,[3,3,43]),(2,2,[7,2017]),(2,1,[7,41,103]),(5,1,[127,233]),(2,1,[5,6949]),(2,1,[79,479]),(2,1,[3,37,359]),(6,1,[3,15413]),(2,2,[3,3,3,857]),(6,2,[3,17,17,31]),(7,1,[3,5,11,337]),(7,1,[3,3,6211]),(3,7,[1031]),(3,7,[1181]),(6,1,[5,5,47,79]),(2,2,[13,3919]),(6,5,[5,37,37]),(2,1,[127,887]),(3,5,[43,233]),(5,2,[3,7,4463]),(7,3,[3,5,3329]),(3,1,[3,269,269]),(2,2,[3,37423]),(7,1,[225299]),(7,1,[5,5,5,7,277]),(2,2,[3,3,61,337]),(2,2,[3,179,367]),(10,3,[3,7,29,163]),(3,1,[3,3,11,4057]),(5,1,[3,7,17,23,53]),(5,1,[11,41,983]),(2,2,[3,92479]),(3,1,[3,7,32443]),(3,4,[43,1999]),(3,3,[421,491]),(3,4,[29,59,61]),(7,1,[5,7,11,31,89]),(2,1,[1653689]),(3,2,[5,5,7,13,373]),(2,2,[870367]),(7,3,[3,151169]),(3,2,[5,7,27143]),(11,5,[3,5,23,353]),(5,2,[3,7,7,23,313]),(2,2,[3,374893]),(2,2,[3,740053]),(2,2,[5,157,3761]),(2,2,[1109,4007]),(7,1,[5,7,399481]),(3,2,[5,23,31,2467]),(2,1,[17775053]),(11,1,[3,5,11,111211]),(2,2,[73,211,619]),(5,1,[11,11,185651]),(5,1,[27963671]),(2,1,[3,13,683,1229]),(11,1,[1237,33107]),(11,1,[11,787,7927]),(3,1,[3,7,3307379]),(2,1,[3,11,101,23021]),(19,1,[5,19,1109749]),(6,1,[5,11,2124431]),(2,1,[3,3011,16477]),(10,4,[3,3,7,11,137,1091]),(7,4,[3,107,484751]),(3,3,[181,3481469]),(3,4,[7,71,79,9689]),(10,1,[3,853,953,1327]),(5,4,[3,13,61,203789]),(3,1,[3,3361,449077]),(2,2,[3,3,5,7,7,11,23,6269]),(15,3,[5,5,7,43,320609]),(2,2,[157,36699631]),(3,1,[3,5119,788317]),(12,1,[3,19,127,487,6823]),(2,1,[3,283,35179421]),(2,2,[241,65473747]),(3,3,[5,5,7,179,239,1427]),(5,1,[3,31,71,139,75683]),(5,3,[3,43,139,1669937]),(2,2,[24631,4498717]),(5,1,[7,63116692109]),(2,1,[5,5,17,1657290097]),(2,2,[7,479,2693,49537]),(3,1,[3,3,3,3,19,2489681137]),(7,1,[5,11,17,73,3779,69491]),(10,4,[3,7,43,3517,803287]),(2,2,[41,239,269,353,38083]),(6,3,[11,11,14947,44927543]),(2,1,[3,3,3,823,18269,3394301]),(7,6,[3,17483,6086707313]),(3,4,[17,23,827,59183,92557]),(5,6,[3,3,59,3833,233687411]),(2,2,[3,3,111799,24212368339]),(11,1,[5,37,2755869972992299]),(5,1,[3221,79699,7757024497]),(2,2,[297673483,9056086783]),(7,3,[3,17,17,431,881,19300661801]),(5,30,[3,3,199,419,85467881801]),(5,38,[3,3,5857,5041167113]),(5,30,[3,37,650042961693929]),(5,31,[3,61,1362607,153457987]),(10,31,[3,56477,239549122777]),(5,30,[3,3,6791,1408696582451]),(5,30,[3,30440279194800193]),(5,30,[3,239,3800021,35550107]),(5,31,[3,47,191,450599,4233013]),(10,31,[3,71,157,7727,210852311]),(5,33,[3,1249,434167,8880637]),(5,31,[3,20431469559010369]),(14,1,[5,7,7,11,13,17,19,794137,7663238539687]),(7,31,[3,3,199,419,85467881801]),(5,31,[3,43,3628057,138909919]),(7,1,[5,7,11,13,17,19,149,239,9133,138926288023]),(5,39,[3,3,5857,5041167113]),(5,35,[3,263,2017,20521,131969]),(7,1,[5,7,11,13,17,19,47,1019671890007150631]),(5,31,[3,37,650042961693929]),(10,33,[3,43,141742434305477]),(7,1,[5,7,11,13,17,19,50831680041876928297]),(5,32,[3,61,1362607,153457987]),(5,31,[3,3,19447,443231593709]),(7,1,[5,5,7,11,13,17,19,10783027580183500757]),(5,32,[3,56477,239549122777]),(19,32,[3,241,839,5743,11809541]),(11,1,[5,7,11,13,17,19,353,4519,35848411813391]),(5,31,[3,3,6791,1408696582451]),(10,32,[3,41,4363,59123,1375313]),(7,1,[5,7,7,11,11,13,17,19,6473,886667,137248079]),(5,31,[3,30440279194800193]),(11,1,[5,5,7,11,11,13,17,19,41,41,107509,6472381459]),(10,31,[3,239,3800021,35550107]),(11,1,[5,7,11,13,17,19,38137829,1789202927093]),(5,32,[3,47,191,450599,4233013]),(19,1,[5,7,11,13,17,19,81906719,883633689527]),(5,32,[3,71,157,7727,210852311]),(14,1,[5,7,11,13,17,19,5867,219041,59734656859]),(5,34,[3,1249,434167,8880637]),(14,1,[5,7,11,13,13,13,17,17,19,28340564410325873]),(7,32,[3,20431469559010369]),(11,1,[5,7,11,13,17,19,67,55927343,23047368269]),(7,32,[3,43,3628057,138909919]),(11,1,[5,7,11,13,17,19,23,3982618948479208127]),(7,36,[3,263,2017,20521,131969]),(7,1,[5,7,11,13,17,19,997,97449068445546997]),(5,34,[3,43,141742434305477]),(7,1,[5,7,11,13,17,19,103,127,193,40817917155793]),(7,32,[3,3,19447,443231593709]),(7,1,[5,7,11,11,13,17,19,53,3897121,48107512879]),(5,33,[3,241,839,5743,11809541]),(11,1,[5,7,11,13,17,19,367,1399,16141,13989022741]),(10,33,[3,41,4363,59123,1375313])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [11477866498712605311369216,12174115359035673444089856,12912598834300626902450176,13695876071816478406475776,14526670109615291730231296,15407859884704034640101376,16342500452847005273686016,17333836032438866695684096,18385308471001516422987776,19500562937829188138172416,20683461808869734996770816,21938123391292269244973056,23268890997122943686803456,24680385870350241010548736,26177502151290444113248256,27765432851504941190086656,29449688369868315375435776,31236110189980297059106816] 12647179923613923665559974066223780521992910605910015 105375014618463822560513826692051241962591418524368894 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_48 (k : ℕ) (lo : 105375014618463822560513826692051241962591418524368895≤k) (hi : k≤877975684353233770983053812712178361431842508679151614) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,73,79,89,97,101,103,109,113,127,131,139,157,173,179,181,193,229,233,239,241,257,269,277,283,307,317,337,347,353,359,379,401,409,433,443,449,463,467,479,509,521,541,547,563,587,631,677,691,761,787,859,877,929,947,1103,1367,1439,1459,1493,1511,1667,1697,1721,1993,1999,2129,2207,2371,2383,2531,2543,2551,2789,2803,2851,2857,3221,3229,3323,3517,3539,3701,3761,3919,3967,4091,4127,4273,4373,4517,4993,5099,5669,6197,6427,7649,7877,8731,9421,9739,9923,10313,10391,10433,12281,15137,15601,16619,17011]
  let factors : List (ℕ × ℕ × List ℕ) := [(3,3,[2531]),(11,3,[3,5,5,5,7]),(3,3,[5,547]),(11,5,[3,233]),(3,1,[3,3761]),(3,1,[3,5,5,173]),(3,1,[3,3,1459]),(2,1,[3,11,433]),(2,2,[3,5,7,73]),(3,1,[3,3,2207]),(2,2,[3,3323]),(2,1,[20249]),(3,3,[29,193]),(2,1,[3,8731]),(2,1,[7,5099]),(2,2,[3,3,5,7,67]),(6,2,[3,3,3,3,3,89]),(2,2,[22369]),(2,2,[3,10433]),(6,2,[3,5,5,433]),(5,1,[7,10313]),(2,1,[5,15601]),(2,1,[29,2857]),(2,1,[11,11,13,53]),(2,2,[19,23,101]),(6,1,[3,73,409]),(13,3,[3,3,3,7,131]),(5,4,[3,4127]),(2,1,[3,39727]),(3,1,[3,39877]),(5,1,[144383]),(11,1,[166739]),(2,2,[3,13,2371]),(3,1,[3,3,21001]),(3,5,[7,1697]),(2,2,[179,677]),(7,1,[5,5,10391]),(14,1,[5,17,19,173]),(3,3,[89477]),(2,1,[5,5,29,541]),(2,2,[353,563]),(7,3,[3,103,359]),(2,1,[484733]),(5,1,[241,2543]),(5,1,[3,7,7,17,317]),(2,1,[7,23,4993]),(2,2,[3,17,9739]),(2,2,[3,59,3221]),(2,1,[3,3,3,3,3,3,5,337]),(2,2,[173,3701]),(3,1,[3,3,5,5,7,859]),(13,3,[3,5,11,2207]),(7,1,[7,13,37,509]),(2,1,[5,7,52387]),(5,2,[3,3,157,691]),(2,1,[5,19,28579]),(2,2,[3,29,17011]),(2,1,[1667,1999]),(2,1,[29,129901]),(7,3,[3,333479]),(2,2,[3,13,13,6427]),(2,1,[3,5,5,173,787]),(2,2,[3,59,103,307]),(3,6,[97,3919]),(3,1,[3,23,479,929]),(3,4,[89,44777]),(7,2,[3,5,5,5,31,31,53]),(11,4,[3,7,239263]),(3,1,[3,3,6664667]),(2,2,[7,11,103,4517]),(5,8,[11,11,47,401]),(5,1,[229,1607747]),(6,1,[5,80392369]),(3,1,[3,3,3,3,11,79,6197]),(6,1,[3,47,1721,2551]),(2,2,[7,7,8003497]),(5,1,[803923691]),(2,2,[379,1986757]),(2,2,[7,7,23,715817]),(2,1,[3011923613]),(5,4,[3,3,11,3905533]),(5,1,[3,3,23,61,449,761]),(2,2,[3,3,13,4273,15137]),(7,3,[3,19,409,198097]),(3,1,[3,6186364273]),(10,1,[5,5,347,2705851]),(6,1,[3,3,11,13,877,21881]),(2,2,[7,11,17,101,443,631]),(2,2,[3,173,283,378019]),(7,1,[7,443,61408759]),(2,1,[17,19,19,19,2456731]),(3,1,[3,3,7,23,61,3427607]),(6,5,[5,7,19,43,43,25951]),(3,1,[3,222089186653]),(5,4,[3,3,3,127,3539,9421]),(6,1,[3,3,5,13,19,257,369877]),(6,2,[3,3,5,5,6023847227]),(5,1,[239,30270427669]),(2,2,[5,5,40499,3667091]),(2,2,[3,31,181,1993,179143]),(2,2,[7,859,7649,156011]),(5,1,[14469264425783]),(2,1,[109,1021086730721]),(6,1,[3,5,5,7,37,8629014007]),(2,1,[7,17,587,26263,165707]),(5,11,[3,7,16619,2561093]),(2,1,[3,521,605925510247]),(2,1,[19,41,2113147987471]),(3,1,[3,23,238363,1568685413]),(7,1,[3,5,73,24039678556669]),(5,1,[7,2803,4091,1238056423]),(10,3,[3,29,198756367329238307]),(19,3,[3,157,1439,28701928399229]),(7,3,[3,5,19,43,1894123145032123]),(7,3,[3,1493,125197,49394125639]),(10,31,[3,29,2129,84421,5919829]),(10,34,[3,3,3,3,3,1367,36945882889]),(10,31,[3,67,887449,583804673]),(5,32,[3,3,173,1584367,22387669]),(5,32,[3,30661,519551,1225727]),(5,31,[3,2789,14851351840901]),(5,32,[3,23,1667,572924409587]),(5,31,[3,139,335237194171951]),(5,31,[3,3,3,3,1830541098817537]),(10,32,[3,29,7534259,119964007]),(5,31,[3,113,269,1829216180017]),(5,31,[3,97,607995334635347]),(7,1,[5,7,11,13,17,19,2383,51600485431650823]),(17,32,[3,29,2129,84421,5919829]),(11,32,[3,61,463,380129,2913241]),(14,1,[5,7,11,11,13,17,19,19,37,89,3517,9923,5430011]),(10,35,[3,3,3,3,3,1367,36945882889]),(5,31,[3,3,3,53,86509,1607847383]),(21,1,[5,7,11,13,17,19,138334431661149861673]),(5,32,[3,67,887449,583804673]),(5,31,[3,1511,2280469,20422651]),(11,1,[5,7,11,13,17,19,176549,13033957,63762449]),(5,33,[3,3,173,1584367,22387669]),(5,32,[3,794957,46946514851]),(7,1,[5,7,11,13,17,19,155626218473736320809]),(15,33,[3,30661,519551,1225727]),(13,32,[3,29,131,3229,3226903037]),(14,1,[5,7,11,13,17,19,5669,784451,37118185639]),(5,32,[3,2789,14851351840901]),(5,34,[3,7877,1332535119919]),(21,1,[5,7,11,13,17,19,47,2851,4373,12281,24329153]),(5,33,[3,23,1667,572924409587]),(7,1,[5,7,11,13,17,19,185699833138949338921]),(5,32,[3,139,335237194171951]),(14,1,[5,7,11,13,17,19,109,22567,558791,143297309]),(5,32,[3,3,3,3,1830541098817537]),(7,1,[5,5,5,7,11,13,17,19,288767,28938528851567]),(5,33,[3,29,7534259,119964007]),(21,1,[5,7,11,13,17,19,221584957128130639657]),(5,32,[3,113,269,1829216180017]),(7,1,[5,7,11,13,17,19,71387,3292284564479819]),(5,32,[3,97,607995334635347]),(7,1,[5,5,7,11,13,17,19,947,52646896039105111]),(5,33,[3,61,463,380129,2913241]),(21,1,[5,7,11,13,17,19,3967,76399501,872401267]),(5,32,[3,3,3,53,86509,1607847383]),(7,1,[5,7,11,13,17,19,736348127,380857123319]),(5,32,[3,1511,2280469,20422651]),(7,1,[5,7,11,13,17,19,277,198073,5421462504301]),(5,33,[3,794957,46946514851]),(7,1,[5,5,7,11,13,17,19,257,1103,222596907297179]),(5,33,[3,29,131,3229,3226903037]),(7,1,[5,5,7,11,13,17,19,467,969467,147827113589]),(5,35,[3,7877,1332535119919])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [33130896165959694869856256,35140621616215786442981376,37272252873314963938082816,39533192649823006727602176,41931279862986540377440256,44474837626881770348609536,47172688361053898162569216,50034189291653764256628736,53069270535485273382322176,56288460727757271933648896,59702927577948819004850176,63324511900700242677334016,67165787052270199867703296,71240074323850743257235456,75561509106090371151036416,80145078888085923074932736,85006692747750427586461696,90163210262014099084804096] 105375014618463822560513826692051241962591418524368895 877975684353233770983053812712178361431842508679151614 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_49 (k : ℕ) (lo : 877975684353233770983053812712178361431842508679151615≤k) (hi : k≤7315220356618431876746424535945111860343510614530850814) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,73,79,83,89,97,101,103,107,109,113,127,131,157,163,179,191,199,211,233,239,271,277,281,283,293,337,373,433,443,461,499,503,563,601,607,619,647,653,673,677,683,701,773,859,863,881,919,1069,1091,1093,1123,1217,1289,1291,1297,1433,1439,1459,1487,1571,1627,1699,1709,1747,1783,1789,2039,2113,2129,2621,2633,2797,2861,2897,2969,3001,3163,3221,3371,3529,3803,3917,4019,5099,5563,5839,6199,6271,6473,6857,6959,7703,7883,7963,8747,9109,10639,10723,10733,10781,12011,12409,12911,13259,14177,14197,14411,17327,17401,17669,17789]
  let factors : List (ℕ × ℕ × List ℕ) := [(12,1,[3,5,701]),(2,1,[10733]),(2,2,[5,1091]),(2,2,[3,3,13,61]),(5,1,[3,3,1627]),(2,1,[3,3,1789]),(17,1,[19,881]),(2,1,[17669]),(2,1,[11,1699]),(3,10,[37]),(5,1,[3,7,7,7,19]),(5,10,[3,13]),(2,2,[10639]),(11,4,[3,3,3,3,5,7]),(3,1,[3,3,5,619]),(2,1,[29,1069]),(2,1,[7,5099]),(11,1,[37379]),(5,3,[3,3,1093]),(7,3,[3,37,101]),(2,2,[5,11,433]),(6,1,[3,3,5,19,61]),(2,2,[3,3,3001]),(6,1,[11,6199]),(3,3,[21821]),(31,3,[3,5,1459]),(2,1,[3,29287]),(2,1,[95261]),(22,1,[5,11,2129]),(3,3,[33479]),(7,1,[136379]),(2,2,[13,13,17,29]),(7,1,[5,5,6959]),(5,1,[13,14411]),(5,5,[3,3,1439]),(10,2,[3,5,7703]),(3,3,[7,19,443]),(3,3,[11,47,131]),(6,1,[5,7,17,503]),(5,1,[233,1291]),(3,5,[13,1487]),(3,4,[39937]),(2,1,[3,67,1709]),(2,2,[175723]),(2,1,[7,37,2039]),(5,6,[3,7963]),(3,1,[3,11,73,337]),(2,1,[5,175081]),(5,1,[3,3,11,9109]),(2,2,[11,19,43,59]),(3,3,[272759]),(2,2,[687019]),(6,2,[3,163,1433]),(5,2,[3,3,11,37,211]),(7,1,[433,3803]),(2,2,[7,199,601]),(2,1,[3,653,859]),(2,1,[5,13,28549]),(6,2,[3,37,8747]),(5,1,[3711371]),(6,3,[5,17,12911]),(2,2,[73,107,293]),(17,3,[3,11,11,3917]),(3,1,[3,3,3,211,1217]),(2,2,[89,42557]),(5,1,[109,71387]),(3,2,[277,14197]),(5,4,[3,239,1571]),(2,1,[31,31,10781]),(29,1,[3,9154493]),(3,3,[8779481]),(2,2,[2621,7883]),(10,3,[3,13,23,43,277]),(3,1,[3,5,19,234191]),(2,2,[3,647,17327]),(7,1,[7,1123,13259]),(2,2,[3,11,19,104311]),(2,2,[461,333269]),(2,2,[3,919,74759]),(6,2,[3,70235849]),(2,2,[3,113,638993]),(6,1,[3,31,127,127,563]),(3,5,[23,863,2861]),(11,1,[5,11,43,598571]),(2,2,[499,1623667]),(5,1,[2831240831]),(2,2,[677,3293399]),(7,1,[3,7,107,2120933]),(3,1,[3,3,3,17,1783,10723]),(2,1,[17,23,79,541817]),(2,1,[3,5662481663]),(5,1,[17,1688996623]),(17,2,[3,3,5,13,1289,21467]),(7,1,[5,19,21031,39103]),(3,1,[3,33472370627]),(7,1,[7,11,11,19,59,79,3163]),(3,3,[5,1747,18022513]),(2,1,[5,11,61,208457999]),(2,1,[157,8918524493]),(6,1,[3,1297,5563,347951]),(5,3,[3,2800416690803]),(3,3,[267833,54926959]),(2,1,[7,23,373,2897,471353]),(2,1,[3,3529,33974889979]),(2,2,[719384320415347]),(3,1,[3,3,164005900941947]),(2,1,[11,19,601,6473,2748077]),(2,1,[5,11,29,109,37889,601607]),(5,1,[7925801749393331]),(5,3,[3,11,19,101,17789,2182073]),(3,3,[4468741757598779]),(2,1,[5,29,31,3221,6857,190523]),(2,2,[11,13,47,12409,133488871]),(5,2,[3,11,13,374687,82645373]),(2,1,[3,11,13,83,702893,1803583]),(3,1,[3,13,23,23,41,64750053421]),(11,1,[3,3,11,13,773,57425885183]),(6,1,[3,5,7,7422743,842830189]),(6,2,[3,3,7,11,2969,6271,134526829]),(7,1,[103,157,62003,17551342063]),(14,3,[3,17,1313783495973569671]),(11,3,[3,3,3,5,5,4019,3091573,11374969]),(10,32,[3,44532362052025277]),(5,36,[3,2952106216955047]),(5,33,[3,37,3371,200834223763]),(10,32,[3,53137908034498717]),(10,36,[3,2797,1259413208441]),(10,35,[3,127,3883669,15150293]),(5,34,[3,15851603498786663]),(5,34,[3,53,174569,1817215649]),(5,32,[3,3,89,191,1398753173291]),(5,33,[3,37829619874522691]),(10,33,[3,3,199,67210000579273]),(5,33,[3,89689,474509926199]),(7,1,[5,5,7,7,11,13,17,19,101,683,45361,3240839333]),(10,33,[3,44532362052025277]),(5,32,[3,90279829794191467]),(14,1,[5,5,7,11,13,17,19,2633,35339,462181,1750811]),(5,37,[3,2952106216955047]),(5,32,[3,3,3348773,9531472903]),(19,1,[5,5,7,11,13,17,19,31,131,19665260886385753]),(5,34,[3,37,3371,200834223763]),(5,32,[3,3,97,2113,108037,1528897]),(19,1,[5,7,11,13,17,19,61,6943031404550206813]),(5,33,[3,53137908034498717]),(5,33,[3,3,20721083,866474509]),(7,1,[5,7,11,13,17,19,29,41,281,15730277,85473337]),(5,37,[3,2797,1259413208441]),(5,32,[3,114260398600385467]),(11,1,[5,7,11,13,13,17,19,47,271,2877537281661389]),(15,36,[3,127,3883669,15150293]),(5,32,[3,3,283,647,14177,15562367]),(7,1,[5,5,7,11,13,17,17,19,17401,414433,824442253]),(5,35,[3,15851603498786663]),(7,1,[5,7,11,13,17,19,536023666357216425769]),(5,35,[3,53,174569,1817215649]),(7,1,[5,5,7,11,13,13,17,19,53,1056203,156251286671]),(5,33,[3,3,89,191,1398753173291]),(14,1,[5,7,11,13,13,17,19,19,673,13866499,261611989]),(5,34,[3,37829619874522691]),(7,1,[5,7,11,13,17,19,5839,109540384874549383]),(5,34,[3,3,199,67210000579273]),(7,1,[5,7,11,13,17,19,179,32203,117690017678777]),(7,34,[3,89689,474509926199]),(14,1,[5,7,11,13,17,19,607,78697,15063239295967]),(7,33,[3,90279829794191467]),(21,1,[5,7,11,13,17,19,763205503708637116201]),(5,33,[3,3,3348773,9531472903]),(14,1,[5,7,11,13,17,19,23,35195724246610856639]),(14,33,[3,3,97,2113,108037,1528897]),(7,1,[5,7,7,11,13,17,19,47,73,35749934060790233]),(5,34,[3,3,20721083,866474509]),(7,1,[5,7,11,13,17,19,43,55711,618593,614548037]),(5,33,[3,114260398600385467]),(7,1,[5,5,5,7,11,11,13,17,19,31,12011,2802949,3365563]),(5,33,[3,3,283,647,14177,15562367])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [95632519313540007640170496,101433597249121660537143296,107586569508980442578026496,114112788593013814634479616,121034884024843677032513536,128376879218114316789088256,136164237232895786531946496,144423983231345238690758656,153184766530055483525431296,162476980181186581454913536,172332858407914798502117376,182786595883530276470521856,193874458227249380763631616,205634910896323065267879936,218108753719583438354251776,231339267932417382558990336,245372337608289876879343616,260256646064113098367696896] 877975684353233770983053812712178361431842508679151615 7315220356618431876746424535945111860343510614530850814 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_50 (k : ℕ) (lo : 7315220356618431876746424535945111860343510614530850815≤k) (hi : k≤60949825924076889551964561035525037401645902348236619774) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,109,127,131,137,139,149,157,167,191,193,197,199,223,229,233,241,251,263,269,277,307,313,317,331,347,353,383,389,397,401,449,457,491,503,521,617,631,653,751,761,769,857,863,881,883,887,911,997,1033,1087,1091,1303,1451,1459,1493,1597,1619,1663,1669,1693,1861,1871,1877,1999,2053,2137,2179,2207,2411,2687,2819,3191,3221,3257,3539,3793,3853,3931,3989,4127,4583,4831,4861,4999,5521,5779,6661,7151,7793,7873,8297,9137,9341,10037,10093,10487,11087,11423,12487,13033,14737,17027,18059]
  let factors : List (ℕ × ℕ × List ℕ) := [(6,3,[5,5,101]),(3,4,[1303]),(3,3,[47,61]),(3,8,[7,13]),(5,1,[19,617]),(3,3,[11,331]),(5,1,[3,19,263]),(21,1,[3,5,17,59]),(2,1,[11,1663]),(3,1,[3,79,79]),(11,1,[5,5,863]),(2,2,[3,3989]),(3,1,[3,5,1597]),(2,1,[17,29,53]),(13,2,[3,3,7,223]),(2,1,[37,857]),(3,3,[11,17,47]),(3,3,[7,11,127]),(3,1,[3,5,5,17,37]),(3,1,[3,19,887]),(11,1,[63419]),(2,1,[89,997]),(11,4,[3,5,761]),(6,2,[3,5,13,263]),(5,2,[3,7,7,397]),(7,3,[3,5,2053]),(17,1,[126839]),(5,3,[3,13,911]),(7,5,[3,11,383]),(2,2,[7,41,401]),(13,1,[253679]),(2,1,[3,5,18059]),(2,2,[5,7,4127]),(2,2,[5,13,2411]),(3,3,[7,11423]),(11,3,[3,3,3,5,751]),(5,1,[307,1493]),(3,3,[5,13,1861]),(3,1,[3,182641]),(2,2,[3,3,19,1669]),(2,2,[3,29,4999]),(7,4,[3,36587]),(3,1,[3,83,3931]),(3,3,[13,23447]),(2,1,[7,177467]),(2,1,[7,127,1877]),(2,1,[13,29,29,197]),(2,2,[1095847]),(7,4,[3,5,5,3793]),(2,1,[2438489]),(3,6,[251,353]),(3,3,[7,277,491]),(5,1,[41,94351]),(5,4,[3,11,17027]),(3,3,[47,30091]),(5,1,[37,199,881]),(3,6,[5,5,5,13,137]),(3,1,[3,241,13033]),(2,1,[5,233,9137]),(7,1,[1087,10037]),(11,3,[3,3,5,7,10093]),(11,1,[3,7,626861]),(6,1,[5,5,7,7,20201]),(19,1,[73,97,3539]),(10,1,[3,5,3337307]),(3,1,[3,73,246361]),(2,2,[43,269,3257]),(2,1,[7,389,37447]),(13,1,[5,19,449,3221]),(2,1,[3,3,317,56197]),(6,2,[3,19,53,127,347]),(2,2,[23,7736783]),(5,1,[7,7,17,541771]),(7,2,[3,89,127,6661]),(3,1,[3,150694877]),(3,3,[71,1756177]),(3,1,[3,4861,47911]),(5,6,[3,7616393]),(2,2,[23,21820439]),(3,2,[223,1619,1871]),(2,2,[3,3,100119211]),(2,1,[3,29,103,167,2179]),(7,1,[3,3,3,3,3,3,5,193,9341]),(6,1,[3,3,902590487]),(5,1,[11,61,2137,7873]),(3,1,[3,5,37,21289211]),(2,1,[5,11,67,79,43151]),(2,1,[3,5,17,17,167,78233]),(5,4,[3,3,904169263]),(5,3,[3,31,203936363]),(2,2,[3,5,17,17,26328163]),(19,8,[3,61,1693,10487]),(2,2,[7,29129,4307603]),(7,4,[3,3,3,5,1999,1141597]),(13,4,[3,5,22937,916703]),(22,3,[3,5,7,17,457,811081]),(2,1,[13,14737,14248001]),(2,2,[5,11,29,997508537]),(3,1,[3,3,3,151728654073]),(2,1,[5,5,11,3191,5670593]),(2,2,[3,7,284233,507359]),(3,1,[3,61,29983,2484539]),(5,3,[3,3,456530346421]),(3,4,[11,229,2702000909]),(7,1,[5,27264779418343]),(5,1,[11,109,139,20849,52259]),(7,3,[3,11,3513332698037]),(7,1,[79,6364104466061]),(2,1,[3,47,4929233190481]),(13,1,[61,2687,47869,1739653]),(3,1,[3,11,4831,130200373873]),(7,1,[5,404449,16246628767]),(6,1,[5,5,389,5293082162761]),(3,3,[5,353,967721,8990257]),(13,1,[3,3,5,149,8297,1397372227]),(2,2,[41513868407910559]),(2,1,[139,397,205141,49492451]),(2,1,[3,5,65709327581843831]),(5,4,[3,521,108901444636337]),(7,3,[3,5,13,61,12973607,2007480389]),(11,33,[3,769,7793,23297,460349]),(10,33,[3,12487,5459292559163]),(5,33,[3,47,127,12113486334349]),(5,34,[3,3853,9952174244651]),(5,34,[3,3,3,71,2819,22578614543]),(5,33,[3,47,2207,831762394369]),(5,34,[3,23,653,11087,274783511]),(11,35,[3,89,272647794183431]),(5,33,[3,102950448065701451]),(5,35,[3,27298858188296999]),(5,33,[3,3,3,3,1459,5521,532529797]),(5,33,[3,122844854179473641]),(11,1,[5,5,7,7,7,11,13,17,19,577781,639689,11314217]),(5,34,[3,769,7793,23297,460349]),(5,33,[3,5779,70313,320660083]),(7,1,[5,7,11,13,13,17,19,1451,4383389,13142506771]),(5,34,[3,12487,5459292559163]),(5,33,[3,149,927519832281769]),(11,1,[5,7,11,11,13,17,19,631,166055473631642237]),(5,34,[3,47,127,12113486334349]),(5,34,[3,50119319,1462347457]),(7,1,[5,7,11,13,17,19,1091,1120538370670966307]),(7,35,[3,3853,9952174244651]),(5,33,[3,155475504697088791]),(14,1,[5,5,7,11,13,17,19,503,4551601,113272778371]),(5,35,[3,3,3,71,2819,22578614543]),(5,35,[3,41,1005528505637639]),(11,1,[5,5,7,11,13,17,19,101,2723407327465515697]),(5,34,[3,47,2207,831762394369]),(11,33,[3,3,37,43,47,863,903471397]),(11,1,[5,7,7,11,13,17,19,25434361,8193347319943]),(5,35,[3,23,653,11087,274783511]),(11,1,[5,7,11,13,17,17,19,191,313,233437,6521690347]),(5,36,[3,89,272647794183431]),(11,1,[5,5,7,11,11,13,17,19,67,18845719,23631024211]),(5,34,[3,102950448065701451]),(7,1,[5,7,11,13,17,19,883,1971279827455314931]),(5,36,[3,27298858188296999]),(11,1,[5,7,11,13,17,19,47,101,107906119,3604291597]),(7,34,[3,3,3,3,1459,5521,532529797]),(7,1,[5,7,11,13,17,19,197,7151,1390043759715643]),(5,34,[3,122844854179473641]),(7,1,[5,7,11,13,17,19,37,103,157,4876979,711784037]),(5,34,[3,5779,70313,320660083]),(7,1,[5,7,11,13,17,19,223,1957639,5046340010641]),(5,34,[3,149,927519832281769]),(7,1,[5,7,11,13,17,19,19,37,101119,32870184942313]),(7,35,[3,50119319,1462347457]),(7,1,[5,7,11,13,17,19,2478371936434181584681]),(17,34,[3,155475504697088791]),(11,1,[5,7,7,7,11,11,13,13,17,19,1033,363170282123903]),(5,36,[3,41,1005528505637639]),(11,1,[5,7,11,13,13,17,19,59,131,241,4583,25123806731]),(10,34,[3,3,37,43,47,863,903471397])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [276043853272194970913079296,292788720232253660673867776,310549328022387530531864576,329387289944924736377061376,349367965154669199932522496,370560679004797608757559296,393038949252908836859150336,416880755926597560545837056,442168807550734191344746496,468990812547509682559778816,497439854425056619303796736,527614631182728202589044736,559619816134013938602868736,593566434560198833891966976,629572272240752167575617536,667762208003090743753179136,708268775693143425591279616,751232480686071625166094336] 7315220356618431876746424535945111860343510614530850815 60949825924076889551964561035525037401645902348236619774 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_51 (k : ℕ) (lo : 60949825924076889551964561035525037401645902348236619775≤k) (hi : k≤507829176091871375174893267215297682742777965088788709374) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,103,107,109,113,127,131,137,139,151,163,173,181,197,199,227,229,233,251,263,271,277,283,307,317,331,353,359,373,383,401,431,449,461,467,503,541,571,577,619,647,661,683,757,761,769,773,827,857,907,911,929,967,1021,1031,1069,1091,1109,1151,1163,1187,1201,1231,1277,1283,1291,1307,1319,1439,1523,1559,1571,1583,1597,1733,1783,1889,2153,2251,2269,2333,2609,2617,2707,2797,2851,2971,3037,3061,3181,3229,3571,3733,4127,4507,5297,5351,5477,5557,6173,6343,6763,8147,8297,9199,9769,10513,11497,11953,12157,12253,12421,12791,13219,13829,15907,15923,16811,17011,18257]
  let factors : List (ℕ × ℕ × List ℕ) := [(5,1,[11,23,41]),(3,3,[2609]),(2,2,[3,1783]),(2,2,[5,1091]),(6,1,[3,5,11,67]),(6,1,[3,7,7,7,11]),(5,3,[3,1069]),(3,1,[3,3,1571]),(3,1,[3,3,23,73]),(2,2,[5,1559]),(5,1,[15923]),(2,1,[3,7,761]),(5,4,[3,769]),(2,2,[3,3571]),(3,6,[7,97]),(2,1,[19,31,41]),(7,10,[3,19]),(17,3,[3,3,929]),(7,3,[3,2797]),(13,1,[5,5,1583]),(2,2,[7,3181]),(23,3,[3,5,7,127]),(6,2,[3,3,5,5,7,17]),(2,1,[5,12157]),(2,2,[29,1283]),(5,1,[79151]),(14,2,[3,11,1439]),(2,2,[3,3,5351]),(2,2,[23,31,71]),(5,4,[3,5297]),(2,1,[148829]),(19,4,[3,3,5,461]),(3,4,[25657]),(17,3,[3,7,11,271]),(11,1,[3,3,5,53,109]),(10,2,[3,3,5,23,137]),(7,1,[297659]),(3,9,[5,283]),(7,4,[3,3,3,11,163]),(2,1,[3,3,3,3,53,113]),(2,2,[317,1031]),(5,1,[43,21821]),(5,1,[107,10513]),(6,2,[3,3,103,619]),(21,6,[3,11,1889]),(7,2,[3,500809]),(7,4,[3,13,13829]),(2,2,[2295253]),(5,1,[3,3,79,6763]),(3,1,[3,3,3,83,2269]),(6,3,[13,13,23,373]),(2,2,[3,127,8147]),(19,3,[3,5,107101]),(3,5,[5,53,1733]),(3,3,[1876607]),(7,3,[3,5,13,43,233]),(3,4,[7,189949]),(2,2,[7,11,67,1307]),(2,1,[14695841]),(2,2,[7,43,31963]),(11,1,[3,3,5,7,7,9199]),(6,2,[3,29,121571]),(11,1,[3,3,5,11,42853]),(2,1,[26971253]),(2,2,[103,197,773]),(2,1,[31,383,3061]),(5,1,[31,79,18257]),(5,1,[7,11,17,48299]),(6,2,[3,1319,12791]),(3,1,[3,3,13,43,28279]),(3,3,[5,31,254257]),(5,2,[3,29391683]),(2,2,[23,31,158303]),(5,1,[7,38483453]),(2,1,[315278681]),(2,1,[5,7,10169659]),(7,1,[5,7,12852121]),(6,3,[41,1021,2851]),(3,3,[6173,30223]),(2,2,[3,3,277,331921]),(2,1,[5,11,11,307,13219]),(3,1,[3,47,647,36913]),(5,1,[97,3037,20747]),(5,1,[683,967,17011]),(2,1,[7,431,3989569]),(10,1,[3,3,3,3,11,17,571,2617]),(21,5,[3,5,5,113,151,1109]),(3,1,[3,3,227,15629641]),(2,2,[3,13,451480157]),(5,1,[17,271,661,11953]),(2,1,[3,7,16811,519931]),(2,2,[89,1492532633]),(3,1,[3,5,11,761,6009709]),(2,2,[3,3,70430904493]),(3,5,[103,331,503,9769]),(3,1,[3,13,199,757,970219]),(3,3,[29,1163,53942507]),(6,1,[3,5,11,45268536259]),(5,1,[827,1201,12416029]),(2,2,[5,857,22639,67129]),(2,1,[1597,12253,724481]),(2,1,[14554551468713]),(2,1,[26048231007341]),(5,1,[3,3,11400222663727]),(2,2,[3,3,683,1277,9181013]),(5,1,[13,37,907,954765689]),(3,5,[5,7,1509218221171]),(5,1,[3,173,467,4910461931]),(5,3,[3,83,567181,2249783]),(2,2,[3,47,106681,202455949]),(3,1,[3,2541860070072217]),(3,1,[3,19,2971,531341617349]),(7,3,[3,3,5,13,37,41,45414880801]),(2,2,[11,61,577,1523,6343,58369]),(3,1,[3,5,5,5,5,9616987,89422787]),(3,3,[873243159417489389]),(5,2,[3,23,541,833065525685927]),(7,1,[7,1151,15251160420433303]),(10,3,[3,13,2153,15012857,630557363]),(5,33,[3,3,43457,66889,21274289]),(5,33,[3,401,11598809,42306709]),(10,35,[3,181,288273488741389]),(5,33,[3,3,31,2380326779204527]),(5,33,[3,4507,52096462014683]),(10,33,[3,3,5557,14938616965471]),(10,33,[3,43,8629297,711876131]),(5,33,[3,23,12181386545731717]),(10,36,[3,97,127,911,3309916213]),(10,35,[3,2707,29109102937427]),(5,34,[3,31181,5360845505633]),(5,39,[3,3,3,3,205204007947087]),(19,1,[5,7,11,13,13,17,19,967,8297,28353347823443]),(5,34,[3,3,43457,66889,21274289]),(5,34,[3,9769,21397,899648471]),(7,1,[5,7,11,13,17,19,449,6985945275339915113]),(5,34,[3,401,11598809,42306709]),(5,35,[3,59,1690324407711521]),(14,1,[5,7,7,11,13,17,19,19,139,179962217746402207]),(5,36,[3,181,288273488741389]),(11,34,[3,1291,2251,72799196663]),(7,1,[5,7,11,13,17,19,251,359,72686507,538768343]),(5,34,[3,3,31,2380326779204527]),(5,35,[3,131,2333,367103521723]),(7,1,[5,7,11,13,17,19,19,19,410513,595319,42424471]),(7,34,[3,4507,52096462014683]),(5,34,[3,3,37,89069,24073059347]),(14,1,[5,7,11,13,17,19,1231,3224916675310383751]),(7,34,[3,3,5557,14938616965471]),(5,35,[3,467,22111,12223675967]),(11,1,[5,5,7,7,11,13,17,19,4127,11497,2535512561749]),(7,34,[3,43,8629297,711876131]),(11,1,[5,7,11,13,17,19,5477,31847,202493,126446783]),(5,34,[3,23,12181386545731717]),(23,1,[5,7,11,13,17,19,31,12421,192637,63862713127]),(7,37,[3,97,127,911,3309916213]),(7,1,[5,7,11,13,17,19,263,774577,24663870471167]),(5,36,[3,2707,29109102937427]),(19,1,[5,7,11,11,11,13,17,19,79,173,3229,15907,62739773]),(5,35,[3,31181,5360845505633]),(14,1,[5,7,11,13,17,19,23,245757199014862244543]),(5,40,[3,3,3,3,205204007947087]),(14,1,[5,7,11,13,17,19,353,1187,40567591,352700197]),(5,35,[3,9769,21397,899648471]),(7,1,[5,7,11,13,17,19,6358967026697264903977]),(15,36,[3,59,1690324407711521]),(7,1,[5,7,11,11,13,17,19,20873,1307309,22470204143]),(5,35,[3,1291,2251,72799196663]),(7,1,[5,7,11,13,17,19,3733,284543299,6734924503]),(7,36,[3,131,2333,367103521723]),(7,1,[5,7,11,13,17,19,61,124390012033319875933]),(5,35,[3,3,37,89069,24073059347]),(19,1,[5,7,11,13,17,19,109,229,322425671139547561]),(5,36,[3,467,22111,12223675967])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [796802367564233469943873536,845136530110140492468453376,896402649468417128588640256,950778587354310441493856256,1008452970860796493929906176,1069625885678506501667291136,1134509573155302618007863296,1203329107178599056813326336,1276323250181157323177721856,1353745201490882295366680576,1435863605304811803656585216,1522963301427410855270547456,1615346516193798334789451776,1713333579977366483790462976,1817264660267369518738702336,1927500226926143299372711936,2044422719582995014186172416,2168437686642311813436276736] 60949825924076889551964561035525037401645902348236619775 507829176091871375174893267215297682742777965088788709374 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_52 (k : ℕ) (lo : 507829176091871375174893267215297682742777965088788709375≤k) (hi : k≤4231194290983950675786183160394196180363248713596609232894) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,149,151,163,167,179,181,191,193,197,211,223,257,269,271,283,307,311,313,349,359,373,443,449,461,487,491,499,547,571,593,601,613,619,659,733,743,877,941,947,953,967,1013,1187,1217,1223,1231,1289,1307,1327,1511,1553,1721,1789,1801,2153,2251,2269,2333,2381,2663,2797,2843,2851,2897,3109,3547,3701,3911,4091,4241,4283,4391,4987,5011,5581,5881,6211,6299,6491,6733,7069,7297,7393,7901,9811,10103,10799,10859,11317,12007,12119,12161,12457,13877,14389,16073,17351,18119,19961]
  let factors : List (ℕ × ℕ × List ℕ) := [(6,1,[3,3,1231]),(2,2,[19,307]),(13,1,[12119]),(3,1,[3,4241]),(2,1,[3,7,11,59]),(3,8,[11,11]),(2,2,[3,3,3,3,3,3,11]),(5,2,[3,37,73]),(6,4,[5,11,37]),(5,1,[17351]),(19,1,[13,17,79]),(3,3,[5,877]),(6,1,[3,3,11,181]),(2,1,[3,61,107]),(3,4,[11,257]),(7,1,[24239]),(6,1,[3,5,5,19,19]),(7,8,[3,3,5,5]),(2,2,[3,5,5,193]),(6,2,[3,5011]),(6,1,[3,5,31,67]),(3,4,[5,5,193]),(2,2,[23,941]),(2,1,[3,3,47,107]),(6,2,[3,3,2663]),(7,1,[5,7,7,211]),(2,1,[5,5,31,71]),(3,3,[7,2843]),(3,4,[11,953]),(3,1,[3,3,3,3,3,11,41]),(2,1,[5,61,373]),(2,2,[3,3,5,7,181]),(2,1,[5,13,1789]),(5,5,[3,2851]),(10,4,[3,7297]),(3,1,[3,3,7,2797]),(3,3,[97,461]),(5,3,[7,6491]),(2,2,[3,7,4987]),(2,2,[3,5,13,547]),(6,1,[5,11,4091]),(2,1,[491,499]),(13,1,[37,37,191]),(2,1,[23,25447]),(3,4,[307,349]),(3,1,[3,5,86573]),(5,2,[3,228061]),(5,2,[3,3,77201]),(5,1,[17,89,947]),(10,3,[3,11,61,223]),(3,3,[490019]),(2,1,[3,37,18119]),(6,1,[3,5,5,5,5581]),(2,2,[499,2251]),(7,1,[5,7,11,6299]),(2,1,[3,3,273697]),(2,2,[3,3,3,48479]),(2,2,[3,522959]),(3,2,[47,35081]),(5,1,[7,71,6733]),(5,3,[3,3,103391]),(2,2,[613,3109]),(19,1,[5,5,17,73,127]),(5,1,[4850231]),(2,2,[13,167,1187]),(3,1,[3,3,19,32561]),(2,1,[6595229]),(3,4,[7,83,1721]),(2,2,[4022419]),(13,6,[3,3,5,7069]),(7,3,[3,3,3,223,487]),(5,2,[3,11,13,13877]),(11,1,[13190459]),(3,3,[73,45233]),(2,2,[3,3,7,17,79,103]),(2,1,[3,3,2779237]),(2,1,[151,450011]),(2,2,[7,4926547]),(3,3,[163,159209]),(3,2,[7,7,11,97,1289]),(2,2,[3,5,6275509]),(2,1,[7,313,110051]),(2,1,[5,5,11,11,223,359]),(3,3,[7,9700463]),(5,1,[23,61,350257]),(12,1,[3,3,5,269,54151]),(11,5,[3,20358721]),(5,1,[193,1801,3911]),(3,1,[3,16073,35839]),(2,1,[3,34919,60133]),(3,4,[7,79,733,2269]),(6,2,[3,53,23457817]),(2,2,[11317,426661]),(7,1,[3,3,3,982821143]),(12,1,[3,5,1954437217]),(13,4,[3,5,269571149]),(3,1,[3,3,3,7,207608537]),(6,1,[3,5,19,4391,32413]),(18,2,[3,5,53,311,95869]),(5,4,[3,11,83,3920153]),(11,1,[3,7,11,376530541]),(13,3,[3,19,482243483]),(7,1,[7,179,3701,34703]),(5,5,[3,7,484344851]),(5,1,[11,14919171613]),(2,2,[7,283,50026267]),(23,3,[3,7,43,6211,10859]),(3,3,[9811,7623269]),(5,2,[3,53072341723]),(2,2,[219903028249]),(3,1,[3,10103,15998417]),(2,1,[7,17,23,163,1170563]),(2,2,[619,19961,23333]),(5,1,[11,325479739873]),(7,1,[3,3,5,7,14715790097]),(2,1,[3,7,62311,4185751]),(3,1,[3,659,659,4492997]),(6,2,[3,3,5,81125525311]),(3,4,[107,449,1223,30977]),(11,1,[5,11707339380943]),(10,6,[3,3,328221775487]),(7,1,[5,2597191,23812933]),(2,2,[11,11,83,1511,11135863]),(3,5,[43,149,3456241483]),(3,1,[3,7,19,19,94812523621]),(3,1,[3,5,5,31,59,64697075761]),(2,2,[418909,171796785073]),(3,1,[3,43,3547,487224478777]),(3,1,[3,5,37,2381,12161,16089677]),(5,1,[7,232571,173957109943]),(26,2,[3,3,5,10307909,543225929]),(6,1,[3,3,7,967,1013,58633116511]),(19,3,[3,5,7,7,167729,10954369883563]),(5,36,[3,37,43,443,34703,2736733]),(5,37,[3,23,53,29121645719249]),(10,34,[3,61,12457,396408139709]),(5,35,[3,3,3,17749642735030351]),(5,34,[3,47,67,127,32077,26416073]),(5,34,[3,7393,357737,135903323]),(5,36,[3,3,47,675945681426797]),(5,40,[3,23,7880351,34858909]),(5,34,[3,3,197,57601,12598705363]),(10,34,[3,443,7444153,137943317]),(5,37,[3,57901,363497,2865623]),(5,36,[3,89,1437547483141603]),(14,1,[5,7,7,11,13,17,19,2153,566403306231748343]),(5,37,[3,37,43,443,34703,2736733]),(10,37,[3,3,37,4283,27259,5235733]),(7,1,[5,7,11,13,17,19,269,1217,352423,78476026987]),(5,38,[3,23,53,29121645719249]),(5,35,[3,287868877752581429]),(7,1,[5,7,11,13,17,19,1327,7236847872298394407]),(5,35,[3,61,12457,396408139709]),(10,35,[3,37,7901,1044448883507]),(7,1,[5,7,11,13,13,17,19,6692603,117073393809431]),(5,36,[3,3,3,17749642735030351]),(5,35,[3,3,571,189055742680513]),(11,1,[5,7,11,13,17,19,10803709176456813950761]),(5,35,[3,47,67,127,32077,26416073]),(10,35,[3,271,1307,969792041707]),(11,1,[5,7,11,13,17,19,22159,517129113367491271]),(7,35,[3,7393,357737,135903323]),(5,35,[3,3,3,29,2333,598335137273]),(7,1,[5,7,11,13,17,19,1310995711,9270947761111]),(5,37,[3,3,47,675945681426797]),(14,1,[5,7,11,13,17,19,83,219187,708612453810593]),(7,41,[3,23,7880351,34858909]),(7,1,[5,7,7,11,13,17,19,101,1553,10799,1153197032189]),(5,35,[3,3,197,57601,12598705363]),(11,1,[5,7,11,13,17,19,14389,1007914219663042981]),(7,35,[3,443,7444153,137943317]),(7,1,[5,7,11,13,17,19,601,743,39163,879612112997]),(5,38,[3,57901,363497,2865623]),(7,1,[5,7,11,13,17,19,26380919,618467352712031]),(5,37,[3,89,1437547483141603]),(7,1,[5,5,5,7,11,13,17,19,12007,90523,636868100677]),(5,38,[3,3,37,4283,27259,5235733]),(7,1,[5,7,7,11,13,17,19,5881,445871788365280903]),(5,36,[3,287868877752581429]),(7,1,[5,7,11,13,17,19,2718872447,7160554277207]),(5,36,[3,37,7901,1044448883507]),(11,1,[5,5,7,11,11,13,17,19,113,227531,14602594555981]),(5,36,[3,3,571,189055742680513]),(7,1,[5,7,11,13,17,19,109,2897,3591193,19314090149]),(5,36,[3,271,1307,969792041707]),(7,1,[5,7,11,13,17,19,71,593,1714289,321860122319]),(10,36,[3,3,3,29,2333,598335137273])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [2299975465883623366659670016,2439492367476400118684450816,2587472364036902099359891456,2744428862255016640046432256,2910906385049622047501582336,3087482464286726523459731456,3274769663837395282858868736,3473417750986408262962774016,3684115867132700359850459136,3907594940644630836864352256,4144630260216773295594274816,4396044231696690910075027456,4662708957676817480360656896,4945549661934236868527783936,5245547552781698087105069056,5563743365210361363217514496,5901240943303733823024398336,6259211205616731848039202816] 507829176091871375174893267215297682742777965088788709375 4231194290983950675786183160394196180363248713596609232894 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_53 (k : ℕ) (lo : 4231194290983950675786183160394196180363248713596609232895≤k) (hi : k≤35253991949736248253797044324670210631167357342309003821054) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,101,109,113,127,131,137,139,149,151,163,173,181,197,199,211,227,239,283,311,313,317,337,367,379,383,401,467,541,587,599,601,607,661,691,709,719,787,809,821,823,881,919,1019,1039,1061,1087,1093,1109,1151,1153,1279,1427,1447,1451,1531,1549,1553,1609,1637,1741,1787,1889,1907,1993,2111,2129,2207,2293,2477,2539,2593,2657,2707,2767,2861,3307,3413,3581,3593,4021,4079,4231,4591,4679,4937,5021,5227,5471,5783,6043,6211,6277,6343,6673,6997,8219,8353,9157,9463,9929,10079,10709,11177,11353,13399,14207,14347,14699,15061,15787,17393,17431]
  let factors : List (ℕ × ℕ × List ℕ) := [(5,3,[3,3,7,7,7]),(2,1,[3,3,7,227]),(3,3,[11,367]),(2,2,[8353]),(17,1,[19,881]),(7,4,[3,5,5,31]),(2,2,[9463]),(3,5,[1553]),(6,1,[5,5,1061]),(3,1,[3,11,823]),(5,3,[3,17,137]),(2,2,[15787]),(13,1,[7,4937]),(2,1,[3,3,4021]),(2,1,[37853]),(3,3,[17,601]),(3,1,[3,14207]),(3,3,[17,661]),(11,3,[3,5,787]),(3,1,[3,7,31,79]),(6,2,[3,31,283]),(15,3,[3,4679]),(2,1,[37,1637]),(7,1,[3,3,5,7,199]),(2,2,[31,1087]),(2,2,[3,11353]),(11,4,[3,5,607]),(10,2,[5,5,11,173]),(2,2,[5,10079]),(2,2,[5,11,13,79]),(7,1,[121139]),(2,2,[17,4079]),(22,1,[5,149,227]),(2,1,[11,17431]),(2,1,[29,6997]),(2,2,[5,43,587]),(2,2,[3,3,14347]),(7,1,[5,47,1109]),(2,2,[3,3,15061]),(2,1,[277373]),(3,7,[67,71]),(2,2,[19,29,317]),(19,1,[5,72379]),(7,1,[3,5,13,1907]),(6,1,[3,145681]),(2,2,[3,3,31,1093]),(5,2,[3,13,11177]),(7,3,[3,31,3593]),(3,4,[37,4591]),(6,1,[3,5,94441]),(3,1,[3,3,3,43,1531]),(2,1,[3,743731]),(3,1,[3,3,3,41,2477]),(2,1,[7,405827]),(7,2,[5,17,24697]),(2,2,[19,112297]),(7,1,[5,7,136237]),(3,3,[5,13,59,467]),(6,2,[3,5,7,29,29,53]),(2,2,[1741,3307]),(2,1,[83,383,401]),(7,2,[3,1039,2111]),(3,1,[3,11,542197]),(11,3,[3,7,37,6343]),(2,1,[3,3,19,89,1427]),(2,2,[3,3,5,242279]),(3,3,[13,13,19,2129]),(2,1,[5,199,28603]),(3,7,[7,89897]),(2,1,[3,41,338231]),(5,2,[3,8534573]),(2,1,[54689753]),(3,2,[7,1609,2539]),(3,1,[3,3,3,29,75707]),(23,4,[3,7,7,11,9929]),(2,1,[19,61,149,919]),(2,1,[3,3,13,19,31,2593]),(2,1,[149,151,13399]),(29,1,[5,197,521231]),(2,2,[3,31,2833231]),(2,1,[3,7,11,19,134789]),(7,1,[7,6043,14699]),(2,1,[1447,554747]),(10,1,[3,3,3,5,1153,6211]),(3,1,[3,1787,201581]),(13,6,[3,23,29,73,239]),(3,3,[7,17,2673193]),(3,1,[3,41,1279,8219]),(3,3,[5,5021,17393]),(5,3,[11,17,1889,2293]),(3,4,[67,2707,2767]),(2,2,[2161351483]),(3,1,[3,11,311,337,1549]),(5,3,[3,3,3,56919971]),(7,3,[3,5,5,5,5681579]),(11,3,[3,89,149,81737]),(2,2,[113,113,874087]),(2,2,[7,2585976847]),(3,1,[3,23,1243564799]),(6,1,[3,53051,3554983]),(5,2,[3,17,17,821,608897]),(3,1,[3,7,127,6277,63149]),(2,2,[55897,18720661]),(2,1,[3,7,7,11,11,13,9536591]),(5,5,[3,3,61,181,541,2657]),(3,4,[7,43,1053961933]),(2,1,[37,72407351717]),(2,1,[379,719,26319949]),(7,5,[3,3,3,41,602928203]),(2,2,[2207,69119,102859]),(5,1,[29,1131572418799]),(2,1,[3,105277,118557163]),(2,2,[5,31,3581,39428089]),(2,2,[3,13,337,2234332609]),(17,4,[3,13,43,101,256883089]),(7,1,[7,599,171611942263]),(3,1,[3,3,117463333920349]),(5,1,[43,709,5075880669329]),(2,2,[13,723791,44644867613]),(6,2,[3,5,5,6673,9157,1026825071]),(7,3,[3,3,3,2861,65631200290343]),(2,2,[3,5,809,1439137747817519]),(2,1,[3,3,18823139360926779301]),(7,4,[3,3,19,109379507,3493210121]),(23,3,[3,13,47,1680304775473005917]),(10,3,[3,3,7,163,317406059,1605437819]),(5,37,[3,37,25494779,102414877]),(5,37,[3,43,1993,33413,35785003]),(10,35,[3,67,5484079,1183177843]),(10,37,[3,3,3,3,3413,54319,23029949]),(13,36,[3,3,3,71,181,2114324380183]),(5,38,[3,125371,190301,2717873]),(5,35,[3,3,43,1019,4185715151669]),(5,37,[3,47,1219789,2544879737]),(5,36,[3,309496747931666447]),(10,36,[3,3,3,3,3,3,698669,1933546411]),(10,35,[3,80547713,8645405933]),(5,35,[3,113,383483,17044737001]),(11,1,[5,7,11,13,17,19,24639989227536158766889]),(5,38,[3,37,25494779,102414877]),(5,36,[3,225941,1733668587517]),(7,1,[5,5,5,7,11,13,17,19,1045386204014219989393]),(5,38,[3,43,1993,33413,35785003]),(5,35,[3,3,131,2114340010566283]),(7,1,[5,7,11,11,13,17,19,1151,504821,516493,8396981]),(5,36,[3,67,5484079,1183177843]),(5,36,[3,3,211,696161391448849]),(7,1,[5,7,11,13,17,19,47,43610221,14344424844899]),(5,38,[3,3,3,3,3413,54319,23029949]),(10,38,[3,5471,21358128663073]),(7,1,[5,5,7,11,13,17,19,37,6479889593,26013944569]),(5,37,[3,3,3,71,181,2114324380183]),(5,37,[3,691,33479,10714838839]),(14,1,[5,7,7,11,13,17,19,1451,37201,87539031759581]),(7,39,[3,125371,190301,2717873]),(5,37,[3,59,71,62762765058989]),(7,1,[5,5,7,11,13,17,19,173,40558506630625005769]),(7,36,[3,3,43,1019,4185715151669]),(7,1,[5,7,7,11,13,13,17,19,61,5227,5783,49697,4462387]),(5,38,[3,47,1219789,2544879737]),(11,1,[5,5,7,11,13,17,19,113,69855746279062372261]),(5,37,[3,309496747931666447]),(11,1,[5,7,11,13,17,19,41862662175111264810793]),(7,37,[3,3,3,3,3,3,698669,1933546411]),(7,1,[5,7,11,11,11,13,17,19,83204827,4410310947043]),(5,36,[3,80547713,8645405933]),(14,1,[5,7,11,13,17,19,139,338816508496682027419]),(7,36,[3,113,383483,17044737001]),(11,1,[5,5,5,7,11,13,17,19,313,85243,74888054694907]),(5,37,[3,225941,1733668587517]),(14,1,[5,5,7,11,13,17,19,83,139,114387029,8029568369]),(5,36,[3,3,131,2114340010566283]),(11,1,[5,7,11,13,17,19,12294713737,4570773672097]),(5,37,[3,3,211,696161391448849]),(7,1,[5,7,11,13,17,19,1087,10709,14327561,357382819]),(7,39,[3,5471,21358128663073]),(7,1,[5,7,11,13,17,19,67,101,1743613,5358144027059]),(5,38,[3,691,33479,10714838839]),(22,1,[5,7,7,11,13,13,17,17,19,67,109,4231,32297,43435027]),(5,38,[3,59,71,62762765058989])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [6638896030845561217489043456,7041612575843534367302352896,7468757964770616542878498816,7921813953691432900588732416,8402352530575804168925085696,8912040659855895071949848576,9452646503352947466930487296,10026045661867299742318329856,10634227284678904261164138496,11279301268702916227016687616,11963505575237156241078747136,12689213855631257098346561536,13458943657416405800395472896,14275365323266186442541367296,15141311431229984831969427456,16059785956956318554732363776,17033975249869413711878291456,18067259099997618152570617856] 4231194290983950675786183160394196180363248713596609232895 35253991949736248253797044324670210631167357342309003821054 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_54 (k : ℕ) (lo : 35253991949736248253797044324670210631167357342309003821055≤k) (hi : k≤293733628181498388409147289178041398271439354037905093820414) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,107,109,113,127,139,151,157,163,167,173,179,191,193,199,211,227,251,257,269,271,283,331,349,373,383,397,409,433,439,443,463,491,503,523,547,557,587,601,607,613,641,739,821,853,859,907,919,937,971,1021,1091,1093,1171,1307,1429,1451,1523,1667,1723,1753,1831,1889,1951,2237,2239,2539,2693,2791,2843,2851,2963,3257,3361,3727,3917,4327,4723,4729,4813,5107,5279,5821,6701,6899,7307,7907,8287,8597,8837,8971,9631,10589,10723,11131,11491,12011,12653,13001,14009,14401,14503,14533,16451,19991]
  let factors : List (ℕ × ℕ × List ℕ) := [(2,1,[3,3,3,3,3,43]),(2,1,[5,11,191]),(2,1,[10589]),(2,2,[3,1889]),(5,1,[12011]),(2,1,[14009]),(3,1,[3,4813]),(5,3,[3,19,71]),(2,2,[3,2791]),(5,1,[11,1753]),(5,1,[19991]),(2,1,[5,7,607]),(7,4,[3,5,191]),(2,2,[5,5,463]),(2,1,[3,3,5,557]),(11,1,[5,5107]),(2,1,[7,11,409]),(3,4,[4327]),(2,1,[7,5279]),(5,1,[39983]),(2,1,[5,7,1171]),(2,1,[5,7,11,113]),(17,4,[3,3,3,7,29]),(2,2,[3,3,5,17,29]),(2,1,[3,5,17,179]),(3,4,[23,251]),(2,1,[3,3,13,409]),(13,3,[3,5,17,47]),(19,2,[3,3,2963]),(3,3,[83,163]),(3,1,[3,21011]),(2,2,[3,10723]),(11,1,[3,7,29,109]),(5,1,[17,47,89]),(7,1,[53,1723]),(2,1,[3,19,23,71]),(3,1,[3,3,13,13,73]),(2,2,[7,67,151]),(2,2,[11,23,283]),(3,1,[3,17,29,97]),(13,1,[3,5,9631]),(2,1,[3,50131]),(5,5,[3,3727]),(5,1,[167,1093]),(13,3,[3,17,919]),(5,3,[19,2693]),(5,1,[17,47,257]),(6,2,[3,3,3,5,821]),(5,2,[3,3,29,439]),(2,1,[11,28879]),(2,2,[331,523]),(3,1,[3,142223]),(11,1,[5,5,21179]),(10,1,[3,5,5,37,191]),(11,1,[5,13,8287]),(2,2,[3,11,23,503]),(2,2,[37,11491]),(5,1,[3,107,2843]),(2,2,[458317]),(14,3,[3,3,17,19,83]),(5,1,[1058951]),(10,5,[3,11,11,397]),(3,1,[3,7,73,1523]),(7,1,[31,92369]),(2,2,[1527109]),(2,2,[3,3,7,37,919]),(6,1,[3,5,357793]),(2,1,[3,5,37,11131]),(11,1,[5,13,95707]),(3,3,[1700669]),(2,2,[3,3,3,3,5,8971]),(2,1,[3,547,4729]),(2,1,[3,3,3,5,87011]),(5,6,[3,113,1091]),(3,5,[853,1307]),(5,5,[3,11,13,47,97]),(2,1,[3,29,410687]),(6,2,[3,5,7,7,11,2239]),(3,9,[5,17,1667]),(6,3,[5,127,14533]),(2,1,[5,5,31,81971]),(13,1,[89,383,3257]),(2,1,[3,937,42491]),(2,2,[5,13605353]),(6,2,[3,3,3,5,13,151,271]),(2,1,[31,12441911]),(6,1,[3,29,59,79967]),(3,1,[3,3,5,10733791]),(5,1,[53,23492971]),(2,1,[3,5,29,61,62987]),(3,3,[29,15520579]),(2,1,[3,3,11,1429,14503]),(2,2,[67,739,20899]),(17,7,[3,5,11,107,2237]),(2,1,[3600774329]),(5,1,[16451,374953]),(11,5,[3,5,7,397,24023]),(2,1,[3,3,7,157,227,8597]),(3,6,[17,73827641]),(2,1,[3,29,771398483]),(2,2,[38604948859]),(3,3,[5,29,222042719]),(3,1,[3,3,5,31,47,2117903]),(7,1,[7,157,443,300787]),(2,2,[5,7,51071,106669]),(3,1,[3,11,23,7307,69233]),(2,2,[5,182639,288931]),(2,2,[349,433,1825207]),(7,1,[5,17,12336703607]),(13,7,[3,3,3,3,5,72409261]),(2,1,[7,11,349,439,222067]),(7,1,[3,5,7,199,6701,28019]),(3,8,[13,23,37,971,3361]),(7,3,[3,3,134223336043]),(7,3,[3,3,3,5,859,14533021]),(2,1,[3,89,907,72547841]),(2,2,[3,91291,35675873]),(13,1,[3,5,5,1055401378181]),(2,1,[3,11,3753696090241]),(3,6,[7,11,80324473409]),(17,3,[3,3,3,3,2097239613191]),(2,2,[3,211,762676949861]),(3,1,[3,3,45841,2490254927]),(3,1,[3,3,11,39082633464517]),(3,1,[3,2054803969954927]),(6,5,[5,5,7,23,613,287265421]),(5,1,[7,331,2851,5821,1833269]),(2,1,[29,4723,767934236059]),(5,5,[3,3,4729,87697,4669519]),(6,1,[3,5,5,37,38567,3342720091]),(2,2,[1951,635339,272107061]),(34,1,[3,3,5,5726879,277720620391]),(11,3,[3,113,151,1359011269347769]),(3,2,[5,373,210363297020586107]),(13,36,[3,557723168011194337]),(5,37,[3,71459539,4139088749]),(5,36,[3,173,269,13482574242121]),(10,37,[3,43,7738361425974367]),(5,37,[3,31,1451,7846294781011]),(5,36,[3,3,491,919,8837,62585953]),(11,36,[3,3,53,73,286397,238884403]),(10,36,[3,101,32377,257569554041]),(10,37,[3,3,601,247743941955907]),(5,38,[3,3,3,3,3,3,59,107,154419795437]),(5,36,[3,2539,395839004959553]),(5,36,[3,47,22680868955802401]),(7,1,[5,7,11,13,17,17,19,1021,443341,9242737523969]),(5,37,[3,557723168011194337]),(5,37,[3,1930249,292880512919]),(7,1,[5,5,7,11,13,17,19,79,1831,127055051,820941223]),(5,38,[3,71459539,4139088749]),(11,37,[3,139,853339,5055262081]),(14,1,[5,7,11,13,17,19,37,283277,1060051,7201548659]),(5,37,[3,173,269,13482574242121]),(13,39,[3,3,587,7907,88741,128677]),(7,1,[5,7,11,11,13,17,19,19,53,14401,22669,126067,186163]),(5,38,[3,43,7738361425974367]),(5,36,[3,1349157299535810917]),(14,1,[5,7,11,13,17,19,163,3917,140986341413164367]),(5,38,[3,31,1451,7846294781011]),(5,37,[3,715498705910263351]),(21,1,[5,7,11,13,17,19,23,29,143142514990577072011]),(5,37,[3,3,491,919,8837,62585953]),(5,37,[3,46301,692453,23670337]),(11,1,[5,7,7,11,13,17,19,73907,6108437,32044760161]),(7,37,[3,3,53,73,286397,238884403]),(14,1,[5,7,11,13,17,19,193,556531422933143578729]),(10,37,[3,101,32377,257569554041]),(11,1,[5,7,11,13,17,19,41,6899,365063,1103279224877]),(5,38,[3,3,601,247743941955907]),(7,1,[5,7,7,11,11,13,17,19,1569310195773572358221]),(15,39,[3,3,3,3,3,3,59,107,154419795437]),(11,1,[5,7,7,11,13,17,19,19,641,286927,5239558499099]),(5,37,[3,2539,395839004959553]),(11,1,[5,5,7,11,13,17,19,23,95881,12328823819729563]),(5,37,[3,47,22680868955802401]),(11,1,[5,7,11,13,17,19,4103507827,35137676214259]),(5,38,[3,1930249,292880512919]),(21,1,[5,7,11,13,17,19,966041191,158310206727151]),(5,38,[3,139,853339,5055262081]),(7,1,[5,7,7,11,13,13,17,19,71,13001,1931098037048053]),(7,40,[3,3,587,7907,88741,128677]),(7,1,[5,7,11,13,13,17,19,12653,108233,9664080195097]),(5,37,[3,1349157299535810917]),(11,1,[5,7,11,13,17,19,33493,409337,1077311,12355411]),(5,38,[3,715498705910263351]),(7,1,[5,5,7,11,13,17,19,47,157,132763,4611553,8568757]),(5,38,[3,46301,692453,23670337])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [19163222134636744314523222016,20325666363631059737872695296,21558624677887222508511297536,22866374363441227865119522816,24253452552875081118752178176,25724671115547499905077477376,27285134080910216787306479616,28940254988836222326617931776,30695775802470165419976032256,32557786827469668866196504576,34532747676853366880160710656,36627509994172401131712413696,38849341018655285425121263616,41205948409702302890680385536,43705508298796359049298313216,46356691829327870954838163456,49168696675438448052677902336,52151278186592468677527863296] 35253991949736248253797044324670210631167357342309003821055 293733628181498388409147289178041398271439354037905093820414 (by decide +kernel) (by decide +kernel) k lo hi

set_option maxRecDepth 32000 in
set_option maxHeartbeats 6000000 in
private theorem certifiedBlock_55 (k : ℕ) (lo : 293733628181498388409147289178041398271439354037905093820415≤k) (hi : k≤1000000000000000000000000000000000000000000000000000000000000) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  let small : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,79,83,89,97,103,107,113,139,149,163,181,193,227,229,251,257,269,281,313,347,349,359,389,439,449,463,487,523,613,619,761,797,823,827,1117,1187,1433,1621,1627,1709,1747,1789,1867,1973,2137,2333,2441,2521,2593,3361,3529,3833,3943,4327,5437,5743,5807,6287,7069,7351,9547,10103,10223,10253,10589,10709,11483,11887,12043,13903,16381]
  let factors : List (ℕ × ℕ × List ℕ) := [(2,2,[13,523]),(2,1,[41,349]),(2,2,[9547]),(21,4,[3,13,67]),(6,2,[3,3,3,389]),(2,1,[67,347]),(2,2,[7,1789]),(2,1,[3,3,3,23,41]),(5,4,[3,1117]),(7,1,[11,2593]),(3,2,[5,7,449]),(5,4,[3,37,41]),(2,1,[38189]),(11,1,[3,3,3,3,3,3,5,11]),(11,3,[3,3529]),(2,2,[11,2333]),(2,1,[5,7,1627]),(2,2,[5,5807]),(2,1,[19,41,79]),(2,1,[11,43,193]),(3,2,[5,10223]),(2,2,[5,5,3361]),(5,1,[17,12043]),(3,6,[29,227]),(2,2,[3,3,37,359]),(2,1,[47,5743]),(3,1,[3,23,53,79]),(3,3,[11,7069]),(2,1,[31,11483]),(3,1,[3,3,3,7,13,149]),(2,2,[3,62861]),(2,1,[421313]),(2,1,[61,67,107]),(3,5,[11,17,149]),(15,3,[3,23,1621]),(3,3,[113891]),(5,1,[13,29,29,47]),(2,1,[3,17,13903]),(2,2,[3,19,6287]),(7,3,[3,17,41,89]),(2,2,[229,1747]),(3,1,[3,3,3,19,1621]),(7,1,[874619]),(2,2,[3,7,37,619]),(19,1,[1749239]),(5,1,[59,41809]),(6,2,[3,478189]),(2,1,[3,1027703]),(10,2,[3,5,13,11887]),(2,1,[3,1663147]),(2,1,[193,27197]),(6,1,[3,823,4327]),(6,2,[3,67,53617]),(5,1,[3,13,163,3833]),(2,2,[3,7,732187]),(5,3,[3,89,139,313]),(2,1,[7,10498043]),(5,1,[17,79,72817]),(2,1,[613,204461]),(3,1,[3,11,29,182579]),(6,1,[13,41,181,2137]),(5,1,[3,11,827,10253]),(3,1,[3,71,1418107]),(2,1,[3,3,43,842627]),(2,2,[13,29,711947]),(2,2,[3,19,9271861]),(12,1,[3,7,11,17,577807]),(5,1,[84697,123083]),(2,2,[3,3,23,23,6166219]),(5,1,[3,59,251,1923853]),(7,1,[5,19,103,439,42013]),(10,3,[3,761,61503709]),(3,3,[59,97,43108069]),(13,1,[5,17,97,146972603]),(7,1,[3,1433437,3498479]),(2,1,[29,1123303741177]),(5,1,[113,139,10589,891617]),(5,3,[3,79,229,46499,336101]),(5,1,[76379,117429474637]),(2,1,[3,2521,2423578223471]),(2,1,[3,3,6785584031479417]),(2,1,[3,181,894793,349456207]),(2,1,[37,463,50093,559629247]),(5,1,[960484046640946403]),(2,1,[1867,1488793,412325603]),(7,3,[3,5,59,797,754333,21366727]),(17,1,[13,10709,36659044208222347]),(5,3,[3,10207124315072180964599]),(10,3,[3,11,29,149,1973,28619,4538096179]),(10,36,[3,23,409463,170942034463]),(5,37,[3,29,48732763,604113583]),(5,37,[3,3,1433,10103,20849521703]),(5,36,[3,1920968093281892807]),(5,37,[3,3,339582391063543987]),(11,36,[3,3,89,269,30089095453939]),(5,36,[3,2292181138458446387]),(10,38,[3,3,102653,1973659831097]),(5,43,[3,50923,80191,4933463]),(5,38,[3,31,163,539843,250669187]),(5,37,[3,2441,911129,652193299]),(11,1,[5,7,7,11,13,17,19,19,7351,195586463,1073616077]),(10,37,[3,23,409463,170942034463]),(11,1,[5,7,11,13,17,17,19,57047,622073,360943345991]),(5,38,[3,29,48732763,604113583]),(14,1,[5,7,7,11,13,13,17,19,439,1709,1600253,2113984309]),(5,38,[3,3,1433,10103,20849521703]),(11,1,[5,7,11,13,17,19,244970983561732343150377]),(5,37,[3,1920968093281892807]),(7,1,[5,5,7,11,13,17,19,139,5738269,65151616988267]),(5,38,[3,3,339582391063543987]),(7,1,[5,5,7,11,13,17,19,83,5437,122140512566629507]),(5,37,[3,3,89,269,30089095453939]),(7,1,[5,7,11,13,17,19,292309835834122288969513]),(7,37,[3,2292181138458446387]),(19,1,[5,7,7,11,13,17,19,487,90947902499720771161]),(10,39,[3,3,102653,1973659831097]),(7,1,[5,7,11,13,17,19,107,257,281,3943,116141,92930953]),(5,44,[3,50923,80191,4933463]),(19,1,[5,7,11,13,17,19,1187,16381,17938291686598847]),(5,39,[3,31,163,539843,250669187]),(11,1,[5,5,5,5,7,11,13,17,19,9978883,296590016421983]),(5,38,[3,2441,911129,652193299])]
  let rows : List (ℕ × ℕ × List ℕ) := small.map (fun p => (p,0,[])) ++ factors.map (fun t =>
    (2^t.2.1*t.2.2.prod+1,t.1,List.replicate t.2.1 2 ++ t.2.2))
  exact certified_cover rows [55314783471945498832683401216,58670187703738578750119346176,62229131317934614190726578176,66003961098441655320341118976,70007772667939395937077559296,74254456161740500286671159296,78758744209496600697074876416,83536262874864832674955001856,88603586916078603620147265536,93978295663639625928336736256,99679035135711716700791504896] 293733628181498388409147289178041398271439354037905093820415 1000000000000000000000000000000000000000000000000000000000000 (by decide +kernel) (by decide +kernel) k lo hi

private theorem certifiedBlock_join (a b c : ℕ)
    (left : ∀ k : ℕ, a≤k → k≤b → ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2)
    (right : ∀ k : ℕ, b+1≤k → k≤c → ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2)
    (k : ℕ) (lo : a≤k) (hi : k≤c) : ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 := by
  by_cases cut : k≤b
  · exact left k lo cut
  · exact right k (by omega) hi

theorem high_multiplicity_two {k : ℕ} (lo : 1494800044≤k) (hi : k≤1000000000000000000000000000000000000000000000000000000000000) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p=2 :=
  (certifiedBlock_join 1494800044 41203610185680866539752074506960894 1000000000000000000000000000000000000000000000000000000000000 (certifiedBlock_join 1494800044 5398017626070663048334 41203610185680866539752074506960894 (certifiedBlock_join 1494800044 1950498488857384 5398017626070663048334 (certifiedBlock_join 1494800044 433907278453 1950498488857384 (certifiedBlock_join 1494800044 8602834273 433907278453 certifiedBlock_0 (certifiedBlock_join 8602834274 60432445663 433907278453 certifiedBlock_1 certifiedBlock_2)) (certifiedBlock_join 433907278454 28400207023309 1950498488857384 (certifiedBlock_join 433907278454 3470140005859 28400207023309 certifiedBlock_3 certifiedBlock_4) (certifiedBlock_join 28400207023310 234868748802868 1950498488857384 certifiedBlock_5 certifiedBlock_6))) (certifiedBlock_join 1950498488857385 1123735244629542424 5398017626070663048334 (certifiedBlock_join 1950498488857385 16229873735087374 1123735244629542424 certifiedBlock_7 (certifiedBlock_join 16229873735087375 134982947321560804 1123735244629542424 certifiedBlock_8 certifiedBlock_9)) (certifiedBlock_join 1123735244629542425 77923389811670798974 5398017626070663048334 (certifiedBlock_join 1123735244629542425 9359571870991978414 77923389811670798974 certifiedBlock_10 certifiedBlock_11) (certifiedBlock_join 77923389811670798975 648236330623735253734 5398017626070663048334 certifiedBlock_12 certifiedBlock_13)))) (certifiedBlock_join 5398017626070663048335 14956760007299482974445756414 41203610185680866539752074506960894 (certifiedBlock_join 5398017626070663048335 3112168098155495977307134 14956760007299482974445756414 (certifiedBlock_join 5398017626070663048335 44952220242206939987134 3112168098155495977307134 certifiedBlock_14 (certifiedBlock_join 44952220242206939987135 374147880289409352327934 3112168098155495977307134 certifiedBlock_15 certifiedBlock_16)) (certifiedBlock_join 3112168098155495977307135 215729467198384297245002494 14956760007299482974445756414 (certifiedBlock_join 3112168098155495977307135 25906211690884115771609854 215729467198384297245002494 certifiedBlock_17 certifiedBlock_18) (certifiedBlock_join 215729467198384297245002495 1796859816709802564152317694 14956760007299482974445756414 certifiedBlock_19 certifiedBlock_20))) (certifiedBlock_join 14956760007299482974445756415 8606338612891744630593965469694 41203610185680866539752074506960894 (certifiedBlock_join 14956760007299482974445756415 124239395924916865525385005054 8606338612891744630593965469694 certifiedBlock_21 (certifiedBlock_join 124239395924916865525385005055 1033663869923839772943807154174 8606338612891744630593965469694 certifiedBlock_22 certifiedBlock_23)) (certifiedBlock_join 8606338612891744630593965469695 596696160471664649054305859444734 41203610185680866539752074506960894 (certifiedBlock_join 8606338612891744630593965469695 71669396469699673331911983230974 596696160471664649054305859444734 certifiedBlock_24 certifiedBlock_25) (certifiedBlock_join 596696160471664649054305859444735 4959726881428298139407231799607294 41203610185680866539752074506960894 certifiedBlock_26 certifiedBlock_27))))) (certifiedBlock_join 41203610185680866539752074506960895 314994925738196187620127920066782521967641624574 1000000000000000000000000000000000000000000000000000000000000 (certifiedBlock_join 41203610185680866539752074506960895 113212912248146446914748909106302052990974 314994925738196187620127920066782521967641624574 (certifiedBlock_join 41203610185680866539752074506960895 23784947663657349347535370593630683134 113212912248146446914748909106302052990974 (certifiedBlock_join 41203610185680866539752074506960895 342914391149760390443021924737744894 23784947663657349347535370593630683134 certifiedBlock_28 (certifiedBlock_join 342914391149760390443021924737744895 2855961681505938789824544240495230974 23784947663657349347535370593630683134 certifiedBlock_29 certifiedBlock_30)) (certifiedBlock_join 23784947663657349347535370593630683135 1639577419169801617090623296675290546174 113212912248146446914748909106302052990974 (certifiedBlock_join 23784947663657349347535370593630683135 197408778092644864465856335061493743614 1639577419169801617090623296675290546174 certifiedBlock_31 certifiedBlock_32) (certifiedBlock_join 1639577419169801617090623296675290546175 13608489505686209262113906953343287689214 113212912248146446914748909106302052990974 certifiedBlock_33 certifiedBlock_34))) (certifiedBlock_join 113212912248146446914748909106302052990975 65388181237838415887562540913331332423090174 314994925738196187620127920066782521967641624574 (certifiedBlock_join 113212912248146446914748909106302052990975 942631794226429097258751070810596395974654 65388181237838415887562540913331332423090174 certifiedBlock_35 (certifiedBlock_join 942631794226429097258751070810596395974655 7850509911003015886599502290291887708307454 65388181237838415887562540913331332423090174 certifiedBlock_36 certifiedBlock_37)) (certifiedBlock_join 65388181237838415887562540913331332423090175 4537920068239263404312538273026024052470317054 314994925738196187620127920066782521967641624574 (certifiedBlock_join 65388181237838415887562540913331332423090175 544718574944255015728900398161949631558189054 4537920068239263404312538273026024052470317054 certifiedBlock_38 certifiedBlock_39) (certifiedBlock_join 4537920068239263404312538273026024052470317055 37807207924022242178699991307404362612805206014 314994925738196187620127920066782521967641624574 certifiedBlock_40 certifiedBlock_41)))) (certifiedBlock_join 314994925738196187620127920066782521967641624575 877975684353233770983053812712178361431842508679151614 1000000000000000000000000000000000000000000000000000000000000 (certifiedBlock_join 314994925738196187620127920066782521967641624575 182183349958096900658611386065147197364161757577214 877975684353233770983053812712178361431842508679151614 (certifiedBlock_join 314994925738196187620127920066782521967641624575 2624426974461194131168937844575824509804547670014 182183349958096900658611386065147197364161757577214 certifiedBlock_42 (certifiedBlock_join 2624426974461194131168937844575824509804547670015 21865985680473949388194443528516696172678921322494 182183349958096900658611386065147197364161757577214 certifiedBlock_43 certifiedBlock_44)) (certifiedBlock_join 182183349958096900658611386065147197364161757577215 12647179923613923665559974066223780521992910605910014 877975684353233770983053812712178361431842508679151614 (certifiedBlock_join 182183349958096900658611386065147197364161757577215 1517925041354314083167506089471868852362815666651134 12647179923613923665559974066223780521992910605910014 certifiedBlock_45 certifiedBlock_46) (certifiedBlock_join 12647179923613923665559974066223780521992910605910015 105375014618463822560513826692051241962591418524368894 877975684353233770983053812712178361431842508679151614 certifiedBlock_47 certifiedBlock_48))) (certifiedBlock_join 877975684353233770983053812712178361431842508679151615 507829176091871375174893267215297682742777965088788709374 1000000000000000000000000000000000000000000000000000000000000 (certifiedBlock_join 877975684353233770983053812712178361431842508679151615 7315220356618431876746424535945111860343510614530850814 507829176091871375174893267215297682742777965088788709374 certifiedBlock_49 (certifiedBlock_join 7315220356618431876746424535945111860343510614530850815 60949825924076889551964561035525037401645902348236619774 507829176091871375174893267215297682742777965088788709374 certifiedBlock_50 certifiedBlock_51)) (certifiedBlock_join 507829176091871375174893267215297682742777965088788709375 35253991949736248253797044324670210631167357342309003821054 1000000000000000000000000000000000000000000000000000000000000 (certifiedBlock_join 507829176091871375174893267215297682742777965088788709375 4231194290983950675786183160394196180363248713596609232894 35253991949736248253797044324670210631167357342309003821054 certifiedBlock_52 certifiedBlock_53) (certifiedBlock_join 35253991949736248253797044324670210631167357342309003821055 293733628181498388409147289178041398271439354037905093820414 1000000000000000000000000000000000000000000000000000000000000 certifiedBlock_54 certifiedBlock_55)))))) k lo hi

end Bin304

namespace Bin304
open OMA.S_oeis_a304916

private theorem terms_in_range (allowed : List ℕ) (bound digits primeBound : ℕ)
    (square : 2*bound < primeBound^2)
    (limit : 2*bound<2^(1+digits)) :
    let primes := (List.range (primeBound+1)).filter Nat.Prime
    let powers := primes.map fun p => (List.range' 1 digits).map (p^·)
    (List.range (bound+1)).all (fun k =>
      allowed.contains k == powers.all (fun qs =>
        let s := qs.countP (fun q => decide (q≤k%q+k%q))+1
        s == 2^s.log2)) = true →
    ∀ k ≤ bound, IsTerm k ↔ k ∈ allowed := by
  intro primes powers checked k hk
  have tested := beq_iff_eq.mp (List.all_eq_true.mp checked k (List.mem_range.mpr (by omega)))
  have val (p : ℕ) (hp : p.Prime) := carry_count k p digits hp <|
    calc 2*k ≤ 2*bound := by omega
         _ < 2^(1+digits) := limit
         _ ≤ p^(1+digits) := Nat.pow_le_pow_left hp.two_le _
  constructor
  · intro h
    have ok : powers.all (fun qs =>
        let s := qs.countP (fun q => decide (q≤k%q+k%q))+1
        s == 2^s.log2) = true := by
      apply List.all_eq_true.mpr
      intro qs hqs
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hqs
      have pp : p.Prime := of_decide_eq_true (List.mem_filter.mp hp).2
      obtain ⟨e,he⟩ := term_iff_valuations.mp h p pp
      rw [val p pp] at he
      dsimp only
      apply beq_iff_eq.mpr
      rw [he]
      simp
    exact List.contains_iff_mem.mp (tested.trans ok)
  · intro h
    have ok := tested.symm.trans (List.contains_iff_mem.mpr h)
    apply term_iff_valuations.mpr
    intro p pp
    by_cases big : primeBound < p
    · have hs : 2*k < p^2 := (show 2*k ≤ 2*bound by omega).trans_lt
          (square.trans_le (Nat.pow_le_pow_left (by omega) 2))
      have hv : k.centralBinom.factorization p ≤ 1 := Nat.factorization_choose_le_one hs
      rcases Nat.eq_zero_or_pos (k.centralBinom.factorization p) with zero | pos
      · exact ⟨0,by simp [zero]⟩
      · exact ⟨1,by omega⟩
    have member : p ∈ primes := List.mem_filter.mpr ⟨List.mem_range.mpr (by omega),decide_eq_true pp⟩
    have single := List.all_eq_true.mp ok _ (List.mem_map.mpr ⟨p,member,rfl⟩)
    rw [val p pp]
    exact ⟨_,beq_iff_eq.mp single⟩

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1200000 in
/-- The fourteen tabulated indices, including zero, are exactly the terms through 784. -/
theorem initial_classification (k : ℕ) (hk : k ≤ 784) :
    IsTerm k ↔ k ∈ ([0,1,2,4,7,11,21,22,28,37,42,52,69,784] : List ℕ) :=
  terms_in_range _ 784 10 40 (by decide) (by decide) (by decide +kernel) k hk

/-- Appending zero digits in base p preserves its central-binomial valuation. -/
theorem valuation_prime_mul (k p : ℕ) (hp : p.Prime) :
    (p*k).centralBinom.factorization p = k.centralBinom.factorization p := by
  have fac (t : ℕ) : (2*t).factorial.factorization p =
      t.centralBinom.factorization p + 2*t.factorial.factorization p := by
    have hc := Nat.choose_mul_factorial_mul_factorial (show t ≤ 2*t by omega)
    change (2*t).choose t * t.factorial * (2*t-t).factorial = _ at hc
    rw [show 2*t-t=t by omega] at hc
    change t.centralBinom * t.factorial * t.factorial = (2*t).factorial at hc
    rw [←hc, Nat.factorization_mul (Nat.mul_ne_zero (Nat.centralBinom_pos t).ne' t.factorial_ne_zero)
        t.factorial_ne_zero,Nat.factorization_mul (Nat.centralBinom_pos t).ne' t.factorial_ne_zero]
    simp [two_mul,add_assoc]
  have h := fac (p*k)
  have h2 := fac k
  rw [show 2*(p*k)=p*(2*k) by ring,Nat.factorization_factorial_mul hp,Nat.factorization_factorial_mul hp] at h
  omega

theorem valuation_prime_pow_mul (k p e : ℕ) (hp : p.Prime) :
    (p^e*k).centralBinom.factorization p = k.centralBinom.factorization p := by
  induction e with
  | zero => simp
  | succ e ih => rw [pow_succ', Nat.mul_assoc, valuation_prime_mul _ _ hp, ih]

end Bin304

namespace Bin304
open OMA.S_oeis_a304916

/-- Except at 786, a prime with exactly two carries exists throughout the
entire certified range. In particular three divides the divisor count there. -/
theorem certified_exact_two {k : ℕ} (lo : 784 < k) (hi : k ≤ 10^60) (ne : k ≠ 786) :
    ∃ p : ℕ, p.Prime ∧ k.centralBinom.factorization p = 2 := by
  by_cases h : k ≤ 1494800044
  · exact prefix_multiplicity_two lo h ne
  · exact high_multiplicity_two (by omega) hi

theorem certified_three_dvd {k : ℕ} (lo : 784 < k) (hi : k ≤ 10^60) (ne : k ≠ 786) :
    3 ∣ k.centralBinom.divisors.card := by
  obtain ⟨p,pp,hp⟩ := certified_exact_two lo hi ne
  simpa only [hp] using multiplicity_succ_dvd_card (Nat.centralBinom_pos k).ne' pp (by omega)

theorem certified_not_term {k : ℕ} (lo : 784 < k) (hi : k ≤ 10^60) : ¬ IsTerm k := by
  rintro ⟨j,h⟩
  by_cases he : k = 786
  · subst k
    have hd := five_dvd_card_786
    rw [h] at hd
    exact (by decide : ¬5∣2) ((by decide : Nat.Prime 5).dvd_of_dvd_pow hd)
  · have hd := certified_three_dvd lo hi he
    rw [h] at hd
    exact (by decide : ¬3∣2) ((by decide : Nat.Prime 3).dvd_of_dvd_pow hd)

/-- The fourteen displayed terms give the complete initial segment through 10^60. -/
theorem certified_classification {k : ℕ} (hk : k ≤ 10^60) :
    IsTerm k ↔ k ∈ ([0,1,2,4,7,11,21,22,28,37,42,52,69,784] : List ℕ) := by
  by_cases h : k ≤ 784
  · exact initial_classification k h
  · constructor
    · exact fun ht => (certified_not_term (by omega) hk ht).elim
    · intro hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      omega

/-- Every excluded positive index supplies an entire infinite geometric progression
of exclusions, obtained by appending base-p zeroes to the same prime witness. -/
theorem prime_ray_of_nonterm {k : ℕ} (h : ¬IsTerm k) :
    ∃ p : ℕ, p.Prime ∧ ∀ a : ℕ, ¬IsTerm (p^a*k) := by
  classical
  rw [term_iff_valuations] at h
  push Not at h
  obtain ⟨p,hp,hbad⟩ := h
  refine ⟨p,hp,?_⟩
  intro a ha
  obtain ⟨j,hj⟩ := term_iff_valuations.mp ha p hp
  rw [valuation_prime_pow_mul _ _ _ hp] at hj
  exact hbad j hj

end Bin304

namespace Bin304

open OMA.S_oeis_a304916 Finset
open scoped Classical

theorem binary_weight_valuation (k : ℕ) :
    k.centralBinom.factorization 2 = k.bitIndices.length := by
  have hbits (n : ℕ) : (Nat.digits 2 n).sum = n.bitIndices.length := by
    induction n using Nat.binaryRec with
    | zero => simp
    | bit b n ih =>
      cases b
      · rw [Nat.bit_false, Nat.bitIndices_two_mul, List.length_map]
        obtain rfl | hn := Nat.eq_zero_or_pos n
        · simp
        · simpa [Nat.digits_base_mul one_lt_two hn] using ih
      · rw [Nat.bit_true, Nat.bitIndices_two_mul_add_one]
        dsimp only
        rw [add_comm (2*n) 1,
          Nat.digits_add 2 one_lt_two 1 n one_lt_two (Or.inl one_ne_zero)]
        simp [ih, Nat.add_comm]
  rw [← hbits, Nat.factorization_def _ Nat.prime_two]
  obtain rfl | hk := Nat.eq_zero_or_pos k
  · simp
  have double : (Nat.digits 2 (k+k)).sum = (Nat.digits 2 k).sum := by
    rw [← two_mul, Nat.digits_base_mul one_lt_two hk]
    simp
  have h := sub_one_mul_padicValNat_choose_eq_sub_sum_digits' (p := 2) (k := k) (n := k)
  rw [double] at h
  simpa [Nat.centralBinom, two_mul] using h

theorem term_binary_weight {k : ℕ} (h : IsTerm k) :
    ∃ j : ℕ, k.bitIndices.length + 1 = 2 ^ j := by
  simpa only [binary_weight_valuation] using term_iff_valuations.mp h 2 Nat.prime_two

theorem term_count_le_weight_sum (m : ℕ) :
    ((range (2^m)).filter IsTerm).card ≤
      ∑ j ∈ range (Nat.log 2 (m+1)+1), m.choose (2^j-1) := by
  classical
  let J := range (Nat.log 2 (m+1)+1)
  let P (j : ℕ) := (range m).powersetCard (2^j-1)
  have inj : ((range (2^m)).filter IsTerm).card ≤ (J.biUnion P).card := by
    apply card_le_card_of_injOn Finset.equivBitIndices _ Finset.equivBitIndices.injective.injOn
    intro k hk
    obtain ⟨hl,ht⟩ := mem_filter.mp hk
    obtain ⟨j,hj⟩ := term_binary_weight ht
    have hsub : k.bitIndices.toFinset ⊆ range m := by
      intro i hi
      rw [mem_range]
      by_contra! h
      have hh := (Nat.pow_le_pow_right (by decide : 0 < 2) h).trans
        (Nat.two_pow_le_of_mem_bitIndices (List.mem_toFinset.mp hi))
      exact (mem_range.mp hl).not_ge hh
    have hc : k.bitIndices.toFinset.card = k.bitIndices.length :=
      List.toFinset_card_of_nodup Nat.bitIndices_nodup
    have hle := card_le_card hsub
    rw [hc,card_range] at hle
    apply mem_biUnion.mpr
    refine ⟨j,mem_range.mpr (Nat.lt_succ_of_le (Nat.le_log_of_pow_le one_lt_two (by omega))),?_⟩
    exact mem_powersetCard.mpr ⟨hsub, by change k.bitIndices.toFinset.card = 2^j-1; omega⟩
  exact inj.trans (card_biUnion_le.trans_eq (by simp [J,P,card_powersetCard]))

theorem term_count_le_middle (m : ℕ) :
    ((range (2^m)).filter IsTerm).card ≤ (Nat.log 2 (m+1)+1) * m.choose (m/2) := by
  apply (term_count_le_weight_sum m).trans
  calc
    _ ≤ ∑ _j ∈ range (Nat.log 2 (m+1)+1), m.choose (m/2) :=
      sum_le_sum (fun j _ => Nat.choose_le_middle _ _)
    _ = _ := by simp

end Bin304

namespace Bin304
open OMA.S_oeis_a304916 Finset Filter
open scoped Classical Topology

theorem central_square_bound (n : ℕ) : (n+1) * n.centralBinom^2 ≤ 16^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    apply (Nat.mul_le_mul_left_iff (by positivity : 0 < (n+1)^2)).mp
    have h : (n+2) * (2 * (2*n+1))^2 ≤ 16 * (n+1)^3 := by nlinarith
    calc
      _ = (n+2) * ((n+1) * (n+1).centralBinom)^2 := by ring
      _ = ((n+2) * (2*(2*n+1))^2) * n.centralBinom^2 := by
        rw [Nat.succ_mul_centralBinom_succ]
        ring
      _ ≤ (16 * (n+1)^3) * n.centralBinom^2 := Nat.mul_le_mul_right _ h
      _ = (16*(n+1)^2) * ((n+1)*n.centralBinom^2) := by ring
      _ ≤ (16*(n+1)^2) * 16^n := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [pow_succ]; ring

theorem middle_square_bound (m : ℕ) : (m/2+1) * (m.choose (m/2))^2 ≤ (2^m)^2 := by
  let n := m/2
  change (n+1) * (m.choose n)^2 ≤ (2^m)^2
  have hh : (2^(2*n))^2 = 16^n := by
    rw [pow_mul, ← pow_mul, Nat.mul_comm n 2, pow_mul]; norm_num
  rcases (show m=2*n ∨ m=2*n+1 by dsimp [n]; omega) with he | ho
  · rw [he,hh]
    exact central_square_bound n
  · have odd_bound : (2*n+1).choose n ≤ 2*n.centralBinom := by
      obtain h | h := Nat.eq_zero_or_pos n
      · rw [h]; decide
      · rw [Nat.choose_succ_left _ _ h]
        have hi := Nat.choose_le_centralBinom (n-1) n
        change _ + n.centralBinom ≤ _
        omega
    rw [ho,pow_succ]
    calc
      _ ≤ (n+1) * (2*n.centralBinom)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left odd_bound 2)
      _ = 4*((n+1)*n.centralBinom^2) := by ring
      _ ≤ 4*16^n := Nat.mul_le_mul_left _ (central_square_bound n)
      _ = _ := by rw [← hh]; ring

theorem count_squared_le (N : ℕ) (hN : 0<N) :
    let r := Nat.log 2 (Nat.log 2 N + 1 + 1)
    (((range N).filter IsTerm).card)^2 * 2^r ≤ (32*r^2)*N^2 := by
  let m := Nat.log 2 N + 1
  let r := Nat.log 2 (m+1)
  let F := ((range N).filter IsTerm).card
  change F^2 * 2^r ≤ (32*r^2)*N^2
  have hF : F ≤ (r+1)*m.choose (m/2) := by
    apply le_trans _ (term_count_le_middle m)
    apply card_le_card
    exact filter_subset_filter _ (range_mono (Nat.lt_pow_succ_log_self one_lt_two N).le)
  have hpow : 2^m ≤ 2*N := by
    dsimp only [m]
    rw [pow_succ, mul_comm]
    exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self _ hN.ne')
  have hr : 1 ≤ r :=
    Nat.le_log_of_pow_le one_lt_two (by dsimp only [m]; omega)
  have hrpow : 2^r ≤ 2*(m/2+1) :=
    (Nat.pow_log_le_self 2 (Nat.succ_ne_zero m)).trans (by omega)
  calc
    _ ≤ ((2*r)*m.choose (m/2))^2 * (2*(m/2+1)) := by
      gcongr
      exact hF.trans (Nat.mul_le_mul_right _ (by omega))
    _ = 8*r^2*((m/2+1)* (m.choose (m/2))^2) := by ring
    _ ≤ 8*r^2*(2^m)^2 := Nat.mul_le_mul_left _ (middle_square_bound m)
    _ ≤ 8*r^2*(2*N)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpow _)
    _ = _ := by ring

theorem term_density_zero :
    Tendsto (fun N : ℕ => (((range N).filter IsTerm).card : ℝ) / N) atTop (𝓝 0) := by
  let F (N : ℕ) : ℝ := ((range N).filter IsTerm).card / (N : ℝ)
  let r (N : ℕ) := Nat.log 2 (Nat.log 2 N + 1 + 1)
  have hr : Tendsto r atTop atTop := by
    apply tendsto_atTop.2
    intro j
    filter_upwards [eventually_ge_atTop (2^(2^j) : ℕ)] with N hN
    apply Nat.le_log_of_pow_le one_lt_two
    have := Nat.le_log_of_pow_le one_lt_two hN
    omega
  have hg := (tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : 1 < (2:ℝ))).comp hr
  have hu : Tendsto (fun N => 32 * ((r N : ℝ)^2 / 2^(r N))) atTop (𝓝 0) := by
    simpa using hg.const_mul 32
  have hF : Tendsto (fun N => (F N)^2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun i => sq_nonneg _) _ hu
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have h : (((range N).filter IsTerm).card : ℝ)^2 * 2^(r N) ≤
      (32*(r N : ℝ)^2)*(N:ℝ)^2 := by exact_mod_cast count_squared_le N hN
    have nh : (0:ℝ) < N := by exact_mod_cast hN
    dsimp only [F]
    rw [div_pow, ← mul_div_assoc]
    apply (div_le_div_iff₀ (sq_pos_of_pos nh) (by positivity)).mpr
    exact h
  have hn (N : ℕ) : 0 ≤ F N := by dsimp [F]; positivity
  simpa [Real.sqrt_sq (hn _), Function.comp_def, F] using hF.sqrt

end Bin304

namespace Bin304
open Finset Real
open scoped ArithmeticFunction.vonMangoldt

/-- Summing the von Mangoldt divisor identity over the first n integers gives the logarithm of n!. -/
theorem log_factorial_weight_sum (M : ℕ) {n : ℕ} (hn : n ≤ M) :
    log (n.factorial : ℝ) = ∑ d ∈ Ioc 0 M, (n/d : ℕ) * Λ d := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs : ((Ioc 0 M).filter fun d => d ∣ n+1) = (n+1).divisors := by
      ext d
      simp only [mem_filter,mem_Ioc,Nat.mem_divisors]
      exact ⟨fun h => ⟨h.2,by omega⟩, fun h => ⟨⟨Nat.pos_of_dvd_of_pos h.1 (by omega),
        (Nat.le_of_dvd (by omega) h.1).trans hn⟩,h.1⟩⟩
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity),
      ih (by omega)]
    simp_rw [Nat.succ_div, Nat.cast_add, add_mul, Finset.sum_add_distrib]
    suffices log (n+1 : ℕ) = ∑ d ∈ Ioc 0 M, ((if d ∣ n+1 then 1 else 0 : ℕ):ℝ) * Λ d by
      push_cast at *
      linarith
    rw [← ArithmeticFunction.vonMangoldt_sum, ← hs, sum_filter]
    apply sum_congr rfl
    intro d _
    split_ifs <;> simp

/-- The floor weight at q equals q + q/30 − q/2 − q/3 − q/5. It takes only the values zero and one, and equals one for q from 1 through 5. -/
theorem cheb_weight_sandwich (t : ℕ) :
    (Real.log (Nat.factorial (30*t) : ℝ) + Real.log (Nat.factorial t : ℝ) - Real.log (Nat.factorial (15*t) : ℝ) - Real.log (Nat.factorial (10*t) : ℝ) - Real.log (Nat.factorial (6*t) : ℝ)) ≤ Chebyshev.psi (30*t : ℕ) ∧
      Chebyshev.psi (30*t : ℕ) ≤ (Real.log (Nat.factorial (30*t) : ℝ) + Real.log (Nat.factorial t : ℝ) - Real.log (Nat.factorial (15*t) : ℝ) - Real.log (Nat.factorial (10*t) : ℝ) - Real.log (Nat.factorial (6*t) : ℝ)) + Chebyshev.psi (5*t : ℕ) := by
  let I := Ioc 0 (30*t)
  let v (d : ℕ) := ((30*t/d : ℕ):ℝ) + (t/d : ℕ)
    - (15*t/d : ℕ) - (10*t/d : ℕ) - (6*t/d : ℕ)
  have hv (d : ℕ) : 0 ≤ v d ∧ v d ≤ 1 ∧ (5*t < d → d ≤ 30*t → v d = 1) := by
    let q := 30*t/d
    have floor_mul (a b : ℕ) (hab : a*b=30) (hb : 0 < b) : q/b = a*t/d := by
      dsimp only [q]
      rw [Nat.div_div_eq_div_mul, ← hab, show a*b*t=(a*t)*b by ring, Nat.mul_div_mul_right _ _ hb]
    have q1 := floor_mul 1 30 rfl (by decide)
    have q2 := floor_mul 15 2 rfl (by decide)
    have q3 := floor_mul 10 3 rfl (by decide)
    have q5 := floor_mul 6 5 rfl (by decide)
    rw [one_mul] at q1
    have hle : q/2+q/3+q/5 ≤ q+q/30 := by omega
    have hge : q+q/30 ≤ q/2+q/3+q/5+1 := by omega
    rw [q1,q2,q3,q5] at hle hge
    dsimp only [q] at hle hge
    have lo : (((15*t/d : ℕ):ℝ)+(10*t/d : ℕ)+(6*t/d : ℕ)) ≤ (30*t/d : ℕ)+(t/d : ℕ) := by exact_mod_cast hle
    have hi : (((30*t/d : ℕ):ℝ)+(t/d : ℕ)) ≤ (15*t/d : ℕ)+(10*t/d : ℕ)+(6*t/d : ℕ)+1 := by exact_mod_cast hge
    refine ⟨by dsimp only [v]; linarith, by dsimp only [v]; linarith, ?_⟩
    intro hd hl
    have hq0 : 0 < q := Nat.div_pos hl (by omega)
    have hq6 : q < 6 := (Nat.div_lt_iff_lt_mul (by omega : 0<d)).mpr (by omega)
    have hq : q+q/30=q/2+q/3+q/5+1 := by interval_cases q <;> decide
    rw [q1,q2,q3,q5] at hq
    dsimp only [q] at hq
    have : (((30*t/d : ℕ):ℝ)+(t/d : ℕ)) = (15*t/d : ℕ)+(10*t/d : ℕ)+(6*t/d : ℕ)+1 := by exact_mod_cast hq
    dsimp only [v]
    linarith
  have hw : (Real.log (Nat.factorial (30*t) : ℝ) + Real.log (Nat.factorial t : ℝ) - Real.log (Nat.factorial (15*t) : ℝ) - Real.log (Nat.factorial (10*t) : ℝ) - Real.log (Nat.factorial (6*t) : ℝ)) = ∑ d ∈ I, v d * Λ d := by
    simp only [log_factorial_weight_sum (30*t) (show 30*t ≤ 30*t by omega),
      log_factorial_weight_sum (30*t) (show t ≤ 30*t by omega),
      log_factorial_weight_sum (30*t) (show 15*t ≤ 30*t by omega),
      log_factorial_weight_sum (30*t) (show 10*t ≤ 30*t by omega),
      log_factorial_weight_sum (30*t) (show 6*t ≤ 30*t by omega),
      v,I,sub_mul,add_mul,sum_add_distrib,sum_sub_distrib]
  have h5 : (I.filter fun d => d ≤ 5*t) = Ioc 0 (5*t) := by ext d; simp [I]; omega
  rw [hw]
  simp only [Chebyshev.psi,Nat.floor_natCast]
  constructor
  · exact sum_le_sum fun d _ => by simpa using
      (mul_le_mul_of_nonneg_right (hv d).2.1 (ArithmeticFunction.vonMangoldt_nonneg (n:=d)))
  · rw [← h5, sum_filter, ← sum_add_distrib]
    apply sum_le_sum
    intro d hd
    by_cases h : d ≤ 5*t
    · simp only [if_pos h,le_add_iff_nonneg_left]
      exact mul_nonneg (hv d).1 ArithmeticFunction.vonMangoldt_nonneg
    · simp [h,(hv d).2.2 (by omega) (mem_Ioc.mp hd).2]

end Bin304

namespace Bin304
open Real

/-- Explicit bounds on the logarithmic remainder in Stirling’s formula. -/
theorem log_factorial_elementary {n : ℕ} (hn : 0 < n) :
    let main := (n:ℝ)*(log n - 1)
    main ≤ log (n.factorial : ℝ) ∧ log (n.factorial : ℝ) ≤ main + log n + 2 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have h1 := Stirling.log_stirlingSeq_bounded_by_constant k
  have h2 := Stirling.log_stirlingSeq'_antitone (show 0 ≤ k by omega)
  change log (Stirling.stirlingSeq (k+1)) ≤ log (Stirling.stirlingSeq 1) at h2
  rw [Stirling.stirlingSeq_one,Real.log_div (by positivity) (by positivity),
    Real.log_exp,Real.log_sqrt (by positivity)] at h2
  have h3 := Stirling.log_stirlingSeq_formula (k+1)
  rw [Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
    Real.log_exp] at h3
  have hp : 0 ≤ log ((k+1 : ℕ):ℝ) := Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))
  dsimp only
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- The main coefficient of the five factorials is 14 log 2 + 9 log 3 + 5 log 5. -/
theorem cheb_weight_linear {m : ℕ} (hm : 2^100 ≤ m) :
    (138/5:ℝ)*m ≤ (Real.log (Nat.factorial (30*m) : ℝ) + Real.log (Nat.factorial m : ℝ) - Real.log (Nat.factorial (15*m) : ℝ) - Real.log (Nat.factorial (10*m) : ℝ) - Real.log (Nat.factorial (6*m) : ℝ)) ∧ (Real.log (Nat.factorial (30*m) : ℝ) + Real.log (Nat.factorial m : ℝ) - Real.log (Nat.factorial (15*m) : ℝ) - Real.log (Nat.factorial (10*m) : ℝ) - Real.log (Nat.factorial (6*m) : ℝ)) ≤ (277/10:ℝ)*m := by
  let f (a : ℕ) := (a:ℝ)*m*(log m - 1)+(a:ℝ)*m*log a
  have hmb : (2^100 : ℝ) ≤ m := by exact_mod_cast hm
  have hmR : (0:ℝ) < m := by linarith
  have hsm : 4096 ≤ sqrt (m : ℝ) := Real.le_sqrt_of_sq_le (by linarith)
  have hslog : log (m:ℝ) ≤ 2*sqrt (m:ℝ) := by
    simpa [Real.sqrt_eq_rpow, div_eq_mul_inv, mul_comm] using
      (Real.log_le_rpow_div hmR.le (show (0:ℝ)<1/2 by norm_num))
  have fact (a : ℕ) (ha : 1≤a) (ha' : a≤30) :
      f a ≤ log ((a*m).factorial : ℝ) ∧ log ((a*m).factorial : ℝ) ≤ f a + m/1000 := by
    have h := log_factorial_elementary (n:=a*m) (Nat.mul_pos ha (by omega))
    have haux : ((a*m : ℕ):ℝ)*(log (a*m : ℕ)-1) = f a := by
      rw [Nat.cast_mul, Real.log_mul (by positivity) hmR.ne']
      dsimp only [f]
      ring
    rw [haux] at h
    refine ⟨h.1,h.2.trans ?_⟩
    rw [Nat.cast_mul, Real.log_mul (by positivity) hmR.ne']
    have haR : (a:ℝ) ≤ 30 := by exact_mod_cast ha'
    have halog := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ)<a)
    nlinarith [Real.sq_sqrt hmR.le, mul_nonneg (sub_nonneg.mpr hsm) (Real.sqrt_nonneg (m : ℝ)),
      mul_nonneg (sub_nonneg.mpr hsm) (show (0:ℝ) ≤ 2 by norm_num)]
  have h30 := fact 30 (by decide) (by decide)
  have h15 := fact 15 (by decide) (by decide)
  have h10 := fact 10 (by decide) (by decide)
  have h6 := fact 6 (by decide) (by decide)
  have h1 := fact 1 (by decide) (by decide)
  rw [one_mul] at h1
  let c := 14 * log 2 + 9*log 3 + 5*log 5
  have cval : f 30 + f 1 - f 15 - f 10 - f 6 = c*m := by
    dsimp [f,c]
    norm_num only [Nat.cast_ofNat,Nat.cast_one,log_one]
    rw [show (30:ℝ)=2*(3*5) by norm_num, show (15:ℝ)=3*5 by norm_num,
      show (10:ℝ)=2*5 by norm_num,show (6:ℝ)=2*3 by norm_num]
    simp only [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3*5 : ℝ) ≠ 0),
      Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by norm_num : (5:ℝ) ≠ 0),
      Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (5:ℝ) ≠ 0),
      Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (3:ℝ) ≠ 0)]
    ring
  have h5l := Real.log_le_log (by positivity : (0:ℝ)<2^58) (by norm_num : (2:ℝ)^58 ≤ 5^25)
  have h5u := Real.log_le_log (by positivity : (0:ℝ)<5^3) (by norm_num : (5:ℝ)^3 ≤ 2^7)
  rw [Real.log_pow, Real.log_pow] at h5l h5u
  norm_num1 at h5l h5u
  have cl : 27.62 ≤ c := by dsimp [c]; linarith [Real.log_two_gt_d9,Real.log_three_gt_d9]
  have cu : c ≤ 27.69 := by dsimp [c]; linarith [Real.log_two_lt_d9,Real.log_three_lt_d9]
  constructor <;> linarith only [cval,h30.1,h30.2,h15.1,h15.2,h10.1,h10.2,h6.1,h6.2,h1.1,h1.2,hmR,mul_le_mul_of_nonneg_right cl hmR.le,mul_le_mul_of_nonneg_right cu hmR.le]

end Bin304

namespace Bin304
open Finset Real
open scoped ArithmeticFunction.vonMangoldt

/-- At 32400t, four iterations of the factorial bound leave a tail of length 25t. -/
theorem cheb_two_scales (t : ℕ) (ht : 2^100 ≤ t) :
    (6000:ℝ)*t + Chebyshev.psi (32400*t : ℕ) ≤ Chebyshev.psi (45720*t : ℕ) := by
  have lower {m : ℕ} (hm : 2^100 ≤ m) :=
    (cheb_weight_linear hm).1.trans (cheb_weight_sandwich m).1
  have upper {m : ℕ} (hm : 2^100 ≤ m) :=
    (cheb_weight_sandwich m).2.trans (add_le_add_left (cheb_weight_linear hm).2 _)
  have hL := lower (m:=1524*t) (by omega)
  have hU1 := upper (m:=1080*t) (by omega)
  have hU2 := upper (m:=180*t) (by omega)
  have hU3 := upper (m:=30*t) (by omega)
  have hU4 := upper (m:=5*t) (by omega)
  have htail := Chebyshev.psi_le_const_mul_self (x:=((25*t : ℕ):ℝ)) (by positivity)
  have hl4 : log 4 ≤ 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num1
    linarith [Real.log_two_lt_d9]
  have htail' : Chebyshev.psi (25*t : ℕ) ≤ 6 * (25*t : ℕ) := htail.trans
    (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  push_cast at hL hU1 hU2 hU3 hU4 htail' ⊢
  norm_num [← mul_assoc] at hL hU1 hU2 hU3 hU4 htail' ⊢
  linarith only [hL,hU1,hU2,hU3,hU4,htail',show 0 ≤ (t:ℝ) by positivity]

/-- The four-scale estimate gives the required von Mangoldt mass in the square-root interval. -/
theorem sqrt_interval_mangoldt_mass_strong {n : ℕ} (hn : 2^250 ≤ n) :
    (5/27:ℝ)*Real.sqrt n ≤ ∑ d ∈ Ioc n.sqrt (2*n).sqrt, Λ d := by
  let a := n.sqrt
  let b := (2*n).sqrt
  let t := a/32400+1
  have ha : 2^125 ≤ a := Nat.le_sqrt'.mpr (by rw [← pow_mul]; exact hn)
  clear hn
  have ht : 2^100 ≤ t := Nat.le_succ_of_le ((Nat.le_div_iff_mul_le (by decide : 0<32400)).mpr
    ((by decide : 2^100 * 32400 ≤ 2^125).trans ha))
  have haU : a+1 ≤ 32400*t := by dsimp only [t]; omega
  have hV : 900*(45720*t) ≤ 1271*a := by
    have hab : 42000000 ≤ a := le_trans (by decide : 42000000 ≤ 2^125) ha
    have div_le : 32400*(a/32400) ≤ a := Nat.mul_div_le _ _
    calc
      _ = 1270*(32400*(a/32400)) + 41148000 := by dsimp only [t]; ring
      _ ≤ 1270*a + 41148000 := Nat.add_le_add_right (Nat.mul_le_mul_left _ div_le) _
      _ ≤ 1270*a + a := Nat.add_le_add_left ((by decide : 41148000 ≤ 42000000).trans hab) _
      _ = _ := by ring
  have hVb : 45720*t ≤ b := by
    apply Nat.le_sqrt'.mpr
    have hsq := Nat.pow_le_pow_left hV 2
    have ha2 : a^2 ≤ n := Nat.sqrt_le' _
    have hh : 810000*(45720*t)^2 ≤ 1615441*n := calc
      _ = (900*(45720*t))^2 := by ring
      _ ≤ (1271*a)^2 := hsq
      _ = 1615441*a^2 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ ha2
    apply (Nat.mul_le_mul_left_iff (by decide : 0<810000)).mp
    calc
      _ ≤ 1615441*n := hh
      _ ≤ 1620000*n := Nat.mul_le_mul_right _ (by decide)
      _ = _ := by ring
  have hmonoU := Chebyshev.psi_mono (by exact_mod_cast (Nat.le_succ a).trans haU :
    (a:ℝ) ≤ (32400*t:ℕ))
  have hmonoL := Chebyshev.psi_mono (by exact_mod_cast hVb : ((45720*t : ℕ):ℝ) ≤ b)
  have hV2 : Real.sqrt n ≤ (32400*t:ℕ) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    exact_mod_cast (Nat.lt_succ_sqrt' n).le.trans (Nat.pow_le_pow_left haU 2)
  have hsum : Chebyshev.psi a + (∑ d ∈ Ioc a b, Λ d) = Chebyshev.psi b := by
    simp only [Chebyshev.psi,Nat.floor_natCast]
    exact sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.sqrt_le_sqrt (by omega : n ≤ 2*n))
  have hLU := cheb_two_scales t ht
  push_cast at hmonoU hmonoL hV2 hLU
  change (5/27:ℝ)*Real.sqrt n ≤ ∑ d ∈ Ioc a b, Λ d
  linarith only [hLU,hmonoU,hmonoL,hV2,hsum,show 0 ≤ (t:ℝ) by positivity]

/-- A convenient decimal fraction implied by the stronger five-twenty-sevenths bound. -/
theorem sqrt_interval_mangoldt_mass_nine_fiftieths {n : ℕ} (hn : 2^250 ≤ n) :
    (9/50:ℝ)*Real.sqrt n ≤ ∑ d ∈ Ioc n.sqrt (2*n).sqrt, Λ d :=
  (mul_le_mul_of_nonneg_right (by norm_num : (9/50:ℝ) ≤ 5/27) (Real.sqrt_nonneg _)).trans
    (sqrt_interval_mangoldt_mass_strong hn)

end Bin304

namespace Bin304

/-- Both Kummer positions contribute in the upper square-root interval exactly
when the units-position remainder lies in the upper half. -/
theorem sqrt_interval_exact {n p : ℕ} (hp : p.Prime)
    (hl : n < p^2) (hu : p^2 ≤ 2*n) (hc : p ≤ n%p+n%p) :
    n.centralBinom.factorization p = 2 := by
  have hcub : 2*n < p^3 := by
    have hy := Nat.mul_le_mul_right (p^2) hp.two_le
    rw [pow_succ, mul_comm (p^2) p]
    omega
  change ((2*n).choose n).factorization p = 2
  rw [two_mul, Nat.factorization_choose' hp (b:=3)
    ((Nat.log_lt_iff_lt_pow hp.one_lt (by have := hp.pos; omega)).mpr (by omega))]
  rw [show Finset.Ico 1 3 = {1,2} by decide, Finset.filter_eq_self.mpr ?_]
  · decide
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl|rfl
    · simpa using hc
    · simpa only [Nat.mod_eq_of_lt hl, ← two_mul] using hu

theorem reciprocal_sin_nonneg {n p : ℕ} (hp : 0<p) (hlo : 2*(n%p) ≤ p) :
    0 ≤ Real.sin (2*Real.pi*(n:ℝ)/p) := by
  have hpR : 0<(p:ℝ) := by exact_mod_cast hp
  have hid : ((n%p:ℕ):ℝ)+(p:ℝ)*((n/p:ℕ):ℝ)=n := by
    exact_mod_cast Nat.mod_add_div n p
  have harg : 2*Real.pi*(n:ℝ)/p =
      2*Real.pi*((n%p:ℕ):ℝ)/p + ((n/p:ℕ):ℝ)*(2*Real.pi) := by
    field_simp
    linarith
  rw [harg, Real.sin_add_nat_mul_two_pi]
  apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
  apply (div_le_iff₀ hpR).mpr
  have hloR : 2*((n%p:ℕ):ℝ) ≤ p := by exact_mod_cast hlo
  nlinarith [mul_le_mul_of_nonneg_left hloR Real.pi_pos.le]

/-- A two-frequency detector on the Granville–Ramaré square-root interval.
The finitely supported composite error accounts precisely for the higher
prime powers in the von Mangoldt weights. -/
theorem reciprocal_detector (n : ℕ) :
    let I := Finset.Ioc n.sqrt (2*n).sqrt
    let w := ArithmeticFunction.vonMangoldt
    let S := fun (h : ℝ) => ∑ d ∈ I, (w d : ℂ) *
      Complex.exp (((h*(2*Real.pi*n/d) : ℝ) : ℂ) * Complex.I)
    (∀ p ∈ I, Nat.Prime p → n.centralBinom.factorization p ≠ 2) →
    ∑ d ∈ I, w d ≤ 2*‖S 1‖ + ‖S 2‖ +
      4 * ∑ d ∈ I with ¬d.Prime, w d := by
  intro I w S hn
  let t (d : ℕ) := 2*Real.pi*n/d
  have hl (d : ℕ) (hd : d ∈ I) (hp : d.Prime) :
      0 ≤ Real.sin (t d) := by
    apply reciprocal_sin_nonneg hp.pos
    by_contra! h
    apply hn d hd hp
    obtain ⟨h1,h2⟩ := Finset.mem_Ioc.mp hd
    exact sqrt_interval_exact hp (Nat.sqrt_lt'.mp h1) (Nat.le_sqrt'.mp h2) (by omega)
  have pt (d : ℕ) (hd : d ∈ I) : w d ≤
      2*(w d*Real.sin (t d)) + w d*Real.cos (2*(t d)) +
      (if ¬d.Prime then 4*w d else 0) := by
    have hw : 0 ≤ w d := ArithmeticFunction.vonMangoldt_nonneg
    by_cases hp : d.Prime
    · simp only [hp,not_true_eq_false,if_false,add_zero,Real.cos_two_mul_eq_one_sub]
      have hs := hl d hd hp
      have hs' := Real.sin_le_one (t d)
      have hk := mul_nonneg hs (sub_nonneg.mpr hs')
      nlinarith [mul_nonneg hw hk]
    · simp only [hp, not_false_eq_true, if_true]
      have hs := Real.neg_one_le_sin (t d)
      have hc := Real.neg_one_le_cos (2*(t d))
      nlinarith [mul_le_mul_of_nonneg_left hs hw, mul_le_mul_of_nonneg_left hc hw]
  have him : (S 1).im = ∑ d ∈ I, w d*Real.sin (t d) := by
    simp only [S, Complex.im_sum, one_mul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, Complex.exp_ofReal_mul_I_im]
    rfl
  have hre : (S 2).re = ∑ d ∈ I, w d*Real.cos (2*(t d)) := by
    simp only [S, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]
    rfl
  calc
    ∑ d ∈ I, w d ≤ _ := Finset.sum_le_sum pt
    _ = 2*(S 1).im + (S 2).re + 4*∑ d ∈ I with ¬ d.Prime, w d := by
      rw [him,hre,Finset.sum_add_distrib,Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum]
      congr 1
      rw [Finset.sum_filter]
    _ ≤ _ := by linarith [Complex.im_le_norm (S 1), Complex.re_le_norm (S 2)]

/-- A direct estimate for the contamination from prime powers with exponent
at least two. The estimate uses the elementary Chebyshev bound in Mathlib. -/
theorem sqrt_interval_composite_mass_large {n : ℕ} (hn : 2^160 ≤ n) :
    4 * (∑ d ∈ Finset.Ioc n.sqrt (2*n).sqrt with ¬d.Prime,
      ArithmeticFunction.vonMangoldt d) ≤ (1/1000000:ℝ)*Real.sqrt n := by
  let b : ℕ := (2*n).sqrt
  have hb : 2^80 ≤ b := Nat.le_sqrt'.mpr (by norm_num; omega)
  have hbR : (2:ℝ)^80 ≤ b := by exact_mod_cast hb
  have hbpos : 0<(b:ℝ) := by linarith
  have hI : (Finset.Ioc n.sqrt b).filter (fun d => ¬d.Prime) ⊆
      (Finset.Ioc 0 b).filter (fun d => ¬d.Prime) := by
    intro d hd
    simp only [Finset.mem_filter,Finset.mem_Ioc] at hd ⊢
    exact ⟨⟨(Nat.zero_le _).trans_lt hd.1.1, hd.1.2⟩, hd.2⟩
  have hmass :
      ∑ d ∈ Finset.Ioc n.sqrt b with ¬d.Prime, ArithmeticFunction.vonMangoldt d ≤
      2*(Real.sqrt b)*Real.log b := by
    calc
      _ ≤ ∑ d ∈ Finset.Ioc 0 b with ¬d.Prime, ArithmeticFunction.vonMangoldt d :=
        Finset.sum_le_sum_of_subset_of_nonneg hI (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
      _ = Chebyshev.psi b - Chebyshev.theta b := by
        rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast]
      _ ≤ _ := Chebyshev.psi_sub_theta_le (by linarith)
  have hs : (1099511627776:ℝ) ≤ Real.sqrt b := (Real.le_sqrt (by norm_num) hbpos.le).mpr (by norm_num at hbR ⊢; exact hbR)
  have hq : 0 < Real.sqrt b/1099511627776 := by positivity
  have hlog : Real.log b ≤ 80*(Real.sqrt b/1099511627776) := by
    have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    have hlogq := Real.log_le_sub_one_of_pos hq
    rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt hbpos.le,
      show (1099511627776:ℝ)=2^40 by norm_num, Real.log_pow] at hlogq
    linarith
  have hb' : (b:ℝ) ≤ 2*Real.sqrt n := by
    have hsq := Nat.sqrt_le' (2*n)
    change b^2 ≤ 2*n at hsq
    have hsqR : (b:ℝ)^2 ≤ 2*(n:ℝ) := by exact_mod_cast hsq
    nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ n), Real.sqrt_nonneg (n:ℝ),
      sq_nonneg ((b:ℝ)-Real.sqrt n)]
  have hprod := mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg (b:ℝ))
  change 4*(∑ d ∈ Finset.Ioc n.sqrt b with ¬d.Prime, ArithmeticFunction.vonMangoldt d) ≤ _
  nlinarith [Real.sq_sqrt hbpos.le]

/-- Only the square-root-interval Mangoldt mass and two reciprocal phases are
needed. All remaining bounds hold for every index at least `2^160`. -/
theorem exact_two_of_frequency_bounds {n : ℕ} (hn : 2^160 ≤ n) :
    let I := Finset.Ioc n.sqrt (2*n).sqrt
    let w := ArithmeticFunction.vonMangoldt
    let S := fun (h : ℝ) => ∑ d ∈ I, (w d : ℂ) *
      Complex.exp (((h*(2*Real.pi*n/d) : ℝ) : ℂ) * Complex.I)
    (5/27:ℝ)*Real.sqrt n ≤ ∑ d ∈ I, w d →
    ‖S 1‖ ≤ (3/50:ℝ)*Real.sqrt n → ‖S 2‖ ≤ (3/50:ℝ)*Real.sqrt n →
    ∃ p ∈ I, Nat.Prime p ∧ n.centralBinom.factorization p = 2 := by
  intro I w S hm h1 h2
  by_contra! h
  have hd := reciprocal_detector n h
  have he := sqrt_interval_composite_mass_large hn
  change (∑ d ∈ I, w d) ≤ 2*‖S 1‖ + ‖S 2‖ + 4*(∑ d ∈ I with ¬d.Prime, w d) at hd
  change 4*(∑ d ∈ I with ¬d.Prime, w d) ≤ _ at he
  have hn' : 0 < n := (by positivity : (0:ℕ)<2^160).trans_le hn
  linarith [Real.sqrt_pos.mpr (show (0:ℝ)<n by exact_mod_cast hn')]

end Bin304

namespace Bin304

/-- The original Granville–Ramaré estimate with exponent 23/48 gives the
two-frequency bound for every real argument from 2^1617 onwards. -/
theorem published_frequency_cutoff_1617 {x : ℝ} (hx : 2^1617 ≤ x) :
    (16/5:ℝ)*x^(23/48:ℝ)*(Real.log (256*x))^(11/4:ℝ) ≤ (3/50:ℝ)*Real.sqrt x := by
  have hx0 : 0<x := (by positivity : (0:ℝ)<2^1617).trans_le hx
  have hL := Real.log_le_log (by positivity) hx
  rw [Real.log_pow] at hL
  norm_num at hL
  have hl2 := Real.log_two_gt_d9
  have hu2 := Real.log_two_lt_d9
  let t := Real.log (256*x)
  have ht : t=8*Real.log 2 + Real.log x := by
    dsimp only [t]
    rw [Real.log_mul (by norm_num) hx0.ne', show (256:ℝ)=2^8 by norm_num, Real.log_pow]
    norm_num
  have ht0 : 0<t := by linarith
  have htup := Real.log_le_sub_one_of_pos (div_pos ht0 (by norm_num : (0:ℝ)<1024))
  rw [Real.log_div ht0.ne' (by norm_num),show (1024:ℝ)=2^10 by norm_num,Real.log_pow] at htup
  have hc := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<(160/3)/64)
  rw [Real.log_div (by norm_num) (by norm_num),show (64:ℝ)=2^6 by norm_num, Real.log_pow] at hc
  rw [show (3/50:ℝ)*Real.sqrt x = Real.sqrt x/(50/3) by ring, le_div_iff₀ (by norm_num : (0:ℝ)<50/3)]
  change (16/5:ℝ)*x^(23/48:ℝ)*t^(11/4:ℝ)*(50/3) ≤ Real.sqrt x
  rw [show (16/5:ℝ)*x^(23/48:ℝ)*t^(11/4:ℝ)*(50/3)=(160/3:ℝ)*x^(23/48:ℝ)*t^(11/4:ℝ) by ring]
  apply (Real.log_le_log_iff (by positivity) (Real.sqrt_pos.mpr hx0)).mp
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hx0, Real.log_rpow ht0, Real.log_sqrt hx0.le]
  norm_num at hc htup ⊢
  linarith

end Bin304

namespace OMA.R_oeis_a304916_R2
open Bin304 OMA.S_oeis_a304916

/-- Finite part of the large-prime-square computation. Only indices with
Mersenne binary digit weight remain after the independent finite certificate. -/
def H1 : Prop :=
  ∀ k : ℕ, 10^60 < k → k < 2^1617 → (∃ j : ℕ, k.bitIndices.length+1 = 2^j) →
    ∃ p : ℕ, p.Prime ∧ k ≤ 5*p^2 ∧ p^2 ∣ k.centralBinom

/-- Granville and Ramaré, printed p. 28 after Lemma 7.2: the two specializations
x=k and x=2k of their explicit reciprocal von Mangoldt sum estimate. -/
def H2 : Prop :=
  ∀ k : ℕ, 2^1617 ≤ k → (∃ j : ℕ, k.bitIndices.length+1 = 2^j) →
    let I := Finset.Ioc k.sqrt (2*k).sqrt
    let S := fun (h : ℝ) => ∑ d ∈ I, (ArithmeticFunction.vonMangoldt d : ℂ) *
      Complex.exp (((h*(2*Real.pi*k/d) : ℝ) : ℂ) * Complex.I)
    let upper := (16/5:ℝ)*(k:ℝ)^(23/48:ℝ)*(Real.log (256*k))^(11/4:ℝ)
    ‖S 1‖ ≤ upper ∧ ‖S 2‖ ≤ upper

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a304916.main := by
  intro hm ha k hk ht
  by_cases small : k ≤ 10^60
  · exact certified_not_term hk small ht
  have bw := term_binary_weight ht
  by_cases mid : k < 2^1617
  · exact of_granville_ramare (le_trans (by decide : 2082 ≤ 10^60) (by omega))
      (hm k (by omega) mid bw) ht
  · have big : 2^1617 ≤ k := Nat.le_of_not_gt mid
    have lower {a b : ℕ} (h : a ≤ b) (hb : 2^b ≤ k) : 2^a ≤ k :=
      (Nat.pow_le_pow_right (by decide : 0 < 2) h).trans hb
    have h250 := lower (by decide : 250 ≤ 1617) big
    have h160 := lower (by decide : 160 ≤ 250) h250
    have castbig : (2:ℝ)^1617 ≤ k := by exact_mod_cast big
    have hcut := published_frequency_cutoff_1617 castbig
    obtain ⟨h1,h2⟩ := ha k big bw
    obtain ⟨p,_,pp,he⟩ := exact_two_of_frequency_bounds h160 (sqrt_interval_mangoldt_mass_strong h250)
      (h1.trans hcut) (h2.trans hcut)
    obtain ⟨j,h⟩ := term_iff_valuations.mp ht p pp
    rw [he] at h
    have hd : 3 ∣ 2^j := h ▸ dvd_refl 3
    exact (by decide : ¬3∣2) ((by decide : Nat.Prime 3).dvd_of_dvd_pow hd)

end OMA.R_oeis_a304916_R2
