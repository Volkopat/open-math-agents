import OMAReductions.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1_H4_R1
import Mathlib
/-! Split on the fourth prime above 17 in the abundancy-index bound. -/
namespace OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1_H4_R1_H1_R1

def H1 : Prop := ∀ n : ℕ, Odd n → n.Abundant → n.primeFactors.card ≤ 5 → 45 ∣ n → 17 ∣ n →
    (∀ r ∈ n.primeFactors, r ≠ 3 → r ≠ 5 → 17 ≤ r) → ∀ q : ℕ, q.Prime → q ∣ n → 18 ≤ q → q < 240 → (∀ r ∈ n.primeFactors, r ≠ 3 → r ≠ 5 → r ≠ 17 → q ≤ r) → n.Pseudoperfect

def H2 : Prop := ∀ n : ℕ, Odd n → n.Abundant → n.primeFactors.card ≤ 5 → 45 ∣ n → 17 ∣ n →
    (∀ r ∈ n.primeFactors, r ≠ 3 → r ≠ 5 → 17 ≤ r) → ∀ q : ℕ, q.Prime → q ∣ n → 240 ≤ q → q < 283 → (∀ r ∈ n.primeFactors, r ≠ 3 → r ≠ 5 → r ≠ 17 → q ≤ r) → n.Pseudoperfect

def H3 : Prop := ∀ n : ℕ, Odd n → n.Abundant → n.primeFactors.card ≤ 5 → 45 ∣ n → 17 ∣ n →
    (∀ r ∈ n.primeFactors, r ≠ 3 → r ≠ 5 → 17 ≤ r) → ∀ q : ℕ, q.Prime → q ∣ n → 283 ≤ q → q < 512 → (∀ r ∈ n.primeFactors, r ≠ 3 → r ≠ 5 → r ≠ 17 → q ≤ r) → n.Pseudoperfect

open OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1
theorem minimum_outside (n : ℕ) (S : List ℕ) {p : ℕ} (mp : p ∈ n.primeFactors) (away : p ∉ S) :
    ∃ q ∈ n.primeFactors, q ∉ S ∧ q ≤ p ∧ ∀ r ∈ n.primeFactors, r ∉ S → q ≤ r := by
  let F := n.primeFactors.filter (fun r => r ∉ S)
  have pm : p ∈ F := Finset.mem_filter.mpr ⟨mp,away⟩
  let q := F.min' ⟨p,pm⟩
  have h := Finset.mem_filter.mp (F.min'_mem ⟨p,pm⟩)
  exact ⟨q,h.1,h.2,F.min'_le _ pm,fun r hr ho => F.min'_le _ (Finset.mem_filter.mpr ⟨hr,ho⟩)⟩

theorem fourth {n p B : ℕ} (odd : Odd n) (ab : n.Abundant) (hc : n.primeFactors.card ≤ 5)
    (d45 : 45 ∣ n) (mp : p ∈ n.primeFactors) (big : 5 < p)
    (least : ∀ r ∈ n.primeFactors, r ≠ 3 → r ≠ 5 → p ≤ r) (hB : 1 < B)
    (bound : ((B : ℚ)/(B-1))^2*((3/2)*(5/4)*((p:ℚ)/(p-1))) ≤ 2) :
    ∃ q, q.Prime ∧ q ∣ n ∧ p < q ∧ q < B ∧
      ∀ r ∈ n.primeFactors, r ≠ 3 → r ≠ 5 → r ≠ p → q ≤ r := by
  have m3 := Nat.mem_primeFactors.mpr ⟨(by decide : Nat.Prime 3),(by decide : 3 ∣ 45).trans d45,odd.pos.ne'⟩
  have m5 := Nat.mem_primeFactors.mpr ⟨(by decide : Nat.Prime 5),(by decide : 5 ∣ 45).trans d45,odd.pos.ne'⟩
  have sub : ∀ x ∈ [3,5,p], x ∈ n.primeFactors := by simp_all
  have nd : [3,5,p].Nodup := by simp [show 3≠p by omega,show 5≠p by omega]
  have c3 := local_ratio_le 3 (n.factorization 3) (by decide) (3/2) (by norm_num)
  have c5 := local_ratio_le 5 (n.factorization 5) (by decide) (5/4) (by norm_num)
  have pp := Nat.prime_of_mem_primeFactors mp
  have pos : (0:ℚ) < p-1 := by
    have hp : (5:ℚ)<p := by exact_mod_cast big
    linarith
  have cp := local_ratio_le p (n.factorization p) pp ((p:ℚ)/(p-1)) (by rw [div_mul_cancel₀ _ pos.ne'])
  obtain ⟨v,mv,av,hv⟩ := next_from_bounds n odd.pos ab hc [3,5,p] [3/2,5/4,(p:ℚ)/(p-1)] B hB nd sub
    (.cons c3 (.cons c5 (.cons cp .nil))) (by simpa [List.prod_cons,mul_assoc] using bound)
  obtain ⟨q,mq,aq,qv,hq⟩ := minimum_outside n [3,5,p] mv av
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at aq
  have pq := least q mq aq.1 aq.2.1
  exact ⟨q,Nat.prime_of_mem_primeFactors mq,Nat.dvd_of_mem_primeFactors mq,by omega,by omega,
    fun r mr a b c => hq r mr (by simp [a,b,c])⟩

theorem main : H1 → H2 → H3 → OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1_H4_R1.H1 := by
  intro a b c n odd ab _ hc _ d45 no7 no11 no13 dp
  have least : ∀ r ∈ n.primeFactors, r ≠ 3 → r ≠ 5 → 17 ≤ r := by
    intro r mr ne3 ne5
    by_contra! lt
    have dr := Nat.dvd_of_mem_primeFactors mr
    have rprime := Nat.prime_of_mem_primeFactors mr
    have census : ∀ j : Fin 17, j.val.Prime → j.val ∈ ([2,3,5,7,11,13] : List ℕ) := by decide
    have member := census ⟨r,lt⟩ rprime
    change r ∈ ([2,3,5,7,11,13] : List ℕ) at member
    have ne2 : r≠2 := fun e => odd.not_two_dvd_nat (e ▸ dr)
    have ne7 : r≠7 := fun e => no7 (e ▸ dr)
    have ne11 : r≠11 := fun e => no11 (e ▸ dr)
    have ne13 : r≠13 := fun e => no13 (e ▸ dr)
    simp [ne2,ne3,ne5,ne7,ne11,ne13] at member
  have mp := Nat.mem_primeFactors.mpr ⟨(by decide : Nat.Prime 17),dp,odd.pos.ne'⟩
  obtain ⟨q,qp,dq,pq,top,leastq⟩ := fourth (B:=512) odd ab hc d45 mp (by decide) least (by decide) (by norm_num)
  by_cases h : q < 240
  · exact a n odd ab hc d45 dp least q qp dq (by omega) h leastq
  by_cases k : q < 283
  · exact b n odd ab hc d45 dp least q qp dq (by omega) k leastq
  · exact c n odd ab hc d45 dp least q qp dq (by omega) top leastq
end OMA.R_Erdos470_erdos_470_variants_odd_weird_prime_div_R2_H2_R1_H4_R1_H1_R1
