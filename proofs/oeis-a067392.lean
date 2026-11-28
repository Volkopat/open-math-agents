import OMAStatements.S_oeis_a067392

/-!
# Distinct noncoprime sums at prime distance

V. S. Guba's conjecture as recorded in OEIS A067392 (May 2024).
Original Lean proof: @AttaQ.
An equality forces two consecutive even totients. A bound for totients
congruent to two modulo four leaves only finitely many cases.
-/

namespace A067392Proof
open OMA.S_oeis_a067392 Finset

/-- Reflect the reduced residues by k ↦ n-k, then sum over their complement. -/
private theorem twice_a (n : ℕ) (hn : 2 ≤ n) : 2 * a n = n * (n + 1 - n.totient) := by
  let S := (range n).filter (n.Coprime ·)
  have memS (k : ℕ) : k ∈ S ↔ k < n ∧ n.Coprime k := by simp [S]
  have refl_mem (k : ℕ) (hk : k ∈ S) : n - k ∈ S := by
    obtain ⟨hlt, hc⟩ := (memS k).mp hk
    have hpos : k ≠ 0 := by
      rintro rfl
      have : n = 1 := by simpa using hc
      omega
    exact (memS _).mpr ⟨by omega, (Nat.coprime_self_sub_right hlt.le).mpr hc⟩
  have refl_refl (k : ℕ) (hk : k ∈ S) : n - (n - k) = k := by
    have := (memS k).mp hk
    omega
  have reflect : (∑ k ∈ S, (n - k)) = ∑ k ∈ S, k :=
    sum_nbij' (n - ·) (n - ·) refl_mem refl_mem refl_refl refl_refl (by intros; rfl)
  have reduced : 2 * (∑ k ∈ S, k) = n * n.totient := by
    calc
      _ = (∑ k ∈ S, k) + ∑ k ∈ S, (n-k) := by rw [reflect]; omega
      _ = ∑ k ∈ S, (k+(n-k)) := sum_add_distrib.symm
      _ = ∑ _k ∈ S, n := sum_congr rfl fun k hk => by have := (memS k).mp hk; omega
      _ = n * n.totient := by simp [Nat.totient_eq_card_coprime, S, mul_comm]
  have hS : (range (n+1)).filter (n.Coprime ·) = S := by
    ext k
    simp only [S, mem_filter, mem_range]
    by_cases hk : k = n
    · subst k
      simp [show n ≠ 1 by omega]
    · rw [show k < n + 1 ↔ k < n by omega]
  have hpred (k : ℕ) : (¬ n.Coprime k) ↔ 1 < n.gcd k := by
    change n.gcd k ≠ 1 ↔ 1 < n.gcd k
    have := Nat.gcd_pos_of_pos_left k (by omega : 0 < n)
    omega
  have hcomp : (∑ k ∈ (range (n+1)).filter (fun k => ¬ n.Coprime k), k) = a n := by
    simp_rw [hpred]
    symm
    unfold a
    apply sum_subset
    · intro k hk
      simp only [mem_filter, mem_Icc, mem_range] at hk ⊢
      omega
    · intro k hk hk'
      simp only [mem_filter, mem_Icc, mem_range] at hk hk'
      omega
  have split := sum_filter_add_sum_filter_not (range (n+1)) (n.Coprime ·) (fun k => k)
  rw [hS, hcomp] at split
  have tri := sum_range_id_mul_two (n+1)
  simp only [Nat.add_sub_cancel] at tri
  rw [Nat.mul_sub, mul_comm n (n + 1)]
  omega

/-- Coprimality forces the larger index to divide a positive smaller factor. -/
private theorem ne_of_not_dvd (n p : ℕ) (hn : 0 < n) (hp : p.Prime) (hpn : ¬p ∣ n) :
    a n ≠ a (n+p) := by
  intro he
  have hp2 := hp.two_le
  have ht := twice_a (n+p) (by omega)
  have ht_le := (n+p).totient_le
  have hpos : 0 < (n+p)*(n+p+1-(n+p).totient) := Nat.mul_pos (by omega) (by omega)
  by_cases h1 : n = 1
  · subst n
    have : a 1 = 0 := by decide
    omega
  have hn2 := twice_a n (by omega)
  have heq : n*(n+1-n.totient) = (n+p)*(n+p+1-(n+p).totient) := by omega
  have hc : (n+p).Coprime n := by
    rw [Nat.add_comm, Nat.coprime_add_self_left]
    exact hp.coprime_iff_not_dvd.mpr hpn
  have hd : (n+p) ∣ n*(n+1-n.totient) := by rw [heq]; exact dvd_mul_right ..
  have hd' := hc.dvd_of_dvd_mul_left hd
  have := n.totient_le
  exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hd'

/-- At an even index above two, four divides twice the sum exactly when it divides the index. -/
private theorem ne_two (n : ℕ) (hn : 0 < n) : a n ≠ a (n+2) := by
  have div4 (m : ℕ) (hm : 2 < m) (he : 2 ∣ m) : 4 ∣ 2 * a m ↔ 4 ∣ m := by
    have evenTotient := (Nat.totient_even hm).two_dvd
    have ht := m.totient_le
    have ho : Odd (m+1-m.totient) := ⟨(m+1-m.totient)/2, by omega⟩
    have hc : Nat.Coprime 4 (m+1-m.totient) := (Nat.coprime_two_left.mpr ho).pow_left 2
    rw [twice_a m hm.le]
    exact hc.dvd_mul_right
  by_cases he : 2 ∣ n
  · by_cases h2 : n = 2
    · subst n
      decide
    intro same
    have h : 4 ∣ n ↔ 4 ∣ n+2 := by
      rw [← div4 n (by omega) he, same, div4 (n+2) (by omega) (by omega)]
    omega
  · exact ne_of_not_dvd n 2 hn Nat.prime_two he

set_option maxHeartbeats 1000000 in
/-- Consecutive quotients determine both totients under the putative equality. -/
private theorem totients_at_multiples (p k : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hk : 0 < k)
    (eqn : k*(p*k+1-(p*k).totient) = (k+1)*(p*(k+1)+1-(p*(k+1)).totient)) :
    (p*k).totient + p = 2*k+3 ∧ (p*(k+1)).totient = 2*k+p+1 ∧
    5 ≤ p ∧ (¬ p ∣ k) ∧ (¬ p ∣ k+1) := by
  let P := (p*k).totient
  let Q := (p*(k+1)).totient
  let X := p*k+1-P
  let Y := p*(k+1)+1-Q
  have hP : 0 < P := Nat.totient_pos.mpr (by positivity)
  have hX : X + P = p*k+1 := by dsimp [X,P]; have := Nat.totient_le (p*k); omega
  have hY : Y + Q = p*(k+1)+1 := by dsimp [Y,Q]; have := Nat.totient_le (p*(k+1)); omega
  have hx : 0 < X := by have h : P ≤ p*k := Nat.totient_le _; omega
  change k*X=(k+1)*Y at eqn
  have hcop : k.Coprime (k+1) := Nat.coprime_self_add_right.mpr (by simp)
  have hd : k+1 ∣ k*X := ⟨Y,eqn⟩
  obtain ⟨s,hs⟩ := hcop.symm.dvd_of_dvd_mul_left hd
  have hys : Y = k*s := by
    apply Nat.mul_left_cancel (Nat.succ_pos k)
    change (k+1)*Y = (k+1)*(k*s)
    rw [← eqn, hs]
    ring
  have hspos : 0 < s := by by_contra! h; simp [show s=0 by omega] at hs; omega
  have hsp : s < p := by
    by_contra! h
    have := Nat.mul_le_mul_left (k+1) h
    nlinarith only [this, hs, hX, hP, hp3]
  let r := p-s
  have hr : r+s=p := Nat.sub_add_cancel (by omega)
  have hrpos : 1 ≤ r := by omega
  have hrlt : r < p := by omega
  have hp1 : p-1+1=p := by omega
  have div (t : ℕ) : p-1 ∣ (p*t).totient := by
    rw [← Nat.totient_prime hp]
    exact Nat.totient_dvd_of_dvd (Nat.dvd_mul_right _ _)
  obtain ⟨i,hi⟩ := div k
  obtain ⟨j,hj⟩ := div (k+1)
  have hdif : Q+r = P+2*p := by nlinarith only [hX,hY,hs,hys,hr]
  have jlo : i+2 ≤ j := by
    by_contra! h
    have := Nat.mul_le_mul_left (p-1) (show j ≤ i+1 by omega)
    nlinarith only [this, hdif,hi,hj,hp1,hrlt]
  have jhi : j ≤ i+2 := by
    by_contra! h
    have := Nat.mul_le_mul_left (p-1) (show i+3 ≤ j by omega)
    nlinarith only [this, hdif,hi,hj,hp1,hrpos,hp3]
  have hj2 : j=i+2 := by omega
  have hr2 : r=2 := by rw [hj2] at hj; nlinarith only [hj,hi,hdif,hp1]
  have sp : s+2=p := by omega
  have hprod : k*s+2*k=k*p := by rw [←sp]; ring
  have Pval : P+p=2*k+3 := by nlinarith only [hX,hs,sp,hprod]
  have Qval : Q=2*k+p+1 := by omega
  change (P+p=2*k+3) ∧ (Q=2*k+p+1) ∧ _
  have pDvdTotient (t : ℕ) (ht : p ∣ t) : p ∣ (p*t).totient := by
    have hp2 : p ^ 2 ∣ p * t := by
      simpa only [pow_two] using Nat.mul_dvd_mul (dvd_refl p) ht
    have hphi := Nat.totient_dvd_of_dvd hp2
    rw [show (p^2).totient = p*(p-1) by
      simpa only [pow_one] using Nat.totient_prime_pow_succ hp 1] at hphi
    exact (dvd_mul_right _ _).trans hphi
  have ndt : ¬p ∣ k+1 := by
    intro h
    have dQ : p ∣ Q := pDvdTotient _ h
    have he : Q+1=2*(k+1)+p := by omega
    have hQ1 : p ∣ Q+1 := he ▸ dvd_add (dvd_mul_of_dvd_right h 2) (dvd_refl p)
    have := (Nat.dvd_add_right dQ).mp hQ1
    exact hp.not_dvd_one this
  have hQval : (p*(k+1)).totient = 2*k+p+1 := Qval
  have h5 : 5 ≤ p := by
    by_contra! h
    interval_cases p
    · have t := Nat.totient_mul_of_prime_of_not_dvd hp ndt
      have l := Nat.totient_le (k+1)
      norm_num at t
      omega
    · exact (by decide : ¬ Nat.Prime 4) hp
  refine ⟨Pval,Qval,h5,?_,ndt⟩
  intro h
  have dP : p ∣ P := pDvdTotient _ h
  have h3 : p ∣ 3 := (Nat.dvd_add_right (dvd_mul_of_dvd_right h 2)).mp
    (Pval ▸ dvd_add dP (dvd_refl p))
  have := Nat.le_of_dvd (by decide) h3
  omega

/-- If a totient is twice an odd number, its argument is at most three
times the totient. For an odd argument the bound improves by a factor of two. -/
private theorem totient_bounds (m : ℕ) (h : m.totient % 4 = 2) :
    m ≤ 3*m.totient ∧ (¬ 2 ∣ m → 2*m ≤ 3*m.totient) := by
  induction m using Nat.recOnPrimeCoprime with
  | zero => norm_num at h
  | prime_pow p k hp =>
    cases k with
    | zero => norm_num at h
    | succ k =>
      rw [Nat.totient_prime_pow_succ hp, pow_succ]
      have hp' := hp.two_le
      constructor
      · calc
          p^k*p ≤ p^k*(3*(p-1)) := Nat.mul_le_mul_left _ (by omega)
          _ = _ := by ring
      · intro ho
        have hp2 : p ≠ 2 := by
          rintro rfl
          exact ho (dvd_mul_left 2 (2^k))
        calc
          2*(p^k*p) = p^k*(2*p) := by ring
          _ ≤ p^k*(3*(p-1)) := Nat.mul_le_mul_left _ (by omega)
          _ = _ := by ring
  | coprime a b ha hb cop ia ib =>
    rw [Nat.totient_mul cop] at h ⊢
    by_cases h2a : a = 2
    · subst a
      norm_num at h ⊢
      obtain ⟨t,ht⟩ := Nat.coprime_two_left.mp cop
      exact (ib h).2 (by omega)
    by_cases h2b : b = 2
    · subst b
      norm_num at h ⊢
      obtain ⟨t,ht⟩ := Nat.coprime_two_right.mp cop
      simpa only [Nat.mul_comm a 2] using (ia h).2 (by omega)
    have ha' := (Nat.totient_even (show 2<a by omega)).two_dvd
    have hb' := (Nat.totient_even (show 2<b by omega)).two_dvd
    have hd : 4 ∣ a.totient*b.totient := Nat.mul_dvd_mul ha' hb'
    omega

/-- The two totients would be consecutive even numbers. One is 2 modulo 4,
so its size rules out all possible values of h = (p-1)/2. -/
private theorem impossible_pair (k h : ℕ) (hh : 2 ≤ h)
    (diff : (k+1).totient = k.totient + 2)
    (mul : h*((k+1).totient - 1) = k+1) : False := by
  have ht : 1 ≤ (k+1).totient-1 := by omega
  have hhk : h ≤ k+1 := by
    calc h = h*1 := by simp
         _ ≤ h*((k+1).totient-1) := Nat.mul_le_mul_left _ ht
         _ = _ := mul
  by_cases low : k < 12
  · have checked : ∀ k : Fin 12, ∀ h : Fin 13, 2 ≤ h.val →
        (k.val+1).totient = k.val.totient+2 →
        h.val*((k.val+1).totient-1) ≠ k.val+1 := by decide +kernel
    exact checked ⟨k,low⟩ ⟨h,by omega⟩ hh diff mul
  obtain ⟨u, hu⟩ := Nat.totient_even (n := k) (by omega)
  obtain ⟨v, hv⟩ := Nat.totient_even (n := k+1) (by omega)
  obtain h2 | h3 : h = 2 ∨ 3 ≤ h := by omega
  · subst h
    have odd : Odd ((k+1).totient-1) := ⟨v-1, by omega⟩
    have e := Nat.totient_two_mul_of_odd odd
    rw [mul] at e
    have := Nat.totient_le ((k+1).totient-1)
    omega
  have lower := Nat.mul_le_mul_right ((k+1).totient-1) h3
  have hu4 : k.totient % 4 ≠ 2 := by
    intro bad
    have := (totient_bounds k bad).1
    omega
  have hv4 : (k+1).totient % 4 = 2 := by omega
  obtain ⟨bound, odd_bound⟩ := totient_bounds (k+1) hv4
  by_cases h4 : 4 ≤ h
  · have := Nat.mul_le_mul_right ((k+1).totient-1) h4
    omega
  · have he : h = 3 := by omega
    subst h
    have odd : ¬ 2 ∣ k+1 := by omega
    have := odd_bound odd
    omega

private theorem positive_multiple (p k : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hk : 0 < k)
    (eqn : k*(p*k+1-(p*k).totient) = (k+1)*(p*(k+1)+1-(p*(k+1)).totient)) : False := by
  obtain ⟨first,second,hp5,hleft,hright⟩ := totients_at_multiples p k hp hp3 hk eqn
  rw [Nat.totient_mul_of_prime_of_not_dvd hp hleft] at first
  rw [Nat.totient_mul_of_prime_of_not_dvd hp hright] at second
  obtain ⟨h, he⟩ := hp.odd_of_ne_two (by omega)
  have pe : p-1 = 2*h := by omega
  rw [pe] at first second
  have h2 : 2 ≤ h := by omega
  have de : (k+1).totient = k.totient + 2 := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2*h)
    rw [Nat.mul_add]
    omega
  have vd : (k+1).totient = ((k+1).totient-1)+1 := by omega
  have m : h*((k+1).totient-1) = k+1 := by
    nth_rw 1 [vd] at second
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc] at second
    omega
  exact impossible_pair k h h2 de m

end A067392Proof

open OMA.S_oeis_a067392 A067392Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a067392.main := by
  intro n p hn hp same
  by_cases hd : p ∣ n
  · obtain ⟨k,rfl⟩ := hd
    by_cases p2 : p=2
    · subst p
      exact ne_two _ hn same
    have hk : 0 < k := Nat.pos_of_mul_pos_left hn
    have pp := hp.two_le
    have pk : 2 ≤ p*k := by nlinarith
    have pm : 2 ≤ p*(k+1) := by nlinarith
    rw [← Nat.mul_succ] at same
    have sums := congrArg (fun t : ℕ => 2*t) same
    change 2*a (p*k) = 2*a (p*(k+1)) at sums
    rw [twice_a _ pk, twice_a _ pm, Nat.mul_assoc, Nat.mul_assoc] at sums
    exact positive_multiple p k hp (by omega) hk (Nat.eq_of_mul_eq_mul_left hp.pos sums)
  · exact ne_of_not_dvd n p hn hp hd same
