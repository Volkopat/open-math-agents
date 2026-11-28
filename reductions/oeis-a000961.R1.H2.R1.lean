import OMAReductions.R_oeis_a000961_R1

/-!
# Complementary totients and the two largest prime factors

Source: https://oeis.org/A000961
Credit: @Dolcruz

Euler's product formula removes all prime exponents from the local tests.
On the squarefree support the resulting integer determines a finite list
of possible pairs of largest prime factors once the other primes are fixed.
-/

namespace OMA.R_oeis_a000961_R1_H2_R1

open Finset

theorem local_support (m p : ℕ) (hm : 0 < m) (hpS : p ∈ m.primeFactors)
    (h : ∀ q e t : ℕ, q.Prime → q.Coprime t → m = q^(e+1)*t →
      t ≡ t.totient [MOD q]) :
    (∏ q ∈ m.primeFactors.erase p, q) ≡
      (∏ q ∈ m.primeFactors.erase p, (q-1)) [MOD p] := by
  have hp := Nat.prime_of_mem_primeFactors hpS
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨e,t,ht,eq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' p hp.ne_one
  cases e with
  | zero =>
    simp only [pow_zero,one_mul] at eq
    exact (ht (eq ▸ Nat.dvd_of_mem_primeFactors hpS)).elim
  | succ e =>
    have ht0 : t ≠ 0 := by intro z; simp [z] at eq; omega
    have hc := h p e t hp (hp.coprime_iff_not_dvd.mpr ht) eq
    have ha : t.primeFactors = m.primeFactors.erase p := by
      rw [eq,Nat.primeFactors_mul (pow_ne_zero _ hp.ne_zero) ht0,
        Nat.primeFactors_prime_pow (by omega) hp]
      have hn : p ∉ t.primeFactors := fun hq => ht (Nat.dvd_of_mem_primeFactors hq)
      simp [hn]
    have he := congrArg (fun n : ℕ => (n : ZMod p)) (Nat.totient_mul_prod_primeFactors t)
    push_cast only [Nat.cast_mul] at he
    rw [← (ZMod.natCast_eq_natCast_iff ..).mpr hc,ha] at he
    exact (ZMod.natCast_eq_natCast_iff ..).mp
      (mul_left_cancel₀ ((ZMod.natCast_eq_zero_iff ..).not.mpr ht) he)

theorem support_divisibility (s : Finset ℕ) (primes : ∀ p ∈ s, Nat.Prime p)
    (h : ∀ p ∈ s, (∏ q ∈ s.erase p, q) ≡ (∏ q ∈ s.erase p, (q-1)) [MOD p]) :
    (∏ q ∈ s, q) ∣ (∏ q ∈ s, (q-1)) + ∑ p ∈ s, ∏ q ∈ s.erase p, q := by
  apply Finset.prod_primes_dvd _ (fun p hp => (primes p hp).prime)
  intro p hp
  let _ : Fact p.Prime := ⟨primes p hp⟩
  have localEq := (ZMod.natCast_eq_natCast_iff ..).mpr (h p hp)
  have other (q : ℕ) (hq : q ∈ s) (hn : q ≠ p) :
      ((∏ a ∈ s.erase q, a : ℕ) : ZMod p) = 0 := by
    apply (ZMod.natCast_eq_zero_iff ..).mpr
    exact dvd_prod_of_mem _ (mem_erase.mpr ⟨hn.symm, hp⟩)
  apply (ZMod.natCast_eq_zero_iff ..).mp
  rw [Nat.cast_add,Nat.cast_sum,Finset.sum_eq_single_of_mem p hp other,
    ← Finset.mul_prod_erase s (fun q => q-1) hp, Nat.cast_mul,
    Nat.cast_sub (primes p hp).one_le,ZMod.natCast_self,Nat.cast_one,localEq]
  ring

theorem integral_support (m : ℕ) (hm : 0 < m)
    (h : ∀ p e t : ℕ, p.Prime → p.Coprime t → m = p^(e+1)*t →
      t ≡ t.totient [MOD p]) :
    (∏ q ∈ m.primeFactors, q) ∣ (∏ q ∈ m.primeFactors, (q-1)) +
      ∑ p ∈ m.primeFactors, ∏ q ∈ m.primeFactors.erase p, q :=
  support_divisibility _ (fun _ hp => Nat.prime_of_mem_primeFactors hp)
    (fun p hp => local_support m p hm hp h)


theorem deletion_sum_insert (s : Finset ℕ) (p : ℕ) (hp : p ∉ s) :
    (∑ r ∈ insert p s, ∏ a ∈ (insert p s).erase r, (a : ℤ)) =
    (∏ a ∈ s, (a : ℤ)) + p * ∑ r ∈ s, ∏ a ∈ s.erase r, (a : ℤ) := by
  rw [sum_insert hp, erase_insert hp, mul_sum]
  congr 1
  apply sum_congr rfl
  intro r hr
  have ne : p ≠ r := fun e => hp (e.symm ▸ hr)
  rw [erase_insert_of_ne ne, prod_insert (fun h => hp (mem_of_mem_erase h))]

/-- Remove the two largest elements, retaining their strict order. -/
theorem two_largest (s : Finset ℕ) (hs : 1 < s.card) :
    ∃ T : Finset ℕ, ∃ p q : ℕ, s = insert q (insert p T) ∧ p < q ∧ ∀ r ∈ T, r < p := by
  have hn : s.Nonempty := card_pos.mp (by omega)
  let q := s.max' hn
  have hq : q ∈ s := max'_mem _ _
  let U := s.erase q
  have hu : U.Nonempty := card_pos.mp (by dsimp [U]; rw [card_erase_of_mem hq]; omega)
  let p := U.max' hu
  have hp : p ∈ U := max'_mem _ _
  have hpq := mem_erase.mp hp
  refine ⟨U.erase p,p,q,?_,lt_of_le_of_ne (le_max' _ _ hpq.2) hpq.1,?_⟩
  · rw [insert_erase hp, show insert q U = s from insert_erase hq]
  · intro r hr
    obtain ⟨hne, hmem⟩ := mem_erase.mp hr
    exact lt_of_le_of_ne (le_max' _ _ hmem) hne

/-- The integer attained after adjoining p and q is forced to be the next
integer above B/N. Completing the product gives a positive factor pair. -/
theorem pair_equation (N A B k p q : ℤ) (hA : 0 < A) (hAN : A ≤ N)
    (hp : 2 ≤ p) (hpq : p < q)
    (h : k*N*(p*q) = B*(p*q)+(N-A)*(p+q)+A) :
    let D := (B/N+1)*N-B
    0 < D*p-(N-A) ∧
      (D*p-(N-A))*(D*q-(N-A)) = (N-A)^2 + D*A := by
  have hN : 0 < N := by omega
  have hP : 0 < p := by omega
  have hQ : 0 < q := by omega
  have hC : 0 ≤ N-A := by omega
  have hpq0 : 0 < p*q := mul_pos hP hQ
  have hlt : p+q < p*q := by
    nlinarith [mul_nonneg (show 0 ≤ p-2 by omega) (show 0 ≤ q-2 by omega)]
  have gap0 : 0 < (N-A)*(p+q)+A := by positivity
  have gap1 : (N-A)*(p+q)+A < N*(p*q) := by
    have ha := mul_nonneg (show 0 ≤ A by omega) (show 0 ≤ p+q-1 by omega)
    nlinarith [mul_lt_mul_of_pos_left hlt hN]
  have low : B < k*N := by
    by_contra! hle
    linarith only [h,gap0,mul_le_mul_of_nonneg_right hle hpq0.le]
  have high : k*N < B+N := by
    by_contra! hle
    have hh := mul_le_mul_of_nonneg_right hle hpq0.le
    rw [add_mul] at hh
    linarith only [h,gap1,hh]
  have floor : B / N = k-1 := (Int.ediv_eq_iff_of_pos hN).mpr ⟨by linarith, by linarith⟩
  let D := (B/N+1)*N-B
  have dEq : D = k*N-B := by dsimp [D]; rw [floor]; ring
  have prodEq : D*p*q = (N-A)*(p+q)+A := by rw [dEq]; linear_combination h
  have posProd : 0 < (D*p-(N-A))*q := by
    have right : 0 ≤ (N-A)*p := mul_nonneg (by omega) (by omega)
    nlinarith only [prodEq,hA,right]
  refine ⟨pos_of_mul_pos_left posProd (by omega), ?_⟩
  change (D*p-(N-A))*(D*q-(N-A)) = (N-A)^2+D*A
  linear_combination D*prodEq

theorem support_pair (T : Finset ℕ) (p q : ℕ) (ht : ∀ a ∈ T, Nat.Prime a)
    (hp : Nat.Prime p) (hpq : p < q) (hlt : ∀ a ∈ T, a < p)
    (k : ℕ) (h :
      (∏ a ∈ insert q (insert p T), a) * k =
      (∏ a ∈ insert q (insert p T), (a-1)) +
        ∑ r ∈ insert q (insert p T), ∏ a ∈ (insert q (insert p T)).erase r, a) :
    let N := ∏ a ∈ T, (a : ℤ)
    let A := ∏ a ∈ T, ((a : ℤ)-1)
    let B := A + ∑ r ∈ T, ∏ a ∈ T.erase r, (a : ℤ)
    let D := (B/N+1)*N-B
    0 < D*p-(N-A) ∧ (D*p-(N-A))*(D*q-(N-A)) = (N-A)^2 + D*A := by
  intro N A B D
  have hpt : p ∉ T := fun h => (hlt p h).false
  have hqt : q ∉ insert p T := by
    intro hq
    rcases mem_insert.mp hq with he | h
    · omega
    · have := hlt _ h; omega
  have posT (a : ℕ) (ha : a ∈ T) : 2 ≤ a := (ht a ha).two_le
  have posS (a : ℕ) (ha : a ∈ insert q (insert p T)) : 1 ≤ a := by
    simp only [mem_insert] at ha
    rcases ha with rfl | rfl | hx
    · have := hp.two_le; omega
    · exact hp.one_le
    · have := posT a hx; omega
  have castA : ((∏ a ∈ insert q (insert p T), (a-1) : ℕ) : ℤ) =
      ∏ a ∈ insert q (insert p T), ((a : ℤ)-1) := by
    rw [Nat.cast_prod]; apply prod_congr rfl; intro a ha; rw [Nat.cast_sub (posS a ha)]; simp
  have eq := congrArg (fun n : ℕ => (n : ℤ)) h
  push_cast only [Nat.cast_mul,Nat.cast_add,Nat.cast_sum] at eq
  rw [castA] at eq
  push_cast only [Nat.cast_prod] at eq
  rw [deletion_sum_insert _ q hqt, deletion_sum_insert _ p hpt] at eq
  simp only [prod_insert hqt,prod_insert hpt] at eq
  apply pair_equation N A B k p q
  · apply Finset.prod_pos; intro a ha; have := posT a ha; omega
  · apply Finset.prod_le_prod
    · intro a ha; have := posT a ha; omega
    · intro a _; omega
  · exact_mod_cast hp.two_le
  · exact_mod_cast hpq
  · dsimp [N,A,B]
    linear_combination eq

/-- The finite-support estimate. Integrality forces more than 10000 distinct
prime factors as soon as the support contains two primes. -/
def H1 : Prop := ∀ s : Finset ℕ, (∀ p ∈ s, Nat.Prime p) → 1 < s.card → s.card ≤ 10000 →
  ¬ (∏ q ∈ s, q) ∣ (∏ q ∈ s, (q-1)) + ∑ p ∈ s, ∏ q ∈ s.erase p, q

/-- Fix all prime factors except the two greatest. The remaining candidates
come from pairs of positive divisors of a single integer determined by T. -/
def H2 : Prop := ∀ (T : Finset ℕ) (p q : ℕ), 9999 ≤ T.card →
  (∀ r ∈ T, Nat.Prime r) → Nat.Prime p → Nat.Prime q → p < q → (∀ r ∈ T, r < p) →
  let N := ∏ r ∈ T, (r : ℤ)
  let A := ∏ r ∈ T, ((r : ℤ)-1)
  let B := A + ∑ r ∈ T, ∏ a ∈ T.erase r, (a : ℤ)
  let D := (B/N+1)*N-B
  ¬ (0 < D*p-(N-A) ∧ (D*p-(N-A))*(D*q-(N-A)) = (N-A)^2 + D*A)

theorem main : H1 → H2 → OMA.R_oeis_a000961_R1.H2 := by
  intro small large m hm hlocal
  by_contra hn
  have hne : m ≠ 1 := fun e => hn (Or.inl e)
  have hnp : ¬ IsPrimePow m := fun e => hn (Or.inr e)
  have hs := one_lt_card_iff_nontrivial.mpr ((Nat.not_isPrimePow_iff_nontrivial_of_two_le
    (by omega : 2 ≤ m)).mp hnp)
  have hdiv := integral_support m hm hlocal
  have primes : ∀ r ∈ m.primeFactors, Nat.Prime r := fun _ hr => Nat.prime_of_mem_primeFactors hr
  by_cases hsmall : m.primeFactors.card ≤ 10000
  · exact small _ primes hs hsmall hdiv
  obtain ⟨T,p,q,eq,hpq,hlt⟩ := two_largest _ hs
  rw [eq] at primes hdiv hsmall
  have hpt : p ∉ T := fun h => (hlt _ h).false
  have hqt : q ∉ insert p T := by
    intro h
    rcases mem_insert.mp h with he | ht
    · omega
    · have := hlt _ ht; omega
  rw [card_insert_of_notMem hqt, card_insert_of_notMem hpt] at hsmall
  have ht : ∀ a ∈ T, Nat.Prime a := fun a ha => primes a (by simp [ha])
  have hp : Nat.Prime p := primes p (by simp)
  have hq : Nat.Prime q := primes q (by simp)
  obtain ⟨k,hk⟩ := hdiv
  exact large T p q (by omega) ht hp hq hpq hlt (support_pair T p q ht hp hpq hlt k hk.symm)

end OMA.R_oeis_a000961_R1_H2_R1
