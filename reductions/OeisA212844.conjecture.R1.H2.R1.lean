import OMAReductions.R_OeisA212844_conjecture_R1
import Mathlib

/-!
Even values of the sequence a(n) = 2^(n+2) mod n.

The previous reduction certifies every target through 300 except seven possible
values, and every dyadic ray of odd part at most nine. Here the witness
55,764,612,646 for 114 completes the even targets through 300. Modular
obstructions give the entire ray of odd part eleven. Two composite-index
constructions cover infinite families outside the original prime criterion.

The remaining questions concern large odd parts and smooth positive differences
from powers of two. The earlier prime construction and finite table are due to
@marcusbuffett. Credit: @AlfredMelson.
-/

namespace OMA.R_OeisA212844_conjecture_R1_H2_R1

namespace ElevenCert

private theorem fold {a m L : ℕ} (period : a^L ≡ 1 [MOD m]) (e : ℕ) :
    a^e ≡ a^(e%L) [MOD m] := by
  conv_lhs => rw [← Nat.mod_add_div e L, pow_add, pow_mul]
  simpa only [one_pow, mul_one] using (period.pow (e/L)).mul_left (a^(e%L))

/-- Reduce both exponents of a smooth product modulo L. The modulus 2^A
filters its possible residues. The odd modulus M separates the survivors
from all powers of two with the required exponent parity. -/
private theorem separate (P Q A M L K parity : ℕ) (hL : 0 < L) (hK : 0 < K)
    (hp : P^L ≡ 1 [MOD 2^A]) (hq : Q^L ≡ 1 [MOD 2^A])
    (hpM : P^L ≡ 1 [MOD M]) (hqM : Q^L ≡ 1 [MOD M]) (h2M : 2^K ≡ 1 [MOD M])
    (table : ∀ i j : Fin L, (P^i.val*Q^j.val+11) % (2^A) = 0 →
      (P^i.val*Q^j.val+11) % M ∉
        ((List.range K).filter fun t => t%2 == parity).map fun t => 2^t % M)
    (e : ℕ) (he : A ≤ e) (hpar : (e%K)%2 = parity) (r s : ℕ) :
    2^e ≠ P^r*Q^s+11 := by
  intro h
  let i : Fin L := ⟨r%L, Nat.mod_lt _ hL⟩
  let j : Fin L := ⟨s%L, Nat.mod_lt _ hL⟩
  have hf (m : ℕ) (hp' : P^L ≡ 1 [MOD m]) (hq' : Q^L ≡ 1 [MOD m]) :
      2^e ≡ P^i.val*Q^j.val+11 [MOD m] :=
    h ▸ ((fold hp' r).mul (fold hq' s)).add_right 11
  have hzero : 2^e ≡ 0 [MOD 2^A] := Nat.modEq_zero_iff_dvd.mpr (pow_dvd_pow 2 he)
  have hz := (hf _ hp hq).symm.trans hzero
  apply table i j (by simpa only [Nat.ModEq, Nat.zero_mod] using hz)
  exact List.mem_map.mpr ⟨e%K,
    List.mem_filter.mpr ⟨List.mem_range.mpr (Nat.mod_lt _ hK), beq_iff_eq.mpr hpar⟩,
    ((hf _ hpM hqM).symm.trans (fold h2M e)).symm⟩

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8000 in
theorem odd_obstruction (e : ℕ) (he : 6 ≤ e) (ho : Odd e) (r s : ℕ) :
    2^e ≠ 3^r*7^s+11 := by
  obtain ⟨x,hx⟩ := ho
  exact separate 3 7 6 (113*5*17) 112 56 1 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) e he (by omega) r s

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8000 in
theorem even_obstruction (e : ℕ) (he : 9 ≤ e) (hev : Even e) (r s : ℕ) :
    2^e ≠ 5^r*7^s+11 := by
  obtain ⟨x,hx⟩ := hev
  exact separate 5 7 9 (257*769) 256 384 0 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (by decide +kernel) e he (by omega) r s

end ElevenCert

namespace Eleven212844Ray
open OeisA212844 OMA.R_OeisA212844_conjecture_R1

private theorem eleven_prime_factor {N P Q : ℕ} (hN : 0 < N)
    (hs : ∀ p : ℕ, p.Prime → p ∣ N → p ≤ 11 → p=P ∨ p=Q)
    (hn : ∀ r s : ℕ, N ≠ P^r*Q^s) : ∃ p : ℕ, p.Prime ∧ 11 < p ∧ p ∣ N := by
  by_contra! hnone
  have factor (l : List ℕ) (h : ∀ p ∈ l, p=P ∨ p=Q) : ∃ r s : ℕ, l.prod = P^r*Q^s := by
    induction l with
    | nil => exact ⟨0,0,by simp⟩
    | cons p l ih =>
      obtain ⟨r,s,hrs⟩ := ih fun q hq => h q (by simp [hq])
      rcases h p (by simp) with rfl|rfl
      · exact ⟨r+1,s,by simp [hrs,pow_succ]; ring⟩
      · exact ⟨r,s+1,by simp [hrs,pow_succ]; ring⟩
  have hh (p : ℕ) (hp : p ∈ N.primeFactorsList) : p=P ∨ p=Q := by
    have hprime := Nat.prime_of_mem_primeFactorsList hp
    have hd := Nat.dvd_of_mem_primeFactorsList hp
    exact hs _ hprime hd (by by_contra! hlt; exact hnone p hprime hlt hd)
  obtain ⟨r,s,he⟩ := factor _ hh
  exact hn r s (by simpa [Nat.prod_primeFactorsList hN.ne'] using he)

theorem eleven_ray
    (hodd : ∀ e : ℕ, 6 ≤ e → Odd e → ∀ r s : ℕ, 2^e ≠ 3^r*7^s+11)
    (heven : ∀ e : ℕ, 9 ≤ e → Even e → ∀ r s : ℕ, 2^e ≠ 5^r*7^s+11)
    (v : ℕ) : ∃ n : ℕ, 1 ≤ n ∧ a n = 2^v*11 := by
  by_cases hv : v < 5
  · interval_cases v <;> exact finite_witnesses _ (by decide) (by decide)
  let T := 2^v+2-v
  have grow (j : ℕ) (hj : 5 ≤ j) : j+9 ≤ 2^j+2 := by
    induction j,hj using Nat.le_induction with
    | base => decide
    | succ j hj ih => rw [pow_succ]; omega
  have hT : 9 ≤ T := by dsimp [T]; have := grow v (by omega); omega
  have hY : 11 < 2^T := lt_of_lt_of_le (by decide : 11 < 2^9)
    (Nat.pow_le_pow_right (by decide) hT)
  let N := 2^T-11
  have hN : 0 < N := Nat.sub_pos_of_lt hY
  have hsum : N+11 = 2^T := Nat.sub_add_cancel hY.le
  have hres {p : ℕ} (hd : p ∣ N) : 2^T ≡ 11 [MOD p] :=
    ((Nat.modEq_iff_dvd' hY.le).mpr hd).symm
  have h2 : ¬2 ∣ N := by
    obtain ⟨k,hk⟩ := (even_two.pow_of_ne_zero (by omega : T ≠ 0) : Even (2^T:ℕ))
    omega
  have h11 : ¬11 ∣ N := by
    intro hd
    have hp : 11 ∣ 2^T := hsum ▸ Nat.dvd_add hd (dvd_rfl)
    exact (by decide : ¬11 ∣ 2) ((by decide : Nat.Prime 11).dvd_of_dvd_pow hp)
  have hsmall (p : ℕ) (hprime : p.Prime) (hle : p ≤ 11) :
      p=2 ∨ p=3 ∨ p=5 ∨ p=7 ∨ p=11 := by
    interval_cases p <;> norm_num at *
  have hprimes : ∃ p : ℕ, p.Prime ∧ 11 < p ∧ p ∣ N := by
    rcases Nat.even_or_odd T with ht|ht
    · have h3 : ¬3 ∣ N := by
        intro hd
        obtain ⟨k,hk⟩ := ht
        have hpow : 2^T ≡ 1 [MOD 3] := by
          rw [show T = 2*k by omega, pow_mul]
          simpa using (by decide : (2:ℕ)^2 ≡ 1 [MOD 3]).pow k
        exact (by decide : ¬(1 ≡ 11 [MOD 3])) (hpow.symm.trans (hres hd))
      apply eleven_prime_factor (P:=5) (Q:=7) hN
      · intro p hprime hd hle
        rcases hsmall p hprime hle with rfl|rfl|rfl|rfl|rfl <;> tauto
      · intro r s h
        exact heven T hT ht r s (hsum.symm.trans (congrArg (·+11) h))
    · have h5 : ¬5 ∣ N := by
        intro hd
        have hmod := hres hd
        change 2^T%5 = 1 at hmod
        rw [Nat.pow_totient_mod (by decide : 1 < 5) (by decide : Nat.Coprime 2 5)] at hmod
        change 2^(T%4)%5 = 1 at hmod
        obtain ⟨k,hk⟩ := ht
        have hh : T%4=1 ∨ T%4=3 := by omega
        rcases hh with h|h <;> norm_num [h] at hmod
      apply eleven_prime_factor (P:=3) (Q:=7) hN
      · intro p hprime hd hle
        rcases hsmall p hprime hle with rfl|rfl|rfl|rfl|rfl <;> tauto
      · intro r s h
        exact hodd T (by omega) ht r s (hsum.symm.trans (congrArg (·+11) h))
  obtain ⟨p,hp,hp11,hd⟩ := hprimes
  exact ⟨_,Nat.mul_pos (by positivity) hp.pos,
    prime_part v 11 p hp (hp.odd_of_ne_two (by omega)) hp11 (hres hd)⟩

end Eleven212844Ray

/-- A positive witness for the remaining even entry in the finite table. -/
theorem alt212844_norm : OeisA212844.a 55764612646 = 114 := by
  have bridge (n w : ℕ) (hw : w < n) (hc : (2 : ZMod n)^(n+2) = w) :
      OeisA212844.a n = w := by
    apply Nat.mod_eq_of_modEq _ hw
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hc
  apply bridge _ _ (by decide)
  change (2 : ZMod 55764612646)^55764612648 = 114
  reduce_mod_char

namespace Even212844Theory

/-- If every prime dividing `m` divides `b−1`, then `m` divides `b^m−1`. -/
private theorem smooth_lift (b : ℤ) (m : ℕ)
    (hs : ∀ p : ℕ, p.Prime → p ∣ m → (p:ℤ) ∣ b-1) : (m:ℤ) ∣ b^m-1 := by
  induction m using induction_on_primes with
  | zero => simp
  | one => simp
  | prime_mul p m hp ih =>
    have hm := ih fun q hq hd => hs q hq (hd.trans (dvd_mul_left m p))
    have hpb := hs p hp (dvd_mul_right p m)
    have hpow : (p:ℤ) ∣ b^m-1 := hpb.trans (by simpa using sub_dvd_pow_sub_pow b (1:ℤ) m)
    have H := mul_dvd_mul (dvd_geom_sum₂_self hpow) hm
    rw [geom_sum₂_mul, one_pow, ← pow_mul, Nat.mul_comm m p] at H
    exact_mod_cast H

/-- In particular all odd `3,5,17`-smooth multipliers work at index `8m`. -/
theorem smooth_eight {m : ℕ} (hm : 1 < m) (ho : Odd m)
    (hs : ∀ p : ℕ, p.Prime → p ∣ m → p ∣ 255) :
    2^(8*m+2) % (8*m) = 4*(m+1) := by
  have H := smooth_lift (256:ℤ) m (fun p hp hpm =>
    by norm_num; exact_mod_cast hs p hp hpm)
  have hper : (2:ℕ)^(8*m) ≡ 1 [MOD m] := by
    symm
    apply Nat.modEq_iff_dvd.mpr
    push_cast
    rwa [pow_mul, show (2:ℤ)^8=256 by decide]
  have h₂ : 2^(8*m+2) ≡ 0 [MOD 8] :=
    Nat.modEq_zero_iff_dvd.mpr (pow_dvd_pow 2 (show 3 ≤ 8*m+2 by omega))
  have hco : Nat.Coprime 8 m := ho.coprime_two_left.pow_left 3
  obtain ⟨t,ht⟩ := ho
  have htarg : 4*(m+1) ≡ 0 [MOD 8] := Nat.modEq_zero_iff_dvd.mpr ⟨t+1, by omega⟩
  have hₘ : 4*(m+1) ≡ 4 [MOD m] := by
    simp [Nat.mul_add, Nat.ModEq]
  apply Nat.mod_eq_of_modEq _ (by omega)
  apply (Nat.modEq_and_modEq_iff_modEq_mul hco).mp
  refine ⟨h₂.trans htarg.symm, ?_⟩
  rw [pow_add]
  exact (show 2^(8*m)*2^2 ≡ 4 [MOD m] from (hper.mul_right 4)).trans hₘ.symm

/-- Witnesses with unbounded odd parts at fixed dyadic exponent three, all
outside the one-prime criterion at the same exponent in the original reduction. -/
theorem outside_prime_part {t : ℕ} (ht : 3 ≤ t) :
    let h := (9^t+1)/2
    Odd h ∧ 128 < h ∧ 2^(8*9^t+2) % (8*9^t) = 2^3*h ∧
      ∀ p : ℕ, h < p → ¬ 2^(2^3+2-3) ≡ h [MOD p] := by
  intro h
  have hl : 729 ≤ 9^t := Nat.pow_le_pow_right (by decide : 0 < 9) ht
  have hmod : 9^t ≡ 1 [MOD 4] := by simpa using (show 9 ≡ 1 [MOD 4] by decide).pow t
  change 9^t % 4 = 1 at hmod
  have he := smooth_eight (m := 9^t) (by omega) ((by decide : Odd 9).pow) (by
    intro p hp hd
    have hp3 : p ∣ (3:ℕ) := hp.dvd_of_dvd_pow (show p ∣ 3^(2*t) by rwa [pow_mul])
    have he := (Nat.dvd_prime Nat.prime_three).mp hp3
    rcases he with he|he <;> simp [he])
  dsimp [h]
  refine ⟨⟨9^t/4,by omega⟩,by omega,by rw [he]; omega, ?_⟩
  intro p hp heq
  change (128:ℕ) ≡ (9^t+1)/2 [MOD p] at heq
  have := heq.eq_of_lt_of_lt (by omega) hp
  omega

/-- A second family addresses exponent one directly. At `n=2·5^t` the
residue is `n−4`, even though the one-prime criterion fails for all `t≥2`. -/
theorem smooth_two {t : ℕ} (ht : 2 ≤ t) :
    let h := 5^t-2
    Odd h ∧ 8 < h ∧ 2^(2*5^t+2) % (2*5^t) = 2*h ∧
      ∀ p : ℕ, h < p → ¬ 2^(2^1+2-1) ≡ h [MOD p] := by
  intro h
  let m := 5^t
  have hm : 25 ≤ m := Nat.pow_le_pow_right (by decide : 0 < 5) ht
  have ho : Odd m := (by decide : Odd 5).pow
  have hs := smooth_lift (-4:ℤ) m (by
    intro p hp hd
    have h5 : p ∣ 5 := hp.dvd_of_dvd_pow hd
    have he := (Nat.dvd_prime Nat.prime_five).mp h5
    rcases he with rfl|rfl <;> norm_num)
  rw [ho.neg_pow] at hs
  have hd : m ∣ 2^(2*m)+1 := by
    have H : (m:ℤ) ∣ 4^m+1 := by simpa only [show -(4:ℤ)^m-1 = -(4^m+1) by ring, dvd_neg] using hs
    rw [pow_mul]
    exact_mod_cast H
  have hdiv : 2*m ∣ 2^(2*m+2)+4 := by
    rw [pow_add, show 2^(2*m)*2^2+4 = 2*(2*(2^(2*m)+1)) by ring]
    exact Nat.mul_dvd_mul_left 2 (hd.trans (dvd_mul_left _ _))
  change Odd (m-2) ∧ 8 < m-2 ∧ 2^(2*m+2) % (2*m) = 2*(m-2) ∧ _
  obtain ⟨j,hj⟩ := ho
  refine ⟨⟨j-1,by omega⟩,by omega,?_,?_⟩
  · apply Nat.mod_eq_of_modEq _ (by omega)
    apply Nat.ModEq.add_right_cancel' 4
    rw [show 2*(m-2)+4 = 2*m by omega]
    exact hdiv.modEq_zero_nat.trans (show 2*m ≡ 0 [MOD 2*m] from Nat.modulus_modEq_zero).symm
  · intro p hp hbad
    change (8:ℕ) ≡ m-2 [MOD p] at hbad
    have := hbad.eq_of_lt_of_lt (by dsimp [h,m] at *; omega) hp
    omega

end Even212844Theory

/-- The odd part is at least the prime-part threshold. Two explicit families
already have witnesses at indices twice a power of five and eight times a
power of nine. -/
def H1 : Prop := ∀ h v : ℕ, Odd h → 13 ≤ h → 0 < v → 300 < 2^v*h →
    2^(2^v+2-v) ≤ h →
    ¬ (v = 1 ∧ ∃ t : ℕ, 2 ≤ t ∧ h = 5^t-2) →
    ¬ (v = 3 ∧ ∃ t : ℕ, 3 ≤ t ∧ h = (9^t+1)/2) →
    ∃ n : ℕ, 1 ≤ n ∧ OeisA212844.a n = 2^v*h

/-- Below the threshold, its difference with the odd part has no prime
factor larger than the odd part. -/
def H2 : Prop := ∀ h v : ℕ, Odd h → 13 ≤ h → 0 < v → 300 < 2^v*h →
    h < 2^(2^v+2-v) →
    (∀ p : ℕ, p.Prime → p ∣ 2^(2^v+2-v)-h → p ≤ h) →
    ∃ n : ℕ, 1 ≤ n ∧ OeisA212844.a n = 2^v*h

/-- Every even value up to 300 occurs, including the exceptional value 114. -/
theorem even_upto_300 (k : ℕ) (he : 2 ∣ k) (hk : k ≤ 300) :
    ∃ n : ℕ, 1 ≤ n ∧ OeisA212844.a n = k := by
  by_cases heq : k = 114
  · exact ⟨55764612646, by decide, heq ▸ alt212844_norm⟩
  apply OMA.R_OeisA212844_conjecture_R1.finite_witnesses k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem main : H1 → H2 → OMA.R_OeisA212844_conjecture_R1.H2 := by
  intro large small h ho h9
  refine ⟨0, ?_⟩
  intro v hv _ hprime _
  by_cases hk : 300 < 2^v*h
  · by_cases h11 : h = 11
    · subst h
      exact Eleven212844Ray.eleven_ray ElevenCert.odd_obstruction ElevenCert.even_obstruction v
    have h13 : 13 ≤ h := by obtain ⟨j, hj⟩ := ho; omega
    by_cases hle : 2^(2^v+2-v) ≤ h
    · by_cases h5 : v = 1 ∧ ∃ t : ℕ, 2 ≤ t ∧ h = 5^t-2
      · obtain ⟨rfl, t, ht, rfl⟩ := h5
        refine ⟨2*5^t, Nat.succ_le_of_lt (by positivity), ?_⟩
        simpa only [OeisA212844.a, pow_one] using (Even212844Theory.smooth_two ht).2.2.1
      by_cases h3 : v = 3 ∧ ∃ t : ℕ, 3 ≤ t ∧ h = (9^t+1)/2
      · obtain ⟨rfl, t, ht, rfl⟩ := h3
        exact ⟨8*9^t, Nat.succ_le_of_lt (by positivity), (Even212844Theory.outside_prime_part ht).2.2.1⟩
      exact large h v ho h13 hv hk hle h5 h3
    · have hlt := Nat.lt_of_not_ge hle
      apply small h v ho h13 hv hk hlt
      intro p hp hd
      by_contra! hgt
      exact hprime p hp hgt ((Nat.modEq_iff_dvd' hlt.le).2 hd).symm
  · exact even_upto_300 _ ((dvd_pow_self (2 : ℕ) hv.ne').trans (dvd_mul_right _ _)) (by omega)

end OMA.R_OeisA212844_conjecture_R1_H2_R1
