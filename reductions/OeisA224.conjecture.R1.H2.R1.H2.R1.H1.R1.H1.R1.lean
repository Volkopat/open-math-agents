import OMAReductions.R_OeisA224_conjecture_R1_H2_R1_H2_R1_H1_R1
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Prime.Basic


/-! Extract the ordered prime-power factors of an odd nonsquarefree number. -/

namespace OMA.Oeis224ThreePrime

open Finset

theorem sorted_prime_powers (n : ℕ) (ho : Odd n) (hcard : n.primeFactors.card = 3)
    (hnsq : ¬Squarefree n)
    (hsmall : ∃ p ∈ n.primeFactors, p < 16*(2^n.primeFactors.card)^3) :
    ∃ p q r e f g : ℕ,
      p.Prime ∧ q.Prime ∧ r.Prime ∧ Odd p ∧ Odd q ∧ Odd r ∧ p < q ∧ q < r ∧ p < 8192 ∧
      0 < e ∧ 0 < f ∧ 0 < g ∧ (1 < e ∨ 1 < f ∨ 1 < g) ∧ n = p^e * q^f * r^g := by
  have hn : n ≠ 0 := ho.pos.ne'
  have hlen : n.primeFactors.sort.length = 3 := by simpa using hcard
  obtain ⟨p, q, r, hlist⟩ := List.length_eq_three.mp hlen
  have hsorted := (sortedLT_sort n.primeFactors).pairwise
  rw [hlist] at hsorted
  have hpq : p < q := (List.pairwise_cons.mp hsorted).1 q (by simp)
  have hqr : q < r := (List.pairwise_cons.mp (List.pairwise_cons.mp hsorted).2).1 r (by simp)
  have hset : n.primeFactors = {p,q,r} := by
    ext x
    rw [← Finset.mem_sort (r := (· ≤ ·)), hlist]
    simp
  have hpMem : p ∈ n.primeFactors := by simp [hset]
  have hqMem : q ∈ n.primeFactors := by simp [hset]
  have hrMem : r ∈ n.primeFactors := by simp [hset]
  have hp := Nat.prime_of_mem_primeFactors hpMem
  have hq := Nat.prime_of_mem_primeFactors hqMem
  have hr := Nat.prime_of_mem_primeFactors hrMem
  have hodd {x : ℕ} (hx : x ∈ n.primeFactors) : Odd x := by
    apply (Nat.prime_of_mem_primeFactors hx).odd_of_ne_two
    intro he
    exact ho.not_two_dvd_nat (he ▸ Nat.dvd_of_mem_primeFactors hx)
  let e := n.factorization p
  let f := n.factorization q
  let g := n.factorization r
  have he : 0 < e := hp.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hpMem)
  have hf : 0 < f := hq.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hqMem)
  have hg : 0 < g := hr.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hrMem)
  have hrepeated : 1 < e ∨ 1 < f ∨ 1 < g := by
    have hw : ∃ t, 1 < n.factorization t := by
      by_contra! h
      exact hnsq ((Nat.squarefree_iff_factorization_le_one hn).mpr h)
    obtain ⟨t, ht⟩ := hw
    have hmem : t ∈ n.primeFactors := by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff]
      omega
    rw [hset] at hmem
    simp only [mem_insert, mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact Or.inl ht
    · exact Or.inr (Or.inl ht)
    · exact Or.inr (Or.inr ht)
  have hpBound : p < 8192 := by
    obtain ⟨t, htm, ht⟩ := hsmall
    rw [hcard] at ht
    change t < 8192 at ht
    rw [hset] at htm
    simp only [mem_insert, mem_singleton] at htm
    rcases htm with rfl | rfl | rfl <;> omega
  refine ⟨p,q,r,e,f,g,hp,hq,hr,hodd hpMem,hodd hqMem,hodd hrMem,hpq,hqr,hpBound,
    he,hf,hg,hrepeated,?_⟩
  calc
    n = ∏ t ∈ n.primeFactors, t ^ n.factorization t := Nat.prod_primeFactors_pow_factorization hn
    _ = _ := by
      rw [hset]
      simp [Finset.prod_insert, hpq.ne, (hpq.trans hqr).ne, hqr.ne, e, f, g, mul_assoc]

end OMA.Oeis224ThreePrime


/-! Express the congruence as an integer equation and clear the count denominators. -/

namespace OMA.Oeis224ThreePrime

theorem quotient_equation {n A : ℕ} (hn : 1 < n)
    (h : n^2 ≡ 1 [MOD A*(A-1)]) :
    ∃ k : ℕ, n^2 = A*(A-1)*k+1 := by
  have hN : 1 ≤ n^2 := (Nat.one_lt_pow (by decide) hn).le
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hN).mp h.symm
  exact ⟨k, by omega⟩

theorem clear_count_equation {n A D C k : ℕ}
    (hcount : D*A = C) (h : n^2 = A*(A-1)*k+1) :
    D^2*(n^2-1) = k*C*(C-D) := by
  have hsub : n^2-1 = A*(A-1)*k := by omega
  have hcountSub : D*(A-1) = C-D := by
    rw [Nat.mul_sub_left_distrib, hcount, mul_one]
  rw [hsub, ← hcountSub, ← hcount]
  ring

end OMA.Oeis224ThreePrime


namespace OMA.A224QuotientBounds

/-- The cleared prime-power count includes an additive margin of at least one half. -/
theorem factor_count_lower (p e a r : ℕ) (hr : r ≤ p)
    (h : 2 * (p + 1) * a = p * p ^ e + (if Even e then p + 2 else 2 * p + 1)) :
    r * p ^ e + (r + 1) ≤ 2 * (r + 1) * a := by
  let correction := if Even e then p + 2 else 2 * p + 1
  have hcorrection : p + 1 ≤ correction := by
    dsimp only [correction]
    split <;> omega
  have hcoef : (p + 1) * r ≤ (r + 1) * p := by
    calc
      (p + 1) * r = p * r + r := by ring
      _ ≤ p * r + p := Nat.add_le_add_left hr _
      _ = (r + 1) * p := by ring
  apply Nat.le_of_mul_le_mul_left (c := p + 1) _ (Nat.succ_pos p)
  calc
    (p + 1) * (r * p ^ e + (r + 1)) = ((p + 1) * r) * p ^ e + (r + 1) * (p + 1) := by ring
    _ ≤ ((r + 1) * p) * p ^ e + (r + 1) * correction :=
      Nat.add_le_add (Nat.mul_le_mul_right _ hcoef) (Nat.mul_le_mul_left _ hcorrection)
    _ = (r + 1) * (p * p ^ e + correction) := by ring
    _ = (p + 1) * (2 * (r + 1) * a) := by rw [← h]; ring

/-- Distinct increasing odd prime bases give lower bounds 3, 5, and 7. -/
theorem ordered_bounds {p q r : ℕ} (hp : p.Prime) (hop : Odd p) (hoq : Odd q)
    (hor : Odd r) (hpq : p < q) (hqr : q < r) : 3 ≤ p ∧ 5 ≤ q ∧ 7 ≤ r := by
  obtain ⟨i, hi⟩ := hop
  obtain ⟨j, hj⟩ := hoq
  obtain ⟨k, hk⟩ := hor
  have hp2 := hp.two_le
  omega

/-- Combining the ratios at 3, 5 and 7 absorbs the subtraction of one from the full count. -/
theorem scaled_count_lower (u v w a b c : ℕ)
    (hv : 5 ≤ v) (hw : 7 ≤ w)
    (ha : 3 * u + 4 ≤ 8 * a) (hb : 5 * v ≤ 12 * b) (hc : 7 * w ≤ 16 * c) :
    105 * (u * v * w) ≤ 1536 * (a * b * c - 1) := by
  let A := a * b * c
  let N := u * v * w
  have hscaled : 105 * N + 140 * (v * w) ≤ 1536 * A := by
    calc
      105 * N + 140 * (v * w) = (3 * u + 4) * (5 * v) * (7 * w) := by dsimp [N]; ring
      _ ≤ (8 * a) * (12 * b) * (16 * c) := Nat.mul_le_mul (Nat.mul_le_mul ha hb) hc
      _ = 1536 * A := by dsimp [A]; ring
  have hmargin : 1536 ≤ 140 * (v * w) :=
    (by decide : 1536 ≤ 140 * (5 * 7)).trans
      (Nat.mul_le_mul_left _ (Nat.mul_le_mul hv hw))
  change 105 * N ≤ 1536 * (A - 1)
  omega

/-- The quotient bound applies whether or not one of the exponents exceeds one. -/
theorem quotient_lt_214 (u v w a b c k : ℕ)
    (hv : 5 ≤ v) (hw : 7 ≤ w)
    (ha : 3 * u + 4 ≤ 8 * a) (hb : 5 * v ≤ 12 * b) (hc : 7 * w ≤ 16 * c)
    (heq : (u * v * w) ^ 2 = k * (a * b * c) * (a * b * c - 1) + 1) :
    k < 214 := by
  let A := a * b * c
  let N := u * v * w
  change N ^ 2 = k * A * (A - 1) + 1 at heq
  have hlower : 105 * N ≤ 1536 * (A - 1) := scaled_count_lower u v w a b c hv hw ha hb hc
  have hlower' : 105 * N ≤ 1536 * A :=
    hlower.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have hsquare := Nat.mul_le_mul hlower' hlower
  have hprev : k * A * (A - 1) < N ^ 2 := by rw [heq]; exact Nat.lt_succ_self _
  have hcross : (k * 105 ^ 2) * N ^ 2 < 1536 ^ 2 * N ^ 2 := by
    calc
      (k * 105 ^ 2) * N ^ 2 = k * ((105 * N) * (105 * N)) := by ring
      _ ≤ k * ((1536 * A) * (1536 * (A - 1))) := Nat.mul_le_mul_left k hsquare
      _ = 1536 ^ 2 * (k * A * (A - 1)) := by ring
      _ < 1536 ^ 2 * N ^ 2 := Nat.mul_lt_mul_of_pos_left hprev (by decide)
  have hk := Nat.lt_of_mul_lt_mul_right hcross
  norm_num at hk
  omega

/-- The density of squares at an odd prime power is at most the density at its prime base. -/
theorem factor_count_upper (p e a r : ℕ) (hp : 0 < p) (he : 0 < e) (hr : r ≤ p)
    (h : 2 * (p + 1) * a = p * p ^ e + (if Even e then p + 2 else 2 * p + 1)) :
    2 * r * a ≤ (r + 1) * p ^ e := by
  let correction := if Even e then p + 2 else 2 * p + 1
  have hcorrection : correction ≤ 2 * p + 1 := by
    dsimp only [correction]
    split <;> omega
  have hcoeff : r * (2 * p + 1) ≤ (p + r + 1) * p := by
    calc
      r * (2 * p + 1) = r * p + r * (p + 1) := by ring
      _ ≤ r * p + p * (p + 1) := Nat.add_le_add_left (Nat.mul_le_mul_right _ hr) _
      _ = (p + r + 1) * p := by ring
  have hterm : r * correction ≤ (p + r + 1) * p ^ e :=
    (Nat.mul_le_mul_left r hcorrection).trans
      (hcoeff.trans (Nat.mul_le_mul_left _ (Nat.le_pow he)))
  apply Nat.le_of_mul_le_mul_left (c := p + 1) _ (Nat.succ_pos p)
  calc
    (p + 1) * (2 * r * a) = r * (2 * (p + 1) * a) := by ring
    _ = r * (p * p ^ e + correction) := by rw [h]
    _ = r * p * p ^ e + r * correction := by ring
    _ ≤ r * p * p ^ e + (p + r + 1) * p ^ e := Nat.add_le_add_left hterm _
    _ = (p + 1) * ((r + 1) * p ^ e) := by ring

/-- At a repeated odd prime factor, at most half the residue classes are squares. -/
theorem repeated_factor_upper (p e a : ℕ) (hp : 3 ≤ p) (he : 2 ≤ e)
    (h : 2 * (p + 1) * a = p * p ^ e + (if Even e then p + 2 else 2 * p + 1)) :
    2 * a ≤ p ^ e := by
  let correction := if Even e then p + 2 else 2 * p + 1
  have hcorrection : correction ≤ 2 * p + 1 := by
    dsimp only [correction]
    split <;> omega
  have hsmall : 2 * p + 1 ≤ p ^ 2 := by
    have hmul := Nat.mul_le_mul_left p hp
    simp only [pow_two, Nat.mul_comm p 3] at hmul ⊢
    omega
  have hpower := Nat.pow_le_pow_right (show 0 < p by omega) he
  have hterm := hcorrection.trans (hsmall.trans hpower)
  apply Nat.le_of_mul_le_mul_left (c := p + 1) _ (Nat.succ_pos p)
  calc
    (p + 1) * (2 * a) = 2 * (p + 1) * a := by ring
    _ = p * p ^ e + correction := h
    _ ≤ p * p ^ e + p ^ e := Nat.add_le_add_left hterm _
    _ = (p + 1) * p ^ e := by ring

private theorem repeated_first_scaled (u v w a b c : ℕ)
    (ha : 2 * a ≤ u) (hb : 6 * b ≤ 4 * v) (hc : 10 * c ≤ 6 * w) :
    5 * (a * b * c) ≤ u * v * w := by
  apply Nat.le_of_mul_le_mul_left (c := 24) _ (by decide)
  calc
    24 * (5 * (a * b * c)) = (2 * a) * (6 * b) * (10 * c) := by ring
    _ ≤ u * (4 * v) * (6 * w) := Nat.mul_le_mul (Nat.mul_le_mul ha hb) hc
    _ = 24 * (u * v * w) := by ring

/-- A repeated factor and the other two densities bound the total count by one fifth. -/
theorem scaled_count_upper (u v w a b c : ℕ)
    (ha : 6 * a ≤ 4 * u) (hb : 10 * b ≤ 6 * v) (hc : 10 * c ≤ 6 * w)
    (hrep : 2 * a ≤ u ∨ 2 * b ≤ v ∨ 2 * c ≤ w) :
    5 * (a * b * c) ≤ u * v * w := by
  rcases hrep with h | h | h
  · exact repeated_first_scaled u v w a b c h (by omega) hc
  · simpa only [mul_comm, mul_left_comm, mul_assoc] using
      repeated_first_scaled v u w b a c h ha hc
  · simpa only [mul_comm, mul_left_comm, mul_assoc] using
      repeated_first_scaled w u v c a b h ha hb

/-- The density bound of one fifth forces the integer quotient to exceed 25. -/
theorem quotient_gt_25 {n a k : ℕ}
    (hn : 1 < n) (hcount : 5 * a ≤ n)
    (heq : n ^ 2 = k * a * (a - 1) + 1) : 25 < k := by
  have hnpow : 1 < n ^ 2 := Nat.one_lt_pow (by decide) hn
  have ha : 0 < a := by
    by_contra! h
    have hzero : a = 0 := by omega
    simp [hzero] at heq
    omega
  by_contra! hk
  have hstep : 25 * a * (a - 1) + 1 < (5 * a) ^ 2 := by
    calc
      25 * a * (a - 1) + 1 < 25 * a * (a - 1) + 25 * a :=
        Nat.add_lt_add_left (by omega) _
      _ = 25 * a * ((a - 1) + 1) := by ring
      _ = (5 * a) ^ 2 := by rw [Nat.sub_add_cancel ha]; ring
  exact (lt_irrefl (n ^ 2)) (calc
    n ^ 2 = k * a * (a - 1) + 1 := heq
    _ ≤ 25 * a * (a - 1) + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hk)) _
    _ < (5 * a) ^ 2 := hstep
    _ ≤ n ^ 2 := Nat.pow_le_pow_left hcount _)

/-- The ancestral square obstruction applies throughout the quotient range 26 through 213. -/
theorem quotient_nonsquare {n a k : ℕ} (hn : 105 ≤ n) (ha : 0 < a)
    (hlo : 25 < k) (hhi : k < 214) (heq : n ^ 2 = k * a * (a - 1) + 1)
    (impossible_square : ∀ {N A t K : ℕ}, 0 < N → 0 < A → t ^ 2 = K →
      4 < K → K < 4 * N + 5 → N ^ 2 = A * (A - 1) * K + 1 → False) :
    ¬ IsSquare k := by
  rintro ⟨t, ht⟩
  have hsq : t ^ 2 = k := by simpa only [pow_two] using ht.symm
  apply impossible_square (show 0 < n by omega) ha hsq (by omega) (by omega)
  rw [heq]
  ring

end OMA.A224QuotientBounds


/-! Normalize the nonsquarefree three-prime case to bounded integer equations. -/

namespace OMA.R_OeisA224_conjecture_R1_H2_R1_H2_R1_H1_R1_H1_R1

open OeisA224 OMA.Oeis224ThreePrime OMA.A224QuotientBounds

private theorem three_counts {p q r e f g : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpq : p < q) (hqr : q < r) :
    a (p^e*q^f*r^g) = a (p^e) * a (q^f) * a (r^g) := by
  have hPQ := ((Nat.coprime_primes hp hq).mpr hpq.ne).pow e f
  have hPR := ((Nat.coprime_primes hp hr).mpr (hpq.trans hqr).ne).pow e g
  have hQR := ((Nat.coprime_primes hq hr).mpr hqr.ne).pow f g
  have hPQR : (p^e*q^f).Coprime (r^g) := Nat.coprime_mul_iff_left.mpr ⟨hPR, hQR⟩
  have he : 0 < p^e := pow_pos hp.pos e
  have hf : 0 < q^f := pow_pos hq.pos f
  have hg : 0 < r^g := pow_pos hr.pos g
  rw [OMA.R_OeisA224_conjecture_R1_H2_R1.count_coprime (Nat.mul_pos he hf) hg hPQR,
    OMA.R_OeisA224_conjecture_R1_H2_R1.count_coprime he hf hPQ]

/-- Exactly one of the three prime exponents is greater than one. -/
def H1 : Prop := ∀ p q r e f g k : ℕ, p.Prime → q.Prime → r.Prime →
  3 ≤ p → p < q → q < r → p < 8192 → 0 < e → 0 < f → 0 < g →
  (1 < e ∨ 1 < f ∨ 1 < g) → (f=1 ∧ g=1 ∨ e=1 ∧ g=1 ∨ e=1 ∧ f=1) →
  25 < k → k < 214 → ¬IsSquare k →
  let D := 8*(p+1)*(q+1)*(r+1)
  let C := (p*p^e+(if Even e then p+2 else 2*p+1)) *
    (q*q^f+(if Even f then q+2 else 2*q+1)) * (r*r^g+(if Even g then r+2 else 2*r+1))
  D^2*((p^e*q^f*r^g)^2-1) ≠ k*C*(C-D)

/-- At least two prime exponents are two, and no exponent exceeds two. -/
def H2 : Prop := ∀ p q r e f g k : ℕ, p.Prime → q.Prime → r.Prime →
  3 ≤ p → p < q → q < r → p < 8192 → 0 < e → 0 < f → 0 < g →
  ¬(f=1 ∧ g=1 ∨ e=1 ∧ g=1 ∨ e=1 ∧ f=1) → (e≤2 ∧ f≤2 ∧ g≤2) →
  25 < k → k < 214 → ¬IsSquare k →
  let D := 8*(p+1)*(q+1)*(r+1)
  let C := (p*p^e+(if Even e then p+2 else 2*p+1)) *
    (q*q^f+(if Even f then q+2 else 2*q+1)) * (r*r^g+(if Even g then r+2 else 2*r+1))
  D^2*((p^e*q^f*r^g)^2-1) ≠ k*C*(C-D)

/-- At least two exponents are repeated, and one exceeds two. -/
def H3 : Prop := ∀ p q r e f g k : ℕ, p.Prime → q.Prime → r.Prime →
  3 ≤ p → p < q → q < r → p < 8192 → 0 < e → 0 < f → 0 < g →
  ¬(f=1 ∧ g=1 ∨ e=1 ∧ g=1 ∨ e=1 ∧ f=1) → (2<e ∨ 2<f ∨ 2<g) →
  25 < k → k < 214 → ¬IsSquare k →
  let D := 8*(p+1)*(q+1)*(r+1)
  let C := (p*p^e+(if Even e then p+2 else 2*p+1)) *
    (q*q^f+(if Even f then q+2 else 2*q+1)) * (r*r^g+(if Even g then r+2 else 2*r+1))
  D^2*((p^e*q^f*r^g)^2-1) ≠ k*C*(C-D)

theorem main : H1 → H2 → H3 → OMA.R_OeisA224_conjecture_R1_H2_R1_H2_R1_H1_R1.H1 := by
  intro h1 h2 h3 n ho hcard hnsq hsmall hmod
  obtain ⟨p,q,r,e,f,g,hp,hq,hr,hop,hoq,hor,hpq,hqr,hpBound,he,hf,hg,hrep,hn⟩ :=
    sorted_prime_powers n ho hcard hnsq hsmall
  obtain ⟨hp3,hq5,hr7⟩ := ordered_bounds hp hop hoq hor hpq hqr
  let U := p^e
  let V := q^f
  let W := r^g
  let A := a U * a V * a W
  let D := 8*(p+1)*(q+1)*(r+1)
  let C := (p*U+(if Even e then p+2 else 2*p+1)) *
    (q*V+(if Even f then q+2 else 2*q+1)) * (r*W+(if Even g then r+2 else 2*r+1))
  have hU : 3 ≤ U := hp3.trans (Nat.le_pow he)
  have hV : 5 ≤ V := hq5.trans (Nat.le_pow hf)
  have hW : 7 ≤ W := hr7.trans (Nat.le_pow hg)
  have hN105 : 105 ≤ U*V*W := Nat.mul_le_mul (Nat.mul_le_mul hU hV) hW
  have hN : 1 < n := by rw [hn]; exact (by decide : 1 < 105).trans_le hN105
  obtain ⟨k, hk⟩ := quotient_equation hN hmod
  have hA : a n = A := by rw [hn, three_counts hp hq hr hpq hqr]
  have hRaw : (U*V*W)^2 = A*(A-1)*k+1 := by
    rw [hA, hn] at hk
    exact hk
  have hEq : (U*V*W)^2 = k*A*(A-1)+1 := hRaw.trans (by ring)
  have hpc := OMA.RoughSquares.cleared p e hp hop
  have hqc := OMA.RoughSquares.cleared q f hq hoq
  have hrc := OMA.RoughSquares.cleared r g hr hor
  have hUp : k < 214 := quotient_lt_214 U V W (a U) (a V) (a W) k hV hW
    (factor_count_lower p e (a U) 3 hp3 hpc)
    (by have h := factor_count_lower q f (a V) 5 hq5 hqc; omega)
    (by have h := factor_count_lower r g (a W) 7 hr7 hrc; omega) hEq
  have hRepCount : 2*a U ≤ U ∨ 2*a V ≤ V ∨ 2*a W ≤ W := by
    rcases hrep with h | h | h
    · exact Or.inl (repeated_factor_upper p e (a U) hp3 h hpc)
    · exact Or.inr (Or.inl (repeated_factor_upper q f (a V) (by omega) h hqc))
    · exact Or.inr (Or.inr (repeated_factor_upper r g (a W) (by omega) h hrc))
  have hLowerCount : 5*A ≤ U*V*W := scaled_count_upper U V W (a U) (a V) (a W)
    (factor_count_upper p e (a U) 3 hp.pos he hp3 hpc)
    (factor_count_upper q f (a V) 5 hq.pos hf hq5 hqc)
    (factor_count_upper r g (a W) 5 hr.pos hg (by omega) hrc) hRepCount
  have hPosN : 1 < U*V*W := (by decide : 1 < 105).trans_le hN105
  have hLo := quotient_gt_25 hPosN hLowerCount hEq
  have hPosA : 0 < A := by
    by_contra! hzero
    have hA0 : A = 0 := by omega
    simp [hA0] at hEq
    have h := Nat.one_lt_pow (by decide : 2 ≠ 0) hPosN
    omega
  have hNonSquare := quotient_nonsquare hN105 hPosA hLo hUp hEq OMA.RoughSquares.impossible_square
  have hD : D*A = C := calc
    _ = (2*(p+1)*a U)*(2*(q+1)*a V)*(2*(r+1)*a W) := by
      dsimp only [D,A]
      ring
    _ = _ := by
      dsimp only [C]
      rw [←hpc, ←hqc, ←hrc]
  have hCleared := clear_count_equation hD hRaw
  by_cases hOne : f=1 ∧ g=1 ∨ e=1 ∧ g=1 ∨ e=1 ∧ f=1
  · exact h1 p q r e f g k hp hq hr hp3 hpq hqr hpBound he hf hg hrep hOne hLo hUp hNonSquare hCleared
  by_cases hCube : e≤2 ∧ f≤2 ∧ g≤2
  · exact h2 p q r e f g k hp hq hr hp3 hpq hqr hpBound he hf hg hOne hCube hLo hUp hNonSquare hCleared
  have hHigh : 2<e ∨ 2<f ∨ 2<g := by omega
  exact h3 p q r e f g k hp hq hr hp3 hpq hqr hpBound he hf hg hOne hHigh hLo hUp hNonSquare hCleared

end OMA.R_OeisA224_conjecture_R1_H2_R1_H2_R1_H1_R1_H1_R1
