import OMAStatements.S_oeis_a307091
import Mathlib

/-!
OEIS A307091: a(n) = Sum_{k=0..floor(n/2)} (-1)^k * binomial(n,2k)^2.
Bala's supercongruence a(n p^r) = a(n p^(r-1)) modulo p^(2r) for odd primes p and n, r >= 1.

Write N = p M with M = n p^(r-1), so p^r divides N.

1. The sum defining a(n) may be extended to any range k < K with K >= n/2 + 1 (`a_eq_sum`).
2. If m divides f(k) for every k not divisible by p, then m divides
   Sum_{k < pK} f(k) - Sum_{k < K} f(pk) (`sum_block`).
3. p^r divides C(N, j) when p does not divide j (`choose_dvd_of_not_dvd`), so the terms of a(N)
   with p not dividing k vanish modulo p^(2r).
4. G(p, D, B) is the product of the factors prime to p of (pD+1)(pD+2)...(pD+pB). Splitting the
   rising factorial in blocks of length p gives
   (pB)! C(pD+pB, pB) = G(p,D,B) p^B B! C(D+B, B) (`star`), hence
   C(p(D+B), pB) G(p,0,B) = C(D+B, B) G(p,D,B) (`choose_mul_G`).
5. The reflection j -> pB - j and (pD+j)(pD+pB-j) = j(pB-j) + p^2 D (D+B) give
   G(p,D,B)^2 = G(p,0,B)^2 modulo p^2 D (D+B) (`G_modEq`).
6. With x = C(pA, pB), y = C(A, B), A = D + B and y D = A C(A-1, B):
   (x^2 - y^2) G(p,0,B)^2 = y^2 (G(p,D,B)^2 - G(p,0,B)^2) is divisible by (pA)^2, hence by p^(2r),
   and G(p,0,B) is prime to p, so p^(2r) divides x^2 - y^2 (`choose_sq_sub`).
7. Since (-1)^(pk) = (-1)^k for odd p, the terms k = p k' of a(N) match the terms of a(M).
-/

open Finset

namespace A307091

/-- The defining sum may be extended: the extra binomial coefficients vanish. -/
private lemma a_eq_sum (n K : ℕ) (hK : n / 2 + 1 ≤ K) :
    OMA.S_oeis_a307091.a n
      = ∑ k ∈ range K, (-1 : ℤ) ^ k * ((n.choose (2 * k) : ℕ) : ℤ) ^ 2 := by
  unfold OMA.S_oeis_a307091.a
  apply Finset.sum_subset (Finset.range_subset_range.2 hK)
  intro k _ hk
  rw [Finset.mem_range, not_lt] at hk
  have h : n < 2 * k := by omega
  rw [Nat.choose_eq_zero_of_lt h]
  simp

/-- Only the indices divisible by `p` matter modulo `m` if the other terms vanish modulo `m`. -/
private lemma sum_block (q : ℕ) (m : ℤ) (f : ℕ → ℤ)
    (hf : ∀ k, ¬ (q + 1) ∣ k → m ∣ f k) (K : ℕ) :
    m ∣ ∑ k ∈ range ((q + 1) * K), f k - ∑ k ∈ range K, f ((q + 1) * k) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Nat.mul_succ, Finset.sum_range_add,
      Finset.sum_range_succ (fun k => f ((q + 1) * k)) K,
      Finset.sum_range_succ' (fun x => f ((q + 1) * K + x)) q]
    have h1 : m ∣ ∑ x ∈ range q, f ((q + 1) * K + (x + 1)) := by
      apply Finset.dvd_sum
      intro x hx
      apply hf
      rw [Finset.mem_range] at hx
      intro hdvd
      have h2 : (q + 1) ∣ x + 1 := (Nat.dvd_add_right (dvd_mul_right _ _)).1 hdvd
      have h3 := Nat.le_of_dvd (Nat.succ_pos x) h2
      omega
    have e : ∑ k ∈ range ((q + 1) * K), f k
          + (∑ x ∈ range q, f ((q + 1) * K + (x + 1)) + f ((q + 1) * K + 0))
          - (∑ k ∈ range K, f ((q + 1) * k) + f ((q + 1) * K))
        = (∑ k ∈ range ((q + 1) * K), f k - ∑ k ∈ range K, f ((q + 1) * k))
          + ∑ x ∈ range q, f ((q + 1) * K + (x + 1)) := by
      rw [Nat.add_zero]; ring
    rw [e]
    exact dvd_add ih h1

/-- `p ^ r ∣ N` and `p ∤ j` imply `p ^ r ∣ C(N, j)`. -/
private lemma choose_dvd_of_not_dvd {p : ℕ} (hp : p.Prime) {r N j : ℕ} (hN : p ^ r ∣ N)
    (hj : ¬ p ∣ j) : p ^ r ∣ N.choose j := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 :=
    Nat.exists_eq_succ_of_ne_zero (by rintro rfl; exact hj (dvd_zero p))
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · simp
  obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := Nat.exists_eq_succ_of_ne_zero hNpos.ne'
  have h := Nat.add_one_mul_choose_eq N' j'
  have h2 : p ^ r ∣ (N' + 1).choose (j' + 1) * (j' + 1) := by
    rw [← h]; exact Dvd.dvd.mul_right hN _
  have hcop : Nat.Coprime (p ^ r) (j' + 1) :=
    Nat.Coprime.pow_left r ((Nat.Prime.coprime_iff_not_dvd hp).2 hj)
  exact hcop.dvd_of_dvd_mul_right h2

/-- The factors prime to `p` of `(pD+1)(pD+2)...(pD+pB)`. -/
private def G (p D B : ℕ) : ℕ :=
  ∏ b ∈ range B, ∏ i ∈ range (p - 1), (p * D + p * b + i + 1)

private lemma prod_range_mul_block (g : ℕ → ℕ) (p B : ℕ) :
    ∏ j ∈ range (p * B), g j = ∏ b ∈ range B, ∏ i ∈ range p, g (p * b + i) := by
  induction B with
  | zero => simp
  | succ B ih => rw [Nat.mul_succ, Finset.prod_range_add, ih, Finset.prod_range_succ]

/-- Splitting the rising factorial `(pD+1)...(pD+pB)` in blocks of length `p = q + 1`. -/
private lemma star (q D B : ℕ) :
    ((q + 1) * B).factorial * ((q + 1) * D + (q + 1) * B).choose ((q + 1) * B)
      = G (q + 1) D B * ((q + 1) ^ B * (B.factorial * (D + B).choose B)) := by
  rw [← Nat.ascFactorial_eq_factorial_mul_choose, Nat.ascFactorial_eq_prod_range,
    prod_range_mul_block]
  simp only [Finset.prod_range_succ, Finset.prod_mul_distrib]
  have h2 : ∏ b ∈ range B, ((q + 1) * D + 1 + ((q + 1) * b + q))
      = (q + 1) ^ B * (B.factorial * (D + B).choose B) := by
    calc ∏ b ∈ range B, ((q + 1) * D + 1 + ((q + 1) * b + q))
        = ∏ b ∈ range B, ((q + 1) * (D + 1 + b)) :=
          Finset.prod_congr rfl (fun b _ => by ring)
      _ = (q + 1) ^ B * ∏ b ∈ range B, (D + 1 + b) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
      _ = (q + 1) ^ B * (B.factorial * (D + B).choose B) := by
          rw [← Nat.ascFactorial_eq_prod_range, Nat.ascFactorial_eq_factorial_mul_choose]
  have h1 : ∏ b ∈ range B, ∏ i ∈ range q, ((q + 1) * D + 1 + ((q + 1) * b + i))
      = G (q + 1) D B := by
    unfold G
    rw [Nat.add_sub_cancel]
    exact Finset.prod_congr rfl (fun b _ => Finset.prod_congr rfl (fun i _ => by ring))
  rw [h1, h2]

/-- `C(p(D+B), pB) * G(p,0,B) = C(D+B, B) * G(p,D,B)` for `p = q + 1`. -/
private lemma choose_mul_G (q D B : ℕ) :
    ((q + 1) * D + (q + 1) * B).choose ((q + 1) * B) * G (q + 1) 0 B
      = (D + B).choose B * G (q + 1) D B := by
  have h1 := star q D B
  have h0 := star q 0 B
  simp only [Nat.mul_zero, Nat.zero_add, Nat.choose_self, Nat.mul_one] at h0
  have hpos : 0 < (q + 1) ^ B * B.factorial := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc ((q + 1) * D + (q + 1) * B).choose ((q + 1) * B) * G (q + 1) 0 B
        * ((q + 1) ^ B * B.factorial)
      = ((q + 1) * B).factorial * ((q + 1) * D + (q + 1) * B).choose ((q + 1) * B) := by
        rw [h0]; ring
    _ = (D + B).choose B * G (q + 1) D B * ((q + 1) ^ B * B.factorial) := by
        rw [h1]; ring

private lemma prod_reflect2 (h : ℕ → ℕ → ℕ) (B q : ℕ) :
    ∏ b ∈ range B, ∏ i ∈ range q, h b i
      = ∏ b ∈ range B, ∏ i ∈ range q, h (B - 1 - b) (q - 1 - i) := by
  calc ∏ b ∈ range B, ∏ i ∈ range q, h b i
      = ∏ b ∈ range B, ∏ i ∈ range q, h (B - 1 - b) i :=
        (Finset.prod_range_reflect (fun b => ∏ i ∈ range q, h b i) B).symm
    _ = ∏ b ∈ range B, ∏ i ∈ range q, h (B - 1 - b) (q - 1 - i) :=
        Finset.prod_congr rfl
          (fun b _ => (Finset.prod_range_reflect (fun i => h (B - 1 - b) i) q).symm)

private lemma G_sq (p D B : ℕ) :
    G p D B * G p D B
      = ∏ b ∈ range B, ∏ i ∈ range (p - 1),
          ((p * D + p * b + i + 1) * (p * D + p * (B - 1 - b) + (p - 1 - 1 - i) + 1)) := by
  have h := prod_reflect2 (fun b i => p * D + p * b + i + 1) B (p - 1)
  simp only [Finset.prod_mul_distrib]
  rw [← h]
  rfl

private lemma pair_identity (D b c i e : ℕ) :
    ((i + 1 + e + 1) * D + (i + 1 + e + 1) * b + i + 1)
        * ((i + 1 + e + 1) * D + (i + 1 + e + 1) * c + e + 1)
      = ((i + 1 + e + 1) * b + i + 1) * ((i + 1 + e + 1) * c + e + 1)
        + (i + 1 + e + 1) ^ 2 * D * (D + (b + 1 + c)) := by
  ring

/-- `G(p,D,B)^2 = G(p,0,B)^2` modulo `p^2 D (D+B)`. -/
private lemma G_modEq (p D B : ℕ) :
    G p D B * G p D B ≡ G p 0 B * G p 0 B [MOD p ^ 2 * D * (D + B)] := by
  rw [G_sq p D B, G_sq p 0 B]
  apply Nat.ModEq.prod
  intro b hb
  apply Nat.ModEq.prod
  intro i hi
  rw [Finset.mem_range] at hb hi
  obtain ⟨c, rfl⟩ : ∃ c, B = b + 1 + c := ⟨B - 1 - b, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, p = i + 1 + e + 1 := ⟨p - 1 - 1 - i, by omega⟩
  have h1 : b + 1 + c - 1 - b = c := by omega
  have h2 : i + 1 + e + 1 - 1 - 1 - i = e := by omega
  rw [h1, h2, Nat.ModEq, pair_identity D b c i e, Nat.add_mod_right]
  simp only [Nat.mul_zero, Nat.zero_add]

private lemma G_coprime {p : ℕ} (hp : p.Prime) (B : ℕ) : Nat.Coprime p (G p 0 B) := by
  unfold G
  apply Nat.Coprime.prod_right
  intro b _
  apply Nat.Coprime.prod_right
  intro i hi
  rw [Finset.mem_range] at hi
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  have h2 : p ∣ i + 1 := by
    have h3 : p * 0 + p * b + i + 1 = p * b + (i + 1) := by ring
    rw [h3] at hdvd
    exact (Nat.dvd_add_right (dvd_mul_right _ _)).1 hdvd
  have h4 := Nat.le_of_dvd (Nat.succ_pos i) h2
  omega

/-- The key congruence between squares of binomial coefficients. -/
private lemma choose_sq_sub {p : ℕ} (hp : p.Prime) (r A B : ℕ) (hA : p ^ r ∣ p * A) :
    ((p : ℤ) ^ (2 * r))
      ∣ ((((p * A).choose (p * B) : ℕ) : ℤ) ^ 2 - ((A.choose B : ℕ) : ℤ) ^ 2) := by
  rcases lt_or_ge A B with hAB | hAB
  · rw [Nat.choose_eq_zero_of_lt hAB,
      Nat.choose_eq_zero_of_lt (Nat.mul_lt_mul_of_pos_left hAB hp.pos)]
    simp
  obtain ⟨D, rfl⟩ : ∃ D, A = D + B := ⟨A - B, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have hxy : ((q + 1) * (D + B)).choose ((q + 1) * B) * G (q + 1) 0 B
      = (D + B).choose B * G (q + 1) D B := by
    rw [Nat.mul_add]; exact choose_mul_G q D B
  have hmod := G_modEq (q + 1) D B
  have hcop := G_coprime hp B
  obtain ⟨c, hc⟩ : ∃ c, (D + B).choose B * D = (D + B) * c := by
    rcases Nat.eq_zero_or_pos D with rfl | hD
    · exact ⟨0, by simp⟩
    · obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := Nat.exists_eq_succ_of_ne_zero hD.ne'
      refine ⟨(d + B).choose B, ?_⟩
      have h := Nat.choose_mul_succ_eq (d + B) B
      have e1 : d + B + 1 - B = d + 1 := by omega
      have e2 : d + 1 + B = d + B + 1 := by ring
      rw [e1] at h
      rw [e2, ← h]; ring
  generalize ((q + 1) * (D + B)).choose ((q + 1) * B) = x at hxy ⊢
  generalize (D + B).choose B = y at hxy hc ⊢
  generalize G (q + 1) 0 B = P at hxy hmod hcop
  generalize G (q + 1) D B = Q at hxy hmod
  have hdiv : ((((q + 1) * (D + B) : ℕ) : ℤ)) ^ 2 ∣ ((x : ℤ) ^ 2 - (y : ℤ) ^ 2) * (P : ℤ) ^ 2 := by
    have hxy' : (x : ℤ) * P = y * Q := by exact_mod_cast hxy
    have e1 : ((x : ℤ) ^ 2 - (y : ℤ) ^ 2) * (P : ℤ) ^ 2 = (y : ℤ) ^ 2 * ((Q : ℤ) * Q - P * P) := by
      linear_combination ((x : ℤ) * P + y * Q) * hxy'
    have e2 : ((((q + 1) ^ 2 * D * (D + B) : ℕ)) : ℤ) ∣ (Q : ℤ) * Q - P * P := by
      have h := Nat.modEq_iff_dvd.1 hmod.symm
      exact_mod_cast h
    obtain ⟨t, ht⟩ := e2
    rw [e1, ht]
    refine ⟨(y : ℤ) * c * t, ?_⟩
    have hc' : (y : ℤ) * D = (D + B) * c := by exact_mod_cast hc
    push_cast
    linear_combination (((q : ℤ) + 1) ^ 2 * (D + B) * y * t) * hc'
  have hpN : (((q + 1 : ℕ) : ℤ)) ^ (2 * r) ∣ ((((q + 1) * (D + B) : ℕ) : ℤ)) ^ 2 := by
    rw [pow_mul']
    exact pow_dvd_pow_of_dvd (by exact_mod_cast hA) 2
  have hcopZ : IsCoprime ((((q + 1 : ℕ) : ℤ)) ^ (2 * r)) ((P : ℤ) ^ 2) :=
    IsCoprime.pow (Nat.isCoprime_iff_coprime.2 hcop)
  exact hcopZ.dvd_of_dvd_mul_right (hpN.trans hdiv)

end A307091

open A307091 in
theorem OMA.solution : type_of% @OMA.S_oeis_a307091.main := by
  intro p n r hp hp3 hn hr
  apply Int.ModEq.symm
  rw [Int.modEq_iff_dvd]
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hN : n * p ^ (s + 1) = p * (n * p ^ s) := by rw [pow_succ]; ring
  have hpr : p ^ (s + 1) ∣ p * (n * p ^ s) := by rw [← hN]; exact dvd_mul_left _ _
  rw [hN]
  generalize n * p ^ s = M at hpr ⊢
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hK : p * M / 2 + 1 ≤ p * (M + 1) := by
    have h1 := Nat.div_le_self (p * M) 2
    have h2 : p * (M + 1) = p * M + p := by ring
    omega
  rw [a_eq_sum (p * M) (p * (M + 1)) hK, a_eq_sum M (M + 1) (by omega)]
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have h1 : ((p : ℤ) ^ (2 * (s + 1)))
      ∣ ∑ k ∈ range (p * (M + 1)), (-1 : ℤ) ^ k * (((p * M).choose (2 * k) : ℕ) : ℤ) ^ 2
        - ∑ k ∈ range (M + 1),
            (-1 : ℤ) ^ (p * k) * (((p * M).choose (2 * (p * k)) : ℕ) : ℤ) ^ 2 := by
    have hf : ∀ k, ¬ p ∣ k →
        ((p : ℤ) ^ (2 * (s + 1))) ∣ (-1 : ℤ) ^ k * (((p * M).choose (2 * k) : ℕ) : ℤ) ^ 2 := by
      intro k hk
      have h2k : ¬ p ∣ 2 * k := by
        intro h
        rcases (Nat.Prime.dvd_mul hp).1 h with h2 | h2
        · have h3 := Nat.le_of_dvd (by norm_num) h2
          omega
        · exact hk h2
      have h4 := choose_dvd_of_not_dvd hp hpr h2k
      have hz : ((p : ℤ) ^ (s + 1)) ∣ (((p * M).choose (2 * k) : ℕ) : ℤ) := by
        exact_mod_cast h4
      rw [pow_mul']
      exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hz 2) _
    subst hq
    exact sum_block q _ (fun k => (-1 : ℤ) ^ k * ((((q + 1) * M).choose (2 * k) : ℕ) : ℤ) ^ 2)
      hf (M + 1)
  have h2 : ((p : ℤ) ^ (2 * (s + 1)))
      ∣ ∑ k ∈ range (M + 1),
            (-1 : ℤ) ^ (p * k) * (((p * M).choose (2 * (p * k)) : ℕ) : ℤ) ^ 2
        - ∑ k ∈ range (M + 1), (-1 : ℤ) ^ k * ((M.choose (2 * k) : ℕ) : ℤ) ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.dvd_sum
    intro k _
    have hs : (-1 : ℤ) ^ (p * k) = (-1) ^ k := by rw [pow_mul, hodd.neg_one_pow]
    have h2k : 2 * (p * k) = p * (2 * k) := by ring
    rw [hs, h2k, ← mul_sub]
    exact Dvd.dvd.mul_left (choose_sq_sub hp (s + 1) M (2 * k) hpr) _
  have h3 := dvd_add h1 h2
  rw [sub_add_sub_cancel] at h3
  exact h3
