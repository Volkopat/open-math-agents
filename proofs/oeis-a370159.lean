import OMAStatements.S_oeis_a370159
import Mathlib

/-!
OEIS A370159: for F = (1 + x) * (1 + x + x^2)^2 and a(n) = [x^n] F^n,
a(n * p^r) = a(n * p^(r-1)) modulo p^(2r) for every prime p >= 5 and all n, r >= 1.

Write P = p^r, N = n * P, Q = n * p^(r-1). Call an integer power series D small if P divides every
coefficient of D and P^2 divides the coefficients whose index is a multiple of p (`InI`).

1. Binomial part. With X = prod (N - j) and Y = prod j over the j < p*b prime to p one has
   C(N, p*b) * Y = C(Q, b) * X. The reflection j -> p*b - j gives X^2 = Y^2 modulo P * p^(t+1)
   and X = Y modulo p^(t+1) whenever p^(t+1) divides N and p*b, hence X = Y modulo P * p^(t+1)
   for odd p. For b = p^s * b' with p not dividing b' take t = min(s, r-1); p^(r-1-t) divides
   C(Q, b), so P^2 divides C(N, p*b) - C(Q, b). Also P divides C(N, i) when p does not divide i.
2. Hence (1 + c x^e)^N - (1 + c x^(e p))^Q is small for c = 1, -1 and e = 1, 3 (p is odd and
   prime to 3), for every n >= 1.
3. From (1 - x)^2 F = (1 + x)(1 - x^3)^2, raised to the powers N and Q (the latter expanded
   by x -> x^p), the series (F^N - expand_p (F^Q)) * (1 - x)^(2N) is small, and division
   by a series with constant coefficient 1 whose coefficients off the multiples of p are
   divisible by P keeps smallness. The coefficient of x^N gives the claim.

This is the method of the workspace proof of A333579 (prime powers), with the binomial part
extended from N = p^k to N = n * p^r.
-/

open Finset

namespace A370159

/-- One step of the binomial recursion, over `ℤ`, with no side condition. -/
private lemma choose_succ_int (n m : ℕ) :
    ((n.choose (m + 1) : ℕ) : ℤ) * ((m : ℤ) + 1) = (n.choose m : ℤ) * ((n : ℤ) - m) := by
  rcases le_or_gt m n with h | h
  · have h1 := Nat.choose_succ_right_eq n m
    have h2 : ((n - m : ℕ) : ℤ) = (n : ℤ) - m := Nat.cast_sub h
    rw [← h2]
    exact_mod_cast h1
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- `r` steps of the binomial recursion. -/
private lemma choose_add_int (n m r : ℕ) :
    ((n.choose (m + r) : ℕ) : ℤ) * ∏ t ∈ range r, ((m : ℤ) + t + 1) =
      (n.choose m : ℤ) * ∏ t ∈ range r, ((n : ℤ) - m - t) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [prod_range_succ, prod_range_succ, ← add_assoc]
    have h := choose_succ_int n (m + r)
    push_cast at h
    linear_combination (∏ t ∈ range r, ((m : ℤ) + t + 1)) * h + ((n : ℤ) - m - r) * ih

/-- The product of `g j` over the `j = p * i + t + 1` with `i < b`, `t < p - 1`
(these are the `j < p * b` that are not multiples of `p`). -/
private def uprod (p b : ℕ) (g : ℕ → ℤ) : ℤ :=
  ∏ i ∈ range b, ∏ t ∈ range (p - 1), g (p * i + t + 1)

private lemma uprod_succ (p b : ℕ) (g : ℕ → ℤ) :
    uprod p (b + 1) g = uprod p b g * ∏ t ∈ range (p - 1), g (p * b + t + 1) := by
  unfold uprod
  rw [prod_range_succ]

private lemma uprod_mul (p b : ℕ) (g h : ℕ → ℤ) :
    uprod p b g * uprod p b h = uprod p b (fun j => g j * h j) := by
  unfold uprod
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [← prod_mul_distrib]

private lemma uprod_modEq (p b : ℕ) (g h : ℕ → ℤ) (M : ℤ)
    (H : ∀ i < b, ∀ t < p - 1, g (p * i + t + 1) ≡ h (p * i + t + 1) [ZMOD M]) :
    uprod p b g ≡ uprod p b h [ZMOD M] := by
  unfold uprod
  refine Int.ModEq.prod fun i hi => Int.ModEq.prod fun t ht => ?_
  exact H i (mem_range.mp hi) t (mem_range.mp ht)

/-- Reflection `j ↦ p * b - j`. -/
private lemma uprod_reflect (p b : ℕ) (g : ℕ → ℤ) :
    uprod p b g = uprod p b (fun j => g (p * b - j)) := by
  unfold uprod
  have h1 : ∏ i ∈ range b, ∏ t ∈ range (p - 1), g (p * i + t + 1)
      = ∏ i ∈ range b, ∏ t ∈ range (p - 1), g (p * (b - 1 - i) + t + 1) :=
    (prod_range_reflect (fun i => ∏ t ∈ range (p - 1), g (p * i + t + 1)) b).symm
  rw [h1]
  refine prod_congr rfl fun i hi => ?_
  have h2 : ∏ t ∈ range (p - 1), g (p * (b - 1 - i) + t + 1)
      = ∏ t ∈ range (p - 1), g (p * (b - 1 - i) + (p - 1 - 1 - t) + 1) :=
    (prod_range_reflect (fun t => g (p * (b - 1 - i) + t + 1)) (p - 1)).symm
  rw [h2]
  refine prod_congr rfl fun t ht => ?_
  rw [mem_range] at hi ht
  show g (p * (b - 1 - i) + (p - 1 - 1 - t) + 1) = g (p * b - (p * i + t + 1))
  congr 1
  obtain ⟨d, rfl⟩ : ∃ d, b = i + 1 + d := ⟨b - (i + 1), by omega⟩
  have h3 : i + 1 + d - 1 - i = d := by omega
  rw [h3]
  have h4 : p * (i + 1 + d) = p * i + p + p * d := by ring
  rw [h4]
  omega

/-- The units `j < p * b` are at most `p * b`. -/
private lemma unit_le {p b i t : ℕ} (hi : i < b) (ht : t < p - 1) : p * i + t + 1 ≤ p * b := by
  have h1 : p * (i + 1) ≤ p * b := Nat.mul_le_mul_left p hi
  have h2 : p * (i + 1) = p * i + p := by ring
  omega

/-- Product formula: `C(pa, pb) * ∏ j = C(a, b) * ∏ (pa - j)`, the products over the units
`j < p * b`. -/
private lemma choose_mul_uprod (p a b : ℕ) (hp : 0 < p) :
    ((p * a).choose (p * b) : ℤ) * uprod p b (fun j => (j : ℤ)) =
      (a.choose b : ℤ) * uprod p b (fun j => ((p * a : ℕ) : ℤ) - j) := by
  induction b with
  | zero => simp [uprod]
  | succ b ih =>
    rw [uprod_succ, uprod_succ]
    have hstep := choose_add_int (p * a) (p * b) p
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [prod_range_succ, prod_range_succ'] at hstep
    have hc := choose_succ_int a b
    have e1 : ∏ t ∈ range (q + 1 - 1), (((q + 1) * b + t + 1 : ℕ) : ℤ)
        = ∏ t ∈ range q, ((((q + 1) * b : ℕ) : ℤ) + t + 1) := by
      rw [Nat.add_sub_cancel]
      refine prod_congr rfl fun t _ => ?_
      push_cast; ring
    have e2 : ∏ t ∈ range (q + 1 - 1), ((((q + 1) * a : ℕ) : ℤ) - (((q + 1) * b + t + 1 : ℕ) : ℤ))
        = ∏ t ∈ range q, ((((q + 1) * a : ℕ) : ℤ) - (((q + 1) * b : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ)) := by
      rw [Nat.add_sub_cancel]
      refine prod_congr rfl fun t _ => ?_
      push_cast; ring
    rw [e1, e2]
    have hne : (((q + 1 : ℕ) : ℤ) * ((b : ℤ) + 1)) ≠ 0 := by positivity
    have hmul : ((q + 1 : ℕ) : ℤ) * (b + 1 : ℕ) = (((q + 1) * (b + 1) : ℕ) : ℤ) := by push_cast; ring
    apply mul_left_cancel₀ hne
    have hidx : (q + 1) * (b + 1) = (q + 1) * b + (q + 1) := by ring
    rw [hidx]
    push_cast at hstep ih hc ⊢
    linear_combination (uprod (q + 1) b (fun j => (j : ℤ))) * hstep
      + (∏ t ∈ range q, (((q : ℤ) + 1) * a - ((q : ℤ) + 1) * b - ((t : ℤ) + 1))) * ((q : ℤ) + 1) * ((a : ℤ) - b) * ih
      - (∏ t ∈ range q, (((q : ℤ) + 1) * a - ((q : ℤ) + 1) * b - ((t : ℤ) + 1))) * ((q : ℤ) + 1)
          * (uprod (q + 1) b (fun j => (((q : ℤ) + 1) * a) - j)) * hc

private lemma not_dvd_uprod_id {p : ℕ} (hp : p.Prime) (b : ℕ) :
    ¬ (p : ℤ) ∣ uprod p b (fun j => (j : ℤ)) := by
  unfold uprod
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  intro h
  rw [hpi.dvd_finsetProd_iff] at h
  obtain ⟨i, _, h⟩ := h
  rw [hpi.dvd_finsetProd_iff] at h
  obtain ⟨t, ht, h⟩ := h
  rw [mem_range] at ht
  have h' : p ∣ p * i + (t + 1) := by
    have := Int.natCast_dvd_natCast.mp h
    rwa [add_assoc] at this
  have h'' : p ∣ t + 1 := (Nat.dvd_add_right (dvd_mul_right p i)).mp h'
  have := Nat.le_of_dvd (by omega) h''
  omega

/-- `X ≡ Y` modulo `p ^ (k + (s + 1))`, where `X = ∏ (A - j)`, `Y = ∏ j` over the units
`j < p * b`, when `p ^ k` and `p ^ (s + 1)` divide `A`, `p ^ (s + 1)` divides `p * b`, and `p` is
an odd prime. -/
private lemma uprod_sub_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (A k b s : ℕ)
    (hA : p ^ k ∣ A) (hAs : p ^ (s + 1) ∣ A) (hb : p ^ (s + 1) ∣ p * b) :
    ((p : ℤ) ^ (k + (s + 1))) ∣
      uprod p b (fun j => (A : ℤ) - j) - uprod p b (fun j => (j : ℤ)) := by
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  set N : ℤ := (A : ℤ) with hNdef
  set X := uprod p b (fun j => N - j) with hX
  set Y := uprod p b (fun j => (j : ℤ)) with hY
  -- reflected forms
  have hXr : X = uprod p b (fun j => N - ((p * b - j : ℕ) : ℤ)) := uprod_reflect p b _
  have hYr : Y = uprod p b (fun j => ((p * b - j : ℕ) : ℤ)) := uprod_reflect p b _
  have hdN : ((p : ℤ) ^ (s + 1)) ∣ N := by
    rw [hNdef]; exact_mod_cast hAs
  have hdNk : ((p : ℤ) ^ k) ∣ N := by
    rw [hNdef]; exact_mod_cast hA
  have hdb : ((p : ℤ) ^ (s + 1)) ∣ ((p * b : ℕ) : ℤ) := by exact_mod_cast hb
  have hdiff : ((p : ℤ) ^ (s + 1)) ∣ N - ((p * b : ℕ) : ℤ) := dvd_sub hdN hdb
  -- X ≡ Y mod p^(s+1)
  have h1 : X ≡ Y [ZMOD (p : ℤ) ^ (s + 1)] := by
    rw [hXr]
    refine uprod_modEq p b _ _ _ fun i hi t ht => ?_
    have hle := unit_le hi ht
    show N - ((p * b - (p * i + t + 1) : ℕ) : ℤ) ≡ ((p * i + t + 1 : ℕ) : ℤ) [ZMOD (p : ℤ) ^ (s + 1)]
    rw [Nat.cast_sub hle, Int.modEq_iff_dvd]
    have : ((p * i + t + 1 : ℕ) : ℤ) - (N - (((p * b : ℕ) : ℤ) - ((p * i + t + 1 : ℕ) : ℤ)))
        = -(N - ((p * b : ℕ) : ℤ)) := by ring
    rw [this]
    exact (dvd_neg).mpr hdiff
  -- X * X ≡ Y * Y mod p^k * p^(s+1)
  have h2 : X * X ≡ Y * Y [ZMOD (p : ℤ) ^ k * (p : ℤ) ^ (s + 1)] := by
    have e1 : X * X = uprod p b (fun j => (N - j) * (N - ((p * b - j : ℕ) : ℤ))) := by
      rw [← uprod_mul, ← hXr]
    have e2 : Y * Y = uprod p b (fun j => (j : ℤ) * ((p * b - j : ℕ) : ℤ)) := by
      rw [← uprod_mul, ← hYr]
    rw [e1, e2]
    refine uprod_modEq p b _ _ _ fun i hi t ht => ?_
    have hle := unit_le hi ht
    show (N - ((p * i + t + 1 : ℕ) : ℤ)) * (N - ((p * b - (p * i + t + 1) : ℕ) : ℤ))
      ≡ ((p * i + t + 1 : ℕ) : ℤ) * ((p * b - (p * i + t + 1) : ℕ) : ℤ)
        [ZMOD (p : ℤ) ^ k * (p : ℤ) ^ (s + 1)]
    rw [Nat.cast_sub hle, Int.modEq_iff_dvd]
    have : ((p * i + t + 1 : ℕ) : ℤ) * (((p * b : ℕ) : ℤ) - ((p * i + t + 1 : ℕ) : ℤ))
        - (N - ((p * i + t + 1 : ℕ) : ℤ)) * (N - (((p * b : ℕ) : ℤ) - ((p * i + t + 1 : ℕ) : ℤ)))
        = -(N * (N - ((p * b : ℕ) : ℤ))) := by ring
    rw [this]
    exact (dvd_neg).mpr (mul_dvd_mul hdNk hdiff)
  -- p does not divide X + Y
  have hYnd : ¬ (p : ℤ) ∣ Y := not_dvd_uprod_id hp b
  have hsum : ¬ (p : ℤ) ∣ X + Y := by
    intro hd
    have hXY : (p : ℤ) ∣ X - Y := by
      have := (Int.modEq_iff_dvd.mp h1.symm)
      exact dvd_trans (dvd_pow_self (p : ℤ) (Nat.succ_ne_zero s)) this
    have h2Y : (p : ℤ) ∣ 2 * Y := by
      have : 2 * Y = (X + Y) - (X - Y) := by ring
      rw [this]; exact dvd_sub hd hXY
    rcases hpi.dvd_or_dvd h2Y with h | h
    · have h' : p ∣ 2 := by exact_mod_cast h
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h'
      exact hp2 this
    · exact hYnd h
  -- conclude
  have hprod : ((p : ℤ) ^ (k + (s + 1))) ∣ (X - Y) * (X + Y) := by
    have h3 := Int.modEq_iff_dvd.mp h2.symm
    have h4 : (X - Y) * (X + Y) = X * X - Y * Y := by ring
    rw [h4, pow_add]
    exact h3
  exact hpi.pow_dvd_of_dvd_mul_right _ hsum hprod

/-- `p ^ (m - s)` divides `C(Q, p ^ s * b')` when `p ^ m` divides `Q > 0` and `p` does not
divide `b'`. -/
private lemma pow_dvd_choose_mul {p : ℕ} (hp : p.Prime) (Q m s b' : ℕ) (hQ : 0 < Q)
    (hmQ : p ^ m ∣ Q) (hs : s ≤ m) (hb' : ¬ p ∣ b') :
    p ^ (m - s) ∣ Q.choose (p ^ s * b') := by
  have hb0 : b' ≠ 0 := fun h => hb' (h ▸ dvd_zero p)
  have hbpos : 0 < p ^ s * b' := Nat.mul_pos (pow_pos hp.pos s) (Nat.pos_of_ne_zero hb0)
  have h := Nat.add_one_mul_choose_eq (Q - 1) (p ^ s * b' - 1)
  rw [Nat.sub_add_cancel hQ, Nat.sub_add_cancel hbpos] at h
  -- h : Q * C(Q - 1, b - 1) = C(Q, b) * b
  have h0 : p ^ m ∣ Q.choose (p ^ s * b') * (p ^ s * b') := by
    rw [← h]
    exact Dvd.dvd.mul_right hmQ _
  have h1 : p ^ s * p ^ (m - s) ∣ p ^ s * (Q.choose (p ^ s * b') * b') := by
    rw [← pow_add, Nat.add_sub_cancel' hs]
    have e : p ^ s * (Q.choose (p ^ s * b') * b') = Q.choose (p ^ s * b') * (p ^ s * b') := by
      ring
    rw [e]
    exact h0
  have h2 : p ^ (m - s) ∣ Q.choose (p ^ s * b') * b' :=
    Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos s) h1
  have hcop : Nat.Coprime (p ^ (m - s)) b' :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hb')
  exact hcop.dvd_of_dvd_mul_right h2

/-- Key binomial congruence: `C(n p^(m+1), p b) ≡ C(n p^m, b)` modulo `p^(2(m+1))` for odd `p`
and `n > 0`. -/
private lemma choose_mul_pow_congr {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (n m b : ℕ)
    (hn : 0 < n) :
    (((p ^ (m + 1) : ℕ) : ℤ) ^ 2) ∣
      (((n * p ^ (m + 1)).choose (p * b) : ℕ) : ℤ) - (((n * p ^ m).choose b : ℕ) : ℤ) := by
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases Nat.eq_zero_or_pos b with rfl | hbpos
  · simp
  have hQpos : 0 < n * p ^ m := Nat.mul_pos hn (pow_pos hp.pos m)
  obtain ⟨s, b', hb', rfl⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Nat.pos_iff_ne_zero.mp hbpos) p hp.ne_one
  have hpa : p * (n * p ^ m) = n * p ^ (m + 1) := by rw [pow_succ]; ring
  have hform := choose_mul_uprod p (n * p ^ m) (p ^ s * b') hp.pos
  rw [hpa] at hform
  -- t = min s m
  obtain ⟨t, hts, htm, hcase⟩ : ∃ t, t ≤ s ∧ t ≤ m ∧ (t = s ∨ t = m) := by
    rcases le_total s m with h | h
    · exact ⟨s, le_rfl, h, Or.inl rfl⟩
    · exact ⟨m, h, le_rfl, Or.inr rfl⟩
  have hsub := uprod_sub_dvd hp hp2 (n * p ^ (m + 1)) (m + 1) (p ^ s * b') t
    (dvd_mul_left (p ^ (m + 1)) n)
    (dvd_trans (pow_dvd_pow p (by omega : t + 1 ≤ m + 1)) (dvd_mul_left (p ^ (m + 1)) n))
    (dvd_trans (pow_dvd_pow p (by omega : t + 1 ≤ s + 1)) ⟨b', by rw [pow_succ]; ring⟩)
  have hch : ((p : ℤ) ^ (m - t)) ∣ (((n * p ^ m).choose (p ^ s * b') : ℕ) : ℤ) := by
    rcases hcase with h | h
    · rw [h]
      exact_mod_cast pow_dvd_choose_mul hp (n * p ^ m) m s b' hQpos (dvd_mul_left (p ^ m) n)
        (by omega) hb'
    · rw [h, Nat.sub_self, pow_zero]
      exact one_dvd _
  set X := uprod p (p ^ s * b') (fun j => ((n * p ^ (m + 1) : ℕ) : ℤ) - j) with hX
  set Y := uprod p (p ^ s * b') (fun j => (j : ℤ)) with hY
  have hYnd : ¬ (p : ℤ) ∣ Y := not_dvd_uprod_id hp _
  have hkey : Y * ((((n * p ^ (m + 1)).choose (p * (p ^ s * b')) : ℕ) : ℤ)
        - (((n * p ^ m).choose (p ^ s * b') : ℕ) : ℤ))
      = (((n * p ^ m).choose (p ^ s * b') : ℕ) : ℤ) * (X - Y) := by
    linear_combination hform
  have hdvd : ((p : ℤ) ^ (2 * (m + 1))) ∣
      Y * ((((n * p ^ (m + 1)).choose (p * (p ^ s * b')) : ℕ) : ℤ)
        - (((n * p ^ m).choose (p ^ s * b') : ℕ) : ℤ)) := by
    rw [hkey]
    have : (p : ℤ) ^ (2 * (m + 1)) = (p : ℤ) ^ (m - t) * (p : ℤ) ^ (m + 1 + (t + 1)) := by
      rw [← pow_add]; congr 1; omega
    rw [this]
    exact mul_dvd_mul hch hsub
  have hfin := hpi.pow_dvd_of_dvd_mul_left _ hYnd hdvd
  have hsq : (((p ^ (m + 1) : ℕ) : ℤ) ^ 2) = (p : ℤ) ^ (2 * (m + 1)) := by
    push_cast; rw [← pow_mul]; congr 1; ring
  rw [hsq]; exact hfin

/-- `p ^ k` divides `C(n * p ^ k, i)` when `p` does not divide `i` and `n > 0`. -/
private lemma pow_dvd_choose_of_not_dvd {p : ℕ} (hp : p.Prime) (n k i : ℕ) (hn : 0 < n)
    (hi : ¬ p ∣ i) : p ^ k ∣ (n * p ^ k).choose i := by
  have h := pow_dvd_choose_mul hp (n * p ^ k) k 0 i (Nat.mul_pos hn (pow_pos hp.pos k))
    (dvd_mul_left (p ^ k) n) (Nat.zero_le k) hi
  simpa using h

/-! Power series part. -/

/-- `D` is in the set `N * (series supported off the multiples of p) + N ^ 2 * (any series)`. -/
private def InI (p N : ℕ) (D : PowerSeries ℤ) : Prop :=
  ∀ j, ((N : ℤ) ∣ PowerSeries.coeff j D) ∧ (p ∣ j → ((N : ℤ) ^ 2) ∣ PowerSeries.coeff j D)

/-- `G` is supported on the multiples of `p`. -/
private def PS (p : ℕ) (G : PowerSeries ℤ) : Prop :=
  ∀ j, ¬ p ∣ j → PowerSeries.coeff j G = 0

private lemma InI_add {p N : ℕ} {A B : PowerSeries ℤ} (hA : InI p N A) (hB : InI p N B) :
    InI p N (A + B) := by
  intro j
  rw [map_add]
  exact ⟨dvd_add (hA j).1 (hB j).1, fun h => dvd_add ((hA j).2 h) ((hB j).2 h)⟩

private lemma InI_sub {p N : ℕ} {A B : PowerSeries ℤ} (hA : InI p N A) (hB : InI p N B) :
    InI p N (A - B) := by
  intro j
  rw [map_sub]
  exact ⟨dvd_sub (hA j).1 (hB j).1, fun h => dvd_sub ((hA j).2 h) ((hB j).2 h)⟩

private lemma InI_mul {p N : ℕ} {A B : PowerSeries ℤ} (hA : InI p N A) (hB : InI p N B) :
    InI p N (A * B) := by
  have key : ∀ j, ((N : ℤ) ^ 2) ∣ PowerSeries.coeff j (A * B) := by
    intro j
    rw [PowerSeries.coeff_mul]
    refine Finset.dvd_sum fun x _ => ?_
    rw [sq]
    exact mul_dvd_mul (hA x.1).1 (hB x.2).1
  intro j
  exact ⟨dvd_trans (dvd_pow_self _ two_ne_zero) (key j), fun _ => key j⟩

private lemma InI_mul_PS {p N : ℕ} {A G : PowerSeries ℤ} (hA : InI p N A) (hG : PS p G) :
    InI p N (A * G) := by
  intro j
  rw [PowerSeries.coeff_mul]
  constructor
  · refine Finset.dvd_sum fun x _ => ?_
    exact Dvd.dvd.mul_right (hA x.1).1 _
  · intro hj
    refine Finset.dvd_sum fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases h2 : p ∣ x.2
    · have h1 : p ∣ x.1 := by
        have h3 : p ∣ x.2 + x.1 := by rw [add_comm, hx]; exact hj
        exact (Nat.dvd_add_right h2).mp h3
      exact Dvd.dvd.mul_right ((hA x.1).2 h1) _
    · rw [hG x.2 h2, mul_zero]; exact dvd_zero _

private lemma PS_mul {p : ℕ} {A B : PowerSeries ℤ} (hA : PS p A) (hB : PS p B) : PS p (A * B) := by
  intro j hj
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  by_cases h1 : p ∣ x.1
  · have h2 : ¬ p ∣ x.2 := fun h2 => hj (hx ▸ dvd_add h1 h2)
    rw [hB x.2 h2, mul_zero]
  · rw [hA x.1 h1, zero_mul]

private lemma InI_mul_sub {p N : ℕ} {A A' B B' : PowerSeries ℤ} (hA : InI p N (A - A'))
    (hB : InI p N (B - B')) (hA' : PS p A') (hB' : PS p B') : InI p N (A * B - A' * B') := by
  have h : A * B - A' * B' = (A - A') * (B - B') + (A - A') * B' + (B - B') * A' := by ring
  rw [h]
  exact InI_add (InI_add (InI_mul hA hB) (InI_mul_PS hA hB')) (InI_mul_PS hB hA')

/-- Division by a series `U` with constant coefficient `1` whose coefficients off the multiples of
`p` are divisible by `N`. -/
private lemma InI_of_mul {p N : ℕ} {D U : PowerSeries ℤ} (hU0 : PowerSeries.coeff 0 U = 1)
    (hU : ∀ j, ¬ p ∣ j → (N : ℤ) ∣ PowerSeries.coeff j U) (h : InI p N (D * U)) : InI p N D := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    have hj := h j
    rw [PowerSeries.coeff_mul] at hj
    have hmem : (j, 0) ∈ Finset.HasAntidiagonal.antidiagonal j := Finset.HasAntidiagonal.mem_antidiagonal.mpr (add_zero j)
    rw [← Finset.add_sum_erase _ _ hmem] at hj
    simp only [hU0, mul_one] at hj
    have hlt : ∀ x ∈ (Finset.HasAntidiagonal.antidiagonal j).erase (j, 0), x.1 < j := by
      intro x hx
      rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hx
      by_contra hge
      have hx1 : x.1 = j := by omega
      have hx2 : x.2 = 0 := by omega
      exact hx.1 (Prod.ext hx1 hx2)
    have hrest1 : (N : ℤ) ∣ ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal j).erase (j, 0),
        PowerSeries.coeff x.1 D * PowerSeries.coeff x.2 U := by
      refine Finset.dvd_sum fun x hx => ?_
      exact Dvd.dvd.mul_right (ih x.1 (hlt x hx)).1 _
    have hrest2 : p ∣ j → ((N : ℤ) ^ 2) ∣ ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal j).erase (j, 0),
        PowerSeries.coeff x.1 D * PowerSeries.coeff x.2 U := by
      intro hpj
      refine Finset.dvd_sum fun x hx => ?_
      have hl := hlt x hx
      rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hx
      by_cases h1 : p ∣ x.1
      · exact Dvd.dvd.mul_right ((ih x.1 hl).2 h1) _
      · have h2 : ¬ p ∣ x.2 := by
          intro h2
          have h3 : p ∣ x.2 + x.1 := by rw [add_comm, hx.2]; exact hpj
          exact h1 ((Nat.dvd_add_right h2).mp h3)
        rw [sq]
        exact mul_dvd_mul (ih x.1 hl).1 (hU x.2 h2)
    exact ⟨(dvd_add_left hrest1).mp hj.1, fun hpj => (dvd_add_left (hrest2 hpj)).mp (hj.2 hpj)⟩

/-- The binomial `1 + c * x ^ e`. -/
private noncomputable def B (c : ℤ) (e : ℕ) : PowerSeries ℤ :=
  1 + PowerSeries.C c * PowerSeries.X ^ e

private lemma coeff_B_pow (c : ℤ) (e n j : ℕ) (he : 0 < e) :
    PowerSeries.coeff j (B c e ^ n) =
      if e ∣ j then c ^ (j / e) * ((n.choose (j / e) : ℕ) : ℤ) else 0 := by
  unfold B
  rw [add_comm, add_pow]
  simp only [one_pow, mul_one, map_sum]
  have hterm : ∀ i ∈ Finset.range (n + 1),
      PowerSeries.coeff j ((PowerSeries.C c * PowerSeries.X ^ e : PowerSeries ℤ) ^ i *
          ((n.choose i : ℕ) : PowerSeries ℤ)) =
        if j = e * i then c ^ i * ((n.choose i : ℕ) : ℤ) else 0 := by
    intro i _
    rw [mul_pow, ← pow_mul, ← map_pow, ← map_natCast (PowerSeries.C : ℤ →+* PowerSeries ℤ) (n.choose i),
      mul_right_comm, ← map_mul, PowerSeries.coeff_C_mul_X_pow]
  rw [Finset.sum_congr rfl hterm]
  split_ifs with h
  · obtain ⟨i, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ he, Finset.sum_eq_single i]
    · simp
    · intro i' _ hne
      rw [if_neg]
      intro h
      exact hne (Nat.eq_of_mul_eq_mul_left he h).symm
    · intro hi
      rw [Finset.mem_range, not_lt] at hi
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      simp
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    intro hj
    exact h ⟨i, hj⟩

private lemma B_pow_PS (p : ℕ) (hp : 0 < p) (c : ℤ) (e n : ℕ) (he : 0 < e) :
    PS p (B c (e * p) ^ n) := by
  intro j hj
  rw [coeff_B_pow c (e * p) n j (Nat.mul_pos he hp), if_neg]
  intro h
  exact hj (dvd_trans (dvd_mul_left p e) h)

private lemma B_pow_InI {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (n m : ℕ) (hn : 0 < n) (c : ℤ)
    (hc : c = 1 ∨ c = -1) (e : ℕ) (he : 0 < e) (hep : Nat.Coprime p e) :
    InI p (p ^ (m + 1)) (B c e ^ (n * p ^ (m + 1)) - B c (e * p) ^ (n * p ^ m)) := by
  intro j
  rw [map_sub, coeff_B_pow c e _ j he, coeff_B_pow c (e * p) _ j (Nat.mul_pos he hp.pos)]
  have hcp : c ^ p = c := by
    rcases hc with rfl | rfl
    · simp
    · exact Odd.neg_one_pow (hp.odd_of_ne_two hp2)
  by_cases hej : e ∣ j
  · obtain ⟨i, rfl⟩ := hej
    rw [if_pos (dvd_mul_right e i), Nat.mul_div_cancel_left _ he]
    by_cases hpi : p ∣ i
    · obtain ⟨i', rfl⟩ := hpi
      have h1 : e * p ∣ e * (p * i') := ⟨i', by ring⟩
      have h2 : e * (p * i') / (e * p) = i' := by
        rw [← mul_assoc]
        exact Nat.mul_div_cancel_left _ (Nat.mul_pos he hp.pos)
      rw [if_pos h1, h2, pow_mul, hcp, ← mul_sub]
      have key := choose_mul_pow_congr hp hp2 n m i' hn
      have key' : ((p ^ (m + 1) : ℕ) : ℤ) ^ 2 ∣
          c ^ i' * ((((n * p ^ (m + 1)).choose (p * i') : ℕ) : ℤ)
            - (((n * p ^ m).choose i' : ℕ) : ℤ)) :=
        Dvd.dvd.mul_left key _
      exact ⟨dvd_trans (dvd_pow_self _ two_ne_zero) key', fun _ => key'⟩
    · have h1 : ¬ e * p ∣ e * i := fun h => hpi (Nat.dvd_of_mul_dvd_mul_left he h)
      rw [if_neg h1, sub_zero]
      constructor
      · have h3 : ((p ^ (m + 1) : ℕ) : ℤ) ∣ (((n * p ^ (m + 1)).choose i : ℕ) : ℤ) := by
          exact_mod_cast pow_dvd_choose_of_not_dvd hp n (m + 1) i hn hpi
        exact Dvd.dvd.mul_left h3 _
      · intro hpj
        exact absurd (hep.dvd_of_dvd_mul_left hpj) hpi
  · have h1 : ¬ e * p ∣ j := fun h => hej (dvd_trans (dvd_mul_right e p) h)
    rw [if_neg hej, if_neg h1, sub_zero]
    exact ⟨dvd_zero _, fun _ => dvd_zero _⟩

private lemma expand_B (p : ℕ) (hp : p ≠ 0) (c : ℤ) (e : ℕ) :
    PowerSeries.expand p hp (B c e) = B c (e * p) := by
  unfold B
  rw [map_add, map_one, map_mul, map_pow, PowerSeries.expand_C, PowerSeries.expand_X, ← pow_mul,
    mul_comm p e]

/-- The series `(1 + x) * (1 + x + x^2)^2`. -/
private noncomputable def Fs : PowerSeries ℤ :=
  (1 + PowerSeries.X) * (1 + PowerSeries.X + PowerSeries.X ^ 2) ^ 2

/-- The sequence read off the power series. -/
private lemma a_eq (n : ℕ) : OMA.S_oeis_a370159.a n = PowerSeries.coeff n (Fs ^ n) := by
  unfold OMA.S_oeis_a370159.a Fs
  rw [← Polynomial.coeff_coe]
  simp only [Polynomial.coe_pow, Polynomial.coe_mul, Polynomial.coe_add, Polynomial.coe_one,
    Polynomial.coe_X]

/-- `(1 - x)^2 * F = (1 + x) * (1 - x^3)^2`. -/
private lemma f_rel : B (-1) 1 ^ 2 * Fs = B 1 1 * B (-1) 3 ^ 2 := by
  unfold B Fs
  simp only [map_neg, map_one, pow_one]
  ring

private lemma f_rel_pow (K : ℕ) :
    B (-1) 1 ^ (2 * K) * Fs ^ K = B 1 1 ^ K * B (-1) 3 ^ (2 * K) := by
  rw [pow_mul, pow_mul, ← mul_pow, ← mul_pow, f_rel]

private lemma main_congr {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (n m : ℕ) (hn : 0 < n) :
    ((p : ℤ) ^ (2 * (m + 1))) ∣
      OMA.S_oeis_a370159.a (n * p ^ (m + 1)) - OMA.S_oeis_a370159.a (n * p ^ m) := by
  rw [a_eq, a_eq]
  have hp2 : p ≠ 2 := by omega
  have hp0 : p ≠ 0 := hp.ne_zero
  have h2n : 0 < 2 * n := by omega
  have hcop1 : Nat.Coprime p 1 := Nat.coprime_one_right p
  have hcop3 : Nat.Coprime p 3 := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => ?_
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h
    omega
  have eN : 2 * (n * p ^ (m + 1)) = 2 * n * p ^ (m + 1) := by ring
  have eQ : 2 * (n * p ^ m) = 2 * n * p ^ m := by ring
  -- the relation at level `N = n * p ^ (m + 1)`
  have hrelN : B (-1) 1 ^ (2 * n * p ^ (m + 1)) * Fs ^ (n * p ^ (m + 1)) =
      B 1 1 ^ (n * p ^ (m + 1)) * B (-1) 3 ^ (2 * n * p ^ (m + 1)) := by
    have h := f_rel_pow (n * p ^ (m + 1))
    rw [eN] at h
    exact h
  -- the relation at level `Q = n * p ^ m`, expanded by `x ↦ x ^ p`
  have hrelQ : B (-1) (1 * p) ^ (2 * n * p ^ m) *
      PowerSeries.expand p hp0 (Fs ^ (n * p ^ m)) =
      B 1 (1 * p) ^ (n * p ^ m) * B (-1) (3 * p) ^ (2 * n * p ^ m) := by
    have h0 := f_rel_pow (n * p ^ m)
    rw [eQ] at h0
    have h1 := congrArg (PowerSeries.expand p hp0) h0
    simp only [map_mul, map_pow, expand_B] at h1 ⊢
    exact h1
  -- memberships
  have iV := B_pow_InI hp hp2 (2 * n) m h2n (-1) (Or.inr rfl) 1 one_pos hcop1
  have iB1 := B_pow_InI hp hp2 n m hn 1 (Or.inl rfl) 1 one_pos hcop1
  have iB3 := B_pow_InI hp hp2 (2 * n) m h2n (-1) (Or.inr rfl) 3 (by norm_num) hcop3
  have sV := B_pow_PS p hp.pos (-1) 1 (2 * n * p ^ m) one_pos
  have sB1 := B_pow_PS p hp.pos 1 1 (n * p ^ m) one_pos
  have sB3 := B_pow_PS p hp.pos (-1) 3 (2 * n * p ^ m) (by norm_num)
  have sPhi : PS p (PowerSeries.expand p hp0 (Fs ^ (n * p ^ m))) :=
    fun j hj => PowerSeries.coeff_expand_of_not_dvd p hp0 _ hj
  have iW := InI_mul_sub iB1 iB3 sB1 sB3
  -- the difference times `(1 - x) ^ (2 N)`
  have hprod : InI p (p ^ (m + 1))
      ((Fs ^ (n * p ^ (m + 1)) - PowerSeries.expand p hp0 (Fs ^ (n * p ^ m))) *
        B (-1) 1 ^ (2 * n * p ^ (m + 1))) := by
    have h : (Fs ^ (n * p ^ (m + 1)) - PowerSeries.expand p hp0 (Fs ^ (n * p ^ m))) *
        B (-1) 1 ^ (2 * n * p ^ (m + 1)) =
        (B 1 1 ^ (n * p ^ (m + 1)) * B (-1) 3 ^ (2 * n * p ^ (m + 1)) -
            B 1 (1 * p) ^ (n * p ^ m) * B (-1) (3 * p) ^ (2 * n * p ^ m)) -
          (B (-1) 1 ^ (2 * n * p ^ (m + 1)) - B (-1) (1 * p) ^ (2 * n * p ^ m)) *
          PowerSeries.expand p hp0 (Fs ^ (n * p ^ m)) := by
      linear_combination hrelN - hrelQ
    rw [h]
    exact InI_sub iW (InI_mul_PS iV sPhi)
  -- divide by `(1 - x) ^ (2 N)`
  have hU0 : PowerSeries.coeff 0 (B (-1) 1 ^ (2 * n * p ^ (m + 1))) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [B]
  have hU : ∀ j, ¬ p ∣ j →
      ((p ^ (m + 1) : ℕ) : ℤ) ∣ PowerSeries.coeff j (B (-1) 1 ^ (2 * n * p ^ (m + 1))) := by
    intro j hj
    have h1 := (iV j).1
    rw [map_sub, sV j hj, sub_zero] at h1
    exact h1
  have hD := InI_of_mul hU0 hU hprod
  -- read off the coefficient of `x ^ N`
  have hfin := (hD (n * p ^ (m + 1))).2
    (Dvd.dvd.mul_left (dvd_pow_self p (Nat.succ_ne_zero m)) n)
  rw [map_sub] at hfin
  have hco : PowerSeries.coeff (n * p ^ (m + 1))
      (PowerSeries.expand p hp0 (Fs ^ (n * p ^ m))) =
      PowerSeries.coeff (n * p ^ m) (Fs ^ (n * p ^ m)) := by
    have e : n * p ^ (m + 1) = p * (n * p ^ m) := by rw [pow_succ]; ring
    rw [e]
    exact PowerSeries.coeff_expand_mul p hp0 _ _
  rw [hco] at hfin
  have hsq : (((p ^ (m + 1) : ℕ) : ℤ) ^ 2) = (p : ℤ) ^ (2 * (m + 1)) := by
    push_cast
    rw [← pow_mul]
    congr 1
    ring
  rw [hsq] at hfin
  exact hfin

end A370159

theorem OMA.solution : type_of% @OMA.S_oeis_a370159.main := by
  intro p n r hp hp5 hn hr
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact (Int.modEq_iff_dvd.mpr (A370159.main_congr hp hp5 n m hn)).symm
