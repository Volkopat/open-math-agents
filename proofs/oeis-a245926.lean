import OMAStatements.S_oeis_a245926
import Mathlib

/-! A245926: a(n) = [x^n] F(x)^n with F = (1+x)^2 (1-x^3)/(1-x)^3. Bala's sum equals C(2n,n) U(n),
U(n) = sum_k 3^k C(n+k,2k) C(2n,n-k) (two order-2 recurrences with telescoping certificates),
U(n) = [x^n] F^n (binomial expansion of F = (1+x)^2 (1 + 3x/(1-x)^2) and a first-order certificate),
then the Dwork-type congruence mod p^(2k) (copy of the workspace library LtsDwork). -/


/-!
A245926D: supercongruences a(n p^r) = a(n p^(r-1)) mod p^(2r) for a(n) = [x^n] F^n,
F a product of factors (1 +- x^e)^(+-1). Method of the workspace proofs of A333579 / A370159.
-/

open Finset

namespace A245926D

/-- One step of the binomial recursion, over `ℤ`, with no side condition. -/
lemma choose_succ_int (n m : ℕ) :
    ((n.choose (m + 1) : ℕ) : ℤ) * ((m : ℤ) + 1) = (n.choose m : ℤ) * ((n : ℤ) - m) := by
  rcases le_or_gt m n with h | h
  · have h1 := Nat.choose_succ_right_eq n m
    have h2 : ((n - m : ℕ) : ℤ) = (n : ℤ) - m := Nat.cast_sub h
    rw [← h2]
    exact_mod_cast h1
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- `r` steps of the binomial recursion. -/
lemma choose_add_int (n m r : ℕ) :
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
def uprod (p b : ℕ) (g : ℕ → ℤ) : ℤ :=
  ∏ i ∈ range b, ∏ t ∈ range (p - 1), g (p * i + t + 1)

lemma uprod_succ (p b : ℕ) (g : ℕ → ℤ) :
    uprod p (b + 1) g = uprod p b g * ∏ t ∈ range (p - 1), g (p * b + t + 1) := by
  unfold uprod
  rw [prod_range_succ]

lemma uprod_mul (p b : ℕ) (g h : ℕ → ℤ) :
    uprod p b g * uprod p b h = uprod p b (fun j => g j * h j) := by
  unfold uprod
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [← prod_mul_distrib]

lemma uprod_modEq (p b : ℕ) (g h : ℕ → ℤ) (M : ℤ)
    (H : ∀ i < b, ∀ t < p - 1, g (p * i + t + 1) ≡ h (p * i + t + 1) [ZMOD M]) :
    uprod p b g ≡ uprod p b h [ZMOD M] := by
  unfold uprod
  refine Int.ModEq.prod fun i hi => Int.ModEq.prod fun t ht => ?_
  exact H i (mem_range.mp hi) t (mem_range.mp ht)

/-- Reflection `j ↦ p * b - j`. -/
lemma uprod_reflect (p b : ℕ) (g : ℕ → ℤ) :
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
lemma unit_le {p b i t : ℕ} (hi : i < b) (ht : t < p - 1) : p * i + t + 1 ≤ p * b := by
  have h1 : p * (i + 1) ≤ p * b := Nat.mul_le_mul_left p hi
  have h2 : p * (i + 1) = p * i + p := by ring
  omega

/-- Product formula: `C(pa, pb) * ∏ j = C(a, b) * ∏ (pa - j)`, the products over the units
`j < p * b`. -/
lemma choose_mul_uprod (p a b : ℕ) (hp : 0 < p) :
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

lemma not_dvd_uprod_id {p : ℕ} (hp : p.Prime) (b : ℕ) :
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
lemma uprod_sub_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (A k b s : ℕ)
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
lemma pow_dvd_choose_mul {p : ℕ} (hp : p.Prime) (Q m s b' : ℕ) (hQ : 0 < Q)
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
lemma choose_mul_pow_congr {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (n m b : ℕ)
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
lemma pow_dvd_choose_of_not_dvd {p : ℕ} (hp : p.Prime) (n k i : ℕ) (hn : 0 < n)
    (hi : ¬ p ∣ i) : p ^ k ∣ (n * p ^ k).choose i := by
  have h := pow_dvd_choose_mul hp (n * p ^ k) k 0 i (Nat.mul_pos hn (pow_pos hp.pos k))
    (dvd_mul_left (p ^ k) n) (Nat.zero_le k) hi
  simpa using h

/-! Power series part. -/

/-- `D` is in the set `N * (series supported off the multiples of p) + N ^ 2 * (any series)`. -/
def InI (p N : ℕ) (D : PowerSeries ℤ) : Prop :=
  ∀ j, ((N : ℤ) ∣ PowerSeries.coeff j D) ∧ (p ∣ j → ((N : ℤ) ^ 2) ∣ PowerSeries.coeff j D)

/-- `G` is supported on the multiples of `p`. -/
def PS (p : ℕ) (G : PowerSeries ℤ) : Prop :=
  ∀ j, ¬ p ∣ j → PowerSeries.coeff j G = 0

lemma InI_add {p N : ℕ} {A B : PowerSeries ℤ} (hA : InI p N A) (hB : InI p N B) :
    InI p N (A + B) := by
  intro j
  rw [map_add]
  exact ⟨dvd_add (hA j).1 (hB j).1, fun h => dvd_add ((hA j).2 h) ((hB j).2 h)⟩

lemma InI_sub {p N : ℕ} {A B : PowerSeries ℤ} (hA : InI p N A) (hB : InI p N B) :
    InI p N (A - B) := by
  intro j
  rw [map_sub]
  exact ⟨dvd_sub (hA j).1 (hB j).1, fun h => dvd_sub ((hA j).2 h) ((hB j).2 h)⟩

lemma InI_mul {p N : ℕ} {A B : PowerSeries ℤ} (hA : InI p N A) (hB : InI p N B) :
    InI p N (A * B) := by
  have key : ∀ j, ((N : ℤ) ^ 2) ∣ PowerSeries.coeff j (A * B) := by
    intro j
    rw [PowerSeries.coeff_mul]
    refine Finset.dvd_sum fun x _ => ?_
    rw [sq]
    exact mul_dvd_mul (hA x.1).1 (hB x.2).1
  intro j
  exact ⟨dvd_trans (dvd_pow_self _ two_ne_zero) (key j), fun _ => key j⟩

lemma InI_mul_PS {p N : ℕ} {A G : PowerSeries ℤ} (hA : InI p N A) (hG : PS p G) :
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

lemma PS_mul {p : ℕ} {A B : PowerSeries ℤ} (hA : PS p A) (hB : PS p B) : PS p (A * B) := by
  intro j hj
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  by_cases h1 : p ∣ x.1
  · have h2 : ¬ p ∣ x.2 := fun h2 => hj (hx ▸ dvd_add h1 h2)
    rw [hB x.2 h2, mul_zero]
  · rw [hA x.1 h1, zero_mul]

lemma InI_mul_sub {p N : ℕ} {A A' B B' : PowerSeries ℤ} (hA : InI p N (A - A'))
    (hB : InI p N (B - B')) (hA' : PS p A') (hB' : PS p B') : InI p N (A * B - A' * B') := by
  have h : A * B - A' * B' = (A - A') * (B - B') + (A - A') * B' + (B - B') * A' := by ring
  rw [h]
  exact InI_add (InI_add (InI_mul hA hB) (InI_mul_PS hA hB')) (InI_mul_PS hB hA')

/-- Division by a series `U` with constant coefficient `1` whose coefficients off the multiples of
`p` are divisible by `N`. -/
lemma InI_of_mul {p N : ℕ} {D U : PowerSeries ℤ} (hU0 : PowerSeries.coeff 0 U = 1)
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
noncomputable def B (c : ℤ) (e : ℕ) : PowerSeries ℤ :=
  1 + PowerSeries.C c * PowerSeries.X ^ e

lemma coeff_B_pow (c : ℤ) (e n j : ℕ) (he : 0 < e) :
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

lemma B_pow_PS (p : ℕ) (hp : 0 < p) (c : ℤ) (e n : ℕ) (he : 0 < e) :
    PS p (B c (e * p) ^ n) := by
  intro j hj
  rw [coeff_B_pow c (e * p) n j (Nat.mul_pos he hp), if_neg]
  intro h
  exact hj (dvd_trans (dvd_mul_left p e) h)

lemma B_pow_InI {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (n m : ℕ) (hn : 0 < n) (c : ℤ)
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

lemma expand_B (p : ℕ) (hp : p ≠ 0) (c : ℤ) (e : ℕ) :
    PowerSeries.expand p hp (B c e) = B c (e * p) := by
  unfold B
  rw [map_add, map_one, map_mul, map_pow, PowerSeries.expand_C, PowerSeries.expand_X, ← pow_mul,
    mul_comm p e]

/-! General factor lists. A factor `(c, e)` stands for `1 + c * x ^ e`. -/

/-- Admissible factor for the prime `p`: `c = 1` or `c = -1`, `0 < e`, `p` does not divide `e`. -/
def Adm (p : ℕ) (f : ℤ × ℕ) : Prop :=
  (f.1 = 1 ∨ f.1 = -1) ∧ 0 < f.2 ∧ ¬ p ∣ f.2

/-- The product of the factors `1 + c * x ^ e` of a list. -/
noncomputable def prodB (L : List (ℤ × ℕ)) : PowerSeries ℤ :=
  (L.map fun f => B f.1 f.2).prod

/-- The same product with every exponent multiplied by `p`. -/
noncomputable def prodBp (p : ℕ) (L : List (ℤ × ℕ)) : PowerSeries ℤ :=
  (L.map fun f => B f.1 (f.2 * p)).prod

lemma prodB_cons (f : ℤ × ℕ) (L : List (ℤ × ℕ)) : prodB (f :: L) = B f.1 f.2 * prodB L := by
  simp [prodB]

lemma prodBp_cons (p : ℕ) (f : ℤ × ℕ) (L : List (ℤ × ℕ)) :
    prodBp p (f :: L) = B f.1 (f.2 * p) * prodBp p L := by
  simp [prodBp]

lemma expand_prodB (p : ℕ) (hp : p ≠ 0) (L : List (ℤ × ℕ)) :
    PowerSeries.expand p hp (prodB L) = prodBp p L := by
  induction L with
  | nil => simp [prodB, prodBp]
  | cons f L ih => rw [prodB_cons, prodBp_cons, map_mul, expand_B, ih]

lemma constantCoeff_B (c : ℤ) (e : ℕ) (he : 0 < e) : PowerSeries.constantCoeff (B c e) = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  simp [B, pow_succ]

lemma constantCoeff_prodB (L : List (ℤ × ℕ)) (hL : ∀ f ∈ L, 0 < f.2) :
    PowerSeries.constantCoeff (prodB L) = 1 := by
  induction L with
  | nil => simp [prodB]
  | cons f L ih =>
    rw [prodB_cons, map_mul, constantCoeff_B _ _ (hL f (by simp)),
      ih (fun g hg => hL g (by simp [hg])), one_mul]

lemma prodBp_pow_PS {p : ℕ} (hp : 0 < p) (L : List (ℤ × ℕ)) (hL : ∀ f ∈ L, 0 < f.2) (k : ℕ) :
    PS p (prodBp p L ^ k) := by
  induction L with
  | nil =>
    intro j hj
    simp only [prodBp, List.map_nil, List.prod_nil, one_pow]
    rw [PowerSeries.coeff_one, if_neg]
    rintro rfl
    exact hj (dvd_zero p)
  | cons f L ih =>
    rw [prodBp_cons, mul_pow]
    exact PS_mul (B_pow_PS p hp f.1 f.2 k (hL f (by simp))) (ih fun g hg => hL g (by simp [hg]))

lemma prodB_pow_InI {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (n m : ℕ) (hn : 0 < n)
    (L : List (ℤ × ℕ)) (hL : ∀ f ∈ L, Adm p f) :
    InI p (p ^ (m + 1)) (prodB L ^ (n * p ^ (m + 1)) - prodBp p L ^ (n * p ^ m)) := by
  induction L with
  | nil =>
    simp only [prodB, prodBp, List.map_nil, List.prod_nil, one_pow, sub_self]
    intro j
    simp
  | cons f L ih =>
    have hf := hL f (by simp)
    have hL' : ∀ g ∈ L, Adm p g := fun g hg => hL g (by simp [hg])
    rw [prodB_cons, prodBp_cons, mul_pow, mul_pow]
    have hcop : Nat.Coprime p f.2 := (Nat.Prime.coprime_iff_not_dvd hp).mpr hf.2.2
    exact InI_mul_sub (B_pow_InI hp hp2 n m hn f.1 hf.1 f.2 hf.2.1 hcop) (ih hL')
      (B_pow_PS p hp.pos f.1 f.2 _ hf.2.1)
      (prodBp_pow_PS hp.pos L (fun g hg => (hL' g hg).2.1) _)

/-- Main criterion, level form: if `F * ∏_den (1 + c x^e) = ∏_num (1 + c x^e)` with all factors
admissible (`c = ±1`, `0 < e`, `p ∤ e`) and `p` an odd prime, then
`p ^ (2 (m + 1))` divides `[x^(n p^(m+1))] F^(n p^(m+1)) - [x^(n p^m)] F^(n p^m)`. -/
theorem supercongr_level (num den : List (ℤ × ℕ)) (F : PowerSeries ℤ)
    (hF : F * prodB den = prodB num) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hnum : ∀ f ∈ num, Adm p f) (hden : ∀ f ∈ den, Adm p f) (n m : ℕ) :
    ((p : ℤ) ^ (2 * (m + 1))) ∣
      PowerSeries.coeff (n * p ^ (m + 1)) (F ^ (n * p ^ (m + 1))) -
        PowerSeries.coeff (n * p ^ m) (F ^ (n * p ^ m)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hp0 : p ≠ 0 := hp.ne_zero
  set N := n * p ^ (m + 1) with hN
  set Q := n * p ^ m with hQ
  have hrelN : F ^ N * prodB den ^ N = prodB num ^ N := by rw [← mul_pow, hF]
  have hrelQ : PowerSeries.expand p hp0 (F ^ Q) * prodBp p den ^ Q = prodBp p num ^ Q := by
    have h := congrArg (fun G => PowerSeries.expand p hp0 (G ^ Q)) hF
    simp only [mul_pow, map_mul, map_pow, expand_prodB] at h
    rw [map_pow]
    exact h
  have iNum := prodB_pow_InI hp hp2 n m hn num hnum
  have iDen := prodB_pow_InI hp hp2 n m hn den hden
  have sDen := prodBp_pow_PS hp.pos den (fun g hg => (hden g hg).2.1) Q
  have sPhi : PS p (PowerSeries.expand p hp0 (F ^ Q)) :=
    fun j hj => PowerSeries.coeff_expand_of_not_dvd p hp0 _ hj
  have hprod : InI p (p ^ (m + 1))
      ((F ^ N - PowerSeries.expand p hp0 (F ^ Q)) * prodB den ^ N) := by
    have h : (F ^ N - PowerSeries.expand p hp0 (F ^ Q)) * prodB den ^ N =
        (prodB num ^ N - prodBp p num ^ Q) -
          (prodB den ^ N - prodBp p den ^ Q) * PowerSeries.expand p hp0 (F ^ Q) := by
      linear_combination hrelN - hrelQ
    rw [h]
    exact InI_sub iNum (InI_mul_PS iDen sPhi)
  have hU0 : PowerSeries.coeff 0 (prodB den ^ N) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow,
      constantCoeff_prodB den (fun g hg => (hden g hg).2.1), one_pow]
  have hU : ∀ j, ¬ p ∣ j → ((p ^ (m + 1) : ℕ) : ℤ) ∣ PowerSeries.coeff j (prodB den ^ N) := by
    intro j hj
    have h1 := (iDen j).1
    rw [map_sub, sDen j hj, sub_zero] at h1
    exact h1
  have hD := InI_of_mul hU0 hU hprod
  have hfin := (hD N).2 (Dvd.dvd.mul_left (dvd_pow_self p (Nat.succ_ne_zero m)) n)
  rw [map_sub] at hfin
  have hco : PowerSeries.coeff N (PowerSeries.expand p hp0 (F ^ Q)) =
      PowerSeries.coeff Q (F ^ Q) := by
    have e : N = p * Q := by rw [hN, hQ, pow_succ]; ring
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

/-- Main criterion: `a(n p^r) ≡ a(n p^(r-1))` modulo `p^(2r)` for `a(n) = [x^n] F^n`. -/
theorem supercongr (num den : List (ℤ × ℕ)) (F : PowerSeries ℤ)
    (hF : F * prodB den = prodB num) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hnum : ∀ f ∈ num, Adm p f) (hden : ∀ f ∈ den, Adm p f) (n r : ℕ) (hr : 1 ≤ r) :
    PowerSeries.coeff (n * p ^ r) (F ^ (n * p ^ r)) ≡
      PowerSeries.coeff (n * p ^ (r - 1)) (F ^ (n * p ^ (r - 1))) [ZMOD (p : ℤ) ^ (2 * r)] := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact (Int.modEq_iff_dvd.mpr (supercongr_level num den F hF hp hp2 hnum hden n m)).symm

/-- The series `∏_num (1 + c x^e) / ∏_den (1 + c x^e)`. -/
noncomputable def Fser (num den : List (ℤ × ℕ)) : PowerSeries ℤ :=
  prodB num * PowerSeries.invOfUnit (prodB den) 1

lemma Fser_mul (num den : List (ℤ × ℕ)) (hden : ∀ f ∈ den, 0 < f.2) :
    Fser num den * prodB den = prodB num := by
  unfold Fser
  rw [mul_assoc, mul_comm (PowerSeries.invOfUnit _ _), PowerSeries.mul_invOfUnit, mul_one]
  rw [constantCoeff_prodB den hden, Units.val_one]

/-- The criterion for the explicit series `Fser num den`, for primes `p ≥ 5`
(any odd prime not dividing an exponent works). -/
theorem supercongr_Fser (num den : List (ℤ × ℕ)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hnum : ∀ f ∈ num, Adm p f) (hden : ∀ f ∈ den, Adm p f) (n r : ℕ) (hr : 1 ≤ r) :
    PowerSeries.coeff (n * p ^ r) (Fser num den ^ (n * p ^ r)) ≡
      PowerSeries.coeff (n * p ^ (r - 1)) (Fser num den ^ (n * p ^ (r - 1)))
        [ZMOD (p : ℤ) ^ (2 * r)] :=
  supercongr num den _ (Fser_mul num den fun f hf => (hden f hf).2.1) hp (by omega) hnum hden n r hr

end A245926D


open Finset

namespace A245926

private def tS (n k : ℕ) : ℤ :=
  (-1 : ℤ) ^ (n + k) * (Nat.choose n k : ℤ) * (Nat.choose (n + k) k : ℤ)
    * (Nat.choose (2 * n + 2 * k) (n + k) : ℤ)

private lemma tS_zero (n k : ℕ) (h : n < k) : tS n k = 0 := by
  simp [tS, Nat.choose_eq_zero_of_lt h]

private lemma tS_fact (n k : ℕ) (h : k ≤ n) :
    (tS n k : ℚ) = (-1) ^ (n + k) * (2 * n + 2 * k).factorial /
      (k.factorial ^ 2 * (n - k).factorial * (n + k).factorial) := by
  unfold tS
  push_cast
  rw [Nat.cast_choose ℚ h, Nat.cast_choose ℚ (by omega : k ≤ n + k),
    Nat.cast_choose ℚ (by omega : n + k ≤ 2 * n + 2 * k),
    show n + k - k = n by omega, show 2 * n + 2 * k - (n + k) = n + k by omega]
  have := n.factorial_pos
  have := k.factorial_pos
  have := (n - k).factorial_pos
  have := (n + k).factorial_pos
  field_simp

private def cS (n : ℕ) : ℤ := -4 * (4 * n + 3) * (4 * n + 5) * (4 * n + 7)
private def pS0 (n : ℕ) : ℤ := 4 * (2 * n + 1) ^ 2 * (4 * n + 7)
private def pS1 (n : ℕ) : ℤ := -2 * (4 * n + 5) * (28 * n ^ 2 + 70 * n + 37)
private def pS2 (n : ℕ) : ℤ := (n + 2) ^ 2 * (4 * n + 3)

private lemma keyS0 (n : ℕ) :
    pS0 n * tS n 0 + pS1 n * tS (n + 1) 0 + pS2 n * tS (n + 2) 0 = cS n * tS (n + 1) 0 := by
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [tS_fact n 0 (by omega), tS_fact (n + 1) 0 (by omega), tS_fact (n + 2) 0 (by omega)]
  simp only [Nat.sub_zero, add_zero, mul_zero, Nat.factorial_zero, Nat.cast_one, one_pow, one_mul]
  rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, show 2 * (n + 2) = 2 * n + 1 + 1 + 1 + 1 by ring]
  simp only [Nat.factorial_succ, pS0, pS1, pS2, cS]
  push_cast
  have := n.factorial_pos
  have := (2 * n).factorial_pos
  field_simp
  ring

private lemma keyS (n k : ℕ) :
    pS0 n * tS n (k + 1) + pS1 n * tS (n + 1) (k + 1) + pS2 n * tS (n + 2) (k + 1)
      = cS n * (tS (n + 1) (k + 1) - tS (n + 1) k) := by
  apply Int.cast_injective (α := ℚ)
  push_cast
  unfold pS0 pS1 pS2 cS
  push_cast
  rcases Nat.lt_or_ge n (k + 1) with h1 | h1
  · rw [tS_zero n (k + 1) h1]
    rcases Nat.lt_or_ge (n + 1) (k + 1) with h2 | h2
    · rw [tS_zero (n + 1) (k + 1) h2]
      rcases Nat.lt_or_ge (n + 1) k with h3 | h3
      · rw [tS_zero (n + 1) k h3]
        rcases Nat.lt_or_ge (n + 2) (k + 1) with h4 | h4
        · rw [tS_zero (n + 2) (k + 1) h4]; ring
        · -- k = n + 1 impossible here (n+1 < k)
          omega
      · -- k = n + 1
        have hk : k = n + 1 := by omega
        subst hk
        rw [tS_fact (n + 2) (n + 1 + 1) (by omega), tS_fact (n + 1) (n + 1) (by omega),
          show n + 2 - (n + 1 + 1) = 0 by omega, show n + 1 - (n + 1) = 0 by omega,
          show 2 * (n + 2) + 2 * (n + 1 + 1) = 2 * (2 * n + 2) + 1 + 1 + 1 + 1 by ring,
          show n + 2 + (n + 1 + 1) = 2 * n + 2 + 1 + 1 by ring,
          show 2 * (n + 1) + 2 * (n + 1) = 2 * (2 * n + 2) by ring,
          show n + 1 + (n + 1) = 2 * n + 2 by ring]
        simp only [Nat.factorial_succ, Nat.factorial_zero]
        push_cast
        have := (2 * (2 * n + 2)).factorial_pos
        have := (2 * n + 2).factorial_pos
        have := n.factorial_pos
        field_simp
        ring
    · -- k = n
      have hk : k = n := by omega
      subst hk
      rw [tS_fact (k + 1) (k + 1) (by omega), tS_fact (k + 2) (k + 1) (by omega),
        tS_fact (k + 1) k (by omega),
        show k + 1 - (k + 1) = 0 by omega, show k + 2 - (k + 1) = 1 by omega,
        show k + 1 - k = 1 by omega,
        show 2 * (k + 1) + 2 * (k + 1) = 4 * k + 1 + 1 + 1 + 1 by ring,
        show 2 * (k + 2) + 2 * (k + 1) = 4 * k + 1 + 1 + 1 + 1 + 1 + 1 by ring,
        show 2 * (k + 1) + 2 * k = 4 * k + 1 + 1 by ring,
        show k + 1 + (k + 1) = 2 * k + 1 + 1 by ring,
        show k + 2 + (k + 1) = 2 * k + 1 + 1 + 1 by ring,
        show k + 1 + k = 2 * k + 1 by ring]
      simp only [Nat.factorial_succ, Nat.factorial_zero]
      push_cast
      have := (4 * k).factorial_pos
      have := (2 * k).factorial_pos
      have := k.factorial_pos
      field_simp
      ring
  · obtain ⟨d, rfl⟩ : ∃ d, n = k + 1 + d := ⟨n - (k + 1), by omega⟩
    rw [tS_fact (k + 1 + d) (k + 1) (by omega), tS_fact (k + 1 + d + 1) (k + 1) (by omega),
      tS_fact (k + 1 + d + 2) (k + 1) (by omega), tS_fact (k + 1 + d + 1) k (by omega),
      show k + 1 + d - (k + 1) = d by omega, show k + 1 + d + 1 - (k + 1) = d + 1 by omega,
      show k + 1 + d + 2 - (k + 1) = d + 1 + 1 by omega,
      show k + 1 + d + 1 - k = d + 1 + 1 by omega,
      show 2 * (k + 1 + d) + 2 * (k + 1) = 2 * (2 * k + d + 2) by ring,
      show 2 * (k + 1 + d + 1) + 2 * (k + 1) = 2 * (2 * k + d + 2) + 1 + 1 by ring,
      show 2 * (k + 1 + d + 2) + 2 * (k + 1) = 2 * (2 * k + d + 2) + 1 + 1 + 1 + 1 by ring,
      show 2 * (k + 1 + d + 1) + 2 * k = 2 * (2 * k + d + 2) by ring,
      show k + 1 + d + (k + 1) = 2 * k + d + 2 by ring,
      show k + 1 + d + 1 + (k + 1) = 2 * k + d + 2 + 1 by ring,
      show k + 1 + d + 2 + (k + 1) = 2 * k + d + 2 + 1 + 1 by ring,
      show k + 1 + d + 1 + k = 2 * k + d + 2 by ring]
    simp only [Nat.factorial_succ]
    push_cast
    have := (2 * (2 * k + d + 2)).factorial_pos
    have := (2 * k + d + 2).factorial_pos
    have := k.factorial_pos
    have := d.factorial_pos
    field_simp
    ring

private def tU (n k : ℕ) : ℤ :=
  (3 : ℤ) ^ k * (Nat.choose (n + k) (2 * k) : ℤ) * (Nat.choose (2 * n) (n - k) : ℤ)

private lemma tU_zero (n k : ℕ) (h : n < k) : tU n k = 0 := by
  simp [tU, Nat.choose_eq_zero_of_lt (by omega : n + k < 2 * k)]

private lemma tU_fact (n k : ℕ) (h : k ≤ n) :
    (tU n k : ℚ) = 3 ^ k * (2 * n).factorial / ((2 * k).factorial * ((n - k).factorial) ^ 2) := by
  unfold tU
  push_cast
  rw [Nat.cast_choose ℚ (by omega : 2 * k ≤ n + k), Nat.cast_choose ℚ (by omega : n - k ≤ 2 * n),
    show n + k - 2 * k = n - k by omega, show 2 * n - (n - k) = n + k by omega]
  have := (2 * n).factorial_pos
  have := (2 * k).factorial_pos
  have := (n - k).factorial_pos
  have := (n + k).factorial_pos
  field_simp

private def pU0 (n : ℕ) : ℤ := (n + 1) * (2 * n + 1) * (4 * n + 7)
private def pU1 (n : ℕ) : ℤ := -(4 * n + 5) * (28 * n ^ 2 + 70 * n + 37)
private def pU2 (n : ℕ) : ℤ := (n + 2) * (2 * n + 3) * (4 * n + 3)
private def QU (n k : ℕ) : ℤ :=
  (4 * n + 7) * k ^ 2 - 10 * (n + 1) * (4 * n + 7) * k + (n + 2) * (52 * n ^ 2 + 131 * n + 74)

private lemma keyU0 (n : ℕ) :
    2 * (pU0 n * tU n 0 + pU1 n * tU (n + 1) 0 + pU2 n * tU (n + 2) 0)
      = -3 * (QU n 1 * tU (n + 1) 0) := by
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [tU_fact n 0 (by omega), tU_fact (n + 1) 0 (by omega), tU_fact (n + 2) 0 (by omega)]
  simp only [Nat.sub_zero, mul_zero, Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero]
  rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, show 2 * (n + 2) = 2 * n + 1 + 1 + 1 + 1 by ring,
    show n + 2 = n + 1 + 1 by ring]
  simp only [Nat.factorial_succ, pU0, pU1, pU2, QU]
  push_cast
  have := n.factorial_pos
  have := (2 * n).factorial_pos
  field_simp
  ring

private lemma keyU (n k : ℕ) :
    2 * (pU0 n * tU n (k + 1) + pU1 n * tU (n + 1) (k + 1) + pU2 n * tU (n + 2) (k + 1))
      = -3 * (QU n (k + 2) * tU (n + 1) (k + 1) - QU n (k + 1) * tU (n + 1) k) := by
  apply Int.cast_injective (α := ℚ)
  push_cast
  unfold pU0 pU1 pU2 QU
  push_cast
  rcases Nat.lt_or_ge n (k + 1) with h1 | h1
  · rw [tU_zero n (k + 1) h1]
    rcases Nat.lt_or_ge (n + 1) (k + 1) with h2 | h2
    · rw [tU_zero (n + 1) (k + 1) h2]
      rcases Nat.lt_or_ge (n + 1) k with h3 | h3
      · rw [tU_zero (n + 1) k h3]
        rcases Nat.lt_or_ge (n + 2) (k + 1) with h4 | h4
        · rw [tU_zero (n + 2) (k + 1) h4]; ring
        · omega
      · have hk : k = n + 1 := by omega
        subst hk
        rw [tU_fact (n + 2) (n + 1 + 1) (by omega), tU_fact (n + 1) (n + 1) (by omega),
          show n + 2 - (n + 1 + 1) = 0 by omega, show n + 1 - (n + 1) = 0 by omega,
          show 2 * (n + 2) = 2 * (n + 1) + 1 + 1 by ring]
        simp only [Nat.factorial_succ, Nat.factorial_zero]
        push_cast
        have := (2 * (n + 1)).factorial_pos
        field_simp
        ring
    · have hk : k = n := by omega
      subst hk
      rw [tU_fact (k + 1) (k + 1) (by omega), tU_fact (k + 2) (k + 1) (by omega),
        tU_fact (k + 1) k (by omega),
        show k + 1 - (k + 1) = 0 by omega, show k + 2 - (k + 1) = 1 by omega,
        show k + 1 - k = 1 by omega,
        show 2 * (k + 2) = 2 * k + 1 + 1 + 1 + 1 by ring,
        show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
      simp only [Nat.factorial_succ, Nat.factorial_zero]
      push_cast
      have := (2 * k).factorial_pos
      field_simp
      ring
  · obtain ⟨d, rfl⟩ : ∃ d, n = k + 1 + d := ⟨n - (k + 1), by omega⟩
    rw [tU_fact (k + 1 + d) (k + 1) (by omega), tU_fact (k + 1 + d + 1) (k + 1) (by omega),
      tU_fact (k + 1 + d + 2) (k + 1) (by omega), tU_fact (k + 1 + d + 1) k (by omega),
      show k + 1 + d - (k + 1) = d by omega, show k + 1 + d + 1 - (k + 1) = d + 1 by omega,
      show k + 1 + d + 2 - (k + 1) = d + 1 + 1 by omega,
      show k + 1 + d + 1 - k = d + 1 + 1 by omega,
      show 2 * (k + 1 + d + 1) = 2 * (k + 1 + d) + 1 + 1 by ring,
      show 2 * (k + 1 + d + 2) = 2 * (k + 1 + d) + 1 + 1 + 1 + 1 by ring,
      show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
    simp only [Nat.factorial_succ]
    push_cast
    have := (2 * (k + 1 + d)).factorial_pos
    have := (2 * k).factorial_pos
    have := d.factorial_pos
    field_simp
    ring

private def S (n : ℕ) : ℤ := ∑ k ∈ range (n + 1), tS n k
private def U (n : ℕ) : ℤ := ∑ k ∈ range (n + 1), tU n k

private lemma sum_ext (f : ℕ → ℤ) (m K : ℕ) (hK : m + 1 ≤ K) (hf : ∀ k, m < k → f k = 0) :
    ∑ k ∈ range (m + 1), f k = ∑ k ∈ range K, f k := by
  rw [← Finset.sum_range_add_sum_Ico _ hK, Finset.sum_eq_zero (s := Ico _ _) (fun k hk => by
    simp only [mem_Ico] at hk; exact hf k (by omega)), add_zero]

private lemma recS (n : ℕ) : pS0 n * S n + pS1 n * S (n + 1) + pS2 n * S (n + 2) = 0 := by
  unfold S
  rw [sum_ext (tS n) n (n + 3) (by omega) (fun k hk => tS_zero n k hk),
    sum_ext (tS (n + 1)) (n + 1) (n + 3) (by omega) (fun k hk => tS_zero _ k hk),
    sum_ext (tS (n + 2)) (n + 2) (n + 3) (by omega) (fun k hk => tS_zero _ k hk),
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, Finset.sum_range_succ']
  rw [Finset.sum_congr rfl (fun k _ => keyS n k), keyS0, ← Finset.mul_sum,
    Finset.sum_range_sub (fun k => tS (n + 1) k), tS_zero (n + 1) (n + 2) (by omega)]
  ring

private lemma recU (n : ℕ) : pU0 n * U n + pU1 n * U (n + 1) + pU2 n * U (n + 2) = 0 := by
  have h : 2 * (pU0 n * U n + pU1 n * U (n + 1) + pU2 n * U (n + 2)) = 0 := by
    unfold U
    rw [sum_ext (tU n) n (n + 3) (by omega) (fun k hk => tU_zero n k hk),
      sum_ext (tU (n + 1)) (n + 1) (n + 3) (by omega) (fun k hk => tU_zero _ k hk),
      sum_ext (tU (n + 2)) (n + 2) (n + 3) (by omega) (fun k hk => tU_zero _ k hk),
      Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_range_succ']
    rw [Finset.sum_congr rfl (fun k _ => keyU n k), keyU0, ← Finset.mul_sum,
      Finset.sum_range_sub (fun k => QU n (k + 1) * tU (n + 1) k), tU_zero (n + 1) (n + 2) (by omega)]
    ring
  linarith

private def cb (n : ℕ) : ℤ := (Nat.choose (2 * n) n : ℤ)

private lemma cb_succ (n : ℕ) : ((n : ℤ) + 1) * cb (n + 1) = 2 * (2 * n + 1) * cb n := by
  have h := Nat.succ_mul_centralBinom_succ n
  simp only [Nat.centralBinom_eq_two_mul_choose] at h
  unfold cb
  exact_mod_cast h

private lemma S_eq (n : ℕ) : S n = cb n * U n ∧ S (n + 1) = cb (n + 1) * U (n + 1) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [S, U, cb, tS, tU]
    · simp [S, U, cb, tS, tU, Finset.sum_range_succ]
      norm_num [Nat.choose]
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have hS := recS n
    have hU := recU n
    have c1 := cb_succ n
    have c2 := cb_succ (n + 1)
    have hne : pS2 n ≠ 0 := by unfold pS2; positivity
    have key : pS2 n * (S (n + 2) - cb (n + 2) * U (n + 2)) = 0 := by
      rw [ih.1, ih.2] at hS
      unfold pS0 pS1 at hS
      unfold pS2 at hS ⊢
      unfold pU0 pU1 pU2 at hU
      push_cast at c1 c2 hS hU ⊢
      linear_combination hS - (((n : ℤ) + 2) * (4 * n + 3) * U (n + 2)) * c2
        - 2 * cb (n + 1) * hU + 2 * (2 * (n : ℤ) + 1) * (4 * n + 7) * U n * c1
    have := (mul_eq_zero.mp key).resolve_left hne
    linarith


open PowerSeries


private lemma cert (k j e : ℕ) :
    (2 * ((k : ℚ) + 1)) * (2 * (2 * k + 3) * (((2 * (k + j + e + 2)).choose e : ℕ) *
        ((2 * k + 3 + j).choose (2 * k + 3) : ℕ))
      - (j + 1 + e) * (((2 * (k + j + e + 2)).choose (e + 1) : ℕ) * ((2 * k + 1 + j).choose (2 * k + 1) : ℕ)))
    = (j + 1) * ((j : ℚ) + 1 + 2 * (k + 1) - (j + 1 + e)) *
        (((2 * (k + j + e + 2)).choose e : ℕ) * ((2 * k + 2 + j).choose (2 * k + 1) : ℕ))
      - j * ((j : ℚ) + 2 * (k + 1) - (j + 1 + e)) *
        (((2 * (k + j + e + 2)).choose (e + 1) : ℕ) * ((2 * k + 1 + j).choose (2 * k + 1) : ℕ)) := by
  rw [Nat.cast_choose ℚ (by omega : e ≤ 2 * (k + j + e + 2)),
    Nat.cast_choose ℚ (by omega : e + 1 ≤ 2 * (k + j + e + 2)),
    Nat.cast_choose ℚ (by omega : 2 * k + 3 ≤ 2 * k + 3 + j),
    Nat.cast_choose ℚ (by omega : 2 * k + 1 ≤ 2 * k + 2 + j),
    Nat.cast_choose ℚ (by omega : 2 * k + 1 ≤ 2 * k + 1 + j),
    show 2 * (k + j + e + 2) - e = (2 * k + 2 * j + e + 3) + 1 by omega,
    show 2 * (k + j + e + 2) - (e + 1) = 2 * k + 2 * j + e + 3 by omega,
    show 2 * k + 3 + j - (2 * k + 3) = j by omega,
    show 2 * k + 2 + j - (2 * k + 1) = j + 1 by omega,
    show 2 * k + 1 + j - (2 * k + 1) = j by omega,
    show 2 * k + 3 + j = (2 * k + 1 + j) + 1 + 1 by omega,
    show 2 * k + 2 + j = (2 * k + 1 + j) + 1 by omega,
    show 2 * k + 3 = (2 * k + 1) + 1 + 1 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  have := (2 * (k + j + e + 2)).factorial_pos
  have := (2 * k + 2 * j + e + 3).factorial_pos
  have := (2 * k + 1 + j).factorial_pos
  have := (2 * k + 1).factorial_pos
  have := j.factorial_pos
  have := e.factorial_pos
  field_simp
  ring

private noncomputable def Gm : PowerSeries ℤ := PowerSeries.mk 1

private lemma Gm_mul : Gm * (1 - X) = 1 := mk_one_mul_one_sub_eq_one ℤ

private lemma coeff_Gm_pow (d j : ℕ) : coeff j (Gm ^ (d + 1)) = ((d + j).choose d : ℤ) := by
  unfold Gm
  rw [mk_one_pow_eq_mk_choose_add, coeff_mk]

private lemma coeff_onePX_pow (N j : ℕ) : coeff j ((1 + X : PowerSeries ℤ) ^ N) = (N.choose j : ℤ) := by
  have h : ((1 + X : PowerSeries ℤ) ^ N) = (((1 + Polynomial.X : Polynomial ℤ) ^ N : Polynomial ℤ) : PowerSeries ℤ) := by
    push_cast; rfl
  rw [h, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

private noncomputable def h (n k : ℕ) : ℤ := coeff (n - k) ((1 + X : PowerSeries ℤ) ^ (2 * n) * Gm ^ (2 * k))

private noncomputable def F : PowerSeries ℤ := (1 + X) ^ 2 * (1 + 3 * X * Gm ^ 2)

private lemma coeff_F_pow (n : ℕ) :
    coeff n (F ^ n) = ∑ k ∈ range (n + 1), (n.choose k : ℤ) * 3 ^ k * h n k := by
  unfold F
  rw [mul_pow, ← pow_mul, add_comm (1 : PowerSeries ℤ) (3 * X * Gm ^ 2), add_pow (3 * X * Gm ^ 2 : PowerSeries ℤ) 1 n, Finset.mul_sum,
    map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Nat.le_of_lt_succ (mem_range.mp hk)
  have e : (1 + X : PowerSeries ℤ) ^ (2 * n) * ((3 * X * Gm ^ 2) ^ k * 1 ^ (n - k) * (n.choose k : PowerSeries ℤ))
      = PowerSeries.C ((3 : ℤ) ^ k * n.choose k) * (X ^ k * ((1 + X) ^ (2 * n) * Gm ^ (2 * k))) := by
    rw [map_mul, map_pow, map_natCast, map_ofNat]
    ring
  rw [e, coeff_C_mul, coeff_X_pow_mul', if_pos hk']
  unfold h
  ring

private lemma h_zero (n : ℕ) : h n 0 = ((2 * n).choose n : ℤ) := by
  unfold h
  rw [Nat.sub_zero, mul_zero, pow_zero, mul_one, coeff_onePX_pow]

private lemma h_top (n : ℕ) (hn : 1 ≤ n) : h n n = 1 := by
  unfold h
  rw [Nat.sub_self, coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton,
    coeff_onePX_pow, show 2 * n = (2 * n - 1) + 1 by omega, coeff_Gm_pow]
  simp

private lemma h_sum (n k : ℕ) (hk : k + 1 ≤ n) :
    h n (k + 1) = ∑ j ∈ range (n - (k + 1) + 1),
      ((2 * n).choose (n - (k + 1) - j) : ℤ) * ((2 * k + 1 + j).choose (2 * k + 1) : ℤ) := by
  unfold h
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := mem_range.mp hj
  rw [coeff_onePX_pow, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, coeff_Gm_pow,
    show n - (k + 1) + 1 - 1 - j = n - (k + 1) - j by omega,
    show n - (k + 1) - (n - (k + 1) - j) = j by omega]

private lemma h_rec (n k : ℕ) (hk : k + 2 ≤ n) :
    ((n - (k + 1) : ℕ) : ℚ) * (h n (k + 1) : ℚ) = 2 * (2 * k + 3) * (h n (k + 2) : ℚ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = k + m + 2 := ⟨n - (k + 2), by omega⟩
  rw [h_sum _ k (by omega), h_sum _ (k + 1) (by omega),
    show k + m + 2 - (k + 1) = m + 1 by omega, show k + m + 2 - (k + 1 + 1) = m by omega]
  push_cast
  set a : ℕ → ℚ := fun j =>
    (((2 * (k + m + 2)).choose (m + 1 - j) : ℕ) : ℚ) * (((2 * k + 1 + j).choose (2 * k + 1) : ℕ) : ℚ) with ha
  set b : ℕ → ℚ := fun j =>
    (((2 * (k + m + 2)).choose (m - j) : ℕ) : ℚ) * (((2 * (k + 1) + 1 + j).choose (2 * (k + 1) + 1) : ℕ) : ℚ)
    with hb
  set g : ℕ → ℚ := fun j => (j : ℚ) * ((j : ℚ) + 2 * (k + 1) - (m + 1)) * a j with hg
  clear_value a b g
  have step : ∀ j ∈ range (m + 1),
      (2 * ((k : ℚ) + 1)) * (2 * (2 * k + 3) * b j - (m + 1) * a j) = g (j + 1) - g j := by
    intro j hj
    have hj' := mem_range.mp hj
    obtain ⟨e, he⟩ : ∃ e, m = j + e := ⟨m - j, by omega⟩
    have c := cert k j e
    simp only [ha, hb, hg]
    rw [show m + 1 - j = e + 1 by omega, show m - j = e by omega, show m + 1 - (j + 1) = e by omega,
      show 2 * (k + 1) + 1 + j = 2 * k + 3 + j by ring, show 2 * (k + 1) + 1 = 2 * k + 3 by ring,
      show 2 * k + 1 + (j + 1) = 2 * k + 2 + j by ring,
      show k + m + 2 = k + j + e + 2 by omega]
    have hm : (m : ℚ) = j + e := by exact_mod_cast he
    rw [hm]
    push_cast
    linear_combination c
  have hsum := Finset.sum_congr rfl step
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_range_sub g] at hsum
  have hA : ∑ j ∈ range (m + 1 + 1), a j = ∑ j ∈ range (m + 1), a j + a (m + 1) := Finset.sum_range_succ _ _
  have hg0 : g 0 = 0 := by simp [hg]
  have hgm : g (m + 1) = (m + 1) * (2 * (k + 1)) * a (m + 1) := by
    simp only [hg]; push_cast; ring
  rw [hA]
  rw [hg0, hgm] at hsum
  have hk0 : (2 * ((k : ℚ) + 1)) ≠ 0 := by positivity
  apply mul_left_cancel₀ hk0
  rw [show (∑ i ∈ range (m + 1), b i) = (range (m + 1)).sum b from rfl] at hsum
  linear_combination (-1) * hsum

private lemma h_closed (n k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    (h n k : ℚ) = (2 * n).factorial * k.factorial / ((2 * k).factorial * (n - k).factorial * n.factorial) := by
  obtain ⟨t, rfl⟩ : ∃ t, k = n - t := ⟨n - k, by omega⟩
  induction t with
  | zero =>
    rw [Nat.sub_zero, h_top n (by omega), Nat.sub_self, Nat.factorial_zero]
    have := (2 * n).factorial_pos
    have := n.factorial_pos
    push_cast
    field_simp
  | succ t ih =>
    have ih' := ih (by omega) (by omega)
    obtain ⟨k, hk⟩ : ∃ k, n - (t + 1) = k + 1 := ⟨n - (t + 1) - 1, by omega⟩
    rw [hk]
    have hr := h_rec n k (by omega)
    rw [show n - t = k + 2 by omega] at ih'
    rw [ih'] at hr
    have hnk : ((n - (k + 1) : ℕ) : ℚ) ≠ 0 := by
      have : 0 < n - (k + 1) := by omega
      positivity
    rw [show n - (k + 2) = (n - (k + 1) - 1) by omega] at hr
    obtain ⟨r, hr'⟩ : ∃ r, n - (k + 1) = r + 1 := ⟨n - (k + 1) - 1, by omega⟩
    rw [hr', Nat.add_sub_cancel] at hr
    rw [hr']
    rw [show 2 * (k + 2) = 2 * (k + 1) + 1 + 1 by ring, show k + 2 = k + 1 + 1 by ring,
      Nat.factorial_succ (2 * (k + 1) + 1), Nat.factorial_succ (2 * (k + 1)),
      Nat.factorial_succ (k + 1)] at hr
    rw [Nat.factorial_succ r]
    push_cast at hr ⊢
    have := (2 * n).factorial_pos
    have := n.factorial_pos
    have := (k + 1).factorial_pos
    have := (2 * (k + 1)).factorial_pos
    have := r.factorial_pos
    have hr0 : ((r : ℚ) + 1) ≠ 0 := by positivity
    apply mul_left_cancel₀ hr0
    rw [hr]
    field_simp
    ring

private lemma term_eq (n k : ℕ) (hk : k ≤ n) : (n.choose k : ℤ) * 3 ^ k * h n k = tU n k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · rw [h_zero]; simp [tU]
  · apply Int.cast_injective (α := ℚ)
    push_cast
    rw [h_closed n k hk1 hk, tU_fact n k hk, Nat.cast_choose ℚ hk]
    have := (2 * n).factorial_pos
    have := n.factorial_pos
    have := k.factorial_pos
    have := (2 * k).factorial_pos
    have := (n - k).factorial_pos
    field_simp

private lemma coeff_F_pow_eq (n : ℕ) :
    coeff n (F ^ n) = ∑ k ∈ range (n + 1), tU n k := by
  rw [coeff_F_pow]
  exact Finset.sum_congr rfl (fun k hk => term_eq n k (Nat.le_of_lt_succ (mem_range.mp hk)))

private lemma Fmul : F * A245926D.prodB [(-1, 1), (-1, 1), (-1, 1)]
    = A245926D.prodB [(1, 1), (1, 1), (-1, 3)] := by
  have hG := Gm_mul
  simp only [A245926D.prodB, A245926D.B, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    map_neg, map_one, pow_one, F]
  linear_combination ((1 + X) ^ 2 * 3 * X * (1 - X) * (Gm * (1 - X) + 1) : PowerSeries ℤ) * hG

private lemma a_eq (m : ℕ) : OMA.S_oeis_a245926.a m = coeff m (F ^ m) := by
  have h1 : OMA.S_oeis_a245926.a m = S m / cb m := rfl
  have hcb : cb m ≠ 0 := by
    unfold cb
    exact_mod_cast (Nat.choose_pos (by omega : m ≤ 2 * m)).ne'
  rw [h1, (S_eq m).1, Int.mul_ediv_cancel_left _ hcb, coeff_F_pow_eq]
  rfl

end A245926

open A245926 in
theorem OMA.solution : type_of% @OMA.S_oeis_a245926.main := by
  intro p hp hp5 n k hn hk
  rw [a_eq, a_eq]
  have hadm : ∀ e : ℕ, e = 1 ∨ e = 3 → ¬ p ∣ e := by
    intro e he hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  refine A245926D.supercongr [(1, 1), (1, 1), (-1, 3)] [(-1, 1), (-1, 1), (-1, 1)] F Fmul hp
    (by omega) ?_ ?_ n k hk
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl <;>
      exact ⟨by norm_num, by norm_num, hadm _ (by norm_num)⟩
  · intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl <;>
      exact ⟨by norm_num, by norm_num, hadm _ (by norm_num)⟩
