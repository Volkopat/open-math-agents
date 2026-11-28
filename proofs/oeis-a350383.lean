import OMAStatements.S_oeis_a350383
import Mathlib

/-!
LtsDwork: supercongruences a(n p^r) = a(n p^(r-1)) mod p^(2r) for a(n) = [x^n] F^n,
F a product of factors (1 +- x^e)^(+-1). Method of the workspace proofs of A333579 / A370159.
-/

open Finset

namespace LtsDwork

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

/-! Closure class for the supercongruence. -/

def Good (p : ℕ) (hp0 : p ≠ 0) (F : PowerSeries ℤ) : Prop :=
  ∀ n m : ℕ, 0 < n → InI p (p ^ (m + 1))
    (F ^ (n * p ^ (m + 1)) - PowerSeries.expand p hp0 (F ^ (n * p ^ m)))

lemma PS_C (p : ℕ) (a : ℤ) : PS p (PowerSeries.C a) := by
  intro j hj
  rw [PowerSeries.coeff_C, if_neg]
  rintro rfl
  exact hj (dvd_zero p)

lemma PS_expand (p : ℕ) (hp0 : p ≠ 0) (F : PowerSeries ℤ) : PS p (PowerSeries.expand p hp0 F) :=
  fun _ hj => PowerSeries.coeff_expand_of_not_dvd p hp0 _ hj

lemma Good_one (p : ℕ) (hp0 : p ≠ 0) : Good p hp0 1 := by
  intro n m _ j
  simp

lemma Good_mul {p : ℕ} {hp0 : p ≠ 0} {F G : PowerSeries ℤ} (hF : Good p hp0 F)
    (hG : Good p hp0 G) : Good p hp0 (F * G) := by
  intro n m hn
  rw [mul_pow, mul_pow, map_mul]
  exact InI_mul_sub (hF n m hn) (hG n m hn) (PS_expand _ _ _) (PS_expand _ _ _)

lemma Good_neg {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {hp0 : p ≠ 0} {F : PowerSeries ℤ}
    (hF : Good p hp0 F) : Good p hp0 (-F) := by
  intro n m hn
  obtain ⟨t, ht⟩ := hp.odd_of_ne_two hp2
  have hsign : ((-1 : PowerSeries ℤ)) ^ (n * p ^ (m + 1)) = (-1) ^ (n * p ^ m) := by
    rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := n * p ^ m)]
    congr 1
    rw [pow_succ, ← mul_assoc, ht, Nat.mul_mod, Nat.add_mod, Nat.mul_mod 2 t]
    simp
  have h : (-F) ^ (n * p ^ (m + 1)) - PowerSeries.expand p hp0 ((-F) ^ (n * p ^ m)) =
      (F ^ (n * p ^ (m + 1)) - PowerSeries.expand p hp0 (F ^ (n * p ^ m))) *
        PowerSeries.C ((-1) ^ (n * p ^ m)) := by
    rw [neg_eq_neg_one_mul, mul_pow, mul_pow, map_mul, hsign, map_pow, map_neg, map_one]
    simp only [map_pow, map_neg, map_one]
    ring
  rw [h]
  exact InI_mul_PS (hF n m hn) (PS_C p _)

lemma Good_inv {p : ℕ} {hp0 : p ≠ 0} {F G : PowerSeries ℤ} (hF : Good p hp0 F)
    (hFG : F * G = 1) : Good p hp0 G := by
  intro n m hn
  set N := n * p ^ (m + 1)
  set Q := n * p ^ m
  have hc : PowerSeries.constantCoeff F * PowerSeries.constantCoeff G = 1 := by
    rw [← map_mul, hFG, map_one]
  set a := PowerSeries.constantCoeff G ^ N
  have h1 : G ^ N * F ^ N = 1 := by rw [← mul_pow, mul_comm, hFG, one_pow]
  have h2 : PowerSeries.expand p hp0 (G ^ Q) * PowerSeries.expand p hp0 (F ^ Q) = 1 := by
    rw [← map_mul, ← mul_pow, mul_comm G, hFG, one_pow, map_one]
  have hD : (G ^ N - PowerSeries.expand p hp0 (G ^ Q)) * (F ^ N * PowerSeries.C a) =
      ((F ^ N - PowerSeries.expand p hp0 (F ^ Q)) * (-PowerSeries.expand p hp0 (G ^ Q))) *
        PowerSeries.C a := by
    linear_combination (PowerSeries.C a) * (h1 - h2)
  have hI : InI p (p ^ (m + 1)) ((G ^ N - PowerSeries.expand p hp0 (G ^ Q)) *
      (F ^ N * PowerSeries.C a)) := by
    rw [hD]
    refine InI_mul_PS (InI_mul_PS (hF n m hn) ?_) (PS_C p a)
    intro j hj
    rw [map_neg, PS_expand p hp0 _ j hj, neg_zero]
  refine InI_of_mul ?_ ?_ hI
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_pow, PowerSeries.constantCoeff_C,
      ← mul_pow, hc, one_pow]
  · intro j hj
    rw [PowerSeries.coeff_mul_C]
    have h3 := (hF n m hn j).1
    rw [map_sub, PS_expand p hp0 _ j hj, sub_zero] at h3
    exact Dvd.dvd.mul_right h3 _

lemma Good_B {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (c : ℤ) (hc : c = 1 ∨ c = -1) (e : ℕ)
    (he : 0 < e) (hpe : ¬ p ∣ e) : Good p hp.ne_zero (B c e) := by
  intro n m hn
  rw [map_pow, expand_B]
  exact B_pow_InI hp hp2 n m hn c hc e he ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpe)

lemma Good_prod {p : ℕ} {hp0 : p ≠ 0} (s : Finset ℕ) (g : ℕ → PowerSeries ℤ)
    (h : ∀ i ∈ s, Good p hp0 (g i)) : Good p hp0 (∏ i ∈ s, g i) := by
  induction s using Finset.induction_on with
  | empty => simpa using Good_one p hp0
  | insert x s hx ih =>
    rw [Finset.prod_insert hx]
    exact Good_mul (h x (by simp)) (ih fun i hi => h i (by simp [hi]))

lemma Good_mprod {p : ℕ} {hp0 : p ≠ 0} (s : Multiset (PowerSeries ℤ))
    (h : ∀ x ∈ s, Good p hp0 x) : Good p hp0 s.prod := by
  induction s using Multiset.induction_on with
  | empty => simpa using Good_one p hp0
  | cons x s ih =>
    rw [Multiset.prod_cons]
    exact Good_mul (h x (by simp)) (ih fun i hi => h i (by simp [hi]))

/-- The integer cyclotomic power series. -/
noncomputable def Cy (d : ℕ) : PowerSeries ℤ := ((Polynomial.cyclotomic d ℤ : Polynomial ℤ) : PowerSeries ℤ)

lemma Cy_rel (d : ℕ) (hd : 0 < d) :
    Cy d * ∏ i ∈ Nat.properDivisors d, Cy i = PowerSeries.X ^ d - 1 := by
  have h := congrArg (Polynomial.coeToPowerSeries.ringHom (R := ℤ))
    (Polynomial.prod_cyclotomic_eq_X_pow_sub_one hd ℤ)
  rw [← Nat.cons_self_properDivisors hd.ne', Finset.prod_cons, map_mul, map_prod] at h
  simpa [Cy, Polynomial.coeToPowerSeries.ringHom_apply] using h

lemma Cy_unit (d : ℕ) (hd : 0 < d) : IsUnit (PowerSeries.constantCoeff (Cy d)) := by
  have h := congrArg PowerSeries.constantCoeff (Cy_rel d hd)
  rw [map_mul] at h
  have hu : IsUnit (PowerSeries.constantCoeff (PowerSeries.X ^ d - 1 : PowerSeries ℤ)) := by
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    simp [pow_succ]
  rw [← h] at hu
  exact isUnit_of_mul_isUnit_left hu

lemma Cy_Good {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ d, 0 < d → d < p → Good p hp.ne_zero (Cy d) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd hdp
    have hPr : Good p hp.ne_zero (∏ i ∈ Nat.properDivisors d, Cy i) := by
      refine Good_prod _ _ fun i hi => ?_
      have hi' := Nat.mem_properDivisors.mp hi
      have hi0 : 0 < i := Nat.pos_of_dvd_of_pos hi'.1 hd
      exact ih i hi'.2 hi0 (by omega)
    have hrel := Cy_rel d hd
    have hXu : IsUnit (PowerSeries.X ^ d - 1 : PowerSeries ℤ) := by
      rw [PowerSeries.isUnit_iff_constantCoeff]
      obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
      simp [pow_succ]
    rw [← hrel] at hXu
    obtain ⟨G, hG⟩ := (isUnit_of_mul_isUnit_right hXu).exists_right_inv
    have hGg := Good_inv hPr hG
    have hX : Good p hp.ne_zero (PowerSeries.X ^ d - 1) := by
      have e : (PowerSeries.X ^ d - 1 : PowerSeries ℤ) = -(B (-1) d) := by
        simp [B]; ring
      rw [e]
      refine Good_neg hp hp2 (Good_B hp hp2 (-1) (Or.inr rfl) d hd ?_)
      intro h
      exact absurd (Nat.le_of_dvd hd h) (by omega)
    have e2 : Cy d = (PowerSeries.X ^ d - 1) * G := by
      rw [← hrel, mul_assoc, hG, mul_one]
    rw [e2]
    exact Good_mul hX hGg

lemma Good_congr {p : ℕ} (hp : p.Prime) {E : PowerSeries ℤ} (hE : Good p hp.ne_zero E)
    (k n r : ℕ) (hn : 0 < n) (hr : 0 < r) :
    ((p : ℤ) ^ (2 * r)) ∣ PowerSeries.coeff (k * p ^ r) (E ^ (n * p ^ r)) -
      PowerSeries.coeff (k * p ^ (r - 1)) (E ^ (n * p ^ (r - 1))) := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have hD := (hE n m hn (k * p ^ (m + 1))).2 ⟨k * p ^ m, by rw [pow_succ]; ring⟩
  rw [map_sub] at hD
  have hco : PowerSeries.coeff (k * p ^ (m + 1))
      (PowerSeries.expand p hp.ne_zero (E ^ (n * p ^ m))) =
      PowerSeries.coeff (k * p ^ m) (E ^ (n * p ^ m)) := by
    have e : k * p ^ (m + 1) = p * (k * p ^ m) := by rw [pow_succ]; ring
    rw [e]
    exact PowerSeries.coeff_expand_mul p hp.ne_zero _ _
  rw [hco] at hD
  have hsq : (((p ^ (m + 1) : ℕ) : ℤ) ^ 2) = (p : ℤ) ^ (2 * (m + 1)) := by
    push_cast
    rw [← pow_mul]
    congr 1
    ring
  rw [hsq] at hD
  exact hD

lemma unit_mprod (s : Multiset ℕ) (hs : ∀ d ∈ s, 0 < d) : IsUnit (s.map Cy).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    refine IsUnit.mul ?_ (ih fun d hd => hs d (by simp [hd]))
    rw [PowerSeries.isUnit_iff_constantCoeff]
    exact Cy_unit x (hs x (by simp))

lemma Good_mprodCy {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (s : Multiset ℕ) (hs : ∀ d ∈ s, 0 < d)
    (hsp : ∀ d ∈ s, d < p) : Good p hp.ne_zero (s.map Cy).prod := by
  refine Good_mprod _ fun x hx => ?_
  obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.mp hx
  exact Cy_Good hp hp2 d (hs d hd) (hsp d hd)

end LtsDwork

open LtsDwork in
theorem OMA.solution : type_of% @OMA.S_oeis_a350383.main := by
  refine ⟨?_, ?_⟩
  · intro p hp hp5 n r hn hr
    have hp2 : p ≠ 2 := by omega
    set E := PowerSeries.invOfUnit (1 + PowerSeries.X + PowerSeries.X ^ 2 : PowerSeries ℤ) 1
    have hC3 : Cy 3 = 1 + PowerSeries.X + PowerSeries.X ^ 2 := by
      simp [Cy, Polynomial.cyclotomic_three]
      ring
    have hinv : Cy 3 * E = 1 := by
      rw [hC3]
      exact PowerSeries.mul_invOfUnit _ _ (by simp)
    have hE := Good_inv (Cy_Good hp hp2 3 (by norm_num) (by omega)) hinv
    have h := Good_congr hp hE n n r hn hr
    unfold OMA.S_oeis_a350383.a
    exact h
  · intro k hk m G H hG hH
    refine ⟨G.sum + H.sum + 2, ?_⟩
    intro p hp hBp n r hn hr
    have hp2 : p ≠ 2 := by omega
    have hGp : ∀ d ∈ G, d < p := fun d hd => by
      have := Multiset.le_sum_of_mem hd
      omega
    have hHp : ∀ d ∈ H, d < p := fun d hd => by
      have := Multiset.le_sum_of_mem hd
      omega
    set AG := (G.map Cy).prod
    set AH := (H.map Cy).prod
    obtain ⟨HI, hHI⟩ := (unit_mprod H hH).exists_right_inv
    set F := AG * HI
    have hFu : IsUnit F := by
      refine IsUnit.mul (unit_mprod G hG) ?_
      exact isUnit_of_mul_isUnit_right (hHI ▸ isUnit_one)
    obtain ⟨FI, hFI⟩ := hFu.exists_right_inv
    have gF : Good p hp.ne_zero F :=
      Good_mul (Good_mprodCy hp hp2 G hG hGp) (Good_inv (Good_mprodCy hp hp2 H hH hHp) hHI)
    have gFI : Good p hp.ne_zero FI := Good_inv gF hFI
    set φ := PowerSeries.map (Int.castRingHom ℚ)
    have hcy : ∀ d, φ (Cy d) = OMA.S_oeis_a350383.cyc d := by
      intro d
      ext j
      simp only [φ, Cy, OMA.S_oeis_a350383.cyc, PowerSeries.coeff_map, Polynomial.coeff_coe]
      rw [← Polynomial.map_cyclotomic d (Int.castRingHom ℚ), Polynomial.coeff_map]
    have hmp : ∀ s : Multiset ℕ, φ (s.map Cy).prod = (s.map OMA.S_oeis_a350383.cyc).prod := by
      intro s
      rw [map_multiset_prod, Multiset.map_map]
      congr 1
      exact Multiset.map_congr rfl fun d _ => hcy d
    have inv_of : ∀ A B : PowerSeries ℤ, A * B = 1 → (φ A)⁻¹ = φ B := by
      intro A B hAB
      have h1 : φ B * φ A = 1 := by rw [← map_mul, mul_comm, hAB, map_one]
      refine (PowerSeries.inv_eq_iff_mul_eq_one ?_).mpr h1
      intro h0
      have := congrArg PowerSeries.constantCoeff h1
      rw [map_mul, h0, mul_zero, map_one] at this
      exact zero_ne_one this
    have hf : OMA.S_oeis_a350383.f G H = φ F := by
      unfold OMA.S_oeis_a350383.f
      rw [← hmp G, ← hmp H, inv_of AH HI hHI, map_mul]
    have hfi : (OMA.S_oeis_a350383.f G H)⁻¹ = φ FI := by
      rw [hf, inv_of F FI hFI]
    -- reduce to an integer series E and exponent multiplier t
    have key : ∃ E : PowerSeries ℤ, ∃ t : ℕ, Good p hp.ne_zero E ∧ ∀ N : ℕ, 0 < N →
        OMA.S_oeis_a350383.gen k m G H N = ((PowerSeries.coeff (k * N) (E ^ (t * N)) : ℤ) : ℚ) := by
      obtain ⟨t, rfl | rfl⟩ := Int.eq_nat_or_neg m
      · refine ⟨F, t, gF, fun N _ => ?_⟩
        unfold OMA.S_oeis_a350383.gen OMA.S_oeis_a350383.fpow
        have e1 : ((t : ℤ) * (N : ℤ)) = ((t * N : ℕ) : ℤ) := by push_cast; ring
        rw [e1, if_pos (Int.natCast_nonneg _), Int.toNat_natCast, hf, ← map_pow,
          PowerSeries.coeff_map]
        rfl
      · rcases Nat.eq_zero_or_pos t with rfl | ht
        · refine ⟨F, 0, gF, fun N _ => ?_⟩
          unfold OMA.S_oeis_a350383.gen OMA.S_oeis_a350383.fpow
          simp
        · refine ⟨FI, t, gFI, fun N hN => ?_⟩
          unfold OMA.S_oeis_a350383.gen OMA.S_oeis_a350383.fpow
          have e1 : -((t : ℤ)) * (N : ℤ) = -((t * N : ℕ) : ℤ) := by push_cast; ring
          have hpos : 0 < t * N := Nat.mul_pos ht hN
          rw [e1, if_neg (by omega), neg_neg, Int.toNat_natCast, hfi, ← map_pow,
            PowerSeries.coeff_map]
          rfl
    obtain ⟨E, t, gE, hgen⟩ := key
    have hpr : 0 < n * p ^ r := Nat.mul_pos hn (pow_pos hp.pos r)
    have hpr' : 0 < n * p ^ (r - 1) := Nat.mul_pos hn (pow_pos hp.pos _)
    rw [hgen _ hpr, hgen _ hpr']
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · refine ⟨0, ?_⟩
      have h1 : k * (n * p ^ r) ≠ 0 := (Nat.mul_pos hk hpr).ne'
      have h2 : k * (n * p ^ (r - 1)) ≠ 0 := (Nat.mul_pos hk hpr').ne'
      simp [PowerSeries.coeff_one, h1, h2]
    obtain ⟨z, hz⟩ := Good_congr hp gE (k * n) (t * n) r (Nat.mul_pos ht hn) hr
    refine ⟨z, ?_⟩
    have e1 : k * (n * p ^ r) = k * n * p ^ r := by ring
    have e2 : t * (n * p ^ r) = t * n * p ^ r := by ring
    have e3 : k * (n * p ^ (r - 1)) = k * n * p ^ (r - 1) := by ring
    have e4 : t * (n * p ^ (r - 1)) = t * n * p ^ (r - 1) := by ring
    rw [e1, e2, e3, e4, ← Int.cast_sub, hz]
    push_cast
    ring
