import OMAStatements.S_oeis_a255672
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


/-- constantCoeff of `B c e` with `0 < e` (lib copy). -/
lemma constantCoeff_B' (c : ℤ) (e : ℕ) (he : 0 < e) : PowerSeries.constantCoeff (B c e) = 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  simp [B, pow_succ]

end LtsDwork

namespace A255672
open LtsDwork OMA.S_oeis_a255672

/-- coefficientwise ideal: all coefficients divisible by `p^(m+1)`, and by `p^(m+1+s)` when `p^s ∣ j`, `s ≤ m+1`. -/
def Jm (p m : ℕ) (G : PowerSeries ℤ) : Prop :=
  ∀ j, ((p : ℤ) ^ (m + 1) ∣ PowerSeries.coeff j G) ∧
    ∀ s, p ^ s ∣ j → s ≤ m + 1 → ((p : ℤ) ^ (m + 1 + s) ∣ PowerSeries.coeff j G)

lemma Jm_add {p m : ℕ} {A B : PowerSeries ℤ} (hA : Jm p m A) (hB : Jm p m B) : Jm p m (A + B) := by
  intro j
  rw [map_add]
  exact ⟨dvd_add (hA j).1 (hB j).1, fun s h1 h2 => dvd_add ((hA j).2 s h1 h2) ((hB j).2 s h1 h2)⟩

lemma Jm_mul {p m : ℕ} {A B : PowerSeries ℤ} (hA : Jm p m A) (hB : Jm p m B) : Jm p m (A * B) := by
  have key : ∀ j, ((p : ℤ) ^ (2 * m + 2)) ∣ PowerSeries.coeff j (A * B) := by
    intro j
    rw [PowerSeries.coeff_mul]
    refine Finset.dvd_sum fun x _ => ?_
    have h : (p : ℤ) ^ (2 * m + 2) = (p : ℤ) ^ (m + 1) * (p : ℤ) ^ (m + 1) := by
      rw [← pow_add]; congr 1; ring
    rw [h]
    exact mul_dvd_mul (hA x.1).1 (hB x.2).1
  intro j
  exact ⟨dvd_trans (pow_dvd_pow _ (by omega)) (key j),
    fun s _ hs => dvd_trans (pow_dvd_pow _ (by omega)) (key j)⟩

lemma Jm_mul_one {p m : ℕ} {G H : PowerSeries ℤ} (hG : Jm p m (G - 1)) (hH : Jm p m (H - 1)) :
    Jm p m (G * H - 1) := by
  have h : G * H - 1 = (G - 1) + (H - 1) + (G - 1) * (H - 1) := by ring
  rw [h]
  exact Jm_add (Jm_add hG hH) (Jm_mul hG hH)

lemma Jm_prod {p m : ℕ} (S : Finset ℕ) (f : ℕ → PowerSeries ℤ) (h : ∀ k ∈ S, Jm p m (f k - 1)) :
    Jm p m ((∏ k ∈ S, f k) - 1) :=
  Finset.prod_induction f (fun G => Jm p m (G - 1)) (fun _ _ ha hb => Jm_mul_one ha hb)
    (fun j => by simp) h

/-- `g = 1/(1-x)`. -/
noncomputable def g : PowerSeries ℤ := geom 1

lemma coeff_g (j : ℕ) : PowerSeries.coeff j g = 1 := by
  simp [g, geom, PowerSeries.coeff_mk]

lemma g_mul : g * B (-1) 1 = 1 := by
  have h : g * B (-1) 1 = g - PowerSeries.X * g := by
    simp only [B, map_neg, map_one, pow_one]; ring
  rw [h]
  ext j
  rcases j with _ | j
  · simp only [map_sub, PowerSeries.coeff_zero_X_mul, coeff_g, PowerSeries.coeff_one]; simp
  · rw [map_sub, PowerSeries.coeff_succ_X_mul, coeff_g, coeff_g, PowerSeries.coeff_one]
    simp

lemma geom_eq (k : ℕ) (hk : k ≠ 0) : geom k = PowerSeries.expand k hk g := by
  ext j
  rw [PowerSeries.coeff_expand, coeff_g]
  simp only [geom, PowerSeries.coeff_mk]

lemma expand_congr (a b : ℕ) (h : a = b) (ha : a ≠ 0) (hb : b ≠ 0) (G : PowerSeries ℤ) :
    PowerSeries.expand a ha G = PowerSeries.expand b hb G := by
  subst h; rfl

lemma expand_comm (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (G : PowerSeries ℤ) :
    PowerSeries.expand a ha (PowerSeries.expand b hb G) =
      PowerSeries.expand b hb (PowerSeries.expand a ha G) := by
  rw [← PowerSeries.expand_mul, ← PowerSeries.expand_mul]
  exact expand_congr _ _ (Nat.mul_comm a b) _ _ G

/-- `psi = (1 - x^p) / (1 - x)^p`. -/
noncomputable def psi (p : ℕ) : PowerSeries ℤ := g ^ p * B (-1) p

lemma psi_pow_InI {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (n w : ℕ) (hn : 0 < n) :
    InI p (p ^ (w + 1)) (psi p ^ (n * p ^ w) - 1) := by
  have hL := B_pow_InI hp hp2 n w hn (-1) (Or.inr rfl) 1 one_pos (Nat.coprime_one_right p)
  rw [one_mul] at hL
  set K := n * p ^ w with hK
  have hU : B (-1) 1 ^ (n * p ^ (w + 1)) = B (-1) 1 ^ (p * K) := by
    rw [hK, pow_succ]; congr 1; ring
  rw [hU] at hL
  have hrel : (psi p ^ K - 1) * B (-1) 1 ^ (p * K) = 0 - (B (-1) 1 ^ (p * K) - B (-1) p ^ K) := by
    have h1 : psi p ^ K * B (-1) 1 ^ (p * K) = (g * B (-1) 1) ^ (p * K) * B (-1) p ^ K := by
      rw [psi, mul_pow, ← pow_mul, mul_pow (g) (B (-1) 1)]; ring
    rw [sub_mul, h1, g_mul, one_pow, one_mul]; ring
  have h0 : InI p (p ^ (w + 1)) 0 := fun j => by simp
  have hprod : InI p (p ^ (w + 1)) ((psi p ^ K - 1) * B (-1) 1 ^ (p * K)) := by
    rw [hrel]; exact InI_sub h0 hL
  have hU0 : PowerSeries.coeff 0 (B (-1) 1 ^ (p * K)) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_B' _ _ one_pos, one_pow]
  have hPS := B_pow_PS p hp.pos (-1) 1 K one_pos
  rw [one_mul] at hPS
  have hUoff : ∀ j, ¬ p ∣ j → ((p ^ (w + 1) : ℕ) : ℤ) ∣ PowerSeries.coeff j (B (-1) 1 ^ (p * K)) := by
    intro j hj
    have h1 := (hL j).1
    rw [map_sub, hPS j hj, sub_zero] at h1
    exact h1
  exact InI_of_mul hU0 hUoff hprod

lemma factor_J {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (n m k : ℕ) (hn : 0 < n) (hk : k ≠ 0) :
    Jm p m (PowerSeries.expand k hk (psi p ^ (k * (n * p ^ m))) - 1) := by
  obtain ⟨v, k', hk', hkk⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk p hp.ne_one
  have hk'0 : 0 < k' := by
    rcases Nat.eq_zero_or_pos k' with h | h
    · exact absurd (h ▸ dvd_zero p) hk'
    · exact h
  have hK : k * (n * p ^ m) = (k' * n) * p ^ (m + v) := by rw [hkk, pow_add]; ring
  have hD := psi_pow_InI hp hp2 (k' * n) (m + v) (Nat.mul_pos hk'0 hn)
  rw [← hK] at hD
  set D := psi p ^ (k * (n * p ^ m)) - 1 with hDdef
  have he : PowerSeries.expand k hk (psi p ^ (k * (n * p ^ m))) - 1 = PowerSeries.expand k hk D := by
    rw [hDdef, map_sub, map_one]
  rw [he]
  intro j
  rw [PowerSeries.coeff_expand]
  split_ifs with hkj
  · obtain ⟨i, rfl⟩ := hkj
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hk)]
    have hc1 := (hD i).1
    push_cast at hc1
    refine ⟨dvd_trans (pow_dvd_pow _ (by omega)) hc1, fun s hs hsm => ?_⟩
    by_cases hpi : p ∣ i
    · have hc2 := (hD i).2 hpi
      push_cast at hc2
      rw [← pow_mul] at hc2
      exact dvd_trans (pow_dvd_pow _ (by omega)) hc2
    · have hcop : Nat.Coprime (p ^ s) (k' * i) :=
        Nat.Coprime.pow_left s (Nat.Coprime.mul_right
          ((Nat.Prime.coprime_iff_not_dvd hp).mpr hk') ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpi))
      have h1 : p ^ s ∣ p ^ v * (k' * i) := by
        have : k * i = p ^ v * (k' * i) := by rw [hkk]; ring
        rw [← this]; exact hs
      have h2 : p ^ s ∣ p ^ v := hcop.dvd_of_dvd_mul_right h1
      have h3 : s ≤ v := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h2
      exact dvd_trans (pow_dvd_pow _ (by omega)) hc1
  · exact ⟨dvd_zero _, fun _ _ _ => dvd_zero _⟩

/-- truncated product `P M = ∏_{k=1}^{M} geom k ^ k`. -/
noncomputable def P (M : ℕ) : PowerSeries ℤ := ∏ k ∈ Finset.range M, geom (k + 1) ^ (k + 1)

/-- `E M = ∏_{k=1}^{M} expand_k(psi)^k`. -/
noncomputable def E (p M : ℕ) : PowerSeries ℤ :=
  ∏ k ∈ Finset.range M, PowerSeries.expand (k + 1) (Nat.succ_ne_zero k) (psi p) ^ (k + 1)

lemma a_eq (q : ℕ) : a q = PowerSeries.coeff q (P q ^ q) := by
  unfold a P
  rw [← Finset.prod_pow]
  congr 1
  have h1 : ∏ k ∈ Finset.range q, (geom (k + 1) ^ (k + 1)) ^ q =
      ∏ k ∈ Finset.Ico (0 + 1) (q + 1), (geom k ^ k) ^ q := by
    rw [Finset.range_eq_Ico, Finset.prod_Ico_add' (fun k => (geom k ^ k) ^ q) 0 q 1]
  have hI : Finset.Icc 1 q = Finset.Ico 1 (q + 1) := by ext x; simp
  rw [h1, zero_add, hI]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← pow_mul]

/-- agreement up to degree `q`. -/
def Ag (q : ℕ) (A B : PowerSeries ℤ) : Prop := ∀ j ≤ q, PowerSeries.coeff j A = PowerSeries.coeff j B

lemma Ag_mul {q : ℕ} {A B : PowerSeries ℤ} (h : Ag q A B) (C : PowerSeries ℤ) : Ag q (A * C) (B * C) := by
  intro j hj
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [h x.1 (by omega)]

lemma Ag_one_mul {q : ℕ} {A B : PowerSeries ℤ} (hA : Ag q A 1) (hB : Ag q B 1) : Ag q (A * B) 1 := by
  intro j hj
  rw [Ag_mul hA B j hj, one_mul, hB j hj]

lemma Ag_pow {q : ℕ} {A : PowerSeries ℤ} (hA : Ag q A 1) (e : ℕ) : Ag q (A ^ e) 1 := by
  induction e with
  | zero => intro j _; simp
  | succ e ih => rw [pow_succ]; exact Ag_one_mul ih hA

lemma geom_Ag {q k : ℕ} (hk : q < k) : Ag q (geom k) 1 := by
  intro j hj
  simp only [geom, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  · rw [if_neg (fun h => absurd (Nat.le_of_dvd hj0 h) (by omega)), if_neg (by omega)]

lemma trunc_eq {q M : ℕ} (h : q ≤ M) : PowerSeries.coeff q (P M ^ q) = PowerSeries.coeff q (P q ^ q) := by
  have hsplit : P M = P q * ∏ k ∈ Finset.Ico q M, geom (k + 1) ^ (k + 1) := by
    unfold P; rw [Finset.prod_range_mul_prod_Ico _ h]
  have hR : Ag q (∏ k ∈ Finset.Ico q M, geom (k + 1) ^ (k + 1)) 1 :=
    Finset.prod_induction _ (fun G => Ag q G 1) (fun _ _ ha hb => Ag_one_mul ha hb)
      (fun j _ => rfl) (fun k hk => Ag_pow (geom_Ag (by rw [Finset.mem_Ico] at hk; omega)) _)
  rw [hsplit, mul_pow, mul_comm]
  have := Ag_mul (Ag_pow hR q) (P q ^ q) q le_rfl
  rw [this, one_mul]

lemma frob_factor (p : ℕ) (hp0 : p ≠ 0) (k : ℕ) (hk : k ≠ 0) :
    (geom k ^ k) ^ p = PowerSeries.expand p hp0 (geom k ^ k) *
      PowerSeries.expand k hk (psi p) ^ k := by
  rw [geom_eq k hk, map_pow, ← mul_pow, ← pow_mul, mul_comm k p, pow_mul, ← map_pow]
  congr 1
  rw [expand_comm, psi, map_mul, ← mul_assoc, mul_comm (PowerSeries.expand k hk _), mul_assoc,
    ← map_mul, ← map_mul]
  have h : PowerSeries.expand p hp0 g * B (-1) p = 1 := by
    have h2 := expand_B p hp0 (-1) 1
    rw [one_mul] at h2
    rw [← h2, ← map_mul, g_mul, map_one]
  rw [h, mul_one]

lemma frob (p : ℕ) (hp0 : p ≠ 0) (M : ℕ) : P M ^ p = PowerSeries.expand p hp0 (P M) * E p M := by
  unfold P E
  rw [← Finset.prod_pow, map_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => frob_factor p hp0 (k + 1) (Nat.succ_ne_zero k)

lemma E_pow_J {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (n m M : ℕ) (hn : 0 < n) :
    Jm p m (E p M ^ (n * p ^ m) - 1) := by
  unfold E
  rw [← Finset.prod_pow]
  apply Jm_prod
  intro k _
  rw [← pow_mul, ← map_pow]
  exact factor_J hp hp2 n m (k + 1) hn (Nat.succ_ne_zero k)

lemma constantCoeff_E (p M : ℕ) (hp : 0 < p) : PowerSeries.constantCoeff (E p M) = 1 := by
  unfold E
  rw [map_prod]
  refine Finset.prod_eq_one fun k _ => ?_
  rw [map_pow, PowerSeries.constantCoeff_expand, psi, map_mul, map_pow, constantCoeff_B' _ _ hp,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_g]
  simp

lemma C_dvd_of_coeff (d : ℤ) (G : PowerSeries ℤ) (h : ∀ j, d ∣ PowerSeries.coeff j G) :
    PowerSeries.C d ∣ G := by
  refine ⟨PowerSeries.mk fun j => PowerSeries.coeff j G / d, ?_⟩
  ext j
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, Int.mul_ediv_cancel' (h j)]

lemma frob_dvd {p : ℕ} (hp : p.Prime) (H : PowerSeries ℤ)
    (hH : ((p : ℕ) : PowerSeries ℤ) ∣ H ^ p - PowerSeries.expand p hp.ne_zero H) :
    ∀ m s k, s ≤ m → ¬ p ^ (s + 1) ∣ k → (p : ℤ) ^ (m - s) ∣ PowerSeries.coeff k (H ^ (p ^ m)) := by
  intro m
  induction m with
  | zero =>
    intro s k hs _
    rw [show s = 0 by omega]; simp
  | succ m ih =>
    intro s k hs hk
    obtain ⟨W, hW⟩ := dvd_sub_pow_of_dvd_sub hH m
    rw [← pow_mul, ← map_pow, ← pow_succ'] at hW
    have hc : PowerSeries.coeff k (H ^ p ^ (m + 1)) =
        PowerSeries.coeff k (PowerSeries.expand p hp.ne_zero (H ^ p ^ m)) +
          (p : ℤ) ^ (m + 1) * PowerSeries.coeff k W := by
      rw [← PowerSeries.coeff_C_mul, ← map_add]
      congr 1
      have hC : PowerSeries.C ((p : ℤ) ^ (m + 1)) = ((p : PowerSeries ℤ)) ^ (m + 1) := by
        rw [map_pow, map_natCast]
      rw [hC, ← hW]; ring
    rw [hc]
    by_cases hpk : p ∣ k
    · obtain ⟨k', rfl⟩ := hpk
      rw [PowerSeries.coeff_expand_mul]
      have hs1 : 1 ≤ s := by
        by_contra h0
        exact hk (by rw [show s = 0 by omega]; simp)
      have hk' : ¬ p ^ (s - 1 + 1) ∣ k' := by
        intro h
        apply hk
        rw [show s + 1 = (s - 1 + 1) + 1 by omega, pow_succ, mul_comm p k']
        exact mul_dvd_mul h (dvd_refl p)
      have := ih (s - 1) k' (by omega) hk'
      rw [show m - (s - 1) = m + 1 - s by omega] at this
      exact dvd_add this (Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _)
    · rw [PowerSeries.coeff_expand_of_not_dvd _ _ _ hpk, zero_add]
      exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _

theorem main_level {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (n m : ℕ) (hn : 0 < n) :
    (p : ℤ) ^ (2 * (m + 1)) ∣ a (n * p ^ (m + 1)) - a (n * p ^ m) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  set Q := n * p ^ m with hQ
  set N := n * p ^ (m + 1) with hN
  have hNQ : N = p * Q := by rw [hN, hQ, pow_succ]; ring
  have hQN : Q ≤ N := by rw [hNQ]; exact Nat.le_mul_of_pos_left Q hp.pos
  rw [a_eq N, a_eq Q, ← trunc_eq hQN]
  set PP := P N
  have hpow : PP ^ N = PowerSeries.expand p hp0 (PP ^ Q) * E p N ^ Q := by
    rw [show PP ^ N = PP ^ (p * Q) by rw [hNQ], pow_mul, frob p hp0 N, mul_pow, map_pow]
  rw [hpow, PowerSeries.coeff_mul]
  have hmem : (N, 0) ∈ Finset.HasAntidiagonal.antidiagonal N :=
    Finset.HasAntidiagonal.mem_antidiagonal.mpr (add_zero N)
  rw [← Finset.add_sum_erase _ _ hmem]
  have hfirst : PowerSeries.coeff N (PowerSeries.expand p hp0 (PP ^ Q)) *
      PowerSeries.coeff 0 (E p N ^ Q) = PowerSeries.coeff Q (PP ^ Q) := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow PowerSeries.constantCoeff,
      constantCoeff_E p N hp.pos, one_pow, mul_one, show N = p * Q from hNQ, PowerSeries.coeff_expand_mul]
  simp only
  rw [hfirst, add_sub_cancel_left]
  -- Frobenius hypothesis for H = PP ^ n
  have hJ1 : Jm p 0 (E p N ^ (1 * p ^ 0) - 1) := E_pow_J hp hp2 1 0 N one_pos
  simp only [pow_zero, mul_one] at hJ1
  have hE1 : ((p : ℕ) : PowerSeries ℤ) ∣ E p N - 1 := by
    rw [← map_natCast PowerSeries.C]
    exact C_dvd_of_coeff _ _ fun j => by simpa using (hJ1 j).1
  have hH : ((p : ℕ) : PowerSeries ℤ) ∣ (PP ^ n) ^ p - PowerSeries.expand p hp0 (PP ^ n) := by
    have h1 : (PP ^ n) ^ p - PowerSeries.expand p hp0 (PP ^ n) =
        PowerSeries.expand p hp0 PP ^ n * (E p N ^ n - 1 ^ n) := by
      rw [← pow_mul, mul_comm n p, pow_mul, frob p hp0 N, mul_pow, map_pow, one_pow]; ring
    rw [h1]
    exact Dvd.dvd.mul_left (dvd_trans hE1 (sub_dvd_pow_sub_pow _ _ _)) _
  have hb := frob_dvd hp (PP ^ n) hH
  have hJ := E_pow_J hp hp2 n m N hn
  rw [← hQ] at hJ
  refine Finset.dvd_sum fun x hx => ?_
  rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hx
  by_cases hpx : p ∣ x.1
  · obtain ⟨s, hs⟩ := hpx
    rw [hs, PowerSeries.coeff_expand_mul]
    have hx2 : x.2 = p * (Q - s) := by
      have h1 : p * s + x.2 = p * Q := by rw [← hs, hx.2, hNQ]
      have h2 : s ≤ Q := by
        by_contra h
        have : p * Q < p * s := Nat.mul_lt_mul_of_pos_left (by omega) hp.pos
        omega
      rw [Nat.mul_sub]; omega
    have ht : 1 ≤ Q - s := by
      by_contra h
      have h0 : x.2 = 0 := by rw [hx2]; simp [show Q - s = 0 by omega]
      have h1 : x.1 = N := by omega
      exact hx.1 (Prod.ext h1 h0)
    rw [hx2]
    set t := Q - s with ht_def
    have hco : PowerSeries.coeff (p * t) (E p N ^ Q - 1) = PowerSeries.coeff (p * t) (E p N ^ Q) := by
      rw [map_sub, PowerSeries.coeff_one, if_neg (Nat.mul_ne_zero hp0 (by omega)), sub_zero]
    have hst : s + t = Q := by omega
    obtain ⟨v, t', ht', htt⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : t ≠ 0) p hp.ne_one
    by_cases hv : m ≤ v
    · have hd : p ^ (m + 1) ∣ p * t := by
        rw [htt, pow_succ']
        exact mul_dvd_mul_left p (dvd_trans (pow_dvd_pow p hv) (dvd_mul_right _ _))
      have := (hJ (p * t)).2 (m + 1) hd le_rfl
      rw [hco] at this
      rw [show 2 * (m + 1) = m + 1 + (m + 1) by ring]
      exact Dvd.dvd.mul_left this _
    · have hd : p ^ (v + 1) ∣ p * t := by
        rw [htt, pow_succ']
        exact mul_dvd_mul_left p (dvd_mul_right _ _)
      have he := (hJ (p * t)).2 (v + 1) hd (by omega)
      rw [hco] at he
      have hsn : ¬ p ^ (v + 1) ∣ s := by
        intro h
        have hQd : p ^ (v + 1) ∣ Q := by
          rw [hQ]; exact Dvd.dvd.mul_left (pow_dvd_pow p (by omega)) n
        have htd : p ^ (v + 1) ∣ t := by
          have := (Nat.dvd_add_right h).mp (hst ▸ hQd)
          exact this
        rw [htt, pow_succ] at htd
        exact ht' (Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos v) htd)
      have hbs := hb m v s (by omega) hsn
      have hQ' : PP ^ Q = (PP ^ n) ^ p ^ m := by rw [hQ, pow_mul]
      rw [hQ']
      have : (p : ℤ) ^ (2 * (m + 1)) = (p : ℤ) ^ (m - v) * (p : ℤ) ^ (m + 1 + (v + 1)) := by
        rw [← pow_add]; congr 1; omega
      rw [this]
      exact mul_dvd_mul hbs he
  · rw [PowerSeries.coeff_expand_of_not_dvd _ _ _ hpx, zero_mul]
    exact dvd_zero _

end A255672

theorem OMA.solution : type_of% @OMA.S_oeis_a255672.main := by
  intro p hp hp3 n k hn hk
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact A255672.main_level hp (by omega) n m hn
