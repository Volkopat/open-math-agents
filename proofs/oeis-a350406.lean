import OMAStatements.S_oeis_a350406
import Mathlib

/-!
OEIS A350406, Bala's supercongruence: for a(n) = [x^n] 1/(1 + x + x^2 + x^3)^n,
a(n p^r) = a(n p^(r-1)) modulo p^(2r) for every prime p >= 5 and all n, r >= 1.

Write Q = n p^(r-1), N = p Q, m = r - 1 (so p^m divides Q) and M = p^(m+1). Call an integer power
series D small (`InI`) if M divides every coefficient of D and M^2 divides the coefficients whose
index is a multiple of p.

1. Binomial part. With X = prod (N - j) and Y = prod j over the j < p*b prime to p one has
   C(N, p*b) * Y = C(Q, b) * X. The reflection j -> p*b - j gives X^2 = Y^2 modulo N * (N - p*b)
   and X = Y modulo p, and p divides neither Y nor X + Y (p odd). Since Q divides
   C(Q, b) * (Q - b), the number p^2 Q^2 divides C(Q, b) * N * (N - p*b), hence M^2 divides
   C(Q, b) * (X - Y) = Y * (C(N, p*b) - C(Q, b)), and so M^2 divides C(N, p*b) - C(Q, b).
   Also M divides C(N, i) when p does not divide i.
2. Hence (1 - x^e)^N - (1 - x^(e p))^Q is small for e = 1, 4 (p is odd).
3. With G_n = 1/(1 + x + x^2 + x^3)^n one has (1 - x^4)^n G_n = (1 - x)^n. Taking n = N, and n = Q
   expanded by x -> x^p, the series (G_N - expand_p G_Q) * (1 - x^4)^N is small, and division by a
   series with constant coefficient 1 whose coefficients off the multiples of p are divisible by M
   keeps smallness. The coefficient of x^N gives the claim.
-/

open Finset

namespace A350406

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

/-- `a` divides `C(a, b) * (a - b)` over `ℤ`, with no side condition. -/
private lemma dvd_choose_mul_sub (a b : ℕ) :
    (a : ℤ) ∣ ((a.choose b : ℕ) : ℤ) * ((a : ℤ) - b) := by
  rw [← choose_succ_int a b]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    have h := Nat.add_one_mul_choose_eq a' b
    have h' : (((a' + 1) * a'.choose b : ℕ) : ℤ) =
        (((a' + 1).choose (b + 1) * (b + 1) : ℕ) : ℤ) := by rw [h]
    refine ⟨((a'.choose b : ℕ) : ℤ), ?_⟩
    push_cast at h' ⊢
    linear_combination -h'

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

/-- Key binomial congruence: `C(p a, p b) ≡ C(a, b)` modulo `p ^ (2 (m + 1))` for an odd prime `p`
and every `a` divisible by `p ^ m`. -/
private lemma choose_mul_congr {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (m a b : ℕ) (ha : p ^ m ∣ a) :
    ((p : ℤ) ^ (2 * (m + 1))) ∣
      (((p * a).choose (p * b) : ℕ) : ℤ) - ((a.choose b : ℕ) : ℤ) := by
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hform := choose_mul_uprod p a b hp.pos
  set N : ℤ := ((p * a : ℕ) : ℤ) with hNdef
  set X := uprod p b (fun j => N - j) with hX
  set Y := uprod p b (fun j => (j : ℤ)) with hY
  have hNe : N = (p : ℤ) * a := by rw [hNdef]; push_cast; ring
  have hbe : ((p * b : ℕ) : ℤ) = (p : ℤ) * b := by push_cast; ring
  -- reflected forms
  have hXr : X = uprod p b (fun j => N - ((p * b - j : ℕ) : ℤ)) := uprod_reflect p b _
  have hYr : Y = uprod p b (fun j => ((p * b - j : ℕ) : ℤ)) := uprod_reflect p b _
  have hdiff : (p : ℤ) ∣ N - ((p * b : ℕ) : ℤ) := by
    rw [hNe, hbe]; exact ⟨(a : ℤ) - b, by ring⟩
  -- X ≡ Y mod p
  have h1 : X ≡ Y [ZMOD (p : ℤ)] := by
    rw [hXr]
    refine uprod_modEq p b _ _ _ fun i hi t ht => ?_
    have hle := unit_le hi ht
    show N - ((p * b - (p * i + t + 1) : ℕ) : ℤ) ≡ ((p * i + t + 1 : ℕ) : ℤ) [ZMOD (p : ℤ)]
    rw [Nat.cast_sub hle, Int.modEq_iff_dvd]
    have : ((p * i + t + 1 : ℕ) : ℤ) - (N - (((p * b : ℕ) : ℤ) - ((p * i + t + 1 : ℕ) : ℤ)))
        = -(N - ((p * b : ℕ) : ℤ)) := by ring
    rw [this]
    exact (dvd_neg).mpr hdiff
  -- X * X ≡ Y * Y mod N * (N - p b)
  have h2 : X * X ≡ Y * Y [ZMOD N * (N - ((p * b : ℕ) : ℤ))] := by
    have e1 : X * X = uprod p b (fun j => (N - j) * (N - ((p * b - j : ℕ) : ℤ))) := by
      rw [← uprod_mul, ← hXr]
    have e2 : Y * Y = uprod p b (fun j => (j : ℤ) * ((p * b - j : ℕ) : ℤ)) := by
      rw [← uprod_mul, ← hYr]
    rw [e1, e2]
    refine uprod_modEq p b _ _ _ fun i hi t ht => ?_
    have hle := unit_le hi ht
    show (N - ((p * i + t + 1 : ℕ) : ℤ)) * (N - ((p * b - (p * i + t + 1) : ℕ) : ℤ))
      ≡ ((p * i + t + 1 : ℕ) : ℤ) * ((p * b - (p * i + t + 1) : ℕ) : ℤ)
        [ZMOD N * (N - ((p * b : ℕ) : ℤ))]
    rw [Nat.cast_sub hle, Int.modEq_iff_dvd]
    have : ((p * i + t + 1 : ℕ) : ℤ) * (((p * b : ℕ) : ℤ) - ((p * i + t + 1 : ℕ) : ℤ))
        - (N - ((p * i + t + 1 : ℕ) : ℤ)) * (N - (((p * b : ℕ) : ℤ) - ((p * i + t + 1 : ℕ) : ℤ)))
        = -(N * (N - ((p * b : ℕ) : ℤ))) := by ring
    rw [this]
    exact (dvd_neg).mpr dvd_rfl
  -- p divides neither Y nor X + Y
  have hYnd : ¬ (p : ℤ) ∣ Y := not_dvd_uprod_id hp b
  have hsum : ¬ (p : ℤ) ∣ X + Y := by
    intro hd
    have hXY : (p : ℤ) ∣ X - Y := Int.modEq_iff_dvd.mp h1.symm
    have h2Y : (p : ℤ) ∣ 2 * Y := by
      have : 2 * Y = (X + Y) - (X - Y) := by ring
      rw [this]; exact dvd_sub hd hXY
    rcases hpi.dvd_or_dvd h2Y with h | h
    · have h' : p ∣ 2 := by exact_mod_cast h
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h'
      exact hp2 this
    · exact hYnd h
  -- p^(2(m+1)) divides C(a, b) * N * (N - p b)
  have hcore : ((p : ℤ) ^ (2 * (m + 1))) ∣
      ((a.choose b : ℕ) : ℤ) * (N * (N - ((p * b : ℕ) : ℤ))) := by
    obtain ⟨c, hc⟩ := dvd_choose_mul_sub a b
    obtain ⟨d, hd⟩ := ha
    have ha' : (a : ℤ) = (p : ℤ) ^ m * d := by exact_mod_cast hd
    refine ⟨(d : ℤ) ^ 2 * c, ?_⟩
    rw [hNe, hbe]
    linear_combination ((p : ℤ) ^ 2 * (a : ℤ)) * hc
      + ((p : ℤ) ^ 2 * c * ((a : ℤ) + (p : ℤ) ^ m * d)) * ha'
  have hprod : ((p : ℤ) ^ (2 * (m + 1))) ∣ ((a.choose b : ℕ) : ℤ) * (X - Y) * (X + Y) := by
    have h3 : N * (N - ((p * b : ℕ) : ℤ)) ∣ X * X - Y * Y := Int.modEq_iff_dvd.mp h2.symm
    have h4 : ((a.choose b : ℕ) : ℤ) * (X - Y) * (X + Y)
        = ((a.choose b : ℕ) : ℤ) * (X * X - Y * Y) := by ring
    rw [h4]
    exact dvd_trans hcore (mul_dvd_mul_left _ h3)
  have hstep : ((p : ℤ) ^ (2 * (m + 1))) ∣ ((a.choose b : ℕ) : ℤ) * (X - Y) :=
    hpi.pow_dvd_of_dvd_mul_right _ hsum hprod
  have hkey : Y * ((((p * a).choose (p * b) : ℕ) : ℤ) - ((a.choose b : ℕ) : ℤ))
      = ((a.choose b : ℕ) : ℤ) * (X - Y) := by
    linear_combination hform
  rw [← hkey] at hstep
  exact hpi.pow_dvd_of_dvd_mul_left _ hYnd hstep

/-- `p ^ k` divides `C(N, i)` when `p ^ k` divides `N` and `p` does not divide `i`. -/
private lemma pow_dvd_choose_of_not_dvd {p : ℕ} (hp : p.Prime) (k N i : ℕ) (hN : p ^ k ∣ N)
    (hi : ¬ p ∣ i) : p ^ k ∣ N.choose i := by
  have hi0 : i ≠ 0 := fun h => hi (h ▸ dvd_zero p)
  have hipos : 0 < i := Nat.pos_of_ne_zero hi0
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · rw [Nat.choose_eq_zero_of_lt hipos]
    exact dvd_zero _
  have h := Nat.add_one_mul_choose_eq (N - 1) (i - 1)
  rw [Nat.sub_add_cancel hNpos, Nat.sub_add_cancel hipos] at h
  -- h : N * C(N - 1, i - 1) = C(N, i) * i
  have h1 : p ^ k ∣ N.choose i * i := by
    rw [← h]
    exact Dvd.dvd.mul_right hN _
  have hcop : Nat.Coprime (p ^ k) i :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hi)
  exact hcop.dvd_of_dvd_mul_right h1

/-! Power series part. -/

/-- `D` is in the set `N * (series supported off the multiples of p) + N ^ 2 * (any series)`. -/
private def InI (p N : ℕ) (D : PowerSeries ℤ) : Prop :=
  ∀ j, ((N : ℤ) ∣ PowerSeries.coeff j D) ∧ (p ∣ j → ((N : ℤ) ^ 2) ∣ PowerSeries.coeff j D)

/-- `G` is supported on the multiples of `p`. -/
private def PS (p : ℕ) (G : PowerSeries ℤ) : Prop :=
  ∀ j, ¬ p ∣ j → PowerSeries.coeff j G = 0

private lemma InI_sub {p N : ℕ} {A B : PowerSeries ℤ} (hA : InI p N A) (hB : InI p N B) :
    InI p N (A - B) := by
  intro j
  rw [map_sub]
  exact ⟨dvd_sub (hA j).1 (hB j).1, fun h => dvd_sub ((hA j).2 h) ((hB j).2 h)⟩

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

/-- `(1 + c x^e)^(p Q) - (1 + c x^(e p))^Q` is small when `p ^ m ∣ Q`, `c = ±1`, `p` odd and prime
to `e`. -/
private lemma B_pow_InI {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (m Q : ℕ) (hQ : p ^ m ∣ Q) (c : ℤ)
    (hc : c = 1 ∨ c = -1) (e : ℕ) (he : 0 < e) (hep : Nat.Coprime p e) :
    InI p (p ^ (m + 1)) (B c e ^ (p * Q) - B c (e * p) ^ Q) := by
  intro j
  rw [map_sub, coeff_B_pow c e _ j he, coeff_B_pow c (e * p) _ j (Nat.mul_pos he hp.pos)]
  have hcp : c ^ p = c := by
    rcases hc with rfl | rfl
    · simp
    · exact Odd.neg_one_pow (hp.odd_of_ne_two hp2)
  have hN : p ^ (m + 1) ∣ p * Q := by
    rw [pow_succ']
    exact Nat.mul_dvd_mul_left p hQ
  have hsq : (((p ^ (m + 1) : ℕ) : ℤ) ^ 2) = (p : ℤ) ^ (2 * (m + 1)) := by
    push_cast
    rw [← pow_mul]
    congr 1
    ring
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
      have key := choose_mul_congr hp hp2 m Q i' hQ
      rw [← hsq] at key
      have key' : ((p ^ (m + 1) : ℕ) : ℤ) ^ 2 ∣
          c ^ i' * ((((p * Q).choose (p * i') : ℕ) : ℤ) - ((Q.choose i' : ℕ) : ℤ)) :=
        Dvd.dvd.mul_left key _
      exact ⟨dvd_trans (dvd_pow_self _ two_ne_zero) key', fun _ => key'⟩
    · have h1 : ¬ e * p ∣ e * i := fun h => hpi (Nat.dvd_of_mul_dvd_mul_left he h)
      rw [if_neg h1, sub_zero]
      constructor
      · have h3 : ((p ^ (m + 1) : ℕ) : ℤ) ∣ (((p * Q).choose i : ℕ) : ℤ) := by
          exact_mod_cast pow_dvd_choose_of_not_dvd hp (m + 1) (p * Q) i hN hpi
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

/-- The series `1/(1 + x + x^2 + x^3)^n`, as in the statement. -/
private noncomputable def G (n : ℕ) : PowerSeries ℤ :=
  Ring.inverse ((1 + PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.X ^ 3 : PowerSeries ℤ) ^ n)

private lemma isUnit_denom (n : ℕ) :
    IsUnit ((1 + PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.X ^ 3 : PowerSeries ℤ) ^ n) := by
  apply IsUnit.pow
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp

/-- `(1 - x^4)^n * G_n = (1 - x)^n`. -/
private lemma G_rel (n : ℕ) : B (-1) 4 ^ n * G n = B (-1) 1 ^ n := by
  have hfac : B (-1) 4 =
      B (-1) 1 * (1 + PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.X ^ 3) := by
    unfold B
    simp only [map_neg, map_one, pow_one]
    ring
  have hinv : (1 + PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.X ^ 3 : PowerSeries ℤ) ^ n *
      G n = 1 := Ring.mul_inverse_cancel _ (isUnit_denom n)
  rw [hfac, mul_pow, mul_assoc, hinv, mul_one]

private theorem main_congr {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (m Q : ℕ) (hQ : p ^ m ∣ Q) :
    ((p : ℤ) ^ (2 * (m + 1))) ∣
      OMA.S_oeis_a350406.a (p * Q) - OMA.S_oeis_a350406.a Q := by
  have hp2 : p ≠ 2 := by omega
  have hp0 : p ≠ 0 := hp.ne_zero
  have hcop1 : Nat.Coprime p 1 := Nat.coprime_one_right p
  have hcop4 : Nat.Coprime p 4 := by
    have h2 : Nat.Coprime p 2 :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h =>
        hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4]
    exact Nat.Coprime.pow_right 2 h2
  -- the relation at level `N = p * Q`
  have hrelN : B (-1) 4 ^ (p * Q) * G (p * Q) = B (-1) 1 ^ (p * Q) := G_rel (p * Q)
  -- the relation at level `Q`, expanded by `x ↦ x ^ p`
  have hrelQ : B (-1) (4 * p) ^ Q * PowerSeries.expand p hp0 (G Q) = B (-1) (1 * p) ^ Q := by
    have h1 := congrArg (PowerSeries.expand p hp0) (G_rel Q)
    simp only [map_mul, map_pow, expand_B] at h1
    exact h1
  -- memberships
  have iA := B_pow_InI hp hp2 m Q hQ (-1) (Or.inr rfl) 4 (by norm_num) hcop4
  have iB := B_pow_InI hp hp2 m Q hQ (-1) (Or.inr rfl) 1 one_pos hcop1
  have sA := B_pow_PS p hp.pos (-1) 4 Q (by norm_num)
  have sPhi : PS p (PowerSeries.expand p hp0 (G Q)) :=
    fun j hj => PowerSeries.coeff_expand_of_not_dvd p hp0 _ hj
  -- the difference times `(1 - x^4)^N`
  have hprod : InI p (p ^ (m + 1))
      ((G (p * Q) - PowerSeries.expand p hp0 (G Q)) * B (-1) 4 ^ (p * Q)) := by
    have h : (G (p * Q) - PowerSeries.expand p hp0 (G Q)) * B (-1) 4 ^ (p * Q) =
        (B (-1) 1 ^ (p * Q) - B (-1) (1 * p) ^ Q) -
          (B (-1) 4 ^ (p * Q) - B (-1) (4 * p) ^ Q) * PowerSeries.expand p hp0 (G Q) := by
      linear_combination hrelN - hrelQ
    rw [h]
    exact InI_sub iB (InI_mul_PS iA sPhi)
  -- divide by `(1 - x^4)^N`
  have hU0 : PowerSeries.coeff 0 (B (-1) 4 ^ (p * Q)) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [B]
  have hU : ∀ j, ¬ p ∣ j →
      ((p ^ (m + 1) : ℕ) : ℤ) ∣ PowerSeries.coeff j (B (-1) 4 ^ (p * Q)) := by
    intro j hj
    have h1 := (iA j).1
    rw [map_sub, sA j hj, sub_zero] at h1
    exact h1
  have hD := InI_of_mul hU0 hU hprod
  -- read off the coefficient of `x ^ N`
  have hfin := (hD (p * Q)).2 (dvd_mul_right p Q)
  have hco : PowerSeries.coeff (p * Q) (PowerSeries.expand p hp0 (G Q)) =
      PowerSeries.coeff Q (G Q) := PowerSeries.coeff_expand_mul p hp0 _ _
  rw [map_sub, hco] at hfin
  have hsq : (((p ^ (m + 1) : ℕ) : ℤ) ^ 2) = (p : ℤ) ^ (2 * (m + 1)) := by
    push_cast
    rw [← pow_mul]
    congr 1
    ring
  rw [hsq] at hfin
  exact hfin

end A350406

theorem OMA.solution : type_of% @OMA.S_oeis_a350406.main := by
  intro p n r hp hp5 hn hr
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have h := A350406.main_congr hp hp5 m (n * p ^ m) (dvd_mul_left _ _)
  have e : p * (n * p ^ m) = n * p ^ (m + 1) := by ring
  rw [e] at h
  exact h
